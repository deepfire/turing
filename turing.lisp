;;; -*- Mode: LISP; Syntax: COMMON-LISP; Package: TURING; Base: 10 -*-
;;;
;;;  (c) copyright 2009-2010 by
;;;           Samium Gromoff (_deepfire@feelingofgreen.ru)
;;;
;;; This library is free software; you can redistribute it and/or
;;; modify it under the terms of the GNU Library General Public
;;; License as published by the Free Software Foundation; either
;;; version 2 of the License, or (at your option) any later version.
;;;
;;; This library is distributed in the hope that it will be useful,
;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;;; Library General Public License for more details.
;;;
;;; You should have received a copy of the GNU Library General Public
;;; License along with this library; if not, write to the
;;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;;; Boston, MA  02111-1307  USA.

(in-package :turing)

(defvar *comp-verbose* nil)

(eval-when (:compile-toplevel :load-toplevel)
  (define-condition comp-condition () ())
  (define-condition comp-error (error comp-condition) ())
  (define-simple-error comp-error))

;;;;
;;;; Types
;;;;
(deftype atomic-ctype () '(member integer char))
(defstruct (compound-ctype (:conc-name ctype-))
  (constructor)
  (arity))
(defstruct (array-ctype (:include compound-ctype) (:conc-name ctype-))
  (base-type)
  (dimensions))
(defstruct (record-ctype (:include compound-ctype) (:conc-name ctype-))
  (fields))
(deftype ctype () '(or compound-ctype atomic-ctype))

(defclass ctype-env ()
  ((ctypes :initform (make-hash-table :test 'eq))))

(define-subcontainer ctype :container-slot ctypes)

;;;;
;;;; Architecture bits
;;;;
(defclass load-store-architecture ()
  ((loads :reader arch-loads :initarg :loads)
   (stores :reader arch-stores :initarg :stores)))

(defgeneric emit-load (arch to-reg base-reg displacement))
(defgeneric emit-store (arch from-reg base-reg displacement))

;;;;
;;;; Symbol table
;;;;

(defstruct symentry
  (name)
  (class nil :type (member :local :local-static))
  (size)
  (bitsize)
  (boundary)
  (bitboundary)
  (type nil :type (member :s8 :u8 :s16 :u18 :s32 :u32 :s64 :u64 :float :double-float :quad-float))
  (basetype)
  (nelts)
  (machtype)
  (props (make-hash-table :test 'equal)))

(defvar *direct-properties* '(name class size bitsize boundary bitboundary type basetype nelts machtype))

(define-subcontainer symprop :type t :container-slot props :if-does-not-exist :continue)

(defmacro with-symentry-properties (properties entry &body body)
  (multiple-value-bind (direct indirect) (unzip (rcurry #'member *direct-properties*) properties)
    (once-only (entry)
      `(symbol-macrolet ,(iter (for s in indirect)
                               (collect `(,indirect `(symprop ,,entry ,,indirect))))
         (with-slots ,direct ,entry
           ,@body)))))

(defstruct (symtab (:constructor %make-symtab (parent)))
  (parent nil :type (or null symtable))
  (syms (make-hash-table :test 'equal) :type hash-table)
  (childs nil :type list))

(define-subcontainer locate-sym :container-slot syms :key-type string :type symentry :if-exists :continue :if-does-not-exist :continue
                     :iterator do-symtab-entries)

(defun make-symtab (&optional parent)
  "Creates a new local symbol table with the given symtol table as its parent,
or NIL if there is none, and returns the new (empty) local symbol table."
  (%make-symtab parent))

(defun dest-symtab (x)
  "Destroys the current local symbol table and returns its parent (or nil
if there is no parent)."
  (when-let ((parent (symtable-parent x)))
    (removef x (symtable-childs parent))
    parent))

(defun insert-sym (symtab x)
  "Inserts an entry for the given symbol into the given symbol table and returns T,
or if the symbol is already present, does not insert a new netry and returns NIL."
  (unless (locate-sym symtab x)
    (setf (locate-sym symtab x) (make-symentry :name x))
    t))

(defun enclosing-symtab (symtab x)
  "Returns the nearest enclosing symbol table that declares X,
or NIL if there is none."
  (labels ((rec (symtab)
             (or (when (locate-sym symtab x)
                   symtab)
                 (when-let ((parent (symtab-parent symtab)))
                   (rec parent)))))
    (rec symtab)))

(defun depth-of-symtab (symtab)
  "Returns the depth of the given symbol table relative to the current one,
which, by convention, has depth zero."
  (labels ((rec (depth symtab)
             (if-let ((parent (symtab-parent symtab)))
               (rec (1+ depth) parent)
               depth)))
    (rec 0 symtab)))

;;;;
;;;; Storage binding
;;;;
(defun round-abs-up (m n)
  "Ensure that M is aligned by N."
  (* (signum m) (ceiling (abs (coerce (/ m n) 'float))) (abs n)))

(defun bind-local-vars (symtab initdisp)
  "Assign each static variable a displacement and, for stack-allocated variables,
assigns a displacement and the frame pointer as the base register."
  (let ((stackloc initdisp)
        (staticloc 0)
        ;; Sort frame entries in order of decreasing alignment requirements.
        ;; When we overflow load/store displacement constants, this becomes
        ;; a size vs. speed tradeoff -- reverting this order, while maintaining
        ;; alignment requirements allows us to access more frame locals, with
        ;; a negligible size loss.
        ;; XXX: we should default to that, actually.
        (alignment-sorted-entries (sort (do-symtab-entries (s symtab) (collect s))
                                        #'> :key #'symentry-size)))
    (dolist (entry alignment-sorted-entries)
      (with-slots (class size basetype nelts) entry
        (ecase class
          (:local
           (case basetype
             (:record
              (dotimes (i nelts)
                (let ((field-size (symprop entry `(,i size))))
                  (decf stackloc field-size)
                  (setf stackloc (round-abs-up stackloc field-size)
                        (symprop entry 'reg) "fp"
                        (symprop entry `(,i disp)) stackloc))))
             (t
              (decf stackloc size)
              (setf stackloc (round-abs-up stackloc size)
                    (symprop entry 'reg) "fp"
                    (symprop entry 'disp) stackloc))))
          (:local-static
           (case basetype
             (:record
              (dotimes (i nelts)
                (let ((field-size (symprop entry `(,i size))))
                  (setf staticloc (round-abs-up staticloc field-size)
                        (symprop entry `(,i disp)) staticloc)
                  (incf staticloc field-size))))
             (t
              (setf staticloc (round-abs-up staticloc size)
                    (symprop entry 'disp) staticloc)
              (incf staticloc size)))))))))

;;;;
;;;; Variable load/store
;;;;
(defun sym-to-reg (symtab var)
  "Generates a load from storage location corresponding to a given variable
to a register, register pair, or register quadruple of the appopriate
type, and returns the name of the first register.")

(defun sym-to-reg-force (symtab var register)
  "Generates a load from storage location corresponding to a given symbol
to the named register, register pair, or register quadruple of the appopriate
type.  This routine can be used, for example, to force procedure arguments to
the appropriate registers.")

(defun alloc-reg (symtab var)
  "Allocates a register, register pair, or register quadruple of the
appropriate type to hold the value of its VARiable argument and sets the 'reg'
field in the variable's symbol-table entry, unless there already is a register
allocated, and (in either case) returns the name of the first register.")

(defun reg-to-sym (symtab register)
  "Generates a store of REGISTER name to the variable's storage location.")

(defun alloc-reg-anon (floatp integer)
  "Allocates a register, register pair, or register quadruple of the
appropriate type (according to the value of the second argument, which
may be 1, 2 or 4) and returns the name of the first register.  It does not
associate the register with a symbol, unlike ALLOC-REG.")

(defun free-reg (register)
  "Returns its argument register to the pool of available registers.")

(defun find-symtab (symtab variable))
(defun gen-ldst (symtab opcode reg symdisp storep))

;;;;
;;;; Operands
;;;;
(defclass constant () ((value :reader value :initarg :value)))
(defclass variable () ((varname :reader varname :initarg :varname)))
(defclass symbol (variable constant) ())
(defclass typename () ((typename :reader typename :initarg :typename)))
(defclass operand (variable constant typename) ())

(define-protocol-class register () ((regname :reader regname :initarg :regname)))
(defclass integer-register (register) ())
(defclass floating-point-register (register) ())
(defclass symbolic-register (register) ())
(defclass lir-operand (register constant typename) ())

(defun make-constant (value)                     (make-instance 'constant :value value))
(defun make-variable (varname)                   (make-instance 'variable :varname varname))
(defun make-integer-register (regname)           (make-instance 'integer-register :regname regname))
(defun make-floating-point-register (regname)    (make-instance 'floating-point-register :regname regname))
(defun make-symbolic-register (regname)          (make-instance 'symbolic-register :regname regname))
(defun make-symbol (varname value)               (make-instance 'symbol :varname varname :value value))
(defun make-operand (varname value typename)     (make-instance 'operand :varname varname :value value :typename typename))
(defun make-lir-operand (regname value typename) (make-instance 'lir-operand :regname regname :value value :typename typename))

;;;;
;;;; Operators
;;;;
(defclass operator ()
  ((sym :reader op-sym :allocation :class :initarg :sym)
   (arity :reader op-arity :allocation :class :type (integer 1 2))))
(defclass unary-operator (operator)  ((arity :allocation :class :initform 1)))
(defclass binary-operator (operator) ((arity :allocation :class :initform 2)))

(defmethod print-object ((o operator) stream)
  (write-string (string-downcase (op-sym o)) stream))

(defvar *ops* (make-hash-table :test 'eq)
  "Map of short names (per Muchnick) to classes.")

(define-root-container *ops* op :type operator)

(defmacro define-operator (sym short-name arity name)
  `(progn
     (defclass ,name (,(ecase arity (1 'unary-operator) (2 'binary-operator)))
       ((sym :allocation :class :initform ',sym)))
     (setf (op ,short-name) (make-instance ',name))))
(defmacro define-unary-operator (sym short-name name)  `(define-operator ,sym ,short-name 1 ,name))
(defmacro define-binary-operator (sym short-name name) `(define-operator ,sym ,short-name 2 ,name))

(define-binary-operator + :add add)
(define-binary-operator - :sub subtract)
(define-binary-operator * :mul multiply)
(define-binary-operator / :div divide)
(define-binary-operator mod :mod modulo)
(define-binary-operator min :min minumum)
(define-binary-operator max :max maximum)
(define-binary-operator = :eql equality)
(define-binary-operator != :neql not-equal)
(define-binary-operator < :less less-than)
(define-binary-operator <= :lseq less-or-equal)
(define-binary-operator > :grtr greater-than)
(define-binary-operator >= :gteq greater-of-equal)
(define-binary-operator shl :shl shift-left)
(define-binary-operator shr :shr shift-right)
(define-binary-operator shra :shra shift-right-arithmetic)
(define-binary-operator and :and logical-and)
(define-binary-operator or :or logical-or)
(define-binary-operator xor :xor logical-exclusive-or)
(define-unary-operator  * :ind indirection)
(define-binary-operator >. :elt element)
(define-binary-operator *. :indelt element-indirection)
(define-unary-operator  - :neg arithmetic-negation)
(define-unary-operator  ! :not logic-negation)
(define-unary-operator  addr :addr address-of)
(define-unary-operator  val :val value)
(define-binary-operator cast :cast cast)
(define-binary-operator lind :lind indirect-assignment)
(define-binary-operator lcond :lcond conditional-assignment)
(define-binary-operator lindelt :lindelt indirect-element-assignment)
(define-binary-operator lelt :lelt element-assignment)

;;;;
;;;; Instructions
;;;;
(defclass inst ()
  ((has-left :reader has-left-p :type boolean :allocation :class :initarg :has-left-p)))

(defclass hir-inst (inst) ())
(defclass mir-inst (inst) ())
(defclass lir-inst (inst) ())
(defclass lir-memaddr-inst (lir-inst) ())

(defclass inst-with-left (inst)
  ((left :accessor inst-left :initarg :left)))

(defgeneric inst-has-left-p (inst)
  (:method ((o inst))) (:method ((o inst-with-left)) t))

(defclass control-transfer-inst (inst) ())

(defgeneric control-transfer-p (inst)
  (:method ((o inst))) (:method ((o control-transfer-inst)) t))

(defclass inst-kind-mixin () 
  ((kind :initarg :kind :reader kind :allocation :class :documentation
         "Expression kind short-hand synonim, as per Muchnick.")))
(defclass nullary (inst-kind-mixin) ((kind :allocation :class :initform :noexp)))
(defclass unary (inst-kind-mixin)   ((kind :allocation :class :initform :unexp)))
(defclass binary (inst-kind-mixin)  ((kind :allocation :class :initform :binexp)))
(defclass ternary (inst-kind-mixin)  ((kind :allocation :class :initform :ternexp)))
(defclass listary (inst-kind-mixin) ((kind :allocation :class :initform :listexp)))

(defvar *insts* (make-hash-table :test 'eq)
  "Map of short names (per Muchnick) to classes.")

(define-root-container *insts* inst :type class)

(defmacro define-inst (principal-type short-name name lambda-list &optional print-spec)
  (when-let ((unknowns (set-difference (mapcar #'ensure-car lambda-list)
                                       '(<- &rest args label procname eltname trapno const typename
                                         unop binop
                                         varname varname1 varname2 operand operand1 operand2
                                         ;; hir
                                         subscripts operand3
                                         ;; lir
                                         integer integer1 integer2 regname regname1 regname2 regname3 liroperand liroperand1 liroperand2
                                         memaddr length))))
    (error "~@<Unknown components in IR instruction definitions:~{ ~S~}.~:@>" unknowns))
  (let* ((left (when (find '<- lambda-list)
                 (first lambda-list)))
         (ctran ;; XXX
          )
         (normalised-lambda-list (remove '<- lambda-list))
         (kind (cond ((find 'operand normalised-lambda-list) 'unary)
                     ((find 'operand1 normalised-lambda-list) 'binary)
                     ((find 'operand3 normalised-lambda-list) 'ternary)
                     ;; Arbitrary: operand reference takes precedence over &rest wrt. determining inst arity
                     ((find '&rest normalised-lambda-list) 'listary)
                     (t 'nullary)))
         (normalised-lambda-list2 (remove '&rest (nsubst 'op 'unop (nsubst 'op 'binop normalised-lambda-list))))
         (initarg-names (mapcar (compose #'make-keyword #'symbol-name) normalised-lambda-list2)))
    `(progn
       (defclass ,name (,kind ,@(when left '(inst-with-left)) ,@(when ctran '(control-transfer-inst)) ,principal-type)
         (,@(iter (for slot-name in normalised-lambda-list2)
                  (let* ((type (case slot-name
                                 (op 'operator)
                                 ((args subscripts) 'list)
                                 (const 'real)
                                 (trapno 'integer)
                                 ((label procname eltname typename varname varname1 varname2) 'keyword)))
                         (accessor-name (format-symbol (symbol-package name) "INST-~A" slot-name))
                         (initarg-name (make-keyword (symbol-name slot-name)))
                         (final-slot-name (if (and left (member slot-name '(varname varname1) :test #'eq))
                                              'left
                                              slot-name)))
                    (collect `(,final-slot-name
                               :accessor ,accessor-name
                               :initarg ,initarg-name
                               ,@(when type `(:type ,type))))))))
       (defun ,(format-symbol (symbol-package name) "MAKE-~A" name) ,normalised-lambda-list2
         (make-instance ',name ,@(iter (for initarg in initarg-names)
                                       (for slot in normalised-lambda-list2)
                                       (collect initarg)
                                       (collect slot))))
       ,@(when print-spec
               (destructuring-bind (control-string &rest args) (ensure-list print-spec)
                 `((defmethod print-object ((o ,name) stream)
                     (with-slots ,normalised-lambda-list2 o
                       (declare (ignorable ,@normalised-lambda-list2))
                       (format stream ,control-string ,@(or args normalised-lambda-list2)))))))
       (setf (inst ,short-name) (find-class ',name)))))

(defmacro define-hir-inst (short-name name lambda-list &optional print-spec)
  `(define-inst hir-inst ,short-name ,name ,lambda-list ,print-spec))
(defmacro define-mir-inst (short-name name lambda-list &optional print-spec)
  `(define-inst mir-inst ,short-name ,name ,lambda-list ,print-spec))
(defmacro define-lir-inst (short-name name lambda-list &optional print-spec)
  `(define-inst lir-inst ,short-name ,name ,lambda-list ,print-spec))
(defmacro define-lir-memaddr-inst (short-name name lambda-list &optional print-spec)
  `(define-inst lir-memaddr-inst ,short-name ,name ,lambda-list ,print-spec))

(define-hir-inst :for         for                                (varname <- operand1 operand2 operand3)               "for ~(~A~) <- ~(~A~) by ~(~A~) to ~(~A~) do")
(define-hir-inst :endfor      endfor                             ()                                                    "endfor")
(define-hir-inst :strbinif    binary-hir-condition               (operand1 binop operand2)                             "if ~(~A~) ~A ~(~A~) then")
(define-hir-inst :strunif     unary-hir-condition                (unop operand)                                        "if ~A ~(~A~) then")
(define-hir-inst :strvalif    value-hir-condition                (operand)                                             "if ~(~A~) then")
(define-hir-inst :else        else                               ()                                                    "else")
(define-hir-inst :endif       endif                              ()                                                    "endif")
(define-hir-inst :arybinasgn  array-binary-assignment            (varname &rest subscripts <- operand1 binop operand2) "~(~A~)[~{, ~A~}] <- ~(~A~) ~A ~(~A~)")
(define-hir-inst :aryunasgn   array-unary-assignment             (varname &rest subscripts <- binop operand)           "~(~A~)[~{, ~A~}] <- ~A ~(~A~)")
(define-hir-inst :aryvalasgn  array-value-assignment             (varname &rest subscripts <- operand)                 "~(~A~)[~{, ~A~}] <- ~(~A~)")
(define-hir-inst :aryref      array-reference                    (varname &rest subscripts)                            "~(~A~)[~{, ~A~}]")
;;; BOOK: aryref kind unspecified (and leftness, but it's obvious)


(define-mir-inst :label       label                              (label)                                               ":~(~A~)")
(define-mir-inst :receive     receive                            (varname <- typename)                                 "receive ~(~A~)(~A)")
(define-mir-inst :binasgn     binary-assignment                  (varname <- operand1 binop operand2)                  "~(~A~) <- ~(~A~) ~A ~(~A~)")
(define-mir-inst :unasgn      unary-assignment                   (varname <- unop operand)                             "~(~A~) <- ~A ~(~A~)")
(define-mir-inst :valasgn     value-assignment                   (varname <- operand)                                  "~(~A~) <- ~(~A~)")
(define-mir-inst :condasgn    conditional-assignment             (varname1 <- varname2 operand)                        "~(~A~) <- (~(~A~)) ~(~A~)")
(define-mir-inst :castasgn    cast-assignment                    (varname <- typename operand)                         "~(~A~) <- (~(~A~)) ~(~A~)")
(define-mir-inst :indasgn     indirected-assignment              (varname <- operand)                                  "*~(~A~) <- ~(~A~)")
(define-mir-inst :eltasgn     element-assignment                 (varname eltname <- operand)                          "~(~A~).~(~A~) <- ~(~A~)")
(define-mir-inst :indeltasgn  indirect-element-assignment        (varname eltname <- operand)                          "*~(~A~).~(~A~) <- ~(~A~)")
(define-mir-inst :goto        goto                               (label)                                               "goto ~(~A~)")
(define-mir-inst :binif       binary-condition                   (operand1 binop operand2 label)                       "if ~(~A~) ~A ~(~A~) goto ~(~A~)")
(define-mir-inst :unif        unary-condition                    (unop operand label)                                  "if ~A ~(~A~) goto ~(~A~)")
(define-mir-inst :valif       value-condition                    (operand label)                                       "if ~(~A~) goto ~(~A~)")
(define-mir-inst :bintrap     binary-trap                        (operand1 binop operand2 trapno)                      "if ~(~A~) ~A ~(~A~) trap #x~X")
(define-mir-inst :untrap      unary-trap                         (unop operand trapno)                                 "if ~A ~(~A~) trap #x~X")
(define-mir-inst :valtrap     value-trap                         (operand trapno)                                      "if ~(~A~) trap #x~X")
(define-mir-inst :call        call                               (procname &rest args)                                 "call ~(~A~)~{ ~A~}")
(define-mir-inst :callasgn    call-assignment                    (varname <- procname &rest args)                      "~(~A~) <- call ~(~A~)~{ ~A~}")
(define-mir-inst :return      just-return                        ()                                                    "return")
(define-mir-inst :retval      return-value                       (operand)                                             "return ~(~A~)")
(define-mir-inst :sequence    memory-barrier                     ()                                                    "sequence")
(define-mir-inst :var         variable-reference                 (varname)                                             "~(~A~)")
(define-mir-inst :const       constant-value                     (const)                                               "~(~A~)")
(define-mir-inst :tn          type-name                          (typename)                                            "~(~A~)")

;; label skipped
(define-lir-inst :regbin      register-binary-assignment         (regname <- liroperand1 binop liroperand2)            "~(~A~) <- ~(~A~) ~A~(~A~)")
(define-lir-inst :regun       register-unary-assignment          (regname <- unop liroperand)                          "~(~A~) <- ~A ~(~A~)")
(define-lir-inst :regval      register-value-assignment          (regname <- liroperand)                               "~(~A~) <- ~(~A~)")
(define-lir-inst :regcond     conditional-register-assignment    (regname1 <- regname2 liroperand)                     "~(~A~) <- (~(~A~)) ~(~A~)")
;; BOOK: fig. 4.11 says regcond has no left -- table 4.9 says it does.
(define-lir-inst :regelt      register-bitfield-assignment       (regname integer1 integer2 <- liroperand)             "~(~A~)[~A:~A] <- ~(~A~)")
;; BOOK: fig. 4.11 says regelt has no left -- table 4.9 says it does.
(define-lir-inst :stormem     memory-store                       (memaddr <- liroperand)                               "~A <- ~(~A~)")
;; XXX: memaddr on the left -> not a real left
(define-lir-inst :loadmem     memory-load                        (regname <- memaddr)                                  "~(~A~) <- ~A")
(define-lir-inst :lirgoto     lir-goto                           (label)                                               "goto ~(~A~)")
(define-lir-inst :gotoaddr    computed-goto                      (regname integer)                                     "goto ~(~A~) + #x~X")
(define-lir-inst :regbinif    register-binary-condition          (liroperand1 binop liroperand2 label)                 "if ~(~A~) ~A ~(~A~) goto ~(~A~)")
(define-lir-inst :regunif     register-unary-condition           (unop liroperand label)                               "if ~A ~(~A~) goto ~(~A~)")
(define-lir-inst :regvalif    register-value-condition           (liroperand label)                                    "if ~(~A~) goto ~(~A~)")
(define-lir-inst :bintrap     register-binary-trap               (liroperand1 binop liroperand2 trapno)                "if ~(~A~) ~A ~(~A~) trap #x~X")
(define-lir-inst :untrap      register-unary-trap                (unop liroperand trapno)                              "if ~A ~(~A~) trap #x~X")
(define-lir-inst :valtrap     register-value-trap                (liroperand trapno)                                   "if ~(~A~) trap #x~X")
(define-lir-inst :callreg     constant-call                      (procname regname)                                    "call ~(~A~) ~(~A~)")
(define-lir-inst :callreg2    register-call                      (regname1 regname2)                                   "call ~(~A~) ~(~A~)")
(define-lir-inst :callregasgn constant-call-assignment           (regname1 <- procname regname2)                       "~(~A~) <- call ~(~A~) ~(~A~)")
(define-lir-inst :callreg3    register-call-assignment           (regname1 <- regname2 regname3)                       "~(~A~) <- call ~(~A~) ~(~A~)")
(define-lir-inst :lirretval   lir-return-value                   (liroperand)                                          "return ~(~A~)")
(define-lir-inst :regno       register-reference                 (regname)                                             "~(~A~)")
(define-lir-inst :lirtn       lir-type-name                      (typename)                                            "~(~A~)")
;; BOOK: LIR typename vs. MIR TNi

(define-lir-memaddr-inst :addr1r register-memory-reference          (regname length)                                   "[~(~A~)](~A)")
(define-lir-memaddr-inst :addr2r register-register-memory-reference (regname1 regname2 length)                         "[~(~A~)+~(~A~)](~A)")
(define-lir-memaddr-inst :addrrc register-constant-memory-reference (regname integer length)                           "[~(~A~)+~(~A~)](~A)")

;;;;
;;;; Function
;;;;
(defclass basic-block ()
  ((pred :accessor bb-pred :initform nil)
   (succ :accessor bb-succ :initform nil)
   (insts :accessor bb-insts :initform (make-array 0 :element-type 'inst :adjustable t))))

(defclass procedure ()
  ((name :reader proc-name :initarg :name)
   (blocks :accessor proc-blocks :initarg :blocks :initform (make-array 0 :element-type 'basic-block :adjustable t))
   (lblocks :accessor proc-lblocks :initarg :lblocks :initform (make-array 0 :element-type 'basic-block :adjustable t))))

(defgeneric insert-before (block inst i)
  (:method ((o basic-block) (inst inst) i)
    (with-slots (insts) o
      (setf insts (adjust-array insts (1+ (length insts)) :element-type inst)
            (subseq insts (1+ i)) (subseq insts i (1- (length insts)))
            (aref insts i) inst))))
(defgeneric insert-after (block inst i)
  (:method ((o basic-block) (inst inst) i)
    (with-slots (insts) o
      (setf insts (adjust-array insts (1+ (length insts)) :element-type inst))
      (let ((lastidx (- (length insts) 2)))
        (cond ((and (= i lastidx)
                    (control-transfer-p (aref insts lastidx)))
               (setf (aref insts (1+ lastidx)) (aref insts lastidx)
                     (aref insts lastidx) inst))
              (t
               (setf 
                     (subseq insts (+ 2 i)) (subseq insts (1+ i) (1- (length insts)))
                     (aref insts (1+ i)) inst)))))))
(defgeneric append-block (block inst)
  (:method ((o basic-block) (inst inst))
    (insert-after o inst (1- (length (bb-insts o))))))

;;;
;;; IR1
;;;
(defun comp-typep (x type)
  (if (consp type)
      (ecase (first type)
        (and (not (null (every (curry #'comp-typep x) (rest type)))))
        (or (not (null (some (curry #'comp-typep x) (rest type))))))
      (ecase type
        (boolean (member x '(t nil)))
        (integer (typep x '(unsigned-byte 32)))
        (nil nil)
        ((t) t))))

(defun comp-type-of (x)
  (cond ((member x '(t nil)) 'boolean)
        ((typep x '(unsigned-byte 32)) 'integer)
        (t t)))

(defun comp-simplify-logical-expression (x &aux (pass-list '(fold-constants remove-duplicates unnest-similars detrivialize recurse)))
  (cond ((atom x) x)
        ((= 2 (length x)) (comp-simplify-logical-expression (second x)))
        (t
         (cons (first x) (let ((state pass-list)
                               (x-body (rest x)))
                           (block machine-collector
                             (tagbody
                              loop
                                (let ((xform (case (car state)
                                               (fold-constants
                                                (lambda ()
                                                  (ecase (first x)
                                                    (or (if (member t (rest x))
                                                            (return-from comp-simplify-logical-expression t)
                                                            (remove nil x-body)))
                                                    (and (if (member nil (rest x))
                                                             (return-from comp-simplify-logical-expression nil)
                                                             (remove t x-body))))))
                                               (remove-duplicates
                                                (lambda ()
                                                  (remove-duplicates x-body :test #'eq)))
                                               (unnest-similars
                                                (lambda ()
                                                  (multiple-value-bind (nested-similars others) (unzip (lambda (subx)
                                                                                                         (and (consp subx) (eq (car subx) (car x))))
                                                                                                       x-body)
                                                    (apply #'append (cons others (mapcar #'rest nested-similars))))))
                                               (detrivialize
                                                (lambda ()
                                                  (if (null (cdr x-body))
                                                      (values (car x-body) t)
                                                      x-body)))
                                               (recurse
                                                (lambda ()
                                                  (mapcar #'comp-simplify-logical-expression x-body))))))
                                  (if xform
                                      (multiple-value-bind (processed-x-body trivial-p) (funcall xform)
                                        (cond (trivial-p
                                               (return-from comp-simplify-logical-expression
                                                 (comp-simplify-logical-expression processed-x-body)))
                                              ((equalp processed-x-body x-body)
                                               (setf state (cdr state)))
                                              (t
                                               (setf state pass-list
                                                     x-body processed-x-body)))
                                        (go loop))
                                      (return-from machine-collector x-body))))))))))

(defclass var ()
  ((name :accessor var-name :initarg :name)))

(defclass frame ()
  ((dominator :accessor frame-dominator :initarg :dominator)
   (vars :accessor frame-vars :initarg :vars)))

(defclass expr-like ()
  ((type :accessor expr-type :type (or symbol list) :initarg :type)
   (effect-free :accessor expr-effect-free :type boolean :initarg :effect-free)
   (pure :accessor expr-pure :type boolean :initarg :pure)
   (branching :accessor expr-branching :type (or null (member :tail :non-tail :funcall)) :initarg :branching)))

(defclass expr (expr-like)
  ((value-used :accessor expr-value-used :type boolean :initarg :value-used)
   (env :accessor expr-env :type (or null frame) :initarg :env)
   (form :accessor expr-form :initarg :form)
   (code :accessor expr-code :initarg :code)
   (df-code :accessor expr-df-code :initform nil :documentation "DF nodes in CODE order (to facilitate side-effect ordering preservation).")))

(define-print-object-method ((o expr) effect-free pure value-used type code)
    "~@<#<EXPR ~;effect-free: ~S, pure: ~S, used: ~S, type: ~S~_~{~S~:@_~}~;>~:@>" effect-free pure value-used type code) ;

(defclass tn (expr)
  ()
  (:documentation "An EXPR whose result requires attention of the register allocator."))

(define-protocol-class dfnode ()
  ((generator :accessor generator :initarg :generator))
  (:documentation "Data flow node."))
(define-print-object-method ((o dfnode) generator)
    "~@<#<~;~A ~S~;>~:@>" (type-of o) generator)

(define-protocol-class dfproducer (dfnode) ((consumers :accessor consumers :initform nil :initarg :consumers)))
(define-protocol-class dfconsumer (dfnode) ((producers :accessor producers :initarg :producers)))
(define-print-object-method ((o dfconsumer) generator producers)
    "~@<#<~;~A ~S~_~{~S~:@_~}~;>~:@>" (type-of o) generator producers)

(define-protocol-class dfcontinue (dfproducer dfconsumer) ())
(define-protocol-class dfextremum (dfnode) ())

(define-protocol-class dfstart (dfextremum dfproducer) ())
(define-protocol-class dfend (dfextremum dfconsumer) ())

(define-protocol-class dffanin (dfconsumer) ())
(define-protocol-class dffanout (dfproducer) ())
(define-protocol-class dfnotfan (dfnode) ())

;; neither a producer, nor a consumer, a category of its own
(defclass dfnop (dfnotfan) ())

(defclass dfhead (dfstart dfnotfan) ())
(defclass dftail (dfend dfnotfan) ())
(defclass dfpipe (dfcontinue dfnotfan) ())

(defclass dfstartfan (dfstart dffanout) ())
(defclass dfendfan (dfend dffanin) ())
(defclass dfuga (dfcontinue dffanout) ())
(defclass dfagu (dfcontinue dffanin) ())

(defclass dfhedge (dfcontinue dffanout dffanin) ())

(defun compute-df-class (input output &aux (input (min 2 input)) (output (min 2 output)))
  (cdr (find (cons input output)
             '(((0 . 0) . dfnop)
               ((0 . 1) . dfhead) ((1 . 0) . dftail) ((1 . 1) . dfpipe)
               ((2 . 0) . dfendfan) ((0 . 2) . dfstartfan) ((2 . 1) . dfagu) ((1 . 2) . dfuga) ((2 . 2) . dfhedge))
             :key #'car :test #'equal)))

(defclass expr-var (var)
  ((expr :accessor var-expr :type expr :initarg :expr)))

(defclass func ()
  ((name :accessor func-name :type symbol :initarg :name)
   (nargs :accessor func-nargs :type (integer 0) :initarg :nargs)
   (nvalues :accessor func-nvalues :type (integer 0) :initarg :nvalues)
   (leafp :accessor func-leafp :type boolean :initarg :leafp)))

(defclass primop (expr-like func)
  ((valuep :accessor primop-valuep :type boolean :initarg :valuep)
   (instantiator :accessor primop-instantiator :type function :initarg :instantiator)
   (folder :accessor primop-folder :type function :initarg :folder)
   (papplicable-p :accessor primop-papplicable-p :type function :initarg :papplicable-p)
   (papplicator :accessor primop-papplicator :type function :initarg :papplicator)))

(defclass expr-func (func)
  ((lambda-list :accessor func-lambda-list :type list :initarg :lambda-list)
   (expr :accessor func-expr :type expr :initarg :expr)
   (complete :accessor func-complete :type boolean :initarg :complete)))

(defmethod expr-type ((o expr-func)) (expr-type (func-expr o)))
(defmethod expr-effect-free ((o expr-func)) (expr-effect-free (func-expr o)))
(defmethod expr-pure ((o expr-func)) (expr-pure (func-expr o)))

(define-print-object-method ((o func) name nargs leafp)
    "~@<#<FUNC ~;~S, ~S args, leafp: ~S, type: ~S, effect-free: ~S>~:@>" name nargs leafp (expr-type o) (expr-effect-free o))

(defparameter *primops* (make-hash-table :test 'eq))

(define-root-container *primops* primop :if-exists :error)

(defclass compenv ()
  ((functions :accessor compenv-functions :initform (make-hash-table :test 'eq))
   (macros :accessor compenv-macros :initform (make-hash-table :test 'eq))))
(define-subcontainer func :container-slot functions :type expr-func :if-exists :error)
(define-subcontainer macro :container-slot macros :type function :if-exists :error)

(defun frame-boundp (name frame)
  (find name (frame-vars frame) :key #'var-name))

(defun env-boundp (name env)
  (and env
       (or (frame-boundp name env)
           (env-boundp name (frame-dominator env)))))

(defun make-frame-from-vars (vars dominator)
  (make-instance 'frame :dominator dominator :vars vars))

(defun make-frame-from-var-names (var-names dominator)
  (make-frame-from-vars (mapcar (curry #'make-instance 'var :name) var-names) dominator))

(defvar *sexp-path* nil)

(defmacro with-noted-sexp-path (designator &body body)
  `(let ((*sexp-path* (cons ,designator *sexp-path*)))
     (declare (special *sexp-path*))
     ,@body))

(defun expr-error (format-control &rest format-arguments)
  (apply #'comp-error (format nil "~~@<In ~~S: ~A.~~:@>" format-control) *sexp-path* format-arguments))

(defun compiler-note (format-control &rest format-arguments)
  (apply #'format t (format nil "~~@<; ~~@;note: ~A.~~:@>~%" format-control) format-arguments))

;;;
;;; IR2
;;;
(defstruct vop
  nargs
  nvalues
  code)

(defmethod print-object ((o vop) stream)
  (print-unreadable-object (o stream)
    (format stream "VOP ~S" (vop-code o))))

(defun emit-label (name)
  (list name))

(defun emit-constant (value)
  (list (make-vop :nargs 0 :nvalues 1 :code `(const ,value))))

(defun emit-lvar-ref (lvar)
  (list (make-vop :nargs 0 :nvalues 1 :code `(lvar-ref ,lvar))))

(defun emit-lvar-set (lvar)
  (list (make-vop :nargs 1 :nvalues 0 :code `(lvar-set ,lvar))))

(defun emit-funarg-set (i)
  (list (make-vop :nargs 1 :nvalues 0 :code `(funarg-set ,i))))

(defun emit-save-continuation (label)
  (list (make-vop :nargs 0 :nvalues 1 :code `(save-continuation ,label))))

(defun emit-jump (label)
  (list (make-vop :nargs 0 :nvalues 0 :code `(jump ,label))))

(defun emit-jump-if (label)
  (list (make-vop :nargs 1 :nvalues 0 :code `(jump-if ,label))))

(defun emit-jump-if-not (label)
  (list (make-vop :nargs 1 :nvalues 0 :code `(jump-if-not ,label))))

(defun emit-return ()
  (list (make-vop :nargs 1 :nvalues 0 :code `(return))))

(defun emit-primitive (name nargs nvalues &rest primitive-args)
  (list (make-vop :nargs nargs :nvalues nvalues :code `(primitive ,name ,@primitive-args))))

;;;
;;; The megaquestion is whether PRIMOP's expr slot is warranted.
;;;
(defun instantiate-simple-primop (primop valuep args arg-exprs &aux (name (func-name primop)))
  (unless (= (length args) (func-nargs primop))
    (error "~@<~S was provided the wrong amount of values: ~D, expected ~D.~:@>" primop (length args) (func-nargs primop)))
  (make-instance 'expr :effect-free (expr-effect-free primop) :pure (expr-pure primop) :value-used valuep :env nil
                 :type (expr-type primop) :branching (expr-branching primop) :form `(,name ,@args) 
                 :code (append arg-exprs
                               (emit-primitive name (func-nargs primop) (func-nvalues primop)))))

(defun ensure-primitive (name nargs nvalues type valuep effect-free pure branching &key folder-fn (instantiator-fn #'instantiate-simple-primop)
                         (papplicable-p (constantly nil)) papplicator-fn)
  (setf (primop name) (make-instance 'primop :name name :nargs nargs :nvalues nvalues :leafp t :type type :valuep valuep :effect-free effect-free :pure pure
                                     :branching branching
                                     :instantiator instantiator-fn
                                     :folder folder-fn
                                     :papplicable-p papplicable-p :papplicator papplicator-fn)))

(defmacro defprimitive (name nargs nvalues type valuep effect-free pure branching &rest args)
  (let ((instantiator (rest (find :instantiator args :key #'car)))
        (folder (rest (find :folder args :key #'car)))
        (papplicable-p (rest (find :papplicable-p args :key #'car)))
        (papplicator (rest (find :papplicator args :key #'car))))
   `(ensure-primitive ',name ,nargs ,nvalues ',type ,valuep ,effect-free ,pure ,branching
                      ,@(when instantiator
                              `(:instantiator-fn (lambda ,(first instantiator) ,@(rest instantiator))))
                      ,@(when folder
                              `(:folder-fn (lambda ,(first folder) ,@(rest folder))))
                      ,@(when papplicable-p
                              (unless papplicator
                                (comp-error "~@<In DEFPRIMITIVE ~S: PAPPLICABLE-P specified without PAPPLICATOR.~:@>" name))
                              `(:papplicable-p (lambda ,(first papplicable-p) ,@(rest papplicable-p))))
                      ,@(when papplicator
                              (unless papplicable-p
                                (comp-error "~@<In DEFPRIMITIVE ~S: PAPPLICATOR specified without PAPPLICABLE-P.~:@>" name))
                              `(:papplicator-fn (lambda ,(first papplicator) ,@(rest papplicator)))))))

(defprimitive +              2 1 integer t   t   t   nil
  (:folder (arg-exprs tailp)
    (compile-constant (apply #'+ (mapcar #'expr-form arg-exprs)) t tailp)))
(defprimitive -              2 1 integer t   t   t   nil)
(defprimitive logior         2 1 integer t   t   t   nil)
(defprimitive logand         2 1 integer t   t   t   nil)
(defprimitive logxor         2 1 integer t   t   t   nil)
(defprimitive ash            2 1 integer t   t   t   nil
  (:folder (arg-exprs tailp)
    (compile-constant (apply #'ash (mapcar #'expr-form arg-exprs)) t tailp))
  (:papplicable-p (arg-exprs &aux (shift (expr-form (second arg-exprs))))
    (and (integerp shift) (zerop shift)))
  (:papplicator (arg-exprs)
    (first arg-exprs)))
(defprimitive lognot         1 1 integer t   t   t   nil)
(defprimitive =              2 1 boolean t   t   t   nil)
(defprimitive /=             2 1 boolean t   t   t   nil)
(defprimitive >=             2 1 boolean t   t   t   nil)
(defprimitive <=             2 1 boolean t   t   t   nil)
(defprimitive >              2 1 boolean t   t   t   nil)
(defprimitive <              2 1 boolean t   t   t   nil)
(defprimitive mem-ref        2 1 integer t   t   nil nil)
(defprimitive mem-set        3 0 nil     nil nil nil nil)
(defprimitive mem-ref-impure 2 1 integer t   nil nil nil)
(defprimitive funarg-ref     2 1 t       t   t   t   nil
  (:instantiator (primop valuep args arg-exprs &aux (type (second args)))
    (declare (ignore arg-exprs))
    (make-instance 'expr :effect-free t :pure t :value-used valuep :env nil
                   :type type :branching nil :form `(,(func-name primop) ,@args)
                   :code (apply #'emit-primitive 'funarg-ref 0 1 args))))

;;;
;;; Actual compilation
;;;
;; Invariants:
;;  (not valuep) -> (not tailp)
;;  (expr-effect-free x) -> (compile-xxx x env nil nil) => nil
;;;
;;; General notes.
;;;
;;; A simplification candidate: DFA might be entirely enough to shake out effect-free dead code.
;;; Practical equivalence of IR1 transforms to it must be seen, though, if not proven.
;;;
;;; Another simplification candidate: some kind of constituent iteration can simplify branching analysis.
;;; Turning CODE sequences of EXPRs into a form useful for that would take:
;;;   - a shift of label generation into a later point,
;;;   - an increase of branch target granularity to EXPRs.
;;;
(defun constant-p (expr)
  (or (eq expr 't)
      (eq expr 'nil)
      (integerp expr)))

(defun degrade-tail-branching (x)
  (if (eq x :tail)
      :non-tail
      x))

(defun maybe-wrap-with-return (wrap-p expr)
  (if wrap-p
      (make-instance 'expr :effect-free (expr-effect-free expr) :pure (expr-pure expr) :value-used t :env nil
                     :type (expr-type expr) :branching (degrade-tail-branching (expr-branching expr)) :form `(return ,(expr-code expr))
                     :code
                     (append (list expr)
                             (emit-return)))
      expr))

(defmacro with-return-wrapped-if (wrap-p &body expr)
  `(maybe-wrap-with-return ,wrap-p ,@expr))

(defun compile-constant (expr valuep tailp)
  (unless (constant-p expr)
    (expr-error "attempted to compile non-constant expression ~S as constant" expr))
  (when valuep
    (with-return-wrapped-if tailp
      (make-instance 'expr :effect-free t :pure t :value-used t :env nil
                     :type (comp-type-of expr) :branching nil :form expr
                     :code
                     (emit-constant (case expr
                                      ((t) 1)
                                      ((nil) 0)
                                      (t expr)))))))

(defun compile-variable-ref (var lexenv valuep tailp)
  (with-noted-sexp-path var
    (unless (env-boundp var lexenv)
      (expr-error "~S not bound" var))
    (when valuep
      (with-return-wrapped-if tailp
        (make-instance 'expr :effect-free t :pure nil :value-used t :env lexenv
                       :type t :branching nil :form var
                       :code
                       (emit-lvar-ref var))))))

(defun compile-variable-set (var value compenv lexenv valuep tailp)
  (with-noted-sexp-path `(setf ,var)
    (unless (env-boundp var lexenv)
      (expr-error "~S not bound" var))
    (with-return-wrapped-if tailp
      (let ((value-expr (if (typep value 'expr)
                            value
                            (compile-expr value compenv lexenv t nil))))
        (make-instance 'expr :effect-free nil :pure nil :value-used valuep :env lexenv
                       :type (expr-type value-expr) :branching nil :form `(setf ,var ,(expr-form value-expr))
                       :code
                       (append (list value-expr)
                               (emit-lvar-set var)))))))

(defvar *compiled-function*)

(defun compile-funcall (fname args compenv lexenv valuep tailp)
  (let ((func (or (func compenv fname :if-does-not-exist :continue)
                  (primop fname :if-does-not-exist :continue))))
    (unless func
      (expr-error "reference to undefined function ~S" fname))
    (unless (= (length args) (func-nargs func))
      (expr-error "wrong argument count in call of ~S: got ~D, expected ~D"
                  fname (length args) (func-nargs func)))
    (with-noted-sexp-path `(funcall ,fname)
      (let* ((args-code (mapcar (rcurry #'compile-expr compenv lexenv t nil) args))
             (effect-free (every #'expr-effect-free (cons func args-code)))
             (pure (and effect-free (expr-pure func) (every #'expr-pure args-code))))
        (when (or valuep (not effect-free))
          (cond ((typep func 'primop)
                 (cond ((and pure (primop-folder func))
                        (funcall (primop-folder func) args-code tailp))
                       ((funcall (primop-papplicable-p func) args-code)
                        (with-return-wrapped-if tailp
                          (funcall (primop-papplicator func) args-code)))
                       (t
                        (with-return-wrapped-if tailp
                          (funcall (primop-instantiator func) func valuep args args-code)))))
                (t
                 (when (and (boundp '*compiled-function*)
                            (func-leafp *compiled-function*))
                   (compiler-note "degrading ~S to non-leaf" *compiled-function*)
                   (setf (func-leafp *compiled-function*) nil))
                 (make-instance 'expr :effect-free effect-free :pure pure :value-used valuep :env lexenv
                                :type (if (and (boundp '*compiled-function*)
                                               (eq func *compiled-function*))
                                          nil
                                          (expr-type func))
                                :branching :funcall
                                :form `(,fname ,@args)
                                :code (let ((ret-label (gensym (concatenate 'string "BACK-FROM-" (symbol-name fname)))))
                                        (append (iter (for arg-code in args-code)
                                                      (for i from 0)
                                                      (collect (make-instance 'expr :effect-free nil :pure nil :value-used t :env lexenv
                                                                              :type (expr-type arg-code) :form `(funarg-set ,i ,(expr-form arg-code))
                                                                              :code
                                                                              (append (list arg-code)
                                                                                      (emit-funarg-set i)))))
                                                (unless tailp
                                                  (emit-save-continuation ret-label))
                                                (emit-jump fname)
                                                (unless tailp
                                                  (emit-label ret-label))))))))))))

;;;
;;; Non-leaf expressions
;;;
(defun compile-progn (expr compenv lexenv valuep tailp)
  (if expr
      (let* ((for-effect (remove nil (mapcar (rcurry #'compile-expr compenv lexenv nil nil) (butlast expr))))
             (for-value (compile-expr (lastcar expr) compenv lexenv tailp valuep))
             (effect-free (and (null for-effect) (expr-effect-free for-value)))
             (pure (and effect-free (expr-pure for-value))))
        (when (or valuep (not effect-free))
          (make-instance 'expr :effect-free effect-free :pure pure :value-used valuep :env lexenv
                         :type (expr-type for-value) :form `(progn ,@expr)
                         :branching (cond ((find :funcall for-effect :key #'expr-branching) :funcall)
                                          ((find :tail for-effect :key #'expr-branching) :non-tail)
                                          ((find :non-tail for-effect :key #'expr-branching) :non-tail)
                                          (for-value (expr-branching for-value)))
                         :code
                         (append for-effect
                                 ;; for-value is NIL iff (and (not valuep) (expr-effect-free for-value-expr))
                                 ;; which implies (not tail)
                                 (when for-value
                                   (list for-value))))))
      (compile-constant nil valuep tailp)))

;;; For now, we can't rely much on VAR-EXPR.
(defun compile-let (bindings body compenv lexenv valuep tailp)
  (with-noted-sexp-path 'let
    (let* ((binding-value-code (mapcar (rcurry #'compile-expr compenv lexenv t nil) (mapcar #'second bindings)))
           (vars (iter (for (name . nil) in bindings)
                       (for expr in binding-value-code)
                       (collect (make-instance 'expr-var :name name :expr expr))))
           (new-lexenv (make-frame-from-vars vars lexenv))
           (body-code (compile-progn body compenv new-lexenv valuep tailp))
           (effect-free (every #'expr-effect-free (cons body-code binding-value-code)))
           (pure (and effect-free (every #'expr-pure (cons body-code binding-value-code)))))
      (when (or valuep (not effect-free))
        (make-instance 'expr :effect-free effect-free :pure pure :value-used valuep :env lexenv
                       :type (expr-type body-code) :form `(let ,bindings ,@body)
                       :branching (cond ((find :funcall binding-value-code :key #'expr-branching) :funcall)
                                        ((find :tail binding-value-code :key #'expr-branching) :non-tail)
                                        ((find :non-tail binding-value-code :key #'expr-branching) :non-tail)
                                        (t (expr-branching body-code)))
                       :code
                       (append (iter (for var in vars)
                                     (collect (compile-variable-set (var-name var) (var-expr var) compenv new-lexenv nil nil)))
                               (list body-code)))))))

;;;
;;;   At this point we're past the fist pass, namely conversion of code
;;; into soup of PRIMOPs, carrying concrete details of:
;;;   - amount of required inputs and outputs, and
;;;   - expansion on specific architecture;
;;; and EXPR tree nodes, qualifying subtrees with:
;;;   - effect-fulness or, perhapes even purity, and
;;;   - type information.
;;;
;;;   Important invariants, simplifying (but, probably, not precluding)
;;; interpretation of the tree, are:
;;;   - dependencies are EXPR-local, i.e. EXPRs cannot have dependencies.
;;;   - whenever a VOP has dependencies, it must be the last one in its
;;; parent's EXPR CODE sequence;
;;;   - at the point of that particular VOP's occurence the amount of
;;; outstanding DF sticks must be equal to the amount of VOP's dependencies.
;;;
;;;   As it stands, EXPR's CODE sequences fall into two types:
;;;   - those ending with a producing VOP or EXPR, described above.
;;; Such entries will mark their parent EXPR as a DF producer.
;;;   - EXPRs which always have a zero DF producer count in their CODE
;;; sequence.
;;;
(defun build-data-flow-graph (parent soup consumer acc-producers)
  (etypecase soup
    (vop
     (unless (or consumer (zerop (vop-nargs soup)))
       (error "~@<Starved VOP ~S in ~S: requires ~D arguments, but wasn't marked as consumer.~:@>" soup parent (vop-nargs soup)))
     (when (and consumer (not (= (vop-nargs soup) (length acc-producers))))
       (error "~@<At expression ~S: producer count ~D, but VOP ~S expected ~D.~:@>" parent (length acc-producers) soup (vop-nargs soup)))
     (let ((dfnode (make-instance (compute-df-class (vop-nargs soup) (vop-nvalues soup))
                                  :generator soup
                                  :producers (when consumer acc-producers))))
       (when consumer
         (format t "~@<Consuming ~S.~:@>~%" acc-producers)
         (dolist (producer acc-producers)
           (push dfnode (consumers producer))))
       (format t "~@<VOP ~S prepending ~S to producers.~:@>~%" soup (when (typep dfnode 'dfproducer)
                                                                  (make-list (vop-nvalues soup) :initial-element dfnode)))
       (values (append (when (typep dfnode 'dfproducer)
                         (make-list (vop-nvalues soup) :initial-element dfnode))
                       (unless consumer acc-producers))
               dfnode)))
    (expr
     (when consumer
       (error "~@<EXPR ~S was marked as consumer.~:@>" soup))
     ;; Here's the point where we need CFA to perform separate iterations
     ;; on basic block, so as not to conflate BBs producers.
     ;; But if we localize passing to subnodes in branchy-branchy EXPRs,
     ;; shouldn't it justwork?
     (values
      (let (producers)
        (format t "~@<Processing ~S.~:@>~%" soup)
        (setf (expr-df-code soup)
              (iter (for (subsoup . rest-code) on (expr-code soup))
                    (format t "~@<Producers: ~S before sub ~S.~:@>~%" producers subsoup)
                    (multiple-value-bind (new-producers node)
                        (build-data-flow-graph soup subsoup (and (endp rest-code) (typep subsoup 'vop) (plusp (vop-nargs subsoup))) producers)
                      (etypecase node 
                        (dfnode (collect node))
                        (expr (appending (expr-df-code node))))
                      (setf producers new-producers))))
        (format t "~@<Prepending ~S to producers.~:@>~%" producers)
        (append producers acc-producers))
      soup))))

;;; NOTE: the expression doesn't contain the label, which must be emitted by the linker.
(defun compile-defun (name lambda-list body compenv)
  (with-noted-sexp-path `(defun ,name ,lambda-list ,@body)
    ;; Make a temporary, incomplete function object for the purpose of recursion, with expression lacking proper code,
    ;; and type being set to t.
    (let ((func (make-instance 'expr-func :name name :nargs (length lambda-list) :lambda-list lambda-list :leafp t :complete nil
                               :expr (make-instance 'expr :effect-free nil :pure nil :value-used t :env nil
                                                    :type t :form `(defun ,name ,lambda-list #:phony) :code nil))))
      (setf (func compenv name) func)
      (multiple-value-bind (docstring declarations body) (destructure-def-body body)
        (declare (ignore docstring))
        (lret ((type-decls (mapcar #'rest (remove-if-not (feq 'type) declarations :key #'car)))
              (*compiled-function* func))
          (declare (special *compiled-function*))
          (setf (func-expr func)
                (compile-let (iter (for arg-name in lambda-list)
                                   (for i from 0)
                                   (collect `(,arg-name (funarg-ref ,i ,(or (first (find name type-decls :key #'rest :test #'member)) t)))))
                             body
                             compenv nil t t)
                (func-complete func) t)
          ;; #+(or)
          (build-data-flow-graph nil (func-expr func) nil nil))))))

(defun compile-if (clauses compenv lexenv valuep tailp)
  (let ((n-args (length clauses)))
    (when (or (< n-args 2)
              (> n-args 3))
      (expr-error "invalid number of elements in IF operator: between 2 and 3 expected")))
  (destructuring-bind (condition then-clause &optional else-clause) clauses
    (let* ((condition-code (compile-expr condition compenv lexenv t nil))
           (then-code (compile-expr then-clause compenv lexenv valuep tailp))
           (else-code (if else-clause
                          (compile-expr else-clause compenv lexenv valuep tailp)
                          (compile-constant nil valuep tailp)))
           (effect-free (every #'expr-effect-free (list condition-code then-code else-code)))
           (pure (and effect-free (every #'expr-pure (list condition-code then-code else-code)))))
      (when (or valuep effect-free)
        (with-noted-sexp-path 'if
          (cond ((null condition) else-code)
                ((constant-p condition) then-code)
                ((equalp then-clause else-clause) (compile-progn `(,condition ,then-clause) compenv lexenv valuep tailp))
                ((and (= 2 (length condition)) (eq (first condition) 'not))
                 (compile-if `(if ,(second condition) ,then-clause ,else-clause) compenv lexenv valuep tailp))
                (t
                 (make-instance 'expr :effect-free effect-free :pure pure :value-used valuep :env lexenv
                                :type (comp-simplify-logical-expression `(or ,(expr-type then-code) ,(expr-type else-code)))
                                :form `(if ,condition ,then-clause ,@(when else-clause `(,else-clause)))
                                :branching (if (find :funcall (list condition-code then-code else-code) :key #'expr-branching)
                                               :funcall
                                               :non-tail)
                                :code
                                (let ((else-label (gensym (concatenate 'string "IF-NOT")))
                                      (end-label (gensym (concatenate 'string "IF-END"))))
                                  (append (list (make-instance 'expr :effect-free (expr-effect-free condition-code) :pure (expr-pure condition-code)
                                                               :value-used t :env lexenv
                                                               :type 'boolean :form condition
                                                               :code
                                                               (append (list condition-code)
                                                                       (emit-jump-if-not else-label))))
                                          (list then-code)
                                          (unless tailp
                                            (emit-jump end-label))
                                          (emit-label else-label)
                                          (list else-code)
                                          (unless tailp
                                            (emit-label end-label))))))))))))

(defun compile-expr (expr compenv lexenv valuep tailp)
  (when *comp-verbose*
    (compiler-note "compiling ~S" expr))
  (cond ((constant-p expr) (compile-constant expr valuep tailp))
        ((symbolp expr) (compile-variable-ref expr lexenv valuep tailp))
        ((atom expr)
         (expr-error "atom ~S has unsupported type ~S" expr (type-of expr)))
        (t
         (case (car expr)
           (progn (compile-progn (rest expr) compenv lexenv valuep tailp))
           (if (compile-if (rest expr) compenv lexenv valuep tailp))
           (let (if (null (second expr))
                    (compile-progn (cddr expr) compenv lexenv valuep tailp)
                    (compile-let (second expr) (cddr expr) compenv lexenv valuep tailp)))
           (t
            (if-let ((macro (macro compenv (car expr) :if-does-not-exist :continue)))
              (compile-expr (apply macro (cdr expr)) compenv lexenv valuep tailp)
              (compile-funcall (car expr) (rest expr) compenv lexenv valuep tailp)))))))

(defun compile-toplevel (expr compenv)
  (compiler-note "compiling toplevel: ~S" expr)
  (when (consp expr)
    (let ((op (first expr)))
      (case op
        (progn
          (with-noted-sexp-path 'progn
            (iter (for sub-toplevel in (rest expr))
                  (for expr = (compile-toplevel sub-toplevel compenv))
                  (when (and expr (not (expr-effect-free expr)))
                    (collect expr)))))
        (defmacro
            (when (func compenv op :if-does-not-exist :continue)
              (comp-error "~@<In DEFMACRO: ~S already defined as function.~:@>" op))
            (destructuring-bind (name lambda-list &body body) (rest expr)
              (setf (macro compenv name) (compile nil `(lambda ,lambda-list ,@body))))
          nil)
        (defun
            (when (macro compenv op :if-does-not-exist :continue)
              (expr-error "~@<In DEFUN: ~S already defined as macro.~:@>" op))
            (destructuring-bind (name lambda-list &body body) (rest expr)
              (compile-defun name lambda-list body compenv)))
        (t
         (if-let ((macro (macro compenv op :if-does-not-exist :continue)))
           (with-noted-sexp-path `(defmacro ,op)
             (compile-toplevel (apply macro (rest expr)) compenv))
           (compile-expr expr compenv nil nil nil)))))))

(defparameter *test-code* `((defun flash-write-abs (absolute-addr value)
                              (mem-set absolute-addr 0
                                       (logior (ash value 0)
                                               (ash value 16))))
                            (defun flash-write (flash-base offset value)
                              (mem-set (+ flash-base (ash offset 2)) 0
                                       (logior (ash value 0)
                                               (ash value 16))))
                            (defun issue-command-abs (flash-base absolute-addr command)
                              (flash-write flash-base #x555 #xaa)
                              (flash-write flash-base #x2aa #x55)
                              (flash-write-abs absolute-addr command))
                            (defun issue-command (flash-base offset command)
                              (flash-write flash-base #x555 #xaa)
                              (flash-write flash-base #x2aa #x55)
                              (flash-write flash-base offset command))
                            (defun poll-toggle-ready (absolute-addr iterations-left)
                              (if (= 0 iterations-left)
                                  nil
                                  (if (= (logand #x40 (mem-ref-impure absolute-addr 0))
                                         (logand #x40 (mem-ref-impure absolute-addr 0)))
                                      t
                                      (poll-toggle-ready absolute-addr (- iterations-left 1)))))
                            (defun poll-ds7 (absolute-addr iterations-left)
                              (if (= 0 iterations-left)
                                  nil
                                  (if (/= 0 (logand #x80 (mem-ref-impure absolute-addr 0)))
                                      t
                                      (poll-ds7  absolute-addr (- iterations-left 1)))))
                            (defun program-word (flash-base absolute-addr value)
                              (issue-command flash-base #x555 ,#xa0 #+nil (bits :amd-opcode :word-program))
                              (mem-set absolute-addr 0 value)
                              (poll-toggle-ready absolute-addr #x7ffffff))
                            (defun program-region (flash-base dest src word-count)
                              (if (= 0 word-count)
                                  nil
                                  (progn
                                    (program-word flash-base dest (mem-ref src 0))
                                    (program-region flash-base (+ dest 4) (+ src 4) (- word-count 1)))))
                            (defun erase-sector (flash-base absolute-sector-address)
                              (issue-command flash-base #x555 ,#x80 #+nil (bits :amd-opcode :cyc1-erase))
                              (issue-command-abs flash-base absolute-sector-address ,#x50 #+nil (bits :amd-opcode :cyc2-erase-sector))
                              (poll-toggle-ready absolute-sector-address #x7ffffff))
                            (defun erase-block (flash-base absolute-block-address)
                              (issue-command flash-base #x555 ,#x80 #+nil (bits :amd-opcode :cyc1-erase))
                              (issue-command-abs flash-base absolute-block-address ,#x30 #+nil (bits :amd-opcode :cyc2-erase-block))
                              (poll-toggle-ready absolute-block-address #x7ffffff))
                            (defun erase-chip (flash-base)
                              (issue-command flash-base #x555 ,#x80 #+nil (bits :amd-opcode :cyc1-erase))
                              (issue-command flash-base 0 ,#x10 #+nil (bits :amd-opcode :cyc2-erase-chip))
                              (poll-ds7 flash-base #x7ffffff))))

#+(or)
(let ((compenv (make-instance 'compenv)))
  (dolist (component (subseq  *test-code* 0))
    (let ((result (compile-toplevel component compenv)))
      (compiler-note "got: ~S" result)
      (when (typep result 'expr-func)
        (compiler-note "IR1 tree: ~S" (func-expr result))))))
