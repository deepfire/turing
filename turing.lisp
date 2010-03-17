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
;;;; Target-architecture-level
;;;;
(defclass architecture ()
  ((loads :reader arch-loads :initarg :loads)
   (stores :reader arch-stores :initarg :stores)
   (addrtype :reader arch-addrtype :initarg :addrtype)))

(defgeneric emit-register-move (arch to-reg from-reg))
(defgeneric emit-load (arch type to-reg base-reg displacement))
(defgeneric emit-store (arch type from-reg base-reg displacement))
(defgeneric emit-address-load (arch to-reg base-reg displacement)
  (:method (arch to-reg base-reg displacement)
    (emit-load arch (arch-addrtype arch) to-reg base-reg displacement)))
(defgeneric constant-fits-displacement (arch x))
(defgeneric clamp-constant-to-fit-displacement (arch x))
(defgeneric emit-extended-displacement-base-register-set (arch register x))

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
;;;; Context
;;;;
(defstruct (symtab (:constructor %make-symtab (parent)))
  (parent nil :type (or null symtab))
  (syms (make-hash-table :test 'equal) :type hash-table)
  (temporary-counter 0 :type fixnum)
  (childs nil :type list))

(defclass ccontext (language architecture)
  ((types      :reader cctx-types       :initform (make-hash-table :test 'eq))
   (procs      :reader cctx-procs       :initform (make-hash-table :test 'eq))
   (macros     :reader cctx-macros      :initform (make-hash-table :test 'eq))
   (compmacros :reader cctx-compmacros  :initform (make-hash-table :test 'eq))
   (ggsymtab   :accessor cctx-ggsymtab  :initarg :ggsymtab)
   ;; storage
   (staticloc  :accessor cctx-staticloc :initarg :staticloc))
  (:default-initargs 
   :ggsymtab (make-symtab)
   :staticloc 0))

;;;;
;;;; Types
;;;;
(defclass typoid ()
  ((name :reader type-name :initarg :name)
   (supers :reader type-supers :initarg :supers)
   (subs :reader type-subs :initarg :subs)
   (exhausted-p :accessor type-exhausted-p :initarg :exhausted-p))
  (:default-initargs :supers nil :subs nil :exhausted-p nil))

(defmacro define-typoid (name supers slots &rest class-options)
  `(progn
     (defclass ,name ,supers
       ,(iter (for slot in slots)
              (collect `(,slot :reader ,(format-symbol (symbol-package name) "TYPE-~A" slot)
                               :initarg ,(make-keyword slot))))
       ,@class-options)
     (defun ,(format-symbol (symbol-package name) "DEFINE-~A" name)
         (name &optional supers ,@slots &rest initargs &key &allow-other-keys)
       (apply #'define-fundamental-type ',name name supers
              ,@(iter (for slot in slots)
                      (collect (make-keyword slot))
                      (collect slot))
              initargs))))

;;; ATOMICS
(define-typoid atomic-type (typoid) ())

(define-typoid numeric-type (atomic-type)
  (storage-size))
(define-typoid integer-type (numeric-type)
  (lower-bound upper-bound))

;;; COMPOUNDS
(defclass compound-type (typoid) ())

(defclass variable-size-compound (compound-type) ())
(defclass fixed-size-compound (compound-type)
  ((strength :reader type-strength :initarg :arity)))
(defclass dimensional-compound (compound-type)
  ((arity :reader type-arity :initarg :arity)))

(defclass homogenous-compound-type (compound-type)
  ((base :reader type-base :initarg :base)))
(defclass heterogenous-compound-type (compound-type)
  ((bases :reader type-bases :initarg :bases)))

(define-typoid structured-type (fixed-size-compound heterogenous-compound-type)
  (slot-names))
(define-typoid tuple-type (fixed-size-compound heterogenous-compound-type) ())
(define-typoid fixed-array-type (dimensional-compound fixed-size-compound uniform-compound-type) ())
(define-typoid fixed-vector-type (fixed-array-type)
  ()
  (:default-initargs :arity 1))
(define-typoid variable-array-type (dimensional-compound variable-size-compound uniform-compound-type)
  ())
(define-typoid variable-vector-type (variable-array-type)
  ()
  (:default-initargs :arity 1))

(defun make-type (type name supers &rest initargs &key &allow-other-keys)
  (apply #'make-instance type :name name :supers supers initargs))

(defvar *fundamental-types* (make-hash-table :test 'eq)
  "Fundamental types, common to everything sensible.")

(define-subcontainer %find-type :container-slot types :type typoid)
(define-root-container *fundamental-types* %find-fundamental-type :type typoid)

(defgeneric find-type (context name)
  (:method ((empty null) name)
    (%find-fundamental-type name))
  (:method ((o ccontext) name)
    (or (%find-type o name)
        (%find-fundamental-type name))))

(defgeneric coerce-to-type (x)
  (:method ((o typoid)) o)
  (:method ((o cl:symbol)) (find-type nil o)))

(defun define-fundamental-type (type name &optional supers &rest initargs &key &allow-other-keys)
  (let ((type (apply #'make-type type name (mapcar #'coerce-to-type supers) initargs)))
    (setf (%find-fundamental-type name) type)
    (dolist (super (type-supers type))
      (push type (slot-value super 'subs)))))

(define-numeric-type :number)
(define-numeric-type :real                '(:number))

(define-numeric-type :float               '(:real))
(define-numeric-type :single-float        '(:float) 32)
(define-numeric-type :double-float        '(:float) 64)
(define-numeric-type :quad-float          '(:float) 128)

(define-numeric-type :integer             '(:real))
(define-integer-type :unsigned-integer    '(:integer))
(define-integer-type :signed-integer      '(:integer))

(define-integer-type :unsigned-byte       '(:unsigned-integer) 0                                   #xff                               :storage-size 8)
(define-integer-type :signed-byte         '(:signed-integer)   #x-7f                               #x80                               :storage-size 8)
(define-integer-type :unsigned-word       '(:unsigned-integer) 0                                   #xffff                             :storage-size 16)
(define-integer-type :signed-word         '(:signed-integer)   #x-7fff                             #x8000                             :storage-size 16)
(define-integer-type :unsigned-short      '(:unsigned-integer) 0                                   #xffffffff                         :storage-size 32)
(define-integer-type :signed-short        '(:signed-integer)   #x-7fffffff                         #x80000000                         :storage-size 32)
(define-integer-type :unsigned-doubleword '(:unsigned-integer) 0                                   #xffffffffffffffff                 :storage-size 64)
(define-integer-type :signed-doubleword   '(:signed-integer)   #x-7fffffffffffffff                 #x8000000000000000                 :storage-size 64)
(define-integer-type :unsigned-quadword   '(:unsigned-integer) 0                                   #xffffffffffffffffffffffffffffffff :storage-size 128)
(define-integer-type :signed-quadword     '(:signed-integer)   #x-7fffffffffffffffffffffffffffffff #x80000000000000000000000000000000 :storage-size 128)

(define-atomic-type :character)

(define-structured-type :structure)


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

;;; any-real -> any-real
(define-binary-operator + :add add)
(define-binary-operator - :sub subtract)
(define-binary-operator * :mul multiply)
(define-binary-operator / :div divide)
(define-unary-operator  - :neg arithmetic-negation)
;;; any-real -> boolean
(define-binary-operator < :less less-than)
(define-binary-operator <= :lseq less-or-equal)
(define-binary-operator > :grtr greater-than)
(define-binary-operator >= :gteq greater-of-equal)
(define-binary-operator = :eql equality)                                 ; incl pointers
(define-binary-operator != :neql not-equal)                              ; incl pointers
;;; boolean -> boolean
(define-unary-operator  ! :not logic-negation)
;;; integer -> integer
(define-binary-operator mod :mod modulo)
(define-binary-operator min :min minumum)
(define-binary-operator max :max maximum)
(define-binary-operator shl :shl shift-left)
(define-binary-operator shr :shr shift-right)
(define-binary-operator shra :shra shift-right-arithmetic)
(define-binary-operator and :and logical-and)
(define-binary-operator or :or logical-or)
(define-binary-operator xor :xor logical-exclusive-or)
;;; pointer -> any-real
(define-unary-operator  * :ind indirection)
;;; structure -> any
(define-binary-operator >. :elt element)
;;; pointer structure -> any
(define-binary-operator *. :indelt element-indirection)
;;; any -> pointer
(define-unary-operator  addr :addr address-of)
;;; any -> any
(define-binary-operator cast :cast cast)
;;; ???
(define-unary-operator  val :val value)
;;; ???
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

;;; LOOP
(define-hir-inst :for         for                                (varname <- operand1 operand2 operand3)               "for ~(~A~) <- ~(~A~) by ~(~A~) to ~(~A~) do")
(define-hir-inst :endfor      endfor                             ()                                                    "endfor")
;;; IF
(define-hir-inst :strbinif    binary-hir-condition               (operand1 binop operand2)                             "if ~(~A~) ~A ~(~A~) then")
(define-hir-inst :strunif     unary-hir-condition                (unop operand)                                        "if ~A ~(~A~) then")
(define-hir-inst :strvalif    value-hir-condition                (operand)                                             "if ~(~A~) then")
(define-hir-inst :else        else                               ()                                                    "else")
(define-hir-inst :endif       endif                              ()                                                    "endif")
;;; ARRAY
(define-hir-inst :arybinasgn  array-binary-assignment            (varname &rest subscripts <- operand1 binop operand2) "~(~A~)[~{, ~A~}] <- ~(~A~) ~A ~(~A~)")
(define-hir-inst :aryunasgn   array-unary-assignment             (varname &rest subscripts <- binop operand)           "~(~A~)[~{, ~A~}] <- ~A ~(~A~)")
(define-hir-inst :aryvalasgn  array-value-assignment             (varname &rest subscripts <- operand)                 "~(~A~)[~{, ~A~}] <- ~(~A~)")
(define-hir-inst :aryref      array-reference                    (varname &rest subscripts)                            "~(~A~)[~{, ~A~}]")
;;; BOOK: aryref kind unspecified (and leftness, but it's obvious)


;;; LABEL/GOTO
(define-mir-inst :label       label                              (label)                                               ":~(~A~)")
(define-mir-inst :goto        goto                               (label)                                               "goto ~(~A~)")
;;; PROCEDURE
(define-mir-inst :receive     receive                            (varname <- typename)                                 "receive ~(~A~)(~A)")
(define-mir-inst :return      just-return                        ()                                                    "return")
(define-mir-inst :retval      return-value                       (operand)                                             "return ~(~A~)")
(define-mir-inst :call        call                               (procname &rest args)                                 "call ~(~A~)~{ ~A~}")
(define-mir-inst :callasgn    call-assignment                    (varname <- procname &rest args)                      "~(~A~) <- call ~(~A~)~{ ~A~}")
;;; ASSIGNMENT
(define-mir-inst :binasgn     binary-assignment                  (varname <- operand1 binop operand2)                  "~(~A~) <- ~(~A~) ~A ~(~A~)")
(define-mir-inst :unasgn      unary-assignment                   (varname <- unop operand)                             "~(~A~) <- ~A ~(~A~)")
(define-mir-inst :valasgn     value-assignment                   (varname <- operand)                                  "~(~A~) <- ~(~A~)")
(define-mir-inst :condasgn    conditional-assignment             (varname1 <- varname2 operand)                        "~(~A~) <- (~(~A~)) ~(~A~)")
(define-mir-inst :castasgn    cast-assignment                    (varname <- typename operand)                         "~(~A~) <- (~(~A~)) ~(~A~)")
(define-mir-inst :indasgn     indirected-assignment              (varname <- operand)                                  "*~(~A~) <- ~(~A~)")
(define-mir-inst :eltasgn     element-assignment                 (varname eltname <- operand)                          "~(~A~).~(~A~) <- ~(~A~)")
(define-mir-inst :indeltasgn  indirect-element-assignment        (varname eltname <- operand)                          "*~(~A~).~(~A~) <- ~(~A~)")
;;; CONDITIONAL CONTROL TRANSFERS
(define-mir-inst :binif       binary-condition                   (operand1 binop operand2 label)                       "if ~(~A~) ~A ~(~A~) goto ~(~A~)")
(define-mir-inst :unif        unary-condition                    (unop operand label)                                  "if ~A ~(~A~) goto ~(~A~)")
(define-mir-inst :valif       value-condition                    (operand label)                                       "if ~(~A~) goto ~(~A~)")
;;; OS
(define-mir-inst :bintrap     binary-trap                        (operand1 binop operand2 trapno)                      "if ~(~A~) ~A ~(~A~) trap #x~X")
(define-mir-inst :untrap      unary-trap                         (unop operand trapno)                                 "if ~A ~(~A~) trap #x~X")
(define-mir-inst :valtrap     value-trap                         (operand trapno)                                      "if ~(~A~) trap #x~X")
;;; ...
(define-mir-inst :sequence    memory-barrier                     ()                                                    "sequence")
(define-mir-inst :var         variable-reference                 (varname)                                             "~(~A~)")
(define-mir-inst :const       constant-value                     (const)                                               "~(~A~)")
(define-mir-inst :tn          type-name                          (typename)                                            "~(~A~)")

;;; LABEL/GOTO
(define-lir-inst :lir-label   lir-label                          (label)                                               ":~(~A~)")
(define-lir-inst :lir-goto    lir-goto                           (label)                                               "goto ~(~A~)")
(define-lir-inst :gotoaddr    computed-goto                      (regname integer)                                     "goto ~(~A~) + #x~X")
;;; PROCEDURE
(define-lir-inst :callreg     constant-call                      (procname regname)                                    "call ~(~A~) ~(~A~)")
(define-lir-inst :callreg2    register-call                      (regname1 regname2)                                   "call ~(~A~) ~(~A~)")
(define-lir-inst :callregasgn constant-call-assignment           (regname1 <- procname regname2)                       "~(~A~) <- call ~(~A~) ~(~A~)")
(define-lir-inst :callreg3    register-call-assignment           (regname1 <- regname2 regname3)                       "~(~A~) <- call ~(~A~) ~(~A~)")
(define-lir-inst :lirretval   lir-return-value                   (liroperand)                                          "return ~(~A~)")
;;; ASSIGNMENT
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
;;; CONDITIONAL CONTROL TRANSFERS
(define-lir-inst :regbinif    register-binary-condition          (liroperand1 binop liroperand2 label)                 "if ~(~A~) ~A ~(~A~) goto ~(~A~)")
(define-lir-inst :regunif     register-unary-condition           (unop liroperand label)                               "if ~A ~(~A~) goto ~(~A~)")
(define-lir-inst :regvalif    register-value-condition           (liroperand label)                                    "if ~(~A~) goto ~(~A~)")
;;; OS
(define-lir-inst :lir-bintrap lir-register-binary-trap           (liroperand1 binop liroperand2 trapno)                "if ~(~A~) ~A ~(~A~) trap #x~X")
(define-lir-inst :lir-untrap  lir-register-unary-trap            (unop liroperand trapno)                              "if ~A ~(~A~) trap #x~X")
(define-lir-inst :lir-valtrap lir-register-value-trap            (liroperand trapno)                                   "if ~(~A~) trap #x~X")
;;; ...
(define-lir-inst :regno       register-reference                 (regname)                                             "~(~A~)")
(define-lir-inst :lirtn       lir-type-name                      (typename)                                            "~(~A~)")
;; BOOK: LIR typename vs. MIR TNi

(define-lir-memaddr-inst :addr1r register-memory-reference          (regname length)                                   "[~(~A~)](~A)")
(define-lir-memaddr-inst :addr2r register-register-memory-reference (regname1 regname2 length)                         "[~(~A~)+~(~A~)](~A)")
(define-lir-memaddr-inst :addrrc register-constant-memory-reference (regname integer length)                           "[~(~A~)+~(~A~)](~A)")

;;;;
;;;; Language-level
;;;;
(defclass language ()
  ((name :reader lang-name :initarg :name)
   (reserved-constants :reader lang-reserved-constants :initarg :reserved-constants)))

(define-subcontainer const :type t)

(defgeneric srctype-to-type (architecture language srctype))

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
;;;; Symbol table
;;;;
(defstruct symentry
  (name)
  (class nil :type (member :local :local-static))
  (size)
  (bitsize)
  (boundary)
  (bitboundary)
  (srctype)
  (type nil :type (member :s8 :u8 :s16 :u18 :s32 :u32 :s64 :u64 :float :double-float :quad-float))
  (basetype)
  (nelts)
  (machtype)
  (props (make-hash-table :test 'equal)))
;;;;
;;;; BIG FAT WARNING:
;;;; the code below uses SYMENTRYes with :SYMBOL-MACRO srctype,
;;;; which messes up concepts pretty much fatally.
;;;;

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *direct-properties* '(name class size bitsize boundary bitboundary type basetype nelts machtype)))

(define-subcontainer symprop :type t :container-slot props :if-does-not-exist :continue)

(defmacro with-symentry-properties (properties entry &body body)
  (multiple-value-bind (direct indirect) (unzip (rcurry #'member *direct-properties*) properties)
    (once-only (entry)
      `(symbol-macrolet ,(iter (for s in indirect)
                               (collect `(,s `(symprop ,,entry ,',s))))
         (with-slots ,direct ,entry
           ,@body)))))

(define-subcontainer locate-sym :container-slot syms :key-type string :type symentry :if-exists :continue :if-does-not-exist :continue
                     :iterator do-symtab-entries)

(defun make-symtab (&optional parent)
  "Creates a new local symbol table with the given symtol table as its parent,
or NIL if there is none, and returns the new (empty) local symbol table."
  (%make-symtab parent))

(defun dest-symtab (x)
  "Destroys the current local symbol table and returns its parent (or nil
if there is no parent)."
  (when-let ((parent (symtab-parent x)))
    (removef x (symtab-childs parent))
    parent))

(defun insert-sym (symtab x)
  "Inserts an entry for the given symbol into the given symbol table and returns T,
or if the symbol is already present, does not insert a new netry and returns NIL."
  (unless (locate-sym symtab x)
    (setf (locate-sym symtab x) (make-symentry :name x))))

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

;;;
;;; Non-Muchnick extensions
(defun set-sym-srctype (cctx symtab sym srctype &aux
                        (syment (locate-sym symtab sym)))
  (setf (symentry-srctype syment) srctype
        (symentry-type syment) (srctype-to-type cctx cctx srctype)))

(defun extend-symtab (cctx symtab syms)
  (dolist (sym syms)
    (insert-sym symtab sym)
    (set-sym-srctype cctx symtab sym t)))

(defun note-type-declarations (cctx symtab decls)
  (iter (for (type . vars) in decls)
        (when-let ((martians (remove-if (curry #'locate-sym symtab) vars)))
          (expr-error "type declaration for variables out of this scope ~S" martians))
        (dolist (v vars)
          (set-sym-srctype cctx symtab v type))))

(defun handle-scope-extension (cctx symtab added-syms declarations)
  (extend-symtab cctx symtab added-syms)
  (note-type-declarations cctx symtab (filter-type-declarations declarations)))

(defun allocate-tempvar (symtab)
  (let ((name (format-symbol :keyword "T~D" (symtab-temporary-counter symtab))))
    (incf (symtab-temporary-counter symtab))
    (insert-sym symtab name)))

;;;;
;;;; Storage binding
;;;;
(defun round-abs-up (m n)
  "Ensure that M is aligned by N."
  (* (signum m) (ceiling (abs (coerce (/ m n) 'float))) (abs n)))

(defun bind-local-vars (cctx symtab initdisp)
  "Assign each static variable a displacement and, for stack-allocated variables,
assigns a displacement and the frame pointer as the base register."
  (let ((stackloc initdisp)
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
           (with-slots (static-link-offset) cctx
             (case basetype
               (:record
                (dotimes (i nelts)
                  (let ((field-size (symprop entry `(,i size))))
                    (setf static-link-offset (round-abs-up static-link-offset field-size)
                          (symprop entry `(,i disp)) static-link-offset)
                    (incf static-link-offset field-size))))
               (t
                (setf static-link-offset (round-abs-up static-link-offset size)
                      (symprop entry 'disp) static-link-offset)
                (incf static-link-offset size))))))))))

;;;;
;;;; Code, context
;;;;
(defstruct (basic-block (:conc-name bb-) (:constructor %make-basic-block (pred succ)))
  (pred nil :type list)
  (succ nil :type list)
  (insts (make-array 0 :element-type 'inst :adjustable t)))

(defstruct (procedure (:conc-name proc-))
  (name)
  (lambda-list)
  (parameters)
  (nparams)
  (nvalues)
  (documentation)
  (body)
  (leafp)
  ;; Muchnik.
  (static-link-offset)
  (gsymtab (make-symtab))
  (depth)
  (blocks (make-array 0 :element-type 'basic-block :adjustable t) :type vector)
  (lblocks (make-array 0 :element-type 'basic-block :adjustable t) :type vector))

(define-subcontainer proc :type procedure :iterator do-procs :container-slot procs)
(define-subcontainer macro :type function :iterator do-macros :container-slot macros)
(define-subcontainer compmacro :type function :iterator do-compmacros :container-slot compmacros)

;;;;
;;;; Basic block machinery
;;;;
(defun insert-before (block inst i)
  "Insert INST before I'th instruction within BLOCK."
  (with-slots (insts) block
    (setf insts (adjust-array insts (1+ (length insts)) :element-type inst)
          (subseq insts (1+ i)) (subseq insts i (1- (length insts)))
          (aref insts i) inst)))

(defun insert-after (block inst i)
  "Insert INST after I'th instruction within BLOCK.
When I refers to the last instruction within BLOCK, and that instruction
is a control transfer, act as INSERT-BEFORE."
  (with-slots (insts) block
    (setf insts (adjust-array insts (1+ (length insts)) :element-type inst))
    (let ((lastidx (- (length insts) 2)))
      (cond ((and (= i lastidx)
                  (control-transfer-p (aref insts lastidx)))
             (setf (aref insts (1+ lastidx)) (aref insts lastidx)
                   (aref insts lastidx) inst))
            (t
             (setf 
              (subseq insts (+ 2 i)) (subseq insts (1+ i) (1- (length insts)))
              (aref insts (1+ i)) inst))))))

(defun append-to-block (block inst)
  "Insert INST after the last instruction within BLOCK, unless that last
instruction is a control transfer, in which case insert INST before it."
  (insert-after block inst (1- (length (bb-insts block)))))

(defun delete-block (proc block)
  "Remove an empty basic block."
  (with-slots (blocks) proc
    (let ((posn (or (position block blocks)
                    (error "~@<~S doesn't belong to ~S.~:@>" block proc))))
      (setf (subseq blocks posn (1- (length blocks)))
            (subseq blocks (1+ posn))))
    (setf blocks (adjust-array blocks (1- (length blocks)))))
  (removef (bb-pred block) block)
  (removef (bb-succ block) block)
  (dolist (pred (bb-pred block))
    (setf (bb-succ pred) (union (bb-succ block) (remove block (bb-succ pred)))))
  (dolist (succ (bb-succ block))
    (setf (bb-pred succ) (union (bb-pred block) (remove block (bb-pred succ))))))

(defun make-basic-block (proc pred succ)
  "Make a basic block (an inconsitent one, admittedly) and insert it into PROC."
  (with-slots (blocks) proc
    (let ((i (length blocks)))
      (setf blocks (adjust-array blocks (1+ i))
            (aref blocks i) (%make-basic-block pred succ)))))

;;; XXXBOOK: doesn't insert the block into the array
(defun insert-block (proc pred-block succ-block)
  "Split an edge by inserting a block with NINSTS instructions between the two given blocks."
  (with-slots (blocks) proc
    (let ((block (make-basic-block proc (list pred-block) (list succ-block))))
      (setf (bb-succ pred-block) (cons block (remove succ-block (bb-succ pred-block)))
            (bb-pred succ-block) (cons block (remove pred-block (bb-pred succ-block)))))))

(defun delete-inst (proc block i)
  "Delete an instruction at I'th position from a basic block.
Will remove empty basic blocks."
  (with-slots (insts) block
    (if (zerop (length insts))
        (delete-block proc block)
        (setf (subseq insts i (1- (length insts))) (subseq insts (1+ i))))))

(defun alloc-reg (proc symtab var)
  "Allocates a register, register pair, or register quadruple of the
appropriate type to hold the value of its VARiable argument and sets the 'reg'
field in the variable's symbol-table entry, unless there already is a register
allocated, and (in either case) returns the name of the first register.")

(defun alloc-reg-anon (proc floatp integer)
  "Allocates a register, register pair, or register quadruple of the
appropriate type (according to the value of the second argument, which
may be 1, 2 or 4) and returns the name of the first register.  It does not
associate the register with a symbol, unlike ALLOC-REG.")

(defun free-reg (proc register)
  "Returns its argument register to the pool of available registers.")

;;;;
;;;; Variable load/store
;;;;
(defun gen-ldst (cctx proc symtab type reg symdisp storep &aux
                 (globalp (eq symtab (proc-gsymtab proc))))
  "TODO: emit LIR, instead of target assembly."
  (let ((base-reg (if globalp "gp" "fp")))
    (unless globalp
      ;; As symdisp is relative to the procedure-global fp, we need to obtain it.
      (let ((scratch-reg (if storep
                             (alloc-reg-anon cctx nil 4) ; can't reuse source reg as scratch
                             reg)))
        (dotimes (i (proc-depth cctx))
          (emit-address-load cctx scratch-reg base-reg (proc-static-link-offset proc))
          (emit-register-move cctx base-reg scratch-reg)
          ;; XXXBOOK: wtf was supposed to be this line?  Page 63.
          ;; (setf base-reg scratch-reg)
          )
        (when storep
          (free-reg cctx scratch-reg))))
    (cond ((constant-fits-displacement cctx symdisp)
           (if storep
               (emit-store cctx type reg base-reg symdisp)
               (emit-load  cctx type reg base-reg symdisp)))
          (t
           (emit-extended-displacement-base-register-set cctx base-reg symdisp)
           (let ((clamped-displacement (clamp-constant-to-fit-displacement cctx symdisp)))
             (if storep
                 (emit-store cctx type reg base-reg clamped-displacement)
                 (emit-load  cctx type reg base-reg clamped-displacement)))))))

(defun find-symtab (proc symtab variable)
  (setf (proc-depth proc) 0)
  ;; XXXBOOK: global symtab trumps local syms?
  (or (find-if (rcurry #'locate-sym variable) 
               (list symtab (proc-gsymtab proc)))
      (lret ((parent-symtab (enclosing-symtab symtab variable)))
        (setf (proc-depth proc) (depth-of-symtab parent-symtab)))))

(defun sym-to-reg (cctx proc symtab var)
  "Generates a load from storage location corresponding to a given variable
to a register, register pair, or register quadruple of the appopriate
type, and returns the name of the first register.
BOOKTODO: register tracking."
  (let ((parent-symtab (find-symtab proc symtab var)))
    (with-symentry-properties (inregp register type disp) (locate-sym parent-symtab var)
      (if inregp
          register
          (lret ((symreg (alloc-reg cctx symtab var)))
            (gen-ldst cctx proc symtab type register disp nil))))))

(defun sym-to-reg-force (cctx proc symtab var register)
  "Generates a load from storage location corresponding to a given symbol
to the named register, register pair, or register quadruple of the appopriate
type.  This routine can be used, for example, to force procedure arguments to
the appropriate registers.
BOOKTODO: register tracking."
  (let ((parent-symtab (find-symtab proc symtab var)))
    (with-symentry-properties (type disp) (locate-sym parent-symtab var)
      (gen-ldst cctx proc symtab type register disp nil))))

;;; XXXBOOK: declares reg-to-sym as Symtab x Register -> Var
(defun reg-to-sym (cctx proc symtab register var)
  "Generates a store of REGISTER name to the variable's storage location.
BOOKTODO: register tracking."
  (let ((parent-symtab (find-symtab proc symtab var)))
    (with-symentry-properties (type disp) (locate-sym parent-symtab var)
      (gen-ldst proc cctx symtab type register disp t))))

;;;;
;;;; Frontend
;;;;
(defvar sexp-path)
(defvar toplevelp)

(defmacro with-noted-sexp-path (designator &body body)
  `(let ((sexp-path (cons ,designator sexp-path)))
     ,@body))

(defun expr-error (format-control &rest format-arguments)
  (apply #'comp-error (format nil "~~@<In ~~S: ~A.~~:@>" format-control) sexp-path format-arguments))

(defun compiler-note (format-control &rest format-arguments)
  (apply #'format t (format nil "~~@<; ~~@;note: ~A.~~:@>~%" format-control) format-arguments))

(defun note-redefinition (what in)
  (compiler-note "redefining ~A in ~A" what in))

;;;;
;;;; Lisp frontend
;;;;
(defclass lisp-language (language)
  ()
  (:default-initargs 
   :name :lisp
   :reserved-constants (alist-hash-table `((t . t) (nil . t) (pi . ,pi)))))

(defclass lisp-context (lisp-language context) ())

(defmethod srctype-to-type (architecture (l lisp-language) srctype)
  (arch-addrtype architecture))

;;;;
;;;;  -> MIR
;;;;
;;;; Function hierarchy goes unconventionally -- top-to-down.
;;;;
(defun the-mir-operand (maybe-mir-value)
  (if (typep maybe-mir-value '(or variable-reference constant-value))
      maybe-mir-value
      (comp-error "internal compiler error while compiling ~S: ~
                   expected either a constant or a variable reference, ~
                   got a value of type ~A"
                  sexp-path (type-of maybe-mir-value))))

(defun filter-type-declarations (decls)
  (mapcar #'rest (remove-if-not (feq 'type) decls :key #'car)))

;;; a dispatcher/forwarder -- doesn't operate on anything
(defun compile-toplevel (cctx expr &aux (toplevelp t))
  (compiler-note "compiling toplevel: ~S" expr)
  (if (atom expr)
      (when-let ((sym (locate-sym (cctx-ggsymtab cctx) expr)))
        (when (eq :symbol-macro (symentry-srctype sym))
          (compile-toplevel cctx (funcall (symprop sym 'expander)))))
      (let ((op (first expr)))
        (with-noted-sexp-path op
          (case op
            (progn                                                                                                       ; done
              (mapcar (curry #'compile-toplevel cctx) (rest expr)))
            (define-symbol-macro                                                                                         ; done
             (destructuring-bind (name expansion) expr
               (compile-define-symbol-macro cctx name expansion)))
            (defmacro                                                                                                    ; done
                (when (proc cctx (second expr) :if-does-not-exist :continue)
                  (comp-error "~@<In DEFMACRO: ~S already defined as function.~:@>" op))
                (destructuring-bind (name lambda-list &body body) (rest expr)
                  (setf (macro cctx name) 
                        (compile nil `(lambda ,lambda-list ,@body)))))
            (defun                                                                                                       ; done (?)
                (when (macro cctx (second expr) :if-does-not-exist :continue)
                  (expr-error "~@<In DEFUN: ~S already defined as macro.~:@>" op))
                (destructuring-bind (name lambda-list &body body) (rest expr)
                  (let ((toplevelp nil))
                    (compile-defun cctx name lambda-list body))))
            (t                                                                                                           ; COMPILE-EXPR not NIL-safe wrt block and symtab
             (if-let ((macro (macro cctx op :if-does-not-exist :continue)))
               (with-noted-sexp-path `(defmacro ,op)
                 (compile-toplevel cctx (apply macro (rest expr))))
               (compile-expr cctx nil nil (cctx-ggsymtab cctx) nil nil expr))))))))

;;; another dispatcher/forwarder -- doesn't emit anything by itself
;;; conventions for all dispatched-to handlers:
;;; - valuep, when non-NIL indicates that the expression is compiled not only for
;;;   effect, and that some kind of value passing is due.  In which case it is either T,
;;;   which indicates that the means of value passing are to be provided by the handler --
;;;   either as a CONSTANT-VALUE or as VARIABLE-REFERENCE MIR instruction; or it must be a
;;;   VARIABLE-REFERENCE itself, indicating that an outer context facilitates value passing.
;;; - the first return value is a variable reference (maybe a temporary), a constant,
;;;   or nil, when VALUEP was provided as NIL.
;;; - the second return value is the current basic block, after compiling the expression.
(defun compile-expr (cctx proc block symtab valuep tailp expr)
  (when *comp-verbose*
    (compiler-note "compiling ~S" expr))
  (cond ((constant-p expr) (compile-constant           cctx proc block symtab valuep tailp expr))                        ; done
        ((symbolp expr)    (compile-symbol-ref         cctx proc block symtab valuep tailp expr))                        ; done
        ((atom expr)       (expr-error "atom ~S has unsupported type ~S" expr (type-of expr)))
        (t
         (with-noted-sexp-path (car expr)
           (case (car expr)
             (progn           (compile-progn           cctx proc block symtab valuep tailp (rest expr)))                 ; done
             (if              (compile-if              cctx proc block symtab valuep tailp (rest expr)))                 ; MIR matching...
             (let             (compile-let             cctx proc block symtab valuep tailp (second expr) (cddr expr)))   ; done
             (setq            (compile-setq            cctx proc block symtab valuep tailp (rest expr)))                 ; done
             (symbol-macrolet (compile-symbol-macrolet cctx proc block symtab valuep tailp (second expr) (cddr expr)))   ; done
             #+nil (function)
             #+nil (funcall) #+nil (apply)
             #+nil (tagbody) #+nil (go)
             #+nil (values)
             #+nil (multiple-value-bind)
             #+nil (block)
             #+nil (catch)   #+nil (throw)
             #+nil (unwind-protect)
             #+nil (cons)
             (t
              (destructuring-bind (name &rest body) expr
                (if-let ((macro (macro cctx name :if-does-not-exist :continue)))
                  (compile-expr                        cctx proc block symtab valuep tailp (apply macro body))          ; self
                  (compile-funcall                     cctx proc block symtab valuep tailp name body)))))))))           ; operators...

;;; Doesn't emit anything.
(defun compile-define-symbol-macro (cctx name expansion)
  (let ((preexisting-sym (locate-sym (cctx-ggsymtab cctx) name)))
    (when preexisting-sym
      (if (eq :symbol-macro (symentry-srctype preexisting-sym))
          (note-redefinition name 'define-symbol-macro)
          (comp-error "In DEFINE-SYMBOL-MACRO: ~S is alredy defined as a ~A"
                      name (symentry-srctype preexisting-sym))))
    (let ((sym (or preexisting-sym (insert-sym (cctx-ggsymtab cctx) name))))
      (setf (symprop sym 'expander)
            (compile nil `(lambda () ,expansion))))))

(defun compile-defun (cctx name lambda-list body)
  (labels ((validate-lambda-list (list)
             (lret ((params (lambda-list-binds list)))
               (when-let ((dups (set-difference params (remove-duplicates params))))
                 (expr-error "duplicate entries in lambda list: ~S" dups))
               (when-let ((consts (remove-if-not #'const params)))
                 (expr-error "reserved constant names in lambda list: ~S" consts)))))
    (with-noted-sexp-path `(defun ,name ,lambda-list)
      (multiple-value-bind (docstring declarations body) (destructure-def-body body)
        (lret* ((parameters (validate-lambda-list lambda-list))
                (proc (make-procedure :name name :lambda-list lambda-list :parameters parameters :nparams (length parameters) :body body
                                      :documentation docstring :leafp t)))
          (when (proc cctx name)
            (note-redefinition name 'defun))
          (setf (proc cctx name) proc)
          (with-slots (gsymtab) proc
            (let ((block (make-basic-block proc nil nil))
                  (return-tn (make-variable-reference (symentry-name (allocate-tempvar gsymtab)))))
              (append-to-block block (make-label name))
              (handle-scope-extension cctx gsymtab parameters declarations)
              (dolist (p parameters)
                (append-to-block block (make-receive p (symentry-type (locate-sym gsymtab p)))))
              (append-to-block (nth-value 1 (compile-progn cctx proc block gsymtab return-tn t body))
                               (make-return-value return-tn)))))))))

;;; leaf, doesn't emit anything, return value is expected to be grafted into another MIR inst 
(defun compile-constant (cctx proc block symtab valuep tailp expr)
  (declare (ignore cctx proc symtab tailp))
  (values
   (cond
     ((not valuep)                        nil)
     ((eq valuep t)                       (make-constant-value expr))
     ((typep valuep 'variable-reference)  (progn
                                            (append-to-block block (make-value-assignment valuep (make-constant-value expr)))
                                            nil))
     (t   
      (comp-error "in CONSTANT ~A: bad value passing specifier ~S from outer context" expr valuep)))
   block))

;;; potential leaf emitter, doesn't emit anything by itself
(defun compile-symbol-ref (cctx proc block symtab valuep tailp sym)
  (if-let ((syment (or (locate-sym symtab sym)
                       (locate-sym (cctx-ggsymtab cctx) sym))))
    (if (eq :symbol-macro (symentry-srctype syment))
        (compile-expr cctx proc block symtab valuep tailp (funcall (symprop syment 'expander)))
        (values
         (cond
           ((not valuep)                        nil)
           ((eq valuep t)                       (make-variable-reference sym))
           ((typep valuep 'variable-reference)  (progn
                                                  (append-to-block block (make-value-assignment valuep (make-variable-reference sym)))
                                                  nil))
           (t   
            (comp-error "in ~A: bad value passing specifier ~S from outer context" sym valuep)))
         block))
    (with-noted-sexp-path sym
      (comp-error "undefined variable ~S" sym))))

(defun compile-setq (cctx proc block symtab valuep tailp assignment-plist)
  (values (iter (for (sym expr . rest) on assignment-plist by #'cddr)
                (if-let ((syment (or (locate-sym symtab sym)
                                     (locate-sym (cctx-ggsymtab cctx) sym))))
                  (if (eq :symbol-macro (symentry-srctype syment))
                      (comp-error "symbol macro assignments not supported")
                      (let ((target-tn (make-variable-reference sym)))
                        (multiple-value-bind (result-tn maybe-new-block) (compile-expr cctx proc block symtab target-tn (and rest tailp) expr)
                          (setf block maybe-new-block)
                          (when (and valuep (null rest))
                            (cond ((eq valuep t)                      result-tn)
                                  ((typep valuep 'variable-reference) (append-to-block block (make-value-assignment valuep result-tn)))
                                  (t
                                   (comp-error "in SETQ ~A: bad value passing specifier ~S from outer context" assignment-plist valuep)))))))
                  (with-noted-sexp-path sym
                    (comp-error "undefined variable ~S" sym))))
          block))

(defun compile-symbol-macrolet (cctx proc block symtab valuep tailp bindings body)
  (let* ((syms (mapcar #'ensure-car bindings))
         (expansions (mapcar (compose #'second #'ensure-list) bindings))
         (new-symtab (make-symtab symtab)))
    (iter (for sym in syms)
          (for expansion in expansions)
          (let ((syment (insert-sym new-symtab sym)))
            (setf (symentry-srctype syment) :symbol-macro
                  (symprop syment 'expander) (compile nil `(lambda () ,expansion)))))
    (compile-progn cctx proc block new-symtab valuep tailp body)))

(defun compile-let (cctx proc block symtab valuep tailp bindings body)
  (let* ((syms (mapcar #'ensure-car bindings))
         (arg-exprs (mapcar (compose #'second #'ensure-list) bindings))
         (arg-tns (mapcar #'make-variable-reference syms))
         (new-symtab (make-symtab symtab)))
    (multiple-value-bind (declarations body) (destructure-binding-form-body body)
      (handle-scope-extension cctx new-symtab syms declarations)
      (iter (for arg-expr in arg-exprs)
            (for arg-tn in arg-tns)
            (for (values nil maybe-new-block) = (compile-expr cctx proc block symtab arg-tn nil arg-expr))
            (setf block maybe-new-block))
      (compile-progn cctx proc block new-symtab valuep tailp body))))

(defun compile-progn (cctx proc block symtab valuep tailp exprs)
  (if exprs
      (iter (for expr in (butlast exprs))
            (setf block (nth-value 1 (compile-expr cctx proc block symtab nil nil expr)))
            (finally
             (return (compile-expr cctx proc block symtab valuep tailp (lastcar exprs)))))
      (values (compile-constant cctx proc block symtab valuep tailp nil)
              block)))

(defun simplify-logical-expression (x &aux (pass-list '(fold-constants remove-duplicates unnest-similars detrivialize recurse)))
  (cond ((atom x) x)
        ((= 2 (length x)) (simplify-logical-expression (second x)))
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
                                                            (return-from simplify-logical-expression t)
                                                            (remove nil x-body)))
                                                    (and (if (member nil (rest x))
                                                             (return-from simplify-logical-expression nil)
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
                                                  (mapcar #'simplify-logical-expression x-body))))))
                                  (if xform
                                      (multiple-value-bind (processed-x-body trivial-p) (funcall xform)
                                        (cond (trivial-p
                                               (return-from simplify-logical-expression
                                                 (simplify-logical-expression processed-x-body)))
                                              ((equalp processed-x-body x-body)
                                               (setf state (cdr state)))
                                              (t
                                               (setf state pass-list
                                                     x-body processed-x-body)))
                                        (go loop))
                                      (return-from machine-collector x-body))))))))))

(defun compile-funcall (cctx proc block symtab valuep tailp name arg-exprs)
  (declare (ignore tailp))
  (let ((func (or (proc cctx name :if-does-not-exist :continue)
                  (primop name :if-does-not-exist :continue))))
    (unless func
      (expr-error "reference to undefined function ~S" name))
    (unless (= (length arg-exprs) (proc-nparams func))
      (expr-error "wrong argument count in call of ~S: got ~D, expected ~D"
                  name (length arg-exprs) (proc-nparams func)))
    (with-noted-sexp-path `(funcall ,name)
      (let ((arg-mir-insts (iter (for arg-expr in arg-exprs)
                                 (for (values result maybe-new-block) = (compile-expr cctx proc block symtab t nil arg-expr))
                                 (setf block maybe-new-block)
                                 (collect result))))
        (values
         (cond
           ((not valuep)                        (progn
                                                  (append-to-block block (make-call proc arg-mir-insts)) 
                                                  nil))
           ((eq valuep t)                       (lret ((tn (make-variable-reference (symentry-name (allocate-tempvar symtab)))))
                                                  (append-to-block block (make-call-assignment tn name arg-mir-insts))))
           ((typep valuep 'variable-reference)  (prog1 valuep
                                                  (append-to-block block (make-call-assignment valuep name arg-mir-insts))))
           (t   
            (comp-error "in COMPILE-FUNCALL (~A ...): bad value passing specifier ~S from outer context" name valuep)))
         block)))))

(defun compile-if (cctx proc block symtab valuep tailp clauses)
  (let ((n-args (length clauses)))
    (when (or (< n-args 2)
              (> n-args 3))
      (expr-error "invalid number of elements in IF operator: between 2 and 3 expected")))
  (destructuring-bind (condition then-clause &optional else-clause) clauses
    (let* ((condition-code (compile-expr cctx proc block symtab t nil condition))
           (then-code (compile-expr cctx proc block symtab valuep nil then-clause))
           (else-code (if else-clause
                          (compile-expr cctx proc block symtab valuep nil else-clause)
                          (compile-constant cctx proc block symtab valuep tailp nil))))
      (with-noted-sexp-path 'if
        (cond ((null condition) else-code)
              ((constant-p condition) then-code)
              ((equalp then-clause else-clause) (compile-progn cctx proc block symtab valuep tailp `(,condition ,then-clause)))
              ((and (= 2 (length condition)) (eq (first condition) 'not))
               (compile-if cctx proc block symtab valuep tailp `(if ,(second condition) ,then-clause ,else-clause)))
              (t
               #+nil
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
                           (emit-label end-label))))))))))

;; (defun comp-typep (x type)
;;   (if (consp type)
;;       (ecase (first type)
;;         (and (not (null (every (curry #'comp-typep x) (rest type)))))
;;         (or (not (null (some (curry #'comp-typep x) (rest type))))))
;;       (ecase type
;;         (boolean (member x '(t nil)))
;;         (integer (typep x '(unsigned-byte 32)))
;;         (nil nil)
;;         ((t) t))))

;; (defun comp-type-of (x)
;;   (cond ((member x '(t nil)) 'boolean)
;;         ((typep x '(unsigned-byte 32)) 'integer)
;;         (t t)))

;; (defprimitive +              2 1 integer t   t   t   nil
;;   (:folder (arg-exprs tailp)
;;     (compile-constant (apply #'+ (mapcar #'expr-form arg-exprs)) t tailp)))
;; (defprimitive -              2 1 integer t   t   t   nil)
;; (defprimitive logior         2 1 integer t   t   t   nil)
;; (defprimitive logand         2 1 integer t   t   t   nil)
;; (defprimitive logxor         2 1 integer t   t   t   nil)
;; (defprimitive ash            2 1 integer t   t   t   nil
;;   (:folder (arg-exprs tailp)
;;     (compile-constant (apply #'ash (mapcar #'expr-form arg-exprs)) t tailp))
;;   (:papplicable-p (arg-exprs &aux (shift (expr-form (second arg-exprs))))
;;     (and (integerp shift) (zerop shift)))
;;   (:papplicator (arg-exprs)
;;     (first arg-exprs)))
;; (defprimitive lognot         1 1 integer t   t   t   nil)
;; (defprimitive =              2 1 boolean t   t   t   nil)
;; (defprimitive /=             2 1 boolean t   t   t   nil)
;; (defprimitive >=             2 1 boolean t   t   t   nil)
;; (defprimitive <=             2 1 boolean t   t   t   nil)
;; (defprimitive >              2 1 boolean t   t   t   nil)
;; (defprimitive <              2 1 boolean t   t   t   nil)
;; (defprimitive mem-ref        2 1 integer t   t   nil nil)
;; (defprimitive mem-set        3 0 nil     nil nil nil nil)
;; (defprimitive mem-ref-impure 2 1 integer t   nil nil nil)
;; (defprimitive funarg-ref     2 1 t       t   t   t   nil
;;   (:instantiator (primop valuep args arg-exprs &aux (type (second args)))
;;     (declare (ignore arg-exprs))
;;     (make-instance 'expr :effect-free t :pure t :value-used valuep :env nil
;;                    :type type :branching nil :form `(,(func-name primop) ,@args)
;;                    :code (apply #'emit-primitive 'funarg-ref 0 1 args))))

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

;; (defun maybe-wrap-with-return (wrap-p expr)
;;   (if wrap-p
;;       (make-instance 'expr :effect-free (expr-effect-free expr) :pure (expr-pure expr) :value-used t :env nil
;;                      :type (expr-type expr) :branching (degrade-tail-branching (expr-branching expr)) :form `(return ,(expr-code expr))
;;                      :code
;;                      (append (list expr)
;;                              (emit-return)))
;;       expr))

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
