;;; -*- Mode: Lisp; indent-tabs-mode: nil -*-

(defsystem :turing
  :depends-on (:alexandria :iterate :pergamum :semi-precious :assem)
  :components
  ((:file "package")
   ;;;
   (:file "turing" :depends-on ("package"))
   (:file "unturing" :depends-on ("package"))
   ;;;
   (:file "unturing-mips" :depends-on ("unturing"))
   ))
