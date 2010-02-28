(in-package :common-lisp-user)

(defpackage #:turing
  (:use :common-lisp :alexandria :iterate :pergamum :environment :isa)
  (:shadowing-import-from :isa #:disassemble)
  (:shadow #:frame)
  (:export
   ))

(defpackage #:unturing
  (:use :common-lisp :alexandria :iterate :pergamum :isa)
  (:shadowing-import-from :isa #:disassemble)
  (:export
   #:ivec
   #:bb
   #:bb-ins
   #:bb-outs
   #:bons
   #:bar
   #:bdr
   #:bons-path
   #:all-bons-paths
   #:shortest-bons-path
   #:bons-connected-p
   #:mapt-bb-paths
   #:do-path-internal-nodes
   #:bb-graph-within-distance-set
   #:linked-bb
   #:linked-addr
   #:linked-reg
   #:linked-to
   #:victim-bb
   #:aggressor-bb
   #:insn-vector-to-basic-blocks
   #:bbnet-tree
   #:default-node-parameter-extractor
   #:pprint-node-graph-linear))
