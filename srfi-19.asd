;;;; srfi-19.asd -*- Mode: Lisp;-*-

(cl:in-package :asdf)

(defsystem :srfi-19
  :version "20200121"
  :description "SRFI 19 for CL:Time Data Types and Procedures"
  :long-description "SRFI 19 for CL:Time Data Types and Procedures
https://srfi.schemers.org/srfi-19"
  :author "Neodesic Corporation"
  :maintainer "CHIBA Masaomi"
  :license "MIT"
  :serial t
  :depends-on (#+lispworks :local-time
               :fiveam
               :srfi-6
               :srfi-8
               :srfi-9
               :srfi-23
               :mbe)
  :components ((:file "package")
               (:file "util")
               (:file "srfi-19")
               (:file "test")))

(defmethod perform :after ((o load-op)
                           (c (eql (find-system :srfi-19))))
  (let ((name "https://github.com/g000001/srfi-19") (nickname :srfi-19))
    (if (and (find-package nickname)
             (not (eq (find-package nickname) (find-package name))))
        (warn "~A: A package with name ~A already exists." name nickname)
        (rename-package name name `(,nickname)))))

(defmethod perform ((o test-op) (c (eql (find-system :srfi-19))))
  (or (flet ((_ (pkg sym)
               (intern (symbol-name sym) (find-package pkg))))
        (let ((result (funcall (_ :fiveam :run)
                               (_ "https://github.com/g000001/srfi-19#internals" :srfi-19))))
          (funcall (_ :fiveam :explain!) result)
          (funcall (_ :fiveam :results-status) result)))
      (error "test-op failed") ))
