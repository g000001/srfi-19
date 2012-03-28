;;;; srfi-19.asd -*- Mode: Lisp;-*-

(cl:in-package :asdf)

(defsystem :srfi-19
  :serial t
  :depends-on (:fiveam
               :srfi-6
               :srfi-8
               :srfi-9
               :srfi-23
               :mbe)
  :components ((:file "package")
               (:file "util")
               (:file "srfi-19")
               (:file "test")))

(defmethod perform ((o test-op) (c (eql (find-system :srfi-19))))
  (load-system :srfi-19)
  (or (flet ((_ (pkg sym)
               (intern (symbol-name sym) (find-package pkg))))
         (let ((result (funcall (_ :fiveam :run) (_ :srfi-19.internal :srfi-19))))
           (funcall (_ :fiveam :explain!) result)
           (funcall (_ :fiveam :results-status) result)))
      (error "test-op failed") ))
