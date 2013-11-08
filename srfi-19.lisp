;;;; srfi-19.lisp

(cl:in-package :srfi-19.internal)

;; SRFI-19: Time Data Types and Procedures.
;;
;; Copyright (C) I/NET, Inc. (2000, 2002, 2003). All Rights Reserved.
;;
;; Permission is hereby granted, free of charge, to any person obtaining
;; a copy of this software and associated documentation files (the
;; "Software"), to deal in the Software without restriction, including
;; without limitation the rights to use, copy, modify, merge, publish,
;; distribute, sublicense, and/or sell copies of the Software, and to
;; permit persons to whom the Software is furnished to do so, subject to
;; the following conditions:
;;
;; The above copyright notice and this permission notice shall be
;; included in all copies or substantial portions of the Software.
;;
;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;; NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
;; LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
;; OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
;; WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

;; -- Bug fixes.
;;
;; MAKE-TIME had parameters seconds and nanoseconds reversed; change all
;;           references in file to match.  Will F: 2002-10-15
;;
;; DATE-YEAR-DAY returned the wrong day; tm.year-day fixed to do the right
;;               thing. Will F: 2002-10-15
;;               It also called an undefined error procedure.
;;
;; DISPLAYING procedure removed. Will F: 2002-10-15.
;;
;; TM.NANO constant corrected. 2002-11-04.
;;
;; The following fixes by Will Fitzgerald, February, 2003.
;;  -- Thanks to Steven Ma and others.
;;
;; (CURRENT-TIME 'TIME-THREAD) added.
;;
;; TIME-RESOLUTION for TIME-PROCESS added.
;;
;; TIME comparison procedures (time=?, etc. fixed.
;;
;; Corrected errors in converting between TAI and UTC time.
;;
;; TAI and UTC date converters no longer look at leap seconds,
;; which was an error.
;;
;; corrections to calls to tm.time-error
;;
;; timezone offset not used in date->time-utc and date->julian-day
;;
;; typos in tm.integer-reader-exact, tm.string->date,
;; time-monotonic->time-utc!, tm.char->int fixed
;;
;; corrected "~k", "~f" formatting for date->string (includes fix for
;; "~4"
;;
;; 'split-real' fixed.
;;
;; fixed julian-day->time-utc and variants.
;;
;; changes 2003-02-26, based on comments by Martin Gasbichler.
;;
;; moronic, overly complicated COPY-TIME procedure changed
;; to simple version suggested by Martin Gasbichler.
;;
;; To provide more portability, changed #\Space to #\space
;; and #\tab to #\Tab to (integer->char 9)
;;
;; changed arity-3 calls to / and - to arity 2 calls (again,
;; for more general portability).
;;
;; split-real fixed again -- by removing it, and using
;; 'fractional part'. Will Fitzgerald 5/16/2003.
;; --------------------------------------------------------------

#|(define-syntax receive
  (syntax-rules ()
    ((receive formals expression body ***)
     (call-with-values (lambda () expression)
                       (lambda formals body ***)))))|#

;;; -- we want receive later on for a couple of small things
;;

;; :OPTIONAL is nice, too

(define-syntax .optional
  (syntax-rules ()
    ((_ val default-value)
     (if (null? val) default-value (car val)))))

(defvar time-tai 'time-tai)
(defvar time-utc 'time-utc)
(defvar time-monotonic 'time-monotonic)
(defvar time-thread 'time-thread)
(defvar time-process 'time-process)
(defvar time-duration 'time-duration)

;; example of extension (MZScheme specific)
(defvar time-gc 'time-gc)

;;-- LOCALE dependent constants

(defvar tm.locale-number-separator ".")

(defvar tm.locale-abbr-weekday-vector (vector "Sun" "Mon" "Tue" "Wed"
                                              "Thu" "Fri" "Sat"))
(defvar tm.locale-long-weekday-vector (vector "Sunday" "Monday"
                                              "Tuesday" "Wednesday"
                                              "Thursday" "Friday"
                                              "Saturday"))
;; note empty string in 0th place.
(defvar tm.locale-abbr-month-vector   (vector "" "Jan" "Feb" "Mar"
                                              "Apr" "May" "Jun" "Jul"
                                              "Aug" "Sep" "Oct" "Nov"
                                              "Dec"))
(defvar tm.locale-long-month-vector   (vector "" "January" "February"
                                              "March" "April" "May"
                                              "June" "July" "August"
                                              "September" "October"
                                              "November" "December"))

(defvar tm.locale-pm "PM")
(defvar tm.locale-am "AM")

;; See date->string
(defvar tm.locale-date-time-format "~a ~b ~d ~H:~M:~S~z ~Y")
(defvar tm.locale-short-date-format "~m/~d/~y")
(defvar tm.locale-time-format "~H:~M:~S")
(defvar tm.iso-8601-date-time-format "~Y-~m-~dT~H:~M:~S~z")
;;-- Miscellaneous Constants.
;;-- only the tm.tai-epoch-in-jd might need changing if
;;   a different epoch is used.

(defvar tm.nano (expt 10 9))
(defvar tm.sid  86400)    ; seconds in a day
(defvar tm.sihd 43200)    ; seconds in a half day
(defvar tm.tai-epoch-in-jd 4881175/2) ; julian day number for 'the epoch'


;;; A Very simple Error system for the time procedures
;;;
(defvar tm.time-error-types
  '(invalid-clock-type
    unsupported-clock-type
    incompatible-time-types
    not-duration
    dates-are-immutable
    bad-date-format-string
    bad-date-template-string
    invalid-month-specification
    ))

(define-function (tm.time-error caller type value)
  (if (member type tm.time-error-types)
      (if value
	  (error caller "TIME-ERROR type ~S: ~S" type value)
	  (error caller "TIME-ERROR type ~S" type))
      (error caller "TIME-ERROR unsupported error type ~S" type)))


;; A table of leap seconds
;; See ftp://maia.usno.navy.mil/ser7/tai-utc.dat
;; and update as necessary.
;; this procedures reads the file in the abover
;; format and creates the leap second table
;; it also calls the almost standard, but not R5 procedures read-line
;; & open-input-string
;; ie (set! tm.leap-second-table (tm.read-tai-utc-date "tai-utc.dat"))

(define-function (tm.read-tai-utc-data filename)
  (with-local-define-function
    (define (convert-jd jd)
      (* (- (rationalize jd) tm.tai-epoch-in-jd) tm.sid) )
    (define (convert-sec sec)
      (rationalize sec) )
    :in
    (with-open-file (port filename)
      (let ( (table '()) )
        (iterate loop ((line (read-line port)))
          (if (not (eq? line +eof+))
              (begin
                (let* ( (data (read (open-input-string (string-append "(" line ")"))))
                       (year (car data))
                        (jd   (cadddr (cdr data)))
                        (secs (cadddr (cdddr data))) )
                  (if (>= year 1972)
                      (set! table (cons (cons (convert-jd jd) (convert-sec secs)) table)) )
                  (loop (read-line port)) ))))
        table ))))

;; each entry is ( utc seconds since epoch . # seconds to add for tai )
;; note they go higher to lower, and end in 1972.
(defvar tm.leap-second-table
  '((1341100800 . 35)
    (1230768000 . 34)
    (1136073600 . 33)
    (915148800 . 32)
    (867715200 . 31)
    (820454400 . 30)
    (773020800 . 29)
    (741484800 . 28)
    (709948800 . 27)
    (662688000 . 26)
    (631152000 . 25)
    (567993600 . 24)
    (489024000 . 23)
    (425865600 . 22)
    (394329600 . 21)
    (362793600 . 20)
    (315532800 . 19)
    (283996800 . 18)
    (252460800 . 17)
    (220924800 . 16)
    (189302400 . 15)
    (157766400 . 14)
    (126230400 . 13)
    (94694400 . 12)
    (78796800 . 11)
    (63072000 . 10) ))

(define-function (read-leap-second-table filename)
  (set! tm.leap-second-table (tm.read-tai-utc-data filename))
  (values))


(define-function (tm.leap-second-delta utc-seconds)
  (letrec ( (lsd (lambda (table)
		   (cond
		    ((>= utc-seconds (caar table))
		     (cdar table))
		    (:else (lsd (cdr table)))))) )
    (if (< utc-seconds  (* (- 1972 1970) 365 tm.sid)) 0
	(lsd  tm.leap-second-table))))

;; going from tai seconds to utc seconds ...
(define-function (tm.leap-second-neg-delta tai-seconds)
  (letrec ( (lsd (lambda (table)
		   (cond ((null? table) 0)
			 ((<= (cdar table) (- tai-seconds (caar table)))
			  (cdar table))
			 (:else (lsd (cdr table)))))) )
    (if (< tai-seconds  (* (- 1972 1970) 365 tm.sid)) 0
	(lsd  tm.leap-second-table))))


;;; the time structure; creates the accessors, too.
;;; wf: changed to match srfi documentation. uses mzscheme structures & inspectors

#|(define-struct time (type nanosecond second) (make-inspector))|#
(define-record-type time
  (make-time type nanosecond second)
  time?
  (type       time-type       set-time-type!)
  (nanosecond time-nanosecond set-time-nanosecond!)
  (second     time-second     set-time-second!))

;; thanks, Martin Gasbichler ...

#|(define-function (copy-time time)
  (make-time (time-type time)
	     (time-second time)
	     (time-nanosecond time)))|#

(defmethod print-object ((obj time) stream)
  (print-unreadable-object (obj stream)
                           (format stream
                                   "~A ~D.~9,'0,D"
                                   (time-type obj)
                                   (time-second obj)
                                   (time-nanosecond obj))))

;;; current-time

;;; specific time getters.
;;; these should be rewritten to be os specific.
;;
;; -- using gnu gettimeofday() would be useful here -- gets
;;    second + millisecond
;;    let's pretend we do, using mzscheme's current-seconds & current-milliseconds
;;    this is supposed to return utc.
;;

(define-function (tm.get-time-of-day)
  (receive (ignore sec millisec)
           #+sbcl (sb-unix:unix-gettimeofday)
           #-sbcl (not-implemented)
    (declare (ignore ignore))
    (values sec millisec)))

(define-function (tm.current-time-utc)
  (receive (seconds ms) (tm.get-time-of-day)
	   (make-time  time-utc (* ms 10000) seconds )))

(define-function (tm.current-time-tai)
  (receive (seconds ms) (tm.get-time-of-day)
	   (make-time time-tai
		      (* ms 10000)
		      (+ seconds (tm.leap-second-delta seconds))
		      )))



(define-function (tm.current-time-ms-time time-type proc)
  (let ((current-ms (funcall proc)))
    (make-time time-type
	       (* (remainder current-ms 1000) 10000)
	       (quotient current-ms 10000)
	       )))

;; -- we define it to be the same as tai.
;;    a different implemation of current-time-montonic
;;    will require rewriting all of the time-monotonic converters,
;;    of course.

(define-function (tm.current-time-monotonic)
  (receive (seconds ms) (tm.get-time-of-day)
	   (make-time time-monotonic
		      (* ms 10000)
		      (+ seconds (tm.leap-second-delta seconds))
		      )))

(defun current-process-milliseconds ()
  (mod (get-internal-real-time)
       internal-time-units-per-second))

(defun current-gc-milliseconds ()
  #+sbcl sb-ext:*gc-run-time*)

(define-function (tm.current-time-thread)
  (tm.current-time-ms-time time-process #'current-process-milliseconds))

(define-function (tm.current-time-process)
  (tm.current-time-ms-time time-process #'current-process-milliseconds))

(define-function (tm.current-time-gc)
  (tm.current-time-ms-time time-gc #'current-gc-milliseconds))

(define-function (current-time . clock-type)
  (let ( (clock-type (.optional clock-type time-utc)) )
    (cond
      ((eq? clock-type time-tai) (tm.current-time-tai))
      ((eq? clock-type time-utc) (tm.current-time-utc))
      ((eq? clock-type time-monotonic) (tm.current-time-monotonic))
      ((eq? clock-type time-thread) (tm.current-time-thread))
      ((eq? clock-type time-process) (tm.current-time-process))
      ((eq? clock-type time-gc) (tm.current-time-gc))
      (:else (tm.time-error 'current-time 'invalid-clock-type clock-type)))))



;; -- time resolution
;; this is the resolution of the clock in nanoseconds.
;; this will be implementation specific.

(define-function (time-resolution . clock-type)
  (let ((clock-type (.optional clock-type time-utc)))
    (cond
      ((eq? clock-type time-tai) 10000)
      ((eq? clock-type time-utc) 10000)
      ((eq? clock-type time-monotonic) 10000)
      ((eq? clock-type time-thread) 10000)
      ((eq? clock-type time-process) 10000)
      ((eq? clock-type time-gc) 10000)
      (:else (tm.time-error 'time-resolution 'invalid-clock-type clock-type)))))

;; -- time comparisons

(define-function (tm.time-compare-check time1 time2 caller)
  (if (or (not (and (time? time1) (time? time2)))
	  (not (eq? (time-type time1) (time-type time2))))
      (tm.time-error caller 'incompatible-time-types 'NIL)
      'T))

(define-function (time=? time1 time2)
  (tm.time-compare-check time1 time2 'time=?)
  (and (= (time-second time1) (time-second time2))
       (= (time-nanosecond time1) (time-nanosecond time2))))

(define-function (time>? time1 time2)
  (tm.time-compare-check time1 time2 'time>?)
  (or (> (time-second time1) (time-second time2))
      (and (= (time-second time1) (time-second time2))
	   (> (time-nanosecond time1) (time-nanosecond time2)))))

(define-function (time<? time1 time2)
  (tm.time-compare-check time1 time2 'time<?)
  (or (< (time-second time1) (time-second time2))
      (and (= (time-second time1) (time-second time2))
	   (< (time-nanosecond time1) (time-nanosecond time2)))))

(define-function (time>=? time1 time2)
  (tm.time-compare-check time1 time2 'time>=?)
  (or (> (time-second time1) (time-second time2))
      (and (= (time-second time1) (time-second time2))
	   (>= (time-nanosecond time1) (time-nanosecond time2)))))

(define-function (time<=? time1 time2)
  (tm.time-compare-check time1 time2 'time<=?)
  (or (< (time-second time1) (time-second time2))
      (and (= (time-second time1) (time-second time2))
	   (<= (time-nanosecond time1) (time-nanosecond time2)))))

;; -- time arithmetic

(define-function (tm.time->nanoseconds time)
  ;; ???
  #|(define (sign1 n)
    (if (negative? n) -1 1))|#
  (+ (* (time-second time) tm.nano)
      (time-nanosecond time)))

(define-function (tm.nanoseconds->time time-type nanoseconds)
  (make-time time-type
             (remainder nanoseconds tm.nano)
             (quotient nanoseconds tm.nano)))

(define-function (tm.nanoseconds->values nanoseconds)
  (values (abs (remainder nanoseconds tm.nano))
          (quotient nanoseconds tm.nano)))

(define-function (tm.time-difference time1 time2 time3)
  (if (or (not (and (time? time1) (time? time2)))
	  (not (eq? (time-type time1) (time-type time2))))
      (tm.time-error 'time-difference 'incompatible-time-types 'NIL))
  (set-time-type! time3 time-duration)
  (if (time=? time1 time2)
      (begin
	(set-time-second! time3 0)
	(set-time-nanosecond! time3 0))
      (receive
       (nanos secs)
       (tm.nanoseconds->values (- (tm.time->nanoseconds time1)
                                  (tm.time->nanoseconds time2)))
       (set-time-second! time3 secs)
       (set-time-nanosecond! time3 nanos)))
  time3)

(define-function (time-difference time1 time2)
  (tm.time-difference time1 time2 (make-time 'NIL 'NIL 'NIL)))

(define-function (time-difference! time1 time2)
  (tm.time-difference time1 time2 time1))

(define-function (tm.add-duration time1 duration time3)
  (if (not (and (time? time1) (time? duration)))
      (tm.time-error 'add-duration 'incompatible-time-types 'NIL))
  (if (not (eq? (time-type duration) time-duration))
      (tm.time-error 'add-duration 'not-duration duration)
      (let ( (sec-plus (+ (time-second time1) (time-second duration)))
	     (nsec-plus (+ (time-nanosecond time1) (time-nanosecond duration))) )
	(let ((r (remainder nsec-plus tm.nano))
	      (q (quotient nsec-plus tm.nano)))
          ; (set-time-type! time3 (time-type time1))
	  (if (negative? r)
	      (begin
		(set-time-second! time3 (+ sec-plus q -1))
		(set-time-nanosecond! time3 (+ tm.nano r)))
	      (begin
		(set-time-second! time3 (+ sec-plus q))
		(set-time-nanosecond! time3 r)))
	  time3))))

(define-function (add-duration time1 duration)
  (tm.add-duration time1 duration (make-time (time-type time1) 'NIL 'NIL)))

(define-function (add-duration! time1 duration)
  (tm.add-duration time1 duration time1))

(define-function (tm.subtract-duration time1 duration time3)
  (if (not (and (time? time1) (time? duration)))
      (tm.time-error 'add-duration 'incompatible-time-types 'NIL))
  (if (not (eq? (time-type duration) time-duration))
      (tm.time-error 'tm.subtract-duration 'not-duration duration)
      (let ( (sec-minus  (- (time-second time1) (time-second duration)))
	     (nsec-minus (- (time-nanosecond time1) (time-nanosecond duration))) )
	(let ((r (remainder nsec-minus tm.nano))
	      (q (quotient nsec-minus tm.nano)))
	  (if (negative? r)
	      (begin
		(set-time-second! time3 (- sec-minus q 1))
		(set-time-nanosecond! time3 (+ tm.nano r)))
	      (begin
		(set-time-second! time3 (- sec-minus q))
		(set-time-nanosecond! time3 r)))
	  time3))))

(define-function (subtract-duration time1 duration)
  (tm.subtract-duration time1 duration (make-time (time-type time1) 'NIL 'NIL)))

(define-function (subtract-duration! time1 duration)
  (tm.subtract-duration time1 duration time1))


;; -- converters between types.

(define-function (tm.time-tai->time-utc! time-in time-out caller)
  (if (not (eq? (time-type time-in) time-tai))
      (tm.time-error caller 'incompatible-time-types time-in))
  (set-time-type! time-out time-utc)
  (set-time-nanosecond! time-out (time-nanosecond time-in))
  (set-time-second!     time-out (- (time-second time-in)
				    (tm.leap-second-neg-delta
				     (time-second time-in))))
  time-out)

(define-function (time-tai->time-utc time-in)
  (tm.time-tai->time-utc! time-in (make-time 'NIL 'NIL 'NIL) 'time-tai->time-utc))


(define-function (time-tai->time-utc! time-in)
  (tm.time-tai->time-utc! time-in time-in 'time-tai->time-utc!))


(define-function (tm.time-utc->time-tai! time-in time-out caller)
  (if (not (eq? (time-type time-in) time-utc))
      (tm.time-error caller 'incompatible-time-types time-in))
  (set-time-type! time-out time-tai)
  (set-time-nanosecond! time-out (time-nanosecond time-in))
  (set-time-second!     time-out (+ (time-second time-in)
				    (tm.leap-second-delta
				     (time-second time-in))))
  time-out)


(define-function (time-utc->time-tai time-in)
  (tm.time-utc->time-tai! time-in (make-time 'NIL 'NIL 'NIL) 'time-utc->time-tai))

(define-function (time-utc->time-tai! time-in)
  (tm.time-utc->time-tai! time-in time-in 'time-utc->time-tai!))

;; -- these depend on time-monotonic having the same definition as time-tai!
(define-function (time-monotonic->time-utc time-in)
  (if (not (eq? (time-type time-in) time-monotonic))
      (tm.time-error 'time-monotoinc->time-utc 'incompatible-time-types time-in))
  (let ((ntime (copy-time time-in)))
    (set-time-type! ntime time-tai)
    (tm.time-tai->time-utc! ntime ntime 'time-monotonic->time-utc)))

(define-function (time-monotonic->time-utc! time-in)
  (if (not (eq? (time-type time-in) time-monotonic))
      (tm.time-error 'time-monotonic->time-utc! 'incompatible-time-types time-in))
  (set-time-type! time-in time-tai)
  (tm.time-tai->time-utc! time-in time-in 'time-monotonic->time-utc))

(define-function (time-monotonic->time-tai time-in)
  (if (not (eq? (time-type time-in) time-monotonic))
      (tm.time-error 'time-monotonic->time-tai 'incompatible-time-types time-in))
  (let ((ntime (copy-time time-in)))
    (set-time-type! ntime time-tai)
    ntime))

(define-function (time-monotonic->time-tai! time-in)
  (if (not (eq? (time-type time-in) time-monotonic))
      (tm.time-error 'time-monotonic->time-tai! 'incompatible-time-types time-in))
  (set-time-type! time-in time-tai)
  time-in)

(define-function (time-utc->time-monotonic time-in)
  (if (not (eq? (time-type time-in) time-utc))
      (tm.time-error 'time-utc->time-monotonic 'incompatible-time-types time-in))
  (let ((ntime (tm.time-utc->time-tai! time-in (make-time 'NIL 'NIL 'NIL)
				       'time-utc->time-monotonic)))
    (set-time-type! ntime time-monotonic)
    ntime))


(define-function (time-utc->time-monotonic! time-in)
  (if (not (eq? (time-type time-in) time-utc))
      (tm.time-error 'time-utc->time-montonic! 'incompatible-time-types time-in))
  (let ((ntime (tm.time-utc->time-tai! time-in time-in
				       'time-utc->time-monotonic!)))
    (set-time-type! ntime time-monotonic)
    ntime))


(define-function (time-tai->time-monotonic time-in)
  (if (not (eq? (time-type time-in) time-tai))
      (tm.time-error 'time-tai->time-monotonic 'incompatible-time-types time-in))
  (let ((ntime (copy-time time-in)))
    (set-time-type! ntime time-monotonic)
    ntime))

(define-function (time-tai->time-monotonic! time-in)
  (if (not (eq? (time-type time-in) time-tai))
      (tm.time-error 'time-tai->time-monotonic!  'incompatible-time-types time-in))
  (set-time-type! time-in time-monotonic)
  time-in)


;; -- date structures

(define-record-type date
  (make-date nanosecond second minute hour day month year zone-offset)
  date?
  (nanosecond date-nanosecond set-date-nanosecond!)
  (second date-second set-date-second!)
  (minute date-minute set-date-minute!)
  (hour date-hour set-date-hour!)
  (day date-day set-date-day!)
  (month date-month set-date-month!)
  (year date-year set-date-year!)
  (zone-offset date-zone-offset set-date-zone-offset!))


;; #<date 2012/03/27 14:15:32.688865000 (32400)>

(defmethod print-object ((obj date) stream)
  (print-unreadable-object (obj stream)
    (format stream
            "DATE ~D/~2,'0,d/~2,'0,d ~2,'0,d:~2,'0,d:~2,'0,d.~9,'0,d (~D)"
            (date-year obj)
            (date-month obj)
            (date-day obj)
            (date-hour obj)
            (date-minute obj)
            (date-second obj)
            (date-nanosecond obj)
            (date-zone-offset obj))))

;; redefine setters

(define-function tm.set-date-nanosecond! #'set-date-nanosecond!)
(define-function tm.set-date-second! #'set-date-second!)
(define-function tm.set-date-minute! #'set-date-minute!)
(define-function tm.set-date-hour! #'set-date-hour!)
(define-function tm.set-date-day! #'set-date-day!)
(define-function tm.set-date-month! #'set-date-month!)
(define-function tm.set-date-year! #'set-date-year!)
(define-function tm.set-date-zone-offset! #'set-date-zone-offset!)

(define-function (set-date-second! date val)
  (declare (ignore val))
  (tm.time-error 'set-date-second! 'dates-are-immutable date))


(define-function (set-date-minute! date val)
  (declare (ignore val))
  (tm.time-error 'set-date-minute! 'dates-are-immutable date))

(define-function (set-date-day! date val)
  (declare (ignore val))
  (tm.time-error 'set-date-day! 'dates-are-immutable date))

(define-function (set-date-month! date val)
  (declare (ignore val))
  (tm.time-error 'set-date-month! 'dates-are-immutable date))

(define-function (set-date-year! date val)
  (declare (ignore val))
  (tm.time-error 'set-date-year! 'dates-are-immutable date))

(define-function (set-date-zone-offset! date val)
  (declare (ignore val))
  (tm.time-error 'set-date-zone-offset! 'dates-are-immutable date))

;; gives the julian day which starts at noon.
(define-function (tm.encode-julian-day-number day month year)
  (let* ((a (quotient (- 14 month) 12))
	 (y (- (- (+ year 4800) a) (if (negative? year) -1 0)))
	 (m (- (+ month (* 12 a)) 3)))
    (+ day
       (quotient (+ (* 153 m) 2) 5)
       (* 365 y)
       (quotient y 4)
       (- (quotient y 100))
       (quotient y 400)
       -32045)))

(define-function (tm.char-pos char str index len)
  (cond
   ((>= index len) 'NIL)
   ((char=? (string-ref str index) char)
    index)
   (:else
    (tm.char-pos char str (+ index 1) len))))


(define-function (tm.fractional-part r)
  (if (integer? r) "0"
      (let ((str (number->string (exact->inexact r))))
	(let ((ppos (tm.char-pos #\. str 0 (string-length str))))
	  (subseq str  (+ ppos 1) (string-length str))))))


;; gives the seconds/date/month/year
(define-function (tm.decode-julian-day-number jdn)
  (let* ((days (truncate jdn))
	 (a (+ days 32044))
	 (b (quotient (+ (* 4 a) 3) 146097))
	 (c (- a (quotient (* 146097 b) 4)))
	 (d (quotient (+ (* 4 c) 3) 1461))
	 (e (- c (quotient (* 1461 d) 4)))
	 (m (quotient (+ (* 5 e) 2) 153))
	 (y (+ (* 100 b) d -4800 (quotient m 10))))
    (values ; seconds date month year
     (* (- jdn days) tm.sid)
     (+ e (- (quotient (+ (* 153 m) 2) 5)) 1)
     (+ m 3 (* -12 (quotient m 10)))
     (if (>= 0 y) (- y 1) y))
    ))


;; relies on the fact that we named our time zone accessor
;; differently from MzScheme's....
;; This should be written to be OS specific.

(define-function (tm.local-tz-offset)
  (* -1 60 60 (nth-value 8 (decode-universal-time (get-universal-time))))
  #|(date-time-zone-offset (seconds->date (current-seconds)))|#)

;; special thing -- ignores nanos
(define-function (tm.time->julian-day-number seconds tz-offset)
  (+ (/ (+ seconds
	   tz-offset
	   tm.sihd)
	tm.sid)
     tm.tai-epoch-in-jd))

(define-function (tm.find proc l)
  (if (null? l)
      'NIL
      (if (funcall proc (car l))
	  'T
	  (tm.find proc (cdr l)))))

(define-function (tm.tai-before-leap-second? second)
  (tm.find (lambda (x)
	     (= second (- (+ (car x) (cdr x)) 1)))
	   tm.leap-second-table))

(define-function (tm.time->date time tz-offset ttype)
  (if (not (eq? (time-type time) ttype))
      (tm.time-error 'time->date 'incompatible-time-types  time))
  (let* ( (offset (.optional tz-offset (tm.local-tz-offset))) )
    (receive (secs date month year)
	     (tm.decode-julian-day-number
	      (tm.time->julian-day-number (time-second time) offset))
	     (let* ( (hours    (quotient secs (* 60 60)))
		     (rem      (remainder secs (* 60 60)))
		     (minutes  (quotient rem 60))
		     (seconds  (remainder rem 60)) )
	       (make-date (time-nanosecond time)
			  seconds
			  minutes
			  hours
			  date
			  month
			  year
			  offset)))))

(define-function (time-tai->date time . tz-offset)
  (if (tm.tai-before-leap-second? (time-second time))
      ;; if it's *right* before the leap, we need to pretend to subtract a second ...
      (let ((d (tm.time->date (subtract-duration! (time-tai->time-utc time) (make-time time-duration 0 1)) tz-offset time-utc)))
	(tm.set-date-second! d 60)
	d)
      (tm.time->date (time-tai->time-utc time) tz-offset time-utc)))

(define-function (time-utc->date time . tz-offset)
  (tm.time->date time tz-offset time-utc))

;; again, time-monotonic is the same as time tai
(define-function (time-monotonic->date time . tz-offset)
  (tm.time->date time tz-offset time-monotonic))

(define-function (date->time-utc date)
  (let ( (nanosecond (date-nanosecond date))
	 (second (date-second date))
	 (minute (date-minute date))
	 (hour (date-hour date))
	 (day (date-day date))
	 (month (date-month date))
	 (year (date-year date))
	 (offset (date-zone-offset date)) )
    (let ( (jdays (- (tm.encode-julian-day-number day month year)
		     tm.tai-epoch-in-jd)) )
      (make-time
       time-utc
       nanosecond
       (+ (* (- jdays 1/2) 24 60 60)
	  (* hour 60 60)
	  (* minute 60)
	  second
	  (- offset))
       ))))

(define-function (date->time-tai d)
  (if (= (date-second d) 60)
      (subtract-duration! (time-utc->time-tai! (date->time-utc d)) (make-time time-duration 0 1))
      (time-utc->time-tai! (date->time-utc d))))

(define-function (date->time-monotonic date)
  (time-utc->time-monotonic! (date->time-utc date)))


(define-function (tm.leap-year? year)
  (or (= (modulo year 400) 0)
      (and (= (modulo year 4) 0) (not (= (modulo year 100) 0)))))

(define-function (leap-year? date)
  (tm.leap-year? (date-year date)))

;; tm.year-day fixed: adding wrong number of days.
(defvar  tm.month-assoc '((0 . 0) (1 . 31)  (2 . 59)   (3 . 90)   (4 . 120)
			  (5 . 151) (6 . 181)  (7 . 212)  (8 . 243)
			  (9 . 273) (10 . 304) (11 . 334)))

(define-function (tm.year-day day month year)
  (let ((days-pr (assoc (- month 1) tm.month-assoc)))
    (if (not days-pr)
	(tm.time-error 'date-year-day 'invalid-month-specification month))
    (if (and (tm.leap-year? year) (> month 2))
	(+ day (cdr days-pr) 1)
	(+ day (cdr days-pr)))))

(define-function (date-year-day date)
  (tm.year-day (date-day date) (date-month date) (date-year date)))

;; from calendar faq
(define-function (tm.week-day day month year)
  (let* ((a (quotient (- 14 month) 12))
	 (y (- year a))
	 (m (+ month (* 12 a) -2)))
    (modulo (+ day y (quotient y 4) (- (quotient y 100))
	       (quotient y 400) (quotient (* 31 m) 12))
	    7)))

(define-function (date-week-day date)
  (tm.week-day (date-day date) (date-month date) (date-year date)))

(define-function (tm.days-before-first-week date day-of-week-starting-week)
  (let* ( (first-day (make-date 0 0 0 0
                                1
                                1
                                (date-year date)
                                'NIL))
          (fdweek-day (date-week-day first-day))  )
    (modulo (- day-of-week-starting-week fdweek-day)
            7)))

(define-function (date-week-number date day-of-week-starting-week)
  (quotient (- (date-year-day date)
	       (tm.days-before-first-week  date day-of-week-starting-week))
	    7))

(define-function (current-date . tz-offset)
  (time-utc->date (current-time time-utc)
		  (.optional tz-offset (tm.local-tz-offset))))

;; given a 'two digit' number, find the year within 50 years +/-
(define-function (tm.natural-year n)
  (let* ( (current-year (date-year (current-date)))
	  (current-century (* (quotient current-year 100) 100)) )
    (cond
      ((>= n 100) n)
      ((<  n 0) n)
      ((<=  (- (+ current-century n) current-year) 50)
       (+ current-century n))
      (:else
       (+ (- current-century 100) n)))))

(define-function (date->julian-day date)
  (let ( (nanosecond (date-nanosecond date))
	 (second (date-second date))
	 (minute (date-minute date))
	 (hour (date-hour date))
	 (day (date-day date))
	 (month (date-month date))
	 (year (date-year date))
	 (offset (date-zone-offset date)) )
    (+ (tm.encode-julian-day-number day month year)
       (- 1/2)
       (+ (/ (/ (+ (* hour 60 60)
		   (* minute 60) second (/ nanosecond tm.nano)) tm.sid)
	     (- offset))))))

(define-function (date->modified-julian-day date)
  (- (date->julian-day date)
     4800001/2))


(define-function (time-utc->julian-day time)
  (if (not (eq? (time-type time) time-utc))
      (tm.time-error 'time-utc->julian-day 'incompatible-time-types  time))
  (+ (/ (+ (time-second time) (/ (time-nanosecond time) tm.nano))
	tm.sid)
     tm.tai-epoch-in-jd))

(define-function (time-utc->modified-julian-day time)
  (- (time-utc->julian-day time)
     4800001/2))

(define-function (time-tai->julian-day time)
  (if (not (eq? (time-type time) time-tai))
      (tm.time-error 'time-tai->julian-day 'incompatible-time-types  time))
  (+ (/ (+ (- (time-second time)
	      (tm.leap-second-delta (time-second time)))
	   (/ (time-nanosecond time) tm.nano))
	tm.sid)
     tm.tai-epoch-in-jd))

(define-function (time-tai->modified-julian-day time)
  (- (time-tai->julian-day time)
     4800001/2))

;; this is the same as time-tai->julian-day
(define-function (time-monotonic->julian-day time)
  (if (not (eq? (time-type time) time-monotonic))
      (tm.time-error 'time-monotonic->julian-day 'incompatible-time-types  time))
  (+ (/ (+ (- (time-second time)
	      (tm.leap-second-delta (time-second time)))
	   (/ (time-nanosecond time) tm.nano))
	tm.sid)
     tm.tai-epoch-in-jd))


(define-function (time-monotonic->modified-julian-day time)
  (- (time-monotonic->julian-day time)
     4800001/2))


(define-function (julian-day->time-utc jdn)
  (let ( (nanosecs (* tm.nano tm.sid (- jdn tm.tai-epoch-in-jd))) )
    (make-time time-utc
	       (remainder nanosecs tm.nano)
	       (floor (/ nanosecs tm.nano)))))

(define-function (julian-day->time-tai jdn)
  (time-utc->time-tai! (julian-day->time-utc jdn)))

(define-function (julian-day->time-monotonic jdn)
  (time-utc->time-monotonic! (julian-day->time-utc jdn)))

(define-function (julian-day->date jdn . tz-offset)
  (let ((offset (.optional tz-offset (tm.local-tz-offset))))
    (time-utc->date (julian-day->time-utc jdn) offset)))

(define-function (modified-julian-day->date jdn . tz-offset)
  (let ((offset (.optional tz-offset (tm.local-tz-offset))))
    (julian-day->date (+ jdn 4800001/2) offset)))

(define-function (modified-julian-day->time-utc jdn)
  (julian-day->time-utc (+ jdn 4800001/2)))

(define-function (modified-julian-day->time-tai jdn)
  (julian-day->time-tai (+ jdn 4800001/2)))

(define-function (modified-julian-day->time-monotonic jdn)
  (julian-day->time-monotonic (+ jdn 4800001/2)))

(define-function (current-julian-day)
  (time-utc->julian-day (current-time time-utc)))

(define-function (current-modified-julian-day)
  (time-utc->modified-julian-day (current-time time-utc)))

;; returns a string rep. of number N, of minimum LENGTH,
;; padded with character PAD-WITH. If PAD-WITH if 'NIL,
;; no padding is done, and it's as if number->string was used.
;; if string is longer than LENGTH, it's as if number->string was used.

(define-function (tm.padding n pad-with length)
  (let* ( (str (number->string n))
	  (str-len (string-length str)) )
    (if (or (> str-len length)
            (not pad-with))
	str
	(let* ( (new-str (make-string length :initial-element pad-with))
		(new-str-offset (- (string-length new-str)
				   str-len)) )
	  (do ((i 0 (+ i 1)))
            ((>= i (string-length str)))
            (string-set! new-str (+ new-str-offset i)
                         (string-ref str i)))
	  new-str))))

(define-function (tm.last-n-digits i n)
  (abs (remainder i (expt 10 n))))

(define-function (tm.locale-abbr-weekday n)
  (vector-ref tm.locale-abbr-weekday-vector n))

(define-function (tm.locale-long-weekday n)
  (vector-ref tm.locale-long-weekday-vector n))

(define-function (tm.locale-abbr-month n)
  (vector-ref tm.locale-abbr-month-vector n))

(define-function (tm.locale-long-month n)
  (vector-ref tm.locale-long-month-vector n))

(define-function (tm.vector-find needle haystack comparator)
  (let ((len (vector-length haystack)))
    (labels ((tm.vector-find-int (index)
               (cond
                 ((>= index len) 'NIL)
                 ((funcall comparator needle (vector-ref haystack index)) index)
                 (:else (tm.vector-find-int (+ index 1))))))
      (tm.vector-find-int 0))))

(define-function (tm.locale-abbr-weekday->index string)
  (tm.vector-find string tm.locale-abbr-weekday-vector #'string=?))

(define-function (tm.locale-long-weekday->index string)
  (tm.vector-find string tm.locale-long-weekday-vector #'string=?))

(define-function (tm.locale-abbr-month->index string)
  (tm.vector-find string tm.locale-abbr-month-vector #'string=?))

(define-function (tm.locale-long-month->index string)
  (tm.vector-find string tm.locale-long-month-vector #'string=?))



;; do nothing.
;; Your implementation might want to do something...
;;
(define-function (tm.locale-print-time-zone date port)
  (declare (ignore date port))
  (values))

;; Again, locale specific.
(define-function (tm.locale-am/pm hr)
  (if (> hr 11) tm.locale-pm tm.locale-am))

(define-function (tm.tz-printer offset port)
  (cond
    ((= offset 0) (display "Z" port))
    ((negative? offset) (display "-" port))
    (:else (display "+" port)))
  (if (not (= offset 0))
      (let ( (hours   (abs (quotient offset (* 60 60))))
	     (minutes (abs (quotient (remainder offset (* 60 60)) 60))) )
	(display (tm.padding hours #\0 2) port)
	(display (tm.padding minutes #\0 2) port))))

;; A table of output formatting directives.
;; the first time is the format char.
;; the second is a procedure that takes the date, a padding character
;; (which might be 'NIL), and the output port.
;;
(defvar tm.directives
  (list
   (cons #\~ (lambda (date pad-with port)
               (declare (ignore pad-with date))
               (display #\~ port)))

   (cons #\a (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (tm.locale-abbr-weekday (date-week-day date))
			port)))
   (cons #\A (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (tm.locale-long-weekday (date-week-day date))
			port)))
   (cons #\b (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (tm.locale-abbr-month (date-month date))
			port)))
   (cons #\B (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (tm.locale-long-month (date-month date))
			port)))
   (cons #\c (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (date->string date tm.locale-date-time-format) port)))
   (cons #\d (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (tm.padding (date-day date)
				    #\0 2)
                        port)))
   (cons #\D (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (date->string date "~m/~d/~y") port)))
   (cons #\e (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (tm.padding (date-day date)
				    #\space 2)
			port)))
   (cons #\f (lambda (date pad-with port)
	       (if (> (date-nanosecond date)
		      tm.nano)
		   (display (tm.padding (+ (date-second date) 1)
					pad-with 2)
			    port)
		   (display (tm.padding (date-second date)
					pad-with 2)
			    port))
	       (let* ((ns (tm.fractional-part (/
					       (date-nanosecond date)
					       tm.nano 1.0)))
		      (le (string-length ns)))
		 (if (> le 2)
		     (begin
		       (display tm.locale-number-separator port)
		       (display (subseq ns 2 le) port))))))
   (cons #\h (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (date->string date "~b") port)))
   (cons #\H (lambda (date pad-with port)
	       (display (tm.padding (date-hour date)
				    pad-with 2)
			port)))
   (cons #\I (lambda (date pad-with port)
	       (let ((hr (date-hour date)))
		 (if (> hr 12)
		     (display (tm.padding (- hr 12)
					  pad-with 2)
			      port)
		     (display (tm.padding hr
					  pad-with 2)
			      port)))))
   (cons #\j (lambda (date pad-with port)
	       (display (tm.padding (date-year-day date)
				    pad-with 3)
			port)))
   (cons #\k (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (tm.padding (date-hour date)
				    #\0 2)
                        port)))
   (cons #\l (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (let ((hr (if (> (date-hour date) 12)
			     (- (date-hour date) 12) (date-hour date))))
		 (display (tm.padding hr  #\space 2)
			  port))))
   (cons #\m (lambda (date pad-with port)
	       (display (tm.padding (date-month date)
				    pad-with 2)
			port)))
   (cons #\M (lambda (date pad-with port)
	       (display (tm.padding (date-minute date)
				    pad-with 2)
			port)))
   (cons #\n (lambda (date pad-with port)
               (declare (ignore pad-with date))
	       (newline port)))
   (cons #\N (lambda (date pad-with port)
	       (display (tm.padding (date-nanosecond date)
				    pad-with 9)
			port)))
   (cons #\p (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (tm.locale-am/pm (date-hour date)) port)))
   (cons #\r (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (date->string date "~I:~M:~S ~p") port)))
   (cons #\s (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (time-second (date->time-utc date)) port)))
   (cons #\S (lambda (date pad-with port)
	       (if (> (date-nanosecond date)
		      tm.nano)
                   (display (tm.padding (+ (date-second date) 1)
                                        pad-with 2)
                            port)
                   (display (tm.padding (date-second date)
                                        pad-with 2)
                            port))))
   (cons #\t (lambda (date pad-with port)
               (declare (ignore pad-with date))
	       (display (code-char 9) port)))
   (cons #\T (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (date->string date "~H:~M:~S") port)))
   (cons #\U (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (if (> (tm.days-before-first-week date 0) 0)
		   (display (tm.padding (+ (date-week-number date 0) 1)
					#\0 2) port)
		   (display (tm.padding (date-week-number date 0)
					#\0 2) port))))
   (cons #\V (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (tm.padding (date-week-number date 1)
				    #\0 2) port)))
   (cons #\w (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (date-week-day date) port)))
   (cons #\x (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (date->string date tm.locale-short-date-format) port)))
   (cons #\X (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (date->string date tm.locale-time-format) port)))
   (cons #\W (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (if (> (tm.days-before-first-week date 1) 0)
		   (display (tm.padding (+ (date-week-number date 1) 1)
					#\0 2) port)
		   (display (tm.padding (date-week-number date 1)
					#\0 2) port))))
   (cons #\y (lambda (date pad-with port)
	       (display (tm.padding (tm.last-n-digits
				     (date-year date) 2)
				    pad-with
				    2)
			port)))
   (cons #\Y (lambda (date pad-with port)
	       (display (tm.padding (date-year date)
				    pad-with
				    4)
			port)))
   (cons #\z (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (tm.tz-printer (date-zone-offset date) port)))
   (cons #\Z (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (tm.locale-print-time-zone date port)))
   (cons #\1 (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (date->string date "~Y-~m-~d") port)))
   (cons #\2 (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (date->string date "~k:~M:~S~z") port)))
   (cons #\3 (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (date->string date "~k:~M:~S") port)))
   (cons #\4 (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (date->string date "~Y-~m-~dT~k:~M:~S~z") port)))
   (cons #\5 (lambda (date pad-with port)
               (declare (ignore pad-with))
	       (display (date->string date "~Y-~m-~dT~k:~M:~S") port)))
   ))


(define-function (tm.get-formatter char)
  (let ( (associated (assoc char tm.directives)) )
    (if associated (cdr associated) 'NIL)))

(define-function (tm.date-printer date index format-string str-len port)
  (if (>= index str-len)
      (values)
      (let ( (current-char (string-ref format-string index)) )
	(if (not (char=? current-char #\~))
	    (begin
	      (display current-char port)
	      (tm.date-printer date (+ index 1) format-string str-len port))

	    (if (= (+ index 1) str-len) ; bad format string.
		(tm.time-error 'tm.date-printer 'bad-date-format-string
			       format-string)
                (let ( (pad-char? (string-ref format-string (+ index 1))) )
                  (cond
                    ((char=? pad-char? #\-)
                     (if (= (+ index 2) str-len) ; bad format string.
                         (tm.time-error 'tm.date-printer 'bad-date-format-string
                                        format-string)
                         (let ( (formatter (tm.get-formatter
                                            (string-ref format-string
                                                        (+ index 2)))) )
                           (if (not formatter)
                               (tm.time-error 'tm.date-printer 'bad-date-format-string
                                              format-string)
                               (begin
                                 (funcall formatter date 'NIL port)
                                 (tm.date-printer date (+ index 3)
                                                  format-string str-len port))))))

                    ((char=? pad-char? #\_)
                     (if (= (+ index 2) str-len) ; bad format string.
                         (tm.time-error 'tm.date-printer 'bad-date-format-string
                                        format-string)
                         (let ( (formatter (tm.get-formatter
                                            (string-ref format-string
                                                        (+ index 2)))) )
                           (if (not formatter)
                               (tm.time-error 'tm.date-printer 'bad-date-format-string
                                              format-string)
                               (begin
                                 (funcall formatter date #\space port)
                                 (tm.date-printer date (+ index 3)
                                                  format-string str-len port))))))
                    (:else
                     (let ( (formatter (tm.get-formatter
                                        (string-ref format-string
                                                    (+ index 1)))) )
                       (if (not formatter)
                           (tm.time-error 'tm.date-printer 'bad-date-format-string
                                          format-string)
                           (begin
                             (funcall formatter date #\0 port)
                             (tm.date-printer date (+ index 2)
                                              format-string str-len port))))))))))))


(define-function (date->string date .  format-string)
  "~~	any	read literal ~	nothing
~a	char-alphabetic?	abbreviated weekday in locale	nothing
~A	char-alphabetic?	full weekday in locale	nothing
~b	char-alphabetic?	abbreviated month name in locale	nothing
~B	char-alphabetic?	full month name in locale	nothing
~d	char-numeric?	day of month	date-day
~e	any	day of month, blank padded	date-day
~h	char-alphabetic?	same as ~b	nothing
~H	char-numeric?	hour	date-hour
~k	any	hour, blank padded	date-hour
~m	char-numeric?	month	date-month
~M	char-numeric?	minute	date-minute
~S	char-numeric?	second	date-second
~y	any	2-digit year	date-year within 50 years
~Y	char-numeric?	year	date-year
~z	any	time zone	date-zone-offset"
  (let ( (str-port (open-output-string))
	 (fmt-str (.optional format-string "~c")) )
    (tm.date-printer date 0 fmt-str (string-length fmt-str) str-port)
    (get-output-string str-port)))

(define-function (tm.char->int ch)
  (cond
    ((char=? ch #\0) 0)
    ((char=? ch #\1) 1)
    ((char=? ch #\2) 2)
    ((char=? ch #\3) 3)
    ((char=? ch #\4) 4)
    ((char=? ch #\5) 5)
    ((char=? ch #\6) 6)
    ((char=? ch #\7) 7)
    ((char=? ch #\8) 8)
    ((char=? ch #\9) 9)
    (:else (tm.time-error 'string->date 'bad-date-template-string
                         (list "Non-integer character" ch )))))

;; read an integer upto n characters long on port; upto -> 'NIL if any length
(define-function (tm.integer-reader upto port)
  (labels ((accum-int (port accum nchars)
             (let ((ch (peek-char port)))
               (if (or (eof-object? ch)
                       (not (digit-char-p ch))
                       (and upto (>= nchars  upto )) )
                   accum
                   (accum-int port
                              (+ (* accum 10)
                                 (tm.char->int (read-char port)))
                              (+ nchars 1))))))
    (accum-int port 0 0) ) )

(define-function (tm.make-integer-reader upto)
  (lambda (port)
    (tm.integer-reader upto port)))

;; read an fractional integer upto n characters long on port; upto -> 'NIL if any length
;;
;; The return value is normalized to upto decimal places. For example, if upto is 9 and
;; the string read is "123", the return value is 123000000.
(define-function (tm.fractional-integer-reader upto port)
  (labels ((accum-int (port accum nchars)
             (let ((ch (peek-char port)))
               (if (or (eof-object? ch)
                       (not (digit-char-p ch))
                       (and upto (>= nchars  upto )) )
                   (* accum (expt 10 (- upto nchars)))
                   (accum-int port
                              (+ (* accum 10) (tm.char->int (read-char port)))
                              (+ nchars 1)) ))))
    (accum-int port 0 0) ))

(define-function (tm.make-fractional-integer-reader upto)
  (lambda (port)
    (tm.fractional-integer-reader upto port)))


;; read *exactly* n characters and convert to integer; could be padded
(define-function (tm.integer-reader-exact n port)
  (let ( (padding-ok 'T) )
    (labels ((accum-int (port accum nchars)
               (let ((ch (peek-char port)))
                 (cond
                   ((>= nchars n) accum)
                   ((eof-object? ch)
                    (tm.time-error 'string->date 'bad-date-template-string
                                   "Premature ending to integer read." ))
                   ((digit-char-p ch)
                    (set! padding-ok 'NIL)
                    (accum-int port (+ (* accum 10) (tm.char->int (read-char
                                                                   port )))
                               (+ nchars 1) ))
                   (padding-ok
                    (read-char port) ; consume padding
                    (accum-int port accum (+ nchars 1)) )
                   (:else ; padding where it shouldn't be
                    (tm.time-error 'string->date 'bad-date-template-string
                                   "Non-numeric characters in integer read." ))))))
      (accum-int port 0 0) )))


(define-function (tm.make-integer-exact-reader n)
  (lambda (port)
    (tm.integer-reader-exact n port)))

(define-function (tm.zone-reader port)
  (let ( (offset 0)
	 (positive? 'NIL) )
    (let ( (ch (read-char port)) )
      (if (eof-object? ch)
	  (tm.time-error 'string->date 'bad-date-template-string
			 (list "Invalid time zone +/-" ch)))
      (if (or (char=? ch #\Z) (char=? ch #\z))
	  0
	  (begin
	    (cond
              ((char=? ch #\+) (set! positive? 'T))
              ((char=? ch #\-) (set! positive? 'NIL))
              (:else
               (tm.time-error 'string->date 'bad-date-template-string
                              (list "Invalid time zone +/-" ch))))
	    (let ((ch (read-char port)))
	      (if (eof-object? ch)
		  (tm.time-error 'string->date 'bad-date-template-string
                                 (list "Invalid time zone number" ch)))
	      (set! offset (* (tm.char->int ch)
			      10 60 60)))
	    (let ((ch (read-char port)))
	      (if (eof-object? ch)
		  (tm.time-error 'string->date 'bad-date-template-string
				 (list "Invalid time zone number" ch)))
	      (set! offset (+ offset (* (tm.char->int ch)
					60 60))))
	    (let ((ch (read-char port)))
	      (if (eof-object? ch)
		  (tm.time-error 'string->date 'bad-date-template-string
				 (list "Invalid time zone number" ch)))
	      (set! offset (+ offset (* (tm.char->int ch)
					10 60))))
	    (let ((ch (read-char port)))
	      (if (eof-object? ch)
		  (tm.time-error 'string->date 'bad-date-template-string
				 (list "Invalid time zone number" ch)))
	      (set! offset (+ offset (* (tm.char->int ch)
					60))))
	    (if positive? offset (- offset)))))))

;; looking at a char, read the char string, run thru indexer, return index
(define-function (tm.locale-reader port indexer)
  (let ( (string-port (open-output-string)) )
    (labels ((read-char-string ()
               (let ((ch (peek-char port)))
                 (if (alpha-char-p ch)
                     (begin (write-char (read-char port) string-port)
                            (read-char-string) )
                     (get-output-string string-port) ))))
      (let* ( (str (read-char-string))
             (index (funcall indexer str)) )
        (if index index (tm.time-error 'string->date
                                       'bad-date-template-string
                                       (list "Invalid string for " indexer) ))))))

(define-function (tm.make-locale-reader indexer)
  (lambda (port)
    (tm.locale-reader port indexer)))

(define-function (tm.make-char-id-reader char)
  (lambda (port)
    (if (char=? char (read-char port))
	char
	(tm.time-error 'string->date
		       'bad-date-template-string
		       "Invalid character match."))))

;; A List of formatted read directives.
;; Each entry is a list.
;; 1. the character directive;
;; a procedure, which takes a character as input & returns
;; 2. 'T as soon as a character on the input port is acceptable
;; for input,
;; 3. a port reader procedure that knows how to read the current port
;; for a value. Its one parameter is the port.
;; 4. a action procedure, that takes the value (from 3.) and some
;; object (here, always the date) and (probably) side-effects it.
;; In some cases (e.g., ~A) the action is to do nothing

;;;;
(defvar tm.read-directives
  (let ( (ireader4 (tm.make-integer-reader 4))
	 (ireader2 (tm.make-integer-reader 2))
	 (fireader9 (tm.make-fractional-integer-reader 9))
	 (ireaderf (tm.make-integer-reader 'NIL))
	 (eireader2 (tm.make-integer-exact-reader 2))
	 (eireader4 (tm.make-integer-exact-reader 4))
	 (locale-reader-abbr-weekday (tm.make-locale-reader
				      #'tm.locale-abbr-weekday->index))
	 (locale-reader-long-weekday (tm.make-locale-reader
				      #'tm.locale-long-weekday->index))
	 (locale-reader-abbr-month   (tm.make-locale-reader
				      #'tm.locale-abbr-month->index))
	 (locale-reader-long-month   (tm.make-locale-reader
				      #'tm.locale-long-month->index))
	 (char-fail (constantly 'T))
	 (do-nothing (lambda (val object)
                       (declare (ignore val object))
                       (values)))
	 (char-alphabetic? #'alpha-char-p)
         (char-numeric? #'digit-char-p))
    (declare (ignore ireaderf eireader4))

    (list
     (list #\~ char-fail (tm.make-char-id-reader #\~) do-nothing)
     (list #\a char-alphabetic? locale-reader-abbr-weekday do-nothing)
     (list #\A char-alphabetic? locale-reader-long-weekday do-nothing)
     (list #\b char-alphabetic? locale-reader-abbr-month
           (lambda (val object)
             (tm.set-date-month! object val)))
     (list #\B char-alphabetic? locale-reader-long-month
           (lambda (val object)
             (tm.set-date-month! object val)))
     (list #\d char-numeric? ireader2 (lambda (val object)
                                        (tm.set-date-day!
                                         object val)))
     (list #\e char-fail eireader2 (lambda (val object)
                                     (tm.set-date-day! object val)))
     (list #\h char-alphabetic? locale-reader-abbr-month
           (lambda (val object)
             (tm.set-date-month! object val)))
     (list #\H char-numeric? ireader2 (lambda (val object)
                                        (tm.set-date-hour! object val)))
     (list #\k char-fail eireader2 (lambda (val object)
                                     (tm.set-date-hour! object val)))
     (list #\m char-numeric? ireader2 (lambda (val object)
                                        (tm.set-date-month! object val)))
     (list #\M char-numeric? ireader2 (lambda (val object)
                                        (tm.set-date-minute!
                                         object val)))
     (list #\N char-numeric? fireader9 (lambda (val object)
					 (tm.set-date-nanosecond! object val)))
     (list #\S char-numeric? ireader2 (lambda (val object)
                                        (tm.set-date-second! object val)))
     (list #\y char-fail eireader2
           (lambda (val object)
             (tm.set-date-year! object (tm.natural-year val))))
     (list #\Y char-numeric? ireader4 (lambda (val object)
                                        (tm.set-date-year! object val)))
     (list #\z (lambda (c)
                 (or (char=? c #\Z)
                     (char=? c #\z)
                     (char=? c #\+)
                     (char=? c #\-)))
           #'tm.zone-reader (lambda (val object)
                            (tm.set-date-zone-offset! object val)))
     )))

(define-function (tm.string->date date index format-string str-len port template-string)
  (labels ((skip-until (port skipper)
             (let ((ch (peek-char port)))
               (if (eof-object? ch)
                   (tm.time-error 'string->date 'bad-date-format-string template-string)
                   (if (not (funcall skipper ch))
                       (begin (read-char port) (skip-until port skipper)) )))))
    (if (>= index str-len)
        (begin
          (values) )
        (let ( (current-char (string-ref format-string index)) )
          (if (not (char=? current-char #\~))
              (let ((port-char (read-char port)))
                (if (or (eof-object? port-char)
                        (not (char=? current-char port-char)) )
                    (tm.time-error 'string->date 'bad-date-format-string template-string) )
                (tm.string->date date (+ index 1) format-string str-len port template-string) )
              ;; otherwise, it's an escape, we hope
              (if (> (+ index 1) str-len)
                  (tm.time-error 'string->date 'bad-date-format-string template-string)
                  (let* ( (format-char (string-ref format-string (+ index 1)))
                         (format-info (assoc format-char tm.read-directives)) )
                    (if (not format-info)
                        (tm.time-error 'string->date 'bad-date-format-string template-string)
                        (begin
                          (let ((skipper (cadr format-info))
                                (reader  (caddr format-info))
                                (actor   (cadddr format-info)) )
                            (skip-until port skipper)
                            (let ((val (funcall reader port)))
                              (if (eof-object? val)
                                  (tm.time-error 'string->date 'bad-date-format-string template-string)
                                  (funcall actor val date) ))
                            (tm.string->date date (+ index 2) format-string  str-len port template-string) ))))))))))

(define-function (string->date input-string template-string)
  "~~	a literal ~
~a	locale's abbreviated weekday name (Sun...Sat)
~A	locale's full weekday name (Sunday...Saturday)
~b	locale's abbreviate month name (Jan...Dec)
~B	locale's full month day (January...December)
~c	locale's date and time (e.g., \"Fri Jul 14 20:28:42-0400 2000\")
~d	day of month, zero padded (01...31)
~D	date (mm/dd/yy)
~e	day of month, blank padded ( 1...31)
~f	seconds+fractional seconds, using locale's decimal separator (e.g. 5.2).
~h	same as ~b
~H	hour, zero padded, 24-hour clock (00...23)
~I	hour, zero padded, 12-hour clock (01...12)
~j	day of year, zero padded
~k	hour, blank padded, 24-hour clock (00...23)
~l	hour, blank padded, 12-hour clock (01...12)
~m	month, zero padded (01...12)
~M	minute, zero padded (00...59)
~n	new line
~N	nanosecond, zero padded
~p	locale's AM or PM
~r	time, 12 hour clock, same as \"~I:~M:~S ~p\"
~s	number of full seconds since \"the epoch\" (in UTC)
~S	second, zero padded (00...60)
~t	horizontal tab
~T	time, 24 hour clock, same as \"~H:~M:~S\"
~U	week number of year with Sunday as first day of week (00...53)
~V	week number of year with Monday as first day of week (01...52)
~w	day of week (0...6)
~W	week number of year with Monday as first day of week (01...52)
~x	week number of year with Monday as first day of week (00...53)
~X	locale's date representation, for example: \"07/31/00\"
~y	last two digits of year (00...99)
~Y	year
~z	time zone in RFC-822 style
~Z	symbol time zone (not-implemented)
~1	ISO-8601 year-month-day format
~2	ISO-8601 hour-minute-second-timezone format
~3	ISO-8601 hour-minute-second format
~4	ISO-8601 year-month-day-hour-minute-second-timezone format
~5	ISO-8601 year-month-day-hour-minute-second format"
  (labels ((tm.date-ok? (date)
             (and (date-nanosecond date)
                  (date-second date)
                  (date-minute date)
                  (date-hour date)
                  (date-day date)
                  (date-month date)
                  (date-year date)
                  (date-zone-offset date))))
    (let ( (newdate (make-date 0 0 0 0 'NIL 'NIL 'NIL (tm.local-tz-offset))) )
      (tm.string->date newdate
                       0
                       template-string
                       (string-length template-string)
                       (open-input-string input-string)
                       template-string)
      (if (tm.date-ok? newdate)
          newdate
          (tm.time-error 'string->date 'bad-date-format-string (list "Incomplete date read. " newdate template-string))))))

;;; eof
