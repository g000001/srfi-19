;;;; package.lisp

(cl:in-package cl-user)

(defpackage "https://github.com/g000001/srfi-19"
  (:use)
  (:export
   time-duration time-monotonic time-process time-tai time-thread
   time-utc current-date current-julian-day
   current-modified-julian-day current-time
   time-resolution make-time time? time-type time-nanosecond
   time-second set-time-type! set-time-nanosecond! set-time-second!
   copy-time time<=? time<? time=? time>? time>=? time-difference
   time-difference! add-duration add-duration! subtract-duration
   subtract-duration! make-date
   date? date-nanosecond date-second date-minute date-hour date-day
   date-month date-year date-zone-offset date-year-day date-week-day
   date-week-number date->julian-day date->modified-julian-day
   date->time-monotonic date->time-tai date->time-utc julian-day->date
   julian-day->time-monotonic julian-day->time-tai julian-day->time-utc
   modified-julian-day->date modified-julian-day->time-monotonic
   modified-julian-day->time-tai modified-julian-day->time-utc
   time-monotonic->date time-monotonic->julian-day
   time-monotonic->modified-julian-day time-monotonic->time-tai
   time-monotonic->time-tai! time-monotonic->time-utc
   time-monotonic->time-utc! time-tai->date time-tai->julian-day
   time-tai->modified-julian-day time-tai->time-monotonic
   time-tai->time-monotonic! time-tai->time-utc time-tai->time-utc!
   time-utc->date time-utc->julian-day time-utc->modified-julian-day
   time-utc->time-monotonic time-utc->time-monotonic!
   time-utc->time-tai time-utc->time-tai! date->string string->date))

(defpackage "https://github.com/g000001/srfi-19#internals"
  (:use "https://github.com/g000001/srfi-19"
        cl
        fiveam
        srfi-9
        srfi-8
        srfi-6
        mbe)
  (:shadow lambda map member assoc loop time
           peek-char read-char)
  (:shadowing-import-from srfi-23 error))

;;; *EOF*
