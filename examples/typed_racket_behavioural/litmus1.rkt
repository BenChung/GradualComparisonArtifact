#lang racket
(module u racket
(define Tp% (class object%
(super-new)
(define/public (t x) (send this s x))))
(provide Tp%))
(module t typed/racket
(require/typed (submod ".." u) [Tp% (Class [t (-> Any Any)])])
(define-type A (Instance (Class (m (-> A A)))))
(define-type I (Instance (Class (n (-> I I)))))
(define-type T (Instance (Class (s (-> I T)))))
(define T% (class Tp%
(super-new)
(: s (-> I T))
(define/public (s x) this)))
(define A% (class object%
(super-new)
(: m (-> A A))
(define/public (m x) this)))
(provide T% A%))
(require 't)
(send (new T%) t (new A%))