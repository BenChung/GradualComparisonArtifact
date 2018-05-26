#lang racket
(module u racket
(define Fp% (class object%
(super-new)
(define/public (n x) (send this m x))))
(provide Fp%))
(module t typed/racket
(require/typed (submod ".." u) [Fp% (Class [n (-> Any Any)])])
(define-type C (Instance (Class (m (-> C C)))))
(define-type E (Instance (Class (m (-> D D)))))
(define-type D (Instance (Class (n (-> D D)))))
(define F% (class Fp%
(super-new)
(: m (-> E E))
(define/public (m x) x)))
(define C% (class object%
(super-new)
(: n (-> C C))
(define/public (n x) x)))
(provide F% C%))
(require 't)
(send (send (new F%) n (new C%)) m (new C%))