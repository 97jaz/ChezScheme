;; Immutable dictionaries based on Okasaki and Gill's
;; "Fast Mergeable Integer Maps" (1998), with an added
;; collision node.
;;
;; This implementation is based partly on the paper and
;; partly on Leijen and Palamarchuk's Haskell implementation
;; of Data.IntMap.

;; This module is meant as a layer on top of which to build more usable abstractions.
(module dict
 (dict?
  empty-dict
  dict-empty?
  dict-count
  dict-ref
  dict-set
  dict-remove
  dict-merge

  ;; internals
  $branch? make-$branch $branch-prefix $branch-mask $branch-left $branch-right
  $leaf? $leaf-hash
  $single? make-$single $single-key $single-val
  $collision? make-$collision $collision-pairs
  $empty?)

 ;; record types

 (define-record-type $dict
   [nongenerative #{$dict pfv8jm0fznpju1uw30h5qd4dd-0}])

 (define-record-type $branch
   [parent $dict]
   [fields count prefix mask left right]
   [nongenerative #{$branch pfv8jpsat5jrk6vq7vclc3ntg-0}]
   [sealed #t])

 (define-record-type $leaf
   [parent $dict]
   [fields hash]
   [nongenerative #{$leaf pfv8jq2dzw50ox4f6vqm1ff5v-0}])

 (define-record-type $single
   [parent $leaf]
   [fields key val]
   [nongenerative #{$single pfv8jtevshstdt2dy2gd30140-0}]
   [sealed #t])

 (define-record-type $collision
   [parent $leaf]
   [fields pairs]
   [nongenerative #{$collision pfv8juoyx9e2hla2x2ufscuhj-0}]
   [sealed #t])

 (define-record-type $empty
   [parent $dict]
   [nongenerative #{$empty pfwk1nal7cs5dornqtzvda91m-0}]
   [sealed #t])

 ;; constants

 (define empty-dict (make-$empty))
 (define *nothing* (gensym))

 ;; predicate

 (define dict? $dict?)

 ;; count & empty

 (define (dict-count d)
   (cond [($branch? d) ($branch-count d)]
         [($single? d) 1]
         [($empty? d) 0]
         [else (length ($collision-pairs d))]))

 (define dict-empty? $empty?)

 ;; ref

 (define (dict-ref d key= hash key default)
   (cond [($branch? d)
          (if (fx<= hash ($branch-prefix d))
              (dict-ref ($branch-left d) key= hash key default)
              (dict-ref ($branch-right d) key= hash key default))]

         [($single? d)
          (if (key= key ($single-key d))
              ($single-val d)
              default)]

         [($empty? d)
          default]

         [else ; collision
          (let ([p (assp (lambda (k) (key= key k))
                         ($collision-pairs d))])
            (if p
                (cdr p)
                default))]))

 ;; set

 (define (dict-set d key= hash key val)
   (cond
    [($branch? d)
     (let ([p ($branch-prefix d)]
           [m ($branch-mask d)])
       (cond
        [(nomatch? hash p m)
         (join hash (make-$single hash key val) p d)]
        [(fx<= hash p)
         (br p m (dict-set ($branch-left d) key= hash key val) ($branch-right d))]
        [else
         (br p m ($branch-left d) (dict-set ($branch-right d) key= hash key val))]))]

    [($single? d)
     (let ([h ($leaf-hash d)])
       (cond
        [(not (fx= hash h))
         (join hash (make-$single hash key val) h d)]
        [(key= key ($single-key d))
         (if (eq? val ($single-val d))
             d
             (make-$single hash key val))]
        [else
         (make-$collision
          hash
          (list (cons key val)
                (cons ($single-key d) ($single-val d))))]))]

    [($empty? d)
     (make-$single hash key val)]

    [else ; collision
     (let ([h ($leaf-hash d)])
       (cond
        [(fx= hash h)
         (make-$collision
          hash
          (cons (cons key val)
                (remp (lambda (p) (key= key (car p)))
                      ($collision-pairs d))))]
        [else
         (join hash (make-$single hash key val) h d)]))]))

 ;; remove

 (define (dict-remove d key= hash key)
   (cond
    [($branch? d)
     (let ([p ($branch-prefix d)]
           [m ($branch-mask d)])
       (cond
        [(nomatch? hash p m)
         d]
        [(fx<= hash p)
         (br* p m (dict-remove ($branch-left d) key= hash key) ($branch-right d))]
        [else
         (br* p m ($branch-left d) (dict-remove ($branch-right d) key= hash key))]))]

    [($single? d)
     (if (key= key ($single-key d))
         empty-dict
         d)]

    [($empty? d)
     empty-dict]

    [else ; collision
     (cond
      [(fx= hash ($leaf-hash d))
       (let ([pairs (remp (lambda (p) (key= key (car p)))
                          ($collision-pairs d))])
         (if (null? (cdr pairs))
             (make-$single hash (caar pairs) (cdar pairs))
             (make-$collision hash pairs)))]
      [else
       d])]))

 ;; set and remove utilities

 (define (br p m l r)
   (let ([c (fx+ (dict-count l) (dict-count r))])
     (make-$branch c p m l r)))

 (define (br* p m l r)
   (cond [($empty? r) l]
         [($empty? l) r]
         [else (br p m l r)]))

 (define (join p0 d0 p1 d1)
   (let ([m (branching-bit p0 p1)])
     (if (fx<= p0 p1)
         (br (mask p0 m) m d0 d1)
         (br (mask p0 m) m d1 d0))))

 (define (join* p1 d1 p2 d2)
   (cond
    [($empty? d1) d2]
    [($empty? d2) d1]
    [else (join p1 d1 p2 d2)]))

 (define (branching-bit p m)
   (highest-set-bit (fxxor p m)))

 (define (mask h m)
   (fxand (fxior h (fx1- m)) (fxnot m)))

 (define (highest-set-bit x1)
   (let* ([x2 (fxior x1 (fxsrl x1 1))]
          [x3 (fxior x2 (fxsrl x2 2))]
          [x4 (fxior x3 (fxsrl x3 4))]
          [x5 (fxior x4 (fxsrl x4 8))]
          [x6 (fxior x5 (fxsrl x5 16))]
          [x7 (fxior x6 (fxsrl x6 32))])
     (fxxor x7 (fxsrl x7 1))))

 (define (nomatch? h p m)
   (not (fx= (mask h m) p)))

 ;; merge

 (define (dict-merge key= bin f id g1 g2 d1 d2)
   (define-syntax go
     (syntax-rules ()
       [(_ d1 d2) (dict-merge key= bin f id g1 g2 d1 d2)]))

   (cond
    [(eq? d1 d2) (id d1)]

    [($branch? d1)
     (cond
      [($branch? d2)
       (let-branch
        ([(p1 m1 l1 r1) d1] [(p2 m2 l2 r2) d2])
        (cond
         [(fx> m1 m2) (cond
                       [(nomatch? p2 p1 m1) (join* p1 (g1 d1) p2 (g2 d2))]
                       [(fx<= p2 p1)        (bin p1 m1 (go l1 d2) (g1 r1))]
                       [else                (bin p1 m1 (g1 l1) (go r1 d2))])]
         [(fx> m2 m1) (cond
                       [(nomatch? p1 p2 m2) (join* p1 (g1 d1) p2 (g2 d2))]
                       [(fx<= p1 p2)        (bin p2 m2 (go d1 l2) (g2 r2))]
                       [else                (bin p2 m2 (g2 l2) (go d1 r2))])]
         [(fx= p1 p2) (bin p1 m1 (go l1 l2) (go r1 r2))]
         [else        (join* p1 (g1 d1) p2 (g2 d2))]))]

      [($leaf? d2)
       (let ([h2 ($leaf-hash d2)])
         (let merge0 ([d1 d1])
           (cond
            [(eq? d1 d2)
             (id d1)]

            [($branch? d1)
             (let-branch
              ([(p1 m1 l1 r1) d1])
              (cond [(nomatch? h2 p1 m1) (join* p1 (g1 d1) h2 (g2 d2))]
                    [(fx<= h2 p1)        (bin p1 m1 (merge0 l1) (g1 r1))]
                    [else                (bin p1 m1 (g1 l1) (merge0 r1))]))]

            [($leaf? d1)
             (let ([h1 ($leaf-hash d1)])
               (cond [(fx= h1 h2) (merge/collision key= h1 f g1 g2 d1 d2)]
                     [else        (join* h1 (g1 d1) h2 (g2 d2))]))]

            [else ; ($empty? d1)
             (g2 d2)])))]

      [else ;; ($empty? d2)
       (g1 d1)])]

    [($leaf? d1)
     (let ([h1 ($leaf-hash d1)])
       (let merge0 ([d2 d2])
         (cond
          [(eq? d1 d2)
           (id d1)]

          [($branch? d2)
           (let-branch
            ([(p2 m2 l2 r2) d2])
            (cond [(nomatch? h1 p2 m2) (join* h1 (g1 d1) p2 (g2 d2))]
                  [(fx<= h1 p2)        (bin p2 m2 (merge0 l2) (g2 r2))]
                  [else                (bin p2 m2 (g2 l2) (merge0 r2))]))]

          [($leaf? d2)
           (let ([h2 ($leaf-hash d2)])
             (cond [(fx= h1 h2) (merge/collision key= h1 f g1 g2 d1 d2)]
                   [else        (join* h1 (g1 d1) h2 (g2 d2))]))]

          [else ; ($empty? d2)
           (g1 d1)])))]

    [else ; ($empty? d1)
     (g2 d2)]))

 ;; d1 and d2 are both $leaf? and have the same hash code = h
 (define (merge/collision key= h f g1 g2 d1 d2)
   (cond
    [(and ($single? d1) ($single? d2))
     (merge-singles key= h f g1 g2 d1 d2)]
    [else
     (let loop ([in-both '()] [in-l '()] [in-r (leaf->pairs d2)] [xs (leaf->pairs d1)])
       (cond
        [(null? xs)
         (let* ([l (g1 (pairs->leaf h in-l))]
                [r (g2 (pairs->leaf h in-r))]
                [pairs (append in-both (leaf->pairs l) (leaf->pairs r))])
           (pairs->leaf h pairs))]
        [else
         (let*-values ([(x) (car xs)]
                       [(y* ys) (partition (lambda (y) (key= (car x) (car y))) in-r)])
           (cond [(null? y*)
                  (loop in-both (cons x in-l) ys (cdr xs))]
                 [else
                  (let ([z (f (car x) (cdr x) (cdar y*) *nothing*)])
                    (if (eq? z *nothing*)
                        (loop in-both in-l ys (cdr xs))
                        (loop (cons (cons (car x) z) in-both) in-l ys (cdr xs))))]))]))]))

 (define (merge-singles key= h f g1 g2 d1 d2)
   (let ([k1 ($single-key d1)]
         [v1 ($single-val d1)]
         [k2 ($single-key d2)]
         [v2 ($single-val d2)])
     (cond [(key= k1 k2)
            (let ([x (f k1 v1 v2 *nothing*)])
              (cond [(eq? x *nothing*) empty-dict]
                    [(eq? x v1)        d1]
                    [(eq? x v2)        d2]
                    [else              (make-$single h k1 x)]))]
           [else
            (let ([s1 (g1 d1)]
                  [s2 (g2 d2)])
              (cond [($empty? s1) s2]
                    [($empty? s2) s1]
                    [else
                     (make-$collision
                      h
                      (list (cons k1 ($single-val s1))
                            (cons k2 ($single-val s2))))]))])))

 (define (leaf->pairs d)
   (cond [($single? d)    (list (cons ($single-key d) ($single-val d)))]
         [($collision? d) ($collision-pairs d)]
         [else            '()]))

 (define (pairs->leaf h xs)
   (cond [(null? xs)       empty-dict]
         [(null? (cdr xs)) (make-$single h (caar xs) (cdar xs))]
         [else             (make-$collision h xs)]))

 (define-syntax let-branch
   (syntax-rules ()
     [(_ ([(p m l r) d] ...) exp ...)
      (let ([p ($branch-prefix d)] ...
            [m ($branch-mask d)] ...
            [l ($branch-left d)] ...
            [r ($branch-right d)] ...)
        exp ...)])))
