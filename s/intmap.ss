;; Immutable maps represented as big-endian Patricia tries.
;; Based on Okasaki & Gill's "Fast Mergeable Integer Maps,"
;; (1998) with an added collision node.
;;
;; I also consulted Leijen and Palamarchuk's Haskell implementation
;; of Data.IntMap.

(module
 ($intmap-empty
  $intmap-empty?
  $intmap-count
  $intmap-ref
  $intmap-set
  $intmap-remove
  $intmap-has-key?
  $intmap-fold
  $intmap-merge)

 (define-record-type Br
   [fields (immutable count)
           (immutable prefix)
           (immutable mask)
           (immutable left)
           (immutable right)]
   [nongenerative #{Br pfwguidjcvqbvofiirp097jco-1}]
   [sealed #t])

 (define-record-type Leaf
   [fields (immutable hash)]
   [nongenerative #{Leaf pfwguidjcvqbvofiirp097jco-2}])

 (define-record-type Lf
   [parent Leaf]
   [fields (immutable key)
           (immutable value)]
   [nongenerative #{Lf pfwguidjcvqbvofiirp097jco-3}]
   [sealed #t])

 (define-record-type Co
   [parent Leaf]
   [fields (immutable pairs)]
   [nongenerative #{Co pfwguidjcvqbvofiirp097jco-4}]
   [sealed #t])

 (define *nothing* (gensym))

 (define $intmap-empty #f)

 (define ($intmap-count t)
   (cond [(Br? t) (Br-count t)]
         [(Lf? t) 1]
         [(Co? t) (length (Co-pairs t))]
         [else 0]))

 (define ($intmap-empty? t)
   (fx= 0 ($intmap-count t)))

 (define ($intmap-ref t key key->hash key= def)
   ($intmap-ref* t key (key->hash key) key= def))

 (define ($intmap-ref* t key h key= def)
   (cond
    [(Br? t)
     (if (fx<= h (Br-prefix t))
         ($intmap-ref* (Br-left t) key h key= def)
         ($intmap-ref* (Br-right t) key h key= def))]

    [(Lf? t)
     (if (key= key (Lf-key t))
         (Lf-value t)
         def)]

    [(Co? t)
     (if (fx= h (Leaf-hash t))
         ($collision-ref key= t key def)
         def)]

    [else
     def]))

 (define ($intmap-has-key? t key key->hash key=)
   (not (eq? *nothing* ($intmap-ref t key key->hash key= *nothing*))))

 (define ($intmap-set t key key->hash key= val)
   ($intmap-set* t key (key->hash key) key= val))

 (define ($intmap-set* t key h key= val)
   (cond
    [(Br? t)
     (let ([p (Br-prefix t)]
           [m (Br-mask t)])
       (cond
        [(not (match-prefix? h p m))
         (join h (make-Lf h key val) p t)]
        [(fx<= h p)
         (br p m ($intmap-set* (Br-left t) key h key= val) (Br-right t))]
        [else
         (br p m (Br-left t) ($intmap-set* (Br-right t) key h key= val))]))]

    [(Lf? t)
     (let ([j (Leaf-hash t)])
       (cond
        [(not (fx= h j))
         (join h (make-Lf h key val) j t)]
        [(key= key (Lf-key t))
         (let ([orig-val (Lf-value t)])
           (if (eq? val orig-val)
               t
               (make-Lf h key val)))]
        [else
         (make-Co h (list (cons key val) (cons (Lf-key t) (Lf-value t))))]))]

    [(Co? t)
     (let ([j (Leaf-hash t)])
       (if (fx= h j)
           (make-Co j ($collision-set key= t key val))
           (join h (make-Lf h key val) j t)))]

    [else
     (make-Lf h key val)]))

 (define (join p0 t0 p1 t1)
   (let ([m (branching-bit p0 p1)])
     (if (fx<= p0 p1)
         (br (mask p0 m) m t0 t1)
         (br (mask p0 m) m t1 t0))))

 (define ($intmap-remove t key key->hash key=)
   ($intmap-remove* t key (key->hash key) key=))

 (define ($intmap-remove* t key h key=)
   (cond
    [(Br? t)
     (let ([p (Br-prefix t)]
           [m (Br-mask t)])
       (cond
        [(not (match-prefix? h p m))
         t]
        [(fx<= h p)
         (br/check-left p m ($intmap-remove* (Br-left t) key h key=) (Br-right t))]
        [else
         (br/check-right p m (Br-left t) ($intmap-remove* (Br-right t) key h key=))]))]

    [(Lf? t)
     (if (key= key (Lf-key t))
         #f
         t)]

    [(Co? t)
     (cond
      [(fx=? h (Leaf-hash t))
       ;; A collision node always has at least 2 key-value pairs,
       ;; so when we remove one, we know the resulting list is non-empty.
       (let ([pairs ($collision-remove key= t key)])
         (if (null? (cdr pairs))
             (make-Lf h (caar pairs) (cdar pairs))
             (make-Co h pairs)))]
      [else
       t])]

    [else
     #f]))

 ;; collision ops
 (define ($collision-ref key= t key def)
   (let loop ([xs (Co-pairs t)])
     (cond [(null? xs) def]
           [(key= key (caar xs)) (cdar xs)]
           [else (loop (cdr xs))])))

 (define ($collision-set key= t key val)
   (cons (cons key val)
         (let loop ([xs (Co-pairs t)])
           (cond [(null? xs) '()]
                 [(key= key (caar xs)) (loop (cdr xs))]
                 [else (cons (car xs) (loop (cdr xs)))]))))

 (define ($collision-remove key= t key)
   (let loop ([xs (Co-pairs t)])
     (cond [(null? xs) '()]
           [(key= key (caar xs)) (loop (cdr xs))]
           [else (cons (car xs) (loop (cdr xs)))])))

 (define ($collision-has-key? key= t key)
   (let loop ([xs (Co-pairs t)])
     (cond [(null? xs) #f]
           [(key= key (caar xs)) #t]
           [else (loop (cdr xs))])))

 ;; bit twiddling
 (define-syntax define-syntax-rule
   (syntax-rules ()
     [(_ (name arg ...) e ...)
      (define-syntax name
        (syntax-rules ()
          [(_ arg ...) e ...]))]))

 (define-syntax-rule (match-prefix? h p m)
   (fx= (mask h m) p))

 (define-syntax-rule (mask h m)
   (fxand (fxior h (fx1- m)) (fxnot m)))

 (define-syntax-rule (branching-bit p m)
   (highest-set-bit (fxxor p m)))

 (define-syntax-rule (highest-set-bit x1)
   (let* ([x2 (fxior x1 (fxsrl x1 1))]
          [x3 (fxior x2 (fxsrl x2 2))]
          [x4 (fxior x3 (fxsrl x3 4))]
          [x5 (fxior x4 (fxsrl x4 8))]
          [x6 (fxior x5 (fxsrl x5 16))]
          [x7 (fxior x6 (fxsrl x6 32))])
     (fxxor x7 (fxsrl x7 1))))

 ;; basic utils
 (define (br p m l r)
   (let ([c (fx+ ($intmap-count l) ($intmap-count r))])
     (make-Br c p m l r)))

 (define (br* p m l r)
   (cond
    [(not r) l]
    [(not l) r]
    [else (br p m l r)]))

 (define (br/check-left p m l r)
   (if l
       (br p m l r)
       r))

 (define (br/check-right p m l r)
   (if r
       (br p m l r)
       l))

 (define ($intmap-enum t next)
   (cond
    [(Br? t)
     ($intmap-enum (Br-left t) (cons (Br-right t) next))]

    [(Lf? t)
     (cons (cons (Lf-key t) (Lf-value t)) next)]

    [(Co? t)
     (let ([pairs (Co-pairs t)])
       (let ([fst (car pairs)]
             [rst (cdr pairs)])
         (if (null? rst)
             (cons fst next)
             (cons fst (cons (make-Co #f rst) next)))))]

    [else
     next]))

 (define ($intmap-fold t nil proc)
   (let loop ([pos ($intmap-enum t #f)] [nil nil])
     (cond
      [pos
       (let ([p (car pos)]
             [next (cdr pos)])
         (loop (and next ($intmap-enum (car next) (cdr next)))
               (proc (car p) (cdr p) nil)))]
      [else
       nil])))

 ;; merge
 ;; based on https://hackage.haskell.org/package/containers-0.5.10.2/docs/src/Data.IntMap.Internal.html#mergeWithKey%27
 (define-syntax let-br
   (syntax-rules ()
     [(_ ([(p m l r) t] ...) exp ...)
      (let ([p (Br-prefix t)] ...
            [m (Br-mask t)] ...
            [l (Br-left t)] ...
            [r (Br-right t)] ...)
        exp ...)]))

 (define ($intmap-merge key= f id g1 g2 t1 t2)
   (merge/key key= br* f id g1 g2 t1 t2))

 (define (merge/key key= bin f id g1 g2 t1 t2)
   (define-syntax go
     (syntax-rules ()
       [(_ t1 t2) (merge/key key= bin f id g1 g2 t1 t2)]))

   (cond
    [(eq? t1 t2)
     (id t1)]

    [(Br? t1)
     (cond
      [(Br? t2)
       (let-br
        ([(p1 m1 l1 r1) t1] [(p2 m2 l2 r2) t2])
        (cond
         [(fx> m1 m2)
          (cond
           [(not (match-prefix? p2 p1 m1))
            (join* p1 (g1 t1) p2 (g2 t2))]
           [(fx<= p2 p1)
            (bin p1 m1 (go l1 t2) (g1 r1))]
           [else
            (bin p1 m1 (g1 l1) (go r1 t2))])]

         [(fx> m2 m1)
          (cond
           [(not (match-prefix? p1 p2 m2))
            (join* p1 (g1 t1) p2 (g2 t2))]
           [(fx<= p1 p2)
            (bin p2 m2 (go t1 l2) (g2 r2))]
           [else
            (bin p2 m2 (g2 l2) (go t1 r2))])]

         [(fx= p1 p2)
          (bin p1 m1 (go l1 l2) (go r1 r2))]

         [else
          (join* p1 (g1 t1) p2 (g2 t2))]))]

      [(Leaf? t2)
       (let merge0 ([t2 t2] [h2 (Leaf-hash t2)] [t1 t1])
         (cond
          [(eq? t1 t2)
           (id t1)]

          [(Br? t1)
           (let-br
            ([(p1 m1 l1 r1) t1])
            (cond
             [(not (match-prefix? h2 p1 m1))
              (join* p1 (g1 t1) h2 (g2 t2))]
             [(fx<= h2 p1)
              (bin p1 m1 (merge0 t2 h2 l1) (g1 r1))]
             [else
              (bin p1 m1 (g1 l1) (merge0 t2 h2 r1))]))]

          [(Leaf? t1)
           (let ([h1 (Leaf-hash t1)])
             (cond
              [(fx= h1 h2)
               (merge/collision key= f g1 g2 h1 t1 t2)]
              [else
               (join* h1 (g1 t1) h2 (g2 t2))]))]

          [else
           (g2 t2)]))]

      [else
       (g1 t1)])]

    [(Leaf? t1)
     (let merge0 ([t1 t1] [h1 (Leaf-hash t1)] [t2 t2])
       (cond
        [(eq? t1 t2)
         (id t1)]

        [(Br? t2)
         (let-br
          ([(p2 m2 l2 r2) t2])
          (cond
           [(not (match-prefix? h1 p2 m2))
            (join* h1 (g1 t1) p2 (g2 p2))]
           [(fx<= h1 p2)
            (bin p2 m2 (merge0 t1 h1 l2) (g2 r2))]
           [else
            (bin p2 m2 (g2 l2) (merge0 t1 h1 r2))]))]

        [(Leaf? t2)
         (let ([h2 (Leaf-hash t2)])
           (cond
            [(fx= h1 h2)
             (merge/collision key= f g1 g2 h1 t1 t2)]
            [else
             (join* h1 (g1 t1) h2 (g2 t2))]))]

        [else
         (g1 t2)]))]

    [else
     (g2 t2)]))

 (define (find+rest p? xs)
   (let loop ([r #f] [ys '()] [xs xs])
     (cond [(null? xs)    (values r ys)]
           [(p? (car xs)) (loop (car xs) ys (cdr xs))]
           [else          (loop r (cons (car xs) ys) (cdr xs))])))

 ;; pre: t1 and t2 satisfy `Leaf?` and have the same hash code
 (define (merge/collision key= f g1 g2 h t1 t2)
   (cond
    [(and (Lf? t1) (Lf? t2))
     (merge/lf-lf key= f g1 g2 h t1 t2)]
    [else
     ;; separate k-v pairs into
     ;; - those in both t1 and t2
     ;; - those in t1 only (left)
     ;; - those in t2 only (right)
     (let loop ([both '()] [left '()] [right (leaf->pairs t2)] [xs (leaf->pairs t1)])
       (cond
        [(null? xs)
         (let* ([l (g1 (pairs->leaf h left))]
                [r (g2 (pairs->leaf h right))]
                [pairs (append both (leaf->pairs l) (leaf->pairs r))])
           (pairs->leaf h pairs))]
        [else
         (let*-values
             ([(x)
               (car xs)]
              [(y ys)
               (find+rest (lambda (y)
                            (key= (car x) (car y)))
                          right)])
           (cond
            [y
             (let* ([k1 (car x)]
                    [z (f k1 (cdr x) (cdr y) *nothing*)])
               (cond
                [(eq? *nothing* z)
                 (loop both left ys (cdr xs))]
                [else
                 (loop (cons (cons k1 z) both) left ys (cdr xs))]))]
            [else
             (loop both (cons x left) ys (cdr xs))]))]))]))

 ;; pre: t1 and t2 are both `Lf?` with the same hash code
 (define (merge/lf-lf key= f g1 g2 h t1 t2)
   (let ([k1 (Lf-key t1)]
         [v1 (Lf-value t1)]
         [k2 (Lf-key t2)]
         [v2 (Lf-value t2)])
     (cond
      [(key= k1 k2)
       (let ([x (f k1 v1 v2 *nothing*)])
         (cond
          [(eq? *nothing* x) #f]
          [(eq? v1 x) t1]
          [(eq? v2 x) t2]
          [else (make-Lf h k1 x)]))]
      [else
       (let ([s1 (g1 t1)]
             [s2 (g2 t2)])
         ;; Since g1 and g2 are only permitted to return nodes with a subset of the keys
         ;; they were given, s1 and s2 must both be either Lf? or #f. But g1 and g2 are
         ;; allowed to modify values.
         (cond
          [(not s1) s2]
          [(not s2) s1]
          [else (make-Co h
                         (list (cons k1 (Lf-value s1))
                               (cons k2 (Lf-value s2))))]))])))

 (define (join* p1 t1 p2 t2)
   (cond
    [(not t1) t2]
    [(not t2) t1]
    [else (join p1 t1 p2 t2)]))

 (define (leaf->pairs t)
   (cond
    [(Lf? t) (list (cons (Lf-key t) (Lf-value t)))]
    [(Co? t) (Co-pairs t)]
    [(not t) '()]))

 (define (pairs->leaf h xs)
   (cond
    [(null? xs) #f]
    [(null? (cdr xs)) (make-Lf h (caar xs) (cdar xs))]
    [else (make-Co h xs)]))

 (define ($union key= t1 t2)
   (merge/key key=
              br
              (lambda (t) t)
              (lambda (k v1 v2 nil) v1)
              (lambda (t) t)
              (lambda (t) t)
              t1
              t2))

 (define ($intersection key= t1 t2)
   (merge/key key=
              br*
              (lambda (t) t)
              (lambda (k v1 v2 nil) v1)
              (lambda (t) #f)
              (lambda (t) #f)
              t1
              t2))

 (define ($difference key= t1 t2)
   (merge/key key=
              br*
              (lambda (t) #f)
              (lambda (k v1 v2 nil) nil)
              (lambda (t) t)
              (lambda (t) #f)
              t1
              t2)))
