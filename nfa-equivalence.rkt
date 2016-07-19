#lang racket
(require racket/set)
(require racket/hash)
(require data/queue)

(define NFA-equivalence
  (lambda (A S o t x y algo)
    (letrec
        [
         (HKC-testing ;通过求lst-of-set中的关系的并集的c等价类的最大元素来检查 X c(R) Y
          (lambda (lst-of-set xy)
            (letrec
                [
                 (x (set-copy (car xy)))
                 (y (set-copy (cadr xy)))
                 
                 (normalize
                  (lambda (x)
                    (begin
                      (for ([st (in-list lst-of-set)])
                           (for ([crt (in-set st)])
                                (let ([ss1 (subset? (car crt) x)]
                                      [ss2 (subset? (cadr crt) x)])
                                  (cond [(and ss1 (not ss2)) (set-union! x (cadr crt))]
                                        [(and ss2 (not ss1)) (set-union! x (car crt))]))))
                      x)))
                 ]
              (set=? (normalize x) (normalize y)))))
         
         (todo (mutable-set))
         (R (mutable-set))
         (new-sim '())
         (testing (cond [(eq? algo 'HKC) (lambda (x)
                                           (HKC-testing (list R todo) x))]
                        [(eq? algo 'HKC-sim) (set! new-sim
                                                   (new-similarity S (similarity A S o t)))
                                             (lambda (x)
                                               (HKC-testing (list R todo new-sim) x))]
                        [(eq? algo 'Naive) (lambda (x) (set-member? R x))]))
         (iter 
          (lambda ()
            (cond ((set-empty? todo) #t) ;todo已空，结束
                  (else
                   (let ([xy (set-first todo)])
                     (set-remove! todo xy)
                     (cond [(testing xy) ;testing即判定是否跳过(x, y)的函数，更换testing即得到不同算法。
                            (iter)] ;(x, y) in R
                           [(not (eq? (output-func (car xy)) 
                                      (output-func (cadr xy)))) 
                            #f] ;o(x) != o(y)，结束
                           [else
                            (set-add! R xy)
                            (update-todo xy A) ;update todo and R
                            (iter)])))))) 
         (output-func
          (lambda (x)
            (> 
             (for/fold ([ans 0])
                       ([item (in-set x)])
               (+ (hash-ref o item) ans)) 
             0)))
         
         (update-todo
          (lambda (xy A)
            (for ([a (in-list A)])
                 (let ([taxy (transform-sets xy a)])
                   (cond [(not (set-member? R taxy))
                          (set-add! todo taxy)])))
            ))
         
         (transform-sets
          (lambda (xy a)
            (list (transform-set (car xy) a) (transform-set (cadr xy) a)))) ;(x, y)走一步a后到达的集合(x', y')
         
         (transform-set
          (lambda (X a)
            (let ([ret (mutable-set)])
              (for ([item (in-set X)])
                   (set-union! ret 
                               (cond [(and (hash-has-key? t item)
                                           (hash-has-key? (hash-ref t item) a)) 
                                      (hash-ref (hash-ref t item) a)]
                                     [else (set)])))
              ret)))
         ]
      (set-add! todo (list x y))
      (iter)
      )))

(define similarity
  (lambda (A S o t)
    (letrec
        [
         (rt (make-hash)) ;反向图
         (reverse-graph
          (lambda ()
            (rg-iter (hash-iterate-first t))))
         (rg-iter ;为原图的每个src构建反向图
          (lambda (t-iter)
            (cond [(eq? t-iter #f) rt]
                  [else (begin
                          (rg-iter-iter-etr (hash-iterate-pair t t-iter))
                          (rg-iter (hash-iterate-next t t-iter)))])))
         (rg-iter-iter-etr ;为原图的每个src对应的每个a构建反向图
          (lambda (crt-pair)
            (let ([crt-dst (car crt-pair)]
                  [crt-src-hash (cdr crt-pair)])
              (rg-iter-iter (hash-iterate-first crt-src-hash) crt-src-hash crt-dst))))
         (rg-iter-iter ;为某个src的某个a构建反向图
          (lambda (crt-hash-pos crt-src-hash dst)
            (cond [(eq? crt-hash-pos #f)]
                  [else
                   (let ([a (hash-iterate-key crt-src-hash crt-hash-pos)] ;当前的a
                         [src-set (hash-iterate-value crt-src-hash crt-hash-pos)]) ;原图src对应的dst集合，新图的src集合
                     (for ([src (in-set src-set)])
                          (nfa-add-edge rt src dst a))
                     (rg-iter-iter (hash-iterate-next crt-src-hash crt-hash-pos) crt-src-hash dst))])))
         (nfa-add-edge
          (lambda (t src dst a)
            (cond [(hash-has-key? t src)
                   (cond [(hash-has-key? (hash-ref t src) a)
                          (let* ([src-hash (hash-ref t src)]
                                 [dst-set (hash-ref src-hash a)])
                            (set-add! dst-set dst))]
                         [else
                          (let ([src-hash (hash-ref t src)])
                            (hash-set! src-hash a (mutable-set dst)))
                          ])]
                  [else
                   (hash-set! t src (make-hash (list (cons a (mutable-set dst)))))])))
         
         (s-kernel-iter-a ;确定原图每个点关于某个a的similarity集合
          (lambda (a)
            (letrec (
                     (init-sim ;返回初始化的sim集合
                      (lambda ()
                        (let ([ret (make-hash)])
                          (for ([u (in-set S)])
                               (let ([rett (mutable-set)])
                                 (cond
                                   [(not (and (hash-has-key? t u) (hash-has-key? (hash-ref t u) a))) ;如果一个点没有出边，sim初始化为o一样的点集
                                    (for ([v (in-set S)])
                                         (cond [(eq? (hash-ref o u) (hash-ref o v))
                                                (set-add! rett v)]))]
                                   [else
                                    (for ([v (in-set S)])
                                         (cond [(and ;如果一个点有出边，sim初始化为o一样并且有出边的集合
                                                 (eq? (hash-ref o u) (hash-ref o v))
                                                 (hash-has-key? t v)
                                                 (hash-has-key? (hash-ref t v) a))
                                                (set-add! rett v)]))])
                                 (hash-set! ret u rett)))
                          ret)))
                     (transform-set
                      (lambda (t X)
                        (cond [(not (eq? (set-count X) 1)) ;点数大于1的集合
                               (let ([ret (mutable-set)])
                                 (for ([item (in-set X)])
                                      (set-union! ret 
                                                  (cond [(and (hash-has-key? t item)
                                                              (hash-has-key? (hash-ref t item) a)) 
                                                         (hash-ref (hash-ref t item) a)]
                                                        [else (set)])))
                                 ret)]
                              [else ;只有一个点的集合
                               (let ([item (set-first X)])
                                 (cond [(and (hash-has-key? t item)
                                             (hash-has-key? (hash-ref t item) a)) 
                                        (hash-ref (hash-ref t item) a)]
                                       [else (mutable-set)]))])))
                     (init-remove ;remove集合初始化为pre(S)-pre(sim(v))
                      (lambda (sim q inq?)
                        (let ([ret (make-hash)])
                          (for ([u (in-set S)])
                               (hash-set! ret
                                          u
                                          (let ([tmp (set-copy (transform-set rt S))])
                                            (set-subtract! tmp (transform-set rt (hash-ref sim u)))
                                            tmp))
                               (cond [(not (set-empty? (hash-ref ret u))) ;remove非空的集合进入更新队列
                                      (enqueue! q u)
                                      (hash-set! inq? u #t)]))
                          ret)))
                     (init-count ;用来统计post(ww)交sim(u)的集合大小
                      (lambda (sim)
                        (let ([ret (make-hash)])
                          (for ([u (in-set S)])
                               (let ([rett (make-hash)])
                                 (for ([v (in-set S)])
                                      (hash-set! rett v (set-count (set-intersect (transform-set t (set u)) (hash-ref sim v)))))
                                 (hash-set! ret u rett)))
                          ret)))
                     
                     (s-kernel-iter ;paper中的while循环
                      (lambda (sim remove count q inq?)
                        (cond [(queue-empty? q) sim]
                              [else
                               (let* ([v (dequeue! q)]
                                      [pre-v (transform-set rt (set v))]
                                      [remove-v (hash-ref remove v)])
                                 (hash-set! inq? v #f)
                                 (for ([u (in-set pre-v)])
                                      (for ([w (in-set remove-v)])
                                           (cond [(set-member? (hash-ref remove u) w)
                                                  (set-remove! (hash-ref sim u) w)
                                                  (for ([ww (in-set (transform-set rt (set w)))])
                                                       (let ([wwu (hash-ref (hash-ref count ww) u)])
                                                         (cond [(eq? 0 wwu)
                                                                (set-add! (hash-ref remove u) ww)]
                                                               [else (hash-set! (hash-ref count ww) u (- wwu 1))])))
                                                  (cond [(and
                                                          (not (eq? (set-count (hash-ref remove u)) 0))
                                                          (not (hash-ref inq? u)))
                                                         (enqueue! q u)
                                                         (hash-set! inq? u #t)])])))
                                 (hash-set! remove v (mutable-set))
                                 
                                 (s-kernel-iter sim remove count q inq?))])))
                     )
              
              (let* ([sim (init-sim)]
                     [q (make-queue)]
                     [inq? (make-hash)]
                     [remove (init-remove sim q inq?)]
                     [count (init-count sim)])
                (s-kernel-iter sim remove count q inq?)))))
         
         (s-kernel
          (lambda ()
            (let ([ret
                   (let ([tmp (make-hash)])
                     (for ([u (in-set S)])
                          (hash-set! tmp u (set-copy S)))
                     tmp)])
              (for ([a (in-list A)])
                   (let ([tmpres (s-kernel-iter-a a)])
                     (for ([u (in-set S)])
                          (set-intersect! (hash-ref ret u) (hash-ref tmpres u)))))
              ret)))
         ]
      (reverse-graph)
      (s-kernel))))

(define new-similarity
  (lambda (S sim)
    (let ([ret (mutable-set)])
      (for ([x (in-set S)])
           (for ([y (in-set (hash-ref sim x))])
                (set-add! ret (list (mutable-set x y) (mutable-set y)))))
      ret)))

;三种算法的接口
(define Naive
  (lambda (A S o t x y)
    (NFA-equivalence A S o t x y 'Naive)))

(define HKC
  (lambda (A S o t x y)
    (NFA-equivalence A S o t x y 'HKC)))

(define HKC-sim
  (lambda (A S o t x y)
    (NFA-equivalence A S o t x y 'HKC-sim)))


;;;下面是文件IO和测试
(define-syntax while
  (syntax-rules ()
    [(while test act ...)
     (letrec (
              (iter
               (lambda (ret)
                 (cond [test (iter (begin act ...))]
                       [else ret])))
              )
       (cond [test (iter (begin act ...))]
             [else (void)]))]))
(define read-nfa-from-file
  (lambda (filename)
    (letrec
        [
         (sA 0)
         (sS 0)
         (st 0)
         (sx 0)
         (sy 0)
         (A '())
         (S (mutable-set))
         (o (make-hash))
         (t (make-hash))
         (x (mutable-set))
         (y (mutable-set))
         (inport (open-input-file filename))
         (rn (lambda () (read inport)))


         (nfa-add-edge
          (lambda (t src dst a)
            (cond [(hash-has-key? t src)
                   (cond [(hash-has-key? (hash-ref t src) a)
                          (let* ([src-hash (hash-ref t src)]
                                 [dst-set (hash-ref src-hash a)])
                            (set-add! dst-set dst))]
                         [else
                          (let ([src-hash (hash-ref t src)])
                            (hash-set! src-hash a (mutable-set dst)))
                          ])]
                  [else
                   (hash-set! t src (make-hash (list (cons a (mutable-set dst)))))])))
         ]
      (set! sA (rn))
      (set! sS (rn))
      (set! st (rn))
      (set! sx (rn))
      (set! sy (rn))
      (let ([n 0])
        (while (< n sA)
               (set! A (cons (rn) A))
               (set! n (+ n 1))))
      (let ([n 0]
            [s-hash (make-hash)])
        (while (< n sS)
               (hash-set! s-hash n (rn))
               (set! n (+ n 1)))
        (set! n 0)
        (while (< n sS)
               (hash-set! o (hash-ref s-hash n) (rn))
               (set! n (+ n 1))))
      (let ([n 0])
        (while (< n sx)
               (set-add! x (rn))
               (set! n (+ n 1)))
        (set! n 0)
        (while (< n sy)
               (set-add! y (rn))
               (set! n (+ n 1))))
      (let ([n 0])
        (while (< n st)
               (nfa-add-edge t (rn) (rn) (rn))
               (set! n (+ n 1))))
      (close-input-port inport)
      (list A S o t x y)
      
      )))

(define nfa-eq-from-file
  (lambda (filename)
    (let* ([nfa (read-nfa-from-file filename)]
           [res (HKC-sim (list-ref nfa 0)
                         (list-ref nfa 1)
                         (list-ref nfa 2)
                         (list-ref nfa 3)
                         (list-ref nfa 4)
                         (list-ref nfa 5))])
      res)))

(define main
  (lambda ()
    (let* ([infilename (vector-ref (current-command-line-arguments) 0)]
           [res (nfa-eq-from-file infilename)])
      (cond [res (displayln "true")]
            [else (displayln "false")]))))
;(main)

;;;下面是测试
(define testing
  (lambda ()
    (define _A '(1))
    (define _o (hash 1 0 2 1 3 0 4 0 5 1 6 0))
    (define _t (hash 1 (hash 1 (set 2)) 2 (hash 1 (set 3)) 3 (hash 1 (set 2))
                     4 (hash 1 (set 5)) 5 (hash 1 (set 6)) 6 (hash 1 (set 5)))
      )
    (define _S (set 1 2 3 4 5 6))
    (define _x (mutable-set 1))
    (define _y (mutable-set 4))
    
    
    (define _AA '(1 2))
    (define _oo (hash 1 0 2 1 3 1 4 0 5 1 6 1))
    (define _tt (hash 1 (hash 1 (set 2) 2 (set 2)) 2 (hash 1 (set 3) 2 (set 3)) 3 (hash 1 (set 3) 2 (set 3))
                      4 (hash 1 (set 5) 2 (set 6)) 5 (hash 1 (set 6) 2 (set 6)) 6 (hash 1 (set 5) 2 (set 5)))
      )
    (define _SS (mutable-set 1 2 3 4 5 6))
    (define _xx (set 1))
    (define _yy (set 4))
    
    (define _A3 '(1))
    (define _o3 (hash 1 1 2 1 3 0 4 1))
    (define _t3 (hash 1 (hash 1 (set 2 3))
                      2 (hash 1 (set 1))
                      3 (hash 1 (set 2))
                      4 (hash 1 (set 4))))
    (define _S3 (mutable-set 1 2 3 4))


    (let ([st (current-process-milliseconds)])
    (displayln (HKC-sim _A _S _o _t _x _y))
    (displayln (HKC-sim _AA _SS _oo _tt _xx _yy))
    (displayln (HKC-sim _A3 _S3 _o3 _t3 (mutable-set 1) (mutable-set 4)))
      (displayln (- (current-process-milliseconds) st)))
      
    ;(nfa-eq-from-file "input.txt")
    ))

(testing)