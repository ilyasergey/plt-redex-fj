#lang racket

#|

This file contains a simple implementation of the Featherweight Java language,
as described in Benjamin C. Pierce's 
"Types and Programming Languages", Chapter 19
  
|#


(require redex)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FJ Syntax
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-language FJ
  
  ; Class declarations
  (CL (class C extends C ((C f) ...) K M ...))
  
  ; Constructor declarations
  (K (C ((C f) ...) (super f ...) (f f) ...))
  
  ; Method declarations
  (M (C m ((C x) ...) t))
  
  ; Terms
  (t x 
     (lkp t f) 
     (call t m t ...) 
     (new C t ...) 
     (cast C t))
  
  ; Values
  (v (new C v ...))
  
  ; Class table
  (CT (CL ...))
  
  ; Evaluation contexts
  (E hole 
     (lkp E f) 
     (call E m t ...)
     (call v m v ... E t ...)
     (new C v ... E t ...)
     (cast C E))
     
  ; Typing environments
  (Γ ((x C) ...))
  
  (Bool #t #f)     
  
  ; Field names
  (f variable-not-otherwise-mentioned)
  ; Local variables and method parameters
  (x variable-not-otherwise-mentioned)
  ; Method names
  (m variable-not-otherwise-mentioned)
  ; Class names
  (B variable-not-otherwise-mentioned)
  (C variable-not-otherwise-mentioned)
  (D variable-not-otherwise-mentioned))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Subtyping
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
The subptying rule is different from the one that is in TAPL.

We defined it in the way so it would be algorithmic, avoiding
choosing a "middle-man" non-deterministically in the case of 
the transitivity rule, so the latter one is not present 
anymore.

|#

(define-judgment-form FJ
  #:mode (<: I I I) 
  #:contract (<: CT C C)
  [----------
   (<: CT C C)]
  
  [(where (class C extends D any ...) (class-lookup CT C))
   (<: CT D D_1)   
   ---------------
   (<: CT C D_1)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary meta-functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Class lookup by name from the class table
(define-metafunction FJ
  class-lookup : CT C -> any
  
  [(class-lookup ((class C any ...) CL_1 ...) C) 
   (class C any ...)]  
  [(class-lookup (CL_0 CL_1 ...) C) 
   (class-lookup (CL_1 ...) C)]
  [(class-lookup () C) #f])

;; Fields lookup
(define-metafunction FJ
  fields : CT C -> ((C f) ...)
  
  [(fields CT Object) ()]
  [(fields CT C)
   ((C_2 f_2) ... (D_3 f_3) ...)
   (where (class C extends D ((C_2 f_2) ...) any ...) 
          (class-lookup CT C))
   (where ((D_3 f_3) ...)
          (fields CT D))])

;; Method type lookup 
(define-metafunction FJ
  mtype : CT m C -> any
  ; m is defined in C
  [(mtype CT m C)
   ; Map parameter entries to types (i.e., take car)
   ((B_1 ...) B)
   (where (class C extends D ((C_2 f_2) ...) K M ...)
          (class-lookup CT C))
   (where (B m ((B_1 x) ...) t)
          (method-in m M ...))]
  ; m is not defined in C
  [(mtype CT m C)
   (mtype CT m D)
   (where (class C extends D ((C_2 f_2) ...) K M ...)
          (class-lookup CT C))
   (where #f (method-in m M ...))]
  ; m is undefined: we hit Object
  [(mtype CT m Object) #f])

;; Method body lookup 
(define-metafunction FJ
  mbody : CT m C -> ((x ...) t)
  ; m is defined in C
  [(mbody CT m C)
   ; Map parameter entries to parameter names (i.e., take cadr)
   ((x ...) t)
   (where (class C extends D ((C_2 f_2) ...) K M ...)
          (class-lookup CT C))
   (where (B m ((B_1 x) ...) t)
          (method-in m M ...))]
  ; m is not defined in C
  [(mbody CT m C)
   (mbody CT m D)
   (where (class C extends D ((C_2 f_2) ...) K M ...)
          (class-lookup CT C))
   (where #f (method-in m M ...))])

;; Auxiliary functions for method lookup
(define-metafunction FJ
  method-in : m M ... -> any
  [(method-in m M_0 ... (C m any ...) M_1 ...)
   (C m any ...)]
  [(method-in m any) #f])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Valid method overriding
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-judgment-form FJ
  ; all constituents are inputs
  #:mode (override I I I I I) 
  #:contract (override CT m D (C ...) C)
  
  [(where #f (mtype CT m D))
   ------------------------------
   (override CT m D (C ...) C_0)]
  
  [(where ((C ...) C_0) (mtype CT m D))
   ------------------------------------
   (override CT m D (C ...) C_0)])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Value substitution
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction FJ
  subst : x v any -> any
  ; Substitute variable
  [(subst x v x) v]
  ; Distribute substitution
  [(subst x v (any_2 ...)) 
   ((subst x v any_2) ...)]
  ; Do not substitute anything else
  [(subst x v any_2) any_2])

(define-metafunction FJ
  subst-many : (x ...) (v ...) any -> any    
  ; Multiple substitution
  [(subst-many (x_1 x_2 ...) (v_1 v_2 ...) any_3)
   (subst x_1 v_1 (subst-many (x_2 ...) (v_2 ...) any_3))]
  ; All other cases
  [(subst-many () () any) any])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reduction semantics of FJ
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; All congruence rules are subsumed by evaluation contexts
(define red
  (reduction-relation
   FJ
   #:domain (t CT)
   
   (--> ((in-hole E (lkp (new C v ...) f_i)) CT)
        ((in-hole E v_i) CT)
        "(E-ProjNew)"
        (where ((C_1 f_1) ...) (fields CT C))
        (where/hidden v_i ,(cadr (assoc (term f_i) (term ((f_1 v) ...)))))
        )
   
   (--> ((in-hole E (call (new C v ...) m v_1 ...)) CT)
        ((in-hole E (subst-many (x ...) (v_1 ...) 
                                (subst this (new C v ...) t_0))) CT)
        "(E-InvkNew)"
        (where ((x ...) t_0) (mbody CT m C)))
   
   (--> ((in-hole E (cast D (new C v ...))) CT)
        ((in-hole E (new C v ...)) CT)
        "(E-CastNew)"
        (judgment-holds (<: CT C D)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Type checking
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; Environment extension
(define-metafunction FJ
  extend : Γ x C -> Γ
  [(extend ((x_0 C_0) ... (x_i C_i) (x_i+1 C_i+1) ...) x_i C)
   ((x_0 C_0) ... (x_i C) (x_i+1 C_i+1) ...)]
  [(extend ((x_1 C_1) ...) x_0 C_0)
      ((x_0 C_0) (x_1 C_1) ...)])

; Environment lookup
(define-metafunction FJ
  lookup : Γ x -> C
  [(lookup ((x_0 C_0) ... (x_i C_i) (x_i+1 C_i+1) ...) x_i) 
   C_i])


;; Typing rules

(define-judgment-form FJ
  #:mode (typeof I I I O)
  #:contract (typeof CT Γ t C)
   
  ; (T-Var)
  [(where C (lookup Γ x))
   ----------------------
   (typeof CT Γ x C)]
  
  ; (T-Field)
  [(typeof CT Γ t_0 C_0)
   (where ((C f) ...) (fields CT C_0))
   (where ((C_1 f_1) ... (C_i f_i) (C_i+1 f_i+1) ...) ((C f) ...))
   -------------------------------
   (typeof CT Γ (lkp t_0 f_i) C_i)]
  
  ; (T-Invk)
  [(typeof CT Γ t_0 C_0)
   (where ((D ...) C) (mtype CT m C_0))
   (typeof CT Γ t B) ...
   (<: CT B D) ...
   ------------------------------------
   (typeof CT Γ (call t_0 m t ...) C)]
  
  ; (T-New)
  [(where ((D f) ...) (fields CT C))
   (typeof CT Γ t B) ...
   (<: CT B D) ...
   ---------------------------------
   (typeof CT Γ (new C t ...) C)]
  
  ; (T-UCast)
  [(typeof CT Γ t_0 D)
   (<: CT D C)
   ----------------------------
   (typeof CT Γ (cast C t_0) C)]
  
  ; (T-DCast)
  [(typeof CT Γ t_0 D)
   (<: CT C D)
   (where #f (c-equal C D))
   ----------------------------
   (typeof CT Γ (cast C t_0) C)]

  ; (T-SCast)
  [(typeof CT Γ t_0 D)
   (where #t (non-related CT C D))
   ; A stupid warning should be emitted here
   ----------------------------------------
   (typeof CT Γ (cast C t_0) C)])

; Method typing
(define-judgment-form FJ
  #:mode (method-ok I I I)
  #:contract (method-ok CT M C)
  
  ; [M OK in C]
  [(where (class C extends D ((C_2 f_2) ...) K M ...)
          (class-lookup CT C))
   (where (C_0 m ((C_1 x) ...) t_0)
          (method-in m M ...))
   (override CT m D (C_1 ...) C_0)
   (typeof CT ((this C) (x C_1) ...) t_0 B_0)
   (<: CT B_0 C_0)
   -------------------------------------------------
   (method-ok CT (C_0 m ((C_1 x) ...) t_0) C)])

; Class typing
(define-judgment-form FJ
  #:mode (class-ok I I)
  #:contract (class-ok CT CL)
  
  ; [C OK]
  [(where ((D_1 f_1) ...) (fields CT D))   
   (where (C ((C_1 f) ... (D_1 f_1) ...) 
             (super f_1 ...) (f f) ...) K)   
   (method-ok CT M C) ...
   -------------------------------------------------------
   (class-ok CT (class C extends D ((C_1 f) ...) K M ...))])
  
; Class table well-formedness
(define-judgment-form FJ
  #:mode (class-table-ok I)
  #:contract (class-table-ok CT)
  
  [(where (CL ...) CT)
   (class-ok CT CL) ...
   --------------------
   (class-table-ok CT)])

; Auxiliary equivalende predicate
(define-metafunction FJ
  c-equal : C C -> Bool
  [(c-equal C C) #t]
  [(c-equal C D) #f])

(define-metafunction FJ
  non-related : CT C C -> Bool
  [(non-related CT C D) 
   #f
   (judgment-holds (<: CT C D))]
  [(non-related CT C D) 
   #f
   (judgment-holds (<: CT D C))]
  [(non-related CT C D) #t])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Working examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Class table
(define class-table
  (term 
   (
    (class A extends Object 
      () 
      (A () (super)) 
      )
    
    (class B extends Object 
      () 
      (B () (super)) 
      )
        
    (class Pair extends Object 
      ;; Class body
      ; Fields
      ((Object fst)
       (Object snd))
      
      ; Constructor
      (Pair ((Object fst) (Object snd))
            (super)
            (fst fst)
            (snd snd))
      
      ; Method definitions
      (Pair setfst ((Object newfst))
            (new Pair newfst (lkp this snd))))
    
    (class Triple extends Pair 
      ;; Class body
      ; Fields
      ((A thrd))
      
      ; Constructor
      (Triple ((A thrd) (Object fst) (Object snd))
              (super fst snd)
              (thrd thrd))
      
      ; Method definitions
      (Triple setthrd ((A newthrd))
              (new Triple newthrd (lkp this fst) (lkp this snd)))
      )
    
    )
   ))


; Programs

(define term0 (term (cast Object (new A))))

(define term1 (term (lkp (new Pair (new A) (new B)) fst)))

(define term2 (term (call (new Pair (new A) (new B)) setfst (new B))))

(define term3 (term (cast Pair (new Pair (new Pair (new A) (new B)) (new A)))))

(define term4 (term (lkp (lkp (new Pair (new Pair (new A) (new B)) (new A)) fst) snd)))

(define term5 (term (lkp (cast Pair (lkp (cast Pair (new Pair (new Pair (new A) (new B)) (new A))) fst)) snd)))

(define term6 (term (lkp (new Triple (new A) (new B) (new A)) fst)))

(define term7 (term (lkp (cast Pair (new Triple (new A) (new B) (new A))) fst)))

(define term8 (term (lkp (new Triple (new A) (new B) (new A)) thrd)))


; Examples
(define example0
  `(,term0 ,class-table))

(define example1
  `(,term1 ,class-table)) 

(define example2
  `(,term2 ,class-table))

(define example3
  `(,term3 ,class-table))

(define example4
  `(,term4 ,class-table))

(define example5
  `(,term5 ,class-table))

(define example6
  `(,term6 ,class-table))

(define example7
  `(,term7 ,class-table))

(define example8
  `(,term8 ,class-table))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Runtime semantics tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(test-->> red
          example1
          `((new A) ,class-table))


(test-->> red
          example2
          `((new Pair (new B) (new B)) ,class-table))

(test-->> red
          example3
          `((new Pair
                 (new Pair (new A) (new B))
                 (new A)) ,class-table))

(test-->> red
          example4
          `((new B) ,class-table))

(test-->> red
          example5
          `((new B) ,class-table))

(test-->> red
          example6
          `((new B) ,class-table))

(test-->> red
          example7
          `((new B) ,class-table))

(test-->> red
          example8
          `((new A) ,class-table))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Type checking tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Class table is well-formed
(test-equal (judgment-holds (class-table-ok ,class-table))
            #t)


; Typing programs
; C is a pattern variable, so the set of admissible types is inferred
(test-equal (judgment-holds (typeof ,class-table () ,term0 C) C)
            '(Object))

(test-equal (judgment-holds (typeof ,class-table () ,term1 C) C)
            '(Object))

(test-equal (judgment-holds (typeof ,class-table () ,term2 C) C)
            '(Pair))

(test-equal (judgment-holds (typeof ,class-table () ,term3 C) C)
            '(Pair))

; Ill-typed term
(test-equal (judgment-holds (typeof ,class-table () ,term4 C) C)
            '())

(test-equal (judgment-holds (typeof ,class-table () ,term5 C) C)
            '(Object))

(test-equal (judgment-holds (typeof ,class-table () ,term6 C) C)
            '(Object))

(test-equal (judgment-holds (typeof ,class-table () ,term7 C) C)
            '(Object))

(test-equal (judgment-holds (typeof ,class-table () ,term8 C) C)
            '(A))

