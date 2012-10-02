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
   (<: CT C D_1)]
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
  fields : CT C -> (f ...)
  
  [(fields CT Object) ()]
  [(fields CT C)
   (f_2 ... f_3 ...)
   (where (class C extends D ((C_2 f_2) ...) any ...) 
          (class-lookup CT C))
   (where ((D_3 f_3) ...)
          (fields CT D))])

;; Checking if a field is in a field list
(define (zip p q) (map list p q))

(define (field-in f fs) 
  (assoc f (zip fs (range (length fs)))))

;; Method type lookup 
(define-metafunction FJ
  mtype : CT m C -> ((C ...) C)
  ; m is defined in C
  [(mtype CT m C)
   ; Map parameter entries to types (i.e., take car)
   (,(map car (term ((B_1 x) ...))) B)
   (where (class C extends D ((C_2 f_2) ...) K M ...)
          (class-lookup CT C))
   (where (B m ((B_1 x) ...) t)
          (method-in m M ...))]
  ; m is not defined in C
  [(mtype CT m C)
   (mtype CT m D)
   (where (class C extends D ((C_2 f_2) ...) K M ...)
          (class-lookup CT C))
   (where #f (method-in m M ...))])

;; Method body lookup 
(define-metafunction FJ
  mbody : CT m C -> ((x ...) t)
  ; m is defined in C
  [(mbody CT m C)
   ; Map parameter entries to parameter names (i.e., take cadr)
   (,(map cadr (term ((B_1 x) ...))) t)
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
  [(method-in m (C m any ...) M_1 ...)
   (C m any ...)]
  [(method-in m M M_1 ...) 
   (method-in m M_1 ...)]
  [(method-in m any) #f])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Valid method overriding
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-judgment-form FJ
  ; all constituents are inputs
  #:mode (override I I I I) 
  #:contract (override m D (C ...) C)
  [(where ((C ...) C_0) (mtype m D))
   ---------------------------------
   (override m D (C ...) C_0)])


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
        (where (f_1 ...) (fields CT C))
        (where/hidden v_i ,(cadr (assoc (term f_i) (zip (term (f_1 ...)) (term (v ...))))))
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
      (P ((Object fst) (Object snd))
         (super)
         (fst fst)
         (snd snd))
      
      ; Method definitions
      (Pair setfst ((Object newfst))
            (new Pair newfst (lkp this snd))))
    )
    ))


; Programs
(define example0
  `((cast Object (new A)) 
    ,class-table))

(define example1
  `((lkp (new Pair (new A) (new B)) fst) ,class-table))


(define example2
  `((call (new Pair (new A) (new B)) setfst (new B)) ,class-table))

(define example3
  `((cast Pair (new Pair (new Pair (new A) (new B)) (new A))) ,class-table))

(define example4
  `((lkp (lkp (cast Pair (new Pair (new Pair (new A) (new B)) (new A))) fst) snd) ,class-table))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tests
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


