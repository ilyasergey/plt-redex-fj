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
  (CL (class C extends C ((C f) ...) K (M ...)))
  
  ; Constructor declarations
  (K (C ((C f) ...) (super (f ...)) ((C f) ...)))
  
  ; Method declarations
  (M (C m ((C x) ...) t))
  
  ; Terms
  (t x 
     (lkp t f) 
     (call t m (t ...)) 
     (new C (t ...)) 
     (cast C t))
  
  ; Values
  (v (new C (v ...)))
  
  ; Class table
  (CT (CL ...))
  
  ; Evaluation contexts
  (E hole 
     (lkp E f) 
     (call E m (t ...))
     (call v m (v ... E t ...))
     (new C (v ... E t ...))
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
   (<: CT C D_1)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary meta-functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Class lookup by name from the class table
(define-metafunction FJ
  class-lookup : CL C -> (or/c CL #f)
  
  [(class-lookup (CL CL_1 ...) C) 
   CL
   (where (class C extends D ((C_2 f) ...) K (M ...)) CL)]  
  [(class-lookup (any CL_1 ...) C) 
   (class-lookup (CL_1 ...) C)]
  [(class-lookup () C) #f])

;; Fields lookup
(define-metafunction FJ
  fields : CT C -> ((C f) ...)
  
  [(fields (CT Object)) ()]
  [(fields (CT C))
   ,(append (term (((C_2 f_2) ...) ((D_3 f_3) ...))))
   (where (class C extends D ((C_2 f_2) ...) K (M ...)) 
          (class-lookup CT C))
   (where ((D_3 f_3) ...)
          (fields CT D))])

; Trivial equality predicate
(define-judgment-form FJ
  #:mode (eq I I) 
  #:contract (eq f f)
  [--------
   (eq f f)])

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
   (where (class C extends D ((C_2 f_2) ...) K (M ...))
          (class-lookup CT C))
   (where (B m ((B_1 x) ...) t)
          (method-in m (M ...)))]
  ; m is not defined in C
  [(mtype CT m C)
   (mtype CT m D)
   (where (class C extends D ((C_2 f_2) ...) K (M ...))
          (class-lookup CT C))
   (where #f (method-in m (M ...)))])

;; Method body lookup 
(define-metafunction FJ
  mbody : CT m C -> ((x ...) t)
  ; m is defined in C
  [(mbody CT m C)
   ; Map parameter entries to parameter names (i.e., take cadr)
   (,(map cadr (term ((B_1 x) ...))) t)
   (where (class C extends D ((C_2 f_2) ...) K (M ...))
          (class-lookup CT C))
   (where (B m ((B_1 x) ...) t)
          (method-in m (M ...)))]
  ; m is not defined in C
  [(mbody CT m C)
   (mbody CT m D)
   (where (class C extends D ((C_2 f_2) ...) K (M ...))
          (class-lookup CT C))
   (where #f (method-in m (M ...)))])

;; Auxiliary functions for method lookup
(define-metafunction FJ
  method-name : m M -> boolean?
  [(method-name m (C m_1 ((C_1 x) ...) t))
   ,(equal? (term m) (term m_1))])

(define-metafunction FJ
  method-in : m (M ...) -> (or/c M #f)
  [(method-in m (M M_1 ...))
   M
   (where #t (method-name m M))]
  [(method-in m (M M_1 ...)) 
   (method-in m (M_1 ...))]
  [(method-in m ()) #f])

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
   #:domain (CT (in-hole E t))
   
   (--> (CT (in-hole E (lkp (new C (v ...)) f_i)))
        (CT (in-hole E v_i))
        "(E-ProjNew)"
        (where ((C_1 f_1) ...) (fields CT C))
        (where/hidden (f_i i) ,(field-in (term f_i) (term ((C_1 f_1) ...))))
        (where/hidden v_i ,(list-ref (term i) (term (v ...)))))
   
   (--> (CT (in-hole E (call (new C (v ...)) m (v_1 ...))))
        (CT (in-hole E (subst-many (x ...) (v_1 ...) 
                                   (subst this (new C (v ...)) t_0))))
        "(E-InvkNew)"
        (where ((x ...) t_0) (mbody CT m C)))
   
   (--> (CT (in-hole E (cast D (new C (v ...)))))
        (CT (in-hole E (new C (v ...))))
        "(E-CastNew)"
        (judgment-holds (<: C D CT)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Working example
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

