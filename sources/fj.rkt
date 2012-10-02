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
  #:contract (<: C C CT)
  [----------
   (<: C C CT)]
  
  [(where (class C extends D any ...) (class-lookup CT C))
   (<: D D_1 CT)   
   ---------------
   (<: C D_1 CT)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary meta-functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Class lookup by name from the class table
(define-metafunction FJ
  class-lookup : CL C -> (or/c CL #f)
  
  [(class-lookup (CL CL_1 ...) C) 
   CL
   (where (class C extends D((C_2 f) ...) K (M ...)) CL)]  
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
(define-judgment-form FJ
  #:mode (field-in I I) 
  #:contract (field-in f ((C f) ...))
  [(eq f f_1)
   ------------------------------
   (field-in f ((C f_1) any ...))]
  
  [(field-in f ((C_1 f_1) ...))
   --------------------------------------
   (field-in f ((C_0 f_0) (C_1 f_1) ...))])


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
;; Reduction semantics of FJ
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(define red
;  (reduction-relation
;   FJ
;   #:domain (E CT)
;   ))

