#lang racket

#|

This file contains a simple implementation of the Featherweight Java language,
as described in Benjamin C. Pierce's "Types and Programming Languages"
  
|#


(require redex)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FJ Syntax
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-language FJ
  
  ; Class declarations
  (CL (class C extends C ((C f) ...) K (M ...)))
  
  ; Constructor declarations
  (K (C ((C f) ...) (super (f ...)) ((f f) ...)))
  
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
  (C variable-not-otherwise-mentioned))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Various lookup meta-functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; Class lookup by name from the class table
(define-metafunction FJ
  class-lookup : CL C -> CL  
  
  [(class-lookup (CL CL_1 ...) C) 
   CL
   (where (class C extends C_1((C_2 f) ...) K (M ...)) CL)]  
  [(class-lookup ((class C_1 extends C_2((C_3 f) ...) K (M ...)) CL_1 ...) C) 
   (class-lookup (CL_1 ...) C)])


(define-metafunction FJ
  fields : CT C -> ((C f) ...)
  
  [(fields (CT Object)) ()]
  [(fields (CT C))
   ,(append (term (((C_2 f_2) ...) ((C_3 f_3) ...))))
   (where (class C extends C_1((C_2 f_2) ...) K (M ...)) 
          (class-lookup CT C))
   (where ((C_3 f_3) ...)
          (fields CT C_1))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Valid method overriding
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reduction semantics of FJ
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(define red
;  (reduction-relation
;   FJ
;   #:domain (E CT)
;   ))

