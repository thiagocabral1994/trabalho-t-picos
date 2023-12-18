#lang racket

(require redex)

; CONSTANTS =====================================
(define SEPARATOR "_")
(define DERIVE-SYMBOL "'")

; UTIL ===============================================
(define (contains-underscore? word)
  (string-contains? word SEPARATOR))

(define (squash-symbols symbol-1 symbol-2)
  (string->symbol
   (if (contains-underscore? (symbol->string symbol-1))
       (string-append (symbol->string symbol-1) (symbol->string symbol-2))
       (string-append (symbol->string symbol-1) SEPARATOR (symbol->string symbol-2)))))

(define (derive-symbol symbol)
  (string->symbol
   (string-append (symbol->string symbol) DERIVE-SYMBOL)))

(define (create-word non-terminal-symbol)
  (let ([NT-string (symbol->string non-terminal-symbol)])
    (if (contains-underscore? NT-string) 
        (cadr (string-split (string-replace NT-string DERIVE-SYMBOL "") SEPARATOR))
        "ε")))

; TERMS =========================================
(define-term grammar-1 ((A → (B a)) (B → (c / d))))
(define-term grammar-loop ((A → (a A))))
(define-term grammar-invalid ((A → a) (A → c)))
(define-term grammar-alt ((A → (((a / b) / (c / d)) e))))
(define-term grammar-cyclic ((A → (B a)) (B → (c / (d A)))))
(define-term grammar-alt-empty ((A → ((a / ε) / c))))
(define-term grammar-invalid-2 ((A → B)))

; LANGUAGE ======================================
(define-language CFG
  [Grammar ::= (Production_1 Production_2 ...)]
  [Production ::= (NT → Exp)]
  [Exp ::= Seq Alt Terminal NT ε]
  [Seq ::= (Exp_1 Exp_2)]
  [Alt ::= (Exp_1 / Exp_2)]
  [Terminal ::= a b c d e f g h i j k l m n o p q r s t u v x y z]
  [word ::= string]
  [NT ::= variable-not-otherwise-mentioned]
  )

(define-extended-language Reduction-CFG
  CFG
  [Reduction ::= Grammar word])

(define-extended-language Judgement-CFG
  CFG
  [Output-Symbol ::= Terminal ε])

; METAFUNCTIONS =================================
(define-metafunction CFG
  unique-productions : Grammar -> boolean
  [(unique-productions ((NT → Exp_1) Production_1 ... (NT → Exp_2) Production_2 ...)) #false]
  [(unique-productions ((NT → Exp_1) Production_1 ... (NT_1 → Exp_2) Production_2 ...)) #true]
  )
(test-equal (term (unique-productions grammar-1)) #true)
(test-equal (term (unique-productions grammar-invalid)) #false)

(define-metafunction CFG
  production-valid : Grammar -> boolean
  [(production-valid ((NT → ε) Production ...)) #true]
  [(production-valid ((NT → Terminal) Production ...)) #true]
  [(production-valid ((NT → NT_1) Production_1 ... (NT_1 → Exp) Production_2 ...)) #true]
  [(production-valid ((NT → (Exp_1 Exp_2)) Production ...))
                     ,(and
                       (term (production-valid ((,(derive-symbol (term NT)) → Exp_1) (NT → (Exp_1 Exp_2)) Production ...)))
                       (term (production-valid ((,(derive-symbol (term NT)) → Exp_2) (NT → (Exp_1 Exp_2)) Production ...))))]
  [(production-valid ((NT → (Exp_1 / Exp_2)) Production ...))
                     ,(and
                       (term (production-valid ((,(derive-symbol (term NT)) → Exp_1) (NT → (Exp_1 / Exp_2)) Production ...)))
                       (term (production-valid ((,(derive-symbol (term NT)) → Exp_2) (NT → (Exp_1 / Exp_2)) Production ...))))]
  [(production-valid _) #false]
  )
(test-equal (term (production-valid ((A → ε)))) #true)
(test-equal (term (production-valid ((A → a)))) #true)
(test-equal (term (production-valid ((A → B) (B → a)))) #true)
(test-equal (term (production-valid ((A → (B c)) (B → a)))) #true)
(test-equal (term (production-valid ((A → (d / B)) (B → e)))) #true)
(test-equal (term (production-valid ((A → B)))) #false)
(test-equal (term (production-valid ((A → (B c))))) #false)
(test-equal (term (production-valid ((A → (d / B))))) #false)

(define-metafunction CFG
  create-derived-non-terminal : NT -> NT
  [(create-derived-non-terminal NT) ,(derive-symbol (term NT))])
(test-equal (term (create-derived-non-terminal A)) (term A\'))
(test-equal (term (create-derived-non-terminal A_abc)) (term A_abc\'))

(define-metafunction CFG
  create-non-terminal : NT Terminal -> NT
  [(create-non-terminal NT Terminal) ,(squash-symbols (term NT) (term Terminal))])
(test-equal (term (create-non-terminal A a)) (term A_a))
(test-equal (term (create-non-terminal A_abc d)) (term A_abcd))

(define-metafunction Reduction-CFG
  get-word : NT -> string
  [(get-word NT) ,(create-word (term NT))])
(test-equal (term (get-word A_abc)) "abc")
(test-equal (term (get-word A)) "ε")

; REDUCTION-RELATION =================================
(define derivative
  (reduction-relation Reduction-CFG
                      #:domain Reduction
                      #:codomain Reduction
                      (--> ((NT → Terminal) Production ...)
                           (((create-non-terminal NT Terminal) → ε) (NT → Terminal) Production ...)
                           "terminal")

                      (--> ((NT_1 → NT_2) Production ... (NT_2 → Exp))
                           (((create-derived-non-terminal NT_1) → Exp) (NT_1 → NT_2) Production ... (NT_2 → Exp))
                           "replace-non-terminal")

                      (--> ((NT → (Exp_1 / Exp_2)) Production ...)
                           (((create-derived-non-terminal NT) → Exp_1) (NT → (Exp_1 / Exp_2)) Production ...)
                           "choose-first-expression")

                      (--> ((NT → (Exp_1 / Exp_2)) Production ...)
                           (((create-derived-non-terminal NT) → Exp_2) (NT → (Exp_1 / Exp_2)) Production ...)
                           "choose-second-expression")

                      (--> ((NT → (Terminal Exp)) Production ...)
                           (((create-non-terminal NT Terminal) → Exp) (NT → (Terminal Exp)) Production ...)
                           "terminal-in-sequence")

                      (--> ((NT_1 → (NT_2 Exp_1)) Production ... (NT_2 → Exp_2))
                           (((create-derived-non-terminal NT_1) → (Exp_2 Exp_1)) (NT_1 → (NT_2 Exp_1)) Production ... (NT_2 → Exp_2))
                           "replace-non-terminal-in-sequence")

                      (--> ((NT_1 → ((Exp_1 Exp_2) Exp_3)) Production ...)
                           ((NT_1 → (Exp_1 (Exp_2 Exp_3))) Production ...)
                           "normalize-sequence")

                      (--> ((NT_1 → ((Exp_1 / Exp_2) Exp_3)) Production ...)
                           (((create-derived-non-terminal NT_1) → (Exp_1 Exp_3)) (NT_1 → ((Exp_1 / Exp_2) Exp_3)) Production ...)
                           "choose-first-exp-in-sequence")

                      (--> ((NT_1 → ((Exp_1 / Exp_2) Exp_3)) Production ...)
                           (((create-derived-non-terminal NT_1) → (Exp_2 Exp_3)) (NT_1 → ((Exp_1 / Exp_2) Exp_3)) Production ...)
                           "choose-second-exp-in-sequence")

                      (--> ((NT_1 → (ε Exp)) Production ...)
                           ((NT_1 → Exp) Production ...)
                           "ignore-ε-in-sequence")
                      
                      (--> ((NT → ε) Production ...)
                           (get-word NT)
                           "accept-word")
  ))

; JULGAMENTO =================================

(define-judgment-form Judgement-CFG
  #:mode (: I O)
  #:contract (: Grammar (Output-Symbol ...))
  
  [
   -----------  "Terminal"
   (: ((NT → Terminal) Production ...) (Terminal))
   ]

   [
   -----------  "Empty"
   (: ((NT → ε) Production ...) (ε))
   ]

  [
   (: ((NT_2 → Exp) Production_1 ... (NT_1 → NT_2) Production_2 ...) (Output-Symbol ...))
   -----------  "Non-Terminal"
   (: ((NT_1 → NT_2) Production_1 ... (NT_2 → Exp) Production_2 ...) (Output-Symbol ...))
   ]

  [
   (: ((NT → Exp_1) Production ...) (Output-Symbol ...))
   -----------  "Sequence"
   (: ((NT → (Exp_1 Exp_2)) Production ...) (Output-Symbol ...))
   ]

  [
   (: ((NT → Exp_1) Production ...) (Output-Symbol ...))
   -----------  "Sequence-ε"
   (: ((NT → (ε Exp_1)) Production ...) (Output-Symbol ...))
   ]

  [
   (: ((NT → Exp_1) Production ...) (Output-Symbol_1 ...))
   (: ((NT → Exp_2) Production ...) (Output-Symbol_2 ...))
   -----------  "Choice"
   (: ((NT → (Exp_1 / Exp_2)) Production ...) (Output-Symbol_1 ... Output-Symbol_2 ...))
   ]

  [
   (: ((NT → Exp_1) Production ...) (ε))
   (: ((NT → Exp_2) Production ...) (Output-Symbol_2 ...))
   (: ((NT → Exp_3) Production ...) (Output-Symbol_3 ...))
   -----------  "Choice-ε-left"
   (: ((NT → ((Exp_1 / Exp_2) Exp_3)) Production ...) (Output-Symbol_2 ... Output-Symbol_3 ...))
   ]

  [
   (: ((NT → Exp_1) Production ...) (Output-Symbol_1 ...))
   (: ((NT → Exp_2) Production ...) (ε))
   (: ((NT → Exp_3) Production ...) (Output-Symbol_3 ...))
   -----------  "Choice-ε-right"
   (: ((NT → ((Exp_1 / Exp_2) Exp_3)) Production ...) (Output-Symbol_1 ... Output-Symbol_3 ...))
   ]
  )

#;(judgment-holds (: grammar-1 (c d)))

(show-derivations
 (build-derivations
  (: grammar-alt-empty (a ε c))))

(traces derivative (term grammar-1))