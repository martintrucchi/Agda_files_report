\begin{code}

{-# OPTIONS --safe --without-K  #-}

open import MLTT.Spartan
open import MGS.index
open import Naturals.Addition renaming (_+_ to _+'_)
open import Naturals.Division
open import Naturals.Multiplication
open import Naturals.Order
open import UF.Base
open import UF.Choice
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Powerset
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

module SyntheticTopology.SierpinskiObjectExamples.QuasidecidableSynthetic
        (𝓤 : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        where
 
open import NotionsOfDecidability.Decidable
open import NotionsOfDecidability.SemiDecidable fe pe pt
open import NotionsOfDecidability.QuasiDecidable fe pe pt
open import SyntheticTopology.SetCombinators 𝓤₀ fe pe pt hiding (ℕ)
open import SyntheticTopology.SierpinskiObject fe pe pt
open import UF.ImageAndSurjection pt
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_ ; ∨-elim)

\end{code}

\begin{code}

eq-to-iff : {p q : 𝓤 ̇} → p ＝ q → (p ↔ q)
eq-to-iff {p} {q} eq = transport (λ - → (p ↔ -)) eq (id , id)

module _ (qde : quasidecidable-propositions-exist 𝓤 𝓤) where

 open quasidecidable-propositions-exist qde

 Quasidecidable : Generalized-Sierpinski-Object 𝓤 𝓤
 Quasidecidable (P , prop-P) = is-quasidecidable P , being-quasidecidable-is-prop P

\end{code}

We here instanciate the modules needed to prove some basic lemmas.

\begin{code}

 open Sierpinski-notations Quasidecidable
 open import SyntheticTopology.Compactness 𝓤 𝓤 fe pe pt Quasidecidable
 open import SyntheticTopology.Overtness 𝓤 𝓤 fe pe pt Quasidecidable
 open import SyntheticTopology.SierpinskiAxioms 𝓤 𝓤 fe pe pt Quasidecidable

 to-quasi-＝
  : {((P , prop-P) , quasi-P) ((Q , prop-Q) , quasi-Q) : Ωₒ}
    → P ＝ Q
    → ((P , prop-P) , quasi-P) ＝ ((Q , prop-Q) , quasi-Q)
 to-quasi-＝ {(P , prop-P) , quasi-P} {(Q , prop-Q) , quasi-Q} eq =
  to-subtype-＝ (λ x → being-quasidecidable-is-prop (pr₁ x) ) (to-Ω-＝ fe eq)

 𝟘ₖ : Ωₒ
 𝟘ₖ = ⊥ , 𝟘-is-quasidecidable
 𝟙ₖ : Ωₒ
 𝟙ₖ = ⊤ , 𝟙-is-quasidecidable

 decidable-gives-quasidecidable
  : (P : 𝓤 ̇) → is-prop P →  is-decidable P → is-quasidecidable P
 decidable-gives-quasidecidable P prop-P =
  cases (λ Pholds → transport is-quasidecidable (pe 𝟙-is-prop prop-P (λ _ → Pholds) (λ _ → ⋆)) (𝟙-is-quasidecidable))
        λ notPholds → transport is-quasidecidable (pe 𝟘-is-prop prop-P 𝟘-elim λ - → 𝟘-elim (notPholds -)) (𝟘-is-quasidecidable)

 quasidecidable-closed-under-binary-joins
  :(p q : Ω 𝓤) → Quasidecidable p holds → Quasidecidable q holds → (Quasidecidable (p ∨ q) holds)
 quasidecidable-closed-under-binary-joins p q quasi-p quasi-q
  = transport (_holds ∘ Quasidecidable) † (quasidecidable-closed-under-ω-joins family quasi-family)
   where
    family : ℕ → 𝓤 ̇ 
    family 0 = p holds
    family 1 = q holds
    family (succ (succ n)) = 𝟘
    
    quasi-family : (n : ℕ) → is-quasidecidable (family n)
    quasi-family 0 = quasi-p
    quasi-family 1 = quasi-q
    quasi-family (succ (succ n)) = 𝟘-is-quasidecidable

    † : (∃ i ꞉ ℕ , family i) , ∃-is-prop ＝ p ∨ q
    † = to-Σ-＝ (pe ∃-is-prop ∥∥-is-prop (∥∥-functor find-i) (∥∥-functor (cases (λ pholds → 0 , pholds) λ qholds → 1 , qholds)) , being-prop-is-prop fe _ _)
     where
      find-i : Σ (λ i → family i) → (p holds) + (q holds)
      find-i (0 , pholds) = inl pholds
      find-i (1 , qholds) = inr qholds
      find-i ((succ (succ n)) , abs) = 𝟘-elim abs

 scott-continuity : (Ωₒ → Ωₒ) → 𝓤 ⁺ ̇
 scott-continuity f = (P : (ℕ → Ωₒ))  
    → ((i : ℕ) → (pr₁ (P i) holds → pr₁ (P (succ i)) holds))
      → pr₁ (f ((Ǝₚ i ꞉ ℕ , pr₁ (P i))
            , quasidecidable-closed-under-ω-joins (_holds ∘ pr₁ ∘ P) (pr₂ ∘ P)))
        ＝ (Ǝₚ i ꞉ ℕ , pr₁ (f (P i)))

 unrestricted-scott-continuity : (Ωₒ → Ωₒ) → 𝓤 ⁺ ̇
 unrestricted-scott-continuity f =
   (P : (ℕ → Ωₒ))  
   → pr₁ (f ((Ǝₚ i ꞉ ℕ , pr₁ (P i))
            , quasidecidable-closed-under-ω-joins (_holds ∘ pr₁ ∘ P) (pr₂ ∘ P)))
        ＝ (Ǝₚ i ꞉ ℕ , pr₁ (f (P i)))

 from-unrestricted-to-normal
  : (f : Ωₒ → Ωₒ) → unrestricted-scott-continuity f → scott-continuity f 
 from-unrestricted-to-normal f cscott P-family _ = cscott P-family

 phoa’s-principle' : 𝓤 ⁺ ̇
 phoa’s-principle'
  = phoa’s-principle 𝟙-is-quasidecidable 𝟘-is-quasidecidable holds

 Scott-continuity-gives-directed-binary-scott-continuity
  : (f : Ωₒ → Ωₒ)
    → scott-continuity f
    → ((p , semi-p) (q , semi-q) : Ωₒ)
    → (p ⇒ q) holds
    → pr₁ (f ((p ∨ q) , quasidecidable-closed-under-binary-joins p q semi-p semi-q))
     ＝ pr₁ (f (p , semi-p)) ∨ pr₁ (f (q , semi-q)) 
 Scott-continuity-gives-directed-binary-scott-continuity
  f scott-f (p , semi-p) (q , semi-q) p-gives-q  =
   pr₁ (f ((p ∨ q) , quasidecidable-closed-under-binary-joins p q semi-p semi-q))
     ＝⟨ ap (pr₁ ∘ f) (to-Σ-＝ (p-or-q-is-p-or-q-join , being-quasidecidable-is-prop ∥ Sigma ℕ (λ i → pr₁ (p-or-q-join i) holds) ∥ _ _)) ⟩
   pr₁ (f ((Ǝₚ i ꞉ ℕ , pr₁ (p-or-q-join i)) , quasidecidable-closed-under-ω-joins (λ i → pr₁ (p-or-q-join i) holds) (λ x → pr₂ (p-or-q-join x))))
     ＝⟨ scott-f p-or-q-join p-or-q-join-is-increasing ⟩
   Ǝₚ i ꞉ ℕ , pr₁ (f (p-or-q-join i)) ＝⟨ destruct-index ⟩ 
   pr₁ (f (p , semi-p)) ∨ pr₁ (f (q , semi-q)) ∎
    where
     p-or-q-join : ℕ → Ωₒ
     p-or-q-join 0 = p , semi-p
     p-or-q-join (succ n) = q , semi-q
      
     p-or-q-is-p-or-q-join : p ∨ q ＝ Ǝₚ i ꞉ ℕ , pr₁ (p-or-q-join i)
     p-or-q-is-p-or-q-join =
      Ω-extensionality pe fe (∥∥-rec ∃-is-prop (cases (λ pholds → ∣ 0 , pholds ∣) (λ qholds → ∣ 1 , qholds ∣)))
                             (∥∥-rec ∥∥-is-prop matching)

      where
       matching : (Σ i ꞉ ℕ , pr₁ (p-or-q-join i) holds) → (p ∨ q) holds
       matching (0 , pholds) = ∣ inl pholds ∣
       matching ((succ n) , qholds) = ∣ inr qholds ∣ 

     p-or-q-join-is-increasing : (i : ℕ) → (pr₁ (p-or-q-join i) ⇒ pr₁ (p-or-q-join (succ i))) holds
     p-or-q-join-is-increasing 0 = p-gives-q
     p-or-q-join-is-increasing (succ n) = id

     destruct-index : Ǝₚ i ꞉ ℕ , (pr₁ (f (p-or-q-join i))) ＝
                        pr₁ (f (p , semi-p)) ∨ pr₁ (f (q , semi-q))
     destruct-index = Ω-extensionality pe fe (∥∥-rec ∥∥-is-prop matching)
                                             (∥∥-rec ∃-is-prop (cases (λ fpholds → ∣ 0 , fpholds ∣) λ fqholds → ∣ 1 , fqholds ∣))
      where
       matching : (Σ i ꞉ ℕ , pr₁ (f (p-or-q-join i)) holds) → (pr₁ (f (p , semi-p)) ∨ pr₁ (f (q , semi-q))) holds
       matching (0 , fpholds) = ∣ inl fpholds ∣
       matching ((succ n) , fqholds) = ∣ inr fqholds ∣
      
 scott-continuity-gives-monotonicity
  : {(p , semi-p) (q , semi-q) : Ωₒ} (f : Ωₒ → Ωₒ) → scott-continuity f → (p ⇒ q) holds → (pr₁ (f (p , semi-p)) ⇒ pr₁ (f (q , semi-q))) holds
 scott-continuity-gives-monotonicity {(p , semi-p)} {q , semi-q} f scott-f p-gives-q f-p-holds
  = transport (_holds ∘ pr₁ ∘ f)
              (to-Σ-＝ ((q-lemma ⁻¹)
                      , being-quasidecidable-is-prop (pr₁ q) (transport (λ p₁ → Quasidecidable p₁ holds)
                                                    (q-lemma ⁻¹)
                                                    (quasidecidable-closed-under-binary-joins p q semi-p semi-q)) semi-q))
              (transport _holds
                         ((Scott-continuity-gives-directed-binary-scott-continuity f scott-f (p , semi-p) (q , semi-q) p-gives-q) ⁻¹)
                         ∣ inl f-p-holds ∣)
   where
    q-lemma : (q ＝ (p ∨ q))
    q-lemma = Ω-extensionality pe fe (∣_∣ ∘ inr) (∥∥-rec (holds-is-prop q) (cases p-gives-q id))

 independence-of-premise : 𝓤 ⁺ ̇
 independence-of-premise = (A : 𝓤 ̇) (B : ℕ → 𝓤 ̇) → (A → ∃ i ꞉ ℕ , B i) → ∃ i ꞉ ℕ , (A → B i)

\end{code}

We formalize a notion of "increasification".

\begin{code}

 is-increasing-family : (ℕ → 𝓤 ̇) → 𝓤 ̇
 is-increasing-family P = (n : ℕ) → P n → P (succ n) 

 weak-increasification : 𝓤 ⁺ ̇
 weak-increasification =
   (P : ℕ → 𝓤 ̇)
    → ((n : ℕ) → is-quasidecidable (P n))
    → Σ Q ꞉ (ℕ → 𝓤 ̇) ,
      ((n : ℕ) → is-quasidecidable (Q n)) × is-increasing-family Q × (∃ Q ↔ ∃ P)

 strong-increasification : 𝓤 ⁺ ̇
 strong-increasification = (P : ℕ → 𝓤 ̇)
    → ((n : ℕ) → is-quasidecidable (P n))
    → Σ Q ꞉ (ℕ → 𝓤 ̇) ,
      ((n : ℕ) → is-quasidecidable (Q n)) × is-increasing-family Q
        × ((n : ℕ) → (∃ i ꞉ ℕ , (Q n → P i))) × ((n : ℕ) → (∃ i ꞉ ℕ , (P n → Q i)))

\end{code}

The weak version always holds for quasidecidable propositions.

\begin{code}

 weak-increasification-holds
  : weak-increasification
 weak-increasification-holds P P-is-quasi-valued =
  Q , Q-is-quasi-valued , increasing-Q , join-Q-gives-join-P , join-P-gives-join-Q
  where
   Q : ℕ → 𝓤 ̇
   Q n = ∃ i ꞉ ℕ , ((i ≤ℕ n) × 𝟙 {𝓤}) × P i

   Q-is-quasi-valued : (n : ℕ) → is-quasidecidable (Q n)
   Q-is-quasi-valued n =
    quasidecidable-closed-under-ω-joins (λ i → ((i ≤ℕ n) × 𝟙 {𝓤}) × P i)
      λ i → hypothetical-quasidecidability.quasidecidable-closed-under-×
             {𝓤} {𝓤} qde
             ((i ≤ℕ n) × 𝟙 {𝓤})
             (decidable-gives-quasidecidable ((i ≤ℕ n) × 𝟙)
               (×-is-prop (≤-is-prop-valued i n) 𝟙-is-prop)
               (×-preserves-decidability (≤-decidable i n) (inl ⋆)))
             (P i)
             λ _ → P-is-quasi-valued i

   increasing-Q : is-increasing-family Q
   increasing-Q n =
    ∥∥-rec ∃-is-prop
           λ (i , (i-le-n , _) , Pi)
             → ∣ i , (≤-trans i n (succ n) i-le-n (≤-succ n) , ⋆) , Pi ∣

   join-Q-gives-join-P : ∃ Q → ∃ P
   join-Q-gives-join-P =
    ∥∥-rec ∃-is-prop
           λ (n , Qn)
            → ∥∥-rec ∃-is-prop (λ (i , _ , Pi) → ∣ i , Pi ∣) Qn

   join-P-gives-join-Q : ∃ P → ∃ Q
   join-P-gives-join-Q =
    ∥∥-rec ∃-is-prop λ (i , Pi) → ∣ i , ∣ i , (≤-refl i , ⋆) , Pi ∣ ∣

\end{code}

Assuming IP, we can derive the strong increasification.

\begin{code}

 ip-gives-strong-increasification
  : independence-of-premise → strong-increasification
 ip-gives-strong-increasification ip P P-is-quasi-valued =
  let (Q , Q-is-quasi-valued , increasing-Q , join-Q-gives-join-P
                                            , join-P-gives-join-Q) =
                             weak-increasification-holds P P-is-quasi-valued in

  Q , Q-is-quasi-valued , increasing-Q ,
  (λ n → ip (Q n) P (λ Qn → join-Q-gives-join-P ∣ n , Qn ∣)) ,
  λ n → ip (P n) Q (λ Pn → join-P-gives-join-Q ∣ n , Pn ∣)

\end{code}

\begin{code}

 scott-continuity-and-strong-increasification-gives-phoa
  : strong-increasification → ((f : Ωₒ → Ωₒ) → scott-continuity f)
  → phoa’s-principle'
 scott-continuity-and-strong-increasification-gives-phoa strong-inc scott-continuity f ((P , prop-P) , quasi-P)
  = transport (λ - → (pr₁ (f -) ⇔
                           (pr₁ (f 𝟙ₖ) ∧ pr₁ - ∨
                            pr₁ (f 𝟘ₖ)))
                          holds) (to-quasi-＝ refl) (pr₂ (pr₂ (quasi-lemma P quasi-P)))
   where
    quasi-lemma : (P₁ : 𝓤 ̇) →
                    is-quasidecidable P₁ →
                    Sigma (is-prop P₁)
                    (λ i →
                       Sigma (is-quasidecidable P₁)
                       (λ i' →
                          (pr₁ (f ((P₁ , i) , i')) ⇔
                           (pr₁ (f 𝟙ₖ) ∧ P₁ , i ∨
                            pr₁ (f 𝟘ₖ)))
                          holds))
    quasi-lemma =
     quasidecidable-induction
      (λ Q → Σ i ꞉ is-prop Q , Σ i' ꞉ is-quasidecidable Q
       , ((pr₁ (f ((Q , i) , i'))) ⇔ (pr₁ (f 𝟙ₖ)
                                          ∧ (Q , i)
                                    ∨ pr₁ (f 𝟘ₖ))) holds)
       (λ Q → Σ-is-prop (being-prop-is-prop fe) λ i → Σ-is-prop (being-quasidecidable-is-prop Q) λ i' → holds-is-prop ((pr₁ (f ((Q , i) , i')) ⇔
      (pr₁ (f 𝟙ₖ) ∧ Q , i ∨
       pr₁ (f 𝟘ₖ)))))
       (𝟘-is-prop , 𝟘-is-quasidecidable , ∣_∣ ∘ inr  , ∥∥-rec (holds-is-prop (pr₁ (f 𝟘ₖ)))
                                                              (cases (𝟘-elim ∘ pr₂) id))
       (𝟙-is-prop , 𝟙-is-quasidecidable , (λ hyp → ∣ inl (hyp , ⊤-holds) ∣) , ∥∥-rec (holds-is-prop (pr₁ (f 𝟙ₖ)))
                                                              (cases pr₁ (scott-continuity-gives-monotonicity f (scott-continuity f) 𝟘-elim)))
 
       induction-step
       where
        induction-step : (P₁ : ℕ → 𝓤 ̇) → ((n : ℕ) → Sigma (is-prop (P₁ n))
                            (λ i →
                               Sigma (is-quasidecidable (P₁ n))
                               (λ i' →
                                  (pr₁ (f ((P₁ n , i) , i')) ⇔
                                   (pr₁ (f 𝟙ₖ) ∧ P₁ n , i ∨
                                    pr₁ (f 𝟘ₖ)))
                                  holds))) →
                           Sigma (is-prop (Exists ℕ P₁))
                           (λ i →
                              Sigma (is-quasidecidable (Exists ℕ P₁))
                              (λ i' →
                                 (pr₁ (f ((Exists ℕ P₁ , i) , i')) ⇔
                                  (pr₁ (f 𝟙ₖ) ∧ Exists ℕ P₁ , i ∨
                                   pr₁ (f 𝟘ₖ)))
                                 holds))
        induction-step P-family IH 
         = let (Q , Q-is-quasi-valued , increasing-Q , any-Q-gives-join-P , any-P-gives-join-Q) = (strong-inc P-family λ n → pr₁ (pr₂ (IH n))) in
           let Q-is-prop-valued = λ i → hypothetical-quasidecidability.quasidecidable-types-are-props qde (Q i) (Q-is-quasi-valued i) in
           ∃-is-prop ,
           quasidecidable-closed-under-ω-joins P-family (λ n → pr₁ (pr₂ (IH n))) ,
           eq-to-iff (((f' ((Exists ℕ P-family , ∃-is-prop) , quasidecidable-closed-under-ω-joins P-family (λ n → pr₁ (pr₂ (IH n))))) holds)
                                       ＝⟨ ap (_holds ∘ f')
                                             (to-quasi-＝ (pe ∃-is-prop
                                                             ∃-is-prop
                                                             ((∥∥-rec ∃-is-prop λ (i , Pi)
                                                                → ∥∥-rec ∃-is-prop (λ (j , Pi-gives-Qj) → ∣ j , Pi-gives-Qj Pi ∣) (any-P-gives-join-Q i)))
                                                             (∥∥-rec ∃-is-prop λ (i , Qi)
                                                               → ∥∥-rec ∃-is-prop (λ (j , Qi-gives-Pj) → ∣ j , Qi-gives-Pj Qi ∣) (any-Q-gives-join-P i)))) ⟩
                     (f' ((Ǝₚ i ꞉ ℕ , (Q i , Q-is-prop-valued i))
                       , quasidecidable-closed-under-ω-joins Q Q-is-quasi-valued)) holds
                          ＝⟨ ap _holds (scott-continuity f (λ i → (Q i
                                                                  , Q-is-prop-valued i)
                                                                  , Q-is-quasi-valued i) increasing-Q) ⟩
                     (∃ i ꞉ ℕ , ((f' ((Q i , Q-is-prop-valued i) , Q-is-quasi-valued i)) holds))
                      ＝⟨ pe ∃-is-prop ∃-is-prop (∥∥-rec ∃-is-prop (λ (i , fqi) → ∥∥-rec ∃-is-prop
                                                                                        (λ (j , Qi-gives-Pj) →
                                                                                          ∣ j , scott-continuity-gives-monotonicity f (scott-continuity f)
                                                                                                 Qi-gives-Pj fqi ∣) (any-Q-gives-join-P i)))
                                                ( (∥∥-rec ∃-is-prop (λ (i , fpi) → ∥∥-rec ∃-is-prop
                                                                                        (λ (j , Pi-gives-Qj) →
                                                                                          ∣ j , scott-continuity-gives-monotonicity f (scott-continuity f)
                                                                                                 Pi-gives-Qj fpi ∣) (any-P-gives-join-Q i)))) ⟩
                     (∃ i ꞉ ℕ , ((f' ((P-family i , pr₁ (IH i)) , pr₁ (pr₂ (IH i)))) holds))
                       ＝⟨ ap (Exists ℕ) (dfunext fe (λ i → pe (holds-is-prop (f' ((P-family i , pr₁ (IH i)) , pr₁ (pr₂ (IH i)))))
                                                               (holds-is-prop ((pr₁ (f 𝟙ₖ) ∧ P-family i , pr₁ (IH i) ∨ pr₁ (f 𝟘ₖ))))
                                                                (pr₁ (pr₂ (pr₂ (IH i)))) (pr₂ (pr₂ (pr₂ (IH i)))))) ⟩
                     (∃ i ꞉ ℕ , (((f' 𝟙ₖ ∧ P-family i , pr₁ (IH i)) ∨ (f' 𝟘ₖ)) holds)) ＝⟨ distributivity-lemma  ⟩
                     ((f' 𝟙ₖ ∧ Exists ℕ P-family , ∃-is-prop ∨ (f' 𝟘ₖ)) holds) ∎ )

         where
          f' = pr₁ ∘ f
          
          distributivity-lemma : Exists ℕ (λ i → (f' 𝟙ₖ ∧ P-family i , pr₁ (IH i) ∨ f' 𝟘ₖ) holds) ＝ ((f' 𝟙ₖ ∧ Exists ℕ P-family , ∃-is-prop ∨ f' 𝟘ₖ) holds)
          distributivity-lemma =
           pe ∃-is-prop
             (holds-is-prop ((f' 𝟙ₖ ∧ Exists ℕ P-family , ∃-is-prop ∨ f' 𝟘ₖ)))
             (∥∥-rec (holds-is-prop ((f' 𝟙ₖ ∧ Exists ℕ P-family , ∃-is-prop ∨ f' 𝟘ₖ)))
               λ (i , hyp-i) → ∥∥-rec (holds-is-prop (f' 𝟙ₖ ∧ Exists ℕ P-family , ∃-is-prop ∨ f' 𝟘ₖ))
                                      (cases (λ (fone , pfami) → ∣ inl (fone , ∣ i , pfami ∣) ∣) (∣_∣ ∘ inr)) hyp-i)
             (∥∥-rec ∃-is-prop (cases (λ (fone , ex-i) → ∥∥-rec ∃-is-prop (λ (i , pfami) → ∣ i , ∣ inl (fone , pfami) ∣ ∣) ex-i)
                                      λ fzero → ∣ 0 , ∣ inr fzero ∣ ∣))


 phoa-gives-unrestricted-scott-continuity
  : phoa’s-principle' → (f : Ωₒ → Ωₒ) → scott-continuity f
 phoa-gives-unrestricted-scott-continuity phoa f p-family _
  = pr₁ (f ((Ǝₚ i ꞉ ℕ , pr₁ (p-family i)) ,
        quasidecidable-closed-under-ω-joins (_holds ∘ pr₁ ∘ p-family)
                                            (pr₂ ∘ p-family)))
        ＝⟨ phoa-eq ((Ǝₚ i ꞉ ℕ , pr₁ (p-family i)) ,
        quasidecidable-closed-under-ω-joins (_holds ∘ pr₁ ∘ p-family)
                                            (pr₂ ∘ p-family)) ⟩
    pr₁ (f 𝟙ₖ) ∧ (Ǝₚ i ꞉ ℕ , pr₁ (p-family i)) ∨ pr₁ (f 𝟘ₖ) ＝⟨ distributivity-lemma ⟩
    ((Ǝₚ i ꞉ ℕ , (pr₁ (f 𝟙ₖ) ∧ pr₁ (p-family i)
               ∨ pr₁ (f 𝟘ₖ)))) ＝⟨  ap (∃ₚ[꞉]-syntax ℕ) (dfunext fe (λ i → phoa-eq (p-family i) ⁻¹)) ⟩
    (Ǝₚ i ꞉ ℕ , (pr₁ (f (p-family i)))) ∎
     where
      phoa-eq : ((q , quasi-q) : Ωₒ)
                → pr₁ (f (q , quasi-q)) ＝ ((pr₁ (f 𝟙ₖ) ∧ q)
                                          ∨ pr₁ (f 𝟘ₖ))
      phoa-eq (q , quasi-q) = Ω-extensionality pe fe (pr₁ (phoa f (q , quasi-q))) (pr₂ (phoa f (q , quasi-q)))
      
      distributivity-lemma
       : pr₁ (f 𝟙ₖ) ∧ (Ǝₚ i ꞉ ℕ , pr₁ (p-family i))
         ∨ pr₁ (f 𝟘ₖ) ＝
           Ǝₚ i ꞉ ℕ , (pr₁ (f 𝟙ₖ) ∧ pr₁ (p-family i)
                       ∨ pr₁ (f 𝟘ₖ))
      distributivity-lemma =
       Ω-extensionality pe fe (∥∥-rec ∃-is-prop
                                      (cases (λ (f-⊤-holds , hyp)
                                        → ∥∥-rec ∃-is-prop
                                                 (λ (i , iprop) → ∣ i , ∣ inl (f-⊤-holds , iprop) ∣ ∣)
                                                 hyp)
                                              (λ f-⊥-holds → ∣ 0 , ∣ inr f-⊥-holds ∣ ∣)))
                              (∥∥-rec ∥∥-is-prop
                                      (λ (i , iprop) → ∥∥-rec ∥∥-is-prop (cases (λ (f-⊤-holds , pfam-i-holds) → ∣ inl (f-⊤-holds , ∣ i , pfam-i-holds ∣) ∣)
                                                                                                 λ f-⊥-holds → ∣ inr f-⊥-holds ∣) iprop))

\end{code}

If we remove the increasing condition in the scott continuity, we get
phoa’s principle, without assuming IP. 

\begin{code}

 unrestricted-scott-gives-phoa :
  ((f : Ωₒ → Ωₒ) → unrestricted-scott-continuity f)
   → phoa’s-principle'

 unrestricted-scott-gives-phoa cscott f ((P , prop-P) , quasi-P) =
  transport (λ - → (f' - ⇔ (f' 𝟙ₖ ∧ pr₁ - ∨ f' 𝟘ₖ)) holds)
            (to-quasi-＝ refl)
            (pr₂ (pr₂ (quasi-lemma P quasi-P)))
   where
    f' = pr₁ ∘ f
    
    quasi-lemma : (Q : 𝓤 ̇) →
                    is-quasidecidable Q →
                    Σ i ꞉ is-prop Q ,
                       Σ i' ꞉ is-quasidecidable Q ,
                          (f' ((Q , i) , i') ⇔ (((f' 𝟙ₖ) ∧ (Q , i)) ∨ (f' 𝟘ₖ)))
                          holds
    quasi-lemma =
     quasidecidable-induction (λ Q → Σ i ꞉ is-prop Q ,
                       Σ i' ꞉ is-quasidecidable Q ,
                          (f' ((Q , i) , i') ⇔ (((f' 𝟙ₖ) ∧ (Q , i)) ∨ (f' 𝟘ₖ)))
                          holds)
       (λ Q → Σ-is-prop (being-prop-is-prop fe) λ i → Σ-is-prop (being-quasidecidable-is-prop Q) λ i' → holds-is-prop ((f' ((Q , i) , i') ⇔
      (f' 𝟙ₖ ∧ Q , i ∨ f' 𝟘ₖ))))
       (𝟘-is-prop , 𝟘-is-quasidecidable , ∣_∣ ∘ inr , ∥∥-rec (holds-is-prop (f' 𝟘ₖ)) (cases (𝟘-elim ∘ pr₂) id))
       (𝟙-is-prop , 𝟙-is-quasidecidable , (λ hyp → ∣ inl (hyp , ⊤-holds) ∣)
        , ∥∥-rec (holds-is-prop (f' 𝟙ₖ)) (cases pr₁ (scott-continuity-gives-monotonicity f (from-unrestricted-to-normal f (cscott f)) 𝟘-elim)))
       induction-step
        where
         induction-step : (P-family : ℕ → 𝓤 ̇) →
                            ((n : ℕ) →
                             Sigma (is-prop (P-family n))
                             (λ i →
                                Sigma (is-quasidecidable (P-family n))
                                (λ i' →
                                   (f' ((P-family n , i) , i') ⇔
                                    (f' 𝟙ₖ ∧ P-family n , i ∨ f' 𝟘ₖ))
                                   holds))) →
                            Sigma (is-prop (Exists ℕ P-family))
                            (λ i →
                               Sigma (is-quasidecidable (Exists ℕ P-family))
                               (λ i' →
                                  (f' ((Exists ℕ P-family , i) , i') ⇔
                                   (f' 𝟙ₖ ∧ Exists ℕ P-family , i ∨  f' 𝟘ₖ))
                                  holds))
         induction-step P-family IH =
          ∃-is-prop
          , quasidecidable-closed-under-ω-joins P-family (λ n → pr₁ (pr₂ (IH n)))
          ,  eq-to-iff (((f' ((Exists ℕ P-family , ∃-is-prop) , quasidecidable-closed-under-ω-joins P-family (λ n → pr₁ (pr₂ (IH n))))) holds)
                                       ＝⟨ ap _holds (cscott f λ n → (P-family n , pr₁ (IH n)) , pr₁ (pr₂ (IH n))) ⟩
                     (∃ i ꞉ ℕ , ((f' ((P-family i , pr₁ (IH i)) , pr₁ (pr₂ (IH i)))) holds))
                      ＝⟨ ap (Exists ℕ) (dfunext fe λ n → ap _holds {(pr₁ (f ((P-family n , pr₁ (IH n)) , pr₁ (pr₂ (IH n)))))}
                                                                   {((f' 𝟙ₖ ∧ P-family n , pr₁ (IH n))) ∨ (f' 𝟘ₖ)}
                                                                   (Ω-extensionality pe fe (pr₁ (pr₂ (pr₂ (IH n)))) (pr₂ (pr₂ (pr₂ (IH n)))))) ⟩
                     (∃ i ꞉ ℕ , (((f' 𝟙ₖ ∧ P-family i , pr₁ (IH i)) ∨ (f' 𝟘ₖ)) holds)) ＝⟨ distributivity-lemma ⟩
                     ((f' 𝟙ₖ ∧ Exists ℕ P-family , ∃-is-prop ∨ (f' 𝟘ₖ)) holds) ∎ )

          where
           distributivity-lemma : Exists ℕ (λ i → (f' 𝟙ₖ ∧ P-family i , pr₁ (IH i) ∨ f' 𝟘ₖ) holds) ＝ ((f' 𝟙ₖ ∧ Exists ℕ P-family , ∃-is-prop ∨ f' 𝟘ₖ) holds)
           distributivity-lemma =
            pe ∃-is-prop
              (holds-is-prop ((f' 𝟙ₖ ∧ Exists ℕ P-family , ∃-is-prop ∨ f' 𝟘ₖ)))
              (∥∥-rec (holds-is-prop ((f' 𝟙ₖ ∧ Exists ℕ P-family , ∃-is-prop ∨ f' 𝟘ₖ)))
                λ (i , hyp-i) → ∥∥-rec (holds-is-prop (f' 𝟙ₖ ∧ Exists ℕ P-family , ∃-is-prop ∨ f' 𝟘ₖ))
                                       (cases (λ (fone , pfami) → ∣ inl (fone , ∣ i , pfami ∣) ∣) (∣_∣ ∘ inr)) hyp-i)
              (∥∥-rec ∃-is-prop (cases (λ (fone , ex-i) → ∥∥-rec ∃-is-prop (λ (i , pfami) → ∣ i , ∣ inl (fone , pfami) ∣ ∣) ex-i)
                                       λ fzero → ∣ 0 , ∣ inr fzero ∣ ∣))
 
\end{code}

We try something.

\begin{code}

 _is-of-level_ : (A : Ω 𝓤) → ℕ → 𝓤 ⁺ ̇
 _is-of-level_ (A , prop-A) 0 = is-decidable A × 𝟙 {𝓤 ⁺}
 _is-of-level_ (A , prop-A) (succ n) =
  ∃ F ꞉ (ℕ → Ω 𝓤) , (((i : ℕ) → (F i) is-of-level n) × (A ↔ ((∃ i ꞉ ℕ , (F i) holds))))

 being-of-level_is-prop : (n : ℕ) (Ap : Ω 𝓤 ) → is-prop (Ap is-of-level n)
 being-of-level zero is-prop (A , prop-A) = ×-is-prop (decidability-of-prop-is-prop fe prop-A) 𝟙-is-prop
 being-of-level succ n is-prop (A , prop-A) = ∃-is-prop

 being-of-level-uplift : (Ap : Ω 𝓤 ) → (n : ℕ) → (Ap is-of-level n) → (k : ℕ) → n ≤ℕ k → Ap is-of-level k
 being-of-level-uplift Ap n Ap-level-n =
  ℕ-induction (λ n-le-0 → transport (Ap is-of-level_) (zero-least'' n n-le-0) Ap-level-n)
               †
   where
    A = pr₁ Ap
    prop-A = pr₂ Ap
    
    † : (k : ℕ) → (n ≤ℕ k → Ap is-of-level k) → n ≤ℕ succ k → Ap is-of-level succ k
    † k IH n-le-sk = cases (λ n-le-k → ♣ (IH n-le-k)) (λ eq → transport (Ap is-of-level_) eq Ap-level-n) (≤-split n k n-le-sk)
     where
      ♣ : (Ap is-of-level k) → Ap is-of-level succ k
      ♣ Ap-level-k = ∣ (λ _ → Ap) , (λ _ → Ap-level-k) , (λ Aholds → ∣ 0 , Aholds ∣) , (λ ex-A → (∥∥-rec prop-A (λ (_ , Aholds) → Aholds) ex-A)) ∣
 
\end{code}

We want to prove that every quasidecidable proposition is of some level.
