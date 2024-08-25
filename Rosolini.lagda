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

module SyntheticTopology.SierpinskiObjectExamples.Rosolini
        (𝓤 : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        where

open import NotionsOfDecidability.SemiDecidable fe pe pt
open import SyntheticTopology.SetCombinators 𝓤₀ fe pe pt hiding (ℕ)
open import SyntheticTopology.SierpinskiObject fe pe pt
open import UF.ImageAndSurjection pt
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)

\end{code}

\begin{code}

_⇔⟨_⟩_ : (p : Ω 𝓤₀) {q r : Ω 𝓤₀}
           → (p ⇔ q) holds → (q ⇔ r) holds → (p ⇔ r) holds
_ ⇔⟨ (eq₁ , eq₁') ⟩ (eq₂ , eq₂') = eq₂ ∘ eq₁ , eq₁' ∘ eq₂'

_⇔∎ : (p : Ω 𝓤₀) → (p ⇔ p) holds
_⇔∎ _ = id , id

infix  1 _⇔∎
infixr 0 _⇔⟨_⟩_


Rosolini : Generalized-Sierpinski-Object 𝓤₀ 𝓤₀
Rosolini P = is-semidecidable (P holds) , being-semidecidable-is-prop

\end{code}

We here instanciate the modules needed to prove some basic lemmas.

\begin{code}

open Sierpinski-notations Rosolini
open import SyntheticTopology.Compactness 𝓤₀ 𝓤₀ fe pe pt Rosolini
open import SyntheticTopology.Overtness 𝓤₀ 𝓤₀ fe pe pt Rosolini
open import SyntheticTopology.SierpinskiAxioms 𝓤₀ 𝓤₀ fe pe pt Rosolini

\end{code}

Is it a dominance ?
We will use countable choice to prove that. See

{
Partial elements and recursion via dominances in
univalent type theory
Martín H. Escardó and Cory M. Knapp
School of Computer Science, University of Birmingham, UK
{m.escardo,cmk497}@cs.bham.ac.uk


We parametrize the module by a bijection ℕ² → ℕ. A future work would be to
actually instanciate one.

\begin{code}

ℕ²-ℕ-bijection-existence : 𝓤₀ ̇
ℕ²-ℕ-bijection-existence = Σ f ꞉ ((ℕ × ℕ) → ℕ) , qinv f

module _ (ℕ²-ℕ-bijection : ℕ²-ℕ-bijection-existence) where

 ℕ²-to-ℕ : ℕ × ℕ → ℕ
 ℕ²-to-ℕ = pr₁ ℕ²-ℕ-bijection

 ℕ-to-ℕ² : ℕ → ℕ × ℕ
 ℕ-to-ℕ² = pr₁ (pr₂ ℕ²-ℕ-bijection)

 invert : ℕ-to-ℕ² ∘ ℕ²-to-ℕ ∼ id × ℕ²-to-ℕ ∘ ℕ-to-ℕ² ∼ id
 invert =  pr₂ (pr₂ ℕ²-ℕ-bijection)

 min𝟚 : 𝟚 → 𝟚 → 𝟚
 min𝟚 ₀ _ = ₀
 min𝟚 ₁ b = b

 max𝟚 : 𝟚 → 𝟚 → 𝟚
 max𝟚 ₁ _ = ₁
 max𝟚 ₀ b = b

 diff : 𝟚 → 𝓤 ̇
 diff ₀ = 𝟘
 diff ₁ = 𝟙

 ₀-is-not-₁ : {𝓥 : Universe} → ₀ ＝ ₁ → 𝟘 {𝓥}
 ₀-is-not-₁ eq = 𝟘-elim (𝟘-is-not-𝟙 (ap diff eq))

 inverse-min : {a b : 𝟚} → min𝟚 a b ＝ ₁ → (a , b) ＝ (₁ , ₁)
 inverse-min {₀} {b} eq = 𝟘-elim (𝟘-is-not-𝟙 (ap diff eq))
 inverse-min {₁} {₁} eq = refl

 inverse-max : {a b : 𝟚} → max𝟚 a b ＝ ₁ → ((a ＝ ₁) + (b ＝ ₁))
 inverse-max {₀} {b} eq = inr eq
 inverse-max {₁} {b} eq = inl refl

 inverse-cases-left
  : {𝓥 : Universe} (A B X : 𝓥 ̇) → (is-prop A) → (f : A → X) (g : B → X) (a-plus-b : A + B) → (A → ¬ B) → (a : A) → cases f g (a-plus-b) ＝ cases f g (inl a)
 inverse-cases-left A B X prop-A f g (inl left) contr a = ap (cases f g) (ap inl (prop-A left a))
 inverse-cases-left A B X prop-A f g (inr right) contr a = 𝟘-elim (contr a right)

 inverse-cases-right
  : {𝓥 : Universe} (A B X : 𝓥 ̇) → (is-prop B) → (f : A → X) (g : B → X) (a-plus-b : A + B) → (B → ¬ A) → (b : B) → cases f g (a-plus-b) ＝ cases f g (inr b)
 inverse-cases-right A B X prop-B f g (inl left) contr b = 𝟘-elim (contr b left)
 inverse-cases-right A B X prop-B f g (inr right) contr b = ap (cases f g) (ap inr (prop-B right b))

 max-swap : (a b : 𝟚) → max𝟚 a b ＝ max𝟚 b a
 max-swap ₀ ₀ = refl
 max-swap ₀ ₁ = refl
 max-swap ₁ ₀ = refl
 max-swap ₁ ₁ = refl

 𝟚-has-decidable-equality : (x y : 𝟚) → is-decidable (x ＝ y)
 𝟚-has-decidable-equality ₀ ₀ = inl refl
 𝟚-has-decidable-equality ₀ ₁ = inr ₀-is-not-₁
 𝟚-has-decidable-equality ₁ ₀ = inr (₀-is-not-₁ ∘ (_⁻¹))
 𝟚-has-decidable-equality ₁ ₁ = inl refl

 𝟚-¬¬-elim : (x : 𝟚) → x ≠ ₁ → x ＝ ₀
 𝟚-¬¬-elim ₀ _ = refl
 𝟚-¬¬-elim ₁ p = 𝟘-elim (p refl)


\end{code}

\begin{code}

 Rosolini-contains-⊤ : contains-top holds
 Rosolini-contains-⊤ = 𝟙-is-semidecidable

 Rosolini-contains-⊥ : contains-bot holds
 Rosolini-contains-⊥ = 𝟘-is-semidecidable

 Rosolini-has-transitive-openness
  : Countable-Semidecidable-Choice 𝓤₀ → openness-is-transitive holds
 Rosolini-has-transitive-openness CSC =
  (SDA-gives-transitive-openness ∘
   dominance-axiom-if-closure-under-Σ ∘
    closure-under-Σ-if-closure-under-subsingleton-countable-joins ∘
     SCSC-implies-semidecidable-closed-under-subsingleton-countable-joins)
      (λ A B → CSC A)
  where
   SDA-gives-transitive-openness : (Semidecidable-Dominance-Axiom 𝓤₀ 𝓤₀)
                                 → openness-is-transitive holds
   SDA-gives-transitive-openness SDA p semi-p q p-gives-semi-q =
    SDA (p holds) semi-p (q holds) p-gives-semi-q

 Rosolini-is-dominance
  : Countable-Semidecidable-Choice 𝓤₀ → is-synthetic-dominance holds
 Rosolini-is-dominance CSC =
  Rosolini-contains-⊤ , Rosolini-has-transitive-openness CSC

\end{code}

Closed under binary joins and meets (without CSC).

\begin{code}

 Rosolini-closed-under-binary-meets
  : (p q : Ω 𝓤₀) → Rosolini p holds → Rosolini q holds → Rosolini (p ∧ q) holds
 Rosolini-closed-under-binary-meets p q semi-p semi-q =
  ∥∥-rec₂ (holds-is-prop (Rosolini (p ∧ q))) † semi-p semi-q
   where
    † : semidecidability-structure (p holds) →
          semidecidability-structure (q holds) → Rosolini (p ∧ q) holds
    † (α , α-prop) (β , β-prop) = ∣ γ , γ-prop ∣
     where
      γ : ℕ → 𝟚
      γ = (λ (n , m) → min𝟚 (α n) (β m)) ∘ ℕ-to-ℕ²

      γ-prop : ((p ∧ q) holds) ≃ (∃ n ꞉ ℕ , γ n ＝ ₁)
      γ-prop =
       logically-equivalent-props-are-equivalent (holds-is-prop (p ∧ q))
                                                 ∃-is-prop
                                                 if only-if
       where
        ♠ : Σ (λ n → α n ＝ ₁) → Σ (λ n → β n ＝ ₁) → ∥ Σ (λ v → γ v ＝ ₁) ∥
        ♠ (n , αn) (m , βm) =
         ∣ (ℕ²-to-ℕ (n , m)) , (γ (ℕ²-to-ℕ (n , m)) ＝⟨ eq ⟩
                                 min𝟚 (α n) (β m)   ＝⟨ ap₂ min𝟚 αn βm ⟩
                                 ₁ ∎) ∣
         where
          eq : uncurry min𝟚 (×functor α β ((ℕ-to-ℕ² ∘ ℕ²-to-ℕ) (n , m))) ＝
                uncurry min𝟚 (α n , β m)
          eq = ap (uncurry min𝟚 ∘ (×functor α β)) ((pr₁ invert) (n , m))

        if : (p ∧ q) holds → ∃ n ꞉ ℕ ,  γ n ＝ ₁
        if (pholds , qholds) = ∥∥-rec₂ ∃-is-prop
                                       ♠
                                       (⌜ α-prop ⌝  pholds)
                                       (⌜ β-prop ⌝  qholds)

        only-if : ∃ a ꞉ ℕ , γ a ＝ ₁ → (p ∧ q) holds
        only-if = ∥∥-rec (holds-is-prop (p ∧ q)) ♣
         where
          ♣ : Σ (λ a → γ a ＝ ₁) → (p ∧ q) holds
          ♣ (a , γa) = ⌜ α-prop ⌝⁻¹ ∣ n , ap pr₁ both-eq-₁  ∣ ,
                       ⌜ β-prop ⌝⁻¹ ∣ m , ap pr₂ both-eq-₁  ∣
           where
            n = pr₁ (ℕ-to-ℕ² a)
            m = pr₂ (ℕ-to-ℕ² a)

            both-eq-₁ : (α n , β m) ＝ (₁ , ₁)
            both-eq-₁ = inverse-min γa

\end{code}

Now with binary joins. We still do not need CSC.

\begin{code}

 Rosolini-closed-under-binary-joins
  : (p q : Ω 𝓤₀) → Rosolini p holds → Rosolini q holds → Rosolini (p ∨ q) holds
 Rosolini-closed-under-binary-joins p q semi-p semi-q =
  ∥∥-rec₂ (holds-is-prop (Rosolini (p ∨ q))) † semi-p semi-q
   where
    † : semidecidability-structure (p holds) →
          semidecidability-structure (q holds) → Rosolini (p ∨ q) holds
    † (α , α-prop) (β , β-prop) = ∣ γ , γ-prop  ∣
     where
      γ : ℕ → 𝟚
      γ n = max𝟚 (α n) (β n)

      γ-prop : ((p ∨ q) holds) ≃ (∃ n ꞉ ℕ , γ n ＝ ₁)
      γ-prop =
        logically-equivalent-props-are-equivalent (holds-is-prop (p ∨ q))
                                                  ∃-is-prop
                                                  if only-if

       where
        if : (p ∨ q) holds → (∃ n ꞉ ℕ , γ n ＝ ₁)
        if = ∥∥-rec ∃-is-prop (cases casep caseq)
         where
          casep : p holds → Exists ℕ (λ n → γ n ＝ ₁)
          casep pholds = ∥∥-rec ∃-is-prop
                                (λ (n , αn)
                                  → ∣ n , ap (λ f → f (β n)) (ap max𝟚 αn)  ∣)
                                (⌜ α-prop  ⌝ pholds )

          caseq : q holds → Exists ℕ (λ n → γ n ＝ ₁)
          caseq qholds = ∥∥-rec ∃-is-prop
                                (λ (n , βn)
                                  → ∣ n , (max-swap (α n) (β n)
                                         ∙ ap (λ f → f (α n)) (ap max𝟚 βn)) ∣)
                                  (⌜ β-prop ⌝ qholds )

        only-if : (∃ n ꞉ ℕ , γ n ＝ ₁) → (p ∨ q) holds
        only-if = ∥∥-rec (holds-is-prop (p ∨ q)) ♠

         where
          ♠ : Σ (λ n → γ n ＝ ₁) → (p ∨ q) holds
          ♠ (n , γn) = ♠' (inverse-max γn)

           where
            ♠' : (α n ＝ ₁) + (β n ＝ ₁) → (p ∨ q) holds
            ♠' = cases (λ αn → ∣ inl (⌜ α-prop  ⌝⁻¹ ∣ n , αn  ∣) ∣)
                       (λ βn → ∣ inr (⌜ β-prop  ⌝⁻¹ ∣ n , βn ∣)  ∣)

\end{code}

We write down the principle of continuity for function from the Sierpinski
set to itself.

\begin{code}

 Sfun : 𝓤₁ ̇
 Sfun = Σ f ꞉ (Ω 𝓤₀ → Ω 𝓤₀) , (Ɐ u ꞉ Ω 𝓤₀ , Rosolini u ⇒ Rosolini (f u)) holds

 Continuity-Sfun : 𝓤₁ ̇
 Continuity-Sfun = ((f , coh-f) : Sfun)
              → (p : Ω 𝓤₀) (α : (ℕ → 𝟚))
              → ((p holds) ≃ (∃ n ꞉ ℕ , α n ＝ ₁))
              → (∃ nα ꞉ ℕ , ((q : Ω 𝓤₀) (β : (ℕ → 𝟚))
                             → (q holds) ≃ (∃ m ꞉ ℕ , β m ＝ ₁)
                             → ((k : ℕ) → k ≤ℕ nα → α k ＝ β k )
                               → ((f p holds) ↔ (f q holds))))
   
\end{code}

\begin{code}

 continuity-Sfun-is-false : ¬ (Continuity-Sfun)
 continuity-Sfun-is-false continuity = ∥∥-rec 𝟘-is-prop † n⊥-existence
  where
   n⊥-existence : ∃ n⊥ ꞉ ℕ , ((q : Ω 𝓤₀) (β : ℕ → 𝟚) →
             (q holds) ≃ Exists ℕ (λ m → β m ＝ ₁) →
             ((k : ℕ) → k ≤ℕ n⊥ → ₀ ＝ β k) → (⊥ holds) ↔ (q holds))
   n⊥-existence = continuity (id , λ _ → id)
                   ⊥
                   (λ _ → ₀)
                   (logically-equivalent-props-are-equivalent
                     𝟘-is-prop
                     ∃-is-prop
                     𝟘-elim
                     (∥∥-rec 𝟘-is-prop (λ (n , abs) → ₀-is-not-₁ abs)))

   † : (Σ n⊥ ꞉ ℕ , ((q : Ω 𝓤₀) (β : ℕ → 𝟚) →
            (q holds) ≃ Exists ℕ (λ m → β m ＝ ₁) →
            ((k : ℕ) → k ≤ℕ n⊥ → ₀ ＝ β k) → (⊥ holds) ↔ (q holds))) → 𝟘
   † (n⊥ , n⊥-prop) = ⊥-is-not-⊤ {𝓤₀}
                                 (holds-gives-equal-⊤ pe fe ⊥ †')

    where
     γ : ℕ → 𝟚
     γ n = cases (λ n⊥-lt-n → ₁)
              (λ n-le-n⊥ → ₀)
              (order-split n⊥ n)
     †' : ⊥ holds
     †' = pr₂ (n⊥-prop ⊤ γ
              (logically-equivalent-props-are-equivalent 𝟙-is-prop
                                                         ∃-is-prop
                                                         (λ _ → ∣ succ n⊥ , inverse-cases-left (n⊥ <ℕ succ n⊥)
                                                                                            (succ n⊥ ≤ℕ n⊥)
                                                                                            𝟚
                                                                                            (<-is-prop-valued n⊥ (succ n⊥))
                                                                                            (λ n⊥-lt-n → ₁)
                                                                                            (λ n-le-n⊥ → ₀)
                                                                                            (order-split n⊥ (succ n⊥))
                                                                                            (λ _ sn⊥-le-n⊥ → not-less-than-itself n⊥ sn⊥-le-n⊥)
                                                                                            (<-succ n⊥) ∣)
                                                         (λ _ → ⊤-holds))
                                                         λ k k-le-n⊥ → (inverse-cases-right (n⊥ <ℕ k)
                                                                                            (k ≤ℕ n⊥)
                                                                                            𝟚
                                                                                            (≤-is-prop-valued k n⊥)
                                                                                            (λ n⊥-lt-n → ₁)
                                                                                            (λ n-le-n⊥ → ₀)
                                                                                            (order-split n⊥ k)
                                                                                            (λ k-le-n⊥' n⊥-lt-k → not-less-than-itself k (≤-<-trans k n⊥ k k-le-n⊥' n⊥-lt-k))
                                                                                            k-le-n⊥) ⁻¹)
              ⊤-holds

\end{code}


\begin{code}

 Semi-closed-under-negations-refutes-phoa
  : Semidecidable-Closed-Under-Negations 𝓤₀ → (¬ₚ (phoa’s-principle Rosolini-contains-⊤ Rosolini-contains-⊥)) holds
 Semi-closed-under-negations-refutes-phoa SCUN phoa = 𝟘-elim †'
  where
   † : (not fe ⊤ ⇔ (not fe ⊤ ∧ ⊤ ∨ not fe ⊥)) holds
   † = phoa (λ (p , semi-p) → (not fe p , SCUN (p holds) semi-p))
            (⊤ , Rosolini-contains-⊤)
   
   †' : 𝟘
   †' = pr₂ † ∣ inr 𝟘-elim ∣ ⊤-holds

\end{code}

We now parametrize the following by the `Countable-Semidecidable-Choice`, in
order to 

\begin{code}

 module _ (CSC : Countable-Semidecidable-Choice 𝓤₀) where
  SCUCJ : Semidecidable-Closed-Under-Countable-Joins 𝓤₀
  SCUCJ = CSC-implies-semidecidable-closed-under-countable-joins CSC

  Scott-continuous : (Ωₒ → Ωₒ) → 𝓤₁ ̇
  Scott-continuous f =
   (P : (ℕ → Ωₒ))  
    → ((i : ℕ) → (pr₁ (P i) holds → pr₁ (P (succ i)) holds))
      → pr₁ (f ((Ǝₚ i ꞉ ℕ , pr₁ (P i)) , SCUCJ (_holds ∘ pr₁ ∘ P) (pr₂ ∘ P)))
        ＝ (Ǝₚ i ꞉ ℕ , pr₁ (f (P i)))

  Scott-continuity-gives-directed-binary-scott-continuity
   : (f : Ωₒ → Ωₒ)
     → Scott-continuous f
     → ((p , semi-p) (q , semi-q) : Ωₒ)
     → (p ⇒ q) holds
     → pr₁ (f ((p ∨ q) , Rosolini-closed-under-binary-joins p q semi-p semi-q))
      ＝ pr₁ (f (p , semi-p)) ∨ pr₁ (f (q , semi-q)) 
  Scott-continuity-gives-directed-binary-scott-continuity
   f scott-f (p , semi-p) (q , semi-q) p-gives-q  =
    pr₁ (f ((p ∨ q) , Rosolini-closed-under-binary-joins p q semi-p semi-q)) ＝⟨ ap (pr₁ ∘ f) (to-Σ-＝ (p-or-q-is-p-or-q-join , being-semidecidable-is-prop _ _)) ⟩
    pr₁ (f ((Ǝₚ i ꞉ ℕ , pr₁ (p-or-q-join i)) , SCUCJ (_holds ∘ pr₁ ∘ p-or-q-join) (pr₂ ∘ p-or-q-join))) ＝⟨ scott-f p-or-q-join p-or-q-join-is-increasing ⟩
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
      
  Scott-continuity-gives-motonicity
   : {(p , semi-p) (q , semi-q) : Ωₒ} (f : Ωₒ → Ωₒ) → Scott-continuous f → (p ⇒ q) holds → (pr₁ (f (p , semi-p)) ⇒ pr₁ (f (q , semi-q))) holds
  Scott-continuity-gives-motonicity {(p , semi-p)} {q , semi-q} f scott-f p-gives-q f-p-holds
   = transport (_holds ∘ pr₁ ∘ f)
               (to-Σ-＝ ((q-lemma ⁻¹)
                       , being-semidecidable-is-prop (transport (λ p₁ → Rosolini p₁ holds)
                                                     (q-lemma ⁻¹)
                                                     (Rosolini-closed-under-binary-joins p q semi-p semi-q)) semi-q))
               (transport _holds
                          ((Scott-continuity-gives-directed-binary-scott-continuity f scott-f (p , semi-p) (q , semi-q) p-gives-q) ⁻¹)
                          ∣ inl f-p-holds ∣)
    where
     q-lemma : (q ＝ (p ∨ q))
     q-lemma = Ω-extensionality pe fe (∣_∣ ∘ inr) (∥∥-rec (holds-is-prop q) (cases p-gives-q id))

  Scott-continuity-gives-phoa’s-principle
   : ((f : Ωₒ → Ωₒ) → Scott-continuous f) → phoa’s-principle Rosolini-contains-⊤ Rosolini-contains-⊥ holds
  Scott-continuity-gives-phoa’s-principle scott-continuity f (p , semi-p) =
   ∥∥-rec (holds-is-prop ((pr₁ (f (p , semi-p)) ⇔ (pr₁ (f (⊤ , Rosolini-contains-⊤)) ∧ p ∨ pr₁ (f (⊥ , Rosolini-contains-⊥))))))
          equivalence
          semi-p

   where
    or-and : Ω 𝓤₀
    or-and = (pr₁ (f (⊤ , Rosolini-contains-⊤)) ∧ p ∨ pr₁ (f (⊥ , Rosolini-contains-⊥)))
    
    equivalence : semidecidability-structure (p holds) →
                    (pr₁ (f (p , semi-p)) ⇔ or-and) holds
    equivalence (α , α-prop) = implication₁ , implication₂

     where
      γ : ℕ → ℕ → 𝟚
      γ i n = cases (λ _ → α n) (λ _ → ₀) (order-split n (succ i))

      p-family-decidable : (k : ℕ) → ((∃ n ꞉ ℕ , (n ≤ℕ k) × (α n ＝ ₁))
                          + ¬ (∃ n ꞉ ℕ , ((n ≤ℕ k) × (α n ＝ ₁))))
      p-family-decidable k =
       cases (λ (n , n-le-k , αn , _) → inl ∣ n , n-le-k , αn  ∣)
             (λ no-n-found → inr (∥∥-rec 𝟘-is-prop
                                         λ (false-n , false-n-le-k , αfalse-n)
                                          → not-less-than-itself false-n
                                            (≤-<-trans false-n k false-n
                                                       false-n-le-k
                                                       (<-≤-trans k
                                                                  (succ k)
                                                                  false-n
                                                                  (≤-refl k)
                                                                  (no-n-found
                                                                   false-n
                                                                   αfalse-n)))))
             (βμ (λ m → α m ＝ ₁)
                 (λ m → 𝟚-has-decidable-equality (α m) ₁)
                 (succ k))

      p-family : ℕ → Ω 𝓤₀
      p-family i = (∃ n ꞉ ℕ , ((n ≤ℕ i) × (α n ＝ ₁))), ∃-is-prop

      p-family-is-increasing : (i : ℕ)
                               → ((p-family i)
                                 ⇒ p-family (succ i)) holds
      p-family-is-increasing i =
       ∥∥-rec ∃-is-prop (λ (n , n-le-i , αn) →
         ∣ n , ≤-trans n i (succ i) n-le-i (≤-succ i) , αn ∣)
        
      p-is-join-of-p-family : (p holds ≃ (Ǝₚ i ꞉ ℕ , p-family i) holds)
      p-is-join-of-p-family =
       logically-equivalent-props-are-equivalent
         (holds-is-prop p)
         ∃-is-prop
         ((λ pholds → ∥∥-rec ∃-is-prop
                             (λ (n , αn) → ∣ n , ∣ n , ≤-refl n , αn  ∣ ∣)
                             (⌜ α-prop ⌝ pholds))) 
         (∥∥-rec (holds-is-prop p)
                 (λ (i , p-fam-i)
                   → ⌜ α-prop ⌝⁻¹ (∥∥-rec ∃-is-prop
                                          (λ (n , n-le-i , αn)
                                           → ∣ n , αn ∣) p-fam-i)))
      
      using-scott : pr₁ (f (p , semi-p)) ＝ Ǝₚ i ꞉ ℕ , (pr₁ (f (p-family i , decidable-props-are-semidecidable ∃-is-prop (p-family-decidable i))))
      using-scott =
       pr₁ (f (p , semi-p))
        ＝⟨ ap (pr₁ ∘ f) (to-Σ-＝ (to-Σ-＝ (pe (holds-is-prop p) ∃-is-prop ⌜ p-is-join-of-p-family ⌝  ⌜ p-is-join-of-p-family ⌝⁻¹
                                           , being-prop-is-prop fe _ _)
                                , being-semidecidable-is-prop _ _)) ⟩
                     pr₁ (f  ((Ǝₚ i ꞉ ℕ , p-family i) ,
                         CSC-implies-semidecidable-closed-under-countable-joins CSC
                         (_holds ∘ p-family)
                         (λ x →  decidable-props-are-semidecidable ∃-is-prop (p-family-decidable x))))
                           ＝⟨ scott-continuity f (λ i → p-family i , (decidable-props-are-semidecidable ∃-is-prop (p-family-decidable i))) p-family-is-increasing ⟩
                     (Ǝₚ i ꞉ ℕ , (pr₁ (f (p-family i , decidable-props-are-semidecidable ∃-is-prop (p-family-decidable i))))) ∎
      
      implication₁ : (pr₁ (f (p , semi-p)) ⇒ or-and) holds
                      
      implication₁ =
       transport (λ - → (- ⇒ or-and) holds)
                  (using-scott ⁻¹)
                  (∥∥-rec (holds-is-prop or-and)
                          λ (i , iprop) → cases (∥∥-rec (holds-is-prop or-and)
                                                λ (n , n-le-i , αn)
                                                 → ∣ inl (transport (_holds ∘ pr₁ ∘ f)
                                                                            (to-Σ-＝ (holds-gives-equal-⊤ pe fe (p-family i) ∣ n , n-le-i , αn ∣ , being-semidecidable-is-prop _ _)) iprop
                                                   , ⌜ α-prop ⌝⁻¹ ∣ n , αn ∣) ∣)
                                                (λ no-n-found → ∣ inr (transport (_holds ∘ pr₁ ∘ f) (to-Σ-＝ (false-gives-equal-⊥ pe fe (p-family i holds) ∃-is-prop no-n-found , being-semidecidable-is-prop _ _)) iprop) ∣ )
                                                (p-family-decidable i))

      implication₂ : (or-and ⇒ pr₁ (f (p , semi-p))) holds
      implication₂ =
       ∥∥-rec (holds-is-prop (pr₁ (f (p , semi-p))))
              (cases (λ (f-⊤-holds , pholds)
                     → transport (_holds ∘ pr₁ ∘ f)
                                 (to-Σ-＝ (((holds-gives-equal-⊤ pe fe p pholds) ⁻¹)
                                   , (being-semidecidable-is-prop _ _)))
                                 f-⊤-holds)
                     (Scott-continuity-gives-motonicity f (scott-continuity f) 𝟘-elim))
    

\end{code}


\begin{code}

  phoa’s-principle-gives-Scott-continuity
   : phoa’s-principle Rosolini-contains-⊤ Rosolini-contains-⊥ holds
   → (f : Ωₒ → Ωₒ) → Scott-continuous f
  phoa’s-principle-gives-Scott-continuity phoa f p-family _
   = pr₁ (f ((Ǝₚ i ꞉ ℕ , pr₁ (p-family i)) , SCUCJ (_holds ∘ pr₁ ∘ p-family) (pr₂ ∘ p-family))) ＝⟨ phoa-eq ((Ǝₚ i ꞉ ℕ , pr₁ (p-family i))
                                                                                                              , SCUCJ (_holds ∘ pr₁ ∘ p-family) (pr₂ ∘ p-family)) ⟩
      pr₁ (f (⊤ , Rosolini-contains-⊤)) ∧ (Ǝₚ i ꞉ ℕ , pr₁ (p-family i)) ∨ pr₁ (f (⊥ , Rosolini-contains-⊥)) ＝⟨ distributivity-lemma ⟩
      (Ǝₚ i ꞉ ℕ , (pr₁ (f (⊤ , Rosolini-contains-⊤)) ∧ pr₁ (p-family i) ∨ pr₁ (f (⊥ , Rosolini-contains-⊥)))) ＝⟨ ap (∃ₚ[꞉]-syntax ℕ) (dfunext fe (λ i → phoa-eq (p-family i) ⁻¹)) ⟩
      Ǝₚ i ꞉ ℕ , pr₁ (f (p-family i)) ∎
      
       where
        phoa-eq : ((q , semi-q) : Ωₒ)
                → pr₁ (f (q , semi-q)) ＝ ((pr₁ (f (⊤ , Rosolini-contains-⊤)) ∧ q) ∨ pr₁ (f (⊥ , Rosolini-contains-⊥)))
        phoa-eq (q , semi-q) = Ω-extensionality pe fe (pr₁ (phoa f (q , semi-q))) (pr₂ (phoa f (q , semi-q)))
        
        distributivity-lemma : pr₁ (f (⊤ , Rosolini-contains-⊤)) ∧ (Ǝₚ i ꞉ ℕ , pr₁ (p-family i)) ∨ pr₁ (f (⊥ , Rosolini-contains-⊥))
                               ＝  (Ǝₚ i ꞉ ℕ , (pr₁ (f (⊤ , Rosolini-contains-⊤)) ∧ pr₁ (p-family i) ∨ pr₁ (f (⊥ , Rosolini-contains-⊥))))
        distributivity-lemma =
          Ω-extensionality pe fe (∥∥-rec ∃-is-prop (cases (λ (f-⊤-holds , hyp) → ∥∥-rec ∃-is-prop (λ (i , iprop) → ∣ i , ∣ inl (f-⊤-holds , iprop) ∣ ∣) hyp)
                                                          λ f-⊥-holds → ∣ 0 , ∣ inr f-⊥-holds ∣ ∣))
                                 (∥∥-rec ∥∥-is-prop (λ (i , iprop) → ∥∥-rec ∥∥-is-prop (cases (λ (f-⊤-holds , pfam-i-holds) → ∣ inl (f-⊤-holds , ∣ i , pfam-i-holds ∣) ∣)
                                                                                                 λ f-⊥-holds → ∣ inr f-⊥-holds ∣) iprop))

\end{code}

\begin{code}

 test : ((P : 𝓤₀ ̇) → is-prop P → P + ¬ P) → 𝟚 ≃ Ω 𝓤₀
 test EM = qinveq 𝟚→Ω (Ω→𝟚 , proof , proof')

  where

   𝟚→Ω : 𝟚 → Ω 𝓤₀
   𝟚→Ω ₀ = ⊥
   𝟚→Ω ₁ = ⊤

   Ω→𝟚 : Ω 𝓤₀ → 𝟚
   Ω→𝟚 (P , prop-P) = cases (λ _ → ₁) (λ _ → ₀) (EM P prop-P)
   
   proof : (λ x → Ω→𝟚 (𝟚→Ω x)) ∼ (λ x → x)
   proof ₀ = inverse-cases-right 𝟘 (¬ 𝟘) 𝟚 (Π-is-prop fe (λ _ → 𝟘-is-prop)) (λ _ → ₁) (λ _ → ₀) (EM 𝟘 𝟘-is-prop) id id
   proof ₁ = inverse-cases-left 𝟙 (¬ 𝟙) 𝟚 𝟙-is-prop (λ _ → ₁) (λ _ → ₀) (EM 𝟙 𝟙-is-prop) ¬¬-intro ⊤-holds
   
   proof' : (λ x → 𝟚→Ω (Ω→𝟚 x)) ∼ (λ x → x)
   proof' (P , prop-P) =
    cases (λ eq → transport (λ - → (𝟚→Ω (Ω→𝟚 -)) ＝ -) (eq ⁻¹)
                            (transport (λ - →  𝟚→Ω - ＝ ⊤) (inverse-cases-left 𝟙 (¬ 𝟙) 𝟚 𝟙-is-prop (λ _ → ₁) (λ _ → ₀) (EM 𝟙 𝟙-is-prop) ¬¬-intro ⋆ ⁻¹) refl))
          (λ eq → transport (λ - → (𝟚→Ω (Ω→𝟚 -)) ＝ -) (eq ⁻¹)
                            ((transport (λ - →  𝟚→Ω - ＝ ⊥) (inverse-cases-right 𝟘 (¬ 𝟘) 𝟚 (Π-is-prop fe (λ _ → 𝟘-is-prop)) (λ _ → ₁) (λ _ → ₀) (EM 𝟘 𝟘-is-prop) id id ⁻¹) refl)))
          (decidable-truth-values-are-⊥-or-⊤ pe fe P prop-P (EM P prop-P))


  
  

\end{code}
