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

module SyntheticTopology.SemiAndQuasidecidable
        (𝓤 𝓣 : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        where

open import NotionsOfDecidability.SemiDecidable fe pe pt
open import NotionsOfDecidability.QuasiDecidable fe pe pt
 hiding (is-semidecidable)
open import UF.ImageAndSurjection pt
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)

\end{code}

In this module, we study the correspondance between semidecidable and
quasidecidable propositions.

First, we prove that the induction principle for quasidecidable propositions is
valid for semidecidable propositions (without any form of choice needed).

\begin{code}

semidecidable-induction : ∀ {𝓤}
      (F : 𝓣 ̇ → 𝓤 ̇ )
    → ((P : 𝓣 ̇ ) → is-prop (F P))
    → F 𝟘
    → F 𝟙
    → ((P : ℕ → 𝓣 ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n))
    → (P : 𝓣 ̇ ) → is-semidecidable P → F P
semidecidable-induction F F-is-prop-valued Fzero Fone F-CUCJ P semi-P =
  ∥∥-rec (F-is-prop-valued P) † semi-P
   where
    open Equality 𝟚-is-set

    † : semidecidability-structure P → F P
    † (α , α-prop) = transport F (P-characterisation ⁻¹) (F-CUCJ P-fun ♣)

     where
      P-fun : ℕ → 𝓣 ̇
      P-fun n = (α n ＝ ₁) × 𝟙 {𝓣}

      P-fun-decidable : (n : ℕ) → (𝟙 ＝ P-fun n) + (𝟘 ＝ P-fun n)
      P-fun-decidable n =
       cases (λ αn → inl (⌜ 𝟙-＝-≃ (P-fun n) fe pe
                                  (×-is-prop 𝟚-is-set 𝟙-is-prop) ⌝⁻¹ (αn , ⋆)))
             (λ no-αn → inr (pe 𝟘-is-prop
                                (×-is-prop 𝟚-is-set 𝟙-is-prop)
                                𝟘-elim λ αn → 𝟘-elim (no-αn (pr₁ αn))))
             (𝟚-is-discrete (α n) ₁)

      P-characterisation : P ＝ (∃ n ꞉ ℕ , P-fun n)
      P-characterisation =
       pe (prop-if-semidecidable semi-P)
          ∃-is-prop
          (λ P-true →
            ∥∥-rec ∃-is-prop (λ (n , αn) → ∣ n , αn , ⋆ ∣) (⌜ α-prop ⌝ P-true))
          (∥∥-rec (prop-if-semidecidable semi-P)
                  λ (n , αn , _) → ⌜ α-prop ⌝⁻¹ ∣ n , αn ∣ )

      ♣ : (n : ℕ) → F (P-fun n)
      ♣ n = cases (λ eq → transport F eq Fone)
                  (λ eq → transport F eq Fzero)
                  (P-fun-decidable n)
\end{code}

Any instance of quasidecidable propositions contains the semidecidable ones.

\begin{code}

module _ (qde : quasidecidable-propositions-exist 𝓣 𝓤) where

 open quasidecidable-propositions-exist qde

 semidecidable-propositions-are-quasidecidable
  : (P : 𝓣 ̇) → is-semidecidable P → is-quasidecidable P
 semidecidable-propositions-are-quasidecidable
  = semidecidable-induction is-quasidecidable
                            being-quasidecidable-is-prop
                            𝟘-is-quasidecidable
                            𝟙-is-quasidecidable
                            quasidecidable-closed-under-ω-joins

\end{code}

The converse holds if and only if the semidecidable propositions are closed
under countable joins.
First, if the quasidecidable propositions are exactly the semidecidable ones,
then semidecidable propositions are closed under countable joins
(because quasidecidable are).

\begin{code}

 SCUCJ-if-quasidecidable-propositions-are-semidecidable
  :  ((P : 𝓣 ̇) → is-quasidecidable P → is-semidecidable P)
    → Semidecidable-Closed-Under-Countable-Joins 𝓣
 SCUCJ-if-quasidecidable-propositions-are-semidecidable hyp X Π-semi-X
  = hyp (∃ X)
        (quasidecidable-closed-under-ω-joins X
          (λ n → semidecidable-propositions-are-quasidecidable (X n)
                                                               (Π-semi-X n)))

\end{code}

And finally, given the fact that semidecidable propositions are closed under
countable joins, they form an instance of quasidecidable propositions.

\begin{code}

semidecidable-propositions-form-quasidecidable-if-SCUCJ
 : Semidecidable-Closed-Under-Countable-Joins 𝓣
   → quasidecidable-propositions-exist 𝓣 𝓣
semidecidable-propositions-form-quasidecidable-if-SCUCJ SCUCJ
 = quasidecidable-propositions is-semidecidable
                               (λ _ → being-semidecidable-is-prop)
                               𝟘-is-semidecidable
                               𝟙-is-semidecidable
                               SCUCJ
                               semidecidable-induction
\end{code}

Note that because of the induction principle, any two instances of
quasidecidable propositions do represent the same propositions. So we proved
here that THE quasidecidable propositions are precisely the semidecidable ones
if and only if the latter are closed under countable joins.

We formalize the first sentence here. `qde` and `qde'` being symmetric here,
we can use the following lemma swapping the two to get the equivalence.

\begin{code}

at-most-one-quasidecidable-set
 : (qde qde' : quasidecidable-propositions-exist 𝓣 𝓤) (P : 𝓣 ̇)
   → (quasidecidable-propositions-exist.is-quasidecidable qde P
   →  quasidecidable-propositions-exist.is-quasidecidable qde' P)
at-most-one-quasidecidable-set qde qde' P =
 quasidecidable-propositions-exist.quasidecidable-induction qde
   (quasidecidable-propositions-exist.is-quasidecidable qde')
   (quasidecidable-propositions-exist.being-quasidecidable-is-prop qde')
   (quasidecidable-propositions-exist.𝟘-is-quasidecidable qde')
   (quasidecidable-propositions-exist.𝟙-is-quasidecidable qde')
   (quasidecidable-propositions-exist.quasidecidable-closed-under-ω-joins qde')
   P

\end{code}
