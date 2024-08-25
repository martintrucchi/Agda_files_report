\begin{code}

{-# OPTIONS --safe --without-K  #-}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.Powerset
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.SubtypeClassifier

module SyntheticTopology.SierpinskiObjectExamples.SingletonTop
        (𝓤 : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        where

open import SyntheticTopology.SetCombinators 𝓤 fe pe pt
open import SyntheticTopology.SierpinskiObject fe pe pt
open import UF.ImageAndSurjection pt
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)

\end{code}

We define here the Sierpinski object corresponding to `{⊤}`.
That is, a proposition `P` is open if and only if it is equal to `⊤`,
which is equivalent to `P holds` (see lemma `holds-gives-equal-⊤` in
`UF.SubtypeClassifier`)

We could generalize to a universe `𝓥` greater than `𝓤`, by lifting both the
proposition and the proof it is indeed a proposition

\begin{code}

SingletonTop : Generalized-Sierpinski-Object 𝓤 𝓤
SingletonTop P = P

\end{code}

We here instanciate the modules needed to prove some basic lemmas.

\begin{code}

open Sierpinski-notations SingletonTop
open import SyntheticTopology.Compactness 𝓤 𝓤 fe pe pt SingletonTop
open import SyntheticTopology.Overtness 𝓤 𝓤 fe pe pt SingletonTop
open import SyntheticTopology.SierpinskiAxioms 𝓤 𝓤 fe pe pt SingletonTop

\end{code}

And then we prove the lemmas

\begin{code}

singleton-⊤-is-dominance : is-synthetic-dominance holds
singleton-⊤-is-dominance =
 ⊤-holds , λ u aff-u p u-holds-imp-p-holds → aff-u , u-holds-imp-p-holds aff-u

module _ (𝒳 : hSet 𝓤) where
 private
  X = underlying-set 𝒳
  set-X = pr₂ 𝒳

 every-set-is-compact : (is-compact 𝒳) holds
 every-set-is-compact (P , open-P) = open-P

 inhabited-sets-are-overt : ∥ X ∥ → (is-overt 𝒳) holds
 inhabited-sets-are-overt x-prop (P , open-P) =
  ∥∥-rec ∃-is-prop (λ x → ∣ x , open-P x ∣) x-prop
 

\end{code}
