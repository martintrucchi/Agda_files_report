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

module SyntheticTopology.SierpinskiObjectExamples.AllProps
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


We define here the Sierpinski object corresponding to {⊤}.
That is, a proposition P is affirmable if and only if it is equal to ⊤,
which is equivalent to "P holds" (see lemma "holds-gives-equal-⊤")

We could generalize to a universe 𝓥 greater than 𝓤, by lifting both the
proposition and the proof it is indeed a proposition

\begin{code}

AllProps : Generalized-Sierpinski-Object 𝓤 𝓤
AllProps P = ⊤

\end{code}

We here instanciate the modules needed to prove some basic lemmas.

\begin{code}

open Sierpinski-notations AllProps
open import SyntheticTopology.Compactness 𝓤 𝓤 fe pe pt AllProps
open import SyntheticTopology.Overtness 𝓤 𝓤 fe pe pt AllProps
open import SyntheticTopology.SierpinskiAxioms 𝓤 𝓤 fe pe pt AllProps

\end{code}

And then we prove the lemmas

\begin{code}

all-props-is-dominance : is-synthetic-dominance holds
all-props-is-dominance = ⊤-holds , λ u _ p _ → ⋆

ct : contains-top holds
ct = ⊤-holds

cb : contains-bot holds
cb = ⊤-holds

\end{code}

\begin{code}

module _ (𝒳 : hSet 𝓤) where
 private
  X = underlying-set 𝒳
  set-X = pr₂ 𝒳

 every-set-is-compact : is-compact 𝒳 holds
 every-set-is-compact (U , open-U) = ⋆

 every-set-is-overt : is-overt 𝒳 holds
 every-set-is-overt (U , open-U) = ⋆

\end{code}
