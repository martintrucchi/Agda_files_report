---
title:          Small proposition 2.13
author:         Martin Trucchi
date-started:   2024-05-28
dates-modified: [2024-06-06]
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import SyntheticTopology.SierpinskiObject
open import UF.FunExt
open import UF.Logic
open import UF.Powerset
open import UF.PropTrunc
open import UF.Sets
open import UF.Subsingletons
open import UF.SubtypeClassifier

module SyntheticTopology.Prop2-13
        (𝓤 : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (𝕊 : Generalized-Sierpinski-Object fe pe pt 𝓤 𝓤)
        where

open import SyntheticTopology.SetCombinators 𝓤 fe pe pt
open import UF.ImageAndSurjection pt

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open Sierpinski-notations fe pe pt 𝕊

\end{code}

We look at proposition 2.13 in Lešnik's thesis.

\begin{code}

module _ (𝒳 : hSet 𝓤) where
 private
  X = underlying-set 𝒳
 open import SyntheticTopology.Overtness 𝓤 𝓤 fe pe pt 𝕊
 proposition-2-13-left-to-right
  : is-overt 𝒳 holds
  → ((Y , sY) : hSet 𝓤)
  → ((U , open-U) : 𝓞 (𝒳 ×ₛ (Y , sY)))
  → is-intrinsically-open (Y , sY)
                          (λ y → Ǝₚ z ꞉ (X × Y) , (z ∈ₚ U ∧ (pr₂ z ＝ y) , sY))
                          holds
 proposition-2-13-left-to-right overt-X (Y , sY) (U , open-U) y
  = ⇔-open (Ǝₚ x ꞉ X , (x , y) ∈ₚ U)
            (Ǝₚ z ꞉ (X × Y) , (z ∈ₚ U ∧ (pr₂ z ＝ₚ y)))
            ((∥∥-rec ∃-is-prop λ (x , xy-in-U) → ∣ (x , y) , xy-in-U , refl ∣)
            , ∥∥-rec ∃-is-prop λ ((x , y') , (Uxy' , y'-eq-y))
                                 → ∣ x , transport (λ - → U (x , -) holds)
                                                   y'-eq-y
                                                   Uxy'  ∣)
            (overt-X ((λ x → (x , y) ∈ₚ U) , λ x → open-U (x , y)))
   where
    open Equality sY

\end{code}

The type of the formula

\begin{code}

 proposition-2-13-right-to-left-type
  : {𝓥 𝓦 : Universe} (X : 𝓥 ̇) → (Y : 𝓦 ̇) → (U : 𝓟 (X × Y)) → Y → 𝓥 ⊔ 𝓦 ̇
 proposition-2-13-right-to-left-type X Y U y
  = ∃ (x , y') ꞉ X × Y , (x , y') ∈ U × (y ＝ y')
  
\end{code}
