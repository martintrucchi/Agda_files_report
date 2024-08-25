---
title:        Investigation of compactness with 𝟚 as the Sierpinski object
author:       Martin Trucchi
date-started: 2024-05-30
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import NotionsOfDecidability.Complemented
open import NotionsOfDecidability.Decidable
open import TypeTopology.CompactTypes hiding (is-compact)
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.FunExt
open import UF.Logic
open import UF.Powerset
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

module SyntheticTopology.NotionOfCompactness
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        where


open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open import SyntheticTopology.SierpinskiObject fe pe pt
open import TypeTopology.WeaklyCompactTypes (λ 𝓥 𝓦 → fe {𝓥} {𝓦}) pt

\end{code}

We first define the `𝟚` Sierpinski object. That is, a proposition `P` is open
if `is-decidable P` holds.

\begin{code}

𝟚-sierpinski : Generalized-Sierpinski-Object 𝓤₀ 𝓤₀
𝟚-sierpinski P = is-decidable (P holds) ,
                 decidability-of-prop-is-prop fe (holds-is-prop P)

open import SyntheticTopology.Compactness 𝓤₀ 𝓤₀ fe pe pt 𝟚-sierpinski
open import SyntheticTopology.Overtness 𝓤₀ 𝓤₀ fe pe pt 𝟚-sierpinski
open import SyntheticTopology.SierpinskiAxioms 𝓤₀ 𝓤₀ fe pe pt 𝟚-sierpinski
open Sierpinski-notations 𝟚-sierpinski

\end{code}

We prove that this Sierpinski object is a dominance.
The proof of transitive-openness seems long but it is just saying that

If u is decidable, and u → "p is decidable", then "u and p" is decidable :

 - either u is false, so "u and p" is also false thus decidable
 - either u is true, but now p is decidable so
          - either p is true, so "u and p" is true thus decidable
          - either p is false, so "u and p" is false thus decidable

\begin{code}

𝟚-is-dominance : is-synthetic-dominance holds
𝟚-is-dominance =  ⊤-is-decidable , 𝟚-has-transitive-openness
 where
  ⊤-is-decidable : is-open-proposition ⊤ holds
  ⊤-is-decidable = inl ⊤-holds

  𝟚-has-transitive-openness : openness-is-transitive holds
  𝟚-has-transitive-openness u affirmable-u p u-gives-affirmable-p =
   † affirmable-u
    where
     affirmable-and : Ω 𝓤₀
     affirmable-and = is-open-proposition (u ∧ p)

     u-and-p-gives-affirmable-and : u holds
                                  → p holds
                                  → affirmable-and holds

     u-and-p-gives-affirmable-and u-holds p-holds = inl (u-holds , p-holds)


     u-and-not-p-gives-affirmable-and : u holds
                                      → (¬ₚ p) holds
                                      → affirmable-and holds

     u-and-not-p-gives-affirmable-and u-holds not-p-holds =
       inr (λ u-and-p → not-p-holds (pr₂ u-and-p))


     dec-p-gives-affirmable-and : u holds
                                → (p holds) + ((¬ₚ p) holds)
                                → affirmable-and holds

     dec-p-gives-affirmable-and u-holds dec-p =
      cases (u-and-p-gives-affirmable-and u-holds)
            (u-and-not-p-gives-affirmable-and u-holds)
            dec-p

     u-gives-affirmable-and : u holds → affirmable-and holds

     u-gives-affirmable-and u-holds =
      (dec-p-gives-affirmable-and u-holds) (u-gives-affirmable-p u-holds)

     not-u-gives-affirmable-and : (¬ₚ u) holds → affirmable-and holds

     not-u-gives-affirmable-and not-u-holds =
      inr (λ u-and-p → not-u-holds (pr₁ u-and-p))

     † : (u holds) + ((¬ₚ u) holds) → affirmable-and holds

     † dec-u = cases u-gives-affirmable-and not-u-gives-affirmable-and dec-u


\end{code}


Now that we know that 𝟚-sierpinski is a dominance, we investigate the notion of
compactness it defines and relate it to the one that are defined in
TypeTopology.CompactTypes and TypeTopology.WeaklyCompactTypes

It turns out that ∃-Compactness (capital C) defined in
TypeTopology.CompactTypes is exactly our synthetic notion of overtness.
(Overtness indeed, not compactness !)

Note that synthetic notions require sets, so we prove the lemmas for sets.

We first prove these two little lemmas :

\begin{code}

₀-is-not-₁ : ₀ ≠ ₁
₀-is-not-₁ pr = 𝟘-elim (𝟘-is-not-𝟙 (ap c pr))
 where
  c : 𝟚 → 𝓤₀ ̇
  c ₁ = 𝟙
  c ₀ = 𝟘

𝟚-has-decidable-equality : (z : 𝟚) → (z ＝ ₀) + (z ＝ ₁)
𝟚-has-decidable-equality = 𝟚-induction {𝓤₀}
                                       {λ z → (z ＝ ₀) + (z ＝ ₁)}
                                       (inl refl)
                                       (inr refl)

\end{code}

The direction ∃-Compact → overt  :

\begin{code}

open CompactTypesPT pt

module _ (𝒳 : hSet 𝓤₀) where
 private
  X = underlying-set 𝒳
  set-X = pr₂ 𝒳

 ∃-Compact-gives-overt : is-∃-Compact X
                       → is-overt 𝒳 holds

 ∃-Compact-gives-overt ∃-Compact-X (P , dec-P) =
  ∃-Compact-X (_holds ∘ P) dec-P

\end{code}

Now the converse. The proof is similar to is-compact → is-Compact in
CompactTypes.
In fact, although it is not in the file (for now), we can prove that
∃-Compactness is equivalent to ∃-compactness (in WeaklyCompactTypes) in a
similar way it is already done in CompactTypes for Σ-Compactness and
Σ-compactness.

\begin{code}

 overt-gives-∃-Compact : is-overt 𝒳 holds
                       → is-∃-Compact X { 𝓤₀ }

 overt-gives-∃-Compact overt-X A A-complemented =
  ii (overt-X ((λ x → p x ＝ₚ ₀) , † ))
  where
   open Equality 𝟚-is-set
   
   i : Σ p ꞉ (X → 𝟚) , ((x : X) → (p x ＝ ₀ → A x) × (p x ＝ ₁ → ¬ A x))
   i = characteristic-function A-complemented

   p : X → 𝟚
   p = pr₁ i

   † :  (is-intrinsically-open 𝒳 (λ x → p x ＝ₚ ₀)) holds
   † x = cases (λ px₀ → inl px₀  )
               (λ px₁ → inr (λ px₀ → ₀-is-not-₁ ((px₀ ⁻¹) ∙ px₁)))
               (𝟚-has-decidable-equality (p x))

   ii : (∃ x ꞉ X , p x ＝ ₀) + ¬ (∃ x ꞉ X , p x ＝ ₀) → is-decidable (∃ A)
   ii (inl ex-x) = inl (∥∥-rec ∃-is-prop
                               (λ (x , px₀) → ∣ x , (pr₁ ((pr₂ i) x) px₀ ) ∣)
                               ex-x)
   ii (inr ¬-ex-x) =
    inr (λ A-prop →
     ∥∥-rec 𝟘-is-prop
            (λ (x , Ax) → pr₂ (pr₂ i x) (cases (λ px₀
                                                 → 𝟘-elim (¬-ex-x ∣ x , px₀ ∣))
                                               id
                                               (𝟚-has-decidable-equality (p x)))
                                        Ax)
            A-prop)

\end{code}

Remark : With our initial definition of " intrinsically-open` ", which
mentionned the factorization through the Sierpinski object, do we get an
equivalence with Σ-Compactness and overtness ?

We now prove that our synthetic notion of compactness in this setting is
equivalent to the notion of Π-Compactness. The proofs are similar to the above.

\begin{code}

 is-synthetic-compact : Ω 𝓤₁
 is-synthetic-compact = is-compact 𝒳

 Π-Compact-gives-synthetic-compact
  : is-Π-Compact X
  → is-synthetic-compact holds

 Π-Compact-gives-synthetic-compact Π-Compact-X (P , dec-P) =
  Π-Compact-X (pr₁ ∘ P) dec-P


 synthetic-compact-gives-Π-Compact
  : is-synthetic-compact holds
  → is-Π-Compact X {𝓤₀}

 synthetic-compact-gives-Π-Compact synth-compact-X A A-complemented =
   ii (synth-compact-X ((λ x → p x ＝ₚ ₀) , † ))
  where
   open Equality 𝟚-is-set
   
   i : Σ p ꞉ (X → 𝟚) , ((x : X) → (p x ＝ ₀ → A x) × (p x ＝ ₁ → ¬ A x))
   i = characteristic-function A-complemented

   p : X → 𝟚
   p = pr₁ i

   † :  (is-intrinsically-open 𝒳 (λ x → p x ＝ₚ ₀)) holds
   † x = cases (λ px₀ → inl px₀  )
               (λ px₁ → inr (λ px₀ → ₀-is-not-₁ ((px₀ ⁻¹) ∙ px₁)))
               (𝟚-has-decidable-equality (p x))


   ii : ((x : X) → p x ＝ ₀) + ¬ ((x : X) → p x ＝ ₀) → is-decidable (Π A)
   ii (inl all-x-p) = inl (λ x → (pr₁ ((pr₂ i) x)) (all-x-p x) )
   ii (inr not-all-x-p) =
    inr (λ all-x-A →
          not-all-x-p (λ x → cases id
                                   (λ px₁ → 𝟘-elim ((pr₂ ((pr₂ i) x))
                                                    px₁
                                                    (all-x-A x)))
                                   (𝟚-has-decidable-equality (p x))))

\end{code}
