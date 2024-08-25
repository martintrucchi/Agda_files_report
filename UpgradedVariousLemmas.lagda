---
title:        Lemmas in Synthetic Topology
author:       ["Martin Trucchi" , "Vincent Rahli"]
date-started: 2024-06-03
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import NotionsOfDecidability.DecidableClassifier
open import SyntheticTopology.SierpinskiObject
open import UF.Base
open import UF.ClassicalLogic
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.FunExt
open import UF.Powerset
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier
open import UF.UniverseEmbedding

module SyntheticTopology.UpgradedVariousLemmas
        (𝓤 : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (𝕊 : Generalized-Sierpinski-Object fe pe pt 𝓤 (𝓤 ⁺))
        where


open import UF.Subsingletons-FunExt
open import SyntheticTopology.Compactness 𝓤 (𝓤 ⁺) fe pe pt 𝕊
open import SyntheticTopology.SetCombinators 𝓤 fe pe pt
open import SyntheticTopology.SierpinskiAxioms 𝓤 (𝓤 ⁺) fe pe pt 𝕊
open import SyntheticTopology.SubObjects 𝓤 (𝓤 ⁺) fe pe pt 𝕊
open import UF.ImageAndSurjection pt
open import UF.Logic

open AllCombinators pt fe
open binary-unions-of-subsets pt
open PropositionalSubsetInclusionNotation fe
open PropositionalTruncation pt hiding (_∨_)
open Sierpinski-notations fe pe pt 𝕊

\end{code}

We formalize here the proofs of results included in [1].

Our Sierpinski object is required to be a dominance.

\begin{code}

module _ ((ct-⊤ , open-transitive) : is-synthetic-dominance holds) where

\end{code}

We define an alias for being closed under binary meets, which is directly
implied by open-transitive.
We also define a useful shortcut (which works because ⊤ is open)

\begin{code}

 cl-∧ : closed-under-binary-meets holds
 cl-∧ = open-transitive-gives-cl-∧ open-transitive

 holds-gives-open : (p : Ω 𝓤) → p holds → is-open-proposition p holds
 holds-gives-open p p-holds =
  transport (_holds ∘ is-open-proposition)
            ((holds-gives-equal-⊤ pe fe p p-holds) ⁻¹)
            ct-⊤

\end{code}
 
We now define a resizing function, `subset-downlift`. The purpose of this
function is to transform a subset `V : 𝓟 𝒳` into a subset `V ∩ U : 𝓟 (𝕋 U)`.

\begin{code}

 module hSetNotations (𝒳 : hSet 𝓤) where
  private
   X = underlying-set 𝒳
   set-X = pr₂ 𝒳

  subset-downlift : (U V : 𝓟 X) → 𝓟 (𝕋 U)
  subset-downlift U V (x , c) = x ∈ₚ V

  subset-downlift-intersect
   : (U V : 𝓟 X) → (subset-downlift U V) ＝ (subset-downlift U (U ∩ V))
  subset-downlift-intersect U V =
   dfunext fe (λ (x , c) →
    ⇔-gives-＝ pe
               (x ∈ₚ V)
               (x ∈ₚ (U ∩ V))
               (holds-gives-equal-⊤ pe
                                    fe
                                    (x ∈ₚ V ⇔ x ∈ₚ (U ∩ V))
                                    ((λ Vx → c , Vx) , pr₂)))

  subset-uplift : (U : 𝓟 X) → (V : 𝓟 (𝕋 U)) → 𝓟 X
  subset-uplift U V = λ x → Ǝₚ P ꞉ x ∈ U , V (x , P)

\end{code}

In the definition above, the condition `Ǝₚ p ꞉ x ∈ₚ U holds` might not be
natural.
At first thought, we wanted to define it like :
`subset-uplift U V = λ x → x ∈ₚ U ⇒ x ∈ₚ V`. The problem here is that `V`
requires a pair `(x , P)` with `x : X` and `P : (x ∈ₚ U holds)` (which is
`x ∈ U)`.
Therefore we are forced to have a proof of that kind to define the statement
`x ∈ₚ V`. However, we can prove that with those defintions, `subset-downlift`
and `subset-uplift` are inverse functions of each other (for `V ⊆ U` !).
This is mainly because
as the type `x ∈ₚ U` is a prop, by definition `P ＝ Q` for `P Q : x ∈ₚ U`.
The specific witness of belonging to `U` is therefore irrelevant.

\begin{code}

  uplift-downlift-cancel
   : (U V : 𝓟 X)
   → V ⊆ U
   → (x : X)
   → (x ∈ₚ (((subset-uplift U) ∘ (subset-downlift U)) V) ⇔ x ∈ₚ V) holds
   
  uplift-downlift-cancel U V incl x = p₁ , p₂
   where
    p₁ : (x ∈ₚ (subset-uplift U ∘ subset-downlift U) V ⇒ x ∈ₚ V) holds
    p₁ comp = ∥∥-rec (holds-is-prop (x ∈ₚ V)) (λ (Ux , V') → V') comp
    
    p₂ : (x ∈ₚ V ⇒ x ∈ₚ (subset-uplift U ∘ subset-downlift U) V) holds
    p₂ Vx = ∣ incl x Vx , Vx ∣
 
  downlift-uplift-cancel
    : (U : 𝓟 X)
    → (V : 𝓟 (𝕋 U))
    → ((x , Ux) : 𝕋 U)
    → ((x , Ux) ∈ₚ (((subset-downlift U) ∘ (subset-uplift U)) V)
      ⇔ (x , Ux) ∈ₚ V) holds
   
  downlift-uplift-cancel U V (x , Ux) = p₁ , p₂
   where
    p₁ : ((x , Ux) ∈ₚ (subset-downlift U ∘ subset-uplift U) V ⇒ (x , Ux) ∈ₚ V)
         holds
    p₁ comp = ∥∥-rec (holds-is-prop ((x , Ux) ∈ₚ V))
                     (λ (Uxholds , p) →
                       transport (λ - → V (x , -) holds)
                                 (holds-is-prop (x ∈ₚ U) Uxholds Ux)
                                 p)
                     comp
   
    p₂ : ((x , Ux) ∈ₚ V ⇒ (x , Ux) ∈ₚ (subset-downlift U ∘ subset-uplift U) V)
         holds
    p₂ V-xux = ∣ Ux , V-xux  ∣

\end{code}

In our setting, we already have a dominance, the Sierpinski object, which
defines a Synthetic Topology.

We prove that this Topology is indeed a Synthetic Topology in the meaning of
Definition 4.4 in [1]

The second lemma is actually a proof of 4.5, which is more general but
equivalent with 4.4.S2

\begin{code}

 singleton-⊤-is-open : is-intrinsically-open 𝟙ₛ full holds
 singleton-⊤-is-open _ = ct-⊤

 module _ (𝒳 : hSet 𝓤) where
  private
   X = underlying-set 𝒳
   set-X = pr₂ 𝒳

  open hSetNotations 𝒳

  topology-induced-by-dominance-is-well-defined
   : ((U , open-U) : 𝓞 𝒳)
   → (V : 𝓟 X)
   → (incl : V ⊆ U)
   → is-intrinsically-open (𝕋ₛ 𝒳 U) (subset-downlift U V)  holds
   → is-intrinsically-open 𝒳 V holds

  topology-induced-by-dominance-is-well-defined (U , open-U) V incl trV x =
   ⇔-open (x ∈ₚ (U ∩ V))
          (x ∈ₚ V)
          (pr₂ , λ Vx → incl x Vx , Vx)
          (open-transitive (x ∈ₚ U) (open-U x) (x ∈ₚ V) (λ Ux → trV (x , Ux)))

  topology-induced-by-dominance-is-well-defined'
   : ((U , open-U) : 𝓞 𝒳)
   → (V : 𝓟 (𝕋 U))
   → is-intrinsically-open (𝕋ₛ 𝒳 U) V holds
   → is-intrinsically-open 𝒳 (subset-uplift U V) holds

  topology-induced-by-dominance-is-well-defined' (U , open-U) V open-V =
   topology-induced-by-dominance-is-well-defined (U , open-U)
                                                 (subset-uplift U V)
                                                 (λ x up-holds →
                                                  ∥∥-rec
                                                   (holds-is-prop (x ∈ₚ U))
                                                   pr₁
                                                   up-holds)
                                                 †

   where
    † : is-intrinsically-open (𝕋ₛ 𝒳 U)
                              (((subset-downlift U) ∘ (subset-uplift U)) V)
        holds
    † (x , Ux) =
     ⇔-transport pe
                 ((x , Ux) ∈ₚ V)
                 ((x , Ux) ∈ₚ ((subset-downlift U) ∘ (subset-uplift U)) V)
                 (_holds ∘ is-open-proposition)
                 (⇔-swap pe
                       ((x , Ux) ∈ₚ ((subset-downlift U) ∘ (subset-uplift U)) V)
                       (V (x , Ux))
                       (downlift-uplift-cancel U V (x , Ux)))
                 (open-V (x , Ux))

\end{code}

Proposition 4.6

\begin{code}

  open-in-self : is-intrinsically-open 𝒳 full holds
  open-in-self _ = ct-⊤

  binary-∩-of-open-is-open
   : ((U , open-U) (V , open-V) : 𝓞 𝒳) → is-intrinsically-open 𝒳 (U ∩ V) holds
  binary-∩-of-open-is-open (U , open-U) (V , open-V) x =
   cl-∧ (x ∈ₚ U) (x ∈ₚ V) ((open-U x) , (open-V x))

\end{code}

Proposition 4.7

\begin{code}

  module _ (𝒴 : hSet 𝓤) where
   private
    Y = underlying-set 𝒴
    set-Y = pr₂ 𝒴

   all-functions-are-continuous
    : (f : X → Y)
    → ((V , open-V) : 𝓞 𝒴)
    → is-intrinsically-open 𝒳 (λ x → (f x) ∈ₚ V) holds
   all-functions-are-continuous f (V , open-V) x = open-V (f x)

\end{code}

Proposition 5.10

\begin{code}

  substandard-gives-decidable-subsets-are-open
   : contains-bot holds
   → (D : 𝓟 X)
   → is-complemented-subset D
   → is-intrinsically-open 𝒳 D holds 
  substandard-gives-decidable-subsets-are-open ct-⊥ D complemented-D x =
   cases (holds-gives-open (x ∈ₚ D))
         (λ not-Dx → transport (_holds ∘ is-open-proposition)
                               ((false-gives-equal-⊥ pe
                                                     fe
                                                     (x ∈ D)
                                                     (holds-is-prop (x ∈ₚ D))
                                                     not-Dx
                                )⁻¹)
                               ct-⊥)
         (complemented-D x)

\end{code}

7.1 is hard : predicativity.
We can't write :
`is-compact' (for some set 𝒳) = is-intrinsically-open (𝓞 𝒳) ❴ X ❵`, because of
the universe of ❴ X ❵

7.8

\begin{code}

 is-compact-prop-type : Ω 𝓤 → Ω (𝓤 ⁺ ⊔ (𝓤 ⁺))
 is-compact-prop-type p = is-compact (Ωₛ p)

 is-compact-prop-open-implication : Ω 𝓤 → Ω (𝓤 ⁺ ⊔ (𝓤 ⁺))
 is-compact-prop-open-implication p =
  Ɐ u ꞉ Ω 𝓤 , is-open-proposition u ⇒ is-open-proposition (p ⇒ u)

 open subdefinitions
 
 is-compact-prop-subcompact : Ω 𝓤 → Ω (𝓤 ⁺ ⊔ (𝓤 ⁺))
 is-compact-prop-subcompact p = is-subcompact 𝟙ₛ (λ ⋆ → p)

\end{code}

We prove the equivalence between these definitions.

\begin{code}

 compact-type-gives-compact-open-implication
  : (Ɐ p ꞉ Ω 𝓤 , is-compact-prop-type p ⇒ is-compact-prop-open-implication p) holds
 compact-type-gives-compact-open-implication p compact₁ u open-u = compact₁ (Q , λ _ → open-u)
  where
   Q : (p holds) → Ω 𝓤
   Q = λ _ → u

{-
 compact-open-implication-gives-compact-subcompact
  : (Ɐ p ꞉ Ω 𝓤 , is-compact-prop-open-implication p ⇒ is-compact-prop-subcompact p) holds
 compact-open-implication-gives-compact-subcompact p compact₂ (u , open-u) =
  ⇔-open (p ⇒ u ⋆)
         (Ɐ (x , px) ꞉ 𝕋 (λ ⋆ → p) , x ∈ₚ u)
         ((λ p-gives-u (x , px) → p-gives-u px)
          , λ forall-hyp pholds → forall-hyp (⋆ , pholds))
         (compact₂ (u ⋆) (open-u ⋆))

 compact-subcompact-gives-compact-open-implication
  : (Ɐ p ꞉ Ω 𝓤 , is-compact-prop-subcompact p ⇒ is-compact-prop-open-implication p) holds
 compact-subcompact-gives-compact-open-implication p compact₃ u open-u =
  ⇔-open (Ɐ (⋆ , px) ꞉ (𝕋 (λ ⋆ → p)) , u)
         (p ⇒ u)
         (eq₁ , eq₂)
         (compact₃ ((λ ⋆ → u) , (λ ⋆ → open-u)))

   where
    eq₁ : ((Ɐ (⋆ , px) ꞉ (𝕋 (λ ⋆ → p)) , u) ⇒ (p ⇒ u)) holds
    eq₁ forall-hyp pholds = forall-hyp (⋆ , pholds)
    
    eq₂ : ((p ⇒ u) ⇒ (Ɐ (⋆ , px) ꞉ (𝕋 (λ ⋆ → p)) , u)) holds
    eq₂ p-gives-u (⋆ , px) = p-gives-u px
-}


 is-open-subproposition : Ω 𝓤 → Ω 𝓤 → Ω (𝓤 ⁺)
 is-open-subproposition u p = (u ⇒ p) ∧ (p ⇒ (is-open-proposition u))

 is-compact-prop-subproposition : Ω 𝓤 → Ω (𝓤 ⁺)
 is-compact-prop-subproposition f =
  Ɐ u ꞉ Ω 𝓤 , is-open-subproposition u f ⇒ is-open-proposition (f ⇒ u)

 compact-subproposition-gives-compact-type
  : (Ɐ f ꞉ (Ω 𝓤) ,
     is-compact-prop-subproposition f ⇒ is-compact-prop-type f ) holds
 compact-subproposition-gives-compact-type f closed-f (u , open-u) =
  ⇔-open (f ⇒ Ǝₚ proof ꞉ f holds , u proof )
         (Ɐ proof ꞉ f holds , u proof)
         ((λ hyp fholds → ∥∥-rec (holds-is-prop (u fholds)) (λ (proof , uproof) → transport (_holds ∘ u) (holds-is-prop f proof fholds) uproof) (hyp fholds)) ,
         λ hyp fholds → ∣ fholds , hyp fholds ∣)
         (closed-f (Ǝₚ proof ꞉ f holds , u proof) ((λ ex → ∥∥-rec (holds-is-prop f) (λ (fholds , _) → fholds) ex) , λ fholds → ⇔-open (u fholds) (Ǝₚ proof ꞉ f holds , u proof) ((λ ufholds → ∣ fholds , ufholds  ∣) , λ ex → ∥∥-rec (holds-is-prop (u fholds)) (λ (proof , uproof) → transport (_holds ∘ u) (holds-is-prop f proof fholds) uproof) ex) (open-u fholds)))

 compact-type-gives-compact-subproposition : (Ɐ f ꞉ (Ω 𝓤) , is-compact-prop-type f ⇒ is-compact-prop-subproposition f ) holds
 compact-type-gives-compact-subproposition f compact₁ u subprop-u = (compact₁ ((λ _ → u) , λ proof → pr₂ subprop-u proof))


 module _ (𝒳 : hSet 𝓤) where
  private
   X = pr₁ 𝒳
   set-X = pr₂ 𝒳

  closed-subset : 𝓟 X → Ω (𝓤 ⁺)
  closed-subset F =
   Ɐ (U , open-U) ꞉ 𝓞 (𝕋ₛ 𝒳 F) ,
     (is-intrinsically-open 𝒳 (λ x → (Ɐ p ꞉ (x ∈ F) , (x , p) ∈ₚ U)))

  closed-subset-from-compact-subproposition : 𝓟 X → Ω (𝓤 ⁺)
  closed-subset-from-compact-subproposition F =
   Ɐ x ꞉ X , is-compact-prop-subproposition (x ∈ₚ F)
   

\end{code}

Closed subset of compact is compact

\begin{code}
{-
  closed-subset-related-compact
   : (F : 𝓟 X)
   → closed-subset F holds
   → is-compact 𝒳 holds
   → is-subcompact 𝒳 F holds
  
  closed-subset-related-compact F closed-F compact-X (P , open-P) = {!!}
-}

  closed-subset-of-compact-is-compact
   : (F : 𝓟 X)
   → closed-subset-from-compact-subproposition F holds
   → is-compact 𝒳 holds
   → is-subcompact 𝒳 F holds
  closed-subset-of-compact-is-compact F closed-F compact-X (P , open-P) =
   ⇔-open (Ɐ x ꞉ X , x ∈ₚ F ⇒ (x ∈ₚ F ∧ x ∈ₚ P))
          (Ɐ x ꞉ X , x ∈ₚ F ⇒ x ∈ₚ P)
          ((λ hyp x fx → pr₂ (hyp x fx)) , (λ hyp x fx → fx , (hyp x fx)))
          (compact-X ((λ z → z ∈ₚ F ⇒ z ∈ₚ F ∧ z ∈ₚ P)
                     , λ z → closed-F z
                                      (z ∈ₚ F ∧ z ∈ₚ P)
                                      (pr₁ , λ Fz → cl-∧ (z ∈ₚ F)
                                                         (z ∈ₚ P)
                                                         ((holds-gives-open (z ∈ₚ F) Fz)
                                                         , (open-P z)))))

\end{code}

Hausdorff

\begin{code}

 Δ : ((X , set-X) : hSet 𝓤) → (𝓟 (X × X))
 Δ (X , set-X) = λ (x , y) → x ＝ₚ y
  where
   open Equality set-X

 module _ (𝒳 : hSet 𝓤) where
  private
   X = pr₁ 𝒳
   set-X = pr₂ 𝒳
   
  open Equality set-X

  is-hausdorff-closed : Ω (𝓤 ⁺)
  is-hausdorff-closed =
   closed-subset (𝒳 ×ₛ 𝒳) (Δ 𝒳)
  
  is-hausdorff-closed-from-subproposition : Ω (𝓤 ⁺)
  is-hausdorff-closed-from-subproposition =
   closed-subset-from-compact-subproposition (𝒳 ×ₛ 𝒳) (Δ 𝒳) 

  is-hausdorff-proposition : Ω (𝓤 ⁺)
  is-hausdorff-proposition =
   Ɐ (u , open-u) ꞉ 𝓞 𝒳 ,
    Ɐ x ꞉ X , Ɐ y ꞉ X , is-open-proposition ((x ＝ₚ y) ⇒ x ∈ₚ u)


\end{code}

compact set of haussdorff is closed

\begin{code}

  compact-in-hausdorff-is-closed
   : (K : 𝓟 X)
   → is-subcompact 𝒳 K holds
   → is-hausdorff-proposition holds 
   → closed-subset 𝒳 K holds
   
  compact-in-hausdorff-is-closed K subcompact-K hausdorff-X (U , open-U) x =
   ⇔-open (Ɐ k ꞉ X , k ∈ₚ K ⇒ (Ɐ x-eq-k ꞉ (x ＝ k) , (Ɐ Kk ꞉ (k ∈ K) ,
                              (x , transport (_holds ∘ K) (x-eq-k ⁻¹) Kk) ∈ₚ U)))
          (Ɐ Kx ꞉ (x ∈ K) , (x , Kx) ∈ₚ U)
          ((λ hyp Kx → hyp x Kx refl Kx) ,
           λ hyp k Kk x-eq-k Kk' → hyp (transport (_holds ∘ K) (x-eq-k ⁻¹) Kk'))
          (subcompact-K ((λ z → (Ɐ x-eq-z ꞉ (x ＝ z)
                                , (Ɐ Kz ꞉ (z ∈ K) ,
                                  U (x , transport (_holds ∘ K) (x-eq-z ⁻¹) Kz))))
                                   , † ))

   where
    † : (z : X) → is-open-proposition (Ɐ x-eq-z ꞉ (x ＝ z) , (Ɐ Kz ꞉ (z ∈ K) ,
                          U (x , transport (_holds ∘ K) (x-eq-z ⁻¹) Kz))) holds
    † z = ⇔-open ((x ＝ₚ z) ⇒ (Ɐ p ꞉ (x ∈ K) , (x , p) ∈ₚ U))
                 (Ɐ x-eq-z ꞉ (x ＝ z) , (Ɐ Kz ꞉ (z ∈ K) ,
                          U (x , transport (_holds ∘ K) (x-eq-z ⁻¹) Kz)))

                 ({!!} , {!!})
                 (hausdorff-X ((λ y → Ɐ p ꞉ (y ∈ K) , (y , p) ∈ₚ U)
                              , λ y → {!!}) x z)
   

{-
  compact-in-hausdorff-is-closed'
   : (A : 𝓟 X)
   → is-subcompact 𝒳 A holds
   → is-hausdorff-closed-from-subproposition holds 
   → closed-subset 𝒳 A holds
   
  compact-in-hausdorff-is-closed' = {!!}
-}
\end{code}

in hausdorff, closed ⇔ compact

EK2017

connection 
