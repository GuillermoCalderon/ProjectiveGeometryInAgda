{-# OPTIONS --no-eta-equality #-} 

open import Relation.Nullary
open import Data.Empty
open import Data.Sum
open import Data.Product hiding (swap)
open import Level using (_⊔_)
open import Relation.Binary.Apartness
import Data.Nat as Nat
open import Data.Fin
open import Function using (_$_)
open import Data.Fin.Setoid
open import ProjectivePlane
import Relation.Binary.EqReasoning as EqR

module ProjectivePlane.CompleteNPoint.Triangle.Perspective
       {a b c d e}
       (PP : ProjectivePlane.ProjectivePlane a b c d e) where

open ProjectivePlane.ProjectivePlane PP
open import ProjectivePlane.CompleteNPoint PP
open import ProjectivePlane.PropertiesGeneral PP
open import ProjectivePlane.CompleteNPoint.Triangle PP
open  ProjectivePlane.Setoid♯Instances PP
open  ProjectivePlane.Rel♯Instances PP



TriangleP : Set _
TriangleP = Complete-N-Point 3




`0 `1 `2 : Fin 3
`0 = zero
`1 = suc zero
`2 = suc (suc zero)

0♯1 : `0 ♯ `1
0♯1 = λ{()}

0♯2 : `0 ♯ `2
0♯2 = λ{()}

1♯2 : `1 ♯ `2
1♯2 = λ{()}





record AreDistinct  (T T' : TriangleP) : Set ( b ⊔ d) where
  field
    -- distinct vértices
    vrt♯ : ∀ i → (T $∙ i) ♯ (T' $∙ i)

    -- distinct sides
    sd♯  : ∀ {i j} (i♯j : i ♯ j) → (edge T i♯j ) ♯ (edge T' i♯j )


record ArePerspectiveCenter (T T' : TriangleP) : Set (a ⊔ b ⊔ d ⊔ e) where
  field
    Center : Point
    areDistinct : AreDistinct T T'
  open AreDistinct areDistinct --public

  field
    Center-∉-T  : ∀ {i j} → {i♯j : i ♯ j} → Center ∉ edge T i♯j
    Center-∉-T' : ∀ {i j} → {i♯j : i ♯ j} → Center ∉ edge T' i♯j
    perspective : ∀ i → Center ∈ join (vrt♯ i)



record ArePerspectiveAxis (T T' : TriangleP) : Set (b ⊔ c ⊔ e ⊔ d) where
  field
    axis : Line
    areDistinct : AreDistinct T T'
  open AreDistinct areDistinct -- public

  field
    axis-∉-T  : ∀ {i} → T  $∙ i ∉ axis
    axis-∉-T' : ∀ {i} → T' $∙ i ∉ axis
    perspective : ∀ {i j} (i♯j : i ♯ j) → meet (sd♯ i♯j) ∈ axis


--  reduced and flat definitions
--
record AreDistinct₁ (T T' : TriangleP) : Set ( b ⊔ d) where
  field
    vrt-0 : T $∙ `0 ♯ T' $∙ `0
    vrt-1 : T $∙ `1 ♯ T' $∙ `1
    vrt-2 : T $∙ `2 ♯ T' $∙ `2


    sd-01  : {p : `0 ♯ `1} → edge T p ♯ edge T' p
    sd-02  : {p : `0 ♯ `2} → edge T p ♯ edge T' p
    sd-12  : {p : `1 ♯ `2} → edge T p ♯ edge T' p


record ArePerspectiveAxis₁ (T T' : TriangleP) : Set (b ⊔ c ⊔ e ⊔ d) where
  field
    axis : Line
    areDistinct : AreDistinct T T'
    axis-∉-T  : ∀ {i} → T  $∙ i ∉ axis
    axis-∉-T' : ∀ {i} → T' $∙ i ∉ axis
 
  open AreDistinct areDistinct
  field
    persp01 : {p : `0 ♯ `1}  → meet (sd♯ p) ∈ axis
    persp02 : {p : `0 ♯ `2}  → meet (sd♯ p) ∈ axis
    persp12 : {p : `1 ♯ `2}  → meet (sd♯ p) ∈ axis



toAreDistinct :  ∀ {T T'} → AreDistinct₁ T T' → AreDistinct T T' 
toAreDistinct {T} {T'} ad₁ = record { vrt♯ = vrt♯ ; sd♯ = λ {i} {j} → sd♯ i j }

           where 
             open AreDistinct₁ ad₁ 

             vrt♯ : (i : Fin 3) → T $∙ i ♯ T' $∙ i
             vrt♯ zero             = vrt-0
             vrt♯ (suc zero)       = vrt-1
             vrt♯ (suc (suc zero)) = vrt-2
             vrt♯ (suc (suc (suc ()))) 

             sd♯ : (i j : Fin 3) → (i♯j : i ♯ j) → edge T i♯j ♯ edge T' i♯j
             sd♯ zero (suc zero)    i♯j              = sd-01
             sd♯ zero (suc (suc zero)) _               = sd-02
             sd♯ (suc zero) (suc (suc zero)) _         = sd-12
             sd♯ (suc zero) zero i♯j                     = ⟨ join-comm ⟩⇐  sd-01 {symmetry i♯j} ⇒⟨ join-comm ⟩
             sd♯  (suc (suc zero)) (zero) i♯j            = ⟨ join-comm ⟩⇐  sd-02 {symmetry i♯j} ⇒⟨ join-comm ⟩
             sd♯ (suc (suc zero)) (suc zero) i♯j         = ⟨ join-comm ⟩⇐  sd-12 {symmetry i♯j} ⇒⟨ join-comm ⟩
             sd♯ zero zero i♯j                         = ⊥-elim $ refl i♯j
             sd♯ (suc zero) (suc zero) i♯j             = ⊥-elim $ refl i♯j
             sd♯ (suc (suc zero)) (suc (suc zero)) i♯j = ⊥-elim $ refl i♯j
             sd♯ (suc (suc (suc ()))) _ _ 
             sd♯ _ (suc (suc (suc ()))) _ 


toPerspectiveAxis : ∀ {T T'} → ArePerspectiveAxis₁ T T' → ArePerspectiveAxis T T'
toPerspectiveAxis {T} {T'} apa-TT' 
  = record
      { axis = axis
      ; areDistinct = areDistinct
      ; axis-∉-T = axis-∉-T
      ; axis-∉-T' = axis-∉-T'
      ; perspective = λ {i} {j} → persp i j
      }
  where open ArePerspectiveAxis₁ apa-TT'
        open AreDistinct areDistinct
        persp : (i j : Fin 3) → (i♯j : i ♯ j) → meet (sd♯ i♯j) ∈ axis

        persp zero (suc zero) _ =  persp01
        persp zero (suc (suc zero)) _ = persp02
        persp (suc zero) (suc (suc zero)) _ =  persp12
        persp (suc zero) zero i♯j =  ⟨ meet-cong join-comm join-comm ⟩⇐ persp01 {symmetry i♯j} 
        persp (suc (suc zero)) zero i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ persp02 {symmetry i♯j}
        persp (suc (suc zero)) (suc zero) i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ persp12 {symmetry i♯j}
        persp zero zero i♯j = ⊥-elim $ refl i♯j
        persp (suc zero) (suc zero) i♯j = ⊥-elim $ refl i♯j
        persp (suc (suc zero)) (suc (suc zero)) i♯j = ⊥-elim $ refl i♯j
        persp (suc (suc (suc ()))) _ _ 
        persp _ (suc (suc (suc ()))) _


record ArePerspectiveCenter₁ (T T' : TriangleP) : Set (a ⊔ b ⊔ d ⊔ e) where
  field
    Center : Point
    areDistinct : AreDistinct T T'

  open AreDistinct areDistinct 

  field
    perspective : ∀ i → Center ∈ join (vrt♯ i)

    O∉T-01  : {p : `0 ♯ `1} → Center ∉ edge T p
    O∉T-02  : {p : `0 ♯ `2} → Center ∉ edge T p
    O∉T-12  : {p : `1 ♯ `2} → Center ∉ edge T p

    O∉T'-01  : {p : `0 ♯ `1} → Center ∉ edge T' p
    O∉T'-02  : {p : `0 ♯ `2} → Center ∉ edge T' p
    O∉T'-12  : {p : `1 ♯ `2} → Center ∉ edge T' p


toArePerspectiveCenter : ∀ {T T'} → ArePerspectiveCenter₁ T T' 
                                  → ArePerspectiveCenter T T'
toArePerspectiveCenter {T} {T'} apc₁-TT' 
  =  record
       { Center = Center
       ; areDistinct = areDistinct
       ; Center-∉-T = λ {i} {j} {i♯j} → O∉T i j i♯j
       ; Center-∉-T' =  λ {i} {j} {i♯j} → O∉T' i j i♯j
       ; perspective = perspective
       }
  where      open ArePerspectiveCenter₁ apc₁-TT'

             O∉T : ∀ i j → (i♯j : i ♯ j) → Center ∉ edge T i♯j
             O∉T zero (suc zero) _ =  O∉T-01
             O∉T zero (suc (suc zero)) _ =  O∉T-02
             O∉T (suc zero) (suc (suc zero)) _ = O∉T-12
             O∉T (suc zero) zero i♯j =  O∉T-01 {symmetry i♯j} ⇒⟨ join-comm ⟩
             O∉T (suc (suc zero)) zero i♯j =  O∉T-02 {symmetry i♯j} ⇒⟨ join-comm ⟩
             O∉T (suc (suc zero))  (suc zero) i♯j = O∉T-12 {symmetry i♯j} ⇒⟨ join-comm ⟩
             O∉T zero zero i♯j = ⊥-elim $ refl i♯j
             O∉T (suc zero) (suc zero) i♯j = ⊥-elim $ refl i♯j
             O∉T (suc (suc zero)) (suc (suc zero)) i♯j = ⊥-elim $ refl i♯j
             O∉T (suc (suc (suc ()))) _ _ 
             O∉T _ (suc (suc (suc ()))) _


             O∉T' : ∀ i j → (i♯j : i ♯ j) → Center ∉ edge T' i♯j
             O∉T' zero (suc zero) _ =  O∉T'-01
             O∉T' zero (suc (suc zero)) _ =  O∉T'-02
             O∉T' (suc zero) (suc (suc zero)) _ = O∉T'-12
             O∉T' (suc zero) zero i♯j =  O∉T'-01 {symmetry i♯j} ⇒⟨ join-comm ⟩
             O∉T' (suc (suc zero)) zero i♯j =  O∉T'-02 {symmetry i♯j} ⇒⟨ join-comm ⟩
             O∉T' (suc (suc zero))  (suc zero) i♯j = O∉T'-12 {symmetry i♯j} ⇒⟨ join-comm ⟩
             O∉T' zero zero i♯j = ⊥-elim $ refl i♯j
             O∉T' (suc zero) (suc zero) i♯j = ⊥-elim $ refl i♯j
             O∉T' (suc (suc zero)) (suc (suc zero)) i♯j = ⊥-elim $ refl i♯j
             O∉T' (suc (suc (suc ()))) _ _ 
             O∉T' _ (suc (suc (suc ()))) _


