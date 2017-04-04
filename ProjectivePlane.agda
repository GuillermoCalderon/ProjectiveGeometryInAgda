{-# OPTIONS --no-eta-equality #-} 

module ProjectivePlane where

 
open import Relation.Nullary
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Level
open import Function hiding (_∋_)
open import Relation.Binary.Apartness




record IsProjectivePlane {a b c d e}        
       { Point♯ : Setoid♯ a b } 
       { Line♯ : Setoid♯ c d  }
       (Incidence  Outside : Rel♯ e Point♯ Line♯)
  : Set (a ⊔ b ⊔ c ⊔ d ⊔ e) where
       



  infix 4 _∉_ 
  infix 4 _∈_

  Point : Set a
  Point = Setoid♯.Carrier Point♯ 
  Line  :  Set c
  Line  = Setoid♯.Carrier Line♯

  _∈_ : Point → Line → Set e
  _∈_ = Rel♯.R Incidence

  -- outside relation
  _∉_    : Point → Line → Set e
  _∉_  =  Rel♯.R Outside 
    -- ∀ {Q : Point} → (Q ∈ l) →    P ♯ Q

  open Setoid♯ ⦃...⦄
  instance 
    private
      L♯ = Line♯
      P♯ = Point♯

  field
    -- caracterization of ∉
    C0 : ∀ {P l} → P ∉ l → (∀ {Q} → Q ∈ l → P ♯ Q)

    -- axioms  
    --  C1 : There exists a point P and a line l, such that P ∉ l
    P₀  : Point
    l₀  : Line
    P₀∉l₀ : P₀ ∉ l₀

    -- C2 : For any distinct points P  and Q,
    --      there exists a unique line passing through both points
    join : ∀ {P Q : ⟨ Point♯ ⟩} →  P ♯ Q → Line


    joinₗ : ∀ {P Q} {P♯Q : P ♯ Q} → P ∈ join P♯Q
    joinᵣ : ∀ {P Q} {P♯Q : P ♯ Q} → Q ∈ join P♯Q

    unq-join : ∀ {P Q} (P♯Q : P ♯ Q) 
             →  ∀ {l} → P ∈ l → Q ∈ l → l ≈ join P♯Q

    -- C3 : For any distinct lines l and r,
    --      there exists a unique point lying on both lines
    meet : ∀ {l r} → l ♯ r → Point
    meetₗ : ∀ {l r} → {l♯r : l ♯ r} → meet l♯r ∈ l
    meetᵣ : ∀ {l r} → {l♯r : l ♯ r} → meet l♯r ∈ r
    unq-meet :  ∀ {l r}  → (l♯r : l ♯ r)
                → ∀ {P} → P ∈ l → P ∈ r → P ≈ meet l♯r

    -- C4 : There exists at least 3 disntict points lying
    --      in any line
    point₁ point₂ point₃ : Line → Point
    ∈-point₁ : ∀ l → point₁ l ∈ l 
    ∈-point₂ : ∀ l → point₂ l ∈ l
    ∈-point₃ : ∀ l → point₃ l ∈ l


    point-i♯j : ∀ l → point₁ l ♯ point₂ l ×  point₁ l ♯ point₃ l ×  point₂ l ♯ point₃ l 

    -- C5 : For any lines l and m, if there exists P ∈ l such that P ∉ m, then m ♯ l
    C5 : ∀ {l m P} → P ∈ l → P ∉ m → l ♯ m

    -- C6 : For any line l and any point P : ¬(P ∉ l) if and only if P ∈ l
    C6 : ∀ {P l} → ¬ (P ∉ l) → P ∈ l



    -- C7 : If l and m are distinct lines, and P is a point
    --        such that P ♯ (l . m), then
    --        either P ∉ l or P ∉ m
    C7 : ∀ {l m P} → (l♯m : l ♯ m) → P ♯ meet l♯m → P ∉ l ⊎ P ∉ m




  -- C6 converse follows from definition of ∉ and irreflexivity ♯
  C6← : ∀ {P l} →  P ∈ l → ¬ (P ∉ l)
  C6← {P} P∈l P∉l = irreflexive (C0 P∉l  P∈l)


  -- usefull variants of C7
  -- C7-a is a weak version of C7. 
  C7-a : ∀ {l m P} → (l♯m : l ♯ m) → P ♯ meet l♯m → P ∈ l → P ∉ m
  C7-a  l♯m P♯l∙m P∈l =
    case C7  l♯m P♯l∙m of
      \{ (inj₁ P∉l) →  ⊥-elim (C6← P∈l P∉l)
       ; (inj₂ P∉m) →  P∉m
       }



  C7-b :  ∀ {l m : Line} → {P Q : Point} → P ♯ Q → (l ♯ m) → Q ∈ l → Q ∈ m → P ∈ l → P ∉ m
  C7-b  P♯Q l♯m Q∈l Q∈m  = C7-a l♯m  $ P♯Q ⇒⟨ unq-meet l♯m Q∈l Q∈m ⟩ 
                         where open IsRel♯ (isRel♯-♯ {S = Point♯})
  

  C7-c :  ∀ {l m : Line} → {P Q : Point} → P ♯ Q → (l ♯ m) → Q ∈ l → Q ∈ m → P ∉ l ⊎ P ∉ m
  C7-c  P♯Q l♯m Q∈l Q∈m = C7 l♯m $ P♯Q ⇒⟨ unq-meet l♯m  Q∈l Q∈m ⟩
                             where open IsRel♯ (isRel♯-♯ {S = Point♯})





record ProjectivePlane (a b c d e : Level) : Set (suc (a ⊔ b ⊔ c ⊔ d ⊔ e)) where
  field
    Point♯       : Setoid♯ a b
    Line♯        : Setoid♯ c d
    Outside Incidence   : Rel♯ e Point♯ Line♯      
    isProjectivePlane     : IsProjectivePlane  Incidence Outside
  open IsProjectivePlane isProjectivePlane public 




toProjectivePlane : ∀ {a b c d e P♯ L♯} {∈ ∉} 
                    → IsProjectivePlane {a} {b} {c} {d} {e} {P♯} {L♯} ∈ ∉
                    → ProjectivePlane a b c d e
toProjectivePlane  isPP = 
  record { -- missing fields inferred from this:  
           isProjectivePlane = isPP 
         }


module Setoid♯Instances {a b c d e} (PP : ProjectivePlane a b c d e)  where
  
  open ProjectivePlane PP
  open Setoid♯ ⦃...⦄ public


  {- instances -}
  instance
    -- setoids
    LineSetoid♯  : Setoid♯ _ _
    LineSetoid♯  = ProjectivePlane.Line♯ PP

    PointSetoid♯ : Setoid♯ _ _
    PointSetoid♯ = ProjectivePlane.Point♯ PP

module EqReasoningInstances {a b c d e} (PP : ProjectivePlane a b c d e)  where
  open ProjectivePlane PP
  open import Relation.Binary
  import Relation.Binary.EqReasoning as EqR 

  open EqR  ⦃...⦄ public
  instance 
    LineSetoid : Setoid _ _ 
    LineSetoid = toSetoid Line♯
    PointSetoid : Setoid _ _
    PointSetoid = toSetoid Point♯
 
module Rel♯Instances {a b c d e} (PP : ProjectivePlane a b c d e)  where

  open ProjectivePlane PP
  open IsRel♯ ⦃...⦄ public

  instance
    isRel-∉ : IsRel♯ _ _ _
    isRel-∉ = Rel♯.isRel Outside 
    isRel-∈ : IsRel♯ _ _ _
    isRel-∈ = Rel♯.isRel Incidence


    isR♯-♯-P : IsRel♯ _ _ _
    isR♯-♯-P = isRel♯-♯  {S = Point♯}
    isR♯-♯-L : IsRel♯ _ _ _
    isR♯-♯-L = isRel♯-♯ {S = Line♯}

    isR♯-≈-P : IsRel♯ _ _ _
    isR♯-≈-P = isRel♯-≈  {S = Point♯}
    isR♯-≈-L : IsRel♯ _ _ _
    isR♯-≈-L = isRel♯-≈ {S = Line♯}


