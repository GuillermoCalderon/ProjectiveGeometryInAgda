


open import Data.Sum
open import Data.Product
open import Level
open import Function hiding (_∋_)
open import Relation.Binary.Apartness
open import ProjectivePlane

module ProjectivePlane.Duality where

module Lemmas {a b c d e}
       (PP : ProjectivePlane a b c d e)  where

       open ProjectivePlane.ProjectivePlane PP
       open import ProjectivePlane.Properties PP     
       open ProjectivePlane.Setoid♯Instances PP
       open ProjectivePlane.Rel♯Instances PP

       -- Dual membership relation
       _∋_ : Line → Point → Set _
       _∋_ = flip _∈_      


       _∌_ = flip _∉_

       
       line₁  : Point → Line
       line₁  P with outside-line P
       ...      | r , P∉r =  join  (C0 P∉r (∈-point₁ r))

       line₂  : Point → Line
       line₂  P with outside-line P
       ...      | r , P∉r =  join  (C0 P∉r (∈-point₂ r))

       line₃  : Point → Line
       line₃  P with outside-line P
       ...      | r , P∉r =  join  (C0 P∉r (∈-point₃ r))


       ∋-line₁ : ∀ P → line₁ P ∋ P
       ∋-line₁ P = joinₗ 
       ∋-line₂ : ∀ P → line₂ P ∋ P
       ∋-line₂ P = joinₗ 
       ∋-line₃ : ∀ P → line₃ P ∋ P
       ∋-line₃ P = joinₗ 


       lemma-line-i♯j : ∀ P l A B → (P∉l : P ∉ l)→ A ♯ B → (A∈l : A ∈ l) → (B∈l : B ∈ l)  
                        → let PA = join  $ C0 P∉l A∈l
                              PB = join  $ C0 P∉l B∈l
                          in PA ♯ PB
       lemma-line-i♯j P l A B P∉l A♯B A∈l B∈l = P-24→ (C0 P∉l A∈l) (C0 P∉l B∈l) A♯B (P∉l ⇒⟨ unq-join A♯B A∈l B∈l ⟩ )
                      -- where open Rel♯ Outside

       line-1♯2 : ∀ P → line₁ P ♯ line₂ P
       line-1♯2 P  with outside-line P 
       ...  | (r , P∉r ) = lemma-line-i♯j P r (point₁ r) (point₂ r) P∉r ( proj₁ $ point-i♯j r) (∈-point₁ r) (∈-point₂ r) 
             

       line-1♯3 : ∀ P → line₁ P ♯ line₃ P
       line-1♯3 P  with outside-line P 
       ...  | (r , P∉r ) = lemma-line-i♯j P r (point₁ r) (point₃ r) P∉r ( proj₁ $ proj₂ $ point-i♯j r) (∈-point₁ r) (∈-point₃ r)


       line-2♯3 : ∀ P → line₂ P ♯ line₃ P
       line-2♯3 P  with outside-line P 
       ...  | (r , P∉r ) = lemma-line-i♯j P r (point₂ r) (point₃ r) P∉r ( proj₂ $ proj₂ $ point-i♯j r) (∈-point₂ r) (∈-point₃ r)
 
       
       c7 : ∀ {P Q l} → (P♯Q : P ♯ Q) → l ♯ join P♯Q → l ∌ P ⊎ l ∌ Q
       c7 {P} {Q} {l} P♯Q l♯PQ  with cotransitivity (meet $ symmetry l♯PQ)  P♯Q 
       ... | (inj₁ l∙PQ♯P) =  inj₁ (C7-a  (symmetry l♯PQ) (symmetry l∙PQ♯P) joinₗ)
       ... | (inj₂ l∙PQ♯Q) =  inj₂ (C7-a  (symmetry l♯PQ)  (symmetry l∙PQ♯Q) joinᵣ)
      


---  Duality theoreme       
duality :  ∀ {a b c d e} {Point♯ : Setoid♯ a b} {Line♯ : Setoid♯ c d}  
             {∈ ∉ : Rel♯ e Point♯ Line♯}
           → IsProjectivePlane ∈ ∉
           → IsProjectivePlane (flip♯ ∈) (flip♯ ∉)
duality  PP = record
                 { C0 = λ l∌P r∋P → symmetry $ C5 r∋P l∌P 
                 ; P₀ = l₀
                 ; l₀ = P₀
                 ; P₀∉l₀ = P₀∉l₀
                 ; join = meet
                 ; joinₗ = meetₗ
                 ; joinᵣ = meetᵣ
                 ; unq-join = unq-meet
                 ; meet = join
                 ; meetₗ = joinₗ
                 ; meetᵣ = joinᵣ
                 ; unq-meet = unq-join
                 ; point₁ = line₁
                         
                 ; point₂ = line₂
                 ; point₃ = line₃
                 ; ∈-point₁ = ∋-line₁
                 ; ∈-point₂ = ∋-line₂
                 ; ∈-point₃ = ∋-line₃
                 ; point-i♯j = λ r → line-1♯2 r , line-1♯3 r , line-2♯3 r
                 ; C5 = λ  l∋P l∌Q → symmetry (C0 l∌Q  l∋P)
                 ; C6 = C6
                 ; C7 = c7
              }
        where open IsProjectivePlane  PP
              open Lemmas (toProjectivePlane PP)
              open ProjectivePlane.Setoid♯Instances (toProjectivePlane PP)




dual : ∀ {a b c d e} → ProjectivePlane a b c d e → ProjectivePlane c d a b e
dual PP = record
            { Point♯ = Line♯
            ; Line♯ = Point♯
            ; Incidence = flip♯ Incidence
            ; isProjectivePlane = duality isProjectivePlane
            }
  where 
        open ProjectivePlane.ProjectivePlane PP
