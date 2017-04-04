{-# OPTIONS --no-eta-equality #-} 

open import ProjectivePlane as P
open import Relation.Binary.Apartness
open import Data.Fin.Setoid
import Level as L
open import Data.Nat
open import Data.Fin
open import Function
-- open import Relation.Binary.PropositionalEquality

module ProjectivePlane.CompleteNPoint {a b c d e : L.Level} 
       (PP : ProjectivePlane a b c d e)
       where


open P.ProjectivePlane PP 
open import ProjectivePlane.PropertiesGeneral PP
open P.Setoid♯Instances PP
open P.Rel♯Instances PP

------------------------------------------
-- Complete n-points
------------------------------------------

record Complete-N-Point (n : ℕ) : Set (L.suc (a L.⊔ b L.⊔ e)) where

         field
           -- n points as an injection
           F : InjectiveFun♯ (setoidFin n) (Point♯)

           -- noncollinear threewise
           nonc3 : let instance foo = setoidFin n in 
                 ∀ {a b c : Fin n} 
                 → a ♯ b → (b♯c : b ♯ c) → a ♯ c
                 → ⟨ fun♯ F ⟩$ a  ∉  join (isInjective F  b♯c)
                     
         --private           
         --   instance SFn = (setoidFin n)
         -- application operators to be used outside 
         _$∙_  : Fin n → Point
         _$∙_  k = ⟨ fun♯ F ⟩$ k

         _$♯_ : ∀ {i j : Fin n} → i ♯ j → (⟨ fun♯ F ⟩$ i)  ♯ ⟨ fun♯ F ⟩$ j
         _$♯_ = isInjective F
  
       
         edge : ∀ {i j} → (i♯j : i ♯ j) → Line
         edge  = join ∘ isInjective F
 
         edge-sym : ∀ {i j} → (i♯j : i ♯ j) → edge i♯j ≈ edge (symmetry i♯j)
         edge-sym {i} {j} i♯j = join-comm

         -- diferents sides
         sides♯ : ∀ {i j p k}
            → {i♯j : i ♯ j}
            → {p♯k : p ♯ k}
            → (i♯p : i ♯ p)
            → (i♯k : i ♯ k)
            → edge  i♯j ♯ edge  p♯k
         sides♯ {i} {j} {p} {k} {i♯j} {p♯k} i♯p i♯k  = 
                C5 joinₗ (nonc3  i♯p p♯k i♯k)

         adjacent♯ : ∀ {i j k : Fin n} 
                           → {i♯j : i ♯ j}
                           → {j♯k : j ♯ k}
                           → {i♯k : i ♯ k}
                           → edge i♯j ♯ edge j♯k
         adjacent♯ {i} {j} {k} {i♯j} {j♯k} {i♯k}= C5 joinₗ (nonc3 i♯j j♯k i♯k)

open Complete-N-Point  public
       
       

subComplete-N-Point : ∀ {m n } → 
                 (f : InjectiveFun♯ (setoidFin m)  (setoidFin n)) →  
                  Complete-N-Point n → Complete-N-Point m
subComplete-N-Point f Pol =  
  record { F =  F Pol ⊙ f  
         ; nonc3 = λ a♯b b♯c a♯c 
                   → nonc3 Pol (isInjective f a♯b) 
                               (isInjective f b♯c) 
                               (isInjective f a♯c) 
         }

-- swapping points in a polygon
_[_↔_] : ∀{n} → Complete-N-Point n
              → (i j : Fin n)
              → Complete-N-Point n
𝒫 [ i ↔ j ] = subComplete-N-Point (swap i j IdInjectiveFun♯) 𝒫
                    

