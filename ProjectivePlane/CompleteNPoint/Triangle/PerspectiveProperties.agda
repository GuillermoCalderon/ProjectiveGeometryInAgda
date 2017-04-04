{-# OPTIONS --no-eta-equality #-} 

open import Data.Empty
open import Level using (_⊔_)
open import Function 
open import Relation.Binary.Apartness
open import Data.Fin
open import Data.Fin.Setoid
open import ProjectivePlane
import Relation.Binary.EqReasoning as EqR

module ProjectivePlane.CompleteNPoint.Triangle.PerspectiveProperties
       {a b c d e}
       (PP : ProjectivePlane.ProjectivePlane a b c d e) where

open ProjectivePlane.ProjectivePlane PP
open import ProjectivePlane.CompleteNPoint PP
open import ProjectivePlane.PropertiesGeneral PP
open import ProjectivePlane.CompleteNPoint.Triangle PP
open import ProjectivePlane.CompleteNPoint.Triangle.Perspective PP

open ProjectivePlane.Setoid♯Instances PP
open ProjectivePlane.Rel♯Instances PP

module TriangleD 
                 {T T'}
                 (paTT' : ArePerspectiveAxis T T')
                 {i j : Fin 3}
                 (i♯j : i ♯ j) where

 open ArePerspectiveAxis paTT' 
 open AreDistinct areDistinct



 -- a family of triangles useful for proof of desargues converse 
 
 -- intersection de IJ with axis
 axis∙IJ  :  Point
 axis∙IJ  = meet $ sd♯ i♯j

 -- a shorter name
 private A = axis∙IJ


 -- vertices are outside the axis
 Ti♯A : (T $∙ i) ♯ A
 Ti♯A = C0 axis-∉-T (perspective i♯j)

 T'i♯A : (T' $∙ i) ♯ A
 T'i♯A = C0 axis-∉-T' (perspective i♯j)


 -- vertices of T' are outside sides of T
 T'i∉Tij : (T' $∙ i) ∉ edge T i♯j
 T'i∉Tij = C7-a (symmetry $ sd♯ i♯j) (T'i♯A ⇒⟨ meet-comm ⟩) joinₗ
 

 Tij≈TiA : edge T i♯j ≈ join Ti♯A
 Tij≈TiA = unq-join Ti♯A joinₗ meetₗ

  
 tr : Triangle
 tr   = 
        isT2T (Min→Triangle (record { B♯C = Ti♯A ; A∉BC =  T'i∉Tij ⇒⟨ unq-join _ joinₗ meetₗ ⟩ }))
 

 trp : TriangleP
 trp = triangle→Poly tr


 I'I♯IA : edge trp 0♯1 ♯ edge trp  1♯2
 I'I♯IA = sides♯ trp {i♯j = 0♯1}  {1♯2} 0♯1 0♯2

 
 I'I♯IJ : edge trp 0♯1 ♯ edge T i♯j
 I'I♯IJ =   I'I♯IA ⇒⟨ sym $ unq-join _ joinₗ  meetₗ ⟩
 

 II'♯IJ : join (vrt♯ i) ♯ edge T i♯j
 II'♯IJ = ⟨ join-comm ⟩⇐ I'I♯IJ


 J∉II' : (T $∙ j) ∉ join (vrt♯ i)
 J∉II' = C7-b (symmetry $ T $♯ i♯j) 
              ( symmetry I'I♯IJ ⇒⟨ join-comm ⟩ )
              joinₗ joinₗ joinᵣ

 II'♯JJ' : join (vrt♯ i) ♯ join (vrt♯ j)
 II'♯JJ' = symmetry $ C5 joinₗ J∉II'
     

  
 I'I♯IX : edge trp 0♯1 ♯ edge trp 1♯2
 I'I♯IX = sides♯ trp {i♯j = 0♯1}  {1♯2} 0♯1 0♯2

   
  
 I♯A : (T $∙ i) ♯ (meet $ sd♯ i♯j)
 I♯A  =  C0 axis-∉-T (perspective i♯j) 

 I'♯A : (T' $∙ i) ♯ (meet $ sd♯ i♯j)
 I'♯A = C0 axis-∉-T'  (perspective i♯j)

 J♯II'∙JJ' : (T $∙ j) ♯ meet II'♯JJ'
 J♯II'∙JJ' = C0 J∉II'  meetₗ

-- end module TriangleD ----------------------------
-----------------------------------------------------

module DesarguesLemmas {T T'}
     (apTT' : ArePerspectiveAxis T T') where

  open TriangleD apTT'
  open ArePerspectiveAxis apTT'
  open AreDistinct areDistinct

  IA♯JB : ∀ {i j k : Fin 3}
         → (i♯j : i ♯ j) 
         → (i♯k : i ♯ k)
         → (j♯k : j ♯ k)
         → join (I♯A i♯k) ♯ join (I♯A j♯k)
  IA♯JB i♯j i♯k j♯k = 
 
           ⟨  sym $ unq-join (I♯A i♯k) joinₗ meetₗ
           ⟩⇐ 
           sides♯ T {i♯j = i♯k} {j♯k} i♯j i♯k  
           ⇒⟨
              unq-join (I♯A j♯k) joinₗ meetₗ 
           ⟩

  
 
  ---------------------
  -- B ∉ triangle 0'0A
  ---------------------

  --  some useful definitions
  B = meet $ sd♯ 0♯2
  T₀ = trp 0♯1 -- 0'0A
  T₂ = trp 0♯2 -- 0'0B
  2♯1 = symmetry 1♯2
  
  
  B∉T₀-01 : B ∉ edge T₀ 0♯1 
  B∉T₀-01 =  nonc3 T₂ (symmetry 0♯2) 0♯1 2♯1 ⇒⟨ ≈join ⟩ 
                
  B∉T₀-02  : B ∉ edge T₀ 0♯2
  B∉T₀-02  =
             C7-b  
                  (symmetry (I'♯A 0♯2)) 
                  (⟨ join-comm ⟩⇐ sides♯ T' {i♯j = symmetry 0♯2}  (symmetry 0♯2) 2♯1)
                  joinₗ joinₗ meetᵣ
             --
             ⇒⟨ begin
                  edge T' 0♯1  ≈⟨ unq-join (T₀ $♯ 0♯2) joinₗ meetᵣ ⟩ 
                  edge T₀ 0♯2
                 ∎
               ⟩
      where open EqR (toSetoid Line♯)


  B∉T₀-12  : B ∉ edge T₀ 1♯2
  B∉T₀-12  = 
             C7-b 
                  (symmetry $ I♯A 0♯2) 
                  (⟨ join-comm ⟩⇐ sides♯ T {i♯j = symmetry 0♯2}  (symmetry 0♯2) 2♯1) 
                  joinₗ joinₗ meetₗ
             ⇒⟨ begin
                  edge T 0♯1  ≈⟨ unq-join (T₀ $♯ 1♯2) joinₗ meetₗ ⟩ 
                  edge T₀ 1♯2
                 ∎
               ⟩
      where open EqR (toSetoid Line♯)
    
  
  B∉T₀ : ∀ i j → (i♯j : i ♯ j) 
                  → B ∉ edge T₀ i♯j

  B∉T₀ zero zero i♯j  = ⊥-elim $ refl i♯j
  B∉T₀ zero (suc zero) i♯j = B∉T₀-01
  B∉T₀ zero (suc (suc zero)) i♯j  = B∉T₀-02
  B∉T₀ zero (suc (suc (suc ()))) i♯j
  B∉T₀ (suc zero) zero i♯j  = B∉T₀-01 ⇒⟨ join-comm ⟩
  B∉T₀ (suc zero) (suc zero) i♯j  =  ⊥-elim $ refl i♯j
  B∉T₀ (suc zero) (suc (suc zero)) i♯j  =  B∉T₀-12
  B∉T₀ (suc (suc zero)) zero i♯j  =  B∉T₀-02 ⇒⟨ join-comm ⟩
  B∉T₀ (suc (suc zero)) (suc zero) i♯j  =  B∉T₀-12 ⇒⟨ join-comm ⟩
  B∉T₀ (suc (suc zero)) (suc (suc zero)) i♯j =  ⊥-elim $ refl i♯j
  B∉T₀ _ (suc (suc (suc ()))) _
  B∉T₀ (suc (suc (suc ()))) _ _


  -- the center
  Cnt =  meet $ II'♯JJ' 0♯1

  T0♯Cnt : (T $∙ `0) ♯ Cnt 
  T0♯Cnt =   J♯II'∙JJ' (symmetry 0♯1) ⇒⟨ meet-comm ⟩

  T1♯Cnt :  (T $∙ `1) ♯ Cnt 
  T1♯Cnt =  J♯II'∙JJ' 0♯1

  Cnt∉T01 : {p01 : `0 ♯ `1} → Cnt ∉ edge T p01
  Cnt∉T01 {p01} = C7-b (symmetry T0♯Cnt) (II'♯IJ p01) joinₗ joinₗ meetₗ


  Cnt∉T02 : {p02 : `0 ♯ `2} → Cnt ∉ edge T p02
  Cnt∉T02 {p02} = C7-b  (symmetry T0♯Cnt) (II'♯IJ p02) joinₗ joinₗ meetₗ

  Cnt∉T12 : {p12 : `1 ♯ `2} → Cnt ∉ edge T p12
  Cnt∉T12 {p12} = C7-b  (symmetry T1♯Cnt) (II'♯IJ p12) joinₗ joinₗ meetᵣ

--  End Module Desargues Lemmas
-------------------------------------------------------------------
