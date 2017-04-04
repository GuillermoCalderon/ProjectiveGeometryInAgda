
open import Function using (_$_)
open import Relation.Binary.Apartness
open import Data.Fin
open import Data.Empty
open import Data.Fin.Setoid
open import ProjectivePlane

module ProjectivePlane.CompleteNPoint.Triangle.Desargues   {a b c d e}
       (PP : ProjectivePlane.ProjectivePlane a b c d e) where


open ProjectivePlane.ProjectivePlane PP
open import ProjectivePlane.PropertiesGeneral PP
open import ProjectivePlane.CompleteNPoint PP
open import ProjectivePlane.CompleteNPoint.Triangle PP
open import ProjectivePlane.CompleteNPoint.Triangle.Perspective PP

open ProjectivePlane.Setoid♯Instances PP
open ProjectivePlane.Rel♯Instances PP

-- desargues direct
Desargues = ∀ T T' → ArePerspectiveCenter T T' 
                   → ArePerspectiveAxis   T T' 

-- desargues converse (dual)
Desargues← = ∀ T T' → ArePerspectiveAxis T T' 
                    → ArePerspectiveCenter   T T'

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

  
 -- the triangle I'IA  with (IJ = IA)
 tr : Triangle
 tr   = 
        isT2T (Min→Triangle 
              (record { B♯C = Ti♯A 
                      ; A∉BC =  T'i∉Tij ⇒⟨ unq-join _ joinₗ meetₗ ⟩ 
                      }
              ))
 

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
  import Relation.Binary.EqReasoning as EqR

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

module DesarguesConverse
       {T T'}
       (arePerspectiveAxis : ArePerspectiveAxis T T')
       where
       
        open import ProjectivePlane.CompleteNPoint.Triangle.DesarguesSymmetries PP
        open ArePerspectiveAxis arePerspectiveAxis
        open AreDistinct areDistinct
        apTT'sym = permPerspectiveAxis (swap  `0 `2 IdInjectiveFun♯) arePerspectiveAxis
        open TriangleD arePerspectiveAxis
        open DesarguesLemmas arePerspectiveAxis

        

        A = meet $ sd♯ 0♯1
        C = meet $ sd♯ 2♯1

        T-01♯21 : edge T 0♯1 ♯ edge T 2♯1
        T-01♯21 = sides♯ T 0♯2 0♯1


        T1♯A :  (T $∙ `1) ♯ A        
        T1♯A =  C0 axis-∉-T  (perspective 0♯1)
               

        T-01∙21♯A : meet T-01♯21 ♯ A
        T-01∙21♯A =  ⟨ sym  meet-joinᵣᵣ ⟩⇐ T1♯A


        A∉T-21 : A ∉ edge T 2♯1
        A∉T-21 = C7-a  T-01♯21 (symmetry T-01∙21♯A) meetₗ

        A♯01∙21 : A ♯ (meet T-01♯21 )
        A♯01∙21 = C0 A∉T-21  meetᵣ

        A∉T21 :  A ∉ (edge T $ symmetry 1♯2)
        A∉T21 = C7-a (C5 joinₗ ((Complete-N-Point.nonc3 T 0♯2 (symmetry 1♯2) 0♯1))) A♯01∙21 meetₗ


        A♯C : A ♯ C
        A♯C = C0 A∉T21  meetₗ

        -- two center-perspective triangles
        Q0 =  T₀ -- trp 0♯1    -- 0'0A
        Q2 =  trp 2♯1    -- 2'2C


        Q0≠Q2 :  AreDistinct Q0 Q2
        Q0≠Q2 = record { vrt♯ = v ; sd♯ = λ {i j}→ s i j }
          where

              v : ∀ i → (Q0 $∙ i) ♯ (Q2 $∙ i)
              v zero             
                =  
                   T' $♯ 0♯2
              v (suc zero)       
                =  
                   T $♯ 0♯2
              v (suc (suc zero)) 
                = 
                   A♯C
              v (suc (suc (suc ())))
            
              
              s01 : (edge Q0 0♯1) ♯ (edge Q2  0♯1)
              s01 = 
                  ⟨  join-comm ⟩⇐ 
                  II'♯JJ' 0♯2  
                  ⇒⟨ join-comm ⟩

              s02 : (edge Q0 0♯2) ♯ (edge Q2  0♯2)
              s02 = 
                  ⟨ join-cong refl meet-comm ⟩⇐  
                  DesarguesLemmas.IA♯JB  (flipPerspectiveAxis arePerspectiveAxis) 0♯2 0♯1 2♯1 
                  ⇒⟨ join-cong refl meet-comm ⟩
  

              s12 = IA♯JB 0♯2 0♯1 2♯1

              s : ∀ i j → (i♯j : i ♯ j) → 
                  edge Q0 i♯j ♯ edge Q2 i♯j


              s zero (suc zero) i♯j = s01
              s zero (suc (suc zero)) i♯j = s02

              s (suc zero) zero i♯j =  ⟨ join-comm ⟩⇐  s01 ⇒⟨ join-comm ⟩
              s (suc zero) (suc (suc zero)) i♯j = s12

              s (suc (suc zero)) zero i♯j = ⟨ join-comm ⟩⇐  s02 ⇒⟨ join-comm ⟩
              s (suc (suc zero)) (suc zero) i♯j = ⟨ join-comm ⟩⇐  s12 ⇒⟨ join-comm ⟩

              s zero zero i♯j = ⊥-elim $ irreflexive i♯j
              s (suc (suc zero)) (suc (suc zero)) i♯j = ⊥-elim $ irreflexive i♯j
              s (suc zero) (suc zero) i♯j =  ⊥-elim $ irreflexive i♯j
              s (suc (suc (suc ()))) _ _
              s _ (suc (suc (suc ()))) _

        paQ0Q2 : ArePerspectiveCenter Q0 Q2
        paQ0Q2 = record
                   { Center = meet $ sd♯ 0♯2
                   ; areDistinct =  Q0≠Q2
                   ; Center-∉-T =   -- {!B∉T₀!}
                                    λ {_} {_} {i♯j} → B∉T₀ _ _ i♯j
                   ; Center-∉-T' =  λ {i} {j} {i♯j} → cnt∉Q₂ _ _ i♯j 
                                    --λ {_} {_} {i♯j} →  ⟨ meet-cong join-comm join-comm ⟩⇐
                                    --                    DesarguesLemmas.B∉T₀  apTT'sym  _ _ i♯j
                   ; perspective = persp
                   }

            where


                 persp : ∀ i → B ∈ join  (AreDistinct.vrt♯  Q0≠Q2 i)
                 persp zero = meetᵣ 
                 persp (suc zero) = meetₗ
                 persp (suc (suc zero)) = perspective 0♯2 ⇒⟨ unq-join A♯C (perspective 0♯1) (perspective 2♯1) ⟩ 
                 persp (suc (suc (suc ())))        

                 cnt∉Q₂ :  ∀ i j → 
                           ( i♯j : i ♯ j) →
                           meet  (sd♯ 0♯2) ∉ edge Q2 i♯j

                 -- we have to define all cases in order to improve performace of  the type checker 
                 cnt∉Q₂ zero (suc zero) i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ DesarguesLemmas.B∉T₀  apTT'sym  _ _ i♯j
                 cnt∉Q₂ zero (suc (suc zero)) i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ DesarguesLemmas.B∉T₀  apTT'sym  _ _ i♯j
                 cnt∉Q₂ (suc zero) (suc (suc zero)) i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ DesarguesLemmas.B∉T₀  apTT'sym  _ _ i♯j
                 cnt∉Q₂ (suc zero) zero i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ DesarguesLemmas.B∉T₀  apTT'sym  _ _ i♯j
                 cnt∉Q₂ (suc (suc zero)) zero i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ DesarguesLemmas.B∉T₀  apTT'sym  _ _ i♯j
                 cnt∉Q₂ (suc (suc zero)) (suc zero) i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ DesarguesLemmas.B∉T₀  apTT'sym  _ _ i♯j
            
                 cnt∉Q₂ zero zero i♯j = ⊥-elim $ refl i♯j
                 cnt∉Q₂ (suc zero) (suc zero) i♯j = ⊥-elim $ refl i♯j
                 cnt∉Q₂ (suc (suc zero)) (suc (suc zero))  i♯j = ⊥-elim $ refl i♯j
                 cnt∉Q₂ (suc (suc (suc ()))) _ _ 
                 cnt∉Q₂ _ (suc (suc (suc ())))  _ 


        module _(direct : Desargues)  where

          apT'T : ArePerspectiveAxis T' T
          apT'T = flipPerspectiveAxis arePerspectiveAxis
  
  
  
          perspectiveAxis-Q0Q2 = direct Q0 Q2 paQ0Q2 
  
  
  
          axisQ = ArePerspectiveAxis.axis  perspectiveAxis-Q0Q2
  
          T01≈Q0-12  : edge T 0♯1  ≈ edge Q0 1♯2
          T01≈Q0-12  = unq-join (Q0 $♯ 1♯2)  joinₗ meetₗ
  
  
          T21≈Q2-12  : edge T 2♯1  ≈ edge Q2 1♯2
          T21≈Q2-12  = unq-join (Q2 $♯ 1♯2)  joinₗ meetₗ
          
          1∈Q0-12 : (T $∙ `1) ∈ edge Q0 1♯2
          1∈Q0-12 =  joinᵣ ⇒⟨ T01≈Q0-12 ⟩
  
  
          
          1∈Q2-12 : (T $∙ `1) ∈ edge Q2 1♯2
          1∈Q2-12 =  joinᵣ ⇒⟨ T21≈Q2-12 ⟩           
  
          1∈axisQ   : (T $∙ `1) ∈ axisQ
          1∈axisQ = ⟨ unq-meet _  1∈Q0-12 1∈Q2-12  ⟩⇐ 
                   ArePerspectiveAxis.perspective perspectiveAxis-Q0Q2 1♯2
  
          1'∈axisQ : (T' $∙ `1) ∈ axisQ
          1'∈axisQ =  ⟨ unq-meet _ 
                                (joinᵣ ⇒⟨ unq-join (Q0 $♯ 0♯2)  joinₗ meetᵣ ⟩)
                                (joinₗ ⇒⟨ unq-join (Q2 $♯ 0♯2) {edge T' 1♯2} joinᵣ (meetᵣ ⇒⟨ join-comm ⟩) ⟩) 
                     ⟩⇐ 
                     ArePerspectiveAxis.perspective perspectiveAxis-Q0Q2 0♯2
  
  
  
  
  
          axisQ≈11' : axisQ ≈ join (vrt♯ `1)
          axisQ≈11' = unq-join (vrt♯ `1)  1∈axisQ 1'∈axisQ
  
  
          Center∉T : (i j : Fin 3) → (i♯j : i ♯ j) → Cnt ∉ (edge T i♯j)
  
          Center∉T zero (suc zero) _  =  Cnt∉T01 
          Center∉T zero (suc (suc zero))  i♯j = Cnt∉T02 
          Center∉T (suc zero) zero i♯j =  Cnt∉T01 {symmetry i♯j} ⇒⟨ join-comm ⟩
          Center∉T (suc (suc zero)) zero  i♯j =  Cnt∉T02 {symmetry i♯j} ⇒⟨ join-comm ⟩
          Center∉T (suc zero) (suc (suc zero)) i♯j = Cnt∉T12
          Center∉T (suc (suc zero)) (suc zero) i♯j = Cnt∉T12 {symmetry i♯j} ⇒⟨ join-comm ⟩
          Center∉T zero zero i♯j = ⊥-elim $ refl i♯j
          Center∉T (suc zero) (suc zero) i♯j = ⊥-elim $ refl i♯j
          Center∉T (suc (suc zero)) (suc (suc zero)) i♯j = ⊥-elim $ refl i♯j
          Center∉T (suc (suc (suc ()))) _ _
          Center∉T _  (suc (suc (suc ()))) _
  
  
          module DLT'T = DesarguesLemmas {T'} {T} apT'T
  
          Center∉T' : (i j : Fin 3) → (i♯j : i ♯ j) → Cnt ∉ (edge T' i♯j)
  
          Center∉T' zero (suc zero) _  =  ⟨ meet-cong join-comm join-comm ⟩⇐ DLT'T.Cnt∉T01 
          Center∉T' zero (suc (suc zero))  i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ DLT'T.Cnt∉T02 
          Center∉T' (suc zero) zero i♯j =  ⟨ meet-cong join-comm join-comm ⟩⇐ DLT'T.Cnt∉T01 {symmetry i♯j} ⇒⟨ join-comm ⟩
          Center∉T' (suc (suc zero)) zero  i♯j =  ⟨ meet-cong join-comm join-comm ⟩⇐ DLT'T.Cnt∉T02 {symmetry i♯j} ⇒⟨ join-comm ⟩
          Center∉T' (suc zero) (suc (suc zero)) i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ DLT'T.Cnt∉T12
          Center∉T' (suc (suc zero)) (suc zero) i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ DLT'T.Cnt∉T12 {symmetry i♯j} ⇒⟨ join-comm ⟩
          Center∉T' zero zero i♯j = ⊥-elim $ refl i♯j
          Center∉T' (suc zero) (suc zero) i♯j = ⊥-elim $ refl i♯j
          Center∉T' (suc (suc zero)) (suc (suc zero)) i♯j = ⊥-elim $ refl i♯j
          Center∉T' (suc (suc (suc ()))) _ _
          Center∉T' _  (suc (suc (suc ()))) _
  
  
          persp : (i : Fin 3) → (meet $ II'♯JJ' 0♯1) ∈ join (vrt♯ i)
  
  
          persp zero = meetₗ
          persp (suc zero) = meetᵣ
          persp (suc (suc zero)) = ⟨ sym (unq-meet _ 
                                                   { meet (symmetry $ AreDistinct.sd♯  Q0≠Q2 0♯1)}
                                                   (meetᵣ ⇒⟨ join-comm ⟩)
  
                                                   ( ⟨ meet-comm  ⟩⇐ 
                                                       ArePerspectiveAxis.perspective perspectiveAxis-Q0Q2 0♯1 
                                                     ⇒⟨ axisQ≈11' ⟩ )) 
                                   ⟩⇐ 
                                      meetₗ  
                                            ⇒⟨ join-comm ⟩
          persp (suc (suc (suc ())))

          arePC-T-T' : ArePerspectiveCenter T T' 
          arePC-T-T' 
            = record
            { Center =    meet $ II'♯JJ' 0♯1  
            ; areDistinct = ArePerspectiveAxis.areDistinct arePerspectiveAxis
            ; Center-∉-T = λ {_} {_}  {i♯j} → Center∉T  _ _ i♯j
            ; Center-∉-T' = λ {_} {_} {i♯j} → Center∉T' _ _ i♯j 
            ; perspective = persp
            }
              where
        
              open ArePerspectiveAxis arePerspectiveAxis



toDesargues← :  Desargues → Desargues←
toDesargues← direct T T' arePA-TT' = DesarguesConverse.arePC-T-T'  arePA-TT' direct 
           
  

  
