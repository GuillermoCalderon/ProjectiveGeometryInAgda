{-# OPTIONS --no-eta-equality #-} 

open import Relation.Binary.PropositionalEquality
     renaming (refl to refl-≡)
open import Relation.Nullary
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Data.Nat hiding (_≟_)
open import Level as L
open import Function renaming (_∋_ to _:∋:_)
open import Data.List
open import Relation.Binary.Apartness
import Data.Nat 
open import Data.Fin
open import Data.Fin.Setoid
-- open ≡-Reasoning

open import ProjectivePlane
import ProjectivePlane.CompleteNPoint
import ProjectivePlane.PropertiesGeneral


module ProjectivePlane.CompleteNPoint.Triangle {a b c d e}
       ( PP : ProjectivePlane a b c d e) where

       open ProjectivePlane.ProjectivePlane PP
       open ProjectivePlane.CompleteNPoint PP
       open ProjectivePlane.PropertiesGeneral PP
       open ProjectivePlane.Setoid♯Instances PP
       open ProjectivePlane.Rel♯Instances PP
       

      --  A flat definition for triangle
       record IsTriangle 
            (A B C : Point) : Set ( a L.⊔ b L.⊔ e) where
            field
              -- 3 distinc points
              A♯B : A ♯ B
              B♯C : B ♯ C
              A♯C : A ♯ C

              -- non collinear
              A∉BC : A ∉ join B♯C
              B∉AC : B ∉ join A♯C
              C∉AB : C ∉ join A♯B

            -- sides are different
            AB♯BC : join A♯B ♯ join B♯C
            AB♯BC = C5 joinₗ A∉BC

            AC♯AB : join A♯C ♯ join A♯B
            AC♯AB = C5 joinᵣ C∉AB

            AC♯BC : join A♯C ♯ join B♯C
            AC♯BC = C5 joinₗ A∉BC

            -- convenient abbreviations
            C♯A = symmetry A♯C
            C♯B = symmetry B♯C
            B♯A = symmetry A♯B
                            
       -- sufficient condition for triangle 
       record IsTriangleMin 
              (A B C : Point) : Set (a L.⊔ b L.⊔ e) where
              -- minimal conditions to be a triangle
              field
                B♯C   : B ♯ C
                A∉BC  : A ∉ join B♯C
              
              --              
              A♯B =  C0 A∉BC  joinₗ

              BC♯AB : join B♯C ♯ join A♯B
              BC♯AB = symmetry $ C5 joinₗ A∉BC 

              C∉AB : C ∉ join A♯B
              C∉AB = C7-b (symmetry B♯C) BC♯AB joinₗ joinᵣ joinᵣ



       module TriangleMinProperties {A B C} 
              (ABC : IsTriangleMin A B C) where
            open IsTriangleMin ABC public
            
            ACB : IsTriangleMin A C B
            ACB = record { B♯C = symmetry B♯C ; A∉BC =  A∉BC ⇒⟨ join-comm ⟩ }
                  

            -- Propiedades que surgen por simetría
            A♯C   : A ♯ C
            A♯C   = IsTriangleMin.A♯B ACB

            C♯B  : C ♯ B
            C♯B  = symmetry B♯C

            CB♯AC : join C♯B ♯ join A♯C
            CB♯AC = IsTriangleMin.BC♯AB ACB
            B∉AC  : B ∉ join A♯C
            B∉AC  = IsTriangleMin.C∉AB ACB




       Triangle→Min : ∀ {A B C}
             → IsTriangle A B C
             → IsTriangleMin A B C
       Triangle→Min  {A} {B} {C} ABC
         = record { B♯C = IsTriangle.B♯C ABC ; A∉BC = IsTriangle.A∉BC ABC }
              
  
       Min→Triangle :  ∀  {A B C}
             → IsTriangleMin  A B C 
             → IsTriangle     A B C
       Min→Triangle {A} {B} {C} tmin 
         = record
             { A♯B  = A♯B
             ; B♯C  = B♯C 
             ; A♯C  = A♯C
             ; A∉BC = A∉BC 
             ; B∉AC = B∉AC 
             ; C∉AB = C∉AB 
             }
         where 
           open TriangleMinProperties tmin

 
       record Triangle        
              : Set ( a L.⊔ b L.⊔ e) where
              field
                A B C : Point
                isTriangle : IsTriangle A B C
    
              open IsTriangle isTriangle public
              
       -- conversion between diferent triangle definitions
       isT2T : ∀ {A B C} → IsTriangle A B C → Triangle
       isT2T isTABC = record { isTriangle = isTABC }
 
       triangle→Poly : Triangle → Complete-N-Point 3
       triangle→Poly ABC = 
         record 
         { F = record 
               { F = record { f = f3 ; sound = λ {a b} → sound-f3 a b  } 
               ; isInjective = λ {a b} → inj a b 
               } 
         ; nonc3 = λ {a b c} → nc3 a b c 
         }
 
          where 
             open Triangle ABC
             
             

             f3 : Fin 3 → Point
             f3 zero = A
             f3 (suc zero) = B
             f3 (suc (suc zero)) = C
             f3 (suc (suc (suc ())))

             sound-f3 : ∀ (a b : Fin 3) → a ≈ b → f3 a ≈ f3 b
             sound-f3 Fin.zero Fin.zero a≈b = refl
             sound-f3 Fin.zero (Fin.suc b₁) a≈b _ = a≈b λ{()}
             sound-f3 (Fin.suc a₁) Fin.zero a≈b _ = a≈b λ{()}
             sound-f3 (Fin.suc a₁) (Fin.suc b₁) a≈b with FinEq _ a₁ b₁ 
             sound-f3 (Fin.suc .a₁) (Fin.suc a₁) a≈b | yes refl-≡  = refl
             sound-f3 (Fin.suc a₁) (Fin.suc b₁) a≈b  | no ¬p  = ⊥-elim (a≈b (λ sa₁≡sb₁ → ¬p (aux a₁ b₁ sa₁≡sb₁)))
                              where  aux : ∀ {n} → (a b : Fin n) →  _≡_ {A = Fin (ℕ.suc n)} (Fin.suc  a) (Fin.suc  b) → a ≡ b
                                     aux a .a refl-≡ = refl-≡

             
             inj : ∀ a b → a ♯ b → f3 a ♯ f3 b
             inj Fin.zero Fin.zero a♯b = ⊥-elim (a♯b refl-≡)
             inj Fin.zero (Fin.suc Fin.zero) a♯b = A♯B 
             inj Fin.zero (Fin.suc (Fin.suc Fin.zero)) a♯b = A♯C
             inj Fin.zero (Fin.suc (Fin.suc (Fin.suc ()))) a♯b
             inj (Fin.suc Fin.zero) Fin.zero a♯b = B♯A
             inj (Fin.suc Fin.zero) (Fin.suc Fin.zero) a♯b = ⊥-elim $ a♯b refl-≡
             inj (Fin.suc Fin.zero) (Fin.suc (Fin.suc Fin.zero)) a♯b = B♯C
             inj (Fin.suc Fin.zero) (Fin.suc (Fin.suc (Fin.suc ()))) a♯b
             inj (Fin.suc (Fin.suc Fin.zero)) Fin.zero a♯b = C♯A
             inj (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero) a♯b = C♯B
             inj (Fin.suc (Fin.suc Fin.zero)) (Fin.suc (Fin.suc Fin.zero)) a♯b = ⊥-elim $ a♯b refl-≡
             inj (Fin.suc (Fin.suc Fin.zero)) (Fin.suc (Fin.suc (Fin.suc ()))) a♯b
             inj (Fin.suc (Fin.suc (Fin.suc ()))) b₁ a♯b

             
             nc3 : ∀ (a b c : Fin 3) → a ♯ b → (b♯c : b ♯ c) → a ♯ c
                   → f3 a ∉ join (inj _ _ b♯c)
             nc3 Fin.zero Fin.zero _ a♯b  _ _ = ⊥-elim (a♯b refl-≡)
             nc3 Fin.zero _ Fin.zero a♯b b♯c a♯c = ⊥-elim (a♯c refl-≡)
             nc3 _ (Fin.suc Fin.zero) (Fin.suc Fin.zero) a♯b b♯c a♯c  = ⊥-elim (b♯c refl-≡) 
             nc3 Fin.zero (Fin.suc Fin.zero) (Fin.suc (Fin.suc Fin.zero)) a♯b b♯c a♯c  = A∉BC
             nc3 Fin.zero (Fin.suc Fin.zero) (Fin.suc (Fin.suc (Fin.suc ()))) a♯b b♯c a♯c
             nc3 Fin.zero (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero) a♯b b♯c a♯c  = A∉BC ⇒⟨ join-comm ⟩
             nc3 _ (Fin.suc (Fin.suc Fin.zero)) (Fin.suc (Fin.suc Fin.zero)) a♯b b♯c a♯c  = ⊥-elim $ b♯c refl-≡
             nc3 Fin.zero (Fin.suc (Fin.suc Fin.zero)) (Fin.suc (Fin.suc (Fin.suc ()))) a♯b b♯c a♯c
             nc3 Fin.zero (Fin.suc (Fin.suc (Fin.suc ()))) c₁ a♯b b♯c a♯c 
             nc3 _  Fin.zero Fin.zero a♯b b♯c a♯c  = ⊥-elim $ b♯c refl-≡
             nc3 (Fin.suc Fin.zero) _ (Fin.suc Fin.zero) a♯b b♯c a♯c  = ⊥-elim $ a♯c refl-≡
             nc3 (Fin.suc Fin.zero) Fin.zero (Fin.suc (Fin.suc Fin.zero)) a♯b b♯c a♯c  = B∉AC
             nc3 (Fin.suc Fin.zero) Fin.zero (Fin.suc (Fin.suc (Fin.suc ()))) a♯b b♯c a♯c
             nc3 (Fin.suc Fin.zero) (Fin.suc Fin.zero) c₁ a♯b b♯c a♯c  = ⊥-elim $ a♯b refl-≡
             nc3 (Fin.suc Fin.zero) (Fin.suc (Fin.suc Fin.zero)) Fin.zero a♯b b♯c a♯c  = B∉AC ⇒⟨ join-comm ⟩
             nc3 (Fin.suc Fin.zero) (Fin.suc (Fin.suc Fin.zero)) (Fin.suc (Fin.suc (Fin.suc ()))) a♯b b♯c a♯c
             nc3 (Fin.suc Fin.zero) (Fin.suc (Fin.suc (Fin.suc ()))) c₁ a♯b b♯c a♯c
             nc3 (Fin.suc (Fin.suc Fin.zero)) Fin.zero (Fin.suc Fin.zero) a♯b b♯c a♯c  = C∉AB
             nc3 (Fin.suc (Fin.suc Fin.zero)) _ (Fin.suc (Fin.suc Fin.zero)) a♯b b♯c a♯c = ⊥-elim $ a♯c refl-≡
             nc3 (Fin.suc (Fin.suc Fin.zero)) Fin.zero (Fin.suc (Fin.suc (Fin.suc ()))) a♯b b♯c a♯c
             nc3 (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero) Fin.zero a♯b b♯c a♯c = C∉AB ⇒⟨ join-comm ⟩
             nc3 (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero) (Fin.suc (Fin.suc (Fin.suc ()))) a♯b b♯c a♯c
             nc3 (Fin.suc (Fin.suc Fin.zero)) (Fin.suc (Fin.suc Fin.zero)) c₁ a♯b b♯c a♯c  = ⊥-elim $ a♯b refl-≡
             nc3 (Fin.suc (Fin.suc Fin.zero)) (Fin.suc (Fin.suc (Fin.suc ()))) c₁ a♯b b♯c a♯c
             nc3 (Fin.suc (Fin.suc (Fin.suc ()))) b₁ c₁ a♯b b♯c a♯c
