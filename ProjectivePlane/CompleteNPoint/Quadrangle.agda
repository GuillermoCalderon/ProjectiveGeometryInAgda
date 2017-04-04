import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality 
     using () renaming (refl to refl-≡)
open import Relation.Nullary
open import Data.Empty
open import Data.Sum
open import Data.Product
import Data.Nat
open import Level using (_⊔_)
open import Function renaming (_∋_ to ⟨_⟩∋[_])
open import Relation.Binary.Apartness
import Data.Nat 
open import Data.Fin
open import Data.Fin.Setoid

open import ProjectivePlane
import ProjectivePlane.CompleteNPoint
import ProjectivePlane.PropertiesGeneral
open import ProjectivePlane.Duality


module ProjectivePlane.CompleteNPoint.Quadrangle {a b c d e}
       ( PP : ProjectivePlane a b c d e) where

open ProjectivePlane.ProjectivePlane PP
open ProjectivePlane.Setoid♯Instances PP
open ProjectivePlane.Rel♯Instances PP
open ProjectivePlane.CompleteNPoint PP
open ProjectivePlane.PropertiesGeneral PP
open ProjectivePlane.Duality
open import ProjectivePlane.CompleteNPoint.Triangle PP

Quadrangle : Set _
Quadrangle = Complete-N-Point 4
    


open EqR ⦃...⦄
instance
  private
    lineSetoid  = toSetoid Line♯
    pointSetoid = toSetoid Point♯



module Fin4♯ where

    -- useful alias
    `0 `1 `2 `3 : Fin 4
    `0 = zero
    `1 = suc zero
    `2 = suc (suc zero)
    `3 = suc (suc (suc zero))

    0♯1 : `0 ♯ `1
    0♯1 = λ ()

    0♯2 : `0  ♯ `2
    0♯2 = λ ()

    0♯3 : `0 ♯ `3
    0♯3 = λ ()

    1♯2 : `1 ♯ `2
    1♯2 = λ ()

    1♯3 : `1 ♯ `3
    1♯3 = λ ()

    2♯3 : `2 ♯ `3
    2♯3 = λ ()

    3♯0 : `3 ♯ `0
    3♯0 =  λ ()

    2♯1 : `2 ♯ `1
    2♯1 =  λ ()

    
open  Fin4♯ public




-- oposite sides
01♯23 : ∀ Q → edge Q 0♯1 ♯ edge Q 2♯3
01♯23 Q = sides♯ Q 0♯2 0♯3 


03♯12 : ∀ Q → edge Q 0♯3 ♯ edge Q 1♯2
03♯12 Q = sides♯  Q 0♯1 0♯2 

03♯01 :  ∀ Q → edge Q 0♯1 ♯ edge Q 1♯2
03♯01 Q =  sides♯ Q 0♯1 0♯2 


-- adjacent sides
01♯12 : ∀ Q → edge Q 0♯1 ♯ edge Q 1♯2
01♯12 Q = C5 joinₗ (nonc3 Q 0♯1 1♯2 0♯2)


01♯13 : ∀ Q → edge Q 0♯1 ♯ edge Q 1♯3
01♯13 Q = C5  joinₗ (nonc3 Q 0♯1 1♯3 0♯3)
 
diag₁  : ∀ Q →  Point
diag₁  = meet ∘ 01♯23  


1∉23 :  ∀ Q → Q $∙ `1  ∉ edge Q 2♯3
1∉23 Q = nonc3 Q 1♯2 2♯3 1♯3


→1023 : Quadrangle → Quadrangle
→1023 Q = Q [ `0 ↔ `1 ] 

diag₁♯1 : ∀ Q → diag₁ Q ♯ (Q $∙ `1)
diag₁♯1 Q = symmetry (C0 (1∉23 Q)   meetᵣ)

  
diag₁♯0 : ∀ Q → diag₁ Q ♯ (Q $∙ `0)
diag₁♯0 Q  = ⟨ begin 
                diag₁ Q           ≈⟨ meet-cong join-comm refl ⟩ 
                (diag₁ $ →1023 Q) ∎ 
              ⟩⇐  
              diag₁♯1 (→1023 Q)  
            


diag₁♯3 : ∀ Q → diag₁ Q ♯ (Q $∙ `3)
diag₁♯3  Q = ⟨  meet-flip-cong join-comm join-comm 
             ⟩⇐ diag₁♯0 (Q [ `0 ↔ `3 ] [ `1 ↔ `2 ]) 


--  The other diganonals
--  diag₂: 03∙21

→0321 : Quadrangle → Quadrangle
→0321 Q =  Q [ `1 ↔ `3 ]

→0213 : Quadrangle → Quadrangle
→0213 Q = Q [ `1 ↔ `2 ]

diag₂ : Quadrangle → Point
diag₂ = diag₁ ∘ →0321


-- diag₃ : 02∙13
diag₃ : Quadrangle → Point
diag₃ = diag₁ ∘ →0213


diag₁∉12 : ∀ Q → diag₁ Q ∉ edge Q 1♯2
diag₁∉12 Q = C7-b (diag₁♯1 Q) (01♯12 Q) joinᵣ joinₗ meetₗ 


-- this is a direct proof that follows the same template as diag₁∉12 
diag₁∉13 : ∀ Q → diag₁ Q ∉ edge Q 1♯3
diag₁∉13 Q = C7-b (diag₁♯1 Q) (01♯13 Q) joinᵣ joinₗ meetₗ


-- another proof reusing diag₁∉12  for an appropriate permutation of Q
diag₁∉13-perm : ∀ Q → diag₁ Q ∉ edge Q 1♯3
diag₁∉13-perm Q = ⟨ meet-cong  refl join-comm 
                  ⟩⇐ 
                  diag₁∉12  (Q [ `2 ↔ `3 ])





diag₁♯diag₃ : ∀ Q → diag₁ Q ♯ diag₃ Q
diag₁♯diag₃ Q   = C0  (diag₁∉13 Q)  meetᵣ


diag₁♯diag₂ : ∀ Q → diag₁ Q ♯ diag₂ Q
diag₁♯diag₂ Q = 
    ⟨ meet-cong  refl join-comm ⟩⇐  -- 01∙32≈01∙23
    diag₁♯diag₃ (Q [ `2 ↔ `3 ])
    ⇒⟨ meet-cong  refl join-comm ⟩  -- 03∙12≈03∙21


diag₂♯diag₃ : ∀ Q → diag₂ Q ♯ diag₃ Q
diag₂♯diag₃ Q = 
                ⟨ meet-comm ⟩⇐
                diag₁♯diag₃ (Q [ `0 ↔ `2 ])
                ⇒⟨ meet-cong  join-comm refl ⟩ 


-- minimal conditions to be a Quadrangle
record IsQuadrangleMin (A B C D : Point) : Set (a ⊔ b ⊔ e) where
   field
     ABC : IsTriangle A B C
     ABD : IsTriangle A B D
     ACD : IsTriangle A C D
     BCD : IsTriangle B C D


isQMin→Q :  ∀ {A B C D} → IsQuadrangleMin A B C D → Quadrangle
isQMin→Q {A} {B} {C} {D} IQMin =  
  record { F = record { F = record { f = ff 
                                   ; sound = λ {i j} → sound-ff i j 
                                   } 
                      ; isInjective = λ {i j} → inj-ff i j 
                      } 
         ; nonc3 = λ {a b c} → nc3-ff a b c 
         }

         where open IsQuadrangleMin IQMin
               open IsTriangle
               
               ff : Fin 4 → Point
               ff zero = A
               ff (suc zero) = B
               ff (suc (suc zero)) = C
               ff (suc (suc (suc zero))) = D
               ff (suc (suc (suc (suc ()))))
               
               sound-ff : ∀ m n → m ≈ n → ff m ≈ ff n
               sound-ff zero zero m≈n = refl
               sound-ff (suc zero) (suc zero) m≈n = refl
               sound-ff (suc (suc zero)) (suc (suc zero)) m≈n = refl
               sound-ff (suc (suc (suc zero))) (suc (suc (suc zero))) m≈n = refl
               sound-ff zero (suc _) m≈n = ⊥-elim (m≈n (λ ()))
               sound-ff (suc _) zero m≈n =  ⊥-elim (m≈n (λ ()))
               sound-ff (suc zero) (suc (suc _)) m≈n =  ⊥-elim (m≈n (λ ()))
               sound-ff (suc (suc _)) (suc zero) m≈n =  ⊥-elim (m≈n (λ ()))
               sound-ff (suc (suc zero)) (suc (suc (suc _))) m≈n =  ⊥-elim (m≈n (λ ()))
               sound-ff (suc (suc (suc _))) (suc (suc zero)) m≈n =  ⊥-elim (m≈n (λ ()))
               sound-ff _  (suc (suc (suc (suc ())))) m≈n
               sound-ff (suc (suc (suc (suc ())))) _ m≈n


               inj-ff : ∀ m n → m ♯ n → ff m ♯ ff n
               inj-ff zero zero m♯n = ⊥-elim (m♯n refl-≡)
               inj-ff (suc zero) (suc zero) m♯n = ⊥-elim (m♯n refl-≡)
               inj-ff (suc (suc zero)) (suc (suc zero)) m♯n = ⊥-elim (m♯n refl-≡)
               inj-ff (suc (suc (suc zero))) (suc (suc (suc zero))) m♯n = ⊥-elim (m♯n refl-≡)
               inj-ff zero (suc zero) m♯n = A♯B ABC
               inj-ff zero (suc (suc zero)) m♯n = A♯C ABC
               inj-ff zero (suc (suc (suc zero))) m♯n = A♯C ABD
               inj-ff (suc zero) zero m♯n = symmetry (A♯B ABC)
               inj-ff (suc zero) (suc (suc zero)) m♯n = B♯C ABC
               inj-ff (suc zero) (suc (suc (suc zero))) m♯n = B♯C ABD
               inj-ff (suc zero) (suc (suc (suc (suc ())))) m♯n
               inj-ff (suc (suc zero)) zero m♯n = symmetry (A♯C ABC)
               inj-ff (suc (suc zero)) (suc zero) m♯n = symmetry (B♯C ABC)
               inj-ff (suc (suc zero)) (suc (suc (suc zero))) m♯n = B♯C BCD
               inj-ff (suc (suc zero)) (suc (suc (suc (suc ())))) m♯n
               inj-ff (suc (suc (suc zero))) zero m♯n = symmetry (A♯C ABD)
               inj-ff (suc (suc (suc zero))) (suc zero) m♯n = symmetry (A♯C BCD)
               inj-ff (suc (suc (suc zero))) (suc (suc zero)) m♯n = symmetry (B♯C BCD)
               inj-ff _  (suc (suc (suc (suc ())))) m♯n
               inj-ff (suc (suc (suc (suc ())))) _ m♯n


               nc3-ff : ∀ (a b c : Fin 4) → a ♯ b → (b♯c : b ♯ c) → a ♯ c → ff a ∉ join (inj-ff _ _ b♯c)
               nc3-ff zero zero _ a♯b b♯c a♯c  = ⊥-elim (a♯b refl-≡)
               nc3-ff zero _ zero a♯b b♯c a♯c  = ⊥-elim (a♯c refl-≡)
               nc3-ff _ (suc zero) (suc zero) a♯b b♯c a♯c = ⊥-elim (b♯c refl-≡)
               nc3-ff zero (suc zero) (suc (suc zero)) a♯b b♯c a♯c  = A∉BC ABC
               nc3-ff zero (suc zero) (suc (suc (suc zero))) a♯b b♯c a♯c = A∉BC ABD
               nc3-ff _ _ (suc (suc (suc (suc ())))) a♯b b♯c a♯c 
               nc3-ff zero (suc (suc zero)) (suc zero) a♯b b♯c a♯c  =   A∉BC ABC  ⇒⟨ join-comm ⟩
               nc3-ff zero (suc (suc (suc zero))) (suc zero) a♯b b♯c a♯c  =  A∉BC ABD ⇒⟨ join-comm ⟩
               nc3-ff _ (suc (suc (suc (suc ())))) _ a♯b b♯c a♯c
               nc3-ff _ (suc (suc zero)) (suc (suc zero)) a♯b b♯c a♯c  =  ⊥-elim (b♯c refl-≡)
               nc3-ff zero (suc (suc zero)) (suc (suc (suc zero))) a♯b b♯c a♯c =  A∉BC ACD  ⇒⟨ ≈join ⟩
               nc3-ff zero (suc (suc (suc zero))) (suc (suc zero)) a♯b b♯c a♯c  = A∉BC ACD  ⇒⟨ join-comm ⟩
               nc3-ff _ (suc (suc (suc zero))) (suc (suc (suc zero))) a♯b b♯c a♯c  = ⊥-elim (b♯c refl-≡)
               nc3-ff _ zero zero a♯b b♯c a♯c  = ⊥-elim (b♯c refl-≡)
               nc3-ff (suc zero) _ (suc zero) a♯b b♯c a♯c  = ⊥-elim (a♯c refl-≡)
               nc3-ff (suc zero) zero (suc (suc zero)) a♯b b♯c a♯c = B∉AC ABC
               nc3-ff (suc zero) zero (suc (suc (suc zero))) a♯b b♯c a♯c  = B∉AC ABD ⇒⟨ ≈join ⟩ 
               nc3-ff (suc (suc zero)) zero (suc zero) a♯b b♯c a♯c  = C∉AB ABC
               nc3-ff (suc (suc (suc zero))) zero (suc zero) a♯b b♯c a♯c = C∉AB ABD  ⇒⟨ ≈join ⟩
               nc3-ff (suc (suc (suc (suc ())))) _ _ a♯b b♯c a♯c
               nc3-ff (suc (suc zero)) _ (suc (suc zero)) a♯b b♯c a♯c = ⊥-elim (a♯c refl-≡)
               nc3-ff (suc (suc zero)) zero (suc (suc (suc zero))) a♯b b♯c a♯c = B∉AC ACD ⇒⟨ ≈join ⟩
               nc3-ff (suc (suc (suc zero))) zero (suc (suc zero)) a♯b b♯c a♯c = C∉AB ACD ⇒⟨ ≈join ⟩
               nc3-ff (suc (suc (suc zero))) _ (suc (suc (suc zero))) a♯b b♯c a♯c = ⊥-elim (a♯c refl-≡)
               nc3-ff (suc zero) (suc zero) _ a♯b b♯c a♯c =  ⊥-elim (a♯b refl-≡)
               nc3-ff (suc zero) (suc (suc zero)) zero a♯b b♯c a♯c = B∉AC ABC ⇒⟨ join-comm ⟩
               nc3-ff (suc zero) (suc (suc (suc zero))) zero a♯b b♯c a♯c = B∉AC ABD ⇒⟨ join-comm ⟩
               nc3-ff (suc (suc zero)) (suc zero) zero a♯b b♯c a♯c = C∉AB ABC ⇒⟨ join-comm ⟩
               nc3-ff (suc (suc (suc zero))) (suc zero) zero a♯b b♯c a♯c = C∉AB ABD  ⇒⟨ join-comm ⟩
               nc3-ff (suc (suc zero)) (suc (suc zero)) _ a♯b b♯c a♯c =  ⊥-elim (a♯b refl-≡)
               nc3-ff (suc (suc zero)) (suc (suc (suc zero))) zero a♯b b♯c a♯c =  B∉AC ACD  ⇒⟨ join-comm ⟩
               nc3-ff (suc (suc (suc zero))) (suc (suc zero)) zero a♯b b♯c a♯c =  C∉AB ACD  ⇒⟨ join-comm ⟩
               nc3-ff (suc (suc (suc zero))) (suc (suc (suc zero))) _ a♯b b♯c a♯c =  ⊥-elim (a♯b refl-≡)
               nc3-ff (suc zero) (suc (suc zero)) (suc (suc (suc zero))) a♯b b♯c a♯c = A∉BC BCD
               nc3-ff (suc zero) (suc (suc (suc zero))) (suc (suc zero)) a♯b b♯c a♯c = A∉BC BCD  ⇒⟨ join-comm ⟩
               nc3-ff (suc (suc zero)) (suc zero) (suc (suc (suc zero))) a♯b b♯c a♯c  = B∉AC BCD ⇒⟨ ≈join ⟩ 
               nc3-ff (suc (suc (suc zero))) (suc zero) (suc (suc zero)) a♯b b♯c a♯c =  C∉AB BCD ⇒⟨ ≈join ⟩
               nc3-ff (suc (suc zero)) (suc (suc (suc zero))) (suc zero) a♯b b♯c a♯c = B∉AC BCD ⇒⟨ join-comm ⟩
               nc3-ff (suc (suc (suc zero))) (suc (suc zero)) (suc zero) a♯b b♯c a♯c = C∉AB BCD ⇒⟨ join-comm ⟩


