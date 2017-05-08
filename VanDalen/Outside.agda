{-# OPTIONS --no-eta-equality #-}

module VanDalen.Outside where

open import Level
open import Relation.Nullary
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function using (id ; case_of_ ; _$_)
open import Relation.Binary.Apartness
open import ProjectivePlane

record IsOutside {a b c}
  (Point : Set a) (Line : Set b) 
  (_∉_ : Point → Line → Set c)  : Set (a ⊔ b  ⊔ c) where

  -- definitions
  _∈_ : Point → Line → Set c
  _∈_ P  l = ¬ (P ∉ l)

  _♯ₚ_ :  Point → Point → Set (c ⊔ b)
  _♯ₚ_ P Q = ∃ \ l → (P ∈ l × Q ∉ l)
  _=ₚ_ :  Point → Point → Set (c ⊔ b)
  _=ₚ_ P Q = ¬ (P ♯ₚ Q)
 

  _♯ₗ_ :  Line → Line → Set (c ⊔ a)
  _♯ₗ_ r s = ∃ \ P → P ∈ r × P ∉ s
  _=ₗ_ :  Line → Line → Set (c ⊔ a)
  _=ₗ_ r s = ¬ (r ♯ₗ s)

  -- some useful properties
  ∈∉→♯ₚ :  ∀ {Q P l} → Q ∈ l → P ∉ l → Q ♯ₚ P
  ∈∉→♯ₚ {Q} {P} {l} Q∈l P∉l = l , Q∈l , P∉l
  ∈∉→♯ₗ :  ∀ {P l s} → P ∈ l → P ∉ s → l ♯ₗ s
  ∈∉→♯ₗ {P} P∈l P∉s = P , P∈l , P∉s
  

  field
  
    -- compatibility of ∉ wrt ♯ 
    Ax1 : ∀{P l} m → P ∉ l → P ∉ m ⊎ m ♯ₗ l
    Ax2 : ∀{l P} Q → P ∉ l → Q ∉ l ⊎ Q ♯ₚ P 

  --  substitution
  subs∉₁  :  ∀ {P Q l} → P ∉ l → Q =ₚ P → Q ∉ l
  subs∉₁ {P} {Q} P∉l Q=P 
     = case Ax2 Q P∉l of 
       \{ (inj₁ Q∉l) → Q∉l
        ; (inj₂ Q♯P) → ⊥-elim (Q=P Q♯P)
        }
  subs∉₂  :  ∀ {P l r} → P ∉ l → r =ₗ l → P ∉ r
  subs∉₂ {P} {l} {r} P∉l r=l
     = case Ax1 r P∉l of 
       \{ (inj₁ P∉r) → P∉r
        ; (inj₂ r♯l) → ⊥-elim (r=l r♯l)
        }
  
  field
    -- line passing by two distintc points
    Ax3-a : ∀ {P Q} → P ♯ₚ Q  →  ∃ \l →  P ∈ l × Q ∈ l   -- existence
    Ax3-b : ∀ {P Q l r}  → P ♯ₚ Q
                         → P ∈ l → Q ∈ l 
                         → P ∈ r → Q ∈ r
                         → l =ₗ r
    -- point determined by intersecting two distintc lines
    Ax4-a : ∀ {l r} → l ♯ₗ r → ∃ \P → P ∈ l × P ∈ r   -- existence
    Ax4-b : ∀ {l r P Q}  → l ♯ₗ r                     -- uniqueness
                         → P ∈ l → P ∈ r 
                         → Q ∈ l → Q ∈ r
                         → P =ₚ Q

  unq-ln = Ax3-b
  unq-pt = Ax4-b
  
  join : ∀ {P Q} →  P ♯ₚ Q → Line
  join P♯Q = proj₁  (Ax3-a P♯Q)



  joinₗ : ∀ {P Q} → {P♯Q : P ♯ₚ Q}
          → P ∈ join P♯Q
  joinₗ {P} {Q} {P♯Q} =  proj₁ (proj₂  (Ax3-a P♯Q))
  joinᵣ : ∀ {P Q} → {P♯Q : P ♯ₚ Q}
          → Q ∈ join P♯Q
  joinᵣ {P} {Q} {P♯Q} =  proj₂ (proj₂  (Ax3-a P♯Q))

  meet : ∀ {p q} → p ♯ₗ q → Point
  meet p♯q = proj₁ (Ax4-a p♯q)

      
  meetₗ : ∀ {p q} → {p♯q : p ♯ₗ q}
          → meet p♯q ∈ p
  meetₗ {p} {q} {p♯q} =  proj₁ (proj₂  (Ax4-a p♯q))
  meetᵣ : ∀ {p q} → {p♯q : p ♯ₗ q}
          → meet p♯q ∈ q
  meetᵣ {p} {q} {p♯q} =  proj₂ (proj₂  (Ax4-a p♯q))
  
  field

    -- triangle axioms
    Ax5 : ∀ {P Q R} 
          → {P♯Q : P ♯ₚ Q} 
          → (R∉PQ : R ∉ join P♯Q) →
          let 
            Q♯R : Q ♯ₚ R
            Q♯R = ∈∉→♯ₚ joinᵣ R∉PQ
          in 
            P ∉ join Q♯R

    Ax6 : ∀ {P Q p  q}
          → (P∉p : P ∉ p) → (Q∉q : Q ∉ q)
          → (P∈q : P ∈ q) → (Q∈p : Q ∈ p)
          → let P♯Q : P ♯ₚ Q
                P♯Q = ∈∉→♯ₚ P∈q Q∉q
                p♯q : p ♯ₗ q
                p♯q = ∈∉→♯ₗ Q∈p Q∉q
            in
             meet p♯q ∉ join P♯Q

    -- there exists 3 diferent points on every line
    Ax7 : ∀ l → ∃ \P₁ 
              → ∃ \P₂ 
              → ∃ \P₃  
              → ( P₁ ∈ l × P₂ ∈ l × P₃ ∈ l × 
                  P₁ ♯ₚ P₂ × P₁ ♯ₚ P₃ × P₂ ♯ₚ P₃
                )
    -- there exists 3 diferent lines passing for every point
    Ax8 : ∀ P → ∃ \l₁ 
              → ∃ \l₂ 
              → ∃ \l₃  
              → ( P ∈ l₁ × P ∈ l₂ × P ∈ l₃ 
                × l₁ ♯ₗ l₂ × l₁ ♯ₗ l₃ × l₂ ♯ₗ l₃
                )
    -- there exists a point
    Ax9 : Σ Point \ _ → ⊤  


  -- lemma 3
  -- line outside a point
  ∀P∃l∌P : ∀ P → ∃ \l → P ∉ l
  ∀P∃l∌P P with Ax8 P 
  ...      | l₁ , l₂ , _ , P∈l₁ , P∈l₂ , _ , l₁♯l₂ , _ 
           with Ax7 l₂ 
  ...      | R₁ , R₂ , _ , R₁∈l₂ , R₂∈l₂ , _ , R₁♯R₂ , _ 
           with l₁♯l₂ 
  ...      | Q , Q∈l₁ , Q∉l₂ 
           with R₁♯R₂ 
  ...      | m , R₁∈m , R₂∉m 
    = case Ax2 P R₂∉m of 
      \{ (inj₁ P∉m) → m , P∉m
       ; (inj₂ P♯R₂) → let PR₂=l₂ : ¬ (join P♯R₂ ♯ₗ l₂)
                           PR₂=l₂ = unq-ln P♯R₂ joinₗ joinᵣ P∈l₂ R₂∈l₂
                           Q∉PR₂ : Q ∉ join P♯R₂
                           Q∉PR₂ = subs∉₂ Q∉l₂ PR₂=l₂  

                       in _ , (Ax5  Q∉PR₂)
                 
       }
    


  ∀l∃P∉l : ∀ l → ∃ \P → P ∉ l
  ∀l∃P∉l l  with Ax7 l 
  ...       |  P , _ , _ , P∈l , _ 
            with ∀P∃l∌P P 
  ...       | m , P∉m
            with Ax7 m
  ...       | R₁ , R₂ , _ , R₁∈m , R₂∈m , _ , R₁♯R₂ , _
            =  qed

       where 
             R₁R₂=m : join R₁♯R₂ =ₗ m
             R₁R₂=m = unq-ln R₁♯R₂ joinₗ joinᵣ R₁∈m R₂∈m
             P∉R₁R₂ : P ∉ join R₁♯R₂
             P∉R₁R₂ = subs∉₂ P∉m R₁R₂=m
          
             R₁∉R₂P = Ax5 P∉R₁R₂
             
             l♯m : l ♯ₗ m
             l♯m = P , (P∈l , P∉m)            

             Q = meet l♯m


             qed : ∃ \P → P ∉ l
             qed with Ax2 Q R₁∉R₂P 
             qed | inj₁ Q∉R₂P =  R₂ , R₂∉l 
                 where
                        P♯Q = ∈∉→♯ₚ joinᵣ Q∉R₂P
                        
                        R₂∉PQ : R₂ ∉ join P♯Q
                        R₂∉PQ = Ax5 Q∉R₂P

                        l=PQ : l =ₗ join P♯Q
                        l=PQ = unq-ln P♯Q P∈l meetₗ joinₗ joinᵣ
                        R₂∉l : R₂ ∉ l
                        R₂∉l = subs∉₂ R₂∉PQ l=PQ

             qed | inj₂ Q♯R₁ = R₁ , R₁∉l
                 where
                       QR₁=m : join Q♯R₁ =ₗ m
                       QR₁=m = unq-ln Q♯R₁ joinₗ joinᵣ meetᵣ R₁∈m 
                       
                       P∉QR₁ : P ∉ join Q♯R₁ 
                       P∉QR₁ = subs∉₂ P∉m QR₁=m


                       P♯Q : P ♯ₚ Q
                       P♯Q = _ , joinᵣ , (Ax5 P∉QR₁)

                       R₁∉PQ =  Ax5 (Ax5 P∉QR₁)

                       l=PQ  : l =ₗ join P♯Q
                       l=PQ  = unq-ln P♯Q P∈l meetₗ joinₗ joinᵣ
                       
                       R₁∉l  : R₁ ∉ l
                       R₁∉l  = subs∉₂ R₁∉PQ l=PQ

  lemma-e : ∀ P Q l 
            → (P∉l : P ∉ l) → (Q∈l : Q ∈ l) 
            → let Q♯P : Q ♯ₚ P
                  Q♯P = ∈∉→♯ₚ Q∈l  P∉l
              in 
                 ∃ \R → R ∈ l × R ∉ join Q♯P 
  lemma-e P Q l P∉l Q∈l with ∀P∃l∌P Q 
  lemma-e P Q l P∉l Q∈l | m , Q∉m = R , meetₗ , R∉QP
          where Q♯P : Q ♯ₚ P
                Q♯P = (l , Q∈l , P∉l)
                l♯m :  l ♯ₗ m
                l♯m = (Q , Q∈l , Q∉m)

                R = meet l♯m
                R♯Q : R ♯ₚ Q
                R♯Q =  m , meetᵣ , Q∉m


                RQ=l : join R♯Q =ₗ l
                RQ=l = unq-ln R♯Q joinₗ joinᵣ meetₗ Q∈l  
                                               
                P∉RQ : P ∉ join R♯Q
                P∉RQ = subs∉₂ P∉l RQ=l

                R∉QP : R ∉ join Q♯P
                R∉QP = subs∉₂ (Ax5 P∉RQ) (unq-ln Q♯P joinₗ joinᵣ joinₗ joinᵣ)  
                       -- This substitution is required
                       -- because Ax5 constructs a different proof of R♯Q
                       -- i.e : join {P} {Q} p1  = join {P} {Q} p2




  -- ♯ₚ is an appartness relation
  isApartness-♯ₚ : IsApartness _♯ₚ_
  isApartness-♯ₚ = record { irreflexive = λ  { (_ , P∈l , P∉l) → P∈l P∉l }
                          ; cotransitivity = λ {X Y} Z  →  cotrans Z X Y
                          }
                 where
                   sym :  ∀ X Y → X ♯ₚ Y → Y ♯ₚ X
                   sym X Y (l , X∈l , Y∉l)  
                       with  lemma-e Y X l Y∉l  X∈l  
                   ...    |  (R , R∈l , R∉XY)  
                          =  join R♯Y , joinᵣ , X∉RY

                       where 
                         R♯Y : R ♯ₚ Y
                         R♯Y =  l , R∈l , Y∉l
                         X∉RY : X ∉ join R♯Y
                         X∉RY = subs∉₁ (Ax6 R∉XY Y∉l R∈l joinᵣ) (unq-pt (Y , joinᵣ , Y∉l) joinₗ X∈l meetₗ meetᵣ) 

                   cotrans : ∀ Z X Y  → X ♯ₚ Y →  Z ♯ₚ X ⊎ Z ♯ₚ Y
                   cotrans Z X Y (l , X∈l , Y∉l) with Ax2 Z Y∉l 
                   cotrans Z X Y (l , X∈l , Y∉l) | inj₁ Z∉l = inj₁ (sym _ _ X♯Z)
                               where X♯Z : X ♯ₚ Z 
                                     X♯Z =  l , X∈l , Z∉l
                   cotrans Z X Y (l , X∈l , Y∉l) | inj₂ Z♯Y = inj₂ Z♯Y

  -- ♯ₗ is an appartness relation
  isApartness-♯ₗ : IsApartness _♯ₗ_
  isApartness-♯ₗ = record { irreflexive = λ  { (_ , P∈l , P∉l) → P∈l P∉l }
                          ; cotransitivity = λ {X Y} Z  →  cotrans Z X Y
                          }
                 where
                   sym :  ∀ r s → r ♯ₗ s → s ♯ₗ r
                   sym r s (X , X∈r , X∉s) = qed  
                       where
                         r♯s = X , X∈r , X∉s 

                         Q = meet r♯s
                 
                         qed : s ♯ₗ r
                         qed with lemma-e X Q s X∉s meetᵣ  
                         qed | R , R∈s , R∉QX = R , R∈s , subs∉₂ R∉QX (unq-ln (s , meetᵣ , X∉s) meetₗ X∈r joinₗ joinᵣ) 


                   cotrans : ∀ z x y → x ♯ₗ y →  z ♯ₗ x ⊎ z ♯ₗ y
                   cotrans z x y (P , P∈x , P∉y) with Ax1 z P∉y
                   cotrans z x y (P , P∈x , P∉y) | inj₁ P∉z = inj₁ (sym _ _ (_ , P∈x , P∉z ))
                   cotrans z x y (P , P∈x , P∉y) | inj₂ z♯y = inj₂ z♯y


  -- setoids for points and lines
  open Setoid♯ ⦃...⦄
  private
    instance
      Point♯ : Setoid♯ a (c ⊔ b) 
      Point♯ = record { Carrier = Point ; _♯_ = _♯ₚ_ ; isApartness = isApartness-♯ₚ }

      Line♯ : Setoid♯ b (c ⊔ a) 
      Line♯ = record { Carrier = Line ; _♯_ = _♯ₗ_ ; isApartness = isApartness-♯ₗ }

  open IsRel♯ ⦃...⦄
  private
    instance
        isR♯-♯-P : IsRel♯ _ _ _
        isR♯-♯-P = isRel♯-♯  {S = Point♯}

  lemma-f : ∀ {l m P} → (l♯m : l ♯ m) → P ∈ l → P ♯ meet l♯m → P ∉ m 
  lemma-f {l} {m} {P} l♯m P∈l P♯meet
          with symmetry l♯m
  ... | Q , Q∈m , Q∉l = subs∉₂ P∉MQ (unq-ln M♯Q meetᵣ Q∈m joinₗ joinᵣ)
      where
        Q∉PM : Q ∉ join P♯meet
        Q∉PM = subs∉₂ Q∉l (unq-ln P♯meet joinₗ joinᵣ P∈l meetₗ)

        M♯Q : meet l♯m ♯ Q
        M♯Q =  l , meetₗ , Q∉l

        -- P∉MQ : P ∉ join M♯Q
        P∉MQ = Ax5 Q∉PM
        
  --  outside a la Heyting-Mandelkern
  _∉∉_   :  Point → Line → Set _
  P ∉∉ l = ∀ {Q} → Q ∈ l → P ♯ Q
  
  -- these lemmas show the equivalence among ∉ of Van Dalen (primitive) and ∉ of Mandelkern (∀ Q ∈ l : P ♯ Q )
  lemma-∉₁ : ∀ {P l} → P ∉ l → ∀ {Q} → Q ∈ l → P ♯ Q 
  lemma-∉₁  P∉l Q∈l = symmetry (_ , Q∈l , P∉l)

  lemma-∉₂ :  ∀ {P l} →  (∀ {Q} → Q ∈ l → P ♯ Q) → P ∉ l
  lemma-∉₂ {P} {l} ∀Q∈l→P♯Q = qed
           where
             Q : Point
             Q = proj₁ (Ax7 l)
             Q∈l : Q ∈ l
             Q∈l = proj₁ (proj₂ (proj₂ (proj₂ (Ax7 l))))

             P♯Q : P ♯ Q
             P♯Q = ∀Q∈l→P♯Q Q∈l

             qed : P ∉ l
             qed with P♯Q
             ... | r , P∈r , Q∉r = subs∉₂ P∉HQ (unq-ln (r , meetᵣ , Q∉r) meetₗ Q∈l joinₗ joinᵣ) 
              where 
                l♯r : l ♯ r
                l♯r = Q , Q∈l , Q∉r
                --
                H = meet l♯r
                --
                P♯H : P ♯ H
                P♯H = ∀Q∈l→P♯Q meetₗ
                --
                Q∉PH :  Q ∉ join P♯H
                Q∉PH = subs∉₂ Q∉r (unq-ln P♯H joinₗ joinᵣ P∈r meetᵣ) 
                --
                P∉HQ = Ax5  Q∉PH

  --  a projective plane (Mandelkern )from an "outside" structure (van Dalen)
  projectivePlane : ProjectivePlane a (c ⊔ b) b (c ⊔ a) c
  projectivePlane = 
    record
    { Point♯ = Point♯
    ; Line♯ = Line♯
    ; Outside
      = record 
        { R = _∉_
        ; isRel = record { sound = λ A≈B c≈d A∉c → subs∉₁ (subs∉₂ A∉c (sym c≈d)) (sym A≈B) } }
        ; Incidence
           = record 
             { R = _∈_
             ; isRel = record { sound =  λ a≈b c≈d a∈c  b∉d 
                                         → a∈c (subs∉₁ (subs∉₂ b∉d c≈d) a≈b) }
             }
         ; isProjectivePlane = record
            { C0 = λ P∉l Q∈l → symmetry (∈∉→♯ₚ Q∈l P∉l)
            ; P₀ = proj₁ Ax9
            ; l₀ = (proj₁ (∀P∃l∌P (proj₁ Ax9)) )
            ; P₀∉l₀ = proj₂ (∀P∃l∌P (proj₁ Ax9))
            ; join = join
            ; joinₗ = joinₗ
            ; joinᵣ = joinᵣ
            ; unq-join = λ P♯Q P∈l Q∈l → unq-ln P♯Q P∈l Q∈l joinₗ joinᵣ 
            ; meet = meet
            ; meetₗ = meetₗ
            ; meetᵣ = meetᵣ
            ; unq-meet =  λ r♯s P∈r P∈s → unq-pt r♯s P∈r P∈s meetₗ meetᵣ 
            ; point₁ =    λ r → proj₁ $ Ax7 r
            ; point₂ =    λ r → proj₁ $ proj₂ $ Ax7 r
            ; point₃ =    λ r → proj₁  $ proj₂ $ proj₂ $ Ax7 r
            ; ∈-point₁ =  λ r → proj₁  $ proj₂ $ proj₂ $ proj₂ $ Ax7 r
            ; ∈-point₂ =  λ r → proj₁  $ proj₂ $ proj₂ $ proj₂ $ proj₂ $ Ax7 r
            ; ∈-point₃ =  λ r →  proj₁  $ proj₂ $ proj₂ $ proj₂ $ proj₂ $ proj₂ $ Ax7 r
            ; point-i♯j = λ r →  proj₂  $ proj₂ $ proj₂ $ proj₂ $ proj₂ $ proj₂ $ Ax7 r
            ; C5 =  ∈∉→♯ₗ
            ; C6 = id 
            ; C7 =  λ {l} {m} {P} → c7 l m P 
           
            }
        }
        
        where   c7 : ∀ l m P → (l♯m : l ♯ m)
                     → (P ♯ meet l♯m)
                     → (P ∉ l) ⊎ (P ∉ m)
                c7 l m P l♯m P♯M =
                  case cotransitivity (join P♯M) l♯m of
                  \{ (inj₁ PM♯l) → inj₁ (lemma-f PM♯l joinₗ (P♯M ⇒⟨ unq-pt PM♯l joinᵣ meetₗ meetₗ meetᵣ ⟩))
                   ; (inj₂ PM♯m) → inj₂ (lemma-f PM♯m joinₗ (P♯M ⇒⟨ unq-pt PM♯m joinᵣ meetᵣ meetₗ meetᵣ ⟩))
                   }


module ToOutside {a b c d e} (PP : ProjectivePlane a b c d e) where

  open ProjectivePlane.ProjectivePlane PP
  open import ProjectivePlane.PropertiesGeneral PP
  open ProjectivePlane.Setoid♯Instances PP
  open ProjectivePlane.Rel♯Instances PP
  open import ProjectivePlane.Duality
  module Dual = ProjectivePlane.ProjectivePlane (dual PP)

  
  _♯ₚ_ : Point → Point → Set _
  P ♯ₚ Q = ∃ \l → ¬(P ∉ l) × Q ∉ l

  _♯ₗ_ : Line → Line → Set _
  l ♯ₗ r = ∃ \P → ¬(P ∉ l) × P ∉ r


  
  ♯→♯ₗ : ∀ {l r : Line} → (l ♯ r) →  ∃  \P → ¬ (P ∉ l) × P ∉ r
  ♯→♯ₗ {l} {r} l♯r = proj₁ pp , C6← (proj₁ (proj₂ pp))
                              , C7-a l♯r (symmetry $ proj₂ (proj₂ pp)) (proj₁ (proj₂ pp))
       where 
         A : Point
         A = meet l♯r
  
         pp : ∃ \P → P ∈ l × A ♯ P
         pp with cotransitivity A (proj₁ (point-i♯j l))
         pp | inj₁ A♯P₁ = _ ,  ∈-point₁ l , A♯P₁
         pp | inj₂ A♯P₂ = _ ,  ∈-point₂ l , A♯P₂

  ♯→♯ₚ : ∀ {P Q} → P ♯ Q → P ♯ₚ Q
  ♯→♯ₚ {P} {Q} P♯Q = proj₁ pp ,  C6← (proj₁ (proj₂ pp)) , C7-b (symmetry P♯Q) (proj₂ (proj₂ pp)) joinₗ (proj₁ (proj₂ pp)) joinᵣ
    where
      l : Line
      l = join P♯Q

      pp : ∃ \r → P ∈ r × l ♯ r
      pp with cotransitivity l (proj₁ (Dual.point-i♯j P))
      pp | inj₁ l♯l₁ = _ ,  Dual.∈-point₁ P , l♯l₁
      pp | inj₂ l♯l₂ = _ ,  Dual.∈-point₂ P , l♯l₂

  _∈'_ : Point → Line → Set _
  P ∈' l = ¬ (P ∉ l)

  ∈'→∈ : ∀ {P l} → P ∈' l → P ∈ l
  ∈'→∈  = C6
  ∈→∈' : ∀ {P l} → P ∈ l → P ∈' l
  ∈→∈'  = C6←


  ax1 : ∀ {A l} m → A ∉ l → A ∉ m ⊎  m ♯ₗ l
  ax1 {A} {l} m A∉l =
    let C = point₁ l
        A♯C : A ♯ C
        A♯C = C0 A∉l (∈-point₁ l)
        AC♯l : join A♯C ♯ l
        AC♯l = C5 joinₗ A∉l 
    in case cotransitivity m AC♯l of 
                 \{ (inj₁ m♯AC) → case cotransitivity (meet m♯AC) A♯C of
                                  \{ (inj₁ Q♯A) → inj₁ (C7-a (symmetry m♯AC) (symmetry Q♯A ⇒⟨ meet-comm ⟩) joinₗ)
                                   ; (inj₂ Q♯C) → inj₂ (♯→♯ₗ (symmetry (C5 (∈-point₁ l) (C7-a (symmetry m♯AC) (symmetry Q♯C ⇒⟨ meet-comm ⟩) joinᵣ))))
                                   }
                  ; (inj₂ m♯l)  → inj₂ (♯→♯ₗ m♯l)
                  }
  ax3-a  : ∀ {P Q} → (∃ \r → ¬(P ∉ r) × Q ∉ r) →  ∃ \l →  ¬ (P ∉ l) × ¬(Q ∉ l)
  ax3-a  {P} {Q} (r , ¬P∉r , Q∉r)  =  join (symmetry (C0 Q∉r (C6 ¬P∉r))) , C6← joinₗ , C6← joinᵣ

  ax3-b :  ∀ {P Q l r}  → P ♯ₚ Q
                        →  ¬(P ∉ l) → ¬(Q ∉ l) 
                        →  ¬(P ∉ r) → ¬(Q ∉ r)
                        →  ¬(l ♯ₗ r)
  ax3-b {P} {Q} P♯ₚQ ¬P∉l ¬Q∉l ¬P∉r ¬Q∉r l♯ₗr = trans (unq-join P♯Q (C6 ¬P∉l) (C6 ¬Q∉l))
                                             (sym (unq-join P♯Q (C6 ¬P∉r) (C6 ¬Q∉r)))
                                             (C5 (C6 $ proj₁ (proj₂ l♯ₗr)) (proj₂ (proj₂ l♯ₗr)))
     where
        P♯Q : P ♯ Q
        P♯Q = case P♯ₚQ of
              \{ ( _ , P∈- , Q∉- ) → symmetry (C0 Q∉- (C6 P∈-)) }

  join' : ∀ {P Q} → P ♯ₚ Q → Line
  join' (_ , P∈- , Q∉- )= join $ symmetry $ C0 Q∉- (C6 P∈-)

  meet' : ∀ {l r} → l ♯ₗ r → Point
  meet' (_ , -∈l , -∉r ) = meet $ C5 (C6 -∈l) -∉r

  ax5 : ∀ {P Q R} 
        → {P♯Q : P ♯ₚ Q} 
        → (R∉PQ : R ∉ join' P♯Q) 
        →  let 
             Q♯R : Q ♯ₚ R
             Q♯R = _ , C6← joinᵣ , R∉PQ
           in 
               P ∉ join' Q♯R
  ax5 R∉PQ = lemma-triangle.B∉AC R∉PQ ⇒⟨ join-comm ⟩

  ax6 :  ∀ {P Q p  q}
          → (P∉p : P ∉ p) → (Q∉q : Q ∉ q)
          → (P∈'q : P ∈' q) → (Q∈'p : Q ∈' p)
          → let P♯Q : P ♯ₚ Q
                P♯Q = q , P∈'q , Q∉q
                p♯q : p ♯ₗ q
                p♯q = Q , Q∈'p , Q∉q
            in
             meet' p♯q ∉ join' P♯Q

  ax6 {P} {Q} {p} {q} P∉p Q∉q P∈'q Q∈'p = lemma-triangle.C∉AB  Q∉PM ⇒⟨ join-comm ⟩
    where
      p♯q : p ♯ q
      p♯q = C5 (C6 Q∈'p) Q∉q

      M : Point
      M = meet p♯q

      P♯M : P ♯ M
      P♯M = C0 P∉p meetₗ

      Q∉PM : Q ∉ join P♯M
      Q∉PM = Q∉q  ⇒⟨ unq-join _ (C6 P∈'q) meetᵣ ⟩

  ax7 : ∀ l → ∃ \P₁ 
              → ∃ \P₂ 
              → ∃ \P₃  
              → ( P₁ ∈' l × P₂ ∈' l × P₃ ∈' l × 
                  P₁ ♯ₚ P₂ × P₁ ♯ₚ P₃ × P₂ ♯ₚ P₃
                )
  ax7 l =  point₁ l , point₂ l , point₃ l ,
           ∈→∈' (∈-point₁ l) , ∈→∈' (∈-point₂ l) , ∈→∈' (∈-point₃ l) ,
           ♯→♯ₚ  (proj₁ (point-i♯j l)) , ♯→♯ₚ (proj₁ (proj₂ (point-i♯j l))) ,  ♯→♯ₚ (proj₂ (proj₂ (point-i♯j l)))
 

fromProjectivePlane : ∀ {a b c d e}
                      → (PP : ProjectivePlane a b c d e)
                      → let open ProjectivePlane.ProjectivePlane PP
                        in  IsOutside Point Line _∉_
fromProjectivePlane PP
  = record
      { Ax1   =  ToOutside.ax1 PP 
      ; Ax2   =  ToOutside.ax1 (dual PP)
      ; Ax3-a =  ToOutside.ax3-a PP
      ; Ax3-b =  ToOutside.ax3-b PP
      ; Ax4-a =  ToOutside.ax3-a (dual PP)
      ; Ax4-b =  ToOutside.ax3-b (dual PP)
      ; Ax5   =  ToOutside.ax5 PP
      ; Ax6   =  λ P∉p Q∉q P∈q Q∈p →  ⟨  ≈meet  ⟩⇐ ToOutside.ax6  PP P∉p Q∉q P∈q Q∈p 
      ; Ax7   =  ToOutside.ax7 PP
      ; Ax8   =  ToOutside.ax7 (dual PP)
      ; Ax9   =  ProjectivePlane.P₀ PP , _
      }                        
    where
          open import ProjectivePlane.Duality
          open ProjectivePlane.Setoid♯Instances
          open  ProjectivePlane.Rel♯Instances PP
          open import ProjectivePlane.PropertiesGeneral PP

                          
