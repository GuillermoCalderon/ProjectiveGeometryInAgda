{-# OPTIONS --no-eta-equality #-} 

module Relation.Binary.Apartness where

open import Level
open import Relation.Binary 
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open import Relation.Nullary
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Function 
  using (_$_ ;  _∘_ ; case_of_ ; flip; id)


record IsApartness {a b}{A : Set a} (_♯_ :  Rel A b) : Set (a ⊔ b)  where
  field

    irreflexive    :   ∀ {x}      → ¬(x ♯ x)
    cotransitivity :   ∀ {x y} z  →  x ♯ y → z ♯ x ⊎ z ♯ y

  symmetry : ∀ {x y} → x ♯ y → y ♯ x
  symmetry {_} {y} x♯y = 
    case cotransitivity y x♯y of
    \{ (inj₁ y♯x) → y♯x
     ; (inj₂ y♯y) → ⊥-elim $ irreflexive y♯y
     }
     

  -- negation of ♯
  _¬♯_ : A → A → Set b
  x ¬♯ y = ¬ (x ♯ y) 



  isEquivalence-¬♯ : IsEquivalence _¬♯_
  isEquivalence-¬♯ = record 
                         { refl  = irreflexive
                         ; sym   = λ x¬♯y  → x¬♯y ∘ symmetry 
                         ; trans = λ {a} {b} {c} a¬b b¬c a♯c → 
                                 case cotransitivity b a♯c of 
                                 λ{ (inj₁ b♯a) → a¬b $ symmetry b♯a
                                  ; (inj₂ b♯c) → b¬c b♯c
                                  }
                         }

  open IsEquivalence isEquivalence-¬♯ public


 
record Setoid♯ a b : Set (suc (a ⊔ b)) where
  infix 4 _♯_
  infix 4 _≈_
  infixr 4 _-∘-_

  field
    Carrier  : Set a
    _♯_  : Rel Carrier b 
    isApartness : IsApartness _♯_ 
  open IsApartness isApartness public

  -- a more standard symbol for ¬♯
  _≈_  : Carrier → Carrier → Set b
  _≈_  = _¬♯_

  -- a Setoid♯ is a classical Setoid (of standard library)
  setoid : Setoid _ _
  setoid = record {isEquivalence = isEquivalence-¬♯ }

  -- another alias for trans
  _-∘-_ : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
  _-∘-_ = trans


open Setoid♯ public using () 
     renaming ( Carrier to ⟨_⟩ 
              ; setoid  to toSetoid)

-- unary predicate for setoid
record IsPred♯ {a b c}(S : Setoid♯ a b)(P :  ⟨ S ⟩ → Set c) : Set (a ⊔ b ⊔ c) where
  open Setoid♯ S
  field
    sound : ∀ {x y} → P x → x ♯ y ⊎ P y 

  subst : ∀ {x y} → x ≈ y → P x → P y
  subst x≈y px = 
    case sound px of 
    \{ (inj₁ x♯y) → ⊥-elim (x≈y x♯y)
     ; (inj₂ py)  → py
     } 

record Pred♯ {a b} c (S : Setoid♯ a b) : Set (suc (a ⊔ b ⊔ c)) where
  open Setoid♯ S
  field
    P     : Carrier → Set c
    isPred : IsPred♯ S  P
  open IsPred♯ isPred public


-- binary heterogeneous relation for setoid♯
record IsRel♯ {a₁ b₁ a₂ b₂ c}
       (S₁ : Setoid♯ a₁ b₁ )
       (S₂ : Setoid♯ a₂ b₂)
       (R : ⟨ S₁ ⟩ → ⟨ S₂ ⟩ → Set c) 
       : 
       Set (a₁ ⊔ b₁ ⊔ a₂ ⊔ b₂ ⊔ c) where

  infix 5  ⟨_⟩⇐_
  infix 6  _⇒⟨_⟩

  field
    sound :  ∀ {a b c d} 
             → Setoid♯._≈_ S₁ a  b  
             → Setoid♯._≈_ S₂ c  d 
             → R a c → R b d

  open Setoid♯ ⦃...⦄

  private
   instance SS1 = S₁
            SS2 = S₂

  -- left rewriting
  ⟨_⟩⇐_ : ∀ {a₁ a₂ b} → a₂ ≈ a₁ → R a₁ b → R a₂ b 
  ⟨ a₂≈a₁ ⟩⇐ Ra₁b = sound (sym a₂≈a₁) refl Ra₁b 
 
  -- rigth rewriting
  _⇒⟨_⟩ : ∀ {a₁ a₂ b} → R b a₁ → a₁ ≈ a₂ → R b a₂ 
  Rba₁ ⇒⟨ a₁≈a₂ ⟩  = sound refl a₁≈a₂ Rba₁


record Rel♯  {a₁ b₁ a₂ b₂} c
             (S₁ : Setoid♯ a₁ b₁)
             (S₂ : Setoid♯ a₂ b₂)
       : Set (suc (a₁ ⊔ b₁ ⊔ a₂ ⊔ b₂ ⊔ c)) where
  field
    R     : ⟨ S₁ ⟩ → ⟨ S₂ ⟩ → Set c
    isRel : IsRel♯  S₁ S₂ R
  open IsRel♯ isRel public


flip♯ : ∀ {a₁ b₁ a₂ b₂ c} 
        → {S₁ : Setoid♯ a₁ b₁}
        → {S₂ : Setoid♯ a₂ b₂}
        → Rel♯ c S₁ S₂ → Rel♯ c S₂ S₁
flip♯ Rel = record { R = flip R ; isRel = record { sound = flip sound  } }
      where open Rel♯ Rel




isRel♯-♯ : ∀ {a b}{S : Setoid♯ a b} → IsRel♯  S S (Setoid♯._♯_ S)
isRel♯-♯ {S = S} =
     record { sound = λ {a} {b} {c} {d} a≈b c≈d a♯c  
              → case cotransitivity d a♯c of
                \{ (inj₁ d♯a) → 
                        case cotransitivity b d♯a of 
                        \{ (inj₁ b♯d) → b♯d
                         ; (inj₂ b♯a) → ⊥-elim $ a≈b $ symmetry b♯a
                         }
                 ; (inj₂ d♯c) → ⊥-elim (c≈d (symmetry d♯c)) 
                 }
             }
     where open Setoid♯ S


--  another operator for transitivity
isRel♯-≈ : ∀ {a b}{S : Setoid♯ a b} → IsRel♯  S S (Setoid♯._≈_ S)
isRel♯-≈ {S = S} =
     record { sound =  λ a≈b c≈d a≈c  → trans (trans (sym a≈b) a≈c) c≈d }
     where open Setoid♯ S



------------------------------------------------------------------------------
-- functions for setoids
--
record Fun♯ {a₁ b₁ a₂ b₂ : Level}
            (From : Setoid♯ a₁ b₁)
            (To   : Setoid♯ a₂ b₂)
            : Set (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂)
       where


            
   field
     f     : ⟨ From ⟩ → ⟨ To ⟩ 
     sound :  ∀ {a b } → Setoid♯._≈_ From a  b → Setoid♯._≈_ To (f a) (f b)

open Fun♯ public 
     renaming ( f     to  ⟨_⟩$_  
              ; sound to  ⟨_⟩≈_ )

-- function composition
_∙_  : ∀ {a b c d e f} →
         {A : Setoid♯ a b} →
         {B : Setoid♯ c d} →
         {C : Setoid♯ e f} →
         (Fun♯ B C) → Fun♯ A B → Fun♯  A C
F ∙ G = record { f = Fun♯.f F ∘ Fun♯.f G 
                ; sound = Fun♯.sound F ∘ Fun♯.sound G 
                }

-- identity function
IdFun♯ : ∀ {a b} 
         → {A : Setoid♯ a b}
         → Fun♯ A A
IdFun♯ = record { f = id ; sound = id }

-------------------------------------------------------------
-- injective function for setoids
-- IsInjective : {a b c d : Level}
--               {{From : Setoid♯ a b}}
--               {{To   : Setoid♯ c d}}
--               (F : Fun♯ From To)
--               → Set _
-- IsInjective  {{From}} {{To}} F =  ∀ {a b : ⟨ From ⟩ } → a ♯ b → ⟨ F ⟩$  a ♯ ⟨ F ⟩$ b
--             where open Setoid♯ ⦃...⦄

record InjectiveFun♯ 
         {a b c d : Level}
         (From : Setoid♯ a b)
         (To   : Setoid♯ c d)
       : Set (a ⊔ b ⊔ c ⊔ d)
       where
   field
     F     : Fun♯  From To 
     isInjective : ∀ {a b : ⟨ From ⟩ } → Setoid♯._♯_ From a b → Setoid♯._♯_  To (⟨ F ⟩$  a)  (⟨ F ⟩$ b)

open InjectiveFun♯ renaming (F to fun♯ ) public 

IdInjectiveFun♯ : ∀ {a b} 
         → {A : Setoid♯ a b}
         → InjectiveFun♯ A A
IdInjectiveFun♯ = record { F = IdFun♯ ; isInjective = id }

-- composition of injective functions   
_⊙_  : ∀ {a b c d e f} →
         {A : Setoid♯ a b} →
         {B : Setoid♯ c d} →
         {C : Setoid♯ e f} →
         (InjectiveFun♯ B C) → InjectiveFun♯ A B → InjectiveFun♯ A C
F₁ ⊙ F₂ = record { F = (fun♯ F₁) ∙  (fun♯ F₂)
                 ; isInjective = isInjective F₁ ∘ isInjective F₂ }

-----------------------------------------
-- Decidable setoids

record DecSetoid♯ a b : Set (suc (a ⊔ b)) where
  field
    S : Setoid♯ a b
  open  Setoid♯ S -- public

  field
    -- apartness relation is decidable
    _≠?_ : Decidable _♯_

  -- So, _≈_ is decidable too
  _≟_ :  Decidable _≈_
  a ≟ b = case a ≠? b of 
          \{ (no ¬a♯b) → yes ¬a♯b
           ; (yes a♯b) → no (λ a≈b → a≈b a♯b)
           }

  ¬≈→♯ : ∀ {a b} → ¬ (a ≈ b) → a ♯ b
  ¬≈→♯ {a} {b} ¬a≈b with a ≠? b 
  ... | yes a♯b  = a♯b
  ... | no ¬a♯b = ⊥-elim (¬a≈b ¬a♯b)

open DecSetoid♯ using () renaming (S to decToSetoid♯) public


-- DecSetoid is classical setoid defined in standard library of agda (Relation.Binary)
-- DecSetoid and DecSetoid♯ are equivalent
toDecSetoid♯ : ∀ {a b} → DecSetoid a b → DecSetoid♯ a b
toDecSetoid♯ S = 
  record { S = record 
               { _♯_ = λ a b → ¬ (a ≈ b) 
               ; isApartness = 
                   record 
                   { irreflexive = λ ¬x≈x → ¬x≈x refl 
                   ; cotransitivity = 
                        λ {x} {y} z ¬x≈y 
                        → case z ≟ x of
                          \{ (yes z≈x) → inj₂ (λ z≈y → ¬x≈y (trans (sym z≈x) z≈y)) 
                           ; (no ¬z≈x) → inj₁ ¬z≈x }
                   } 
                                     } 
               ; _≠?_ = λ x y → case x ≟ y of 
                                \{ (yes x≈y) → no (λ ¬x≈y → ¬x≈y x≈y)
                                 ; (no ¬x≈y) → yes ¬x≈y }
               } 
               where open DecSetoid S



