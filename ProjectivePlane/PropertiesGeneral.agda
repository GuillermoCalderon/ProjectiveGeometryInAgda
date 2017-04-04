{-
  This module is only a front-end to incorporate 
  properties with its dual ones with convenient names

  we  can always incorporate new dual operations as follows:

     open import ProjectivePlane.Properties (dual PP)
         using ()
         renaming ( foo to foo1 ;  ... )

  A more general importing mechanism can be used:

         open import ProjectivePlane.Properties (dual PP) as Dual

  so, dual of "foo" is denotes as "Dual.foo"
 
-}



open import ProjectivePlane


module ProjectivePlane.PropertiesGeneral {a b c d e}
    (PP : ProjectivePlane a b c d e)
    where

    open ProjectivePlane.ProjectivePlane PP
    open import ProjectivePlane.Duality
    open import ProjectivePlane.Properties PP public
    open import ProjectivePlane.Properties (dual PP)
      using ()
      renaming ( ∉join to ∉meet
               ; join-comm to meet-comm
               ; sym-join to sym-meet
               ; ≈join   to ≈meet
               ; join-cong to meet-cong
               ; join-flip-cong to meet-flip-cong
               ;  meet-joinᵣᵣ to join-meetᵣᵣ
               ;  meet-joinₗᵣ to join-meetₗᵣ
               ;  meet-joinᵣₗ to join-meetᵣₗ 
               ;  meet-joinₗₗ to join-meetₗₗ
               )
      public
     

