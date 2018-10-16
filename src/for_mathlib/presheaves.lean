import category_theory.presheaves
import category_theory.sheaves
import category_theory.limits
import for_mathlib.open_set

open category_theory
open category_theory.examples
open category_theory.limits

universes u v w₁ w₂

section under_set
variables {X : Top.{v}}

def under_set (B : set (open_set X)) (U : open_set X) : set B := (λ U' : B, U'.1 ⊆ U)

variables {B : set (open_set X)} {U U₁ U₂ U₃ : open_set X}

instance : category (under_set B U) := by unfold under_set; apply_instance

variables (B) (U)

def under_set.map (ι : U₁ ⟶ U₂) : under_set B U₂ ⥤ under_set B U₁ :=
{ obj  := λ U, ⟨U.1, set.subset.trans U.2 ι.1.1⟩,
  map' := λ U U' f, f }

lemma under_set.map_map (ι : U₁ ⟶ U₂) (ι' : U₂ ⟶ U₃) :
under_set.map B ι' ⋙ under_set.map B ι = under_set.map B (ι ≫ ι') := by tidy

def under_set.embedding : under_set B U ⥤ B := full_subcategory_embedding (under_set B U)

lemma under_set.map_embedding (ι : U₁ ⟶ U₂) :
under_set.map B ι ⋙ under_set.embedding B U₁ = under_set.embedding B U₂ := by tidy

end under_set

section extend
open open_set
variables {X : Top.{v}}
variables {V : Type u} [𝒱 : category.{u v} V] [has_limits.{u v} V]
include 𝒱

variables {B : set (open_set X)} (F : presheaf B V)

def extend : presheaf (open_set X) V :=
{ obj  := λ U, limit ((under_set.embedding B U) ⋙ F),
  map' := λ U₁ U₂ ι, limit.pre ((under_set.embedding B U₁) ⋙ F) (under_set.map B ι) }

def Γ {C : Type w₁} [category.{w₁ w₂} C] (U : C) (F : presheaf C V) : V := F.obj U

lemma extend_val (U : open_set X) : Γ U (extend F) = limit ((under_set.embedding B U) ⋙ F) := rfl

lemma extend_val_basic_open (U : B) : Γ U.1 (extend F) ≅ Γ U F :=
by rw extend_val; exact
{ hom := limit.π (under_set.embedding B (U.val) ⋙ F) ⟨U, set.subset.refl _⟩,
  inv := limit.lift (under_set.embedding B (U.val) ⋙ F)
  { X := Γ U F,
    π := λ U', F.map (ulift.up (plift.up U'.2)) } }

namespace sheaf_on_basis
variables (hB : is_basis B)

def sheaf_hypothesis (F : presheaf B V) : Prop := ∀ U : B, ∀ Us ⊆ B, sorry

-- Condition to be a "sheaf on a basis":
-- A sheaf F of sets on B is a presheaf of sets on B which satisfies the following additional property:
-- Given any U∈B, and any covering U=⋃i∈IUi with Ui∈B,
--  and any coverings Ui∩Uj=⋃k∈IijUijk with Uijk∈B the sheaf condition holds: 
    -- For any collection of sections si∈F(Ui), i∈I such that ∀i,j∈I, ∀k∈Iij
    -- si|Uijk=sj|Uijk
    -- there exists a unique section s∈F(U) such that si=s|Ui for all i∈I.




-- The following is very false and need some sort of sheaf condition for F on the basis
-- 
-- instance [has_products.{u v} V] {F : presheaf B V} : is_sheaf (extend F) :=
-- { sheaf_condition := λ cover,
--   { lift := λ s, begin
--     sorry
--   end
--   } }

end sheaf_on_basis

end extend
