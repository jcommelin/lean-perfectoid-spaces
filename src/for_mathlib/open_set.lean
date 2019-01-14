import category_theory.examples.topological_spaces
import order.lattice order.galois_connection
import category_theory.tactics.obviously

universes u v

open category_theory
open category_theory.examples

namespace open_set
open topological_space lattice

variables {X : Top.{v}}

local attribute [back] topological_space.is_open_inter
local attribute [back] is_open_union
local attribute [back] open_set.is_open

local attribute [back] set.subset_union_left
local attribute [back] set.subset_union_right

local attribute [back'] set.inter_subset_left
local attribute [back'] set.inter_subset_right

@[simp] instance : has_inter (open_set X) :=
{ inter := λ U V, ⟨ U.s ∩ V.s, by obviously ⟩ }

@[simp] instance : has_union (open_set X) :=
{ union := λ U V, ⟨ U.s ∪ V.s, by obviously ⟩ }

instance : partial_order (open_set X) :=
{ le_antisymm := λ U₁ U₂ _ _, by cases U₁; cases U₂; tidy,
   .. open_set.preorder }

def interior (s : set X) : open_set X :=
{ s := interior s,
  is_open := is_open_interior }

def gc : galois_connection (@open_set.s X) interior :=
λ U s, ⟨λ h, interior_maximal h U.is_open, λ h, le_trans h interior_subset⟩

def gi : @galois_insertion (order_dual (set X)) (order_dual (open_set X)) _ _ interior (@open_set.s X) :=
{ choice := λ s hs, { s := s, is_open := interior_eq_iff_open.mp $ le_antisymm interior_subset hs },
  gc := galois_connection.dual _ _ gc,
  le_l_u := λ _, interior_subset,
  choice_eq := λ s hs, le_antisymm interior_subset hs }

instance : complete_lattice (open_set X) :=
@order_dual.lattice.complete_lattice _
  (@galois_insertion.lift_complete_lattice
    (order_dual (set X)) (order_dual (open_set X)) _ interior (@open_set.s X) _ gi)

@[simp] lemma top_s : (⊤ : open_set X).s = set.univ :=
begin
  refine le_antisymm (set.subset_univ _) (_),
  change set.univ ≤ (interior ⊤ : order_dual $ open_set X).s,
  dsimp [interior],
  convert le_of_eq interior_univ.symm,
end

@[simp] lemma Sup_s {Us : set (open_set X)} : (Sup Us).s = ⋃₀ (open_set.s '' Us) :=
by rw [@galois_connection.l_Sup _ _ _ _ (@open_set.s X) interior (gc) Us, set.sUnion_image]

def is_basis (B : set (open_set X)) : Prop := is_topological_basis (open_set.s '' B)

lemma is_basis_iff₁ {B : set (open_set X)} :
is_basis B ↔ ∀ {U : open_set X} {x : X}, x ∈ U → ∃ U' ∈ B, x ∈ U' ∧ U' ⊆ U :=
begin
split; intro h,
{ rintros ⟨sU, hU⟩ x hx,
  rcases (mem_nhds_of_is_topological_basis h).mp (mem_nhds_sets hU hx) with ⟨sV,⟨⟨V,H₁,H₂⟩,hsV⟩⟩,
  refine ⟨V,H₁,_⟩,
  cases V, dsimp at H₂, subst H₂, exact hsV },
  { refine is_topological_basis_of_open_of_nhds _ _,
    { rintros sU ⟨U,⟨H₁,H₂⟩⟩, subst H₂, exact U.is_open },
    { intros x sU hx hsU,
      rcases @h (⟨sU,hsU⟩ : open_set X) x hx with ⟨V,hV,H⟩,
      refine ⟨V, ⟨V,hV,rfl⟩, H⟩ } }
end

-- lemma is_basis_iff₂ {B : set (open_set X)} :
-- is_basis B ↔ ∀ U : open_set X, ∃ Us ⊆ B, U = Sup Us :=
-- begin
--   split,
--   { intros hB U,
--     rcases sUnion_basis_of_is_open hB U.is_open with ⟨sUs, H, hU⟩,
--     existsi {U : open_set X | U ∈ B ∧ U.s ∈ sUs},
--     split,
--     { intros U hU, exact hU.left },
--     { have : sUs = open_set.s '' {U : open_set X | U ∈ B ∧ U.s ∈ sUs},
--       begin sorry end,
--       rw [this, ← Sup_s] at hU,
--       refine le_antisymm _ _,
--       exact le_of_eq hU,
--       sorry } },
--   { intro h,
--     rw is_basis_iff₁,
--     intros U x hx,
--     rcases h U with ⟨Us, hUs, H⟩,
--     replace H := congr_arg open_set.s H,
--     rw Sup_s at H,
--     change x ∈ U.s at hx,
--     rw H at hx,
--     rcases set.mem_sUnion.mp hx with ⟨sV, ⟨⟨V,H₁,H₂⟩,hsV⟩⟩,
--     refine ⟨V,hUs H₁,_⟩,
--     cases V, dsimp at H₂, subst H₂,
--     refine ⟨hsV,_⟩,
--     change V_s ⊆ U.s, rw H,
--     exact set.subset_sUnion_of_mem ⟨⟨V_s,V_is_open⟩,⟨H₁,rfl⟩⟩, },
-- end

def univ : open_set X :=
{ s := set.univ,
  is_open := is_open_univ }


def cover_by_basic_opens (B : set (open_set X)) (U : open_set X) :=
{ Us : set (open_set X) | Us ⊆ B ∧ U = Sup Us }

local notation B`-cover` := cover_by_basic_opens B

end open_set
