import data.set.basic ring_theory.ideals 
universes u v

namespace quotient
variables {α : Type u} {β : Type v} [s : setoid α]
lemma prod_preimage_eq_image (g : quotient s → β) {h : α → β} (Hh : h = g ∘ quotient.mk) (r : set (β × β)) :
  {x : quotient s × quotient s | (g x.1, g x.2) ∈ r} =
  (λ a : α × α, (⟦a.1⟧, ⟦a.2⟧)) '' ((λ a : α × α, (h a.1, h a.2)) ⁻¹' r) :=
  Hh.symm ▸
  set.ext (λ ⟨a₁, a₂⟩, ⟨quotient.induction_on₂ a₁ a₂
    (λ a₁ a₂ h, ⟨(a₁, a₂), h, rfl⟩),
    λ ⟨⟨b₁, b₂⟩, h₁, h₂⟩, show (g a₁, g a₂) ∈ r, from
    have h₃ : ⟦b₁⟧ = a₁ ∧ ⟦b₂⟧ = a₂ := prod.ext_iff.1 h₂,
     h₃.1 ▸ h₃.2 ▸ h₁⟩)

end quotient

namespace quotient_ring -- move this to the right file
open is_submodule
variables {α : Type u} [comm_ring α] {β : Type v} [comm_ring β]

local attribute [instance] quotient_rel

def lift (S : set α) [is_ideal S] (f : α → β) [is_ring_hom f] (H : ∀ (a : α), a ∈ S → f a = 0) :
quotient S → β :=
quotient.lift f $ λ a b h,
eq_of_sub_eq_zero (by rw quotient_rel_eq at h;
  simpa only [is_ring_hom.map_sub f] using H _ h)

variables {S : set α} [is_ideal S] {f : α → β} [is_ring_hom f] {H : ∀ (a : α), a ∈ S → f a = 0} {a : α}

@[simp] lemma lift_mk : lift S f H ⟦a⟧ = f a := rfl

instance : is_ring_hom (lift S f H) :=
{ map_one := by show lift S f H ⟦1⟧ = 1; simp [is_ring_hom.map_one f],
  map_add := λ a₁ a₂, quotient.induction_on₂ a₁ a₂ $ λ a₁ a₂, begin
    show lift S f H (mk a₁ + mk a₂) = lift S f H ⟦a₁⟧ + lift S f H ⟦a₂⟧,
    have := quotient_ring.is_ring_hom_mk S,
    rw ← this.map_add,
    show lift S f H (⟦a₁ + a₂⟧) = lift S f H ⟦a₁⟧ + lift S f H ⟦a₂⟧,
    simp only [lift_mk, is_ring_hom.map_add f],
  end,
  map_mul := λ a₁ a₂, quotient.induction_on₂ a₁ a₂ $ λ a₁ a₂, begin
    show lift S f H (mk a₁ * mk a₂) = lift S f H ⟦a₁⟧ * lift S f H ⟦a₂⟧,
    have := quotient_ring.is_ring_hom_mk S,
    rw ← this.map_mul,
    show lift S f H (⟦a₁ * a₂⟧) = lift S f H ⟦a₁⟧ * lift S f H ⟦a₂⟧,
    simp only [lift_mk, is_ring_hom.map_mul f],
  end }

end quotient_ring
