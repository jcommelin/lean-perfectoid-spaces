import continuous_valuations
import Huber_pair 

universes u₁ u₂ u₃

local attribute [instance] classical.prop_decidable

open set Spv

-- Wedhorn def 7.23.
definition Spa (A : Huber_pair) : set (Spv A) :=
{v | (v ∈ Cont A) ∧ ∀ r, r ∈ A⁺ → v r ≤ 1}

lemma mk_mem_Spa {A : Huber_pair} {v : Valuation A} : mk v ∈ Spa A ↔ (mk v ∈ Cont A) ∧ ∀ r, r ∈ A⁺ → v r ≤ 1 :=
begin
  split; intro h; split; try { exact h.left };
  intros r hr,
  { rw ← (v.val).map_one,
    apply (out_mk r 1).mp,
    convert h.right r hr,
    exact valuation.map_one _, },
  { rw ← (v.val).map_one at h,
    convert (out_mk r 1).mpr (h.right r hr),
    exact (valuation.map_one _).symm }
end

namespace Spa

variable {A : Huber_pair}

instance : has_coe (Spa A) (Spv A) := ⟨subtype.val⟩

definition basic_open (r s : A) : set (Spa A) :=
{v | v r ≤ v s ∧ v s ≠ 0 }

lemma mk_mem_basic_open {r s : A} {v : Valuation A} {hv : mk v ∈ Spa A} :
(⟨mk v, hv⟩ : Spa A) ∈ basic_open r s ↔ v r ≤ v s ∧ v s ≠ 0 :=
begin
  split; intro h; split,
  { exact (out_mk r s).mp h.left },
  { exact Valuation.ne_zero_of_equiv_ne_zero out_mk h.right },
  { exact (out_mk r s).mpr h.left },
  { exact Valuation.ne_zero_of_equiv_ne_zero (setoid.symm out_mk) h.right }
end

instance (A : Huber_pair) : topological_space (Spa A) :=
topological_space.generate_from {U : set (Spa A) | ∃ r s : A, U = basic_open r s}

lemma basic_open.is_open (r s : A) : is_open (basic_open r s) :=
topological_space.generate_open.basic (basic_open r s) ⟨r, ⟨s, rfl⟩⟩

lemma basic_open_eq (s : A) : basic_open s s = {v | v s ≠ 0} :=
set.ext $ λ v, ⟨λ h, h.right, λ h, ⟨le_refl _, h⟩⟩

-- should only be applied with (HfinT : fintype T) and (Hopen: is_open (span T))
definition rational_open (s : A) (T : set A) : set (Spa A) :=
{v | (∀ t ∈ T, (v t ≤ v s)) ∧ (v s ≠ 0)}

lemma mk_mem_rational_open {s : A} {T : set A} {v : Valuation A} {hv : mk v ∈ Spa A} :
(⟨mk v, hv⟩ : Spa A) ∈ rational_open s T ↔ (∀ t ∈ T, (v t ≤ v s)) ∧ (v s ≠ 0) :=
begin
  split; intro h; split,
  { intros t ht,
    exact (out_mk t s).mp (h.left t ht) },
  { exact Valuation.ne_zero_of_equiv_ne_zero out_mk h.right },
  { intros t ht,
    exact (out_mk t s).mpr (h.left t ht) },
  { exact Valuation.ne_zero_of_equiv_ne_zero (setoid.symm out_mk) h.right }
end

definition rational_open_Inter (s : A) (T : set A) :
rational_open s T = (set.Inter (λ (t : T), basic_open t s)) ∩ {v | v s ≠ 0} :=
set.ext $ λ v, ⟨λ ⟨H1, H2⟩, ⟨set.mem_Inter.2 $ λ t, ⟨H1 _ t.property, H2⟩, H2⟩,
  λ ⟨H1, H2⟩, ⟨λ t ht, (set.mem_Inter.1 H1 ⟨t, ht⟩).1, H2⟩⟩

lemma rational_open_add_s (s : A.R) (T : set A.R) :
rational_open s T = rational_open s (insert s T) :=
set.ext $ λ v,
⟨ λ ⟨H1, H2⟩, ⟨λ t Ht, or.rec_on Ht (λ H, by rw H; exact le_refl _) (H1 t), H2⟩,
  λ ⟨H1, H2⟩, ⟨λ t Ht, H1 t $ set.mem_insert_of_mem _ Ht,H2⟩⟩

lemma rational_open.is_open (s : A) (T : set A) (HfinT : fintype T) :
is_open (rational_open s T) :=
begin
  rw rational_open_Inter,
  apply is_open_inter, swap, rw ← basic_open_eq s, exact basic_open.is_open s s,
  simpa using @is_open_bInter _ _ _ _ (λ t : T, basic_open t.1 s) 
    (finite_mem_finset finset.univ) (λ t ht, basic_open.is_open t s),
end

end Spa

-- goal now to define the 𝓞_X on *rational subsets* and then to extend.

-- to define it on rational subsets it's just a ring completion.

-- remember that a rational open is not actually `rational_open s T` in full
-- generality -- we also need that T is finite and that T generates an open ideal in A.
-- The construction on p73/74 (note typo in first line of p74 -- ideal should be I.D)
-- gives A<T/s> (need completion) and A<T/s>^+ (need integral closure).

-- Once we have this, we see mid way through p75 that the definition of the presheaf
-- on V is proj lim of O_X(U) as U runs through rationals opens in V. This gets
-- the projective limit topology and then we have a presheaf (hopefully this is
-- straightforward) of complete topological rings (need proj lim of complete is complete)

-- We then need the valuations on the stalks (this is direct limit in cat of rings, forget
-- the topology). This will be fiddly but not impossible.

-- We then have an object in V^pre and I think then everything should follow.