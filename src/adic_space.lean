import for_mathlib.prime
import for_mathlib.ideals
import for_mathlib.is_cover 
import analysis.topology.topological_structures
import data.nat.prime 
import algebra.group_power
import for_mathlib.presheaves
import for_mathlib.topology
import for_mathlib.subring
import linear_algebra.basic

open nat function

variables {R : Type} [comm_ring R] [topological_space R] [topological_ring R]  

-- Schol= : "Recall that a topological ring R is Tate if it contains an
-- open and bounded subring R0 ⊂ R and a topologically nilpotent unit pi ∈ R; such elements are
-- called pseudo-uniformizers.""
-- we need definitions of bounded subsets and topologically nilpotent -- and do we have unit? Probably.
class Tate_ring (R : Type) extends comm_ring R, topological_space R, topological_ring R :=
(unfinished : sorry)

def adic_topology {R : Type} [comm_ring R] (I : set R) [is_ideal I] : topological_space R :=
begin
  have adic_nhd_of_zero : ℕ → (set R) := λn, span {i | ∃ x : multiset I, x.card = n ∧ i = (x.map subtype.val).prod},
  have adic_nhd_of : R → set (set R) := λr, (set.range (λn : ℕ, {r' | ((r' : R) - r) ∈ adic_nhd_of_zero n})),
  have adic_nhds := ⋃₀ (set.range adic_nhd_of),
  exact topological_space.generate_from adic_nhds
end

def is_pair_of_definition [T : topological_space R] (R₀ : set R) [is_subring R₀] (I : set R₀) [is_ideal I]: Prop :=
topological_space.induced (@subtype.val _ (R₀ : set R)) T = adic_topology I

def is_ring_of_definition (R₀ : set R) [is_subring R₀] :=
∃ (I : set R₀) [hI : is_ideal I], @is_pair_of_definition _ _ _ _ _ R₀ _ I hI

-- f-adic rings are called Huber rings by Scholze.
-- Topological ring A contains on open subring A0 such that the subspace topology on A0 is
-- I-adic, where I is a finitely generated ideal of A0 .
class Huber_ring (R : Type) extends comm_ring R, topological_space R, topological_ring R :=
(exists_ring_of_definition : ∃ (R₀ : set R) [is_subring R₀], is_ring_of_definition R₀)

-- TODO should have an instance going from Tate to Huber

-- peredicates we need for topological rings
definition is_complete (R : Type) [topological_space R] [comm_ring R] [topological_ring R] : Prop := sorry 
definition is_uniform (R : Type) : Prop := sorry 
definition is_bounded {R : Type} [topological_space R] [comm_ring R] [topological_ring R] 
  (U : set R) : Prop := sorry
definition is_power_bounded {R : Type} (r : R) : Prop := sorry 
definition power_bounded_subring (R : Type) := {r : R // is_power_bounded r}
-- instance subring_to_ring (R : Type) : has_coe (power_bounded_subring R) R := ⟨subtype.val⟩ 
instance power_bounded_subring_is_ring (R : Type) : comm_ring (power_bounded_subring R) := sorry
theorem p_is_power_bounded (R : Type) [p : Prime] : is_power_bounded (p : power_bounded_subring R) := sorry
definition is_pseudo_uniformizer {R : Type} : R → Prop := sorry 


-- Wedhorn Def 7.14
structure is_ring_of_integral_elements {R : Type} [Huber_ring R] (Rplus : set R) : Prop :=
[is_subring : is_subring Rplus]
(is_open : is_open Rplus)
(is_int_closed : is_integrally_closed Rplus)
(is_power_bounded : Rplus ⊆ { r : R | is_power_bounded r})

-- a Huber Ring is an f-adic ring.
-- a Huber Pair is what Huber called an Affinoid Ring.
structure Huber_pair :=
(R : Type) 
[RHuber : Huber_ring R]
(Rplus : set R)
[intel : is_ring_of_integral_elements Rplus]

instance : has_coe_to_sort Huber_pair := 
{ S := Type, coe := Huber_pair.R}

postfix `⁺` : 66 := λ R : Huber_pair _, R.Rplus  

definition Spa (A : Huber_pair) : Type := sorry
instance Spa_topology (A : Huber_pair) : topological_space (Spa A) := sorry 

--definition 𝓞_X (A : Huber_pair) : presheaf_of_rings (Spa A) := sorry 
-- it's a presheaf of complete topological rings on all opens (defined on rational opens
-- first and then extended to all via proj limits) -- Huber p75
-- most of that would not be in the adic_space file.

--structure 𝓥pre :=
--(X : sorry)
--(𝓞X : sorry)
--(v : sorry)

/-
We denote by 𝓥pre the category of tuples X = (X, O X , (v x ) x∈X ), where
(a) X is a topological space,
(b) 𝓞_X is a presheaf of complete topological rings on X such that the stalk 𝓞_X,x of
𝓞_X (considered as a presheaf of rings) is a local ring,
(c) v_x is an equivalence class of valuations on the stalk 𝓞_X,x such that supp(v_x) is the
maximal ideal of 𝓞_X,x .

Wedhorn p76 shows how Spa(A) gives an object of this for A a Huber pair
-/

--definition affinoid_adic_space (A : Huber_pair) : 𝓥pre := sorry

-- unwritten -- it's a full subcat of 𝓥pre
class preadic_space (X : Type) extends topological_space X 

-- not logically necessary but should be easy
instance (A : Huber_pair) : preadic_space (Spa A) := sorry 

-- attribute [class] _root_.is_open 

instance preadic_space_restriction {X : Type} [preadic_space X] {U : opens X} :
  preadic_space U := sorry

-- unwritten 
class adic_space (X : Type) extends preadic_space X

-- a preadic_space_equiv is just an isom in 𝓥pre, or an isomorphism of preadic spaces.
-- is homeo in Lean yet?
-- unwritten
structure preadic_space_equiv (X Y : Type) [AX : preadic_space X] [AY : preadic_space Y] extends equiv X Y

definition is_preadic_space_equiv (X Y : Type) [AX : preadic_space X] [AY : preadic_space Y] := 
  nonempty (preadic_space_equiv X Y)

definition preadic_space_pullback {X : Type} [preadic_space X] (U : set X) := {x : X // x ∈ U}

instance pullback_is_preadic_space {X : Type} [preadic_space X] (U : set X) : preadic_space (preadic_space_pullback U) := sorry 

-- notation `is_open` := _root_.is_open
