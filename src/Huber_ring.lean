import analysis.topology.topological_structures
import for_mathlib.ideals
import ring_theory.subring
-- f-adic rings are called Huber rings by Scholze.
-- Topological ring A contains on open subring A0 such that the subspace topology on A0 is
-- I-adic, where I is a finitely generated ideal of A0 .

instance subring_has_zero (R : Type*) [comm_ring R] (S : set R) [HS : is_subring S] : has_zero S :=
⟨⟨0, is_add_submonoid.zero_mem S⟩⟩

class Huber_ring (R : Type*) extends comm_ring R, topological_space R, topological_ring R :=
(S : set R) [HS : is_subring S]
(J : set S) [HJ : is_ideal J]
(HJ_fin : ∃ gen : set S, set.finite gen ∧ span gen = J)
(H1 : ∀ n, @topological_space.is_open S
  (topological_space.induced subtype.val to_topological_space) (pow_ideal J n))
(H2 : ∀ K : set S, (0 : S) ∈ K
   → @topological_space.is_open S (topological_space.induced subtype.val to_topological_space) K
  → ∃ n, pow_ideal J n ⊆ K)

