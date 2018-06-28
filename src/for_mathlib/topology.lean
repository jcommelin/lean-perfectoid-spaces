import analysis.topology.topological_space
import analysis.topology.uniform_space

variable (X : Type*)

section opens
variable [topological_space X]
include X

@[class] def opens := {U : set X // is_open U}

instance : has_coe (opens X) (set X) := ⟨λU, U.1⟩

instance : has_mem X (opens X) := ⟨λx U, x ∈ U.1⟩

instance : has_inter (opens X) := ⟨λ U V, ⟨U.1 ∩ V.1, is_open_inter U.2 V.2⟩⟩

instance : has_union (opens X) := ⟨λ U V, ⟨U.1 ∪ V.1, is_open_union U.2 V.2⟩⟩

instance : has_emptyc (opens X) := ⟨⟨∅, is_open_empty⟩⟩
end opens

-- Predicates that we need for topological rings

-- We need to think whether we could directly use the class t2_space (which is not using opens though)
definition is_hausdorff [topological_space X] : Prop :=
  ∀ x y, x ≠ y → ∃ u v : opens X, x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅

-- Wedhorn Definition 5.31 page 38
definition is_complete [uniform_space X] :=
  is_hausdorff X ∧ ∀ {f : filter X}, cauchy f → ∃ x, f ≤ nhds x