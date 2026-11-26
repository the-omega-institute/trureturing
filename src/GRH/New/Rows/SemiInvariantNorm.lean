import GRH.Lib.Adelic.CuspForms.DeltaForms
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Twisted theta forms lie on one line (see New.Rows.LineArithmetic).

This file: for products of polynomials, weights add and norm bounds multiply. -/

variable {Φ n : Type} [Fintype Φ] [Fintype n]

/-- F is the polynomial of some coordinate vector ξ of weight κ, and, if p holds, ξ has squared
norm at most b. -/
def HasWeightNormLe (p : Prop) κ F b := ∃ ξ, toPoly (Φ := Φ) n κ ξ = F ∧ (p → weylNormSq ξ ≤ b)

lemma HasWeightNormLe.prod {p ι} {s : Finset ι} {κ F b} :
  (∀ i ∈ s, @HasWeightNormLe Φ n _ _ p (κ i) (F i) (b i)) →
  HasWeightNormLe p (s.sum κ) (s.prod F) (s.prod b) := s.induction_on (by simpa using ⟨weylEval _
  _ 0, by simp [weylKernel, highestPoly, tableauPoly, weylNormSq, PolyRep.star_weylEval]⟩) <| by
  simp_intro _ _ _ i; apply_rw [i]
  exact fun ⟨_, e⟩ ⟨_, f⟩ ↦ e.1 ▸ f.1 ▸ (range_toPoly.ge (by simp [SetLike.mul_mem_graded,
    diagramWeight_add, nablaFam, ← range_toPoly])).imp fun _ z ↦
    ⟨z, by grind [(weylNormSq_le_mul_of_toPoly_eq z).trans, weylNormSq_nonneg, mul_le_mul]⟩
