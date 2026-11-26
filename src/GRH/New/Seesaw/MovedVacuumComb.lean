import GRH.New.Seesaw.AdmissibleComb
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

This file: A moved translate of the vacuum is an admissible average of vacuum translates. -/

open Matrix Complex AddSubgroup Finset

/-- Let g be finite, cC = Δ_f(g), and g(x + Ô^n) ⊂ A. If dc/|Δ_f(g)|² is integral away from q
and, under p, all |σc| ≤ 1, then ω(g)ϱ_f(x)vac is an admissible combination of the
Cϱ_f(z)vac, z ∈ A, of denominator d and size 1. -/
lemma isAdmissibleComb_weil_vacElem {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n]
  {s} (V : Space E n s) {q g x A p d C c} (e : c * C = finMultiplier g) (I : ∀ y ∈ stdLattice E n,
  g *ᵥ (x + y) ∈ A) (hc : (d : ℕ) * (c / ‖finMultiplier g‖ ^ 2) ∈ integralAway q) (hp : p →
  ∀ σ : ℂ ≃+* ℂ, ‖σ c‖ ≤ 1) : IsAdmissibleComb (C • V.finHeisOp
  · V.vacElem) A q d p 1 (V.ω (1, g) (V.finHeisOp x V.vacElem)) := by
  have := fintypeOfIndexNeZero
    (mod_cast norm_finMultiplier_sq g ▸ pow_ne_zero 2 (by simp [finMultiplier_ne_zero]))
  simp [V.omega_vacElem_sum, e ▸ mul_div_right_comm .., mul_smul, smul_sum, V.finHeisOp_finHeisOp,
    ← mulVec_add]
  refine .of_eq_isOfFinOrder_smul (.of_sum ?_ ?_) fun y _ ↦ ⟨_, isOfFinOrder_ψf _, _, I _ y.out.2,
    smul_comm ..⟩ <;> simp_all [relIndex, index, ← ofReal_pow, norm_finMultiplier_sq, field]
