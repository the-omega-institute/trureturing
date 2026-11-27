/- GID: D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubspaceCodes/FerrersPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The root bound for a four-term linearized polynomial gives rank at least nine. -/

import Mathlib.Algebra.Polynomial.Basis
import Mathlib.FieldTheory.Finite.Basic

/-! # Rank of four-term linearized polynomials -/

namespace D5.S3.Combinatorics.SubspaceCodes.FerrersPolynomial

open Polynomial

section

variable (F E : Type*) [Field F] [Fintype F] [Field E] [Algebra F E]

private noncomputable def sigmaPower (i : Fin 4) : E →ₗ[F] E :=
  ((FiniteField.frobeniusAlgHom F E) ^ i.val).toLinearMap

private theorem sigmaPower_apply (i : Fin 4) (x : E) :
    sigmaPower F E i x = x ^ Fintype.card F ^ i.val := by
  change (FiniteField.frobeniusAlgHom F E ^ i.val) x = _
  simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]

/-- Evaluation as a linear combination of Frobenius powers.

Used by
- `FerrersCoefficients.evaluation_on_K`
- `FerrersCoefficients.evaluation_on_bK`
- `FerrersRankNine.evaluationMap`
- `FerrersRankNine.codeMap_rank`
- `FerrersRankNine.codeMap_supported` -/
noncomputable def evaluateLinearized (a : Fin 4 → E) : E →ₗ[F] E :=
  ∑ i, a i • sigmaPower F E i

/-- The scalar formula for evaluation of the linear map.

Used by
- `FerrersCoefficients.evaluation_on_K`
- `FerrersCoefficients.evaluation_on_bK`
- `FerrersRankNine.evaluationMap` through its additivity and scalar multiplication proofs
- `FerrersPolynomial.eval_linearizedPolynomial_eq` -/
theorem evaluateLinearized_apply (a : Fin 4 → E) (x : E) :
    evaluateLinearized F E a x = ∑ i : Fin 4, a i * x ^ Fintype.card F ^ i.val := by
  simp [evaluateLinearized, LinearMap.sum_apply, sigmaPower_apply]

private noncomputable def linearizedPolynomial (a : Fin 4 → E) : E[X] :=
  ∑ i : Fin 4, monomial (Fintype.card F ^ i.val) (a i)

private theorem eval_linearizedPolynomial_eq (a : Fin 4 → E) (x : E) :
    (linearizedPolynomial F E a).eval x = evaluateLinearized F E a x := by
  rw [evaluateLinearized_apply]
  simp [linearizedPolynomial, Polynomial.eval_finsetSum]

omit [Algebra F E] in
private theorem linearizedPolynomial_ne_zero (a : Fin 4 → E) (ha : a ≠ 0) :
    linearizedPolynomial F E a ≠ 0 := by
  intro hp
  apply ha
  have hli := (Polynomial.basisMonomials E).linearIndependent.comp
    (fun i : Fin 4 => Fintype.card F ^ i.val)
    (fun _ _ h => Fin.ext (Nat.pow_right_injective Fintype.one_lt_card h))
  have hcoeff := (Fintype.linearIndependent_iff.mp hli) a (by
    simpa only [linearizedPolynomial, Function.comp_apply, Polynomial.coe_basisMonomials,
      Polynomial.smul_monomial, smul_eq_mul, mul_one] using hp)
  exact funext hcoeff

omit [Algebra F E] in
private theorem natDegree_linearizedPolynomial_le (a : Fin 4 → E) :
    (linearizedPolynomial F E a).natDegree ≤ Fintype.card F ^ 3 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_monomial_le _).trans (Nat.pow_le_pow_right Fintype.card_pos (by omega))

private theorem finrank_ker_evaluateLinearized_le_three [Finite E]
    (a : Fin 4 → E) (ha : a ≠ 0) :
    Module.finrank F (LinearMap.ker (evaluateLinearized F E a)) ≤ 3 := by
  classical
  let p := linearizedPolynomial F E a
  let ker := LinearMap.ker (evaluateLinearized F E a)
  let : Fintype ker := Fintype.ofFinite ker
  let s : Finset E := Finset.univ.map ⟨ker.subtype, Subtype.val_injective⟩
  have hs : s.val ⊆ p.roots := by
    intro x hx
    rcases Finset.mem_map.mp (Finset.mem_def.mpr hx) with ⟨y, _, rfl⟩
    exact (p.mem_roots (linearizedPolynomial_ne_zero F E a ha)).mpr
      (by rw [Polynomial.IsRoot.def, eval_linearizedPolynomial_eq]; exact y.property)
  have hle := (Polynomial.card_le_degree_of_subset_roots hs).trans
    (natDegree_linearizedPolynomial_le F E a)
  have hc : s.card = Fintype.card F ^ Module.finrank F ker := by
    change (Finset.univ.map (⟨ker.subtype, Subtype.val_injective⟩ : ker ↪ E)).card = _
    rw [Finset.card_map, Finset.card_univ, Module.card_eq_pow_finrank (K := F) (V := ker)]
  rw [hc] at hle
  exact (Nat.pow_le_pow_iff_right Fintype.one_lt_card).mp hle

/-- Nonzero coefficient tuples give rank at least nine in degree twelve.

Used by
- `FerrersRankNine.codeMap_injective`
- `FerrersRankNine.exists_supported_dim27_with_rank` -/
theorem finrank_range_evaluateLinearized_ge_nine [Finite E]
    (hE : Module.finrank F E = 12) (a : Fin 4 → E) (ha : a ≠ 0) :
    9 ≤ Module.finrank F (LinearMap.range (evaluateLinearized F E a)) := by
  have h₁ := finrank_ker_evaluateLinearized_le_three F E a ha
  have h₂ := LinearMap.finrank_range_add_finrank_ker (evaluateLinearized F E a)
  omega

end

end D5.S3.Combinatorics.SubspaceCodes.FerrersPolynomial
