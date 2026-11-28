/- GID: D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/GangulyCircuitAccess/Encoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two distinct logical pure states have the same circuit-authorized reduction. -/

import D5.S3.Quantum.Information.GangulyCircuitAccess.Combinatorial
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The normalized computational-basis slices of the graph state give an encoding on
the players. Its off-diagonal reduced entries are controlled by integer sign sums. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.GangulyCircuitAccess

open scoped BigOperators Matrix

/-- The dealer slices of the graph-state amplitude, with the discarded players
indexed by the first factor and the retained players by the second. -/
noncomputable def dealerSlices {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (d : Fin n) (A : Finset (Fin n)) : Matrix (Config (discarded d A) × Config A) (Fin 2) ℂ :=
  fun p s => (signedGraphEntry (G.adjMatrix (ZMod 2)) (fullConfig d A p s) : ℂ) /
    ((Real.sqrt (2 ^ (n - 1)) : ℝ) : ℂ)

/-- Encode the logical matrix and trace out the discarded players. The entry
at `a,b` is the trace of the block with retained row `a` and column `b`. -/
noncomputable def reducedEncoding {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (d : Fin n) (A : Finset (Fin n)) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Config A) (Config A) ℂ := fun a b =>
  let V := dealerSlices G d A
  ((V * ρ * Vᴴ).submatrix
    (fun (c : Config (discarded d A)) => (c, a)) (fun c => (c, b))).trace

private abbrev WitnessRow := Config (discarded witnessDealer witnessPlayers) × Config witnessPlayers

private abbrev witnessSign (p : WitnessRow) (s : Fin 2) : ℤ :=
  signedGraphEntry witnessMatrix (fullConfig witnessDealer witnessPlayers p s)

private noncomputable abbrev witnessEncoding :=
  dealerSlices witnessGraph witnessDealer witnessPlayers

private theorem witnessEncoding_apply (p : WitnessRow) (s : Fin 2) :
    witnessEncoding p s = (witnessSign p s : ℂ) * (8 : ℂ)⁻¹ := by
  have h : Real.sqrt (2 ^ (7 - 1 : ℕ) : ℝ) = 8 := by
    convert Real.sqrt_mul_self (show (0 : ℝ) ≤ 8 by norm_num) using 1 <;> norm_num
  change (witnessSign p s : ℂ) / ((Real.sqrt (2 ^ (7 - 1 : ℕ)) : ℝ) : ℂ) = _
  rw [h, Complex.ofReal_ofNat, div_eq_mul_inv]

private theorem witness_product_sum {ι : Type*} [Fintype ι]
    (p q : ι → WitnessRow) (s t : Fin 2) :
    (∑ i, witnessEncoding (p i) s * star (witnessEncoding (q i) t)) =
      (∑ i, witnessSign (p i) s * witnessSign (q i) t : ℤ) * ((8 : ℂ)⁻¹ * (8 : ℂ)⁻¹) := by
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [witnessEncoding_apply, Complex.star_def, map_mul, map_inv₀, map_ofNat,
    map_intCast]
  ring

/-- The normalized encoding columns are orthonormal. -/
theorem witness_encoding_isometry :
    (dealerSlices witnessGraph witnessDealer witnessPlayers)ᴴ *
      dealerSlices witnessGraph witnessDealer witnessPlayers = 1 := by
  ext s t
  change (∑ i : WitnessRow, star (witnessEncoding i s) * witnessEncoding i t) = _
  rw [show (∑ i : WitnessRow, star (witnessEncoding i s) * witnessEncoding i t) =
      ∑ i : WitnessRow, witnessEncoding i t * star (witnessEncoding i s) from
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)]
  rw [witness_product_sum id id t s, witness_signed_gram]
  by_cases h : s = t
  · subst t
    norm_num [Matrix.one_apply]
  · simp [Matrix.one_apply, h, Ne.symm h]

private theorem witness_cross_zero (a b : Config witnessPlayers) :
    (∑ c : Config (discarded witnessDealer witnessPlayers),
      witnessEncoding (c, a) 0 * star (witnessEncoding (c, b) 1)) = 0 := by
  rw [witness_product_sum (fun c => (c, a)) (fun c => (c, b)) 0 1,
    witness_signed_cross_zero]
  simp

private theorem witness_reverse_cross_zero (a b : Config witnessPlayers) :
    (∑ c : Config (discarded witnessDealer witnessPlayers),
      witnessEncoding (c, a) 1 * star (witnessEncoding (c, b) 0)) = 0 := by
  rw [witness_product_sum (fun c => (c, a)) (fun c => (c, b)) 1 0]
  have h : (∑ c : Config (discarded witnessDealer witnessPlayers),
      witnessSign (c, a) 1 * witnessSign (c, b) 0) = 0 := by
    calc
      _ = ∑ c : Config (discarded witnessDealer witnessPlayers),
          witnessSign (c, b) 0 * witnessSign (c, a) 1 :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      _ = 0 := witness_signed_cross_zero b a
  rw [h]
  simp

/-- The projectors onto the logical `X` eigenstates are obtained at signs `1` and `-1`. -/
noncomputable def logicalDensity (sign : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then 1 / 2 else sign / 2

private noncomputable def logicalVector (negative : Bool) (i : Fin 2) : ℂ :=
  (if negative && decide (i = 1) then -1 else 1) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

private theorem logical_outer (negative : Bool) :
    Matrix.vecMulVec (logicalVector negative) (star (logicalVector negative)) =
      logicalDensity (if negative then -1 else 1) := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hInv : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv_rev, h, one_div]
  have hStar : star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [Complex.star_def, map_inv₀, Complex.conj_ofReal]
  ext i j
  cases negative <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.vecMulVec_apply, logicalVector, logicalDensity, Pi.star_apply,
      hStar, hInv, neg_mul, mul_neg]

/-- Both logical inputs are outer products of unit vectors. -/
theorem logical_x_pure (negative : Bool) :
    ∃ v : Fin 2 → ℂ, (∑ i, v i * star (v i)) = 1 ∧
      logicalDensity (if negative then -1 else 1) = Matrix.vecMulVec v (star v) := by
  refine ⟨logicalVector negative, ?_, (logical_outer negative).symm⟩
  rw [← Matrix.trace_vecMulVec, logical_outer]
  norm_num [Matrix.trace, Matrix.diag_apply, logicalDensity, Fin.sum_univ_two]

theorem logical_x_distinct : logicalDensity 1 ≠ logicalDensity (-1) := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  norm_num [logicalDensity] at h01

private theorem encoded_difference (p q : WitnessRow) :
    (witnessEncoding * logicalDensity 1 * witnessEncodingᴴ) p q -
      (witnessEncoding * logicalDensity (-1) * witnessEncodingᴴ) p q =
      witnessEncoding p 0 * star (witnessEncoding q 1) +
        witnessEncoding p 1 * star (witnessEncoding q 0) := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, logicalDensity] <;> ring

/-- The two logical `X` eigenstates give equal reduced density matrices on `{2,5,6}`. -/
theorem witness_reduced_density_eq :
    reducedEncoding witnessGraph witnessDealer witnessPlayers (logicalDensity 1) =
      reducedEncoding witnessGraph witnessDealer witnessPlayers (logicalDensity (-1)) := by
  ext a b
  apply sub_eq_zero.mp
  simp only [reducedEncoding, Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  rw [← Finset.sum_sub_distrib]
  simp_rw [encoded_difference]
  rw [Finset.sum_add_distrib, witness_cross_zero, witness_reverse_cross_zero, add_zero]

#print axioms witness_encoding_isometry
#print axioms logical_x_pure
#print axioms logical_x_distinct
#print axioms witness_reduced_density_eq

end D5.S3.Quantum.Information.GangulyCircuitAccess
