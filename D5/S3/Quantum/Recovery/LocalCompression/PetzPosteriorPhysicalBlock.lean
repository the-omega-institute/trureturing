/- GID: D5/S3/Quantum/Recovery/LocalCompression/PetzPosteriorPhysicalBlock
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/PetzPosteriorPhysicalBlock
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound the ordinary Petz benchmark drift for one bin of diagonal reference blocks. -/

import D5.S3.Quantum.Recovery.LocalCompression.PetzPosteriorBenchmark
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability

/-! The Petz recovery block of a sum of references diagonal in a fixed common basis. -/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Recovery.LocalCompression.PetzPosteriorPhysicalBlock

open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (cfc_diagonal)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_smul_nonneg)
open D5.S3.Quantum.Recovery.LocalCompression.PetzPosteriorBenchmark
  (traceNorm_posteriorBenchmark_square_bin_le)

variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq κ]

/-- A nonempty group in a common coordinatewise square bin has Petz benchmark
drift at most its total Petz mass times `2 * √m / L ^ 2`. The reference
blocks are diagonal in the chosen basis and the positive middle factor
may have off-diagonal entries. -/
theorem traceNorm_petzPosteriorPhysicalBlock_square_bin_le
    (K : Matrix κ κ ℂ) (hK : K.PosSemidef) (hk : ∀ j, 0 < (K j j).re)
    (s : ι → κ → ℝ) (hs : ∀ i j, 0 ≤ s i j)
    (a : κ → ℕ) (L : ℕ) (hL : 0 < L) :
    let D : (κ → ℝ) → Matrix κ κ ℂ := fun v => diagonal (fun j => (v j : ℂ))
    let S : ι → Matrix κ κ ℂ := fun i => D (s i)
    let r : ι → ℝ := fun i => (Matrix.trace (S i * K)).re
    let y : ι → κ → ℝ := fun i j => Real.sqrt ((K j j).re * s i j / r i)
    let T : Matrix κ κ ℂ := ∑ i, S i
    (∀ i, 0 < r i) →
    (∀ j i, ((a j : ℝ) / L) ^ 2 ≤ y i j ∧
      y i j ≤ (((a j : ℝ) + 1) / L) ^ 2) →
    traceNorm (CFC.sqrt T * K * CFC.sqrt T -
      ∑ i, CFC.sqrt (S i) * K * CFC.sqrt (S i)) ≤
      (∑ i, r i) * (2 * Real.sqrt (Fintype.card κ : ℝ) / (L : ℝ) ^ 2) := by
  intro D S r y T hr hbin
  let k : κ → ℝ := fun j => (K j j).re
  let R : ℝ := ∑ i, r i
  let w : ι → ℝ := fun i => r i / R
  let d : κ → ℝ := fun j => (Real.sqrt (k j))⁻¹
  let C : Matrix κ κ ℂ := fun j l => K j l / (Real.sqrt (k j * k l) : ℂ)
  let u : κ → ℝ := fun j => Real.sqrt (∑ i, w i * (y i j) ^ 2)
  let t : κ → ℝ := fun j => ∑ i, s i j
  have hR : 0 < R := Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty
  have hKdiag (j : κ) : K j j = (k j : ℂ) :=
    Complex.ext (by simp [k]) (by
      simpa only [Complex.ofReal_im] using
        (Complex.nonneg_iff.mp (hK.diag_nonneg (i := j))).2.symm)
  have hr_coord (i : ι) : r i = ∑ j, k j * s i j := by
    have htrace : Matrix.trace (S i * K) = ((∑ j, k j * s i j : ℝ) : ℂ) := by
      simp only [S, D, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, hKdiag,
        ← Complex.ofReal_mul, Complex.ofReal_sum, mul_comm]
    simpa only [r, Complex.ofReal_re] using congrArg Complex.re htrace
  have hcongruence : C = D d * K * D d := by
    ext j l
    simp only [C, D, d, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Real.sqrt_mul (show 0 ≤ k j from (hk j).le), Complex.ofReal_mul,
      Complex.ofReal_inv, div_eq_mul_inv, mul_inv_rev]
    ring
  have hDadj : (D d)ᴴ = D d := by
    change (diagonal (fun j => (d j : ℂ)))ᴴ = _
    rw [Matrix.diagonal_conjTranspose]
    exact congrArg diagonal (funext fun j => by simp [Pi.star_apply])
  have hC : C.PosSemidef := by
    rw [hcongruence]
    simpa only [hDadj] using hK.mul_mul_conjTranspose_same (D d)
  have hdiag (j : κ) : C j j = 1 := by
    change K j j / (Real.sqrt (k j * k j) : ℂ) = 1
    rw [hKdiag j, Real.sqrt_mul_self (show 0 ≤ k j from (hk j).le)]
    exact div_self (Complex.ofReal_ne_zero.mpr (hk j).ne')
  have recovery (v : κ → ℝ) (hv : ∀ j, 0 ≤ v j) (p : ℝ) (hp : 0 < p) :
      let x : κ → ℝ := fun j => Real.sqrt (k j * v j / p)
      CFC.sqrt (D v) * K * CFC.sqrt (D v) = p • (D x * C * D x) := by
    intro x
    have hpositive : (D v).PosSemidef :=
      Matrix.PosSemidef.diagonal (fun j => Complex.zero_le_real.mpr (hv j))
    have hsqrt : CFC.sqrt (D v) = D (fun j => Real.sqrt (v j)) := by
      rw [CFC.sqrt_eq_real_sqrt _ hpositive.nonneg, cfcₙ_eq_cfc]
      exact cfc_diagonal Real.sqrt v
    have hcoord (j : κ) :
        (x j : ℂ) * (d j : ℂ) * (Real.sqrt p : ℂ) = (Real.sqrt (v j) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      apply congrArg Complex.ofReal
      have hkj : 0 < k j := hk j
      dsimp only [x, d]
      rw [Real.sqrt_div (mul_nonneg hkj.le (hv j)), Real.sqrt_mul hkj.le]
      calc
        _ = (Real.sqrt (k j) * Real.sqrt (v j)) * (Real.sqrt (k j))⁻¹ := by
          rw [mul_right_comm _ _ (Real.sqrt p), div_mul_cancel₀ _ (Real.sqrt_pos.mpr hp).ne']
        _ = _ := by
          rw [mul_right_comm, mul_inv_cancel₀ (Real.sqrt_pos.mpr hkj).ne', one_mul]
    have hp_sq : (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp.le]
    rw [hsqrt, hcongruence]
    ext j l
    simp only [D, Matrix.smul_apply, Complex.real_smul, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [← hcoord j, ← hcoord l, ← hp_sq]
    ring
  have hy_sq (i : ι) (j : κ) : (y i j) ^ 2 = k j * s i j / r i :=
    Real.sq_sqrt (div_nonneg (mul_nonneg (hk j).le (hs i j)) (hr i).le)
  have hy (i : ι) : ∑ j, (y i j) ^ 2 = 1 := by
    simp only [hy_sq, ← Finset.sum_div, ← hr_coord i, div_self (hr i).ne']
  have hw (i : ι) : 0 ≤ w i := div_nonneg (hr i).le hR.le
  have hw_sum : ∑ i, w i = 1 := by
    change (∑ i, r i / R) = 1
    rw [← Finset.sum_div, show ∑ i, r i = R from rfl, div_self hR.ne']
  have hblock (i : ι) : CFC.sqrt (S i) * K * CFC.sqrt (S i) =
      r i • (D (y i) * C * D (y i)) :=
    recovery (s i) (hs i) (r i) (hr i)
  have hu (j : κ) : u j = Real.sqrt (k j * t j / R) := by
    change Real.sqrt (∑ i, r i / R * (y i j) ^ 2) = Real.sqrt (k j * t j / R)
    apply congrArg Real.sqrt
    simp only [hy_sq]
    calc
      _ = ∑ i, k j * s i j / R := by
        refine Finset.sum_congr rfl fun i _ => ?_
        calc
          _ = (k j * s i j / r i) * r i / R := by ring
          _ = _ := by rw [div_mul_cancel₀ _ (hr i).ne']
      _ = _ := by simp only [t, ← Finset.sum_div, Finset.mul_sum]
  have hT : T = D t := by
    change (∑ i, D (s i)) = D t
    ext j l
    by_cases hjl : j = l
    · subst l
      simp only [D, t, Matrix.sum_apply, Matrix.diagonal_apply_eq, Complex.ofReal_sum]
    · simp [D, Matrix.sum_apply, Matrix.diagonal_apply, hjl]
  have hmerged : CFC.sqrt T * K * CFC.sqrt T = R • (D u * C * D u) := by
    rw [hT, show u = (fun j => Real.sqrt (k j * t j / R)) from funext hu]
    exact recovery t (fun j => Finset.sum_nonneg fun i _ => hs i j) R hR
  have hsum : (∑ i, CFC.sqrt (S i) * K * CFC.sqrt (S i)) =
      R • ∑ i, w i • (D (y i) * C * D (y i)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hw_scale : R * w i = r i := by
      change R * (r i / R) = r i
      rw [mul_comm R, div_mul_cancel₀ _ hR.ne']
    rw [hblock i, smul_smul, hw_scale]
  rw [hmerged, hsum, ← smul_sub]
  change traceNorm ((R : ℂ) •
    (D u * C * D u - ∑ i, w i • (D (y i) * C * D (y i)))) ≤ _
  rw [traceNorm_smul_nonneg _ R hR.le]
  exact mul_le_mul_of_nonneg_left
    (traceNorm_posteriorBenchmark_square_bin_le C hC hdiag w y hw hw_sum hy a L hL hbin)
    hR.le

end D5.S3.Quantum.Recovery.LocalCompression.PetzPosteriorPhysicalBlock
