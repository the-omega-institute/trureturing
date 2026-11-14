/- GID: D5/S3/Quantum/Matrix/CentralSqrtTwoDefectGap
   generality: I
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantitative rank-one sector separation and simple spectrum for the central sqrt-two defect family. -/

import D5.S3.Weil.ZetaLinear.Inertia
import D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum
import D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-! Endpoint observability and rank-one separation for finite Jacobi recurrences. -/

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

noncomputable section

open Finset Matrix
open scoped BigOperators

namespace D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap

/-! The scalar estimate used by the defect calculation.  The endpoint control is
the output of the recurrence argument; the theorem below is the rank-one
bridge which turns it into an inverse-cubic spectral separation. -/

theorem rank_one_gap_from_identity {c K lam mu x y z : ℝ}
    (hc : 0 < c) (hK : 0 < K)
    (hidentity : (lam - mu) * z = c * x * y)
    (hx : 1 ≤ K * x ^ 2) (hy : 1 ≤ K * y ^ 2)
    (hz : |z| ≤ 1) :
    c / K ≤ |lam - mu| := by
  have hxy : 1 ≤ K ^ 2 * (x * y) ^ 2 := by
    have hmul := mul_le_mul hx hy (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : 0 ≤ K * x ^ 2)
    nlinarith
  have habs := congrArg abs hidentity
  rw [abs_mul, abs_mul] at habs
  have hxyabs : 1 ≤ K * |x * y| := by
    have hKabs : 0 ≤ K * |x * y| := mul_nonneg hK.le (abs_nonneg _)
    have hsquare : 1 ≤ (K * |x * y|) ^ 2 := by
      simpa [sq_abs, mul_pow] using hxy
    nlinarith [sq_nonneg (K * |x * y| - 1)]
  have hupper : c * |x * y| ≤ |lam - mu| := by
    have hcx : |c * x| * |y| = c * |x * y| := by
      rw [abs_mul, abs_mul, abs_of_pos hc]
      ring
    calc
      c * |x * y| = |lam - mu| * |z| := by rw [habs, hcx]
      _ ≤ |lam - mu| := mul_le_of_le_one_right (abs_nonneg _) hz
  have hscale : c ≤ K * (c * |x * y|) := by
    have := mul_le_mul_of_nonneg_left hxyabs hc.le
    nlinarith
  have hfinal : c ≤ K * |lam - mu| := by
    exact hscale.trans (mul_le_mul_of_nonneg_left hupper hK.le)
  exact (div_le_iff₀ hK).2 (by simpa [mul_comm] using hfinal)

theorem rank_one_cross_identity {d : Type*} [Fintype d] [DecidableEq d]
    {A B : Matrix d d ℝ} {q : d} {c : ℝ}
    (hA : A.IsSymm)
    (hupdate : B = A + c • Matrix.vecMulVec (Pi.single q 1) (Pi.single q 1))
    (u v : d → ℝ) (lam mu : ℝ)
    (hu : A *ᵥ u = lam • u) (hv : B *ᵥ v = mu • v) :
    (mu - lam) * (u ⬝ᵥ v) = c * (u q) * (v q) := by
  have hs : (A *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (A *ᵥ v) := by
    rw [dotProduct_comm]
    exact hA.dotProduct_mulVec_comm
  have hcore : (lam - mu) * (u ⬝ᵥ v) = -c * (u q) * (v q) := by
    calc
    (lam - mu) * (u ⬝ᵥ v) = (A *ᵥ u) ⬝ᵥ v - u ⬝ᵥ (B *ᵥ v) := by
      rw [hu, hv, smul_dotProduct, dotProduct_smul]
      ring
    _ = u ⬝ᵥ (A *ᵥ v) - u ⬝ᵥ (B *ᵥ v) := by rw [hs]
    _ = u ⬝ᵥ ((A - B) *ᵥ v) := by rw [sub_mulVec, dotProduct_sub]
    _ = -c * (u q) * (v q) := by
      have hab : A - B = -(c • Matrix.vecMulVec (Pi.single q 1) (Pi.single q 1)) := by
        rw [hupdate]
        ext i j
        simp
      rw [hab, neg_mulVec, smul_mulVec, dotProduct_neg, dotProduct_smul]
      simp [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Pi.single_apply]
      ring
  calc
    (mu - lam) * (u ⬝ᵥ v) = -((lam - mu) * (u ⬝ᵥ v)) := by ring
    _ = -(-c * (u q) * (v q)) := by rw [hcore]
    _ = c * (u q) * (v q) := by ring

theorem rank_one_gap_of_matrices {d : Type*} [Fintype d] [DecidableEq d]
    {A B : Matrix d d ℝ} {q : d} {c K : ℝ}
    (hc : 0 < c) (hK : 0 < K) (hA : A.IsSymm)
    (hupdate : B = A + c • Matrix.vecMulVec (Pi.single q 1) (Pi.single q 1))
    (u v : d → ℝ) (lam mu : ℝ)
    (hu : A *ᵥ u = lam • u) (hv : B *ᵥ v = mu • v)
    (hx : 1 ≤ K * (u q) ^ 2) (hy : 1 ≤ K * (v q) ^ 2)
    (hz : |u ⬝ᵥ v| ≤ 1) :
    c / K ≤ |lam - mu| := by
  have h := rank_one_gap_from_identity hc hK
    (rank_one_cross_identity hA hupdate u v lam mu hu hv) hx hy hz
  simpa [abs_sub_comm] using h

def centralEdges (n : ℕ) (_hn : 1 ≤ n) : Fin (2 * n - 1 + 1) → ℝ :=
  fun i => if i.val = n - 1 then Real.sqrt 2 else 1

def centralDefect (n : ℕ) (hn : 1 ≤ n) :
    Matrix (Fin (2 * n - 1 + 1)) (Fin (2 * n - 1 + 1)) ℝ :=
  D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix
    (2 * n - 1) 0 (centralEdges n hn)

private theorem chebyshev_u_band_bound (k : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    |(Polynomial.Chebyshev.U ℝ (k : ℤ)).eval x| ≤ k + 1 := by
  have ht (j : ℤ) := Polynomial.Chebyshev.abs_eval_T_real_le_one j hx
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, Polynomial.Chebyshev.U_eq_X_mul_U_add_T]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    calc
      |x * (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval x +
          (Polynomial.Chebyshev.T ℝ ((k : ℤ) + 1)).eval x| ≤
          |x| * |(Polynomial.Chebyshev.U ℝ (k : ℤ)).eval x| + 1 := by
        exact (abs_add_le _ _).trans (by rw [abs_mul]; exact add_le_add_right (ht _) _)
      _ ≤ (k : ℝ) + 1 + 1 := by
        have hh := mul_le_mul hx ih (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        simpa using hh
      _ = _ := by push_cast; ring

private theorem chebyshev_s_band_bound (k : ℕ) (t : ℝ) (ht : |t| ≤ 2) :
    |(Polynomial.Chebyshev.S ℝ (k : ℤ)).eval t| ≤ k + 1 := by
  rw [Polynomial.Chebyshev.S_eq_U_comp_half_mul_X]
  simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, invOf_eq_inv]
  have he : (2 : ℝ)⁻¹ * t = t / 2 := by ring
  rw [he]
  exact chebyshev_u_band_bound k (t / 2) (by rw [abs_div]; norm_num; linarith)

/-- A finite free Jacobi recurrence with a Robin endpoint has a uniform cubic
endpoint observability bound, including both exterior regimes. -/
theorem recurrence_endpoint_observability (n : ℕ) (hn : 1 ≤ n)
    (t b : ℝ) (y : ℕ → ℝ) (hzero : y 0 = 0)
    (hrec : ∀ j, j + 2 ≤ n + 1 → y (j + 2) = t * y (j + 1) - y j)
    (hboundary : y (n + 1) = b * y n) :
    (∑ j ∈ Finset.range n, y (j + 1) ^ 2) ≤
      (1 + |b|) ^ 2 * (n : ℝ) ^ 3 * y n ^ 2 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpoint : ∀ j, 1 ≤ j → j ≤ n → |y j| ≤ (1 + |b|) * n * |y n| := by
    by_cases ht : |t| ≤ 2
    · let z : ℕ → ℝ := fun k => y (n + 1 - k)
      have hzrec : ∀ k, k + 2 ≤ n → z (k + 2) = t * z (k + 1) - z k := by
        intro k hk
        have hr := hrec (n - 1 - k) (by omega)
        have h0 : n - 1 - k + 2 = n + 1 - k := by omega
        have h1 : n - 1 - k + 1 = n + 1 - (k + 1) := by omega
        have h2 : n - 1 - k = n + 1 - (k + 2) := by omega
        dsimp [z]
        rw [h0, h1, h2] at hr
        linarith
      intro j hj hjn
      let k := n + 1 - j
      have hk : 1 ≤ k := by dsimp [k]; omega
      have hkn : k ≤ n := by dsimp [k]; omega
      have hz := D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence.bounded_continuant_endpoint
        k hk t z (fun l hl => hzrec l (hl.trans hkn))
      have hz0 : z 0 = b * y n := by simpa [z] using hboundary
      have hz1 : z 1 = y n := by simp [z]
      have hzk : z k = y j := by dsimp [z, k]; congr 1; omega
      rw [hz0, hz1, hzk] at hz
      have hfirst : |(Polynomial.Chebyshev.S ℝ ((k : ℤ) - 1)).eval t| ≤ k := by
        have hb := chebyshev_s_band_bound (k - 1) t ht
        convert hb using 1 <;> push_cast [Nat.cast_sub hk] <;> ring
      have hsecond : |(Polynomial.Chebyshev.S ℝ ((k : ℤ) - 2)).eval t| ≤ k := by
        by_cases hk1 : k = 1
        · rw [hk1]; norm_num
        · have htwo : 2 ≤ k := by omega
          have hb := chebyshev_s_band_bound (k - 2) t ht
          have heq : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by omega
          rw [heq] at hb
          exact hb.trans (by push_cast [Nat.cast_sub htwo]; linarith)
      rw [hz]
      calc
        |_ - _| ≤ |(Polynomial.Chebyshev.S ℝ ((k : ℤ) - 1)).eval t| * |y n| +
            |(Polynomial.Chebyshev.S ℝ ((k : ℤ) - 2)).eval t| * (|b| * |y n|) := by
          simpa [abs_mul] using abs_sub_le
            ((Polynomial.Chebyshev.S ℝ ((k : ℤ) - 1)).eval t * y n) 0
            ((Polynomial.Chebyshev.S ℝ ((k : ℤ) - 2)).eval t * (b * y n))
        _ ≤ (k : ℝ) * |y n| + k * (|b| * |y n|) :=
          add_le_add (mul_le_mul_of_nonneg_right hfirst (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hsecond (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
        _ = (1 + |b|) * k * |y n| := by ring
        _ ≤ (1 + |b|) * n * |y n| := by gcongr
    · have ht' : 2 ≤ |t| := le_of_lt (lt_of_not_ge ht)
      have hm : ∀ k, k + 1 ≤ n → |y k| ≤ |y (k + 1)| := by
        intro k
        induction k with
        | zero => intro _; rw [hzero, abs_zero]; exact abs_nonneg _
        | succ k ih =>
          intro hk
          have hp := ih (by omega)
          have hr := hrec k (by omega)
          have ha := abs_add_le (y (k + 2)) (y k)
          have he : y (k + 2) + y k = t * y (k + 1) := by linarith [hr]
          rw [he, abs_mul] at ha
          have hmul := mul_le_mul_of_nonneg_right ht' (abs_nonneg (y (k + 1)))
          have hh : |y (k + 1)| ≤ |y (k + 2)| := by linarith
          simpa [Nat.succ_eq_add_one] using hh
      have hmono : ∀ i j, i ≤ j → j ≤ n → |y i| ≤ |y j| := by
        intro i j hij hj
        induction hij with
        | refl => exact le_rfl
        | @step j hij ih => exact (ih (by omega)).trans (hm j (by omega))
      intro j hj hjn
      calc
        |y j| ≤ |y n| := hmono j n hjn le_rfl
        _ ≤ (1 + |b|) * n * |y n| := by
          have hfac : (1 : ℝ) ≤ (1 + |b|) * n := by nlinarith [abs_nonneg b]
          simpa using mul_le_mul_of_nonneg_right hfac (abs_nonneg (y n))
  calc
    (∑ j ∈ Finset.range n, y (j + 1) ^ 2) ≤
        ∑ j ∈ Finset.range n, ((1 + |b|) * n * |y n|) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hb := hpoint (j + 1) (by omega) (by simpa using Finset.mem_range.mp hj)
      calc
        y (j + 1) ^ 2 = |y (j + 1)| ^ 2 := (sq_abs _).symm
        _ ≤ ((1 + |b|) * n * |y n|) ^ 2 := by gcongr
    _ = (1 + |b|) ^ 2 * (n : ℝ) ^ 3 * y n ^ 2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [mul_pow, mul_pow, sq_abs]
      ring

/-- The reflection sector is a free path with its final diagonal equal to b. -/
def sectorMatrix (n : ℕ) (b : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix n
    (Pi.single (Fin.last n) b) 1

private theorem sector_row (n : ℕ) (b : ℝ) (v : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    (sectorMatrix n b *ᵥ v) i =
      (if hi : i.val < n then v ⟨i.val + 1, by omega⟩ else b * v (Fin.last n)) +
      (if hi : 0 < i.val then v ⟨i.val - 1, by omega⟩ else 0) := by
  classical
  open D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence in
  have hup : (upperBand n 1 *ᵥ v) i =
      if hi : i.val < n then v ⟨i.val + 1, by omega⟩ else 0 := by
    simp only [Matrix.mulVec, dotProduct, upperBand, Pi.one_apply]
    by_cases hi : i.val < n
    · rw [dite_eq_left hi, Finset.sum_eq_single (⟨i.val + 1, by omega⟩ : Fin (n + 1))]
      · simp
      · intro j _ hj
        have hne : i.val + 1 ≠ j.val := by
          intro he
          apply hj
          exact Fin.ext he.symm
        simp [hne]
      · simp
    · rw [dite_eq_right hi]
      apply Finset.sum_eq_zero
      intro j _
      have hne : i.val + 1 ≠ j.val := by omega
      simp [hne]
  open D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence in
  have hlow : ((upperBand n 1)ᵀ *ᵥ v) i =
      if hi : 0 < i.val then v ⟨i.val - 1, by omega⟩ else 0 := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, upperBand, Pi.one_apply]
    by_cases hi : 0 < i.val
    · rw [dite_eq_left hi, Finset.sum_eq_single (⟨i.val - 1, by omega⟩ : Fin (n + 1))]
      · have he : i.val - 1 + 1 = i.val := by omega
        simp [he]
      · intro j _ hj
        have hne : j.val + 1 ≠ i.val := by
          intro he
          apply hj
          apply Fin.ext
          change j.val = i.val - 1
          omega
        simp [hne]
      · simp
    · rw [dite_eq_right hi]
      apply Finset.sum_eq_zero
      intro j _
      have hne : j.val + 1 ≠ i.val := by omega
      simp [hne]
  simp only [sectorMatrix, D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix,
    Matrix.add_mulVec, Matrix.mulVec_diagonal, Pi.add_apply, hup, hlow]
  by_cases hi : i.val < n
  · have hne : i ≠ Fin.last n := by intro he; subst i; simp at hi
    simp [hi, Pi.single_apply, hne]
  · have he : i = Fin.last n := Fin.ext (by simp; omega)
    subst i
    simp

/-- Endpoint observability for every eigenpair of the concrete sector matrix. -/
theorem sector_endpoint_observability (n : ℕ) (b t : ℝ) (v : Fin (n + 1) → ℝ)
    (hv : sectorMatrix n b *ᵥ v = t • v) :
    (∑ i, v i ^ 2) ≤ (1 + |b|) ^ 2 * (n + 1 : ℝ) ^ 3 * v (Fin.last n) ^ 2 := by
  let y : ℕ → ℝ := fun j =>
    if hj : 1 ≤ j ∧ j ≤ n + 1 then v ⟨j - 1, by omega⟩
    else if j = n + 2 then b * v (Fin.last n) else 0
  have hy0 : y 0 = 0 := by simp [y]
  have hyn : y (n + 1) = v (Fin.last n) := by
    simp only [y, show 1 ≤ n + 1 ∧ n + 1 ≤ n + 1 by omega, dite_true,
      Nat.add_sub_cancel]
    rfl
  have hyb : y (n + 1 + 1) = b * y (n + 1) := by simp [y, hyn, Nat.add_assoc]
  have hrec : ∀ j, j + 2 ≤ n + 1 + 1 → y (j + 2) = t * y (j + 1) - y j := by
    intro j hj
    have hjn : j ≤ n := by omega
    let i : Fin (n + 1) := ⟨j, by omega⟩
    have hr := congrFun hv i
    rw [sector_row] at hr
    simp only [Pi.smul_apply, smul_eq_mul] at hr
    have hyi : y (j + 1) = v i := by simp [y, i, show j + 1 ≤ n + 1 by omega]
    have hyleft : y j = if hi : 0 < i.val then v ⟨i.val - 1, by omega⟩ else 0 := by
      by_cases h0 : j = 0
      · subst j; simp [y, i]
      · simp [y, i, show 1 ≤ j by omega, show j ≤ n + 1 by omega,
          show 0 < j by omega]
    have hyright : y (j + 2) =
        if hi : i.val < n then v ⟨i.val + 1, by omega⟩ else b * v (Fin.last n) := by
      by_cases hl : j < n
      · simp [y, i, hl, show j + 2 ≤ n + 1 by omega]
      · have he : j = n := by omega
        subst j
        simp [y, i]
    rw [hyright, hyi, hyleft]
    linarith
  have hb := recurrence_endpoint_observability (n + 1) (by omega) t b y hy0 hrec hyb
  rw [hyn] at hb
  have hs : (∑ j ∈ Finset.range (n + 1), y (j + 1) ^ 2) = ∑ i, v i ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => y (j + 1) ^ 2)]
    apply Finset.sum_congr rfl
    intro j hj
    simp [y, show j.val + 1 ≤ n + 1 by omega]
  rw [hs] at hb
  simpa only [Nat.cast_add, Nat.cast_one] using hb

/-- Uniform separation between the two concrete reflection-sector spectra. -/
theorem sector_inverse_cubic_gap (n : ℕ) (u v : Fin (n + 1) → ℝ) (lam mu : ℝ)
    (hu : sectorMatrix n (-Real.sqrt 2) *ᵥ u = lam • u)
    (hv : sectorMatrix n (Real.sqrt 2) *ᵥ v = mu • v)
    (hnu : ∑ i, u i ^ 2 = 1) (hnv : ∑ i, v i ^ 2 = 1) :
    (2 * Real.sqrt 2 / (1 + Real.sqrt 2) ^ 2) / (n + 1 : ℝ) ^ 3 ≤ |lam - mu| := by
  have ha : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  let K : ℝ := (1 + Real.sqrt 2) ^ 2 * (n + 1 : ℝ) ^ 3
  have hK : 0 < K := by dsimp [K]; positivity
  have hs : (sectorMatrix n (-Real.sqrt 2)).IsSymm := by
    unfold sectorMatrix D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix
    simpa only [add_assoc] using
      (Matrix.isSymm_diagonal (Pi.single (Fin.last n) (-Real.sqrt 2))).add
        (Matrix.isSymm_add_transpose_self
          (D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.upperBand n 1))
  have hupdate : sectorMatrix n (Real.sqrt 2) = sectorMatrix n (-Real.sqrt 2) +
      (2 * Real.sqrt 2) • Matrix.vecMulVec
        (Pi.single (Fin.last n) 1) (Pi.single (Fin.last n) 1) := by
    classical
    ext i j
    simp only [sectorMatrix, D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix,
      Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.vecMulVec_apply,
      Pi.single_apply, smul_eq_mul]
    by_cases hi : i = Fin.last n <;> by_cases hj : j = Fin.last n <;>
      by_cases hij : i = j <;> simp_all <;> ring
  have hx := sector_endpoint_observability n (-Real.sqrt 2) lam u hu
  have hy := sector_endpoint_observability n (Real.sqrt 2) mu v hv
  rw [hnu, abs_neg, abs_of_pos ha] at hx
  rw [hnv, abs_of_pos ha] at hy
  have hz : |u ⬝ᵥ v| ≤ 1 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin (n + 1))) u v
    rw [hnu, hnv] at hh
    change |∑ i, u i * v i| ≤ 1
    nlinarith [sq_abs (∑ i, u i * v i)]
  have hg := rank_one_gap_of_matrices (by positivity : 0 < 2 * Real.sqrt 2) hK hs
    hupdate u v lam mu hu hv hx hy hz
  convert hg using 1
  dsimp [K]
  rw [div_div]

private theorem positive_index_congr {d : Type*} [Fintype d] [DecidableEq d]
    {A B : Matrix d d ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) :
    RHLinalg.posIndex hA = RHLinalg.posIndex hB := by subst B; rfl

private theorem positive_count_congr {d : Type*} [Fintype d] [DecidableEq d]
    {A B : Matrix d d ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) (t : ℝ) :
    RHLinalg.posIndexAbove hA t = RHLinalg.posIndexAbove hB t := by subst B; rfl

private theorem shifted_positive_count {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℝ) (hA : A.IsHermitian) (t : ℝ) :
    RHLinalg.posIndex (hA.sub (Matrix.isHermitian_diagonal (fun _ => t))) =
      RHLinalg.posIndexAbove hA t := by
  classical
  have hr : (A - Matrix.diagonal (fun _ => t)).charpoly.roots =
      A.charpoly.roots.map (fun x => x - t) := by
    rw [show Matrix.diagonal (fun _ : d => t) = Matrix.scalar d t by rfl,
      Matrix.charpoly_sub_scalar]
    simpa using Polynomial.roots_comp_C_mul_X_add_C A.charpoly 1 t isUnit_one
  have count (B : Matrix d d ℝ) (hB : B.IsHermitian) (p : ℝ → Prop)
      [DecidablePred p] :
      B.charpoly.roots.countP p = (Finset.univ.filter (fun i => p (hB.eigenvalues i))).card := by
    rw [hB.roots_charpoly_eq_eigenvalues, Multiset.countP_map]
    rfl
  unfold RHLinalg.posIndex RHLinalg.posIndexAbove
  rw [← count _ _ (fun x => 0 < x), hr, Multiset.countP_map]
  simpa only [Function.comp_apply, sub_pos, Multiset.countP_eq_card_filter] using
    count A hA (fun x => t < x)

private theorem positive_count_mono {d : Type*} [Fintype d] [DecidableEq d]
    {A R : Matrix d d ℝ} (hA : A.IsHermitian) (hR : R.PosSemidef) :
    RHLinalg.posIndex hA ≤ RHLinalg.posIndex (hA.add hR.isHermitian) := by
  obtain ⟨W, hp, hd⟩ := RHLinalg.posIndex_eq_max_finrank_posDefOn hA
  rw [← hd]
  apply RHLinalg.finrank_le_posIndex_of_posDefOn
  intro x hx hne
  rw [RHLinalg.hermForm_add]
  exact add_pos_of_pos_of_nonneg (hp x hx hne)
    (RHLinalg.hermForm_nonneg_of_posSemidef hR x)

private theorem rank_one_counts {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℝ) (hA : A.IsHermitian) (q : d) (c : ℝ) (hc : 0 ≤ c)
    (t : ℝ) :
    let R : Matrix d d ℝ := c • Matrix.vecMulVec (Pi.single q 1) (Pi.single q 1)
    let hR : R.PosSemidef := by
      simpa only [Pi.star_def, star_trivial] using
        (Matrix.posSemidef_vecMulVec_self_star (Pi.single q (1 : ℝ))).smul hc
    RHLinalg.posIndexAbove hA t ≤ RHLinalg.posIndexAbove (hA.add hR.isHermitian) t ∧
      RHLinalg.posIndexAbove (hA.add hR.isHermitian) t ≤ RHLinalg.posIndexAbove hA t + 1 := by
  classical
  dsimp only
  let R : Matrix d d ℝ := c • Matrix.vecMulVec (Pi.single q 1) (Pi.single q 1)
  have hR : R.PosSemidef := by
    simpa only [Pi.star_def, star_trivial] using
      (Matrix.posSemidef_vecMulVec_self_star (Pi.single q (1 : ℝ))).smul hc
  have hrank : R.rank ≤ 1 := by
    have he : R = Matrix.vecMulVec (c • Pi.single q 1) (Pi.single q 1) := by
      ext i j
      simp [R, Matrix.vecMulVec, mul_assoc]
    rw [he]
    exact Matrix.rank_vecMulVec_le _ _
  have hindex : RHLinalg.posIndex hR.isHermitian ≤ 1 := by
    rw [RHLinalg.posIndex_eq_rank_of_posSemidef hR]
    exact hrank
  have hshift := hA.sub (Matrix.isHermitian_diagonal (fun _ => t))
  have he : A - Matrix.diagonal (fun _ => t) + R =
      A + R - Matrix.diagonal (fun _ => t) := by abel
  have hlo := positive_count_mono hshift hR
  have hup := RHLinalg.posIndex_add_le hshift hR.isHermitian
  have he' := positive_index_congr (hshift.add hR.isHermitian)
    ((hA.add hR.isHermitian).sub (Matrix.isHermitian_diagonal (fun _ => t))) he
  rw [he', shifted_positive_count (A + R) (hA.add hR.isHermitian) t,
    shifted_positive_count A hA t] at hlo
  rw [he', shifted_positive_count (A + R) (hA.add hR.isHermitian) t,
    shifted_positive_count A hA t] at hup
  exact ⟨hlo, hup.trans (Nat.add_le_add_left hindex _)⟩

private theorem two_values_force_count {d : Type*} [Fintype d] [DecidableEq d]
    (a : d → ℝ) (i j : d) (hij : i ≠ j) (lo hi : ℝ) (hlt : lo ≤ hi)
    (hilo : lo < a i) (hjlo : lo < a j) (hihi : a i ≤ hi) (hjhi : a j ≤ hi) :
    (Finset.univ.filter (fun k => hi < a k)).card + 2 ≤
      (Finset.univ.filter (fun k => lo < a k)).card := by
  classical
  let S := Finset.univ.filter (fun k => hi < a k)
  have hiS : i ∉ S := by simp [S]; linarith
  have hjS : j ∉ S := by simp [S]; linarith
  have hsub : insert i (insert j S) ⊆ Finset.univ.filter (fun k => lo < a k) := by
    intro k hk
    simp only [Finset.mem_insert] at hk
    rcases hk with rfl | rfl | hk
    · simpa using hilo
    · simpa using hjlo
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lt_of_le_of_lt hlt (Finset.mem_filter.mp hk).2⟩
  have hh := Finset.card_le_card hsub
  simpa [S, Finset.card_insert_of_notMem, hiS, hjS, hij, Nat.add_assoc] using hh


private theorem absent_between_close_pair {d : Type*} [Fintype d] [DecidableEq d]
    (a b : d → ℝ) (delta : ℝ) (hd : 0 < delta)
    (hgap : ∀ i j, delta ≤ |a i - b j|)
    (i j : d) (hsmall : |a i - a j| < delta) :
    Finset.univ.filter (fun k => min (a i) (a j) - delta < b k) =
      Finset.univ.filter (fun k => max (a i) (a j) < b k) := by
  classical
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hk
    by_contra hn
    have hkhi : b k ≤ max (a i) (a j) := le_of_not_gt hn
    have hspan : max (a i) (a j) - min (a i) (a j) < delta := by
      rcases le_total (a i) (a j) with h | h
      · simpa [min_eq_left h, max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)] using hsmall
      · simpa [min_eq_right h, max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)] using hsmall
    have hmin : delta ≤ |min (a i) (a j) - b k| := by
      rcases le_total (a i) (a j) with h | h
      · simpa [min_eq_left h] using hgap i k
      · simpa [min_eq_right h] using hgap j k
    have hh : |min (a i) (a j) - b k| < delta :=
      abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith
  · intro hk
    exact lt_of_le_of_lt (by linarith [min_le_left (a i) (a j), le_max_left (a i) (a j)]) hk

private theorem separated_of_count_sandwich {d : Type*} [Fintype d] [DecidableEq d]
    (a b : d → ℝ) (delta : ℝ) (hd : 0 < delta)
    (hgap : ∀ i j, delta ≤ |a i - b j|)
    (hcount : ∀ t,
      (Finset.univ.filter (fun i => t < a i)).card ≤
        (Finset.univ.filter (fun i => t < b i)).card ∧
      (Finset.univ.filter (fun i => t < b i)).card ≤
        (Finset.univ.filter (fun i => t < a i)).card + 1) :
    (∀ i j, i ≠ j → delta ≤ |a i - a j|) ∧
      (∀ i j, i ≠ j → delta ≤ |b i - b j|) := by
  classical
  constructor
  · intro i j hij
    by_contra hbad
    have hsmall : |a i - a j| < delta := lt_of_not_ge hbad
    let lo := min (a i) (a j) - delta
    let hi := max (a i) (a j)
    have hsize := two_values_force_count a i j hij lo hi
      (by dsimp [lo, hi]; linarith [min_le_left (a i) (a j), le_max_left (a i) (a j)])
      (by dsimp [lo]; linarith [min_le_left (a i) (a j)])
      (by dsimp [lo]; linarith [min_le_right (a i) (a j)])
      (le_max_left _ _) (le_max_right _ _)
    have heq := absent_between_close_pair a b delta hd hgap i j hsmall
    have h1 := (hcount lo).1
    have h2 := (hcount hi).2
    change (Finset.univ.filter (fun k => lo < b k)) =
      (Finset.univ.filter (fun k => hi < b k)) at heq
    rw [heq] at h1
    omega
  · intro i j hij
    by_contra hbad
    have hsmall : |b i - b j| < delta := lt_of_not_ge hbad
    let lo := min (b i) (b j) - delta
    let hi := max (b i) (b j)
    have hsize := two_values_force_count b i j hij lo hi
      (by dsimp [lo, hi]; linarith [min_le_left (b i) (b j), le_max_left (b i) (b j)])
      (by dsimp [lo]; linarith [min_le_left (b i) (b j)])
      (by dsimp [lo]; linarith [min_le_right (b i) (b j)])
      (le_max_left _ _) (le_max_right _ _)
    have hswap : ∀ i j, delta ≤ |b i - a j| := by
      intro i j; simpa [abs_sub_comm] using hgap j i
    have heq := absent_between_close_pair b a delta hd hswap i j hsmall
    have h1 := (hcount lo).2
    have h2 := (hcount hi).1
    change (Finset.univ.filter (fun k => lo < a k)) =
      (Finset.univ.filter (fun k => hi < a k)) at heq
    rw [heq] at h1
    omega

private theorem sector_hermitian (n : ℕ) (b : ℝ) : (sectorMatrix n b).IsHermitian := by
  unfold sectorMatrix D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix
  simpa only [add_assoc, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.isHermitian_diagonal (Pi.single (Fin.last n) b)).add
      (Matrix.isHermitian_add_transpose_self
        (D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.upperBand n 1))

/-- The complete sector union retains every algebraic eigenvalue, with its index. -/
def sectorSpectrum (n : ℕ) : Fin (n + 1) ⊕ Fin (n + 1) → ℝ :=
  Sum.elim (sector_hermitian n (-Real.sqrt 2)).eigenvalues
    (sector_hermitian n (Real.sqrt 2)).eigenvalues

/-- Every two distinct indices in the complete sector union are uniformly separated. -/
theorem sector_spectral_gap (n : ℕ) (i j : Fin (n + 1) ⊕ Fin (n + 1)) (hij : i ≠ j) :
    (2 * Real.sqrt 2 / (1 + Real.sqrt 2) ^ 2) / (n + 1 : ℝ) ^ 3 ≤
      |sectorSpectrum n i - sectorSpectrum n j| := by
  classical
  let hA := sector_hermitian n (-Real.sqrt 2)
  let hB := sector_hermitian n (Real.sqrt 2)
  let a := hA.eigenvalues
  let b := hB.eigenvalues
  let delta := (2 * Real.sqrt 2 / (1 + Real.sqrt 2) ^ 2) / (n + 1 : ℝ) ^ 3
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hn (c : ℝ) (k : Fin (n + 1)) :
      ∑ l, ((sector_hermitian n c).eigenvectorBasis k l) ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq]
    rw [(sector_hermitian n c).eigenvectorBasis.orthonormal.norm_eq_one k]
    norm_num
  have hcross : ∀ k l, delta ≤ |a k - b l| := by
    intro k l
    exact sector_inverse_cubic_gap n (hA.eigenvectorBasis k) (hB.eigenvectorBasis l)
      _ _ (hA.mulVec_eigenvectorBasis k) (hB.mulVec_eigenvectorBasis l) (hn _ _) (hn _ _)
  have hcount : ∀ t,
      (Finset.univ.filter (fun k => t < a k)).card ≤
        (Finset.univ.filter (fun k => t < b k)).card ∧
      (Finset.univ.filter (fun k => t < b k)).card ≤
        (Finset.univ.filter (fun k => t < a k)).card + 1 := by
    intro t
    have hc := rank_one_counts (sectorMatrix n (-Real.sqrt 2)) hA (Fin.last n)
      (2 * Real.sqrt 2) (by positivity) t
    have he : sectorMatrix n (-Real.sqrt 2) +
        (2 * Real.sqrt 2) • Matrix.vecMulVec (Pi.single (Fin.last n) 1)
          (Pi.single (Fin.last n) 1) = sectorMatrix n (Real.sqrt 2) := by
      ext k l
      simp only [sectorMatrix, D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix,
        Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.vecMulVec_apply,
        Pi.single_apply, smul_eq_mul]
      by_cases hk : k = Fin.last n <;> by_cases hl : l = Fin.last n <;>
        by_cases hkl : k = l <;> simp_all <;> ring
    dsimp only at hc
    have hC : (sectorMatrix n (-Real.sqrt 2) +
        (2 * Real.sqrt 2) • Matrix.vecMulVec (Pi.single (Fin.last n) 1)
          (Pi.single (Fin.last n) 1)).IsHermitian := he.symm ▸ hB
    have he' := positive_count_congr hC hB he t
    rw [he'] at hc
    exact hc
  have hs := separated_of_count_sandwich a b delta hd hcross hcount
  cases i with
  | inl k => cases j with
    | inl l => exact hs.1 k l (by simpa using hij)
    | inr l => exact hcross k l
  | inr k => cases j with
    | inl l =>
      change delta ≤ |b k - a l|
      rw [abs_sub_comm]
      exact hcross l k
    | inr l => exact hs.2 k l (by simpa using hij)

private def folding (n : ℕ) :
    Fin (n + 1) ⊕ Fin (n + 1) ≃ Fin (2 * (n + 1) - 1 + 1) :=
  ((Equiv.sumCongr (Equiv.refl (Fin (n + 1))) Fin.revPerm).trans finSumFinEquiv).trans
    (finCongr (by omega))

private theorem folded_defect (n : ℕ) :
    (centralDefect (n + 1) (by omega)).submatrix (folding n) (folding n) =
      Matrix.fromBlocks (sectorMatrix n 0)
        (Real.sqrt 2 • Matrix.vecMulVec (Pi.single (Fin.last n) 1) (Pi.single (Fin.last n) 1))
        (Real.sqrt 2 • Matrix.vecMulVec (Pi.single (Fin.last n) 1) (Pi.single (Fin.last n) 1))
        (sectorMatrix n 0) := by
  classical
  ext i j
  cases i with
  | inl i => cases j with
    | inl j =>
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁]
      simp [centralDefect, centralEdges, folding, sectorMatrix,
        D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix,
        D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.upperBand, Matrix.diagonal_apply]
      split_ifs <;> simp_all [Fin.ext_iff] <;> omega
    | inr j =>
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂]
      simp [centralDefect, centralEdges, folding,
        D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix,
        D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.upperBand, Matrix.diagonal_apply,
        Matrix.vecMulVec, Pi.single_apply, Fin.revPerm, Fin.rev]
      split_ifs <;> simp_all [Fin.ext_iff] <;> omega
  | inr i => cases j with
    | inl j =>
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁]
      simp [centralDefect, centralEdges, folding,
        D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix,
        D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.upperBand, Matrix.diagonal_apply,
        Matrix.vecMulVec, Pi.single_apply, Fin.revPerm, Fin.rev]
      split_ifs <;> simp_all [Fin.ext_iff] <;> omega
    | inr j =>
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂]
      simp [centralDefect, centralEdges, folding, sectorMatrix,
        D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix,
        D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.upperBand, Matrix.diagonal_apply,
        Fin.revPerm, Fin.rev]
      split_ifs <;> simp_all [Fin.ext_iff] <;> omega

private theorem central_charpoly (n : ℕ) :
    (centralDefect (n + 1) (by omega)).charpoly =
      (sectorMatrix n (Real.sqrt 2)).charpoly * (sectorMatrix n (-Real.sqrt 2)).charpoly := by
  classical
  let P := sectorMatrix n 0
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Real.sqrt 2 • Matrix.vecMulVec (Pi.single (Fin.last n) 1) (Pi.single (Fin.last n) 1)
  let W : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ :=
    Matrix.fromBlocks 1 1 1 (-1)
  let H := Matrix.fromBlocks P E E P
  let D := Matrix.fromBlocks (sectorMatrix n (Real.sqrt 2)) 0 0
    (sectorMatrix n (-Real.sqrt 2))
  have hp : sectorMatrix n (Real.sqrt 2) = P + E := by
    ext i j
    simp only [P, E, sectorMatrix, D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix,
      Matrix.add_apply, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.vecMulVec_apply, Pi.single_apply]
    by_cases hi : i = Fin.last n <;> by_cases hj : j = Fin.last n <;>
      by_cases hij : i = j <;> simp_all <;> ring
  have hm : sectorMatrix n (-Real.sqrt 2) = P - E := by
    ext i j
    simp only [P, E, sectorMatrix, D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix,
      Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.vecMulVec_apply, Pi.single_apply]
    by_cases hi : i = Fin.last n <;> by_cases hj : j = Fin.last n <;>
      by_cases hij : i = j <;> simp_all <;> ring
  have hw : W * ((1 / 2 : ℝ) • W) = 1 := by
    simp [W, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, ← add_smul]
    norm_num <;> rfl
  have hconj : H * W = W * D := by
    simp [H, W, D, hp, hm, Matrix.fromBlocks_multiply, sub_eq_add_neg, add_comm]
  have hH : H = W * D * ((1 / 2 : ℝ) • W) := by
    rw [← hconj, Matrix.mul_assoc, hw, Matrix.mul_one]
  have hc : H.charpoly = D.charpoly := by
    rw [hH, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc]
    have hw' : ((1 / 2 : ℝ) • W) * W = 1 := by
      rw [Matrix.smul_mul, ← Matrix.mul_smul, hw]
    rw [hw', Matrix.one_mul]
  have hfold : H.charpoly = (centralDefect (n + 1) (by omega)).charpoly := by
    rw [show H = (centralDefect (n + 1) (by omega)).submatrix (folding n) (folding n) from
      (folded_defect n).symm]
    simpa only [Matrix.reindex_apply, Equiv.symm_symm] using
      Matrix.charpoly_reindex (folding n).symm (centralDefect (n + 1) (by omega))
  rw [← hfold, hc]
  exact Matrix.charpoly_fromBlocks_zero₁₂
    (M₁₁ := sectorMatrix n (Real.sqrt 2))
    (M₂₁ := (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
    (M₂₂ := sectorMatrix n (-Real.sqrt 2))

/-- The actual defect characteristic roots are precisely the complete sector union. -/
private theorem central_roots (n : ℕ) :
    (centralDefect (n + 1) (by omega)).charpoly.roots =
      Finset.univ.val.map (sectorSpectrum n) := by
  classical
  rw [central_charpoly, Polynomial.roots_mul (mul_ne_zero
    (sectorMatrix n (Real.sqrt 2)).charpoly_monic.ne_zero
    (sectorMatrix n (-Real.sqrt 2)).charpoly_monic.ne_zero)]
  rw [(sector_hermitian n (Real.sqrt 2)).roots_charpoly_eq_eigenvalues,
    (sector_hermitian n (-Real.sqrt 2)).roots_charpoly_eq_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq, Function.comp_def]
  rw [← Finset.univ_disjSum_univ]
  rw [Finset.val_disjSum, Multiset.map_disjSum]
  simpa only [sectorSpectrum, Sum.elim_inl, Sum.elim_inr] using
    (add_comm (Finset.univ.val.map (sector_hermitian n (Real.sqrt 2)).eigenvalues)
      (Finset.univ.val.map (sector_hermitian n (-Real.sqrt 2)).eigenvalues))

/-- Every enumeration of all algebraic eigenvalues of the actual defect matrix
obeys the same pairwise inverse-cubic bound. -/
theorem central_spectral_gap (n : ℕ)
    (lambda : Fin (2 * (n + 1) - 1 + 1) → ℝ)
    (hlambda : Finset.univ.val.map lambda =
      (centralDefect (n + 1) (by omega)).charpoly.roots)
    (i j : Fin (2 * (n + 1) - 1 + 1)) (hij : i ≠ j) :
    (2 * Real.sqrt 2 / (1 + Real.sqrt 2) ^ 2) / (n + 1 : ℝ) ^ 3 ≤
      |lambda i - lambda j| := by
  classical
  let delta := (2 * Real.sqrt 2 / (1 + Real.sqrt 2) ^ 2) / (n + 1 : ℝ) ^ 3
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hinj : Function.Injective (sectorSpectrum n) := by
    intro k l hkl
    by_contra hne
    have hg := sector_spectral_gap n k l hne
    rw [hkl, sub_self, abs_zero] at hg
    exact (not_le_of_gt hd) hg
  have hroot : (Finset.univ.val.map (sectorSpectrum n)).Nodup :=
    Finset.univ.nodup.map hinj
  have hlist : Finset.univ.val.map lambda =
      Finset.univ.val.map (sectorSpectrum n) := hlambda.trans (central_roots n)
  have hlnodup : (Finset.univ.val.map lambda).Nodup := by rw [hlist]; exact hroot
  have hlinj : Function.Injective lambda := by
    intro i j hij
    exact Multiset.inj_on_of_nodup_map hlnodup i (by simp) j (by simp) hij
  have hm (k : Fin (2 * (n + 1) - 1 + 1)) :
      ∃ l, sectorSpectrum n l = lambda k := by
    have hmem : lambda k ∈ Finset.univ.val.map lambda := Multiset.mem_map.mpr ⟨k, by simp, rfl⟩
    rw [hlist] at hmem
    obtain ⟨l, _, he⟩ := Multiset.mem_map.mp hmem
    exact ⟨l, he⟩
  obtain ⟨k, hk⟩ := hm i
  obtain ⟨l, hl⟩ := hm j
  have hkl : k ≠ l := by intro he; apply hij; apply hlinj; rw [← hk, ← hl, he]
  simpa only [hk, hl] using sector_spectral_gap n k l hkl

/-- A positive common constant works for all positive half-dimensions and all
algebraic eigenvalue enumerations of the fixed central-square-root-two family. -/
theorem uniform_inverse_cubic_gap :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ (n : ℕ) (hn : 1 ≤ n), N ≤ n →
        (centralDefect n hn).IsHermitian ∧
        ∀ (lambda : Fin (2 * n - 1 + 1) → ℝ),
          Finset.univ.val.map lambda = (centralDefect n hn).charpoly.roots →
          ∀ i j, i ≠ j → c / (n : ℝ) ^ 3 ≤ |lambda i - lambda j| := by
  refine ⟨2 * Real.sqrt 2 / (1 + Real.sqrt 2) ^ 2, by positivity, 1, le_rfl, ?_⟩
  intro n hn _
  constructor
  · unfold centralDefect D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix
    simpa only [add_assoc, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.isHermitian_diagonal (0 : Fin (2 * n - 1 + 1) → ℝ)).add
        (Matrix.isHermitian_add_transpose_self
          (D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.upperBand (2 * n - 1) (centralEdges n hn)))
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    intro lambda hlambda i j hij
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
      central_spectral_gap m lambda hlambda i j hij

end D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
