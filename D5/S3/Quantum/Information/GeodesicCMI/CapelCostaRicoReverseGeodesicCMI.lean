/- GID: D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.claim; result=D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.result; claim=D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.claim
   digest: Reverse geodesic CMI has no trace-distance modulus on a fixed faithful pair-marginal fiber. -/

import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoGeodesicModular
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Capel and Costa Rico, arXiv:2608.15833, equations (52), (59), (62), (357)
and Open questions 6. Preregistration: trureturing #32390. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoReverseGeodesicCMI

open Matrix Filter Set
open scoped BigOperators ComplexOrder CStarAlgebra Kronecker Matrix MatrixOrder
  Matrix.Norms.L2Operator Topology
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceDistance)
open D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation (diagonal_norm)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft partialTraceRight)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (cfc_diagonal)

noncomputable section

section MatrixForm

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real diagonal in the specified orthonormal basis. -/
def diagReal (a : n → ℝ) : Matrix n n ℂ :=
  Matrix.diagonal fun i => Complex.ofReal (a i)

omit [Fintype n] in
private theorem diagReal_posDef (a : n → ℝ) (ha : ∀ i, 0 < a i) :
    (diagReal a).PosDef :=
  Matrix.PosDef.diagonal (fun i => Complex.zero_lt_real.mpr (ha i))

private theorem trace_diagReal (a : n → ℝ) :
    (diagReal a).trace = Complex.ofReal (∑ i, a i) := by
  simp only [diagReal, Matrix.trace_diagonal, Complex.ofReal_sum]

private theorem diagReal_mul (a b : n → ℝ) :
    diagReal a * diagReal b = diagReal (fun i => a i * b i) := by
  simp [diagReal, Complex.ofReal_mul]

private theorem cfc_diagReal (f : ℝ → ℝ) (a : n → ℝ) :
    cfc f (diagReal a) = diagReal (fun i => f (a i)) :=
  cfc_diagonal f a

omit [Fintype n] in
private theorem diagReal_sub (a b : n → ℝ) :
    diagReal a - diagReal b = diagReal (fun i => a i - b i) := by
  simpa only [diagReal, Complex.ofReal_sub] using
    (Matrix.diagonal_sub (fun i => (a i : ℂ)) (fun i => (b i : ℂ)))

/-- A normalized positive diagonal, packaged as the repository's density state. -/
def diagonalState (a : n → ℝ) (ha : ∀ i, 0 < a i) (hn : ∑ i, a i = 1) :
    DensityState n := by
  refine ⟨CStarMatrix.ofMatrix (diagReal a), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (diagReal_posDef a ha).posSemidef.nonneg
  · change (diagReal a).trace = 1
    calc
      (diagReal a).trace = Complex.ofReal (∑ i, a i) := trace_diagReal a
      _ = 1 := by rw [hn, Complex.ofReal_one]

end MatrixForm

section Geodesic

variable {n : Type*} [Fintype n] [DecidableEq n]

def modularEigenvalue (t : ℝ) (r s : n → ℝ) (i : n × n) : ℝ :=
  r i.1 ^ (1 - t) * r i.2 ^ t / s i.2

private theorem geodesicAction_diagonal (t : ℝ) (r s : n → ℝ)
    (hs : ∀ i, 0 < s i) (X : Matrix n n ℂ) (i j : n) :
    geodesicAction t (diagReal r) (diagReal s) X i j =
      (modularEigenvalue t r s (i, j) : ℂ) * X i j := by
  have hright (j : n) :
      (Real.sqrt (s j))⁻¹ * r j ^ t * (Real.sqrt (s j))⁻¹ = r j ^ t / s j := by
    calc
      _ = r j ^ t / (Real.sqrt (s j) * Real.sqrt (s j)) := by
        rw [div_eq_mul_inv, _root_.mul_inv]
        ring
      _ = _ := by rw [Real.mul_self_sqrt (hs j).le]
  unfold geodesicAction
  simp only [cfc_diagReal, diagReal_mul]
  simp only [diagReal, Matrix.mul_diagonal, Matrix.diagonal_mul,
    hright, modularEigenvalue, Complex.ofReal_div, Complex.ofReal_mul]
  ring

/-- The full diagonal spectrum, including the off-diagonal matrix units. -/
theorem geodesicModular_diagonal (t : ℝ) (r s : n → ℝ) (hs : ∀ i, 0 < s i) :
    geodesicModular t (diagReal r) (diagReal s) = diagReal (modularEigenvalue t r s) := by
  apply Matrix.ext
  intro i j
  change geodesicAction t (diagReal r) (diagReal s) (Matrix.single j.1 j.2 1)
    i.1 i.2 = _
  rw [geodesicAction_diagonal t r s hs]
  by_cases h : i = j
  · subst j
    simp [diagReal]
  · have hj : ¬ (j.1 = i.1 ∧ j.2 = i.2) :=
      fun hEq => h ((Prod.ext hEq.1 hEq.2).symm)
    simp [diagReal, h, hj]

private theorem weightedVector_diagonal (s : n → ℝ) (i j : n) :
    weightedVector (diagReal s) (i, j) =
      if i = j then (Real.sqrt (s i) : ℂ) else 0 := by
  simp only [weightedVector, diagReal, cfc_diagonal, Matrix.diagonal_apply]

/-- Equation (62) specializes the spectral quadratic form to classical KL on faithful diagonals. -/
theorem geodesicRelativeEntropy_diagonal (t : ℝ) (r s : n → ℝ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i) :
    geodesicRelativeEntropy t (diagReal r) (diagReal s) =
      ∑ i, r i * Real.log (r i / s i) := by
  have hdiag (i : n) : modularEigenvalue t r s (i, i) = r i / s i := by
    change r i ^ (1 - t) * r i ^ t / s i = r i / s i
    rw [← Real.rpow_add (hr i), sub_add_cancel, Real.rpow_one]
  have hvec (i j : n) : weightedVector (Matrix.diagonal fun k : n => (s k : ℂ)) (i, j) =
      if i = j then (Real.sqrt (s i) : ℂ) else 0 :=
    weightedVector_diagonal s i j
  unfold geodesicRelativeEntropy
  rw [geodesicModular_diagonal t r s hs, cfc_diagReal]
  simp only [diagReal, Matrix.mulVec_diagonal, dotProduct, Fintype.sum_prod_type, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · have hself : weightedVector (Matrix.diagonal fun k : n => (s k : ℂ)) (i, i) =
        (Real.sqrt (s i) : ℂ) := (hvec i i).trans (if_pos rfl)
    simp only [hself, Pi.star_apply,
      Complex.star_def, Complex.conj_ofReal, hdiag,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    calc
      _ = (Real.sqrt (s i) * Real.sqrt (s i)) *
          (r i / s i * Real.log (r i / s i)) := by ring
      _ = _ := by
        rw [Real.mul_self_sqrt (hs i).le, ← mul_assoc, mul_div_cancel₀ _ (hs i).ne']
  · intro j _ hj
    have hij : i ≠ j := Ne.symm hj
    simp [Pi.star_apply, hvec, hij]
  · simp

end Geodesic

abbrev Bit := Fin 2
abbrev Pair := Bit × Bit
abbrev Triple := Pair × Bit

def toMatrix {n : Type*} [Fintype n] [DecidableEq n] (ρ : DensityState n) :
    Matrix n n ℂ :=
  CStarMatrix.ofMatrix.symm ρ.val

private def middleReorder : (Pair × Bit) ≃ Triple where
  toFun i := ((i.1.1, i.2), i.1.2)
  invFun i := ((i.1.1, i.2), i.1.2)
  left_inv := by rintro ⟨⟨a, c⟩, b⟩; rfl
  right_inv := by rintro ⟨⟨a, b⟩, c⟩; rfl

def marginalAB (ρ : Matrix Triple Triple ℂ) : Matrix Pair Pair ℂ :=
  partialTraceRight ρ

def marginalAC (ρ : Matrix Triple Triple ℂ) : Matrix Pair Pair ℂ :=
  partialTraceRight (ρ.submatrix middleReorder middleReorder)

def marginalBC (ρ : Matrix Triple Triple ℂ) : Matrix Pair Pair ℂ :=
  partialTraceLeft (ρ.submatrix (Equiv.prodAssoc Bit Bit Bit).symm
    (Equiv.prodAssoc Bit Bit Bit).symm)

def marginalB (ρ : Matrix Triple Triple ℂ) : Matrix Bit Bit ℂ :=
  partialTraceLeft (marginalAB ρ)

private theorem partialTraceRight_diagReal {A B : Type*} [DecidableEq A]
    [DecidableEq B] [Fintype B] (p : A × B → ℝ) :
    partialTraceRight (diagReal p) = diagReal (fun a => ∑ b, p (a, b)) := by
  apply Matrix.ext
  intro a a'
  by_cases h : a = a'
  · subst a'
    simp [partialTraceRight, diagReal, Complex.ofReal_sum]
  · simp [partialTraceRight, diagReal, h]

private theorem partialTraceLeft_diagReal {A B : Type*} [DecidableEq A]
    [DecidableEq B] [Fintype A] (p : A × B → ℝ) :
    partialTraceLeft (diagReal p) = diagReal (fun b => ∑ a, p (a, b)) := by
  apply Matrix.ext
  intro b b'
  by_cases h : b = b'
  · subst b'
    simp [partialTraceLeft, diagReal, Complex.ofReal_sum]
  · simp [partialTraceLeft, diagReal, h]

private theorem submatrix_diagReal {A B : Type*} [DecidableEq A] [DecidableEq B]
    (p : A → ℝ) (e : B ≃ A) :
    (diagReal p).submatrix e e = diagReal (fun b => p (e b)) :=
  Matrix.submatrix_diagonal_equiv _ e

private theorem kronecker_diagReal {A B : Type*} [DecidableEq A] [DecidableEq B]
    (a : A → ℝ) (b : B → ℝ) :
    diagReal a ⊗ₖ diagReal b = diagReal (fun i => a i.1 * b i.2) := by
  simp only [diagReal, Matrix.diagonal_kronecker_diagonal, Complex.ofReal_mul]

/-- The reverse orientation in equation (357), evaluated on density matrices. -/
def reverseCMI (t : ℝ) (τ : DensityState Bit) (ρ : Matrix Triple Triple ℂ) : ℝ :=
  geodesicRelativeEntropy t (marginalAB ρ ⊗ₖ toMatrix τ) ρ -
    geodesicRelativeEntropy t (marginalB ρ ⊗ₖ toMatrix τ) (marginalBC ρ)

def weight (i : Triple) : ℕ := i.1.1.val + i.1.2.val + i.2.val

def q (i : Triple) : ℝ :=
  match weight i with
  | 0 => 0
  | 1 => 3 / 16
  | 2 => 1 / 8
  | _ => 1 / 16

def parity (i : Triple) : ℝ := (-1) ^ weight i

def p (x : ℝ) (i : Triple) : ℝ := q i + parity i * x

def origin : Triple := ((0, 0), 0)

private theorem p_origin (x : ℝ) : p x origin = x := by
  norm_num [p, q, parity, weight, origin]

private theorem q_pos_of_ne (i : Triple) (hi : i ≠ origin) : 0 < q i := by
  rcases i with ⟨⟨a, b⟩, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c
  all_goals
    first
    | exact (hi rfl).elim
    | norm_num [q, weight]

abbrev Valid (x : ℝ) : Prop := 0 < x ∧ x < 1 / 16

private theorem p_pos {x : ℝ} (hx : Valid x) (i : Triple) : 0 < p x i := by
  rcases i with ⟨⟨a, b⟩, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [p, q, parity, weight] <;> linarith [hx.1, hx.2]

private theorem p_sum (x : ℝ) : ∑ i, p x i = 1 := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [p, q, parity, weight] <;> ring

private theorem valid_sq {x : ℝ} (hx : Valid x) : Valid (x ^ 2) := by
  refine ⟨pow_pos hx.1 _, ?_⟩
  have hp := mul_pos hx.1 (show 0 < 1 - x by linarith [hx.2])
  nlinarith [hx.2]

/-- The faithful three-qubit state in the computational basis. -/
def family (x : ℝ) (hx : Valid x) : DensityState Triple :=
  diagonalState (p x) (p_pos hx) (p_sum x)

private theorem family_matrix (x : ℝ) (hx : Valid x) :
    toMatrix (family x hx) = diagReal (p x) := rfl

def pairLaw (i : Pair) : ℝ := if i.1 = i.2 then 3 / 16 else 5 / 16

private theorem pairLaw_pos (i : Pair) : 0 < pairLaw i := by
  unfold pairLaw
  split <;> norm_num

private theorem family_AB (x : ℝ) :
    marginalAB (diagReal (p x)) = diagReal pairLaw := by
  rw [marginalAB, partialTraceRight_diagReal]
  apply congrArg diagReal
  funext i
  rcases i with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [Fin.sum_univ_two, p, q, parity, weight, pairLaw] <;> ring

private theorem family_AC (x : ℝ) :
    marginalAC (diagReal (p x)) = diagReal pairLaw := by
  rw [marginalAC, submatrix_diagReal, partialTraceRight_diagReal]
  apply congrArg diagReal
  funext i
  rcases i with ⟨a, c⟩
  fin_cases a <;> fin_cases c <;>
    norm_num [middleReorder, Fin.sum_univ_two, p, q, parity, weight, pairLaw] <;> ring

private theorem family_BC (x : ℝ) :
    marginalBC (diagReal (p x)) = diagReal pairLaw := by
  rw [marginalBC, submatrix_diagReal, partialTraceLeft_diagReal]
  apply congrArg diagReal
  funext i
  rcases i with ⟨b, c⟩
  fin_cases b <;> fin_cases c <;>
    norm_num [Equiv.prodAssoc, Fin.sum_univ_two, p, q, parity, weight, pairLaw] <;> ring

private theorem family_B (x : ℝ) :
    marginalB (diagReal (p x)) = diagReal (fun _ : Bit => 1 / 2) := by
  rw [marginalB, family_AB, partialTraceLeft_diagReal]
  apply congrArg diagReal
  funext i
  fin_cases i <;> norm_num [Fin.sum_univ_two, pairLaw]

/-- The same faithful diagonal matrix is the actual AB, AC and BC marginal. -/
theorem family_fixed_marginals (x : ℝ) (hx : Valid x) :
    (diagReal pairLaw).PosDef ∧
    marginalAB (toMatrix (family x hx)) = diagReal pairLaw ∧
    marginalAC (toMatrix (family x hx)) = diagReal pairLaw ∧
    marginalBC (toMatrix (family x hx)) = diagReal pairLaw :=
  ⟨diagReal_posDef pairLaw pairLaw_pos, family_AB x, family_AC x, family_BC x⟩

private theorem distanceFormula_pos {x : ℝ} (hx : Valid x) : 0 < 4 * (x - x ^ 2) := by
  have hp := mul_pos hx.1 (show 0 < 1 - x by linarith [hx.2])
  nlinarith

/-- The exact half trace norm for the two witnesses. -/
theorem family_traceDistance {x : ℝ} (hx : Valid x) :
    traceDistance (family (x ^ 2) (valid_sq hx)) (family x hx) = 4 * (x - x ^ 2) := by
  change traceNorm (diagReal (p (x ^ 2)) - diagReal (p x)) / 2 = _
  rw [diagReal_sub]
  change traceNorm (Matrix.diagonal (fun i => Complex.ofReal (p (x ^ 2) i - p x i))) / 2 = _
  rw [diagonal_norm]
  have hδ : 0 ≤ x - x ^ 2 := by linarith [distanceFormula_pos hx]
  have h (i : Triple) : |p (x ^ 2) i - p x i| = x - x ^ 2 := by
    rw [show p (x ^ 2) i - p x i = -(parity i * (x - x ^ 2)) by
      unfold p
      ring]
    simp [parity, abs_mul, abs_pow, abs_of_nonneg hδ]
  simp_rw [h]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring

private def referenceWeight (τ : Bit → ℝ) (i : Triple) : ℝ := pairLaw i.1 * τ i.2

private theorem reverseCMI_family (t : ℝ) (τ : Bit → ℝ)
    (hτ : ∀ i, 0 < τ i) (hτsum : ∑ i, τ i = 1) {x : ℝ} (hx : Valid x) :
    reverseCMI t (diagonalState τ hτ hτsum) (diagReal (p x)) =
      (∑ i, referenceWeight τ i * Real.log (referenceWeight τ i / p x i)) -
        geodesicRelativeEntropy t (diagReal (fun i : Pair => (1 / 2) * τ i.2))
          (diagReal pairLaw) := by
  unfold reverseCMI
  rw [family_AB, family_B, family_BC]
  change geodesicRelativeEntropy t (diagReal pairLaw ⊗ₖ diagReal τ) (diagReal (p x)) -
    geodesicRelativeEntropy t (diagReal (fun _ : Bit => 1 / 2) ⊗ₖ diagReal τ)
      (diagReal pairLaw) = _
  rw [kronecker_diagReal, kronecker_diagReal]
  change geodesicRelativeEntropy t (diagReal (referenceWeight τ)) (diagReal (p x)) -
    geodesicRelativeEntropy t (diagReal (fun i : Pair => (1 / 2) * τ i.2))
      (diagReal pairLaw) = _
  rw [geodesicRelativeEntropy_diagonal t (referenceWeight τ) (p x)
    (fun i => mul_pos (pairLaw_pos i.1) (hτ i.2)) (p_pos hx)]

def gapTerm (τ : Bit → ℝ) (x : ℝ) (i : Triple) : ℝ :=
  referenceWeight τ i * Real.log (p x i / p (x ^ 2) i)

/-- The lower-system term is constant, so the gap is the stated logarithmic sum. -/
theorem family_gap_formula (t : ℝ) (τ : Bit → ℝ)
    (hτ : ∀ i, 0 < τ i) (hτsum : ∑ i, τ i = 1) {x : ℝ} (hx : Valid x) :
    reverseCMI t (diagonalState τ hτ hτsum) (diagReal (p (x ^ 2))) -
      reverseCMI t (diagonalState τ hτ hτsum) (diagReal (p x)) =
        ∑ i, gapTerm τ x i := by
  rw [reverseCMI_family t τ hτ hτsum (valid_sq hx), reverseCMI_family t τ hτ hτsum hx,
    sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hw : 0 < referenceWeight τ i := mul_pos (pairLaw_pos i.1) (hτ i.2)
  unfold gapTerm
  rw [Real.log_div hw.ne' (p_pos (valid_sq hx) i).ne',
    Real.log_div hw.ne' (p_pos hx i).ne',
    Real.log_div (p_pos hx i).ne' (p_pos (valid_sq hx) i).ne']
  ring

private theorem gapTerm_origin (τ : Bit → ℝ) {x : ℝ} (hx : 0 < x) :
    gapTerm τ x origin = (3 / 16) * τ 0 * (-Real.log x) := by
  simp only [gapTerm, p_origin]
  rw [Real.log_div hx.ne' (pow_ne_zero 2 hx.ne'), Real.log_pow]
  norm_num [referenceWeight, pairLaw, origin] <;> ring

private def remainder (τ : Bit → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.erase origin, gapTerm τ x i

private theorem remainder_tendsto_zero (τ : Bit → ℝ) :
    Tendsto (remainder τ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsum :
      Tendsto (remainder τ) (𝓝[>] (0 : ℝ))
        (𝓝 (∑ _i ∈ Finset.univ.erase origin, (0 : ℝ))) := by
    unfold remainder
    apply tendsto_finsetSum
    intro i hi
    have hq := q_pos_of_ne i (Finset.mem_erase.mp hi).1
    have hp : ContinuousAt (fun x : ℝ => p x i) 0 := by
      unfold p
      fun_prop
    have hp2 : ContinuousAt (fun x : ℝ => p (x ^ 2) i) 0 := by
      unfold p
      fun_prop
    have hr : ContinuousAt (gapTerm τ · i) 0 := by
      unfold gapTerm
      have hden : p ((0 : ℝ) ^ 2) i ≠ 0 := by simpa [p] using hq.ne'
      have hquot : ContinuousAt (fun x : ℝ => p x i / p (x ^ 2) i) 0 :=
        hp.div₀ hp2 hden
      have hratio : p 0 i / p ((0 : ℝ) ^ 2) i ≠ 0 := by
        simp [p, div_self hq.ne']
      exact continuousAt_const.mul (hquot.log hratio)
    have hzero : gapTerm τ 0 i = 0 := by simp [gapTerm, p, div_self hq.ne']
    have hr' : Tendsto (gapTerm τ · i) (𝓝[>] (0 : ℝ)) (𝓝 (gapTerm τ 0 i)) :=
      hr.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [hzero] using hr'
  simpa using hsum

private theorem valid_eventually : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), Valid x :=
  Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 16 by norm_num)

/-- The gap diverges while the marginals remain fixed. -/
theorem family_gap_tendsto_atTop (t : ℝ) (τ : Bit → ℝ)
    (hτ : ∀ i, 0 < τ i) (hτsum : ∑ i, τ i = 1) :
    Tendsto (fun x : ℝ =>
      reverseCMI t (diagonalState τ hτ hτsum) (diagReal (p (x ^ 2))) -
        reverseCMI t (diagonalState τ hτ hτsum) (diagReal (p x)))
      (𝓝[>] (0 : ℝ)) atTop := by
  have hlog : Tendsto (fun x : ℝ => -Real.log x) (𝓝[>] 0) atTop :=
    tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero
  have hmain := Tendsto.const_mul_atTop (mul_pos (by norm_num : 0 < (3 : ℝ) / 16) (hτ 0)) hlog
  refine (Tendsto.atTop_add hmain (remainder_tendsto_zero τ)).congr' ?_
  filter_upwards [valid_eventually] with x hx
  rw [family_gap_formula t τ hτ hτsum hx, ← Finset.sum_erase_add
    Finset.univ (gapTerm τ x) (Finset.mem_univ origin), gapTerm_origin τ hx.1]
  exact add_comm _ _

private theorem distanceFormula_tendsto :
    Tendsto (fun x : ℝ => 4 * (x - x ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : ContinuousAt (fun x : ℝ => 4 * (x - x ^ 2)) 0 := by fun_prop
    have h' : Tendsto (fun x : ℝ => 4 * (x - x ^ 2)) (𝓝[>] (0 : ℝ))
        (𝓝 (4 * ((0 : ℝ) - 0 ^ 2))) := h.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h'
  · exact valid_eventually.mono fun _ h => distanceFormula_pos h

/-- The faithful diagonal states on the fiber of the three fixed pair marginals. -/
def FixedMarginals (ρ : DensityState Triple) : Prop :=
  (toMatrix ρ).PosDef ∧
    (∃ p : Triple → ℝ, toMatrix ρ = diagReal p) ∧
    marginalAB (toMatrix ρ) = diagReal pairLaw ∧
    marginalAC (toMatrix ρ) = diagReal pairLaw ∧
    marginalBC (toMatrix ρ) = diagReal pairLaw

private theorem family_mem_fiber (x : ℝ) (hx : Valid x) : FixedMarginals (family x hx) :=
  ⟨diagReal_posDef _ (p_pos hx), ⟨p x, family_matrix x hx⟩,
    (family_fixed_marginals x hx).2⟩

/-- A right-zero trace-distance modulus on the entire faithful diagonal fiber. -/
def HasContinuityModulus (t : ℝ) (τ : DensityState Bit) : Prop :=
  ∃ ω : ℝ → ℝ, Tendsto ω (𝓝[>] 0) (𝓝 0) ∧
    ∀ ρ σ : DensityState Triple, FixedMarginals ρ → FixedMarginals σ →
      |reverseCMI t τ (toMatrix ρ) - reverseCMI t τ (toMatrix σ)| ≤
        ω (traceDistance ρ σ)

/-- Existence of a trace-distance modulus on the faithful fixed fiber
for some interpolation parameter and some faithful qubit reference. -/
def claim : Prop :=
  ∃ (t : ℝ) (τ : Bit → ℝ) (hτ : ∀ i, 0 < τ i) (hτsum : ∑ i, τ i = 1),
    HasContinuityModulus t (diagonalState τ hτ hτsum)

/-- Every faithful reference and every interpolation parameter fail to admit
a trace-distance modulus on this fixed pair-marginal fiber. -/
theorem result : ¬ claim := by
  rintro ⟨t, τ, hτ, hτsum, ω, hω, hbound⟩
  have hsmall : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), ω (4 * (x - x ^ 2)) < 1 :=
    (hω.comp distanceFormula_tendsto).eventually
      (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hlarge := (tendsto_atTop.1 (family_gap_tendsto_atTop t τ hτ hτsum)) (1 : ℝ)
  have he := valid_eventually.and (hsmall.and hlarge)
  obtain ⟨x, hx, hωx, hxgap⟩ := he.exists
  have h := hbound (family (x ^ 2) (valid_sq hx)) (family x hx)
    (family_mem_fiber _ (valid_sq hx)) (family_mem_fiber _ hx)
  rw [family_traceDistance hx, family_matrix, family_matrix] at h
  exact (not_lt_of_ge (hxgap.trans ((le_abs_self _).trans h))) hωx

/-- Positive normalized coordinates of a native faithful qubit reference in its eigenbasis. -/
def referenceInEigenbasis (τ : DensityState Bit)
    (hτ : (toMatrix τ).PosDef) :
    {a : Bit → ℝ // (∀ i, 0 < a i) ∧ (∑ i, a i) = 1 ∧
      toMatrix τ = Unitary.conjStarAlgAut ℂ _ hτ.isHermitian.eigenvectorUnitary (diagReal a)} := by
  have htrace : (toMatrix τ).trace = 1 := τ.property.2
  have hs := congrArg Complex.re hτ.isHermitian.trace_eq_sum_eigenvalues
  rw [htrace] at hs
  have hn : (∑ i, hτ.isHermitian.eigenvalues i) = 1 := by
    simpa only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re,
      Complex.one_re] using hs.symm
  have heigen : toMatrix τ = Unitary.conjStarAlgAut ℂ _ hτ.isHermitian.eigenvectorUnitary
      (diagReal hτ.isHermitian.eigenvalues) := by
    simpa only [diagReal, RCLike.ofReal_eq_complex_ofReal, Function.comp_def]
      using hτ.isHermitian.spectral_theorem
  exact ⟨hτ.isHermitian.eigenvalues, hτ.eigenvalues_pos, hn, heigen⟩

end
end D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoReverseGeodesicCMI
