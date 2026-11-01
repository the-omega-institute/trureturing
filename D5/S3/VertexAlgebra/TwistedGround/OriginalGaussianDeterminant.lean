/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual signed Gaussian finite determinant and pointwise cutoff limit. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Actual signed cycles and determinants on the original Gaussian operator. -/

noncomputable section
open scoped BigOperators Topology ENNReal
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant

open OriginalGaussianMatrix
open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open OriginalGaussianResolvent

private def unit1Entry (z : ℂ) (i j : ℕ) : ℂ :=
  matrixEntry z (i + 1) (j + 1)

def unit1Geo (ρ : ℝ) (a : ℕ × ℕ) : ℝ :=
  ρ ^ (a.1 + 1) * ρ ^ (a.2 + 1)

private def unit1GeoMass (ρ : ℝ) : ℝ := ∑' a : ℕ × ℕ, unit1Geo ρ a

private lemma unit1Geo_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (a : ℕ × ℕ) :
    0 ≤ unit1Geo ρ a := by
  exact mul_nonneg (pow_nonneg hρ _) (pow_nonneg hρ _)

lemma unit1Geo_summable {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Summable (unit1Geo ρ) := by
  have h : Summable (fun n : ℕ => ρ ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hρ hρ1)
  exact h.mul_of_nonneg h (fun _ => pow_nonneg hρ _) (fun _ => pow_nonneg hρ _)

private lemma unit1Entry_bound {ρ : ℝ} (hρ : 0 ≤ ρ) {z : ℂ}
    (hzρ : ‖z‖ ≤ ρ) (i j : ℕ) :
    ‖unit1Entry z i j‖ ≤ unit1Geo ρ (i, j) := by
  calc
    _ ≤ ‖z‖ ^ ((i + 1) + (j + 1)) :=
      entry_bound z (i + 1) (j + 1) (by omega) (by omega)
    _ ≤ ρ ^ ((i + 1) + (j + 1)) :=
      pow_le_pow_left₀ (norm_nonneg z) hzρ _
    _ = _ := pow_add ρ _ _

private lemma unit1Basis_norm (i : ℕ) : ‖basis i‖ = 1 := by
  simp [basis, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

private instance : Nontrivial H := by
  refine ⟨⟨basis 0, 0, ?_⟩⟩
  intro h
  have he := congrArg (fun x : H => x 0) h
  simpa [basis, lp.single_apply] using he

lemma unit1Power_coordinate_bound (T : H →L[ℂ] H) (p i j : ℕ) :
    ‖(T ^ p) (basis i) j‖ ≤ ‖T‖ ^ p := by
  calc
    _ ≤ ‖(T ^ p) (basis i)‖ :=
      lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) _ _
    _ ≤ ‖T ^ p‖ * ‖basis i‖ := (T ^ p).le_opNorm _
    _ ≤ ‖T‖ ^ p := by rw [unit1Basis_norm, mul_one]; exact norm_pow_le _ _

private def unit1Contract (z : ℂ) (p : ℕ) (a : ℕ × ℕ) : ℂ :=
  unit1Entry z a.1 a.2 * (operator z ^ p) (basis a.1) a.2

private lemma unit1Contract_bound {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {z : ℂ} (hzρ : ‖z‖ ≤ ρ) (p : ℕ) (a : ℕ × ℕ) :
    ‖unit1Contract z p a‖ ≤ unit1Geo ρ a * (ρ ^ 2) ^ p := by
  have hz : ‖z‖ < 1 := hzρ.trans_lt hρ1
  have hop : ‖operator z‖ ≤ ρ ^ 2 :=
    (operator_norm_le hz).trans (pow_le_pow_left₀ (norm_nonneg z) hzρ 2)
  rw [unit1Contract, norm_mul]
  exact mul_le_mul (unit1Entry_bound hρ hzρ _ _)
    ((unit1Power_coordinate_bound _ _ _ _).trans
      (pow_le_pow_left₀ (norm_nonneg _) hop p))
    (norm_nonneg _) (unit1Geo_nonneg hρ a)

private lemma unit1Contract_norm_summable {z : ℂ} (hz : ‖z‖ < 1) (p : ℕ) :
    Summable (fun a : ℕ × ℕ => ‖unit1Contract z p a‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (unit1Contract_bound (norm_nonneg z) hz le_rfl p)
    ((unit1Geo_summable (norm_nonneg z) hz).mul_right _)

private lemma unit1Contract_row_norm_summable {z : ℂ} (hz : ‖z‖ < 1)
    (p i : ℕ) : Summable (fun j : ℕ => ‖unit1Contract z p (i, j)‖) := by
  exact (unit1Contract_norm_summable hz p).comp_injective
    (fun _ _ h => congrArg Prod.snd h)

private lemma unit1Diagonal_expansion {z : ℂ} (hz : ‖z‖ < 1) (p i : ℕ) :
    (operator z ^ (p + 1)) (basis i) i =
      ∑' j : ℕ, unit1Contract z p (i, j) := by
  rw [pow_succ']
  exact operator_apply hz ((operator z ^ p) (basis i)) i

private lemma unit1Diagonal_norm_summable {z : ℂ} (hz : ‖z‖ < 1) (p : ℕ) :
    Summable (fun i : ℕ => ‖(operator z ^ (p + 1)) (basis i) i‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => ?_) (unit1Contract_norm_summable hz p).prod
  rw [unit1Diagonal_expansion hz]
  exact norm_tsum_le_tsum_norm (unit1Contract_row_norm_summable hz p i)

private lemma unit1Diagonal_tsum {z : ℂ} (hz : ‖z‖ < 1) (p : ℕ) :
    (∑' i : ℕ, (operator z ^ (p + 1)) (basis i) i) =
      ∑' a : ℕ × ℕ, unit1Contract z p a := by
  simp_rw [unit1Diagonal_expansion hz]
  exact (unit1Contract_norm_summable hz p).of_norm.tsum_prod.symm

/-- Literal recursively summed paths; the zero-length path is the identity kernel. -/
private def unit1Walk (z : ℂ) : ℕ → ℕ → ℕ → ℂ
  | 0, i, j => if i = j then 1 else 0
  | p + 1, i, j => ∑' m : ℕ, unit1Entry z i m * unit1Walk z p m j

private lemma unit1Walk_eq_power {z : ℂ} (hz : ‖z‖ < 1) (p i j : ℕ) :
    unit1Walk z p i j = (operator z ^ p) (basis j) i := by
  induction p generalizing i with
  | zero => simp [unit1Walk, basis, lp.single_apply, Pi.single_apply, eq_comm]
  | succ p ih =>
    rw [unit1Walk, pow_succ']
    change (∑' m : ℕ, unit1Entry z i m * unit1Walk z p m j) =
      operator z ((operator z ^ p) (basis j)) i
    simpa only [ih, unit1Entry] using
      (operator_apply hz ((operator z ^ p) (basis j)) i).symm

private lemma unit1Walk_row_norm_summable {z : ℂ} (hz : ‖z‖ < 1)
    (p i j : ℕ) :
    Summable (fun m : ℕ => ‖unit1Entry z i m * unit1Walk z p m j‖) := by
  have hg : Summable (fun m : ℕ => ‖z‖ ^ (m + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg z) hz)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => ?_) (hg.mul_left (‖z‖ ^ (i + 1) * ‖operator z‖ ^ p))
  rw [norm_mul, unit1Walk_eq_power hz]
  calc
    _ ≤ unit1Geo ‖z‖ (i, m) * ‖operator z‖ ^ p :=
      mul_le_mul (unit1Entry_bound (norm_nonneg z) le_rfl i m)
        (unit1Power_coordinate_bound _ _ _ _)
        (norm_nonneg _) (unit1Geo_nonneg (norm_nonneg z) _)
    _ = _ := by dsimp [unit1Geo]; ring

/-- Even closed walks, lengths 2,4,6,..., with original signed complex entries. -/
private def cycleTrace (z : ℂ) (k : ℕ) : ℂ :=
  ∑' i : ℕ, unit1Walk z (2 * (k + 1)) i i

private lemma cycleTrace_contract {z : ℂ} (hz : ‖z‖ < 1) (k : ℕ) :
    cycleTrace z k = ∑' a : ℕ × ℕ, unit1Contract z (2 * k + 1) a := by
  unfold cycleTrace
  simp_rw [unit1Walk_eq_power hz]
  have he : (2 * k + 1) + 1 = 2 * (k + 1) := by omega
  simpa only [he] using unit1Diagonal_tsum hz (2 * k + 1)

private lemma cycleTrace_bound {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {z : ℂ} (hzρ : ‖z‖ ≤ ρ) (k : ℕ) :
    ‖cycleTrace z k‖ ≤ unit1GeoMass ρ * (ρ ^ 2) ^ (2 * k + 1) := by
  rw [cycleTrace_contract (hzρ.trans_lt hρ1)]
  exact tsum_of_norm_bounded
    (by simpa only [unit1GeoMass, tsum_mul_right] using
      ((unit1Geo_summable hρ hρ1).mul_right ((ρ ^ 2) ^ (2 * k + 1))).hasSum)
    (unit1Contract_bound hρ hρ1 hzρ _)

private def unit1Majorant (ρ : ℝ) (k : ℕ) : ℝ :=
  unit1GeoMass ρ * (ρ ^ 2) ^ (2 * k + 1)

lemma unit1Majorant_summable {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Summable (unit1Majorant ρ) := by
  have hq : ρ ^ 4 < 1 := pow_lt_one₀ hρ hρ1 (by norm_num : (4 : ℕ) ≠ 0)
  convert (summable_geometric_of_lt_one (by positivity : 0 ≤ ρ ^ 4) hq).mul_left
    (unit1GeoMass ρ * ρ ^ 2) using 1
  ext k
  dsimp [unit1Majorant]
  rw [pow_add, pow_one, pow_mul]
  have he : (ρ ^ 2) ^ 2 = ρ ^ 4 := by ring
  rw [he]
  ring

/-- Exponent of the absolutely convergent actual even closed-cycle series. -/
def gaussianLogDet (z : ℂ) : ℂ := -∑' k : ℕ, cycleTrace z k / (k + 1 : ℂ)

/-- The exponential of the original signed Gaussian closed-cycle logarithm. -/
def gaussianDet (z : ℂ) : ℂ := Complex.exp (gaussianLogDet z)

/-- The literal finite matrix square, including its empty determinant. -/
private def unit1DetN (N : ℕ) (z : ℂ) : ℂ := Matrix.det (1 - finiteSection N z ^ 2)

/- Absolute paths use the norm of EACH original edge before any summation.
   This is stronger than summability of the already-contracted trace. -/

private def unit1AbsWalk (z : ℂ) : ℕ → ℕ → ℕ → ℝ
  | 0, i, j => if i = j then 1 else 0
  | p + 1, i, j => ∑' m : ℕ, ‖unit1Entry z i m‖ * unit1AbsWalk z p m j

private lemma unit1AbsWalk_nonneg (z : ℂ) (p i j : ℕ) :
    0 ≤ unit1AbsWalk z p i j := by
  induction p generalizing i with
  | zero => simp only [unit1AbsWalk]; split_ifs <;> norm_num
  | succ p ih =>
    exact tsum_nonneg (fun m => mul_nonneg (norm_nonneg _) (ih m))

private lemma unit1Entry_abs_realization (z : ℂ) (i j : ℕ) :
    unit1Entry (-(‖z‖ : ℂ)) i j = (‖unit1Entry z i j‖ : ℂ) := by
  let s := i + 1
  let t := j + 1
  have hsign : (-1 : ℂ) ^ s * (-1 : ℂ) ^ t * (-(‖z‖ : ℂ)) ^ (s + t) =
      (‖z‖ : ℂ) ^ (s + t) := by
    have hn : (-(‖z‖ : ℂ)) = (-1 : ℂ) * (‖z‖ : ℂ) := by ring
    rw [← pow_add, hn, mul_pow, ← mul_assoc, ← mul_pow]
    norm_num
  change matrixEntry (-(‖z‖ : ℂ)) s t = (‖matrixEntry z s t‖ : ℂ)
  rw [entry_sqrt _ _ _ (by dsimp [s]; omega) (by dsimp [t]; omega),
    matrixEntry_norm _ _ _ (by dsimp [s]; omega) (by dsimp [t]; omega),
    halfBinomial_eq_signed_centralWeight, halfBinomial_eq_signed_centralWeight]
  push_cast
  calc
    _ = ((Real.sqrt (s : ℝ) : ℂ) * (Real.sqrt (t : ℝ) : ℂ) *
        (centralWeight s : ℂ) * (centralWeight t : ℂ)) *
        ((-1 : ℂ) ^ s * (-1 : ℂ) ^ t * (-(‖z‖ : ℂ)) ^ (s + t)) /
        ((s : ℂ) + t) := by ring
    _ = _ := by rw [hsign]

private lemma unit1AbsWalk_realization {z : ℂ} (hz : ‖z‖ < 1) (p i j : ℕ) :
    (unit1AbsWalk z p i j : ℂ) = unit1Walk (-(‖z‖ : ℂ)) p i j := by
  induction p generalizing i with
  | zero =>
    by_cases hij : i = j <;> simp [unit1AbsWalk, unit1Walk, hij]
  | succ p ih =>
    rw [unit1AbsWalk, unit1Walk, Complex.ofReal_tsum]
    apply tsum_congr
    intro m
    rw [Complex.ofReal_mul, ih m, unit1Entry_abs_realization]

private lemma unit1AbsWalk_le {z : ℂ} (hz : ‖z‖ < 1) (p i j : ℕ) :
    unit1AbsWalk z p i j ≤ (‖z‖ ^ 2) ^ p := by
  have hw : ‖(-(‖z‖ : ℂ))‖ = ‖z‖ := by simp
  have h := unit1Power_coordinate_bound (operator (-(‖z‖ : ℂ))) p j i
  rw [← unit1Walk_eq_power (by simpa only [hw] using hz),
    ← unit1AbsWalk_realization hz, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (unit1AbsWalk_nonneg _ _ _ _)] at h
  exact h.trans (pow_le_pow_left₀ (norm_nonneg _)
    (by simpa only [hw] using (operator_norm_le (z := -(‖z‖ : ℂ))
      (by simpa only [hw] using hz))) p)

private lemma unit1AbsWalk_row_summable {z : ℂ} (hz : ‖z‖ < 1) (p i j : ℕ) :
    Summable (fun m : ℕ => ‖unit1Entry z i m‖ * unit1AbsWalk z p m j) := by
  have hg : Summable (fun m : ℕ => ‖z‖ ^ (m + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg z) hz)
  apply Summable.of_nonneg_of_le
    (fun m => mul_nonneg (norm_nonneg _) (unit1AbsWalk_nonneg _ _ _ _))
    (fun m => ?_) (hg.mul_left (‖z‖ ^ (i + 1) * (‖z‖ ^ 2) ^ p))
  calc
    _ ≤ unit1Geo ‖z‖ (i, m) * (‖z‖ ^ 2) ^ p :=
      mul_le_mul (unit1Entry_bound (norm_nonneg z) le_rfl i m)
        (unit1AbsWalk_le hz p m j) (unit1AbsWalk_nonneg _ _ _ _)
        (unit1Geo_nonneg (norm_nonneg z) _)
    _ = _ := by dsimp [unit1Geo]; ring

private lemma unit1Walk_norm_le_abs {z : ℂ} (hz : ‖z‖ < 1) (p i j : ℕ) :
    ‖unit1Walk z p i j‖ ≤ unit1AbsWalk z p i j := by
  induction p generalizing i with
  | zero => simp only [unit1Walk, unit1AbsWalk]; split_ifs <;> simp
  | succ p ih =>
    rw [unit1Walk, unit1AbsWalk]
    exact (norm_tsum_le_tsum_norm (unit1Walk_row_norm_summable hz p i j)).trans
      ((unit1Walk_row_norm_summable hz p i j).tsum_le_tsum
        (fun m => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (ih m) (norm_nonneg _))
        (unit1AbsWalk_row_summable hz p i j))

private lemma unit1AbsClosed_summable {z : ℂ} (hz : ‖z‖ < 1) (p : ℕ) :
    Summable (fun i : ℕ => unit1AbsWalk z (p + 1) i i) := by
  have hw : ‖(-(‖z‖ : ℂ))‖ < 1 := by simpa using hz
  convert unit1Diagonal_norm_summable hw p using 1
  ext i
  rw [← unit1Walk_eq_power hw, ← unit1AbsWalk_realization hz,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (unit1AbsWalk_nonneg _ _ _ _)]

private lemma unit1AbsClosed_bound {z : ℂ} (hz : ‖z‖ < 1) (k : ℕ) :
    (∑' i : ℕ, unit1AbsWalk z (2 * (k + 1)) i i) ≤ unit1Majorant ‖z‖ k := by
  have hw : ‖(-(‖z‖ : ℂ))‖ < 1 := by simpa using hz
  have h := cycleTrace_bound (norm_nonneg z) hz
    (z := -(‖z‖ : ℂ)) (by simp) k
  have he : cycleTrace (-(‖z‖ : ℂ)) k =
      ((∑' i : ℕ, unit1AbsWalk z (2 * (k + 1)) i i) : ℝ) := by
    rw [cycleTrace, Complex.ofReal_tsum]
    exact tsum_congr (fun i => (unit1AbsWalk_realization hz _ i i).symm)
  rw [he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg (fun i => unit1AbsWalk_nonneg _ _ _ _))] at h
  exact h

/-- The nested absolute sums of all actual even closed walks are summable in length.
The absolute values are taken on edges before summing internal vertices. -/
private lemma unit1_absolute_cycles_summable {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ =>
      (∑' i : ℕ, unit1AbsWalk z (2 * (k + 1)) i i) / (k + 1 : ℝ)) := by
  apply Summable.of_nonneg_of_le
    (fun k => div_nonneg (tsum_nonneg (fun i => unit1AbsWalk_nonneg _ _ _ _)) (by positivity))
    (fun k => ?_) (unit1Majorant_summable (norm_nonneg z) hz)
  exact (div_le_self (tsum_nonneg (fun i => unit1AbsWalk_nonneg _ _ _ _))
    (by linarith [Nat.cast_nonneg (α := ℝ) k] : 1 ≤ (k + 1 : ℝ))).trans (unit1AbsClosed_bound hz k)

private lemma unit1CycleLog_norm_summable {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => ‖cycleTrace z k / (k + 1 : ℂ)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => ?_) (unit1_absolute_cycles_summable hz)
  rw [norm_div, show ‖(k + 1 : ℂ)‖ = (k + 1 : ℝ) by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (k + 1)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact tsum_of_norm_bounded
    (by simpa only [show (2 * k + 1) + 1 = 2 * (k + 1) by omega] using
      (unit1AbsClosed_summable hz (2 * k + 1)).hasSum)
    (fun i => unit1Walk_norm_le_abs hz _ i i)

private def unit1EntryN (N : ℕ) (z : ℂ) (i j : ℕ) : ℂ :=
  if i < N ∧ j < N then unit1Entry z i j else 0

private def unit1ContractN (N : ℕ) (z : ℂ) (p : ℕ) (a : ℕ × ℕ) : ℂ :=
  unit1EntryN N z a.1 a.2 * (sectionOp N z ^ p) (basis a.1) a.2

private lemma unit1ContractN_bound {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {z : ℂ} (hzρ : ‖z‖ ≤ ρ) (N p : ℕ) (a : ℕ × ℕ) :
    ‖unit1ContractN N z p a‖ ≤ unit1Geo ρ a * (ρ ^ 2) ^ p := by
  have hz : ‖z‖ < 1 := hzρ.trans_lt hρ1
  have hop : ‖sectionOp N z‖ ≤ ρ ^ 2 :=
    (sectionOp_norm_le N hz).trans (pow_le_pow_left₀ (norm_nonneg z) hzρ 2)
  unfold unit1ContractN unit1EntryN
  split_ifs with h
  · rw [norm_mul]
    exact mul_le_mul (unit1Entry_bound hρ hzρ _ _)
      ((unit1Power_coordinate_bound _ _ _ _).trans
        (pow_le_pow_left₀ (norm_nonneg _) hop p))
      (norm_nonneg _) (unit1Geo_nonneg hρ a)
  · simpa only [zero_mul, norm_zero] using
      mul_nonneg (unit1Geo_nonneg hρ a) (pow_nonneg (by positivity : 0 ≤ ρ ^ 2) p)

private lemma unit1Section_apply_fin (N : ℕ) (z : ℂ) (x : H) (i : Fin N) :
    sectionOp N z x i.val = ∑ j : Fin N, finiteSection N z i j * x j.val := by
  rw [sectionOp_factorization]
  change zeroExtend N
    (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) (finiteSection N z)
      (WithLp.toLp 2 (fun j : Fin N => x j.val))) i.val = _
  rw [zeroExtend_apply, dif_pos i.isLt]
  rfl

lemma unit1Section_power_coordinate (N : ℕ) (z : ℂ)
    (p : ℕ) (i j : Fin N) :
    (sectionOp N z ^ p) (basis i.val) j.val = (finiteSection N z ^ p) j i := by
  induction p generalizing j with
  | zero =>
    simp [basis, lp.single_apply, Pi.single_apply, Matrix.one_apply, Fin.ext_iff, eq_comm]
  | succ p ih =>
    rw [pow_succ', pow_succ']
    change sectionOp N z ((sectionOp N z ^ p) (basis i.val)) j.val = _
    rw [unit1Section_apply_fin, Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun m _ => congrArg (fun t => finiteSection N z j m * t) (ih m))

private lemma unit1ContractN_tsum (N : ℕ) (z : ℂ) (p : ℕ) :
    (∑' a : ℕ × ℕ, unit1ContractN N z p a) =
      Matrix.trace (finiteSection N z ^ (p + 1)) := by
  classical
  have hs : ∀ a ∉ ((Finset.range N) ×ˢ (Finset.range N)),
      unit1ContractN N z p a = 0 := by
    intro a ha
    have hn : ¬(a.1 < N ∧ a.2 < N) := by simpa only [Finset.mem_product, Finset.mem_range] using ha
    simp [unit1ContractN, unit1EntryN, hn]
  rw [tsum_eq_sum hs, Finset.sum_product]
  rw [Finset.sum_range]
  simp_rw [Finset.sum_range]
  rw [pow_succ']
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  change (∑ j : Fin N, unit1ContractN N z p (i.val, j.val)) =
    (finiteSection N z * finiteSection N z ^ p) i i
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp only [unit1ContractN, unit1EntryN, i.isLt, j.isLt, and_self, ite_true,
    unit1Entry, unit1Section_power_coordinate]
  rfl

/-- The logarithm-series cutoff uses the literal original finite matrix powers. -/
def finiteLog (N : ℕ) (z : ℂ) : ℂ :=
  -∑' k : ℕ, Matrix.trace (finiteSection N z ^ (2 * (k + 1))) / (k + 1 : ℂ)

private lemma unit1FiniteTrace_bound {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {z : ℂ} (hzρ : ‖z‖ ≤ ρ) (N k : ℕ) :
    ‖Matrix.trace (finiteSection N z ^ (2 * (k + 1)))‖ ≤ unit1Majorant ρ k := by
  have he : (2 * k + 1) + 1 = 2 * (k + 1) := by omega
  rw [← he, ← unit1ContractN_tsum]
  exact tsum_of_norm_bounded
    (by simpa only [unit1Majorant, unit1GeoMass, tsum_mul_right] using
      ((unit1Geo_summable hρ hρ1).mul_right ((ρ ^ 2) ^ (2 * k + 1))).hasSum)
    (unit1ContractN_bound hρ hρ1 hzρ N _)

lemma finiteLogTerm_bound {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {z : ℂ} (hzρ : ‖z‖ ≤ ρ) (N k : ℕ) :
    ‖Matrix.trace (finiteSection N z ^ (2 * (k + 1))) / (k + 1 : ℂ)‖ ≤
      unit1Majorant ρ k := by
  rw [norm_div]
  have hk : 1 ≤ ‖(k + 1 : ℂ)‖ := by
    rw [show (k + 1 : ℂ) = ((k + 1 : ℕ) : ℂ) by norm_cast, Complex.norm_natCast]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  exact (div_le_self (norm_nonneg _) hk).trans (unit1FiniteTrace_bound hρ hρ1 hzρ N k)

private lemma unit1ContractN_tendsto {z : ℂ} (hz : ‖z‖ < 1) (p : ℕ) (a : ℕ × ℕ) :
    Tendsto (fun N : ℕ => unit1ContractN N z p a) atTop
      (𝓝 (unit1Contract z p a)) := by
  have hc : Continuous (fun T : H →L[ℂ] H => (T ^ p) (basis a.1) a.2) :=
    ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 a.2).comp
      (ContinuousLinearMap.apply ℂ H (basis a.1))).continuous.comp (continuous_id.pow p)
  have ht := (tendsto_const_nhds (x := unit1Entry z a.1 a.2)).mul
    (hc.continuousAt.tendsto.comp (sectionOp_tendsto hz))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (max a.1 a.2 + 1)] with N hN
  have hi : a.1 < N := by omega
  have hj : a.2 < N := by omega
  simp only [unit1ContractN, unit1EntryN, hi, hj, and_self, ite_true, Function.comp_def]

private lemma unit1FiniteTrace_tendsto {z : ℂ} (hz : ‖z‖ < 1) (k : ℕ) :
    Tendsto (fun N : ℕ => Matrix.trace (finiteSection N z ^ (2 * (k + 1))))
      atTop (𝓝 (cycleTrace z k)) := by
  have he : (2 * k + 1) + 1 = 2 * (k + 1) := by omega
  rw [cycleTrace_contract hz]
  simp_rw [← he, ← unit1ContractN_tsum]
  exact tendsto_tsum_of_dominated_convergence
    ((unit1Geo_summable (norm_nonneg z) hz).mul_right ((‖z‖ ^ 2) ^ (2 * k + 1)))
    (unit1ContractN_tendsto hz _)
    (Filter.Eventually.of_forall (fun N a =>
      unit1ContractN_bound (norm_nonneg z) hz le_rfl N _ a))

lemma finiteLog_tendsto {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun N : ℕ => finiteLog N z) atTop (𝓝 (gaussianLogDet z)) := by
  exact (tendsto_tsum_of_dominated_convergence
    (unit1Majorant_summable (norm_nonneg z) hz)
    (fun k => (unit1FiniteTrace_tendsto hz k).div_const (k + 1 : ℂ))
    (Filter.Eventually.of_forall (fun N k =>
      finiteLogTerm_bound (norm_nonneg z) hz le_rfl N k))).neg


open Metric
open scoped ComplexConjugate Matrix.Norms.L2Operator

private lemma unit1Trace_conj (N : ℕ)
    (U : Matrix.unitaryGroup (Fin N) ℂ) (B : Matrix (Fin N) (Fin N) ℂ) :
    Matrix.trace (Unitary.conjStarAlgAut ℂ _ U B) = Matrix.trace B := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul]

private lemma unit1Det_conj (N : ℕ)
    (U : Matrix.unitaryGroup (Fin N) ℂ) (B : Matrix (Fin N) (Fin N) ℂ) :
    Matrix.det (Unitary.conjStarAlgAut ℂ _ U B) = Matrix.det B := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul_right_comm,
    ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.one_mul]

/-- One chosen spectral conjugation works in EVERY power. -/
private lemma unit1Spectral_power_trace {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) (p : ℕ) :
    Matrix.trace (A ^ p) = ∑ i : Fin N, (hA.eigenvalues i : ℂ) ^ p := by
  classical
  let U := hA.eigenvectorUnitary
  let C := Unitary.conjStarAlgAut ℂ (Matrix (Fin N) (Fin N) ℂ) U
  let D : Matrix (Fin N) (Fin N) ℂ :=
    Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))
  have hs : A = C D := hA.spectral_theorem
  have hp : A ^ p = C (D ^ p) := by rw [map_pow, ← hs]
  rw [hp, unit1Trace_conj, Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

private lemma unit1Spectral_det_one_sub_sq {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    Matrix.det (1 - A ^ 2) =
      ∏ i : Fin N, (1 - (hA.eigenvalues i : ℂ) ^ 2) := by
  classical
  let U := hA.eigenvectorUnitary
  let C := Unitary.conjStarAlgAut ℂ (Matrix (Fin N) (Fin N) ℂ) U
  let D : Matrix (Fin N) (Fin N) ℂ :=
    Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))
  have hs : A = C D := hA.spectral_theorem
  have hd : Matrix.diagonal (fun i => 1 - (hA.eigenvalues i : ℂ) ^ 2) =
      1 - D ^ 2 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Matrix.diagonal_pow]
    · simp [D, Matrix.diagonal_pow, Matrix.one_apply, Matrix.diagonal_apply, hij]
  have he : 1 - A ^ 2 =
      C (Matrix.diagonal (fun i => 1 - (hA.eigenvalues i : ℂ) ^ 2)) := by
    rw [hd, map_sub, map_one, map_pow, ← hs]
  rw [he, unit1Det_conj, Matrix.det_diagonal]

private lemma unit1Finite_eigen_sq_small (N : ℕ) (t : ℝ)
    (ht : ‖(t : ℂ)‖ < 1) (i : Fin N) :
    ‖((finiteSection_radial_hermitian N t).eigenvalues i : ℂ) ^ 2‖ < 1 := by
  classical
  -- A concrete i supplies Nonempty even though N=0 is allowed in the endpoint.
  letI : Nonempty (Fin N) := ⟨i⟩
  let A := finiteSection N (t : ℂ)
  let hA := finiteSection_radial_hermitian N t
  have hmem : (hA.eigenvalues i : ℂ) ∈ spectrum ℂ A := by
    rw [hA.spectrum_eq_image_range]
    exact ⟨hA.eigenvalues i, ⟨i, rfl⟩, rfl⟩
  have hb : ‖(hA.eigenvalues i : ℂ)‖ ≤ ‖(t : ℂ)‖ ^ 2 := by
    calc
      _ ≤ ‖A‖ := spectrum.norm_le_norm_of_mem hmem
      _ = ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) A‖ :=
        (Matrix.l2_opNorm_toEuclideanCLM A).symm
      _ ≤ _ := finiteSection_opNorm_le N (t : ℂ) ht
  have he : ‖(hA.eigenvalues i : ℂ)‖ < 1 :=
    hb.trans_lt (pow_lt_one₀ (norm_nonneg _) ht (by norm_num : (2 : ℕ) ≠ 0))
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) he (by norm_num : (2 : ℕ) ≠ 0)

private lemma unit1FiniteDet_real (N : ℕ) (t : ℝ) (ht : ‖(t : ℂ)‖ < 1) :
    unit1DetN N (t : ℂ) = Complex.exp (finiteLog N (t : ℂ)) := by
  classical
  let hA := finiteSection_radial_hermitian N t
  let ev : Fin N → ℂ := fun i => (hA.eigenvalues i : ℂ)
  have hsmall (i : Fin N) : ‖ev i ^ 2‖ < 1 := unit1Finite_eigen_sq_small N t ht i
  have hscalar (i : Fin N) :
      HasSum (fun k : ℕ => ev i ^ (2 * (k + 1)) / (k + 1 : ℂ))
        (-Complex.log (1 - ev i ^ 2)) := by
    simpa only [pow_mul] using Complex.hasSum_taylorSeries_neg_log' (hsmall i)
  -- hasSum_sum is the to_additive-generated finite-sum theorem, not a
  -- rearrangement of an uncontrolled infinite eigenvalue family.
  have hsum : HasSum
      (fun k : ℕ => Matrix.trace (finiteSection N (t : ℂ) ^ (2 * (k + 1))) /
        (k + 1 : ℂ)) (∑ i : Fin N, -Complex.log (1 - ev i ^ 2)) := by
    convert (hasSum_sum (s := Finset.univ) (fun i _ => hscalar i)) using 1
    ext k
    rw [unit1Spectral_power_trace hA]
    simp only [ev, div_eq_mul_inv, Finset.sum_mul]
  have hlog : finiteLog N (t : ℂ) =
      ∑ i : Fin N, Complex.log (1 - ev i ^ 2) := by
    simp only [finiteLog, hsum.tsum_eq, Finset.sum_neg_distrib, neg_neg]
  have hne (i : Fin N) : 1 - ev i ^ 2 ≠ 0 := by
    intro h
    have he : ev i ^ 2 = 1 := (sub_eq_zero.mp h).symm
    have hc := hsmall i
    rw [he, norm_one] at hc
    exact (lt_irrefl (1 : ℝ)) hc
  rw [hlog, Complex.exp_sum]
  change Matrix.det (1 - finiteSection N (t : ℂ) ^ 2) = _
  rw [unit1Spectral_det_one_sub_sq hA]
  exact Finset.prod_congr rfl (fun i _ => (Complex.exp_log (hne i)).symm)

/-- Entrywise polynomial reasoning avoids any unverified matrix-holomorphy API. -/
private lemma unit1FiniteEntry_diff (N : ℕ) (i j : Fin N) :
    Differentiable ℂ (fun z : ℂ => finiteSection N z i j) := by
  dsimp [finiteSection, matrixEntry]
  fun_prop

private lemma unit1FinitePowerEntry_diff (N p : ℕ) (i j : Fin N) :
    Differentiable ℂ (fun z : ℂ => (finiteSection N z ^ p) i j) := by
  induction p generalizing i j with
  | zero =>
      simp only [pow_zero]
      exact differentiable_const _
  | succ p ih =>
      simp only [pow_succ, Matrix.mul_apply]
      exact Differentiable.fun_sum (fun m _ =>
        (ih i m).mul (unit1FiniteEntry_diff N m j))

private lemma finiteLogTerm_diff (N k : ℕ) :
    Differentiable ℂ (fun z : ℂ =>
      Matrix.trace (finiteSection N z ^ (2 * (k + 1))) / (k + 1 : ℂ)) := by
  unfold Matrix.trace
  exact (Differentiable.fun_sum (fun i _ =>
    unit1FinitePowerEntry_diff N (2 * (k + 1)) i i)).div_const _

private lemma unit1FiniteDet_diff (N : ℕ) : Differentiable ℂ (unit1DetN N) := by
  classical
  unfold unit1DetN
  simp only [Matrix.det_apply']
  apply Differentiable.fun_sum
  intro σ _
  apply Differentiable.const_mul
  apply Differentiable.fun_finsetProd
  intro i _
  change Differentiable ℂ (fun z : ℂ =>
    (1 : Matrix (Fin N) (Fin N) ℂ) (σ i) i - (finiteSection N z ^ 2) (σ i) i)
  exact (differentiable_const _).sub (unit1FinitePowerEntry_diff N 2 (σ i) i)

/-- Holomorphy is local in z; the actual trace bound pays the M-test on
each smaller disk for this fixed finite N. This is NOT spatial uniformity. -/
private lemma finiteLog_diff (N : ℕ) :
    DifferentiableOn ℂ (finiteLog N) (ball (0 : ℂ) 1) := by
  intro z hz
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  obtain ⟨ρ, hzρ, hρ1⟩ := exists_between hz1
  have hρ : 0 ≤ ρ := (norm_nonneg z).trans hzρ.le
  have hd : DifferentiableOn ℂ
      (fun w : ℂ => ∑' k : ℕ,
        Matrix.trace (finiteSection N w ^ (2 * (k + 1))) / (k + 1 : ℂ))
      (ball (0 : ℂ) ρ) := by
    apply Complex.differentiableOn_tsum_of_summable_norm
      (unit1Majorant_summable hρ hρ1)
      (fun k => (finiteLogTerm_diff N k).differentiableOn) isOpen_ball
    intro k w hw
    exact finiteLogTerm_bound hρ hρ1 (mem_ball_zero_iff.mp hw).le N k
  exact ((hd.neg).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hzρ))).differentiableWithinAt

private lemma unit1Finite_real_accum (N : ℕ) :
    ∃ᶠ z in 𝓝[≠] (0 : ℂ),
      unit1DetN N z = Complex.exp (finiteLog N z) := by
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℂ) + 1)) atTop (𝓝 (0 : ℂ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hne (n : ℕ) : (1 / ((n : ℂ) + 1)) ≠ 0 := by
    apply div_ne_zero one_ne_zero
    exact_mod_cast Nat.succ_ne_zero n
  have hp : Tendsto (fun n : ℕ => 1 / ((n : ℂ) + 1)) atTop (𝓝[≠] (0 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall (fun n => by simpa using hne n)⟩
  apply hp.frequently
  apply Filter.Eventually.frequently
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (1 / ((n : ℝ) + 1)) := by positivity
  have hsmall : ‖((1 / ((n : ℝ) + 1) : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    exact (div_lt_one (by positivity : 0 < (n : ℝ) + 1)).mpr (by linarith)
  have hcast : ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) = 1 / ((n : ℂ) + 1) := by
    push_cast
    rfl
  simpa only [hcast] using unit1FiniteDet_real N (1 / ((n : ℝ) + 1)) hsmall

/-- The literal original finite determinant equals its actual even trace-log
exponential, at EVERY complex argument in the unit disk, including N=0. -/
theorem finite_determinant_identity (N : ℕ) (z : ℂ) (hz : ‖z‖ < 1) :
    Matrix.det (1 - finiteSection N z ^ 2) = Complex.exp (finiteLog N z) := by
  change unit1DetN N z = _
  have hd : AnalyticOnNhd ℂ (unit1DetN N) (ball (0 : ℂ) 1) :=
    (unit1FiniteDet_diff N).differentiableOn.analyticOnNhd isOpen_ball
  have he : AnalyticOnNhd ℂ (fun w => Complex.exp (finiteLog N w))
      (ball (0 : ℂ) 1) :=
    (finiteLog_diff N).cexp.analyticOnNhd isOpen_ball
  exact hd.eqOn_of_preconnected_of_frequently_eq he isPreconnected_ball
    (by simp) (unit1Finite_real_accum N) (mem_ball_zero_iff.mpr hz)


/-- The literal finite section is squared after cutoff; its determinant converges
at every complex argument of the open unit disk. -/
theorem finite_determinants_tendsto {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun N : ℕ => Matrix.det (1 - finiteSection N z ^ 2))
      atTop (𝓝 (gaussianDet z)) := by
  simp_rw [finite_determinant_identity _ z hz]
  exact Complex.continuous_exp.continuousAt.tendsto.comp (finiteLog_tendsto hz)

/- Uniform analytic control of the recursively summed original signed walks.
The geometric bounds below are uniform on each smaller complex disk. -/

private lemma unit1Entry_diff (i j : ℕ) :
    Differentiable ℂ (fun z : ℂ => unit1Entry z i j) := by
  dsimp [unit1Entry, matrixEntry]
  fun_prop

private lemma unit1WalkTerm_bound {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {z : ℂ} (hzρ : ‖z‖ ≤ ρ) (p i j m : ℕ) :
    ‖unit1Entry z i m * unit1Walk z p m j‖ ≤
      ρ ^ (i + 1) * ρ ^ (m + 1) * (ρ ^ 2) ^ p := by
  have hz : ‖z‖ < 1 := hzρ.trans_lt hρ1
  have hop : ‖operator z‖ ≤ ρ ^ 2 :=
    (operator_norm_le hz).trans (pow_le_pow_left₀ (norm_nonneg z) hzρ 2)
  rw [norm_mul, unit1Walk_eq_power hz]
  exact mul_le_mul (unit1Entry_bound hρ hzρ i m)
    ((unit1Power_coordinate_bound (operator z) p j m).trans
      (pow_le_pow_left₀ (norm_nonneg _) hop p))
    (norm_nonneg _) (unit1Geo_nonneg hρ (i, m))

private lemma unit1Walk_succ_bound {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {z : ℂ} (hzρ : ‖z‖ ≤ ρ) (p i j : ℕ) :
    ‖unit1Walk z (p + 1) i j‖ ≤
      ρ ^ (i + 1) * (∑' m : ℕ, ρ ^ (m + 1)) * (ρ ^ 2) ^ p := by
  have hg : Summable (fun m : ℕ => ρ ^ (m + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hρ hρ1)
  rw [unit1Walk]
  exact tsum_of_norm_bounded
    (by simpa only [tsum_mul_left, tsum_mul_right] using
      (((hg.mul_left (ρ ^ (i + 1))).mul_right ((ρ ^ 2) ^ p)).hasSum))
    (fun m => unit1WalkTerm_bound hρ hρ1 hzρ p i j m)

private lemma unit1Walk_diff (p i j : ℕ) :
    DifferentiableOn ℂ (fun z : ℂ => unit1Walk z p i j) (ball (0 : ℂ) 1) := by
  induction p generalizing i with
  | zero =>
    change DifferentiableOn ℂ (fun _ : ℂ => if i = j then 1 else 0) _
    exact (differentiable_const _).differentiableOn
  | succ p ih =>
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    obtain ⟨ρ, hzρ, hρ1⟩ := exists_between hz1
    have hρ : 0 ≤ ρ := (norm_nonneg z).trans hzρ.le
    have hg : Summable (fun m : ℕ => ρ ^ (m + 1)) :=
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hρ hρ1)
    have hd : DifferentiableOn ℂ
        (fun w : ℂ => ∑' m : ℕ, unit1Entry w i m * unit1Walk w p m j)
        (ball (0 : ℂ) ρ) := by
      apply Complex.differentiableOn_tsum_of_summable_norm
        ((hg.mul_left (ρ ^ (i + 1))).mul_right ((ρ ^ 2) ^ p))
        (fun m => (unit1Entry_diff i m).differentiableOn.mul
          ((ih m).mono (ball_subset_ball hρ1.le))) isOpen_ball
      intro m w hw
      exact unit1WalkTerm_bound hρ hρ1 (mem_ball_zero_iff.mp hw).le p i j m
    exact (hd.differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hzρ))).differentiableWithinAt

/-- Positive-length diagonal walks have a summable geometric envelope in the
outer vertex, so their actual infinite trace is holomorphic. -/
private lemma cycleTrace_diff (k : ℕ) :
    DifferentiableOn ℂ (fun z : ℂ => cycleTrace z k) (ball (0 : ℂ) 1) := by
  intro z hz
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  obtain ⟨ρ, hzρ, hρ1⟩ := exists_between hz1
  have hρ : 0 ≤ ρ := (norm_nonneg z).trans hzρ.le
  have hg : Summable (fun i : ℕ => ρ ^ (i + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hρ hρ1)
  have hd : DifferentiableOn ℂ
      (fun w : ℂ => ∑' i : ℕ, unit1Walk w (2 * (k + 1)) i i)
      (ball (0 : ℂ) ρ) := by
    apply Complex.differentiableOn_tsum_of_summable_norm
      ((hg.mul_right (∑' m : ℕ, ρ ^ (m + 1))).mul_right ((ρ ^ 2) ^ (2 * k + 1)))
      (fun i => (unit1Walk_diff (2 * (k + 1)) i i).mono
        (ball_subset_ball hρ1.le)) isOpen_ball
    intro i w hw
    have he : (2 * k + 1) + 1 = 2 * (k + 1) := by omega
    simpa only [he] using
      unit1Walk_succ_bound hρ hρ1 (mem_ball_zero_iff.mp hw).le (2 * k + 1) i i
  exact (hd.differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hzρ))).differentiableWithinAt

/-- Complex holomorphy of the actual infinite signed-cycle logarithm.
All three summations (internal vertex, outer vertex, and cycle length) have
uniform summable majorants on a disk strictly larger than the evaluation point. -/
theorem gaussianLogDet_differentiableOn :
    DifferentiableOn ℂ gaussianLogDet {z : ℂ | ‖z‖ < 1} := by
  intro z hz
  have hz1 : ‖z‖ < 1 := hz
  obtain ⟨ρ, hzρ, hρ1⟩ := exists_between hz1
  have hρ : 0 ≤ ρ := (norm_nonneg z).trans hzρ.le
  have hd : DifferentiableOn ℂ
      (fun w : ℂ => ∑' k : ℕ, cycleTrace w k / (k + 1 : ℂ))
      (ball (0 : ℂ) ρ) := by
    apply Complex.differentiableOn_tsum_of_summable_norm
      (unit1Majorant_summable hρ hρ1)
      (fun k => ((cycleTrace_diff k).mono (ball_subset_ball hρ1.le)).div_const _)
      isOpen_ball
    intro k w hw
    rw [norm_div, show ‖(k + 1 : ℂ)‖ = (k + 1 : ℝ) by
      simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (k + 1)]
    exact (div_le_self (norm_nonneg _)
      (by linarith [Nat.cast_nonneg (α := ℝ) k] : 1 ≤ (k + 1 : ℝ))).trans
      (cycleTrace_bound hρ hρ1 (mem_ball_zero_iff.mp hw).le k)
  exact ((hd.neg).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hzρ))).differentiableWithinAt

/-- Complex holomorphy of the exponential of the actual original Gaussian
signed-cycle logarithm, on the full open unit disk. -/
theorem gaussianDet_differentiableOn :
    DifferentiableOn ℂ gaussianDet {z : ℂ | ‖z‖ < 1} := by
  exact gaussianLogDet_differentiableOn.cexp

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant
