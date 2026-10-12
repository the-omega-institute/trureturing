/- GID: D5/S3/Estimation/TimeArrow/OriginalScoreWindow
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/OriginalScoreWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The complete original score window and its zero posterior group are identified on the minimal environment. -/

import D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
import D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
import D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import D5.S3.Estimation.TimeArrow.NativeAnchoredSmallBall
import D5.S3.Estimation.TimeArrow.NativeEnvironmentAnchors
import D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
import D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
import D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
import D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall
open Filter
open scoped Topology BigOperators
open Finset
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.NativeRectangleGeometry
open D5.S3.Estimation.TimeArrow.NativeRectangleReferenceMass
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeCalibrationRootBudgets
open D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Estimation.TimeArrow.NativeGrowthRounding
noncomputable section
/-- Index zero corresponds to the first decimal exponent of the original sequence. -/
def decimalExponent : ℕ → ℕ
  | 0 => 1
  | n + 1 => 10 ^ (5 * decimalExponent n)
/-- The original decimal denominator. -/
def denominator (n : ℕ) : ℕ := 10 ^ decimalExponent n
/-- The original integer observation scale. -/
def scale (n : ℕ) : ℕ := denominator n ^ 3
/-- The lower-left signal cell retains the original floor. -/
def centralPositive (r : ℝ) (L : ℕ) : ℕ := ⌊((1 + r) / 2) * (L : ℝ)⌋₊
/-- The second coordinate retains the exact total count. -/
def centralNegative (r : ℝ) (L : ℕ) : ℕ := L - centralPositive r L
/-- The uncompensated score at the original lower-left cell. -/
def center (r : ℝ) (L : ℕ) : ℝ :=
  centralPositive r L * Real.log (1 + r) +
    centralNegative r L * Real.log (1 - r)
/-- Original population size, with its base-two floor. -/
def population (r β : ℝ) (L : ℕ) : ℕ :=
  2 ^ ⌊phi r * (L : ℝ) / (β * Real.log 2)⌋₊
/-- Original signal cardinality, with its final floor. -/
def signalSize (r β : ℝ) (L : ℕ) : ℕ :=
  ⌊(population r β L : ℝ) * Real.exp (-center r L)⌋₊
/-- The original A-cell logit uses the complete background population. -/
def cellLogit (r β : ℝ) (L : ℕ) : ℝ :=
  let M := population r β L
  let q := signalSize r β L
  centralPositive r L * Real.log ((1 + r) / (1 - compensation M q r)) +
    centralNegative r L * Real.log ((1 - r) / (1 + compensation M q r)) -
      Real.log (((M - q : ℕ) : ℝ) / q)
/-- Both central coordinates have a bounded rounding error. -/
theorem central_rounding (r : ℝ) (L : ℕ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    centralPositive r L ≤ L ∧
      0 ≤ ((1 + r) / 2) * (L : ℝ) - centralPositive r L ∧
      ((1 + r) / 2) * (L : ℝ) - centralPositive r L < 1 ∧
      (centralNegative r L : ℝ) = (L : ℝ) - centralPositive r L := by
  have ha : 0 ≤ ((1 + r) / 2) * (L : ℝ) := by positivity
  have hk : centralPositive r L ≤ L := by
    apply Nat.floor_le_of_le
    nlinarith [show (0 : ℝ) ≤ L from Nat.cast_nonneg L]
  refine ⟨hk, sub_nonneg.mpr (Nat.floor_le ha), ?_, ?_⟩
  · have h : ((1 + r) / 2) * (L : ℝ) <
        (⌊((1 + r) / 2) * (L : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    change ((1 + r) / 2) * (L : ℝ) - ⌊((1 + r) / 2) * (L : ℝ)⌋₊ < 1
    linarith
  · exact Nat.cast_sub hk
/-- The original score is the information rate times scale minus a bounded error. -/
theorem center_rounding (r : ℝ) (L : ℕ) (hr : 0 ≤ r) (hr1 : r < 1) :
    phi r * (L : ℝ) - Real.log ((1 + r) / (1 - r)) ≤ center r L ∧
      center r L ≤ phi r * (L : ℝ) := by
  obtain ⟨hk, hx0, hx1, hl⟩ := central_rounding r L hr hr1.le
  have hp : 0 < 1 + r := by linarith
  have hm : 0 < 1 - r := by linarith
  have hc : 0 ≤ Real.log (1 + r) - Real.log (1 - r) :=
    sub_nonneg.mpr (Real.log_le_log hm (by linarith))
  have he : center r L = phi r * (L : ℝ) -
      (((1 + r) / 2) * (L : ℝ) - centralPositive r L) *
        (Real.log (1 + r) - Real.log (1 - r)) := by
    unfold center phi
    rw [hl]
    ring
  rw [he, Real.log_div hp.ne' hm.ne']
  constructor <;> nlinarith
/-- The base-two floor costs at most one factor of two. -/
theorem population_exponential_bounds (r β : ℝ) (L : ℕ)
    (hφ : 0 ≤ phi r) (hβ : 0 < β) :
    Real.exp (phi r / β * (L : ℝ)) / 2 ≤ (population r β L : ℝ) ∧
      (population r β L : ℝ) ≤ Real.exp (phi r / β * (L : ℝ)) := by
  let t := phi r * (L : ℝ) / (β * Real.log 2)
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hm : 0 < (population r β L : ℝ) := by unfold population; positivity
  have he : Real.log (population r β L : ℝ) = (⌊t⌋₊ : ℝ) * Real.log 2 := by
    simp [population, t, Real.log_pow]
  have hlo := mul_le_mul_of_nonneg_right (Nat.floor_le ht) hlog.le
  have hhi := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one t) hlog
  have hrate : t * Real.log 2 = phi r / β * (L : ℝ) := by
    dsimp [t]
    field_simp
  rw [← he, hrate] at hlo
  have hlower : phi r / β * (L : ℝ) - Real.log 2 ≤
      Real.log (population r β L : ℝ) := by
    rw [add_mul, one_mul, ← he, hrate] at hhi
    linarith
  constructor
  · have h := Real.exp_le_exp.mpr hlower
    simpa [Real.exp_sub, Real.exp_log hm, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  · simpa only [Real.exp_log hm] using Real.exp_le_exp.mpr hlo
/-- The fixed nonzero signal amplitude gives a strictly positive information rate. -/
theorem information_rate_bounds (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    0 < phi r ∧ phi r < Real.log 2 := by
  have hp : 0 < 1 + r := by linarith
  have hm : 0 < 1 - r := by linarith
  have hstrict := Real.strictConvexOn_mul_log.2 hp.le hm.le
    (show 1 + r ≠ 1 - r by linarith) (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  have he : (1/2 : ℝ) • (1+r) + (1/2 : ℝ) • (1-r) = 1 := by
    simp only [smul_eq_mul]; ring
  rw [he] at hstrict
  dsimp only at hstrict
  simp only [Real.log_one, mul_zero, smul_eq_mul] at hstrict
  have hlp : Real.log (1+r) < Real.log 2 := Real.log_lt_log hp (by linarith)
  have hlm : Real.log (1-r) < Real.log 2 := Real.log_lt_log hm (by linarith)
  have h1 := mul_lt_mul_of_pos_left hlp hp
  have h2 := mul_lt_mul_of_pos_left hlm hm
  unfold phi
  constructor <;> nlinarith
end
end D5.S3.Estimation.TimeArrow.NativeGrowthRounding
open scoped BigOperators Topology
open Finset Filter
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
open D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback
open D5.S3.Estimation.TimeArrow.NativeAnchoredSmallBall
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
open D5.S3.Estimation.TimeArrow.NativeGlobalRectangleEnvironment
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Estimation.TimeArrow.OriginalScoreWindow
noncomputable section
/-- The original complete window keeps its left-open, right-closed endpoints. -/
def originalWindow {M s : ℕ} (q : ℕ) (r center width : ℝ)
    (e : Experiment) (o : Obs M s e) : Finset (Fin M) := by
  classical
  exact univ.filter fun i => center-width < score q r e o i ∧ score q r e o i ≤ center+width
/-- Exact scores index groups inside the complete window. -/
def originalScoreGroup {M s : ℕ} (q : ℕ) (r center width value : ℝ)
    (e : Experiment) (o : Obs M s e) : Finset (Fin M) := by
  classical
  exact (originalWindow q r center width e o).filter fun i => score q r e o i = value
/-- The denominator in inclusion is the complete uniform-size support posterior. -/
def originalGroupPosteriorMean {M s : ℕ} (q : ℕ) (r center width value : ℝ)
    (e : Experiment) (o : Obs M s e) : ℝ :=
  ∑ i ∈ originalScoreGroup q r center width value e o,inclusion q r e o i
/-- A cut on complete signed departure counts, including all background rows. -/
def originalCountCut {M s : ℕ} (H : ℕ) (e : Experiment) (o : Obs M s e) : Prop :=
  ∀ i : Fin M,count e o i 1+count e o i (-1) ≤ H
set_option maxHeartbeats 800000 in
private theorem compensated_log_bounds (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/2) :
    |Real.log (1-ε)| ≤ 2*ε ∧ |Real.log (1+ε)| ≤ ε ∧
    Real.log (1-ε) ≤ -ε ∧ Real.log (1+ε) ≤ ε := by
  have hp : 0 < 1-ε := by linarith only [hε1]
  have hm := Real.log_le_sub_one_of_pos hp
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hi : (1-ε)⁻¹ ≤ 1+2*ε := by
    apply (inv_le_iff_one_le_mul₀ hp).mpr
    nlinarith only [hε,hε1]
  have hpl := Real.log_le_sub_one_of_pos (by linarith only [hε] : 0 < 1+ε)
  rw [abs_of_nonpos (Real.log_nonpos hp.le (by linarith only [hε])),
    abs_of_nonneg (Real.log_nonneg (by linarith only [hε]))]
  exact ⟨by linarith only [hl,hi],by linarith only [hpl],
    by linarith only [hm],by linarith only [hpl]⟩
set_option maxHeartbeats 800000 in
/-- Integer separation applies to the actual compensated scores. The error
uses the complete count cut and the original uncorrected window center. -/
private theorem count_score_grid_error (k l k0 l0 H Q P : ℕ) (h η ε center raw : ℝ)
    (hQ : 0 < Q) (hh : 0 < h) (hη : 0 < η) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/2)
    (hkl : k+l ≤ H) (hraw : raw = k0*(h*((P : ℝ)/Q+η))-(l0 : ℝ)*h) :
    let a := h*((P : ℝ)/Q+η)-Real.log (1-ε)
    let b := -h-Real.log (1+ε)
    let D : ℤ := (P : ℤ)*((k : ℤ)-k0)-(Q : ℤ)*((l : ℤ)-l0)
    |k*a+l*b-center-(h/Q)*D| ≤
      h*η*(H+k0+l0)+2*ε*H+|raw-center| := by
  dsimp only
  obtain ⟨hminus,hplus,_,_⟩ := compensated_log_bounds ε hε hε1
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have he : (k : ℝ)*(h*((P : ℝ)/Q+η)-Real.log (1-ε))+
      l*(-h-Real.log (1+ε))-center-(h/Q)*
        (((P : ℤ)*((k : ℤ)-k0)-(Q : ℤ)*((l : ℤ)-l0) : ℤ) : ℝ) =
      h*η*((k : ℝ)-k0)-(k : ℝ)*Real.log (1-ε)-l*Real.log (1+ε)+(raw-center) := by
    rw [hraw]
    push_cast
    field_simp <;> ring
  rw [he]
  have hk : |(k : ℝ)-k0| ≤ H+k0+l0 := by
    have hh' : (k : ℝ)+(l : ℝ) ≤ H := by exact_mod_cast hkl
    rw [abs_le]
    constructor <;> linarith only [hh',(Nat.cast_nonneg l : (0 : ℝ) ≤ l),(Nat.cast_nonneg k : (0 : ℝ) ≤ k),(Nat.cast_nonneg k0 : (0 : ℝ) ≤ k0),(Nat.cast_nonneg l0 : (0 : ℝ) ≤ l0)]
  have hcounts : 2*ε*k+ε*l ≤ 2*ε*H := by
    have hh' : (k : ℝ)+(l : ℝ) ≤ H := by exact_mod_cast hkl
    nlinarith only [mul_le_mul_of_nonneg_left hh' hε,(Nat.cast_nonneg l : (0 : ℝ) ≤ l),hε]
  calc
    _ ≤ |h*η*((k : ℝ)-k0)|+|(k : ℝ)*Real.log (1-ε)|+
        |(l : ℝ)*Real.log (1+ε)|+|raw-center| := by
      have h1 := abs_add_le (h*η*((k : ℝ)-k0)-(k : ℝ)*Real.log (1-ε)-l*Real.log (1+ε)) (raw-center)
      have h2 := abs_sub_le (h*η*((k : ℝ)-k0)-(k : ℝ)*Real.log (1-ε)) 0 (l*Real.log (1+ε))
      have h3 := abs_sub_le (h*η*((k : ℝ)-k0)) 0 ((k : ℝ)*Real.log (1-ε))
      simp only [sub_zero,zero_sub,abs_neg] at h2 h3
      linarith only [h1,h2,h3]
    _ ≤ h*η*(H+k0+l0)+2*ε*k+ε*l+|raw-center| := by
      simp only [abs_mul,abs_of_nonneg hh.le,abs_of_nonneg hη.le,
        abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k),abs_of_nonneg (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
      have hx := mul_le_mul_of_nonneg_left hk (mul_nonneg hh.le hη.le)
      have hm := mul_le_mul_of_nonneg_left hminus (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      have hp := mul_le_mul_of_nonneg_left hplus (Nat.cast_nonneg l : (0 : ℝ) ≤ l)
      nlinarith only [hx,hm,hp]
    _ ≤ _ := by linarith only [hcounts]
set_option maxHeartbeats 800000 in
/-- The positive original score step separates exact groups, including
negative original grid indices. -/
private theorem compensated_grid_step_pos (Q P : ℕ) (h η ε : ℝ)
    (hPQ : P < Q) (hh : 0 < h) (hη : 0 < η) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/2) :
    0 < (Q : ℝ)*(h*((P : ℝ)/Q+η)-Real.log (1-ε))+
      P*(-h-Real.log (1+ε)) := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hPQ' : (P : ℝ) < Q := by exact_mod_cast hPQ
  obtain ⟨_,_,hminus,hplus⟩ := compensated_log_bounds ε hε hε1
  have he : (Q : ℝ)*(h*((P : ℝ)/Q+η)-Real.log (1-ε))+
      P*(-h-Real.log (1+ε)) = (Q : ℝ)*h*η-Q*Real.log (1-ε)-P*Real.log (1+ε) := by
    field_simp <;> ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hminus hQ.le
  have hp := mul_le_mul_of_nonneg_left hplus (Nat.cast_nonneg P : (0 : ℝ) ≤ P)
  have hgap : 0 ≤ ((Q : ℝ)-P)*ε := mul_nonneg (by linarith only [hPQ']) hε
  have hpos : 0 < (Q : ℝ)*h*η := by positivity
  nlinarith only [hm,hp,hgap,hpos]
set_option maxHeartbeats 800000 in
private theorem count_zero_score_unique (k l k0 l0 H Q P : ℕ) (a b scale center E : ℝ)
    (hQ : 0 < Q) (hscale : 0 < scale) (hgap : 2*E < scale)
    (hstep : 0 < (Q : ℝ)*a+P*b)
    (hkl : k+l ≤ H) (hbase : k0+l0 ≤ H)
    (herror : ∀ K L : ℕ,K+L ≤ H →
      |(K : ℝ)*a+L*b-center-scale*
        (((P : ℤ)*((K : ℤ)-k0)-(Q : ℤ)*((L : ℤ)-l0) : ℤ) : ℝ)| ≤ E)
    (heq : (k : ℝ)*a+l*b = k0*a+l0*b) : k = k0 ∧ l = l0 := by
  let D : ℤ := (P : ℤ)*((k : ℤ)-k0)-(Q : ℤ)*((l : ℤ)-l0)
  have hi := herror k l hkl
  have hb := herror k0 l0 hbase
  simp only [sub_self,mul_zero,sub_zero,Int.cast_zero] at hb
  have hD : D = 0 := by
    by_contra hn
    have habs : (1 : ℝ) ≤ |(D : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have he : scale*(D : ℝ) = ((k0 : ℝ)*a+l0*b-center)-
        ((k : ℝ)*a+l*b-center-scale*(D : ℝ)) := by rw [heq]; ring
    have hbound : |scale*(D : ℝ)| ≤ 2*E := by
      rw [he]
      calc
        _ ≤ |(k0 : ℝ)*a+l0*b-center|+|(k : ℝ)*a+l*b-center-scale*(D : ℝ)| := abs_sub _ _
        _ ≤ _ := by linarith only [hi,hb]
    rw [abs_mul,abs_of_pos hscale] at hbound
    have hl := mul_le_mul_of_nonneg_left habs hscale.le
    linarith only [hl,hbound,hgap]
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hDreal : (P : ℝ)*((k : ℝ)-k0)-(Q : ℝ)*((l : ℝ)-l0) = 0 := by
    have hd : (D : ℝ) = 0 := by rw [hD]; simp
    simpa only [D,Int.cast_sub,Int.cast_mul,Int.cast_natCast] using hd
  have hlinear : ((Q : ℝ)*a+P*b)*((k : ℝ)-k0) =
      (Q : ℝ)*((k : ℝ)*a+l*b-(k0*a+l0*b))+b*((P : ℝ)*((k : ℝ)-k0)-(Q : ℝ)*((l : ℝ)-l0)) := by ring
  rw [heq,sub_self,hDreal,mul_zero,zero_add,mul_zero] at hlinear
  have hk : (k : ℝ) = k0 := by
    have hh := (mul_eq_zero.mp hlinear).resolve_left hstep.ne'
    linarith only [hh]
  have hl : (l : ℝ) = l0 := by
    rw [hk,sub_self,mul_zero,zero_sub,neg_eq_zero] at hDreal
    have hh := (mul_eq_zero.mp hDreal).resolve_left hQ0
    linarith only [hh]
  exact ⟨by exact_mod_cast hk,by exact_mod_cast hl⟩
set_option maxHeartbeats 1000000 in
/-- Finite original numerical bounds identify the complete exact zero score
group with the A cell over all candidates, including background rows. -/
theorem original_zero_group_eq_all_cell {M s : ℕ} (q : ℕ) (r center width η : ℝ)
    (e : Experiment) (o : Obs M s e) (k0 l0 H Q P : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (hPQ : P < Q) (hη : 0 < η)
    (hε : 0 ≤ compensation M q r) (hε1 : compensation M q r ≤ 1/2)
    (hbase : k0+l0 ≤ H) (hcut : originalCountCut H e o) (hwidth : 0 < width)
    (hlog : Real.log (1+r) = (-Real.log (1-r))*((P : ℝ)/Q+η))
    (herror : (-Real.log (1-r))*η*(H+k0+l0)+2*compensation M q r*H+
      |(k0 : ℝ)*Real.log (1+r)+l0*Real.log (1-r)-center| ≤ width/2)
    (hgrid : (Q : ℝ)*width ≤ (-Real.log (1-r))/4) :
    let value := (k0 : ℝ)*Real.log ((1+r)/(1-compensation M q r))+
      l0*Real.log ((1-r)/(1+compensation M q r))
    originalScoreGroup q r center width value e o =
      nativeCalibrationCells (⟨univ,by simp⟩ : Support M M) e o k0 l0 0 := by
  classical
  dsimp only
  let h := -Real.log (1-r)
  let ε := compensation M q r
  let raw := (k0 : ℝ)*Real.log (1+r)+l0*Real.log (1-r)
  let E := h*η*(H+k0+l0)+2*ε*H+|raw-center|
  let a := h*((P : ℝ)/Q+η)-Real.log (1-ε)
  let b := -h-Real.log (1+ε)
  have hh : 0 < h := by
    dsimp [h]
    exact neg_pos.mpr (Real.log_neg (by linarith only [hr1]) (by linarith only [hr]))
  have hQ : 0 < Q := by omega
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have ha : Real.log ((1+r)/(1-ε)) = a := by
    rw [Real.log_div (by linarith only [hr]) (by linarith only [hε1]),hlog]
  have hb : Real.log ((1-r)/(1+ε)) = b := by
    rw [Real.log_div (by linarith only [hr1]) (by linarith only [hε])]
    dsimp [b,h]
    ring
  have hraw : raw = k0*(h*((P : ℝ)/Q+η))-(l0 : ℝ)*h := by dsimp [raw,h]; rw [hlog] <;> ring
  have he (K L : ℕ) (hKL : K+L ≤ H) :
      |(K : ℝ)*a+L*b-center-(h/Q)*
        (((P : ℤ)*((K : ℤ)-k0)-(Q : ℤ)*((L : ℤ)-l0) : ℤ) : ℝ)| ≤ E :=
    count_score_grid_error K L k0 l0 H Q P h η ε center raw hQ hh hη hε hε1 hKL hraw
  have hstep : 0 < (Q : ℝ)*a+P*b := compensated_grid_step_pos Q P h η ε hPQ hh hη hε hε1
  have hE : E ≤ width/2 := herror
  have hgap : 2*E < h/Q := by
    have hscale := div_pos hh hQreal
    have hsmall : width ≤ (h/Q)/4 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
      apply (le_div_iff₀ hQreal).mpr
      nlinarith only [hgrid]
    linarith only [hE,hsmall,hscale]
  have hbaseerror := he k0 l0 hbase
  simp only [sub_self,mul_zero,sub_zero,Int.cast_zero] at hbaseerror
  have hwindow : center-width < (k0 : ℝ)*a+l0*b ∧ (k0 : ℝ)*a+l0*b ≤ center+width := by
    have hx := abs_le.mp hbaseerror
    constructor <;> linarith only [hx.1,hx.2,hE,hwidth]
  ext i
  simp only [originalScoreGroup,originalWindow,nativeCalibrationCells,mem_filter,mem_univ,true_and]
  rw [native_row_cell_iff]
  simp only [mem_univ,true_and,Fin.isValue,Matrix.cons_val_zero,Nat.add_zero]
  rw [ha,hb]
  constructor
  · rintro ⟨_,hscore⟩
    change (count e o i 1 : ℝ)*Real.log ((1+r)/(1-ε))+
      count e o i (-1)*Real.log ((1-r)/(1+ε)) = _ at hscore
    rw [ha,hb] at hscore
    exact count_zero_score_unique (count e o i 1) (count e o i (-1)) k0 l0 H Q P a b
      (h/Q) center E hQ (div_pos hh hQreal) hgap hstep (hcut i) hbase he hscore
  · rintro ⟨hk,hl⟩
    constructor
    · simpa only [score,hk,hl,ε,ha,hb] using hwindow
    · simpa only [score,hk,hl,ε,ha,hb]
private theorem original_count_cut_transfer {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)] (k l H : ℕ)
    (y z : Fiber S e o)
    (henv : nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z)
    (hH : k+l+2 ≤ H) (hcut : originalCountCut H e z.val) : originalCountCut H e y.val := by
  classical
  intro i
  cases ho : nativeRowCell S e y.val k l i with
  | none =>
    have hmargin := (native_minimal_readout_eq_iff S e o k l z y).mp henv.symm
    have hi := native_environment_outside_counts S e o k l z y hmargin i ho
    rw [←hi.1,←hi.2.1]
    exact hcut i
  | some j =>
    have hi := (native_row_cell_iff S e y.val k l i j).mp ho
    fin_cases j <;> simp at hi <;> omega
/-- A cut witnessed by one anchor holds on its entire original environment;
the conditioning sigma-algebra receives no additional success flag. -/
theorem original_count_cut_same_environment {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)] (k l H : ℕ)
    (y z : Fiber S e o)
    (henv : nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z)
    (hH : k+l+2 ≤ H) : originalCountCut H e y.val ↔ originalCountCut H e z.val :=
  ⟨original_count_cut_transfer S e o k l H z y henv.symm hH,
    original_count_cut_transfer S e o k l H y z henv hH⟩
/-- A complete cube coordinate is numbered by its remaining coordinates and
its product sign. This preserves state identity and parity simultaneously. -/
def cubeParityEquiv (d : ℕ) : (Fin (d+1) → ℤˣ) ≃ Vertex (2^d) := by
  classical
  let number : (Fin d → ℤˣ) ≃ Fin (2^d) := Fintype.equivFinOfCardEq (by simp)
  let split : (Fin (d+1) → ℤˣ) ≃ ((Fin d → ℤˣ) × ℤˣ) :=
    (Fin.consEquiv (fun _ : Fin (d+1) => ℤˣ)).symm.trans
      { toFun := fun u => (u.2,u.1*∏ j,u.2 j)
        invFun := fun u => (u.2*(∏ j,u.1 j)⁻¹,u.1)
        left_inv := by
          intro u
          change (u.1 * (∏ j, u.2 j) * (∏ j, u.2 j)⁻¹, u.2) = u
          rw [mul_inv_cancel_right]
        right_inv := by
          intro u
          change (u.1, u.2 * (∏ j, u.1 j)⁻¹ * (∏ j, u.1 j)) = u
          rw [inv_mul_cancel_right] }
  exact split.trans
    { toFun := fun u => if u.2 = 1 then Sum.inl (number u.1) else Sum.inr (number u.1)
      invFun := fun u => match u with
        | .inl i => (number.symm i,1)
        | .inr i => (number.symm i,-1)
      left_inv := by
        intro ⟨f,z⟩
        rcases Int.units_eq_one_or z with h | h <;> subst z <;> simp
      right_inv := by
        intro u
        cases u <;> simp }
/-- The native sign agrees exactly with the frozen original cube parity. -/
private theorem cube_parity_preserved (d : ℕ) (x : Fin (d+1) → ℤˣ) :
    chi (cubeParityEquiv d x) = D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.parity x := by
  rcases Int.units_eq_one_or (∏ j,x j) with h | h
  · have hs : x 0*(∏ j : Fin d,x j.succ) = 1 := by simpa only [Fin.prod_univ_succ] using h
    simp [cubeParityEquiv,Fin.consEquiv,chi,
      D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.parity,Fin.prod_univ_succ,Fin.tail,hs]
  · have hs : x 0*(∏ j : Fin d,x j.succ) = -1 := by simpa only [Fin.prod_univ_succ] using h
    simp [cubeParityEquiv,Fin.consEquiv,chi,
      D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.parity,Fin.prod_univ_succ,Fin.tail,hs]
/-- Every site is preserved, so path adjacency is preserved along with pair
endpoints. The original path is not replaced by a product of independent edges. -/
def cubeObservationEquiv (d s : ℕ) (e : Experiment) :
    (Sites s e → Fin (d+1) → ℤˣ) ≃ Obs (2^d) s e :=
  (Equiv.piCongrRight fun _ : Sites s e => cubeParityEquiv d).trans (siteEquiv (2^d) s e).symm
private theorem cube_transition_eq {d q : ℕ} (S : Support (2^d) q) (r : ℝ)
    (x y : Fin (d+1) → ℤˣ) :
    D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.parityKernel
      (fun u => b r S (cubeParityEquiv d u)) x y =
        transition r S (cubeParityEquiv d x) (cubeParityEquiv d y) := by
  unfold D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.parityKernel transition
  rw [←cube_parity_preserved d y]
  congr 1
  push_cast
  rw [pow_succ]
  ring
/-- Original pair and path masses use the frozen cube transition kernel
with its original uniform initial law and actual compensation coefficient. -/
def originalCubeProbability {d q s : ℕ} (r : ℝ) (e : Experiment)
    (S : Support (2^d) q) (X : Sites s e → Fin (d+1) → ℤˣ) : ℝ :=
  match e with
  | .pair => ∏ k : Fin s,(2*(2^d : ℕ) : ℝ)⁻¹ *
      D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.parityKernel
        (fun u => b r S (cubeParityEquiv d u)) (X (k,false)) (X (k,true))
  | .path => (2*(2^d : ℕ) : ℝ)⁻¹ * ∏ k : Fin s,
      D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.parityKernel
        (fun u => b r S (cubeParityEquiv d u)) (X k.castSucc) (X k.succ)
theorem original_cube_probability_eq_native {d q s : ℕ} (r : ℝ) (e : Experiment)
    (S : Support (2^d) q) (X : Sites s e → Fin (d+1) → ℤˣ) :
    originalCubeProbability r e S X = probability r e S (cubeObservationEquiv d s e X) := by
  cases e <;> dsimp [originalCubeProbability,probability,cubeObservationEquiv,siteEquiv]
  · simp only [cube_transition_eq,Equiv.piCongrRight_apply] <;> rfl
  · simp only [cube_transition_eq,Equiv.piCongrRight_apply,Equiv.refl_apply] <;> rfl
open scoped Classical in
theorem original_cube_conditional_mass_eq {d q s : ℕ} (r : ℝ) (e : Experiment)
    [Fintype (Sites s e)] (S : Support (2^d) q) (X : Sites s e → Fin (d+1) → ℤˣ)
    (k l : ℕ) (P : Obs (2^d) s e → Prop) :
    (∑ Y : Sites s e → Fin (d+1) → ℤˣ,
      if fullRectangleReadout S e k l (cubeObservationEquiv d s e Y) =
          fullRectangleReadout S e k l (cubeObservationEquiv d s e X) ∧ P (cubeObservationEquiv d s e Y)
        then originalCubeProbability r e S Y else 0)/
      (∑ Y : Sites s e → Fin (d+1) → ℤˣ,
        if fullRectangleReadout S e k l (cubeObservationEquiv d s e Y) =
            fullRectangleReadout S e k l (cubeObservationEquiv d s e X)
          then originalCubeProbability r e S Y else 0) =
    (∑ y : Obs (2^d) s e,if fullRectangleReadout S e k l y =
        fullRectangleReadout S e k l (cubeObservationEquiv d s e X) ∧ P y
      then probability r e S y else 0)/
      (∑ y : Obs (2^d) s e,if fullRectangleReadout S e k l y =
          fullRectangleReadout S e k l (cubeObservationEquiv d s e X)
        then probability r e S y else 0) := by
  classical
  simp_rw [original_cube_probability_eq_native]
  rw [(cubeObservationEquiv d s e).sum_comp (fun y =>
    if fullRectangleReadout S e k l y = fullRectangleReadout S e k l (cubeObservationEquiv d s e X) ∧ P y
      then probability r e S y else 0)]
  rw [(cubeObservationEquiv d s e).sum_comp (fun y =>
    if fullRectangleReadout S e k l y = fullRectangleReadout S e k l (cubeObservationEquiv d s e X)
      then probability r e S y else 0)]
/-- Exact departure counts use the same source site and successor sign in
both experiments, including the path endpoint convention. -/
private theorem original_cube_departure_counts {d s : ℕ}
    (e : Experiment) (X : Sites s e → Fin (d+1) → ℤˣ) (i : Fin (2^d)) (sign : ℝ) :
    count e (cubeObservationEquiv d s e X) i sign =
      (univ.filter fun j : Fin s => cubeParityEquiv d (X (departureSite s e j)) = Sum.inl i ∧
        D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.parity (X (successorSite s e j)) = sign).card := by
  classical
  simp_rw [←cube_parity_preserved]
  cases e <;> rfl
/-- Original cube scores use actual departure sites and successor parity. -/
def originalCubeScore {d s : ℕ} (q : ℕ) (r : ℝ) (e : Experiment)
    (X : Sites s e → Fin (d+1) → ℤˣ) (i : Fin (2^d)) : ℝ := by
  classical
  let C := fun sign : ℝ => (univ.filter fun j : Fin s =>
    cubeParityEquiv d (X (departureSite s e j)) = Sum.inl i ∧
      D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.parity (X (successorSite s e j)) = sign).card
  exact C 1*Real.log ((1+r)/(1-compensation (2^d) q r))+
    C (-1)*Real.log ((1-r)/(1+compensation (2^d) q r))
private theorem original_cube_score_eq_native {d s : ℕ} (q : ℕ) (r : ℝ)
    (e : Experiment) (X : Sites s e → Fin (d+1) → ℤˣ) (i : Fin (2^d)) :
    originalCubeScore q r e X i = score q r e (cubeObservationEquiv d s e X) i := by
  unfold originalCubeScore score
  rw [original_cube_departure_counts e X i 1,
    original_cube_departure_counts e X i (-1)]
/-- Uniform-size support posterior inclusion from the original full cube
likelihood, with all size-q supports retained in its denominator. -/
def originalCubeInclusion {d s : ℕ} (q : ℕ) (r : ℝ) (e : Experiment)
    (X : Sites s e → Fin (d+1) → ℤˣ) (i : Fin (2^d)) : ℝ := by
  classical
  exact ∑ S : Support (2^d) q, if i ∈ S.val then
    originalCubeProbability r e S X /
      (∑ T : Support (2^d) q, originalCubeProbability r e T X) else 0
private theorem original_cube_inclusion_eq_native {d s : ℕ} (q : ℕ) (r : ℝ)
    (e : Experiment) (X : Sites s e → Fin (d+1) → ℤˣ) (i : Fin (2^d)) :
    originalCubeInclusion q r e X i = inclusion q r e (cubeObservationEquiv d s e X) i := by
  classical
  unfold originalCubeInclusion inclusion posterior
  simp_rw [original_cube_probability_eq_native]
/-- The complete original cube group keeps the original window and exact
score; inclusion uses the complete size-q posterior under its full-data law. -/
def originalCubeGroupPosteriorMean {d s : ℕ} (q : ℕ) (r center width value : ℝ)
    (e : Experiment) (X : Sites s e → Fin (d+1) → ℤˣ) : ℝ := by
  classical
  exact ∑ i ∈ univ.filter (fun i => center-width < originalCubeScore q r e X i ∧
    originalCubeScore q r e X i ≤ center+width ∧ originalCubeScore q r e X i = value),
    originalCubeInclusion q r e X i
theorem original_cube_group_eq_native {d s : ℕ} (q : ℕ) (r center width value : ℝ)
    (e : Experiment) (X : Sites s e → Fin (d+1) → ℤˣ) :
    originalCubeGroupPosteriorMean q r center width value e X =
      originalGroupPosteriorMean q r center width value e (cubeObservationEquiv d s e X) := by
  classical
  unfold originalCubeGroupPosteriorMean originalGroupPosteriorMean originalScoreGroup originalWindow
  simp_rw [original_cube_score_eq_native,original_cube_inclusion_eq_native]
  rw [filter_filter]
  congr 1
  ext i
  simp only [mem_filter,mem_univ,true_and]
  tauto
end
end D5.S3.Estimation.TimeArrow.OriginalScoreWindow
open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Estimation.TimeArrow.NativeRectangleOccupancy
noncomputable section
/-- An exact native cell indicator uses the finite relative law, so no
whole-population tail term is needed for a bounded count cell. -/
theorem native_cell_occupancy_budget (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        ∀ (S : Support M q) (e : Experiment) (I : Finset (Fin M)) (c : ℕ × ℕ),
          (c.1 : ℝ) ≤ 8 * L → (c.2 : ℝ) ≤ 8 * L →
          ∀ m : ℝ, 0 < m →
          7 / 8 * m ≤ ∑ i ∈ I, rowReference S r L i c →
          (∑ i ∈ I, rowReference S r L i c) ≤ 9 / 8 * m →
          (∑ o : Obs M (2 * M * L) e,
            if ¬(3 / 4 * m ≤ ((I.filter fun i =>
                count e o i 1 = c.1 ∧ count e o i (-1) = c.2).card : ℝ) ∧
              ((I.filter fun i => count e o i 1 = c.1 ∧
                count e o i (-1) = c.2).card : ℝ) ≤ 5 / 4 * m)
            then probability r e S o else 0) ≤
              108 / m + 243 * (A * (L : ℝ) ^ 3 / M) := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ :=
    native_truncated_weighted_moments κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e I c hc1 hc2 m hm hlo hhi
  let a : ℝ := ∑ i ∈ I, rowReference S r L i c
  let Z := fun o : Obs M (2 * M * L) e =>
    ((I.filter fun i => count e o i 1 = c.1 ∧ count e o i (-1) = c.2).card : ℝ)
  have hZ (o : Obs M (2 * M * L) e) :
      (∑ i ∈ I, truncatedRow e {c} (fun _ _ => 1) i o) = Z o := by
    simp only [truncatedRow, sum_singleton]
    exact sum_boole _ _
  have hmoment := (h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall
    S e I {c} (fun _ _ => 1)
    (by simpa only [mem_singleton] using fun d (hd : d = c) => hd ▸ And.intro hc1 hc2)
    (by intros; norm_num)).2
  simp only [sum_singleton, one_mul, hZ] at hmoment
  have hr1 : r < 1 := by linarith only [hrκ, hκ]
  have hcomp : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hcomp1 : compensation M q r < 1 := by linarith only [hcκ, hκ]
  have hp := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hcomp hcomp1 e).2.1.1 S
  have htail := finite_square_markov (probability r e S) Z a (m / 8)
    ((3 / 2) * a + 3 * (A * (L : ℝ) ^ 3 / M) * a ^ 2) hp (by positivity) hmoment
  have hcontain (o : Obs M (2 * M * L) e)
      (ho : ¬(3 / 4 * m ≤ Z o ∧ Z o ≤ 5 / 4 * m)) : m / 8 < |Z o - a| := by
    by_contra hn
    have hh := abs_le.mp (le_of_not_gt hn)
    apply ho
    dsimp only [a] at hh
    constructor <;> linarith only [hh.1, hh.2, hlo, hhi]
  have hnum : (3 / 2) * a + 3 * (A * (L : ℝ) ^ 3 / M) * a ^ 2 ≤
      (108 / m + 243 * (A * (L : ℝ) ^ 3 / M)) * (m / 8) ^ 2 := by
    have ha0 : 0 ≤ a := by dsimp only [a]; linarith only [hlo, hm]
    have hasq : a ^ 2 ≤ (9 / 8 * m) ^ 2 := by dsimp only [a]; nlinarith only [hhi, ha0, hm]
    have hδ : 0 ≤ A * (L : ℝ) ^ 3 / M := by positivity
    have hh := mul_le_mul_of_nonneg_left hasq (show 0 ≤ 3 * (A * (L : ℝ) ^ 3 / M) by positivity)
    have he : (108 / m + 243 * (A * (L : ℝ) ^ 3 / M)) * (m / 8) ^ 2 =
        (27 / 16) * m + (243 / 64) * (A * (L : ℝ) ^ 3 / M) * m ^ 2 := by
      field_simp
      <;> ring
    rw [he]
    dsimp only [a] at *
    nlinarith only [hh, hhi]
  apply le_trans _ (htail.trans ((div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < m / 8))).mpr hnum))
  apply sum_le_sum
  intro o _
  change (if ¬(3 / 4 * m ≤ Z o ∧ Z o ≤ 5 / 4 * m) then _ else _) ≤ _
  by_cases ho : 3 / 4 * m ≤ Z o ∧ Z o ≤ 5 / 4 * m
  · by_cases ht : m / 8 < |Z o - a| <;> simp [ho, ht, hp o]
  · simp [ho, hcontain o ho]
/-- The four signal cells and background A cell may share arbitrary native
dependence. Only their individual reference means are used in the union bound. -/
theorem native_five_cell_occupancy_budget (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        ∀ (S : Support M q) (e : Experiment) (I : Fin 5 → Finset (Fin M))
          (c : Fin 5 → ℕ × ℕ),
          (∀ j, ((c j).1 : ℝ) ≤ 8 * L ∧ ((c j).2 : ℝ) ≤ 8 * L) →
          ∀ m : ℝ, 0 < m →
          (∀ j, 7 / 8 * m ≤ ∑ i ∈ I j, rowReference S r L i (c j)) →
          (∀ j, (∑ i ∈ I j, rowReference S r L i (c j)) ≤ 9 / 8 * m) →
          (∑ o : Obs M (2 * M * L) e,
            if ¬∀ j, 3 / 4 * m ≤ (((I j).filter fun i =>
                count e o i 1 = (c j).1 ∧ count e o i (-1) = (c j).2).card : ℝ) ∧
              (((I j).filter fun i => count e o i 1 = (c j).1 ∧
                count e o i (-1) = (c j).2).card : ℝ) ≤ 5 / 4 * m
            then probability r e S o else 0) ≤
              540 / m + 1215 * (A * (L : ℝ) ^ 3 / M) := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ := native_cell_occupancy_budget κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e I c hc m hm hlo hhi
  let Good := fun (o : Obs M (2 * M * L) e) (j : Fin 5) =>
    3 / 4 * m ≤ (((I j).filter fun i => count e o i 1 = (c j).1 ∧
      count e o i (-1) = (c j).2).card : ℝ) ∧
    (((I j).filter fun i => count e o i 1 = (c j).1 ∧
      count e o i (-1) = (c j).2).card : ℝ) ≤ 5 / 4 * m
  have hr1 : r < 1 := by linarith only [hrκ, hκ]
  have hcomp : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hcomp1 : compensation M q r < 1 := by linarith only [hcκ, hκ]
  have hp := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hcomp hcomp1 e).2.1.1 S
  calc
    _ ≤ ∑ o : Obs M (2 * M * L) e, ∑ j : Fin 5,
        if ¬Good o j then probability r e S o else 0 := by
      apply sum_le_sum
      intro o _
      change (if ¬∀ j, Good o j then _ else _) ≤ _
      by_cases ho : ∀ j, Good o j
      · simp [ho]
      · obtain ⟨j, hj⟩ := not_forall.mp ho
        simp only [ho, not_false_eq_true, if_true]
        have hh := single_le_sum
          (f := fun j : Fin 5 => if ¬Good o j then probability r e S o else 0)
          (fun k (_ : k ∈ (univ : Finset (Fin 5))) => by
            split_ifs <;> first | exact hp o | exact le_rfl) (mem_univ j)
        simpa only [hj, not_false_eq_true, if_true] using hh
    _ = ∑ j : Fin 5, ∑ o : Obs M (2 * M * L) e,
        if ¬Good o j then probability r e S o else 0 := sum_comm
    _ ≤ ∑ _j : Fin 5, (108 / m + 243 * (A * (L : ℝ) ^ 3 / M)) := by
      apply sum_le_sum
      intro j _
      exact h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e (I j) (c j)
        (hc j).1 (hc j).2 m hm (hlo j) (hhi j)
    _ = _ := by simp; ring
/-- Simultaneous occupancy is for the actual four signal cells and the
actual background A cell. Its reference comparison preserves the original
compensation and full population sizes. -/
theorem native_signal_background_occupancy (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        ∀ (S : Support M q) (e : Experiment) (i j : Fin M),
          i ∈ S.val → j ∉ S.val → ∀ k l : ℕ,
          k = ⌊((1+r)/2)*(L : ℝ)⌋₊ → l = L-k →
          15 ≤ ((1+r)/2)*(L : ℝ) → 30 ≤ ((1-r)/2)*(L : ℝ) →
          let dA := k * Real.log ((1+r)/(1-compensation M q r)) +
            l * Real.log ((1-r)/(1+compensation M q r)) -
            Real.log (((M-q : ℕ) : ℝ)/q)
          Real.log (7/8) ≤ -dA → -dA ≤ Real.log (9/8) →
          let m := (q : ℝ) * rowReference S r L i (k,l)
          let All : Support M M := ⟨univ, by simp⟩
          (∑ o : Obs M (2*M*L) e,
            if ¬((∀ a : Fin 4,
                3/4*m ≤ ((nativeCalibrationCells S e o k l a).card : ℝ) ∧
                ((nativeCalibrationCells S e o k l a).card : ℝ) ≤ 5/4*m) ∧
              3/4*m ≤ ((nativeCalibrationCells All e o k l 0 \ S.val).card : ℝ) ∧
              ((nativeCalibrationCells All e o k l 0 \ S.val).card : ℝ) ≤ 5/4*m)
            then probability r e S o else 0) ≤
              540/m + 1215*(A*(L : ℝ)^3/M) := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ := native_five_cell_occupancy_budget κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e i j hi hj k l hkfloor hlfloor hplus hminus
  have hr1 : r < 1 := by linarith only [hrκ,hκ]
  have hround := original_count_rounding r L hr hr1 hL hplus hminus
  dsimp only at hround
  rw [← hkfloor, ← hlfloor] at hround
  have hkL : (k : ℝ) ≤ L := by exact_mod_cast hround.1
  have hlL : (l : ℝ) ≤ L := by
    exact_mod_cast (show l ≤ L by rw [hlfloor]; omega)
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hk : (k+1 : ℝ) ≤ 8*L := by linarith only [hkL,hLR]
  have hl : (l+1 : ℝ) ≤ 8*L := by linarith only [hlL,hLR]
  dsimp only
  intro hdlo hdhi
  let m := (q : ℝ) * rowReference S r L i (k,l)
  let c : Fin 5 → ℕ × ℕ := ![(k,l),(k+1,l),(k,l+1),(k+1,l+1),(k,l)]
  let I : Fin 5 → Finset (Fin M) := ![S.val,S.val,S.val,S.val,univ \ S.val]
  have hm : 0 < m := mul_pos (by exact_mod_cast (show 0 < q by omega))
    (reference_pos S r κ hκ hr hrκ hcκ hL i (k,l))
  have hsig (a : Fin 4) : (∑ u ∈ S.val,
      rowReference S r L u (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] a)) =
      (q : ℝ) * rowReference S r L i (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] a) := by
    calc
      _ = ∑ _u ∈ S.val,
          rowReference S r L i (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] a) :=
        sum_congr rfl fun u hu => by simp only [rowReference,b,if_pos hu,if_pos hi]
      _ = _ := by simp [S.property,nsmul_eq_mul]
  have hbg : (∑ u ∈ univ \ S.val, rowReference S r L u (k,l)) =
      ((M-q : ℕ) : ℝ) * rowReference S r L j (k,l) := by
    calc
      _ = ∑ _u ∈ univ \ S.val, rowReference S r L j (k,l) :=
        sum_congr rfl fun u hu => by
          simp only [rowReference,b,if_neg (mem_sdiff.mp hu).2,if_neg hj]
      _ = _ := by simp [card_sdiff_of_subset (subset_univ S.val),S.property,nsmul_eq_mul]
  have hs := floored_signal_four_reference_ratios S r κ hκ hr hrκ hcκ hL i hi hplus hminus
  dsimp only at hs
  rw [← hkfloor, ← hlfloor] at hs
  have hb := background_reference_cell_ratio S r κ hκ hr hrκ hcκ hL hq hqm i j hi hj k l
  have hexlo := Real.exp_le_exp.mpr hdlo
  have hexhi := Real.exp_le_exp.mpr hdhi
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 7/8)] at hexlo
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 9/8)] at hexhi
  have hsm (a : Fin 4) :
      7/8*m ≤ ∑ u ∈ S.val, rowReference S r L u (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] a) ∧
      (∑ u ∈ S.val, rowReference S r L u (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] a)) ≤ 9/8*m := by
    rw [hsig a]
    have hh := And.intro
      (mul_le_mul_of_nonneg_left (hs a).1 (by positivity : (0 : ℝ) ≤ q))
      (mul_le_mul_of_nonneg_left (hs a).2 (by positivity : (0 : ℝ) ≤ q))
    simpa [m, mul_assoc, mul_left_comm] using hh
  have hmean (a : Fin 5) : 7/8*m ≤ ∑ u ∈ I a, rowReference S r L u (c a) ∧
      (∑ u ∈ I a, rowReference S r L u (c a)) ≤ 9/8*m := by
    fin_cases a
    · exact hsm 0
    · exact hsm 1
    · exact hsm 2
    · exact hsm 3
    · change 7/8*m ≤ ∑ u ∈ univ \ S.val, rowReference S r L u (k,l) ∧
        (∑ u ∈ univ \ S.val, rowReference S r L u (k,l)) ≤ 9/8*m
      rw [hbg,hb]
      have hh := And.intro (mul_le_mul_of_nonneg_left hexlo hm.le)
        (mul_le_mul_of_nonneg_left hexhi hm.le)
      simpa only [m,mul_comm] using hh
  have he := h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e I c
    (by intro a; fin_cases a <;> simp [c] <;> constructor <;> linarith only [hk,hl])
    m hm (fun a => (hmean a).1) (fun a => (hmean a).2)
  convert he using 1
  apply sum_congr rfl
  intro o _
  congr 1
  have hcell (a : Fin 4) : nativeCalibrationCells S e o k l a =
      S.val.filter fun u => count e o u 1 = k + ![0,1,0,1] a ∧
        count e o u (-1) = l + ![0,0,1,1] a := by
    ext u
    simp [nativeCalibrationCells,native_row_cell_iff]
  have hback : nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e o k l 0 \ S.val =
      (univ \ S.val).filter fun u => count e o u 1 = k ∧ count e o u (-1) = l := by
    ext u
    simp [nativeCalibrationCells,native_row_cell_iff,and_assoc,and_left_comm,and_comm]
  simp_rw [hcell,hback]
  simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,I,c,m,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_fin_one,Nat.add_zero,and_true]
  apply propext
  tauto
end
end D5.S3.Estimation.TimeArrow.NativeRectangleOccupancy
open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open D5.S3.Estimation.TimeArrow.NativeRectangleOccupancy
open D5.S3.Estimation.TimeArrow.NativeRectangleReferenceMass
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeGlobalRectangleEnvironment
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricMaxAtom
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Estimation.TimeArrow.NativeRectangleGeometry
noncomputable section
private theorem native_occupancy_geometry {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) (k l : ℕ) (m : ℝ)
    (hcell : ∀ j : Fin 4,
      3/4*m ≤ ((nativeCalibrationCells S e o k l j).card : ℝ) ∧
      ((nativeCalibrationCells S e o k l j).card : ℝ) ≤ 5/4*m)
    (hbg : ((nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e o k l 0 \ S.val).card : ℝ)
      ≤ 5/4*m) :
    let V := nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)
    let R := (V.filter fun i => count e o i.val 1 = k).card
    let U := (V.filter fun i => count e o i.val (-1) = l).card
    3*m ≤ V.card ∧ (V.card : ℝ) ≤ 5*m ∧
      3/8*(V.card : ℝ) ≤ R ∧ (R : ℝ) ≤ 5/8*(V.card : ℝ) ∧
      3/8*(V.card : ℝ) ≤ U ∧ (U : ℝ) ≤ 5/8*(V.card : ℝ) ∧
      ((nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e o k l 0 \ S.val).card : ℝ)
        ≤ 5/12*(V.card : ℝ) := by
  have hc := native_calibration_counts_margins S e o k l (⟨o,rfl⟩ : Fiber S e o)
  dsimp only at hc ⊢
  rcases hc with ⟨hN,hR,hU,_⟩
  rw [hN,hR,hU]
  push_cast
  have h0 := hcell 0
  have h1 := hcell 1
  have h2 := hcell 2
  have h3 := hcell 3
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith only [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,hbg]
open scoped Classical in
/-- The actual native good event has N comparable to q/lambda, balanced
margins, and background A no larger than N. All five occupancies are
proved under the original pair or path law with one shared failure budget. -/
theorem native_signal_geometry_budget (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ K : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧ 0 < K ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1-κ → compensation M q r ≤ 1-κ →
        1 ≤ L → (L : ℝ)/M ≤ η₀ → A*(L : ℝ)^2/M ≤ 1/2 →
        ∀ (S : Support M q) (e : Experiment) (i j : Fin M),
          i ∈ S.val → j ∉ S.val →
          15 ≤ ((1+r)/2)*(L : ℝ) → 30 ≤ ((1-r)/2)*(L : ℝ) →
          let k := ⌊((1+r)/2)*(L : ℝ)⌋₊
          let l := L-k
          let dA := k*Real.log ((1+r)/(1-compensation M q r)) +
            l*Real.log ((1-r)/(1+compensation M q r)) - Real.log (((M-q : ℕ) : ℝ)/q)
          Real.log (7/8) ≤ -dA → -dA ≤ Real.log (9/8) →
          let c := Real.exp (-1/((1+r)/2)-1)*Real.exp (-1/((1-r)/2)-1) /
            (Real.sqrt ((3/2)*((1+r)/2))*Real.sqrt ((3/2)*((1-r)/2)))
          let C := 2/Real.sqrt (((1+r)/2)*((1-r)/2))
          let m := (q : ℝ)*rowReference S r L i (k,l)
          (∑ o : Obs M (2*M*L) e,
            let V := nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)
            let R := (V.filter fun u => count e o u.val 1 = k).card
            let U := (V.filter fun u => count e o u.val (-1) = l).card
            if ¬(3*c*q/L ≤ V.card ∧ (V.card : ℝ) ≤ 5*C*q/L ∧
                3/8*(V.card : ℝ) ≤ R ∧ (R : ℝ) ≤ 5/8*(V.card : ℝ) ∧
                3/8*(V.card : ℝ) ≤ U ∧ (U : ℝ) ≤ 5/8*(V.card : ℝ) ∧
                ((nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e o k l 0 \ S.val).card : ℝ)
                  ≤ 5/12*(V.card : ℝ) ∧
                (∀ t : ℕ, 2 ≤ V.card →
                  (∑ x : Obs M (2*M*L) e,
                    if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o ∧
                        nativeRectangleACount S e x k l (⟨x,rfl⟩ : Fiber S e x) = t
                    then probability r e S x else 0) /
                    (∑ x : Obs M (2*M*L) e,
                      if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o
                      then probability r e S x else 0) ≤ K/Real.sqrt V.card))
            then probability r e S o else 0) ≤ 540/m+1215*(A*(L : ℝ)^3/M) := by
  classical
  obtain ⟨A,M₀,η₀,hA,hM₀,hη₀,h⟩ := native_signal_background_occupancy κ hκ hκ1
  obtain ⟨K,hKpos,hK⟩ := hypergeometric_balanced_max_atom (3/8) (by norm_num) (by norm_num)
  refine ⟨A,M₀,η₀,K,hA,hM₀,hη₀,hKpos,?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e i j hi hj hplus hminus
  dsimp only
  intro hdlo hdhi
  let k := ⌊((1+r)/2)*(L : ℝ)⌋₊
  let l := L-k
  let c := Real.exp (-1/((1+r)/2)-1)*Real.exp (-1/((1-r)/2)-1) /
    (Real.sqrt ((3/2)*((1+r)/2))*Real.sqrt ((3/2)*((1-r)/2)))
  let C := 2/Real.sqrt (((1+r)/2)*((1-r)/2))
  let m := (q : ℝ)*rowReference S r L i (k,l)
  have hm := floored_signal_reference_mass S r hr (by linarith only [hrκ,hκ]) hL i hi hplus hminus
  dsimp only at hm
  have hml : c*(q : ℝ)/L ≤ m := by
    have hh := mul_le_mul_of_nonneg_left hm.1 (by positivity : (0 : ℝ) ≤ q)
    simpa only [c,m,k,l,div_div,mul_div_assoc,div_mul_eq_mul_div,mul_comm,mul_left_comm,mul_assoc] using hh
  have hmu : m ≤ C*(q : ℝ)/L := by
    have hh := mul_le_mul_of_nonneg_left hm.2 (by positivity : (0 : ℝ) ≤ q)
    simpa only [C,m,k,l,div_div,mul_div_assoc,div_mul_eq_mul_div,mul_comm,mul_left_comm,mul_assoc] using hh
  have hb := h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e i j hi hj
    k l rfl rfl hplus hminus hdlo hdhi
  apply le_trans _ hb
  apply sum_le_sum
  intro o _
  by_cases hg : (∀ a : Fin 4,
      3/4*m ≤ ((nativeCalibrationCells S e o k l a).card : ℝ) ∧
      ((nativeCalibrationCells S e o k l a).card : ℝ) ≤ 5/4*m) ∧
      3/4*m ≤ ((nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e o k l 0 \ S.val).card : ℝ) ∧
      ((nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e o k l 0 \ S.val).card : ℝ) ≤ 5/4*m
  · have hn := native_occupancy_geometry S e o k l m hg.1 hg.2.2
    dsimp only at hn
    have hlo := (mul_le_mul_of_nonneg_left hml (by norm_num : (0 : ℝ) ≤ 3)).trans hn.1
    have hhi := hn.2.1.trans (mul_le_mul_of_nonneg_left hmu (by norm_num : (0 : ℝ) ≤ 5))
    letI : Fintype (Sites (2*M*L) e) := by cases e <;> unfold Sites <;> infer_instance
    let V := nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)
    let R := (V.filter fun u => count e o u.val 1 = k).card
    let U := (V.filter fun u => count e o u.val (-1) = l).card
    have hatom (t : ℕ) (hN : 2 ≤ V.card) :
        (∑ x : Obs M (2*M*L) e,
          if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o ∧
              nativeRectangleACount S e x k l (⟨x,rfl⟩ : Fiber S e x) = t
          then probability r e S x else 0) /
          (∑ x : Obs M (2*M*L) e,
            if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o
            then probability r e S x else 0) ≤ K/Real.sqrt V.card := by
      have he := full_native_four_cell_conditional_law S r e o hq hqm hr
        (by linarith only [hrκ,hκ]) (by unfold compensation; positivity)
        (by linarith only [hcκ,hκ]) k l t
      have hb := hK V.card R U t hN (card_filter_le V _) (card_filter_le V _)
        hn.2.2.1 (by norm_num; exact hn.2.2.2.1)
        hn.2.2.2.2.1 (by norm_num; exact hn.2.2.2.2.2.1)
      dsimp only at he
      rw [he]
      exact hb
    have hgood : 3*c*q/L ≤ V.card ∧ (V.card : ℝ) ≤ 5*C*q/L ∧
        3/8*(V.card : ℝ) ≤ R ∧ (R : ℝ) ≤ 5/8*(V.card : ℝ) ∧
        3/8*(V.card : ℝ) ≤ U ∧ (U : ℝ) ≤ 5/8*(V.card : ℝ) ∧
        ((nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e o k l 0 \ S.val).card : ℝ)
          ≤ 5/12*(V.card : ℝ) ∧
        (∀ t : ℕ, 2 ≤ V.card →
          (∑ x : Obs M (2*M*L) e,
            if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o ∧
                nativeRectangleACount S e x k l (⟨x,rfl⟩ : Fiber S e x) = t
            then probability r e S x else 0) /
            (∑ x : Obs M (2*M*L) e,
              if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o
              then probability r e S x else 0) ≤ K/Real.sqrt V.card) := by
      refine ⟨?_,?_,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,hn.2.2.2.2.2.1,
        hn.2.2.2.2.2.2,hatom⟩
      · simpa only [mul_div_assoc,mul_assoc,V] using hlo
      · simpa only [mul_div_assoc,mul_assoc,V] using hhi
    change (if ¬_ then _ else _) ≤ (if ¬_ then _ else _)
    simp only [k,l,c,C,V,R,U,m,nativeRectangleRows,nativeRectangleACount] at hgood hg ⊢
    simp only [hgood,hg,true_and,and_self,forall_const,not_true_eq_false,if_false]
    split_ifs with hbad
    · exact le_rfl
    · exfalso
      apply hbad
      intro t hN
      convert hatom t hN using 1 <;>
        try simp only [k,l,V,nativeRectangleRows,nativeRectangleACount]
      all_goals congr 3 <;> first | exact Subsingleton.elim _ _ | (ext y <;> simp)
  · have hp := (finite_support_bayes (s := 2*M*L) hq hqm hr
      (by linarith only [hrκ,hκ]) (by
        unfold compensation
        positivity) (by linarith only [hcκ,hκ]) e).2.2.1 S o
    change (if ¬_ then _ else _) ≤ (if ¬_ then _ else _)
    simp only [k,l,c,C,m,nativeRectangleRows,nativeRectangleACount] at hg ⊢
    simp only [hg,not_false_eq_true,if_true]
    split_ifs <;> first | exact le_rfl | exact hp.1.le
end
end D5.S3.Estimation.TimeArrow.NativeRectangleGeometry
