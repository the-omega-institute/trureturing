/- GID: D5/S3/Estimation/TimeArrow/OriginalScoreWindow
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/OriginalScoreWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The complete original score window and its zero posterior group are identified on the minimal environment. -/

import D5.S3.Estimation.TimeArrow.NativeAnchoredSmallBall
import D5.S3.Estimation.TimeArrow.NativeGlobalRectangleEnvironment
import D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates

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

open scoped Classical in
set_option maxHeartbeats 4000000 in
/-- The original complete window posterior has the registered arithmetic
bound, conditioned on the full native minimal readout. A cut and full-root
anchor select an environment value; neither changes the posterior law. -/
theorem original_full_env_small_ball :
    ∃ Cpost V0 : ℝ, 0 < Cpost ∧ 0 < V0 ∧
    ∀ (r v : ℝ), 0 < r → r < 1 → 0 < v →
    ∃ a γ η c Cfb : ℝ, 0 < a ∧ 0 < γ ∧ γ ≤ 1/32 ∧ 0 < η ∧ 0 < c ∧ 0 < Cfb ∧
    ∀ ell : ℤ, ell ≠ 0 → ∃ Cell : ℝ, 0 < Cell ∧
    ∀ (M q s : ℕ) (S : Support M q) (e : Experiment) (o : Obs M s e),
    ∀ [Fintype (Sites s e)], ∀ (k l H Q P : ℕ) (center width ζ : ℝ),
      1 ≤ q → q < M → 0 ≤ compensation M q r → compensation M q r ≤ 1/2 →
      letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
      let z : Fiber S e o := ⟨o,rfl⟩
      let All : Support M M := ⟨univ,by simp⟩
      let bg : ℝ := (nativeCalibrationCells All e o k l 0 \ S.val).card
      let z0 := (k : ℝ)*Real.log ((1+r)/(1-compensation M q r))+
        (l : ℝ)*Real.log ((1-r)/(1+compensation M q r))
      let V := nativeRectangleRows S e o k l z
      let N : ℝ := V.card
      let R : ℝ := (V.filter fun i => count e o i.val 1 = k).card
      let U : ℝ := (V.filter fun i => count e o i.val (-1) = l).card
      let s0 := c*(N/q)
      1 < V.card → N/4 ≤ R → R ≤ 3*N/4 → N/4 ≤ U → U ≤ 3*N/4 →
      max 4 (32/(a*v)) ≤ Real.sqrt N →
      N/q ≤ v/2 → N/q ≤ v*Real.log 2/8 → a*N/q < η →
      |compensation M q r| < η → bg ≤ N → s0 ≤ 1 → V0 ≤ v*q/4 →
      1 ≤ γ*s0*Real.sqrt N →
      k+l+2 ≤ H → P < Q → 0 < width → 0 < ζ →
      Real.log (1+r) = (-Real.log (1-r))*((P : ℝ)/Q+ζ) →
      (-Real.log (1-r))*ζ*(H+k+l)+2*compensation M q r*H+
        |(k : ℝ)*Real.log (1+r)+l*Real.log (1-r)-center| ≤ width/2 →
      (Q : ℝ)*width ≤ (-Real.log (1-r))/4 →
      ∀ (anchor : Fiber S e o) (xStar : ℝ),
        nativeMinimalRectangleReadout S e o k l anchor = nativeMinimalRectangleReadout S e o k l z →
        originalCountCut H e anchor.val →
        (∑ i : Fin M,Real.sigmoid (xStar+(score q r e anchor.val i-z0))) = q →
        v*q ≤ ∑ i : Fin M,Real.sigmoid (xStar+(score q r e anchor.val i-z0))*
          (1-Real.sigmoid (xStar+(score q r e anchor.val i-z0))) →
        |xStar| ≤ a*N/(4*q) →
        |(nativeRectangleACount S e o k l anchor : ℝ)-U*R/N| ≤ 2*Real.sqrt N →
        ∀ L τ : ℝ,0 < L → 0 ≤ τ →
          (∑ x : Obs M s e,if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o ∧
            (∃ b : ℤ,|(ell : ℝ)*(1/2-originalGroupPosteriorMean q r center width z0 e x)-b| ≤ τ)
            then probability r e S x else 0)/
            (∑ x : Obs M s e,if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o
              then probability r e S x else 0) ≤
            Cell*(L*(s0+τ)+(1+τ/s0)/Real.sqrt N+L^(-2 : ℤ)) := by
  classical
  obtain ⟨Cpost,V0,hCpost,hV0,hmain⟩ := native_anchored_posterior_small_ball
  refine ⟨Cpost,V0,hCpost,hV0,?_⟩
  intro r v hr hr1 hv
  obtain ⟨a,γ,η,c,Cfb,ha,hγ,hγsmall,hη,hc,hCfb,hmain⟩ := hmain r v hr hr1 hv
  refine ⟨a,γ,η,c,Cfb,ha,hγ,hγsmall,hη,hc,hCfb,?_⟩
  intro ell hell
  obtain ⟨Cell,hCell,hmain⟩ := hmain ell hell
  refine ⟨Cell,hCell,?_⟩
  intro M q s S e o _ k l H Q P center width ζ hq hqm hε hεhalf
  letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
  dsimp only
  let z : Fiber S e o := ⟨o,rfl⟩
  let All : Support M M := ⟨univ,by simp⟩
  let z0 := (k : ℝ)*Real.log ((1+r)/(1-compensation M q r))+
    (l : ℝ)*Real.log ((1-r)/(1+compensation M q r))
  let Env := univ.filter fun y : Fiber S e o =>
    nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z
  intro hN hRlo hRhi hUlo hUhi hlarge hsize hsize' hηscale hεη hbgN hs1 hV hscale
    hH hPQ hwidth hζ hlog herror hgrid anchor xStar henv hcut hroot hvar hx hstar L τ hL hτ
  have hε1 : compensation M q r < 1 := by linarith only [hεhalf]
  have hnative := hmain M q s S e o k l z hq hqm hε hε1 hN hRlo hRhi hUlo hUhi
    hlarge hsize hsize' hηscale hεη hbgN hs1 hV hscale
    anchor xStar henv hroot hvar hx hstar L τ hL hτ
  have hmu (y : Fiber S e o) (hy : y ∈ Env) :
      originalGroupPosteriorMean q r center width z0 e y.val =
        ∑ i ∈ nativeCalibrationCells All e y.val k l 0,inclusion q r e y.val i := by
    have hyenv : nativeMinimalRectangleReadout S e o k l y =
        nativeMinimalRectangleReadout S e o k l z := (mem_filter.mp hy).2
    have hcuty := (original_count_cut_same_environment S e o k l H y anchor
      (hyenv.trans henv.symm) hH).mpr hcut
    unfold originalGroupPosteriorMean
    rw [original_zero_group_eq_all_cell q r center width ζ e y.val k l H Q P
      hr hr1 hPQ hζ hε hεhalf (by omega) hcuty hwidth hlog herror hgrid]
  let Pred := fun x : Obs M s e => ∃ b : ℤ,
    |(ell : ℝ)*(1/2-originalGroupPosteriorMean q r center width z0 e x)-b| ≤ τ
  have heq := full_native_conditional_mass_eq S r e o hq hqm hr hr1 hε hε1 k l Pred
  change (∑ x : Obs M s e,if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o ∧ Pred x
    then probability r e S x else 0)/
    (∑ x : Obs M s e,if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o
      then probability r e S x else 0) ≤ _
  dsimp only at heq
  have hpred : Env.filter (fun y => Pred y.val) = Env.filter (fun y => ∃ b : ℤ,
      |(ell : ℝ)*(1/2-(∑ i ∈ nativeCalibrationCells All e y.val k l 0,inclusion q r e y.val i))-b| ≤ τ) := by
    apply filter_congr
    intro y hy
    dsimp only [Pred]
    rw [hmu y hy]
  let N : ℝ := (nativeRectangleRows S e o k l z).card
  let B := Cell*(L*(c*(N/q)+τ)+(1+τ/(c*(N/q)))/Real.sqrt N+L^(-2 : ℤ))
  have hf : conditionalFiberMass S r e o (Env.filter fun y => Pred y.val)/
      conditionalFiberMass S r e o Env ≤ B := by
    rw [hpred]
    simpa only [Env,All,N,B,z] using hnative
  have heqEnv : (∑ x : Obs M s e,if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o ∧ Pred x
      then probability r e S x else 0)/
      (∑ x : Obs M s e,if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o
        then probability r e S x else 0) =
      conditionalFiberMass S r e o (Env.filter fun y => Pred y.val)/conditionalFiberMass S r e o Env := by
    convert heq using 1 <;> congr 1
    all_goals first
      | (apply sum_congr rfl; intro x _; split_ifs <;> rfl)
      | (congr 1; ext y; simp only [Env,z,mem_filter,mem_univ,true_and])
  simpa only [N,B,z] using heqEnv.le.trans hf

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
