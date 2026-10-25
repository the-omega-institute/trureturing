/-
TEMPORARY EXACT-CHECK CANDIDATE -- UNCOMPILED.

The target below is the local analytic part of the original Section 71.3:
actual original six-slot cosine/extended-angle readouts at two explicit
centers, followed by one full-six-coordinate neighborhood radius.

There is no global face-pairing or quotient-edge theorem in this file.
No result about the 629 equal-middle-length family is imported or assumed.
All helper applications and center normalizations here are bind-only evidence,
not proposed new canonical mathematics or an admission/novelty claim.

The temporary probe calls two existing private theorems directly using
OpenPrivate; it does not copy them or export aliases. A canonical consumer
must instead publicize their original declarations under the existing
visibility/frozen-state workflow and verify the affected consumers.
-/

import Batteries.Tactic.OpenPrivate
import D5.S3.Geometry.Hyperideal.PositiveFlatClassification
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter
open scoped Topology
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
open D5.S3.Geometry.Hyperideal.PositiveFlatClassification

open private raw_cos_lt_of_square clipped_arccos_lower
  from D5.S3.Geometry.Hyperideal.TwoLengthAngleSum

namespace Section71OpenNeighborhood685Temporary

abbrev Coordinates := Fin 6 → ℝ

def shortCenter : ℝ := (579 - 221 * Real.sqrt 5) / 84
def F0 : Coordinates := ![22, 10, 10, 22, 10, 10]
def centerFamily (u : ℝ) : Coordinates := ![22, 10, 10, u, 10, 10]
def G0 : Coordinates := centerFamily shortCenter

def Middle (q : Fin 6) : Prop := q ≠ 0 ∧ q ≠ 3
def Positive (x : Coordinates) : Prop := ∀ q, 1 < x q

def flatLower (q : Fin 6) : ℝ := if q = 0 ∨ q = 3 then 21 else 9
def flatUpper (q : Fin 6) : ℝ := if q = 0 ∨ q = 3 then 23 else 11
def genuineLower (q : Fin 6) : ℝ := if q = 0 then 21 else if q = 3 then 1 else 9
def genuineUpper (q : Fin 6) : ℝ := if q = 0 then 23 else if q = 3 then 2 else 11

def FlatProfile (x : Coordinates) : Prop :=
  ∀ q, flatLower q < x q ∧ x q < flatUpper q

def GenuineProfile (x : Coordinates) : Prop :=
  ∀ q, genuineLower q < x q ∧ x q < genuineUpper q

def FlatPattern (x : Coordinates) : Prop :=
  ∀ q, extendedAngle x q = if q = 0 ∨ q = 3 then Real.pi else 0

def MiddleRawWindow (x : Coordinates) : Prop :=
  ∀ q, Middle q → 0 < rawCos x q ∧ rawCos x q < (1 : ℝ) / 2

def MiddleAngleWindow (x : Coordinates) : Prop :=
  ∀ q, Middle q → Real.pi / 3 < extendedAngle x q ∧
    extendedAngle x q < Real.pi / 2

def FlatStable (x : Coordinates) : Prop :=
  FlatProfile x ∧ Positive x ∧ rawCos x 0 < -1 ∧ FlatPattern x

def GenuineStable (x : Coordinates) : Prop :=
  GenuineProfile x ∧ Positive x ∧ Genuine x ∧
    (∀ q, 0 < extendedAngle x q ∧ extendedAngle x q < Real.pi) ∧
    MiddleRawWindow x ∧ MiddleAngleWindow x

/- The short coordinate is strictly inside I_S=(1,2), using only exact
   ordered-real square-root comparisons. -/
theorem shortCenter_bounds : 1 < shortCenter ∧ shortCenter < 2 := by
  have hlo : (2 : ℝ) < Real.sqrt 5 :=
    (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2)).2 (by norm_num)
  have hhi : Real.sqrt 5 < (495 : ℝ) / 221 :=
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 495 / 221)).2 (by norm_num)
  unfold shortCenter
  constructor <;> linarith

theorem F0_positive : Positive F0 := by
  intro q
  fin_cases q <;> norm_num [F0]

theorem centerFamily_positive (u : ℝ) (hu : 1 < u) : Positive (centerFamily u) := by
  intro q
  fin_cases q <;> norm_num [centerFamily] <;> exact hu

theorem G0_positive : Positive G0 :=
  centerFamily_positive shortCenter shortCenter_bounds.1

/- At F0 all six actual raw cosines are determined, including the four
   values above 1 that are clipped to zero angles. -/
theorem F0_rawCos (q : Fin 6) :
    rawCos F0 q = if q = 0 ∨ q = 3 then -(262 : ℝ) / 221 else 230 / 221 := by
  have hs : Real.sqrt (5083 : ℝ) * Real.sqrt 5083 = 5083 :=
    Real.mul_self_sqrt (by norm_num)
  fin_cases q <;>
    norm_num [rawCos, F0, frame, cosine, numerator, rad, div_div, hs]

private theorem axis0_data (u : ℝ) :
    rawNum (centerFamily u) 0 = 4600 - 483 * u ∧
      leftRad (centerFamily u) 0 = 5083 ∧
      rightRad (centerFamily u) 0 = 5083 := by
  constructor
  · norm_num [rawNum, centerFamily, frame, numerator] <;> ring
  · constructor <;> norm_num [leftRad, rightRad, centerFamily, frame, rad]

private theorem axis3_data (u : ℝ) :
    rawNum (centerFamily u) 3 = (u + 1) * (222 - 22 * u) ∧
      leftRad (centerFamily u) 3 = (u + 1) * (u + 199) ∧
      rightRad (centerFamily u) 3 = (u + 1) * (u + 199) := by
  constructor
  · norm_num [rawNum, centerFamily, frame, numerator] <;> ring
  · constructor <;>
      norm_num [leftRad, rightRad, centerFamily, frame, rad] <;> ring

private theorem middle_data (u : ℝ) (q : Fin 6) (hq : Middle q) :
    rawNum (centerFamily u) q = 230 * (u + 1) ∧
      leftRad (centerFamily u) q = (u + 1) * (u + 199) ∧
      rightRad (centerFamily u) q = 5083 := by
  constructor
  · fin_cases q <;> simp [Middle] at hq <;>
      norm_num [rawNum, centerFamily, frame, numerator] <;> ring
  · constructor
    · fin_cases q <;> simp [Middle] at hq <;>
        norm_num [leftRad, centerFamily, frame, rad] <;> ring
    · fin_cases q <;> simp [Middle] at hq <;>
        norm_num [rightRad, centerFamily, frame, rad]

theorem centerFamily_axis0_rawCos (u : ℝ) :
    rawCos (centerFamily u) 0 = (4600 - 483 * u) / 5083 := by
  obtain ⟨hN, hL, hR⟩ := axis0_data u
  have hs : Real.sqrt (5083 : ℝ) * Real.sqrt 5083 = 5083 :=
    Real.mul_self_sqrt (by norm_num)
  change rawNum (centerFamily u) 0 / Real.sqrt (leftRad (centerFamily u) 0) /
    Real.sqrt (rightRad (centerFamily u) 0) = _
  rw [hN, hL, hR, div_div, hs]

theorem centerFamily_axis3_rawCos (u : ℝ) (hu : 1 < u) :
    rawCos (centerFamily u) 3 = (222 - 22 * u) / (u + 199) := by
  obtain ⟨hN, hL, hR⟩ := axis3_data u
  have hp : 0 < u + 1 := by linarith
  have hd : 0 < u + 199 := by linarith
  have hD : 0 ≤ (u + 1) * (u + 199) := (mul_pos hp hd).le
  change rawNum (centerFamily u) 3 / Real.sqrt (leftRad (centerFamily u) 3) /
    Real.sqrt (rightRad (centerFamily u) 3) = _
  rw [hN, hL, hR, div_div, Real.mul_self_sqrt hD]
  field_simp [hp.ne', hd.ne'] <;> ring

/- This family is used ONLY to certify the one center G0. No neighborhood
   theorem below restricts nearby vectors to centerFamily or equal middles. -/
theorem centerFamily_middle_rawCos_window (u : ℝ) (hu : 1 < u ∧ u < 2)
    (q : Fin 6) (hq : Middle q) :
    0 < rawCos (centerFamily u) q ∧ rawCos (centerFamily u) q < (1 : ℝ) / 2 := by
  have hx := centerFamily_positive u hu.1
  obtain ⟨hN, hL, hR⟩ := middle_data u q hq
  have hNp : 0 < rawNum (centerFamily u) q := by
    rw [hN]
    have : 0 < u + 1 := by linarith
    positivity
  have hLp : 0 < leftRad (centerFamily u) q :=
    rad_positive _ _ _ (hx _) (hx _) (hx _)
  have hRp : 0 < rightRad (centerFamily u) q :=
    rad_positive _ _ _ (hx _) (hx _) (hx _)
  constructor
  · change 0 < rawNum (centerFamily u) q /
      Real.sqrt (leftRad (centerFamily u) q) /
      Real.sqrt (rightRad (centerFamily u) q)
    exact div_pos (div_pos hNp (Real.sqrt_pos.mpr hLp)) (Real.sqrt_pos.mpr hRp)
  · apply raw_cos_lt_of_square (centerFamily u) hx q ((1 : ℝ) / 2) (by norm_num)
    rw [hN, hL, hR]
    have hp : 0 < u + 1 := by linarith
    have hgap : 0 < 799917 - 206517 * u := by linarith
    nlinarith only [mul_pos hp hgap]

theorem centerFamily_all_rawCos_bounds (u : ℝ) (hu : 1 < u ∧ u < 2) :
    ∀ q, 0 < rawCos (centerFamily u) q ∧ rawCos (centerFamily u) q < 1 := by
  intro q
  by_cases h0 : q = 0
  · subst q
    rw [centerFamily_axis0_rawCos]
    constructor
    · exact div_pos (by linarith) (by norm_num)
    · apply (div_lt_one (by norm_num : (0 : ℝ) < 5083)).2
      linarith
  by_cases h3 : q = 3
  · subst q
    rw [centerFamily_axis3_rawCos u hu.1]
    have hd : 0 < u + 199 := by linarith
    constructor
    · exact div_pos (by linarith) hd
    · apply (div_lt_one hd).2
      linarith
  have hm := centerFamily_middle_rawCos_window u hu q ⟨h0, h3⟩
  exact ⟨hm.1, hm.2.trans (by norm_num)⟩

theorem G0_all_rawCos_bounds : ∀ q, 0 < rawCos G0 q ∧ rawCos G0 q < 1 :=
  centerFamily_all_rawCos_bounds shortCenter shortCenter_bounds

theorem G0_middle_raw_window : MiddleRawWindow G0 :=
  centerFamily_middle_rawCos_window shortCenter shortCenter_bounds

/- Direct application of the original clipped-arccos comparison and the
   principal upper-half-angle branch, not an assumed response formula. -/
theorem actual_middle_angle_window (x : Coordinates) (q : Fin 6)
    (hraw : 0 < rawCos x q ∧ rawCos x q < (1 : ℝ) / 2) :
    Real.pi / 3 < extendedAngle x q ∧ extendedAngle x q < Real.pi / 2 := by
  have hlo : Real.pi / 3 < extendedAngle x q := by
    exact clipped_arccos_lower (rawCos x q) (Real.pi / 3)
      (by positivity) (by linarith [Real.pi_pos])
      (by rw [Real.cos_pi_div_three]; norm_num)
      (by rw [Real.cos_pi_div_three]; exact hraw.2)
  have hclip : max (-1) (min (rawCos x q) 1) = rawCos x q := by
    rw [min_eq_left (by linarith [hraw.2]), max_eq_right (by linarith [hraw.1])]
  refine ⟨hlo, ?_⟩
  rw [extendedAngle, hclip]
  exact Real.arccos_lt_pi_div_two.mpr hraw.1

theorem actual_flat_pattern (x : Coordinates) (hx : Positive x)
    (hraw : rawCos x 0 < -1) : FlatPattern x := by
  have hs : Sector x (0 : Fin 3) := hraw.le
  simpa [FlatPattern] using
    ((positive_classification x hx).2.2 (0 : Fin 3)).2.mp hs

theorem flatProfile_positive (x : Coordinates) (hx : FlatProfile x) : Positive x := by
  intro q
  have hlo : (1 : ℝ) ≤ flatLower q := by
    unfold flatLower
    split_ifs <;> norm_num
  exact lt_of_le_of_lt hlo (hx q).1

theorem genuineProfile_positive (x : Coordinates) (hx : GenuineProfile x) : Positive x := by
  intro q
  have hlo : (1 : ℝ) ≤ genuineLower q := by
    unfold genuineLower
    split_ifs <;> norm_num
  exact lt_of_le_of_lt hlo (hx q).1

theorem F0_profile : FlatProfile F0 := by
  intro q
  fin_cases q <;> norm_num [flatLower, flatUpper, F0]

theorem G0_profile : GenuineProfile G0 := by
  intro q
  fin_cases q <;>
    norm_num [genuineLower, genuineUpper, G0, centerFamily] <;>
    exact shortCenter_bounds

theorem F0_stable : FlatStable F0 := by
  have hraw : rawCos F0 0 < -1 := by rw [F0_rawCos]; norm_num
  exact ⟨F0_profile, F0_positive, hraw, actual_flat_pattern F0 F0_positive hraw⟩

theorem G0_stable : GenuineStable G0 := by
  have hg : Genuine G0 := fun q =>
    ⟨by linarith [(G0_all_rawCos_bounds q).1], (G0_all_rawCos_bounds q).2⟩
  refine ⟨G0_profile, G0_positive, hg, (positive_classification G0 G0_positive).1.mp hg,
    G0_middle_raw_window, ?_⟩
  intro q hq
  exact actual_middle_angle_window G0 q (G0_middle_raw_window q hq)

/- Actual, unconditional certificates for BOTH fixed centers. -/
theorem exact_center_readouts :
    (∀ q, rawCos F0 q =
      if q = 0 ∨ q = 3 then -(262 : ℝ) / 221 else 230 / 221) ∧
    FlatStable F0 ∧
    (∀ q, 0 < rawCos G0 q ∧ rawCos G0 q < 1) ∧
    GenuineStable G0 :=
  ⟨F0_rawCos, F0_stable, G0_all_rawCos_bounds, G0_stable⟩

/- Full six-coordinate continuity. None of the six coordinate projections
   is constrained to agree with another projection. -/
theorem rawCos_continuousAt (x : Coordinates) (hx : Positive x) (q : Fin 6) :
    ContinuousAt (fun y : Coordinates => rawCos y q) x := by
  have hn : Continuous (fun y : Coordinates => rawNum y q) := by
    unfold rawNum numerator
    fun_prop
  have hl : Continuous (fun y : Coordinates => leftRad y q) := by
    unfold leftRad rad
    fun_prop
  have hr : Continuous (fun y : Coordinates => rightRad y q) := by
    unfold rightRad rad
    fun_prop
  have hln : Real.sqrt (leftRad x q) ≠ 0 :=
    (Real.sqrt_pos.mpr (rad_positive _ _ _ (hx _) (hx _) (hx _))).ne'
  have hrn : Real.sqrt (rightRad x q) ≠ 0 :=
    (Real.sqrt_pos.mpr (rad_positive _ _ _ (hx _) (hx _) (hx _))).ne'
  change ContinuousAt
    (fun y : Coordinates => rawNum y q / Real.sqrt (leftRad y q) /
      Real.sqrt (rightRad y q)) x
  exact (hn.continuousAt.div (Real.continuous_sqrt.comp hl).continuousAt hln).div
    (Real.continuous_sqrt.comp hr).continuousAt hrn

theorem profile_eventually (a lower upper : Coordinates)
    (ha : ∀ q, lower q < a q ∧ a q < upper q) :
    ∀ᶠ x : Coordinates in 𝓝 a, ∀ q, lower q < x q ∧ x q < upper q := by
  apply Filter.eventually_all.mpr
  intro q
  have hc : ContinuousAt (fun x : Coordinates => x q) a :=
    (continuous_apply q).continuousAt
  exact (continuousAt_const.eventually_lt hc (ha q).1).and
    (hc.eventually_lt continuousAt_const (ha q).2)

theorem F0_stable_eventually : ∀ᶠ x : Coordinates in 𝓝 F0, FlatStable x := by
  have hp : ∀ᶠ x : Coordinates in 𝓝 F0, FlatProfile x :=
    profile_eventually F0 flatLower flatUpper F0_profile
  have hbase : rawCos F0 0 < -1 := by rw [F0_rawCos]; norm_num
  have hr : ∀ᶠ x : Coordinates in 𝓝 F0, rawCos x 0 < -1 :=
    (rawCos_continuousAt F0 F0_positive 0).eventually_lt continuousAt_const hbase
  filter_upwards [hp, hr] with x hx hraw
  have hxpos := flatProfile_positive x hx
  exact ⟨hx, hxpos, hraw, actual_flat_pattern x hxpos hraw⟩

theorem G0_stable_eventually : ∀ᶠ x : Coordinates in 𝓝 G0, GenuineStable x := by
  have hp : ∀ᶠ x : Coordinates in 𝓝 G0, GenuineProfile x :=
    profile_eventually G0 genuineLower genuineUpper G0_profile
  have hg : ∀ᶠ x : Coordinates in 𝓝 G0, Genuine x := by
    apply Filter.eventually_all.mpr
    intro q
    have hc := rawCos_continuousAt G0 G0_positive q
    have hlo : (-1 : ℝ) < rawCos G0 q := by linarith [(G0_all_rawCos_bounds q).1]
    exact (continuousAt_const.eventually_lt hc hlo).and
      (hc.eventually_lt continuousAt_const (G0_all_rawCos_bounds q).2)
  have hm : ∀ᶠ x : Coordinates in 𝓝 G0, MiddleRawWindow x := by
    apply Filter.eventually_all.mpr
    intro q
    by_cases hq : Middle q
    · have hc := rawCos_continuousAt G0 G0_positive q
      have hbase := G0_middle_raw_window q hq
      exact ((continuousAt_const.eventually_lt hc hbase.1).and
        (hc.eventually_lt continuousAt_const hbase.2)).mono
          (fun x hx _ => hx)
    · exact Filter.Eventually.of_forall (fun _ h => (hq h).elim)
  filter_upwards [hp, hg, hm] with x hx hxg hxm
  have hxpos := genuineProfile_positive x hx
  refine ⟨hx, hxpos, hxg, (positive_classification x hxpos).1.mp hxg, hxm, ?_⟩
  intro q hq
  exact actual_middle_angle_window x q (hxm q hq)

theorem coordinate_radius_of_eventually (a : Coordinates) (P : Coordinates → Prop)
    (hP : ∀ᶠ x in 𝓝 a, P x) :
    ∃ δ > 0, ∀ x : Coordinates, (∀ q, |x q - a q| < δ) → P x := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hP
  refine ⟨δ, hδ, fun x hx => hball ?_⟩
  exact (dist_pi_lt_iff hδ).mpr (by simpa only [Real.dist_eq] using hx)

/- No angle inequalities or zero-contribution assumptions occur among the
   premises: ALL readouts follow from the six coordinatewise bounds alone.
   The radius is chosen before, and independently of, any block collection.
   Intervals in FlatProfile/GenuineProfile are I_S=(1,2), I_M=(9,11),
   I_L=(21,23). Their separation does not identify distinct global labels.
 -/
theorem uniform_full_six_coordinate_neighborhood :
    ∃ ε > 0,
      (∀ x : Coordinates, (∀ q, |x q - F0 q| < ε) → FlatStable x) ∧
      (∀ x : Coordinates, (∀ q, |x q - G0 q| < ε) → GenuineStable x) := by
  obtain ⟨δF, hδF, hF⟩ :=
    coordinate_radius_of_eventually F0 FlatStable F0_stable_eventually
  obtain ⟨δG, hδG, hG⟩ :=
    coordinate_radius_of_eventually G0 GenuineStable G0_stable_eventually
  refine ⟨min δF δG, lt_min hδF hδG, ?_, ?_⟩
  · intro x hx
    apply hF x
    intro q
    exact lt_of_lt_of_le (hx q) (min_le_left δF δG)
  · intro x hx
    apply hG x
    intro q
    exact lt_of_lt_of_le (hx q) (min_le_right δF δG)

#print axioms exact_center_readouts
#print axioms uniform_full_six_coordinate_neighborhood

end Section71OpenNeighborhood685Temporary

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``Section71OpenNeighborhood685Temporary.exact_center_readouts,
      ``Section71OpenNeighborhood685Temporary.uniform_full_six_coordinate_neighborhood] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"Section71-697 declaration absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"Section71-697 disallowed axiom {ax} for {name}"
    Lean.logInfo m!"Section71-697 CHECKED {name} axioms={axioms}"
