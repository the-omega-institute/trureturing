import D5.S3.Geometry.Hyperideal.FourCycleAnisotropicMeanResponse
import D5.S3.Geometry.Hyperideal.PositiveFlatClassification
import D5.S3.Geometry.Hyperideal.Section71AngleWindow
import D5.S3.Geometry.Hyperideal.EdgeStarTransitions
import D5.S3.PrimeForms.Crossing.GlideCrossingParity
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
open scoped Matrix Classical

namespace Section71ExactCheck620

open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
open D5.S3.Geometry.Hyperideal.PositiveFlatClassification
open D5.S3.Geometry.Hyperideal.Section71AngleWindow
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions

open private Flag Pairing Pairing.mk cross from
  D5.S3.Geometry.Hyperideal.EdgeStarTransitions

/-- The original local order is 01,02,03,23,13,12. -/
def six (r h s : ℝ) : Fin 6 → ℝ := ![r,h,h,s,h,h]

/-- A temporary exact application to the literal genuine block in Section71.1.
All six raw cosine inequalities belong to this same six-length input. -/
theorem literal_local_bridge
    (r h s : ℝ)
    (hh : 1 < h) (hs : 1 < s) (hrh : 1 + 2 * h ≤ r)
    (hg : Genuine (six r h s))
    (htan : Real.tan
      (Real.arccos (cosine r h h s h h) / 2) ≤ (1 : ℝ) / 2) :
    let Q : ℝ := 2 * h ^ 2 / (r - 1)
    let theta : ℝ := Real.arccos (cosine r h h s h h)
    extendedAngle (six r h s) 0 = theta ∧
      s < h ∧
      (Real.cot (theta / 2)) ^ 2 < Q ∧
      (∀ q : Fin 6, q ≠ 0 → q ≠ 3 →
        extendedAngle (six r h s) q = middleAngle h Q theta ∧
          Real.pi / 3 < extendedAngle (six r h s) q ∧
          extendedAngle (six r h s) q < Real.pi / 2) := by
  let Q : ℝ := 2 * h ^ 2 / (r - 1)
  let theta : ℝ := Real.arccos (cosine r h h s h h)
  let beta : ℝ := Real.arccos (cosine h h r h h s)
  change extendedAngle (six r h s) 0 = theta ∧ s < h ∧
    (Real.cot (theta / 2)) ^ 2 < Q ∧
    (∀ q : Fin 6, q ≠ 0 → q ≠ 3 →
      extendedAngle (six r h s) q = middleAngle h Q theta ∧
        Real.pi / 3 < extendedAngle (six r h s) q ∧
        extendedAngle (six r h s) q < Real.pi / 2)
  have hh0 : 0 < h := lt_trans (by norm_num) hh
  have hr : 1 < r := by linarith
  have hrm : 0 < r - 1 := by linarith
  have hrp : 0 < r + 1 := by linarith
  have hQ : 0 < Q := by
    dsimp [Q]
    exact div_pos (by positivity) hrm
  have hQp : 0 < Q + 1 := by linarith
  have hQh : Q ≤ h := by
    dsimp [Q]
    apply (div_le_iff₀ hrm).2
    have hm := mul_le_mul_of_nonneg_left
      (show 2 * h ≤ r - 1 by linarith) hh0.le
    nlinarith
  have haxis : -1 < cosine r h h s h h ∧ cosine r h h s h h < 1 := by
    change -1 < rawCos (six r h s) 0 ∧ rawCos (six r h s) 0 < 1
    exact hg 0
  have htrans : -1 < cosine h h r h h s ∧ cosine h h r h h s < 1 := by
    change -1 < rawCos (six r h s) 1 ∧ rawCos (six r h s) 1 < 1
    exact hg 1
  have htheta_pos : 0 < theta := Real.arccos_pos.mpr haxis.2
  have htheta_lt_pi : theta < Real.pi := Real.arccos_lt_pi.mpr haxis.1
  have hrad : 0 < rad r h h := rad_positive r h h hr hh hh
  have hD : 0 < r - 1 + 2 * h ^ 2 := by positivity
  have hrad_factor : rad r h h = (r + 1) * (r - 1 + 2 * h ^ 2) := by
    dsimp [rad]
    ring
  have hnum_factor : numerator r h h s h h =
      (r + 1) * (2 * h ^ 2 - (r - 1) * s) := by
    dsimp [numerator]
    ring
  have haxis_quotient : cosine r h h s h h =
      (2 * h ^ 2 - (r - 1) * s) / (r - 1 + 2 * h ^ 2) := by
    calc
      cosine r h h s h h = numerator r h h s h h / rad r h h := by
        dsimp only [cosine]
        rw [div_div, ← pow_two, Real.sq_sqrt hrad.le]
      _ = _ := by
        rw [hnum_factor, hrad_factor]
        field_simp [hrp.ne', hD.ne']
        <;> ring
  have hresponse : cosine r h h s h h = (Q - s) / (Q + 1) := by
    rw [haxis_quotient]
    apply (div_eq_div_iff hD.ne' hQp.ne').2
    dsimp [Q]
    field_simp [hrm.ne']
    <;> ring
  have hcos : Real.cos theta = (Q - s) / (Q + 1) := by
    calc
      Real.cos theta = cosine r h h s h h :=
        Real.cos_arccos haxis.1.le haxis.2.le
      _ = _ := hresponse
  have hhalf_sin : 0 < Real.sin (theta / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hhalf_cos : 0 < Real.cos (theta / 2) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith⟩
  have hdouble : Real.cos theta = 2 * Real.cos (theta / 2) ^ 2 - 1 := by
    calc
      Real.cos theta = Real.cos (2 * (theta / 2)) := by congr 1; ring
      _ = _ := Real.cos_two_mul _
  have htrig := Real.sin_sq_add_cos_sq (theta / 2)
  have hcos_mul : Real.cos theta * (Q + 1) = Q - s :=
    (eq_div_iff hQp.ne').mp hcos
  have hhalf_gap : Real.cos (theta / 2) ^ 2 <
      Q * Real.sin (theta / 2) ^ 2 := by
    have hdoubleQ := congrArg (fun z : ℝ => z * (Q + 1)) hdouble
    have htrigQ := congrArg (fun z : ℝ => Q * z) htrig
    nlinarith [hdoubleQ, htrigQ]
  have hQcot : (Real.cot (theta / 2)) ^ 2 < Q := by
    rw [Real.cot_eq_cos_div_sin, div_pow]
    exact (div_lt_iff₀ (sq_pos_of_pos hhalf_sin)).2 hhalf_gap
  have htan_half : Real.sin (theta / 2) / Real.cos (theta / 2) ≤ (1 : ℝ) / 2 := by
    simpa only [Real.tan_eq_sin_div_cos] using htan
  have hhalf_bound : 2 * Real.sin (theta / 2) ≤ Real.cos (theta / 2) := by
    have hb := (div_le_iff₀ hhalf_cos).mp htan_half
    linarith
  have hhalf_bound_sq : (2 * Real.sin (theta / 2)) ^ 2 ≤
      Real.cos (theta / 2) ^ 2 := by
    simpa only [pow_two] using
      (mul_self_le_mul_self (by positivity) hhalf_bound)
  have hcos_pos : 0 < Real.cos theta := by
    nlinarith [htrig, hdouble, hhalf_bound_sq]
  have hsQ : s < Q := by
    have hp : 0 < Q - s := by
      rw [← hcos_mul]
      exact mul_pos hcos_pos hQp
    linarith
  have hshort : s < h := hsQ.trans_le hQh
  have hA : 0 < h ^ 2 - 1 := by nlinarith
  have hden : 0 < Q + h ^ 2 := by positivity
  have hden_factor : Q + h ^ 2 = h ^ 2 * ((r + 1) / (r - 1)) := by
    dsimp [Q]
    field_simp [hrm.ne']
    <;> ring
  have hsqrtA : (Real.sqrt (h ^ 2 - 1)) ^ 2 = h ^ 2 - 1 :=
    Real.sq_sqrt hA.le
  have hfirst :
      (Real.sqrt (h ^ 2 - 1) + Real.sqrt (h ^ 2 - 1)) / (h + h) =
        Real.sqrt (h ^ 2 - 1) / h := by
    field_simp [hh0.ne', (show h + h ≠ 0 by linarith)]
    <;> ring
  have hfirst_sq :
      ((Real.sqrt (h ^ 2 - 1) + Real.sqrt (h ^ 2 - 1)) / (h + h)) ^ 2 =
        (h ^ 2 - 1) / h ^ 2 := by
    rw [hfirst, div_pow, hsqrtA]
  have hfactor_sq :
      (((Real.sqrt (h ^ 2 - 1) + Real.sqrt (h ^ 2 - 1)) / (h + h)) *
        Real.sqrt ((r - 1) / (r + 1))) ^ 2 =
          (h ^ 2 - 1) / (Q + h ^ 2) := by
    rw [mul_pow, hfirst_sq, Real.sq_sqrt (div_nonneg hrm.le hrp.le),
      hden_factor]
    field_simp [hrm.ne', hrp.ne', hh0.ne']
    <;> ring
  have hfactor :
      ((Real.sqrt (h ^ 2 - 1) + Real.sqrt (h ^ 2 - 1)) / (h + h)) *
        Real.sqrt ((r - 1) / (r + 1)) =
          Real.sqrt ((h ^ 2 - 1) / (Q + h ^ 2)) := by
    have hleft : 0 ≤
        ((Real.sqrt (h ^ 2 - 1) + Real.sqrt (h ^ 2 - 1)) / (h + h)) *
          Real.sqrt ((r - 1) / (r + 1)) := by positivity
    have hright := Real.sqrt_nonneg ((h ^ 2 - 1) / (Q + h ^ 2))
    have hright_sq := Real.sq_sqrt (div_nonneg hA.le hden.le)
    nlinarith [hfactor_sq, hright_sq]
  have hmean :=
    D5.S3.Geometry.Hyperideal.FourCycleAnisotropicMeanResponse.paired_angle_half_sum
      r h h s hr hh hh hs haxis htrans htrans
  have hbeta_response : beta = middleAngle h Q theta := by
    change (beta + beta) / 2 =
      Real.arctan
        ((((Real.sqrt (h ^ 2 - 1) + Real.sqrt (h ^ 2 - 1)) / (h + h)) *
          Real.sqrt ((r - 1) / (r + 1))) * Real.cot (theta / 2)) at hmean
    rw [hfactor] at hmean
    change beta = Real.arctan
      (Real.sqrt ((h ^ 2 - 1) / (Q + h ^ 2)) * Real.cot (theta / 2))
    linarith only [hmean]
  have hwindow := middle_angle_window hh hQh htheta_pos htheta_lt_pi htan hQcot
  have hclip (q : Fin 6) : extendedAngle (six r h s) q =
      Real.arccos (rawCos (six r h s) q) := by
    dsimp only [extendedAngle]
    rw [min_eq_left (hg q).2.le, max_eq_right (hg q).1.le]
  have htheta_actual : extendedAngle (six r h s) 0 = theta := by
    change extendedAngle (six r h s) 0 = Real.arccos (rawCos (six r h s) 0)
    exact hclip 0
  refine ⟨htheta_actual, hshort, hQcot, ?_⟩
  intro q hq0 hq3
  have hraw : rawCos (six r h s) q = cosine h h r h h s := by
    fin_cases q <;> first | contradiction | rfl
  have hactual : extendedAngle (six r h s) q = beta := by
    exact (hclip q).trans (congrArg Real.arccos hraw)
  rw [hactual, hbeta_response]
  exact ⟨rfl, hwindow⟩

/-- Low means an actual face contains a value below the common middle value. -/
def lowFlag {T : Type*} (p : RawFacePairing T)
    (x : p.GlobalEdge → ℝ) (h : ℝ) (d : Flag T) : Prop :=
  ∃ m : Fin 3, x (p.edgeLabel d.1 (faceEdge d.2.1 m)) < h

/-- The same original quotient class is retained, including repeated labels. -/
def lowFiber {T : Type*} (p : RawFacePairing T)
    (x : p.GlobalEdge → ℝ) (h : ℝ) (e : p.GlobalEdge) :=
  {d : Flag T // lowFlag p x h d ∧ p.edgeLabel d.1 (faceEdge d.2.1 d.2.2) = e}

/-- The original low-slot subtype is finite before any theorem statement uses its card. -/
noncomputable instance lowFiberFintype {T : Type*} [Fintype T]
    (p : RawFacePairing T) (x : p.GlobalEdge → ℝ) (h : ℝ) (e : p.GlobalEdge) :
    Fintype (lowFiber p x h e) := by
  classical
  unfold lowFiber
  infer_instance

/-- This uses the original private crossing, not an independently supplied partner. -/
theorem actual_low_flag_count_even {T : Type*} [Fintype T]
    (p : RawFacePairing T) (x : p.GlobalEdge → ℝ) (h : ℝ) (e : p.GlobalEdge) :
    Even (Fintype.card (lowFiber p x h e)) := by
  classical
  let q : Pairing T := Pairing.mk
    p.facePair p.faceMap p.pairInvolutive p.pairFixedFree p.mapInverse
  let C : Equiv.Perm (Flag T) := cross q
  have hC (d : Flag T) : C d =
      ((p.facePair (d.1,d.2.1)).1,
        ((p.facePair (d.1,d.2.1)).2, p.faceMap (d.1,d.2.1) d.2.2)) := by
    dsimp only [C, cross, q]
    rfl
  have hlabels (f : T × Fin 4) (m : Fin 3) :
      p.edgeLabel f.1 (faceEdge f.2 m) =
        p.edgeLabel (p.facePair f).1
          (faceEdge (p.facePair f).2 (p.faceMap f m)) := by
    apply Quotient.sound
    exact Relation.EqvGen.rel _ _ ⟨f,m,rfl,rfl⟩
  have hpres (d : lowFiber p x h e) :
      lowFlag p x h (C d.val) ∧
        p.edgeLabel (C d.val).1 (faceEdge (C d.val).2.1 (C d.val).2.2) = e := by
    constructor
    · obtain ⟨m,hm⟩ := d.property.1
      refine ⟨p.faceMap (d.val.1,d.val.2.1) m, ?_⟩
      rw [hC]
      change x (p.edgeLabel (p.facePair (d.val.1,d.val.2.1)).1
        (faceEdge (p.facePair (d.val.1,d.val.2.1)).2
          (p.faceMap (d.val.1,d.val.2.1) m))) < h
      rw [← hlabels (d.val.1,d.val.2.1) m]
      exact hm
    · rw [hC]
      change p.edgeLabel (p.facePair (d.val.1,d.val.2.1)).1
        (faceEdge (p.facePair (d.val.1,d.val.2.1)).2
          (p.faceMap (d.val.1,d.val.2.1) d.val.2.2)) = e
      exact (hlabels (d.val.1,d.val.2.1) d.val.2.2).symm.trans d.property.2
  let partner : lowFiber p x h e → lowFiber p x h e :=
    fun d => ⟨C d.val,hpres d⟩
  have hinvolutive : Function.Involutive partner := by
    intro d
    apply Subtype.ext
    change C (C d.val) = d.val
    exact C.left_inv d.val
  have hfixed : ∀ d, partner d ≠ d := by
    intro d hd
    have hval : C d.val = d.val := by
      simpa only [partner] using congrArg Subtype.val hd
    have hf := congrArg (fun z : Flag T => (z.1,z.2.1)) hval
    rw [hC] at hf
    exact p.pairFixedFree (d.val.1,d.val.2.1) hf
  exact D5.S3.PrimeForms.Crossing.GlideCrossingParity.glide_crossing_count_even
    partner hinvolutive hfixed

end Section71ExactCheck620

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``Section71ExactCheck620.literal_local_bridge,
      ``Section71ExactCheck620.actual_low_flag_count_even] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"Section71-620 declaration absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"Section71-620 disallowed axiom {ax} for {name}"
    Lean.logInfo m!"Section71-620 CHECKED {name} axioms={axioms}"
