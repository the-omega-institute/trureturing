/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectanglePosteriors
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectanglePosteriors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original finite posterior ratios and aligned counts give same-law half-line defects. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Rectangles.OriginalRectangleHalfLines
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Rectangles.OriginalRectangleMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory ProbabilityTheory Function Filter
open scoped BigOperators ENNReal Classical
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureCylinders
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalErasureComparison
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleSmoothing
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleOccurrence
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleMoments
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleHalfLines
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleMessages
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleLaw

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectanglePosteriors
universe u
variable {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
private abbrev Visible := ℤ → Bool

private def observation (k n : ℕ) (z : Visible) := (leftWord k z,rightWord n z)
private def leftList (k : ℕ) (z : Visible) := List.ofFn (leftWord k z)
private def rightList (n : ℕ) (z : Visible) := List.ofFn (rightWord n z)
private def wordAt (d : ℤ) (n : ℕ) (z : Visible) : List Bool :=
  List.ofFn (fun i : Fin n => z (d+i.val))

private theorem record_fiber (k n : ℕ) (a : Fin k → Bool) (c : Fin n → Bool) :
    record (List.ofFn a) (List.ofFn c) = observation k n ⁻¹' {(a,c)} := by
  ext z
  simp only [record,block,Set.mem_inter_iff,Set.mem_setOf_eq,Set.mem_preimage,
    Set.mem_singleton_iff,observation,Prod.mk.injEq,List.length_ofFn]
  constructor
  · rintro ⟨ha,hc⟩
    constructor
    · funext i
      simpa [leftWord,List.get_ofFn] using ha i
    · funext i
      simpa [rightWord,List.get_ofFn,add_comm] using hc i
  · rintro ⟨ha,hc⟩
    constructor
    · intro i
      simpa [leftWord,List.get_ofFn] using congrFun ha i
    · intro i
      simpa [rightWord,List.get_ofFn,add_comm] using congrFun hc i

/-- The union of all zero observation fibers is null, including empty words. -/
private theorem positive_observed_record (P : Measure Visible) [IsProbabilityMeasure P]
    (k n : ℕ) : ∀ᵐ z ∂P, 0 < P.real (record (leftList k z) (rightList n z)) := by
  let o := observation k n
  have he (e : (Fin k → Bool) × (Fin n → Bool)) :
      ∀ᵐ z ∂P, o z = e → 0 < P.real (o ⁻¹' {e}) := by
    by_cases hh : P (o ⁻¹' {e}) = 0
    · have hn : ∀ᵐ z ∂P, o z ≠ e := by
        apply ae_iff.mpr
        simpa only [Set.preimage,Set.mem_singleton_iff,not_not] using hh
      exact hn.mono fun z hz hze => (hz hze).elim
    · exact Filter.Eventually.of_forall fun _ _ =>
        ENNReal.toReal_pos hh (measure_ne_top P _)
  filter_upwards [ae_all_iff.mpr he] with z hz
  simpa only [leftList,rightList,record_fiber,o] using hz (o z) rfl

/-- On each positive observation fiber, disintegration is the original record ratio.
The observation alphabet is finite; its zero fibers were removed above, not normalized. -/
private theorem record_condExp (P : Measure Visible) [IsProbabilityMeasure P]
    (k n : ℕ) : ∀ᵐ z ∂P,
      recordPosterior P (leftList k z) (rightList n z) = (P[erasedBit | recordField k n]) z := by
  let o := observation k n
  have ho : Measurable o := by dsimp [o,observation,leftWord,rightWord]; fun_prop
  have hx : Measurable (fun z : Visible => z 0) := measurable_pi_apply 0
  have hc := bitPredictor_condExp P (fun z : Visible => z 0) o hx ho
  filter_upwards [positive_observed_record P k n,hc] with z hz hce
  have hf : record (leftList k z) (rightList n z) = o ⁻¹' {o z} :=
    record_fiber k n (leftWord k z) (rightWord n z)
  have hp : P (o ⁻¹' {o z}) ≠ 0 := by
    rw [← hf]
    exact (measureReal_ne_zero_iff (measure_ne_top P _)).mp hz.ne'
  have hm : (P.map o) {o z} ≠ 0 := by
    rwa [Measure.map_apply ho (measurableSet_singleton _)]
  have hd := condDistrib_apply_of_ne_zero ho hx (o z) hm {true}
  have he : (fun z : Visible => (o z,z 0)) ⁻¹' ({o z} ×ˢ {true}) =
      record (leftList k z) (rightList n z) ∩ {z | z 0 = true} := by
    rw [hf]
    rfl
  have hr : bitPredictor P (fun z : Visible => z 0) o (o z) =
      recordPosterior P (leftList k z) (rightList n z) := by
    unfold bitPredictor Measure.real
    rw [hd,Measure.map_apply (ho.prodMk hx)
      ((measurableSet_singleton _).prod (measurableSet_singleton true)),
      Measure.map_apply ho (measurableSet_singleton _),he,ENNReal.toReal_mul,
      ENNReal.toReal_inv]
    simp only [recordPosterior,measureReal_def,hf,div_eq_mul_inv,mul_comm]
  exact hr.symm.trans hce

private theorem wordAt_take (d : ℤ) (n s : ℕ) (hs : s ≤ n) (z : Visible) :
    (wordAt d n z).take s = wordAt d s z := by
  apply List.ext_getElem
  · simp [wordAt,Nat.min_eq_left hs]
  · intro i hi hi'
    simp only [wordAt,List.getElem_take,List.getElem_ofFn]

private theorem wordAt_drop (d : ℤ) (n s : ℕ) (hs : s ≤ n) (z : Visible) :
    (wordAt d n z).drop s = wordAt (d+s) (n-s) z := by
  apply List.ext_getElem
  · simp [wordAt]
  · intro i hi hi'
    simp only [wordAt,List.getElem_drop,List.getElem_ofFn]
    congr 1
    push_cast
    ring

private theorem leftList_wordAt (k : ℕ) (z : Visible) :
    leftList k z = wordAt (-(k : ℤ)) k z := rfl

private theorem rightList_wordAt (n : ℕ) (z : Visible) :
    rightList n z = wordAt 1 n z := by
  unfold rightList wordAt rightWord
  congr 1
  funext i
  rw [add_comm (i.val : ℤ) 1]

private theorem left_suffix (j k : ℕ) (hjk : j ≤ k) (z : Visible) :
    (leftList k z).drop (k-j) = leftList j z := by
  rw [leftList_wordAt,leftList_wordAt,wordAt_drop _ _ _ (by omega)]
  have hd : -(k : ℤ)+(k-j : ℕ) = -(j : ℤ) := by
    rw [Int.natCast_sub hjk]
    ring
  rw [hd,show k-(k-j) = j by omega]

private theorem right_prefix (j n : ℕ) (hjn : j ≤ n) (z : Visible) :
    (rightList n z).take j = rightList j z := by
  rw [rightList_wordAt,rightList_wordAt,wordAt_take _ _ _ hjn]

private theorem finite_condExp_bounds (θ : Presentation H)
    (J : Measure (PathSpace H)) [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ)
    (w : List Bool) (hw : w ≠ []) (R : Rectangle (product θ w)) (j : ℕ) :
    let P := J.map Prod.snd
    let b := w.length + Fintype.card H
    let ρ := 1-rectangleMinimum (product θ w) R / rectangleMaximum (product θ w) R
    (∀ k n, j ≤ k → ∀ᵐ z ∂P,
      |(P[erasedBit | recordField k n]) z - (P[erasedBit | recordField j n]) z| ≤
        ρ ^ originalSuccessCount w b (j/b) ((leftList j z).drop (j%b))) ∧
    (∀ k n, j ≤ n → ∀ᵐ z ∂P,
      |(P[erasedBit | recordField k n]) z - (P[erasedBit | recordField k j]) z| ≤
        ρ ^ originalSuccessCount w b (j/b) (rightList j z)) := by
  dsimp only
  let P := J.map Prod.snd
  have hs := finite_record_smoothing_by_original_success_count θ J hc w hw R
  constructor
  · intro k n hjk
    filter_upwards [positive_observed_record P k n,positive_observed_record P j n,
      record_condExp P k n,record_condExp P j n] with z hlong hshort hce hce'
    have he : (leftList k z).take (k-j) ++ leftList j z = leftList k z := by
      rw [← left_suffix j k hjk z,List.take_append_drop]
    have hh := hs.1 ((leftList k z).take (k-j)) (leftList j z) (rightList n z)
      (by rwa [he]) hshort
    rw [he,hce,hce'] at hh
    simpa only [leftList,List.length_ofFn] using hh
  · intro k n hjn
    filter_upwards [positive_observed_record P k n,positive_observed_record P k j,
      record_condExp P k n,record_condExp P k j] with z hlong hshort hce hce'
    have he : rightList j z ++ (rightList n z).drop j = rightList n z := by
      rw [← right_prefix j n hjn z,List.take_append_drop]
    have hh := hs.2 (leftList k z) (rightList j z) ((rightList n z).drop j)
      (by rwa [he]) hshort
    rw [he,hce,hce'] at hh
    simpa only [rightList,List.length_ofFn] using hh

/-- Count the recursively split finite word by the same chronological block indicators. -/
private theorem count_wordAt (w : List Bool) (b q n : ℕ) (d : ℤ)
    (hn : q*b ≤ n) (z : PathSpace H) :
    originalSuccessCount w b q (wordAt d n z.2) = chronologicalCount w b d q z := by
  induction q generalizing n d with
  | zero => simp [originalSuccessCount,chronologicalCount]
  | succ q ih =>
    have hn' : q*b+b ≤ n := by simpa only [Nat.add_mul,one_mul] using hn
    have hb : b ≤ n := by omega
    rw [originalSuccessCount,wordAt_take d n b hb,wordAt_drop d n b hb,
      ih (n-b) (d+b) (by omega)]
    have he : (w <:+: wordAt d b z.2) ↔ z ∈ blockSuccess w b d := by
      rfl
    have hsplit : chronologicalCount w b d (q+1) z =
        (if z ∈ blockSuccess w b d then 1 else 0) +
          chronologicalCount w b (d+b) q z := by
      unfold chronologicalCount
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_add,Nat.cast_one,add_mul,one_mul]
      have htime (i : ℕ) : d + ((i : ℤ)*b+b) = d+b+(i : ℤ)*b := by ring
      simp only [htime,zero_mul,add_zero]
      omega
    rw [hsplit]
    simp only [he]

private theorem left_count (w : List Bool) (b j : ℕ) (hb : 0 < b) (z : PathSpace H) :
    originalSuccessCount w b (j/b) ((leftList j z.2).drop (j%b)) =
      chronologicalCount w b (-((j/b : ℕ) : ℤ)*b) (j/b) z := by
  rw [leftList_wordAt,wordAt_drop _ _ _ (Nat.le_of_lt (Nat.mod_lt j hb))]
  have hdiv : j%b+(j/b)*b = j := by
    simpa only [Nat.mul_comm b] using Nat.mod_add_div j b
  have hn : j-j%b = (j/b)*b := by omega
  have hd : -(j : ℤ)+(j%b : ℕ) = -((j/b : ℕ) : ℤ)*b := by
    have hdiv := Nat.mod_add_div j b
    have hh := congrArg (fun a : ℕ => (a : ℤ)) hdiv
    push_cast at hh
    nlinarith
  rw [hn,hd]
  exact count_wordAt w b (j/b) _ _ le_rfl z

private theorem right_count (w : List Bool) (b j : ℕ) (z : PathSpace H) :
    originalSuccessCount w b (j/b) (rightList j z.2) =
      chronologicalCount w b 1 (j/b) z := by
  rw [rightList_wordAt]
  exact count_wordAt w b (j/b) j 1 (Nat.div_mul_le_self j b) z

/-- Under the one original-cylinder law, complete both exterior limits and keep
exactly the chronological original-block count on each side. -/
private theorem half_line_count_bounds (θ : Presentation H)
    (J : Measure (PathSpace H)) [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ)
    (w : List Bool) (hw : w ≠ []) (R : Rectangle (product θ w)) (j : ℕ) :
    let P := J.map Prod.snd
    let b := w.length + Fintype.card H
    let ρ := 1-rectangleMinimum (product θ w) R / rectangleMaximum (product θ w) R
    ∀ᵐ z ∂J,
      |(P[erasedBit | MeasurableSpace.comap exterior inferInstance]) z.2 -
        (P[erasedBit | MeasurableSpace.comap (leftObservation j) inferInstance]) z.2| ≤
        ρ ^ chronologicalCount w b (-((j/b : ℕ) : ℤ)*b) (j/b) z ∧
      |(P[erasedBit | MeasurableSpace.comap exterior inferInstance]) z.2 -
        (P[erasedBit | MeasurableSpace.comap (rightObservation j) inferInstance]) z.2| ≤
        ρ ^ chronologicalCount w b 1 (j/b) z := by
  dsimp only
  let P := J.map Prod.snd
  let b := w.length + Fintype.card H
  let ρ := 1-rectangleMinimum (product θ w) R / rectangleMaximum (product θ w) R
  have hb : 0 < b := by
    have hw' : 0 < w.length := List.length_pos_iff.mpr hw
    dsimp [b]
    omega
  have hf := finite_condExp_bounds θ J hc w hw R j
  have hh := finite_record_bounds_to_half_lines P erasedBit j
    (fun z => ρ ^ originalSuccessCount w b (j/b) ((leftList j z).drop (j%b)))
    (fun z => ρ ^ originalSuccessCount w b (j/b) (rightList j z)) hf.1 hf.2
  have hl := ae_of_ae_map measurable_snd.aemeasurable hh.1
  have hr := ae_of_ae_map measurable_snd.aemeasurable hh.2
  filter_upwards [hl,hr] with z hzl hzr
  exact ⟨by simpa only [left_count w b j hb z] using hzl,
    by simpa only [right_count w b j z] using hzr⟩

private theorem rectangle_rho_range (B : Matrix H H ℝ) (R : Rectangle B) :
    0 ≤ 1-rectangleMinimum B R / rectangleMaximum B R ∧
      1-rectangleMinimum B R / rectangleMaximum B R < 1 := by
  let S := (R.rows ×ˢ R.cols).image fun ij => B ij.1 ij.2
  have hS : S.Nonempty := (R.rows_nonempty.product R.cols_nonempty).image _
  have hu : 0 < rectangleMinimum B R := by
    obtain ⟨ij,hij,he⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
    change 0 < S.min' hS
    rw [← he]
    exact R.positive ij.1 (Finset.mem_product.mp hij).1 ij.2 (Finset.mem_product.mp hij).2
  have huv : rectangleMinimum B R ≤ rectangleMaximum B R := Finset.min'_le_max' hS
  have hv : 0 < rectangleMaximum B R := hu.trans_le huv
  exact ⟨sub_nonneg.mpr ((div_le_one hv).mpr huv),
    sub_lt_self _ (div_pos hu hv)⟩

/-- The finite-word representation also makes the chronological count measurable;
no completion or future-conditioned occurrence premise is introduced. -/
private theorem count_payment_integrable (J : Measure (PathSpace H)) [IsProbabilityMeasure J]
    (w : List Bool) (b : ℕ) (d : ℤ) (q : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    Integrable (fun z => ρ^(2 * chronologicalCount w b d q z)) J := by
  let read : PathSpace H → (Fin (q*b) → Bool) := fun z i => z.2 (d+i.val)
  let value : (Fin (q*b) → Bool) → ℝ :=
    fun v => ρ^(2 * originalSuccessCount w b q (List.ofFn v))
  have hm : Measurable (fun z : PathSpace H => ρ^(2 * chronologicalCount w b d q z)) := by
    have hh : Measurable (value ∘ read) :=
      (measurable_of_finite value).comp (by dsimp [read]; fun_prop)
    convert hh using 1
    funext z
    dsimp [value,read,Function.comp_def]
    rw [show (List.ofFn fun i : Fin (q*b) => z.2 (d+i.val)) = wordAt d (q*b) z.2 from rfl,
      count_wordAt w b q (q*b) d le_rfl z]
  apply (integrable_const (μ := J) (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hρ _)]
    exact pow_le_one₀ hρ hρ1

private theorem erasedBit_memLp (P : Measure Visible) [IsProbabilityMeasure P] :
    MemLp erasedBit 2 P := by
  have hm : Measurable erasedBit := by unfold erasedBit; fun_prop
  apply memLp_of_bounded (a := 0) (b := 1) _ hm.aestronglyMeasurable 2
  exact Filter.Eventually.of_forall fun z => by
    cases hz : z 0 <;> simp [erasedBit,hz]

private theorem square_integrable (P : Measure Visible) [IsProbabilityMeasure P]
    (m n : MeasurableSpace Visible) :
    Integrable (fun z => ((P[erasedBit | m]) z - (P[erasedBit | n]) z)^2) P := by
  have hm : MemLp (P[erasedBit | m]) 2 P := (erasedBit_memLp P).condExp (by norm_num)
  have hn : MemLp (P[erasedBit | n]) 2 P := (erasedBit_memLp P).condExp (by norm_num)
  exact (memLp_two_iff_integrable_sq (hm.sub hn).aestronglyMeasurable).mp (hm.sub hn)

/-- The genuine erasure defects under one original-cylinder law. Finite record
ratios are identified with conditional expectations outside the union of null
observation fibers. Both list counts are matched to chronological original blocks
before the existing ordered limits and occurrence moments are consumed.

The opposite infinite half-line is retained in each conditional expectation.
The two squared integrals are under the same visible pushforward P of J. -/
theorem original_rectangle_erasure_bounds (θ : Presentation H)
    (J : Measure (PathSpace H)) [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ)
    (w : List Bool) (hw : w ≠ []) (R : Rectangle (product θ w))
    (r : H) (hr : r ∈ R.rows) (a : ∀ h, LabelledRoute θ h r)
    (ha : ∀ h, (a h).length ≤ Fintype.card H) (j : ℕ) :
    let P := J.map Prod.snd
    let b := w.length + Fintype.card H
    let ρ := 1-rectangleMinimum (product θ w) R / rectangleMaximum (product θ w) R
    let η := 1-selectedEpsilon θ w r a*(1-ρ^2)
    let q := j/b
    let q0 := P[erasedBit | MeasurableSpace.comap exterior inferInstance]
    let pL := P[erasedBit | MeasurableSpace.comap (leftObservation j) inferInstance]
    let pR := P[erasedBit | MeasurableSpace.comap (rightObservation j) inferInstance]
    (∀ᵐ z ∂J,
      |q0 z.2-pL z.2| ≤ ρ ^ chronologicalCount w b (-(q : ℤ)*b) q z ∧
      |q0 z.2-pR z.2| ≤ ρ ^ chronologicalCount w b 1 q z) ∧
    (∫ z, (q0 z-pL z)^2 ∂P) ≤ η^q ∧
    (∫ z, (q0 z-pR z)^2 ∂P) ≤ η^q := by
  dsimp only
  let P := J.map Prod.snd
  let b := w.length + Fintype.card H
  let ρ := 1-rectangleMinimum (product θ w) R / rectangleMaximum (product θ w) R
  let η := 1-selectedEpsilon θ w r a*(1-ρ^2)
  let q := j/b
  let q0 := P[erasedBit | MeasurableSpace.comap exterior inferInstance]
  let pL := P[erasedBit | MeasurableSpace.comap (leftObservation j) inferInstance]
  let pR := P[erasedBit | MeasurableSpace.comap (rightObservation j) inferInstance]
  have hρ := rectangle_rho_range (product θ w) R
  have hbnd := half_line_count_bounds θ J hc w hw R j
  have hL : Integrable (fun z => (q0 z-pL z)^2) P := square_integrable P _ _
  have hR : Integrable (fun z => (q0 z-pR z)^2) P := square_integrable P _ _
  have hsquare (x : ℝ) (K : ℕ) (hx : |x| ≤ ρ^K) : x^2 ≤ ρ^(2*K) := by
    have hh := mul_self_le_mul_self (abs_nonneg x) hx
    simpa only [← pow_two,sq_abs,← pow_mul,Nat.mul_comm K 2] using hh
  refine ⟨hbnd,?_,?_⟩
  · calc
      (∫ z, (q0 z-pL z)^2 ∂P) = ∫ z, (q0 z.2-pL z.2)^2 ∂J :=
        integral_map measurable_snd.aemeasurable hL.aestronglyMeasurable
      _ ≤ ∫ z, ρ^(2 * chronologicalCount w b (-(q : ℤ)*b) q z) ∂J := by
        apply integral_mono_ae
          ((integrable_map_measure hL.aestronglyMeasurable measurable_snd.aemeasurable).mp hL)
          (count_payment_integrable J w b _ q ρ hρ.1 hρ.2.le)
        exact hbnd.mono fun z hz => hsquare _ _ hz.1
      _ ≤ η^q := chronological_success_moment θ J hc w R r hr a ha ρ hρ.1 hρ.2.le _ q
  · calc
      (∫ z, (q0 z-pR z)^2 ∂P) = ∫ z, (q0 z.2-pR z.2)^2 ∂J :=
        integral_map measurable_snd.aemeasurable hR.aestronglyMeasurable
      _ ≤ ∫ z, ρ^(2 * chronologicalCount w b 1 q z) ∂J := by
        apply integral_mono_ae
          ((integrable_map_measure hR.aestronglyMeasurable measurable_snd.aemeasurable).mp hR)
          (count_payment_integrable J w b 1 q ρ hρ.1 hρ.2.le)
        exact hbnd.mono fun z hz => hsquare _ _ hz.2
      _ ≤ η^q := chronological_success_moment θ J hc w R r hr a ha ρ hρ.1 hρ.2.le 1 q

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectanglePosteriors
