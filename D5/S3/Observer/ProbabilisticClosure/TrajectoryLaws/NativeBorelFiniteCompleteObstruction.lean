/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The genuine continuous common-flow tail cannot be realized by any finite COMPLETE observer. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteProducts
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFiniteWordCoordinates
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw

/- This instance layer retains the native descriptor and paid-history dependency family.
   The I classification does not enlarge its original endpoint boxes or mathematical quantifiers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteCompleteObstruction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open NativeBorelCommonFlow NativeBorelTVTopology NativeBorelEndpointIdentification
open NativeConditionalControl.Tail NativeFullResidual FourthSegmentStoppedLaw


def curveLaw (s : ActivePhase) (t : CurveParameter) : ProbabilityMeasure (ValidTail s) :=
  let T := curveParameters t
  let z := NativePeriodicWordLaw.atLabel s 2
  ⟨(NativePeriodicWordLaw.wordLaw T s z).comap Subtype.val, ⟨by
    rw [(inclusion_embedding s).comap_apply, Set.image_univ]
    rw [NativePeriodicWordLaw.wordLaw, Measure.map_apply
      (measurable_stopped_read_word s) (Set.to_countable _).measurableSet]
    have he : stoppedReadWord s ⁻¹' Set.range (Subtype.val : ValidTail s → RawTail) =
        Set.univ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨⟨stoppedReadWord s ω, stopped_legal s ω⟩,rfl⟩
    rw [he, measure_univ]⟩⟩

private theorem curve_point (s : ActivePhase) (t : CurveParameter) (a : ValidTail s) :
    (curveLaw s t : Measure _) {a} =
      NativePeriodicWordLaw.wordLaw (curveParameters t) s
        (NativePeriodicWordLaw.atLabel s 2) {a.val} := by
  change (NativePeriodicWordLaw.wordLaw _ _ _).comap
    (Subtype.val : ValidTail s → RawTail) {a} = _
  rw [(inclusion_embedding s).comap_apply, Set.image_singleton]

private theorem curve_atoms (t : CurveParameter) :
    (∀ n b, (curveLaw .p t : Measure _).real {pAtom n b} =
      (if b = 0 then curveU t else curveG t) * (t : ℝ)^n) ∧
    (curveLaw .beta t : Measure _).real {betaStop} = 1 - curveV t ∧
    (∀ n b, (curveLaw .beta t : Measure _).real {betaAtom n b} =
      curveV t * ((if b = 0 then curveU t else curveG t) * (t : ℝ)^n)) ∧
    (∀ s, (curveLaw s t : Measure _) {infinity s} = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n b
    rw [Measure.real, curve_point]
    have h := (NativePeriodicWordLaw.native_word_identification (curveParameters t) .p
      (NativePeriodicWordLaw.atLabel .p 2) rfl).1 n b
    rw [NativePeriodicWordLaw.source_coord_eq] at h
    simpa only [Measure.real, pAtom, NativePeriodicWordLaw.typeWord,
      NativePeriodicWordLaw.nativeCoord, NativePeriodicWordLaw.atLabel, curve_coord] using h
  · rw [Measure.real, curve_point]
    exact (NativePeriodicWordLaw.native_word_identification (curveParameters t) .beta
      (NativePeriodicWordLaw.atLabel .beta 2) rfl).2 rfl
  · intro n b
    rw [Measure.real, curve_point]
    have h := (NativePeriodicWordLaw.native_word_identification (curveParameters t) .beta
      (NativePeriodicWordLaw.atLabel .beta 2) rfl).1 n b
    simp only [NativePeriodicWordLaw.source_coord_eq, NativePeriodicWordLaw.nativeCoord,
      NativePeriodicWordLaw.atLabel] at h
    rw [curve_coord] at h
    simpa only [Measure.real, betaAtom, NativePeriodicWordLaw.typeWord,
      NativePeriodicWordLaw.nativeCoord, NativePeriodicWordLaw.atLabel, curveParameters,
      curve_coord] using h
  · intro s
    rw [curve_point]
    exact (NativePeriodicWordLaw.native_noncompletion (curveParameters t) s
      (NativePeriodicWordLaw.atLabel s 2) rfl).2

private theorem curve_measurable (s : ActivePhase) : Measurable (curveLaw s) := by
  have he : curveLaw s = (coordinateEquiv s).symm ∘
      (fun t => (coordinateEquiv s) (curveLaw s t)) := by
    funext t
    simp
  rw [he]
  apply (coordinateEquiv s).symm.measurable.comp
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  rintro ⟨a,ha⟩
  have hmU : Measurable (fun t : CurveParameter => curveU t) := by
    unfold curveU curveG curveQ; fun_prop
  have hmG : Measurable (fun t : CurveParameter => curveG t) := by
    unfold curveG curveQ; fun_prop
  have hmV : Measurable (fun t : CurveParameter => curveV t) := by
    unfold curveV curveG curveQ; fun_prop
  cases a with
  | none =>
    change Measurable (fun t => (curveLaw s t : Measure _) {infinity s})
    have hz (t : CurveParameter) := (curve_atoms t).2.2.2 s
    simp_rw [hz]
    exact measurable_const
  | some w =>
    obtain ⟨b,hb⟩ := ha
    cases s with
    | p =>
      obtain ⟨n,rfl⟩ := hb
      have he (t : CurveParameter) : (curveLaw .p t : Measure _) {pAtom n b} =
          ENNReal.ofReal ((if b = 0 then curveU t else curveG t) * (t : ℝ)^n) := by
        rw [← (curve_atoms t).1 n b, Measure.real,
          ENNReal.ofReal_toReal (measure_ne_top _ _)]
      change Measurable (fun t => (curveLaw .p t : Measure _) {pAtom n b})
      simp_rw [he]
      by_cases h : b = 0 <;> simp only [h, ↓reduceIte] <;> fun_prop
    | beta =>
      rcases hb with ⟨rfl,rfl⟩ | ⟨n,rfl⟩
      · have he (t : CurveParameter) : (curveLaw .beta t : Measure _) {betaStop} =
            ENNReal.ofReal (1 - curveV t) := by
          rw [← (curve_atoms t).2.1, Measure.real,
            ENNReal.ofReal_toReal (measure_ne_top _ _)]
        change Measurable (fun t => (curveLaw .beta t : Measure _) {betaStop})
        simp_rw [he]; fun_prop
      · have he (t : CurveParameter) : (curveLaw .beta t : Measure _) {betaAtom n b} =
            ENNReal.ofReal (curveV t * ((if b = 0 then curveU t else curveG t) * (t : ℝ)^n)) := by
          rw [← (curve_atoms t).2.2.1 n b, Measure.real,
            ENNReal.ofReal_toReal (measure_ne_top _ _)]
        change Measurable (fun t => (curveLaw .beta t : Measure _) {betaAtom n b})
        simp_rw [he]
        by_cases h : b = 0 <;> simp only [h, ↓reduceIte] <;> fun_prop


private theorem curve_eatoms (t : CurveParameter) :
    (∀ n b, (curveLaw .p t : Measure _) {pAtom n b} =
      ENNReal.ofReal (if b = 0 then curveU t else curveG t) * ENNReal.ofReal (t : ℝ)^n) ∧
    (curveLaw .beta t : Measure _) {betaStop} = ENNReal.ofReal (1 - curveV t) ∧
    (∀ n b, (curveLaw .beta t : Measure _) {betaAtom n b} =
      ENNReal.ofReal (curveV t) *
        (ENNReal.ofReal (if b = 0 then curveU t else curveG t) * ENNReal.ofReal (t : ℝ)^n)) := by
  have hx : 0 ≤ (t : ℝ) := le_trans (by norm_num) t.property.1
  have hc (b : Letter) : 0 ≤ (if b = 0 then curveU t else curveG t) := by
    split_ifs <;> linarith [(scalar_boxes t).1,(scalar_boxes t).2.2.2.2.1]
  refine ⟨?_, ?_, ?_⟩
  · intro n b
    rw [← ENNReal.ofReal_pow hx, ← ENNReal.ofReal_mul (hc b),
      ← (curve_atoms t).1 n b, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · rw [← (curve_atoms t).2.1, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · intro n b
    rw [← ENNReal.ofReal_pow hx, ← ENNReal.ofReal_mul (hc b),
      ← ENNReal.ofReal_mul (by linarith [(scalar_boxes t).2.2.1]),
      ← (curve_atoms t).2.2.1 n b, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]

private theorem curve_p_expansion (t : CurveParameter) :
    (curveLaw .p t : Measure _) = Measure.sum (fun n : ℕ =>
      (ENNReal.ofReal (curveU t) * ENNReal.ofReal (t : ℝ)^n) • Measure.dirac (pAtom n 0) +
      (ENNReal.ofReal (curveG t) * ENNReal.ofReal (t : ℝ)^n) • Measure.dirac (pAtom n 1)) := by
  apply Measure.ext_of_singleton
  rintro ⟨a,ha⟩
  cases a with
  | none =>
    simpa [infinity, Measure.sum_apply, pAtom, Pi.single_apply, Subtype.ext_iff] using (curve_atoms t).2.2.2 .p
  | some w =>
    obtain ⟨b,n,rfl⟩ := ha
    have h := (curve_eatoms t).1 n b
    fin_cases b <;>
      simpa [pAtom, Measure.sum_apply, Pi.single_apply, Subtype.ext_iff, p_word_injective] using h

private theorem curve_b_expansion (t : CurveParameter) :
    (curveLaw .beta t : Measure _) = ENNReal.ofReal (1 - curveV t) • Measure.dirac betaStop +
      Measure.sum (fun n : ℕ =>
        (ENNReal.ofReal (curveV t) * ENNReal.ofReal (curveU t) * ENNReal.ofReal (t : ℝ)^n) •
          Measure.dirac (betaAtom n 0) +
        (ENNReal.ofReal (curveV t) * ENNReal.ofReal (curveG t) * ENNReal.ofReal (t : ℝ)^n) •
          Measure.dirac (betaAtom n 1)) := by
  apply Measure.ext_of_singleton
  rintro ⟨a,ha⟩
  cases a with
  | none =>
    simpa [infinity, Measure.sum_apply, betaAtom, betaStop, Pi.single_apply, Subtype.ext_iff] using (curve_atoms t).2.2.2 .beta
  | some w =>
    obtain ⟨b,hb⟩ := ha
    rcases hb with ⟨rfl,rfl⟩ | ⟨n,rfl⟩
    · simpa [betaStop, betaAtom, Measure.sum_apply, Pi.single_apply, Subtype.ext_iff] using (curve_eatoms t).2.1
    · have h := (curve_eatoms t).2.2 n b
      fin_cases b <;>
        simpa [betaStop, betaAtom, Measure.sum_apply, Pi.single_apply,
          Subtype.ext_iff, p_word_injective, mul_assoc] using h

private theorem curve_tails (t : CurveParameter) (j : ℕ) :
    (curveLaw .p t : Measure _) (tailSet .p j) = ENNReal.ofReal (t : ℝ)^j ∧
    (curveLaw .beta t : Measure _) (tailSet .beta j) =
      ENNReal.ofReal (curveV t) * ENNReal.ofReal (t : ℝ)^j := by
  classical
  let z := ENNReal.ofReal (t : ℝ)
  let d := ENNReal.ofReal (curveU t) + ENNReal.ofReal (curveG t)
  have hp (j : ℕ) : (curveLaw .p t : Measure _) (tailSet .p j) =
      ∑' n : ℕ, if j ≤ n then d * z^n else 0 := by
    rw [curve_p_expansion, Measure.sum_apply _ (Set.to_countable _).measurableSet]
    apply tsum_congr
    intro n
    simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
      smul_eq_mul, Set.indicator_apply, Pi.one_apply, p_atom_tail]
    split_ifs <;> simp [d,z,add_mul]
  have hp0 : ∑' n : ℕ, d * z^n = 1 := by
    have h0 : tailSet .p 0 = Set.univ := by
      ext a
      rcases a with ⟨a,ha⟩
      cases a with
      | none => simp [tailSet,infinity]
      | some w =>
        obtain ⟨b,n,rfl⟩ := ha
        change pAtom n b ∈ tailSet .p 0 ↔ True
        simp [p_atom_tail]
    simpa [h0] using (hp 0).symm
  refine ⟨?_, ?_⟩
  · rw [hp, geometric_tail, hp0, mul_one]
  · rw [curve_b_expansion, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply, Set.indicator_of_notMem (beta_stop_not_tail j),
      smul_zero, zero_add, Measure.sum_apply _ (Set.to_countable _).measurableSet]
    calc
      _ = ENNReal.ofReal (curveV t) * (∑' n : ℕ, if j ≤ n then d*z^n else 0) := by
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro n
        simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
          smul_eq_mul, Set.indicator_apply, Pi.one_apply, beta_atom_tail]
        split_ifs <;> simp [d,z,mul_add,add_mul,mul_assoc]
      _ = _ := by rw [geometric_tail,hp0,mul_one]

private theorem curve_emission (s : ActivePhase) (t : CurveParameter) :
    emission s (curveLaw s t) = ENNReal.ofReal (if s = .p then curveU t else curveV t) := by
  cases s with
  | p => simpa [emission] using (curve_eatoms t).1 0 0
  | beta =>
    change 1 - (curveLaw .beta t : Measure _) {betaStop} = ENNReal.ofReal (curveV t)
    rw [(curve_eatoms t).2.1]
    have hv := (scalar_boxes t).2.2
    have he : ENNReal.ofReal (1 - curveV t) + ENNReal.ofReal (curveV t) = 1 := by
      rw [← ENNReal.ofReal_add (by linarith [hv.2.1]) (by linarith [hv.1])]
      simp
    exact ENNReal.sub_eq_of_eq_add (by finiteness) (by simpa only [add_comm] using he.symm)

private theorem curve_regular (s : ActivePhase) (t : CurveParameter) : Regular s (curveLaw s t) := by
  have hx : 0 ≤ (t : ℝ) := le_trans (by norm_num) t.property.1
  have hz : ENNReal.ofReal (t : ℝ) ≤ tailRate := by
    rw [show tailRate = ENNReal.ofReal (4/15 : ℝ) by norm_num [tailRate, ENNReal.ofReal_div_of_pos]]
    exact ENNReal.ofReal_le_ofReal (by linarith [t.property.2])
  have hu := scalar_boxes t
  cases s with
  | p =>
    rw [Regular,curve_emission]
    simp only [reduceCtorEq, if_true, if_false]
    refine ⟨?_,?_,fun j => ?_⟩
    · rw [show lower = ENNReal.ofReal (1/3 : ℝ) by norm_num [lower, ENNReal.ofReal_div_of_pos]]
      exact ENNReal.ofReal_le_ofReal hu.1
    · rw [show upper = ENNReal.ofReal (2/5 : ℝ) by norm_num [upper, ENNReal.ofReal_div_of_pos]]
      exact ENNReal.ofReal_le_ofReal hu.2.1
    · rw [(curve_tails t j).1]
      simpa only [one_mul] using pow_le_pow_left' hz j
  | beta =>
    rw [Regular,curve_emission]
    simp only [reduceCtorEq, if_true, if_false]
    refine ⟨?_,?_,fun j => ?_⟩
    · rw [show lower = ENNReal.ofReal (1/3 : ℝ) by norm_num [lower, ENNReal.ofReal_div_of_pos]]
      exact ENNReal.ofReal_le_ofReal hu.2.2.1
    · rw [show upper = ENNReal.ofReal (2/5 : ℝ) by norm_num [upper, ENNReal.ofReal_div_of_pos]]
      exact ENNReal.ofReal_le_ofReal hu.2.2.2.1
    · rw [(curve_tails t j).2]
      apply mul_le_mul' _ (pow_le_pow_left' hz j)
      rw [show upper = ENNReal.ofReal (2/5 : ℝ) by norm_num [upper, ENNReal.ofReal_div_of_pos]]
      exact ENNReal.ofReal_le_ofReal hu.2.2.2.1

def curveDescriptor (s : ActivePhase) (t : CurveParameter) : RegularDescriptor s :=
  ⟨curveLaw s t,curve_regular s t⟩

private theorem curve_descriptor_measurable (s : ActivePhase) : Measurable (curveDescriptor s) :=
  (curve_measurable s).subtype_mk


private theorem curve_suspended_seeds (t : CurveParameter) :
    (18/125 : ℝ) ≤ curveV t * curveG t ∧
    curveV t * curveG t ≤ 73/500 ∧
    curveV t * curveG t * (t : ℝ) ≤ (18/125) * (6/25) := by
  let x : ℝ := t
  have hlo : (239/1000 : ℝ) ≤ x := t.property.1
  have hhi : x ≤ 6/25 := t.property.2
  have hx : 0 < x := by linarith
  have hg := scalar_boxes t
  have hd : 0 < curveG x + x := by linarith [hg.2.2.2.2.1]
  have hd4 : 0 < curveQ + x^4 := by unfold curveQ; positivity
  have he : curveV x * curveG x = curveQ*x/(curveQ+x^4) := by
    unfold curveV curveG
    field_simp [ne_of_gt hx, ne_of_gt hd4]
  have hp2lo : (239/1000 : ℝ)^2 ≤ x^2 := pow_le_pow_left₀ (by norm_num) hlo 2
  have hp3lo : (239/1000 : ℝ)^3 ≤ x^3 := pow_le_pow_left₀ (by norm_num) hlo 3
  have hp2hi : x^2 ≤ (6/25 : ℝ)^2 := pow_le_pow_left₀ hx.le hhi 2
  have hbr : 0 ≤ (18/125 : ℝ) *
      (x^3 + (6/25)*x^2 + (6/25)^2*x + (6/25)^3) - curveQ := by
    unfold curveQ
    norm_num at hp2lo hp3lo
    nlinarith
  have hfac := mul_nonneg (show 0 ≤ (6/25 : ℝ)-x by linarith) hbr
  have hlow : (18/125 : ℝ) ≤ curveV x * curveG x := by
    rw [he]
    apply (le_div_iff₀ hd4).mpr
    unfold curveQ at *
    nlinarith [hfac]
  have hhigh : curveV x * curveG x ≤ (73/500 : ℝ) := by
    have hp := mul_le_mul hg.2.2.2.1 hg.2.2.2.2.2
      (by linarith [hg.2.2.2.2.1]) (by norm_num : (0:ℝ) ≤ 2/5)
    norm_num at hp
    exact hp
  have hprod : 0 ≤ ((6/25 : ℝ)^2-x^2) * (curveQ - x^2*(6/25)^2) := by
    apply mul_nonneg (by linarith)
    unfold curveQ
    nlinarith [hp2hi]
  have hxhigh : curveV x * curveG x * x ≤ (18/125 : ℝ)*(6/25) := by
    rw [he, div_mul_eq_mul_div]
    apply (div_le_iff₀ hd4).mpr
    unfold curveQ at *
    nlinarith [hprod]
  exact ⟨hlow,hhigh,hxhigh⟩

private theorem curve_p_seed_lower (t : CurveParameter) (n : ℕ) (hn : n ≤ 3) :
    (9/25 : ℝ)*(6/25)^n ≤ curveG t * (t : ℝ)^n := by
  have hx : 0 < (t : ℝ) := lt_of_lt_of_le (by norm_num) t.property.1
  have hg : 0 ≤ curveG t := by linarith [(scalar_boxes t).2.2.2.2.1]
  have he : curveG t * (t : ℝ)^3 = (9/25 : ℝ)*(6/25)^3 := by
    unfold curveG curveQ
    field_simp
    norm_num
  have hn' : n + (3-n) = 3 := Nat.add_sub_of_le hn
  have hp := pow_le_pow_left₀ hx.le t.property.2 (3-n)
  apply le_of_mul_le_mul_right _ (pow_pos (by norm_num : (0:ℝ)<6/25) (3-n))
  calc
    _ = (9/25 : ℝ)*(6/25)^3 := by rw [mul_assoc, ← pow_add, hn']
    _ = (curveG t * (t : ℝ)^n) * (t : ℝ)^(3-n) := by
      rw [mul_assoc, ← pow_add, hn']; exact he.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (mul_nonneg hg (pow_nonneg hx.le n))

private theorem curve_finite_markers (t : CurveParameter) (n : ℕ) (hn4 : n ≤ 4) :
    (NativePeriodicWordLaw.InBox (curveU t * (t : ℝ)^n)
      ((1/3)*(2/9)^n) ((2/5)*(6/25)^n)) ∧
    (NativePeriodicWordLaw.InBox (curveG t * (t : ℝ)^n)
      ((4/9)*(2/9)^n) ((9/25)*(6/25)^n)) ∧
    (NativePeriodicWordLaw.InBox (curveV t * (curveU t * (t : ℝ)^n))
      ((1/9)*(2/9)^n) ((4/25)*(6/25)^n)) ∧
    (NativePeriodicWordLaw.InBox (curveV t * (curveG t * (t : ℝ)^n))
      ((4/27)*(2/9)^n) ((18/125)*(6/25)^n)) := by
  have hu := (scalar_boxes t)
  have hx : 0 ≤ (t : ℝ) := le_trans (by norm_num) t.property.1
  have hxlo : (2/9 : ℝ) ≤ (t : ℝ) := by linarith [t.property.1]
  have hxhi := t.property.2
  have hg : 0 ≤ curveG t := by linarith [hu.2.2.2.2.1]
  have hv : 0 ≤ curveV t := by linarith [hu.2.2.1]
  have hp (n : ℕ) : (2/9 : ℝ)^n ≤ (t : ℝ)^n ∧ (t : ℝ)^n ≤ (6/25 : ℝ)^n :=
    ⟨pow_le_pow_left₀ (by norm_num) hxlo n, pow_le_pow_left₀ hx hxhi n⟩
  have hprod : (1/9 : ℝ) ≤ curveV t*curveU t ∧ curveV t*curveU t ≤ 4/25 := by
    constructor
    · have hh := mul_le_mul hu.2.2.1 hu.1 (by norm_num : (0:ℝ)≤1/3)
        (by linarith [hu.2.2.1]); norm_num at hh; exact hh
    · have hh := mul_le_mul hu.2.2.2.1 hu.2.1 (by linarith [hu.1])
        (by norm_num : (0:ℝ)≤2/5); norm_num at hh; exact hh
  have hzero (n : ℕ) : (1/3 : ℝ)*(2/9)^n ≤ curveU t*(t : ℝ)^n ∧
      curveU t*(t : ℝ)^n ≤ (2/5)*(6/25)^n :=
    ⟨mul_le_mul hu.1 (hp n).1 (by positivity) (by linarith [hu.1]),
      mul_le_mul hu.2.1 (hp n).2 (pow_nonneg hx n) (by norm_num)⟩
  have hbzero (n : ℕ) : (1/9 : ℝ)*(2/9)^n ≤ curveV t*(curveU t*(t : ℝ)^n) ∧
      curveV t*(curveU t*(t : ℝ)^n) ≤ (4/25)*(6/25)^n := by
    rw [← mul_assoc]
    exact ⟨mul_le_mul hprod.1 (hp n).1 (by positivity) (by linarith [hprod.1]),
      mul_le_mul hprod.2 (hp n).2 (pow_nonneg hx n) (by norm_num)⟩
  have ht (n : ℕ) (hn : 3 ≤ n) (hn4 : n ≤ 4) : (4/9 : ℝ)*(2/9)^n ≤ curveG t*(t : ℝ)^n ∧
      curveG t*(t : ℝ)^n ≤ (9/25)*(6/25)^n := by
    have he : curveG t*(t : ℝ)^3 = (9/25 : ℝ)*(6/25)^3 := by
      unfold curveG curveQ
      field_simp
      norm_num
    have casesN : n = 3 ∨ n = 4 := by omega
    rcases casesN with rfl | rfl
    · rw [he]; constructor <;> norm_num
    · rw [show (t:ℝ)^4 = (t:ℝ)^3*(t:ℝ) by ring, ← mul_assoc,he]
      constructor
      · have hh := mul_le_mul_of_nonneg_left hxlo (by norm_num : 0 ≤ (9/25:ℝ)*(6/25)^3)
        norm_num at hh ⊢
        linarith
      · have hh := mul_le_mul_of_nonneg_left hxhi (by norm_num : 0 ≤ (9/25:ℝ)*(6/25)^3)
        norm_num at hh ⊢
        linarith
  have hbt (n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4) : (4/27 : ℝ)*(2/9)^n ≤ curveV t*(curveG t*(t : ℝ)^n) ∧
      curveV t*(curveG t*(t : ℝ)^n) ≤ (18/125)*(6/25)^n := by
    have hh := (curve_suspended_seeds t)
    constructor
    · have hl := mul_le_mul hh.1 (pow_le_pow_left₀ (by norm_num) t.property.1 n)
        (by positivity : (0:ℝ) ≤ (239/1000:ℝ)^n) (by linarith [hh.1])
      rw [mul_assoc] at hl
      interval_cases n <;> norm_num at hl ⊢ <;> linarith
    · obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
      rw [pow_succ]
      have hu := mul_le_mul hh.2.2 (pow_le_pow_left₀ hx hxhi m)
        (pow_nonneg hx m) (by positivity : (0:ℝ) ≤ (18/125:ℝ)*(6/25))
      simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm] using hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨(min_le_left _ _).trans (hzero n).1, (hzero n).2.trans (le_max_right _ _)⟩
  · by_cases hn : 3 ≤ n
    · exact ⟨(min_le_left _ _).trans (ht n hn hn4).1, (ht n hn hn4).2.trans (le_max_right _ _)⟩
    · have hn' : n ≤ 2 := by omega
      have hl := curve_p_seed_lower t n (by omega)
      have hh := mul_le_mul hu.2.2.2.2.2 (hp n).2 (pow_nonneg hx n) (by norm_num : (0:ℝ)≤73/200)
      interval_cases n <;> norm_num [NativePeriodicWordLaw.InBox] at * <;> constructor <;> nlinarith
  · exact ⟨(min_le_left _ _).trans (hbzero n).1, (hbzero n).2.trans (le_max_right _ _)⟩
  · by_cases hn : 1 ≤ n
    · exact ⟨(min_le_left _ _).trans (hbt n hn hn4).1, (hbt n hn hn4).2.trans (le_max_right _ _)⟩
    · have he : n = 0 := by omega
      subst n
      have hh := curve_suspended_seeds t
      norm_num [NativePeriodicWordLaw.InBox]
      constructor <;> linarith [hh.1,hh.2.1]

open NativePeriodicWordLaw in
private theorem curve_rates (t : CurveParameter) : Rates (curveParameters t) := by
  have he := (curve_algebra t).1
  have hh (i : Label) : h (curveParameters t) i = (t:ℝ) := he
  simp only [Rates,eta,fixedRate,hh]
  have hl : (2/9:ℝ) ≤ (t:ℝ) := by linarith [t.property.1]
  have hu := t.property.2
  exact ⟨by nlinarith [pow_le_pow_left₀ (by norm_num) hl 2], by nlinarith [pow_le_pow_left₀ (le_trans (by norm_num) t.property.1) hu 2], hl,hu⟩
open NativePeriodicWordLaw in
private theorem curve_seeds (t : CurveParameter) : Seeds (curveParameters t) := by
  intro s n hn b i
  have hcoord : ∀ n : ℕ, n ≤ 4 → ∀ (b : Letter) (i : Label),
      coord (curveParameters t) n b i = (if b=0 then curveU t else curveG t)*(t:ℝ)^n := by
    intro n hn b i
    have hh (i : Label) : h (curveParameters t) i = (t:ℝ) := (curve_algebra t).1
    have hg (i : Label) : g (curveParameters t) i = curveG t := (curve_algebra t).2
    interval_cases n <;> simp only [coord,hStep,hh] <;> split_ifs <;> (try simp only [hg]) <;> (try simp [curveParameters]) <;> first | rfl | ring
  rw [source_coord_eq]
  simp only [nativeCoord]
  cases s <;> fin_cases b
  all_goals simp only [hcoord n hn,Fin.reduceEq,if_true,if_false]
  all_goals change InBox _ _ _
  · convert (curve_finite_markers t n hn).1 using 1 <;> norm_num [pureCoord,pureCoeff,curveParameters]
  · convert (curve_finite_markers t n hn).2.1 using 1 <;> norm_num [pureCoord,pureCoeff,curveParameters]
  · convert (curve_finite_markers t n hn).2.2.1 using 1 <;> norm_num [pureCoord,pureCoeff,curveParameters]
  · convert (curve_finite_markers t n hn).2.2.2 using 1 <;> norm_num [pureCoord,pureCoeff,curveParameters]

private theorem curve_marker_bounds (t : CurveParameter) :
    (∀ n, NativePeriodicWordLaw.InBox (curveU t * (t : ℝ)^n)
      ((1/3)*(2/9)^n) ((2/5)*(6/25)^n)) ∧
    (∀ n, NativePeriodicWordLaw.InBox (curveG t * (t : ℝ)^n)
      ((4/9)*(2/9)^n) ((9/25)*(6/25)^n)) ∧
    (∀ n, NativePeriodicWordLaw.InBox (curveV t * (curveU t * (t : ℝ)^n))
      ((1/9)*(2/9)^n) ((4/25)*(6/25)^n)) ∧
    (∀ n, NativePeriodicWordLaw.InBox (curveV t * (curveG t * (t : ℝ)^n))
      ((4/27)*(2/9)^n) ((18/125)*(6/25)^n)) := by
  have hi := NativePeriodicWordLaw.all_indices (curveParameters t)
    (curve_rates t) (curve_seeds t)
  refine ⟨fun n => ?_,fun n => ?_,fun n => ?_,fun n => ?_⟩
  · have hh := hi .p n 0 2
    norm_num [NativePeriodicWordLaw.IndexedBox,NativePeriodicWordLaw.nativeCoord,
      curve_coord,NativePeriodicWordLaw.pureCoord,NativePeriodicWordLaw.pureCoeff] at hh
    exact hh
  · have hh := hi .p n 1 2
    norm_num [NativePeriodicWordLaw.IndexedBox,NativePeriodicWordLaw.nativeCoord,
      curve_coord,NativePeriodicWordLaw.pureCoord,NativePeriodicWordLaw.pureCoeff] at hh
    exact hh
  · have hh := hi .beta n 0 2
    norm_num [NativePeriodicWordLaw.IndexedBox,NativePeriodicWordLaw.nativeCoord,
      curve_coord,NativePeriodicWordLaw.pureCoord,NativePeriodicWordLaw.pureCoeff] at hh
    simpa only [curveParameters] using hh
  · have hh := hi .beta n 1 2
    norm_num [NativePeriodicWordLaw.IndexedBox,NativePeriodicWordLaw.nativeCoord,
      curve_coord,NativePeriodicWordLaw.pureCoord,NativePeriodicWordLaw.pureCoeff] at hh
    simpa only [curveParameters] using hh


private theorem curve_endpoint_box (s : ActivePhase) (t : CurveParameter) :
    EndpointBox (curveDescriptor s t) := by
  intro a
  have hreal : NativePeriodicWordLaw.InBox ((curveLaw s t : Measure _).real {a})
      ((native s lowerRate : Measure _).real {a})
      ((native s upperRate : Measure _).real {a}) := by
    rcases a with ⟨a,ha⟩
    cases a with
    | none =>
      change NativePeriodicWordLaw.InBox _ _ _
      simp only [Measure.real, show (⟨none,ha⟩ : ValidTail s) = infinity s from rfl,
        (curve_atoms t).2.2.2 s, (native_atoms lowerRate).2.2.2 s,
        (native_atoms upperRate).2.2.2 s, ENNReal.toReal_zero]
      norm_num [NativePeriodicWordLaw.InBox]
    | some w =>
      obtain ⟨b,hb⟩ := ha
      cases s with
      | p =>
        obtain ⟨n,rfl⟩ := hb
        change NativePeriodicWordLaw.InBox ((curveLaw .p t : Measure _).real {pAtom n b})
          ((native .p lowerRate : Measure _).real {pAtom n b})
          ((native .p upperRate : Measure _).real {pAtom n b})
        rw [(curve_atoms t).1]
        simp only [Measure.real, (native_atoms lowerRate).1, (native_atoms upperRate).1]
        fin_cases b <;>
          norm_num [alphaMass,betaMass,lowerRate,upperRate,unitInterval.symm,
            unitInterval.coe_toNNReal,ENNReal.toReal_mul,ENNReal.toReal_pow] <;>
          first | exact (curve_marker_bounds t).1 n | exact (curve_marker_bounds t).2.1 n
      | beta =>
        rcases hb with ⟨rfl,rfl⟩ | ⟨n,rfl⟩
        · change NativePeriodicWordLaw.InBox ((curveLaw .beta t : Measure _).real {betaStop})
            ((native .beta lowerRate : Measure _).real {betaStop})
            ((native .beta upperRate : Measure _).real {betaStop})
          rw [(curve_atoms t).2.1]
          simp only [Measure.real,(native_atoms lowerRate).2.1,(native_atoms upperRate).2.1]
          norm_num [NativePeriodicWordLaw.InBox,alphaMass,betaMass,lowerRate,upperRate,
            unitInterval.symm,unitInterval.coe_toNNReal]
          constructor <;> linarith [(scalar_boxes t).2.2.1,(scalar_boxes t).2.2.2.1]
        · change NativePeriodicWordLaw.InBox ((curveLaw .beta t : Measure _).real {betaAtom n b})
            ((native .beta lowerRate : Measure _).real {betaAtom n b})
            ((native .beta upperRate : Measure _).real {betaAtom n b})
          rw [(curve_atoms t).2.2.1]
          simp only [Measure.real,(native_atoms lowerRate).2.2.1,(native_atoms upperRate).2.2.1]
          fin_cases b <;>
            norm_num [alphaMass,betaMass,lowerRate,upperRate,unitInterval.symm,
              unitInterval.coe_toNNReal,ENNReal.toReal_mul,ENNReal.toReal_pow] <;>
            first | exact (curve_marker_bounds t).2.2.1 n | exact (curve_marker_bounds t).2.2.2 n
  rw [← native_coordinate s lowerRate a, ← native_coordinate s upperRate a]
  change min ((native s lowerRate : Measure _) {a}) ((native s upperRate : Measure _) {a}) ≤
      (curveLaw s t : Measure _) {a} ∧
    (curveLaw s t : Measure _) {a} ≤ max ((native s lowerRate : Measure _) {a})
      ((native s upperRate : Measure _) {a})
  have hA := measure_ne_top (native s lowerRate : Measure _) {a}
  have hB := measure_ne_top (native s upperRate : Measure _) {a}
  have hD := measure_ne_top (curveLaw s t : Measure _) {a}
  constructor
  · apply (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hA (min_le_left _ _)) hD).mp
    simpa only [ENNReal.toReal_min hA hB, Measure.real, NativePeriodicWordLaw.InBox] using hreal.1
  · apply (ENNReal.toReal_le_toReal hD (ne_of_lt (max_lt hA.lt_top hB.lt_top))).mp
    simpa only [ENNReal.toReal_max hA hB, Measure.real, NativePeriodicWordLaw.InBox] using hreal.2

private theorem curve_prefixB (t : CurveParameter) :
    (curveLaw .p t : Measure _).comap prependB =
      ENNReal.ofReal (1 - curveU t) • (curveLaw .beta t : Measure _) := by
  have hnon : 0 ≤ 1-curveU t := by linarith [(scalar_boxes t).2.1]
  have hreturn : ENNReal.ofReal (1-curveU t)*ENNReal.ofReal (curveV t) = ENNReal.ofReal (t:ℝ) := by
    rw [← ENNReal.ofReal_mul hnon,(curve_algebra t).1]
  have hstop : ENNReal.ofReal (1-curveU t)*ENNReal.ofReal (1-curveV t) = ENNReal.ofReal (curveG t) := by
    rw [← ENNReal.ofReal_mul hnon,(curve_algebra t).2]
  apply Measure.ext_of_singleton
  rintro ⟨a,ha⟩
  rw [prependB_embedding.comap_apply,Set.image_singleton,Measure.smul_apply,smul_eq_mul]
  cases a with
  | none =>
    change (curveLaw .p t : Measure _) {infinity .p} = _ * (curveLaw .beta t : Measure _) {infinity .beta}
    rw [(curve_atoms t).2.2.2,(curve_atoms t).2.2.2,mul_zero]
  | some w =>
    obtain ⟨b,hb⟩ := ha
    rcases hb with ⟨rfl,rfl⟩ | ⟨n,rfl⟩
    · change (curveLaw .p t : Measure _) {pAtom 0 1} = _ * (curveLaw .beta t : Measure _) {betaStop}
      rw [(curve_eatoms t).1,(curve_eatoms t).2.1]
      simpa only [Fin.reduceEq,if_false,pow_zero,mul_one] using hstop.symm
    · have he : prependB (betaAtom n b) = pAtom (n+1) b := by
        apply Subtype.ext
        exact congrArg some (p_word_succ n b).symm
      change (curveLaw .p t : Measure _) {prependB (betaAtom n b)} =
        _ * (curveLaw .beta t : Measure _) {betaAtom n b}
      rw [he,(curve_eatoms t).1,(curve_eatoms t).2.2,pow_succ]
      calc
        _ = ENNReal.ofReal (t:ℝ) * (ENNReal.ofReal (if b=0 then curveU t else curveG t)*
              ENNReal.ofReal (t:ℝ)^n) := by ring
        _ = _ := by rw [← hreturn]; ring

private theorem curve_prefixA (t : CurveParameter) :
    (curveLaw .beta t : Measure _).comap prependA =
      ENNReal.ofReal (curveV t) • (curveLaw .p t : Measure _) := by
  apply Measure.ext_of_singleton
  rintro ⟨a,ha⟩
  rw [prependA_embedding.comap_apply,Set.image_singleton,Measure.smul_apply,smul_eq_mul]
  cases a with
  | none =>
    change (curveLaw .beta t : Measure _) {infinity .beta} = _ * (curveLaw .p t : Measure _) {infinity .p}
    rw [(curve_atoms t).2.2.2,(curve_atoms t).2.2.2,mul_zero]
  | some w =>
    obtain ⟨b,n,rfl⟩ := ha
    change (curveLaw .beta t : Measure _) {betaAtom n b} = _ * (curveLaw .p t : Measure _) {pAtom n b}
    rw [(curve_eatoms t).1,(curve_eatoms t).2.2]

private theorem curve_residuals (t : CurveParameter) :
    residualB (curveDescriptor .p t) = law (curveDescriptor .beta t) ∧
    residualA (curveDescriptor .beta t) = law (curveDescriptor .p t) := by
  have hv : 0 < curveV t := by linarith [(scalar_boxes t).2.2.1]
  have hu : 0 < 1-curveU t := by linarith [(scalar_boxes t).2.1]
  have hc : 1-ENNReal.ofReal (curveU t) = ENNReal.ofReal (1-curveU t) := by
    apply ENNReal.sub_eq_of_eq_add (by finiteness)
    rw [← ENNReal.ofReal_add hu.le (by linarith [(scalar_boxes t).1])]
    simp
  constructor
  · change (1-emission .p (curveLaw .p t))⁻¹ • (curveLaw .p t : Measure _).comap prependB = _
    rw [curve_emission]
    simp only [if_true]
    rw [hc,curve_prefixB,smul_smul,ENNReal.inv_mul_cancel
      (ENNReal.ofReal_ne_zero_iff.mpr hu) ENNReal.ofReal_ne_top,one_smul]
    rfl
  · change (emission .beta (curveLaw .beta t))⁻¹ • (curveLaw .beta t : Measure _).comap prependA = _
    rw [curve_emission]
    simp only [reduceCtorEq,if_false]
    rw [curve_prefixA,smul_smul,ENNReal.inv_mul_cancel
      (ENNReal.ofReal_ne_zero_iff.mpr hv) ENNReal.ofReal_ne_top,one_smul]
    rfl

/-- Complete laws on the original regular descriptor spaces, for every parameter in J. -/
theorem continuous_descriptor_family :
    (∀ s, Measurable (curveDescriptor s)) ∧
    ∀ t : CurveParameter,
      (∀ n b, (law (curveDescriptor .p t)).real {pAtom n b} =
        (if b=0 then curveU t else curveG t)*(t:ℝ)^n) ∧
      (∀ n b, (law (curveDescriptor .beta t)).real {betaAtom n b} =
        curveV t*((if b=0 then curveU t else curveG t)*(t:ℝ)^n)) ∧
      (∀ s, law (curveDescriptor s t) Set.univ = 1 ∧
        law (curveDescriptor s t) {infinity s} = 0 ∧
        law (curveDescriptor s t) (tailSet s 0) =
          (if s=.p then 1 else ENNReal.ofReal (curveV t)) ∧
        EndpointBox (curveDescriptor s t)) ∧
      residualB (curveDescriptor .p t) = law (curveDescriptor .beta t) ∧
      residualA (curveDescriptor .beta t) = law (curveDescriptor .p t) := by
  refine ⟨curve_descriptor_measurable, fun t => ?_⟩
  refine ⟨(curve_atoms t).1,(curve_atoms t).2.2.1,?_,(curve_residuals t).1,(curve_residuals t).2⟩
  intro s
  refine ⟨measure_univ,(curve_atoms t).2.2.2 s,?_,curve_endpoint_box s t⟩
  cases s
  · simpa only [law,curveDescriptor,pow_zero,if_true] using (curve_tails t 0).1
  · simpa only [law,curveDescriptor,pow_zero,mul_one,reduceCtorEq,if_false] using (curve_tails t 0).2

def recoveredParameter (s : ActivePhase) (D : RegularDescriptor s) : ℝ :=
  match s with
  | .p => (law D).real {pAtom 1 1} / max (9/25) ((law D).real {pAtom 0 1})
  | .beta => (law D).real {betaAtom 1 1} / max (18/125) ((law D).real {betaAtom 0 1})

theorem recovered_measurable (s : ActivePhase) : Measurable (recoveredParameter s) := by
  cases s <;> unfold recoveredParameter <;>
    exact (((Measure.measurable_coe (measurableSet_singleton _)).comp
      (measurable_law _)).ennreal_toReal).div
        (measurable_const.max (((Measure.measurable_coe (measurableSet_singleton _)).comp
          (measurable_law _)).ennreal_toReal))

theorem recovered_curve (s : ActivePhase) (t : CurveParameter) :
    recoveredParameter s (curveDescriptor s t) = (t:ℝ) := by
  cases s
  · change (curveLaw .p t : Measure _).real {pAtom 1 1} /
      max (9/25) ((curveLaw .p t : Measure _).real {pAtom 0 1}) = _
    rw [(curve_atoms t).1,(curve_atoms t).1]
    simp only [Fin.reduceEq,if_false,pow_one,pow_zero,mul_one,
      max_eq_right (scalar_boxes t).2.2.2.2.1]
    exact mul_div_cancel_left₀ (t:ℝ) (ne_of_gt (by linarith [(scalar_boxes t).2.2.2.2.1]))
  · change (curveLaw .beta t : Measure _).real {betaAtom 1 1} /
      max (18/125) ((curveLaw .beta t : Measure _).real {betaAtom 0 1}) = _
    rw [(curve_atoms t).2.2.1,(curve_atoms t).2.2.1]
    simp only [Fin.reduceEq,if_false,pow_one,pow_zero,mul_one,
      max_eq_right (curve_suspended_seeds t).1]
    rw [← mul_assoc]
    exact mul_div_cancel_left₀ (t:ℝ) (ne_of_gt (by linarith [(curve_suspended_seeds t).1]))

private def clampParameter (r : ℝ) : CurveParameter :=
  ⟨max (239/1000) (min (6/25) r),⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩⟩

private theorem clamp_measurable : Measurable clampParameter := by
  unfold clampParameter
  fun_prop

private theorem clamp_curve (t : CurveParameter) : clampParameter (t:ℝ) = t := by
  apply Subtype.ext
  simp only [clampParameter,min_eq_right t.property.2,max_eq_right t.property.1]

private def curveSuccessor (s t : ActivePhase) (D : RegularDescriptor s) : RegularDescriptor t :=
  curveDescriptor t (clampParameter (recoveredParameter s D))

private theorem curve_successor_measurable (s t : ActivePhase) : Measurable (curveSuccessor s t) :=
  (continuous_descriptor_family.1 t).comp (clamp_measurable.comp (recovered_measurable s))

private theorem curve_successor_same (s t : ActivePhase) (x : CurveParameter) :
    curveSuccessor s t (curveDescriptor s x) = curveDescriptor t x := by
  simp only [curveSuccessor,recovered_curve,clamp_curve]

private def curveKernel (s t : ActivePhase) : Kernel (RegularDescriptor s) (RegularDescriptor t) :=
  Kernel.deterministic (curveSuccessor s t) (curve_successor_measurable s t)

private instance curveKernel_markov (s t : ActivePhase) : IsMarkovKernel (curveKernel s t) :=
  inferInstanceAs (IsMarkovKernel (Kernel.deterministic _ _))

def uniformReal : Measure ℝ := (1000 : ℝ≥0∞) • volume.restrict (Set.Ico (239/1000 : ℝ) (6/25))

def curveUniform : Measure CurveParameter := uniformReal.comap Subtype.val

private theorem parameter_embedding : MeasurableEmbedding (Subtype.val : CurveParameter → ℝ) :=
  MeasurableEmbedding.subtype_coe measurableSet_Icc

instance curveUniform_probability : IsProbabilityMeasure curveUniform := ⟨by
  rw [curveUniform,parameter_embedding.comap_apply,Set.image_univ,Subtype.range_coe,
    uniformReal,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply measurableSet_Icc]
  have he : Set.Icc (239/1000 : ℝ) (6/25) ∩ Set.Ico (239/1000 : ℝ) (6/25) =
      Set.Ico (239/1000 : ℝ) (6/25) := Set.inter_eq_right.mpr Set.Ico_subset_Icc_self
  rw [he,Real.volume_Ico]
  norm_num [ENNReal.ofReal_div_of_pos]
  exact ENNReal.mul_inv_cancel (by norm_num) (by finiteness)⟩

instance curveUniform_nullSingleton : NullSingletonClass curveUniform := ⟨fun x => by
  rw [curveUniform,parameter_embedding.comap_apply,Set.image_singleton,
    uniformReal,Measure.smul_apply,smul_eq_mul]
  rw [Measure.restrict_apply (measurableSet_singleton _)]
  rw [measure_mono_null Set.inter_subset_left (measure_singleton _),mul_zero]⟩

private def curveMargin (s : ActivePhase) : Measure (RegularDescriptor s) :=
  curveUniform.map (curveDescriptor s)

private instance curveMargin_probability (s : ActivePhase) : IsProbabilityMeasure (curveMargin s) := by
  unfold curveMargin
  infer_instance

private def curveGraph (s t : ActivePhase) : Measure (RegularDescriptor s × RegularDescriptor t) :=
  curveUniform.map (fun x => (curveDescriptor s x,curveDescriptor t x))

private instance curveGraph_probability (s t : ActivePhase) : IsProbabilityMeasure (curveGraph s t) := by
  unfold curveGraph
  infer_instance

private theorem curve_graph_fst (s t : ActivePhase) : (curveGraph s t).fst = curveMargin s := by
  rw [Measure.fst,curveGraph,Measure.map_map measurable_fst
    ((continuous_descriptor_family.1 s).prodMk (continuous_descriptor_family.1 t))]
  rfl

private theorem curve_graph_snd (s t : ActivePhase) : (curveGraph s t).snd = curveMargin t := by
  rw [Measure.snd,curveGraph,Measure.map_map measurable_snd
    ((continuous_descriptor_family.1 s).prodMk (continuous_descriptor_family.1 t))]
  rfl

private theorem curve_compProd (s t : ActivePhase) :
    curveMargin s ⊗ₘ curveKernel s t = curveGraph s t := by
  rw [curveKernel,Measure.compProd_deterministic,curveMargin,Measure.map_map
    (by simpa only [id_eq] using measurable_id.prodMk (curve_successor_measurable s t)) (continuous_descriptor_family.1 s)]
  simp only [Function.comp_def,curve_successor_same]
  rfl


private theorem complete_law_eq_measurable {X : Type*} [MeasurableSpace X] (s : ActivePhase)
    (f g : X → Measure (ValidTail s)) (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {x | f x = g x} := by
  have he : {x | f x = g x} = ⋂ a : ValidTail s, {x | f x {a} = g x {a}} := by
    ext x
    simp only [Set.mem_setOf_eq,Set.mem_iInter]
    exact ⟨fun h _ => congrArg (fun μ : Measure (ValidTail s) => μ {_}) h,
      fun h => Measure.ext_of_singleton h⟩
  rw [he]
  exact MeasurableSet.iInter (fun a => measurableSet_eq_fun
    ((Measure.measurable_coe (measurableSet_singleton a)).comp hf)
    ((Measure.measurable_coe (measurableSet_singleton a)).comp hg))

private theorem complete_box_measurable (s : ActivePhase) :
    MeasurableSet {D : RegularDescriptor s | EndpointBox D} := by
  simp only [EndpointBox,Set.setOf_forall]
  exact MeasurableSet.iInter (fun a =>
    (measurableSet_le measurable_const
      ((Measure.measurable_coe (measurableSet_singleton a)).comp (measurable_law s))).inter
    (measurableSet_le ((Measure.measurable_coe (measurableSet_singleton a)).comp
      (measurable_law s)) measurable_const))

/-- The actual graph measures and deterministic acquired kernels keep the same x. -/
def continuousCommonFlow : CommonFlow where
  nuP := curveMargin .p
  nuB := curveMargin .beta
  probP := inferInstance
  probB := inferInstance
  GammaB := curveGraph .p .beta
  GammaA := curveGraph .beta .p
  probGammaB := inferInstance
  probGammaA := inferInstance
  B := curveKernel .p .beta
  A := curveKernel .beta .p
  markovB := inferInstance
  markovA := inferInstance
  marginB₁ := curve_graph_fst .p .beta
  marginB₂ := curve_graph_snd .p .beta
  marginA₁ := curve_graph_fst .beta .p
  marginA₂ := curve_graph_snd .beta .p
  disintegrateB := ⟨by rw [curve_graph_fst,curve_compProd]⟩
  disintegrateA := ⟨by rw [curve_graph_fst,curve_compProd]⟩
  normalizedB := by
    apply (ae_map_iff (continuous_descriptor_family.1 .p).aemeasurable
      (complete_law_eq_measurable .beta _ _ residualB_measurable (Kernel.comp (lawKernel .beta)
        (curveKernel .p .beta)).measurable)).mpr
    apply ae_of_all
    intro x
    rw [(continuous_descriptor_family.2 x).2.2.2.1]
    change law _ = (lawKernel .beta) ∘ₘ Measure.dirac (curveSuccessor .p .beta (curveDescriptor .p x))
    rw [curve_successor_same]
    exact (Measure.dirac_bind (lawKernel .beta).measurable (curveDescriptor .beta x)).symm
  normalizedA := by
    apply (ae_map_iff (continuous_descriptor_family.1 .beta).aemeasurable
      (complete_law_eq_measurable .p _ _ residualA_measurable (Kernel.comp (lawKernel .p)
        (curveKernel .beta .p)).measurable)).mpr
    apply ae_of_all
    intro x
    rw [(continuous_descriptor_family.2 x).2.2.2.2]
    change law _ = (lawKernel .p) ∘ₘ Measure.dirac (curveSuccessor .beta .p (curveDescriptor .beta x))
    rw [curve_successor_same]
    exact (Measure.dirac_bind (lawKernel .p).measurable (curveDescriptor .p x)).symm
  boxP := by
    apply (ae_map_iff (continuous_descriptor_family.1 .p).aemeasurable
      (complete_box_measurable .p)).mpr
    exact ae_of_all _ (fun x => ((continuous_descriptor_family.2 x).2.2.1 .p).2.2.2)
  boxB := by
    apply (ae_map_iff (continuous_descriptor_family.1 .beta).aemeasurable
      (complete_box_measurable .beta)).mpr
    exact ae_of_all _ (fun x => ((continuous_descriptor_family.2 x).2.2.1 .beta).2.2.2)


def averagedCompletion (n : ℕ) : ℝ :=
  ∫ Q, (coordinate n 1 Q).toReal ∂continuousCommonFlow.nuP

theorem averaged_parameter (n : ℕ) : averagedCompletion n =
    ∫ t : CurveParameter, curveG t*(t:ℝ)^n ∂curveUniform := by
  rw [averagedCompletion]
  change (∫ Q, (coordinate n 1 Q).toReal ∂curveUniform.map (curveDescriptor .p)) = _
  rw [integral_map (continuous_descriptor_family.1 .p).aemeasurable
    ((measurable_coordinate n 1).ennreal_toReal.aestronglyMeasurable)]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  simpa only [coordinate,law,curveDescriptor,Measure.real,Fin.reduceEq,if_false]
    using (curve_atoms t).1 n 1

theorem moment_integrable (n : ℕ) :
    Integrable (fun t : CurveParameter => curveG t*(t:ℝ)^n) curveUniform := by
  have hm : Measurable (fun t : CurveParameter => curveG t*(t:ℝ)^n) := by
    unfold curveG
    fun_prop
  apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro t
  have hcoord : (curveLaw .p t : Measure _).real {pAtom n 1} =
      curveG t * (t : ℝ)^n := by
    simpa only [Fin.reduceEq, if_false] using (curve_atoms t).1 n 1
  rw [Real.norm_eq_abs, ← hcoord]
  rw [abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one



open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
open FourthSegmentStoppedLaw NativeInstalledFullLaw NativeObserverJointLaw
open NativeBorelCommonFlow NativeBorelFiniteCompleteObstruction Polynomial

private theorem polynomial_moment_expansion (p : ℝ[X]) (N : ℕ) (t : CurveParameter) :
    curveG t*(t:ℝ)^N*p.eval (t:ℝ) =
      ∑ i ∈ p.support, p.coeff i*(curveG t*(t:ℝ)^(N+i)) := by
  rw [Polynomial.eval_eq_sum,Polynomial.sum_def,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]
  ring

private theorem polynomial_moment_integrable (p : ℝ[X]) (N : ℕ) :
    Integrable (fun t : CurveParameter => curveG t*(t:ℝ)^N*p.eval (t:ℝ)) curveUniform := by
  simp_rw [polynomial_moment_expansion]
  exact integrable_finsetSum _ (fun i _ => (moment_integrable (N+i)).const_mul (p.coeff i))

private theorem polynomial_moment_integral (p : ℝ[X]) (N : ℕ) :
    (∫ t : CurveParameter, curveG t*(t:ℝ)^N*p.eval (t:ℝ) ∂curveUniform) =
      ∑ i ∈ p.support, p.coeff i*averagedCompletion (N+i) := by
  simp_rw [polynomial_moment_expansion]
  rw [integral_finsetSum _ (fun i _ => (moment_integrable (N+i)).const_mul (p.coeff i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul,← averaged_parameter]

private theorem polynomial_square_positive (p : ℝ[X]) (hp : p ≠ 0) (N : ℕ) :
    0 < ∫ t : CurveParameter, curveG t*(t:ℝ)^N*(p.eval (t:ℝ))^2 ∂curveUniform := by
  let f : CurveParameter → ℝ := fun t => curveG t*(t:ℝ)^N*(p.eval (t:ℝ))^2
  have hi : Integrable f curveUniform := by
    apply (polynomial_moment_integrable (p^2) N).congr
    apply ae_of_all
    intro t
    dsimp [f]
    rw [Polynomial.eval_pow]
  have hfinite : Set.Finite {t : CurveParameter | p.eval (t:ℝ) = 0} := by
    exact (Polynomial.finite_setOfPred_isRoot hp).preimage Subtype.val_injective.injOn
  have hnon : ∀ᵐ t : CurveParameter ∂curveUniform, p.eval (t:ℝ) ≠ 0 :=
    hfinite.countable.ae_notMem curveUniform
  have hpos : ∀ᵐ t ∂curveUniform, 0 < f t := by
    filter_upwards [hnon] with t ht
    have hx : 0 < (t:ℝ) := lt_of_lt_of_le (by norm_num) t.property.1
    have hg : 0 < curveG t := by unfold curveG curveQ; positivity
    exact mul_pos (mul_pos hg (pow_pos hx N)) (sq_pos_of_ne_zero ht)
  apply (integral_pos_iff_support_of_nonneg_ae (hpos.mono (fun _ h => h.le)) hi).mpr
  have he : Function.support f =ᵐ[curveUniform] Set.univ := by
    filter_upwards [hpos] with t ht
    apply propext
    change f t ≠ 0 ↔ True
    exact iff_true_intro (ne_of_gt ht)
  rw [measure_congr he,measure_univ]
  norm_num

/-- No nonzero recurrence, of any finite order and after any finite initial segment, fits the
actual continuous averaged coordinates. -/
theorem continuous_no_linear_recurrence (p : ℝ[X]) (hp : p ≠ 0) (N : ℕ) :
    ∃ n : ℕ, (∑ i ∈ p.support, p.coeff i*averagedCompletion (N+n+i)) ≠ 0 := by
  by_contra! hzero
  have hsquare := polynomial_square_positive p hp N
  have he : (∫ t : CurveParameter, curveG t*(t:ℝ)^N*(p.eval (t:ℝ))^2 ∂curveUniform) =
      ∑ j ∈ p.support, p.coeff j *
        (∑ i ∈ p.support, p.coeff i*averagedCompletion (N+j+i)) := by
    calc
      _ = ∫ t : CurveParameter, ∑ j ∈ p.support,
          p.coeff j * (curveG t*(t:ℝ)^(N+j)*p.eval (t:ℝ)) ∂curveUniform := by
        apply integral_congr_ae
        apply ae_of_all
        intro t
        change curveG t*(t:ℝ)^N*(p.eval (t:ℝ))^2 = _
        rw [pow_two]
        calc
          _ = (curveG t*(t:ℝ)^N*p.eval (t:ℝ))*p.eval (t:ℝ) := by ring
          _ = _ := by
            rw [polynomial_moment_expansion,Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = _ := by
        rw [integral_finsetSum _ (fun j _ => (polynomial_moment_integrable p (N+j)).const_mul
          (p.coeff j))]
        apply Finset.sum_congr rfl
        intro j _
        rw [integral_const_mul,polynomial_moment_integral]
  rw [he] at hsquare
  simp only [hzero,mul_zero,Finset.sum_const_zero] at hsquare
  exact lt_irrefl _ hsquare

/-- Every finite-dimensional homogeneous linear realization is excluded; its annihilating
polynomial would give a recurrence forbidden by the exact continuous moments. -/
theorem continuous_no_finite_linear_realization
    (V : Type*) [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    (T : Module.End ℝ V) (x : V) (ℓ : V →ₗ[ℝ] ℝ) (N : ℕ) :
    ¬ (∀ n : ℕ, averagedCompletion (N+n) = ℓ ((T^n) x)) := by
  intro h
  obtain ⟨p,hmonic,hann⟩ := LinearMap.exists_monic_and_aeval_eq_zero ℝ T
  obtain ⟨n,hn⟩ := continuous_no_linear_recurrence p hmonic.ne_zero N
  apply hn
  calc
    _ = ℓ ((aeval T p) ((T^n) x)) := by
      rw [Polynomial.aeval_def,Polynomial.eval₂_eq_sum,Polynomial.sum_def]
      simp only [LinearMap.sum_apply,map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [show N+n+i = N+(i+n) by omega,h,pow_add]
      simp [Module.End.mul_apply]
    _ = 0 := by rw [hann]; simp


universe u
variable {Z : Type u} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]


/-- Every lawful original finite COMPLETE carrier, acquired update table, installed emission
law and starting configuration distribution is excluded, even for one averaged tail coordinate. -/
theorem continuous_no_finite_complete (M : Observer Z) (e : InstalledEmitter M)
    (ρ : PMF Z) (N : ℕ) :
    ¬ (∀ n : ℕ, averagedCompletion (N+n) =
      ∑ z : Z, (ρ z).toReal * (tailLaw M e .p z).real {pAtom n 1}) := by
  intro h
  apply continuous_no_finite_linear_realization (Marked Z → ℝ)
    (letterStep M e 1 * letterStep M e 0) (cylinderVector M e [1,1]) (initialReadout ρ) N
  intro n
  rw [h]
  simp_rw [tail_coordinate,cylinderVector_pWord]
  rfl

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteCompleteObstruction
