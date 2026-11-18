/- GID: D5/S3/TotalVariation/ParryFirstReturn
   generality: I
   mirror-B: D5/B/S3/TotalVariation/ParryFirstReturn
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual next-zero section and return events of the bilateral Parry source. -/

import D5.S3.TotalVariation.ParryBilateralLaw
import Mathlib.Probability.ConditionalProbability

/-! # The actual bounded zero-section return map -/

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal BigOperators
open D5.S3.TotalVariation.ParryBilateralLaw
open D5.S3.TotalVariation.ParryResetLaw
open D5.S3.TotalVariation.TwistedResetPaths

namespace D5.S3.TotalVariation.ParryFirstReturn

variable {k : ℕ}

/-- The native section immediately after a zero relation bit. -/
def zeroSection (k : ℕ) : Set (RelationPath k) := {r | r.val (-1) = false}

private theorem nextZero_exists (r : RelationPath k) : ∃ n : ℕ, r.val (n : ℤ) = false := by
  obtain ⟨i, hi⟩ := r.property 0
  exact ⟨i.val, by simpa using hi⟩

/-- The actual least positive return to `zeroSection`, measured in shift steps. -/
noncomputable def returnTime (r : RelationPath k) : ℕ :=
  Nat.find (nextZero_exists r) + 1

/-- The actual induced map, represented on the ambient space with its section-supported measure. -/
noncomputable def returnMap (r : RelationPath k) : RelationPath k :=
  relationShift^[returnTime r] r

/-- Literal normalized restriction to the native zero section. -/
noncomputable def sectionMeasure (μ : Measure (RelationPath k)) : Measure (RelationPath k) :=
  ProbabilityTheory.cond μ (zeroSection k)

private theorem measurable_relationShift : Measurable (@relationShift k) := by
  apply Measurable.subtype_mk
  exact Measurable.of_eval fun t => (measurable_pi_apply (t + 1)).comp measurable_subtype_coe

theorem shift_iterate (r : RelationPath k) (n : ℕ) (t : ℤ) :
    (relationShift^[n] r).val t = r.val (t + n) := by
  induction n generalizing r t with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (relationShift^[n] r).val (t + 1) = r.val (t + (n + 1 : ℕ))
    rw [ih]
    exact congrArg r.val (show t + 1 + (n : ℤ) = t + (n + 1 : ℕ) by omega)

private theorem measurable_zeroSection : MeasurableSet (zeroSection k) := by
  have hm : Measurable (fun r : RelationPath k => r.val (-1)) :=
    (measurable_pi_apply (-1)).comp measurable_subtype_coe
  exact hm (measurableSet_singleton false)

theorem measurable_returnTime : Measurable (@returnTime k) := by
  unfold returnTime
  have hm : Measurable (fun r : RelationPath k => Nat.find (nextZero_exists r)) := by
    apply measurable_find
    intro n
    have he : Measurable (fun r : RelationPath k => r.val (n : ℤ)) :=
      (measurable_pi_apply (n : ℤ)).comp measurable_subtype_coe
    exact he (measurableSet_singleton false)
  exact hm.add_const 1

private theorem measurable_returnMap : Measurable (@returnMap k) := by
  have hm : Measurable (fun p : ℕ × RelationPath k => relationShift^[p.1] p.2) :=
    measurable_from_prod_countable_right (fun n : ℕ => measurable_relationShift.iterate n)
  exact hm.comp (measurable_returnTime.prodMk measurable_id)

theorem returnTime_spec (r : RelationPath k) :
    0 < returnTime r ∧ returnTime r ≤ k ∧
    returnMap r ∈ zeroSection k ∧
    ∀ n : ℕ, 0 < n → n < returnTime r → relationShift^[n] r ∉ zeroSection k := by
  have hs := Nat.find_spec (nextZero_exists r)
  obtain ⟨i, hi⟩ := r.property 0
  have hle := Nat.find_min' (nextZero_exists r) (by simpa using hi)
  have hil := i.isLt
  refine ⟨by simp [returnTime], by dsimp [returnTime]; omega, ?_, ?_⟩
  · change (relationShift^[returnTime r] r).val (-1) = false
    rw [shift_iterate]
    simpa [returnTime] using hs
  · intro n hn hnt hmem
    have he : -1 + (n : ℤ) = ((n - 1 : ℕ) : ℤ) := by omega
    have hz : r.val ((n - 1 : ℕ) : ℤ) = false := by
      simpa only [zeroSection, mem_ofPred_eq, shift_iterate, he] using hmem
    exact Nat.find_min (nextZero_exists r) (by dsimp [returnTime] at hnt; omega) hz

private theorem returnTime_eq (r : RelationPath k) (n : ℕ) (hn : 0 < n)
    (hz : r.val ((n : ℤ) - 1) = false)
    (ho : ∀ i : ℕ, i + 1 < n → r.val (i : ℤ) = true) : returnTime r = n := by
  have he : Nat.find (nextZero_exists r) = n - 1 := by
    apply (Nat.find_eq_iff (nextZero_exists r)).2
    refine ⟨?_, ?_⟩
    · simpa only [show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 by omega] using hz
    · intro i hi
      rw [ho i (by omega)]
      decide
  dsimp [returnTime]
  omega

private def translate (n : ℤ) : RelationPath k ≃ᵐ RelationPath k where
  toFun r := ⟨fun t => r.val (t + n), fun t => by
    obtain ⟨i, hi⟩ := r.property (t + n)
    exact ⟨i, by simpa only [show t + (i.val : ℤ) + n = t + n + i.val by ring] using hi⟩⟩
  invFun r := ⟨fun t => r.val (t - n), fun t => by
    obtain ⟨i, hi⟩ := r.property (t - n)
    exact ⟨i, by simpa only [show t + (i.val : ℤ) - n = t - n + i.val by ring] using hi⟩⟩
  left_inv r := by apply Subtype.ext; funext t; simp
  right_inv r := by apply Subtype.ext; funext t; simp
  measurable_toFun := by
    apply Measurable.subtype_mk
    exact Measurable.of_eval fun t => (measurable_pi_apply _).comp measurable_subtype_coe
  measurable_invFun := by
    apply Measurable.subtype_mk
    exact Measurable.of_eval fun t => (measurable_pi_apply _).comp measurable_subtype_coe

private theorem translate_nat (n : ℕ) :
    (translate (k := k) (n : ℤ) : _ → _) = relationShift^[n] := by
  funext r
  apply Subtype.ext
  funext t
  exact (shift_iterate r n t).symm

private theorem returnMap_injOn : Set.InjOn (@returnMap k) (zeroSection k) := by
  intro r hr s hs hrs
  let n := returnTime r
  let m := returnTime s
  have hn := returnTime_spec r
  have hm := returnTime_spec s
  have he (t : ℤ) : r.val (t + n) = s.val (t + m) := by
    have hh := congrArg (fun w : RelationPath k => w.val t) hrs
    simpa only [returnMap, shift_iterate] using hh
  have hnm : n = m := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hbad := hm.2.2.2 (m - n) (by omega) (by dsimp [n, m] at *; omega)
      apply hbad
      change (relationShift^[m - n] s).val (-1) = false
      rw [shift_iterate]
      have hh := he (-1 - n)
      have he₁ : -1 - (n : ℤ) + n = -1 := by ring
      have he₂ : -1 - (n : ℤ) + m = -1 + ((m - n : ℕ) : ℤ) := by omega
      rw [he₁, he₂] at hh
      exact hh.symm.trans hr
    · have hbad := hn.2.2.2 (n - m) (by omega) (by dsimp [n, m] at *; omega)
      apply hbad
      change (relationShift^[n - m] r).val (-1) = false
      rw [shift_iterate]
      have hh := he (-1 - m)
      have he₁ : -1 - (m : ℤ) + m = -1 := by ring
      have he₂ : -1 - (m : ℤ) + n = -1 + ((n - m : ℕ) : ℤ) := by omega
      rw [he₁, he₂] at hh
      exact hh.trans hs
  apply (translate (n : ℤ)).injective
  rw [translate_nat]
  change relationShift^[n] r = relationShift^[m] s at hrs
  rwa [← hnm] at hrs

private theorem returnMap_surjOn : Set.SurjOn (@returnMap k) (zeroSection k) (zeroSection k) := by
  intro r hr
  change r.val (-1) = false at hr
  have hp : ∃ n : ℕ, r.val (-(n : ℤ) - 2) = false := by
    obtain ⟨i, hi⟩ := r.property (-(k : ℤ) - 1)
    refine ⟨k - i.val - 1, ?_⟩
    have hil := i.isLt
    simpa only [show -(((k - i.val - 1 : ℕ) : ℤ)) - 2 =
      -(k : ℤ) - 1 + i.val by omega] using hi
  let m := Nat.find hp
  let s := (translate (k := k) (-((m + 1 : ℕ) : ℤ))) r
  have hs : s ∈ zeroSection k := by
    change r.val (-1 + -((m + 1 : ℕ) : ℤ)) = false
    simpa only [show -1 + -((m + 1 : ℕ) : ℤ) = -(m : ℤ) - 2 by omega] using Nat.find_spec hp
  have htime : returnTime s = m + 1 := by
    apply returnTime_eq s (m + 1) (by omega)
    · change r.val (((m + 1 : ℕ) : ℤ) - 1 + -((m + 1 : ℕ) : ℤ)) = false
      simpa using hr
    · intro i hi
      change r.val ((i : ℤ) + -((m + 1 : ℕ) : ℤ)) = true
      have hmin := Nat.find_min hp (show m - i - 1 < Nat.find hp by dsimp [m] at *; omega)
      have he : -(((m - i - 1 : ℕ) : ℤ)) - 2 = (i : ℤ) + -((m + 1 : ℕ) : ℤ) := by omega
      rw [he] at hmin
      cases hb : r.val ((i : ℤ) + -((m + 1 : ℕ) : ℤ)) <;> simp_all
  refine ⟨s, hs, ?_⟩
  apply Subtype.ext
  funext t
  change (relationShift^[returnTime s] s).val t = r.val t
  rw [htime, shift_iterate]
  change r.val (t + (m + 1 : ℕ) + -((m + 1 : ℕ) : ℤ)) = r.val t
  exact congrArg r.val (by omega)

private theorem returnMap_preserves_restrict (μ : Measure (RelationPath k))
    (hμ : μ.map relationShift = μ) :
    MeasurePreserving returnMap (μ.restrict (zeroSection k)) (μ.restrict (zeroSection k)) := by
  classical
  have hT : MeasurePreserving (@relationShift k) μ μ := ⟨measurable_relationShift, hμ⟩
  refine ⟨measurable_returnMap, ?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply measurable_returnMap hB,
    Measure.restrict_apply (measurable_returnMap hB), Measure.restrict_apply hB]
  let C (n : ℕ) : Set (RelationPath k) :=
    {r | r ∈ zeroSection k ∧ returnTime r = n + 1 ∧ returnMap r ∈ B}
  let D (n : ℕ) : Set (RelationPath k) := (translate ((n + 1 : ℕ) : ℤ)) '' C n
  have hC (n : ℕ) : MeasurableSet (C n) :=
    measurable_zeroSection.inter
      ((measurable_returnTime (measurableSet_singleton _)).inter (measurable_returnMap hB))
  have hD (n : ℕ) : MeasurableSet (D n) :=
    (translate _).measurableEmbedding.measurableSet_image.mpr (hC n)
  have hCD (n : ℕ) (r : RelationPath k) (hr : r ∈ C n) :
      translate ((n + 1 : ℕ) : ℤ) r = returnMap r := by
    rw [translate_nat]
    change relationShift^[n + 1] r = relationShift^[returnTime r] r
    rw [hr.2.1]
  have hdisC : Pairwise (Disjoint on C) := by
    intro n m hnm
    change Disjoint (C n) (C m)
    rw [Set.disjoint_left]
    intro r hr hs
    exact hnm (by have := hr.2.1; have := hs.2.1; omega)
  have hdisD : Pairwise (Disjoint on D) := by
    intro n m hnm
    change Disjoint (D n) (D m)
    rw [Set.disjoint_left]
    rintro y ⟨r, hr, hry⟩ ⟨s, hs, hsy⟩
    have he : returnMap r = returnMap s := by rw [← hCD n r hr, ← hCD m s hs, hry, hsy]
    have hrs := returnMap_injOn hr.1 hs.1 he
    subst s
    exact hnm (by have := hr.2.1; have := hs.2.1; omega)
  have hunC : ⋃ n, C n = returnMap ⁻¹' B ∩ zeroSection k := by
    ext r
    simp only [mem_iUnion, C, mem_ofPred_eq, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨n, hr, _, hB⟩
      exact ⟨hB, hr⟩
    · rintro ⟨hb, hr⟩
      have hp := (returnTime_spec r).1
      exact ⟨returnTime r - 1, hr, by omega, hb⟩
  have hunD : ⋃ n, D n = B ∩ zeroSection k := by
    ext y
    simp only [mem_iUnion, D, mem_image, mem_inter_iff]
    constructor
    · rintro ⟨n, r, hr, rfl⟩
      rw [hCD n r hr]
      exact ⟨hr.2.2, (returnTime_spec r).2.2.1⟩
    · rintro ⟨hb, hy⟩
      obtain ⟨r, hr, rfl⟩ := returnMap_surjOn hy
      have hp := (returnTime_spec r).1
      refine ⟨returnTime r - 1, r, ⟨hr, by omega, hb⟩, ?_⟩
      exact hCD _ r ⟨hr, by omega, hb⟩
  have hmass (n : ℕ) : μ (D n) = μ (C n) := by
    have ht : MeasurePreserving (translate (k := k) ((n + 1 : ℕ) : ℤ)) μ μ := by
      rw [translate_nat]
      exact hT.iterate (n + 1)
    have hi := (MeasurePreserving.symm
      (translate (k := k) ((n + 1 : ℕ) : ℤ)) ht).measure_preimage_equiv (C n)
    exact (congrArg μ ((translate _).image_eq_preimage_symm (C n))).trans hi
  rw [← hunC, measure_iUnion hdisC hC, ← hunD, measure_iUnion hdisD hD]
  exact tsum_congr fun n => (hmass n).symm

private theorem suffix_zero_iff
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hsuffix : ∀ (z : Bool × RelationPath k) (t : ℤ),
      let j := ((e z).val t).2.val
      z.2.val (t - (j : ℤ) - 1) = false ∧
      ∀ i : ℕ, i < j → z.2.val (t - (i : ℤ) - 1) = true)
    (r : RelationPath k) (t : ℤ) :
    ((e (false, r)).val t).2.val = 0 ↔ r.val (t - 1) = false := by
  have hs := hsuffix (false, r) t
  dsimp only at hs
  constructor
  · intro hj
    simpa only [hj, Nat.cast_zero, sub_zero] using hs.1
  · intro hz
    by_contra hne
    have ho := hs.2 0 (Nat.pos_of_ne_zero hne)
    simp only [Nat.cast_zero, sub_zero] at ho
    rw [hz] at ho
    contradiction

private theorem suffix_eq_of_window
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hsuffix : ∀ (z : Bool × RelationPath k) (t : ℤ),
      let j := ((e z).val t).2.val
      z.2.val (t - (j : ℤ) - 1) = false ∧
      ∀ i : ℕ, i < j → z.2.val (t - (i : ℤ) - 1) = true)
    (r : RelationPath k) (n : ℕ)
    (hz : r.val (-(n : ℤ) - 1) = false)
    (ho : ∀ i : ℕ, i < n → r.val (-(i : ℤ) - 1) = true) :
    ((e (false, r)).val 0).2.val = n := by
  have hs := hsuffix (false, r) 0
  dsimp only at hs
  simp only [zero_sub] at hs
  apply le_antisymm
  · by_contra h
    have hh := hs.2 n (Nat.lt_of_not_ge h)
    rw [hz] at hh
    contradiction
  · by_contra h
    have hh := ho _ (Nat.lt_of_not_ge h)
    rw [hs.1] at hh
    contradiction

private theorem actual_return_floor
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hsuffix : ∀ (z : Bool × RelationPath k) (t : ℤ),
      let j := ((e z).val t).2.val
      z.2.val (t - (j : ℤ) - 1) = false ∧
      ∀ i : ℕ, i < j → z.2.val (t - (i : ℤ) - 1) = true)
    (i : Fin k) :
    (translate (i.val : ℤ)) '' {r | r ∈ zeroSection k ∧ i.val < returnTime r} =
      {r | ((e (false, r)).val 0).2 = i} := by
  classical
  ext r
  constructor
  · rintro ⟨s, hs, rfl⟩
    apply Fin.ext
    apply suffix_eq_of_window e hsuffix
    · change s.val (-(i.val : ℤ) - 1 + i.val) = false
      simpa only [show -(i.val : ℤ) - 1 + i.val = -1 by omega]
        using (show s.val (-1) = false from hs.1)
    · intro j hj
      change s.val (-(j : ℤ) - 1 + i.val) = true
      have hmin := Nat.find_min (nextZero_exists s)
        (show i.val - j - 1 < Nat.find (nextZero_exists s) by
          dsimp [returnTime] at hs
          omega)
      have he : ((i.val - j - 1 : ℕ) : ℤ) = -(j : ℤ) - 1 + i.val := by omega
      rw [he] at hmin
      cases hb : s.val (-(j : ℤ) - 1 + i.val) <;> simp_all
  · intro hr
    have hs := hsuffix (false, r) 0
    dsimp only at hs
    rw [hr] at hs
    simp only [zero_sub] at hs
    let s := translate (- (i.val : ℤ)) r
    have hsA : s ∈ zeroSection k := by
      change r.val (-1 + -(i.val : ℤ)) = false
      simpa only [show -1 + -(i.val : ℤ) = -(i.val : ℤ) - 1 by omega] using hs.1
    have htime : i.val < returnTime s := by
      by_contra h
      have hle := Nat.le_of_not_gt h
      let m := Nat.find (nextZero_exists s)
      have hm : m + 1 ≤ i.val := hle
      have hmin := Nat.find_spec (nextZero_exists s)
      change r.val ((m : ℤ) + -(i.val : ℤ)) = false at hmin
      have hprev := hs.2 (i.val - m - 1) (by omega)
      have he : -(((i.val - m - 1 : ℕ) : ℤ)) - 1 = (m : ℤ) + -(i.val : ℤ) := by omega
      rw [he, hmin] at hprev
      contradiction
    refine ⟨s, ⟨hsA, htime⟩, ?_⟩
    apply Subtype.ext
    funext t
    change r.val (t + i.val + -(i.val : ℤ)) = r.val t
    simp

private theorem actual_return_occupation
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hsuffix : ∀ (z : Bool × RelationPath k) (t : ℤ),
      let j := ((e z).val t).2.val
      z.2.val (t - (j : ℤ) - 1) = false ∧
      ∀ i : ℕ, i < j → z.2.val (t - (i : ℤ) - 1) = true)
    (μ : Measure (RelationPath k)) (hμ : μ.map relationShift = μ) :
    μ = ∑ i : Fin k,
      (μ.restrict {r | r ∈ zeroSection k ∧ i.val < returnTime r}).map
        (relationShift^[i.val]) := by
  classical
  let floor (i : Fin k) : Set (RelationPath k) := {r | ((e (false, r)).val 0).2 = i}
  have hm : Measurable (fun r : RelationPath k => ((e (false, r)).val 0).2) :=
    measurable_snd.comp ((measurable_pi_apply 0).comp
      (measurable_subtype_coe.comp (e.measurable.comp (measurable_const.prodMk measurable_id))))
  have hfloor (i : Fin k) : MeasurableSet (floor i) := hm (measurableSet_singleton i)
  have hdis : Pairwise (Disjoint on floor) := by
    intro i j hij
    change Disjoint (floor i) (floor j)
    rw [Set.disjoint_left]
    intro r hri hrj
    exact hij (hri.symm.trans hrj)
  have hcover : ⋃ i : Fin k, floor i = Set.univ := by
    ext r
    simp only [mem_iUnion, mem_univ, iff_true]
    exact ⟨((e (false, r)).val 0).2, rfl⟩
  have hT : MeasurePreserving (@relationShift k) μ μ := ⟨measurable_relationShift, hμ⟩
  have he (i : Fin k) :
      (μ.restrict {r | r ∈ zeroSection k ∧ i.val < returnTime r}).map
        (relationShift^[i.val]) = μ.restrict (floor i) := by
    have hi : MeasurePreserving (translate (k := k) (i.val : ℤ)) μ μ := by
      rw [translate_nat]
      exact hT.iterate i.val
    have hr := hi.restrict_image_emb (translate _).measurableEmbedding
      {r | r ∈ zeroSection k ∧ i.val < returnTime r}
    have hh := hr.map_eq
    rw [actual_return_floor e hsuffix i, translate_nat] at hh
    exact hh
  simp_rw [he]
  apply Measure.ext
  intro B hB
  simp only [Measure.finsetSum_apply]
  simp only [Measure.restrict_apply hB]
  have hD : Pairwise (Disjoint on fun i : Fin k => B ∩ floor i) := by
    intro i j hij
    exact (hdis hij).mono inter_subset_right inter_subset_right
  have hu : ⋃ i : Fin k, B ∩ floor i = B := by rw [← inter_iUnion, hcover, inter_univ]
  have hsum := measure_iUnion hD (fun i => hB.inter (hfloor i)) (μ := μ)
  rw [hu, tsum_fintype] at hsum
  exact hsum

/-- For any one of the simultaneous bilateral Parry witnesses, the zero section
is literally `J₀ = 0`, has positive mass `1 / normalizer k`, and its actual
least-positive-return map preserves the literal normalized restriction. -/
theorem actual_first_return_system (hk : 2 ≤ k)
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (μ : ProbabilityMeasure (RelationPath k))
    (hsuffix : ∀ (z : Bool × RelationPath k) (t : ℤ),
      let j := ((e z).val t).2.val
      z.2.val (t - (j : ℤ) - 1) = false ∧
      ∀ i : ℕ, i < j → z.2.val (t - (i : ℤ) - 1) = true)
    (hμ : (μ : Measure (RelationPath k)).map relationShift = μ)
    (hcylinder : ∀ (ell : ℤ) (m : ℕ) (v : Fin (m + 1) → Fin k),
      (μ : Measure (RelationPath k))
        {r | (fun i : Fin (m + 1) => ((e (false, r)).val (ell + i.val)).2) = v} =
        ENNReal.ofReal (suffixLaw k (v 0)) * ∏ i : Fin m,
          ENNReal.ofReal (suffixKernel k (v i.castSucc) (v i.succ))) :
    zeroSection k = {r | ((e (false, r)).val 0).2.val = 0} ∧
    (μ : Measure (RelationPath k)) (zeroSection k) = ENNReal.ofReal (1 / normalizer k) ∧
    0 < (μ : Measure (RelationPath k)) (zeroSection k) ∧
    IsProbabilityMeasure (sectionMeasure (μ : Measure (RelationPath k))) ∧
    MeasurePreserving returnMap (sectionMeasure (μ : Measure (RelationPath k)))
      (sectionMeasure (μ : Measure (RelationPath k))) ∧
    ((μ : Measure (RelationPath k)) = (μ : Measure (RelationPath k)) (zeroSection k) •
      ∑ i : Fin k, ((sectionMeasure (μ : Measure (RelationPath k))).restrict
        {r | i.val < returnTime r}).map (relationShift^[i.val])) ∧
    (∀ r : RelationPath k, 0 < returnTime r ∧ returnTime r ≤ k ∧
      returnMap r ∈ zeroSection k ∧
      ∀ n : ℕ, 0 < n → n < returnTime r → relationShift^[n] r ∉ zeroSection k) := by
  classical
  have hsection : zeroSection k = {r | ((e (false, r)).val 0).2.val = 0} := by
    ext r
    exact (suffix_zero_iff e hsuffix r 0).symm
  have hmass : (μ : Measure (RelationPath k)) (zeroSection k) =
      ENNReal.ofReal (1 / normalizer k) := by
    let z : Fin k := ⟨0, by omega⟩
    have he := hcylinder 0 0 (fun _ => z)
    have hset : {r | (fun i : Fin 1 => ((e (false, r)).val (0 + i.val)).2) = fun _ => z} =
        zeroSection k := by
      rw [hsection]
      ext r
      simp only [mem_ofPred_eq, funext_iff]
      constructor
      · intro h
        have hh := congrArg Fin.val (h 0)
        simpa [z] using hh
      · intro h i
        have hi : i.val = 0 := by have := i.isLt; omega
        apply Fin.ext
        simpa [hi, z] using h
    rw [hset] at he
    have hweight : suffixWeight k (parryParameter k) z = 1 := by
      simpa [suffixWeight, rootSum, z] using (parry_stationary_law k hk).1.2.2
    simpa [suffixLaw, z, hweight] using he
  have hpos : 0 < (μ : Measure (RelationPath k)) (zeroSection k) := by
    rw [hmass, ENNReal.ofReal_pos]
    exact one_div_pos.mpr (lt_of_lt_of_le zero_lt_one (parry_stationary_law k hk).2.2.1)
  have hoccupation := actual_return_occupation e hsuffix (μ : Measure (RelationPath k)) hμ
  have hnormalize (i : Fin k) :
      (μ : Measure (RelationPath k)) (zeroSection k) •
        ((sectionMeasure (μ : Measure (RelationPath k))).restrict
          {r | i.val < returnTime r}).map (relationShift^[i.val]) =
      ((μ : Measure (RelationPath k)).restrict
        {r | r ∈ zeroSection k ∧ i.val < returnTime r}).map (relationShift^[i.val]) := by
    rw [← Measure.map_smul _ (measurable_relationShift.iterate i.val).aemeasurable]
    congr 1
    rw [sectionMeasure, ProbabilityTheory.cond, Measure.restrict_smul, smul_smul,
      ENNReal.mul_inv_cancel hpos.ne' (measure_ne_top _ _), one_smul,
      Measure.restrict_restrict' measurable_zeroSection]
    congr 1
    ext r
    exact and_comm
  exact ⟨hsection, hmass, hpos, ProbabilityTheory.cond_isProbabilityMeasure hpos.ne',
    (returnMap_preserves_restrict (μ : Measure (RelationPath k)) hμ).smul_measure _,
    by rw [Finset.smul_sum]; simp_rw [hnormalize]; exact hoccupation,
    returnTime_spec⟩

end D5.S3.TotalVariation.ParryFirstReturn
