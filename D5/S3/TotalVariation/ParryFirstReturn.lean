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
    (r : RelationPath k) (t : ℤ) (n : ℕ)
    (hz : r.val (t - (n : ℤ) - 1) = false)
    (ho : ∀ i : ℕ, i < n → r.val (t - (i : ℤ) - 1) = true) :
    ((e (false, r)).val t).2.val = n := by
  have hs := hsuffix (false, r) t
  dsimp only at hs
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
    · change s.val (0 - (i.val : ℤ) - 1 + i.val) = false
      simp only [zero_sub]
      simpa only [show -(i.val : ℤ) - 1 + i.val = -1 by omega]
        using (show s.val (-1) = false from hs.1)
    · intro j hj
      change s.val (0 - (j : ℤ) - 1 + i.val) = true
      simp only [zero_sub]
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

private theorem reset_prefix_kernel_product (hk : 2 ≤ k) {m : ℕ}
    (word : Fin (m + 1) → Fin k)
    (initial : (word 0).val = 0)
    (allowed : ∀ i : Fin m,
      (word i.succ).val = 0 ∨ (word i.succ).val = (word i.castSucc).val + 1) :
    ∏ i : Fin m, suffixKernel k (word i.castSucc) (word i.succ) =
      parryParameter k ^ m * suffixWeight k (parryParameter k) (word (Fin.last m)) := by
  classical
  let p := parryParameter k
  let weight := suffixWeight k p
  have parameters := parry_stationary_law k hk
  have hp : 0 < p := lt_trans (by norm_num) parameters.1.1
  have positive (j : Fin k) : 0 < weight j := lt_of_lt_of_le hp (parameters.2.1 j).1
  have atZero (j : Fin k) (hj : j.val = 0) : weight j = 1 := by
    simpa [weight, suffixWeight, hj, rootSum] using parameters.1.2.2
  have factor (i : Fin m) :
      suffixKernel k (word i.castSucc) (word i.succ) =
        p * weight (word i.succ) / weight (word i.castSucc) := by
    rcases allowed i with hzero | hsucc
    · simp [suffixKernel, hzero, atZero _ hzero, p, weight]
    · simp [suffixKernel, hsucc, p, weight]
  have equalProducts :
      (∏ i : Fin m, weight (word i.succ)) =
        (∏ i : Fin m, weight (word i.castSucc)) * weight (word (Fin.last m)) := by
    calc
      (∏ i : Fin m, weight (word i.succ)) = ∏ j : Fin (m + 1), weight (word j) := by
        rw [Fin.prod_univ_succ, atZero _ initial, one_mul]
      _ = (∏ i : Fin m, weight (word i.castSucc)) * weight (word (Fin.last m)) :=
        Fin.prod_univ_castSucc _
  have denominator : (∏ i : Fin m, weight (word i.castSucc)) ≠ 0 :=
    (Finset.prod_pos fun i _ => positive (word i.castSucc)).ne'
  calc
    (∏ i : Fin m, suffixKernel k (word i.castSucc) (word i.succ)) =
        ∏ i : Fin m, p * weight (word i.succ) / weight (word i.castSucc) :=
      Finset.prod_congr rfl (fun i _ => factor i)
    _ = p ^ m * weight (word (Fin.last m)) := by
      rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, equalProducts]
      generalize (∏ i : Fin m, weight (word i.castSucc)) = w at denominator ⊢
      field_simp
      simp
      ring

private def returnSuffixBlock (length : Fin k) (t : Fin (length.val + 2)) : Fin k :=
  if h : t.val ≤ length.val then ⟨t.val, h.trans_lt length.isLt⟩
  else ⟨0, by have := length.isLt; omega⟩

private theorem return_suffix_block_iff
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hsuffix : ∀ (z : Bool × RelationPath k) (t : ℤ),
      let j := ((e z).val t).2.val
      z.2.val (t - (j : ℤ) - 1) = false ∧
      ∀ i : ℕ, i < j → z.2.val (t - (i : ℤ) - 1) = true)
    (r : RelationPath k) (length : Fin k) :
    (r ∈ zeroSection k ∧ returnTime r = length.val + 1) ↔
      ∀ t : Fin (length.val + 2), ((e (false, r)).val (t.val : ℤ)).2 =
        returnSuffixBlock length t := by
  constructor
  · rintro ⟨hsection, hreturn⟩ t
    have hfind : Nat.find (nextZero_exists r) = length.val :=
      Nat.add_right_cancel hreturn
    have terminal : r.val (length.val : ℤ) = false := by
      simpa only [hfind] using Nat.find_spec (nextZero_exists r)
    have consecutive (i : ℕ) (hi : i < length.val) : r.val (i : ℤ) = true := by
      have hnot := Nat.find_min (nextZero_exists r) (hfind ▸ hi)
      cases hb : r.val (i : ℤ) <;> simp_all
    apply Fin.ext
    by_cases ht : t.val ≤ length.val
    · simp only [returnSuffixBlock, dite_eq_left ht]
      apply suffix_eq_of_window e hsuffix
      · simpa only [sub_self, zero_sub] using (show r.val (-1) = false from hsection)
      · intro i hi
        have index : ((t.val - i - 1 : ℕ) : ℤ) = (t.val : ℤ) - i - 1 := by omega
        rw [← index]
        exact consecutive _ (by omega)
    · simp only [returnSuffixBlock, dite_eq_right ht]
      apply (suffix_zero_iff e hsuffix r _).2
      have index : (t.val : ℤ) - 1 = length.val := by
        have := t.isLt
        omega
      simpa only [index] using terminal
  · intro cylinder
    have initial := congrArg Fin.val (cylinder 0)
    have hstart : r ∈ zeroSection k := by
      apply (suffix_zero_iff e hsuffix r 0).1
      simpa [returnSuffixBlock] using initial
    refine ⟨hstart, returnTime_eq r (length.val + 1) (by omega) ?_ ?_⟩
    · let last : Fin (length.val + 2) := ⟨length.val + 1, by omega⟩
      have hlast := congrArg Fin.val (cylinder last)
      have hzero : ((e (false, r)).val ((length.val + 1 : ℕ) : ℤ)).2.val = 0 := by
        simpa [last, returnSuffixBlock] using hlast
      have hb := (suffix_zero_iff e hsuffix r _).1 hzero
      simpa using hb
    · intro i hi
      let t : Fin (length.val + 2) := ⟨i + 1, by omega⟩
      have hvalue := congrArg Fin.val (cylinder t)
      have hvalue' : ((e (false, r)).val ((i + 1 : ℕ) : ℤ)).2.val = i + 1 := by
        simpa [t, returnSuffixBlock, show i + 1 ≤ length.val by omega] using hvalue
      cases hb : r.val (i : ℤ)
      · have hj := (suffix_zero_iff e hsuffix r ((i + 1 : ℕ) : ℤ)).2 (by simpa using hb)
        omega
      · rfl

private theorem suffix_iterate_shift
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hsuffix : ∀ (z : Bool × RelationPath k) (t : ℤ),
      let j := ((e z).val t).2.val
      z.2.val (t - (j : ℤ) - 1) = false ∧
      ∀ i : ℕ, i < j → z.2.val (t - (i : ℤ) - 1) = true)
    (r : RelationPath k) (n : ℕ) (t : ℤ) :
    ((e (false, relationShift^[n] r)).val t).2 = ((e (false, r)).val (t + n)).2 := by
  apply Fin.ext
  apply suffix_eq_of_window e hsuffix
  · rw [shift_iterate]
    convert (hsuffix (false, r) (t + n)).1 using 2
    omega
  · intro i hi
    rw [shift_iterate]
    convert (hsuffix (false, r) (t + n)).2 i hi using 2
    omega

private theorem conditioned_reset_prefix (hk : 2 ≤ k)
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
          ENNReal.ofReal (suffixKernel k (v i.castSucc) (v i.succ)))
    {m : ℕ} (word : Fin (m + 1) → Fin k)
    (initial : (word 0).val = 0)
    (allowed : ∀ i : Fin m,
      (word i.succ).val = 0 ∨ (word i.succ).val = (word i.castSucc).val + 1) :
    sectionMeasure (μ : Measure (RelationPath k))
      {r | (fun i : Fin (m + 1) => ((e (false, r)).val (i.val : ℤ)).2) = word} =
        ENNReal.ofReal
          (parryParameter k ^ m * suffixWeight k (parryParameter k) (word (Fin.last m))) := by
  let C : Set (RelationPath k) :=
    {r | (fun i : Fin (m + 1) => ((e (false, r)).val (i.val : ℤ)).2) = word}
  change sectionMeasure (μ : Measure (RelationPath k)) C = _
  have contained : C ⊆ zeroSection k := by
    intro r hr
    have hzero := congrArg (fun v : Fin (m + 1) → Fin k => (v 0).val) hr
    apply (suffix_zero_iff e hsuffix r 0).1
    simpa [initial, Fin.val_zero] using hzero
  have hsystem := actual_first_return_system hk e μ hsuffix hμ hcylinder
  have hC := hcylinder 0 m word
  simp only [zero_add] at hC
  change (μ : Measure (RelationPath k)) C = _ at hC
  have hp : 0 < parryParameter k := lt_trans (by norm_num) (parry_stationary_law k hk).1.1
  have positive (j : Fin k) : 0 < suffixWeight k (parryParameter k) j :=
    lt_of_lt_of_le hp ((parry_stationary_law k hk).2.1 j).1
  have nonnegative (i : Fin m) :
      0 ≤ suffixKernel k (word i.castSucc) (word i.succ) := by
    unfold suffixKernel
    split_ifs
    · exact div_nonneg hp.le (positive _).le
    · exact div_nonneg (mul_nonneg hp.le (positive _).le) (positive _).le
    · exact le_rfl
  have weight0 : suffixWeight k (parryParameter k) (word 0) = 1 := by
    simpa [suffixWeight, initial, rootSum] using (parry_stationary_law k hk).1.2.2
  have startMass : suffixLaw k (word 0) = 1 / normalizer k := by
    simp [suffixLaw, initial, weight0]
  have noInfinite : (μ : Measure (RelationPath k)) (zeroSection k) ≠ ∞ :=
    measure_ne_top _ _
  rw [sectionMeasure, ProbabilityTheory.cond_apply measurable_zeroSection,
    inter_eq_right.mpr contained, hC, startMass, ← hsystem.2.1,
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => nonnegative i),
    reset_prefix_kernel_product hk word initial allowed, ← mul_assoc,
    ENNReal.inv_mul_cancel hsystem.2.2.1.ne' noInfinite, one_mul]

private def returnSpan : List (Fin k) → ℕ
  | [] => 0
  | n :: ns => n.val + 1 + returnSpan ns

private def returnWord (hk : 0 < k) :
    (ns : List (Fin k)) → Fin (returnSpan ns + 1) → Fin k
  | [], _ => ⟨0, hk⟩
  | n :: ns, i =>
    if hi : i.val ≤ n.val then ⟨i.val, hi.trans_lt n.isLt⟩
    else returnWord hk ns ⟨i.val - (n.val + 1), by
      have h := i.isLt
      simp only [returnSpan] at h
      omega⟩

private theorem returnWord_initial (hk : 0 < k) (ns : List (Fin k)) :
    (returnWord hk ns 0).val = 0 := by
  cases ns <;> simp [returnWord]

private theorem returnWord_terminal (hk : 0 < k) (ns : List (Fin k)) :
    (returnWord hk ns (Fin.last (returnSpan ns))).val = 0 := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    have h : ¬(Fin.last (returnSpan (n :: ns))).val ≤ n.val := by
      simp only [Fin.val_last, returnSpan]
      omega
    rw [returnWord, dite_eq_right h]
    convert ih using 3
    apply Fin.ext
    simp [returnSpan]

private theorem returnWord_allowed (hk : 0 < k) (ns : List (Fin k)) :
    ∀ i : Fin (returnSpan ns),
      (returnWord hk ns i.succ).val = 0 ∨
        (returnWord hk ns i.succ).val = (returnWord hk ns i.castSucc).val + 1 := by
  induction ns with
  | nil =>
    intro i
    have hi := i.isLt
    simp [returnSpan] at hi
  | cons n ns ih =>
    intro i
    by_cases hin : i.val + 1 ≤ n.val
    · right
      simp [returnWord, hin, show i.val ≤ n.val by omega]
    by_cases hcut : i.val ≤ n.val
    · left
      have he : i.val + 1 - (n.val + 1) = 0 := by omega
      simp [returnWord, hin, he, returnWord_initial]
    let j : Fin (returnSpan ns) := ⟨i.val - (n.val + 1), by
      have h := i.isLt
      simp only [returnSpan] at h
      omega⟩
    have hfirst : (returnWord hk (n :: ns) i.castSucc).val =
        (returnWord hk ns j.castSucc).val := by
      simp only [returnWord, Fin.val_castSucc, dite_eq_right hcut]
      rfl
    have hnext : (returnWord hk (n :: ns) i.succ).val =
        (returnWord hk ns j.succ).val := by
      simp only [returnWord, Fin.val_succ, dite_eq_right hin]
      congr 2
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [hfirst, hnext] using ih j

/-- Match the first successive positive return times, with each entry stored
one below its duration so that the alphabet is `Fin k`. -/
noncomputable def matchesReturnTimes (r : RelationPath k) : List (Fin k) → Bool
  | [] => true
  | n :: ns => decide (returnTime r = n.val + 1) && matchesReturnTimes (returnMap r) ns

private theorem matchesReturnTimes_cons (r : RelationPath k) (n : Fin k) (ns : List (Fin k)) :
    matchesReturnTimes r (n :: ns) = true ↔
      returnTime r = n.val + 1 ∧ matchesReturnTimes (returnMap r) ns = true := by
  simp [matchesReturnTimes, Bool.and_eq_true]

private theorem returnWord_head (hk : 0 < k) (n : Fin k) (ns : List (Fin k))
    (t : Fin (n.val + 2)) (u : Fin (returnSpan (n :: ns) + 1))
    (same : u.val = t.val) :
    returnWord hk (n :: ns) u = returnSuffixBlock n t := by
  apply Fin.ext
  by_cases ht : t.val ≤ n.val
  · simp [returnWord, returnSuffixBlock, ht, same]
  · have index : t.val - (n.val + 1) = 0 := by
      have h := t.isLt
      omega
    simp [returnWord, returnSuffixBlock, ht, same, index, returnWord_initial]

private theorem returnWord_tail (hk : 0 < k) (n : Fin k) (ns : List (Fin k))
    (t : Fin (returnSpan ns + 1)) (u : Fin (returnSpan (n :: ns) + 1))
    (index : u.val = t.val + (n.val + 1)) :
    returnWord hk (n :: ns) u = returnWord hk ns t := by
  have outside : ¬u.val ≤ n.val := by omega
  rw [returnWord, dite_eq_right outside]
  congr 1
  apply Fin.ext
  simp [index]

private theorem return_word_iff (hk : 0 < k)
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hsuffix : ∀ (z : Bool × RelationPath k) (t : ℤ),
      let j := ((e z).val t).2.val
      z.2.val (t - (j : ℤ) - 1) = false ∧
      ∀ i : ℕ, i < j → z.2.val (t - (i : ℤ) - 1) = true)
    (ns : List (Fin k)) (r : RelationPath k) :
    (r ∈ zeroSection k ∧ matchesReturnTimes r ns = true) ↔
      ∀ i : Fin (returnSpan ns + 1), ((e (false, r)).val (i.val : ℤ)).2 =
        returnWord hk ns i := by
  induction ns generalizing r with
  | nil =>
    constructor
    · rintro ⟨hr, _⟩ i
      have index : i.val = 0 := by
        have hi := i.isLt
        simp only [returnSpan] at hi
        omega
      apply Fin.ext
      simpa [returnWord, index] using (suffix_zero_iff e hsuffix r 0).2 hr
    · intro h
      refine ⟨(suffix_zero_iff e hsuffix r 0).1 ?_, rfl⟩
      simpa [returnWord] using congrArg Fin.val (h 0)
  | cons n ns ih =>
    constructor
    · rintro ⟨hsection, htimes⟩ i
      obtain ⟨hreturn, htail⟩ := (matchesReturnTimes_cons r n ns).1 htimes
      by_cases hhead : i.val ≤ n.val
      · let t : Fin (n.val + 2) := ⟨i.val, by omega⟩
        rw [returnWord_head hk n ns t i rfl]
        exact (return_suffix_block_iff e hsuffix r n).1 ⟨hsection, hreturn⟩ t
      · let t : Fin (returnSpan ns + 1) := ⟨i.val - (n.val + 1), by
          have hi := i.isLt
          simp only [returnSpan] at hi
          omega⟩
        have index : i.val = t.val + (n.val + 1) := by dsimp [t]; omega
        rw [returnWord_tail hk n ns t i index]
        have hshifted := (ih (returnMap r)).1 ⟨(returnTime_spec r).2.2.1, htail⟩ t
        rw [returnMap, hreturn, suffix_iterate_shift e hsuffix] at hshifted
        have indexZ : (i.val : ℤ) = (t.val : ℤ) + ((n.val + 1 : ℕ) : ℤ) := by omega
        simpa only [indexZ] using hshifted
    · intro h
      have hblock : ∀ t : Fin (n.val + 2),
          ((e (false, r)).val (t.val : ℤ)).2 = returnSuffixBlock n t := by
        intro t
        let u : Fin (returnSpan (n :: ns) + 1) := ⟨t.val, by
          have ht := t.isLt
          simp only [returnSpan]
          omega⟩
        simpa only [returnWord_head hk n ns t u rfl] using h u
      obtain ⟨hsection, hreturn⟩ := (return_suffix_block_iff e hsuffix r n).2 hblock
      refine ⟨hsection, (matchesReturnTimes_cons r n ns).2
        ⟨hreturn, ((ih (returnMap r)).2 (fun t => ?_)).2⟩⟩
      let u : Fin (returnSpan (n :: ns) + 1) := ⟨t.val + (n.val + 1), by
        have ht := t.isLt
        simp only [returnSpan]
        omega⟩
      rw [returnMap, hreturn, suffix_iterate_shift e hsuffix]
      have indexZ : (u.val : ℤ) = (t.val : ℤ) + ((n.val + 1 : ℕ) : ℤ) := by
        dsimp [u]
      simpa only [indexZ, returnWord_tail hk n ns t u rfl] using h u

private theorem returnSpan_weight (p : ℝ) (ns : List (Fin k)) :
    p ^ returnSpan ns = (ns.map fun n => p ^ (n.val + 1)).prod := by
  induction ns with
  | nil => simp [returnSpan]
  | cons n ns ih => simp [returnSpan, pow_add, ih]

/-- The conditioned bilateral Parry law assigns a product of geometric
weights to every finite prefix of actual successive return times. -/
theorem return_time_cylinder_probability (hk : 2 ≤ k)
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
          ENNReal.ofReal (suffixKernel k (v i.castSucc) (v i.succ)))
    (ns : List (Fin k)) :
    sectionMeasure (μ : Measure (RelationPath k)) {r | matchesReturnTimes r ns = true} =
      ENNReal.ofReal ((ns.map fun n => parryParameter k ^ (n.val + 1)).prod) := by
  have hkpos : 0 < k := by omega
  have events :
      zeroSection k ∩ {r | matchesReturnTimes r ns = true} =
      {r | (fun i : Fin (returnSpan ns + 1) => ((e (false, r)).val (i.val : ℤ)).2) =
        returnWord hkpos ns} := by
    ext r
    change (r ∈ zeroSection k ∧ matchesReturnTimes r ns = true) ↔ _
    rw [return_word_iff hkpos e hsuffix]
    exact ⟨funext, fun h i => congrFun h i⟩
  have support :
      sectionMeasure (μ : Measure (RelationPath k))
        (zeroSection k ∩ {r | matchesReturnTimes r ns = true}) =
      sectionMeasure (μ : Measure (RelationPath k)) {r | matchesReturnTimes r ns = true} :=
    ProbabilityTheory.cond_inter_self measurable_zeroSection _ _
  rw [← support, events, conditioned_reset_prefix hk e μ hsuffix hμ hcylinder
    (returnWord hkpos ns) (returnWord_initial hkpos ns) (returnWord_allowed hkpos ns)]
  have terminalWeight : suffixWeight k (parryParameter k)
      (returnWord hkpos ns (Fin.last (returnSpan ns))) = 1 := by
    simpa [suffixWeight, rootSum, returnWord_terminal hkpos ns] using
      (parry_stationary_law k hk).1.2.2
  rw [terminalWeight, mul_one, returnSpan_weight]

/-- Compare the actual raw window with the Boolean labels of a suffix path. -/
def matchesRawWindow {m : ℕ} (r : RelationPath k) (word : Fin (m + 1) → Fin k) : Bool :=
  decide (∀ i : Fin m, r.val (i.val : ℤ) = decide ((word i.succ).val ≠ 0))

private theorem suffix_edge (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (r : RelationPath k) (t : ℤ) :
    ((e (false, r)).val (t + 1)).2.val = 0 ∨
      ((e (false, r)).val (t + 1)).2.val = ((e (false, r)).val t).2.val + 1 := by
  by_contra! h
  have hp := (e (false, r)).property t
  simpa [kernel, h.1, h.2] using hp

private theorem bits_iff_suffix_prefix
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (hsuffix : ∀ (z : Bool × RelationPath k) (t : ℤ),
      let j := ((e z).val t).2.val
      z.2.val (t - (j : ℤ) - 1) = false ∧
      ∀ i : ℕ, i < j → z.2.val (t - (i : ℤ) - 1) = true)
    (r : RelationPath k) {m : ℕ} (word : Fin (m + 1) → Fin k)
    (initial : (word 0).val = 0)
    (allowed : ∀ i : Fin m,
      (word i.succ).val = 0 ∨ (word i.succ).val = (word i.castSucc).val + 1) :
    (r ∈ zeroSection k ∧ ∀ i : Fin m, r.val (i.val : ℤ) = decide ((word i.succ).val ≠ 0)) ↔
      (fun i : Fin (m + 1) => ((e (false, r)).val (i.val : ℤ)).2) = word := by
  let actual (i : Fin (m + 1)) := ((e (false, r)).val (i.val : ℤ)).2
  have zero_iff (i : Fin m) : (actual i.succ).val = 0 ↔ r.val (i.val : ℤ) = false := by
    simpa [actual] using suffix_zero_iff e hsuffix r ((i.val : ℤ) + 1)
  constructor
  · rintro ⟨hr, hbits⟩
    change actual = word
    funext i
    induction i using Fin.induction with
    | zero =>
      apply Fin.ext
      rw [initial]
      have h := (suffix_zero_iff e hsuffix r 0).2 (show r.val (-1) = false from hr)
      simpa [actual] using h
    | succ i ih =>
      have hzero : (actual i.succ).val = 0 ↔ (word i.succ).val = 0 := by
        rw [zero_iff, hbits i]
        simp
      apply Fin.ext
      by_cases hz : (word i.succ).val = 0
      · rw [hz]
        exact hzero.mpr hz
      · have hw := (allowed i).resolve_left hz
        have ha := (suffix_edge e r (i.val : ℤ)).resolve_left (fun hx =>
          hz (hzero.mp (by simpa [actual] using hx)))
        have ha' : (actual i.succ).val = (actual i.castSucc).val + 1 := by
          simpa [actual] using ha
        rw [ha', hw, ih]
  · intro hs
    change actual = word at hs
    refine ⟨?_, fun i => ?_⟩
    · change r.val (-1) = false
      apply (suffix_zero_iff e hsuffix r 0).mp
      simpa [actual] using (congrArg (fun f => (f 0).val) hs).trans initial
    · rw [← hs]
      by_cases hz : (actual i.succ).val = 0
      · simpa [hz] using (zero_iff i).mp hz
      · have hn : r.val (i.val : ℤ) ≠ false := fun h => hz ((zero_iff i).mpr h)
        simpa [hz] using Bool.eq_true_of_ne_false hn

/-- A legal finite raw prefix observed immediately after a reset has mass
given by the reciprocal root for each consumed bit and the final suffix weight. -/
theorem zero_section_raw_window (hk : 2 ≤ k)
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
          ENNReal.ofReal (suffixKernel k (v i.castSucc) (v i.succ)))
    {m : ℕ} (word : Fin (m + 1) → Fin k) (initial : (word 0).val = 0)
    (allowed : ∀ i : Fin m,
      (word i.succ).val = 0 ∨ (word i.succ).val = (word i.castSucc).val + 1) :
    sectionMeasure (μ : Measure (RelationPath k))
      {r | matchesRawWindow r word = true} =
        ENNReal.ofReal
          (parryParameter k ^ m * suffixWeight k (parryParameter k) (word (Fin.last m))) := by
  let raw : Set (RelationPath k) := {r | matchesRawWindow r word = true}
  have event : zeroSection k ∩ raw =
      {r | (fun i : Fin (m + 1) => ((e (false, r)).val (i.val : ℤ)).2) = word} := by
    ext r
    simpa [raw, matchesRawWindow] using bits_iff_suffix_prefix e hsuffix r word initial allowed
  calc
    sectionMeasure (μ : Measure (RelationPath k)) raw =
        sectionMeasure (μ : Measure (RelationPath k)) (zeroSection k ∩ raw) :=
      (ProbabilityTheory.cond_inter_self measurable_zeroSection _ _).symm
    _ = _ := event ▸ conditioned_reset_prefix hk e μ hsuffix hμ hcylinder word initial allowed

end D5.S3.TotalVariation.ParryFirstReturn
