/- GID: D5/S3/TotalVariation/ParryFirstReturn
   generality: I
   mirror-B: D5/B/S3/TotalVariation/ParryFirstReturn
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual next-zero section and return events of the bilateral Parry source. -/

import D5.S3.TotalVariation.ParryBilateralLaw
import Mathlib.Probability.ConditionalProbability

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

private theorem shift_iterate (r : RelationPath k) (n : ℕ) (t : ℤ) :
    (relationShift^[n] r).val t = r.val (t + n) := by
  induction n generalizing r t with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', relationShift, ih]
    congr 1
    push_cast
    ring

private theorem measurable_zeroSection : MeasurableSet (zeroSection k) :=
  ((measurable_pi_apply (-1)).comp measurable_subtype_coe) (measurableSet_singleton false)

private theorem measurable_returnTime : Measurable (@returnTime k) := by
  unfold returnTime
  exact (measurable_find nextZero_exists (fun n =>
    ((measurable_pi_apply (n : ℤ)).comp measurable_subtype_coe)
      (measurableSet_singleton false))).add_const 1

private theorem measurable_returnMap : Measurable (@returnMap k) := by
  exact (measurable_from_prod_countable_right
    (fun n : ℕ => measurable_relationShift.iterate n)).comp
      (measurable_returnTime.prodMk measurable_id)

private theorem returnTime_spec (r : RelationPath k) :
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
      simpa only [zeroSection, mem_setOf_eq, shift_iterate, he] using hmem
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

private theorem translate_nat (n : ℕ) : (translate (k := k) (n : ℤ) : _ → _) = relationShift^[n] := by
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
  simpa only [returnMap, ← hnm] using hrs

private theorem returnMap_surjOn : Set.SurjOn (@returnMap k) (zeroSection k) (zeroSection k) := by
  intro r hr
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
  congr 1
  ring

end D5.S3.TotalVariation.ParryFirstReturn
