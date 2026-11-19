/- GID: D5/S3/ArithUnits/MercaSquareClassNumberRefutation
   generality: I
   mirror-B: D5/B/S3/ArithUnits/MercaSquareClassNumberRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ArithUnits/MercaSquareClassNumberRefutation.claim; result=D5/S3/ArithUnits/MercaSquareClassNumberRefutation.result; claim=D5/S3/ArithUnits/MercaSquareClassNumberRefutation.claim
   digest: The genuine relative class number can be square without equal quartic coordinates. -/

import D5.S3.ArithUnits.MercaClassNumberCriterion
import Mathlib.Tactic.NormNum.LegendreSymbol

/-! The historical r=181 counterexample, with actual character and field objects.
Only finite residue computations are decided; genuine class numbers follow from
the proved universal analytic bridges. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace D5.S3.ArithUnits.MercaSquareClassNumberRefutation
open D5.S3.ArithUnits MercaQuarticCharacter MercaQuarticMoments MercaCosetFiberLift
open D5.S3.Analytic.Zeta MercaRelativeClassNumber

private instance : Fact (Nat.Prime 181) := ⟨by decide⟩
private def orbit (a : Fin 45) : (ZMod 181)ˣ := twoUnit 181 (by decide) ^ (4 * a.val)
private def orbitSet : Finset (ZMod 181)ˣ := Finset.univ.image orbit

private lemma orbit_injective : Function.Injective orbit := by decide

private lemma orbit_kernel : orbitSet = cosetFinset (kernel 181 (by decide)) 1 := by
  classical
  have hsub : orbitSet ⊆ cosetFinset (kernel 181 (by decide)) 1 := by
    intro u hu
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hu
    simp only [cosetFinset, Finset.mem_filter, Finset.mem_univ, true_and, inv_one, one_mul]
    change (character 181 (by decide)).toUnitHom (orbit a) = 1
    apply Units.ext
    change character 181 (by decide) ((orbit a : (ZMod 181)ˣ) : ZMod 181) = 1
    rw [orbit, Units.val_pow_eq_pow_val, map_pow]
    have ht : character 181 (by decide) (twoUnit 181 (by decide)) = Complex.I := by
      simpa only [twoUnit, Units.val_mk0] using (kernel_structure 181 (by decide)).2.1
    rw [ht, pow_mul, Complex.I_pow_four, one_pow]
  apply Finset.eq_of_subset_of_card_le hsub
  have hc : (cosetFinset (kernel 181 (by decide)) 1).card = 45 := by
    have he : cosetFinset (kernel 181 (by decide)) 1 = (kernel 181 (by decide) : Set (ZMod 181)ˣ).toFinset := by
      ext u
      simp [cosetFinset]
    rw [he, Set.toFinset_card]
    change Fintype.card (kernel 181 (by decide)) = 45
    rw [← Nat.card_eq_fintype_card]
    exact (kernel_structure 181 (by decide)).2.2.2.2.2.1
  rw [hc, orbitSet, Finset.card_image_of_injective _ orbit_injective]
  simp

private lemma sum_identity : sumRep 181 (by decide) 1 = 3439 := by
  rw [sumRep, ← orbit_kernel]
  decide

private lemma sum_two : sumRep 181 (by decide) (twoUnit 181 (by decide)) = 3982 := by
  have he : cosetFinset (kernel 181 (by decide)) (twoUnit 181 (by decide)) =
      orbitSet.image (fun u => twoUnit 181 (by decide) * u) := by
    rw [orbit_kernel]
    ext u
    simp only [Finset.mem_image, cosetFinset, Finset.mem_filter, Finset.mem_univ,
      true_and, inv_one, one_mul]
    constructor
    · intro hu
      exact ⟨(twoUnit 181 (by decide))⁻¹ * u, hu, by simp⟩
    · rintro ⟨v, hv, rfl⟩
      simpa using hv
  rw [sumRep, he]
  decide

private lemma coordinates :
    realCoordinate 181 (by decide) = -7 ∧ imagCoordinate 181 (by decide) = -1 := by
  norm_num [realCoordinate, imagCoordinate, coordinate, sum_identity, sum_two]

private lemma actual_relative_class_number :
    relativeClassNumber 181 (by decide) = 25 := by
  have h := relative_norm 181 (by decide) (by decide)
  rw [coordinates.1, coordinates.2] at h
  norm_num at h ⊢
  linarith

/-- The tempting square-only replacement of the actual magnitude criterion. -/
def claim : Prop :=
  ∀ (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5), 5 < r →
    (∃ n : ℕ, (n : ℚ) ^ 2 = relativeClassNumber r hr) →
      |realCoordinate r hr| = |imagCoordinate r hr|

/-- The historical actual r=181 field has h-minus=25 but coordinates -7 and -1. -/
theorem result : ¬ claim := by
  intro hc
  have he := hc 181 (by decide) (by decide) ⟨5, by norm_num [actual_relative_class_number]⟩
  norm_num [coordinates.1, coordinates.2] at he


end D5.S3.ArithUnits.MercaSquareClassNumberRefutation
