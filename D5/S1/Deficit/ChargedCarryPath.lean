/- GID: D5/S1/Deficit/ChargedCarryPath
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   digest: Raw carry paths have a unique signed bottom-carry charge, classified by golden phases. -/

import D5.S1.Digit.CarryStepConfluence
import D5.S1.Deficit.Beatty.BetaBeattyClosedForms
import D5.S1.Deficit.FixedModulusNoncongruence
import Mathlib.Tactic.LinearCombination

/-!
# Charged raw carry paths

This module refines arbitrary raw Zeckendorf carry reductions with an integer
charge: the two exceptional bottom rules contribute `+1` and `-1`, while the
internal rules contribute zero. A constructor-level GoldenInt ledger proves
that both the canonical endpoint and total charge are independent of the path.

For canonical-addend inputs, the same invariant is identified with the golden
Beatty deficit. This supports the paper's strengthened central claim by deriving
the exact three phase regions and proving that no fixed congruence modulus can
determine the normalization charge.

The repository and pinned Mathlib were searched first. D5 contains the public
normalizer, confluence, Beatty closed forms, phase classifier, and modulus
non-determinacy theorem, but no charged relation or path ledger. The one-step
`betaDigits` lemmas in `DeficitInteger` are private, so the local constructor
calculation below is the first reusable public ledger for arbitrary carry paths.
-/

namespace D5.S1.Deficit

open D5.S0.Carrier
open D5.S1.Deficit.BetaBeattyClosedForms
open D5.S1.Deficit.FixedModulusNoncongruence
open D5.S1.Deficit.GoldenPhaseDeficit
open D5.S1.Deficit.ZeckendorfDisplacementReading
open D5.S1.Digit

/-- A raw carry step together with its signed exceptional-bottom-rule charge. -/
inductive ChargedCarryStep : RawDigits → RawDigits → ℤ → Prop
  /-- An adjacent carry is internal and has charge zero. -/
  | adjacent (rest : RawDigits) (i : ℕ) :
      ChargedCarryStep
        (rest + Finsupp.single i 1 + Finsupp.single (i + 1) 1)
        (rest + Finsupp.single (i + 2) 1) 0
  /-- The lowest repeated carry has charge `+1`. -/
  | double_zero (rest : RawDigits) :
      ChargedCarryStep
        (rest + Finsupp.single 0 2)
        (rest + Finsupp.single 1 1) 1
  /-- The second repeated carry has charge `-1`. -/
  | double_one (rest : RawDigits) :
      ChargedCarryStep
        (rest + Finsupp.single 1 2)
        (rest + Finsupp.single 0 1 + Finsupp.single 2 1) (-1)
  /-- Every higher repeated carry is internal and has charge zero. -/
  | double_succ (rest : RawDigits) (i : ℕ) :
      ChargedCarryStep
        (rest + Finsupp.single (i + 2) 2)
        (rest + Finsupp.single i 1 + Finsupp.single (i + 3) 1) 0

/-- A finite raw carry reduction whose third index is the sum of its step charges. -/
inductive ChargedReduces : RawDigits → RawDigits → ℤ → Prop
  /-- The empty reduction has charge zero. -/
  | refl (r : RawDigits) : ChargedReduces r r 0
  /-- Appending one charged step adds its charge to the path total. -/
  | tail {r s t : RawDigits} {z w : ℤ} :
      ChargedReduces r s z →
      ChargedCarryStep s t w →
      ChargedReduces r t (z + w)

/-- Forgetting a charge recovers the underlying raw `CarryStep`. -/
theorem ChargedCarryStep.toCarryStep {r s : RawDigits} {z : ℤ}
    (h : ChargedCarryStep r s z) : CarryStep r s := by
  cases h with
  | adjacent rest i => exact CarryStep.adjacent rest i
  | double_zero rest => exact CarryStep.double_zero rest
  | double_one rest => exact CarryStep.double_one rest
  | double_succ rest i => exact CarryStep.double_succ rest i

/-- Forgetting all charges maps a charged path to the raw reflexive-transitive closure. -/
theorem ChargedReduces.toReflTransGen {r s : RawDigits} {z : ℤ}
    (h : ChargedReduces r s z) : Relation.ReflTransGen CarryStep r s := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact ih.tail step.toCarryStep

private theorem betaDigits_add (r s : RawDigits) :
    betaDigits (r + s) = betaDigits r + betaDigits s := by
  classical
  refine Finsupp.sum_add_index' (fun i => ?_) (fun i m₁ m₂ => ?_)
  · simp
  · push_cast
    ring

@[simp] private theorem betaDigits_single (i coefficient : ℕ) :
    betaDigits (Finsupp.single i coefficient) =
      (coefficient : GoldenInt) * phi ^ (i + 2) := by
  classical
  rw [betaDigits, Finsupp.sum_single_index (by simp)]

private theorem phi_pow_carry (n : ℕ) :
    phi ^ (n + 2) = phi ^ (n + 1) + phi ^ n := by
  rw [pow_add, phi_sq]
  ring

/-- One charged carry changes the GoldenInt model-set value by exactly its label. -/
theorem betaDigits_sub_chargedCarryStep {r s : RawDigits} {z : ℤ}
    (h : ChargedCarryStep r s z) :
    betaDigits r - betaDigits s = (z : GoldenInt) := by
  cases h with
  | adjacent rest i =>
      simp only [betaDigits_add, betaDigits_single]
      push_cast
      linear_combination -(phi_pow_carry (i + 2))
  | double_zero rest =>
      simp only [betaDigits_add, betaDigits_single]
      push_cast
      linear_combination (1 - phi) * phi_sq
  | double_one rest =>
      simp only [betaDigits_add, betaDigits_single]
      push_cast
      linear_combination (-phi ^ 2 + phi - 1) * phi_sq
  | double_succ rest i =>
      simp only [betaDigits_add, betaDigits_single]
      push_cast
      linear_combination
        (phi_pow_carry (i + 2)) - (phi_pow_carry (i + 3))

/-- The GoldenInt difference across a charged path is exactly its total charge. -/
theorem betaDigits_sub_chargedReduces {r s : RawDigits} {z : ℤ}
    (h : ChargedReduces r s z) :
    betaDigits r - betaDigits s = (z : GoldenInt) := by
  induction h with
  | refl => simp
  | tail _ step ih =>
      rw [Int.cast_add]
      linear_combination ih + betaDigits_sub_chargedCarryStep step

/-- Charged reductions from one source to canonical endpoints have the same endpoint
and the same total signed charge. -/
theorem charged_normal_form_unique
    {r s t : RawDigits} {z w : ℤ}
    (hs : ChargedReduces r s z) (hsc : CanonicalRaw s)
    (ht : ChargedReduces r t w) (htc : CanonicalRaw t) :
    s = t ∧ z = w := by
  have hst : s = t := by
    rw [reachable_canonical_eq_normalize hs.toReflTransGen hsc,
      reachable_canonical_eq_normalize ht.toReflTransGen htc]
  refine ⟨hst, ?_⟩
  have hz := betaDigits_sub_chargedReduces hs
  have hw := betaDigits_sub_chargedReduces ht
  rw [hst] at hz
  have hcast : (z : GoldenInt) = (w : GoldenInt) := hz.symm.trans hw
  exact congrArg GoldenInt.a hcast

/-- A single charged carry is a one-step charged reduction. -/
theorem ChargedReduces.single {r s : RawDigits} {z : ℤ}
    (h : ChargedCarryStep r s z) : ChargedReduces r s z := by
  simpa using ChargedReduces.tail (ChargedReduces.refl r) h

/-- Charged reductions compose and their total charges add. -/
theorem ChargedReduces.trans {r s t : RawDigits} {z w : ℤ}
    (hrs : ChargedReduces r s z) (hst : ChargedReduces s t w) :
    ChargedReduces r t (z + w) := by
  induction hst with
  | refl => simpa using hrs
  | @tail u v q p hu step ih =>
      simpa [Int.add_assoc] using ChargedReduces.tail ih step

private theorem chargedCarryRepeated {r : RawDigits} {i : ℕ} (hi : 2 ≤ r i) :
    ChargedCarryStep r (carryRepeated r i)
      (if i = 0 then 1 else if i = 1 then -1 else 0) := by
  have hle : Finsupp.single i 2 ≤ r := Finsupp.single_le_iff.mpr hi
  have hrest : r - Finsupp.single i 2 + Finsupp.single i 2 = r :=
    tsub_add_cancel_of_le hle
  rcases i with _ | _ | i
  · have step := ChargedCarryStep.double_zero (r - Finsupp.single 0 2)
    rw [hrest] at step
    simpa [carryRepeated] using step
  · have step := ChargedCarryStep.double_one (r - Finsupp.single 1 2)
    rw [hrest] at step
    simpa [carryRepeated] using step
  · have step := ChargedCarryStep.double_succ (r - Finsupp.single (i + 2) 2) i
    rw [hrest] at step
    simpa [carryRepeated] using step

private theorem chargedCarryAdjacent {r : RawDigits} {i : ℕ}
    (hi : r i = 1) (hnext : r (i + 1) = 1) :
    ChargedCarryStep r (carryAdjacent r i) 0 := by
  have hle : Finsupp.single i 1 + Finsupp.single (i + 1) 1 ≤ r := by
    intro j
    by_cases hj : j = i
    · subst j
      simp [hi]
    by_cases hjnext : j = i + 1
    · subst j
      simp [hnext]
    · simp [hj, hjnext]
  have hrest :
      r - (Finsupp.single i 1 + Finsupp.single (i + 1) 1) +
          (Finsupp.single i 1 + Finsupp.single (i + 1) 1) = r :=
    tsub_add_cancel_of_le hle
  have step := ChargedCarryStep.adjacent
    (r - (Finsupp.single i 1 + Finsupp.single (i + 1) 1)) i
  rw [add_assoc, hrest] at step
  simpa only [carryAdjacent] using step

private theorem chargedCarryPass {r : RawDigits} (h : ¬ CanonicalRaw r) :
    ChargedCarryStep r (carryPass r) (carrySign r) := by
  classical
  rw [carryPass, carrySign]
  split
  next hrepeat =>
    exact chargedCarryRepeated (Nat.find_spec hrepeat)
  next hrepeat =>
    split
    next hadjacent =>
      exact chargedCarryAdjacent (Nat.find_spec hadjacent).1
        (Nat.find_spec hadjacent).2
    next hadjacent =>
      exfalso
      apply h
      have hbinary : ∀ i, r i ≤ 1 := by
        intro i
        by_contra hi
        exact hrepeat ⟨i, by omega⟩
      refine ⟨hbinary, ?_⟩
      intro i hi
      by_contra hnext
      apply hadjacent
      refine ⟨i, hi, ?_⟩
      have := hbinary (i + 1)
      omega

/-- The fixed normalizer has a charged derivation whose total is `carrySignedCount`. -/
theorem charged_normalize_exists (r : RawDigits) :
    ChargedReduces r (normalize r) (carrySignedCount r) := by
  rw [D5.S1.Digit.normalize, D5.S1.Deficit.carrySignedCount]
  split
  next h => exact ChargedReduces.refl r
  next h =>
    exact ChargedReduces.trans (ChargedReduces.single (chargedCarryPass h))
      (charged_normalize_exists (carryPass r))
termination_by (tokenCount r, indexWeight r)
decreasing_by
  apply carryStep_measure_decreases
  apply carryPass_step
  assumption

/-- The analytic golden-addition deficit equals the integer golden Beatty coboundary. -/
theorem deficit_eq_beattyDeficit (v₁ v₂ : ℕ) :
    deficit v₁ v₂ = (beattyDeficit v₁ v₂ : ℝ) := by
  have hshift (v : ℕ) : (displacementDecode v : ℤ) = goldenShift v :=
    displacement_decode_eq_beatty_floor v
  have hshiftReal (v : ℕ) : (displacementDecode v : ℝ) = (goldenShift v : ℝ) := by
    exact_mod_cast hshift v
  rw [deficit, betaReal_eq_displacement_sub_goldenConj,
    betaReal_eq_displacement_sub_goldenConj,
    betaReal_eq_displacement_sub_goldenConj, beattyDeficit]
  rw [hshiftReal, hshiftReal, hshiftReal]
  push_cast
  ring

/-- On canonical-addend inputs, the deterministic signed carry count is the Beatty deficit. -/
theorem carrySignedCount_eq_beattyDeficit (v₁ v₂ : ℕ) :
    carrySignedCount (toRaw (Z v₁) + toRaw (Z v₂)) = beattyDeficit v₁ v₂ := by
  have hcount := (deficit_integer v₁ v₂).2.2
  have hbeat := deficit_eq_beattyDeficit v₁ v₂
  exact_mod_cast hcount.symm.trans hbeat

/-- The signed carry charge is `+1`, `-1`, or zero exactly on the three golden
phase-sum regions cut out by `φ⁻¹` and `φ`. -/
theorem carrySignedCount_phase_classifier (v₁ v₂ : ℕ) :
    let c := carrySignedCount (toRaw (Z v₁) + toRaw (Z v₂))
    (c = 1 ↔ goldenPhase v₁ + goldenPhase v₂ < Real.goldenRatio⁻¹) ∧
    (c = -1 ↔ Real.goldenRatio ≤ goldenPhase v₁ + goldenPhase v₂) ∧
    (c = 0 ↔ Real.goldenRatio⁻¹ ≤ goldenPhase v₁ + goldenPhase v₂ ∧
      goldenPhase v₁ + goldenPhase v₂ < Real.goldenRatio) := by
  rw [carrySignedCount_eq_beattyDeficit]
  exact golden_phase_deficit v₁ v₂

/-- For every fixed modulus at least two, coordinatewise-congruent input pairs can
have different signed carry charges. -/
theorem carryCharge_not_determined_by_fixed_modulus (m : ℕ) (hm : 2 ≤ m) :
    ∃ v₁ v₂ v₁' v₂' : ℕ,
      Nat.ModEq m v₁ v₁' ∧ Nat.ModEq m v₂ v₂' ∧
      carrySignedCount (toRaw (Z v₁) + toRaw (Z v₂)) ≠
        carrySignedCount (toRaw (Z v₁') + toRaw (Z v₂')) := by
  obtain ⟨v₁, v₂, v₁', v₂', h₁, h₂, hne⟩ :=
    deficit_not_determined_by_fixed_modulus m hm
  refine ⟨v₁, v₂, v₁', v₂', h₁, h₂, ?_⟩
  intro heq
  apply hne
  rw [(deficit_integer v₁ v₂).2.2, (deficit_integer v₁' v₂').2.2]
  exact_mod_cast heq

end D5.S1.Deficit
