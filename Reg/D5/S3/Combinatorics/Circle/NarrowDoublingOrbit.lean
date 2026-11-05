import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.NarrowDoublingOrbit
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Faithful whole-family audit attempts for the denominator theorem, actual
explicit numerator reconstruction and exact anchored classification.
The original five auxiliary public results remain unregistered.
Kernel compilation of these records does not establish source binding. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit

namespace Reg.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit
namespace narrow_classification

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ X Q => diameter X Q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X Q : ℕ}, 3 ≤ X → Odd X → 0 < Q → Q < X →
    2 * R.readout 0 X Q < X →
    2 ≤ period X Q ∧
    period X Q = orderOf (2 : ZMod (denominator X Q)) ∧
    denominator X Q = 2 ^ period X Q - 1 ∧
    2 * R.readout 1 X Q = X - Nat.gcd X Q

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (X := 3) (Q := 1) (by decide) (by decide)
    (by decide) (by decide) (by norm_num [rejected, realize])).2.2.2
  norm_num [rejected, realize] at hh

private theorem diameter_zero_seed (X : ℕ) : diameter X 0 = 0 := by
  classical
  unfold diameter
  split_ifs with h
  · have hz (z : ℕ) (hz : z ∈ orbit X 0) : z = 0 := by
      obtain ⟨n, _, he⟩ := Finset.mem_image.mp hz
      simpa [residue] using he.symm
    rw [hz _ ((orbit X 0).max'_mem h), hz _ ((orbit X 0).min'_mem h)]
  · rfl

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨Q, _, hQX, _, _, hdiam, _⟩ :=
    exists_narrow_of_mersenne_dvd (X := 3) (t := 2)
      (by decide) (by decide) (by decide) (by norm_num)
  refine ⟨3, 0, Q, ?_⟩
  change diameter 3 0 ≠ diameter 3 Q
  rw [diameter_zero_seed]
  omega


private theorem two_power_not_six (r : ℕ) (hr : 2 ≤ r) : 5 ≠ 2 ^ r - 1 := by
  by_cases he : r = 2
  · norm_num [he]
  · have hp : 8 ≤ 2 ^ r := by
      simpa using pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ))
        (show 3 ≤ r by omega)
    omega

private theorem actual_sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    let bad : Realization signature := realize signature
      (fun j X Q => if j = i then 0 else diameter X Q) (fun e => nomatch e)
    refine ⟨bad, ?_, rfl, ?_⟩
    · intro j hji
      funext X Q
      simp [actual, bad, realize, hji]
    · intro h
      fin_cases i
      · have hh := h (X := 5) (Q := 1) (by decide) (by decide)
          (by decide) (by decide) (by norm_num [bad, realize])
        have hd : 5 = 2 ^ period 5 1 - 1 := by
          simpa [denominator] using hh.2.2.1
        exact two_power_not_six _ hh.1 hd
      · obtain ⟨Q, hQ, hQX, _, _, _, hnarrow⟩ :=
          exists_narrow_of_mersenne_dvd (X := 3) (t := 2)
            (by decide) (by decide) (by decide) (by norm_num)
        have hh := (h (X := 3) (Q := Q) (by decide) (by decide)
          hQ hQX (by simpa [bad, realize] using hnarrow)).2.2.2
        have hg : Nat.gcd 3 Q ≤ Q := Nat.le_of_dvd hQ (Nat.gcd_dvd_right 3 Q)
        have hd : 0 = 3 - Nat.gcd 3 Q := by simpa [bad, realize] using hh
        omega
  · intro e
    exact nomatch e

def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.narrow_classification)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.narrow_classification,
    rejected, rejected_law⟩
  sensitivity := actual_sensitivity
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.narrow_classification)
    (type_of% (realize signature (fun _ X Q => diameter X Q) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.narrow_classification.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.narrow_classification.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ X Q => diameter X Q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.NarrowDoublingOrbit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "fn", "arg", "arg"]
      stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit

end narrow_classification

namespace narrow_explicit_numerator

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ X Q => orbit X Q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X Q : ℕ}, 3 ≤ X → Odd X → 0 < Q → Q < X →
    2 * diameter X Q < X →
    ∃ s u : ℕ, 0 < s ∧ s < period X Q ∧ Nat.Coprime s (period X Q) ∧
      u < period X Q ∧ (s : ZMod (period X Q)) * u = 1 ∧
      R.readout 0 X Q = (Finset.range (period X Q)).image
        (fun j => Nat.gcd X Q * explicitPoint (period X Q) s u j) ∧
      IsGreatest (↑(R.readout 0 X Q) : Set ℕ)
        (Nat.gcd X Q * explicitNumerator (period X Q) s u)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨Q, hQ, hQX, _, _, _, hn⟩ :=
    exists_narrow_of_mersenne_dvd (X := 3) (t := 2)
      (by decide) (by decide) (by decide) (by norm_num)
  obtain ⟨s, u, _, _, _, _, _, _, hg⟩ :=
    h (X := 3) (Q := Q) (by decide) (by decide) hQ hQX hn
  simpa only [rejected, realize, Finset.coe_empty, Set.mem_empty_iff_false] using hg.1

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨Q, hQ, hQX, hr, _, _, _⟩ :=
    exists_narrow_of_mersenne_dvd (X := 3) (t := 2)
      (by decide) (by decide) (by decide) (by norm_num)
  refine ⟨3, 0, Q, ?_⟩
  change orbit 3 0 ≠ orbit 3 Q
  intro he
  have hmem : Q ∈ orbit 3 Q := by
    apply Finset.mem_image.mpr
    refine ⟨0, ?_, ?_⟩
    · rw [Finset.mem_range, hr]; decide
    · simp [residue, Nat.mod_eq_of_lt hQX]
  rw [← he] at hmem
  obtain ⟨n, _, hn⟩ := Finset.mem_image.mp hmem
  have hzero : Q = 0 := by simpa [residue] using hn.symm
  omega

private theorem actual_sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact False.elim (hji (Subsingleton.elim _ _))
  · intro e
    exact nomatch e

def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.narrow_explicit_numerator)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.narrow_explicit_numerator,
    rejected, rejected_law⟩
  sensitivity := actual_sensitivity
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.narrow_explicit_numerator)
    (type_of% (realize signature (fun _ X Q => orbit X Q) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.narrow_explicit_numerator.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.narrow_explicit_numerator.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ X Q => orbit X Q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.NarrowDoublingOrbit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit

end narrow_explicit_numerator


namespace anchored_explicit_classification

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ X Q => Anchored X Q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X Q : ℕ}, 3 ≤ X → Odd X → 0 < Q → Q < X →
    (R.readout 0 X Q ↔ ∃ r s u : ℕ, 2 ≤ r ∧ 0 < s ∧ s < r ∧ Nat.Coprime s r ∧
      u < r ∧ (s : ZMod r) * u = 1 ∧ 2 ^ r - 1 ∣ X ∧
      Q = (X / (2 ^ r - 1)) * explicitNumerator r s u) ∧
    (∀ r s u : ℕ, 2 ≤ r → 0 < s → s < r → Nat.Coprime s r → u < r →
      (s : ZMod r) * u = 1 → 2 ^ r - 1 ∣ X →
      Q = (X / (2 ^ r - 1)) * explicitNumerator r s u →
      period X Q = r ∧ Nat.gcd X Q = X / (2 ^ r - 1))

private theorem three_witness :
    ∃ r s u : ℕ, 2 ≤ r ∧ 0 < s ∧ s < r ∧ Nat.Coprime s r ∧
      u < r ∧ (s : ZMod r) * u = 1 ∧ 2 ^ r - 1 ∣ 3 ∧
      2 = (3 / (2 ^ r - 1)) * explicitNumerator r s u := by
  refine ⟨2, 1, 1, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  norm_num [explicitNumerator]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (X := 3) (Q := 2) (by decide) (by decide) (by decide) (by decide)).1.mpr
    three_witness

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, 2, 1, ?_⟩
  change Anchored 3 2 ≠ Anchored 3 1
  intro he
  have htwo : Anchored 3 2 :=
    (_root_.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.anchored_explicit_classification
      (by decide) (by decide) (by decide) (by decide)).1.mpr three_witness
  have hone : Anchored 3 1 := he.mp htwo
  have hh := (hone 1).1
  norm_num [residue] at hh

private theorem actual_sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact False.elim (hji (Subsingleton.elim _ _))
  · intro e
    exact nomatch e

def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.anchored_explicit_classification)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.anchored_explicit_classification,
    rejected, rejected_law⟩
  sensitivity := actual_sensitivity
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.anchored_explicit_classification)
    (type_of% (realize signature (fun _ X Q => Anchored X Q) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.anchored_explicit_classification.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit.anchored_explicit_classification.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ X Q => Anchored X Q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.NarrowDoublingOrbit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit

end anchored_explicit_classification

end Reg.D5.S3.Combinatorics.Circle.NarrowDoublingOrbit
