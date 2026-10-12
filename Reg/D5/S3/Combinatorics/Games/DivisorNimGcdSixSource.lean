import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Games.DivisorNimGcdSixSource
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Games.DivisorNimGcdSixSource

open _root_.D5.S3.Combinatorics.Games.DivisorNimGrundy
open _root_.D5.S0.Certificates.Games.CrimGrundyRefutation (mex)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Position
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature := realize signature
  (fun _ A n => grundy (n ::ₘ A)) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A : Position}, Positive A → A.gcd = 6 →
    (∀ n, 0 < n → (R.readout () A n = 0 ↔ n % 4 = sixZeroPhase A)) ∧
    (∀ n, 2 * A.sum < n →
      R.readout () A n = mex (fixedValues A n ∪
        {R.readout () A (n - 1), R.readout () A (n - 2),
         R.readout () A (n - 3), R.readout () A (n - 6)})) ∧
    (∀ n, 2 * A.sum + 6 < n → n % 2 = 1 →
      fixedValues A n = {0} ∧
      1 ≤ R.readout () A n ∧ R.readout () A n ≤ 4) ∧
    (∀ t, 2 * A.sum + 10 < t → t % 4 = sixZeroPhase A →
      let u := R.readout () A (t - 3)
      let v := R.readout () A (t - 1)
      let w := R.readout () A (t + 1)
      let b := R.readout () A (t + 2)
      let y := R.readout () A (t + 3)
      (1 ≤ u ∧ u ≤ 4) ∧ (1 ≤ v ∧ v ≤ 4) ∧ (1 ≤ w ∧ w ≤ 4) ∧
      u ≠ v ∧ v ≠ w ∧
      b = mex (fixedValues A (t + 2) ∪ {0, v, w}) ∧
      y = mex {0, b, w, u} ∧
      R.readout () A (t + 5) = mex {0, y, b, v}) ∧
    (∀ H, (∀ h ∈ A, h ≤ H) →
      (∀ Q ∈ moves A, Q ≠ 0 → HasTailPeriod Q (sixTargetPeriod H)) →
      ∃ N, 4 ∣ sixTargetPeriod H ∧ ∀ n, N ≤ n →
        fixedValues A (n + sixTargetPeriod H) = fixedValues A n)

noncomputable def registration : Registration arena (type_of% (@gcd_six_source_reduction)) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    constructor
    · intro A hp hg
      exact gcd_six_source_reduction hp hg
    · refine ⟨rejected, ?_⟩
      intro h
      have hp : Positive ({6} : Position) := by
        intro x hx
        have : x = 6 := by simpa using hx
        omega
      have hg : ({6} : Position).gcd = 6 := by simp
      have hh := (h (A := {6}) hp hg).2.2.1 21 (by norm_num) (by decide)
      change fixedValues {6} 21 = {0} ∧ 1 ≤ 0 ∧ 0 ≤ 4 at hh
      exact (by decide : ¬ (1 ≤ (0 : ℕ))) hh.2.1
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, ?_⟩
      · intro j hj
        exact (hj (Subsingleton.elim j i)).elim
      · intro h
        have hp : Positive ({6} : Position) := by
          intro x hx
          have : x = 6 := by simpa using hx
          omega
        have hg : ({6} : Position).gcd = 6 := by simp
        have hh := (h (A := {6}) hp hg).2.2.1 21 (by norm_num) (by decide)
        change fixedValues {6} 21 = {0} ∧ 1 ≤ 0 ∧ 0 ≤ 4 at hh
        exact (by decide : ¬ (1 ≤ (0 : ℕ))) hh.2.1
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨{6}, 1, 2, ?_⟩
    change grundy (1 ::ₘ ({6} : Position)) ≠ grundy (2 ::ₘ ({6} : Position))
    have hp : Positive ({6} : Position) := by
      intro x hx
      have : x = 6 := by simpa using hx
      omega
    have hg : ({6} : Position).gcd = 6 := by simp
    have hz := (gcd_six_source_reduction hp hg).1
    have hv : valuation 6 = 1 := valuation_eq_of_dvd_not (by decide) (by decide) (by decide)
    have hc : countAt ({6} : Position) 1 = 1 := by
      change Multiset.countP (fun h => valuation h = 1) (6 ::ₘ 0) = 1
      rw [Multiset.countP_cons, Multiset.countP_zero, if_pos hv]
    have hpz : sixZeroPhase ({6} : Position) = 2 := by
      unfold sixZeroPhase
      rw [hc]
      norm_num
    have h2 : grundy (2 ::ₘ ({6} : Position)) = 0 :=
      (hz 2 (by decide)).mpr (by rw [hpz])
    rw [h2]
    intro h1
    have he := (hz 1 (by decide)).mp h1
    rw [hpz] at he
    norm_num at he

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@gcd_six_source_reduction)
      (type_of% (realize signature (fun _ A n => grundy (n ::ₘ A))
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Games.DivisorNimGcdSixSource.informationUnit
  realizationName := `Reg.D5.S3.Combinatorics.Games.DivisorNimGcdSixSource.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ A n => grundy (n ::ₘ A))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Games.DivisorNimGcdSixSource
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }


/-- The parent conclusion uses exactly the same actual follower hypotheses. -/
abbrev parentArena : Arena where
  signature := signature
  Law R := ∀ {A : Position}, Positive A → A.gcd = 6 →
    ∀ (H : ℕ), (∀ h ∈ A, h ≤ H) →
    (∀ Q ∈ moves A, Q ≠ 0 → HasTailPeriod Q (sixTargetPeriod H)) →
    ∃ N, ∀ n, N ≤ n →
      R.readout () A (n + sixTargetPeriod H) = R.readout () A n

end Reg.D5.S3.Combinatorics.Games.DivisorNimGcdSixSource
