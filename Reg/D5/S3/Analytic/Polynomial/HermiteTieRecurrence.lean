import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Polynomial.HermiteTieRecurrence
import Reg.Support.DependentFamily

/-! Source-family audit of the complete Hermite absolute-tie recurrence. -/

namespace Reg.D5.S3.Analytic.Polynomial.HermiteTieRecurrence
open _root_.D5.S3.Analytic.Polynomial.HermiteTieRecurrence
open _root_.D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders (HasExactlyTwo)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => HasExactlyTwo k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r :=
    ∃ g : ℤ → ℕ,
      (∀ n : ℤ, 1 ≤ n → 0 < g n) ∧
      (∀ n m : ℤ, 1 ≤ n → n < m → g n < g m) ∧
      (∀ k : ℕ, r.readout () () k ↔ ∃! n : ℤ, 1 ≤ n ∧ k = g n) ∧
      ∀ n : ℤ, 6 ≤ n →
        (g n : ℤ) = (g (n-1) : ℤ) + 2 * (g (n-2) : ℤ) -
          2 * (g (n-3) : ℤ) - (g (n-4) : ℤ) + (g (n-5) : ℤ)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨g, hp, _, he, _⟩
  obtain ⟨n, ⟨hn, hv⟩, _⟩ := (he 0).mp True.intro
  have hh := hp n hn
  omega

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    have hzero : ¬ HasExactlyTwo 0 := by
      intro h
      obtain ⟨n, ⟨hn, he⟩, _⟩ :=
        (_root_.D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders.result.2.2 0).mp h
      have hp := _root_.D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders.result.1 n hn
      omega
    have height : HasExactlyTwo 8 := by
      apply (_root_.D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders.result.2.2 8).mpr
      refine ⟨1, ⟨by decide, by norm_num [_root_.D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders.a]⟩, ?_⟩
      rintro n ⟨hn, he⟩
      by_contra hne
      have hlt : 1 < n := by omega
      have hh := _root_.D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders.result.2.1 1 n (by decide) hlt
      have hone : _root_.D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders.a 1 = 8 := by
        norm_num [_root_.D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders.a]
      rw [hone, ← he] at hh
      omega
    refine ⟨(), 8, 0, ?_⟩
    change HasExactlyTwo 8 ≠ HasExactlyTwo 0
    intro he
    exact hzero (he ▸ height)

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Polynomial.HermiteTieRecurrence.unit
  realizationName := `Reg.D5.S3.Analytic.Polynomial.HermiteTieRecurrence.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => HasExactlyTwo k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Polynomial.HermiteTieRecurrence
    definition := some {
      owner := `D5.S3.Analytic.Polynomial.HermiteTieRecurrence
      name := `D5.S3.Analytic.Polynomial.HermiteTieRecurrence.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Analytic.Polynomial.HermiteTieRecurrence
