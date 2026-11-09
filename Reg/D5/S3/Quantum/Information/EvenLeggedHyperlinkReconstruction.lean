import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction
import Reg.Support.UniverseSingleReadout

/-! Source-bound registrations of the selected public mathematical statements. -/

namespace Reg.D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction
open _root_.D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the rational coefficient family in the reconstruction formula. -/
abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Unit
    (fun _ => ℕ → ℕ → ℚ) (fun _ => ℕ → ℕ → ℚ)

def actual : Realization signature :=
  realize signature (fun _ _ L => L) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ _ => 0) (fun e => nomatch e)

/-- The zero and symmetry laws retain their witness; reconstruction observes that witness. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∃ L : ℕ → ℕ → ℚ,
    (∀ m, L m 0 = 0 ∧ L m m = 0) ∧
    (∀ m p, L m p = L m (m - p)) ∧
    ∀ (N : ℕ) (S : Finset (Fin N) → ℝ),
      S ∅ = 0 → (∀ A, S Aᶜ = S A) → ∀ A,
        S A =
          ∑ I ∈ (Finset.univ : Finset (Fin N)).powerset.filter
              (fun I => Even I.card ∧ I ≠ ∅),
            (R.readout () () L I.card (I ∩ A).card : ℝ) * hyperlink S I

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨L, _, _, hrec⟩ := h
  let S : Finset (Fin 2) → ℝ := fun A => if A.card = 1 then 1 else 0
  have hzero : S ∅ = 0 := by simp [S]
  have hcompl : ∀ A, S Aᶜ = S A := by
    intro A
    have hcard : A.card ≤ 2 := by simpa using Finset.card_le_univ A
    have he : Aᶜ.card = 1 ↔ A.card = 1 := by
      rw [Finset.card_compl]
      simp only [Fintype.card_fin]
      omega
    simp only [S, he]
  have hbad := hrec 2 S hzero hcompl {0}
  change S {0} =
    ∑ I ∈ (Finset.univ : Finset (Fin 2)).powerset.filter
      (fun I => Even I.card ∧ I ≠ ∅), ((0 : ℚ) : ℝ) * hyperlink S I at hbad
  simp only [Rat.cast_zero, zero_mul, Finset.sum_const_zero] at hbad
  have hone : S {0} = 1 := by simp only [S, Finset.card_singleton, ite_true]
  exact one_ne_zero (hone.symm.trans hbad)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  intro h
  have he := congrArg (fun L : ℕ → ℕ → ℚ => L 2 1) h
  exact zero_ne_one he

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction.result)
      (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction "unit",
  realizationName :=
    `Reg.D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction.source_registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨source_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ L => L) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction,
    definition := some {
      owner := `D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction,
      name := `D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction.claim,
      path := #[] },
    coordinates := #[],
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "fn", "arg", "arg", "fn", "fn"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms signature
#print axioms actual
#print axioms rejected
#print axioms arena
#print axioms rejected_law
#print axioms dependence
#print axioms source_registration
#print axioms registration

end
namespace Zeta
universe u
abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type u} (S : Finset α → ℝ) (A : Finset α),
    R.readout () () (∑ I ∈ A.powerset, hyperlink S I) (S A)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (α := ULift.{u} Unit) (fun _ => 0) ∅

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (0 : ℝ) = 1 := (congrFun h 1).mpr rfl
  exact zero_ne_one hh

def family : Registration arena.{u} (type_of% (@zeta_hyperlink.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@zeta_hyperlink, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@zeta_hyperlink.{u})
    (type_of% (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction.zeta_hyperlink "__information_unit"
  realizationName := `Reg.D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction.Zeta.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms registration
end Zeta


namespace HyperlinkZeta
noncomputable section
universe u_1

/-- Observe the hyperlink of the subset zeta transform at a varying subset. -/
abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature (Σ α : Type u_1, Finset α → ℝ)
    (fun p => Finset p.1) (fun _ => ℝ)

def actual : Realization signature.{u_1} :=
  realize signature (fun _ p I => hyperlink (fun A => ∑ K ∈ A.powerset, Sigma.snd p K) I)
    (fun e => nomatch e)

def rejected : Realization signature.{u_1} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u_1}
  Law R := ∀ {α : Type u_1} (v : Finset α → ℝ) (I : Finset α),
    R.readout () ⟨α, v⟩ I = v I

private theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro h
  have he := h (α := ULift.{u_1} Unit) (fun _ => 1) ∅
  exact zero_ne_one he

private theorem dependence : ObservationalDependence signature.{u_1} actual := by
  intro i
  refine ⟨⟨ULift.{u_1} Unit, fun I => (I.card : ℝ)⟩, ∅, {ULift.up ()}, ?_⟩
  let v : Finset (ULift.{u_1} Unit) → ℝ := fun I => (I.card : ℝ)
  change hyperlink (fun A => ∑ K ∈ A.powerset, v K) ∅ ≠
    hyperlink (fun A => ∑ K ∈ A.powerset, v K) {ULift.up ()}
  rw [hyperlink_zeta, hyperlink_zeta]
  simpa only [v, Finset.card_empty, Finset.card_singleton, Nat.cast_zero, Nat.cast_one]
    using (zero_ne_one : (0 : ℝ) ≠ 1)

def source_registration : Registration arena.{u_1} (type_of% (@hyperlink_zeta.{u_1})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hyperlink_zeta.{u_1}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@hyperlink_zeta.{u_1}) (Realization signature.{u_1}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction.HyperlinkZeta.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction.HyperlinkZeta
    "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_1}⟩
  objectArena := .source ⟨arena.{u_1}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_1} ⟨source_registration.{u_1}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature.{u_1} (actual.{u_1}).readout (actual.{u_1}).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end HyperlinkZeta

end Reg.D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction
