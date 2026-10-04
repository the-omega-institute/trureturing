import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.GeneralInstrumentEffectClosure
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentEffectClosure
open LeanInformationAudit Matrix

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.GeneralInstrumentEffectClosure

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => d ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} {α ι ξ : Type} [Fintype α] [Fintype ι] [DecidableEq ξ]
    (hd : 1 ≤ d) (Q : α → Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ) (lab : ι → ξ)
    (hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ i, (L i)ᴴ * L i = 1),
    ∃ Nstar : ℕ, 1 ≤ Nstar ∧ Nstar ≤ R.readout () () d ∧
      (∀ N, Nstar ≤ N → effectSpace Q L lab N = effectSpace Q L lab Nstar) ∧
      ∀ X ∈ effectSpace Q L lab Nstar, noClickDual Q X ∈ effectSpace Q L lab Nstar

theorem actual_law : arena.Law actual := by
  intro d α ι ξ _ _ _ hd Q L lab hcomp
  exact effectSpace_closure hd Q L lab hcomp

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hcomp : ∑ _a : Unit, (0 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ * 0 +
      ∑ _i : Unit, (1 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ * 1 = 1 := by simp
  obtain ⟨N, hN, hN0, _⟩ := h (d := 1) (α := Unit) (ι := Unit) (ξ := Unit)
    (by decide) (fun _ => 0) (fun _ => 1) (fun _ => ()) hcomp
  change N ≤ 0 at hN0
  omega

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Quantum.Measurement.GeneralInstrumentEffectClosure.effectSpace_closure) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ d => d ^ 2) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "GeneralInstrumentEffectClosure") "effectSpace_closure") "Reg.D5.S3.Quantum.Measurement.GeneralInstrumentEffectClosure/Reg.D5.S3.Quantum.Measurement.GeneralInstrumentEffectClosure.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentEffectClosure.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ d => d ^ 2) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.GeneralInstrumentEffectClosure, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Quantum.Measurement.GeneralInstrumentEffectClosure
