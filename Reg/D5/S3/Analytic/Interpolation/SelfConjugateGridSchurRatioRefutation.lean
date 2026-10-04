import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.SelfConjugateGridSchurRatioRefutation
import Reg.Support.CounterexampleRecord

namespace Reg.D5.S3.Analytic.Interpolation.SelfConjugateGridSchurRatioRefutation

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
open _root_.D5.S3.Analytic.Interpolation.SelfConjugateGridSchurRatioRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private def predicate (k : ℕ) : Prop :=
  ∀ n t : ℕ, k < n → n ≤ t → ∀ z : Fin n → ℂ,
    selfConjugate z → (∀ i, ‖z i‖ ≤ 1) →
      ‖Q t n k (z + 1)‖ ≤ 1 ∧
        ((∀ i, 0 ≤ (z i).re) →
          ‖schurHook (t - n) (n - k - 1) z‖ ≤ (t.choose n : ℝ) * ‖e (n - k) z‖)

private theorem failure_exists : ∃ k, ¬ predicate k := by
  classical
  exact not_forall.mp result

private def embed : Fin 1 → ℕ := fun _ => Classical.choose failure_exists

private def decision : ∀ w : Fin 1, Decidable (predicate (embed w)) :=
  fun _ => .isFalse (Classical.choose_spec failure_exists)

private def arena := WitnessArena.ofCarrier (Fin 1) ℕ predicate embed decision
private def reads := counterexampleRealization (fun _ : Fin 1 => false)

private theorem law : arena.Law reads := ⟨(0 : Fin 1), rfl⟩
private theorem bridge : WitnessPrimitiveRealization arena (¬ claim) reads :=
  ⟨arena.law_refutes⟩
private theorem variation : arena.Law reads ∧ ¬ arena.Law arena.constantTrue :=
  arena.variation law
private theorem sensitivity : FiniteSlotSensitivity arena.toPrimitiveLawArena :=
  arena.sensitivity law

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Analytic.Interpolation.SelfConjugateGridSchurRatioRefutation.result) (type_of% (arena)) (type_of% (arena)) (type_of% (@counterexampleRealization (Fin 1) (fun _ : Fin 1 => false))) (type_of% (variation)) (type_of% (sensitivity)) (type_of% (Nat)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "Analytic") "Interpolation") "SelfConjugateGridSchurRatioRefutation") 0) "D5") "S3") "Analytic") "Interpolation") "SelfConjugateGridSchurRatioRefutation") "result") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "Analytic") "Interpolation") "SelfConjugateGridSchurRatioRefutation") 0) "Reg") "D5") "S3") "Analytic") "Interpolation") "SelfConjugateGridSchurRatioRefutation") "bridge"),
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .witness (arena) (Reg.D5.S3.Analytic.Interpolation.SelfConjugateGridSchurRatioRefutation.reads) (reads.toPrimitiveBundle) ⟨(bridge)⟩ (And.left (variation)),
  readout := some (@counterexampleRealization (Fin 1) (fun _ : Fin 1 => false)),
  variation := some ⟨(variation)⟩,
  sensitivity := some ⟨(sensitivity)⟩,
  escapeFrom := some (Nat),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end

end Reg.D5.S3.Analytic.Interpolation.SelfConjugateGridSchurRatioRefutation
