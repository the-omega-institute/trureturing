import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Asymptotics.CosineIntegralGram
import Reg.Support.DependentFamily

open MeasureTheory
open _root_.D5.S3.Fourier.Asymptotics.CosineIntegralLattice (cosineIntegral)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram

abbrev signature : Signature where
  Params := Σ _ : ℝ, ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p z => cosineIntegral (p.1 * |z|) * cosineIntegral (p.2 * |z|))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The whole original conjunction, on the whole real line and at every positive pair. -/
def arena : Arena where
  signature := signature
  Law r := ∀ a b : ℝ, 0 < a → 0 < b →
    Integrable (fun z : ℝ => r.readout () ⟨a, b⟩ z) ∧
      (∫ z : ℝ, r.readout () ⟨a, b⟩ z) = Real.pi / max a b

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := (h 1 1 zero_lt_one zero_lt_one).2
  have hp := Real.pi_pos
  norm_num [rejected, realize] at hz
  linarith

/-- A constant integrand on infinite Lebesgue volume has zero Bochner integral;
the original positive Gram mass therefore forces actual state dependence. -/
theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  by_contra h
  push Not at h
  have hc : (fun z : ℝ => cosineIntegral (1 * |z|) * cosineIntegral (1 * |z|)) =
      fun _ : ℝ => cosineIntegral (1 * |(0 : ℝ)|) * cosineIntegral (1 * |(0 : ℝ)|) := by
    funext z
    exact h ⟨1, 1⟩ z 0
  have hm := (_root_.D5.S3.Fourier.Asymptotics.CosineIntegralGram.result 1 1
    zero_lt_one zero_lt_one).2
  rw [hc] at hm
  simp [measureReal_def, Real.volume_univ] at hm
  exact Real.pi_ne_zero hm.symm

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Fourier.Asymptotics.CosineIntegralGram.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.Asymptotics.CosineIntegralGram.result) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p z => cosineIntegral (p.1 * |z|) * cosineIntegral (p.2 * |z|))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "Asymptotics") "CosineIntegralGram") "result") "Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram/Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ p z => cosineIntegral (p.1 * |z|) * cosineIntegral (p.2 * |z|))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.Asymptotics.CosineIntegralGram, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "body"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram
