import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.TorusGeneratorRigidity
import Reg.Support.DependentFamily

open Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Fourier.TorusGeneratorRigidity
universe u v

/-- All parameter and coordinate types, including empty and infinite types, are retained. -/
abbrev Params := Σ P : Type u, Σ I : Type v, P → I → Circle

abbrev signature : Signature where
  Params := Params.{u, v}
  State := fun p => p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Set (p.2.1 → Circle)
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The readout is the actual closure of the nonnegative-power orbit at the selected parameter. -/
def actual : Realization signature.{u, v} :=
  realize signature (fun _ p t => closure (range (fun n : ℕ => p.2.2 t ^ n)))
    (fun e => nomatch e)

/-- Replacing every orbit closure by the whole product discards the common-orbit constraint. -/
def rejected : Realization signature.{u, v} :=
  realize signature (fun _ _ _ => univ) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u, v}
  Law r := ∀ {P : Type u} {I : Type v} [TopologicalSpace P] {S : Set P},
    IsPreconnected S → ∀ (g : P → I → Circle), ContinuousOn g S →
    ∀ G : Set (I → Circle),
    (∀ p ∈ S, r.readout () ⟨P, I, g⟩ p = G) →
    ∀ p ∈ S, ∀ q ∈ S, g p = g q

/-- A continuous nonconstant family falsifies the law with the altered readout. -/
theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let g : ULift.{u} ℝ → ULift.{v} Unit → Circle := fun t _ => Circle.exp t.down
  have hg : Continuous g := continuous_pi fun _ =>
    Circle.exp.continuous.comp continuous_uliftDown
  have hconn := isPreconnected_univ.image (ULift.up : ℝ → ULift.{u} ℝ)
    continuous_uliftUp.continuousOn
  rw [image_univ, Set.range_eq_univ.mpr (fun x => ⟨x.down, rfl⟩)] at hconn
  have heq := h hconn g hg.continuousOn univ (fun _ _ => rfl)
    ⟨Real.pi⟩ (mem_univ _) ⟨0⟩ (mem_univ _)
  have hbad := congrFun heq (ULift.up ())
  exact Circle.exp_pi_ne_one (by simpa [g] using hbad)

theorem dependence : ObservationalDependence signature.{u, v} actual := by
  intro i
  let g : ULift.{u} ℝ → ULift.{v} Unit → Circle := fun t _ => Circle.exp t.down
  refine ⟨⟨ULift.{u} ℝ, ULift.{v} Unit, g⟩, ⟨Real.pi⟩, ⟨0⟩, ?_⟩
  intro h
  change closure (range (fun n : ℕ => g ⟨Real.pi⟩ ^ n)) =
    closure (range (fun n : ℕ => g ⟨0⟩ ^ n)) at h
  have hzero : g ⟨0⟩ = 1 := by funext j; exact Circle.exp_zero
  have hone : closure (range (fun n : ℕ => g ⟨0⟩ ^ n)) = {1} := by
    simp only [hzero, one_pow, range_const, closure_singleton]
  have hmem : g ⟨Real.pi⟩ ∈ closure (range (fun n : ℕ => g ⟨Real.pi⟩ ^ n)) :=
    subset_closure ⟨1, pow_one _⟩
  rw [h, hone, mem_singleton_iff] at hmem
  exact Circle.exp_pi_ne_one (congrFun hmem (ULift.up ()))

def registration : Registration arena.{u, v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Fourier.TorusGeneratorRigidity.result.{u, v},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.TorusGeneratorRigidity.result.{u_1, u_2}) (type_of% (realize.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0} signature.{u_1, u_2}
    (fun _ p t => closure.{u_2} (range.{u_2, 1} (fun n : ℕ => p.2.2 t ^ n))) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "TorusGeneratorRigidity") "result") "Reg.D5.S3.Fourier.TorusGeneratorRigidity/Reg.D5.S3.Fourier.TorusGeneratorRigidity.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.TorusGeneratorRigidity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0} signature.{u_1, u_2}
    (fun _ p t => closure.{u_2} (range.{u_2, 1} (fun n : ℕ => p.2.2 t ^ n))) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.TorusGeneratorRigidity, definition := none, coordinates := #[0, 1, 5], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "domain", "body", "body", "fn", "arg"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.Fourier.TorusGeneratorRigidity
