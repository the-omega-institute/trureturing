import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.GaussianIsometry
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u t s r o a

namespace Reg.D5.S3.Fourier.GaussianIsometry
open _root_.D5.S3.Fourier.GaussianIsometry

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ≥0
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output := fun _ _ => Measure ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def emptyAnchor : Empty → Unit → ℝ≥0 := fun e => nomatch e

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => gaussianReal 0 x) emptyAnchor

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => gaussianReal 1 0) emptyAnchor

def theoremLaw (R : Realization signature.{u}) : Prop := ∀ (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H],
    ∃ (ι : Type u)
      (W : H →ₗᵢ[ℝ] Lp ℝ 2 (Measure.infinitePi (fun _ : ι => gaussianReal 0 1))),
      (∀ h : H, HasLaw (fun ω => W h ω) (R.readout ⟨()⟩ () (‖h‖ ^ 2).toNNReal)
        (Measure.infinitePi (fun _ : ι => gaussianReal 0 1))) ∧
      IsGaussianProcess (fun h ω => W h ω)
        (Measure.infinitePi (fun _ : ι => gaussianReal 0 1)) ∧
      ∀ h k, cov[fun ω => W h ω, fun ω => W k ω;
        Measure.infinitePi (fun _ : ι => gaussianReal 0 1)] = ⟪h, k⟫

def arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  intro H _ _ _
  exact exists_gaussian_isometry H

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨ι, W, hw, _⟩ := h (lp (fun _ : ULift.{u} Unit => ℝ) 2)
  have hz := hw 0
  have he : (fun ω => W 0 ω) =ᵐ[Measure.infinitePi (fun _ : ι => gaussianReal 0 1)]
      (fun _ => (0 : ℝ)) := by
    rw [map_zero]
    exact Lp.coeFn_zero _ _ _
  have hz' := hz.congr he.symm
  have hi := hz'.integral_eq
  norm_num [rejected, realize, integral_id_gaussianReal] at hi

theorem dependence_proof : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hv := congrArg (fun μ : Measure ℝ => variance (fun x : ℝ => x) μ) h
  norm_num [actual, realize, variance_id_gaussianReal] at hv

private theorem sensitivity_of_rejected
    (A : Arena.{t, s, r, o, a}) (x y : Realization A.signature)
    (hrole : ∀ i j : A.signature.Role, j = i)
    (hanchor : x.anchor = y.anchor)
    (hempty : ∀ _ : A.signature.Anchor, False)
    (hbad : ¬ A.Law y) : Sensitivity A x := by
  constructor
  · intro i
    exact ⟨y, fun j h => (h (hrole i j)).elim, hanchor, hbad⟩
  · intro i
    exact (hempty i).elim

private theorem roles_equal (i j : signature.{u}.Role) : j = i :=
  @Subsingleton.elim (ULift.{u} Unit) _ j i

private theorem anchors_equal : actual.{u}.anchor = rejected.anchor := rfl

private theorem anchors_empty (i : signature.{u}.Anchor) : False := nomatch i

theorem sensitivity_proof : Sensitivity arena.{u} actual :=
  sensitivity_of_rejected arena actual rejected roles_equal
    anchors_equal anchors_empty.{u} rejected_law

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.GaussianIsometry.exists_gaussian_isometry.{u}) (type_of% (realize.{0, 0, u, 0, 0} signature.{u} (fun _ _ x => gaussianReal 0 x) emptyAnchor)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "GaussianIsometry") "exists_gaussian_isometry") "Reg.D5.S3.Fourier.GaussianIsometry/Reg.D5.S3.Fourier.GaussianIsometry.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.GaussianIsometry.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u})⟩,
  objectArena := .source ⟨(arena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u}) ⟨(registration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, u, 0, 0} signature.{u} (fun _ _ x => gaussianReal 0 x) emptyAnchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.GaussianIsometry, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "fn", "arg", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.Fourier.GaussianIsometry
