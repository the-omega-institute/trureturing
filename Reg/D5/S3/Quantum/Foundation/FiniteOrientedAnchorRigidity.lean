import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Foundation.FiniteOrientedAnchorRigidity
import Reg.Support.DependentFamily

/-! The norm observations retain the original Hilbert carriers and their norms.
The full source law includes all mass, orientation and anchor hypotheses. -/

noncomputable section

universe u v w

open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteOrientedAnchorRigidity

namespace Reg.D5.S3.Quantum.Foundation.FiniteOrientedAnchorRigidity

abbrev signature : Signature where
  Params := (Σ A : Type u, NormedAddCommGroup A) ⊕
    (Σ B : Type w, NormedAddCommGroup B)
  State p := match p with
    | .inl q => ULift.{w} q.1
    | .inr q => ULift.{u} q.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, w} :=
  realize signature (fun _ p x => by
    cases p with
    | inl q => letI := q.2; exact ‖x.down‖ ^ 2
    | inr q => letI := q.2; exact ‖x.down‖ ^ 2) (fun e => nomatch e)

def rejected : Realization signature.{u, w} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, w}
  Law R := ∀ {d : ℕ} (hd : 1 ≤ d)
    {H : Type u} [nH : NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H]
    {E : Type v} [Fintype E]
    {W : E → Type w} [nW : ∀ e, NormedAddCommGroup (W e)]
    [∀ e, InnerProductSpace ℂ (W e)] [∀ e, FiniteDimensional ℂ (W e)]
    (a : OrthonormalBasis (Fin d) ℂ H) (F : H → PiLp 2 W)
    (hmass : ∀ x, ∑ e, R.readout () (.inr ⟨W e, nW e⟩) ⟨F x e⟩ =
      R.readout () (.inl ⟨H, nH⟩) ⟨x⟩)
    (hphase : ∀ (j : Fin d) (k : Fin 4) (e : E),
      F ((Complex.I ^ k.val) • a j) e = (Complex.I ^ k.val) • F (a j) e)
    (hanchor : ∀ (x : H) (j : Fin d) (k : Fin 4),
      (∑ e, R.readout () (.inr ⟨W e, nW e⟩)
        ⟨F x e - F ((Complex.I ^ k.val) • a j) e⟩) ≤
          R.readout () (.inl ⟨H, nH⟩) ⟨x - (Complex.I ^ k.val) • a j⟩),
    ∃! V : H →ₗᵢ[ℂ] PiLp 2 W,
      (∀ x, F x = V x) ∧ V.adjoint ∘ₗ V.toLinearMap = LinearMap.id

private theorem rejected_law : ¬ arena.{u, v, w}.Law rejected := by
  classical
  intro h
  let H := EuclideanSpace ℂ (ULift.{u} (Fin 1))
  let E := ULift.{v} Unit
  let W : E → Type w := fun _ => EuclideanSpace ℂ (ULift.{w} (Fin 1))
  let a : OrthonormalBasis (Fin 1) ℂ H :=
    (EuclideanSpace.basisFun (ULift.{u} (Fin 1)) ℂ).reindex Equiv.ulift
  obtain ⟨V, hV, _⟩ := @h 1 (by norm_num) H inferInstance inferInstance inferInstance
    E inferInstance W inferInstance inferInstance inferInstance a (fun _ => 0)
    (by intro x; change (∑ _ : E, (0 : ℝ)) = 0; simp)
    (by intro j k e; simp)
    (by intro x j k; change (∑ _ : E, (0 : ℝ)) ≤ 0; simp)
  have hz : V (a 0) = 0 := (hV.1 (a 0)).symm
  have hn := V.norm_map (a 0)
  rw [hz, norm_zero, a.orthonormal.norm_eq_one] at hn
  norm_num at hn

private theorem dependence : ObservationalDependence signature.{u, w} actual := by
  intro i
  let H := EuclideanSpace ℂ (ULift.{u} (Fin 1))
  let a : OrthonormalBasis (Fin 1) ℂ H :=
    (EuclideanSpace.basisFun (ULift.{u} (Fin 1)) ℂ).reindex Equiv.ulift
  have hmass (x : H) : ∑ e, ‖x e‖ ^ 2 = ‖x‖ ^ 2 :=
    (PiLp.norm_sq_eq_of_L2 _ x).symm
  have hphase (j : Fin 1) (k : Fin 4) (e : ULift.{u} (Fin 1)) :
      ((Complex.I ^ k.val) • a j) e = (Complex.I ^ k.val) • a j e := rfl
  have hanchor (x : H) (j : Fin 1) (k : Fin 4) :
      (∑ e, ‖x e - ((Complex.I ^ k.val) • a j) e‖ ^ 2) ≤
        ‖x - (Complex.I ^ k.val) • a j‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    rfl
  obtain ⟨V, _, _⟩ := finite_oriented_anchor_rigidity (by norm_num : 1 ≤ 1)
    a (fun x : H => x) hmass hphase hanchor
  refine ⟨.inl ⟨H, inferInstance⟩, ⟨0⟩, ⟨V (a 0)⟩, ?_⟩
  change ‖(0 : H)‖ ^ 2 ≠ ‖V (a 0)‖ ^ 2
  rw [V.norm_map, a.orthonormal.norm_eq_one]
  norm_num

def source_registration :
    Registration arena.{u, v, w} (type_of% @finite_oriented_anchor_rigidity.{u, v, w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_oriented_anchor_rigidity.{u, v, w}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@finite_oriented_anchor_rigidity.{u, v, w}) (Realization signature.{u, w}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Foundation.FiniteOrientedAnchorRigidity.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Foundation.FiniteOrientedAnchorRigidity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => by
    cases p with
    | inl q => letI := q.2; exact ‖x.down‖ ^ 2
    | inr q => letI := q.2; exact ‖x.down‖ ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.FiniteOrientedAnchorRigidity
    definition := none
    coordinates := #[2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "domain", "body", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Foundation.FiniteOrientedAnchorRigidity
