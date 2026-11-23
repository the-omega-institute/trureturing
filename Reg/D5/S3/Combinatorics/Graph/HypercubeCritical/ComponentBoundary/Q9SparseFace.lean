import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseFace
import Reg.Support.SingleDependentReadout

/-! The selected face resolves each of its off-mask coordinates. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseFace

open _root_.D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum (Q)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary (directions)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents
  (componentFinset mem_componentFinset)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang (parity)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentSaturation
  (componentDefect componentDefect_det_eq componentParityFinset)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram (signed)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedSaturation (defect)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedSpectrum (maskedGraph)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseFace
  (maskedComponentFinset parityDefect exists_fixed_singular_masked_component)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Fin 9) (fun _ => Q 9) (fun _ => Bool)

open Classical in
private abbrev arena : Arena where
  signature := signature
  Law r := ∀ (U : Finset (Q 9)) (b : Bool)
    (C : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent) (I : Finset (Fin 9)),
    (∀ w : Fin 9 → ℝ, (∀ a ∉ I, w a = 0) → (componentDefect w U b C).det = 0) →
    let S := componentFinset U C
    ∃ K : ((maskedGraph I).induce (S : Set (Q 9))).ConnectedComponent,
      let T := maskedComponentFinset I S K
      (∀ w : Fin 9 → ℝ, (∀ a ∉ I, w a = 0) → (parityDefect w T b).det = 0) ∧
      (∀ x ∈ T, directions T x = directions S x ∩ I) ∧
      (∀ p : Bool, T.filter (fun x => parity x = p) = componentParityFinset U p C ∩ T) ∧
      (∀ x ∈ T, ∀ y ∈ T, ∀ a ∉ I, r.readout () a x = y a)

private def actual : Realization signature :=
  realize signature (fun _ a x => x a) Empty.elim

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) Empty.elim

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro law
  let x : Q 9 := fun _ => false
  let U : Finset (Q 9) := {x}
  let v : (U : Set (Q 9)) := ⟨x, Finset.mem_singleton_self x⟩
  let C := ((hypercube 9).induce (U : Set (Q 9))).connectedComponentMk v
  let b := parity x
  have hx : x ∈ componentParityFinset U b C :=
    Finset.mem_filter.mpr ⟨(mem_componentFinset U C x).mpr ⟨v.property, rfl⟩, rfl⟩
  have hs : signed (0 : Fin 9 → ℝ) = 0 := by
    ext i j
    simp [signed]
  have hdet (w : Fin 9 → ℝ) (hw : ∀ a ∉ (∅ : Finset (Fin 9)), w a = 0) :
      (componentDefect w U b C).det = 0 := by
    have hw0 : w = 0 := funext fun a => hw a (Finset.notMem_empty a)
    letI : Nonempty ↥(componentParityFinset U b C) := ⟨⟨x, hx⟩⟩
    rw [hw0, componentDefect_det_eq, hs]
    simp [defect, Matrix.submatrix_zero]
  obtain ⟨K, _, _, _, hoff⟩ := law U b C ∅ hdet
  obtain ⟨y, hy⟩ := K.nonempty_supp
  have hyT : y.val ∈ maskedComponentFinset ∅ (componentFinset U C) K :=
    Finset.mem_image.mpr ⟨y, Set.mem_toFinset.mpr hy, rfl⟩
  have hyU := (mem_componentFinset U C y.val).mp y.property
  have hyx : y.val = x := Finset.mem_singleton.mp hyU.choose
  have hfalse := hoff y.val hyT y.val hyT 0 (Finset.notMem_empty 0)
  change true = y.val 0 at hfalse
  rw [hyx] at hfalse
  exact Bool.noConfusion hfalse

def sourceEvidence : Registration arena (type_of% @exists_fixed_singular_masked_component) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_fixed_singular_masked_component, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    exact ⟨0, fun _ => false, fun _ => true, Bool.noConfusion⟩

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_fixed_singular_masked_component) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseFace.exists_fixed_singular_masked_component.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseFace.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a x => x a) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseFace
    definition := none
    coordinates := #[12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "body",
        "arg", "arg", "arg", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end
end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseFace
