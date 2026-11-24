import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedSwapNormalForm
import Reg.Support.SingleDependentReadout

/-! The swapped vertex gives the invariance test needed for the paired mask. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedSwapNormalForm

noncomputable section

open _root_.D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum (Q IsBalanced)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PairBoundaryKernel
  (cubeMask pairVertex)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedSwapNormalForm
  (complementLeadingPair exists_cubeMask_of_leadingSwap leadingSwap)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Q 9) (fun _ => Q 9)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {C : Finset (Q 9)}, IsBalanced C →
    (∀ x ∈ C, R.readout () () x ∈ C) →
    ((hypercube 9).induce (C : Set (Q 9))).Preconnected →
    ∃ (b : Bool) (M S : Set (Q 7)),
      (∀ t : Q 7, pairVertex (!b, !b, t) ∉ C) ∧
      (C.image (complementLeadingPair b) : Set (Q 9)) = cubeMask M S ∧
      IsBalanced (C.image (complementLeadingPair b))

private def actual : Realization signature :=
  realize signature (fun _ _ z => leadingSwap z) Empty.elim

private def rejected : Realization signature :=
  realize signature (fun _ _ z => z) Empty.elim

private def tail : Q 7 := fun _ => false
private def x : Q 9 := pairVertex (true, false, tail)
private def y : Q 9 := pairVertex (false, true, tail)

private theorem x_ne_y : x ≠ y := by
  intro h
  have hbit : true = false := congrFun h 0
  exact Bool.noConfusion hbit

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro law
  let C : Finset (Q 9) := {x}
  have only_x {z : Q 9} (hz : z ∈ C) : z = x := Finset.mem_singleton.mp hz
  have hC : IsBalanced C := by
    refine ⟨fun _ => 1, fun _ _ => Or.inl rfl, ?_⟩
    intro u hu v hv hadj
    rw [only_x hu, only_x hv] at hadj
    exact (SimpleGraph.irrefl _ hadj).elim
  have hconn : ((hypercube 9).induce (C : Set (Q 9))).Preconnected := by
    intro u v
    have huv : u = v := Subtype.ext ((only_x u.property).trans (only_x v.property).symm)
    subst v
    exact ⟨.nil⟩
  obtain ⟨b, M, S, _, hmask, _⟩ := law hC (fun _ hz => hz) hconn
  have hxy : x ∈ cubeMask M S ↔ y ∈ cubeMask M S := by
    unfold x y cubeMask
    simp only [Set.mem_preimage, Equiv.symm_apply_apply]
    rfl
  have hgx : complementLeadingPair b x ∈ C.image (complementLeadingPair b) :=
    Finset.mem_image.mpr ⟨x, Finset.mem_singleton_self _, rfl⟩
  have hgy : complementLeadingPair b y ∈ C.image (complementLeadingPair b) := by
    change complementLeadingPair b y ∈ (C.image (complementLeadingPair b) : Set (Q 9))
    change complementLeadingPair b x ∈ (C.image (complementLeadingPair b) : Set (Q 9)) at hgx
    rw [hmask] at hgx ⊢
    cases b
    · exact hxy.mp hgx
    · have hxx : complementLeadingPair true x = y := by
        funext i
        fin_cases i <;> rfl
      have hyy : complementLeadingPair true y = x := by
        funext i
        fin_cases i <;> rfl
      rw [hxx] at hgx
      rw [hyy]
      exact hxy.mpr hgx
  obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hgy
  exact x_ne_y ((only_x hz).symm.trans ((complementLeadingPair b).injective hzy))

def sourceEvidence : Registration arena (type_of% @exists_cubeMask_of_leadingSwap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_cubeMask_of_leadingSwap, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    exact ⟨(), x, y, fun h => x_ne_y (leadingSwap.injective h)⟩

set_option linter.style.longLine false in
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_cubeMask_of_leadingSwap) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedSwapNormalForm.exists_cubeMask_of_leadingSwap.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedSwapNormalForm.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => leadingSwap z) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedSwapNormalForm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "domain", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedSwapNormalForm
