import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Topology.FiniteMatchingAssociativity
import D5.S3.Topology.FiniteMatchingClosure
import D5.S3.Topology.FiniteMatchingComposition
import D5.S3.Topology.FiniteMatchingSewing
import D5.S3.Topology.CupCapComposition
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Topology.FiniteMatchingAssociativity
open _root_.D5.S3.Topology.FiniteMatchingAssociativity
open _root_.D5.S3.Topology.FiniteMatchingClosure
open _root_.D5.S3.Topology.FiniteMatchingComposition
open _root_.D5.S3.Topology.FiniteMatchingSewing
open _root_.D5.S3.Topology.CupCapComposition
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev signature : Signature where
  Params := ℕ
  State n := Matching (Boundary n) × Matching (Boundary n) × Matching (Boundary n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def lhs (n : ℕ) (s : signature.State n) : Prop :=
  0 < internalLoopCount s.1 s.2.1 ∨ 0 < internalLoopCount (composite s.1 s.2.1) s.2.2

def rhs (n : ℕ) (s : signature.State n) : Prop :=
  0 < internalLoopCount s.2.1 s.2.2 ∨ 0 < internalLoopCount s.1 (composite s.2.1 s.2.2)

def actual : Realization signature := realize signature (fun _ n s => decide (lhs n s)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ n s => !(decide (rhs n s))) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ n s, r.readout () n s = decide (rhs n s)

private theorem actual_law : arena.Law actual := by
  intro n ⟨d,e,f⟩
  change decide (lhs n (d,e,f)) = decide (rhs n (d,e,f))
  exact congrArg (fun p : Prop => decide p) (propext (internalLoopCount_pos_assoc d e f))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 (identityMatching 0,identityMatching 0,identityMatching 0)
  change (!(decide (rhs 0 (identityMatching 0,identityMatching 0,identityMatching 0)))) = decide (rhs 0 (identityMatching 0,identityMatching 0,identityMatching 0)) at hh
  cases hv : decide (rhs 0 (identityMatching 0,identityMatching 0,identityMatching 0)) <;> simp_all

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let d : Matching (Boundary 2) := cupcapMatching 0 (by omega)
  have hp : d.mate (false,⟨0,by omega⟩) = (false,⟨1,by omega⟩) := by rfl
  have hpos := internalLoopCount_cupcap_pos 0 (by omega) d hp
  refine ⟨2, (identityMatching 2,identityMatching 2,identityMatching 2),
    (d,d,identityMatching 2), ?_⟩
  have hzero : ¬ lhs 2 (identityMatching 2,identityMatching 2,identityMatching 2) := by
    simp [lhs, internalLoopCount_left_identity, composite_left_identity]
  have hnonzero : lhs 2 (d,d,identityMatching 2) := Or.inl hpos
  change decide (lhs 2 _) ≠ decide (lhs 2 _)
  simp only [hzero, hnonzero, decide_false, decide_true]
  decide

def source_registration : Registration arena
    (∀ (n : ℕ) (d e f : Matching (Boundary n)),
      (0 < internalLoopCount d e ∨ 0 < internalLoopCount (composite d e) f) ↔
      (0 < internalLoopCount e f ∨ 0 < internalLoopCount d (composite e f))) where
  actual := actual
  bridge := by
    constructor
    · intro h n ⟨d,e,f⟩
      exact congrArg (fun p : Prop => decide p) (propext (h n d e f))
    · intro h n d e f
      have hh := h n (d,e,f)
      simpa only [actual, realize, lhs, rhs, decide_eq_decide] using hh
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Topology.FiniteMatchingAssociativity.internalLoopCount_pos_assoc)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Topology.FiniteMatchingAssociativity.unit
  realizationName := `Reg.D5.S3.Topology.FiniteMatchingAssociativity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n s => decide (lhs n s)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Topology.FiniteMatchingAssociativity
