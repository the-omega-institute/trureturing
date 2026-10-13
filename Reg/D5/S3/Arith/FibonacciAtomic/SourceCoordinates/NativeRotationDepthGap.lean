import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.NativeRotationDepthGap
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.NativeRotationDepthGap

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability (T U)
open _root_.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates
open _root_.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.NativeRotationDepthGap
open _root_.D5.S3.Combinatorics.Partitions.WordPartitionInverse (wd)
open _root_.D5.S3.Combinatorics.Partitions.PaddedWordPartition (G)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ t => depth t) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ n : ℕ, 3 ≤ n →
      (leftContext (n-3)).holeAddress = List.replicate (n-3) false ∧
      (leftContext (n-3)).plug (T 3) = T n ∧
      (leftContext (n-3)).plug (U 3) = U n ∧
      ContextRotation (leftContext (n-3)) (T n) (U n) ∧
      rotationGraph.Adj (T n) (U n) ∧ rotationGraph.dist (T n) (U n) = 1 ∧
      wd (T n) = wd (U n) ∧ (T n).length = Nat.fib (n+1) ∧
      (U n).length = Nat.fib (n+1) ∧ Q (T n) = (n,true) ∧ Q (U n) = (0,false) ∧
      (∀ j : ℕ, wd (substitution^[j] (T n)) = wd (substitution^[j] (U n)) ∧
        G (wd (substitution^[j] (T n))) = G (wd (substitution^[j] (U n))) ∧
        R.readout () () (substitution^[j] (T n)) = n+j ∧ R.readout () () (substitution^[j] (U n)) = j) ∧
      (∀ t : Source, wd t = wd (T n) → 0 ≤ R.readout () () t ∧ R.readout () () t ≤ n) ∧
      (∀ t : Source, G (wd t) = G (wd (T n)) → 0 ≤ R.readout () () t ∧ R.readout () () t ≤ n) ∧
      R.readout () () (T n) = n ∧ R.readout () () (U n) = 0) ∧
    (¬ ∃ A : ℝ, ∀ s t : Source, wd s = wd t → rotationGraph.Reachable s t →
      |(R.readout () () s : ℝ) - (R.readout () () t : ℝ)| ≤ A * (rotationGraph.dist s t : ℝ))

theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  rcases h.1 3 (by omega) with ⟨_, _, _, _, _, _, _, _, _, _, _, hf, _⟩
  have hd := (hf 1).2.2.1
  change (0 : ℕ) = 3+1 at hd
  omega

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), .of true, .of false, ?_⟩
  change depth (.of true) ≠ depth (.of false)
  have ha := congrArg Prod.fst all_source_coordinate_law.2.2.2.1
  have hb := congrArg Prod.fst all_source_coordinate_law.2.2.2.2
  change depth (.of true) = 0 at ha
  change depth (.of false) = 1 at hb
  rw [ha, hb]
  decide

def family : Registration arena (type_of% (@native_rotation_depth_gap)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_rotation_depth_gap, rejected, rejectedLaw⟩
  sensitivity := ⟨fun _i => ⟨rejected, fun _j h => (h (Subsingleton.elim _ _)).elim,
    rfl, rejectedLaw⟩, fun i => nomatch i⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_rotation_depth_gap)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.SourceCoordinates.NativeRotationDepthGap.native_rotation_depth_gap.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.NativeRotationDepthGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.SourceCoordinates.NativeRotationDepthGap,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["fn", "arg", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "fn", "arg", "body", "body", "arg", "fn", "arg"],
      stateBinder := 2,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
#check native_rotation_depth_gap

end Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.NativeRotationDepthGap
