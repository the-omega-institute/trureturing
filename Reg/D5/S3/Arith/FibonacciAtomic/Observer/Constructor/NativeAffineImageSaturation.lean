import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeAffineImageSaturation
import Reg.Support.DependentFamily

/-! Observe complete reconstructed canonical coordinates while retaining the
entire original affine parameter, guard, mode and joint-filter telescope. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedFreeExtension
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedImageSaturation
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeRootLinkNormalization
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeAffineImageSaturation
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeAffineImageSaturation

noncomputable section

abbrev signature : Signature where
  Params := Σ m : Nat, Fin m
  State q := Fin q.1 → CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CompletionTree
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature := realize signature
  (fun _ q v => v q.2) (fun e => nomatch e)

abbrev rejected : Realization signature := realize signature
  (fun _ _ _ => leaf true) (fun e => nomatch e)

def observed (R : Realization signature) {m : Nat} (v : Fin m → CompletionTree) :
    Fin m → CompletionTree := fun i => R.readout () ⟨m, i⟩ v

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n k m : Nat} (I : Input n k m) (p : Fin n → Nat)
    (legal : Legal I p) (mode : FreeMode I.equations (threshold I.filters)),
    (∀ j, (ranks I p j : Int) = (I.indices j).eval (environment p)) ∧
    SourceSatisfies I p (observed R (sourceCanonical I p mode)) ∧
    SourceInMode I p mode (observed R (sourceCanonical I p mode)) ∧
    ((∃ v, SourceSatisfies I p v ∧ SourceInMode I p mode v ∧ SourcePasses I p v) ↔
      SourcePasses I p (observed R (sourceCanonical I p mode)))

private theorem actual_law : arena.Law actual := by
  exact @affine_original_saturation

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let I : Input 0 0 1 := {
    equations := fun _ => some (.ground (.of false))
    filters := []
    indices := Fin.elim0
    guard := .qf .truth }
  let p : Fin 0 → Nat := Fin.elim0
  have legal : Legal I p := ⟨rfl, fun j => Fin.elim0 j⟩
  let mode : FreeMode I.equations (threshold I.filters) := fun _ => none
  have sat := (law I p legal mode).2.1
  have eq : leaf true = leaf false := sat 0 (.ground (.of false)) rfl
  have tags := congrArg (fun X => (PFunctor.M.dest X).1) eq
  cases tags

private theorem readout_depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨1, 0⟩, (fun _ => leaf true), (fun _ => leaf false), ?_⟩
  intro eq
  have tags := congrArg (fun X => (PFunctor.M.dest X).1) eq
  cases tags

def evidence : Registration arena (type_of% (@affine_original_saturation)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := readout_depends

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@affine_original_saturation) (Realization signature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeAffineImageSaturation.affine_original_saturation.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeAffineImageSaturation.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q v => v q.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun m : Nat => Fin m → CompletionTree)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeAffineImageSaturation
