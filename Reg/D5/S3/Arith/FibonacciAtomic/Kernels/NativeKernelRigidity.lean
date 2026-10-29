import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Kernels.NativeKernelRigidity
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Kernels.NativeKernelRigidity

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.Kernels.NativeKernelRigidity (kernel_zero_or_one)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := (Source → Source → ℂ) × Source
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p t => p.1 p.2 t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K : Source → Source → ℂ),
    (∀ s t, K t s = star (K s t)) →
    (∀ s t, K (substitution s) (substitution t) = K s t) →
    (∀ s t u v, K (FreeMagma.mul s t) (FreeMagma.mul u v) = K s u * K t v) →
    ∀ s t, R.readout () (K, s) t = 0 ∨ K s t = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (fun _ _ => 0) (by intros; simp) (by intros; rfl)
    (by intros; simp) (.of true) (.of true)
  norm_num [rejected, realize] at he

def family : Registration arena (type_of% (@kernel_zero_or_one)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨kernel_zero_or_one, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro _
    let K : Source → Source → ℂ := fun _ t => if t = .of true then 0 else 1
    refine ⟨(K, .of true), .of true, .of false, ?_⟩
    change K (.of true) (.of true) ≠ K (.of true) (.of false)
    simp [K]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kernel_zero_or_one)
    (type_of% (realize signature (fun _ p t => p.1 p.2 t) (fun e => nomatch e)))
    Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Kernels.NativeKernelRigidity.kernel_zero_or_one.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Kernels.NativeKernelRigidity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p t => p.1 p.2 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Kernels.NativeKernelRigidity
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Kernels.NativeKernelRigidity
