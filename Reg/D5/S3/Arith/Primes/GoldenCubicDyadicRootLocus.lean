import D5.S3.Arith.Primes.GoldenCubicDyadicRootLocus
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Primes.GoldenCubicDyadicRootLocus
open _root_.D5.S3.Arith.Primes.GoldenCubicDyadicRootLocus
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ) (fun _ => ℕ → ℤ → ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ n => nativeResidual n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ),
    let residual := R.readout () () n
    ∀ (j : ℕ) (_hj : 1 ≤ j),
      ∃ e p q : ℤ, Even e ∧ Odd p ∧ Odd q ∧ Odd ((p-q)/2) ∧
        ∀ t : ℤ, residual j t = 0 ↔
          (2 : ℤ)^(n+3) ∣ (t-e) ∨
          (2 : ℤ)^(n+2) ∣ (t-p) ∨ (2 : ℤ)^(n+2) ∣ (t-q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨e,p,q,_,_,_,_,hz⟩ := h 0 1 (by decide)
  have he := (hz e).mpr (Or.inl (by simp))
  change (1 : ℤ) = 0 at he
  omega

private theorem actual_dependence : actual.readout () () 0 ≠ actual.readout () () 1 := by
  intro h
  have h0 := congrFun (congrFun h 1) 0
  change nativeResidual 0 1 0 = nativeResidual 1 1 0 at h0
  exact (by decide +kernel : nativeResidual 0 1 0 ≠ nativeResidual 1 1 0) h0

def family : Registration arena (type_of% @native_cubic_dyadic_locus) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_cubic_dyadic_locus,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨(), 0, 1, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@native_cubic_dyadic_locus) (type_of% actual) Unit Unit where
  unitName := `D5.S3.Arith.Primes.GoldenCubicDyadicRootLocus.native_cubic_dyadic_locus.__information_unit
  realizationName := `Reg.D5.S3.Arith.Primes.GoldenCubicDyadicRootLocus.family
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
      owner := `D5.S3.Arith.Primes.GoldenCubicDyadicRootLocus
      definition := none
      coordinates := #[]
      readouts := #[{
        path := #["body","value"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Reg.D5.S3.Arith.Primes.GoldenCubicDyadicRootLocus
