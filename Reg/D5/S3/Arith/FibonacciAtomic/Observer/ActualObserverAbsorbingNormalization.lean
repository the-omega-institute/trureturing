import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
open D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
universe u
abbrev membershipSignature : Signature where
  Params := Nat
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def membershipActual : Realization membershipSignature :=
  realize membershipSignature (fun _ N U => U ∈ allowedSources N) (fun e => nomatch e)

abbrev membershipArena : Arena where
  signature := membershipSignature
  Law R := ∀ (N : Nat) (U : Source), R.readout () N U ↔ Allowed N U

abbrev sourceSetSignature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset Source
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def sourceSetActual : Realization sourceSetSignature :=
  realize sourceSetSignature (fun _ _ N => allowedSources N) (fun e => nomatch e)

abbrev sourceSetArena : Arena where
  signature := sourceSetSignature
  Law R := ∀ (N : Nat), 1 ≤ N → (R.readout () () N).Nonempty

structure FeeContext where
  Carrier : Type u
  finite : Fintype Carrier
  observer : @Observer Carrier finite
  tau : Address → ℝ

abbrev feeSignature : Signature where
  Params := FeeContext.{u}
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def feeActual : Realization feeSignature.{u} :=
  realize feeSignature (fun _ p U => @Fee p.Carrier p.finite p.observer p.tau U)
    (fun e => nomatch e)

abbrev feeArena : Arena where
  signature := feeSignature.{u}
  Law R := ∀ {E : Type u} [Fintype E] (M : Observer E) (tau : Address → ℝ) (U : Source)
    {t : RawHistory} {f : E} {b : Bool}, Run M U M.e0 t f b →
      R.readout () ⟨E, inferInstance, M, tau⟩ U = charge tau t

abbrev maximumArena : Arena where
  signature := feeSignature.{u}
  Law R := ∀ {E : Type u} [Fintype E] (N : Nat) (positive : 1 ≤ N)
    (M : Observer E) (tau : Address → ℝ),
    (∀ U, Allowed N U → R.readout () ⟨E, inferInstance, M, tau⟩ U ≤ maxFee N M tau) ∧
    ∃ U, Allowed N U ∧ maxFee N M tau = R.readout () ⟨E, inferInstance, M, tau⟩ U

theorem membership_bridge : (type_of% (@allowedSources_exact)) ↔ membershipArena.Law membershipActual := Iff.rfl
theorem sourceSet_bridge : (type_of% (@allowedSources_nonempty)) ↔ sourceSetArena.Law sourceSetActual := Iff.rfl
theorem fee_bridge : (type_of% (@fee_run.{u})) ↔ feeArena.{u}.Law feeActual.{u} := Iff.rfl
theorem maximum_bridge : (type_of% (@maximum_exact.{u})) ↔ maximumArena.{u}.Law feeActual.{u} := Iff.rfl

theorem membership_actual_law : membershipArena.Law membershipActual := allowedSources_exact
theorem sourceSet_actual_law : sourceSetArena.Law sourceSetActual := allowedSources_nonempty
theorem fee_actual_law : feeArena.{u}.Law feeActual.{u} := @fee_run.{u}
theorem maximum_actual_law : maximumArena.{u}.Law feeActual.{u} := @maximum_exact.{u}

#print axioms membership_bridge
#print axioms sourceSet_bridge
#print axioms fee_bridge
#print axioms maximum_bridge
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
