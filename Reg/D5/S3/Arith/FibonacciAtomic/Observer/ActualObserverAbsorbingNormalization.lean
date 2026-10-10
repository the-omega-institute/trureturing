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

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.Exports
universe u
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source composition)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev compositionSignature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat × Nat
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev compositionActual : Realization compositionSignature :=
  realize compositionSignature (fun _ _ U => composition U) (fun e => nomatch e)

abbrev compositionArena : Arena where
  signature := compositionSignature
  Law R := ∀ T : Source, (R.readout () () T).1 + (R.readout () () T).2 = T.length

theorem compositionBridge : (type_of% (@composition_total)) ↔ compositionArena.Law compositionActual := Iff.rfl
theorem compositionLaw : compositionArena.Law compositionActual := @composition_total

structure StepContext where
  Carrier : Type u
  finite : Fintype Carrier
  observer : @Observer Carrier finite
  source : Source

abbrev stepSignature : Signature where
  Params := StepContext.{u}
  State p := p.Carrier
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.Carrier
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev stepActual : Realization stepSignature.{u} :=
  realize stepSignature (fun _ p e => @sourceStep p.Carrier p.finite p.observer p.source e)
    (fun e => nomatch e)

abbrev orbitArena : Arena where
  signature := stepSignature.{u}
  Law R := ∀ {E : Type u} [Fintype E] (M : Observer E) (U : Source)
    {e f : E} {t : RawHistory} {b : Bool}, Run M U e t f b →
      (R.readout () ⟨E, inferInstance, M, U⟩)^[t.length] e = f ∧
      M.action f = .inr b ∧
      ∀ i < t.length, ∃ q, M.action
        ((R.readout () ⟨E, inferInstance, M, U⟩)^[i] e) = .inl q

theorem orbitBridge : (type_of% (@run_orbit.{u})) ↔ orbitArena.{u}.Law stepActual.{u} := Iff.rfl
theorem orbitLaw : orbitArena.{u}.Law stepActual.{u} := @run_orbit.{u}

structure ObserverContext where
  Carrier : Type u
  finite : Fintype Carrier

abbrev observerSignature : Signature where
  Params := ObserverContext.{u}
  State p := @Observer p.Carrier p.finite
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := @Observer p.Carrier p.finite
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev observerActual : Realization observerSignature.{u} :=
  realize observerSignature (fun _ _ M => M) (fun e => nomatch e)

abbrev lengthArena : Arena where
  signature := observerSignature.{u}
  Law R := ∀ {E : Type u} [Fintype E] (M : Observer E) (U : Source)
    {e f : E} {t : RawHistory} {b : Bool},
    Run (R.readout () ⟨E, inferInstance⟩ M) U e t f b → t.length < Fintype.card E

theorem lengthBridge : (type_of% (@run_length_bound.{u})) ↔ lengthArena.{u}.Law observerActual.{u} := Iff.rfl
theorem lengthLaw : lengthArena.{u}.Law observerActual.{u} := @run_length_bound.{u}


end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.Exports
