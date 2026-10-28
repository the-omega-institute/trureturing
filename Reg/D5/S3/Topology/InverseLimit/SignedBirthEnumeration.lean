import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedBirthEnumeration

/-! Exact source telescopes for signed and clopen birth construction.
A source telescope is not a validated four-slot registration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Topology.InverseLimit.SignedProperLimit
open _root_.D5.S3.Topology.InverseLimit.SignedBirthEnumeration
open Set Function MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal

namespace Reg.D5.S3.Topology.InverseLimit.SignedBirthEnumeration

universe u

abbrev encodingScope := type_of% (@signed_sequences_card_le_continuum.{u})
abbrev signedScope := type_of% (@exists_signed_enumeration)
abbrev supportScope := type_of% (@exists_supportFamily.{u})
abbrev clopenScope := type_of% (@exists_clopen_enumerations)

structure SignedInputs where
  X : Type 1
  topology : TopologicalSpace X
  metrizable : @PseudoMetrizableSpace X topology
  compact : @CompactSpace X topology
  measurable : MeasurableSpace X
  borel : @BorelSpace X topology measurable
  secondCountable : @SecondCountableTopology X topology
  V : @SupportFamily X topology
  CH : Cardinal.continuum.{0} = ℵ₁

def signedConclusion (P : SignedInputs) : Prop :=
  ∃ ν : Label → @BornData P.X P.topology P.measurable P.V, Surjective ν

theorem signed_source_bridge : signedScope ↔ ∀ P : SignedInputs, signedConclusion P := by
  constructor
  · intro h P
    exact @h P.X P.topology P.metrizable P.compact P.measurable P.borel P.secondCountable P.V P.CH
  · intro h X topology metrizable compact measurable borel secondCountable V CH
    exact h ⟨X, topology, metrizable, compact, measurable, borel, secondCountable, V, CH⟩

theorem signed_actual_positive : ∀ P : SignedInputs, signedConclusion P :=
  signed_source_bridge.mp @exists_signed_enumeration

/-- These carry exact original statements; no source-binding status is asserted. -/
theorem encoding_source : encodingScope.{u} := @signed_sequences_card_le_continuum.{u}
theorem support_source : supportScope.{u} := @exists_supportFamily.{u}
theorem clopen_source : clopenScope := @exists_clopen_enumerations

end Reg.D5.S3.Topology.InverseLimit.SignedBirthEnumeration
