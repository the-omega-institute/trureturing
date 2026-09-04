/- GID: D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Typed arenas expose agenda power, adaptive residues, and the five-atom spectrum. -/

import D5.S3.ConceptDynamics.Aggregation.AgendaPower
import D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
import D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit

/- Library-search audit trail (2026-09-04):
   * Repository searches for `LegacyPrimitiveRealization`, `PrimitiveLawArena`,
     and each of the three source theorem names found only the A2 engine and the
     frozen source theorems imported above; no realization layer was present.
   * Exact hits `ExactAtDepth`, `StaticExactAtCardinality`, and
     `UsesReadoutFamily` are reused from `AdaptiveResidueIdentification`.
   * Pinned Mathlib's `Fintype.ofEquiv`, product instances, and `Nat.find`
     provide the finite carriers and parameterized minimum-depth definitions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas

open D5.S3.ConceptDynamics.InformationEscape

namespace AgendaSource
open D5.S3.ConceptDynamics.Aggregation.AgendaPower
open D5.S3.ConceptDynamics.Aggregation.MajorityCycleNotScalarOrder

section
set_option backward.isDefEq.respectTransparency.types false

private def agendaEquiv : Agenda ≃ Fin 3 × Fin 3 × Fin 3 where
  toFun a := (a.first, a.second, a.final)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩
  left_inv := by rintro ⟨first, second, final⟩; rfl
  right_inv := by rintro ⟨first, second, final⟩; rfl

def agendaFintype : Fintype Agenda := Fintype.ofEquiv _ agendaEquiv.symm

inductive AgendaReadout
  | winner
  | valid
  deriving DecidableEq, Fintype

end

def agendaPowerSignature : PrimitiveSignature Agenda where
  Index := AgendaReadout
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output
    | .winner => Fin 3
    | .valid => Bool
  outputDecidableEq
    | .winner => inferInstance
    | .valid => inferInstance
  axis
    | .winner => .cut
    | .valid => .admit
  readoutAxisNotAnchor := by intro i; cases i <;> simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def agendaPowerArena : PrimitiveLawArena where
  toArena :=
    { State := Agenda
      stateFintype := agendaFintype
      stateDecidableEq := inferInstance }
  signature := agendaPowerSignature
  Law := fun r =>
    (forall desired : Fin 3, exists agenda : Agenda,
      r.readout .valid agenda = true ∧ r.readout .winner agenda = desired) ∧
    exists agenda agenda' : Agenda,
      r.readout .valid agenda = true ∧ r.readout .valid agenda' = true ∧
        agenda ≠ agenda' ∧ r.readout .winner agenda ≠ r.readout .winner agenda'

end AgendaSource

namespace ResidueSource
open D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
open D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification

noncomputable def adaptiveDepthFor
    (readout : ResidueSensor -> ResidueState -> Bool) : Nat := by
  classical
  exact if h : exists depth, ExactAtDepth readout depth then Nat.find h else 0

noncomputable def staticDepthFor
    (readout : ResidueSensor -> ResidueState -> Bool) : Nat := by
  classical
  exact if h : exists cardinality, StaticExactAtCardinality readout cardinality then
      Nat.find h
    else 0

def residueSignature : PrimitiveSignature ResidueState where
  Index := ResidueSensor
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def residueArena : PrimitiveLawArena where
  toArena := Arena.ofFintype ResidueState
  signature := residueSignature
  Law := fun realization =>
    let r : ResidueSensor -> ResidueState -> Bool := realization.readout
    (forall state, r .two state = false <->
      state = zeroState ∨ state = tenState) ∧
    (forall state, r .two state = true <->
      state = fifteenState ∨ state = twentyOneState) ∧
    (exists protocol : BinaryProtocol ResidueState 2,
      (forall history : Fin 0 -> Bool,
        protocol.question ⟨0, by decide⟩ history = r .two) ∧
      (forall history : Fin 1 -> Bool,
        protocol.question ⟨1, by decide⟩ history =
          if history 0 then r .five else r .three) ∧
      UsesReadoutFamily r protocol ∧ Function.Injective protocol.transcript) ∧
    (forall sensor, ¬Function.Injective (r sensor)) ∧
    (forall depth, depth < 2 -> ¬ExactAtDepth r depth) ∧
    adaptiveDepthFor r = 2 ∧ staticDepthFor r = 3 ∧
    adaptiveDepthFor r < staticDepthFor r

end ResidueSource

namespace SpectrumSource
open D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope

def spectrumSignature : PrimitiveSignature SpectrumAtom where
  Index := Unit
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Fin 5
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def spectrumArena : PrimitiveLawArena where
  toArena := Arena.ofFintype SpectrumAtom
  signature := spectrumSignature
  Law := fun r => Function.Bijective (r.readout ())

end SpectrumSource

end D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
