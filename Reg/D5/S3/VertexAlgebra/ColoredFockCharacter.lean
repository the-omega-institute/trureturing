import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.ColoredFockCharacter

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.ColoredFockCharacter

open _root_.D5.S3.VertexAlgebra.ColoredFockCharacter
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped PowerSeries.WithPiTopology

universe colorsUniverse

noncomputable section

structure Parameters where
  colors : Type colorsUniverse
  finite : Fintype colors
  decidable : DecidableEq colors

def coefficientSignature : Signature where
  Params := Parameters.{colorsUniverse}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ × ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def coefficientReadout : Realization coefficientSignature.{colorsUniverse} :=
  realize coefficientSignature.{colorsUniverse} (fun _ parameter level => by
    letI := parameter.finite
    letI := parameter.decidable
    exact (Nat.card (EnergyFiber parameter.colors level),
      partitionCoefficient parameter.colors level)) (fun empty => nomatch empty)

def coefficientArena : Arena where
  signature := coefficientSignature.{colorsUniverse}
  Law readout := ∀ parameter level,
    (readout.readout () parameter level).1 = (readout.readout () parameter level).2

theorem coefficientBridge : (type_of% (@energyFiber_card.{colorsUniverse})) ↔
    coefficientArena.{colorsUniverse}.Law coefficientReadout.{colorsUniverse} := by
  constructor
  · intro source parameter level
    exact @source parameter.colors parameter.finite parameter.decidable level
  · intro law colors finite decidable level
    exact law ⟨colors, finite, decidable⟩ level

def characterSignature : Signature where
  Params := ℕ
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := PowerSeries ℕ × PowerSeries ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def characterReadout : Realization characterSignature :=
  realize characterSignature (fun _ (colors : ℕ) _ =>
    (PowerSeries.mk (fun level => Nat.card (EnergyFiber (Fin colors) level)),
      Nat.Partition.genFun (fun _ _ => (1 : ℕ)) ^ colors)) (fun empty => nomatch empty)

def characterArena : Arena where
  signature := characterSignature
  Law readout := ∀ colors state,
    (readout.readout () colors state).1 = (readout.readout () colors state).2

theorem characterBridge : (type_of% (@character)) ↔ characterArena.Law characterReadout := by
  constructor
  · intro source colors _
    exact source colors
  · intro law colors
    exact law colors ()

def eulerSignature : Signature where
  Params := ℕ
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := PowerSeries ℂ × PowerSeries ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def eulerReadout : Realization eulerSignature :=
  realize eulerSignature (fun _ (colors : ℕ) _ =>
    (PowerSeries.mk (fun level => (Nat.card (EnergyFiber (Fin colors) level) : ℂ)),
      (∏' frequency : ℕ,
        (1 - (PowerSeries.X : PowerSeries ℂ) ^ (frequency + 1))⁻¹) ^ colors))
    (fun empty => nomatch empty)

def eulerArena : Arena where
  signature := eulerSignature
  Law readout := ∀ colors state,
    (readout.readout () colors state).1 = (readout.readout () colors state).2

theorem eulerBridge : (type_of% (@character_euler)) ↔ eulerArena.Law eulerReadout := by
  constructor
  · intro source colors _
    exact source colors
  · intro law colors
    exact law colors ()

def characterEscapeFrom := @fiberPartitionTuple.{colorsUniverse}
def characterContinuation : Contract.Continuation Unit := .unknown

abbrev coefficientRealizationObligation := Registration coefficientArena.{colorsUniverse}
  (type_of% (@energyFiber_card.{colorsUniverse}))
abbrev coefficientContractObligation :=
  Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@energyFiber_card.{colorsUniverse})
    (type_of% coefficientReadout.{colorsUniverse}) (type_of% characterEscapeFrom.{colorsUniverse}) Unit
abbrev characterRealizationObligation := Registration characterArena (type_of% (@character))
abbrev characterContractObligation :=
  Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@character)
    (type_of% characterReadout) (type_of% characterEscapeFrom) Unit
abbrev eulerRealizationObligation := Registration eulerArena (type_of% (@character_euler))
abbrev eulerContractObligation :=
  Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@character_euler)
    (type_of% eulerReadout) (type_of% characterEscapeFrom) Unit

end

end Reg.D5.S3.VertexAlgebra.ColoredFockCharacter
