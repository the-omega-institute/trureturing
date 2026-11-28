import D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D
import Reg.Support.UnitSixO.Common

/-! Registration notation for the magnetic and optical readouts. -/

open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D

macro "bindMagnetic% " unit:term:max familyName:term:max arena:term:max family:term:max
    actual:term:max path:term:max : term =>
  `({ unitName := $unit
      realizationName := $familyName
      realizationSource := none
      generated := false
      arena := .source ⟨$arena⟩
      objectArena := .source ⟨$arena⟩
      catalog := Lean.Name.anonymous
      localNames := false
      realization := .source $arena ⟨$family⟩
      correspondence := ⟨.evidence, .evidence⟩
      bundleNonempty := .absent
      readout := some $actual
      variation := .absent
      sensitivity := .absent
      partialSensitivity := none
      escapeFrom := none
      sourceSelection := some {
        owner := `D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D
        definition := none
        coordinates := #[]
        readouts := #[{ path := $path
                        stateBinder := 0
                        functionOperand := true
                        stateOperand := none
                        booleanPredicate := false }] }
      continuation := .unknown
      familyRecord := none
      options := #[] })

end Reg.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D
