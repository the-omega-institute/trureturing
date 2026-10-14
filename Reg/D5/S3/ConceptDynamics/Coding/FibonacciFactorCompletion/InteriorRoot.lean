import Reg.Support.FibonacciFactorCompletion.InteriorRootReadouts
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal94
noncomputable section

def original_spectral_positive_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_spectral_positive)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => weightedRadius p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal94.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal94.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => weightedRadius p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_spectral_positive_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal94

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal96
noncomputable section

def original_radius_scaling_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_radius_scaling)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal96.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal96.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_radius_scaling_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal96

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal97
noncomputable section

def original_radius_strict_increase_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_radius_strict_increase)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal97.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal97.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_radius_strict_increase_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal97

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal98
noncomputable section

def original_adjacency_zero_continuous_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_adjacency_zero_continuous)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => complexAdjacency p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal98.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal98.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => complexAdjacency p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_adjacency_zero_continuous_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal98

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal99
noncomputable section

def original_radius_continuous_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_radius_continuous)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal99.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal99.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_radius_continuous_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal99

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal100
noncomputable section

def original_spectral_at_one_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_spectral_at_one)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal100.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal100.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_spectral_at_one_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal100

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal101
noncomputable section

def original_interior_root_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_interior_root)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => weightedRadius p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal101.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal101.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => weightedRadius p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_interior_root_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal101

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal102
noncomputable section

def original_weighted_interior_root_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_weighted_interior_root)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => weightedRadius p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal102.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal102.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => weightedRadius p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_weighted_interior_root_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal102

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal103
noncomputable section

def original_root_rate_families_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_root_rate_families)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => weightedRadius p.2.2.1 p.2.2.2 p.1 p.2.1 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal103.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal103.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => weightedRadius p.2.2.1 p.2.2.2 p.1 p.2.1 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "fn", "arg", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_root_rate_families_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal103


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal91
noncomputable section

def original_positive_weighted_rate_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_positive_weighted_rate)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal91.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal91.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_positive_weighted_rate_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal91


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal92
noncomputable section

def original_memory_rate_nesting_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_memory_rate_nesting)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal92.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal92.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_memory_rate_nesting_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal92

open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.SetWitness


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal85
noncomputable section

def original_low_cap_inclusion_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_low_cap_inclusion)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ _ K => LowCapLanguage K) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal85.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal85.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ _ K => LowCapLanguage K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_low_cap_inclusion_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal85


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal88
noncomputable section

def original_memory_language_nesting_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_memory_language_nesting)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ p K => MemoryLanguage .upper p.1 K p.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal88.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal88.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ p K => MemoryLanguage .upper p.1 K p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_memory_language_nesting_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal88

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal87
noncomputable section

def original_memory_envelopes_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_memory_envelopes)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ q z => finitePast q.1 q.2.1 q.2.2 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal87.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal87.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ q z => finitePast q.1 q.2.1 q.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_memory_envelopes_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal87

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal86
noncomputable section

def literal_bilateral_low_codebook_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.literal_bilateral_low_codebook)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ choices i => lowSequence choices i) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal86.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal86.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ choices i => lowSequence choices i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms literal_bilateral_low_codebook_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal86

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal90
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : MemorySide, Σ _ : ℕ, Σ _ : ℕ, ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ p q => factorCount (MemoryLanguage p.1 p.2.1 p.2.2.1 p.2.2.2) (q*58)) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d : ℝ) (hK : 2 ≤ K) (q : ℕ),
    (2 : ℕ)^q ≤ r.readout () ⟨side, n, K, d⟩ q

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h .lower 0 2 0 le_rfl 0
  exact (by decide : ¬ (2^0 ≤ (0 : ℕ))) impossible

def evidence : Registration sourceArena
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_literal_codebook_growth)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_literal_codebook_growth, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨MemorySide.lower, 0, 2, 0⟩, 0, 1, ?_⟩
    change factorCount (MemoryLanguage .lower 0 2 0) (0*58) ≠
      factorCount (MemoryLanguage .lower 0 2 0) (1*58)
    have zero : factorCount (MemoryLanguage .lower 0 2 0) 0 = 1 := by
      change Nat.card (FactorDictionary (MemoryLanguage .lower 0 2 0) 0) = 1
      apply Nat.card_eq_one_iff_exists.mpr
      refine ⟨⟨[], ⟨?_, rfl⟩⟩, ?_⟩
      · refine ⟨lowSequence (fun _ => false), ?_, 0, ?_⟩
        · exact original_low_cap_inclusion .lower 0 2 0 (by decide)
            (literal_bilateral_low_codebook (fun _ => false) 2 le_rfl).2
        · intro k
          exact Fin.elim0 k
      · intro w
        apply Subtype.ext
        exact word_weight_geometry.2.2 w.val w.property.2
    have positive := original_literal_codebook_growth .lower 0 2 0 le_rfl 1
    norm_num only [Nat.zero_mul, Nat.one_mul, pow_one] at positive ⊢
    rw [zero]
    omega

def original_literal_codebook_growth_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_literal_codebook_growth)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ p q => factorCount (MemoryLanguage p.1 p.2.1 p.2.2.1 p.2.2.2) (q*58)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal90.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal90.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ p q => factorCount (MemoryLanguage p.1 p.2.1 p.2.2.1 p.2.2.2) (q*58)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_literal_codebook_growth_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal90

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal95
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => List CuLetter) (fun _ => ℕ)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ w => wordWeight w) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ w : List CuLetter,
    6*w.length ≤ r.readout () () w ∧ wordWeight w ≤ 20*w.length

theorem source_bridge : (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.word_weight_bounds) ↔
    sourceArena.Law actual := Iff.rfl

theorem positive_law : sourceArena.Law actual := @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.word_weight_bounds

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h [CuLetter.u]).1
  norm_num [rejected, realize] at impossible

theorem sensitivity : Sensitivity sourceArena actual :=
  Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law

theorem actual_dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨(), [], [CuLetter.u], ?_⟩
  norm_num [actual, realize, wordWeight]

def evidence : Registration sourceArena (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.word_weight_bounds) where
  actual := actual
  bridge := source_bridge
  variation := ⟨positive_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := actual_dependence

def word_weight_bounds_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.word_weight_bounds)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ w => wordWeight w) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal95.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal95.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ w => wordWeight w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms word_weight_bounds_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal95

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal93
noncomputable section
open scoped Matrix.Norms.Operator

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature
  (fun _ _ z => z) (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d z : ℝ) (hz : 0 ≤ z),
    ∃ v : CoreVertex side n K d,
      MemoryEdge side K d v.val .u v.val ∧
      ∀ k : ℕ, (z^6)^k ≤ pathMass side n K d (r.readout () () z) k

theorem path_mass_zero_one (side : MemorySide) (n K : ℕ) (d : ℝ) :
    pathMass side n K d 0 1 = 0 := by
  classical
  have bounds := path_mass_norm_bounds side n K d 0 le_rfl 1
  refine le_antisymm ?_ bounds.1
  simpa [(original_adjacency_zero_continuous side n K d).1] using bounds.2.2

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨_, _, mass⟩ := h .lower 0 0 0 1 (by norm_num)
  have impossible := mass 1
  change ((1 : ℝ)^6)^1 ≤ pathMass .lower 0 0 0 0 1 at impossible
  rw [path_mass_zero_one] at impossible
  norm_num at impossible

def evidence : Registration sourceArena
    (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_all_u_cycle) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_all_u_cycle,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def original_all_u_cycle_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_all_u_cycle)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ z => z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal93.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal93.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_all_u_cycle_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal93

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.UpperMemoryIntersection
noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_upper_memory_intersection)
    (type_of% Reg.Support.FibonacciFactorCompletion.UpperMemoryObservation.actual) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.UpperMemoryIntersection.unit, realizationName := `Reg.Support.FibonacciFactorCompletion.UpperMemoryObservation.evidence, realizationSource := none, generated := false,
  arena := .source ⟨Reg.Support.FibonacciFactorCompletion.UpperMemoryObservation.sourceArena⟩, objectArena := .source ⟨Reg.Support.FibonacciFactorCompletion.UpperMemoryObservation.sourceArena⟩, catalog := Lean.Name.anonymous, localNames := false,
  realization := .source Reg.Support.FibonacciFactorCompletion.UpperMemoryObservation.sourceArena ⟨Reg.Support.FibonacciFactorCompletion.UpperMemoryObservation.evidence⟩, correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize.{0,0,0,0,0} Reg.Support.FibonacciFactorCompletion.UpperMemoryObservation.observationSignature (fun _ n K => MemoryLanguage .upper n K) (fun e => nomatch e)), variation := .absent, sensitivity := .absent,
  partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot, definition := none, coordinates := #[3], readouts := #[{ path := #["body", "body", "fn", "arg", "arg", "body", "body", "body", "fn", "arg", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.UpperMemoryIntersection
