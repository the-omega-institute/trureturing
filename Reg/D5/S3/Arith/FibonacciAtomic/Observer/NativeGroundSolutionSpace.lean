import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace
import Reg.Support.DependentFamily
import Reg.Support.NativeGroundAssignmentEvidence
import Reg.Support.NativeGroundExtensionEvidence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

open NativeTermUnification Lambda Strata.Util
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace

noncomputable def registration_Ext_sol :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@Ext_sol)
      (type_of% (realize signature (fun _ a w => _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext a.p a.C a.S a.success w)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.extension,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ a w => _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext a.p a.C a.S a.success w)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0,1,2,3],
    readouts := #[{
      path := #["body","body","body","body","body","body","arg"], stateBinder := 5,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_groundSubst_find :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundSubst_find)
      (type_of% (realize Audit_groundSubst_find.signature (fun _ a s => (groundSubst a.2.1 a.2.2).find? s) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_groundSubst_find.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_groundSubst_find.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_groundSubst_find.arena⟩,
  objectArena := .source ⟨Audit_groundSubst_find.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_groundSubst_find.arena ⟨Audit_groundSubst_find.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_groundSubst_find.signature (fun _ a s => (groundSubst a.2.1 a.2.2).find? s) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_groundSubst_other :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundSubst_other)
      (type_of% (realize Audit_groundSubst_other.signature (fun _ a s => (groundSubst a.2.1 a.2.2).find? s) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_groundSubst_other.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_groundSubst_other.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_groundSubst_other.arena⟩,
  objectArena := .source ⟨Audit_groundSubst_other.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_groundSubst_other.arena ⟨Audit_groundSubst_other.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_groundSubst_other.signature (fun _ a s => (groundSubst a.2.1 a.2.2).find? s) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_groundSubst_evaluate :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundSubst_evaluate)
      (type_of% (realize Audit_groundSubst_evaluate.signature (fun _ _ u => encodeGround u) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_groundSubst_evaluate.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_groundSubst_evaluate.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_groundSubst_evaluate.arena⟩,
  objectArena := .source ⟨Audit_groundSubst_evaluate.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_groundSubst_evaluate.arena ⟨Audit_groundSubst_evaluate.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_groundSubst_evaluate.signature (fun _ _ u => encodeGround u) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_encodeGround_injective :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.encodeGround_injective)
      (type_of% (realize Audit_encodeGround_injective.signature (fun _ _ u => encodeGround u) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_encodeGround_injective.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_encodeGround_injective.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_encodeGround_injective.arena⟩,
  objectArena := .source ⟨Audit_encodeGround_injective.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_encodeGround_injective.arena ⟨Audit_encodeGround_injective.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_encodeGround_injective.signature (fun _ _ u => encodeGround u) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["arg"], stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_groundSubst_sol :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundSubst_sol)
      (type_of% (realize Audit_groundSubst_sol.signature (fun _ a t => LMonoTy.subst (groundSubst a.2.1 a.2.2) t) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_groundSubst_sol.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_groundSubst_sol.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_groundSubst_sol.arena⟩,
  objectArena := .source ⟨Audit_groundSubst_sol.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_groundSubst_sol.arena ⟨Audit_groundSubst_sol.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_groundSubst_sol.signature (fun _ a t => LMonoTy.subst (groundSubst a.2.1 a.2.2) t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 1, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_native_complete :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.native_complete)
      (type_of% (realize Audit_native_complete.signature (fun _ a C => encodeEquations a.2 C) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_native_complete.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_native_complete.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_native_complete.arena⟩,
  objectArena := .source ⟨Audit_native_complete.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_native_complete.arena ⟨Audit_native_complete.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_native_complete.signature (fun _ a C => encodeEquations a.2 C) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_output_native :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.output_native)
      (type_of% (realize Audit_output_native.signature (fun _ _ S => S.subst) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_output_native.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_output_native.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_output_native.arena⟩,
  objectArena := .source ⟨Audit_output_native.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_output_native.arena ⟨Audit_output_native.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_output_native.signature (fun _ _ S => S.subst) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_equations_supported :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.equations_supported)
      (type_of% (realize Audit_equations_supported.signature (fun _ a C => (encodeEquations a.2 C).freeVars) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_equations_supported.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_equations_supported.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_equations_supported.arena⟩,
  objectArena := .source ⟨Audit_equations_supported.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_equations_supported.arena ⟨Audit_equations_supported.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_equations_supported.signature (fun _ a C => (encodeEquations a.2 C).freeVars) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "fn", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_output_supported :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.output_supported)
      (type_of% (realize Audit_output_supported.signature (fun _ _ S => Subst.freeVars S) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_output_supported.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_output_supported.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_output_supported.arena⟩,
  objectArena := .source ⟨Audit_output_supported.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_output_supported.arena ⟨Audit_output_supported.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_output_supported.signature (fun _ _ S => Subst.freeVars S) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "fn", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_action_encode :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_encode)
      (type_of% (realize Audit_action_encode.signature (fun _ a x => action a.2.1 a.2.2 x) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_action_encode.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_action_encode.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_action_encode.arena⟩,
  objectArena := .source ⟨Audit_action_encode.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_action_encode.arena ⟨Audit_action_encode.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_action_encode.signature (fun _ a x => action a.2.1 a.2.2 x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 1, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_encode_variables :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.encode_variables)
      (type_of% (realize Audit_encode_variables.signature (fun _ a t => encode a.2 t) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_encode_variables.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_encode_variables.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_encode_variables.arena⟩,
  objectArena := .source ⟨Audit_encode_variables.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_encode_variables.arena ⟨Audit_encode_variables.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_encode_variables.signature (fun _ a t => encode a.2 t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_action_support :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_support)
      (type_of% (realize Audit_action_support.signature (fun _ a S => D a.2 S) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_action_support.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_action_support.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_action_support.arena⟩,
  objectArena := .source ⟨Audit_action_support.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_action_support.arena ⟨Audit_action_support.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_action_support.signature (fun _ a S => D a.2 S) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_action_identity :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_identity)
      (type_of% (realize Audit_action_identity.signature (fun _ a x => action a.2.1 a.2.2 x) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_action_identity.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_action_identity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_action_identity.arena⟩,
  objectArena := .source ⟨Audit_action_identity.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_action_identity.arena ⟨Audit_action_identity.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_action_identity.signature (fun _ a x => action a.2.1 a.2.2 x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_bound_iff_nonidentity :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.bound_iff_nonidentity)
      (type_of% (realize Audit_bound_iff_nonidentity.signature (fun _ a x => action a.2.1 a.2.2 x) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_bound_iff_nonidentity.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_bound_iff_nonidentity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_bound_iff_nonidentity.arena⟩,
  objectArena := .source ⟨Audit_bound_iff_nonidentity.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_bound_iff_nonidentity.arena ⟨Audit_bound_iff_nonidentity.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_bound_iff_nonidentity.signature (fun _ a x => action a.2.1 a.2.2 x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 1, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_evaluate_restrictTerm :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.evaluate_restrictTerm)
      (type_of% (realize Audit_evaluate_restrictTerm.signature (fun _ a t => evaluate a.2 t) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_evaluate_restrictTerm.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_evaluate_restrictTerm.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_evaluate_restrictTerm.arena⟩,
  objectArena := .source ⟨Audit_evaluate_restrictTerm.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_evaluate_restrictTerm.arena ⟨Audit_evaluate_restrictTerm.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_evaluate_restrictTerm.signature (fun _ a t => evaluate a.2 t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_restriction_Ext :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.restriction_Ext)
      (type_of% (realize Audit_restriction_Ext.signature (fun _ a v => restriction a.2.1 a.2.2 v) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_restriction_Ext.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_restriction_Ext.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_restriction_Ext.arena⟩,
  objectArena := .source ⟨Audit_restriction_Ext.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_restriction_Ext.arena ⟨Audit_restriction_Ext.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_restriction_Ext.signature (fun _ a v => restriction a.2.1 a.2.2 v) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 1, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn"], stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_Ext_restriction :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext_restriction)
      (type_of% (realize Audit_Ext_restriction.signature (fun _ a v => restriction a.2.1 a.2.2 v) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_Ext_restriction.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_Ext_restriction.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_Ext_restriction.arena⟩,
  objectArena := .source ⟨Audit_Ext_restriction.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_Ext_restriction.arena ⟨Audit_Ext_restriction.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_Ext_restriction.signature (fun _ a v => restriction a.2.1 a.2.2 v) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 1, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn"], stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_shape_ground :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.shape_ground)
      (type_of% (realize Audit_shape_ground.signature (fun _ _ u => encodeGround u) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_shape_ground.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_shape_ground.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_shape_ground.arena⟩,
  objectArena := .source ⟨Audit_shape_ground.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_shape_ground.arena ⟨Audit_shape_ground.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_shape_ground.signature (fun _ _ u => encodeGround u) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "fn", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_native_ground_iff :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.native_ground_iff)
      (type_of% (realize Audit_native_ground_iff.signature (fun _ _ u => encodeGround u) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_native_ground_iff.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_native_ground_iff.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_native_ground_iff.arena⟩,
  objectArena := .source ⟨Audit_native_ground_iff.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_native_ground_iff.arena ⟨Audit_native_ground_iff.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_native_ground_iff.signature (fun _ _ u => encodeGround u) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body", "fn", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_encodeGround_freeVars :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.encodeGround_freeVars)
      (type_of% (realize Audit_encodeGround_freeVars.signature (fun _ _ u => encodeGround u) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_encodeGround_freeVars.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_encodeGround_freeVars.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_encodeGround_freeVars.arena⟩,
  objectArena := .source ⟨Audit_encodeGround_freeVars.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_encodeGround_freeVars.arena ⟨Audit_encodeGround_freeVars.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_encodeGround_freeVars.signature (fun _ _ u => encodeGround u) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_substitute_evaluate :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.substitute_evaluate)
      (type_of% (realize Audit_substitute_evaluate.signature (fun _ a t => substitute a.2 t) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_substitute_evaluate.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_substitute_evaluate.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_substitute_evaluate.arena⟩,
  objectArena := .source ⟨Audit_substitute_evaluate.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_substitute_evaluate.arena ⟨Audit_substitute_evaluate.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_substitute_evaluate.signature (fun _ a t => substitute a.2 t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_action_substitute_encode :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_substitute_encode)
      (type_of% (realize Audit_action_substitute_encode.signature (fun _ a x => action a.2.1 a.2.2 x) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_action_substitute_encode.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_action_substitute_encode.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_action_substitute_encode.arena⟩,
  objectArena := .source ⟨Audit_action_substitute_encode.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_action_substitute_encode.arena ⟨Audit_action_substitute_encode.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_action_substitute_encode.signature (fun _ a x => action a.2.1 a.2.2 x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 1, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"], stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_action_idempotent :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.action_idempotent)
      (type_of% (realize Audit_action_idempotent.signature (fun _ a x => action a.2.1 a.2.2 x) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_action_idempotent.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_action_idempotent.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_action_idempotent.arena⟩,
  objectArena := .source ⟨Audit_action_idempotent.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_action_idempotent.arena ⟨Audit_action_idempotent.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_action_idempotent.signature (fun _ a x => action a.2.1 a.2.2 x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 1, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"], stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_total_action_spec :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.total_action_spec)
      (type_of% (realize Audit_total_action_spec.signature (fun _ a x => action a.2.1 a.2.2 x) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_total_action_spec.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_total_action_spec.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_total_action_spec.arena⟩,
  objectArena := .source ⟨Audit_total_action_spec.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_total_action_spec.arena ⟨Audit_total_action_spec.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_total_action_spec.signature (fun _ a x => action a.2.1 a.2.2 x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 1, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"], stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_restriction_fill :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.restriction_fill)
      (type_of% (realize Audit_restriction_fill.signature (fun _ a w => restriction a.2.1 a.2.2 (fill a.2.1 a.2.2 w)) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_restriction_fill.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_restriction_fill.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_restriction_fill.arena⟩,
  objectArena := .source ⟨Audit_restriction_fill.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_restriction_fill.arena ⟨Audit_restriction_fill.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_restriction_fill.signature (fun _ a w => restriction a.2.1 a.2.2 (fill a.2.1 a.2.2 w)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_Ext_evaluate_action :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Ext_evaluate_action)
      (type_of% (realize Audit_Ext_evaluate_action.signature (fun _ a t => evaluate (fill a.2.1 a.2.2.1 a.2.2.2) t) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_Ext_evaluate_action.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_Ext_evaluate_action.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_Ext_evaluate_action.arena⟩,
  objectArena := .source ⟨Audit_Ext_evaluate_action.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_Ext_evaluate_action.arena ⟨Audit_Ext_evaluate_action.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_Ext_evaluate_action.signature (fun _ a t => evaluate (fill a.2.1 a.2.2.1 a.2.2.2) t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[0, 1, 3, 5],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_groundDecoder_exact :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.groundDecoder_exact)
      (type_of% (realize Audit_groundDecoder_exact.signature (fun _ _ t => groundDecoder t) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_groundDecoder_exact.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_groundDecoder_exact.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_groundDecoder_exact.arena⟩,
  objectArena := .source ⟨Audit_groundDecoder_exact.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_groundDecoder_exact.arena ⟨Audit_groundDecoder_exact.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_groundDecoder_exact.signature (fun _ _ t => groundDecoder t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_output_keys :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.output_keys)
      (type_of% (realize Audit_output_keys.signature (fun _ _ S => S.keys) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_output_keys.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace.Audit_output_keys.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Audit_output_keys.arena⟩,
  objectArena := .source ⟨Audit_output_keys.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Audit_output_keys.arena ⟨Audit_output_keys.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Audit_output_keys.signature (fun _ _ S => S.keys) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "fn", "arg"], stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }



end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace
