/- SOURCE_ONLY_UNCOMPILED.
All 19 final registrations remain in this exact mirrored owner.
Static source preparation only; formal verification remains pending.
-/
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Analysis.Source
import D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
import Reg.Support.DependentFamily
import Reg.Support.PrimeSymbolMeanSquare.PhaseAndFiniteFamilies
import Reg.Support.PrimeSymbolMeanSquare.MeanSquareAndTailFamilies

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open LeanInformationAudit
namespace Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare

namespace prime_symbol_block
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@prime_symbol_block) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.prime_symbol_block.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.prime_symbol_block.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => primeSquareMass c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end prime_symbol_block

namespace finite_abel_majorant
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@finite_abel_majorant) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.finite_abel_majorant.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.finite_abel_majorant.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ w i => w i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "arg", "body", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end finite_abel_majorant

namespace prime_symbol_square_tail
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@prime_symbol_square_tail) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.prime_symbol_square_tail.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.prime_symbol_square_tail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ c M => primeTailBudget c M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end prime_symbol_square_tail

namespace canonical_first_jet_prime_tail
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@canonical_first_jet_prime_tail) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.canonical_first_jet_prime_tail.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.canonical_first_jet_prime_tail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end canonical_first_jet_prime_tail

namespace logLength_pos
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@logLength_pos) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.logLength_pos.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.logLength_pos.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => logLength c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end logLength_pos

namespace phase_geometry
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@phase_geometry) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.phase_geometry.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.phase_geometry.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ c q => theta c q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end phase_geometry

namespace primePhase_norm
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@primePhase_norm) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.primePhase_norm.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.primePhase_norm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end primePhase_norm

namespace primePhase_noncollision
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@primePhase_noncollision) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.primePhase_noncollision.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.primePhase_noncollision.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => conj z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end primePhase_noncollision

namespace owner_term_cutoff
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@owner_term_cutoff) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.owner_term_cutoff.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.owner_term_cutoff.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.sin x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end owner_term_cutoff

namespace owner_prime_sum_eq
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@owner_prime_sum_eq) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.owner_prime_sum_eq.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.owner_prime_sum_eq.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.sin x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "body", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end owner_prime_sum_eq

namespace owner_prime_sum_inclusive
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@owner_prime_sum_inclusive) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.owner_prime_sum_inclusive.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.owner_prime_sum_inclusive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.sin x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "body", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end owner_prime_sum_inclusive

namespace primeSymbol_is_im
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@primeSymbol_is_im) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.primeSymbol_is_im.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.primeSymbol_is_im.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.im) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end primeSymbol_is_im

namespace geometric_block_norm
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@geometric_block_norm) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.geometric_block_norm.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.geometric_block_norm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end geometric_block_norm

namespace norm_square_expansion
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@norm_square_expansion) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.norm_square_expansion.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.norm_square_expansion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end norm_square_expansion

namespace inverseSquareWeight_antitone
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@inverseSquareWeight_antitone) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.inverseSquareWeight_antitone.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.inverseSquareWeight_antitone.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ M j => inverseSquareWeight M j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end inverseSquareWeight_antitone

namespace complex_prime_energy
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@complex_prime_energy) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.complex_prime_energy.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.complex_prime_energy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end complex_prime_energy

namespace complex_prime_tail
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@complex_prime_tail) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.complex_prime_tail.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.complex_prime_tail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end complex_prime_tail

namespace retained_arithmetic_tail
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@retained_arithmetic_tail) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.retained_arithmetic_tail.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.retained_arithmetic_tail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end retained_arithmetic_tail

namespace canonical_first_jet_split
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@canonical_first_jet_split) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.canonical_first_jet_split.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.canonical_first_jet_split.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => arithmeticBoundarySymbol p.1 p.2 + x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare,
    definition := none,
    coordinates := #[0, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end canonical_first_jet_split

end Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
