import D5.S3.VertexAlgebra.OriginalAllChargeBrstMultiplicity
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.OriginalAllChargeBrstMultiplicity

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  OriginalQQuartetSource OriginalBrstReassembly OriginalAllChargeBrstMultiplicity
  RelativePairing.AbsolutePhysicalNoGhost LatticeOscillatorFockMetric
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure ClassificationParameters where
  lattice : LatticeData
  inverse : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  leftGram : inverse * gramComplex lattice = 1
  rightGram : gramComplex lattice * inverse = 1
  critical : lattice.rank = 26
  charge : Charge lattice
  signatureLaw : charge ≠ 0 → _root_.D5.S3.QuadraticForms.ActualSignature.signature
    (gramReal lattice).toQuadraticForm' = (lattice.rank : ℤ) - 2

def classificationSignature : Signature where
  Params := ClassificationParameters
  State _ := ℤ × ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (ℕ × ℕ) × (ℕ × ℕ)
  Anchor := Empty
  finiteAnchor := inferInstance

def classificationReadout : Realization classificationSignature :=
  realize classificationSignature (fun _ parameter state =>
    let sector := originalEnergySector parameter.lattice parameter.inverse parameter.charge state.1
    let stable := energyStable parameter.lattice parameter.inverse parameter.leftGram
      parameter.rightGram parameter.charge state.1
    ((Module.finrank ℂ (ghostCohomology parameter.lattice parameter.inverse parameter.leftGram
        parameter.rightGram parameter.critical sector stable state.2),
      Module.finrank ℂ (Cohomology parameter.lattice parameter.inverse parameter.leftGram
        parameter.rightGram parameter.critical sector stable)),
      (gradedMultiplicity parameter.lattice parameter.charge state.1 state.2,
        totalMultiplicity parameter.lattice parameter.charge state.1)))
    (fun empty => nomatch empty)

def classificationArena : Arena where
  signature := classificationSignature
  Law readout := ∀ parameter state,
    (readout.readout () parameter state).1 = (readout.readout () parameter state).2

theorem classificationSourceBridge : (type_of% (@original_all_charge_multiplicities)) ↔
    classificationArena.Law classificationReadout := by
  constructor
  · intro source parameter state
    have conclusion := source parameter.lattice parameter.inverse parameter.leftGram
      parameter.rightGram parameter.critical parameter.charge state.1 parameter.signatureLaw state.2
    exact Prod.ext conclusion.1 conclusion.2
  · intro law lattice inverse leftGram rightGram critical charge level signatureLaw degree
    have conclusion := law ⟨lattice, inverse, leftGram, rightGram, critical, charge, signatureLaw⟩
      (level, degree)
    exact ⟨congrArg Prod.fst conclusion, congrArg Prod.snd conclusion⟩

abbrev AmbientRepresentativeTarget := type_of% (@original_ambient_representative)
abbrev OffShellTarget := type_of% (@original_off_shell_zero)
abbrev NegativeLevelTarget := type_of% (@original_negative_level_multiplicities)

theorem ambientSourceBridge : (type_of% (@original_ambient_representative)) ↔
    AmbientRepresentativeTarget := Iff.rfl
theorem offShellSourceBridge : (type_of% (@original_off_shell_zero)) ↔ OffShellTarget := Iff.rfl
theorem negativeLevelSourceBridge : (type_of% (@original_negative_level_multiplicities)) ↔
    NegativeLevelTarget := Iff.rfl

abbrev classificationRealizationObligation := Registration classificationArena
  (type_of% (@original_all_charge_multiplicities))
abbrev classificationContractObligation :=
  Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@original_all_charge_multiplicities)
    (type_of% classificationReadout) (PLift (type_of% (@original_off_shell_zero))) Unit

theorem classification_zero_charge_dependence (parameter : ClassificationParameters)
    (zeroCharge : parameter.charge = 0) :
    classificationReadout.readout () parameter (1, 0) ≠
      classificationReadout.readout () parameter (1, 4) := by
  intro equality
  have law := classificationSourceBridge.mp (@original_all_charge_multiplicities)
  have first := congrArg Prod.fst (law parameter (1, 0))
  have second := congrArg Prod.fst (law parameter (1, 4))
  have ranksSame := congrArg (fun output => output.1.1) equality
  have contradiction := first.symm.trans (ranksSame.trans second)
  have impossible : (1 : ℕ) = 0 := by
    simpa [classificationReadout, realize, gradedMultiplicity, exceptionalMultiplicity,
      zeroCharge, chosenH, complexCharge, gramPair] using contradiction
  exact Nat.one_ne_zero impossible

theorem classification_dependence_of_zero_charge (parameter : ClassificationParameters)
    (zeroCharge : parameter.charge = 0) :
    ObservationalDependence classificationSignature classificationReadout := by
  intro role
  cases role
  exact ⟨parameter, (1, 0), (1, 4), classification_zero_charge_dependence parameter zeroCharge⟩

structure OffShellParameters where
  lattice : LatticeData
  inverse : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  leftGram : inverse * gramComplex lattice = 1
  rightGram : gramComplex lattice * inverse = 1
  critical : lattice.rank = 26
  charge : Charge lattice
  level : ℤ
  offShell : chosenH lattice charge + (level : ℂ) - 1 ≠ 0

abbrev OffShellCohomology (parameter : OffShellParameters) :=
  Cohomology parameter.lattice parameter.inverse parameter.leftGram parameter.rightGram
    parameter.critical
    (originalEnergySector parameter.lattice parameter.inverse parameter.charge parameter.level)
    (energyStable parameter.lattice parameter.inverse parameter.leftGram parameter.rightGram
      parameter.charge parameter.level)

def offShellSignature : Signature where
  Params := OffShellParameters
  State := OffShellCohomology
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := OffShellCohomology
  Anchor := Empty
  finiteAnchor := inferInstance

def offShellReadout : Realization offShellSignature :=
  realize offShellSignature (fun _ _ state => state) (fun empty => nomatch empty)

def offShellArena : Arena where
  signature := offShellSignature
  Law readout := ∀ (parameter : OffShellParameters) (state : OffShellCohomology parameter),
    readout.readout () parameter state = (0 : OffShellCohomology parameter)

theorem offShellRealizationBridge : (type_of% (@original_off_shell_zero)) ↔
    offShellArena.Law offShellReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.inverse parameter.leftGram parameter.rightGram
      parameter.critical parameter.charge parameter.level parameter.offShell state
  · intro law lattice inverse leftGram rightGram critical charge level offShell state
    exact law ⟨lattice, inverse, leftGram, rightGram, critical, charge, level, offShell⟩ state

theorem off_shell_dependence_impossible :
    ¬ ObservationalDependence offShellSignature offShellReadout := by
  intro dependence
  obtain ⟨parameter, first, second, different⟩ := dependence ()
  have law := offShellRealizationBridge.mp (@original_off_shell_zero)
  exact different ((law parameter first).trans (law parameter second).symm)

def negativeSignature : Signature where
  Params := ClassificationParameters
  State _ := {state : ℤ × ℤ // state.1 < 0}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ × ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def negativeReadout : Realization negativeSignature :=
  realize negativeSignature (fun _ parameter state =>
    (classificationReadout.readout () parameter state.val).1) (fun empty => nomatch empty)

def negativeArena : Arena where
  signature := negativeSignature
  Law readout := ∀ parameter state, readout.readout () parameter state = (0, 0)

theorem negativeRealizationBridge : (type_of% (@original_negative_level_multiplicities)) ↔
    negativeArena.Law negativeReadout := by
  constructor
  · intro source parameter state
    have conclusion := source parameter.lattice parameter.inverse parameter.leftGram
      parameter.rightGram parameter.critical parameter.charge state.val.1 parameter.signatureLaw
      state.property state.val.2
    exact Prod.ext conclusion.1 conclusion.2
  · intro law lattice inverse leftGram rightGram critical charge level signatureLaw negative degree
    have conclusion := law ⟨lattice, inverse, leftGram, rightGram, critical, charge, signatureLaw⟩
      ⟨(level, degree), negative⟩
    exact ⟨congrArg Prod.fst conclusion, congrArg Prod.snd conclusion⟩

theorem negative_dependence_impossible :
    ¬ ObservationalDependence negativeSignature negativeReadout := by
  intro dependence
  obtain ⟨parameter, first, second, different⟩ := dependence ()
  have law := negativeRealizationBridge.mp (@original_negative_level_multiplicities)
  exact different ((law parameter first).trans (law parameter second).symm)

end
end Reg.D5.S3.VertexAlgebra.OriginalAllChargeBrstMultiplicity
