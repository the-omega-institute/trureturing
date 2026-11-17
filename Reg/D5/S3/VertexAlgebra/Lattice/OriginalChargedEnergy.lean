import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.SourceBPZ.TransverseHermitian
open _root_.D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.OriginalGram
open _root_.D5.S3.VertexAlgebra.LatticeAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy
open private fullFrame from D5.S3.VertexAlgebra.Energy.OriginalCurrentEnergy
open scoped VertexOperator Matrix

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature LatticeData Carrier (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ v => normD v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def neutralArena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData}, (gramReal D).PosDef →
    ∀ (H : Matrix (Fin D.rank) (Fin D.rank) ℂ),
    H*gramComplex D=1 → gramComplex D*H=1 →
    ∀ (p : Oscillator D) (w : ℕ),
    MvPolynomial.IsWeightedHomogeneous (fun x : Index D => x.2+1) p w →
    ∃ K : ℝ, 0 < K ∧ ∀ v : Carrier D,
      R.readout () D (((Y D (Finsupp.single 0 p))[[(w : ℤ)-1]]) v) ≤
        K*normD (((1+sugawaraMode D H 0)^(2*w)) v)

def chargedArena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData}, (gramReal D).PosDef →
    ∀ (H : Matrix (Fin D.rank) (Fin D.rank) ℂ),
    H*gramComplex D=1 → gramComplex D*H=1 →
    ∀ (a : Charge D), a ≠ 0 →
    let d := (chargeEnergy D a).toNat
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℤ) (v : Carrier D),
      R.readout () D (((actualField D a)[[m+(d : ℤ)-1]]) v) ≤
        C*(1+|(m : ℝ)|)^(2*d)*normD (((1+sugawaraMode D H 0)^(2*d)) v)

private def testLattice : LatticeData where
  rank := 1
  G := Matrix.diagonal (fun _ => 2)
  symmetric := by intro i j; simp [Matrix.diagonal, eq_comm]
  even_diagonal := by intro i; norm_num [Matrix.diagonal]

private theorem test_positive : (gramReal testLattice).PosDef := by
  simpa [gramReal, testLattice] using
    (Matrix.PosDef.diagonal (fun _ : Fin 1 => (by norm_num : (0 : ℝ)<2)))

private def testIndex : Fin testLattice.rank := ⟨0, by decide⟩

private theorem test_charge_nonzero : unitCharge testLattice testIndex ≠ 0 := by
  intro h
  have hh := congrFun h testIndex
  norm_num [unitCharge] at hh

private theorem neutral_rejected : ¬ neutralArena.Law rejected := by
  intro h
  obtain ⟨H,hHG,hGH⟩ := complex_inverse_exists testLattice test_positive
  have hp : MvPolynomial.IsWeightedHomogeneous (fun x : Index testLattice => x.2+1)
      (0 : Oscillator testLattice) 0 := by intro e he; simp at he
  obtain ⟨K,hK,hb⟩ := h test_positive H hHG hGH 0 0 hp
  have hz := hb 0
  norm_num [rejected, realize, normD] at hz

private theorem charged_rejected : ¬ chargedArena.Law rejected := by
  intro h
  obtain ⟨H,hHG,hGH⟩ := complex_inverse_exists testLattice test_positive
  obtain ⟨C,hC,hb⟩ := h test_positive H hHG hGH
    (unitCharge testLattice testIndex) test_charge_nonzero
  have hz := hb 0 0
  norm_num [rejected, realize, normD] at hz

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨testLattice, 0, vacuum testLattice, ?_⟩
  have he := source_delta_delta_eq_factorial (fullFrame test_positive) 0 0
    (1 : SourceBPZ.TransverseHermitian.Polynomial testLattice.rank) 1
  have hi : FactorialFockMetric.inner
      (1 : SourceBPZ.TransverseHermitian.Polynomial testLattice.rank) 1 = 1 := by
    have h := FactorialFockMetric.inner_monomial_left
      (0 : Occupation testLattice.rank) (1 : ℂ)
      (1 : SourceBPZ.TransverseHermitian.Polynomial testLattice.rank)
    simpa [FactorialFockMetric.weight] using h
  have hg : Hm (Finsupp.single (0 : Charge testLattice) 1) (Finsupp.single 0 1)=1 := by
    simpa only [delta, map_one, hi, ite_true] using he
  have hv : normD (vacuum testLattice)=1 := by
    simp only [normD, vacuum, hg, ite_true, Complex.one_re, Real.sqrt_one]
  change normD (0 : Carrier testLattice) ≠ normD (vacuum testLattice)
  rw [hv]
  norm_num [normD]

def neutralEvidence : Registration neutralArena (type_of% (@neutral_energy_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@neutral_energy_bound, rejected, neutral_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    neutralArena.Law actual rejected neutral_rejected
  dependence := actual_dependence

def chargedEvidence : Registration chargedArena (type_of% (@charged_energy_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@charged_energy_bound, rejected, charged_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    chargedArena.Law actual rejected charged_rejected
  dependence := actual_dependence

def neutralAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@neutral_energy_bound) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy.neutralUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy.neutralEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨neutralArena⟩
  objectArena := .source ⟨neutralArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source neutralArena ⟨neutralEvidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def chargedAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@charged_energy_bound) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy.chargedUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy.chargedEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨chargedArena⟩
  objectArena := .source ⟨chargedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source chargedArena ⟨chargedEvidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms neutralEvidence
#print axioms chargedEvidence
end Reg.D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy
