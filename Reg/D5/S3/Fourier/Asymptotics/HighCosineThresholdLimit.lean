import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Asymptotics.HighCosineThresholdLimit

/-! The contact level and scale of the finite two-cosine threshold. -/

namespace Reg.D5.S3.Fourier.Asymptotics.HighCosineThresholdLimit

open Filter
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.HighCosineThreshold
open _root_.D5.S3.Fourier.Asymptotics.HighCosineThresholdLimit
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

namespace Contact

def actual : Realization signature :=
  realize signature (fun _ _ q => Real.cos (4 * Real.pi / q)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    let contact := fun q : ℕ => R.readout () () q
    ∀ᶠ q : ℕ in atTop,
      let c := cyclicReadout q
      let u := cyclicUpper q
      let l := cyclicLower q
      let v := contact q
      let a := criticalThreshold c u l
      let r := (1 - a) / (1 - tailMoment u l)
      let nu := count c u
      let nl := count c l
      let P := polynomial u l nu nl r
      let β := firstMultiplier u l nu nl r
      let γ := secondMultiplier u l nu nl r
      l < v ∧ v < u ∧ (∃ i, c i = v) ∧ 0 < r ∧ r < 1 ∧
        0 < β ∧ 0 < γ ∧ P v = 0 ∧
        (∀ i, l < c i → c i < u → c i ≠ v → P (c i) < 0) ∧
        P 1 = 1 - r ∧ P u = r * upperFraction u l / nu ∧
        P l = r * (1 - upperFraction u l) / nl ∧
        (∀ x, P x = (topCoeff u l r * u * l + upperCoeff u l nu r * l +
          lowerCoeff u l nl r * u + γ) + β * x + γ * (2 * x ^ 2 - 1)) ∧
        (∀ i, weights c u l r i = max 0 (P (c i))) ∧ IsCertified c u l a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨q, h⟩ := law.exists
  have hlt : (2 : ℝ) < cyclicUpper q := h.2.1
  change (2 : ℝ) < Real.cos (2 * Real.pi / q) at hlt
  linarith only [hlt, Real.cos_le_one (2 * Real.pi / q)]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 4, 8, ?_⟩
  change Real.cos (4 * Real.pi / (↑(4 : ℕ) : ℝ)) ≠ Real.cos (4 * Real.pi / (↑(8 : ℕ) : ℝ))
  norm_num only [Nat.cast_ofNat]
  rw [show 4 * Real.pi / 4 = Real.pi by ring,
    show 4 * Real.pi / 8 = Real.pi / 2 by ring, Real.cos_pi, Real.cos_pi_div_two]
  norm_num

def evidence : Registration arena (type_of% @cyclic_threshold_first_contact) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_threshold_first_contact, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@cyclic_threshold_first_contact) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.HighCosineThresholdLimit.Contact.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.HighCosineThresholdLimit.Contact.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.HighCosineThresholdLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Contact

namespace Scale

def actual : Realization signature :=
  realize signature (fun _ _ q => (q : ℝ) ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    let scale := fun q : ℕ => R.readout () () q
    Tendsto (fun q : ℕ => scale q *
      (1 - criticalThreshold (cyclicReadout q) (cyclicUpper q) (cyclicLower q)))
      atTop (𝓝 (24 * Real.pi ^ 2 / 5))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (24 * Real.pi ^ 2 / 5)) := by
    simpa [arena, rejected, realize] using law
  have he := tendsto_nhds_unique tendsto_const_nhds hz
  have hp : 0 < 24 * Real.pi ^ 2 / 5 := by positivity
  exact hp.ne' he.symm

def evidence : Registration arena (type_of% @cyclic_criticalThreshold_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_criticalThreshold_limit, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (↑(0 : ℕ) : ℝ) ^ 2 ≠ (↑(1 : ℕ) : ℝ) ^ 2
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@cyclic_criticalThreshold_limit) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.HighCosineThresholdLimit.Scale.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.HighCosineThresholdLimit.Scale.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.HighCosineThresholdLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Scale

end

end Reg.D5.S3.Fourier.Asymptotics.HighCosineThresholdLimit
