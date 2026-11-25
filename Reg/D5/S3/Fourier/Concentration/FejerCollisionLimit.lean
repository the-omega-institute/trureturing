import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.FejerCollisionLimit

/-! The normalized ramp observation determines the hard-band limit. -/

namespace Reg.D5.S3.Fourier.Concentration.FejerCollisionLimit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support
open _root_.D5.S3.Fourier.Concentration.FejerCollisionLimit
open _root_.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open Filter Set Finset
open scoped Topology
universe u v
noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ × ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => max 0 (z.1-z.2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0,0), (1,0), ?_⟩
  norm_num [actual,realize]

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} {l : Filter ι} {I : ι → Type v}
    (s : ∀ n, Finset (I n)) (x c : ∀ n, I n → ℝ),
    (∀ᶠ n in l, ∀ i ∈ s n, ∀ j ∈ s n, 0 ≤ c n i*c n j) →
    ∀ (B η : ι → ℝ), (∀ᶠ n in l, 0 ≤ B n) →
    ∀ (f : ℝ → ℝ) (a d ρ : ℝ), 0 < ρ → HasDerivAt f d a →
    let ramp := R.readout () ()
    let L := fun n t => ∑ i ∈ s n, ∑ j ∈ s n, c n i*c n j*ramp (t,|x n i-x n j|)
    (∀ t : ℝ, |t-a| < ρ → Tendsto (fun n => B n*L n (t*η n)) l (𝓝 (f t))) →
    Tendsto (fun n => (B n*η n)*nearCollisionMass (s n) (x n) (c n) (a*η n)) l (𝓝 d)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro law
  let i := ULift.up.{u} ()
  let j := ULift.up.{v} ()
  have h := law (ι := ULift.{u} Unit) (l := pure i) (I := fun _ => ULift.{v} Unit)
    (fun _ => {j}) (fun _ _ => 0) (fun _ _ => 1)
    (by simp) (fun _ => 1) (fun _ => 1) (by simp)
    (fun _ => 0) 1 0 1 zero_lt_one (hasDerivAt_const 1 0)
    (by intro t ht; simp [rejected,realize])
  simp [nearCollisionMass] at h

def evidence : Registration arena.{u,v} (type_of% @collision_ramp_tendsto_hard.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@collision_ramp_tendsto_hard.{u,v}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence


def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@collision_ramp_tendsto_hard.{u,v}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FejerCollisionLimit.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FejerCollisionLimit.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FejerCollisionLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Fourier.Concentration.FejerCollisionLimit
