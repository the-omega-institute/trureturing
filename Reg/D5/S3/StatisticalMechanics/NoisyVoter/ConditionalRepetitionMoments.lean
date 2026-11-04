import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.NoisyVoter.ConditionalRepetitionMoments
import Reg.Support.DependentFamily

/-! The original conditional-expectation operator on arbitrary probability spaces. -/

namespace Reg.D5.S3.StatisticalMechanics.NoisyVoter.ConditionalRepetitionMoments

open MeasureTheory ProbabilityTheory Filter
open _root_.D5.S3.StatisticalMechanics.NoisyVoter
open RepetitionVarianceLinear ConditionalRepetitionMoments
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure Parameters where
  Sample : Type
  measurable : MeasurableSpace Sample
  measure : @Measure Sample measurable
  field : MeasurableSpace Sample

abbrev signature : Signature where
  Params := Parameters
  State p := p.Sample → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.Sample → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout (p : Parameters) (f : p.Sample → ℝ) : p.Sample → ℝ := by
  letI := p.measurable
  exact p.measure[f | p.field]

def actual : Realization signature :=
  realize signature (fun _ p f => actualReadout p f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

/-- Both formulas retain the original graph, law, process and conditioning field. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V Ω : Type} {G : SimpleGraph V} [G.LocallyFinite] [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (M : Model G P) (u : V) (d t : ℕ) (_hd : 1 ≤ d),
    (R.readout () ⟨Ω,mΩ,P,H M⟩ (W M.coordinate u d t) =ᵐ[P]
      fun ω => ((t : ℝ) + C M u d t ω) / 2) ∧
    (R.readout () ⟨Ω,mΩ,P,H M⟩
      (fun ω => (W M.coordinate u d t ω -
        R.readout () ⟨Ω,mΩ,P,H M⟩ (W M.coordinate u d t) ω)^2) =ᵐ[P]
      fun ω => (1/4 : ℝ) * ∑ e ∈ pairs G u (t+d), (multiplicity M u d t e ω : ℝ)^2)

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  let G : SimpleGraph (Fin 2) := ⊤
  have hNbr : ∀ v, ∃ w, G.Adj v w := by
    intro v
    fin_cases v
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
  let ε : unitInterval := ⟨1/2, by norm_num, by norm_num⟩
  let S := (c : Coord (Fin 2)) → Value G c
  let Q : Measure S := Measure.infinitePi (coordinateLaw G ε hNbr)
  let M : Model G Q := {
    probability := inferInstance
    connected := SimpleGraph.connected_top
    hasNeighbor := hNbr
    ε := ε
    positiveNoise := by norm_num [ε]
    belowOne := by norm_num [ε]
    coordinate := fun c z => z c
    measurable_coordinate := fun c => measurable_pi_apply c
    independent := iIndepFun_infinitePi (X := fun _ a => a) (fun _ => measurable_id)
    laws := fun c => ⟨(measurable_pi_apply c).aemeasurable,
      (measurePreserving_eval_infinitePi (coordinateLaw G ε hNbr) c).map_eq⟩ }
  let := M.probability
  have hb := (h Q M 0 1 0 (by omega)).1
  have hfalse : ∀ᵐ _ω ∂Q, False := hb.mono (by
    intro ω hω
    norm_num [rejected, realize, C] at hω)
  have hz : Q = 0 := by simpa using hfalse
  have hmass := congrArg (fun μ : Measure S => μ Set.univ) hz
  simpa using hmass

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let p : Parameters := ⟨Unit, inferInstance, Measure.dirac (), ⊤⟩
  refine ⟨p, (fun _ => 0), (fun _ => 1), ?_⟩
  have h0 : actual.readout i p (fun _ => 0) = (fun _ => 0) := by
    exact condExp_const le_rfl 0
  have h1 : actual.readout i p (fun _ => 1) = (fun _ => 1) := by
    exact condExp_const le_rfl 1
  rw [h0,h1]
  intro h
  have := congrFun h ()
  norm_num at this

def source_registration : Registration arena (type_of% (@conditional_repetition_moments)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@conditional_repetition_moments, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@conditional_repetition_moments) (Realization signature) Unit Unit where
  unitName := `D5.S3.StatisticalMechanics.NoisyVoter.ConditionalRepetitionMoments.conditional_repetition_moments.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p f => actualReadout p f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.NoisyVoter.ConditionalRepetitionMoments
    definition := none
    coordinates := #[]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.NoisyVoter.ConditionalRepetitionMoments
