import Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingRearFirstOrder
import D5.S3.Fourier.Asymptotics.CyclicGrowingThresholdExact

/-! Source dependence of the exact adjacent-window comparison and support decision. -/

namespace Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingThresholdExact

open Filter Matrix Finset Asymptotics
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.CyclicGrowingThresholdExact
open _root_.D5.S3.Fourier.Asymptotics.CyclicGrowingSupport
open _root_.D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits
open _root_.D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit
open _root_.D5.S3.Fourier.Asymptotics.CyclicParityCorrection
open _root_.D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
open _root_.Reg.Support

noncomputable section

namespace Comparison

abbrev signature := CyclicGrowingEdgeLimits.RearEdge.signature
abbrev actual := CyclicGrowingEdgeLimits.RearEdge.actual
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {h : ℕ → ℝ} {K : ℝ},
    Tendsto (fun n : ℕ => (n:ℝ)^5*(h n)^2) atTop (𝓝 K) →
    ∀ e l : ℕ, e<2 →
    let r := (l:ℝ)+1+(e:ℝ)/2
    let S := rearRealOffsets e l
    let T := rearRealOffsets e (l+1)
    let readout := R.readout () ()
    ∀ᶠ n : ℕ in atTop,
      0<(coupledMomentMatrix S n (h n)).det ∧
      0<(coupledMomentMatrix T n (h n)).det ∧
      (coupledMomentMatrix S n (h n)).det*readout (((S,n),h n),r) =
      (coupledMomentMatrix T n (h n)).det*readout (((T,n),h n),r)

private theorem card_even (l : ℕ) : (rearRealOffsets 0 l).card=2*l+1 := by
  classical
  unfold rearRealOffsets
  rw [Finset.card_image_of_injective]
  · simp [rearOffsets,Int.card_Icc]
    omega
  · intro x y h
    simp at h
    exact_mod_cast h

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : Tendsto (fun n : ℕ => (n:ℝ)^5*(0:ℝ)^2) atTop (𝓝 0) := by simp
  have hscale : Tendsto (fun n : ℕ => (n:ℝ)^3*((n:ℝ)*(0:ℝ))^4) atTop (𝓝 0) := by simp
  let S := rearRealOffsets 0 0
  let T := rearRealOffsets 0 1
  have ht := h hs 0 0 (by decide)
  have heq : ∀ᶠ n : ℕ in atTop,
      (coupledMomentMatrix S n 0).det=(coupledMomentMatrix T n 0).det := by
    filter_upwards [ht] with n hn
    have hh := hn.2.2
    change (coupledMomentMatrix S n 0).det*1=(coupledMomentMatrix T n 0).det*1 at hh
    simpa using hh
  have hS := continuous_id.matrix_det.continuousAt.tendsto.comp (coupledMatrix_tendsto hscale S)
  have hT := continuous_id.matrix_det.continuousAt.tendsto.comp (coupledMatrix_tendsto hscale T)
  change Tendsto (fun n => (coupledMomentMatrix S n 0).det) atTop
    (𝓝 (!![(2:ℝ),2/3,0;2/3,2/5,0;0,∑ r∈S,r^2,(S.card:ℝ)]).det) at hS
  change Tendsto (fun n => (coupledMomentMatrix T n 0).det) atTop
    (𝓝 (!![(2:ℝ),2/3,0;2/3,2/5,0;0,∑ r∈T,r^2,(T.card:ℝ)]).det) at hT
  rw [coupledLimit_det] at hS hT
  have hS' : Tendsto (fun n => (coupledMomentMatrix S n 0).det) atTop (𝓝 (16/45:ℝ)) := by
    simpa [S,card_even] using hS
  have hT' : Tendsto (fun n => (coupledMomentMatrix T n 0).det) atTop (𝓝 (16*3/45:ℝ)) := by
    simpa [T,card_even] using hT
  have he := tendsto_nhds_unique (hS'.congr' heq) hT'
  norm_num at he

def evidence : Registration arena (type_of% @adjacent_fit_score) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@adjacent_fit_score, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := CyclicGrowingEdgeLimits.RearEdge.evidence.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@adjacent_fit_score) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingThresholdExact.Comparison.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingThresholdExact.Comparison.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.CyclicGrowingThresholdExact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Comparison

namespace Support

abbrev signature := CyclicGrowingEdgeLimits.Coefficients.signature
abbrev actual := CyclicGrowingEdgeLimits.Coefficients.actual
abbrev rejected := CyclicGrowingEdgeLimits.Coefficients.rejected

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ → ℕ) (hq : ∀ n, q n ≠ 0) (e l : ℕ)
    (_hpar : ∀ᶠ n in atTop, q n % 2 = e) {K : ℝ},
    Tendsto (fun n : ℕ => (n:ℝ)^5*(mesh (q n))^2) atTop (𝓝 K) →
    3*K/20=rearThreshold e (l+1) →
    let readout := R.readout () ()
    let r := (l:ℝ)+1+(e:ℝ)/2
    ∀ᶠ n : ℕ in atTop,
      letI : NeZero (q n) := ⟨hq n⟩
      let k := if 0<rearValue (rearRealOffsets e l) n (mesh (q n)) r then l+1 else l
      let v : ZMod (q n) → ℝ := windowLaw n k (readout ((rearRealOffsets e k,n),mesh (q n)))
      let threshold := 1-2*budget n*(mesh (q n))^2
      cosineMoment 1 v = threshold ∧ cosineMoment 2 v = threshold ∧
      v ∈ feasible (q n) threshold ∧
        (∀ w ∈ feasible (q n) threshold, w ≠ v → energy v < energy w) ∧
        (∀ w ∈ feasible (q n) threshold, energy v + (∑ i,(w i-v i)^2) ≤ energy w) ∧
        ∀ w ∈ feasible (q n) threshold, IsMinOn energy (feasible (q n) threshold) w →
          ∀ i, 0 < max 0 (w i) ↔ i ∈ frontSites (q n) n ∪ rearSites (q n) k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let q := CyclicGrowingRearFirstOrder.Support.cycles
  have hq := CyclicGrowingRearFirstOrder.Support.cycles_nonzero
  have ht := h q hq 0 0
    (Eventually.of_forall fun n => by
      by_cases hn : n=0 <;> simp [q,CyclicGrowingRearFirstOrder.Support.cycles,hn])
    CyclicGrowingRearFirstOrder.Support.cycles_scale (by norm_num [rearThreshold])
  obtain ⟨n,hn⟩ := ht.exists
  letI : NeZero (q n) := ⟨hq n⟩
  let k : ℕ := if 0<rearValue (rearRealOffsets 0 0) n (mesh (q n)) (((0:ℕ):ℝ)+1+((0:ℕ):ℝ)/2) then 0+1 else 0
  have hf := hn.2.2.1
  change windowLaw n k (rejected.readout () () ((rearRealOffsets 0 k,n),mesh (q n))) ∈
    feasible (q n) _ at hf
  change windowLaw n k 0 ∈ feasible (q n) _ at hf
  have hz : windowLaw (q := q n) n k 0 = 0 := by
    funext i
    simp only [windowLaw]
    split
    · change _ ⬝ᵥ (0 : Fin 3 → ℝ) = _
      simp
    · rfl
  rw [hz] at hf
  have hm := hf.2.1
  simp at hm

def evidence : Registration arena (type_of% @eventual_support_at_leading_threshold) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eventual_support_at_leading_threshold, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := CyclicGrowingEdgeLimits.Coefficients.evidence.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@eventual_support_at_leading_threshold) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingThresholdExact.Support.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingThresholdExact.Support.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.CyclicGrowingThresholdExact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Support

end

end Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingThresholdExact
