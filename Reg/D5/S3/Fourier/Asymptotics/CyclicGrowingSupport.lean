import Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits
import D5.S3.Fourier.Asymptotics.CyclicGrowingSupport
import Mathlib.Analysis.Real.Pi.Bounds

/-! Dependence of the strict eventual optimizer support on the fitted coefficients. -/

namespace Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingSupport

open Filter Matrix Finset
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.CyclicGrowingSupport
open _root_.D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit
open _root_.D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits
open _root_.D5.S3.Fourier.Asymptotics.CyclicParityCorrection
open _root_.D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
open _root_.D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
open _root_.Reg.Support

noncomputable section

abbrev signature := CyclicGrowingEdgeLimits.Coefficients.signature
abbrev actual := CyclicGrowingEdgeLimits.Coefficients.actual
abbrev rejected := CyclicGrowingEdgeLimits.Coefficients.rejected

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ → ℕ) (hq : ∀ n, q n ≠ 0) (e : ℕ)
    (_hpar : ∀ᶠ n in atTop, q n % 2 = e) {K : ℝ},
    Tendsto (fun n : ℕ => (n : ℝ)^5 * (mesh (q n))^2) atTop (𝓝 K) →
    (∀ l, 3*K/20 ≠ rearThreshold e l) →
    let readout := R.readout () ()
    ∃! l : ℕ, rearThreshold e l < 3*K/20 ∧ 3*K/20 < rearThreshold e (l+1) ∧
      ∀ᶠ n : ℕ in atTop,
        letI : NeZero (q n) := ⟨hq n⟩
        let v : ZMod (q n) → ℝ :=
          windowLaw n l (readout ((rearRealOffsets e l,n),mesh (q n)))
        let threshold := 1-2*budget n*(mesh (q n))^2
        cosineMoment 1 v = threshold ∧ cosineMoment 2 v = threshold ∧
        v ∈ feasible (q n) threshold ∧
        (∀ w ∈ feasible (q n) threshold, w ≠ v → energy v < energy w) ∧
        (∀ w ∈ feasible (q n) threshold, energy v + (∑ i,(w i-v i)^2) ≤ energy w) ∧
        ∀ w ∈ feasible (q n) threshold, IsMinOn energy (feasible (q n) threshold) w →
          ∀ i, 0 < max 0 (w i) ↔ i ∈ frontSites (q n) n ∪ rearSites (q n) l

private def cycles (n : ℕ) : ℕ :=
  if n=0 then 2 else 2*n^2*⌈Real.sqrt (n:ℝ)⌉₊

private theorem cycles_nonzero (n : ℕ) : cycles n ≠ 0 := by
  by_cases h : n=0
  · simp [cycles,h]
  · have hn : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
    have hc : 0 < ⌈Real.sqrt (n:ℝ)⌉₊ := Nat.ceil_pos.mpr (Real.sqrt_pos.mpr hn)
    simp [cycles,h,hc.ne']

private theorem cycles_scale :
    Tendsto (fun n : ℕ => (n : ℝ)^5 * (mesh (cycles n))^2) atTop (𝓝 (Real.pi^2)) := by
  have hs : Tendsto (fun n : ℕ => Real.sqrt (n:ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun n : ℕ => (⌈Real.sqrt (n:ℝ)⌉₊ : ℝ) / Real.sqrt (n:ℝ)) atTop (𝓝 1) :=
    tendsto_nat_ceil_div_atTop.comp hs
  have hv := (tendsto_const_nhds (x := Real.pi^2)).div (hr.pow 2) (by norm_num)
  apply (show Tendsto (fun n : ℕ => Real.pi^2 / ((⌈Real.sqrt (n:ℝ)⌉₊ : ℝ) / Real.sqrt (n:ℝ))^2)
      atTop (𝓝 (Real.pi^2)) by
        change Tendsto (fun n : ℕ => Real.pi^2 / ((⌈Real.sqrt (n:ℝ)⌉₊ : ℝ) /
          Real.sqrt (n:ℝ))^2) atTop (𝓝 (Real.pi^2 / 1^2)) at hv
        simpa using hv).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hn0 : n ≠ 0 := by omega
  have hnr : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hc : 0 < (⌈Real.sqrt (n:ℝ)⌉₊ : ℝ) := by
    exact_mod_cast Nat.ceil_pos.mpr (Real.sqrt_pos.mpr hnr)
  have hs0 := Real.sqrt_pos.mpr hnr
  rw [cycles,ite_eq_right hn0,mesh]
  push_cast
  rw [div_pow, div_div_eq_mul_div, Real.sq_sqrt hnr.le]
  field_simp [hnr.ne',hc.ne']

private theorem scale_not_threshold (l : ℕ) :
    3*Real.pi^2/20 ≠ rearThreshold 0 l := by
  have hlo : 3/4 < 3*Real.pi^2/20 := by
    nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi-3)]
  have hhi : 3*Real.pi^2/20 < 15/2 := by
    nlinarith [Real.pi_lt_four, Real.pi_pos,
      mul_pos (sub_pos.mpr Real.pi_lt_four) (add_pos Real.pi_pos (by norm_num : (0:ℝ)<4))]
  rcases l with _ | l
  · simp [rearThreshold]
  rcases l with _ | l
  · norm_num [rearThreshold] at *
    linarith
  · have hbound : (15:ℝ)/2 ≤ rearThreshold 0 (l+2) := by
      simp [rearThreshold]
      have hnonneg : 0 ≤ (l:ℝ) := Nat.cast_nonneg _
      nlinarith only [hnonneg,sq_nonneg (l:ℝ),mul_nonneg hnonneg (sq_nonneg (l:ℝ))]
    linarith

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨l,hl,_⟩ := h cycles cycles_nonzero 0
    (Eventually.of_forall fun n => by by_cases h : n=0 <;> simp [cycles,h,Nat.mul_mod])
    cycles_scale scale_not_threshold
  obtain ⟨n,hn⟩ := hl.2.2.exists
  letI : NeZero (cycles n) := ⟨cycles_nonzero n⟩
  have hf := hn.2.2.1
  change windowLaw n l 0 ∈ feasible (cycles n) _ at hf
  have hz : windowLaw (q := cycles n) n l 0 = 0 := by
    funext i
    simp only [windowLaw]
    split
    · change _ ⬝ᵥ (0 : Fin 3 → ℝ) = _
      simp
    · rfl
  rw [hz] at hf
  have hm := hf.2.1
  simp at hm

def evidence : Registration arena (type_of% @eventual_strict_support_away_from_thresholds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eventual_strict_support_away_from_thresholds, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := CyclicGrowingEdgeLimits.Coefficients.evidence.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@eventual_strict_support_away_from_thresholds) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingSupport.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingSupport.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.CyclicGrowingSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingSupport
