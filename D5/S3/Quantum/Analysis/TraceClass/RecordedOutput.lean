/- GID: D5/S3/Quantum/Analysis/TraceClass/RecordedOutput
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/RecordedOutput
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Norming positive decompositions for trace-class recorded outputs. -/

import D5.S3.Quantum.Analysis.TraceClass.LogRegularization
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Terminal trace-class blocks and scalar fixed-block Bochner records. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
open MeasureTheory

namespace TraceClassRecordedOutput

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {ι X : Type*} [Fintype ι] [MeasurableSpace X]

/-- Real trace, continuous for the trace norm, on an arbitrary complete complex Hilbert space. -/
def traceMass : TraceClass H →L[ℝ] ℝ :=
  Complex.reCLM.comp ((TraceClass.tracePairing (1 : H →L[ℂ] H)).restrictScalars ℝ)

private theorem traceMass_eq (x : TraceClass H) :
    traceMass x = (trace x.1 (TraceClass.isTraceClass_coe x)).re := by
  change (trace ((1 : H →L[ℂ] H) * x.1) _).re = _
  congr 1

private theorem positive_norm (x : TraceClass H) (hx : 0 ≤ x.1) :
    ‖x‖ = traceMass x := by
  rw [TraceClass.norm_eq_traceNorm,traceMass_eq]
  exact QuantumLogEnergy.traceNorm_eq_re_trace _ hx

/-- One terminal block and finitely many exact-record L¹ blocks, with the additive cq norm. -/
abbrev Output (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (ι : Type*) [Fintype ι] {X : Type*} [MeasurableSpace X] (μ : Measure X) :=
  WithLp 1 (TraceClass H × PiLp 1 (fun _ : ι => X →₁[μ] TraceClass K))

/-- Actual componentwise/a.e. positivity, including every retained record. -/
def Positive {μ : Measure X} (q : Output H K ι μ) : Prop :=
  0 ≤ q.fst.1 ∧ ∀ i, ∀ᵐ t ∂μ, 0 ≤ (q.snd i t).1

/-- The complete mass is terminal real trace plus the integrals of the record real traces. -/
def mass {μ : Measure X} : Output H K ι μ →L[ℝ] ℝ :=
  traceMass.comp (WithLp.fstL 1 ℝ _ _) +
    ∑ i : ι, (traceMass (H := K)).comp
      ((L1.integralCLM : (X →₁[μ] TraceClass K) →L[ℝ] TraceClass K).comp
        ((PiLp.proj 1 (fun _ : ι => X →₁[μ] TraceClass K) i).comp
          (WithLp.sndL 1 ℝ _ _)))

private theorem mass_apply {μ : Measure X} (q : Output H K ι μ) :
    mass q = traceMass q.fst + ∑ i, ∫ t, traceMass (q.snd i t) ∂μ := by
  simp only [mass,ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,WithLp.fstL_apply,WithLp.sndL_apply,PiLp.proj_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← L1.integral_eq,L1.integral_eq_integral]
  exact (traceMass (H := K)).integral_comp_L1_comm (q.snd i) |>.symm

/-- The positive cq norm is its actual total real trace mass. -/
theorem norm_eq_mass {μ : Measure X} (q : Output H K ι μ) (hq : Positive q) :
    ‖q‖ = mass q := by
  rw [WithLp.prod_norm_eq_of_L1,PiLp.norm_eq_of_L1,mass_apply,positive_norm _ hq.1]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae ((hq.2 i).mono (fun t ht => positive_norm _ ht))

/-- Form a cq output from genuine Bochner-integrable record densities. -/
def pack (μ : Measure X) (s : TraceClass H) (f : ι → X → TraceClass K)
    (hf : ∀ i, Integrable (f i) μ) : Output H K ι μ :=
  WithLp.toLp 1 (s, WithLp.toLp 1 (fun i => (hf i).toL1 (f i)))

private theorem pack_norm (μ : Measure X) (s : TraceClass H) (f : ι → X → TraceClass K)
    (hf : ∀ i, Integrable (f i) μ) :
    ‖pack μ s f hf‖ = ‖s‖ + ∑ i, ∫ t, ‖f i t‖ ∂μ := by
  rw [WithLp.prod_norm_eq_of_L1,PiLp.norm_eq_of_L1]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => L1.norm_of_fun_eq_integral_norm (hf i))

private theorem pack_positive (μ : Measure X) (s : TraceClass H) (f : ι → X → TraceClass K)
    (hf : ∀ i, Integrable (f i) μ) (hs : 0 ≤ s.1)
    (hp : ∀ i t, 0 ≤ (f i t).1) : Positive (pack μ s f hf) := by
  refine ⟨hs,fun i => ?_⟩
  filter_upwards [(hf i).coeFn_toL1] with t ht
  change 0 ≤ (((hf i).toL1 (f i)) t).1
  rw [ht]
  exact hp i t

private theorem jordan (s : TraceClass H) (hs : IsSelfAdjoint s.1) :
    ∃ p n : TraceClass H, 0 ≤ p.1 ∧ 0 ≤ n.1 ∧ s = p - n ∧
      ‖p‖ + ‖n‖ = ‖s‖ := by
  let p := TraceClass.ofOperator s.1⁺
    (isTraceClass_posPart_of_isSelfAdjoint hs (TraceClass.isTraceClass_coe s))
  let n := TraceClass.ofOperator s.1⁻
    (isTraceClass_negPart_of_isSelfAdjoint hs (TraceClass.isTraceClass_coe s))
  refine ⟨p,n,CFC.posPart_nonneg _,CFC.negPart_nonneg _,?_,?_⟩
  · exact Subtype.ext (CFC.posPart_sub_negPart s.1 hs).symm
  · obtain ⟨w,b,_⟩ := exists_hilbertBasis ℂ H
    have hp := summable_inner_abs_of_hilbertBasis (TraceClass.isTraceClass_coe p) b
    have hn := summable_inner_abs_of_hilbertBasis (TraceClass.isTraceClass_coe n) b
    simp only [p,n,TraceClass.ofOperator_coe,CFC.abs_of_nonneg _ (CFC.posPart_nonneg _),
      CFC.abs_of_nonneg _ (CFC.negPart_nonneg _)] at hp hn
    simp only [TraceClass.norm_eq_traceNorm]
    rw [traceNorm_eq_of_hilbertBasis _ b,traceNorm_eq_of_hilbertBasis _ b,
      traceNorm_eq_of_hilbertBasis _ b]
    simp only [p,n,TraceClass.ofOperator_coe,CFC.abs_of_nonneg _ (CFC.posPart_nonneg _),
      CFC.abs_of_nonneg _ (CFC.negPart_nonneg _)]
    rw [← hp.tsum_add hn]
    apply tsum_congr
    intro i
    rw [← Complex.add_re,← inner_add_right,← add_apply,
      CFC.posPart_add_negPart s.1 hs]

/-- Fixed positive record blocks admit an exact norming decomposition even when the record
space or the Hilbert spaces are nonseparable. No operator-valued Jordan measurability is used. -/
theorem fixed_block_decomposition (μ : Measure X) (s : TraceClass H)
    (hs : IsSelfAdjoint s.1) (A : ι → TraceClass K) (hA : ∀ i, 0 ≤ (A i).1)
    (h : ι → X → ℝ) (hh : ∀ i, Integrable (h i) μ) :
    let f := fun i t => h i t • A i
    let hf := fun i => (hh i).smul_const (A i)
    ∃ P N : Output H K ι μ, Positive P ∧ Positive N ∧
      pack μ s f hf = P - N ∧ mass P + mass N = ‖pack μ s f hf‖ := by
  dsimp only
  obtain ⟨p,n,hp,hn,hsplit,hnorm⟩ := jordan s hs
  let fp : ι → X → TraceClass K := fun i t => max (h i t) 0 • A i
  let fn : ι → X → TraceClass K := fun i t => max (-h i t) 0 • A i
  have hip : ∀ i, Integrable (fp i) μ := fun i => (hh i).pos_part.smul_const (A i)
  have hin : ∀ i, Integrable (fn i) μ := fun i => (hh i).neg_part.smul_const (A i)
  let P := pack μ p fp hip
  let N := pack μ n fn hin
  have hP : Positive P := pack_positive μ p fp hip hp (fun i t => by
    change 0 ≤ max (h i t) 0 • (A i).1
    exact smul_nonneg (le_max_right _ _) (hA i))
  have hN : Positive N := pack_positive μ n fn hin hn (fun i t => by
    change 0 ≤ max (-h i t) 0 • (A i).1
    exact smul_nonneg (le_max_right _ _) (hA i))
  refine ⟨P,N,hP,hN,?_,?_⟩
  · apply (WithLp.equiv 1 _).injective
    apply Prod.ext
    · exact hsplit
    · apply (WithLp.equiv 1 _).injective
      funext i
      apply Lp.ext
      filter_upwards [((hh i).smul_const (A i)).coeFn_toL1,
        Lp.coeFn_sub (hip i |>.toL1 (fp i)) (hin i |>.toL1 (fn i)),
        (hip i).coeFn_toL1,(hin i).coeFn_toL1] with t ht he hpt hnt
      change (((hh i).smul_const (A i)).toL1 (fun t => h i t • A i)) t =
        (((hip i).toL1 (fp i)) - ((hin i).toL1 (fn i))) t
      rw [ht,he,Pi.sub_apply,hpt,hnt]
      dsimp [fp,fn]
      rw [← sub_smul]
      congr 1
      by_cases hz : 0 ≤ h i t
      · simp [max_eq_left hz,max_eq_right (neg_nonpos.mpr hz)]
      · have hz' : h i t ≤ 0 := le_of_not_ge hz
        simp [max_eq_right hz',max_eq_left (neg_nonneg.mpr hz')]
  · rw [← norm_eq_mass P hP,← norm_eq_mass N hN]
    rw [pack_norm,pack_norm,pack_norm]
    have hi : ∀ i, (∫ t, ‖fp i t‖ ∂μ) + (∫ t, ‖fn i t‖ ∂μ) =
        ∫ t, ‖h i t • A i‖ ∂μ := by
      intro i
      rw [← integral_add (hip i).norm (hin i).norm]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by
        by_cases hz : 0 ≤ h i t
        · simp [fp,fn,norm_smul,Real.norm_eq_abs,max_eq_left hz,
            max_eq_right (neg_nonpos.mpr hz)]
        · have hz' : h i t ≤ 0 := le_of_not_ge hz
          simp [fp,fn,norm_smul,Real.norm_eq_abs,max_eq_right hz',
            max_eq_left (neg_nonneg.mpr hz')])
    calc
      ‖p‖ + ∑ i, ∫ t, ‖fp i t‖ ∂μ + (‖n‖ + ∑ i, ∫ t, ‖fn i t‖ ∂μ) =
          (‖p‖ + ‖n‖) + ∑ i, ((∫ t, ‖fp i t‖ ∂μ) + ∫ t, ‖fn i t‖ ∂μ) := by
            rw [Finset.sum_add_distrib]; ring
      _ = _ := by rw [hnorm]; simp_rw [hi]

/-- A single positive mass-nonincreasing real-linear action contracts these actual differences.
No operator norm bound or contraction premise is part of the map laws. -/
theorem fixed_block_contracts {W : Type*} [SeminormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure X) (s : TraceClass H) (hs : IsSelfAdjoint s.1)
    (A : ι → TraceClass K) (hA : ∀ i, 0 ≤ (A i).1)
    (h : ι → X → ℝ) (hh : ∀ i, Integrable (h i) μ)
    (D : W → Prop) (v : W → ℝ) (hv : ∀ w, D w → ‖w‖ = v w)
    (Φ : Output H K ι μ →ₗ[ℝ] W)
    (hΦ : ∀ q, Positive q → D (Φ q) ∧ v (Φ q) ≤ mass q) :
    ‖Φ (pack μ s (fun i t => h i t • A i) (fun i => (hh i).smul_const (A i)))‖ ≤
      ‖pack μ s (fun i t => h i t • A i) (fun i => (hh i).smul_const (A i))‖ := by
  obtain ⟨P,N,hP,hN,he,hm⟩ := fixed_block_decomposition μ s hs A hA h hh
  rw [he,map_sub]
  calc
    ‖Φ P - Φ N‖ ≤ ‖Φ P‖ + ‖Φ N‖ := norm_sub_le _ _
    _ = v (Φ P) + v (Φ N) := by rw [hv _ (hΦ P hP).1,hv _ (hΦ N hN).1]
    _ ≤ mass P + mass N := add_le_add (hΦ P hP).2 (hΦ N hN).2
    _ = ‖P - N‖ := by rw [← he]; exact hm

end TraceClassRecordedOutput
