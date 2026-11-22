/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformCompactGraph
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformCompactGraph
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Compact graph of periodic bond-two projectors. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformTraceAmplitude
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformTracePowerSimpleRoots
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreLocalization
import D5.S3.Quantum.TensorNetworks.PeriodicMPSProjectiveCoordinates
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Algebra.Module.Cardinality
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSRegularComplement
import Mathlib.Topology.Sequences

/-! Compact graph of the literal periodic amplitude in weight-two coordinates, and its trace-one chart. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformCompactGraph

open Set Filter Function Polynomial PeriodicMPSProjectiveCoordinates
open SevenSiteTraceBase (Bond Word amplitudeOfLength amplitudeOfLength_actual
  amplitudeOfLength_scale differentiable_amplitudeOfLength)
open PeriodicMPSUniformTraceBase (amplitude_first_eq_zero_iff normalizedTracePower
  normalizedTracePower_eq_tracePowerPolynomial)
open UniformMPSExpectedDimensionRefutation (traceWord)
open PeriodicMPSFiveSiteCoordinates (exists_trace_coordinates)
open scoped Topology Matrix.Norms.Elementwise ComplexConjugate

noncomputable section

abbrev Invariants := Fin 5 → ℂ
abbrev StateMatrix (n : ℕ) := Matrix (Word n) (Word n) ℂ
abbrev Ambient (n : ℕ) := Matrix (Fin 6) (Fin 6) ℂ × StateMatrix n

variable {n : ℕ}

/-- Weight-two coordinates (t², ts, s², d, e, k) of a trace tuple. -/
def weighted (p : Invariants) : Fin 6 → ℂ :=
  ![p 0 ^ 2, p 0 * p 1, p 1 ^ 2, p 2, p 3, p 4]

def rescale (c : ℂ) (p : Invariants) : Invariants :=
  ![c * p 0,c * p 1,c^2 * p 2,c^2 * p 3,c^2 * p 4]

theorem weighted_rescale (c : ℂ) (p : Invariants) :
    weighted (rescale c p) = c^2 • weighted p := by
  funext i
  fin_cases i <;> simp [weighted, rescale, Pi.smul_apply, smul_eq_mul] <;> ring

theorem amplitude_rescale (n : ℕ) (c : ℂ) (p : Invariants) :
    amplitudeOfLength n (rescale c p) = c ^ n • amplitudeOfLength n p := by
  have h : (![p 0,p 1,p 2,p 3,p 4] : Invariants) = p := by
    funext i
    fin_cases i <;> rfl
  simpa only [rescale, h] using amplitudeOfLength_scale n c (p 0) (p 1) (p 2) (p 3) (p 4)

def graph (n : ℕ) (p : Invariants) : Ambient n :=
  (projector (weighted p), projector (amplitudeOfLength n p))

theorem graph_rescale (c : ℂ) (p : Invariants) (hc : c ≠ 0) :
    graph n (rescale c p) = graph n p := by
  simp only [graph, weighted_rescale, amplitude_rescale, projector_scale _ (pow_ne_zero _ hc)]

def defined (n : ℕ) : Set Invariants := {p | amplitudeOfLength n p ≠ 0}

/-- The closure of the graph over the nonzero trace-word amplitudes. -/
def source (n : ℕ) : Set (Ambient n) := closure (graph n '' defined n)

theorem graph_mem {p : Invariants} (hp : amplitudeOfLength n p ≠ 0) : graph n p ∈ source n :=
  subset_closure ⟨p,hp,rfl⟩

theorem weighted_eq_zero {p : Invariants} (h : weighted p = 0) : p = 0 := by
  funext i
  fin_cases i
  · exact sq_eq_zero_iff.mp (congrFun h 0)
  · exact sq_eq_zero_iff.mp (congrFun h 2)
  · exact congrFun h 3
  · exact congrFun h 4
  · exact congrFun h 5

private theorem amplitude_zero (hn : 0 < n) : amplitudeOfLength n (0 : Invariants) = 0 := by
  have h : rescale 0 (0 : Invariants) = 0 := by
    funext i
    fin_cases i <;> simp [rescale]
  simpa only [h, zero_pow hn.ne', zero_smul] using amplitude_rescale n 0 0

private theorem weighted_ne_zero (hn : 0 < n) {p : Invariants}
    (hp : amplitudeOfLength n p ≠ 0) : weighted p ≠ 0 := by
  intro hw
  exact hp ((congrArg (amplitudeOfLength n) (weighted_eq_zero hw)).trans (amplitude_zero hn))

theorem source_projective (hn : 0 < n) :
    source n ⊆ projective (ι := Fin 6) ×ˢ projective (ι := Word n) := by
  apply closure_minimal _ (isCompact_projective.prod isCompact_projective).isClosed
  rintro _ ⟨p,hp,rfl⟩
  exact ⟨projector_mem _ (weighted_ne_zero hn hp),projector_mem _ hp⟩

theorem source_isCompact (hn : 0 < n) : IsCompact (source n) :=
  (isCompact_projective.prod isCompact_projective).of_isClosed_subset isClosed_closure (source_projective hn)

theorem continuous_weighted : Continuous weighted := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [weighted] <;> fun_prop

theorem continuous_amplitude (n : ℕ) : Continuous (amplitudeOfLength (R := ℂ) n) :=
  (differentiable_amplitudeOfLength (𝕜 := ℂ) n).continuous

theorem continuousAt_graph (hn : 0 < n) {p : Invariants} (hp : amplitudeOfLength n p ≠ 0) : ContinuousAt (graph n) p :=
  ((continuousAt_projector (weighted_ne_zero hn hp)).comp continuous_weighted.continuousAt).prodMk
    ((continuousAt_projector hp).comp (continuous_amplitude n).continuousAt)

theorem continuousOn_graph (hn : 0 < n) : ContinuousOn (graph n) (defined n) :=
  fun _ hp => (continuousAt_graph hn hp).continuousWithinAt

theorem graph_actual (n : ℕ) (A : Fin 2 → Bond ℂ) :
    graph n ![(A 0).trace,(A 1).trace,(A 0).det,(A 1).det,(A 0*A 1).trace] =
      (projector ![(A 0).trace^2,(A 0).trace*(A 1).trace,(A 1).trace^2,
        (A 0).det,(A 1).det,(A 0*A 1).trace], projector (traceWord 2 2 n A)) := by
  unfold graph
  rw [amplitudeOfLength_actual n]
  rfl

/-- Projectors of the nonzero states of actual binary bond-two cores. -/
def actualProjectors (n : ℕ) : Set (StateMatrix n) :=
  (fun A : Fin 2 → Bond ℂ => projector (traceWord 2 2 n A)) ''
    {A | traceWord 2 2 n A ≠ 0}

/-- The compact physical projector image at period `n`. -/
def physical (n : ℕ) : Set (StateMatrix n) := closure (actualProjectors n)

theorem actualProjectors_eq_hardCore (m : ℕ) :
    actualProjectors (2 + m) = PeriodicMPSUniformHardCoreLocalization.actualProjectors m := rfl

/-- The second projection before taking closure is the actual nonzero projector image. -/
theorem image_graph_snd (n : ℕ) :
    Prod.snd '' (graph n '' defined n) = actualProjectors n := by
  ext P
  constructor
  · rintro ⟨_,⟨p,hp,rfl⟩,rfl⟩
    obtain ⟨A,ht,hs,hd,he,hk⟩ := exists_trace_coordinates (p 0) (p 1) (p 2) (p 3) (p 4)
    have hcoords : (![(A 0).trace, (A 1).trace, (A 0).det, (A 1).det,
        (A 0 * A 1).trace] : Invariants) = p := by
      funext i
      fin_cases i <;> assumption
    have h : amplitudeOfLength n p = traceWord 2 2 n A := by
      rw [← hcoords]
      exact amplitudeOfLength_actual n A
    refine ⟨A, ?_, (congrArg projector h).symm⟩
    change traceWord 2 2 n A ≠ 0
    rwa [← h]
  · rintro ⟨A,hA,rfl⟩
    let p : Invariants := ![(A 0).trace,(A 1).trace,(A 0).det,(A 1).det,(A 0*A 1).trace]
    have h : amplitudeOfLength n p = traceWord 2 2 n A := amplitudeOfLength_actual n A
    refine ⟨graph n p, ⟨p, ?_, rfl⟩, congrArg projector h⟩
    change amplitudeOfLength n p ≠ 0
    rwa [h]

theorem image_source_snd (hn : 0 < n) : Prod.snd '' source n = physical n := by
  rw [physical, ← image_graph_snd]
  apply Subset.antisymm
  · exact image_closure_subset_closure_image continuous_snd
  · apply closure_minimal (image_mono subset_closure)
    exact ((source_isCompact hn).image continuous_snd).isClosed

theorem physical_isCompact (hn : 0 < n) : IsCompact (physical n) := by
  rw [← image_source_snd hn]
  exact (source_isCompact hn).image continuous_snd

/-- Forget the trace coordinates and retain the physical projector. -/
def physicalProjection (hn : 0 < n) (x : source n) : physical n :=
  ⟨x.val.2, image_source_snd hn ▸ ⟨x.val, x.property, rfl⟩⟩

theorem continuous_physicalProjection (hn : 0 < n) : Continuous (physicalProjection hn) :=
  (continuous_snd.comp continuous_subtype_val).subtype_mk _

theorem surjective_physicalProjection (hn : 0 < n) : Surjective (physicalProjection hn) := by
  intro P
  have hP : P.val ∈ Prod.snd '' source n := by
    simpa only [image_source_snd hn] using P.property
  obtain ⟨x, hx, he⟩ := hP
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

private theorem unit_weight_representative (hn : 0 < n) {p : Invariants} (hp : amplitudeOfLength n p ≠ 0) :
    ∃ q, ‖weighted q‖ = 1 ∧ amplitudeOfLength n q ≠ 0 ∧ graph n q = graph n p := by
  have hw := weighted_ne_zero hn hp
  let r : ℂ := ↑‖weighted p‖
  have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)
  obtain ⟨c,hc⟩ := IsAlgClosed.exists_pow_nat_eq r⁻¹ (n := 2) (by decide)
  have hcn : c ≠ 0 := by
    intro h
    exact (inv_ne_zero hr) (by simpa [h] using hc.symm)
  refine ⟨rescale c p, ?_, ?_, graph_rescale c p hcn⟩
  · rw [weighted_rescale, norm_smul, hc, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
  · rw [amplitude_rescale]
    exact smul_ne_zero (pow_ne_zero _ hcn) hp

private theorem unit_weight_in_ball {p : Invariants} (hp : ‖weighted p‖ = 1) :
    p ∈ Metric.closedBall 0 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
  have hb (i : Fin 6) : ‖weighted p i‖ ≤ 1 := hp ▸ norm_le_pi_norm (weighted p) i
  intro i
  fin_cases i
  · have h : ‖p 0‖^2 ≤ 1 := by simpa only [weighted, Matrix.cons_val_zero, norm_pow] using hb 0
    change ‖p 0‖ ≤ 1
    nlinarith [norm_nonneg (p 0)]
  · have h : ‖p 1‖^2 ≤ 1 := by simpa [weighted, norm_pow] using hb 2
    change ‖p 1‖ ≤ 1
    nlinarith [norm_nonneg (p 1)]
  · exact hb 3
  · exact hb 4
  · exact hb 5

/-- Every point of the compact graph has an approximating sequence
with convergent, bounded representatives in literal trace coordinates. -/
theorem exists_lift_sequence (hn : 0 < n) {x : Ambient n} (hx : x ∈ source n) :
    ∃ (p : ℕ → Invariants) (q : Invariants),
      (∀ j, amplitudeOfLength n (p j) ≠ 0 ∧ ‖weighted (p j)‖ = 1 ∧
        p j ∈ Metric.closedBall 0 1) ∧ ‖weighted q‖ = 1 ∧
      Tendsto p atTop (𝓝 q) ∧ Tendsto (graph n ∘ p) atTop (𝓝 x) ∧ x.1 = projector (weighted q) := by
  let _ : FirstCountableTopology (Ambient n) :=
    inferInstanceAs (FirstCountableTopology ((Fin 6 → Fin 6 → ℂ) × (Word n → Word n → ℂ)))
  obtain ⟨X,hX,hlim⟩ := mem_closure_iff_seq_limit.mp hx
  have h (j : ℕ) : ∃ p : Invariants,
      ‖weighted p‖ = 1 ∧ amplitudeOfLength n p ≠ 0 ∧ graph n p = X j := by
    obtain ⟨q,hq,hXq⟩ := hX j
    rw [← hXq]
    exact unit_weight_representative hn hq
  choose p hw hp hgraph using h
  obtain ⟨q,_,φ,hφ,hlimq⟩ := (isCompact_closedBall (0 : Invariants) 1).tendsto_subseq
    (fun n => unit_weight_in_ball (hw n))
  have hlimX : Tendsto (graph n ∘ (p ∘ φ)) atTop (𝓝 x) := by
    simpa only [comp_def, hgraph] using hlim.comp hφ.tendsto_atTop
  have hqw : ‖weighted q‖ = 1 := by
    apply tendsto_nhds_unique
      ((continuous_norm.comp continuous_weighted).continuousAt.tendsto.comp hlimq)
    simpa only [comp_def, hw] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hne : weighted q ≠ 0 := by
    intro he
    simp [he] at hqw
  refine ⟨p ∘ φ,q,fun j => ⟨hp (φ j), hw (φ j), unit_weight_in_ball (hw (φ j))⟩,hqw,hlimq,hlimX,?_⟩
  exact tendsto_nhds_unique (continuous_fst.continuousAt.tendsto.comp hlimX)
    (((continuousAt_projector hne).comp continuous_weighted.continuousAt).tendsto.comp hlimq)

theorem eq_graph_of_lift (hn : 0 < n) {x : Ambient n} (hx : x ∈ source n) {q : Invariants}
    (hq : amplitudeOfLength n q ≠ 0) (hP : x.1 = projector (weighted q)) : x = graph n q := by
  obtain ⟨_, r, _, _, hl, hx', hR⟩ := exists_lift_sequence hn hx
  have hmul : ∃ c : ℂ, c ≠ 0 ∧ weighted r = c • weighted q :=
    eq_smul_of_projector_eq (weighted_ne_zero hn hq) (hP.symm.trans hR)
  obtain ⟨c,hc,hcR⟩ := hmul
  obtain ⟨a,ha⟩ := IsAlgClosed.exists_pow_nat_eq c (n := 2) (by decide)
  have ha' : a ≠ 0 := fun h => hc (by simpa [h] using ha.symm)
  have hw : weighted r = weighted (rescale a q) := by rw [weighted_rescale, ha, hcR]
  have hsame {u v : Invariants} (h : weighted u = weighted v) :
      u = v ∨ u = rescale (-1) v := by
    have h₀ : u 0 ^ 2 = v 0 ^ 2 := congrFun h 0
    have h₁ : u 0 * u 1 = v 0 * v 1 := congrFun h 1
    have h₂ : u 1 ^ 2 = v 1 ^ 2 := congrFun h 2
    have h₃ : u 2 = v 2 := congrFun h 3
    have h₄ : u 3 = v 3 := congrFun h 4
    have h₅ : u 4 = v 4 := congrFun h 5
    have hsq (s t : ℂ) (h : s^2 = t^2) : s = t ∨ s = -t := by
      have hh : (s-t)*(s+t)=0 := by linear_combination h
      rcases mul_eq_zero.mp hh with hh | hh
      · exact Or.inl (sub_eq_zero.mp hh)
      · exact Or.inr (eq_neg_of_add_eq_zero_left hh)
    have he : (u 0 = v 0 ∧ u 1 = v 1) ∨ (u 0 = -v 0 ∧ u 1 = -v 1) := by
      by_cases hv : v 0 = 0
      · have hu : u 0 = 0 := sq_eq_zero_iff.mp (by simpa [hv] using h₀)
        rcases hsq _ _ h₂ with hpos | hneg
        · exact Or.inl ⟨hu.trans hv.symm, hpos⟩
        · exact Or.inr ⟨by simp [hu,hv], hneg⟩
      · rcases hsq _ _ h₀ with hpos | hneg
        · refine Or.inl ⟨hpos, mul_left_cancel₀ hv ?_⟩
          simpa [hpos] using h₁
        · refine Or.inr ⟨hneg, mul_left_cancel₀ (neg_ne_zero.mpr hv) ?_⟩
          simpa [hneg] using h₁
    rcases he with ⟨h₀',h₁'⟩ | ⟨h₀',h₁'⟩
    · exact Or.inl (by funext i; fin_cases i <;> assumption)
    · refine Or.inr (by funext i; fin_cases i <;>
        simp [rescale,h₀',h₁',h₃,h₄,h₅])
  rcases hsame hw with he | he
  · have hrn : amplitudeOfLength n r ≠ 0 := by
      rw [he, amplitude_rescale]
      exact smul_ne_zero (pow_ne_zero _ ha') hq
    rw [tendsto_nhds_unique hx' ((continuousAt_graph hn hrn).tendsto.comp hl), he,
      graph_rescale a q ha']
  · have hrn : amplitudeOfLength n r ≠ 0 := by
      rw [he, amplitude_rescale, amplitude_rescale]
      exact smul_ne_zero (pow_ne_zero _ (by norm_num)) (smul_ne_zero (pow_ne_zero _ ha') hq)
    rw [tendsto_nhds_unique hx' ((continuousAt_graph hn hrn).tendsto.comp hl), he,
      graph_rescale _ _ (by norm_num), graph_rescale a q ha']


abbrev Parameters := Fin 4 → ℂ
abbrev Source (n : ℕ) := ↥(source n)

def traceChart (u : Parameters) : Invariants := ![1,u 0,u 1,u 2,u 3]
def chartDomain (n : ℕ) : Set Parameters := {u | amplitudeOfLength n (traceChart u) ≠ 0}

theorem continuous_traceChart : Continuous traceChart := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [traceChart] <;> fun_prop

private theorem traceChart_normalize {p : Invariants} (hp : p 0 ≠ 0) :
    ∃ u : Parameters, traceChart u = rescale (p 0)⁻¹ p := by
  let r := rescale (p 0)⁻¹ p
  refine ⟨![r 1, r 2, r 3, r 4], ?_⟩
  funext i
  fin_cases i <;> simp [traceChart, r, rescale, hp]

theorem isOpen_chartDomain (n : ℕ) : IsOpen (chartDomain n) :=
  isOpen_ne.preimage ((continuous_amplitude n).comp continuous_traceChart)

def decode (x : Ambient n) : Parameters :=
  ![x.1 1 0 / x.1 0 0, x.1 3 0 / x.1 0 0, x.1 4 0 / x.1 0 0, x.1 5 0 / x.1 0 0]

theorem continuousAt_decode {x : Ambient n} (hx : x.1 0 0 ≠ 0) : ContinuousAt decode x := by
  have c (i : Fin 6) : Continuous (fun y : Ambient n => y.1 i 0) :=
    (continuous_apply 0).comp ((continuous_apply i).comp continuous_fst)
  apply continuousAt_pi.mpr
  intro j
  fin_cases j
  · exact (c 1).continuousAt.div (c 0).continuousAt hx
  · exact (c 3).continuousAt.div (c 0).continuousAt hx
  · exact (c 4).continuousAt.div (c 0).continuousAt hx
  · exact (c 5).continuousAt.div (c 0).continuousAt hx

def ordinary (n : ℕ) : Set (Ambient n) := {x | x.1 0 0 ≠ 0 ∧ decode x ∈ chartDomain n}

theorem isOpen_ordinary (n : ℕ) : IsOpen (ordinary n) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have c : Continuous (fun y : Ambient n => y.1 0 0) :=
    (continuous_apply 0).comp ((continuous_apply 0).comp continuous_fst)
  have hdiag : ∀ᶠ y in 𝓝 x, y.1 0 0 ≠ 0 :=
    c.continuousAt (isOpen_ne.mem_nhds hx.1)
  have hdecode : ∀ᶠ y in 𝓝 x, decode y ∈ chartDomain n :=
    continuousAt_decode hx.1 ((isOpen_chartDomain n).mem_nhds hx.2)
  exact hdiag.and hdecode

private theorem decode_chart {x : Ambient n} {u : Parameters}
    (hx : x.1 = projector (weighted (traceChart u))) : decode x = u := by
  have h₀ : weighted (traceChart u) 0 = 1 := by simp [weighted,traceChart]
  have h (j : Fin 6) : x.1 j 0 / x.1 0 0 = weighted (traceChart u) j := by
    rw [hx, projector_ratio _ j 0 (by simp [h₀]), h₀, div_one]
  funext j
  fin_cases j <;> simp [decode,h,weighted,traceChart]

private theorem chart_round_trip (hn : 0 < n) {x : Ambient n} (hx : x ∈ source n) (ho : x ∈ ordinary n) :
    graph n (traceChart (decode x)) = x := by
  obtain ⟨_,q,_,_,_,_,hP⟩ := exists_lift_sequence hn hx
  have hq0 : q 0 ≠ 0 := by
    have hn : projector (weighted q) 0 0 ≠ 0 := by
      rw [← hP]
      exact ho.1
    intro h
    exact (projector_diag_ne_zero_iff (weighted q) 0).mp hn (by simp [weighted, h])
  obtain ⟨u, hr⟩ := traceChart_normalize hq0
  have hPx : x.1 = projector (weighted (traceChart u)) := by
    rw [hr, weighted_rescale, projector_scale _ (pow_ne_zero _ (inv_ne_zero hq0))]
    exact hP
  have hd := decode_chart hPx
  rw [hd]
  have hu : amplitudeOfLength n (traceChart u) ≠ 0 := by
    have hn := ho.2
    rwa [hd] at hn
  exact (eq_graph_of_lift hn hx hu hPx).symm

theorem chart_mem_ordinary {u : Parameters} (hu : u ∈ chartDomain n) :
    graph n (traceChart u) ∈ ordinary n := by
  constructor
  · exact (projector_diag_ne_zero_iff _ _).2 (by simp [weighted,traceChart])
  · rw [decode_chart rfl]
    exact hu

theorem image_traceChart (hn : 0 < n) :
    (graph n ∘ traceChart) '' chartDomain n = source n ∩ ordinary n := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨graph_mem hu,chart_mem_ordinary hu⟩
  · rintro ⟨hx,ho⟩
    exact ⟨decode x,ho.2,chart_round_trip hn hx ho⟩

theorem closure_ordinary (hn : 0 < n) : closure (source n ∩ ordinary n) = source n := by
  apply Subset.antisymm (closure_minimal inter_subset_left isClosed_closure)
  apply closure_minimal _ isClosed_closure
  rintro _ ⟨p,hp,rfl⟩
  let S : Set Invariants := {p | p 0 ≠ 0} ∩ defined n
  have hDense : Dense ({p : Invariants | p 0 ≠ 0}) := by
    exact (dense_compl_singleton (0 : ℂ)).preimage (isOpenMap_eval 0)
  have hOpen : IsOpen (defined n) := isOpen_ne.preimage (continuous_amplitude n)
  have hpcl : p ∈ closure S := by
    rw [mem_closure_iff]
    intro U hU hpU
    obtain ⟨q,hq,hn⟩ := hDense.inter_open_nonempty (U ∩ defined n)
      (hU.inter hOpen) ⟨p,hpU,hp⟩
    exact ⟨q,hq.1,hn,hq.2⟩
  have hcl := (continuousAt_graph hn hp).continuousWithinAt.mem_closure_image hpcl
  apply closure_mono _ hcl
  rintro _ ⟨q,⟨hq0,hq⟩,rfl⟩
  change q 0 ≠ 0 at hq0
  obtain ⟨u, hr⟩ := traceChart_normalize hq0
  have hu : u ∈ chartDomain n := by
    change amplitudeOfLength n (traceChart u) ≠ 0
    rw [hr, amplitude_rescale]
    exact smul_ne_zero (pow_ne_zero _ (inv_ne_zero hq0)) hq
  change graph n q ∈ source n ∩ ordinary n
  rw [← image_traceChart hn]
  exact ⟨u, hu, (congrArg (graph n) hr).trans (graph_rescale _ _ (inv_ne_zero hq0))⟩

abbrev VacuumRoot (n : ℕ) := {a : ℂ // (normalizedTracePower n).IsRoot a}

theorem normalizedTracePower_eval_zero (n : ℕ) (hn : 0 < n) :
    (normalizedTracePower n).eval 0 = 1 := by
  rw [normalizedTracePower_eq_tracePowerPolynomial]
  let power := PeriodicMPSUniformHardCoreBaseLocus.tracePowerPolynomial
  have h (m : ℕ) : (power 1 (m + 1)).eval 0 = 1 := by
    induction m with
    | zero => simp [power, PeriodicMPSUniformHardCoreBaseLocus.tracePowerPolynomial]
    | succ m ih =>
      change (C 1 * power 1 (m + 1) - X * power 1 m).eval 0 = 1
      simp only [eval_sub, eval_mul, eval_C, eval_X, zero_mul, sub_zero, one_mul, ih]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact h m

theorem finite_vacuum (n : ℕ) (hn : 0 < n) :
    Set.Finite {a : ℂ | (normalizedTracePower n).IsRoot a} := by
  apply Polynomial.finite_setOfPred_isRoot
  intro h
  have h' := normalizedTracePower_eval_zero n hn
  simp [h] at h'

theorem chartDomain_compl (hn : 2 ≤ n) (u : Parameters) :
    u ∈ (chartDomain n)ᶜ ↔
      (normalizedTracePower n).IsRoot (u 1) ∧
        u 2 = u 1 * u 0 ^ 2 ∧ u 3 = (1 - 2 * u 1) * u 0 := by
  rw [mem_compl_iff]
  change (¬ amplitudeOfLength n (traceChart u) ≠ 0) ↔ _
  rw [not_ne_iff]
  exact amplitude_first_eq_zero_iff n hn (u 0) (u 1) (u 2) (u 3)

theorem dense_chartDomain (hn : 2 ≤ n) : Dense (chartDomain n) := by
  have h : Dense ({a : ℂ | (normalizedTracePower n).IsRoot a}ᶜ) :=
    (finite_vacuum n (by omega)).countable.dense_compl ℂ
  apply (h.preimage (isOpenMap_eval (1 : Fin 4))).mono
  intro u hu
  by_contra hum
  exact hu ((chartDomain_compl hn u).mp hum).1

private theorem chartDomain_zero (n : ℕ) (hn : 2 ≤ n) : (0 : Parameters) ∈ chartDomain n := by
  change amplitudeOfLength n (![1, 0, 0, 0, 0] : Invariants) ≠ 0
  intro h
  have hroot := ((amplitude_first_eq_zero_iff n hn 0 0 0 0).mp h).1
  exact zero_ne_one (hroot.symm.trans (normalizedTracePower_eval_zero n (by omega)))

theorem isPathConnected_chartDomain (hn : 2 ≤ n) : IsPathConnected (chartDomain n) := by
  let f (a : VacuumRoot n) (s : ℂ) : Parameters :=
    ![s, a.val, a.val * s ^ 2, (1 - 2 * a.val) * s]
  let _ : Finite (VacuumRoot n) := finite_coe_iff.mpr (finite_vacuum n (by omega))
  let _ : Encodable (VacuumRoot n) := Encodable.ofCountable _
  let g := Function.extend (Encodable.encode : VacuumRoot n → ℕ) f (fun _ _ => 0)
  have hg (i : ℕ) : DifferentiableOn ℝ (g i) (univ : Set ℂ) := by
    by_cases hi : ∃ a : VacuumRoot n, Encodable.encode a = i
    · obtain ⟨a,rfl⟩ := hi
      rw [show g (Encodable.encode a) = f a from Encodable.encode_injective.extend_apply _ _ _]
      apply Differentiable.differentiableOn
      apply differentiable_pi.mpr
      intro j
      fin_cases j <;> simp [f]
      fun_prop
    · rw [show g i = (fun _ => 0) from Function.extend_apply' _ _ _ hi]
      exact differentiableOn_const (0 : Parameters)
  have hc : (chartDomain n)ᶜ ⊆ ⋃ i, g i '' (univ : Set ℂ) := by
    intro u hu
    obtain ⟨hd, he, hk⟩ := (chartDomain_compl hn u).mp hu
    let a : VacuumRoot n := ⟨u 1,hd⟩
    refine mem_iUnion.mpr ⟨Encodable.encode a, u 0, mem_univ _, ?_⟩
    rw [show g (Encodable.encode a) = f a from Encodable.encode_injective.extend_apply _ _ _]
    funext i
    fin_cases i <;> simp [f,a,he,hk]
  simpa only [compl_compl] using
    PeriodicMPSRegularComplement.isPathConnected_compl_of_smooth_cover _ _ _ hg hc
      (by norm_num [Parameters, Module.finrank_pi_fintype, Complex.finrank_real_complex])

theorem isPathConnected_ordinary (hn : 2 ≤ n) : IsPathConnected (source n ∩ ordinary n) := by
  have hn' : 0 < n := by omega
  rw [← image_traceChart hn']
  exact (isPathConnected_chartDomain hn).image' ((continuousOn_graph hn').comp
    continuous_traceChart.continuousOn fun _ hu => hu)

def boundary (n : ℕ) : Set (Ambient n) := source n \ ordinary n

theorem isCompact_boundary (hn : 0 < n) : IsCompact (boundary n) :=
  (source_isCompact hn).diff (isOpen_ordinary n)

open scoped Classical in
/-- The entire ordinary locus has a single affine chart. -/
def chart (hn : 2 ≤ n) : OpenPartialHomeomorph Parameters (Source n) where
  toFun u := if hu : u ∈ chartDomain n then ⟨graph n (traceChart u),graph_mem hu⟩
    else ⟨graph n (traceChart 0),graph_mem (chartDomain_zero n hn)⟩
  invFun x := decode x.val
  source := chartDomain n
  target := Subtype.val ⁻¹' ordinary n
  map_source' u hu := by
    rw [dite_eq_left hu]
    change graph n (traceChart u) ∈ ordinary n
    exact chart_mem_ordinary hu
  map_target' _ hx := hx.2
  left_inv' u hu := by simp only [dite_eq_left hu]; exact decode_chart rfl
  right_inv' x hx := by
    have hdecode : decode x.val ∈ chartDomain n := hx.2
    simp only [dite_eq_left hdecode]
    exact Subtype.ext (chart_round_trip (by omega) x.property hx)
  open_source := isOpen_chartDomain n
  open_target := (isOpen_ordinary n).preimage continuous_subtype_val
  continuousOn_toFun := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    have hc : ContinuousOn (graph n ∘ traceChart) (chartDomain n) :=
      (continuousOn_graph (by omega)).comp continuous_traceChart.continuousOn fun _ hu => hu
    apply hc.congr
    intro u hu
    simp only [Function.comp_apply, dite_eq_left hu]
  continuousOn_invFun := fun x hx =>
    ((continuousAt_decode hx.1).comp continuous_subtype_val.continuousAt).continuousWithinAt

/-- The trace-one parameters and the ordinary part of the compact graph are homeomorphic. -/
def traceOneHomeomorph (hn : 2 ≤ n) :
    (chartDomain n) ≃ₜ (Subtype.val ⁻¹' ordinary n : Set (Source n)) :=
  (chart hn).toHomeomorphSourceTarget

theorem chart_target_dense (hn : 2 ≤ n) : Dense (chart hn).target := by
  apply Subtype.dense_iff.mpr
  change source n ⊆ closure (Subtype.val '' (Subtype.val ⁻¹' ordinary n : Set (Source n)))
  simpa only [Subtype.image_preimage_val, closure_ordinary (show 0 < n by omega)] using (Subset.rfl : source n ⊆ source n)

theorem chart_target_pathConnected (hn : 2 ≤ n) : IsPathConnected (chart hn).target := by
  change IsPathConnected (Subtype.val ⁻¹' ordinary n : Set (Source n))
  have h := (isPathConnected_ordinary hn).preimage_coe (U := source n) inter_subset_left
  simpa only [preimage_inter, show (Subtype.val ⁻¹' source n : Set (Source n)) = univ from
    eq_univ_of_forall fun x => x.property, univ_inter] using h

/-- The normalized two-site marginal on the graph is the partial trace of its physical ray. -/
def observation (m : ℕ) (x : Source (2 + m)) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  PeriodicMPSUniformHardCoreLocalization.twoSiteObservation m x.val.2

theorem continuous_observation (m : ℕ) : Continuous (observation m) :=
  (PeriodicMPSUniformHardCoreLocalization.continuous_twoSiteObservation m).comp
    (continuous_snd.comp continuous_subtype_val)

theorem observation_actual (m : ℕ) (A : Fin 2 → Bond ℂ)
    (hA : traceWord 2 2 (2 + m) A ≠ 0) :
    let p : Invariants := ![(A 0).trace, (A 1).trace, (A 0).det, (A 1).det, (A 0 * A 1).trace]
    let hp : amplitudeOfLength (2 + m) p ≠ 0 := by
      simpa only [p, amplitudeOfLength_actual] using hA
    observation m ⟨graph (2 + m) p, graph_mem hp⟩ =
      PeriodicMPSUniformHardCoreLocalization.normalizedMarginal m A := by
  dsimp only [observation, graph]
  rw [amplitudeOfLength_actual]
  exact PeriodicMPSUniformHardCoreLocalization.twoSiteObservation_traceWord A

theorem compactSpace_source (hn : 0 < n) : CompactSpace (Source n) :=
  isCompact_iff_compactSpace.mp (source_isCompact hn)

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformCompactGraph
