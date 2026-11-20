/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCompactGraph
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCompactGraph
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: The ordinary chart of the compact seven-site trace graph. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteTraceBase
import D5.S3.Quantum.TensorNetworks.PeriodicMPSProjectiveCoordinates
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSRegularComplement
import Mathlib.Topology.Sequences

/-! Compact graph of the literal seven-site amplitude in the weight-two coordinates. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteCompactGraph

open Set Filter Function Polynomial SevenSiteTraceBase PeriodicMPSProjectiveCoordinates
open UniformMPSExpectedDimensionRefutation (traceWord)
open PeriodicMPSFiveSiteCoordinates (exists_trace_coordinates)
open scoped Topology Matrix.Norms.Elementwise ComplexConjugate

noncomputable section

abbrev Invariants := Fin 5 → ℂ
abbrev Ambient := Matrix (Fin 6) (Fin 6) ℂ × Matrix (Word 7) (Word 7) ℂ

def weighted (p : Invariants) : Fin 6 → ℂ :=
  ![p 0 ^ 2, p 0 * p 1, p 1 ^ 2, p 2, p 3, p 4]

def rescale (c : ℂ) (p : Invariants) : Invariants :=
  ![c * p 0,c * p 1,c^2 * p 2,c^2 * p 3,c^2 * p 4]

theorem weighted_rescale (c : ℂ) (p : Invariants) :
    weighted (rescale c p) = c^2 • weighted p := by
  funext i
  fin_cases i <;> simp [weighted, rescale, Pi.smul_apply, smul_eq_mul] <;> ring

theorem amplitude_rescale (c : ℂ) (p : Invariants) :
    amplitude (rescale c p) = c^7 • amplitude p := by
  have h : (![p 0,p 1,p 2,p 3,p 4] : Invariants) = p := by
    funext i
    fin_cases i <;> rfl
  simpa only [rescale, h] using amplitude_scale c (p 0) (p 1) (p 2) (p 3) (p 4)

def graph (p : Invariants) : Ambient := (projector (weighted p), projector (amplitude p))

theorem graph_rescale (c : ℂ) (p : Invariants) (hc : c ≠ 0) :
    graph (rescale c p) = graph p := by
  simp only [graph, weighted_rescale, amplitude_rescale, projector_scale _ (pow_ne_zero _ hc)]

def defined : Set Invariants := {p | amplitude p ≠ 0}
def source : Set Ambient := closure (graph '' defined)

theorem graph_mem {p : Invariants} (hp : amplitude p ≠ 0) : graph p ∈ source :=
  subset_closure ⟨p,hp,rfl⟩

theorem weighted_eq_zero {p : Invariants} (h : weighted p = 0) : p = 0 := by
  funext i
  fin_cases i
  · exact sq_eq_zero_iff.mp (congrFun h 0)
  · exact sq_eq_zero_iff.mp (congrFun h 2)
  · exact congrFun h 3
  · exact congrFun h 4
  · exact congrFun h 5

private theorem weighted_ne_zero {p : Invariants} (h : amplitude p ≠ 0) : weighted p ≠ 0 := by
  intro hp
  rw [weighted_eq_zero hp] at h
  have h₀ : traceBase (0 : Fin 3 → ℂ) = 0 := by
    funext i
    fin_cases i <;> rfl
  apply h
  rw [← h₀]
  exact amplitude_traceless 0 0 0

theorem source_projective :
    source ⊆ projective (ι := Fin 6) ×ˢ projective (ι := Word 7) := by
  apply closure_minimal _ (isCompact_projective.prod isCompact_projective).isClosed
  rintro _ ⟨p,hp,rfl⟩
  exact ⟨projector_mem _ (weighted_ne_zero hp),projector_mem _ hp⟩

theorem source_isCompact : IsCompact source :=
  (isCompact_projective.prod isCompact_projective).of_isClosed_subset isClosed_closure source_projective

theorem continuous_weighted : Continuous weighted := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [weighted] <;> fun_prop

theorem continuous_amplitude : Continuous (amplitude (R := ℂ)) :=
  (differentiable_amplitude (𝕜 := ℂ)).continuous

theorem continuousAt_graph {p : Invariants} (hp : amplitude p ≠ 0) : ContinuousAt graph p :=
  ((continuousAt_projector (weighted_ne_zero hp)).comp continuous_weighted.continuousAt).prodMk
    ((continuousAt_projector hp).comp continuous_amplitude.continuousAt)

theorem continuousOn_graph : ContinuousOn graph defined :=
  fun _ hp => (continuousAt_graph hp).continuousWithinAt

theorem graph_actual (A : Fin 2 → Bond ℂ) :
    graph ![(A 0).trace,(A 1).trace,(A 0).det,(A 1).det,(A 0*A 1).trace] =
      (projector ![(A 0).trace^2,(A 0).trace*(A 1).trace,(A 1).trace^2,
        (A 0).det,(A 1).det,(A 0*A 1).trace], projector (traceWord 2 2 7 A)) := by
  unfold graph
  rw [amplitude_actual]
  rfl

/-- The second projections of the graph before taking closure are exactly the actual
nonzero seven-site state projectors. -/
theorem image_graph_snd :
    Prod.snd '' (graph '' defined) =
      {P | ∃ A : Fin 2 → Bond ℂ, traceWord 2 2 7 A ≠ 0 ∧
        P = projector (traceWord 2 2 7 A)} := by
  ext P
  constructor
  · rintro ⟨_,⟨p,hp,rfl⟩,rfl⟩
    obtain ⟨A,ht,hs,hd,he,hk⟩ := exists_trace_coordinates (p 0) (p 1) (p 2) (p 3) (p 4)
    have hcoords : (![(A 0).trace, (A 1).trace, (A 0).det, (A 1).det,
        (A 0 * A 1).trace] : Invariants) = p := by
      funext i
      fin_cases i <;> assumption
    have h : amplitude p = traceWord 2 2 7 A := by
      rw [← hcoords]
      exact amplitude_actual A
    refine ⟨A, ?_, congrArg projector h⟩
    rw [← h]
    exact hp
  · rintro ⟨A,hA,rfl⟩
    let p : Invariants := ![(A 0).trace,(A 1).trace,(A 0).det,(A 1).det,(A 0*A 1).trace]
    have h : amplitude p = traceWord 2 2 7 A := amplitude_actual A
    refine ⟨graph p, ⟨p, ?_, rfl⟩, congrArg projector h⟩
    change amplitude p ≠ 0
    rwa [h]

theorem image_source_snd :
    Prod.snd '' source = closure (Prod.snd '' (graph '' defined)) := by
  apply Subset.antisymm
  · exact image_closure_subset_closure_image continuous_snd
  · apply closure_minimal (image_mono subset_closure)
    exact (source_isCompact.image continuous_snd).isClosed

private theorem unit_weight_representative {p : Invariants} (hp : amplitude p ≠ 0) :
    ∃ q, ‖weighted q‖ = 1 ∧ amplitude q ≠ 0 ∧ graph q = graph p := by
  have hw := weighted_ne_zero hp
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

/-- Every point of the compact graph has an ordinary approximating sequence
with convergent, bounded representatives in literal trace coordinates. -/
theorem exists_lift_sequence {x : Ambient} (hx : x ∈ source) :
    ∃ (p : ℕ → Invariants) (q : Invariants),
      (∀ n, amplitude (p n) ≠ 0) ∧ ‖weighted q‖ = 1 ∧
      Tendsto p atTop (𝓝 q) ∧ Tendsto (graph ∘ p) atTop (𝓝 x) ∧ x.1 = projector (weighted q) := by
  letI : FirstCountableTopology Ambient :=
    inferInstanceAs (FirstCountableTopology ((Fin 6 → Fin 6 → ℂ) × (Word 7 → Word 7 → ℂ)))
  obtain ⟨X,hX,hlim⟩ := mem_closure_iff_seq_limit.mp hx
  have h (n : ℕ) : ∃ p : Invariants,
      ‖weighted p‖ = 1 ∧ amplitude p ≠ 0 ∧ graph p = X n := by
    obtain ⟨q,hq,hXq⟩ := hX n
    rw [← hXq]
    exact unit_weight_representative hq
  choose p hw hp hgraph using h
  obtain ⟨q,_,φ,hφ,hlimq⟩ := (isCompact_closedBall (0 : Invariants) 1).tendsto_subseq
    (fun n => unit_weight_in_ball (hw n))
  have hlimX : Tendsto (graph ∘ (p ∘ φ)) atTop (𝓝 x) := by
    simpa only [comp_def, hgraph] using hlim.comp hφ.tendsto_atTop
  have hqw : ‖weighted q‖ = 1 := by
    apply tendsto_nhds_unique
      ((continuous_norm.comp continuous_weighted).continuousAt.tendsto.comp hlimq)
    simpa only [comp_def, hw] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hne : weighted q ≠ 0 := by
    intro he
    simp [he] at hqw
  refine ⟨p ∘ φ,q,fun n => hp (φ n),hqw,hlimq,hlimX,?_⟩
  exact tendsto_nhds_unique (continuous_fst.continuousAt.tendsto.comp hlimX)
    (((continuousAt_projector hne).comp continuous_weighted.continuousAt).tendsto.comp hlimq)

theorem eq_graph_of_lift {x : Ambient} (hx : x ∈ source) {q : Invariants}
    (hq : amplitude q ≠ 0) (hP : x.1 = projector (weighted q)) : x = graph q := by
  obtain ⟨p,r,_,hr,hl,hx',hR⟩ := exists_lift_sequence hx
  have hmul : ∃ c : ℂ, c ≠ 0 ∧ weighted r = c • weighted q :=
    eq_smul_of_projector_eq (weighted_ne_zero hq) (hP.symm.trans hR)
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
  · have hn : amplitude r ≠ 0 := by
      rw [he, amplitude_rescale]
      exact smul_ne_zero (pow_ne_zero _ ha') hq
    rw [tendsto_nhds_unique hx' ((continuousAt_graph hn).tendsto.comp hl), he,
      graph_rescale a q ha']
  · have hn : amplitude r ≠ 0 := by
      rw [he, amplitude_rescale, amplitude_rescale]
      exact smul_ne_zero (by norm_num) (smul_ne_zero (pow_ne_zero _ ha') hq)
    rw [tendsto_nhds_unique hx' ((continuousAt_graph hn).tendsto.comp hl), he,
      graph_rescale _ _ (by norm_num), graph_rescale a q ha']


abbrev Parameters := Fin 4 → ℂ
abbrev Source := ↥source

def traceChart (u : Parameters) : Invariants := ![1,u 0,u 1,u 2,u 3]
def chartDomain : Set Parameters := {u | amplitude (traceChart u) ≠ 0}

theorem continuous_traceChart : Continuous traceChart := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [traceChart] <;> fun_prop

theorem isOpen_chartDomain : IsOpen chartDomain :=
  isOpen_ne.preimage (continuous_amplitude.comp continuous_traceChart)

def decode (x : Ambient) : Parameters :=
  ![x.1 1 0 / x.1 0 0, x.1 3 0 / x.1 0 0, x.1 4 0 / x.1 0 0, x.1 5 0 / x.1 0 0]

theorem continuousAt_decode {x : Ambient} (hx : x.1 0 0 ≠ 0) : ContinuousAt decode x := by
  have c (i : Fin 6) : Continuous (fun y : Ambient => y.1 i 0) :=
    (continuous_apply 0).comp ((continuous_apply i).comp continuous_fst)
  apply continuousAt_pi.mpr
  intro j
  fin_cases j
  · exact (c 1).continuousAt.div (c 0).continuousAt hx
  · exact (c 3).continuousAt.div (c 0).continuousAt hx
  · exact (c 4).continuousAt.div (c 0).continuousAt hx
  · exact (c 5).continuousAt.div (c 0).continuousAt hx

def ordinary : Set Ambient := {x | x.1 0 0 ≠ 0 ∧ decode x ∈ chartDomain}

theorem isOpen_ordinary : IsOpen ordinary := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have c : Continuous (fun y : Ambient => y.1 0 0) :=
    (continuous_apply 0).comp ((continuous_apply 0).comp continuous_fst)
  have hdiag : ∀ᶠ y in 𝓝 x, y.1 0 0 ≠ 0 :=
    c.continuousAt (isOpen_ne.mem_nhds hx.1)
  have hdecode : ∀ᶠ y in 𝓝 x, decode y ∈ chartDomain :=
    continuousAt_decode hx.1 (isOpen_chartDomain.mem_nhds hx.2)
  exact hdiag.and hdecode

private theorem decode_chart {x : Ambient} {u : Parameters}
    (hx : x.1 = projector (weighted (traceChart u))) : decode x = u := by
  have h₀ : weighted (traceChart u) 0 = 1 := by simp [weighted,traceChart]
  have h (j : Fin 6) : x.1 j 0 / x.1 0 0 = weighted (traceChart u) j := by
    rw [hx, projector_ratio _ j 0 (by simp [h₀]), h₀, div_one]
  funext j
  fin_cases j <;> simp [decode,h,weighted,traceChart]

private theorem chart_round_trip {x : Ambient} (hx : x ∈ source) (ho : x ∈ ordinary) :
    graph (traceChart (decode x)) = x := by
  obtain ⟨_,q,_,_,_,_,hP⟩ := exists_lift_sequence hx
  have hq0 : q 0 ≠ 0 := by
    have hn : projector (weighted q) 0 0 ≠ 0 := by
      rw [← hP]
      exact ho.1
    intro h
    exact (projector_diag_ne_zero_iff (weighted q) 0).mp hn (by simp [weighted, h])
  let r := rescale (q 0)⁻¹ q
  let u : Parameters := ![r 1,r 2,r 3,r 4]
  have hr : traceChart u = r := by
    funext i
    fin_cases i <;> simp [traceChart,u,r,rescale,hq0]
  have hPx : x.1 = projector (weighted (traceChart u)) := by
    rw [hr, weighted_rescale, projector_scale _ (pow_ne_zero _ (inv_ne_zero hq0))]
    exact hP
  have hd := decode_chart hPx
  rw [hd]
  have hu : amplitude (traceChart u) ≠ 0 := by
    have hn := ho.2
    rwa [hd] at hn
  exact (eq_graph_of_lift hx hu hPx).symm

theorem chart_mem_ordinary {u : Parameters} (hu : u ∈ chartDomain) :
    graph (traceChart u) ∈ ordinary := by
  constructor
  · exact (projector_diag_ne_zero_iff _ _).2 (by simp [weighted,traceChart])
  · rw [decode_chart rfl]
    exact hu

theorem image_traceChart : (graph ∘ traceChart) '' chartDomain = source ∩ ordinary := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨graph_mem hu,chart_mem_ordinary hu⟩
  · rintro ⟨hx,ho⟩
    exact ⟨decode x,ho.2,chart_round_trip hx ho⟩

theorem closure_ordinary : closure (source ∩ ordinary) = source := by
  apply Subset.antisymm (closure_minimal inter_subset_left isClosed_closure)
  apply closure_minimal _ isClosed_closure
  rintro _ ⟨p,hp,rfl⟩
  let S : Set Invariants := {p | p 0 ≠ 0} ∩ defined
  have hDense : Dense ({p : Invariants | p 0 ≠ 0}) := by
    exact (dense_compl_singleton (0 : ℂ)).preimage (isOpenMap_eval 0)
  have hOpen : IsOpen defined := isOpen_ne.preimage continuous_amplitude
  have hpcl : p ∈ closure S := by
    rw [mem_closure_iff]
    intro U hU hpU
    obtain ⟨q,hq,hn⟩ := hDense.inter_open_nonempty (U ∩ defined)
      (hU.inter hOpen) ⟨p,hpU,hp⟩
    exact ⟨q,hq.1,hn,hq.2⟩
  have hcl := (continuousAt_graph hp).continuousWithinAt.mem_closure_image hpcl
  apply closure_mono _ hcl
  rintro _ ⟨q,⟨hq0,hq⟩,rfl⟩
  change q 0 ≠ 0 at hq0
  let r := rescale (q 0)⁻¹ q
  let u : Parameters := ![r 1,r 2,r 3,r 4]
  have hr : traceChart u = r := by
    funext i
    fin_cases i <;> simp [traceChart,u,r,rescale,hq0]
  have hrn : amplitude r ≠ 0 := by
    rw [show r = rescale (q 0)⁻¹ q from rfl, amplitude_rescale]
    exact smul_ne_zero (pow_ne_zero _ (inv_ne_zero hq0)) hq
  change graph q ∈ source ∩ ordinary
  rw [← image_traceChart]
  exact ⟨u,by simpa only [chartDomain,mem_setOf_eq,hr] using hrn, (congrArg graph hr).trans (graph_rescale _ _ (inv_ne_zero hq0))⟩

abbrev VacuumRoot := {a : ℂ // vacuum a = 0}

theorem finite_vacuum : Set.Finite {a : ℂ | vacuum a = 0} := by
  let p : ℂ[X] := vacuum Polynomial.X
  have hp : p ≠ 0 := by
    intro h
    have h' := congrArg (Polynomial.eval 0) h
    norm_num [p,vacuum] at h'
  simpa only [Polynomial.IsRoot, p, vacuum, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_ofNat] using Polynomial.finite_setOfPred_isRoot hp

instance : Finite VacuumRoot := finite_coe_iff.mpr finite_vacuum

theorem isPathConnected_chartDomain : IsPathConnected chartDomain := by
  let E := Fin 3 → ℂ
  let f (a : VacuumRoot) (q : E) : Parameters :=
    ![q 0,a.val,a.val*(q 0)^2,(1-2*a.val)*q 0]
  letI : Encodable VacuumRoot := Encodable.ofCountable _
  let g := Function.extend (Encodable.encode : VacuumRoot → ℕ) f (fun _ _ => 0)
  have hg (i : ℕ) : DifferentiableOn ℝ (g i) (univ : Set E) := by
    by_cases hi : ∃ a : VacuumRoot, Encodable.encode a = i
    · obtain ⟨a,rfl⟩ := hi
      rw [show g (Encodable.encode a) = f a from Encodable.encode_injective.extend_apply _ _ _]
      apply Differentiable.differentiableOn
      apply differentiable_pi.mpr
      intro j
      fin_cases j <;> simp [f] <;> fun_prop
    · rw [show g i = (fun _ => 0) from Function.extend_apply' _ _ _ hi]
      exact differentiableOn_const (0 : Parameters)
  have hc : chartDomainᶜ ⊆ ⋃ i, g i '' (univ : Set E) := by
    intro u hu
    have ha : amplitude (traceChart u) = 0 := by
      simpa [chartDomain] using hu
    obtain ⟨hd,he,hk⟩ := (amplitude_first_eq_zero_iff (u 0) (u 1) (u 2) (u 3)).1 ha
    let a : VacuumRoot := ⟨u 1,hd⟩
    refine mem_iUnion.mpr ⟨Encodable.encode a,![u 0,0,0],mem_univ _,?_⟩
    rw [show g (Encodable.encode a) = f a from Encodable.encode_injective.extend_apply _ _ _]
    funext i
    fin_cases i <;> simp [f,a,he,hk]
  simpa only [compl_compl] using
    PeriodicMPSRegularComplement.isPathConnected_compl_of_smooth_cover _ _ _ hg hc
      (by norm_num [E,Parameters,Module.finrank_pi_fintype,Complex.finrank_real_complex])

theorem isPathConnected_ordinary : IsPathConnected (source ∩ ordinary) := by
  rw [← image_traceChart]
  exact isPathConnected_chartDomain.image' (continuousOn_graph.comp
    continuous_traceChart.continuousOn fun _ hu => hu)

def boundary : Set Ambient := source \ ordinary

theorem isCompact_boundary : IsCompact boundary :=
  source_isCompact.diff isOpen_ordinary

open scoped Classical in
/-- The entire ordinary locus has a single affine chart. -/
def chart : OpenPartialHomeomorph Parameters Source where
  toFun u := if hu : u ∈ chartDomain then ⟨graph (traceChart u),graph_mem hu⟩
    else ⟨graph (traceChart ![0,0,0,0]),graph_mem (by
      change amplitude (![1,0,0,0,0] : Invariants) ≠ 0
      rw [ne_eq, amplitude_first_eq_zero_iff]
      norm_num [vacuum])⟩
  invFun x := decode x.val
  source := chartDomain
  target := Subtype.val ⁻¹' ordinary
  map_source' u hu := by
    rw [dite_eq_left hu]
    change graph (traceChart u) ∈ ordinary
    exact chart_mem_ordinary hu
  map_target' _ hx := hx.2
  left_inv' u hu := by simp only [dite_eq_left hu]; exact decode_chart rfl
  right_inv' x hx := by
    have hdecode : decode x.val ∈ chartDomain := hx.2
    simp only [dite_eq_left hdecode]
    exact Subtype.ext (chart_round_trip x.property hx)
  open_source := isOpen_chartDomain
  open_target := isOpen_ordinary.preimage continuous_subtype_val
  continuousOn_toFun := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    have hc : ContinuousOn (graph ∘ traceChart) chartDomain :=
      continuousOn_graph.comp continuous_traceChart.continuousOn fun _ hu => hu
    apply hc.congr
    intro u hu
    simp only [Function.comp_apply, dite_eq_left hu]
  continuousOn_invFun := fun x hx =>
    ((continuousAt_decode hx.1).comp continuous_subtype_val.continuousAt).continuousWithinAt

theorem chart_target_dense : Dense chart.target := by
  apply Subtype.dense_iff.mpr
  change source ⊆ closure (Subtype.val '' (Subtype.val ⁻¹' ordinary : Set Source))
  simpa only [Subtype.image_preimage_val, closure_ordinary] using (Subset.rfl : source ⊆ source)

theorem chart_target_pathConnected : IsPathConnected chart.target := by
  change IsPathConnected (Subtype.val ⁻¹' ordinary : Set Source)
  have h := isPathConnected_ordinary.preimage_coe (U := source) inter_subset_left
  simpa only [preimage_inter, show (Subtype.val ⁻¹' source : Set Source) = univ from
    eq_univ_of_forall fun x => x.property, univ_inter] using h

instance : CompactSpace Source := isCompact_iff_compactSpace.mp source_isCompact

end

end D5.S3.Quantum.TensorNetworks.SevenSiteCompactGraph
