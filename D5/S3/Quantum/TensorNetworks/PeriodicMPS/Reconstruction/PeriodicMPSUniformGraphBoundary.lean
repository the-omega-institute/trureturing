/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGraphBoundary
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGraphBoundary
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Hausdorff dimension of the uniform compact graph boundary. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteGraphBoundary
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformCompactGraph
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformTraceNormalLimits

/-! Finite charts for the compact trace-graph boundary at every period at least two. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformGraphBoundary

open Set Filter
open Function (comp_def)
open PeriodicMPSProjectiveCoordinates PeriodicMPSUniformCompactGraph
open SevenSiteTraceBase (Bond Word amplitudeOfLength wordPolynomial_eq_trace wordProduct pencil
  proportional pencilNormal traceBase traceNormal differentiable_amplitudeOfLength)
open PeriodicMPSFiveSiteCoordinates (exists_trace_coordinates)
open PeriodicMPSUniformTraceNormalInjectivity (normal contraction contraction_amplitude)
open PeriodicMPSUniformTraceNormalLimits
  (limit_at_proportional limit_at_traceless normal_smul secant differentiable_secant secant_zero)
open PeriodicMPSUniformTracePowerBoundary (eval_dickson_even_at_trace_zero)
open scoped Topology ENNReal Matrix.Norms.Elementwise

-- These projective chart and smoothness lemmas of the seven-site proof are length independent.
open private patch patch_nonzero exists_patch projector_permute differentiable_projector_comp
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteGraphBoundary
open private permute from D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteGraphBoundary

noncomputable section

variable {n : ℕ}

private def flipWord (n : ℕ) : Word n ≃ Word n where
  toFun w i := Fin.rev (w i)
  invFun w i := Fin.rev (w i)
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp

private def flipWeight : Fin 6 ≃ Fin 6 where
  toFun := ![2, 1, 0, 4, 3, 5]
  invFun := ![2, 1, 0, 4, 3, 5]
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

private def flip (p : Invariants) : Invariants := ![p 1, p 0, p 3, p 2, p 4]

private def flipPoint (x : Ambient n) : Ambient n :=
  (permute flipWeight x.1, permute (flipWord n) x.2)

private theorem flipPoint_involution (x : Ambient n) : flipPoint (flipPoint x) = x := by
  apply Prod.ext
  · ext i j
    change x.1 (flipWeight (flipWeight i)) (flipWeight (flipWeight j)) = _
    have h (k : Fin 6) : flipWeight (flipWeight k) = k := by fin_cases k <;> decide
    rw [h, h]
  · ext i j
    change x.2 (flipWord n (flipWord n i)) (flipWord n (flipWord n j)) = _
    have h (w : Word n) : flipWord n (flipWord n w) = w := (flipWord n).left_inv w
    rw [h, h]

private theorem amplitude_flip (p : Invariants) :
    amplitudeOfLength n (flip p) = amplitudeOfLength n p ∘ flipWord n := by
  obtain ⟨A, ht, hs, hd, he, hk⟩ := exists_trace_coordinates (p 0) (p 1) (p 2) (p 3) (p 4)
  let B : Fin 2 → Bond ℂ := fun i => A (Fin.rev i)
  have hBA : (B 0 * B 1).trace = p 4 := by
    change (A 1 * A 0).trace = p 4
    rw [Matrix.trace_mul_comm, hk]
  have hA (w : Word n) : amplitudeOfLength n p w = (wordProduct A w).trace := by
    simpa only [amplitudeOfLength, ht, hs, hd, he, hk] using wordPolynomial_eq_trace A w
  have hB (w : Word n) : amplitudeOfLength n (flip p) w = (wordProduct B w).trace := by
    have htB : (B 0).trace = p 1 := hs
    have hsB : (B 1).trace = p 0 := ht
    have hdB : (B 0).det = p 3 := he
    have heB : (B 1).det = p 2 := hd
    simpa [amplitudeOfLength, flip, htB, hsB, hdB, heB, hBA] using wordPolynomial_eq_trace B w
  funext w
  rw [hB, Function.comp_apply, hA]
  rfl

private theorem weighted_flip (p : Invariants) : weighted (flip p) = weighted p ∘ flipWeight := by
  funext i
  fin_cases i <;> dsimp [weighted, flip, flipWeight]
  ring

private theorem graph_flip (p : Invariants) : graph n (flip p) = flipPoint (graph n p) := by
  simp only [graph, flipPoint, projector_permute, weighted_flip, amplitude_flip]

private theorem flip_mem_source {x : Ambient n} (hx : x ∈ source n) : flipPoint x ∈ source n := by
  have h : MapsTo flipPoint (graph n '' defined n) (graph n '' defined n) := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨flip p, ?_, graph_flip p⟩
    change amplitudeOfLength n (flip p) ≠ 0
    rw [amplitude_flip]
    intro hzero
    apply hp
    funext w
    obtain ⟨v, rfl⟩ := (flipWord n).surjective w
    exact congrFun hzero v
  have hd : Continuous (flipPoint : Ambient n → Ambient n) := by
    apply Continuous.prodMk
    · exact continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply _).comp ((continuous_apply _).comp continuous_fst)
    · exact continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply _).comp ((continuous_apply _).comp continuous_snd)
  exact h.closure hd hx

private theorem continuous_rescaling :
    Continuous (fun z : ℂ × Invariants => rescale z.1 z.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [rescale] <;> fun_prop

private theorem first_chart_cases (hn : 2 ≤ n) {x : Ambient n} (hx : x ∈ source n)
    (h : x.1 0 0 ≠ 0) :
    (∃ u ∈ chartDomain n, x = graph n (traceChart u)) ∨
      ∃ (s : ℂ) (a : VacuumRoot n) (v : Fin 3 → ℂ), v ≠ 0 ∧
        x = (projector (weighted (proportional s a.val)),
          projector (normal n (proportional s a.val) (pencilNormal v))) := by
  obtain ⟨p, q, hpn, _, hp, hlim, hP⟩ := exists_lift_sequence (by omega) hx
  have hq0 : q 0 ≠ 0 := by
    have hh := (projector_diag_ne_zero_iff (weighted q) 0).mp (hP ▸ h)
    exact fun hq => hh (by simp [weighted, hq])
  let g (p : Invariants) := rescale (p 0)⁻¹ p
  let q' := g q
  have hg : ContinuousAt g q :=
    continuous_rescaling.continuousAt.comp
      (((continuous_apply 0).continuousAt.inv₀ hq0).prodMk continuousAt_id)
  have hp' : Tendsto (g ∘ p) atTop (𝓝 q') := hg.tendsto.comp hp
  have hne : ∀ᶠ j in atTop, p j 0 ≠ 0 :=
    ((continuous_apply 0).continuousAt.tendsto.comp hp) (isOpen_ne.mem_nhds hq0)
  have hq1 : q' 0 = 1 := inv_mul_cancel₀ hq0
  have hP' : x.1 = projector (weighted q') := by
    rw [show q' = rescale (q 0)⁻¹ q from rfl, weighted_rescale,
      projector_scale _ (pow_ne_zero _ (inv_ne_zero hq0))]
    exact hP
  let u : Parameters := ![q' 1, q' 2, q' 3, q' 4]
  have hu : traceChart u = q' := by
    funext i
    fin_cases i <;> simp [traceChart, u, hq1]
  by_cases hbase : u ∈ chartDomain n
  · exact Or.inl ⟨u, hbase,
      eq_graph_of_lift (by omega) hx hbase (by simpa only [hu] using hP')⟩
  · obtain ⟨ha, hd, hk⟩ := (chartDomain_compl hn u).mp hbase
    let a : VacuumRoot n := ⟨q' 2, ha⟩
    have hqprop : q' = proportional (q' 1) a.val := by
      funext i
      fin_cases i <;> simp [proportional, a, hq1, show q' 3 = q' 2 * (q' 1)^2 from hd,
        show q' 4 = (1 - 2 * q' 2) * q' 1 from hk]
    have hn' : ∀ᶠ j in atTop, amplitudeOfLength n (g (p j)) ≠ 0 := hne.mono fun j ht => by
      change amplitudeOfLength n (rescale (p j 0)⁻¹ (p j)) ≠ 0
      rw [amplitude_rescale]
      exact smul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) (hpn j).1
    have ht' : ∀ᶠ j in atTop, g (p j) 0 = 1 := hne.mono fun _ ht => inv_mul_cancel₀ ht
    have hlim' : Tendsto (fun j => projector (amplitudeOfLength n (g (p j)))) atTop (𝓝 x.2) :=
      (continuous_snd.continuousAt.tendsto.comp hlim).congr' (hne.mono fun j ht =>
        (congrArg Prod.snd (graph_rescale (n := n) _ (p j) (inv_ne_zero ht))).symm)
    rw [hqprop] at hp' hP'
    obtain ⟨v, hv, _, hvP⟩ := limit_at_proportional n hn a.property hp' ht' hn' hlim'
    exact Or.inr ⟨q' 1, a, v, hv, Prod.ext hP' hvP⟩

/-- At even period a nonzero traceless pencil always has a nonzero actual amplitude. -/
theorem amplitude_traceless_ne_zero (hn : Even n) {q : Fin 3 → ℂ} (hq : q ≠ 0) :
    amplitudeOfLength n (traceBase q) ≠ 0 := by
  obtain ⟨m, hm⟩ := hn
  have he : n = 2 * m := by omega
  intro hzero
  have h (z w : ℂ) : pencil (traceBase q) z w = 0 := by
    have hc := contraction_amplitude n (traceBase q) z w
    change contraction z w (amplitudeOfLength n (traceBase q)) = _ at hc
    rw [hzero, show contraction z w (0 : Word n → ℂ) = 0 by simp [contraction]] at hc
    simp only [traceBase, Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, add_zero] at hc
    rw [he, eval_dickson_even_at_trace_zero] at hc
    by_contra hd
    exact (mul_ne_zero (by norm_num) (pow_ne_zero m (neg_ne_zero.mpr hd))) hc.symm
  have hd : q 0 = 0 := by simpa [pencil, traceBase] using h 1 0
  have he' : q 1 = 0 := by simpa [pencil, traceBase] using h 0 1
  have hk : q 2 = 0 := by simpa [pencil, traceBase, hd, he'] using h 1 1
  exact hq (by funext i; fin_cases i <;> assumption)

/-- Normalize a traceless limiting pencil and rescale its approximating sequence
by the same nonzero scalar. -/
private theorem traceless_patch_lift (hn : 0 < n) {x : Ambient n} (hx : x ∈ source n)
    (ht : x.1 0 0 = 0) (hs : x.1 2 2 = 0) :
    ∃ (j : Fin 3) (u : Fin 2 → ℂ) (p : ℕ → Invariants),
      (∀ k, amplitudeOfLength n (p k) ≠ 0) ∧
      Tendsto p atTop (𝓝 (traceBase (patch j u))) ∧
      Tendsto (graph n ∘ p) atTop (𝓝 x) ∧
      x.1 = projector (weighted (traceBase (patch j u))) := by
  obtain ⟨p, r, hpn, hr, hp, hlim, hP⟩ := exists_lift_sequence hn hx
  have hr₀ : r 0 = 0 := by
    by_contra h
    exact ((projector_diag_ne_zero_iff (weighted r) 0).2 (by simp [weighted, h])) (hP ▸ ht)
  have hr₁ : r 1 = 0 := by
    by_contra h
    exact ((projector_diag_ne_zero_iff (weighted r) 2).2 (by simp [weighted, h])) (hP ▸ hs)
  let q : Fin 3 → ℂ := ![r 2, r 3, r 4]
  have hq : r = traceBase q := by
    funext i
    fin_cases i <;> simp [traceBase, q, hr₀, hr₁]
  have hqn : q ≠ 0 := by
    intro he
    have hh : weighted (traceBase (0 : Fin 3 → ℂ)) = 0 := by
      funext i
      fin_cases i <;> simp [weighted, traceBase]
    rw [hq, he, hh, norm_zero] at hr
    exact zero_ne_one hr
  obtain ⟨j, u, c, hc, hq'⟩ := exists_patch hqn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ (n := 2) (by decide)
  have hzn : z ≠ 0 := fun h => inv_ne_zero hc (by simpa [h] using hz.symm)
  have hcancel : z^2 * c = 1 := by rw [hz, inv_mul_cancel₀ hc]
  have he : rescale z r = traceBase (patch j u) := by
    rw [hq, hq']
    funext i
    fin_cases i <;> simp [rescale, traceBase, Pi.smul_apply, smul_eq_mul, ← mul_assoc, hcancel]
  let p' (k : ℕ) := rescale z (p k)
  have hp' : Tendsto p' atTop (𝓝 (traceBase (patch j u))) :=
    he ▸ continuous_rescaling.continuousAt.tendsto.comp (tendsto_const_nhds.prodMk_nhds hp)
  have hl' : Tendsto (graph n ∘ p') atTop (𝓝 x) := by
    simpa only [comp_def, p', graph_rescale z _ hzn] using hlim
  have hn' (k : ℕ) : amplitudeOfLength n (p' k) ≠ 0 := by
    change amplitudeOfLength n (rescale z (p k)) ≠ 0
    rw [amplitude_rescale]
    exact smul_ne_zero (pow_ne_zero _ hzn) (hpn k).1
  have hP' : x.1 = projector (weighted (traceBase (patch j u))) := by
    rw [← he, weighted_rescale, projector_scale _ (pow_ne_zero _ hzn)]
    exact hP
  exact ⟨j, u, p', hn', hp', hl', hP'⟩

private theorem traceNormal_smul (c : ℂ) (v : Fin 2 → ℂ) :
    traceNormal (c • v) = c • traceNormal v := by
  funext i
  fin_cases i <;> simp [traceNormal, Pi.smul_apply]

private theorem pencilNormal_smul (c : ℂ) (v : Fin 3 → ℂ) :
    pencilNormal (c • v) = c • pencilNormal v := by
  funext i
  fin_cases i <;> simp [pencilNormal, Pi.smul_apply]

/-- Indices for the two proportional families, odd and even pencil charts,
and the ordinary second trace chart. -/
abbrev BoundaryFamily (n : ℕ) :=
  (Bool × VacuumRoot n × Fin 3) ⊕ ((Fin 3 × Fin 2) ⊕ (Fin 3 ⊕ Unit))

/-- The even traceless charts have two complex coordinates. The other charts have three. -/
abbrev boundaryChartDim {n : ℕ} : BoundaryFamily n → ℕ
  | .inl _ => 3
  | .inr (.inl _) => 3
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr _)) => 3

abbrev BoundaryParameters (i : BoundaryFamily n) := Fin (boundaryChartDim i) → ℂ

theorem finite_boundaryFamily (hn : 0 < n) : Finite (BoundaryFamily n) := by
  let _ : Finite (VacuumRoot n) := finite_coe_iff.mpr (finite_vacuum n hn)
  infer_instance

private def tail (u : Fin 3 → ℂ) : Fin 2 → ℂ := fun i => u i.succ

private def boundaryVectors (n : ℕ) :
    (i : BoundaryFamily n) → BoundaryParameters i → (Fin 6 → ℂ) × (Word n → ℂ)
  | .inl (f, a, j), u =>
      let p := proportional (u 0) a.val
      let v := normal n p (pencilNormal (patch j (tail u)))
      if f then (weighted (flip p), v ∘ flipWord n) else (weighted p, v)
  | .inr (.inl (j, k)), u =>
      let p := traceBase (patch j (tail u))
      (weighted p, normal n p (traceNormal (patch k (fun _ => u 0))))
  | .inr (.inr (.inl j)), u =>
      let p := traceBase (patch j u)
      (weighted p, amplitudeOfLength n p)
  | .inr (.inr (.inr _)), u =>
      let p : Invariants := ![0, 1, u 1, u 0, u 2]
      (weighted p, amplitudeOfLength n p)

def boundaryMap (i : BoundaryFamily n) (u : BoundaryParameters i) : Ambient n :=
  (projector (boundaryVectors n i u).1, projector (boundaryVectors n i u).2)

def boundaryDomain (i : BoundaryFamily n) : Set (BoundaryParameters i) :=
  {u | (boundaryVectors n i u).1 ≠ 0 ∧ (boundaryVectors n i u).2 ≠ 0}

private theorem ne_zero_of_projector_mem {ι : Type*} [Fintype ι] {v : ι → ℂ}
    (hv : projector v ∈ projective) : v ≠ 0 := by
  rintro rfl
  obtain ⟨p, hp, houter⟩ := hv
  have hp' : p ≠ 0 := by
    intro hz
    change mass p = 1 at hp
    simp [hz, mass] at hp
  obtain ⟨j, hj⟩ : ∃ j, p j ≠ 0 := by
    by_contra! H
    exact hp' (funext H)
  have hh := congrFun (congrFun houter j) j
  simp only [outer, projector, Matrix.smul_apply, Pi.zero_apply, zero_mul, smul_zero] at hh
  exact (mul_ne_zero hj ((map_ne_zero (starRingEnd ℂ)).2 hj)) hh

private theorem proportional_cover (f : Bool) (s : ℂ) (a : VacuumRoot n)
    (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    ∃ (j : Fin 3) (u : Fin 3 → ℂ),
      (if f then flipPoint else id)
        (projector (weighted (proportional s a.val)),
          projector (normal n (proportional s a.val) (pencilNormal v))) =
        boundaryMap (.inl (f, a, j)) u := by
  obtain ⟨j, w, c, hc, hv'⟩ := exists_patch hv
  let u : Fin 3 → ℂ := Fin.cons s w
  have ht : tail u = w := by funext i; simp [tail, u]
  have h₀ : u 0 = s := by simp [u]
  refine ⟨j, u, ?_⟩
  rw [hv', pencilNormal_smul, normal_smul, projector_scale _ hc]
  cases f
  · simp [boundaryMap, boundaryVectors, ht, h₀]
  · simp [boundaryMap, boundaryVectors, ht, h₀, flipPoint, weighted_flip, projector_permute]

/-- Every point lost from the trace-one chart belongs to one of the finite boundary charts. -/
theorem boundary_subset_charts (hn : 2 ≤ n) :
    boundary n ⊆ ⋃ i : BoundaryFamily n, boundaryMap i '' boundaryDomain i := by
  intro x hx
  have finish (i : BoundaryFamily n) (u : BoundaryParameters i)
      (he : x = boundaryMap i u) :
      x ∈ ⋃ j : BoundaryFamily n, boundaryMap j '' boundaryDomain j := by
    have hs := source_projective (show 0 < n by omega) hx.1
    rw [he] at hs
    exact mem_iUnion.mpr ⟨i, u, ⟨ne_zero_of_projector_mem hs.1,
      ne_zero_of_projector_mem hs.2⟩, he.symm⟩
  by_cases ht : x.1 0 0 ≠ 0
  · rcases first_chart_cases hn hx.1 ht with ⟨u, hu, h⟩ | ⟨s, a, v, hv, h⟩
    · exact (hx.2 (by rw [h]; exact chart_mem_ordinary hu)).elim
    · obtain ⟨j, u, hu⟩ := proportional_cover false s a v hv
      exact finish (.inl (false, a, j)) u (h.trans hu)
  · by_cases hs : x.1 2 2 ≠ 0
    · rcases first_chart_cases hn (flip_mem_source hx.1)
        (show (flipPoint x).1 0 0 ≠ 0 from hs) with ⟨u, _, h⟩ | ⟨s, a, v, hv, h⟩
      · have hx' : x = graph n (flip (traceChart u)) := by
          rw [graph_flip, ← h, flipPoint_involution]
        have ht' : u 0 = 0 := by
          by_contra he
          apply ht
          rw [hx']
          exact (projector_diag_ne_zero_iff (weighted (flip (traceChart u))) 0).2
            (by simp [weighted, flip, traceChart, he])
        let w : Fin 3 → ℂ := ![u 1, u 2, u 3]
        apply finish (.inr (.inr (.inr ()))) w
        rw [hx']
        have hh : flip (traceChart u) = (![0, 1, w 1, w 0, w 2] : Invariants) := by
          funext i
          fin_cases i <;> simp [flip, traceChart, ht', w]
        simpa only [graph, boundaryMap, boundaryVectors] using congrArg (graph n) hh
      · obtain ⟨j, u, hu⟩ := proportional_cover true s a v hv
        exact finish (.inl (true, a, j)) u
          ((flipPoint_involution x).symm.trans ((congrArg flipPoint h).trans hu))
    · obtain ⟨j, u, p, hne, hp, hlim, hP⟩ :=
        traceless_patch_lift (by omega) hx.1 (not_ne_iff.mp ht) (not_ne_iff.mp hs)
      rcases Nat.even_or_odd n with heven | hodd
      · have ha := amplitude_traceless_ne_zero heven (patch_nonzero j u)
        apply finish (.inr (.inr (.inl j))) u
        simpa only [boundaryMap, boundaryVectors, graph] using
          eq_graph_of_lift (show 0 < n by omega) hx.1 ha hP
      · have hl : Tendsto (fun k => projector (amplitudeOfLength n (p k))) atTop (𝓝 x.2) :=
          continuous_snd.continuousAt.tendsto.comp hlim
        obtain ⟨v, hv, _, hvP⟩ :=
          limit_at_traceless n hodd (patch_nonzero j u) hp (Eventually.of_forall hne) hl
        obtain ⟨k, w, c, hc, hv'⟩ := exists_patch hv
        let t : Fin 3 → ℂ := Fin.cons (w 0) u
        have htail : tail t = u := by funext i; simp [tail, t]
        have hw : (fun _ : Fin 1 => t 0) = w := by
          funext i
          fin_cases i
          simp [t]
        apply finish (.inr (.inl (j, k))) t
        rw [hv', traceNormal_smul, normal_smul, projector_scale _ hc] at hvP
        simpa [boundaryMap, boundaryVectors, htail, hw] using Prod.ext hP hvP

private theorem differentiable_boundaryVectors (j : BoundaryFamily n) :
    Differentiable ℝ (boundaryVectors n j) := by
  have hpatch {m l : ℕ} (j : Fin (m + 1)) (u : (Fin l → ℂ) → Fin m → ℂ)
      (hu : Differentiable ℝ u) : Differentiable ℝ (fun x => patch j (u x)) := by
    apply differentiable_pi.mpr
    intro i
    by_cases hi : i = j
    · subst i
      simp [patch]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
      simpa [patch] using (differentiable_apply k).fun_comp hu
  have hnormal (b v : (Fin 3 → ℂ) → Invariants)
      (hb : Differentiable ℝ b) (hv : Differentiable ℝ v) :
      Differentiable ℝ (fun u => normal n (b u) (v u)) := by
    simp_rw [← secant_zero]
    exact ((differentiable_secant n).restrictScalars ℝ).comp
      (hb.prodMk (hv.prodMk (differentiable_const _)))
  have hweight {l : ℕ} (b : (Fin l → ℂ) → Invariants) (hb : Differentiable ℝ b) :
      Differentiable ℝ (fun u => weighted (b u)) := by
    have hd (i : Fin 5) := (differentiable_apply i).comp hb
    apply differentiable_pi.mpr
    intro i
    fin_cases i <;> simp [weighted] <;> fun_prop
  have htail : Differentiable ℝ (tail : (Fin 3 → ℂ) → Fin 2 → ℂ) :=
    differentiable_pi.mpr fun i => differentiable_apply i.succ
  have hbase {l : ℕ} (j : Fin 3) (pencilCoords : (Fin l → ℂ) → Fin 2 → ℂ)
      (hp : Differentiable ℝ pencilCoords) :
      Differentiable ℝ (fun u => traceBase (patch j (pencilCoords u))) := by
    have hd (i : Fin 3) := (differentiable_apply i).comp (hpatch j pencilCoords hp)
    apply differentiable_pi.mpr
    intro i
    fin_cases i <;> simp [traceBase] <;> fun_prop
  rcases j with ⟨f, a, j⟩ | (⟨j, k⟩ | j | ⟨⟩)
  · let b (u : Fin 3 → ℂ) := proportional (u 0) a.val
    let v (u : Fin 3 → ℂ) := pencilNormal (patch j (tail u))
    have hb : Differentiable ℝ b := by
      apply differentiable_pi.mpr
      intro i
      fin_cases i <;> simp [b, proportional] <;> fun_prop
    have hv : Differentiable ℝ v := by
      have hd (i : Fin 3) := (differentiable_apply i).comp (hpatch j tail htail)
      apply differentiable_pi.mpr
      intro i
      fin_cases i <;> simp [v, pencilNormal] <;> fun_prop
    have ha := hnormal b v hb hv
    cases f
    · exact (hweight b hb).prodMk ha
    · have hf : Differentiable ℝ (fun u => flip (b u)) := by
        apply differentiable_pi.mpr
        intro i
        fin_cases i <;> simpa [flip] using (differentiable_apply _).fun_comp hb
      exact (hweight _ hf).prodMk (differentiable_pi.mpr
        fun w => (differentiable_apply (flipWord n w)).comp ha)
  · let v (u : Fin 3 → ℂ) := traceNormal (patch k (fun _ => u 0))
    have hv : Differentiable ℝ v := by
      have hc : Differentiable ℝ (fun u : Fin 3 → ℂ => fun _ : Fin 1 => u 0) :=
        differentiable_pi.mpr fun _ => differentiable_apply 0
      have hd (i : Fin 2) := (differentiable_apply i).comp (hpatch k _ hc)
      apply differentiable_pi.mpr
      intro i
      fin_cases i <;> simp [v, traceNormal] <;> fun_prop
    exact (hweight _ (hbase j tail htail)).prodMk (hnormal _ v (hbase j tail htail) hv)
  · have hb := hbase j (id : (Fin 2 → ℂ) → Fin 2 → ℂ) differentiable_id
    exact (hweight _ hb).prodMk ((differentiable_amplitudeOfLength n).fun_comp hb)
  · let b (u : Fin 3 → ℂ) : Invariants := ![0, 1, u 1, u 0, u 2]
    have hb : Differentiable ℝ b := by
      apply differentiable_pi.mpr
      intro i
      fin_cases i <;> simp [b] <;> fun_prop
    exact (hweight _ hb).prodMk ((differentiable_amplitudeOfLength n).fun_comp hb)

theorem boundary_differentiable_cover (hn : 2 ≤ n) :
    (∀ i : BoundaryFamily n, IsOpen (boundaryDomain i) ∧
      DifferentiableOn ℝ (boundaryMap i) (boundaryDomain i)) ∧
      boundary n ⊆ ⋃ i : BoundaryFamily n, boundaryMap i '' boundaryDomain i := by
  refine ⟨fun i => ?_, boundary_subset_charts hn⟩
  have h := differentiable_boundaryVectors i
  have hl := differentiable_fst.comp h
  have hr := differentiable_snd.comp h
  exact ⟨(isOpen_ne.preimage hl.continuous).inter (isOpen_ne.preimage hr.continuous),
    ((differentiable_projector_comp _ hl).mono inter_subset_left).prodMk
      ((differentiable_projector_comp _ hr).mono inter_subset_right)⟩

/-- The complement of the trace-one chart in the actual compact graph has Hausdorff
dimension at most six, for every period at least two. -/
theorem dimH_boundary_le (hn : 2 ≤ n) : dimH (boundary n) ≤ 6 := by
  let _ := finite_boundaryFamily (show 0 < n by omega)
  apply (dimH_mono (boundary_differentiable_cover hn).2).trans
  rw [dimH_iUnion]
  apply iSup_le
  intro i
  calc
    _ ≤ dimH (boundaryDomain i) := ((boundary_differentiable_cover hn).1 i).2.dimH_image_le
    _ ≤ dimH (univ : Set (BoundaryParameters i)) := dimH_mono (subset_univ _)
    _ ≤ 6 := by
      rw [Real.dimH_univ_eq_finrank]
      rcases i with ⟨f, a, j⟩ | (⟨j, k⟩ | j | ⟨⟩) <;>
        norm_num [BoundaryParameters, boundaryChartDim, Module.finrank_pi_fintype,
          Complex.finrank_real_complex]

/-- The same complement as a subset of the compact graph with the inherited metric. -/
def chartBoundary (hn : 2 ≤ n) : Set (Source n) := (chart hn).targetᶜ

theorem isCompact_chartBoundary (hn : 2 ≤ n) : IsCompact (chartBoundary hn) := by
  let _ : CompactSpace (Source n) := isCompact_iff_compactSpace.mp (source_isCompact (by omega))
  exact (chart hn).open_target.isClosed_compl.isCompact

theorem dimH_chartBoundary_le (hn : 2 ≤ n) : dimH (chartBoundary hn) ≤ 6 := by
  have h : Subtype.val '' chartBoundary hn = boundary n := by
    change Subtype.val '' (Subtype.val ⁻¹' ordinary n : Set (Source n))ᶜ = boundary n
    rw [← preimage_compl, Subtype.image_preimage_val]
    rfl
  rw [← isometry_subtype_coe.dimH_image, h]
  exact dimH_boundary_le hn

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformGraphBoundary
