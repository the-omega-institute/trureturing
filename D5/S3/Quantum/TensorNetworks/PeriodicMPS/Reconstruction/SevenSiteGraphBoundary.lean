/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGraphBoundary
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGraphBoundary
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Hausdorff dimension of the compact seven-site graph boundary. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCompactGraph
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-! Differentiable charts for the compact seven-site graph boundary. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteGraphBoundary

open Set Filter SevenSiteTraceBase SevenSiteCompactGraph PeriodicMPSProjectiveCoordinates
open Function (comp_def)
open PeriodicMPSFiveSiteCoordinates (exists_trace_coordinates)
open scoped BigOperators Topology ENNReal Matrix.Norms.Elementwise ComplexConjugate

noncomputable section

private def flipWord : Word 7 ≃ Word 7 where
  toFun w i := Fin.rev (w i)
  invFun w i := Fin.rev (w i)
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp

private def flipWeight : Fin 6 ≃ Fin 6 :=
  { toFun := ![2,1,0,4,3,5]
    invFun := ![2,1,0,4,3,5]
    left_inv := by intro i; fin_cases i <;> decide
    right_inv := by intro i; fin_cases i <;> decide }

def flip (p : Invariants) : Invariants := ![p 1,p 0,p 3,p 2,p 4]

private def permute {ι : Type*} (σ : ι ≃ ι) (P : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => P (σ i) (σ j)

private theorem projector_permute {ι : Type*} [Fintype ι] (σ : ι ≃ ι) (v : ι → ℂ) :
    permute σ (projector v) = projector (v ∘ σ) := by
  have hm : mass (v ∘ σ) = mass v := σ.sum_comp fun i => Complex.normSq (v i)
  ext i j
  simp only [permute, projector, hm, outer, Matrix.smul_apply, Function.comp_apply]

private def flipPoint (x : Ambient) : Ambient :=
  (permute flipWeight x.1, permute flipWord x.2)

private theorem flipPoint_involution (x : Ambient) : flipPoint (flipPoint x) = x := by
  apply Prod.ext
  · ext i j
    change x.1 (flipWeight (flipWeight i)) (flipWeight (flipWeight j)) = _
    have h (k : Fin 6) : flipWeight (flipWeight k) = k := by fin_cases k <;> decide
    rw [h,h]
  · ext i j
    change x.2 (flipWord (flipWord i)) (flipWord (flipWord j)) = _
    have h (w : Word 7) : flipWord (flipWord w) = w := flipWord.left_inv w
    rw [h,h]

private theorem amplitude_flip (p : Invariants) : amplitude (flip p) = amplitude p ∘ flipWord := by
  obtain ⟨A,ht,hs,hd,he,hk⟩ := exists_trace_coordinates (p 0) (p 1) (p 2) (p 3) (p 4)
  let B : Fin 2 → Bond ℂ := fun i => A (Fin.rev i)
  have hBA : (B 0 * B 1).trace = p 4 := by
    change (A 1 * A 0).trace = p 4
    rw [Matrix.trace_mul_comm, hk]
  have hA (w : Word 7) : amplitude p w = (wordProduct A w).trace := by
    simpa only [amplitude,ht,hs,hd,he,hk] using wordPolynomial_eq_trace A w
  have hB (w : Word 7) : amplitude (flip p) w = (wordProduct B w).trace := by
    have htB : (B 0).trace = p 1 := hs
    have hsB : (B 1).trace = p 0 := ht
    have hdB : (B 0).det = p 3 := he
    have heB : (B 1).det = p 2 := hd
    simpa [amplitude,flip,htB,hsB,hdB,heB,hBA] using wordPolynomial_eq_trace B w
  funext w
  rw [hB, Function.comp_apply, hA]
  rfl

private theorem amplitude_flip_eq_zero (p : Invariants) :
    amplitude (flip p) = 0 ↔ amplitude p = 0 := by
  rw [amplitude_flip]
  constructor
  · intro h
    funext w
    have hw := congrFun h (flipWord w)
    have hw' : flipWord (flipWord w) = w := flipWord.left_inv w
    simpa only [Function.comp_apply, hw', Pi.zero_apply] using hw
  · intro h
    rw [h]
    rfl

private theorem normalized_eq_zero_iff (p : Invariants) (hp : p 0 ≠ 0) :
    amplitude p = 0 ↔
      ∃ (s : ℂ) (a : VacuumRoot), rescale (p 0)⁻¹ p = proportional s a.val := by
  let q := rescale (p 0)⁻¹ p
  have hq : q 0 = 1 := inv_mul_cancel₀ hp
  have hscale : amplitude p = 0 ↔ amplitude q = 0 := by
    change _ ↔ amplitude (rescale (p 0)⁻¹ p) = 0
    rw [amplitude_rescale]
    constructor
    · intro h
      rw [h,smul_zero]
    · intro h
      exact (smul_eq_zero.mp h).resolve_left (pow_ne_zero _ (inv_ne_zero hp))
  have hvec : (![1,q 1,q 2,q 3,q 4] : Invariants) = q := by
    funext i
    fin_cases i <;> simp [hq]
  rw [hscale]
  constructor
  · intro h
    have hz := (amplitude_first_eq_zero_iff (q 1) (q 2) (q 3) (q 4)).mp
      (by simpa only [hvec] using h)
    refine ⟨q 1,⟨q 2,hz.1⟩,?_⟩
    change q = proportional (q 1) (q 2)
    funext i
    fin_cases i <;> simp [proportional,hq,hz.2.1,hz.2.2]
  · rintro ⟨s,a,ha⟩
    change q = _ at ha
    rw [ha]
    exact amplitude_proportional s a.val a.property

/-- The base locus consists of the traceless plane and the proportional trace
components in the two trace charts. -/
theorem amplitude_eq_zero_iff (p : Invariants) :
    amplitude p = 0 ↔
      (p 0 = 0 ∧ p 1 = 0) ∨
      (p 0 ≠ 0 ∧ ∃ (s : ℂ) (a : VacuumRoot),
        rescale (p 0)⁻¹ p = proportional s a.val) ∨
      (p 1 ≠ 0 ∧ ∃ (s : ℂ) (a : VacuumRoot),
        rescale (p 1)⁻¹ (flip p) = proportional s a.val) := by
  constructor
  · intro h
    by_cases ht : p 0 = 0
    · by_cases hs : p 1 = 0
      · exact Or.inl ⟨ht,hs⟩
      · exact Or.inr (Or.inr ⟨hs,(normalized_eq_zero_iff (flip p) hs).mp
          ((amplitude_flip_eq_zero p).mpr h)⟩)
    · exact Or.inr (Or.inl ⟨ht,(normalized_eq_zero_iff p ht).mp h⟩)
  · rintro (⟨ht,hs⟩ | ⟨ht,h⟩ | ⟨hs,h⟩)
    · have hh : (![0,0,p 2,p 3,p 4] : Invariants) = p := by
        funext i
        fin_cases i <;> simp [ht,hs]
      rw [← hh]
      exact amplitude_traceless _ _ _
    · exact (normalized_eq_zero_iff p ht).mpr h
    · exact (amplitude_flip_eq_zero p).mp ((normalized_eq_zero_iff (flip p) hs).mpr h)

private theorem weighted_flip (p : Invariants) : weighted (flip p) = weighted p ∘ flipWeight := by
  funext i
  fin_cases i <;> dsimp [weighted,flip,flipWeight]
  ring

private theorem graph_flip (p : Invariants) : graph (flip p) = flipPoint (graph p) := by
  simp only [graph,flipPoint,projector_permute,weighted_flip,amplitude_flip]

private theorem flip_mem_source {x : Ambient} (hx : x ∈ source) : flipPoint x ∈ source := by
  have h : MapsTo flipPoint (graph '' defined) (graph '' defined) := by
    rintro _ ⟨p,hp,rfl⟩
    refine ⟨flip p,?_,graph_flip p⟩
    exact fun he => hp ((amplitude_flip_eq_zero p).mp he)
  have hd : Continuous flipPoint := by
    apply Continuous.prodMk
    · exact continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply _).comp ((continuous_apply _).comp continuous_fst)
    · exact continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply _).comp ((continuous_apply _).comp continuous_snd)
  exact h.closure hd hx

private theorem lift_limit {m : ℕ} (pack : (Fin m → ℂ) → Invariants)
    (hpack : ∀ (c : ℂ) v, pack (c • v) = c • pack v)
    (b : ℕ → Invariants) (b₀ : Invariants) (v : ℕ → Fin m → ℂ)
    (hb : ∀ n, amplitude (b n) = 0) (hbl : Tendsto b atTop (𝓝 b₀))
    (hvl : Tendsto v atTop (𝓝 0))
    (hn : ∀ᶠ n in atTop, amplitude (b n + pack (v n)) ≠ 0)
    (hzero : ∀ u ≠ 0, normal b₀ (pack u) ≠ 0)
    (hcont : Continuous pack)
    (P : Matrix (Word 7) (Word 7) ℂ)
    (hP : Tendsto (fun n => projector (amplitude (b n + pack (v n)))) atTop (𝓝 P)) :
    ∃ u : Fin m → ℂ, u ≠ 0 ∧ P = projector (normal b₀ (pack u)) := by
  let l (n : ℕ) : ℂ := ↑‖v n‖
  let u (n : ℕ) := (l n)⁻¹ • v n
  have hpack₀ : pack 0 = 0 := by simpa using hpack 0 (0 : Fin m → ℂ)
  have hn' : ∀ᶠ n in atTop, v n ≠ 0 := hn.mono fun n hn' h =>
    hn' (by rw [h,hpack₀,add_zero,hb])
  have hu : ∀ᶠ n in atTop, u n ∈ Metric.sphere (0 : Fin m → ℂ) 1 := by
    filter_upwards [hn'] with n hv
    have hnorm := norm_ne_zero_iff.mpr hv
    rw [Metric.mem_sphere,dist_zero_right,show u n = (l n)⁻¹ • v n from rfl,
      norm_smul,norm_inv,show ‖l n‖ = ‖v n‖ by simp [l],inv_mul_cancel₀ hnorm]
  obtain ⟨u₀,hu₀,φ,hφ,hlφ⟩ := (isCompact_sphere (0 : Fin m → ℂ) 1).tendsto_subseq' hu.frequently
  have hlu : Tendsto l atTop (𝓝 0) := by
    have hd : Continuous (fun x : Fin m → ℂ => (↑‖x‖ : ℂ)) :=
      Complex.continuous_ofReal.comp continuous_norm
    simpa only [comp_def, norm_zero, Complex.ofReal_zero] using hd.continuousAt.tendsto.comp hvl
  have hunit : u₀ ≠ 0 := Metric.ne_of_mem_sphere hu₀ one_ne_zero
  have hl : Tendsto (fun n => secant (b (φ n)) (pack (u (φ n))) (l (φ n))) atTop
      (𝓝 (normal b₀ (pack u₀))) := by
    rw [← secant_zero]
    exact ((differentiable_secant (𝕜 := ℂ)).continuous.continuousAt.tendsto).comp
      ((hbl.comp hφ.tendsto_atTop).prodMk_nhds
        ((hcont.continuousAt.tendsto.comp hlφ).prodMk_nhds (hlu.comp hφ.tendsto_atTop)))
  have heq : ∀ᶠ n in atTop, projector (amplitude (b n + pack (v n))) =
      projector (secant (b n) (pack (u n)) (l n)) := by
    filter_upwards [hn'] with n hn'
    have hl₀ : l n ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hn')
    have hp : l n • pack (u n) = pack (v n) := by
      rw [← hpack, show u n = (l n)⁻¹ • v n from rfl, smul_smul, mul_inv_cancel₀ hl₀,one_smul]
    rw [← hp, amplitude_eq_smul_secant _ _ _ (hb n), projector_scale _ hl₀]
  refine ⟨u₀,hunit,?_⟩
  exact tendsto_nhds_unique ((hP.comp hφ.tendsto_atTop).congr' (hφ.tendsto_atTop.eventually heq))
    ((continuousAt_projector (hzero u₀ hunit)).tendsto.comp hl)

private theorem traceNormal_smul (c : ℂ) (v : Fin 2 → ℂ) :
    traceNormal (c • v) = c • traceNormal v := by
  funext i
  fin_cases i <;> simp [traceNormal,Pi.smul_apply]

private theorem pencilNormal_smul (c : ℂ) (v : Fin 3 → ℂ) :
    pencilNormal (c • v) = c • pencilNormal v := by
  funext i
  fin_cases i <;> simp [pencilNormal,Pi.smul_apply]

private theorem limit_at_traceless {x : Ambient} (p : ℕ → Invariants) (q : Fin 3 → ℂ)
    (hq : q ≠ 0) (hn : ∀ n, amplitude (p n) ≠ 0)
    (hp : Tendsto p atTop (𝓝 (traceBase q))) (hlim : Tendsto (graph ∘ p) atTop (𝓝 x)) :
    ∃ u : Fin 2 → ℂ, u ≠ 0 ∧ x.2 = projector (normal (traceBase q) (traceNormal u)) := by
  let b (n : ℕ) := traceBase ![p n 2,p n 3,p n 4]
  let v (n : ℕ) : Fin 2 → ℂ := ![p n 0,p n 1]
  have hb (n : ℕ) : amplitude (b n) = 0 := amplitude_traceless _ _ _
  have hsum (n : ℕ) : b n + traceNormal (v n) = p n := by
    funext i
    fin_cases i <;> simp [b,v,traceBase,traceNormal,Pi.add_apply]
  have c (i : Fin 5) := (continuous_apply i).continuousAt.tendsto.comp hp
  have hbl : Tendsto b atTop (𝓝 (traceBase q)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i <;> simp [b,traceBase] <;> first | exact tendsto_const_nhds | exact c _
  have hvl : Tendsto v atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact c 0
    · exact c 1
  apply lift_limit traceNormal traceNormal_smul b _ v hb hbl hvl
  · exact Eventually.of_forall fun n => hsum n ▸ hn n
  · intro u hu h
    apply hu
    apply trace_normal_injective q hq
    have he : traceNormal (0 : Fin 2 → ℂ) = 0 := by
      funext i
      fin_cases i <;> rfl
    change normal (traceBase q) (traceNormal u) = normal (traceBase q) (traceNormal 0)
    rw [h,he,normal_zero]
  · apply continuous_pi
    intro i
    fin_cases i <;> simp [traceNormal] <;> fun_prop
  · simpa only [hsum,comp_def,graph] using continuous_snd.continuousAt.tendsto.comp hlim

private theorem limit_at_proportional {x : Ambient} (p : ℕ → Invariants) (s a : ℂ)
    (ha : vacuum a = 0) (hn : ∀ᶠ n in atTop, amplitude (p n) ≠ 0)
    (ht : ∀ᶠ n in atTop, p n 0 = 1)
    (hp : Tendsto p atTop (𝓝 (proportional s a)))
    (hlim : Tendsto (fun n => projector (amplitude (p n))) atTop (𝓝 x.2)) :
    ∃ u : Fin 3 → ℂ, u ≠ 0 ∧ x.2 = projector (normal (proportional s a) (pencilNormal u)) := by
  let b (n : ℕ) := proportional (p n 1) a
  let v (n : ℕ) : Fin 3 → ℂ := ![p n 2 - b n 2,p n 3 - b n 3,p n 4 - b n 4]
  have hb (n : ℕ) : amplitude (b n) = 0 := amplitude_proportional _ _ ha
  have hsum : ∀ᶠ n in atTop, b n + pencilNormal (v n) = p n := by
    filter_upwards [ht] with n hn
    funext i
    fin_cases i <;> simp [b,v,pencilNormal,proportional,Pi.add_apply,hn] <;> ring
  have hbl : Tendsto b atTop (𝓝 (proportional s a)) := by
    have hc : Continuous (fun t : ℂ => proportional t a) := by
      apply continuous_pi
      intro i
      fin_cases i <;> simp [proportional] <;> fun_prop
    exact hc.continuousAt.tendsto.comp ((continuous_apply 1).continuousAt.tendsto.comp hp)
  have hvl : Tendsto v atTop (𝓝 0) := by
    have hs (i : Fin 5) := (continuous_apply i).continuousAt.tendsto.comp (hp.sub hbl)
    simp only [sub_self] at hs
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact hs 2
    · exact hs 3
    · exact hs 4
  apply lift_limit pencilNormal pencilNormal_smul b _ v hb hbl hvl
  · filter_upwards [hn,hsum] with n hn hs
    rwa [hs]
  · intro u hu h
    apply hu
    apply proportional_normal_injective s a ha
    have he : pencilNormal (0 : Fin 3 → ℂ) = 0 := by
      funext i
      fin_cases i <;> rfl
    change normal (proportional s a) (pencilNormal u) =
      normal (proportional s a) (pencilNormal 0)
    rw [h,he,normal_zero]
  · apply continuous_pi
    intro i
    fin_cases i <;> simp [pencilNormal] <;> fun_prop
  · exact hlim.congr' (hsum.mono fun n h => congrArg (fun q => projector (amplitude q)) h.symm)

private theorem continuous_rescale : Continuous (fun z : ℂ × Invariants => rescale z.1 z.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [rescale] <;> fun_prop

private theorem first_chart_cases {x : Ambient} (hx : x ∈ source) (h : x.1 0 0 ≠ 0) :
    (∃ u ∈ chartDomain, x = graph (traceChart u)) ∨
      ∃ (s : ℂ) (a : VacuumRoot) (v : Fin 3 → ℂ), v ≠ 0 ∧
        x = (projector (weighted (proportional s a.val)),
          projector (normal (proportional s a.val) (pencilNormal v))) := by
  obtain ⟨p,q,hn,_,hp,hlim,hP⟩ := exists_lift_sequence hx
  have hq0 : q 0 ≠ 0 := by
    have hh := (projector_diag_ne_zero_iff (weighted q) 0).mp (hP ▸ h)
    exact fun hq => hh (by simp [weighted,hq])
  let g (p : Invariants) := rescale (p 0)⁻¹ p
  let q' := g q
  have hg : ContinuousAt g q :=
    continuous_rescale.continuousAt.comp
      (((continuous_apply 0).continuousAt.inv₀ hq0).prodMk continuousAt_id)
  have hp' : Tendsto (g ∘ p) atTop (𝓝 q') := hg.tendsto.comp hp
  have hne : ∀ᶠ n in atTop, p n 0 ≠ 0 :=
    ((continuous_apply 0).continuousAt.tendsto.comp hp) (isOpen_ne.mem_nhds hq0)
  have hq1 : q' 0 = 1 := inv_mul_cancel₀ hq0
  have hP' : x.1 = projector (weighted q') := by
    rw [show q' = rescale (q 0)⁻¹ q from rfl,weighted_rescale,
      projector_scale _ (pow_ne_zero _ (inv_ne_zero hq0))]
    exact hP
  let u : Parameters := ![q' 1,q' 2,q' 3,q' 4]
  have hu : traceChart u = q' := by
    funext i
    fin_cases i <;> simp [traceChart,u,hq1]
  by_cases hbase : amplitude q' = 0
  · have hbase' : amplitude (traceChart u) = 0 := hu.symm ▸ hbase
    have hh := (amplitude_first_eq_zero_iff (u 0) (u 1) (u 2) (u 3)).mp hbase'
    let a : VacuumRoot := ⟨q' 2,hh.1⟩
    have hqprop : q' = proportional (q' 1) a.val := by
      funext i
      fin_cases i <;> simp [proportional,a,hq1,show q' 3 = q' 2*(q' 1)^2 from hh.2.1,
        show q' 4 = (1-2*q' 2)*q' 1 from hh.2.2]
    have hn' : ∀ᶠ n in atTop, amplitude (g (p n)) ≠ 0 := hne.mono fun n ht => by
      change amplitude (rescale (p n 0)⁻¹ (p n)) ≠ 0
      rw [amplitude_rescale]
      exact smul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) (hn n)
    have ht' : ∀ᶠ n in atTop, g (p n) 0 = 1 := hne.mono fun _ ht => inv_mul_cancel₀ ht
    have hlim' : Tendsto (fun n => projector (amplitude (g (p n)))) atTop (𝓝 x.2) :=
      (continuous_snd.continuousAt.tendsto.comp hlim).congr' (hne.mono fun n ht =>
        (congrArg Prod.snd (graph_rescale _ (p n) (inv_ne_zero ht))).symm)
    rw [hqprop] at hp' hP'
    obtain ⟨v,hv,hvP⟩ := limit_at_proportional (x := x) (g ∘ p) (q' 1) a.val a.property
      hn' ht' hp' hlim'
    exact Or.inr ⟨q' 1,a,v,hv,Prod.ext hP' hvP⟩
  · have hn' : amplitude (traceChart u) ≠ 0 := by simpa only [hu] using hbase
    exact Or.inl ⟨u,hn',eq_graph_of_lift hx hn' (by simpa only [hu] using hP')⟩


private def patch {n : ℕ} (j : Fin (n + 1)) (u : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.insertNth (α := fun _ => ℂ) j 1 u

private theorem patch_nonzero {n : ℕ} (j : Fin (n + 1)) (u : Fin n → ℂ) :
    patch j u ≠ 0 := fun h => one_ne_zero (α := ℂ) (by simpa [patch] using congrFun h j)

private theorem exists_patch {n : ℕ} {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) :
    ∃ (j : Fin (n + 1)) (u : Fin n → ℂ) (c : ℂ), c ≠ 0 ∧ v = c • patch j u := by
  obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  let u := fun i => v (j.succAbove i) / v j
  refine ⟨j,u,v j,hj,?_⟩
  funext i
  by_cases h : i = j
  · subst i
    simp [patch,Pi.smul_apply,smul_eq_mul]
  · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq h
    simp [patch,u,Pi.smul_apply,smul_eq_mul,mul_div_cancel₀ _ hj]

private theorem traceless_patch_cases {x : Ambient} (hx : x ∈ source)
    (ht : x.1 0 0 = 0) (hs : x.1 2 2 = 0) :
    ∃ (j : Fin 3) (u : Fin 2 → ℂ) (v : Fin 2 → ℂ), v ≠ 0 ∧
      x = (projector (weighted (traceBase (patch j u))),
        projector (normal (traceBase (patch j u)) (traceNormal v))) := by
  obtain ⟨p,r,hn,hr,hp,hlim,hP⟩ := exists_lift_sequence hx
  have hr₀ : r 0 = 0 := by
    by_contra h
    exact ((projector_diag_ne_zero_iff (weighted r) 0).2 (by simp [weighted,h])) (hP ▸ ht)
  have hr₁ : r 1 = 0 := by
    by_contra h
    exact ((projector_diag_ne_zero_iff (weighted r) 2).2 (by simp [weighted,h])) (hP ▸ hs)
  let q : Fin 3 → ℂ := ![r 2,r 3,r 4]
  have hq : r = traceBase q := by
    funext i
    fin_cases i <;> simp [traceBase,q,hr₀,hr₁]
  have hqn : q ≠ 0 := by
    intro he
    have hh : weighted (traceBase (0 : Fin 3 → ℂ)) = 0 := by
      funext i
      fin_cases i <;> simp [weighted,traceBase]
    rw [hq,he,hh,norm_zero] at hr
    exact zero_ne_one hr
  obtain ⟨j,u,c,hc,hq'⟩ := exists_patch hqn
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ (n := 2) (by decide)
  have hzn : z ≠ 0 := fun h => inv_ne_zero hc (by simpa [h] using hz.symm)
  have hcancel : z^2 * c = 1 := by rw [hz,inv_mul_cancel₀ hc]
  have he : rescale z r = traceBase (patch j u) := by
    rw [hq,hq']
    funext i
    fin_cases i <;> simp [rescale,traceBase,Pi.smul_apply,smul_eq_mul,← mul_assoc,hcancel]
  let p' (n : ℕ) := rescale z (p n)
  have hp' : Tendsto p' atTop (𝓝 (traceBase (patch j u))) :=
    he ▸ continuous_rescale.continuousAt.tendsto.comp (tendsto_const_nhds.prodMk_nhds hp)
  have hl' : Tendsto (graph ∘ p') atTop (𝓝 x) := by
    simpa only [comp_def,p',graph_rescale z _ hzn] using hlim
  have hn' (n : ℕ) : amplitude (p' n) ≠ 0 := by
    change amplitude (rescale z (p n)) ≠ 0
    rw [amplitude_rescale]
    exact smul_ne_zero (pow_ne_zero _ hzn) (hn n)
  obtain ⟨v,hv,hvP⟩ := limit_at_traceless p' (patch j u) (patch_nonzero j u) hn' hp' hl'
  have hP' : x.1 = projector (weighted (traceBase (patch j u))) := by
    rw [← he,weighted_rescale,projector_scale _ (pow_ne_zero _ hzn)]
    exact hP
  exact ⟨j,u,v,hv,Prod.ext hP' hvP⟩

abbrev BoundaryFamily := (Bool × VacuumRoot × Fin 3) ⊕ ((Fin 3 × Fin 2) ⊕ Unit)
abbrev BoundaryParameters := Fin 3 → ℂ

private def tail (u : BoundaryParameters) : Fin 2 → ℂ := fun i => u i.succ

private def boundaryVectors : BoundaryFamily → BoundaryParameters → (Fin 6 → ℂ) × Amp
  | .inl (f,a,j), u =>
      let p := proportional (u 0) a.val
      let a := normal p (pencilNormal (patch j (tail u)))
      if f then (weighted (flip p), a ∘ flipWord) else (weighted p, a)
  | .inr (.inl (j,k)), u =>
      let p := traceBase (patch j (tail u))
      (weighted p, normal p (traceNormal (patch k (fun _ => u 0))))
  | .inr (.inr _), u =>
      let p : Invariants := ![0,1,u 1,u 0,u 2]
      (weighted p, amplitude p)

def boundaryMap (i : BoundaryFamily) (u : BoundaryParameters) : Ambient :=
  (projector (boundaryVectors i u).1,projector (boundaryVectors i u).2)

def boundaryDomain (i : BoundaryFamily) : Set BoundaryParameters :=
  {u | (boundaryVectors i u).1 ≠ 0 ∧ (boundaryVectors i u).2 ≠ 0}

private theorem graph_of_boundary_vectors {x : Ambient} {i : BoundaryFamily} {u : BoundaryParameters}
    (hx : x ∈ source) (he : x = boundaryMap i u) : u ∈ boundaryDomain i := by
  have hs := source_projective hx
  rw [he] at hs
  have h (ι : Type) [Fintype ι] {v : ι → ℂ} (hv : projector v ∈ projective) : v ≠ 0 := by
    rintro rfl
    obtain ⟨p,hp,houter⟩ := hv
    change mass p = 1 at hp
    have hp' : p ≠ 0 := by
      intro hz
      simp [hz,mass] at hp
    obtain ⟨j,hj⟩ : ∃ j, p j ≠ 0 := by
      by_contra! H
      exact hp' (funext H)
    have hh := congrFun (congrFun houter j) j
    simp only [outer,projector,Matrix.smul_apply,Pi.zero_apply,zero_mul,smul_zero] at hh
    exact (mul_ne_zero hj ((map_ne_zero (starRingEnd ℂ)).2 hj)) hh
  exact ⟨h (Fin 6) (v := (boundaryVectors i u).1) hs.1,
    h (Word 7) (v := (boundaryVectors i u).2) hs.2⟩

private theorem proportional_cover (f : Bool) (s : ℂ) (a : VacuumRoot)
    (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    ∃ (j : Fin 3) (u : BoundaryParameters),
      (if f then flipPoint else id)
        (projector (weighted (proportional s a.val)),
          projector (normal (proportional s a.val) (pencilNormal v))) =
        boundaryMap (.inl (f,a,j)) u := by
  obtain ⟨j,w,c,hc,hv'⟩ := exists_patch hv
  let u : BoundaryParameters := Fin.cons s w
  have ht : tail u = w := by funext i; simp [tail,u]
  have h₀ : u 0 = s := by simp [u]
  refine ⟨j,u,?_⟩
  rw [hv',pencilNormal_smul,normal_smul,projector_scale _ hc]
  cases f
  · simp [boundaryMap,boundaryVectors,ht,h₀]
  · simp [boundaryMap,boundaryVectors,ht,h₀,flipPoint,weighted_flip,projector_permute]

private theorem boundary_subset_charts : boundary ⊆ ⋃ i, boundaryMap i '' boundaryDomain i := by
  intro x hx
  have finish (i : BoundaryFamily) (u : BoundaryParameters) (he : x = boundaryMap i u) :
      x ∈ ⋃ j, boundaryMap j '' boundaryDomain j :=
    mem_iUnion.mpr ⟨i,u,graph_of_boundary_vectors hx.1 he,he.symm⟩
  by_cases ht : x.1 0 0 ≠ 0
  · rcases first_chart_cases hx.1 ht with ⟨u,hu,h⟩ | ⟨s,a,v,hv,h⟩
    · exact (hx.2 (by rw [h]; exact chart_mem_ordinary hu)).elim
    · obtain ⟨j,u,hu⟩ := proportional_cover false s a v hv
      exact finish _ u (h.trans hu)
  · have ht' : x.1 0 0 = 0 := not_ne_iff.mp ht
    by_cases hs : x.1 2 2 ≠ 0
    · rcases first_chart_cases (flip_mem_source hx.1) (show (flipPoint x).1 0 0 ≠ 0 from hs) with
        ⟨u,hu,h⟩ | ⟨s,a,v,hv,h⟩
      · have hx' : x = graph (flip (traceChart u)) := by
          rw [graph_flip,← h,flipPoint_involution]
        have ht'' : u 0 = 0 := by
          by_contra he
          apply ht
          rw [hx']
          exact (projector_diag_ne_zero_iff (weighted (flip (traceChart u))) 0).2
            (by simp [weighted,flip,traceChart,he])
        let w : BoundaryParameters := ![u 1,u 2,u 3]
        apply finish (.inr (.inr ())) w
        rw [hx']
        have hh : flip (traceChart u) = (![0,1,w 1,w 0,w 2] : Invariants) := by
          funext i
          fin_cases i <;> simp [flip,traceChart,ht'',w]
        simpa only [graph,boundaryMap,boundaryVectors] using congrArg graph hh
      · obtain ⟨j,u,hu⟩ := proportional_cover true s a v hv
        exact finish _ u ((flipPoint_involution x).symm.trans ((congrArg flipPoint h).trans hu))
    · obtain ⟨j,u,v,hv,h⟩ := traceless_patch_cases hx.1 ht' (not_ne_iff.mp hs)
      obtain ⟨k,w,c,hc,hv'⟩ := exists_patch hv
      let t : BoundaryParameters := Fin.cons (w 0) u
      have htail : tail t = u := by funext i; simp [tail,t]
      have hw : (fun _ : Fin 1 => t 0) = w := by
        funext i
        fin_cases i
        simp [t]
      apply finish (.inr (.inl (j,k))) t
      rw [h,hv',traceNormal_smul,normal_smul,projector_scale _ hc]
      simp [boundaryMap,boundaryVectors,htail,hw]

private theorem differentiable_projector_comp {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ι → ℂ) (hf : Differentiable ℝ f) :
    DifferentiableOn ℝ (fun x => projector (f x)) {x | f x ≠ 0} := by
  have hd (i : ι) : Differentiable ℝ (fun x => f x i) := (differentiable_apply i).fun_comp hf
  have hconj (i : ι) : Differentiable ℝ (fun x => conj (f x i)) :=
    Complex.differentiable_conj.comp (hd i)
  have hm : Differentiable ℝ (fun x => mass (f x)) := by
    unfold mass
    apply Differentiable.fun_sum
    intro i _
    have he (z : ℂ) : Complex.normSq z = (z * conj z).re := by
      simp [Complex.normSq_apply,Complex.mul_re] <;> ring
    simp_rw [he]
    exact Complex.reCLM.differentiable.comp ((hd i).mul (hconj i))
  intro x hx
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  change DifferentiableAt ℝ (fun y => (mass (f y))⁻¹ • (f y i * conj (f y j))) x
  exact (hm.differentiableAt.inv (mass_pos _ hx).ne').smul ((hd i).mul (hconj j)).differentiableAt

private theorem differentiable_boundaryVectors (j : BoundaryFamily) :
    Differentiable ℝ (boundaryVectors j) := by
  have hpatch {n : ℕ} (j : Fin (n + 1)) (u : BoundaryParameters → Fin n → ℂ)
      (hu : Differentiable ℝ u) : Differentiable ℝ (fun x => patch j (u x)) := by
    apply differentiable_pi.mpr
    intro i
    by_cases hi : i = j
    · subst i
      simpa [patch] using (differentiable_const (1 : ℂ) :
        Differentiable ℝ (fun _ : BoundaryParameters => (1 : ℂ)))
    · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hi
      simpa [patch] using (differentiable_apply k).fun_comp hu
  have hnormal (b v : BoundaryParameters → Invariants)
      (hb : Differentiable ℝ b) (hv : Differentiable ℝ v) :
      Differentiable ℝ (fun u => normal (b u) (v u)) := by
    simp_rw [← secant_zero]
    exact (differentiable_secant (𝕜 := ℝ)).comp (hb.prodMk (hv.prodMk (differentiable_const _)))
  have hweight (b : BoundaryParameters → Invariants) (hb : Differentiable ℝ b) :
      Differentiable ℝ (fun u => weighted (b u)) := by
    have hd (i : Fin 5) := (differentiable_apply i).comp hb
    apply differentiable_pi.mpr
    intro i
    fin_cases i <;> simp [weighted] <;> fun_prop
  have htail : Differentiable ℝ (tail : BoundaryParameters → Fin 2 → ℂ) :=
    differentiable_pi.mpr fun i => differentiable_apply i.succ
  rcases j with ⟨f,a,j⟩ | ⟨j,k⟩ | ⟨⟩
  · let b (u : BoundaryParameters) := proportional (u 0) a.val
    let v (u : BoundaryParameters) := pencilNormal (patch j (tail u))
    have hb : Differentiable ℝ b := by
      apply differentiable_pi.mpr
      intro i
      fin_cases i <;> simp [b,proportional] <;> fun_prop
    have hv : Differentiable ℝ v := by
      have hd (i : Fin 3) := (differentiable_apply i).comp (hpatch j tail htail)
      apply differentiable_pi.mpr
      intro i
      fin_cases i <;> simp [v,pencilNormal] <;> fun_prop
    have ha := hnormal b v hb hv
    cases f
    · exact (hweight b hb).prodMk ha
    · have hf : Differentiable ℝ (fun u => flip (b u)) := by
        apply differentiable_pi.mpr
        intro i
        fin_cases i <;> simpa [flip] using (differentiable_apply _).fun_comp hb
      exact (hweight _ hf).prodMk (differentiable_pi.mpr
        fun w => (differentiable_apply (flipWord w)).comp ha)
  · let b (u : BoundaryParameters) := traceBase (patch j (tail u))
    let v (u : BoundaryParameters) := traceNormal (patch k (fun _ => u 0))
    have hb : Differentiable ℝ b := by
      have hd (i : Fin 3) := (differentiable_apply i).comp (hpatch j tail htail)
      apply differentiable_pi.mpr
      intro i
      fin_cases i <;> simp [b,traceBase] <;> fun_prop
    have hv : Differentiable ℝ v := by
      have hc : Differentiable ℝ (fun u : BoundaryParameters => fun _ : Fin 1 => u 0) :=
        differentiable_pi.mpr fun _ => differentiable_apply 0
      have hd (i : Fin 2) := (differentiable_apply i).comp (hpatch k _ hc)
      apply differentiable_pi.mpr
      intro i
      fin_cases i <;> simp [v,traceNormal] <;> fun_prop
    exact (hweight _ hb).prodMk (hnormal _ _ hb hv)
  · let b (u : BoundaryParameters) : Invariants := ![0,1,u 1,u 0,u 2]
    have hb : Differentiable ℝ b := by
      apply differentiable_pi.mpr
      intro i
      fin_cases i <;> simp [b] <;> fun_prop
    exact (hweight _ hb).prodMk ((differentiable_amplitude (𝕜 := ℝ)).fun_comp hb)

theorem boundary_differentiable_cover :
    (∀ i, IsOpen (boundaryDomain i) ∧ DifferentiableOn ℝ (boundaryMap i) (boundaryDomain i)) ∧
      boundary ⊆ ⋃ i, boundaryMap i '' boundaryDomain i := by
  refine ⟨fun i => ?_,boundary_subset_charts⟩
  have h := differentiable_boundaryVectors i
  have hl := differentiable_fst.comp h
  have hr := differentiable_snd.comp h
  exact ⟨(isOpen_ne.preimage hl.continuous).inter (isOpen_ne.preimage hr.continuous),
    ((differentiable_projector_comp _ hl).mono inter_subset_left).prodMk
      ((differentiable_projector_comp _ hr).mono inter_subset_right)⟩

/-- The compact graph boundary has Hausdorff dimension at most six. -/
theorem dimH_boundary_le : dimH boundary ≤ 6 := by
  apply (dimH_mono boundary_differentiable_cover.2).trans
  rw [dimH_iUnion]
  apply iSup_le
  intro i
  calc
    _ ≤ dimH (boundaryDomain i) :=
      (boundary_differentiable_cover.1 i).2.dimH_image_le
    _ ≤ dimH (univ : Set BoundaryParameters) := dimH_mono (subset_univ _)
    _ = 6 := by
      rw [Real.dimH_univ_eq_finrank]
      norm_num [BoundaryParameters,Module.finrank_pi_fintype,Complex.finrank_real_complex]

/-- The complement of the chart in the compact source, with its inherited metric. -/
def chartBoundary : Set Source := chart.targetᶜ

theorem isCompact_chartBoundary : IsCompact chartBoundary :=
  chart.open_target.isClosed_compl.isCompact

theorem dimH_chartBoundary_le : dimH chartBoundary ≤ 6 := by
  have h : Subtype.val '' chartBoundary = boundary := by
    change Subtype.val '' (Subtype.val ⁻¹' ordinary : Set Source)ᶜ = boundary
    rw [← preimage_compl, Subtype.image_preimage_val]
    rfl
  rw [← isometry_subtype_coe.dimH_image, h]
  exact dimH_boundary_le


end

end D5.S3.Quantum.TensorNetworks.SevenSiteGraphBoundary
