/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTraceNormalLimits
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTraceNormalLimits
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Limits of projectors at the trace-word base locus. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformTracelessNormalInjectivity
import D5.S3.Quantum.TensorNetworks.PeriodicMPSProjectiveCoordinates
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Sequences

/-! Polynomial secants and projective normal limits at the uniform trace base loci. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTraceNormalLimits

open Filter Polynomial
open scoped Topology
open SevenSiteTraceBase
  (Word line proportional pencilNormal traceBase traceNormal differentiable_eval_polynomial
    wordPolynomial)
open PeriodicMPSUniformTraceBase (amplitude normalizedTracePower amplitude_first_eq_zero_iff)
open PeriodicMPSUniformTraceNormalInjectivity (normal proportional_normal_injective)
open PeriodicMPSUniformTracelessNormalInjectivity (traceless_normal_injective)
open PeriodicMPSProjectiveCoordinates (projector projector_scale continuousAt_projector)

-- The ring-map and parity lemmas already quantify over arbitrary words.
open private map_amplitude from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformTraceNormalInjectivity
open private form form_traceless from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteTraceBase

noncomputable section

theorem eval_line_amplitude (n : ℕ) (b v : Fin 5 → ℂ) (l : ℂ) (w : Word n) :
    (amplitude n (line b v) w).eval l = amplitude n (b + l • v) w := by
  rw [← Polynomial.coe_evalRingHom, map_amplitude]
  congr 1
  funext i
  change (line b v i).eval l = (b + l • v) i
  simp only [line, Pi.add_apply, Pi.smul_apply, smul_eq_mul, eval_add, eval_mul, eval_C, eval_X]

/-- The divided difference of the amplitude along a line, evaluated at the line parameter. -/
def secant (n : ℕ) (b v : Fin 5 → ℂ) (l : ℂ) : Word n → ℂ :=
  fun w => ((amplitude n (line b v) w).divX).eval l

@[simp] theorem secant_zero (n : ℕ) (b v : Fin 5 → ℂ) :
    secant n b v 0 = normal n b v := by
  funext w
  simp only [secant, normal, ← coeff_zero_eq_eval_zero, coeff_divX, zero_add]

/-- The exact divided-difference identity, including when the base is off the zero locus. -/
theorem amplitude_sub_eq_smul_secant (n : ℕ) (b v : Fin 5 → ℂ) (l : ℂ) :
    amplitude n (b + l • v) - amplitude n b = l • secant n b v l := by
  funext w
  have h := congrArg (Polynomial.eval l) (X_mul_divX_add (amplitude n (line b v) w))
  have h₀ : (amplitude n (line b v) w).coeff 0 = amplitude n b w := by
    rw [coeff_zero_eq_eval_zero, eval_line_amplitude, zero_smul, add_zero]
  have h' : l * secant n b v l w + amplitude n b w = amplitude n (b + l • v) w := by
    simpa [secant, h₀, eval_line_amplitude] using h
  simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using (eq_sub_of_add_eq h').symm

theorem amplitude_eq_smul_secant (n : ℕ) (b v : Fin 5 → ℂ) (l : ℂ)
    (hb : amplitude n b = 0) :
    amplitude n (b + l • v) = l • secant n b v l := by
  simpa only [hb, sub_zero] using amplitude_sub_eq_smul_secant n b v l

/-- Variables for the base coordinates, direction coordinates, and line parameter. -/
abbrev SecantVariables := Fin 5 ⊕ (Fin 5 ⊕ Unit)

def secantPolynomial {n : ℕ} (w : Word n) : MvPolynomial SecantVariables ℂ :=
  let b : Fin 5 → MvPolynomial SecantVariables ℂ := fun i => MvPolynomial.X (.inl i)
  let v : Fin 5 → MvPolynomial SecantVariables ℂ := fun i => MvPolynomial.X (.inr (.inl i))
  (amplitude n (line b v) w).divX.eval (MvPolynomial.X (.inr (.inr ())))

def secantValues (x : (Fin 5 → ℂ) × (Fin 5 → ℂ) × ℂ) : SecantVariables → ℂ
  | .inl i => x.1 i
  | .inr (.inl i) => x.2.1 i
  | .inr (.inr _) => x.2.2

/-- Each secant coordinate is jointly polynomial in the base, direction, and parameter. -/
theorem secant_eq_eval {n : ℕ} (b v : Fin 5 → ℂ) (l : ℂ) (w : Word n) :
    secant n b v l w = MvPolynomial.eval (secantValues (b, v, l)) (secantPolynomial w) := by
  let f := MvPolynomial.eval (secantValues (b, v, l))
  let p : (MvPolynomial SecantVariables ℂ)[X] := amplitude n (line
    (fun i => MvPolynomial.X (.inl i)) (fun i => MvPolynomial.X (.inr (.inl i)))) w
  have hl : f (MvPolynomial.X (.inr (.inr ()))) = l :=
    MvPolynomial.eval_X (f := secantValues (b, v, l)) _
  have hp : p.map f = amplitude n (line b v) w := by
    rw [← coe_mapRingHom, map_amplitude]
    congr 1
    funext i
    simp [line, f, secantValues]
  have hdiv : p.divX.map f = (p.map f).divX := by
    apply Polynomial.ext
    intro i
    simp only [coeff_map, coeff_divX]
  change ((amplitude n (line b v) w).divX).eval l =
    f (p.divX.eval (MvPolynomial.X (.inr (.inr ()))))
  rw [← eval_map_apply, hl, hdiv, hp]

theorem differentiable_secant (n : ℕ) :
    Differentiable ℂ (fun x : (Fin 5 → ℂ) × (Fin 5 → ℂ) × ℂ => secant n x.1 x.2.1 x.2.2) := by
  apply differentiable_pi.mpr
  intro w
  simp_rw [secant_eq_eval]
  apply differentiable_eval_polynomial
  rintro (i | i | ⟨⟩) <;> simp only [secantValues] <;> fun_prop

theorem continuous_secant (n : ℕ) :
    Continuous (fun x : (Fin 5 → ℂ) × (Fin 5 → ℂ) × ℂ => secant n x.1 x.2.1 x.2.2) :=
  (differentiable_secant n).continuous

private theorem differentiable_amplitude (n : ℕ) : Differentiable ℂ (amplitude (R := ℂ) n) := by
  apply differentiable_pi.mpr
  intro w
  have h (b : Fin 5 → ℂ) :
      MvPolynomial.eval b (amplitude n MvPolynomial.X w) = amplitude n b w := by
    rw [map_amplitude]
    congr 1
    funext i
    exact MvPolynomial.eval_X (f := b) i
  simpa only [h] using differentiable_eval_polynomial (𝕜 := ℂ) (amplitude n MvPolynomial.X w)
    (fun i (b : Fin 5 → ℂ) => b i) (fun i => differentiable_apply i)

/-- The linear coefficient agrees with the derivative in the given direction. -/
theorem normal_eq_fderiv (n : ℕ) (b v : Fin 5 → ℂ) :
    normal n b v = fderiv ℂ (amplitude n) b v := by
  have hline : HasDerivAt (fun l : ℂ => b + l • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add b
  have hcomp : HasDerivAt (fun l : ℂ => amplitude n (b + l • v))
      (fderiv ℂ (amplitude n) b v) 0 := by
    have h := (differentiable_amplitude n b).hasFDerivAt
    exact (show HasFDerivAt (amplitude n) (fderiv ℂ (amplitude n) b) (b + (0 : ℂ) • v) by
      simpa only [zero_smul, add_zero] using h).comp_hasDerivAt 0 hline
  funext w
  have h₁ : HasDerivAt (fun l : ℂ => amplitude n (b + l • v) w) (normal n b v w) 0 := by
    simpa only [eval_line_amplitude, normal, ← coeff_zero_eq_eval_zero, coeff_derivative, zero_add,
      Nat.cast_zero, one_mul, mul_one] using (amplitude n (line b v) w).hasDerivAt 0
  exact h₁.unique (hasDerivAt_pi.mp hcomp w)

theorem normal_add (n : ℕ) (b u v : Fin 5 → ℂ) :
    normal n b (u + v) = normal n b u + normal n b v := by
  simp only [normal_eq_fderiv, map_add]

theorem normal_smul (n : ℕ) (b v : Fin 5 → ℂ) (c : ℂ) :
    normal n b (c • v) = c • normal n b v := by
  simp only [normal_eq_fderiv, map_smul]

@[simp] theorem normal_zero (n : ℕ) (b : Fin 5 → ℂ) : normal n b 0 = 0 := by
  simp [normal_eq_fderiv]

/-- The divided amplitudes converge even when the base and direction both vary. -/
theorem tendsto_secant {ι : Type*} {F : Filter ι} (n : ℕ)
    {b v : ι → Fin 5 → ℂ} {l : ι → ℂ} {b₀ v₀ : Fin 5 → ℂ}
    (hb : Tendsto b F (𝓝 b₀)) (hv : Tendsto v F (𝓝 v₀)) (hl : Tendsto l F (𝓝 0)) :
    Tendsto (fun j => secant n (b j) (v j) (l j)) F (𝓝 (normal n b₀ v₀)) := by
  rw [← secant_zero]
  exact (continuous_secant n).continuousAt.tendsto.comp (hb.prodMk_nhds (hv.prodMk_nhds hl))

/-- Rescaling the amplitudes along a moving zero-locus base yields the normal in the limit. -/
theorem tendsto_rescaled_amplitude {ι : Type*} {F : Filter ι} (n : ℕ)
    {b v : ι → Fin 5 → ℂ} {l : ι → ℂ} {b₀ v₀ : Fin 5 → ℂ}
    (hb : Tendsto b F (𝓝 b₀)) (hv : Tendsto v F (𝓝 v₀)) (hl : Tendsto l F (𝓝 0))
    (hbase : ∀ᶠ j in F, amplitude n (b j) = 0) (hlne : ∀ᶠ j in F, l j ≠ 0) :
    Tendsto (fun j => (l j)⁻¹ • amplitude n (b j + l j • v j)) F (𝓝 (normal n b₀ v₀)) := by
  apply (tendsto_secant n hb hv hl).congr'
  filter_upwards [hbase, hlne] with j hbase hlne
  rw [amplitude_eq_smul_secant _ _ _ _ hbase, inv_smul_smul₀ hlne]

/-- Along a convergent transverse direction, the amplitude eventually defines a ray and its
projector converges to the projector of the normal. -/
theorem tendsto_projector_of_normal {ι : Type*} {F : Filter ι} (n : ℕ)
    {b v : ι → Fin 5 → ℂ} {l : ι → ℂ} {b₀ v₀ : Fin 5 → ℂ}
    (hb : Tendsto b F (𝓝 b₀)) (hv : Tendsto v F (𝓝 v₀)) (hl : Tendsto l F (𝓝 0))
    (hbase : ∀ᶠ j in F, amplitude n (b j) = 0) (hlne : ∀ᶠ j in F, l j ≠ 0)
    (hnormal : normal n b₀ v₀ ≠ 0) :
    (∀ᶠ j in F, amplitude n (b j + l j • v j) ≠ 0) ∧
    Tendsto (fun j => projector (amplitude n (b j + l j • v j))) F
      (𝓝 (projector (normal n b₀ v₀))) := by
  have ht := tendsto_secant n hb hv hl
  constructor
  · filter_upwards [hbase, hlne, ht.eventually_ne hnormal] with j hbase hlne hsecant
    rw [amplitude_eq_smul_secant _ _ _ _ hbase]
    exact smul_ne_zero hlne hsecant
  · apply ((continuousAt_projector hnormal).tendsto.comp ht).congr'
    filter_upwards [hbase, hlne] with j hbase hlne
    simp only [Function.comp_apply, amplitude_eq_smul_secant _ _ _ _ hbase, projector_scale _ hlne]

/-- For a moving zero-locus base and transverse displacement tending to zero, every limit of
the amplitude projectors comes from a nonzero normal direction. -/
theorem lift_limit (n : ℕ) {m : ℕ} (pack : (Fin m → ℂ) → Fin 5 → ℂ)
    (hpack : ∀ (c : ℂ) u, pack (c • u) = c • pack u) (hcont : Continuous pack)
    {b : ℕ → Fin 5 → ℂ} {b₀ : Fin 5 → ℂ} {v : ℕ → Fin m → ℂ}
    (hbase : ∀ᶠ j in atTop, amplitude n (b j) = 0) (hb : Tendsto b atTop (𝓝 b₀))
    (hv : Tendsto v atTop (𝓝 0))
    (hne : ∀ᶠ j in atTop, amplitude n (b j + pack (v j)) ≠ 0)
    (hinj : Function.Injective (fun u => normal n b₀ (pack u)))
    {P : Matrix (Word n) (Word n) ℂ}
    (hP : Tendsto (fun j => projector (amplitude n (b j + pack (v j)))) atTop (𝓝 P)) :
    ∃ u : Fin m → ℂ, u ≠ 0 ∧ normal n b₀ (pack u) ≠ 0 ∧
      P = projector (normal n b₀ (pack u)) := by
  let l (j : ℕ) : ℂ := ↑‖v j‖
  let u (j : ℕ) := (l j)⁻¹ • v j
  have hpack₀ : pack 0 = 0 := by simpa using hpack 0 (0 : Fin m → ℂ)
  have hvne : ∀ᶠ j in atTop, v j ≠ 0 := by
    filter_upwards [hbase, hne] with j hbase hne h
    exact hne (by rw [h, hpack₀, add_zero, hbase])
  have hlne : ∀ᶠ j in atTop, l j ≠ 0 :=
    hvne.mono fun j hj => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hj)
  have hu : ∀ᶠ j in atTop, u j ∈ Metric.sphere (0 : Fin m → ℂ) 1 := by
    filter_upwards [hvne] with j hj
    rw [Metric.mem_sphere, dist_zero_right, show u j = (l j)⁻¹ • v j from rfl,
      norm_smul, norm_inv, show ‖l j‖ = ‖v j‖ by simp [l], inv_mul_cancel₀ (norm_ne_zero_iff.mpr hj)]
  obtain ⟨u₀, hu₀, φ, hφ, huφ⟩ := (isCompact_sphere (0 : Fin m → ℂ) 1).tendsto_subseq' hu.frequently
  have hφtop := hφ.tendsto_atTop
  have hl : Tendsto l atTop (𝓝 0) := by
    have hc : Continuous (fun x : Fin m → ℂ => (↑‖x‖ : ℂ)) :=
      Complex.continuous_ofReal.comp continuous_norm
    simpa only [Function.comp_def, norm_zero, Complex.ofReal_zero] using
      hc.continuousAt.tendsto.comp hv
  have hu₀ne : u₀ ≠ 0 := Metric.ne_of_mem_sphere hu₀ one_ne_zero
  have hnormal : normal n b₀ (pack u₀) ≠ 0 := by
    intro h
    apply hu₀ne
    apply hinj
    simpa only [hpack₀, normal_zero] using h
  have hsum : ∀ᶠ j in atTop, l j • pack (u j) = pack (v j) := by
    filter_upwards [hlne] with j hj
    rw [← hpack, show u j = (l j)⁻¹ • v j from rfl, smul_smul, mul_inv_cancel₀ hj, one_smul]
  have hlim := (tendsto_projector_of_normal n (hb.comp hφtop)
    (hcont.continuousAt.tendsto.comp huφ) (hl.comp hφtop)
    (hφtop.eventually hbase) (hφtop.eventually hlne) hnormal).2
  refine ⟨u₀, hu₀ne, hnormal, tendsto_nhds_unique (hP.comp hφtop) ?_⟩
  apply hlim.congr'
  filter_upwards [hφtop.eventually hsum] with j hj
  simp only [Function.comp_apply, hj]

private theorem traceNormal_smul (c : ℂ) (v : Fin 2 → ℂ) :
    traceNormal (c • v) = c • traceNormal v := by
  funext i
  fin_cases i <;> simp [traceNormal, Pi.smul_apply]

private theorem pencilNormal_smul (c : ℂ) (v : Fin 3 → ℂ) :
    pencilNormal (c • v) = c • pencilNormal v := by
  funext i
  fin_cases i <;> simp [pencilNormal, Pi.smul_apply]

theorem amplitude_traceless (n : ℕ) (hn : Odd n) (q : Fin 3 → ℂ) :
    amplitude n (traceBase q) = 0 := by
  funext w
  have hw : (List.ofFn w).length % 2 = 1 := by simpa using Nat.odd_iff.mp hn
  have h := (form_traceless (q 0) (q 1) (q 2) (List.ofFn w)).2 hw
  change wordPolynomial 0 0 (q 0) (q 1) (q 2) (List.ofFn w) = 0
  unfold wordPolynomial
  rcases hf : form (0 : ℂ) 0 (q 0) (q 1) (q 2) (List.ofFn w) with ⟨u, a, b, c⟩
  simp only [hf] at h
  simp [h.1, h.2]

/-- At the odd traceless base, every projective limit is a nonzero trace-normal ray. -/
theorem limit_at_traceless (n : ℕ) (hn : Odd n) {q : Fin 3 → ℂ} (hq : q ≠ 0)
    {p : ℕ → Fin 5 → ℂ} (hp : Tendsto p atTop (𝓝 (traceBase q)))
    (hne : ∀ᶠ j in atTop, amplitude n (p j) ≠ 0)
    {P : Matrix (Word n) (Word n) ℂ}
    (hP : Tendsto (fun j => projector (amplitude n (p j))) atTop (𝓝 P)) :
    ∃ u : Fin 2 → ℂ, u ≠ 0 ∧ normal n (traceBase q) (traceNormal u) ≠ 0 ∧
      P = projector (normal n (traceBase q) (traceNormal u)) := by
  let b (j : ℕ) := traceBase ![p j 2, p j 3, p j 4]
  let v (j : ℕ) : Fin 2 → ℂ := ![p j 0, p j 1]
  have hsum (j : ℕ) : b j + traceNormal (v j) = p j := by
    funext i
    fin_cases i <;> simp [b, v, traceBase, traceNormal, Pi.add_apply]
  have hcoord (i : Fin 5) := (continuous_apply i).continuousAt.tendsto.comp hp
  have hb : Tendsto b atTop (𝓝 (traceBase q)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i <;> simp [b, traceBase] <;> exact hcoord _
  have hv : Tendsto v atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact hcoord 0
    · exact hcoord 1
  have hc : Continuous traceNormal := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [traceNormal] <;> fun_prop
  have hne' : ∀ᶠ j in atTop, amplitude n (b j + traceNormal (v j)) ≠ 0 :=
    hne.mono fun j hj => (hsum j).symm ▸ hj
  have hP' := hP.congr' (Eventually.of_forall fun j =>
    congrArg (fun x => projector (amplitude n x)) (hsum j).symm)
  have hbase : ∀ᶠ j in atTop, amplitude n (b j) = 0 :=
    Eventually.of_forall fun j => amplitude_traceless n hn ![p j 2, p j 3, p j 4]
  exact lift_limit n traceNormal traceNormal_smul hc hbase hb hv hne'
    (traceless_normal_injective n hn q hq) hP'

/-- In the trace-one chart, every projective limit at a proportional base is a nonzero
determinant and mixed-trace normal ray. -/
theorem limit_at_proportional (n : ℕ) (hn : 2 ≤ n) {s a : ℂ}
    (ha : (normalizedTracePower n).IsRoot a)
    {p : ℕ → Fin 5 → ℂ} (hp : Tendsto p atTop (𝓝 (proportional s a)))
    (ht : ∀ᶠ j in atTop, p j 0 = 1) (hne : ∀ᶠ j in atTop, amplitude n (p j) ≠ 0)
    {P : Matrix (Word n) (Word n) ℂ}
    (hP : Tendsto (fun j => projector (amplitude n (p j))) atTop (𝓝 P)) :
    ∃ u : Fin 3 → ℂ, u ≠ 0 ∧ normal n (proportional s a) (pencilNormal u) ≠ 0 ∧
      P = projector (normal n (proportional s a) (pencilNormal u)) := by
  let b (j : ℕ) := proportional (p j 1) a
  let v (j : ℕ) : Fin 3 → ℂ := ![p j 2 - b j 2, p j 3 - b j 3, p j 4 - b j 4]
  have hbase : ∀ᶠ j in atTop, amplitude n (b j) = 0 :=
    Eventually.of_forall fun j => (amplitude_first_eq_zero_iff n hn _ _ _ _).2 ⟨ha, rfl, rfl⟩
  have hsum : ∀ᶠ j in atTop, b j + pencilNormal (v j) = p j := by
    filter_upwards [ht] with j ht
    funext i
    fin_cases i <;> simp [b, v, pencilNormal, proportional, Pi.add_apply, ht]
  have hb : Tendsto b atTop (𝓝 (proportional s a)) := by
    have hc : Continuous (fun t : ℂ => proportional t a) := by
      apply continuous_pi
      intro i
      fin_cases i <;> simp [proportional] <;> fun_prop
    exact hc.continuousAt.tendsto.comp ((continuous_apply 1).continuousAt.tendsto.comp hp)
  have hv : Tendsto v atTop (𝓝 0) := by
    have hcoord (i : Fin 5) := (continuous_apply i).continuousAt.tendsto.comp (hp.sub hb)
    simp only [sub_self] at hcoord
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact hcoord 2
    · exact hcoord 3
    · exact hcoord 4
  have hc : Continuous pencilNormal := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [pencilNormal] <;> fun_prop
  have hne' : ∀ᶠ j in atTop, amplitude n (b j + pencilNormal (v j)) ≠ 0 := by
    filter_upwards [hsum, hne] with j hsum hne
    rwa [hsum]
  have hP' := hP.congr' (hsum.mono fun j hj => congrArg (fun x => projector (amplitude n x)) hj.symm)
  exact lift_limit n pencilNormal pencilNormal_smul hc hbase hb hv hne'
    (proportional_normal_injective n hn s a ha) hP'

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTraceNormalLimits
