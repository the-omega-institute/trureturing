/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Vacuum and one-photon mixtures form two Wigner-majorization chains. -/
/-
admission_basis: open-problem-resolution (#18571; Proved)
result: proof_shape: bind-only; escape_witness: none; consumers: settling result.
Definitions fockWigner, mixtureWigner, levelFunctional, WignerMajorizes and claim:
  proof_shape: bind-only; escape_witness: none; consumers: result.
Private definition k: proof_shape: bind-only; escape_witness: none;
  consumers: k_cont, h_deriv, k_integrable, concrete_cancel, concrete_rays, mixture_closed.
k_cont: proof_shape: bind-only; escape_witness: none; consumers: concrete_rays.
h_deriv: proof_shape: bind-only; escape_witness: none; consumers: concrete_cancel.
h_integrable: proof_shape: bind-only; escape_witness: none; consumers: k_integrable, concrete_rays.
k_integrable: proof_shape: bind-only; escape_witness: none; consumers: concrete_cancel, concrete_rays.
concrete_cancel: proof_shape: bind-only; escape_witness: none; consumers: concrete_rays.
concrete_rays: proof_shape: bind-only; escape_witness: none; consumers: result.
mixture_closed: proof_shape: bind-only; escape_witness: none; consumers: level_reduction.
level_reduction: proof_shape: bind-only; escape_witness: none; consumers: result.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20140
Direct frozen dependencies: genLaguerre in
  D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality;
  declaration statement_id: sha256:36d2ffef3a187d3a6769cb89e6d335dbe51d43c43d11a375c91235c9ecf9b30f.
The five source definitions retain the expressions recorded in #18571.
No declaration is a finite computation or certified instance; utility is none.
-/
import D5.S3.Analytic.Convexity.DerivativeHingeMajorization
import D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality

set_option autoImplicit false

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization
open MeasureTheory Set Filter
open scoped Topology
open D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality (genLaguerre)

/-- Page 16, Eq. (99): the Wigner function of the `n`-th oscillator eigenstate at the phase-space point
`(x, p)`, `W_{|n⟩}(x,p) = (-1)ⁿ/π · e^{-(x²+p²)} · Lₙ(2(x²+p²))`. -/
noncomputable def fockWigner (n : ℕ) (x p : ℝ) : ℝ :=
  (-1 : ℝ) ^ n / Real.pi * Real.exp (-(x ^ 2 + p ^ 2)) * genLaguerre 0 n (2 * (x ^ 2 + p ^ 2))

/-- Page 16, Eq. (100): `W̃_u = (1 - u) W_{|0⟩} + u W_{|1⟩}`. -/
noncomputable def mixtureWigner (u : ℝ) (x p : ℝ) : ℝ :=
  (1 - u) * fockWigner 0 x p + u * fockWigner 1 x p

/-- Page 16, Eq. (97): `I_t[|W|] = ∫ [|W(r)| - t]₊ dr` over the phase space `ℝ²`. -/
noncomputable def levelFunctional (W : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ r : ℝ × ℝ, max (|W r.1 r.2| - t) 0

/-- Page 16, Result 8 (Proposal 1), Eq. (98): `ρ₁ ≻_W ρ₂` iff `I_t[|W₁|] ≥ I_t[|W₂|]` for all `t ≥ 0`. -/
def WignerMajorizes (W₁ W₂ : ℝ → ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → levelFunctional W₂ t ≤ levelFunctional W₁ t

/-- Section V.A.1: the members of the family `W̃_u` with `1/2 ≤ u ≤ 1` form a Wigner-majorization
chain increasing in `u`, and those with `0 ≤ u ≤ 1/2` form a chain decreasing in `u`. -/
def claim : Prop :=
  (∀ u v : ℝ, 1 / 2 ≤ u → u ≤ v → v ≤ 1 → WignerMajorizes (mixtureWigner v) (mixtureWigner u)) ∧
  (∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ 1 / 2 → WignerMajorizes (mixtureWigner u) (mixtureWigner v))

private noncomputable def k (s : ℝ) : ℝ := (1 - s) * Real.exp (-s)

private lemma k_cont : Continuous k := by unfold k; fun_prop
private lemma h_deriv (s : ℝ) : HasDerivAt (fun s : ℝ => s * Real.exp (-s)) (k s) s := by
  unfold k
  convert (hasDerivAt_id s).mul (((hasDerivAt_id s).neg).exp) using 1 <;> first | rfl | (simp only [Pi.neg_apply, id_eq]; ring)
private lemma h_integrable : IntegrableOn (fun s : ℝ => s * Real.exp (-s)) (Ioi (0 : ℝ)) := by
  simpa only [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_rpow
    (p := 1) (s := 1) (by norm_num) (by norm_num)
private lemma k_integrable : IntegrableOn k (Ioi (0 : ℝ)) := by
  convert (integrableOn_exp_neg_Ioi (0 : ℝ)).sub h_integrable using 1
  funext s
  dsimp [k]
  ring

private lemma concrete_cancel (T : ℝ) :
    (∫ s in Ioi (0 : ℝ), k s * (if T < s * Real.exp (-s) then 1 else 0)) = 0 := by
  apply D5.S3.Analytic.Convexity.DerivativeHingeMajorization.boundary_cancellation (fun s : ℝ => s * Real.exp (-s)) k (continuous_id.mul (Real.continuous_exp.comp continuous_id.neg)) h_deriv k_integrable 1 (by norm_num)
  · intro x hx
    exact mul_nonneg (sub_nonneg.mpr hx.2.le) (Real.exp_pos _).le
  · intro x hx
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.le) (Real.exp_pos _).le
  · simp
  · change Tendsto (fun s : ℝ => s * Real.exp (-s)) atTop (𝓝 0)
    simpa only [pow_one] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1

private lemma concrete_rays (T : ℝ) (hT : 0 ≤ T) :
    MonotoneOn (D5.S3.Analytic.Convexity.DerivativeHingeMajorization.hingeIntegral (fun s : ℝ => s * Real.exp (-s)) k T) (Ici (0 : ℝ)) ∧
    AntitoneOn (D5.S3.Analytic.Convexity.DerivativeHingeMajorization.hingeIntegral (fun s : ℝ => s * Real.exp (-s)) k T) (Iic (0 : ℝ)) := by
  apply D5.S3.Analytic.Convexity.DerivativeHingeMajorization.convex_rays _ (D5.S3.Analytic.Convexity.DerivativeHingeMajorization.hinge_convex (fun s : ℝ => s * Real.exp (-s)) k (continuous_id.mul (Real.continuous_exp.comp continuous_id.neg)) k_cont h_integrable k_integrable T hT)
  intro c
  exact D5.S3.Analytic.Convexity.DerivativeHingeMajorization.hinge_min (fun s : ℝ => s * Real.exp (-s)) k (continuous_id.mul (Real.continuous_exp.comp continuous_id.neg)) k_cont h_integrable k_integrable
    (fun s hs => mul_nonneg hs.le (Real.exp_pos _).le) T c hT (concrete_cancel T)

private lemma mixture_closed (u x p : ℝ) :
    mixtureWigner u x p =
      ((x ^ 2 + p ^ 2) * Real.exp (-(x ^ 2 + p ^ 2)) + (1 - 2 * u) * k (x ^ 2 + p ^ 2)) / Real.pi := by
  simp [mixtureWigner, fockWigner, genLaguerre, Finset.sum_range_succ, k]
  ring

private lemma level_reduction (u t : ℝ) :
    levelFunctional (mixtureWigner u) t = D5.S3.Analytic.Convexity.DerivativeHingeMajorization.hingeIntegral (fun s : ℝ => s * Real.exp (-s)) k (Real.pi * t) (1 - 2 * u) := by
  unfold levelFunctional
  simp_rw [mixture_closed, abs_div, abs_of_pos Real.pi_pos]
  have alg (A : ℝ) : max (|A| / Real.pi - t) 0 =
      (Real.pi)⁻¹ * max (|A| - Real.pi * t) 0 := by
    rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr Real.pi_pos.le)]
    congr 1 <;> field_simp [Real.pi_ne_zero] <;> ring
  simp_rw [alg]
  rw [integral_const_mul, D5.S3.Analytic.Convexity.DerivativeHingeMajorization.radial (fun s : ℝ => max (|s * Real.exp (-s) + (1 - 2 * u) * k s| - Real.pi * t) 0)]
  unfold D5.S3.Analytic.Convexity.DerivativeHingeMajorization.hingeIntegral
  field_simp

theorem result : claim := by
  constructor
  · intro u v hu huv hv t ht
    rw [level_reduction, level_reduction]
    apply (concrete_rays (Real.pi * t) (mul_nonneg Real.pi_pos.le ht)).2
      (show 1 - 2 * v ∈ Iic (0 : ℝ) by apply mem_Iic.mpr; linarith)
      (show 1 - 2 * u ∈ Iic (0 : ℝ) by apply mem_Iic.mpr; linarith)
    linarith
  · intro u v hu huv hv t ht
    rw [level_reduction, level_reduction]
    apply (concrete_rays (Real.pi * t) (mul_nonneg Real.pi_pos.le ht)).1
      (show 1 - 2 * v ∈ Ici (0 : ℝ) by apply mem_Ici.mpr; linarith)
      (show 1 - 2 * u ∈ Ici (0 : ℝ) by apply mem_Ici.mpr; linarith)
    linarith


end D5.S3.Quantum.QuantumChannels.FockAttenuator.VacuumOnePhotonWignerMajorization
