/- GID: D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The calibrated separable two-qubit CHSH value is attained and optimal. -/

import D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness
import D5.S3.Quantum.Information.ActualPureQubitGeometry
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

/-! The sharp separable CHSH bound for four imprecisely calibrated binary observables. -/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Kronecker ComplexOrder
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open D5.S3.QuantumBounds.NonlocalityDepthQuantumBound (IsBinaryObservable)
open D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness (Separable)

namespace D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum

/-- The real expectation of the CHSH operator on two qubits. -/
def witness (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (a₁ a₂ b₁ b₂ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (trace (ρ * (a₁ ⊗ₖ b₁ + a₁ ⊗ₖ b₂ + a₂ ⊗ₖ b₁ - a₂ ⊗ₖ b₂))).re

/-- Four binary observables calibrated against the Pauli X and Z targets. -/
def Admissible (ε : ℝ) (a₁ a₂ b₁ b₂ : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  IsBinaryObservable a₁ ∧ IsBinaryObservable a₂ ∧
  IsBinaryObservable b₁ ∧ IsBinaryObservable b₂ ∧
  2 - 4 * ε ≤ (trace (a₁ * qubitX)).re ∧
  2 - 4 * ε ≤ (trace (a₂ * qubitZ)).re ∧
  2 - 4 * ε ≤ (trace (b₁ * qubitX)).re ∧
  2 - 4 * ε ≤ (trace (b₂ * qubitZ)).re

/-- The sharp separable value, with its constant branch past the calibration threshold. -/
def separableValue (ε : ℝ) : ℝ :=
  if ε ≤ 1 / 2 - 1 / (2 * Real.sqrt 2) then
    4 * (1 - 2 * ε) * Real.sqrt (ε * (1 - ε)) +
      Real.sqrt (2 - 16 * ε * (1 - ε) * (1 - 2 * ε) ^ 2)
  else 2

/-- The sharp value is a greatest element of the full set of admissible witness values. -/
def claim : Prop :=
  ∀ ε ∈ Set.Icc (0 : ℝ) 1,
    IsGreatest {w | ∃ ρ a₁ a₂ b₁ b₂, Separable ρ ∧
      Admissible ε a₁ a₂ b₁ b₂ ∧ w = witness ρ a₁ a₂ b₁ b₂} (separableValue ε)

private lemma product_witness (σ τ a₁ a₂ b₁ b₂ : Matrix (Fin 2) (Fin 2) ℂ)
    (hσ : σ.IsHermitian) (hτ : τ.IsHermitian)
    (ha₁ : a₁.IsHermitian) (ha₂ : a₂.IsHermitian)
    (hb₁ : b₁.IsHermitian) (hb₂ : b₂.IsHermitian) :
    witness (σ ⊗ₖ τ) a₁ a₂ b₁ b₂ =
      (trace (σ * a₁)).re * (trace (τ * b₁)).re +
      (trace (σ * a₁)).re * (trace (τ * b₂)).re +
      (trace (σ * a₂)).re * (trace (τ * b₁)).re -
      (trace (σ * a₂)).re * (trace (τ * b₂)).re := by
  have hr := D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.trace_hermitian_product_real
    (n := Fin 2)
  simp only [witness, Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_kronecker_mul,
    trace_add, trace_sub, trace_kronecker, Complex.add_re, Complex.sub_re, Complex.mul_re,
    hr σ a₁ hσ ha₁, hr σ a₂ hσ ha₂, hr τ b₁ hτ hb₁, hr τ b₂ hτ hb₂,
    mul_zero, sub_zero]

private lemma expectation_interval (σ a : Matrix (Fin 2) (Fin 2) ℂ)
    (hσ : σ.PosSemidef) (htσ : trace σ = 1) (ha : IsBinaryObservable a) :
    |(trace (σ * a)).re| ≤ 1 := by
  have hp := RHLinalg.trace_mul_nonneg_of_posSemidef hσ ha.2.2
  have hm := RHLinalg.trace_mul_nonneg_of_posSemidef hσ ha.2.1
  change 0 ≤ (trace (σ * (1 + a))).re at hp
  change 0 ≤ (trace (σ * (1 - a))).re at hm
  simp only [Matrix.mul_add, Matrix.mul_sub, mul_one, trace_add, trace_sub, htσ,
    Complex.add_re, Complex.sub_re, Complex.one_re] at hp hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma scalar_chsh (a₁ a₂ b₁ b₂ : ℝ)
    (ha₁ : |a₁| ≤ 1) (ha₂ : |a₂| ≤ 1) (hb₁ : |b₁| ≤ 1) (hb₂ : |b₂| ≤ 1) :
    a₁ * b₁ + a₁ * b₂ + a₂ * b₁ - a₂ * b₂ ≤ 2 := by
  have hh : |b₁ + b₂| + |b₁ - b₂| ≤ 2 := by
    rcases abs_le.mp hb₁ with ⟨hb₁l, hb₁u⟩
    rcases abs_le.mp hb₂ with ⟨hb₂l, hb₂u⟩
    rcases le_total 0 (b₁ + b₂) with hp | hp <;>
      rcases le_total 0 (b₁ - b₂) with hm | hm
    · rw [abs_of_nonneg hp, abs_of_nonneg hm]; linarith
    · rw [abs_of_nonneg hp, abs_of_nonpos hm]; linarith
    · rw [abs_of_nonpos hp, abs_of_nonneg hm]; linarith
    · rw [abs_of_nonpos hp, abs_of_nonpos hm]; linarith
  calc
    _ = a₁ * (b₁ + b₂) + a₂ * (b₁ - b₂) := by ring
    _ ≤ |a₁ * (b₁ + b₂)| + |a₂ * (b₁ - b₂)| :=
      add_le_add (le_abs_self _) (le_abs_self _)
    _ ≤ |b₁ + b₂| + |b₁ - b₂| := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) ha₁)
        (mul_le_of_le_one_left (abs_nonneg _) ha₂)
    _ ≤ 2 := hh

private lemma product_upper_small (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hsmall : ε ≤ 1 / 2 - 1 / (2 * Real.sqrt 2))
    (σ τ a₁ a₂ b₁ b₂ : Matrix (Fin 2) (Fin 2) ℂ)
    (hσ : σ.PosSemidef) (htσ : trace σ = 1)
    (hτ : τ.PosSemidef) (htτ : trace τ = 1)
    (ha : Admissible ε a₁ a₂ b₁ b₂) :
    witness (σ ⊗ₖ τ) a₁ a₂ b₁ b₂ ≤ separableValue ε := by
  sorry

private lemma product_upper_two (σ τ a₁ a₂ b₁ b₂ : Matrix (Fin 2) (Fin 2) ℂ)
    (hσ : σ.PosSemidef) (htσ : trace σ = 1)
    (hτ : τ.PosSemidef) (htτ : trace τ = 1)
    (ha₁ : IsBinaryObservable a₁) (ha₂ : IsBinaryObservable a₂)
    (hb₁ : IsBinaryObservable b₁) (hb₂ : IsBinaryObservable b₂) :
    witness (σ ⊗ₖ τ) a₁ a₂ b₁ b₂ ≤ 2 := by
  rw [product_witness σ τ a₁ a₂ b₁ b₂ hσ.isHermitian hτ.isHermitian
    ha₁.1 ha₂.1 hb₁.1 hb₂.1]
  exact scalar_chsh _ _ _ _ (expectation_interval σ a₁ hσ htσ ha₁)
    (expectation_interval σ a₂ hσ htσ ha₂) (expectation_interval τ b₁ hτ htτ hb₁)
    (expectation_interval τ b₂ hτ htτ hb₂)

private lemma convex_extension (a₁ a₂ b₁ b₂ : Matrix (Fin 2) (Fin 2) ℂ) (v : ℝ)
    (h : ∀ σ τ : Matrix (Fin 2) (Fin 2) ℂ,
      σ.PosSemidef → trace σ = 1 → τ.PosSemidef → trace τ = 1 →
      witness (σ ⊗ₖ τ) a₁ a₂ b₁ b₂ ≤ v)
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hρ : Separable ρ) :
    witness ρ a₁ a₂ b₁ b₂ ≤ v := by
  apply convexHull_min (t := {ρ | witness ρ a₁ a₂ b₁ b₂ ≤ v}) ?_ ?_ hρ
  · rintro ρ ⟨σ, τ, hσ, htσ, hτ, htτ, rfl⟩
    exact h σ τ hσ htσ hτ htτ
  · intro ρ hρ σ hσ a b ha hb hab
    change witness (a • ρ + b • σ) a₁ a₂ b₁ b₂ ≤ v
    have he : witness (a • ρ + b • σ) a₁ a₂ b₁ b₂ =
        a * witness ρ a₁ a₂ b₁ b₂ + b * witness σ a₁ a₂ b₁ b₂ := by
      simp only [witness, Matrix.add_mul, Matrix.smul_mul, trace_add, trace_smul,
        Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
    rw [he]
    calc
      _ ≤ a * v + b * v := add_le_add (mul_le_mul_of_nonneg_left hρ ha)
        (mul_le_mul_of_nonneg_left hσ hb)
      _ = v := by rw [← add_mul, hab, one_mul]

private def xz (x z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  x • qubitX + z • qubitZ

private lemma xz_hermitian (x z : ℝ) : (xz x z).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [xz, qubitX, qubitZ]

private lemma xz_binary (x z : ℝ) (h : x ^ 2 + z ^ 2 = 1) :
    IsBinaryObservable (xz x z) := by
  have hs : xz x z ^ 2 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [xz, qubitX, qubitZ, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
    · exact_mod_cast (show z * z + x * x = 1 by nlinarith only [h])
    · ring
    · ring
    · exact_mod_cast (show x * x + z * z = 1 by nlinarith only [h])
  exact ⟨xz_hermitian x z,
    D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Upper.involution_binary _
      (xz_hermitian x z) hs⟩

private lemma xz_calibration (x z : ℝ) :
    (trace (xz x z * qubitX)).re = 2 * x ∧
      (trace (xz x z * qubitZ)).re = 2 * z := by
  constructor <;> simp [xz, qubitX, qubitZ, trace, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private lemma xz_state (x z : ℝ) (h : x ^ 2 + z ^ 2 = 1) :
    ((1 / 2 : ℝ) • (1 + xz x z)).PosSemidef ∧
      trace ((1 / 2 : ℝ) • (1 + xz x z)) = 1 := by
  constructor
  · exact (xz_binary x z h).2.2.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · simp [xz, qubitX, qubitZ, trace, Fin.sum_univ_two]
    ring

private lemma xz_expectation (x z a b : ℝ) :
    (trace (((1 / 2 : ℝ) • (1 + xz x z)) * xz a b)).re = x * a + z * b := by
  simp [xz, qubitX, qubitZ, trace, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private lemma product_separable (σ τ : Matrix (Fin 2) (Fin 2) ℂ)
    (hσ : σ.PosSemidef) (htσ : trace σ = 1)
    (hτ : τ.PosSemidef) (htτ : trace τ = 1) : Separable (σ ⊗ₖ τ) :=
  subset_convexHull ℝ _ ⟨σ, τ, hσ, htσ, hτ, htτ, rfl⟩

private lemma xz_attainment (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ σ : Matrix (Fin 2) (Fin 2) ℂ, σ.PosSemidef ∧ trace σ = 1 ∧
      witness (σ ⊗ₖ σ) (xz c s) (xz s c) (xz c s) (xz s c) =
        2 * c * s + Real.sqrt (1 + (c ^ 2 - s ^ 2) ^ 2) := by
  let d := c ^ 2 - s ^ 2
  let k := Real.sqrt (1 + d ^ 2)
  let u := Real.sqrt ((k + d) ^ 2 + 1)
  have hk : k ^ 2 = 1 + d ^ 2 := Real.sq_sqrt (by positivity)
  have hu : u ^ 2 = (k + d) ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have hu0 : 0 < u := Real.sqrt_pos.mpr (by positivity)
  let x := (k + d) / u
  let z := 1 / u
  have hxz : x ^ 2 + z ^ 2 = 1 := by
    dsimp [x, z]
    field_simp
    nlinarith only [hu]
  have hid : d * (k + d) ^ 2 + 2 * (k + d) - d = k * ((k + d) ^ 2 + 1) := by
    linear_combination -(d + k) * hk
  have hev : d * x ^ 2 + 2 * x * z - d * z ^ 2 = k := by
    calc
      _ = (d * (k + d) ^ 2 + 2 * (k + d) - d) / u ^ 2 := by
        dsimp [x, z]; ring
      _ = k := by rw [hid, ← hu]; field_simp
  let σ := (1 / 2 : ℝ) • (1 + xz x z)
  have hσ := xz_state x z hxz
  refine ⟨σ, hσ.1, hσ.2, ?_⟩
  rw [product_witness σ σ _ _ _ _ hσ.1.isHermitian hσ.1.isHermitian
    (xz_hermitian c s) (xz_hermitian s c) (xz_hermitian c s) (xz_hermitian s c)]
  dsimp only [σ]
  simp only [xz_expectation]
  calc
    _ = (2 * c * s) * (x ^ 2 + z ^ 2) +
        (c ^ 2 - s ^ 2) * (x ^ 2 - z ^ 2) + 2 * x * z * (c ^ 2 + s ^ 2) := by ring
    _ = 2 * c * s + k := by rw [hxz, hcs]; dsimp [d] at hev; nlinarith only [hev]
    _ = _ := rfl

private lemma attainment_small (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hsmall : ε ≤ 1 / 2 - 1 / (2 * Real.sqrt 2)) :
    ∃ ρ a₁ a₂ b₁ b₂, Separable ρ ∧ Admissible ε a₁ a₂ b₁ b₂ ∧
      separableValue ε = witness ρ a₁ a₂ b₁ b₂ := by
  let c := 1 - 2 * ε
  let s := 2 * Real.sqrt (ε * (1 - ε))
  have hroot := Real.sq_sqrt (mul_nonneg hε.1 (sub_nonneg.mpr hε.2))
  have hcs : c ^ 2 + s ^ 2 = 1 := by dsimp [c, s]; nlinarith only [hroot]
  obtain ⟨σ, hσ, htσ, hw⟩ := xz_attainment c s hcs
  have hc : 2 - 4 * ε = 2 * c := by dsimp [c]; ring
  have hrad : 2 - 16 * ε * (1 - ε) * (1 - 2 * ε) ^ 2 =
      1 + (c ^ 2 - s ^ 2) ^ 2 := by
    have he : s ^ 2 = 4 * ε * (1 - ε) := by dsimp [s]; nlinarith only [hroot]
    calc
      _ = 2 - 4 * c ^ 2 * s ^ 2 := by rw [he]; dsimp [c]; ring
      _ = _ := by linear_combination -(c ^ 2 + s ^ 2 + 1) * hcs
  have hca := xz_calibration c s
  have hcb := xz_calibration s c
  refine ⟨σ ⊗ₖ σ, xz c s, xz s c, xz c s, xz s c,
    product_separable σ σ hσ htσ hσ htσ,
    ⟨xz_binary c s hcs, xz_binary s c (by linarith only [hcs]),
      xz_binary c s hcs, xz_binary s c (by linarith only [hcs]), ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hca.1, hc]
  · rw [hcb.2, hc]
  · rw [hca.1, hc]
  · rw [hcb.2, hc]
  · rw [hw, separableValue, if_pos hsmall, hrad]
    dsimp [c, s]
    ring

private lemma attainment_large (ε : ℝ)
    (hlarge : 1 / 2 - 1 / (2 * Real.sqrt 2) < ε) :
    ∃ ρ a₁ a₂ b₁ b₂, Separable ρ ∧ Admissible ε a₁ a₂ b₁ b₂ ∧
      separableValue ε = witness ρ a₁ a₂ b₁ b₂ := by
  let k : ℝ := 1 / Real.sqrt 2
  have hk : k ^ 2 + k ^ 2 = 1 := by
    dsimp [k]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hc : 2 - 4 * ε ≤ 2 * k := by
    have he : 1 / (2 * Real.sqrt 2) = k / 2 := by dsimp [k]; ring
    rw [he] at hlarge
    linarith
  let σ := (1 / 2 : ℝ) • (1 + xz k k)
  have hσ := xz_state k k hk
  have ha := xz_binary k k hk
  have hcal := xz_calibration k k
  refine ⟨σ ⊗ₖ σ, xz k k, xz k k, xz k k, xz k k,
    product_separable σ σ hσ.1 hσ.2 hσ.1 hσ.2,
    ⟨ha, ha, ha, ha, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [hcal.1] using hc
  · simpa only [hcal.2] using hc
  · simpa only [hcal.1] using hc
  · simpa only [hcal.2] using hc
  · rw [separableValue, if_neg (not_le.mpr hlarge),
      product_witness σ σ _ _ _ _ hσ.1.isHermitian hσ.1.isHermitian ha.1 ha.1 ha.1 ha.1]
    have hm : (trace (σ * xz k k)).re = 1 := by
      rw [xz_expectation]
      nlinarith only [hk]
    rw [hm]
    norm_num

theorem result : claim := by
  intro ε hε
  constructor
  · by_cases hs : ε ≤ 1 / 2 - 1 / (2 * Real.sqrt 2)
    · exact attainment_small ε hε hs
    · exact attainment_large ε (lt_of_not_ge hs)
  · rintro w ⟨ρ, a₁, a₂, b₁, b₂, hρ, ha, rfl⟩
    apply convex_extension a₁ a₂ b₁ b₂ (separableValue ε) _ ρ hρ
    intro σ τ hσ htσ hτ htτ
    by_cases hs : ε ≤ 1 / 2 - 1 / (2 * Real.sqrt 2)
    · exact product_upper_small ε hε hs σ τ a₁ a₂ b₁ b₂ hσ htσ hτ htτ ha
    · rw [separableValue, if_neg hs]
      exact product_upper_two σ τ a₁ a₂ b₁ b₂ hσ htσ hτ htτ
        ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1

end D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum
