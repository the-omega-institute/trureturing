/- GID: D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The calibrated separable two-qubit CHSH value is attained and optimal. -/

import D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness
import D5.S3.Quantum.Measurement.FourQubitParentConstruction

/-! The sharp separable CHSH bound for four imprecisely calibrated binary observables.

The calibrated Bloch support bound dominates each pair of local expectations by an ellipse.
Its scalar CHSH bound extends from product states to their real convex hull. Explicit product
states attain both branches of the value in Morelli–Yamasaki–Huber–Tavakoli, arXiv:2202.13131v2.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Kronecker ComplexOrder
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open D5.S3.QuantumBounds.NonlocalityDepthQuantumBound (IsBinaryObservable)
open D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness (Separable)
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum (bloch)
open D5.S3.Quantum.Measurement.FourQubitParentConstruction
  (B scalarB B_formula B_neg scalarB_posSemidef_iff
    hermitian_decomposition trace_B_mul)

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
  simp only [witness.eq_1, Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_kronecker_mul,
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

private lemma pair_cauchy (u v w z : ℝ) (hu : u ^ 2 + v ^ 2 = 1) :
    (u * w + v * z) ^ 2 ≤ w ^ 2 + z ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (![u, v] : Fin 2 → ℝ) ![w, z]
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hu, one_mul] using h

private lemma ellipse_chsh (c s u v w z : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hcs : c ^ 2 + s ^ 2 = 1) (hu : u ^ 2 + v ^ 2 = 1) (hw : w ^ 2 + z ^ 2 = 1) :
    |(c * u + s * v) * (c * w + s * z) +
      (c * u + s * v) * (s * w + c * z) +
      (s * u + c * v) * (c * w + s * z) -
      (s * u + c * v) * (s * w + c * z)| ≤
        2 * c * s + Real.sqrt (1 + (c ^ 2 - s ^ 2) ^ 2) := by
  let d := c ^ 2 - s ^ 2
  have h0 : |u * w + v * z| ≤ 1 :=
    abs_le_of_sq_le_sq (by simpa only [hw, one_pow] using pair_cauchy u v w z hu)
      (by norm_num)
  have he : (d * w + z) ^ 2 + (w - d * z) ^ 2 = 1 + d ^ 2 := by
    linear_combination (1 + d ^ 2) * hw
  have h1 : |u * (d * w + z) + v * (w - d * z)| ≤ Real.sqrt (1 + d ^ 2) := by
    apply abs_le_of_sq_le_sq _ (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt (by positivity)]
    exact (pair_cauchy u v _ _ hu).trans_eq he
  have hr : 0 ≤ 2 * c * s := by positivity
  calc
    _ = |(2 * c * s) * (u * w + v * z) +
        u * (d * w + z) + v * (w - d * z)| := by
      congr 1; dsimp [d]; linear_combination (u * z + v * w) * hcs
    _ ≤ |(2 * c * s) * (u * w + v * z)| +
        |u * (d * w + z) + v * (w - d * z)| := by
      rw [add_assoc]
      exact abs_add_le _ _
    _ ≤ _ := by rw [abs_mul, abs_of_nonneg hr]; nlinarith only [h0, h1, hr]

private lemma interval_affine (x a b d k : ℝ) (hx : |x| ≤ a)
    (hl : -a * b + d ≤ k) (hu : a * b + d ≤ k) : x * b + d ≤ k := by
  rcases abs_le.mp hx with ⟨hxl, hxu⟩
  by_cases hb : 0 ≤ b
  · linarith only [mul_le_mul_of_nonneg_right hxu hb, hu]
  · linarith only [mul_le_mul_of_nonpos_right hxl (le_of_not_ge hb), hl]

private lemma rectangle_chsh (a₁ a₂ b₁ b₂ a b c d k : ℝ)
    (ha₁ : |a₁| ≤ a) (ha₂ : |a₂| ≤ b) (hb₁ : |b₁| ≤ c) (hb₂ : |b₂| ≤ d)
    (h : ∀ x y z t : ℝ, (x = -a ∨ x = a) → (y = -b ∨ y = b) →
      (z = -c ∨ z = c) → (t = -d ∨ t = d) → x * z + x * t + y * z - y * t ≤ k) :
    a₁ * b₁ + a₁ * b₂ + a₂ * b₁ - a₂ * b₂ ≤ k := by
  have step₁ (x y z : ℝ) (hx : x = -a ∨ x = a) (hy : y = -b ∨ y = b)
      (hz : z = -c ∨ z = c) : x * z + x * b₂ + y * z - y * b₂ ≤ k := by
    have hl := h x y z (-d) hx hy hz (Or.inl rfl)
    have hu := h x y z d hx hy hz (Or.inr rfl)
    have hh := interval_affine b₂ d (x - y) ((x + y) * z) k hb₂
      (by nlinarith only [hl]) (by nlinarith only [hu])
    nlinarith only [hh]
  have step₂ (x y : ℝ) (hx : x = -a ∨ x = a) (hy : y = -b ∨ y = b) :
      x * b₁ + x * b₂ + y * b₁ - y * b₂ ≤ k := by
    have hl := step₁ x y (-c) hx hy (Or.inl rfl)
    have hu := step₁ x y c hx hy (Or.inr rfl)
    have hh := interval_affine b₁ c (x + y) ((x - y) * b₂) k hb₁
      (by nlinarith only [hl]) (by nlinarith only [hu])
    nlinarith only [hh]
  have step₃ (x : ℝ) (hx : x = -a ∨ x = a) :
      x * b₁ + x * b₂ + a₂ * b₁ - a₂ * b₂ ≤ k := by
    have hl := step₂ x (-b) hx (Or.inl rfl)
    have hu := step₂ x b hx (Or.inr rfl)
    have hh := interval_affine a₂ b (b₁ - b₂) (x * (b₁ + b₂)) k ha₂
      (by nlinarith only [hl]) (by nlinarith only [hu])
    nlinarith only [hh]
  have hl := step₃ (-a) (Or.inl rfl)
  have hu := step₃ a (Or.inr rfl)
  have hh := interval_affine a₁ a (b₁ + b₂) (a₂ * (b₁ - b₂)) k ha₁
    (by nlinarith only [hl]) (by nlinarith only [hu])
  nlinarith only [hh]

private lemma dominated_ellipse_chsh (a₁ a₂ b₁ b₂ c s u v w z : ℝ)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hu : u ^ 2 + v ^ 2 = 1) (hw : w ^ 2 + z ^ 2 = 1)
    (ha₁ : |a₁| ≤ c * u + s * v) (ha₂ : |a₂| ≤ s * u + c * v)
    (hb₁ : |b₁| ≤ c * w + s * z) (hb₂ : |b₂| ≤ s * w + c * z) :
    a₁ * b₁ + a₁ * b₂ + a₂ * b₁ - a₂ * b₂ ≤
      2 * c * s + Real.sqrt (1 + (c ^ 2 - s ^ 2) ^ 2) := by
  apply rectangle_chsh _ _ _ _ _ _ _ _ _ ha₁ ha₂ hb₁ hb₂
  intro x y p q hx hy hp hq
  have h0 := abs_le.mp (ellipse_chsh c s u v w z hc hs hcs hu hw)
  have h1 := abs_le.mp (ellipse_chsh c s u v z w hc hs hcs hu (by linarith only [hw]))
  have h2 := abs_le.mp (ellipse_chsh c s v u w z hc hs hcs (by linarith only [hu]) hw)
  have h3 := abs_le.mp (ellipse_chsh c s v u z w hc hs
    hcs (by linarith only [hu]) (by linarith only [hw]))
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
    nlinarith only [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

private lemma observable_coordinates (σ a : Matrix (Fin 2) (Fin 2) ℂ)
    (hσ : σ.IsHermitian) (htσ : trace σ = 1) (ha : IsBinaryObservable a) :
    ∃ (t : ℝ) (v : EuclideanSpace ℝ (Fin 3)), |t| + ‖v‖ ≤ 1 ∧
      (trace (a * qubitX)).re = 2 * v 0 ∧ (trace (a * qubitZ)).re = 2 * v 2 ∧
      (trace (σ * a)).re = t + inner ℝ v (bloch σ) := by
  let t := (trace a).re / 2
  let v := (1 / 2 : ℝ) • bloch a
  have he : a = scalarB t v := hermitian_decomposition a ha.1
  have hp : 1 + a = scalarB (1 + t) v := by
    rw [he]
    simp only [scalarB, Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]
    abel
  have hm : 1 - a = scalarB (1 - t) (-v) := by
    rw [he]
    simp only [scalarB, B_neg, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    abel
  have hpv : ‖v‖ ≤ 1 + t := by
    apply (scalarB_posSemidef_iff _ _).mp
    rw [← hp]; exact ha.2.2
  have hmv : ‖v‖ ≤ 1 - t := by
    have hh := (scalarB_posSemidef_iff _ _).mp (hm ▸ ha.2.1)
    simpa only [norm_neg] using hh
  refine ⟨t, v, ?_, ?_, ?_, ?_⟩
  · rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]; linarith only [hmv]
    · rw [abs_of_nonpos ht]; linarith only [hpv]
  · rw [he]
    simp [scalarB, B_formula, qubitX, trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · rw [he]
    simp [scalarB, B_formula, qubitZ, trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · have hb (w : EuclideanSpace ℝ (Fin 3)) : trace (B w) = 0 := by
      simp [B_formula, trace_fin_two]
    conv_lhs => rw [hermitian_decomposition σ hσ, htσ, he]
    simp only [scalarB, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      trace_add, trace_smul, one_mul, mul_one, trace_B_mul, hb]
    simp [inner_smul_left, real_inner_comm]

private lemma cap_support (c s u k t : ℝ) (v n : EuclideanSpace ℝ (Fin 3)) (i : Fin 3)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hk : 0 ≤ k)
    (hcs : c ^ 2 + s ^ 2 = 1) (huk : u ^ 2 + k ^ 2 = 1)
    (huc : u ≤ c) (hsk : s ≤ k) (hbudget : |t| + ‖v‖ ≤ 1)
    (hcal : c ≤ v i) (hn : ‖n‖ ≤ 1) (hcoord : |n i| ≤ u) :
    |t + inner ℝ v n| ≤ c * u + s * k := by
  let e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single i 1
  by_cases hs0 : s = 0
  · have hc1 : c = 1 := by nlinarith only [hcs, hs0, hc]
    have hv : ‖v‖ ≤ 1 := by linarith only [hbudget, abs_nonneg t]
    have hi : v i ≤ ‖v‖ := (le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i)
    have hv1 : ‖v‖ = 1 := by rw [hc1] at hcal; linarith only [hcal, hi, hv]
    have hit : v i = 1 := by rw [hc1] at hcal; linarith only [hcal, hi, hv]
    have ht : t = 0 := abs_eq_zero.mp (by linarith only [hbudget, hv1, abs_nonneg t])
    have he : v = e := by
      have hh : ‖v - e‖ ^ 2 = 0 := by
        rw [norm_sub_sq_real]
        simp [e, hv1, hit, EuclideanSpace.inner_single_right]
        norm_num
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hh))
    simpa [ht, he, e, hs0, hc1, EuclideanSpace.inner_single_left] using hcoord
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    let γ := c * k - s * u
    have hγ : 0 ≤ γ := by
      dsimp [γ]
      nlinarith only [mul_nonneg hc (sub_nonneg.mpr hsk),
        mul_nonneg hs (sub_nonneg.mpr huc)]
    have hid : s ^ 2 + 2 * s * γ * u + γ ^ 2 = k ^ 2 := by
      dsimp [γ]
      linear_combination k ^ 2 * hcs - s ^ 2 * huk
    have dual (m : EuclideanSpace ℝ (Fin 3)) (hm : ‖m‖ ≤ 1) (hmi : m i ≤ u) :
        s * inner ℝ v m ≤ ‖v‖ * k - c * γ := by
      let z := s • m + γ • e
      have hmsq : ‖m‖ ^ 2 ≤ 1 := by nlinarith only [hm, norm_nonneg m]
      have hzsq : ‖z‖ ^ 2 ≤ k ^ 2 := by
        have h₁ := mul_le_mul_of_nonneg_left hmsq (sq_nonneg s)
        have h₂ := mul_le_mul_of_nonneg_left hmi
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs) hγ)
        simp only [z, norm_add_sq_real, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs,
          abs_of_nonneg hγ, inner_smul_left, inner_smul_right,
          EuclideanSpace.inner_single_right, e, one_mul, starRingEnd_apply, star_trivial]
        simp only [PiLp.norm_single, Real.norm_eq_abs, abs_one, mul_one]
        nlinarith only [h₁, h₂, hid]
      have hz : ‖z‖ ≤ k := by nlinarith only [hzsq, norm_nonneg z, hk]
      have hh := (real_inner_le_norm v z).trans
        (mul_le_mul_of_nonneg_left hz (norm_nonneg v))
      have hcalγ := mul_le_mul_of_nonneg_left hcal hγ
      simp only [z, inner_add_right, inner_smul_right, e,
        EuclideanSpace.inner_single_right, one_mul, starRingEnd_apply, star_trivial] at hh
      nlinarith only [hh, hcalγ]
    have hp := dual n hn (abs_le.mp hcoord).2
    have hm := dual (-n) (by simpa only [norm_neg] using hn)
      (by simpa only [PiLp.neg_apply, neg_neg] using neg_le_neg (abs_le.mp hcoord).1)
    simp only [inner_neg_right] at hm
    have hv : s * |inner ℝ v n| ≤ ‖v‖ * k - c * γ := by
      rcases le_total 0 (inner ℝ v n) with hi | hi
      · rw [abs_of_nonneg hi]; exact hp
      · rw [abs_of_nonpos hi]; linarith only [hm]
    have ht := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsk) (abs_nonneg t)
    have hb := mul_le_mul_of_nonneg_right hbudget hk
    have ha := mul_le_mul_of_nonneg_left (abs_add_le t (inner ℝ v n)) hs
    have hcsk := congrArg (fun x : ℝ => x * k) hcs
    have hh : s * |t + inner ℝ v n| ≤ s * (c * u + s * k) := by
      dsimp [γ] at hv
      nlinarith only [hv, ht, hb, ha, hcsk]
    nlinarith only [hh, hspos]

private lemma local_ellipse_domination (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hsc : s ≤ c) (hcs : c ^ 2 + s ^ 2 = 1)
    (σ a₁ a₂ : Matrix (Fin 2) (Fin 2) ℂ) (hσ : σ.PosSemidef) (htσ : trace σ = 1)
    (ha₁ : IsBinaryObservable a₁) (ha₂ : IsBinaryObservable a₂)
    (hcal₁ : 2 * c ≤ (trace (a₁ * qubitX)).re)
    (hcal₂ : 2 * c ≤ (trace (a₂ * qubitZ)).re) :
    ∃ u v : ℝ, u ^ 2 + v ^ 2 = 1 ∧
      |(trace (σ * a₁)).re| ≤ c * u + s * v ∧
      |(trace (σ * a₂)).re| ≤ s * u + c * v := by
  let n := bloch σ
  have hn : ‖n‖ ≤ 1 := by
    simpa only [htσ, Complex.one_re] using
      D5.S3.Quantum.Information.ActualPureQubitCostInfimum.norm_bloch_le_trace_of_posSemidef σ hσ
  have hnn : n 0 ^ 2 + n 2 ^ 2 ≤ 1 := by
    have he := EuclideanSpace.real_norm_sq_eq n
    simp only [Fin.sum_univ_three] at he
    nlinarith only [he, hn, norm_nonneg n, sq_nonneg (n 1)]
  obtain ⟨t₁, v₁, hbudget₁, hx₁, _, hexp₁⟩ := observable_coordinates σ a₁ hσ.isHermitian htσ ha₁
  obtain ⟨t₂, v₂, hbudget₂, _, hz₂, hexp₂⟩ := observable_coordinates σ a₂ hσ.isHermitian htσ ha₂
  have hcalv₁ : c ≤ v₁ 0 := by linarith only [hcal₁, hx₁]
  have hcalv₂ : c ≤ v₂ 2 := by linarith only [hcal₂, hz₂]
  have support₁ (u v : ℝ) (hv : 0 ≤ v) (huv : u ^ 2 + v ^ 2 = 1)
      (huc : u ≤ c) (hsv : s ≤ v) (hcoord : |n 0| ≤ u) :
      |(trace (σ * a₁)).re| ≤ c * u + s * v := by
    rw [hexp₁]
    exact cap_support c s u v t₁ v₁ n 0 hc hs hv
      hcs huv huc hsv hbudget₁ hcalv₁ hn hcoord
  have support₂ (u v : ℝ) (hv : 0 ≤ v) (huv : u ^ 2 + v ^ 2 = 1)
      (huc : u ≤ c) (hsv : s ≤ v) (hcoord : |n 2| ≤ u) :
      |(trace (σ * a₂)).re| ≤ c * u + s * v := by
    rw [hexp₂]
    exact cap_support c s u v t₂ v₂ n 2 hc hs hv
      hcs huv huc hsv hbudget₂ hcalv₂ hn hcoord
  by_cases hx : c ≤ |n 0|
  · have hz : |n 2| ≤ s := by
      nlinarith only [hnn, hcs, hx, hs, hc, abs_nonneg (n 0), abs_nonneg (n 2),
        sq_abs (n 0), sq_abs (n 2)]
    refine ⟨c, s, hcs, ?_, ?_⟩
    · nlinarith only [hcs, expectation_interval σ a₁ hσ htσ ha₁]
    · have hh := support₂ s c hc (by linarith only [hcs]) hsc hsc hz
      nlinarith only [hh]
  · by_cases hz : c ≤ |n 2|
    · have hx : |n 0| ≤ s := by
        nlinarith only [hnn, hcs, hz, hs, hc, abs_nonneg (n 0), abs_nonneg (n 2),
          sq_abs (n 0), sq_abs (n 2)]
      refine ⟨s, c, by linarith only [hcs], ?_, ?_⟩
      · exact support₁ s c hc (by linarith only [hcs]) hsc hsc hx
      · nlinarith only [hcs, expectation_interval σ a₂ hσ htσ ha₂]
    · let u := max |n 0| s
      let v := Real.sqrt (1 - u ^ 2)
      have hu : 0 ≤ u := (abs_nonneg _).trans (le_max_left _ _)
      have huc : u ≤ c := max_le (le_of_not_ge hx) hsc
      have hsu : s ≤ u := le_max_right _ _
      have hun : u ^ 2 + n 2 ^ 2 ≤ 1 := by
        by_cases hx0 : |n 0| ≤ s
        · dsimp only [u]; rw [max_eq_right hx0]
          nlinarith only [hcs, le_of_not_ge hz, abs_nonneg (n 2), hc, sq_abs (n 2)]
        · dsimp only [u]; rw [max_eq_left (le_of_not_ge hx0), sq_abs]
          exact hnn
      have hv : 0 ≤ v := Real.sqrt_nonneg _
      have hv2 : v ^ 2 = 1 - u ^ 2 := Real.sq_sqrt (by nlinarith only [hun, sq_nonneg (n 2)])
      have huv : u ^ 2 + v ^ 2 = 1 := by linarith only [hv2]
      have hvc : v ≤ c := by nlinarith only [huv, hcs, hsu, hc, hu, hv, hs]
      have hsv : s ≤ v := by nlinarith only [huv, hcs, huc, hc, hu, hv, hs]
      have hnv : |n 2| ≤ v := by
        nlinarith only [hun, huv, sq_abs (n 2), abs_nonneg (n 2), hv]
      refine ⟨u, v, huv, support₁ u v hv huv huc hsv (le_max_left _ _), ?_⟩
      have hh := support₂ v u hu (by linarith only [huv]) hvc hsu hnv
      nlinarith only [hh]

private lemma product_upper_small (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hsmall : ε ≤ 1 / 2 - 1 / (2 * Real.sqrt 2))
    (σ τ a₁ a₂ b₁ b₂ : Matrix (Fin 2) (Fin 2) ℂ)
    (hσ : σ.PosSemidef) (htσ : trace σ = 1)
    (hτ : τ.PosSemidef) (htτ : trace τ = 1)
    (ha : Admissible ε a₁ a₂ b₁ b₂) :
    witness (σ ⊗ₖ τ) a₁ a₂ b₁ b₂ ≤ separableValue ε := by
  let c := 1 - 2 * ε
  let s := 2 * Real.sqrt (ε * (1 - ε))
  have hroot := Real.sq_sqrt (mul_nonneg hε.1 (sub_nonneg.mpr hε.2))
  have hc : 0 ≤ c := by
    have hp : 0 < 1 / (2 * Real.sqrt 2) := by positivity
    dsimp [c]; linarith only [hsmall, hp]
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hcs : c ^ 2 + s ^ 2 = 1 := by dsimp [c, s]; nlinarith only [hroot]
  have hsc : s ≤ c := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hp := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    have hcc : 1 / Real.sqrt 2 ≤ c := by
      have he : 1 / (2 * Real.sqrt 2) = (1 / Real.sqrt 2) / 2 := by ring
      rw [he] at hsmall
      dsimp [c]; linarith only [hsmall]
    have hmul : 1 ≤ c * Real.sqrt 2 := (div_le_iff₀ hp).mp hcc
    have hcc2 : 1 ≤ 2 * c ^ 2 := by
      have hh := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (mul_nonneg hc hp.le)).mpr hmul
      rw [mul_pow, hsq] at hh
      nlinarith only [hh]
    nlinarith only [hcs, hcc2, hc, hs]
  have hcal : 2 - 4 * ε = 2 * c := by dsimp [c]; ring
  obtain ⟨u, v, huv, ha₁, ha₂⟩ := local_ellipse_domination c s hc hs hsc hcs
    σ a₁ a₂ hσ htσ ha.1 ha.2.1 (by simpa only [← hcal] using ha.2.2.2.2.1)
      (by simpa only [← hcal] using ha.2.2.2.2.2.1)
  obtain ⟨w, z, hwz, hb₁, hb₂⟩ := local_ellipse_domination c s hc hs hsc hcs
    τ b₁ b₂ hτ htτ ha.2.2.1 ha.2.2.2.1
      (by simpa only [← hcal] using ha.2.2.2.2.2.2.1)
      (by simpa only [← hcal] using ha.2.2.2.2.2.2.2)
  have hrad : 2 - 16 * ε * (1 - ε) * (1 - 2 * ε) ^ 2 =
      1 + (c ^ 2 - s ^ 2) ^ 2 := by
    have he : s ^ 2 = 4 * ε * (1 - ε) := by dsimp [s]; nlinarith only [hroot]
    calc
      _ = 2 - 4 * c ^ 2 * s ^ 2 := by rw [he]; dsimp [c]; ring
      _ = _ := by linear_combination -(c ^ 2 + s ^ 2 + 1) * hcs
  rw [separableValue, if_pos hsmall, hrad,
    product_witness σ τ a₁ a₂ b₁ b₂ hσ.isHermitian hτ.isHermitian
      ha.1.1 ha.2.1.1 ha.2.2.1.1 ha.2.2.2.1.1]
  have he : 4 * (1 - 2 * ε) * Real.sqrt (ε * (1 - ε)) = 2 * c * s := by dsimp [c, s]; ring
  rw [he]
  exact dominated_ellipse_chsh _ _ _ _ c s u v w z hc hs hcs huv hwz ha₁ ha₂ hb₁ hb₂

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
      simp only [witness.eq_1, Matrix.add_mul, Matrix.smul_mul, trace_add, trace_smul,
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
  fin_cases i <;> fin_cases j <;> simp [xz.eq_1, qubitX, qubitZ]

private lemma xz_binary (x z : ℝ) (h : x ^ 2 + z ^ 2 = 1) :
    IsBinaryObservable (xz x z) := by
  have hs : xz x z ^ 2 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [xz.eq_1, qubitX, qubitZ, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
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
  constructor <;> simp [xz.eq_1, qubitX, qubitZ, trace_fin_two] <;> ring

private lemma xz_state (x z : ℝ) (h : x ^ 2 + z ^ 2 = 1) :
    ((1 / 2 : ℝ) • (1 + xz x z)).PosSemidef ∧
      trace ((1 / 2 : ℝ) • (1 + xz x z)) = 1 := by
  constructor
  · exact (xz_binary x z h).2.2.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · simp [xz.eq_1, qubitX, qubitZ, trace_fin_two]

private lemma xz_expectation (x z a b : ℝ) :
    (trace (((1 / 2 : ℝ) • (1 + xz x z)) * xz a b)).re = x * a + z * b := by
  simp [xz.eq_1, qubitX, qubitZ, trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
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
    change ((k + d) / u) ^ 2 + (1 / u) ^ 2 = 1
    rw [div_pow, div_pow, one_pow, ← add_div, ← hu]
    exact div_self (pow_ne_zero 2 (ne_of_gt hu0))
  have hid : d * (k + d) ^ 2 + 2 * (k + d) - d = k * ((k + d) ^ 2 + 1) := by
    linear_combination -(d + k) * hk
  have hev : d * x ^ 2 + 2 * x * z - d * z ^ 2 = k := by
    calc
      _ = (d * (k + d) ^ 2 + 2 * (k + d) - d) / u ^ 2 := by
        dsimp [x, z]; ring
      _ = k := by
        rw [hid, ← hu]
        exact mul_div_cancel_right₀ k (pow_ne_zero 2 (ne_of_gt hu0))
  let σ := (1 / 2 : ℝ) • (1 + xz x z)
  have hσ := xz_state x z hxz
  refine ⟨σ, hσ.1, hσ.2, ?_⟩
  rw [product_witness σ σ _ _ _ _ hσ.1.isHermitian hσ.1.isHermitian
    (xz_hermitian c s) (xz_hermitian s c) (xz_hermitian c s) (xz_hermitian s c)]
  rw [xz_expectation, xz_expectation]
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
