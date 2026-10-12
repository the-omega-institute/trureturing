/- GID: D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/LossyQubitPartialJMTightness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Tightness of the lossy-qubit partial joint-measurability bound. -/

import D5.S3.Quantum.Measurement.FourQubitParentConstruction
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder Matrix MatrixOrder InnerProductSpace
open Matrix Real WithLp RCLike
open D5.S3.Quantum.FiniteDimensional (QubitMatrix)
open D5.S3.Quantum.Measurement.FourQubitParentConstruction
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
  (bloch blochMatrix blochLinear blochMatrix_trace bloch_blochMatrix
    norm_bloch_le_trace_of_posSemidef)
namespace D5.S3.Quantum.Measurement.LossyQubitPartialJMTightness
def effects (η : ℝ) (r : Fin 2 → EuclideanSpace ℝ (Fin 3)) (b : Fin 3) (y : Fin 2) : QubitMatrix :=
  if b = 2 then (1 - η) • (1 : QubitMatrix)
  else η • blochMatrix 1 (if b = 0 then r y else -r y)
def G (y : Fin 2) : Finset (Fin 3) := if y = 0 then {0, 1} else ∅
def starPart (E : Fin 2 → Fin 3 → Fin 2 → QubitMatrix) (W : Fin 2 → QubitMatrix)
    (β : Fin 2) (y : Fin 2) : QubitMatrix :=
  W β - ∑ b ∈ (Finset.univ.filter (fun b => b ∉ G y)), E β b y
def GJointMeasurable (η : ℝ) (r : Fin 2 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ (E : Fin 2 → Fin 3 → Fin 2 → QubitMatrix) (W : Fin 2 → QubitMatrix),
    (∀ y, IsPOVM (fun k : Fin 2 × Fin 3 => E k.1 k.2 y)) ∧
    (∀ β y, (∑ b, E β b y) = W β) ∧
    (∀ b y, effects η r b y = ∑ β, E β b y) ∧
    (∀ β y, (starPart E W β y).PosSemidef) ∧
    (∀ β y b, b ∈ G y → E β b y = if b = β.castSucc then starPart E W β y else 0)
def claim : Prop :=
  ∀ (r₁ r₂ : EuclideanSpace ℝ (Fin 3)) (η : ℝ), ‖r₁‖ = 1 → ‖r₂‖ = 1 → 0 ≤ η → η ≤ 1 →
    GJointMeasurable η ![r₁, r₂] → η * (2 + ‖WithLp.toLp 2 (WithLp.ofLp r₁ ⨯₃ WithLp.ofLp r₂)‖) ≤ 2
private def a0 : QubitMatrix →ₗ[ℝ] ℝ :=
  (1 / 2 : ℝ) • Complex.reLm.comp (Matrix.traceLinearMap (Fin 2) ℝ ℂ)
private def bv : QubitMatrix →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) := (1 / 2 : ℝ) • blochLinear
private theorem noise_difference_bound (F G : QubitMatrix) (δ : ℝ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (hSum : F + G = δ • (1 : QubitMatrix)) :
    ‖bv (F - G)‖ ≤ δ := by
  calc
    ‖bv (F - G)‖ ≤ ‖bv F‖ + ‖bv G‖ := by
      rw [map_sub]
      exact norm_sub_le _ _
    _ ≤ a0 F + a0 G := by
      apply add_le_add
      · simpa [bv.eq_1, a0.eq_1, blochLinear, norm_smul, Real.norm_eq_abs] using
          (mul_le_mul_of_nonneg_left
            (norm_bloch_le_trace_of_posSemidef F hF)
            (by norm_num : (0 : ℝ) ≤ 1 / 2))
      · simpa [bv.eq_1, a0.eq_1, blochLinear, norm_smul, Real.norm_eq_abs] using
          (mul_le_mul_of_nonneg_left
            (norm_bloch_le_trace_of_posSemidef G hG)
            (by norm_num : (0 : ℝ) ≤ 1 / 2))
    _ = δ := by
      rw [← map_add, hSum, map_smul]
      have hone : a0 (1 : QubitMatrix) = 1 := by
        change (1 / 2 : ℝ) * (Matrix.trace (1 : QubitMatrix)).re = 1
        norm_num [Matrix.trace]
      rw [hone, smul_eq_mul, mul_one]
private theorem dominated_projector (r : EuclideanSpace ℝ (Fin 3)) (c : ℝ) (H : QubitMatrix)
    (hr : ‖r‖ = 1) (hH : H.PosSemidef)
    (hR : (c • blochMatrix 1 r - H).PosSemidef) :
    H = (2 * a0 H) • blochMatrix 1 r := by
  let α : ℝ := a0 H
  let a : EuclideanSpace ℝ (Fin 3) := bv H
  let k : ℝ := c / 2
  have ha : ‖a‖ ≤ α := by
    simpa [a, α, bv, a0, blochLinear, norm_smul, Real.norm_eq_abs] using
      (mul_le_mul_of_nonneg_left
        (norm_bloch_le_trace_of_posSemidef H hH)
        (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hka : ‖k • r - a‖ ≤ k - α := by
    have h : ‖bv (c • blochMatrix 1 r - H)‖ ≤ a0 (c • blochMatrix 1 r - H) := by
      simpa [bv.eq_1, a0.eq_1, blochLinear, norm_smul, Real.norm_eq_abs] using
        (mul_le_mul_of_nonneg_left
          (norm_bloch_le_trace_of_posSemidef (c • blochMatrix 1 r - H) hR)
          (by norm_num : (0 : ℝ) ≤ 1 / 2))
    rw [map_sub, map_smul, map_sub, map_smul] at h
    simpa [α, a, k, bv, a0, blochLinear, bloch_blochMatrix, blochMatrix_trace,
      div_eq_mul_inv, smul_smul] using h
  have hkα : 0 ≤ k - α := le_trans (norm_nonneg _) hka
  have hir : ⟪r, a⟫_ℝ ≤ α := by
    calc
      ⟪r, a⟫_ℝ ≤ ‖r‖ * ‖a‖ := real_inner_le_norm _ _
      _ = ‖a‖ := by rw [hr]; simp
      _ ≤ α := ha
  have hirk : α ≤ ⟪r, a⟫_ℝ := by
    have hinnerexpr : ⟪r, k • r - a⟫_ℝ = k - ⟪r, a⟫_ℝ := by
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hr]
      ring
    have hb0 := real_inner_le_norm r (k • r - a)
    have hb : ⟪r, k • r - a⟫_ℝ ≤ ‖k • r - a‖ := by
      simpa [hr] using hb0
    rw [hinnerexpr] at hb
    have hc : k - ⟪r, a⟫_ℝ ≤ k - α := le_trans hb hka
    linarith
  have hia : ⟪r, a⟫_ℝ = α := le_antisymm hir hirk
  have hα : 0 ≤ α := le_trans (norm_nonneg a) ha
  have hnorm : ‖a‖ ≤ ‖α • r‖ := by
    calc
      ‖a‖ ≤ α := ha
      _ = ‖α • r‖ := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα, hr]
  have hinner : re ⟪a, α • r⟫_ℝ = ‖α • r‖ ^ 2 := by
    rw [real_inner_smul_right, real_inner_comm, hia]
    simp [RCLike.re_to_real, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα, hr]
    ring
  have hv : a = α • r :=
    eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ) hnorm hinner
  calc
    H = scalarB α (bv H) := by
      change H = scalarB ((1 / 2 : ℝ) * (Matrix.trace H).re) ((1 / 2 : ℝ) • bloch H)
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hermitian_decomposition H hH.isHermitian
    _ = scalarB α (α • r) := by
      change scalarB α a = scalarB α (α • r)
      rw [hv]
    _ = (2 * α) • blochMatrix 1 r := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [α, scalarB, B_formula, blochMatrix] <;> ring
private theorem bv_dominated (r : EuclideanSpace ℝ (Fin 3)) (c : ℝ) (H : QubitMatrix)
    (hr : ‖r‖ = 1) (hH : H.PosSemidef)
    (hR : (c • blochMatrix 1 r - H).PosSemidef) :
    bv H = a0 H • r := by
  have hd := dominated_projector r c H hr hH hR
  calc
    bv H = bv ((2 * a0 H) • blochMatrix 1 r) := congrArg bv hd
    _ = a0 H • r := by
      rw [map_smul]
      simp only [bv, LinearMap.smul_apply, blochLinear, LinearMap.coe_mk, AddHom.coe_mk,
        bloch_blochMatrix]
      module
private theorem witness_vectors (r₁ r₂ : EuclideanSpace ℝ (Fin 3)) (η : ℝ)
    (_hr₁ : ‖r₁‖ = 1) (hr₂ : ‖r₂‖ = 1) (hJM : GJointMeasurable η ![r₁, r₂]) :
    ∃ (D U₀ U₁ : EuclideanSpace ℝ (Fin 3)) (δ : ℝ),
      δ = 1 - η ∧
      ‖U₀‖ ≤ δ ∧ ‖U₁‖ ≤ δ ∧
      D = η • r₁ + U₀ ∧
      ∃ κ : ℝ, D = κ • r₂ + U₁ := by
  classical
  rcases hJM with ⟨E, W, hpovm, hns, hcons, hstar, hdelta⟩
  let δ : ℝ := 1 - η
  let U₀ : QubitMatrix := E 0 2 0 - E 1 2 0
  let U₁ : QubitMatrix := E 0 2 1 - E 1 2 1
  let Dm : QubitMatrix := W 0 - W 1
  have hEpos (β : Fin 2) (b : Fin 3) (y : Fin 2) : (E β b y).PosSemidef := by
    exact (hpovm y).1 (β, b)
  have hnoise (y : Fin 2) :
      ‖bv (E 0 2 y - E 1 2 y)‖ ≤ δ := by
    apply noise_difference_bound _ _ δ (hEpos 0 2 y) (hEpos 1 2 y)
    have hc := hcons 2 y
    dsimp only [effects] at hc
    simpa [Fin.sum_univ_two] using hc.symm
  have hz10 : E 1 0 0 = 0 := by
    have h := hdelta 1 0 0 (by dsimp only [G]; simp)
    simpa using h
  have hz01 : E 0 1 0 = 0 := by
    have h := hdelta 0 0 1 (by dsimp only [G]; simp)
    simpa using h
  have hc00 := hcons 0 0
  have hc10 := hcons 1 0
  simp only [Fin.sum_univ_two] at hc00 hc10
  have he00 : E 0 0 0 = effects η ![r₁, r₂] 0 0 := by
    rw [hz10] at hc00
    simpa [add_zero] using hc00.symm
  have he10 : E 1 1 0 = effects η ![r₁, r₂] 1 0 := by
    rw [hz01] at hc10
    simpa [add_zero] using hc10.symm
  have hw00 := hns 0 0
  have hw10 := hns 1 0
  have hw01 := hns 0 1
  have hw11 := hns 1 1
  simp only [Fin.sum_univ_three] at hw00 hw10 hw01 hw11
  have hD0 : bv Dm = η • r₁ + bv U₀ := by
    have hm : Dm = E 0 0 0 + E 0 1 0 + E 0 2 0 -
        (E 1 0 0 + E 1 1 0 + E 1 2 0)  := by
      dsimp [Dm]
      rw [← hw00, ← hw10]
    rw [hm, map_sub, map_add, map_add, map_add, map_add]
    rw [hz10, hz01, he00, he10]
    have ep : effects η ![r₁, r₂] 0 0 = η • blochMatrix 1 r₁ := by
      dsimp only [effects]
      simp
    have em : effects η ![r₁, r₂] 1 0 = η • blochMatrix 1 (-r₁) := by
      dsimp only [effects]
      simp
    rw [ep, em, map_smul, map_smul]
    simp only [map_zero, add_zero, zero_add, U₀, map_sub]
    simp only [bv, LinearMap.smul_apply, blochLinear, LinearMap.coe_mk, AddHom.coe_mk,
      bloch_blochMatrix]
    module
  have hres00 : (η • blochMatrix 1 r₂ - E 0 0 1).PosSemidef := by
    have hc := hcons 0 1
    simp only [Fin.sum_univ_two] at hc
    have he : η • blochMatrix 1 r₂ - E 0 0 1 = E 1 0 1 := by
      calc
        η • blochMatrix 1 r₂ - E 0 0 1 = effects η ![r₁, r₂] 0 1 - E 0 0 1 := by
          dsimp only [effects]
          simp
        _ = E 1 0 1 := by rw [hc]; abel
    rw [he]
    exact hEpos 1 0 1
  have hres01 : (η • blochMatrix 1 (-r₂) - E 0 1 1).PosSemidef := by
    have hc := hcons 1 1
    simp only [Fin.sum_univ_two] at hc
    have he : η • blochMatrix 1 (-r₂) - E 0 1 1 = E 1 1 1 := by
      calc
        η • blochMatrix 1 (-r₂) - E 0 1 1 = effects η ![r₁, r₂] 1 1 - E 0 1 1 := by
          dsimp only [effects]
          simp
        _ = E 1 1 1 := by rw [hc]; abel
    rw [he]
    exact hEpos 1 1 1
  have hres10 : (η • blochMatrix 1 r₂ - E 1 0 1).PosSemidef := by
    have hc := hcons 0 1
    simp only [Fin.sum_univ_two] at hc
    have he : η • blochMatrix 1 r₂ - E 1 0 1 = E 0 0 1 := by
      calc
        η • blochMatrix 1 r₂ - E 1 0 1 = effects η ![r₁, r₂] 0 1 - E 1 0 1 := by
          dsimp only [effects]
          simp
        _ = E 0 0 1 := by rw [hc]; abel
    rw [he]
    exact hEpos 0 0 1
  have hres11 : (η • blochMatrix 1 (-r₂) - E 1 1 1).PosSemidef := by
    have hc := hcons 1 1
    simp only [Fin.sum_univ_two] at hc
    have he : η • blochMatrix 1 (-r₂) - E 1 1 1 = E 0 1 1 := by
      calc
        η • blochMatrix 1 (-r₂) - E 1 1 1 = effects η ![r₁, r₂] 1 1 - E 1 1 1 := by
          dsimp only [effects]
          simp
        _ = E 0 1 1 := by rw [hc]; abel
    rw [he]
    exact hEpos 0 1 1
  have hd00 := bv_dominated r₂ η (E 0 0 1) hr₂
      (hEpos 0 0 1) hres00
  have hd01 := bv_dominated (-r₂) η (E 0 1 1) (by simpa [norm_neg] using hr₂)
      (hEpos 0 1 1) hres01
  have hd10 := bv_dominated r₂ η (E 1 0 1) hr₂
      (hEpos 1 0 1) hres10
  have hd11 := bv_dominated (-r₂) η (E 1 1 1) (by simpa [norm_neg] using hr₂)
      (hEpos 1 1 1) hres11
  have hD1 : bv Dm =
      (a0 (E 0 0 1) - a0 (E 0 1 1) - a0 (E 1 0 1) + a0 (E 1 1 1)) • r₂ + bv U₁ := by
    have hm : Dm = E 0 0 1 + E 0 1 1 + E 0 2 1 -
        (E 1 0 1 + E 1 1 1 + E 1 2 1)  := by
      dsimp [Dm]
      rw [← hw01, ← hw11]
    rw [hm, map_sub, map_add, map_add, map_add, map_add]
    rw [hd00, hd01, hd10, hd11]
    simp [U₁, sub_eq_add_neg]
    module
  refine ⟨bv Dm, bv U₀, bv U₁, δ, rfl, ?_, ?_, hD0, ?_⟩
  · simpa [U₀, δ] using hnoise 0
  · simpa [U₁, δ] using hnoise 1
  · refine ⟨a0 (E 0 0 1) - a0 (E 0 1 1) - a0 (E 1 0 1) + a0 (E 1 1 1), ?_⟩
    simpa [Dm, U₁] using hD1
theorem result : claim := by
  intro r₁ r₂ η hr₁ hr₂ hη hη₁ hJM
  rcases witness_vectors r₁ r₂ η hr₁ hr₂ hJM with
    ⟨D, U₀, U₁, δ, hδ, hU₀, hU₁, hD₀, κ, hD₁⟩
  have hEq : η • r₁ + U₀ = κ • r₂ + U₁ := hD₀.symm.trans hD₁
  have hCrossEq :
      η • WithLp.toLp 2 (WithLp.ofLp r₁ ⨯₃ WithLp.ofLp r₂) =
        WithLp.toLp 2 (WithLp.ofLp (U₁ - U₀) ⨯₃ WithLp.ofLp r₂) := by
    have h := congrArg
      (fun x : EuclideanSpace ℝ (Fin 3) => WithLp.ofLp x ⨯₃ WithLp.ofLp r₂) hEq
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, LinearMap.map_add₂,
      LinearMap.map_smul₂, cross_self, smul_zero, zero_add] at h
    have h' : η • (WithLp.ofLp r₁ ⨯₃ WithLp.ofLp r₂) =
        WithLp.ofLp (U₁ - U₀) ⨯₃ WithLp.ofLp r₂ := by
      rw [WithLp.ofLp_sub, LinearMap.map_sub₂]
      exact (eq_sub_iff_add_eq).2 h
    simpa only [WithLp.toLp_smul] using congrArg (WithLp.toLp 2) h'
  have hNormEq :
      η * ‖WithLp.toLp 2 (WithLp.ofLp r₁ ⨯₃ WithLp.ofLp r₂)‖ =
        ‖WithLp.toLp 2 (WithLp.ofLp (U₁ - U₀) ⨯₃ WithLp.ofLp r₂)‖ := by
    calc
      η * ‖WithLp.toLp 2 (WithLp.ofLp r₁ ⨯₃ WithLp.ofLp r₂)‖ =
          ‖η • WithLp.toLp 2 (WithLp.ofLp r₁ ⨯₃ WithLp.ofLp r₂)‖ := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
      _ = ‖WithLp.toLp 2 (WithLp.ofLp (U₁ - U₀) ⨯₃ WithLp.ofLp r₂)‖ := by rw [hCrossEq]
  have hBound :
      ‖WithLp.toLp 2 (WithLp.ofLp (U₁ - U₀) ⨯₃ WithLp.ofLp r₂)‖ ≤ ‖U₁‖ + ‖U₀‖ := by
    calc
      ‖WithLp.toLp 2 (WithLp.ofLp (U₁ - U₀) ⨯₃ WithLp.ofLp r₂)‖ =
          ‖U₁ - U₀‖ * Real.sin (InnerProductGeometry.angle (U₁ - U₀) r₂) := by
        rw [InnerProductGeometry.norm_ofLp_crossProduct, hr₂, mul_one]
      _ ≤ ‖U₁ - U₀‖ := by
        exact mul_le_of_le_one_right (norm_nonneg _) (Real.sin_le_one _)
      _ ≤ ‖U₁‖ + ‖U₀‖ := norm_sub_le _ _
  nlinarith [hNormEq, hBound, hη₁]
end D5.S3.Quantum.Measurement.LossyQubitPartialJMTightness
