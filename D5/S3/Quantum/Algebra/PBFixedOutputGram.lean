/- GID: D5/S3/Quantum/Algebra/PBFixedOutputGram
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PBFixedOutputGram
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Symmetric]
   utility: none
   digest: Scalar PB yields full vector transverse identities. -/

import D5.S3.Quantum.Algebra.PBAffineFirstBudget
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Positive

/-! Scalar PB and transverse readings on a full Jordan representation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Algebra.PBFixedOutputGram

open Filter Topology PBAffineFirstBudget

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The scalar budget for one original probe and one common reading. -/
def scalarPB (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (κ ρ : E →ₗ[ℝ] E)
    (t k g x : E) (φ : E →ₗ[ℝ] ℝ) : Prop :=
  |φ ((-2 : ℝ) • (J x (κ x - k) + J t (ρ x + g)))| ≤
    Real.sqrt (gram J φ (x + (κ x - k)) (t + (ρ x + g))) +
    Real.sqrt (gram J φ (x - (κ x - k)) (t - (ρ x + g)))

/-- Primitive spectral - pair relations for the known Jordan and commutator rows. -/
structure SpectralPair (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (κ ρ : E →ₗ[ℝ] E) where
  e : E
  j : E
  n : E
  μ : ℝ
  lam : ℝ
  kappa_e : κ e = lam • j
  kappa_n : κ n = 0
  rho_e : ρ e = μ • e
  rho_n : ρ n = (μ + lam) • n
  jordan_ej : J e j = 0
  jordan_nj : J n j = j

/-- A Jordan representation, with no response or separate P2 field. -/
structure VectorModel (J : E →ₗ[ℝ] E →ₗ[ℝ] E) where
  op : E →ₗ[ℝ] (H →ₗ[ℝ] H)
  symmetric : ∀ a, (op a).IsSymmetric
  jordan : ∀ a b, op (J a b) =
    (1 / 2 : ℝ) • ((op a).comp (op b) + (op b).comp (op a))

/-- The reading acts on the entire represented space. -/
def vectorReading {J : E →ₗ[ℝ] E →ₗ[ℝ] E}
    (R : VectorModel (H := H) J) (v : H) : E →ₗ[ℝ] ℝ where
  toFun a := ⟪v, R.op a v⟫
  map_add' a b := by simp [inner_add_right]
  map_smul' a b := by simp [inner_smul_right]



private theorem reading_jordan {J : E →ₗ[ℝ] E →ₗ[ℝ] E}
    (R : VectorModel (H := H) J) (a b : E) (v : H) :
    vectorReading R v (J a b) = ⟪R.op a v, R.op b v⟫ := by
  simp only [vectorReading, LinearMap.coe_mk, AddHom.coe_mk, R.jordan,
    LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    inner_smul_right, inner_add_right]
  rw [← R.symmetric a v (R.op b v), ← R.symmetric b v (R.op a v), real_inner_comm]
  ring

private theorem first_budget (J : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hs : ∀ a b, J a b = J b a) (κ ρ : E →ₗ[ℝ] E)
    (F : SpectralPair J κ ρ) (t k g : E) (φ : E →ₗ[ℝ] ℝ)
    (hPB : ∀ T α : ℝ, scalarPB J κ ρ t k g (T • F.e + α • F.n) φ)
    (T : ℝ) :
    let a := F.μ + F.lam
    let V := a • J F.n t - J F.n k
    let Z := t + a • k
    2 * |φ ((F.lam * T) • F.j + V)| ≤
      Real.sqrt (gram J φ F.n (Z + g - (F.lam * T) • F.e - (a * F.lam * T) • F.j)) +
      Real.sqrt (gram J φ F.n (Z - g + (F.lam * T) • F.e - (a * F.lam * T) • F.j)) := by
  let a := F.μ + F.lam
  let V := a • J F.n t - J F.n k
  let Z := t + a • k
  let A := T • (F.e + F.lam • F.j) - k
  let B := t + g + (F.μ * T) • F.e
  let C := T • (F.e - F.lam • F.j) + k
  let D := t - g - (F.μ * T) • F.e
  let L := (2 * T) • J F.e k - (2 * F.μ * T) • J t F.e - 2 • J t g
  have finite (α : ℝ) :
      |φ L - α * (2 * φ ((F.lam * T) • F.j + V))| ≤
        Real.sqrt (gram J φ (A + α • F.n) (B + (a * α) • F.n)) +
        Real.sqrt (gram J φ (C + α • F.n) (D + (-a * α) • F.n)) := by
    have hb := hPB T α
    have hk : κ (T • F.e + α • F.n) = (F.lam * T) • F.j := by
      simp [F.kappa_e, F.kappa_n, smul_smul, mul_comm]
    have hr : ρ (T • F.e + α • F.n) = (F.μ * T) • F.e + (a * α) • F.n := by
      simp [F.rho_e, F.rho_n, a, smul_smul, mul_comm]
    have hp : T • F.e + α • F.n + (κ (T • F.e + α • F.n) - k) = A + α • F.n := by
      rw [hk]; dsimp [A]; module
    have hm : T • F.e + α • F.n - (κ (T • F.e + α • F.n) - k) = C + α • F.n := by
      rw [hk]; dsimp [C]; module
    have sp : t + (ρ (T • F.e + α • F.n) + g) = B + (a * α) • F.n := by
      rw [hr]; dsimp [B]; module
    have sm : t - (ρ (T • F.e + α • F.n) + g) = D + (-a * α) • F.n := by
      rw [hr]; dsimp [D]; module
    have hl : (-2 : ℝ) • (J (T • F.e + α • F.n)
        (κ (T • F.e + α • F.n) - k) + J t (ρ (T • F.e + α • F.n) + g)) =
        L - (2 * α) • ((F.lam * T) • F.j + V) := by
      rw [hk, hr]
      simp only [map_add, map_sub, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, F.jordan_ej, F.jordan_nj,
        smul_zero, hs t F.n]
      dsimp [L, V]
      module
    unfold scalarPB at hb
    rw [hp, hm, sp, sm, hl] at hb
    have hread : φ (L - (2 * α) • ((F.lam * T) • F.j + V)) =
        φ L - α * (2 * φ ((F.lam * T) • F.j + V)) := by
      simp only [map_sub, map_smul, smul_eq_mul]
      ring
    rw [hread] at hb
    exact hb
  have lead := leading_budget (φ L) (2 * φ ((F.lam * T) • F.j + V))
    (gram J φ A B)
    (a * φ (J A A) * φ (J F.n B) + φ (J F.n A) * φ (J B B)-
      φ (J A B) * (φ (J F.n B) + a * φ (J F.n A)))
    (gram J φ F.n (B - a • A))
    (gram J φ C D)
    ((-a) * φ (J C C) * φ (J F.n D) + φ (J F.n C) * φ (J D D)-
      φ (J C D) * (φ (J F.n D) + (-a) * φ (J F.n C)))
    (gram J φ F.n (D - (-a) • C))
    (by intro α; simpa only [gram_shift J hs] using finite α)
  have wp : B - a • A = Z + g - (F.lam * T) • F.e - (a * F.lam * T) • F.j := by
    dsimp [A, B, Z, a]; module
  have wm : D - (-a) • C = Z - g + (F.lam * T) • F.e - (a * F.lam * T) • F.j := by
    dsimp [C, D, Z, a]; module
  rw [wp, wm] at lead
  simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using lead

/-- The mixed - vector limit of the scalar PB, with every complementary component retained. -/
private theorem vector_budget (J : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hs : ∀ a b, J a b = J b a) (κ ρ : E →ₗ[ℝ] E)
    (F : SpectralPair J κ ρ) (R : VectorModel (H := H) J) (t k g : E)
    (hPB : ∀ (v : H), ‖v‖ = 1 → ∀ (T α : ℝ),
      scalarPB J κ ρ t k g (T • F.e + α • F.n) (vectorReading R v))
    (ξ η ν : H) (d : ℝ) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (hnξ : R.op F.n ξ = 0) (hnη : R.op F.n η = (2 : ℝ) • η)
    (hjξ : R.op F.j ξ = d • η) (heξ : R.op F.e ξ = d • ν)
    (hην : ⟪η, ν⟫ = 0)
    (hnV : J F.n ((F.μ + F.lam) • J F.n t - J F.n k) =
      (F.μ + F.lam) • J F.n t - J F.n k)
    (T : ℝ) :
    let V := (F.μ + F.lam) • J F.n t - J F.n k
    let Z := t + (F.μ + F.lam) • k
    2 * |F.lam * T * d+⟪η, R.op V ξ⟫| ≤
      ‖realPerp η (R.op (Z + g) ξ) - (F.lam * T * d) • ν‖ +
      ‖realPerp η (R.op (Z - g) ξ) + (F.lam * T * d) • ν‖ := by
  let a := F.μ + F.lam
  let V := a • J F.n t - J F.n k
  let Z := t + a • k
  let P := realPerp η
  let Wp := Z + g - (F.lam * T) • F.e - (a * F.lam * T) • F.j
  let Wm := Z - g + (F.lam * T) • F.e - (a * F.lam * T) • F.j
  have hηη : ⟪η, η⟫ = 1 := by simp [hη]
  have diag (b : E) (hb : J F.n b = b) :
      ⟪ξ, R.op b ξ⟫ = 0 ∧ ⟪η, R.op b η⟫ = 0 := by
    have hx := reading_jordan R F.n b ξ
    have hy := reading_jordan R F.n b η
    rw [hb, hnξ, inner_zero_left] at hx
    rw [hb, hnη, inner_smul_left] at hy
    change ⟪ξ, R.op b ξ⟫ = 0 at hx
    change ⟪η, R.op b η⟫ = 2*⟪η, R.op b η⟫ at hy
    exact ⟨hx, by linarith⟩
  obtain ⟨hdiagξ, hdiagη⟩ := diag V hnV
  obtain ⟨hjjξ, hjjη⟩ := diag F.j F.jordan_nj
  have exactGram (W : E) (ε : ℝ) :
      gram J (vectorReading R (ξ + ε • η)) F.n W =
        4 * ε ^ 2*‖P (R.op W ξ + ε • R.op W η)‖^2 := by
    rw [gram, reading_jordan, reading_jordan, reading_jordan]
    have hn : R.op F.n (ξ + ε • η) = (2 * ε) • η := by
      simp [hnξ, hnη, smul_smul, mul_comm]
    rw [hn, map_add, map_smul]
    simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real, hηη, mul_one]
    rw [real_inner_self_eq_norm_sq]
    have perp (z : H) : ‖P z‖^2 = ‖z‖^2-⟪η, z⟫^2 := by
      change ‖z-⟪η, z⟫ • η‖^2 = _
      rw [norm_sub_sq_real, inner_smul_right, real_inner_comm z η, norm_smul]
      simp only [hη, mul_one, Real.norm_eq_abs, sq_abs]
      ring
    rw [perp]
    ring
  have exactRead (ε : ℝ) :
      vectorReading R (ξ + ε • η) ((F.lam * T) • F.j + V) =
        2 * ε * (F.lam * T * d+⟪η, R.op V ξ⟫) := by
    have sy (b : E) : ⟪ξ, R.op b η⟫ = ⟪η, R.op b ξ⟫ := by
      rw [← R.symmetric b ξ η, real_inner_comm]
    simp only [vectorReading, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_smul,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
    rw [hjjξ, hjjη, hdiagξ, hdiagη, sy F.j, sy V, hjξ, inner_smul_right, hηη]
    simp only [RCLike.conj_to_real]
    ring
  have finite (ε : ℝ) (hε : 0 < ε) :
      2 * |F.lam * T * d+⟪η, R.op V ξ⟫| ≤
        ‖P (R.op Wp ξ + ε • R.op Wp η)‖ +
        ‖P (R.op Wm ξ + ε • R.op Wm η)‖ := by
    let b := (Real.sqrt (1 + ε ^ 2))⁻¹
    have hroot : 0 < Real.sqrt (1 + ε ^ 2) := Real.sqrt_pos.2 (by positivity)
    have hbpos : 0 < b := inv_pos.2 hroot
    have hξη : ⟪ξ, η⟫ = 0 := by
      have h := R.symmetric F.n ξ η
      rw [hnξ, hnη, inner_zero_left, inner_smul_right] at h
      linarith
    have hnorm : ‖ξ + ε • η‖ = Real.sqrt (1 + ε ^ 2) := by
      have hn : ‖ξ + ε • η‖^2 = 1 + ε ^ 2 := by
        rw [norm_add_sq_real, inner_smul_right, hξη, norm_smul, hξ, hη,
          Real.norm_eq_abs, mul_one, sq_abs]
        ring
      rw [← hn, Real.sqrt_sq (norm_nonneg _)]
    have hunit : ‖b • (ξ + ε • η)‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hbpos, hnorm]
      exact inv_mul_cancel₀ (ne_of_gt hroot)
    have sr (z : H) (W : E) :
        vectorReading R (b • z) W = b ^ 2 * vectorReading R z W := by
      simp only [vectorReading, LinearMap.coe_mk, AddHom.coe_mk, map_smul,
        inner_smul_left, inner_smul_right, RCLike.conj_to_real]
      ring
    have sg (W : E) : gram J (vectorReading R (b • (ξ + ε • η))) F.n W =
        b ^ 4 * gram J (vectorReading R (ξ + ε • η)) F.n W := by
      simp only [gram, sr]
      ring
    have hb := first_budget J hs κ ρ F t k g
      (vectorReading R (b • (ξ + ε • η))) (hPB _ hunit) T
    change 2 * |vectorReading R (b • (ξ + ε • η)) ((F.lam * T) • F.j + V)| ≤ _ at hb
    rw [sr, sg, sg, exactRead, exactGram, exactGram] at hb
    have sqr (z : H) : Real.sqrt (b ^ 4 * (4 * ε ^ 2*‖z‖^2)) = 2 * ε * b ^ 2*‖z‖ := by
      rw [show b ^ 4 * (4 * ε ^ 2*‖z‖^2) = (2 * ε * b ^ 2*‖z‖) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    rw [sqr, sqr, abs_mul, abs_mul, abs_mul, abs_of_pos hε,
      abs_of_nonneg (sq_nonneg b)] at hb
    simp only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hb
    apply le_of_mul_le_mul_left (a := 2 * ε * b ^ 2) (a0 := by positivity)
    convert hb using 1 <;> ring
  have pp : P (R.op F.e ξ) = d • ν := by
    simp [P, realPerp, heξ, hην]
  have pq : P (R.op F.j ξ) = 0 := by simp [P, realPerp, hjξ, hη]
  have hr : Tendsto (fun ε : ℝ =>
      ‖P (R.op Wp ξ + ε • R.op Wp η)‖ + ‖P (R.op Wm ξ + ε • R.op Wm η)‖)
      (𝓝[>] 0) (𝓝 (‖P (R.op (Z + g) ξ) - (F.lam * T * d) • ν‖ +
        ‖P (R.op (Z - g) ξ) + (F.lam * T * d) • ν‖)) := by
    have hc : Continuous (fun ε : ℝ =>
      ‖P (R.op Wp ξ + ε • R.op Wp η)‖ + ‖P (R.op Wm ξ + ε • R.op Wm η)‖) := by
      dsimp [P, realPerp]; fun_prop
    simpa only [Wp, Wm, zero_smul, add_zero, map_sub, map_add, map_smul,
      LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      pp, pq, smul_zero, sub_zero, smul_smul, mul_assoc] using
      (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hr (by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact finite ε hε)

/-- PB alone identifies a transverse real reading of the fixed output.
The vectors and operators act on the full representation, including its environment. -/
theorem fixed_output_anchor_identity (J : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hs : ∀ a b, J a b = J b a) (κ ρ : E →ₗ[ℝ] E)
    (F : SpectralPair J κ ρ) (R : VectorModel (H := H) J) (t k g : E)
    (hPB : ∀ (v : H), ‖v‖ = 1 → ∀ (T α : ℝ),
      scalarPB J κ ρ t k g (T • F.e + α • F.n) (vectorReading R v))
    (ξ η ν : H) (d : ℝ) (hd : d ≠ 0) (hlam : F.lam ≠ 0)
    (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (hν : ‖ν‖ = 1)
    (hnξ : R.op F.n ξ = 0) (hnη : R.op F.n η = (2 : ℝ) • η)
    (hjξ : R.op F.j ξ = d • η) (heξ : R.op F.e ξ = d • ν)
    (hην : ⟪η, ν⟫ = 0)
    (hnV : J F.n ((F.μ + F.lam) • J F.n t - J F.n k) =
      (F.μ + F.lam) • J F.n t - J F.n k) :
    ⟪ν, R.op g ξ⟫ = -⟪η, R.op ((F.μ + F.lam) • J F.n t - J F.n k) ξ⟫ := by
  let V := (F.μ + F.lam) • J F.n t - J F.n k
  let Z := t + (F.μ + F.lam) • k
  let P := realPerp η
  have hb := two_ended_budget (F.lam * d) (⟪η, R.op V ξ⟫/(F.lam * d))
    (mul_ne_zero hlam hd) ν (P (R.op (Z + g) ξ)) (P (R.op (Z - g) ξ)) hν
    (by
      intro T
      have h := vector_budget J hs κ ρ F R t k g hPB ξ η ν d hξ hη
        hnξ hnη hjξ heξ hην hnV T
      have heq : 2* |F.lam * d| * |T+⟪η, R.op V ξ⟫/(F.lam * d)| =
          2* |F.lam * T * d+⟪η, R.op V ξ⟫| := by
        rw [mul_assoc, ← abs_mul]
        congr 2
        field_simp [hlam, hd]
      rw [heq]
      simpa only [mul_assoc, mul_left_comm, mul_comm] using h)
  have hνη : ⟪ν, η⟫ = 0 := by rw [real_inner_comm, hην]
  have heq : ⟪ν, P (R.op (Z - g) ξ)⟫-⟪ν, P (R.op (Z + g) ξ)⟫ =
      -2*⟪ν, R.op g ξ⟫ := by
    simp only [P, realPerp, LinearMap.coe_mk, AddHom.coe_mk, inner_sub_right,
      inner_smul_right, hνη, mul_zero, sub_zero, map_sub, map_add,
      LinearMap.sub_apply, LinearMap.add_apply, inner_add_right]
    ring
  have hscale : 2 * (F.lam * d) * (⟪η, R.op V ξ⟫/(F.lam * d)) = 2*⟪η, R.op V ξ⟫ := by
    field_simp [hlam, hd]
  rw [heq, hscale] at hb
  change ⟪ν, R.op g ξ⟫ = -⟪η, R.op V ξ⟫
  linarith

section Complex

variable {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℂ C]
local instance : InnerProductSpace ℝ C := InnerProductSpace.complexToReal

/-- The two companion axes of the same scalar PB identify the complex output reading.
The orientation may be either sign of the imaginary unit. -/
theorem fixed_output_two_axis_identity (J : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hs : ∀ a b, J a b = J b a) (κ ρ : E →ₗ[ℝ] E)
    (F : SpectralPair J κ ρ) (R : VectorModel (H := C) J) (t k g : E)
    (hκj : κ F.j = (-F.lam) • F.e) (hρj : ρ F.j = F.μ • F.j)
    (hne : J F.n F.e = F.e)
    (hPB : ∀ (v : C), ‖v‖ = 1 → ∀ (T α : ℝ),
      scalarPB J κ ρ t k g (T • F.e + α • F.n) (vectorReading R v) ∧
      scalarPB J κ ρ t k g (T • F.j + α • F.n) (vectorReading R v))
    (ι : ℂ) (hι : ι = Complex.I ∨ ι = -Complex.I)
    (ξ η : C) (d : ℝ) (hd : d ≠ 0) (hlam : F.lam ≠ 0)
    (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (hnξ : R.op F.n ξ = 0) (hnη : R.op F.n η = (2 : ℝ) • η)
    (hnν : R.op F.n ((-ι) • η) = (2 : ℝ) • ((-ι) • η))
    (hjξ : R.op F.j ξ = d • η) (heξ : R.op F.e ξ = d • ((-ι) • η))
    (hnV : J F.n ((F.μ + F.lam) • J F.n t - J F.n k) =
      (F.μ + F.lam) • J F.n t - J F.n k) :
    inner ℂ η (R.op g ξ) =
      ι * inner ℂ η (R.op ((F.μ + F.lam) • J F.n t - J F.n k) ξ) := by
  let ν : C := (-ι) • η
  have hν : ‖ν‖ = 1 := by rcases hι with rfl | rfl <;> simp [ν, norm_smul, hη]
  have hην : inner ℝ η ν = 0 := by
    change (inner ℂ η ν).re = 0
    rcases hι with rfl | rfl <;> simp [ν, inner_smul_right, hη]
  let F' : SpectralPair J κ ρ := {
    e := F.j, j := -F.e, n := F.n, μ := F.μ, lam := F.lam
    kappa_e := by simpa only [smul_neg, neg_smul] using hκj
    kappa_n := F.kappa_n
    rho_e := hρj
    rho_n := F.rho_n
    jordan_ej := by rw [map_neg, hs F.j F.e, F.jordan_ej, neg_zero]
    jordan_nj := by rw [map_neg, hne] }
  have hfirst := fixed_output_anchor_identity J hs κ ρ F R t k g
    (fun v hv T α => (hPB v hv T α).1) ξ η ν d hd hlam hξ hη hν
    hnξ hnη hjξ heξ hην hnV
  have hsecond := fixed_output_anchor_identity J hs κ ρ F' R t k g
    (fun v hv T α => (hPB v hv T α).2) ξ (-ν) η d hd hlam hξ
    (by simpa using hν) hη hnξ
    (by change R.op F.n (-ν) = (2 : ℝ) • -ν
        rw [map_neg, hnν, smul_neg])
    (by change R.op (-F.e) ξ = d • -ν; simp only [map_neg, LinearMap.neg_apply, heξ, smul_neg]; rfl)
    hjξ (by rw [inner_neg_left, real_inner_comm, hην, neg_zero]) hnV
  change inner ℝ ν (R.op g ξ) = -inner ℝ η (R.op ((F.μ + F.lam) • J F.n t - J F.n k) ξ) at hfirst
  change inner ℝ η (R.op g ξ) =
    -inner ℝ (-ν) (R.op ((F.μ + F.lam) • J F.n t - J F.n k) ξ)
    at hsecond
  rw [inner_neg_left, neg_neg] at hsecond
  change (inner ℂ ν (R.op g ξ)).re =
    -(inner ℂ η (R.op ((F.μ + F.lam) • J F.n t - J F.n k) ξ)).re
    at hfirst
  change (inner ℂ η (R.op g ξ)).re =
    (inner ℂ ν (R.op ((F.μ + F.lam) • J F.n t - J F.n k) ξ)).re
    at hsecond
  rcases hι with rfl | rfl
  all_goals
    simp [ν, inner_smul_left, Complex.mul_re] at hfirst hsecond
    apply Complex.ext
    · simpa [Complex.mul_re] using hsecond
    · simpa [Complex.mul_im] using hfirst

#print axioms fixed_output_two_axis_identity

end Complex

#print axioms fixed_output_anchor_identity

end D5.S3.Quantum.Algebra.PBFixedOutputGram
