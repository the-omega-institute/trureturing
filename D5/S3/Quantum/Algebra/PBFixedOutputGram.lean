/- GID: D5 / S3 / Quantum / Algebra / PBFixedOutputGram
   generality: G
   mirror - B: D5 / B / S3 / Quantum / Algebra / PBFixedOutputGram
   mirror - E: none(waiver:registration - template - not - established)
   anchors: [mathlib / module / Mathlib.Analysis.InnerProductSpace.Symmetric]
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

/-! The concrete four-dimensional self-adjoint matrix carrier used by the
fixed-output reconstruction.  The action is the literal matrix action on the
whole four-dimensional space, so the fourth row and column remain present. -/

private abbrev M4 := Matrix (Fin 4) (Fin 4) ℂ
private abbrev M4E := selfAdjoint.submodule ℝ M4
private abbrev M4H := EuclideanSpace ℂ (Fin 4)

private def m4Herm (A : M4) (h : star A = A) : M4E := ⟨A, by
  change star A = A
  exact h⟩

private def m4JordanVal (a b : M4E) : M4 :=
  (1 / 2 : ℂ) • ((a : M4) * b + (b : M4) * a)

private def m4Jordan (a b : M4E) : M4E := m4Herm (m4JordanVal a b) (by
  have ha : star (a : M4) = (a : M4) := a.property
  have hb : star (b : M4) = (b : M4) := b.property
  simp [m4JordanVal, star_mul, ha, hb]
  module)

/-- The concrete Jordan product on the self-adjoint part of `M₄(ℂ)`. -/
def m4J : M4E →ₗ[ℝ] M4E →ₗ[ℝ] M4E where
  toFun a := {
    toFun := fun b => m4Jordan a b
    map_add' := by
      intro b c
      apply Subtype.ext
      change m4JordanVal a (b + c) = m4JordanVal a b + m4JordanVal a c
      simp [m4JordanVal, Matrix.mul_add, Matrix.add_mul]
      module
    map_smul' := by
      intro r b
      apply Subtype.ext
      change m4JordanVal a (r • b) = r • m4JordanVal a b
      simp [m4JordanVal, Matrix.mul_smul, Matrix.smul_mul]
      module }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    change m4JordanVal (a + b) c = m4JordanVal a c + m4JordanVal b c
    simp [m4JordanVal, Matrix.mul_add, Matrix.add_mul]
    module
  map_smul' := by
    intro r a
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    change m4JordanVal (r • a) b = r • m4JordanVal a b
    simp [m4JordanVal, Matrix.mul_smul, Matrix.smul_mul]
    module

private def m4OpVal (a : M4E) : M4H →ₗ[ℂ] M4H :=
  Matrix.toEuclideanLin (a : M4)

private def m4Op : M4E →ₗ[ℝ] (M4H →ₗ[ℝ] M4H) where
  toFun a := (m4OpVal a).restrictScalars ℝ
  map_add' := by
    intro a b
    ext x i
    simp [m4OpVal, Matrix.toEuclideanLin, Matrix.mulVec]
  map_smul' := by
    intro r a
    ext x i
    simp [m4OpVal, Matrix.toEuclideanLin, Matrix.smul_mulVec]

/-- Literal `M₄(ℂ)` realization of the abstract vector model. -/
def m4VectorModel : VectorModel (J := m4J) (H := M4H) where
  op := m4Op
  symmetric := by
    intro a x y
    change (inner ℂ (m4OpVal a x) y).re = (inner ℂ x (m4OpVal a y)).re
    have ha : (a : M4).IsHermitian := by
      change (a : M4).conjTranspose = (a : M4)
      rw [← Matrix.star_eq_conjTranspose]
      exact a.property
    exact congrArg Complex.re ((Matrix.isSymmetric_toEuclideanLin_iff.mpr ha) x y)
  jordan := by
    intro a b
    have hc : m4OpVal (m4Jordan a b) =
        (1 / 2 : ℂ) • (m4OpVal a ∘ₗ m4OpVal b + m4OpVal b ∘ₗ m4OpVal a) := by
      change Matrix.toLpLin 2 2 (m4JordanVal a b) = _
      simp only [m4JordanVal, map_smul, map_add, Matrix.toEuclideanLin,
        m4OpVal, LinearMap.add_apply]
      rw [Matrix.toLpLin_mul, Matrix.toLpLin_mul]
    change LinearMap.restrictScalars ℝ (m4OpVal (m4Jordan a b)) = _
    rw [hc]
    simp only [LinearMap.restrictScalars, LinearMap.smul_apply,
      LinearMap.add_apply, LinearMap.comp_apply, Pi.smul_apply]
    ext x i
    simp [m4Op, m4OpVal]

/-- The complete row reconstruction consumer.  Once the three actor rows have
been obtained from the scalar-PB axes, Hermiticity supplies the matching
columns and leaves precisely four real diagonal residuals. -/
theorem m4_full_row_reconstruction (g k : M4)
    (hg : g.IsHermitian) (hk : k.IsHermitian)
    (hrow : ∀ i j : Fin 4, i ≠ j → g i j = k i j) :
    ∃ s : Fin 4 → ℝ, g - k = Matrix.diagonal (fun i => (s i : ℂ)) := by
  let s : Fin 4 → ℝ := fun i => (g i i - k i i).re
  refine ⟨s, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    have hgd : ((g i i).re : ℂ) = g i i := hg.coe_re_apply_self i
    have hkd : ((k i i).re : ℂ) = k i i := hk.coe_re_apply_self i
    simp [s, Matrix.diagonal_apply, hgd, hkd, sub_eq_add_neg]
  · simp [Matrix.diagonal_apply, hij, hrow i j hij]

/-- The complex functional associated with a full-space vector state. -/
def m4VectorFunctional (v : M4H) : M4 →ₗ[ℂ] ℂ where
  toFun A := inner ℂ v (Matrix.toEuclideanLin A v)
  map_add' A B := by
    change inner ℂ v ((Matrix.toEuclideanLin (A + B)) v) = _
    rw [map_add]
    simp only [LinearMap.add_apply]
    rw [inner_add_right]
  map_smul' z A := by
    change inner ℂ v ((Matrix.toEuclideanLin (z • A)) v) = _
    rw [map_smul]
    simp [inner_smul_right]

/-- Restriction of a complex functional to the real self-adjoint carrier. -/
def m4RealFunctional (φ : M4 →ₗ[ℂ] ℂ) : M4E →ₗ[ℝ] ℝ where
  toFun A := (φ (A : M4)).re
  map_add' A B := by simp [map_add]
  map_smul' r A := by simp [map_smul, RCLike.smul_re]

/-- The restricted vector state is exactly the existing vector reading. -/
theorem m4RealFunctional_vector (v : M4H) (A : M4E) :
    m4RealFunctional (m4VectorFunctional v) A =
      vectorReading m4VectorModel v A := by
  rfl

/-- The full complex positive-semidefinite cone, stated without imposing an
order on `ℂ`: Hermiticity and nonnegative quadratic forms. -/
def m4PosSemidef (A : M4) : Prop :=
  A.IsHermitian ∧ ∀ v : M4H, (0 : ℝ) ≤
    (inner ℂ v (Matrix.toEuclideanLin A v)).re

/-- Positivity on the full matrix cone, in the form needed by the original
scalar PB quantifier. -/
def m4Positive (φ : M4 →ₗ[ℂ] ℂ) : Prop :=
  ∀ A : M4, m4PosSemidef A → (0 : ℝ) ≤ (φ A).re

theorem m4VectorFunctional_positive (v : M4H) :
    m4Positive (m4VectorFunctional v) := by
  intro A hA
  exact hA.2 v

/-- Actor support is stated on the original four-by-four carrier; the fourth
row and column are retained in the ambient positive functional. -/
def m4ActorSupported (x : M4E) : Prop :=
  ∀ i j : Fin 4, (i = 3 ∨ j = 3) → (x : M4) i j = 0

/-- The original positive-functional scalar PB transfers to every full-space
vector reading.  This is the exact bridge consumed by the spectral argument. -/
theorem m4_positive_pb_transfer
    {J : M4E →ₗ[ℝ] M4E →ₗ[ℝ] M4E} {κ ρ : M4E →ₗ[ℝ] M4E}
    {t k g : M4E}
    (hPB : ∀ (φ : M4 →ₗ[ℂ] ℂ), m4Positive φ →
      ∀ x : M4E, m4ActorSupported x →
        scalarPB (J := J) κ ρ t k g x (m4RealFunctional φ)) :
    ∀ (v : M4H), ‖v‖ = 1 → ∀ x : M4E, m4ActorSupported x →
      scalarPB (J := J) κ ρ t k g x (vectorReading m4VectorModel v) := by
  intro v hv x hx
  have h := hPB (m4VectorFunctional v) (m4VectorFunctional_positive v) x hx
  have heq : m4RealFunctional (m4VectorFunctional v) =
      vectorReading m4VectorModel v := by
    ext A
    exact m4RealFunctional_vector v A
  rw [heq] at h
  exact h


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

private theorem m4J_comm (a b : M4E) : m4J a b = m4J b a := by
  apply Subtype.ext
  simp [m4J, m4Jordan, m4JordanVal, add_comm]

/-- The original diagonal actor with its environment eigenvalue zero. -/
def m4C : M4E := m4Herm (Matrix.diagonal ![1, 2, 3, 0]) (by
  simp [Matrix.star_eq_conjTranspose])

private def m4Edge (i j : Fin 4) (z : ℂ) : M4E :=
  m4Herm (Matrix.single i j z + Matrix.single j i (star z)) (by
    simp [Matrix.star_eq_conjTranspose, add_comm])

/-- The original two-leg star, without rotating either complex coefficient. -/
def m4T (q₁ q₂ : ℂ) : M4E := m4Edge 0 3 q₁ + m4Edge 1 3 q₂

/-- The oriented commutator row on the real self-adjoint matrix carrier. -/
def m4Kappa (c : M4E) (ι : ℂ) (hι : ι = Complex.I ∨ ι = -Complex.I) :
    M4E →ₗ[ℝ] M4E where
  toFun x := m4Herm ((ι / 2) • ((c : M4) * x - (x : M4) * c)) (by
    have hc : star (c : M4) = (c : M4) := c.property
    have hx : star (x : M4) = (x : M4) := x.property
    rcases hι with rfl | rfl <;> simp [star_mul, hc, hx, sub_eq_add_neg] <;> module)
  map_add' := by
    intro a b
    apply Subtype.ext
    simp [Matrix.mul_add, Matrix.add_mul]
    module
  map_smul' := by
    intro r a
    apply Subtype.ext
    simp [Matrix.mul_smul, Matrix.smul_mul, smul_comm]

private def m4N (i : Fin 4) : M4E :=
  m4Herm (Matrix.diagonal (fun r => if r = i then 2 else 0)) (by
    simp [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose])

private def m4Eigen (i : Fin 4) : ℝ := ![1, 2, 3, 0] i

private theorem m4J_c_entry (x : M4E) (r s : Fin 4) :
    ((m4J m4C x : M4E) : M4) r s =
      ((m4Eigen r + m4Eigen s : ℝ) / 2 : ℂ) * (x : M4) r s := by
  simp [m4J, m4Jordan, m4JordanVal, m4Herm, m4C, m4Eigen,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply]
  ring

private theorem m4K_c_entry (ι : ℂ) (hι : ι = Complex.I ∨ ι = -Complex.I)
    (x : M4E) (r s : Fin 4) :
    ((m4Kappa m4C ι hι x : M4E) : M4) r s =
      ι * ((m4Eigen r - m4Eigen s : ℝ) / 2 : ℂ) * (x : M4) r s := by
  simp [m4Kappa, m4Herm, m4C, m4Eigen, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.smul_apply]
  ring

private theorem m4J_n_entry (i : Fin 4) (x : M4E) (r s : Fin 4) :
    ((m4J (m4N i) x : M4E) : M4) r s =
      (if r = i then (x : M4) r s else 0) +
      (if s = i then (x : M4) r s else 0) := by
  simp [m4J, m4Jordan, m4JordanVal, m4Herm, m4N,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply]
  split_ifs <;> ring

private theorem m4Edge_entry (i j r s : Fin 4) (z : ℂ) :
    (m4Edge i j z : M4) r s =
      (if r = i ∧ s = j then z else 0) +
      (if r = j ∧ s = i then star z else 0) := by
  simp [m4Edge, m4Herm, Matrix.single_apply]

private theorem m4Op_apply (a : M4E) (v : M4H) (r : Fin 4) :
    m4Op a v r = ∑ s, (a : M4) r s * v s := rfl

private theorem m4Edge_apply (i j : Fin 4) (z : ℂ) (v : M4H) :
    m4Op (m4Edge i j z) v =
      EuclideanSpace.single i (z * v j) + EuclideanSpace.single j (star z * v i) := by
  ext r
  simp [m4Op_apply, m4Edge_entry, Finset.sum_add_distrib,
    ite_and, PiLp.single_apply, ite_mul]

private theorem m4N_apply (i : Fin 4) (v : M4H) :
    m4Op (m4N i) v = EuclideanSpace.single i (2 * v i) := by
  ext r
  simp [m4Op_apply, m4N, m4Herm, Matrix.diagonal_apply,
    PiLp.single_apply, ite_mul]

end D5.S3.Quantum.Algebra.PBFixedOutputGram
