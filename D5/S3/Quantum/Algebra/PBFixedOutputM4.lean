/- GID: D5/S3/Quantum/Algebra/PBFixedOutputM4
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PBFixedOutputM4
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.LinearMap]
   utility: none
   digest: Concrete full-space matrix realization of scalar fixed-output PB. -/

import D5.S3.Quantum.Algebra.PBFixedOutputGram

/-! Literal full-space matrix spectral geometry for the scalar PB. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Quantum.Algebra.PBFixedOutputM4

open PBFixedOutputGram

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
  ∀ A : M4, m4PosSemidef A → (φ A).im = 0 ∧ (0 : ℝ) ≤ (φ A).re

theorem m4VectorFunctional_positive (v : M4H) :
    m4Positive (m4VectorFunctional v) := by
  intro A hA
  refine ⟨?_, hA.2 v⟩
  change (inner ℂ v (Matrix.toEuclideanLin A v)).im = 0
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.1
  have hi := congrArg Complex.im (hs v v)
  rw [← inner_conj_symm (Matrix.toEuclideanLin A v) v] at hi
  change -(inner ℂ v (Matrix.toEuclideanLin A v)).im =
    (inner ℂ v (Matrix.toEuclideanLin A v)).im at hi
  linarith

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


private theorem m4J_comm (a b : M4E) : m4J a b = m4J b a := by
  apply Subtype.ext
  simp [m4J, m4Jordan, m4JordanVal, add_comm]

private def m4Eigen (i : Fin 4) : ℝ := ![1, 2, 3, 0] i

/-- The original diagonal actor with its environment eigenvalue zero. -/
def m4C : M4E := m4Herm (Matrix.diagonal (fun i => (m4Eigen i : ℂ))) (by
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
    simp [m4Herm, Matrix.mul_add, Matrix.add_mul]
    module
  map_smul' := by
    intro r a
    apply Subtype.ext
    simp only [m4Herm, Submodule.coe_smul, RingHom.id_apply,
      Matrix.mul_smul, Matrix.smul_mul]
    rw [← smul_sub, smul_comm]

private def m4N (i : Fin 4) : M4E :=
  m4Herm (Matrix.diagonal (fun r => if r = i then 2 else 0)) (by
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext r
    change star (if r = i then (2 : ℂ) else 0) = _
    split_ifs <;> simp)

private theorem m4J_c_entry (x : M4E) (r s : Fin 4) :
    ((m4J m4C x : M4E) : M4) r s =
      ((m4Eigen r + m4Eigen s : ℝ) / 2 : ℂ) * (x : M4) r s := by
  simp [m4J, m4Jordan, m4JordanVal, m4Herm, m4C,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply]
  ring

private theorem m4K_c_entry (ι : ℂ) (hι : ι = Complex.I ∨ ι = -Complex.I)
    (x : M4E) (r s : Fin 4) :
    ((m4Kappa m4C ι hι x : M4E) : M4) r s =
      ι * ((m4Eigen r - m4Eigen s : ℝ) / 2 : ℂ) * (x : M4) r s := by
  simp [m4Kappa, m4Herm, m4C, Matrix.diagonal_mul,
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
  simp [m4Edge, m4Herm, Matrix.single_apply, eq_comm]

private theorem m4Op_apply (a : M4E) (v : M4H) (r : Fin 4) :
    m4Op a v r = ∑ s, (a : M4) r s * v s := rfl

private theorem m4Edge_apply (i j : Fin 4) (z : ℂ) (v : M4H) :
    m4Op (m4Edge i j z) v =
      EuclideanSpace.single i (z * v j) + EuclideanSpace.single j (star z * v i) := by
  ext r
  simp [m4Op_apply, m4Edge_entry, Finset.sum_add_distrib,
    ite_and, PiLp.single_apply, ite_mul, add_mul, mul_ite, Finset.sum_ite_irrel]

private theorem m4N_apply (i : Fin 4) (v : M4H) :
    m4Op (m4N i) v = EuclideanSpace.single i (2 * v i) := by
  ext r
  simp [m4Op_apply, m4N, m4Herm, Matrix.diagonal_apply,
    PiLp.single_apply, ite_mul]
  split_ifs <;> simp_all

private def m4Pair (ι : ℂ) (hι : ι = Complex.I ∨ ι = -Complex.I)
    (i j : Fin 4) (hij : i ≠ j) :
    SpectralPair m4J (m4Kappa m4C ι hι) (m4J m4C) where
  e := m4Edge i j 1
  j := m4Edge i j ι
  n := m4N i
  μ := (m4Eigen i + m4Eigen j) / 2
  lam := (m4Eigen i - m4Eigen j) / 2
  kappa_e := by
    apply Subtype.ext
    ext r s
    rw [m4K_c_entry]
    change _ = ((m4Eigen i - m4Eigen j) / 2) • (m4Edge i j ι : M4) r s
    rw [m4Edge_entry, m4Edge_entry]
    have hc : star ι = -ι := by rcases hι with rfl | rfl <;> simp
    simp only [star_one, hc, Complex.real_smul]
    split_ifs <;> simp_all <;> push_cast <;> ring
  kappa_n := by
    apply Subtype.ext
    ext r s
    rw [m4K_c_entry]
    simp only [m4N, m4Herm, Matrix.diagonal_apply, mul_ite, mul_zero]
    split_ifs <;> simp_all
  rho_e := by
    apply Subtype.ext
    ext r s
    rw [m4J_c_entry]
    change _ = ((m4Eigen i + m4Eigen j) / 2) • (m4Edge i j 1 : M4) r s
    rw [m4Edge_entry]
    simp only [star_one, Complex.real_smul]
    split_ifs <;> simp_all <;> push_cast <;> ring
  rho_n := by
    apply Subtype.ext
    ext r s
    rw [m4J_c_entry]
    change _ = (((m4Eigen i + m4Eigen j) / 2 +
      (m4Eigen i - m4Eigen j) / 2) • (m4N i : M4)) r s
    simp only [m4N, m4Herm, Matrix.smul_apply, Matrix.diagonal_apply,
      Complex.real_smul]
    split_ifs <;> simp_all <;> push_cast <;> ring
  jordan_ej := by
    apply Subtype.ext
    ext r s
    have hc : star ι = -ι := by rcases hι with rfl | rfl <;> simp
    simp [m4J, m4Jordan, m4JordanVal, m4Edge, m4Herm,
      Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_same,
      Matrix.single_mul_single_of_ne, hij, hij.symm,
      hc, Matrix.single_apply, Matrix.smul_apply]
    split_ifs <;> simp_all <;> ring
  jordan_nj := by
    apply Subtype.ext
    ext r s
    rw [m4J_n_entry, m4Edge_entry]
    split_ifs <;> simp_all

private theorem m4Pair_companion (ι : ℂ) (hι : ι = Complex.I ∨ ι = -Complex.I)
    (i j : Fin 4) (hij : i ≠ j) :
    m4Kappa m4C ι hι (m4Edge i j ι) =
        (-((m4Pair ι hι i j hij).lam)) • m4Edge i j 1 ∧
    m4J m4C (m4Edge i j ι) =
        (m4Pair ι hι i j hij).μ • m4Edge i j ι ∧
    m4J (m4N i) (m4Edge i j 1) = m4Edge i j 1 := by
  have hc : star ι = -ι := by rcases hι with rfl | rfl <;> simp
  have hs : ι * ι = -1 := by rcases hι with rfl | rfl <;> simp
  refine ⟨?_, ?_, ?_⟩
  · apply Subtype.ext
    ext r s
    rw [m4K_c_entry]
    change _ = (-((m4Eigen i - m4Eigen j) / 2)) • (m4Edge i j 1 : M4) r s
    rw [m4Edge_entry, m4Edge_entry]
    simp only [hc, star_one, Complex.real_smul]
    rcases hι with rfl | rfl
    all_goals split_ifs <;> simp_all <;> push_cast <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  · apply Subtype.ext
    ext r s
    rw [m4J_c_entry]
    change _ = ((m4Eigen i + m4Eigen j) / 2) • (m4Edge i j ι : M4) r s
    rw [m4Edge_entry]
    simp only [hc, Complex.real_smul]
    split_ifs <;> simp_all <;> push_cast <;> ring
    all_goals aesop
  · apply Subtype.ext
    ext r s
    rw [m4J_n_entry, m4Edge_entry]
    split_ifs <;> simp_all

private theorem m4Op_complex_smul (a : M4E) (z : ℂ) (v : M4H) :
    m4Op a (z • v) = z • m4Op a v := (m4OpVal a).map_smul z v

private theorem m4N_single (i : Fin 4) (z : ℂ) :
    m4Op (m4N i) (EuclideanSpace.single i z) =
      (2 : ℝ) • EuclideanSpace.single i z := by
  rw [m4N_apply]
  ext r
  by_cases h : r = i <;> simp [PiLp.single_apply, h, Complex.real_smul]

private theorem m4_pair_support (i : Fin 4) (t : M4E) :
    m4J (m4N i) ((m4Eigen i) • m4J (m4N i) t -
      m4J (m4N i) (m4J m4C t)) =
      (m4Eigen i) • m4J (m4N i) t - m4J (m4N i) (m4J m4C t) := by
  apply Subtype.ext
  ext r s
  simp only [m4J_n_entry, Submodule.coe_sub, Submodule.coe_smul,
    Matrix.sub_apply, Matrix.smul_apply, m4J_c_entry, Complex.real_smul]
  split_ifs <;> simp_all <;> push_cast <;> ring

private theorem m4_probe_supported (i j : Fin 4) (hi : i ≠ 3) (hj : j ≠ 3)
    (z : ℂ) (T α : ℝ) :
    m4ActorSupported (T • m4Edge i j z + α • m4N i) := by
  intro r s hrs
  simp only [Submodule.coe_add, Submodule.coe_smul, Matrix.add_apply,
    Matrix.smul_apply, m4Edge_entry, m4N, m4Herm, Matrix.diagonal_apply]
  rcases hrs with rfl | rfl <;> simp_all [eq_comm]

private theorem m4_pair_unit_quadratic
    (ι : ℂ) (hι : ι = Complex.I ∨ ι = -Complex.I)
    (i j : Fin 4) (hij : i ≠ j) (hi : i ≠ 3) (hj : j ≠ 3)
    (hlam : (m4Eigen i - m4Eigen j) / 2 ≠ 0) (t g : M4E)
    (hPB : ∀ (v : M4H), ‖v‖ = 1 → ∀ x : M4E, m4ActorSupported x →
      scalarPB m4J (m4Kappa m4C ι hι) (m4J m4C) t (m4J m4C t) g x
        (vectorReading m4VectorModel v))
    (ξ : M4H) (hξ : ‖ξ‖ = 1) (hxi : ξ i = 0) :
    inner ℂ (m4Op (m4Edge i j ι) ξ) (m4Op g ξ) =
      ι * inner ℂ (m4Op (m4Edge i j ι) ξ)
        (m4Op ((m4Eigen i) • m4J (m4N i) t -
          m4J (m4N i) (m4J m4C t)) ξ) := by
  let y := m4Op (m4Edge i j ι) ξ
  let d : ℝ := ‖y‖
  by_cases hd : d = 0
  · have hy : y = 0 := norm_eq_zero.mp hd
    change inner ℂ y _ = ι * inner ℂ y _
    simp [hy]
  let η := d⁻¹ • y
  have hy : y = EuclideanSpace.single i (ι * ξ j) := by
    simp [y, m4Edge_apply, hxi]
  have hnormη : ‖η‖ = 1 := by
    rw [show η = d⁻¹ • y from rfl, norm_smul, Real.norm_eq_abs]
    change |d⁻¹| * d = 1
    rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg y)), inv_mul_cancel₀ hd]
  have hnη : m4Op (m4N i) η = (2 : ℝ) • η := by
    simp only [η, map_smul, hy, m4N_single, smul_comm d⁻¹ (2 : ℝ)]
  have hjξ : y = d • η := by simp [η, smul_smul, hd]
  have heξ : m4Op (m4Edge i j 1) ξ = d • ((-ι) • η) := by
    rw [smul_comm d (-ι), ← hjξ, hy]
    ext r
    simp [m4Edge_apply, hxi, PiLp.single_apply]
    split_ifs <;> simp_all
    all_goals rcases hι with rfl | rfl <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  obtain ⟨hκ, hρ, hne⟩ := m4Pair_companion ι hι i j hij
  have ha : (m4Pair ι hι i j hij).μ + (m4Pair ι hι i j hij).lam = m4Eigen i := by
    dsimp [m4Pair]; ring
  have h := fixed_output_two_axis_identity m4J m4J_comm
    (m4Kappa m4C ι hι) (m4J m4C) (m4Pair ι hι i j hij) m4VectorModel
    t (m4J m4C t) g hκ hρ hne
    (fun v hv T α => ⟨hPB v hv _ (m4_probe_supported i j hi hj 1 T α),
      hPB v hv _ (m4_probe_supported i j hi hj ι T α)⟩)
    ι hι ξ η d hd hlam hξ hnormη
    (by change m4Op (m4N i) ξ = 0; simp [m4N_apply, hxi])
    hnη (by change m4Op (m4N i) ((-ι) • η) = _
            rw [m4Op_complex_smul, hnη, smul_comm]) hjξ heξ
    (by rw [ha]; exact m4_pair_support i t)
  change inner ℂ η (m4Op g ξ) = _ at h
  rw [ha] at h
  change inner ℂ η (m4Op g ξ) = ι * inner ℂ η
    (m4Op ((m4Eigen i) • m4J (m4N i) t - m4J (m4N i) (m4J m4C t)) ξ) at h
  change inner ℂ y _ = ι * inner ℂ y _
  rw [hjξ]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left,
    Complex.conj_ofReal, h]
  ring

private theorem m4_pair_quadratic
    (ι : ℂ) (hι : ι = Complex.I ∨ ι = -Complex.I)
    (i j : Fin 4) (hij : i ≠ j) (hi : i ≠ 3) (hj : j ≠ 3)
    (hlam : (m4Eigen i - m4Eigen j) / 2 ≠ 0) (t g : M4E)
    (hPB : ∀ (v : M4H), ‖v‖ = 1 → ∀ x : M4E, m4ActorSupported x →
      scalarPB m4J (m4Kappa m4C ι hι) (m4J m4C) t (m4J m4C t) g x
        (vectorReading m4VectorModel v))
    (ξ : M4H) (hxi : ξ i = 0) :
    inner ℂ (m4Op (m4Edge i j ι) ξ) (m4Op g ξ) =
      ι * inner ℂ (m4Op (m4Edge i j ι) ξ)
        (m4Op ((m4Eigen i) • m4J (m4N i) t -
          m4J (m4N i) (m4J m4C t)) ξ) := by
  by_cases hz : ξ = 0
  · simp [hz]
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let w := (‖ξ‖⁻¹ : ℝ) • ξ
  have hw : ‖w‖ = 1 := by
    simp [w, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg ξ)), hn]
  have h := m4_pair_unit_quadratic ι hι i j hij hi hj hlam t g hPB w hw
    (by simp [w, hxi])
  simp only [w, map_smul] at h
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, Complex.ofReal_inv] at h
  field_simp at h
  have hc : ((1 / ‖ξ‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (one_div_ne_zero hn)
  apply mul_left_cancel₀ (a := ((1 / ‖ξ‖ : ℝ) : ℂ) * star ((1 / ‖ξ‖ : ℝ) : ℂ))
    (mul_ne_zero hc (star_ne_zero.mpr hc))
  convert h using 1 <;> simp only [starRingEnd_apply, one_div, Complex.ofReal_inv] <;> ring

private def m4P (i : Fin 4) : M4E :=
  m4Herm (Matrix.diagonal (fun r => if r = i then 0 else 1)) (by
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext r
    change star (if r = i then (0 : ℂ) else 1) = _
    split_ifs <;> simp)

private theorem m4P_apply (i : Fin 4) (v : M4H) (r : Fin 4) :
    m4OpVal (m4P i) v r = if r = i then 0 else v r := by
  change m4Op (m4P i) v r = _
  simp [m4Op_apply, m4P, m4Herm, Matrix.diagonal_apply, ite_mul]

private theorem m4Op_symmetric (a : M4E) : (m4OpVal a).IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  change star (a : M4) = (a : M4)
  exact a.property

private theorem m4_row_of_quadratic
    (ι : ℂ) (hι : ι = Complex.I ∨ ι = -Complex.I)
    (i j : Fin 4) (hij : i ≠ j) (g V : M4E)
    (hquad : ∀ ξ : M4H, ξ i = 0 →
      inner ℂ (m4Op (m4Edge i j ι) ξ) (m4Op g ξ) =
        ι * inner ℂ (m4Op (m4Edge i j ι) ξ) (m4Op V ξ)) :
    ∀ k : Fin 4, k ≠ i → (g : M4) i k = ι * (V : M4) i k := by
  let P := m4OpVal (m4P i)
  let Y := m4OpVal (m4Edge i j ι)
  let A := m4OpVal g - ι • m4OpVal V
  have hz (v : M4H) : inner ℂ (Y (P v)) (A (P v)) = 0 := by
    have h := hquad (P v) (by simp [P, m4P_apply])
    change inner ℂ (Y (P v)) (m4OpVal g (P v)) =
      ι * inner ℂ (Y (P v)) (m4OpVal V (P v)) at h
    simp [A, inner_sub_right, inner_smul_right, h]
  have hzero : P ∘ₗ Y ∘ₗ A ∘ₗ P = 0 :=
    (_root_.inner_map_self_eq_zero _).mp (by
      intro v
      change inner ℂ (P (Y (A (P v)))) v = 0
      rw [m4Op_symmetric (m4P i), m4Op_symmetric (m4Edge i j ι)]
      exact inner_eq_zero_symm.mpr (hz v))
  intro k hki
  have hpek : P (EuclideanSpace.single k 1) = EuclideanSpace.single k 1 := by
    ext r
    simp only [P, m4P_apply, PiLp.single_apply]
    split_ifs <;> simp_all [eq_comm]
  have hread := congrArg
    (fun L : M4H →ₗ[ℂ] M4H => L (EuclideanSpace.single k 1) j) hzero
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, PiLp.zero_apply, hpek] at hread
  have hyp : (Y (A (EuclideanSpace.single k 1))) j =
      star ι * ((g : M4) i k - ι * (V : M4) i k) := by
    change m4Op (m4Edge i j ι) (A (EuclideanSpace.single k 1)) j = _
    rw [m4Edge_apply]
    simp [PiLp.single_apply, hij.symm, A, m4OpVal, Matrix.toEuclideanLin,
      Matrix.mulVec_single, Matrix.mulVec, Matrix.single, mul_sub]
  rw [show (P (Y (A (EuclideanSpace.single k 1)))) j =
      (Y (A (EuclideanSpace.single k 1))) j by simp [P, m4P_apply, hij.symm], hyp] at hread
  have hnι : star ι ≠ 0 := by rcases hι with rfl | rfl <;> simp
  exact sub_eq_zero.mp ((mul_eq_zero.mp hread).resolve_left hnι)

/-- Full positive-functional scalar PB on the original actor-supported probes
determines every off-diagonal entry of the complete four-dimensional output.
The environment diagonal residual is unrestricted. -/
theorem m4_scalar_pb_diagonal_residual (q₁ q₂ : ℂ) (_hq : q₁ * q₂ ≠ 0)
    (ι : ℂ) (hι : ι = Complex.I ∨ ι = -Complex.I) (g : M4E)
    (hPB : ∀ (φ : M4 →ₗ[ℂ] ℂ), m4Positive φ →
      ∀ x : M4E, m4ActorSupported x →
        scalarPB m4J (m4Kappa m4C ι hι) (m4J m4C)
          (m4T q₁ q₂) (m4J m4C (m4T q₁ q₂)) g x (m4RealFunctional φ)) :
    ∃ s : Fin 4 → ℝ, (g : M4) - (m4Kappa m4C ι hι (m4T q₁ q₂) : M4) =
      Matrix.diagonal (fun i => (s i : ℂ)) := by
  let t := m4T q₁ q₂
  have hvPB := m4_positive_pb_transfer hPB
  have row (i : Fin 4) (hi : i ≠ 3) (k : Fin 4) (hki : k ≠ i) :
      (g : M4) i k = (m4Kappa m4C ι hι t : M4) i k := by
    let j : Fin 4 := if i = 0 then 1 else 0
    have hij : i ≠ j := by dsimp [j]; split_ifs <;> simp_all
    have hj : j ≠ 3 := by dsimp [j]; split_ifs <;> norm_num
    have hlam : (m4Eigen i - m4Eigen j) / 2 ≠ 0 := by
      fin_cases i <;> norm_num [m4Eigen, j] at *
    have hquad := m4_pair_quadratic ι hι i j hij hi hj hlam t g hvPB
    have hr := m4_row_of_quadratic ι hι i j hij g
      ((m4Eigen i) • m4J (m4N i) t - m4J (m4N i) (m4J m4C t)) hquad k hki
    rw [hr, m4K_c_entry]
    simp only [Submodule.coe_sub, Submodule.coe_smul, Matrix.sub_apply,
      Matrix.smul_apply, m4J_n_entry, m4J_c_entry, Complex.real_smul]
    simp only [if_pos rfl, if_neg hki, add_zero]
    push_cast
    ring
  have herm (a : M4E) : (a : M4).IsHermitian := a.property
  apply m4_full_row_reconstruction _ _ (herm g) (herm _)
  intro i k hik
  by_cases hi : i = 3
  · have hk : k ≠ 3 := by simpa [hi] using hik.symm
    rw [← (herm g).apply i k, ← (herm (m4Kappa m4C ι hι t)).apply i k,
      row k hk i hik]
  · exact row i hi k hik.symm

example (q₁ q₂ : ℂ) : (m4T q₁ q₂ : M4) =
    !![0, 0, 0, q₁; 0, 0, 0, q₂; 0, 0, 0, 0; star q₁, star q₂, 0, 0] := by
  ext r s
  fin_cases r <;> fin_cases s <;> simp [m4T, m4Edge, m4Herm, Matrix.single_apply]

example : (m4C : M4) = Matrix.diagonal ![1, 2, 3, 0] := by
  ext r s
  fin_cases r <;> fin_cases s <;> simp [m4C, m4Herm, m4Eigen, Matrix.diagonal_apply]

#print axioms m4_scalar_pb_diagonal_residual

end D5.S3.Quantum.Algebra.PBFixedOutputM4
