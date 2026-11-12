/- GID: D5/S3/Topology/EJASpectralNorm
   generality: G
   mirror-B: D5/B/S3/Topology/EJASpectralNorm
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Algebra.Jordan.Basic]
   utility: none
   digest: The spectral JB norm derived from the original finite Euclidean Jordan laws. -/

/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license; see docs/reports/third-party/euclidean-jordan-LICENSE.txt.
Authors: Bryan Ehrlich

The private single-idempotent Peirce and inner-product lemmas are adapted from
EuclideanJordan/Bridge.lean, EuclideanJordan/Peirce.lean and EuclideanJordan/Order.lean in ehrlich-b/euclidean-jordan,
immutable revision a83407e4dbf73c77c31a2291c02f20b37a5ebbaf.
Only dependencies used by the spectral norm construction are retained.
-/

module

public import D5.S3.Topology.EJAFiniteSpectral
public import D5.S3.Topology.JBAlgebra
public import Mathlib.Algebra.QuadraticDiscriminant

/-! The spectral norm is derived from all normalized idempotent functionals. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace D5.S3.Topology.EJASpectralNorm
open scoped BigOperators
local notation "L" => AddMonoid.End.mulLeft
section Linearisation

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J]

/-- The repeated-variable specialization of Mathlib's polarized Jordan identity. -/
private theorem two_lin1_raw (a b : J) :
    (2 : ℕ) • ⁅L b, L (a * a)⁆ + (4 : ℕ) • ⁅L a, L (a * b)⁆ = 0 := by
  have h := two_nsmul_lie_lmul_lmul_add_add_eq_zero a a b
  rw [mul_comm b a] at h
  rw [← h]
  abel

/-- `two_lin1_raw` evaluated at an element. -/
private theorem two_lin1_apply (a b w : J) :
    (2 : ℕ) • (b * (a * a * w) - a * a * (b * w))
      + (4 : ℕ) • (a * (a * b * w) - a * b * (a * w)) = 0 := by
  have h := congrArg (fun f : AddMonoid.End J => f w) (two_lin1_raw a b)
  simpa [Ring.lie_def, sub_eq_add_neg, AddMonoidHom.add_apply, AddMonoid.End.coe_mul,
    AddMonoidHom.neg_apply, AddMonoid.End.mulLeft, AddMonoidHom.mul_apply] using h

end Linearisation

section Projections
variable {J : Type*} [NonUnitalNonAssocCommRing J] [Module ℝ J] [IsScalarTower ℝ J J]

/-- The Jordan multiplication operator `L_c : y ↦ c ∘ y`, as an `ℝ`-linear map. -/
private def mulL (c : J) : J →ₗ[ℝ] J where
  toFun y := c * y
  map_add' := mul_add c
  map_smul' r y := D5.S3.Topology.EJAFiniteSpectral.mul_smul_comm' r c y

/-- The Peirce projection onto the `1`-eigenspace of `L_c`: the Lagrange interpolant
`2L² − L`, which is `1` at `1` and `0` at `0` and `1/2`. -/
private def peirceOne (c : J) : J →ₗ[ℝ] J := (2 : ℝ) • (mulL c ∘ₗ mulL c) - mulL c

/-- The Peirce projection onto the `1/2`-eigenspace of `L_c`: the Lagrange interpolant
`4L − 4L²`. -/
private def peirceHalf (c : J) : J →ₗ[ℝ] J := (4 : ℝ) • mulL c - (4 : ℝ) • (mulL c ∘ₗ mulL c)

private theorem peirceOne_of_eigen {c y : J} (h : c * y = y) : peirceOne c y = y := by
  change (2 : ℝ) • (c * (c * y)) - c * y = y
  simp only [h]
  module

private theorem peirceHalf_of_eigen_half {c y : J} (h : c * y = (2 : ℝ)⁻¹ • y) :
    peirceHalf c y = y := by
  change (4 : ℝ) • (c * y) - (4 : ℝ) • (c * (c * y)) = y
  simp only [h, D5.S3.Topology.EJAFiniteSpectral.mul_smul_comm']
  module

end Projections

section Peirce

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J]

omit [IsCommJordan J] [IsScalarTower ℝ J J] in
private theorem two_smul_eq_zero' {x : J} (h : (2 : ℕ) • x = 0) : x = 0 := by
  have h2 : (2 : ℝ) • x = 0 := by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Nat.cast_smul_eq_nsmul]
    exact h
  simpa using h2

omit [IsScalarTower ℝ J J] in
/-- **The Peirce polynomial identity.** For an idempotent `c`,

  `2·L_c³ − 3·L_c² + L_c = 0`,   i.e.   `L_c (L_c − 1) (2L_c − 1) = 0`.

The repeated-variable polarized identity at `a := c`, `b := y`, applied to `c`,
gives this polynomial from the Jordan law and `c ∘ c = c`. -/
private theorem peirce_poly {c : J} (hc : c * c = c) (y : J) :
    (2 : ℕ) • (c * (c * (c * y))) + c * y = (3 : ℕ) • (c * (c * y)) := by
  have h := two_lin1_apply c y c
  simp only [hc, mul_comm y c, mul_comm (c * y) c] at h
  refine sub_eq_zero.mp (two_smul_eq_zero' ?_)
  rw [← h]
  abel

omit [IsScalarTower ℝ J J] in
/-- `peirce_poly` solved for the cube, over `ℝ` — the form every consumer below uses. -/
private theorem peirce_cube {c : J} (hc : c * c = c) (y : J) :
    c * (c * (c * y)) = (3 / 2 : ℝ) • (c * (c * y)) - (2 : ℝ)⁻¹ • (c * y) := by
  have h := peirce_poly hc y
  have h2 : (2 : ℝ) • (c * (c * (c * y))) + c * y = (3 : ℝ) • (c * (c * y)) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact h
  have h3 : (2 : ℝ) • (c * (c * (c * y))) = (3 : ℝ) • (c * (c * y)) - c * y :=
    eq_sub_of_add_eq h2
  calc c * (c * (c * y)) = (2 : ℝ)⁻¹ • ((2 : ℝ) • (c * (c * (c * y)))) := by module
    _ = (2 : ℝ)⁻¹ • ((3 : ℝ) • (c * (c * y)) - c * y) := by rw [h3]
    _ = (3 / 2 : ℝ) • (c * (c * y)) - (2 : ℝ)⁻¹ • (c * y) := by module

/-- The image of `peirceOne c` lies in the `1`-eigenspace of `L_c`. -/
private theorem mul_peirceOne {c : J} (hc : c * c = c) (y : J) :
    c * peirceOne c y = peirceOne c y := by
  change c * ((2 : ℝ) • (c * (c * y)) - c * y) =
    (2 : ℝ) • (c * (c * y)) - c * y
  simp only [mul_sub, D5.S3.Topology.EJAFiniteSpectral.mul_smul_comm', peirce_cube hc y]
  module

/-- The image of `peirceHalf c` lies in the `1/2`-eigenspace of `L_c`. -/
private theorem mul_peirceHalf {c : J} (hc : c * c = c) (y : J) :
    c * peirceHalf c y = (2 : ℝ)⁻¹ • peirceHalf c y := by
  change c * ((4 : ℝ) • (c * y) - (4 : ℝ) • (c * (c * y))) =
    (2 : ℝ)⁻¹ • ((4 : ℝ) • (c * y) - (4 : ℝ) • (c * (c * y)))
  simp only [mul_sub, D5.S3.Topology.EJAFiniteSpectral.mul_smul_comm', peirce_cube hc y]
  module

end Peirce

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
@[instance_reducible] private def ringOfBilinear (m : J →ₗ[ℝ] J →ₗ[ℝ] J)
    (hcomm : ∀ x y, m x y = m y x) : NonUnitalNonAssocCommRing J :=
  { (inferInstance : AddCommGroup J) with
    mul := fun x y => m x y
    left_distrib := fun x y z => (m x).map_add y z
    right_distrib := fun x y z => congrArg (fun f : J →ₗ[ℝ] J => f z) (m.map_add x y)
    zero_mul := fun x => congrArg (fun f : J →ₗ[ℝ] J => f x) m.map_zero
    mul_zero := fun x => (m x).map_zero
    mul_comm := hcomm }
private theorem smul_bilinear (m : J →ₗ[ℝ] J →ₗ[ℝ] J) (r : ℝ) (x y : J) :
    m (r • x) y = r • m x y := by simp
variable {m : J →ₗ[ℝ] J →ₗ[ℝ] J}
private theorem inner_mul_self_nonneg_of_idem
    (hcomm : ∀ x y : J, m x y = m y x)
    (hjordan : ∀ a b : J, m (m a b) (m a a) = m a (m b (m a a)))
    (hassoc : ∀ x y z : J, inner ℝ (m x y) z = inner ℝ y (m x z))
    {c : J} (hc : m c c = c) (y : J) :
    0 ≤ inner ℝ (m c y) y := by
  let : NonUnitalNonAssocCommRing J := ringOfBilinear m hcomm
  let : IsCommJordan J := ⟨hjordan⟩
  let : IsScalarTower ℝ J J := ⟨fun r x y => smul_bilinear m r x y⟩
  have hc' : c * c = c := hc
  have hsa : ∀ u v : J, inner ℝ (c * u) v = inner ℝ u (c * v) := fun u v => hassoc c u v
  have hsa1 : ∀ u v : J, inner ℝ (peirceOne c u) v = inner ℝ u (peirceOne c v) := by
    intro u v
    change inner ℝ ((2 : ℝ) • (c * (c * u)) - c * u) v =
      inner ℝ u ((2 : ℝ) • (c * (c * v)) - c * v)
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [hsa (c * u) v, hsa u (c * v), hsa u v]
  have hsah : ∀ u v : J, inner ℝ (peirceHalf c u) v = inner ℝ u (peirceHalf c v) := by
    intro u v
    change inner ℝ ((4 : ℝ) • (c * u) - (4 : ℝ) • (c * (c * u))) v =
      inner ℝ u ((4 : ℝ) • (c * v) - (4 : ℝ) • (c * (c * v)))
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [hsa (c * u) v, hsa u (c * v), hsa u v]
  have hid1 : peirceOne c (peirceOne c y) = peirceOne c y :=
    peirceOne_of_eigen (mul_peirceOne hc' y)
  have hidh : peirceHalf c (peirceHalf c y) = peirceHalf c y :=
    peirceHalf_of_eigen_half (mul_peirceHalf hc' y)
  have hsplit : (m c y : J) = peirceOne c y + (2 : ℝ)⁻¹ • peirceHalf c y := by
    change c * y = (2 : ℝ) • (c * (c * y)) - c * y +
      (2 : ℝ)⁻¹ • ((4 : ℝ) • (c * y) - (4 : ℝ) • (c * (c * y)))
    module
  have key1 : inner ℝ (peirceOne c y) (peirceOne c y) = inner ℝ (peirceOne c y) y := by
    rw [hsa1 y (peirceOne c y), hid1, real_inner_comm]
  have keyh : inner ℝ (peirceHalf c y) (peirceHalf c y) = inner ℝ (peirceHalf c y) y := by
    rw [hsah y (peirceHalf c y), hidh, real_inner_comm]
  have h1 : (0 : ℝ) ≤ inner ℝ (peirceOne c y) y := key1 ▸ real_inner_self_nonneg
  have hh : (0 : ℝ) ≤ inner ℝ (peirceHalf c y) y := keyh ▸ real_inner_self_nonneg
  rw [hsplit, inner_add_left, real_inner_smul_left]
  linarith

/-- Inner associativity reads a spectral coefficient against its nonzero idempotent. -/
private theorem inner_left_coeff
    (hassoc : ∀ x y z : J, inner ℝ (m x y) z = inner ℝ y (m x z))
    {n : ℕ} {q : Fin n → J} {lam : Fin n → ℝ}
    (hidem : ∀ i, m (q i) (q i) = q i)
    (horth : ∀ i j, i ≠ j → m (q i) (q j) = 0)
    {x : J} (hx : x = ∑ i, lam i • q i) (k : Fin n) :
    inner ℝ (q k) x = lam k * inner ℝ (q k) (q k) := by
  have horthinner : ∀ i, i ≠ k → inner ℝ (q k) (q i) = (0 : ℝ) := by
    intro i hi
    calc inner ℝ (q k) (q i) = inner ℝ (m (q k) (q k)) (q i) := by rw [hidem k]
      _ = inner ℝ (q k) (m (q k) (q i)) := hassoc (q k) (q k) (q i)
      _ = 0 := by rw [horth k i (Ne.symm hi), inner_zero_right]
  rw [hx, inner_sum, Finset.sum_eq_single k]
  · rw [real_inner_smul_right]
  · intro i _ hi
    rw [real_inner_smul_right, horthinner i hi, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {x : X} {S : X →ₗ[ℝ] X →ₗ[ℝ] X} {u : X}

/-- The normalized inner functional; the zero idempotent gives the zero functional. -/
def coeff (c : X) : X →ₗ[ℝ] ℝ where
  toFun x := inner ℝ c x / inner ℝ c c
  map_add' x y := by simp only [inner_add_right, add_div]
  map_smul' r x := by
    simp only [real_inner_smul_right, mul_div_assoc, RingHom.id_apply, smul_eq_mul]

@[simp] private theorem coeff_zero (x : X) : coeff (0 : X) x = 0 := by
  simp [coeff]

private theorem coeff_unit (A : EJAFiniteSpectral.Data X S u) {c : X}
    (hc : S c c = c) (hc0 : c ≠ 0) : coeff c u = 1 := by
  have hi : inner ℝ c u = inner ℝ c c := by
    calc
      inner ℝ c u = inner ℝ (S c c) u := by rw [hc]
      _ = inner ℝ c (S c u) := A.inner_assoc c c u
      _ = inner ℝ c c := by rw [A.symm c u, A.unit_mul]
  exact (congrArg (fun t : ℝ => t / inner ℝ c c) hi).trans
    (div_self (real_inner_self_pos.mpr hc0).ne')

private theorem coeff_square_nonneg (A : EJAFiniteSpectral.Data X S u)
    {c : X} (hc : S c c = c) (y : X) : 0 ≤ coeff c (S y y) := by
  have hi : inner ℝ c (S y y) = inner ℝ (S c y) y := by
    calc
      inner ℝ c (S y y) = inner ℝ (S y y) c := real_inner_comm (S y y) c
      _ = inner ℝ y (S y c) := A.inner_assoc y y c
      _ = inner ℝ y (S c y) := by rw [A.symm y c]
      _ = inner ℝ (S c y) y := real_inner_comm (S c y) y
  change 0 ≤ inner ℝ c (S y y) / inner ℝ c c
  apply div_nonneg _ real_inner_self_nonneg
  rw [hi]
  exact inner_mul_self_nonneg_of_idem A.symm A.jordan A.inner_assoc hc y

/-- All idempotent evaluations, including zero, so this set is nonempty in the zero algebra. -/
def values (S : X →ₗ[ℝ] X →ₗ[ℝ] X) (x : X) : Set ℝ :=
  {t | ∃ c : X, S c c = c ∧ t = |coeff c x|}

/-- The supremum of the absolute normalized nonzero-idempotent functionals, with zero adjoined. -/
def spectralNorm (S : X →ₗ[ℝ] X →ₗ[ℝ] X) (x : X) : ℝ := sSup (values S x)

private theorem values_nonempty (x : X) : (values S x).Nonempty :=
  ⟨0, 0, by simp, by simp⟩

private theorem coeff_bound (A : EJAFiniteSpectral.Data X S u)
    {n : ℕ} {e : Fin n → X} {r : Fin n → ℝ}
    (he : ∀ i, S (e i) (e i) = e i) (heu : ∑ i, e i = u)
    (hex : ∑ i, r i • e i = x) {R : ℝ} (hR : 0 ≤ R)
    (hr : ∀ i, e i ≠ 0 → |r i| ≤ R) {c : X} (hc : S c c = c) :
    |coeff c x| ≤ R := by
  classical
  by_cases hc0 : c = 0
  · subst c; simpa using hR
  have hw (i : Fin n) : 0 ≤ coeff c (e i) := by
    simpa only [he i] using coeff_square_nonneg A hc (e i)
  have hsum : ∑ i, coeff c (e i) = 1 := by
    rw [← map_sum, heu, coeff_unit A hc hc0]
  rw [← hex, map_sum]
  calc
    |∑ i, coeff c (r i • e i)| ≤ ∑ i, |coeff c (r i • e i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |r i| * coeff c (e i) := by
      simp only [map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (hw _)]
    _ ≤ ∑ i, R * coeff c (e i) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : e i = 0
      · simp [hi]
      · exact mul_le_mul_of_nonneg_right (hr i hi) (hw i)
    _ = R := by rw [← Finset.mul_sum, hsum, mul_one]

variable [FiniteDimensional ℝ X]

private theorem values_bdd (A : EJAFiniteSpectral.Data X S u) (x : X) :
    BddAbove (values S x) := by
  obtain ⟨n, e, r, he, _, heu, hex, _, _⟩ := EJAFiniteSpectral.finite_spectral_resolution A x
  refine ⟨∑ i, |r i|, ?_⟩
  rintro t ⟨c, hc, rfl⟩
  exact coeff_bound A he heu hex (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (fun i _ => Finset.single_le_sum (fun j _ => abs_nonneg (r j)) (Finset.mem_univ i)) hc

private theorem coeff_le_norm (A : EJAFiniteSpectral.Data X S u)
    {c : X} (hc : S c c = c) (x : X) : |coeff c x| ≤ spectralNorm S x :=
  le_csSup (values_bdd A x) ⟨c, hc, rfl⟩

private theorem norm_nonneg' (A : EJAFiniteSpectral.Data X S u) (x : X) :
    0 ≤ spectralNorm S x := by
  simpa using coeff_le_norm A (c := 0) (by simp) x

omit [FiniteDimensional ℝ X] in
private theorem norm_le (x : X) {R : ℝ}
    (h : ∀ c, S c c = c → |coeff c x| ≤ R) : spectralNorm S x ≤ R := by
  apply csSup_le (values_nonempty x)
  rintro t ⟨c, hc, rfl⟩
  exact h c hc

omit [FiniteDimensional ℝ X] in
private theorem norm_le_of_spectral (A : EJAFiniteSpectral.Data X S u)
    {n : ℕ} {e : Fin n → X} {r : Fin n → ℝ}
    (he : ∀ i, S (e i) (e i) = e i) (heu : ∑ i, e i = u)
    (hex : ∑ i, r i • e i = x) {R : ℝ} (hR : 0 ≤ R)
    (hr : ∀ i, e i ≠ 0 → |r i| ≤ R) : spectralNorm S x ≤ R :=
  norm_le x (fun _ hc => coeff_bound A he heu hex hR hr hc)

private theorem spectral_coeff_le (A : EJAFiniteSpectral.Data X S u)
    {n : ℕ} {e : Fin n → X} {r : Fin n → ℝ}
    (he : ∀ i, S (e i) (e i) = e i)
    (heo : ∀ i j, i ≠ j → S (e i) (e j) = 0)
    (hex : ∑ i, r i • e i = x) (i : Fin n) (hi : e i ≠ 0) :
    |r i| ≤ spectralNorm S x := by
  have hread := inner_left_coeff A.inner_assoc he heo hex.symm i
  have hc : coeff (e i) x = r i := by
    change inner ℝ (e i) x / inner ℝ (e i) (e i) = r i
    rw [hread, mul_div_cancel_right₀ _ (real_inner_self_pos.mpr hi).ne']
  simpa only [hc] using coeff_le_norm A (he i) x

private theorem norm_triangle' (A : EJAFiniteSpectral.Data X S u) (x y : X) :
    spectralNorm S (x + y) ≤ spectralNorm S x + spectralNorm S y := by
  apply norm_le
  intro c hc
  rw [map_add]
  exact (abs_add_le _ _).trans (add_le_add (coeff_le_norm A hc x) (coeff_le_norm A hc y))

private theorem norm_smul' (A : EJAFiniteSpectral.Data X S u) (t : ℝ) (x : X) :
    spectralNorm S (t • x) = |t| * spectralNorm S x := by
  have upper (r : ℝ) (y : X) : spectralNorm S (r • y) ≤ |r| * spectralNorm S y := by
    apply norm_le
    intro c hc
    rw [map_smul, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (coeff_le_norm A hc y) (abs_nonneg r)
  apply le_antisymm (upper t x)
  by_cases ht : t = 0
  · subst t; simpa using norm_nonneg' A (0 : X)
  have hh := upper t⁻¹ (t • x)
  rw [smul_smul, inv_mul_cancel₀ ht, one_smul, abs_inv] at hh
  exact (le_inv_mul_iff₀ (abs_pos.mpr ht)).mp hh

private theorem norm_definite (A : EJAFiniteSpectral.Data X S u) (x : X) :
    spectralNorm S x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    obtain ⟨n, e, r, he, heo, heu, hex, _, _⟩ := EJAFiniteSpectral.finite_spectral_resolution A x
    rw [← hex]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : e i = 0
    · simp [hi]
    · have hb := spectral_coeff_le A he heo hex i hi
      rw [hx] at hb
      have hr : r i = 0 := abs_nonpos_iff.mp hb
      simp [hr]
  · rintro rfl
    apply le_antisymm
    · apply norm_le
      intro c _
      simp
    · exact norm_nonneg' A 0

private theorem norm_square (A : EJAFiniteSpectral.Data X S u) (x : X) :
    spectralNorm S (S x x) = spectralNorm S x ^ 2 := by
  obtain ⟨n, e, r, he, heo, heu, hex, hesq, _⟩ := EJAFiniteSpectral.finite_spectral_resolution A x
  have hupper : spectralNorm S (S x x) ≤ spectralNorm S x ^ 2 := by
    apply norm_le_of_spectral A he heu hesq (sq_nonneg _)
    intro i hi
    rw [abs_of_nonneg (sq_nonneg _)]
    have hb := (sq_le_sq₀ (abs_nonneg (r i)) (norm_nonneg' A x)).mpr
      (spectral_coeff_le A he heo hex i hi)
    simpa only [sq_abs] using hb
  have hlower : spectralNorm S x ≤ Real.sqrt (spectralNorm S (S x x)) := by
    apply norm_le_of_spectral A he heu hex (Real.sqrt_nonneg _)
    intro i hi
    have hb := spectral_coeff_le A he heo hesq i hi
    rw [abs_of_nonneg (sq_nonneg _)] at hb
    exact Real.abs_le_sqrt hb
  have hs := Real.sq_sqrt (norm_nonneg' A (S x x))
  have hn := norm_nonneg' A x
  have hr := Real.sqrt_nonneg (spectralNorm S (S x x))
  nlinarith

private theorem norm_square_mono (A : EJAFiniteSpectral.Data X S u) (x y : X) :
    spectralNorm S (S x x) ≤ spectralNorm S (S x x + S y y) := by
  apply norm_le
  intro c hc
  rw [abs_of_nonneg (coeff_square_nonneg A hc x)]
  have hb := coeff_le_norm A hc (S x x + S y y)
  rw [map_add, abs_of_nonneg (add_nonneg (coeff_square_nonneg A hc x)
    (coeff_square_nonneg A hc y))] at hb
  linarith [coeff_square_nonneg A hc y]

private theorem coeff_cauchy (A : EJAFiniteSpectral.Data X S u)
    {c : X} (hc : S c c = c) (x y : X) :
    coeff c (S x y) ^ 2 ≤ coeff c (S x x) * coeff c (S y y) := by
  have hd := discrim_le_zero (a := coeff c (S x x))
    (b := 2 * coeff c (S x y)) (c := coeff c (S y y)) (fun t : ℝ => by
      have hp := coeff_square_nonneg A hc (t • x + y)
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        A.symm y x, smul_eq_mul] at hp
      nlinarith)
  dsimp [discrim] at hd
  nlinarith

private theorem norm_product (A : EJAFiniteSpectral.Data X S u) (x y : X) :
    spectralNorm S (S x y) ≤ spectralNorm S x * spectralNorm S y := by
  apply norm_le
  intro c hc
  have hcx := coeff_le_norm A hc (S x x)
  have hcy := coeff_le_norm A hc (S y y)
  rw [abs_of_nonneg (coeff_square_nonneg A hc x), norm_square A] at hcx
  rw [abs_of_nonneg (coeff_square_nonneg A hc y), norm_square A] at hcy
  have hm := mul_le_mul hcx hcy (coeff_square_nonneg A hc y) (sq_nonneg _)
  have hcs := coeff_cauchy A hc x y
  have hn := mul_nonneg (norm_nonneg' A x) (norm_nonneg' A y)
  nlinarith [sq_abs (coeff c (S x y))]

/-- An explicit type copy, so the given Hilbert norm on X is never replaced. -/
def Space (_A : EJAFiniteSpectral.Data X S u) := X

instance spaceAdd (A : EJAFiniteSpectral.Data X S u) : AddCommGroup (Space A) :=
  inferInstanceAs (AddCommGroup X)

instance spaceModule (A : EJAFiniteSpectral.Data X S u) : Module ℝ (Space A) :=
  inferInstanceAs (Module ℝ X)

/-- The algebraic identification between the normed copy and the original carrier. -/
def equiv (A : EJAFiniteSpectral.Data X S u) : Space A ≃ₗ[ℝ] X := LinearEquiv.refl ℝ X

instance spaceNorm (A : EJAFiniteSpectral.Data X S u) : Norm (Space A) :=
  ⟨fun x => spectralNorm S (equiv A x)⟩

/-- The norm core on the type copy, proved from the original EJA laws. -/
theorem norm_core (A : EJAFiniteSpectral.Data X S u) : NormedSpace.Core ℝ (Space A) where
  norm_nonneg := by
    intro x
    change 0 ≤ spectralNorm S (equiv A x)
    exact norm_nonneg' A (equiv A x)
  norm_smul := by
    intro t x
    change spectralNorm S (t • equiv A x) = ‖t‖ * spectralNorm S (equiv A x)
    rw [Real.norm_eq_abs]
    exact norm_smul' A t (equiv A x)
  norm_triangle := by
    intro x y
    change spectralNorm S (equiv A x + equiv A y) ≤
      spectralNorm S (equiv A x) + spectralNorm S (equiv A y)
    exact norm_triangle' A (equiv A x) (equiv A y)
  norm_eq_zero_iff := by
    intro x
    change spectralNorm S (equiv A x) = 0 ↔ equiv A x = 0
    exact norm_definite A (equiv A x)

instance spaceNormedAddCommGroup (A : EJAFiniteSpectral.Data X S u) :
    NormedAddCommGroup (Space A) := NormedAddCommGroup.ofCore (norm_core A)

instance spaceNormedSpace (A : EJAFiniteSpectral.Data X S u) : NormedSpace ℝ (Space A) :=
  NormedSpace.ofCore (norm_core A)

instance spaceFinite (A : EJAFiniteSpectral.Data X S u) : FiniteDimensional ℝ (Space A) :=
  (equiv A).symm.finiteDimensional

instance spaceComplete (A : EJAFiniteSpectral.Data X S u) : CompleteSpace (Space A) :=
  FiniteDimensional.complete ℝ (Space A)

/-- The same bilinear product on the type copy. -/
def product (A : EJAFiniteSpectral.Data X S u) : Space A →ₗ[ℝ] Space A →ₗ[ℝ] Space A := S

/-- Every original finite real EJA admits the spectral JB realization, including the zero algebra.
No norm law is an input. The carrier identification transports the original product and unit. -/
theorem jb_data (A : EJAFiniteSpectral.Data X S u) :
    JBAlgebra.Data (Space A) (product A) ((equiv A).symm u) where
  symm := A.symm
  unit_mul := A.unit_mul
  jordan := A.jordan
  product_norm := by
    intro x y
    change spectralNorm S (S (equiv A x) (equiv A y)) ≤
      spectralNorm S (equiv A x) * spectralNorm S (equiv A y)
    exact norm_product A (equiv A x) (equiv A y)
  square_norm := by
    intro x
    change spectralNorm S (S (equiv A x) (equiv A x)) = spectralNorm S (equiv A x) ^ 2
    exact norm_square A (equiv A x)
  square_mono := by
    intro x y
    change spectralNorm S (S (equiv A x) (equiv A x)) ≤
      spectralNorm S (S (equiv A x) (equiv A x) + S (equiv A y) (equiv A y))
    exact norm_square_mono A (equiv A x) (equiv A y)

#print axioms jb_data

end D5.S3.Topology.EJASpectralNorm
