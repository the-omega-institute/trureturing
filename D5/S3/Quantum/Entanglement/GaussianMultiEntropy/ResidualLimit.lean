/- GID: D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Fourier replica products and the residual-determinant limit of Gaussian multi-entropy. -/

import D5.S3.Quantum.Entanglement.GaussianMultiEntropyAsymptotic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum

/-!
# Fourier replica products and the residual-determinant limit

For the fully symmetric pure Gaussian state with positive party sizes, the
twisted replica Gram matrices are diagonalized by the discrete Fourier basis of
the replica torus and of the replica cycle. Their eigenvalues are
`|A ω^p + B ω^q + C|² / N²`, and `1 - λ` equals four times an explicit sine
weight divided by `N²`. With `x = (a² - 1) / (N - 1)` the genuine multi-entropy
of the source integral definition equals the Fourier product formula
`(2 log P₃ - n Σ log Pᵢ) / (4 n (n - 1))`. The leading coefficients of these
products in `a²` are the residual Gram products rescaled by `N² / (4 (N - 1))`,
and they give the constant term of the large-squeezing expansion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology
open scoped BigOperators ComplexConjugate Matrix

namespace D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ResidualLimit

open GaussianReplicaReduction GaussianMultiEntropyAsymptotic

/-! ## Roots of unity and Fourier matrices -/

/-- The primitive root `exp(2πi/n)`. -/
def unitRoot (n : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))

theorem unitRoot_primitive (n : ℕ) (hn : 0 < n) : IsPrimitiveRoot (unitRoot n) n :=
  Complex.isPrimitiveRoot_exp n hn.ne'

theorem unitRoot_ne_zero (n : ℕ) : unitRoot n ≠ 0 := Complex.exp_ne_zero _

theorem unitRoot_pow_pow (n : ℕ) (hn : 0 < n) (p : ℕ) : (unitRoot n ^ p) ^ n = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, (unitRoot_primitive n hn).pow_eq_one, one_pow]

/-- Rotating a cycle coordinate multiplies a power of an `n`-th root of unity by its base. -/
theorem pow_rotate {n : ℕ} (z : ℂ) (hz : z ^ n = 1) (x : Fin n) :
    z ^ ((finRotate n x : Fin n) : ℕ) = z ^ (x : ℕ) * z := by
  cases n with
  | zero => exact x.elim0
  | succ m =>
    rw [finRotate_apply, Fin.val_add_one]
    split_ifs with h
    · subst h
      simp only [Fin.val_last, pow_zero]
      rw [← pow_succ, hz]
    · rw [pow_succ]

/-- Orthogonality of the characters of the cycle of length `n`. -/
theorem sum_ratio_pow (n : ℕ) (hn : 0 < n) (j j' : Fin n) :
    ∑ t : Fin n, (unitRoot n ^ (j' : ℕ) / unitRoot n ^ (j : ℕ)) ^ (t : ℕ) =
      if j = j' then (n : ℂ) else 0 := by
  have hω := unitRoot_primitive n hn
  split_ifs with h
  · subst h
    simp [div_self (pow_ne_zero _ (unitRoot_ne_zero n))]
  · set z := unitRoot n ^ (j' : ℕ) / unitRoot n ^ (j : ℕ) with hzdef
    have hz : z ≠ 1 := by
      intro hz
      rw [hzdef, div_eq_one_iff_eq (pow_ne_zero _ (unitRoot_ne_zero n))] at hz
      exact h (Fin.ext (hω.pow_inj j'.isLt j.isLt hz).symm)
    have hn1 : z ^ n = 1 := by
      rw [hzdef, div_pow, unitRoot_pow_pow n hn, unitRoot_pow_pow n hn, div_one]
    have hsum := Fin.sum_univ_eq_sum_range (fun t => z ^ t) n
    rw [hsum, geom_sum_eq hz, hn1, sub_self, zero_div]

/-- The character of the replica torus with frequencies `t`. -/
def torusCharacter (n : ℕ) (t x : Fin n × Fin n) : ℂ :=
  (unitRoot n ^ (t.1 : ℕ)) ^ (x.1 : ℕ) * (unitRoot n ^ (t.2 : ℕ)) ^ (x.2 : ℕ)

/-- The Fourier matrix of the replica torus; column `t` is a character. -/
def torusFourier (n : ℕ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun r t => torusCharacter n t r

/-- The dual Fourier matrix of the replica torus. -/
def torusDual (n : ℕ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun t r => (torusCharacter n t r)⁻¹

/-- The character of the replica cycle with frequency `t`. -/
def cycleCharacter (n : ℕ) (t x : Fin n) : ℂ := (unitRoot n ^ (t : ℕ)) ^ (x : ℕ)

/-- The Fourier matrix of the replica cycle. -/
def cycleFourier (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun r t => cycleCharacter n t r

/-- The dual Fourier matrix of the replica cycle. -/
def cycleDual (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun t r => (cycleCharacter n t r)⁻¹

theorem torusDual_mul_fourier (n : ℕ) (hn : 0 < n) :
    torusDual n * torusFourier n =
      ((n : ℂ) ^ 2) • (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) := by
  ext t t'
  have hterm : ∀ r : Fin n × Fin n, torusDual n t r * torusFourier n r t' =
      (unitRoot n ^ (t'.1 : ℕ) / unitRoot n ^ (t.1 : ℕ)) ^ (r.1 : ℕ) *
        (unitRoot n ^ (t'.2 : ℕ) / unitRoot n ^ (t.2 : ℕ)) ^ (r.2 : ℕ) := by
    intro r
    simp only [torusDual, torusFourier, torusCharacter]
    rw [div_pow, div_pow, mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [Matrix.mul_apply, Finset.sum_congr rfl (fun r _ => hterm r), Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [sum_ratio_pow n hn, sum_ratio_pow n hn]
  by_cases h1 : t.1 = t'.1 <;> by_cases h2 : t.2 = t'.2 <;>
    simp [h1, h2, Matrix.one_apply, Prod.ext_iff, sq]

theorem cycleDual_mul_fourier (n : ℕ) (hn : 0 < n) :
    cycleDual n * cycleFourier n = (n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext t t'
  have hterm : ∀ r : Fin n, cycleDual n t r * cycleFourier n r t' =
      (unitRoot n ^ (t' : ℕ) / unitRoot n ^ (t : ℕ)) ^ (r : ℕ) := by
    intro r
    simp only [cycleDual, cycleFourier, cycleCharacter]
    rw [div_pow, div_eq_mul_inv, mul_comm]
  rw [Matrix.mul_apply, Finset.sum_congr rfl (fun r _ => hterm r), sum_ratio_pow n hn]
  by_cases h : t = t' <;> simp [h]

/-- A matrix diagonalized by a Fourier matrix with a nonsingular dual has
determinant equal to the product of its eigenvalues. -/
theorem det_eq_prod_of_fourier {R : Type*} [Fintype R] [DecidableEq R]
    (M F G : Matrix R R ℂ) (c : ℂ) (hc : c ≠ 0) (hGF : G * F = c • (1 : Matrix R R ℂ))
    (κ : R → ℂ) (heig : ∀ t r, ∑ s, M r s * F s t = κ t * F r t) :
    M.det = ∏ t, κ t := by
  have hMF : M * F = F * Matrix.diagonal κ := by
    ext r t
    rw [Matrix.mul_apply, heig t r, Matrix.mul_diagonal, mul_comm]
  have hF : F.det ≠ 0 := by
    intro h
    have hd := congrArg Matrix.det hGF
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at hd
    exact pow_ne_zero _ hc hd.symm
  have h := congrArg Matrix.det hMF
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm] at h
  exact mul_left_cancel₀ hF h

/-! ## Twisted Gram matrices on characters -/

/-- A twist-average matrix acts on a common eigenvector of the twists by the
average of the inverse eigenvalues, and its transpose by the average of the
eigenvalues. -/
theorem twist_fourier {R K : Type*} [Fintype R] [DecidableEq R] [Fintype K]
    (g : K → Equiv.Perm R) (c : ℝ) (φ : R → ℂ) (χ : K → ℂ)
    (hχ : ∀ k x, φ (g k x) = χ k * φ x) (hχ0 : ∀ k, χ k ≠ 0) :
    (∀ u, ∑ s, (((Matrix.of fun r s => ∑ k, if r = g k s then c else 0 :
        Matrix R R ℝ) u s : ℝ) : ℂ) * φ s = (∑ k, (c : ℂ) * (χ k)⁻¹) * φ u) ∧
      (∀ r, ∑ u, (((Matrix.of fun r s => ∑ k, if r = g k s then c else 0 :
        Matrix R R ℝ) u r : ℝ) : ℂ) * φ u = (∑ k, (c : ℂ) * χ k) * φ r) := by
  have hcast : ∀ r s, (((Matrix.of fun r s => ∑ k, if r = g k s then c else 0 :
      Matrix R R ℝ) r s : ℝ) : ℂ) = ∑ k, if r = g k s then (c : ℂ) else 0 := by
    intro r s
    simp only [Matrix.of_apply, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun k _ => by split_ifs <;> simp)
  constructor
  · intro u
    have hinner : ∀ k, ∑ s, (if u = g k s then (c : ℂ) else 0) * φ s =
        (c : ℂ) * (χ k)⁻¹ * φ u := by
      intro k
      have hs : ∀ s, (if u = g k s then (c : ℂ) else 0) * φ s =
          if (g k).symm u = s then (c : ℂ) * φ s else 0 := by
        intro s
        by_cases h : u = g k s
        · have h' : (g k).symm u = s := by rw [Equiv.symm_apply_eq]; exact h
          simp [h]
        · have h' : ¬ (g k).symm u = s := by rw [Equiv.symm_apply_eq]; exact h
          simp [h, h']
      rw [Finset.sum_congr rfl (fun s _ => hs s), Finset.sum_ite_eq]
      simp only [Finset.mem_univ, ite_true]
      have hk := hχ k ((g k).symm u)
      rw [Equiv.apply_symm_apply] at hk
      rw [hk]
      field_simp [hχ0 k]
    simp_rw [hcast, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => hinner k)
  · intro r
    have hinner : ∀ k, ∑ u, (if u = g k r then (c : ℂ) else 0) * φ u =
        (c : ℂ) * χ k * φ r := by
      intro k
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [hχ k r, mul_assoc]
    simp_rw [hcast, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => hinner k)

/-- The normalized replica precision matrix acts on a common eigenvector of a
Gram pair by the scalar `α - β μ' μ`. -/
theorem gram_fourier {R : Type*} [Fintype R] [DecidableEq R] (Q : Matrix R R ℝ)
    (α β : ℝ) (φ : R → ℂ) (μ μ' : ℂ)
    (h1 : ∀ u, ∑ s, (Q u s : ℂ) * φ s = μ * φ u)
    (h2 : ∀ r, ∑ u, (Q u r : ℂ) * φ u = μ' * φ r) (r : R) :
    ∑ s, (((α • (1 : Matrix R R ℝ) - β • (Qᵀ * Q)) r s : ℝ) : ℂ) * φ s =
      ((α : ℂ) - β * (μ' * μ)) * φ r := by
  have hI : ∑ s, (((α • (1 : Matrix R R ℝ)) r s : ℝ) : ℂ) * φ s = α * φ r := by
    rw [Finset.sum_eq_single r]
    · simp
    · intro s _ hs
      simp [Ne.symm hs]
    · simp
  have hG : ∑ s, (((β • (Qᵀ * Q)) r s : ℝ) : ℂ) * φ s = β * (μ' * μ) * φ r := by
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul,
      Complex.ofReal_mul, Complex.ofReal_sum]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hu : ∀ u, ∑ s, (β : ℂ) * ((Q u r : ℂ) * (Q u s : ℂ)) * φ s =
        (β : ℂ) * (Q u r : ℂ) * (μ * φ u) := by
      intro u
      rw [← h1 u, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    rw [Finset.sum_congr rfl (fun u _ => hu u)]
    calc ∑ u, (β : ℂ) * (Q u r : ℂ) * (μ * φ u)
        = (β : ℂ) * μ * ∑ u, (Q u r : ℂ) * φ u := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun u _ => by ring)
      _ = β * (μ' * μ) * φ r := by rw [h2 r]; ring
  simp only [Matrix.sub_apply, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib, hI, hG]

/-! ## Fourier eigenvalues and sine weights -/

theorem norm_unitRoot_pow (n : ℕ) (hn : 0 < n) (p : ℕ) : ‖unitRoot n ^ p‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (unitRoot_pow_pow n hn p) hn.ne'

theorem inv_unitRoot_pow (n : ℕ) (hn : 0 < n) (p : ℕ) :
    (unitRoot n ^ p)⁻¹ = conj (unitRoot n ^ p) := by
  apply inv_eq_of_mul_eq_one_right
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_unitRoot_pow n hn p]
  simp

theorem unitRoot_pow_eq (n p : ℕ) :
    unitRoot n ^ p = (Real.cos (2 * (Real.pi * p / n)) : ℂ) +
      (Real.sin (2 * (Real.pi * p / n)) : ℂ) * Complex.I := by
  rw [unitRoot, ← Complex.exp_nat_mul]
  have h : (p : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) =
      ((2 * (Real.pi * p / n) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- The squared modulus of a three-term trigonometric sum. -/
theorem normSq_three_term (A B C θ₁ θ₂ : ℝ) :
    Complex.normSq ((A : ℂ) * ((Real.cos (2 * θ₁) : ℂ) + (Real.sin (2 * θ₁) : ℂ) * Complex.I) +
        (B : ℂ) * ((Real.cos (2 * θ₂) : ℂ) + (Real.sin (2 * θ₂) : ℂ) * Complex.I) + (C : ℂ)) =
      (A + B + C) ^ 2 - 4 * (A * B * Real.sin (θ₁ - θ₂) ^ 2 + A * C * Real.sin θ₁ ^ 2 +
        B * C * Real.sin θ₂ ^ 2) := by
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [Real.cos_two_mul θ₁, Real.cos_two_mul θ₂, Real.sin_two_mul θ₁, Real.sin_two_mul θ₂,
    Real.sin_sub]
  have h1 := Real.sin_sq_add_cos_sq θ₁
  have h2 := Real.sin_sq_add_cos_sq θ₂
  linear_combination
    (4 * A * ((A + B + C) - 2 * A * Real.sin θ₁ ^ 2 - 2 * B * Real.sin θ₂ ^ 2) +
      4 * A ^ 2 * Real.sin θ₁ ^ 2 + 4 * A * B * Real.sin θ₂ ^ 2 +
      4 * A ^ 2 * (Real.sin θ₁ ^ 2 + Real.cos θ₁ ^ 2 - 1) +
      8 * A * B * (Real.sin θ₂ ^ 2 + Real.cos θ₂ ^ 2 - 1)) * h1 +
    (4 * B * ((A + B + C) - 2 * A * Real.sin θ₁ ^ 2 - 2 * B * Real.sin θ₂ ^ 2) +
      4 * B ^ 2 * Real.sin θ₂ ^ 2 + 4 * A * B * Real.sin θ₁ ^ 2 +
      4 * B ^ 2 * (Real.sin θ₂ ^ 2 + Real.cos θ₂ ^ 2 - 1)) * h2

/-- The Fourier eigenvalue `|A ω^p + B ω^q + C|² / N²` of the tripartite replica Gram matrix;
party `A` carries frequency `p` and party `B` carries frequency `q`. -/
def tripartiteEigenvalue (n : ℕ) (A B C : ℝ) (p q : ℕ) : ℝ :=
  Complex.normSq ((A : ℂ) * unitRoot n ^ p + (B : ℂ) * unitRoot n ^ q + (C : ℂ)) /
    (A + B + C) ^ 2

/-- The Fourier eigenvalue `|U ω^k + V|² / (U + V)²` of a bipartite replica Gram matrix. -/
def cycleEigenvalue (n : ℕ) (U V : ℝ) (k : ℕ) : ℝ :=
  Complex.normSq ((U : ℂ) * unitRoot n ^ k + (V : ℂ)) / (U + V) ^ 2

/-- The sine weight of the tripartite Fourier mode. -/
def tripartiteWeight (n : ℕ) (A B C : ℝ) (p q : ℕ) : ℝ :=
  A * B * Real.sin (Real.pi * ((p : ℝ) - q) / n) ^ 2 + A * C * Real.sin (Real.pi * p / n) ^ 2 +
    B * C * Real.sin (Real.pi * q / n) ^ 2

/-- The sine weight of a cut Fourier mode with cut coefficient `u`. -/
def cutWeight (n : ℕ) (u : ℝ) (k : ℕ) : ℝ := u * Real.sin (Real.pi * k / n) ^ 2

theorem one_sub_tripartiteEigenvalue (n : ℕ) (A B C : ℝ) (hN : A + B + C ≠ 0) (p q : ℕ) :
    1 - tripartiteEigenvalue n A B C p q = 4 * tripartiteWeight n A B C p q / (A + B + C) ^ 2 := by
  rw [tripartiteEigenvalue, unitRoot_pow_eq, unitRoot_pow_eq, normSq_three_term, tripartiteWeight,
    show Real.pi * ((p : ℝ) - q) / n = Real.pi * p / n - Real.pi * q / n by ring]
  field_simp
  ring

theorem one_sub_cycleEigenvalue (n : ℕ) (U V : ℝ) (hN : U + V ≠ 0) (k : ℕ) :
    1 - cycleEigenvalue n U V k = 4 * cutWeight n (U * V) k / (U + V) ^ 2 := by
  have h := normSq_three_term U 0 V (Real.pi * k / n) (Real.pi * k / n)
  simp only [Complex.ofReal_zero, zero_mul, add_zero, zero_add, mul_zero] at h
  rw [cycleEigenvalue, unitRoot_pow_eq, h, cutWeight]
  field_simp
  ring

/-! ## Replica Gram determinants -/

theorem tripartite_gram_det (n NA NB NC : ℕ) (hn : 0 < n) (hN : 0 < NA + NB + NC) (α β : ℝ) :
    (α • (1 : Matrix (Replica3 n) (Replica3 n) ℝ) -
      β • ((Matrix.of fun r s => ∑ p : Mode [NA, NB, NC],
          if r = twists3 n p.1 s then ((NA + NB + NC : ℕ) : ℝ)⁻¹ else 0 :
          Matrix (Replica3 n) (Replica3 n) ℝ)ᵀ *
        (Matrix.of fun r s => ∑ p : Mode [NA, NB, NC],
          if r = twists3 n p.1 s then ((NA + NB + NC : ℕ) : ℝ)⁻¹ else 0))).det =
      ∏ t : Fin n × Fin n, (α - β * tripartiteEigenvalue n NA NB NC t.1 t.2) := by
  set Q : Matrix (Replica3 n) (Replica3 n) ℝ := Matrix.of fun r s => ∑ p : Mode [NA, NB, NC],
    if r = twists3 n p.1 s then ((NA + NB + NC : ℕ) : ℝ)⁻¹ else 0 with hQ
  set M := α • (1 : Matrix (Replica3 n) (Replica3 n) ℝ) - β • (Qᵀ * Q) with hM
  apply Complex.ofReal_injective
  rw [Complex.ofReal_prod]
  have hmap := Complex.ofRealHom.map_det M
  rw [Complex.ofRealHom_eq_coe] at hmap
  rw [hmap]
  refine det_eq_prod_of_fourier _ (torusFourier n) (torusDual n) ((n : ℂ) ^ 2)
    (pow_ne_zero _ (Nat.cast_ne_zero.mpr hn.ne')) (torusDual_mul_fourier n hn) _ ?_
  intro t r
  let χ : Mode [NA, NB, NC] → ℂ := fun p =>
    if p.1 = 0 then unitRoot n ^ (t.1 : ℕ) else if p.1 = 1 then unitRoot n ^ (t.2 : ℕ) else 1
  have hχ : ∀ p x, torusCharacter n t (twists3 n p.1 x) = χ p * torusCharacter n t x := by
    intro p x
    simp only [twists3, χ]
    split_ifs
    · simp only [g_A, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, torusCharacter]
      rw [pow_rotate _ (unitRoot_pow_pow n hn _)]
      ring
    · simp only [g_B, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, torusCharacter]
      rw [pow_rotate _ (unitRoot_pow_pow n hn _)]
      ring
    · simp [g_C]
  have hχ0 : ∀ p, χ p ≠ 0 := by
    intro p
    simp only [χ]
    split_ifs <;> simp [unitRoot_ne_zero]
  obtain ⟨h1, h2⟩ := twist_fourier (fun p : Mode [NA, NB, NC] => twists3 n p.1)
    (((NA + NB + NC : ℕ) : ℝ)⁻¹) (torusCharacter n t) χ hχ hχ0
  have hg := gram_fourier Q α β (torusCharacter n t) _ _ h1 h2 r
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Complex.ofRealHom_eq_coe]
  change ∑ s, ((M r s : ℝ) : ℂ) * torusCharacter n t s = _ * torusCharacter n t r
  rw [hM, hg]
  congr 1
  have hN0 : ((NA + NB + NC : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hsum1 : ∑ k : Mode [NA, NB, NC], (((NA + NB + NC : ℕ) : ℝ)⁻¹ : ℂ) * χ k =
      ((NA + NB + NC : ℕ) : ℂ)⁻¹ *
        ((NA : ℂ) * unitRoot n ^ (t.1 : ℕ) + (NB : ℂ) * unitRoot n ^ (t.2 : ℕ) + (NC : ℂ)) := by
    simp [χ, Mode, Fintype.sum_sigma, Fin.sum_univ_succ]
    split_ifs with h
    · first
        | exact absurd h (by exact (by decide : ¬ ((2 : Fin 3) = 1)))
        | (simp [Fin.ext_iff] at h; done)
        | (have h' := congrArg Fin.val h; simp at h'; done)
        | (have h' := congrArg Fin.val h; norm_num at h'; done)
    · first | (simp; done) | (simp; ring) | ring
  have hsum2 : ∑ k : Mode [NA, NB, NC], (((NA + NB + NC : ℕ) : ℝ)⁻¹ : ℂ) * (χ k)⁻¹ =
      ((NA + NB + NC : ℕ) : ℂ)⁻¹ * ((NA : ℂ) * conj (unitRoot n ^ (t.1 : ℕ)) +
        (NB : ℂ) * conj (unitRoot n ^ (t.2 : ℕ)) + (NC : ℂ)) := by
    simp [χ, Mode, Fintype.sum_sigma, Fin.sum_univ_succ, inv_unitRoot_pow n hn]
    split_ifs with h
    · first
        | exact absurd h (by exact (by decide : ¬ ((2 : Fin 3) = 1)))
        | (simp [Fin.ext_iff] at h; done)
        | (have h' := congrArg Fin.val h; simp at h'; done)
        | (have h' := congrArg Fin.val h; norm_num at h'; done)
    · first | (simp; done) | (simp; ring) | ring
  rw [Complex.ofReal_inv, hsum1, hsum2]
  have hconj : (NA : ℂ) * conj (unitRoot n ^ (t.1 : ℕ)) + (NB : ℂ) * conj (unitRoot n ^ (t.2 : ℕ)) +
      (NC : ℂ) = conj ((NA : ℂ) * unitRoot n ^ (t.1 : ℕ) + (NB : ℂ) * unitRoot n ^ (t.2 : ℕ) +
        (NC : ℂ)) := by
    simp [map_add, map_mul]
  rw [hconj]
  have hm := Complex.mul_conj ((NA : ℂ) * unitRoot n ^ (t.1 : ℕ) +
    (NB : ℂ) * unitRoot n ^ (t.2 : ℕ) + (NC : ℂ))
  have hev : (tripartiteEigenvalue n NA NB NC t.1 t.2 : ℂ) =
      ((NA + NB + NC : ℕ) : ℂ)⁻¹ * ((NA : ℂ) * unitRoot n ^ (t.1 : ℕ) +
        (NB : ℂ) * unitRoot n ^ (t.2 : ℕ) + (NC : ℂ)) * (((NA + NB + NC : ℕ) : ℂ)⁻¹ *
        conj ((NA : ℂ) * unitRoot n ^ (t.1 : ℕ) + (NB : ℂ) * unitRoot n ^ (t.2 : ℕ) +
          (NC : ℂ))) := by
    rw [tripartiteEigenvalue]
    push_cast
    rw [← hm]
    have hN0' : (NA : ℂ) + NB + NC ≠ 0 := by exact_mod_cast hN0
    push_cast
    field_simp <;> ring
  rw [Complex.ofReal_sub, Complex.ofReal_mul, hev]

theorem cycle_gram_det (n U V : ℕ) (hn : 0 < n) (hUV : 0 < U + V) (α β : ℝ) :
    (α • (1 : Matrix (Fin n) (Fin n) ℝ) -
      β • ((Matrix.of fun r s => ∑ p : Mode [U, V],
          if r = twists2 n p.1 s then ((U + V : ℕ) : ℝ)⁻¹ else 0 :
          Matrix (Fin n) (Fin n) ℝ)ᵀ *
        (Matrix.of fun r s => ∑ p : Mode [U, V],
          if r = twists2 n p.1 s then ((U + V : ℕ) : ℝ)⁻¹ else 0))).det =
      ∏ k : Fin n, (α - β * cycleEigenvalue n U V k) := by
  set Q : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun r s => ∑ p : Mode [U, V],
    if r = twists2 n p.1 s then ((U + V : ℕ) : ℝ)⁻¹ else 0 with hQ
  set M := α • (1 : Matrix (Fin n) (Fin n) ℝ) - β • (Qᵀ * Q) with hM
  apply Complex.ofReal_injective
  rw [Complex.ofReal_prod]
  have hmap := Complex.ofRealHom.map_det M
  rw [Complex.ofRealHom_eq_coe] at hmap
  rw [hmap]
  refine det_eq_prod_of_fourier _ (cycleFourier n) (cycleDual n) (n : ℂ)
    (Nat.cast_ne_zero.mpr hn.ne') (cycleDual_mul_fourier n hn) _ ?_
  intro t r
  let χ : Mode [U, V] → ℂ := fun p => if p.1 = 0 then unitRoot n ^ (t : ℕ) else 1
  have hχ : ∀ p x, cycleCharacter n t (twists2 n p.1 x) = χ p * cycleCharacter n t x := by
    intro p x
    simp only [twists2, χ]
    split_ifs
    · simp only [cycleCharacter]
      rw [pow_rotate _ (unitRoot_pow_pow n hn _)]
      ring
    · simp
  have hχ0 : ∀ p, χ p ≠ 0 := by
    intro p
    simp only [χ]
    split_ifs <;> simp [unitRoot_ne_zero]
  obtain ⟨h1, h2⟩ := twist_fourier (fun p : Mode [U, V] => twists2 n p.1)
    (((U + V : ℕ) : ℝ)⁻¹) (cycleCharacter n t) χ hχ hχ0
  have hg := gram_fourier Q α β (cycleCharacter n t) _ _ h1 h2 r
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Complex.ofRealHom_eq_coe]
  change ∑ s, ((M r s : ℝ) : ℂ) * cycleCharacter n t s = _ * cycleCharacter n t r
  rw [hM, hg]
  congr 1
  have hN0 : ((U + V : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hUV.ne'
  have hsum1 : ∑ k : Mode [U, V], (((U + V : ℕ) : ℝ)⁻¹ : ℂ) * χ k =
      ((U + V : ℕ) : ℂ)⁻¹ * ((U : ℂ) * unitRoot n ^ (t : ℕ) + (V : ℂ)) := by
    simp [χ, Mode, Fintype.sum_sigma, Fin.sum_univ_succ]
    ring
  have hsum2 : ∑ k : Mode [U, V], (((U + V : ℕ) : ℝ)⁻¹ : ℂ) * (χ k)⁻¹ =
      ((U + V : ℕ) : ℂ)⁻¹ * ((U : ℂ) * conj (unitRoot n ^ (t : ℕ)) + (V : ℂ)) := by
    simp [χ, Mode, Fintype.sum_sigma, Fin.sum_univ_succ, inv_unitRoot_pow n hn]
    ring
  rw [Complex.ofReal_inv, hsum1, hsum2]
  have hconj : (U : ℂ) * conj (unitRoot n ^ (t : ℕ)) + (V : ℂ) =
      conj ((U : ℂ) * unitRoot n ^ (t : ℕ) + (V : ℂ)) := by
    simp [map_add, map_mul]
  rw [hconj]
  have hm := Complex.mul_conj ((U : ℂ) * unitRoot n ^ (t : ℕ) + (V : ℂ))
  have hev : (cycleEigenvalue n U V t : ℂ) =
      ((U + V : ℕ) : ℂ)⁻¹ * ((U : ℂ) * unitRoot n ^ (t : ℕ) + (V : ℂ)) *
        (((U + V : ℕ) : ℂ)⁻¹ * conj ((U : ℂ) * unitRoot n ^ (t : ℕ) + (V : ℂ))) := by
    rw [cycleEigenvalue]
    push_cast
    rw [← hm]
    have hN0' : (U : ℂ) + V ≠ 0 := by exact_mod_cast hN0
    field_simp
  rw [Complex.ofReal_sub, Complex.ofReal_mul, hev]

/-! ## The squeezing parameter -/

/-- The normalized squeezing parameter `x = (a² - 1) / (N - 1)`. -/
def squeezing (N a : ℝ) : ℝ := (a ^ 2 - 1) / (N - 1)

/-- The symmetric-state eigenvalue ratio `ε` satisfies `(1 - ε)² = ε N² x`. -/
theorem epsilon_identity (a : ℝ) (N : ℕ) (ha : 1 ≤ a) (hN : 3 ≤ N) :
    (1 - (a + ((N : ℝ) - 1) * eMinus a N) / (a - eMinus a N)) ^ 2 =
      (a + ((N : ℝ) - 1) * eMinus a N) / (a - eMinus a N) *
        ((N : ℝ) ^ 2 * squeezing N a) := by
  obtain ⟨hα, -, -⟩ := symmetric_parameters a N ha hN
  have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have ha0 : 0 < a := by linarith
  have hN1 : (N : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have hden : 2 * a * ((N : ℝ) - 1) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero ha0.ne') hN1
  set e := eMinus a N with he
  set s := Real.sqrt (a ^ 2 - 1) * Real.sqrt ((a ^ 2 - 1) * (N : ℝ) ^ 2 + 4 * ((N : ℝ) - 1))
    with hs
  have ht : 0 ≤ a ^ 2 - 1 := by nlinarith
  have hr : 0 ≤ (a ^ 2 - 1) * (N : ℝ) ^ 2 + 4 * ((N : ℝ) - 1) :=
    add_nonneg (mul_nonneg ht (sq_nonneg _)) (by linarith)
  have hs2 : s ^ 2 = (a ^ 2 - 1) * ((a ^ 2 - 1) * (N : ℝ) ^ 2 + 4 * ((N : ℝ) - 1)) := by
    rw [hs, mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hr]
  have hee : e * (2 * a * ((N : ℝ) - 1)) = (a ^ 2 - 1) * ((N : ℝ) - 2) - s := by
    rw [he, hs, eMinus, div_mul_cancel₀ _ hden]
  have hQ : ((N : ℝ) - 1) * a * e ^ 2 - (a ^ 2 - 1) * ((N : ℝ) - 2) * e - (a ^ 2 - 1) * a = 0 := by
    have h4 : 4 * a * ((N : ℝ) - 1) *
        (((N : ℝ) - 1) * a * e ^ 2 - (a ^ 2 - 1) * ((N : ℝ) - 2) * e - (a ^ 2 - 1) * a) = 0 := by
      linear_combination (2 * a * ((N : ℝ) - 1) * e + ((a ^ 2 - 1) * ((N : ℝ) - 2) - s) -
        2 * (a ^ 2 - 1) * ((N : ℝ) - 2)) * hee + hs2
    have h4' : 4 * a * ((N : ℝ) - 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) ha0.ne') hN1
    exact (mul_eq_zero.mp h4).resolve_left h4'
  have hd : a - e ≠ 0 := hα.ne'
  have key : (1 - (a + ((N : ℝ) - 1) * e) / (a - e)) ^ 2 -
      (a + ((N : ℝ) - 1) * e) / (a - e) * ((N : ℝ) ^ 2 * ((a ^ 2 - 1) / ((N : ℝ) - 1))) =
      (N : ℝ) ^ 2 * a * (((N : ℝ) - 1) * a * e ^ 2 - (a ^ 2 - 1) * ((N : ℝ) - 2) * e -
        (a ^ 2 - 1) * a) / ((a - e) ^ 2 * ((N : ℝ) - 1)) := by
    field_simp
    ring
  rw [hQ, mul_zero, zero_div, sub_eq_zero] at key
  rw [squeezing]
  exact key

/-! ## Fourier replica products -/

/-- The tripartite replica product `P₃ = ∏_{p,q} (1 + x w_{pq})`. -/
def tripartiteProduct (n : ℕ) (A B C x : ℝ) : ℝ :=
  ∏ t : Fin n × Fin n, (1 + x * tripartiteWeight n A B C t.1 t.2)

/-- The cut replica product `Pᵢ = ∏_k (1 + x uᵢ sin²(πk/n))`. -/
def cutProduct (n : ℕ) (u x : ℝ) : ℝ := ∏ k : Fin n, (1 + x * cutWeight n u k)

/-- The Fourier product formula `(2 log P₃ - n Σᵢ log Pᵢ) / (4 n (n - 1))`, with
`x = (a² - 1) / (N - 1)` and cut coefficients `uᵢ = Nᵢ (N - Nᵢ)`. -/
def fourierGM (n : ℕ) (A B C a : ℝ) : ℝ :=
  (2 * Real.log (tripartiteProduct n A B C (squeezing (A + B + C) a)) -
    (n : ℝ) * (Real.log (cutProduct n (A * (B + C)) (squeezing (A + B + C) a)) +
      Real.log (cutProduct n (B * (A + C)) (squeezing (A + B + C) a)) +
      Real.log (cutProduct n (C * (A + B)) (squeezing (A + B + C) a)))) /
    (4 * (n : ℝ) * ((n : ℝ) - 1))

theorem replica_factor (ε x N w : ℝ) (hN : N ≠ 0) (hκ : (1 - ε) ^ 2 = ε * (N ^ 2 * x)) :
    ((1 + ε) / 2) ^ 2 - ((1 - ε) / 2) ^ 2 * (1 - 4 * w / N ^ 2) = ε * (1 + x * w) := by
  have h : ((1 + ε) / 2) ^ 2 - ((1 - ε) / 2) ^ 2 * (1 - 4 * w / N ^ 2) =
      ε + (1 - ε) ^ 2 * w / N ^ 2 := by
    field_simp
    ring
  rw [h, hκ]
  field_simp

theorem tripartiteWeight_nonneg (n : ℕ) (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (p q : ℕ) : 0 ≤ tripartiteWeight n A B C p q := by
  unfold tripartiteWeight
  positivity

theorem cutWeight_nonneg (n : ℕ) (u : ℝ) (hu : 0 ≤ u) (k : ℕ) : 0 ≤ cutWeight n u k := by
  unfold cutWeight
  positivity

theorem tripartiteProduct_pos (n : ℕ) (A B C x : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hx : 0 ≤ x) : 0 < tripartiteProduct n A B C x :=
  Finset.prod_pos fun _ _ => add_pos_of_pos_of_nonneg one_pos
    (mul_nonneg hx (tripartiteWeight_nonneg n A B C hA hB hC _ _))

theorem cutProduct_pos (n : ℕ) (u x : ℝ) (hu : 0 ≤ u) (hx : 0 ≤ x) : 0 < cutProduct n u x :=
  Finset.prod_pos fun _ _ => add_pos_of_pos_of_nonneg one_pos
    (mul_nonneg hx (cutWeight_nonneg n u hu _))

theorem tripartite_det_product (n NA NB NC : ℕ) (hn : 0 < n) (hN : 0 < NA + NB + NC)
    (ε x : ℝ) (hε : 0 < ε) (hκ : (1 - ε) ^ 2 = ε * (((NA + NB + NC : ℕ) : ℝ) ^ 2 * x)) :
    (H [NA, NB, NC] (twists3 n) ε).det = ε ^ (n ^ 2) * tripartiteProduct n NA NB NC x := by
  have hr := replica_determinant_reduction [NA, NB, NC] (by simp; omega) (twists3 n) ε hε
  dsimp only at hr
  have hs3 : [NA, NB, NC].sum = NA + NB + NC := by simp [add_assoc]
  rw [hs3] at hr
  rw [hr, tripartite_gram_det n NA NB NC hn hN]
  have hN0' : ((NA + NB + NC : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hN0 : (NA : ℝ) + NB + NC ≠ 0 := by push_cast at hN0'; exact hN0'
  have hκ' : (1 - ε) ^ 2 = ε * (((NA : ℝ) + NB + NC) ^ 2 * x) := by push_cast at hκ; exact hκ
  have hfac : ∀ t : Fin n × Fin n, ((1 + ε) / 2) ^ 2 - ((1 - ε) / 2) ^ 2 *
      tripartiteEigenvalue n NA NB NC t.1 t.2 =
        ε * (1 + x * tripartiteWeight n NA NB NC t.1 t.2) := by
    intro t
    have h1 := one_sub_tripartiteEigenvalue n NA NB NC hN0 t.1 t.2
    rw [show tripartiteEigenvalue n NA NB NC t.1 t.2 =
      1 - 4 * tripartiteWeight n NA NB NC t.1 t.2 / ((NA : ℝ) + NB + NC) ^ 2 by linarith]
    exact replica_factor ε x _ _ hN0 hκ'
  rw [Finset.prod_congr rfl (fun t _ => hfac t), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, tripartiteProduct, sq n]

theorem cut_det_product (n U V : ℕ) (hn : 0 < n) (hUV : 0 < U + V)
    (ε x : ℝ) (hε : 0 < ε) (hκ : (1 - ε) ^ 2 = ε * (((U + V : ℕ) : ℝ) ^ 2 * x)) :
    (H [U, V] (twists2 n) ε).det = ε ^ n * cutProduct n ((U : ℝ) * V) x := by
  have hr := replica_determinant_reduction [U, V] (by simp; omega) (twists2 n) ε hε
  dsimp only at hr
  have hs2 : [U, V].sum = U + V := by simp
  rw [hs2] at hr
  rw [hr, cycle_gram_det n U V hn hUV]
  have hN0' : ((U + V : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hUV.ne'
  have hN0 : (U : ℝ) + V ≠ 0 := by push_cast at hN0'; exact hN0'
  have hκ' : (1 - ε) ^ 2 = ε * (((U : ℝ) + V) ^ 2 * x) := by push_cast at hκ; exact hκ
  have hfac : ∀ k : Fin n, ((1 + ε) / 2) ^ 2 - ((1 - ε) / 2) ^ 2 * cycleEigenvalue n U V k =
      ε * (1 + x * cutWeight n ((U : ℝ) * V) k) := by
    intro k
    have h1 := one_sub_cycleEigenvalue n U V hN0 k
    rw [show cycleEigenvalue n U V k =
      1 - 4 * cutWeight n ((U : ℝ) * V) k / ((U : ℝ) + V) ^ 2 by linarith]
    exact replica_factor ε x _ _ hN0 hκ'
  rw [Finset.prod_congr rfl (fun k _ => hfac k), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, cutProduct]

/-- The genuine multi-entropy of the replica integral definition equals the Fourier
product formula, for every replica order `n ≥ 2`, positive party sizes and `a ≥ 1`. -/
theorem GM3_eq_fourierGM (n NA NB NC : ℕ) (hn : 2 ≤ n) (a : ℝ) (ha : 1 ≤ a)
    (hNA : 0 < NA) (hNB : 0 < NB) (hNC : 0 < NC) :
    GM3 n NA NB NC a = fourierGM n NA NB NC a := by
  rw [multi_entropy_determinant_formula n NA NB NC a ha hNA hNB hNC]
  have hN3 : 3 ≤ NA + NB + NC := by omega
  obtain ⟨-, hε, -⟩ := symmetric_parameters a (NA + NB + NC) ha hN3
  have hκ := epsilon_identity a (NA + NB + NC) ha hN3
  dsimp only [determinantGM3]
  set ε := (a + (((NA + NB + NC : ℕ) : ℝ) - 1) * eMinus a (NA + NB + NC)) /
    (a - eMinus a (NA + NB + NC)) with hεdef
  set x := squeezing ((NA + NB + NC : ℕ) : ℝ) a with hx
  have hn3 : (3 : ℝ) ≤ ((NA + NB + NC : ℕ) : ℝ) := by exact_mod_cast hN3
  have hx0 : 0 ≤ x := by rw [hx, squeezing]; exact div_nonneg (by nlinarith) (by linarith)
  have h3 := tripartite_det_product n NA NB NC (by omega) (by omega) ε x hε hκ
  have hAB := cut_det_product n (NA + NB) NC (by omega) (by omega) ε x hε hκ
  have hBC := cut_det_product n (NB + NC) NA (by omega) (by omega) ε x hε
    (by rw [show NB + NC + NA = NA + NB + NC by omega]; exact hκ)
  have hCA := cut_det_product n (NC + NA) NB (by omega) (by omega) ε x hε
    (by rw [show NC + NA + NB = NA + NB + NC by omega]; exact hκ)
  rw [h3, hAB, hBC, hCA]
  have hlog : ∀ (d : ℕ) (P : ℝ), 0 < P →
      Real.log (Real.sqrt (ε ^ d / (ε ^ d * P))) = -Real.log P / 2 := by
    intro d P hP
    rw [show ε ^ d / (ε ^ d * P) = P⁻¹ by field_simp, Real.log_sqrt (inv_nonneg.mpr hP.le),
      Real.log_inv]
  have hP3 := tripartiteProduct_pos n (NA : ℝ) NB NC x (by positivity) (by positivity)
    (by positivity) hx0
  have hPAB := cutProduct_pos n (((NA + NB : ℕ) : ℝ) * (NC : ℝ)) x (by positivity) hx0
  have hPBC := cutProduct_pos n (((NB + NC : ℕ) : ℝ) * (NA : ℝ)) x (by positivity) hx0
  have hPCA := cutProduct_pos n (((NC + NA : ℕ) : ℝ) * (NB : ℝ)) x (by positivity) hx0
  rw [hlog _ _ hP3, hlog _ _ hPAB, hlog _ _ hPBC, hlog _ _ hPCA]
  have hsq : squeezing ((NA : ℝ) + NB + NC) a = x := by rw [hx]; push_cast; ring
  have e1 : ((NA + NB : ℕ) : ℝ) * (NC : ℝ) = (NC : ℝ) * ((NA : ℝ) + NB) := by push_cast; ring
  have e2 : ((NB + NC : ℕ) : ℝ) * (NA : ℝ) = (NA : ℝ) * ((NB : ℝ) + NC) := by push_cast; ring
  have e3 : ((NC + NA : ℕ) : ℝ) * (NB : ℝ) = (NB : ℝ) * ((NA : ℝ) + NC) := by push_cast; ring
  rw [fourierGM, hsq, e1, e2, e3]
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hn1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have hn1' : 1 - (n : ℝ) ≠ 0 := ne_of_lt (by linarith)
  field_simp
  ring

/-! ## Leading coefficients and the residual-determinant limit -/

/-- The nonconstant Fourier modes of the replica torus. -/
def tripartiteModes (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun t => (t.1 : ℕ) ≠ 0 ∨ (t.2 : ℕ) ≠ 0

/-- The nonconstant Fourier modes of the replica cycle. -/
def cycleModes (n : ℕ) : Finset (Fin n) := Finset.univ.filter fun k => (k : ℕ) ≠ 0

/-- The residual tripartite Gram product `D₃ = ∏_{(p,q) ≠ (0,0)} (1 - λ_{pq})`. -/
def tripartiteResidual (n : ℕ) (A B C : ℝ) : ℝ :=
  ∏ t ∈ tripartiteModes n, (1 - tripartiteEigenvalue n A B C t.1 t.2)

/-- The residual Gram product `∏_{k ≠ 0} (1 - λ_k)` of the cut with cycled size `U`
and untwisted size `V`. -/
def cutResidual (n : ℕ) (U V : ℝ) : ℝ :=
  ∏ k ∈ cycleModes n, (1 - cycleEigenvalue n U V k)

/-- The leading coefficient `H₃ = D₃ [N² / (4 (N - 1))]^(n² - 1)` of `P₃` in `a²`. -/
def tripartiteLeading (n : ℕ) (A B C : ℝ) : ℝ :=
  tripartiteResidual n A B C * ((A + B + C) ^ 2 / (4 * (A + B + C - 1))) ^ (n ^ 2 - 1)

/-- The leading coefficient `Hᵢ = Dᵢ [N² / (4 (N - 1))]^(n - 1)` of a cut product in `a²`. -/
def cutLeading (n : ℕ) (U V : ℝ) : ℝ :=
  cutResidual n U V * ((U + V) ^ 2 / (4 * (U + V - 1))) ^ (n - 1)

/-- The constant `Kₙ = (2 log H₃ - n Σᵢ log Hᵢ) / (4 n (n - 1))`. -/
def residualConstant (n : ℕ) (A B C : ℝ) : ℝ :=
  (2 * Real.log (tripartiteLeading n A B C) -
    (n : ℝ) * (Real.log (cutLeading n (B + C) A) + Real.log (cutLeading n (A + C) B) +
      Real.log (cutLeading n (A + B) C))) / (4 * (n : ℝ) * ((n : ℝ) - 1))

theorem card_cycleModes (n : ℕ) (hn : 0 < n) : (cycleModes n).card = n - 1 := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun k : Fin n => (k : ℕ) ≠ 0)
  have h1 : (Finset.univ.filter fun k : Fin n => ¬ (k : ℕ) ≠ 0).card = 1 := by
    rw [Finset.card_eq_one]
    exact ⟨⟨0, hn⟩, by ext k; simp [Fin.ext_iff]⟩
  rw [h1, Finset.card_univ, Fintype.card_fin] at h
  unfold cycleModes
  omega

theorem card_tripartiteModes (n : ℕ) (hn : 0 < n) : (tripartiteModes n).card = n ^ 2 - 1 := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n × Fin n)))
    (fun t : Fin n × Fin n => (t.1 : ℕ) ≠ 0 ∨ (t.2 : ℕ) ≠ 0)
  have h1 : (Finset.univ.filter fun t : Fin n × Fin n =>
      ¬ ((t.1 : ℕ) ≠ 0 ∨ (t.2 : ℕ) ≠ 0)).card = 1 := by
    rw [Finset.card_eq_one]
    exact ⟨(⟨0, hn⟩, ⟨0, hn⟩), by ext t; simp [Prod.ext_iff, Fin.ext_iff]⟩
  rw [h1, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h
  unfold tripartiteModes
  rw [sq]
  exact Nat.eq_sub_of_add_eq h

theorem sin_sq_pos_of_mode (n : ℕ) (k : Fin n) (hk : (k : ℕ) ≠ 0) :
    0 < Real.sin (Real.pi * (k : ℕ) / n) ^ 2 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero (fun h => by
    exact absurd k.isLt (by omega)))
  have hk0 : (0 : ℝ) < (k : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hkn : ((k : ℕ) : ℝ) < n := by exact_mod_cast k.isLt
  apply pow_pos
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos (mul_pos Real.pi_pos hk0) hn
  · rw [div_lt_iff₀ hn]
    nlinarith [Real.pi_pos]

theorem tripartiteWeight_pos (n : ℕ) (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (t : Fin n × Fin n) (ht : t ∈ tripartiteModes n) :
    0 < tripartiteWeight n A B C t.1 t.2 := by
  simp only [tripartiteModes, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  unfold tripartiteWeight
  have h1 : 0 ≤ A * B * Real.sin (Real.pi * (((t.1 : ℕ) : ℝ) - ((t.2 : ℕ) : ℝ)) / n) ^ 2 := by
    positivity
  have h2 : 0 ≤ A * C * Real.sin (Real.pi * ((t.1 : ℕ) : ℝ) / n) ^ 2 := by positivity
  have h3 : 0 ≤ B * C * Real.sin (Real.pi * ((t.2 : ℕ) : ℝ) / n) ^ 2 := by positivity
  rcases ht with ht | ht
  · have := mul_pos (mul_pos hA hC) (sin_sq_pos_of_mode n t.1 ht)
    linarith
  · have := mul_pos (mul_pos hB hC) (sin_sq_pos_of_mode n t.2 ht)
    linarith

theorem cutWeight_pos (n : ℕ) (u : ℝ) (hu : 0 < u) (k : Fin n) (hk : k ∈ cycleModes n) :
    0 < cutWeight n u k := by
  simp only [cycleModes, Finset.mem_filter, Finset.mem_univ, true_and] at hk
  exact mul_pos hu (sin_sq_pos_of_mode n k hk)

theorem log_tripartiteProduct (n : ℕ) (A B C x : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hx : 0 ≤ x) : Real.log (tripartiteProduct n A B C x) =
      ∑ t ∈ tripartiteModes n, Real.log (1 + x * tripartiteWeight n A B C t.1 t.2) := by
  rw [tripartiteProduct, Real.log_prod (fun t _ => (add_pos_of_pos_of_nonneg one_pos
    (mul_nonneg hx (tripartiteWeight_nonneg n A B C hA hB hC _ _))).ne'), tripartiteModes,
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  split_ifs with h
  · rfl
  · push Not at h
    simp [tripartiteWeight, h.1, h.2]

theorem log_cutProduct (n : ℕ) (u x : ℝ) (hu : 0 ≤ u) (hx : 0 ≤ x) :
    Real.log (cutProduct n u x) = ∑ k ∈ cycleModes n, Real.log (1 + x * cutWeight n u k) := by
  rw [cutProduct, Real.log_prod (fun k _ => (add_pos_of_pos_of_nonneg one_pos
    (mul_nonneg hx (cutWeight_nonneg n u hu _))).ne'), cycleModes, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  split_ifs with h
  · rfl
  · push Not at h
    simp [cutWeight, h]

theorem log_tripartiteLeading (n : ℕ) (hn : 0 < n) (A B C : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hN : 1 < A + B + C) :
    Real.log (tripartiteLeading n A B C) =
      ∑ t ∈ tripartiteModes n, Real.log (tripartiteWeight n A B C t.1 t.2 / (A + B + C - 1)) := by
  have hN0 : A + B + C ≠ 0 := ne_of_gt (by linarith)
  have hD : A + B + C - 1 ≠ 0 := ne_of_gt (by linarith)
  have hprod : tripartiteLeading n A B C =
      ∏ t ∈ tripartiteModes n, (tripartiteWeight n A B C t.1 t.2 / (A + B + C - 1)) := by
    rw [tripartiteLeading, tripartiteResidual, ← card_tripartiteModes n hn,
      Finset.prod_mul_pow_card]
    refine Finset.prod_congr rfl (fun t _ => ?_)
    rw [one_sub_tripartiteEigenvalue n A B C hN0]
    field_simp
  rw [hprod, Real.log_prod (fun t ht => (div_pos (tripartiteWeight_pos n A B C hA hB hC t ht)
    (by linarith)).ne')]

theorem log_cutLeading (n : ℕ) (hn : 0 < n) (U V u D : ℝ) (hU : 0 < U) (hV : 0 < V)
    (hu : U * V = u) (hD : U + V - 1 = D) (hD0 : 0 < D) :
    Real.log (cutLeading n U V) = ∑ k ∈ cycleModes n, Real.log (cutWeight n u k / D) := by
  have hN0 : U + V ≠ 0 := ne_of_gt (by linarith)
  have hD' : D ≠ 0 := hD0.ne'
  have hprod : cutLeading n U V = ∏ k ∈ cycleModes n, (cutWeight n u k / D) := by
    rw [cutLeading, cutResidual, ← card_cycleModes n hn, Finset.prod_mul_pow_card]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [one_sub_cycleEigenvalue n U V hN0, hu, hD]
    field_simp
  rw [hprod, Real.log_prod (fun k hk => (div_pos (cutWeight_pos n u (hu ▸ mul_pos hU hV) k hk)
    hD0).ne')]

theorem log_factor_tendsto (w D : ℝ) (hw : 0 < w) (hD : 0 < D) :
    Tendsto (fun a : ℝ => Real.log (1 + (a ^ 2 - 1) / D * w) - 2 * Real.log a) atTop
      (𝓝 (Real.log (w / D))) := by
  have h1 : Tendsto (fun a : ℝ => (1 - w / D) * (a⁻¹) ^ 2 + w / D) atTop (𝓝 (w / D)) := by
    have h := ((tendsto_inv_atTop_zero.pow 2).const_mul (1 - w / D)).add_const (w / D)
    simpa using h
  have h2 := h1.log (div_pos hw hD).ne'
  apply h2.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
  have ha0 : 0 < a := by linarith
  have hX : 0 < 1 + (a ^ 2 - 1) / D * w := by
    have : 0 ≤ (a ^ 2 - 1) / D * w := mul_nonneg (div_nonneg (by nlinarith) hD.le) hw.le
    linarith
  have h2a : 2 * Real.log a = Real.log (a ^ 2) := by
    rw [Real.log_pow]
    norm_num
  rw [h2a, ← Real.log_div hX.ne' (pow_pos ha0 2).ne']
  congr 1
  field_simp
  ring

/-- The Fourier product formula has the residual-determinant constant term. -/
theorem fourierGM_tendsto (n : ℕ) (hn : 2 ≤ n) (A B C : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hN : 1 < A + B + C) :
    Tendsto (fun a => fourierGM n A B C a + ((n : ℝ) - 2) / (2 * n) * Real.log a) atTop
      (𝓝 (residualConstant n A B C)) := by
  have hn0 : 0 < n := by omega
  have hD0 : 0 < A + B + C - 1 := by linarith
  have huA : 0 < A * (B + C) := by positivity
  have huB : 0 < B * (A + C) := by positivity
  have huC : 0 < C * (A + B) := by positivity
  have h3 := tendsto_finsetSum (tripartiteModes n) (fun t ht =>
    log_factor_tendsto _ _ (tripartiteWeight_pos n A B C hA hB hC t ht) hD0)
  have hcA := tendsto_finsetSum (cycleModes n) (fun k hk =>
    log_factor_tendsto _ _ (cutWeight_pos n _ huA k hk) hD0)
  have hcB := tendsto_finsetSum (cycleModes n) (fun k hk =>
    log_factor_tendsto _ _ (cutWeight_pos n _ huB k hk) hD0)
  have hcC := tendsto_finsetSum (cycleModes n) (fun k hk =>
    log_factor_tendsto _ _ (cutWeight_pos n _ huC k hk) hD0)
  have hlim := ((h3.const_mul 2).sub (((hcA.add hcB).add hcC).const_mul (n : ℝ))).div_const
    (4 * (n : ℝ) * ((n : ℝ) - 1))
  have hK : residualConstant n A B C =
      (2 * ∑ t ∈ tripartiteModes n,
          Real.log (tripartiteWeight n A B C t.1 t.2 / (A + B + C - 1)) -
        (n : ℝ) * (∑ k ∈ cycleModes n, Real.log (cutWeight n (A * (B + C)) k / (A + B + C - 1)) +
          ∑ k ∈ cycleModes n, Real.log (cutWeight n (B * (A + C)) k / (A + B + C - 1)) +
          ∑ k ∈ cycleModes n, Real.log (cutWeight n (C * (A + B)) k / (A + B + C - 1)))) /
        (4 * (n : ℝ) * ((n : ℝ) - 1)) := by
    rw [residualConstant, log_tripartiteLeading n hn0 A B C hA hB hC hN,
      log_cutLeading n hn0 (B + C) A (A * (B + C)) (A + B + C - 1) (by positivity) hA
        (by ring) (by ring) hD0,
      log_cutLeading n hn0 (A + C) B (B * (A + C)) (A + B + C - 1) (by positivity) hB
        (by ring) (by ring) hD0,
      log_cutLeading n hn0 (A + B) C (C * (A + B)) (A + B + C - 1) (by positivity) hC
        (by ring) (by ring) hD0]
  rw [hK]
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
  have hx0 : 0 ≤ squeezing (A + B + C) a := div_nonneg (by nlinarith) hD0.le
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [fourierGM, log_tripartiteProduct n A B C _ hA.le hB.le hC.le hx0,
    log_cutProduct n _ _ huA.le hx0, log_cutProduct n _ _ huB.le hx0,
    log_cutProduct n _ _ huC.le hx0, card_tripartiteModes n hn0, card_cycleModes n hn0]
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hc1 : ((n ^ 2 - 1 : ℕ) : ℝ) = (n : ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hn0), Nat.cast_pow, Nat.cast_one]
  have hc2 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hc1, hc2]
  simp only [squeezing]
  have hn0' : (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hn1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have hD' : A + B + C - 1 ≠ 0 := hD0.ne'
  field_simp
  ring

/-- The residual-determinant limit for the genuine multi-entropy of the fully symmetric
pure Gaussian state: for every replica order `n ≥ 2` and positive party sizes,
`GMₙ + ((n - 2) / (2n)) log a → Kₙ` as `a → ∞`. -/
theorem residual_determinant_limit (n NA NB NC : ℕ) (hn : 2 ≤ n) (hNA : 0 < NA) (hNB : 0 < NB)
    (hNC : 0 < NC) :
    Tendsto (fun a : ℝ => GM3 n NA NB NC a + ((n : ℝ) - 2) / (2 * n) * Real.log a) atTop
      (𝓝 (residualConstant n NA NB NC)) := by
  have hN : (3 : ℝ) ≤ (NA : ℝ) + NB + NC := by
    exact_mod_cast (show 3 ≤ NA + NB + NC by omega)
  have h := fourierGM_tendsto n hn NA NB NC (by exact_mod_cast hNA) (by exact_mod_cast hNB)
    (by exact_mod_cast hNC) (by linarith)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
  rw [GM3_eq_fourierGM n NA NB NC hn a ha hNA hNB hNC]

end D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ResidualLimit
