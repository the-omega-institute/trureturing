/- GID: D5/S3/VertexAlgebra/Sewing/LongitudinalFockTranspose
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/Sewing/LongitudinalFockTranspose
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact Fischer transpose, factorial coefficient identity, uniform occupation mass and frequency preservation. -/
/- Delivery scope and attribution: the native import-to-EOF proof source is
preserved exactly; only this metadata prefix is authored for canonical delivery.
proof_shape: content for the transpose/chain-rule, mass inequalities and weighted
support argument (LongitudinalFockTranspose); content for the literal projected
row/column estimates and all-disk summability (CompressedOccupation).
admission_basis: escape-witness. The live non-binding step is the actual Fischer
transpose and its frequency-preserving uniform occupation majorant, used to
transport the ambient factorial column estimate through the literal projection.
Scalar/sum/radius normalization helpers are consumed in those proof paths;
they are organizational helpers, not separate new mathematical results.
utility: none: these are symbolic identities/estimates over all polynomials,
occupations and signed modes, not finite enumeration, a checker, a numerical
reduction or a certified finite instance. No completed state space is assumed.
Source attribution: supplied final native LongitudinalFockTranspose export
SHA256 518543a4ac559b5f5f651e37bb80dbdfe7b974425970e9b129fcb2d4712e745b;
supplied final native CompressedOccupation export SHA256
969e9b20dbc3c8434530097e8d2f90343215bf829fd3d4c6a55d70295037dc7d.
FactorialFockMetric, CanonicalOccupation/Row, LatticeCosetCompression and
Mathlib retain their source attribution. No literature-priority claim is made.
The actual finite ranks include zero, B is arbitrary integral, C is symmetric
even, and the original cocycle is unchanged. No additional positivity or
nondegeneracy premise is imposed. This pair proves no product identification,
braid/category coherence, full CFT, string or AdS/CFT completion.
The Blueprint mirror is produced by make emit. No separate experimental
artifact is specified by this formal content; the mirror-E field uses the
canonical route's evidence-not-specified-by-formal-manifest representation.
Typed escape registration remains separately subject to a current bounded
attempt. The incomplete source-bound audit and exact missing witnesses are
disclosed at https://github.com/the-omega-institute/trureturing/issues/29344;
no Contract registration or declared_validated status is claimed. -/

import D5.S3.VertexAlgebra.FactorialFockMetric
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! A mode-preserving linear substitution has its genuine Fischer transpose.
   The coefficient-mass argument below controls that transpose uniformly in
   every occupation. No inner product or completed state space is constructed.
   This algebraic estimate asserts no completed CFT sewing theorem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.LongitudinalFockTranspose

open MvPolynomial
open scoped BigOperators

abbrev Variables (n : ℕ) := Fin n × ℕ
abbrev Poly (n : ℕ) := MvPolynomial (Variables n) ℂ
abbrev Occupation (n : ℕ) := Variables n →₀ ℕ

def linearSub {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℂ) :
    Poly k →ₐ[ℂ] Poly n :=
  aeval (fun x : Variables k => ∑ i : Fin n, Q i x.1 • X (i,x.2))

def transposeSub {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℂ) :
    Poly n →ₐ[ℂ] Poly k :=
  linearSub (fun j i => star (Q i j))

private theorem inner_add_right {σ : Type} (p q r : MvPolynomial σ ℂ) :
    FactorialFockMetric.inner p (q+r) =
      FactorialFockMetric.inner p q + FactorialFockMetric.inner p r := by
  simp only [FactorialFockMetric.inner, map_add, _root_.inner_add_right]

private theorem inner_smul_left {σ : Type} (z : ℂ) (p q : MvPolynomial σ ℂ) :
    FactorialFockMetric.inner (z • p) q =
      star z * FactorialFockMetric.inner p q := by
  simp only [FactorialFockMetric.inner, map_smul, _root_.inner_smul_left]
  rfl

private theorem inner_smul_right {σ : Type} (z : ℂ) (p q : MvPolynomial σ ℂ) :
    FactorialFockMetric.inner p (z • q) =
      z * FactorialFockMetric.inner p q := by
  simp only [FactorialFockMetric.inner, map_smul, _root_.inner_smul_right]

private theorem inner_sum_left {σ ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial σ ℂ) (q : MvPolynomial σ ℂ) :
    FactorialFockMetric.inner (∑ i ∈ s, f i) q =
      ∑ i ∈ s, FactorialFockMetric.inner (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FactorialFockMetric.inner]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, FactorialFockMetric.inner_add_first, ih]

private theorem inner_sum_right {σ ι : Type} (s : Finset ι)
    (p : MvPolynomial σ ℂ) (f : ι → MvPolynomial σ ℂ) :
    FactorialFockMetric.inner p (∑ i ∈ s, f i) =
      ∑ i ∈ s, FactorialFockMetric.inner p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FactorialFockMetric.inner]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, inner_add_right, ih]

theorem constantCoeff_linearSub {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℂ)
    (f : Poly k) : constantCoeff (linearSub Q f) = constantCoeff f := by
  classical
  induction f using MvPolynomial.induction_on with
  | C z => simp [linearSub]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f x hf => simp [linearSub, map_sum, map_smul]

/-- The chain rule is for the literal finite substitution, at each positive
oscillator frequency. In particular it includes every rational matrix entry. -/
theorem pderiv_linearSub {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℂ)
    (x : Variables n) (f : Poly k) :
    pderiv x (linearSub Q f) =
      ∑ j : Fin k, Q x.1 j • linearSub Q (pderiv (j,x.2) f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C z => simp [linearSub]
  | add f g hf hg =>
    simp only [map_add, hf, hg, smul_add, Finset.sum_add_distrib]
  | mul_X f y hf =>
    have hvar : pderiv x (linearSub Q (X y)) =
        if x.2 = y.2 then C (Q x.1 y.1) else 0 := by
      rcases x with ⟨i,r⟩
      rcases y with ⟨j,s⟩
      by_cases hrs : r = s
      · subst s
        simp [linearSub, map_sum, Derivation.map_smul, pderiv_X,
          Pi.single_apply, Prod.mk.injEq, smul_eq_C_mul, eq_comm]
      · simp [linearSub, map_sum, Derivation.map_smul, pderiv_X,
          Pi.single_apply, Prod.mk.injEq, hrs, Ne.symm hrs]
    rw [map_mul, pderiv_mul, hf, hvar]
    simp only [pderiv_mul, map_add, map_mul, smul_add, Finset.sum_add_distrib,
      smul_mul_assoc, Finset.sum_mul]
    congr 1
    rcases y with ⟨j,s⟩
    by_cases hxy : x.2 = s
    · simp [pderiv_X, Pi.single_apply, Prod.mk.injEq, hxy, eq_comm,
        smul_eq_C_mul, mul_comm, mul_left_comm, mul_assoc]
    · simp [pderiv_X, Pi.single_apply, Prod.mk.injEq, hxy, Ne.symm hxy]

/-- This transports the inserted projection, rather than treating a projected
contraction as a subseries of an ambient contraction. -/
theorem fock_transpose {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℂ)
    (p : Poly n) (f : Poly k) :
    FactorialFockMetric.inner p (linearSub Q f) =
      FactorialFockMetric.inner (transposeSub Q p) f := by
  classical
  induction p using MvPolynomial.induction_on generalizing f with
  | C z =>
    simp only [transposeSub, linearSub, aeval_C, MvPolynomial.algebraMap_apply]
    change FactorialFockMetric.inner (monomial 0 z) (linearSub Q f) =
      FactorialFockMetric.inner (monomial 0 z) f
    simp only [FactorialFockMetric.inner_monomial_left]
    rw [show (linearSub Q f).coeff 0 = f.coeff 0 from constantCoeff_linearSub Q f]
    simp [FactorialFockMetric.weight]
  | add p q hp hq =>
    simp only [map_add, FactorialFockMetric.inner_add_first, hp, hq]
  | mul_X p x hp =>
    rw [mul_comm p (X x), FactorialFockMetric.mul_X_pderiv_pairing,
      pderiv_linearSub, inner_sum_right]
    simp_rw [inner_smul_right, hp]
    have hx : transposeSub Q (X x) =
        ∑ j : Fin k, star (Q x.1 j) • X (j,x.2) := by
      simp only [transposeSub, linearSub, aeval_X]
    rw [map_mul, hx]
    rw [Finset.sum_mul, inner_sum_left]
    apply Finset.sum_congr rfl
    intro j hj
    rw [smul_mul_assoc, inner_smul_left, star_star,
      FactorialFockMetric.mul_X_pderiv_pairing]

theorem inner_coefficient_sum {σ : Type} (p f : MvPolynomial σ ℂ) :
    FactorialFockMetric.inner p f = ∑ d ∈ p.support,
      (FactorialFockMetric.weight d : ℂ) * star (p.coeff d) * f.coeff d := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [inner_sum_left]
  exact Finset.sum_congr rfl (fun d hd =>
    FactorialFockMetric.inner_monomial_left d (p.coeff d) f)

/-- The exact coefficient formula retains factorials on both sides. -/
theorem coefficient_transpose {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℂ)
    (d : Occupation n) (f : Poly k) :
    (linearSub Q f).coeff d =
      (∑ t ∈ (transposeSub Q (monomial d 1)).support,
        (FactorialFockMetric.weight t : ℂ) *
          star ((transposeSub Q (monomial d 1)).coeff t) * f.coeff t) /
        (FactorialFockMetric.weight d : ℂ) := by
  have hw : (FactorialFockMetric.weight d : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (FactorialFockMetric.weight_pos d))
  have h := fock_transpose Q (monomial d 1) f
  rw [FactorialFockMetric.inner_monomial_left, inner_coefficient_sum] at h
  apply (eq_div_iff hw).mpr
  simpa only [map_one, star_one, mul_one, one_mul, mul_comm] using h

section Mass

variable {σ : Type}

/-- A finite coefficient mass, used only as an algebraic estimate. -/
def monomialRadius (t : σ → ℝ) (d : σ →₀ ℕ) : ℝ :=
  d.prod (fun x n => (t x)^n)

def mass (t : σ → ℝ) (p : MvPolynomial σ ℂ) : ℝ :=
  ∑ d ∈ p.support, ‖p.coeff d‖ * monomialRadius t d

theorem radius_nonneg (t : σ → ℝ) (ht : ∀ x, 0 ≤ t x) (d : σ →₀ ℕ) :
    0 ≤ monomialRadius t d := by
  exact Finset.prod_nonneg (fun x hx => pow_nonneg (ht x) _)

theorem radius_add (t : σ → ℝ) (d e : σ →₀ ℕ) :
    monomialRadius t (d+e) = monomialRadius t d * monomialRadius t e := by
  classical
  exact Finsupp.prod_add_index' (by simp) (by intros; exact pow_add _ _ _)

theorem mass_nonneg (t : σ → ℝ) (ht : ∀ x, 0 ≤ t x) (p : MvPolynomial σ ℂ) :
    0 ≤ mass t p := by
  exact Finset.sum_nonneg (fun d hd => mul_nonneg (norm_nonneg _) (radius_nonneg t ht d))

private theorem mass_eq_sum {t : σ → ℝ} (p : MvPolynomial σ ℂ)
    (s : Finset (σ →₀ ℕ)) (hs : p.support ⊆ s) :
    mass t p = ∑ d ∈ s, ‖p.coeff d‖ * monomialRadius t d := by
  classical
  exact Finset.sum_subset hs (fun d hd hn => by
    simp [MvPolynomial.notMem_support_iff.mp hn])

theorem mass_monomial (t : σ → ℝ) (d : σ →₀ ℕ) (z : ℂ) :
    mass t (monomial d z) = ‖z‖ * monomialRadius t d := by
  classical
  by_cases hz : z = 0
  · simp [hz, mass]
  · simp [mass, MvPolynomial.support_monomial, hz]

theorem mass_add_le (t : σ → ℝ) (ht : ∀ x, 0 ≤ t x)
    (p q : MvPolynomial σ ℂ) : mass t (p+q) ≤ mass t p + mass t q := by
  classical
  let s := p.support ∪ q.support
  rw [mass_eq_sum (p+q) s MvPolynomial.support_add,
    mass_eq_sum p s Finset.subset_union_left,
    mass_eq_sum q s Finset.subset_union_right, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  rw [MvPolynomial.coeff_add, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (radius_nonneg t ht d)

theorem mass_sum_le {ι : Type} (t : σ → ℝ) (ht : ∀ x, 0 ≤ t x)
    (s : Finset ι) (p : ι → MvPolynomial σ ℂ) :
    mass t (∑ i ∈ s, p i) ≤ ∑ i ∈ s, mass t (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mass]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (mass_add_le t ht _ _).trans (add_le_add_right ih _)

theorem mass_mul_le (t : σ → ℝ) (ht : ∀ x, 0 ≤ t x)
    (p q : MvPolynomial σ ℂ) : mass t (p*q) ≤ mass t p * mass t q := by
  classical
  rw [MvPolynomial.mul_def]
  change mass t (∑ d ∈ p.support, ∑ e ∈ q.support,
    monomial (d+e) (p.coeff d * q.coeff e)) ≤ _
  calc
    _ ≤ ∑ d ∈ p.support, mass t (∑ e ∈ q.support,
        monomial (d+e) (p.coeff d * q.coeff e)) := mass_sum_le t ht _ _
    _ ≤ ∑ d ∈ p.support, ∑ e ∈ q.support,
        mass t (monomial (d+e) (p.coeff d * q.coeff e)) :=
      Finset.sum_le_sum (fun d hd => mass_sum_le t ht _ _)
    _ = _ := by
      simp only [mass_monomial, norm_mul, radius_add]
      unfold mass
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      ring

theorem mass_pow_le (t : σ → ℝ) (ht : ∀ x, 0 ≤ t x)
    (p : MvPolynomial σ ℂ) (N : ℕ) : mass t (p^N) ≤ (mass t p)^N := by
  induction N with
  | zero =>
    rw [pow_zero, pow_zero]
    change mass t (monomial 0 1) ≤ 1
    simp only [mass_monomial, norm_one, monomialRadius, Finsupp.prod_zero_index, one_mul,
      le_refl]
  | succ N ih =>
    rw [pow_succ, pow_succ]
    exact (mass_mul_le t ht _ _).trans
      (mul_le_mul_of_nonneg_right ih (mass_nonneg t ht p))

theorem mass_prod_le {ι : Type} (t : σ → ℝ) (ht : ∀ x, 0 ≤ t x)
    (s : Finset ι) (p : ι → MvPolynomial σ ℂ) :
    mass t (∏ i ∈ s, p i) ≤ ∏ i ∈ s, mass t (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    change mass t (monomial 0 1) ≤ 1
    simp only [mass_monomial, norm_one, monomialRadius, Finsupp.prod_zero_index, one_mul,
      le_refl]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (mass_mul_le t ht _ _).trans
      (mul_le_mul_of_nonneg_left ih (mass_nonneg t ht _))

end Mass

/-- A finite matrix has one occupation-independent absolute row-sum bound.
The added 1 also covers empty color sets and zero longitudinal matrices. -/
def rowSumBound {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℂ) : ℝ :=
  1 + ∑ i : Fin n, ∑ j : Fin k, ‖Q i j‖

theorem rowSumBound_one_le {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℂ) :
    1 ≤ rowSumBound Q := by
  have h : 0 ≤ ∑ i : Fin n, ∑ j : Fin k, ‖Q i j‖ :=
    Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => norm_nonneg _))
  unfold rowSumBound
  linarith

theorem rowSum_le {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℂ) (i : Fin n) :
    (∑ j : Fin k, ‖Q i j‖) ≤ rowSumBound Q := by
  have h : (∑ j : Fin k, ‖Q i j‖) ≤ ∑ a : Fin n, ∑ j : Fin k, ‖Q a j‖ :=
    Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun j _ => norm_nonneg (Q a j)))
      (Finset.mem_univ i)
  unfold rowSumBound
  linarith

def frequencyRadius {k : ℕ} (A : ℝ) (x : Variables k) : ℝ := A / (x.2+1 : ℝ)

theorem frequencyRadius_nonneg {k : ℕ} (A : ℝ) (hA : 0 ≤ A)
    (x : Variables k) : 0 ≤ frequencyRadius A x := by
  exact div_nonneg hA (by positivity)

private theorem transpose_variable_mass {n k : ℕ}
    (Q : Matrix (Fin n) (Fin k) ℂ) (A : ℝ) (hA : 0 ≤ A) (x : Variables n) :
    mass (frequencyRadius A) (transposeSub Q (X x)) ≤
      frequencyRadius (A * rowSumBound Q) x := by
  classical
  simp only [transposeSub, linearSub, aeval_X]
  calc
    _ ≤ ∑ j : Fin k, mass (frequencyRadius A) (star (Q x.1 j) • X (j,x.2)) :=
      mass_sum_le _ (frequencyRadius_nonneg A hA) _ _
    _ = (A / (x.2+1 : ℝ)) * ∑ j : Fin k, ‖Q x.1 j‖ := by
      simp [X, MvPolynomial.smul_monomial, mass_monomial, monomialRadius,
        frequencyRadius, norm_star, Finset.mul_sum, mul_comm]
    _ ≤ (A / (x.2+1 : ℝ)) * rowSumBound Q :=
      mul_le_mul_of_nonneg_left (rowSum_le Q x.1) (by positivity)
    _ = _ := by unfold frequencyRadius; ring

/-- The new uniform transpose majorant. The denominator frequency is retained;
no constant is raised to oscillator energy. Only the occupation degree grows. -/
theorem transpose_monomial_mass {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℂ)
    (A : ℝ) (hA : 0 ≤ A) (d : Occupation n) :
    mass (frequencyRadius A) (transposeSub Q (monomial d 1)) ≤
      monomialRadius (frequencyRadius (A * rowSumBound Q)) d := by
  classical
  rw [show transposeSub Q (monomial d 1) =
      ∏ x ∈ d.support, (transposeSub Q (X x)) ^ d x by
    simp [transposeSub, linearSub, aeval_eq_bind₁, bind₁_monomial, Finsupp.prod]]
  calc
    _ ≤ ∏ x ∈ d.support, mass (frequencyRadius A) ((transposeSub Q (X x))^d x) :=
      mass_prod_le _ (frequencyRadius_nonneg A hA) _ _
    _ ≤ ∏ x ∈ d.support, mass (frequencyRadius A) (transposeSub Q (X x)) ^ d x := by
      apply Finset.prod_le_prod₀
      · intro x hx; exact mass_nonneg _ (frequencyRadius_nonneg A hA) _
      · intro x hx; exact mass_pow_le _ (frequencyRadius_nonneg A hA) _ _
    _ ≤ _ := by
      apply Finset.prod_le_prod₀
      · intro x hx; exact pow_nonneg (mass_nonneg _ (frequencyRadius_nonneg A hA) _) _
      · intro x hx
        exact pow_le_pow_left₀ (mass_nonneg _ (frequencyRadius_nonneg A hA) _)
          (transpose_variable_mass Q A hA x) _

def energy {n : ℕ} (d : Occupation n) : ℕ :=
  Finsupp.weight (fun x : Variables n => x.2+1) d

/-- Every monomial in the actual transpose has exactly the original energy.
This is a support conclusion, not an intermediate-state cutoff premise. -/
theorem transpose_monomial_energy {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℂ)
    (d : Occupation n) {t : Occupation k}
    (ht : (transposeSub Q (monomial d 1)).coeff t ≠ 0) : energy t = energy d := by
  classical
  have hv (x : Variables n) :
      (transposeSub Q (X x)).IsWeightedHomogeneous
        (fun y : Variables k => y.2+1) (x.2+1) := by
    simp only [transposeSub, linearSub, aeval_X]
    apply MvPolynomial.IsWeightedHomogeneous.sum
    intro j hj
    simpa [MvPolynomial.smul_eq_C_mul] using
      (MvPolynomial.isWeightedHomogeneous_X ℂ (fun y : Variables k => y.2+1)
        (j,x.2)).C_mul (star (Q x.1 j))
  have hp := MvPolynomial.IsWeightedHomogeneous.prod d.support
    (fun x => (transposeSub Q (X x)) ^ d x)
    (fun x => d x • (x.2+1)) (fun x hx => (hv x).pow (d x))
  have he : (∑ x ∈ d.support, d x • (x.2+1)) = energy d := by
    simp [energy, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  rw [he] at hp
  have hm : transposeSub Q (monomial d 1) =
      ∏ x ∈ d.support, (transposeSub Q (X x)) ^ d x := by
    simp [transposeSub, linearSub, aeval_eq_bind₁, bind₁_monomial, Finsupp.prod]
  rw [hm] at ht
  exact hp ht

end D5.S3.VertexAlgebra.LongitudinalFockTranspose
