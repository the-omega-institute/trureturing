/- GID: D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/NativeAffineTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native affine Gaussian coefficients, finite Taylor comparison and ordinary linear transport. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource

/-! Finite Taylor comparison for the native affine moment recurrence and its
transport under arbitrary complex linear substitutions. Both finite index
types may be empty, and the substitution matrix may be rectangular, singular
or zero. Covariance uses ordinary transpose and the mean is transported by U.

proof_shape: content; admission_basis: escape-witness. The strong occupation
induction in native_affine_eq_taylor compares the native moment recurrence
with the independent finite exponential polynomial. It is consumed by
linear transport and by OriginalSourceInverseCoefficient's original-row
readout. The cutoff, coefficient and external-section helpers have live
proof consumers and provide no separate admission witness. Utility is none:
occupations and finite index types are unbounded; these are polynomial
identities, not finite certificates. Gaussian polynomial calculus is
classical; no literature novelty or completed sewing equation is asserted.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Matrix

namespace D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport

open MvPolynomial OriginalChargedRowSource
open NativeGaussianMoment (weight_sub_single sub_single_degree occupation_nonzero)
open FactorialFockQuadraticEstimate (quadratic gaussianPiece gaussianPiece_pderiv)
open FactorialFockMetric (weight weight_pos)

universe u v
variable {I : Type u} [Fintype I] [DecidableEq I]

def expCut (p : MvPolynomial I ℂ) (N : ℕ) : MvPolynomial I ℂ :=
  ∑ k ∈ Finset.range (N+1), (k.factorial : ℂ)⁻¹ • p^k

def affineExponent (A : Matrix I I ℂ) (mu : I → ℂ) : MvPolynomial I ℂ :=
  quadratic A + ∑ i, mu i • X i

def taylorCoefficient (A : Matrix I I ℂ) (mu : I → ℂ) (d : I →₀ ℕ) : ℂ :=
  (expCut (affineExponent A mu) d.degree).coeff d

private theorem pow_coeff_vanish (p : MvPolynomial I ℂ) (hp : p.coeff 0 = 0)
    (k : ℕ) (d : I →₀ ℕ) (hd : d.degree < k) : (p^k).coeff d = 0 := by
  classical
  induction k generalizing d with
  | zero => omega
  | succ k ih =>
    rw [pow_succ, coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨a,b⟩ hab
    have he : a+b = d := by simpa only [Finset.HasAntidiagonal.mem_antidiagonal] using hab
    by_cases hb : b = 0
    · simp [hb, hp]
    · have hbdeg : 0 < b.degree := by
        obtain ⟨i,hi⟩ := occupation_nonzero b hb
        have hh := sub_single_degree b i hi
        omega
      have hedeg : a.degree+b.degree = d.degree := by
        simpa only [map_add] using congrArg Finsupp.degree he
      rw [ih a (by omega), zero_mul]

theorem affineExponent_constant (A : Matrix I I ℂ) (mu : I → ℂ) :
    (affineExponent A mu).coeff 0 = 0 := by
  classical
  simp [affineExponent, quadratic, coeff_mul_X']

theorem taylorCoefficient_cut (A : Matrix I I ℂ) (mu : I → ℂ)
    (d : I →₀ ℕ) (N : ℕ) (hN : d.degree ≤ N) :
    taylorCoefficient A mu d = (expCut (affineExponent A mu) N).coeff d := by
  classical
  simp only [taylorCoefficient, expCut, coeff_sum, coeff_smul, smul_eq_mul]
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hN 1))
  intro k hk hout
  rw [pow_coeff_vanish _ (affineExponent_constant A mu) k d (by
    have hh : ¬ k < d.degree+1 := by simpa only [Finset.mem_range] using hout
    omega), mul_zero]

private theorem factorial_ratio (j : ℕ) :
    ((j+1).factorial : ℂ)⁻¹ * (j+1 : ℂ) = (j.factorial : ℂ)⁻¹ := by
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hs : (j+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [hj, hs]

theorem pderiv_expCut (p : MvPolynomial I ℂ) (n : ℕ) (i : I) :
    pderiv i (expCut p (n+1)) = pderiv i p * expCut p n := by
  classical
  have ht (j : ℕ) :
      pderiv i (((j+1).factorial : ℂ)⁻¹ • p^(j+1)) =
        pderiv i p * ((j.factorial : ℂ)⁻¹ • p^j) := by
    rw [Derivation.map_smul, pderiv_pow, Nat.add_sub_cancel]
    simp only [smul_eq_C_mul]
    have hcast : ((j+1 : ℕ) : MvPolynomial I ℂ) = C (j+1 : ℂ) := by simp
    rw [hcast]
    calc
      _ = (C (((j+1).factorial : ℂ)⁻¹) * C (j+1 : ℂ)) *
          (p^j * pderiv i p) := by ring
      _ = _ := by rw [← map_mul, factorial_ratio]; ring
  rw [expCut, map_sum, Finset.sum_range_succ']
  simp_rw [ht]
  simp only [pow_zero, pderiv_one, Derivation.map_smul, smul_zero, add_zero]
  rw [← Finset.mul_sum]
  rfl

private theorem affineExponent_pderiv (A : Matrix I I ℂ) (mu : I → ℂ)
    (hs : ∀ i j, A i j = A j i) (i : I) :
    pderiv i (affineExponent A mu) = (∑ j, A i j • X j) + C (mu i) := by
  classical
  have hq := gaussianPiece_pderiv A hs 0 i
  simp only [gaussianPiece, Nat.zero_add, Nat.factorial_one, Nat.factorial_zero,
    Nat.cast_one, inv_one, one_smul, pow_one, pow_zero, mul_one] at hq
  simp [affineExponent, hq, pderiv_X, Pi.single_apply, eq_comm, smul_eq_C_mul]

private theorem taylor_coefficient_step (A : Matrix I I ℂ) (mu : I → ℂ)
    (hs : ∀ i j, A i j = A j i) (d : I →₀ ℕ) (i : I) :
    taylorCoefficient A mu (d+Finsupp.single i 1) * (d i+1 : ℂ) =
      mu i * taylorCoefficient A mu d + ∑ j, A i j *
        (if d j ≠ 0 then taylorCoefficient A mu (d-Finsupp.single j 1) else 0) := by
  classical
  have htop : (expCut (affineExponent A mu) (d.degree+1)).coeff
      (d+Finsupp.single i 1) = taylorCoefficient A mu (d+Finsupp.single i 1) := by
    symm
    apply taylorCoefficient_cut
    simp only [map_add, Finsupp.degree_single, le_refl]
  have hbase : (expCut (affineExponent A mu) d.degree).coeff d =
      taylorCoefficient A mu d := rfl
  have hsub (j : I) : (expCut (affineExponent A mu) d.degree).coeff
      (d-Finsupp.single j 1) = taylorCoefficient A mu (d-Finsupp.single j 1) := by
    symm
    exact taylorCoefficient_cut A mu _ _ (Finsupp.degree_mono tsub_le_self)
  have h := congrArg (fun p : MvPolynomial I ℂ => p.coeff d)
    (pderiv_expCut (affineExponent A mu) d.degree i)
  rw [coeff_pderiv, htop] at h
  rw [affineExponent_pderiv A mu hs, add_mul, MvPolynomial.coeff_add, Finset.sum_mul,
    coeff_sum, coeff_C_mul, hbase] at h
  simp only [smul_mul_assoc, coeff_smul, smul_eq_mul, coeff_X_mul', hsub,
    Finsupp.mem_support_iff] at h
  exact h.trans (add_comm _ _)

private theorem taylor_moment_step (A : Matrix I I ℂ) (mu : I → ℂ)
    (hs : ∀ i j, A i j = A j i) (d : I →₀ ℕ) (i : I) :
    (weight (d+Finsupp.single i 1) : ℂ) * taylorCoefficient A mu (d+Finsupp.single i 1) =
      mu i * ((weight d : ℂ) * taylorCoefficient A mu d) +
      ∑ j, (d j : ℂ) * A i j *
        ((weight (d-Finsupp.single j 1) : ℂ) * taylorCoefficient A mu (d-Finsupp.single j 1)) := by
  classical
  have hw : (weight (d+Finsupp.single i 1) : ℂ) =
      (d i+1 : ℂ) * (weight d : ℂ) := by
    exact_mod_cast FactorialFockMetric.weight_add_single d i
  rw [hw]
  calc
    _ = (weight d : ℂ) *
        (taylorCoefficient A mu (d+Finsupp.single i 1) * (d i+1 : ℂ)) := by ring
    _ = _ := by
      rw [taylor_coefficient_step A mu hs, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro j hj
        by_cases hz : d j = 0
        · simp [hz]
        · rw [if_pos hz]
          have hwj : (weight d : ℂ) =
              (d j : ℂ) * (weight (d-Finsupp.single j 1) : ℂ) := by
            exact_mod_cast weight_sub_single d j hz
          rw [hwj]
          ring

theorem native_affine_eq_taylor (A : Matrix I I ℂ) (mu : I → ℂ)
    (hs : ∀ i j, A i j = A j i) (d : I →₀ ℕ) :
    affineCoefficient A mu d = taylorCoefficient A mu d := by
  classical
  have hm (d : I →₀ ℕ) : affineMoment A mu d =
      (weight d : ℂ) * taylorCoefficient A mu d := by
    induction hn : d.degree using Nat.strong_induction_on generalizing d with
    | h n ih =>
      by_cases hd : d = 0
      · subst d
        simp [affineMoment_zero, taylorCoefficient, expCut, weight]
      · obtain ⟨i,hi⟩ := occupation_nonzero d hd
        let r := d-Finsupp.single i 1
        have hr : r+Finsupp.single i 1 = d := Finsupp.sub_add_single_one_cancel hi
        have hrd : r.degree < n := by
          have hh := sub_single_degree d i hi
          dsimp only [r]
          omega
        have ir := ih r.degree hrd r rfl
        have ij (j : I) : affineMoment A mu (r-Finsupp.single j 1) =
            (weight (r-Finsupp.single j 1) : ℂ) *
              taylorCoefficient A mu (r-Finsupp.single j 1) := by
          apply ih (r-Finsupp.single j 1).degree
          · exact (Finsupp.degree_mono tsub_le_self).trans_lt hrd
          · rfl
        rw [← hr, affineMoment_step A mu hs, taylor_moment_step A mu hs, ir]
        simp_rw [ij]
  have h := hm d
  rw [affineMoment_coefficient] at h
  have hw : (weight d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (weight_pos d))
  exact mul_left_cancel₀ hw h


variable {J : Type v} [Fintype J] [DecidableEq J]

/-- Linear coordinate substitution: the image of source coordinate j is
sum_i U[i,j] X_i. No invertibility or complex conjugation is involved. -/
def linearSubstitution (U : Matrix I J ℂ) :
    MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ :=
  aeval (fun j => ∑ i, U i j • X i)

/-- Ordinary congruence U A U transpose, including rectangular or zero U. -/
def transportCovariance (U : Matrix I J ℂ) (A : Matrix J J ℂ) : Matrix I I ℂ :=
  fun i j => ∑ a, ∑ b, U i a * A a b * U j b

/-- The transported affine mean U mu. -/
def transportMean (U : Matrix I J ℂ) (mu : J → ℂ) : I → ℂ :=
  fun i => ∑ a, U i a * mu a

theorem transportCovariance_symm (U : Matrix I J ℂ) (A : Matrix J J ℂ)
    (hs : ∀ i j, A i j = A j i) :
    ∀ i j, transportCovariance U A i j = transportCovariance U A j i := by
  intro i j
  unfold transportCovariance
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [hs b a]
  ring

private theorem sum_four_swap {M : Type*} [AddCommMonoid M]
    (f : J → J → I → I → M) :
    (∑ a, ∑ b, ∑ i, ∑ j, f a b i j) = ∑ i, ∑ j, ∑ a, ∑ b, f a b i j := by
  calc
    _ = ∑ a, ∑ i, ∑ b, ∑ j, f a b i j := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ b, ∑ j, f a b i j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        _ = ∑ a, ∑ j, ∑ b, f a b i j := by
          apply Finset.sum_congr rfl
          intro a ha
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

private theorem quadratic_linearSubstitution (U : Matrix I J ℂ) (A : Matrix J J ℂ) :
    linearSubstitution U (quadratic A) = quadratic (transportCovariance U A) := by
  classical
  simp only [quadratic, map_smul, map_sum, map_mul, linearSubstitution, aeval_X,
    Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, smul_mul_smul_comm, smul_smul,
    transportCovariance, Finset.sum_smul]
  rw [sum_four_swap, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  ring

private theorem affineExponent_linearSubstitution (U : Matrix I J ℂ)
    (A : Matrix J J ℂ) (mu : J → ℂ) :
    linearSubstitution U (affineExponent A mu) =
      affineExponent (transportCovariance U A) (transportMean U mu) := by
  classical
  rw [affineExponent, map_add, quadratic_linearSubstitution]
  congr 1
  simp only [map_sum, map_smul, linearSubstitution, aeval_X, Finset.smul_sum,
    smul_smul, transportMean, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro a ha
  rw [mul_comm]

private theorem linearSubstitution_monomial_homogeneous
    (U : Matrix I J ℂ) (d : J →₀ ℕ) (c : ℂ) :
    (linearSubstitution U (monomial d c)).IsHomogeneous d.degree := by
  classical
  simpa only [linearSubstitution, Nat.one_mul] using (isHomogeneous_monomial (d := d) c rfl).aeval (n := 1)
    (fun j => ∑ i, U i j • (X i : MvPolynomial I ℂ)) (by
      intro j
      apply IsHomogeneous.sum
      intro i hi
      rw [smul_eq_C_mul]
      exact (isHomogeneous_X ℂ i).C_mul _)

private theorem linearSubstitution_coeff_finite (U : Matrix I J ℂ)
    (p : MvPolynomial J ℂ) (d : I →₀ ℕ) (N : ℕ) (hN : d.degree ≤ N) :
    (linearSubstitution U p).coeff d =
      ∑ e ∈ (Finsupp.finite_of_degree_le (σ := J) N).toFinset,
        p.coeff e * (linearSubstitution U (monomial e 1)).coeff d := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, coeff_sum]
  have ht (e : J →₀ ℕ) :
      (linearSubstitution U (monomial e (p.coeff e))).coeff d =
        p.coeff e * (linearSubstitution U (monomial e 1)).coeff d := by
    rw [show monomial e (p.coeff e) = p.coeff e • monomial e 1 by
      simp [smul_monomial], map_smul, coeff_smul, smul_eq_mul]
  simp_rw [ht]
  apply Finset.sum_congr_of_eq_on_inter
  · intro e he hout
    have hedeg : N < e.degree := by
      simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] using hout
    rw [(linearSubstitution_monomial_homogeneous U e 1).coeff_eq_zero (by omega), mul_zero]
  · intro e he hout
    rw [MvPolynomial.notMem_support_iff.mp hout, zero_mul]
  · intros; rfl

/-- Native affine coefficients transform under arbitrary finite linear
substitution. N bounds the TOTAL degree of the target occupation. The proof
compares the native moment recurrence with ordinary finite Taylor coefficients
and then transports the actual quadratic and linear exponent polynomials. -/
theorem affineCoefficient_linear_substitution (U : Matrix I J ℂ)
    (A : Matrix J J ℂ) (mu : J → ℂ) (hs : ∀ i j, A i j = A j i)
    (d : I →₀ ℕ) (N : ℕ) (hN : d.degree ≤ N) :
    (∑ e ∈ (Finsupp.finite_of_degree_le (σ := J) N).toFinset,
      affineCoefficient A mu e * (linearSubstitution U (monomial e 1)).coeff d) =
      affineCoefficient (transportCovariance U A) (transportMean U mu) d := by
  classical
  rw [native_affine_eq_taylor _ _ (transportCovariance_symm U A hs),
    taylorCoefficient_cut _ _ d N hN]
  have ht : linearSubstitution U (expCut (affineExponent A mu) N) =
      expCut (affineExponent (transportCovariance U A) (transportMean U mu)) N := by
    simp only [expCut, map_sum, map_smul, map_pow, affineExponent_linearSubstitution]
  rw [← ht, linearSubstitution_coeff_finite U _ d N hN]
  apply Finset.sum_congr rfl
  intro e he
  have hedeg : e.degree ≤ N := by
    simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using he
  rw [native_affine_eq_taylor A mu hs, taylorCoefficient_cut A mu e N hedeg]


/-- Extend a source substitution by fixing every external coordinate. -/
def sourceBlock (U : Matrix I I ℂ) : Matrix (I ⊕ J) (I ⊕ J) ℂ :=
  Matrix.fromBlocks U 0 0 1

def externalSection (p : MvPolynomial (I ⊕ J) ℂ) (h : J →₀ ℕ) :
    MvPolynomial I ℂ :=
  (sumRingEquiv ℂ J I (rename Sum.swap p)).coeff h

theorem externalSection_coeff (p : MvPolynomial (I ⊕ J) ℂ)
    (h : J →₀ ℕ) (d : I →₀ ℕ) :
    (externalSection p h).coeff d = p.coeff (d.sumElim h) := by
  classical
  change (AddMonoidAlgebra.mapDomainRingEquiv ℂ Finsupp.sumFinsuppAddEquivProdFinsupp
    (rename Sum.swap p)).coeff (h,d) = _
  rw [AddMonoidAlgebra.coeff_mapDomainRingEquiv]
  simp only [Finsupp.equivMapDomain_apply]
  change (rename Sum.swap p).coeff (h.sumElim d) = _
  have hj : (d.sumElim h).mapDomain Sum.swap = h.sumElim d := by
    ext (j | i)
    · exact Finsupp.mapDomain_apply_of_injective (Equiv.sumComm I J).injective _ (.inr j)
    · exact Finsupp.mapDomain_apply_of_injective (Equiv.sumComm I J).injective _ (.inl i)
  rw [← hj]
  exact coeff_rename_mapDomain Sum.swap (Equiv.sumComm I J).injective p (d.sumElim h)

private theorem sourceBlock_X (U : Matrix I I ℂ) (x : I ⊕ J) :
    linearSubstitution (sourceBlock (J := J) U) (X x) =
      match x with
      | .inl i => rename Sum.inl (linearSubstitution U (X i))
      | .inr j => X (.inr j) := by
  classical
  cases x <;> simp [linearSubstitution, sourceBlock, Fintype.sum_sum_type,
    Matrix.one_apply, eq_comm, map_sum, map_smul]

private theorem externalSection_substitution (U : Matrix I I ℂ)
    (p : MvPolynomial (I ⊕ J) ℂ) (h : J →₀ ℕ) :
    externalSection (linearSubstitution (sourceBlock U) p) h =
      linearSubstitution U (externalSection p h) := by
  classical
  have he : (sumRingEquiv ℂ J I).toRingHom.comp
      ((rename Sum.swap).toRingHom.comp (linearSubstitution (sourceBlock U)).toRingHom) =
      (MvPolynomial.map (linearSubstitution U).toRingHom).comp
        ((sumRingEquiv ℂ J I).toRingHom.comp (rename Sum.swap).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [linearSubstitution, RingHom.comp_apply]
    · intro x
      change (sumRingEquiv ℂ J I) (rename Sum.swap
          (linearSubstitution (sourceBlock U) (X x))) =
        MvPolynomial.map (linearSubstitution U).toRingHom
          ((sumRingEquiv ℂ J I) (rename Sum.swap (X x)))
      rw [sourceBlock_X]
      cases x <;> simp [linearSubstitution, map_sum, smul_eq_C_mul,
        MvPolynomial.rename_rename, Function.comp_def]

  have hp := congrArg (fun f : MvPolynomial (I ⊕ J) ℂ →+*
      MvPolynomial J (MvPolynomial I ℂ) => (f p).coeff h) he
  simp only [RingHom.comp_apply, coeff_map] at hp
  exact hp

theorem externalSection_native (U : Matrix I I ℂ)
    (A : Matrix (I ⊕ J) (I ⊕ J) ℂ) (mu : I ⊕ J → ℂ)
    (hs : ∀ i j, A i j = A j i) (d : I →₀ ℕ) (h : J →₀ ℕ)
    (N : ℕ) (hN : (d.sumElim h).degree ≤ N) :
    (linearSubstitution U (externalSection (expCut (affineExponent A mu) N) h)).coeff d =
      affineCoefficient (transportCovariance (sourceBlock U) A)
        (transportMean (sourceBlock U) mu) (d.sumElim h) := by
  rw [← externalSection_substitution, externalSection_coeff]
  have he : linearSubstitution (sourceBlock (J := J) U) (expCut (affineExponent A mu) N) =
      expCut (affineExponent (transportCovariance (sourceBlock U) A)
        (transportMean (sourceBlock U) mu)) N := by
    simp only [expCut, map_sum, map_smul, map_pow, affineExponent_linearSubstitution]
  rw [he, native_affine_eq_taylor _ _ (transportCovariance_symm _ A hs),
    taylorCoefficient_cut _ _ _ N hN]

end D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport
