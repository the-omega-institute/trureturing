/- GID: D5/S3/Quantum/Dynamics/AverageMixingDiscriminantIntegrality
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/AverageMixingDiscriminantIntegrality
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: The minimal-polynomial discriminant clears average mixing denominators. -/

/-
proof_shape: result: content
escape_witness: the local discriminant cancellation discr_scaled_entry and the
  permutation-invariant formalSum in result express every scaled mixing entry as
  an integer symmetric polynomial in the distinct eigenvalues; Vieta and the
  fundamental theorem of symmetric polynomials supply its integer value.
admission_basis: open-problem-resolution (#12339; Proved)
Direct frozen dependencies:
  D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.idempotent,
  D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.avgMixing;
  statement_id: sha256:e9ed4aafa0539ad392a8da26418ae5af60eaf51671d3d661f56e05577edd7ac5.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.Vieta

open Matrix Finset Polynomial
open D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum (idempotent avgMixing)

namespace D5.S3.Quantum.Dynamics.AverageMixingDiscriminantIntegrality

/-- Godsil, arXiv:1103.2578v3, section 11, Question 1: the minimal-polynomial
discriminant times the average mixing matrix has integer entries. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∀ i j,
    ∃ z : ℤ, ((minpoly ℚ (G.adjMatrix ℚ)).discr : ℝ) * avgMixing G i j = z

set_option backward.isDefEq.respectTransparency false in
/-- Affirmative answer to Question 1 for every finite simple graph. -/
theorem result : claim := by
  classical
  -- Coefficient maps preserve the monic discriminant.
  have discr_map {R S : Type} [CommRing R] [CommRing S] [IsDomain R]
      [IsDomain S] (φ : R →+* S) (f : R[X]) (hm : f.Monic) :
      (f.map φ).discr = φ f.discr := by
    by_cases h0 : f.natDegree = 0
    · have hf : f = 1 := hm.natDegree_eq_zero.mp h0
      have hR : (1 : R[X]).discr = 1 := by simpa only [C_1] using discr_C (1 : R)
      have hS : (1 : S[X]).discr = 1 := by simpa only [C_1] using discr_C (1 : S)
      simp only [hf, Polynomial.map_one, map_one, hR, hS]
    have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero h0)
    have hdm : (f.map φ).natDegree = f.natDegree := hm.natDegree_map φ
    have hpm : 0 < (f.map φ).degree := by
      rw [← natDegree_pos_iff_degree_pos, hdm]
      exact Nat.pos_of_ne_zero h0
    have hleft := resultant_deriv hpm
    rw [derivative_map, hdm, resultant_map_map] at hleft
    have hright := congrArg φ (resultant_deriv hdeg)
    have hm' := hm.map φ
    simp only [map_mul, map_pow, map_neg, map_one, hm.leadingCoeff,
      hm'.leadingCoeff, mul_one] at hleft hright
    exact mul_left_cancel₀ (by simp : (-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2) ≠ 0)
      (hleft.symm.trans hright)
  -- Removing one root cancels its squared spectral denominator.
  have discr_mul_root {R : Type} [CommRing R] [IsDomain R] [CharZero R]
      (q : R[X]) (hq : q.Monic) (a : R) :
      ((X - C a) * q).discr = q.discr * q.eval a ^ 2 := by
    by_cases h0 : q.natDegree = 0
    · have hf : q = 1 := hq.natDegree_eq_zero.mp h0
      rw [hf, mul_one, discr_of_degree_eq_one (degree_X_sub_C a)]
      have hR : (1 : R[X]).discr = 1 := by simpa only [C_1] using discr_C (1 : R)
      simp only [hR, eval_one, one_pow, mul_one]
    let d := q.natDegree
    have hd : 0 < d := Nat.pos_of_ne_zero h0
    have hq0 : q ≠ 0 := hq.ne_zero
    have hqd : 0 < q.degree := natDegree_pos_iff_degree_pos.mp hd
    have hfdeg : ((X - C a) * q).natDegree = 1 + d := by
      rw [natDegree_mul (X_sub_C_ne_zero a) hq0, natDegree_X_sub_C]
    have hfd : 0 < ((X - C a) * q).degree := by
      rw [← natDegree_pos_iff_degree_pos, hfdeg]
      omega
    have hfm : ((X - C a) * q).Monic := (monic_X_sub_C a).mul hq
    have hfder : derivative ((X - C a) * q) = (X - C a) * q.derivative + q := by
      rw [derivative_mul, derivative_X_sub_C, one_mul, add_comm]
    have hreduce : resultant q (derivative ((X - C a) * q)) d d =
        resultant q ((X - C a) * q.derivative) d d := by
      rw [hfder]
      have hh : resultant q (((X - C a) * q.derivative) + q * 1) d d =
          resultant q ((X - C a) * q.derivative) d d :=
        resultant_add_mul_right (R := R) q ((X - C a) * q.derivative) (1 : R[X]) d d
          (by simp only [natDegree_one, zero_add]; exact le_rfl) le_rfl
      rw [mul_one] at hh
      exact hh
    have hmult : resultant q ((X - C a) * q.derivative) d d =
        ((-1 : R) ^ d * q.eval a) * resultant q q.derivative d (d - 1) := by
      have hh := resultant_mul_right q (X - C a) q.derivative d le_rfl
      rw [natDegree_X_sub_C, natDegree_derivative] at hh
      have hhdeg : 1 + (d - 1) = d := by omega
      rw [show 1 + (q.natDegree - 1) = d from hhdeg] at hh
      rw [resultant_X_sub_C_right q d a le_rfl] at hh
      exact hh
    have hresult : resultant ((X - C a) * q) (derivative ((X - C a) * q)) (1 + d) d =
        q.eval a * (((-1 : R) ^ d * q.eval a) *
          ((-1 : R) ^ (d * (d - 1) / 2) * q.discr)) := by
      have hh := resultant_mul_left (X - C a) q (derivative ((X - C a) * q)) d
        (by rw [natDegree_derivative, hfdeg]; omega)
      rw [natDegree_X_sub_C, resultant_X_sub_C_left _ d a (by
        rw [natDegree_derivative, hfdeg]; omega), hfder] at hh
      have heval : eval a ((X - C a) * derivative q + q) = eval a q := by simp
      rw [heval] at hh
      rw [← hfder, hreduce, hmult] at hh
      have hqr := resultant_deriv hqd
      simp only [hq.leadingCoeff, mul_one] at hqr
      rw [hqr] at hh
      exact hh
    have hfr := resultant_deriv hfd
    rw [hfdeg] at hfr
    simp only [hfm.leadingCoeff, mul_one] at hfr
    have he : (1 + d) * (1 + d - 1) / 2 = d + d * (d - 1) / 2 := by
      have hh := Nat.choose_succ_succ' d 1
      change (d + 1).choose 2 = d.choose 1 + d.choose 2 at hh
      simpa only [Nat.choose_two_right, Nat.choose_one_right, Nat.add_comm] using hh
    rw [he, pow_add, show 1 + d - 1 = d by omega] at hfr
    have hsign : ((-1 : R) ^ d * (-1 : R) ^ (d * (d - 1) / 2)) ≠ 0 := by simp
    apply mul_left_cancel₀ hsign
    rw [← hfr, hresult]
    ring
  -- Polynomial evaluation preserves symmetry.
  have symm_aeval {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
      (hA : A.IsSymm) (p : ℚ[X]) : (aeval A p).IsSymm := by
    rw [aeval_eq_sum_range]
    apply Matrix.IsSymm.ext
    intro i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply sum_congr rfl
    intro k hk
    rw [(hA.pow k).apply i j]
  -- A symmetric rational matrix with square zero vanishes.
  have symm_sq_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ)
      (hB : B.IsSymm) (h0 : B ^ 2 = 0) : B = 0 := by
    ext i j
    have hi : ∑ k, B i k ^ 2 = 0 := by
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℚ => M i i) h0
      calc ∑ k, B i k ^ 2 = ∑ k, B i k * B k i := by
             apply sum_congr rfl
             intro k hk
             rw [hB.apply i k, pow_two]
           _ = 0 := by simpa only [pow_two, Matrix.mul_apply, Matrix.zero_apply] using h
    have hij : B i j ^ 2 = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (B i k))).mp hi j (mem_univ j)
    simpa only [sq_eq_zero_iff, Matrix.zero_apply] using hij
  -- The symmetric adjacency matrix has a squarefree minimal polynomial.
  have adj_minpoly_squarefree {n : ℕ} (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj] : Squarefree (minpoly ℚ (G.adjMatrix ℚ)) := by
    apply IsRadical.squarefree (minpoly.ne_zero (Matrix.isIntegral _))
    apply (isRadical_iff_pow_one_lt 2 one_lt_two).mpr
    intro p hp
    apply minpoly.dvd
    exact symm_sq_zero _ (symm_aeval _ G.isSymm_adjMatrix p) (by
      rw [← map_pow]
      exact minpoly.dvd_iff.mp hp)
  -- The monic rational minimal polynomial has integer coefficients.
  have adj_minpoly_integer {n : ℕ} (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj] :
      ∃ f : ℤ[X], f.Monic ∧ f.map (algebraMap ℤ ℚ) = minpoly ℚ (G.adjMatrix ℚ) := by
    have hmap : (G.adjMatrix ℤ).map (algebraMap ℤ ℚ) = G.adjMatrix ℚ := by
      ext i j
      simp [SimpleGraph.adjMatrix_apply]
    have hd : minpoly ℚ (G.adjMatrix ℚ) ∣
        (G.adjMatrix ℤ).charpoly.map (algebraMap ℤ ℚ) := by
      rw [← Matrix.charpoly_map, hmap]
      exact Matrix.minpoly_dvd_charpoly _
    obtain ⟨f, hf⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ
      (Matrix.charpoly_monic (G.adjMatrix ℤ)) hd
    have hm : (minpoly ℚ (G.adjMatrix ℚ)).Monic := minpoly.monic (Matrix.isIntegral _)
    rw [hm.leadingCoeff, C_1, mul_one] at hf
    refine ⟨f, ?_, hf⟩
    exact Polynomial.monic_of_injective Int.cast_injective (hf ▸ hm)
  -- Use the same Hermitian proof as the imported spectral projections.
  have hermitian {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
      (G.adjMatrix ℝ).IsHermitian := isHermitian_iff_isSymm.mpr G.isSymm_adjMatrix
  -- Polynomial evaluation acts coordinatewise on a diagonal matrix.
  have aeval_diagonal {n : ℕ} (x : Fin n → ℝ) (p : ℝ[X]) :
      aeval (diagonal x) p = diagonal (fun k => p.eval (x k)) := by
    change aeval ((diagonalAlgHom ℝ : (Fin n → ℝ) →ₐ[ℝ] Matrix (Fin n) (Fin n) ℝ) x) p = _
    rw [aeval_algHom_apply]
    change diagonal (aeval x p) = diagonal (fun k => p.eval (x k))
    congr 1
    exact funext (fun k => aeval_pi_apply₂ x p k)
  -- Conjugate diagonal evaluation into the orthonormal eigenbasis.
  have aeval_spectral {n : ℕ} (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj] (p : ℝ[X]) :
      aeval (G.adjMatrix ℝ) p =
        ∑ k, p.eval ((hermitian G).eigenvalues k) •
          vecMulVec ⇑((hermitian G).eigenvectorBasis k)
            ⇑((hermitian G).eigenvectorBasis k) := by
    conv_lhs => rw [(hermitian G).spectral_theorem]
    rw [aeval_algHom_apply]
    have hx : (RCLike.ofReal ∘ (hermitian G).eigenvalues) = (hermitian G).eigenvalues := rfl
    rw [hx, aeval_diagonal, Unitary.conjStarAlgAut_apply]
    ext i j
    rw [Matrix.mul_apply]
    simp only [mul_diagonal, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, vecMulVec_apply, star_eq_conjTranspose, conjTranspose_apply,
      star_trivial, Matrix.IsHermitian.eigenvectorUnitary_apply]
    apply sum_congr rfl
    intro k hk
    ring
  -- Each distinct eigenvalue occurs once.
  let eigs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
      Finset ℝ := by
    classical
    exact univ.image (hermitian G).eigenvalues
  -- The root-deleted polynomial supplies the projector numerator.
  let numerator {n : ℕ} (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj] (θ : ℝ) : ℝ[X] := by
    classical
    exact ∏ s ∈ (eigs G).erase θ, (X - C s)
  -- Its evaluation at the omitted root supplies the projector denominator.
  let denominator {n : ℕ} (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj] (θ : ℝ) : ℝ := by
    classical
    exact ∏ s ∈ (eigs G).erase θ, (θ - s)
  -- The root-deleted polynomial vanishes at every other eigenvalue.
  have numerator_eval {n : ℕ} (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj] (θ : ℝ) (k : Fin n) :
      (numerator G θ).eval ((hermitian G).eigenvalues k) =
        if (hermitian G).eigenvalues k = θ then denominator G θ else 0 := by
    classical
    simp only [numerator, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    split_ifs with hk
    · simp only [hk, denominator]
    · apply prod_eq_zero ((mem_erase.mpr ⟨hk, mem_image_of_mem _ (mem_univ k)⟩) :
        (hermitian G).eigenvalues k ∈ (eigs G).erase θ)
      exact sub_self _
  -- Identify the polynomial matrix with the scaled spectral projector.
  have lagrange_scaled {n : ℕ} (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj] (θ : ℝ) :
      aeval (G.adjMatrix ℝ) (numerator G θ) = denominator G θ • idempotent G θ := by
    classical
    rw [aeval_spectral]
    unfold idempotent
    rw [Finset.smul_sum, Finset.sum_filter]
    apply sum_congr rfl
    intro k hk
    rw [numerator_eval]
    split_ifs <;> simp
  -- An annihilating polynomial vanishes at every eigenvalue.
  have aeval_eigen_zero {n : ℕ} (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj] (p : ℝ[X]) (hp : aeval (G.adjMatrix ℝ) p = 0) (k : Fin n) :
      p.eval ((hermitian G).eigenvalues k) = 0 := by
    let φ := Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) (hermitian G).eigenvectorUnitary
    have hh : aeval (G.adjMatrix ℝ) p =
        φ (diagonal (fun i => p.eval ((hermitian G).eigenvalues i))) := by
      conv_lhs => rw [(hermitian G).spectral_theorem]
      rw [aeval_algHom_apply]
      change φ (aeval (diagonal ((hermitian G).eigenvalues)) p) = _
      rw [aeval_diagonal]
    have hz : diagonal (fun i => p.eval ((hermitian G).eigenvalues i)) = 0 := by
      apply φ.injective
      change φ (diagonal (fun i => p.eval ((hermitian G).eigenvalues i))) = φ 0
      rw [← hh, hp, map_zero]
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M k k) hz
    simpa only [diagonal_apply_eq, Matrix.zero_apply] using this
  -- Transport the rational annihilation identity to the real matrix.
  have adj_minpoly_real_aeval {n : ℕ} (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj] :
      aeval (G.adjMatrix ℝ) ((minpoly ℚ (G.adjMatrix ℚ)).map (algebraMap ℚ ℝ)) = 0 := by
    let φ : Matrix (Fin n) (Fin n) ℚ →ₐ[ℚ] Matrix (Fin n) (Fin n) ℝ :=
      (Algebra.ofId ℚ ℝ).mapMatrix
    have hφ : φ (G.adjMatrix ℚ) = G.adjMatrix ℝ := by
      ext i j
      simp [φ, SimpleGraph.adjMatrix_apply]
    have hq : aeval (G.adjMatrix ℝ) (minpoly ℚ (G.adjMatrix ℚ)) = 0 := by
      rw [← hφ, aeval_algHom_apply, minpoly.aeval, map_zero]
    rw [← aeval_eq_aeval_map (IsScalarTower.algebraMap_eq ℚ ℝ _).symm]
    exact hq
  -- Identify the simple roots of the minimal polynomial with the spectrum.
  have adj_minpoly_root_product {n : ℕ} (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj] :
      (minpoly ℚ (G.adjMatrix ℚ)).map (algebraMap ℚ ℝ) = ∏ θ ∈ eigs G, (X - C θ) := by
    classical
    let f : ℝ[X] := (minpoly ℚ (G.adjMatrix ℚ)).map (algebraMap ℚ ℝ)
    have hm : f.Monic := (minpoly.monic (Matrix.isIntegral _)).map _
    have hmap : (G.adjMatrix ℚ).map (algebraMap ℚ ℝ) = G.adjMatrix ℝ := by
      ext i j
      simp [SimpleGraph.adjMatrix_apply]
    have hd : f ∣ (G.adjMatrix ℝ).charpoly := by
      rw [← hmap, Matrix.charpoly_map]
      exact Polynomial.map_dvd (algebraMap ℚ ℝ) (Matrix.minpoly_dvd_charpoly (G.adjMatrix ℚ))
    have hs : f.Splits := (hermitian G).splits_charpoly.of_dvd
      (Matrix.charpoly_monic _).ne_zero hd
    have hn : f.roots.Nodup := Polynomial.nodup_roots
      ((PerfectField.separable_iff_squarefree.mpr (adj_minpoly_squarefree G)).map)
    have hr : f.roots.toFinset = eigs G := by
      ext θ
      constructor
      · intro hθ
        have hc : θ ∈ (G.adjMatrix ℝ).charpoly.roots :=
          Multiset.mem_of_le (Polynomial.roots.le_of_dvd (Matrix.charpoly_monic _).ne_zero hd)
            (Multiset.mem_toFinset.mp hθ)
        rw [(hermitian G).roots_charpoly_eq_eigenvalues] at hc
        simpa [eigs] using hc
      · intro hθ
        obtain ⟨k, hk, rfl⟩ := mem_image.mp hθ
        apply Multiset.mem_toFinset.mpr
        apply (Polynomial.mem_roots hm.ne_zero).mpr
        exact aeval_eigen_zero G f (adj_minpoly_real_aeval G) k
    change f = _
    rw [← hr, ← Multiset.toFinset_eq hn, Finset.prod_mk]
    exact hs.eq_prod_roots_of_monic hm
  -- Cancel the discriminant against each squared projector denominator.
  have discr_scaled_entry {n : ℕ} (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj] (θ : ℝ) (hθ : θ ∈ eigs G) (i j : Fin n) :
      ((minpoly ℚ (G.adjMatrix ℚ)).discr : ℝ) * (idempotent G θ i j) ^ 2 =
        (numerator G θ).discr * (aeval (G.adjMatrix ℝ) (numerator G θ) i j) ^ 2 := by
    classical
    have hm : (numerator G θ).Monic := monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)
    have hf : (minpoly ℚ (G.adjMatrix ℚ)).map (algebraMap ℚ ℝ) =
        (X - C θ) * numerator G θ := by
      rw [adj_minpoly_root_product]
      dsimp only [numerator]
      exact (mul_prod_erase _ (fun s => X - C s) hθ).symm
    have hd : ((minpoly ℚ (G.adjMatrix ℚ)).discr : ℝ) =
        (numerator G θ).discr * denominator G θ ^ 2 := by
      change (algebraMap ℚ ℝ) ((minpoly ℚ (G.adjMatrix ℚ)).discr) = _
      rw [← discr_map (algebraMap ℚ ℝ) _ (minpoly.monic (Matrix.isIntegral _)), hf,
        discr_mul_root _ hm]
      congr 1
      simp only [numerator, denominator, eval_prod, eval_sub, eval_X, eval_C]
    have hb := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) (lagrange_scaled G θ)
    simp only [Matrix.smul_apply, smul_eq_mul] at hb
    rw [hd, hb]
    ring
  -- Replace the eigenvalues by independent integer polynomial variables.
  let formalNumerator {σ : Type} [Fintype σ] (r : σ) :
      Polynomial (MvPolynomial σ ℤ) := by
    classical
    exact ∏ s ∈ univ.erase r, (X - C (MvPolynomial.X s))
  -- Each formal root-deleted polynomial is monic.
  have formalNumerator_monic {σ : Type} [Fintype σ] (r : σ) :
      (formalNumerator r).Monic :=
    monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)
  -- Permuting variables carries the omitted root along with them.
  have formalNumerator_rename {σ : Type} [Fintype σ] (e : Equiv.Perm σ) (r : σ) :
      (formalNumerator r).map (MvPolynomial.rename e).toRingHom = formalNumerator (e r) := by
    classical
    simp only [formalNumerator, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.rename_X]
    apply prod_bij (fun s _ => e s)
    · intro s hs
      exact mem_erase.mpr ⟨fun h => (ne_of_mem_erase hs) (e.injective h), mem_univ _⟩
    · intro s hs t ht hst
      exact e.injective hst
    · intro s hs
      refine ⟨e.symm s, mem_erase.mpr ⟨?_, mem_univ _⟩, e.apply_symm_apply s⟩
      intro h
      exact (ne_of_mem_erase hs) (by rw [← h, e.apply_symm_apply])
    · intro s hs
      rfl
  -- Coefficient maps commute with polynomial matrix evaluation.
  have matrix_aeval_map {n : ℕ} {R S : Type} [CommRing R] [CommRing S]
      (φ : R →+* S) (A : Matrix (Fin n) (Fin n) R) (p : R[X]) :
      φ.mapMatrix (aeval A p) = aeval (φ.mapMatrix A) (p.map φ) := by
    apply map_aeval_eq_aeval_map
    ext r i j
    by_cases h : i = j
    · subst j
      simp [RingHom.mapMatrix_apply, Matrix.algebraMap_eq_diagonal]
    · simp [RingHom.mapMatrix_apply, Matrix.algebraMap_eq_diagonal, h]
  -- Integer adjacency entries are preserved by the coefficient map.
  have adj_aeval_map {n : ℕ} {R S : Type} [CommRing R] [CommRing S]
      (φ : R →+* S) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : R[X]) (i j : Fin n) :
      φ (aeval (G.adjMatrix R) p i j) = aeval (G.adjMatrix S) (p.map φ) i j := by
    have hA : φ.mapMatrix (G.adjMatrix R) = G.adjMatrix S := by
      ext u v
      simp [RingHom.mapMatrix_apply, SimpleGraph.adjMatrix_apply]
    have hh := congrArg (fun M : Matrix (Fin n) (Fin n) S => M i j)
      (matrix_aeval_map φ (G.adjMatrix R) p)
    rw [hA] at hh
    exact hh
  -- Construct the integer polynomial for a discriminant-scaled entry.
  let formalSum {σ : Type} [Fintype σ] {n : ℕ}
      (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i j : Fin n) : MvPolynomial σ ℤ :=
    ∑ r : σ, (formalNumerator r).discr *
      (aeval (G.adjMatrix (MvPolynomial σ ℤ)) (formalNumerator r) i j) ^ 2
  -- Reindex both products and the sum to prove permutation invariance.
  have formalSum_symmetric {σ : Type} [Fintype σ] {n : ℕ}
      (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i j : Fin n) :
      (formalSum (σ := σ) G i j).IsSymmetric := by
    classical
    intro e
    simp only [formalSum, map_sum, map_mul, map_pow]
    have hr (r : σ) : MvPolynomial.rename e
        ((formalNumerator r).discr) *
          (MvPolynomial.rename e
            (aeval (G.adjMatrix (MvPolynomial σ ℤ)) (formalNumerator r) i j)) ^ 2 =
        (formalNumerator (e r)).discr *
          (aeval (G.adjMatrix (MvPolynomial σ ℤ)) (formalNumerator (e r)) i j) ^ 2 := by
      have hd := discr_map (MvPolynomial.rename e).toRingHom _ (formalNumerator_monic r)
      have hb := adj_aeval_map (MvPolynomial.rename e).toRingHom G (formalNumerator r) i j
      rw [formalNumerator_rename] at hd hb
      simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
        congrArg₂ (fun a b => a * b ^ 2) hd.symm hb
    simp_rw [hr]
    exact Fintype.sum_equiv e _ _ (fun r => rfl)
  -- Integer elementary symmetric values make every symmetric value integral.
  have symmetric_integer_eval {σ : Type} [Fintype σ]
      (p : MvPolynomial σ ℤ) (hp : p.IsSymmetric) (x : σ → ℝ)
      (hx : ∀ k : Fin (Fintype.card σ),
        ∃ z : ℤ, MvPolynomial.aeval x (MvPolynomial.esymm σ ℤ (k.val + 1)) = z) :
      ∃ z : ℤ, MvPolynomial.aeval x p = z := by
    classical
    obtain ⟨q, hq⟩ := MvPolynomial.esymmAlgHom_surjective (σ := σ) ℤ le_rfl ⟨p, hp⟩
    have hpq : p = MvPolynomial.aeval
        (fun k : Fin (Fintype.card σ) => MvPolynomial.esymm σ ℤ (k.val + 1)) q := by
      have hh := congrArg Subtype.val hq
      rw [MvPolynomial.esymmAlgHom_apply] at hh
      exact hh.symm
    choose z hz using hx
    refine ⟨MvPolynomial.aeval z q, ?_⟩
    rw [hpq, MvPolynomial.comp_aeval_apply]
    simp only [hz]
    exact (MvPolynomial.comp_aeval_apply z (Algebra.ofId ℤ ℝ) q).symm
  -- Vieta gives signed integer coefficients for the elementary symmetric values.
  have esymm_integer_eval {σ : Type} [Fintype σ] (x : σ → ℝ)
      (f : ℤ[X]) (hf : f.map (Int.castRingHom ℝ) = ∏ i, (X - C (x i)))
      (k : ℕ) (hk : k ≤ Fintype.card σ) :
      ∃ z : ℤ, MvPolynomial.aeval x (MvPolynomial.esymm σ ℤ k) = z := by
    classical
    let m := Fintype.card σ
    have hpoly : f.map (Int.castRingHom ℝ) =
        ((univ.val.map x).map (fun r => X - C r)).prod := by
      simpa only [Finset.prod, Multiset.map_map, Function.comp_def] using hf
    have hV := Multiset.prod_X_sub_C_coeff (univ.val.map x) (k := m - k) (by simp [m])
    have hsub : Fintype.card σ - (m - k) = k := Nat.sub_sub_self hk
    simp only [Multiset.card_map, ← Finset.card_def, Finset.card_univ, ← hpoly, hsub] at hV
    have hc : (f.coeff (m - k) : ℝ) =
        (-1 : ℝ) ^ k * MvPolynomial.aeval x (MvPolynomial.esymm σ ℤ k) := by
      rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
      simpa only [coeff_map, Int.coe_castRingHom] using hV
    refine ⟨(-1 : ℤ) ^ k * f.coeff (m - k), ?_⟩
    have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
      rw [← mul_pow]
      norm_num
    calc MvPolynomial.aeval x (MvPolynomial.esymm σ ℤ k) =
        (-1 : ℝ) ^ k * (f.coeff (m - k) : ℝ) := by
          rw [hc, ← mul_assoc, hsign, one_mul]
      _ = ((-1 : ℤ) ^ k * f.coeff (m - k) : ℤ) := by push_cast; rfl
  -- Evaluate the formal root-deleted polynomial at the actual spectrum.
  have formalNumerator_at_eigs {n : ℕ} (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj] (r : eigs G) :
      (formalNumerator r).map (MvPolynomial.aeval (fun s : eigs G => (s : ℝ))).toRingHom =
        numerator G r := by
    classical
    let : DecidableEq (eigs G) := fun a b => Classical.propDecidable (a = b)
    simp only [formalNumerator, numerator, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, MvPolynomial.aeval_X]
    apply prod_bij (fun (s : eigs G) _ => (s : ℝ))
    · intro s hs
      exact mem_erase.mpr ⟨fun h => (ne_of_mem_erase hs) (Subtype.ext h), s.property⟩
    · intro s hs t ht hst
      exact Subtype.ext hst
    · intro θ hθ
      refine ⟨⟨θ, mem_of_mem_erase hθ⟩, mem_erase.mpr ⟨?_, mem_univ _⟩, rfl⟩
      intro h
      exact (ne_of_mem_erase hθ) (congrArg Subtype.val h)
    · intro s hs
      rfl
  -- Evaluate the integer polynomial at the actual spectrum.
  have formalSum_at_eigs {n : ℕ} (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj] (i j : Fin n) :
      MvPolynomial.aeval (fun s : eigs G => (s : ℝ)) (formalSum G i j) =
        ∑ θ ∈ eigs G, (numerator G θ).discr *
          (aeval (G.adjMatrix ℝ) (numerator G θ) i j) ^ 2 := by
    classical
    rw [← sum_coe_sort (eigs G)]
    simp only [formalSum, map_sum, map_mul, map_pow]
    apply sum_congr rfl
    intro r hr
    have hd := discr_map (MvPolynomial.aeval (fun s : eigs G => (s : ℝ))).toRingHom _
      (formalNumerator_monic r)
    have hb := adj_aeval_map (MvPolynomial.aeval (fun s : eigs G => (s : ℝ))).toRingHom
      G (formalNumerator r) i j
    rw [formalNumerator_at_eigs] at hd hb
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
      congrArg₂ (fun a b => a * b ^ 2) hd.symm hb
  -- Evaluate the symmetric polynomial and recover the scaled mixing entry.
  intro n G _ i j
  obtain ⟨f, hfmonic, hf⟩ := adj_minpoly_integer G
  have hfr : f.map (Int.castRingHom ℝ) = ∏ r : eigs G, (X - C (r : ℝ)) := by
    calc f.map (Int.castRingHom ℝ) =
        (f.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℝ) := by
          rw [Polynomial.map_map]
          rfl
      _ = (minpoly ℚ (G.adjMatrix ℚ)).map (algebraMap ℚ ℝ) := by rw [hf]
      _ = ∏ θ ∈ eigs G, (X - C θ) := adj_minpoly_root_product G
      _ = ∏ r : eigs G, (X - C (r : ℝ)) := (prod_coe_sort _ _).symm
  obtain ⟨z, hz⟩ := symmetric_integer_eval (formalSum (σ := eigs G) G i j)
    (formalSum_symmetric G i j) (fun r : eigs G => (r : ℝ)) (fun k =>
      esymm_integer_eval (fun r : eigs G => (r : ℝ)) f hfr (k.val + 1) (by omega))
  refine ⟨z, ?_⟩
  calc ((minpoly ℚ (G.adjMatrix ℚ)).discr : ℝ) * avgMixing G i j =
      ∑ θ ∈ eigs G, ((minpoly ℚ (G.adjMatrix ℚ)).discr : ℝ) * (idempotent G θ i j) ^ 2 := by
        simp only [avgMixing, eigs, Matrix.sum_apply, Matrix.hadamard_apply,
          mul_sum, pow_two]
    _ = ∑ θ ∈ eigs G, (numerator G θ).discr *
        (aeval (G.adjMatrix ℝ) (numerator G θ) i j) ^ 2 := by
          apply sum_congr rfl
          intro θ hθ
          exact discr_scaled_entry G θ hθ i j
    _ = MvPolynomial.aeval (fun r : eigs G => (r : ℝ)) (formalSum G i j) :=
      (formalSum_at_eigs G i j).symm
    _ = z := hz

#print axioms result
end D5.S3.Quantum.Dynamics.AverageMixingDiscriminantIntegrality
