/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairIntegralPolynomial
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairIntegralPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual ideal-graph integrality forces full integer tensor characteristic factorization. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.RepeatedPairProductSpectrum
import Mathlib.Algebra.Polynomial.Splits

/-! Source: repeated-pair-modular, PR9 6d491f77b35dec808fc777b69939c56cdae5dc02.
The integer polynomial here is that of the full subset-index operator.
Its integer roots are deduced from actual ideal-graph integrality through
nonzero eigenvectors and the existing weighted graph lift. No integer-root
premise or compressed scalar operator replaces the graph hypothesis. -/
set_option autoImplicit false
set_option maxRecDepth 2000
noncomputable section
open Finset Matrix Polynomial
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.RepeatedPairIntegralPolynomial
open RepeatedPairSupport RepeatedPairProductSpectrum
open IdealIntersectionSupport IdealIntersectionObstructions
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Full ring-valued operator reduction, before any spectral hypothesis. -/
theorem map_operator {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : R) (k : ι → R) :
    (K a k).map f=K (f a) (fun i => f (k i)) := by
  ext T U
  simp only [K, Matrix.map_apply, Matrix.add_apply, Matrix.diagonal_apply,
    Matrix.smul_apply, smul_eq_mul, diagonalFactor, disjointKernel,
    apply_ite, map_add, map_mul, map_zero, map_one, map_prod]
  split_ifs <;> rfl

/-- Positive weights give equality of full characteristic polynomials. -/
theorem symmetric_charpoly (a : ℝ) (k : ι → ℝ) (hk : ∀ i, 0 < k i) :
    (symmetricK a k).charpoly=(K a k).charpoly := by
  have hD : (diagonal (rootWeight k)).det ≠ 0 := by
    rw [det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro T _
    apply (Real.sqrt_pos.mpr _).ne'
    exact Finset.prod_pos (fun i _ => hk i)
  apply Matrix.charpoly_eq_of_mul_eq_mul hD
  exact (intertwine a k hk).symm

/-- Every eigenvalue, with multiplicity, comes from the actual graph.
The conclusion is an integer factorization, not merely rational splitting. -/
theorem actual_factorization (p : Fin 2 ⊕ ι → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (a : ℕ) (k : ι → ℕ) (ha : 0 < a) (hk : ∀ i, 0 < k i)
    (H : ActualLaplacianIntegral (modulus p (pairExponents a k))) :
    ∃ z : Finset ι → ℤ,
      (K (a : ℤ) (fun i => (k i : ℤ))).charpoly=∏ i, (X-C (z i)) := by
  let kr : ι → ℝ := fun i => k i
  have hkr (i : ι) : 0 < kr i := by
    dsimp only [kr]
    exact_mod_cast hk i
  let hM := hermitian (a : ℝ) kr
  have hall (T : Finset ι) : ∃ z : ℤ, hM.eigenvalues T=z := by
    let v : Finset ι → ℝ := hM.eigenvectorBasis T
    have hv : v ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.mpr
      (hM.eigenvectorBasis.orthonormal.ne_zero T)
    have hE : symmetricK (a : ℝ) kr*ᵥv=hM.eigenvalues T • v :=
      hM.mulVec_eigenvectorBasis T
    obtain ⟨h,hh,hK⟩ := eigenpair_transport (a : ℝ) kr hkr _ v hv hE
    have hactual := actual_paired_eigenvalue p hp hinj a k ha hk _ h hh hK
    obtain ⟨z,hz⟩ := H _ hactual
    refine ⟨(((a+1)^2*(∏ i, (k i+1))-2 : ℕ) : ℤ)+1-z,?_⟩
    push_cast
    linarith
  choose z hz using hall
  refine ⟨z,?_⟩
  have hc : ((K (a : ℤ) (fun i => (k i : ℤ))).charpoly).map (Int.castRingHom ℝ)=
      ∏ i, (X-C ((z i : ℤ) : ℝ)) := by
    rw [← Matrix.charpoly_map,map_operator]
    change (K (a : ℝ) kr).charpoly=_
    rw [← symmetric_charpoly (a : ℝ) kr hkr,hM.charpoly_eq]
    simp [hz]
  apply Polynomial.map_injective (Int.castRingHom ℝ) (Int.cast_injective (α := ℝ))
  rw [hc]
  simp [Polynomial.map_prod]

/-- Splitting survives every characteristic reduction, with multiplicities. -/
theorem actual_reduction_splits (p : Fin 2 ⊕ ι → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (a : ℕ) (k : ι → ℕ) (ha : 0 < a) (hk : ∀ i, 0 < k i)
    (H : ActualLaplacianIntegral (modulus p (pairExponents a k)))
    {R : Type*} [CommRing R] :
    (K (a : R) (fun i => (k i : R))).charpoly.Splits := by
  obtain ⟨z,hz⟩ := actual_factorization p hp hinj a k ha hk H
  have hs : (K (a : ℤ) (fun i => (k i : ℤ))).charpoly.Splits := by
    rw [hz]
    exact Polynomial.Splits.prod (fun _ _ => Polynomial.Splits.X_sub_C _)
  have hh := hs.map (Int.castRingHom R)
  rw [← Matrix.charpoly_map,map_operator] at hh
  simpa using hh

end D5.S3.Combinatorics.SpectralGraph.RepeatedPairIntegralPolynomial
