/- GID: D5/S3/Quantum/Measurement/Auric/ProjectionSpectralTransport
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/ProjectionSpectralTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rectangular spectral transport and isometric frames for finite Hermitian projections. -/

import D5.S3.Quantum.Measurement.Auric.ProjectionFrames
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! Spectra of rectangular products and rectangular frames for Hermitian projections. -/

namespace D5.S3.Quantum.Measurement.Auric

open _root_.Matrix Polynomial
open scoped BigOperators ComplexOrder Matrix
open D5.S3.Quantum.Measurement.Auric.ProjectionFrames (exists_complementary_frames)

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

/-- Zero-insensitive spectral transport for rectangular products. Additional zero eigenvalues contribute zero. -/
theorem spectralSum_mul_reverse (f : ℝ → ℝ) (hf : f 0 = 0)
    (A : Matrix ι n ℂ) (B : Matrix n ι ℂ)
    (hAB : (A * B).IsHermitian) (hBA : (B * A).IsHermitian) :
    (∑ i, f (hAB.eigenvalues i)) = ∑ i, f (hBA.eigenvalues i) := by
  have h := congrArg Polynomial.roots (Matrix.charpoly_mul_comm' A B)
  rw [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
    (Matrix.charpoly_monic _).ne_zero),
    Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Matrix.charpoly_monic _).ne_zero), Polynomial.roots_X_pow,
    Polynomial.roots_X_pow, hAB.roots_charpoly_eq_eigenvalues,
    hBA.roots_charpoly_eq_eigenvalues] at h
  have hs := congrArg (fun t : Multiset ℂ => (t.map (f ∘ RCLike.re)).sum) h
  simpa only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul,
    Multiset.sum_nsmul, Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_map,
    Function.comp_def, RCLike.zero_re, RCLike.ofReal_re, hf, nsmul_zero, zero_add, Finset.sum]
    using hs

theorem exists_projection_frame {d : ℕ} {Q : Matrix ι ι ℂ}
    (hQ : Q.IsHermitian) (hidem : Q * Q = Q) (hRank : Q.rank = d) :
    ∃ V : Matrix ι (Fin d) ℂ, Vᴴ * V = 1 ∧ V * Vᴴ = Q := by
  classical
  by_cases hzero : Q = 0
  · have hd : d = 0 := by simpa [hzero] using hRank.symm
    subst hd
    exact ⟨0, by ext i; exact Fin.elim0 i, by simp [hzero]⟩
  by_cases hone : Q = 1
  · subst Q
    rw [Matrix.rank_one] at hRank
    subst d
    let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
    refine ⟨(1 : Matrix ι ι ℂ).submatrix id e, ?_, ?_⟩
    · rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
        ← Matrix.submatrix_mul _ _ e id e Function.bijective_id, Matrix.one_mul]
      exact Matrix.submatrix_one_equiv e
    · rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
        Matrix.submatrix_mul_equiv _ _ id e id, Matrix.one_mul, Matrix.submatrix_id_id]
  obtain ⟨k, l, _, _, _, V, _, hV, _, hVQ, _⟩ :=
    exists_complementary_frames Q hQ hidem hzero hone
  have hRankQ : Q.rank = k := by
    rw [← hVQ, Matrix.rank_self_mul_conjTranspose, ← Matrix.rank_conjTranspose_mul_self V,
      hV, Matrix.rank_one, Fintype.card_fin]
  have hk : d = k := hRank.symm.trans hRankQ
  exact hk.symm ▸ ⟨V, hV, hVQ⟩

end D5.S3.Quantum.Measurement.Auric
