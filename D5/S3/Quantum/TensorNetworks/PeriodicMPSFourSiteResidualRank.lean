/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualRank
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A degree-eight coefficient minor bounds the dimension of the residual quotient. -/

import D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteInterpolation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! A certificate of codimension one in the degree-eight ternary polynomial space. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteResidualRank

open MvPolynomial
open scoped BigOperators

/-- The first two exponents of a ternary monomial of total degree `n`. -/
abbrev Exponent (n : ℕ) := {p : Fin (n + 1) × Fin (n + 1) // p.1.val + p.2.val ≤ n}

/-- The third exponent is determined by the total degree. -/
noncomputable def Exponent.toFinsupp {n : ℕ} (p : Exponent n) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![p.val.1.val, p.val.2.val, n - (p.val.1.val + p.val.2.val)]

private lemma exponent_cover {n : ℕ} (d : Fin 3 →₀ ℕ) (hd : d 0 + d 1 + d 2 = n) :
    ∃ p : Exponent n, p.toFinsupp = d := by
  refine ⟨⟨(⟨d 0, by omega⟩, ⟨d 1, by omega⟩), by change d 0 + d 1 ≤ n; omega⟩, ?_⟩
  ext i
  fin_cases i
  · simp [Exponent.toFinsupp]
  · simp [Exponent.toFinsupp]
  · simp [Exponent.toFinsupp]; omega

private lemma degree_sum (d : Fin 3 →₀ ℕ) :
    Finsupp.weight (fun _ : Fin 3 => (1 : ℕ)) d = d 0 + d 1 + d 2 := by
  rw [Finsupp.weight_apply]
  simp only [smul_eq_mul, mul_one]
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_three]

/-- The square matrix reads selected degree-eight coefficients of the ideal polynomials. -/
noncomputable def coefficientMinor {R : Type*} [CommRing R]
    (f : Fin 44 → MvPolynomial (Fin 3) R) (p : Fin 44 → Exponent 8) :
    Matrix (Fin 44) (Fin 44) R :=
  Matrix.of fun i j => (f j).coeff (p i).toFinsupp

/-- Coefficient selection commutes with reduction or extension of the ground ring. -/
theorem map_coefficientMinor {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (f : Fin 44 → MvPolynomial (Fin 3) R) (p : Fin 44 → Exponent 8) :
    g.mapMatrix (coefficientMinor f p) = coefficientMinor (fun i => map g (f i)) p := by
  ext i j
  exact (coeff_map g (f j) (p i).toFinsupp).symm

/-- The degree-eight quotient has dimension at most one if 44 degree-eight
polynomials in the ideal have an invertible square coefficient submatrix. -/
theorem quotient_finrank_le_of_minor {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin 3) K)) (f : Fin 44 → MvPolynomial (Fin 3) K)
    (hf : ∀ i, (f i).IsHomogeneous 8) (hi : ∀ i, f i ∈ I) (p : Fin 44 → Exponent 8)
    (hdet : (coefficientMinor f p).det ≠ 0) :
    Module.finrank K (LinearMap.range
      ((Ideal.Quotient.mkₐ K I).toLinearMap.comp
        (homogeneousSubmodule (Fin 3) K 8).subtype)) ≤ 1 := by
  let S := homogeneousSubmodule (Fin 3) K 8
  let : Module.Finite K S := Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 3) K 8)
  let q := (Ideal.Quotient.mkₐ K I).toLinearMap.comp S.subtype
  let read (n : Type) (e : n → Exponent 8) : S →ₗ[K] (n → K) :=
    LinearMap.pi fun i => (lcoeff K (e i).toFinsupp).comp S.subtype
  have hinj : Function.Injective (read (Exponent 8) id) := by
    intro a b hab
    apply Subtype.ext
    ext d
    by_cases hsum : d 0 + d 1 + d 2 = 8
    · obtain ⟨e, rfl⟩ := exponent_cover d hsum
      exact congr_fun hab e
    · have hn (c : S) : c.val.coeff d = 0 := by
        by_contra hne
        have hc := c.property hne
        exact hsum ((degree_sum d).symm.trans hc)
      rw [hn a, hn b]
  have hdim : Module.finrank K S ≤ 45 := by
    calc
      Module.finrank K S ≤ Module.finrank K (Exponent 8 → K) :=
        (read (Exponent 8) id).finrank_le_finrank_of_injective hinj
      _ = 45 := by rw [Module.finrank_pi]; decide
  let u (i : Fin 44) : LinearMap.ker q := ⟨⟨f i, hf i⟩,
    Ideal.Quotient.eq_zero_iff_mem.mpr (hi i)⟩
  have hind : LinearIndependent K u := by
    apply LinearIndependent.of_comp ((read (Fin 44) p).comp (LinearMap.ker q).subtype)
    exact Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hker : 44 ≤ Module.finrank K (LinearMap.ker q) := by
    simpa only [Fintype.card_fin] using hind.fintype_card_le_finrank
  have hdim' := q.finrank_range_add_finrank_ker
  change Module.finrank K (LinearMap.range q) ≤ 1
  omega

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteResidualRank
