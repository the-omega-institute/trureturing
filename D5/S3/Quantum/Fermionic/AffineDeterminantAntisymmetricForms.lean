/- GID: D5/S3/Quantum/Fermionic/AffineDeterminantAntisymmetricForms
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/AffineDeterminantAntisymmetricForms
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Low-degree alternating polynomials in vector variables are affine determinants. -/

import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

noncomputable section

namespace D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms

open MvPolynomial Finset

/-- A permutation of vector variables preserves the coordinate within each vector. -/
def blockPerm {r d : ℕ} (σ : Equiv.Perm (Fin r)) :
    Equiv.Perm (Fin r × Fin d) :=
  Equiv.prodCongr σ (Equiv.refl _)

/-- Alternation under permutations of the vector variables. -/
def IsAlternating {r d : ℕ} (f : MvPolynomial (Fin r × Fin d) ℂ) : Prop :=
  ∀ σ : Equiv.Perm (Fin r),
    rename (blockPerm σ) f = (((Equiv.Perm.sign σ : ℤ) : ℂ)) • f

/-- The determinant with columns the differences from the first point. -/
def affineDet (d : ℕ) : MvPolynomial (Fin (d + 1) × Fin d) ℂ :=
  Matrix.det (fun j k : Fin d => X (k.succ, j) - X (0, j))

/-- Vanishing for every first point forces affine dimension at most `d - 2`. -/
def IsNondegenerate (d : ℕ) (ω : (Fin (d + 1) → Fin d → ℂ) → ℂ) : Prop :=
  ∀ x : Fin d → (Fin d → ℂ),
    (∀ x₀, ω (Fin.cons x₀ x) = 0) →
      Module.finrank ℂ (affineSpan ℂ (Set.range x)).direction ≤ d - 2

private def canonical (d : ℕ) : (Fin (d + 1) × Fin d) →₀ ℕ :=
  ∑ k : Fin d, Finsupp.single (k.succ, k) 1

private lemma coeff_permuted {r d : ℕ} {f : MvPolynomial (Fin r × Fin d) ℂ}
    (ha : IsAlternating f) (σ : Equiv.Perm (Fin r)) (m : (Fin r × Fin d) →₀ ℕ) :
    f.coeff (m.mapDomain (blockPerm σ)) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * f.coeff m := by
  sorry

private lemma equal_rows_coeff_zero {r d : ℕ}
    {f : MvPolynomial (Fin r × Fin d) ℂ} (ha : IsAlternating f)
    (m : (Fin r × Fin d) →₀ ℕ) {a b : Fin r} (hab : a ≠ b)
    (he : ∀ j, m (a, j) = m (b, j)) : f.coeff m = 0 := by
  sorry

private lemma support_rows_distinct {r d : ℕ}
    {f : MvPolynomial (Fin r × Fin d) ℂ} (ha : IsAlternating f)
    {m : (Fin r × Fin d) →₀ ℕ} (hm : m ∈ f.support) :
    Function.Injective (fun i : Fin r => fun j : Fin d => m (i, j)) := by
  sorry

private lemma distinct_rows_orbit {d : ℕ}
    (m : (Fin (d + 1) × Fin d) →₀ ℕ)
    (hi : Function.Injective (fun i : Fin (d + 1) => fun j : Fin d => m (i, j)))
    (ht : m.sum (fun _ n => n) ≤ d) :
    ∃ σ : Equiv.Perm (Fin (d + 1)),
      (canonical d).mapDomain (blockPerm σ) = m := by
  sorry

private lemma support_orbit {d : ℕ}
    {f : MvPolynomial (Fin (d + 1) × Fin d) ℂ}
    (ha : IsAlternating f) (hd : f.totalDegree ≤ d)
    {m : (Fin (d + 1) × Fin d) →₀ ℕ} (hm : m ∈ f.support) :
    ∃ σ : Equiv.Perm (Fin (d + 1)),
      (canonical d).mapDomain (blockPerm σ) = m := by
  exact distinct_rows_orbit m (support_rows_distinct ha hm) ((le_totalDegree hm).trans hd)

private lemma too_many_rows {d r : ℕ} (hr : d + 2 ≤ r)
    (f : MvPolynomial (Fin r × Fin d) ℂ) (ha : IsAlternating f)
    (hd : f.totalDegree ≤ d) : f = 0 := by
  sorry

private lemma affineDet_alternating (d : ℕ) : IsAlternating (affineDet d) := by
  sorry

private lemma affineDet_degree (d : ℕ) : (affineDet d).totalDegree ≤ d := by
  sorry

private lemma affineDet_coeff (d : ℕ) : (affineDet d).coeff (canonical d) = 1 := by
  sorry

private lemma coefficient_determines {d : ℕ}
    (f : MvPolynomial (Fin (d + 1) × Fin d) ℂ)
    (ha : IsAlternating f) (hd : f.totalDegree ≤ d) :
    f = f.coeff (canonical d) • affineDet d := by
  sorry

private lemma affineDet_nondegenerate (d : ℕ) (hd : 2 ≤ d) :
    IsNondegenerate d (fun y => eval (fun p => y p.1 p.2) (affineDet d)) := by
  sorry

/-- Low-degree alternation vanishes with too many vectors, and is otherwise the affine determinant. -/
theorem result :
    (∀ d r, d + 2 ≤ r → ∀ f : MvPolynomial (Fin r × Fin d) ℂ,
      IsAlternating f → f.totalDegree ≤ d → f = 0) ∧
    (∀ d, IsAlternating (affineDet d) ∧ (affineDet d).totalDegree ≤ d) ∧
    (∀ d (f : MvPolynomial (Fin (d + 1) × Fin d) ℂ),
      IsAlternating f → f.totalDegree ≤ d → ∃ c : ℂ, f = c • affineDet d) ∧
    (∀ d, 2 ≤ d →
      IsNondegenerate d (fun y => eval (fun p => y p.1 p.2) (affineDet d))) := by
  refine ⟨fun d r hr f ha hd => too_many_rows hr f ha hd,
    fun d => ⟨affineDet_alternating d, affineDet_degree d⟩,
    fun d f ha hd => ⟨f.coeff (canonical d), coefficient_determines f ha hd⟩,
    affineDet_nondegenerate⟩

end D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms
