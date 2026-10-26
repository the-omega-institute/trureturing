/- GID: D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Perfect homogeneous one-generator extensions exist exactly at differential order one. -/

import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

noncomputable section

namespace D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra

open MvPolynomial
open scoped BigOperators

/-- All multi-indices of total order at most `k`, each occurring once. -/
def I (d k : ℕ) : Finset (Fin d →₀ ℕ) :=
  (Finsupp.finite_of_degree_le (σ := Fin d) k).toFinset

/-- Ordinary iterated partial differentiation, in increasing coordinate order. -/
def pderivMulti {K : Type*} [Field K] {d : ℕ} (α : Fin d →₀ ℕ) :
    MvPolynomial (Fin d) K →ₗ[K] MvPolynomial (Fin d) K :=
  ((List.finRange d).map fun i => (pderiv i).toLinearMap ^ α i).prod

/-- The complete generalized Wronskian, with rows indexed by differential multi-indices. -/
def wronskian {K : Type*} [Field K] {d k : ℕ}
    (f : I d k → MvPolynomial (Fin d) K) : MvPolynomial (Fin d) K :=
  Matrix.det (fun α β => pderivMulti α.val (f β))

/-- The sum of all polynomials of total degree at most `k` and the line through `p`. -/
def lonely {K : Type*} [Field K] {d k : ℕ} (p : MvPolynomial (Fin d) K) :
    Submodule K (MvPolynomial (Fin d) K) :=
  restrictTotalDegree (Fin d) K k ⊔ K ∙ p

/-- Perfectness means that all Wronskian brackets span the entire polynomial subspace. -/
def perfect {K : Type*} [Field K] {d k : ℕ} (p : MvPolynomial (Fin d) K) : Prop :=
  Submodule.span K {w | ∃ f : I d k → MvPolynomial (Fin d) K,
    (∀ β, f β ∈ lonely (k := k) p) ∧ wronskian f = w} = lonely (k := k) p

/-- The source question over every characteristic-zero field and in every base dimension. -/
def claim : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (d k : ℕ), 2 ≤ d → 1 ≤ k →
    ((∃ p : MvPolynomial (Fin d) K,
      p ≠ 0 ∧ p.IsHomogeneous (k + 1) ∧ perfect (k := k) p) ↔ k = 1)

private lemma bracket_mem_span_basis {K : Type*} [Field K] {d k : ℕ}
    (p : MvPolynomial (Fin d) K) (f : I d k → MvPolynomial (Fin d) K)
    (hf : ∀ β, f β ∈ lonely (k := k) p) :
    wronskian f ∈ Submodule.span K {w | ∃ b : I d k → Option (I d k),
      wronskian (fun β => (b β).elim p (fun α => monomial α.val 1)) = w} := by
  sorry

private lemma wronskian_homogeneous {K : Type*} [Field K] {d k : ℕ}
    (f : I d k → MvPolynomial (Fin d) K) (n : I d k → ℕ)
    (hf : ∀ β, (f β).IsHomogeneous (n β)) :
    (wronskian f).IsHomogeneous ((∑ β, n β) - ∑ α : I d k, α.val.degree) := by
  sorry

private lemma upper_order_obstruction {K : Type*} [Field K] [CharZero K]
    {d k : ℕ} (hd : 2 ≤ d) (hk : 2 ≤ k) (p : MvPolynomial (Fin d) K)
    (hp : p ≠ 0) (hh : p.IsHomogeneous (k + 1))
    (hb : ∀ f : I d k → MvPolynomial (Fin d) K,
      (∀ β, f β ∈ lonely (k := k) p) →
      wronskian f ∈ Submodule.span K {w | ∃ b : I d k → Option (I d k),
        wronskian (fun β => (b β).elim p (fun α => monomial α.val 1)) = w})
    (hw : ∀ (f : I d k → MvPolynomial (Fin d) K) (n : I d k → ℕ),
      (∀ β, (f β).IsHomogeneous (n β)) →
      (wronskian f).IsHomogeneous ((∑ β, n β) - ∑ α : I d k, α.val.degree)) :
    ¬ perfect (k := k) p := by
  sorry

private lemma quadratic_construction {K : Type*} [Field K] [CharZero K]
    {d : ℕ} (hd : 2 ≤ d)
    (hb : ∀ (p : MvPolynomial (Fin d) K) (f : I d 1 → MvPolynomial (Fin d) K),
      (∀ β, f β ∈ lonely (k := 1) p) →
      wronskian f ∈ Submodule.span K {w | ∃ b : I d 1 → Option (I d 1),
        wronskian (fun β => (b β).elim p (fun α => monomial α.val 1)) = w}) :
    ∃ p : MvPolynomial (Fin d) K,
      p ≠ 0 ∧ p.IsHomogeneous 2 ∧ perfect (k := 1) p := by
  sorry

 theorem result : claim := by
  intro K _ _ d k hd hk
  constructor
  · rintro ⟨p, hp, hh, hperfect⟩
    by_contra hne
    have hk2 : 2 ≤ k := by omega
    exact upper_order_obstruction hd hk2 p hp hh
      (bracket_mem_span_basis p) wronskian_homogeneous hperfect
  · rintro rfl
    exact quadratic_construction hd bracket_mem_span_basis

end D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra
