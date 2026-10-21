/- GID: D5/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/GeometricMeasure/FlipConjugateGeometricMeasure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The geometric measure of the flip-conjugate symmetric subspaces. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic

noncomputable section

open scoped BigOperators ComplexConjugate

namespace D5.S3.Quantum.Entanglement.GeometricMeasure.FlipConjugateGeometricMeasure

abbrev State (d : ℕ) := Fin d × Fin d × Fin d → ℂ

def UnitVector {ι : Type*} [Fintype ι] (v : ι → ℂ) : Prop :=
  ‖WithLp.toLp 2 v‖ = 1

def z (d : ℕ) : ℂ :=
  (1 + Complex.I * (Real.sqrt (((d : ℝ) + 1) / ((d : ℝ) - 1)) : ℂ)) / 2

def φ (d : ℕ) (n : Fin d) : State d := fun (i, j, k) =>
  (conj (z d) * (if j = n ∧ k = i then 1 else 0) +
    z d * (if j = i ∧ k = n then 1 else 0)) / (Real.sqrt ((d : ℝ) + 1) : ℂ)

def φbar (d : ℕ) (n : Fin d) : State d := fun (i, j, k) =>
  (z d * (if j = n ∧ k = i then 1 else 0) +
    conj (z d) * (if j = i ∧ k = n then 1 else 0)) /
    (Real.sqrt ((d : ℝ) + 1) : ℂ)

def H_I (d : ℕ) : Submodule ℂ (State d) := Submodule.span ℂ (Set.range (φ d))

def H_Ibar (d : ℕ) : Submodule ℂ (State d) := Submodule.span ℂ (Set.range (φbar d))

def overlap {d : ℕ} (a b c : Fin d → ℂ) (ψ : State d) : ℂ :=
  ∑ i, ∑ j, ∑ k, conj (a i) * conj (b j) * conj (c k) * ψ (i, j, k)

def overlapSet {d : ℕ} (ψ : State d) : Set ℝ :=
  {t | ∃ a b c : Fin d → ℂ, UnitVector a ∧ UnitVector b ∧ UnitVector c ∧
    t = ‖overlap a b c ψ‖ ^ 2}

def G {d : ℕ} (ψ : State d) : ℝ := 1 - sSup (overlapSet ψ)

def sharpValue (d : ℕ) : ℝ :=
  (d : ℝ) ^ 2 / (((d : ℝ) ^ 2 - 1) * ((d : ℝ) + 1))

def claim : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ ψ : State d,
    UnitVector ψ → ψ ∈ H_I d ∨ ψ ∈ H_Ibar d → G ψ = 1 - sharpValue d

private lemma scalar_identities (d : ℕ) (hd : 2 ≤ d) :
    ‖z d‖ ^ 2 = (d : ℝ) / (2 * ((d : ℝ) - 1)) ∧
    ((z d) ^ 2).re = -1 / (2 * ((d : ℝ) - 1)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 0 < (d : ℝ) - 1 := by linarith
  have hden : (d : ℝ) - 1 ≠ 0 := ne_of_gt hd1
  have hs := Real.sq_sqrt (show 0 ≤ ((d : ℝ) + 1) / ((d : ℝ) - 1) by positivity)
  have hs' := (eq_div_iff hden).mp hs
  have hr : (z d).re = 1 / 2 := by
    norm_num [z, Complex.div_re, Complex.mul_re]
  have hi : (z d).im = Real.sqrt (((d : ℝ) + 1) / ((d : ℝ) - 1)) / 2 := by
    norm_num [z, Complex.div_im, Complex.mul_im]
  constructor
  · rw [Complex.sq_norm, Complex.normSq_apply, hr, hi]
    field_simp
    nlinarith [hs']
  · rw [pow_two, Complex.mul_re, hr, hi]
    field_simp
    nlinarith [hs']

private lemma basis_orthogonality (d : ℕ) (hd : 2 ≤ d) (m n : Fin d) :
    (∑ p, conj (φ d m p) * φ d n p) = if m = n then 1 else 0 := by
  sorry

private lemma coefficient_normalization (d : ℕ) (hd : 2 ≤ d) (ψ : State d)
    (hψ : UnitVector ψ) (hmem : ψ ∈ H_I d) :
    ∃ α : Fin d → ℂ, UnitVector α ∧ ψ = ∑ n, α n • φ d n := by
  sorry

private lemma overlap_transport (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (α : Fin d → ℂ) (hα : UnitVector α) :
    overlapSet (∑ n, α n • φ d n) = overlapSet (φ d 0) := by
  sorry

private lemma sharp_upper (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (a b c : Fin d → ℂ) (ha : UnitVector a) (hb : UnitVector b) (hc : UnitVector c) :
    ‖overlap a b c (φ d 0)‖ ^ 2 ≤ sharpValue d := by
  sorry

private lemma sharp_attainment (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    sharpValue d ∈ overlapSet (φ d 0) := by
  sorry

private lemma conjugate_reduction (d : ℕ) (hd : 2 ≤ d) (ψ : State d)
    (hψ : UnitVector ψ) (hmem : ψ ∈ H_Ibar d) :
    ∃ ξ : State d, UnitVector ξ ∧ ξ ∈ H_I d ∧ overlapSet ψ = overlapSet ξ := by
  sorry

private lemma basis_supremum (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    sSup (overlapSet (φ d 0)) = sharpValue d := by
  apply IsGreatest.csSup_eq
  refine ⟨sharp_attainment d hd, ?_⟩
  rintro t ⟨a, b, c, ha, hb, hc, rfl⟩
  exact sharp_upper d hd a b c ha hb hc

private lemma subspace_measure (d : ℕ) (hd : 2 ≤ d) (ψ : State d)
    (hψ : UnitVector ψ) (hmem : ψ ∈ H_I d) : G ψ = 1 - sharpValue d := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨α, hα, rfl⟩ := coefficient_normalization d hd ψ hψ hmem
  unfold G
  rw [overlap_transport d hd α hα, basis_supremum d hd]

theorem result : claim := by
  intro d hd ψ hψ hmem
  rcases hmem with hmem | hmem
  · exact subspace_measure d hd ψ hψ hmem
  · obtain ⟨ξ, hξ, hξmem, heq⟩ := conjugate_reduction d hd ψ hψ hmem
    change 1 - sSup (overlapSet ψ) = _
    rw [heq]
    exact subspace_measure d hd ξ hξ hξmem

end D5.S3.Quantum.Entanglement.GeometricMeasure.FlipConjugateGeometricMeasure
