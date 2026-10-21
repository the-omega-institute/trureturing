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

/-! The sharp product overlap of the flip-conjugate symmetric subspaces. -/

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
  classical
  have hs : Real.sqrt ((d : ℝ) + 1) ≠ 0 := by positivity
  have hq := (scalar_identities d hd).1
  have hr := (scalar_identities d hd).2
  simp only [Fintype.sum_prod_type]
  by_cases hmn : m = n
  · subst n
    simp [φ, div_eq_mul_inv, apply_ite conj, ite_and, mul_add, add_mul,
      mul_ite, ite_mul, Finset.sum_add_distrib]
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hden : (d : ℝ) - 1 ≠ 0 := by linarith
    have he : 2 * (d : ℝ) * ‖z d‖ ^ 2 + 2 * ((z d) ^ 2).re = (d : ℝ) + 1 := by
      rw [hq, hr]
      field_simp [hden]
      <;> ring
    have heC : 2 * (d : ℂ) * ((‖z d‖ ^ 2 : ℝ) : ℂ) +
        ((2 * ((z d) ^ 2).re : ℝ) : ℂ) = (d : ℂ) + 1 := by
      exact_mod_cast he
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self,
      ← Complex.add_conj, map_pow] at heC
    have hsC : (Real.sqrt ((d : ℝ) + 1) : ℂ) ^ 2 = (d : ℂ) + 1 := by
      exact_mod_cast Real.sq_sqrt (show 0 ≤ (d : ℝ) + 1 by positivity)
    field_simp [hs]
    linear_combination heC - hsC
  · simp [φ, div_eq_mul_inv, apply_ite conj, ite_and, mul_add, add_mul,
      mul_ite, ite_mul, Finset.sum_add_distrib, hmn, Ne.symm hmn]

private lemma coefficient_normalization (d : ℕ) (hd : 2 ≤ d) (ψ : State d)
    (hψ : UnitVector ψ) (hmem : ψ ∈ H_I d) :
    ∃ α : Fin d → ℂ, UnitVector α ∧ ψ = ∑ n, α n • φ d n := by
  classical
  obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  refine ⟨α, ?_, hα.symm⟩
  have ho : Orthonormal ℂ (fun n : Fin d => WithLp.toLp 2 (φ d n)) := by
    rw [orthonormal_iff_ite]
    intro m n
    simpa only [PiLp.inner_apply, RCLike.inner_apply', PiLp.toLp_apply] using
      basis_orthogonality d hd m n
  have he : WithLp.toLp 2 ψ = ∑ n, α n • WithLp.toLp 2 (φ d n) := by
    rw [← hα, WithLp.toLp_sum]
    exact Finset.sum_congr rfl fun n _ => WithLp.toLp_smul _ _ _
  have hi : inner ℂ (WithLp.toLp 2 ψ) (WithLp.toLp 2 ψ) =
      inner ℂ (WithLp.toLp 2 α) (WithLp.toLp 2 α) := by
    rw [he, ho.inner_sum α α Finset.univ]
    simp only [PiLp.inner_apply, RCLike.inner_apply', PiLp.toLp_apply]
  have hn : ‖WithLp.toLp 2 ψ‖ ^ 2 = ‖WithLp.toLp 2 α‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, hi]
  change ‖WithLp.toLp 2 α‖ = 1
  change ‖WithLp.toLp 2 ψ‖ = 1 at hψ
  nlinarith [norm_nonneg (WithLp.toLp 2 α)]

private lemma conjugate_norm {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    ‖WithLp.toLp 2 (fun i => conj (v i))‖ = ‖WithLp.toLp 2 v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [PiLp.toLp_apply, Complex.norm_conj]

private lemma overlap_conjugate {d : ℕ} (a b c : Fin d → ℂ) (ψ : State d) :
    overlap (fun i => conj (a i)) (fun i => conj (b i)) (fun i => conj (c i))
      (fun p => conj (ψ p)) = conj (overlap a b c ψ) := by
  simp only [overlap, map_sum, map_mul, starRingEnd_self_apply]

private lemma conjugate_overlap_set {d : ℕ} (ψ : State d) :
    overlapSet (fun p => conj (ψ p)) = overlapSet ψ := by
  have hsub (ξ : State d) : overlapSet ξ ⊆ overlapSet (fun p => conj (ξ p)) := by
    rintro t ⟨a, b, c, ha, hb, hc, rfl⟩
    refine ⟨fun i => conj (a i), fun i => conj (b i), fun i => conj (c i),
      (conjugate_norm a).trans ha, (conjugate_norm b).trans hb,
      (conjugate_norm c).trans hc, ?_⟩
    rw [overlap_conjugate, Complex.norm_conj]
  apply Set.Subset.antisymm
  · have h := hsub (fun p => conj (ψ p))
    simp only [starRingEnd_self_apply] at h
    exact h
  · exact hsub ψ

private lemma conjugate_reduction (d : ℕ) (ψ : State d)
    (hψ : UnitVector ψ) (hmem : ψ ∈ H_Ibar d) :
    ∃ ξ : State d, UnitVector ξ ∧ ξ ∈ H_I d ∧ overlapSet ψ = overlapSet ξ := by
  classical
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  have hbar (n : Fin d) (p : Fin d × Fin d × Fin d) :
      conj (φbar d n p) = φ d n p := by
    rcases p with ⟨i, j, k⟩
    simp only [φbar, φ, map_div₀, map_add, map_mul, apply_ite conj, map_one, map_zero,
      starRingEnd_self_apply, Complex.conj_ofReal]
  refine ⟨fun p => conj (ψ p), (conjugate_norm ψ).trans hψ, ?_,
    (conjugate_overlap_set ψ).symm⟩
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
  refine ⟨fun n => conj (β n), ?_⟩
  ext p
  have he := congrArg (fun v : State d => conj (v p)) hβ
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hbar] using he

private def overlapForm (d : ℕ) (α A B C : EuclideanSpace ℂ (Fin d)) : ℂ :=
  (conj (z d) * inner ℂ B α * inner ℂ C A +
    z d * inner ℂ C α * inner ℂ B A) / (Real.sqrt ((d : ℝ) + 1) : ℂ)

set_option maxHeartbeats 1000000 in
private lemma coefficient_overlap (d : ℕ) (α a b c : Fin d → ℂ) :
    overlap a b c (∑ n, α n • φ d n) =
      overlapForm d (WithLp.toLp 2 α) (WithLp.toLp 2 (fun i => conj (a i)))
        (WithLp.toLp 2 b) (WithLp.toLp 2 c) := by
  classical
  unfold overlap overlapForm
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, φ, PiLp.inner_apply,
    RCLike.inner_apply', PiLp.toLp_apply]
  simp [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_div,
    div_eq_mul_inv, mul_add, add_mul, ite_and, mul_ite, ite_mul,
    mul_comm, mul_left_comm, mul_assoc]
  rw [Finset.sum_comm]

private lemma overlap_transport (d : ℕ) [NeZero d]
    (α : Fin d → ℂ) (hα : UnitVector α) :
    overlapSet (∑ n, α n • φ d n) = overlapSet (φ d 0) := by
  classical
  have hsub (U : EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d))
      (γ : Fin d → ℂ) : overlapSet (∑ n, γ n • φ d n) ⊆
        overlapSet (∑ n, (U (WithLp.toLp 2 γ)) n • φ d n) := by
    rintro t ⟨a, b, c, ha, hb, hc, rfl⟩
    refine ⟨fun i => conj ((U (WithLp.toLp 2 (fun j => conj (a j)))) i),
      fun i => (U (WithLp.toLp 2 b)) i, fun i => (U (WithLp.toLp 2 c)) i,
      ?_, ?_, ?_, ?_⟩
    · change ‖WithLp.toLp 2 (fun i => conj ((U (WithLp.toLp 2
        (fun j => conj (a j)))) i))‖ = 1
      rw [conjugate_norm]
      change ‖U (WithLp.toLp 2 (fun j => conj (a j)))‖ = 1
      rw [U.norm_map, conjugate_norm]
      exact ha
    · change ‖U (WithLp.toLp 2 b)‖ = 1
      rw [U.norm_map]
      exact hb
    · change ‖U (WithLp.toLp 2 c)‖ = 1
      rw [U.norm_map]
      exact hc
    · rw [coefficient_overlap, coefficient_overlap]
      have hA : WithLp.toLp 2 (fun i => conj (conj
          ((U (WithLp.toLp 2 (fun j => conj (a j)))) i))) =
          U (WithLp.toLp 2 (fun j => conj (a j))) := by
        ext i
        exact starRingEnd_self_apply _
      rw [hA]
      change ‖overlapForm d (WithLp.toLp 2 γ)
          (WithLp.toLp 2 (fun j => conj (a j))) (WithLp.toLp 2 b) (WithLp.toLp 2 c)‖ ^ 2 =
        ‖overlapForm d (U (WithLp.toLp 2 γ))
          (U (WithLp.toLp 2 (fun j => conj (a j))))
          (U (WithLp.toLp 2 b)) (U (WithLp.toLp 2 c))‖ ^ 2
      simp only [overlapForm, U.inner_map_map]
  have ho : Orthonormal ℂ (({0} : Set (Fin d)).domRestrict
      (fun _ : Fin d => WithLp.toLp 2 α)) := by
    letI : Subsingleton ({0} : Set (Fin d)) := Set.subsingleton_singleton.coe_sort
    rw [orthonormal_subsingleton_iff]
    intro i
    exact hα
  obtain ⟨basis, hbasis⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (ι := Fin d) (v := fun _ : Fin d => WithLp.toLp 2 α) (s := {0}) (by simp) ho
  let U := basis.repr
  have hU : U (WithLp.toLp 2 α) = EuclideanSpace.single 0 (1 : ℂ) := by
    change basis.repr (WithLp.toLp 2 α) = _
    rw [← hbasis 0 (by simp)]
    exact basis.repr_self 0
  have hz : (∑ n, (U (WithLp.toLp 2 α)) n • φ d n) = φ d 0 := by
    rw [hU]
    simp [PiLp.single_apply, ite_smul]
  apply Set.Subset.antisymm
  · rw [← hz]
    exact hsub U α
  · have h := hsub U.symm (fun n => (U (WithLp.toLp 2 α)) n)
    change overlapSet (∑ n, (U (WithLp.toLp 2 α)) n • φ d n) ⊆
      overlapSet (∑ n, (U.symm (U (WithLp.toLp 2 α))) n • φ d n) at h
    rw [U.symm_apply_apply, hz] at h
    exact h

private lemma sharp_upper (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (a b c : Fin d → ℂ) (ha : UnitVector a) (hb : UnitVector b) (hc : UnitVector c) :
    ‖overlap a b c (φ d 0)‖ ^ 2 ≤ sharpValue d := by
  sorry

private lemma sharp_attainment (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    sharpValue d ∈ overlapSet (φ d 0) := by
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
  rw [overlap_transport d α hα, basis_supremum d hd]

theorem result : claim := by
  intro d hd ψ hψ hmem
  rcases hmem with hmem | hmem
  · exact subspace_measure d hd ψ hψ hmem
  · obtain ⟨ξ, hξ, hξmem, heq⟩ := conjugate_reduction d ψ hψ hmem
    change 1 - sSup (overlapSet ψ) = _
    rw [heq]
    exact subspace_measure d hd ξ hξ hξmem

end D5.S3.Quantum.Entanglement.GeometricMeasure.FlipConjugateGeometricMeasure
