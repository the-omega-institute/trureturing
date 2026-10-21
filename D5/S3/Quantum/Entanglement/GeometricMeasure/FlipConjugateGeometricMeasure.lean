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

private def contraction (d : ℕ) (n : Fin d) (b c : Fin d → ℂ) :
    EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 fun i =>
  conj (z d) * conj (b n) * conj (c i) + z d * conj (c n) * conj (b i)

private lemma contraction_overlap (d : ℕ) (n : Fin d) (a b c : Fin d → ℂ) :
    overlap a b c (φ d n) = inner ℂ (WithLp.toLp 2 a) (contraction d n b c) /
      (Real.sqrt ((d : ℝ) + 1) : ℂ) := by
  classical
  have he : (∑ j, (EuclideanSpace.single n (1 : ℂ)) j • φ d j) = φ d n := by
    simp [PiLp.single_apply, ite_smul]
  rw [← he, coefficient_overlap]
  unfold overlapForm
  change (_ * inner ℂ (WithLp.toLp 2 b) (EuclideanSpace.single n 1) * _ +
    _ * inner ℂ (WithLp.toLp 2 c) (EuclideanSpace.single n 1) * _) / _ = _
  rw [EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_right]
  simp only [PiLp.toLp_apply, one_mul, PiLp.inner_apply, RCLike.inner_apply',
    contraction, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
  congr 1
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

private def coordinateTail (d : ℕ) (n : Fin d) (b : Fin d → ℂ) :
    EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 fun i => if i = n then 0 else b i

private lemma tail_norm_split (d : ℕ) (n : Fin d) (b : Fin d → ℂ) :
    ‖WithLp.toLp 2 b‖ ^ 2 = ‖b n‖ ^ 2 + ‖coordinateTail d n b‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [coordinateTail, PiLp.toLp_apply]
  rw [← Finset.add_sum_erase Finset.univ (fun i => ‖b i‖ ^ 2) (Finset.mem_univ n)]
  congr 1
  rw [← Finset.sum_erase_add Finset.univ
    (fun i => ‖if i = n then (0 : ℂ) else b i‖ ^ 2) (Finset.mem_univ n)]
  simp only [ite_true, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [if_neg (Finset.mem_erase.mp hi).1]

private lemma contraction_at_index (d : ℕ) (n : Fin d) (b c : Fin d → ℂ) :
    (contraction d n b c) n = conj (b n) * conj (c n) := by
  have hzsum : conj (z d) + z d = 1 := by
    rw [add_comm, Complex.add_conj]
    norm_num [z, Complex.div_re, Complex.mul_re]
  change conj (z d) * conj (b n) * conj (c n) +
      z d * conj (c n) * conj (b n) = _
  calc
    _ = (conj (z d) + z d) * conj (b n) * conj (c n) := by ring
    _ = _ := by rw [hzsum, one_mul]

private lemma contraction_bound (d : ℕ) (hd : 2 ≤ d) (n : Fin d)
    (b c : Fin d → ℂ) (hb : UnitVector b) (hc : UnitVector c) :
    ‖contraction d n b c‖ ^ 2 ≤ sharpValue d * ((d : ℝ) + 1) := by
  classical
  let B := coordinateTail d n (fun i => conj (b i))
  let C := coordinateTail d n (fun i => conj (c i))
  let X := (conj (z d) * conj (b n)) • C + (z d * conj (c n)) • B
  let u := ‖b n‖
  let v := ‖c n‖
  let s := ‖B‖
  let t := ‖C‖
  have hB : s ^ 2 = 1 - u ^ 2 := by
    have h := tail_norm_split d n (fun i => conj (b i))
    rw [conjugate_norm, hb, Complex.norm_conj] at h
    change 1 ^ 2 = u ^ 2 + s ^ 2 at h
    linarith
  have hC : t ^ 2 = 1 - v ^ 2 := by
    have h := tail_norm_split d n (fun i => conj (c i))
    rw [conjugate_norm, hc, Complex.norm_conj] at h
    change 1 ^ 2 = v ^ 2 + t ^ 2 at h
    linarith
  have hzero := contraction_at_index d n b c
  have htail : coordinateTail d n (fun i => (contraction d n b c) i) = X := by
    ext i
    by_cases hi : i = n
    · simp [coordinateTail, X, B, C, hi]
    · simp [coordinateTail, contraction, X, B, C, hi]
  have hsplit : ‖contraction d n b c‖ ^ 2 = u ^ 2 * v ^ 2 + ‖X‖ ^ 2 := by
    have h := tail_norm_split d n (fun i => (contraction d n b c) i)
    change ‖contraction d n b c‖ ^ 2 = _ at h
    rw [hzero, norm_mul, Complex.norm_conj, Complex.norm_conj, mul_pow, htail] at h
    exact h
  have hX : ‖X‖ ≤ ‖z d‖ * (u * t + v * s) := by
    calc
      ‖X‖ ≤ ‖(conj (z d) * conj (b n)) • C‖ +
        ‖(z d * conj (c n)) • B‖ := norm_add_le _ _
      _ = ‖z d‖ * (u * t + v * s) := by
        simp only [norm_smul, norm_mul, Complex.norm_conj]
        change ‖z d‖ * u * t + ‖z d‖ * v * s = _
        ring
  have hX2 : ‖X‖ ^ 2 ≤ ‖z d‖ ^ 2 * (u * t + v * s) ^ 2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg X) (by positivity)).2 hX
  have hAM : (u * t + v * s) ^ 2 ≤
      2 * (u ^ 2 + v ^ 2) - (u ^ 2 + v ^ 2) ^ 2 := by
    calc
      _ ≤ (u * t + v * s) ^ 2 + (u * s - v * t) ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg _)
      _ = (u ^ 2 + v ^ 2) * (s ^ 2 + t ^ 2) := by ring
      _ = _ := by rw [hB, hC]; ring
  have hest := hX2.trans (mul_le_mul_of_nonneg_left hAM (sq_nonneg ‖z d‖))
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 0 < (d : ℝ) - 1 := by linarith
  have hd2 : 0 < (d : ℝ) ^ 2 - 1 := by nlinarith
  rw [(scalar_identities d hd).1] at hest
  have hest' := (le_div_iff₀ (show 0 < 2 * ((d : ℝ) - 1) by positivity)).mp
    (show ‖X‖ ^ 2 ≤ ((d : ℝ) *
      (2 * (u ^ 2 + v ^ 2) - (u ^ 2 + v ^ 2) ^ 2)) /
        (2 * ((d : ℝ) - 1)) by convert hest using 1 <;> ring)
  have hpoly : ((d : ℝ) ^ 2 - 1) * ‖contraction d n b c‖ ^ 2 ≤ (d : ℝ) ^ 2 := by
    rw [hsplit]
    have hnonneg : 0 ≤ ((d : ℝ) ^ 2 - 1) * (u ^ 2 - v ^ 2) ^ 2 :=
      mul_nonneg hd2.le (sq_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left hest' (show 0 ≤ (d : ℝ) + 1 by positivity)
    nlinarith [sq_nonneg (((d : ℝ) + 1) * (u ^ 2 + v ^ 2) - 2 * (d : ℝ))]
  have hpoly' : ‖contraction d n b c‖ ^ 2 ≤ (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) :=
    (le_div_iff₀ hd2).2 (by simpa only [mul_comm] using hpoly)
  have heq : sharpValue d * ((d : ℝ) + 1) =
      (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) := by
    unfold sharpValue
    field_simp [ne_of_gt hd2, show (d : ℝ) + 1 ≠ 0 by positivity]
  rw [heq]
  exact hpoly'


private lemma sharp_upper (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (a b c : Fin d → ℂ) (ha : UnitVector a) (hb : UnitVector b) (hc : UnitVector c) :
    ‖overlap a b c (φ d 0)‖ ^ 2 ≤ sharpValue d := by
  have hs : 0 < Real.sqrt ((d : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hn := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 a) (contraction d 0 b c)
  change ‖WithLp.toLp 2 a‖ = 1 at ha
  rw [ha, one_mul] at hn
  have hn2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hn
  have hbound := contraction_bound d hd 0 b c hb hc
  rw [contraction_overlap, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs, div_pow]
  rw [Real.sq_sqrt (by positivity)]
  exact (div_le_iff₀ (by positivity)).2 (hn2.trans hbound)

private lemma contraction_attains (d : ℕ) (hd : 2 ≤ d) (n : Fin d)
    (b c : Fin d → ℂ) (hb : UnitVector b) (hc : UnitVector c)
    (henergy : ‖contraction d n b c‖ ^ 2 = sharpValue d * ((d : ℝ) + 1)) :
    sharpValue d ∈ overlapSet (φ d n) := by
  let χ := contraction d n b c
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 0 < (d : ℝ) - 1 := by linarith
  have hd2 : 0 < (d : ℝ) ^ 2 - 1 := by nlinarith
  have hdp : 0 < (d : ℝ) + 1 := by positivity
  change ‖χ‖ ^ 2 = sharpValue d * ((d : ℝ) + 1) at henergy
  have hχne : χ ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_pow (by decide)] at henergy
    have : 0 < sharpValue d * ((d : ℝ) + 1) := by unfold sharpValue; positivity
    linarith
  let A := (‖χ‖⁻¹ : ℂ) • χ
  have hA : UnitVector (fun i => A i) := by
    change ‖(‖χ‖⁻¹ : ℂ) • χ‖ = 1
    exact norm_smul_inv_norm (𝕜 := ℂ) hχne
  refine ⟨fun i => A i, fun i => b i, fun i => c i, hA, hb, hc, ?_⟩
  symm
  rw [contraction_overlap]
  change ‖inner ℂ A χ / (Real.sqrt ((d : ℝ) + 1) : ℂ)‖ ^ 2 = _
  have hinner : inner ℂ A χ = (‖χ‖ : ℂ) := by
    change inner ℂ ((‖χ‖⁻¹ : ℂ) • χ) χ = (‖χ‖ : ℂ)
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K, map_inv₀, Complex.conj_ofReal, pow_two]
    exact inv_mul_cancel_left₀
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.2 hχne)) _
  rw [hinner, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg χ), abs_of_nonneg (Real.sqrt_nonneg _),
    div_pow, Real.sq_sqrt hdp.le, henergy]
  exact mul_div_cancel_right₀ _ (ne_of_gt hdp)

set_option maxHeartbeats 1000000 in
private lemma sharp_attainment (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    sharpValue d ∈ overlapSet (φ d 0) := by
  classical
  let j : Fin d := ⟨1, by omega⟩
  have hj : j ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [j] at this
  have hj' : (0 : Fin d) ≠ j := Ne.symm hj
  let e₀ := EuclideanSpace.single (0 : Fin d) (1 : ℂ)
  let e₁ := EuclideanSpace.single j (1 : ℂ)
  have hnorm (v w : ℂ) : ‖v • e₀ + w • e₁‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ)]
    have hinner : inner ℂ (v • e₀) (w • e₁) = 0 := by
      simp [e₀, e₁, inner_smul_left, inner_smul_right,
        EuclideanSpace.inner_single_left, PiLp.single_apply, hj]
    rw [hinner]
    simp [norm_smul, e₀, e₁]
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 0 < (d : ℝ) - 1 := by linarith
  have hd2 : 0 < (d : ℝ) ^ 2 - 1 := by nlinarith
  have hdp : 0 < (d : ℝ) + 1 := by positivity
  let r := Real.sqrt ((d : ℝ) / ((d : ℝ) + 1))
  let t := Real.sqrt (1 / ((d : ℝ) + 1))
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = (d : ℝ) / ((d : ℝ) + 1) := Real.sq_sqrt (by positivity)
  have ht2 : t ^ 2 = 1 / ((d : ℝ) + 1) := Real.sq_sqrt (by positivity)
  have hz : z d ≠ 0 := by
    intro h
    have hq := (scalar_identities d hd).1
    rw [h, norm_zero, zero_pow (by decide)] at hq
    have : 0 < (d : ℝ) / (2 * ((d : ℝ) - 1)) := by positivity
    linarith
  let ρ := conj (z d) / z d
  have hρ : ‖ρ‖ = 1 := by
    dsimp [ρ]
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hz)]
  have hphase : conj (z d) * conj ρ = z d := by
    dsimp [ρ]
    rw [map_div₀, starRingEnd_self_apply]
    exact mul_div_cancel₀ _ ((map_ne_zero (starRingEnd ℂ)).2 hz)
  let b := (r : ℂ) • e₀ + (t : ℂ) • e₁
  let c := (r : ℂ) • e₀ + (ρ * (t : ℂ)) • e₁
  have hunit (σ : ℂ) (hσ : ‖σ‖ = 1) :
      UnitVector (fun i => ((r : ℂ) • e₀ + (σ * (t : ℂ)) • e₁) i) := by
    change ‖(r : ℂ) • e₀ + (σ * (t : ℂ)) • e₁‖ = 1
    have he : ‖(r : ℂ) • e₀ + (σ * (t : ℂ)) • e₁‖ ^ 2 = 1 := by
      rw [hnorm]
      simp only [norm_mul, hσ, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hr, abs_of_nonneg ht, hr2, ht2]
      field_simp
    nlinarith [norm_nonneg ((r : ℂ) • e₀ + (σ * (t : ℂ)) • e₁)]
  have hb : UnitVector (fun i => b i) := by
    simpa only [one_mul] using hunit 1 norm_one
  have hc : UnitVector (fun i => c i) := hunit ρ hρ
  have hb0 : b 0 = (r : ℂ) := by simp [b, e₀, e₁, PiLp.single_apply, hj']
  have hc0 : c 0 = (r : ℂ) := by simp [c, e₀, e₁, PiLp.single_apply, hj']
  have hb1 : b j = (t : ℂ) := by simp [b, e₀, e₁, PiLp.single_apply, hj]
  have hc1 : c j = ρ * (t : ℂ) := by simp [c, e₀, e₁, PiLp.single_apply, hj]
  let χ := contraction d 0 (fun i => b i) (fun i => c i)
  have hχ : χ = ((r ^ 2 : ℝ) : ℂ) • e₀ +
      (2 * z d * ((r * t : ℝ) : ℂ)) • e₁ := by
    ext i
    by_cases hi0 : i = 0
    · subst i
      change (contraction d 0 (fun i => b i) (fun i => c i)) 0 = _
      rw [contraction_at_index, hb0, hc0]
      simp [e₀, e₁, PiLp.single_apply, hj', pow_two]
    · by_cases hi1 : i = j
      · subst i
        change conj (z d) * conj (b 0) * conj (c j) +
          z d * conj (c 0) * conj (b j) = _
        rw [hb0, hc0, hb1, hc1]
        simp only [map_mul, Complex.conj_ofReal]
        calc
          _ = (conj (z d) * conj ρ + z d) * ((r * t : ℝ) : ℂ) := by push_cast; ring
          _ = _ := by
            rw [hphase]
            change (z d + z d) * ((r * t : ℝ) : ℂ) =
              ((r ^ 2 : ℝ) : ℂ) * e₀ j + (2 * z d * ((r * t : ℝ) : ℂ)) * e₁ j
            have he0 : e₀ j = 0 := by simp [e₀, PiLp.single_apply, hj]
            have he1 : e₁ j = 1 := by simp [e₁, PiLp.single_apply]
            rw [he0, he1]
            ring
      · simp [χ, contraction, b, c, e₀, e₁, PiLp.single_apply, hi0, hi1]
  have henergy : ‖χ‖ ^ 2 = sharpValue d * ((d : ℝ) + 1) := by
    calc
      _ = (r ^ 2) ^ 2 + 4 * ‖z d‖ ^ 2 * r ^ 2 * t ^ 2 := by
        rw [hχ, hnorm]
        simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg r), abs_of_nonneg (mul_nonneg hr ht),
          abs_of_nonneg hr, abs_of_nonneg ht]
        ring
      _ = _ := by
        rw [(scalar_identities d hd).1, hr2, ht2]
        unfold sharpValue
        field_simp [ne_of_gt hd1, ne_of_gt hd2, ne_of_gt hdp]
        <;> ring
  exact contraction_attains d hd 0 (fun i => b i) (fun i => c i) hb hc henergy


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
