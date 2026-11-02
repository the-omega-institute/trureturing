/- GID: D5/S3/Quantum/Analysis/SingularGramCommonBranchOptimum
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/SingularGramCommonBranchOptimum
   mirror-E: none(waiver:universal-hilbert-theorem)
   anchors: []
   utility: none
   digest: Finite coherent synthesis has an attained singular Gram constrained minimum. -/

import D5.S3.Observer.Hilbert.FiniteSynthesisGramDistance
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.Combination

/-! An exact affine constraint on finite coherent synthesis, including singular Gram operators. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Analysis.SingularGramCommonBranchOptimum

open scoped InnerProductSpace BigOperators
open D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse
open D5.S3.Observer.Hilbert.FiniteSynthesisGramDistance

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E
local instance : CompleteSpace H := FiniteDimensional.complete ℂ H

private theorem constrained_minimizer (V : E →L[ℂ] H) (b : E) (hb : b ≠ 0) :
    let G := gram V
    let p := moorePenroseInverse G b
    let a := (inner ℂ b p).re
    ∃ c : E, inner ℂ b c = 1 ∧
      (∀ d : E, inner ℂ b d = 1 → ‖V c‖ ^ 2 ≤ ‖V d‖ ^ 2) ∧
      (b ∈ G.range → inner ℂ b p = (a : ℂ) ∧
        0 < a ∧ c = (a⁻¹ : ℂ) • p ∧ ‖V c‖ ^ 2 = a⁻¹) ∧
      (b ∉ G.range → c ∈ G.ker ∧ V c = 0) := by
  dsimp only
  let G := gram V
  let p := moorePenroseInverse G b
  have hrange : G.range = V.kerᗮ := by
    change (V.toLinearMap.adjoint ∘ₗ V.toLinearMap).range = _
    rw [V.toLinearMap.range_adjoint_comp_self, ← V.toLinearMap.orthogonal_ker]
  by_cases h : b ∈ G.range
  · obtain ⟨u, hu⟩ := h
    have hnormal : G p = b := by
      change G (moorePenroseInverse G b) = b
      rw [← hu]
      exact congrArg (fun A : E →ₗ[ℂ] E => A u) (comp_moorePenroseInverse_comp G)
    have henergy : inner ℂ b p = (‖V p‖ ^ 2 : ℝ) := by
      rw [← hnormal]
      change inner ℂ (V.adjoint (V p)) p = _
      rw [V.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
      simp
    have hv : V p ≠ 0 := by
      intro hz
      apply hb
      rw [← hnormal]
      change V.adjoint (V p) = 0
      rw [hz, map_zero]
    have ha : 0 < (inner ℂ b p).re := by
      rw [henergy, Complex.ofReal_re]
      exact sq_pos_of_pos (norm_pos_iff.mpr hv)
    set a : ℝ := (inner ℂ b p).re with hadef
    have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    have hinner : inner ℂ b p = (a : ℂ) := by
      rw [hadef, henergy]
      simp only [← Complex.ofReal_pow, Complex.ofReal_re]
    let c : E := (a⁻¹ : ℂ) • p
    have hc : inner ℂ b c = 1 := by
      simp only [c, inner_smul_right, hinner]
      exact inv_mul_cancel₀ haC
    have hcenergy : ‖V c‖ ^ 2 = a⁻¹ := by
      have hvp : ‖V p‖ ^ 2 = a := by
        simpa only [← Complex.ofReal_pow, Complex.ofReal_re, hadef] using
          (congrArg Complex.re henergy).symm
      rw [show V c = (a⁻¹ : ℂ) • V p by simp [c], norm_smul, mul_pow, hvp]
      simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs]
      field_simp [ha.ne']
    refine ⟨c, hc, ?_, ?_, ?_⟩
    · intro d hd
      have ho : inner ℂ (V c) (V d - V c) = 0 := by
        rw [← map_sub, ← V.adjoint_inner_left]
        have hnc : V.adjoint (V c) = (a⁻¹ : ℂ) • b := by
          simp only [c, map_smul]
          exact congrArg (fun z : E => (a⁻¹ : ℂ) • z) hnormal
        rw [hnc, inner_smul_left, inner_sub_right, hd, hc, sub_self, mul_zero]
      have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (V c) (V d - V c) ho
      have hsplit : V c + (V d - V c) = V d := by abel
      rw [hsplit] at he
      nlinarith [sq_nonneg ‖V d - V c‖]
    · intro _
      exact ⟨hinner, ha, rfl, hcenergy⟩
    · exact fun hn => (hn ⟨u, hu⟩).elim
  · have hn : b ∉ V.kerᗮ := by rwa [← hrange]
    rw [Submodule.mem_orthogonal'] at hn
    push Not at hn
    obtain ⟨k, hk, hbk⟩ := hn
    let c : E := (inner ℂ b k)⁻¹ • k
    have hc : inner ℂ b c = 1 := by
      simp only [c, inner_smul_right]
      exact inv_mul_cancel₀ hbk
    have hv : V c = 0 := by simp [c, show V k = 0 from hk]
    refine ⟨c, hc, ?_, ?_, ?_⟩
    · intro d _
      rw [hv, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact sq_nonneg _
    · exact fun hh => (h hh).elim
    · intro _
      refine ⟨?_, hv⟩
      change V.adjoint (V c) = 0
      rw [hv, map_zero]

variable {ι : Type*} [Fintype ι]

/-- Synthesis of the actual complex amplitudes; the coefficient space has its Euclidean norm. -/
def synthesis (x : ι → H) : EuclideanSpace ℂ ι →L[ℂ] H :=
  ∑ j, (EuclideanSpace.proj j).smulRight (x j)

/-- The fixed coherent signature with every entry equal to one. -/
def ones : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun _ => 1)

/-- Differences use one fixed reference amplitude and preserve all cross-input phases. -/
def differenceSpace (x : ι → H) (i₀ : ι) : Submodule ℂ H :=
  Submodule.span ℂ (Set.range (fun j => x j - x i₀))

omit [FiniteDimensional ℂ H] in
private theorem synthesis_apply (x : ι → H) (c : EuclideanSpace ℂ ι) :
    synthesis x c = ∑ j, c j • x j := by
  simp [synthesis]

private theorem ones_inner (c : EuclideanSpace ℂ ι) :
    inner ℂ (ones : EuclideanSpace ℂ ι) c = ∑ j, c j := by
  simp [ones, PiLp.inner_apply]

private theorem feasible_image (x : ι → H) (i₀ : ι) (z : H) :
    (∃ c : EuclideanSpace ℂ ι, ∑ j, c j = 1 ∧ synthesis x c = z) ↔
      z - x i₀ ∈ differenceSpace x i₀ := by
  classical
  constructor
  · rintro ⟨c, hc, rfl⟩
    have he : synthesis x c - x i₀ = ∑ j, c j • (x j - x i₀) := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hc,
        one_smul, synthesis_apply]
    rw [he]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j))
  · intro hz
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hz
    let c : EuclideanSpace ℂ ι := WithLp.toLp 2
      (fun j => d j + if j = i₀ then 1 - ∑ k, d k else 0)
    have hc : ∑ j, c j = 1 := by
      change (∑ j, (d j + if j = i₀ then 1 - ∑ k, d k else 0)) = 1
      simp [Finset.sum_add_distrib]
    refine ⟨c, hc, ?_⟩
    rw [synthesis_apply]
    have he : ∑ j, c j • x j = (∑ j, d j • x j) + (1 - ∑ k, d k) • x i₀ := by
      simp [c, add_smul, Finset.sum_add_distrib, ite_smul]
    rw [he]
    have hd' : (∑ j, d j • x j) - (∑ j, d j) • x i₀ = z - x i₀ := by
      simpa only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul] using hd
    rw [sub_smul, one_smul]
    calc
      _ = ((∑ j, d j • x j) - (∑ j, d j) • x i₀) + x i₀ := by abel
      _ = z := by rw [hd']; abel

/-- The attained coherent minimum, its geometric interpretation, and both singular cases.
The Moore-Penrose inverse is the constructed finite inverse, with its four Penrose laws. -/
theorem singular_gram_common_branch_optimum (x : ι → H) (i₀ : ι) :
    let X := synthesis x
    let G := gram X
    let D := differenceSpace x i₀
    let q := Dᗮ.starProjection (x i₀)
    let b : EuclideanSpace ℂ ι := ones
    let p := moorePenroseInverse G b
    let a := (inner ℂ b p).re
    (∀ c : EuclideanSpace ℂ ι, inner ℂ c (G c) = (‖X c‖ ^ 2 : ℝ)) ∧
    (∀ z : H, (∃ c : EuclideanSpace ℂ ι, ∑ j, c j = 1 ∧ X c = z) ↔
      z - x i₀ ∈ D) ∧
    IsLeast {t : ℝ | ∃ c : EuclideanSpace ℂ ι,
      ∑ j, c j = 1 ∧ (inner ℂ c (G c)).re = t} (‖q‖ ^ 2) ∧
    (b ∈ G.range → inner ℂ b p = (a : ℂ) ∧ 0 < a ∧ ‖q‖ ^ 2 = a⁻¹ ∧
      (∑ j, ((a⁻¹ : ℂ) • p) j) = 1 ∧ ‖X ((a⁻¹ : ℂ) • p)‖ ^ 2 = ‖q‖ ^ 2) ∧
    (b ∉ G.range → ‖q‖ ^ 2 = 0 ∧
      ∃ c : EuclideanSpace ℂ ι, c ∈ G.ker ∧ ∑ j, c j = 1 ∧ X c = 0) := by
  dsimp only
  let X := synthesis x
  let G := gram X
  let D := differenceSpace x i₀
  let q := Dᗮ.starProjection (x i₀)
  have hquadratic (c : EuclideanSpace ℂ ι) :
      inner ℂ c (G c) = (‖X c‖ ^ 2 : ℝ) := by
    change inner ℂ c (X.adjoint (X c)) = _
    rw [X.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    simp
  have hquadre (c : EuclideanSpace ℂ ι) : (inner ℂ c (G c)).re = ‖X c‖ ^ 2 := by
    rw [hquadratic]
    simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  have hqD : q - x i₀ ∈ D := by
    have hh := Dᗮ.sub_starProjection_mem_orthogonal (x i₀)
    have hh' : x i₀ - q ∈ D := by simpa only [Submodule.orthogonal_orthogonal] using hh
    simpa only [neg_sub] using D.neg_mem hh'
  obtain ⟨cq, hcq, hXcq⟩ := (feasible_image x i₀ q).mpr hqD
  change X cq = q at hXcq
  have hqmin (d : EuclideanSpace ℂ ι) (hd : ∑ j, d j = 1) :
      ‖q‖ ^ 2 ≤ ‖X d‖ ^ 2 := by
    have hdD := (feasible_image x i₀ (X d)).mp ⟨d, hd, rfl⟩
    have hdiff : X d - q ∈ D := by
      convert D.sub_mem hdD hqD using 1 <;> abel
    have ho : inner ℂ q (X d - q) = 0 :=
      (Submodule.mem_orthogonal' _ _).mp (Dᗮ.starProjection_apply_mem _) _ hdiff
    have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero q (X d - q) ho
    have hsplit : q + (X d - q) = X d := by abel
    rw [hsplit] at he
    nlinarith [sq_nonneg ‖X d - q‖]
  have hb : (ones : EuclideanSpace ℂ ι) ≠ 0 := by
    intro h
    have hi := congrArg (fun c : EuclideanSpace ℂ ι => c i₀) h
    simpa [ones] using hi
  obtain ⟨c, hc, hcmin, hcrange, hckernel⟩ := constrained_minimizer X ones hb
  have hcsum : ∑ j, c j = 1 := by rwa [ones_inner] at hc
  have hcval : ‖X c‖ ^ 2 = ‖q‖ ^ 2 :=
    le_antisymm (by simpa only [hXcq] using hcmin cq (by rw [ones_inner]; exact hcq))
      (hqmin c hcsum)
  refine ⟨hquadratic, feasible_image x i₀, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact ⟨c, hcsum, (hquadre c).trans hcval⟩
  · rintro t ⟨d, hd, rfl⟩
    rw [hquadre]
    exact hqmin d hd
  · intro hr
    obtain ⟨hreal, ha, hcp, hcv⟩ := hcrange hr
    refine ⟨hreal, ha, hcval.symm.trans hcv, ?_, ?_⟩
    · rwa [← hcp]
    · rwa [← hcp]
  · intro hn
    obtain ⟨hk, hz⟩ := hckernel hn
    refine ⟨?_, c, hk, hcsum, hz⟩
    rw [← hcval, hz, norm_zero, zero_pow (by decide : 2 ≠ 0)]

#print axioms singular_gram_common_branch_optimum

example :
    let x : Fin 2 → ℂ := fun _ => 1
    (∃ k : EuclideanSpace ℂ (Fin 2), k ≠ 0 ∧ gram (synthesis x) k = 0) ∧
    (ones : EuclideanSpace ℂ (Fin 2)) ∈ (gram (synthesis x)).range := by
  dsimp only
  have hkernel : synthesis (fun _ : Fin 2 => (1 : ℂ))
      (WithLp.toLp 2 ![1, -1]) = 0 := by
    simp [synthesis_apply, Fin.sum_univ_two]
  constructor
  · refine ⟨WithLp.toLp 2 ![1, -1], ?_, ?_⟩
    · intro h
      have hi := congrArg (fun c : EuclideanSpace ℂ (Fin 2) => c 0) h
      norm_num at hi
    · change (synthesis (fun _ : Fin 2 => (1 : ℂ))).adjoint
        (synthesis (fun _ : Fin 2 => (1 : ℂ)) (WithLp.toLp 2 ![1, -1])) = 0
      rw [hkernel, map_zero]
  · by_contra hn
    have hz := (singular_gram_common_branch_optimum (fun _ : Fin 2 => (1 : ℂ)) 0).2.2.2.2 hn
    norm_num [differenceSpace, Submodule.starProjection_top] at hz

example :
    let x : Fin 2 → ℂ := ![1, 0]
    (ones : EuclideanSpace ℂ (Fin 2)) ∉ (gram (synthesis x)).range ∧
    ∃ k : EuclideanSpace ℂ (Fin 2), k ∈ (gram (synthesis x)).ker ∧
      (∑ j, k j) = 1 ∧ synthesis x k = 0 := by
  dsimp only
  let X := synthesis (![1, 0] : Fin 2 → ℂ)
  let k : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 1 1
  have hsum : (∑ j, k j) = 1 := by simp [k, PiLp.single_apply, Fin.sum_univ_two]
  have hk : X k = 0 := by simp [X, synthesis_apply, k, PiLp.single_apply, Fin.sum_univ_two]
  have hrange : (gram X).range = X.kerᗮ := by
    change (X.toLinearMap.adjoint ∘ₗ X.toLinearMap).range = _
    rw [X.toLinearMap.range_adjoint_comp_self, ← X.toLinearMap.orthogonal_ker]
  have hn : (ones : EuclideanSpace ℂ (Fin 2)) ∉ (gram X).range := by
    intro h
    rw [hrange, Submodule.mem_orthogonal'] at h
    have hz := h k hk
    rw [ones_inner, hsum] at hz
    exact one_ne_zero hz
  exact ⟨hn, (singular_gram_common_branch_optimum (![1, 0] : Fin 2 → ℂ) 0).2.2.2.2 hn |>.2⟩

end D5.S3.Quantum.Analysis.SingularGramCommonBranchOptimum
