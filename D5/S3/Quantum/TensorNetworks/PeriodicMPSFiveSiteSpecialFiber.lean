/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteSpecialFiber
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteSpecialFiber
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Basic]
   utility: none
   digest: An exactly classified exceptional fiber of the binary five-site marginal. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCoordinates

/-! Positivity reduces the chosen fiber to the independent sets of the five-cycle. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteSpecialFiber

open Matrix PeriodicMPSFiveSiteCoordinates
open scoped Matrix ComplexConjugate

noncomputable section

/-- The two-site matrix in the standard binary basis. -/
def gram (p : Fin 8 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  flatten p * (flatten p)ᴴ

/-- Only the empty, singleton and separated-pair necklaces can be nonzero
when the observed probability of two adjacent ones vanishes. -/
theorem supported_of_corner_zero (p : Fin 8 → ℂ) (h : gram p 3 3 = 0) :
    p = ![p 0, p 1, 0, p 3, 0, 0, 0, 0] := by
  have hs : ∑ j : Fin 8, Complex.normSq (flatten p 3 j) = 0 := by
    have hc := congrArg Complex.re h
    simpa [gram, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj] using hc
  have hz (j : Fin 8) : flatten p 3 j = 0 :=
    Complex.normSq_eq_zero.mp <| (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => Complex.normSq_nonneg (flatten p 3 k))).mp hs j (Finset.mem_univ _)
  have h₂ : p 2 = 0 := hz 0
  have h₄ : p 4 = 0 := hz 1
  have h₅ : p 5 = 0 := hz 2
  have h₆ : p 6 = 0 := hz 3
  have h₇ : p 7 = 0 := hz 7
  funext i
  fin_cases i <;> simp [h₂, h₄, h₅, h₆, h₇]

private def sparse (a b c : ℂ) : Fin 8 → ℂ := ![a, b, 0, c, 0, 0, 0, 0]

private lemma sparse_gram (a b c : ℂ) :
    gram (sparse a b c) =
      !![a * star a + 3 * (b * star b) + c * star c, a * star b + 2 * (b * star c),
          a * star b + 2 * (b * star c), 0;
        star (a * star b + 2 * (b * star c)), b * star b + 2 * (c * star c),
          b * star b + c * star c, 0;
        star (a * star b + 2 * (b * star c)), b * star b + c * star c,
          b * star b + 2 * (c * star c), 0;
        0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, flatten, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      sparse, star_mul, star_add, mul_comm] <;> ring

/-- The exceptional observation at which all physical state rays can be enumerated. -/
def target : Matrix (Fin 4) (Fin 4) ℂ :=
  !![33373 / 1296, 161 / 72, 161 / 72, 0;
    161 / 72, 9 / 4, 5 / 4, 0;
    161 / 72, 5 / 4, 9 / 4, 0;
    0, 0, 0, 0]

private lemma gram_phase (p : Fin 8 → ℂ) (z : ℂ) (hz : z * star z = 1) :
    gram (z • p) = gram p := by
  have hf : flatten (z • p) = z • flatten p := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [gram, hf, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hz, one_smul]
  rfl

private lemma sparse_mass (a b c : ℂ) (h : gram (sparse a b c) = target) :
    Complex.normSq a = 4 + (161 / 36 : ℝ) ^ 2 ∧
      Complex.normSq b = 1 / 4 ∧ Complex.normSq c = 1 := by
  rw [sparse_gram] at h
  have ha := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => (M 0 0).re) h
  have hb := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => (M 1 1).re) h
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => (M 1 2).re) h
  simp [target, Complex.mul_conj, Complex.star_def] at ha hb hc
  constructor
  · linarith
  constructor <;> linarith

private lemma normalized_sparse (a b : ℂ) (h : gram (sparse a b 1) = target) :
    (a = 2 - (161 / 36 : ℂ) * Complex.I ∧ b = -Complex.I / 2) ∨
      (a = 2 + (161 / 36 : ℂ) * Complex.I ∧ b = Complex.I / 2) := by
  obtain ⟨ha, hb, _⟩ := sparse_mass a b 1 h
  let q := 2 * b
  let α : ℝ := 161 / 36
  have hq : Complex.normSq q = 1 := by
    change Complex.normSq (2 * b) = 1
    rw [Complex.normSq_mul, hb]
    norm_num [Complex.normSq_apply]
  have he : a * star b + 2 * b = (α : ℂ) / 2 := by
    rw [sparse_gram] at h
    have e := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 1) h
    calc
      _ = (161 / 72 : ℂ) := by simpa [target] using e
      _ = _ := by norm_num [α]
  have hb' : b * star b = (1 / 4 : ℂ) := by
    change b * conj b = _
    rw [Complex.mul_conj, hb]
    norm_num
  have ha' : a = q * ((α : ℂ) - 2 * q) := by
    have hlin : a * (1 / 4 : ℂ) + 2 * b ^ 2 = ((α : ℂ) / 2) * b := by
      calc
        _ = (a * star b + 2 * b) * b := by rw [← hb']; ring
        _ = _ := by rw [he]
    calc
      a = 4 * (a * (1 / 4 : ℂ) + 2 * b ^ 2) - 8 * b ^ 2 := by ring
      _ = q * ((α : ℂ) - 2 * q) := by rw [hlin]; dsimp [q]; ring
  have hn : Complex.normSq ((α : ℂ) - 2 * q) = 4 + α ^ 2 := by
    rw [ha', Complex.normSq_mul, hq, one_mul] at ha
    exact ha
  have hre : q.re = 0 := by
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im] at hq hn
    have hα : α ≠ 0 := by norm_num [α]
    have he' : α * q.re = 0 := by nlinarith
    exact (mul_eq_zero.mp he').resolve_left hα
  have him : q.im ^ 2 = 1 ^ 2 := by
    simpa [Complex.normSq_apply, hre, pow_two] using hq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp him with hp | hm
  · have hqi : q = Complex.I := Complex.ext (by simp [hre]) (by simpa using hp)
    right
    refine ⟨?_, ?_⟩
    · rw [ha', hqi]
      apply Complex.ext <;> simp [α, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
    · apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr
      simpa [q, mul_comm] using hqi
  · have hqi : q = -Complex.I := Complex.ext (by simp [hre]) (by simpa using hm)
    left
    refine ⟨?_, ?_⟩
    · rw [ha', hqi]
      apply Complex.ext <;> simp [α, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
    · apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr
      simpa [q, mul_comm] using hqi

/-- The special marginal has exactly the two indicated candidate necklace rays
after fixing the separated-pair amplitude to one. -/
theorem special_fiber_classification (p : Fin 8 → ℂ) (h : gram p = target) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      (z • p = sparse (2 - (161 / 36 : ℂ) * Complex.I) (-Complex.I / 2) 1 ∨
        z • p = sparse (2 + (161 / 36 : ℂ) * Complex.I) (Complex.I / 2) 1) := by
  have hp := supported_of_corner_zero p (by rw [h]; rfl)
  let a := p 0
  let b := p 1
  let c := p 3
  change p = sparse a b c at hp
  have hc : Complex.normSq c = 1 := (sparse_mass a b c (hp ▸ h)).2.2
  have hz : c * star c = 1 := by
    change c * conj c = 1
    rw [Complex.mul_conj, hc]
    norm_num
  refine ⟨star c, ?_, ?_⟩
  · have hc' : ‖c‖ ^ 2 = 1 := by rwa [Complex.sq_norm]
    have hc'' : ‖c‖ = 1 := by nlinarith [norm_nonneg c]
    simpa using hc''
  have hshape : star c • p = sparse (star c * a) (star c * b) 1 := by
    rw [hp]
    funext i
    fin_cases i <;> simp [sparse, Pi.smul_apply, smul_eq_mul]
    change star c * c = 1
    exact (mul_comm _ _).trans hz
  have hg : gram (sparse (star c * a) (star c * b) 1) = target := by
    rw [← hshape, gram_phase p _ (by simpa [mul_comm] using hz), h]
  rcases normalized_sparse _ _ hg with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl (by rw [hshape, ha, hb])
  · exact Or.inr (by rw [hshape, ha, hb])

private def specialRay (sgn : ℂ) : Fin 8 → ℂ :=
  sparse (2 - (161 / 36 : ℂ) * sgn * Complex.I) (-sgn * Complex.I / 2) 1

private lemma specialRay_gram (sgn : ℂ) (h : sgn = 1 ∨ sgn = -1) :
    gram (specialRay sgn) = target := by
  rcases h with rfl | rfl <;> rw [specialRay, sparse_gram]
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;> norm_num [target, Complex.star_def, Complex.mul_re,
        Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
        Complex.normSq_apply]

private lemma specialRay_actual (sgn : ℂ) (h : sgn = 1 ∨ sgn = -1) :
    ∃ A : Fin 2 → PeriodicMPSParentIntersection.Bond,
      UniformMPSExpectedDimensionRefutation.traceWord 2 2 5 A ∘ necklaces = specialRay sgn := by
  let x : ℂ := (7 / 6 : ℂ) * (1 + sgn * Complex.I)
  let y : ℂ := -sgn * Complex.I / 2
  have hxy : 2 * x - 3 * y ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    rcases h with h | h <;>
      norm_num [x, y, h, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.div_re,
        Complex.normSq_apply] at hr
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (2 * x - 3 * y) (n := 2) (by decide)
  have htn : t ≠ 0 := fun he => hxy (by simpa [he] using ht.symm)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq t⁻¹ (n := 5) (by decide)
  obtain ⟨A, h0, h1, h2, h3, h4⟩ :=
    exists_trace_coordinates (z * t) (z * 0) (z ^ 2 * (x-y)) (z ^ 2 * 0) (z ^ 2 * (-1))
  refine ⟨A, ?_⟩
  rw [trace_word_necklaces, h0, h1, h2, h3, h4, coordinates_scale, aligned_trace, smul_smul,
    hz, inv_mul_cancel₀ htn, one_smul, ht]
  have hx : 3 * (x - y) - (2 * x - 3 * y) = x := by ring
  have hy : 2 * (x - y) - (2 * x - 3 * y) = y := by ring
  rw [hx, hy]
  rcases h with h | h <;>
    funext i <;> fin_cases i <;>
    apply Complex.ext <;> norm_num [aligned, sparse, specialRay, x, y, h, Complex.mul_re,
      Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
      Complex.normSq_apply, pow_two]

/-- Both phase classes in the exceptional fiber have actual five-site tensors. -/
theorem special_fiber_realized :
    ∃ A B : Fin 2 → PeriodicMPSParentIntersection.Bond,
      let trace := UniformMPSExpectedDimensionRefutation.traceWord 2 2 5
      trace A ∘ necklaces = specialRay 1 ∧ trace B ∘ necklaces = specialRay (-1) ∧
        gram (trace A ∘ necklaces) = target ∧ gram (trace B ∘ necklaces) = target := by
  obtain ⟨A, hA⟩ := specialRay_actual 1 (Or.inl rfl)
  obtain ⟨B, hB⟩ := specialRay_actual (-1) (Or.inr rfl)
  exact ⟨A, B, hA, hB, hA.symm ▸ specialRay_gram 1 (Or.inl rfl),
    hB.symm ▸ specialRay_gram (-1) (Or.inr rfl)⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteSpecialFiber
