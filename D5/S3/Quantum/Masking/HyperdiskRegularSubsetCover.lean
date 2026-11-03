/- GID: D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover
   generality: I
   mirror-B: D5/B/S3/Quantum/Masking/HyperdiskRegularSubsetCover
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.claim; result=D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.result; claim=D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.claim
   digest: A regular subset of a four-dimensional hyperdisk has no finite hyperdisk cover. -/

import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Ding and Hu, arXiv:1909.11256v3, Definitions 1 and 4 and the second open
question in the conclusion. Pure states are unit vectors, including their global
phases. A cover consists of hyperdisks contained in the regular subset. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace D5.S3.Quantum.Masking.HyperdiskRegularSubsetCover

/-- The full coefficient-modulus level set of unit vectors in the source definition. -/
def IsHyperdisk {n : ℕ} (s : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  ∃ (m : ℕ) (φ : Fin m → EuclideanSpace ℂ (Fin n)) (r : Fin m → ℝ),
    Orthonormal ℂ φ ∧ Submodule.span ℂ (Set.range φ) = Submodule.span ℂ s ∧
      (∀ j, 0 < r j) ∧ s = {ψ | ‖ψ‖ = 1 ∧ ∀ j, ‖⟪φ j, ψ⟫_ℂ‖ = r j}

/-- Definition 4: intersection with the linear span of the subset. -/
def IsRegularSubset {n : ℕ} (c s : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  IsHyperdisk s ∧ ((Submodule.span ℂ c : Set _) ∩ s = c)

/-- The finite-cover question for regular subsets of hyperdisks. -/
def claim : Prop :=
  ∀ (n : ℕ) (s c : Set (EuclideanSpace ℂ (Fin n))), IsRegularSubset c s →
    ∃ (k : ℕ) (h : Fin k → Set (EuclideanSpace ℂ (Fin n))),
      (∀ i, IsHyperdisk (h i) ∧ h i ⊆ c) ∧ c = ⋃ i, h i

private def radii : Fin 4 → ℝ := fun j => ![1, 2, 3, 4] j / Real.sqrt 30

private def constraint : EuclideanSpace ℂ (Fin 4) →ₗ[ℂ] ℂ :=
  (6 : ℂ) • EuclideanSpace.projₗ 0 + (3 : ℂ) • EuclideanSpace.projₗ 1 +
    (2 : ℂ) • EuclideanSpace.projₗ 2 + (3 : ℂ) • EuclideanSpace.projₗ 3

private def ambient : Set (EuclideanSpace ℂ (Fin 4)) :=
  {x | ‖x‖ = 1 ∧ ∀ j, ‖x j‖ = radii j}

private def counterexample : Set (EuclideanSpace ℂ (Fin 4)) :=
  (LinearMap.ker constraint : Set _) ∩ ambient

private def parameter (a : ℕ) : ℝ := -1 / 2 - 1 / (4 * ((a : ℝ) + 1))

private def phases (t : ℝ) : Fin 4 → ℂ :=
  let z : ℂ := (t : ℂ) + Complex.I * (Real.sqrt (1 - t ^ 2) : ℂ)
  let w : ℂ := -2 - z
  let q : ℝ := 5 + 4 * t
  let k : ℂ := (Real.sqrt ((4 - q) / q) : ℂ)
  ![z, w * (1 + Complex.I * k) / 2, w * (1 - Complex.I * k) / 2, 1]

private def family (a : ℕ) : EuclideanSpace ℂ (Fin 4) :=
  WithLp.toLp 2 (fun j => (radii j : ℂ) * phases (parameter a) j)

private lemma radii_pos (j : Fin 4) : 0 < radii j := by
  fin_cases j <;> exact div_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))

private lemma coordinate_norm (x : EuclideanSpace ℂ (Fin 4))
    (hx : ∀ j, ‖x j‖ = radii j) : ‖x‖ = 1 := by
  have hs : ‖x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [hx]
    dsimp only [radii]
    norm_num [Fin.sum_univ_succ, div_pow, Real.sq_sqrt]
  nlinarith [norm_nonneg x]

private lemma ambient_span : Submodule.span ℂ ambient = ⊤ := by
  have hsingle (j : Fin 4) : EuclideanSpace.single j (1 : ℂ) ∈
      Submodule.span ℂ ambient := by
    let a : EuclideanSpace ℂ (Fin 4) := WithLp.toLp 2 (fun k => (radii k : ℂ))
    let b : EuclideanSpace ℂ (Fin 4) :=
      WithLp.toLp 2 (fun k => if k = j then -(radii k : ℂ) else (radii k : ℂ))
    have ha : a ∈ ambient := by
      have hn (k : Fin 4) : ‖a k‖ = radii k := by
        simp [a, Complex.norm_real, abs_of_pos (radii_pos k)]
      exact ⟨coordinate_norm a hn, hn⟩
    have hb : b ∈ ambient := by
      have hn (k : Fin 4) : ‖b k‖ = radii k := by
        change ‖if k = j then -(radii k : ℂ) else (radii k : ℂ)‖ = radii k
        split_ifs <;> simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (radii_pos k)]
      exact ⟨coordinate_norm b hn, hn⟩
    have he : a - b = (2 * (radii j : ℂ)) • EuclideanSpace.single j 1 := by
      apply WithLp.ofLp_injective
      have hu : (fun k => if k = j then -(radii k : ℂ) else (radii k : ℂ)) =
          Function.update (fun k => (radii k : ℂ)) j (-(radii j : ℂ)) := by
        funext k
        simp only [Function.update_apply, eq_comm]
        split_ifs with h
        · rw [h]
        · rfl
      change (fun k => (radii k : ℂ)) -
        (fun k => if k = j then -(radii k : ℂ) else (radii k : ℂ)) = _
      rw [hu, Pi.update_eq_sub_add_single, Pi.single_neg]
      change (fun k => (radii k : ℂ)) -
        ((fun k => (radii k : ℂ)) - Pi.single j (radii j : ℂ) +
          -Pi.single j (radii j : ℂ)) = (2 * (radii j : ℂ)) • Pi.single j 1
      rw [← Pi.single_smul, smul_eq_mul, mul_one, two_mul, Pi.single_add]
      abel
    have hz : (2 * (radii j : ℂ)) ≠ 0 :=
      mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (ne_of_gt (radii_pos j)))
    have hm := (Submodule.span ℂ ambient).smul_mem ((2 * (radii j : ℂ))⁻¹)
      ((Submodule.span ℂ ambient).sub_mem (Submodule.subset_span ha)
        (Submodule.subset_span hb))
    rw [he, smul_smul, inv_mul_cancel₀ hz, one_smul] at hm
    exact hm
  apply top_unique
  intro x _
  rw [← (EuclideanSpace.basisFun (Fin 4) ℂ).sum_repr x]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  simpa only [EuclideanSpace.basisFun_apply] using hsingle j

private lemma ambient_hyperdisk : IsHyperdisk ambient := by
  refine ⟨4, fun j => EuclideanSpace.single j 1, radii,
    EuclideanSpace.orthonormal_single, ?_, radii_pos, ?_⟩
  · rw [ambient_span]
    have he : (fun j : Fin 4 => EuclideanSpace.single j (1 : ℂ)) =
        ⇑(EuclideanSpace.basisFun (Fin 4) ℂ) := by
      funext j; exact (EuclideanSpace.basisFun_apply (Fin 4) ℂ j).symm
    rw [he]
    simpa only [OrthonormalBasis.coe_toBasis] using
      (EuclideanSpace.basisFun (Fin 4) ℂ).toBasis.span_eq
  · ext x
    dsimp only [ambient]
    simp only [Set.mem_ofPred_eq, EuclideanSpace.inner_single_left,
      map_one, one_mul]

private lemma regular : IsRegularSubset counterexample ambient := by
  refine ⟨ambient_hyperdisk, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    exact ⟨(Submodule.span_le.mpr (fun y hy => hy.1)) hx.1, hx.2⟩
  · intro x hx
    exact ⟨Submodule.subset_span hx, hx.2⟩

private lemma parameter_bounds (a : ℕ) : -(3 : ℝ) / 4 ≤ parameter a ∧
    parameter a ≤ -(1 : ℝ) / 2 := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hp : 0 < 4 * ((a : ℝ) + 1) := by positivity
  have hle : 1 / (4 * ((a : ℝ) + 1)) ≤ (1 : ℝ) / 4 := by
    apply (div_le_div_iff₀ hp (by norm_num : (0 : ℝ) < 4)).mpr
    nlinarith
  have hnonneg : 0 ≤ 1 / (4 * ((a : ℝ) + 1)) := le_of_lt (one_div_pos.mpr hp)
  dsimp only [parameter]
  constructor <;> linarith

private lemma phases_unit (t : ℝ) (ht : -(3 : ℝ) / 4 ≤ t ∧ t ≤ -(1 : ℝ) / 2) :
    (∀ j, ‖phases t j‖ = 1) ∧
      phases t 0 + phases t 1 + phases t 2 + 2 * phases t 3 = 0 := by
  let s : ℝ := Real.sqrt (1 - t ^ 2)
  let q : ℝ := 5 + 4 * t
  let k : ℝ := Real.sqrt ((4 - q) / q)
  let z : ℂ := (t : ℂ) + Complex.I * (s : ℂ)
  let w : ℂ := -2 - z
  have hq : 0 < q := by dsimp [q]; linarith [ht.1]
  have hq4 : q ≤ 4 := by dsimp [q]; linarith [ht.2]
  have hk : k ^ 2 = (4 - q) / q := Real.sq_sqrt (div_nonneg (by linarith) (le_of_lt hq))
  have hz : Complex.normSq z = 1 := by
    exact Complex.normSq_ofReal_add_I_mul_sqrt_one_sub (by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [ht.1, ht.2])
  have hw : Complex.normSq w = q := by
    dsimp only [w, q]
    rw [Complex.normSq_sub, hz]
    dsimp only [z]
    norm_num [Complex.mul_re, Complex.mul_im]
    ring
  have hp : Complex.normSq (1 + Complex.I * (k : ℂ)) = 1 + k ^ 2 := by
    simpa only [Complex.ofReal_one, one_pow, mul_comm Complex.I] using
      Complex.normSq_add_mul_I 1 k
  have hm : Complex.normSq (1 - Complex.I * (k : ℂ)) = 1 + k ^ 2 := by
    simpa only [Complex.ofReal_one, Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg,
      neg_sq, one_pow, mul_comm Complex.I] using Complex.normSq_add_mul_I 1 (-k)
  have hcalc : q * (1 + k ^ 2) / 4 = 1 := by
    rw [hk]
    field_simp [ne_of_gt hq]
    ring
  have hn (a : ℂ) (ha : Complex.normSq a = 1) : ‖a‖ = 1 := by
    exact (sq_eq_sq₀ (norm_nonneg a) zero_le_one).mp
      (by simpa only [Complex.sq_norm, one_pow] using ha)
  constructor
  · intro j
    fin_cases j
    · exact hn z hz
    · apply hn
      change Complex.normSq (w * (1 + Complex.I * (k : ℂ)) / 2) = 1
      rw [map_div₀, map_mul, hw, hp]
      norm_num
      exact hcalc
    · apply hn
      change Complex.normSq (w * (1 - Complex.I * (k : ℂ)) / 2) = 1
      rw [map_div₀, map_mul, hw, hm]
      norm_num
      exact hcalc
    · change ‖(1 : ℂ)‖ = 1
      norm_num
  · change z + w * (1 + Complex.I * (k : ℂ)) / 2 +
      w * (1 - Complex.I * (k : ℂ)) / 2 + 2 * 1 = 0
    dsimp [w]
    ring

private lemma family_mem (a : ℕ) : family a ∈ counterexample := by
  obtain ⟨hn, hs⟩ := phases_unit (parameter a) (parameter_bounds a)
  have hc (j : Fin 4) : ‖family a j‖ = radii j := by
    change ‖(radii j : ℂ) * phases (parameter a) j‖ = radii j
    rw [norm_mul, hn j, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (radii_pos j)]
  refine ⟨?_, coordinate_norm (family a) hc, hc⟩
  change 6 * family a 0 + 3 * family a 1 + 2 * family a 2 + 3 * family a 3 = 0
  dsimp [family, radii, Matrix.vecHead, Matrix.vecTail]
  push_cast
  linear_combination (6 / (Real.sqrt 30 : ℂ)) * hs

private lemma family_ray_injective (a b : ℕ) (u : ℂ)
    (h : family a = u • family b) : a = b := by
  have h4 := congrArg (fun x : EuclideanSpace ℂ (Fin 4) => x 3) h
  have hr : (radii 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (radii_pos 3))
  have hu : u = 1 := by
    have he : (radii 3 : ℂ) = u * (radii 3 : ℂ) := by
      dsimp only [family, phases] at h4
      simpa [PiLp.smul_apply] using h4
    exact (mul_right_cancel₀ hr (by simpa using he.symm) : u = 1)
  rw [hu, one_smul] at h
  have h0 := congrArg (fun x : EuclideanSpace ℂ (Fin 4) => (x 0).re) h
  have ht : parameter a = parameter b := by
    have hr0 : radii 0 ≠ 0 := ne_of_gt (radii_pos 0)
    have he : radii 0 * parameter a = radii 0 * parameter b := by
      dsimp only [family, phases] at h0
      simpa [Complex.mul_re] using h0
    exact mul_left_cancel₀ hr0 he
  dsimp only [parameter] at ht
  have hd : (4 : ℝ) * ((a : ℝ) + 1) = 4 * ((b : ℝ) + 1) := by
    apply inv_injective
    have he : 1 / (4 * ((a : ℝ) + 1)) = 1 / (4 * ((b : ℝ) + 1)) := by linarith
    simpa only [one_div] using he
  have hab : (a : ℝ) = b := by linarith
  exact_mod_cast hab

private lemma four_phase_zero (a b : ℂ)
    (hm : ‖-a + b‖ = ‖a + b‖) (hi : ‖Complex.I * a + b‖ = ‖a + b‖) :
    a = 0 ∨ b = 0 := by
  have hm2 := congrArg (fun r : ℝ => r ^ 2) hm
  have hi2 := congrArg (fun r : ℝ => r ^ 2) hi
  simp only [Complex.sq_norm, Complex.normSq_add, Complex.normSq_neg, neg_mul,
    Complex.neg_re, map_mul, Complex.normSq_I, one_mul, mul_assoc,
    Complex.I_mul_re] at hm2 hi2
  have he : a * conj b = 0 := by
    apply Complex.ext
    · change (a * conj b).re = 0
      linarith
    · change (a * conj b).im = 0
      linarith
  simpa only [map_eq_zero] using (mul_eq_zero.mp he)

private lemma constant_modulus {m : ℕ} (a : Fin m → ℂ) (r : ℝ)
    (h : ∀ u : Fin m → ℂ, (∀ p, ‖u p‖ = 1) → ‖∑ p, a p * u p‖ = r) :
    ∀ p q, p ≠ q → a p = 0 ∨ a q = 0 := by
  classical
  intro p q hpq
  by_cases hp : a p = 0
  · exact Or.inl hp
  right
  have hpartial (u : Fin m → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
      ∑ i ∈ Finset.univ.erase p, a i * u i = 0 := by
    have hn (v : ℂ) (hv : ‖v‖ = 1) :
        ‖a p * v + ∑ i ∈ Finset.univ.erase p, a i * u i‖ = r := by
      have hh := h (fun i => if i = p then v else u i) (by
        intro i
        by_cases hip : i = p
        · simpa only [ite_eq_left hip] using hv
        · simpa only [ite_eq_right hip] using hu i)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)] at hh
      have he : (∑ i ∈ Finset.univ.erase p, a i * (if i = p then v else u i)) =
          ∑ i ∈ Finset.univ.erase p, a i * u i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ite_eq_right (Finset.mem_erase.mp hi).1]
      simpa only [ite_true, he] using hh
    apply (four_phase_zero (a p) (∑ i ∈ Finset.univ.erase p, a i * u i)
      (by simpa using (hn (-1) (by simp)).trans (hn 1 (by simp)).symm)
      (by simpa [mul_comm] using
        (hn Complex.I (by simp)).trans (hn 1 (by simp)).symm)).resolve_left hp
  have hbase := hpartial (fun _ => 1) (by simp)
  have hflip := hpartial (fun i => if i = q then -1 else 1) (by intro i; split_ifs <;> simp)
  have hqmem : q ∈ Finset.univ.erase p := Finset.mem_erase.mpr ⟨Ne.symm hpq, by simp⟩
  rw [← Finset.add_sum_erase _ _ hqmem] at hbase hflip
  simp only [mul_one] at hbase
  have hrest : (∑ i ∈ (Finset.univ.erase p).erase q,
      a i * (if i = q then -1 else 1)) =
      ∑ i ∈ (Finset.univ.erase p).erase q, a i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_right (Finset.mem_erase.mp hi).1, mul_one]
  rw [ite_eq_left rfl, mul_neg_one, hrest] at hflip
  have : 2 * a q = 0 := by linear_combination hbase - hflip
  exact (mul_eq_zero.mp this).resolve_left (by norm_num)

private lemma span_reconstruction {m : ℕ} (φ : Fin m → EuclideanSpace ℂ (Fin 4))
    (ho : Orthonormal ℂ φ) (x : EuclideanSpace ℂ (Fin 4))
    (hx : x ∈ Submodule.span ℂ (Set.range φ)) :
    ∑ p, ⟪φ p, x⟫_ℂ • φ p = x := by
  classical
  let b : OrthonormalBasis (Fin m) ℂ (Submodule.span ℂ (Set.range φ)) :=
    (Module.Basis.span ho.linearIndependent).toOrthonormalBasis (by
      have he : ⇑(Module.Basis.span ho.linearIndependent) =
          fun i => ⟨φ i, Submodule.subset_span (Set.mem_range_self i)⟩ := by
        funext i; exact Module.Basis.span_apply ho.linearIndependent i
      rw [he]
      exact orthonormal_span ho)
  have he := congrArg (fun z : Submodule.span ℂ (Set.range φ) =>
    (z : EuclideanSpace ℂ (Fin 4))) (b.sum_repr' ⟨x, hx⟩)
  simpa [b, Module.Basis.coe_toOrthonormalBasis, Module.Basis.span_apply] using he

private lemma phase_state {m : ℕ} (φ : Fin m → EuclideanSpace ℂ (Fin 4))
    (r : Fin m → ℝ) (ho : Orthonormal ℂ φ) (hr : ∀ p, 0 < r p)
    (x : EuclideanSpace ℂ (Fin 4)) (hx : ‖x‖ = 1)
    (hcoeff : ∀ p, ‖⟪φ p, x⟫_ℂ‖ = r p)
    (hspan : x ∈ Submodule.span ℂ (Set.range φ))
    (u : Fin m → ℂ) (hu : ∀ p, ‖u p‖ = 1) :
    ‖∑ p, ((r p : ℂ) * u p) • φ p‖ = 1 ∧
      ∀ p, ‖⟪φ p, ∑ q, ((r q : ℂ) * u q) • φ q⟫_ℂ‖ = r p := by
  have energy (c : Fin m → ℂ) :
      ‖∑ p, c p • φ p‖ ^ 2 = ∑ p, ‖c p‖ ^ 2 := by
    simpa only [LinearIsometry.toSpanSingleton_apply] using
      ho.orthogonalFamily.norm_sum c Finset.univ
  have hsum : ∑ p, (r p) ^ 2 = 1 := by
    have he := energy (fun p => ⟪φ p, x⟫_ℂ)
    rw [span_reconstruction φ ho x hspan, hx] at he
    simpa only [hcoeff, one_pow] using he.symm
  have hnorm (p : Fin m) : ‖(r p : ℂ) * u p‖ = r p := by
    rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr p)]
  constructor
  · have he := energy (fun p => (r p : ℂ) * u p)
    simp only [hnorm, hsum] at he
    nlinarith [norm_nonneg (∑ p, ((r p : ℂ) * u p) • φ p)]
  · intro p
    rw [ho.inner_right_fintype]
    exact hnorm p

private lemma coordinate_sum {m : ℕ} (c : Fin m → ℂ)
    (φ : Fin m → EuclideanSpace ℂ (Fin 4)) (j : Fin 4) :
    (∑ p, c p • φ p) j = ∑ p, c p * φ p j := by
  change (EuclideanSpace.projₗ j) (∑ p, c p • φ p) = _
  simp only [map_sum, map_smul, smul_eq_mul]
  rfl

private lemma disjoint_generators {m : ℕ}
    (φ : Fin m → EuclideanSpace ℂ (Fin 4)) (r : Fin m → ℝ)
    (_ho : Orthonormal ℂ φ) (hr : ∀ p, 0 < r p)
    (hs : ∀ u : Fin m → ℂ, (∀ p, ‖u p‖ = 1) →
      (∑ p, ((r p : ℂ) * u p) • φ p) ∈ counterexample) :
    ∀ j p q, p ≠ q → φ p j = 0 ∨ φ q j = 0 := by
  intro j p q hpq
  have hn : ∀ u : Fin m → ℂ, (∀ p, ‖u p‖ = 1) →
      ‖∑ p, ((r p : ℂ) * φ p j) * u p‖ = radii j := by
    intro u hu
    have he := (hs u hu).2.2 j
    simpa only [coordinate_sum,
      mul_assoc, mul_comm, mul_left_comm] using he
  have he := constant_modulus (fun p => (r p : ℂ) * φ p j) (radii j) hn p q hpq
  have hrp : (r p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hr p))
  have hrq : (r q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hr q))
  exact he.imp (fun h => (mul_eq_zero.mp h).resolve_left hrp)
    (fun h => (mul_eq_zero.mp h).resolve_left hrq)

private lemma weighted_block (a b : Fin 4 → ℂ)
    (ha : a 0 + a 1 + a 2 + a 3 = 0) (hb : b 0 + b 1 + b 2 + b 3 = 0)
    (hd : ∀ j, a j = 0 ∨ b j = 0)
    (hn : ∀ j : Fin 3, a j.castSucc = 0 ∨ ‖a j.castSucc‖ = 1)
    (h3 : ‖a 3‖ = 2) : b = 0 := by
  have ha3 : a 3 ≠ 0 := by intro he; simp [he] at h3
  have hb3 : b 3 = 0 := (hd 3).resolve_left ha3
  have hsingle (j : Fin 3) (he : a 3 = -a j.castSucc)
      (hj : a j.castSucc ≠ 0) : False := by
    have hjn := (hn j).resolve_left hj
    rw [he, norm_neg, hjn] at h3
    norm_num at h3
  by_cases h0 : a 0 = 0 <;> by_cases h1 : a 1 = 0 <;> by_cases h2 : a 2 = 0
  · exfalso
    apply ha3
    simpa only [h0, h1, h2, zero_add] using ha
  · exact (hsingle 2 (by change a 3 = -a 2; linear_combination ha - h0 - h1) h2).elim
  · exact (hsingle 1 (by change a 3 = -a 1; linear_combination ha - h0 - h2) h1).elim
  · have hb1 := (hd 1).resolve_left h1
    have hb2 := (hd 2).resolve_left h2
    have hb0 : b 0 = 0 := by simpa [hb1, hb2, hb3] using hb
    funext j; fin_cases j <;> assumption
  · exact (hsingle 0 (by change a 3 = -a 0; linear_combination ha - h1 - h2) h0).elim
  · have hb0 := (hd 0).resolve_left h0
    have hb2 := (hd 2).resolve_left h2
    have hb1 : b 1 = 0 := by simpa [hb0, hb2, hb3] using hb
    funext j; fin_cases j <;> assumption
  · have hb0 := (hd 0).resolve_left h0
    have hb1 := (hd 1).resolve_left h1
    have hb2 : b 2 = 0 := by simpa [hb0, hb1, hb3] using hb
    funext j; fin_cases j <;> assumption
  · have hb0 := (hd 0).resolve_left h0
    have hb1 := (hd 1).resolve_left h1
    have hb2 := (hd 2).resolve_left h2
    funext j; fin_cases j <;> assumption

private lemma phase_coefficient_zero {m : ℕ} (a : Fin m → ℂ)
    (h : ∀ u : Fin m → ℂ, (∀ p, ‖u p‖ = 1) → ∑ p, a p * u p = 0) :
    ∀ p, a p = 0 := by
  classical
  intro p
  have hbase := h (fun _ => 1) (by simp)
  have hflip := h (fun q => if q = p then -1 else 1) (by intro q; split_ifs <;> simp)
  have he (q : Fin m) : a q * (if q = p then -1 else 1) =
      a q - (if q = p then 2 * a p else 0) := by
    by_cases hq : q = p
    · subst q; simp; ring
    · simp [hq]
  simp_rw [he] at hflip
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at hflip
  simp only [mul_one] at hbase
  have hz : 2 * a p = 0 := by linear_combination hbase - hflip
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

private lemma block_obstruction {m : ℕ}
    (φ : Fin m → EuclideanSpace ℂ (Fin 4)) (r : Fin m → ℝ)
    (ho : Orthonormal ℂ φ) (hr : ∀ p, 0 < r p)
    (hd : ∀ j p q, p ≠ q → φ p j = 0 ∨ φ q j = 0)
    (hs : ∀ u : Fin m → ℂ, (∀ p, ‖u p‖ = 1) →
      (∑ p, ((r p : ℂ) * u p) • φ p) ∈ counterexample) : m ≤ 1 := by
  classical
  let v : EuclideanSpace ℂ (Fin 4) := ∑ p, (r p : ℂ) • φ p
  have hv : v ∈ counterexample := by simpa [v] using hs (fun _ => 1) (by simp)
  have hker (p : Fin m) : constraint (φ p) = 0 := by
    have he := phase_coefficient_zero (fun p => (r p : ℂ) * constraint (φ p)) (by
      intro u hu
      have hh := (hs u hu).1
      change constraint (∑ p, ((r p : ℂ) * u p) • φ p) = 0 at hh
      simpa only [map_sum, map_smul, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
        using hh) p
    exact (mul_eq_zero.mp he).resolve_left
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (hr p)))
  let b (p : Fin m) (j : Fin 4) : ℂ :=
    ((![6, 3, 2, 3] j : ℝ) : ℂ) * ((r p : ℂ) * φ p j) * (Real.sqrt 30 : ℂ) / 6
  have hbsum (p : Fin m) : b p 0 + b p 1 + b p 2 + b p 3 = 0 := by
    have he := hker p
    change 6 * φ p 0 + 3 * φ p 1 + 2 * φ p 2 + 3 * φ p 3 = 0 at he
    dsimp [b]
    linear_combination (r p : ℂ) * (Real.sqrt 30 : ℂ) / 6 * he
  have hbnorm (p : Fin m) (j : Fin 4) (hpj : φ p j ≠ 0) :
      ‖b p j‖ = ![1, 1, 1, 2] j := by
    have he : v j = (r p : ℂ) * φ p j := by
      simp only [v, coordinate_sum]
      apply Finset.sum_eq_single p
      · intro q _ hqp
        rw [(hd j p q (Ne.symm hqp)).resolve_left hpj, mul_zero]
      · simp
    have hc := hv.2.2 j
    rw [he] at hc
    have hsqrt : 0 < Real.sqrt (30 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
    simp only [b, norm_div, norm_mul, Complex.norm_real,
      Complex.norm_ofNat, hc]
    dsimp only [radii]
    fin_cases j <;> norm_num [abs_of_pos hsqrt] <;> field_simp <;> ring
  have hbd (p q : Fin m) (hpq : p ≠ q) (j : Fin 4) : b p j = 0 ∨ b q j = 0 := by
    rcases hd j p q hpq with hp | hq
    · left; simp [b, hp]
    · right; simp [b, hq]
  have hex : ∃ p : Fin m, φ p 3 ≠ 0 := by
    by_contra! hn
    have he : v 3 = 0 := by simp only [v, coordinate_sum, hn, mul_zero, Finset.sum_const_zero]
    have hc := hv.2.2 3
    rw [he, norm_zero] at hc
    linarith [radii_pos 3]
  obtain ⟨p, hp⟩ := hex
  have hunique (q : Fin m) : q = p := by
    by_contra hqp
    have hbq : b q = 0 := weighted_block (b p) (b q) (hbsum p) (hbsum q)
      (hbd p q (Ne.symm hqp)) (by
        intro j
        by_cases hj : φ p j.castSucc = 0
        · left; simp [b, hj]
        · right
          have he := hbnorm p j.castSucc hj
          fin_cases j <;> simpa using he) (hbnorm p 3 hp)
    have hφ : φ q = 0 := by
      ext j
      by_contra hj
      have he := hbnorm q j hj
      rw [hbq] at he
      fin_cases j <;> norm_num at he
    have he := ho.norm_eq_one q
    rw [hφ, norm_zero] at he
    norm_num at he
  by_contra hm
  have htwo : 2 ≤ m := by omega
  have he := (hunique ⟨0, by omega⟩).trans (hunique ⟨1, by omega⟩).symm
  have := congrArg Fin.val he
  norm_num at this

private lemma hyperdisk_single_ray (h : Set (EuclideanSpace ℂ (Fin 4)))
    (hh : IsHyperdisk h) (hc : h ⊆ counterexample)
    (x : EuclideanSpace ℂ (Fin 4)) (hx : x ∈ h)
    (y : EuclideanSpace ℂ (Fin 4)) (hy : y ∈ h) : ∃ u : ℂ, x = u • y := by
  obtain ⟨m, φ, r, ho, hspan, hr, hset⟩ := hh
  have hxspan : x ∈ Submodule.span ℂ (Set.range φ) := by
    rw [hspan]; exact Submodule.subset_span hx
  have hyspan : y ∈ Submodule.span ℂ (Set.range φ) := by
    rw [hspan]; exact Submodule.subset_span hy
  have hxdata : ‖x‖ = 1 ∧ ∀ p, ‖⟪φ p, x⟫_ℂ‖ = r p := by
    simpa only [hset, Set.mem_ofPred_eq] using hx
  have hydata : ‖y‖ = 1 ∧ ∀ p, ‖⟪φ p, y⟫_ℂ‖ = r p := by
    simpa only [hset, Set.mem_ofPred_eq] using hy
  have hs : ∀ u : Fin m → ℂ, (∀ p, ‖u p‖ = 1) →
      (∑ p, ((r p : ℂ) * u p) • φ p) ∈ counterexample := by
    intro u hu
    apply hc
    rw [hset]
    exact phase_state φ r ho hr x hxdata.1 hxdata.2 hxspan u hu
  have hm := block_obstruction φ r ho hr (disjoint_generators φ r ho hr hs) hs
  have hxr := span_reconstruction φ ho x hxspan
  have hyr := span_reconstruction φ ho y hyspan
  have hmpos : 0 < m := by
    by_contra hn
    have hxzero : x = 0 := hxr.symm.trans (Finset.sum_eq_zero (by
      intro p _
      have hp := p.isLt
      omega))
    have he := hxdata.1
    rw [hxzero, norm_zero] at he
    norm_num at he
  let p : Fin m := ⟨0, hmpos⟩
  have hp (q : Fin m) : q = p := by
    exact @Subsingleton.elim (Fin m) (Fin.subsingleton_iff_le_one.mpr hm) q p
  have reduce (v : EuclideanSpace ℂ (Fin 4)) :
      (∑ q, ⟪φ q, v⟫_ℂ • φ q) = ⟪φ p, v⟫_ℂ • φ p := by
    apply Finset.sum_eq_single p
    · intro q _ hqp; exact (hqp (hp q)).elim
    · simp
  have hxr1 := (reduce x).symm.trans hxr
  have hyr1 := (reduce y).symm.trans hyr
  have hy0 : ⟪φ p, y⟫_ℂ ≠ 0 := by
    intro he
    have hn := hydata.2 p
    rw [he, norm_zero] at hn
    linarith [hr p]
  refine ⟨⟪φ p, x⟫_ℂ / ⟪φ p, y⟫_ℂ, ?_⟩
  calc
    x = ⟪φ p, x⟫_ℂ • φ p := hxr1.symm
    _ = (⟪φ p, x⟫_ℂ / ⟪φ p, y⟫_ℂ) • (⟪φ p, y⟫_ℂ • φ p) := by
      rw [smul_smul, div_mul_cancel₀ _ hy0]
    _ = (⟪φ p, x⟫_ℂ / ⟪φ p, y⟫_ℂ) • y := by rw [hyr1]

/-- The registered four-coordinate regular subset refutes the finite-cover question. -/
theorem result : ¬ claim := by
  intro hclaim
  obtain ⟨k, h, hh, hcover⟩ := hclaim 4 ambient counterexample regular
  have hmem (a : ℕ) : ∃ i, family a ∈ h i := by
    have ha := family_mem a
    rw [hcover] at ha
    exact Set.mem_iUnion.mp ha
  choose f hf using hmem
  have hinj : Function.Injective f := by
    intro a b hab
    obtain ⟨u, hu⟩ := hyperdisk_single_ray (h (f a)) (hh (f a)).1 (hh (f a)).2
      (family a) (hf a) (family b) (hab ▸ hf b)
    exact family_ray_injective a b u hu
  have : Finite ℕ := Finite.of_injective f hinj
  exact (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) Set.finite_univ

end D5.S3.Quantum.Masking.HyperdiskRegularSubsetCover
