import D5.S3.Quantum.Matrix.CirculantBraceletNonUnistochastic

/-!
# Closure of bracelet matrices

Conjecture 9 of Rajchel-Mieldzioć, Korzekwa, Puchała and Życzkowski
(arXiv:2101.11288v1). The proof uses orthogonal complex amplitudes for each
input pair and a Euclidean norm of weighted inner-product and minor coordinates.
-/

noncomputable section

open Finset Matrix Complex
open scoped BigOperators ComplexConjugate Real

open D5.S3.Quantum.Matrix.CirculantBraceletNonUnistochastic (IsBracelet)

namespace D5.S3.Quantum.Matrix.BraceletMonoid

private lemma pivot_iff {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (len : ι → ℝ) :
    (∀ r, len r ≤ ∑ s ∈ univ.erase r, len s) ↔
      2 * (⨆ r, len r) ≤ ∑ s, len s := by
  have hsum (r : ι) := sum_erase_add univ len (mem_univ r)
  constructor
  · intro h
    suffices (⨆ r, len r) ≤ (∑ s, len s) / 2 by linarith
    exact ciSup_le fun r => by linarith [h r, hsum r]
  · intro h r
    linarith [le_ciSup (Finite.bddAbove_range len) r, hsum r]

private lemma weighted_lagrange {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (x y : ι → ℂ) :
    ‖∑ i, (t i : ℂ) * (conj (x i) * y i)‖ ^ 2 +
      (∑ ij : ι × ι, t ij.1 * t ij.2 *
        ‖x ij.1 * y ij.2 - x ij.2 * y ij.1‖ ^ 2) / 2 =
      (∑ i, t i * ‖x i‖ ^ 2) * (∑ i, t i * ‖y i‖ ^ 2) := by
  let z (i : ι) := (t i : ℂ) * (conj (x i) * y i)
  let a (i : ι) := t i * ‖x i‖ ^ 2
  let b (i : ι) := t i * ‖y i‖ ^ 2
  let c (i j : ι) := (z i).re * (z j).re + (z i).im * (z j).im
  let m (i j : ι) := t i * t j * ‖x i * y j - x j * y i‖ ^ 2
  have hpoint (i j : ι) : 2 * c i j + m i j = a i * b j + a j * b i := by
    simp only [a, b, c, m, z, Complex.sq_norm, normSq_apply, mul_re, mul_im,
      sub_re, sub_im, conj_re, conj_im, ofReal_re, ofReal_im]
    ring
  have hz : ‖∑ i, z i‖ ^ 2 = ∑ i, ∑ j, c i j := by
    simp only [Complex.sq_norm, normSq_apply, ← reCLM_apply, ← imCLM_apply, map_sum]
    simp only [reCLM_apply, imCLM_apply, c, sum_add_distrib, sum_mul, mul_sum, mul_comm]
  have hab : (∑ i, a i) * (∑ j, b j) = ∑ i, ∑ j, a i * b j := by
    rw [sum_mul]
    simp only [mul_sum]
  have hba : (∑ i, ∑ j, a j * b i) = ∑ i, ∑ j, a i * b j :=
    sum_comm
  have htotal := sum_congr (rfl : (univ : Finset ι) = univ) fun i _ =>
    sum_congr (rfl : (univ : Finset ι) = univ) fun j _ => hpoint i j
  simp only [sum_add_distrib, ← mul_sum] at htotal
  have hab' : (∑ i, a i * (∑ j, b j)) = ∑ i, ∑ j, a i * b j := by
    simp only [mul_sum]
  rw [hba, hab'] at htotal
  change ‖∑ i, z i‖ ^ 2 + (∑ ij : ι × ι, m ij.1 ij.2) / 2 =
    (∑ i, a i) * (∑ j, b j)
  rw [hz, Fintype.sum_prod_type, hab]
  linarith only [htotal]

private lemma signed_sum {ι : Type*} (s : Finset ι)
    (len : ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (h0 : ∀ i, 0 ≤ len i) (hmax : ∀ i, len i ≤ L) :
    ∃ neg : ι → Bool, |∑ i ∈ s, if neg i then -len i else len i| ≤ L := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => false, by simpa using hL⟩
  | @insert i s hi ih =>
    obtain ⟨neg, hneg⟩ := ih
    let a := ∑ j ∈ s, if neg j then -len j else len j
    have ha : -L ≤ a ∧ a ≤ L := abs_le.mp hneg
    refine ⟨Function.update neg i (decide (0 ≤ a)), ?_⟩
    rw [sum_insert hi, Function.update_self]
    have htail :
        (∑ j ∈ s, if Function.update neg i (decide (0 ≤ a)) j then -len j else len j) = a :=
      sum_congr rfl fun j hj => by
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
    rw [htail, abs_le]
    by_cases h : 0 ≤ a
    · simp only [h, decide_true, ite_true]
      constructor <;> linarith [h0 i, hmax i, ha.2]
    · simp only [h, decide_false, Bool.false_eq_true, ite_false]
      constructor <;> linarith [h0 i, hmax i, ha.1]

private lemma polygon {ι : Type*} [Fintype ι] [DecidableEq ι] (len : ι → ℝ)
    (h0 : ∀ i, 0 ≤ len i)
    (hp : ∀ i, len i ≤ ∑ j ∈ univ.erase i, len j) :
    ∃ w : ι → ℂ, (∀ i, ‖w i‖ = len i) ∧ ∑ i, w i = 0 := by
  cases isEmpty_or_nonempty ι with
  | inl h => exact ⟨fun _ => 0, fun i => isEmptyElim i, by simp⟩
  | inr h =>
    obtain ⟨r, _, hr⟩ := exists_max_image univ len (univ_nonempty : (univ : Finset ι).Nonempty)
    let s := univ.erase r
    obtain ⟨neg, hneg⟩ := signed_sum s len (len r) (h0 r) h0
      (fun i => hr i (mem_univ i))
    let θ (i : ι) : ℝ := if neg i then Real.pi else 0
    let w (u : ℝ) (i : ι) : ℂ :=
      (len i : ℂ) * Complex.exp (((u * θ i : ℝ) : ℂ) * I)
    have hw (u : ℝ) (i : ι) : ‖w u i‖ = len i := by
      dsimp only [w]
      rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (h0 i)]
    let f (u : ℝ) := ‖∑ i ∈ s, w u i‖
    have hcontinuous : Continuous f := by
      unfold f w
      fun_prop
    have hstart : f 0 = ∑ i ∈ s, len i := by
      simp only [f, w, zero_mul, ofReal_zero, exp_zero, mul_one, ← Complex.ofReal_sum,
        Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (sum_nonneg fun i _ => h0 i)
    have hend : f 1 = |∑ i ∈ s, if neg i then -len i else len i| := by
      have hone (i : ι) :
          w 1 i = ((if neg i then -len i else len i : ℝ) : ℂ) := by
        cases hneg' : neg i <;> simp [w, θ, hneg', exp_pi_mul_I]
      simp only [f, hone, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    obtain ⟨u, _, hu⟩ := intermediate_value_Icc' zero_le_one hcontinuous.continuousOn
      (show len r ∈ Set.Icc (f 1) (f 0) by
        exact ⟨hend ▸ hneg, hstart ▸ hp r⟩)
    let S := ∑ i ∈ s, w u i
    let v := Function.update (w u) r (-S)
    have hvsum : (∑ i ∈ s, v i) = S :=
      sum_congr rfl fun i hi => Function.update_of_ne (mem_erase.mp hi).1 ..
    refine ⟨v, ?_, ?_⟩
    · intro i
      by_cases he : i = r
      · subst i
        simpa only [v, Function.update_self, norm_neg] using hu
      · dsimp only [v]
        rw [Function.update_of_ne he, hw]
    · rw [← sum_erase_add univ v (mem_univ r)]
      change (∑ i ∈ s, v i) + Function.update (w u) r (-S) r = 0
      rw [hvsum, Function.update_self, add_neg_cancel]

private lemma amplitudes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpair : ∀ r, √(p r * q r) ≤ ∑ s ∈ univ.erase r, √(p s * q s)) :
    ∃ x y : ι → ℂ, (∀ i, ‖x i‖ ^ 2 = p i) ∧ (∀ i, ‖y i‖ ^ 2 = q i) ∧
      ∑ i, conj (x i) * y i = 0 := by
  let len (i : ι) := √(p i * q i)
  obtain ⟨w, hw, hsum⟩ := polygon len (fun _ => Real.sqrt_nonneg _) hpair
  let u (i : ι) : ℂ := if len i = 0 then 1 else w i / (len i : ℂ)
  have hunit (i : ι) : ‖u i‖ = 1 := by
    by_cases h : len i = 0
    · simp [u, h]
    · simp [u, h, hw, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ len i from Real.sqrt_nonneg _)]
  have hphase (i : ι) : (len i : ℂ) * u i = w i := by
    by_cases h : len i = 0
    · have : w i = 0 := norm_eq_zero.mp ((hw i).trans h)
      simp [h, this]
    · dsimp only [u]
      rw [ite_eq_right h, mul_div_cancel₀]
      exact_mod_cast h
  refine ⟨fun i => (√(p i) : ℂ), fun i => (√(q i) : ℂ) * u i, ?_, ?_, ?_⟩
  · intro i
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hp i)]
  · intro i
    simp [hunit, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hq i)]
  · calc
      (∑ i, conj (√(p i) : ℂ) * ((√(q i) : ℂ) * u i)) =
          ∑ i, (len i : ℂ) * u i := by
        apply sum_congr rfl
        intro i _
        rw [conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, ← Real.sqrt_mul (hp i)]
      _ = 0 := by simpa only [hphase] using hsum

private lemma column_preservation {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (T : Matrix ι κ ℝ) (p q : κ → ℝ)
    (hT : ∀ r i, 0 ≤ T r i) (hsums : ∀ i, ∑ r, T r i = 1)
    (hcols : ∀ i j, i ≠ j → ∀ r,
      √(T r i * T r j) ≤ ∑ s ∈ univ.erase r, √(T s i * T s j))
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpair : ∀ i, √(p i * q i) ≤ ∑ j ∈ univ.erase i, √(p j * q j)) :
    ∀ r, √((T.mulVec p) r * (T.mulVec q) r) ≤
      ∑ s ∈ univ.erase r, √((T.mulVec p) s * (T.mulVec q) s) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := amplitudes p q hp hq hpair
  let z (r : ι) : ℂ := ∑ i, (T r i : ℂ) * (conj (x i) * y i)
  let minor (ij : κ × κ) : ℂ := x ij.1 * y ij.2 - x ij.2 * y ij.1
  -- Both orders of each distinct pair occur, so each square has weight one half.
  let scale (ij : κ × κ) : ℝ := √(1 / 2 : ℝ) * ‖minor ij‖
  let coord (r : ι) : Option (κ × κ) → ℝ
    | none => ‖z r‖
    | some ij => √(T r ij.1 * T r ij.2) * scale ij
  let v (r : ι) : EuclideanSpace ℝ (Option (κ × κ)) := WithLp.toLp 2 (coord r)
  have hnorm (r : ι) : ‖v r‖ = √((T.mulVec p) r * (T.mulVec q) r) := by
    have hnonneg : 0 ≤ (T.mulVec p) r * (T.mulVec q) r := by
      exact mul_nonneg (sum_nonneg fun i _ => mul_nonneg (hT r i) (hp i))
        (sum_nonneg fun i _ => mul_nonneg (hT r i) (hq i))
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hnonneg, PiLp.norm_sq_eq_of_L2, Fintype.sum_option]
    simp only [v, coord, Real.norm_eq_abs, sq_abs]
    have hminor (ij : κ × κ) :
        (√(T r ij.1 * T r ij.2) * scale ij) ^ 2 =
          (T r ij.1 * T r ij.2 * ‖minor ij‖ ^ 2) / 2 := by
      dsimp only [scale]
      rw [mul_pow, Real.sq_sqrt (mul_nonneg (hT r _) (hT r _)),
        mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring
    simp_rw [hminor, ← sum_div]
    simpa only [z, minor, mulVec, dotProduct, hx, hy, add_comm] using
      weighted_lagrange (T r) x y
  -- Unit column sums recover the orthogonality of the input amplitudes.
  have hz : ∑ s, z s = 0 := by
    simp only [z]
    rw [sum_comm]
    simp_rw [← sum_mul, ← Complex.ofReal_sum, hsums, ofReal_one, one_mul]
    exact hxy
  intro r
  have hcoord (j : Option (κ × κ)) : coord r j ≤ ∑ s ∈ univ.erase r, coord s j := by
    cases j with
    | none =>
      have hcancel := sum_erase_add univ z (mem_univ r)
      rw [hz] at hcancel
      change ‖z r‖ ≤ ∑ s ∈ univ.erase r, ‖z s‖
      rw [eq_neg_of_add_eq_zero_right hcancel, norm_neg]
      exact norm_sum_le _ _
    | some ij =>
      change √(T r ij.1 * T r ij.2) * scale ij ≤
        ∑ s ∈ univ.erase r, √(T s ij.1 * T s ij.2) * scale ij
      by_cases h : ij.1 = ij.2
      · simp [scale, minor, h]
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (hcols _ _ h r) (by positivity)
  have h0 (j : Option (κ × κ)) : 0 ≤ coord r j := by
    cases j <;> simp only [coord, scale] <;> positivity
  calc
    √((T.mulVec p) r * (T.mulVec q) r) = ‖v r‖ := (hnorm r).symm
    _ ≤ ‖∑ s ∈ univ.erase r, v s‖ := by
      simp only [PiLp.norm_eq_of_L2, Real.norm_eq_abs, sq_abs]
      exact Real.sqrt_le_sqrt (sum_le_sum fun j _ => by
        have hj : (∑ s ∈ univ.erase r, v s) j = ∑ s ∈ univ.erase r, coord s j :=
          map_sum (EuclideanSpace.projₗ (𝕜 := ℝ) j) _ _
        change coord r j ^ 2 ≤ ((∑ s ∈ univ.erase r, v s) j) ^ 2
        rw [hj]
        exact pow_le_pow_left₀ (h0 j) (hcoord j) 2)
    _ ≤ ∑ s ∈ univ.erase r, ‖v s‖ := norm_sum_le _ _
    _ = ∑ s ∈ univ.erase r, √((T.mulVec p) s * (T.mulVec q) s) := by simp only [hnorm]

private lemma columns_mul {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ}
    (hA : IsBracelet A) (hB : IsBracelet B) (k l : Fin d) (hkl : k ≠ l) :
    2 * (⨆ r, √((A * B) r k * (A * B) r l)) ≤
      ∑ r, √((A * B) r k * (A * B) r l) := by
  let : Nonempty (Fin d) := ⟨k⟩
  apply (pivot_iff _).mp
  exact column_preservation A (fun i => B i k) (fun i => B i l)
    (fun _ _ => nonneg_of_mem_doublyStochastic hA.1)
    (sum_col_of_mem_doublyStochastic hA.1)
    (fun i j hij => (pivot_iff _).mpr (hA.2.1 i j hij))
    (fun _ => nonneg_of_mem_doublyStochastic hB.1)
    (fun _ => nonneg_of_mem_doublyStochastic hB.1)
    ((pivot_iff _).mpr (hB.2.1 k l hkl))

private lemma bracelet_transpose {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : IsBracelet A) : IsBracelet A.transpose :=
  ⟨transpose_mem_doublyStochastic_iff.mpr hA.1, hA.2.2, hA.2.1⟩

private lemma columns_one {d : ℕ} (k l : Fin d) (hkl : k ≠ l) :
    2 * (⨆ r, √((1 : Matrix (Fin d) (Fin d) ℝ) r k *
      (1 : Matrix (Fin d) (Fin d) ℝ) r l)) ≤
      ∑ r, √((1 : Matrix (Fin d) (Fin d) ℝ) r k *
        (1 : Matrix (Fin d) (Fin d) ℝ) r l) := by
  let : Nonempty (Fin d) := ⟨k⟩
  have hzero (r : Fin d) : (1 : Matrix (Fin d) (Fin d) ℝ) r k *
      (1 : Matrix (Fin d) (Fin d) ℝ) r l = 0 := by
    by_cases hr : r = k
    · subst r
      simp [hkl]
    · simp [Matrix.one_apply, hr]
  simp [hzero]

/-- The identity and ordinary products of bracelet matrices are bracelet in every dimension. -/
theorem bracelet_monoid (d : ℕ) :
    IsBracelet (1 : Matrix (Fin d) (Fin d) ℝ) ∧
      ∀ A B : Matrix (Fin d) (Fin d) ℝ, IsBracelet A → IsBracelet B → IsBracelet (A * B) := by
  constructor
  · refine ⟨(doublyStochastic ℝ (Fin d)).one_mem, ?_, ?_⟩
    · exact columns_one
    · intro k l hkl
      have h := columns_one k l hkl
      have htranspose : (1 : Matrix (Fin d) (Fin d) ℝ).transpose = 1 :=
        Matrix.transpose_one
      rw [← htranspose] at h
      exact h
  · intro A B hA hB
    refine ⟨(doublyStochastic ℝ (Fin d)).mul_mem hA.1 hB.1, columns_mul hA hB, ?_⟩
    intro k l hkl
    simpa only [← Matrix.transpose_mul, Matrix.transpose_apply] using
      columns_mul (bracelet_transpose hB) (bracelet_transpose hA) k l hkl

end D5.S3.Quantum.Matrix.BraceletMonoid
