/- GID: D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement
   generality: I
   mirror-B: D5/B/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The symmetric coin maximizes full-mode geometric entanglement on every circle. -/

import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays

/-! The circle walk, its single-excitation vector, and full-mode product overlaps. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate

namespace D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement

/-- A normalized two-component coin, with component zero denoting the left mover. -/
def unitCoin (c : Fin 2 → ℂ) : Prop := ∑ b, Complex.normSq (c b) = 1

/-- The Hadamard coin followed by the controlled periodic shift. -/
def hadamardStep (p : ℕ) (ψ : Fin 2 × ZMod p → ℂ) : Fin 2 × ZMod p → ℂ :=
  fun j => if j.1 = 0 then
    (ψ (0, j.2 + 1) + ψ (1, j.2 + 1)) / (Real.sqrt 2 : ℂ)
  else (ψ (0, j.2 - 1) - ψ (1, j.2 - 1)) / (Real.sqrt 2 : ℂ)

/-- The localized coin after `n` steps of the source's circle walk. -/
def walkState (p n : ℕ) (c : Fin 2 → ℂ) : Fin 2 × ZMod p → ℂ :=
  (hadamardStep p)^[n] (fun j => if j.2 = 0 then c j.1 else 0)

/-- The symmetric source coin, with angles `θ = φ = π / 2`. -/
def cStar : Fin 2 → ℂ := ![1 / (Real.sqrt 2 : ℂ), Complex.I / (Real.sqrt 2 : ℂ)]

/-- The generalized W vector in the computational basis of all individual modes. -/
def wState {ι : Type*} [Fintype ι] (lam : ι → ℂ) : (ι → Bool) → ℂ := by
  classical
  exact fun s => ∑ k, if s = Function.update (fun _ => false) k true then lam k else 0

/-- An ordinary tensor product of the two-component local vectors. -/
def productState {ι : Type*} [Fintype ι] (z : ι → Fin 2 → ℂ) : (ι → Bool) → ℂ :=
  fun s => ∏ k, z k (if s k then 1 else 0)

/-- Every local vector has unit Hilbert norm. -/
def unitFactors {ι : Type*} (z : ι → Fin 2 → ℂ) : Prop := ∀ k, unitCoin (z k)

/-- The standard inner product of a product vector with the generalized W vector. -/
def overlap {ι : Type*} [Fintype ι] (lam : ι → ℂ) (z : ι → Fin 2 → ℂ) : ℂ := by
  classical
  exact ∑ s : ι → Bool, conj (productState z s) * wState lam s

/-- The full-partition maximum product overlap squared. -/
def gMax {ι : Type*} [Fintype ι] (lam : ι → ℂ) : ℝ :=
  sSup {t | ∃ z : ι → Fin 2 → ℂ, unitFactors z ∧ t = Complex.normSq (overlap lam z)}

/-- The source's pure-state geometric measure for the partition into individual modes. -/
def geometricEntanglement {ι : Type*} [Fintype ι] (lam : ι → ℂ) : ℝ := 1 - gMax lam

/-- The source expectation, for every positive circle size, time, and normalized coin. -/
def claim : Prop :=
  ∀ (p : ℕ) (hp : 1 ≤ p) (n : ℕ) (c : Fin 2 → ℂ), unitCoin c →
    letI : NeZero p := ⟨by omega⟩
    geometricEntanglement (walkState p n c) ≤ geometricEntanglement (walkState p n cStar)

private lemma overlap_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] (lam : ι → ℂ)
    (z : ι → Fin 2 → ℂ) : overlap lam z =
      ∑ k, lam k * conj (z k 1 * ∏ l ∈ Finset.univ.erase k, z l 0) := by
  classical
  unfold overlap wState
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [mul_comm]
  congr 2
  unfold productState
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  apply congrArg₂ (· * ·)
  · simp only [Function.update_same, Bool.true_eq_true, if_true]
  · apply Finset.prod_congr rfl
    intro l hl
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
    rfl

private lemma overlap_bounded {ι : Type*} [Fintype ι] (lam : ι → ℂ) :
    BddAbove {t | ∃ z : ι → Fin 2 → ℂ,
      unitFactors z ∧ t = Complex.normSq (overlap lam z)} := by
  classical
  refine ⟨∑ s : ι → Bool, ‖wState lam s‖ ^ 2, ?_⟩
  rintro t ⟨z, hz, rfl⟩
  have hprod : (∑ s : ι → Bool, ‖productState z s‖ ^ 2) = 1 := by
    unfold productState
    simp only [norm_prod, ← Finset.prod_pow]
    rw [← Fintype.prod_sum]
    calc
      _ = ∏ k : ι, (1 : ℝ) := by
        apply Finset.prod_congr rfl
        intro k hk
        have h := hz k
        unfold unitCoin at h
        rw [Fin.sum_univ_two] at h
        simpa only [Fintype.sum_bool, Bool.cond_false, Bool.cond_true,
          Complex.normSq_eq_norm_sq, add_comm] using h
      _ = 1 := Finset.prod_const_one
  have h := D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays.cs_sq
    (productState z) (wState lam)
  change ‖overlap lam z‖ ^ 2 ≤ _ at h
  rw [hprod, one_mul] at h
  exact (Complex.normSq_eq_norm_sq _).symm ▸ h

private lemma overlap_attained {ι : Type*} [Fintype ι] (lam : ι → ℂ) :
    ∃ z : ι → Fin 2 → ℂ, unitFactors z ∧ gMax lam = Complex.normSq (overlap lam z) := by
  classical
  have hclosed : IsClosed {c : Fin 2 → ℂ | unitCoin c} := by
    unfold unitCoin
    exact isClosed_eq (by fun_prop) continuous_const
  have hlocal : IsCompact {c : Fin 2 → ℂ | unitCoin c} := by
    apply (isCompact_closedBall (0 : Fin 2 → ℂ) 1).of_isClosed_subset hclosed
    intro c hc
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro b
    have h := hc
    unfold unitCoin at h
    rw [Fin.sum_univ_two] at h
    fin_cases b <;>
      nlinarith [Complex.normSq_eq_norm_sq (c 0), Complex.normSq_eq_norm_sq (c 1),
        Complex.normSq_nonneg (c 0), Complex.normSq_nonneg (c 1), norm_nonneg (c 0),
        norm_nonneg (c 1)]
  have hcompact : IsCompact {z : ι → Fin 2 → ℂ | unitFactors z} := by
    exact (show IsCompact (Set.pi Set.univ (fun _ : ι => {c | unitCoin c})) from
      isCompact_univ_pi (fun _ => hlocal))
  have hnonempty : Set.Nonempty {z : ι → Fin 2 → ℂ | unitFactors z} := by
    refine ⟨fun _ => ![1, 0], ?_⟩
    intro k
    unfold unitCoin
    norm_num [Fin.sum_univ_two]
  have hcont : Continuous (fun z : ι → Fin 2 → ℂ => Complex.normSq (overlap lam z)) := by
    unfold overlap productState
    fun_prop
  obtain ⟨z, hz, hmax⟩ := hcompact.exists_isMaxOn hnonempty hcont.continuousOn
  refine ⟨z, hz, le_antisymm ?_ ?_⟩
  · unfold gMax
    apply csSup_le ⟨Complex.normSq (overlap lam z), z, hz, rfl⟩
    rintro t ⟨w, hw, rfl⟩
    exact hmax hw
  · exact le_csSup (overlap_bounded lam) ⟨z, hz, rfl⟩

private lemma phase_invariance {ι : Type*} [Fintype ι] (lam μ : ι → ℂ)
    (h : ∀ k, Complex.normSq (lam k) = Complex.normSq (μ k)) : gMax lam = gMax μ := by
  sorry

private lemma quadratic_max (d e f : ℝ) (hf : 0 ≤ f) :
    let t := (d + e + Real.sqrt ((d - e) ^ 2 + 4 * f ^ 2)) / 2
    ∃ y : Fin 2 → ℝ, (∀ k, 0 ≤ y k) ∧ y 0 ^ 2 + y 1 ^ 2 = 1 ∧
      d * y 0 ^ 2 + 2 * f * y 0 * y 1 + e * y 1 ^ 2 = t ∧
      ∀ v : Fin 2 → ℝ, v 0 ^ 2 + v 1 ^ 2 = 1 →
        d * v 0 ^ 2 + 2 * f * v 0 * v 1 + e * v 1 ^ 2 ≤ t := by
  dsimp only
  set t := (d + e + Real.sqrt ((d - e) ^ 2 + 4 * f ^ 2)) / 2
  have hdsc : 0 ≤ (d - e) ^ 2 + 4 * f ^ 2 := by positivity
  have hs := Real.sq_sqrt hdsc
  have habs : |d - e| ≤ Real.sqrt ((d - e) ^ 2 + 4 * f ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    nlinarith [sq_nonneg f]
  have htd : 0 ≤ t - d := by dsimp [t]; linarith [(abs_le.mp habs).2]
  have hte : 0 ≤ t - e := by dsimp [t]; linarith [(abs_le.mp habs).1]
  have hroot : (t - d) * (t - e) = f ^ 2 := by dsimp [t]; nlinarith only [hs]
  have hbound (v : Fin 2 → ℝ) (hv : v 0 ^ 2 + v 1 ^ 2 = 1) :
      d * v 0 ^ 2 + 2 * f * v 0 * v 1 + e * v 1 ^ 2 ≤ t := by
    by_cases hz : t - e = 0
    · have hfz : f = 0 := by rw [hz, mul_zero] at hroot; nlinarith
      rw [hfz]
      have heq : e * (v 0 ^ 2 + v 1 ^ 2) = t := by
        rw [hv, mul_one]
        exact (sub_eq_zero.mp hz).symm
      have hn : 0 ≤ (e - d) * v 0 ^ 2 := by
        rw [← sub_eq_zero.mp hz]
        exact mul_nonneg htd (sq_nonneg (v 0))
      nlinarith only [heq, hn]
    · have hpos : 0 < t - e := lt_of_le_of_ne hte (Ne.symm hz)
      have hid : (t - e) * (t - (d * v 0 ^ 2 + 2 * f * v 0 * v 1 + e * v 1 ^ 2)) =
          ((t - e) * v 1 - f * v 0) ^ 2 := by
        calc
          _ = ((t - e) * v 1 - f * v 0) ^ 2 +
              (t - e) * t * (1 - (v 0 ^ 2 + v 1 ^ 2)) +
              ((t - d) * (t - e) - f ^ 2) * v 0 ^ 2 := by ring
          _ = _ := by rw [hv, hroot]; ring
      have hn : 0 ≤ (t - e) *
          (t - (d * v 0 ^ 2 + 2 * f * v 0 * v 1 + e * v 1 ^ 2)) := by
        rw [hid]; exact sq_nonneg _
      exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hn hpos)
  by_cases hz : t - e = 0
  · refine ⟨![0, 1], ?_, by norm_num, ?_, hbound⟩
    · intro k; fin_cases k <;> norm_num
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      nlinarith
  · let k := Real.sqrt ((t - e) ^ 2 + f ^ 2)
    have hkpos : 0 < k := Real.sqrt_pos.2 (by nlinarith [sq_pos_of_ne_zero hz, sq_nonneg f])
    have hks : k ^ 2 = (t - e) ^ 2 + f ^ 2 := Real.sq_sqrt (by positivity)
    refine ⟨![(t - e) / k, f / k], ?_, ?_, ?_, hbound⟩
    · intro i; fin_cases i
      · exact div_nonneg hte hkpos.le
      · exact div_nonneg hf hkpos.le
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, div_pow]
      rw [← add_div, ← hks, div_self (pow_ne_zero 2 hkpos.ne')]
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp [hkpos.ne']
      rw [hks]
      linear_combination -(t - e) * hroot

private lemma two_factor_max (a b r s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    ∃ x y : Fin 2 → ℝ,
      (∀ k, 0 ≤ x k) ∧ (∀ k, 0 ≤ y k) ∧
      x 0 ^ 2 + x 1 ^ 2 = 1 ∧ y 0 ^ 2 + y 1 ^ 2 = 1 ∧
      (a * x 0 * y 0 + b * s * x 0 * y 1 + b * r * x 1 * y 0) ^ 2 =
        ((a ^ 2 + b ^ 2 * (r ^ 2 + s ^ 2)) +
          Real.sqrt ((a ^ 2 + b ^ 2 * (r ^ 2 + s ^ 2)) ^ 2 -
            4 * b ^ 4 * (r ^ 2 * s ^ 2))) / 2 ∧
      ∀ u v : Fin 2 → ℝ, u 0 ^ 2 + u 1 ^ 2 = 1 → v 0 ^ 2 + v 1 ^ 2 = 1 →
        (a * u 0 * v 0 + b * s * u 0 * v 1 + b * r * u 1 * v 0) ^ 2 ≤
          (a * x 0 * y 0 + b * s * x 0 * y 1 + b * r * x 1 * y 0) ^ 2 := by
  obtain ⟨y, hy, hyn, hyt, hbound⟩ :=
    quadratic_max (a ^ 2 + b ^ 2 * r ^ 2) (b ^ 2 * s ^ 2) (a * b * s)
      (by positivity)
  let t := (a ^ 2 + b ^ 2 * (r ^ 2 + s ^ 2) +
    Real.sqrt ((a ^ 2 + b ^ 2 * (r ^ 2 + s ^ 2)) ^ 2 -
      4 * b ^ 4 * (r ^ 2 * s ^ 2))) / 2
  have hdisc : (a ^ 2 + b ^ 2 * r ^ 2 - b ^ 2 * s ^ 2) ^ 2 +
      4 * (a * b * s) ^ 2 =
      (a ^ 2 + b ^ 2 * (r ^ 2 + s ^ 2)) ^ 2 - 4 * b ^ 4 * (r ^ 2 * s ^ 2) := by ring
  have htrace : a ^ 2 + b ^ 2 * r ^ 2 + b ^ 2 * s ^ 2 =
      a ^ 2 + b ^ 2 * (r ^ 2 + s ^ 2) := by ring
  rw [hdisc, htrace] at hyt hbound
  let v : Fin 2 → ℝ := ![a * y 0 + b * s * y 1, b * r * y 0]
  have hy0 := hy 0
  have hy1 := hy 1
  have hv : ∀ k, 0 ≤ v k := by
    intro k; fin_cases k <;> dsimp [v] <;> positivity
  have hvs : v 0 ^ 2 + v 1 ^ 2 = t := by
    calc
      _ = (a ^ 2 + b ^ 2 * r ^ 2) * y 0 ^ 2 +
          2 * (a * b * s) * y 0 * y 1 + b ^ 2 * s ^ 2 * y 1 ^ 2 := by dsimp [v]; ring
      _ = t := hyt
  have ht : 0 ≤ t := by rw [← hvs]; positivity
  have hall (u w : Fin 2 → ℝ) (hu : u 0 ^ 2 + u 1 ^ 2 = 1)
      (hw : w 0 ^ 2 + w 1 ^ 2 = 1) :
      (a * u 0 * w 0 + b * s * u 0 * w 1 + b * r * u 1 * w 0) ^ 2 ≤ t := by
    have hcs := D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays.cs_sq
      ![(u 0 : ℂ), (u 1 : ℂ)]
      ![((a * w 0 + b * s * w 1 : ℝ) : ℂ), ((b * r * w 0 : ℝ) : ℂ)]
    simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, Complex.star_def,
      Matrix.cons_val_zero, Matrix.cons_val_one, Complex.conj_ofReal,
      ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, hu, one_mul] at hcs
    calc
      _ ≤ (a * w 0 + b * s * w 1) ^ 2 + (b * r * w 0) ^ 2 := by
        convert hcs using 1 <;> ring
      _ = (a ^ 2 + b ^ 2 * r ^ 2) * w 0 ^ 2 +
          2 * (a * b * s) * w 0 * w 1 + b ^ 2 * s ^ 2 * w 1 ^ 2 := by ring
      _ ≤ t := hbound w hw
  suffices hex : ∃ x : Fin 2 → ℝ, (∀ k, 0 ≤ x k) ∧ x 0 ^ 2 + x 1 ^ 2 = 1 ∧
      (a * x 0 * y 0 + b * s * x 0 * y 1 + b * r * x 1 * y 0) ^ 2 = t by
    obtain ⟨x, hx, hxn, hxt⟩ := hex
    refine ⟨x, y, hx, hy, hxn, hyn, hxt, ?_⟩
    intro u w hu hw
    rw [hxt]
    exact hall u w hu hw
  by_cases hz : t = 0
  · have hvz : v 0 = 0 := by nlinarith [sq_nonneg (v 1)]
    refine ⟨![1, 0], ?_, by norm_num, ?_⟩
    · intro k; fin_cases k <;> norm_num
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      change (a * 1 * y 0 + b * s * 1 * y 1 + b * r * 0 * y 0) ^ 2 = t
      have : a * y 0 + b * s * y 1 = 0 := hvz
      nlinarith
  · have hk : 0 < Real.sqrt t := Real.sqrt_pos.2 (lt_of_le_of_ne ht (Ne.symm hz))
    have hks : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
    refine ⟨![v 0 / Real.sqrt t, v 1 / Real.sqrt t], ?_, ?_, ?_⟩
    · intro k; fin_cases k
      · exact div_nonneg (hv 0) hk.le
      · exact div_nonneg (hv 1) hk.le
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, div_pow]
      rw [← add_div, hvs, hks, div_self hz]
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have he : a * (v 0 / Real.sqrt t) * y 0 + b * s * (v 0 / Real.sqrt t) * y 1 +
          b * r * (v 1 / Real.sqrt t) * y 0 = (v 0 ^ 2 + v 1 ^ 2) / Real.sqrt t := by
        dsimp [v]; ring
      rw [he, hvs, div_pow, hks, pow_two, mul_div_cancel_right₀ _ hz]

private lemma pair_balancing {ι : Type*} [Fintype ι] (lam μ : ι → ℂ) (i j : ι)
    (hij : i ≠ j)
    (hrest : ∀ k, k ≠ i → k ≠ j → Complex.normSq (μ k) = Complex.normSq (lam k))
    (hsum : Complex.normSq (μ i) + Complex.normSq (μ j) =
      Complex.normSq (lam i) + Complex.normSq (lam j))
    (hprod : Complex.normSq (lam i) * Complex.normSq (lam j) ≤
      Complex.normSq (μ i) * Complex.normSq (μ j)) : gMax μ ≤ gMax lam := by
  sorry

private lemma walk_linearity (p n : ℕ) (c : Fin 2 → ℂ) (j : Fin 2 × ZMod p) :
    walkState p n c j = c 0 * walkState p n ![1, 0] j +
      c 1 * walkState p n ![0, 1] j := by
  sorry

private lemma walk_reflection (p n : ℕ) :
    (∀ j, (walkState p n ![1, 0] j).im = 0 ∧ (walkState p n ![0, 1] j).im = 0) ∧
    (∀ x : ZMod p,
      walkState p n ![1, 0] (1, -x) =
        -(-1 : ℂ) ^ n * walkState p n ![0, 1] (0, x) ∧
      walkState p n ![0, 1] (1, -x) =
        (-1 : ℂ) ^ n * walkState p n ![1, 0] (0, x)) := by
  sorry

private lemma walk_pair_probabilities (p n : ℕ) (c : Fin 2 → ℂ) (hc : unitCoin c) :
    ∀ x : ZMod p,
      Complex.normSq (walkState p n cStar (0, x)) =
        Complex.normSq (walkState p n cStar (1, -x)) ∧
      Complex.normSq (walkState p n cStar (0, x)) +
          Complex.normSq (walkState p n cStar (1, -x)) =
        Complex.normSq (walkState p n c (0, x)) +
          Complex.normSq (walkState p n c (1, -x)) := by
  sorry

private lemma pair_average_le (p : ℕ) [NeZero p] (lam μ : Fin 2 × ZMod p → ℂ)
    (h : ∀ x : ZMod p,
      Complex.normSq (μ (0, x)) = Complex.normSq (μ (1, -x)) ∧
      Complex.normSq (μ (0, x)) + Complex.normSq (μ (1, -x)) =
        Complex.normSq (lam (0, x)) + Complex.normSq (lam (1, -x))) : gMax μ ≤ gMax lam := by
  sorry

theorem result : claim := by
  intro p hp n c hc
  letI : NeZero p := ⟨by omega⟩
  have h := pair_average_le p (walkState p n c) (walkState p n cStar)
    (walk_pair_probabilities p n c hc)
  exact sub_le_sub_left h 1

end D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement
