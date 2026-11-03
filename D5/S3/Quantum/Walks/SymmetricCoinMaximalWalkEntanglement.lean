/- GID: D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement
   generality: I
   mirror-B: D5/B/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The symmetric coin maximizes full-mode geometric entanglement on every circle. -/

import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays
import D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry

/-! The circle walk, its single-excitation vector, and full-mode product overlaps. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate

namespace D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement

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
def unitFactors {ι : Type*} (z : ι → Fin 2 → ℂ) : Prop := ∀ k, D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor (z k)

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
  ∀ (p : ℕ) (hp : 1 ≤ p) (n : ℕ) (c : Fin 2 → ℂ), D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor c →
    letI : NeZero p := ⟨by omega⟩
    geometricEntanglement (walkState p n c) ≤ geometricEntanglement (walkState p n cStar)

open Classical in
private lemma overlap_expansion {ι : Type*} [Fintype ι] (lam : ι → ℂ)
    (z : ι → Fin 2 → ℂ) : overlap lam z =
      ∑ k, lam k * conj (z k 1 * ∏ l ∈ Finset.univ.erase k, z l 0) := by
  classical
  unfold overlap wState
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [mul_comm]
  congr 2
  unfold productState
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  apply congrArg₂ (· * ·)
  · simp only [Function.update_self, ite_true]
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
    rw [← Fintype.prod_sum (fun k (b : Bool) => ‖z k (if b then 1 else 0)‖ ^ 2)]
    calc
      _ = ∏ k : ι, (1 : ℝ) := by
        apply Finset.prod_congr rfl
        intro k hk
        have h := hz k
        unfold D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor at h
        rw [Fin.sum_univ_two] at h
        simpa only [Fintype.sum_bool, Bool.cond_false, Bool.cond_true,
          Bool.false_eq_true, ite_false, ite_true,
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
  have hclosed : IsClosed {c : Fin 2 → ℂ | D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor c} := by
    unfold D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor
    exact isClosed_eq (by fun_prop) continuous_const
  have hlocal : IsCompact {c : Fin 2 → ℂ | D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor c} := by
    apply (isCompact_closedBall (0 : Fin 2 → ℂ) 1).of_isClosed_subset hclosed
    intro c hc
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro b
    have h := hc
    change (∑ t, Complex.normSq (c t)) = 1 at h
    rw [Fin.sum_univ_two] at h
    fin_cases b
    · change ‖c 0‖ ≤ 1
      nlinarith [Complex.normSq_eq_norm_sq (c 0), Complex.normSq_eq_norm_sq (c 1),
        Complex.normSq_nonneg (c 0), Complex.normSq_nonneg (c 1), norm_nonneg (c 0),
        norm_nonneg (c 1)]
    · change ‖c 1‖ ≤ 1
      nlinarith [Complex.normSq_eq_norm_sq (c 0), Complex.normSq_eq_norm_sq (c 1),
        Complex.normSq_nonneg (c 0), Complex.normSq_nonneg (c 1), norm_nonneg (c 0),
        norm_nonneg (c 1)]
  have hcompact : IsCompact {z : ι → Fin 2 → ℂ | unitFactors z} := by
    have heq : {z : ι → Fin 2 → ℂ | unitFactors z} =
        Set.pi Set.univ (fun _ : ι => {c | D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor c}) := by
      ext z
      exact Set.mem_univ_pi.symm
    rw [heq]
    exact isCompact_univ_pi (fun _ => hlocal)
  have hnonempty : Set.Nonempty {z : ι → Fin 2 → ℂ | unitFactors z} := by
    refine ⟨fun _ => ![1, 0], ?_⟩
    intro k
    unfold D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor
    norm_num [Fin.sum_univ_two]
  have hcont : Continuous (fun z : ι → Fin 2 → ℂ => Complex.normSq (overlap lam z)) := by
    unfold overlap productState
    fun_prop
  obtain ⟨z, hz, hmax⟩ := hcompact.exists_isMaxOn hnonempty hcont.continuousOn
  refine ⟨z, hz, le_antisymm ?_ ?_⟩
  · unfold gMax
    refine csSup_le ?_ ?_
    · exact ⟨Complex.normSq (overlap lam z), z, hz, rfl⟩
    · rintro t ⟨w, hw, rfl⟩
      exact (isMaxOn_iff.mp hmax) w hw
  · exact le_csSup (overlap_bounded lam) ⟨z, hz, rfl⟩

private lemma phase_transport {ι : Type*} [Fintype ι] (lam μ : ι → ℂ)
    (h : ∀ k, Complex.normSq (lam k) = Complex.normSq (μ k))
    (z : ι → Fin 2 → ℂ) (hz : unitFactors z) :
    ∃ w : ι → Fin 2 → ℂ, unitFactors w ∧ overlap μ w = overlap lam z := by
  classical
  let ρ : ι → ℂ := fun k => if lam k = 0 then 1 else μ k / lam k
  have hρ (k : ι) : Complex.normSq (ρ k) = 1 ∧ μ k = ρ k * lam k := by
    dsimp [ρ]
    split_ifs with hk
    · have hm : μ k = 0 := Complex.normSq_eq_zero.mp (by rw [← h k, hk, Complex.normSq_zero])
      simp only [Complex.normSq_one, hk, hm, one_mul, and_self]
    · exact ⟨by rw [Complex.normSq_div, ← h k, div_self (Complex.normSq_pos.mpr hk).ne'],
        (div_mul_cancel₀ _ hk).symm⟩
  let w : ι → Fin 2 → ℂ := fun k => ![z k 0, ρ k * z k 1]
  refine ⟨w, ?_, ?_⟩
  · intro k
    have hk := hz k
    unfold D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor at hk ⊢
    rw [Fin.sum_univ_two] at hk ⊢
    dsimp only [w, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Complex.normSq_mul, (hρ k).1, one_mul]
    exact hk
  · rw [overlap_expansion, overlap_expansion]
    apply Finset.sum_congr rfl
    intro k hk
    have hprod : (∏ l ∈ Finset.univ.erase k, w l 0) =
        ∏ l ∈ Finset.univ.erase k, z l 0 := rfl
    rw [hprod]
    change μ k * conj ((ρ k * z k 1) * ∏ l ∈ Finset.univ.erase k, z l 0) = _
    rw [(hρ k).2]
    simp only [map_mul]
    have he : ρ k * conj (ρ k) = 1 := by
      rw [Complex.mul_conj, (hρ k).1, Complex.ofReal_one]
    calc
      _ = (ρ k * conj (ρ k)) *
          (lam k * conj (z k 1) * conj (∏ l ∈ Finset.univ.erase k, z l 0)) := by ring
      _ = _ := by rw [he, one_mul]; ring

private lemma phase_invariance {ι : Type*} [Fintype ι] (lam μ : ι → ℂ)
    (h : ∀ k, Complex.normSq (lam k) = Complex.normSq (μ k)) : gMax lam = gMax μ := by
  unfold gMax
  congr 1
  ext t
  constructor
  · rintro ⟨z, hz, ht⟩
    obtain ⟨w, hw, he⟩ := phase_transport lam μ h z hz
    exact ⟨w, hw, he.symm ▸ ht⟩
  · rintro ⟨z, hz, ht⟩
    obtain ⟨w, hw, he⟩ := phase_transport μ lam (fun k => (h k).symm) z hz
    exact ⟨w, hw, he.symm ▸ ht⟩

private def positiveOverlap {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (z : ι → Fin 2 → ℝ) : ℝ := by
  classical
  exact ∑ k, a k * z k 1 * ∏ l ∈ Finset.univ.erase k, z l 0

private lemma overlap_real {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (z : ι → Fin 2 → ℝ) :
    overlap (fun k => (a k : ℂ)) (fun k b => (z k b : ℂ)) = (positiveOverlap a z : ℂ) := by
  classical
  rw [overlap_expansion]
  unfold positiveOverlap
  push_cast
  simp only [map_mul, map_prod, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private lemma overlap_modulus_bound {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (z : ι → Fin 2 → ℂ) :
    ‖overlap (fun k => (a k : ℂ)) z‖ ≤ positiveOverlap a (fun k b => ‖z k b‖) := by
  classical
  rw [overlap_expansion]
  calc
    _ ≤ ∑ k, ‖(a k : ℂ) * conj (z k 1 * ∏ l ∈ Finset.univ.erase k, z l 0)‖ :=
      norm_sum_le _ _
    _ = _ := by
      unfold positiveOverlap
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul, Complex.norm_conj, norm_mul, norm_prod, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (ha k)]
      ring

private lemma positive_max {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ k, 0 ≤ a k) :
    ∃ z : ι → Fin 2 → ℝ, (∀ k b, 0 ≤ z k b) ∧
      (∀ k, z k 0 ^ 2 + z k 1 ^ 2 = 1) ∧
      gMax (fun k => (a k : ℂ)) = positiveOverlap a z ^ 2 := by
  classical
  obtain ⟨w, hw, hmax⟩ := overlap_attained (fun k => (a k : ℂ))
  let z : ι → Fin 2 → ℝ := fun k b => ‖w k b‖
  have hzn (k : ι) : z k 0 ^ 2 + z k 1 ^ 2 = 1 := by
    have h := hw k
    unfold D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor at h
    rw [Fin.sum_univ_two] at h
    simpa only [Complex.normSq_eq_norm_sq] using h
  have hz : unitFactors (fun k b => (z k b : ℂ)) := by
    intro k
    unfold D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor
    rw [Fin.sum_univ_two, Complex.normSq_ofReal, Complex.normSq_ofReal]
    simpa only [pow_two] using hzn k
  have hnonneg : 0 ≤ positiveOverlap a z := by
    unfold positiveOverlap
    exact Finset.sum_nonneg fun k hk => mul_nonneg (mul_nonneg (ha k) (norm_nonneg _))
      (Finset.prod_nonneg fun l hl => norm_nonneg _)
  refine ⟨z, fun k b => norm_nonneg _, hzn, le_antisymm ?_ ?_⟩
  · rw [hmax, Complex.normSq_eq_norm_sq]
    exact (sq_le_sq₀ (norm_nonneg _) hnonneg).mpr (overlap_modulus_bound a ha w)
  · have h := le_csSup (overlap_bounded (fun k => (a k : ℂ)))
      ⟨fun k b => (z k b : ℂ), hz, rfl⟩
    rw [overlap_real, Complex.normSq_ofReal] at h
    unfold gMax
    simpa only [pow_two] using h

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
    unfold dotProduct at hcs
    simp only [Fin.sum_univ_two, Pi.star_apply, Complex.star_def,
      Matrix.cons_val_zero, Matrix.cons_val_one, Complex.conj_ofReal,
      ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, hu, one_mul] at hcs
    calc
      _ ≤ (a * w 0 + b * s * w 1) ^ 2 + (b * r * w 0) ^ 2 := by
        convert hcs using 1; ring
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

open Classical in
private lemma pair_slice {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (z : ι → Fin 2 → ℝ) (i j : ι) (hij : i ≠ j) :
    let s := (Finset.univ.erase i).erase j
    positiveOverlap a z =
      (∑ k ∈ s, a k * z k 1 * ∏ l ∈ s.erase k, z l 0) * z i 0 * z j 0 +
        (∏ k ∈ s, z k 0) * a j * z i 0 * z j 1 +
        (∏ k ∈ s, z k 0) * a i * z i 1 * z j 0 := by
  classical
  dsimp only
  set s := (Finset.univ.erase i).erase j
  have hji : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩
  have hi : (∏ k ∈ Finset.univ.erase i, z k 0) = z j 0 * ∏ k ∈ s, z k 0 := by
    exact (Finset.mul_prod_erase _ _ hji).symm
  have hj : (∏ k ∈ Finset.univ.erase j, z k 0) = z i 0 * ∏ k ∈ s, z k 0 := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩)]
    rw [Finset.erase_right_comm]
  have hterm (k : ι) (hk : k ∈ s) :
      (∏ l ∈ Finset.univ.erase k, z l 0) = z i 0 * z j 0 * ∏ l ∈ s.erase k, z l 0 := by
    have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hki.symm, Finset.mem_univ _⟩)]
    rw [← Finset.mul_prod_erase _ _
      (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_erase.mpr ⟨hkj.symm, Finset.mem_univ _⟩⟩)]
    have he : ((Finset.univ.erase k).erase i).erase j = s.erase k := by
      ext l
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, s]
      tauto
    rw [he]
    ring
  unfold positiveOverlap
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ hji, hi, hj]
  have hsum : (∑ k ∈ s, a k * z k 1 * ∏ l ∈ Finset.univ.erase k, z l 0) =
      (∑ k ∈ s, a k * z k 1 * ∏ l ∈ s.erase k, z l 0) * z i 0 * z j 0 := by
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hterm k hk]
    ring
  rw [hsum]
  ring

private lemma positive_pair_balancing {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (i j : ι) (hij : i ≠ j)
    (hrest : ∀ k, k ≠ i → k ≠ j → a k = b k)
    (hsum : b i ^ 2 + b j ^ 2 = a i ^ 2 + a j ^ 2)
    (hprod : a i ^ 2 * a j ^ 2 ≤ b i ^ 2 * b j ^ 2) :
    gMax (fun k => (b k : ℂ)) ≤ gMax (fun k => (a k : ℂ)) := by
  classical
  obtain ⟨z, hz, hzn, hmax⟩ := positive_max b hb
  let s := (Finset.univ.erase i).erase j
  let d := ∑ k ∈ s, b k * z k 1 * ∏ l ∈ s.erase k, z l 0
  let e := ∏ k ∈ s, z k 0
  have hd : 0 ≤ d := Finset.sum_nonneg fun k hk =>
    mul_nonneg (mul_nonneg (hb k) (hz k 1)) (Finset.prod_nonneg fun l hl => hz l 0)
  have he : 0 ≤ e := Finset.prod_nonneg fun k hk => hz k 0
  obtain ⟨x, y, hx, hy, hxn, hyn, hpv, hpmax⟩ :=
    two_factor_max d e (a i) (a j) hd he (ha i) (ha j)
  obtain ⟨u, v, hu, hv, hun, hvn, hqv, hqmax⟩ :=
    two_factor_max d e (b i) (b j) hd he (hb i) (hb j)
  have hq := hqmax (z i) (z j) (hzn i) (hzn j)
  rw [hqv] at hq
  have hslice : positiveOverlap b z =
      d * z i 0 * z j 0 + e * b j * z i 0 * z j 1 + e * b i * z i 1 * z j 0 :=
    pair_slice b z i j hij
  rw [← hslice] at hq
  have hcmp := Real.sqrt_le_sqrt (show
      (d ^ 2 + e ^ 2 * (b i ^ 2 + b j ^ 2)) ^ 2 - 4 * e ^ 4 * (b i ^ 2 * b j ^ 2) ≤
      (d ^ 2 + e ^ 2 * (a i ^ 2 + a j ^ 2)) ^ 2 - 4 * e ^ 4 * (a i ^ 2 * a j ^ 2) from by
    rw [hsum]
    nlinarith only [mul_nonneg (pow_nonneg he 4) (sub_nonneg.mpr hprod)])
  rw [hsum] at hq
  have hqbound : positiveOverlap b z ^ 2 ≤
      (d * x 0 * y 0 + e * a j * x 0 * y 1 + e * a i * x 1 * y 0) ^ 2 := by
    rw [hpv]
    rw [hsum] at hcmp
    linarith only [hq, hcmp]
  let w := Function.update (Function.update z j y) i x
  have hwi : w i = x := Function.update_self _ _ _
  have hwj : w j = y := by
    dsimp only [w]
    rw [Function.update_of_ne hij.symm, Function.update_self]
  have hwr (k : ι) (hk : k ∈ s) : w k = z k := by
    have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj := (Finset.mem_erase.mp hk).1
    exact (Function.update_of_ne hki _ _).trans (Function.update_of_ne hkj _ _)
  have hwn (k : ι) : w k 0 ^ 2 + w k 1 ^ 2 = 1 := by
    by_cases hki : k = i
    · subst k; rw [hwi]; exact hxn
    by_cases hkj : k = j
    · subst k; rw [hwj]; exact hyn
    rw [hwr k (by simp only [s, Finset.mem_erase, Finset.mem_univ, and_true]; exact ⟨hkj, hki⟩)]
    exact hzn k
  have hw : unitFactors (fun k t => (w k t : ℂ)) := by
    intro k
    unfold D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor
    rw [Fin.sum_univ_two, Complex.normSq_ofReal, Complex.normSq_ofReal]
    simpa only [pow_two] using hwn k
  have hed : (∑ k ∈ s, a k * w k 1 * ∏ l ∈ s.erase k, w l 0) = d := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hrest k (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      (Finset.mem_erase.mp hk).1, hwr k hk]
    congr 1
    exact Finset.prod_congr rfl fun l hl => congrFun (hwr l (Finset.mem_of_mem_erase hl)) 0
  have hee : (∏ k ∈ s, w k 0) = e :=
    Finset.prod_congr rfl fun k hk => congrFun (hwr k hk) 0
  have hwp := pair_slice a w i j hij
  change positiveOverlap a w =
    (∑ k ∈ s, a k * w k 1 * ∏ l ∈ s.erase k, w l 0) * w i 0 * w j 0 +
      (∏ k ∈ s, w k 0) * a j * w i 0 * w j 1 +
      (∏ k ∈ s, w k 0) * a i * w i 1 * w j 0 at hwp
  rw [hed, hee, hwi, hwj] at hwp
  have hsup := le_csSup (overlap_bounded (fun k => (a k : ℂ)))
    ⟨fun k t => (w k t : ℂ), hw, rfl⟩
  rw [overlap_real, Complex.normSq_ofReal] at hsup
  rw [hmax]
  calc
    _ ≤ (d * x 0 * y 0 + e * a j * x 0 * y 1 + e * a i * x 1 * y 0) ^ 2 := hqbound
    _ = positiveOverlap a w ^ 2 := congrArg (· ^ 2) hwp.symm
    _ ≤ _ := by unfold gMax; simpa only [pow_two] using hsup

private lemma pair_balancing {ι : Type*} [Fintype ι] (lam μ : ι → ℂ) (i j : ι)
    (hij : i ≠ j)
    (hrest : ∀ k, k ≠ i → k ≠ j → Complex.normSq (μ k) = Complex.normSq (lam k))
    (hsum : Complex.normSq (μ i) + Complex.normSq (μ j) =
      Complex.normSq (lam i) + Complex.normSq (lam j))
    (hprod : Complex.normSq (lam i) * Complex.normSq (lam j) ≤
      Complex.normSq (μ i) * Complex.normSq (μ j)) : gMax μ ≤ gMax lam := by
  have hp := phase_invariance lam (fun k => (‖lam k‖ : ℂ)) (fun k => by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, pow_two])
  have hq := phase_invariance μ (fun k => (‖μ k‖ : ℂ)) (fun k => by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, pow_two])
  rw [hp, hq]
  apply positive_pair_balancing (fun k => ‖lam k‖) (fun k => ‖μ k‖)
    (fun k => norm_nonneg _) (fun k => norm_nonneg _) i j hij
  · intro k hki hkj
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
      simpa only [Complex.normSq_eq_norm_sq] using (hrest k hki hkj).symm)
  · simpa only [Complex.normSq_eq_norm_sq] using hsum
  · simpa only [Complex.normSq_eq_norm_sq] using hprod

private lemma walk_succ (p n : ℕ) (c : Fin 2 → ℂ) :
    walkState p (n + 1) c = hadamardStep p (walkState p n c) := by
  delta walkState
  rw [Function.iterate_succ_apply']

private lemma walk_linearity (p n : ℕ) (c : Fin 2 → ℂ) (j : Fin 2 × ZMod p) :
    walkState p n c j = c 0 * walkState p n ![1, 0] j +
      c 1 * walkState p n ![0, 1] j := by
  induction n generalizing j with
  | zero =>
      rcases j with ⟨b, x⟩
      fin_cases b <;> by_cases hx : x = 0 <;> delta walkState <;> simp [hx]
  | succ n ih =>
      rw [walk_succ, walk_succ, walk_succ]
      delta hadamardStep
      split_ifs <;> rw [ih, ih] <;> ring

private lemma walk_reflection (p n : ℕ) :
    (∀ j, (walkState p n ![1, 0] j).im = 0 ∧ (walkState p n ![0, 1] j).im = 0) ∧
    (∀ x : ZMod p,
      walkState p n ![1, 0] (1, -x) =
        -(-1 : ℂ) ^ n * walkState p n ![0, 1] (0, x) ∧
      walkState p n ![0, 1] (1, -x) =
        (-1 : ℂ) ^ n * walkState p n ![1, 0] (0, x)) := by
  induction n with
  | zero =>
      constructor
      · rintro ⟨b, x⟩
        fin_cases b <;> by_cases hx : x = 0 <;> delta walkState <;> simp [hx]
      · intro x
        delta walkState
        simp
  | succ n ih =>
      have hu (j : Fin 2 × ZMod p) : (walkState p n ![1, 0] j).im = 0 := (ih.1 j).1
      have hw (j : Fin 2 × ZMod p) : (walkState p n ![0, 1] j).im = 0 := (ih.1 j).2
      have he : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by rw [← mul_pow]; norm_num
      have hback (x : ZMod p) :
          walkState p n ![1, 0] (0, -x) = (-1 : ℂ) ^ n * walkState p n ![0, 1] (1, x) ∧
          walkState p n ![0, 1] (0, -x) = -(-1 : ℂ) ^ n * walkState p n ![1, 0] (1, x) := by
        obtain ⟨h1, h2⟩ := ih.2 (-x)
        rw [neg_neg] at h1 h2
        constructor
        · linear_combination -(-1 : ℂ) ^ n * h2 - walkState p n ![1, 0] (0, -x) * he
        · linear_combination (-1 : ℂ) ^ n * h1 - walkState p n ![0, 1] (0, -x) * he
      constructor
      · intro j
        constructor <;> rw [walk_succ] <;> delta hadamardStep <;> split_ifs <;>
          simp only [Complex.div_ofReal_im, Complex.add_im, Complex.sub_im, hu, hw,
            add_zero, sub_self, zero_div]
      · intro x
        have hn : -x - 1 = -(x + 1) := by ring
        constructor
        · simp only [walk_succ]
          delta hadamardStep
          rw [ite_eq_right (show (1 : Fin 2) ≠ 0 from Ne.symm Fin.zero_ne_one), ite_eq_left rfl]
          rw [hn, (hback (x + 1)).1, (ih.2 (x + 1)).1, pow_succ]
          ring
        · simp only [walk_succ]
          delta hadamardStep
          rw [ite_eq_right (show (1 : Fin 2) ≠ 0 from Ne.symm Fin.zero_ne_one), ite_eq_left rfl]
          rw [hn, (hback (x + 1)).2, (ih.2 (x + 1)).2, pow_succ]
          ring

private lemma walk_pair_probabilities (p n : ℕ) (c : Fin 2 → ℂ) (hc : D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor c) :
    ∀ x : ZMod p,
      Complex.normSq (walkState p n cStar (0, x)) =
        Complex.normSq (walkState p n cStar (1, -x)) ∧
      Complex.normSq (walkState p n cStar (0, x)) +
          Complex.normSq (walkState p n cStar (1, -x)) =
        Complex.normSq (walkState p n c (0, x)) +
          Complex.normSq (walkState p n c (1, -x)) := by
  intro x
  obtain ⟨hreal, hrel⟩ := walk_reflection p n
  let a := (walkState p n ![1, 0] (0, x)).re
  let b := (walkState p n ![0, 1] (0, x)).re
  have hu : walkState p n ![1, 0] (0, x) = (a : ℂ) :=
    Complex.ext rfl (hreal (0, x)).1
  have hw : walkState p n ![0, 1] (0, x) = (b : ℂ) :=
    Complex.ext rfl (hreal (0, x)).2
  have he : Complex.normSq ((-1 : ℂ) ^ n) = 1 := by rw [map_pow]; norm_num
  have h0 (d : Fin 2 → ℂ) : walkState p n d (0, x) = d 0 * (a : ℂ) + d 1 * (b : ℂ) := by
    rw [walk_linearity, hu, hw]
  have h1 (d : Fin 2 → ℂ) : Complex.normSq (walkState p n d (1, -x)) =
      Complex.normSq (d 1 * (a : ℂ) - d 0 * (b : ℂ)) := by
    rw [walk_linearity, (hrel x).1, (hrel x).2, hu, hw]
    rw [show d 0 * (-(-1 : ℂ) ^ n * (b : ℂ)) + d 1 * ((-1 : ℂ) ^ n * (a : ℂ)) =
      (-1 : ℂ) ^ n * (d 1 * (a : ℂ) - d 0 * (b : ℂ)) by ring]
    rw [Complex.normSq_mul, he, one_mul]
  have hcs : Complex.normSq (c 0) + Complex.normSq (c 1) = 1 := by
    unfold D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor at hc
    exact Fin.sum_univ_two (fun b => Complex.normSq (c b)) ▸ hc
  have hsum : Complex.normSq (walkState p n c (0, x)) +
      Complex.normSq (walkState p n c (1, -x)) = a ^ 2 + b ^ 2 := by
    rw [h0, h1]
    calc
      _ = (a ^ 2 + b ^ 2) * (Complex.normSq (c 0) + Complex.normSq (c 1)) := by
        simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
          Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
      _ = _ := by rw [hcs, mul_one]
  have hs : Complex.normSq (Real.sqrt 2 : ℂ) = 2 := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]
  have hstar0 : Complex.normSq (walkState p n cStar (0, x)) = (a ^ 2 + b ^ 2) / 2 := by
    rw [h0]
    have hnum : cStar 0 * (a : ℂ) + cStar 1 * (b : ℂ) =
        ((a : ℂ) + Complex.I * (b : ℂ)) / (Real.sqrt 2 : ℂ) := by
      dsimp [cStar]; ring
    rw [hnum, Complex.normSq_div, hs]
    congr 1
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hstar1 : Complex.normSq (walkState p n cStar (1, -x)) = (a ^ 2 + b ^ 2) / 2 := by
    rw [h1]
    have hnum : cStar 1 * (a : ℂ) - cStar 0 * (b : ℂ) =
        (Complex.I * (a : ℂ) - (b : ℂ)) / (Real.sqrt 2 : ℂ) := by
      dsimp [cStar]; ring
    rw [hnum, Complex.normSq_div, hs]
    congr 1
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  constructor
  · rw [hstar0, hstar1]
  · rw [hstar0, hstar1, hsum]
    ring

private lemma pair_average_le (p : ℕ) [NeZero p] (lam μ : Fin 2 × ZMod p → ℂ)
    (h : ∀ x : ZMod p,
      Complex.normSq (μ (0, x)) = Complex.normSq (μ (1, -x)) ∧
      Complex.normSq (μ (0, x)) + Complex.normSq (μ (1, -x)) =
        Complex.normSq (lam (0, x)) + Complex.normSq (lam (1, -x))) : gMax μ ≤ gMax lam := by
  classical
  let f (s : Finset (ZMod p)) (k : Fin 2 × ZMod p) :=
    if (if k.1 = 0 then k.2 else -k.2) ∈ s then μ k else lam k
  have hind (s : Finset (ZMod p)) : gMax (f s) ≤ gMax lam := by
    induction s using Finset.induction_on with
    | empty =>
        exact le_of_eq (congrArg gMax (by
          funext k
          simp only [f, Finset.notMem_empty, ite_false]))
    | @insert x s hxs ih =>
        have hs0 : f s (0, x) = lam (0, x) := by simp [f, hxs]
        have hs1 : f s (1, -x) = lam (1, -x) := by simp [f, hxs]
        have hn0 : f (insert x s) (0, x) = μ (0, x) := by simp [f]
        have hn1 : f (insert x s) (1, -x) = μ (1, -x) := by simp [f]
        have hp : gMax (f (insert x s)) ≤ gMax (f s) := by
          apply pair_balancing (f s) (f (insert x s)) (0, x) (1, -x)
          · intro he
            have hc := congrArg Prod.fst he
            norm_num at hc
          · intro k hki hkj
            have hr : (if k.1 = 0 then k.2 else -k.2) ≠ x := by
              rcases k with ⟨b, t⟩
              fin_cases b
              · change t ≠ x
                intro he
                exact hki (Prod.ext rfl he)
              · change -t ≠ x
                intro he
                apply hkj
                exact Prod.ext rfl (by rw [← he, neg_neg])
            simp only [f, Finset.mem_insert, hr, false_or]
          · rw [hs0, hs1, hn0, hn1]
            exact (h x).2
          · rw [hs0, hs1, hn0, hn1]
            have hsq := congrArg (fun t : ℝ => t ^ 2) (h x).2
            have he : (Complex.normSq (μ (0, x)) - Complex.normSq (μ (1, -x))) ^ 2 = 0 := by
              rw [(h x).1]; ring
            nlinarith only [hsq, he,
              sq_nonneg (Complex.normSq (lam (0, x)) - Complex.normSq (lam (1, -x)))]
        exact hp.trans ih
  have hall := hind Finset.univ
  simpa only [f, Finset.mem_univ, ite_true] using hall

theorem result : claim := by
  intro p hp n c hc
  letI : NeZero p := ⟨by omega⟩
  have h := pair_average_le p (walkState p n c) (walkState p n cStar)
    (walk_pair_probabilities p n c hc)
  exact sub_le_sub_left h 1

end D5.S3.Quantum.Walks.SymmetricCoinMaximalWalkEntanglement
