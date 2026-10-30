/- GID: D5/S3/Quantum/FockSpace/HigherOrderEPRTightness
   generality: I
   mirror-B: D5/B/S3/Quantum/FockSpace/HigherOrderEPRTightness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The nonnegative higher-order EPR bound is tight at every positive order. -/

import Mathlib.NumberTheory.Harmonic.Bounds

/-! Finite occupation-basis states for the tightness clause of (nS:2) in
Shchukin and van Loock, arXiv:1511.08444v1. The harmonic taper gives arbitrarily
small squared norms. No Gaussian or strict-positivity assertion is made. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.FockSpace.HigherOrderEPRTightness

open Finset

/-- Squared Hilbert norm in the two-mode occupation basis. -/
def normSq (ψ : ℕ × ℕ →₀ ℂ) : ℝ :=
  ψ.sum fun _ z => ‖z‖ ^ 2

/-- The power of the annihilation operator of the first mode. -/
def annihilateA (n : ℕ) : (ℕ × ℕ →₀ ℂ) →ₗ[ℂ] (ℕ × ℕ →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun p =>
    if n ≤ p.1 then Finsupp.single (p.1 - n, p.2)
      (Real.sqrt ((p.1.factorial : ℝ) / (p.1 - n).factorial) : ℂ) else 0

/-- The power of the creation operator of the second mode. -/
def createB (n : ℕ) : (ℕ × ℕ →₀ ℂ) →ₗ[ℂ] (ℕ × ℕ →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun p =>
    Finsupp.single (p.1, p.2 + n)
      (Real.sqrt (((p.2 + n).factorial : ℝ) / p.2.factorial) : ℂ)

/-- Tightness of the zero bound, for either sign and every positive order. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ σ : ℂ, (σ = 1 ∨ σ = -1) →
    ∀ ε : ℝ, 0 < ε → ∃ ψ : ℕ × ℕ →₀ ℂ,
      normSq ψ = 1 ∧ normSq (annihilateA n ψ + σ • createB n ψ) < ε

private lemma norm_smul (c : ℂ) (v : ℕ × ℕ →₀ ℂ) :
    normSq (c • v) = ‖c‖ ^ 2 * normSq v := by
  change (c • v).sum (fun _ z => ‖z‖ ^ 2) =
    ‖c‖ ^ 2 * v.sum (fun _ z => ‖z‖ ^ 2)
  rw [Finsupp.sum_smul_index (by simp)]
  simp only [norm_mul, mul_pow]
  exact (Finset.mul_sum _ _ _).symm

private lemma norm_sum (s : Finset ℕ) (i : ℕ → ℕ × ℕ)
    (hi : Function.Injective i) (c : ℕ → ℂ) :
    normSq (∑ k ∈ s, Finsupp.single (i k) (c k)) = ∑ k ∈ s, ‖c k‖ ^ 2 := by
  classical
  let v : ℕ × ℕ →₀ ℂ := ∑ k ∈ s, Finsupp.single (i k) (c k)
  have hs : v.support ⊆ s.image i := by
    intro p hp
    obtain ⟨k, hk, hkp⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hp)
    exact Finset.mem_image.mpr ⟨k, hk, (Finset.mem_singleton.mp
      (Finsupp.support_single_subset hkp)).symm⟩
  have hc (k : ℕ) (hk : k ∈ s) : v (i k) = c k := by
    change (∑ j ∈ s, Finsupp.single (i j) (c j)) (i k) = c k
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply, hi.eq_iff, hk]
  change v.sum (fun _ z => ‖z‖ ^ 2) = _
  rw [Finsupp.sum_of_support_subset v hs _ (by simp),
    Finset.sum_image (by intro a _ b _ h; exact hi h)]
  exact Finset.sum_congr rfl fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hc k hk)

private def taper (m k : ℕ) : ℝ := 1 - (harmonic k : ℝ) / harmonic m

private def coefficient (n k : ℕ) : ℝ :=
  Real.sqrt (((n * k).factorial : ℝ) / (n * k + n - 1).factorial)

private def vector (n : ℕ) (σ : ℂ) (m : ℕ) : ℕ × ℕ →₀ ℂ :=
  ∑ k ∈ range (m + 1), Finsupp.single (n * k + n - 1, n * k)
    ((-σ) ^ k * (taper m k * coefficient n k : ℝ))

private lemma sqrt_factorial (r t : ℕ) (hr : 1 ≤ r) :
    Real.sqrt ((t.factorial : ℝ) / (r - 1).factorial) *
      Real.sqrt ((r.factorial : ℝ) / t.factorial) = Real.sqrt (r : ℝ) := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  have ht : (t.factorial : ℝ) ≠ 0 := by positivity
  have hd : ((r - 1).factorial : ℝ) ≠ 0 := by positivity
  have hf : (r.factorial : ℝ) = r * ((r - 1).factorial : ℝ) := by
    have h := Nat.factorial_succ (r - 1)
    rw [Nat.sub_add_cancel hr] at h
    exact_mod_cast h
  rw [hf]
  field_simp (disch := positivity)

private lemma lower_chain (n k : ℕ) (hn : 1 ≤ n) :
    annihilateA n (Finsupp.single (n * (k + 1) + n - 1, n * (k + 1))
      (coefficient n (k + 1) : ℂ)) =
      Finsupp.single (n * (k + 1) - 1, n * (k + 1))
        (Real.sqrt (n * (k + 1) : ℝ) : ℂ) := by
  have hr : 1 ≤ n * (k + 1) := by nlinarith
  have ha : n ≤ n * (k + 1) + n - 1 := by omega
  have he : n * (k + 1) + n - 1 - n = n * (k + 1) - 1 := by omega
  change Finsupp.linearCombination ℂ (fun p : ℕ × ℕ =>
    if n ≤ p.1 then Finsupp.single (p.1 - n, p.2)
      (Real.sqrt ((p.1.factorial : ℝ) / (p.1 - n).factorial) : ℂ) else 0) _ = _
  rw [Finsupp.linearCombination_single]
  dsimp only
  rw [ite_eq_left ha, he, Finsupp.smul_single]
  congr 1
  change (coefficient n (k + 1) : ℂ) * _ = _
  rw [mul_comm]
  change ((Real.sqrt (((n * (k + 1) + n - 1).factorial : ℝ) /
    (n * (k + 1) - 1).factorial) : ℂ) *
    (Real.sqrt (((n * (k + 1)).factorial : ℝ) /
      (n * (k + 1) + n - 1).factorial) : ℂ)) = _
  rw [← Complex.ofReal_mul, sqrt_factorial _ _ hr]
  push_cast
  rfl

private lemma upper_chain (n k : ℕ) (hn : 1 ≤ n) :
    createB n (Finsupp.single (n * k + n - 1, n * k) (coefficient n k : ℂ)) =
      Finsupp.single (n * (k + 1) - 1, n * (k + 1))
        (Real.sqrt (n * (k + 1) : ℝ) : ℂ) := by
  have hr : 1 ≤ n * (k + 1) := by nlinarith
  have he : n * k + n = n * (k + 1) := by ring
  change Finsupp.linearCombination ℂ (fun p : ℕ × ℕ =>
    Finsupp.single (p.1, p.2 + n)
      (Real.sqrt (((p.2 + n).factorial : ℝ) / p.2.factorial) : ℂ)) _ = _
  rw [Finsupp.linearCombination_single]
  dsimp only
  rw [Finsupp.smul_single]
  simp only [he]
  congr 1
  change (Real.sqrt (((n * k).factorial : ℝ) / (n * k + n - 1).factorial) : ℂ) * _ = _
  rw [he, ← Complex.ofReal_mul, sqrt_factorial _ _ hr]
  push_cast
  rfl

private lemma taper_image (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (σ : ℂ) :
    annihilateA n (vector n σ m) + σ • createB n (vector n σ m) =
      ∑ k ∈ range m, Finsupp.single (n * (k + 1) - 1, n * (k + 1))
        ((-σ) ^ (k + 1) * (Real.sqrt (n * (k + 1) : ℝ) *
          (taper m (k + 1) - taper m k) : ℝ)) := by
  have hh : 0 < (harmonic m : ℝ) :=
    (Real.log_pos (by norm_cast; omega)).trans_le (log_add_one_le_harmonic m)
  have hv : vector n σ m = ∑ k ∈ range (m + 1),
      ((-σ) ^ k * (taper m k : ℂ)) •
        Finsupp.single (n * k + n - 1, n * k) (coefficient n k : ℂ) := by
    change (∑ k ∈ range (m + 1), Finsupp.single _ _) = _
    apply Finset.sum_congr rfl
    intro k _
    rw [Finsupp.smul_single]
    congr 1
    simp only [smul_eq_mul, Complex.ofReal_mul]
    ring
  have hz : annihilateA n
      (Finsupp.single (n - 1, 0) (coefficient n 0 : ℂ)) = 0 := by
    change Finsupp.linearCombination ℂ (fun p : ℕ × ℕ =>
      if n ≤ p.1 then Finsupp.single (p.1 - n, p.2)
        (Real.sqrt ((p.1.factorial : ℝ) / (p.1 - n).factorial) : ℂ) else 0) _ = _
    rw [Finsupp.linearCombination_single]
    dsimp only
    rw [ite_eq_right (by omega), smul_zero]
  have ha : annihilateA n (vector n σ m) = ∑ k ∈ range m,
      ((-σ) ^ (k + 1) * (taper m (k + 1) : ℂ)) •
        Finsupp.single (n * (k + 1) - 1, n * (k + 1))
          (Real.sqrt (n * (k + 1) : ℝ) : ℂ) := by
    rw [hv, map_sum]
    simp_rw [map_smul]
    rw [Finset.sum_range_succ']
    simp only [Nat.mul_zero, Nat.zero_add, hz, smul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    rw [lower_chain n k hn]
  have hb : createB n (vector n σ m) = ∑ k ∈ range m,
      ((-σ) ^ k * (taper m k : ℂ)) •
        Finsupp.single (n * (k + 1) - 1, n * (k + 1))
          (Real.sqrt (n * (k + 1) : ℝ) : ℂ) := by
    have ht : taper m m = 0 := by
      change 1 - (harmonic m : ℝ) / harmonic m = 0
      rw [div_self hh.ne', sub_self]
    rw [hv, map_sum]
    simp_rw [map_smul]
    rw [Finset.sum_range_succ]
    simp only [ht, Complex.ofReal_zero, mul_zero, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    rw [upper_chain n k hn]
  rw [ha, hb, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [smul_smul, ← add_smul, Finsupp.smul_single]
  congr 1
  simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_sub, pow_succ]
  ring

private lemma dirichlet_energy (n m : ℕ) (hm : 1 ≤ m) :
    (∑ k ∈ range m, (Real.sqrt (n * (k + 1) : ℝ) *
      (taper m (k + 1) - taper m k)) ^ 2) = (n : ℝ) / harmonic m := by
  have hh : 0 < (harmonic m : ℝ) :=
    (Real.log_pos (by norm_cast; omega)).trans_le (log_add_one_le_harmonic m)
  have hd (k : ℕ) : taper m (k + 1) - taper m k =
      -1 / (((k : ℝ) + 1) * (harmonic m : ℝ)) := by
    have hr : (harmonic (k + 1) : ℝ) = (harmonic k : ℝ) + ((k : ℝ) + 1)⁻¹ := by
      rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast,
        Nat.cast_add, Nat.cast_one]
    change (1 - (harmonic (k + 1) : ℝ) / harmonic m) -
      (1 - (harmonic k : ℝ) / harmonic m) = _
    rw [hr]
    field_simp (disch := positivity)
    ring
  have ht (k : ℕ) : (Real.sqrt (n * (k + 1) : ℝ) *
      (taper m (k + 1) - taper m k)) ^ 2 =
      ((n : ℝ) / (harmonic m : ℝ) ^ 2) * ((k : ℝ) + 1)⁻¹ := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hd]
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp (disch := positivity)
  have he : (∑ k ∈ range m, (Real.sqrt (n * (k + 1) : ℝ) *
      (taper m (k + 1) - taper m k)) ^ 2) =
      ∑ k ∈ range m, ((n : ℝ) / (harmonic m : ℝ) ^ 2) * ((k : ℝ) + 1)⁻¹ :=
    Finset.sum_congr rfl fun k _ => ht k
  rw [he, ← Finset.mul_sum]
  have hs : (harmonic m : ℝ) = ∑ k ∈ range m, ((k : ℝ) + 1)⁻¹ := by
    change ((∑ k ∈ range m, ((k + 1 : ℕ) : ℚ)⁻¹ : ℚ) : ℝ) = _
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Rat.cast_inv, Rat.cast_natCast, Nat.cast_add, Nat.cast_one]
  rw [← hs]
  field_simp (disch := positivity)

private lemma taper_norm_bound (n m : ℕ) (hn : 1 ≤ n) (σ : ℂ) :
    1 / ((n - 1).factorial : ℝ) ≤ normSq (vector n σ m) := by
  have hi : Function.Injective (fun k : ℕ => (n * k + n - 1, n * k)) := by
    intro a b h
    have hmul := congrArg Prod.snd h
    exact mul_left_cancel₀ (by omega : n ≠ 0) hmul
  change 1 / ((n - 1).factorial : ℝ) ≤
    normSq (∑ k ∈ range (m + 1), Finsupp.single (n * k + n - 1, n * k)
      ((-σ) ^ k * (taper m k * coefficient n k : ℝ)))
  rw [norm_sum _ _ hi]
  have hzero : ‖(-σ) ^ 0 * (taper m 0 * coefficient n 0 : ℝ)‖ ^ 2 =
      1 / ((n - 1).factorial : ℝ) := by
    change ‖(-σ) ^ 0 * (((1 - (harmonic 0 : ℝ) / harmonic m) *
      Real.sqrt (((n * 0).factorial : ℝ) / (n * 0 + n - 1).factorial) : ℝ) : ℂ)‖ ^ 2 = _
    simp only [pow_zero, one_mul, harmonic_zero, Rat.cast_zero, zero_div, sub_zero,
      Nat.mul_zero, Nat.zero_add, Nat.factorial_zero, Nat.cast_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact Real.sq_sqrt (by positivity)
  rw [← hzero]
  exact Finset.single_le_sum
    (fun k _ => sq_nonneg ‖(-σ) ^ k * (taper m k * coefficient n k : ℝ)‖)
    (show 0 ∈ range (m + 1) from by simp)

private lemma taper_energy (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) :
    normSq (annihilateA n (vector n σ m) + σ • createB n (vector n σ m)) =
      (n : ℝ) / harmonic m := by
  rw [taper_image n m hn hm σ]
  have hi : Function.Injective (fun k : ℕ => (n * (k + 1) - 1, n * (k + 1))) := by
    intro a b h
    have hmul := congrArg Prod.snd h
    have he := mul_left_cancel₀ (by omega : n ≠ 0) hmul
    omega
  rw [norm_sum _ _ hi]
  have hs : ‖-σ‖ = 1 := by rcases hσ with rfl | rfl <;> simp
  simp only [norm_mul, norm_pow, hs, one_pow, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  simpa only [mul_pow, sq_abs] using dirichlet_energy n m hm

private lemma harmonic_large (b : ℝ) :
    ∃ m : ℕ, 1 ≤ m ∧ b < (harmonic m : ℝ) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (Real.exp b)
  have hmpos : 0 < (m : ℝ) := (Real.exp_pos b).trans hm
  refine ⟨m, by exact_mod_cast hmpos, ?_⟩
  have hl : b < Real.log (m + 1 : ℕ) := by
    rw [← Real.log_exp b]
    apply Real.log_lt_log (Real.exp_pos b)
    exact hm.trans (by norm_cast; omega)
  exact hl.trans_le (log_add_one_le_harmonic m)

private lemma normalize (n : ℕ) (σ : ℂ) (v : ℕ × ℕ →₀ ℂ)
    (hv : 0 < normSq v) :
    ∃ ψ : ℕ × ℕ →₀ ℂ, normSq ψ = 1 ∧
      normSq (annihilateA n ψ + σ • createB n ψ) =
        normSq (annihilateA n v + σ • createB n v) / normSq v := by
  let c : ℂ := ((Real.sqrt (normSq v))⁻¹ : ℝ)
  have hc : ‖c‖ ^ 2 = (normSq v)⁻¹ := by
    change ‖(((Real.sqrt (normSq v))⁻¹ : ℝ) : ℂ)‖ ^ 2 = _
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hv.le]
  refine ⟨c • v, ?_, ?_⟩
  · rw [norm_smul, hc, inv_mul_cancel₀ hv.ne']
  · rw [map_smul, map_smul, smul_comm σ c, ← smul_add, norm_smul, hc]
    exact mul_comm _ _

/-- Every positive order admits normalized finite states arbitrarily close to zero. -/
theorem result : claim := by
  intro n hn σ hσ ε hε
  obtain ⟨m, hm, hlarge⟩ := harmonic_large ((n.factorial : ℝ) / ε)
  have hp : 0 < ((n - 1).factorial : ℝ) := by positivity
  have hlow := taper_norm_bound n m hn σ
  have hv : 0 < normSq (vector n σ m) := lt_of_lt_of_le (by positivity) hlow
  obtain ⟨ψ, hψ, he⟩ := normalize n σ (vector n σ m) hv
  refine ⟨ψ, hψ, ?_⟩
  rw [he, taper_energy n m hn hm σ hσ]
  have hfac : (n.factorial : ℝ) = n * ((n - 1).factorial : ℝ) := by
    have h := Nat.factorial_succ (n - 1)
    rw [Nat.sub_add_cancel hn] at h
    exact_mod_cast h
  have hh : 0 < (harmonic m : ℝ) := by
    have : 0 < (n.factorial : ℝ) / ε := by positivity
    linarith
  have hbound : (n : ℝ) / harmonic m / normSq (vector n σ m) ≤
      n.factorial / (harmonic m : ℝ) := by
    apply (div_le_iff₀ hv).2
    have hz : 1 ≤ normSq (vector n σ m) * ((n - 1).factorial : ℝ) :=
      (div_le_iff₀ hp).1 hlow
    calc
      (n : ℝ) / harmonic m ≤ (n : ℝ) / harmonic m *
          (normSq (vector n σ m) * ((n - 1).factorial : ℝ)) := by
        exact le_mul_of_one_le_right (by positivity) hz
      _ = n.factorial / (harmonic m : ℝ) * normSq (vector n σ m) := by
        rw [hfac]; ring
  apply hbound.trans_lt
  apply (div_lt_iff₀ hh).2
  simpa only [mul_comm] using (div_lt_iff₀ hε).1 hlarge

end D5.S3.Quantum.FockSpace.HigherOrderEPRTightness
