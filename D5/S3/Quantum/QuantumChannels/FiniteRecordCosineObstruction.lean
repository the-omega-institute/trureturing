/- GID: D5/S3/Quantum/QuantumChannels/FiniteRecordCosineObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FiniteRecordCosineObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A strictly positive cosine error floor for every finite-record channel recovery. -/

import D5.S3.Quantum.Decoherence.FiniteRecordRecoveryError
import D5.S3.QuantumBounds.ReferenceFrameTaxOptimal
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance

namespace D5.S3.Quantum.QuantumChannels.FiniteRecordCosineObstruction

private theorem path_correlation_le_cos (m : ℕ) (x : Fin (m + 1) → ℝ) :
    (∑ k : Fin m, x k.castSucc * x k.succ) ≤
      Real.cos (Real.pi / ((m : ℝ) + 2)) *
        ∑ k : Fin (m + 1), x k ^ 2 := by
  let a : Fin (m + 1) → ℝ := fun k =>
    ((if h : 0 < k.val then
      x ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le ..) k.isLt⟩ else 0) +
      (if h : k.val + 1 < m + 1 then x ⟨k.val + 1, h⟩ else 0)) / 2
  have hl : (∑ k : Fin (m + 1), x k * (if h : 0 < k.val then
      x ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le ..) k.isLt⟩ else 0)) =
      ∑ k : Fin m, x k.castSucc * x k.succ := by
    rw [Fin.sum_univ_succ]
    simp [Fin.val_succ]
    apply Finset.sum_congr rfl
    intro k _
    change x k.succ * x k.castSucc = x k.castSucc * x k.succ
    ring
  have hr : (∑ k : Fin (m + 1), x k *
      (if h : k.val + 1 < m + 1 then x ⟨k.val + 1, h⟩ else 0)) =
      ∑ k : Fin m, x k.castSucc * x k.succ := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_last, lt_self_iff_false, dite_false, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Fin.val_castSucc, Nat.add_lt_add_iff_right, k.isLt, dite_true]
    rfl
  have hpair : (∑ k, x k * a k) = ∑ k : Fin m, x k.castSucc * x k.succ := by
    calc
      _ = ((∑ k : Fin (m + 1), x k * (if h : 0 < k.val then
          x ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le ..) k.isLt⟩ else 0)) +
          ∑ k : Fin (m + 1), x k *
            (if h : k.val + 1 < m + 1 then x ⟨k.val + 1, h⟩ else 0)) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k _
        dsimp only [a]
        ring
      _ = _ := by rw [hl, hr]; ring
  have hquad := D5.S3.QuantumBounds.ReferenceFrameTax.nearestNeighborQuadratic_le_cos_sq
    (m + 1) x
  change (∑ k, a k ^ 2) ≤ _ at hquad
  simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] at hquad
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x a
  rw [hpair] at hcs
  have hs : 0 ≤ ∑ k : Fin (m + 1), x k ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have ht : Real.pi / ((m : ℝ) + 2) ≤ Real.pi / 2 := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hc : 0 ≤ Real.cos (Real.pi / ((m : ℝ) + 2)) :=
    Real.cos_nonneg_of_mem_Icc ⟨by
      have hx : 0 ≤ Real.pi / ((m : ℝ) + 2) := by positivity
      linarith [Real.pi_pos], ht⟩
  have hmul := mul_le_mul_of_nonneg_left hquad hs
  have hright := mul_nonneg hc hs
  nlinarith [sq_nonneg ((∑ k : Fin m, x k.castSucc * x k.succ) -
    Real.cos (Real.pi / ((m : ℝ) + 2)) * ∑ k : Fin (m + 1), x k ^ 2)]

private theorem residue_block_bounds (N d : ℕ) (hd : 0 < d)
    (c : ℤ → ℂ)
    (hsupport : ∀ k : ℤ, k < 0 ∨ (N : ℤ) < k → c k = 0) :
    let m : ℕ := N / d
    let x : Fin d → Fin (m + 1) → ℝ :=
      fun r k => ‖c ((r.val : ℤ) + (k.val : ℤ) * (d : ℤ))‖
    (∑ r : Fin d, ∑ k : Fin (m + 1), x r k ^ 2) =
      (∑' k : ℤ, ‖c k‖ ^ 2) ∧
    ‖(∑' k : ℤ, c (k + (d : ℤ)) * star (c k))‖ ≤
      ∑ r : Fin d, ∑ k : Fin m, x r k.castSucc * x r k.succ := by
  classical
  intro m x
  let z : Fin d × Fin (m + 1) → ℤ := fun p => ((p.1.val + p.2.val * d : ℕ) : ℤ)
  have hz : Function.Injective z := by
    intro p t h
    have hn : p.1.val + p.2.val * d = t.1.val + t.2.val * d := by
      dsimp [z] at h
      exact_mod_cast h
    have hr := congrArg (fun n => n % d) hn
    have hk := congrArg (fun n => n / d) hn
    apply Prod.ext <;> apply Fin.ext
    · simpa [Nat.mod_eq_of_lt p.1.isLt, Nat.mod_eq_of_lt t.1.isLt] using hr
    · simpa [Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt p.1.isLt,
        Nat.div_eq_of_lt t.1.isLt] using hk
  have hcover (n : ℤ) (hn : 0 ≤ n) (hN : n ≤ N) : ∃ p, z p = n := by
    have hnat : n.toNat ≤ N := by omega
    refine ⟨(⟨n.toNat % d, Nat.mod_lt _ hd⟩,
      ⟨n.toNat / d, Nat.lt_succ_of_le (Nat.div_le_div_right hnat)⟩), ?_⟩
    simp only [z, Nat.mod_add_div', Int.natCast_toNat_eq_self.mpr hn]
  have hsum {A : Type} [AddCommMonoid A] (f : ℤ → A)
      (hf : ∀ k : ℤ, k < 0 ∨ (N : ℤ) < k → f k = 0) :
      (∑ k ∈ Finset.Icc (0 : ℤ) (N : ℤ), f k) =
        ∑ r : Fin d, ∑ k : Fin (m + 1), f (z (r, k)) := by
    rw [← Fintype.sum_prod_type (fun p : Fin d × Fin (m + 1) => f (z p))]
    symm
    refine Finset.sum_bij_ne_zero (fun p _ _ => z p) ?_ ?_ ?_ ?_
    · intro p _ hp
      by_contra h
      exact hp (hf _ (by simpa only [Finset.mem_Icc, not_and_or, not_le] using h))
    · intro p _ _ t _ _ h
      exact hz h
    · intro n hn hfn
      obtain ⟨p, hp⟩ := hcover n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
      exact ⟨p, Finset.mem_univ _, by simpa [hp] using hfn, hp⟩
    · intros; rfl
  have hm : (∑' k : ℤ, ‖c k‖ ^ 2) = ∑ r, ∑ k, x r k ^ 2 := by
    rw [tsum_eq_sum (s := Finset.Icc (0 : ℤ) (N : ℤ)) (by
      intro k hk
      rw [hsupport k (by simpa only [Finset.mem_Icc, not_and_or, not_le] using hk)]
      simp)]
    simpa [x, z] using hsum (fun k => ‖c k‖ ^ 2) (by
      intro k hk; simp [hsupport k hk])
  refine ⟨hm.symm, ?_⟩
  have hg : (∑' k : ℤ, c (k + (d : ℤ)) * star (c k)) =
      ∑ r, ∑ k : Fin (m + 1), c (z (r, k) + d) * star (c (z (r, k))) := by
    rw [tsum_eq_sum (s := Finset.Icc (0 : ℤ) (N : ℤ)) (by
      intro k hk
      simp [hsupport k (by simpa only [Finset.mem_Icc, not_and_or, not_le] using hk)])]
    exact hsum _ (by intro k hk; simp [hsupport k hk])
  rw [hg]
  calc
    _ ≤ ∑ r, ∑ k : Fin (m + 1), ‖c (z (r, k))‖ * ‖c (z (r, k) + d)‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r _ => by
        simpa [norm_mul, norm_star, mul_comm] using norm_sum_le Finset.univ
          (fun k : Fin (m + 1) => c (z (r, k) + d) * star (c (z (r, k))))))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Fin.sum_univ_castSucc]
      have hlast : c (z (r, Fin.last m) + d) = 0 := by
        apply hsupport _ (Or.inr ?_)
        have hdiv := Nat.mod_lt N hd
        have heq := Nat.mod_add_div N d
        dsimp [z, m]
        exact_mod_cast (show N < r.val + N / d * d + d by nlinarith)
      simp only [hlast, norm_zero, mul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro k _
      simp only [x, z, Nat.cast_add, Nat.cast_mul, Fin.val_castSucc, Fin.val_succ,
        Nat.cast_one]
      congr 3
      ring

theorem coefficient_gamma_le_cosine (N : ℕ) (c : ℤ → ℂ)
    (hsupport : ∀ k : ℤ, k < 0 ∨ (N : ℤ) < k → c k = 0)
    (hnorm : (∑' k : ℤ, ‖c k‖ ^ 2) = (1 : ℝ))
    (ell : ℤ) (hell : ell ≠ 0) :
    ‖(∑' k : ℤ, c (k + ell) * star (c k))‖ ≤
      Real.cos (Real.pi / (((N / ell.natAbs : ℕ) : ℝ) + 2)) := by
  have hd : 0 < ell.natAbs := Int.natAbs_pos.mpr hell
  obtain ⟨hmass, hbound⟩ := residue_block_bounds N ell.natAbs hd c hsupport
  dsimp only at hmass hbound
  have hpositive : ‖(∑' k : ℤ, c (k + (ell.natAbs : ℤ)) * star (c k))‖ ≤
      Real.cos (Real.pi / (((N / ell.natAbs : ℕ) : ℝ) + 2)) := by
    refine hbound.trans ?_
    calc
      _ ≤ ∑ r : Fin ell.natAbs,
          Real.cos (Real.pi / (((N / ell.natAbs : ℕ) : ℝ) + 2)) *
            ∑ k : Fin (N / ell.natAbs + 1), ‖c ((r.val : ℤ) + k.val * ell.natAbs)‖ ^ 2 :=
        Finset.sum_le_sum (fun r _ => path_correlation_le_cos _ _)
      _ = _ := by rw [← Finset.mul_sum, hmass, hnorm, mul_one]
  rcases le_total 0 ell with h | h
  · simpa [Int.natCast_natAbs, abs_of_nonneg h] using hpositive
  · have hneg := congrArg norm
      (D5.S3.Quantum.Decoherence.FiniteRecordRecoveryError.coefficient_gamma_neg c ell)
    simpa only [Int.natCast_natAbs, abs_of_nonpos h, ← sub_eq_add_neg,
      hneg, norm_star] using hpositive

private theorem gap_floor_positive (N : ℕ) (ell : ℤ) (hell : ell ≠ 0) :
    let d : ℕ := ell.natAbs
    let u : ℝ := (N : ℝ) / |(ell : ℝ)|
    let m : ℕ := N / d
    let f : ℤ := Int.floor u
    let denominator : ℝ := (f : ℝ) + 2
    let bound : ℝ := (1 - Real.cos (Real.pi / denominator)) / 2
    0 < d ∧ (d : ℝ) = |(ell : ℝ)| ∧
      0 < |(ell : ℝ)| ∧ |(ell : ℝ)| ≠ 0 ∧ 0 ≤ u ∧
      Nat.floor u = m ∧ f = (m : ℤ) ∧
      denominator = (m : ℝ) + 2 ∧
      0 < denominator ∧ denominator ≠ 0 ∧
      (0 < Real.pi / denominator ∧ Real.pi / denominator ≤ Real.pi / 2) ∧
      bound = (1 - Real.cos (Real.pi / ((m : ℝ) + 2))) / 2 ∧
      0 < bound := by
  intro d u m f denominator bound
  have hd : 0 < d := Int.natAbs_pos.mpr hell
  have hc : (d : ℝ) = |(ell : ℝ)| := by simp [d, Nat.cast_natAbs, Int.cast_abs]
  have ha : 0 < |(ell : ℝ)| := by rw [← hc]; exact_mod_cast hd
  have hu : 0 ≤ u := div_nonneg (Nat.cast_nonneg N) (abs_nonneg _)
  have hn : Nat.floor u = m := by
    dsimp [u, m]
    rw [← hc]
    exact Nat.floor_div_eq_div N d
  have hf : f = (m : ℤ) := by
    dsimp [f]
    rw [← Int.natCast_floor_eq_floor hu, hn]
  have hden : denominator = (m : ℝ) + 2 := by simp [denominator, hf]
  have hp : 0 < denominator := by rw [hden]; positivity
  have ht : 0 < Real.pi / denominator := div_pos Real.pi_pos hp
  have htop : Real.pi / denominator ≤ Real.pi / 2 := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
    rw [hden]
    linarith [Nat.cast_nonneg (α := ℝ) m]
  refine ⟨hd, hc, ha, ha.ne', hu, hn, hf, hden, hp, hp.ne', ⟨ht, htop⟩, ?_, ?_⟩
  · simp only [bound, hden]
  · have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (le_refl 0) htop ht
    rw [Real.cos_zero] at hcos
    dsimp [bound]
    linarith

/-- The obstruction concerns this recording channel and a realized nonzero label gap.
It makes no obstruction claim about unaffected degenerate subspaces or other encodings. -/
theorem finite_record_cosine_obstruction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (c : ℤ → ℂ) (q : ι → ℤ)
    (hsupport : ∀ k : ℤ, k < 0 ∨ (N : ℤ) < k → c k = 0)
    (hnorm : (∑' k : ℤ, ‖c k‖ ^ 2) = (1 : ℝ)) :
    let gamma : ℤ → ℂ := fun t => ∑' k : ℤ, c (k + t) * star (c k)
    let Q : ℕ := ∑ i : ι, (q i).natAbs
    let L : ℕ := N + 2 * Q + 1
    let coord : Fin L → ℤ := fun a => (a.val : ℤ) - (Q : ℤ)
    let record : ι → Fin L → ℂ := fun i a => c (coord a + q i)
    let V : Matrix (ι × Fin L) ι ℂ :=
      fun p j => if j = p.1 then record p.1 p.2 else 0
    let partialTrace : Matrix (ι × Fin L) (ι × Fin L) ℂ → Matrix ι ι ℂ :=
      fun joint i j => ∑ a : Fin L, joint (i, a) (j, a)
    let Lambda : Matrix ι ι ℂ → Matrix ι ι ℂ :=
      fun A => partialTrace (V * A * V.conjTranspose)
    ∃ C : QuantumChannel ι ι,
      (∀ A : Matrix ι ι ℂ, act C A = Lambda A) ∧
      (∀ (A : Matrix ι ι ℂ) i j,
        Lambda A i j = gamma (q i - q j) * A i j) ∧
      ∀ (i j : ι) (ell : ℤ), ell ≠ 0 → q i - q j = ell →
      ∀ R : QuantumChannel ι ι,
        let f : ℤ := Int.floor ((N : ℝ) / |(ell : ℝ)|)
        let bound : ℝ := (1 - Real.cos (Real.pi / ((f : ℝ) + 2))) / 2
        let errors : Set ℝ := Set.range (fun rho : DensityState ι =>
          traceDistance (R.mapState (C.mapState rho)) rho)
        let matrixErrors : Set ℝ := Set.range (fun rho : DensityState ι =>
          traceNorm (act R (Lambda (CStarMatrix.ofMatrix.symm rho.val)) -
            CStarMatrix.ofMatrix.symm rho.val) / 2)
        errors = matrixErrors ∧
          (∀ rho sigma : DensityState ι,
            0 ≤ traceDistance rho sigma ∧ traceDistance rho sigma ≤ 1) ∧
          errors.Nonempty ∧ BddAbove errors ∧
          bound ≤ sSup errors ∧ 0 < bound := by
  intro gamma Q L coord record V partialTrace Lambda
  have hfinite_normalization : (∑ k ∈ Finset.Icc (0 : ℤ) (N : ℤ), ‖c k‖ ^ 2) = (1 : ℝ) := by
    rw [← hnorm]
    symm
    apply tsum_eq_sum
    intro k hk
    simp [hsupport k (by simpa only [Finset.mem_Icc, not_and_or, not_le] using hk)]
  have hreal := D5.S3.Quantum.Decoherence.FiniteShiftedRecordChannel.finite_shifted_record_channel
    N c q hsupport hfinite_normalization
  dsimp only at hreal
  obtain ⟨C, hC⟩ := hreal.2.2.2.1
  change ∀ A : Matrix ι ι ℂ, act C A = Lambda A at hC
  have hact (A : Matrix ι ι ℂ) (i j : ι) : Lambda A i j = gamma (q i - q j) * A i j := by
    exact (hreal.2.2.2.2.1 A i j).trans (congrArg (fun z => z * A i j) (hreal.2.1 _))
  refine ⟨C, hC, hact, ?_⟩
  intro i j ell hell hgap R f bound errors matrixErrors
  have hLambda (A : Matrix ι ι ℂ) : (fun k l => gamma (q k - q l) * A k l) = Lambda A := by
    funext k l
    exact (hact A k l).symm
  have hr : (∀ rho sigma : DensityState ι,
      0 ≤ traceDistance rho sigma ∧ traceDistance rho sigma ≤ 1) ∧
      matrixErrors.Nonempty ∧ BddAbove matrixErrors ∧
      (1 - ‖gamma (q i - q j)‖) / 2 ≤ sSup matrixErrors := by
    simpa only [matrixErrors, ← hLambda] using
      D5.S3.Quantum.Decoherence.FiniteRecordRecoveryError.finite_record_recovery_error_lower_bound
        N c q hsupport hnorm i j (by rwa [hgap]) R
  have herr (rho : DensityState ι) : traceDistance (R.mapState (C.mapState rho)) rho =
      traceNorm (act R (Lambda (CStarMatrix.ofMatrix.symm rho.val)) -
        CStarMatrix.ofMatrix.symm rho.val) / 2 := by
    change traceNorm (act R (act C (CStarMatrix.ofMatrix.symm rho.val)) -
      CStarMatrix.ofMatrix.symm rho.val) / 2 = _
    rw [hC]
  have heq : errors = matrixErrors := congrArg Set.range (funext herr)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hb, hpos⟩ := gap_floor_positive N ell hell
  change bound = (1 - Real.cos (Real.pi / (((N / ell.natAbs : ℕ) : ℝ) + 2))) / 2 at hb
  refine ⟨heq, hr.1, heq.symm ▸ hr.2.1, heq.symm ▸ hr.2.2.1, ?_, hpos⟩
  rw [heq, hb]
  have hc := coefficient_gamma_le_cosine N c hsupport hnorm ell hell
  have hlo := hr.2.2.2
  rw [hgap] at hlo
  linarith

#print axioms path_correlation_le_cos
#print axioms residue_block_bounds
#print axioms coefficient_gamma_le_cosine
#print axioms gap_floor_positive
#print axioms finite_record_cosine_obstruction

end D5.S3.Quantum.QuantumChannels.FiniteRecordCosineObstruction
