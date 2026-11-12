/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionFamily
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionFamily
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Finite bias mixtures propagate scalar pairing defects at arbitrary order. -/

/-
proof_shape: TopOrderTransfer, oddQ, oddDenom, oddValue, oddWeight, oddMoment,
  oddObstructionConstant, evenQ, evenT, evenValue, evenWeight, evenMoment,
  mixtureData: definitions.
proof_shape: oddQ_step, oddFamily_properties, evenFamily_properties,
  top_order_transfer_fails: content.
proof_shape: oddQ_strictAnti: bind-only (consumer: oddQ_lt).
proof_shape: oddQ_lt: bind-only (consumer: oddFamily_properties).
proof_shape: mixtureData_ratio, mixture_transfer_contradiction: bind-only
  (local helpers consumed along the proof path of top_order_transfer_fails).
escape_witness: oddFamily_properties gives a three-point law with zero top
  moment and strictly negative propagated lower defects; evenFamily_properties
  gives a three-point law with zero top scalar defect and strictly positive
  propagated lower defects. The core propagation limit and uniform leading-term
  estimate turn these laws into nonzero full-defect limits, contradicting the
  unchanged transfer proposition in top_order_transfer_fails.
admission_basis: escape-witness.
-/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.TopOrderObstructionCore

open scoped BigOperators Topology
open Filter

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open FifthOrderTopOnlyRefutation

/-- Top distinct pairing control and bounded lower distinct moments are proposed
as sufficient conditions for the normalized full pairing defect to vanish. -/
def TopOrderTransfer (k : ℕ) : Prop :=
  ∀ (C : ℝ), 1 ≤ C → ∀ (D : ℕ → FifthData),
    (∀ n, (D n).ℓ 1 = 1) →
    (∀ n (y : (D n).A), 0 ≤ (D n).ℓ (y * y)) →
    (∀ n d, (D n).ℓ ((D n).Y d) = 0) →
    (∀ n d, (D n).Y d ^ 2 = (D n).a • (D n).Y d + (D n).b • 1) →
    (∀ n, (D n).L ≤ (D n).H) →
    (∀ n, 1 ≤ (D n).L) →
    (∀ n, |(D n).a| ≤ C * (D n).L) →
    (∀ n, |(D n).b| ≤ C * (D n).L) →
    (∀ n, (Fintype.card (D n).ι : ℝ) ≤ C * (D n).H) →
    (∀ n r, 2 ≤ r → r < k → ∀ (g : Fin r → (D n).ι → ℝ),
      (∀ i d, |g i d| ≤ 1) →
      |distinctIndexMoment (D n).ℓ (D n).Y g| ≤
        C * (Real.sqrt ((D n).H * (D n).L)) ^ r) →
    (∀ n (g : Fin k → (D n).ι → ℝ), (∀ i d, |g i d| ≤ 1) →
      |subsetDistinctMoment (D n).ℓ (D n).Y g Finset.univ -
        finitePairingPolynomial Finset.univ
          (subsetDistinctMoment (D n).ℓ (D n).Y g)| ≤
        C * (Real.sqrt ((D n).H * (D n).L)) ^ k / (D n).H) →
    Tendsto (fun n => (D n).L / (D n).H) atTop (𝓝 0) →
    Tendsto (fun n =>
      (subsetFamilyMoment (D n).ℓ (D n).Y (fun (_ : Fin k) _ => (1 : ℝ)) Finset.univ -
        finitePairingPolynomial Finset.univ
          (subsetFamilyMoment (D n).ℓ (D n).Y (fun (_ : Fin k) _ => (1 : ℝ)))) /
        (Real.sqrt ((D n).H * (D n).L)) ^ k) atTop (𝓝 0)

private def oddQ (j : ℕ) : ℝ := ((2 : ℝ)^j - 2) / ((3 : ℝ)^j - 3)

private lemma oddQ_step (j : ℕ) (hj : 2 ≤ j) : oddQ (j+1) < oddQ j := by
  have h2 : (4 : ℝ) ≤ 2^j := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
    norm_num at h
    exact h
  have h3 : (9 : ℝ) ≤ 3^j := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hj
    norm_num at h
    exact h
  have h3' : (9 : ℝ) ≤ 3^(j+1) := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
      (show 2 ≤ j+1 by omega)
    norm_num at h
    exact h
  have hgap : 0 < (3 : ℝ)^j * (2^j - 4) + 3 * 2^j := by
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (by positivity) (by linarith)) (by positivity)
  have hid : ((2 : ℝ)^j - 2) * (3^(j+1) - 3) -
      (2^(j+1) - 2) * (3^j - 3) = 3^j * (2^j - 4) + 3 * 2^j := by
    simp only [pow_succ]
    ring
  simp only [oddQ]
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  linarith


private lemma oddQ_strictAnti : StrictAnti (fun n : ℕ => oddQ (n+2)) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    oddQ_step (n+2) (by omega)


private lemma oddQ_lt {j k : ℕ} (hj : 2 ≤ j) (hjk : j < k) : oddQ k < oddQ j := by
  have h := oddQ_strictAnti (show j-2 < k-2 by omega)
  simpa only [Nat.sub_add_cancel hj,
    Nat.sub_add_cancel (show 2 ≤ k by omega)] using h


private def oddDenom (k : ℕ) : ℝ := (3 : ℝ)^(k+1) - 2^(k+1) - 5


private def oddValue : Fin 3 → ℝ := ![-2, 1, 3]


private def oddWeight (k : ℕ) : Fin 3 → ℝ :=
  ![((3 : ℝ)^k - 3) / oddDenom k,
    (2 * (3 : ℝ)^k - 3 * 2^k) / oddDenom k,
    ((2 : ℝ)^k - 2) / oddDenom k]


private def oddMoment (k j : ℕ) : ℝ := ∑ z : Fin 3, oddWeight k z * oddValue z ^ j


private def oddObstructionConstant (k : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (k/2+1),
    (k.choose (2*p) : ℝ) * (Nat.doubleFactorial (2*p-1) : ℝ) * oddMoment k (k-2*p)


private lemma oddFamily_properties (k : ℕ) (hk : 5 ≤ k) (ho : Odd k) :
    (∀ z, 0 < oddWeight k z) ∧
    (∑ z : Fin 3, oddWeight k z = 1) ∧
    oddMoment k 0 = 1 ∧ oddMoment k 1 = 0 ∧ oddMoment k k = 0 ∧
    (∀ j, 3 ≤ j → j < k → Odd j → oddMoment k j < 0) ∧
    (∀ j, j ≤ k → Odd j → oddMoment k j ≤ 0) ∧
    (∀ j, |oddMoment k j| ≤ 3^j) ∧ oddObstructionConstant k < 0 := by
  have odd_numerators_pos (k : ℕ) (hk : 2 ≤ k) :
      0 < (3 : ℝ)^k - 3 ∧ 0 < 2 * (3 : ℝ)^k - 3 * 2^k ∧
        0 < (2 : ℝ)^k - 2 := by
    have h2 : (4 : ℝ) ≤ 2^k := by
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
      norm_num at h
      exact h
    have h3 : (9 : ℝ) ≤ 3^k := by
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hk
      norm_num at h
      exact h
    refine ⟨by linarith, ?_, by linarith⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k = n+2 := ⟨k-2, by omega⟩
    rw [hn]
    have hpow : (2 : ℝ)^n ≤ 3^n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
    have hp : (0 : ℝ) < 3^n := by positivity
    simp only [pow_add]
    norm_num
    nlinarith

  have oddDenom_pos (k : ℕ) (hk : 2 ≤ k) : 0 < oddDenom k := by
    obtain ⟨h1, h2, h3⟩ := odd_numerators_pos k hk
    have hid : oddDenom k = ((3 : ℝ)^k - 3) +
        (2 * (3 : ℝ)^k - 3 * 2^k) + ((2 : ℝ)^k - 2) := by
      simp only [oddDenom, pow_succ]
      ring
    rw [hid]
    linarith

  have oddWeight_pos (k : ℕ) (hk : 2 ≤ k) (z : Fin 3) : 0 < oddWeight k z := by
    obtain ⟨h1, h2, h3⟩ := odd_numerators_pos k hk
    have hd := oddDenom_pos k hk
    fin_cases z
    · exact div_pos h1 hd
    · exact div_pos h2 hd
    · exact div_pos h3 hd

  have oddWeight_sum (k : ℕ) (hk : 2 ≤ k) : ∑ z : Fin 3, oddWeight k z = 1 := by
    have hd := (oddDenom_pos k hk).ne'
    simp [oddWeight, Fin.sum_univ_succ]
    field_simp [hd]
    simp only [oddDenom, pow_succ]
    ring

  have oddMoment_zero (k : ℕ) (hk : 2 ≤ k) : oddMoment k 0 = 1 := by
    simpa [oddMoment] using oddWeight_sum k hk

  have oddMoment_one (k : ℕ) : oddMoment k 1 = 0 := by
    simp [oddMoment, oddValue, oddWeight, Fin.sum_univ_succ]
    ring

  have oddMoment_formula (k j : ℕ) (hj : Odd j) :
      oddMoment k j =
        (((2 : ℝ)^k - 2) * (3^j - 3) - (3^k - 3) * (2^j - 2)) /
          oddDenom k := by
    simp [oddMoment, oddValue, oddWeight, Fin.sum_univ_succ, hj.neg_pow]
    ring

  have oddMoment_top_zero (k : ℕ) (hk : Odd k) : oddMoment k k = 0 := by
    rw [oddMoment_formula k k hk]
    ring

  have oddMoment_neg {k j : ℕ} (hj : 3 ≤ j) (hjk : j < k) (ho : Odd j) :
      oddMoment k j < 0 := by
    have h3j : (9 : ℝ) ≤ 3^j := by
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
        (show 2 ≤ j by omega)
      norm_num at h
      exact h
    have h3k : (9 : ℝ) ≤ 3^k := by
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
        (show 2 ≤ k by omega)
      norm_num at h
      exact h
    have hq := oddQ_lt (show 2 ≤ j by omega) hjk
    simp only [oddQ] at hq
    have hc := (div_lt_div_iff₀ (by linarith : 0 < (3 : ℝ)^k - 3)
      (by linarith : 0 < (3 : ℝ)^j - 3)).mp hq
    rw [oddMoment_formula k j ho]
    exact div_neg_of_neg_of_pos (by linarith) (oddDenom_pos k (by omega))

  have oddMoment_nonpos {k j : ℕ} (hk : 2 ≤ k) (ho : Odd k)
      (hj : j ≤ k) (hjo : Odd j) : oddMoment k j ≤ 0 := by
    by_cases h1 : j = 1
    · subst j
      rw [oddMoment_one]
    by_cases ht : j = k
    · subst j
      rw [oddMoment_top_zero k ho]
    exact (oddMoment_neg (by have := Nat.odd_iff.mp hjo; omega) (by omega) hjo).le

  have oddMoment_abs_le (k : ℕ) (hk : 2 ≤ k) (j : ℕ) : |oddMoment k j| ≤ 3^j := by
    classical
    calc
      _ ≤ ∑ z : Fin 3, |oddWeight k z * oddValue z ^ j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z : Fin 3, oddWeight k z * 3^j := by
        apply Finset.sum_le_sum
        intro z hz
        rw [abs_mul, abs_of_pos (oddWeight_pos k hk z), abs_pow]
        apply mul_le_mul_of_nonneg_left _ (oddWeight_pos k hk z).le
        apply pow_le_pow_left₀ (abs_nonneg _)
        fin_cases z <;> norm_num [oddValue]
      _ = 3^j := by rw [← Finset.sum_mul, oddWeight_sum k hk, one_mul]

  have oddObstructionConstant_neg (k : ℕ) (hk : 5 ≤ k) (ho : Odd k) :
      oddObstructionConstant k < 0 := by
    classical
    have hko := Nat.odd_iff.mp ho
    have hle (p : ℕ) (hp : p ∈ Finset.range (k/2+1)) : 2*p ≤ k := by
      have := Finset.mem_range.mp hp
      omega
    have hall (p : ℕ) (hp : p ∈ Finset.range (k/2+1)) :
        (k.choose (2*p) : ℝ) * (Nat.doubleFactorial (2*p-1) : ℝ) *
          oddMoment k (k-2*p) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
      apply oddMoment_nonpos (by omega) ho (by omega)
      apply Nat.odd_iff.mpr
      have := hle p hp
      omega
    let p := (k-3)/2
    have hp : p ∈ Finset.range (k/2+1) := by
      apply Finset.mem_range.mpr
      dsimp [p]
      omega
    have hj : k-2*p = 3 := by dsimp [p]; omega
    have hc : 0 < (k.choose (2*p) : ℝ) * (Nat.doubleFactorial (2*p-1) : ℝ) := by
      apply mul_pos
      · exact_mod_cast Nat.choose_pos (hle p hp)
      · exact_mod_cast Nat.doubleFactorial_pos (2*p-1)
    have hneg : (k.choose (2*p) : ℝ) * (Nat.doubleFactorial (2*p-1) : ℝ) *
        oddMoment k (k-2*p) < 0 := by
      rw [hj]
      exact mul_neg_of_pos_of_neg hc (oddMoment_neg (by omega) (by omega) (by decide))
    have hs := Finset.sum_lt_sum hall ⟨p, hp, hneg⟩
    simpa only [oddObstructionConstant, Finset.sum_const_zero] using hs
  exact ⟨oddWeight_pos k (by omega), oddWeight_sum k (by omega),
    oddMoment_zero k (by omega), oddMoment_one k, oddMoment_top_zero k ho,
    fun j hj hjk hjo => oddMoment_neg hj hjk hjo,
    fun j hj hjo => oddMoment_nonpos (by omega) ho hj hjo,
    oddMoment_abs_le k (by omega), oddObstructionConstant_neg k hk ho⟩

private def evenQ (m : ℕ) : ℝ := Nat.doubleFactorial (2 * m - 1)

private def evenT (m : ℕ) : ℝ := evenQ m ^ (((m - 1 : ℕ) : ℝ)⁻¹)

private def evenValue (m : ℕ) : Fin 3 → ℝ :=
  ![Real.sqrt (evenT m), -Real.sqrt (evenT m), 0]

private def evenWeight (m : ℕ) : Fin 3 → ℝ :=
  ![1 / (2 * evenT m), 1 / (2 * evenT m), 1 - 1 / evenT m]

private def evenMoment (m j : ℕ) : ℝ :=
  ∑ z : Fin 3, evenWeight m z * evenValue m z ^ j

private lemma evenFamily_properties (m : ℕ) (hm : 3 ≤ m) :
    1 < evenT m ∧
    evenT m ^ (m - 1) = evenQ m ∧
    (∀ z : Fin 3, 0 < evenWeight m z) ∧
    (∑ z : Fin 3, evenWeight m z) = 1 ∧
    evenMoment m 0 = 1 ∧
    evenMoment m 1 = 0 ∧
    evenMoment m 2 = 1 ∧
    evenMoment m (2 * m) = evenQ m ∧
    (∀ r : ℕ, 1 ≤ r → evenMoment m (2 * r) = evenT m ^ (r - 1)) ∧
    (∀ j : ℕ, Odd j → evenMoment m j = 0) ∧
    (∀ r : ℕ, 2 ≤ r → r < m →
      0 < evenMoment m (2 * r) - evenQ r * evenMoment m 2 ^ r) ∧
    (∀ z : Fin 3, |evenValue m z| ≤ Real.sqrt (evenT m)) := by
  have evenQ_pos (m : ℕ) : 0 < evenQ m := by
    dsimp only [evenQ]
    exact_mod_cast Nat.doubleFactorial_pos (2 * m - 1)

  have evenT_pos (m : ℕ) : 0 < evenT m :=
    Real.rpow_pos_of_pos (evenQ_pos m) _

  have evenT_pow (m : ℕ) (hm : 2 ≤ m) :
      evenT m ^ (m - 1) = evenQ m := by
    exact Real.rpow_inv_natCast_pow (evenQ_pos m).le (by omega)

  have evenQ_succ (m : ℕ) (hm : 1 ≤ m) :
      evenQ (m + 1) = (2 * (m : ℝ) + 1) * evenQ m := by
    have hn : Nat.doubleFactorial (2 * (m + 1) - 1) =
        (2 * m + 1) * Nat.doubleFactorial (2 * m - 1) := by
      rw [show 2 * (m + 1) - 1 = (2 * m - 1) + 2 by omega,
        Nat.doubleFactorial_add_two]
      congr 1
      omega
    change ((Nat.doubleFactorial (2 * (m + 1) - 1) : ℕ) : ℝ) = _
    dsimp only [evenQ]
    exact_mod_cast hn

  have evenQ_le (m : ℕ) (hm : 2 ≤ m) :
      evenQ m ≤ (2 * (m : ℝ) - 1) ^ (m - 1) := by
    have hprod : Nat.doubleFactorial (2 * m - 1) =
        ∏ i ∈ Finset.range (m - 1), (2 * (i + 1) + 1) := by
      rw [show 2 * m - 1 = 2 * (m - 1) + 1 by omega,
        Nat.doubleFactorial_eq_prod_odd]
    have hnat : Nat.doubleFactorial (2 * m - 1) ≤ (2 * m - 1) ^ (m - 1) := by
      calc
        _ = ∏ i ∈ Finset.range (m - 1), (2 * (i + 1) + 1) := hprod
        _ ≤ ∏ _i ∈ Finset.range (m - 1), (2 * m - 1) := by
          apply Finset.prod_le_prod
          intro i hi
          have hi' := Finset.mem_range.mp hi
          omega
        _ = _ := by simp
    have hreal : evenQ m ≤ ((2 * m - 1 : ℕ) : ℝ) ^ (m - 1) := by
      dsimp only [evenQ]
      exact_mod_cast hnat
    simpa only [Nat.cast_sub (by omega : 1 ≤ 2 * m), Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] using hreal

  have evenT_le (m : ℕ) (hm : 2 ≤ m) :
      evenT m ≤ 2 * (m : ℝ) - 1 := by
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    apply (pow_le_pow_iff_left₀ (evenT_pos m).le
      (by linarith : 0 ≤ 2 * (m : ℝ) - 1) (by omega : m - 1 ≠ 0)).mp
    rw [evenT_pow m hm]
    exact evenQ_le m hm

  have evenQ_gt_one (m : ℕ) (hm : 2 ≤ m) : 1 < evenQ m := by
    have hp : (1 : ℝ) ≤ evenQ (m - 1) := by
      dsimp only [evenQ]
      exact_mod_cast (Nat.succ_le_iff.mpr
        (Nat.doubleFactorial_pos (2 * (m - 1) - 1)))
    have hn : (1 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ m - 1 by omega)
    have h := evenQ_succ (m - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at h
    rw [h]
    nlinarith

  have evenT_gt_one (m : ℕ) (hm : 2 ≤ m) : 1 < evenT m := by
    apply Real.one_lt_rpow (evenQ_gt_one m hm)
    apply inv_pos.mpr
    exact_mod_cast (show 0 < m - 1 by omega)

  have evenT_lt_succ (m : ℕ) (hm : 2 ≤ m) :
      evenT m < evenT (m + 1) := by
    apply (pow_lt_pow_iff_left₀ (evenT_pos m).le (evenT_pos (m + 1)).le
      (by omega : m ≠ 0)).mp
    calc
      evenT m ^ m = evenT m ^ ((m - 1) + 1) := by congr 1; omega
      _ = evenQ m * evenT m := by rw [pow_succ, evenT_pow m hm]
      _ < evenQ m * (2 * (m : ℝ) + 1) :=
        mul_lt_mul_of_pos_left (by linarith [evenT_le m hm]) (evenQ_pos m)
      _ = evenQ (m + 1) := by rw [evenQ_succ m (by omega)]; ring
      _ = evenT (m + 1) ^ m := by
        simpa only [Nat.add_sub_cancel] using (evenT_pow (m + 1) (by omega)).symm

  have evenT_strict (r m : ℕ) (hr : 2 ≤ r) (hrm : r < m) :
      evenT r < evenT m := by
    have hmono : StrictMono (fun n : ℕ => evenT (n + 2)) :=
      strictMono_nat_of_lt_succ (fun n => evenT_lt_succ (n + 2) (by omega))
    have h := hmono (show r - 2 < m - 2 by omega)
    simpa only [Nat.sub_add_cancel hr,
      Nat.sub_add_cancel (by omega : 2 ≤ m)] using h

  have evenWeight_positive (m : ℕ) (hm : 2 ≤ m) (z : Fin 3) :
      0 < evenWeight m z := by
    have ht := evenT_gt_one m hm
    have htpos := evenT_pos m
    fin_cases z
    · dsimp [evenWeight]
      positivity
    · dsimp [evenWeight]
      positivity
    · dsimp [evenWeight]
      apply sub_pos.mpr
      exact (div_lt_one htpos).mpr (by simpa using ht)

  have evenWeight_sum (m : ℕ) : ∑ z : Fin 3, evenWeight m z = 1 := by
    have htne := ne_of_gt (evenT_pos m)
    norm_num [evenWeight, Fin.sum_univ_succ] <;> field_simp [htne] <;> ring

  have evenMoment_zero (m : ℕ) : evenMoment m 0 = 1 := by
    simpa only [evenMoment, pow_zero, mul_one] using evenWeight_sum m

  have evenMoment_odd (m j : ℕ) (hj : Odd j) : evenMoment m j = 0 := by
    have hj0 : j ≠ 0 := by
      obtain ⟨r, hr⟩ := hj
      omega
    norm_num [evenMoment, evenWeight, evenValue, Fin.sum_univ_succ,
      hj.neg_pow, hj0] <;> ring

  have evenMoment_even (m r : ℕ) (hr : 1 ≤ r) :
      evenMoment m (2 * r) = evenT m ^ (r - 1) := by
    have htne := ne_of_gt (evenT_pos m)
    have hzero : 2 * r ≠ 0 := by omega
    have hpower : Real.sqrt (evenT m) ^ (2 * r) = evenT m ^ r := by
      rw [pow_mul, Real.sq_sqrt (evenT_pos m).le]
    have hrec : evenT m ^ r = evenT m ^ (r - 1) * evenT m := by
      rw [← pow_succ, Nat.sub_add_cancel hr]
    norm_num [evenMoment, evenWeight, evenValue, Fin.sum_univ_succ,
      (even_two_mul r).neg_pow, hzero, hpower]
    rw [hrec]
    field_simp [htne]
    ring

  have evenMoment_one (m : ℕ) : evenMoment m 1 = 0 :=
    evenMoment_odd m 1 (by decide)

  have evenMoment_two (m : ℕ) : evenMoment m 2 = 1 := by
    simpa using evenMoment_even m 1 (by omega)

  have evenMoment_top (m : ℕ) (hm : 2 ≤ m) :
      evenMoment m (2 * m) = evenQ m := by
    rw [evenMoment_even m m (by omega), evenT_pow m hm]

  have evenMoment_lower_defect (r m : ℕ) (hr : 2 ≤ r) (hrm : r < m) :
      0 < evenMoment m (2 * r) - evenQ r * evenMoment m 2 ^ r := by
    rw [evenMoment_even m r (by omega), evenMoment_two, one_pow, mul_one,
      sub_pos, ← evenT_pow r hr]
    exact pow_lt_pow_left₀ (evenT_strict r m hr hrm) (evenT_pos r).le (by omega)

  have evenValue_abs_le (m : ℕ) (z : Fin 3) :
      |evenValue m z| ≤ Real.sqrt (evenT m) := by
    fin_cases z <;> simp [evenValue, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact ⟨evenT_gt_one m (by omega), evenT_pow m (by omega),
    evenWeight_positive m (by omega), evenWeight_sum m, evenMoment_zero m,
    evenMoment_one m, evenMoment_two m, evenMoment_top m (by omega),
    evenMoment_even m, evenMoment_odd m,
    fun r hr hrm => evenMoment_lower_defect r m hr hrm, evenValue_abs_le m⟩


private def mixtureData {κ : Type} [Fintype κ]
    (offset : ℕ) (zValue zWeight : κ → ℝ) (n : ℕ) : FifthData where
  ι := Fin (n + offset)
  A := (Fin (n + offset) → Bool) → ℝ
  ℓ := mixtureFunctional (n + offset) zValue zWeight
  Y := modelY (n + offset)
  a := 0
  b := 1
  H := ((n + offset : ℕ) : ℝ)
  L := 1


set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Every order at least five admits a positive three-point bias mixture whose
normalized full pairing defect has a nonzero limit despite top-order control. -/
theorem top_order_transfer_fails : ∀ k, 5 ≤ k → ¬ TopOrderTransfer k := by
  classical

  have mixtureData_ratio {κ : Type} [Fintype κ]
      (offset : ℕ) (zValue zWeight : κ → ℝ) :
      Tendsto (fun n : ℕ => (mixtureData offset zValue zWeight n).L /
        (mixtureData offset zValue zWeight n).H) atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => 1 / ((n + offset : ℕ) : ℝ)) atTop (𝓝 0)
    simp only [Nat.cast_add, one_div]
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (offset : ℝ) tendsto_natCast_atTop_atTop)

  have mixture_transfer_contradiction {κ : Type} [Fintype κ]
      (k offset : ℕ) (C c : ℝ) (zValue zWeight : κ → ℝ)
      (hC : 1 ≤ C) (hoffset : 1 ≤ offset)
      (hweight : ∀ z, 0 ≤ zWeight z) (hnorm : ∑ z, zWeight z = 1)
      (hcenter : ∑ z, zWeight z * zValue z = 0)
      (hbound : ∀ n z, |zValue z| ≤ Real.sqrt ((n + offset : ℕ) : ℝ))
      (hlower : ∀ r, 2 ≤ r → r < k → |∑ z, zWeight z * zValue z ^ r| ≤ C)
      (htop : ∀ n (g : Fin k → Fin (n + offset) → ℝ), (∀ i d, |g i d| ≤ 1) →
        |subsetPairingDefect (mixtureFunctional (n + offset) zValue zWeight)
          (modelY (n + offset)) g Finset.univ| ≤
        C * Real.sqrt ((n + offset : ℕ) : ℝ) ^ k / ((n + offset : ℕ) : ℝ))
      (hlimit : Tendsto (fun n : ℕ =>
        (subsetFamilyMoment (mixtureFunctional (n + offset) zValue zWeight)
          (modelY (n + offset)) (fun (_ : Fin k) _ => (1 : ℝ)) Finset.univ -
        finitePairingPolynomial Finset.univ
          (subsetFamilyMoment (mixtureFunctional (n + offset) zValue zWeight)
            (modelY (n + offset)) (fun (_ : Fin k) _ => (1 : ℝ)))) /
        Real.sqrt ((n + offset : ℕ) : ℝ) ^ k) atTop (𝓝 c))
      (hc : c ≠ 0) : ¬ TopOrderTransfer k := by
    classical
    intro hclaim
    let D := mixtureData offset zValue zWeight
    have hN (n : ℕ) : 0 < n + offset := by omega
    have hN1 (n : ℕ) : (1 : ℝ) ≤ ((n + offset : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ n + offset by omega)
    have hone : ∀ n, (D n).ℓ 1 = 1 := by
      intro n
      simpa [D, mixtureData, hnorm] using
        (mixture_character (n + offset) zValue zWeight ∅)
    have hcent : ∀ n d, (D n).ℓ ((D n).Y d) = 0 := by
      intro n d
      simpa [D, mixtureData, hcenter] using
        (mixture_character (n + offset) zValue zWeight {d})
    have hquad : ∀ n d, (D n).Y d ^ 2 = (D n).a • (D n).Y d + (D n).b • 1 := by
      intro n d
      funext ω
      change sign (ω d)^2 = 0 * sign (ω d) + 1 * 1
      cases ω d <;> norm_num [sign]
    have hlow : ∀ n r, 2 ≤ r → r < k → ∀ g : Fin r → (D n).ι → ℝ,
        (∀ i d, |g i d| ≤ 1) →
        |distinctIndexMoment (D n).ℓ (D n).Y g| ≤
          C * Real.sqrt ((D n).H * (D n).L)^r := by
      intro n r hr hrk g hg
      dsimp only [D, mixtureData] at g hg ⊢
      simp only [mul_one]
      have hb := (mixture_distinct_bound (n + offset) r (hN n) zValue zWeight g hg).trans
        (mul_le_mul_of_nonneg_right (hlower r hr hrk) (by positivity))
      first
      | exact hb
      | convert hb using 1
        congr 1
        unfold distinctIndexMoment
        apply Finset.sum_congr
        · ext x
          simp
        · intro x hx
          rfl
    have ht : ∀ n (g : Fin k → (D n).ι → ℝ), (∀ i d, |g i d| ≤ 1) →
        |subsetDistinctMoment (D n).ℓ (D n).Y g Finset.univ -
          finitePairingPolynomial Finset.univ (subsetDistinctMoment (D n).ℓ (D n).Y g)| ≤
          C * Real.sqrt ((D n).H * (D n).L)^k / (D n).H := by
      intro n g hg
      simpa only [D, mixtureData, mul_one, subsetPairingDefect] using htop n g hg
    have hzero := hclaim C hC D hone
      (by
        intro n y
        exact mixture_positive (n + offset) zValue zWeight
          (hbound n) hweight (hN n) y) hcent hquad
      (by intro n; exact hN1 n)
      (by intro n; exact le_refl 1)
      (by intro n; simp [D, mixtureData]; linarith)
      (by intro n; simpa [D, mixtureData] using hC)
      (by
        intro n
        change (Fintype.card (Fin (n + offset)) : ℝ) ≤ C * ((n + offset : ℕ) : ℝ)
        rw [Fintype.card_fin]
        nlinarith [hN1 n]) hlow ht (mixtureData_ratio offset zValue zWeight)
    have hz : Tendsto (fun n : ℕ =>
        (subsetFamilyMoment (mixtureFunctional (n + offset) zValue zWeight)
          (modelY (n + offset)) (fun (_ : Fin k) _ => (1 : ℝ)) Finset.univ -
        finitePairingPolynomial Finset.univ
          (subsetFamilyMoment (mixtureFunctional (n + offset) zValue zWeight)
            (modelY (n + offset)) (fun (_ : Fin k) _ => (1 : ℝ)))) /
        Real.sqrt ((n + offset : ℕ) : ℝ) ^ k) atTop (𝓝 0) := by
      simpa only [D, mixtureData, mul_one] using hzero
    exact hc (tendsto_nhds_unique hlimit hz)

  have odd_top_order_transfer_fails (k : ℕ) (hk : 5 ≤ k) (ho : Odd k) :
      ¬ TopOrderTransfer k := by
    classical
    obtain ⟨hw, hn, hm0, hm1, hmk, hneg, hnonpos, habs, hc⟩ :=
      oddFamily_properties k hk ho
    have hC : (1 : ℝ) ≤ 3^k := one_le_pow₀ (by norm_num)
    have hlow (r : ℕ) (hr : 2 ≤ r) (hrk : r < k) :
        |∑ z : Fin 3, oddWeight k z * oddValue z ^ r| ≤ (3 : ℝ)^k := by
      exact (habs r).trans (pow_le_pow_right₀ (by norm_num) hrk.le)
    have hlim := mixture_propagation_limit k oddValue (oddWeight k) (3^k) hC
      (by simpa only [scalarMoment, oddMoment] using hm0)
      (by simpa only [scalarMoment, oddMoment] using hm1)
      (by intro r hr hrk; exact hlow r hr hrk)
    have heq : (∑ p ∈ Finset.range (k / 2 + 1),
        ((k.choose (2 * p) * Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) *
          scalarDefect oddValue (oddWeight k) (k - 2 * p)) = oddObstructionConstant k := by
      apply Finset.sum_congr rfl
      intro p hp
      have hple : 2*p ≤ k := by have := Finset.mem_range.mp hp; omega
      have hj : Odd (k - 2*p) := Nat.Odd.sub_even hple ho (even_two_mul p)
      simp [scalarDefect, scalarGaussian, scalarMoment, oddMoment, oddObstructionConstant,
        Nat.not_even_iff_odd.mpr hj, Nat.cast_mul, mul_assoc]
    rw [heq] at hlim
    apply mixture_transfer_contradiction k 9 (3^k) (oddObstructionConstant k)
      oddValue (oddWeight k) hC (by omega)
      (fun z => (hw z).le) hn
      (by simpa only [oddMoment, pow_one] using hm1)
      (by
        intro n z
        have hz : |oddValue z| ≤ (3 : ℝ) := by fin_cases z <;> norm_num [oddValue]
        apply hz.trans
        apply (Real.le_sqrt (by norm_num) (by positivity)).2
        exact_mod_cast (show 9 ≤ n+9 by omega))
      hlow
      (by
        intro n g hg
        have hR : subsetDistinctMoment (mixtureFunctional (n+9) oddValue (oddWeight k))
            (modelY (n+9)) g Finset.univ = 0 := by
          rw [SixthOrderTopPairingRefutation.subsetDistinct_univ, mixture_distinct_moments,
            ← oddMoment, hmk]
          simp
        have hempty : ((Finset.univ : Finset (Finset (Finset (Fin k)))).filter
            (IsPerfectPairing Finset.univ)) = ∅ := by
          apply Finset.card_eq_zero.mp
          rw [perfectPairingCount]
          simp [Nat.not_even_iff_odd.mpr ho]
        simp [subsetPairingDefect, hR, finitePairingPolynomial, hempty]
        positivity)
      (hlim.comp (tendsto_add_atTop_nat 9)) (ne_of_lt hc)

  have even_top_order_transfer_fails (m : ℕ) (hm : 3 ≤ m) :
      ¬ TopOrderTransfer (2*m) := by
    classical
    obtain ⟨ht, htpow, hw, hn, hm0, hm1, hm2, hmtop, hmeven, hmodd, hdef, hsupport⟩ :=
      evenFamily_properties m hm
    let c : ℝ := ∑ p ∈ Finset.range ((2*m)/2+1),
      (((2*m).choose (2*p) * Nat.doubleFactorial (2*p-1) : ℕ) : ℝ) *
        scalarDefect (evenValue m) (evenWeight m) (2*m-2*p)
    have hscalar (r : ℕ) :
        scalarDefect (evenValue m) (evenWeight m) (2*r) =
        evenMoment m (2*r) - evenQ r * evenMoment m 2 ^ r := by
      simp [scalarDefect, scalarMoment, scalarGaussian, evenMoment, evenQ,
        even_two_mul, show 2*r/2 = r by omega]
    have hdtop : scalarDefect (evenValue m) (evenWeight m) (2*m) = 0 := by
      rw [hscalar, hmtop, hm2, one_pow, mul_one, sub_self]
    have hd0 : scalarDefect (evenValue m) (evenWeight m) 0 = 0 := by
      change evenMoment m 0 - scalarGaussian 0 (evenMoment m 2) = 0
      rw [hm0]
      norm_num [scalarGaussian, Nat.doubleFactorial]
    have hd2 : scalarDefect (evenValue m) (evenWeight m) 2 = 0 := by
      rw [show 2 = 2*1 by omega, hscalar]
      simp [evenQ, Nat.doubleFactorial]
    have hpos : 0 < c := by
      have hall (p : ℕ) (hp : p ∈ Finset.range ((2*m)/2+1)) :
          0 ≤ (((2*m).choose (2*p) * Nat.doubleFactorial (2*p-1) : ℕ) : ℝ) *
            scalarDefect (evenValue m) (evenWeight m) (2*m-2*p) := by
        have hple : p ≤ m := by have := Finset.mem_range.mp hp; omega
        apply mul_nonneg (by positivity)
        by_cases h0 : p = 0
        · simpa [h0] using le_of_eq hdtop.symm
        by_cases h1 : p = m
        · simp [h1, hd0]
        by_cases h2 : p+1 = m
        · have hj : 2*m-2*p = 2 := by omega
          simp [hj, hd2]
        have hj : 2*m-2*p = 2*(m-p) := by omega
        rw [hj, hscalar]
        exact (hdef (m-p) (by omega) (by omega)).le
      have hp : m-2 ∈ Finset.range ((2*m)/2+1) := by
        apply Finset.mem_range.mpr
        omega
      have hj : 2*m-2*(m-2) = 4 := by omega
      have hc : 0 < (((2*m).choose (2*(m-2)) *
          Nat.doubleFactorial (2*(m-2)-1) : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.doubleFactorial_pos _)
      have hd4 : 0 < scalarDefect (evenValue m) (evenWeight m) 4 := by
        rw [show 4 = 2*2 by omega, hscalar]
        exact hdef 2 (by omega) (by omega)
      have hs := Finset.sum_lt_sum hall ⟨m-2, hp, by rw [hj]; exact mul_pos hc hd4⟩
      simpa only [Finset.sum_const_zero] using hs
    let β : ℝ := 2 * (m : ℝ)^2 * evenQ m
    have hβeval : mixtureLeadingConstant (evenValue m) (evenWeight m) (2*m) = β := by
      have hm2' : scalarMoment (evenValue m) (evenWeight m) 2 = 1 := by
        simpa only [scalarMoment, evenMoment] using hm2
      have hmtop' : scalarMoment (evenValue m) (evenWeight m) (2*m) = evenQ m := by
        simpa only [scalarMoment, evenMoment] using hmtop
      have hQnonneg : 0 ≤ evenQ m := by unfold evenQ; positivity
      have hchooseNat : (2*m).choose 2 = m * (2*m-1) := by
        rw [Nat.choose_two_right,
          show 2*m*(2*m-1) = (m*(2*m-1))*2 by ring,
          Nat.mul_div_cancel _ (by decide : 0 < 2)]
      have hchoose : ((2*m).choose 2 : ℝ) = (m : ℝ) * (2*(m : ℝ)-1) := by
        have hc : ((2*m).choose 2 : ℝ) = (m : ℝ) * ((2*m-1 : ℕ) : ℝ) := by
          exact_mod_cast hchooseNat
        simpa only [Nat.cast_sub (by omega : 1 ≤ 2*m), Nat.cast_mul,
          Nat.cast_ofNat, Nat.cast_one] using hc
      have hgaussian : gaussianPairingCount (2*m) = evenQ m := by
        simp [gaussianPairingCount, evenQ, even_two_mul]
      have hhalf : 2*m/2 = m := by omega
      simp only [mixtureLeadingConstant, hm2', hmtop', abs_one, max_self, one_pow,
        mul_one, abs_of_nonneg hQnonneg, hchoose, hgaussian, hhalf]
      dsimp only [β]
      push_cast
      ring
    let M := ∑ r ∈ Finset.range (2*m), |scalarMoment (evenValue m) (evenWeight m) r|
    let C := max 1 (max M β)
    have hC : 1 ≤ C := le_max_left _ _
    have hβ : β ≤ C := (le_max_right M β).trans (le_max_right 1 _)
    have hlow (r : ℕ) (hr : 2 ≤ r) (hrk : r < 2*m) :
        |∑ z : Fin 3, evenWeight m z * evenValue m z ^ r| ≤ C := by
      exact (Finset.single_le_sum (fun i hi => abs_nonneg
        (scalarMoment (evenValue m) (evenWeight m) i))
        (Finset.mem_range.mpr hrk)).trans
          ((le_max_left M β).trans (le_max_right 1 _))
    obtain ⟨offset, hoff⟩ := exists_nat_ge (max (2*m : ℝ) (evenT m))
    have hsize (n : ℕ) : (2*m : ℝ) ≤ ((n+offset : ℕ) : ℝ) := by
      have := (le_max_left (2*m : ℝ) (evenT m)).trans hoff
      push_cast at *
      nlinarith [show (0 : ℝ) ≤ n by positivity]
    have hN (n : ℕ) : 0 < n+offset := by
      have hn := hsize n
      have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
      exact_mod_cast (show (0 : ℝ) < ((n+offset : ℕ) : ℝ) by linarith)
    have hlim := mixture_propagation_limit (2*m) (evenValue m) (evenWeight m) C hC
      (by simpa only [scalarMoment, evenMoment] using hm0)
      (by simpa only [scalarMoment, evenMoment] using hm1)
      (by intro r hr hrk; exact hlow r hr hrk)
    apply mixture_transfer_contradiction (2*m) offset C c (evenValue m) (evenWeight m)
      hC (by have := hN 0; omega) (fun z => (hw z).le) hn
      (by simpa only [evenMoment, pow_one] using hm1)
      (by
        intro n z
        apply (hsupport z).trans
        apply Real.sqrt_le_sqrt
        have := (le_max_right (2*m : ℝ) (evenT m)).trans hoff
        push_cast at *
        nlinarith [show (0 : ℝ) ≤ n by positivity])
      hlow
      (by
        intro n g hg
        have hb := mixture_uniform_leading_bound_all (n+offset) (evenValue m) (evenWeight m)
          (Finset.univ : Finset (Fin (2*m))) (hN n)
          (by simpa using (show 2*m ≤ n+offset by exact_mod_cast hsize n)) g hg
        simp only [Finset.card_univ, Fintype.card_fin, hdtop, zero_mul, sub_zero] at hb
        rw [hβeval] at hb
        have hs : 0 < Real.sqrt ((n+offset : ℕ) : ℝ) ^ (2*m) := by
          exact pow_pos (Real.sqrt_pos.2 (by exact_mod_cast hN n)) _
        rw [abs_div, abs_of_pos hs] at hb
        have hb' := (div_le_iff₀ hs).mp hb
        calc
          _ ≤ (β / ((n+offset : ℕ) : ℝ)) * Real.sqrt ((n+offset : ℕ) : ℝ)^(2*m) := hb'
          _ ≤ (C / ((n+offset : ℕ) : ℝ)) * Real.sqrt ((n+offset : ℕ) : ℝ)^(2*m) := by
            exact mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_right hβ (by positivity)) (by positivity)
          _ = _ := by ring)
      (by simpa only [c, Function.comp_def] using hlim.comp (tendsto_add_atTop_nat offset))
      (ne_of_gt hpos)

  intro k hk
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨m, hm⟩ := he
    have hkm : k = 2*m := by omega
    rw [hkm]
    exact even_top_order_transfer_fails m (by omega)
  · exact odd_top_order_transfer_fails k hk ho


end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
