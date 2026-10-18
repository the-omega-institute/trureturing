/- GID: D5/S3/Estimation/SequentialDecisionRisk/FiniteSupportPosteriorMoment
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/FiniteSupportPosteriorMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite exponential moments for the actual fixed-support posterior. -/

import D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
import D5.S3.Analytic.RealRootedCoefficientNewton

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportPosteriorMoment
noncomputable section

/-- Both exponential-moment bounds hold for the same complete observation,
actual posterior, and index set fixed after conditioning. -/
theorem finite_support_posterior_moment {M q s : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha1 : compensation M q r < 1)
    (e : Experiment) (o : Obs M s e) (I : Finset (Fin M)) (t : ℝ) (ht : 0 ≤ t) :
    (∑ S : Support M q, posterior r e o S *
      Real.exp (t * ((I ∩ S.val).card : ℝ))) ≤
      ∏ i ∈ I, (1 + (Real.exp t - 1) * inclusion q r e o i) ∧
    (∏ i ∈ I, (1 + (Real.exp t - 1) * inclusion q r e o i)) ≤
      Real.exp ((Real.exp t - 1) * ∑ i ∈ I, inclusion q r e o i) := by
  classical
  have ha : 0 ≤ compensation M q r := by
    unfold compensation
    positivity
  have cert := finite_support_bayes (s := s) hq hqm hr hr1 ha ha1 e
  obtain ⟨hZ, hw, hpost, _⟩ := cert.2.2.2.1 o
  let w : Fin M → ℝ := weight q r e o
  let E : Finset (Fin M) → ℕ → ℝ := fun U k =>
    ∑ A ∈ U.powersetCard k, ∏ i ∈ A, w i
  have hE (U : Finset (Fin M)) (k : ℕ) :
      E U k = (U.val.map w).esymm k := (Finset.esymm_map_val w U k).symm
  have hEnonneg (U : Finset (Fin M)) (k : ℕ) : 0 ≤ E U k := by
    exact sum_nonneg (fun A _ => prod_nonneg (fun i _ => (hw i).1.le))
  have hEpos (U : Finset (Fin M)) (k : ℕ) (hk : k ≤ U.card) : 0 < E U k := by
    exact sum_pos (fun A _ => prod_pos (fun i _ => (hw i).1))
      (powersetCard_nonempty.mpr hk)
  have hEzero (U : Finset (Fin M)) (k : ℕ) (hk : U.card < k) : E U k = 0 := by
    simp [E, powersetCard_eq_empty.mpr hk]
  have hE0 (U : Finset (Fin M)) : E U 0 = 1 := by simp [E]
  have hEinsert (U : Finset (Fin M)) (i : Fin M) (hi : i ∉ U) (k : ℕ) :
      E (insert i U) (k + 1) = E U (k + 1) + w i * E U k := by
    have hcons (a : ℝ) (v : Multiset ℝ) (n : ℕ) :
        (a ::ₘ v).esymm (n + 1) = v.esymm (n + 1) + a * v.esymm n := by
      simp [Multiset.esymm, Multiset.sum_map_mul_left]
    simp only [hE, insert_val_of_notMem hi, Multiset.map_cons, hcons]
  have hNewton (U : Finset (Fin M)) (k : ℕ) :
      E U k * E U (k + 2) ≤ (E U (k + 1)) ^ 2 := by
    by_cases hk : k + 2 ≤ U.card
    · have hn := D5.S3.Analytic.RealRootedCoefficientNewton.esymm_mul_esymm_le_sq_esymm
        (U.val.map w) k
      simp only [Multiset.card_map, card_val, ← hE] at hn
      have hcard : (k : ℝ) + 2 ≤ U.card := by exact_mod_cast hk
      have hL : 0 < ((k : ℝ) + 2) * ((U.card : ℝ) - k) :=
        mul_pos (by positivity) (by linarith)
      have hR : ((k : ℝ) + 1) * ((U.card : ℝ) - k - 1) ≤
          ((k : ℝ) + 2) * ((U.card : ℝ) - k) := by nlinarith
      have hs := sq_nonneg (E U (k + 1))
      have hb := mul_le_mul_of_nonneg_right hR hs
      exact (mul_le_mul_iff_right₀ hL).mp (hn.trans hb)
    · rw [hEzero U (k + 2) (by omega), mul_zero]
      exact sq_nonneg _
  have hpair (U : Finset (Fin M)) (i j : Fin M)
      (hi : i ∈ U) (hj : j ∈ U) (hij : i ≠ j) (k : ℕ) :
      E U (k + 2) * E ((U.erase i).erase j) k ≤
        E (U.erase i) (k + 1) * E (U.erase j) (k + 1) := by
    let C := (U.erase i).erase j
    have hiC : i ∉ C := by simp [C]
    have hjC : j ∉ C := by simp [C]
    have hei : U.erase i = insert j C := by
      exact (insert_erase (mem_erase.mpr ⟨hij.symm, hj⟩)).symm
    have hej : U.erase j = insert i C := by
      change U.erase j = insert i ((U.erase i).erase j)
      rw [erase_right_comm]
      exact (insert_erase (mem_erase.mpr ⟨hij, hi⟩)).symm
    have hU : U = insert i (insert j C) := by
      rw [← hei, insert_erase hi]
    have hni : i ∉ insert j C := by simp [hij, hiC]
    have hn := hNewton C k
    change E U (k + 2) * E C k ≤
      E (U.erase i) (k + 1) * E (U.erase j) (k + 1)
    rw [hei, hej, hU]
    rw [hEinsert C i hiC k, hEinsert C j hjC k,
      show k + 2 = (k + 1) + 1 by omega,
      hEinsert (insert j C) i hni (k + 1), hEinsert C j hjC (k + 1)]
    rw [hEinsert C j hjC k]
    simp only [erase_insert hjC, Nat.add_assoc, Nat.reduceAdd]
    nlinarith
  have hforce (U B : Finset (Fin M)) (n : ℕ)
      (hB : B ⊆ U) (hn : B.card ≤ n) :
      (∑ S ∈ U.powersetCard n, if B ⊆ S then ∏ i ∈ S, w i else 0) =
        (∏ i ∈ B, w i) * E (U \ B) (n - B.card) := by
    rw [← sum_filter]
    change (∑ S ∈ (U.powersetCard n).filter (fun S => B ⊆ S), ∏ i ∈ S, w i) =
      (∏ i ∈ B, w i) * ∑ T ∈ (U \ B).powersetCard (n - B.card), ∏ i ∈ T, w i
    rw [mul_sum]
    symm
    apply sum_bij (fun T _ => B ∪ T)
    · intro T hT
      obtain ⟨hTU, hTc⟩ := mem_powersetCard.mp hT
      have hd : Disjoint B T := by
        apply disjoint_left.mpr
        intro i hiB hiT
        exact (mem_sdiff.mp (hTU hiT)).2 hiB
      apply mem_filter.mpr
      refine ⟨mem_powersetCard.mpr ⟨union_subset hB (hTU.trans sdiff_subset), ?_⟩,
        subset_union_left⟩
      rw [card_union_of_disjoint hd, hTc]
      omega
    · intro T hT V hV heq
      have hdT : Disjoint T B := disjoint_of_subset_left
        (mem_powersetCard.mp hT).1 disjoint_sdiff_self_left
      have hdV : Disjoint V B := disjoint_of_subset_left
        (mem_powersetCard.mp hV).1 disjoint_sdiff_self_left
      have hh := congrArg (fun S : Finset (Fin M) => S \ B) heq
      simpa [union_sdiff_left, hdT.sdiff_eq_left, hdV.sdiff_eq_left] using hh
    · intro S hS
      obtain ⟨hSn, hBS⟩ := mem_filter.mp hS
      obtain ⟨hSU, hSc⟩ := mem_powersetCard.mp hSn
      refine ⟨S \ B, mem_powersetCard.mpr ⟨sdiff_subset_sdiff_left B hSU, ?_⟩,
        (union_sdiff_of_subset hBS)⟩
      rw [card_sdiff_of_subset hBS, hSc]
    · intro T hT
      have hd : Disjoint B T := by
        apply disjoint_left.mpr
        intro i hiB hiT
        exact (mem_sdiff.mp ((mem_powersetCard.mp hT).1 hiT)).2 hiB
      exact (prod_union hd).symm
  let F : Finset (Fin M) → ℕ → Finset (Fin M) → ℝ := fun U n B =>
    (∑ S ∈ U.powersetCard n, if B ⊆ S then ∏ i ∈ S, w i else 0) / E U n
  have hFnonneg (U B : Finset (Fin M)) (n : ℕ) : 0 ≤ F U n B := by
    apply div_nonneg _ (hEnonneg U n)
    apply sum_nonneg
    intro S _
    split_ifs
    · exact prod_nonneg (fun i _ => (hw i).1.le)
    · exact le_rfl
  have hFzero (U B : Finset (Fin M)) (n : ℕ) (hn : n < B.card) : F U n B = 0 := by
    have hz : (∑ S ∈ U.powersetCard n,
        if B ⊆ S then ∏ i ∈ S, w i else 0) = 0 := by
      apply sum_eq_zero
      intro S hS
      rw [if_neg]
      intro hBS
      have hc := card_le_card hBS
      have hSc := (mem_powersetCard.mp hS).2
      omega
    change _ / _ = 0
    rw [hz, zero_div]
  have hFempty (U : Finset (Fin M)) (n : ℕ) (hn : n ≤ U.card) : F U n ∅ = 1 := by
    change (∑ S ∈ U.powersetCard n, if ∅ ⊆ S then ∏ i ∈ S, w i else 0) / E U n = 1
    simp only [empty_subset, ↓reduceIte]
    exact div_self (ne_of_gt (hEpos U n hn))
  have hFformula (U B : Finset (Fin M)) (n : ℕ)
      (hB : B ⊆ U) (hn : B.card ≤ n) :
      F U n B = (∏ i ∈ B, w i) * E (U \ B) (n - B.card) / E U n := by
    change _ / _ = _
    rw [hforce U B n hB hn]
  have hFsingle (U : Finset (Fin M)) (i : Fin M) (hi : i ∈ U) (n : ℕ) :
      F U (n + 1) {i} = w i * E (U.erase i) n / E U (n + 1) := by
    rw [hFformula U {i} (n + 1) (singleton_subset_iff.mpr hi) (by simp)]
    simp only [prod_singleton, card_singleton, Nat.add_sub_cancel, sdiff_singleton_eq_erase]
  have hFnext (U B : Finset (Fin M)) (j : Fin M) (hj : j ∈ U)
      (hjB : j ∉ B) (hBU : B ⊆ U) (n : ℕ) (hBn : B.card ≤ n)
      (hn : n + 1 ≤ U.card) :
      F U (n + 1) (insert j B) = F U (n + 1) {j} * F (U.erase j) n B := by
    have hchild : n ≤ (U.erase j).card := by rw [card_erase_of_mem hj]; omega
    have hBchild : B ⊆ U.erase j := subset_erase.mpr ⟨hBU, hjB⟩
    rw [hFformula U (insert j B) (n + 1) (insert_subset hj hBU)
      (by rw [card_insert_of_notMem hjB]; omega), hFsingle U j hj n,
      hFformula (U.erase j) B n hBchild hBn, prod_insert hjB,
      card_insert_of_notMem hjB]
    have hd : U \ insert j B = U.erase j \ B := by ext i; simp; tauto
    rw [hd, show n + 1 - (B.card + 1) = n - B.card by omega]
    field_simp [ne_of_gt (hEpos (U.erase j) n hchild), ne_of_gt (hEpos U (n + 1) hn)]
  have hFdecrease (U : Finset (Fin M)) (i j : Fin M)
      (hi : i ∈ U) (hj : j ∈ U) (hij : i ≠ j) (n : ℕ)
      (hn : n + 1 ≤ U.card) :
      F (U.erase j) n {i} ≤ F U (n + 1) {i} := by
    cases n with
    | zero => rw [hFzero _ _ 0 (by simp)]; exact hFnonneg _ _ _
    | succ k =>
      have hic : i ∈ U.erase j := mem_erase.mpr ⟨hij, hi⟩
      have hchild : k + 1 ≤ (U.erase j).card := by rw [card_erase_of_mem hj]; omega
      rw [hFsingle (U.erase j) i hic k, hFsingle U i hi (k + 1)]
      apply (div_le_div_iff₀ (hEpos _ _ hchild) (hEpos _ _ hn)).mpr
      have hp := mul_le_mul_of_nonneg_left (hpair U i j hi hj hij k) (hw i).1.le
      simpa only [erase_right_comm, Nat.add_assoc, Nat.reduceAdd, mul_assoc,
        mul_comm, mul_left_comm] using hp
  have hFjoint (B : Finset (Fin M)) : ∀ (U : Finset (Fin M)) (n : ℕ),
      B ⊆ U → n ≤ U.card → F U n B ≤ ∏ i ∈ B, F U n {i} := by
    induction B using Finset.induction with
    | empty => intro U n _ hn; rw [hFempty U n hn, prod_empty]
    | @insert j B hjB ih =>
      intro U n hBU hn
      by_cases hBn : (insert j B).card ≤ n
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
          have : 0 < n := by rw [card_insert_of_notMem hjB] at hBn; omega
          exact Nat.exists_eq_succ_of_ne_zero (by omega)
        have hj : j ∈ U := hBU (mem_insert_self _ _)
        have hBU' : B ⊆ U := (subset_insert j B).trans hBU
        have hBk : B.card ≤ k := by rw [card_insert_of_notMem hjB] at hBn; omega
        have hchild : k ≤ (U.erase j).card := by rw [card_erase_of_mem hj]; omega
        rw [hFnext U B j hj hjB hBU' k hBk hn, prod_insert hjB]
        apply mul_le_mul_of_nonneg_left _ (hFnonneg U {j} (k + 1))
        apply (ih (U.erase j) k (subset_erase.mpr ⟨hBU', hjB⟩) hchild).trans
        apply prod_le_prod₀
        · intro i _; exact hFnonneg _ _ _
        · intro i hi
          exact hFdecrease U i j (hBU' hi) hj (by intro h; exact hjB (h ▸ hi)) k hn
      · rw [hFzero U (insert j B) n (by omega)]
        exact prod_nonneg (fun i _ => hFnonneg U {i} n)
  have hposterior_nonneg (S : Support M q) : 0 ≤ posterior r e o S := by
    rw [hpost S]
    exact div_nonneg (prod_nonneg (fun i _ => (hw i).1.le)) hZ.le
  have hinclusion_nonneg (i : Fin M) : 0 ≤ inclusion q r e o i := by
    unfold inclusion
    apply sum_nonneg
    intro S _
    split_ifs
    · exact hposterior_nonneg S
    · exact le_rfl
  have hx : 0 ≤ Real.exp t - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr ht)
  have hjoint (A : Finset (Fin M)) :
      (∑ S : Support M q, if A ⊆ S.val then posterior r e o S else 0) ≤
        ∏ i ∈ A, inclusion q r e o i := by
    have hsum (f : Finset (Fin M) → ℝ) :
        (∑ S : Support M q, f S.val) = ∑ S ∈ univ.powersetCard q, f S :=
      (sum_subtype _ (fun S => by simp) f).symm
    have hpartition : partition (q := q) r e o = E univ q := by
      exact hsum (fun S => ∏ i ∈ S, w i)
    have hactual (B : Finset (Fin M)) :
        (∑ S : Support M q, if B ⊆ S.val then posterior r e o S else 0) = F univ q B := by
      have hterm (S : Support M q) :
          (if B ⊆ S.val then posterior r e o S else 0) =
            (if B ⊆ S.val then ∏ i ∈ S.val, w i else 0) / partition (q := q) r e o := by
        split_ifs <;> simp only [hpost, zero_div] <;> rfl
      simp_rw [hterm]
      rw [← sum_div, hsum (fun T => if B ⊆ T then ∏ i ∈ T, w i else 0), hpartition]
    have hsingle (i : Fin M) : F univ q {i} = inclusion q r e o i := by
      rw [← hactual]
      simp only [singleton_subset_iff, inclusion]
    rw [hactual]
    simpa only [hsingle] using hFjoint A univ q (subset_univ A) (by simpa using hqm.le)
  have hpoint (S : Support M q) :
      Real.exp (t * ((I ∩ S.val).card : ℝ)) =
        ∏ i ∈ I, (1 + (Real.exp t - 1) * (if i ∈ S.val then 1 else 0)) := by
    have hf (i : Fin M) :
        (1 + (Real.exp t - 1) * (if i ∈ S.val then 1 else 0)) =
          if i ∈ S.val then Real.exp t else 1 := by
      split_ifs <;> ring
    simp only [hf, prod_ite, filter_mem_eq_inter, prod_const, prod_const_one, mul_one]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hprod (A : Finset (Fin M)) (S : Support M q) :
      (∏ i ∈ A, (Real.exp t - 1) * (if i ∈ S.val then 1 else 0)) =
        if A ⊆ S.val then (Real.exp t - 1) ^ A.card else 0 := by
    by_cases hA : A ⊆ S.val
    · rw [if_pos hA]
      simp only [prod_mul_distrib, prod_const]
      have hind : (∏ i ∈ A, (if i ∈ S.val then (1 : ℝ) else 0)) = 1 := by
        apply prod_eq_one
        intro i hi
        simp [hA hi]
      rw [hind, mul_one]
    · rw [if_neg hA]
      obtain ⟨i, hi, hnot⟩ := not_subset.mp hA
      exact prod_eq_zero hi (by simp [hnot])
  constructor
  · calc
      (∑ S : Support M q, posterior r e o S *
          Real.exp (t * ((I ∩ S.val).card : ℝ))) =
          ∑ A ∈ I.powerset, (Real.exp t - 1) ^ A.card *
            ∑ S : Support M q, if A ⊆ S.val then posterior r e o S else 0 := by
        simp_rw [hpoint, prod_one_add, hprod, mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro A _
        apply sum_congr rfl
        intro S _
        split_ifs <;> simp_all only [mul_zero] <;> ring
      _ ≤ ∑ A ∈ I.powerset, (Real.exp t - 1) ^ A.card *
          ∏ i ∈ A, inclusion q r e o i := by
        apply sum_le_sum
        intro A _
        exact mul_le_mul_of_nonneg_left (hjoint A) (pow_nonneg hx _)
      _ = ∏ i ∈ I, (1 + (Real.exp t - 1) * inclusion q r e o i) := by
        rw [prod_one_add]
        apply sum_congr rfl
        intro A _
        rw [prod_mul_distrib, prod_const]
  · simpa only [mul_sum] using
      Real.prod_one_add_le_exp_sum I
        (f := fun i => (Real.exp t - 1) * inclusion q r e o i)
        (fun i => mul_nonneg hx (hinclusion_nonneg i))

end
end D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportPosteriorMoment

#check @D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportPosteriorMoment.finite_support_posterior_moment
#print axioms D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportPosteriorMoment.finite_support_posterior_moment
