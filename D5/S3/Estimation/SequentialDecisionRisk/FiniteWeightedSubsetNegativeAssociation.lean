/- GID: D5/S3/Estimation/SequentialDecisionRisk/FiniteWeightedSubsetNegativeAssociation
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/FiniteWeightedSubsetNegativeAssociation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Whole-observable rank comparison for fixed positive product weights. -/

import Mathlib
import D5.S3.Analytic.RealRootedCoefficientNewton

open scoped BigOperators
open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.SequentialDecisionRisk.FiniteWeightedSubsetNegativeAssociation
noncomputable section

/-- Increasing real observables have increasing expectations on adjacent weighted
slices. The weights are fixed while the rank varies, and monotonicity is required
on the entire Boolean subcube. -/
theorem weighted_slice_rank_comparison {α : Type*}
    (U : Finset α) (w : α → ℝ) (hw : ∀ i ∈ U, 0 < w i)
    (f : Finset α → ℝ)
    (hf : ∀ S ⊆ U, ∀ T ⊆ U, S ⊆ T → f S ≤ f T)
    (k : ℕ) (hk : k < U.card) :
    (∑ S ∈ U.powersetCard k, (∏ i ∈ S, w i) * f S) /
        (∑ S ∈ U.powersetCard k, ∏ i ∈ S, w i) ≤
    (∑ S ∈ U.powersetCard (k + 1), (∏ i ∈ S, w i) * f S) /
        (∑ S ∈ U.powersetCard (k + 1), ∏ i ∈ S, w i) := by
  classical
  let Z : Finset α → ℕ → ℝ := fun V n => ∑ S ∈ V.powersetCard n, ∏ i ∈ S, w i
  let N : Finset α → ℕ → (Finset α → ℝ) → ℝ :=
    fun V n g => ∑ S ∈ V.powersetCard n, (∏ i ∈ S, w i) * g S
  have hpos (V : Finset α) (n : ℕ) (hV : ∀ i ∈ V, 0 < w i)
      (hn : n ≤ V.card) : 0 < Z V n := by
    exact sum_pos (fun S hS => prod_pos (fun i hi => hV i ((mem_powersetCard.mp hS).1 hi)))
      (powersetCard_nonempty.mpr hn)
  have hrec (V : Finset α) (i : α) (hi : i ∉ V) (n : ℕ) (g : Finset α → ℝ) :
      N (insert i V) (n+1) g = N V (n+1) g + w i * N V n (fun S => g (insert i S)) := by
    dsimp [N]
    rw [powersetCard_succ_insert hi, sum_union]
    · rw [mul_sum]
      congr 1
      rw [sum_image]
      · apply sum_congr rfl
        intro S hS
        rw [prod_insert (fun h => hi ((mem_powersetCard.mp hS).1 h))]
        ring
      · intro S hS T hT heq
        have hiS : i ∉ S := fun h => hi ((mem_powersetCard.mp hS).1 h)
        have hiT : i ∉ T := fun h => hi ((mem_powersetCard.mp hT).1 h)
        simpa [hiS, hiT] using congrArg (fun S : Finset α => S.erase i) heq
    · apply disjoint_left.mpr
      intro S hS hT
      obtain ⟨T, hT, rfl⟩ := mem_image.mp hT
      exact hi ((mem_powersetCard.mp hS).1 (mem_insert_self _ _))
  have hZrec (V : Finset α) (i : α) (hi : i ∉ V) (n : ℕ) :
      Z (insert i V) (n+1) = Z V (n+1) + w i * Z V n := by
    simpa [N, Z] using hrec V i hi n (fun _ => 1)
  have hNewton (V : Finset α) (n : ℕ) :
      Z V n * Z V (n+2) ≤ (Z V (n+1))^2 := by
    let m := V.val.map w
    have he (j : ℕ) : m.esymm j = Z V j := Finset.esymm_map_val w V j
    rw [← he, ← he, ← he]
    by_cases hn : n+2 ≤ m.card
    · have h := D5.S3.Analytic.RealRootedCoefficientNewton.esymm_mul_esymm_le_sq_esymm m n
      have hc : (n : ℝ)+2 ≤ m.card := by exact_mod_cast hn
      have hp : 0 < ((n : ℝ)+2)*((m.card : ℝ)-n) := mul_pos (by positivity) (by linarith)
      have hd : ((n : ℝ)+1)*((m.card : ℝ)-n-1) ≤ ((n : ℝ)+2)*((m.card : ℝ)-n) := by nlinarith
      exact (mul_le_mul_iff_right₀ hp).mp
        (h.trans (mul_le_mul_of_nonneg_right hd (sq_nonneg _)))
    · have hz : m.esymm (n+2) = 0 := by simp [Multiset.esymm, show m.card < n+2 by omega]
      rw [hz, mul_zero]
      exact sq_nonneg _
  change N U k f / Z U k ≤ N U (k+1) f / Z U (k+1)
  induction U using Finset.induction_on generalizing f k with
  | empty => simp at hk
  | @insert i V hi ih =>
    have hwi : 0 < w i := hw i (mem_insert_self _ _)
    have hV : ∀ j ∈ V, 0 < w j := fun j hj => hw j (mem_insert_of_mem hj)
    have hUpos (n : ℕ) (hn : n ≤ (insert i V).card) := hpos (insert i V) n hw hn
    by_cases hk0 : k = 0
    · subst k
      have hlow : f ∅ * Z (insert i V) 1 ≤ N (insert i V) 1 f := by
        dsimp [N, Z]
        rw [mul_sum]
        apply sum_le_sum
        intro S hS
        have hm := hf ∅ (empty_subset _) S (mem_powersetCard.mp hS).1 (empty_subset _)
        have hp : 0 ≤ ∏ j ∈ S, w j :=
          prod_nonneg (fun j hj => (hw j ((mem_powersetCard.mp hS).1 hj)).le)
        nlinarith
      simpa [N, Z] using (le_div_iff₀ (hUpos 1 (by omega))).mpr hlow
    · by_cases htop : k+1 = (insert i V).card
      · have hup : N (insert i V) k f ≤ f (insert i V) * Z (insert i V) k := by
          dsimp [N, Z]
          rw [mul_sum]
          apply sum_le_sum
          intro S hS
          have hm := hf S (mem_powersetCard.mp hS).1 (insert i V) (subset_refl _) (mem_powersetCard.mp hS).1
          have hp : 0 ≤ ∏ j ∈ S, w j :=
            prod_nonneg (fun j hj => (hw j ((mem_powersetCard.mp hS).1 hj)).le)
          nlinarith
        have hu := (div_le_iff₀ (hUpos k (by omega))).mpr hup
        have hp : (∏ l ∈ insert i V, w l) ≠ 0 :=
          ne_of_gt (prod_pos (fun l hl => hw l hl))
        simpa [htop, N, Z, hp] using hu
      · obtain ⟨j, rfl⟩ : ∃ j, k = j+1 := Nat.exists_eq_succ_of_ne_zero hk0
        have hj : j+2 ≤ V.card := by rw [card_insert_of_notMem hi] at hk htop; omega
        have h0 := hpos V j hV (by omega)
        have h1 := hpos V (j+1) hV (by omega)
        have h2 := hpos V (j+2) hV hj
        let g : Finset α → ℝ := fun S => f (insert i S)
        have hfm : ∀ S ⊆ V, ∀ T ⊆ V, S ⊆ T → f S ≤ f T := by
          intro S hS T hT hST
          exact hf S (hS.trans (subset_insert _ _)) T (hT.trans (subset_insert _ _)) hST
        have hgm : ∀ S ⊆ V, ∀ T ⊆ V, S ⊆ T → g S ≤ g T := by
          intro S hS T hT hST
          exact hf _ (insert_subset_insert i hS) _ (insert_subset_insert i hT) (insert_subset_insert i hST)
        have hfg : N V (j+1) f / Z V (j+1) ≤ N V (j+1) g / Z V (j+1) := by
          apply div_le_div_of_nonneg_right _ h1.le
          apply sum_le_sum
          intro S hS
          apply mul_le_mul_of_nonneg_left
          · exact hf S ((mem_powersetCard.mp hS).1.trans (subset_insert _ _))
              (insert i S) (insert_subset_insert i (mem_powersetCard.mp hS).1) (subset_insert _ _)
          · exact prod_nonneg (fun l hl => (hV l ((mem_powersetCard.mp hS).1 hl)).le)
        have hff := ih hV f hfm (j+1) (by omega)
        have hgg := ih hV g hgm j (by omega)
        let p : ℝ := w i * Z V j / (Z V (j+1) + w i * Z V j)
        let p' : ℝ := w i * Z V (j+1) / (Z V (j+2) + w i * Z V (j+1))
        have hd : 0 < Z V (j+1) + w i * Z V j := by positivity
        have hd' : 0 < Z V (j+2) + w i * Z V (j+1) := by positivity
        have hp : 0 ≤ p := div_nonneg (mul_nonneg hwi.le h0.le) hd.le
        have hp' : p' ≤ 1 := (div_le_one hd').mpr (by linarith)
        have hpp : p ≤ p' := by
          apply (div_le_div_iff₀ hd hd').mpr
          have hn := mul_le_mul_of_nonneg_left (hNewton V j) hwi.le
          nlinarith
        have heq : N (insert i V) (j+1) f / Z (insert i V) (j+1) =
            (1-p) * (N V (j+1) f / Z V (j+1)) + p * (N V j g / Z V j) := by
          rw [hrec V i hi j f, hZrec V i hi j]
          dsimp [p, g]
          field_simp
          <;> ring
        have heq' : N (insert i V) (j+1+1) f / Z (insert i V) (j+1+1) =
            (1-p') * (N V (j+2) f / Z V (j+2)) + p' * (N V (j+1) g / Z V (j+1)) := by
          rw [hrec V i hi (j+1) f, hZrec V i hi (j+1)]
          dsimp [p', g]
          field_simp
          <;> ring
        rw [heq, heq']
        have hA := mul_nonneg hp (sub_nonneg.mpr hgg)
        have hB := mul_nonneg (sub_nonneg.mpr hpp) (sub_nonneg.mpr hfg)
        have hC := mul_nonneg (sub_nonneg.mpr hp') (sub_nonneg.mpr hff)
        nlinarith

/-- Negative association for arbitrary increasing signed observables on disjoint
Boolean blocks, under one and the same fixed-weight slice law. -/
theorem weighted_slice_negative_association {α : Type*} [DecidableEq α]
    (U : Finset α) (w : α → ℝ) (hw : ∀ i ∈ U, 0 < w i)
    (q : ℕ) (hq : q ≤ U.card)
    (A B : Finset α) (hA : A ⊆ U) (hB : B ⊆ U) (hAB : Disjoint A B)
    (f g : Finset α → ℝ)
    (hf : ∀ S ⊆ A, ∀ T ⊆ A, S ⊆ T → f S ≤ f T)
    (hg : ∀ S ⊆ B, ∀ T ⊆ B, S ⊆ T → g S ≤ g T) :
    (∑ S ∈ U.powersetCard q, (∏ i ∈ S, w i) * (f (S ∩ A) * g (S ∩ B))) /
        (∑ S ∈ U.powersetCard q, ∏ i ∈ S, w i) ≤
    ((∑ S ∈ U.powersetCard q, (∏ i ∈ S, w i) * f (S ∩ A)) /
        (∑ S ∈ U.powersetCard q, ∏ i ∈ S, w i)) *
    ((∑ S ∈ U.powersetCard q, (∏ i ∈ S, w i) * g (S ∩ B)) /
        (∑ S ∈ U.powersetCard q, ∏ i ∈ S, w i)) := by
  classical
  let C := U \ A
  let Z : Finset α → ℕ → ℝ := fun V n => ∑ S ∈ V.powersetCard n, ∏ i ∈ S, w i
  let N : Finset α → ℕ → (Finset α → ℝ) → ℝ :=
    fun V n h => ∑ S ∈ V.powersetCard n, (∏ i ∈ S, w i) * h S
  let E := fun V n h => N V n h / Z V n
  have hC : C ⊆ U := sdiff_subset
  have hBC : B ⊆ C := by
    intro i hi
    exact mem_sdiff.mpr ⟨hB hi, fun ha => disjoint_left.mp hAB ha hi⟩
  have hAC : Disjoint A C := disjoint_sdiff_self_right
  have hpos (V : Finset α) (hV : V ⊆ U) (n : ℕ) (hn : n ≤ V.card) : 0 < Z V n := by
    exact sum_pos (fun S hS => prod_pos (fun i hi => hw i (hV ((mem_powersetCard.mp hS).1 hi))))
      (powersetCard_nonempty.mpr hn)
  have hfactor (V : Finset α) (hV : V ⊆ U) (n : ℕ) (h : Finset α → ℝ) :
      N V n h = Z V n * E V n h := by
    by_cases hn : n ≤ V.card
    · dsimp [E]
      field_simp [ne_of_gt (hpos V hV n hn)]
    · simp [N, Z, E, powersetCard_eq_empty.mpr (by omega : V.card < n)]
  have hrepr (a c : Finset α) (ha : a ⊆ A) (hc : c ⊆ C) :
      (a ∪ c) ∩ A = a ∧ (a ∪ c) \ A = c := by
    have hn : ∀ i ∈ c, i ∉ A := fun i hi => (mem_sdiff.mp (hc hi)).2
    constructor
    · ext i
      simp only [mem_inter, mem_union]
      have hai : i ∈ a → i ∈ A := fun h => ha h
      have hci : i ∈ c → i ∉ A := fun h => hn i h
      tauto
    · ext i
      simp only [mem_sdiff, mem_union]
      have hai : i ∈ a → i ∈ A := fun h => ha h
      have hci : i ∈ c → i ∉ A := fun h => hn i h
      tauto
  have hsplit (H : Finset α → ℝ) :
      (∑ S ∈ U.powersetCard q, H S) =
      ∑ k ∈ range (q+1), ∑ a ∈ A.powersetCard k,
        ∑ c ∈ C.powersetCard (q-k), H (a ∪ c) := by
    let R := (range (q+1)).sigma (fun k => (A.powersetCard k) ×ˢ (C.powersetCard (q-k)))
    have hR : (∑ p ∈ R, H (p.2.1 ∪ p.2.2)) =
        ∑ k ∈ range (q+1), ∑ a ∈ A.powersetCard k,
          ∑ c ∈ C.powersetCard (q-k), H (a ∪ c) := by
      simp only [R, sum_sigma, sum_product]
    rw [← hR]
    symm
    apply sum_bij (fun p _ => p.2.1 ∪ p.2.2)
    · intro p hp
      obtain ⟨hk, ha, hc⟩ := by simpa only [R, mem_sigma, mem_product] using hp
      obtain ⟨haA, hak⟩ := mem_powersetCard.mp ha
      obtain ⟨hcC, hck⟩ := mem_powersetCard.mp hc
      have hd : Disjoint p.2.1 p.2.2 := hAC.mono haA hcC
      refine mem_powersetCard.mpr ⟨union_subset (haA.trans hA) (hcC.trans hC), ?_⟩
      rw [card_union_of_disjoint hd, hak, hck]
      have := mem_range.mp hk
      omega
    · intro p hp t ht he
      obtain ⟨hpk, hpa, hpc⟩ := by simpa only [R, mem_sigma, mem_product] using hp
      obtain ⟨htk, hta, htc⟩ := by simpa only [R, mem_sigma, mem_product] using ht
      have hpR := hrepr p.2.1 p.2.2 (mem_powersetCard.mp hpa).1 (mem_powersetCard.mp hpc).1
      have htR := hrepr t.2.1 t.2.2 (mem_powersetCard.mp hta).1 (mem_powersetCard.mp htc).1
      have ha : p.2.1 = t.2.1 := by rw [← hpR.1, ← htR.1, he]
      have hc : p.2.2 = t.2.2 := by rw [← hpR.2, ← htR.2, he]
      have hk : p.1 = t.1 := by
        rw [← (mem_powersetCard.mp hpa).2, ← (mem_powersetCard.mp hta).2, ha]
      exact Sigma.ext hk (heq_of_eq (Prod.ext ha hc))
    · intro S hS
      obtain ⟨hSU, hSq⟩ := mem_powersetCard.mp hS
      refine ⟨⟨(S ∩ A).card, S ∩ A, S \ A⟩, ?_, ?_⟩
      · simp only [R, mem_sigma, mem_product]
        refine ⟨mem_range.mpr ?_, mem_powersetCard.mpr ⟨inter_subset_right, rfl⟩,
          mem_powersetCard.mpr ⟨sdiff_subset_sdiff_left A hSU, ?_⟩⟩
        · have := card_le_card (inter_subset_left (s₁ := S) (s₂ := A)); omega
        · have := card_sdiff_add_card_inter S A; omega
      · ext i; simp only [mem_union, mem_inter, mem_sdiff]; tauto
    · intros; rfl
  let gC : Finset α → ℝ := fun S => g (S ∩ B)
  have hgC : ∀ S ⊆ C, ∀ T ⊆ C, S ⊆ T → gC S ≤ gC T := by
    intro S _ T _ hST
    exact hg _ inter_subset_right _ inter_subset_right (inter_subset_inter hST (subset_refl B))
  let F : ℕ → ℝ := fun k => E A k f
  let G : ℕ → ℝ := fun k => E C (q-k) gC
  let P : ℕ → ℝ := fun k => Z A k * Z C (q-k)
  let K := (range (q+1)).filter (fun k => k ≤ A.card ∧ q-k ≤ C.card)
  have hK (k : ℕ) : k ∈ K ↔ k ≤ q ∧ k ≤ A.card ∧ q-k ≤ C.card := by
    simp only [K, mem_filter, mem_range]; omega
  have hmono (V : Finset α) (hV : V ⊆ U) (h : Finset α → ℝ)
      (hm : ∀ S ⊆ V, ∀ T ⊆ V, S ⊆ T → h S ≤ h T)
      (k l : ℕ) (hkl : k ≤ l) (hl : l ≤ V.card) : E V k h ≤ E V l h := by
    induction l, hkl using Nat.le_induction with
    | base => exact le_rfl
    | succ l hkl ih =>
      exact (ih (by omega)).trans
        (weighted_slice_rank_comparison V w (fun i hi => hw i (hV hi)) h hm l (by omega))
  have hFG (k l : ℕ) (hk : k ∈ K) (hl : l ∈ K) :
      (F k - F l) * (G k - G l) ≤ 0 := by
    obtain ⟨hkq, hkA, hkC⟩ := (hK k).mp hk
    obtain ⟨hlq, hlA, hlC⟩ := (hK l).mp hl
    rcases le_total k l with hkl | hlk
    · have hF := hmono A hA f hf k l hkl hlA
      have hG := hmono C hC gC hgC (q-l) (q-k) (by omega) hkC
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hF) (sub_nonneg.mpr hG)
    · have hF := hmono A hA f hf l k hlk hkA
      have hG := hmono C hC gC hgC (q-k) (q-l) (by omega) hlC
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hF) (sub_nonpos.mpr hG)
  have hPn (k : ℕ) : 0 ≤ P k := by
    apply mul_nonneg <;> apply sum_nonneg <;> intro S hS <;> apply prod_nonneg
    · intro i hi; exact (hw i (hA ((mem_powersetCard.mp hS).1 hi))).le
    · intro i hi; exact (hw i (hC ((mem_powersetCard.mp hS).1 hi))).le
  have hdecomp (fa gb : Finset α → ℝ) :
      N U q (fun S => fa (S ∩ A) * gb (S \ A)) =
        ∑ k ∈ range (q+1), N A k fa * N C (q-k) gb := by
    rw [show N U q (fun S => fa (S ∩ A) * gb (S \ A)) =
      ∑ S ∈ U.powersetCard q, (∏ i ∈ S, w i) * (fa (S ∩ A) * gb (S \ A)) from rfl, hsplit]
    apply sum_congr rfl
    intro k hk
    dsimp [N]
    rw [sum_mul_sum]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro c hc
    have haA := (mem_powersetCard.mp ha).1
    have hcC := (mem_powersetCard.mp hc).1
    rw [(hrepr a c haA hcC).1, (hrepr a c haA hcC).2,
      prod_union (hAC.mono haA hcC)]
    ring
  have hrestrict (H : ℕ → ℝ) :
      (∑ k ∈ range (q+1), P k * H k) = ∑ k ∈ K, P k * H k := by
    symm
    apply sum_subset (filter_subset _ _)
    intro k hk hn
    have hh : ¬ (k ≤ A.card ∧ q-k ≤ C.card) := by simpa only [K, mem_filter, hk, true_and] using hn
    rcases not_and_or.mp hh with ha | hc
    · simp [P, Z, powersetCard_eq_empty.mpr (by omega : A.card < k)]
    · simp [P, Z, powersetCard_eq_empty.mpr (by omega : C.card < q-k)]
  have hsumZ : Z U q = ∑ k ∈ K, P k := by
    have hd := hdecomp (fun _ => 1) (fun _ => 1)
    have hd' : Z U q = ∑ k ∈ range (q+1), P k := by simpa [N, Z, P] using hd
    exact hd'.trans (by simpa using hrestrict (fun _ => 1))
  have hsumF : N U q (fun S => f (S ∩ A)) = ∑ k ∈ K, P k * F k := by
    have hd := hdecomp f (fun _ => 1)
    simp only [mul_one] at hd
    rw [hd]
    have he : (∑ k ∈ range (q+1), N A k f * N C (q-k) (fun _ => 1)) =
        ∑ k ∈ range (q+1), P k * F k := by
      apply sum_congr rfl
      intro k _
      rw [hfactor A hA k f]
      simp only [N, mul_one]
      dsimp [P, F, Z]
      ring
    exact he.trans (hrestrict F)
  have hdiffB (S : Finset α) : (S \ A) ∩ B = S ∩ B := by
    ext i
    simp only [mem_inter, mem_sdiff]
    have hn : i ∈ B → i ∉ A := fun hb ha => disjoint_left.mp hAB ha hb
    tauto
  have hsumG : N U q (fun S => g (S ∩ B)) = ∑ k ∈ K, P k * G k := by
    have hd := hdecomp (fun _ => 1) gC
    simp only [one_mul, gC, hdiffB] at hd
    rw [hd]
    have he : (∑ k ∈ range (q+1), N A k (fun _ => 1) * N C (q-k) gC) =
        ∑ k ∈ range (q+1), P k * G k := by
      apply sum_congr rfl
      intro k _
      rw [hfactor C hC (q-k) gC]
      simp only [N, mul_one]
      dsimp [P, G, Z]
      ring
    exact he.trans (hrestrict G)
  have hsumFG : N U q (fun S => f (S ∩ A) * g (S ∩ B)) =
      ∑ k ∈ K, P k * (F k * G k) := by
    have hd := hdecomp f gC
    simp only [gC, hdiffB] at hd
    rw [hd]
    have he : (∑ k ∈ range (q+1), N A k f * N C (q-k) gC) =
        ∑ k ∈ range (q+1), P k * (F k * G k) := by
      apply sum_congr rfl
      intro k _
      rw [hfactor A hA k f, hfactor C hC (q-k) gC]
      dsimp [P, F, G]
      ring
    exact he.trans (hrestrict (fun k => F k * G k))
  have hcov : (∑ k ∈ K, P k * (F k * G k)) * (∑ k ∈ K, P k) ≤
      (∑ k ∈ K, P k * F k) * (∑ k ∈ K, P k * G k) := by
    have hpairs : (∑ k ∈ K, ∑ l ∈ K,
        P k * P l * ((F k - F l) * (G k - G l))) ≤ 0 := by
      apply sum_nonpos
      intro k hk
      apply sum_nonpos
      intro l hl
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hPn k) (hPn l)) (hFG k l hk hl)
    have heq : (∑ k ∈ K, ∑ l ∈ K,
        P k * P l * ((F k - F l) * (G k - G l))) =
        2 * ((∑ k ∈ K, P k * (F k * G k)) * (∑ k ∈ K, P k) -
          (∑ k ∈ K, P k * F k) * (∑ k ∈ K, P k * G k)) := by
      simp_rw [sub_mul, mul_sub, sum_sub_distrib]
      have ht (a b : ℕ → ℝ) :
          (∑ k ∈ K, ∑ l ∈ K, P k * P l * (a k * b l)) =
          (∑ k ∈ K, P k * a k) * (∑ l ∈ K, P l * b l) := by
        rw [sum_mul_sum]
        apply sum_congr rfl
        intro k _
        apply sum_congr rfl
        intro l _
        ring
      have ht' (a : ℕ → ℝ) :
          (∑ k ∈ K, ∑ l ∈ K, P k * P l * a k) =
          (∑ k ∈ K, P k * a k) * (∑ l ∈ K, P l) := by
        simpa only [mul_one] using ht a (fun _ => 1)
      have ht'' (a : ℕ → ℝ) :
          (∑ k ∈ K, ∑ l ∈ K, P k * P l * a l) =
          (∑ k ∈ K, P k) * (∑ l ∈ K, P l * a l) := by
        simpa only [one_mul, mul_one] using ht (fun _ => 1) a
      rw [ht' (fun k => F k * G k), ht F G, ht'' (fun k => F k * G k)]
      have htGF : (∑ k ∈ K, ∑ l ∈ K, P k * P l * (F l * G k)) =
          (∑ k ∈ K, P k * G k) * (∑ l ∈ K, P l * F l) := by
        calc
          _ = ∑ k ∈ K, ∑ l ∈ K, P k * P l * (G k * F l) := by
            apply sum_congr rfl
            intro k _
            apply sum_congr rfl
            intro l _
            ring
          _ = _ := ht G F
      rw [htGF]
      ring
    rw [heq] at hpairs
    linarith
  change N U q (fun S => f (S ∩ A) * g (S ∩ B)) / Z U q ≤
    (N U q (fun S => f (S ∩ A)) / Z U q) * (N U q (fun S => g (S ∩ B)) / Z U q)
  have hz := hpos U (subset_refl _) q hq
  rw [hsumFG, hsumF, hsumG, hsumZ]
  have hz' : 0 < ∑ k ∈ K, P k := by rwa [← hsumZ]
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ hz' (mul_pos hz' hz')).mpr
  nlinarith [mul_le_mul_of_nonneg_right hcov hz'.le]

end
end D5.S3.Estimation.SequentialDecisionRisk.FiniteWeightedSubsetNegativeAssociation

open D5.S3.Estimation.SequentialDecisionRisk.FiniteWeightedSubsetNegativeAssociation in
#print axioms weighted_slice_rank_comparison

open D5.S3.Estimation.SequentialDecisionRisk.FiniteWeightedSubsetNegativeAssociation in
#print axioms weighted_slice_negative_association
