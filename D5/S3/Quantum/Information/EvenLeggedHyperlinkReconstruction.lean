/- GID: D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Universal rational leg factors reconstruct complement-symmetric set functions. -/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
The hyperlink transform is Eq. (5) of Santalla, Singha Roy, Sierra and
Rodríguez-Laguna, *The hyperlink representation of entanglement and the
inclusion-exclusion principle*, arXiv:2601.17926v2, Appendix B.

The reconstruction concerns every real complement-symmetric set function
vanishing at the empty set. Subsystem entropies of finite-dimensional pure
states satisfy these hypotheses by equality of the complementary nonzero
spectra and zero entropy of the empty subsystem. The identification with
the repository's density-state and von Neumann entropy definitions is not
formalized here.
-/

open scoped BigOperators

namespace D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction

noncomputable section

variable {α : Type*} [DecidableEq α]

/-- The inclusion-exclusion hyperlink coefficient. -/
def hyperlink (S : Finset α → ℝ) (I : Finset α) : ℝ :=
  ∑ B ∈ I.powerset, (-1 : ℝ) ^ (I.card - B.card) * S B

/-- Rational coefficients of the inverse triangular system on even ranks. -/
def legInverseCoeff : ℕ → ℚ :=
  Nat.strongRec (fun r prev =>
    if r = 0 then 1
    else if Even r then
      -(1 / 2 : ℚ) * ∑ j : Fin r,
        if Even j.val then (r.choose j.val : ℚ) * prev j.val j.isLt else 0
    else 0)

/-- Universal leg factors, with zero totalization outside the leg range. -/
def legFactor (m p : ℕ) : ℚ :=
  if p ≤ m then
    -(1 / 2 : ℚ) *
      ∑ k ∈ (Finset.range (m + 1)).filter (fun k => 2 ≤ k ∧ Even k),
        legInverseCoeff (m - k) *
          ((m.choose k : ℚ) - (p.choose k : ℚ) - ((m - p).choose k : ℚ))
  else 0

/-- One rational coefficient family works for every finite ambient system. -/
def claim : Prop :=
  ∃ L : ℕ → ℕ → ℚ,
    (∀ m, L m 0 = 0 ∧ L m m = 0) ∧
    (∀ m p, L m p = L m (m - p)) ∧
    ∀ (N : ℕ) (S : Finset (Fin N) → ℝ),
      S ∅ = 0 → (∀ A, S Aᶜ = S A) → ∀ A,
        S A =
          ∑ I ∈ (Finset.univ : Finset (Fin N)).powerset.filter
              (fun I => Even I.card ∧ I ≠ ∅),
            (L I.card (I ∩ A).card : ℝ) * hyperlink S I

private theorem legInverseCoeff_eq (r : ℕ) :
    legInverseCoeff r =
      if r = 0 then 1
      else if Even r then
        -(1 / 2 : ℚ) *
          ∑ j ∈ (Finset.range r).filter (fun j => Even j),
            (r.choose j : ℚ) * legInverseCoeff j
      else 0 := by
  rw [legInverseCoeff, Nat.strongRec_eq]
  change (if r = 0 then 1 else if Even r then
    -(1 / 2 : ℚ) * ∑ j : Fin r,
      if Even j.val then (r.choose j.val : ℚ) * legInverseCoeff j.val else 0
    else 0) = _
  by_cases hz : r = 0
  · rw [if_pos hz, if_pos hz]
  · rw [if_neg hz, if_neg hz]
    by_cases he : Even r
    · rw [if_pos he, if_pos he]
      congr 1
      rw [Finset.sum_filter]
      exact Fin.sum_univ_eq_sum_range
        (fun j => if Even j then (r.choose j : ℚ) * legInverseCoeff j else 0) r
    · rw [if_neg he, if_neg he]

private theorem legInverseCoeff_convolution (r : ℕ) (hr : Even r) :
    legInverseCoeff r +
        (1 / 2 : ℚ) *
          ∑ j ∈ (Finset.range r).filter (fun j => Even j),
            (r.choose j : ℚ) * legInverseCoeff j =
      if r = 0 then 1 else 0 := by
  rw [legInverseCoeff_eq]
  by_cases h : r = 0
  · subst r
    simp only [ite_true, Finset.range_zero, Finset.filter_empty, Finset.sum_empty,
      mul_zero, add_zero]
  · rw [if_neg h, if_pos hr, if_neg h]
    ring

private theorem alternating_powerset (A : Finset α) :
    (∑ B ∈ A.powerset, (-1 : ℝ) ^ B.card) = if A = ∅ then 1 else 0 := by
  exact_mod_cast (Finset.sum_powerset_neg_one_pow_card (x := A))

private theorem powerset_interval_sum (A B : Finset α) (hBA : B ⊆ A)
    (f : Finset α → ℝ) :
    (∑ I ∈ A.powerset.filter (fun I => B ⊆ I), f I) =
      ∑ D ∈ (A \ B).powerset, f (B ∪ D) := by
  rw [← Finset.Icc_eq_filter_powerset, Finset.Icc_eq_image_powerset hBA,
    Finset.sum_image]
  intro D hD E hE h
  exact Finset.disjoint_injOn_union_left B
    (disjoint_sdiff_self_right.mono_right (Finset.mem_powerset.mp hD))
    (disjoint_sdiff_self_right.mono_right (Finset.mem_powerset.mp hE))
    (by simpa only [Finset.union_comm] using h)

private theorem alternating_interval (A B : Finset α) (hBA : B ⊆ A) :
    (∑ I ∈ A.powerset.filter (fun I => B ⊆ I),
      (-1 : ℝ) ^ (I.card - B.card)) = if A = B then 1 else 0 := by
  rw [powerset_interval_sum A B hBA]
  have hc : ∀ D ∈ (A \ B).powerset, (B ∪ D).card - B.card = D.card := by
    intro D hD
    rw [Finset.card_union_of_disjoint
      (disjoint_sdiff_self_right.mono_right (Finset.mem_powerset.mp hD))]
    omega
  rw [Finset.sum_congr rfl (fun D hD => congrArg ((-1 : ℝ) ^ ·) (hc D hD))]
  rw [alternating_powerset]
  have he : A \ B = ∅ ↔ A = B := by
    rw [Finset.sdiff_eq_empty_iff_subset]
    exact ⟨fun h => Finset.Subset.antisymm h hBA, fun h => h ▸ Finset.Subset.refl B⟩
  simp only [he]

private theorem sign_sub (n m : ℕ) (h : m ≤ n) :
    (-1 : ℝ) ^ (n - m) = (-1 : ℝ) ^ n * (-1 : ℝ) ^ m := by
  have hs : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← pow_add, ← two_mul]
    exact (even_two_mul m).neg_one_pow
  calc
    _ = (-1 : ℝ) ^ (n - m) * ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) := by rw [hs, mul_one]
    _ = _ := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel h]

omit [DecidableEq α] in
theorem zeta_hyperlink (S : Finset α → ℝ) (A : Finset α) :
    (∑ I ∈ A.powerset, hyperlink S I) = S A := by
  classical
  simp only [hyperlink]
  rw [Finset.sum_comm' (t' := A.powerset)
    (s' := fun B => A.powerset.filter (fun I => B ⊆ I))]
  · simp_rw [← Finset.sum_mul]
    have h : ∀ B ∈ A.powerset,
        (∑ I ∈ A.powerset.filter (fun I => B ⊆ I),
          (-1 : ℝ) ^ (I.card - B.card)) = if A = B then 1 else 0 :=
      fun B hB => alternating_interval A B (Finset.mem_powerset.mp hB)
    rw [Finset.sum_congr rfl (fun B hB => congrArg (· * S B) (h B hB))]
    simp only [ite_mul, one_mul, zero_mul]
    simp
  · intro I B
    simp only [Finset.mem_powerset, Finset.mem_filter]
    exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2.trans h.1⟩, fun h => ⟨h.1.1, h.1.2⟩⟩

omit [DecidableEq α] in
private theorem hyperlink_zeta (v : Finset α → ℝ) (I : Finset α) :
    hyperlink (fun A => ∑ K ∈ A.powerset, v K) I = v I := by
  classical
  simp only [hyperlink, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := I.powerset)
    (s' := fun K => I.powerset.filter (fun B => K ⊆ B))]
  · simp_rw [← Finset.sum_mul]
    have h : ∀ K ∈ I.powerset,
        (∑ B ∈ I.powerset.filter (fun B => K ⊆ B),
          (-1 : ℝ) ^ (I.card - B.card)) = if I = K then 1 else 0 := by
      intro K hK
      rw [powerset_interval_sum I K (Finset.mem_powerset.mp hK)]
      have he : ∀ D ∈ (I \ K).powerset,
          I.card - (K ∪ D).card = (I \ K).card - D.card := by
        intro D hD
        rw [Finset.card_union_of_disjoint
          (disjoint_sdiff_self_right.mono_right (Finset.mem_powerset.mp hD)),
          Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hK)]
        omega
      rw [Finset.sum_congr rfl (fun D hD => congrArg ((-1 : ℝ) ^ ·) (he D hD))]
      have hb := Finset.sum_pow_mul_eq_add_pow (1 : ℝ) (-1) (I \ K)
      simp only [one_pow, one_mul, add_neg_cancel] at hb
      rw [hb]
      by_cases hk : I = K
      · subst K
        simp
      · have hn : (I \ K).card ≠ 0 := by
          intro hz
          have h := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hz)
          exact hk (Finset.Subset.antisymm h (Finset.mem_powerset.mp hK))
        simp only [zero_pow hn, if_neg hk]
    rw [Finset.sum_congr rfl (fun K hK => congrArg (· * v K) (h K hK))]
    simp only [ite_mul, one_mul, zero_mul]
    simp
  · intro B K
    simp only [Finset.mem_powerset, Finset.mem_filter]
    exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2.trans h.1⟩, fun h => ⟨h.1.1, h.1.2⟩⟩

variable [Fintype α]

private theorem hyperlink_compl (S : Finset α → ℝ) (I : Finset α) :
    hyperlink (fun A => S Aᶜ) I =
      (-1 : ℝ) ^ I.card *
        ∑ K ∈ (Finset.univ : Finset α).powerset.filter (fun K => I ⊆ K),
          hyperlink S K := by
  rw [hyperlink]
  simp_rw [← zeta_hyperlink S, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := (Finset.univ : Finset α).powerset)
    (s' := fun K => (I \ K).powerset)]
  · have h : ∀ K ∈ (Finset.univ : Finset α).powerset,
        (∑ B ∈ (I \ K).powerset, (-1 : ℝ) ^ (I.card - B.card)) =
          if I ⊆ K then (-1 : ℝ) ^ I.card else 0 := by
      intro K _
      calc
        _ = (-1 : ℝ) ^ I.card * ∑ B ∈ (I \ K).powerset, (-1 : ℝ) ^ B.card := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun B hB =>
            sign_sub I.card B.card
              (Finset.card_le_card ((Finset.mem_powerset.mp hB).trans Finset.sdiff_subset)))
        _ = _ := by
          rw [alternating_powerset]
          simp only [Finset.sdiff_eq_empty_iff_subset, mul_ite, mul_one, mul_zero]
    simp_rw [← Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun K hK => congrArg (· * hyperlink S K) (h K hK))]
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
  · intro B K
    simp only [Finset.mem_powerset, Finset.subset_univ, and_true,
      Finset.subset_sdiff, Finset.subset_compl_iff_disjoint_left]

omit [DecidableEq α] [Fintype α] in
private theorem hyperlink_weighted_sum {β : Type*} (t : Finset β)
    (a : β → ℝ) (F : β → Finset α → ℝ) (I : Finset α) :
    hyperlink (fun A => ∑ b ∈ t, a b * F b A) I =
      ∑ b ∈ t, a b * hyperlink (F b) I := by
  simp only [hyperlink, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  exact Finset.sum_congr rfl (fun B _ => mul_left_comm _ _ _)

private theorem even_hyperlink_ext (S T : Finset α → ℝ)
    (hzero : S ∅ = T ∅) (hS : ∀ A, S Aᶜ = S A) (hT : ∀ A, T Aᶜ = T A)
    (heven : ∀ I, Even I.card → I ≠ ∅ → hyperlink S I = hyperlink T I) :
    S = T := by
  have hc : ∀ n I, Fintype.card α - I.card = n → hyperlink S I = hyperlink T I := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro I hn
      by_cases hz : I = ∅
      · subst I
        simpa only [hyperlink, Finset.powerset_empty, Finset.sum_singleton,
          Finset.card_empty, Nat.sub_self, pow_zero, one_mul] using hzero
      by_cases he : Even I.card
      · exact heven I he hz
      have hsign : (-1 : ℝ) ^ I.card = -1 := (Nat.not_even_iff_odd.mp he).neg_one_pow
      have hs := hyperlink_compl S I
      have ht := hyperlink_compl T I
      rw [funext hS, hsign] at hs
      rw [funext hT, hsign] at ht
      let t := (Finset.univ : Finset α).powerset.filter (fun K => I ⊆ K)
      have hi : I ∈ t := Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.subset_univ I), Finset.Subset.refl I⟩
      have hrest : (∑ K ∈ t.erase I, hyperlink S K) =
          ∑ K ∈ t.erase I, hyperlink T K := by
        refine Finset.sum_congr rfl (fun K hK => ?_)
        have hk := Finset.mem_erase.mp hK
        have hIK := (Finset.mem_filter.mp hk.2).2
        have hlt : I.card < K.card := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨hIK, Ne.symm hk.1⟩)
        have hbound := K.card_le_univ
        have hm : Fintype.card α - K.card < n := by omega
        exact ih (Fintype.card α - K.card) hm K rfl
      change hyperlink S I = -1 * ∑ K ∈ t, hyperlink S K at hs
      change hyperlink T I = -1 * ∑ K ∈ t, hyperlink T K at ht
      rw [← Finset.sum_erase_add t (hyperlink S) hi, hrest] at hs
      rw [← Finset.sum_erase_add t (hyperlink T) hi] at ht
      linarith
  funext A
  rw [← zeta_hyperlink S A, ← zeta_hyperlink T A]
  exact Finset.sum_congr rfl (fun I _ => hc (Fintype.card α - I.card) I rfl)

private def q (K A : Finset α) : ℝ :=
  ((if K ⊆ A then (1 : ℝ) else 0) + (if K ⊆ Aᶜ then 1 else 0) - 1) / 2

private theorem q_laws (K : Finset α) (hK : K ≠ ∅) :
    q K ∅ = 0 ∧ ∀ A, q K Aᶜ = q K A := by
  constructor
  · rw [q, if_neg (fun h => hK (Finset.subset_empty.mp h))]
    simp only [Finset.compl_empty, Finset.subset_univ, ite_true]
    norm_num
  · intro A
    rw [q, q, compl_compl, add_comm]

omit [Fintype α] in
private theorem hyperlink_monomial (I K : Finset α) :
    hyperlink (fun A => if K ⊆ A then (1 : ℝ) else 0) I =
      if I = K then 1 else 0 := by
  have hf : (fun A => if K ⊆ A then (1 : ℝ) else 0) =
      (fun A => ∑ L ∈ A.powerset, if L = K then (1 : ℝ) else 0) := by
    funext A
    simp only [Finset.sum_ite_eq', Finset.mem_powerset]
  rw [hf, hyperlink_zeta]

private theorem hyperlink_q_even (I K : Finset α) (hI : Even I.card) (hI0 : I ≠ ∅) :
    hyperlink (q K) I = if I = K then 1 else if I ⊆ K then 1 / 2 else 0 := by
  have hlin : hyperlink (q K) I =
      (hyperlink (fun A => if K ⊆ A then (1 : ℝ) else 0) I +
       hyperlink (fun A => if K ⊆ Aᶜ then (1 : ℝ) else 0) I -
       hyperlink (fun _ => (1 : ℝ)) I) / 2 := by
    change (∑ B ∈ I.powerset, (-1 : ℝ) ^ (I.card - B.card) *
      (((if K ⊆ B then (1 : ℝ) else 0) + (if K ⊆ Bᶜ then 1 else 0) - 1) / 2)) = _
    simp only [hyperlink, div_eq_mul_inv, ← mul_assoc, mul_sub, mul_add]
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hc : hyperlink (fun _ : Finset α => (1 : ℝ)) I = 0 := by
    have hm := hyperlink_monomial I (∅ : Finset α)
    simp only [Finset.empty_subset, ite_true, if_neg hI0] at hm
    exact hm
  rw [hlin, hc, hyperlink_monomial,
    hyperlink_compl (fun A => if K ⊆ A then (1 : ℝ) else 0), hI.neg_one_pow, one_mul]
  simp only [hyperlink_monomial, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_powerset, Finset.subset_univ, true_and]
  by_cases he : I = K
  · subst K
    simp only [ite_true, Finset.Subset.refl, sub_zero]
    norm_num
  · simp only [if_neg he]
    by_cases hs : I ⊆ K <;> simp only [hs, ite_true, ite_false] <;> norm_num

omit [Fintype α] in
private theorem interval_c_inverse (I K : Finset α) (hIK : I ⊆ K)
    (hI : Even I.card) (hK : Even K.card) :
    (∑ L ∈ K.powerset.filter (fun L => I ⊆ L ∧ Even L.card),
      (if L = I then (1 : ℚ) else 1 / 2) * legInverseCoeff (K.card - L.card)) =
      if I = K then 1 else 0 := by
  let T := K \ I
  let r := T.card
  have hr : Even r := by
    dsimp only [r, T]
    rw [Finset.card_sdiff_of_subset hIK, Nat.even_sub (Finset.card_le_card hIK)]
    exact ⟨fun _ => hI, fun _ => hK⟩
  have hbij : (∑ L ∈ K.powerset.filter (fun L => I ⊆ L ∧ Even L.card),
      (if L = I then (1 : ℚ) else 1 / 2) * legInverseCoeff (K.card - L.card)) =
      ∑ D ∈ T.powerset.filter (fun D => Even D.card),
        (if D.card = r then (1 : ℚ) else 1 / 2) * legInverseCoeff D.card := by
    refine Finset.sum_bij (fun L _ => K \ L) ?_ ?_ ?_ ?_
    · intro L hL
      obtain ⟨hLK, hIL, he⟩ := Finset.mem_filter.mp hL
      have hLK := Finset.mem_powerset.mp hLK
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · exact Finset.sdiff_subset_sdiff (Finset.Subset.refl K) hIL
      · rw [Finset.card_sdiff_of_subset hLK, Nat.even_sub (Finset.card_le_card hLK)]
        exact ⟨fun _ => he, fun _ => hK⟩
    · intro L hL M hM he
      have hl := Finset.mem_powerset.mp (Finset.mem_filter.mp hL).1
      have hm := Finset.mem_powerset.mp (Finset.mem_filter.mp hM).1
      have hc := congrArg (fun D => K \ D) he
      rwa [Finset.sdiff_sdiff_eq_self hl, Finset.sdiff_sdiff_eq_self hm] at hc
    · intro D hD
      obtain ⟨hDT, he⟩ := Finset.mem_filter.mp hD
      have hDT := Finset.mem_powerset.mp hDT
      have hDK : D ⊆ K := hDT.trans Finset.sdiff_subset
      refine ⟨K \ D, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        Finset.sdiff_subset, ?_, ?_⟩, Finset.sdiff_sdiff_eq_self hDK⟩
      · exact Finset.subset_sdiff.mpr ⟨hIK,
          (disjoint_sdiff_self_left.mono_left hDT).symm⟩
      · rw [Finset.card_sdiff_of_subset hDK, Nat.even_sub (Finset.card_le_card hDK)]
        exact ⟨fun _ => he, fun _ => hK⟩
    · intro L hL
      obtain ⟨hLK, hIL, _⟩ := Finset.mem_filter.mp hL
      have hLK := Finset.mem_powerset.mp hLK
      rw [Finset.card_sdiff_of_subset hLK]
      have he : L = I ↔ K.card - L.card = r := by
        dsimp only [r, T]
        rw [Finset.card_sdiff_of_subset hIK]
        constructor
        · intro h; rw [h]
        · intro h
          exact (Finset.eq_of_subset_of_card_le hIL (by
            have := Finset.card_le_card hLK
            have := Finset.card_le_card hIK
            omega)).symm
      simp only [he]
  rw [hbij, Finset.sum_filter]
  rw [Finset.sum_powerset_apply_card (fun j => if Even j then
    (if j = r then (1 : ℚ) else 1 / 2) * legInverseCoeff j else 0)]
  change (∑ j ∈ Finset.range (r + 1),
    r.choose j • (if Even j then
      (if j = r then (1 : ℚ) else 1 / 2) * legInverseCoeff j else 0)) = _
  rw [Finset.sum_range_succ]
  simp only [Nat.choose_self, hr, ite_true, one_mul, one_nsmul]
  have hs : (∑ j ∈ Finset.range r, r.choose j •
      (if Even j then (if j = r then (1 : ℚ) else 1 / 2) * legInverseCoeff j else 0)) =
      (1 / 2 : ℚ) * ∑ j ∈ (Finset.range r).filter (fun j => Even j),
        (r.choose j : ℚ) * legInverseCoeff j := by
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjr : j ≠ r := Nat.ne_of_lt (Finset.mem_range.mp hj)
    by_cases he : Even j <;> simp only [he, ite_true, ite_false, if_neg hjr,
      nsmul_eq_mul, mul_zero]
    ring
  rw [hs, add_comm, legInverseCoeff_convolution r hr]
  have hz : r = 0 ↔ I = K := by
    dsimp only [r, T]
    rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]
    exact ⟨fun h => Finset.Subset.antisymm hIK h, fun h => h ▸ Finset.Subset.refl K⟩
  simp only [hz]

private def h (S : Finset α → ℝ) (I : Finset α) : ℝ :=
  ∑ K ∈ (Finset.univ : Finset α).powerset.filter (fun K => Even K.card ∧ I ⊆ K),
    (legInverseCoeff (K.card - I.card) : ℝ) * hyperlink S K

private def synth (S : Finset α → ℝ) (A : Finset α) : ℝ :=
  ∑ K ∈ (Finset.univ : Finset α).powerset.filter (fun K => Even K.card ∧ K ≠ ∅),
    h S K * q K A

private theorem synth_even_hyperlink (S : Finset α → ℝ) (I : Finset α)
    (hI : Even I.card) (hI0 : I ≠ ∅) : hyperlink (synth S) I = hyperlink S I := by
  change hyperlink (fun A => ∑ K ∈ (Finset.univ : Finset α).powerset.filter
    (fun K => Even K.card ∧ K ≠ ∅), h S K * q K A) I = _
  rw [hyperlink_weighted_sum]
  rw [Finset.sum_congr rfl (fun K _ =>
    congrArg (h S K * ·) (hyperlink_q_even I K hI hI0))]
  have hf : (∑ K ∈ (Finset.univ : Finset α).powerset.filter
      (fun K => Even K.card ∧ K ≠ ∅),
      h S K * (if I = K then 1 else if I ⊆ K then 1 / 2 else 0)) =
      ∑ K ∈ (Finset.univ : Finset α).powerset.filter
        (fun K => Even K.card ∧ I ⊆ K),
        (if K = I then (1 : ℝ) else 1 / 2) * h S K := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun K _ => ?_)
    by_cases he : Even K.card
    · by_cases hs : I ⊆ K
      · have hn : K ≠ ∅ := fun hz => hI0 (Finset.subset_empty.mp (hz ▸ hs))
        conv_lhs => rw [if_pos (And.intro he hn)]
        conv_rhs => rw [if_pos (And.intro he hs)]
        by_cases hi : I = K
        · subst K
          rw [if_pos rfl, if_pos rfl, mul_one, one_mul]
        · rw [if_neg hi, if_pos hs, if_neg (Ne.symm hi), mul_comm]
      · have hn : I ≠ K := fun hi => hs (hi ▸ Finset.Subset.refl I)
        rw [if_neg (show ¬(Even K.card ∧ I ⊆ K) from fun h => hs h.2)]
        have hv : h S K * (if I = K then 1 else if I ⊆ K then 1 / 2 else 0) = 0 := by
          rw [if_neg hn, if_neg hs, mul_zero]
        rw [hv, ite_self]
    · conv_lhs => rw [if_neg (show ¬(Even K.card ∧ K ≠ ∅) from fun h => he h.1)]
      conv_rhs => rw [if_neg (show ¬(Even K.card ∧ I ⊆ K) from fun h => he h.1)]
  rw [hf]
  change (∑ L ∈ (Finset.univ : Finset α).powerset.filter
    (fun L => Even L.card ∧ I ⊆ L), (if L = I then (1 : ℝ) else 1 / 2) *
      ∑ K ∈ (Finset.univ : Finset α).powerset.filter
        (fun K => Even K.card ∧ L ⊆ K),
        (legInverseCoeff (K.card - L.card) : ℝ) * hyperlink S K) = _
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := (Finset.univ : Finset α).powerset.filter
    (fun K => Even K.card ∧ I ⊆ K))
    (s' := fun K => K.powerset.filter (fun L => I ⊆ L ∧ Even L.card))]
  · have hc : ∀ K ∈ (Finset.univ : Finset α).powerset.filter
        (fun K => Even K.card ∧ I ⊆ K),
        (∑ L ∈ K.powerset.filter (fun L => I ⊆ L ∧ Even L.card),
          (if L = I then (1 : ℝ) else 1 / 2) *
            ((legInverseCoeff (K.card - L.card) : ℝ) * hyperlink S K)) =
          (if I = K then 1 else 0) * hyperlink S K := by
      intro K hK
      obtain ⟨_, he, hs⟩ := Finset.mem_filter.mp hK
      simp only [← mul_assoc, ← Finset.sum_mul]
      have hv := interval_c_inverse I K hs hI he
      have hreal : (∑ L ∈ K.powerset.filter (fun L => I ⊆ L ∧ Even L.card),
          (if L = I then (1 : ℝ) else 1 / 2) *
            (legInverseCoeff (K.card - L.card) : ℝ)) = if I = K then 1 else 0 := by
        have hvR := congrArg (fun x : ℚ => (x : ℝ)) hv
        simp only [Rat.cast_sum, Rat.cast_mul, apply_ite, Rat.cast_div,
          Rat.cast_one, Rat.cast_ofNat, Rat.cast_zero] at hvR
        by_cases hi : I = K <;> simp only [hi, ite_true, ite_false] at hvR ⊢ <;> exact hvR
      simpa only [mul_assoc] using congrArg (· * hyperlink S K) hreal
    rw [Finset.sum_congr rfl hc]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_filter,
      Finset.mem_powerset, Finset.subset_univ, hI, Finset.Subset.refl, and_self, ite_true]
  · intro L K
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
    constructor
    · rintro ⟨⟨heL, hIL⟩, heK, hLK⟩
      exact ⟨⟨hLK, hIL, heL⟩, heK, hIL.trans hLK⟩
    · rintro ⟨⟨hLK, hIL, heL⟩, heK, _⟩
      exact ⟨⟨heL, hIL⟩, heK, hLK⟩

private theorem synth_eq (S : Finset α → ℝ) (hzero : S ∅ = 0)
    (hcompl : ∀ A, S Aᶜ = S A) : synth S = S := by
  apply even_hyperlink_ext
  · rw [hzero]
    change (∑ K ∈ (Finset.univ : Finset α).powerset.filter
      (fun K => Even K.card ∧ K ≠ ∅), h S K * q K ∅) = 0
    apply Finset.sum_eq_zero
    intro K hK
    rw [(q_laws K (Finset.mem_filter.mp hK).2.2).1, mul_zero]
  · intro A
    change (∑ K ∈ (Finset.univ : Finset α).powerset.filter
      (fun K => Even K.card ∧ K ≠ ∅), h S K * q K Aᶜ) = _
    exact Finset.sum_congr rfl (fun K hK =>
      congrArg (h S K * ·) ((q_laws K (Finset.mem_filter.mp hK).2.2).2 A))
  · exact hcompl
  · exact synth_even_hyperlink S

private theorem sum_q_powersetCard (I A : Finset α) (k : ℕ) (_hk : 0 < k) :
    (∑ K ∈ I.powersetCard k, q K A) =
      -(1 / 2 : ℝ) * ((I.card.choose k : ℝ) - ((I ∩ A).card.choose k : ℝ) -
        ((I \ A).card.choose k : ℝ)) := by
  have hleft : (I.powersetCard k).filter (fun K => K ⊆ A) = (I ∩ A).powersetCard k := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_inter_iff]
    tauto
  have hright : (I.powersetCard k).filter (fun K => K ⊆ Aᶜ) =
      (I \ A).powersetCard k := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_sdiff,
      Finset.subset_compl_iff_disjoint_left]
    tauto
  have hl : (∑ K ∈ I.powersetCard k, if K ⊆ A then (1 : ℝ) else 0) =
      ((I ∩ A).card.choose k : ℝ) := by
    rw [← Finset.sum_filter, hleft, Finset.sum_const, Finset.card_powersetCard]
    simp only [nsmul_eq_mul, mul_one]
  have hr : (∑ K ∈ I.powersetCard k, if K ⊆ Aᶜ then (1 : ℝ) else 0) =
      ((I \ A).card.choose k : ℝ) := by
    rw [← Finset.sum_filter, hright, Finset.sum_const, Finset.card_powersetCard]
    simp only [nsmul_eq_mul, mul_one]
  change (∑ K ∈ I.powersetCard k,
    (((if K ⊆ A then (1 : ℝ) else 0) + (if K ⊆ Aᶜ then 1 else 0) - 1) / 2)) = _
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib, hl, hr,
    Finset.sum_const, Finset.card_powersetCard]
  simp only [nsmul_eq_mul, mul_one]
  ring

private theorem lambda_contraction (I A : Finset α) :
    (∑ K ∈ I.powerset.filter (fun K => Even K.card ∧ K ≠ ∅),
      (legInverseCoeff (I.card - K.card) : ℝ) * q K A) =
      (legFactor I.card (I ∩ A).card : ℝ) := by
  rw [Finset.sum_filter, Finset.sum_powerset]
  have hg : ∀ k, (∑ K ∈ I.powersetCard k,
      if Even K.card ∧ K ≠ ∅ then
        (legInverseCoeff (I.card - K.card) : ℝ) * q K A else 0) =
      if 2 ≤ k ∧ Even k then
        (legInverseCoeff (I.card - k) : ℝ) * ∑ K ∈ I.powersetCard k, q K A else 0 := by
    intro k
    by_cases he : 2 ≤ k ∧ Even k
    · rw [if_pos he, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun K hK => ?_)
      have hc := (Finset.mem_powersetCard.mp hK).2
      have hn : K ≠ ∅ := by
        intro hz
        rw [hz, Finset.card_empty] at hc
        omega
      rw [if_pos (And.intro (hc.symm ▸ he.2) hn), hc]
    · rw [if_neg he]
      apply Finset.sum_eq_zero
      intro K hK
      have hc := (Finset.mem_powersetCard.mp hK).2
      have hn : ¬(Even K.card ∧ K ≠ ∅) := by
        intro ht
        apply he
        have hp : 0 < k := by
          rw [← hc, Finset.card_pos]
          exact Finset.nonempty_iff_ne_empty.mpr ht.2
        have hev : Even k := hc ▸ ht.1
        exact ⟨by obtain ⟨j, hj⟩ := hev; omega, hev⟩
      rw [if_neg hn]
  rw [Finset.sum_congr rfl (fun k _ => hg k), ← Finset.sum_filter]
  have hp : (I ∩ A).card ≤ I.card := Finset.card_le_card Finset.inter_subset_left
  rw [legFactor, if_pos hp]
  conv_rhs => simp only [Rat.cast_mul, Rat.cast_neg, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat, Rat.cast_sum, Rat.cast_sub, Rat.cast_natCast]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have he := (Finset.mem_filter.mp hk).2
  rw [sum_q_powersetCard I A k (by omega), Finset.card_sdiff, Finset.inter_comm A I]
  ring

private theorem lambda_laws :
    (∀ m, legFactor m 0 = 0 ∧ legFactor m m = 0) ∧
    (∀ m p, legFactor m p = legFactor m (m - p)) := by
  have hz : ∀ m, legFactor m 0 = 0 ∧ legFactor m m = 0 := by
    intro m
    have hc : ∀ k ∈ (Finset.range (m + 1)).filter (fun k => 2 ≤ k ∧ Even k),
        (0 : ℕ).choose k = 0 := by
      intro k hk
      exact Nat.choose_eq_zero_of_lt (by have := (Finset.mem_filter.mp hk).2.1; omega)
    constructor
    · rw [legFactor, if_pos (Nat.zero_le m), Nat.sub_zero]
      have hs : (∑ k ∈ (Finset.range (m + 1)).filter (fun k => 2 ≤ k ∧ Even k),
          legInverseCoeff (m - k) *
            ((m.choose k : ℚ) - ((0 : ℕ).choose k : ℚ) - (m.choose k : ℚ))) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [hc k hk, Nat.cast_zero, sub_zero, sub_self, mul_zero]
      rw [hs, mul_zero]
    · rw [legFactor, if_pos (Nat.le_refl m), Nat.sub_self]
      have hs : (∑ k ∈ (Finset.range (m + 1)).filter (fun k => 2 ≤ k ∧ Even k),
          legInverseCoeff (m - k) *
            ((m.choose k : ℚ) - (m.choose k : ℚ) - ((0 : ℕ).choose k : ℚ))) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [hc k hk, Nat.cast_zero, sub_self, sub_zero, mul_zero]
      rw [hs, mul_zero]
  refine ⟨hz, ?_⟩
  intro m p
  by_cases hp : p ≤ m
  · rw [legFactor, legFactor, if_pos hp, if_pos (Nat.sub_le m p), Nat.sub_sub_self hp]
    congr 1
    exact Finset.sum_congr rfl (fun k _ => by ring)
  · rw [legFactor, if_neg hp, Nat.sub_eq_zero_of_le (by omega), (hz m).1]

private theorem reconstruction (S : Finset α → ℝ) (A : Finset α) :
    synth S A = ∑ I ∈ (Finset.univ : Finset α).powerset.filter
      (fun I => Even I.card ∧ I ≠ ∅),
      (legFactor I.card (I ∩ A).card : ℝ) * hyperlink S I := by
  change (∑ K ∈ (Finset.univ : Finset α).powerset.filter
    (fun K => Even K.card ∧ K ≠ ∅),
    (∑ I ∈ (Finset.univ : Finset α).powerset.filter
      (fun I => Even I.card ∧ K ⊆ I),
      (legInverseCoeff (I.card - K.card) : ℝ) * hyperlink S I) * q K A) = _
  rw [Finset.sum_congr rfl (fun K _ => Finset.sum_mul _ _ _)]
  rw [Finset.sum_comm' (t' := (Finset.univ : Finset α).powerset.filter
    (fun I => Even I.card ∧ I ≠ ∅))
    (s' := fun I => I.powerset.filter (fun K => Even K.card ∧ K ≠ ∅))]
  · refine Finset.sum_congr rfl (fun I _ => ?_)
    calc
      _ = (∑ K ∈ I.powerset.filter (fun K => Even K.card ∧ K ≠ ∅),
          (legInverseCoeff (I.card - K.card) : ℝ) * q K A) * hyperlink S I := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun K _ => by ring)
      _ = _ := by rw [lambda_contraction]
  · intro K I
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
    constructor
    · rintro ⟨⟨heK, hnK⟩, heI, hKI⟩
      have hnI : I ≠ ∅ := fun hz => hnK (Finset.subset_empty.mp (hz ▸ hKI))
      exact ⟨⟨hKI, heK, hnK⟩, heI, hnI⟩
    · rintro ⟨⟨hKI, heK, hnK⟩, heI, _⟩
      exact ⟨⟨heK, hnK⟩, heI, hKI⟩

/-- Rational leg factors reconstruct every complement-symmetric set function vanishing at ∅. -/
theorem result : claim := by
  refine ⟨legFactor, lambda_laws.1, lambda_laws.2, ?_⟩
  intro N S hzero hcompl A
  calc
    S A = synth S A := (congrFun (synth_eq S hzero hcompl) A).symm
    _ = _ := reconstruction S A

end

end D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction
