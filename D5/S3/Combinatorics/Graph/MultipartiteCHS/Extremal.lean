/- GID: D5/S3/Combinatorics/Graph/MultipartiteCHS/Extremal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MultipartiteCHS/Extremal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Set.Equitable, mathlib/module/Mathlib.Logic.Equiv.Fintype, mathlib/module/Mathlib.Data.Fintype.Pi, mathlib/module/Mathlib.Data.Fintype.Fin]
   utility: none
   digest: Coefficient comparison and strict extremal partitions for multipartite reciprocal sequences. -/

import D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence
import Mathlib.Data.Set.Equitable
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Fin

open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal

open D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs
open D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence

/-- Elementary coefficient domination propagates through the reciprocal recurrence. -/
private theorem recH_mono {r : ℕ} (a b : Fin r → ℕ)
    (hab : ∀ j, 2 ≤ j → esymmParts a j ≤ esymmParts b j) :
    ∀ d, recH a d ≤ recH b d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      by_cases hd : d = 0
      · simp [hd, recH_zero]
      rw [recH_eq a (by omega), recH_eq b (by omega)]
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hj, hjd⟩ := Finset.mem_Icc.mp hj
      have hc : 0 ≤ (j : ℝ) - 1 := by
        have : (2 : ℝ) ≤ j := by exact_mod_cast hj
        linarith
      have he : (esymmParts a j : ℝ) ≤ esymmParts b j := by
        exact_mod_cast hab j hj
      exact mul_le_mul (mul_le_mul_of_nonneg_left he hc)
        (ih (d - j) (by omega)) (recH_nonneg a _) (by positivity)

/-- A strict increase of the quadratic elementary coefficient is detected at every
positive even degree, provided the smaller partition has positive parts. -/
private theorem recH_even_strict_mono {r : ℕ} (hr : 2 ≤ r) (a b : Fin r → ℕ)
    (ha : ∀ i, 0 < a i)
    (hab : ∀ j, 2 ≤ j → esymmParts a j ≤ esymmParts b j)
    (h2 : esymmParts a 2 < esymmParts b 2) {m : ℕ} (hm : 1 ≤ m) :
    recH a (2 * m) < recH b (2 * m) := by
  rw [recH_eq a (by omega), recH_eq b (by omega)]
  apply Finset.sum_lt_sum
  · intro j hj
    obtain ⟨hj, hjd⟩ := Finset.mem_Icc.mp hj
    have hc : 0 ≤ (j : ℝ) - 1 := by
      have : (2 : ℝ) ≤ j := by exact_mod_cast hj
      linarith
    have he : (esymmParts a j : ℝ) ≤ esymmParts b j := by
      exact_mod_cast hab j hj
    exact mul_le_mul (mul_le_mul_of_nonneg_left he hc)
      (recH_mono a b hab _) (recH_nonneg a _) (by positivity)
  · refine ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, ?_⟩
    have hp : 0 < recH a (2 * m - 2) := by
      by_cases h : m = 1
      · simp [h, recH_zero]
      · have he : 2 * m - 2 = 2 * (m - 1) := by omega
        rw [he]
        exact recH_two_mul_pos hr a ha (by omega)
    have he : (esymmParts a 2 : ℝ) < esymmParts b 2 := by exact_mod_cast h2
    norm_num only [Nat.cast_ofNat, sub_self, add_sub_cancel_left, mul_one, one_mul]
    calc
      (esymmParts a 2 : ℝ) * recH a (2 * m - 2) <
          (esymmParts b 2 : ℝ) * recH a (2 * m - 2) :=
        mul_lt_mul_of_pos_right he hp
      _ ≤ (esymmParts b 2 : ℝ) * recH b (2 * m - 2) :=
        mul_le_mul_of_nonneg_left (recH_mono a b hab _) (by positivity)

private lemma esymmParts_multiset {r : ℕ} (a : Fin r → ℕ) (j : ℕ) :
    esymmParts a j = ((Finset.univ : Finset (Fin r)).val.map a).esymm j :=
  (Finset.esymm_map_val a Finset.univ j).symm

private lemma esymmParts_perm {r : ℕ} (a : Fin r → ℕ)
    (σ : Equiv.Perm (Fin r)) (j : ℕ) :
    esymmParts (a ∘ σ) j = esymmParts a j := by
  simp only [esymmParts_multiset]
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

private lemma recH_sameParts {r : ℕ} {a b : Fin r → ℕ}
    (h : SameParts a b) (d : ℕ) : recH a d = recH b d := by
  obtain ⟨σ, rfl⟩ := h
  apply le_antisymm
  · exact recH_mono _ _ (fun j _ => (esymmParts_perm b σ j).le) d
  · exact recH_mono _ _ (fun j _ => (esymmParts_perm b σ j).ge) d

lemma esymm_cons (x : ℕ) (s : Multiset ℕ) (k : ℕ) :
    (x ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + x * s.esymm k := by
  simp [Multiset.esymm, Multiset.sum_map_mul_left]

private lemma esymm_pair (x y : ℕ) (s : Multiset ℕ) (k : ℕ) :
    (x ::ₘ y ::ₘ s).esymm (k + 2) =
      s.esymm (k + 2) + (x + y) * s.esymm (k + 1) + x * y * s.esymm k := by
  rw [show k + 2 = (k + 1) + 1 by omega, esymm_cons, esymm_cons, esymm_cons]
  ring

private lemma partMultiset_split {r : ℕ} (a : Fin r → ℕ)
    (i k : Fin r) (hik : i ≠ k) :
    (Finset.univ.val.map a) = a i ::ₘ a k ::ₘ
      (((Finset.univ.erase i).erase k).val.map a) := by
  classical
  have hu : (Finset.univ : Finset (Fin r)) =
      insert i (insert k ((Finset.univ.erase i).erase k)) := by
    ext t
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_erase]
    tauto
  conv_lhs => rw [hu]
  rw [Finset.insert_val_of_notMem (by simp [hik]),
    Finset.insert_val_of_notMem (by simp)]
  simp

private lemma esymmParts_transfer {r : ℕ} (a b : Fin r → ℕ)
    (i k : Fin r) (hik : i ≠ k)
    (hrest : ∀ t, t ≠ i → t ≠ k → a t = b t)
    (hs : a i + a k = b i + b k) (hp : a i * a k < b i * b k) :
    (∀ j, 2 ≤ j → esymmParts a j ≤ esymmParts b j) ∧
      esymmParts a 2 < esymmParts b 2 := by
  classical
  have hrem : (((Finset.univ.erase i).erase k).val.map a) =
      (((Finset.univ.erase i).erase k).val.map b) := by
    apply Multiset.map_congr rfl
    intro t ht
    have ht' : t ∈ ((Finset.univ.erase i).erase k) := ht
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at ht'
    exact hrest t ht'.2 ht'.1
  have hf (j : ℕ) : esymmParts a (j + 2) < esymmParts b (j + 2) ∨
      esymmParts a (j + 2) = esymmParts b (j + 2) := by
    rw [esymmParts_multiset, esymmParts_multiset,
      partMultiset_split a i k hik, partMultiset_split b i k hik,
      esymm_pair, esymm_pair, hrem, hs]
    exact lt_or_eq_of_le (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ hp.le) _)
  constructor
  · intro j hj
    obtain ⟨j, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    exact (hf j).elim le_of_lt le_of_eq
  · rw [esymmParts_multiset, esymmParts_multiset,
      partMultiset_split a i k hik, partMultiset_split b i k hik,
      show 2 = 0 + 2 by rfl, esymm_pair, esymm_pair, hrem, hs]
    simpa using Nat.add_lt_add_left hp
      ((((Finset.univ.erase i).erase k).val.map b).esymm 2 +
        (b i + b k) * (((Finset.univ.erase i).erase k).val.map b).esymm 1)

private lemma sum_pair_eq {r : ℕ} (a b : Fin r → ℕ)
    (i k : Fin r) (hik : i ≠ k)
    (hrest : ∀ t, t ≠ i → t ≠ k → a t = b t)
    (hs : a i + a k = b i + b k) : ∑ t, a t = ∑ t, b t := by
  classical
  have hrem : (((Finset.univ.erase i).erase k).val.map a) =
      (((Finset.univ.erase i).erase k).val.map b) := by
    apply Multiset.map_congr rfl
    intro t ht
    have ht' : t ∈ ((Finset.univ.erase i).erase k) := ht
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at ht'
    exact hrest t ht'.2 ht'.1
  change (Finset.univ.val.map a).sum = (Finset.univ.val.map b).sum
  rw [partMultiset_split a i k hik, partMultiset_split b i k hik, hrem]
  simp only [Multiset.sum_cons]
  omega

private lemma sameParts_two_values {r : ℕ} (q : ℕ) (a b : Fin r → ℕ)
    (ha : ∀ i, a i = q ∨ a i = q + 1)
    (hb : ∀ i, b i = q ∨ b i = q + 1)
    (hs : ∑ i, a i = ∑ i, b i) : SameParts a b := by
  classical
  have sumform (c : Fin r → ℕ) (hc : ∀ i, c i = q ∨ c i = q + 1) :
      ∑ i, c i = r * q + (Finset.univ.filter (fun i => c i = q + 1)).card := by
    calc
      _ = ∑ i : Fin r, (q + if c i = q + 1 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        have := hc i
        split_ifs <;> omega
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.card_filter]
        simp
  have hc : (Finset.univ.filter (fun i => a i = q + 1)).card =
      (Finset.univ.filter (fun i => b i = q + 1)).card := by
    have hsa := sumform a ha
    have hsb := sumform b hb
    omega
  let e : {i : Fin r // a i = q + 1} ≃ {i : Fin r // b i = q + 1} :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_subtype] using hc)
  refine ⟨e.extendSubtype, ?_⟩
  funext i
  change a i = b (e.extendSubtype i)
  by_cases hi : a i = q + 1
  · have he := Equiv.extendSubtype_mem e i hi
    exact hi.trans he.symm
  · have he := Equiv.extendSubtype_not_mem e i hi
    have hia := ha i
    have hib := hb (e.extendSubtype i)
    omega

private lemma balancedParts_sum {r n : ℕ} (hr : 0 < r) :
    ∑ i : Fin r, balancedParts r n i = n := by
  classical
  simp only [balancedParts, Finset.sum_add_distrib]
  rw [← Finset.card_filter, Fin.card_filter_val_lt,
    Nat.min_eq_right (Nat.mod_lt n hr).le]
  simpa [Nat.mul_comm] using Nat.div_add_mod n r

private lemma sameParts_balanced {r n : ℕ} (hr : 0 < r) (a : Fin r → ℕ)
    (hsum : ∑ i, a i = n) (hgap : ∀ i k, a i ≤ a k + 1) :
    SameParts a (balancedParts r n) := by
  classical
  have heq : Set.EquitableOn (Finset.univ : Finset (Fin r)) a :=
    fun _ _ _ _ => hgap _ _
  apply sameParts_two_values (n / r) a (balancedParts r n)
  · intro i
    have hv := (Finset.equitableOn_iff.mp heq) i (Finset.mem_univ i)
    simpa only [hsum, Finset.card_univ, Fintype.card_fin] using hv
  · intro i
    simp only [balancedParts]
    split_ifs <;> omega
  · rw [hsum, balancedParts_sum hr]

private lemma sameParts_min {r n : ℕ} (hr : 0 < r) (a : Fin r → ℕ)
    (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = n)
    (hpair : ∀ i k, i ≠ k → a i = 1 ∨ a k = 1) :
    SameParts a (minParts r n) := by
  classical
  have hn : (Finset.univ : Finset (Fin r)).Nonempty := ⟨⟨0, hr⟩, by simp⟩
  obtain ⟨i₀, _, hmax⟩ := Finset.exists_max_image Finset.univ a hn
  have hrest (i : Fin r) (hi : i ≠ i₀) : a i = 1 := by
    have hm := hmax i (Finset.mem_univ i)
    have hp := ha i
    rcases hpair i i₀ hi with h | h
    · exact h
    · omega
  have herase : ∑ i ∈ (Finset.univ : Finset (Fin r)).erase i₀, a i = r - 1 := by
    calc
      _ = ∑ i ∈ (Finset.univ : Finset (Fin r)).erase i₀, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hrest i (Finset.mem_erase.mp hi).1
      _ = r - 1 := by simp
  have hsplit := Finset.add_sum_erase Finset.univ a (Finset.mem_univ i₀)
  have hbig : a i₀ = n - r + 1 := by
    have hai := ha i₀
    rw [herase, hsum] at hsplit
    omega
  let z : Fin r := ⟨0, hr⟩
  refine ⟨Equiv.swap i₀ z, ?_⟩
  funext i
  change a i = minParts r n (Equiv.swap i₀ z i)
  by_cases hi : i = i₀
  · subst i
    simp [minParts, Equiv.swap_apply_left, z, hbig]
  · have hsz : Equiv.swap i₀ z i ≠ z := by
      intro he
      have he' : Equiv.swap i₀ z i = Equiv.swap i₀ z i₀ := by simpa using he
      exact hi ((Equiv.swap i₀ z).injective he')
    have hsv : (Equiv.swap i₀ z i).val ≠ 0 := by
      intro he
      exact hsz (Fin.ext he)
    simp [minParts, hsv, hrest i hi]

private lemma exists_balancing {r n m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (a : Fin r → ℕ) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = n)
    (i k : Fin r) (hgap : a k + 1 < a i) :
    ∃ b : Fin r → ℕ, (∀ t, 0 < b t) ∧ ∑ t, b t = n ∧
      recH a (2 * m) < recH b (2 * m) := by
  classical
  have hik : i ≠ k := by intro h; subst k; omega
  let b : Fin r → ℕ := fun t => if t = i then a i - 1 else if t = k then a k + 1 else a t
  have hi : b i = a i - 1 := by simp [b]
  have hk : b k = a k + 1 := by simp [b, hik.symm]
  have hrest : ∀ t, t ≠ i → t ≠ k → a t = b t := by
    intro t hti htk
    simp [b, hti, htk]
  have hp : ∀ t, 0 < b t := by
    intro t
    by_cases hti : t = i
    · subst t; rw [hi]; omega
    by_cases htk : t = k
    · subst t; rw [hk]; omega
    simpa [b, hti, htk] using ha t
  have hs : a i + a k = b i + b k := by rw [hi, hk]; omega
  have hprod : a i * a k < b i * b k := by
    rw [hi, hk]
    have hx : a i - 1 + 1 = a i := by omega
    nlinarith
  obtain ⟨hcoef, h2⟩ := esymmParts_transfer a b i k hik hrest hs hprod
  refine ⟨b, hp, ?_, recH_even_strict_mono hr a b ha hcoef h2 hm⟩
  rw [← sum_pair_eq a b i k hik hrest hs, hsum]

private lemma exists_unbalancing {r n m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (a : Fin r → ℕ) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = n)
    (i k : Fin r) (hik : i ≠ k) (hki : a k ≤ a i) (hk2 : 2 ≤ a k) :
    ∃ b : Fin r → ℕ, (∀ t, 0 < b t) ∧ ∑ t, b t = n ∧
      recH b (2 * m) < recH a (2 * m) := by
  classical
  let b : Fin r → ℕ := fun t => if t = i then a i + 1 else if t = k then a k - 1 else a t
  have hi : b i = a i + 1 := by simp [b]
  have hk : b k = a k - 1 := by simp [b, hik.symm]
  have hrest : ∀ t, t ≠ i → t ≠ k → b t = a t := by
    intro t hti htk
    simp [b, hti, htk]
  have hp : ∀ t, 0 < b t := by
    intro t
    by_cases hti : t = i
    · subst t; rw [hi]; omega
    by_cases htk : t = k
    · subst t; rw [hk]; omega
    simpa [b, hti, htk] using ha t
  have hs : b i + b k = a i + a k := by rw [hi, hk]; omega
  have hprod : b i * b k < a i * a k := by
    rw [hi, hk]
    have hx : a k - 1 + 1 = a k := by omega
    nlinarith
  obtain ⟨hcoef, h2⟩ := esymmParts_transfer b a i k hik hrest hs hprod
  refine ⟨b, hp, ?_, recH_even_strict_mono hr b a hp hcoef h2 hm⟩
  rw [sum_pair_eq b a i k hik hrest hs, hsum]

private noncomputable def admissible (r n : ℕ) : Finset (Fin r → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.Icc 1 n)).filter (fun a => ∑ i, a i = n)

private lemma mem_admissible {r n : ℕ} (a : Fin r → ℕ) :
    a ∈ admissible r n ↔ (∀ i, 0 < a i) ∧ ∑ i, a i = n := by
  classical
  simp only [admissible, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨h, hs⟩
    exact ⟨fun i => (h i).1, hs⟩
  · rintro ⟨ha, hs⟩
    refine ⟨fun i => ⟨ha i, ?_⟩, hs⟩
    calc
      a i ≤ ∑ t, a t := Finset.single_le_sum (fun t _ => Nat.zero_le (a t)) (Finset.mem_univ i)
      _ = n := hs

private lemma maximizer_balanced {r n m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (a : Fin r → ℕ) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = n)
    (hmax : ∀ b : Fin r → ℕ, (∀ i, 0 < b i) → ∑ i, b i = n →
      recH b (2 * m) ≤ recH a (2 * m)) : SameParts a (balancedParts r n) := by
  apply sameParts_balanced (by omega) a hsum
  intro i k
  by_contra h
  have hgap : a k + 1 < a i := by omega
  obtain ⟨b, hb, hs, hlt⟩ := exists_balancing hr hm a ha hsum i k hgap
  exact (not_lt_of_ge (hmax b hb hs)) hlt

private lemma minimizer_min {r n m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (a : Fin r → ℕ) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = n)
    (hmin : ∀ b : Fin r → ℕ, (∀ i, 0 < b i) → ∑ i, b i = n →
      recH a (2 * m) ≤ recH b (2 * m)) : SameParts a (minParts r n) := by
  apply sameParts_min (by omega) a ha hsum
  intro i k hik
  by_contra h
  push Not at h
  have hi : 2 ≤ a i := by have := ha i; omega
  have hk : 2 ≤ a k := by have := ha k; omega
  rcases le_total (a k) (a i) with hki | hik'
  · obtain ⟨b, hb, hs, hlt⟩ := exists_unbalancing hr hm a ha hsum i k hik hki hk
    exact (not_lt_of_ge (hmin b hb hs)) hlt
  · obtain ⟨b, hb, hs, hlt⟩ := exists_unbalancing hr hm a ha hsum k i hik.symm hik' hi
    exact (not_lt_of_ge (hmin b hb hs)) hlt

/-- The reciprocal coefficients have precisely the concentrated minimum and balanced
maximum among positive multipartite part sizes of a fixed total. -/
theorem recH_extremal {r n m : ℕ} (hr : 2 ≤ r) (hrn : r ≤ n) (hm : 1 ≤ m)
    (a : Fin r → ℕ) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = n) :
    (recH (minParts r n) (2 * m) ≤ recH a (2 * m) ∧
      (recH a (2 * m) = recH (minParts r n) (2 * m) → SameParts a (minParts r n))) ∧
    (recH a (2 * m) ≤ recH (balancedParts r n) (2 * m) ∧
      (recH a (2 * m) = recH (balancedParts r n) (2 * m) → SameParts a (balancedParts r n))) := by
  classical
  have hne : (admissible r n).Nonempty := ⟨a, (mem_admissible a).mpr ⟨ha, hsum⟩⟩
  obtain ⟨lo, hlo, hmin⟩ := Finset.exists_min_image (admissible r n)
    (fun b => recH b (2 * m)) hne
  obtain ⟨hi, hhi, hmax⟩ := Finset.exists_max_image (admissible r n)
    (fun b => recH b (2 * m)) hne
  obtain ⟨hlo_pos, hlo_sum⟩ := (mem_admissible lo).mp hlo
  obtain ⟨hhi_pos, hhi_sum⟩ := (mem_admissible hi).mp hhi
  have hlo_min : ∀ b, (∀ i, 0 < b i) → ∑ i, b i = n →
      recH lo (2 * m) ≤ recH b (2 * m) :=
    fun b hb hs => hmin b ((mem_admissible b).mpr ⟨hb, hs⟩)
  have hhi_max : ∀ b, (∀ i, 0 < b i) → ∑ i, b i = n →
      recH b (2 * m) ≤ recH hi (2 * m) :=
    fun b hb hs => hmax b ((mem_admissible b).mpr ⟨hb, hs⟩)
  have helo := recH_sameParts (minimizer_min hr hm lo hlo_pos hlo_sum hlo_min) (2 * m)
  have hehi := recH_sameParts (maximizer_balanced hr hm hi hhi_pos hhi_sum hhi_max) (2 * m)
  constructor
  · constructor
    · rw [← helo]
      exact hlo_min a ha hsum
    · intro he
      apply minimizer_min hr hm a ha hsum
      intro b hb hs
      rw [he, ← helo]
      exact hlo_min b hb hs
  · constructor
    · rw [← hehi]
      exact hhi_max a ha hsum
    · intro he
      apply maximizer_balanced hr hm a ha hsum
      intro b hb hs
      rw [he, ← hehi]
      exact hhi_max b hb hs

end D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal
