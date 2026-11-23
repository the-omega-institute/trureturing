/- GID: D5/S3/Combinatorics/Graph/PrincipalSpecialization/AlexanderssonLeiteFundamentalLengthRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrincipalSpecialization/AlexanderssonLeiteFundamentalLengthRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/PrincipalSpecialization/AlexanderssonLeiteFundamentalLengthRefutation.claim; result=D5/S3/Combinatorics/Graph/PrincipalSpecialization/AlexanderssonLeiteFundamentalLengthRefutation.result; claim=D5/S3/Combinatorics/Graph/PrincipalSpecialization/AlexanderssonLeiteFundamentalLengthRefutation.claim
   digest: The natural unit interval path on four vertices at q = 16 refutes Question 6.7. -/

module

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The real-rootedness clause of Alexandersson–Leite Question 6.7

The homogeneous monomial coordinates are indexed by proper partial sums.
An alphabet word is represented by its weakly increasing list of positive color indices.
-/

namespace AlexanderssonLeiteFundamentalLengthRefutation

open Finset Polynomial
open scoped BigOperators

private abbrev OrderedEdge {n : ℕ} (h : Fin n → Fin n) (i j : Fin n) : Prop :=
  i < j ∧ j ≤ h i

private def graph {n : ℕ} (h : Fin n → Fin n) : SimpleGraph (Fin n) where
  Adj i j := OrderedEdge h i j ∨ OrderedEdge h j i
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun i => by simp [OrderedEdge]⟩

private abbrev Proper {n : ℕ} {α : Type} (h : Fin n → Fin n) (c : Fin n → α) : Prop :=
  ∀ i j, OrderedEdge h i j → c i ≠ c j

private theorem proper_iff_coloring {n : ℕ} {α : Type} (h : Fin n → Fin n) (c : Fin n → α) :
    Proper h c ↔ ∃ k : (graph h).Coloring α, ∀ i, k i = c i := by
  constructor
  · intro hc
    refine ⟨SimpleGraph.Coloring.mk c ?_, fun _ => rfl⟩
    intro i j hij
    exact hij.elim (hc i j) (fun hji => (hc j i hji).symm)
  · rintro ⟨k, hk⟩ i j hij
    simpa only [hk] using k.valid (v := i) (w := j) (Or.inl hij)

private def ascents {n : ℕ} {α : Type} [LinearOrder α]
    (h : Fin n → Fin n) (c : Fin n → α) : ℕ :=
  ((univ : Finset (Fin n × Fin n)).filter
    (fun ij => OrderedEdge h ij.1 ij.2 ∧ c ij.1 < c ij.2)).card

private theorem ascents_orderIso {n : ℕ} {α β : Type} [LinearOrder α] [LinearOrder β]
    (h : Fin n → Fin n) (e : α ≃o β) (c : Fin n → α) :
    ascents h (e ∘ c) = ascents h c := by
  unfold ascents
  apply congrArg Finset.card
  ext ij
  simp [e.lt_iff_lt]

private abbrev Cuts (m : ℕ) := Finset (Fin m)

private def strictCuts {m : ℕ} {α : Type} [LinearOrder α]
    (w : Fin (m + 1) → α) : Cuts m :=
  univ.filter (fun i => w i.castSucc < w i.succ)

private def rankAt {m : ℕ} (T : Cuts m) (i : Fin (m + 1)) : ℕ :=
  (T.filter (fun j => j.val < i.val)).card

private def cutWord {m : ℕ} (T : Cuts m) (i : Fin (m + 1)) : Fin (T.card + 1) :=
  ⟨rankAt T i, Nat.lt_succ_of_le (card_filter_le _ _)⟩

private theorem rankAt_step {m : ℕ} (T : Cuts m) (i : Fin m) :
    rankAt T i.succ = rankAt T i.castSucc + if i ∈ T then 1 else 0 := by
  classical
  by_cases hi : i ∈ T
  · have hs : T.filter (fun j => j.val < i.succ.val) =
        insert i (T.filter (fun j => j.val < i.castSucc.val)) := by
      ext j
      simp only [mem_filter, mem_insert, Fin.val_succ, Fin.val_castSucc]
      constructor
      · rintro ⟨hj, hji⟩
        by_cases he : j.val = i.val
        · exact Or.inl (Fin.ext he)
        · exact Or.inr ⟨hj, by omega⟩
      · rintro (rfl | ⟨hj, hji⟩)
        · exact ⟨hi, by omega⟩
        · exact ⟨hj, by omega⟩
    unfold rankAt
    rw [hs, card_insert_of_notMem (by simp)]
    simp [hi]
  · have hs : T.filter (fun j => j.val < i.succ.val) =
        T.filter (fun j => j.val < i.castSucc.val) := by
      ext j
      simp only [mem_filter, Fin.val_succ, Fin.val_castSucc]
      constructor
      · rintro ⟨hj, hji⟩
        refine ⟨hj, ?_⟩
        by_contra hn
        exact hi (Fin.ext (show j.val = i.val by omega) ▸ hj)
      · rintro ⟨hj, hji⟩
        exact ⟨hj, by omega⟩
    unfold rankAt
    rw [hs]
    simp [hi]

private theorem rankAt_first {m : ℕ} (T : Cuts m) : rankAt T 0 = 0 := by
  simp [rankAt]

private theorem rankAt_last {m : ℕ} (T : Cuts m) : rankAt T (Fin.last m) = T.card := by
  change (T.filter (fun j => j.val < m)).card = T.card
  simp

private theorem cutWord_mono {m : ℕ} (T : Cuts m) : Monotone (cutWord T) := by
  refine Fin.monotone_iff_le_succ.2 fun i => ?_
  change rankAt T i.castSucc ≤ rankAt T i.succ
  rw [rankAt_step]
  omega

private theorem strictCuts_cutWord {m : ℕ} (T : Cuts m) : strictCuts (cutWord T) = T := by
  ext i
  simp only [strictCuts, mem_filter, mem_univ, true_and]
  change rankAt T i.castSucc < rankAt T i.succ ↔ _
  rw [rankAt_step]
  by_cases hi : i ∈ T <;> simp [hi]

private theorem cutWord_surjective {m : ℕ} (T : Cuts m) :
    Function.Surjective (cutWord T) := by
  intro a
  have reach : ∀ i : Fin (m + 1), a.val ≤ rankAt T i →
      ∃ j : Fin (m + 1), cutWord T j = a := by
    intro i
    induction i using Fin.induction with
    | zero =>
        intro h
        exact ⟨0, Fin.ext (by rw [show (cutWord T 0).val = rankAt T 0 from rfl,
          rankAt_first] at *; omega)⟩
    | succ i ih =>
        intro h
        by_cases hprev : a.val ≤ rankAt T i.castSucc
        · exact ih hprev
        · refine ⟨i.succ, Fin.ext ?_⟩
          change rankAt T i.succ = a.val
          rw [rankAt_step] at h ⊢
          by_cases hi : i ∈ T <;> simp [hi] at h ⊢ <;> omega
  exact reach (Fin.last m) (by rw [rankAt_last]; omega)

private theorem rankAt_strictCuts {m r : ℕ} (w : Fin (m + 1) → Fin r)
    (hm : Monotone w) (hs : Function.Surjective w) :
    ∀ i, rankAt (strictCuts w) i = (w i).val := by
  have hzero : (w 0).val = 0 := by
    obtain ⟨j, hj⟩ := hs ⟨0, Nat.zero_lt_of_lt (w 0).isLt⟩
    have hle := hm (Fin.zero_le j)
    rw [hj] at hle
    change (w 0).val ≤ 0 at hle
    omega
  have hstep (i : Fin m) : (w i.succ).val ≤ (w i.castSucc).val + 1 := by
    by_contra! h
    obtain ⟨j, hj⟩ := hs ⟨(w i.castSucc).val + 1, by have := (w i.succ).isLt; omega⟩
    have hjval := congrArg Fin.val hj
    by_cases hji : j ≤ i.castSucc
    · have hc := hm hji
      change (w j).val ≤ (w i.castSucc).val at hc
      dsimp at hjval
      omega
    · have hji' : i.succ ≤ j := by
        change i.val + 1 ≤ j.val
        change ¬ j.val ≤ i.val at hji
        omega
      have hc := hm hji'
      change (w i.succ).val ≤ (w j).val at hc
      dsimp at hjval
      omega
  intro i
  induction i using Fin.induction with
  | zero => rw [rankAt_first, hzero]
  | succ i ih =>
      have hmono := hm (Fin.castSucc_le_succ i)
      change (w i.castSucc).val ≤ (w i.succ).val at hmono
      rw [rankAt_step, ih]
      simp only [strictCuts, mem_filter, mem_univ, true_and, Fin.lt_def]
      have := hstep i
      split <;> omega

private theorem strictCuts_card {m r : ℕ} (w : Fin (m + 1) → Fin r)
    (hm : Monotone w) (hs : Function.Surjective w) :
    (strictCuts w).card + 1 = r := by
  have hpos := (w 0).isLt
  obtain ⟨j, hj⟩ := hs ⟨r - 1, by omega⟩
  have hlew := hm (Fin.le_last j)
  rw [hj] at hlew
  change r - 1 ≤ (w (Fin.last m)).val at hlew
  have hrank := rankAt_strictCuts w hm hs (Fin.last m)
  rw [rankAt_last] at hrank
  have := (w (Fin.last m)).isLt
  omega

/-- In cut coordinates, a fundamental element contains each monomial whose strict
positions contain S. The coefficient is one because its sorted word is unique. -/
private noncomputable def fundamental {m : ℕ} (S : Cuts m) : Cuts m → ℝ :=
  fun T => if S ⊆ T then 1 else 0

private noncomputable def monomialImage {m : ℕ} (T : Cuts m) : Polynomial ℝ :=
  X ^ (T.card + 1) * (1 - X) ^ (m - T.card)

private noncomputable def psi (m : ℕ) : (Cuts m → ℝ) →ₗ[ℝ] Polynomial ℝ where
  toFun f := ∑ T : Cuts m, f T • monomialImage T
  map_add' f g := by simp only [Pi.add_apply, add_smul, sum_add_distrib]
  map_smul' a f := by
    simp only [Pi.smul_apply, smul_smul, RingHom.id_apply, smul_sum, smul_eq_mul]

private theorem psi_fundamental {m : ℕ} (S : Cuts m) :
    psi m (fundamental S) = X ^ (S.card + 1) := by
  classical
  let available : Finset (Fin m) := univ \ S
  have hAvailable : available.card = m - S.card := by
    simp [available, card_sdiff_of_subset (subset_univ S)]
  have hreindex :
      (∑ T ∈ (univ : Finset (Cuts m)).filter (S ⊆ ·), monomialImage T) =
      ∑ U ∈ available.powerset,
        X ^ (S.card + 1) * (X ^ U.card * (1 - X) ^ (available.card - U.card)) := by
    refine sum_nbij' (· \ S) (· ∪ S) ?_ ?_ ?_ ?_ ?_
    · intro T hT
      exact mem_powerset.2 (fun i hi => mem_sdiff.2 ⟨mem_univ i, (mem_sdiff.1 hi).2⟩)
    · intro U _
      exact mem_filter.2 ⟨mem_univ _, subset_union_right⟩
    · intro T hT
      exact sdiff_union_of_subset (mem_filter.1 hT).2
    · intro U hU
      ext i
      have hsub := mem_powerset.1 hU
      simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨hi | hi, hn⟩
        · exact hi
        · exact (hn hi).elim
      · intro hi
        exact ⟨Or.inl hi, (mem_sdiff.1 (hsub hi)).2⟩
    · intro T hT
      have hST := (mem_filter.1 hT).2
      have hcard := card_sdiff_add_card_eq_card hST
      have hpow : T.card + 1 = (S.card + 1) + (T \ S).card := by omega
      have hexp : m - T.card = available.card - (T \ S).card := by omega
      rw [monomialImage, hpow, hexp, pow_add, mul_assoc]
  change (∑ T : Cuts m, (if S ⊆ T then (1 : ℝ) else 0) • monomialImage T) = _
  simp only [ite_smul, one_smul, zero_smul, ← sum_filter]
  rw [hreindex, ← mul_sum, sum_pow_mul_eq_add_pow]
  simp

/-- Two words contribute the same monomial exactly when every color has
the same multiplicity in the two words. -/
private abbrev SameMonomial {n : ℕ} {α : Type} (c w : Fin n → α) : Prop :=
  (List.ofFn c).Perm (List.ofFn w)

private theorem sameMonomial_comp_iff {n : ℕ} {α β : Type} {e : α → β}
    (he : Function.Injective e) (c w : Fin n → α) :
    SameMonomial (e ∘ c) (e ∘ w) ↔ SameMonomial c w := by
  simpa only [List.map_ofFn] using
    (List.map_perm_map_iff he : ((List.ofFn c).map e).Perm ((List.ofFn w).map e) ↔ _)

private theorem sameMonomial_surjective {n : ℕ} {α : Type} {c w : Fin n → α}
    (h : SameMonomial c w) (hw : Function.Surjective w) : Function.Surjective c := by
  intro a
  obtain ⟨i, rfl⟩ := hw a
  exact ((List.mem_ofFn' c (w i)).1 (h.mem_iff.2 ((List.mem_ofFn' w (w i)).2 ⟨i, rfl⟩)))

private noncomputable def coefficient {n : ℕ} {α : Type} [Fintype α] [LinearOrder α]
    (h : Fin n → Fin n) (q : ℝ) (w : Fin n → α) : ℝ := by
  classical
  exact ∑ c ∈ univ.filter (fun c => Proper h c ∧ SameMonomial c w), q ^ ascents h c

private theorem coefficient_orderIso {n : ℕ} {α β : Type} [Fintype α] [Fintype β]
    [LinearOrder α] [LinearOrder β] (h : Fin n → Fin n) (q : ℝ)
    (e : α ≃o β) (w : Fin n → α) :
    coefficient h q (e ∘ w) = coefficient h q w := by
  classical
  unfold coefficient
  symm
  refine sum_equiv (Equiv.arrowCongr (.refl (Fin n)) e.toEquiv) ?_ ?_
  · intro c
    change (_ ∈ univ.filter _ ↔ (e ∘ c) ∈ univ.filter _)
    simp only [mem_filter, mem_univ, true_and, sameMonomial_comp_iff e.injective]
    simp [Proper, e.injective.eq_iff]
  · intro c _
    change q ^ ascents h c = q ^ ascents h (e ∘ c)
    rw [ascents_orderIso]

private def palette {n : ℕ} (w : Fin n → ℕ+) : Finset ℕ+ := univ.image w

private def paletteWord {n : ℕ} (w : Fin n → ℕ+) (i : Fin n) : palette w :=
  ⟨w i, mem_image_of_mem w (mem_univ _)⟩

private theorem paletteWord_surjective {n : ℕ} (w : Fin n → ℕ+) :
    Function.Surjective (paletteWord w) := by
  intro a
  obtain ⟨i, _, hi⟩ := mem_image.1 a.property
  exact ⟨i, Subtype.ext hi⟩

/-- The literal coefficient of the coloring sum at the monomial with color
word w. A coloring contributing to this coefficient uses colors in w. -/
private noncomputable def sourceColorings {n : ℕ} (h : Fin n → Fin n) (w : Fin n → ℕ+) :
    Finset (Fin n → palette w) := by
  classical
  exact univ.filter (fun c =>
    (∃ k : (graph h).Coloring ℕ+, ∀ i, k i = (c i).val) ∧
    SameMonomial (Subtype.val ∘ c) w)

private theorem sourceColorings_spec {n : ℕ} (h : Fin n → Fin n)
    (w c : Fin n → ℕ+) :
    ((∃ k : (graph h).Coloring ℕ+, ∀ i, k i = c i) ∧
      ∀ a, (List.ofFn c).count a = (List.ofFn w).count a) ↔
    ∃! d : Fin n → palette w, d ∈ sourceColorings h w ∧ Subtype.val ∘ d = c := by
  classical
  rw [← List.perm_iff_count]
  constructor
  · rintro ⟨hp, hm⟩
    have hs (i : Fin n) : c i ∈ palette w := by
      have hc := hm.mem_iff.1 ((List.mem_ofFn' c (c i)).2 ⟨i, rfl⟩)
      obtain ⟨j, hj⟩ := (List.mem_ofFn' w (c i)).1 hc
      exact mem_image.2 ⟨j, mem_univ _, hj⟩
    let d : Fin n → palette w := fun i => ⟨c i, hs i⟩
    refine ⟨d, ⟨?_, rfl⟩, ?_⟩
    · simpa [sourceColorings, d, Function.comp_def] using And.intro hp hm
    · intro e he
      exact funext fun i => Subtype.ext (congrFun he.2 i)
  · rintro ⟨d, ⟨hd, rfl⟩, _⟩
    simpa [sourceColorings] using hd

private noncomputable def sourceCoefficient {n : ℕ} (h : Fin n → Fin n) (q : ℝ)
    (w : Fin n → ℕ+) : ℝ :=
  ∑ c ∈ sourceColorings h w, q ^ ascents h (Subtype.val ∘ c)

private theorem sourceCoefficient_eq_coefficient {n : ℕ} (h : Fin n → Fin n) (q : ℝ)
    (w : Fin n → ℕ+) :
    sourceCoefficient h q w = coefficient h q (paletteWord w) := by
  classical
  unfold sourceCoefficient coefficient
  apply sum_congr
  · ext c
    let c' : Fin n → ℕ+ := Subtype.val ∘ c
    have hspec : c ∈ sourceColorings h w ↔
        (∃ k : (graph h).Coloring ℕ+, ∀ i, k i = c' i) ∧ SameMonomial c' w := by
      have h := sourceColorings_spec h w c'
      rw [← List.perm_iff_count] at h
      rw [h]
      constructor
      · intro hc
        refine ⟨c, ⟨hc, rfl⟩, ?_⟩
        intro e he
        exact funext fun i => Subtype.ext (congrFun he.2 i)
      · rintro ⟨d, ⟨hd, he⟩, _⟩
        have : d = c := funext fun i => Subtype.ext (congrFun he i)
        simpa [this] using hd
    rw [hspec, ← proper_iff_coloring]
    have hm := sameMonomial_comp_iff Subtype.val_injective c (paletteWord w)
    change SameMonomial c' w ↔ _ at hm
    simp [hm, c', Proper, Subtype.val_injective.eq_iff]
  · intro c _
    rfl

private def rankedWord {n : ℕ} (w : Fin n → ℕ+) : Fin n → Fin (palette w).card :=
  (Finset.orderIsoOfFin (palette w) rfl).symm ∘ paletteWord w

private theorem rankedWord_surjective {n : ℕ} (w : Fin n → ℕ+) :
    Function.Surjective (rankedWord w) :=
  (Finset.orderIsoOfFin (palette w) rfl).symm.surjective.comp (paletteWord_surjective w)

private theorem rankedWord_mono {n : ℕ} (w : Fin n → ℕ+) (hw : Monotone w) :
    Monotone (rankedWord w) :=
  (Finset.orderIsoOfFin (palette w) rfl).symm.monotone.comp hw

private theorem strictCuts_rankedWord {m : ℕ} (w : Fin (m + 1) → ℕ+) :
    strictCuts (rankedWord w) = strictCuts w := by
  ext i
  simp only [strictCuts, mem_filter, mem_univ, true_and, rankedWord, Function.comp_apply,
    OrderIso.lt_iff_lt]
  rfl

private theorem coefficient_eq_cutWord {m r : ℕ} (h : Fin (m + 1) → Fin (m + 1)) (q : ℝ)
    (w : Fin (m + 1) → Fin r) (hm : Monotone w) (hs : Function.Surjective w) :
    coefficient h q w = coefficient h q (cutWord (strictCuts w)) := by
  let e := Fin.castOrderIso (strictCuts_card w hm hs)
  have hw : e ∘ cutWord (strictCuts w) = w := by
    funext i
    exact Fin.ext (rankAt_strictCuts w hm hs i)
  rw [← coefficient_orderIso h q e, hw]

private theorem sourceCoefficient_eq_cutWord {m : ℕ} (h : Fin (m + 1) → Fin (m + 1))
    (q : ℝ) (w : Fin (m + 1) → ℕ+) (hw : Monotone w) :
    sourceCoefficient h q w = coefficient h q (cutWord (strictCuts w)) := by
  rw [sourceCoefficient_eq_coefficient,
    ← coefficient_orderIso h q (Finset.orderIsoOfFin (palette w) rfl).symm]
  change coefficient h q (rankedWord w) = _
  rw [coefficient_eq_cutWord h q _ (rankedWord_mono w hw) (rankedWord_surjective w),
    strictCuts_rankedWord]

/-- One actual alphabet word realizing each cut pattern. -/
private def alphabetWord {m : ℕ} (T : Cuts m) : Fin (m + 1) → ℕ+ :=
  Nat.succPNat ∘ Fin.val ∘ cutWord T

private theorem alphabetWord_mono {m : ℕ} (T : Cuts m) : Monotone (alphabetWord T) :=
  fun _ _ hij => Nat.succPNat_mono (show _ ≤ _ from cutWord_mono T hij)

private theorem strictCuts_alphabetWord {m : ℕ} (T : Cuts m) : strictCuts (alphabetWord T) = T := by
  refine Eq.trans ?_ (strictCuts_cutWord T)
  ext i
  simp only [strictCuts, mem_filter, mem_univ, true_and, alphabetWord, Function.comp_apply,
    Nat.succPNat_lt_succPNat]
  rfl

/-- Coefficient of a fundamental basis element at any actual alphabet word.
The word is already sorted, so each eligible monomial occurs exactly once. -/
private theorem fundamental_apply_word {m : ℕ} (S : Cuts m) (w : Fin (m + 1) → ℕ+) :
    fundamental S (strictCuts w) =
    if ∀ i ∈ S, w i.castSucc < w i.succ then 1 else 0 := by
  classical
  simp [fundamental, strictCuts, Finset.subset_iff]

private noncomputable def chromaticCoordinates {m : ℕ} (h : Fin (m + 1) → Fin (m + 1))
    (q : ℝ) (T : Cuts m) : ℝ :=
  sourceCoefficient h q (alphabetWord T)

private theorem chromaticCoordinates_apply_word {m : ℕ} (h : Fin (m + 1) → Fin (m + 1))
    (q : ℝ) (w : Fin (m + 1) → ℕ+) (hw : Monotone w) :
    chromaticCoordinates h q (strictCuts w) = sourceCoefficient h q w := by
  unfold chromaticCoordinates
  rw [sourceCoefficient_eq_cutWord h q _ (alphabetWord_mono _), strictCuts_alphabetWord,
    sourceCoefficient_eq_cutWord h q w hw]

private theorem chromaticCoordinates_eq_cutWord {m : ℕ} (h : Fin (m + 1) → Fin (m + 1))
    (q : ℝ) (T : Cuts m) :
    chromaticCoordinates h q T = coefficient h q (cutWord T) := by
  rw [← strictCuts_alphabetWord T, chromaticCoordinates_apply_word h q _ (alphabetWord_mono T),
    sourceCoefficient_eq_cutWord h q _ (alphabetWord_mono T)]

private theorem fundamental_eq_sum {m : ℕ} (S : Cuts m) :
    fundamental S =
      ∑ T ∈ (univ : Finset (Cuts m)).filter (S ⊆ ·), Pi.single T (1 : ℝ) := by
  classical
  funext U
  have hf := fundamental_apply_word S (alphabetWord U)
  rw [strictCuts_alphabetWord] at hf
  have hcuts : (∀ i ∈ S, alphabetWord U i.castSucc < alphabetWord U i.succ) ↔ S ⊆ U := by
    calc
      _ ↔ S ⊆ strictCuts (alphabetWord U) := by simp [strictCuts, Finset.subset_iff]
      _ ↔ S ⊆ U := by rw [strictCuts_alphabetWord]
  rw [hf]
  simp only [hcuts, sum_apply]
  by_cases hSU : S ⊆ U
  · rw [ite_eq_left hSU, sum_eq_single_of_mem U (by simp [hSU])]
    · simp
    · intro T _ hTU
      simp [Ne.symm hTU]
  · rw [ite_eq_right hSU]
    symm
    apply sum_eq_zero
    intro T hT
    have hTU : T ≠ U := fun he => hSU (he ▸ (mem_filter.1 hT).2)
    simp [Ne.symm hTU]

/-- The source prescription determines a unique linear map. Descending by cut
inclusion, each fundamental element determines the value at its own monomial. -/
private theorem psi_unique (m : ℕ) (L : (Cuts m → ℝ) →ₗ[ℝ] Polynomial ℝ)
    (hL : ∀ S, L (fundamental S) = X ^ (S.card + 1)) : L = psi m := by
  classical
  have hpoint : ∀ k (S : Cuts m), m - S.card = k →
      L (Pi.single S 1) = psi m (Pi.single S 1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro S hS
      let supers := (univ : Finset (Cuts m)).filter (S ⊆ ·)
      have hmem : S ∈ supers := by simp [supers]
      have hsum := (hL S).trans (psi_fundamental S).symm
      rw [fundamental_eq_sum, map_sum, map_sum] at hsum
      change (∑ T ∈ supers, L (Pi.single T 1)) =
        ∑ T ∈ supers, psi m (Pi.single T 1) at hsum
      rw [← add_sum_erase _ _ hmem, ← add_sum_erase supers (fun T => psi m (Pi.single T 1))
        hmem] at hsum
      have htail : (∑ T ∈ supers.erase S, L (Pi.single T 1)) =
          ∑ T ∈ supers.erase S, psi m (Pi.single T 1) := by
        apply sum_congr rfl
        intro T hT
        have hST := (mem_filter.1 (mem_of_mem_erase hT)).2
        have hne := ne_of_mem_erase hT
        have hcard := card_lt_card (ssubset_of_subset_of_ne hST (Ne.symm hne))
        have hbound : T.card ≤ m := by simpa using card_le_univ T
        exact ih _ (by omega) T rfl
      rw [htail] at hsum
      exact add_right_cancel hsum
  apply LinearMap.ext
  intro f
  have hf : (∑ T : Cuts m, f T • Pi.single T (1 : ℝ)) = f := by
    funext U
    rw [sum_apply, sum_eq_single_of_mem U (mem_univ _)]
    · simp
    · intro T _ hne
      simp [Ne.symm hne]
  have hsingle (T : Cuts m) := hpoint (m - T.card) T rfl
  calc
    L f = L (∑ T : Cuts m, f T • Pi.single T (1 : ℝ)) := congrArg L hf.symm
    _ = psi m (∑ T : Cuts m, f T • Pi.single T (1 : ℝ)) := by
      simp only [map_sum, LinearMap.map_smul, hsingle]
    _ = psi m f := congrArg (psi m) hf

/-- In positive degree the source defines Ψ by its values on the fundamental
basis. The computed monomial formula is a realization of this prescription. -/
private noncomputable def sourcePsi (m : ℕ) : (Cuts m → ℝ) →ₗ[ℝ] Polynomial ℝ :=
  Classical.choose (show ∃ L : (Cuts m → ℝ) →ₗ[ℝ] Polynomial ℝ,
    ∀ S, L (fundamental S) = X ^ (S.card + 1) from ⟨psi m, psi_fundamental⟩)

private theorem sourcePsi_eq (m : ℕ) : sourcePsi m = psi m :=
  psi_unique m _ (Classical.choose_spec (show ∃ L : (Cuts m → ℝ) →ₗ[ℝ] Polynomial ℝ,
    ∀ S, L (fundamental S) = X ^ (S.card + 1) from ⟨psi m, psi_fundamental⟩))

private noncomputable def sourceImage {n : ℕ} (h : Fin n → Fin n) (q : ℝ) : Polynomial ℝ :=
  match n with
  | 0 => 1
  | m + 1 => sourcePsi m (chromaticCoordinates h q)

/-- The candidate maps here are computable so the witness can be enumerated by
the kernel. The surjectivity filter enforces the use of every palette color. -/
private def packed {n : ℕ} (h : Fin n → Fin n) (r : ℕ) : Finset (Fin n → Fin r) :=
  univ.filter (fun c => Proper h c ∧ ∀ a, ∃ i, c i = a)

private theorem mem_packed {n r : ℕ} (h : Fin n → Fin n) (c : Fin n → Fin r) :
    c ∈ packed h r ↔ Proper h c ∧ Function.Surjective c := by
  simp [packed, Function.Surjective]

private noncomputable def sortedColors {n r : ℕ} (c : Fin n → Fin r) : Fin n → Fin r :=
  c ∘ Tuple.sort c

private noncomputable def colorCuts {m r : ℕ} (c : Fin (m + 1) → Fin r) : Cuts m :=
  strictCuts (sortedColors c)

private theorem colorCuts_card {m r : ℕ} (c : Fin (m + 1) → Fin r)
    (hc : Function.Surjective c) : (colorCuts c).card + 1 = r :=
  strictCuts_card _ (Tuple.monotone_sort c) (hc.comp (Tuple.sort c).surjective)

private theorem sortedColors_eq_of_sameMonomial {n r : ℕ} {c w : Fin n → Fin r}
    (hc : SameMonomial c w) (hw : Monotone w) : sortedColors c = w := by
  apply List.ofFn_injective
  exact ((Tuple.sort c).ofFn_comp_perm c |>.trans hc).eq_of_sortedLE
    (List.sortedLE_ofFn_iff.2 (Tuple.monotone_sort c)) (List.sortedLE_ofFn_iff.2 hw)

private theorem packed_filter_sum {m r : ℕ} (h : Fin (m + 1) → Fin (m + 1))
    (q : ℝ) (T : Cuts m) (hT : T.card + 1 = r) :
    (∑ c ∈ (packed h r).filter (fun c => colorCuts c = T), q ^ ascents h c) =
      coefficient h q (cutWord T) := by
  classical
  let e := Fin.castOrderIso hT
  let w := e ∘ cutWord T
  rw [← coefficient_orderIso h q e]
  change _ = coefficient h q w
  unfold coefficient
  have hw : Monotone w := e.monotone.comp (cutWord_mono T)
  have hws : Function.Surjective w := e.surjective.comp (cutWord_surjective T)
  have hwCuts : strictCuts w = T := by
    refine Eq.trans ?_ (strictCuts_cutWord T)
    ext i
    simp only [strictCuts, mem_filter, mem_univ, true_and, w, Function.comp_apply,
      OrderIso.lt_iff_lt]
  apply sum_congr _ (fun _ _ => rfl)
  ext c
  simp only [mem_filter, mem_packed, mem_univ, true_and]
  constructor
  · rintro ⟨⟨hp, hs⟩, hcuts⟩
    refine ⟨hp, ?_⟩
    have heq : sortedColors c = w := by
      funext i
      apply Fin.ext
      change (sortedColors c i).val = rankAt T i
      rw [← rankAt_strictCuts (sortedColors c) (Tuple.monotone_sort c)
        (hs.comp (Tuple.sort c).surjective), ← colorCuts, hcuts]
    rw [← heq]
    exact ((Tuple.sort c).ofFn_comp_perm c).symm
  · rintro ⟨hp, hm⟩
    exact ⟨⟨hp, sameMonomial_surjective hm hws⟩,
      (congrArg strictCuts (sortedColors_eq_of_sameMonomial hm hw)).trans hwCuts⟩

private theorem packed_by_cuts {m : ℕ} (h : Fin (m + 1) → Fin (m + 1))
    (q : ℝ) (r : ℕ) :
    (∑ c ∈ packed h r, q ^ ascents h c) =
    ∑ T ∈ (univ : Finset (Cuts m)).filter (fun T => T.card + 1 = r),
      coefficient h q (cutWord T) := by
  classical
  rw [← sum_fiberwise_of_maps_to (g := colorCuts)
    (t := (univ : Finset (Cuts m)).filter (fun T => T.card + 1 = r))
    (fun c hc => mem_filter.2 ⟨mem_univ _, colorCuts_card c ((mem_packed h c).1 hc).2⟩)]
  exact sum_congr rfl fun T hT => packed_filter_sum h q T (mem_filter.1 hT).2

private theorem sourceImage_eq_packed {m : ℕ} (h : Fin (m + 1) → Fin (m + 1)) (q : ℝ) :
    sourceImage h q =
    ∑ r ∈ range (m + 2), (∑ c ∈ packed h r, q ^ ascents h c) •
      (X ^ r * (1 - X) ^ (m + 1 - r)) := by
  classical
  change sourcePsi m (chromaticCoordinates h q) = _
  rw [sourcePsi_eq]
  change (∑ T : Cuts m, chromaticCoordinates h q T • monomialImage T) = _
  have hr (T : Cuts m) : T.card + 1 ∈ range (m + 2) := by
    have hcard : T.card ≤ m := by simpa using card_le_univ T
    exact mem_range.2 (by omega)
  rw [← sum_fiberwise_of_maps_to (fun T _ => hr T)]
  apply sum_congr rfl
  intro r _
  rw [packed_by_cuts, sum_smul]
  apply sum_congr rfl
  intro T hT
  have hTr : T.card + 1 = r := (mem_filter.1 hT).2
  rw [chromaticCoordinates_eq_cutWord, monomialImage, ← hTr]
  have : m + 1 - (T.card + 1) = m - T.card := by omega
  rw [this]

/-- The last yes/no clause of Question 6.7, with real-rootedness expressed
by splitting over ℝ. The positive-degree hypothesis is explicit. -/
public def claim : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (h : Fin n → Fin n), Monotone h →
    (∀ i, i ≤ h i) → ∀ (q : ℝ), 0 ≤ q → (sourceImage h q).Splits

private def pathH : Fin 4 → Fin 4 := ![1, 2, 3, 3]

private theorem pathH_mono : Monotone pathH := by
  apply Fin.monotone_iff_le_succ.2
  decide

private theorem pathH_le : ∀ i, i ≤ pathH i := by decide

private theorem pathH_edges :
    ∀ i j : Fin 4, OrderedEdge pathH i j ↔ j.val = i.val + 1 := by decide

private theorem path_ascents_le {r : ℕ} (c : Fin 4 → Fin r) : ascents pathH c ≤ 3 := by
  have hEdges : ((univ : Finset (Fin 4 × Fin 4)).filter
      (fun ij => ij.2.val = ij.1.val + 1)).card = 3 := by decide
  rw [← hEdges]
  apply card_le_card
  intro ij hij
  exact mem_filter.2 ⟨mem_univ _, (pathH_edges ij.1 ij.2).1 (mem_filter.1 hij).2.1⟩

private def histogram (r a : ℕ) : ℕ :=
  ((packed pathH r).filter (fun c => ascents pathH c = a)).card

private def pathCounts : Fin 5 → Fin 4 → ℕ :=
  ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 1, 0], ![0, 9, 9, 0], ![1, 11, 11, 1]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Kernel reduction enumerates the functions on each of the five palettes.
private theorem histogram_eq_pathCounts :
    ∀ (r : Fin 5) (a : Fin 4), histogram r.val a.val = pathCounts r a := by
  decide +kernel

private theorem path_weight_eq_histogram (r : ℕ) :
    (∑ c ∈ packed pathH r, (16 : ℝ) ^ ascents pathH c) =
      ∑ a ∈ range 4, (histogram r a : ℝ) * 16 ^ a := by
  rw [← sum_fiberwise_of_maps_to (g := ascents pathH) (t := range 4)
    (fun c _ => mem_range.2 (Nat.lt_succ_of_le (path_ascents_le c)))]
  apply sum_congr rfl
  intro a _
  rw [← nsmul_eq_mul]
  unfold histogram
  rw [← sum_const]
  apply sum_congr rfl
  intro c hc
  rw [(mem_filter.1 hc).2]

private theorem path_weight (r : Fin 5) :
    (∑ c ∈ packed pathH r.val, (16 : ℝ) ^ ascents pathH c) =
      (![0, 0, 272, 2448, 7089] : Fin 5 → ℝ) r := by
  rw [path_weight_eq_histogram]
  have hh (a : Fin 4) := histogram_eq_pathCounts r a
  rw [sum_range]
  simp_rw [hh]
  fin_cases r <;> norm_num [pathCounts, Fin.sum_univ_succ]

private theorem path_image :
    sourceImage pathH 16 =
      X ^ 2 * (C (4913 : ℝ) * X ^ 2 + C 1904 * X + C 272) := by
  classical
  rw [sourceImage_eq_packed]
  change (∑ r ∈ range 5, _) = _
  rw [sum_range]
  calc
    _ = ∑ r : Fin 5, (![0, 0, 272, 2448, 7089] : Fin 5 → ℝ) r •
        ((X : Polynomial ℝ) ^ r.val * (1 - X) ^ (4 - r.val)) := by
      apply sum_congr rfl
      intro r _
      rw [path_weight r]
    _ = _ := by
      norm_num [Fin.sum_univ_succ, smul_eq_C_mul, C_ofNat] <;> ring

private theorem path_image_not_splits : ¬ (sourceImage pathH 16).Splits := by
  let p : Polynomial ℝ := C (4913 : ℝ) * X ^ 2 + C 1904 * X + C 272
  have hform : sourceImage pathH 16 = (X - C 0) * ((X - C 0) * p) := by
    rw [path_image]
    simp only [map_zero, sub_zero, p, pow_two, mul_assoc]
  intro hs
  rw [hform, splits_X_sub_C_mul_iff, splits_X_sub_C_mul_iff] at hs
  have hd : p.degree = 2 := degree_quadratic (by norm_num : (4913 : ℝ) ≠ 0)
  obtain ⟨a, ha⟩ := hs.exists_eval_eq_zero (by rw [hd]; norm_num)
  have he : (4913 : ℝ) * (a * a) + 1904 * a + 272 = 0 := by
    simpa [p, eval_add, eval_mul, eval_pow, pow_two] using ha
  have hsq := discrim_eq_sq_of_quadratic_eq_zero he
  norm_num [discrim] at hsq
  nlinarith only [hsq, sq_nonneg (2 * 4913 * a + 1904)]

/-- The ordered path on four vertices at q = 16 refutes the source claim. -/
public theorem result : ¬ claim := by
  intro hc
  exact path_image_not_splits (hc 4 (by decide) pathH pathH_mono pathH_le 16 (by norm_num))

#print axioms claim
#print axioms result

end AlexanderssonLeiteFundamentalLengthRefutation
