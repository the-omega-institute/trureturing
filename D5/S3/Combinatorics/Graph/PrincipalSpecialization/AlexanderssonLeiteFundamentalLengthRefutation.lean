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
    ((∃ k : (graph h).Coloring ℕ+, ∀ i, k i = c i) ∧ SameMonomial c w) ↔
    ∃! d : Fin n → palette w, d ∈ sourceColorings h w ∧ Subtype.val ∘ d = c := by
  classical
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
      rw [sourceColorings_spec]
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

private noncomputable def sourceImage {n : ℕ} (h : Fin n → Fin n) (q : ℝ) : Polynomial ℝ :=
  match n with
  | 0 => 1
  | m + 1 => psi m (chromaticCoordinates h q)

end AlexanderssonLeiteFundamentalLengthRefutation
