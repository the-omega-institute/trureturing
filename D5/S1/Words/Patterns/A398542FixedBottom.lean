/- GID: D5/S1/Words/Patterns/A398542FixedBottom
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/A398542FixedBottom
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual permutation semantics for the fixed-bottom A398542 conjecture. -/

import D5.S1.Words.Patterns.DerangementRatioNonconvergence
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

/-!
The source uses values `1,...,m+k`; here they are `Fin (m+k)`, translated
by adding one. Thus the lower cell is exactly the values strictly below `m`.
All permutations and both cells may have size zero in the semantic maps.
The polynomial conjecture itself requires a nonempty bottom.
-/

namespace D5.S1.Words.Patterns.A398542FixedBottom

open D5.S1.Words.Patterns.DerangementRatioNonconvergence

noncomputable section

/-- The pattern 132, with values shifted down by one. -/
def pattern132 : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (fun i : Fin 3 => ![0, 2, 1] i) (by decide)

/-- The pattern 213, with values shifted down by one. -/
def pattern213 : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (fun i : Fin 3 => ![1, 0, 2] i) (by decide)

/-- The pattern 1324, with values shifted down by one. -/
def pattern1324 : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (fun i : Fin 4 => ![0, 2, 1, 3] i) (by decide)

/-- The literal lower-value subsequence, in position order. -/
def lowerWord {m k : ℕ} (w : Equiv.Perm (Fin (m + k))) : List ℕ :=
  (List.ofFn fun i => (w i).val).filter (· < m)

/-- The literal upper-value subsequence, standardized by subtracting the cut. -/
def upperWord {m k : ℕ} (w : Equiv.Perm (Fin (m + k))) : List ℕ :=
  ((List.ofFn fun i => (w i).val).filter (m ≤ ·)).map (· - m)

/-- Lower positions, with the value map restricted to the lower alphabet. -/
def lowerValues {m k : ℕ} (w : Equiv.Perm (Fin (m + k))) :
    {i : Fin (m + k) // (w i).val < m} ≃ Fin m where
  toFun i := ⟨(w i).val, i.property⟩
  invFun j := ⟨w.symm (j.castAdd k), by simp⟩
  left_inv i := by apply Subtype.ext; exact w.symm_apply_apply i
  right_inv j := by apply Fin.ext; simp

/-- Upper positions, with exactly the source's subtraction by `m`. -/
def upperValues {m k : ℕ} (w : Equiv.Perm (Fin (m + k))) :
    {i : Fin (m + k) // ¬(w i).val < m} ≃ Fin k where
  toFun i := ⟨(w i).val - m, by have := (w i).isLt; have := i.property; omega⟩
  invFun j := ⟨w.symm (j.natAdd m), by simp⟩
  left_inv i := by
    apply Subtype.ext
    have hi : m ≤ (w i).val := Nat.le_of_not_gt i.property
    change w.symm ⟨m + ((w i).val - m), _⟩ = i.val
    have hv : (⟨m + ((w i).val - m), by omega⟩ : Fin (m + k)) = w i := by
      apply Fin.ext; dsimp; omega
    rw [hv, w.symm_apply_apply]
  right_inv j := by apply Fin.ext; simp

/-- Increasing enumeration of precisely the positions whose values are below the cut. -/
def lowerOrder {m k : ℕ} (w : Equiv.Perm (Fin (m + k))) :
    Fin m ≃o {i : Fin (m + k) // (w i).val < m} :=
  Fintype.orderIsoFinOfCardEq _
    ((Fintype.card_congr (lowerValues w)).trans (Fintype.card_fin m))

/-- Increasing enumeration of precisely the positions whose values are above the cut. -/
def upperOrder {m k : ℕ} (w : Equiv.Perm (Fin (m + k))) :
    Fin k ≃o {i : Fin (m + k) // ¬(w i).val < m} :=
  Fintype.orderIsoFinOfCardEq _
    ((Fintype.card_congr (upperValues w)).trans (Fintype.card_fin k))

/-- The lower permutation read in its actual position order. -/
def lowerPerm {m k : ℕ} (w : Equiv.Perm (Fin (m + k))) : Equiv.Perm (Fin m) :=
  (lowerOrder w).toEquiv.trans (lowerValues w)

/-- The upper permutation read in position order and standardized by subtracting `m`. -/
def upperPerm {m k : ℕ} (w : Equiv.Perm (Fin (m + k))) : Equiv.Perm (Fin k) :=
  (upperOrder w).toEquiv.trans (upperValues w)

/-- An interleaving of two ordered position sets. Both sets can be empty. -/
structure Shuffle (m k : ℕ) where
  positions : Fin m ⊕ Fin k ≃ Fin (m + k)
  lower_mono : StrictMono (fun i => positions (Sum.inl i))
  upper_mono : StrictMono (fun i => positions (Sum.inr i))

/-- Extract the ordered interleaving by the literal value cut. -/
def extractShuffle {m k : ℕ} (w : Equiv.Perm (Fin (m + k))) : Shuffle m k where
  positions := (Equiv.sumCongr (lowerOrder w).toEquiv (upperOrder w).toEquiv).trans
    (Equiv.sumCompl (fun i => (w i).val < m))
  lower_mono := (Subtype.strictMono_coe _).comp (lowerOrder w).strictMono
  upper_mono := (Subtype.strictMono_coe _).comp (upperOrder w).strictMono

/-- Insert both permutations into one shared ordered position set. -/
def insert {m k : ℕ} (b : Equiv.Perm (Fin m)) (u : Equiv.Perm (Fin k))
    (s : Shuffle m k) : Equiv.Perm (Fin (m + k)) :=
  s.positions.symm.trans ((Equiv.sumCongr b u).trans finSumFinEquiv)

/-- Insertion and extraction give a bijection on actual permutations, for all two cell sizes.
The order in each cell is retained; the shuffle only chooses positions. -/
def insertionEquiv (m k : ℕ) :
    ((Equiv.Perm (Fin m) × Equiv.Perm (Fin k)) × Shuffle m k) ≃
      Equiv.Perm (Fin (m + k)) where
  toFun x := insert x.1.1 x.1.2 x.2
  invFun w := ((lowerPerm w, upperPerm w), extractShuffle w)
  left_inv := by
    rintro ⟨⟨b, u⟩, s⟩
    let w := insert b u s
    have hl (i : Fin m) : w (s.positions (Sum.inl i)) = (b i).castAdd k := by
      simp [w, insert]
    have hu (i : Fin k) : w (s.positions (Sum.inr i)) = (u i).natAdd m := by
      simp [w, insert]
    have rangeL : Set.range (fun i => s.positions (Sum.inl i)) =
        {x | (w x).val < m} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩; simpa [hl] using (b i).isLt
      · intro hx
        obtain ⟨i | i, rfl⟩ := s.positions.surjective x
        · exact ⟨i, rfl⟩
        · simp [hu] at hx
    have rangeU : Set.range (fun i => s.positions (Sum.inr i)) =
        {x | ¬(w x).val < m} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩; simp [hu]
      · intro hx
        obtain ⟨i | i, rfl⟩ := s.positions.surjective x
        · exact (hx (by simpa [hl] using (b i).isLt)).elim
        · exact ⟨i, rfl⟩
    have enumL : (fun i => ((lowerOrder w) i).val) =
        (fun i => s.positions (Sum.inl i)) := by
      apply ((Subtype.strictMono_coe _).comp (lowerOrder w).strictMono).range_inj
        s.lower_mono |>.mp
      rw [rangeL]
      ext x
      constructor
      · rintro ⟨i, rfl⟩; exact ((lowerOrder w) i).property
      · intro hx
        obtain ⟨i, hi⟩ := (lowerOrder w).surjective ⟨x, hx⟩
        exact ⟨i, congrArg Subtype.val hi⟩
    have enumU : (fun i => ((upperOrder w) i).val) =
        (fun i => s.positions (Sum.inr i)) := by
      apply ((Subtype.strictMono_coe _).comp (upperOrder w).strictMono).range_inj
        s.upper_mono |>.mp
      rw [rangeU]
      ext x
      constructor
      · rintro ⟨i, rfl⟩; exact ((upperOrder w) i).property
      · intro hx
        obtain ⟨i, hi⟩ := (upperOrder w).surjective ⟨x, hx⟩
        exact ⟨i, congrArg Subtype.val hi⟩
    have hb : lowerPerm w = b := by
      apply Equiv.ext; intro i; apply Fin.ext
      change (w ((lowerOrder w i).val)).val = (b i).val
      rw [congrFun enumL i, hl]; rfl
    have hub : upperPerm w = u := by
      apply Equiv.ext; intro i; apply Fin.ext
      change (w ((upperOrder w i).val)).val - m = (u i).val
      rw [congrFun enumU i, hu]; simp
    have hs : extractShuffle w = s := by
      have he : (extractShuffle w).positions = s.positions := by
        apply Equiv.ext
        rintro (i | i)
        · exact congrFun enumL i
        · exact congrFun enumU i
      have extShuffle : ∀ a b : Shuffle m k, a.positions = b.positions → a = b := by
        rintro ⟨a, ha, ha'⟩ ⟨b, hb, hb'⟩ hab
        cases hab
        rfl
      exact extShuffle _ _ he
    exact Prod.ext (Prod.ext hb hub) hs
  right_inv w := by
    apply Equiv.ext
    intro x
    by_cases hx : (w x).val < m
    · let i := (lowerOrder w).symm ⟨x, hx⟩
      have hi : ((lowerOrder w) i).val = x := by simp [i]
      have he : (extractShuffle w).positions (Sum.inl i) = x := hi
      rw [← he]
      simp only [insert, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply,
        Sum.map_inl, finSumFinEquiv_apply_left]
      apply Fin.ext
      change (w ((lowerOrder w i).val)).val = _
      rw [hi, he]
    · let i := (upperOrder w).symm ⟨x, hx⟩
      have hi : ((upperOrder w) i).val = x := by simp [i]
      have he : (extractShuffle w).positions (Sum.inr i) = x := hi
      rw [← he]
      simp only [insert, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply,
        Sum.map_inr, finSumFinEquiv_apply_right]
      apply Fin.ext
      change m + ((w ((upperOrder w i).val)).val - m) = _
      rw [hi, he]
      omega

/-- A gap is literally the number of lower points before the given upper point. -/
def gap {m k : ℕ} (s : Shuffle m k) (j : Fin k) : Fin (m + 1) :=
  ⟨(Finset.univ.filter (fun i => s.positions (Sum.inl i) < s.positions (Sum.inr j))).card,
    Nat.lt_succ_of_le (by
      simpa using Finset.card_le_card
        (Finset.filter_subset (fun i => s.positions (Sum.inl i) < s.positions (Sum.inr j))
          Finset.univ))⟩

/-- Gaps are weakly increasing, describe the exact lower prefix, and recover upper positions.
In particular equal consecutive gaps are permitted. -/
theorem gap_spec {m k : ℕ} (s : Shuffle m k) :
    Monotone (gap s) ∧
    (∀ i j, s.positions (Sum.inl i) < s.positions (Sum.inr j) ↔ i.val < (gap s j).val) ∧
    (∀ j, (s.positions (Sum.inr j)).val = (gap s j).val + j.val) := by
  classical
  have hprefix (i : Fin m) (j : Fin k) :
      s.positions (Sum.inl i) < s.positions (Sum.inr j) ↔ i.val < (gap s j).val := by
    let l := Finset.univ.filter
      (fun i => s.positions (Sum.inl i) < s.positions (Sum.inr j))
    change _ ↔ i.val < l.card
    constructor
    · intro hij
      have hsub : Finset.Iic i ⊆ l := by
        intro a ha
        simp only [Finset.mem_Iic] at ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          lt_of_le_of_lt (s.lower_mono.monotone ha) hij⟩
      have hcard := Finset.card_le_card hsub
      simpa using hcard
    · intro hic
      by_contra hij
      have hsub : l ⊆ Finset.Iio i := by
        intro a ha
        have ha' := (Finset.mem_filter.mp ha).2
        apply Finset.mem_Iio.mpr
        by_contra hai
        have := s.lower_mono.monotone (le_of_not_gt hai)
        exact hij (lt_of_le_of_lt this ha')
      have hcard := Finset.card_le_card hsub
      have : l.card ≤ i.val := by simpa using hcard
      omega
  refine ⟨?_, hprefix, ?_⟩
  · intro i j hij
    change (Finset.univ.filter (fun a => s.positions (Sum.inl a) < s.positions (Sum.inr i))).card ≤
      (Finset.univ.filter (fun a => s.positions (Sum.inl a) < s.positions (Sum.inr j))).card
    apply Finset.card_le_card
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_of_lt_of_le (Finset.mem_filter.mp ha).2 (s.upper_mono.monotone hij)⟩
  · intro j
    let l := Finset.univ.filter
      (fun i => s.positions (Sum.inl i) < s.positions (Sum.inr j))
    let lo := l.image (fun i => s.positions (Sum.inl i))
    let up := (Finset.Iio j).image (fun i => s.positions (Sum.inr i))
    have hd : Disjoint lo up := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hy
      cases s.positions.injective he
    have he : lo ∪ up = Finset.Iio (s.positions (Sum.inr j)) := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_Iio.mpr (Finset.mem_filter.mp hi).2
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_Iio.mpr (s.upper_mono (Finset.mem_Iio.mp hi))
      · intro hx
        have hx' := Finset.mem_Iio.mp hx
        obtain ⟨i | i, rfl⟩ := s.positions.surjective x
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr
            ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩, rfl⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨i, Finset.mem_Iio.mpr (s.upper_mono.lt_iff_lt.mp hx'), rfl⟩)
    have hc := congrArg Finset.card he
    rw [Finset.card_union_of_disjoint hd] at hc
    dsimp [lo, up] at hc
    rw [Finset.card_image_of_injective _ s.lower_mono.injective,
      Finset.card_image_of_injective _ s.upper_mono.injective] at hc
    simpa [gap, l] using hc.symm

/-- Insert arbitrary weakly increasing gap labels; upper point `i` occupies `gap(i)+i`.
The complementary positions hold the one shared bottom, in its original order. -/
def shuffleOfGaps {m k : ℕ} (g : Fin k → Fin (m + 1)) (hg : Monotone g) : Shuffle m k := by
  classical
  let hi : Fin k ↪o Fin (m + k) := OrderEmbedding.ofStrictMono
    (fun i => ⟨(g i).val + i.val, by have := (g i).isLt; have := i.isLt; omega⟩)
    (by
      intro i j hij
      have hgij := hg (le_of_lt hij)
      change (g i).val + i.val < (g j).val + j.val
      omega)
  let u := Finset.univ.image hi
  have huc : u.card = k := by simp [u, Finset.card_image_of_injective, hi.injective]
  have hlc : uᶜ.card = m := by simp [Finset.card_compl, huc]
  let lo := uᶜ.orderEmbOfFin hlc
  have hlo (i : Fin m) : lo i ∉ u := by
    exact Finset.mem_compl.mp (Finset.orderEmbOfFin_mem _ _ i)
  have hhi (j : Fin k) : hi j ∈ u := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  let e : Fin m ⊕ Fin k ≃ Fin (m + k) := Equiv.ofBijective (Sum.elim lo hi) (by
    constructor
    · rintro (i | i) (j | j) he
      · exact congrArg Sum.inl (lo.injective he)
      · change lo i = hi j at he
        exact (hlo i (he.symm ▸ hhi j)).elim
      · change hi i = lo j at he
        exact (hlo j (he ▸ hhi i)).elim
      · exact congrArg Sum.inr (hi.injective he)
    · intro x
      by_cases hx : x ∈ u
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨Sum.inr j, rfl⟩
      · obtain ⟨i, he⟩ := (uᶜ.orderIsoOfFin hlc).surjective ⟨x, Finset.mem_compl.mpr hx⟩
        exact ⟨Sum.inl i, congrArg Subtype.val he⟩)
  exact ⟨e, lo.strictMono, hi.strictMono⟩

/-- Ordered interleavings are exactly weakly increasing gap labels. -/
def gapEquiv (m k : ℕ) : Shuffle m k ≃ {g : Fin k → Fin (m + 1) // Monotone g} where
  toFun s := ⟨gap s, (gap_spec s).1⟩
  invFun g := shuffleOfGaps g.val g.property
  right_inv g := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    have h := (gap_spec (shuffleOfGaps g.val g.property)).2.2 j
    have hp : ((shuffleOfGaps g.val g.property).positions (Sum.inr j)).val =
        (g.val j).val + j.val := rfl
    change (gap (shuffleOfGaps g.val g.property) j).val = (g.val j).val
    omega
  left_inv s := by
    let t := shuffleOfGaps (gap s) (gap_spec s).1
    have hu (j : Fin k) : t.positions (Sum.inr j) = s.positions (Sum.inr j) := by
      apply Fin.ext
      exact ((gap_spec s).2.2 j).symm
    have hr (a : Shuffle m k) :
        Set.range (fun i => a.positions (Sum.inl i)) =
          (Set.range (fun i => a.positions (Sum.inr i)))ᶜ := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩ ⟨j, he⟩
        cases a.positions.injective he
      · intro hx
        obtain ⟨i | j, rfl⟩ := a.positions.surjective x
        · exact ⟨i, rfl⟩
        · exact (hx ⟨j, rfl⟩).elim
    have hl : (fun i => t.positions (Sum.inl i)) =
        (fun i => s.positions (Sum.inl i)) := by
      apply (t.lower_mono.range_inj s.lower_mono).mp
      rw [hr t, hr s]
      congr 2
      funext j
      exact hu j
    have he : t.positions = s.positions := by
      apply Equiv.ext
      rintro (i | j)
      · exact congrFun hl i
      · exact hu j
    have extShuffle : ∀ a b : Shuffle m k, a.positions = b.positions → a = b := by
      rintro ⟨a, ha, ha'⟩ ⟨b, hb, hb'⟩ hab
      cases hab
      rfl
    exact extShuffle _ _ he


/-- Minimum lower value before gap `g`; the empty prefix has sentinel value `m`. -/
def prefixMin {m : ℕ} (b : Equiv.Perm (Fin m)) (g : ℕ) : ℕ :=
  (Insert.insert m ((Finset.univ.filter (fun i : Fin m => i.val < g)).image
    (fun i => (b i).val))).min' (Finset.insert_nonempty _ _)

/-- The first later bottom endpoint above the prefix minimum, in the source's
one-based endpoint convention. The absent endpoint has sentinel `m+2`. -/
def dead {m : ℕ} (b : Equiv.Perm (Fin m)) (g : ℕ) : ℕ :=
  (Insert.insert (m + 2) ((Finset.univ.filter
    (fun j : Fin m => g ≤ j.val ∧ prefixMin b g < (b j).val)).image
      (fun j => j.val + 1))).min' (Finset.insert_nonempty _ _)

/-- Under the two cell-avoidance conditions, the only possible 1324 consists of
two interleaved ascents, one in each cell. This is a statement about actual positions. -/
theorem contains1324_iff_mixed {m k : ℕ} (w : Equiv.Perm (Fin (m + k)))
    (hb : ¬Contains pattern132 (lowerPerm w))
    (hu : ¬Contains pattern213 (upperPerm w)) :
    Contains pattern1324 w ↔
      ∃ a x c y : Fin (m + k), a < x ∧ x < c ∧ c < y ∧
        (w a).val < m ∧ (w c).val < m ∧ m ≤ (w x).val ∧ m ≤ (w y).val ∧
        w a < w c ∧ w x < w y := by
  have mk132 {n : ℕ} (v : Equiv.Perm (Fin n)) (a b c : Fin n)
      (hab : a < b) (hbc : b < c) (hacv : v a < v c) (hcbv : v c < v b) :
      Contains pattern132 v := by
    refine ⟨OrderEmbedding.ofStrictMono ![a, b, c] ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
          Fin.reduceFinMk, Matrix.cons_val] <;> omega
    · intro i j
      change pattern132 i < pattern132 j ↔ v (![a, b, c] i) < v (![a, b, c] j)
      fin_cases i <;> fin_cases j <;> simp [pattern132] <;> omega
  have mk213 {n : ℕ} (v : Equiv.Perm (Fin n)) (a b c : Fin n)
      (hab : a < b) (hbc : b < c) (hbav : v b < v a) (hacv : v a < v c) :
      Contains pattern213 v := by
    refine ⟨OrderEmbedding.ofStrictMono ![a, b, c] ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
          Fin.reduceFinMk, Matrix.cons_val] <;> omega
    · intro i j
      change pattern213 i < pattern213 j ↔ v (![a, b, c] i) < v (![a, b, c] j)
      fin_cases i <;> fin_cases j <;> simp [pattern213] <;> omega
  have noLower (a b c : Fin (m + k)) (ha : (w a).val < m)
      (hb' : (w b).val < m) (hc : (w c).val < m)
      (hab : a < b) (hbc : b < c) (hacv : w a < w c) (hcbv : w c < w b) : False := by
    apply hb
    apply mk132 (lowerPerm w) ((lowerOrder w).symm ⟨a, ha⟩)
      ((lowerOrder w).symm ⟨b, hb'⟩) ((lowerOrder w).symm ⟨c, hc⟩)
    · exact (lowerOrder w).symm.strictMono hab
    · exact (lowerOrder w).symm.strictMono hbc
    · change (w ((lowerOrder w) ((lowerOrder w).symm ⟨a, ha⟩))).val <
        (w ((lowerOrder w) ((lowerOrder w).symm ⟨c, hc⟩))).val
      rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
      exact hacv
    · change (w ((lowerOrder w) ((lowerOrder w).symm ⟨c, hc⟩))).val <
        (w ((lowerOrder w) ((lowerOrder w).symm ⟨b, hb'⟩))).val
      rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
      exact hcbv
  have noUpper (a b c : Fin (m + k)) (ha : ¬(w a).val < m)
      (hb' : ¬(w b).val < m) (hc : ¬(w c).val < m)
      (hab : a < b) (hbc : b < c) (hbav : w b < w a) (hacv : w a < w c) : False := by
    apply hu
    apply mk213 (upperPerm w) ((upperOrder w).symm ⟨a, ha⟩)
      ((upperOrder w).symm ⟨b, hb'⟩) ((upperOrder w).symm ⟨c, hc⟩)
    · exact (upperOrder w).symm.strictMono hab
    · exact (upperOrder w).symm.strictMono hbc
    · change (w ((upperOrder w) ((upperOrder w).symm ⟨b, hb'⟩))).val - m <
        (w ((upperOrder w) ((upperOrder w).symm ⟨a, ha⟩))).val - m
      rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
      change (w b).val - m < (w a).val - m
      omega
    · change (w ((upperOrder w) ((upperOrder w).symm ⟨a, ha⟩))).val - m <
        (w ((upperOrder w) ((upperOrder w).symm ⟨c, hc⟩))).val - m
      rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
      change (w a).val - m < (w c).val - m
      omega
  constructor
  · rintro ⟨f, hf⟩
    have h01 : f 0 < f 1 := f.strictMono (by decide)
    have h12 : f 1 < f 2 := f.strictMono (by decide)
    have h23 : f 2 < f 3 := f.strictMono (by decide)
    have v02 : w (f 0) < w (f 2) := (hf 0 2).mp (by decide)
    have v21 : w (f 2) < w (f 1) := (hf 2 1).mp (by decide)
    have v13 : w (f 1) < w (f 3) := (hf 1 3).mp (by decide)
    by_cases hlow : (w (f 1)).val < m
    · exact (noLower (f 0) (f 1) (f 2) (by omega) hlow (by omega)
        h01 h12 v02 v21).elim
    · by_cases hhigh : (w (f 2)).val < m
      · exact ⟨f 0, f 1, f 2, f 3, h01, h12, h23, by omega, hhigh,
          by omega, by omega, v02, v13⟩
      · exact (noUpper (f 1) (f 2) (f 3) hlow hhigh (by omega)
          h12 h23 v21 v13).elim
  · rintro ⟨a, x, c, y, hax, hxc, hcy, ha, hc, hx, hy, hacv, hxyv⟩
    have hcxv : w c < w x := by omega
    refine ⟨OrderEmbedding.ofStrictMono ![a, x, c, y] ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
          Fin.reduceFinMk, Matrix.cons_val] <;> omega
    · intro i j
      change pattern1324 i < pattern1324 j ↔
        w (![a, x, c, y] i) < w (![a, x, c, y] j)
      fin_cases i <;> fin_cases j <;> simp [pattern1324] <;> omega

/-- The exact cutoff criterion, with its strict guard and empty-prefix sentinel.
It uses the same complete bottom in every gap. -/
theorem gap_criterion {m k : ℕ} (w : Equiv.Perm (Fin (m + k)))
    (hb : ¬Contains pattern132 (lowerPerm w))
    (hu : ¬Contains pattern213 (upperPerm w)) :
    dead (lowerPerm w) 0 = m + 2 ∧
    (∀ g ≤ m, g < dead (lowerPerm w) g) ∧
    (¬Contains pattern1324 w ↔ ∀ i j : Fin k, i < j → upperPerm w i < upperPerm w j →
      (gap (extractShuffle w) j).val < dead (lowerPerm w) (gap (extractShuffle w) i).val) := by
  classical
  let b := lowerPerm w
  let u := upperPerm w
  let s := extractShuffle w
  have pm (g : ℕ) (j : Fin m) : prefixMin b g < (b j).val ↔
      ∃ i : Fin m, i.val < g ∧ b i < b j := by
    constructor
    · intro h
      have hm := Finset.min'_mem
        (Insert.insert m ((Finset.univ.filter (fun i : Fin m => i.val < g)).image
          (fun i => (b i).val))) (Finset.insert_nonempty _ _)
      change prefixMin b g ∈ _ at hm
      rcases Finset.mem_insert.mp hm with hm | hm
      · have := (b j).isLt; omega
      · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
        exact ⟨i, (Finset.mem_filter.mp hi).2, by change (b i).val < (b j).val; omega⟩
    · rintro ⟨i, hi, hij⟩
      have hle : prefixMin b g ≤ (b i).val := Finset.min'_le _ _
        (Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩))
      exact lt_of_le_of_lt hle hij
  have dl (g t : ℕ) (ht : t ≤ m) : dead b g ≤ t ↔
      ∃ a c : Fin m, a.val < g ∧ g ≤ c.val ∧ c.val < t ∧ b a < b c := by
    constructor
    · intro h
      have hm := Finset.min'_mem
        (Insert.insert (m + 2) ((Finset.univ.filter
          (fun j : Fin m => g ≤ j.val ∧ prefixMin b g < (b j).val)).image
            (fun j => j.val + 1))) (Finset.insert_nonempty _ _)
      change dead b g ∈ _ at hm
      rcases Finset.mem_insert.mp hm with hm | hm
      · omega
      · obtain ⟨c, hc, he⟩ := Finset.mem_image.mp hm
        obtain ⟨hgc, hpc⟩ := (Finset.mem_filter.mp hc).2
        obtain ⟨a, ha, hac⟩ := (pm g c).mp hpc
        exact ⟨a, c, ha, hgc, by omega, hac⟩
    · rintro ⟨a, c, ha, hgc, hct, hac⟩
      have hle : dead b g ≤ c.val + 1 := Finset.min'_le _ _
        (Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgc,
            (pm g c).mpr ⟨a, ha, hac⟩⟩, rfl⟩))
      omega
  have hl (a : Fin m) : (w (s.positions (Sum.inl a))).val = (b a).val := rfl
  have hh (i : Fin k) : (w (s.positions (Sum.inr i))).val = m + (u i).val := by
    have hnot := (upperOrder w i).property
    change (w ((upperOrder w i).val)).val = m + ((w ((upperOrder w i).val)).val - m)
    omega
  have cross (i : Fin k) (c : Fin m) :
      s.positions (Sum.inr i) < s.positions (Sum.inl c) ↔ (gap s i).val ≤ c.val := by
    have hp := (gap_spec s).2.1 c i
    have hn : s.positions (Sum.inr i) ≠ s.positions (Sum.inl c) := by
      intro h; cases s.positions.injective h
    omega
  refine ⟨?_, ?_, ?_⟩
  · have hnone : (Finset.univ.filter
        (fun j : Fin m => 0 ≤ j.val ∧ prefixMin b 0 < (b j).val)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro j hj h
      obtain ⟨i, hi, _⟩ := (pm 0 j).mp h.2
      omega
    change dead b 0 = m + 2
    unfold dead
    simp only [hnone, Finset.image_empty]
    simp
  · intro g hg
    change g < dead b g
    unfold dead
    rw [Finset.lt_min'_iff]
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · omega
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
      have := (Finset.mem_filter.mp hj).2.1
      omega
  · constructor
    · intro hw i j hij huv
      by_contra hbad
      change ¬(gap s j).val < dead b (gap s i).val at hbad
      obtain ⟨a, c, hag, hgc, hcj, hac⟩ :=
        (dl (gap s i).val (gap s j).val (Nat.le_of_lt_succ (gap s j).isLt)).mp
          (Nat.le_of_not_gt hbad)
      apply hw
      apply (contains1324_iff_mixed w hb hu).mpr
      refine ⟨s.positions (Sum.inl a), s.positions (Sum.inr i),
        s.positions (Sum.inl c), s.positions (Sum.inr j),
        ((gap_spec s).2.1 a i).mpr hag, (cross i c).mpr hgc,
        ((gap_spec s).2.1 c j).mpr hcj, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hl]; exact (b a).isLt
      · rw [hl]; exact (b c).isLt
      · rw [hh]; omega
      · rw [hh]; omega
      · change (w _).val < (w _).val; rw [hl, hl]; exact hac
      · change (w _).val < (w _).val; rw [hh, hh]; exact Nat.add_lt_add_left huv m
    · intro hs hw
      obtain ⟨a, x, c, y, hax, hxc, hcy, ha, hc, hx, hy, hac, hxy⟩ :=
        (contains1324_iff_mixed w hb hu).mp hw
      let a' := (lowerOrder w).symm ⟨a, ha⟩
      let c' := (lowerOrder w).symm ⟨c, hc⟩
      let i := (upperOrder w).symm ⟨x, by omega⟩
      let j := (upperOrder w).symm ⟨y, by omega⟩
      have ea : s.positions (Sum.inl a') = a := by change ((lowerOrder w) a').val = a; simp [a']
      have ec : s.positions (Sum.inl c') = c := by change ((lowerOrder w) c').val = c; simp [c']
      have ex : s.positions (Sum.inr i) = x := by change ((upperOrder w) i).val = x; simp [i]
      have ey : s.positions (Sum.inr j) = y := by change ((upperOrder w) j).val = y; simp [j]
      have hij : i < j := s.upper_mono.lt_iff_lt.mp (by rw [ex, ey]; exact lt_trans hxc hcy)
      have huv : u i < u j := by
        have hxi := hh i; have hyj := hh j
        rw [ex] at hxi; rw [ey] at hyj
        change (u i).val < (u j).val
        omega
      have hle : dead b (gap s i).val ≤ (gap s j).val :=
        (dl _ _ (Nat.le_of_lt_succ (gap s j).isLt)).mpr ⟨a', c',
          ((gap_spec s).2.1 a' i).mp (by rw [ea, ex]; exact hax),
          (cross i c').mp (by rw [ex, ec]; exact hxc),
          ((gap_spec s).2.1 c' j).mp (by rw [ec, ey]; exact hcy), by
            have hal := hl a'; have hcl := hl c'
            rw [ea] at hal; rw [ec] at hcl
            change (b a').val < (b c').val
            omega⟩
      exact (Nat.not_lt_of_ge hle) (hs i j hij huv)

/-- The source class counts actual permutations, with no recursive count definition. -/
def Actual {m : ℕ} (b : Equiv.Perm (Fin m)) (k : ℕ) :=
  {w : Equiv.Perm (Fin (m + k)) //
    lowerWord w = List.ofFn (fun i => (b i).val) ∧
    ¬Contains pattern1324 w ∧ ¬Contains pattern213 (upperPerm w)}

/-- A fixed-bottom configuration consists of an upper permutation and monotone gaps,
subject to the exact mixed-pattern cutoff. -/
def Configuration {m : ℕ} (b : Equiv.Perm (Fin m)) (k : ℕ) :=
  {c : Equiv.Perm (Fin k) × {g : Fin k → Fin (m + 1) // Monotone g} //
    ¬Contains pattern213 c.1 ∧ ∀ i j, i < j → c.1 i < c.1 j →
      (c.2.val j).val < dead b (c.2.val i).val}

/-- The actual source class and the fixed-bottom gap configurations are equivalent.
Both composites are identities, including at upper size zero. -/
def actualEquiv {m : ℕ} (b : Equiv.Perm (Fin m))
    (hb : ¬Contains pattern132 b) (k : ℕ) : Actual b k ≃ Configuration b k := by
  have cell_words {m k : ℕ} (w : Equiv.Perm (Fin (m + k))) :
      lowerWord w = List.ofFn (fun i => (lowerPerm w i).val) ∧
      upperWord w = List.ofFn (fun i => (upperPerm w i).val) := by
    have filtered {n r : ℕ} (p : Fin n → Prop) [DecidablePred p]
        (e : Fin r ≃o {i // p i}) :
        (List.finRange n).filter (fun i => decide (p i)) =
          List.ofFn (fun i => (e i).val) := by
      apply List.SortedLT.eq_of_mem_iff
      · exact ((List.sortedLT_finRange n).pairwise.filter _).sortedLT
      · exact ((Subtype.strictMono_coe _).comp e.strictMono).sortedLT_ofFn
      · intro x
        simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
          List.mem_ofFn]
        constructor
        · intro hx
          obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
          exact ⟨i, congrArg Subtype.val hi⟩
        · rintro ⟨i, rfl⟩; exact (e i).property
    constructor
    · unfold lowerWord
      rw [List.ofFn_eq_map, List.filter_map]
      change ((List.finRange (m + k)).filter (fun i => decide ((w i).val < m))).map
        (fun i => (w i).val) = _
      rw [filtered _ (lowerOrder w), List.map_ofFn]
      rfl
    · unfold upperWord
      rw [List.ofFn_eq_map, List.filter_map]
      have hp : (fun i : Fin (m + k) => decide (m ≤ (w i).val)) =
          (fun i => decide (¬(w i).val < m)) := by ext i; simp
      change (((List.finRange (m + k)).filter (fun i => decide (m ≤ (w i).val))).map
        (fun i => (w i).val)).map (· - m) = _
      rw [hp, filtered _ (upperOrder w), List.map_ofFn, List.map_ofFn]
      rfl
  have lower_eq (w : Equiv.Perm (Fin (m + k)))
      (hw : lowerWord w = List.ofFn (fun i => (b i).val)) : lowerPerm w = b := by
    have hl := (cell_words w).1.symm.trans hw
    apply Equiv.ext
    intro i
    apply Fin.ext
    have he := congrArg (fun l : List ℕ => l[i.val]?) hl
    simpa using he
  let encode : Actual b k → Configuration b k := fun a => by
    have hl := lower_eq a.val a.property.1
    refine ⟨(upperPerm a.val, (gapEquiv m k) (extractShuffle a.val)), a.property.2.2, ?_⟩
    have h := (gap_criterion a.val (hl.symm ▸ hb) a.property.2.2).2.2.mp a.property.2.1
    change ∀ i j : Fin k, i < j → upperPerm a.val i < upperPerm a.val j →
      (gap (extractShuffle a.val) j).val < dead b (gap (extractShuffle a.val) i).val
    simpa only [hl] using h
  let decode : Configuration b k → Actual b k := fun c => by
    let s := (gapEquiv m k).symm c.val.2
    let w := insert b c.val.1 s
    have he := (insertionEquiv m k).symm_apply_apply ((b, c.val.1), s)
    have hl : lowerPerm w = b := congrArg (fun x => x.1.1) he
    have hu : upperPerm w = c.val.1 := congrArg (fun x => x.1.2) he
    have hs : extractShuffle w = s := congrArg Prod.snd he
    have hg : gap s = c.val.2.val :=
      congrArg Subtype.val ((gapEquiv m k).apply_symm_apply c.val.2)
    have hav : ¬Contains pattern213 (upperPerm w) := hu.symm ▸ c.property.1
    refine ⟨w, (cell_words w).1.trans ?_, ?_, hav⟩
    · rw [hl]
    · apply (gap_criterion w (hl.symm ▸ hb) hav).2.2.mpr
      simpa only [hl, hu, hs, hg] using c.property.2
  refine ⟨encode, decode, ?_, ?_⟩
  · intro a
    apply Subtype.ext
    change insert b (upperPerm a.val)
      ((gapEquiv m k).symm ((gapEquiv m k) (extractShuffle a.val))) = a.val
    rw [(gapEquiv m k).symm_apply_apply]
    have h := (insertionEquiv m k).apply_symm_apply a.val
    change insert (lowerPerm a.val) (upperPerm a.val) (extractShuffle a.val) = a.val at h
    rwa [lower_eq a.val a.property.1] at h
  · intro c
    apply Subtype.ext
    let s := (gapEquiv m k).symm c.val.2
    let w := insert b c.val.1 s
    have he := (insertionEquiv m k).symm_apply_apply ((b, c.val.1), s)
    have hu : upperPerm w = c.val.1 := congrArg (fun x => x.1.2) he
    have hs : extractShuffle w = s := congrArg Prod.snd he
    change (upperPerm w, (gapEquiv m k) (extractShuffle w)) = c.val
    apply Prod.ext hu
    rw [hs]
    exact (gapEquiv m k).apply_symm_apply c.val.2

/-- The exact fixed-bottom completion count, including an empty upper cell. -/
def count {m : ℕ} (b : Equiv.Perm (Fin m)) (k : ℕ) : ℕ :=
  Nat.card (Actual b k)

end

end D5.S1.Words.Patterns.A398542FixedBottom
