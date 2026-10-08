/- GID: D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/QubitSupportCoefficientForms
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Composition]
   utility: none
   digest: Ordered complementary two-row supports have one form per composition. -/

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic
import D5.S0.Computability.DescriptionComplexity.TimeBoundedTwoPointPrice

set_option autoImplicit false

open D5.S0.Computability.DescriptionComplexity.TimeBoundedTwoPointPrice (BitWord)

namespace D5.S3.Quantum.Entanglement.QubitSupportCoefficientForms

/-- A string has no nonzero bit outside the given qubit set. -/
def Supported {n : ℕ} (P : Finset (Fin n)) (x : BitWord n) : Prop :=
  ∀ i : Fin n, i ∉ P → x.val.testBit i.val = false

/-- The complementary row factor and increasing column factor, with no fixed qubit. -/
structure Config (n p : ℕ) where
  P : Finset (Fin n)
  nonempty : P.Nonempty
  x : BitWord n
  y : BitWord n
  x_supported : Supported P x
  y_bits : ∀ i : Fin n, y.val.testBit i.val =
    if i ∈ P then !(x.val.testBit i.val) else false
  first_zero : ∀ q ∈ P, (∀ i ∈ P, i ≤ q) → x.val.testBit q.val = false
  sigma : Fin p → BitWord n
  increasing : StrictMono sigma
  sigma_supported : ∀ j, Supported Pᶜ (sigma j)
  varying : ∀ i : Fin n, i ∉ P →
    (∃ j, (sigma j).val.testBit i.val = false) ∧
    (∃ j, (sigma j).val.testBit i.val = true)

/-- The occupied basis string at a row and column. The supports are disjoint. -/
def occupied {n p : ℕ} (c : Config n p) (r : Fin 2) (j : Fin p) : ℕ :=
  (if r = 0 then c.x.val else c.y.val) + (c.sigma j).val

/-- The index of an occupied basis string in increasing binary order, starting at zero. -/
noncomputable def form {n p : ℕ} (c : Config n p) :
    Fin 2 → Fin p → Fin (2 * p) := fun r j =>
  ⟨(Finset.univ.filter fun z : Fin 2 × Fin p =>
      occupied c z.1 z.2 < occupied c r j).card, by
    have h := Finset.card_lt_card (Finset.filter_ssubset.mpr
      (show ∃ z ∈ (Finset.univ : Finset (Fin 2 × Fin p)),
        ¬ occupied c z.1 z.2 < occupied c r j from
        ⟨(r, j), Finset.mem_univ _, lt_irrefl _⟩))
    simpa using h⟩

/-- All coefficient-index matrices obtained at an arbitrary number of qubits. -/
def forms (p : ℕ) : Set (Fin 2 → Fin p → Fin (2 * p)) :=
  {f | ∃ n, ∃ c : Config n p, form c = f}

/-- The coefficient-index matrices obtained at a fixed number of qubits. -/
def formsAt (n p : ℕ) : Set (Fin 2 → Fin p → Fin (2 * p)) :=
  {f | ∃ c : Config n p, form c = f}

/-- A composition contributes a top run and a bottom run of each part's size. -/
def formOf {p : ℕ} (d : Composition p) : Fin 2 → Fin p → Fin (2 * p) :=
  fun r j => ⟨j.val + d.sizeUpTo ((d.index j).val + r.val), by
    have := d.sizeUpTo_le ((d.index j).val + r.val)
    omega⟩

private theorem index_lt_iff {p : ℕ} (d : Composition p) (i : Fin p)
    (b : Fin d.length) :
    d.index i < b ↔ i.val < d.sizeUpTo b.val := by
  constructor
  · intro h
    have hi := d.lt_sizeUpTo_index_succ i
    change i.val < d.sizeUpTo ((d.index i).val + 1) at hi
    exact hi.trans_le
      (d.monotone_sizeUpTo (by change (d.index i).val < b.val at h; omega))
  · intro h
    by_contra hn
    have hb : b.val ≤ (d.index i).val := by simpa using not_lt.mp hn
    have := (d.monotone_sizeUpTo hb).trans (d.sizeUpTo_index_le i)
    omega

private theorem index_le_iff {p : ℕ} (d : Composition p) (i : Fin p)
    (b : Fin d.length) :
    d.index i ≤ b ↔ i.val < d.sizeUpTo (b.val + 1) := by
  constructor
  · intro h
    have hi := d.lt_sizeUpTo_index_succ i
    change i.val < d.sizeUpTo ((d.index i).val + 1) at hi
    exact hi.trans_le
      (d.monotone_sizeUpTo (by change (d.index i).val ≤ b.val at h; omega))
  · intro h
    by_contra hn
    have hb : b.val + 1 ≤ (d.index i).val := by
      change ¬ (d.index i).val ≤ b.val at hn
      omega
    have := (d.monotone_sizeUpTo hb).trans (d.sizeUpTo_index_le i)
    omega

private theorem boundary_iff {p : ℕ} (d : Composition p) (j : Fin (p + 1)) :
    j ∈ d.boundaries ↔ j.val = p ∨
      ∃ i : Fin p, i.val = j.val ∧ d.sizeUpTo (d.index i).val = i.val := by
  constructor
  · intro hj
    obtain ⟨b, hb, heq⟩ :=
      d.toCompositionAsSet.mem_boundaries_iff_exists_blocks_sum_take_eq.mp hj
    rw [Composition.toCompositionAsSet_blocks] at heq
    change d.sizeUpTo b = j.val at heq
    have hbl : b ≤ d.length := by
      simpa only [Composition.toCompositionAsSet_boundaries,
        d.card_boundaries_eq_succ_length, Nat.lt_succ_iff] using hb
    by_cases hlast : b = d.length
    · left
      simpa [hlast] using heq.symm
    · right
      let bi : Fin d.length := ⟨b, by omega⟩
      let t : Fin (d.blocksFun bi) := ⟨0, d.one_le_blocksFun bi⟩
      refine ⟨d.embedding bi t, ?_, ?_⟩
      · simpa [t, bi] using heq
      · simp [d.index_embedding, t]
  · rintro (h | ⟨i, hi, heq⟩)
    · have hj : j = Fin.last p := Fin.ext h
      rw [hj]
      exact d.toCompositionAsSet.getLast_mem
    · apply d.toCompositionAsSet.mem_boundaries_iff_exists_blocks_sum_take_eq.mpr
      refine ⟨(d.index i).val, ?_, ?_⟩
      · rw [Composition.toCompositionAsSet_boundaries, d.card_boundaries_eq_succ_length]
        omega
      · rw [Composition.toCompositionAsSet_blocks]
        change d.sizeUpTo (d.index i).val = j.val
        omega

/-- The top-row indices recover all the boundaries of the composition. -/
theorem formOf_injective (p : ℕ) : Function.Injective (@formOf p) := by
  intro c d h
  apply (compositionEquiv p).injective
  apply CompositionAsSet.ext
  ext j
  change j ∈ c.boundaries ↔ j ∈ d.boundaries
  rw [boundary_iff, boundary_iff]
  have hs (i : Fin p) : c.sizeUpTo (c.index i).val = d.sizeUpTo (d.index i).val := by
    have hv := congrArg Fin.val (congrFun (congrFun h 0) i)
    change i.val + c.sizeUpTo ((c.index i).val + 0) =
      i.val + d.sizeUpTo ((d.index i).val + 0) at hv
    simpa using hv
  simp_rw [hs]

private theorem disjoint_add_eq_or {n a b : ℕ}
    (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (h : ∀ i, a.testBit i = false ∨ b.testBit i = false) :
    a + b = a ||| b := by
  have hand : a &&& b = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rcases h i with h | h <;> simp [h]
  let x := BitVec.ofNat n a
  let y := BitVec.ofNat n b
  have hxy : x &&& y = 0 := by
    simp [x, y, ← BitVec.ofNat_and, hand]
  have heq := congrArg BitVec.toNat (BitVec.add_eq_or_of_and_eq_zero x y hxy)
  rw [BitVec.toNat_add_of_and_eq_zero hxy, BitVec.toNat_or] at heq
  simpa [x, y, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using heq

private theorem occupied_or {n p : ℕ} (c : Config n p) (r : Fin 2) (j : Fin p) :
    occupied c r j = (if r = 0 then c.x.val else c.y.val) ||| (c.sigma j).val := by
  apply disjoint_add_eq_or (n := n)
  · split_ifs <;> exact Fin.isLt _
  · exact Fin.isLt _
  · intro k
    by_cases hk : k < n
    · let i : Fin n := ⟨k, hk⟩
      by_cases hi : i ∈ c.P
      · right
        exact c.sigma_supported j i (by simpa)
      · left
        split_ifs
        · exact c.x_supported i hi
        · simpa [hi] using c.y_bits i
    · left
      apply Nat.testBit_eq_false_of_lt
      apply lt_of_lt_of_le (show (if r = 0 then c.x.val else c.y.val) < 2 ^ n by
        split_ifs <;> exact Fin.isLt _)
      exact Nat.pow_le_pow_right (by omega) (by omega)

private theorem row_bound {n p : ℕ} (c : Config n p) (q : Fin n)
    (hmax : ∀ i ∈ c.P, i ≤ q) (r : Fin 2) :
    (if r = 0 then c.x.val else c.y.val) < 2 ^ (q.val + 1) := by
  apply Nat.lt_pow_two_of_testBit
  intro k hk
  by_cases hkn : k < n
  · let i : Fin n := ⟨k, hkn⟩
    have hi : i ∉ c.P := by
      intro hi
      have := hmax i hi
      have : k ≤ q.val := this
      omega
    split_ifs
    · exact c.x_supported i hi
    · simpa [hi] using c.y_bits i
  · apply Nat.testBit_eq_false_of_lt
    apply lt_of_lt_of_le (show (if r = 0 then c.x.val else c.y.val) < 2 ^ n by
      split_ifs <;> exact Fin.isLt _)
    exact Nat.pow_le_pow_right (by omega) (by omega)

private theorem occupied_prefix {n p : ℕ} (c : Config n p) (q : Fin n)
    (hmax : ∀ i ∈ c.P, i ≤ q) (r : Fin 2) (j : Fin p) :
    occupied c r j / 2 ^ (q.val + 1) = (c.sigma j).val / 2 ^ (q.val + 1) := by
  rw [occupied_or, Nat.or_div_two_pow, Nat.div_eq_of_lt (row_bound c q hmax r)]
  simp

private theorem occupied_same_prefix {n p : ℕ} (c : Config n p) (q : Fin n)
    (hq : q ∈ c.P) (hmax : ∀ i ∈ c.P, i ≤ q) (i j : Fin p)
    (h : (c.sigma i).val / 2 ^ (q.val + 1) =
      (c.sigma j).val / 2 ^ (q.val + 1)) :
    occupied c 0 i < occupied c 1 j := by
  have hz : (occupied c 0 i).testBit q.val = false := by
    rw [occupied_or, Nat.testBit_lor]
    have hs := c.sigma_supported i q (by simpa)
    simp [c.first_zero q hq hmax, hs]
  have ho : (occupied c 1 j).testBit q.val = true := by
    rw [occupied_or, Nat.testBit_lor]
    have hs := c.sigma_supported j q (by simpa)
    have hy := c.y_bits q
    simp [hq, c.first_zero q hq hmax] at hy
    simp [hy, hs]
  apply Nat.lt_of_testBit q.val hz ho
  intro k hk
  have hd : occupied c 0 i / 2 ^ (q.val + 1) =
      occupied c 1 j / 2 ^ (q.val + 1) := by
    rw [occupied_prefix c q hmax, occupied_prefix c q hmax, h]
  have hb := congrArg (fun x : ℕ => x.testBit (k - (q.val + 1))) hd
  have hk' : k - (q.val + 1) + (q.val + 1) = k := Nat.sub_add_cancel (by omega)
  simpa only [Nat.testBit_div_two_pow, hk'] using hb

private theorem prefix_monotone {n p : ℕ} (c : Config n p) (q : Fin n) :
    Monotone (fun j : Fin p => (c.sigma j).val / 2 ^ (q.val + 1)) := by
  intro i j hij
  exact Nat.div_le_div_right (c.increasing.monotone hij)

private theorem occupied_cross_zero_one {n p : ℕ} (c : Config n p) (q : Fin n)
    (hq : q ∈ c.P) (hmax : ∀ i ∈ c.P, i ≤ q) (i j : Fin p) :
    occupied c 0 i < occupied c 1 j ↔
      (c.sigma i).val / 2 ^ (q.val + 1) ≤ (c.sigma j).val / 2 ^ (q.val + 1) := by
  constructor
  · intro h
    simpa only [occupied_prefix c q hmax] using (Nat.div_le_div_right (c := 2 ^ (q.val + 1)) h.le)
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · apply Nat.lt_of_div_lt_div (c := 2 ^ (q.val + 1))
      simpa only [occupied_prefix c q hmax] using h
    · exact occupied_same_prefix c q hq hmax i j h

private theorem occupied_cross_one_zero {n p : ℕ} (c : Config n p) (q : Fin n)
    (hq : q ∈ c.P) (hmax : ∀ i ∈ c.P, i ≤ q) (i j : Fin p) :
    occupied c 1 i < occupied c 0 j ↔
      (c.sigma i).val / 2 ^ (q.val + 1) < (c.sigma j).val / 2 ^ (q.val + 1) := by
  constructor
  · intro h
    have hle : (c.sigma i).val / 2 ^ (q.val + 1) ≤
        (c.sigma j).val / 2 ^ (q.val + 1) := by
      simpa only [occupied_prefix c q hmax] using (Nat.div_le_div_right (c := 2 ^ (q.val + 1)) h.le)
    apply lt_of_le_of_ne hle
    intro he
    exact h.asymm (occupied_same_prefix c q hq hmax j i he.symm)
  · intro h
    apply Nat.lt_of_div_lt_div (c := 2 ^ (q.val + 1))
    simpa only [occupied_prefix c q hmax] using h

private theorem form_zero_val {n p : ℕ} (c : Config n p) (q : Fin n)
    (hq : q ∈ c.P) (hmax : ∀ i ∈ c.P, i ≤ q) (j : Fin p) :
    (form c 0 j).val = j.val +
      (Finset.univ.filter fun i : Fin p =>
        (c.sigma i).val / 2 ^ (q.val + 1) <
        (c.sigma j).val / 2 ^ (q.val + 1)).card := by
  classical
  have hsame (r : Fin 2) (i j : Fin p) :
      occupied c r i < occupied c r j ↔ i < j := by
    simp only [occupied, Nat.add_lt_add_iff_left]
    exact c.increasing.lt_iff_lt
  let S0 := Finset.univ.filter fun i : Fin p => i < j
  let S1 := Finset.univ.filter fun i : Fin p =>
    (c.sigma i).val / 2 ^ (q.val + 1) < (c.sigma j).val / 2 ^ (q.val + 1)
  have hcard : S0.card = j.val := by
    have he : S0 = Finset.Iio j := by ext i; simp [S0]
    rw [he, Fin.card_Iio]
  have hd : Disjoint (({0} : Finset (Fin 2)) ×ˢ S0) (({1} : Finset (Fin 2)) ×ˢ S1) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    simp only [Finset.mem_product, Finset.mem_singleton] at hz hz'
    have := hz.1.symm.trans hz'.1
    norm_num at this
  have he : (Finset.univ.filter fun z : Fin 2 × Fin p =>
      occupied c z.1 z.2 < occupied c 0 j) =
      (({0} : Finset (Fin 2)) ×ˢ S0) ∪ (({1} : Finset (Fin 2)) ×ˢ S1) := by
    ext ⟨r, i⟩
    fin_cases r <;> simp [S0, S1, hsame,
      occupied_cross_one_zero c q hq hmax]
  change (Finset.univ.filter fun z : Fin 2 × Fin p =>
    occupied c z.1 z.2 < occupied c 0 j).card = _
  rw [he, Finset.card_union_of_disjoint hd]
  simp [hcard, S1]

private theorem form_one_val {n p : ℕ} (c : Config n p) (q : Fin n)
    (hq : q ∈ c.P) (hmax : ∀ i ∈ c.P, i ≤ q) (j : Fin p) :
    (form c 1 j).val = j.val +
      (Finset.univ.filter fun i : Fin p =>
        (c.sigma i).val / 2 ^ (q.val + 1) ≤
        (c.sigma j).val / 2 ^ (q.val + 1)).card := by
  classical
  have hsame (r : Fin 2) (i j : Fin p) :
      occupied c r i < occupied c r j ↔ i < j := by
    simp only [occupied, Nat.add_lt_add_iff_left]
    exact c.increasing.lt_iff_lt
  let S0 := Finset.univ.filter fun i : Fin p =>
    (c.sigma i).val / 2 ^ (q.val + 1) ≤ (c.sigma j).val / 2 ^ (q.val + 1)
  let S1 := Finset.univ.filter fun i : Fin p => i < j
  have hcard : S1.card = j.val := by
    have he : S1 = Finset.Iio j := by ext i; simp [S1]
    rw [he, Fin.card_Iio]
  have hd : Disjoint (({0} : Finset (Fin 2)) ×ˢ S0) (({1} : Finset (Fin 2)) ×ˢ S1) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    simp only [Finset.mem_product, Finset.mem_singleton] at hz hz'
    have := hz.1.symm.trans hz'.1
    norm_num at this
  have he : (Finset.univ.filter fun z : Fin 2 × Fin p =>
      occupied c z.1 z.2 < occupied c 1 j) =
      (({0} : Finset (Fin 2)) ×ˢ S0) ∪ (({1} : Finset (Fin 2)) ×ˢ S1) := by
    ext ⟨r, i⟩
    fin_cases r <;> simp [S0, S1, hsame,
      occupied_cross_zero_one c q hq hmax]
  change (Finset.univ.filter fun z : Fin 2 × Fin p =>
    occupied c z.1 z.2 < occupied c 1 j).card = _
  rw [he, Finset.card_union_of_disjoint hd]
  simp [hcard, S0, Nat.add_comm]


private theorem monotone_composition {p : Nat} (g : Fin p → Nat) (hg : Monotone g) :
    ∃ d : Composition p, ∀ j : Fin p,
      d.sizeUpTo (d.index j) = (Finset.univ.filter (fun i => g i < g j)).card ∧
      d.sizeUpTo ((d.index j).val + 1) =
        (Finset.univ.filter (fun i => g i ≤ g j)).card := by
  classical
  let L : Fin p → Nat := fun j => (Finset.univ.filter (fun i => g i < g j)).card
  let R : Fin p → Nat := fun j => (Finset.univ.filter (fun i => g i ≤ g j)).card
  have hL : ∀ i j : Fin p, g i < g j ↔ i.val < L j := by
    intro i j
    exact (Fin.lt_card_filter_univ_iff_apply_of_imp (j := i) (fun t => g t < g j)
      (by
        intro u t htu hu
        exact lt_of_le_of_lt (hg htu) hu)).symm
  have hR : ∀ i j : Fin p, g i ≤ g j ↔ i.val < R j := by
    intro i j
    exact (Fin.lt_card_filter_univ_iff_apply_of_imp (j := i) (fun t => g t ≤ g j)
      (by
        intro u t htu hu
        exact le_trans (hg htu) hu)).symm
  have hLp : ∀ j, L j ≤ p := by
    intro j
    simpa [L] using Finset.card_le_card
      (Finset.filter_subset (fun i => g i < g j) (Finset.univ : Finset (Fin p)))
  have hRp : ∀ j, R j ≤ p := by
    intro j
    simpa [R] using Finset.card_le_card
      (Finset.filter_subset (fun i => g i ≤ g j) (Finset.univ : Finset (Fin p)))
  let lower : Fin p → Fin (p + 1) := fun j => ⟨L j, by have := hLp j; omega⟩
  let B : CompositionAsSet p := {
    boundaries := insert 0 (insert (Fin.last p) (Finset.univ.image lower))
    zero_mem := Finset.mem_insert_self _ _
    getLast_mem := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  }
  let d := B.toComposition
  have hd : d.boundaries = B.boundaries := B.toComposition_boundaries
  have hmemL : ∀ j, lower j ∈ d.boundaries := by
    intro j
    rw [hd]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
  have hmemR : ∀ j, (⟨R j, by have := hRp j; omega⟩ : Fin (p + 1)) ∈ d.boundaries := by
    intro j
    by_cases hr : R j = p
    · rw [hd]
      have he : (⟨R j, by have := hRp j; omega⟩ : Fin (p + 1)) = Fin.last p := by
        apply Fin.ext
        exact hr
      rw [he]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · have hrp : R j < p := by have := hRp j; omega
      let t : Fin p := ⟨R j, hrp⟩
      have hjt : g j < g t := by
        have hn : ¬ g t ≤ g j := by
          intro h
          have hh := (hR t j).mp h
          change R j < R j at hh
          omega
        omega
      have he : L t = R j := by
        apply congrArg Finset.card
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hit
          have hi : i < t := by
            by_contra hn
            exact (not_lt_of_ge (hg (le_of_not_gt hn))) hit
          exact (hR i j).mpr hi
        · intro hij
          exact lt_of_le_of_lt hij hjt
      convert hmemL t using 1
      apply Fin.ext
      exact he.symm
  refine ⟨d, ?_⟩
  intro j
  let s := d.sizeUpTo (d.index j)
  let t := d.sizeUpTo ((d.index j).val + 1)
  have hsj : s ≤ j.val := d.sizeUpTo_index_le j
  have hjt : j.val < t := d.lt_sizeUpTo_index_succ j
  have hLj : L j ≤ j.val := by
    have hh := hL j j
    omega
  have hjR : j.val < R j := (hR j j).mp le_rfl
  have hleft : ∀ b ∈ d.boundaries, b.val ≤ j.val → b.val ≤ s := by
    intro b hb hbj
    rcases Finset.mem_map.mp hb with ⟨i, _, hi⟩
    have hiv : d.sizeUpTo i.val = b.val := congrArg Fin.val hi
    have hile : i.val ≤ (d.index j).val := by
      by_contra hn
      have hx := d.monotone_sizeUpTo (show (d.index j).val + 1 ≤ i.val by omega)
      omega
    have hx := d.monotone_sizeUpTo hile
    omega
  have hright : ∀ b ∈ d.boundaries, j.val < b.val → t ≤ b.val := by
    intro b hb hbj
    rcases Finset.mem_map.mp hb with ⟨i, _, hi⟩
    have hiv : d.sizeUpTo i.val = b.val := congrArg Fin.val hi
    have hilt : (d.index j).val < i.val := by
      by_contra hn
      have hx := d.monotone_sizeUpTo (show i.val ≤ (d.index j).val by omega)
      omega
    have hx := d.monotone_sizeUpTo (show (d.index j).val + 1 ≤ i.val by omega)
    omega
  have hsB : (⟨s, by have := d.sizeUpTo_le (d.index j); omega⟩ : Fin (p + 1)) ∈ B.boundaries := by
    rw [← hd]
    exact Finset.mem_map.mpr ⟨⟨(d.index j).val, by have := (d.index j).isLt; omega⟩,
      Finset.mem_univ _, rfl⟩
  have htB :
      (⟨t, by have := d.sizeUpTo_le ((d.index j).val + 1); omega⟩ : Fin (p + 1)) ∈
        B.boundaries := by
    rw [← hd]
    exact Finset.mem_map.mpr ⟨⟨(d.index j).val + 1, by have := (d.index j).isLt; omega⟩,
      Finset.mem_univ _, rfl⟩
  have hsL : s ≤ L j := by
    rcases Finset.mem_insert.mp hsB with hz | hsB
    · have hzero := congrArg Fin.val hz
      change s = 0 at hzero
      omega
    rcases Finset.mem_insert.mp hsB with hp | hsB
    · have hp' := congrArg Fin.val hp
      change s = p at hp'
      have := j.isLt
      omega
    rcases Finset.mem_image.mp hsB with ⟨i, _, hi⟩
    have hsi : L i = s := congrArg Fin.val hi
    have hij : g i ≤ g j := by
      have hh := hL j i
      omega
    have hc : L i ≤ L j := Finset.card_le_card (by
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lt_of_lt_of_le (Finset.mem_filter.mp hu).2 hij⟩)
    omega
  have hRt : R j ≤ t := by
    rcases Finset.mem_insert.mp htB with hz | htB
    · have hzero := congrArg Fin.val hz
      change t = 0 at hzero
      omega
    rcases Finset.mem_insert.mp htB with hp | htB
    · have hp' := congrArg Fin.val hp
      change t = p at hp'
      have := hRp j
      omega
    rcases Finset.mem_image.mp htB with ⟨i, _, hi⟩
    have hti : L i = t := congrArg Fin.val hi
    have hji : g j < g i := (hL j i).mpr (by omega)
    have hc : R j ≤ L i := Finset.card_le_card (by
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lt_of_le_of_lt (Finset.mem_filter.mp hu).2 hji⟩)
    omega
  constructor
  · exact le_antisymm hsL (hleft (lower j) (hmemL j) hLj)
  · exact le_antisymm (hright _ (hmemR j) hjR) hRt


/-- Grouping columns by the bits above the highest row qubit gives a composition. -/
theorem necessity {n p : ℕ} (c : Config n p) :
    ∃ d : Composition p, form c = formOf d := by
  let q := c.P.max' c.nonempty
  have hq : q ∈ c.P := Finset.max'_mem _ _
  have hmax : ∀ i ∈ c.P, i ≤ q := fun i hi => Finset.le_max' _ _ hi
  obtain ⟨d, hd⟩ := monotone_composition
    (fun j : Fin p => (c.sigma j).val / 2 ^ (q.val + 1)) (prefix_monotone c q)
  refine ⟨d, ?_⟩
  funext r j
  apply Fin.ext
  fin_cases r
  · change (form c 0 j).val = (formOf d 0 j).val
    rw [form_zero_val c q hq hmax]
    change j.val + _ = j.val + d.sizeUpTo ((d.index j).val + 0)
    simpa using congrArg (j.val + ·) (hd j).1.symm
  · change (form c 1 j).val = (formOf d 1 j).val
    rw [form_one_val c q hq hmax]
    change j.val + _ = j.val + d.sizeUpTo ((d.index j).val + 1)
    exact congrArg (j.val + ·) (hd j).2.symm

private theorem realization_data {p n : ℕ} (hp : 1 ≤ p) (d : Composition p)
    (hn : 2 * Nat.clog 2 p + 1 ≤ n) :
    ∃ (c : Config n p) (q t : ℕ),
      q + t < n ∧
      (∀ i : Fin n, i ∈ c.P ↔ i.val < t ∨ i.val = q + t) ∧
      c.x.val = 0 ∧
      c.y.val = 2 ^ t * 2 ^ q + (2 ^ t - 1) ∧
      (∀ j, (c.sigma j).val = 2 ^ t *
        (2 ^ (q + 1) * (d.index j).val + (d.invEmbedding j).val)) ∧
      (∀ j, (d.invEmbedding j).val < 2 ^ q) ∧
      (∀ j, (c.sigma j).val / 2 ^ (q + t + 1) = (d.index j).val) := by
  classical
  let a := Finset.univ.sup d.blocksFun
  let q := Nat.clog 2 a
  let h := Nat.clog 2 d.length
  let t := n - (h + q + 1)
  have hdlen : 0 < d.length := d.length_pos_iff.mpr hp
  have hblocks : ∀ i : Fin d.length, d.blocksFun i ≤ a :=
    fun i => Finset.le_sup (Finset.mem_univ i)
  have ha : 1 ≤ a := (d.one_le_blocksFun ⟨0, hdlen⟩).trans (hblocks _)
  have hap : a ≤ p := Finset.sup_le (fun i _ => d.blocksFun_le i)
  have hqp : q ≤ Nat.clog 2 p := Nat.clog_mono_right 2 hap
  have hhp : h ≤ Nat.clog 2 p := Nat.clog_mono_right 2 d.length_le
  have hsmall : h + q + 1 ≤ n := by omega
  have hn_eq : n = h + q + 1 + t := by omega
  have hqt : q + t < n := by omega
  have hpowq : a ≤ 2 ^ q := Nat.le_pow_clog (by decide) a
  have hpowh : d.length ≤ 2 ^ h := Nat.le_pow_clog (by decide) d.length
  have hoff : ∀ j : Fin p, (d.invEmbedding j).val < 2 ^ q :=
    fun j => (d.invEmbedding j).isLt.trans_le ((hblocks _).trans hpowq)
  let P : Finset (Fin n) := Finset.univ.filter (fun i => i.val < t ∨ i.val = q + t)
  have hP : ∀ i : Fin n, i ∈ P ↔ i.val < t ∨ i.val = q + t := by
    intro i
    simp [P]
  let sigmaNat : Fin p → ℕ := fun j =>
    2 ^ t * (2 ^ (q + 1) * (d.index j).val + (d.invEmbedding j).val)
  have hsbound : ∀ j, sigmaNat j < 2 ^ n := by
    intro j
    have hidx := (d.index j).isLt.trans_le hpowh
    have hu := hoff j
    have hpq := Nat.two_pow_pos q
    have hpt := Nat.two_pow_pos t
    have he : 2 ^ n = 2 ^ t * (2 ^ (q + 1) * 2 ^ h) := by
      rw [hn_eq]
      simp only [pow_add]
      ring
    rw [he]
    dsimp [sigmaNat]
    have hb : 2 ^ (q + 1) * (d.index j).val + (d.invEmbedding j).val <
        2 ^ (q + 1) * 2 ^ h := by
      rw [pow_succ] at *
      nlinarith
    exact Nat.mul_lt_mul_of_pos_left hb hpt
  let sig : Fin p → BitWord n := fun j => ⟨sigmaNat j, hsbound j⟩
  have hsbits : ∀ (j : Fin p) (i : Fin n),
      (sig j).val.testBit i.val =
        if i.val < t then false else
        if i.val - t < q + 1 then (d.invEmbedding j).val.testBit (i.val - t)
        else (d.index j).val.testBit (i.val - t - (q + 1)) := by
    intro j i
    change (2 ^ t * (2 ^ (q + 1) * (d.index j).val +
      (d.invEmbedding j).val)).testBit i.val = _
    rw [Nat.testBit_two_pow_mul]
    by_cases hi : i.val < t
    · simp [hi]
    · simp only [hi, if_false,
        show decide (i.val ≥ t) = true from decide_eq_true (Nat.le_of_not_lt hi),
        Bool.true_and]
      exact Nat.testBit_two_pow_mul_add _
        ((hoff j).trans_le (show 2 ^ q ≤ 2 ^ (q + 1) from
          Nat.pow_le_pow_right (by decide) (by omega))) _
  have hidxmono : Monotone (fun j : Fin p => d.index j) := by
    intro i j hij
    change (d.index i).val ≤ (d.index j).val
    by_contra hbad
    have hji : (d.index j).val + 1 ≤ (d.index i).val := by
      exact Nat.succ_le_of_lt (not_le.mp hbad)
    have hsz := d.monotone_sizeUpTo hji
    have hjb := d.lt_sizeUpTo_index_succ j
    change j.val < d.sizeUpTo ((d.index j).val + 1) at hjb
    have hib := d.sizeUpTo_index_le i
    have hij' : i.val ≤ j.val := hij
    omega
  have hsmono : StrictMono sig := by
    intro i j hij
    have hijv : i.val < j.val := hij
    have hidx := hidxmono hij.le
    change sigmaNat i < sigmaNat j
    apply Nat.mul_lt_mul_of_pos_left _ (Nat.two_pow_pos t)
    by_cases he : d.index i = d.index j
    · have hai := d.sizeUpTo_index_le i
      have haj := d.sizeUpTo_index_le j
      have heval : (d.index i).val = (d.index j).val := congrArg Fin.val he
      have hsz : d.sizeUpTo (d.index i).val = d.sizeUpTo (d.index j).val :=
        congrArg d.sizeUpTo heval
      simp only [Composition.coe_invEmbedding]
      rw [heval]
      omega
    · have hil : (d.index i).val < (d.index j).val :=
        lt_of_le_of_ne hidx (fun hh => he (Fin.ext hh))
      have hu := hoff i
      have hv := hoff j
      have hpq := Nat.two_pow_pos q
      simp only [pow_succ]
      nlinarith
  let ynat := 2 ^ t * 2 ^ q + (2 ^ t - 1)
  have hybound : ynat < 2 ^ n := by
    have hpt := Nat.two_pow_pos t
    have hpq := Nat.two_pow_pos q
    have hlt : ynat < 2 ^ (q + t + 1) := by
      have hsub : 2 ^ t - 1 < 2 ^ t := by omega
      have hlarge : 2 ^ t ≤ 2 ^ t * 2 ^ q := by nlinarith
      dsimp [ynat]
      simp only [pow_add, pow_one]
      rw [Nat.mul_comm (2 ^ q) (2 ^ t)]
      omega
    exact hlt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  let x : BitWord n := ⟨0, Nat.two_pow_pos n⟩
  let y : BitWord n := ⟨ynat, hybound⟩
  have hybits : ∀ i : Fin n, y.val.testBit i.val = if i ∈ P then true else false := by
    intro i
    dsimp [y, ynat]
    rw [Nat.testBit_two_pow_mul_add _ (by have := Nat.two_pow_pos t; omega)]
    rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
    simp only [hP]
    by_cases hi : i.val < t
    · simp [hi]
    · have he : q = i.val - t ↔ i.val = q + t := by omega
      simp [hi, he]
  have hssupported : ∀ j, Supported Pᶜ (sig j) := by
    intro j i hi
    have hip : i ∈ P := by simpa using hi
    rw [hP] at hip
    rw [hsbits]
    rcases hip with hit | he
    · simp [hit]
    · have hnlt : ¬ i.val < t := by omega
      have hsub : i.val - t = q := by omega
      simp only [hnlt, if_false, hsub, Nat.lt_add_one, if_true]
      exact Nat.testBit_lt_two_pow (hoff j)
  have hz : ∃ j : Fin p, sigmaNat j = 0 := by
    let i0 : Fin d.length := ⟨0, hdlen⟩
    let u0 : Fin (d.blocksFun i0) := ⟨0, d.one_le_blocksFun i0⟩
    refine ⟨d.embedding i0 u0, ?_⟩
    simp [sigmaNat, i0, u0, d.index_embedding]
  have hvar : ∀ i : Fin n, i ∉ P →
      (∃ j, (sig j).val.testBit i.val = false) ∧
      (∃ j, (sig j).val.testBit i.val = true) := by
    intro i hi
    obtain ⟨jz, hjz⟩ := hz
    refine ⟨⟨jz, ?_⟩, ?_⟩
    · change (sigmaNat jz).testBit i.val = false
      simp [hjz]
    · have hiP : ¬ (i.val < t ∨ i.val = q + t) := by rwa [← hP]
      have hit : t ≤ i.val := by omega
      have hisep : i.val - t ≠ q := by omega
      by_cases hilow : i.val - t < q
      · have hb : 2 ^ (i.val - t) < a :=
          Nat.pow_lt_of_lt_clog (show i.val - t < q from hilow)
        obtain ⟨b, _, hab⟩ := Finset.exists_mem_eq_sup Finset.univ
          (Finset.univ_nonempty_iff.mpr ⟨⟨0, hdlen⟩⟩) d.blocksFun
        have hba : a = d.blocksFun b := hab
        let u : Fin (d.blocksFun b) := ⟨2 ^ (i.val - t), by rwa [← hba]⟩
        refine ⟨d.embedding b u, ?_⟩
        rw [hsbits]
        simp [Nat.not_lt.mpr hit, show i.val - t < q + 1 by omega,
          d.index_embedding, u]
      · have hhigh : q + 1 ≤ i.val - t := by omega
        have hib : i.val - t - (q + 1) < h := by omega
        have hb : 2 ^ (i.val - t - (q + 1)) < d.length :=
          Nat.pow_lt_of_lt_clog hib
        let b : Fin d.length := ⟨2 ^ (i.val - t - (q + 1)), hb⟩
        let u : Fin (d.blocksFun b) := ⟨0, d.one_le_blocksFun b⟩
        refine ⟨d.embedding b u, ?_⟩
        rw [hsbits]
        simp [Nat.not_lt.mpr hit, Nat.not_lt.mpr hhigh, d.index_embedding, b]
  let c : Config n p := {
    P := P
    nonempty := ⟨⟨q + t, hqt⟩, (hP _).mpr (Or.inr rfl)⟩
    x := x
    y := y
    x_supported := by intro i hi; simp [x]
    y_bits := by intro i; simpa [x] using hybits i
    first_zero := by intro b hb hmax; simp [x]
    sigma := sig
    increasing := hsmono
    sigma_supported := hssupported
    varying := hvar }
  have hprefix : ∀ j, (sig j).val / 2 ^ (q + t + 1) = (d.index j).val := by
    intro j
    have he : 2 ^ (q + t + 1) = 2 ^ t * 2 ^ (q + 1) := by
      simp only [pow_add, pow_one]
      ring
    change sigmaNat j / 2 ^ (q + t + 1) = _
    rw [he]
    dsimp only [sigmaNat]
    rw [Nat.mul_div_mul_left _ _ (Nat.two_pow_pos t),
      Nat.mul_add_div (Nat.two_pow_pos (q + 1))]
    have hu : (d.invEmbedding j).val < 2 ^ (q + 1) :=
      (hoff j).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    simp only [Nat.add_eq_left, Nat.div_eq_zero_iff]
    exact Or.inr hu
  exact ⟨c, q, t, hqt, hP, rfl, rfl, fun _ => rfl, hoff, hprefix⟩


/-- Every composition is realized at each sufficiently large qubit count. -/
theorem realization {p : ℕ} (hp : 1 ≤ p) (d : Composition p) (n : ℕ)
    (hn : 2 * Nat.clog 2 p + 1 ≤ n) : ∃ c : Config n p, form c = formOf d := by
  classical
  have counts (j : Fin p) :
      (Finset.univ.filter fun i : Fin p => d.index i < d.index j).card =
        d.sizeUpTo (d.index j).val ∧
      (Finset.univ.filter fun i : Fin p => d.index i ≤ d.index j).card =
        d.sizeUpTo ((d.index j).val + 1) := by
    constructor
    · simp_rw [index_lt_iff]
      rw [Fin.card_filter_val_lt, min_eq_right (d.sizeUpTo_le _)]
    · simp_rw [index_le_iff]
      rw [Fin.card_filter_val_lt, min_eq_right (d.sizeUpTo_le _)]
  obtain ⟨c, q, t, hqt, hP, hx, hy, hs, hoff, hprefix⟩ := realization_data hp d hn
  let qf : Fin n := ⟨q + t, hqt⟩
  have hq : qf ∈ c.P := (hP qf).mpr (Or.inr rfl)
  have hmax : ∀ i ∈ c.P, i ≤ qf := by
    intro i hi
    have hip := (hP i).mp hi
    change i.val ≤ q + t
    omega
  refine ⟨c, ?_⟩
  funext r j
  apply Fin.ext
  fin_cases r
  · change (form c 0 j).val = j.val + d.sizeUpTo ((d.index j).val + 0)
    rw [form_zero_val c qf hq hmax]
    simp only [qf, hprefix, add_zero]
    exact congrArg (j.val + ·) (counts j).1
  · change (form c 1 j).val = j.val + d.sizeUpTo ((d.index j).val + 1)
    rw [form_one_val c qf hq hmax]
    simp only [qf, hprefix]
    exact congrArg (j.val + ·) (counts j).2


/-- The forms are exactly the distinct images of compositions. -/
theorem forms_eq_range (p : ℕ) (hp : 1 ≤ p) :
    forms p = Set.range (@formOf p) := by
  ext f
  constructor
  · rintro ⟨n, c, rfl⟩
    obtain ⟨d, hd⟩ := necessity c
    exact ⟨d, hd.symm⟩
  · rintro ⟨d, rfl⟩
    obtain ⟨c, hc⟩ := realization hp d (2 * Nat.clog 2 p + 1) le_rfl
    exact ⟨2 * Nat.clog 2 p + 1, c, hc⟩

/-- There are one form per composition, and all occur at every sufficiently large qubit count. -/
theorem result (p : ℕ) (hp : 1 ≤ p) :
    (forms p).ncard = 2 ^ (p - 1) ∧
    ∀ n, 2 * Nat.clog 2 p + 1 ≤ n → formsAt n p = forms p := by
  constructor
  · rw [forms_eq_range p hp, Set.ncard_range_of_injective (formOf_injective p),
      Nat.card_eq_fintype_card, composition_card]
  · intro n hn
    ext f
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨n, c, hc⟩
    · rintro ⟨m, c, rfl⟩
      obtain ⟨d, hd⟩ := necessity c
      obtain ⟨c', hc'⟩ := realization hp d n hn
      exact ⟨c', hc'.trans hd.symm⟩

end D5.S3.Quantum.Entanglement.QubitSupportCoefficientForms
