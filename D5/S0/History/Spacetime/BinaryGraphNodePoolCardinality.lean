/- GID: D5/S0/History/Spacetime/BinaryGraphNodePoolCardinality
   generality: G
   mirror-B: D5/B/S0/History/Spacetime/BinaryGraphNodePoolCardinality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact cardinality of the ordinal and Kuratowski nodes of a finite binary graph. -/

import D5.S0.History.Spacetime.HFEncoding
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

namespace D5.S0.History.Spacetime.BinaryGraphNodePoolCardinality

noncomputable section

open HFEncoding (toZF natCode)

local notation "o" => fun n : ℕ => toZF (natCode n)

/-- The singleton of a finite von Neumann index. -/
def singletonNode (j : ℕ) : ZFSet.{0} := {o j}

/-- The unordered pair of an index and its binary value. -/
def doubleNode (b : ℕ → Bool) (j : ℕ) : ZFSet.{0} :=
  {o j, o (if b j then 1 else 0)}

/-- The Kuratowski pair of an index and its binary value. -/
def edge (b : ℕ → Bool) (j : ℕ) : ZFSet.{0} :=
  ZFSet.pair (o j) (o (if b j then 1 else 0))

/-- All ordinal indices, singletons, unordered bit pairs, and edges in a finite window. -/
def nodePool (ell : ℕ) (b : ℕ → Bool) : Finset ZFSet.{0} := by
  classical
  exact (Finset.range ell).image o ∪
    (Finset.range ell).image singletonNode ∪
    (Finset.range ell).image (doubleNode b) ∪
    (Finset.range ell).image (edge b)

/-- A binary graph window of length at least three has exactly this many distinct nodes. -/
theorem nodePool_card (ell : ℕ) (hell : 3 ≤ ell) (b : ℕ → Bool) :
    (nodePool ell b).card = 4 * ell - 4 +
      (if b 0 then 1 else 0) * (1 - (if b 2 then 1 else 0)) := by
  classical
  have oi (i j : ℕ) : o i = o j ↔ i = j := by
    simp [HFEncoding.toZF_natCode, Ordinal.toZFSet_injective.eq_iff]
  have om (i j : ℕ) : o i ∈ o j ↔ i < j := by
    simp [HFEncoding.toZF_natCode, Ordinal.toZFSet_mem_toZFSet_iff]
  have oo (i : ℕ) : ZFSet.IsOrdinal (o i) := by
    simpa [HFEncoding.IsNatCode] using HFEncoding.natCode_valid i
  have oz : o 0 = (∅ : ZFSet) := by simp [HFEncoding.toZF_natCode]
  have os (j : ℕ) : o (j + 1) = insert (o j) (o j) := by
    simp [HFEncoding.toZF_natCode, Ordinal.toZFSet_add_one]
  have az : singletonNode 0 = o 1 := by
    rw [show 1 = 0 + 1 from rfl, os]
    simp [singletonNode, oz]
  have ot : o 2 = ({o 0, o 1} : ZFSet) := by
    rw [show 2 = 1 + 1 from rfl, os]
    have h1 : o 1 = ({o 0} : ZFSet) := az.symm
    rw [h1]
    ext x
    simp [or_comm]
  have an (j : ℕ) (hj : 1 ≤ j) : ¬ ZFSet.IsOrdinal (singletonNode j) := by
    intro h
    have hz : o 0 ∈ singletonNode j :=
      h.mem_trans ((om 0 j).mpr (by omega)) (by simp [singletonNode])
    have := (oi 0 j).mp (ZFSet.mem_singleton.mp hz)
    omega
  have dn (j : ℕ) (hj : 2 ≤ j) : ¬ ZFSet.IsOrdinal (doubleNode b j) := by
    intro h
    have hm : o j ∈ doubleNode b j := by simp [doubleNode]
    have hz := h.mem_trans ((om 0 j).mpr (by omega)) hm
    have hu := h.mem_trans ((om 1 j).mpr (by omega)) hm
    simp only [doubleNode, ZFSet.mem_pair, oi] at hz hu
    cases hb : b j <;> simp [hb] at hz hu <;> omega
  have ai : Function.Injective singletonNode := by
    intro i j h
    exact (oi i j).mp (ZFSet.singleton_inj.mp h)
  have di : Set.InjOn (doubleNode b) {j | 2 ≤ j} := by
    intro i hi j hj h
    change 2 ≤ i at hi
    have hm : o i ∈ doubleNode b j := h ▸ (by simp [doubleNode])
    simp only [doubleNode, ZFSet.mem_pair, oi] at hm
    cases hb : b j <;> simp [hb] at hm <;> omega
  have pi : Function.Injective (edge b) := by
    intro i j h
    exact (oi i j).mp (ZFSet.pair_inj.mp h).1
  have da (i j : ℕ) (hi : 2 ≤ i) : doubleNode b i ≠ singletonNode j := by
    intro h
    have h' := ZFSet.pair_eq_singleton_iff.mp h
    have hij := (oi i j).mp h'.1
    have hbj := (oi (if b i then 1 else 0) j).mp h'.2
    cases hb : b i <;> simp [hb] at hbj <;> omega
  let O := (Finset.range ell).image o
  let A := (Finset.Ico 1 ell).image singletonNode
  let D := (Finset.Ico 2 ell).image (doubleNode b)
  let P := (Finset.Ico 1 ell).image (edge b)
  let B := O ∪ A ∪ D
  have memO (x : ZFSet) : x ∈ O ↔ ∃ j < ell, o j = x := by simp [O]
  have memA (x : ZFSet) : x ∈ A ↔ ∃ j, (1 ≤ j ∧ j < ell) ∧ singletonNode j = x := by
    simp [A]
  have memD (x : ZFSet) : x ∈ D ↔ ∃ j, (2 ≤ j ∧ j < ell) ∧ doubleNode b j = x := by
    simp [D]
  have memP (x : ZFSet) : x ∈ P ↔ ∃ j, (1 ≤ j ∧ j < ell) ∧ edge b j = x := by
    simp [P]
  have hOA : Disjoint O A := by
    apply Finset.disjoint_left.mpr
    intro x hx ha
    obtain ⟨i, hi, rfl⟩ := (memO x).mp hx
    obtain ⟨j, hj, he⟩ := (memA (o i)).mp ha
    exact an j hj.1 (he.symm ▸ oo i)
  have hOD : Disjoint O D := by
    apply Finset.disjoint_left.mpr
    intro x hx hd
    obtain ⟨i, hi, rfl⟩ := (memO x).mp hx
    obtain ⟨j, hj, he⟩ := (memD (o i)).mp hd
    exact dn j hj.1 (he.symm ▸ oo i)
  have hAD : Disjoint A D := by
    apply Finset.disjoint_left.mpr
    intro x ha hd
    obtain ⟨i, hi, rfl⟩ := (memA x).mp ha
    obtain ⟨j, hj, he⟩ := (memD (singletonNode i)).mp hd
    exact da j i hj.1 he
  have hBc : B.card = 3 * ell - 3 := by
    have hO : O.card = ell := by
      rw [Finset.card_image_of_injective _ (fun i j h => (oi i j).mp h)]
      exact Finset.card_range ell
    have hA : A.card = ell - 1 := by
      rw [Finset.card_image_of_injective _ ai]
      exact Nat.card_Ico 1 ell
    have hD : D.card = ell - 2 := by
      rw [Finset.card_image_of_injOn (fun i hi j hj h =>
        di (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hj).1 h)]
      exact Nat.card_Ico 2 ell
    have hd : Disjoint (O ∪ A) D := Finset.disjoint_union_left.mpr ⟨hOD, hAD⟩
    dsimp [B]
    rw [Finset.card_union_of_disjoint hd, Finset.card_union_of_disjoint hOA,
      hO, hA, hD]
    omega
  have bm (x : ZFSet) (hx : x ∈ B) : ∀ y ∈ x, ZFSet.IsOrdinal y := by
    intro y hy
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨j, hj, rfl⟩ := (memO x).mp hx
        exact (oo j).mem hy
      · obtain ⟨j, hj, rfl⟩ := (memA x).mp hx
        have he : y = o j := ZFSet.mem_singleton.mp hy
        exact he.symm ▸ oo j
    · obtain ⟨j, hj, rfl⟩ := (memD x).mp hx
      rcases ZFSet.mem_pair.mp hy with rfl | rfl <;> exact oo _
  have hBP : Disjoint B P := by
    apply Finset.disjoint_left.mpr
    intro x hx hp
    obtain ⟨j, hj, rfl⟩ := (memP x).mp hp
    exact an j hj.1 (bm _ hx _ (by simp [edge, ZFSet.pair, singletonNode]))
  have hPc : P.card = ell - 1 := by
    rw [Finset.card_image_of_injective _ pi]
    exact Nat.card_Ico 1 ell
  have hQ : (B ∪ P).card = 4 * ell - 4 := by
    rw [Finset.card_union_of_disjoint hBP, hBc, hPc]
    omega
  have a1B : singletonNode 1 ∈ B := by
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      ((memA _).mpr ⟨1, ⟨by omega, by omega⟩, rfl⟩))
  have oB (j : ℕ) (hj : j < ell) : o j ∈ B := by
    exact Finset.mem_union_left _ (Finset.mem_union_left _ ((memO _).mpr ⟨j, hj, rfl⟩))
  have d0 : doubleNode b 0 = if b 0 then o 2 else o 1 := by
    cases hb : b 0
    · simpa [doubleNode, hb, singletonNode] using az
    · simpa [doubleNode, hb] using ot.symm
  have d1 : doubleNode b 1 = if b 1 then singletonNode 1 else o 2 := by
    cases hb : b 1
    · change doubleNode b 1 = o 2
      simp only [doubleNode, hb, Bool.false_eq_true, ↓reduceIte, ot]
      ext x
      simp only [ZFSet.mem_pair]
      exact or_comm
    · simp [doubleNode, singletonNode, hb]
  have haB (j : ℕ) (hj : j < ell) : singletonNode j ∈ B := by
    by_cases hz : j = 0
    · subst j
      rw [az]
      exact oB 1 (by omega)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        ((memA _).mpr ⟨j, ⟨by omega, hj⟩, rfl⟩))
  have hdB (j : ℕ) (hj : j < ell) : doubleNode b j ∈ B := by
    by_cases h0 : j = 0
    · subst j
      rw [d0]
      split <;> exact oB _ (by omega)
    by_cases h1 : j = 1
    · subst j
      rw [d1]
      split
      · exact a1B
      · exact oB _ (by omega)
    exact Finset.mem_union_right _ ((memD _).mpr ⟨j, ⟨by omega, hj⟩, rfl⟩)
  have pool_eq : nodePool ell b = insert (edge b 0) (B ∪ P) := by
    ext x
    constructor
    · intro hx
      simp only [nodePool, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hx
      rcases hx with ((hx | hx) | hx) | hx
      · obtain ⟨j, hj, rfl⟩ := hx
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (oB j hj))
      · obtain ⟨j, hj, rfl⟩ := hx
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (haB j hj))
      · obtain ⟨j, hj, rfl⟩ := hx
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hdB j hj))
      · obtain ⟨j, hj, rfl⟩ := hx
        by_cases hz : j = 0
        · simp [hz]
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
            ((memP _).mpr ⟨j, ⟨by omega, hj⟩, rfl⟩))
    · intro hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp only [nodePool, Finset.mem_union, Finset.mem_image, Finset.mem_range]
        exact Or.inr ⟨0, by omega, rfl⟩
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp hx with hx | hx
        · rcases Finset.mem_union.mp hx with hx | hx
          · obtain ⟨j, hj, rfl⟩ := (memO x).mp hx
            simp only [nodePool, Finset.mem_union, Finset.mem_image, Finset.mem_range]
            exact Or.inl (Or.inl (Or.inl ⟨j, hj, rfl⟩))
          · obtain ⟨j, hj, rfl⟩ := (memA x).mp hx
            simp only [nodePool, Finset.mem_union, Finset.mem_image, Finset.mem_range]
            exact Or.inl (Or.inl (Or.inr ⟨j, hj.2, rfl⟩))
        · obtain ⟨j, hj, rfl⟩ := (memD x).mp hx
          simp only [nodePool, Finset.mem_union, Finset.mem_image, Finset.mem_range]
          exact Or.inl (Or.inr ⟨j, hj.2, rfl⟩)
      · obtain ⟨j, hj, rfl⟩ := (memP x).mp hx
        simp only [nodePool, Finset.mem_union, Finset.mem_image, Finset.mem_range]
        exact Or.inr ⟨j, hj.2, rfl⟩
  have p0P : edge b 0 ∉ P := by
    intro h
    obtain ⟨j, hj, he⟩ := (memP _).mp h
    have := pi he
    omega
  have p0zero (hb : b 0 = false) : edge b 0 = singletonNode 1 := by
    change ({singletonNode 0, doubleNode b 0} : ZFSet) = singletonNode 1
    rw [az, d0]
    simp [hb, singletonNode]
  have p0one (hb : b 0 = true) : edge b 0 = ({o 1, o 2} : ZFSet) := by
    change ({singletonNode 0, doubleNode b 0} : ZFSet) = _
    rw [az, d0]
    simp [hb]
  have exceptional (hb : b 0 = true) : edge b 0 ∈ B ↔ b 2 = true := by
    have hn : ¬ ZFSet.IsOrdinal (edge b 0) := by
      intro h
      have hm : o 1 ∈ edge b 0 := by simp [p0one hb]
      have hz := h.mem_trans ((om 0 1).mpr (by omega)) hm
      simp only [p0one hb, ZFSet.mem_pair, oi] at hz
      omega
    have hna (j : ℕ) : edge b 0 ≠ singletonNode j := by
      intro h
      rw [p0one hb] at h
      have h' := ZFSet.pair_eq_singleton_iff.mp h
      have := (oi 1 j).mp h'.1
      have := (oi 2 j).mp h'.2
      omega
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp hx with hx | hx
        · obtain ⟨j, hj, he⟩ := (memO _).mp hx
          exact (hn (he ▸ oo j)).elim
        · obtain ⟨j, hj, he⟩ := (memA _).mp hx
          exact (hna j he.symm).elim
      · obtain ⟨j, hj, he⟩ := (memD _).mp hx
        have hm : o j ∈ edge b 0 := he ▸ (by simp [doubleNode])
        simp only [p0one hb, ZFSet.mem_pair, oi] at hm
        have hj2 : j = 2 := by omega
        subst j
        have hm1 : o 1 ∈ doubleNode b 2 := by rw [he, p0one hb]; simp
        simp only [doubleNode, ZFSet.mem_pair, oi] at hm1
        cases h2 : b 2 <;> simp_all
    · intro h2
      apply Finset.mem_union_right
      apply (memD _).mpr
      refine ⟨2, ⟨by omega, by omega⟩, ?_⟩
      rw [p0one hb]
      simp only [doubleNode, h2, ↓reduceIte]
      ext x
      simp only [ZFSet.mem_pair]
      exact or_comm
  rw [pool_eq]
  cases h0 : b 0
  · have hm : edge b 0 ∈ B ∪ P :=
      Finset.mem_union_left _ ((p0zero h0).symm ▸ a1B)
    rw [Finset.card_insert_of_mem hm, hQ]
    simp
  · cases h2 : b 2
    · have hn : edge b 0 ∉ B ∪ P := by
        simp only [Finset.mem_union, not_or]
        exact ⟨fun h => by simpa [h2] using (exceptional h0).mp h, p0P⟩
      rw [Finset.card_insert_of_notMem hn, hQ]
      simp
    · have hm : edge b 0 ∈ B ∪ P := Finset.mem_union_left _ ((exceptional h0).mpr h2)
      rw [Finset.card_insert_of_mem hm, hQ]
      simp

end
end D5.S0.History.Spacetime.BinaryGraphNodePoolCardinality
