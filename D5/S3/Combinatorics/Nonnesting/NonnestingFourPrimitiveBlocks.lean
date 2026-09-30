/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveBlocks
   mirror-E: none(waiver:row-four-later-block-cuts)
   anchors: []
   utility: none
   digest: Turns a first later first-occurrence inversion into a value cut. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveLargeConverse
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicCuts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveBlocks

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicCuts
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveThree
open D5.S3.Combinatorics.Nonnesting.NonnestingFourBlocks

theorem later_inversion_cut (w : List ℕ) (n t c : ℕ)
    (hw : w ∈ NonnestingDefs.avoiders n
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
    (ht : 2 ≤ t ∧ t < c ∧ c ≤ n)
    (hct : (w).idxOf c < (w).idxOf t)
    (hbefore : ∀ a b, 1 ≤ a → a < t → t ≤ b → b ≤ n →
      (w).idxOf a < (w).idxOf b) :
    valueCut w (t - 1) := by
  have count_two_positions (a : ℕ) (w : List ℕ)
      (hw : w.count a = 2) :
      (w).idxOf a < secondPos a w ∧
        w[(w).idxOf a]? = some a ∧ w[secondPos a w]? = some a := by
    obtain ⟨u, v, z, hu, hv, _, rfl⟩ := count_two_decomposition a w hw
    have hfirst : ((u ++ [a] ++ v ++ [a] ++ z)).idxOf a = u.length := by
      simp [List.idxOf_append, hu]
    have hsecond : secondPos a (u ++ [a] ++ v ++ [a] ++ z) =
        u.length + 1 + v.length := by
      have hdrop : u.drop (u.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr
        omega
      simp [secondPos, List.idxOf_append, hu, hv, List.drop_append, hdrop]
    constructor
    · rw [hfirst, hsecond]
      omega
    constructor
    · rw [hfirst]
      simp
    · rw [hsecond]
      have hle : ¬ u.length + 1 + v.length < u.length := by omega
      simp [List.getElem?_append, hle]
      have heq : u.length + 1 + v.length - u.length = v.length + 1 := by omega
      rw [heq]
      simp
  have count_two_position_iff (a : ℕ) (w : List ℕ)
      (hw : w.count a = 2) (i : ℕ) :
      w[i]? = some a ↔ i = (w).idxOf a ∨ i = secondPos a w := by
    obtain ⟨u, v, z, hu, hv, hz, rfl⟩ := count_two_decomposition a w hw
    have hfirst : ((u ++ [a] ++ v ++ [a] ++ z)).idxOf a = u.length := by
      simp [List.idxOf_append, hu]
    have hsecond : secondPos a (u ++ [a] ++ v ++ [a] ++ z) =
        u.length + 1 + v.length := by
      have hdrop : u.drop (u.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr
        omega
      simp [secondPos, List.idxOf_append, hu, hv, List.drop_append, hdrop]
    rw [hfirst, hsecond]
    constructor
    · intro hi
      by_cases h0 : i < u.length
      · have hmem : a ∈ u := by
          have : u[i]? = some a := by simpa [List.getElem?_append, h0] using hi
          exact List.mem_of_getElem? this
        exact (hu hmem).elim
      by_cases h1 : i = u.length
      · exact Or.inl h1
      by_cases h2 : i < u.length + 1 + v.length
      · have hmem : a ∈ v := by
          have hi' : (a :: (v ++ a :: z))[i - u.length]? = some a := by
            simpa [List.getElem?_append, h0] using hi
          have heq : i - u.length = (i - u.length - 1) + 1 := by omega
          rw [heq] at hi'
          have hi'' : (v ++ a :: z)[i - u.length - 1]? = some a := by
            simpa using hi'
          have hlt : i - u.length - 1 < v.length := by omega
          have hiv : v[i - u.length - 1]? = some a := by
            simpa [List.getElem?_append, hlt] using hi''
          exact List.mem_of_getElem? hiv
        exact (hv hmem).elim
      by_cases h3 : i = u.length + 1 + v.length
      · exact Or.inr h3
      · have hmem : a ∈ z := by
          have hi' : (a :: (v ++ a :: z))[i - u.length]? = some a := by
            simpa [List.getElem?_append, h0] using hi
          have heq : i - u.length = (i - u.length - 1) + 1 := by omega
          rw [heq] at hi'
          have hi'' : (v ++ a :: z)[i - u.length - 1]? = some a := by
            simpa using hi'
          have hle : ¬ i - u.length - 1 < v.length := by omega
          have hi''' : (a :: z)[i - u.length - 1 - v.length]? = some a := by
            simpa [List.getElem?_append, hle] using hi''
          have heq' : i - u.length - 1 - v.length =
              (i - u.length - 1 - v.length - 1) + 1 := by omega
          rw [heq'] at hi'''
          have hiz : z[i - u.length - 1 - v.length - 1]? = some a := by
            simpa using hi'''
          exact List.mem_of_getElem? hiz
        exact (hz hmem).elim
    · rintro (rfl | rfl)
      · simp at *
      · have h := (count_two_positions a _ hw).2.2
        rw [hsecond] at h
        exact h
  have hbound (x : ℕ) (hx : x ∈ w) : 1 ≤ x ∧ x ≤ n := by
    have hxbase := hw.1.mem_iff.mp hx
    obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hxbase
    have heq : x = i := by simpa using hxi
    subst x
    rw [List.mem_range'_1] at hi
    omega
  have hcount (x : ℕ) (hx : 1 ≤ x ∧ x ≤ n) : w.count x = 2 := by
    apply doubled_count n x w hw.1
    rw [List.mem_range'_1]
    omega
  have hcountAll : ∀ x ∈ w, w.count x = 2 := by
    intro x hx
    exact hcount x (hbound x hx)
  have hsame := (nonnesting_iff_equal_orders w hcountAll).mp
    ⟨hw.2.1, hw.2.2.1⟩
  have h1231 : ¬ NonnestingDefs.Occurs [1, 2, 3, 1] w :=
    hw.2.2.2 _ (by simp)
  have h1312 : ¬ NonnestingDefs.Occurs [1, 3, 1, 2] w :=
    hw.2.2.2 _ (by simp)
  have hsep (a b : ℕ) (ha : 1 ≤ a ∧ a < t)
      (hb : t ≤ b ∧ b ≤ n) : secondPos a w < (w).idxOf b := by
    have hac := hbefore a c ha.1 ha.2 (by omega) ht.2.2
    have hsac : secondPos a w < (w).idxOf c :=
      (separated_three_orders w a t c (hcount a ⟨ha.1, by omega⟩)
        (hcount t ⟨by omega, by omega⟩)
        (hcount c ⟨by omega, ht.2.2⟩)
        ha.2 ht.2.1 hsame h1231 h1312).2.1 hac hct
    by_cases hbt : b = t
    · subst b
      omega
    have htb : t < b := by omega
    by_cases hpos : (w).idxOf b < (w).idxOf t
    · have hab := hbefore a b ha.1 ha.2 hb.1 hb.2
      exact (separated_three_orders w a t b
        (hcount a ⟨ha.1, by omega⟩)
        (hcount t ⟨by omega, by omega⟩)
        (hcount b ⟨by omega, hb.2⟩)
        ha.2 htb hsame h1231 h1312).2.1 hab hpos
    · omega
  apply valueCut_of_separated_indices n (t - 1) w hw.1 (by omega)
  intro i j a b hia hjb hat htb
  have ha : a ∈ w := List.mem_of_getElem? hia
  have hb : b ∈ w := List.mem_of_getElem? hjb
  have hab := hsep a b ⟨(hbound a ha).1, by omega⟩
    ⟨by omega, (hbound b hb).2⟩
  have hai := (count_two_position_iff a w
    (hcount a (hbound a ha)) i).mp hia
  have hbj := (count_two_position_iff b w
    (hcount b (hbound b hb)) j).mp hjb
  have hpa := (count_two_positions a w (hcount a (hbound a ha))).1
  have hpb := (count_two_positions b w (hcount b (hbound b hb))).1
  rcases hai with rfl | rfl <;> rcases hbj with rfl | rfl <;> omega

theorem primitive_later_order (w : List ℕ) (n k : ℕ)
    (hw : w ∈ NonnestingDefs.avoiders n
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
    (hprimitive : primitive w n) (hk : k = 1 ∨ k = 2)
    (hhead : w.head? = some k) :
    ∀ a b, 2 ≤ a → a < b → b ≤ n → (w).idxOf a < (w).idxOf b := by
  have count_two_positions (a : ℕ) (w : List ℕ)
      (hw : w.count a = 2) :
      (w).idxOf a < secondPos a w ∧
        w[(w).idxOf a]? = some a ∧ w[secondPos a w]? = some a := by
    obtain ⟨u, v, z, hu, hv, _, rfl⟩ := count_two_decomposition a w hw
    have hfirst : ((u ++ [a] ++ v ++ [a] ++ z)).idxOf a = u.length := by
      simp [List.idxOf_append, hu]
    have hsecond : secondPos a (u ++ [a] ++ v ++ [a] ++ z) =
        u.length + 1 + v.length := by
      have hdrop : u.drop (u.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr
        omega
      simp [secondPos, List.idxOf_append, hu, hv, List.drop_append, hdrop]
    constructor
    · rw [hfirst, hsecond]
      omega
    constructor
    · rw [hfirst]
      simp
    · rw [hsecond]
      have hle : ¬ u.length + 1 + v.length < u.length := by omega
      simp [List.getElem?_append, hle]
      have heq : u.length + 1 + v.length - u.length = v.length + 1 := by omega
      rw [heq]
      simp
  classical
  have hfirstk : (w).idxOf k = 0 := by
    cases w with
    | nil => simp at hhead
    | cons y ys =>
      have hy : y = k := by simpa using hhead
      subst y
      simp []
  have hcount (x : ℕ) (hx : 1 ≤ x ∧ x ≤ n) : w.count x = 2 := by
    apply doubled_count n x w hw.1
    rw [List.mem_range'_1]
    omega
  have hmem (x : ℕ) (hx : 1 ≤ x ∧ x ≤ n) : x ∈ w :=
    List.mem_of_getElem? (count_two_positions x w (hcount x hx)).2.1
  have hne (a b : ℕ) (ha : 1 ≤ a ∧ a ≤ n)
      (hb : 1 ≤ b ∧ b ≤ n) (hab : a ≠ b) :
      (w).idxOf a ≠ (w).idxOf b := by
    intro heq
    exact hab ((List.idxOf_inj (hmem a ha)).mp heq)
  have hbeforeOne (b : ℕ) (hb : 3 ≤ b ∧ b ≤ n) :
      (w).idxOf 1 < (w).idxOf b := by
    rcases hk with h1 | h2
    · subst k
      rw [hfirstk]
      have hneq := hne 1 b ⟨by omega, by omega⟩
        ⟨by omega, hb.2⟩ (by omega)
      omega
    · subst k
      have hblock := first_block_structure w n 2 hw
        ⟨by omega, by omega⟩ hfirstk
      exact hblock.2 1 b (by omega) (by omega) (by omega) hb.2
  intro a b ha hab hb
  by_contra hnot
  have hba : (w).idxOf b < (w).idxOf a := by
    have hneq := hne a b ⟨by omega, by omega⟩
      ⟨by omega, hb⟩ (by omega)
    omega
  let P : ℕ → Prop := fun t => 2 ≤ t ∧
    ∃ c, t < c ∧ c ≤ n ∧ (w).idxOf c < (w).idxOf t
  have hex : ∃ t, P t := ⟨a, ha, b, hab, hb, hba⟩
  let t := Nat.find hex
  obtain ⟨ht2, c, htc, hcn, hct⟩ : P t := Nat.find_spec hex
  have ht3 : k = 2 → 3 ≤ t := by
    intro hk2
    by_contra hnot3
    have hteq : t = 2 := by omega
    rw [hteq, ← hk2, hfirstk] at hct
    omega
  have hbefore (x y : ℕ) (hx : 1 ≤ x) (hxt : x < t)
      (hty : t ≤ y) (hyn : y ≤ n) : (w).idxOf x < (w).idxOf y := by
    by_cases hx1 : x = 1
    · subst x
      rcases hk with h1 | h2
      · have hfirst1 : (w).idxOf 1 = 0 := h1 ▸ hfirstk
        have hneq := hne 1 y ⟨by omega, by omega⟩
          ⟨by omega, hyn⟩ (by omega)
        omega
      · have hty3 : 3 ≤ y := by have := ht3 h2; omega
        exact hbeforeOne y ⟨hty3, hyn⟩
    · have hx2 : 2 ≤ x := by omega
      have hxy : x < y := by omega
      have hnotBad : ¬ P x := by
        intro hbad
        have hleast : t ≤ x := Nat.find_min' hex hbad
        omega
      have hnotRev : ¬ (w).idxOf y < (w).idxOf x := by
        intro hrev
        apply hnotBad
        exact ⟨hx2, y, hxy, hyn, hrev⟩
      have hneq := hne x y ⟨hx, by omega⟩
        ⟨by omega, hyn⟩ (by omega)
      omega
  have hcut := later_inversion_cut w n t c hw
    ⟨ht2, htc, hcn⟩ hct hbefore
  exact hprimitive (t - 1) (by omega) (by omega) hcut

end D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveBlocks

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveBlocks.later_inversion_cut
#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveBlocks.primitive_later_order
