/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Alphabet
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Alphabet
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hardin's alphabet comparison for literal constant-stress rectangles. -/

/-
result: proof_shape: content
escape_witness: lowEquiv restricts sum-two rectangles to the three smallest symbols
  and embeds those rectangles back into each alphabet without changing any entry.
admission_basis: open-problem-resolution (#34261; Proved)
Direct frozen dependency: D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.T
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence

/-! Hardin's alphabet comparison for literal rectangular arrays. -/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Alphabet

open D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence

noncomputable section

private abbrev Grid (i n k : ℕ) := Fin (n + 1) → Fin (k + 1) → Fin (i + 3)

private def Legal {i n k : ℕ} (a : Grid i n k) : Prop :=
  ∀ (r : Fin n) (c : Fin k),
    Int.natAbs (((a r.castSucc c.castSucc).val : ℤ) + ((a r.succ c.succ).val : ℤ) -
      (((a r.castSucc c.succ).val : ℤ) + ((a r.succ c.castSucc).val : ℤ))) = 2 + 2 * i

private def block {i n k : ℕ} (a : Grid i n k) (r : Fin n) (c : Fin k) : ℕ :=
  (a r.castSucc c.castSucc).val + (a r.castSucc c.succ).val +
    (a r.succ c.castSucc).val + (a r.succ c.succ).val

private def Mixed {i n k : ℕ} (a : Grid i n k) : Prop :=
  ∀ r c, block a r c = 2 ∨ block a r c = 4 * (i + 2) - 2

private def Low {i n k : ℕ} (a : Grid i n k) : Prop := ∀ r c, block a r c = 2

private def High {i n k : ℕ} (a : Grid i n k) : Prop :=
  ∀ r c, block a r c = 4 * (i + 2) - 2

private def checker {i n k : ℕ} (a : Grid i n k) : Grid i n k :=
  fun r c => if (r.val + c.val) % 2 = 0 then (a r c).rev else a r c

private theorem checker_involutive {i n k : ℕ} (a : Grid i n k) :
    checker (checker a) = a := by
  funext r c
  by_cases h : (r.val + c.val) % 2 = 0 <;> simp [checker, h]

private theorem checker_iff {i n k : ℕ} (a : Grid i n k) :
    Legal a ↔ Mixed (checker a) := by
  unfold Legal Mixed
  refine forall_congr' fun r => forall_congr' fun c => ?_
  rw [Int.natAbs_eq_iff]
  simp only [block, checker, Fin.val_castSucc, Fin.val_succ]
  have h₁ := (a r.castSucc c.castSucc).isLt
  have h₂ := (a r.castSucc c.succ).isLt
  have h₃ := (a r.succ c.castSucc).isLt
  have h₄ := (a r.succ c.succ).isLt
  by_cases h : (r.val + c.val) % 2 = 0
  · have hright : (r.val + (c.val + 1)) % 2 ≠ 0 := by omega
    have hdown : (r.val + 1 + c.val) % 2 ≠ 0 := by omega
    have hdiag : (r.val + 1 + (c.val + 1)) % 2 = 0 := by omega
    simp only [h, hright, hdown, hdiag, ite_true, ite_false, Fin.val_rev]
    omega
  · have hright : (r.val + (c.val + 1)) % 2 = 0 := by omega
    have hdown : (r.val + 1 + c.val) % 2 = 0 := by omega
    have hdiag : (r.val + 1 + (c.val + 1)) % 2 ≠ 0 := by omega
    simp only [h, hright, hdown, hdiag, ite_true, ite_false, Fin.val_rev]
    omega

private def checkerEquiv (i n k : ℕ) :
    {a : Grid i n k // Legal a} ≃ {a : Grid i n k // Mixed a} where
  toFun a := ⟨checker a.1, (checker_iff a.1).mp a.2⟩
  invFun a := ⟨checker a.1, (checker_iff (checker a.1)).mpr (by
    rw [checker_involutive]
    exact a.2)⟩
  left_inv a := Subtype.ext (checker_involutive a.1)
  right_inv a := Subtype.ext (checker_involutive a.1)

private theorem vertical {i n k : ℕ} (hi : 1 ≤ i) {a : Grid i (n + 1) k}
    (h : Mixed a) (r : Fin n) (c : Fin k) :
    block a r.castSucc c = block a r.succ c := by
  have htop := h r.castSucc c
  have hbottom := h r.succ c
  have hedge : r.castSucc.succ = r.succ.castSucc := Fin.ext rfl
  have h₁ := (a r.castSucc.castSucc c.castSucc).isLt
  have h₂ := (a r.castSucc.castSucc c.succ).isLt
  have h₃ := (a r.succ.succ c.castSucc).isLt
  have h₄ := (a r.succ.succ c.succ).isLt
  simp only [block, hedge] at htop hbottom ⊢
  omega

private theorem horizontal {i n k : ℕ} (hi : 1 ≤ i) {a : Grid i n (k + 1)}
    (h : Mixed a) (r : Fin n) (c : Fin k) :
    block a r c.castSucc = block a r c.succ := by
  have hleft := h r c.castSucc
  have hright := h r c.succ
  have hedge : c.castSucc.succ = c.succ.castSucc := Fin.ext rfl
  have h₁ := (a r.castSucc c.castSucc.castSucc).isLt
  have h₂ := (a r.succ c.castSucc.castSucc).isLt
  have h₃ := (a r.castSucc c.succ.succ).isLt
  have h₄ := (a r.succ c.succ.succ).isLt
  simp only [block, hedge] at hleft hright ⊢
  omega

private theorem uniform {i n k : ℕ} (hi : 1 ≤ i) {a : Grid i (n + 1) (k + 1)}
    (h : Mixed a) : Low a ∨ High a := by
  have same (r : Fin (n + 1)) (c : Fin (k + 1)) : block a r c = block a 0 0 := by
    calc
      block a r c = block a 0 c :=
        HardinA235289Recurrence.fin_constant (fun row => block a row c)
          (fun row => vertical hi h row c) r
      _ = block a 0 0 :=
        HardinA235289Recurrence.fin_constant (block a 0) (horizontal hi h 0) c
  rcases h 0 0 with low | high
  · exact Or.inl fun r c => (same r c).trans low
  · exact Or.inr fun r c => (same r c).trans high

private def split (i n k : ℕ) (hi : 1 ≤ i) :
    {a : Grid i (n + 1) (k + 1) // Mixed a} ≃
    ({a : Grid i (n + 1) (k + 1) // Low a} ⊕ {a : Grid i (n + 1) (k + 1) // High a}) := by
  classical
  refine
    { toFun := fun a => if h : Low a.1 then Sum.inl ⟨a.1, h⟩
        else Sum.inr ⟨a.1, (uniform hi a.2).resolve_left h⟩
      invFun := fun
        | .inl a => ⟨a.1, fun r c => Or.inl (a.2 r c)⟩
        | .inr a => ⟨a.1, fun r c => Or.inr (a.2 r c)⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro a
    by_cases h : Low a.1 <;> simp [h]
  · rintro (a | a)
    · simp [a.2]
    · have h : ¬ Low a.1 := fun low => by
        have hlow := low 0 0
        have hhigh := a.2 0 0
        omega
      simp [h]

private def complement {i n k : ℕ} (a : Grid i n k) : Grid i n k :=
  fun r c => (a r c).rev

private theorem complement_involutive {i n k : ℕ} (a : Grid i n k) :
    complement (complement a) = a := by
  funext r c
  simp [complement]

private theorem complement_block {i n k : ℕ} (a : Grid i n k) (r : Fin n) (c : Fin k) :
    block (complement a) r c + block a r c = 4 * (i + 2) := by
  have h₁ := (a r.castSucc c.castSucc).isLt
  have h₂ := (a r.castSucc c.succ).isLt
  have h₃ := (a r.succ c.castSucc).isLt
  have h₄ := (a r.succ c.succ).isLt
  simp only [complement, block, Fin.val_rev]
  omega

private def complementEquiv (i n k : ℕ) :
    {a : Grid i n k // Low a} ≃ {a : Grid i n k // High a} where
  toFun a := ⟨complement a.1, fun r c => by
    have total := complement_block a.1 r c
    have low := a.2 r c
    omega⟩
  invFun a := ⟨complement a.1, fun r c => by
    have total := complement_block a.1 r c
    have high := a.2 r c
    omega⟩
  left_inv a := Subtype.ext (complement_involutive a.1)
  right_inv a := Subtype.ext (complement_involutive a.1)

/-- Every index on an axis of length at least two occurs in an adjacent pair. -/
theorem inPair {n : ℕ} (x : Fin (n + 2)) :
    ∃ j : Fin (n + 1), x = j.castSucc ∨ x = j.succ := by
  refine Fin.cases ?_ (fun j => ?_) x
  · exact ⟨0, Or.inl (Fin.ext rfl)⟩
  · exact ⟨j, Or.inr rfl⟩

private theorem lowEntry {i n k : ℕ} (a : {a : Grid i (n + 1) (k + 1) // Low a})
    (r : Fin (n + 2)) (c : Fin (k + 2)) : (a.1 r c).val < 3 := by
  obtain ⟨r', hr⟩ := inPair r
  obtain ⟨c', hc⟩ := inPair c
  have sum := a.2 r' c'
  unfold block at sum
  rcases hr with rfl | rfl <;> rcases hc with rfl | rfl <;> omega

/-- The sum-two arrays are equivalent to sum-two arrays over Fin 3. -/
private def lowEquiv (i n k : ℕ) :
    {a : Grid i (n + 1) (k + 1) // Low a} ≃ {a : Grid 0 (n + 1) (k + 1) // Low a} where
  toFun a := ⟨fun r c => ⟨(a.1 r c).val, lowEntry a r c⟩, fun r c => a.2 r c⟩
  invFun a := ⟨fun r c => Fin.castLE (by omega) (a.1 r c), fun r c => a.2 r c⟩
  left_inv a := Subtype.ext (by
    funext r c
    apply Fin.ext
    rfl)
  right_inv a := Subtype.ext (by
    funext r c
    apply Fin.ext
    rfl)

private theorem count_eq (i n k : ℕ) (hi : 1 ≤ i) :
    Nat.card {a : Grid i (n + 1) (k + 1) // Legal a} =
      2 * Nat.card {a : Grid 0 (n + 1) (k + 1) // Low a} := by
  rw [Nat.card_congr (checkerEquiv i _ _), Nat.card_congr (split i n k hi), Nat.card_sum,
    ← Nat.card_congr (complementEquiv i (n + 1) (k + 1)),
    Nat.card_congr (lowEquiv i n k), two_mul]

/-- The integer-valued count of indexed (n+1) by (k+1) arrays over 0 through i+2
with absolute diagonal difference 2+2i in every contiguous block. -/
def literalCount (n k i : ℕ) : ℤ := Nat.card {a : Grid i n k // Legal a}

/-- The literal count agrees with the four-symbol count at Hardin's four values of i. -/
theorem result (n k i : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) :
    literalCount n k i = HardinA235289Recurrence.T n k := by
  have hi' : 1 ≤ i := by omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  change (Nat.card {a : Grid i (n + 1) (k + 1) // Legal a} : ℤ) = _
  calc
    _ = (↑(2 * Nat.card {a : Grid 0 (n + 1) (k + 1) // Low a}) : ℤ) := by
      rw [count_eq i n k hi']
    _ = 2 * (Nat.card {a : Grid 1 (n + 1) (k + 1) // Low a} : ℤ) := by
      rw [Nat.card_congr (lowEquiv 1 n k)]
      rfl
    _ = HardinA235289Recurrence.T (n + 1) (k + 1) :=
      (HardinA235289Recurrence.original_eq_twice_low n k).symm

end
end D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Alphabet
