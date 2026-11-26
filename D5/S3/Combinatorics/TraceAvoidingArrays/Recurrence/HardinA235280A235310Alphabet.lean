/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hardin's literal constant-stress alphabet comparisons for A235280 and A235310. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence
import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Alphabet
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega

/-! Literal alphabet comparisons for Hardin's constant-stress rectangles.
Checkerboard complementation and restriction to the smallest symbols give the count at a fixed deficit. -/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet

noncomputable section

private abbrev Grid (M n k : ℕ) := Fin (n + 1) × Fin (k + 1) → Fin (M + 1)

private def Legal {M n k : ℕ} (S : ℕ) (a : Grid M n k) : Prop :=
  ∀ (r : Fin n) (c : Fin k),
    Int.natAbs (((a (r.castSucc, c.castSucc)).val : ℤ) + ((a (r.succ, c.succ)).val : ℤ) -
      (((a (r.castSucc, c.succ)).val : ℤ) + ((a (r.succ, c.castSucc)).val : ℤ))) = S

/-- The number of literal indexed grids with stress S in every contiguous block. -/
def C (M S n k : ℕ) : ℕ := Nat.card {a : Grid M n k // Legal S a}

private def block {M n k : ℕ} (a : Grid M n k) (r : Fin n) (c : Fin k) : ℕ :=
  (a (r.castSucc, c.castSucc)).val + (a (r.castSucc, c.succ)).val +
    (a (r.succ, c.castSucc)).val + (a (r.succ, c.succ)).val

private def Mixed {M n k : ℕ} (d : ℕ) (a : Grid M n k) : Prop :=
  ∀ r c, block a r c = d ∨ block a r c = 4 * M - d

private def Low {M n k : ℕ} (d : ℕ) (a : Grid M n k) : Prop := ∀ r c, block a r c = d

private def High {M n k : ℕ} (d : ℕ) (a : Grid M n k) : Prop :=
  ∀ r c, block a r c = 4 * M - d

private def checker {M n k : ℕ} (a : Grid M n k) : Grid M n k :=
  fun (r, c) => if (r.val + c.val) % 2 = 0 then (a (r, c)).rev else a (r, c)

private theorem checker_involutive {M n k : ℕ} (a : Grid M n k) :
    checker (checker a) = a := by
  funext ⟨r, c⟩
  by_cases h : (r.val + c.val) % 2 = 0 <;> simp [checker, h]

private theorem checker_iff {M d n k : ℕ} (hd : d < M) (a : Grid M n k) :
    Legal (2 * M - d) a ↔ Mixed d (checker a) := by
  unfold Legal Mixed
  refine forall_congr' fun r => forall_congr' fun c => ?_
  rw [Int.natAbs_eq_iff]
  simp only [block, checker, Fin.val_castSucc, Fin.val_succ]
  have h₁ := (a (r.castSucc, c.castSucc)).isLt
  have h₂ := (a (r.castSucc, c.succ)).isLt
  have h₃ := (a (r.succ, c.castSucc)).isLt
  have h₄ := (a (r.succ, c.succ)).isLt
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

private def checkerEquiv (M d n k : ℕ) (hd : d < M) :
    {a : Grid M n k // Legal (2 * M - d) a} ≃ {a : Grid M n k // Mixed d a} where
  toFun a := ⟨checker a.1, (checker_iff hd a.1).mp a.2⟩
  invFun a := ⟨checker a.1, (checker_iff hd (checker a.1)).mpr (by
    rw [checker_involutive]
    exact a.2)⟩
  left_inv a := Subtype.ext (checker_involutive a.1)
  right_inv a := Subtype.ext (checker_involutive a.1)

/-- The unshared entries of adjoining blocks can change the total by at most 2M. -/
private theorem vertical {M d n k : ℕ} (hd : d < M) {a : Grid M (n + 1) k}
    (h : Mixed d a) (r : Fin n) (c : Fin k) :
    block a r.castSucc c = block a r.succ c := by
  have htop := h r.castSucc c
  have hbottom := h r.succ c
  have hedge : r.castSucc.succ = r.succ.castSucc := Fin.ext rfl
  have h₁ := (a (r.castSucc.castSucc, c.castSucc)).isLt
  have h₂ := (a (r.castSucc.castSucc, c.succ)).isLt
  have h₃ := (a (r.succ.succ, c.castSucc)).isLt
  have h₄ := (a (r.succ.succ, c.succ)).isLt
  simp only [block, hedge] at htop hbottom ⊢
  omega

private theorem horizontal {M d n k : ℕ} (hd : d < M) {a : Grid M n (k + 1)}
    (h : Mixed d a) (r : Fin n) (c : Fin k) :
    block a r c.castSucc = block a r c.succ := by
  have hleft := h r c.castSucc
  have hright := h r c.succ
  have hedge : c.castSucc.succ = c.succ.castSucc := Fin.ext rfl
  have h₁ := (a (r.castSucc, c.castSucc.castSucc)).isLt
  have h₂ := (a (r.succ, c.castSucc.castSucc)).isLt
  have h₃ := (a (r.castSucc, c.succ.succ)).isLt
  have h₄ := (a (r.succ, c.succ.succ)).isLt
  simp only [block, hedge] at hleft hright ⊢
  omega

private theorem uniform {M d n k : ℕ} (hd : d < M) {a : Grid M (n + 1) (k + 1)}
    (h : Mixed d a) : Low d a ∨ High d a := by
  have same (r : Fin (n + 1)) (c : Fin (k + 1)) : block a r c = block a 0 0 := by
    calc
      block a r c = block a 0 c :=
        HardinA235289Recurrence.fin_constant (fun row => block a row c)
          (fun row => vertical hd h row c) r
      _ = block a 0 0 :=
        HardinA235289Recurrence.fin_constant (block a 0) (horizontal hd h 0) c
  rcases h 0 0 with low | high
  · exact Or.inl fun r c => (same r c).trans low
  · exact Or.inr fun r c => (same r c).trans high

private def split (M d n k : ℕ) (hd : d < M) :
    {a : Grid M (n + 1) (k + 1) // Mixed d a} ≃
    ({a : Grid M (n + 1) (k + 1) // Low d a} ⊕
      {a : Grid M (n + 1) (k + 1) // High d a}) := by
  classical
  refine
    { toFun := fun a => if h : Low d a.1 then Sum.inl ⟨a.1, h⟩
        else Sum.inr ⟨a.1, (uniform hd a.2).resolve_left h⟩
      invFun := fun
        | .inl a => ⟨a.1, fun r c => Or.inl (a.2 r c)⟩
        | .inr a => ⟨a.1, fun r c => Or.inr (a.2 r c)⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro a
    by_cases h : Low d a.1 <;> simp [h]
  · rintro (a | a)
    · simp [a.2]
    · have h : ¬ Low d a.1 := fun low => by
        have hlow := low 0 0
        have hhigh := a.2 0 0
        omega
      simp [h]

private def complement {M n k : ℕ} (a : Grid M n k) : Grid M n k :=
  fun p => (a p).rev

private theorem complement_involutive {M n k : ℕ} (a : Grid M n k) :
    complement (complement a) = a := by
  funext p
  simp [complement]

private theorem complement_block {M n k : ℕ} (a : Grid M n k) (r : Fin n) (c : Fin k) :
    block (complement a) r c + block a r c = 4 * M := by
  have h₁ := (a (r.castSucc, c.castSucc)).isLt
  have h₂ := (a (r.castSucc, c.succ)).isLt
  have h₃ := (a (r.succ, c.castSucc)).isLt
  have h₄ := (a (r.succ, c.succ)).isLt
  simp only [complement, block, Fin.val_rev]
  omega

private def complementEquiv (M d n k : ℕ) (hd : d < M) :
    {a : Grid M n k // Low d a} ≃ {a : Grid M n k // High d a} where
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

private theorem lowEntry {M d n k : ℕ} (a : {a : Grid M (n + 1) (k + 1) // Low d a})
    (r : Fin (n + 2)) (c : Fin (k + 2)) : (a.1 (r, c)).val < d + 1 := by
  obtain ⟨r', hr⟩ := HardinA235289Alphabet.inPair r
  obtain ⟨c', hc⟩ := HardinA235289Alphabet.inPair c
  have sum := a.2 r' c'
  unfold block at sum
  rcases hr with rfl | rfl <;> rcases hc with rfl | rfl <;> omega

/-- The sum-d grids use only the first d+1 symbols. -/
private def lowEquiv (M d n k : ℕ) (hd : d ≤ M) :
    {a : Grid M (n + 1) (k + 1) // Low d a} ≃
    {a : Grid d (n + 1) (k + 1) // Low d a} where
  toFun a := ⟨fun (r, c) => ⟨(a.1 (r, c)).val, lowEntry a r c⟩, fun r c => a.2 r c⟩
  invFun a := ⟨fun p => Fin.castLE (Nat.succ_le_succ hd) (a.1 p), fun r c => a.2 r c⟩
  left_inv a := Subtype.ext (by
    funext ⟨r, c⟩
    apply Fin.ext
    rfl)
  right_inv a := Subtype.ext (by
    funext ⟨r, c⟩
    apply Fin.ext
    rfl)

/-- At fixed deficit d, the count is twice the count of sum-d grids over Fin (d+1). -/
private theorem count_eq (M d n k : ℕ) (hd : d < M) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    C M (2 * M - d) n k = 2 * Nat.card {a : Grid d n k // Low d a} := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  unfold C
  rw [Nat.card_congr (checkerEquiv M d _ _ hd), Nat.card_congr (split M d n k hd),
    Nat.card_sum, ← Nat.card_congr (complementEquiv M d _ _ hd),
    Nat.card_congr (lowEquiv M d n k (Nat.le_of_lt hd)), two_mul]

/-- OEIS A235280, revision 9, with i=1,2,3. -/
theorem a235280 (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    C 4 5 n k = C 5 7 n k ∧ C 5 7 n k = C 6 9 n k := by
  have h4 : C 4 5 n k = 2 * Nat.card {a : Grid 3 n k // Low 3 a} :=
    count_eq 4 3 n k (by decide) hn hk
  have h5 : C 5 7 n k = 2 * Nat.card {a : Grid 3 n k // Low 3 a} :=
    count_eq 5 3 n k (by decide) hn hk
  have h6 : C 6 9 n k = 2 * Nat.card {a : Grid 3 n k // Low 3 a} :=
    count_eq 6 3 n k (by decide) hn hk
  exact ⟨h4.trans h5.symm, h5.trans h6.symm⟩

/-- OEIS A235310, revision 7, with i=1,2,3. -/
theorem a235310 (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    C 5 6 n k = C 6 8 n k ∧ C 6 8 n k = C 7 10 n k := by
  have h5 : C 5 6 n k = 2 * Nat.card {a : Grid 4 n k // Low 4 a} :=
    count_eq 5 4 n k (by decide) hn hk
  have h6 : C 6 8 n k = 2 * Nat.card {a : Grid 4 n k // Low 4 a} :=
    count_eq 6 4 n k (by decide) hn hk
  have h7 : C 7 10 n k = 2 * Nat.card {a : Grid 4 n k // Low 4 a} :=
    count_eq 7 4 n k (by decide) hn hk
  exact ⟨h5.trans h6.symm, h6.trans h7.symm⟩

end
end D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet
