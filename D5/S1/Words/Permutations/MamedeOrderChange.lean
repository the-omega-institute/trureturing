/- GID: D5/S1/Words/Permutations/MamedeOrderChange
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/MamedeOrderChange
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A reversed pair order in an adjacent-swap word has an actual crossing. -/

import D5.S1.Words.Permutations.MamedeAdjacentWords

namespace D5.S1.Words.Permutations.MamedeOrderChange

open D5.S1.Words.Permutations.MamedeAdjacentWords

def before (σ : Equiv.Perm (Fin (n + 1))) (x y : Fin (n + 1)) : Prop :=
  (σ⁻¹ x).val < (σ⁻¹ y).val

def crossing (σ : Equiv.Perm (Fin (n + 1))) (k : Nat)
    (x y : Fin (n + 1)) : Prop :=
  (σ (position n k) = x ∧ σ (position n (k + 1)) = y) ∨
    (σ (position n k) = y ∧ σ (position n (k + 1)) = x)

theorem order_change_has_crossing (n : Nat)
    (σ : Equiv.Perm (Fin (n + 1))) (w : List Nat) (hw : validWord n w)
    (x y : Fin (n + 1)) (hxy : x ≠ y)
    (hc : before σ x y ≠ before (σ * wordProduct n w) x y) :
    ∃ p k q, w = p ++ k :: q ∧ crossing (σ * wordProduct n p) k x y := by
  have adjacent_order_change (n k : Nat) (hk : 1 ≤ k ∧ k ≤ n)
      (a b : Fin (n + 1)) (hab : a ≠ b)
      (hchange : ((adjacent n k a).val < (adjacent n k b).val) ≠ (a.val < b.val)) :
      (a = position n k ∧ b = position n (k + 1)) ∨
        (a = position n (k + 1) ∧ b = position n k) := by
    let A := position n k
    let B := position n (k + 1)
    have hAv : A.val = k - 1 := by
      simp [A, position, Nat.mod_eq_of_lt (show k - 1 < n + 1 by omega)]
    have hBv : B.val = k := by
      simp [B, position, Nat.mod_eq_of_lt (show k < n + 1 by omega)]
    have hAB : A ≠ B := by intro h; have := congrArg Fin.val h; omega
    have hAdj : adjacent n k = Equiv.swap A B := by simp [adjacent, A, B, position]
    by_cases haA : a = A
    · by_cases hbB : b = B
      · exact Or.inl ⟨haA, hbB⟩
      · have hbA : b ≠ A := by intro h; exact hab (haA.trans h.symm)
        have h : (adjacent n k a).val = B.val := by
          simp [hAdj, haA]
        have h' : (adjacent n k b).val = b.val := by
          rw [hAdj, Equiv.swap_apply_of_ne_of_ne hbA hbB]
        rw [h, h', haA] at hchange
        have hbBv : b.val ≠ B.val := fun he => hbB (Fin.ext he)
        exact False.elim (hchange (propext (by constructor <;> intro hlt <;> omega)))
    · by_cases haB : a = B
      · by_cases hbA : b = A
        · exact Or.inr ⟨haB, hbA⟩
        · have hbB : b ≠ B := by intro h; exact hab (haB.trans h.symm)
          have h : (adjacent n k a).val = A.val := by
            simp [hAdj, haB]
          have h' : (adjacent n k b).val = b.val := by
            rw [hAdj, Equiv.swap_apply_of_ne_of_ne hbA hbB]
          rw [h, h', haB] at hchange
          have hbAv : b.val ≠ A.val := fun he => hbA (Fin.ext he)
          exact False.elim (hchange (propext (by constructor <;> intro hlt <;> omega)))
      · by_cases hbA : b = A
        · have h : (adjacent n k a).val = a.val := by
            rw [hAdj, Equiv.swap_apply_of_ne_of_ne haA haB]
          have h' : (adjacent n k b).val = B.val := by
            simp [hAdj, hbA]
          rw [h, h', hbA] at hchange
          have haAv : a.val ≠ A.val := fun he => haA (Fin.ext he)
          exact False.elim (hchange (propext (by constructor <;> intro hlt <;> omega)))
        · by_cases hbB : b = B
          · have h : (adjacent n k a).val = a.val := by
              rw [hAdj, Equiv.swap_apply_of_ne_of_ne haA haB]
            have h' : (adjacent n k b).val = A.val := by
              simp [hAdj, hbB]
            rw [h, h', hbB] at hchange
            have haBv : a.val ≠ B.val := fun he => haB (Fin.ext he)
            exact False.elim (hchange (propext (by constructor <;> intro hlt <;> omega)))
          · have h : adjacent n k a = a := by
              rw [hAdj, Equiv.swap_apply_of_ne_of_ne haA haB]
            have h' : adjacent n k b = b := by
              rw [hAdj, Equiv.swap_apply_of_ne_of_ne hbA hbB]
            simp [h, h'] at hchange
  have order_change_step (n k : Nat) (hk : 1 ≤ k ∧ k ≤ n)
      (σ : Equiv.Perm (Fin (n + 1))) (x y : Fin (n + 1)) (hxy : x ≠ y)
      (hc : before σ x y ≠ before (σ * adjacent n k) x y) :
      crossing σ k x y := by
    let a := σ⁻¹ x
    let b := σ⁻¹ y
    have hab : a ≠ b := by
      intro h
      apply hxy
      have := congrArg σ h
      simpa [a, b] using this
    have hchange :
        ((adjacent n k a).val < (adjacent n k b).val) ≠ (a.val < b.val) := by
      intro heq
      apply hc
      apply propext
      simpa [before, a, b, mul_inv_rev, Equiv.Perm.mul_apply, adjacent] using heq.symm
    obtain ⟨ha, hb⟩ | ⟨ha, hb⟩ := adjacent_order_change n k hk a b hab hchange
    · left
      constructor
      · have := congrArg σ ha.symm
        simpa [a] using this
      · have := congrArg σ hb.symm
        simpa [b] using this
    · right
      constructor
      · have := congrArg σ hb.symm
        simpa [b] using this
      · have := congrArg σ ha.symm
        simpa [a] using this

  induction w generalizing σ with
  | nil =>
    have : wordProduct n [] = 1 := by simp [wordProduct]
    simp [this] at hc
  | cons k w ih =>
    have hk : 1 ≤ k ∧ k ≤ n := hw k (by simp)
    have htail : validWord n w := by
      intro l hl
      exact hw l (by simp [hl])
    have hprod : wordProduct n (k :: w) = adjacent n k * wordProduct n w := by
      simp [wordProduct]
    by_cases hfirst : before σ x y = before (σ * adjacent n k) x y
    · have hc' : before (σ * adjacent n k) x y ≠
          before ((σ * adjacent n k) * wordProduct n w) x y := by
        intro heq
        apply hc
        calc
          before σ x y = before (σ * adjacent n k) x y := hfirst
          _ = before ((σ * adjacent n k) * wordProduct n w) x y := heq
          _ = before (σ * wordProduct n (k :: w)) x y := by rw [hprod, mul_assoc]
      obtain ⟨p, l, q, hdecomp, hcross⟩ := ih (σ * adjacent n k) htail hc'
      refine ⟨k :: p, l, q, ?_, ?_⟩
      · simp [hdecomp]
      · simpa [wordProduct, mul_assoc] using hcross
    · refine ⟨[], k, w, by simp, ?_⟩
      simpa [wordProduct] using order_change_step n k hk σ x y hxy hfirst

#print axioms order_change_has_crossing

end D5.S1.Words.Permutations.MamedeOrderChange
