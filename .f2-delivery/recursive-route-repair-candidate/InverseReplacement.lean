/- UNCOMPILED private-consumer replacement for the four inverse proofs.
Uses only the definitions and single-endpoint Route evaluation helpers from
RouteStepReplacement.lean. Place all Route/Inverse definitions and evaluator
helpers before these proofs; retain the four original statement names.

Logical check: the even tail has indices i=1..2s+2 with side opposite i mod 2;
the odd body has i=1..2s with the same opposite parity. Thus neither range
collides with the exceptional inverse clauses. The s=0 odd body is empty,
and the mid4/preatil overlaps are handled by their evaluator lemmas.
-/

private theorem even_inverse_route (s j : ℕ) (hj : j < 4 * s + 6) :
    evenInverse s (evenRoute s j) = j := by
  have hmod := Nat.mod_lt j (by decide : 0 < 2)
  by_cases hf : j ≤ 2 * s
  · rw [even_route_front_eq s j hf]
    have hp : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases hp with hp | hp <;>
      simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg]
  · by_cases hm : j ≤ 2 * s + 3
    · have hc : j = 2 * s + 1 ∨ j = 2 * s + 2 ∨ j = 2 * s + 3 := by omega
      rcases hc with rfl | rfl | rfl
      · rw [even_route_mid1_eq]
        simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg]
      · rw [even_route_mid2_eq]
        simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg]
      · rw [even_route_mid3_eq]
        simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg]
    · rw [even_route_tail_eq s j (by omega)]
      have hsum : j - (2 * s + 3) + (2 * s + 3) = j := by omega
      have hp : j % 2 = 0 ∨ j % 2 = 1 := by omega
      rcases hp with hp | hp <;>
        simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg]
          <;> omega

private theorem even_route_inverse (s : ℕ) (p : RawPort)
    (hi : p.1 ≤ 2 * s + 2) (hb : p.2 < 2) :
    evenRoute s (evenInverse s p) = p := by
  rcases p with ⟨i, b⟩
  dsimp only at hi hb
  have hm := Nat.mod_lt i (by decide : 0 < 2)
  have hside : b = 0 ∨ b = 1 := by omega
  rcases hside with rfl | rfl
  · by_cases ht : i = 2 * s + 2
    · subst i
      simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg,
        even_route_mid1_eq]
    · by_cases hp : i % 2 = 0
      · have hinv : evenInverse s (i, 0) = i := by
          simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg]
        rw [hinv, even_route_front_eq s i (by omega)]
        exact Prod.ext rfl hp
      · have hinv : evenInverse s (i, 0) = i + 2 * s + 3 := by
          simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg]
        rw [hinv, even_route_tail_eq s (i + 2 * s + 3) (by omega)]
        apply Prod.ext <;> omega
  · by_cases hz : i = 0
    · subst i
      simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg,
        even_route_mid3_eq]
    · by_cases ht : i = 2 * s + 1
      · subst i
        simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg,
          even_route_mid2_eq]
      · by_cases hp : i % 2 = 1
        · have hinv : evenInverse s (i, 1) = i := by
            simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg]
          rw [hinv, even_route_front_eq s i (by omega)]
          exact Prod.ext rfl hp
        · have hinv : evenInverse s (i, 1) = i + 2 * s + 3 := by
            simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg]
          rw [hinv, even_route_tail_eq s (i + 2 * s + 3) (by omega)]
          apply Prod.ext <;> omega

private theorem odd_inverse_route (s j : ℕ) (hj : j < 4 * s + 8) :
    oddInverse s (oddRoute s j) = j := by
  have hmod := Nat.mod_lt j (by decide : 0 < 2)
  by_cases hf : j ≤ 2 * s
  · rw [odd_route_front_eq s j hf]
    have hp : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases hp with hp | hp <;>
      simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg]
  · by_cases hm : j ≤ 2 * s + 3
    · have hc : j = 2 * s + 1 ∨ j = 2 * s + 2 ∨ j = 2 * s + 3 := by omega
      rcases hc with rfl | rfl | rfl
      · rw [odd_route_mid1_eq]
        simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg]
      · rw [odd_route_mid2_eq]
        simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg]
      · rw [odd_route_mid3_eq]
        simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg]
    · by_cases hb : j < 4 * s + 4
      · rw [odd_route_body_eq s j (by omega) hb]
        have hsum : j - (2 * s + 3) + (2 * s + 3) = j := by omega
        have hp : j % 2 = 0 ∨ j % 2 = 1 := by omega
        rcases hp with hp | hp <;>
          simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg]
            <;> omega
      · have hc : j = 4 * s + 4 ∨ j = 4 * s + 5 ∨ j = 4 * s + 6 ∨
            j = 4 * s + 7 := by omega
        rcases hc with rfl | rfl | rfl | rfl
        · rw [odd_route_last0_eq]
          simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg]
        · rw [odd_route_last1_eq]
          simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg]
        · rw [odd_route_last2_eq]
          simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg]
        · rw [odd_route_last3_eq]
          simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg]

private theorem odd_route_inverse (s : ℕ) (p : RawPort)
    (hi : p.1 ≤ 2 * s + 3) (hb : p.2 < 2) :
    oddRoute s (oddInverse s p) = p := by
  rcases p with ⟨i, b⟩
  dsimp only at hi hb
  have hm := Nat.mod_lt i (by decide : 0 < 2)
  have hside : b = 0 ∨ b = 1 := by omega
  rcases hside with rfl | rfl
  · by_cases ht : i = 2 * s + 3
    · subst i
      simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg,
        odd_route_mid1_eq]
    · by_cases ht' : i = 2 * s + 2
      · subst i
        simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg,
          odd_route_last1_eq]
      · by_cases ht'' : i = 2 * s + 1
        · subst i
          simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg,
            odd_route_last0_eq]
        · by_cases hp : i % 2 = 0
          · have hinv : oddInverse s (i, 0) = i := by
              simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg]
            rw [hinv, odd_route_front_eq s i (by omega)]
            exact Prod.ext rfl hp
          · have hinv : oddInverse s (i, 0) = i + 2 * s + 3 := by
              simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg]
            rw [hinv, odd_route_body_eq s (i + 2 * s + 3) (by omega) (by omega)]
            apply Prod.ext <;> omega
  · by_cases hz : i = 0
    · subst i
      simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg,
        odd_route_mid3_eq]
    · by_cases ht : i = 2 * s + 3
      · subst i
        simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg,
          odd_route_last3_eq]
      · by_cases ht' : i = 2 * s + 2
        · subst i
          simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg,
            odd_route_mid2_eq]
        · by_cases ht'' : i = 2 * s + 1
          · subst i
            simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg,
              odd_route_last2_eq]
          · by_cases hp : i % 2 = 1
            · have hinv : oddInverse s (i, 1) = i := by
                simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg]
              rw [hinv, odd_route_front_eq s i (by omega)]
              exact Prod.ext rfl hp
            · have hinv : oddInverse s (i, 1) = i + 2 * s + 3 := by
                simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg]
              rw [hinv, odd_route_body_eq s (i + 2 * s + 3) (by omega) (by omega)]
              apply Prod.ext <;> omega
