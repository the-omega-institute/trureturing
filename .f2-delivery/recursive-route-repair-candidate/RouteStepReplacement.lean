/- UNCOMPILED private-consumer replacement candidate for RecursivePortBoundary.
Paste within its namespace after oddRoute/oddInverse are declared, remove the
old even_route_steps/odd_route_steps, and move dependent declarations below.
Only one Route term is evaluated by each helper. Step proofs never unfold
two Route expressions and never split the full matching disjunction.
-/

private theorem even_route_front_eq (s j : ℕ) (h : j ≤ 2 * s) :
    evenRoute s j = (j, j % 2) := by
  simp only [evenRoute, if_pos h]

private theorem even_route_tail_eq (s j : ℕ) (h : 2 * s + 3 < j) :
    evenRoute s j = (j - (2 * s + 3), j % 2) := by
  simp (disch := omega) only [evenRoute, if_pos, if_neg]

private theorem even_route_mid0_eq (s : ℕ) : evenRoute s (2 * s) = (2 * s, 0) := by
  rw [even_route_front_eq s (2 * s) (by omega)]
  exact Prod.ext rfl (by omega)

private theorem even_route_mid1_eq (s : ℕ) :
    evenRoute s (2 * s + 1) = (2 * s + 2, 0) := by
  simp (disch := omega) only [evenRoute, if_pos, if_neg]

private theorem even_route_mid2_eq (s : ℕ) :
    evenRoute s (2 * s + 2) = (2 * s + 1, 1) := by
  simp (disch := omega) only [evenRoute, if_pos, if_neg]

private theorem even_route_mid3_eq (s : ℕ) : evenRoute s (2 * s + 3) = (0, 1) := by
  simp (disch := omega) only [evenRoute, if_pos, if_neg]

private theorem even_route_mid4_eq (s : ℕ) : evenRoute s (2 * s + 4) = (1, 0) := by
  rw [even_route_tail_eq s (2 * s + 4) (by omega)]
  apply Prod.ext <;> omega

private theorem even_route_last0_eq (s : ℕ) :
    evenRoute s (4 * s + 4) = (2 * s + 1, 0) := by
  rw [even_route_tail_eq s (4 * s + 4) (by omega)]
  apply Prod.ext <;> omega

private theorem even_route_last1_eq (s : ℕ) :
    evenRoute s (4 * s + 5) = (2 * s + 2, 1) := by
  rw [even_route_tail_eq s (4 * s + 5) (by omega)]
  apply Prod.ext <;> omega

private theorem odd_route_front_eq (s j : ℕ) (h : j ≤ 2 * s) :
    oddRoute s j = (j, j % 2) := by
  simp only [oddRoute, if_pos h]

private theorem odd_route_body_eq (s j : ℕ)
    (h : 2 * s + 3 < j) (h' : j < 4 * s + 4) :
    oddRoute s j = (j - (2 * s + 3), j % 2) := by
  simp (disch := omega) only [oddRoute, if_pos, if_neg]

private theorem odd_route_mid0_eq (s : ℕ) : oddRoute s (2 * s) = (2 * s, 0) := by
  rw [odd_route_front_eq s (2 * s) (by omega)]
  exact Prod.ext rfl (by omega)

private theorem odd_route_mid1_eq (s : ℕ) :
    oddRoute s (2 * s + 1) = (2 * s + 3, 0) := by
  simp (disch := omega) only [oddRoute, if_pos, if_neg]

private theorem odd_route_mid2_eq (s : ℕ) :
    oddRoute s (2 * s + 2) = (2 * s + 2, 1) := by
  simp (disch := omega) only [oddRoute, if_pos, if_neg]

private theorem odd_route_mid3_eq (s : ℕ) : oddRoute s (2 * s + 3) = (0, 1) := by
  simp (disch := omega) only [oddRoute, if_pos, if_neg]

private theorem odd_route_mid4_eq (s : ℕ) : oddRoute s (2 * s + 4) = (1, 0) := by
  by_cases hs : s = 0
  · subst s
    rfl
  · rw [odd_route_body_eq s (2 * s + 4) (by omega) (by omega)]
    apply Prod.ext <;> omega

private theorem odd_route_pretail_eq (s : ℕ) :
    oddRoute s (4 * s + 3) = (2 * s, 1) := by
  by_cases hs : s = 0
  · subst s
    rfl
  · rw [odd_route_body_eq s (4 * s + 3) (by omega) (by omega)]
    apply Prod.ext <;> omega

private theorem odd_route_last0_eq (s : ℕ) :
    oddRoute s (4 * s + 4) = (2 * s + 1, 0) := by
  simp (disch := omega) only [oddRoute, if_pos, if_neg]

private theorem odd_route_last1_eq (s : ℕ) :
    oddRoute s (4 * s + 5) = (2 * s + 2, 0) := by
  simp (disch := omega) only [oddRoute, if_pos, if_neg]

private theorem odd_route_last2_eq (s : ℕ) :
    oddRoute s (4 * s + 6) = (2 * s + 1, 1) := by
  simp (disch := omega) only [oddRoute, if_pos, if_neg]

private theorem odd_route_last3_eq (s : ℕ) :
    oddRoute s (4 * s + 7) = (2 * s + 3, 1) := by
  simp (disch := omega) only [oddRoute, if_pos, if_neg]

private theorem seam_forward (k i : ℕ) (h : i < k) :
    internalSeam k (i, 1) (i + 1, 0) := Or.inl ⟨rfl, rfl, h, rfl⟩

private theorem seam_reverse (k i : ℕ) (h : i < k) :
    internalSeam k (i + 1, 0) (i, 1) := Or.inr ⟨rfl, rfl, h, rfl⟩

private theorem even_ladder_forward (k i : ℕ) (hk : 3 ≤ k) (hi : i ≤ k - 3) :
    evenBoundary k (i, 0) (i + 1, 1) :=
  Or.inl ⟨hk, Or.inl ⟨rfl, rfl, hi, rfl⟩⟩

private theorem odd_ladder_forward (k i : ℕ) (hk : 4 ≤ k) (hi : i ≤ k - 4) :
    oddBoundary k (i, 0) (i + 1, 1) :=
  Or.inl ⟨hk, Or.inl ⟨rfl, rfl, hi, rfl⟩⟩

private theorem even_route_boundary_step (s j : ℕ)
    (hj : j + 1 < 4 * s + 6) (hp : j % 2 = 0) :
    evenBoundary (2 * s + 2) (evenRoute s j) (evenRoute s (j + 1)) := by
  have hp' : (j + 1) % 2 = 1 := by omega
  by_cases hf : j < 2 * s
  · rw [even_route_front_eq s j (by omega),
      even_route_front_eq s (j + 1) (by omega), hp, hp']
    exact even_ladder_forward _ _ (by omega) (by omega)
  · by_cases hm : j ≤ 2 * s + 3
    · have hc : j = 2 * s ∨ j = 2 * s + 1 ∨ j = 2 * s + 2 ∨
          j = 2 * s + 3 := by omega
      rcases hc with rfl | rfl | rfl | rfl
      · rw [even_route_mid0_eq, even_route_mid1_eq]
        exact Or.inr (Or.inl (Or.inl ⟨Prod.ext (by omega) rfl, rfl⟩))
      · omega
      · rw [even_route_mid2_eq,
          show 2 * s + 2 + 1 = 2 * s + 3 by omega, even_route_mid3_eq]
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Prod.ext (by omega) rfl, rfl⟩)))
      · omega
    · by_cases hl : j = 4 * s + 4
      · subst j
        rw [even_route_last0_eq,
          show 4 * s + 4 + 1 = 4 * s + 5 by omega, even_route_last1_eq]
        exact Or.inr (Or.inr (Or.inl (Or.inl ⟨Prod.ext (by omega) rfl, rfl⟩)))
      · have hn : j + 1 - (2 * s + 3) = (j - (2 * s + 3)) + 1 := by omega
        rw [even_route_tail_eq s j (by omega),
          even_route_tail_eq s (j + 1) (by omega), hp, hp', hn]
        exact even_ladder_forward _ _ (by omega) (by omega)

private theorem even_route_seam_step (s j : ℕ)
    (hj : j + 1 < 4 * s + 6) (hp : j % 2 = 1) :
    internalSeam (2 * s + 2) (evenRoute s j) (evenRoute s (j + 1)) := by
  have hp' : (j + 1) % 2 = 0 := by omega
  by_cases hf : j < 2 * s
  · rw [even_route_front_eq s j (by omega),
      even_route_front_eq s (j + 1) (by omega), hp, hp']
    exact seam_forward _ _ (by omega)
  · by_cases hm : j ≤ 2 * s + 3
    · have hc : j = 2 * s ∨ j = 2 * s + 1 ∨ j = 2 * s + 2 ∨
          j = 2 * s + 3 := by omega
      rcases hc with rfl | rfl | rfl | rfl
      · omega
      · rw [even_route_mid1_eq,
          show 2 * s + 1 + 1 = 2 * s + 2 by omega, even_route_mid2_eq]
        exact seam_reverse _ _ (by omega)
      · omega
      · rw [even_route_mid3_eq,
          show 2 * s + 3 + 1 = 2 * s + 4 by omega, even_route_mid4_eq]
        exact seam_forward _ _ (by omega)
    · have hn : j + 1 - (2 * s + 3) = (j - (2 * s + 3)) + 1 := by omega
      rw [even_route_tail_eq s j (by omega),
        even_route_tail_eq s (j + 1) (by omega), hp, hp', hn]
      exact seam_forward _ _ (by omega)

private theorem even_route_steps (s j : ℕ) (hj : j + 1 < 4 * s + 6) :
    (j % 2 = 0 → evenBoundary (2 * s + 2) (evenRoute s j) (evenRoute s (j + 1))) ∧
      (j % 2 = 1 → internalSeam (2 * s + 2) (evenRoute s j) (evenRoute s (j + 1))) :=
  ⟨even_route_boundary_step s j hj, even_route_seam_step s j hj⟩

private theorem odd_route_boundary_step (s j : ℕ)
    (hj : j + 1 < 4 * s + 8) (hp : j % 2 = 0) :
    oddBoundary (2 * s + 3) (oddRoute s j) (oddRoute s (j + 1)) := by
  have hp' : (j + 1) % 2 = 1 := by omega
  by_cases hf : j < 2 * s
  · rw [odd_route_front_eq s j (by omega),
      odd_route_front_eq s (j + 1) (by omega), hp, hp']
    exact odd_ladder_forward _ _ (by omega) (by omega)
  · by_cases hm : j ≤ 2 * s + 3
    · have hc : j = 2 * s ∨ j = 2 * s + 1 ∨ j = 2 * s + 2 ∨
          j = 2 * s + 3 := by omega
      rcases hc with rfl | rfl | rfl | rfl
      · rw [odd_route_mid0_eq, odd_route_mid1_eq]
        exact Or.inr (Or.inr (Or.inl (Or.inl ⟨Prod.ext (by omega) rfl, rfl⟩)))
      · omega
      · rw [odd_route_mid2_eq,
          show 2 * s + 2 + 1 = 2 * s + 3 by omega, odd_route_mid3_eq]
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨Prod.ext (by omega) rfl, rfl⟩))))
      · omega
    · by_cases hb : j < 4 * s + 3
      · have hn : j + 1 - (2 * s + 3) = (j - (2 * s + 3)) + 1 := by omega
        rw [odd_route_body_eq s j (by omega) (by omega),
          odd_route_body_eq s (j + 1) (by omega) (by omega), hp, hp', hn]
        exact odd_ladder_forward _ _ (by omega) (by omega)
      · have hc : j = 4 * s + 3 ∨ j = 4 * s + 4 ∨ j = 4 * s + 5 ∨
            j = 4 * s + 6 := by omega
        rcases hc with rfl | rfl | rfl | rfl
        · omega
        · rw [odd_route_last0_eq,
            show 4 * s + 4 + 1 = 4 * s + 5 by omega, odd_route_last1_eq]
          exact Or.inr (Or.inl (Or.inl
            ⟨Prod.ext (by omega) rfl, Prod.ext (by omega) rfl⟩))
        · omega
        · rw [odd_route_last2_eq,
            show 4 * s + 6 + 1 = 4 * s + 7 by omega, odd_route_last3_eq]
          exact Or.inr (Or.inr (Or.inr
            (Or.inl (Or.inl ⟨Prod.ext (by omega) rfl, rfl⟩))))

private theorem odd_route_seam_step (s j : ℕ)
    (hj : j + 1 < 4 * s + 8) (hp : j % 2 = 1) :
    internalSeam (2 * s + 3) (oddRoute s j) (oddRoute s (j + 1)) := by
  have hp' : (j + 1) % 2 = 0 := by omega
  by_cases hf : j < 2 * s
  · rw [odd_route_front_eq s j (by omega),
      odd_route_front_eq s (j + 1) (by omega), hp, hp']
    exact seam_forward _ _ (by omega)
  · by_cases hm : j ≤ 2 * s + 3
    · have hc : j = 2 * s ∨ j = 2 * s + 1 ∨ j = 2 * s + 2 ∨
          j = 2 * s + 3 := by omega
      rcases hc with rfl | rfl | rfl | rfl
      · omega
      · rw [odd_route_mid1_eq,
          show 2 * s + 1 + 1 = 2 * s + 2 by omega, odd_route_mid2_eq]
        exact seam_reverse _ _ (by omega)
      · omega
      · rw [odd_route_mid3_eq,
          show 2 * s + 3 + 1 = 2 * s + 4 by omega, odd_route_mid4_eq]
        exact seam_forward _ _ (by omega)
    · by_cases hb : j < 4 * s + 3
      · have hn : j + 1 - (2 * s + 3) = (j - (2 * s + 3)) + 1 := by omega
        rw [odd_route_body_eq s j (by omega) (by omega),
          odd_route_body_eq s (j + 1) (by omega) (by omega), hp, hp', hn]
        exact seam_forward _ _ (by omega)
      · have hc : j = 4 * s + 3 ∨ j = 4 * s + 4 ∨ j = 4 * s + 5 ∨
            j = 4 * s + 6 := by omega
        rcases hc with rfl | rfl | rfl | rfl
        · rw [odd_route_pretail_eq,
            show 4 * s + 3 + 1 = 4 * s + 4 by omega, odd_route_last0_eq]
          exact seam_forward _ _ (by omega)
        · omega
        · rw [odd_route_last1_eq,
            show 4 * s + 5 + 1 = 4 * s + 6 by omega, odd_route_last2_eq]
          exact seam_reverse _ _ (by omega)
        · omega

private theorem odd_route_steps (s j : ℕ) (hj : j + 1 < 4 * s + 8) :
    (j % 2 = 0 → oddBoundary (2 * s + 3) (oddRoute s j) (oddRoute s (j + 1))) ∧
      (j % 2 = 1 → internalSeam (2 * s + 3) (oddRoute s j) (oddRoute s (j + 1))) :=
  ⟨odd_route_boundary_step s j hj, odd_route_seam_step s j hj⟩
