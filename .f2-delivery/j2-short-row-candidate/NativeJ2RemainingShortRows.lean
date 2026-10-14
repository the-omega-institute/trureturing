/- UNCOMPILED consumer snippet. Paste after NativeJ2ReflectedRowChain.
Requires j2_h_lower_domain/deleted generalized by dropping the unused hj;
the full-H unmarked premise retains hj. All adjacencies use survivingGraph.
-/

private theorem j2_circle_native_closed {m : ℕ} (z x g : Configuration m)
    (hx : Circle z x) (hg : g = a m ∨ g = b m) : Circle z (x * g) := by
  exact native_circle_edge_endpoint z (x * g) s(x, x * g)
    ⟨x, g, hx, hg, rfl⟩ (Sym2.mem_mk_right _ _)

private theorem j2_lower_a_uncut {m : ℕ} (hm : 5 ≤ m)
    (j : Fin (m - 2)) (x : Configuration m) (hx : Circle (lowerPort j) x) :
    ¬ F2DeletedEdge m s(x, x * a m) := by
  intro hc
  have he := j2_h_lower_deleted hm j _ ⟨x, a m, hx, Or.inl rfl, rfl⟩ hc
  have hab : a m = b m := j2_edge_generator_unique _ _ _ _ (a_sq m) he
  have hv := congrArg (fun f : Configuration m => (f (Fin.last m)).val) hab
  simp only [a_apply, Fin.val_rev, Fin.val_last, Nat.sub_self, b_last] at hv
  omega

private theorem j2_lower_a_survives {m : ℕ} (hm : 5 ≤ m)
    (j : Fin (m - 2)) (x : Configuration m) (hx : Circle (lowerPort j) x) :
    (survivingGraph m).Adj x (x * a m) :=
  j2_native_survives hm x (a m) (j2_h_lower_domain hm j x hx) (Or.inl rfl)
    (j2_lower_a_uncut hm j x hx) (j2_a_not_marked hm x)

private theorem j2_final_contact_a_survives {m : ℕ} (hm : 5 ≤ m)
    (i : Fin m) (x : Configuration m)
    (hx : Circle (gapAnchor (contactAnchor (j2Contact hm)) i) x) :
    (survivingGraph m).Adj x (x * a m) :=
  j2_native_survives hm x (a m) (j2_h_newgap_domain hm i x hx) (Or.inl rfl)
    (j2_contact_a_uncut hm _ i x hx) (j2_a_not_marked hm x)

private theorem j2_lower_last_zero {m : ℕ} (hm : 5 ≤ m) (j : Fin (m - 2)) :
    ((lowerPort j) (Fin.last m)).val = 0 := by
  change ((a m * c m) (((b m * c m) ^ j.val) (Fin.last m))).val = 0
  rw [native_ac_apply_val (by omega : 3 ≤ m), native_bc_pow_val (by omega : 2 ≤ m)]
  simp (disch := omega) only [Fin.val_last, if_pos, if_neg]

private theorem j2_final_lower_positive_last {m : ℕ} (hm : 5 ≤ m)
    (q : ℕ) (hq : 2 ≤ q) (hq' : q ≤ m) :
    ((lowerPort (j2Contact hm) * finRotate (m + 1) ^ q) (Fin.last m)).val =
      if q = 2 then m else q - 2 := by
  simp only [Equiv.Perm.mul_apply]
  rw [native_lowerPort_val (by omega : 3 ≤ m) (j2Contact hm) _
    (by rw [j2_positive_last_position q (by omega) hq']; omega),
    j2_positive_last_position q (by omega) hq']
  simp only [j2Contact, Fin.val_mk]
  by_cases h2 : q = 2
  · have hmod : (q - 1 + (m - 3)) % m = m - 2 := by
      rw [show q - 1 + (m - 3) = m - 2 by omega,
        Nat.mod_eq_of_lt (by omega : m - 2 < m)]
    rw [hmod, if_pos (by omega : m - 2 < m - 1), if_pos h2]
    omega
  · by_cases h3 : q = 3
    · have hmod : (q - 1 + (m - 3)) % m = m - 1 := by
        rw [show q - 1 + (m - 3) = m - 1 by omega,
          Nat.mod_eq_of_lt (by omega : m - 1 < m)]
      rw [hmod, if_neg (by omega : ¬ m - 1 < m - 1), if_neg h2]
      omega
    · have hmod : (q - 1 + (m - 3)) % m = q - 4 := by
        rw [show q - 1 + (m - 3) = (q - 4) + m by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega : q - 4 < m)]
      rw [hmod, if_pos (by omega : q - 4 < m - 1), if_neg h2]
      omega

private theorem j2_word4_final_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (lowerPort (j2Contact hm) * b m)
      (uWord m (m - 1))).IsChain (survivingGraph m).Adj := by
  apply j2_b_complement_short_chain hm _ _ (by omega)
  · exact j2_h_lower_domain hm _
  · exact j2_lower_a_uncut hm _
  · exact j2_h_lower_deleted hm _
  · intro q hq hq'
    rw [j2_final_lower_positive_last hm q (by omega) hq', j2_lower_last_zero hm]
    split_ifs <;> constructor <;> omega

private theorem j2_word1_final_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (lowerPort (j2Contact hm)) [a m]).IsChain
      (survivingGraph m).Adj := by
  apply scanl_chain_cons
  · exact j2_lower_a_survives hm _ _ (Or.inl rfl)
  · simp

private theorem j2_word2_initial_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (wordStart m 2) [a m]).IsChain
      (survivingGraph m).Adj := by
  rw [j2_word2_initial_positive hm]
  apply scanl_chain_cons
  · apply j2_final_contact_a_survives hm ⟨0, by omega⟩
    simp only [gapAnchor, Fin.val_mk, pow_zero, mul_one]
    left
    rw [rotate_pow_eq_cycle, native_configurationCycle_rotation]
  · simp

private theorem j2_word3_initial_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·) (wordStart m 3) [a m]).IsChain
      (survivingGraph m).Adj := by
  rw [j2_word3_initial_reflected hm]
  apply scanl_chain_cons
  · apply j2_final_contact_a_survives hm ⟨m - 1, by omega⟩
    right
    exact native_configurationCycle_reversal _
  · simp

private theorem j2_gap_m2_reflected_last {m : ℕ} (hm : 5 ≤ m) :
    ((gapAnchor (contactAnchor (j2Contact hm)) ⟨m - 2, by omega⟩ * a m)
      (Fin.last m)).val = m := by
  simp only [Equiv.Perm.mul_apply, a_apply, Fin.val_rev, Fin.val_last,
    Nat.sub_self]
  simp only [gapAnchor, Equiv.Perm.mul_apply, contactAnchor_val,
    native_bc_pow_val (by omega : 2 ≤ m), Fin.val_mk, j2Contact]
  rw [if_pos (by omega : 0 < m), Nat.zero_add,
    Nat.mod_eq_of_lt (by omega : m - 2 < m),
    if_neg (by omega : ¬ m - 2 < m - 3 + 1),
    if_pos (by omega : m - 2 = m - 3 + 1)]

private theorem j2_word2_final_chain {m : ℕ} (hm : 5 ≤ m) :
    (List.scanl (· * ·)
      (gapAnchor (contactAnchor (j2Contact hm)) ⟨m - 2, by omega⟩)
      [a m, b m, a m]).IsChain (survivingGraph m).Adj := by
  let z := gapAnchor (contactAnchor (j2Contact hm)) ⟨m - 2, by omega⟩
  have hza : Circle z (z * a m) :=
    j2_circle_native_closed z z (a m) (Or.inl rfl) (Or.inl rfl)
  have hzab : Circle z (z * a m * b m) :=
    j2_circle_native_closed z (z * a m) (b m) hza (Or.inr rfl)
  change (List.scanl (· * ·) z [a m, b m, a m]).IsChain _
  apply scanl_chain_cons
  · exact j2_final_contact_a_survives hm _ z (Or.inl rfl)
  · apply scanl_chain_cons
    · apply j2_b_single_cut_survives hm z (z * a m) hza
        (j2_h_newgap_domain hm _ _ hza)
        (j2_h_newgap_deleted hm _ (by simp only [Fin.val_mk]; omega))
      · rw [show ((z * a m) (Fin.last m)).val = m from
          j2_gap_m2_reflected_last hm, show (z (Fin.last m)).val = 0 from
          j2_contact_gap_last_zero hm _]
        omega
      · rw [show ((z * a m) (Fin.last m)).val = m from
          j2_gap_m2_reflected_last hm]
        omega
    · apply scanl_chain_cons
      · exact j2_final_contact_a_survives hm _ _ hzab
      · simp
