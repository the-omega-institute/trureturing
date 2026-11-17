/- GID: D5/S3/Combinatorics/Permutation/Verkama62Run
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/Verkama62Run
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Northeast ear runs preserve connectedness after every single deletion. -/

import D5.S3.Combinatorics.Permutation.Verkama62EarGeometry

/-! Connected induced stages are stable under the two permitted ear additions. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.Verkama62Local

private theorem conn_insert {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (x y : Fin n) (hy : y ∈ S)
    (hc : ((valueGraph π).induce (π '' (S : Set (Fin n)))).Connected)
    (he : (valueGraph π).Adj (π x) (π y)) :
    ((valueGraph π).induce (π '' ((insert x S : Finset _) : Set _))).Connected := by
  classical
  let T := π '' ((insert x S : Finset _) : Set _)
  have hsub : π '' (S : Set (Fin n)) ⊆ T := by
    rintro v ⟨i, hi, rfl⟩
    exact ⟨i, Finset.mem_insert_of_mem hi, rfl⟩
  let root : {v // v ∈ T} := ⟨π y, y, Finset.mem_insert_of_mem hy, rfl⟩
  have reach (v : {v // v ∈ T}) : ((valueGraph π).induce T).Reachable v root := by
    obtain ⟨i, hi, hval⟩ := v.property
    rcases Finset.mem_insert.mp hi with hix | hi
    · have he' : ((valueGraph π).induce T).Adj v root := by
        change (valueGraph π).Adj v.val (π y)
        rw [← hval, hix]
        exact he
      exact he'.reachable
    · have hm := (hc ⟨π i, i, hi, rfl⟩ ⟨π y, y, hy, rfl⟩).map
        ((valueGraph π).induceHomOfLE hsub).toHom
      have heq : ((valueGraph π).induceHomOfLE hsub).toHom ⟨π i, i, hi, rfl⟩ = v :=
        Subtype.ext hval
      rw [heq] at hm
      exact hm
  letI : Nonempty {v // v ∈ T} := ⟨root⟩
  refine ⟨?_⟩
  intro a b
  exact (reach a).trans (reach b).symm

private theorem small_connected {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (hne : S.Nonempty)
    (hsteps : ∀ i ∈ S, ∀ j ∈ S, i = j ∨ (valueGraph π).Adj (π i) (π j) ∨
      ∃ k ∈ S, (valueGraph π).Adj (π i) (π k) ∧ (valueGraph π).Adj (π k) (π j)) :
    ((valueGraph π).induce (π '' (S : Set (Fin n)))).Connected := by
  obtain ⟨r, hr⟩ := hne
  letI : Nonempty {v // v ∈ π '' (S : Set (Fin n))} := ⟨⟨π r, r, hr, rfl⟩⟩
  refine ⟨?_⟩
  rintro ⟨a, i, hi, rfl⟩ ⟨b, j, hj, rfl⟩
  rcases hsteps i hi j hj with rfl | he | ⟨k, hk, hik, hkj⟩
  · exact .refl _
  · exact SimpleGraph.Adj.reachable he
  · exact (SimpleGraph.Adj.reachable (G := (valueGraph π).induce (π '' (S : Set _)))
      (u := ⟨π i, i, hi, rfl⟩) (v := ⟨π k, k, hk, rfl⟩) hik).trans
        (SimpleGraph.Adj.reachable hkj)

private theorem erase_nonempty {n : ℕ} (S : Finset (Fin n)) (a b w : Fin n)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) : (S.erase w).Nonempty := by
  classical
  by_cases h : a = w
  · exact ⟨b, Finset.mem_erase.mpr ⟨by intro h'; exact hab (h.trans h'.symm), hb⟩⟩
  · exact ⟨a, Finset.mem_erase.mpr ⟨h, ha⟩⟩

private theorem triangle_robust {n : ℕ} (π : Equiv.Perm (Fin n)) (a b c : Fin n)
    (hab : a < b) (hbc : b < c) (hba : π b < π a) (hcb : π c < π b) (w : Fin n) :
    ((valueGraph π).induce (π '' ((({a,b,c} : Finset _).erase w) : Set _))).Connected := by
  apply small_connected π _ (erase_nonempty _ a b w (by simp) (by simp) (ne_of_lt hab))
  intro i hi j hj
  have hi' := (Finset.mem_erase.mp hi).2
  have hj' := (Finset.mem_erase.mp hj).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi' hj'
  have eab : (valueGraph π).Adj (π a) (π b) := by rw [value_adj]; simp; omega
  have ebc : (valueGraph π).Adj (π b) (π c) := by rw [value_adj]; simp; omega
  have eac : (valueGraph π).Adj (π a) (π c) := by rw [value_adj]; simp; omega
  rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl <;>
    first | exact .inl rfl | exact .inr (.inl eab) | exact .inr (.inl eab.symm)
          | exact .inr (.inl ebc) | exact .inr (.inl ebc.symm)
          | exact .inr (.inl eac) | exact .inr (.inl eac.symm)

private theorem square_robust {n : ℕ} (π : Equiv.Perm (Fin n)) (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hcv : π c < π d) (hda : π d < π a) (hav : π a < π b) (w : Fin n) :
    ((valueGraph π).induce (π '' ((({a,b,c,d} : Finset _).erase w) : Set _))).Connected := by
  classical
  apply small_connected π _ (erase_nonempty _ a b w (by simp) (by simp) (ne_of_lt hab))
  have eac : (valueGraph π).Adj (π a) (π c) := by rw [value_adj]; simp; omega
  have ead : (valueGraph π).Adj (π a) (π d) := by rw [value_adj]; simp; omega
  have ebc : (valueGraph π).Adj (π b) (π c) := by rw [value_adj]; simp; omega
  have ebd : (valueGraph π).Adj (π b) (π d) := by rw [value_adj]; simp; omega
  have common₁ : ∃ k ∈ ({a,b,c,d} : Finset _).erase w,
      (valueGraph π).Adj (π a) (π k) ∧ (valueGraph π).Adj (π k) (π b) := by
    by_cases h : c = w
    · exact ⟨d, Finset.mem_erase.mpr ⟨by intro h'; have := h.trans h'.symm; omega, by simp⟩,
        ead, ebd.symm⟩
    · exact ⟨c, Finset.mem_erase.mpr ⟨h, by simp⟩, eac, ebc.symm⟩
  have common₂ : ∃ k ∈ ({a,b,c,d} : Finset _).erase w,
      (valueGraph π).Adj (π c) (π k) ∧ (valueGraph π).Adj (π k) (π d) := by
    by_cases h : a = w
    · exact ⟨b, Finset.mem_erase.mpr ⟨by intro h'; have := h.trans h'.symm; omega, by simp⟩,
        ebc.symm, ebd⟩
    · exact ⟨a, Finset.mem_erase.mpr ⟨h, by simp⟩, eac.symm, ead⟩
  intro i hi j hj
  have hi' := (Finset.mem_erase.mp hi).2
  have hj' := (Finset.mem_erase.mp hj).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi' hj'
  have common₁' : ∃ k ∈ ({a,b,c,d} : Finset _).erase w,
      (valueGraph π).Adj (π b) (π k) ∧ (valueGraph π).Adj (π k) (π a) := by
    obtain ⟨k,hk,h₁,h₂⟩ := common₁
    exact ⟨k,hk,h₂.symm,h₁.symm⟩
  have common₂' : ∃ k ∈ ({a,b,c,d} : Finset _).erase w,
      (valueGraph π).Adj (π d) (π k) ∧ (valueGraph π).Adj (π k) (π c) := by
    obtain ⟨k,hk,h₁,h₂⟩ := common₂
    exact ⟨k,hk,h₂.symm,h₁.symm⟩
  rcases hi' with rfl | rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl | rfl <;>
    first | exact .inl rfl | exact .inr (.inl eac) | exact .inr (.inl eac.symm)
          | exact .inr (.inl ead) | exact .inr (.inl ead.symm)
          | exact .inr (.inl ebc) | exact .inr (.inl ebc.symm)
          | exact .inr (.inl ebd) | exact .inr (.inl ebd.symm)
          | exact .inr (.inr common₁) | exact .inr (.inr common₁')
          | exact .inr (.inr common₂) | exact .inr (.inr common₂')

/-- Every permitted ear run remains connected after deleting any ambient point. -/
theorem EarRun.robust {n : ℕ} {π : Equiv.Perm (Fin n)} {S : Finset (Fin n)}
    (run : EarRun π S) (w : Fin n) :
    ((valueGraph π).induce (π '' ((S.erase w : Finset _) : Set _))).Connected := by
  classical
  induction run with
  | triangle a b c hab hbc hba hcb => exact triangle_robust π a b c hab hbc hba hcb w
  | square a b c d hab hbc hcd hcv hda hav =>
    exact square_robust π a b c d hab hbc hcd hcv hda hav w
  | @singleton S run x hx hdegree ih =>
    by_cases hxw : x = w
    · subst w
      rw [Finset.erase_insert_eq_erase]
      exact ih
    · have hmany := hdegree
      obtain ⟨y, hy, hyw⟩ : ∃ y ∈ neighbours π S x, y ≠ w := by
        by_contra h
        have hsub : neighbours π S x ⊆ {w} := by
          intro y hy
          by_contra hne
          exact h ⟨y, hy, by simpa using hne⟩
        have := Finset.card_le_card hsub
        simp only [Finset.card_singleton] at this
        omega
      have hyS := (Finset.mem_filter.mp hy).1
      have he : (valueGraph π).Adj (π x) (π y) := by
        rw [value_adj]; simp only [Equiv.symm_apply_apply]
        rcases (Finset.mem_filter.mp hy).2 with h | h
        · exact .inl ⟨h.2,h.1⟩
        · exact .inr ⟨h.2,h.1⟩
      rw [Finset.erase_insert_of_ne hxw]
      exact conn_insert π (S.erase w) x y (Finset.mem_erase.mpr ⟨hyw, hyS⟩) ih he
  | @double S run e ih =>
    have eux : (valueGraph π).Adj (π e.u) (π e.x) := by
      rw [value_adj]; simp only [Equiv.symm_apply_apply]
      right; exact ⟨e.old_below e.x e.hx e.hxy |>.trans (e.hvy.trans e.hyu), e.hux⟩
    have evy : (valueGraph π).Adj (π e.v) (π e.y) := by
      rw [value_adj]; simp only [Equiv.symm_apply_apply]
      left; exact ⟨e.hvy, (e.old_left e.y e.hy e.hxy.symm).trans (e.hux.trans e.hxv)⟩
    have euv : (valueGraph π).Adj (π e.u) (π e.v) := by
      rw [value_adj]; simp only [Equiv.symm_apply_apply]
      right; exact ⟨e.hvy.trans e.hyu, e.hux.trans e.hxv⟩
    have huv : e.u ≠ e.v := ne_of_lt (e.hux.trans e.hxv)
    by_cases huw : e.u = w
    · have hyw : e.y ≠ w := by intro h; exact e.hu (huw.trans h.symm ▸ e.hy)
      have hvw : e.v ≠ w := fun h => huv (huw.trans h.symm)
      rw [huw, Finset.erase_insert_eq_erase, Finset.erase_insert_of_ne hvw]
      exact conn_insert π (S.erase w) e.v e.y (Finset.mem_erase.mpr ⟨hyw,e.hy⟩) ih evy
    · by_cases hvw : e.v = w
      · have hxw : e.x ≠ w := by intro h; exact e.hv (hvw.trans h.symm ▸ e.hx)
        rw [Finset.erase_insert_of_ne huw, hvw, Finset.erase_insert_eq_erase]
        exact conn_insert π (S.erase w) e.u e.x (Finset.mem_erase.mpr ⟨hxw,e.hx⟩) ih eux
      · by_cases hxw : e.x = w
        · have hyw : e.y ≠ w := by intro h; exact e.hxy (hxw.trans h.symm)
          have h₁ := conn_insert π (S.erase w) e.v e.y
            (Finset.mem_erase.mpr ⟨hyw,e.hy⟩) ih evy
          have h₂ := conn_insert π (insert e.v (S.erase w)) e.u e.v (by simp) h₁ euv
          rw [Finset.erase_insert_of_ne huw, Finset.erase_insert_of_ne hvw]
          exact h₂
        · have h₁ := conn_insert π (S.erase w) e.u e.x
            (Finset.mem_erase.mpr ⟨hxw,e.hx⟩) ih eux
          have h₂ := conn_insert π (insert e.u (S.erase w)) e.v e.u (by simp) h₁ euv.symm
          rw [Finset.erase_insert_of_ne huw, Finset.erase_insert_of_ne hvw, Finset.insert_comm]
          exact h₂

end D5.S3.Combinatorics.Permutation.Verkama62Local
