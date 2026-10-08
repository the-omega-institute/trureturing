/- GID: D5/S3/Combinatorics/DihedralRamsey/NestedSelection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/NestedSelection
   mirror-E: none(waiver:endpoint-sum-selection)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.Order.Preorder.Finite]
   utility: none
   digest: Closed endpoint-sum sets inherit nested matching rank reflections. -/

import D5.S3.Combinatorics.DihedralRamsey.NestedMatching
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.NestedSelection

open DihedralRamseyDefs CyclicRamseyDefs NestedRamseyDefs Finset Classical

/-- A fixed-point-free constant-sum pairing reverses the increasing endpoint enumeration. -/
theorem constant_sum_ordered {n : ℕ} (S : Finset (Fin n)) (d : ℕ)
    (G : SimpleGraph (Fin n))
    (hpair : ∀ x ∈ S, ∃ y ∈ S, x ≠ y ∧ x.val + y.val = d)
    (hedge : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x.val + y.val = d → G.Adj x y) :
    S.card % 2 = 0 ∧ ∀ i j : Fin S.card, i.val + j.val + 1 = S.card →
      G.Adj (S.orderEmbOfFin rfl i) (S.orderEmbOfFin rfl j) := by
  classical
  let e : Fin S.card ≃o S := S.orderIsoOfFin rfl
  let p : S → S := fun x => ⟨(hpair x x.property).choose,
    (hpair x x.property).choose_spec.1⟩
  have hp : ∀ x : S, x.val ≠ (p x).val ∧ x.val.val + (p x).val.val = d := by
    intro x
    exact (hpair x x.property).choose_spec.2
  have anti : StrictAnti p := by
    intro x y hxy
    have hx := (hp x).2
    have hy := (hp y).2
    change (p y).val.val < (p x).val.val
    change x.val.val < y.val.val at hxy
    omega
  let f : Fin S.card → Fin S.card := fun i => e.symm (p (e i))
  have hf : StrictAnti f := e.symm.strictMono.comp_strictAnti (anti.comp_strictMono e.strictMono)
  have rev : ∀ i, f i = i.rev := by
    intro i
    have hh : StrictMono (fun j => (f j).rev) := Fin.rev_strictAnti.comp hf
    have hi := hh.apply_eq (x := i)
    exact Fin.rev_injective (by simpa using hi)
  have hp_rank : ∀ i, p (e i) = e i.rev := by
    intro i
    apply e.symm.injective
    simpa only [f, OrderIso.symm_apply_apply] using rev i
  have even : S.card % 2 = 0 := by
    by_contra h
    have hmod : S.card % 2 = 1 := by omega
    let i : Fin S.card := ⟨S.card / 2, by omega⟩
    have hrev : i.rev = i := by
      apply Fin.ext
      simp only [Fin.val_rev]
      dsimp [i]
      omega
    have hh := (hp (e i)).1
    rw [hp_rank, hrev] at hh
    exact hh rfl
  refine ⟨even, ?_⟩
  intro i j hsum
  have hj : j = i.rev := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  subst j
  exact hedge (e i).val (e i).property (e i.rev).val (e i.rev).property
    (by simpa only [hp_rank] using (hp (e i)).1)
    (by simpa only [hp_rank] using (hp (e i)).2)

/-- Two separated ordered nested matchings form one cyclic nested matching. -/
theorem cyclic_of_separated {a b n : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 0)
    (ht : 0 < a + b) (G : SimpleGraph (Fin n))
    (u : Fin a → Fin n) (v : Fin b → Fin n) (hu : StrictMono u) (hv : StrictMono v)
    (sep : ∀ i j, u i < v j)
    (huedge : ∀ i j, i.val + j.val + 1 = a → G.Adj (u i) (u j))
    (hvedge : ∀ i j, i.val + j.val + 1 = b → G.Adj (v i) (v j)) :
    CyclicEmbeddable (nestMatching (a + b)) G := by
  let ψ : Fin (a + b) → Fin n := fun i =>
    if h : i.val < a then u ⟨i.val, h⟩ else v ⟨i.val - a, by omega⟩
  have hψ : StrictMono ψ := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hlt : i.val < j.val := hij
    dsimp [ψ]
    split_ifs with hia hja
    · exact hu hlt
    · exact sep _ _
    · omega
    · apply hv
      apply Fin.mk_lt_mk.mpr
      omega
  have htot : (a + b) % 2 = 0 := by omega
  apply (NestedMatching.cyclic_iff_reflection ht htot G).mpr
  let c : Fin (a + b) := ⟨if a = 0 then a + b - 1 else a - 1, by split_ifs <;> omega⟩
  have hc : c.val % 2 = 1 := by dsimp [c]; split_ifs <;> omega
  refine ⟨ψ, hψ, c, hc, ?_⟩
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hs : i.val + j.val = c.val ∨ i.val + j.val = c.val + (a + b) := by
    by_cases h : i.val + j.val < a + b
    · rw [Nat.mod_eq_of_lt h] at hij
      exact Or.inl hij
    · have hge : a + b ≤ i.val + j.val := by omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at hij
      right
      omega
  by_cases ha0 : a = 0
  · have hs' : i.val + j.val + 1 = b := by dsimp [c] at hs; simp [ha0] at hs; omega
    have hi' : ¬i.val < a := by omega
    have hj' : ¬j.val < a := by omega
    dsimp [ψ]
    rw [dif_neg hi', dif_neg hj']
    apply hvedge
    change i.val - a + (j.val - a) + 1 = b
    omega
  · have hcv : c.val = a - 1 := by simp [c, ha0]
    rw [hcv] at hs
    by_cases hia : i.val < a <;> by_cases hja : j.val < a
    · have hs' : i.val + j.val + 1 = a := by omega
      dsimp [ψ]
      rw [dif_pos hia, dif_pos hja]
      exact huedge _ _ hs'
    · omega
    · omega
    · dsimp [ψ]
      rw [dif_neg hia, dif_neg hja]
      apply hvedge
      change i.val - a + (j.val - a) + 1 = b
      omega

/-- A closed fixed-point-free endpoint-sum set is a cyclic nested matching. -/
theorem modular_sum_set {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) (c : Fin n)
    (hS : 0 < S.card) (G : SimpleGraph (Fin n))
    (hpair : ∀ x ∈ S, ∃ y ∈ S, x ≠ y ∧ (x.val + y.val) % n = c.val)
    (hedge : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      (x.val + y.val) % n = c.val → G.Adj x y) :
    S.card % 2 = 0 ∧ CyclicEmbeddable (nestMatching S.card) G := by
  classical
  let A := S.filter fun x => x.val ≤ c.val
  let B := S.filter fun x => c.val < x.val
  have sums : ∀ x y : Fin n, (x.val + y.val) % n = c.val →
      x.val + y.val = c.val ∨ x.val + y.val = c.val + n := by
    intro x y h
    have hx := x.isLt
    have hy := y.isLt
    by_cases hlt : x.val + y.val < n
    · exact Or.inl (by simpa [Nat.mod_eq_of_lt hlt] using h)
    · have hge : n ≤ x.val + y.val := by omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h
      right
      omega
  have pairA : ∀ x ∈ A, ∃ y ∈ A, x ≠ y ∧ x.val + y.val = c.val := by
    intro x hx
    obtain ⟨hxS, hxc⟩ := mem_filter.mp hx
    obtain ⟨y, hy, hne, hsum⟩ := hpair x hxS
    have hs := sums x y hsum
    have hxlt := x.isLt
    have hylt := y.isLt
    have hsum' : x.val + y.val = c.val := by omega
    exact ⟨y, mem_filter.mpr ⟨hy, by omega⟩, hne, hsum'⟩
  have pairB : ∀ x ∈ B, ∃ y ∈ B, x ≠ y ∧ x.val + y.val = c.val + n := by
    intro x hx
    obtain ⟨hxS, hxc⟩ := mem_filter.mp hx
    obtain ⟨y, hy, hne, hsum⟩ := hpair x hxS
    have hs := sums x y hsum
    have hxlt := x.isLt
    have hylt := y.isLt
    have hsum' : x.val + y.val = c.val + n := by omega
    exact ⟨y, mem_filter.mpr ⟨hy, by omega⟩, hne, hsum'⟩
  have factsA := constant_sum_ordered A c.val G pairA (by
    intro x hx y hy hne hs
    apply hedge x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 hne
    simp [hs, Nat.mod_eq_of_lt c.isLt])
  have factsB := constant_sum_ordered B (c.val + n) G pairB (by
    intro x hx y hy hne hs
    apply hedge x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 hne
    simp [hs, Nat.mod_eq_of_lt c.isLt])
  have hcard : A.card + B.card = S.card := by
    dsimp [A, B]
    simpa only [not_le] using
      card_filter_add_card_filter_not (s := S) (fun x : Fin n => x.val ≤ c.val)
  have hcopy : CyclicEmbeddable (nestMatching (A.card + B.card)) G := by
    apply cyclic_of_separated factsA.1 factsB.1 (by omega) G
      (A.orderEmbOfFin rfl) (B.orderEmbOfFin rfl)
      (A.orderEmbOfFin rfl).strictMono (B.orderEmbOfFin rfl).strictMono
    · intro i j
      have hi := mem_filter.mp (A.orderEmbOfFin_mem rfl i) |>.2
      have hj := mem_filter.mp (B.orderEmbOfFin_mem rfl j) |>.2
      change (A.orderEmbOfFin rfl i).val < (B.orderEmbOfFin rfl j).val
      omega
    · exact factsA.2
    · exact factsB.2
  rw [hcard] at hcopy
  exact ⟨by omega, hcopy⟩

/-- Any `k` distinct edges of one modular endpoint-sum class give a nested cyclic copy. -/
theorem sum_class_copy {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (G : SimpleGraph (Fin n)) (c : Fin n)
    (hcard : k ≤ (univ.filter fun e : Fin n × Fin n =>
      e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ (e.1.val + e.2.val) % n = c.val).card) :
    CyclicEmbeddable (nestMatching (2 * k)) G := by
  classical
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨P, hP, hPk⟩ := exists_subset_card_eq hcard
  have facts : ∀ e : P, e.val.1 < e.val.2 ∧ G.Adj e.val.1 e.val.2 ∧
      (e.val.1.val + e.val.2.val) % n = c.val := by
    intro e
    exact (mem_filter.mp (hP e.property)).2
  have unique : ∀ x y z : Fin n, (x.val + y.val) % n = c.val →
      (x.val + z.val) % n = c.val → y = z := by
    intro x y z hy hz
    apply add_left_cancel (a := x)
    apply Fin.ext
    simpa only [Fin.val_add] using hy.trans hz.symm
  let f : P × Bool → Fin n := fun e => if e.2 then e.1.val.2 else e.1.val.1
  have hf : Function.Injective f := by
    rintro ⟨p, b⟩ ⟨q, d⟩ h
    have hp := facts p
    have hq := facts q
    cases b <;> cases d
    · change p.val.1 = q.val.1 at h
      have h2 : p.val.2 = q.val.2 := unique p.val.1 _ _ hp.2.2 (by rw [h]; exact hq.2.2)
      congr 1
      exact Subtype.ext (Prod.ext h h2)
    · change p.val.1 = q.val.2 at h
      have h2 : p.val.2 = q.val.1 := unique p.val.1 _ _ hp.2.2 (by
        rw [h, Nat.add_comm]
        exact hq.2.2)
      have hh := hp.1
      rw [h, h2] at hh
      exact False.elim (lt_asymm hh hq.1)
    · change p.val.2 = q.val.1 at h
      have h1 : p.val.1 = q.val.2 := unique p.val.2 _ _
        (by simpa only [Nat.add_comm] using hp.2.2) (by rw [h]; exact hq.2.2)
      have hh := hp.1
      rw [h1, h] at hh
      exact False.elim (lt_asymm hh hq.1)
    · change p.val.2 = q.val.2 at h
      have h1 : p.val.1 = q.val.1 := unique p.val.2 _ _
        (by simpa only [Nat.add_comm] using hp.2.2) (by
          rw [h, Nat.add_comm]
          exact hq.2.2)
      congr 1
      exact Subtype.ext (Prod.ext h1 h)
  let S : Finset (Fin n) := univ.image f
  have size : S.card = 2 * k := by
    rw [card_image_of_injective _ hf]
    simp only [card_univ, Fintype.card_prod, Fintype.card_coe, Fintype.card_bool, hPk]
    omega
  have pair : ∀ x ∈ S, ∃ y ∈ S, x ≠ y ∧ (x.val + y.val) % n = c.val := by
    intro x hx
    obtain ⟨⟨p, b⟩, _, hp⟩ := mem_image.mp hx
    subst x
    have hp' := facts p
    cases b
    · refine ⟨p.val.2, mem_image.mpr ⟨(p, true), mem_univ _, rfl⟩, hp'.1.ne, hp'.2.2⟩
    · refine ⟨p.val.1, mem_image.mpr ⟨(p, false), mem_univ _, rfl⟩, hp'.1.ne.symm, ?_⟩
      simpa [f, Nat.add_comm] using hp'.2.2
  have edges : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      (x.val + y.val) % n = c.val → G.Adj x y := by
    intro x hx y _ _ hsum
    obtain ⟨⟨p, b⟩, _, hp⟩ := mem_image.mp hx
    subst x
    have hp' := facts p
    cases b
    · have hy : y = p.val.2 := unique p.val.1 _ _ hsum hp'.2.2
      exact hy ▸ hp'.2.1
    · have hy : y = p.val.1 := unique p.val.2 _ _ hsum
        (by simpa only [Nat.add_comm] using hp'.2.2)
      exact hy ▸ hp'.2.1.symm
  have hcopy := (modular_sum_set hn S c (by omega) G pair edges).2
  rw [size] at hcopy
  exact hcopy


end D5.S3.Combinatorics.DihedralRamsey.NestedSelection
