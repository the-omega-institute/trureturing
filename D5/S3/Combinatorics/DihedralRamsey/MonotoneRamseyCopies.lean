/- GID: D5/S3/Combinatorics/DihedralRamsey/MonotoneRamseyCopies
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/MonotoneRamseyCopies
   mirror-E: none(waiver:shared-monotone-copy-criterion)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Circular gaps characterize monotone copies and constrain saturated cliques. -/

import D5.S3.Combinatorics.DihedralRamsey.MonotoneRamseyDefs
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyPermutations
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyBlocks
import Mathlib.Combinatorics.SimpleGraph.Clique

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey

open DihedralRamseyDefs CyclicRamseyDefs MonotoneRamseyDefs

theorem monotone_dihedral_iff_cyclic {b n : ℕ} (hb : 2 ≤ b)
    (G : SimpleGraph (Fin n)) :
    DihedralEmbeddable (monoPath b) G ↔ CyclicEmbeddable (monoPath b) G := by
  constructor
  · rintro ⟨s, refl, ψ, hψ, he⟩
    cases refl
    · exact ⟨s, ψ, hψ, he⟩
    · refine ⟨s, ψ, hψ, ?_⟩
      intro i j hij
      have hr : (monoPath b).Adj i.rev j.rev := by
        rw [monoPath, SimpleGraph.fromRel_adj] at hij ⊢
        refine ⟨fun h => hij.1 (Fin.rev_injective h), ?_⟩
        have hi := i.isLt
        have hj := j.isLt
        simp only [Fin.val_rev]
        rcases hij.2 with h | h
        · exact Or.inr (by omega)
        · exact Or.inl (by omega)
      have hd : ∀ x : Fin b, dihedralPerm s true x.rev = dihedralPerm s false x := by
        intro x
        apply Fin.ext
        have hx := x.isLt
        simp only [dihedralPerm, Fin.val_rev, Bool.false_eq_true, ↓reduceIte]
        congr 1
        omega
      simpa only [hd] using he i.rev j.rev hr
  · rintro ⟨s, ψ, hψ, he⟩
    exact ⟨s, false, ψ, hψ, he⟩

theorem monotone_cyclic_iff_gaps {b n : ℕ} [NeZero b] (hb : 2 ≤ b)
    (G : SimpleGraph (Fin n)) :
    CyclicEmbeddable (monoPath b) G ↔
      ∃ ψ : Fin b → Fin n, StrictMono ψ ∧ ∃ t : Fin b,
        ∀ i : Fin b, i ≠ t → G.Adj (ψ i) (ψ (i + 1)) := by
  have one : (1 : Fin b).val = 1 := by
    simp [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < b)]
  have rotation : ∀ (s : ℕ) (i : Fin b),
      dihedralPerm s false i = i + (Fin.ofNat b s) := by
    intro s i
    apply Fin.ext
    simp only [dihedralPerm, Bool.false_eq_true, ↓reduceIte, Fin.val_add, Fin.val_ofNat]
    rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  constructor
  · rintro ⟨s, ψ, hψ, he⟩
    let last : Fin b := ⟨b - 1, by omega⟩
    refine ⟨ψ, hψ, dihedralPerm s false last, ?_⟩
    intro i hi
    obtain ⟨j, rfl⟩ := Finite.surjective_of_injective (dihedralPerm_injective b s false) i
    have hjlast : j ≠ last := fun h => hi (congrArg (dihedralPerm s false) h)
    have hj : j.val + 1 < b := by
      have hj := j.isLt
      have hj' : j.val ≠ b - 1 := fun h => hjlast (Fin.ext h)
      omega
    let k : Fin b := ⟨j.val + 1, hj⟩
    have hnext : k = j + 1 := by
      apply Fin.ext
      simp only [Fin.val_add, one]
      exact (Nat.mod_eq_of_lt hj).symm
    have hedge : (monoPath b).Adj j k := by
      rw [monoPath, SimpleGraph.fromRel_adj]
      exact ⟨by intro h; have := congrArg Fin.val h; dsimp [k] at this; omega,
        Or.inl rfl⟩
    have hrot : dihedralPerm s false k = dihedralPerm s false j + 1 := by
      rw [rotation, rotation, hnext]
      exact add_right_comm j 1 (Fin.ofNat b s)
    simpa only [hrot] using he j k hedge
  · rintro ⟨ψ, hψ, t, hg⟩
    refine ⟨t.val + 1, ψ, hψ, ?_⟩
    have rot : ∀ i : Fin b,
        dihedralPerm (t.val + 1) false i = i + (t + 1) := by
      intro i
      rw [rotation]
      congr 1
      apply Fin.ext
      simp only [Fin.val_ofNat, Fin.val_add, one]
    have step : ∀ i j : Fin b, j.val = i.val + 1 →
        G.Adj (ψ (dihedralPerm (t.val + 1) false i))
          (ψ (dihedralPerm (t.val + 1) false j)) := by
      intro i j hij
      have ij : j = i + 1 := by
        apply Fin.ext
        simp only [Fin.val_add, one]
        rw [← hij, Nat.mod_eq_of_lt j.isLt]
      have ine : dihedralPerm (t.val + 1) false i ≠ t := by
        rw [rot]
        intro h
        have h' : i + 1 = 0 := by
          apply add_right_cancel (b := t)
          simpa only [add_assoc, add_comm, add_left_comm, zero_add, add_zero] using h
        have hv := congrArg Fin.val h'
        simp only [Fin.val_add, one, Fin.val_zero] at hv
        have hi := i.isLt
        have hj := j.isLt
        rw [Nat.mod_eq_of_lt (by omega)] at hv
        omega
      have hnext : dihedralPerm (t.val + 1) false j =
          dihedralPerm (t.val + 1) false i + 1 := by
        rw [rot, rot, ij]
        exact add_right_comm i 1 (t + 1)
      simpa only [hnext] using hg _ ine
    intro i j hij
    rw [monoPath, SimpleGraph.fromRel_adj] at hij
    rcases hij.2 with h | h
    · exact step i j h
    · exact (step j i h).symm

/-- Inserting one vertex into a saturated clique forbids both incident circular gaps. -/
theorem saturated_clique_gaps {b n : ℕ} [NeZero b] (hb : 3 ≤ b)
    (G : SimpleGraph (Fin n)) (havoid : ¬CyclicEmbeddable (monoPath b) G)
    (ψ : Fin b → Fin n) (hψ : StrictMono ψ) (j : Fin b)
    (hclique : ∀ u v : Fin b, u ≠ j → v ≠ j → u ≠ v → G.Adj (ψ u) (ψ v)) :
    ¬G.Adj (ψ j) (ψ (j + 1)) ∧ ¬G.Adj (ψ (j - 1)) (ψ j) := by
  have one : (1 : Fin b).val = 1 := by
    simp [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < b)]
  have distinct : ∀ i : Fin b, i ≠ i + 1 := by
    intro i h
    have hv := congrArg Fin.val h
    simp only [Fin.val_add, one] at hv
    have hi := i.isLt
    by_cases hlt : i.val + 1 < b
    · rw [Nat.mod_eq_of_lt hlt] at hv
      omega
    · have heq : i.val + 1 = b := by omega
      rw [heq, Nat.mod_self] at hv
      omega
  constructor
  · intro edge
    apply havoid
    apply (monotone_cyclic_iff_gaps (by omega) G).mpr
    refine ⟨ψ, hψ, j - 1, ?_⟩
    intro i hi
    by_cases hij : i = j
    · subst i; exact edge
    · apply hclique i (i + 1) hij ?_ (distinct i)
      intro h
      apply hi
      rw [← h, add_sub_cancel_right]
  · intro edge
    apply havoid
    apply (monotone_cyclic_iff_gaps (by omega) G).mpr
    refine ⟨ψ, hψ, j, ?_⟩
    intro i hi
    by_cases hij : i + 1 = j
    · have h : i = j - 1 := by rw [← hij, add_sub_cancel_right]
      simpa only [h, sub_add_cancel] using edge
    · exact hclique i (i + 1) hi hij (distinct i)

/-- The two forbidden clique neighbours delimit the circular gap containing the new vertex. -/
theorem saturated_clique_neighbors {b n : ℕ} (hb : 3 ≤ b)
    (G : SimpleGraph (Fin n)) (havoid : ¬CyclicEmbeddable (monoPath b) G)
    (C : Finset (Fin n)) (hC : G.IsClique (C : Set (Fin n))) (hc : C.card = b - 1)
    (x : Fin n) (hx : x ∉ C) :
    ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ ¬G.Adj u x ∧ ¬G.Adj x v ∧
      ((u < x ∧ x < v ∧ ∀ z ∈ C, z ≤ u ∨ v ≤ z) ∨
       (v < u ∧ (x < v ∨ u < x) ∧ ∀ z ∈ C, v ≤ z ∧ z ≤ u)) := by
  classical
  letI : NeZero b := ⟨by omega⟩
  let U := insert x C
  have hU : U.card = b := by
    simp only [U, Finset.card_insert_of_notMem hx, hc]
    omega
  let ψ := U.orderEmbOfFin hU
  let q := (U.orderIsoOfFin hU).symm ⟨x, Finset.mem_insert_self x C⟩
  have hq : ψ q = x :=
    congrArg Subtype.val ((U.orderIsoOfFin hU).apply_symm_apply _)
  have memC : ∀ i : Fin b, i ≠ q → ψ i ∈ C := by
    intro i hi
    have hm := U.orderEmbOfFin_mem hU i
    exact (Finset.mem_insert.mp hm).resolve_left (fun h => hi (ψ.injective (h.trans hq.symm)))
  have clique : ∀ i j : Fin b, i ≠ q → j ≠ q → i ≠ j → G.Adj (ψ i) (ψ j) := by
    intro i j hi hj hij
    exact hC (memC i hi) (memC j hj) (ψ.injective.ne hij)
  obtain ⟨hplus, hminus⟩ := saturated_clique_gaps hb G havoid ψ ψ.strictMono q clique
  let p : Fin b := ⟨if q.val = 0 then b - 1 else q.val - 1, by
    split_ifs <;> have := q.isLt <;> omega⟩
  let r : Fin b := ⟨if q.val + 1 < b then q.val + 1 else 0, by
    split_ifs <;> omega⟩
  have hp : p + 1 = q := by
    apply Fin.ext
    have one : (1 : Fin b).val = 1 := by
      simp [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < b)]
    simp only [Fin.val_add, one]
    dsimp [p]
    split_ifs with he
    · rw [show b - 1 + 1 = b by omega, Nat.mod_self, he]
    · rw [Nat.mod_eq_of_lt (by have := q.isLt; omega)]
      omega
  have hr : r = q + 1 := by
    apply Fin.ext
    have one : (1 : Fin b).val = 1 := by
      simp [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < b)]
    simp only [Fin.val_add, one]
    dsimp [r]
    split_ifs with he
    · exact (Nat.mod_eq_of_lt he).symm
    · have heq : q.val + 1 = b := by have := q.isLt; omega
      rw [heq, Nat.mod_self]
  have hp' : p = q - 1 := by rw [← hp, add_sub_cancel_right]
  have pv : p.val = if q.val = 0 then b - 1 else q.val - 1 := rfl
  have rv : r.val = if q.val + 1 < b then q.val + 1 else 0 := rfl
  have pne : p ≠ q := by
    intro h
    have hv := congrArg Fin.val h
    rw [pv] at hv
    have := q.isLt
    split_ifs at hv <;> omega
  have rne : r ≠ q := by
    intro h
    have hv := congrArg Fin.val h
    rw [rv] at hv
    have := q.isLt
    split_ifs at hv <;> omega
  have pr : p ≠ r := by
    intro h
    have hv := congrArg Fin.val h
    rw [pv, rv] at hv
    have := q.isLt
    split_ifs at hv <;> omega
  refine ⟨ψ p, memC p pne, ψ r, memC r rne, ψ.injective.ne pr, ?_, ?_, ?_⟩
  · simpa only [← hp', hq] using hminus
  · simpa only [← hr, hq] using hplus
  have rank : ∀ z ∈ C, ∃ i : Fin b, ψ i = z ∧ i ≠ q := by
    intro z hz
    let i := (U.orderIsoOfFin hU).symm ⟨z, Finset.mem_insert_of_mem hz⟩
    have hi : ψ i = z :=
      congrArg Subtype.val ((U.orderIsoOfFin hU).apply_symm_apply _)
    exact ⟨i, hi, fun h => hx (by simpa only [← hi, h, hq] using hz)⟩
  by_cases hzero : q.val = 0
  · right
    have hpv : p.val = b - 1 := by simp only [pv, hzero, ↓reduceIte]
    have hrv : r.val = 1 := by rw [rv]; simp [hzero, show 1 < b by omega]
    refine ⟨ψ.strictMono (by show r.val < p.val; omega), Or.inl ?_, ?_⟩
    · rw [← hq]
      exact ψ.strictMono (by show q.val < r.val; omega)
    · intro z hz
      obtain ⟨i, rfl, hi⟩ := rank z hz
      have hiv : i.val ≠ 0 := fun h => hi (Fin.ext (h.trans hzero.symm))
      exact ⟨ψ.monotone (by show r.val ≤ i.val; omega),
        ψ.monotone (by have := i.isLt; show i.val ≤ p.val; omega)⟩
  · by_cases hlast : q.val + 1 = b
    · right
      have hpv : p.val = q.val - 1 := by simp only [pv, hzero, ↓reduceIte]
      have hrv : r.val = 0 := by rw [rv]; simp [hlast]
      refine ⟨ψ.strictMono (by show r.val < p.val; omega), Or.inr ?_, ?_⟩
      · rw [← hq]
        exact ψ.strictMono (by show p.val < q.val; omega)
      · intro z hz
        obtain ⟨i, rfl, hi⟩ := rank z hz
        have hiv : i.val ≠ q.val := fun h => hi (Fin.ext h)
        exact ⟨ψ.monotone (by show r.val ≤ i.val; omega),
          ψ.monotone (by have := i.isLt; show i.val ≤ p.val; omega)⟩
    · left
      have hpv : p.val = q.val - 1 := by simp only [pv, hzero, ↓reduceIte]
      have hrv : r.val = q.val + 1 := by
        rw [rv, if_pos (by have := q.isLt; omega)]
      refine ⟨?_, ?_, ?_⟩
      · rw [← hq]; exact ψ.strictMono (by show p.val < q.val; omega)
      · rw [← hq]; exact ψ.strictMono (by show q.val < r.val; omega)
      · intro z hz
        obtain ⟨i, rfl, hi⟩ := rank z hz
        have hiv : i.val ≠ q.val := fun h => hi (Fin.ext h)
        by_cases hil : i.val < q.val
        · exact Or.inl (ψ.monotone (by show i.val ≤ p.val; omega))
        · exact Or.inr (ψ.monotone (by show r.val ≤ i.val; omega))

theorem saturated_clique_non_neighbors {b n : ℕ} (hb : 3 ≤ b)
    (G : SimpleGraph (Fin n)) (havoid : ¬CyclicEmbeddable (monoPath b) G)
    (C : Finset (Fin n)) (hC : G.IsClique (C : Set (Fin n))) (hc : C.card = b - 1)
    (x : Fin n) (hx : x ∉ C) :
    ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ ¬G.Adj x u ∧ ¬G.Adj x v := by
  obtain ⟨u, hu, v, hv, huv, hux, hxv, _⟩ :=
    saturated_clique_neighbors hb G havoid C hC hc x hx
  exact ⟨u, hu, v, hv, huv, fun h => hux h.symm, hxv⟩

end D5.S3.Combinatorics.DihedralRamsey
