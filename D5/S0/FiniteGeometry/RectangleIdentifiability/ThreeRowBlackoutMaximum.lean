/- GID: D5/S0/FiniteGeometry/RectangleIdentifiability/ThreeRowBlackoutMaximum
   generality: I
   mirror-B: D5/B/S0/FiniteGeometry/RectangleIdentifiability/ThreeRowBlackoutMaximum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact maximum valid blackout in every three-row grid of width at least three. -/

import Mathlib.Tactic.ClearExcept
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-
Three-Row conjecture, Arjun Pemmasani, OEIS A397315 and
Blackouts Preserving Rectangle Identifiability on Grid Points,
preliminary note, conjecture `conj:threerow` (Git revision
b9567e4dc1c7cf1e5034569571a9479b1b83dc57).
Independent proof in pinned Mathlib; no upstream Lean code is copied.
The three-row oblique-rectangle classification is known background:
Hector J. Partridge, OEIS A289832, COMMENTS (2017).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.FiniteGeometry.RectangleIdentifiability.ThreeRowBlackoutMaximum

def IsRectangle {m : ℕ} (C : Finset (Fin m × Fin 3)) : Prop :=
  C.card = 4 ∧
  ∃ a b c d : Fin m × Fin 3,
    C = {a, b, c, d} ∧
    (((b.1.val : ℤ) - (a.1.val : ℤ)) *
        ((c.1.val : ℤ) - (a.1.val : ℤ)) +
      ((b.2.val : ℤ) - (a.2.val : ℤ)) *
        ((c.2.val : ℤ) - (a.2.val : ℤ)) = 0) ∧
    (a.1.val : ℤ) + (d.1.val : ℤ) =
      (b.1.val : ℤ) + (c.1.val : ℤ) ∧
    (a.2.val : ℤ) + (d.2.val : ℤ) =
      (b.2.val : ℤ) + (c.2.val : ℤ)

def ValidBlackout {m : ℕ} (S : Finset (Fin m × Fin 3)) : Prop :=
  ∀ C D : Finset (Fin m × Fin 3),
    IsRectangle C → IsRectangle D → C \ S = D \ S → C = D

theorem result :
  ∀ m : ℕ, 3 ≤ m →
    (∃ S : Finset (Fin m × Fin 3),
      ValidBlackout S ∧ S.card = m + 2) ∧
    (∀ S : Finset (Fin m × Fin 3),
      ValidBlackout S → S.card ≤ m + 2) := by
  classical
  intro m hm
  let ax := fun (i j : Fin m) (r s : Fin 3) =>
    ({(i,r), (i,s), (j,r), (j,s)} : Finset (Fin m × Fin 3))
  let dia := fun (i j k : Fin m) =>
    ({(i,1), (j,0), (j,2), (k,1)} : Finset (Fin m × Fin 3))
  have axis_rect (i j : Fin m) (r s : Fin 3) (hij : i ≠ j) (hrs : r ≠ s) :
      IsRectangle (ax i j r s) := by
    refine ⟨?_, (i,r), (i,s), (j,r), (j,s), ?_, ?_, ?_, ?_⟩
    · simp [ax, hij, hrs, Ne.symm hrs]
    · simp [ax]
    · simp
    · simp
    · simp [add_comm]
  have geom (C : Finset (Fin m × Fin 3)) (hC : IsRectangle C) :
      (∃ i j r s, i ≠ j ∧ r ≠ s ∧ C = ax i j r s) ∨
      (∃ i j k, i.val + 1 = j.val ∧ j.val + 1 = k.val ∧ C = dia i j k) := by
    obtain ⟨hcard, ⟨⟨a,ar⟩, ⟨b,br⟩, ⟨c,cr⟩, ⟨d,dr⟩, rfl, hdot, hx, hy⟩⟩ := hC
    dsimp at hdot hx hy
    have hab : (a,ar) ≠ (b,br) := by
      intro he
      have hle := Finset.card_le_three (a := (b,br)) (b := (c,cr)) (c := (d,dr))
      rw [he, Finset.insert_idem] at hcard
      omega
    have hac : (a,ar) ≠ (c,cr) := by
      intro he
      have hle := Finset.card_le_three (a := (b,br)) (b := (c,cr)) (c := (d,dr))
      rw [he, Finset.insert_comm (c,cr) (b,br), Finset.insert_idem] at hcard
      omega
    by_cases hbr : br = ar
    · subst br
      have hp : (b.val : ℤ) - a.val = 0 ∨ (c.val : ℤ) - a.val = 0 := by
        simpa using hdot
      rcases hp with hb | hc
      · have he : b = a := Fin.ext (by omega)
        exact (hab (by simp [he])).elim
      · have he : c = a := Fin.ext (by omega)
        have hd : d = b := Fin.ext (by omega)
        have hr : dr = cr := Fin.ext (by omega)
        subst c; subst d; subst dr
        refine Or.inl ⟨a,b,ar,cr, ?_, ?_, ?_⟩
        · intro h; exact hab (by simp [h])
        · intro h; exact hac (by simp [h])
        · apply Finset.ext; intro x
          simp only [ax, Finset.mem_insert, Finset.mem_singleton] ; tauto
    by_cases hcr : cr = ar
    · subst cr
      have hp : (b.val : ℤ) - a.val = 0 ∨ (c.val : ℤ) - a.val = 0 := by
        simpa using hdot
      rcases hp with hb | hc
      · have he : b = a := Fin.ext (by omega)
        have hd : d = c := Fin.ext (by omega)
        have hr : dr = br := Fin.ext (by omega)
        subst b; subst d; subst dr
        refine Or.inl ⟨a,c,ar,br, ?_, ?_, ?_⟩
        · intro h; exact hac (by simp [h])
        · intro h; exact hab (by simp [h])
        · rfl
      · have he : c = a := Fin.ext (by omega)
        exact (hac (by simp [he])).elim
    have rows :
        (ar = 0 ∧ br = 1 ∧ cr = 1 ∧ dr = 2) ∨
        (ar = 1 ∧ br = 0 ∧ cr = 2 ∧ dr = 1) ∨
        (ar = 1 ∧ br = 2 ∧ cr = 0 ∧ dr = 1) ∨
        (ar = 2 ∧ br = 1 ∧ cr = 1 ∧ dr = 0) := by
      clear ax dia axis_rect hdot hx hcard hab hac hm a b c d
      fin_cases ar <;> fin_cases br <;> fin_cases cr <;> fin_cases dr <;>
        norm_num at * <;> rfl
    rcases rows with ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ |
      ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩
    · clear hcard hab hac hbr hcr hy
      norm_num at hdot
      have hp : ((b.val : ℤ) - a.val) * ((c.val : ℤ) - a.val) = -1 := by omega
      rcases Int.mul_eq_neg_one_iff_eq_one_or_neg_one.mp hp with ⟨hb,hc⟩ | ⟨hb,hc⟩
      · have hd : d = a := Fin.ext (by omega)
        subst d
        exact Or.inr ⟨c, a, b, by omega, by omega, by
          dsimp only [dia] ; clear * - ; apply Finset.ext ; intro x ; simp only
              [Finset.mem_insert, Finset.mem_singleton] ; tauto⟩
      · have hd : d = a := Fin.ext (by omega)
        subst d
        exact Or.inr ⟨b, a, c, by omega, by omega, by
          dsimp only [dia] ; clear * - ; apply Finset.ext ; intro x ; simp only
              [Finset.mem_insert, Finset.mem_singleton] ; tauto⟩
    · clear hcard hab hac hbr hcr hy
      norm_num at hdot
      have hp : ((b.val : ℤ) - a.val) * ((c.val : ℤ) - a.val) = 1 := by omega
      rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hp with ⟨hb,hc⟩ | ⟨hb,hc⟩
      · have hc : c = b := Fin.ext (by omega)
        subst c
        exact Or.inr ⟨a, b, d, by omega, by omega, by
          rfl⟩
      · have hc : c = b := Fin.ext (by omega)
        subst c
        exact Or.inr ⟨d, b, a, by omega, by omega, by
          dsimp only [dia] ; clear * - ; apply Finset.ext ; intro x ; simp only
              [Finset.mem_insert, Finset.mem_singleton] ; tauto⟩
    · clear hcard hab hac hbr hcr hy
      norm_num at hdot
      have hp : ((b.val : ℤ) - a.val) * ((c.val : ℤ) - a.val) = 1 := by omega
      rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hp with ⟨hb,hc⟩ | ⟨hb,hc⟩
      · have hc : c = b := Fin.ext (by omega)
        subst c
        exact Or.inr ⟨a, b, d, by omega, by omega, by
          dsimp only [dia] ; clear * - ; apply Finset.ext ; intro x ; simp only
              [Finset.mem_insert, Finset.mem_singleton] ; tauto⟩
      · have hc : c = b := Fin.ext (by omega)
        subst c
        exact Or.inr ⟨d, b, a, by omega, by omega, by
          dsimp only [dia] ; clear * - ; apply Finset.ext ; intro x ; simp only
              [Finset.mem_insert, Finset.mem_singleton] ; tauto⟩
    · clear hcard hab hac hbr hcr hy
      norm_num at hdot
      have hp : ((b.val : ℤ) - a.val) * ((c.val : ℤ) - a.val) = -1 := by omega
      rcases Int.mul_eq_neg_one_iff_eq_one_or_neg_one.mp hp with ⟨hb,hc⟩ | ⟨hb,hc⟩
      · have hd : d = a := Fin.ext (by omega)
        subst d
        exact Or.inr ⟨c, a, b, by omega, by omega, by
          dsimp only [dia] ; clear * - ; apply Finset.ext ; intro x ; simp only
              [Finset.mem_insert, Finset.mem_singleton] ; tauto⟩
      · have hd : d = a := Fin.ext (by omega)
        subst d
        exact Or.inr ⟨b, a, c, by omega, by omega, by
          dsimp only [dia] ; clear * - ; apply Finset.ext ; intro x ; simp only
              [Finset.mem_insert, Finset.mem_singleton] ; tauto⟩
  have canon (C : Finset (Fin m × Fin 3)) (hC : IsRectangle C) :
      (∃ i j : Fin m, i < j ∧
        (C = ax i j 0 1 ∨ C = ax i j 0 2 ∨ C = ax i j 1 2)) ∨
      (∃ i j k, i.val + 1 = j.val ∧ j.val + 1 = k.val ∧ C = dia i j k) := by
    rcases geom C hC with ⟨i,j,r,s,hij,hrs,rfl⟩ | h
    · left
      have rowcase (i j : Fin m) (hij : i < j) (r s : Fin 3) (hrs : r ≠ s) :
          ∃ k l : Fin m, k < l ∧
            (ax i j r s = ax k l 0 1 ∨ ax i j r s = ax k l 0 2 ∨
             ax i j r s = ax k l 1 2) := by
        refine ⟨i,j,hij,?_⟩
        fin_cases r <;> fin_cases s <;> (try norm_num at hrs)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl (by dsimp only [ax]; clear * -; apply Finset.ext; intro x; simp only
            [Finset.mem_insert, Finset.mem_singleton] ; tauto)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inl (by dsimp only [ax]; clear * -; apply Finset.ext; intro x; simp
            only [Finset.mem_insert, Finset.mem_singleton] ; tauto))
        · exact Or.inr (Or.inr (by dsimp only [ax]; clear * -; apply Finset.ext; intro x; simp
            only [Finset.mem_insert, Finset.mem_singleton] ; tauto))
      rcases lt_or_gt_of_ne hij with h | h
      · exact rowcase i j h r s hrs
      · have he : ax i j r s = ax j i r s := by
          dsimp only [ax]
          clear * -
          apply Finset.ext
          intro x
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [he]
        exact rowcase j i h r s hrs
    · exact Or.inr h
  let L : Finset (Fin m × Fin 3) := Finset.univ.filter (fun p => p.1.val = 0 ∨ p.2 = 0)
  have memL (x : Fin m) (r : Fin 3) : (x,r) ∈ L ↔ x.val = 0 ∨ r = 0 := by
    simp [L]
  have obs (C D : Finset (Fin m × Fin 3)) (h : C \ L = D \ L)
      (x : Fin m) (r : Fin 3) :
      ((x,r) ∈ C ∧ x.val ≠ 0 ∧ r ≠ 0) ↔ ((x,r) ∈ D ∧ x.val ≠ 0 ∧ r ≠ 0) := by
    have he := Finset.ext_iff.mp h (x,r)
    simpa [memL, not_or, and_assoc] using he
  have Lvalid : ValidBlackout L := by
    intro C D hC hD he
    rcases canon C hC with ⟨i,j,hij,hCi⟩ | ⟨i,j,k,hij,hjk,rfl⟩
    · rcases canon D hD with ⟨k,l,hkl,hDk⟩ | ⟨k,l,n,hkl,hln,rfl⟩
      · rcases hCi with rfl | rfl | rfl <;> rcases hDk with rfl | rfl | rfl
        all_goals
          have hi1 := obs _ _ he i 1
          have hi2 := obs _ _ he i 2
          have hj1 := obs _ _ he j 1
          have hj2 := obs _ _ he j 2
          have hk1 := obs _ _ he k 1
          have hk2 := obs _ _ he k 2
          have hl1 := obs _ _ he l 1
          have hl2 := obs _ _ he l 2
          norm_num only [ax, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq,
              Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_natCast, Fin.coe_ofNat_eq_mod,
              Nat.zero_mod, Nat.one_mod, Nat.reduceMod, iff_false, false_iff, iff_true, true_iff,
              not_false_eq_true, not_true_eq_false, not_not, and_true, true_and, or_true, true_or,
              and_false, false_and, or_false, false_or] at hi1 hi2 hj1 hj2 hk1 hk2 hl1 hl2
          clear * - hij hkl hi1 hi2 hj1 hj2 hk1 hk2 hl1 hl2
          have hik : i = k := Fin.ext (by omega)
          have hjl : j = l := Fin.ext (by omega)
          subst k
          subst l
          first | rfl | omega
      · rcases hCi with rfl | rfl | rfl
        all_goals
          have hl1 := obs _ _ he l 1
          have hl2 := obs _ _ he l 2
          have hn1 := obs _ _ he n 1
          have hn2 := obs _ _ he n 2
          norm_num only [ax, dia, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq,
              Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_natCast, Fin.coe_ofNat_eq_mod,
              Nat.zero_mod, Nat.one_mod, Nat.reduceMod, iff_false, false_iff, iff_true, true_iff,
              not_false_eq_true, not_true_eq_false, not_not, and_true, true_and, or_true, true_or,
              and_false, false_and, or_false, false_or] at hl1 hl2 hn1 hn2
          clear * - hkl hln hl1 hl2 hn1 hn2
          omega
    · rcases canon D hD with ⟨l,n,hln,hDl⟩ | ⟨l,n,p,hln,hnp,rfl⟩
      · rcases hDl with rfl | rfl | rfl
        all_goals
          have hj1 := obs _ _ he j 1
          have hj2 := obs _ _ he j 2
          have hk1 := obs _ _ he k 1
          have hk2 := obs _ _ he k 2
          norm_num only [ax, dia, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq,
              Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_natCast, Fin.coe_ofNat_eq_mod,
              Nat.zero_mod, Nat.one_mod, Nat.reduceMod, iff_false, false_iff, iff_true, true_iff,
              not_false_eq_true, not_true_eq_false, not_not, and_true, true_and, or_true, true_or,
              and_false, false_and, or_false, false_or] at hj1 hj2 hk1 hk2
          clear * - hij hjk hj1 hj2 hk1 hk2
          omega
      · have hj2 := obs _ _ he j 2
        norm_num only [dia, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq,
            Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_natCast, Fin.coe_ofNat_eq_mod,
            Nat.zero_mod, Nat.one_mod, Nat.reduceMod, iff_false, false_iff, iff_true, true_iff,
            not_false_eq_true, not_true_eq_false, not_not, and_true, true_and, or_true, true_or,
            and_false, false_and, or_false, false_or] at hj2
        clear * - hij hjk hln hnp hj2
        have hjn : j = n := Fin.ext (by omega)
        have hil : i = l := Fin.ext (by omega)
        have hkp : k = p := Fin.ext (by omega)
        subst l
        subst n
        subst p
        rfl
  have upper (S : Finset (Fin m × Fin 3)) (valid : ValidBlackout S) : S.card ≤ m + 2 := by
    -- The repeated row-pair obstruction is the argument in Pemmasani's two-row
    -- Strip Theorem; hm supplies its third-column hypothesis. The source
    -- difference-set criterion is used through direct finite-set deletion below.
    have pair_unique (r s : Fin 3) (hrs : r ≠ s) (p q : Fin m)
        (hpr : (p,r) ∈ S) (hps : (p,s) ∈ S) (hqr : (q,r) ∈ S) (hqs : (q,s) ∈ S) : p = q := by
      by_contra hpq
      have hh : ({p,q} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
        simp only [Finset.card_univ, Fintype.card_fin]
        exact lt_of_le_of_lt Finset.card_le_two (by omega)
      obtain ⟨z,_,hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hh
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
      have hrect := valid (ax p z r s) (ax q z r s)
        (axis_rect p z r s (Ne.symm hz.1) hrs)
        (axis_rect q z r s (Ne.symm hz.2) hrs) (by
          simp only [ax, Finset.insert_sdiff_of_mem _ hpr, Finset.insert_sdiff_of_mem _ hps,
            Finset.insert_sdiff_of_mem _ hqr, Finset.insert_sdiff_of_mem _ hqs])
      have hmem := Finset.ext_iff.mp hrect (p,r)
      simp only [ax, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
      have hf : p = q ∨ p = z := by tauto
      exact hf.elim hpq (Ne.symm hz.1)
    have triangle (p q r : Fin m)
        (hp0 : (p,0) ∈ S) (hp1 : (p,1) ∈ S)
        (hq0 : (q,0) ∈ S) (hq2 : (q,2) ∈ S)
        (hr1 : (r,1) ∈ S) (hr2 : (r,2) ∈ S) : q = r := by
      by_cases hpq : p = q
      · subst q
        exact pair_unique 1 2 (by decide) p r hp1 hq2 hr1 hr2
      by_cases hqr : q = r
      · exact hqr
      have hrect := valid (ax p q 0 1) (ax r q 1 2)
        (axis_rect p q 0 1 hpq (by decide))
        (axis_rect r q 1 2 (Ne.symm hqr) (by decide)) (by
          simp only [ax, Finset.insert_sdiff_of_mem _ hp0, Finset.insert_sdiff_of_mem _ hp1,
            Finset.insert_sdiff_of_mem _ hq0, Finset.insert_sdiff_of_mem _ hr1,
            Finset.insert_sdiff_of_mem _ hr2]
          rw [Finset.pair_comm (q,1) (q,2), Finset.insert_sdiff_of_mem _ hq2])
      have hmem := Finset.ext_iff.mp hrect (p,0)
      norm_num [ax, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hmem
    let row := fun r : Fin 3 => Finset.univ.filter (fun i : Fin m => (i,r) ∈ S)
    have rowmem (r : Fin 3) (i : Fin m) : i ∈ row r ↔ (i,r) ∈ S := by simp [row]
    have one (r s : Fin 3) (hrs : r ≠ s) : (row r ∩ row s).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro p hp q hq
      simp only [Finset.mem_inter, rowmem] at hp hq
      exact pair_unique r s hrs p q hp.1 hp.2 hq.1 hq.2
    have h01 := one 0 1 (by decide)
    have h02 := one 0 2 (by decide)
    have h12 := one 1 2 (by decide)
    have hover : (row 0 ∩ row 1).card + ((row 0 ∪ row 1) ∩ row 2).card ≤ 2 := by
      by_cases hzero : (row 0 ∩ row 1).card = 0
      · have he : (row 0 ∪ row 1) ∩ row 2 = (row 0 ∩ row 2) ∪ (row 1 ∩ row 2) := by
          ext x; simp only [Finset.mem_inter, Finset.mem_union]; tauto
        rw [he]
        have hb := Finset.card_union_le (row 0 ∩ row 2) (row 1 ∩ row 2)
        omega
      · obtain ⟨p,hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)
        simp only [Finset.mem_inter, rowmem] at hp
        have hsub : ((row 0 ∪ row 1) ∩ row 2).card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro q hq r hr
          simp only [Finset.mem_inter, Finset.mem_union, rowmem] at hq hr
          rcases hq.1 with hq0 | hq1 <;> rcases hr.1 with hr0 | hr1
          · exact pair_unique 0 2 (by decide) q r hq0 hq.2 hr0 hr.2
          · exact triangle p q r hp.1 hp.2 hq0 hq.2 hr1 hr.2
          · exact (triangle p r q hp.1 hp.2 hr0 hr.2 hq1 hq.2).symm
          · exact pair_unique 1 2 (by decide) q r hq1 hq.2 hr1 hr.2
        omega
    have hsum : (row 0).card + (row 1).card + (row 2).card ≤ m + 2 := by
      have he1 := Finset.card_union_add_card_inter (row 0) (row 1)
      have he2 := Finset.card_union_add_card_inter (row 0 ∪ row 1) (row 2)
      have hle : ((row 0 ∪ row 1) ∪ row 2).card ≤ m := by
        exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
      omega
    have hS : S = ((row 0).product ({0} : Finset (Fin 3)) ∪ (row 1).product ({1} : Finset (Fin
        3))) ∪ (row 2).product ({2} : Finset (Fin 3)) := by
      ext ⟨x,r⟩
      fin_cases r <;> simp [row]
    have hd01 : Disjoint ((row 0).product ({0} : Finset (Fin 3))) ((row 1).product ({1} : Finset
        (Fin 3))) := by
      simp [Finset.disjoint_left]
    have hd2 : Disjoint ((row 0).product ({0} : Finset (Fin 3)) ∪ (row 1).product ({1} : Finset
        (Fin 3))) ((row 2).product ({2} : Finset (Fin 3))) := by
      apply Finset.disjoint_union_left.mpr
      constructor <;> simp [Finset.disjoint_left, Fin.ext_iff, Fin.coe_ofNat_eq_mod]
    rw [hS, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd01]
    simpa using hsum
  let z : Fin m := ⟨0, by omega⟩
  have Lshape : L = (Finset.univ : Finset (Fin m)).product ({0} : Finset (Fin 3)) ∪ {(z,1),(z,2)}
      := by
    ext ⟨x,r⟩
    fin_cases r <;>
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.product_eq_sprod, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
    all_goals
      norm_num only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.coe_ofNat_eq_mod,
        Fin.reduceFinMk, z, Nat.reduceMod, and_true, true_and, or_true, true_or,
        and_false, false_and, or_false, false_or]
  have Ldis : Disjoint ((Finset.univ : Finset (Fin m)).product ({0} : Finset (Fin 3)))
      {(z,1),(z,2)} := by
    simp [Finset.disjoint_left, Fin.ext_iff, Fin.coe_ofNat_eq_mod]
  have Lcard : L.card = m + 2 := by
    rw [Lshape, Finset.card_union_of_disjoint Ldis]
    simp [Fin.ext_iff, Fin.coe_ofNat_eq_mod]
  exact ⟨⟨L,Lvalid,Lcard⟩, upper⟩

end D5.S0.FiniteGeometry.RectangleIdentifiability.ThreeRowBlackoutMaximum
