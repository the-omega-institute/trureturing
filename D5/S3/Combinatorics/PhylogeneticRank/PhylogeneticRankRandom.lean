/- GID: D5/S3/Combinatorics/PhylogeneticRank/PhylogeneticRankRandom
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PhylogeneticRank/PhylogeneticRankRandom
   mirror-E: none(waiver:finite-random-graph-construction)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Finite edge selection and cycle deletion produce sparse-independence graphs. -/

import Mathlib.Tactic
import D5.S3.Combinatorics.PhylogeneticRank.PhylogeneticRankDeletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PhylogeneticRank.PhylogeneticRankRandom

open scoped BigOperators
open SimpleGraph

/-- Explicit polynomial-size blocks have no short cycles and small independence number. -/
theorem exists_good_block (t : ℕ) (ht : 16 ≤ t) :
    ∃ H : SimpleGraph (Fin (t ^ 9)), H.CliqueFree 3 ∧
      (∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        H.Adj a b → H.Adj b c → H.Adj c d → H.Adj d a → False) ∧
      H.indepNum ≤ 12 * t ^ 8 := by
  classical
  have finite_selection {E C I : Type} [Fintype E] [Fintype C] [Fintype I]
      (cycles : C → Finset E) (required : I → Finset E) (p r : ℝ)
      (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 < r)
      (hbudget : (∑ c, p ^ (cycles c).card) / r +
        (∑ i, (1 - p) ^ (required i).card) < 1) :
      ∃ x : E → Bool,
        ((Finset.univ.filter fun c => ∀ e ∈ cycles c, x e = true).card : ℝ) < r ∧
        ∀ i, ∃ e ∈ required i, x e = true := by
    classical
    let w : (E → Bool) → ℝ := fun x => ∏ e, if x e then p else 1 - p
    have hw (x : E → Bool) : 0 ≤ w x := by
      exact Finset.prod_nonneg fun e _ => by split_ifs <;> linarith
    have htotal : ∑ x, w x = 1 := by
      rw [show (∑ x, w x) = ∑ x : E → Bool, ∏ e, if x e then p else 1 - p from rfl]
      rw [← Fintype.prod_sum (fun (_ : E) (b : Bool) =>
        if b then p else 1 - p)]
      simp
    have hpattern (A : Finset E) (b : Bool) :
        (∑ x : E → Bool, w x * if ∀ e ∈ A, x e = b then 1 else 0) =
          (if b then p else 1 - p) ^ A.card := by
      let g : E → Bool → ℝ := fun e t =>
        if e ∈ A ∧ t ≠ b then 0 else if t then p else 1 - p
      have hg (x : E → Bool) :
          (∏ e, g e (x e)) = w x * if ∀ e ∈ A, x e = b then 1 else 0 := by
        by_cases hx : ∀ e ∈ A, x e = b
        · simp only [if_pos hx, mul_one]
          apply Finset.prod_congr rfl
          intro e _
          simp only [g]
          rw [if_neg]
          exact fun h => h.2 (hx e h.1)
        · simp only [if_neg hx, mul_zero]
          push Not at hx
          obtain ⟨e, he, hne⟩ := hx
          exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [g, he, hne])
      rw [show (∑ x : E → Bool, w x * if ∀ e ∈ A, x e = b then 1 else 0) =
          ∑ x : E → Bool, ∏ e, g e (x e) from
        Finset.sum_congr rfl fun x _ => (hg x).symm]
      rw [← Fintype.prod_sum]
      have hs (e : E) : (∑ t : Bool, g e t) =
          if e ∈ A then (if b then p else 1 - p) else 1 := by
        cases b <;> by_cases he : e ∈ A <;> simp [g, he]
      simp_rw [hs]
      rw [Finset.prod_ite]
      simp
    let count : (E → Bool) → ℝ := fun x =>
      ∑ c : C, if ∀ e ∈ cycles c, x e = true then 1 else 0
    let failures : (E → Bool) → ℝ := fun x =>
      ∑ i : I, if ∀ e ∈ required i, x e = false then 1 else 0
    have hcf : ∑ x, w x * count x = ∑ c, p ^ (cycles c).card := by
      simp only [count, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      simpa using hpattern (cycles c) true
    have hff : ∑ x, w x * failures x = ∑ i, (1 - p) ^ (required i).card := by
      simp only [failures, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simpa using hpattern (required i) false
    by_contra hnone
    have hbad (x : E → Bool) : 1 ≤ count x / r + failures x := by
      by_cases hx : count x < r
      · have hhit : ¬ ∀ i, ∃ e ∈ required i, x e = true := by
          intro h
          exact hnone ⟨x, by
            convert hx using 1
            simp only [count, Finset.sum_boole], h⟩
        push Not at hhit
        obtain ⟨i, hi⟩ := hhit
        have hi' : ∀ e ∈ required i, x e = false := by
          intro e he
          cases h : x e
          · rfl
          · exact False.elim (hi e he h)
        have hone : 1 ≤ failures x := by
          calc
            1 = (if ∀ e ∈ required i, x e = false then 1 else 0 : ℝ) := by rw [if_pos hi']
            _ ≤ failures x := by
              unfold failures
              exact Finset.single_le_sum (f := fun j : I =>
                if ∀ e ∈ required j, x e = false then (1 : ℝ) else 0)
                (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
        have hcn : 0 ≤ count x / r := div_nonneg
          (Finset.sum_nonneg fun c _ => by split_ifs <;> norm_num) hr.le
        linarith
      · have hge : r ≤ count x := le_of_not_gt hx
        have hone : 1 ≤ count x / r := (le_div_iff₀ hr).2 (by simpa using hge)
        have hfn : 0 ≤ failures x :=
          Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
        linarith
    have hsum : 1 ≤ (∑ c, p ^ (cycles c).card) / r +
        ∑ i, (1 - p) ^ (required i).card := by
      calc
        1 = ∑ x, w x := htotal.symm
        _ ≤ ∑ x, w x * (count x / r + failures x) :=
          Finset.sum_le_sum fun x _ => by
            exact le_mul_of_one_le_right (hw x) (hbad x)
        _ = (∑ c, p ^ (cycles c).card) / r +
            ∑ i, (1 - p) ^ (required i).card := by
          simp_rw [mul_add, ← mul_div_assoc]
          rw [Finset.sum_add_distrib, ← Finset.sum_div, hcf, hff]
    exact (not_le_of_gt hbudget) hsum
  have exists_sparse_graph (n s : ℕ) (p r : ℝ)
      (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 < r)
      (hbudget : ((n : ℝ) ^ 3 * p ^ 3 + (n : ℝ) ^ 4 * p ^ 4) / r +
        (2 : ℝ) ^ n * (1 - p) ^ (s.choose 2) < 1) :
      ∃ X : SimpleGraph (Fin n),
        ((Finset.univ.filter fun f : {f : Fin 3 → Fin n // Function.Injective f} =>
          X.Adj (f.1 0) (f.1 1) ∧ X.Adj (f.1 1) (f.1 2) ∧
          X.Adj (f.1 2) (f.1 0)).card +
          (Finset.univ.filter fun f : {f : Fin 4 → Fin n // Function.Injective f} =>
            X.Adj (f.1 0) (f.1 1) ∧ X.Adj (f.1 1) (f.1 2) ∧
            X.Adj (f.1 2) (f.1 3) ∧ X.Adj (f.1 3) (f.1 0)).card : ℝ) < r ∧
        X.indepNum < s := by
    classical
    let C3 := {f : Fin 3 → Fin n // Function.Injective f}
    let C4 := {f : Fin 4 → Fin n // Function.Injective f}
    let I := {S : Finset (Fin n) // S.card = s}
    let cycles : C3 ⊕ C4 → Finset (Sym2 (Fin n)) := Sum.elim
      (fun f => {s(f.1 0, f.1 1), s(f.1 1, f.1 2), s(f.1 2, f.1 0)})
      (fun f => {s(f.1 0, f.1 1), s(f.1 1, f.1 2),
        s(f.1 2, f.1 3), s(f.1 3, f.1 0)})
    let required : I → Finset (Sym2 (Fin n)) := fun S =>
      ((⊤ : SimpleGraph S.1).edgeFinset).map (Function.Embedding.subtype (· ∈ S.1)).sym2Map
    have hc3 (f : C3) : (cycles (Sum.inl f)).card = 3 := by
      simp [cycles, f.2.eq_iff]
    have hc4 (f : C4) : (cycles (Sum.inr f)).card = 4 := by
      simp [cycles, f.2.eq_iff]
    have hreq (S : I) : (required S).card = s.choose 2 := by
      simp only [required, Finset.card_map, card_edgeFinset_top_eq_card_choose_two]
      simp [S.2]
    have hC3 : Fintype.card C3 ≤ n ^ 3 := by
      calc
        _ ≤ Fintype.card (Fin 3 → Fin n) :=
          Fintype.card_le_of_injective Subtype.val Subtype.val_injective
        _ = _ := by simp
    have hC4 : Fintype.card C4 ≤ n ^ 4 := by
      calc
        _ ≤ Fintype.card (Fin 4 → Fin n) :=
          Fintype.card_le_of_injective Subtype.val Subtype.val_injective
        _ = _ := by simp
    have hI : Fintype.card I ≤ 2 ^ n := by
      calc
        _ ≤ Fintype.card (Finset (Fin n)) :=
          Fintype.card_le_of_injective Subtype.val Subtype.val_injective
        _ = _ := by simp
    have hb : (∑ c, p ^ (cycles c).card) / r +
        (∑ i, (1 - p) ^ (required i).card) < 1 := by
      have hcy : (∑ c, p ^ (cycles c).card) ≤
          (n : ℝ) ^ 3 * p ^ 3 + (n : ℝ) ^ 4 * p ^ 4 := by
        rw [Fintype.sum_sum_type]
        simp_rw [hc3, hc4]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hC3) (pow_nonneg hp 3))
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hC4) (pow_nonneg hp 4))
      have hi : (∑ i, (1 - p) ^ (required i).card) ≤
          (2 : ℝ) ^ n * (1 - p) ^ (s.choose 2) := by
        simp_rw [hreq]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hI)
          (pow_nonneg (sub_nonneg.mpr hp1) _)
      exact lt_of_le_of_lt (add_le_add (div_le_div_of_nonneg_right hcy hr.le) hi) hbudget
    obtain ⟨x, hx, hhit⟩ := finite_selection cycles required p r hp hp1 hr hb
    let X : SimpleGraph (Fin n) :=
      { Adj := fun a b => a ≠ b ∧ x s(a, b) = true
        symm := ⟨fun a b h => ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
        loopless := ⟨fun a h => h.1 rfl⟩ }
    have hxc3 (f : C3) : (∀ e ∈ cycles (Sum.inl f), x e = true) ↔
        X.Adj (f.1 0) (f.1 1) ∧ X.Adj (f.1 1) (f.1 2) ∧
        X.Adj (f.1 2) (f.1 0) := by
      simp [cycles, X, f.2.eq_iff]
    have hxc4 (f : C4) : (∀ e ∈ cycles (Sum.inr f), x e = true) ↔
        X.Adj (f.1 0) (f.1 1) ∧ X.Adj (f.1 1) (f.1 2) ∧
        X.Adj (f.1 2) (f.1 3) ∧ X.Adj (f.1 3) (f.1 0) := by
      simp [cycles, X, f.2.eq_iff]
    refine ⟨X, ?_, ?_⟩
    · convert hx using 1
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      rw [Fintype.sum_sum_type]
      simp_rw [hxc3, hxc4]
      congr 1
    · by_contra hlarge
      obtain ⟨S, hS⟩ := X.exists_isNIndepSet_indepNum
      obtain ⟨A, hAS, hA⟩ := Finset.exists_subset_card_eq
        ((le_of_not_gt hlarge).trans hS.card_eq.ge)
      obtain ⟨e, he, hxe⟩ := hhit (⟨A, hA⟩ : I)
      obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp he
      induction d using Sym2.inductionOn with | hf a b
      have hab : a ≠ b := by simpa using (mem_edgeFinset.mp hd)
      have hAdj : X.Adj a.1 b.1 :=
        ⟨fun h => hab (Subtype.ext h), by simpa using hxe⟩
      exact hS.isIndepSet (hAS a.2) (hAS b.2) hAdj.ne hAdj
  have htail : (2 : ℝ) ^ (t ^ 9) *
      (1 - 1 / (t : ℝ) ^ 7) ^ ((4 * t ^ 8).choose 2) ≤ 1 / 4 := by
    let q := t ^ 7
    let a : ℝ := 1 - 1 / (q : ℝ)
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
    have hq1 : 1 ≤ q := by dsimp [q]; exact one_le_pow₀ (by omega)
    have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hq0 : (0 : ℝ) < q := by linarith
    have ha0 : 0 ≤ a := by
      dsimp [a]
      have := (div_le_one hq0).mpr hq1R
      linarith
    have ha1 : a ≤ 1 := by
      dsimp [a]
      linarith [one_div_nonneg.mpr hq0.le]
    have hhalf : a ^ q ≤ (1 / 2 : ℝ) := by
      have h := pow_add_mul_le_add_pow (a := a) (b := 1 / (q : ℝ)) ha0
        (show 0 ≤ 2 * a + 1 / (q : ℝ) by positivity) q
      have hab : a + 1 / (q : ℝ) = 1 := by dsimp [a]; ring
      rw [hab, one_pow] at h
      have heq : (q : ℝ) * a ^ (q - 1) * (1 / (q : ℝ)) = a ^ (q - 1) := by
        field_simp
      rw [heq] at h
      have hmono : a ^ q ≤ a ^ (q - 1) :=
        pow_le_pow_of_le_one ha0 ha1 (Nat.sub_le _ _)
      linarith
    have hchoose : (t ^ 9 + 2) * q ≤ (4 * t ^ 8).choose 2 := by
      have h7 : (t : ℝ) ^ 7 ≤ (t : ℝ) ^ 16 := pow_le_pow_right₀ ht1 (by omega)
      have h8 : (t : ℝ) ^ 8 ≤ (t : ℝ) ^ 16 := pow_le_pow_right₀ ht1 (by omega)
      have h16 : 0 ≤ (t : ℝ) ^ 16 := by positivity
      have hcast : (((4 * t ^ 8).choose 2 : ℕ) : ℝ) =
          (4 * (t : ℝ) ^ 8) * (4 * (t : ℝ) ^ 8 - 1) / 2 := by
        rw [Nat.cast_choose_two]
        push_cast
        rfl
      have hbound : ((t : ℝ) ^ 9 + 2) * (t : ℝ) ^ 7 ≤
          (((4 * t ^ 8).choose 2 : ℕ) : ℝ) := by
        rw [hcast]
        nlinarith
      dsimp [q]
      exact_mod_cast hbound
    have hexp : a ^ ((4 * t ^ 8).choose 2) ≤ a ^ ((t ^ 9 + 2) * q) :=
      pow_le_pow_of_le_one ha0 ha1 hchoose
    have hblock : a ^ ((t ^ 9 + 2) * q) ≤ (1 / 2 : ℝ) ^ (t ^ 9 + 2) := by
      rw [Nat.mul_comm, pow_mul]
      exact pow_le_pow_left₀ (pow_nonneg ha0 _) hhalf _
    have htwo : (0 : ℝ) ≤ 2 ^ (t ^ 9) := by positivity
    have hfinal := mul_le_mul_of_nonneg_left (hexp.trans hblock) htwo
    have hid : (2 : ℝ) ^ (t ^ 9) * (1 / 2 : ℝ) ^ (t ^ 9 + 2) = 1 / 4 := by
      rw [pow_add, ← mul_assoc, ← mul_pow]
      norm_num
    rw [hid] at hfinal
    simpa [a, q] using hfinal
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hr : 0 < 8 * (t : ℝ) ^ 8 := by positivity
  have hp : 0 ≤ 1 / (t : ℝ) ^ 7 := by positivity
  have hp1 : 1 / (t : ℝ) ^ 7 ≤ 1 := by
    exact (div_le_one (pow_pos ht0 7)).mpr (one_le_pow₀ ht1)
  have hcycle : (((t : ℝ) ^ 9) ^ 3 * (1 / (t : ℝ) ^ 7) ^ 3 +
      ((t : ℝ) ^ 9) ^ 4 * (1 / (t : ℝ) ^ 7) ^ 4) /
        (8 * (t : ℝ) ^ 8) ≤ 1 / 4 := by
    have hid : (((t : ℝ) ^ 9) ^ 3 * (1 / (t : ℝ) ^ 7) ^ 3 +
        ((t : ℝ) ^ 9) ^ 4 * (1 / (t : ℝ) ^ 7) ^ 4) /
          (8 * (t : ℝ) ^ 8) =
        ((t : ℝ) ^ 6 + (t : ℝ) ^ 8) / (8 * (t : ℝ) ^ 8) := by
      field_simp
    rw [hid]
    apply (div_le_iff₀ hr).mpr
    nlinarith [pow_le_pow_right₀ ht1 (show 6 ≤ 8 by omega)]
  have hb : (((t ^ 9 : ℕ) : ℝ) ^ 3 * (1 / (t : ℝ) ^ 7) ^ 3 +
      ((t ^ 9 : ℕ) : ℝ) ^ 4 * (1 / (t : ℝ) ^ 7) ^ 4) /
        (8 * (t : ℝ) ^ 8) +
      (2 : ℝ) ^ (t ^ 9) * (1 - 1 / (t : ℝ) ^ 7) ^ ((4 * t ^ 8).choose 2) < 1 := by
    push_cast
    linarith
  obtain ⟨X, hXcycles, hXalpha⟩ := exists_sparse_graph (t ^ 9) (4 * t ^ 8)
    (1 / (t : ℝ) ^ 7) (8 * (t : ℝ) ^ 8) hp hp1 hr hb
  obtain ⟨H, _, htri, hsquare, halpha⟩ := exists_short_cycle_free_deletion X
  refine ⟨H, htri, hsquare, ?_⟩
  have hcycles : (Finset.univ.filter fun f :
      {f : Fin 3 → Fin (t ^ 9) // Function.Injective f} =>
        X.Adj (f.1 0) (f.1 1) ∧ X.Adj (f.1 1) (f.1 2) ∧ X.Adj (f.1 2) (f.1 0)).card +
      (Finset.univ.filter fun f : {f : Fin 4 → Fin (t ^ 9) // Function.Injective f} =>
        X.Adj (f.1 0) (f.1 1) ∧ X.Adj (f.1 1) (f.1 2) ∧
        X.Adj (f.1 2) (f.1 3) ∧ X.Adj (f.1 3) (f.1 0)).card < 8 * t ^ 8 := by
    exact_mod_cast hXcycles
  omega

#print axioms exists_good_block

end D5.S3.Combinatorics.PhylogeneticRank.PhylogeneticRankRandom
