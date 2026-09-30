/- GID: D5/S3/Combinatorics/LatinHFamilyTheorem
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LatinHFamilyTheorem
   mirror-E: none(waiver:explicit-H-family)
   anchors: [D5/S3/Combinatorics/LatinHTransversals]
   utility: none
   digest: Coordinate partitions and the actual H-family transversal obstruction. -/

import D5.S3.Combinatorics.LatinHTransversals
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LatinHFamilyTheorem

open D5.S3.Combinatorics.LatinHTransversals

set_option maxHeartbeats 4000000 in
/-- The cap complements exclude all four bulk progressions, so both complete coordinate maps are permutations. -/
theorem coordinate_permutations (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) :
    Function.Bijective (column k hk j) ∧ Function.Bijective (symbol k hk j) := by
  have hcapcol (i : Fin 36) :
      column k hk j (capRow k hk i) =
        let p := capAffine j (k % 2 = 1) i
        residue k hk (p.1 * (k : ℤ) + p.2) := by
    by_cases hi : i.val < 15
    · simp [column, columnRaw, capRow, hi]
    · have htail : order k - 21 ≤ (capRow k hk i).val := by
        dsimp [capRow, order]
        simp [hi]
        omega
      have hhead : 15 ≤ (capRow k hk i).val := by
        dsimp [capRow, order]
        simp [hi]
        omega
      have hind : (capRow k hk i).val - (order k - 21) + 15 = i.val := by
        dsimp [capRow, order]
        simp [hi]
        omega
      simp [column, columnRaw, not_lt.mpr hhead, htail, hind]
  have hcapsym (i : Fin 36) :
      symbol k hk j (capRow k hk i) =
        let p := capSymbolAffine j (k % 2 = 1) i
        residue k hk (p.1 * (k : ℤ) + p.2) := by
    by_cases hi : i.val < 15
    · simp [symbol, symbolRaw, columnRaw, capSymbolAffine, capRow, hi]
      ring
    · have htail : order k - 21 ≤ (capRow k hk i).val := by
        dsimp [capRow, order]
        simp [hi]
        omega
      have hhead : 15 ≤ (capRow k hk i).val := by
        dsimp [capRow, order]
        simp [hi]
        omega
      have hind : (capRow k hk i).val - (order k - 21) + 15 = i.val := by
        dsimp [capRow, order]
        simp [hi]
        omega
      simp [symbol, symbolRaw, not_lt.mpr hhead, htail,
        columnRaw, hind, capSymbolAffine, hi]
      have hrow : ((capRow k hk i).val : ℤ) =
          (order k : ℤ) + (i.val : ℤ) - 36 := by
        dsimp [capRow, order]
        simp [hi]
        omega
      rw [hrow]
      have harg :
          (order k : ℤ) + (i.val : ℤ) - 36 +
              ((capAffine j (k % 2 = 1) i).1 * (k : ℤ) +
                (capAffine j (k % 2 = 1) i).2) =
          (order k : ℤ) +
              ((capAffine j (k % 2 = 1) i).1 * (k : ℤ) +
                ((capAffine j (k % 2 = 1) i).2 + ((i.val : ℤ) - 36))) := by
        ring
      rw [harg]
      have hperiod (z : ℤ) : residue k hk ((order k : ℤ) + z) =
          residue k hk z := by
        apply Fin.ext
        simp [residue]
      exact hperiod _
  have hbulkcol (w : Fin (k - 9)) (s : Fin 4) :
      column k hk j (bulkRow k hk w s) =
        residue k hk (bulkColumnRaw k j w.val s.val) := by
    have hw : w.val + 9 < k := by have := w.isLt; omega
    have hs : s.val < 4 := s.isLt
    have hlo : 15 ≤ (bulkRow k hk w s).val := by dsimp [bulkRow]; omega
    have hhi : (bulkRow k hk w s).val < order k - 21 := by
      dsimp [bulkRow, order]
      omega
    have hquot : ((bulkRow k hk w s).val - 15) / 4 = w.val := by
      dsimp [bulkRow]
      omega
    have hrem : ((bulkRow k hk w s).val - 15) % 4 = s.val := by
      dsimp [bulkRow]
      omega
    simp [column, columnRaw, not_lt.mpr hlo, Nat.not_le.mpr hhi,
      hquot, hrem]
  have hbulksym (w : Fin (k - 9)) (s : Fin 4) :
      symbol k hk j (bulkRow k hk w s) =
        residue k hk (bulkSymbolRaw k j w.val s.val) := by
    have hw : w.val + 9 < k := by have := w.isLt; omega
    have hs : s.val < 4 := s.isLt
    have hlo : 15 ≤ (bulkRow k hk w s).val := by dsimp [bulkRow]; omega
    have hhi : (bulkRow k hk w s).val < order k - 21 := by
      dsimp [bulkRow, order]
      omega
    have hquot : ((bulkRow k hk w s).val - 15) / 4 = w.val := by
      dsimp [bulkRow]
      omega
    have hrem : ((bulkRow k hk w s).val - 15) % 4 = s.val := by
      dsimp [bulkRow]
      omega
    simp [symbol, symbolRaw, not_lt.mpr hlo, Nat.not_le.mpr hhi,
      hquot, hrem]
  have hcertificate (sym : Bool) :
      List.Perm (List.ofFn (if sym then capSymbolAffine j (k % 2 = 1)
                                  else capAffine j (k % 2 = 1)))
        (if sym then capSymbolComplement (shift j) else capColumnComplement (shift j)) := by
    cases sym <;> fin_cases j <;> by_cases hodd : k % 2 = 1 <;>
      simp only [hodd, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] <;> decide
  have hvalue (z : ℤ) (hz : -(order k : ℤ) < z ∧
      z < 2 * (order k : ℤ)) :
      ((residue k hk z).val : ℤ) =
        if z < 0 then z + order k
        else if z < order k then z else z - order k := by
    have hn : 0 ≤ z % (order k : ℤ) :=
      Int.emod_nonneg _ (by dsimp [order]; omega)
    have hv : ((residue k hk z).val : ℤ) = z % (order k : ℤ) := by
      simp [residue, Int.toNat_of_nonneg hn]
    rw [hv]
    by_cases hneg : z < 0
    · have hstep : 0 ≤ z + order k ∧ z + order k < order k := by omega
      rw [if_pos hneg, show z % (order k : ℤ) =
        (z + order k) % (order k : ℤ) by simp,
        Int.emod_eq_of_lt hstep.1 hstep.2]
    · have hnonneg : 0 ≤ z := by omega
      rw [if_neg hneg]
      by_cases hsmall : z < order k
      · rw [if_pos hsmall, Int.emod_eq_of_lt hnonneg hsmall]
      · have hstep : 0 ≤ z - order k ∧ z - order k < order k := by omega
        rw [if_neg hsmall, show z % (order k : ℤ) =
          (z - order k) % (order k : ℤ) by simp,
          Int.emod_eq_of_lt hstep.1 hstep.2]

  have hcross (sym : Bool) (p : ℤ × ℤ)
      (hp : p ∈ (if sym then capSymbolComplement (shift j)
                        else capColumnComplement (shift j)))
      (t : Fin (k - 9)) (r : Fin 4) :
      residue k hk (p.1 * (k : ℤ) + p.2) ≠
        residue k hk (if sym then bulkSymbolRaw k j t.val r.val
                            else bulkColumnRaw k j t.val r.val) := by
    intro heq
    have ht : t.val + 9 < k := by have := t.isLt; omega
    have hs : shift j = 0 ∨ shift j = -4 := by fin_cases j <;> simp [shift]
    let x := p.1 * (k : ℤ) + p.2
    let y := if sym then bulkSymbolRaw k j t.val r.val
                  else bulkColumnRaw k j t.val r.val
    have hx : -(order k : ℤ) < x ∧ x < 2 * (order k : ℤ) := by
      cases sym <;> simp only [Bool.false_eq_true, ↓reduceIte] at hp
      all_goals simp only [capColumnComplement, capSymbolComplement,
        List.mem_append, List.mem_map, List.mem_range] at hp
      all_goals rcases hp with (((⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) |
        ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩)
      all_goals dsimp [x, order] <;> rcases hs with hs | hs <;> omega
    have hy : -(order k : ℤ) < y ∧ y < 2 * (order k : ℤ) := by
      cases sym <;> fin_cases r
      all_goals rcases hs with hs | hs
      all_goals simp [y, bulkSymbolRaw, bulkColumnRaw, hs, order] <;> omega
    have heq' :
        (if x < 0 then x + order k else if x < order k then x else x - order k) =
        (if y < 0 then y + order k else if y < order k then y else y - order k) := by
      have hv := congrArg (fun z : Fin (order k) => (z.val : ℤ)) heq
      simpa [x, y, hvalue x hx, hvalue y hy] using hv
    cases sym <;> simp only [Bool.false_eq_true, ↓reduceIte] at hp
    all_goals simp only [capColumnComplement, capSymbolComplement,
      List.mem_append, List.mem_map, List.mem_range] at hp
    all_goals rcases hp with (((⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) |
      ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩)
    all_goals fin_cases r
    all_goals rcases hs with hs | hs
    all_goals simp [x, y, bulkColumnRaw, bulkSymbolRaw, hs, order] at heq'
    all_goals split_ifs at heq' <;> omega
  have hexhaust (a : Fin (order k)) :
      (∃ i : Fin 36, capRow k hk i = a) ∨
      ∃ p : Fin (k - 9) × Fin 4, bulkRow k hk p.1 p.2 = a := by
    by_cases hhead : a.val < 15
    · left
      exact ⟨⟨a.val, by omega⟩, by apply Fin.ext; simp [capRow, hhead]⟩
    by_cases htail : order k - 21 ≤ a.val
    · left
      let i : Fin 36 := ⟨a.val - (order k - 21) + 15, by have := a.isLt; omega⟩
      refine ⟨i, ?_⟩
      apply Fin.ext
      have hi : ¬ i.val < 15 := by dsimp [i]; omega
      simp [capRow, hi, i, order]
      dsimp [order] at htail
      omega
    · right
      let t : Fin (k - 9) := ⟨(a.val - 15) / 4, by dsimp [order] at *; omega⟩
      let r : Fin 4 := ⟨(a.val - 15) % 4, Nat.mod_lt _ (by decide)⟩
      refine ⟨(t,r), ?_⟩
      apply Fin.ext
      dsimp [bulkRow, t, r]
      omega
  have hbij (sym : Bool) :
      Function.Bijective (if sym then symbol k hk j else column k hk j) := by
    apply (Finite.injective_iff_bijective).mp
    intro a b heq
    rcases hexhaust a with ⟨i, rfl⟩ | ⟨⟨t,r⟩, rfl⟩
    · rcases hexhaust b with ⟨l, rfl⟩ | ⟨⟨u,v⟩, rfl⟩
      · have hi : i = l := by
          cases sym
          · exact cap_column_injective k hk j heq
          · exact cap_symbol_injective k hk j heq
        rw [hi]
      · exfalso
        cases sym
        · simp only [Bool.false_eq_true, ↓reduceIte] at heq
          rw [hcapcol i, hbulkcol u v] at heq
          exact hcross false _ ((hcertificate false).mem_iff.mp
            (List.mem_ofFn.mpr ⟨i, rfl⟩)) u v heq
        · simp only [↓reduceIte] at heq
          rw [hcapsym i, hbulksym u v] at heq
          exact hcross true _ ((hcertificate true).mem_iff.mp
            (List.mem_ofFn.mpr ⟨i, rfl⟩)) u v heq
    · rcases hexhaust b with ⟨l, rfl⟩ | ⟨⟨u,v⟩, rfl⟩
      · exfalso
        cases sym
        · simp only [Bool.false_eq_true, ↓reduceIte] at heq
          rw [hbulkcol t r, hcapcol l] at heq
          exact hcross false _ ((hcertificate false).mem_iff.mp
            (List.mem_ofFn.mpr ⟨l, rfl⟩)) t r heq.symm
        · simp only [↓reduceIte] at heq
          rw [hbulksym t r, hcapsym l] at heq
          exact hcross true _ ((hcertificate true).mem_iff.mp
            (List.mem_ofFn.mpr ⟨l, rfl⟩)) t r heq.symm
      · have hi : (t,r) = (u,v) := by
          cases sym
          · exact bulk_column_injective k hk j heq
          · exact bulk_symbol_injective k hk j heq
        cases hi
        rfl
  exact ⟨hbij false, hbij true⟩

set_option maxHeartbeats 3000000 in
/-- Summing the actual priority increments forces at least two distinguished entries in every transversal. -/
theorem transversal_obstruction (k : ℕ) (hk : 9 ≤ k)
    (S : Set (Fin (order k) × Fin (order k) × Fin (order k)))
    (hS : IsTransversal k hk S) :
    2 ≤ {f | f ∈ D k hk ∧ f ∈ S}.ncard := by
  classical
  have hncard : {f | f ∈ D k hk ∧ f ∈ S}.ncard =
      ((D k hk).filter (fun f => f ∈ S)).card := by
    rw [show {f | f ∈ D k hk ∧ f ∈ S} =
      (↑((D k hk).filter (fun f => f ∈ S)) : Set _) by ext; simp]
    exact Set.ncard_coe_finset _
  rw [hncard]
  let e (a : Fin (order k)) := Classical.choose (hS.2.1 a)
  have he (a : Fin (order k)) : e a ∈ S ∧ (e a).1 = a :=
    (Classical.choose_spec (hS.2.1 a)).1
  have hunique (a : Fin (order k)) (f : Fin (order k) × Fin (order k) × Fin (order k))
      (hf : f ∈ S) (hr : f.1 = a) : f = e a :=
    (Classical.choose_spec (hS.2.1 a)).2 f ⟨hf,hr⟩
  have hei : Function.Injective e := by
    intro a b hab
    have h := congrArg Prod.fst hab
    simpa only [(he a).2, (he b).2] using h
  have hcoord (g : (Fin (order k) × Fin (order k) × Fin (order k)) → Fin (order k))
      (hg : ∀ x, ∃! f, f ∈ S ∧ g f = x) : Function.Bijective (fun a => g (e a)) := by
    constructor
    · intro a b hab
      obtain ⟨f,hf,hfuniq⟩ := hg (g (e a))
      have ha : e a = f := hfuniq _ ⟨(he a).1,rfl⟩
      have hb : e b = f := hfuniq _ ⟨(he b).1,hab.symm⟩
      exact hei (ha.trans hb.symm)
    · intro x
      obtain ⟨f,hf,_⟩ := hg x
      refine ⟨f.1, ?_⟩
      change g (e f.1) = x
      rw [← hunique f.1 f hf.1 rfl]
      exact hf.2
  have hc := hcoord (fun f => f.2.1) hS.2.2.1
  have hz := hcoord (fun f => f.2.2) hS.2.2.2
  let R : ℤ := ∑ a : Fin (order k), (a.val : ℤ)
  let charge : ℤ := ∑ a : Fin (order k), delta k a (e a).2.1
  have hR : R = 2 * (k : ℤ) * (4 * (k : ℤ) - 1) := by
    have hgauss := Finset.sum_range_id_mul_two (order k)
    have hgaussInt := congrArg (fun z : ℕ => (z : ℤ)) hgauss
    have horder : 1 ≤ order k := by dsimp [order]; omega
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum,
      Nat.cast_sub horder] at hgaussInt
    have hrange : R = ∑ a ∈ Finset.range (order k), (a : ℤ) :=
      Fin.sum_univ_eq_sum_range (fun a => (a : ℤ)) (order k)
    rw [← hrange] at hgaussInt
    dsimp [order] at hgaussInt
    push_cast at hgaussInt
    nlinarith
  have hmod : charge ≡ 2 * (k : ℤ) [ZMOD (order k : ℤ)] := by
    have hrow (a : Fin (order k)) :
        delta k a (e a).2.1 ≡
          ((e a).2.2.val : ℤ) - (a.val : ℤ) - ((e a).2.1.val : ℤ)
            [ZMOD (order k : ℤ)] := by
      have hsource := hS.1 (e a) (he a).1
      rw [(he a).2] at hsource
      have hval := congrArg (fun z : Fin (order k) => (z.val : ℤ)) hsource
      have hnonneg : 0 ≤ ((a.val : ℤ) + ((e a).2.1.val : ℤ) +
          delta k a (e a).2.1) % (order k : ℤ) :=
        Int.emod_nonneg _ (by dsimp [order]; omega)
      have hb : ((e a).2.2.val : ℤ) < order k := by exact_mod_cast (e a).2.2.isLt
      have ht : (a.val : ℤ) + ((e a).2.1.val : ℤ) + delta k a (e a).2.1 ≡
          ((e a).2.2.val : ℤ) [ZMOD (order k : ℤ)] := by
        change _ % _ = _ % _
        rw [Int.emod_eq_of_lt (by omega) hb]
        simpa [square, residue, Int.toNat_of_nonneg hnonneg] using hval.symm
      have ht' := (ht.sub (Int.ModEq.refl (a.val : ℤ))).sub
        (Int.ModEq.refl ((e a).2.1.val : ℤ))
      convert ht' using 1 <;> ring
    have hsum := Int.ModEq.sum (s := Finset.univ) (fun a _ => hrow a)
    have hcsum : (∑ a : Fin (order k), ((e a).2.1.val : ℤ)) = R := hc.sum_comp (fun b => (b.val : ℤ))
    have hzsum : (∑ a : Fin (order k), ((e a).2.2.val : ℤ)) = R := hz.sum_comp (fun b => (b.val : ℤ))
    have hsum' : charge ≡ -R [ZMOD (order k : ℤ)] := by
      simpa [charge, Finset.sum_sub_distrib, hcsum, hzsum, R] using hsum
    apply hsum'.trans
    rw [hR]
    have hexpr : -(2 * (k : ℤ) * (4 * (k : ℤ) - 1)) =
        2 * (k : ℤ) + (order k : ℤ) * (-2 * (k : ℤ)) := by dsimp [order]; push_cast; ring
    rw [hexpr]
    exact Int.modEq_add_fac_self
  let A0 : Finset (Fin (order k)) := {headRow k hk 0, headRow k hk 5, headRow k hk 10}
  let A1 : Finset (Fin (order k)) := {headRow k hk 1, headRow k hk 6, headRow k hk 11}
  let A4 : Finset (Fin (order k)) := {headRow k hk 4, headRow k hk 9, headRow k hk 14}
  let B (r : Fin 4) := Finset.univ.image (fun t : Fin (k - 9) => bulkRow k hk t r)
  have hA0 (a : Fin (order k)) : a ∈ A0 ↔ a.val = 0 ∨ a.val = 5 ∨ a.val = 10 := by
    simp [A0, Fin.ext_iff, headRow]
  have hA1 (a : Fin (order k)) : a ∈ A1 ↔ a.val = 1 ∨ a.val = 6 ∨ a.val = 11 := by
    simp [A1, Fin.ext_iff, headRow]
  have hA4 (a : Fin (order k)) : a ∈ A4 ↔ a.val = 4 ∨ a.val = 9 ∨ a.val = 14 := by
    simp [A4, Fin.ext_iff, headRow]
  have hB (r : Fin 4) (a : Fin (order k)) :
      a ∈ B r ↔ 15 ≤ a.val ∧ a.val < order k - 21 ∧ a.val % 4 = (3+r.val)%4 := by
    simp only [B, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t,rfl⟩
      have := t.isLt
      have := r.isLt
      dsimp [bulkRow,order]
      omega
    · intro ha
      let t : Fin (k - 9) := ⟨(a.val-15)/4, by dsimp [order] at *; omega⟩
      refine ⟨t, ?_⟩
      apply Fin.ext
      have := r.isLt
      dsimp [bulkRow,t]
      omega
  have hBcard (r : Fin 4) : (B r).card = k - 9 := by
    have hi : Function.Injective (fun t : Fin (k - 9) => bulkRow k hk t r) := by
      intro t u h
      apply Fin.ext
      have hv := congrArg Fin.val h
      dsimp [bulkRow] at hv
      omega
    simp [B, Finset.card_image_of_injective _ hi]
  have hsumIndicator (A : Finset (Fin (order k))) :
      (∑ a : Fin (order k), if a ∈ A then (1 : ℤ) else 0) = A.card := by
    simp
  let lo (a : Fin (order k)) : ℤ :=
    -(if a ∈ A1 then 1 else 0) - 4*(if a ∈ A4 then 1 else 0) - 2*(if a ∈ B 2 then 1 else 0)
  let hi (a : Fin (order k)) : ℤ :=
    4*(if a ∈ A0 then 1 else 0) + 2*(if a ∈ B 0 then 1 else 0)
  have hlo (a : Fin (order k)) : lo a ≤ delta k a (e a).2.1 := by
    simp only [lo,hA1,hA4,hB]
    norm_num
    dsimp only [delta]
    split_ifs <;> omega
  have hres (z : ℤ) (h0 : 0 ≤ z) (hlt : z < order k) :
      ((residue k hk z).val : ℤ) = z := by
    simp [residue,Int.emod_eq_of_lt h0 hlt,Int.toNat_of_nonneg h0]
  have hdist (a : Fin (order k))
      (h : (a.val = 1 ∧ (e a).2.1.val = 1) ∨
        (a.val = 6 ∧ (e a).2.1.val = 5) ∨
        (a.val = 11 ∧ (e a).2.1.val = 9)) : e a ∈ D k hk := by
    have hsource := hS.1 (e a) (he a).1
    rw [(he a).2] at hsource
    have hrow := congrArg Fin.val (he a).2
    rcases h with h | h | h
    all_goals have hdelta : delta k a (e a).2.1 = 3 := by simp [delta,h.1,h.2]
    all_goals simp only [square,hdelta] at hsource
    all_goals simp only [h.1,h.2, Nat.cast_ofNat] at hsource
    all_goals norm_num only at hsource
    all_goals have hsymbol := congrArg (fun z : Fin (order k) => (z.val : ℤ)) hsource
    all_goals simp only [D,Finset.mem_insert,Finset.mem_singleton]
    · left
      simp only [d0,Prod.ext_iff,Fin.ext_iff]
      have hv1 := hres 1 (by omega) (by dsimp [order]; omega)
      have hv5 := hres 5 (by omega) (by dsimp [order]; omega)
      have hz5 : ((e a).2.2.val : ℤ) = 5 := by simpa [hv5] using hsymbol
      omega
    · right; left
      simp only [d1,Prod.ext_iff,Fin.ext_iff]
      have hv6 := hres 6 (by omega) (by dsimp [order]; omega)
      have hv5 := hres 5 (by omega) (by dsimp [order]; omega)
      have hv14 := hres 14 (by omega) (by dsimp [order]; omega)
      have hz14 : ((e a).2.2.val : ℤ) = 14 := by simpa [hv14] using hsymbol
      omega
    · right; right
      simp only [d2,Prod.ext_iff,Fin.ext_iff]
      have hv11 := hres 11 (by omega) (by dsimp [order]; omega)
      have hv9 := hres 9 (by omega) (by dsimp [order]; omega)
      have hv23 := hres 23 (by omega) (by dsimp [order]; omega)
      have hz23 : ((e a).2.2.val : ℤ) = 23 := by simpa [hv23] using hsymbol
      omega
  have hhi (a : Fin (order k)) :
      delta k a (e a).2.1 ≤ hi a + 3*(if e a ∈ D k hk then 1 else 0) := by
    have hd := hdist a
    simp only [hi,hA0,hB]
    norm_num
    dsimp only [delta]
    split_ifs <;> simp_all <;> omega
  have hAs : A0.card = 3 ∧ A1.card = 3 ∧ A4.card = 3 := by
    simp [A0,A1,A4,Fin.ext_iff,headRow]
  have hlosum : (∑ a : Fin (order k), lo a) = -2*(k : ℤ)+3 := by
    simp only [lo, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      ← Finset.mul_sum, hsumIndicator, hAs, hBcard]
    have hsub : ((k-9 : ℕ) : ℤ) = (k : ℤ)-9 := by omega
    rw [hsub]
    ring
  have hhisum : (∑ a : Fin (order k), hi a) = 2*(k : ℤ)-6 := by
    simp only [hi, Finset.sum_add_distrib, ← Finset.mul_sum, hsumIndicator, hAs, hBcard]
    have hsub : ((k-9 : ℕ) : ℤ) = (k : ℤ)-9 := by omega
    rw [hsub]
    ring
  let chosen := Finset.univ.filter (fun a => e a ∈ D k hk)
  have hchosen : chosen.card ≤ ((D k hk).filter (fun f => f ∈ S)).card := by
    have himage : chosen.image e ⊆ (D k hk).filter (fun f => f ∈ S) := by
      intro f hf
      rcases Finset.mem_image.mp hf with ⟨a,ha,rfl⟩
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).2,(he a).1⟩
    have hh := Finset.card_le_card himage
    rwa [Finset.card_image_of_injective _ hei] at hh
  have hchosenSum : (∑ a : Fin (order k), if e a ∈ D k hk then (1 : ℤ) else 0) =
      chosen.card := by simp [chosen]
  have hlobound : -2*(k : ℤ)+3 ≤ charge := by
    rw [← hlosum]
    exact Finset.sum_le_sum (fun a _ => hlo a)
  have hhibound : charge ≤ 2*(k : ℤ)-6+3*(chosen.card : ℤ) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hhi a)
    simpa only [charge, Finset.sum_add_distrib, ← Finset.mul_sum, hhisum, hchosenSum] using hh
  by_contra hbad
  have hone : chosen.card ≤ 1 := by omega
  have hub : charge ≤ 2*(k : ℤ)-3 := by omega
  have hmodEq : charge % (order k : ℤ) = 2*(k : ℤ) := by
    exact (show charge % (order k : ℤ) = (2*(k : ℤ)) % (order k : ℤ) from hmod).trans
      (Int.emod_eq_of_lt (by omega) (by dsimp [order]; omega))
  by_cases hnonneg : 0 ≤ charge
  · rw [Int.emod_eq_of_lt hnonneg (by dsimp [order]; omega)] at hmodEq
    omega
  · have hshift : (charge+(order k : ℤ)) % (order k : ℤ) = charge % (order k : ℤ) := by simp
    rw [Int.emod_eq_of_lt (by dsimp [order]; omega)
      (by dsimp [order]; omega)] at hshift
    have ho : (order k : ℤ) = 4*(k : ℤ) := by simp [order]
    rw [ho] at hshift hmodEq
    omega

/-- The literal distinguished entry indexed by a profile. -/
def distinguished (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) :
    Fin (order k) × Fin (order k) × Fin (order k) :=
  if j.val = 0 then d0 k hk else if j.val = 1 then d1 k hk else d2 k hk

set_option maxHeartbeats 3000000 in
/-- The complete integer-parameter H-family conclusion for the three literal profiles. -/
theorem result (K : ℤ) (hK : 9 ≤ K) :
    let k := K.toNat
    let hk : 9 ≤ k := by omega
    D5.S3.Combinatorics.LatinEulerianMultiples.IsLatin (order k) (square k hk) →
    (order k : ℤ) = 4*K ∧
    (∀ j : Fin 3,
      Function.Bijective (column k hk j) ∧ Function.Bijective (symbol k hk j) ∧
      (∀ a, symbol k hk j a = square k hk a (column k hk j a)) ∧
      IsTransversal k hk (T k hk j) ∧
      T k hk j ∩ (D k hk : Set _) = (D k hk : Set _) \ {distinguished k hk j}) ∧
    T k hk 0 ∩ T k hk 1 = {d2 k hk} ∧
    T k hk 0 ∩ T k hk 1 ∩ T k hk 2 = ∅ ∧
    (∀ S U, IsTransversal k hk S → IsTransversal k hk U → (S ∩ U).Nonempty) ∧
    ∀ e, ¬ IsPinned k hk e := by
  classical
  dsimp only
  let k := K.toNat
  have hk : 9 ≤ k := by dsimp [k]; omega
  intro hLatin
  have hT (j : Fin 3) : IsTransversal k hk (T k hk j) := by
    have hperm := coordinate_permutations k hk j
    refine ⟨?_,?_,?_,?_⟩
    · rintro f ⟨a,rfl⟩
      exact source_compatibility k hk j a
    · intro a
      refine ⟨entry k hk j a, ⟨⟨a,rfl⟩,rfl⟩, ?_⟩
      rintro f ⟨⟨b,rfl⟩,hba⟩
      change b = a at hba
      rw [hba]
    · intro b
      obtain ⟨a,hab⟩ := hperm.1.2 b
      refine ⟨entry k hk j a, ⟨⟨a,rfl⟩,hab⟩, ?_⟩
      rintro f ⟨⟨u,rfl⟩,hub⟩
      have hua : u = a := hperm.1.1 (hub.trans hab.symm)
      rw [hua]
    · intro c
      obtain ⟨a,hac⟩ := hperm.2.2 c
      refine ⟨entry k hk j a, ⟨⟨a,rfl⟩,hac⟩, ?_⟩
      rintro f ⟨⟨u,rfl⟩,huc⟩
      have hua : u = a := hperm.2.1 (huc.trans hac.symm)
      rw [hua]
  have hdentry (j q : Fin 3) :
      entry k hk j (headRow k hk ⟨1+5*q.val,by have := q.isLt; omega⟩) =
        distinguished k hk q ↔ q ≠ j := by
    fin_cases q <;> fin_cases j
    all_goals by_cases hp : k % 2 = 1
    all_goals simp [entry,column,columnRaw,symbol,symbolRaw,capEpsilon,
      capAffine,capTable,headRow,distinguished,d0,d1,d2,hp,
      Prod.ext_iff,Fin.ext_iff,residue]
    all_goals repeat rw [Int.emod_eq_of_lt (by omega) (by dsimp [order]; omega)]
    all_goals norm_num
    all_goals omega
  have hdrow (q : Fin 3) :
      (distinguished k hk q).1 =
        headRow k hk ⟨1+5*q.val,by have := q.isLt; omega⟩ := by
    fin_cases q
    all_goals apply Fin.ext
    all_goals simp [distinguished,d0,d1,d2,headRow,residue]
    all_goals rw [Int.emod_eq_of_lt (by omega) (by dsimp [order]; omega)]
    all_goals rfl
  have hdmem (j q : Fin 3) : distinguished k hk q ∈ T k hk j ↔ q ≠ j := by
    constructor
    · rintro ⟨a,ha⟩
      have hr := congrArg Prod.fst ha
      change a = (distinguished k hk q).1 at hr
      rw [hdrow q] at hr
      subst a
      exact (hdentry j q).mp ha
    · intro hq
      exact ⟨_,(hdentry j q).mpr hq⟩
  have hd_inj : Function.Injective (distinguished k hk) := by
    intro j q heq
    have h := congrArg (fun f : Fin (order k) × Fin (order k) × Fin (order k) => f.1.val) heq
    rw [hdrow j,hdrow q] at h
    apply Fin.ext
    dsimp [headRow] at h
    omega
  have hdistinguished (f : Fin (order k) × Fin (order k) × Fin (order k)) :
      f ∈ D k hk ↔ ∃ q : Fin 3, f = distinguished k hk q := by
    simp only [D,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro (h|h|h)
      · exact ⟨0,by simpa [distinguished] using h⟩
      · exact ⟨1,by simpa [distinguished] using h⟩
      · exact ⟨2,by simpa [distinguished] using h⟩
    · rintro ⟨q,rfl⟩
      fin_cases q <;> simp [distinguished]
  have hD (j : Fin 3) : T k hk j ∩ (D k hk : Set _) =
      (D k hk : Set _) \ {distinguished k hk j} := by
    ext f
    constructor
    · rintro ⟨hf,hd⟩
      rcases (hdistinguished f).mp hd with ⟨q,rfl⟩
      exact ⟨hd,by simpa only [Set.mem_singleton_iff, hd_inj.eq_iff] using (hdmem j q).mp hf⟩
    · rintro ⟨hd,hne⟩
      rcases (hdistinguished f).mp hd with ⟨q,rfl⟩
      exact ⟨(hdmem j q).mpr (by simpa only [Set.mem_singleton_iff,hd_inj.eq_iff] using hne),hd⟩
  have hpair (S U : Set (Fin (order k) × Fin (order k) × Fin (order k)))
      (hS : IsTransversal k hk S) (hU : IsTransversal k hk U) : (S ∩ U).Nonempty := by
    let A := (D k hk).filter (fun f => f ∈ S)
    let B := (D k hk).filter (fun f => f ∈ U)
    have hn (V : Set (Fin (order k) × Fin (order k) × Fin (order k))) :
        {f | f ∈ D k hk ∧ f ∈ V}.ncard = ((D k hk).filter (fun f => f ∈ V)).card := by
      rw [show {f | f ∈ D k hk ∧ f ∈ V} =
        (↑((D k hk).filter (fun f => f ∈ V)) : Set _) by ext; simp]
      exact Set.ncard_coe_finset _
    have hA : 2 ≤ A.card := by simpa only [hn S] using transversal_obstruction k hk S hS
    have hB : 2 ≤ B.card := by simpa only [hn U] using transversal_obstruction k hk U hU
    have hDcard : (D k hk).card ≤ 3 := by
      have h0 := Finset.card_insert_le (d0 k hk) ({d1 k hk,d2 k hk} : Finset _)
      have h1 := Finset.card_insert_le (d1 k hk) ({d2 k hk} : Finset _)
      simp only [Finset.card_singleton] at h1
      dsimp [D]
      omega
    by_contra hnone
    have hdisjoint : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro f hf hg
      exact hnone ⟨f,(Finset.mem_filter.mp hf).2,(Finset.mem_filter.mp hg).2⟩
    have hsub : A ∪ B ⊆ D k hk := by
      intro f hf
      rcases Finset.mem_union.mp hf with hf|hf
      · exact (Finset.mem_filter.mp hf).1
      · exact (Finset.mem_filter.mp hf).1
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisjoint] at hcard
    omega
  have hcommon := exact_common_entry k hk
  refine ⟨?_,?_,hcommon.1,hcommon.2,hpair,?_⟩
  · dsimp [order,k]
    omega
  · intro j
    exact ⟨(coordinate_permutations k hk j).1,(coordinate_permutations k hk j).2,
      source_compatibility k hk j,hT j,hD j⟩
  · intro f hpin
    have hf : f ∈ T k hk 0 ∩ T k hk 1 ∩ T k hk 2 :=
      ⟨⟨hpin.2 _ (hT 0),hpin.2 _ (hT 1)⟩,hpin.2 _ (hT 2)⟩
    rw [hcommon.2] at hf
    exact hf

#print axioms D5.S3.Combinatorics.LatinHTransversals.bulk_source_increment
#print axioms D5.S3.Combinatorics.LatinHTransversals.head_source_increment
#print axioms D5.S3.Combinatorics.LatinHTransversals.source_compatibility
#print axioms D5.S3.Combinatorics.LatinHTransversals.cap_zero_one_residue_eq_iff
#print axioms D5.S3.Combinatorics.LatinHTransversals.column_zero_one_eq_iff
#print axioms D5.S3.Combinatorics.LatinHTransversals.exact_common_entry
#print axioms D5.S3.Combinatorics.LatinHTransversals.bulk_column_injective
#print axioms D5.S3.Combinatorics.LatinHTransversals.bulk_symbol_injective
#print axioms D5.S3.Combinatorics.LatinHTransversals.cap_column_injective
#print axioms D5.S3.Combinatorics.LatinHTransversals.cap_symbol_injective
#print axioms coordinate_permutations
#print axioms transversal_obstruction
#print axioms result

end D5.S3.Combinatorics.LatinHFamilyTheorem
