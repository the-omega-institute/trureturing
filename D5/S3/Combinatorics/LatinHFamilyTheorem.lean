/- GID: D5/S3/Combinatorics/LatinHFamilyTheorem
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LatinHFamilyTheorem
   mirror-E: none(waiver:explicit-H-family)
   anchors: [D5/S3/Combinatorics/LatinHTransversals]
   utility: none
   digest: The complete integer-parameter H-family transversal theorem. -/

import D5.S3.Combinatorics.LatinHTransversals

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LatinHFamilyTheorem

open D5.S3.Combinatorics.LatinHTransversals

/-- The literal distinguished entry indexed by a profile. -/
def distinguished (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) :
    Fin (order k) × Fin (order k) × Fin (order k) :=
  if j.val = 0 then d0 k hk else if j.val = 1 then d1 k hk else d2 k hk
set_option maxHeartbeats 3000000 in
-- Symbolic cap certificates and all profile cases share this complete proof.
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
  -- Equal residues in this range differ by at most one modulus.
  have residue_eq_cases (x y : ℤ)
      (hb : -2 * (order k : ℤ) < x - y ∧ x - y < 2 * (order k : ℤ))
      (h : residue k hk x = residue k hk y) :
      x - y = -(order k : ℤ) ∨ x - y = 0 ∨ x - y = order k := by
    have hx := Int.emod_nonneg x (by dsimp [order]; omega : (order k : ℤ) ≠ 0)
    have hy := Int.emod_nonneg y (by dsimp [order]; omega : (order k : ℤ) ≠ 0)
    have hmod : x % (order k : ℤ) = y % (order k : ℤ) := by
      have hv := congrArg (fun a : Fin (order k) => (a.val : ℤ)) h
      simpa only [residue, Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy] using hv
    have hzero := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod
    by_cases h0 : 0 ≤ x - y
    · by_cases hn : x - y < order k
      · rw [Int.emod_eq_of_lt h0 hn] at hzero
        exact Or.inr (Or.inl hzero)
      · have hs : 0 ≤ x - y - order k ∧ x - y - order k < order k := by omega
        have hz : (x - y - order k) % (order k : ℤ) = 0 := by simpa using hzero
        rw [Int.emod_eq_of_lt hs.1 hs.2] at hz
        exact Or.inr (Or.inr (by omega))
    · by_cases hn : -(order k : ℤ) ≤ x - y
      · have hs : 0 ≤ x - y + order k ∧ x - y + order k < order k := by omega
        have hz : (x - y + order k) % (order k : ℤ) = 0 := by simpa using hzero
        rw [Int.emod_eq_of_lt hs.1 hs.2] at hz
        exact Or.inl (by omega)
      · have hs : 0 ≤ x - y + 2 * order k ∧ x - y + 2 * order k < order k := by omega
        have hz : (x - y + 2 * order k) % (order k : ℤ) = 0 := by simpa using hzero
        rw [Int.emod_eq_of_lt hs.1 hs.2] at hz
        omega

  have coordinate_permutations (j : Fin 3) :
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
    have hbulkinj (sym : Bool) :
        Function.Injective (fun p : Fin (k - 9) × Fin 4 =>
          (if sym then symbol k hk j else column k hk j) (bulkRow k hk p.1 p.2)) := by
      intro ⟨t, r⟩ ⟨u, v⟩ heq
      have ht := t.isLt
      have hu := u.isLt
      have hvals : t.val = u.val ∧ r.val = v.val := by
        cases sym
        · change column k hk j (bulkRow k hk t r) =
            column k hk j (bulkRow k hk u v) at heq
          rw [hbulkcol t r, hbulkcol u v] at heq
          have hcases := residue_eq_cases _ _ (by
            fin_cases r <;> fin_cases v <;> simp [bulkColumnRaw, order] <;> omega) heq
          fin_cases r <;> fin_cases v
          all_goals simp [bulkColumnRaw, order] at hcases ⊢
          all_goals rcases hcases with h | h | h <;> omega
        · change symbol k hk j (bulkRow k hk t r) =
            symbol k hk j (bulkRow k hk u v) at heq
          rw [hbulksym t r, hbulksym u v] at heq
          have hcases := residue_eq_cases _ _ (by
            fin_cases r <;> fin_cases v <;> simp [bulkSymbolRaw, order] <;> omega) heq
          fin_cases r <;> fin_cases v
          all_goals simp [bulkSymbolRaw, order] at hcases ⊢
          all_goals rcases hcases with h | h | h <;> omega
      exact Prod.ext (Fin.ext hvals.1) (Fin.ext hvals.2)
    have hcapinj (sym : Bool) :
        Function.Injective (fun i : Fin 36 =>
          (if sym then symbol k hk j else column k hk j) (capRow k hk i)) := by
      have hpair : Function.Injective
          (if sym then capSymbolAffine j (k % 2 = 1) else capAffine j (k % 2 = 1)) := by
        cases sym <;> fin_cases j <;> by_cases hp : k % 2 = 1 <;>
          simp only [hp, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] <;> decide
      have normalize (p q : ℤ × ℤ)
          (hp : p ∈ (if sym then capSymbolComplement (shift j) else capColumnComplement (shift j)))
          (hq : q ∈ (if sym then capSymbolComplement (shift j) else capColumnComplement (shift j)))
          (heq : residue k hk (p.1 * (k : ℤ) + p.2) =
            residue k hk (q.1 * (k : ℤ) + q.2)) : p = q := by
        cases sym <;> simp only [Bool.false_eq_true, ↓reduceIte] at hp hq
        all_goals simp only [capColumnComplement, capSymbolComplement,
          List.mem_append, List.mem_map, List.mem_range] at hp hq
        all_goals rcases hp with (((⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) |
          ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩)
        all_goals rcases hq with (((⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩) |
          ⟨v, hv, rfl⟩) | ⟨v, hv, rfl⟩)
        all_goals have hcases := residue_eq_cases _ _ (by simp [order]; omega) heq
        all_goals simp [order] at hcases ⊢
        all_goals rcases hcases with h | h | h <;> omega
      intro i l heq
      apply hpair
      apply normalize _ _
        ((hcertificate sym).mem_iff.mp (List.mem_ofFn.mpr ⟨i, rfl⟩))
        ((hcertificate sym).mem_iff.mp (List.mem_ofFn.mpr ⟨l, rfl⟩))
      cases sym
      · change column k hk j (capRow k hk i) = column k hk j (capRow k hk l) at heq
        simpa only [Bool.false_eq_true, ↓reduceIte, hcapcol i, hcapcol l] using heq
      · change symbol k hk j (capRow k hk i) = symbol k hk j (capRow k hk l) at heq
        simpa only [↓reduceIte, hcapsym i, hcapsym l] using heq
    have hcross (sym : Bool) (p : ℤ × ℤ)
        (hp : p ∈ (if sym then capSymbolComplement (shift j)
                          else capColumnComplement (shift j)))
        (t : Fin (k - 9)) (r : Fin 4) :
        residue k hk (p.1 * (k : ℤ) + p.2) ≠
          residue k hk (if sym then bulkSymbolRaw k j t.val r.val
                              else bulkColumnRaw k j t.val r.val) := by
      intro heq
      have ht := t.isLt
      cases sym <;> simp only [Bool.false_eq_true, ↓reduceIte] at hp heq
      all_goals simp only [capColumnComplement, capSymbolComplement,
        List.mem_append, List.mem_map, List.mem_range] at hp
      all_goals rcases hp with (((⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) |
        ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩)
      all_goals fin_cases r
      all_goals
        have hcases := residue_eq_cases _ _ (by
          simp [bulkColumnRaw, bulkSymbolRaw, order]
          omega) heq
        simp [bulkColumnRaw, bulkSymbolRaw, order] at hcases
        rcases hcases with h | h | h <;> omega
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
            exact hcapinj sym heq
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
            exact hbulkinj sym heq
          cases hi
          rfl
    exact ⟨hbij false, hbij true⟩

  have source_compatibility (j : Fin 3)
      (a : Fin (order k)) :
      symbol k hk j a = square k hk a (column k hk j a) := by
    have bulk_source_compatibility (t : Fin (k - 9)) (r : Fin 4) :
      square k hk (bulkRow k hk t r)
        (column k hk j (bulkRow k hk t r)) =
      symbol k hk j (bulkRow k hk t r) := by
      let a := bulkRow k hk t r
      let b := column k hk j a
      have ht : t.val + 9 < k := by have := t.isLt; omega
      have hr : r.val < 4 := r.isLt
      have ha : 15 ≤ a.val ∧ a.val < order k - 21 := by
        dsimp [a, bulkRow, order]
        omega
      have hq : (a.val - 15) / 4 = t.val := by
        dsimp [a, bulkRow]
        omega
      have hs : (a.val - 15) % 4 = r.val := by
        dsimp [a, bulkRow]
        omega
      have hraw : columnRaw k hk j a = bulkColumnRaw k j t.val r.val := by
        simp [columnRaw, not_lt.mpr ha.1, Nat.not_le.mpr ha.2, hq, hs]
      have hsym : symbolRaw k hk j a = bulkSymbolRaw k j t.val r.val := by
        simp [symbolRaw, not_lt.mpr ha.1, Nat.not_le.mpr ha.2, hq, hs]
      have hsum : bulkSymbolRaw k j t.val r.val =
          (a.val : ℤ) + bulkColumnRaw k j t.val r.val +
            (if r.val = 0 then 2 else 0) := by
        fin_cases r <;> simp [a, bulkRow, bulkSymbolRaw, bulkColumnRaw] <;> ring
      have hb : (b.val : ℤ) = bulkColumnRaw k j t.val r.val % (order k) := by
        have hnonneg : 0 ≤ bulkColumnRaw k j t.val r.val % (order k : ℤ) :=
          Int.emod_nonneg _ (by dsimp [order]; omega)
        simp [b, column, residue, hraw, Int.toNat_of_nonneg hnonneg]
      have hdelta : delta k a b = (if r.val = 0 then 2 else 0) := by
        have ha4 : a.val % 4 = (3 + r.val) % 4 := by
          dsimp [a, bulkRow]
          omega
        have hparity : (b.val : ℤ) % 2 = bulkColumnRaw k j t.val r.val % 2 := by
          rw [hb]
          exact Int.emod_emod_of_dvd _ (by dsimp [order]; omega)
        have hparityNat : b.val % 2 = (bulkColumnRaw k j t.val r.val % 2).toNat := by
          have hnonneg : 0 ≤ bulkColumnRaw k j t.val r.val % (2 : ℤ) :=
            Int.emod_nonneg _ (by decide)
          omega
        have hsmall0 : a.val ≠ 0 ∧ a.val ≠ 5 ∧ a.val ≠ 10 := by omega
        have hsmall1 : a.val ≠ 1 ∧ a.val ≠ 6 ∧ a.val ≠ 11 := by omega
        have hsmall4 : a.val ≠ 4 ∧ a.val ≠ 9 ∧ a.val ≠ 14 := by omega
        have hdelta : delta k a b =
            if a.val % 4 = 3 ∧ b.val % 2 = 0 then 2
            else if a.val % 4 = 1 ∧ b.val % 2 = 0 then -2 else 0 := by
          simp [delta, hsmall0.1, hsmall0.2.1, hsmall0.2.2,
            hsmall1.1, hsmall1.2.1, hsmall1.2.2,
            hsmall4.1, hsmall4.2.1, hsmall4.2.2, ha.1, ha.2]
        change delta k a b = if r.val = 0 then 2 else 0
        rw [hdelta]
        fin_cases r <;> fin_cases j
        all_goals simp [ha4, hparityNat, bulkColumnRaw, shift]
      change residue k hk ((a.val : ℤ) + (b.val : ℤ) + delta k a b) =
        residue k hk (symbolRaw k hk j a)
      rw [hdelta, hsym, hsum]
      apply Fin.ext
      simp only [residue]
      rw [hb]
      simp [Int.add_emod]
    have head_source_compatibility (i : Fin 15) :
      square k hk (headRow k hk i)
        (column k hk j (headRow k hk i)) =
      symbol k hk j (headRow k hk i) := by
      let a := headRow k hk i
      let b := column k hk j a
      have hsym : symbolRaw k hk j a =
          (a.val : ℤ) + columnRaw k hk j a + capEpsilon j ⟨i.val, by omega⟩ := by
        simp [symbolRaw, a, headRow]
      have hb : (b.val : ℤ) = columnRaw k hk j a % (order k : ℤ) := by
        have hnonneg : 0 ≤ columnRaw k hk j a % (order k : ℤ) :=
          Int.emod_nonneg _ (by dsimp [order]; omega)
        simp [b, column, residue, Int.toNat_of_nonneg hnonneg]
      have hdelta : delta k a b = capEpsilon j ⟨i.val, by omega⟩ := by
        let raw := columnRaw k hk j a
        have hraw : raw =
            let p := capAffine j (k % 2 = 1) ⟨i.val, by omega⟩
            p.1 * (k : ℤ) + p.2 := by
          simp [raw, columnRaw, a, headRow]
        have hbound : -3 ≤ raw ∧ raw < order k := by
          rw [hraw]
          fin_cases i <;> fin_cases j
          all_goals by_cases hp : k % 2 = 1
          all_goals (simp [capAffine, capTable, order, hp]; omega)
        have hmod : (b.val : ℤ) = raw % (order k : ℤ) := by
          have hnonneg : 0 ≤ raw % (order k : ℤ) :=
            Int.emod_nonneg _ (by dsimp [order]; omega)
          simp [b, column, residue, raw, Int.toNat_of_nonneg hnonneg]
        have hord : 36 ≤ order k := by dsimp [order]; omega
        have hb : (b.val : ℤ) = if raw < 0 then raw + order k else raw := by
          by_cases hn : raw < 0
          · have hstep : 0 ≤ raw + order k ∧ raw + order k < order k := by omega
            have hshift : raw % (order k : ℤ) = (raw + order k) % (order k : ℤ) := by
              simp
            rw [hmod, if_pos hn, hshift, Int.emod_eq_of_lt hstep.1 hstep.2]
          · have hnonneg : 0 ≤ raw := by omega
            rw [hmod, if_neg hn, Int.emod_eq_of_lt hnonneg hbound.2]
        have hbNat : b.val = (if raw < 0 then raw + order k else raw).toNat := by
          omega
        change delta k a b = capEpsilon j ⟨i.val, by omega⟩
        fin_cases i <;> fin_cases j
        all_goals by_cases hp : k % 2 = 1
        all_goals simp [delta, a, headRow, hbNat, hraw, capAffine,
          capTable, capEpsilon, order, hp] <;> omega
      change residue k hk ((a.val : ℤ) + (b.val : ℤ) + delta k a b) =
        residue k hk (symbolRaw k hk j a)
      rw [hdelta, hsym]
      apply Fin.ext
      simp only [residue]
      rw [hb]
      simp [Int.add_emod]
    have tail_source_compatibility (i : Fin 21) :
      square k hk (tailRow k hk i)
        (column k hk j (tailRow k hk i)) =
      symbol k hk j (tailRow k hk i) := by
      let a := tailRow k hk i
      let b := column k hk j a
      have htail : order k - 21 ≤ a.val := by simp [a, tailRow]
      have hhead : 15 ≤ a.val := by dsimp [a, tailRow, order]; omega
      have hdelta : delta k a b = 0 := by
        simp [delta, show a.val ≠ 0 by omega, show a.val ≠ 5 by omega,
          show a.val ≠ 10 by omega, show a.val ≠ 1 by omega,
          show a.val ≠ 6 by omega, show a.val ≠ 11 by omega,
          show a.val ≠ 4 by omega, show a.val ≠ 9 by omega,
          show a.val ≠ 14 by omega, Nat.not_lt.mpr htail]
      have hsym : symbolRaw k hk j a = (a.val : ℤ) + columnRaw k hk j a := by
        simp [symbolRaw, not_lt.mpr hhead, htail]
      have hb : (b.val : ℤ) = columnRaw k hk j a % (order k : ℤ) := by
        have hnonneg : 0 ≤ columnRaw k hk j a % (order k : ℤ) :=
          Int.emod_nonneg _ (by dsimp [order]; omega)
        simp [b, column, residue, Int.toNat_of_nonneg hnonneg]
      change residue k hk ((a.val : ℤ) + (b.val : ℤ) + delta k a b) =
        residue k hk (symbolRaw k hk j a)
      rw [hdelta, hsym]
      apply Fin.ext
      simp only [residue]
      rw [hb]
      simp [Int.add_emod]
    by_cases hhead : a.val < 15
    · let i : Fin 15 := ⟨a.val, hhead⟩
      have ha : headRow k hk i = a := by apply Fin.ext; rfl
      rw [← ha]
      exact (head_source_compatibility i).symm
    by_cases htail : order k - 21 ≤ a.val
    · let i : Fin 21 := ⟨a.val - (order k - 21), by
          have := a.isLt
          omega⟩
      have ha : tailRow k hk i = a := by
        apply Fin.ext
        dsimp [tailRow, i]
        omega
      rw [← ha]
      exact (tail_source_compatibility i).symm
    · have ha15 : 15 ≤ a.val := by omega
      let u := a.val - 15
      let t : Fin (k - 9) := ⟨u / 4, by
        have hlt := a.isLt
        dsimp [u, order] at *
        omega⟩
      let r : Fin 4 := ⟨u % 4, Nat.mod_lt _ (by decide)⟩
      have ha : bulkRow k hk t r = a := by
        apply Fin.ext
        dsimp [bulkRow, t, r, u]
        omega
      rw [← ha]
      exact (bulk_source_compatibility t r).symm
  have hT (j : Fin 3) : IsTransversal k hk (T k hk j) := by
    have hperm := coordinate_permutations j
    refine ⟨?_,?_,?_,?_⟩
    · rintro f ⟨a,rfl⟩
      exact source_compatibility j a
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
  have hcapResidue
      (odd : Bool) (i : Fin 36) :
      let p := capAffine 0 odd i
      let q := capAffine 1 odd i
      residue k hk (p.1 * (k : ℤ) + p.2) =
        residue k hk (q.1 * (k : ℤ) + q.2) ↔ i.val = 11 := by
    let p := capAffine 0 odd i
    let q := capAffine 1 odd i
    let x := p.1 * (k : ℤ) + p.2
    let y := q.1 * (k : ℤ) + q.2
    let d := x - y
    have hdexpr : d = (p.1 - q.1) * (k : ℤ) + p.2 - q.2 := by
      dsimp [d, x, y]
      ring
    have hd : (d = 0 ↔ i.val = 11) ∧ -(order k : ℤ) < d ∧ d < order k := by
      have hbase :
          (((p.1 - q.1) * (k : ℤ) + p.2 - q.2 = 0 ↔ i.val = 11) ∧
          -(order k : ℤ) < (p.1 - q.1) * (k : ℤ) + p.2 - q.2 ∧
          (p.1 - q.1) * (k : ℤ) + p.2 - q.2 < order k) := by
        dsimp [p,q]
        fin_cases i <;> cases odd <;>
          simp [capAffine,capTable,order] <;> omega
      change (((p.1 - q.1) * (k : ℤ) + p.2 - q.2 = 0 ↔ i.val = 11) ∧
        -(order k : ℤ) < (p.1 - q.1) * (k : ℤ) + p.2 - q.2 ∧
        (p.1 - q.1) * (k : ℤ) + p.2 - q.2 < order k) at hbase
      rw [← hdexpr] at hbase
      exact hbase
    change residue k hk x = residue k hk y ↔ i.val = 11
    constructor
    · intro heq
      have hmod : x % (order k : ℤ) = y % (order k : ℤ) := by
        have hv := congrArg (fun z : Fin (order k) => (z.val : ℤ)) heq
        have hx : 0 ≤ x % (order k : ℤ) :=
          Int.emod_nonneg _ (by dsimp [order]; omega)
        have hy : 0 ≤ y % (order k : ℤ) :=
          Int.emod_nonneg _ (by dsimp [order]; omega)
        simpa [residue, Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy] using hv
      have hz : d % (order k : ℤ) = 0 := by
        simpa [d] using (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp hmod
      have hpos : (0 : ℤ) < order k := by dsimp [order]; omega
      have hd0 : d = 0 := by
        by_cases h : 0 ≤ d
        · have heqmod : d % (order k : ℤ) = d := Int.emod_eq_of_lt h hd.2.2
          omega
        · have hstep : 0 ≤ d + order k ∧ d + order k < order k := by omega
          have heqmod : (d + order k) % (order k : ℤ) = d + order k :=
            Int.emod_eq_of_lt hstep.1 hstep.2
          have hsame : (d + order k) % (order k : ℤ) = d % (order k : ℤ) := by
            simp
          omega
      exact hd.1.mp hd0
    · intro hi
      have hd0 := hd.1.mpr hi
      have hxy : x = y := by dsimp [d] at hd0; omega
      rw [hxy]
  have hcolumnEquality
      (a : Fin (order k)) :
      column k hk 0 a = column k hk 1 a ↔ a.val = 11 := by
    by_cases hhead : a.val < 15
    · let i : Fin 36 := ⟨a.val, by omega⟩
      have hcol (j : Fin 3) :
          column k hk j a =
            let p := capAffine j (k % 2 = 1) i
            residue k hk (p.1 * (k : ℤ) + p.2) := by
        simp [column, columnRaw, hhead, i]
      rw [hcol 0, hcol 1]
      exact hcapResidue (k % 2 = 1) i
    by_cases htail : order k - 21 ≤ a.val
    · let i : Fin 36 := ⟨a.val - (order k - 21) + 15, by
          have := a.isLt
          omega⟩
      have hcol (j : Fin 3) :
          column k hk j a =
            let p := capAffine j (k % 2 = 1) i
            residue k hk (p.1 * (k : ℤ) + p.2) := by
        simp [column, columnRaw, not_lt.mpr (by omega : 15 ≤ a.val), htail, i]
      rw [hcol 0, hcol 1]
      have hi := hcapResidue (k % 2 = 1) i
      exact hi.trans (by
        constructor <;> intro h
        · dsimp [i, order] at h
          omega
        · omega)
    · have hbulk : 15 ≤ a.val ∧ a.val < order k - 21 := by omega
      let t := (a.val - 15) / 4
      let r := (a.val - 15) % 4
      have hraw : bulkColumnRaw k 0 t r = bulkColumnRaw k 1 t r + 4 := by
        have hr : r < 4 := Nat.mod_lt _ (by decide)
        interval_cases r <;> simp [bulkColumnRaw, shift] <;> ring
      have hcol (j : Fin 3) :
          column k hk j a = residue k hk (bulkColumnRaw k j t r) := by
        simp [column, columnRaw, not_lt.mpr hbulk.1,
          Nat.not_le.mpr hbulk.2, t, r]
      rw [hcol 0, hcol 1, hraw]
      have hneq : residue k hk (bulkColumnRaw k 1 t r + 4) ≠
          residue k hk (bulkColumnRaw k 1 t r) := by
        intro heq
        have hmod : (bulkColumnRaw k 1 t r + 4) % (order k : ℤ) =
            bulkColumnRaw k 1 t r % (order k : ℤ) := by
          have hv := congrArg (fun z : Fin (order k) => (z.val : ℤ)) heq
          have hx : 0 ≤ (bulkColumnRaw k 1 t r + 4) % (order k : ℤ) :=
            Int.emod_nonneg _ (by dsimp [order]; omega)
          have hy : 0 ≤ bulkColumnRaw k 1 t r % (order k : ℤ) :=
            Int.emod_nonneg _ (by dsimp [order]; omega)
          simpa [residue, Int.toNat_of_nonneg hx,
            Int.toNat_of_nonneg hy] using hv
        have hz : (4 : ℤ) % (order k : ℤ) = 0 := by
          simpa using (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp hmod
        have hfour : (4 : ℤ) % (order k : ℤ) = 4 :=
          Int.emod_eq_of_lt (by omega) (by dsimp [order]; omega)
        omega
      simp [hneq]
      omega
  have hcommon : T k hk 0 ∩ T k hk 1 = {d2 k hk} ∧
      T k hk 0 ∩ T k hk 1 ∩ T k hk 2 = ∅ := by
    let row : Fin (order k) := ⟨11, by dsimp [order]; omega⟩
    have hrow : residue k hk 11 = row := by
      apply Fin.ext
      change ((11 : ℤ) % (order k : ℤ)).toNat = 11
      rw [Int.emod_eq_of_lt (by omega) (by dsimp [order]; omega)]
      rfl
    have hcap (j : Fin 3) (hj : j.val = 0 ∨ j.val = 1) :
        column k hk j row = residue k hk 9 ∧
        symbol k hk j row = residue k hk 23 := by
      fin_cases j
      all_goals by_cases hp : k % 2 = 1
      all_goals simp [column, columnRaw, symbol, symbolRaw, row,
        capAffine, capTable, capEpsilon, hp] at *
    have hentry (j : Fin 3) (hj : j.val = 0 ∨ j.val = 1) :
        entry k hk j row = d2 k hk := by
      have hc := hcap j hj
      simp [entry, d2, hrow, hc.1, hc.2]
    have hthird : entry k hk 2 row ≠ d2 k hk := by
      intro heq
      have hc := congrArg (fun e : Fin (order k) × Fin (order k) × Fin (order k) =>
        e.2.1) heq
      change column k hk 2 row = residue k hk 9 at hc
      have hraw : column k hk 2 row =
          residue k hk (if k % 2 = 1 then 2 * (k : ℤ) + 9
            else 2 * (k : ℤ) + 7) := by
        by_cases hp : k % 2 = 1 <;>
          simp [column, columnRaw, row, capAffine, capTable, hp]
      rw [hraw] at hc
      have hmod : (if k % 2 = 1 then 2 * (k : ℤ) + 9
            else 2 * (k : ℤ) + 7) % (order k : ℤ) = 9 := by
        have hv := congrArg (fun z : Fin (order k) => (z.val : ℤ)) hc
        have hx : 0 ≤ (if k % 2 = 1 then 2 * (k : ℤ) + 9
            else 2 * (k : ℤ) + 7) % (order k : ℤ) :=
          Int.emod_nonneg _ (by dsimp [order]; omega)
        have h9 : (9 : ℤ) % (order k : ℤ) = 9 :=
          Int.emod_eq_of_lt (by omega) (by dsimp [order]; omega)
        simpa [residue, Int.toNat_of_nonneg hx, h9] using hv
      have hlt : 0 ≤ (if k % 2 = 1 then 2 * (k : ℤ) + 9
            else 2 * (k : ℤ) + 7) ∧
          (if k % 2 = 1 then 2 * (k : ℤ) + 9
            else 2 * (k : ℤ) + 7) < order k := by
        dsimp [order]
        split <;> omega
      rw [Int.emod_eq_of_lt hlt.1 hlt.2] at hmod
      split at hmod <;> omega
    have hcommon : T k hk 0 ∩ T k hk 1 = {d2 k hk} := by
      ext e
      constructor
      · intro he
        rcases he.1 with ⟨a, rfl⟩
        rcases he.2 with ⟨b, hab⟩
        have hr : b = a := by simpa [entry] using congrArg Prod.fst hab
        subst b
        have hc : column k hk 0 a = column k hk 1 a :=
          (by simpa [entry] using
            (congrArg (fun e : Fin (order k) × Fin (order k) × Fin (order k) =>
              e.2.1) hab).symm)
        have ha : a = row := by
          apply Fin.ext
          exact (hcolumnEquality a).mp hc
        subst a
        simpa [hentry 0 (Or.inl rfl)]
      · intro he
        have heq : e = d2 k hk := by simpa using he
        subst e
        constructor
        · exact ⟨row, hentry 0 (Or.inl rfl)⟩
        · exact ⟨row, hentry 1 (Or.inr rfl)⟩
    constructor
    · exact hcommon
    · rw [hcommon]
      ext e
      constructor
      · intro he
        have heq : e = d2 k hk := by simpa using he.1
        subst e
        rcases he.2 with ⟨a, ha⟩
        have hr : a = row := by
          have h := congrArg Prod.fst ha
          change a = residue k hk 11 at h
          simpa [hrow] using h
        subst a
        exact (hthird ha).elim
      · simp
  refine ⟨?_,?_,hcommon.1,hcommon.2,hpair,?_⟩
  · dsimp [order,k]
    omega
  · intro j
    exact ⟨(coordinate_permutations j).1,(coordinate_permutations j).2,
      source_compatibility j,hT j,hD j⟩
  · intro f hpin
    have hf : f ∈ T k hk 0 ∩ T k hk 1 ∩ T k hk 2 :=
      ⟨⟨hpin.2 _ (hT 0),hpin.2 _ (hT 1)⟩,hpin.2 _ (hT 2)⟩
    rw [hcommon.2] at hf
    exact hf
#print axioms result

end D5.S3.Combinatorics.LatinHFamilyTheorem
