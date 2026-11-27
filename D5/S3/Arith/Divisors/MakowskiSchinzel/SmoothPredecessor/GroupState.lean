/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/GroupState
   generality: G
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors; instance=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors
   digest: Label projection of table transitions and every fixed-point prefix check. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.CertificateState

/-! Projection of a successful table run onto a single group. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor

/-- The fixed-point product of a list of successor values. -/
def fixedProduct : ℕ → List ℕ → ℕ
  | L, [] => L
  | L, q :: qs => fixedProduct (L * (q - 1) / q) qs

/-- Entries carrying label `i`, preserving the full table's order. -/
def groupValues (i : ℕ) (es : List ℕ) : List ℕ :=
  (es.filter (fun e => entryLabel e = i)).map entryValue

/-- A successful run checks every proper prefix and computes the group's final state. -/
theorem stepTable_group {ts : List (ℕ × ℕ × ℕ)} {es : List ℕ}
    {st st' : List (ℕ × ℕ)} {i p j L : ℕ} {t : ℕ × ℕ × ℕ}
    (hrun : stepTable ts es st = some st') (hp : oddPrimes[i]? = some p)
    (hs : st[i]? = some (j, L)) (ht : ts[i]? = some t) :
    st'[i]? = some (j + (groupValues i es).length,
      fixedProduct L (groupValues i es)) ∧
    ∀ k < (groupValues i es).length,
      prefixOk p (j + k) (fixedProduct L ((groupValues i es).take k)) t = true := by
  induction es generalizing st j L with
  | nil =>
    have he : st = st' := Option.some.inj hrun
    subst st'
    simpa [groupValues, fixedProduct] using hs
  | cons e es ih =>
    obtain ⟨pe, je, Le, te, hpe, hse, hte, hc, hr⟩ := stepTable_head.mp hrun
    by_cases hei : entryLabel e = i
    · subst i
      have he_p : pe = p := Option.some.inj (hpe.symm.trans hp)
      have he_s : (je, Le) = (j, L) := Option.some.inj (hse.symm.trans hs)
      have he_t : te = t := Option.some.inj (hte.symm.trans ht)
      cases he_p
      cases he_s
      cases he_t
      have hi : entryLabel e < st.length := (List.getElem?_eq_some_iff.mp hs).1
      have hnext : (st.set (entryLabel e)
          (j + 1, L * (entryValue e - 1) / entryValue e))[entryLabel e]? =
            some (j + 1, L * (entryValue e - 1) / entryValue e) :=
        List.getElem?_set_self hi
      obtain ⟨hf, hchecks⟩ := ih hr hnext
      have hvals : groupValues (entryLabel e) (e :: es) =
          entryValue e :: groupValues (entryLabel e) es := by simp [groupValues]
      rw [hvals]
      constructor
      · simpa only [List.length_cons, fixedProduct, Nat.add_assoc, Nat.add_comm 1] using hf
      · intro k hk
        cases k with
        | zero => simpa [fixedProduct] using hc
        | succ k =>
          have hk' : k < (groupValues (entryLabel e) es).length := by simpa using hk
          simpa only [List.take_succ_cons, fixedProduct, Nat.add_assoc,
            Nat.add_comm 1] using hchecks k hk'
    · have hnext : (st.set (entryLabel e)
          (je + 1, Le * (entryValue e - 1) / entryValue e))[i]? = some (j, L) := by
        rw [List.getElem?_set_ne hei]
        exact hs
      have hvals : groupValues i (e :: es) = groupValues i es := by
        simp [groupValues, hei]
      rw [hvals]
      exact ih hr hnext

/-- Rounding down at each step gives a lower bound on the exact rational product. -/
theorem fixedProduct_le (L : ℕ) (qs : List ℕ) :
    (fixedProduct L qs : ℚ) ≤
      L * (qs.map (fun q : ℕ => ((q : ℚ) - 1) / q)).prod := by
  induction qs generalizing L with
  | nil => simp [fixedProduct]
  | cons q qs ih =>
    by_cases hzero : q = 0
    · subst q
      have hz : ∀ qs : List ℕ, fixedProduct 0 qs = 0 := by
        intro qs
        induction qs with
        | nil => rfl
        | cons a qs ih => simpa only [fixedProduct, zero_mul, Nat.zero_div] using ih
      simp [fixedProduct, hz]
    have hq1 : 1 ≤ q := by omega
    have hprod : 0 ≤ (qs.map (fun q : ℕ => ((q : ℚ) - 1) / q)).prod := by
      apply List.prod_nonneg
      intro a ha
      obtain ⟨x, hx, hxa⟩ :=
        (List.mem_map (f := fun q : ℕ => ((q : ℚ) - 1) / q)).mp ha
      rw [← hxa]
      by_cases hx0 : x = 0
      · simp [hx0]
      · have hx1 : (1 : ℚ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
        exact div_nonneg (by linarith) (Nat.cast_nonneg x)
    have hround : ((L * (q - 1) / q : ℕ) : ℚ) ≤ L * (((q : ℚ) - 1) / q) := by
      have hh := (Nat.cast_div_le (m := L * (q - 1)) (n := q) :
        ((L * (q - 1) / q : ℕ) : ℚ) ≤ (L * (q - 1) : ℕ) / q)
      simpa [Nat.cast_mul, Nat.cast_sub hq1, mul_div_assoc] using hh
    calc
      (fixedProduct L (q :: qs) : ℚ) ≤
          (L * (q - 1) / q : ℕ) * (qs.map (fun q : ℕ => ((q : ℚ) - 1) / q)).prod :=
        ih _
      _ ≤ (L * (((q : ℚ) - 1) / q)) *
          (qs.map (fun q : ℕ => ((q : ℚ) - 1) / q)).prod :=
        mul_le_mul_of_nonneg_right hround hprod
      _ = L * ((q :: qs).map (fun q : ℕ => ((q : ℚ) - 1) / q)).prod := by
        change (_ * _) * _ = _ * (_ * _)
        exact mul_assoc _ _ _

/-- Under a successful run, all prefixes pass exactly when the last prefix passes. -/
theorem stepTable_all_prefixes {ts : List (ℕ × ℕ × ℕ)} {es : List ℕ}
    {st st' : List (ℕ × ℕ)} {i p j L : ℕ} {t : ℕ × ℕ × ℕ}
    (hrun : stepTable ts es st = some st') (hp : oddPrimes[i]? = some p)
    (hs : st[i]? = some (j, L)) (ht : ts[i]? = some t) :
    (∀ k ≤ (groupValues i es).length,
      prefixOk p (j + k) (fixedProduct L ((groupValues i es).take k)) t = true) ↔
      prefixOk p (j + (groupValues i es).length)
        (fixedProduct L (groupValues i es)) t = true := by
  obtain ⟨_, hproper⟩ := stepTable_group hrun hp hs ht
  constructor
  · intro h
    simpa only [List.take_length] using h (groupValues i es).length le_rfl
  · intro h k hk
    rcases hk.eq_or_lt with heq | hlt
    · subst k
      simpa only [List.take_length] using h
    · exact hproper k hlt

end D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
