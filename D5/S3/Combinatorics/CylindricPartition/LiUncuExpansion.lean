/- GID: D5/S3/Combinatorics/CylindricPartition/LiUncuExpansion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CylindricPartition/LiUncuExpansion
   mirror-E: none(waiver:iterated-peak-deletion)
   anchors: []
   utility: none
   digest: Iterated peak deletion gives the fixed finite multiple sum. -/

import D5.S3.Combinatorics.CylindricPartition.LiUncuRecurrence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CylindricPartition.LiUncu

open Polynomial LiUncuDefs

/-- Unrolling deletion counts every bounded nonincreasing tuple with its exact weight. -/
theorem lhs_path_expansion (n k i : ℕ) (hk : 1 ≤ k) (hi : 1 ≤ i) (hik : i ≤ k) :
    lhs n k i = ∑ N ∈ Finset.range (n + 1),
      refinedPathSum (k - 1) ((k : ℤ) - i) (2 * n) N := by
  classical
  let V (H : ℕ) := Fin H → Fin (n + 1)
  let e {H : ℕ} (v : V H) (j : ℕ) : ℕ := if h : j < H then (v ⟨j, h⟩).val else 0
  let ordered {H : ℕ} (v : V H) := ∀ x y : Fin H, x ≤ y → v y ≤ v x
  let term (H : ℕ) (a L : ℤ) (v : V H) : ℤ[X] :=
    X ^ (∑ j : Fin H, (e v j.val ^ 2 + if (H : ℤ) ≤ j.val + a then e v j.val else 0)) *
      ∏ j : Fin H,
        gaussPrime
          (L - 2 * (∑ l ∈ Finset.range j.val, (e v l : ℤ)) - e v j.val -
            e v (j.val + 1) - 2 * max ((j.val : ℤ) + a - H + 1) 0)
          ((e v j.val : ℤ) - e v (j.val + 1))
  have e_zero {H : ℕ} (v : V (H + 1)) : e v 0 = (v 0).val := by simp [e]
  have e_cons {H : ℕ} (x : Fin (n + 1)) (v : V H) (j : ℕ) :
      e (Fin.cons x v) (j + 1) = e v j := by
    dsimp [e]
    split_ifs with h h'
    · have he : (⟨j + 1, h⟩ : Fin (H + 1)) = (⟨j, h'⟩ : Fin H).succ := rfl
      rw [he, Fin.cons_succ]
    · omega
    · omega
    · rfl
  have ordered_cons {H : ℕ} (x : Fin (n + 1)) (v : V H) :
      ordered (Fin.cons x v) ↔ ordered v ∧ e v 0 ≤ x.val := by
    constructor
    · intro hv
      refine ⟨fun j l hjl => ?_, ?_⟩
      · simpa using hv j.succ l.succ (by simpa using hjl)
      · by_cases h : 0 < H
        · have hh := hv 0 (⟨0, h⟩ : Fin H).succ (by simp)
          change (v ⟨0, h⟩).val ≤ x.val at hh
          simpa [e, h] using hh
        · simp [e, h]
    · rintro ⟨hv, hx⟩ j l hjl
      cases j using Fin.cases with
      | zero =>
          cases l using Fin.cases with
          | zero => rfl
          | succ l =>
              simp only [Fin.cons_zero, Fin.cons_succ]
              have h : 0 < H := Nat.zero_lt_of_lt l.isLt
              have hh := hv ⟨0, h⟩ l (by change 0 ≤ l.val; omega)
              have hx' : (v ⟨0, h⟩).val ≤ x.val := by simpa [e, h] using hx
              exact le_trans hh hx'
      | succ j =>
          cases l using Fin.cases with
          | zero => simp at hjl
          | succ l => simpa using hv j l (by simpa using hjl)
  have peel (H : ℕ) (a L : ℤ) (ha : 0 ≤ a) (haH : a ≤ H + 1)
      (boundary : Bool) (hb : boundary = true ↔ a = H + 1)
      (N : ℕ) (hN : N ≤ n) (v : V H) :
      term (H + 1) a L (Fin.cons ⟨N, by omega⟩ v) =
        X ^ (N ^ 2 + boundary.toNat * N) *
          gaussPrime (L - 2 * N - 2 * boundary.toNat + N - e v 0)
            ((N : ℤ) - e v 0) *
          term H (a - boundary.toNat) (L - 2 * N - 2 * boundary.toNat) v := by
    have hd : (if (H + 1 : ℤ) ≤ a then N else 0) = boundary.toNat * N := by
      cases boundary <;> simp_all <;> omega
    have hshift (j : ℕ) :
        ((H + 1 : ℤ) ≤ (j + 1 : ℕ) + a ↔ (H : ℤ) ≤ j + (a - boundary.toNat)) ∧
        max (((j + 1 : ℕ) : ℤ) + a - (H + 1) + 1) 0 =
          boundary.toNat + max ((j : ℤ) + (a - boundary.toNat) - H + 1) 0 := by
      cases boundary <;> simp_all <;> omega
    have hsum (j : ℕ) :
        (∑ l ∈ Finset.range (j + 1), (e (Fin.cons ⟨N, by omega⟩ v) l : ℤ)) =
          N + ∑ l ∈ Finset.range j, (e v l : ℤ) := by
      rw [Finset.sum_range_succ']
      simp only [e_cons, e_zero, Fin.cons_zero]
      omega
    dsimp only [term]
    rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, e_zero, Fin.cons_zero, e_cons,
      Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero, zero_add,
      Nat.cast_add, Nat.cast_one, Nat.cast_zero]
    rw [hd]
    have halpha : max (a - (H + 1) + 1) 0 = (boundary.toNat : ℤ) := by
      cases boundary <;> simp_all <;> omega
    rw [halpha]
    have hw :
        (∑ j : Fin H, (e v j.val ^ 2 +
          if (H + 1 : ℤ) ≤ (j.val : ℤ) + 1 + a then e v j.val else 0)) =
        ∑ j : Fin H, (e v j.val ^ 2 +
          if (H : ℤ) ≤ (j.val : ℤ) + (a - boundary.toNat) then e v j.val else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [show ((H + 1 : ℤ) ≤ (j.val : ℤ) + 1 + a) ↔
        (H : ℤ) ≤ (j.val : ℤ) + (a - boundary.toNat) by simpa using (hshift j.val).1]
    rw [hw, pow_add]
    have hp :
        (∏ j : Fin H,
          gaussPrime
            (L - 2 * ∑ l ∈ Finset.range (j.val + 1),
              (e (Fin.cons ⟨N, by omega⟩ v) l : ℤ) - e v j.val -
              e v (j.val + 1) -
              2 * max ((j.val : ℤ) + 1 + a - (H + 1) + 1) 0)
            ((e v j.val : ℤ) - e v (j.val + 1))) =
        ∏ j : Fin H,
          gaussPrime
            (L - 2 * N - 2 * boundary.toNat -
              2 * ∑ l ∈ Finset.range j.val, (e v l : ℤ) - e v j.val -
              e v (j.val + 1) - 2 * max ((j.val : ℤ) +
                (a - boundary.toNat) - H + 1) 0)
            ((e v j.val : ℤ) - e v (j.val + 1)) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [hsum, show max ((j.val : ℤ) + 1 + a - (H + 1) + 1) 0 =
        boundary.toNat + max ((j.val : ℤ) + (a - boundary.toNat) - H + 1) 0 by
          simpa using (hshift j.val).2]
      congr 1
      ring
    rw [hp]
    have ht : L - N - e v 0 - 2 * (boundary.toNat : ℤ) =
        L - 2 * N - 2 * boundary.toNat + N - e v 0 := by ring
    rw [ht]
    ring
  have expansion (H : ℕ) (a L : ℤ) (ha : 0 ≤ a) (haH : a ≤ H)
      (hL : Even L) (N : ℕ) (hN : N ≤ n) :
      refinedPathSum H a L N =
        ∑ v : V H, if ordered v ∧ e v 0 = N then term H a L v else 0 := by
    induction H generalizing a L N with
    | zero =>
        have ha0 : a = 0 := by omega
        subst a
        rw [path_zero_height]
        simp [ordered, term, e, V, eq_comm]
    | succ H ih =>
        let boundary : Bool := decide (a = H + 1)
        have hb : boundary = true ↔ a = H + 1 := by simp [boundary]
        have ha' : 0 ≤ a - boundary.toNat := by
          cases h : boundary <;> simp_all [boundary] <;> omega
        have haH' : a - boundary.toNat ≤ H := by
          cases h : boundary <;> simp_all [boundary] <;> omega
        have hL' : Even (L - 2 * N - 2 * boundary.toNat) := by
          exact (hL.sub (even_two_mul _)).sub (even_two_mul _)
        rw [path_deletion_recurrence (H + 1) (by omega) a ha haH L hL N boundary hb]
        simp only [Nat.add_sub_cancel]
        have hi (s : ℕ) (hs : s ∈ Finset.range (N + 1)) :=
          ih (a - boundary.toNat) (L - 2 * N - 2 * boundary.toNat) ha' haH' hL' s
            (by have := Finset.mem_range.mp hs; omega)
        have hsub :
            (∑ s ∈ Finset.range (N + 1),
              gaussPrime (L - 2 * N - 2 * boundary.toNat + N - s) ((N : ℤ) - s) *
                refinedPathSum H (a - boundary.toNat) (L - 2 * N - 2 * boundary.toNat) s) =
            ∑ s ∈ Finset.range (N + 1),
              gaussPrime (L - 2 * N - 2 * boundary.toNat + N - s) ((N : ℤ) - s) *
                ∑ v : V H, if ordered v ∧ e v 0 = s then
                  term H (a - boundary.toNat) (L - 2 * N - 2 * boundary.toNat) v else 0 := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [hi s hs]
        rw [hsub]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        let equiv : V (H + 1) ≃ Fin (n + 1) × V H :=
          { toFun := fun v => (v 0, fun j => v j.succ)
            invFun := fun p => Fin.cons p.1 p.2
            left_inv := by intro v; funext j; cases j using Fin.cases <;> simp
            right_inv := by intro p; cases p; simp }
        rw [← equiv.symm.sum_comp
          (fun v => if ordered v ∧ e v 0 = N then term (H + 1) a L v else 0)]
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_eq_single (⟨N, by omega⟩ : Fin (n + 1))]
        · simp only [equiv, Equiv.coe_fn_symm_mk, ordered_cons, e_zero, Fin.cons_zero]
          apply Finset.sum_congr rfl
          intro v _
          by_cases hv : ordered v ∧ e v 0 ≤ N
          · rw [Finset.sum_eq_single (e v 0)]
            · simp only [hv.1, hv.2, and_true, ite_true]
              rw [peel H a L ha haH boundary hb N hN v]
              ring
            · intro s hs hne
              have he : e v 0 ≠ s := Ne.symm hne
              simp [he]
            · intro hnot
              exact (hnot (Finset.mem_range.mpr (by omega))).elim
          · have hz : ∀ s ∈ Finset.range (N + 1),
                ¬(ordered v ∧ e v 0 = s) := by
              intro s hs h
              apply hv
              exact ⟨h.1, by have := Finset.mem_range.mp hs; omega⟩
            trans 0
            · apply Finset.sum_eq_zero
              intro s hs
              simp only [hz s hs, ite_false, mul_zero]
            · simp [hv]
        · intro x _ hne
          apply Finset.sum_eq_zero
          intro v _
          have hx : x.val ≠ N := fun h => hne (Fin.ext h)
          simp [equiv, e_zero, hx]
        · simp
  have final : lhs n k i =
      ∑ N ∈ Finset.range (n + 1),
        ∑ v : V (k - 1), if ordered v ∧ e v 0 = N then
          term (k - 1) ((k : ℤ) - i) (2 * n) v else 0 := by
    unfold lhs
    rw [Finset.sum_filter, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    have hv : e v 0 ≤ n := by
      dsimp [e]
      split_ifs
      · exact Nat.le_of_lt_succ (v _).isLt
      · omega
    rw [Finset.sum_eq_single (e v 0)]
    · by_cases h : ordered v
      · change (if ordered v then leftTerm n k i v else 0) = _
        simp only [h, ite_true, and_self]
        change leftTerm n k i v = term (k - 1) ((k : ℤ) - i) (2 * n) v
        have he (j : ℕ) : entry v (j + 1) = (e v j : ℤ) := by
          dsimp [entry, e]
          split_ifs with h h'
          · congr 2
          · omega
          · omega
          · rfl
        have he' (j : ℕ) (hj : 1 ≤ j) : entry v j = (e v (j - 1) : ℤ) := by
          simpa [Nat.sub_add_cancel hj] using he (j - 1)
        have shift (f : ℕ → ℤ) :
            (∑ j ∈ Finset.Icc 1 (k - 1), f j) =
              ∑ j : Fin (k - 1), f (j.val + 1) := by
          apply Finset.sum_bij (fun j hj =>
            (⟨j - 1, by have := Finset.mem_Icc.mp hj; omega⟩ : Fin (k - 1)))
          · intro j hj; simp
          · intro j hj l hl h
            have heq : j - 1 = l - 1 := congrArg Fin.val h
            have := Finset.mem_Icc.mp hj
            have := Finset.mem_Icc.mp hl
            omega
          · intro j _
            refine ⟨j.val + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
            ext
            simp
          · intro j hj
            change f j = f (j - 1 + 1)
            have := Finset.mem_Icc.mp hj
            congr 1
            omega
        have hlin : (∑ j ∈ Finset.Icc i (k - 1), entry v j) =
            ∑ j ∈ Finset.Icc 1 (k - 1), if i ≤ j then entry v j else 0 := by
          rw [← Finset.sum_filter]
          congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_Icc]
          omega
        have hw :
            (∑ j ∈ Finset.Icc 1 (k - 1), entry v j ^ 2 +
              ∑ j ∈ Finset.Icc i (k - 1), entry v j) =
            ((∑ j : Fin (k - 1), (e v j.val ^ 2 +
              if ((k - 1 : ℕ) : ℤ) ≤ j.val + ((k : ℤ) - i)
                then e v j.val else 0) : ℕ) : ℤ) := by
          rw [hlin, shift, shift]
          simp only [he, Nat.cast_sum, Nat.cast_add, Nat.cast_pow, Nat.cast_ite,
            Nat.cast_zero, Finset.sum_add_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          simp only [show (i ≤ j.val + 1) ↔
            (((k - 1 : ℕ) : ℤ) ≤ (j.val : ℤ) + ((k : ℤ) - i)) by omega]
        have prefix_sum (j : ℕ) (hj : 1 ≤ j) :
            (∑ l ∈ Finset.Ico 1 j, entry v l) =
              ∑ l ∈ Finset.range (j - 1), (e v l : ℤ) := by
          apply Finset.sum_bij (fun l _ => l - 1)
          · intro l hl
            have := Finset.mem_Ico.mp hl
            apply Finset.mem_range.mpr
            omega
          · intro l hl t ht h
            have := Finset.mem_Ico.mp hl
            have := Finset.mem_Ico.mp ht
            omega
          · intro l hl
            refine ⟨l + 1, Finset.mem_Ico.mpr ⟨by omega, ?_⟩, by omega⟩
            have := Finset.mem_range.mp hl
            omega
          · intro l hl
            exact he' l (Finset.mem_Ico.mp hl).1
        unfold leftTerm
        dsimp only [term]
        rw [hw, Int.toNat_natCast]
        congr 1
        apply Finset.prod_bij (fun j hj =>
          (⟨j - 1, by have := Finset.mem_Icc.mp hj; omega⟩ : Fin (k - 1)))
        · intro j hj; simp
        · intro j hj l hl h
          have heq : j - 1 = l - 1 := congrArg Fin.val h
          have := Finset.mem_Icc.mp hj
          have := Finset.mem_Icc.mp hl
          omega
        · intro j _
          refine ⟨j.val + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
          ext
          simp
        · intro j hj
          have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
          rw [prefix_sum j hj1, he' j hj1, he]
          have hjj : j - 1 + 1 = j := by omega
          simp only [hjj]
          unfold alpha
          congr 1
          congr 1
          omega
      · change (if ordered v then leftTerm n k i v else 0) = _
        simp only [h, false_and, ite_false]
    · intro N hN hne
      simp [Ne.symm hne]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  rw [final]
  apply Finset.sum_congr rfl
  intro N hN
  symm
  exact expansion (k - 1) ((k : ℤ) - i) (2 * n) (by omega) (by omega)
    (even_two_mul _) N (by have := Finset.mem_range.mp hN; omega)

end D5.S3.Combinatorics.CylindricPartition.LiUncu
