/- GID: D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionBasic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/IndecomposableInversion/FranklinInversionBasic
   mirror-E: none(waiver:canonical-star-family)
   anchors: []
   utility: none
   digest: Canonical star and five-block permutations give indecomposable pattern avoiders. -/

import D5.S3.Combinatorics.IndecomposableInversion.FranklinInversionDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.IndecomposableInversion.FranklinInversion

open D5.S3.Combinatorics
open FranklinInversionDefs

def star (k : ℕ) : List ℕ := (k + 1) :: List.range' 1 k


def fiveBlock (r t d h : ℕ) : List ℕ :=
  List.range' (t + 1) r ++ List.range' 1 (t - d) ++
    ((r + t + h + 1) :: (List.range' (t - d + 1) d ++ List.range' (t + r + 1) h))

theorem fiveBlock_mem_avoiders (r t d h : ℕ)
    (hr : 1 ≤ r) (ht : 1 ≤ t) (hd : 1 ≤ d) (hdt : d ≤ t) :
    fiveBlock r t d h ∈ FranklinInversionDefs.avoiders (r * t + d + h) := by
  let s := t - d
  let n := r + t + h + 1
  let m := r + s
  have hsd : s + d = t := by dsimp [s]; omega
  have hlength : (fiveBlock r t d h).length = n := by
    simp only [fiveBlock, List.length_append, List.length_range', List.length_cons]
    dsimp [n]
    omega
  have hrangeGet (start count index : ℕ) (hi : index < count) :
      (List.range' start count).getD index 0 = start + index := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  have hget (index : ℕ) (hi : index < n) :
      (fiveBlock r t d h).getD index 0 =
        if index < r then t + 1 + index else
        if index < m then index - r + 1 else
        if index = m then n else
        if index < r + t + 1 then index - r else index := by
    unfold fiveBlock
    rw [List.append_assoc]
    by_cases hir : index < r
    · rw [List.getD_append _ _ _ _ (by simpa using hir)]
      simp only [hir, ite_true]
      exact hrangeGet _ _ _ hir
    · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_range', hir, ite_false]
      by_cases him : index < m
      · rw [List.getD_append _ _ _ _ (by simp; dsimp [m, s] at him; omega)]
        simp only [him, ite_true]
        rw [hrangeGet 1 (t - d) (index - r) (by dsimp [m, s] at him; omega)]
        omega
      · rw [List.getD_append_right _ _ _ _ (by simp; dsimp [m, s] at him; omega)]
        simp only [List.length_range', him, ite_false]
        by_cases hieq : index = m
        · have hz : index - r - (t - d) = 0 := by dsimp [m, s] at hieq; omega
          rw [hz]
          simp only [List.getD_cons_zero, hieq, ite_true]
          rfl
        · have hpos : 0 < index - r - (t - d) := by dsimp [m, s] at *; omega
          obtain ⟨offset, hoffset⟩ := Nat.exists_eq_succ_of_ne_zero (by omega :
            index - r - (t - d) ≠ 0)
          rw [hoffset, List.getD_cons_succ]
          simp only [hieq, ite_false]
          by_cases hiend : index < r + t + 1
          · rw [List.getD_append _ _ _ _ (by simp; dsimp [m, s] at *; omega),
              hrangeGet _ _ _ (by dsimp [m, s] at *; omega)]
            simp only [hiend, ite_true]
            dsimp [m, s] at *
            omega
          · rw [List.getD_append_right _ _ _ _ (by simp; dsimp [m, s] at *; omega)]
            simp only [List.length_range', hiend, ite_false]
            rw [hrangeGet _ _ _ (by dsimp [n, m, s] at *; omega)]
            dsimp [m, s] at *
            omega
  have hinversion (index next : ℕ) (hi : index < n) (hj : next < n) :
      (index < next ∧
        (fiveBlock r t d h).getD next 0 < (fiveBlock r t d h).getD index 0) ↔
      (index < r ∧ (r ≤ next ∧ next < m ∨ m < next ∧ next < r + t + 1)) ∨
        (index = m ∧ m < next) := by
    rw [hget index hi, hget next hj]
    dsimp [m, s, n] at *
    split_ifs <;> omega
  have hperm : (fiveBlock r t d h).Perm (List.range' 1 n) := by
    let high := List.range' (t + 1) r
    let consumed := List.range' 1 s
    let residual := List.range' (s + 1) d
    let finalHigh := List.range' (t + r + 1) h
    have hlow : consumed ++ residual = List.range' 1 t := by
      dsimp [consumed, residual]
      have := List.range'_append (s := 1) (m := s) (n := d) (step := 1)
      simpa [hsd, Nat.add_comm] using this
    have hhigh : high ++ finalHigh = List.range' (t + 1) (r + h) := by
      dsimp [high, finalHigh]
      have := List.range'_append (s := t + 1) (m := r) (n := h) (step := 1)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    have hall : consumed ++ residual ++ high ++ finalHigh ++ [n] = List.range' 1 n := by
      rw [hlow]
      rw [List.append_assoc (List.range' 1 t) high finalHigh, hhigh]
      have hjoin := List.range'_append (s := 1) (m := t) (n := r + h) (step := 1)
      rw [show List.range' 1 t ++ List.range' (t + 1) (r + h) =
        List.range' 1 (t + (r + h)) by simpa [Nat.add_comm] using hjoin]
      have hlast := List.range'_concat (s := 1) (n := t + (r + h)) (step := 1)
      simpa [n, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlast.symm
    have hmove : (n :: (residual ++ finalHigh)).Perm (residual ++ finalHigh ++ [n]) := by
      simpa using
        (List.perm_middle (a := n) (l₁ := residual ++ finalHigh) (l₂ := [])).symm
    have hmove' := (hmove.append_left consumed).append_left high
    have hswap :=
      (List.perm_append_comm (l₁ := high) (l₂ := consumed ++ residual)).append_right
        (finalHigh ++ [n])
    have hfirst : (fiveBlock r t d h).Perm
        ((high ++ (consumed ++ residual)) ++ (finalHigh ++ [n])) := by
      simpa [fiveBlock, high, consumed, residual, finalHigh, s, n, List.append_assoc]
        using hmove'
    have := hfirst.trans hswap
    simp only [← List.append_assoc] at this
    rwa [hall] at this
  have hindices : List.range n = List.range' 0 r ++ List.range' r s ++ [m] ++
      List.range' (m + 1) d ++ List.range' (r + t + 1) h := by
    have hjoin (count extra : ℕ) :
        List.range' 0 count ++ List.range' count extra =
          List.range' 0 (count + extra) := by
      simpa using (List.range'_append (s := 0) (m := count) (n := extra) (step := 1))
    rw [hjoin r s]
    rw [show [m] = List.range' m 1 by simp]
    rw [hjoin (r + s) 1]
    rw [hjoin (r + s + 1) d]
    rw [show r + t + 1 = r + s + 1 + d by omega, hjoin (r + s + 1 + d) h]
    rw [List.range_eq_range']
    congr 1
    dsimp [n]
    omega
  have hinv : inv (fiveBlock r t d h) = r * t + d + h := by
    let row := fun index =>
      ((List.range n).filter fun next => decide (index < next ∧
        (fiveBlock r t d h).getD next 0 < (fiveBlock r t d h).getD index 0)).length
    have hrow (index : ℕ) (hi : index ∈ List.range n) :
        row index = if index < r then t else if index = m then d + h else 0 := by
      have hi' := List.mem_range.mp hi
      have hfilter :
          (List.range n).filter (fun next => decide (index < next ∧
              (fiveBlock r t d h).getD next 0 < (fiveBlock r t d h).getD index 0)) =
            (List.range n).filter (fun next => decide
              ((index < r ∧ (r ≤ next ∧ next < m ∨ m < next ∧ next < r + t + 1)) ∨
                (index = m ∧ m < next))) := by
        apply List.filter_congr
        intro next hj
        simp only [hinversion index next hi' (List.mem_range.mp hj)]
      have hfilterConst (values : List ℕ) (predicate : ℕ → Bool) (value : Bool)
          (hpred : ∀ next ∈ values, predicate next = value) :
          values.filter predicate = if value then values else [] := by
        cases value
        · exact List.filter_eq_nil_iff.mpr (by intro next hj; simpa using hpred next hj)
        · exact List.filter_eq_self.mpr (by intro next hj; simpa using hpred next hj)
      dsimp [row]
      rw [hfilter, hindices]
      simp only [List.filter_append, List.filter_cons, List.filter_nil]
      by_cases hir : index < r
      · have hne : index ≠ m := by dsimp [m]; omega
        simp only [hir, hne, true_and, false_and, or_false, ite_true, Nat.lt_irrefl,
          ite_false]
        rw [hfilterConst _ _ false (by
            intro next hj; simp only [List.mem_range'] at hj
            obtain ⟨offset, hoff, rfl⟩ := hj
            dsimp [m]; simp only [decide_eq_false_iff_not]; omega),
          hfilterConst _ _ true (by
            intro next hj; simp only [List.mem_range'] at hj
            obtain ⟨offset, hoff, rfl⟩ := hj
            dsimp [m]; simp only [decide_eq_true_eq]; omega),
          hfilterConst _ _ true (by
            intro next hj; simp only [List.mem_range'] at hj
            obtain ⟨offset, hoff, rfl⟩ := hj
            dsimp [m]; simp only [decide_eq_true_eq]; omega),
          hfilterConst _ _ false (by
            intro next hj; simp only [List.mem_range'] at hj
            obtain ⟨offset, hoff, rfl⟩ := hj
            dsimp [m]; simp only [decide_eq_false_iff_not]; omega)]
        simp [hsd]
      · simp only [hir, false_and, false_or, ite_false]
        by_cases hieq : index = m
        · simp only [hieq, true_and, ite_true, Nat.lt_irrefl, decide_false,
            Bool.false_eq_true, ite_false]
          rw [hfilterConst _ _ false (by
              intro next hj; simp only [List.mem_range'] at hj
              obtain ⟨offset, hoff, rfl⟩ := hj
              dsimp [m]; simp only [decide_eq_false_iff_not]; omega),
            hfilterConst _ _ false (by
              intro next hj; simp only [List.mem_range'] at hj
              obtain ⟨offset, hoff, rfl⟩ := hj
              dsimp [m]; simp only [decide_eq_false_iff_not]; omega),
            hfilterConst _ _ true (by
              intro next hj; simp only [List.mem_range'] at hj
              obtain ⟨offset, hoff, rfl⟩ := hj
              simp only [decide_eq_true_eq]; omega),
            hfilterConst _ _ true (by
              intro next hj; simp only [List.mem_range'] at hj
              obtain ⟨offset, hoff, rfl⟩ := hj
              dsimp [m]; simp only [decide_eq_true_eq]; omega)]
          simp
        · simp [hieq]
    unfold inv
    rw [hlength]
    change ((List.range n).map row).sum = _
    rw [List.map_congr_left hrow, hindices]
    have hmapConst (values : List ℕ) (f : ℕ → ℕ) (value : ℕ)
        (hf : ∀ index ∈ values, f index = value) :
        (values.map f).sum = values.length * value := by
      rw [List.map_congr_left hf]
      simp
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil]
    rw [hmapConst _ _ t (by
        intro index hi; simp only [List.mem_range'] at hi
        obtain ⟨offset, hoff, rfl⟩ := hi; simp [hoff]),
      hmapConst _ _ 0 (by
        intro index hi; simp only [List.mem_range'] at hi
        obtain ⟨offset, hoff, rfl⟩ := hi
        dsimp [m]; split_ifs <;> omega),
      hmapConst _ _ 0 (by
        intro index hi; simp only [List.mem_range'] at hi
        obtain ⟨offset, hoff, rfl⟩ := hi
        dsimp [m]; split_ifs <;> omega),
      hmapConst _ _ 0 (by
        intro index hi; simp only [List.mem_range'] at hi
        obtain ⟨offset, hoff, rfl⟩ := hi
        dsimp [m]; split_ifs <;> omega)]
    have hmr : ¬ m < r := by dsimp [m]; omega
    simp [hmr, Nat.add_assoc]
  refine ⟨n, by dsimp [n]; omega, hperm, ?_, hinv, ?_, ?_⟩
  · intro cut hcut hproper hprefix
    rw [hlength] at hproper
    have hcross : ∃ index next, index < cut ∧ cut ≤ next ∧ next < n ∧
        (fiveBlock r t d h).getD next 0 < (fiveBlock r t d h).getD index 0 := by
      by_cases hcm : cut ≤ m
      · refine ⟨0, r + t, by omega, ?_, ?_, ?_⟩
        · dsimp [m, s] at hcm; omega
        · dsimp [n]; omega
        · rw [hget 0 (by dsimp [n]; omega),
            hget (r + t) (by dsimp [n]; omega)]
          dsimp [m, s]
          split_ifs <;> omega
      · refine ⟨m, n - 1, by omega, by omega, by dsimp [n]; omega, ?_⟩
        rw [hget m (by dsimp [m, s, n]; omega), hget (n - 1) (by dsimp [n]; omega)]
        dsimp [m, s, n]
        split_ifs <;> omega
    obtain ⟨index, next, hi, hj, hjn, hinv⟩ := hcross
    have htop : (fiveBlock r t d h).getD index 0 < cut + 1 := by
      have hmem : (fiveBlock r t d h).getD index 0 ∈ (fiveBlock r t d h).take cut := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.mem_take_iff_getElem.mpr ⟨index, by omega, rfl⟩
      have := hprefix.mem_iff.mp hmem
      simp only [List.mem_range'] at this
      obtain ⟨offset, hoff, heq⟩ := this
      omega
    have hbottom : (fiveBlock r t d h).getD next 0 ∈ List.range' 1 cut := by
      simp only [List.mem_range']
      refine ⟨(fiveBlock r t d h).getD next 0 - 1, by omega, ?_⟩
      have hpositive : 1 ≤ (fiveBlock r t d h).getD next 0 := by
        rw [hget next hjn]
        dsimp [m, s, n]
        split_ifs <;> omega
      omega
    have hmem := hprefix.mem_iff.mpr hbottom
    obtain ⟨before, hb, heq⟩ := List.mem_take_iff_getElem.mp hmem
    have hnodup := hperm.nodup_iff.mpr (List.nodup_range' (s := 1) (n := n))
    have hnext : next < (fiveBlock r t d h).length := by omega
    rw [List.getD_eq_getElem _ _ hnext] at heq
    have := hnodup.getElem_inj_iff.mp heq
    omega
  · rintro ⟨values, hincreasing, _, hsublist, _⟩
    have h12 : values 1 < values 2 := hincreasing 1 (by omega) (by decide)
    have h23 : values 2 < values 3 := hincreasing 2 (by omega) (by decide)
    have hsub : [values 3, values 2, values 1].Sublist (fiveBlock r t d h) := by
      simpa using hsublist
    obtain ⟨embedding, hembedding⟩ :=
      List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    let first := embedding ⟨0, by simp⟩
    let second := embedding ⟨1, by simp⟩
    let third := embedding ⟨2, by simp⟩
    have hfirst : first.val < n := by simpa [hlength] using first.isLt
    have hsecond : second.val < n := by simpa [hlength] using second.isLt
    have hthird : third.val < n := by simpa [hlength] using third.isLt
    have hfs : first.val < second.val := embedding.strictMono (by simp)
    have hst : second.val < third.val := embedding.strictMono (by simp)
    have hvalue (index : Fin 3) :
        (fiveBlock r t d h).getD (embedding index).val 0 =
          [values 3, values 2, values 1].get index := by
      rw [List.getD_eq_getElem _ _ (embedding index).isLt]
      exact (hembedding index).symm
    have hfsinv : (fiveBlock r t d h).getD second.val 0 <
        (fiveBlock r t d h).getD first.val 0 := by
      dsimp only [first, second]
      rw [hvalue, hvalue]
      exact h23
    have hstinv : (fiveBlock r t d h).getD third.val 0 <
        (fiveBlock r t d h).getD second.val 0 := by
      dsimp only [second, third]
      rw [hvalue, hvalue]
      exact h12
    have hf := (hinversion first.val second.val hfirst hsecond).mp ⟨hfs, hfsinv⟩
    have hs := (hinversion second.val third.val hsecond hthird).mp ⟨hst, hstinv⟩
    dsimp [m, s] at *
    omega
  · rintro ⟨values, hincreasing, _, hsublist, _⟩
    have h12 : values 1 < values 2 := hincreasing 1 (by omega) (by decide)
    have h23 : values 2 < values 3 := hincreasing 2 (by omega) (by decide)
    have h34 : values 3 < values 4 := hincreasing 3 (by omega) (by decide)
    have hsub : [values 1, values 3, values 4, values 2].Sublist
        (fiveBlock r t d h) := by simpa using hsublist
    obtain ⟨embedding, hembedding⟩ :=
      List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    let first := embedding ⟨0, by simp⟩
    let second := embedding ⟨1, by simp⟩
    let third := embedding ⟨2, by simp⟩
    let fourth := embedding ⟨3, by simp⟩
    have hfirst : first.val < n := by simpa [hlength] using first.isLt
    have hsecond : second.val < n := by simpa [hlength] using second.isLt
    have hthird : third.val < n := by simpa [hlength] using third.isLt
    have hfourth : fourth.val < n := by simpa [hlength] using fourth.isLt
    have hfs : first.val < second.val := embedding.strictMono (by simp)
    have hst : second.val < third.val := embedding.strictMono (by simp)
    have htf : third.val < fourth.val := embedding.strictMono (by simp)
    have hvalue (index : Fin 4) :
        (fiveBlock r t d h).getD (embedding index).val 0 =
          [values 1, values 3, values 4, values 2].get index := by
      rw [List.getD_eq_getElem _ _ (embedding index).isLt]
      exact (hembedding index).symm
    have hsfInv : (fiveBlock r t d h).getD fourth.val 0 <
        (fiveBlock r t d h).getD second.val 0 := by
      dsimp only [second, fourth]
      rw [hvalue, hvalue]
      exact h23
    have htfInv : (fiveBlock r t d h).getD fourth.val 0 <
        (fiveBlock r t d h).getD third.val 0 := by
      have := Nat.lt_trans h23 h34
      dsimp only [third, fourth]
      rw [hvalue, hvalue]
      exact this
    have hff : (fiveBlock r t d h).getD first.val 0 <
        (fiveBlock r t d h).getD fourth.val 0 := by
      dsimp only [first, fourth]
      rw [hvalue, hvalue]
      exact h12
    have hs := (hinversion second.val fourth.val hsecond hfourth).mp ⟨by omega, hsfInv⟩
    have ht' := (hinversion third.val fourth.val hthird hfourth).mp ⟨htf, htfInv⟩
    rw [hget first.val hfirst, hget fourth.val hfourth] at hff
    dsimp [m, s, n] at *
    split_ifs at hff <;> omega

end D5.S3.Combinatorics.IndecomposableInversion.FranklinInversion
