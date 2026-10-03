/- GID: D5/S3/Combinatorics/IndecomposableInversion/FranklinInversion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/IndecomposableInversion/FranklinInversion
   mirror-E: none(waiver:triangular-counting-bijection)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs.claim; result=D5/S3/Combinatorics/IndecomposableInversion/FranklinInversion.result; claim=D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs.claim
   digest: Euclidean division bijects the five-block family with a triangular set of pairs. -/

import D5.S3.Combinatorics.IndecomposableInversion.FranklinInversionClassification

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.IndecomposableInversion.FranklinInversion

open D5.S3.Combinatorics
open FranklinInversionDefs

theorem avoiders_ncard (k : ℕ) :
    (FranklinInversionDefs.avoiders k).ncard = k * (k - 1) / 2 + 1 := by
  classical
  have hstarMembership (k : ℕ) : star k ∈ FranklinInversionDefs.avoiders k := by
    have hget (index : ℕ) (hi : index < k + 1) :
        (star k).getD index 0 = if index = 0 then k + 1 else index := by
      cases index with
      | zero => simp [star]
      | succ index =>
        have hi' : index < k := by omega
        simp [star, hi', Nat.add_comm]
    have hinv : inv (star k) = k := by
      have hrow (index : ℕ) (hi : index ∈ List.range (k + 1)) :
          ((List.range (k + 1)).filter fun next => decide
            (index < next ∧ (star k).getD next 0 < (star k).getD index 0)).length =
            if index = 0 then k else 0 := by
        have hi' : index < k + 1 := List.mem_range.mp hi
        by_cases hz : index = 0
        · subst index
          have hfilter :
              (List.range (k + 1)).filter (fun next => decide
                  (0 < next ∧ (star k).getD next 0 < (star k).getD 0 0)) =
                (List.range (k + 1)).filter (fun next => decide (0 < next)) := by
            apply List.filter_congr
            intro next hn
            rw [hget next (List.mem_range.mp hn), hget 0 (by omega)]
            simp only [ite_true]
            by_cases hnext : next = 0 <;> simp [hnext, List.mem_range.mp hn]
          rw [hfilter, List.range_succ_eq_map]
          simp [List.filter_map, Function.comp_def]
        · have hfilter :
              (List.range (k + 1)).filter (fun next => decide
                (index < next ∧ (star k).getD next 0 < (star k).getD index 0)) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro next hn
            rw [hget next (List.mem_range.mp hn), hget index hi']
            simp only [hz, ite_false]
            by_cases hnext : next = 0
            · simp [hnext]
            · simp only [hnext, ite_false, decide_eq_true_eq]
              omega
          rw [hfilter]
          simp [hz]
      unfold inv
      have hlength : (star k).length = k + 1 := by simp [star]
      simp only [hlength]
      have hmap := List.map_congr_left hrow
      rw [hmap, List.range_succ_eq_map]
      simp [List.map_map, Function.comp_def]
    refine ⟨k + 1, by omega, ?_, ?_, hinv, ?_, ?_⟩
    · rw [List.range'_concat]
      simpa [star, Nat.add_comm] using
        (List.perm_middle (a := k + 1) (l₁ := List.range' 1 k) (l₂ := [])).symm
    · intro cut hcut hproper hperm
      have hbound : cut ≤ k := by simpa [star] using hproper
      have hmem : k + 1 ∈ (star k).take cut := by
        obtain ⟨cut, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : cut ≠ 0)
        simp [star]
      have := hperm.mem_iff.mp hmem
      simp only [List.mem_range', Nat.one_mul] at this
      omega
    · rintro ⟨values, hincreasing, _, hsublist, _⟩
      have h12 : values 1 < values 2 := hincreasing 1 (by omega) (by decide)
      have htail : [values 2, values 1].Sublist (List.range' 1 k) := by
        simpa [star] using hsublist.tail
      have hordered := (List.pairwise_lt_range' (s := 1) (n := k)).sublist htail
      have h21 : values 2 < values 1 :=
        (List.pairwise_cons.mp hordered).1 _ (by simp)
      omega
    · rintro ⟨values, hincreasing, _, hsublist, _⟩
      have h23 : values 2 < values 3 := hincreasing 2 (by omega) (by decide)
      have htail : [values 3, values 4, values 2].Sublist (List.range' 1 k) := by
        simpa [star] using hsublist.tail
      have hordered := (List.pairwise_lt_range' (s := 1) (n := k)).sublist htail
      have h32 : values 3 < values 2 :=
        (List.pairwise_cons.mp hordered).1 _ (by simp)
      omega
  have hlength (r t d h : ℕ) (hdt : d ≤ t) :
      (fiveBlock r t d h).length = r + t + h + 1 := by
    simp only [fiveBlock, List.length_append, List.length_range', List.length_cons]
    omega
  have hfront (r t d h index : ℕ) (hi : index < r) :
      (fiveBlock r t d h).getD index 0 = t + 1 + index := by
    unfold fiveBlock
    rw [List.append_assoc, List.getD_append _ _ _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  have hboundary (r t d h : ℕ) :
      (fiveBlock r t d h).getD r 0 = if t - d = 0 then r + t + h + 1 else 1 := by
    unfold fiveBlock
    rw [List.append_assoc, List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_range', Nat.sub_self]
    cases hs : t - d with
    | zero => simp
    | succ count => rw [List.range'_succ]; simp
  have hmax (r t d h : ℕ) :
      (fiveBlock r t d h).getD (r + (t - d)) 0 = r + t + h + 1 := by
    unfold fiveBlock
    rw [List.append_assoc, List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_range', Nat.add_sub_cancel_left]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hunique (r t d h r' t' d' h' : ℕ)
      (hr : 1 ≤ r) (ht : 1 ≤ t) (hd : 1 ≤ d) (hdt : d ≤ t)
      (hr' : 1 ≤ r') (ht' : 1 ≤ t') (hd' : 1 ≤ d') (hdt' : d' ≤ t')
      (heq : fiveBlock r t d h = fiveBlock r' t' d' h') :
      r = r' ∧ t = t' ∧ d = d' ∧ h = h' := by
    have hlen := congrArg List.length heq
    rw [hlength _ _ _ _ hdt, hlength _ _ _ _ hdt'] at hlen
    have hhead := congrArg (fun values => values.getD 0 0) heq
    rw [hfront r t d h 0 (by omega), hfront r' t' d' h' 0 (by omega)] at hhead
    have htt : t = t' := by omega
    subst t'
    have hrr : r = r' := by
      rcases lt_trichotomy r r' with hlt | heq' | hgt
      · have hvalue := congrArg (fun values => values.getD r 0) heq
        rw [hboundary, hfront _ _ _ _ _ hlt] at hvalue
        split_ifs at hvalue <;> omega
      · exact heq'
      · have hvalue := congrArg (fun values => values.getD r' 0) heq
        rw [hfront _ _ _ _ _ hgt, hboundary] at hvalue
        split_ifs at hvalue <;> omega
    subst r'
    obtain ⟨_, _, hperm, _, _, _, _⟩ := fiveBlock_mem_avoiders r t d h hr ht hd hdt
    have hnodup := hperm.nodup_iff.mpr List.nodup_range'
    have hm := hmax r t d h
    have hm' := hmax r t d' h'
    rw [← heq] at hm'
    have hright : r + t + h' + 1 = r + t + h + 1 := by omega
    rw [hright] at hm'
    have hsame := hm.trans hm'.symm
    have hbound : r + (t - d) < (fiveBlock r t d h).length := by
      rw [hlength _ _ _ _ hdt]
      omega
    have hbound' : r + (t - d') < (fiveBlock r t d h).length := by
      rw [hlength _ _ _ _ hdt]
      omega
    rw [List.getD_eq_getElem _ _ hbound, List.getD_eq_getElem _ _ hbound'] at hsame
    have hindices := hnodup.getElem_inj_iff.mp hsame
    exact ⟨rfl, rfl, by omega, by omega⟩
  let pairs := Σ upper : Fin k, Fin upper.val
  let pairList : pairs → List ℕ := fun pair =>
    fiveBlock (pair.1.val / (pair.2.val + 1)) (pair.2.val + 1)
      (pair.1.val % (pair.2.val + 1) + 1) (k - (pair.1.val + 1))
  let encode : Option pairs → List ℕ := fun code =>
    match code with
    | none => star k
    | some pair => pairList pair
  have hdata (pair : pairs) :
      1 ≤ pair.1.val / (pair.2.val + 1) ∧ 1 ≤ pair.2.val + 1 ∧
      1 ≤ pair.1.val % (pair.2.val + 1) + 1 ∧
      pair.1.val % (pair.2.val + 1) + 1 ≤ pair.2.val + 1 ∧
      pair.1.val / (pair.2.val + 1) * (pair.2.val + 1) +
        (pair.1.val % (pair.2.val + 1) + 1) + (k - (pair.1.val + 1)) = k := by
    have hpositive : 0 < pair.2.val + 1 := by omega
    have hr : 1 ≤ pair.1.val / (pair.2.val + 1) := by
      apply (Nat.le_div_iff_mul_le hpositive).mpr
      have := pair.2.isLt
      simp only [Nat.one_mul]
      omega
    have hrem := Nat.mod_lt pair.1.val hpositive
    have hdiv := Nat.mod_add_div pair.1.val (pair.2.val + 1)
    rw [Nat.mul_comm] at hdiv
    have hupper := pair.1.isLt
    exact ⟨hr, by omega, by omega, by omega, by omega⟩
  have hmem (code : Option pairs) : encode code ∈ FranklinInversionDefs.avoiders k := by
    cases code with
    | none => exact hstarMembership k
    | some pair =>
      obtain ⟨hr, ht, hd, hdt, hinv⟩ := hdata pair
      dsimp [encode, pairList]
      have hmember := fiveBlock_mem_avoiders _ _ _ (k - (pair.1.val + 1)) hr ht hd hdt
      rwa [hinv] at hmember
  have hnoStar (r t d h : ℕ) (hr : 1 ≤ r) (hd : 1 ≤ d)
      (hcount : r * t + d + h = k) : star k ≠ fiveBlock r t d h := by
    intro heq
    have hhead := congrArg (fun values => values.getD 0 0) heq
    rw [hfront _ _ _ _ 0 (by omega)] at hhead
    simp only [star, List.getD_cons_zero, Nat.add_zero] at hhead
    have hproduct : t ≤ r * t := by simpa using Nat.mul_le_mul_right t hr
    omega
  have hpairInjective : Function.Injective pairList := by
    rintro ⟨upper, lower⟩ ⟨upper', lower'⟩ heq
    obtain ⟨hr, ht, hd, hdt, _⟩ := hdata ⟨upper, lower⟩
    obtain ⟨hr', ht', hd', hdt', _⟩ := hdata ⟨upper', lower'⟩
    obtain ⟨hquot, hdenom, hrem, _⟩ :=
      hunique _ _ _ _ _ _ _ _ hr ht hd hdt hr' ht' hd' hdt' heq
    have hdivision := Nat.mod_add_div upper.val (lower.val + 1)
    have hdivision' := Nat.mod_add_div upper'.val (lower'.val + 1)
    dsimp only at hquot hdenom hrem
    have hdenomVal : lower.val = lower'.val := by omega
    have hremVal : upper.val % (lower.val + 1) = upper'.val % (lower'.val + 1) := by
      omega
    rw [hquot, hremVal, hdenomVal] at hdivision
    have hupper : upper = upper' := Fin.ext (by omega)
    subst upper'
    have hlower : lower = lower' := Fin.ext (by omega)
    subst lower'
    rfl
  have hinjective : Function.Injective encode := by
    intro first second heq
    cases first with
    | none =>
      cases second with
      | none => rfl
      | some pair =>
        obtain ⟨hr, _, hd, _, hcount⟩ := hdata pair
        exact False.elim (hnoStar _ _ _ _ hr hd hcount heq)
    | some pair =>
      cases second with
      | none =>
        obtain ⟨hr, _, hd, _, hcount⟩ := hdata pair
        exact False.elim (hnoStar _ _ _ _ hr hd hcount heq.symm)
      | some other => exact congrArg some (hpairInjective heq)
  have hsurjective (p : List ℕ) (hp : p ∈ FranklinInversionDefs.avoiders k) :
      ∃ code, encode code = p := by
    rcases classification p k hp with hstar | ⟨r, t, d, h, hr, ht, hd, hdt, hblock, hcount⟩
    · exact ⟨none, hstar.symm⟩
    · have hproduct : t ≤ r * t := by simpa using Nat.mul_le_mul_right t hr
      let upper : Fin k := ⟨r * t + d - 1, by omega⟩
      let lower : Fin upper.val := ⟨t - 1, by dsimp [upper]; omega⟩
      let pair : pairs := ⟨upper, lower⟩
      have hdenom : lower.val + 1 = t := by dsimp [lower]; omega
      have hquot : upper.val / t = r := by
        apply Nat.div_eq_of_lt_le
        · dsimp [upper]
          omega
        · rw [Nat.add_mul, Nat.one_mul]
          dsimp [upper]
          omega
      have hrem : upper.val % t + 1 = d := by
        have hdivision := Nat.mod_add_div upper.val t
        rw [hquot, Nat.mul_comm] at hdivision
        dsimp [upper] at *
        omega
      have htail : k - (upper.val + 1) = h := by dsimp [upper]; omega
      refine ⟨some pair, ?_⟩
      change fiveBlock (upper.val / (lower.val + 1)) (lower.val + 1)
        (upper.val % (lower.val + 1) + 1) (k - (upper.val + 1)) = p
      rw [hdenom, hquot, hrem, htail]
      exact hblock.symm
  have hrange : FranklinInversionDefs.avoiders k = Set.range encode := by
    ext p
    constructor
    · exact hsurjective p
    · rintro ⟨code, rfl⟩
      exact hmem code
  rw [hrange, Set.ncard_range_of_injective hinjective, Nat.card_eq_fintype_card]
  rw [Fintype.card_option, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  change (∑ upper : Fin k, upper.val) + 1 = _
  rw [Fin.sum_univ_eq_sum_range (fun value : ℕ => value) k, Finset.sum_range_id]

theorem result : ¬ FranklinInversionDefs.claim := by
  intro hclaim
  have hcorrect : (FranklinInversionDefs.avoiders 1).ncard = 1 := by
    calc
      (FranklinInversionDefs.avoiders 1).ncard = 1 * (1 - 1) / 2 + 1 :=
        avoiders_ncard 1
      _ = 1 := by norm_num
  have hprinted : (FranklinInversionDefs.avoiders 1).ncard = 2 := by
    calc
      (FranklinInversionDefs.avoiders 1).ncard = 1 * (1 + 1) / 2 + 1 := hclaim 1
      _ = 2 := by norm_num
  have hneq : (1 : ℕ) ≠ 2 := by norm_num
  exact hneq (hcorrect.symm.trans hprinted)

end D5.S3.Combinatorics.IndecomposableInversion.FranklinInversion
