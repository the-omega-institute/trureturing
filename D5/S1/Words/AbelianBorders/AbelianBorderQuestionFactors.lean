/- GID: D5/S1/Words/AbelianBorders/AbelianBorderQuestionFactors
   generality: G
   mirror-B: D5/B/S1/Words/AbelianBorders/AbelianBorderQuestionFactors
   mirror-E: none(waiver:unbounded-unbordered-factor-family)
   anchors: []
   utility: none
   digest: Prefix induction and chord exclusion prove an unbounded family unbordered. -/

import D5.S1.Words.AbelianBorders.AbelianBorderQuestionWord
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S1.Words.AbelianBorders.Counterexample
open AbelianBorderQuestionDefs

def F (m : ℕ) : List (Fin 3) := [1, 2] ++ (List.replicate m A).flatten ++ [0]

set_option maxHeartbeats 3000000 in
-- Prefix induction and all possible pairs of internal cuts are checked locally.
theorem unbordered (m : ℕ) : ¬ WeakAbelianBordered (F m) := by
  have countA (a : Fin 3) : A.count a = 5 := by fin_cases a <;> decide
  have powerLength (m : ℕ) : (List.replicate m A).flatten.length = 15*m := by
    simp [List.length_flatten, A, List.sum_replicate, Nat.mul_comm]
  have lengthF : (F m).length = 15*m + 3 := by simp [F, powerLength]
  have powerPrefix : ∀ m r, r ≤ 15*m → ∀ a : Fin 3,
      (((List.replicate m A).flatten).take r).count a =
        5 * (r / 15) + (A.take (r % 15)).count a := by
    intro m
    induction m with
    | zero =>
      intro r hr a
      have he : r = 0 := by omega
      subst r
      simp
    | succ m ih =>
      intro r hr a
      simp only [List.replicate_succ, List.flatten_cons]
      by_cases h : r < 15
      · have hl : r ≤ A.length := by simpa [A] using (show r ≤ 15 by omega)
        rw [List.take_append_of_le_length hl]
        simp [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      · have h15 : 15 ≤ r := by omega
        have hsub : r - 15 ≤ 15*m := by omega
        rw [List.take_append, List.take_of_length_le (by simpa [A] using h15),
          List.count_append, countA]
        have lenA : A.length = 15 := rfl
        rw [lenA, ih (r-15) hsub a]
        have hdiv : r / 15 = (r-15)/15 + 1 := by omega
        have hmod : r % 15 = (r-15)%15 := by omega
        rw [hdiv, hmod]
        omega
  have total (a : Fin 3) : (F m).count a = 5*m + 1 := by
    have hpow := powerPrefix m (15*m) (le_refl _) a
    rw [List.take_of_length_le (by rw [powerLength])] at hpow
    simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 15), Nat.mul_mod_right,
      List.take_zero, List.count_nil, Nat.add_zero] at hpow
    simp only [F, List.count_append, hpow]
    fin_cases a <;> norm_num [List.count_cons, List.count_nil, Fin.ext_iff] <;> omega
  have prefixCounts (i : ℕ) (hi : 2 ≤ i) (hi' : i < 15*m+3) (a : Fin 3) :
      ((F m).take i).count a = [1, 2].count a +
        5 * ((i-2)/15) + (A.take ((i-2)%15)).count a := by
    have hp : i-2 ≤ (List.replicate m A).flatten.length := by rw [powerLength]; omega
    have he : (F m).take i = [1, 2] ++ ((List.replicate m A).flatten).take (i-2) := by
      unfold F
      rw [List.append_assoc, List.take_append,
        List.take_of_length_le (by simp; omega)]
      simp only [List.length_cons, List.length_nil]
      rw [List.take_append_of_le_length hp]
    rw [he, List.count_append, powerPrefix m (i-2) (by omega) a]
    omega
  let dx : ℕ → ℤ := fun r =>
    [-1, -1, -1, 0, 1, 0, -1, -2, -3, -4, -3, -2, -1, -1, -1].getD r 0
  let dy : ℕ → ℤ := fun r =>
    [0, 1, 2, 2, 2, 1, 0, -1, -2, -3, -3, -3, -3, -2, -1].getD r 0
  have excursion (r : ℕ) (hr : r < 15) :
      (((A.take r).count 0 : ℤ) - ((A.take r).count 2 : ℤ) - 1 = dx r) ∧
      (((A.take r).count 1 : ℤ) - ((A.take r).count 2 : ℤ) = dy r) := by
    interval_cases r <;>
      norm_num [A, dx, dy, List.count_cons, List.count_nil, Fin.ext_iff]
  have difference (i : ℕ) (hi : 2 ≤ i) (hi' : i < 15*m+3) :
      ((((F m).take i).count 0 : ℤ) - (((F m).take i).count 2 : ℤ) = dx ((i-2)%15)) ∧
      ((((F m).take i).count 1 : ℤ) - (((F m).take i).count 2 : ℤ) = dy ((i-2)%15)) := by
    obtain ⟨hx, hy⟩ := excursion ((i-2)%15) (Nat.mod_lt _ (by decide))
    simp only [prefixCounts i hi hi']
    norm_num [List.count_cons, List.count_nil, Fin.ext_iff]
    constructor <;> linarith
  have chord (i j : ℕ) (hi : i < 15) (hj : j < 15) (R S : ℤ)
      (hR : 0 < R) (hS : 0 < S)
      (hx : S*dx i + R*dx j = 0) (hy : S*dy i + R*dy j = 0) :
      R = S ∧ ((i = 4 ∧ j = 13) ∨ (i = 13 ∧ j = 4)) := by
    clear difference excursion prefixCounts total lengthF powerPrefix countA powerLength m
    interval_cases i <;> interval_cases j <;> norm_num [dx, dy] at hx hy ⊢ <;> omega
  intro hb
  obtain ⟨r, s, hr, hr', hs, hs', _, _, heq⟩ := hb
  rw [lengthF] at hr' hs' heq
  have lr : ((F m).take r).length = r := by simp [List.length_take, lengthF]; omega
  have ls : ((F m).drop (15*m+3-s)).length = s := by
    simp [List.length_drop, lengthF]; omega
  simp only [lr, ls, letterCount] at heq
  let t := 15*m+3-s
  have ht : t < 15*m+3 := by dsimp [t]; omega
  have hts : t+s = 15*m+3 := by dsimp [t]; omega
  have partition (a : Fin 3) :
      (((F m).take t).count a : ℤ) + (((F m).drop t).count a : ℤ) = 5*m+1 := by
    have h := congrArg (List.count a) (List.take_append_drop t (F m))
    rw [List.count_append, total] at h
    exact_mod_cast h
  have equations (a : Fin 3) :
      (s : ℤ) * ((((F m).take r).count a : ℤ) - (((F m).take r).count 2 : ℤ)) +
      (r : ℤ) * ((((F m).take t).count a : ℤ) - (((F m).take t).count 2 : ℤ)) = 0 := by
    have eqa : (s : ℤ) * (((F m).take r).count a : ℤ) =
        (r : ℤ) * (((F m).drop t).count a : ℤ) := by exact_mod_cast heq a
    have eq2 : (s : ℤ) * (((F m).take r).count 2 : ℤ) =
        (r : ℤ) * (((F m).drop t).count 2 : ℤ) := by exact_mod_cast heq 2
    have pa := partition a
    have p2 := partition 2
    linear_combination eqa - eq2 + (r : ℤ)*pa - (r : ℤ)*p2
  have e0 := equations 0
  have e1 := equations 1
  by_cases hr1 : r = 1
  · subst r
    have hfirst : (F m).take 1 = [1] := by simp [F]
    rw [hfirst] at e0 e1
    by_cases ht0 : t = 0
    · simp [ht0, Fin.ext_iff] at e1
      omega
    · by_cases ht1 : t = 1
      · rw [ht1, hfirst] at e1
        norm_num [List.count_cons, List.count_nil, Fin.ext_iff] at e1
        omega
      · obtain ⟨hd0, hd1⟩ := difference t (by omega) ht
        rw [hd0] at e0
        rw [hd1] at e1
        generalize htt : (t-2)%15 = tt at e0 e1
        have httlt : tt < 15 := by
          have := Nat.mod_lt (t-2) (by decide : 0 < 15)
          omega
        interval_cases tt <;>
          norm_num [List.count_cons, List.count_nil, Fin.ext_iff, dx, dy] at e0 <;>
          norm_num [List.count_cons, List.count_nil, Fin.ext_iff, dx, dy] at e1 <;>
          omega
  · obtain ⟨hd0, hd1⟩ := difference r (by omega) hr'
    rw [hd0] at e0
    rw [hd1] at e1
    by_cases ht0 : t = 0
    · simp only [ht0, List.take_zero, List.count_nil, Int.natCast_zero, sub_self,
        mul_zero, add_zero] at e0 e1
      generalize hrr : (r-2)%15 = rr at e0 e1
      have hrrlt : rr < 15 := by
        have := Nat.mod_lt (r-2) (by decide : 0 < 15)
        omega
      interval_cases rr <;> norm_num [dx, dy] at e0 <;>
        norm_num [dx, dy] at e1 <;> omega
    · by_cases ht1 : t = 1
      · have hfirst : (F m).take t = [1] := by simp [ht1, F]
        rw [hfirst] at e0 e1
        generalize hrr : (r-2)%15 = rr at e0 e1
        have hrrlt : rr < 15 := by
          have := Nat.mod_lt (r-2) (by decide : 0 < 15)
          omega
        interval_cases rr <;>
          norm_num [dx, dy, List.count_cons, List.count_nil, Fin.ext_iff] at e0 <;>
          norm_num [dx, dy, List.count_cons, List.count_nil, Fin.ext_iff] at e1 <;>
          omega
      · obtain ⟨htd0, htd1⟩ := difference t (by omega) ht
        rw [htd0] at e0
        rw [htd1] at e1
        have hc := chord ((r-2)%15) ((t-2)%15)
          (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) r s
          (by omega) (by omega) e0 e1
        rcases hc with ⟨he, hpair | hpair⟩ <;> omega


/-- Square gaps realize unboundedly many distinct unbordered factors. -/
theorem infinitely_many_unbordered :
    ¬ {u : List (Fin 3) | (∃ i n, u = factor word i n) ∧
      u ≠ [] ∧ ¬ WeakAbelianBordered u}.Finite := by
  classical
  have occurs (q : ℕ) : ∃ i, factor word i (15*(2*q)+3) = F (2*q) := by
    classical
    obtain ⟨prefixFormula, _, _⟩ := word_structure
    have isSq (a : ℕ) : IsSquare (a^2) := ⟨a, by ring⟩
    have between (j : ℕ) (hj : q^2 < j) (hj' : j < (q+1)^2) : ¬ IsSquare j := by
      intro h
      obtain ⟨r, hr⟩ := IsSquare.exists_sq j h
      have hlo : q < r := by nlinarith
      have hhi : r < q+1 := by nlinarith
      omega
    have run : ∀ d, d ≤ 2*q → initial (q^2+1+d) =
        initial (q^2) ++ B ++ (List.replicate d A).flatten := by
      intro d
      induction d with
      | zero => simp [initial, block, isSq]
      | succ d ih =>
        intro hd
        have hns : ¬ IsSquare (q^2+1+d) := between _ (by omega) (by nlinarith)
        rw [show q^2+1+(d+1) = (q^2+1+d)+1 by omega, initial, ih (by omega)]
        simp [block, hns, List.replicate_add, List.flatten_append, List.append_assoc]
    have hnext : q^2+1+2*q = (q+1)^2 := by ring
    have he := run (2*q) (le_refl _)
    rw [hnext] at he
    have hb : block ((q+1)^2) = B := by simp [block, isSq]
    have hpre : factor word 0 ((initial ((q+1)^2)).length+1) =
        initial (q^2) ++ B ++ (List.replicate (2*q) A).flatten ++ [0] := by
      rw [prefixFormula ((q+1)^2) 1 (by rw [hb]; decide), hb, he]
      simp [B]
    have lengthPower : (List.replicate (2*q) A).flatten.length = 15*(2*q) := by
      simp [List.length_flatten, A, List.sum_replicate, Nat.mul_comm]
    have hlen := congrArg List.length he
    simp only [List.length_append] at hlen
    have lenB : B.length = 3 := rfl
    rw [lenB, lengthPower] at hlen
    have ht : (initial (q^2)).length + 1 + (15*(2*q)+3) =
        (initial ((q+1)^2)).length + 1 := by omega
    refine ⟨(initial (q^2)).length+1, ?_⟩
    have splitFactor (i n : ℕ) : factor word 0 (i+n) = factor word 0 i ++ factor word i n := by
      simp [factor, List.range_add, List.map_map, Function.comp_def]
    have hdrop := congrArg (fun l : List (Fin 3) => l.drop ((initial (q^2)).length+1))
      (splitFactor ((initial (q^2)).length+1) (15*(2*q)+3))
    have hleft : (factor word 0 ((initial (q^2)).length+1)).length =
        (initial (q^2)).length+1 := by simp [factor]
    rw [ht, hpre] at hdrop
    have hdr : (factor word 0 ((initial (q^2)).length+1) ++
        factor word ((initial (q^2)).length+1) (15*(2*q)+3)).drop
          ((initial (q^2)).length+1) = factor word ((initial (q^2)).length+1) (15*(2*q)+3) := by
      have hh := (List.drop_left
        (l₁ := factor word 0 ((initial (q^2)).length+1))
        (l₂ := factor word ((initial (q^2)).length+1) (15*(2*q)+3)))
      rw [hleft] at hh
      exact hh
    rw [hdr] at hdrop
    have hcanonical : initial (q^2) ++ B ++ (List.replicate (2*q) A).flatten ++ [0] =
        (initial (q^2) ++ [0]) ++ ([1, 2] ++ (List.replicate (2*q) A).flatten ++ [0]) := by
      simp [B, List.append_assoc]
    rw [hcanonical] at hdrop
    have hfirstlen : (initial (q^2) ++ [0]).length = (initial (q^2)).length+1 := by simp
    have hdc : ((initial (q^2) ++ [0]) ++
        ([1, 2] ++ (List.replicate (2*q) A).flatten ++ [0])).drop
          ((initial (q^2)).length+1) = [1, 2] ++ (List.replicate (2*q) A).flatten ++ [0] := by
      have hh := (List.drop_left (l₁ := initial (q^2) ++ [0])
        (l₂ := [1, 2] ++ (List.replicate (2*q) A).flatten ++ [0]))
      rw [hfirstlen] at hh
      exact hh
    rw [hdc] at hdrop
    simpa only [F] using hdrop.symm
  intro hf
  obtain ⟨N, hN⟩ := (hf.image List.length).bddAbove
  obtain ⟨i, hi⟩ := occurs (N+1)
  have hlen : (F (2*(N+1))).length = 15*(2*(N+1))+3 := by
    simp [F, List.length_flatten, A, List.sum_replicate, Nat.mul_comm]
  have hm : F (2*(N+1)) ∈ {u : List (Fin 3) | (∃ i n, u = factor word i n) ∧
      u ≠ [] ∧ ¬ WeakAbelianBordered u} := by
    refine ⟨⟨i, 15*(2*(N+1))+3, hi.symm⟩, ?_, unbordered _⟩
    exact List.ne_nil_of_length_pos (by rw [hlen]; omega)
  have hb := hN (Set.mem_image_of_mem List.length hm)
  rw [hlen] at hb
  omega

end D5.S1.Words.AbelianBorders.Counterexample
