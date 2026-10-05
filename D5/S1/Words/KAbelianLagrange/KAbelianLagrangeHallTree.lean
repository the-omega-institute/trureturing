/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeHallTree
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeHallTree
   mirror-E: none(waiver:concrete-four-digit-hall-tree)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The physical binary continued-fraction cylinders form a shrinking Hall tree. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeHallSplit
import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeHallBranches
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

set_option maxHeartbeats 800000 in
-- The endpoint geometry and finite-path inductions share one proof-local telescope.
/-- Finite path reconstruction makes the same continuant cylinder independent of the
chosen infinite extension. Its physical children retain the outer endpoints and cut
out the normalized pending gap; digit progress makes the widths shrink uniformly. -/
theorem hall_binary_interval_tree :
    ∃ U : HallTree,
      U.lo [] = (Real.sqrt 2 - 1) / 2 ∧
      U.hi [] = 2 * (Real.sqrt 2 - 1) ∧
      ∀ (b : ℕ → Bool) (n : ℕ) (g : GenContFract ℝ), g.h = 0 →
        (∀ i : ℕ, ∀ hi : i < (hallBinaryAddress b n).1.length,
          g.s.get? i = some ⟨1, (((hallBinaryAddress b n).1[i]).val + 1 : ℕ)⟩) →
        Set.Icc (U.lo ((List.ofFn (fun i : Fin n => b i)).reverse))
          (U.hi ((List.ofFn (fun i : Fin n => b i)).reverse)) =
          GenContFract.compExactValue (g.contsAux (hallBinaryAddress b n).1.length)
            (g.conts (hallBinaryAddress b n).1.length) ''
              Set.Icc ((Real.sqrt 2 - 1) / 2)
                (1 / (((hallBinaryAddress b n).2.val + 1 : ℕ) +
                  (Real.sqrt 2 - 1) / 2)) := by
  classical
  let m := (Real.sqrt 2 - 1) / 2
  let M := 2 * (Real.sqrt 2 - 1)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hs1 : 1 < Real.sqrt 2 := by nlinarith
  have hs3 : Real.sqrt 2 < 3 / 2 := by nlinarith
  have hm : 0 < m := by dsimp [m]; linarith
  have hM : 0 < M := by dsimp [M]; linarith
  have hmM : m < M := by dsimp [m, M]; linarith
  have hM1 : M < 1 := by dsimp [M]; linarith
  have hmrec : m = 1 / (4 + M) := by
    apply (eq_div_iff (by positivity : (4 : ℝ) + M ≠ 0)).mpr
    dsimp [m, M]
    nlinarith
  have hMrec : M = 1 / (1 + m) := by
    apply (eq_div_iff (by positivity : (1 : ℝ) + m ≠ 0)).mpr
    dsimp [m, M]
    nlinarith
  let hallGap (a s : ℝ) := 1 / (a + M + s) - 1 / (a + 1 + m + s)
  let hallCell (a s : ℝ) := 1 / (a + m + s) - 1 / (a + M + s)
  let d := 1 + m - M
  let f := M - m
  have hd : 0 < d := by dsimp [d, m, M]; linarith
  have hf : 0 < f := sub_pos.mpr hmM
  have hdf : d ≤ f := by dsimp [d, f, m, M]; nlinarith
  have hall_gap_formula (a s : ℝ) (ha : 1 ≤ a) (hs : 0 ≤ s) :
      hallGap a s = d / ((a + M + s) * (a + 1 + m + s)) ∧ 0 < hallGap a s := by
    have hx : 0 < a + M + s := by positivity
    have hy : 0 < a + 1 + m + s := by positivity
    have he : hallGap a s = d / ((a + M + s) * (a + 1 + m + s)) := by
      dsimp [hallGap, d]
      rw [div_sub_div _ _ hx.ne' hy.ne']
      congr 1
      ring
    exact ⟨he, he ▸ div_pos hd (mul_pos hx hy)⟩
  have hcellFormula (a s : ℝ) (ha : 1 ≤ a) (hs : 0 ≤ s) :
      hallCell a s = f / ((a + m + s) * (a + M + s)) := by
    dsimp [hallCell, f]
    rw [div_sub_div _ _ (by positivity) (by positivity)]
    congr 1
    ring
  have hall_gap_le_left_cell (a s : ℝ) (ha : 1 ≤ a) (hs : 0 ≤ s) :
      hallGap a s ≤ hallCell a s := by
    rw [(hall_gap_formula a s ha hs).1, hcellFormula a s ha hs]
    have hx : 0 < a + M + s := by positivity
    have hy : 0 < a + 1 + m + s := by positivity
    have hz : 0 < a + m + s := by positivity
    apply (div_le_div_iff₀ (mul_pos hx hy) (mul_pos hz hx)).2
    have hprod : d * (a + m + s) ≤ f * (a + 1 + m + s) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hdf) hz.le]
    nlinarith [hprod]
  have hall_gap_le_right_cell (a s : ℝ) (ha : 1 ≤ a) (hs : 0 ≤ s) :
      hallGap a s ≤ hallCell (a + 1) s := by
    rw [(hall_gap_formula a s ha hs).1, hcellFormula (a + 1) s (by linarith) hs]
    have hx : 0 < a + M + s := by positivity
    have hy : 0 < a + 1 + m + s := by positivity
    have hw : 0 < a + 1 + M + s := by positivity
    apply (div_le_div_iff₀ (mul_pos hx hy) (mul_pos hy hw)).2
    have hbase : d ≤ (f - d) * (2 * Real.sqrt 2 - 1) := by
      dsimp [d, f, m, M]
      nlinarith
    have hlow : 2 * Real.sqrt 2 - 1 ≤ a + M + s := by dsimp [M]; linarith
    have hmul := mul_le_mul_of_nonneg_left hlow (sub_nonneg.mpr hdf)
    have hred : d * (a + 1 + M + s) ≤ f * (a + M + s) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hred hy.le]
  let B (p : List Bool) (i : ℕ) := (p.reverse[i]?).getD false
  let A (p : List Bool) := hallBinaryAddress (B p) p.length
  let G (P : List (Fin 4)) : GenContFract ℝ :=
    ⟨0, Stream'.Seq.ofStream (fun i => ⟨1, (((P[i]?).getD 0).val + 1 : ℕ)⟩)⟩
  let T (P : List (Fin 4)) :=
    GenContFract.compExactValue ((G P).contsAux P.length) ((G P).conts P.length)
  let V (j : ℕ) : ℝ := 1 / ((j + 1 : ℕ) + m)
  let lo (p : List Bool) := min (T (A p).1 m) (T (A p).1 (V (A p).2.val))
  let hi (p : List Bool) := max (T (A p).1 m) (T (A p).1 (V (A p).2.val))
  have hget (P : List (Fin 4)) (i : ℕ) :
      (G P).s.get? i = some ⟨1, (((P[i]?).getD 0).val + 1 : ℕ)⟩ := rfl
  have hpositive (P : List (Fin 4)) (i : ℕ) :
      ∃ a : ℝ, 1 ≤ a ∧ (G P).s.get? i = some ⟨1, a⟩ := by
    refine ⟨(((P[i]?).getD 0).val + 1 : ℕ), ?_, rfl⟩
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hagree : ∀ n : ℕ, ∀ u v : ℕ → Bool,
      (∀ i < n, u i = v i) → hallBinaryAddress u n = hallBinaryAddress v n := by
    intro n
    induction n with
    | zero => intro u v _; rfl
    | succ n ih =>
        intro u v huv
        simp only [hallBinaryAddress, ih u v (fun i hi => huv i (by omega)),
          huv n (by omega)]
  have hB (p : List Bool) (c : Bool) (i : ℕ) (hi : i < p.length) :
      B (c :: p) i = B p i := by
    dsimp only [B]
    rw [List.reverse_cons, List.getElem?_append_left (by simpa using hi)]
  have hBnext (p : List Bool) (c : Bool) : B (c :: p) p.length = c := by
    simp [B, List.reverse_cons]
  have hnode (p : List Bool) (c : Bool) : A (c :: p) =
      if c = decide ((A p).1.length % 2 = 0) then
        ((A p).1 ++ [⟨(A p).2.val, by have := (A p).2.isLt; omega⟩], 0)
      else if h : (A p).2.val = 2 then ((A p).1 ++ [3], 0)
      else ((A p).1, ⟨(A p).2.val + 1, by have := (A p).2.isLt; omega⟩) := by
    have ha : hallBinaryAddress (B (c :: p)) p.length = A p :=
      hagree p.length _ _ (hB p c)
    simp only [A, List.length_cons, hallBinaryAddress, ha, hBnext]
  have hcont : ∀ (g h : GenContFract ℝ) (n : ℕ), g.h = h.h →
      (∀ i < n, g.s.get? i = h.s.get? i) →
      g.contsAux n = h.contsAux n ∧ g.conts n = h.conts n := by
    intro g h n hhead hd
    have hc : ∀ k ≤ n + 1, g.contsAux k = h.contsAux k := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
          intro hk
          rcases k with (_ | _ | k)
          · rfl
          · simp [GenContFract.contsAux, hhead]
          · have hgk := hd k (by omega)
            cases he : h.s.get? k with
            | none =>
                have hge : g.s.get? k = none := hgk.trans he
                rw [GenContFract.contsAux, GenContFract.contsAux, hge, he]
                exact ih (k + 1) (by omega) (by omega)
            | some v =>
                have hge : g.s.get? k = some v := hgk.trans he
                rw [GenContFract.contsAux_recurrence hge rfl rfl,
                  GenContFract.contsAux_recurrence he rfl rfl,
                  ih k (by omega) (by omega), ih (k + 1) (by omega) (by omega)]
    exact ⟨hc n (by omega), by
      simpa only [GenContFract.nth_cont_eq_succ_nth_contAux] using hc (n + 1) le_rfl⟩
  have hform (P : List (Fin 4)) (z : ℝ) : T P z =
      ((G P).nums P.length + ((G P).contsAux P.length).a * z) /
        ((G P).dens P.length + ((G P).contsAux P.length).b * z) := by
    by_cases hz : z = 0
    · simp [T, hz, GenContFract.compExactValue, GenContFract.num_eq_conts_a,
        GenContFract.den_eq_conts_b]
    · simp only [T, GenContFract.compExactValue, if_neg hz, GenContFract.nextConts,
        GenContFract.nextNum, GenContFract.nextDen, one_mul,
        GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b]
      rw [← mul_div_mul_right _ _ hz]
      congr 1 <;> field_simp [hz]
  have hq (P : List (Fin 4)) : 0 < (G P).dens P.length := by
    have hf : 0 < (Nat.fib (P.length + 1) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos P.length)
    exact hf.trans_le (prefix_geometry (G P) P.length
      (fun i _ => hpositive P i)).1
  have hp (P : List (Fin 4)) : 0 ≤ ((G P).contsAux P.length).b := by
    cases hn : P.length with
    | zero => simp [GenContFract.contsAux]
    | succ n =>
        have h := (prefix_geometry (G P) n (fun i _ => hpositive P i)).1
        have hf : 0 ≤ (Nat.fib (n + 1) : ℝ) := by positivity
        simpa only [hn, GenContFract.den_eq_conts_b,
          GenContFract.nth_cont_eq_succ_nth_contAux] using hf.trans h
  have hden (P : List (Fin 4)) (z : ℝ) (hz : 0 ≤ z) :
      0 < (G P).dens P.length + ((G P).contsAux P.length).b * z :=
    add_pos_of_pos_of_nonneg (hq P) (mul_nonneg (hp P) hz)
  have hdet (P : List (Fin 4)) :
      ((G P).contsAux P.length).a * (G P).dens P.length -
        (G P).nums P.length * ((G P).contsAux P.length).b = (-1 : ℝ) ^ P.length := by
    cases hn : P.length with
    | zero => simp [GenContFract.contsAux, GenContFract.zeroth_den_eq_one]
    | succ n =>
        have hprod : (∏ i ∈ Finset.range (n + 1), -((G P).partNums.get? i).getD 0) =
            (-1 : ℝ) ^ (n + 1) := by
          calc
            _ = ∏ _i ∈ Finset.range (n + 1), (-1 : ℝ) := by
              apply Finset.prod_congr rfl
              intro i _
              rw [GenContFract.partNum_eq_s_a (hget P i)]
              rfl
            _ = _ := by simp
        have hd := (G P).determinant (n := n)
        rw [hprod] at hd
        simpa only [hn, GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b,
          GenContFract.nth_cont_eq_succ_nth_contAux, mul_comm] using hd
  have hdiff (P : List (Fin 4)) (z w : ℝ) (hz : 0 ≤ z) (hw : 0 ≤ w) :
      T P z - T P w = (-1 : ℝ) ^ P.length * (z - w) /
        (((G P).dens P.length + ((G P).contsAux P.length).b * z) *
          ((G P).dens P.length + ((G P).contsAux P.length).b * w)) := by
    rw [hform, hform, div_sub_div _ _ (ne_of_gt (hden P z hz))
      (ne_of_gt (hden P w hw)), ← hdet P]
    congr 1
    ring
  have horient (P : List (Fin 4)) :
      (P.length % 2 = 0 → StrictMonoOn (T P) (Set.Ici 0)) ∧
      (P.length % 2 ≠ 0 → StrictAntiOn (T P) (Set.Ici 0)) := by
    have hsign : (-1 : ℝ) ^ P.length = if P.length % 2 = 0 then 1 else -1 := by
      rw [neg_one_pow_eq_pow_mod_two]
      split_ifs with h
      · simp [h]
      · have hmod : P.length % 2 = 1 := by omega
        simp [hmod]
    constructor
    · intro he z hz w hw hzw
      have hd := hdiff P w z hw hz
      rw [hsign, if_pos he, one_mul] at hd
      have hpos := div_pos (sub_pos.mpr hzw) (mul_pos (hden P w hw) (hden P z hz))
      linarith
    · intro he z hz w hw hzw
      have hd := hdiff P z w hz hw
      rw [hsign, if_neg he] at hd
      have hpos : 0 < (-1 : ℝ) * (z - w) := by linarith
      have hpos' := div_pos hpos (mul_pos (hden P z hz) (hden P w hw))
      linarith
  have hV (j : ℕ) (hj : j < 3) : m < V j ∧ V j ≤ M := by
    have ha : (1 : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    have hb : ((j + 1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : j + 1 ≤ 3)
    constructor
    · rw [hmrec]
      exact (one_div_lt_one_div_of_lt (by positivity)
        (by linarith : ((j + 1 : ℕ) : ℝ) + m < 4 + M))
    · rw [hMrec]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have himage (P : List (Fin 4)) (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) :
      T P '' Set.Icc u v = Set.Icc (min (T P u) (T P v)) (max (T P u) (T P v)) := by
    have hc : ContinuousOn (T P) (Set.Icc u v) := by
      have h : ContinuousOn (fun z : ℝ =>
          ((G P).nums P.length + ((G P).contsAux P.length).a * z) /
            ((G P).dens P.length + ((G P).contsAux P.length).b * z)) (Set.Icc u v) :=
        (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).div
        (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
        (fun z (hz : z ∈ Set.Icc u v) => ne_of_gt (hden P z (hu.trans hz.1)))
      exact h.congr (fun z _ => hform P z)
    by_cases he : P.length % 2 = 0
    · have hmono := (horient P).1 he
      have hle : T P u ≤ T P v := hmono.monotoneOn hu (hu.trans huv) huv
      rw [min_eq_left hle, max_eq_right hle]
      exact hc.image_Icc_of_monotoneOn huv (hmono.monotoneOn.mono
        (fun z hz => hu.trans hz.1))
    · have hanti := (horient P).2 he
      have hle : T P v ≤ T P u := hanti.antitoneOn hu (hu.trans huv) huv
      rw [min_eq_right hle, max_eq_left hle]
      exact hc.image_Icc_of_antitoneOn huv (hanti.antitoneOn.mono
        (fun z hz => hu.trans hz.1))
  have happend (P : List (Fin 4)) (a : Fin 4) (z : ℝ) (hz : 0 ≤ z) :
      T (P ++ [a]) z = T P (1 / ((a.val + 1 : ℕ) + z)) := by
    have hprefix : ∀ i < P.length, (G (P ++ [a])).s.get? i = (G P).s.get? i := by
      intro i hi
      simp [hget, List.getElem?_append_left hi]
    obtain ⟨hprev, hcurrent⟩ := hcont (G (P ++ [a])) (G P) P.length rfl hprefix
    have hg : (G (P ++ [a])).s.get? P.length = some ⟨1, (a.val + 1 : ℕ)⟩ := by
      simp [hget]
    have hdigit : (0 : ℝ) < (a.val + 1 : ℕ) := by positivity
    have haz : 0 < (a.val + 1 : ℕ) + z := by positivity
    have hd := hden P (1 / ((a.val + 1 : ℕ) + z)) (one_div_pos.mpr haz).le
    have hn := hden (P ++ [a]) z hz
    rw [hform, hform]
    simp only [List.length_append, List.length_singleton, GenContFract.num_eq_conts_a,
      GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux] at hn ⊢
    rw [GenContFract.contsAux_recurrence hg rfl rfl, hprev,
      ← GenContFract.nth_cont_eq_succ_nth_contAux, hcurrent] at hn ⊢
    simp only [one_mul] at hn ⊢
    apply (div_eq_div_iff (ne_of_gt hn) (ne_of_gt hd)).2
    field_simp [ne_of_gt haz]
    simp only [GenContFract.den_eq_conts_b,
      GenContFract.nth_cont_eq_succ_nth_contAux]
    ring
  have hV0 : V 0 = M := by simpa [V] using hMrec.symm
  have hcommit (P : List (Fin 4)) (a : Fin 4) :
      min (T (P ++ [a]) m) (T (P ++ [a]) (V 0)) =
        min (T P (1 / ((a.val + 1 : ℕ) + M))) (T P (1 / ((a.val + 1 : ℕ) + m))) ∧
      max (T (P ++ [a]) m) (T (P ++ [a]) (V 0)) =
        max (T P (1 / ((a.val + 1 : ℕ) + M))) (T P (1 / ((a.val + 1 : ℕ) + m))) := by
    rw [hV0, happend P a m hm.le, happend P a M hM.le]
    exact ⟨min_comm _ _, max_comm _ _⟩
  have hcut (p : List Bool) :
      lo (false :: p) = lo p ∧ hi (true :: p) = hi p ∧
      hi (false :: p) =
        (if (A p).1.length % 2 = 0 then T (A p).1 (V ((A p).2.val + 1))
          else T (A p).1 (1 / (((A p).2.val + 1 : ℕ) + M))) ∧
      lo (true :: p) =
        (if (A p).1.length % 2 = 0 then
          T (A p).1 (1 / (((A p).2.val + 1 : ℕ) + M))
          else T (A p).1 (V ((A p).2.val + 1))) := by
    let P := (A p).1
    let j := (A p).2.val
    let u := V j
    let v := V (j + 1)
    let w := 1 / ((j + 1 : ℕ) + M)
    have hj : j < 3 := (A p).2.isLt
    have ha : (1 : ℝ) ≤ (j + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    have hw0 : 0 < w := by dsimp [w]; positivity
    have hv0 : 0 < v := by dsimp [v, V]; positivity
    have hmv : m ≤ v := by
      rw [hmrec]
      dsimp [v, V]
      apply one_div_le_one_div_of_le (by positivity)
      have hj4 : ((j + 1 + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (by omega : j + 2 ≤ 4)
      linarith
    have hvw : v < w := by
      dsimp [v, w, V]
      apply one_div_lt_one_div_of_lt (by positivity)
      push_cast
      dsimp [m, M]
      linarith
    have hwu : w ≤ u := by
      dsimp [w, u, V]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have hc := hcommit P ⟨j, by omega⟩
    have hr :
        (min (T P m) (T P v), max (T P m) (T P v)) =
          if h : j = 2 then
            (min (T (P ++ [3]) m) (T (P ++ [3]) (V 0)),
              max (T (P ++ [3]) m) (T (P ++ [3]) (V 0)))
          else (min (T P m) (T P (V (j + 1))),
            max (T P m) (T P (V (j + 1)))) := by
      split_ifs with hj2
      · have hc4 := hcommit P 3
        rw [hc4.1, hc4.2]
        change (min (T P m) (T P v), max (T P m) (T P v)) =
          (min (T P (1 / (4 + M))) (T P (1 / (4 + m))),
            max (T P (1 / (4 + M))) (T P (1 / (4 + m))))
        rw [← hmrec]
        simp [v, V, hj2]
      · rfl
    by_cases he : P.length % 2 = 0
    · have hmono := (horient P).1 he
      have h₀ := hmono.monotoneOn hm.le (hm.le.trans hmv) hmv
      have h₂ := hmono.monotoneOn hw0.le (hw0.le.trans hwu) hwu
      have h₃ := hmono.monotoneOn hm.le (hm.le.trans (hV j hj).1.le) (hV j hj).1.le
      have hf : A (false :: p) = if h : j = 2 then (P ++ [3], 0)
          else (P, ⟨j + 1, by omega⟩) := by simp [hnode, P, j, he]
      have ht : A (true :: p) = (P ++ [⟨j, by omega⟩], 0) := by
        simp [hnode, P, j, he]
      have hfl : lo (false :: p) = T P m := by
        dsimp only [lo]
        rw [hf]
        split_ifs with hj2 <;> dsimp only [Prod.fst, Prod.snd, Fin.val_zero]
        · have heq := congrArg Prod.fst hr
          simp only [dif_pos hj2] at heq
          rw [← heq]
          exact min_eq_left h₀
        · exact min_eq_left h₀
      have hfh : hi (false :: p) = T P v := by
        dsimp only [hi]
        rw [hf]
        split_ifs with hj2 <;> dsimp only [Prod.fst, Prod.snd, Fin.val_zero]
        · have heq := congrArg Prod.snd hr
          simp only [dif_pos hj2] at heq
          rw [← heq]
          exact max_eq_right h₀
        · exact max_eq_right h₀
      have htl : lo (true :: p) = T P w := by
        dsimp only [lo]
        rw [ht]
        dsimp only [Prod.fst, Prod.snd, Fin.val_zero]
        rw [hc.1]
        exact min_eq_left h₂
      have hth : hi (true :: p) = T P u := by
        dsimp only [hi]
        rw [ht]
        dsimp only [Prod.fst, Prod.snd, Fin.val_zero]
        rw [hc.2]
        exact max_eq_right h₂
      exact ⟨hfl.trans (min_eq_left h₃).symm, hth.trans (max_eq_right h₃).symm,
        by simpa only [P, j, v, if_pos he] using hfh,
        by simpa only [P, j, w, if_pos he] using htl⟩
    · have hanti := (horient P).2 he
      have h₀ := hanti.antitoneOn hm.le (hm.le.trans hmv) hmv
      have h₂ := hanti.antitoneOn hw0.le (hw0.le.trans hwu) hwu
      have h₃ := hanti.antitoneOn hm.le (hm.le.trans (hV j hj).1.le) (hV j hj).1.le
      have hf : A (false :: p) = (P ++ [⟨j, by omega⟩], 0) := by
        simp [hnode, P, j, he]
      have ht : A (true :: p) = if h : j = 2 then (P ++ [3], 0)
          else (P, ⟨j + 1, by omega⟩) := by simp [hnode, P, j, he]
      have hfl : lo (false :: p) = T P u := by
        dsimp only [lo]
        rw [hf]
        dsimp only [Prod.fst, Prod.snd, Fin.val_zero]
        rw [hc.1]
        exact min_eq_right h₂
      have hfh : hi (false :: p) = T P w := by
        dsimp only [hi]
        rw [hf]
        dsimp only [Prod.fst, Prod.snd, Fin.val_zero]
        rw [hc.2]
        exact max_eq_left h₂
      have htl : lo (true :: p) = T P v := by
        dsimp only [lo]
        rw [ht]
        split_ifs with hj2 <;> dsimp only [Prod.fst, Prod.snd, Fin.val_zero]
        · have heq := congrArg Prod.fst hr
          simp only [dif_pos hj2] at heq
          rw [← heq]
          exact min_eq_right h₀
        · exact min_eq_right h₀
      have hth : hi (true :: p) = T P m := by
        dsimp only [hi]
        rw [ht]
        split_ifs with hj2 <;> dsimp only [Prod.fst, Prod.snd, Fin.val_zero]
        · have heq := congrArg Prod.snd hr
          simp only [dif_pos hj2] at heq
          rw [← heq]
          exact max_eq_left h₀
        · exact max_eq_left h₀
      exact ⟨hfl.trans (min_eq_right h₃).symm, hth.trans (max_eq_left h₃).symm,
        by simpa only [P, j, w, if_neg he] using hfh,
        by simpa only [P, j, v, if_neg he] using htl⟩
  have hinvlen (P : List (Fin 4)) (r t : ℝ) (hr : 0 < r) (ht : 0 < t) :
      |T P (1 / r) - T P (1 / t)| =
        |t - r| / (((r + ((G P).contsAux P.length).b / (G P).dens P.length) *
          (t + ((G P).contsAux P.length).b / (G P).dens P.length)) *
            (G P).dens P.length ^ 2) := by
    rw [hdiff P _ _ (one_div_pos.mpr hr).le (one_div_pos.mpr ht).le,
      abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (mul_pos (hden P _ (one_div_pos.mpr hr).le)
        (hden P _ (one_div_pos.mpr ht).le)),
      div_sub_div _ _ (ne_of_gt hr) (ne_of_gt ht)]
    simp only [one_mul, abs_div, abs_of_pos (mul_pos hr ht)]
    field_simp [ne_of_gt (hq P)]
  have hgap (p : List Bool) : lo (true :: p) - hi (false :: p) =
      hallGap ((A p).2.val + 1 : ℕ)
        (((G (A p).1).contsAux (A p).1.length).b / (G (A p).1).dens (A p).1.length) /
          (G (A p).1).dens (A p).1.length ^ 2 := by
    let P := (A p).1
    let a : ℝ := ((A p).2.val + 1 : ℕ)
    let s := ((G P).contsAux P.length).b / (G P).dens P.length
    have ha : 1 ≤ a := by
      dsimp [a]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le (A p).2.val)
    have hsw : 0 ≤ s := div_nonneg (hp P) (hq P).le
    have hvw : 1 / (a + 1 + m) < 1 / (a + M) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      dsimp [m, M]
      linarith
    have heq : lo (true :: p) - hi (false :: p) =
        |T P (1 / (a + M)) - T P (1 / (a + 1 + m))| := by
      have hVeq : V ((A p).2.val + 1) = 1 / (a + 1 + m) := by
        dsimp [V, a]; push_cast; congr 2
      rw [(hcut p).2.2.1, (hcut p).2.2.2, hVeq]
      change (if P.length % 2 = 0 then T P (1 / (a + M))
        else T P (1 / (a + 1 + m))) -
        (if P.length % 2 = 0 then T P (1 / (a + 1 + m))
          else T P (1 / (a + M))) = _
      have hv0 : 0 ≤ 1 / (a + 1 + m) := by positivity
      have hw0 : 0 ≤ 1 / (a + M) := by positivity
      by_cases he : P.length % 2 = 0
      · have ho := (horient P).1 he hv0 hw0 hvw
        simp only [if_pos he]
        exact (abs_of_pos (sub_pos.mpr ho)).symm
      · have ho := (horient P).2 he hv0 hw0 hvw
        simp only [if_neg he]
        rw [abs_of_neg (sub_neg.mpr ho), neg_sub]
    rw [heq, hinvlen P (a + M) (a + 1 + m) (by positivity) (by positivity),
      (hall_gap_formula a s ha hsw).1]
    have hd : 0 < 1 + m - M := by dsimp [m, M]; linarith
    change |a + 1 + m - (a + M)| / (((a + M + s) * (a + 1 + m + s)) * _) = _
    rw [show a + 1 + m - (a + M) = 1 + m - M by ring, abs_of_pos hd]
    exact (div_div _ _ _).symm
  have hsize (p : List Bool) (c : Bool) :
      lo (true :: p) - hi (false :: p) ≤ hi (c :: p) - lo (c :: p) := by
    let P := (A p).1
    let j := (A p).2.val
    let a : ℝ := (j + 1 : ℕ)
    let s := ((G P).contsAux P.length).b / (G P).dens P.length
    let u := V j
    let v := V (j + 1)
    let w := 1 / (a + M)
    let e := 1 / (a + 1 + M)
    have ha : 1 ≤ a := by
      dsimp [a]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    have hj : j < 3 := (A p).2.isLt
    have ha4 : a + 1 ≤ 4 := by dsimp [a]; push_cast; exact_mod_cast (by omega : j + 2 ≤ 4)
    have hs : 0 ≤ s := div_nonneg (hp P) (hq P).le
    have hme : m ≤ e := by
      rw [hmrec]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have hev : e ≤ v := by
      dsimp [e, v, V, a]
      push_cast
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have hv0 : 0 ≤ v := by dsimp [v, V]; positivity
    have hw0 : 0 ≤ w := by dsimp [w]; positivity
    have hwu : w ≤ u := by
      dsimp [w, u, V, a]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have hcell (r : ℝ) (hr : 1 ≤ r) :
        |T P (1 / (r + m)) - T P (1 / (r + M))| =
          hallCell r s / (G P).dens P.length ^ 2 := by
      rw [hinvlen P (r + m) (r + M) (by positivity) (by positivity)]
      have hd : 0 < M - m := sub_pos.mpr hmM
      rw [show r + M - (r + m) = M - m by ring, abs_of_pos hd]
      dsimp only [hallCell]
      change (M - m) / (((r + m + s) * (r + M + s)) * _) =
        (1 / (r + m + s) - 1 / (r + M + s)) / _
      rw [div_sub_div _ _ (by positivity) (by positivity), div_div]
      congr 1
      ring
    have hsmallDigit : hallGap a s / (G P).dens P.length ^ 2 ≤ |T P u - T P w| := by
      have h := div_le_div_of_nonneg_right (hall_gap_le_left_cell a s ha hs)
        (sq_nonneg ((G P).dens P.length))
      simpa only [hcell a ha, u, w, V, a] using h
    have hsmallRest : hallGap a s / (G P).dens P.length ^ 2 ≤ |T P v - T P m| := by
      have h := div_le_div_of_nonneg_right (hall_gap_le_right_cell a s ha hs)
        (sq_nonneg ((G P).dens P.length))
      have heq : |T P v - T P e| = hallCell (a + 1) s / (G P).dens P.length ^ 2 := by
        have hv : v = 1 / (a + 1 + m) := by
          dsimp [v, V, a]; push_cast; congr 2
        rw [hv]
        exact hcell (a + 1) (by linarith)
      rw [← heq] at h
      apply h.trans
      by_cases he : P.length % 2 = 0
      · have ho := (horient P).1 he
        have h₀ := ho.monotoneOn hm.le (hm.le.trans hme) hme
        have h₁ := ho.monotoneOn (hm.le.trans hme) hv0 hev
        rw [abs_of_nonneg (sub_nonneg.mpr h₁),
          abs_of_nonneg (sub_nonneg.mpr (h₀.trans h₁))]
        linarith
      · have ho := (horient P).2 he
        have h₀ := ho.antitoneOn hm.le (hm.le.trans hme) hme
        have h₁ := ho.antitoneOn (hm.le.trans hme) hv0 hev
        rw [abs_of_nonpos (sub_nonpos.mpr h₁),
          abs_of_nonpos (sub_nonpos.mpr (h₁.trans h₀))]
        linarith
    rw [hgap p]
    change hallGap a s / (G P).dens P.length ^ 2 ≤ _
    have hc := hcut p
    by_cases he : P.length % 2 = 0
    · have ho := (horient P).1 he
      have h₀ := ho.monotoneOn hm.le (hm.le.trans (hV j hj).1.le) (hV j hj).1.le
      have h₁ := ho.monotoneOn hw0 (hw0.trans hwu) hwu
      have hmv : m ≤ v := hme.trans hev
      have h₂ := ho.monotoneOn hm.le (hm.le.trans hmv) hmv
      cases c
      · rw [hc.1, hc.2.2.1]
        change _ ≤ (if P.length % 2 = 0 then T P v else T P w) - _
        rw [if_pos he]
        change _ ≤ T P v - min (T P m) (T P u)
        rw [min_eq_left h₀]
        simpa only [abs_of_nonneg (sub_nonneg.mpr h₂)] using hsmallRest
      · rw [hc.2.1, hc.2.2.2]
        change _ ≤ _ - (if P.length % 2 = 0 then T P w else T P v)
        rw [if_pos he]
        change _ ≤ max (T P m) (T P u) - T P w
        rw [max_eq_right h₀]
        simpa only [abs_of_nonneg (sub_nonneg.mpr h₁)] using hsmallDigit
    · have ho := (horient P).2 he
      have h₀ := ho.antitoneOn hm.le (hm.le.trans (hV j hj).1.le) (hV j hj).1.le
      have h₁' := ho.antitoneOn hw0 (hw0.trans hwu) hwu
      have hmv : m ≤ v := hme.trans hev
      have h₂' := ho.antitoneOn hm.le (hm.le.trans hmv) hmv
      cases c
      · rw [hc.1, hc.2.2.1]
        change _ ≤ (if P.length % 2 = 0 then T P v else T P w) - _
        rw [if_neg he]
        change _ ≤ T P w - min (T P m) (T P u)
        rw [min_eq_right h₀]
        simpa only [abs_of_nonpos (sub_nonpos.mpr h₁'), neg_sub] using hsmallDigit
      · rw [hc.2.1, hc.2.2.2]
        change _ ≤ _ - (if P.length % 2 = 0 then T P w else T P v)
        rw [if_neg he]
        change _ ≤ max (T P m) (T P u) - T P v
        rw [max_eq_left h₀]
        simpa only [abs_of_nonpos (sub_nonpos.mpr h₂'), neg_sub] using hsmallRest
  have hcanon (p : List Bool) (g : GenContFract ℝ) (hh : g.h = 0)
      (hd : ∀ i : ℕ, ∀ hi : i < (A p).1.length,
        g.s.get? i = some ⟨1, (((A p).1[i]).val + 1 : ℕ)⟩) :
      g.contsAux (A p).1.length = (G (A p).1).contsAux (A p).1.length ∧
      g.conts (A p).1.length = (G (A p).1).conts (A p).1.length := by
    apply hcont g (G (A p).1) _ hh
    intro i hi
    rw [hd i hi, hget, List.getElem?_eq_getElem hi, Option.getD_some]
  have hpositiveGap (p : List Bool) : 0 < lo (true :: p) - hi (false :: p) := by
    rw [hgap p]
    exact div_pos (hall_gap_formula _ _
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (A p).2.val))
      (div_nonneg (hp _) (hq _).le)).2 (sq_pos_of_pos (hq _))
  have hordered (p : List Bool) : lo p ≤ hi p := min_le_max
  have hinside (p : List Bool) (c : Bool) : lo p ≤ lo (c :: p) ∧ hi (c :: p) ≤ hi p := by
    have hc := hcut p
    have hg := (hpositiveGap p).le
    have hf := hordered (false :: p)
    have ht := hordered (true :: p)
    cases c <;> constructor <;> linarith [hc.1, hc.2.1]
  have hgapMono (p : List Bool) (c : Bool) :
      lo (true :: c :: p) - hi (false :: c :: p) ≤ lo (true :: p) - hi (false :: p) := by
    let P := (A p).1
    let a : ℝ := ((A p).2.val + 1 : ℕ)
    have ha : 1 ≤ a := by
      dsimp [a]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (A p).2.val)
    have hscaled (a q r : ℝ) (ha : 1 ≤ a) (hq : 0 < q) (hr : 0 ≤ r) :
        hallGap a (r / q) / q ^ 2 =
          d / (((a + M) * q + r) * ((a + 1 + m) * q + r)) := by
      rw [(hall_gap_formula a (r / q) ha (div_nonneg hr hq.le)).1]
      field_simp
    have hcommitGap (v : Fin 4) (hv : a ≤ (v.val + 1 : ℕ)) :
        hallGap 1 (((G (P ++ [v])).contsAux (P ++ [v]).length).b /
            (G (P ++ [v])).dens (P ++ [v]).length) /
          (G (P ++ [v])).dens (P ++ [v]).length ^ 2 ≤
        hallGap a (((G P).contsAux P.length).b / (G P).dens P.length) /
          (G P).dens P.length ^ 2 := by
      obtain ⟨hprev, hcur⟩ := hcont (G (P ++ [v])) (G P) P.length rfl (by
        intro i hi
        simp [hget, List.getElem?_append_left hi])
      have hgetv : (G (P ++ [v])).s.get? P.length = some ⟨1, (v.val + 1 : ℕ)⟩ := by
        simp [hget]
      have hrec : (G (P ++ [v])).dens (P ++ [v]).length =
          (v.val + 1 : ℕ) * (G P).dens P.length + ((G P).contsAux P.length).b := by
        simp only [List.length_append, List.length_singleton, GenContFract.den_eq_conts_b,
          GenContFract.nth_cont_eq_succ_nth_contAux]
        rw [GenContFract.contsAux_recurrence hgetv rfl rfl, hprev,
          ← GenContFract.nth_cont_eq_succ_nth_contAux, hcur]
        simp [GenContFract.nth_cont_eq_succ_nth_contAux]
      have hprev' : ((G (P ++ [v])).contsAux (P ++ [v]).length).b =
          (G P).dens P.length := by
        simp only [List.length_append, List.length_singleton,
          ← GenContFract.nth_cont_eq_succ_nth_contAux, hcur,
          GenContFract.den_eq_conts_b]
      let q := (G P).dens P.length
      let r := ((G P).contsAux P.length).b
      let v' : ℝ := (v.val + 1 : ℕ)
      have hq' : 0 < q := hq P
      have hr : 0 ≤ r := hp P
      have hv' : 1 ≤ v' := ha.trans hv
      have hQ : 0 < v' * q + r := by positivity
      rw [hprev', hrec, hscaled 1 _ _ (by norm_num) hQ hq'.le,
        hscaled a _ _ ha hq' hr]
      have hx : 0 < (a + M) * q + r := by positivity
      have hy : 0 < (a + 1 + m) * q + r := by positivity
      have hcx : (a + M) * q + r ≤ (1 + M) * (v' * q + r) + q := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hv) hq'.le,
          mul_nonneg (mul_nonneg hM.le (sub_nonneg.mpr hv')) hq'.le,
          mul_nonneg hM.le hr]
      have hcy : (a + 1 + m) * q + r ≤ (1 + 1 + m) * (v' * q + r) + q := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hv) hq'.le,
          mul_nonneg (mul_nonneg (by linarith : 0 ≤ 1 + m)
            (sub_nonneg.mpr hv')) hq'.le, mul_nonneg (by linarith : 0 ≤ 1 + m) hr]
      exact div_le_div_of_nonneg_left hd.le (mul_pos hx hy)
        (mul_le_mul hcx hcy hy.le (hx.le.trans hcx))
    rw [hgap, hgap, hnode]
    split
    · simpa only [P, a, Fin.val_zero, Nat.cast_zero, Nat.cast_one, zero_add] using
        hcommitGap ⟨(A p).2.val, by have := (A p).2.isLt; omega⟩ le_rfl
    · split
      · have hv : a ≤ (3 + 1 : ℕ) := by
          dsimp [a]; exact_mod_cast (by have := (A p).2.isLt; omega : (A p).2.val + 1 ≤ 4)
        simpa only [P, a, Fin.val_zero, Nat.cast_zero, Nat.cast_one, zero_add] using
          hcommitGap 3 hv
      · let s := ((G P).contsAux P.length).b / (G P).dens P.length
        have hs' : 0 ≤ s := div_nonneg (hp P) (hq P).le
        have hg : hallGap (a + 1) s ≤ hallGap a s := by
          rw [(hall_gap_formula (a + 1) s (by linarith) hs').1,
            (hall_gap_formula a s ha hs').1]
          have hx : 0 < a + M + s := by positivity
          have hy : 0 < a + 1 + m + s := by positivity
          exact div_le_div_of_nonneg_left hd.le (mul_pos hx hy)
            (mul_le_mul (by linarith) (by linarith) hy.le (by linarith))
        convert div_le_div_of_nonneg_right hg (sq_nonneg ((G P).dens P.length)) using 1
        all_goals first | rfl | (dsimp only [P, a, s]; push_cast; ring)
  have hshrink (ε : ℝ) (hε : 0 < ε) :
      ∃ N : ℕ, ∀ p : List Bool, N ≤ p.length → hi p - lo p < ε := by
    obtain ⟨D, hD⟩ := exists_nat_gt (1 / ε)
    refine ⟨3 * (D + 5), ?_⟩
    intro p hn
    let P := (A p).1
    let j := (A p).2.val
    obtain ⟨_, _, hd⟩ := hall_binary_branch_expansion (B p)
    have htime : p.length ≤ 3 * P.length + j := (hd p.length).1
    have hj : j < 3 := (A p).2.isLt
    have hlen : D + 5 ≤ P.length := by omega
    have hf := Nat.le_fib_self (n := P.length + 1) (by omega)
    have hDF : D < Nat.fib (P.length + 1) := (by omega : D < P.length + 1).trans_le hf
    have hF : 0 < (Nat.fib (P.length + 1) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos P.length)
    have hF1 : 1 ≤ (Nat.fib (P.length + 1) : ℝ) := by
      have := Nat.fib_pos.mpr (Nat.succ_pos P.length)
      exact_mod_cast this
    have hFε : 1 / ε < (Nat.fib (P.length + 1) : ℝ) :=
      hD.trans (by exact_mod_cast hDF)
    have hinv : 1 / (Nat.fib (P.length + 1) : ℝ) < ε :=
      (div_lt_iff₀ hF).mpr (by have := (div_lt_iff₀ hε).mp hFε; nlinarith)
    have hgeom := ((prefix_geometry (G P) P.length
      (fun i _ => hpositive P i)).2 m ⟨hm.le, hmM.le.trans hM1.le⟩
        (V j) ⟨hm.le.trans (hV j hj).1.le, (hV j hj).2.trans hM1.le⟩).2
    have hwidth : hi p - lo p = |T P m - T P (V j)| := by
      exact (max_sub_min_eq_abs (T P m) (T P (V j))).trans (abs_sub_comm _ _)
    rw [hwidth]
    exact hgeom.trans_lt ((one_div_le_one_div_of_le hF (by nlinarith :
      (Nat.fib (P.length + 1) : ℝ) ≤ (Nat.fib (P.length + 1) : ℝ) ^ 2)).trans_lt hinv)
  let U : HallTree :=
    { lo := lo, hi := hi, ordered := hordered,
      left := fun p => (hcut p).1, right := fun p => (hcut p).2.1,
      inside := hinside, gap_pos := hpositiveGap, child_size := hsize,
      gap_mono := hgapMono, shrink := hshrink }
  refine ⟨U, ?_, ?_, ?_⟩
  · have hT (z : ℝ) : T [] z = z := by
      rw [hform]
      simp only [List.length_nil, GenContFract.zeroth_num_eq_h,
        GenContFract.zeroth_den_eq_one, GenContFract.contsAux, G,
        zero_add, zero_mul, one_mul, add_zero, div_one]
    change min (T [] m) (T [] (V 0)) = m
    rw [hV0, hT, hT, min_eq_left hmM.le]
  · have hT (z : ℝ) : T [] z = z := by
      rw [hform]
      simp only [List.length_nil, GenContFract.zeroth_num_eq_h,
        GenContFract.zeroth_den_eq_one, GenContFract.contsAux, G,
        zero_add, zero_mul, one_mul, add_zero, div_one]
    change max (T [] m) (T [] (V 0)) = M
    rw [hV0, hT, hT, max_eq_right hmM.le]
  · intro b n g hh hd
    let p := (List.ofFn (fun i : Fin n => b i)).reverse
    have hpn : p.length = n := by simp [p]
    have hAp : A p = hallBinaryAddress b n := by
      dsimp only [A]
      rw [hpn]
      apply hagree n
      intro i hi
      simp [B, p, hi]
    have hdp : ∀ i : ℕ, ∀ hi : i < (A p).1.length,
        g.s.get? i = some ⟨1, (((A p).1[i]).val + 1 : ℕ)⟩ := by
      simpa only [hAp] using hd
    have hc := hcanon p g hh hdp
    change Set.Icc (lo p) (hi p) = _
    rw [← hAp]
    change Set.Icc (min (T (A p).1 m) (T (A p).1 (V (A p).2.val)))
      (max (T (A p).1 m) (T (A p).1 (V (A p).2.val))) = _
    rw [← himage (A p).1 m (V (A p).2.val) hm.le (hV _ (A p).2.isLt).1.le]
    simp only [T, hc.1, hc.2, V, m]

end D5.S1.Words.KAbelianLagrange
