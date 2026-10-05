/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeHallNested
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeHallNested
   mirror-E: none(waiver:binary-hall-cylinder-intersection)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Every binary Hall path has nested shrinking cylinders and a unique C4 survivor. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeHallBranches
import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeHallCylinders
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

/-- The pending digits have hull `[m, 1/(j+1+m)]`. A commitment pulls the full hull
back through its chosen digit, whereas a cursor increment trims the upper endpoint.
Induction projects arbitrary later full cylinders to earlier ones. Compact intersection
and finite-cylinder decoding then identify the unique survivor as a C4 point. -/
theorem hall_binary_nested_cylinders (b : ℕ → Bool) (g : GenContFract ℝ)
    (hh : g.h = 0)
    (hmatch : ∀ n i : ℕ, ∀ hi : i < (hallBinaryAddress b n).1.length,
      g.s.get? i = some ⟨1, (((hallBinaryAddress b n).1[i]).val + 1 : ℕ)⟩) :
    let m := (Real.sqrt 2 - 1) / 2
    let C (n : ℕ) :=
      GenContFract.compExactValue (g.contsAux (hallBinaryAddress b n).1.length)
        (g.conts (hallBinaryAddress b n).1.length) ''
          Set.Icc m (1 / (((hallBinaryAddress b n).2.val + 1 : ℕ) + m))
    Antitone C ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
        ∀ x ∈ C n, ∀ y ∈ C n, |x - y| < ε) ∧
      ∃! x : ℝ, (∀ n : ℕ, x ∈ C n) ∧ x ∈ hallCantor := by
  classical
  let P (n : ℕ) := (hallBinaryAddress b n).1
  let J (n : ℕ) := (hallBinaryAddress b n).2.val
  let m := (Real.sqrt 2 - 1) / 2
  let M := 2 * (Real.sqrt 2 - 1)
  let U (n : ℕ) := 1 / ((J n + 1 : ℕ) + m)
  let T (n : ℕ) := GenContFract.compExactValue (g.contsAux n) (g.conts n)
  let C (n : ℕ) := T (P n).length '' Set.Icc m (U n)
  change Antitone C ∧ _ ∧ ∃! x : ℝ, (∀ n : ℕ, x ∈ C n) ∧ x ∈ hallCantor
  obtain ⟨_, _, hbranch⟩ := hall_binary_branch_expansion b
  have htime (n : ℕ) : n ≤ 3 * (P n).length + J n := (hbranch n).1
  have hJ (n : ℕ) : J n < 3 := (hallBinaryAddress b n).2.isLt
  have hg (i : ℕ) : ∃ a : ℕ, 0 < a ∧ a ≤ 4 ∧
      g.s.get? i = some ⟨1, (a : ℝ)⟩ := by
    have ht := htime (3 * (i + 1))
    have hj := hJ (3 * (i + 1))
    have hi : i < (P (3 * (i + 1))).length := by omega
    refine ⟨((P (3 * (i + 1)))[i]).val + 1, Nat.succ_pos _, ?_, hmatch _ i hi⟩
    have := ((P (3 * (i + 1)))[i]).isLt
    omega
  have hreal (i : ℕ) : ∃ a : ℝ, 1 ≤ a ∧ g.s.get? i = some ⟨1, a⟩ := by
    obtain ⟨a, ha, _, hs⟩ := hg i
    exact ⟨a, by exact_mod_cast ha, hs⟩
  have hq (n : ℕ) : 0 < g.dens n := by
    have hf : 0 < (Nat.fib (n + 1) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos n)
    exact hf.trans_le (prefix_geometry g n (fun i _ => hreal i)).1
  have hp (n : ℕ) : 0 ≤ (g.contsAux n).b := by
    cases n with
    | zero => simp [GenContFract.contsAux]
    | succ n =>
        simpa only [GenContFract.den_eq_conts_b,
          GenContFract.nth_cont_eq_succ_nth_contAux] using (hq n).le
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hs1 : 1 < Real.sqrt 2 := by nlinarith
  have hs3 : Real.sqrt 2 < 3 / 2 := by nlinarith
  have hm : 0 < m := by dsimp [m]; linarith
  have hmM : m ≤ M := by dsimp [m, M]; linarith
  have hM1 : M < 1 := by dsimp [M]; linarith
  have hmrec : m = 1 / (4 + M) := by
    apply (eq_div_iff (by dsimp [M]; linarith : (4 : ℝ) + M ≠ 0)).mpr
    dsimp [m, M]
    nlinarith
  have hMrec : M = 1 / (1 + m) := by
    apply (eq_div_iff (by linarith : (1 : ℝ) + m ≠ 0)).mpr
    dsimp [m, M]
    nlinarith
  have hU (n : ℕ) : m ≤ U n ∧ U n ≤ M := by
    have hj : (J n + 1 : ℕ) ≤ 4 := by have := hJ n; omega
    have hjr : ((J n + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hj
    constructor
    · rw [hmrec]
      change 1 / (4 + M) ≤ 1 / (((J n + 1 : ℕ) : ℝ) + m)
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    · rw [hMrec]
      change 1 / (((J n + 1 : ℕ) : ℝ) + m) ≤ 1 / (1 + m)
      exact one_div_le_one_div_of_le (by linarith)
        (by have : (1 : ℝ) ≤ (J n + 1 : ℕ) := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le (J n))
            linarith)
  have hH : Set.Icc m M ⊆ Set.Icc (0 : ℝ) 1 := by
    intro z hz
    exact ⟨hm.le.trans hz.1, hz.2.trans hM1.le⟩
  have hform (n : ℕ) (z : ℝ) : T n z =
      (g.nums n + (g.contsAux n).a * z) /
        (g.dens n + (g.contsAux n).b * z) := by
    by_cases hz : z = 0
    · simp [T, hz, GenContFract.compExactValue, GenContFract.num_eq_conts_a,
        GenContFract.den_eq_conts_b]
    · simp only [T, GenContFract.compExactValue, if_neg hz, GenContFract.nextConts,
        GenContFract.nextNum, GenContFract.nextDen, one_mul,
        GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b]
      rw [← mul_div_mul_right _ _ hz]
      congr 1 <;> field_simp [hz]
  have hden (n : ℕ) (z : ℝ) (hz : 0 ≤ z) :
      0 < g.dens n + (g.contsAux n).b * z :=
    add_pos_of_pos_of_nonneg (hq n) (mul_nonneg (hp n) hz)
  have hstep (n a : ℕ) (ha : 0 < a) (hget : g.s.get? n = some ⟨1, (a : ℝ)⟩)
      (z : ℝ) (hz : z ∈ Set.Icc m M) : T (n + 1) z = T n (1 / ((a : ℝ) + z)) := by
    have har : (0 : ℝ) < a := by exact_mod_cast ha
    have haz : 0 < (a : ℝ) + z := by linarith [hz.1]
    have hd := hden n (1 / ((a : ℝ) + z)) (one_div_pos.mpr haz).le
    have hn := hden (n + 1) z ((hH hz).1)
    rw [hform, hform]
    simp only [GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b,
      GenContFract.nth_cont_eq_succ_nth_contAux] at hn hd ⊢
    rw [GenContFract.contsAux_recurrence hget rfl rfl] at hn ⊢
    simp only [one_mul] at hn ⊢
    apply (div_eq_div_iff (ne_of_gt hn) (ne_of_gt hd)).2
    field_simp [ne_of_gt haz]
    ring
  have hinverse (a : ℕ) (ha : 0 < a) (ha4 : a ≤ 4) (z : ℝ)
      (hz : z ∈ Set.Icc m M) : 1 / ((a : ℝ) + z) ∈ Set.Icc m M := by
    have har : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have har4 : (a : ℝ) ≤ 4 := by exact_mod_cast ha4
    constructor
    · rw [hmrec]
      exact one_div_le_one_div_of_le (by linarith [hz.1]) (by linarith [hz.2])
    · rw [hMrec]
      exact one_div_le_one_div_of_le (by linarith) (by linarith [hz.1])
  have hfull : ∀ d n : ℕ, T (n + d) '' Set.Icc m M ⊆ T n '' Set.Icc m M := by
    intro d
    induction d with
    | zero => intro n; simp
    | succ d ih =>
        intro n x hx
        obtain ⟨z, hz, rfl⟩ := hx
        obtain ⟨a, ha, ha4, hget⟩ := hg (n + d)
        rw [Nat.add_succ, hstep (n + d) a ha hget z hz]
        exact ih n ⟨1 / ((a : ℝ) + z), hinverse a ha ha4 z hz, rfl⟩
  have haddr (n : ℕ) :
      (∃ a : Fin 4, P (n + 1) = P n ++ [a] ∧ J (n + 1) = 0 ∧ J n ≤ a.val) ∨
      (P (n + 1) = P n ∧ J (n + 1) = J n + 1) := by
    dsimp only [P, J]
    rw [hallBinaryAddress]
    split
    · exact Or.inl ⟨_, rfl, rfl, le_rfl⟩
    · split
      · exact Or.inl ⟨3, rfl, rfl, by have := hJ n; omega⟩
      · exact Or.inr ⟨rfl, rfl⟩
  have hnested (n : ℕ) : C (n + 1) ⊆ C n := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    rcases haddr n with ⟨a, hP, hJ0, hJa⟩ | ⟨hP, hJs⟩
    · have hlen : (P (n + 1)).length = (P n).length + 1 := by simp [hP]
      have hget := hmatch (n + 1) (P n).length (by
        change (P n).length < (P (n + 1)).length
        omega)
      change g.s.get? (P n).length =
        some ⟨1, (((P (n + 1))[(P n).length]'(by omega)).val + 1 : ℕ)⟩ at hget
      simp only [hP, List.getElem_append_right (le_refl _), Nat.sub_self,
        List.getElem_cons_zero] at hget
      have hzM : z ∈ Set.Icc m M := ⟨hz.1, hz.2.trans (hU _).2⟩
      rw [hlen, hstep _ (a.val + 1) (Nat.succ_pos _) hget z hzM]
      refine ⟨1 / ((a.val + 1 : ℕ) + z), ?_, rfl⟩
      refine ⟨(hinverse _ (Nat.succ_pos _) (by have := a.isLt; omega) z hzM).1, ?_⟩
      have hJaR : ((J n + 1 : ℕ) : ℝ) ≤ (a.val + 1 : ℕ) := by
        exact_mod_cast Nat.succ_le_succ hJa
      exact one_div_le_one_div_of_le (by positivity : 0 < ((J n + 1 : ℕ) : ℝ) + m)
        (by linarith [hz.1])
    · rw [hP]
      refine ⟨z, ⟨hz.1, hz.2.trans ?_⟩, rfl⟩
      dsimp only [U]
      rw [hJs]
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      linarith
  have hanti : Antitone C := antitone_nat_of_succ_le hnested
  have hdiam : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      ∀ x ∈ C n, ∀ y ∈ C n, |x - y| < ε := by
    intro ε hε
    obtain ⟨B, hB⟩ := exists_nat_gt (1 / ε)
    refine ⟨3 * (B + 5), ?_⟩
    intro n hn x hx y hy
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    have hlen : B + 5 ≤ (P n).length := by have := htime n; have := hJ n; omega
    have hf := Nat.le_fib_self (n := (P n).length + 1) (by omega)
    have hBF : B < Nat.fib ((P n).length + 1) := (by omega : B < (P n).length + 1).trans_le hf
    have hF : 0 < (Nat.fib ((P n).length + 1) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos (P n).length)
    have hF1 : 1 ≤ (Nat.fib ((P n).length + 1) : ℝ) := by
      have := Nat.fib_pos.mpr (Nat.succ_pos (P n).length)
      exact_mod_cast this
    have hFε : 1 / ε < (Nat.fib ((P n).length + 1) : ℝ) :=
      hB.trans (by exact_mod_cast hBF)
    have hinv : 1 / (Nat.fib ((P n).length + 1) : ℝ) < ε :=
      (div_lt_iff₀ hF).mpr (by have := (div_lt_iff₀ hε).mp hFε; nlinarith)
    have hzH : z ∈ Set.Icc m M := ⟨hz.1, hz.2.trans (hU _).2⟩
    have hwH : w ∈ Set.Icc m M := ⟨hw.1, hw.2.trans (hU _).2⟩
    exact ((prefix_geometry g _ (fun i _ => hreal i)).2 z (hH hzH) w (hH hwH)).2.trans_lt
      ((one_div_le_one_div_of_le hF (by nlinarith :
        (Nat.fib ((P n).length + 1) : ℝ) ≤ (Nat.fib ((P n).length + 1) : ℝ) ^ 2)).trans_lt
          hinv)
  have hcompact (n : ℕ) : IsCompact (C n) := by
    apply isCompact_Icc.image_of_continuousOn
    have hc : ContinuousOn (fun z : ℝ =>
        (g.nums (P n).length + (g.contsAux (P n).length).a * z) /
          (g.dens (P n).length + (g.contsAux (P n).length).b * z)) (Set.Icc m (U n)) :=
      (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).div
        (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
        (fun z hz => ne_of_gt (hden _ z (hm.le.trans hz.1)))
    exact hc.congr (fun z _ => hform _ z)
  have hne (n : ℕ) : (C n).Nonempty :=
    ⟨T (P n).length m, m, ⟨le_rfl, (hU n).1⟩, rfl⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    hnested hne (hcompact 0) (fun n => (hcompact n).isClosed)
  have hxall : ∀ n, x ∈ C n := Set.mem_iInter.mp hx
  have hxC : x ∈ hallCantor := by
    apply (hall_cylinder_survivors x).2
    intro k
    let L := (P (3 * k)).length
    have hkL : k ≤ L := by have := htime (3 * k); have := hJ (3 * k); dsimp [L]; omega
    obtain ⟨z, hz, he⟩ := hxall (3 * k)
    have hzH : z ∈ Set.Icc m M := ⟨hz.1, hz.2.trans (hU _).2⟩
    have hL : x ∈ T L '' Set.Icc m M := ⟨z, hzH, he⟩
    have hsmall := hfull (L - k) k
    rw [Nat.add_sub_of_le hkL] at hsmall
    exact ⟨g, hh, fun i _ => hg i, hsmall hL⟩
  refine ⟨hanti, hdiam, x, ⟨hxall, hxC⟩, ?_⟩
  intro y hy
  apply eq_of_abs_sub_nonpos
  by_contra h
  have hpos : 0 < |y - x| := lt_of_not_ge h
  obtain ⟨N, hN⟩ := hdiam |y - x| hpos
  exact (lt_irrefl _) (hN N le_rfl y (hy.1 N) x (hxall N))

end D5.S1.Words.KAbelianLagrange
