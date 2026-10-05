/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangePeaks
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangePeaks
   mirror-E: none(waiver:two-sided-splice-estimate)
   anchors: []
   utility: none
   digest: Matching reversed and forward blocks control the actual Perron coefficient. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangePerron

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open GenContFract

/-- The finite backward tail and infinite forward tail at a center can be compared
with independently chosen irrational tails. The backwards recursion stops at the
seed boundary; telescoping each common block through its continuants gives a
uniform estimate independent of everything outside the two blocks. -/
theorem perron_block_estimate (α x y : ℝ) (hα : Irrational α)
    (hx : Irrational x) (hx0 : 0 < x) (hx1 : x < 1)
    (hy : Irrational y) (hy0 : 0 < y) (hy1 : y < 1)
    (n L : ℕ) (hLn : L ≤ n)
    (hleft : ∀ i < L,
      (GenContFract.of α).s.get? (n - (i + 1)) = (GenContFract.of x).s.get? i)
    (hright : ∀ i < L,
      (GenContFract.of α).s.get? (n + 1 + i) = (GenContFract.of y).s.get? i) :
    |1 / (((α.convergent n).den : ℝ) ^ 2 * |α - (α.convergent n : ℝ)|) -
      (((GenContFract.of α).s.get? n).getD ⟨1, 1⟩).b - x - y| ≤
        2 / (Nat.fib (L + 1) : ℝ) ^ 2 := by
  classical
  have hdata (t : ℝ) (ht : Irrational t) :
      ∃ f a : ℕ → ℝ,
        (∀ i, 0 < f i ∧ f i < 1) ∧
        (∀ i, 1 ≤ a i) ∧
        (∀ i, (GenContFract.of t).s.get? i = some ⟨1, a i⟩) ∧
        (∀ i, f i = 1 / (a i + f (i + 1))) ∧
        (∀ i, ((IntFractPair.stream t i).getD ⟨0, 0⟩).fr = f i) ∧
        f 0 = Int.fract t := by
    have hnt (i : ℕ) : ¬(GenContFract.of t).TerminatedAt i := by
      intro hi
      have he := GenContFract.of_correctness_of_terminatedAt hi
      rw [Real.convs_eq_convergent] at he
      exact ht.ne_rat _ he
    have hpairs : ∀ i, ∃ P : IntFractPair ℝ, IntFractPair.stream t i = some P := by
      intro i
      cases i with
      | zero => exact ⟨IntFractPair.of t, IntFractPair.stream_zero t⟩
      | succ i =>
          obtain ⟨Q, hQ⟩ := Option.ne_none_iff_exists'.mp (hnt i)
          obtain ⟨P, hP, _⟩ :=
            IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some hQ
          exact ⟨P, hP⟩
    choose P hP using hpairs
    let f (i : ℕ) := (P i).fr
    let a (i : ℕ) : ℝ := (P (i + 1)).b
    have hf (i : ℕ) : 0 < f i ∧ f i < 1 := by
      have hb := IntFractPair.nth_stream_fr_nonneg_lt_one (hP i)
      have hn : (P i).fr ≠ 0 := by
        intro he
        exact hnt i
          (GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr
            (IntFractPair.stream_eq_none_of_fr_eq_zero (hP i) he))
      exact ⟨lt_of_le_of_ne hb.1 hn.symm, hb.2⟩
    refine ⟨f, a, hf, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      dsimp only [a]
      exact_mod_cast IntFractPair.one_le_succ_nth_stream_b (hP (i + 1))
    · intro i
      exact GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream (hP (i + 1))
    · intro i
      obtain ⟨Q, hQ, _, hstep⟩ :=
        IntFractPair.succ_nth_stream_eq_some_iff.mp (hP (i + 1))
      have hQP : Q = P i := Option.some.inj (hQ.symm.trans (hP i))
      subst Q
      have hfr := congrArg IntFractPair.fr hstep
      have hb := congrArg IntFractPair.b hstep
      have he : (f i)⁻¹ = a i + f (i + 1) := by
        simp only [IntFractPair.of, Int.fract] at hb hfr
        dsimp only [f, a]
        rw [← hb, ← hfr]
        ring
      rw [← he]
      simp
    · intro i
      rw [hP i, Option.getD_some]
    · have he := Option.some.inj ((hP 0).symm.trans (IntFractPair.stream_zero t))
      exact congrArg IntFractPair.fr he
  obtain ⟨f, a, hf, ha, hs, hrec, hread, _⟩ := hdata α hα
  obtain ⟨fx, ax, hfx, hax, hsx, hrecx, _, hfx0⟩ := hdata x hx
  obtain ⟨fy, ay, hfy, hay, hsy, hrecy, _, hfy0⟩ := hdata y hy
  have hxfract : fx 0 = x := by
    rw [hfx0, Int.fract, Int.floor_eq_zero_iff.mpr ⟨hx0.le, hx1⟩]
    simp
  have hyfract : fy 0 = y := by
    rw [hfy0, Int.fract, Int.floor_eq_zero_iff.mpr ⟨hy0.le, hy1⟩]
    simp
  let g := GenContFract.of α
  let r (i : ℕ) := (g.contsAux i).b / g.dens i
  have hq (i : ℕ) : 0 < g.dens i := by
    have hb : 0 < (Nat.fib (i + 1) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos i)
    exact hb.trans_le (prefix_geometry g i (fun j _ => ⟨a j, ha j, hs j⟩)).1
  have hr (i : ℕ) : r i ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg GenContFract.zero_le_of_contsAux_b (hq i).le,
      (div_le_one (hq i)).mpr ?_⟩
    cases i with
    | zero => simp [GenContFract.contsAux, GenContFract.zeroth_den_eq_one]
    | succ i =>
        simpa only [← GenContFract.nth_cont_eq_succ_nth_contAux,
          ← GenContFract.den_eq_conts_b] using
            (GenContFract.of_den_mono (v := α) (n := i))
  have hrrec (i : ℕ) : r (i + 1) = 1 / (a i + r i) := by
    have hd : g.dens (i + 1) = a i * g.dens i + (g.contsAux i).b := by
      simp only [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
      rw [GenContFract.contsAux_recurrence (hs i) rfl rfl]
      simp [g]
    dsimp only [r]
    simp only [← GenContFract.nth_cont_eq_succ_nth_contAux,
      ← GenContFract.den_eq_conts_b]
    rw [hd]
    field_simp [ne_of_gt (hq i)]
  have hcontract (G : GenContFract ℝ) (hG : G.h = 0) (b z w : ℕ → ℝ)
      (hb : ∀ i, 1 ≤ b i) (hsG : ∀ i, G.s.get? i = some ⟨1, b i⟩)
      (hz : ∀ i ≤ L, z i ∈ Set.Icc (0 : ℝ) 1)
      (hw : ∀ i ≤ L, w i ∈ Set.Icc (0 : ℝ) 1)
      (hzrec : ∀ i < L, z i = 1 / (b i + z (i + 1)))
      (hwrec : ∀ i < L, w i = 1 / (b i + w (i + 1))) :
      |z 0 - w 0| ≤ 1 / (Nat.fib (L + 1) : ℝ) ^ 2 := by
    let T (i : ℕ) := GenContFract.compExactValue (G.contsAux i) (G.conts i)
    have hform (i : ℕ) (s : ℝ) : T i s =
        (G.nums i + (G.contsAux i).a * s) /
          (G.dens i + (G.contsAux i).b * s) := by
      by_cases he : s = 0
      · simp [T, he, GenContFract.compExactValue, GenContFract.num_eq_conts_a,
          GenContFract.den_eq_conts_b]
      · simp only [T, GenContFract.compExactValue, if_neg he, GenContFract.nextConts,
          GenContFract.nextNum, GenContFract.nextDen, one_mul,
          GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b]
        rw [← mul_div_mul_right _ _ he]
        congr 1 <;> field_simp [he]
    have hden (i : ℕ) (s : ℝ) (hs0 : 0 ≤ s) :
        0 < G.dens i + (G.contsAux i).b * s := by
      have hqi : 0 < G.dens i := by
        have hfi : 0 < (Nat.fib (i + 1) : ℝ) := by
          exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos i)
        exact hfi.trans_le (prefix_geometry G i (fun j _ => ⟨b j, hb j, hsG j⟩)).1
      have hp : 0 ≤ (G.contsAux i).b := by
        cases i with
        | zero => simp [GenContFract.contsAux]
        | succ i =>
            have hh := (prefix_geometry G i (fun j _ => ⟨b j, hb j, hsG j⟩)).1
            simpa only [GenContFract.den_eq_conts_b,
              GenContFract.nth_cont_eq_succ_nth_contAux] using
                (le_trans (by positivity : (0 : ℝ) ≤ Nat.fib (i + 1)) hh)
      exact add_pos_of_pos_of_nonneg hqi (mul_nonneg hp hs0)
    have hstep (i : ℕ) (s : ℝ) (hs0 : 0 ≤ s) :
        T (i + 1) s = T i (1 / (b i + s)) := by
      have hbs : 0 < b i + s := by linarith [hb i]
      have hd := hden i _ (one_div_pos.mpr hbs).le
      have hn := hden (i + 1) s hs0
      rw [hform, hform]
      simp only [GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b,
        GenContFract.nth_cont_eq_succ_nth_contAux] at hn hd ⊢
      rw [GenContFract.contsAux_recurrence (hsG i) rfl rfl] at hn ⊢
      simp only [one_mul] at hn ⊢
      apply (div_eq_div_iff (ne_of_gt hn) (ne_of_gt hd)).2
      field_simp [ne_of_gt hbs]
      ring
    have htel (v : ℕ → ℝ) (hv : ∀ i ≤ L, v i ∈ Set.Icc (0 : ℝ) 1)
        (hvrec : ∀ i < L, v i = 1 / (b i + v (i + 1))) :
        ∀ i ≤ L, T i (v i) = v 0 := by
      intro i
      induction i with
      | zero =>
          intro _
          simp [hform, GenContFract.contsAux, GenContFract.zeroth_num_eq_h,
            GenContFract.zeroth_den_eq_one, hG]
      | succ i ih =>
          intro hi
          rw [hstep i _ (hv (i + 1) hi).1, ← hvrec i (by omega)]
          exact ih (by omega)
    have hh := ((prefix_geometry G L (fun i _ => ⟨b i, hb i, hsG i⟩)).2
      (z L) (hz L le_rfl) (w L) (hw L le_rfl)).2
    change |T L (z L) - T L (w L)| ≤ _ at hh
    rwa [htel z hz hzrec L le_rfl, htel w hw hwrec L le_rfl] at hh
  have hxhead : (GenContFract.of x).h = 0 := by
    rw [GenContFract.of_h_eq_floor, Int.floor_eq_zero_iff.mpr ⟨hx0.le, hx1⟩]
    simp
  have hyhead : (GenContFract.of y).h = 0 := by
    rw [GenContFract.of_h_eq_floor, Int.floor_eq_zero_iff.mpr ⟨hy0.le, hy1⟩]
    simp
  have hback : |r n - x| ≤ 1 / (Nat.fib (L + 1) : ℝ) ^ 2 := by
    have hh := hcontract (GenContFract.of x) hxhead ax (fun i => r (n - i)) fx
      hax hsx (fun i _ => hr _) (fun i _ => ⟨(hfx i).1.le, (hfx i).2.le⟩)
      ?_ (fun i _ => hrecx i)
    · simpa only [Nat.sub_zero, hxfract] using hh
    · intro i hi
      have hd : a (n - (i + 1)) = ax i := by
        have he := hleft i hi
        rw [hs, hsx] at he
        exact congrArg Pair.b (Option.some.inj he)
      have hn : n - i = n - (i + 1) + 1 := by omega
      rw [hn, hrrec, hd]
  have hforward : |f (n + 1) - y| ≤ 1 / (Nat.fib (L + 1) : ℝ) ^ 2 := by
    have hh := hcontract (GenContFract.of y) hyhead ay (fun i => f (n + 1 + i)) fy
      hay hsy (fun i _ => ⟨(hf _).1.le, (hf _).2.le⟩)
      (fun i _ => ⟨(hfy i).1.le, (hfy i).2.le⟩) ?_ (fun i _ => hrecy i)
    · simpa only [Nat.add_zero, hyfract] using hh
    · intro i hi
      have hd : a (n + 1 + i) = ay i := by
        have he := hright i hi
        rw [hs, hsy] at he
        exact congrArg Pair.b (Option.some.inj he)
      rw [hrec, hd]
      congr 2
  have hcoef : 1 / (((α.convergent n).den : ℝ) ^ 2 *
      |α - (α.convergent n : ℝ)|) = a n + f (n + 1) + r n := by
    have he := perron_coefficient α hα n
    rw [hread] at he
    have hl : List.ofFn (fun i : Fin n =>
        ((GenContFract.of α).s.get? i).getD ⟨1, 1⟩) =
          List.ofFn (fun i : Fin n => (⟨1, a i⟩ : Pair ℝ)) := by
      apply congrArg List.ofFn
      funext i
      rw [hs, Option.getD_some]
    rw [hl, reversed_prefix_ratio g a ha hs n] at he
    rw [hrec n] at he
    simpa only [one_div, inv_inv] using he
  rw [hcoef, hs n, Option.getD_some]
  have he : a n + f (n + 1) + r n - a n - x - y =
      (r n - x) + (f (n + 1) - y) := by ring
  rw [he]
  calc
    _ ≤ |r n - x| + |f (n + 1) - y| := abs_add_le _ _
    _ ≤ 1 / (Nat.fib (L + 1) : ℝ) ^ 2 +
        1 / (Nat.fib (L + 1) : ℝ) ^ 2 := add_le_add hback hforward
    _ = _ := by ring

end D5.S1.Words.KAbelianLagrange
