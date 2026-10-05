/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeContinuous
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeContinuous
   mirror-E: none(waiver:continuous-feedback-realization)
   anchors: [mathlib/module/Mathlib.Topology.Instances.ENNReal.Lemmas]
   utility: none
   digest: Continuous feedback realizes its target while controlling every Perron position. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeFeedbackDigits
import D5.S1.Words.KAbelianLagrange.KAbelianLagrangePeaks
import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeDigits
import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeLegendre
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open GenContFract Filter
open scoped Topology

/-- Sampling the growing finite prefixes makes the target depend on the slope that
is being constructed. The central coefficients converge to that target. Away from
centers the two fractional tails keep coefficients below six; excluding finitely
many early centers then controls the upper limit at every position. -/
theorem continuous_feedback_realization (seed : List ℕ) (A B : ℕ)
    (hseed : ∀ a ∈ seed, 0 < a ∧ a ≤ A) (F : ℝ → ℝ)
    (hF : Continuous F) (hbound : ∀ z, 6 < F z ∧ F z ≤ (B : ℝ)) :
    ∃ α : ℝ, Irrational α ∧ 0 < α ∧ α < 1 ∧
      (∀ i : ℕ, ∀ hi : i < seed.length,
        (GenContFract.of α).s.get? i = some ⟨1, (seed[i] : ℝ)⟩) ∧
      (∀ i, ∃ a : ℕ, 0 < a ∧ a ≤ max A (max 4 B) ∧
        (GenContFract.of α).s.get? i = some ⟨1, (a : ℝ)⟩) ∧
      limsup (fun q : ℕ => ENNReal.ofReal
        (1 / ((q : ℝ) * |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)|)))
        atTop = ENNReal.ofReal (F α) := by
  classical
  let S (p : List ℕ) : GenContFract ℝ :=
    ⟨0, Stream'.Seq.ofList (p.map fun a : ℕ => (⟨1, (a : ℝ)⟩ : Pair ℝ))⟩
  let T (p : List ℕ) := F ((S p).convs p.length)
  obtain ⟨P, d, c, x, y, u, v, hzero, hp, hc, hd, hnc, hj⟩ :=
    feedback_digit_construction seed A B hseed T (fun p => hbound _)
  have hlen (j : ℕ) : (P (j + 1)).length = (P j).length + 2 * (j + 1) + 1 := by
    rw [(hj j).2.2.2.2.2.2.2]
    simp only [List.length_append, List.length_reverse, List.length_ofFn,
      List.length_singleton]
    omega
  have hgrowth : ∀ j, j ≤ (P j).length := by
    intro j
    induction j with
    | zero => omega
    | succ j ih => rw [hlen]; omega
  let g : GenContFract ℝ :=
    ⟨0, Stream'.Seq.ofStream (fun i => ⟨1, (d i : ℝ)⟩)⟩
  have hg (i : ℕ) : ∃ a : ℕ, 0 < a ∧ g.s.get? i = some ⟨1, (a : ℝ)⟩ :=
    ⟨d i, (hd i).1, rfl⟩
  obtain ⟨α, hα, hα0, hα1, hconv, hcyl⟩ := integer_stream_value g rfl hg
  have he : GenContFract.of α = g := stream_digit_recovery g rfl hg α hcyl
  have hs (i : ℕ) : (GenContFract.of α).s.get? i = some ⟨1, (d i : ℝ)⟩ := by
    rw [he]; rfl
  have hget (j i : ℕ) (hi : i < (P j).length) : (P j)[i] = d i := by
    have hh := congrArg (fun p : List ℕ => p[i]?) (hp j)
    apply Option.some.inj
    simpa only [List.getElem?_eq_getElem hi, List.getElem?_ofFn, dif_pos hi] using hh
  have hsample (j : ℕ) : (S (P j)).convs (P j).length = g.convs (P j).length := by
    have hmatch (i : ℕ) (hi : i < (P j).length) : (S (P j)).s.get? i = g.s.get? i := by
      simp only [S, Stream'.Seq.ofList_get?, List.getElem?_map,
        List.getElem?_eq_getElem hi, Option.map_some]
      rw [hget j i hi]
      rfl
    have hcont : ∀ n, n ≤ (P j).length + 1 → (S (P j)).contsAux n = g.contsAux n := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro hn
          rcases n with (_ | _ | n)
          · rfl
          · rfl
          · simp only [GenContFract.contsAux, hmatch n (by omega),
              ih n (by omega) (by omega), ih (n + 1) (by omega) (by omega)]
    simp only [GenContFract.convs, GenContFract.nums, GenContFract.dens,
      GenContFract.conts, Stream'.map, Stream'.get, Stream'.tail]
    rw [hcont _ le_rfl]
  have hlength : Tendsto (fun j => (P j).length) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop N] with j hjN
    exact hjN.trans (hgrowth j)
  have htarget : Tendsto (fun j => T (P j)) atTop (𝓝 (F α)) := by
    have hh := hF.continuousAt.tendsto.comp (hconv.comp hlength)
    exact hh.congr' (Eventually.of_forall (fun j => congrArg F (hsample j).symm))
  let H (n : ℕ) : ℝ :=
    1 / (((α.convergent n).den : ℝ) ^ 2 * |α - (α.convergent n : ℝ)|)
  have hpeak (j : ℕ) : |H (c j) - T (P j)| ≤ 2 / (Nat.fib (j + 2) : ℝ) ^ 2 := by
    obtain ⟨hx, hy, ht, _, _, hcenter, hdigits, hstep⟩ := hj j
    have hleft (i : ℕ) (hi : i < j + 1) :
        (GenContFract.of α).s.get? (c j - (i + 1)) = (GenContFract.of (x j)).s.get? i := by
      rw [hs, (hdigits i).1.2.2]
      congr 2
      have hn : c j - (i + 1) < (P (j + 1)).length := by
        rw [hlen, hcenter]; omega
      rw [← hget (j + 1) _ hn]
      simp only [hstep]
      have hl : c j - (i + 1) <
          (P j ++ (List.ofFn (fun t : Fin (j + 1) => u j t)).reverse).length := by
        simp only [List.length_append, List.length_reverse, List.length_ofFn]
        rw [hcenter]; omega
      have hl' : c j - (i + 1) <
          (P j ++ (List.ofFn (fun t : Fin (j + 1) => u j t)).reverse ++ [d (c j)]).length :=
        hl.trans_le (by simp)
      rw [List.getElem_append_left hl', List.getElem_append_left hl,
        List.getElem_append_right (by rw [hcenter]; omega), List.getElem_reverse]
      simp only [List.length_ofFn, List.getElem_ofFn]
      have hidx : j + 1 - 1 - (c j - (i + 1) - (P j).length) = i := by
        rw [hcenter]
        omega
      rw [hidx]
    have hright (i : ℕ) (hi : i < j + 1) :
        (GenContFract.of α).s.get? (c j + 1 + i) = (GenContFract.of (y j)).s.get? i := by
      rw [hs, (hdigits i).2.2.2]
      congr 2
      have hn : c j + 1 + i < (P (j + 1)).length := by
        rw [hlen, hcenter]; omega
      rw [← hget (j + 1) _ hn]
      simp only [hstep]
      have hl : (P j ++ (List.ofFn (fun t : Fin (j + 1) => u j t)).reverse ++
          [d (c j)]).length = c j + 1 := by
        simp only [List.length_append, List.length_reverse, List.length_ofFn,
          List.length_singleton, hcenter]
      rw [List.getElem_append_right (by rw [hl]; omega)]
      simp only [hl, Nat.add_sub_cancel_left, List.getElem_ofFn]
    have hh := perron_block_estimate α (x j) (y j) hα hx.1 hx.2.1 hx.2.2.1
      hy.1 hy.2.1 hy.2.2.1 (c j) (j + 1) (by rw [hcenter]; omega) hleft hright
    rw [hs, Option.getD_some] at hh
    dsimp only [H]
    rw [ht]
    convert hh using 1; congr 1; ring
  have hfib : Tendsto (fun j => (Nat.fib (j + 2) : ℝ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt b
    filter_upwards [eventually_ge_atTop (max N 5)] with j hjN
    have hn : (N : ℝ) ≤ (j + 2 : ℕ) := by exact_mod_cast (show N ≤ j + 2 by omega)
    have hf : ((j + 2 : ℕ) : ℝ) ≤ Nat.fib (j + 2) := by
      exact_mod_cast Nat.le_fib_self (show 5 ≤ j + 2 by omega)
    exact hN.le.trans (hn.trans hf)
  have herr : Tendsto (fun j => 2 / (Nat.fib (j + 2) : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, Pi.inv_apply, zero_pow (by decide : 2 ≠ 0), mul_zero] using
      (tendsto_const_nhds (x := (2 : ℝ))).mul (hfib.inv_tendsto_atTop.pow 2)
  have hdiff : Tendsto (fun j => H (c j) - T (P j)) atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa only [neg_zero] using herr.neg) herr
      (fun j => (abs_le.mp (hpeak j)).1) (fun j => (abs_le.mp (hpeak j)).2)
  have hcentral : Tendsto (fun j => H (c j)) atTop (𝓝 (F α)) := by
    simpa only [sub_add_cancel, zero_add] using hdiff.add htarget
  have hq (n : ℕ) : 0 < g.dens n := by
    have hf : 0 < (Nat.fib (n + 1) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos n)
    exact hf.trans_le (prefix_geometry g n
      (fun i _ => ⟨(d i : ℝ), by exact_mod_cast (hd i).1, rfl⟩)).1
  have hupper (n : ℕ) : H n < (d n : ℝ) + 2 := by
    obtain ⟨Q, hQ, hbQ⟩ :=
      IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some (hs n)
    obtain ⟨R, hR, _, hQR⟩ := IntFractPair.succ_nth_stream_eq_some_iff.mp hQ
    have hfr := congrArg IntFractPair.fr hQR
    have hb := congrArg IntFractPair.b hQR
    have hinv : R.fr⁻¹ = (d n : ℝ) + Q.fr := by
      simp only [IntFractPair.of, Int.fract] at hfr hb
      have hb' : (⌊R.fr⁻¹⌋ : ℝ) = (d n : ℝ) := by rw [hb]; exact hbQ
      rw [← hb', ← hfr]
      ring
    have hh := perron_coefficient α hα n
    have hl : List.ofFn (fun i : Fin n =>
        ((GenContFract.of α).s.get? i).getD ⟨1, 1⟩) =
          List.ofFn (fun i : Fin n => (⟨1, (d i : ℝ)⟩ : Pair ℝ)) := by
      apply congrArg List.ofFn
      funext i
      rw [hs, Option.getD_some]
    rw [hR, Option.getD_some, hinv, hl,
      reversed_prefix_ratio g (fun i => (d i : ℝ))
        (fun i => by exact_mod_cast (hd i).1) (fun _ => rfl) n] at hh
    have hr : (g.contsAux n).b / g.dens n ≤ 1 := by
      apply (div_le_one (hq n)).mpr
      cases n with
      | zero => simp [GenContFract.contsAux, GenContFract.zeroth_den_eq_one]
      | succ n =>
          simpa only [he, ← GenContFract.nth_cont_eq_succ_nth_contAux,
            ← GenContFract.den_eq_conts_b] using GenContFract.of_den_mono (v := α) (n := n)
    have hQfr := (IntFractPair.nth_stream_fr_nonneg_lt_one hQ).2
    dsimp only [H]
    linarith
  have hfull : ∀ b : ℝ, F α < b → ∀ᶠ n in atTop, H n ≤ b := by
    intro b hb
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (hcentral.eventually (eventually_lt_nhds hb))
    filter_upwards [eventually_ge_atTop (max seed.length (c J))] with n hn
    by_cases hcen : ∃ j, n = c j
    · obtain ⟨j, rfl⟩ := hcen
      have hjJ : J ≤ j := hc.le_iff_le.mp (by omega)
      exact (hJ j hjJ).le
    · have hnseed : seed.length ≤ n := by omega
      have hsmall : d n ≤ 4 := hnc n hnseed (fun j heq => hcen ⟨j, heq⟩)
      have hsmall' : (d n : ℝ) ≤ 4 := by exact_mod_cast hsmall
      linarith [(hbound α).1, hupper n]
  have hlim : limsup (fun n => ENNReal.ofReal (H n)) atTop = ENNReal.ofReal (F α) := by
    apply le_antisymm
    · apply (limsup_le_iff).mpr
      intro b hb
      by_cases hbtop : b = ⊤
      · subst b
        exact Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
      · have hbF : F α < b.toReal := by
          exact (ENNReal.ofReal_lt_iff_lt_toReal (by linarith [(hbound α).1]) hbtop).mp hb
        obtain ⟨t, htF, htb⟩ := exists_between hbF
        filter_upwards [hfull t htF] with n hn
        exact (ENNReal.ofReal_le_ofReal hn).trans_lt
          ((ENNReal.ofReal_lt_iff_lt_toReal (by linarith [(hbound α).1]) hbtop).mpr htb)
    · have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hcentral
      have hsub := hc.tendsto_atTop.limsup_comp_le_limsup
        (u := fun n => ENNReal.ofReal (H n))
      exact hh.limsup_eq.symm.le.trans hsub
  have hlagrange : limsup (fun q : ℕ => ENNReal.ofReal
      (1 / ((q : ℝ) * |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)|)))
      atTop = ENNReal.ofReal (F α) := by
    apply le_antisymm
    · have hh := lagrange_limsup_upper α hα
      change _ ≤ max 2 (limsup (fun n => ENNReal.ofReal (H n)) atTop) at hh
      rw [hlim, max_eq_right] at hh
      · exact hh
      · have hhF := ENNReal.ofReal_le_ofReal (show (2 : ℝ) ≤ F α by
          linarith [(hbound α).1])
        simpa using hhF
    · have hh := lagrange_limsup_lower α hα
      change limsup (fun n => ENNReal.ofReal (H n)) atTop ≤ _ at hh
      rwa [hlim] at hh
  refine ⟨α, hα, hα0, hα1, ?_, ?_, hlagrange⟩
  · intro i hi
    rw [hs]
    congr 2
    have hh := hget 0 i (by rw [hzero]; exact hi)
    simpa only [hzero] using congrArg (fun a : ℕ => (a : ℝ)) hh.symm
  · intro i
    exact ⟨d i, (hd i).1, (hd i).2, hs i⟩

end D5.S1.Words.KAbelianLagrange
