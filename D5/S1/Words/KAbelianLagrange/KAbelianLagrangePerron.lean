/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangePerron
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangePerron
   mirror-E: none(waiver:reduced-perron-coefficient)
   anchors: [mathlib/module/Mathlib.NumberTheory.Real.Irrational]
   utility: none
   digest: Integral continuants identify reduced approximation coefficients with Perron tails. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeReverse
import Mathlib.NumberTheory.Real.Irrational

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open GenContFract

/-- The integral recurrence and unimodular determinant rule out any reduction factor
in the continuants. The reduced convergent coefficient therefore equals the next
complete quotient plus the actual reversed finite prefix, without a type restriction. -/
theorem perron_coefficient (x : ℝ) (hx : Irrational x) (n : ℕ) :
    1 / (((x.convergent n).den : ℝ) ^ 2 * |x - (x.convergent n : ℝ)|) =
      ((IntFractPair.stream x n).getD ⟨0, 0⟩).fr⁻¹ +
        GenContFract.convs'Aux (Stream'.Seq.ofList
          (List.ofFn (fun i : Fin n =>
            ((GenContFract.of x).s.get? i).getD ⟨1, 1⟩)).reverse) n := by
  classical
  let g := GenContFract.of x
  have hnt (m : ℕ) : ¬g.TerminatedAt m := by
    intro hm
    have he := GenContFract.of_correctness_of_terminatedAt hm
    rw [Real.convs_eq_convergent] at he
    exact hx.ne_rat _ he
  have hdigits : ∀ m, ∃ a : ℝ, 1 ≤ a ∧ g.s.get? m = some ⟨1, a⟩ := by
    intro m
    obtain ⟨P, hP⟩ := Option.ne_none_iff_exists'.mp (hnt m)
    have hnum := (GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hP).1
    refine ⟨P.b, GenContFract.of_one_le_get?_partDen
      (GenContFract.partDen_eq_s_b hP), ?_⟩
    exact hP.trans (congrArg some (by cases P; simp_all))
  choose a ha hs using hdigits
  have hq (m : ℕ) : 0 < g.dens m := by
    have hf : 0 < (Nat.fib (m + 1) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos m)
    exact lt_of_lt_of_le hf (prefix_geometry g m (fun i _ => ⟨a i, ha i, hs i⟩)).1
  have hint : ∀ m, ∃ p q : ℤ, g.contsAux m = ⟨(p : ℝ), (q : ℝ)⟩ := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        rcases m with (_ | _ | m)
        · exact ⟨1, 0, by simp [GenContFract.contsAux]⟩
        · exact ⟨⌊x⌋, 1, by simp [GenContFract.contsAux, g]⟩
        · obtain ⟨p, q, hpq⟩ := ih m (by omega)
          obtain ⟨p', q', hpq'⟩ := ih (m + 1) (by omega)
          obtain ⟨P, hP⟩ := Option.ne_none_iff_exists'.mp (hnt m)
          obtain ⟨hPa, b, hPb⟩ :=
            GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hP
          refine ⟨b * p' + p, b * q' + q, ?_⟩
          rw [GenContFract.contsAux_recurrence hP hpq hpq', hPa, hPb]
          simp
  obtain ⟨p, q, hpq⟩ := hint (n + 1)
  obtain ⟨p', q', hpq'⟩ := hint (n + 2)
  have hp : g.nums n = (p : ℝ) := by
    simpa only [GenContFract.num_eq_conts_a,
      GenContFract.nth_cont_eq_succ_nth_contAux] using congrArg Pair.a hpq
  have hqn : g.dens n = (q : ℝ) := by
    simpa only [GenContFract.den_eq_conts_b,
      GenContFract.nth_cont_eq_succ_nth_contAux] using congrArg Pair.b hpq
  have hp' : g.nums (n + 1) = (p' : ℝ) := by
    simpa only [GenContFract.num_eq_conts_a,
      GenContFract.nth_cont_eq_succ_nth_contAux] using congrArg Pair.a hpq'
  have hq' : g.dens (n + 1) = (q' : ℝ) := by
    simpa only [GenContFract.den_eq_conts_b,
      GenContFract.nth_cont_eq_succ_nth_contAux] using congrArg Pair.b hpq'
  have hqpos : 0 < q := by exact_mod_cast (hqn ▸ hq n)
  have hdet : p * q' - q * p' = (-1 : ℤ) ^ (n + 1) := by
    have hd := (SimpContFract.of x).determinant (hnt n)
    change g.nums n * g.dens (n + 1) - g.dens n * g.nums (n + 1) = _ at hd
    rw [hp, hqn, hp', hq'] at hd
    exact_mod_cast hd
  let r : ℚ := (p : ℚ) / (q : ℚ)
  have hr : x.convergent n = r := by
    apply Rat.cast_injective (α := ℝ)
    rw [← Real.convs_eq_convergent, GenContFract.conv_eq_num_div_den]
    change g.nums n / g.dens n = (r : ℝ)
    simp [r, hp, hqn]
  have hden : ((x.convergent n).den : ℝ) = g.dens n := by
    obtain ⟨d, hpd, hqd⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den p
      (ne_of_gt hqpos)
    change p = d * r.num at hpd
    change q = d * (r.den : ℤ) at hqd
    have hdpos : 0 < d := by
      have hrpos : (0 : ℤ) < r.den := by exact_mod_cast r.pos
      nlinarith
    have hdiv : d ∣ p * q' - q * p' := by
      refine ⟨r.num * q' - (r.den : ℤ) * p', ?_⟩
      rw [hpd, hqd]
      ring
    rw [hdet] at hdiv
    have hdle : d.natAbs ≤ 1 := by
      simpa only [Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow] using
        Int.natAbs_le_of_dvd_ne_zero hdiv (pow_ne_zero _ (by norm_num))
    have hd1 : d = 1 := by
      have habs : (d.natAbs : ℤ) = d := by
        rw [Int.natCast_natAbs, abs_of_pos hdpos]
      have : d ≤ 1 := by
        have hcast : (d.natAbs : ℤ) ≤ 1 := by exact_mod_cast hdle
        rwa [habs] at hcast
      omega
    rw [hd1, one_mul] at hqd
    rw [hr, hqn, hqd]
    norm_cast
  obtain ⟨P, hP⟩ : ∃ P, IntFractPair.stream x n = some P := by
    cases n with
    | zero => exact ⟨IntFractPair.of x, IntFractPair.stream_zero x⟩
    | succ m =>
        obtain ⟨Q, hQ, _⟩ :=
          IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some (hs m)
        exact ⟨Q, hQ⟩
  have hPne : P.fr ≠ 0 := by
    intro he
    have hterm := IntFractPair.stream_eq_none_of_fr_eq_zero hP he
    exact hnt n (GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr
      hterm)
  have hPpos : 0 < P.fr := lt_of_le_of_ne
    (IntFractPair.nth_stream_fr_nonneg hP) hPne.symm
  have hprev : 0 ≤ (g.contsAux n).b :=
    GenContFract.zero_le_of_contsAux_b
  have hD : 0 < P.fr⁻¹ * g.dens n + (g.contsAux n).b :=
    add_pos_of_pos_of_nonneg (mul_pos (inv_pos.mpr hPpos) (hq n)) hprev
  have herror : |x - g.convs n| =
      1 / (g.dens n * (P.fr⁻¹ * g.dens n + (g.contsAux n).b)) := by
    have he := GenContFract.sub_convs_eq hP
    change x - g.convs n = if P.fr = 0 then 0 else _ at he
    rw [if_neg hPne] at he
    simp only [← GenContFract.nth_cont_eq_succ_nth_contAux,
      ← GenContFract.den_eq_conts_b] at he
    rw [he, abs_div, abs_neg_one_pow, abs_of_pos (mul_pos (hq n) hD)]
  have hreverse := reversed_prefix_ratio g a ha hs n
  have hlist : (List.ofFn (fun i : Fin n =>
      (g.s.get? i).getD ⟨1, 1⟩)) =
        List.ofFn (fun i : Fin n => (⟨1, a i⟩ : Pair ℝ)) := by
    apply congrArg List.ofFn
    funext i
    rw [hs i, Option.getD_some]
  rw [hden, ← Real.convs_eq_convergent]
  change 1 / (g.dens n ^ 2 * |x - g.convs n|) = _
  rw [hP, Option.getD_some]
  change 1 / (g.dens n ^ 2 * |x - g.convs n|) =
    P.fr⁻¹ + GenContFract.convs'Aux (Stream'.Seq.ofList
      (List.ofFn (fun i : Fin n => (g.s.get? i).getD ⟨1, 1⟩)).reverse) n
  rw [hlist, hreverse, herror]
  field_simp [ne_of_gt (hq n), ne_of_gt hD]

end D5.S1.Words.KAbelianLagrange
