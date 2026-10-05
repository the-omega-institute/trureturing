/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeHallCylinders
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeHallCylinders
   mirror-E: none(waiver:hall-cylinder-survivors)
   anchors: [mathlib/module/Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat]
   utility: none
   digest: Surviving all four-digit cylinders forces one infinite computed expansion. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeHallHull
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open GenContFract

/-- The finite-level cylinders need not be chosen compatibly: their interior tail
coordinates force the computed digits, and hence force compatibility. Conversely,
every fractional tail of a four-digit expansion belongs to the same sharp hull. -/
theorem hall_cylinder_survivors (x : ℝ) :
    x ∈ hallCantor ↔ ∀ n : ℕ, ∃ g : GenContFract ℝ, g.h = 0 ∧
      (∀ i < n, ∃ a : ℕ, 0 < a ∧ a ≤ 4 ∧ g.s.get? i = some ⟨1, (a : ℝ)⟩) ∧
      x ∈ GenContFract.compExactValue (g.contsAux n) (g.conts n) ''
        Set.Icc ((Real.sqrt 2 - 1) / 2) (2 * (Real.sqrt 2 - 1)) := by
  classical
  let m := (Real.sqrt 2 - 1) / 2
  let M := 2 * (Real.sqrt 2 - 1)
  change x ∈ hallCantor ↔ ∀ n : ℕ, ∃ g : GenContFract ℝ, g.h = 0 ∧
    (∀ i < n, ∃ a : ℕ, 0 < a ∧ a ≤ 4 ∧ g.s.get? i = some ⟨1, (a : ℝ)⟩) ∧
    x ∈ GenContFract.compExactValue (g.contsAux n) (g.conts n) '' Set.Icc m M
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hsp := Real.sqrt_nonneg (2 : ℝ)
  have hsl : 1 < Real.sqrt 2 := by nlinarith
  have hsu : Real.sqrt 2 < 3 / 2 := by nlinarith
  have hm : 0 < m := by dsimp [m]; linarith
  have hM : M < 1 := by dsimp [M]; linarith
  have hI : Set.Icc m M ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro z hz
    exact ⟨hm.trans_le hz.1, hz.2.trans_lt hM⟩
  have hirr (v : ℝ)
      (hd : ∀ i, ∃ a : ℕ, 0 < a ∧ a ≤ 4 ∧
        (GenContFract.of v).s.get? i = some ⟨1, (a : ℝ)⟩) : Irrational v := by
    rintro ⟨q, hq⟩
    have ht : (GenContFract.of v).Terminates :=
      (GenContFract.terminates_iff_rat v).mpr ⟨q, hq.symm⟩
    obtain ⟨n, hn⟩ := ht
    obtain ⟨a, _, _, ha⟩ := hd n
    change (GenContFract.of v).s.get? n = none at hn
    rw [ha] at hn
    simp at hn
  constructor
  · intro hx n
    obtain ⟨_, hx0, hx1, hd⟩ := hx
    have hpairs : ∀ j, ∃ P : IntFractPair ℝ, IntFractPair.stream x j = some P := by
      intro j
      cases j with
      | zero => exact ⟨IntFractPair.of x, IntFractPair.stream_zero x⟩
      | succ j =>
          obtain ⟨a, _, _, ha⟩ := hd j
          obtain ⟨P, hP, _⟩ :=
            IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some ha
          exact ⟨P, hP⟩
    choose P hP using hpairs
    let f (j : ℕ) := (P j).fr
    have hf : ∀ j, 0 ≤ f j ∧ f j < 1 := by
      intro j
      exact IntFractPair.nth_stream_fr_nonneg_lt_one (hP j)
    have hfn : ∀ j, f j ≠ 0 := by
      intro j
      obtain ⟨Q, hQ, hQn, _⟩ :=
        IntFractPair.succ_nth_stream_eq_some_iff.mp (hP (j + 1))
      have hQP : Q = P j := Option.some.inj (hQ.symm.trans (hP j))
      rw [hQP] at hQn
      exact hQn
    have hnext : ∀ j, IntFractPair.of (f j)⁻¹ = P (j + 1) := by
      intro j
      have ht := IntFractPair.stream_succ_of_some (hP j) (hfn j)
      exact Option.some.inj (ht.symm.trans (hP (j + 1)))
    have hshift : ∀ j, ∃ b : ℤ,
        IntFractPair.stream (f n) j = some ⟨b, f (n + j)⟩ := by
      intro j
      induction j with
      | zero =>
          refine ⟨0, ?_⟩
          have hfloor := Int.floor_eq_zero_iff.mpr (hf n)
          simp [IntFractPair.stream_zero, IntFractPair.of, Int.fract, hfloor]
      | succ j ih =>
          obtain ⟨b, hb⟩ := ih
          refine ⟨(P (n + j + 1)).b, ?_⟩
          rw [IntFractPair.stream_succ_of_some hb (hfn (n + j)), hnext]
          simp only [Nat.add_assoc, f]
    have htaildigits : ∀ j, ∃ a : ℕ, 0 < a ∧ a ≤ 4 ∧
        (GenContFract.of (f n)).s.get? j = some ⟨1, (a : ℝ)⟩ := by
      intro j
      obtain ⟨a, ha0, ha4, ha⟩ := hd (n + j)
      obtain ⟨b, hb⟩ := hshift j
      have ht := IntFractPair.stream_succ_of_some hb (hfn (n + j))
      rw [hnext] at ht
      have hget := GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream ht
      have horig := GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream
        (hP (n + j + 1))
      refine ⟨a, ha0, ha4, ?_⟩
      rw [hget, ← horig, ha]
    have htail : f n ∈ hallCantor :=
      ⟨hirr (f n) htaildigits, lt_of_le_of_ne (hf n).1 (Ne.symm (hfn n)),
        (hf n).2, htaildigits⟩
    have htailH : f n ∈ Set.Icc m M := hall_cantor_hull.1 htail
    refine ⟨GenContFract.of x, ?_, fun i _ => hd i, f n, htailH, ?_⟩
    · rw [GenContFract.of_h_eq_floor,
        Int.floor_eq_zero_iff.mpr ⟨hx0.le, hx1⟩]
      simp
    · exact (GenContFract.compExactValue_correctness_of_stream_eq_some (hP n)).symm
  · intro hx
    let T (g : GenContFract ℝ) (n : ℕ) :=
      GenContFract.compExactValue (g.contsAux n) (g.conts n)
    have hform : ∀ g : GenContFract ℝ, ∀ n z, T g n z =
        (g.nums n + (g.contsAux n).a * z) /
          (g.dens n + (g.contsAux n).b * z) := by
      intro g n z
      by_cases hz : z = 0
      · simp [T, hz, GenContFract.compExactValue, GenContFract.num_eq_conts_a,
          GenContFract.den_eq_conts_b]
      · simp only [T, GenContFract.compExactValue, if_neg hz, GenContFract.nextConts,
          GenContFract.nextNum, GenContFract.nextDen, one_mul,
          GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b]
        rw [← mul_div_mul_right _ _ hz]
        congr 1 <;> field_simp [hz]
    have hstep (g : GenContFract ℝ) (n : ℕ)
        (hg : ∀ i < n + 1, ∃ a : ℕ, 0 < a ∧ a ≤ 4 ∧
          g.s.get? i = some ⟨1, (a : ℝ)⟩)
        (a : ℕ) (ha : g.s.get? n = some ⟨1, (a : ℝ)⟩)
        (ha0 : 0 < a) (z : ℝ) (hz : z ∈ Set.Ioo (0 : ℝ) 1) :
        T g (n + 1) z = T g n (1 / ((a : ℝ) + z)) := by
      have hreal : ∀ i < n + 1, ∃ b : ℝ, 1 ≤ b ∧ g.s.get? i = some ⟨1, b⟩ := by
        intro i hi
        obtain ⟨b, hb, _, hs⟩ := hg i hi
        exact ⟨b, by exact_mod_cast hb, hs⟩
      have hq : ∀ j, j ≤ n + 1 → 0 < g.dens j := by
        intro j hj
        have hfib : 0 < (Nat.fib (j + 1) : ℝ) := by
          exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos j)
        exact hfib.trans_le (prefix_geometry g j (fun i hi => hreal i (by omega))).1
      have hp : ∀ j, j ≤ n + 1 → 0 ≤ (g.contsAux j).b := by
        intro j hj
        cases j with
        | zero => simp [GenContFract.contsAux]
        | succ j =>
            simpa only [GenContFract.den_eq_conts_b,
              GenContFract.nth_cont_eq_succ_nth_contAux] using (hq j (by omega)).le
      have haz : 0 < (a : ℝ) + z := by
        have hap : (0 : ℝ) < a := by exact_mod_cast ha0
        linarith [hz.1]
      have hd : 0 < g.dens n + (g.contsAux n).b * (1 / ((a : ℝ) + z)) :=
        add_pos_of_pos_of_nonneg (hq n (by omega))
          (mul_nonneg (hp n (by omega)) (one_div_pos.mpr haz).le)
      have hn : 0 < g.dens (n + 1) + (g.contsAux (n + 1)).b * z :=
        add_pos_of_pos_of_nonneg (hq (n + 1) le_rfl)
          (mul_nonneg (hp (n + 1) le_rfl) hz.1.le)
      rw [hform, hform]
      simp only [GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b,
        GenContFract.nth_cont_eq_succ_nth_contAux] at hn hd ⊢
      rw [GenContFract.contsAux_recurrence ha rfl rfl] at hn ⊢
      simp only [one_mul] at hn ⊢
      apply (div_eq_div_iff (ne_of_gt hn) (ne_of_gt hd)).2
      field_simp [ne_of_gt haz]
      ring
    have hrecognize : ∀ n : ℕ, ∀ g : GenContFract ℝ, g.h = 0 →
        (∀ i < n, ∃ a : ℕ, 0 < a ∧ a ≤ 4 ∧ g.s.get? i = some ⟨1, (a : ℝ)⟩) →
        ∀ z ∈ Set.Ioo (0 : ℝ) 1,
        (∃ b : ℤ, IntFractPair.stream (T g n z) n = some ⟨b, z⟩) ∧
        (∀ i < n, (GenContFract.of (T g n z)).s.get? i = g.s.get? i) := by
      intro n
      induction n with
      | zero =>
          intro g hh _ z hz
          have hT : T g 0 z = z := by
            simp [hform, GenContFract.contsAux, GenContFract.zeroth_num_eq_h,
              GenContFract.zeroth_den_eq_one, hh]
          refine ⟨⟨0, ?_⟩, fun i hi => by omega⟩
          have hfloor := Int.floor_eq_zero_iff.mpr ⟨hz.1.le, hz.2⟩
          simp [hT, IntFractPair.stream_zero, IntFractPair.of, Int.fract, hfloor]
      | succ n ih =>
          intro g hh hg z hz
          obtain ⟨a, ha0, _, ha⟩ := hg n (by omega)
          let t := 1 / ((a : ℝ) + z)
          have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha0
          have ht : t ∈ Set.Ioo (0 : ℝ) 1 := by
            refine ⟨one_div_pos.mpr (by linarith [hz.1]), ?_⟩
            exact (div_lt_one (by linarith [hz.1])).mpr (by linarith [hz.1])
          obtain ⟨⟨b, hb⟩, hd⟩ := ih g hh (fun i hi => hg i (by omega)) t ht
          have he := hstep g n hg a ha ha0 z hz
          change T g (n + 1) z = T g n t at he
          rw [← he] at hb hd
          have hinv : t⁻¹ = (a : ℝ) + z := by simp [t]
          have hfloor : ⌊t⁻¹⌋ = (a : ℤ) := by
            rw [hinv]
            apply Int.floor_eq_iff.mpr
            push_cast
            exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
          have hpair : IntFractPair.of t⁻¹ = ⟨(a : ℤ), z⟩ := by
            simp only [IntFractPair.of, Int.fract]
            rw [hfloor, hinv]
            simp
          have hsucc := IntFractPair.stream_succ_of_some hb (ne_of_gt ht.1)
          rw [hpair] at hsucc
          refine ⟨⟨a, hsucc⟩, ?_⟩
          intro i hi
          by_cases hin : i < n
          · exact hd i hin
          · have hie : i = n := by omega
            subst i
            rw [GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream hsucc, ha]
            simp
    have hd : ∀ i, ∃ a : ℕ, 0 < a ∧ a ≤ 4 ∧
        (GenContFract.of x).s.get? i = some ⟨1, (a : ℝ)⟩ := by
      intro i
      obtain ⟨g, hh, hg, z, hz, he⟩ := hx (i + 1)
      obtain ⟨a, ha0, ha4, ha⟩ := hg i (by omega)
      have hget := (hrecognize (i + 1) g hh hg z (hI hz)).2 i (by omega)
      change T g (i + 1) z = x at he
      rw [he, ha] at hget
      exact ⟨a, ha0, ha4, hget⟩
    have hxx : x ∈ Set.Icc m M := by
      obtain ⟨g, hh, _, z, hz, he⟩ := hx 0
      have hT : GenContFract.compExactValue (g.contsAux 0) (g.conts 0) z = z := by
        change T g 0 z = z
        simp [hform, GenContFract.contsAux, GenContFract.zeroth_num_eq_h,
          GenContFract.zeroth_den_eq_one, hh]
      rw [hT] at he
      exact he ▸ hz
    exact ⟨hirr x hd, (hI hxx).1, (hI hxx).2, hd⟩

end D5.S1.Words.KAbelianLagrange
