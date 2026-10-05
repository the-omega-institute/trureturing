/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeHallHull
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeHallHull
   mirror-E: none(waiver:bounded-digit-cantor-hull)
   anchors: [mathlib/module/Mathlib.NumberTheory.Real.Irrational]
   utility: none
   digest: Joint extremal tail estimates determine the exact hull of the four-digit Cantor set. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangePrefix
import Mathlib.NumberTheory.Real.Irrational

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open GenContFract

/-- The classical continued-fraction Cantor set with positive digits at most four,
using Mathlib's computed expansion rather than a second digit or value representation. -/
def hallCantor : Set ℝ :=
  {x | Irrational x ∧ 0 < x ∧ x < 1 ∧
    ∀ n, ∃ a : ℕ, 0 < a ∧ a ≤ 4 ∧
      (GenContFract.of x).s.get? n = some ⟨1, (a : ℝ)⟩}

/-- The hull endpoints are the alternating expansions with digits four and one.
For an arbitrary point, the infimum and supremum of all of its fractional tails are
coupled by reciprocal bounds; solving their joint inequalities gives the sharp hull. -/
theorem hall_cantor_hull :
    let m := (Real.sqrt 2 - 1) / 2
    let M := 2 * (Real.sqrt 2 - 1)
    hallCantor ⊆ Set.Icc m M ∧ m ∈ hallCantor ∧ M ∈ hallCantor := by
  classical
  dsimp only
  let m := (Real.sqrt 2 - 1) / 2
  let M := 2 * (Real.sqrt 2 - 1)
  change hallCantor ⊆ Set.Icc m M ∧ m ∈ hallCantor ∧ M ∈ hallCantor
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hsp := Real.sqrt_nonneg (2 : ℝ)
  have hsl : 1 < Real.sqrt 2 := by nlinarith
  have hsu : Real.sqrt 2 < 3 / 2 := by nlinarith
  have hm : 0 < m := by dsimp [m]; linarith
  have hM : 0 < M := by dsimp [M]; linarith
  have hml : m < 1 := by dsimp [m]; linarith
  have hMl : M < 1 := by dsimp [M]; linarith
  have hpoly : 4 * m ^ 2 + 4 * m = 1 := by dsimp [m]; nlinarith
  have hmrec : m = 1 / (4 + M) := by
    apply (eq_div_iff (by linarith : (4 : ℝ) + M ≠ 0)).mpr
    dsimp [m, M]
    nlinarith
  have hMrec : M = 1 / (1 + m) := by
    apply (eq_div_iff (by linarith : (1 : ℝ) + m ≠ 0)).mpr
    dsimp [m, M]
    nlinarith
  have hbounds : hallCantor ⊆ Set.Icc m M := by
    intro x hx
    obtain ⟨hix, hx0, hx1, hd⟩ := hx
    have hpairs : ∀ n, ∃ P : IntFractPair ℝ, IntFractPair.stream x n = some P := by
      intro n
      cases n with
      | zero => exact ⟨IntFractPair.of x, IntFractPair.stream_zero x⟩
      | succ n =>
          obtain ⟨a, _, _, ha⟩ := hd n
          obtain ⟨P, hP, _⟩ := IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some ha
          exact ⟨P, hP⟩
    choose P hP using hpairs
    let f (n : ℕ) := (P n).fr
    have hf : ∀ n, 0 ≤ f n ∧ f n < 1 := by
      intro n
      exact IntFractPair.nth_stream_fr_nonneg_lt_one (hP n)
    have hrec : ∀ n, ∃ a : ℝ, 1 ≤ a ∧ a ≤ 4 ∧ f n = 1 / (a + f (n + 1)) := by
      intro n
      obtain ⟨a, ha0, ha4, ha⟩ := hd n
      obtain ⟨Q, hQ, hQb⟩ := IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some ha
      have hQP : Q = P (n + 1) := Option.some.inj (hQ.symm.trans (hP _))
      subst Q
      obtain ⟨R, hR, hRn, hReq⟩ := IntFractPair.succ_nth_stream_eq_some_iff.mp (hP (n + 1))
      have hRP : R = P n := Option.some.inj (hR.symm.trans (hP _))
      subst R
      have hb : ((P (n + 1)).b : ℝ) = a := hQb
      have hinv : (f n)⁻¹ = (a : ℝ) + f (n + 1) := by
        have hfr := congrArg IntFractPair.fr hReq
        simp only [IntFractPair.of, Int.fract] at hfr
        have hfloor := congrArg IntFractPair.b hReq
        simp only [IntFractPair.of] at hfloor
        change (P n).fr⁻¹ = (a : ℝ) + (P (n + 1)).fr
        rw [← hb, ← hfloor, ← hfr]
        ring
      refine ⟨a, by exact_mod_cast ha0, by exact_mod_cast ha4, ?_⟩
      rw [← hinv]
      simp
    have hfive : ∀ n, (1 : ℝ) / 5 ≤ f n := by
      intro n
      obtain ⟨a, ha, ha4, hr⟩ := hrec n
      rw [hr]
      apply one_div_le_one_div_of_le (by linarith [(hf (n + 1)).1])
      linarith [(hf (n + 1)).2]
    let R := Set.range f
    have hR : R.Nonempty := Set.range_nonempty f
    have hb : BddBelow R := ⟨0, fun _ ⟨n, hn⟩ => hn ▸ (hf n).1⟩
    have hu : BddAbove R := ⟨1, fun _ ⟨n, hn⟩ => hn ▸ (hf n).2.le⟩
    let l := sInf R
    let u := sSup R
    have hln (n : ℕ) : l ≤ f n := csInf_le hb ⟨n, rfl⟩
    have hnu (n : ℕ) : f n ≤ u := le_csSup hu ⟨n, rfl⟩
    have hl : (1 : ℝ) / 5 ≤ l := le_csInf hR (fun _ ⟨n, hn⟩ => hn ▸ hfive n)
    have hl0 : 0 < l := by linarith
    have hu0 : 0 < u := by linarith [hfive 0, hnu 0]
    have hlow : 1 / (4 + u) ≤ l := by
      apply le_csInf hR
      rintro _ ⟨n, rfl⟩
      obtain ⟨a, ha, ha4, hr⟩ := hrec n
      rw [hr]
      apply one_div_le_one_div_of_le (by linarith [(hf (n + 1)).1])
      linarith [hnu (n + 1)]
    have hupp : u ≤ 1 / (1 + l) := by
      apply csSup_le hR
      rintro _ ⟨n, rfl⟩
      obtain ⟨a, ha, ha4, hr⟩ := hrec n
      rw [hr]
      apply one_div_le_one_div_of_le (by linarith)
      linarith [hln (n + 1)]
    have hlprod : 1 ≤ l * (4 + u) := (div_le_iff₀ (by linarith)).mp hlow
    have huprod : u * (1 + l) ≤ 1 := (le_div_iff₀ (by linarith)).mp hupp
    have hlpoly : 1 ≤ 4 * l ^ 2 + 4 * l := by
      have hmul := mul_le_mul_of_nonneg_right hlprod (by linarith : 0 ≤ 1 + l)
      have hmul' := mul_le_mul_of_nonneg_left huprod hl0.le
      nlinarith
    have hmlow : m ≤ l := by
      by_contra h
      have hlt : l < m := lt_of_not_ge h
      have hsq : l ^ 2 < m ^ 2 := by nlinarith
      nlinarith
    have hMup : u ≤ M := by
      rw [hMrec]
      exact hupp.trans (one_div_le_one_div_of_le (by linarith) (by linarith))
    have hf0 : f 0 = x := by
      have hpair : P 0 = IntFractPair.of x :=
        Option.some.inj ((hP 0).symm.trans (IntFractPair.stream_zero x))
      have hfloor : ⌊x⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨hx0.le, hx1⟩
      simp [f, hpair, IntFractPair.of, Int.fract, hfloor]
    exact ⟨hf0 ▸ hmlow.trans (hln 0), hf0 ▸ (hnu 0).trans hMup⟩
  have him : Irrational m := by
    simpa [m] using
      (irrational_sqrt_two.sub_ratCast 1).div_ratCast (by norm_num : (2 : ℚ) ≠ 0)
  have hiM : Irrational M := by
    have hMm : M = (4 : ℚ) * m := by dsimp [m, M]; norm_num; ring
    rw [hMm]
    exact him.ratCast_mul (by norm_num)
  have hpairm : IntFractPair.of m⁻¹ = ⟨4, M⟩ := by
    have he : m⁻¹ = 4 + M := by rw [hmrec]; simp
    have hfloor : ⌊m⁻¹⌋ = (4 : ℤ) := by
      rw [he]
      exact Int.floor_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
    simp only [IntFractPair.of, Int.fract, hfloor, Int.cast_ofNat]
    rw [he]
    congr 1
    ring
  have hpairM : IntFractPair.of M⁻¹ = ⟨1, m⟩ := by
    have he : M⁻¹ = 1 + m := by rw [hMrec]; simp
    have hfloor : ⌊M⁻¹⌋ = (1 : ℤ) := by
      rw [he]
      exact Int.floor_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
    simp only [IntFractPair.of, Int.fract, hfloor, Int.cast_one]
    rw [he]
    congr 1
    ring
  have hperiodic : ∀ n,
      (∃ b : ℤ, IntFractPair.stream m n =
        some ⟨b, if n % 2 = 0 then m else M⟩) ∧
      (∃ b : ℤ, IntFractPair.stream M n =
        some ⟨b, if n % 2 = 0 then M else m⟩) := by
    intro n
    induction n with
    | zero =>
        constructor
        · refine ⟨0, ?_⟩
          have hfloor := Int.floor_eq_zero_iff.mpr ⟨hm.le, hml⟩
          simp [IntFractPair.stream_zero, IntFractPair.of, Int.fract, hfloor]
        · refine ⟨0, ?_⟩
          have hfloor := Int.floor_eq_zero_iff.mpr ⟨hM.le, hMl⟩
          simp [IntFractPair.stream_zero, IntFractPair.of, Int.fract, hfloor]
    | succ n ih =>
        obtain ⟨⟨b, hb⟩, ⟨c, hc⟩⟩ := ih
        by_cases hn : n % 2 = 0
        · have hn' : (n + 1) % 2 ≠ 0 := by omega
          simp only [if_pos hn] at hb hc
          constructor
          · refine ⟨4, ?_⟩
            rw [IntFractPair.stream_succ_of_some hb (ne_of_gt hm), hpairm]
            simp [hn']
          · refine ⟨1, ?_⟩
            rw [IntFractPair.stream_succ_of_some hc (ne_of_gt hM), hpairM]
            simp [hn']
        · have hn' : (n + 1) % 2 = 0 := by omega
          simp only [if_neg hn] at hb hc
          constructor
          · refine ⟨1, ?_⟩
            rw [IntFractPair.stream_succ_of_some hb (ne_of_gt hM), hpairM]
            simp [hn']
          · refine ⟨4, ?_⟩
            rw [IntFractPair.stream_succ_of_some hc (ne_of_gt hm), hpairm]
            simp [hn']
  have hdigit (x : ℝ)
      (hp : ∀ n, ∃ b : ℤ, IntFractPair.stream x n =
        some ⟨b, if n % 2 = 0 then m else M⟩ ∨
        IntFractPair.stream x n = some ⟨b, if n % 2 = 0 then M else m⟩) :
      ∀ n, ∃ a : ℕ, 0 < a ∧ a ≤ 4 ∧
        (GenContFract.of x).s.get? n = some ⟨1, (a : ℝ)⟩ := by
    intro n
    obtain ⟨b, hb | hb⟩ := hp n <;> by_cases hn : n % 2 = 0
    all_goals simp only [hn, ite_true, ite_false] at hb
    all_goals first
    | have h := IntFractPair.stream_succ_of_some hb (ne_of_gt hm)
      rw [hpairm] at h
      exact ⟨4, by norm_num, le_rfl,
        GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream h⟩
    | have h := IntFractPair.stream_succ_of_some hb (ne_of_gt hM)
      rw [hpairM] at h
      exact ⟨1, by norm_num, by norm_num,
        GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream h⟩
  exact ⟨hbounds, ⟨him, hm, hml, hdigit m (fun n => by
    obtain ⟨b, hb⟩ := (hperiodic n).1
    exact ⟨b, Or.inl hb⟩)⟩, ⟨hiM, hM, hMl, hdigit M (fun n => by
    obtain ⟨b, hb⟩ := (hperiodic n).2
    exact ⟨b, Or.inr hb⟩)⟩⟩

end D5.S1.Words.KAbelianLagrange
