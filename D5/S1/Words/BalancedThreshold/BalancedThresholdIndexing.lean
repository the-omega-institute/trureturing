/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdIndexing
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdIndexing
   mirror-E: none(waiver:unimodular-bracket-euclidean-classification)
   anchors: [mathlib/module/Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat]
   utility: none
   digest: Euclidean descent identifies every unimodular bracket with computed continuants. -/

import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import D5.S1.Words.BalancedThreshold.BalancedThresholdExpansion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold

open GenContFract

/-- Every nonnegative unimodular bracket of an irrational ratio is a consecutive
convergent/semiconvergent pair. The predecessor at index zero is `(1,0)`.
Digit subtraction strictly decreases the sum of the integral coordinates. -/
theorem unimodular_bracket_continuants {theta : ℝ} (h0 : 0 < theta) (h1 : theta < 1)
    (hirr : Irrational theta) (p q r s : ℕ)
    (hdet : p * s + 1 = r * q ∨ r * q + 1 = p * s)
    (hbr : ((p : ℝ) - theta * q) * ((r : ℝ) - theta * s) < 0) :
    let g := GenContFract.of theta
    ∃ N m : ℕ, ∃ c : ℤ, g.s.get? N = some ⟨1, (c : ℝ)⟩ ∧ (m : ℤ) < c ∧
      let v := g.contsAux (N + 1)
      let w := g.contsAux N
      let z : Pair ℝ := ⟨(m : ℝ) * v.a + w.a, (m : ℝ) * v.b + w.b⟩
      (⟨(p : ℝ), (q : ℝ)⟩ = v ∧ ⟨(r : ℝ), (s : ℝ)⟩ = z) ∨
      (⟨(r : ℝ), (s : ℝ)⟩ = v ∧ ⟨(p : ℝ), (q : ℝ)⟩ = z) := by
  classical
  let C := fun (x : ℝ) (p q r s : ℕ) =>
    let g := GenContFract.of x
    ∃ N m : ℕ, ∃ c : ℤ, g.s.get? N = some ⟨1, (c : ℝ)⟩ ∧ (m : ℤ) ≤ c ∧
      let v := g.contsAux (N + 1)
      let w := g.contsAux N
      let z : Pair ℝ := ⟨(m : ℝ) * v.a + w.a, (m : ℝ) * v.b + w.b⟩
      (⟨(p : ℝ), (q : ℝ)⟩ = v ∧ ⟨(r : ℝ), (s : ℝ)⟩ = z) ∨
      (⟨(r : ℝ), (s : ℝ)⟩ = v ∧ ⟨(p : ℝ), (q : ℝ)⟩ = z)
  have classify : ∀ (size : ℕ) (x : ℝ) (p q r s : ℕ), p + q + r + s = size →
      0 < x → x < 1 → Irrational x →
      (p * s + 1 = r * q ∨ r * q + 1 = p * s) →
      ((p : ℝ) - x * q) * ((r : ℝ) - x * s) < 0 → C x p q r s := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro x p q r s hsize hx0 hx1 hxi hd hb
      let c := ⌊x⁻¹⌋.toNat
      let y := Int.fract x⁻¹
      let g := GenContFract.of x
      let f := GenContFract.of y
      have hinv : 1 < x⁻¹ := (one_lt_inv₀ hx0).mpr hx1
      have hcI : (1 : ℤ) ≤ ⌊x⁻¹⌋ := Int.le_floor.mpr (by simpa using hinv.le)
      have hcpos : 0 < c := by dsimp [c]; omega
      have hcast : (c : ℝ) = (⌊x⁻¹⌋ : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ ⌊x⁻¹⌋)
      have hyirr : Irrational y := hxi.inv.sub_intCast _
      have hy0 : 0 < y := Int.fract_pos.mpr (hxi.inv.ne_int _)
      have hy1 : y < 1 := Int.fract_lt_one _
      have hxy : x⁻¹ = (c : ℝ) + y := by
        change x⁻¹ = (c : ℝ) + (x⁻¹ - (⌊x⁻¹⌋ : ℝ))
        rw [hcast]
        ring
      have hcx : (c : ℝ) * x < 1 := by
        have he := mul_pos hy0 hx0
        have hxne := hx0.ne'
        have hi : ((c : ℝ) + y) * x = 1 := by
          rw [← hxy, inv_mul_cancel₀ hxne]
        nlinarith only [hi, he]
      have hfloor : ⌊x⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hx0.le, hx1⟩
      have hfract : Int.fract x = x := by simp [Int.fract, hfloor]
      have hhead : g.s.get? 0 = some ⟨1, (c : ℝ)⟩ := by
        simpa only [g, Stream'.Seq.head, hfract, ← hcast] using
          GenContFract.of_s_head (v := x) (by rw [hfract]; exact hx0.ne')
      have zero_case : ∀ a b d : ℕ,
          (0 * d + 1 = b * a ∨ b * a + 1 = 0 * d) →
          ((0 : ℝ) - x * a) * ((b : ℝ) - x * d) < 0 → C x 0 a b d := by
        intro a b d hdet hbr
        have hab : b * a = 1 := by
          rcases hdet with h | h
          · simpa only [Nat.zero_mul, Nat.zero_add] using h.symm
          · simp at h
        have ha : a = 1 := (mul_eq_one.mp hab).2
        have hb : b = 1 := (mul_eq_one.mp hab).1
        subst a
        subst b
        norm_num only [Nat.cast_one, zero_sub, mul_one] at hbr
        have hupper : (d : ℝ) < x⁻¹ := by
          have hpos : 0 < 1 - x * d :=
            (pos_of_mul_neg_right hbr (neg_nonpos.mpr hx0.le))
          have hi : x⁻¹ * x = 1 := inv_mul_cancel₀ hx0.ne'
          exact (mul_lt_mul_iff_left₀ hx0).mp (by nlinarith only [hpos, hi])
        have hdc : d ≤ c := by
          have hi : (d : ℤ) ≤ ⌊x⁻¹⌋ := Int.le_floor.mpr hupper.le
          dsimp [c]
          omega
        refine ⟨0, d, (c : ℤ), hhead, by exact_mod_cast hdc, Or.inl ?_⟩
        constructor
        · simp [GenContFract.contsAux, GenContFract.of_h_eq_floor, hfloor]
        · simp [GenContFract.contsAux, GenContFract.of_h_eq_floor, hfloor]
      by_cases hp : p = 0
      · subst p
        exact zero_case q r s hd (by simpa only [Nat.cast_zero] using hb)
      by_cases hr : r = 0
      · subst r
        have he := zero_case s p q (by simpa [or_comm] using hd)
          (by simpa only [mul_comm, Nat.cast_zero] using hb)
        obtain ⟨N, m, d, hdigit, hm, hpair⟩ := he
        exact ⟨N, m, d, hdigit, hm, hpair.symm⟩
      have hp0 : 0 < p := by omega
      have hr0 : 0 < r := by omega
      have bounds : ∀ a b d e : ℕ, 0 < a → 0 < d →
          (a * e + 1 = d * b ∨ d * b + 1 = a * e) →
          ((a : ℝ) - x * b) * ((d : ℝ) - x * e) < 0 → c * a ≤ b := by
        intro a b d e ha hd hdet hbr
        by_contra hn
        have hbc : b + 1 ≤ c * a := by omega
        have hac : x * b < (a : ℝ) := by
          have hbR : (b : ℝ) < (c : ℝ) * a := by exact_mod_cast (by omega : b < c * a)
          have hmul := mul_lt_mul_of_pos_left hbR hx0
          have hmul' := mul_lt_mul_of_pos_right hcx (by exact_mod_cast ha : (0 : ℝ) < a)
          nlinarith only [hmul, hmul']
        have hde : (d : ℝ) < x * e := by nlinarith only [hbr, hac]
        have hec : c * d + 1 ≤ e := by
          by_contra hne
          have heR : (e : ℝ) ≤ (c : ℝ) * d := by
            exact_mod_cast (by omega : e ≤ c * d)
          have hmul := mul_le_mul_of_nonneg_left heR hx0.le
          have hmul' := mul_lt_mul_of_pos_right hcx (by exact_mod_cast hd : (0 : ℝ) < d)
          nlinarith only [hmul, hmul', hde]
        have hbmul := Nat.mul_le_mul_left d hbc
        have hemul := Nat.mul_le_mul_left a hec
        rcases hdet with h | h <;> nlinarith only [hbmul, hemul, h, ha, hd]
      have hq : c * p ≤ q := bounds p q r s hp0 hr0 hd hb
      have hs : c * r ≤ s := bounds r s p q hr0 hp0
        (by simpa only [or_comm] using hd) (by simpa only [mul_comm, Nat.cast_zero] using hb)
      let P := q - c * p
      let R := s - c * r
      have hP : P + c * p = q := Nat.sub_add_cancel hq
      have hR : R + c * r = s := Nat.sub_add_cancel hs
      have hsmall : P + p + R + r < size := by
        have hmulp := Nat.le_mul_of_pos_left p hcpos
        have hmulr := Nat.le_mul_of_pos_left r hcpos
        omega
      have hdet' : P * r + 1 = R * p ∨ R * p + 1 = P * r := by
        rcases hd with h | h
        · right
          nlinarith only [h, hP, hR]
        · left
          nlinarith only [h, hP, hR]
      have error : ∀ a b d : ℕ, d + c * a = b →
          (d : ℝ) - y * a = -((a : ℝ) - x * b) / x := by
        intro a b d he
        have heR : (d : ℝ) + (c : ℝ) * a = b := by exact_mod_cast he
        apply (eq_div_iff hx0.ne').mpr
        have hi : x⁻¹ * x = 1 := inv_mul_cancel₀ hx0.ne'
        have hix : (c : ℝ) * x + y * x = 1 := by
          calc
            (c : ℝ) * x + y * x = ((c : ℝ) + y) * x := by ring
            _ = 1 := by rw [← hxy, hi]
        have ha := congrArg (fun v : ℝ => v * a) hix
        have heb := congrArg (fun v : ℝ => v * x) heR
        nlinarith only [heb, ha]
      have hbr' : ((P : ℝ) - y * p) * ((R : ℝ) - y * r) < 0 := by
        rw [error p q P hP, error r s R hR, div_mul_div_comm]
        exact div_neg_of_neg_of_pos (by nlinarith only [hb]) (mul_pos hx0 hx0)
      obtain ⟨N, m, d, hdigit, hm, hpair⟩ :=
        ih (P + p + R + r) hsmall y P p R r rfl hy0 hy1 hyirr hdet' hbr'
      have hyfract : Int.fract y = y := by
        rw [Int.fract, Int.floor_eq_zero_iff.mpr ⟨hy0.le, hy1⟩]
        simp only [Int.cast_zero, sub_zero]
      have tails : ∀ n, g.s.get? (n + 1) = f.s.get? n := by
        intro n
        rw [GenContFract.of_s_succ, hfract]
        cases n with
        | zero =>
          have hxfract : Int.fract x⁻¹ = y := rfl
          change (GenContFract.of x⁻¹).s.head = (GenContFract.of y).s.head
          rw [GenContFract.of_s_head (v := x⁻¹) hy0.ne',
            GenContFract.of_s_head (v := y) (by rw [hyfract]; exact hy0.ne')]
          rw [hxfract, hyfract]
        | succ n =>
          rw [GenContFract.of_s_succ, GenContFract.of_s_succ]
          rw [show Int.fract x⁻¹ = y from rfl, hyfract]
      let lift : Pair ℝ → Pair ℝ := fun v => ⟨v.b, v.a + (c : ℝ) * v.b⟩
      have hlift : ∀ n, g.contsAux (n + 1) = lift (f.contsAux n) := by
        intro n
        induction n using Nat.twoStepInduction with
        | zero => simp [g, lift, GenContFract.contsAux,
            GenContFract.of_h_eq_floor, hfloor]
        | one =>
          have hyfloor : ⌊y⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hy0.le, hy1⟩
          simp [GenContFract.contsAux, hhead, lift, g, f,
            GenContFract.of_h_eq_floor, hfloor, hyfloor, nextConts, nextNum, nextDen]
        | more n hn hn1 =>
          cases hd : f.s.get? n with
          | none =>
            have hg := (tails n).trans hd
            simp only [GenContFract.contsAux, hg, hd]
            exact hn1
          | some v =>
            have hg := (tails n).trans hd
            rw [GenContFract.contsAux_recurrence hg rfl rfl,
              GenContFract.contsAux_recurrence hd rfl rfl, hn, hn1]
            dsimp [lift]
            congr 1
            ring
      have hlP : lift ⟨(P : ℝ), (p : ℝ)⟩ = ⟨(p : ℝ), (q : ℝ)⟩ := by
        dsimp [lift]
        congr 1
        exact_mod_cast hP
      have hlR : lift ⟨(R : ℝ), (r : ℝ)⟩ = ⟨(r : ℝ), (s : ℝ)⟩ := by
        dsimp [lift]
        congr 1
        exact_mod_cast hR
      have linear : ∀ v w : Pair ℝ,
          lift ⟨(m : ℝ) * v.a + w.a, (m : ℝ) * v.b + w.b⟩ =
          ⟨(m : ℝ) * (lift v).a + (lift w).a,
            (m : ℝ) * (lift v).b + (lift w).b⟩ := by
        intro v w
        dsimp [lift]
        congr 1
        ring
      refine ⟨N + 1, m, d, (tails N).trans hdigit, hm, ?_⟩
      change (_ ∧ _) ∨ (_ ∧ _)
      rw [hlift (N + 1), hlift N]
      rcases hpair with ⟨hv, hw⟩ | ⟨hv, hw⟩
      · left
        constructor
        · rw [← hv, hlP]
        · rw [← linear, ← hw, hlR]
      · right
        constructor
        · rw [← hv, hlR]
        · rw [← linear, ← hw, hlP]
  obtain ⟨N, m, c, hdigit, hm, hpair⟩ :=
    classify (p + q + r + s) theta p q r s rfl h0 h1 hirr hdet hbr
  dsimp only
  by_cases hmc : (m : ℤ) < c
  · exact ⟨N, m, c, hdigit, hmc, hpair⟩
  have heq : (m : ℤ) = c := by omega
  let g := GenContFract.of theta
  have hnext : ∃ d : ℤ, g.s.get? (N + 1) = some ⟨1, (d : ℝ)⟩ ∧ 0 < d := by
    have hnot : ¬g.TerminatedAt (N + 1) := by
      intro hterm
      obtain ⟨v, hv⟩ := (GenContFract.terminates_iff_rat theta).mp ⟨N + 1, hterm⟩
      exact hirr.ne_rat v hv
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hnot
    obtain ⟨ha, d, hd⟩ := GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hv
    refine ⟨d, hv.trans (congrArg some (by cases v; simp_all)), ?_⟩
    have hpos := GenContFract.of_one_le_get?_partDen (GenContFract.partDen_eq_s_b hv)
    rw [hd] at hpos
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hpos)
  obtain ⟨d, hd, hdpos⟩ := hnext
  have hrec := GenContFract.contsAux_recurrence hdigit rfl rfl
  have hmR : (m : ℝ) = (c : ℝ) := by exact_mod_cast heq
  refine ⟨N + 1, 0, d, hd, by simpa using hdpos, ?_⟩
  have he : g.contsAux (N + 2) =
      ⟨(m : ℝ) * (g.contsAux (N + 1)).a + (g.contsAux N).a,
        (m : ℝ) * (g.contsAux (N + 1)).b + (g.contsAux N).b⟩ := by
    simpa only [hmR, one_mul] using hrec
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rcases hpair with ⟨hv, hw⟩ | ⟨hv, hw⟩
  · exact Or.inr ⟨hw.trans he.symm, hv⟩
  · exact Or.inl ⟨hw.trans he.symm, hv⟩

end D5.S1.Words.BalancedThreshold
