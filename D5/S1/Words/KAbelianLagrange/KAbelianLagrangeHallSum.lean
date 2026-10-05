/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeHallSum
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeHallSum
   mirror-E: none(waiver:four-digit-hall-sum)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Four-digit continued fractions fill their hull sum and represent reals modulo one. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeHallTree
import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeHallNested
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

/-- Strictly separated children force independent level survivors to share their
ancestors. The compatible diagonal path identifies those survivors with actual C4
expansions. Greedy Hall splitting then fills the hull sum, whose length exceeds one. -/
theorem hall_cantor_sum :
    (∀ z ∈ Set.Icc (Real.sqrt 2 - 1) (4 * (Real.sqrt 2 - 1)),
      ∃ x ∈ hallCantor, ∃ y ∈ hallCantor, z = x + y) ∧
    (∀ t : ℝ, ∃ N : ℤ, ∃ x ∈ hallCantor, ∃ y ∈ hallCantor, t = N + x + y) := by
  classical
  obtain ⟨U, hrootLo, hrootHi, hbridge⟩ := hall_binary_interval_tree
  have hdecode (x : ℝ)
      (hx : ∀ n : ℕ, ∃ p : List Bool, p.length = n ∧ x ∈ Set.Icc (U.lo p) (U.hi p)) :
      x ∈ hallCantor := by
    choose p hlen hmem using hx
    have hunique : ∀ n : ℕ, ∀ r s : List Bool, r.length = n → s.length = n →
        x ∈ Set.Icc (U.lo r) (U.hi r) → x ∈ Set.Icc (U.lo s) (U.hi s) → r = s := by
      intro n
      induction n with
      | zero =>
          intro r s hr hs _ _
          have hr0 := List.length_eq_zero_iff.mp hr
          have hs0 := List.length_eq_zero_iff.mp hs
          rw [hr0, hs0]
      | succ n ih =>
          intro r s hr hs hxr hxs
          cases r with
          | nil => simp at hr
          | cons c r =>
            cases s with
            | nil => simp at hs
            | cons d s =>
              have hrn : r.length = n := by simpa using hr
              have hsn : s.length = n := by simpa using hs
              have hxr' : x ∈ Set.Icc (U.lo r) (U.hi r) :=
                ⟨(U.inside r c).1.trans hxr.1, hxr.2.trans (U.inside r c).2⟩
              have hxs' : x ∈ Set.Icc (U.lo s) (U.hi s) :=
                ⟨(U.inside s d).1.trans hxs.1, hxs.2.trans (U.inside s d).2⟩
              have hrs := ih r s hrn hsn hxr' hxs'
              subst s
              have hcd : c = d := by
                cases c <;> cases d
                · rfl
                · have := U.gap_pos r; linarith [hxr.2, hxs.1]
                · have := U.gap_pos r; linarith [hxr.1, hxs.2]
                · rfl
              rw [hcd]
    let b (n : ℕ) := (p (n + 1)).head!
    have hstep (n : ℕ) : p (n + 1) = b n :: p n := by
      have hn := hlen (n + 1)
      cases hp : p (n + 1) with
      | nil => simp [hp] at hn
      | cons c r =>
          have hr : r.length = n := by simpa [hp] using hn
          have hxr := hmem (n + 1)
          rw [hp] at hxr
          have hrmem : x ∈ Set.Icc (U.lo r) (U.hi r) :=
            ⟨(U.inside r c).1.trans hxr.1, hxr.2.trans (U.inside r c).2⟩
          have heq := hunique n r (p n) hr (hlen n) hrmem (hmem n)
          simp only [b, hp, List.head!_cons, heq]
    have hpath : ∀ n : ℕ, (List.ofFn (fun i : Fin n => b i)).reverse = p n := by
      intro n
      induction n with
      | zero => simpa using (List.length_eq_zero_iff.mp (hlen 0)).symm
      | succ n ih =>
          rw [List.ofFn_succ', List.concat_eq_append, List.reverse_concat]
          simpa only [Fin.val_castSucc, Fin.val_last, ih] using (hstep n).symm
    obtain ⟨y, hy, hd⟩ := hall_binary_branch_expansion b
    have hh : (GenContFract.of y).h = 0 := by
      rw [GenContFract.of_h_eq_floor]
      have hf : ⌊y⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨hy.2.1.le, hy.2.2.1⟩
      simp only [hf, Int.cast_zero]
    have hd' := fun n => (hd n).2.1
    have hnested := hall_binary_nested_cylinders b (GenContFract.of y) hh hd'
    obtain ⟨z, hz, _⟩ := hnested.2.2
    have hxm (n : ℕ) : x ∈
        GenContFract.compExactValue ((GenContFract.of y).contsAux
          (hallBinaryAddress b n).1.length)
          ((GenContFract.of y).conts (hallBinaryAddress b n).1.length) ''
            Set.Icc ((Real.sqrt 2 - 1) / 2)
              (1 / (((hallBinaryAddress b n).2.val + 1 : ℕ) +
                (Real.sqrt 2 - 1) / 2)) := by
      rw [← hbridge b n (GenContFract.of y) hh (hd' n), hpath]
      exact hmem n
    have hzx : z = x := by
      apply eq_of_abs_sub_nonpos
      by_contra h
      have hpos : 0 < |z - x| := lt_of_not_ge h
      obtain ⟨N, hN⟩ := hnested.2.1 |z - x| hpos
      exact (lt_irrefl _) (hN N le_rfl z (hz.1 N) x (hxm N))
    exact hzx ▸ hz.2
  have hcross : U.lo [true] - U.hi [false] ≤ U.hi [] - U.lo [] := by
    have hc := U.child_size [] false
    have hi := (U.inside [] false).2
    have hl := U.left []
    linarith
  have hsum : ∀ z ∈ Set.Icc (Real.sqrt 2 - 1) (4 * (Real.sqrt 2 - 1)),
      ∃ x ∈ hallCantor, ∃ y ∈ hallCantor, z = x + y := by
    intro z hz
    have hz' : z ∈ Set.Icc (U.lo [] + U.lo []) (U.hi [] + U.hi []) := by
      rw [hrootLo, hrootHi]
      constructor <;> linarith [hz.1, hz.2]
    obtain ⟨x, y, heq, hx, hy⟩ := hall_interval_splitting U U hcross hcross z hz'
    exact ⟨x, hdecode x hx, y, hdecode y hy, heq⟩
  refine ⟨hsum, ?_⟩
  intro t
  let N : ℤ := ⌊t - (Real.sqrt 2 - 1)⌋
  have hfloor : (N : ℝ) ≤ t - (Real.sqrt 2 - 1) := Int.floor_le _
  have hceil : t - (Real.sqrt 2 - 1) < (N : ℝ) + 1 := Int.lt_floor_add_one _
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hs4 : (4 : ℝ) / 3 < Real.sqrt 2 := by nlinarith
  have htarget : t - N ∈ Set.Icc (Real.sqrt 2 - 1) (4 * (Real.sqrt 2 - 1)) := by
    constructor <;> linarith
  obtain ⟨x, hx, y, hy, heq⟩ := hsum (t - N) htarget
  exact ⟨N, x, hx, y, hy, by linarith⟩

end D5.S1.Words.KAbelianLagrange
