/- GID: D5/S1/Words/ReturnWords/GoldenArcFirstReturn
   generality: I
   mirror-B: none(waiver:formal-kernel-first-return-spectrum)
   mirror-E: none(waiver:kernel-symbolic-rotation-first-return)
   anchors: []
   digest: Golden rotation-gap arcs have exactly two positive first-return times. -/

import D5.S1.Words.ReturnWords.GoldenArcFirstReturnCore
import D5.S1.Words.ReturnWords.GoldenGapFirstReturn
import D5.S1.Words.ReturnWords.GoldenRankArcs

namespace D5.S1.Words

open Set
open GoldenArcFirstReturnInternal

private theorem backward_sub_eq_add_forward (alpha : Real) {u k : Nat} (hku : k ≤ u)
    (hsum : backwardDisplacement alpha u + forwardDisplacement alpha k < 1) :
    backwardDisplacement alpha (u - k) =
      backwardDisplacement alpha u + forwardDisplacement alpha k := by
  rw [backwardDisplacement, forwardDisplacement, Int.fract_eq_iff]
  constructor
  · exact add_nonneg (Int.fract_nonneg _) (Int.fract_nonneg _)
  constructor
  · exact hsum
  · refine ⟨⌊(u : Real) * (-alpha)⌋ + ⌊(k : Real) * alpha⌋, ?_⟩
    rw [Int.cast_add]
    calc
      ((u - k : Nat) : Real) * (-alpha) -
          (Int.fract ((u : Real) * (-alpha)) + Int.fract ((k : Real) * alpha)) =
          ((u : Real) * (-alpha) - Int.fract ((u : Real) * (-alpha))) +
            ((k : Real) * alpha - Int.fract ((k : Real) * alpha)) := by
              rw [Nat.cast_sub hku]
              ring
      _ = (↑⌊(u : Real) * (-alpha)⌋ : Real) + ↑⌊(k : Real) * alpha⌋ := by
        rw [Int.self_sub_fract, Int.self_sub_fract]

private theorem backward_add_eq_add_backward (alpha : Real) (u k : Nat)
    (hsum : backwardDisplacement alpha u + backwardDisplacement alpha k < 1) :
    backwardDisplacement alpha (u + k) =
      backwardDisplacement alpha u + backwardDisplacement alpha k := by
  rw [backwardDisplacement, Int.fract_eq_iff]
  constructor
  · exact add_nonneg (Int.fract_nonneg _) (Int.fract_nonneg _)
  constructor
  · exact hsum
  · refine ⟨⌊(u : Real) * (-alpha)⌋ + ⌊(k : Real) * (-alpha)⌋, ?_⟩
    rw [Int.cast_add]
    calc
      ((u + k : Nat) : Real) * (-alpha) -
          (Int.fract ((u : Real) * (-alpha)) + Int.fract ((k : Real) * (-alpha))) =
          ((u : Real) * (-alpha) - Int.fract ((u : Real) * (-alpha))) +
            ((k : Real) * (-alpha) - Int.fract ((k : Real) * (-alpha))) := by
              push_cast
              ring
      _ = (↑⌊(u : Real) * (-alpha)⌋ : Real) + ↑⌊(k : Real) * (-alpha)⌋ := by
        rw [Int.self_sub_fract, Int.self_sub_fract]

private theorem no_rotation_cut_between (alpha : Real) (N : Nat)
    [Fact (Irrational alpha)] [NeZero N] (r : Fin N) {x : Real}
    (hxcut : x ∈ rotationCutSet alpha N) :
    x ∉ Ioo (rotationCut alpha N r.castSucc) (rotationCut alpha N r.succ) := by
  intro hx
  have hxrange : x ∈ Set.range (rotationCut alpha N) := by
    unfold rotationCut
    rw [Finset.range_orderEmbOfFin]
    exact hxcut
  obtain ⟨j, rfl⟩ := hxrange
  have hlo : r.castSucc < j := (rotationCut alpha N).lt_iff_lt.mp hx.1
  have hhi : j < r.succ := (rotationCut alpha N).lt_iff_lt.mp hx.2
  change r.val < j.val at hlo
  change j.val < r.val + 1 at hhi
  omega

private theorem rotation_cut_orbit_index (alpha : Real) (N : Nat)
    [Fact (Irrational alpha)] [NeZero N] {j : Fin (N + 1)} (hj : j < Fin.last N) :
    ∃ u < N, rotationCut alpha N j = backwardDisplacement alpha u := by
  have hjlt : rotationCut alpha N j < 1 := by
    calc
      rotationCut alpha N j < rotationCut alpha N (Fin.last N) :=
        (rotationCut alpha N).strictMono hj
      _ = 1 := rotation_cut_last alpha N
  have hjmem : rotationCut alpha N j ∈ rotationCutSet alpha N := by
    exact Finset.orderEmbOfFin_mem _ _ _
  rw [rotationCutSet, Finset.mem_insert] at hjmem
  rcases hjmem with hone | horbit
  · rw [hone] at hjlt
    exact (lt_irrefl (1 : Real) hjlt).elim
  · rw [D5.S1.Recurrence.RotationOrbitGapsPartition.rotationOrbit,
      Finset.mem_image] at horbit
    obtain ⟨u, hu, heq⟩ := horbit
    exact ⟨u, Finset.mem_range.mp hu, by simpa [backwardDisplacement] using heq.symm⟩

private theorem backward_displacement_mem_cut_set (alpha : Real) (N k : Nat) (hk : k < N) :
    backwardDisplacement alpha k ∈ rotationCutSet alpha N := by
  rw [rotationCutSet, Finset.mem_insert]
  right
  rw [D5.S1.Recurrence.RotationOrbitGapsPartition.rotationOrbit, Finset.mem_image]
  exact ⟨k, Finset.mem_range.mpr hk, by rfl⟩

private theorem rotation_gap_best_displacement (alpha : Real) (N : Nat)
    [Fact (Irrational alpha)] [NeZero N] (hN : 1 < N) (r : Fin N) :
    let a := rotationCut alpha N r.castSucc
    let ell := rotationCut alpha N r.succ - a
    ∃ d : Nat, 0 < d ∧
      ((ell = forwardDisplacement alpha d ∧
          ∀ k, 0 < k → k < d → ell ≤ forwardDisplacement alpha k) ∨
        (ell = backwardDisplacement alpha d ∧
          ∀ k, 0 < k → k < d → ell ≤ backwardDisplacement alpha k)) := by
  dsimp only
  let a := rotationCut alpha N r.castSucc
  let b := rotationCut alpha N r.succ
  have hab : a < b := (rotationCut alpha N).strictMono r.castSucc_lt_succ
  have ha0 : 0 ≤ a := by
    calc
      0 = rotationCut alpha N 0 := (rotation_cut_zero alpha N).symm
      _ ≤ a := (rotationCut alpha N).monotone (by simp)
  have hb1 : b ≤ 1 := by
    calc
      b ≤ rotationCut alpha N (Fin.last N) :=
        (rotationCut alpha N).monotone (Fin.le_last _)
      _ = 1 := rotation_cut_last alpha N
  have hleftlt : r.castSucc < Fin.last N := by
    apply Fin.mk_lt_mk.mpr
    exact r.isLt
  obtain ⟨u, huN, hleft⟩ := rotation_cut_orbit_index alpha N hleftlt
  have haleft : a = backwardDisplacement alpha u := by
    dsimp [a]
    exact hleft
  by_cases hrightLast : r.succ = Fin.last N
  · have hbright : b = 1 := by
      dsimp [b]
      rw [hrightLast, rotation_cut_last]
    have hupos : 0 < u := by
      by_contra hu
      have hu0 : u = 0 := Nat.eq_zero_of_not_pos hu
      have hpoint0 : backwardDisplacement alpha 1 ∈ Ioo a b := by
        have hbackpos := backward_displacement_pos (alpha := alpha) Fact.out
          (by omega : 0 < (1 : Nat))
        have hbacklt := backward_displacement_lt_one alpha 1
        rw [haleft, hu0, backwardDisplacement]
        norm_num
        rw [hbright]
        exact ⟨hbackpos, hbacklt⟩
      exact no_rotation_cut_between alpha N r
        (backward_displacement_mem_cut_set alpha N 1 hN) hpoint0
    refine ⟨u, hupos, Or.inl ⟨?_, ?_⟩⟩
    · change b - a = forwardDisplacement alpha u
      have hback := backward_displacement_eq_one_sub_forward (alpha := alpha) Fact.out hupos
      dsimp [a]
      rw [hleft]
      linarith
    · intro k hkpos hku
      by_contra hsmall
      have hsmall' : forwardDisplacement alpha k < b - a := lt_of_not_ge hsmall
      have hsum : backwardDisplacement alpha u + forwardDisplacement alpha k < 1 := by
        linarith [hleft, hbright]
      have hpoint : backwardDisplacement alpha (u - k) ∈ Ioo a b := by
        rw [backward_sub_eq_add_forward alpha (Nat.le_of_lt hku) hsum, ← hleft]
        constructor <;> linarith [forward_displacement_pos (alpha := alpha) Fact.out hkpos]
      apply no_rotation_cut_between alpha N r
        (backward_displacement_mem_cut_set alpha N (u - k) (by omega)) hpoint
  · have hrightlt : r.succ < Fin.last N :=
      lt_of_le_of_ne (Fin.le_last _) hrightLast
    obtain ⟨v, hvN, hright⟩ := rotation_cut_orbit_index alpha N hrightlt
    have hbrightIndex : b = backwardDisplacement alpha v := by
      dsimp [b]
      exact hright
    have huv : u ≠ v := by
      intro huv
      subst v
      have : a = b := by
        dsimp [a, b]
        exact hleft.trans hright.symm
      linarith
    rcases lt_or_gt_of_ne huv with huvlt | hvult
    · let d := v - u
      have hdpos : 0 < d := by dsimp [d]; omega
      have hdiff := forward_displacement_sub (alpha := -alpha) huvlt (by
        change backwardDisplacement alpha u < backwardDisplacement alpha v
        linarith [hab, hleft, hright])
      refine ⟨d, hdpos, Or.inr ⟨?_, ?_⟩⟩
      · change b - a = backwardDisplacement alpha d
        change b - a = forwardDisplacement (-alpha) d
        dsimp [d]
        rw [hdiff]
        change b - a = backwardDisplacement alpha v - backwardDisplacement alpha u
        linarith [hleft, hright]
      · intro k hkpos hkd
        by_contra hsmall
        have hsmall' : backwardDisplacement alpha k < b - a := lt_of_not_ge hsmall
        have hukv : u + k < v := by dsimp [d] at hkd; omega
        have hsum : backwardDisplacement alpha u + backwardDisplacement alpha k < 1 := by
          rw [← hleft]
          exact (by linarith [hsmall', hb1])
        have hpoint : backwardDisplacement alpha (u + k) ∈ Ioo a b := by
          rw [backward_add_eq_add_backward alpha u k hsum, ← hleft]
          constructor <;> linarith [backward_displacement_pos (alpha := alpha) Fact.out hkpos]
        apply no_rotation_cut_between alpha N r
          (backward_displacement_mem_cut_set alpha N (u + k) (by omega)) hpoint
    · let d := u - v
      have hdpos : 0 < d := by dsimp [d]; omega
      have hvpos : 0 < v := by
        by_contra hv
        have hv0 : v = 0 := Nat.eq_zero_of_not_pos hv
        subst v
        have hb0 : b = 0 := by
          dsimp [b]
          rw [hright, backwardDisplacement]
          norm_num
        linarith
      have hupos : 0 < u := hvpos.trans hvult
      have hdiff := forward_displacement_sub (alpha := alpha) hvult (by
        have hvback := backward_displacement_eq_one_sub_forward (alpha := alpha)
          Fact.out hvpos
        have huback := backward_displacement_eq_one_sub_forward (alpha := alpha)
          Fact.out hupos
        calc
          forwardDisplacement alpha v = 1 - backwardDisplacement alpha v := by
            linarith
          _ < 1 - backwardDisplacement alpha u := by
            linarith [hab, haleft, hbrightIndex]
          _ = forwardDisplacement alpha u := by linarith)
      refine ⟨d, hdpos, Or.inl ⟨?_, ?_⟩⟩
      · change b - a = forwardDisplacement alpha d
        dsimp [d]
        rw [hdiff]
        have hvback := backward_displacement_eq_one_sub_forward (alpha := alpha)
          Fact.out hvpos
        have huback := backward_displacement_eq_one_sub_forward (alpha := alpha)
          Fact.out hupos
        linarith [haleft, hbrightIndex, hvback, huback]
      · intro k hkpos hkd
        by_contra hsmall
        have hsmall' : forwardDisplacement alpha k < b - a := lt_of_not_ge hsmall
        have hvuk : v < u - k := by dsimp [d] at hkd; omega
        have hsum : backwardDisplacement alpha u + forwardDisplacement alpha k < 1 := by
          rw [← hleft]
          exact (by linarith [hsmall', hb1])
        have hpoint : backwardDisplacement alpha (u - k) ∈ Ioo a b := by
          rw [backward_sub_eq_add_forward alpha (by omega) hsum, ← hleft]
          constructor <;> linarith [forward_displacement_pos (alpha := alpha) Fact.out hkpos]
        apply no_rotation_cut_between alpha N r
          (backward_displacement_mem_cut_set alpha N (u - k) (by omega)) hpoint

/-- Positive first-return times of the natural golden phase orbit to a rotation gap arc. -/
def goldenArcFirstReturnGapSet (n : Nat) (r : Fin (n + 1)) : Set Nat :=
  {d | 0 < d ∧ ∃ i,
    goldenPhase i ∈ rotationGapArc goldenMechanicalSlope (n + 1) r ∧
    goldenPhase (i + d) ∈ rotationGapArc goldenMechanicalSlope (n + 1) r ∧
    ∀ e, 0 < e → e < d →
      goldenPhase (i + e) ∉ rotationGapArc goldenMechanicalSlope (n + 1) r}

/-- Arc first returns and cylinder-rank first returns are the same set. -/
theorem golden_arc_first_return_gap_set_eq_rank_first_return_gap_set
    (n : Nat) (r : Fin (n + 1)) :
    goldenArcFirstReturnGapSet n r = goldenRankFirstReturnGapSet n r.val := by
  ext d
  constructor
  · rintro ⟨hd, i, hstart, hreturn, hfirst⟩
    refine ⟨hd, i, (golden_cylinder_rank_iff_mem_rotation_gap_arc n i r).mpr hstart,
      (golden_cylinder_rank_iff_mem_rotation_gap_arc n (i + d) r).mpr hreturn, ?_⟩
    intro e hepos helt hrank
    exact hfirst e hepos helt
      ((golden_cylinder_rank_iff_mem_rotation_gap_arc n (i + e) r).mp hrank)
  · rintro ⟨hd, i, hstart, hreturn, hfirst⟩
    refine ⟨hd, i, (golden_cylinder_rank_iff_mem_rotation_gap_arc n i r).mp hstart,
      (golden_cylinder_rank_iff_mem_rotation_gap_arc n (i + d) r).mp hreturn, ?_⟩
    intro e hepos helt harc
    exact hfirst e hepos helt
      ((golden_cylinder_rank_iff_mem_rotation_gap_arc n (i + e) r).mpr harc)

/-- Every positive-length golden rotation-gap arc has exactly two first-return times. -/
theorem golden_arc_first_return_gap_set_encard_eq_two
    (n : Nat) (hn : 0 < n) (r : Fin (n + 1)) :
    (goldenArcFirstReturnGapSet n r).encard = 2 := by
  let alpha := goldenMechanicalSlope
  let N := n + 1
  let a := rotationCut alpha N r.castSucc
  let b := rotationCut alpha N r.succ
  let ell := b - a
  have halpha : Irrational alpha := golden_mechanical_slope_irrational
  have hN : 1 < N := by dsimp [N]; omega
  have ha0 : 0 ≤ a := by
    calc
      0 = rotationCut alpha N 0 := (rotation_cut_zero alpha N).symm
      _ ≤ a := (rotationCut alpha N).monotone (by simp)
  have hb1 : b ≤ 1 := by
    calc
      b ≤ rotationCut alpha N (Fin.last N) :=
        (rotationCut alpha N).monotone (Fin.le_last _)
      _ = 1 := rotation_cut_last alpha N
  have hellpos : 0 < ell := by
    dsimp [ell, b, a, alpha, N]
    exact rotation_gap_arc_pos goldenMechanicalSlope (n + 1) r
  have hellone : ell < 1 := by
    by_cases hr0 : r.val = 0
    · have hrsucc : r.succ < Fin.last N := by
        apply Fin.mk_lt_mk.mpr
        dsimp [N]
        omega
      have hb_lt : b < 1 := by
        calc
          b < rotationCut alpha N (Fin.last N) :=
            (rotationCut alpha N).strictMono hrsucc
          _ = 1 := rotation_cut_last alpha N
      linarith
    · have hzero : (0 : Fin (N + 1)) < r.castSucc := by
        apply Fin.mk_lt_mk.mpr
        simpa using Nat.pos_of_ne_zero hr0
      have ha_pos : 0 < a := by
        calc
          0 = rotationCut alpha N 0 := (rotation_cut_zero alpha N).symm
          _ < a := (rotationCut alpha N).strictMono hzero
      linarith
  have hend : a + ell ≤ 1 := by dsimp [ell]; linarith
  obtain ⟨d, hdpos, hbest⟩ := rotation_gap_best_displacement alpha N hN r
  have hpExists :
      ∃ k : Nat, 0 < k ∧ forwardDisplacement alpha k < ell := by
    simpa [forwardDisplacement] using
      exists_positive_fract_lt halpha hellpos hellone.le
  let p := Nat.find hpExists
  have hpSpec : 0 < p ∧ forwardDisplacement alpha p < ell := by
    exact Nat.find_spec hpExists
  have hpfirst : ∀ k, 0 < k → forwardDisplacement alpha k < ell → p ≤ k := by
    intro k hk hlt
    exact Nat.find_min' hpExists ⟨hk, hlt⟩
  have hqExists :
      ∃ k : Nat, 0 < k ∧ backwardDisplacement alpha k < ell := by
    simpa [backwardDisplacement] using
      exists_positive_fract_lt halpha.neg hellpos hellone.le
  let q := Nat.find hqExists
  have hqSpec : 0 < q ∧ backwardDisplacement alpha q < ell := by
    exact Nat.find_spec hqExists
  have hqfirst : ∀ k, 0 < k → backwardDisplacement alpha k < ell → q ≤ k := by
    intro k hk hlt
    exact Nat.find_min' hqExists ⟨hk, hlt⟩
  have hsum : ell = forwardDisplacement alpha p + backwardDisplacement alpha q :=
    minimal_displacements_sum_of_best halpha hellpos hdpos hpSpec.1 hpSpec.2 hpfirst
      hqSpec.1 hqSpec.2 hqfirst hbest
  have hpair := orbit_arc_first_return_eq_pair halpha ha0 hellpos hellone hend
    hpSpec.1 hpSpec.2 hpfirst hqSpec.1 hqSpec.2 hqfirst hsum
  have hendpoint : a + ell = b := by dsimp [ell]; ring
  have hsets : goldenArcFirstReturnGapSet n r = orbitArcFirstReturnGapSet alpha a ell := by
    ext gap
    simp only [goldenArcFirstReturnGapSet, orbitArcFirstReturnGapSet, Set.mem_setOf_eq,
      rotationGapArc]
    rw [hendpoint]
    rfl
  have hpq : p ≠ q := by
    intro hpq
    rw [← hpq] at hsum
    have hback := backward_displacement_eq_one_sub_forward halpha hpSpec.1
    linarith [hsum, hellone]
  rw [hsets, hpair]
  exact Set.encard_pair hpq

/-- Every occurring positive-length golden factor has exactly two adjacent-gap values. -/
theorem golden_occurrence_gap_set_encard_eq_two {n i : Nat} (hn : 0 < n)
    {w : List Bool} (hw : goldenFactor n i = w) :
    (goldenOccurrenceGapSet n w).encard = 2 := by
  rw [golden_occurrence_gap_set_eq_rank_first_return_gap_set hw]
  let r : Fin (n + 1) := ⟨goldenCylinderRank n i, by
    apply Nat.lt_succ_iff.mpr
    change
      (((Finset.range n).image fun m : Nat =>
        1 - Int.fract (((m + 1 : Nat) : Real) * goldenMechanicalSlope)).filter
          (fun x => x ≤ goldenPhase i)).card ≤ n
    calc
      _ ≤ ((Finset.range n).image fun m : Nat =>
          1 - Int.fract (((m + 1 : Nat) : Real) * goldenMechanicalSlope)).card :=
        Finset.card_filter_le _ _
      _ ≤ (Finset.range n).card := Finset.card_image_le
      _ = n := Finset.card_range n⟩
  rw [← golden_arc_first_return_gap_set_eq_rank_first_return_gap_set n r]
  exact golden_arc_first_return_gap_set_encard_eq_two n hn r

private theorem golden_mechanical_slope_eq_goldenRatio_sub_one :
    goldenMechanicalSlope = Real.goldenRatio - 1 := by
  rw [goldenMechanicalSlope, Real.inv_goldenRatio, ← Real.one_sub_goldenConj]
  ring

private theorem golden_mechanical_slope_bounds :
    0 < goldenMechanicalSlope ∧
      1 < 2 * goldenMechanicalSlope ∧
      3 * goldenMechanicalSlope < 2 ∧
      3 < 5 * goldenMechanicalSlope ∧
      goldenMechanicalSlope < 1 := by
  rw [golden_mechanical_slope_eq_goldenRatio_sub_one, Real.goldenRatio]
  have hsqrt : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

private theorem fract_golden_mechanical_slope :
    Int.fract goldenMechanicalSlope = goldenMechanicalSlope := by
  exact Int.fract_eq_self.mpr
    ⟨golden_mechanical_slope_bounds.1.le, golden_mechanical_slope_bounds.2.2.2.2⟩

private theorem fract_two_mul_golden_mechanical_slope :
    Int.fract (2 * goldenMechanicalSlope) = 2 * goldenMechanicalSlope - 1 := by
  apply Int.fract_eq_iff.mpr
  refine ⟨by linarith [golden_mechanical_slope_bounds.2.1],
    by linarith [golden_mechanical_slope_bounds.2.2.1], 1, ?_⟩
  norm_num

private theorem golden_cylinder_breakpoints_two_order :
    0 < 1 - goldenMechanicalSlope ∧
      1 - goldenMechanicalSlope < 2 - 2 * goldenMechanicalSlope ∧
      2 - 2 * goldenMechanicalSlope < 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    linarith [golden_mechanical_slope_bounds.2.1,
      golden_mechanical_slope_bounds.2.2.2.2]

private theorem golden_cylinder_rank_two (i : Nat) :
    goldenCylinderRank 2 i =
      if 2 - 2 * goldenMechanicalSlope ≤ goldenPhase i then 2
      else if 1 - goldenMechanicalSlope ≤ goldenPhase i then 1 else 0 := by
  classical
  change
    (((Finset.range 2).image fun m : Nat =>
      1 - Int.fract (((m + 1 : Nat) : Real) * goldenMechanicalSlope)).filter
        (fun x => x ≤ goldenPhase i)).card = _
  have hzero :
      1 - Int.fract ((((0 + 1 : Nat) : Real) * goldenMechanicalSlope)) =
        1 - goldenMechanicalSlope := by
    norm_num [fract_golden_mechanical_slope]
  have hone :
      1 - Int.fract ((((1 + 1 : Nat) : Real) * goldenMechanicalSlope)) =
        2 - 2 * goldenMechanicalSlope := by
    norm_num [fract_two_mul_golden_mechanical_slope]
    ring
  have hbreak :
      (Finset.range 2).image (fun m : Nat =>
        1 - Int.fract (((m + 1 : Nat) : Real) * goldenMechanicalSlope)) =
          {1 - goldenMechanicalSlope, 2 - 2 * goldenMechanicalSlope} := by
    ext x
    constructor
    · intro hx
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
      have hm' : m = 0 ∨ m = 1 := by
        have := Finset.mem_range.mp hm
        omega
      rcases hm' with rfl | rfl
      · rw [hzero]
        simp
      · rw [hone]
        simp
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_image.mpr ⟨0, by decide, hzero⟩
      · exact Finset.mem_image.mpr ⟨1, by decide, hone⟩
  rw [hbreak]
  have hne : 1 - goldenMechanicalSlope ≠ 2 - 2 * goldenMechanicalSlope :=
    ne_of_lt golden_cylinder_breakpoints_two_order.2.1
  by_cases hhigh : 2 - 2 * goldenMechanicalSlope ≤ goldenPhase i
  · have hlow : 1 - goldenMechanicalSlope ≤ goldenPhase i :=
      golden_cylinder_breakpoints_two_order.2.1.le.trans hhigh
    simp only [Finset.filter_insert, Finset.filter_singleton]
    simp [hhigh, hlow, hne]
  · by_cases hlow : 1 - goldenMechanicalSlope ≤ goldenPhase i
    · simp only [Finset.filter_insert, Finset.filter_singleton]
      simp [hhigh, hlow]
    · simp only [Finset.filter_insert, Finset.filter_singleton]
      simp [hhigh, hlow]

private theorem golden_cylinder_rank_two_eq_zero_iff (i : Nat) :
    goldenCylinderRank 2 i = 0 ↔ goldenPhase i < 1 - goldenMechanicalSlope := by
  rw [golden_cylinder_rank_two]
  by_cases hhigh : 2 - 2 * goldenMechanicalSlope ≤ goldenPhase i
  · have hlow : 1 - goldenMechanicalSlope ≤ goldenPhase i :=
      golden_cylinder_breakpoints_two_order.2.1.le.trans hhigh
    simp [hhigh, hlow]
  · by_cases hlow : 1 - goldenMechanicalSlope ≤ goldenPhase i
    · simp [hhigh, hlow]
    · simp [hhigh, hlow, lt_of_not_ge hlow]

private theorem golden_cylinder_rank_two_eq_one_iff (i : Nat) :
    goldenCylinderRank 2 i = 1 ↔
      goldenPhase i ∈ Ico (1 - goldenMechanicalSlope)
        (2 - 2 * goldenMechanicalSlope) := by
  rw [golden_cylinder_rank_two]
  by_cases hhigh : 2 - 2 * goldenMechanicalSlope ≤ goldenPhase i
  · have hlow : 1 - goldenMechanicalSlope ≤ goldenPhase i :=
      golden_cylinder_breakpoints_two_order.2.1.le.trans hhigh
    simp [hhigh, hlow]
  · by_cases hlow : 1 - goldenMechanicalSlope ≤ goldenPhase i
    · simp [hhigh, hlow, lt_of_not_ge hhigh]
    · simp [hhigh, hlow]

private theorem golden_cylinder_rank_two_eq_two_iff (i : Nat) :
    goldenCylinderRank 2 i = 2 ↔ 2 - 2 * goldenMechanicalSlope ≤ goldenPhase i := by
  rw [golden_cylinder_rank_two]
  by_cases hhigh : 2 - 2 * goldenMechanicalSlope ≤ goldenPhase i
  · simp [hhigh]
  · by_cases hlow : 1 - goldenMechanicalSlope ≤ goldenPhase i <;>
      simp [hhigh, hlow]

private theorem fract_three_mul_golden_mechanical_slope :
    Int.fract (3 * goldenMechanicalSlope) = 3 * goldenMechanicalSlope - 1 := by
  apply Int.fract_eq_iff.mpr
  refine ⟨by linarith [golden_mechanical_slope_bounds.2.1],
    by linarith [golden_mechanical_slope_bounds.2.2.1], 1, ?_⟩
  norm_num

private theorem golden_cylinder_rank_two_zero : goldenCylinderRank 2 1 = 0 := by
  rw [golden_cylinder_rank_two_eq_zero_iff]
  simp [goldenPhase, fract_two_mul_golden_mechanical_slope]
  linarith [golden_mechanical_slope_bounds.2.2.1]

private theorem golden_cylinder_rank_two_one : goldenCylinderRank 2 0 = 1 := by
  rw [golden_cylinder_rank_two_eq_one_iff]
  simp [goldenPhase, fract_golden_mechanical_slope]
  constructor <;> linarith [golden_mechanical_slope_bounds.2.1,
    golden_mechanical_slope_bounds.2.2.1]

private theorem golden_cylinder_rank_two_two : goldenCylinderRank 2 2 = 2 := by
  rw [golden_cylinder_rank_two_eq_two_iff]
  simp [goldenPhase, fract_three_mul_golden_mechanical_slope]
  linarith [golden_mechanical_slope_bounds.2.2.2.1]

private theorem golden_arc_first_return_gap_set_two_zero :
    goldenArcFirstReturnGapSet 2 (0 : Fin 3) = {2, 3} := by
  rw [golden_arc_first_return_gap_set_eq_rank_first_return_gap_set]
  change goldenRankFirstReturnGapSet 2 0 = {2, 3}
  calc
    _ = goldenOccurrenceGapSet 2 [false, true] := by
      symm
      simpa only [golden_cylinder_rank_two_zero] using
        golden_occurrence_gap_set_eq_rank_first_return_gap_set
          (show goldenFactor 2 1 = [false, true] by decide)
    _ = {2, 3} := golden_occurrence_gap_set_two_false_true

private theorem golden_arc_first_return_gap_set_two_one :
    goldenArcFirstReturnGapSet 2 (1 : Fin 3) = {2, 3} := by
  rw [golden_arc_first_return_gap_set_eq_rank_first_return_gap_set]
  change goldenRankFirstReturnGapSet 2 1 = {2, 3}
  calc
    _ = goldenOccurrenceGapSet 2 [true, false] := by
      symm
      simpa only [golden_cylinder_rank_two_one] using
        golden_occurrence_gap_set_eq_rank_first_return_gap_set
          (show goldenFactor 2 0 = [true, false] by decide)
    _ = {2, 3} := golden_occurrence_gap_set_two_true_false

private theorem golden_arc_first_return_gap_set_two_two :
    goldenArcFirstReturnGapSet 2 (2 : Fin 3) = {3, 5} := by
  rw [golden_arc_first_return_gap_set_eq_rank_first_return_gap_set]
  change goldenRankFirstReturnGapSet 2 2 = {3, 5}
  calc
    _ = goldenOccurrenceGapSet 2 [true, true] := by
      symm
      simpa only [golden_cylinder_rank_two_two] using
        golden_occurrence_gap_set_eq_rank_first_return_gap_set
          (show goldenFactor 2 2 = [true, true] by decide)
    _ = {3, 5} := golden_occurrence_gap_set_two_true_true

private def consecutiveGaps : List Nat → List Nat
  | x :: y :: xs => (y - x) :: consecutiveGaps (y :: xs)
  | _ => []

private def boundedFirstReturnGaps (start bound : Nat) : Finset Nat :=
  (consecutiveGaps <|
    (List.range bound).filter fun i => goldenFactor 2 i = goldenFactor 2 start).toFinset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Kernel reduction enumerates 128 starts for each of the three length-two factors.
private theorem golden_arc_first_return_two_bounded_readout :
    [boundedFirstReturnGaps 1 128, boundedFirstReturnGaps 0 128,
      boundedFirstReturnGaps 2 128] = [{2, 3}, {2, 3}, {3, 5}] := by
  decide

#print axioms golden_arc_first_return_gap_set_eq_rank_first_return_gap_set
#print axioms golden_arc_first_return_gap_set_encard_eq_two
#print axioms golden_occurrence_gap_set_encard_eq_two

end D5.S1.Words
