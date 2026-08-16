/- GID: D5/S0/Tower/Champions/PhaseAudit
   generality: I
   mirror-B: D5/B/S0/Tower/Champions/PhaseAudit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact golden arm phases package the demoted even-phase point and restored champion. -/

import D5.S0.Tower.MetricGeometry.GoldenSurvivorSet

/- Library-search audit trail (2026-08-16): repository search found the frozen
   golden grid, survivor, maximizer family, gap order, and champion point identity.
   Pinned mathlib supplied `Metric.le_infDist`, the golden-ratio algebra, and
   Fibonacci/Zeckendorf normalization; no exact phase-audit theorem was found. -/

namespace D5.S0.Tower.Champions.PhaseAudit

open D5.S0.Conventions
open D5.S0.Tower.GoldenGaps
open D5.S0.Tower.GoldenNames
open D5.S0.Tower.GoldenChampionPoint
open D5.S0.Tower.MetricGeometry.GoldenSurvivor
open D5.S0.Tower.MetricGeometry.GoldenSurvivorSet

local notation "φ" => Real.goldenRatio

set_option maxHeartbeats 800000 in
-- The single packaged proof elaborates four phase inductions and three exact finite-grid audits.
theorem golden_phase_audit :
    ((∀ k : Nat,
        goldenSurvivor (2 * (k + 1)) (1 / (φ + 2)) =
          1 / (φ * Real.sqrt 5)) ∧
      (∀ k : Nat,
        goldenSurvivor (4 * k + 1) (1 / (φ + 2)) = 1 / Real.sqrt 5 ∧
        goldenSurvivor (4 * k + 3) (1 / (φ + 2)) =
          1 / (φ ^ 2 * Real.sqrt 5)) ∧
      (1 / (φ + 2) : Real) = 1 / (φ * Real.sqrt 5)) ∧
    (((13 / 2 : Real) - 4 * φ) ∈ goldenSurvivorMaximizers 6 ∧
      goldenSurvivor 5 ((13 / 2 : Real) - 4 * φ) = φ ^ (-1 : Int) / 2 ∧
      goldenSurvivor 6 ((13 / 2 : Real) - 4 * φ) = 1 / 2 ∧
      goldenSurvivor 7 ((13 / 2 : Real) - 4 * φ) = φ ^ (-2 : Int) / 2) := by
  have adjacent_infDist (Q : Nat) (i : Fin (Nat.fib (Q + 2) - 1)) (x : Real)
      (hx : x ∈ Set.Icc (indexedNameValue Q (goldenGapLeft Q i))
        (indexedNameValue Q (goldenGapRight Q i))) :
      Metric.infDist x (goldenNameGrid Q) =
        min (x - indexedNameValue Q (goldenGapLeft Q i))
          (indexedNameValue Q (goldenGapRight Q i) - x) := by
    let a := indexedNameValue Q (goldenGapLeft Q i)
    let b := indexedNameValue Q (goldenGapRight Q i)
    have hax : a ≤ x := by simpa [a] using hx.1
    have hxb : x ≤ b := by simpa [b] using hx.2
    have ha_mem : a ∈ goldenNameGrid Q := ⟨goldenGapLeft Q i, rfl⟩
    have hb_mem : b ∈ goldenNameGrid Q := ⟨goldenGapRight Q i, rfl⟩
    have hgrid : (goldenNameGrid Q).Nonempty := ⟨a, ha_mem⟩
    apply le_antisymm
    · apply le_min
      · calc
          Metric.infDist x (goldenNameGrid Q) ≤ dist x a :=
            Metric.infDist_le_dist_of_mem ha_mem
          _ = x - a := by rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hax)]
      · calc
          Metric.infDist x (goldenNameGrid Q) ≤ dist x b :=
            Metric.infDist_le_dist_of_mem hb_mem
          _ = b - x := by
            rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxb)]
            ring
    · rw [Metric.le_infDist hgrid]
      intro y hy
      rcases hy with ⟨j, rfl⟩
      by_cases hj : j ≤ goldenGapLeft Q i
      · have hjv : indexedNameValue Q j ≤ a :=
          (indexed_nameValue_strictMono Q).monotone hj
        rw [Real.dist_eq, abs_of_nonneg]
        · exact min_le_left _ _ |>.trans (by linarith)
        · linarith
      · have hjr : goldenGapRight Q i ≤ j := by
          change i.1 + 1 ≤ j.1
          change ¬j.1 ≤ i.1 at hj
          omega
        have hjv : b ≤ indexedNameValue Q j :=
          (indexed_nameValue_strictMono Q).monotone hjr
        rw [Real.dist_eq, abs_of_nonpos]
        · exact min_le_right _ _ |>.trans (by linarith)
        · linarith
  
  have shift_four (Q n : Nat) (hn : n < Nat.fib (Q + 2)) :
      indexedNameValue (Q + 4)
          (⟨Nat.fib (Q + 3) + n, by
            have hrec : Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) := by
              rw [Nat.fib_add_two (n := Q + 2), add_comm]
            have hmono : Nat.fib (Q + 4) ≤ Nat.fib ((Q + 4) + 2) :=
              Nat.fib_mono (by omega)
            omega⟩ : Fin (Nat.fib ((Q + 4) + 2))) =
        φ ^ (-3 : Int) + φ ^ (-4 : Int) *
          indexedNameValue Q ⟨n, hn⟩ := by
    have hbounded : ∀ k ∈ wdigits n, k < Q + 2 := by
      intro k hk
      have hk_mem : Nat.fib k ∈ (wdigits n).map Nat.fib :=
        List.mem_map.mpr ⟨k, hk, rfl⟩
      have hk_le : Nat.fib k ≤ ((wdigits n).map Nat.fib).sum :=
        List.le_sum_of_mem hk_mem
      rw [decode_wdigits] at hk_le
      by_contra hk_bound
      have hindex : Q + 2 ≤ k := Nat.le_of_not_gt hk_bound
      have hfib : Nat.fib (Q + 2) ≤ Nat.fib k := Nat.fib_mono hindex
      omega
    have hcanonical : ((Q + 3) :: wdigits n).IsZeckendorfRep := by
      rw [List.IsZeckendorfRep, List.cons_append]
      apply (wdigits_isCanonical n).cons
      intro k hk
      have hk_mem := List.mem_of_mem_head? hk
      rw [List.mem_append, List.mem_singleton] at hk_mem
      rcases hk_mem with hk_digits | rfl
      · have := hbounded k hk_digits
        omega
      · omega
    have hdigits : wdigits (Nat.fib (Q + 3) + n) = (Q + 3) :: wdigits n := by
      symm
      apply wdigits_unique hcanonical
      simp only [List.map_cons, List.sum_cons, decode_wdigits]
    change ((wdigits (Nat.fib (Q + 3) + n)).map fun k : Nat ↦
        φ ^ ((k : Int) - ((((Q + 4) + 2 : Nat)) : Int))).sum =
      φ ^ (-3 : Int) + φ ^ (-4 : Int) *
        ((wdigits n).map fun k : Nat ↦
          φ ^ ((k : Int) - ((Q + 2 : Nat) : Int))).sum
    rw [hdigits]
    simp only [List.map_cons, List.sum_cons]
    have hhead :
        ((Q + 3 : Nat) : Int) - (((Q + 4) + 2 : Nat) : Int) = -3 := by
      push_cast
      omega
    rw [hhead]
    congr 1
    induction wdigits n with
    | nil => simp
    | cons k digits ih =>
        simp only [List.map_cons, List.sum_cons]
        have hexponent :
            (k : Int) - (((Q + 4) + 2 : Nat) : Int) =
              -4 + ((k : Int) - ((Q + 2 : Nat) : Int)) := by
          push_cast
          omega
        rw [hexponent, zpow_add₀ Real.goldenRatio_ne_zero, ih]
        ring
  
  have audit_shift (Q : Nat) (i : Fin (Nat.fib (Q + 2) - 1))
      (hx : (1 / (φ + 2) : Real) ∈
        Set.Icc (indexedNameValue Q (goldenGapLeft Q i))
          (indexedNameValue Q (goldenGapRight Q i))) :
      ∃ j : Fin (Nat.fib ((Q + 4) + 2) - 1),
        (1 / (φ + 2) : Real) ∈
          Set.Icc (indexedNameValue (Q + 4) (goldenGapLeft (Q + 4) j))
            (indexedNameValue (Q + 4) (goldenGapRight (Q + 4) j)) ∧
        goldenSurvivor (Q + 4) (1 / (φ + 2)) =
          goldenSurvivor Q (1 / (φ + 2)) := by
    let x : Real := 1 / (φ + 2)
    have hphi_sq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
    have hphi_pos : 0 < φ := Real.goldenRatio_pos
    have hsqrt_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hsqrt_cube : (Real.sqrt 5) ^ 3 = 5 * Real.sqrt 5 := by
      calc
        (Real.sqrt 5) ^ 3 = Real.sqrt 5 * (Real.sqrt 5) ^ 2 := by ring
        _ = 5 * Real.sqrt 5 := by rw [hsqrt_sq]; ring
    have hsqrt_four : (Real.sqrt 5) ^ 4 = 25 := by
      calc
        (Real.sqrt 5) ^ 4 = ((Real.sqrt 5) ^ 2) ^ 2 := by ring
        _ = 25 := by rw [hsqrt_sq]; norm_num
    have hfix : x = φ ^ (-3 : Int) + φ ^ (-4 : Int) * x := by
      dsimp [x]
      rw [zpow_neg, zpow_neg]
      norm_num only [zpow_ofNat]
      field_simp [Real.goldenRatio_ne_zero]
      ring_nf
      nlinarith [hsqrt_sq, hsqrt_cube, hsqrt_four]
    have hleftBound : i.1 < Nat.fib (Q + 2) := by
      have hi := i.2
      have hpos : 0 < Nat.fib (Q + 2) := Nat.fib_pos.2 (by omega)
      omega
    have hrightBound : i.1 + 1 < Nat.fib (Q + 2) := by
      have hi := i.2
      omega
    have hnewRightBound :
        Nat.fib (Q + 3) + (i.1 + 1) < Nat.fib ((Q + 4) + 2) := by
      have hrec : Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) := by
        rw [Nat.fib_add_two (n := Q + 2), add_comm]
      have hmono : Nat.fib (Q + 4) ≤ Nat.fib ((Q + 4) + 2) :=
        Nat.fib_mono (by omega)
      omega
    let j : Fin (Nat.fib ((Q + 4) + 2) - 1) :=
      ⟨Nat.fib (Q + 3) + i.1, by omega⟩
    have hleft :
        indexedNameValue (Q + 4) (goldenGapLeft (Q + 4) j) =
          φ ^ (-3 : Int) + φ ^ (-4 : Int) *
            indexedNameValue Q (goldenGapLeft Q i) := by
      simpa [j, goldenGapLeft] using shift_four Q i.1 hleftBound
    have hright :
        indexedNameValue (Q + 4) (goldenGapRight (Q + 4) j) =
          φ ^ (-3 : Int) + φ ^ (-4 : Int) *
            indexedNameValue Q (goldenGapRight Q i) := by
      have hnewIndex : goldenGapRight (Q + 4) j =
          (⟨Nat.fib (Q + 3) + (i.1 + 1), hnewRightBound⟩ :
            Fin (Nat.fib ((Q + 4) + 2))) := by
        apply Fin.ext
        dsimp [j, goldenGapRight]
        omega
      have holdIndex : goldenGapRight Q i =
          (⟨i.1 + 1, hrightBound⟩ : Fin (Nat.fib (Q + 2))) := by
        apply Fin.ext
        rfl
      rw [hnewIndex, holdIndex]
      exact shift_four Q (i.1 + 1) hrightBound
    have hscale_pos : 0 < φ ^ (-4 : Int) := zpow_pos hphi_pos _
    have hxLeft : indexedNameValue Q (goldenGapLeft Q i) ≤ x := by
      simpa [x] using hx.1
    have hxRight : x ≤ indexedNameValue Q (goldenGapRight Q i) := by
      simpa [x] using hx.2
    have hx' : x ∈
        Set.Icc (indexedNameValue (Q + 4) (goldenGapLeft (Q + 4) j))
          (indexedNameValue (Q + 4) (goldenGapRight (Q + 4) j)) := by
      constructor
      · rw [hleft, hfix]
        simpa [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_left hxLeft hscale_pos.le)
            (φ ^ (-3 : Int))
      · rw [hright, hfix]
        simpa [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_left hxRight hscale_pos.le)
            (φ ^ (-3 : Int))
    refine ⟨j, hx', ?_⟩
    have hinf := adjacent_infDist Q i x hx
    have hinf' := adjacent_infDist (Q + 4) j x hx'
    have hleftDistance :
        x - indexedNameValue (Q + 4) (goldenGapLeft (Q + 4) j) =
          φ ^ (-4 : Int) *
            (x - indexedNameValue Q (goldenGapLeft Q i)) := by
      rw [hleft]
      nth_rewrite 1 [hfix]
      ring
    have hrightDistance :
        indexedNameValue (Q + 4) (goldenGapRight (Q + 4) j) - x =
          φ ^ (-4 : Int) *
            (indexedNameValue Q (goldenGapRight Q i) - x) := by
      rw [hright]
      nth_rewrite 1 [hfix]
      ring
    have hinfScale :
        Metric.infDist x (goldenNameGrid (Q + 4)) =
          φ ^ (-4 : Int) * Metric.infDist x (goldenNameGrid Q) := by
      rw [hinf', hinf, hleftDistance, hrightDistance,
        ← mul_min_of_nonneg _ _ hscale_pos.le]
    unfold goldenSurvivor
    rw [hinfScale]
    calc
      φ ^ ((Q + 4 : Nat) : Int) *
            (φ ^ (-4 : Int) * Metric.infDist x (goldenNameGrid Q)) =
          (φ ^ ((Q + 4 : Nat) : Int) * φ ^ (-4 : Int)) *
            Metric.infDist x (goldenNameGrid Q) := by ring
      _ = φ ^ (Q : Int) * Metric.infDist x (goldenNameGrid Q) := by
        rw [← zpow_add₀ Real.goldenRatio_ne_zero]
        congr 2
        push_cast
        omega
  
  have audit_base_one :
      ∃ i : Fin (Nat.fib (1 + 2) - 1),
        (1 / (φ + 2) : Real) ∈
          Set.Icc (indexedNameValue 1 (goldenGapLeft 1 i))
            (indexedNameValue 1 (goldenGapRight 1 i)) ∧
        goldenSurvivor 1 (1 / (φ + 2)) = 1 / Real.sqrt 5 := by
    have hsqrt_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
    have hphi_pos : 0 < φ := Real.goldenRatio_pos
    have hsqrt : Real.sqrt 5 = 2 * φ - 1 := by
      rw [Real.goldenRatio]
      ring
    have hsqrt_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hsqrt_cube : (Real.sqrt 5) ^ 3 = 5 * Real.sqrt 5 := by
      calc
        (Real.sqrt 5) ^ 3 = Real.sqrt 5 * (Real.sqrt 5) ^ 2 := by ring
        _ = 5 * Real.sqrt 5 := by rw [hsqrt_sq]; ring
    have hsqrt_four : (Real.sqrt 5) ^ 4 = 25 := by
      calc
        (Real.sqrt 5) ^ 4 = ((Real.sqrt 5) ^ 2) ^ 2 := by ring
        _ = 25 := by rw [hsqrt_sq]; norm_num
    have hphi_sq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
    have hden : 0 < φ + 2 := by positivity
    let i : Fin (Nat.fib (1 + 2) - 1) := ⟨0, by norm_num [Nat.fib]⟩
    have hleft : indexedNameValue 1 (goldenGapLeft 1 i) = 0 := by
      change ((wdigits 0).map fun k : Nat ↦
        φ ^ ((k : Int) - (((1 : Nat) + 2 : Nat) : Int))).sum = 0
      rw [show wdigits 0 = [] by
        symm
        apply wdigits_unique
        · exact List.IsZeckendorfRep_nil
        · rfl]
      rfl
    have hright : indexedNameValue 1 (goldenGapRight 1 i) = φ ^ (-1 : Int) := by
      change ((wdigits 1).map fun k : Nat ↦
        φ ^ ((k : Int) - (((1 : Nat) + 2 : Nat) : Int))).sum = _
      rw [show wdigits 1 = [2] by
        symm
        apply wdigits_unique
        · norm_num [List.IsZeckendorfRep]
        · norm_num [Nat.fib]]
      norm_num
    have hx : (1 / (φ + 2) : Real) ∈
        Set.Icc (indexedNameValue 1 (goldenGapLeft 1 i))
          (indexedNameValue 1 (goldenGapRight 1 i)) := by
      rw [hleft, hright]
      constructor
      · positivity
      · rw [zpow_neg]
        norm_num only [zpow_ofNat, pow_one]
        rw [div_le_iff₀ hden]
        field_simp [Real.goldenRatio_ne_zero]
        nlinarith
    refine ⟨i, hx, ?_⟩
    have hinf := adjacent_infDist 1 i (1 / (φ + 2)) hx
    unfold goldenSurvivor
    rw [hinf, hleft, hright]
    have hmin :
        min (1 / (φ + 2) - 0) (φ ^ (-1 : Int) - 1 / (φ + 2)) =
          1 / (φ + 2) := by
      simp only [sub_zero]
      apply min_eq_left
      rw [zpow_neg]
      norm_num only [zpow_ofNat, pow_one]
      apply (le_sub_iff_add_le).2
      rw [← two_mul]
      have htwo : 2 / (φ + 2) ≤ φ⁻¹ := by
        rw [div_le_iff₀ hden]
        field_simp [Real.goldenRatio_ne_zero]
        nlinarith [Real.goldenRatio_lt_two]
      simpa [div_eq_mul_inv] using htwo
    rw [hmin]
    norm_num only [Int.reduceNeg, Nat.cast_ofNat, zpow_one]
    rw [hsqrt]
    field_simp [Real.goldenRatio_ne_zero, ne_of_gt hden]
    nlinarith [hphi_sq]
  
  have audit_base_two :
      ∃ i : Fin (Nat.fib (2 + 2) - 1),
        (1 / (φ + 2) : Real) ∈
          Set.Icc (indexedNameValue 2 (goldenGapLeft 2 i))
            (indexedNameValue 2 (goldenGapRight 2 i)) ∧
        goldenSurvivor 2 (1 / (φ + 2)) = 1 / (φ * Real.sqrt 5) := by
    have hphi_pos : 0 < φ := Real.goldenRatio_pos
    have hphi_sq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
    have hsqrt : Real.sqrt 5 = 2 * φ - 1 := by
      rw [Real.goldenRatio]
      ring
    have hden : 0 < φ + 2 := by positivity
    have hphiSqrt : φ * Real.sqrt 5 = φ + 2 := by
      rw [hsqrt]
      nlinarith [hphi_sq]
    let i : Fin (Nat.fib (2 + 2) - 1) := ⟨0, by norm_num [Nat.fib]⟩
    have hleft : indexedNameValue 2 (goldenGapLeft 2 i) = 0 := by
      change ((wdigits 0).map fun k : Nat ↦
        φ ^ ((k : Int) - (((2 : Nat) + 2 : Nat) : Int))).sum = 0
      rw [show wdigits 0 = [] by
        symm
        apply wdigits_unique
        · exact List.IsZeckendorfRep_nil
        · rfl]
      rfl
    have hright : indexedNameValue 2 (goldenGapRight 2 i) = φ ^ (-2 : Int) := by
      change ((wdigits 1).map fun k : Nat ↦
        φ ^ ((k : Int) - (((2 : Nat) + 2 : Nat) : Int))).sum = _
      rw [show wdigits 1 = [2] by
        symm
        apply wdigits_unique
        · norm_num [List.IsZeckendorfRep]
        · norm_num [Nat.fib]]
      norm_num
    have hx : (1 / (φ + 2) : Real) ∈
        Set.Icc (indexedNameValue 2 (goldenGapLeft 2 i))
          (indexedNameValue 2 (goldenGapRight 2 i)) := by
      rw [hleft, hright]
      constructor
      · positivity
      · rw [zpow_neg]
        norm_num only [zpow_ofNat]
        rw [div_le_iff₀ hden]
        field_simp [Real.goldenRatio_ne_zero]
        nlinarith [hphi_sq]
    refine ⟨i, hx, ?_⟩
    have hinf := adjacent_infDist 2 i (1 / (φ + 2)) hx
    unfold goldenSurvivor
    rw [hinf, hleft, hright]
    have hmin :
        min (1 / (φ + 2) - 0) (φ ^ (-2 : Int) - 1 / (φ + 2)) =
          φ ^ (-2 : Int) - 1 / (φ + 2) := by
      simp only [sub_zero]
      apply min_eq_right
      rw [zpow_neg]
      norm_num only [zpow_ofNat]
      rw [sub_le_iff_le_add, ← two_mul]
      have hcompare : (φ ^ 2)⁻¹ ≤ 2 / (φ + 2) := by
        rw [le_div_iff₀ hden]
        field_simp [Real.goldenRatio_ne_zero]
        nlinarith [hphi_sq, Real.one_lt_goldenRatio]
      simpa [div_eq_mul_inv] using hcompare
    rw [hmin, hphiSqrt]
    norm_num only [Nat.cast_ofNat, zpow_ofNat]
    rw [zpow_neg]
    norm_num only [zpow_ofNat]
    field_simp [Real.goldenRatio_ne_zero, ne_of_gt hden]
    nlinarith [hphi_sq]
  
  have audit_base_three :
      ∃ i : Fin (Nat.fib (3 + 2) - 1),
        (1 / (φ + 2) : Real) ∈
          Set.Icc (indexedNameValue 3 (goldenGapLeft 3 i))
            (indexedNameValue 3 (goldenGapRight 3 i)) ∧
        goldenSurvivor 3 (1 / (φ + 2)) =
          1 / (φ ^ 2 * Real.sqrt 5) := by
    have hphi_sq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
    have hsqrt : Real.sqrt 5 = 2 * φ - 1 := by
      rw [Real.goldenRatio]
      ring
    have hsqrt_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hsqrt_cube : (Real.sqrt 5) ^ 3 = 5 * Real.sqrt 5 := by
      calc
        (Real.sqrt 5) ^ 3 = Real.sqrt 5 * (Real.sqrt 5) ^ 2 := by ring
        _ = 5 * Real.sqrt 5 := by rw [hsqrt_sq]; ring
    have hsqrt_four : (Real.sqrt 5) ^ 4 = 25 := by
      calc
        (Real.sqrt 5) ^ 4 = ((Real.sqrt 5) ^ 2) ^ 2 := by ring
        _ = 25 := by rw [hsqrt_sq]; norm_num
    have hden : 0 < φ + 2 := by positivity
    let i : Fin (Nat.fib (3 + 2) - 1) := ⟨1, by norm_num [Nat.fib]⟩
    have hleft : indexedNameValue 3 (goldenGapLeft 3 i) = φ ^ (-3 : Int) := by
      change ((wdigits 1).map fun k : Nat ↦
        φ ^ ((k : Int) - (((3 : Nat) + 2 : Nat) : Int))).sum = _
      rw [show wdigits 1 = [2] by
        symm
        apply wdigits_unique
        · norm_num [List.IsZeckendorfRep]
        · norm_num [Nat.fib]]
      norm_num
    have hright : indexedNameValue 3 (goldenGapRight 3 i) = φ ^ (-2 : Int) := by
      change ((wdigits 2).map fun k : Nat ↦
        φ ^ ((k : Int) - (((3 : Nat) + 2 : Nat) : Int))).sum = _
      rw [show wdigits 2 = [3] by
        symm
        apply wdigits_unique
        · norm_num [List.IsZeckendorfRep]
        · norm_num [Nat.fib]]
      norm_num
    have hx : (1 / (φ + 2) : Real) ∈
        Set.Icc (indexedNameValue 3 (goldenGapLeft 3 i))
          (indexedNameValue 3 (goldenGapRight 3 i)) := by
      rw [hleft, hright, zpow_neg, zpow_neg]
      norm_num only [zpow_ofNat]
      constructor <;>
        field_simp [Real.goldenRatio_ne_zero, ne_of_gt hden] <;>
        ring_nf <;>
        nlinarith [hsqrt_sq, hsqrt_cube, hsqrt_four, Real.one_lt_goldenRatio]
    refine ⟨i, hx, ?_⟩
    have hinf := adjacent_infDist 3 i (1 / (φ + 2)) hx
    unfold goldenSurvivor
    rw [hinf, hleft, hright]
    have hmin :
        min (1 / (φ + 2) - φ ^ (-3 : Int))
            (φ ^ (-2 : Int) - 1 / (φ + 2)) =
          1 / (φ + 2) - φ ^ (-3 : Int) := by
      apply min_eq_left
      rw [zpow_neg, zpow_neg]
      norm_num only [zpow_ofNat]
      field_simp [Real.goldenRatio_ne_zero, ne_of_gt hden]
      ring_nf
      nlinarith [hsqrt_sq, hsqrt_cube, hsqrt_four, Real.one_lt_goldenRatio]
    rw [hmin]
    norm_num only [Nat.cast_ofNat, zpow_ofNat]
    rw [zpow_neg]
    norm_num only [zpow_ofNat]
    rw [hsqrt]
    field_simp [Real.goldenRatio_ne_zero, ne_of_gt hden]
    ring_nf
    nlinarith [hsqrt_sq, hsqrt_cube, hsqrt_four]
  
  have audit_base_four :
      ∃ i : Fin (Nat.fib (4 + 2) - 1),
        (1 / (φ + 2) : Real) ∈
          Set.Icc (indexedNameValue 4 (goldenGapLeft 4 i))
            (indexedNameValue 4 (goldenGapRight 4 i)) ∧
        goldenSurvivor 4 (1 / (φ + 2)) = 1 / (φ * Real.sqrt 5) := by
    have hphi_sq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
    have hsqrt : Real.sqrt 5 = 2 * φ - 1 := by
      rw [Real.goldenRatio]
      ring
    have hsqrt_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hsqrt_cube : (Real.sqrt 5) ^ 3 = 5 * Real.sqrt 5 := by
      calc
        (Real.sqrt 5) ^ 3 = Real.sqrt 5 * (Real.sqrt 5) ^ 2 := by ring
        _ = 5 * Real.sqrt 5 := by rw [hsqrt_sq]; ring
    have hsqrt_four : (Real.sqrt 5) ^ 4 = 25 := by
      calc
        (Real.sqrt 5) ^ 4 = ((Real.sqrt 5) ^ 2) ^ 2 := by ring
        _ = 25 := by rw [hsqrt_sq]; norm_num
    have hden : 0 < φ + 2 := by positivity
    have hphiSqrt : φ * Real.sqrt 5 = φ + 2 := by
      rw [hsqrt]
      nlinarith [hphi_sq]
    let i : Fin (Nat.fib (4 + 2) - 1) := ⟨2, by norm_num [Nat.fib]⟩
    have hleft : indexedNameValue 4 (goldenGapLeft 4 i) = φ ^ (-3 : Int) := by
      change ((wdigits 2).map fun k : Nat ↦
        φ ^ ((k : Int) - (((4 : Nat) + 2 : Nat) : Int))).sum = _
      rw [show wdigits 2 = [3] by
        symm
        apply wdigits_unique
        · norm_num [List.IsZeckendorfRep]
        · norm_num [Nat.fib]]
      norm_num
    have hright : indexedNameValue 4 (goldenGapRight 4 i) = φ ^ (-2 : Int) := by
      change ((wdigits 3).map fun k : Nat ↦
        φ ^ ((k : Int) - (((4 : Nat) + 2 : Nat) : Int))).sum = _
      rw [show wdigits 3 = [4] by
        symm
        apply wdigits_unique
        · norm_num [List.IsZeckendorfRep]
        · norm_num [Nat.fib]]
      norm_num
    have hx : (1 / (φ + 2) : Real) ∈
        Set.Icc (indexedNameValue 4 (goldenGapLeft 4 i))
          (indexedNameValue 4 (goldenGapRight 4 i)) := by
      rw [hleft, hright, zpow_neg, zpow_neg]
      norm_num only [zpow_ofNat]
      constructor <;>
        field_simp [Real.goldenRatio_ne_zero, ne_of_gt hden] <;>
        ring_nf <;>
        nlinarith [hsqrt_sq, hsqrt_cube, hsqrt_four, Real.one_lt_goldenRatio]
    refine ⟨i, hx, ?_⟩
    have hinf := adjacent_infDist 4 i (1 / (φ + 2)) hx
    unfold goldenSurvivor
    rw [hinf, hleft, hright]
    have hmin :
        min (1 / (φ + 2) - φ ^ (-3 : Int))
            (φ ^ (-2 : Int) - 1 / (φ + 2)) =
          1 / (φ + 2) - φ ^ (-3 : Int) := by
      apply min_eq_left
      rw [zpow_neg, zpow_neg]
      norm_num only [zpow_ofNat]
      field_simp [Real.goldenRatio_ne_zero, ne_of_gt hden]
      ring_nf
      nlinarith [hsqrt_sq, hsqrt_cube, hsqrt_four, Real.one_lt_goldenRatio]
    rw [hmin, hphiSqrt]
    norm_num only [Nat.cast_ofNat, zpow_ofNat]
    rw [zpow_neg]
    norm_num only [zpow_ofNat]
    field_simp [Real.goldenRatio_ne_zero, ne_of_gt hden]
    ring_nf
    nlinarith [hsqrt_sq, hsqrt_cube, hsqrt_four]
  
  have audit_all_phases : ∀ k : Nat,
      goldenSurvivor (4 * k + 1) (1 / (φ + 2)) = 1 / Real.sqrt 5 ∧
      goldenSurvivor (4 * k + 2) (1 / (φ + 2)) = 1 / (φ * Real.sqrt 5) ∧
      goldenSurvivor (4 * k + 3) (1 / (φ + 2)) =
        1 / (φ ^ 2 * Real.sqrt 5) ∧
      goldenSurvivor (4 * k + 4) (1 / (φ + 2)) = 1 / (φ * Real.sqrt 5) := by
    let Phase := fun (Q : Nat) (value : Real) ↦
      ∃ i : Fin (Nat.fib (Q + 2) - 1),
        (1 / (φ + 2) : Real) ∈
          Set.Icc (indexedNameValue Q (goldenGapLeft Q i))
            (indexedNameValue Q (goldenGapRight Q i)) ∧
        goldenSurvivor Q (1 / (φ + 2)) = value
    have hstep : ∀ Q value, Phase Q value → Phase (Q + 4) value := by
      intro Q value hphase
      rcases hphase with ⟨i, hbracket, hvalue⟩
      rcases audit_shift Q i hbracket with ⟨j, hbracket', hperiod⟩
      exact ⟨j, hbracket', hperiod.trans hvalue⟩
    have hphase : ∀ k : Nat,
        Phase (4 * k + 1) (1 / Real.sqrt 5) ∧
        Phase (4 * k + 2) (1 / (φ * Real.sqrt 5)) ∧
        Phase (4 * k + 3) (1 / (φ ^ 2 * Real.sqrt 5)) ∧
        Phase (4 * k + 4) (1 / (φ * Real.sqrt 5)) := by
      intro k
      induction k with
      | zero =>
          simpa [Phase] using
            And.intro audit_base_one
              (And.intro audit_base_two (And.intro audit_base_three audit_base_four))
      | succ k ih =>
          rcases ih with ⟨h1, h2, h3, h4⟩
          have hs1 := hstep (4 * k + 1) _ h1
          have hs2 := hstep (4 * k + 2) _ h2
          have hs3 := hstep (4 * k + 3) _ h3
          have hs4 := hstep (4 * k + 4) _ h4
          simpa [Nat.mul_succ, add_assoc, add_comm, add_left_comm] using
            And.intro hs1 (And.intro hs2 (And.intro hs3 hs4))
    intro k
    rcases hphase k with ⟨⟨_, _, h1⟩, ⟨_, _, h2⟩, ⟨_, _, h3⟩, ⟨_, _, h4⟩⟩
    exact ⟨h1, h2, h3, h4⟩
  
  have champion_arm_five :
      goldenSurvivor 5 ((13 / 2 : Real) - 4 * φ) = φ ^ (-1 : Int) / 2 := by
    let x : Real := (13 / 2 : Real) - 4 * φ
    have hxclosed : x = φ ^ (-6 : Int) / 2 := by
      dsimp [x]
      exact golden_champion_point_identity.1.trans golden_champion_point_identity.2
    let i : Fin (Nat.fib (5 + 2) - 1) := firstGoldenGap 5 (by omega)
    have hleft : indexedNameValue 5 (goldenGapLeft 5 i) = 0 := by
      change ((wdigits 0).map fun k : Nat ↦
        φ ^ ((k : Int) - (((5 : Nat) + 2 : Nat) : Int))).sum = 0
      rw [show wdigits 0 = [] by
        symm
        apply wdigits_unique
        · exact List.IsZeckendorfRep_nil
        · rfl]
      rfl
    have hright : indexedNameValue 5 (goldenGapRight 5 i) = φ ^ (-5 : Int) := by
      have hgap := first_golden_gap_value 5 (by omega)
      simpa [i, hleft] using hgap
    have hshift : φ ^ (-5 : Int) = φ ^ (-6 : Int) * φ := by
      conv_rhs => rhs; rw [show φ = φ ^ (1 : Int) by norm_num]
      rw [← zpow_add₀ Real.goldenRatio_ne_zero]
      norm_num
    have hxcell : x ∈
        Set.Icc (indexedNameValue 5 (goldenGapLeft 5 i))
          (indexedNameValue 5 (goldenGapRight 5 i)) := by
      rw [hleft, hright, hxclosed]
      constructor
      · positivity
      · rw [hshift]
        have hpow_pos : 0 < φ ^ (-6 : Int) := zpow_pos Real.goldenRatio_pos _
        calc
          φ ^ (-6 : Int) / 2 = φ ^ (-6 : Int) * (1 / 2 : Real) := by ring
          _ ≤ φ ^ (-6 : Int) * φ := by
            exact mul_le_mul_of_nonneg_left (by nlinarith [Real.one_lt_goldenRatio]) hpow_pos.le
    have hinf := adjacent_infDist 5 i x hxcell
    unfold goldenSurvivor
    rw [hinf, hleft, hright, hxclosed]
    have hmin :
        min (φ ^ (-6 : Int) / 2 - 0)
            (φ ^ (-5 : Int) - φ ^ (-6 : Int) / 2) =
          φ ^ (-6 : Int) / 2 := by
      simp only [sub_zero]
      apply min_eq_left
      rw [le_sub_iff_add_le, ← two_mul]
      rw [hshift]
      have hmul := mul_le_mul_of_nonneg_left Real.one_lt_goldenRatio.le
        (zpow_pos Real.goldenRatio_pos (-6 : Int)).le
      convert hmul using 1
      ring
    rw [hmin]
    rw [← mul_div_assoc, ← zpow_add₀ Real.goldenRatio_ne_zero]
    norm_num
  
  have champion_arm_seven :
      goldenSurvivor 7 ((13 / 2 : Real) - 4 * φ) = φ ^ (-2 : Int) / 2 := by
    let x : Real := (13 / 2 : Real) - 4 * φ
    have hxclosed : x = φ ^ (-6 : Int) / 2 := by
      dsimp [x]
      exact golden_champion_point_identity.1.trans golden_champion_point_identity.2
    let i : Fin (Nat.fib (7 + 2) - 1) := firstGoldenGap 7 (by omega)
    have hleft : indexedNameValue 7 (goldenGapLeft 7 i) = 0 := by
      change ((wdigits 0).map fun k : Nat ↦
        φ ^ ((k : Int) - (((7 : Nat) + 2 : Nat) : Int))).sum = 0
      rw [show wdigits 0 = [] by
        symm
        apply wdigits_unique
        · exact List.IsZeckendorfRep_nil
        · rfl]
      rfl
    have hright : indexedNameValue 7 (goldenGapRight 7 i) = φ ^ (-7 : Int) := by
      have hgap := first_golden_gap_value 7 (by omega)
      simpa [i, hleft] using hgap
    have hshift : φ ^ (-6 : Int) = φ ^ (-7 : Int) * φ := by
      conv_rhs => rhs; rw [show φ = φ ^ (1 : Int) by norm_num]
      rw [← zpow_add₀ Real.goldenRatio_ne_zero]
      norm_num
    have hxcell : x ∈
        Set.Icc (indexedNameValue 7 (goldenGapLeft 7 i))
          (indexedNameValue 7 (goldenGapRight 7 i)) := by
      rw [hleft, hright, hxclosed]
      constructor
      · positivity
      · rw [hshift]
        have hpow_pos : 0 < φ ^ (-7 : Int) := zpow_pos Real.goldenRatio_pos _
        calc
          φ ^ (-7 : Int) * φ / 2 =
              φ ^ (-7 : Int) * (φ / 2) := by ring
          _ ≤ φ ^ (-7 : Int) := by
            nlinarith [Real.goldenRatio_lt_two]
    have hinf := adjacent_infDist 7 i x hxcell
    unfold goldenSurvivor
    rw [hinf, hleft, hright, hxclosed]
    have hmin :
        min (φ ^ (-6 : Int) / 2 - 0)
            (φ ^ (-7 : Int) - φ ^ (-6 : Int) / 2) =
          φ ^ (-7 : Int) - φ ^ (-6 : Int) / 2 := by
      simp only [sub_zero]
      apply min_eq_right
      rw [sub_le_iff_le_add, ← two_mul]
      rw [hshift]
      have hmul := mul_le_mul_of_nonneg_left Real.one_lt_goldenRatio.le
        (zpow_pos Real.goldenRatio_pos (-7 : Int)).le
      convert hmul using 1 <;> ring
    rw [hmin]
    have hphi_sq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
    have hcancelSeven : φ ^ ((7 : Nat) : Int) * φ ^ (-7 : Int) = 1 := by
      rw [← zpow_add₀ Real.goldenRatio_ne_zero]
      norm_num
    have hcancelSix : φ ^ ((7 : Nat) : Int) * φ ^ (-6 : Int) = φ := by
      conv_rhs => rw [show φ = φ ^ (1 : Int) by norm_num]
      rw [← zpow_add₀ Real.goldenRatio_ne_zero]
      norm_num
    have hinvSq : φ ^ (-2 : Int) = 2 - φ := by
      rw [zpow_neg]
      norm_num only [zpow_ofNat]
      apply inv_eq_of_mul_eq_one_right
      nlinarith [hphi_sq]
    rw [mul_sub, hcancelSeven, ← mul_div_assoc, hcancelSix, hinvSq]
    ring
  
  have champion_mem_six :
      ((13 / 2 : Real) - 4 * φ) ∈ goldenSurvivorMaximizers 6 := by
    let x : Real := (13 / 2 : Real) - 4 * φ
    have hxclosed : x = φ ^ (-6 : Int) / 2 := by
      dsimp [x]
      exact golden_champion_point_identity.1.trans golden_champion_point_identity.2
    let i : Fin (Nat.fib (6 + 2) - 1) := firstGoldenGap 6 (by omega)
    have hleft : indexedNameValue 6 (goldenGapLeft 6 i) = 0 := by
      change ((wdigits 0).map fun k : Nat ↦
        φ ^ ((k : Int) - (((6 : Nat) + 2 : Nat) : Int))).sum = 0
      rw [show wdigits 0 = [] by
        symm
        apply wdigits_unique
        · exact List.IsZeckendorfRep_nil
        · rfl]
      rfl
    have hgap :
        indexedNameValue 6 (goldenGapRight 6 i) -
            indexedNameValue 6 (goldenGapLeft 6 i) = φ ^ (-6 : Int) := by
      simpa [i] using first_golden_gap_value 6 (by omega)
    have hlarge : IsGoldenLargeGap 6 i := by
      simpa [IsGoldenLargeGap] using hgap
    have hmid : goldenGapMidpoint 6 i = φ ^ (-6 : Int) / 2 := by
      unfold goldenGapMidpoint
      rw [hleft] at hgap ⊢
      linarith
    rw [goldenSurvivorMaximizers_eq_midpoint_image 6 (by omega)]
    refine ⟨i, ?_, ?_⟩
    · simp [goldenLargeGapIndices, hlarge]
    · rw [hmid]
      exact hxclosed.symm
  
  have heven : ∀ k : Nat,
      goldenSurvivor (2 * (k + 1)) (1 / (φ + 2)) =
        1 / (φ * Real.sqrt 5) := by
    intro k
    obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' k
    · subst k
      rw [show 2 * (2 * m + 1) = 4 * m + 2 by omega]
      exact (audit_all_phases m).2.1
    · subst k
      rw [show 2 * (2 * m + 1 + 1) = 4 * m + 4 by omega]
      exact (audit_all_phases m).2.2.2
  have hodd : ∀ k : Nat,
      goldenSurvivor (4 * k + 1) (1 / (φ + 2)) = 1 / Real.sqrt 5 ∧
      goldenSurvivor (4 * k + 3) (1 / (φ + 2)) =
        1 / (φ ^ 2 * Real.sqrt 5) := by
    intro k
    exact ⟨(audit_all_phases k).1, (audit_all_phases k).2.2.1⟩
  have hidentity : (1 / (φ + 2) : Real) = 1 / (φ * Real.sqrt 5) := by
    have hsqrt : Real.sqrt 5 = 2 * φ - 1 := by
      rw [Real.goldenRatio]
      ring
    have hden : φ * Real.sqrt 5 = φ + 2 := by
      rw [hsqrt]
      nlinarith [Real.goldenRatio_sq]
    rw [hden]
  exact ⟨⟨heven, hodd, hidentity⟩,
    ⟨champion_mem_six, champion_arm_five, golden_champion_point_realizes,
      champion_arm_seven⟩⟩

example :
    goldenSurvivor 2 (1 / (φ + 2)) = 1 / (φ * Real.sqrt 5) ∧
      goldenSurvivor 3 (1 / (φ + 2)) = 1 / (φ ^ 2 * Real.sqrt 5) := by
  have htwo := golden_phase_audit.1.1 0
  have hthree := (golden_phase_audit.1.2.1 0).2
  norm_num at htwo hthree ⊢
  exact ⟨htwo, hthree⟩

example :
    goldenSurvivor 5 ((13 / 2 : Real) - 4 * φ) = φ ^ (-1 : Int) / 2 ∧
      goldenSurvivor 6 ((13 / 2 : Real) - 4 * φ) = 1 / 2 ∧
      goldenSurvivor 7 ((13 / 2 : Real) - 4 * φ) = φ ^ (-2 : Int) / 2 := by
  norm_num only
  exact ⟨golden_phase_audit.2.2.1, golden_phase_audit.2.2.2.1,
    golden_phase_audit.2.2.2.2⟩

end D5.S0.Tower.Champions.PhaseAudit
