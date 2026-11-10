/- GID: D5/S3/Arith/DiophantineApproximation/SimultaneousPhaseAlignment
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/SimultaneousPhaseAlignment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Simultaneous Dirichlet approximation aligns finitely many real phases and yields a cosine-alignment scale. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.NumberTheory.DiophantineApproximation.Basic

namespace D5.S3.Arith.DiophantineApproximation.SimultaneousPhaseAlignment

open scoped BigOperators

theorem simultaneous_dirichlet {d Q : ℕ} (hQ : 1 ≤ Q) (lambda : Fin d → ℝ) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ^ d ∧
      ∀ j, ∃ a : ℤ, |(q : ℝ) * lambda j - (a : ℝ)| ≤ 1 / (Q : ℝ) := by
  classical
  let N : ℕ := Q ^ d
  have hQpos : 0 < Q := lt_of_lt_of_le Nat.zero_lt_one hQ
  have hQposR : (0 : ℝ) < Q := by exact_mod_cast hQpos
  let box (k : ℕ) : Fin d → Fin Q := fun j =>
    ⟨⌊(Q : ℝ) * Int.fract ((k : ℝ) * lambda j)⌋₊,
      (Nat.floor_lt' (Nat.ne_of_gt hQpos)).2 <| by
        calc
          (Q : ℝ) * Int.fract ((k : ℝ) * lambda j) < (Q : ℝ) * 1 :=
            mul_lt_mul_of_pos_left (Int.fract_lt_one _) hQposR
          _ = (Q : ℝ) := by ring⟩
  have hcard : (Finset.univ : Finset (Fin d → Fin Q)).card <
      (Finset.range (N + 1)).card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Finset.card_range]
    simp [N]
  have hmaps : Set.MapsTo box (↑(Finset.range (N + 1)))
      (↑(Finset.univ : Finset (Fin d → Fin Q))) := by
    intro k hk
    exact Finset.mem_univ _
  obtain ⟨u₀, hu₀, v₀, hv₀, huv, hbox⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (N + 1)) (t := Finset.univ) hcard hmaps
  have collision_bound {u v : ℕ} (hu : u < v) (hvN : v < N + 1)
      (hbox : box u = box v) :
      ∃ q : ℕ, 1 ≤ q ∧ q ≤ N ∧
        ∀ j, ∃ a : ℤ, |(q : ℝ) * lambda j - (a : ℝ)| ≤ 1 / (Q : ℝ) := by
    have hqpos : 1 ≤ v - u := by omega
    have hqle : v - u ≤ N := by omega
    refine ⟨v - u, hqpos, hqle, ?_⟩
    intro j
    have hboxj := congrArg Fin.val (congrFun hbox j)
    change ⌊(Q : ℝ) * Int.fract ((u : ℝ) * lambda j)⌋₊ =
      ⌊(Q : ℝ) * Int.fract ((v : ℝ) * lambda j)⌋₊ at hboxj
    let x : ℝ := Int.fract ((u : ℝ) * lambda j)
    let z : ℝ := Int.fract ((v : ℝ) * lambda j)
    have hx0 : 0 ≤ x := Int.fract_nonneg _
    have hz0 : 0 ≤ z := Int.fract_nonneg _
    have hxupper : (Q : ℝ) * x < (⌊(Q : ℝ) * x⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hzupper : (Q : ℝ) * z < (⌊(Q : ℝ) * z⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hxlower : (⌊(Q : ℝ) * x⌋₊ : ℝ) ≤ (Q : ℝ) * x :=
      Nat.floor_le (mul_nonneg (le_of_lt hQposR) hx0)
    have hzlower : (⌊(Q : ℝ) * z⌋₊ : ℝ) ≤ (Q : ℝ) * z :=
      Nat.floor_le (mul_nonneg (le_of_lt hQposR) hz0)
    have hxu : (Q : ℝ) * x < (⌊(Q : ℝ) * z⌋₊ : ℝ) + 1 := by
      rw [← hboxj]
      exact hxupper
    have hzx : (Q : ℝ) * z < (⌊(Q : ℝ) * x⌋₊ : ℝ) + 1 := by
      rw [hboxj]
      exact hzupper
    have hupper : x - z ≤ 1 / (Q : ℝ) := by
      apply (le_div_iff₀ hQposR).2
      nlinarith [hxu, hzlower]
    have hlower : -(1 / (Q : ℝ)) ≤ x - z := by
      apply (le_div_iff₀ hQposR).mp at hupper
      have htmp : z - x ≤ 1 / (Q : ℝ) := by
        apply (le_div_iff₀ hQposR).2
        nlinarith [hzx, hxlower]
      linarith
    have hdiff : |z - x| ≤ 1 / (Q : ℝ) := by
      rw [abs_sub_comm]
      exact abs_le.mpr ⟨hlower, hupper⟩
    refine ⟨⌊(v : ℝ) * lambda j⌋ - ⌊(u : ℝ) * lambda j⌋, ?_⟩
    have hident :
        ((v - u : ℕ) : ℝ) * lambda j -
            ((⌊(v : ℝ) * lambda j⌋ - ⌊(u : ℝ) * lambda j⌋ : ℤ) : ℝ) =
          z - x := by
      dsimp [x, z]
      simp only [Int.fract]
      rw [Nat.cast_sub (Nat.le_of_lt hu)]
      push_cast
      ring
    rw [hident]
    exact hdiff
  rcases lt_or_gt_of_ne huv with huv' | hvu'
  · exact collision_bound huv' (Finset.mem_range.mp hv₀) hbox
  · exact collision_bound hvu' (Finset.mem_range.mp hu₀) hbox.symm

theorem simultaneous_cos_alignment {d : ℕ} (lambda : Fin d → ℝ) {L : ℝ} (hL : 1 ≤ L) :
    ∃ y : ℝ, L ≤ y ∧ y ≤ L * (8 : ℝ) ^ d ∧
      ∀ j, Real.cos (Real.pi / 4) ≤ Real.cos (lambda j * y) := by
  have hQ : 1 ≤ (8 : ℕ) := by norm_num
  let lambda' : Fin d → ℝ := fun j => L * lambda j / (2 * Real.pi)
  obtain ⟨q, hqpos, hqbound, happrox⟩ := simultaneous_dirichlet hQ lambda'
  refine ⟨(q : ℝ) * L, ?_, ?_, ?_⟩
  · have hL0 : 0 ≤ L := le_trans (by norm_num) hL
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
    calc
      L = 1 * L := by ring
      _ ≤ (q : ℝ) * L := mul_le_mul_of_nonneg_right hqR hL0
  · have hL0 : 0 ≤ L := le_trans (by norm_num) hL
    have hqR : (q : ℝ) ≤ (8 ^ d : ℕ) := by exact_mod_cast hqbound
    have hmul := mul_le_mul_of_nonneg_right hqR hL0
    simpa [Nat.cast_pow, mul_comm] using hmul
  intro j
  obtain ⟨a, ha⟩ := happrox j
  have hpi : 0 < Real.pi := Real.pi_pos
  have herr : |2 * Real.pi *
      ((q : ℝ) * lambda' j - (a : ℝ))| ≤ Real.pi / 4 := by
    calc
      |2 * Real.pi * ((q : ℝ) * lambda' j - (a : ℝ))| =
          (2 * Real.pi) * |(q : ℝ) * lambda' j - (a : ℝ)| := by
            rw [abs_mul, abs_of_pos (mul_pos (by norm_num) hpi)]
      _ ≤ (2 * Real.pi) * (1 / (8 : ℝ)) :=
        mul_le_mul_of_nonneg_left ha (by positivity)
      _ = Real.pi / 4 := by ring
  have hcoserr : Real.cos (Real.pi / 4) ≤
      Real.cos (2 * Real.pi * ((q : ℝ) * lambda' j - (a : ℝ))) := by
    calc
      Real.cos (Real.pi / 4) ≤
          Real.cos |2 * Real.pi * ((q : ℝ) * lambda' j - (a : ℝ))| :=
        Real.cos_le_cos_of_nonneg_of_le_pi (x :=
          |2 * Real.pi * ((q : ℝ) * lambda' j - (a : ℝ))|)
          (y := Real.pi / 4) (abs_nonneg _) (by nlinarith [hpi]) herr
      _ = Real.cos (2 * Real.pi * ((q : ℝ) * lambda' j - (a : ℝ))) :=
        Real.cos_abs _
  have hang : lambda j * ((q : ℝ) * L) =
      2 * Real.pi * ((q : ℝ) * lambda' j - (a : ℝ)) +
        (a : ℝ) * (2 * Real.pi) := by
    dsimp [lambda']
    field_simp
    ring
  rw [hang, Real.cos_add_int_mul_two_pi]
  exact hcoserr

end D5.S3.Arith.DiophantineApproximation.SimultaneousPhaseAlignment
