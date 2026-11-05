/- GID: D5/S1/Recurrence/LinearRows/QuadrupledLinearExponentDyadicSupport
   generality: I
   mirror-B: D5/B/S1/Recurrence/LinearRows/QuadrupledLinearExponentDyadicSupport
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's quadrupled-row integer series has dyadic-neighbor odd support. -/

/-
result:
  proof_shape: bind-only; existing fixed-point construction, normalization and parity owners.
  escape_witness: none; the fixed-point and homogeneous dyadic-support theorems are reused.
  admission_basis: open-problem-resolution (#22490; Proved)
  Direct frozen dependencies: D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport.
    Agree, generatingSeries, generating_equation, hanna_conjecture,
    advance, advance_zero, advance_agree, exact_normalization,
    geom, geom_map, geom_inverse, normalized, normalized_map, normalized_unique,
    row, row.eq_1, solution, solution_zero, solution_normalized.
  D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.exists_unique_fixed.
  D5/S1/Recurrence/Invariants/UnitReversionSquareParity.Agree.
IsSourceSeries and claim retain the source's rational rescaling and full quantifiers.
The proof uses the existing row and normalized operators through the imported owners.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22657.
-/

import Batteries.Tactic.OpenPrivate
import D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport
import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity

open PowerSeries
open D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport
open private geom geom_map geom_inverse row normalized exact_normalization
  advance advance_zero advance_agree normalized_unique
  normalized_map solution solution_zero solution_normalized from
  D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport

noncomputable section
namespace D5.S1.Recurrence.LinearRows.QuadrupledLinearExponentDyadicSupport

def IsSourceSeries (A : PowerSeries ℤ) : Prop :=
  PowerSeries.constantCoeff A = 1 ∧
    ∀ m : ℕ, 0 < m →
      (Finset.range m).sum (fun j : ℕ => PowerSeries.coeff j
        ((PowerSeries.rescale (((m : ℚ)⁻¹))
          (A.map (Int.castRingHom ℚ))) ^ m)) = (4 : ℚ) ^ (m - 1)

def claim : Prop :=
  (∃ A : PowerSeries ℤ, IsSourceSeries A) ∧
    ∀ A : PowerSeries ℤ, IsSourceSeries A →
      ∀ n : ℕ, 3 < n →
        (Odd (PowerSeries.coeff n A) ↔
          ∃ k : ℕ, 1 < k ∧ (n = 2 ^ k - 1 ∨ n = 2 ^ k + 1))

theorem result : D5.S1.Recurrence.LinearRows.QuadrupledLinearExponentDyadicSupport.claim := by
  classical
  change (∃ A : PowerSeries ℤ, IsSourceSeries A) ∧
    ∀ A : PowerSeries ℤ, IsSourceSeries A →
      ∀ n : ℕ, 3 < n →
        (Odd (PowerSeries.coeff n A) ↔
          ∃ k : ℕ, 1 < k ∧ (n = 2 ^ k - 1 ∨ n = 2 ^ k + 1))
  -- First clear the NAME denominators, retaining all positive rows.
  have hscale (A : PowerSeries Int) (n : Nat) :
      ((n + 1 : Nat) : Rat)^n *
        (Finset.range (n+1)).sum (fun j => coeff j
          ((rescale (((n+1 : Nat) : Rat)⁻¹)
            (A.map (Int.castRingHom Rat)))^(n+1))) = ((row A n : Int) : Rat) := by
    have hm : ((n+1 : Nat) : Rat) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have hmap : row (A.map (Int.castRingHom Rat)) n = ((row A n : Int) : Rat) := by
      simp only [row, ← geom_map (Int.castRingHom Rat), ← map_pow, ← map_mul, coeff_map]
      rfl
    rw [← hmap, row, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [← map_pow, coeff_rescale, geom, coeff_mk, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Finset.mem_range_succ_iff.mp hj
    rw [pow_sub₀ _ hm hjn, inv_pow]
    ring
  -- This is the complete equivalence with the source's formula (2), using its
  -- constant-one formal inverse, rather than an assumed alternative source.
  have hname_row (A : PowerSeries Int) : IsSourceSeries A ↔
      constantCoeff A = 1 ∧ ∀ m : Nat, 0 < m →
        coeff (m-1) (A^m * invOfUnit (1-C (m : Int)*X) 1) =
          (4 * (m : Int))^(m-1) := by
    have hr (n : Nat) : row A n =
        coeff n (A^(n+1) * invOfUnit (1-C ((n+1 : Nat) : Int)*X) 1) := by
      rw [row, geom_inverse]
    constructor
    · rintro ⟨h0, hA⟩
      refine ⟨h0, ?_⟩
      intro m hm
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
      have h := hscale A n
      rw [hA (n+1) (by omega), Nat.add_sub_cancel] at h
      have h' : row A n = (4 * ((n+1 : Nat) : Int))^n := by
        apply Int.cast_injective (α := Rat)
        push_cast
        rw [← h, mul_pow]
        push_cast
        ring
      simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, hr] using h'
    · rintro ⟨h0, hA⟩
      refine ⟨h0, ?_⟩
      intro m hm
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
      have h := hscale A n
      have ha := hA (n+1) (by omega)
      simp only [Nat.add_sub_cancel] at ha
      rw [hr, ha] at h
      have hm' : (((n+1 : Nat) : Rat)^n) ≠ 0 :=
        pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
      apply (mul_left_cancel₀ hm')
      simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Int.cast_pow,
        Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, mul_pow, mul_comm] using h
  let t : Nat → Int := fun n => 4^n * ((n+1 : Nat) : Int)^(n-1)
  have hfactor (n : Nat) (hn : 0 < n) :
      (4 * ((n+1 : Nat) : Int))^n = ((n+1 : Nat) : Int) * t n := by
    dsimp [t]
    have hp : ((n+1 : Nat) : Int)^n = ((n+1 : Nat) : Int) * ((n+1 : Nat) : Int)^(n-1) := by
      rw [← pow_succ', Nat.sub_add_cancel hn]
    simp only [Nat.cast_add, Nat.cast_one] at hp
    rw [mul_pow, hp]
    ring
  have hnormalized (A : PowerSeries Int) : IsSourceSeries A ↔
      constantCoeff A = 1 ∧ ∀ n : Nat, 0 < n → normalized A n = t n := by
    rw [hname_row]
    constructor
    · rintro ⟨h0, hA⟩
      refine ⟨h0, ?_⟩
      intro n hn
      have h := hA (n+1) (by omega)
      rw [← geom_inverse, Nat.add_sub_cancel] at h
      change row A n = _ at h
      rw [exact_normalization A n hn, hfactor n hn] at h
      exact mul_left_cancel₀ (by positivity : ((n+1 : Nat) : Int) ≠ 0) h
    · rintro ⟨h0, hA⟩
      refine ⟨h0, ?_⟩
      intro m hm
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
      cases n with
      | zero => simpa using h0
      | succ n =>
        rw [← geom_inverse]
        change row A (n+1) = (4 * ((n+1+1 : Nat) : Int))^(n+1)
        rw [exact_normalization A (n+1) (by omega), hA (n+1) (by omega),
          hfactor (n+1) (by omega)]
  -- Integer iteration: the forcing term is added after the existing advance.
  let forcing : PowerSeries Int := mk fun n => if n=0 then 0 else t n
  let step : PowerSeries Int → PowerSeries Int := fun F => advance F + forcing
  have step_zero (F : PowerSeries Int) : constantCoeff (step F) = 1 := by
    simp [step, forcing, advance_zero]
  have step_agree {d : Nat} {F G : PowerSeries Int}
      (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (h : Agree d F G) :
      Agree (d+1) (step F) (step G) := by
    intro k hk
    simpa only [step, map_add] using
      congrArg (fun z : Int => z + coeff k forcing) (advance_agree hF hG h k hk)
  obtain ⟨A, A_zero, A_fixed, _⟩ :=
    D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed
      step (fun F _ => step_zero F)
      (fun _ hF hG h => step_agree hF hG h)
  have A_normalized (n : Nat) (hn : 0 < n) : normalized A n = t n := by
    have h := congrArg (coeff n) A_fixed
    simp only [step, map_add, advance, forcing, coeff_mk, if_neg (by omega : n ≠ 0)] at h
    linear_combination h
  have A_source : IsSourceSeries A := (hnormalized A).mpr ⟨A_zero, A_normalized⟩
  refine ⟨⟨A, A_source⟩, ?_⟩
  intro B hB n hn
  obtain ⟨B_zero, B_normalized⟩ := (hnormalized B).mp hB
  -- Reduction takes place only after normalization over the integers.
  have hmod : B.map (Int.castRingHom (ZMod 2)) =
      (solution (R := Int)).map (Int.castRingHom (ZMod 2)) := by
    apply normalized_unique
    · rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, B_zero, map_one]
    · rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
        solution_zero, map_one]
    · intro j hj
      rw [normalized_map, B_normalized j hj]
      have ht : (Int.castRingHom (ZMod 2)) (t j) = 0 := by
        have hj0 : j ≠ 0 := Nat.ne_of_gt hj
        simp only [t, map_mul, map_pow]
        have h4 : (Int.castRingHom (ZMod 2)) (4 : Int) = 0 :=
          (ZMod.val_eq_zero ((Int.castRingHom (ZMod 2)) 4)).mp rfl
        rw [h4, zero_pow hj0, zero_mul]
      exact ht
    · intro j hj
      rw [normalized_map, solution_normalized j hj, map_zero]
  have hc : ((coeff n B : Int) : ZMod 2) = ((coeff n generatingSeries : Int) : ZMod 2) := by
    have h := congrArg (coeff n) hmod
    simpa only [coeff_map, Int.coe_castRingHom, generatingSeries, map_sub, coeff_one,
      if_neg (by omega : n ≠ 0), zero_sub, Int.cast_neg, CharTwo.neg_eq] using h
  rw [← ZMod.intCast_eq_one_iff_odd, hc, ZMod.intCast_eq_one_iff_odd]
  exact hanna_conjecture generatingSeries generating_equation n hn

end D5.S1.Recurrence.LinearRows.QuadrupledLinearExponentDyadicSupport
