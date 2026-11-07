/- GID: D5/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaSquareExponentIntegrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's three square-exponent factorial series have integer coefficients. -/

/-
result proof_shape: bind-only
escape_witness: none; the settling result uses the external open-problem basis.
admission_basis: open-problem-resolution (#27303; Proved)
Direct frozen dependencies: LinearExponentDyadicSupport.pow_change;
PowerSeriesNormalizedContraction.exists_unique_fixed;
UnitReversionSquareParity.Agree; HannaLogarithmicPowerClosure.IntegralSeries.
The claim expands the existing IntegralSeries predicate; proofs use its owner.
Declaration classifications (definitions introduce expressions, not proof content):
squarePowerSum proof_shape: bind-only; consumers: vanishingEquation.
normalized proof_shape: bind-only; consumers: vanishingEquation.
vanishingEquation proof_shape: bind-only; consumers: isSourceA350410.
isSourceA350410 proof_shape: bind-only; consumers: claim.
isSourceA350411 proof_shape: bind-only; consumers: claim.
isSourceA350412 proof_shape: bind-only; consumers: claim.
claim proof_shape: bind-only; consumers: result.
slope proof_shape: bind-only; consumers: slope_closed.
square_sign proof_shape: bind-only; consumers: slope_closed.
slope_closed proof_shape: bind-only; consumers: slope_nonzero.
slope_nonzero proof_shape: bind-only; consumers: source_unique.
pow_change_minus proof_shape: bind-only; consumers: sum_change.
sum_change proof_shape: bind-only; consumers: nextCoeff_equation.
square_derivative proof_shape: bind-only; consumers: last_divisibility.
last_divisibility proof_shape: bind-only; consumers: nextCoeff_equation.
cleared proof_shape: bind-only; consumers: cleared_spec.
cleared_spec proof_shape: bind-only; consumers: nextCoeff_equation.
nextCoeff proof_shape: bind-only; consumers: step.
step proof_shape: bind-only; consumers: step_contract.
step_contract proof_shape: bind-only; consumers: source_exists.
nextCoeff_equation proof_shape: bind-only; consumers: source_exists.
source_exists proof_shape: bind-only; consumers: all_for_cutoff.
source_unique proof_shape: bind-only; consumers: all_for_cutoff.
all_for_cutoff proof_shape: bind-only; consumers: result.
translate_source proof_shape: bind-only; consumers: result.
translate_integral proof_shape: bind-only; consumers: result.
result proof_shape: bind-only; consumers: settlement of A350410, A350411 and A350412.
Every helper has escape_witness none; only result supplies the settlement.

Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27346.
-/
import D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport
import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure

/-! Integer coefficients of three rational square-exponent factorial series. -/

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.HannaSquareExponentIntegrality

open scoped BigOperators

noncomputable def squarePowerSum (M : ℕ) (B : PowerSeries ℚ) : PowerSeries ℚ :=
  ∑ m ∈ Finset.range (M + 1), (1 / (Nat.factorial m : ℚ)) • B ^ (m * m)

def normalized (B : PowerSeries ℚ) : Prop :=
  PowerSeries.constantCoeff B = (-1 : ℚ) ∧ PowerSeries.coeff 1 B = 1

def vanishingEquation (cutoff : ℕ → ℕ) (B : PowerSeries ℚ) : Prop :=
  normalized B ∧ ∀ n : ℕ, 2 ≤ n →
    PowerSeries.coeff n (squarePowerSum (cutoff n) B) = 0

def isSourceA350410 (A : PowerSeries ℚ) : Prop :=
  vanishingEquation (fun n => n) A

def isSourceA350411 (A : PowerSeries ℚ) : Prop :=
  vanishingEquation (fun n => n + 1) A

def isSourceA350412 (A : PowerSeries ℚ) : Prop :=
  PowerSeries.constantCoeff A = 0 ∧ PowerSeries.coeff 1 A = 1 ∧
    ∀ n : ℕ, 2 ≤ n →
      PowerSeries.coeff n (squarePowerSum (2 * n) (A - 1)) = 0

def claim : Prop :=
  (∃ A : PowerSeries ℚ, isSourceA350410 A ∧ ∀ A' : PowerSeries ℚ, isSourceA350410 A' → A' = A) ∧
  (∀ A : PowerSeries ℚ, isSourceA350410 A → (∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n A = (z : ℚ))) ∧
  (∃ A : PowerSeries ℚ, isSourceA350411 A ∧ ∀ A' : PowerSeries ℚ, isSourceA350411 A' → A' = A) ∧
  (∀ A : PowerSeries ℚ, isSourceA350411 A → (∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n A = (z : ℚ))) ∧
  (∃ A : PowerSeries ℚ, isSourceA350412 A ∧ ∀ A' : PowerSeries ℚ, isSourceA350412 A' → A' = A) ∧
  (∀ A : PowerSeries ℚ, isSourceA350412 A → (∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n A = (z : ℚ)))

end D5.S1.Recurrence.Algebraic.HannaSquareExponentIntegrality

set_option maxRecDepth 2000

namespace D5.S1.Recurrence.Algebraic.HannaSquareExponentIntegrality
open PowerSeries
open D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure (IntegralSeries)
open scoped BigOperators
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity
noncomputable section

private def slope (M : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (M + 1), -((-1 : ℚ) ^ (m * m)) * (m * m : ℕ) / Nat.factorial m

private theorem square_sign (m : ℕ) : (-1 : ℚ) ^ (m * m) = (-1 : ℚ) ^ m := by
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two m]
  rw [Nat.mul_mod]
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;> norm_num [hm]

private theorem slope_closed (k : ℕ) : slope (k + 1) = (-1 : ℚ) ^ k / Nat.factorial k := by
  let f : ℕ → ℚ := fun m => if m = 0 then 0 else (-1 : ℚ) ^ (m - 1) / Nat.factorial (m - 1)
  have ht (m : ℕ) : -((-1 : ℚ) ^ ((m + 1) * (m + 1))) *
      ((m + 1) * (m + 1) : ℕ) / Nat.factorial (m + 1) = f (m + 1) - f m := by
    rw [square_sign]
    cases m with
    | zero => norm_num [f]
    | succ m =>
      have hf : (Nat.factorial m : ℚ) ≠ 0 := by positivity
      have hm1 : (m : ℚ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero m
      have hm2 : (m : ℚ) + 1 + 1 ≠ 0 := by positivity
      simp [f, Nat.factorial_succ, pow_succ]
      field_simp
      ring
  rw [slope, Finset.sum_range_succ']
  simp only [ht, Nat.cast_zero, mul_zero, zero_div, add_zero]
  rw [Finset.sum_range_sub]
  simp [f]

private theorem slope_nonzero {M : ℕ} (hM : 1 ≤ M) : slope M ≠ 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : M ≠ 0)
  rw [slope_closed]
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)

private theorem pow_change_minus {n : ℕ} {F G : PowerSeries ℚ}
    (hF : constantCoeff F = -1) (hG : constantCoeff G = -1)
    (h : Agree n F G) (e : ℕ) :
    coeff n (F ^ e) - coeff n (G ^ e) =
      -((-1 : ℚ) ^ e) * (e : ℚ) * (coeff n F - coeff n G) := by
  have hh := D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport.pow_change
    (F := -F) (G := -G) (by simpa using congrArg Neg.neg hF)
    (by simpa using congrArg Neg.neg hG)
    (fun j hj => by simpa using congrArg Neg.neg (h j hj)) e
  have he (H : PowerSeries ℚ) : coeff n ((-H) ^ e) = (-1 : ℚ) ^ e * coeff n (H ^ e) := by
    have hp : (-H) ^ e = C ((-1 : ℚ) ^ e) * H ^ e := by
      rw [neg_pow H e]
      simp only [map_pow, map_neg, map_one]
    rw [hp, coeff_C_mul]
  rw [he, he, map_neg, map_neg] at hh
  have hs : (-1 : ℚ) ^ e * (-1 : ℚ) ^ e = 1 := by
    rw [← mul_pow]; norm_num
  have hh' := congrArg (fun q : ℚ => (-1 : ℚ) ^ e * q) hh
  simp only [mul_sub, ← mul_assoc, hs, one_mul] at hh'
  linear_combination hh'

private theorem sum_change {n : ℕ} {F G : PowerSeries ℚ}
    (hF : constantCoeff F = -1) (hG : constantCoeff G = -1)
    (h : Agree n F G) (M : ℕ) :
    coeff n (squarePowerSum M F) - coeff n (squarePowerSum M G) =
      slope M * (coeff n F - coeff n G) := by
  simp only [squarePowerSum, map_sum, map_smul, smul_eq_mul, slope]
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  have hh := pow_change_minus hF hG h (m * m)
  push_cast at hh ⊢
  linear_combination (1 / (Nat.factorial m : ℚ)) * hh

private theorem square_derivative (F : PowerSeries ℤ) (n M : ℕ) (hn : 0 < n) :
    (n : ℤ) * coeff n (F ^ (M * M)) = (M : ℤ) * M *
      coeff (n - 1) (F ^ (M * M - 1) * PowerSeries.derivative F) := by
  have h := congrArg (coeff (n - 1)) (derivative_pow F (M * M))
  rw [coeff_derivative, Nat.sub_add_cancel hn, mul_assoc] at h
  have hc : ((M * M : ℕ) : PowerSeries ℤ) = C ((M : ℤ) * M) := by simp
  rw [hc, coeff_C_mul] at h
  have hncast : ((n - 1 : ℕ) : ℤ) + 1 = n := by
    exact_mod_cast Nat.sub_add_cancel hn
  simpa [mul_comm, hncast] using h

private theorem last_divisibility (F : PowerSeries ℤ) {n M : ℕ}
    (hn : 0 < n) (hM : M = n ∨ M = n + 1 ∨ M = 2 * n) :
    (M : ℤ) ∣ coeff n (F ^ (M * M)) := by
  have hd := square_derivative F n M hn
  have hnz : (n : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.mpr hn
  let c := coeff n (F ^ (M * M))
  let d := coeff (n - 1) (F ^ (M * M - 1) * PowerSeries.derivative F)
  change (n : ℤ) * c = (M : ℤ) * M * d at hd
  change (M : ℤ) ∣ c
  rcases hM with hM | hM | hM <;> subst M
  · refine ⟨d, ?_⟩
    apply mul_left_cancel₀ hnz
    nlinarith [hd]
  · refine ⟨c - (n + 1 : ℤ) * d, ?_⟩
    push_cast at hd ⊢
    linear_combination -hd
  · refine ⟨2 * d, ?_⟩
    apply mul_left_cancel₀ hnz
    push_cast at hd ⊢
    nlinarith [hd]


private def cleared (M n : ℕ) (F : PowerSeries ℤ) : ℤ :=
  (∑ m ∈ Finset.range M,
    (Nat.factorial (M - 1) / Nat.factorial m : ℕ) * coeff n (F ^ (m * m))) +
    coeff n (F ^ (M * M)) / (M : ℤ)

private theorem cleared_spec (F : PowerSeries ℤ) {n M : ℕ} (hM : 1 ≤ M)
    (hd : (M : ℤ) ∣ coeff n (F ^ (M * M))) :
    (Nat.factorial (M - 1) : ℚ) *
      coeff n (squarePowerSum M ((PowerSeries.map (Int.castRingHom ℚ)) F)) =
      (cleared M n F : ℚ) := by
  have hc (m : ℕ) : coeff n ((PowerSeries.map (Int.castRingHom ℚ)) F ^ (m * m)) =
      (coeff (R := ℤ) n (F ^ (m * m)) : ℚ) := by
    simp only [← map_pow, coeff_map]
    rfl
  simp only [squarePowerSum, map_sum, map_smul, smul_eq_mul, hc]
  rw [Finset.sum_range_succ, mul_add, Finset.mul_sum]
  simp only [cleared, Int.cast_add, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    rw [Nat.cast_div_charZero (Nat.factorial_dvd_factorial (by
      have := Finset.mem_range.mp hm
      omega))]
    ring
  · rw [Int.cast_div hd (by exact_mod_cast (by omega : M ≠ 0))]
    have hf : (Nat.factorial (M - 1) : ℚ) ≠ 0 := by positivity
    have hm : (M : ℚ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
    have hfac := congrArg (fun t : ℕ => (t : ℚ))
      (Nat.mul_factorial_pred (by omega : M ≠ 0))
    push_cast at hfac
    rw [← hfac]
    field_simp
    push_cast
    ring

private def nextCoeff (cutoff : ℕ → ℕ) (n : ℕ) (F : PowerSeries ℤ) : ℤ :=
  (-1 : ℤ) ^ (cutoff n) * cleared (cutoff n) n (trunc n F)

private def step (cutoff : ℕ → ℕ) (U : PowerSeries ℤ) : PowerSeries ℤ :=
  mk fun n => if n = 0 then 1 else if n = 1 then -1 else -(nextCoeff cutoff n (-U))

private theorem step_contract (cutoff : ℕ → ℕ) {d : ℕ}
    {U V : PowerSeries ℤ} (h : Agree d U V) :
    Agree (d + 1) (step cutoff U) (step cutoff V) := by
  intro n hn
  have ht : trunc n (-U) = trunc n (-V) := by
    apply Polynomial.ext
    intro j
    simp only [Polynomial.coeff_neg, map_neg, coeff_trunc]
    split_ifs with hj
    · rw [h j (by omega)]
    · rfl
  simp only [step, coeff_mk]
  split_ifs <;> try rfl
  simp only [nextCoeff, ht]

private theorem nextCoeff_equation (cutoff : ℕ → ℕ)
    (hcut : ∀ n, 2 ≤ n → cutoff n = n ∨ cutoff n = n + 1 ∨ cutoff n = 2 * n)
    (F : PowerSeries ℤ) (hF : constantCoeff F = -1) {n : ℕ} (hn : 2 ≤ n) :
    coeff n (squarePowerSum (cutoff n) ((PowerSeries.map (Int.castRingHom ℚ)) F)) = 0 ↔
      coeff n F = nextCoeff cutoff n F := by
  let G : PowerSeries ℤ := trunc n F
  have hG : constantCoeff G = -1 := by
    simpa [G, coeff_trunc, show 0 < n by omega] using hF
  have hg : Agree n ((PowerSeries.map (Int.castRingHom ℚ)) F)
      ((PowerSeries.map (Int.castRingHom ℚ)) G) := by
    intro j hj
    simp [G, coeff_trunc, hj]
  have hfc : constantCoeff ((PowerSeries.map (Int.castRingHom ℚ)) F) = -1 := by
    exact Eq.symm (Rat.ext (id (Eq.symm hF)) rfl)
  have hgc : constantCoeff ((PowerSeries.map (Int.castRingHom ℚ)) G) = -1 := by
    exact Eq.symm (Rat.ext (id (Eq.symm hG)) rfl)
  have hg0 : coeff n ((PowerSeries.map (Int.castRingHom ℚ)) G) = 0 := by simp [G, coeff_trunc]
  have hM : 2 ≤ cutoff n := by rcases hcut n hn with h | h | h <;> omega
  have hs := sum_change hfc hgc hg (cutoff n)
  rw [hg0, sub_zero] at hs
  have hclear := cleared_spec G (by omega : 1 ≤ cutoff n)
    (last_divisibility G (by omega : 0 < n) (hcut n hn))
  have hsign : (-1 : ℚ) ^ (cutoff n) = -((-1 : ℚ) ^ (cutoff n - 1)) := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ cutoff n), pow_succ]
    ring
  have hslope : slope (cutoff n) = (-1 : ℚ) ^ (cutoff n - 1) /
      Nat.factorial (cutoff n - 1) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ cutoff n)] using
      slope_closed (cutoff n - 1)
  have hnorm : (Nat.factorial (cutoff n - 1) : ℚ) * slope (cutoff n) =
      (-1 : ℚ) ^ (cutoff n - 1) := by
    rw [hslope]
    field_simp
  have hsg : (-1 : ℚ) ^ (cutoff n - 1) * (-1 : ℚ) ^ (cutoff n - 1) = 1 := by
    rw [← mul_pow]; norm_num
  have hnx : (nextCoeff cutoff n F : ℚ) =
      (-1 : ℚ) ^ (cutoff n) * (cleared (cutoff n) n G : ℚ) := by
    simp [nextCoeff, G]
  have hcoeff : coeff n ((PowerSeries.map (Int.castRingHom ℚ)) F) =
      (coeff (R := ℤ) n F : ℚ) := Eq.symm (Rat.ext rfl rfl)
  rw [← Int.cast_inj (α := ℚ), hnx]
  rw [hsign]
  constructor
  · intro hz
    rw [hz, hcoeff] at hs
    have h := congrArg (fun t : ℚ => (Nat.factorial (cutoff n - 1) : ℚ) * t) hs
    rw [mul_sub, hclear, ← mul_assoc, hnorm] at h
    have hh := congrArg (fun t : ℚ => (-1 : ℚ) ^ (cutoff n - 1) * t) h
    simp only [mul_sub, ← mul_assoc, hsg, one_mul, mul_zero] at hh
    linear_combination -hh
  · intro heq
    have h := congrArg (fun t : ℚ => (Nat.factorial (cutoff n - 1) : ℚ) * t) hs
    rw [mul_sub, hclear, ← mul_assoc, hnorm, hcoeff, heq] at h
    have hf : (Nat.factorial (cutoff n - 1) : ℚ) ≠ 0 := by positivity
    apply (mul_eq_zero.mp (show (Nat.factorial (cutoff n - 1) : ℚ) *
      coeff n (squarePowerSum (cutoff n) ((PowerSeries.map (Int.castRingHom ℚ)) F)) = 0 by
        have hmul : (-1 : ℚ) ^ (cutoff n - 1) *
          (-((-1 : ℚ) ^ (cutoff n - 1)) * (cleared (cutoff n) n G : ℚ)) =
          -(cleared (cutoff n) n G : ℚ) := by
          calc
            _ = -(((-1 : ℚ) ^ (cutoff n - 1) * (-1 : ℚ) ^ (cutoff n - 1)) *
              (cleared (cutoff n) n G : ℚ)) := by ring
            _ = _ := by rw [hsg]; ring
        rw [hmul] at h
        linear_combination h)).resolve_left hf

private theorem source_exists (cutoff : ℕ → ℕ)
    (hcut : ∀ n, 2 ≤ n → cutoff n = n ∨ cutoff n = n + 1 ∨ cutoff n = 2 * n) :
    ∃ B : PowerSeries ℚ, vanishingEquation cutoff B ∧ IntegralSeries B := by
  obtain ⟨U, hU0, hfix, _hunique⟩ :=
    D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed
      (step cutoff) (fun _ _ => by simp [step, constantCoeff_mk])
      (fun _ _ _ h => step_contract cutoff h)
  have hF0 : constantCoeff (-U) = -1 := by
    exact Eq.symm ((fun {a b} => Int.neg_inj.mp)
      (congrArg Neg.neg (congrArg Neg.neg (id (Eq.symm hU0)))))
  have hF1 : coeff 1 (-U) = 1 := by
    have h := congrArg (coeff 1) hfix
    simp [step] at h
    simp [h]
  refine ⟨(PowerSeries.map (Int.castRingHom ℚ)) (-U), ⟨?_, ?_⟩, ?_⟩
  · constructor
    · rw [← coeff_zero_eq_constantCoeff, coeff_map]
      rw [coeff_zero_eq_constantCoeff, hF0]
      norm_num
    · rw [coeff_map, hF1]
      norm_num
  · intro n hn
    apply (nextCoeff_equation cutoff hcut (-U) hF0 hn).mpr
    have h := congrArg (coeff n) hfix
    simp only [step, coeff_mk, ite_eq_right (by omega : n ≠ 0),
      ite_eq_right (by omega : n ≠ 1)] at h
    simpa only [map_neg, neg_neg] using congrArg Neg.neg h
  · intro n
    exact ⟨coeff n (-U), by simp []⟩

private theorem source_unique (cutoff : ℕ → ℕ)
    (hcut : ∀ n, 2 ≤ n → 1 ≤ cutoff n) {B G : PowerSeries ℚ}
    (hB : vanishingEquation cutoff B) (hG : vanishingEquation cutoff G) : B = G := by
  let T : PowerSeries ℚ → PowerSeries ℚ := fun U => mk fun n =>
    if n = 0 then 1 else if n = 1 then -1 else
      coeff n (squarePowerSum (cutoff n) (trunc n (-U))) / slope (cutoff n)
  obtain ⟨f, _hf0, _hf, huniq⟩ :=
    D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed T
      (fun _ _ => by simp [T, constantCoeff_mk]) (by
        intro d U V _hd _hU _hV h n hn
        have ht : trunc n (-U) = trunc n (-V) := by
          apply Polynomial.ext
          intro j
          simp only [Polynomial.coeff_neg, map_neg, coeff_trunc]
          split_ifs with hj
          · rw [h j (by omega)]
          · rfl
        simp only [T, coeff_mk]
        split_ifs <;> try rfl
        rw [ht])
  have fixed (A : PowerSeries ℚ) (hA : vanishingEquation cutoff A) : -A = T (-A) := by
    apply PowerSeries.ext
    intro n
    by_cases hn0 : n = 0
    · subst n
      simp [T, hA.1.1]
    by_cases hn1 : n = 1
    · subst n
      simp [T, hA.1.2]
    have hn : 2 ≤ n := by omega
    let C : PowerSeries ℚ := trunc n A
    have hC0 : constantCoeff C = -1 := by
      simpa [C, coeff_trunc, show 0 < n by omega] using hA.1.1
    have hAC : Agree n A C := by
      intro j hj
      simp [C, coeff_trunc, hj]
    have hCn : coeff n C = 0 := by simp [C, coeff_trunc]
    have hs := sum_change hA.1.1 hC0 hAC (cutoff n)
    rw [hA.2 n hn, hCn, sub_zero, zero_sub] at hs
    simp only [T, coeff_mk, ite_eq_right hn0, ite_eq_right hn1, map_neg, neg_neg]
    change -coeff n A = coeff n (squarePowerSum (cutoff n) C) / slope (cutoff n)
    apply (eq_div_iff (slope_nonzero (hcut n hn))).mpr
    linear_combination hs
  have eB := huniq (-B) (by simp [hB.1.1]) (fixed B hB)
  have eG := huniq (-G) (by simp [hG.1.1]) (fixed G hG)
  exact neg_injective (eB.trans eG.symm)

private theorem all_for_cutoff (cutoff : ℕ → ℕ)
    (hcut : ∀ n, 2 ≤ n → cutoff n = n ∨ cutoff n = n + 1 ∨ cutoff n = 2 * n) :
    (∃ B : PowerSeries ℚ, vanishingEquation cutoff B ∧
      ∀ B' : PowerSeries ℚ, vanishingEquation cutoff B' → B' = B) ∧
    (∀ B : PowerSeries ℚ, vanishingEquation cutoff B → IntegralSeries B) := by
  obtain ⟨B, hB, hI⟩ := source_exists cutoff hcut
  have hM : ∀ n, 2 ≤ n → 1 ≤ cutoff n := by
    intro n hn
    rcases hcut n hn with h | h | h <;> omega
  refine ⟨⟨B, hB, fun _ hG => source_unique cutoff hM hG hB⟩, ?_⟩
  intro G hG
  rw [source_unique cutoff hM hG hB]
  exact hI

private theorem translate_source (B : PowerSeries ℚ) :
    isSourceA350412 (B + 1) ↔ vanishingEquation (fun n => 2 * n) B := by
  simp only [isSourceA350412, vanishingEquation, normalized, map_add,
    map_one, coeff_one, Nat.one_ne_zero, ite_false, add_zero,
    add_sub_cancel_right]
  constructor
  · rintro ⟨h0, h1, hE⟩
    exact ⟨⟨by linarith, h1⟩, hE⟩
  · rintro ⟨⟨h0, h1⟩, hE⟩
    exact ⟨by linarith, h1, hE⟩

private theorem translate_integral {B : PowerSeries ℚ} (h : IntegralSeries B) :
    IntegralSeries (B + 1) := by
  intro n
  obtain ⟨z, hz⟩ := h n
  by_cases hn : n = 0
  · subst n
    refine ⟨z + 1, ?_⟩
    rw [coeff_zero_eq_constantCoeff] at hz
    simp [hz]
  · refine ⟨z, ?_⟩
    simp [hz, hn]

theorem result : claim := by
  obtain ⟨h10, h10I⟩ := all_for_cutoff (fun n => n) (fun _ _ => Or.inl rfl)
  obtain ⟨h11, h11I⟩ := all_for_cutoff (fun n => n + 1) (fun _ _ => Or.inr (Or.inl rfl))
  obtain ⟨⟨B, hB, hBu⟩, h12I⟩ := all_for_cutoff (fun n => 2 * n)
    (fun _ _ => Or.inr (Or.inr rfl))
  refine ⟨h10, h10I, h11, h11I, ?_, ?_⟩
  · refine ⟨B + 1, (translate_source B).mpr hB, ?_⟩
    intro A hA
    have h : vanishingEquation (fun n => 2 * n) (A - 1) := by
      apply (translate_source (A - 1)).mp
      simpa only [sub_add_cancel] using hA
    have hu := hBu (A - 1) h
    linear_combination hu
  · intro A hA
    have h : vanishingEquation (fun n => 2 * n) (A - 1) := by
      apply (translate_source (A - 1)).mp
      simpa only [sub_add_cancel] using hA
    have hI := translate_integral (h12I (A - 1) h)
    simpa only [IntegralSeries, sub_add_cancel] using hI

end
end D5.S1.Recurrence.Algebraic.HannaSquareExponentIntegrality
