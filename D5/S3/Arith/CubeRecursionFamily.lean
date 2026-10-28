/- GID: D5/S3/Arith/CubeRecursionFamily
   generality: G
   mirror-B: D5/B/S3/Arith/CubeRecursionFamily
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Rat.Lemmas, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Positive rational cubic recursions preserve their exact reduced pairs and have a uniform cube sum. -/

import D5.S3.Arith.CubeRecursionProjective
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-! # Positive rational cubic recursions

The reduced numerator plus denominator of each positive iterate is an integer cube.
-/

namespace D5.S3.Arith.CubeRecursionFamily

/-- The autonomous rational recursion, with nonnegative integer parameter. -/
def step (t : ℕ) (x : ℚ) : ℚ :=
  (x + t) / ((x + t + 1) ^ 3 - (x + t))

/-- The positive numerator before reduction. -/
def nextA (t a b : ℕ) : ℕ := (a + t * b) * b ^ 2

/-- Expanded form of the positive denominator. -/
def nextB (t a b : ℕ) : ℕ :=
  (a + t * b) ^ 3 + 3 * (a + t * b) ^ 2 * b +
    2 * (a + t * b) * b ^ 2 + b ^ 3

private theorem pair_sum (t a b : ℕ) :
    nextA t a b + nextB t a b = (a + (t + 1) * b) ^ 3 := by
  simp only [nextA, nextB]
  ring

private theorem pair_positive (t a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    0 < nextA t a b ∧ 0 < nextB t a b := by
  constructor
  · unfold nextA; positivity
  · unfold nextB; positivity

private theorem pair_coprime (t a b : ℕ) (h : a.Coprime b) :
    (nextA t a b).Coprime (nextB t a b) := by
  let u := a + t * b
  have hub : u.Coprime b := (Nat.coprime_add_mul_right_left a b t).mpr h
  have huw : u.Coprime (u + b) := Nat.coprime_self_add_right.mpr hub
  have hbw : b.Coprime (u + b) := Nat.coprime_add_self_right.mpr hub.symm
  have hc : (u * b ^ 2).Coprime ((u + b) ^ 3) :=
    huw.pow_right 3 |>.mul_left (hbw.pow 2 3)
  have he : (u + b) ^ 3 = nextB t a b + nextA t a b := by
    dsimp [u, nextA, nextB]
    ring
  rw [he] at hc
  exact Nat.coprime_add_self_right.mp hc

private theorem step_pair (t a b : ℕ) (hb : 0 < b) :
    step t ((a : ℚ) / b) = (nextA t a b : ℚ) / nextB t a b := by
  have hb0 : (b : ℚ) ≠ 0 := by positivity
  have hd : ((a : ℚ) / b + t + 1) ^ 3 - ((a : ℚ) / b + t) =
      (nextB t a b : ℚ) / (b : ℚ) ^ 3 := by
    simp only [nextB, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
    ring
  unfold step
  rw [hd]
  simp only [nextA, Nat.cast_mul, Nat.cast_add, Nat.cast_pow]
  field_simp

/-- A step has exactly the displayed positive coprime numerator and denominator. -/
theorem reduced_step (t a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a.Coprime b) :
    0 < step t ((a : ℚ) / b) ∧
    (step t ((a : ℚ) / b)).num = (nextA t a b : ℤ) ∧
    (step t ((a : ℚ) / b)).den = nextB t a b ∧
    (nextA t a b).Coprime (nextB t a b) ∧
    nextA t a b + nextB t a b = (a + (t + 1) * b) ^ 3 := by
  have hp := pair_positive t a b ha hb
  have hc := pair_coprime t a b h
  rw [step_pair t a b hb]
  have hn : (((nextA t a b : ℤ) : ℚ) / (nextB t a b : ℤ)).num =
      (nextA t a b : ℤ) :=
    Rat.num_div_eq_of_coprime (by exact_mod_cast hp.2) (by simpa using hc)
  have hd : ((((nextA t a b : ℤ) : ℚ) / (nextB t a b : ℤ)).den : ℤ) =
      (nextB t a b : ℤ) :=
    Rat.den_div_eq_of_coprime (by exact_mod_cast hp.2) (by simpa using hc)
  simp only [Int.cast_natCast] at hn hd
  have hd' : ((nextA t a b : ℚ) / nextB t a b).den = nextB t a b := Int.ofNat_inj.mp hd
  exact ⟨div_pos (by exact_mod_cast hp.1) (by exact_mod_cast hp.2), hn, hd', hc,
    pair_sum t a b⟩

/-- The actual iterates, starting at index zero. -/
def orbit (t : ℕ) (x : ℚ) (n : ℕ) : ℚ := (step t)^[n] x

/-- Positivity and the exact integer cube identity for the actual reduced pair. -/
theorem positive_orbit_cube (t : ℕ) (x : ℚ) (hx : 0 < x) :
    (∀ n, 0 < orbit t x n) ∧
    ∀ n, (orbit t x (n + 1)).num + ((orbit t x (n + 1)).den : ℤ) =
      ((orbit t x n).num + ((t + 1 : ℕ) : ℤ) * (orbit t x n).den) ^ 3 := by
  have one_step (q : ℚ) (hq : 0 < q) :
      0 < step t q ∧ (step t q).num + ((step t q).den : ℤ) =
        (q.num + ((t + 1 : ℕ) : ℤ) * q.den) ^ 3 := by
    have hnum : 0 < q.num := Rat.num_pos.mpr hq
    have habs : (q.num.natAbs : ℤ) = q.num := by
      simpa [abs_of_nonneg hnum.le] using (Int.natCast_natAbs q.num)
    have hqeq : (q.num.natAbs : ℚ) / q.den = q := by
      calc
        (q.num.natAbs : ℚ) / q.den = (q.num : ℚ) / q.den := by rw [← habs]; rfl
        _ = q := q.num_div_den
    have r := reduced_step t q.num.natAbs q.den (by omega) q.pos q.reduced
    rw [hqeq] at r
    refine ⟨r.1, ?_⟩
    rw [r.2.1, r.2.2.1]
    have hs := pair_sum t q.num.natAbs q.den
    have hi := congrArg (fun n : ℕ => (n : ℤ)) hs
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, habs] using hi
  have hp : ∀ n, 0 < orbit t x n := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih =>
      simpa [orbit, Function.iterate_succ_apply'] using (one_step _ ih).1
  refine ⟨hp, fun n => ?_⟩
  simpa [orbit, Function.iterate_succ_apply'] using (one_step _ (hp n)).2

open CubeRecursionProjective OnePoint
open scoped MatrixGroups

private theorem rational_projective_step (t : ℕ) (x : ℚ) (hx : 0 < x) :
    projectiveMap t ((x : ℂ) : OnePoint ℂ) = ((step t x : ℂ) : OnePoint ℂ) := by
  have hp : 0 < step t x := by
    simpa [orbit] using (positive_orbit_cube t x hx).1 1
  have hd : (x + t + 1) ^ 3 - (x + t) ≠ 0 := by
    intro he
    simp [step, he] at hp
  have hc : q t (x : ℂ) ≠ 0 := by
    unfold q
    exact_mod_cast hd
  change (if q t (x : ℂ) = 0 then (OnePoint.infty : OnePoint ℂ)
    else ((((x : ℂ) + t) / q t (x : ℂ) : ℂ) : OnePoint ℂ)) = _
  rw [if_neg hc]
  congr 1
  simp [step, q]

/-- The source question with the explicit uniform-family interpretation of natural.
The formula is fixed, the reduced pairs are intrinsic to the rational iterates,
and the conjugacy quantifier ranges over the complete complex projective group. -/
def originalClaim : Prop :=
  ∀ t : ℕ,
    mapDegree (rationalMap t) = 3 ∧
    (∀ x y : ℂ, ∀ h : x ≠ 0 ∨ y ≠ 0,
      projectiveMap t (projectivePoint x y h) = homogeneousImage t x y h) ∧
    ((∀ g : PGL(2, ℂ), ∃ m : GL (Fin 2) ℂ, Matrix.ProjGenLinGroup.mk m = g) ∧
      ∀ m : GL (Fin 2) ℂ,
        mobius (Matrix.ProjGenLinGroup.mk m) OnePoint.infty =
          (if m 1 0 = 0 then OnePoint.infty else (m 0 0 / m 1 0 : ℂ)) ∧
        ∀ z : ℂ, mobius (Matrix.ProjGenLinGroup.mk m) z =
          (if m 1 0 * z + m 1 1 = 0 then OnePoint.infty
           else ((m 0 0 * z + m 0 1) / (m 1 0 * z + m 1 1) : ℂ))) ∧
    (projectiveMap t OnePoint.infty = (0 : ℂ) ∧
      ∀ z : ℂ, projectiveMap t z =
        if (rationalMap t).denom.eval z = 0 then OnePoint.infty
        else (RatFunc.eval (RingHom.id ℂ) z (rationalMap t) : ℂ)) ∧
    (∀ g : PGL(2, ℂ), ¬ ∀ p : OnePoint ℂ,
      mobius g (projectiveMap t (mobius g⁻¹ p)) = powerMap p) ∧
    ∀ x : ℚ, 0 < x →
      (∀ n : ℕ, 0 < orbit t x n ∧ 0 < (orbit t x n).num ∧
        0 < (orbit t x n).den ∧
        (orbit t x n).num.natAbs.Coprime (orbit t x n).den ∧
        (orbit t x n).num / ((orbit t x n).den : ℚ) = orbit t x n) ∧
      (∀ n : ℕ, 1 ≤ n →
        (orbit t x n).num + ((orbit t x n).den : ℤ) =
          ((orbit t x (n - 1)).num +
            ((t + 1 : ℕ) : ℤ) * (orbit t x (n - 1)).den) ^ 3) ∧
      (∀ n : ℕ, projectiveMap t (((orbit t x n) : ℂ) : OnePoint ℂ) =
        (((orbit t x (n + 1)) : ℂ) : OnePoint ℂ))

/-- Every nonnegative parameter gives the full reduced-pair cube family,
with constant one and no complex projective conjugacy to the cube map. -/
theorem result : originalClaim := by
  intro t
  refine ⟨(map_degree_three t).2.2, homogeneous_coordinates t,
    ⟨Matrix.ProjGenLinGroup.mk_surjective, mobius_coordinates⟩,
    rational_map_semantics t, not_conjugate t, ?_⟩
  intro x hx
  obtain ⟨hp, hc⟩ := positive_orbit_cube t x hx
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact ⟨hp n, Rat.num_pos.mpr (hp n), (orbit t x n).pos,
      (orbit t x n).reduced, (orbit t x n).num_div_den⟩
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa using hc k
  · intro n
    simpa [orbit, Function.iterate_succ_apply'] using
      rational_projective_step t (orbit t x n) (hp n)

end D5.S3.Arith.CubeRecursionFamily
