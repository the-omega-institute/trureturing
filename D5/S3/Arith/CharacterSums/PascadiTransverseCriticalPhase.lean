/- GID: D5/S3/Arith/CharacterSums/PascadiTransverseCriticalPhase
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiTransverseCriticalPhase
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: The two upper digits of the transverse rational phase select the stationary equations. -/

module

public import D5.S3.Arith.CharacterSums.PascadiMixedQuotientFourier
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Units.Basic

/-! Upper-digit orthogonality for the transverse prime-square kernel. -/

@[expose] public section

open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.PascadiTransverseCriticalPhase

open MixedQuotient (reduce canonicalLift)

noncomputable section

variable {p : ℕ}

local notation "R" => ZMod (p ^ 2)
local notation "P" => (p : R)

/-- The three factors of the transverse product, with `J_i = d_i + α * n_i`. -/
def factor (d n : Fin 3 → R) (lam alpha : R) (i : Fin 3) : R :=
  lam - (d i + alpha * n i)

/-- The rational phase `Ψ = D/λ` on the unit chart. -/
def phase (d n : Fin 3 → R) (lam alpha : R) : R :=
  (∏ i, factor d n lam alpha i) * lam⁻¹

/-- The middle slope modulo the square, using the actual lower slope `s0`. -/
def middleSlope (s0 alpha : R) : R := s0 + P * alpha

/-- The square of the signed phase on the transverse chart. -/
def radicand (d n : Fin 3 → R) (g s0 lam alpha : R) : R :=
  4 * phase d n lam alpha * (g * middleSlope s0 alpha)⁻¹

private theorem prime_square_zero : P ^ 2 = 0 := by
  norm_cast
  simp

private theorem mul_upper_factors (x y : R) :
    (1 + P * x) * (1 + P * y) = 1 + P * (x + y) := by
  calc
    _ = 1 + P * (x + y) + P ^ 2 * (x * y) := by ring
    _ = _ := by rw [prime_square_zero]; simp

private theorem inverse_upper (x a : R) (hx : IsUnit x) :
    (x + P * a)⁻¹ = x⁻¹ * (1 + P * (-(a * x⁻¹))) := by
  have hi := ZMod.mul_inv_of_unit x hx
  apply ZMod.inv_eq_of_mul_eq_one
  calc
    _ = (x * x⁻¹ + P * (a * x⁻¹)) * (1 + P * (-(a * x⁻¹))) := by ring
    _ = 1 := by rw [hi, mul_upper_factors, add_neg_cancel, mul_zero, add_zero]

/-- The two independent upper digits give the exact first variation of the
three-factor rational phase modulo `p²`. -/
theorem phase_add_digits (d n : Fin 3 → R) (lam alpha : R)
    (hlam : IsUnit lam) (hfactor : ∀ i, IsUnit (factor d n lam alpha i))
    (j k : ZMod p) :
    phase d n (lam + P * canonicalLift j) (alpha + P * canonicalLift k) =
      phase d n lam alpha * (1 + P *
        (canonicalLift j * ((∑ i, (factor d n lam alpha i)⁻¹) - lam⁻¹) -
          canonicalLift k * (∑ i, n i * (factor d n lam alpha i)⁻¹))) := by
  let a := canonicalLift j
  let b := canonicalLift k
  let l := factor d n lam alpha
  let delta : Fin 3 → R := fun i => (a - b * n i) * (l i)⁻¹
  have hf (i : Fin 3) :
      factor d n (lam + P * a) (alpha + P * b) i = l i * (1 + P * delta i) := by
    have hi := ZMod.mul_inv_of_unit (l i) (hfactor i)
    calc
      _ = l i + P * (a - b * n i) * (l i * (l i)⁻¹) := by
        rw [hi]
        dsimp [l, factor]
        ring
      _ = _ := by dsimp [delta]; ring
  have hprod : (∏ i : Fin 3, (1 + P * delta i)) = 1 + P * ∑ i, delta i := by
    simp only [Fin.prod_univ_three, Fin.sum_univ_three, mul_upper_factors]
  have hsum : (∑ i, delta i) + -(a * lam⁻¹) =
      a * ((∑ i, (l i)⁻¹) - lam⁻¹) - b * ∑ i, n i * (l i)⁻¹ := by
    simp only [Fin.sum_univ_three, delta]
    ring
  calc
    _ = ((∏ i, l i) * (1 + P * ∑ i, delta i)) *
        (lam⁻¹ * (1 + P * (-(a * lam⁻¹)))) := by
      change phase d n (lam + P * a) (alpha + P * b) = _
      simp only [phase, hf, Finset.prod_mul_distrib, hprod, inverse_upper lam a hlam]
    _ = phase d n lam alpha * (1 + P * ((∑ i, delta i) + -(a * lam⁻¹))) := by
      rw [phase, ← mul_upper_factors]
      change _ = ((∏ i, l i) * lam⁻¹) *
        ((1 + P * ∑ i, delta i) * (1 + P * (-(a * lam⁻¹))))
      ring
    _ = _ := by rw [hsum]

/-- On the stationary chart the reconstructed signed phase has square
`4 * Ψ / (g * s(α))`. Here `u_i = l_3 / l_i` and `t` is the signed parameter. -/
theorem signed_phase_sq (d n : Fin 3 → R) (g s0 lam alpha t : R)
    (hlam : IsUnit lam) (hfactor : ∀ i, IsUnit (factor d n lam alpha i))
    (hgs : IsUnit (g * middleSlope s0 alpha))
    (hstationary : lam * (∑ i, (factor d n lam alpha i)⁻¹) = 1) :
    let u : Fin 3 → R := fun i => factor d n lam alpha 2 * (factor d n lam alpha i)⁻¹
    t ^ 2 = (∑ i, u i) * (g * middleSlope s0 alpha * ∏ i, u i)⁻¹ →
      (t * ∑ i, u i * (d i + alpha * n i)) ^ 2 = radicand d n g s0 lam alpha := by
  let l := factor d n lam alpha
  let gs := g * middleSlope s0 alpha
  let u : Fin 3 → R := fun i => l 2 * (l i)⁻¹
  change t ^ 2 = (∑ i, u i) * (gs * ∏ i, u i)⁻¹ → _
  intro ht
  have hlu (i : Fin 3) : l i * u i = l 2 := by
    calc
      _ = l 2 * (l i * (l i)⁻¹) := by dsimp [u]; ring
      _ = _ := by rw [ZMod.mul_inv_of_unit _ (hfactor i), mul_one]
  have hS : (∑ i, u i) = l 2 * lam⁻¹ := by
    have hi : (∑ i, (l i)⁻¹) = lam⁻¹ :=
      (ZMod.inv_eq_of_mul_eq_one _ _ _ hstationary).symm
    simp only [u, ← Finset.mul_sum, hi]
  have hdot : (∑ i, u i * (d i + alpha * n i)) = -2 * l 2 := by
    have hterm (i : Fin 3) : u i * (d i + alpha * n i) = lam * u i - l 2 := by
      rw [← hlu i]
      change _ = lam * u i - (lam - (d i + alpha * n i)) * u i
      ring
    simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hS, Fin.sum_univ_three]
    calc
      _ = l 2 * (lam * lam⁻¹) - (l 2 + l 2 + l 2) := by ring
      _ = _ := by rw [ZMod.mul_inv_of_unit _ hlam]; ring
  have hprod : (∏ i, l i) * (∏ i, u i) = l 2 ^ 3 := by
    rw [← Finset.prod_mul_distrib]
    simp only [hlu, Fin.prod_const]
  have hu : IsUnit (∏ i, u i) := by
    rw [Fin.prod_univ_three]
    have hu' (i : Fin 3) : IsUnit (u i) := by
      have hi : IsUnit ((l i)⁻¹) :=
        isUnit_iff_exists_inv'.2 ⟨l i, ZMod.mul_inv_of_unit _ (hfactor i)⟩
      exact (hfactor 2).mul hi
    exact ((hu' 0).mul (hu' 1)).mul (hu' 2)
  have hts : t ^ 2 * (gs * ∏ i, u i) = ∑ i, u i := by
    rw [ht, mul_assoc, ZMod.inv_mul_of_unit _ (hgs.mul hu), mul_one]
  have htransfer : t ^ 2 * (l 2) ^ 2 = phase d n lam alpha * gs⁻¹ := by
    apply (hgs.mul hu).mul_right_cancel
    calc
      _ = l 2 ^ 2 * (t ^ 2 * (gs * ∏ i, u i)) := by ring
      _ = l 2 ^ 3 * lam⁻¹ := by rw [hts, hS]; ring
      _ = ((∏ i, l i) * lam⁻¹) * (gs⁻¹ * gs) * (∏ i, u i) := by
        rw [ZMod.inv_mul_of_unit _ hgs, mul_one, ← hprod]
        ring
      _ = _ := by unfold phase; ring
  change (t * ∑ i, u i * (d i + alpha * n i)) ^ 2 = _
  rw [hdot]
  calc
    _ = 4 * (t ^ 2 * l 2 ^ 2) := by ring
    _ = _ := by rw [htransfer]; unfold radicand; ring

variable [Fact p.Prime]

private instance squareNeZero : NeZero (p ^ 2) :=
  ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

private theorem isUnit_iff_reduce_ne_zero (x : R) : IsUnit x ↔ reduce x ≠ 0 := by
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective x
  rw [map_natCast, ZMod.isUnit_natCast_iff_not_dvd_pow Fact.out (by decide : 0 < 2),
    ne_eq, ZMod.natCast_eq_zero_iff]

private theorem two_isUnit (hp : p ≠ 2) : IsUnit (2 : R) := by
  apply (isUnit_iff_reduce_ne_zero _).2
  rw [map_ofNat]
  change ((2 : ℕ) : ZMod p) ≠ 0
  rw [ne_eq, ZMod.natCast_eq_zero_iff, Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two]
  exact hp

private theorem reduce_inv (x : R) (hx : IsUnit x) :
    reduce x⁻¹ = (reduce x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, ZMod.inv_mul_of_unit _ hx, map_one]

private theorem reduce_canonicalLift (a : ZMod p) : reduce (canonicalLift a) = a := by
  simp [canonicalLift]

private theorem stdAddChar_on_digit (x : R) :
    ZMod.stdAddChar (P * x) = ZMod.stdAddChar (reduce x) := by
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective x
  rw [map_natCast, ← Nat.cast_mul, ZMod.stdAddChar_apply, ZMod.stdAddChar_apply,
    ZMod.toCircle_natCast, ZMod.toCircle_natCast]
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  congr 1
  push_cast
  field_simp

private theorem sum_stdAddChar_mul (b : ZMod p) :
    ∑ j : ZMod p, ZMod.stdAddChar (j * b) = if b = 0 then (p : ℂ) else 0 := by
  split_ifs with h
  · simp [h, ZMod.card]
  · simpa only [AddChar.mulShift_apply, mul_comm b] using
      (AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p h))

private def lambdaVariation (d n : Fin 3 → R) (lam alpha : R) : R :=
  (∑ i, (factor d n lam alpha i)⁻¹) - lam⁻¹

private def alphaVariation (d n : Fin 3 → R) (lam alpha : R) : R :=
  -(∑ i, n i * (factor d n lam alpha i)⁻¹)

private def radicalLift (z a b : R) (j k : ZMod p) : R :=
  z + P * (canonicalLift j * (z * (2 : R)⁻¹ * a) +
    canonicalLift k * (z * (2 : R)⁻¹ * b))

private theorem radicalLift_sq (hp : p ≠ 2)
    (d n : Fin 3 → R) (g s0 lam alpha z : R)
    (hlam : IsUnit lam) (hfactor : ∀ i, IsUnit (factor d n lam alpha i))
    (hz : z ^ 2 = radicand d n g s0 lam alpha) (j k : ZMod p) :
    radicalLift z (lambdaVariation d n lam alpha) (alphaVariation d n lam alpha) j k ^ 2 =
      radicand d n g s0 (lam + P * canonicalLift j) (alpha + P * canonicalLift k) := by
  let w := canonicalLift j * lambdaVariation d n lam alpha +
    canonicalLift k * alphaVariation d n lam alpha
  have hs : middleSlope s0 (alpha + P * canonicalLift k) = middleSlope s0 alpha := by
    unfold middleSlope
    calc
      _ = s0 + P * alpha + P ^ 2 * canonicalLift k := by ring
      _ = _ := by rw [prime_square_zero, zero_mul, add_zero]
  have hphase :
      phase d n (lam + P * canonicalLift j) (alpha + P * canonicalLift k) =
        phase d n lam alpha * (1 + P * w) := by
    rw [phase_add_digits d n lam alpha hlam hfactor]
    dsimp [w, lambdaVariation, alphaVariation]
    ring
  have hlift :
      radicalLift z (lambdaVariation d n lam alpha) (alphaVariation d n lam alpha) j k =
        z * (1 + P * ((2 : R)⁻¹ * w)) := by
    dsimp [radicalLift, w]
    ring
  have hsquare : (1 + P * ((2 : R)⁻¹ * w)) ^ 2 = 1 + P * w := by
    have htwice : (2 : R)⁻¹ * w + (2 : R)⁻¹ * w = w := by
      calc
        _ = ((2 : R) * (2 : R)⁻¹) * w := by ring
        _ = _ := by rw [ZMod.mul_inv_of_unit _ (two_isUnit hp), one_mul]
    calc
      _ = (1 + P * ((2 : R)⁻¹ * w)) * (1 + P * ((2 : R)⁻¹ * w)) := pow_two _
      _ = _ := by rw [mul_upper_factors, htwice]
  rw [hlift, mul_pow, hsquare, hz]
  unfold radicand
  rw [hs, hphase]
  ring

private theorem radical_fibre_singleton (hp : p ≠ 2)
    (d n : Fin 3 → R) (g s0 lam alpha z : R)
    (hlam : IsUnit lam) (hfactor : ∀ i, IsUnit (factor d n lam alpha i))
    (hzunit : IsUnit z) (hz : z ^ 2 = radicand d n g s0 lam alpha) (j k : ZMod p) :
    (Finset.univ.filter fun y : R => reduce y = reduce z ∧
        y ^ 2 = radicand d n g s0 (lam + P * canonicalLift j) (alpha + P * canonicalLift k)) =
      {radicalLift z (lambdaVariation d n lam alpha) (alphaVariation d n lam alpha) j k} := by
  let x := radicalLift z (lambdaVariation d n lam alpha) (alphaVariation d n lam alpha) j k
  have hx : reduce x = reduce z := by simp [x, radicalLift]
  have hxsq := radicalLift_sq hp d n g s0 lam alpha z hlam hfactor hz j k
  apply Finset.eq_singleton_iff_unique_mem.2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨hx, hxsq⟩, ?_⟩
  intro y hy
  have hunit : IsUnit (y + x) := by
    apply (isUnit_iff_reduce_ne_zero _).2
    rw [map_add, hy.1, hx, ← two_mul]
    simpa only [map_mul, map_ofNat] using
      (isUnit_iff_reduce_ne_zero _).1 ((two_isUnit hp).mul hzunit)
  exact hunit.mul_right_cancel (calc
    y * (y + x) = y ^ 2 + y * x := by ring
    _ = x ^ 2 + y * x := by rw [hy.2, ← hxsq]
    _ = x * (y + x) := by ring)

/-- Each nonzero square root modulo `p` determines one signed root at every
pair of upper digits. -/
theorem existsUnique_radical_root_of_reduce (hp : p ≠ 2)
    (d n : Fin 3 → R) (g s0 lam alpha : R)
    (hlam : IsUnit lam) (hfactor : ∀ i, IsUnit (factor d n lam alpha i))
    (r : ZMod p) (hr : r ≠ 0) (hrs : r ^ 2 = reduce (radicand d n g s0 lam alpha))
    (j k : ZMod p) :
    ∃! z : R, reduce z = r ∧
      z ^ 2 = radicand d n g s0 (lam + P * canonicalLift j) (alpha + P * canonicalLift k) := by
  let q := radicand d n g s0 lam alpha
  let x := canonicalLift r
  have hx : reduce x = r := reduce_canonicalLift r
  have hdiff : reduce (q - x ^ 2) = 0 := by
    rw [map_sub, map_pow, hx, hrs, sub_self]
  obtain ⟨N, hN⟩ := ZMod.natCast_zmod_surjective (q - x ^ 2)
  have hdvd : p ∣ N := by
    rw [← hN, map_natCast, ZMod.natCast_eq_zero_iff] at hdiff
    exact hdiff
  obtain ⟨m, hm⟩ := hdvd
  have hdiff' : P * (m : R) = q - x ^ 2 := by rw [← Nat.cast_mul, ← hm, hN]
  let y := ((2 : R) * x)⁻¹ * (m : R)
  let z := x + P * y
  have hy : ((2 : R) * x) * y = (m : R) := by
    have hxunit := (isUnit_iff_reduce_ne_zero _).2 (hx.trans_ne hr)
    rw [show y = ((2 : R) * x)⁻¹ * (m : R) from rfl, ← mul_assoc,
      ZMod.mul_inv_of_unit _ ((two_isUnit hp).mul hxunit), one_mul]
  have hz : z ^ 2 = q := by
    calc
      z ^ 2 = x ^ 2 + P * ((2 * x) * y) + P ^ 2 * y ^ 2 := by dsimp [z]; ring
      _ = q := by rw [hy, hdiff', prime_square_zero, zero_mul, add_zero]; ring
  have hzr : reduce z = r := by simp [z, hx]
  have hsingleton := radical_fibre_singleton hp d n g s0 lam alpha z hlam hfactor
    ((isUnit_iff_reduce_ne_zero _).2 (hzr.trans_ne hr)) hz j k
  have hex := (Finset.singleton_iff_unique_mem _).1 ⟨_, hsingleton⟩
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hzr] using hex

/-- The sum of the actual prime-square characters over the two upper digits
and over the roots in a fixed unit residue branch. It vanishes unless both
stationary equations hold modulo `p`, in which case it equals
`p² * e_(p²)(z)` for the base root `z`. -/
theorem sum_radical_fibre (hp : p ≠ 2)
    (d n : Fin 3 → R) (g s0 lam alpha z : R)
    (hlam : IsUnit lam) (hfactor : ∀ i, IsUnit (factor d n lam alpha i))
    (hzunit : IsUnit z) (hz : z ^ 2 = radicand d n g s0 lam alpha) :
    (∑ j : ZMod p, ∑ k : ZMod p,
      ∑ y ∈ Finset.univ.filter (fun y : R => reduce y = reduce z ∧
        y ^ 2 = radicand d n g s0 (lam + P * canonicalLift j) (alpha + P * canonicalLift k)),
        ZMod.stdAddChar y) =
      if reduce lam * (∑ i, (reduce (factor d n lam alpha i))⁻¹) = 1 ∧
        (∑ i, reduce (n i) * (reduce (factor d n lam alpha i))⁻¹) = 0
      then (p : ℂ) ^ 2 * ZMod.stdAddChar z else 0 := by
  let a := lambdaVariation d n lam alpha
  let b := alphaVariation d n lam alpha
  let scale := z * (2 : R)⁻¹
  let A := reduce (scale * a)
  let B := reduce (scale * b)
  have hscale : reduce scale ≠ 0 := by
    have hi := ZMod.mul_inv_of_unit _ (two_isUnit hp)
    have hInvUnit : IsUnit ((2 : R)⁻¹) := isUnit_iff_exists_inv'.2 ⟨2, hi⟩
    exact (isUnit_iff_reduce_ne_zero _).1 (hzunit.mul hInvUnit)
  have hA : A = 0 ↔ reduce lam * (∑ i, (reduce (factor d n lam alpha i))⁻¹) = 1 := by
    have hcoeff : reduce lam * reduce a =
        reduce lam * (∑ i, (reduce (factor d n lam alpha i))⁻¹) - 1 := by
      simp only [a, lambdaVariation, map_sub, map_sum,
        reduce_inv _ (hfactor _), mul_sub]
      rw [← map_mul, ZMod.mul_inv_of_unit _ hlam, map_one]
    calc
      A = 0 ↔ reduce a = 0 := by simp [A, hscale]
      _ ↔ reduce lam * reduce a = 0 := by simp [(isUnit_iff_reduce_ne_zero _).1 hlam]
      _ ↔ _ := by rw [hcoeff, sub_eq_zero]
  have hB : B = 0 ↔ (∑ i, reduce (n i) * (reduce (factor d n lam alpha i))⁻¹) = 0 := by
    simp only [B, map_mul, mul_eq_zero, hscale, false_or, b, alphaVariation,
      map_neg, map_sum, reduce_inv _ (hfactor _), neg_eq_zero]
  have hchar (j k : ZMod p) :
      ZMod.stdAddChar (radicalLift z a b j k) =
        ZMod.stdAddChar z * (ZMod.stdAddChar (j * A) * ZMod.stdAddChar (k * B)) := by
    simp only [radicalLift, ZMod.stdAddChar.map_add_eq_mul, stdAddChar_on_digit,
      map_add, map_mul, reduce_canonicalLift, A, B, scale]
  have hsum :
      (∑ j : ZMod p, ∑ k : ZMod p, ZMod.stdAddChar (radicalLift z a b j k)) =
        ZMod.stdAddChar z * ((∑ j : ZMod p, ZMod.stdAddChar (j * A)) *
          ∑ k : ZMod p, ZMod.stdAddChar (k * B)) := by
    simp only [hchar, ← Finset.mul_sum, ← Finset.sum_mul]
  simp only [radical_fibre_singleton hp d n g s0 lam alpha z hlam hfactor hzunit hz,
    Finset.sum_singleton]
  change (∑ j : ZMod p, ∑ k : ZMod p, ZMod.stdAddChar (radicalLift z a b j k)) = _
  rw [hsum, sum_stdAddChar_mul, sum_stdAddChar_mul]
  simp only [← hA, ← hB]
  by_cases ha : A = 0 <;> by_cases hb : B = 0
  all_goals simp [ha, hb]
  ring

end

end D5.S3.Arith.CharacterSums.PascadiTransverseCriticalPhase
