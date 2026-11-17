/- GID: D5/S3/Arith/CharacterSums/PascadiModularZeroPartners
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiModularZeroPartners
   mirror-E: none(waiver:open-original-modular-zero-partner-bound)
   anchors: []
   utility: none
   digest: Integer determinant lifts and signed divisor counts for actual modular partners. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalCoefficients
import D5.S3.Arith.Divisors.DivisorSubpower
import Mathlib.NumberTheory.Divisors

/-! # Modular-zero partners in the original integer chart

The finite partner set uses the original endpoint pencil. The determinant count
below supplies the integer lift and divisor injection for an oriented pair of
modular lines. The regular dividing branch supplies both orientations from
the actual pencil; the nondividing absolute bound remains separate.
-/

open Polynomial

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The determinant in the actual integer chart. -/
def coordinateDet (x y : Coordinate) : ℤ := x.1 * y.2 - x.2 * y.1

/-- The shifted endpoint value in the original chart. -/
def actualValue {p : ℕ} (α β : ZMod p) (z : Coordinate) : ZMod p :=
  α + z.1 + β * z.2

/-- An ordered actual pair; swapping its endpoints represents the same paper pair. -/
def ActualPair {p : ℕ} (E : Finset Coordinate) (α β : ZMod p)
    (q : Coordinate) (e : Endpoint) : Prop :=
  e.1 ∈ E ∧ e.2 ∈ E ∧
    actualValue α β e.1 * actualValue α β e.2 =
      α * (α + (q.1 : ZMod p) + β * q.2)

/-- Actual pairs whose original integer pencil is identically zero modulo p. -/
def modularZeroPartners {p : ℕ} (E : Finset Coordinate) (α β : ZMod p)
    (q : Coordinate) (base : Endpoint) : Finset Endpoint :=
  (E ×ˢ E).filter fun e => ActualPair E α β q e ∧
    (pencil q base e).map (Int.castRingHom (ZMod p)) = 0

/-- Alignment refers to exact integer collinearity with the anchor. -/
def Aligned (q : Coordinate) (e : Endpoint) : Prop :=
  coordinateDet q e.1 = 0 ∧ coordinateDet q e.2 = 0

private theorem actual_pair_anchor_of_linear_eval_zero {p : ℕ} [Fact p.Prime]
    (E : Finset Coordinate) (α β : ZMod p) (q : Coordinate) (e : Endpoint)
    (h0 : (0 : Coordinate) ∈ E) (hq : q ∈ E)
    (hinj : Set.InjOn (actualValue α β) (E : Set Coordinate))
    (he : ActualPair E α β q e)
    (hL : (endpointL q e).eval₂ (Int.castRingHom (ZMod p)) β = 0) :
    e = (0, q) ∨ e = (q, 0) := by
  have heval (n : ℤ) : (n : ℤ[X]).eval₂ (Int.castRingHom (ZMod p)) β =
      (n : ZMod p) := map_intCast
        (Polynomial.eval₂RingHom (Int.castRingHom (ZMod p)) β) n
  have hsum : (e.1.1 : ZMod p) + β * e.1.2 +
      ((e.2.1 : ZMod p) + β * e.2.2) = (q.1 : ZMod p) + β * q.2 := by
    simp [endpointL, PrimeCube.linear, coeffL, coeffM, heval] at hL
    linear_combination hL
  have hprod : ((e.1.1 : ZMod p) + β * e.1.2) *
      ((e.2.1 : ZMod p) + β * e.2.2) = 0 := by
    have h := he.2.2
    dsimp [actualValue] at h
    linear_combination h - α * hsum
  have hval (z w : Coordinate)
      (hz : (z.1 : ZMod p) + β * z.2 = (w.1 : ZMod p) + β * w.2) :
      actualValue α β z = actualValue α β w := by
    dsimp [actualValue]
    linear_combination hz
  rcases mul_eq_zero.mp hprod with hx | hy
  · have hx0 : e.1 = 0 := hinj he.1 h0 (hval _ _ (by simpa using hx))
    have hyq : e.2 = q := hinj he.2.1 hq (hval _ _ (by simpa [hx] using hsum))
    exact Or.inl (Prod.ext hx0 hyq)
  · have hy0 : e.2 = 0 := hinj he.2.1 h0 (hval _ _ (by simpa using hy))
    have hxq : e.1 = q := hinj he.1 hq (hval _ _ (by simpa [hy] using hsum))
    exact Or.inr (Prod.ext hxq hy0)

private theorem actual_pair_polynomial_eval {p : ℕ} (E : Finset Coordinate)
    (α β : ZMod p) (q : Coordinate) (e : Endpoint) (he : ActualPair E α β q e) :
    α * (endpointL q e).eval₂ (Int.castRingHom (ZMod p)) β +
      (endpointQ e).eval₂ (Int.castRingHom (ZMod p)) β = 0 := by
  have heval (n : ℤ) : (n : ℤ[X]).eval₂ (Int.castRingHom (ZMod p)) β =
      (n : ZMod p) := map_intCast (eval₂RingHom (Int.castRingHom (ZMod p)) β) n
  have h := he.2.2
  dsimp [actualValue] at h
  simp [endpointL, endpointQ, PrimeCube.linear, PrimeCube.quadratic,
    coeffL, coeffM, coeffQ, coeffR, coeffS, heval]
  linear_combination h

/-- Injectivity excludes both anchor orientations and all repeated-endpoint
exceptions to the nonzero L,Q observation for a nonaligned actual pair. -/
theorem nonaligned_actual_pair_nondegenerate {p : ℕ} [Fact p.Prime]
    (E : Finset Coordinate) (α β : ZMod p) (q : Coordinate) (e : Endpoint)
    (h0 : (0 : Coordinate) ∈ E) (hq : q ∈ E)
    (hinj : Set.InjOn (actualValue α β) (E : Set Coordinate))
    (he : ActualPair E α β q e) (hnonaligned : ¬ Aligned q e) (hα : α ≠ 0)
    (hκ : α * (α + (q.1 : ZMod p) + β * q.2) ≠ 0) :
    (endpointL q e).eval₂ (Int.castRingHom (ZMod p)) β ≠ 0 ∧
    (endpointQ e).eval₂ (Int.castRingHom (ZMod p)) β ≠ 0 ∧
    ((endpointQ e).map (Int.castRingHom (ZMod p)) *
      ((endpointQ e).map (Int.castRingHom (ZMod p)) -
        (endpointL q e).map (Int.castRingHom (ZMod p)) *
          PrimeCube.linear (q.1 : ZMod p) (q.2 : ZMod p))) ≠ 0 := by
  have hL : (endpointL q e).eval₂ (Int.castRingHom (ZMod p)) β ≠ 0 := by
    intro hz
    rcases actual_pair_anchor_of_linear_eval_zero E α β q e h0 hq hinj he hz with h | h
    · subst e
      exact hnonaligned (by simp [Aligned, coordinateDet, mul_comm])
    · subst e
      exact hnonaligned (by simp [Aligned, coordinateDet, mul_comm])
  have hid := actual_pair_polynomial_eval E α β q e he
  have hQ : (endpointQ e).eval₂ (Int.castRingHom (ZMod p)) β ≠ 0 := by
    intro hz
    rw [hz, add_zero] at hid
    exact (mul_ne_zero hα hL) hid
  refine ⟨hL, hQ, ?_⟩
  intro hzero
  have hz := congrArg (eval β) hzero
  simp only [eval_mul, eval_sub, eval_map, eval_zero, PrimeCube.linear,
    eval_add, eval_C, eval_X] at hz
  have hQval : (endpointQ e).eval₂ (Int.castRingHom (ZMod p)) β =
      -α * (endpointL q e).eval₂ (Int.castRingHom (ZMod p)) β := by
    linear_combination hid
  rw [hQval] at hz
  have hκL : (α * (α + (q.1 : ZMod p) + β * q.2)) *
      ((endpointL q e).eval₂ (Int.castRingHom (ZMod p)) β)^2 = 0 := by
    linear_combination hz
  exact (mul_ne_zero hκ (pow_ne_zero 2 hL)) hκL

private theorem det_bound {a b : Coordinate} {A₁ A₂ B₁ B₂ : ℝ}
    (ha : CoordinateBound A₁ A₂ a) (hb : CoordinateBound B₁ B₂ b) :
    |(coordinateDet a b : ℝ)| ≤ A₁ * B₂ + A₂ * B₁ := by
  have hA₁ : 0 ≤ A₁ := (abs_nonneg _).trans ha.1
  have hA₂ : 0 ≤ A₂ := (abs_nonneg _).trans ha.2
  simp only [coordinateDet, Int.cast_sub, Int.cast_mul]
  calc
    _ ≤ |(a.1 : ℝ) * b.2| + |(a.2 : ℝ) * b.1| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul ha.1 hb.2 (abs_nonneg _) hA₁)
        (mul_le_mul ha.2 hb.1 (abs_nonneg _) hA₂)

private theorem sub_bound {a b : Coordinate} {J₁ J₂ : ℝ}
    (ha : CoordinateBound J₁ J₂ a) (hb : CoordinateBound J₁ J₂ b) :
    CoordinateBound (2 * J₁) (2 * J₂) (a - b) := by
  constructor
  · change |((a.1 - b.1 : ℤ) : ℝ)| ≤ _
    push_cast
    exact (abs_sub _ _).trans (by linarith [ha.1, hb.1])
  · change |((a.2 - b.2 : ℤ) : ℝ)| ≤ _
    push_cast
    exact (abs_sub _ _).trans (by linarith [ha.2, hb.2])

private theorem int_eq_zero_of_modular_small {p : ℕ} {a : ℤ}
    (hmod : (a : ZMod p) = 0) (hsmall : |(a : ℝ)| < p) : a = 0 := by
  have hdvd : (p : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hmod
  by_contra ha
  have hle := Int.le_abs_of_dvd ha hdvd
  have hle' : (p : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast hle
  exact (not_le_of_gt hsmall) hle'

private theorem det_coordinates_injective (f h : Coordinate)
    (hΔ : coordinateDet f h ≠ 0) (z w : Coordinate)
    (hf : coordinateDet f z = coordinateDet f w)
    (hh : coordinateDet z h = coordinateDet w h) : z = w := by
  have hx : coordinateDet f h * (z.1 - w.1) = 0 := by
    dsimp [coordinateDet] at *
    linear_combination h.1 * hf + f.1 * hh
  have hy : coordinateDet f h * (z.2 - w.2) = 0 := by
    dsimp [coordinateDet] at *
    linear_combination h.2 * hf + f.2 * hh
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hΔ))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hΔ))

/-- The three modular line conditions on an oriented actual endpoint pair. -/
def ModularLinePair (p : ℕ) (q f h : Coordinate) (e : Endpoint) : Prop :=
  (coordinateDet f e.1 : ZMod p) = 0 ∧
  (coordinateDet h (e.2 - q) : ZMod p) = 0 ∧
  (coordinateDet (e.1 - q) e.2 : ZMod p) = 0

def fieldDet {K : Type*} [CommRing K] (x y : K × K) : K :=
  x.1 * y.2 - x.2 * y.1

theorem fieldDet_zero_scalar {K : Type*} [Field K]
    (b z : K × K) (hb : b.1 ≠ 0 ∨ b.2 ≠ 0)
    (hd : fieldDet b z = 0) :
    ∃ k : K, z.1 = k * b.1 ∧ z.2 = k * b.2 := by
  rcases hb with hb | hb
  · refine ⟨z.1 / b.1, ?_, ?_⟩
    · field_simp
    · have h : b.1 * z.2 = b.2 * z.1 := by
        dsimp [fieldDet] at hd
        linear_combination hd
      field_simp
      linear_combination h
  · refine ⟨z.2 / b.2, ?_, ?_⟩
    · have h : b.1 * z.2 = b.2 * z.1 := by
        dsimp [fieldDet] at hd
        linear_combination hd
      field_simp
      linear_combination -h
    · field_simp

private theorem regular_dividing_factor_choice {K : Type*} [Field K]
    (b q z v : K × K) (c : K) (hc : c ≠ 0)
    (hpoly : ∀ s t : K,
      c * (s * z.1 + t * z.2) * (s * v.1 + t * v.2) =
        (s * (z.1 + v.1 - q.1) + t * (z.2 + v.2 - q.2)) *
          (s * b.1 + t * b.2)) :
    fieldDet b z = 0 ∨ fieldDet b v = 0 := by
  have h := hpoly b.2 (-b.1)
  have hprod : fieldDet b z * fieldDet b v = 0 := by
    have h' : c * (fieldDet b z * fieldDet b v) = 0 := by
      change c * (b.2 * z.1 + -b.1 * z.2) *
          (b.2 * v.1 + -b.1 * v.2) =
        (b.2 * (z.1 + v.1 - q.1) + -b.1 * (z.2 + v.2 - q.2)) *
          (b.2 * b.1 + -b.1 * b.2) at h
      rw [show b.2 * b.1 + -b.1 * b.2 = 0 by ring, mul_zero] at h
      unfold fieldDet
      convert h using 1 <;> ring_nf
    exact (mul_eq_zero.mp h').resolve_left hc
  exact mul_eq_zero.mp hprod

private theorem regular_dividing_oriented {K : Type*} [Field K]
    (a b q z v : K × K) (c : K)
    (hD : fieldDet b q ≠ 0)
    (hq : q.1 = b.1 + (1 - c) * a.1 ∧
      q.2 = b.2 + (1 - c) * a.2)
    (hpoly : ∀ s t : K,
      c * (s * z.1 + t * z.2) * (s * v.1 + t * v.2) =
        (s * (z.1 + v.1 - q.1) + t * (z.2 + v.2 - q.2)) *
          (s * b.1 + t * b.2))
    (hz : fieldDet b z = 0) :
    fieldDet (a.1 - q.1, a.2 - q.2) (v.1 - q.1, v.2 - q.2) = 0 ∧
      fieldDet (z.1 - q.1, z.2 - q.2) v = 0 := by
  have hb : b.1 ≠ 0 ∨ b.2 ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hD
    simp [fieldDet, hn.1, hn.2]
  obtain ⟨k, hz1, hz2⟩ := fieldDet_zero_scalar b z hb hz
  let D := c * k - 1
  let L1 := D * v.1 - (k * b.1 - q.1)
  let L2 := D * v.2 - (k * b.2 - q.2)
  have h11 : b.1 * L1 = 0 := by
    have h := hpoly 1 0
    simp only [one_mul, zero_mul, add_zero] at h
    rw [hz1] at h
    dsimp [L1, D]
    linear_combination h
  have h22 : b.2 * L2 = 0 := by
    have h := hpoly 0 1
    simp only [one_mul, zero_mul, zero_add] at h
    rw [hz2] at h
    dsimp [L2, D]
    linear_combination h
  have h12 : b.1 * L2 + b.2 * L1 = 0 := by
    have h := hpoly 1 1
    have h1 := hpoly 1 0
    have h2 := hpoly 0 1
    simp only [one_mul, zero_mul, add_zero, zero_add] at h h1 h2
    rw [hz1, hz2] at h
    rw [hz1] at h1
    rw [hz2] at h2
    dsimp [L1, L2, D]
    linear_combination h - h1 - h2
  have hL1 : L1 = 0 := by
    rcases hb with hb1 | hb2
    · exact (mul_eq_zero.mp h11).resolve_left hb1
    · have hL2 : L2 = 0 := (mul_eq_zero.mp h22).resolve_left hb2
      rw [hL2, mul_zero, zero_add] at h12
      exact (mul_eq_zero.mp h12).resolve_left hb2
  have hL2 : L2 = 0 := by
    rcases hb with hb1 | hb2
    · rw [hL1, mul_zero, add_zero] at h12
      exact (mul_eq_zero.mp h12).resolve_left hb1
    · exact (mul_eq_zero.mp h22).resolve_left hb2
  have hD0 : D ≠ 0 := by
    intro hd
    dsimp [L1, L2] at hL1 hL2
    rw [hd] at hL1 hL2
    have hbq : fieldDet b q = 0 := by
      dsimp [fieldDet]
      linear_combination b.1 * hL2 - b.2 * hL1
    exact hD hbq
  constructor
  · have hrel1 : D * (v.1 - q.1) = k * (c - 1) * (a.1 - q.1) := by
      dsimp [L1, D] at hL1
      linear_combination hL1 - k * hq.1
    have hrel2 : D * (v.2 - q.2) = k * (c - 1) * (a.2 - q.2) := by
      dsimp [L2, D] at hL2
      linear_combination hL2 - k * hq.2
    have hzero : D * fieldDet (a.1 - q.1, a.2 - q.2)
        (v.1 - q.1, v.2 - q.2) = 0 := by
      dsimp [fieldDet]
      linear_combination (a.1 - q.1) * hrel2 - (a.2 - q.2) * hrel1
    exact (mul_eq_zero.mp hzero).resolve_left hD0
  · have hzero : D * fieldDet (z.1 - q.1, z.2 - q.2) v = 0 := by
      rw [hz1, hz2]
      dsimp [fieldDet, L1, L2, D] at *
      linear_combination (k * b.1 - q.1) * hL2 -
        (k * b.2 - q.2) * hL1
    exact (mul_eq_zero.mp hzero).resolve_left hD0

/-- A regular dividing pencil gives both orientations of the three modular
lines. The homogeneous identity retains constant and vertical factors. -/
theorem regular_dividing_homogeneous_lines {K : Type*} [Field K]
    (a b q z v : K × K) (c : K) (hc : c ≠ 0)
    (hD : fieldDet b q ≠ 0)
    (hq : q.1 = b.1 + (1 - c) * a.1 ∧
      q.2 = b.2 + (1 - c) * a.2)
    (hpoly : ∀ s t : K,
      c * (s * z.1 + t * z.2) * (s * v.1 + t * v.2) =
        (s * (z.1 + v.1 - q.1) + t * (z.2 + v.2 - q.2)) *
          (s * b.1 + t * b.2)) :
    (fieldDet b z = 0 ∧
      fieldDet (a.1 - q.1, a.2 - q.2) (v.1 - q.1, v.2 - q.2) = 0 ∧
      fieldDet (z.1 - q.1, z.2 - q.2) v = 0) ∨
    (fieldDet b v = 0 ∧
      fieldDet (a.1 - q.1, a.2 - q.2) (z.1 - q.1, z.2 - q.2) = 0 ∧
      fieldDet (v.1 - q.1, v.2 - q.2) z = 0) := by
  rcases regular_dividing_factor_choice b q z v c hc hpoly with hz | hv
  · exact Or.inl ⟨hz, regular_dividing_oriented a b q z v c hD hq hpoly hz⟩
  · have hs : ∀ s t : K,
        c * (s * v.1 + t * v.2) * (s * z.1 + t * z.2) =
          (s * (v.1 + z.1 - q.1) + t * (v.2 + z.2 - q.2)) *
            (s * b.1 + t * b.2) := by
      intro s t
      convert hpoly s t using 1 <;> ring
    exact Or.inr ⟨hv, regular_dividing_oriented a b q v z c hD hq hs hv⟩

private theorem homogeneous_of_linear_polynomial_identity {K : Type*} [Field K]
    (b q z v : K × K) (c : K)
    (h : C c * PrimeCube.linear z.1 z.2 * PrimeCube.linear v.1 v.2 =
      (PrimeCube.linear z.1 z.2 + PrimeCube.linear v.1 v.2 -
        PrimeCube.linear q.1 q.2) * PrimeCube.linear b.1 b.2) :
    ∀ s t : K,
      c * (s * z.1 + t * z.2) * (s * v.1 + t * v.2) =
        (s * (z.1 + v.1 - q.1) + t * (z.2 + v.2 - q.2)) *
          (s * b.1 + t * b.2) := by
  have hn : C (c * z.1 * v.1) + C (c * (z.1 * v.2 + z.2 * v.1)) * X +
        C (c * z.2 * v.2) * X^2 =
      C ((z.1 + v.1 - q.1) * b.1) +
        C ((z.1 + v.1 - q.1) * b.2 + (z.2 + v.2 - q.2) * b.1) * X +
        C ((z.2 + v.2 - q.2) * b.2) * X^2 := by
    convert h using 1 <;>
      simp only [PrimeCube.linear, Polynomial.C_mul,
        Polynomial.C_add, Polynomial.C_sub] <;> ring
  have h0 := congrArg (fun P : K[X] => P.coeff 0) hn
  have h1 := congrArg (fun P : K[X] => P.coeff 1) hn
  have h2 := congrArg (fun P : K[X] => P.coeff 2) hn
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] at h0 h1 h2
  norm_num at h0 h1 h2
  intro s t
  linear_combination s^2 * h0 + s*t * h1 + t^2 * h2

private def fieldCoordinate (p : ℕ) (z : Coordinate) : ZMod p × ZMod p :=
  ((z.1 : ZMod p), (z.2 : ZMod p))

private theorem mapped_endpoint_linear {p : ℕ} (q : Coordinate) (e : Endpoint) :
    (endpointL q e).map (Int.castRingHom (ZMod p)) =
      PrimeCube.linear ((e.1.1 : ZMod p) + e.2.1 - q.1)
        ((e.1.2 : ZMod p) + e.2.2 - q.2) := by
  simp [endpointL, PrimeCube.linear, coeffL, coeffM]

private theorem mapped_endpoint_quadratic {p : ℕ} (e : Endpoint) :
    (endpointQ e).map (Int.castRingHom (ZMod p)) =
      PrimeCube.linear (e.1.1 : ZMod p) e.1.2 *
        PrimeCube.linear (e.2.1 : ZMod p) e.2.2 := by
  simp [endpointQ, PrimeCube.quadratic, PrimeCube.linear,
    coeffQ, coeffR, coeffS]
  ring

private theorem mapped_pencil_formal {p : ℕ} (q : Coordinate)
    (base e : Endpoint)
    (hzero : (pencil q base e).map (Int.castRingHom (ZMod p)) = 0) :
    PrimeCube.linear ((base.1.1 : ZMod p) + base.2.1 - q.1)
        ((base.1.2 : ZMod p) + base.2.2 - q.2) *
      PrimeCube.linear (e.1.1 : ZMod p) e.1.2 *
        PrimeCube.linear (e.2.1 : ZMod p) e.2.2 =
      (PrimeCube.linear (e.1.1 : ZMod p) e.1.2 +
          PrimeCube.linear (e.2.1 : ZMod p) e.2.2 -
          PrimeCube.linear (q.1 : ZMod p) q.2) *
        PrimeCube.linear (base.1.1 : ZMod p) base.1.2 *
          PrimeCube.linear (base.2.1 : ZMod p) base.2.2 := by
  have hLb := mapped_endpoint_linear (p := p) q base
  have hLe := mapped_endpoint_linear (p := p) q e
  have hQb := mapped_endpoint_quadratic (p := p) base
  have hQe := mapped_endpoint_quadratic (p := p) e
  simp only [pencil, Polynomial.map_sub, Polynomial.map_mul] at hzero
  rw [hLb, hLe, hQb, hQe] at hzero
  apply sub_eq_zero.mp at hzero
  convert hzero using 1 <;>
    simp [PrimeCube.linear, Polynomial.C_add, Polynomial.C_sub] <;> ring

private theorem linear_triple_coeff_three {K : Type*} [CommRing K]
    (x y z : K × K) :
    (PrimeCube.linear x.1 x.2 * PrimeCube.linear y.1 y.2 *
      PrimeCube.linear z.1 z.2).coeff 3 = x.2 * y.2 * z.2 := by
  have hn : PrimeCube.linear x.1 x.2 * PrimeCube.linear y.1 y.2 *
        PrimeCube.linear z.1 z.2 =
      C (x.1 * y.1 * z.1) +
        C (x.1 * y.1 * z.2 + x.1 * y.2 * z.1 + x.2 * y.1 * z.1) * X +
        C (x.1 * y.2 * z.2 + x.2 * y.1 * z.2 + x.2 * y.2 * z.1) * X^2 +
        C (x.2 * y.2 * z.2) * X^3 := by
    simp only [PrimeCube.linear, Polynomial.C_mul, Polynomial.C_add]
    ring
  rw [hn]
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

private theorem nondividing_first_factor {K : Type*} [Field K]
    (a b d q z v : K × K) (hα : fieldDet a d ≠ 0)
    (hpoly : PrimeCube.linear d.1 d.2 *
        PrimeCube.linear z.1 z.2 * PrimeCube.linear v.1 v.2 =
      (PrimeCube.linear z.1 z.2 + PrimeCube.linear v.1 v.2 -
        PrimeCube.linear q.1 q.2) *
          PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2) :
    fieldDet a z = 0 ∨ fieldDet a v = 0 := by
  by_cases ha2 : a.2 = 0
  · have ha1 : a.1 ≠ 0 := by
      intro hz
      apply hα
      simp [fieldDet, hz, ha2]
    have hd2 : d.2 ≠ 0 := by
      intro hz
      apply hα
      simp [fieldDet, ha2, hz]
    have h3 := congrArg (fun P : K[X] => P.coeff 3) hpoly
    have hright :
        ((PrimeCube.linear z.1 z.2 + PrimeCube.linear v.1 v.2 -
          PrimeCube.linear q.1 q.2) *
            PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2).coeff 3 = 0 := by
      rw [ha2]
      have hn : (PrimeCube.linear z.1 z.2 + PrimeCube.linear v.1 v.2 -
            PrimeCube.linear q.1 q.2) * PrimeCube.linear a.1 0 *
            PrimeCube.linear b.1 b.2 =
          C ((z.1 + v.1 - q.1) * a.1 * b.1) +
            C ((z.1 + v.1 - q.1) * a.1 * b.2 +
              (z.2 + v.2 - q.2) * a.1 * b.1) * X +
            C ((z.2 + v.2 - q.2) * a.1 * b.2) * X^2 := by
        simp [PrimeCube.linear, Polynomial.C_mul, Polynomial.C_add,
          Polynomial.C_sub]
        ring
      rw [hn]
      simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
      norm_num
    rw [linear_triple_coeff_three, hright] at h3
    have hprod : z.2 * v.2 = 0 := by
      rw [mul_assoc] at h3
      exact (mul_eq_zero.mp h3).resolve_left hd2
    rcases mul_eq_zero.mp hprod with hz | hv
    · left
      simp [fieldDet, ha2, hz]
    · right
      simp [fieldDet, ha2, hv]
  · let t : K := -a.1 / a.2
    have ha : a.1 + a.2 * t = 0 := by
      dsimp [t]
      field_simp
      ring
    have hd : d.1 + d.2 * t ≠ 0 := by
      intro hz
      apply hα
      dsimp [fieldDet]
      dsimp [t] at hz
      field_simp at hz
      linear_combination -hz
    have heval := congrArg (fun P : K[X] => P.eval t) hpoly
    simp only [eval_mul, eval_sub, eval_add, PrimeCube.linear,
      eval_C, eval_X, eval_mul] at heval
    rw [ha] at heval
    simp only [mul_zero, zero_mul] at heval
    have hprod : (z.1 + z.2 * t) * (v.1 + v.2 * t) = 0 := by
      rw [mul_assoc] at heval
      exact (mul_eq_zero.mp heval).resolve_left hd
    rcases mul_eq_zero.mp hprod with hz | hv
    · left
      have h := congrArg (fun x : K => a.2 * x) hz
      dsimp [t] at h
      field_simp at h
      dsimp [fieldDet]
      linear_combination -h
    · right
      have h := congrArg (fun x : K => a.2 * x) hv
      dsimp [t] at h
      field_simp at h
      dsimp [fieldDet]
      linear_combination -h

private theorem linear_eq_zero_iff {K : Type*} [Field K] (z : K × K) :
    PrimeCube.linear z.1 z.2 = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have h0 := congrArg (fun P : K[X] => P.coeff 0) hz
    have h1 := congrArg (fun P : K[X] => P.coeff 1) hz
    simp [PrimeCube.linear] at h0 h1
    exact Prod.ext h0 h1
  · intro hz
    subst z
    simp [PrimeCube.linear]

private theorem linear_injective {K : Type*} [Field K] (z v : K × K)
    (h : PrimeCube.linear z.1 z.2 = PrimeCube.linear v.1 v.2) : z = v := by
  have h0 := congrArg (fun P : K[X] => P.coeff 0) h
  have h1 := congrArg (fun P : K[X] => P.coeff 1) h
  simp [PrimeCube.linear] at h0 h1
  exact Prod.ext h0 h1

private theorem nondividing_second_factor {K : Type*} [Field K]
    (b d r v : K × K) (k : K) (hk : k ≠ 0)
    (hβ : fieldDet d b ≠ 0)
    (hpoly : C k * PrimeCube.linear d.1 d.2 * PrimeCube.linear v.1 v.2 =
      PrimeCube.linear r.1 r.2 * PrimeCube.linear b.1 b.2) :
    fieldDet b v = 0 := by
  by_cases hb2 : b.2 = 0
  · have hb1 : b.1 ≠ 0 := by
      intro hz
      apply hβ
      simp [fieldDet, hz, hb2]
    have hd2 : d.2 ≠ 0 := by
      intro hz
      apply hβ
      simp [fieldDet, hb2, hz]
    have h2 := congrArg (fun P : K[X] => P.coeff 2) hpoly
    have hl : (C k * PrimeCube.linear d.1 d.2 *
        PrimeCube.linear v.1 v.2).coeff 2 = k * d.2 * v.2 := by
      have hn : C k * PrimeCube.linear d.1 d.2 * PrimeCube.linear v.1 v.2 =
          C (k * d.1 * v.1) +
          C (k * (d.1 * v.2 + d.2 * v.1)) * X +
          C (k * d.2 * v.2) * X^2 := by
        simp [PrimeCube.linear, Polynomial.C_mul, Polynomial.C_add]
        ring
      rw [hn]
      simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
      norm_num
    have hr : (PrimeCube.linear r.1 r.2 *
        PrimeCube.linear b.1 b.2).coeff 2 = 0 := by
      rw [hb2]
      have hn : PrimeCube.linear r.1 r.2 * PrimeCube.linear b.1 0 =
          C (r.1 * b.1) + C (r.2 * b.1) * X := by
        simp [PrimeCube.linear, Polynomial.C_mul, Polynomial.C_add]
        ring
      rw [hn]
      simp [coeff_add, coeff_C_mul_X, coeff_C]
    rw [hl, hr] at h2
    have hv2 : v.2 = 0 := by
      rw [mul_assoc] at h2
      exact (mul_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hk)).resolve_left hd2
    simp [fieldDet, hb2, hv2]
  · let t : K := -b.1 / b.2
    have hb : b.1 + b.2 * t = 0 := by
      dsimp [t]
      field_simp
      ring
    have hd : d.1 + d.2 * t ≠ 0 := by
      intro hz
      apply hβ
      dsimp [fieldDet]
      dsimp [t] at hz
      field_simp at hz
      linear_combination hz
    have heval := congrArg (fun P : K[X] => P.eval t) hpoly
    simp only [eval_mul, eval_C, eval_add, eval_X, PrimeCube.linear] at heval
    rw [hb] at heval
    simp only [mul_zero] at heval
    have hv : v.1 + v.2 * t = 0 := by
      rw [mul_assoc] at heval
      exact (mul_eq_zero.mp ((mul_eq_zero.mp heval).resolve_left hk)).resolve_left hd
    have h := congrArg (fun x : K => b.2 * x) hv
    dsimp [t] at h
    field_simp at h
    dsimp [fieldDet]
    linear_combination -h

private theorem nondividing_oriented_vectors {K : Type*} [Field K]
    (a b d q v : K × K) (k : K) (hk : k ≠ 0)
    (hα : fieldDet a d ≠ 0) (hβ : fieldDet d b ≠ 0)
    (hpoly : PrimeCube.linear d.1 d.2 *
        PrimeCube.linear (k * a.1) (k * a.2) *
          PrimeCube.linear v.1 v.2 =
      (PrimeCube.linear (k * a.1) (k * a.2) +
          PrimeCube.linear v.1 v.2 - PrimeCube.linear q.1 q.2) *
        PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2) :
    ∃ l : K, v = (l * b.1, l * b.2) ∧
      k * l * d.1 = k * a.1 + l * b.1 - q.1 ∧
      k * l * d.2 = k * a.2 + l * b.2 - q.2 := by
  let A := PrimeCube.linear a.1 a.2
  let B := PrimeCube.linear b.1 b.2
  let D := PrimeCube.linear d.1 d.2
  let V := PrimeCube.linear v.1 v.2
  let R := PrimeCube.linear (k * a.1 + v.1 - q.1)
      (k * a.2 + v.2 - q.2)
  have ha : a ≠ 0 := by
    intro hz
    apply hα
    simp [fieldDet, hz]
  have hb : b ≠ 0 := by
    intro hz
    apply hβ
    simp [fieldDet, hz]
  have hA : A ≠ 0 := by
    intro hz
    exact ha ((linear_eq_zero_iff a).mp hz)
  have hB : B ≠ 0 := by
    intro hz
    exact hb ((linear_eq_zero_iff b).mp hz)
  have hred : C k * D * V = R * B := by
    apply mul_left_cancel₀ hA
    convert hpoly using 1 <;>
      simp [A, B, D, V, R, PrimeCube.linear, Polynomial.C_mul,
        Polynomial.C_add, Polynomial.C_sub] <;> ring
  have hdet : fieldDet b v = 0 :=
    nondividing_second_factor b d
      (k * a.1 + v.1 - q.1, k * a.2 + v.2 - q.2)
      v k hk hβ hred
  have hb_nonzero : b.1 ≠ 0 ∨ b.2 ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hb (Prod.ext hn.1 hn.2)
  obtain ⟨l, hv1, hv2⟩ := fieldDet_zero_scalar b v hb_nonzero hdet
  have hv : v = (l * b.1, l * b.2) := Prod.ext hv1 hv2
  have hlin : C (k * l) * D = R := by
    apply mul_left_cancel₀ hB
    convert hred using 1 <;>
      simp [B, D, V, R, hv1, hv2, PrimeCube.linear,
        Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub] <;> ring
  have hvec : (k * l * d.1, k * l * d.2) =
      (k * a.1 + l * b.1 - q.1, k * a.2 + l * b.2 - q.2) := by
    apply linear_injective
    convert hlin using 1 <;>
      simp [D, R, hv1, hv2, PrimeCube.linear,
        Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub] <;> ring
  exact ⟨l, hv, congrArg Prod.fst hvec, congrArg Prod.snd hvec⟩

private theorem nondividing_scalar_candidates {K : Type*} [Field K]
    (a b d q : K × K) (k l : K)
    (hq : q.1 = a.1 + b.1 - d.1 ∧
      q.2 = a.2 + b.2 - d.2)
    (hα : fieldDet a d ≠ 0) (hβ : fieldDet d b ≠ 0)
    (h1 : k * l * d.1 = k * a.1 + l * b.1 - q.1)
    (h2 : k * l * d.2 = k * a.2 + l * b.2 - q.2) :
    (k = 1 ∧ l = 1) ∨
      (k = (fieldDet a b - fieldDet d b) / fieldDet a d ∧
       l = (fieldDet a b - fieldDet a d) / fieldDet d b) := by
  let α := fieldDet a d
  let β := fieldDet d b
  let Δ := fieldDet a b
  have hr1 : (k * l - 1) * d.1 - (k - 1) * a.1 - (l - 1) * b.1 = 0 := by
    linear_combination h1 - hq.1
  have hr2 : (k * l - 1) * d.2 - (k - 1) * a.2 - (l - 1) * b.2 = 0 := by
    linear_combination h2 - hq.2
  have heq1 : β * (l - 1) = α * (k - 1) := by
    dsimp [α, β, fieldDet]
    linear_combination -(d.1 * hr2 - d.2 * hr1)
  have heq2 : β * (k * l - 1) = Δ * (k - 1) := by
    dsimp [β, Δ, fieldDet]
    linear_combination b.2 * hr1 - b.1 * hr2
  have hfactor : (k - 1) * (α * k + β - Δ) = 0 := by
    linear_combination heq2 - k * heq1
  rcases mul_eq_zero.mp hfactor with hk | hk
  · left
    have hk1 : k = 1 := sub_eq_zero.mp hk
    have hl1 : l = 1 := by
      rw [hk1] at heq1
      have hz : β * (l - 1) = 0 := by simpa using heq1
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hβ)
    exact ⟨hk1, hl1⟩
  · right
    have hk' : k = (Δ - β) / α := by
      apply (eq_div_iff hα).2
      linear_combination hk
    have hl' : l = (Δ - α) / β := by
      apply (eq_div_iff hβ).2
      linear_combination heq1 + hk
    exact ⟨hk', hl'⟩

private def nondividingLambda {K : Type*} [Field K] (a b d : K × K) : K :=
  (fieldDet a b - fieldDet d b) / fieldDet a d

private def nondividingMu {K : Type*} [Field K] (a b d : K × K) : K :=
  (fieldDet a b - fieldDet a d) / fieldDet d b

private theorem nondividing_oriented_cover {K : Type*} [Field K]
    (a b d q z v : K × K)
    (hq : q.1 = a.1 + b.1 - d.1 ∧ q.2 = a.2 + b.2 - d.2)
    (hα : fieldDet a d ≠ 0) (hβ : fieldDet d b ≠ 0)
    (hz0 : z ≠ 0) (hz : fieldDet a z = 0)
    (hpoly : PrimeCube.linear d.1 d.2 *
        PrimeCube.linear z.1 z.2 * PrimeCube.linear v.1 v.2 =
      (PrimeCube.linear z.1 z.2 + PrimeCube.linear v.1 v.2 -
        PrimeCube.linear q.1 q.2) *
          PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2) :
    (z, v) = (a, b) ∨
      (z, v) = ((nondividingLambda a b d * a.1,
        nondividingLambda a b d * a.2),
        (nondividingMu a b d * b.1, nondividingMu a b d * b.2)) := by
  have ha : a.1 ≠ 0 ∨ a.2 ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hα
    simp [fieldDet, hn.1, hn.2]
  obtain ⟨k, hz1, hz2⟩ := fieldDet_zero_scalar a z ha hz
  have hk : k ≠ 0 := by
    intro hzero
    apply hz0
    exact Prod.ext (by simpa [hzero] using hz1) (by simpa [hzero] using hz2)
  have hp : PrimeCube.linear d.1 d.2 *
      PrimeCube.linear (k * a.1) (k * a.2) *
        PrimeCube.linear v.1 v.2 =
    (PrimeCube.linear (k * a.1) (k * a.2) +
        PrimeCube.linear v.1 v.2 - PrimeCube.linear q.1 q.2) *
      PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2 := by
    simpa only [hz1, hz2] using hpoly
  obtain ⟨l, hv, heq1, heq2⟩ :=
    nondividing_oriented_vectors a b d q v k hk hα hβ hp
  rcases nondividing_scalar_candidates a b d q k l hq hα hβ heq1 heq2 with
    ⟨hk1, hl1⟩ | ⟨hkAlt, hlAlt⟩
  · left
    apply Prod.ext
    · exact Prod.ext (by simpa [hk1] using hz1) (by simpa [hk1] using hz2)
    · simpa [hl1] using hv
  · right
    apply Prod.ext
    · exact Prod.ext (by simpa [nondividingLambda, hkAlt] using hz1)
        (by simpa [nondividingLambda, hkAlt] using hz2)
    · simpa [nondividingMu, hlAlt] using hv

private theorem nondividing_zero_endpoint {K : Type*} [Field K]
    (a b d q v : K × K)
    (hα : fieldDet a d ≠ 0) (hβ : fieldDet d b ≠ 0)
    (hpoly : PrimeCube.linear d.1 d.2 *
        PrimeCube.linear (0 : K) 0 * PrimeCube.linear v.1 v.2 =
      (PrimeCube.linear (0 : K) 0 + PrimeCube.linear v.1 v.2 -
        PrimeCube.linear q.1 q.2) *
          PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2) :
    v = q := by
  have ha : a ≠ 0 := by
    intro hz
    apply hα
    simp [fieldDet, hz]
  have hb : b ≠ 0 := by
    intro hz
    apply hβ
    simp [fieldDet, hz]
  have hA : PrimeCube.linear a.1 a.2 ≠ 0 := by
    intro hz
    exact ha ((linear_eq_zero_iff a).mp hz)
  have hB : PrimeCube.linear b.1 b.2 ≠ 0 := by
    intro hz
    exact hb ((linear_eq_zero_iff b).mp hz)
  have hzero : (PrimeCube.linear v.1 v.2 - PrimeCube.linear q.1 q.2) *
      PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2 = 0 := by
    simpa [PrimeCube.linear] using hpoly.symm
  have hlin : PrimeCube.linear v.1 v.2 - PrimeCube.linear q.1 q.2 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hB)).resolve_right hA
  exact linear_injective v q (sub_eq_zero.mp hlin)

/-- Every nondividing formal pencil partner lies among six ordered field pairs. -/
theorem nondividing_field_partner_cover {K : Type*} [Field K]
    (a b d q z v : K × K)
    (hq : q.1 = a.1 + b.1 - d.1 ∧ q.2 = a.2 + b.2 - d.2)
    (hα : fieldDet a d ≠ 0) (hβ : fieldDet d b ≠ 0)
    (hpoly : PrimeCube.linear d.1 d.2 *
        PrimeCube.linear z.1 z.2 * PrimeCube.linear v.1 v.2 =
      (PrimeCube.linear z.1 z.2 + PrimeCube.linear v.1 v.2 -
        PrimeCube.linear q.1 q.2) *
          PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2) :
    (z, v) = (0, q) ∨ (z, v) = (q, 0) ∨
    (z, v) = (a, b) ∨ (z, v) = (b, a) ∨
    (z, v) = ((nondividingLambda a b d * a.1,
      nondividingLambda a b d * a.2),
      (nondividingMu a b d * b.1, nondividingMu a b d * b.2)) ∨
    (z, v) = ((nondividingMu a b d * b.1,
      nondividingMu a b d * b.2),
      (nondividingLambda a b d * a.1,
        nondividingLambda a b d * a.2)) := by
  by_cases hz0 : z = 0
  · left
    subst z
    exact congrArg (fun w : K × K => ((0, 0), w))
      (nondividing_zero_endpoint a b d q v hα hβ hpoly)
  by_cases hv0 : v = 0
  · right; left
    subst v
    have hs : PrimeCube.linear d.1 d.2 *
        PrimeCube.linear (0 : K) 0 * PrimeCube.linear z.1 z.2 =
      (PrimeCube.linear (0 : K) 0 + PrimeCube.linear z.1 z.2 -
        PrimeCube.linear q.1 q.2) *
          PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2 := by
      simpa [PrimeCube.linear] using hpoly
    exact congrArg (fun w : K × K => (w, (0, 0)))
      (nondividing_zero_endpoint a b d q z hα hβ hs)
  rcases nondividing_first_factor a b d q z v hα hpoly with hz | hv
  · rcases nondividing_oriented_cover a b d q z v hq hα hβ hz0 hz hpoly with
      h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · have hs : PrimeCube.linear d.1 d.2 *
        PrimeCube.linear v.1 v.2 * PrimeCube.linear z.1 z.2 =
      (PrimeCube.linear v.1 v.2 + PrimeCube.linear z.1 z.2 -
        PrimeCube.linear q.1 q.2) *
          PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2 := by
      convert hpoly using 1 <;> ring
    rcases nondividing_oriented_cover a b d q v z hq hα hβ hv0 hv hs with
      h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl (congrArg Prod.swap h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (congrArg Prod.swap h)))))

private theorem mapped_pencil_homogeneous {p : ℕ} [Fact p.Prime]
    (q : Coordinate) (base e : Endpoint) (c : ZMod p)
    (hq : (q.1 : ZMod p) = (base.2.1 : ZMod p) + (1 - c) * base.1.1 ∧
      (q.2 : ZMod p) = (base.2.2 : ZMod p) + (1 - c) * base.1.2)
    (ha : (base.1.1 : ZMod p) ≠ 0 ∨ (base.1.2 : ZMod p) ≠ 0)
    (hzero : (pencil q base e).map (Int.castRingHom (ZMod p)) = 0) :
    ∀ s t : ZMod p,
      c * (s * (e.1.1 : ZMod p) + t * e.1.2) *
          (s * (e.2.1 : ZMod p) + t * e.2.2) =
        (s * ((e.1.1 : ZMod p) + e.2.1 - q.1) +
          t * ((e.1.2 : ZMod p) + e.2.2 - q.2)) *
            (s * (base.2.1 : ZMod p) + t * base.2.2) := by
  let A := PrimeCube.linear (base.1.1 : ZMod p) base.1.2
  let B := PrimeCube.linear (base.2.1 : ZMod p) base.2.2
  let Z := PrimeCube.linear (e.1.1 : ZMod p) e.1.2
  let V := PrimeCube.linear (e.2.1 : ZMod p) e.2.2
  let Q := PrimeCube.linear (q.1 : ZMod p) q.2
  have hA : A ≠ 0 := by
    intro hz
    rcases ha with ha1 | ha2
    · have h := congrArg (fun P : (ZMod p)[X] => P.coeff 0) hz
      simp [A, PrimeCube.linear] at h
      exact ha1 h
    · have h := congrArg (fun P : (ZMod p)[X] => P.coeff 1) hz
      simp only [A, PrimeCube.linear, coeff_add, coeff_C_mul_X, coeff_C] at h
      norm_num at h
      exact ha2 h
  have hLb : (endpointL q base).map (Int.castRingHom (ZMod p)) = C c * A := by
    rw [mapped_endpoint_linear]
    dsimp [A]
    simp only [hq.1, hq.2]
    simp [PrimeCube.linear, Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub]
    ring
  have hLe : (endpointL q e).map (Int.castRingHom (ZMod p)) = Z + V - Q := by
    rw [mapped_endpoint_linear]
    dsimp [Z, V, Q]
    simp [PrimeCube.linear, Polynomial.C_add, Polynomial.C_sub]
    ring
  have hQb : (endpointQ base).map (Int.castRingHom (ZMod p)) = A * B := by
    rw [mapped_endpoint_quadratic]
  have hQe : (endpointQ e).map (Int.castRingHom (ZMod p)) = Z * V := by
    rw [mapped_endpoint_quadratic]
  simp only [pencil, Polynomial.map_sub, Polynomial.map_mul] at hzero
  rw [hLb, hLe, hQb, hQe] at hzero
  have hfac : A * (C c * Z * V - (Z + V - Q) * B) = 0 := by
    linear_combination hzero
  have hquad : C c * Z * V = (Z + V - Q) * B := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left hA)
  exact homogeneous_of_linear_polynomial_identity
    (fieldCoordinate p base.2) (fieldCoordinate p q)
    (fieldCoordinate p e.1) (fieldCoordinate p e.2) c hquad

/-- The actual mapped pencil in the regular dividing branch produces both
orientations of the three determinant lines, including vertical factors. -/
theorem regular_dividing_actual_line_cover {p : ℕ} [Fact p.Prime]
    (q a b : Coordinate) (e : Endpoint) (c : ZMod p)
    (hc : c ≠ 0)
    (hD : (coordinateDet b q : ZMod p) ≠ 0)
    (hq : (q.1 : ZMod p) = (b.1 : ZMod p) + (1 - c) * a.1 ∧
      (q.2 : ZMod p) = (b.2 : ZMod p) + (1 - c) * a.2)
    (hzero : (pencil q (a, b) e).map (Int.castRingHom (ZMod p)) = 0) :
    ModularLinePair p q b (a - q) e ∨
      ModularLinePair p q b (a - q) e.swap := by
  have hD' : fieldDet (fieldCoordinate p b) (fieldCoordinate p q) ≠ 0 := by
    simpa [fieldDet, fieldCoordinate, coordinateDet] using hD
  have ha : (a.1 : ZMod p) ≠ 0 ∨ (a.2 : ZMod p) ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hD'
    dsimp [fieldDet, fieldCoordinate]
    rw [hq.1, hq.2, hn.1, hn.2]
    ring
  have hp := mapped_pencil_homogeneous q (a, b) e c hq ha hzero
  have hl := regular_dividing_homogeneous_lines
    (fieldCoordinate p a) (fieldCoordinate p b) (fieldCoordinate p q)
    (fieldCoordinate p e.1) (fieldCoordinate p e.2) c hc hD' hq hp
  rcases hl with hl | hl
  · left
    simpa [ModularLinePair, fieldDet, fieldCoordinate, coordinateDet,
      Int.cast_sub, Int.cast_mul] using hl
  · right
    simpa [ModularLinePair, fieldDet, fieldCoordinate, coordinateDet,
      Int.cast_sub, Int.cast_mul] using hl

/-- The small determinant, rather than the divisor product height, lifts to zero.
No integer collinearity or integer factorization is assumed. -/
theorem modular_line_pair_integer_lift {p : ℕ} {J₁ J₂ : ℝ}
    (q f h : Coordinate) (e : Endpoint)
    (hq : CoordinateBound J₁ J₂ q) (hf : CoordinateBound J₁ J₂ f)
    (hh : CoordinateBound (2 * J₁) (2 * J₂) h)
    (hz : CoordinateBound J₁ J₂ e.1) (hv : CoordinateBound J₁ J₂ e.2)
    (hsmall : 8 * J₁ * J₂ < p) (he : ModularLinePair p q f h e) :
    coordinateDet f e.1 = 0 ∧ coordinateDet h (e.2 - q) = 0 ∧
      coordinateDet (e.1 - q) e.2 = 0 := by
  have hJ₁ : 0 ≤ J₁ := (abs_nonneg _).trans hq.1
  have hJ₂ : 0 ≤ J₂ := (abs_nonneg _).trans hq.2
  have hD : 0 ≤ J₁ * J₂ := mul_nonneg hJ₁ hJ₂
  refine ⟨int_eq_zero_of_modular_small he.1 ?_,
    int_eq_zero_of_modular_small he.2.1 ?_,
    int_eq_zero_of_modular_small he.2.2 ?_⟩
  · have hb := det_bound hf hz
    nlinarith
  · have hb := det_bound hh (sub_bound hv hq)
    nlinarith
  · have hb := det_bound (sub_bound hz hq) hv
    nlinarith

private theorem determinant_divisor_identity (q f h : Coordinate) (e : Endpoint)
    (hf : coordinateDet f e.1 = 0) (hh : coordinateDet h (e.2 - q) = 0)
    (he : coordinateDet (e.1 - q) e.2 = 0) :
    coordinateDet (e.1 - q) h * coordinateDet f e.2 =
      coordinateDet q h * coordinateDet q f := by
  dsimp [coordinateDet] at *
  change h.1 * (e.2.2 - q.2) - h.2 * (e.2.1 - q.1) = 0 at hh
  change (e.1.1 - q.1) * e.2.2 - (e.1.2 - q.2) * e.2.1 = 0 at he
  linear_combination (f.1 * h.2 - f.2 * h.1) * he -
    (q.1 * f.2 - q.2 * f.1) * hh +
    (q.1 * h.2 - q.2 * h.1 - (h.1 * (e.2.2 - q.2) -
      h.2 * (e.2.1 - q.1))) * hf

private theorem divisor_coordinates_injective (q f h : Coordinate)
    (hΔ : coordinateDet f h ≠ 0) (e e' : Endpoint)
    (he : coordinateDet f e.1 = 0 ∧ coordinateDet h (e.2 - q) = 0)
    (he' : coordinateDet f e'.1 = 0 ∧ coordinateDet h (e'.2 - q) = 0)
    (hab : (coordinateDet (e.1 - q) h, coordinateDet f e.2) =
      (coordinateDet (e'.1 - q) h, coordinateDet f e'.2)) : e = e' := by
  have ha := congrArg Prod.fst hab
  have hb := congrArg Prod.snd hab
  apply Prod.ext
  · apply det_coordinates_injective f h hΔ e.1 e'.1 (he.1.trans he'.1.symm)
    dsimp [coordinateDet] at *
    change (e.1.1 - q.1) * h.2 - (e.1.2 - q.2) * h.1 =
      (e'.1.1 - q.1) * h.2 - (e'.1.2 - q.2) * h.1 at ha
    linear_combination ha
  · apply det_coordinates_injective f h hΔ e.2 e'.2 hb
    have hv := he.2
    have hv' := he'.2
    change h.1 * (e.2.2 - q.2) - h.2 * (e.2.1 - q.1) = 0 at hv
    change h.1 * (e'.2.2 - q.2) - h.2 * (e'.2.1 - q.1) = 0 at hv'
    dsimp [coordinateDet]
    linear_combination hv' - hv

/-- Finite divisor bound for the actual bounded integer endpoints on one
orientation of the two modular lines. All three integer lifts are derived. -/
theorem oriented_modular_line_partner_count {p : ℕ} {J₁ J₂ : ℝ}
    (E : Finset Coordinate) (q f h : Coordinate)
    (hq : CoordinateBound J₁ J₂ q) (hf : CoordinateBound J₁ J₂ f)
    (hh : CoordinateBound (2 * J₁) (2 * J₂) h)
    (hE : ∀ z ∈ E, CoordinateBound J₁ J₂ z)
    (hsmall : 8 * J₁ * J₂ < p)
    (hΔ : coordinateDet f h ≠ 0)
    (hAC : coordinateDet q h * coordinateDet q f ≠ 0) :
    ((E ×ˢ E).filter (ModularLinePair p q f h)).card ≤
      (Int.divisorsAntidiag (coordinateDet q h * coordinateDet q f)).card := by
  classical
  let S := (E ×ˢ E).filter (ModularLinePair p q f h)
  have hlift (e : Endpoint) (he : e ∈ S) := by
    obtain ⟨hmem, hm⟩ := Finset.mem_filter.mp he
    obtain ⟨hz, hv⟩ := Finset.mem_product.mp hmem
    exact modular_line_pair_integer_lift q f h e hq hf hh (hE _ hz) (hE _ hv) hsmall hm
  apply Finset.card_le_card_of_injOn
    (fun e => (coordinateDet (e.1 - q) h, coordinateDet f e.2))
  · intro e he
    exact Int.mem_divisorsAntidiag.mpr
      ⟨determinant_divisor_identity q f h e (hlift e he).1 (hlift e he).2.1
        (hlift e he).2.2, hAC⟩
  · intro e he e' he' hab
    exact divisor_coordinates_injective q f h hΔ e e'
      ⟨(hlift e he).1, (hlift e he).2.1⟩
      ⟨(hlift e' he').1, (hlift e' he').2.1⟩ hab

/-- The divisor constant has size at most 8(J₁J₂)²; the hypothesis
8J₁J₂ < p therefore gives a strict p² bound without assuming (J₁J₂)² < p. -/
theorem modular_line_divisor_height {p : ℕ} {J₁ J₂ : ℝ}
    (q f h : Coordinate) (hq : CoordinateBound J₁ J₂ q)
    (hf : CoordinateBound J₁ J₂ f) (hh : CoordinateBound (2 * J₁) (2 * J₂) h)
    (hsmall : 8 * J₁ * J₂ < p) :
    |((coordinateDet q h * coordinateDet q f : ℤ) : ℝ)| ≤ 8 * (J₁ * J₂)^2 ∧
      |((coordinateDet q h * coordinateDet q f : ℤ) : ℝ)| < (p : ℝ)^2 := by
  have hJ₁ : 0 ≤ J₁ := (abs_nonneg _).trans hq.1
  have hJ₂ : 0 ≤ J₂ := (abs_nonneg _).trans hq.2
  have hD : 0 ≤ J₁ * J₂ := mul_nonneg hJ₁ hJ₂
  have hA := det_bound hq hh
  have hC := det_bound hq hf
  have hA' : |(coordinateDet q h : ℝ)| ≤ 4 * (J₁ * J₂) := by nlinarith
  have hC' : |(coordinateDet q f : ℝ)| ≤ 2 * (J₁ * J₂) := by nlinarith
  have hb := mul_le_mul hA' hC' (abs_nonneg _) (by positivity : 0 ≤ 4 * (J₁ * J₂))
  rw [Int.cast_mul, abs_mul]
  constructor <;> nlinarith [sq_nonneg ((p : ℝ) - 8 * (J₁ * J₂))]


/-- Both endpoint orientations cost at most a factor of two. The set consists
of actual elements of E, including repeated endpoints if the equations allow them. -/
theorem modular_line_partner_count {p : ℕ} {J₁ J₂ : ℝ}
    (E : Finset Coordinate) (q f h : Coordinate)
    (hq : CoordinateBound J₁ J₂ q) (hf : CoordinateBound J₁ J₂ f)
    (hh : CoordinateBound (2 * J₁) (2 * J₂) h)
    (hE : ∀ z ∈ E, CoordinateBound J₁ J₂ z)
    (hsmall : 8 * J₁ * J₂ < p)
    (hΔ : coordinateDet f h ≠ 0)
    (hAC : coordinateDet q h * coordinateDet q f ≠ 0) :
    ((E ×ˢ E).filter (fun e => ModularLinePair p q f h e ∨
      ModularLinePair p q f h e.swap)).card ≤
        2 * (Int.divisorsAntidiag (coordinateDet q h * coordinateDet q f)).card ∧
    |((coordinateDet q h * coordinateDet q f : ℤ) : ℝ)| ≤ 8 * (J₁ * J₂)^2 ∧
    |((coordinateDet q h * coordinateDet q f : ℤ) : ℝ)| < (p : ℝ)^2 := by
  classical
  refine ⟨?_, modular_line_divisor_height q f h hq hf hh hsmall⟩
  have hswap : ((E ×ˢ E).filter (fun e => ModularLinePair p q f h e.swap)).card =
      ((E ×ˢ E).filter (ModularLinePair p q f h)).card := by
    apply Finset.card_bij (fun e _ => e.swap)
    · intro e he
      obtain ⟨hm, hp⟩ := Finset.mem_filter.mp he
      obtain ⟨hz, hv⟩ := Finset.mem_product.mp hm
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv, hz⟩, hp⟩
    · intro e _ e' _ he
      exact Prod.swap_injective he
    · intro e he
      refine ⟨e.swap, ?_, by simp⟩
      obtain ⟨hm, hp⟩ := Finset.mem_filter.mp he
      obtain ⟨hz, hv⟩ := Finset.mem_product.mp hm
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv, hz⟩, by simpa using hp⟩
  rw [Finset.filter_or]
  have hc := Finset.card_union_le
    ((E ×ˢ E).filter (ModularLinePair p q f h))
    ((E ×ˢ E).filter (fun e => ModularLinePair p q f h e.swap))
  rw [hswap] at hc
  have hb := oriented_modular_line_partner_count E q f h hq hf hh hE hsmall hΔ hAC
  omega

/-- The actual regular dividing branch is bounded by the signed divisor
count, with the line cover supplied by its mapped pencil. -/
theorem regular_dividing_modular_zero_partner_count {p : ℕ} [Fact p.Prime]
    {J₁ J₂ : ℝ} (E : Finset Coordinate) (α β : ZMod p)
    (q a b : Coordinate) (c : ZMod p)
    (hqBound : CoordinateBound J₁ J₂ q)
    (hbBound : CoordinateBound J₁ J₂ b)
    (hhBound : CoordinateBound (2 * J₁) (2 * J₂) (a - q))
    (hE : ∀ z ∈ E, CoordinateBound J₁ J₂ z)
    (hsmall : 8 * J₁ * J₂ < p)
    (hc : c ≠ 0)
    (hD : (coordinateDet b q : ZMod p) ≠ 0)
    (hq : (q.1 : ZMod p) = (b.1 : ZMod p) + (1 - c) * a.1 ∧
      (q.2 : ZMod p) = (b.2 : ZMod p) + (1 - c) * a.2)
    (hΔ : coordinateDet b (a - q) ≠ 0)
    (hAC : coordinateDet q (a - q) * coordinateDet q b ≠ 0) :
    (modularZeroPartners E α β q (a, b)).card ≤
      2 * (Int.divisorsAntidiag
        (coordinateDet q (a - q) * coordinateDet q b)).card := by
  apply le_trans ?_
    (modular_line_partner_count E q b (a - q) hqBound hbBound hhBound hE
      hsmall hΔ hAC).1
  apply Finset.card_le_card
  intro e he
  obtain ⟨hm, _, hp⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨hm,
    regular_dividing_actual_line_cover q a b e c hc hD hq hp⟩

/-- The signed divisor count used above inherits the classical subpower
bound from the natural divisor count. -/
theorem signed_divisors_antidiag_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℤ, k ≠ 0 →
      ((Int.divisorsAntidiag k).card : ℝ) ≤ C * (k.natAbs : ℝ)^ε := by
  obtain ⟨C, hC, hbound⟩ :=
    D5.S3.Arith.Divisors.DivisorSubpower.card_divisors_subpower ε hε
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro k hk
  have hcard : (Int.divisorsAntidiag k).card ≤ k.divisors.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro xy hxy
      rw [← Int.image_fst_divisorsAntidiag]
      exact Finset.mem_image.mpr ⟨xy, hxy, rfl⟩
    · intro x hx y hy hxy
      apply Prod.ext hxy
      have hxmul := (Int.mem_divisorsAntidiag.mp hx).1
      have hymul := (Int.mem_divisorsAntidiag.mp hy).1
      have hx0 : x.1 ≠ 0 := by
        intro hz
        apply hk
        simpa [hz] using hxmul.symm
      apply mul_left_cancel₀ hx0
      simpa [hxy] using hxmul.trans hymul.symm
  have hcount : k.divisors.card = 2 * k.natAbs.divisors.card := by
    unfold Int.divisors
    rw [Finset.card_disjUnion, Finset.card_map, Finset.card_map]
    omega
  have hn : k.natAbs ≠ 0 := by simpa using hk
  have hpow := hbound k.natAbs hn
  have hcardR : ((Int.divisorsAntidiag k).card : ℝ) ≤
      (k.divisors.card : ℝ) := by exact_mod_cast hcard
  rw [hcount, Nat.cast_mul, Nat.cast_ofNat] at hcardR
  exact hcardR.trans (by
    convert mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring)

/-- In the regular dividing branch, the divisor estimate and determinant
height give a uniform subpower bound in the prime. -/
theorem regular_dividing_modular_zero_partner_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (J₁ J₂ : ℝ)
      (E : Finset Coordinate) (α β : ZMod p) (q a b : Coordinate) (c : ZMod p),
      CoordinateBound J₁ J₂ q →
      CoordinateBound J₁ J₂ b →
      CoordinateBound (2 * J₁) (2 * J₂) (a - q) →
      (∀ z ∈ E, CoordinateBound J₁ J₂ z) →
      8 * J₁ * J₂ < p →
      c ≠ 0 →
      (coordinateDet b q : ZMod p) ≠ 0 →
      ((q.1 : ZMod p) = (b.1 : ZMod p) + (1 - c) * a.1 ∧
        (q.2 : ZMod p) = (b.2 : ZMod p) + (1 - c) * a.2) →
      coordinateDet b (a - q) ≠ 0 →
      coordinateDet q (a - q) * coordinateDet q b ≠ 0 →
      ((modularZeroPartners E α β q (a, b)).card : ℝ) ≤ C * (p : ℝ)^ε := by
  obtain ⟨C, hC, hbound⟩ := signed_divisors_antidiag_subpower (ε / 2) (by positivity)
  refine ⟨4 * C, mul_pos (by norm_num) hC, ?_⟩
  intro p hp J₁ J₂ E α β q a b c hqBound hbBound hhBound hE hsmall
    hc hD hq hΔ hAC
  letI : Fact p.Prime := ⟨hp⟩
  let k := coordinateDet q (a - q) * coordinateDet q b
  have hk : k ≠ 0 := hAC
  have hcard := regular_dividing_modular_zero_partner_count E α β q a b c
    hqBound hbBound hhBound hE hsmall hc hD hq hΔ hAC
  have hheight := (modular_line_divisor_height q b (a - q)
    hqBound hbBound hhBound hsmall).2
  have hnat : (k.natAbs : ℝ) < (p : ℝ)^2 := by
    simpa [k, Nat.cast_natAbs] using hheight
  have hpow : (k.natAbs : ℝ)^(ε / 2) ≤ (p : ℝ)^ε := by
    have hh := (Real.rpow_lt_rpow (Nat.cast_nonneg _) hnat (by positivity : 0 < ε / 2)).le
    have hpnonneg : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    rw [← Real.rpow_natCast_mul hpnonneg 2 (ε / 2)] at hh
    simpa [show (2 : ℝ) * (ε / 2) = ε by ring] using hh
  have hd := hbound k hk
  have hcardR : ((modularZeroPartners E α β q (a, b)).card : ℝ) ≤
      2 * ((Int.divisorsAntidiag k).card : ℝ) := by exact_mod_cast hcard
  calc
    _ ≤ 2 * ((Int.divisorsAntidiag k).card : ℝ) := hcardR
    _ ≤ 2 * (C * (k.natAbs : ℝ)^(ε / 2)) := by gcongr
    _ ≤ 4 * C * (p : ℝ)^ε := by
      have hh := mul_le_mul_of_nonneg_left hpow (le_of_lt hC)
      nlinarith

end
end D5.S3.Arith.CharacterSums.Original
