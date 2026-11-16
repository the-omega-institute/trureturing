/- GID: D5/S3/Arith/CharacterSums/PascadiModularZeroPartners
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiModularZeroPartners
   mirror-E: none(waiver:open-original-modular-zero-partner-bound)
   anchors: []
   utility: none
   digest: Integer determinant lifts and signed divisor counts for actual modular partners. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalCoefficients
import Mathlib.NumberTheory.Divisors

/-! # Modular-zero partners in the original integer chart

The finite partner set uses the original endpoint pencil. The determinant count
below supplies the integer lift and divisor injection for an oriented pair of
modular lines. Deriving the two orientations from polynomial degeneracy, and
the nondividing absolute bound, remain separate obligations.
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


end
end D5.S3.Arith.CharacterSums.Original
