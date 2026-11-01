/- GID: D5/S3/HomologicalAlgebra/FinitePerturbation
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/FinitePerturbation
   mirror-E: none(waiver:algebraic-inference)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Finite polynomial basic perturbation of an actual strong deformation retraction. -/

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
The classical basic perturbation lemma of Gugenheim--Lambe--Stasheff, with finite
polynomials and a one-sided nilpotence bound. This is an algebraic inference;
it supplies no physical BRST nilpotence, quartet contraction or no-ghost input.
-/
/-
proof_shape: finite_perturbation: content
admission_basis: escape-witness
escape_witness: master, deriving the transferred Maurer--Cartan identity by
  invertible noncommutative residual cancellation, consumed by the full retraction.
The elementary inverse, push-through and representative helpers are consumed
proof organization; geometric sums and nilpotent units come from pinned Mathlib.
No mathematical novelty is asserted.
-/
namespace D5.S3.HomologicalAlgebra.FinitePerturbation

open Finset

section Ring
variable {S : Type*} [Ring S]

def inversePolynomial (a : S) (n : ℕ) : S := ∑ j ∈ range n, (-a) ^ j

private theorem series_inverse (a : S) (n : ℕ) (ha : a ^ n = 0) :
    inversePolynomial a n * (1 + a) = 1 ∧ (1 + a) * inversePolynomial a n = 1 := by
  have hn : (-a) ^ n = 0 := by rw [neg_pow, ha, mul_zero]
  constructor
  · simpa [inversePolynomial, hn] using geom_sum_mul_neg (-a) n
  · simpa [inversePolynomial, hn] using mul_neg_geom_sum (-a) n

private theorem opposite_power (h t : S) (n : ℕ) :
    (t * h) ^ (n + 1) = t * (h * t) ^ n * h := by
  rw [pow_succ, ← mul_assoc, mul_pow_mul]

private theorem inverse_push (h t k j : S)
    (hk : k * (1 + h * t) = 1) (hk' : (1 + h * t) * k = 1)
    (hj : (1 + t * h) * j = 1) (hj' : j * (1 + t * h) = 1) :
    k * h = h * j ∧ t * k = j * t := by
  constructor
  · calc
      k * h = k * h * ((1 + t * h) * j) := by rw [hj, mul_one]
      _ = (k * (1 + h * t)) * h * j := by noncomm_ring
      _ = h * j := by rw [hk, one_mul]
  · calc
      t * k = (j * (1 + t * h)) * (t * k) := by rw [hj', one_mul]
      _ = j * t * ((1 + h * t) * k) := by noncomm_ring
      _ = j * t := by rw [hk', mul_one]

private theorem master (d h t e k : S)
    (hd : d * d = 0) (hD : (d + t) * (d + t) = 0)
    (hc : d * h + h * d = 1 - e)
    (hk : k * (1 + h * t) = 1) (hk' : (1 + h * t) * k = 1)
    (uk : IsUnit (1 + h * t)) (uj : IsUnit (1 + t * h)) :
    let T := t * k
    d * T + T * d + T * e * T = 0 := by
  dsimp only
  let T := t * k
  have tr : T * (1 + h * t) = t := by dsimp [T]; rw [mul_assoc, hk, mul_one]
  have lt : (1 + t * h) * T = t := by
    dsimp [T]
    calc
      (1 + t * h) * (t * k) = t * ((1 + h * t) * k) := by noncomm_ring
      _ = t := by rw [hk', mul_one]
  have hc' : h * d + d * h + e = 1 := by linear_combination (norm := noncomm_ring) hc
  have sand : (1 + t * h) * (d * T + T * d + T * e * T) * (1 + h * t) = 0 := by
    calc
      _ = (1 + t * h) * d * (T * (1 + h * t)) + ((1 + t * h) * T) * d * (1 + h * t) +
          ((1 + t * h) * T) * e * (T * (1 + h * t)) := by noncomm_ring
      _ = (1 + t * h) * d * t + t * d * (1 + h * t) + t * e * t := by rw [tr, lt]
      _ = d * t + t * d + t * (h * d + d * h + e) * t := by noncomm_ring
      _ = d * t + t * d + t * t := by rw [hc', mul_one]
      _ = 0 := by linear_combination (norm := noncomm_ring) hD - hd
  apply uk.mul_right_cancel
  apply uj.mul_left_cancel
  simpa only [T, mul_assoc, mul_zero, zero_mul] using sand

private theorem core (d h t e k j : S)
    (hd : d * d = 0) (hD : (d + t) * (d + t) = 0)
    (hc : d * h + h * d = 1 - e)
    (hk : k * (1 + h * t) = 1) (hk' : (1 + h * t) * k = 1)
    (hj : j * (1 + t * h) = 1) (hj' : (1 + t * h) * j = 1)
    (uk : IsUnit (1 + h * t)) (uj : IsUnit (1 + t * h)) :
    let T := t * k
    (d + t) * k = k * d + k * e * T ∧
    j * (d + t) = d * j + T * e * j ∧
    (d + t) * (k * h) + (k * h) * (d + t) = 1 - k * e * j := by
  dsimp only
  let T := t * k
  have hm : d * T + T * d + T * e * T = 0 := master d h t e k hd hD hc hk hk' uk uj
  have hp := inverse_push h t k j hk hk' hj' hj
  have ht : T = j * t := hp.2
  have hkt : k = 1 - h * T := by
    have eq := hk'
    change (1 + h * t) * k = 1 at eq
    dsimp [T]
    linear_combination (norm := noncomm_ring) eq
  have hjt : j = 1 - T * h := by
    linear_combination (norm := noncomm_ring) hj + ht * h
  have tr : T * (1 + h * t) = t := by dsimp [T]; rw [mul_assoc, hk, mul_one]
  have lt : (1 + t * h) * T = t := by rw [ht, ← mul_assoc, hj', one_mul]
  have hc' : 1 - d * h - h * d - e = 0 := by linear_combination (norm := noncomm_ring) - hc
  have dk : (d + t) * k = k * d + k * e * T := by
    rw [hkt]
    linear_combination (norm := noncomm_ring) h * hm + hc' * T - lt
  have jd : j * (d + t) = d * j + T * e * j := by
    rw [hjt]
    linear_combination (norm := noncomm_ring) hm * h + T * hc' - tr
  refine ⟨dk, jd, ?_⟩
  calc
    (d + t) * (k * h) + (k * h) * (d + t) =
        (k * d + k * e * T) * h + h * (d * j + T * e * j) := by
      rw [← mul_assoc, dk, hp.1, mul_assoc h j (d + t), jd]
    _ = 1 - k * e * j := by
      rw [hkt, hjt]
      linear_combination (norm := noncomm_ring) hc - h * hm * h

end Ring

section Modules
variable {R U V : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]

/-- Only the unperturbed identities and the actual perturbed square enter the input. -/
structure Input where
  d0 : Module.End R V
  h : Module.End R V
  delta : Module.End R V
  i : U →ₗ[R] V
  p : V →ₗ[R] U
  d0_sq : d0 * d0 = 0
  pi : p.comp i = LinearMap.id
  di : d0.comp i = 0
  pd : p.comp d0 = 0
  contraction : d0 * h + h * d0 = 1 - i.comp p
  hh : h * h = 0
  hi : h.comp i = 0
  ph : p.comp h = 0
  perturbed_sq : (d0 + delta) * (d0 + delta) = 0

namespace Input

variable (c : Input (R := R) (U := U) (V := V))

/-- Left inverse polynomial: N terms for h delta. -/
def K (n : ℕ) : Module.End R V := inversePolynomial (c.h * c.delta) n
/-- Right inverse polynomial: N+1 terms for delta h. -/
def J (n : ℕ) : Module.End R V := inversePolynomial (c.delta * c.h) (n + 1)
def D : Module.End R V := c.d0 + c.delta
def I (n : ℕ) : U →ₗ[R] V := (c.K n).comp c.i
def P (n : ℕ) : V →ₗ[R] U := c.p.comp (c.J n)
def H (n : ℕ) : Module.End R V := c.K n * c.h
def transferred (n : ℕ) : Module.End R U := c.p.comp (c.delta.comp (c.I n))

/-- All assertions are conclusions of the perturbation inference, never input fields. -/
structure Retraction (n : ℕ) : Prop where
  opposite_nilpotent : (c.delta * c.h) ^ (n + 1) = 0
  K_left : c.K n * (1 + c.h * c.delta) = 1
  K_right : (1 + c.h * c.delta) * c.K n = 1
  J_left : c.J n * (1 + c.delta * c.h) = 1
  J_right : (1 + c.delta * c.h) * c.J n = 1
  push_h : c.K n * c.h = c.h * c.J n
  push_delta : c.delta * c.K n = c.J n * c.delta
  transferred_sq : c.transferred n * c.transferred n = 0
  inclusion_chain : c.D.comp (c.I n) = (c.I n).comp (c.transferred n)
  projection_chain : (c.P n).comp c.D = (c.transferred n).comp (c.P n)
  retract : (c.P n).comp (c.I n) = LinearMap.id
  homotopy : c.D * c.H n + c.H n * c.D = 1 - (c.I n).comp (c.P n)
  homotopy_sq : c.H n * c.H n = 0
  homotopy_inclusion : (c.H n).comp (c.I n) = 0
  projection_homotopy : (c.P n).comp (c.H n) = 0

/-- The finite basic perturbation lemma, including the asymmetric opposite bound. -/
private theorem finite_retraction (n : ℕ) (hn : 1 ≤ n)
    (nilpotent : (c.h * c.delta) ^ n = 0) : c.Retraction n := by
  have nb : (c.delta * c.h) ^ (n + 1) = 0 := by
    rw [opposite_power, nilpotent, mul_zero, zero_mul]
  have uk : IsUnit (1 + c.h * c.delta) :=
    (show IsNilpotent (c.h * c.delta) from ⟨n,nilpotent⟩).isUnit_one_add
  have uj : IsUnit (1 + c.delta * c.h) :=
    (show IsNilpotent (c.delta * c.h) from ⟨n + 1,nb⟩).isUnit_one_add
  obtain ⟨kl, kr⟩ := series_inverse (c.h * c.delta) n nilpotent
  obtain ⟨jl, jr⟩ := series_inverse (c.delta * c.h) (n + 1) nb
  change c.K n * (1 + c.h * c.delta) = 1 at kl
  change (1 + c.h * c.delta) * c.K n = 1 at kr
  change c.J n * (1 + c.delta * c.h) = 1 at jl
  change (1 + c.delta * c.h) * c.J n = 1 at jr
  obtain ⟨pushh, pusht⟩ := inverse_push c.h c.delta (c.K n) (c.J n) kl kr jr jl
  let T : Module.End R V := c.delta * c.K n
  have tm : c.d0 * T + T * c.d0 + T * (c.i.comp c.p) * T = 0 :=
    master c.d0 c.h c.delta (c.i.comp c.p) (c.K n)
      c.d0_sq c.perturbed_sq c.contraction kl kr uk uj
  obtain ⟨dk, jd, hom⟩ := core c.d0 c.h c.delta (c.i.comp c.p) (c.K n) (c.J n)
      c.d0_sq c.perturbed_sq c.contraction kl kr jl jr uk uj
  have kform : c.K n = 1 - c.h * T := by
    linear_combination (norm := noncomm_ring) kr
  have jform : c.J n = 1 - T * c.h := by
    dsimp [T]
    linear_combination (norm := noncomm_ring) jl + pusht * c.h
  have hdi (u : U) : c.d0 (c.i u) = 0 := DFunLike.congr_fun c.di u
  have hpd (v : V) : c.p (c.d0 v) = 0 := DFunLike.congr_fun c.pd v
  have hhi (u : U) : c.h (c.i u) = 0 := DFunLike.congr_fun c.hi u
  have hph (v : V) : c.p (c.h v) = 0 := DFunLike.congr_fun c.ph v
  have hhh (v : V) : c.h (c.h v) = 0 := DFunLike.congr_fun c.hh v
  have hpi (u : U) : c.p (c.i u) = u := DFunLike.congr_fun c.pi u
  have inc : c.D.comp (c.I n) = (c.I n).comp (c.transferred n) := by
    ext u
    have eq := DFunLike.congr_fun dk (c.i u)
    simpa [D, I, transferred, T, hdi] using eq
  have proj : (c.P n).comp c.D = (c.transferred n).comp (c.P n) := by
    ext v
    have eq := congrArg c.p (DFunLike.congr_fun jd v)
    simpa [P, D, transferred, I, T, hpd] using eq
  have sq : c.transferred n * c.transferred n = 0 := by
    ext u
    have eq := congrArg c.p (DFunLike.congr_fun tm (c.i u))
    simpa [transferred, I, T, hdi, hpd] using eq
  have ret : (c.P n).comp (c.I n) = LinearMap.id := by
    ext u
    simp [P, I, kform, jform, hhi, hph, hhh, hpi]
  have hk : c.h * c.K n = c.h := by
    rw [kform]
    linear_combination (norm := noncomm_ring) - c.hh * T
  have jh : c.J n * c.h = c.h := by
    rw [jform]
    linear_combination (norm := noncomm_ring) - T * c.hh
  refine ⟨nb, kl, kr, jl, jr, pushh, pusht, sq, inc, proj, ret, ?_, ?_, ?_, ?_⟩
  · simpa only [D, H, I, P, Module.End.mul_eq_comp, LinearMap.comp_assoc] using hom
  · change (c.K n * c.h) * (c.K n * c.h) = 0
    calc
      _ = c.K n * (c.h * c.K n) * c.h := by noncomm_ring
      _ = 0 := by rw [hk, mul_assoc, c.hh, mul_zero]
  · ext u
    change (c.K n) (c.h ((c.K n) (c.i u))) = 0
    have eq := DFunLike.congr_fun hk (c.i u)
    simpa [hhi] using congrArg (c.K n) eq
  · ext v
    change c.p ((c.J n) ((c.K n * c.h) v)) = 0
    rw [pushh]
    have eq := DFunLike.congr_fun jh ((c.J n) v)
    simpa [hph] using congrArg c.p eq

/-- With zero transferred differential, every cycle has an explicit lift and primitive.
The last equivalence detects boundaries by the original projection. -/
private theorem zero_transfer_representatives (n : ℕ) (hn : 1 ≤ n)
    (nilpotent : (c.h * c.delta) ^ n = 0) (zero_transfer : c.transferred n = 0) :
    (∀ u : U, c.D (c.I n u) = 0 ∧ c.P n (c.I n u) = u) ∧
    (∀ x : V, c.D x = 0 → x - c.I n (c.P n x) = c.D (c.H n x)) ∧
    (∀ x : V, c.D x = 0 → ((∃ y : V, c.D y = x) ↔ c.P n x = 0)) := by
  have out := finite_retraction c n hn nilpotent
  have ci (u : U) : c.D (c.I n u) = 0 := by
    have eq := DFunLike.congr_fun out.inclusion_chain u
    simpa [zero_transfer] using eq
  have pc (x : V) : c.P n (c.D x) = 0 := by
    have eq := DFunLike.congr_fun out.projection_chain x
    simpa [zero_transfer] using eq
  have primitive (x : V) (hx : c.D x = 0) :
      x - c.I n (c.P n x) = c.D (c.H n x) := by
    have eq := DFunLike.congr_fun out.homotopy x
    simpa [hx] using eq.symm
  refine ⟨fun u => ⟨ci u, DFunLike.congr_fun out.retract u⟩, primitive, ?_⟩
  intro x hx
  constructor
  · rintro ⟨y, rfl⟩
    exact pc y
  · intro hp
    refine ⟨c.H n x, ?_⟩
    simpa [hp] using (primitive x hx).symm

/-- The full retraction and its explicit zero-transfer cohomology interface. -/
structure Conclusion (n : ℕ) : Prop extends c.Retraction n where
  representatives : c.transferred n = 0 →
    (∀ u : U, c.D (c.I n u) = 0 ∧ c.P n (c.I n u) = u) ∧
    (∀ x : V, c.D x = 0 → x - c.I n (c.P n x) = c.D (c.H n x)) ∧
    (∀ x : V, c.D x = 0 → ((∃ y : V, c.D y = x) ↔ c.P n x = 0))

/-- Finite polynomial basic perturbation, with one-sided nilpotence and explicit primitives. -/
theorem finite_perturbation (n : ℕ) (hn : 1 ≤ n)
    (nilpotent : (c.h * c.delta) ^ n = 0) : c.Conclusion n :=
  ⟨finite_retraction c n hn nilpotent, zero_transfer_representatives c n hn nilpotent⟩

end Input

end Modules
end D5.S3.HomologicalAlgebra.FinitePerturbation
