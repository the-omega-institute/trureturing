/- GID: D5/S3/HomologicalAlgebra/FinitePerturbation
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/FinitePerturbation
   mirror-E: none(waiver:algebraic-inference)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: kind=framework; basis=none
   digest: Finite polynomial basic perturbation of an actual strong deformation retraction. -/

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.LinearAlgebra.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
The classical basic perturbation lemma of Gugenheim--Lambe--Stasheff, with finite
polynomials and a one-sided nilpotence bound. This is an algebraic inference;
it supplies no physical BRST nilpotence, quartet contraction or no-ghost input.
-/
namespace D5.S3.HomologicalAlgebra.FinitePerturbation

open Finset

section Ring
variable {S : Type*} [Ring S]

private def series (a : S) (n : ℕ) : S := ∑ j ∈ range n, (-a) ^ j

private theorem series_inverse (a : S) (n : ℕ) (ha : a ^ n = 0) :
    series a n * (1 + a) = 1 ∧ (1 + a) * series a n = 1 := by
  have hn : (-a) ^ n = 0 := by rw [neg_pow, ha, mul_zero]
  constructor
  · simpa [series, hn] using geom_sum_mul_neg (-a) n
  · simpa [series, hn] using mul_neg_geom_sum (-a) n

private theorem opposite_power (h t : S) (n : ℕ) :
    (t * h) ^ (n + 1) = t * (h * t) ^ n * h := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; noncomm_ring

private theorem inverse_push (h t k j : S)
    (hk : k * (1 + h*t) = 1) (hk' : (1+h*t)*k = 1)
    (hj : (1 + t*h) * j = 1) (hj' : j*(1+t*h) = 1) :
    k*h = h*j ∧ t*k = j*t := by
  constructor
  · calc
      k*h = k*h*((1+t*h)*j) := by rw [hj, mul_one]
      _ = (k*(1+h*t))*h*j := by noncomm_ring
      _ = h*j := by rw [hk, one_mul]
  · calc
      t*k = (j*(1+t*h))*(t*k) := by rw [hj', one_mul]
      _ = j*t*((1+h*t)*k) := by noncomm_ring
      _ = j*t := by rw [hk', mul_one]

private theorem master (d h t e k j : S)
    (hd : d*d = 0) (hD : (d+t)*(d+t) = 0)
    (hc : d*h+h*d = 1-e)
    (hk : k*(1+h*t) = 1) (hk' : (1+h*t)*k = 1)
    (hj : j*(1+t*h) = 1) (hj' : (1+t*h)*j = 1) :
    let T := t*k
    d*T+T*d+T*e*T = 0 := by
  dsimp only
  let T := t*k
  have tr : T*(1+h*t) = t := by dsimp [T]; rw [mul_assoc, hk, mul_one]
  have lt : (1+t*h)*T = t := by
    dsimp [T]
    calc
      (1+t*h)*(t*k) = t*((1+h*t)*k) := by noncomm_ring
      _ = t := by rw [hk', mul_one]
  have hc' : h*d+d*h+e = 1 := by linear_combination hc
  have sand : (1+t*h)*(d*T+T*d+T*e*T)*(1+h*t) = 0 := by
    calc
      _ = (1+t*h)*d*(T*(1+h*t))+((1+t*h)*T)*d*(1+h*t)+
          ((1+t*h)*T)*e*(T*(1+h*t)) := by noncomm_ring
      _ = (1+t*h)*d*t+t*d*(1+h*t)+t*e*t := by rw [tr, lt]
      _ = d*t+t*d+t*(h*d+d*h+e)*t := by noncomm_ring
      _ = d*t+t*d+t*t := by rw [hc', mul_one]
      _ = 0 := by linear_combination (norm := noncomm_ring) hD - hd
  have cancel := congrArg (fun z => j*z*k) sand
  simpa only [mul_assoc, ← mul_assoc j (1+t*h), hj, one_mul,
    hk', mul_one, mul_zero, zero_mul] using cancel

private theorem core (d h t e k j : S)
    (hd : d*d = 0) (hD : (d+t)*(d+t) = 0)
    (hc : d*h+h*d = 1-e)
    (hk : k*(1+h*t) = 1) (hk' : (1+h*t)*k = 1)
    (hj : j*(1+t*h) = 1) (hj' : (1+t*h)*j = 1) :
    let T := t*k
    (d+t)*k = k*d+k*e*T ∧
    j*(d+t) = d*j+T*e*j ∧
    (d+t)*(k*h)+(k*h)*(d+t) = 1-k*e*j := by
  dsimp only
  let T := t*k
  have hm : d*T+T*d+T*e*T = 0 := master d h t e k j hd hD hc hk hk' hj hj'
  have hp := inverse_push h t k j hk hk' hj' hj
  have ht : T = j*t := hp.2
  have hkt : k = 1-h*T := by
    have eq := hk'
    change (1+h*t)*k = 1 at eq
    dsimp [T]
    linear_combination (norm := noncomm_ring) eq
  have hjt : j = 1-T*h := by
    have eq := hj
    rw [← ht] at eq
    linear_combination (norm := noncomm_ring) eq
  have tr : T*(1+h*t) = t := by dsimp [T]; rw [mul_assoc, hk, mul_one]
  have lt : (1+t*h)*T = t := by rw [ht, ← mul_assoc, hj', one_mul]
  have hc' : 1-d*h-h*d-e = 0 := by linear_combination hc
  have dk : (d+t)*k = k*d+k*e*T := by
    rw [hkt]
    linear_combination (norm := noncomm_ring) h*hm + hc'*T - lt
  have jd : j*(d+t) = d*j+T*e*j := by
    rw [hjt]
    linear_combination (norm := noncomm_ring) hm*h + T*hc' - tr
  refine ⟨dk, jd, ?_⟩
  calc
    (d+t)*(k*h)+(k*h)*(d+t) =
        (k*d+k*e*T)*h+h*(d*j+T*e*j) := by
      rw [← mul_assoc, dk, hp.1, mul_assoc, jd]
    _ = 1-k*e*j := by
      rw [hkt, hjt]
      linear_combination (norm := noncomm_ring) hc - h*hm*h

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
  d0_sq : d0*d0 = 0
  pi : p.comp i = LinearMap.id
  di : d0.comp i = 0
  pd : p.comp d0 = 0
  contraction : d0*h+h*d0 = 1-i.comp p
  hh : h*h = 0
  hi : h.comp i = 0
  ph : p.comp h = 0
  perturbed_sq : (d0+delta)*(d0+delta) = 0

variable (c : Input (R := R) (U := U) (V := V))

/-- Left inverse polynomial: N terms for h delta. -/
def K (n : ℕ) : Module.End R V := series (c.h*c.delta) n
/-- Right inverse polynomial: N+1 terms for delta h. -/
def J (n : ℕ) : Module.End R V := series (c.delta*c.h) (n+1)
def D : Module.End R V := c.d0+c.delta
def I (n : ℕ) : U →ₗ[R] V := (c.K n).comp c.i
def P (n : ℕ) : V →ₗ[R] U := c.p.comp (c.J n)
def H (n : ℕ) : Module.End R V := c.K n*c.h
def transferred (n : ℕ) : Module.End R U := c.p.comp (c.delta.comp (c.I n))

/-- All assertions are conclusions of the perturbation inference, never input fields. -/
structure Conclusion (n : ℕ) : Prop where
  opposite_nilpotent : (c.delta*c.h)^(n+1) = 0
  K_left : c.K n*(1+c.h*c.delta) = 1
  K_right : (1+c.h*c.delta)*c.K n = 1
  J_left : c.J n*(1+c.delta*c.h) = 1
  J_right : (1+c.delta*c.h)*c.J n = 1
  push_h : c.K n*c.h = c.h*c.J n
  push_delta : c.delta*c.K n = c.J n*c.delta
  transferred_sq : c.transferred n*c.transferred n = 0
  inclusion_chain : c.D.comp (c.I n) = (c.I n).comp (c.transferred n)
  projection_chain : (c.P n).comp c.D = (c.transferred n).comp (c.P n)
  retract : (c.P n).comp (c.I n) = LinearMap.id
  homotopy : c.D*c.H n+c.H n*c.D = 1-(c.I n).comp (c.P n)
  homotopy_sq : c.H n*c.H n = 0
  homotopy_inclusion : (c.H n).comp (c.I n) = 0
  projection_homotopy : (c.P n).comp (c.H n) = 0

end Modules
end D5.S3.HomologicalAlgebra.FinitePerturbation
