/- GID: D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbation
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/LocallyNilpotentPerturbation
   mirror-E: none(waiver:algebraic-inference)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Actual cohomology quotients and pointwise perturbation retractions. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.HomologicalAlgebra.FinitePerturbation
import Mathlib.Algebra.Module.Equiv.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
The locally nilpotent algebraic basic perturbation lemma of
Gugenheim--Lambe--Stasheff. Geometric sums, endomorphism units and their inverses
come from Mathlib; the noncommutative perturbation algebra is reused from
`FinitePerturbation`. A cutoff is chosen only for an individual vector.

This supplies no local-nilpotence assertion for an original BRST operator and
does not complete the Moonshine/VOA/CFT/anomaly/fusion/string/AdS-CFT goal.
-/

open private D5.S3.HomologicalAlgebra.FinitePerturbation.inverse_push
  D5.S3.HomologicalAlgebra.FinitePerturbation.master
  D5.S3.HomologicalAlgebra.FinitePerturbation.core
  from D5.S3.HomologicalAlgebra.FinitePerturbation

namespace D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation

open FinitePerturbation

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

private theorem geometric_apply (a : Module.End R V) (n : ℕ) (x : V)
    (hx : (a ^ n) x = 0) :
    inversePolynomial a n ((1 + a) x) = x ∧
      (1 + a) (inversePolynomial a n x) = x := by
  have hn : ((-a) ^ n) x = 0 := by
    rw [neg_pow, Module.End.mul_apply, hx, map_zero]
  constructor
  · simpa only [inversePolynomial, sub_neg_eq_add, Module.End.mul_apply,
      LinearMap.sub_apply, Module.End.one_apply, hn, sub_zero] using
      DFunLike.congr_fun (geom_sum_mul_neg (-a) n) x
  · simpa only [inversePolynomial, sub_neg_eq_add, Module.End.mul_apply,
      LinearMap.sub_apply, Module.End.one_apply, hn, sub_zero] using
      DFunLike.congr_fun (mul_neg_geom_sum (-a) n) x

/-- Pointwise local nilpotence suffices for a global unit; no uniform cutoff is used.
The unit/bijection conversion is Mathlib's `Module.End.isUnit_iff`. -/
theorem isUnit_one_add_of_locally_nilpotent (a : Module.End R V)
    (nilpotent : ∀ x : V, ∃ n : ℕ, (a ^ n) x = 0) : IsUnit (1 + a) := by
  apply (Module.End.isUnit_iff (1 + a)).2
  constructor
  · intro x y hxy
    obtain ⟨n, hn⟩ := nilpotent (x - y)
    have hzero : (1 + a) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have eq := (geometric_apply a n (x - y) hn).1
    rw [hzero, map_zero] at eq
    exact sub_eq_zero.mp eq.symm
  · intro x
    obtain ⟨n, hn⟩ := nilpotent x
    exact ⟨inversePolynomial a n x, (geometric_apply a n x hn).2⟩

section Perturbation

variable {U : Type*} [AddCommGroup U] [Module R U]
variable (c : Input (R := R) (U := U) (V := V))
variable (nilpotent : ∀ x : V, ∃ n : ℕ, ((c.h * c.delta) ^ n) x = 0)

/-- The genuine global inverse of `1 + h * delta`, chosen as an endomorphism unit. -/
noncomputable def K : Module.End R V :=
  (isUnit_one_add_of_locally_nilpotent (c.h * c.delta) nilpotent).unit.inv

/-- The Woodbury/Jacobson inverse of `1 + delta * h`. -/
noncomputable def J : Module.End R V := 1 - c.delta * K c nilpotent * c.h

/-- Global perturbed inclusion. -/
noncomputable def I : U →ₗ[R] V := (K c nilpotent).comp c.i

/-- Global perturbed projection. -/
noncomputable def P : V →ₗ[R] U := c.p.comp (J c nilpotent)

/-- Global perturbed contracting homotopy. -/
noncomputable def H : Module.End R V := K c nilpotent * c.h

/-- The transferred differential, which is derived to have square zero. -/
noncomputable def transferred : Module.End R U :=
  c.p.comp (c.delta.comp (I c nilpotent))

private theorem K_inverse :
    K c nilpotent * (1 + c.h * c.delta) = 1 ∧
      (1 + c.h * c.delta) * K c nilpotent = 1 := by
  constructor
  · ext x
    exact Module.End.isUnit_inv_apply_apply_of_isUnit
      (isUnit_one_add_of_locally_nilpotent (c.h * c.delta) nilpotent) x
  · ext x
    exact Module.End.isUnit_apply_inv_apply_of_isUnit
      (isUnit_one_add_of_locally_nilpotent (c.h * c.delta) nilpotent) x

/-- On any vector killed by the indicated power, the global inverse is the
finite inverse polynomial. There is no positivity restriction on `n`:
for `n = 0` the hypothesis says precisely `x = 0`. -/
theorem K_apply_eq_inversePolynomial (x : V) (n : ℕ)
    (hx : ((c.h * c.delta) ^ n) x = 0) :
    K c nilpotent x = inversePolynomial (c.h * c.delta) n x := by
  have eq := (geometric_apply (c.h * c.delta) n x hx).2
  calc
    K c nilpotent x =
        K c nilpotent ((1 + c.h * c.delta)
          (inversePolynomial (c.h * c.delta) n x)) := congrArg (K c nilpotent) eq.symm
    _ = inversePolynomial (c.h * c.delta) n x :=
      DFunLike.congr_fun (K_inverse c nilpotent).1
        (inversePolynomial (c.h * c.delta) n x)

private theorem J_inverse :
    J c nilpotent * (1 + c.delta * c.h) = 1 ∧
      (1 + c.delta * c.h) * J c nilpotent = 1 := by
  obtain ⟨kl, kr⟩ := K_inverse c nilpotent
  constructor
  · change (1 - c.delta * K c nilpotent * c.h) * (1 + c.delta * c.h) = 1
    calc
      _ = 1 + c.delta * c.h -
          c.delta * (K c nilpotent * (1 + c.h * c.delta)) * c.h := by noncomm_ring
      _ = 1 := by rw [kl]; noncomm_ring
  · change (1 + c.delta * c.h) * (1 - c.delta * K c nilpotent * c.h) = 1
    calc
      _ = 1 + c.delta * c.h -
          c.delta * ((1 + c.h * c.delta) * K c nilpotent) * c.h := by noncomm_ring
      _ = 1 := by rw [kr]; noncomm_ring

include nilpotent in
private theorem J_isUnit : IsUnit (1 + c.delta * c.h) := by
  obtain ⟨jl, jr⟩ := J_inverse c nilpotent
  exact ⟨⟨1 + c.delta * c.h, J c nilpotent, jr, jl⟩, rfl⟩

/-- The global basic perturbation retraction from pointwise local nilpotence.
All conclusions concern the existing `Input.D` and the maps defined above.
The master identity and the two chain identities and homotopy identity are
consumed from the exact private ring facts of `FinitePerturbation`; its
module-level finite-retraction argument supplies the remaining proof pattern. -/
theorem locally_nilpotent_perturbation :
    transferred c nilpotent * transferred c nilpotent = 0 ∧
    c.D.comp (I c nilpotent) = (I c nilpotent).comp (transferred c nilpotent) ∧
    (P c nilpotent).comp c.D = (transferred c nilpotent).comp (P c nilpotent) ∧
    (P c nilpotent).comp (I c nilpotent) = LinearMap.id ∧
    c.D * H c nilpotent + H c nilpotent * c.D =
      1 - (I c nilpotent).comp (P c nilpotent) ∧
    H c nilpotent * H c nilpotent = 0 ∧
    (H c nilpotent).comp (I c nilpotent) = 0 ∧
    (P c nilpotent).comp (H c nilpotent) = 0 := by
  have uk : IsUnit (1 + c.h * c.delta) :=
    isUnit_one_add_of_locally_nilpotent (c.h * c.delta) nilpotent
  have uj : IsUnit (1 + c.delta * c.h) := J_isUnit c nilpotent
  obtain ⟨kl, kr⟩ := K_inverse c nilpotent
  obtain ⟨jl, jr⟩ := J_inverse c nilpotent
  obtain ⟨pushh, _⟩ := D5.S3.HomologicalAlgebra.FinitePerturbation.inverse_push c.h c.delta
    (K c nilpotent) (J c nilpotent) kl kr jr jl
  let T : Module.End R V := c.delta * K c nilpotent
  have tm : c.d0 * T + T * c.d0 + T * (c.i.comp c.p) * T = 0 :=
    D5.S3.HomologicalAlgebra.FinitePerturbation.master c.d0 c.h c.delta (c.i.comp c.p) (K c nilpotent)
      c.d0_sq c.perturbed_sq c.contraction kl kr uk uj
  obtain ⟨dk, jd, hom⟩ := D5.S3.HomologicalAlgebra.FinitePerturbation.core c.d0 c.h c.delta
    (c.i.comp c.p) (K c nilpotent) (J c nilpotent)
    c.d0_sq c.perturbed_sq c.contraction kl kr jl jr uk uj
  have kform : K c nilpotent = 1 - c.h * T := by
    linear_combination (norm := noncomm_ring) kr
  have jform : J c nilpotent = 1 - T * c.h := rfl
  have hdi (u : U) : c.d0 (c.i u) = 0 := DFunLike.congr_fun c.di u
  have hpd (v : V) : c.p (c.d0 v) = 0 := DFunLike.congr_fun c.pd v
  have hhi (u : U) : c.h (c.i u) = 0 := DFunLike.congr_fun c.hi u
  have hph (v : V) : c.p (c.h v) = 0 := DFunLike.congr_fun c.ph v
  have hhh (v : V) : c.h (c.h v) = 0 := DFunLike.congr_fun c.hh v
  have hpi (u : U) : c.p (c.i u) = u := DFunLike.congr_fun c.pi u
  have inc : c.D.comp (I c nilpotent) =
      (I c nilpotent).comp (transferred c nilpotent) := by
    ext u
    have eq := DFunLike.congr_fun dk (c.i u)
    simpa [Input.D, I, transferred, T, hdi] using eq
  have proj : (P c nilpotent).comp c.D =
      (transferred c nilpotent).comp (P c nilpotent) := by
    ext v
    have eq := congrArg c.p (DFunLike.congr_fun jd v)
    simpa [P, Input.D, transferred, I, T, hpd] using eq
  have sq : transferred c nilpotent * transferred c nilpotent = 0 := by
    ext u
    have eq := congrArg c.p (DFunLike.congr_fun tm (c.i u))
    simpa [transferred, I, T, hdi, hpd] using eq
  have ret : (P c nilpotent).comp (I c nilpotent) = LinearMap.id := by
    ext u
    simp [P, I, kform, jform, hhi, hph, hhh, hpi]
  have hk : c.h * K c nilpotent = c.h := by
    rw [kform]
    linear_combination (norm := noncomm_ring) - c.hh * T
  have jh : J c nilpotent * c.h = c.h := by
    rw [jform]
    linear_combination (norm := noncomm_ring) - T * c.hh
  refine ⟨sq, inc, proj, ret, ?_, ?_, ?_, ?_⟩
  · simpa only [Input.D, H, I, P, Module.End.mul_eq_comp, LinearMap.comp_assoc] using hom
  · change (K c nilpotent * c.h) * (K c nilpotent * c.h) = 0
    calc
      _ = K c nilpotent * (c.h * K c nilpotent) * c.h := by noncomm_ring
      _ = 0 := by rw [hk, mul_assoc, c.hh, mul_zero]
  · ext u
    change K c nilpotent (c.h (K c nilpotent (c.i u))) = 0
    have eq := DFunLike.congr_fun hk (c.i u)
    simpa [hhi] using congrArg (K c nilpotent) eq
  · ext v
    change c.p (J c nilpotent ((K c nilpotent * c.h) v)) = 0
    rw [pushh]
    have eq := DFunLike.congr_fun jh (J c nilpotent v)
    simpa [hph] using congrArg c.p eq

end Perturbation

end D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation
