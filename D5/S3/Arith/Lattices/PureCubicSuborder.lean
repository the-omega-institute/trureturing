/- GID: D5/S3/Arith/Lattices/PureCubicSuborder
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/PureCubicSuborder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An integral cubic subring with an explicit multiplication table. -/

import D5.S3.Arith.Lattices.PureCubicIntegralLattices
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Lattices.PureCubicSuborder

open D5.S3.Arith.Lattices.PureCubicIntegralLattices
open Module

/-- The cubic relation makes the integral span of `1`, `theta`, and `beta`
closed under multiplication; the span is a rational basis of the field. -/
theorem pure_cubic_suborder
    {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    (pb : PowerBasis ℚ K) (h3 : pb.dim = 3) (a : ℤ)
    (hroot : pb.gen ^ 3 = ((1 + 9 * a : ℤ) : K)) :
    let theta : K := pb.gen
    let beta : K := (1 + theta + theta ^ 2) / 3
    theta ^ 2 = 3 * beta - theta - 1 ∧
    theta * beta = beta + 3 * (a : K) ∧
    beta ^ 2 = beta + (a : K) * theta + 2 * (a : K) ∧
    ∃ A : Subring K,
      (∀ x : K, x ∈ A ↔
        ∃ u v w : ℤ, x = (u : K) + (v : K) * theta + (w : K) * beta) ∧
      (∀ x ∈ A, IsIntegral ℤ x) ∧
      ∃ basis : Basis (Fin 3) ℚ K,
        (basis : Fin 3 → K) = ![(1 : K), theta, beta] := by
  let theta : K := pb.gen
  let beta : K := (1 + theta + theta ^ 2) / 3
  change theta ^ 2 = 3 * beta - theta - 1 ∧
    theta * beta = beta + 3 * (a : K) ∧
    beta ^ 2 = beta + (a : K) * theta + 2 * (a : K) ∧
    ∃ A : Subring K,
      (∀ x : K, x ∈ A ↔
        ∃ u v w : ℤ, x = (u : K) + (v : K) * theta + (w : K) * beta) ∧
      (∀ x ∈ A, IsIntegral ℤ x) ∧
      ∃ basis : Basis (Fin 3) ℚ K,
        (basis : Fin 3 → K) = ![(1 : K), theta, beta]
  have hcube : theta ^ 3 = 1 + 9 * (a : K) := by
    simpa [theta] using hroot
  have hsq : theta ^ 2 = 3 * beta - theta - 1 := by
    dsimp [beta]
    field_simp
    ring
  have htb : theta * beta = beta + 3 * (a : K) := by
    dsimp [beta]
    field_simp
    linear_combination hcube
  have hbb : beta ^ 2 = beta + (a : K) * theta + 2 * (a : K) := by
    dsimp [beta]
    field_simp
    linear_combination (theta + 2) * hcube
  have hmul (u v w u' v' w' : ℤ) :
      ((u : K) + (v : K) * theta + (w : K) * beta) *
          ((u' : K) + (v' : K) * theta + (w' : K) * beta) =
        ((u * u' - v * v' + 3 * a * (v * w' + w * v') + 2 * a * w * w' : ℤ) : K) +
          ((u * v' + v * u' - v * v' + a * w * w' : ℤ) : K) * theta +
          ((u * w' + w * u' + 3 * v * v' + v * w' + w * v' + w * w' : ℤ) : K) * beta := by
    push_cast
    calc
      ((u : K) + (v : K) * theta + (w : K) * beta) *
          ((u' : K) + (v' : K) * theta + (w' : K) * beta) =
        (u : K) * u' + ((u : K) * v' + (v : K) * u') * theta +
          ((u : K) * w' + (w : K) * u') * beta +
          ((v : K) * v') * theta ^ 2 +
          ((v : K) * w' + (w : K) * v') * (theta * beta) +
          ((w : K) * w') * beta ^ 2 := by ring
      _ = _ := by rw [hsq, htb, hbb]; ring
  let A : Subring K := {
    carrier := {x | ∃ u v w : ℤ,
      x = (u : K) + (v : K) * theta + (w : K) * beta}
    zero_mem' := by
      refine ⟨0, 0, 0, ?_⟩
      simp
    one_mem' := by
      refine ⟨1, 0, 0, ?_⟩
      simp
    add_mem' := by
      intro x y hx hy
      obtain ⟨u, v, w, rfl⟩ := hx
      obtain ⟨u', v', w', rfl⟩ := hy
      refine ⟨u + u', v + v', w + w', ?_⟩
      push_cast
      ring
    neg_mem' := by
      intro x hx
      obtain ⟨u, v, w, rfl⟩ := hx
      refine ⟨-u, -v, -w, ?_⟩
      push_cast
      ring
    mul_mem' := by
      intro x y hx hy
      obtain ⟨u, v, w, rfl⟩ := hx
      obtain ⟨u', v', w', rfl⟩ := hy
      refine ⟨u * u' - v * v' + 3 * a * (v * w' + w * v') + 2 * a * w * w',
        u * v' + v * u' - v * v' + a * w * w',
        u * w' + w * u' + 3 * v * v' + v * w' + w * v' + w * w', ?_⟩
      exact hmul u v w u' v' w'
  }
  have hm : (1 + 9 * a : ℤ) ≠ 0 := by omega
  have hsource := integral_cubic_lattices pb h3
    (1 + 9 * a) 1 1 a 0 1 hm (by norm_num) (Or.inl rfl)
    (by simpa using hroot) (by ring) (by ring)
  have htheta : IsIntegral ℤ theta := by simpa [theta] using hsource.1
  have hbeta : IsIntegral ℤ beta := by
    simpa [beta, theta] using hsource.2.2.1
  refine ⟨hsq, htb, hbb, A, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x hx
    obtain ⟨u, v, w, rfl⟩ := hx
    have hu : IsIntegral ℤ (u : K) := isIntegral_algebraMap
    have hv : IsIntegral ℤ (v : K) := isIntegral_algebraMap
    have hw : IsIntegral ℤ (w : K) := isIntegral_algebraMap
    exact (hu.add (hv.mul htheta)).add (hw.mul hbeta)
  · obtain ⟨_, basis, _, hb, _, _⟩ := hsource.2.2.2
    exact ⟨basis, by simpa [beta, theta] using hb⟩

#print axioms pure_cubic_suborder

end D5.S3.Arith.Lattices.PureCubicSuborder
