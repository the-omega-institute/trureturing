/- GID: D5/S3/Arith/Lattices/PureCubicIntegerCoordinateEquiv
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/PureCubicIntegerCoordinateEquiv
   mirror-E: none(waiver:algebraically-proved)
   anchors: [D5/S3/Arith/Lattices/PureCubicOrderFieldCoordinates,
     D5/S3/Arith/Lattices/PureCubicIntegralLattices]
   utility: none
   digest: Integral coordinates give an additive equivalence with the cubic integer ring. -/

import D5.S3.Arith.Lattices.PureCubicOrderFieldCoordinates
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Lattices.PureCubicIntegerCoordinateEquiv

open Module
open scoped NumberField

theorem pure_cubic_integer_coordinate_equiv
    {K : Type*} [Field K] [NumberField K]
    (pb : PowerBasis ℚ K) (h3 : pb.dim = 3)
    (m n c a k v : ℤ) (hmpos : 0 < m) (hnpos : 0 < n) (hcpos : 0 < c)
    (hmsq : Squarefree m) (hnsq : Squarefree n) (hcop : IsCoprime m n)
    (hv : v = 1 ∨ v = -1)
    (hroot : pb.gen ^ 3 = ((m * n ^ 2 : ℤ) : K))
    (hcubic : c ^ 3 * m * n ^ 2 = 1 + 9 * a)
    (hcv : c ^ 2 * n = v + 3 * k) :
    ∃ e : (ℤ × ℤ × ℤ) ≃+ 𝓞 K,
      ∀ x : ℤ × ℤ × ℤ,
        ((e x : 𝓞 K) : K) =
          (x.1 : K) + (x.2.1 : K) * pb.gen +
            (x.2.2 : K) *
              ((1 + (c : K) * pb.gen + (v : K) * (pb.gen ^ 2 / (n : K))) / 3) := by
  let gamma : K :=
    (1 + (c : K) * pb.gen + (v : K) * (pb.gen ^ 2 / (n : K))) / 3
  have hfield :=
    D5.S3.Arith.Lattices.PureCubicOrderFieldCoordinates.pure_cubic_order_field_coordinates
      pb h3 m n c a k v hmpos hnpos hcpos hmsq hnsq hcop hv hroot hcubic hcv
  have hchar (z : K) : IsIntegral ℤ z ↔
      ∃ u r s : ℤ, z = (u : K) + (r : K) * pb.gen + (s : K) * gamma := by
    simpa [gamma] using hfield.1 z
  have hbsource :=
    D5.S3.Arith.Lattices.PureCubicIntegralLattices.integral_cubic_lattices
      pb h3 m n c a k v (ne_of_gt hmpos) (ne_of_gt hnpos)
      hv hroot hcubic hcv
  obtain ⟨_, b, _, hb, _, _⟩ := hbsource.2.2.2
  have hb0 : b 0 = (1 : K) := by simpa using congrFun hb 0
  have hb1 : b 1 = pb.gen := by simpa using congrFun hb 1
  have hb2 : b 2 = gamma := by simpa [gamma] using congrFun hb 2
  have huniq (u r s u' r' s' : ℤ)
      (heq : (u : K) + (r : K) * pb.gen + (s : K) * gamma =
        (u' : K) + (r' : K) * pb.gen + (s' : K) * gamma) :
      u = u' ∧ r = r' ∧ s = s' := by
    have heq' : (u : ℚ) • b 0 + (r : ℚ) • b 1 + (s : ℚ) • b 2 =
        (u' : ℚ) • b 0 + (r' : ℚ) • b 1 + (s' : ℚ) • b 2 := by
      simpa [hb0, hb1, hb2, Algebra.smul_def] using heq
    have heqrepr := congrArg b.repr heq'
    have hu := congrArg (fun f : Fin 3 →₀ ℚ => f 0) heqrepr
    have hr := congrArg (fun f : Fin 3 →₀ ℚ => f 1) heqrepr
    have hs := congrArg (fun f : Fin 3 →₀ ℚ => f 2) heqrepr
    simp [map_add, map_smul, Basis.repr_self] at hu hr hs
    exact ⟨by exact_mod_cast hu, by exact_mod_cast hr, by exact_mod_cast hs⟩
  let phi : (ℤ × ℤ × ℤ) → 𝓞 K := fun x =>
      ⟨(x.1 : K) + (x.2.1 : K) * pb.gen + (x.2.2 : K) * gamma,
        (hchar _).mpr ⟨x.1, x.2.1, x.2.2, rfl⟩⟩
  let f : (ℤ × ℤ × ℤ) →+ 𝓞 K := {
    toFun := phi
    map_zero' := by
      apply NumberField.RingOfIntegers.ext
      change (phi 0 : K) = ((0 : 𝓞 K) : K)
      simp [phi, NumberField.RingOfIntegers.coe_eq_algebraMap]
      exact map_zero (algebraMap (𝓞 K) K)
    map_add' := by
      intro x y
      apply NumberField.RingOfIntegers.ext
      change (phi (x + y) : K) = ((phi x + phi y : 𝓞 K) : K)
      have hcoe (p q : 𝓞 K) : ((p + q : 𝓞 K) : K) = (p : K) + (q : K) :=
        map_add (algebraMap (𝓞 K) K) p q
      rw [hcoe]
      change ((x.1 + y.1 : ℤ) : K) + ((x.2.1 + y.2.1 : ℤ) : K) * pb.gen +
          ((x.2.2 + y.2.2 : ℤ) : K) * gamma =
        ((x.1 : K) + (x.2.1 : K) * pb.gen + (x.2.2 : K) * gamma) +
          ((y.1 : K) + (y.2.1 : K) * pb.gen + (y.2.2 : K) * gamma)
      push_cast
      ring
  }
  have hval (x : ℤ × ℤ × ℤ) : (f x : K) =
      (x.1 : K) + (x.2.1 : K) * pb.gen + (x.2.2 : K) * gamma := by
    rfl
  have hinj : Function.Injective f := by
    intro x y h
    have heq := congrArg (fun z : 𝓞 K => (z : K)) h
    rw [hval x, hval y] at heq
    obtain ⟨hu, hr, hs⟩ := huniq x.1 x.2.1 x.2.2
      y.1 y.2.1 y.2.2 heq
    exact Prod.ext hu (Prod.ext hr hs)
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨u, r, s, hz⟩ :=
      (hchar (z : K)).mp (NumberField.RingOfIntegers.isIntegral_coe z)
    refine ⟨(u, r, s), ?_⟩
    apply NumberField.RingOfIntegers.ext
    rw [hval]
    exact hz.symm
  refine ⟨AddEquiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  intro x
  rfl

#print axioms pure_cubic_integer_coordinate_equiv

end D5.S3.Arith.Lattices.PureCubicIntegerCoordinateEquiv
