/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/StandardCubicOfProjectedInversion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/StandardCubicOfProjectedInversion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Projected charge inversion gives a standard cubic in the actual acting group. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.DiagonalCharacterConjugacy
import D5.S3.VertexAlgebra.Lattice.Orbifold.NativeStandardThirdLift
import OmegaBuild.Commands

/-!
The leading charged product makes the multipliers of a lift multiplicative
on the fixed charges. A conjugate by a lift of negation supplies the inverse
multiplier there. The resulting word is compared with the native standard
lift on the actual lattice carrier.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction.StandardCubicOfProjectedInversion

open LatticeGeneratingFieldLocality LatticeAllStateField
open DiagonalCharacterConjugacy (PreservesModes ground diagonal conjugate_of_fixed_ground)
open NativeStandardThirdLift (standardLift standardLift_compatible standardLift_ground_single
  standardLift_cube)
open ThirdTwistedChargeAction (nativeStandardEta nativeStandardEta_fixed)
open scoped VertexOperator

open private ground_mul ground_ne_zero epsilon_ne_zero mode_smul from
  D5.S3.VertexAlgebra.Lattice.Orbifold.DiagonalCharacterConjugacy

/-- The explicit word in a lift of a cubic isometry and a lift of charge inversion
has exact order three and is standard on the actual fixed-charge ground lines. -/
theorem standard_cubic_of_projected_inversion
    (D : LatticeData) {G : Type*} [Group G]
    (U : G →* (Carrier D ≃ₗ[ℂ] Carrier D))
    (charge : G →* Multiplicative (AddAut (Charge D)))
    (phase : G → Charge D → ℂˣ) (hFaithful : Function.Injective U)
    (hMode : ∀ t, PreservesModes D (U t))
    (hGround : ∀ t a, U t (ground D a) =
      (phase t a : ℂ) • ground D ((charge t).toAdd a))
    (x s : G) (hx : orderOf (charge x) = 3)
    (hs : ∀ a, (charge s).toAdd a = -a)
    (hg : ∀ a b, bilinear D ((charge x).toAdd a) ((charge x).toAdd b) = bilinear D a b) :
    let z := (x * (s * x * s⁻¹)) ^ 2
    charge z = charge x ∧ orderOf z = 3 ∧
      ∀ a, (charge x).toAdd a = a → phase z a = 1 := by
  let y := s * x * s⁻¹
  let z := (x * y) ^ 2
  let g := (charge x).toAdd
  change charge z = charge x ∧ orderOf z = 3 ∧ ∀ a, g a = a → phase z a = 1
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨hxCube, hxNontrivial⟩ := orderOf_eq_prime_iff.mp hx
  have hCube (a : Charge D) : g (g (g a)) = a :=
    congrArg (fun q : Multiplicative (AddAut (Charge D)) => q.toAdd a) hxCube
  have hComm : charge s * charge x = charge x * charge s := by
    apply AddEquiv.ext
    intro a
    change (charge s).toAdd (g a) = g ((charge s).toAdd a)
    rw [hs, hs, map_neg]
  have hys : y * s = s * x := by simp [y, mul_assoc]
  have hChargeYS : charge y * charge s = charge s * charge x := by
    simpa only [map_mul] using congrArg charge hys
  have hy : charge y = charge x := mul_right_cancel (hChargeYS.trans hComm)
  have hz : charge z = charge x := by
    change charge ((x * y) ^ 2) = charge x
    rw [map_pow, map_mul, hy, ← pow_two, ← pow_mul, show 2 * 2 = 3 + 1 by decide,
      pow_succ, hxCube, one_mul]
  have hFixedAdd (b c : Charge D) (hb : g b = b) (hc : g c = c) :
      phase x (b + c) = phase x b * phase x c := by
    have hbc : g (b + c) = b + c := by rw [map_add, hb, hc]
    change (charge x).toAdd b = b at hb
    change (charge x).toAdd c = c at hc
    change (charge x).toAdd (b + c) = b + c at hbc
    have h := hMode x (ground D b) (ground D c) (-bilinear D b c - 1)
    rw [ground_mul, map_smul, hGround x (b + c), hbc, hGround x b, hGround x c,
      hb, hc, mode_smul, ground_mul, smul_smul, smul_smul] at h
    apply Units.ext
    change (phase x (b + c) : ℂ) = (phase x b : ℂ) * (phase x c : ℂ)
    apply mul_left_cancel₀ (epsilon_ne_zero D b c)
    exact (smul_left_injective ℂ (ground_ne_zero D (b + c)) h).trans (by ac_rfl)
  have hZero : phase x 0 = 1 := by
    have h := hFixedAdd 0 0 (map_zero g) (map_zero g)
    rw [zero_add] at h
    exact mul_left_cancel (by simpa only [mul_one] using h.symm :
      phase x 0 * phase x 0 = phase x 0 * 1)
  have hFixed (a : Charge D) (ha : g a = a) : phase z a = 1 := by
    change (charge x).toAdd a = a at ha
    have hNegFixed : (charge x).toAdd (-a) = -a := by rw [map_neg, ha]
    have hInverse := hFixedAdd a (-a) ha hNegFixed
    rw [add_neg_cancel, hZero] at hInverse
    have hSNeg : U s (ground D (-a)) = (phase s (-a) : ℂ) • ground D a := by
      rw [hGround, hs, neg_neg]
    have hXNeg : U x (ground D (-a)) = (phase x (-a) : ℂ) • ground D (-a) := by
      rw [hGround, hNegFixed]
    have hY : U y (ground D a) = (phase y a : ℂ) • ground D a := by
      rw [hGround, hy, ha]
    have hyPhase : phase y a = phase x (-a) := by
      have hEval := congrArg (fun t : G => U t (ground D (-a))) hys
      simp only [map_mul, LinearEquiv.mul_apply, hSNeg, hXNeg, hY, map_smul, smul_smul] at hEval
      apply Units.ext
      apply mul_left_cancel₀ (Units.ne_zero (phase s (-a)))
      exact (smul_left_injective ℂ (ground_ne_zero D a) hEval).trans (mul_comm _ _)
    have hProduct : U (x * y) (ground D a) = ground D a := by
      rw [map_mul, LinearEquiv.mul_apply, hY, map_smul, hGround x a, ha, smul_smul,
        hyPhase, ← Units.val_mul, mul_comm, ← hInverse, Units.val_one, one_smul]
    have hFixGround : U z (ground D a) = ground D a := by
      change U ((x * y) ^ 2) (ground D a) = ground D a
      rw [map_pow, pow_two, LinearEquiv.mul_apply, hProduct, hProduct]
    apply Units.ext
    rw [hGround, hz, ha] at hFixGround
    exact smul_left_injective ℂ (ground_ne_zero D a) (hFixGround.trans (one_smul ℂ _).symm)
  let native := standardLift D g hCube hg
  obtain ⟨χ, hConj⟩ := conjugate_of_fixed_ground D g (U z) native
    (phase z) (nativeStandardEta D g) (hMode z)
    (fun u v n => (standardLift_compatible D g hCube hg).2.1 u n v)
    (fun a => by rw [hGround, hz]) (standardLift_ground_single D g hCube hg)
    (fun a ha => (nativeStandardEta_fixed D g hg a ha).trans (hFixed a ha).symm)
  have hIntertwine (v : Carrier D) : diagonal D χ (U z v) = native (diagonal D χ v) :=
    congrArg (fun e : Carrier D ≃ₗ[ℂ] Carrier D => e v) hConj
  have hNativeCube : native ^ 3 = 1 := standardLift_cube D g hCube hg
  have hUCube : U z ^ 3 = 1 := by
    apply LinearEquiv.ext
    intro v
    apply (diagonal D χ).injective
    have h := congrArg (fun e : Carrier D ≃ₗ[ℂ] Carrier D => e (diagonal D χ v)) hNativeCube
    change diagonal D χ ((U z ^ 3) v) = diagonal D χ v
    change (native ^ 3) (diagonal D χ v) = diagonal D χ v at h
    simpa only [pow_succ, pow_zero, one_mul, LinearEquiv.mul_apply, hIntertwine] using h
  refine ⟨hz, orderOf_eq_prime_iff.mpr ⟨?_, ?_⟩, hFixed⟩
  · apply hFaithful
    rwa [map_pow, map_one]
  · intro h
    apply hxNontrivial
    rw [← hz, h, map_one]

#print axioms standard_cubic_of_projected_inversion

end D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction.StandardCubicOfProjectedInversion
