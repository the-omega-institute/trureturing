/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteJetCoordinates
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteJetCoordinates
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteTraceChart]
   utility: none
   digest: Tangential and normal observation polynomials on the five-site trace chart. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteTraceChart
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-! An auxiliary positive gain restores the raw density as a polynomial map
of nine real coordinates. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteJetCoordinates

open PeriodicMPSFiveSiteCoordinates PeriodicMPSFiveSiteTraceChart

/-- The Gaussian quadratic algebra allows the same formula over the reals,
the rationals, polynomial rings, and the small algebras used to compute jets. -/
abbrev Gaussian (R : Type*) [CommRing R] := QuadraticAlgebra R (-1) 0

private def amplitude {R : Type*} [CommRing R] (u : Fin 9 → R) : Fin 8 → Gaussian R :=
  chart ⟨u 6, u 7⟩ ⟨u 0, u 1⟩ ⟨u 2, u 3⟩ 1 ⟨u 4, u 5⟩

private def entry {R : Type*} [CommRing R] (u : Fin 9 → R) (i j : Fin 4) : Gaussian R :=
  let A := flatten (amplitude u)
  ⟨u 8, 0⟩ * ∑ k : Fin 8, A i k * star (A j k)

/-- The nine tangential coordinates followed by the corner probability.
Coordinates zero through seven parametrize the trace chart and coordinate eight
is the raw gain. -/
def raw {R : Type*} [CommRing R] (u : Fin 9 → R) : Fin 10 → R :=
  ![(entry u 0 0).re, (entry u 0 1).re, (entry u 0 1).im,
    (entry u 0 3).re, (entry u 0 3).im, (entry u 1 1).re,
    (entry u 1 2).re, (entry u 1 3).re, (entry u 1 3).im, (entry u 3 3).re]

/-- The Jacobian of the raw output, computed with dual numbers. -/
def rawJacobian (u : Fin 9 → ℚ) : Matrix (Fin 10) (Fin 9) ℚ :=
  fun i j => (raw (R := DualNumber ℚ)
    (fun k => ⟨u k, if k = j then 1 else 0⟩) i).snd

/-- The first nine rows of the raw Jacobian. -/
def tangentJacobian (u : Fin 9 → ℚ) : Matrix (Fin 9) (Fin 9) ℚ :=
  (rawJacobian u).submatrix Fin.castSucc id

private abbrev D₁ := DualNumber ℚ
private abbrev D₂ := DualNumber D₁
private abbrev D₃ := DualNumber D₂

private local instance : CommRing D₁ := TrivSqZeroExt.commRing
private local instance : CommRing D₂ := TrivSqZeroExt.commRing
private local instance : CommRing D₃ := TrivSqZeroExt.commRing

private def constant (q : ℚ) : D₃ :=
  ⟨⟨⟨q, 0⟩, 0⟩, 0⟩

private def parameter : D₃ :=
  ⟨⟨⟨0, 1⟩, 1⟩, 1⟩

set_option maxRecDepth 32768 in
private noncomputable def jet (u v w : Fin 9 → ℚ) (i : Fin 10) : D₃ :=
  raw (R := D₃) (fun k =>
    constant (u k) + constant (v k) * parameter + constant (w k) * parameter ^ (2 : ℕ)) i

/-- The quadratic coefficient along a second-order source path. -/
noncomputable def quadraticCoefficient (u v w : Fin 9 → ℚ) (i : Fin 10) : ℚ :=
  (jet u v w i).fst.snd.snd / 2

/-- The cubic coefficient along a second-order source path. -/
noncomputable def cubicCoefficient (u v w : Fin 9 → ℚ) (i : Fin 10) : ℚ :=
  (jet u v w i).snd.snd.snd / 6

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteJetCoordinates
