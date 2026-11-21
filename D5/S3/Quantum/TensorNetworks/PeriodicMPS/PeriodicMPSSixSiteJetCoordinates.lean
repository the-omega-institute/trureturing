/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteJetCoordinates
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteJetCoordinates
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMarginal]
   utility: none
   digest: Raw six-site observation and its jets in the normalized affine trace chart. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMarginal
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.QuadraticAlgebra.Basic

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteJetCoordinates

open PeriodicMPSSixSiteCoordinates PeriodicMPSSixSiteMarginal

/-- The Gaussian coefficient algebra over the scalar ring. -/
abbrev Gaussian (R : Type*) [CommRing R] := QuadraticAlgebra R (-1) 0

/-- The chart uses complex inputs `(x, y, h, z)` in adjacent real-imaginary
pairs and the normalized trace tuple `(x, x*h, x*h^2, y, z, 1)`. -/
private def amplitude {R : Type*} [CommRing R] (u : Fin 9 → R) : Fin 14 → Gaussian R :=
  let x : Gaussian R := ⟨u 0, u 1⟩
  let y : Gaussian R := ⟨u 2, u 3⟩
  let h : Gaussian R := ⟨u 4, u 5⟩
  let z : Gaussian R := ⟨u 6, u 7⟩
  coordinates x (x * h) (x * h ^ 2) y z 1

private def entry {R : Type*} [CommRing R] (gain : R) (p : Fin 14 → Gaussian R)
    (i j : Fin 4) : Gaussian R :=
  let A := flatten p
  ⟨gain, 0⟩ * ∑ k : Fin 16, A i k * star (A j k)

private def readout {R : Type*} [CommRing R] (gain : R) (p : Fin 14 → Gaussian R) : Fin 10 → R :=
  let G := entry gain p
  ![(G 0 0).re, (G 0 1).re, (G 0 1).im, (G 0 3).re, (G 0 3).im,
    (G 1 1).re, (G 1 2).re, (G 1 3).re, (G 1 3).im, (G 3 3).re]

/-- The first nine entries are tangential and the last entry is the corner
probability. Input eight is the raw gain. Output three is `Re G₀₃`. -/
def raw {R : Type*} [CommRing R] (u : Fin 9 → R) : Fin 10 → R :=
  readout (u 8) (amplitude u)

/-- The Jacobian of the ten real outputs, evaluated by first-order dual numbers. -/
def rawJacobian (u : Fin 9 → ℚ) : Matrix (Fin 10) (Fin 9) ℚ :=
  fun i j => (raw (R := DualNumber ℚ)
    (fun k => ⟨u k, if k = j then 1 else 0⟩) i).snd

/-- The Jacobian of the first nine outputs. -/
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

private noncomputable def pathInput (u v w : Fin 9 → ℚ) (k : Fin 9) : D₃ :=
  constant (u k) + constant (v k) * parameter + constant (w k) * parameter ^ (2 : ℕ)

set_option maxRecDepth 32768 in
private noncomputable def jet (u v w : Fin 9 → ℚ) (i : Fin 10) : D₃ :=
  raw (R := D₃) (pathInput u v w) i

/-- The quadratic coefficient for the source path `u + ε v + ε² w`. -/
noncomputable def quadraticCoefficient (u v w : Fin 9 → ℚ) (i : Fin 10) : ℚ :=
  (jet u v w i).fst.snd.snd / 2

/-- The cubic coefficient for the source path `u + ε v + ε² w`. -/
noncomputable def cubicCoefficient (u v w : Fin 9 → ℚ) (i : Fin 10) : ℚ :=
  (jet u v w i).snd.snd.snd / 6

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteJetCoordinates
