/- GID: D5/S3/Quantum/Measurements/GTestThresholdPrior
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/GTestThresholdPrior
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The G-test threshold prior is its orbit count divided by word count plus orbit count. -/

import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The position action uses inverse permutations. The fixed-unitary twirl has the same tested
probability as the Haar mixture after unitary independence is proved. Burnside is applied to
fixed points after double-counting the stabilizer sum. No optimality over all tests is asserted.
-/

namespace D5.S3.Quantum.Measurements.GTestThresholdPrior

noncomputable section

open scoped BigOperators Matrix

attribute [local instance] Classical.propDecidable

abbrev Word (n d : ℕ) :=
  Fin n → Fin d

abbrev TensorVec (n d : ℕ) :=
  Word n d → ℂ

abbrev TensorMat (n d : ℕ) :=
  Matrix (Word n d) (Word n d) ℂ

local instance wordAction (n d : ℕ) :
    MulAction (Equiv.Perm (Fin n)) (Word n d) :=
  arrowAction

abbrev WordOrbit {n d : ℕ} (w : Word n d) :=
  ↥(MulAction.orbit (Equiv.Perm (Fin n)) w)

def orbitMap {n d : ℕ} (w : Word n d)
    (π : Equiv.Perm (Fin n)) : WordOrbit w :=
  ⟨π • w, MulAction.mem_orbit w π⟩

def M {n d : ℕ} (w : Word n d) : ℕ :=
  Fintype.card (WordOrbit w)

def O {n d : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n)))
    (w : Word n d) : ℕ :=
  Fintype.card
    (MulAction.orbitRel.Quotient G (WordOrbit w))

def psi {n d : ℕ} :
    Equiv.Perm (Fin n) →* TensorMat n d :=
  (Matrix.permMatrixHom (n := Word n d) (R := ℂ)).comp
    (MulAction.toPermHom
      (Equiv.Perm (Fin n)) (Word n d))

def ket {n d : ℕ} (w : Word n d) : TensorVec n d :=
  fun x => if x = w then 1 else 0

def pure {ι : Type*} (v : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.vecMulVec v (star v)

def tensorPower (n : ℕ) {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) : TensorMat n d :=
  Matrix.of (fun x y => ∏ j : Fin n, A (x j) (y j))

def repeatKet (n : ℕ) {d : ℕ}
    (φ : Fin d → ℂ) : TensorVec n d :=
  fun x => ∏ j : Fin n, φ (x j)

def equalState (n : ℕ) {d : ℕ}
    (φ : Fin d → ℂ) : TensorMat n d :=
  pure (repeatKet n φ)

def UnitVector {d : ℕ} (φ : Fin d → ℂ) : Prop :=
  (∑ i : Fin d, star (φ i) * φ i) = (1 : ℂ)

def PiG {n d : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n))) : TensorMat n d :=
  (Fintype.card G : ℂ)⁻¹ •
    ∑ g : G, psi (d := d) (g : Equiv.Perm (Fin n))

def rhoTilde {n d : ℕ}
    (w : Word n d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : TensorMat n d :=
  let T := tensorPower n (U : Matrix (Fin d) (Fin d) ℂ)
  (n.factorial : ℂ)⁻¹ •
    ∑ π : Equiv.Perm (Fin n),
      psi (d := d) π *
        (T * pure (ket w) * T.conjTranspose) *
        psi (d := d) (π⁻¹)

def completeness {n d : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n)))
    (φ : Fin d → ℂ) : ℝ :=
  (Matrix.trace (PiG G * equalState n φ)).re

def soundnessError {n d : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n)))
    (w : Word n d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : ℝ :=
  (Matrix.trace (PiG G * rhoTilde w U)).re

def soundness {n d : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n)))
    (w : Word n d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : ℝ :=
  1 - soundnessError G w U

def P_G {n d : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n)))
    (w : Word n d)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (φ : Fin d → ℂ) (p : ℝ) : ℝ :=
  p * completeness G φ + (1 - p) * soundness G w U

def P_T (p : ℝ) : ℝ :=
  1 - p

def claim : Prop :=
  ∀ (n d : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (w : Word n d)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (φ : Fin d → ℂ)
    (p : ℝ),
    (∃ i j : Fin n, w i ≠ w j) →
    UnitVector φ →
    p ∈ Set.Icc (0 : ℝ) 1 →
    (((P_G G w U φ p > P_T p) ↔
        p > (O G w : ℝ) / ((M w : ℝ) + (O G w : ℝ))) ∧
     ((P_G G w U φ p = P_T p) ↔
        p = (O G w : ℝ) / ((M w : ℝ) + (O G w : ℝ)))) ∧
    Matrix.trace (PiG G * rhoTilde w U) =
      (O G w : ℂ) / (M w : ℂ)

end

end D5.S3.Quantum.Measurements.GTestThresholdPrior
