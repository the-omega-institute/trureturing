/- GID: D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Matrix.Basis]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.claim; result=D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.result; claim=D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.claim
   digest: Two opposite matrix units refute nilpotent adjacency in the annihilator digraph. -/

import OmegaBuild.Commands
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.ZMod.Defs
import D5.S0.Certificates.Algebra.BergmanQuestion15Refutation

/-! A counterexample to nilpotent adjacency in arXiv:2608.09243v2, Section 7. -/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S0.Certificates.Algebra.MekeraNilpotentAdjacencyRefutation

open BergmanQuestion15Refutation (positivePower)

universe u

/-- A vertex of the annihilator digraph is a nonzero left or right zero divisor. -/
def vertex {R : Type u} [Mul R] [Zero R] (x : R) : Prop :=
  x ≠ 0 ∧ ∃ t : R, t ≠ 0 ∧ (x * t = 0 ∨ t * x = 0)

/-- Definition 4.1, with the left and right annihilator differences expanded. -/
def arc {R : Type u} [Mul R] [Zero R] (x y : R) : Prop :=
  vertex x ∧ vertex y ∧ x ≠ y ∧
    ((∃ t : R, t * (x * y) = 0 ∧ t * x ≠ 0 ∧ t * y ≠ 0) ∨
      (∃ t : R, (x * y) * t = 0 ∧ x * t ≠ 0 ∧ y * t ≠ 0))

/-- The index k represents exponent k + 1. -/
def nilpotent {R : Type u} [Mul R] [Zero R] (x : R) : Prop :=
  ∃ k : ℕ, positivePower x k = 0

private def claimAt : Prop :=
  ∀ (R : Type u) [NonUnitalRing R],
    (¬ (∀ r s : R, r * s = s * r)) →
    ∀ x y : R, x ≠ y → x ≠ 0 → y ≠ 0 →
      nilpotent x → nilpotent y → arc x y ∨ arc y x

/-- The Section 7 assertion with carriers in Type 0. -/
def claim : Prop := claimAt.{0}

private abbrev Coeff := ULift.{u} (ZMod 2)
private abbrev Mat := Matrix (Fin 2) (Fin 2) Coeff.{u}

private def matrixUnit (i j : Fin 2) : Mat.{u} :=
  Matrix.single i j (1 : Coeff.{u})

private theorem refuteAt : ¬ claimAt.{u} := by
  intro hClaim
  unfold claimAt at hClaim
  let A : Mat.{u} := matrixUnit.{u} 0 1
  let B : Mat.{u} := matrixUnit.{u} 1 0

  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := Ne.symm h01
  have hScalar : (1 : Coeff.{u}) ≠ 0 := by
    intro h
    have hBase : (1 : ZMod 2) = 0 :=
      congrArg (fun value : Coeff.{u} => value.down) h
    exact (show (1 : ZMod 2) ≠ 0 by decide) hBase

  have onEntry (i j : Fin 2) : matrixUnit.{u} i j i j = (1 : Coeff.{u}) :=
    Matrix.single_apply_same i j (1 : Coeff.{u})
  have offRow {i i' : Fin 2} (h : i ≠ i') (j j' : Fin 2) :
      matrixUnit.{u} i j i' j' = 0 :=
    Matrix.single_apply_of_row_ne h j j' (1 : Coeff.{u})

  have hA : A ≠ 0 := by
    intro h
    apply hScalar
    calc
      1 = A 0 1 := (onEntry 0 1).symm
      _ = 0 := congrArg (fun M : Mat.{u} => M 0 1) h
  have hB : B ≠ 0 := by
    intro h
    apply hScalar
    calc
      1 = B 1 0 := (onEntry 1 0).symm
      _ = 0 := congrArg (fun M : Mat.{u} => M 1 0) h
  have hDistinct : A ≠ B := by
    intro h
    apply hScalar
    calc
      1 = A 0 1 := (onEntry 0 1).symm
      _ = B 0 1 := congrArg (fun M : Mat.{u} => M 0 1) h
      _ = 0 := offRow h10 0 1

  have unitMul (i j k : Fin 2) :
      matrixUnit.{u} i j * matrixUnit.{u} j k = matrixUnit.{u} i k := by
    simpa only [matrixUnit, one_mul] using
      (Matrix.single_mul_single_same (1 : Coeff.{u}) i j k (1 : Coeff.{u}))
  have hAA : A * A = 0 := by
    change Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : Coeff.{u}) *
      Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : Coeff.{u}) = 0
    exact Matrix.single_mul_single_of_ne (1 : Coeff.{u}) (0 : Fin 2) 1 0 h10 1
  have hBB : B * B = 0 := by
    change Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : Coeff.{u}) *
      Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : Coeff.{u}) = 0
    exact Matrix.single_mul_single_of_ne (1 : Coeff.{u}) (1 : Fin 2) 0 1 h01 1
  have hAB : A * B = matrixUnit.{u} 0 0 := unitMul 0 1 0
  have hBA : B * A = matrixUnit.{u} 1 1 := unitMul 1 0 1
  have hNoncommutative : ¬ (∀ x y : Mat.{u}, x * y = y * x) := by
    intro hComm
    have hDiag : matrixUnit.{u} 0 0 = matrixUnit.{u} 1 1 :=
      hAB.symm.trans ((hComm A B).trans hBA)
    apply hScalar
    calc
      1 = matrixUnit.{u} 0 0 0 0 := (onEntry 0 0).symm
      _ = matrixUnit.{u} 1 1 0 0 := congrArg (fun M : Mat.{u} => M 0 0) hDiag
      _ = 0 := offRow h10 1 0

  have hVertexA : vertex A := ⟨hA, A, hA, Or.inl hAA⟩
  have hVertexB : vertex B := ⟨hB, B, hB, Or.inl hBB⟩
  have hNilA : nilpotent A := ⟨1, hAA⟩
  have hNilB : nilpotent B := ⟨1, hBB⟩

  have hAB_mul_A : (A * B) * A = A := by
    rw [hAB]
    exact unitMul 0 0 1
  have hB_mul_AB : B * (A * B) = B := by
    rw [hAB]
    exact unitMul 1 0 0
  have hBA_mul_B : (B * A) * B = B := by
    rw [hBA]
    exact unitMul 1 1 0
  have hA_mul_BA : A * (B * A) = A := by
    rw [hBA]
    exact unitMul 0 1 1

  have hNoAB : ¬ arc A B := by
    intro hArc
    unfold arc at hArc
    rcases hArc.2.2.2 with ⟨t, ht, htA, _⟩ | ⟨t, ht, _, hBt⟩
    · apply htA
      calc
        t * A = t * ((A * B) * A) := congrArg (fun M : Mat.{u} => t * M) hAB_mul_A.symm
        _ = (t * (A * B)) * A := (mul_assoc t (A * B) A).symm
        _ = 0 := by rw [ht, zero_mul]
    · apply hBt
      calc
        B * t = (B * (A * B)) * t := congrArg (fun M : Mat.{u} => M * t) hB_mul_AB.symm
        _ = B * ((A * B) * t) := mul_assoc B (A * B) t
        _ = 0 := by rw [ht, mul_zero]

  have hNoBA : ¬ arc B A := by
    intro hArc
    unfold arc at hArc
    rcases hArc.2.2.2 with ⟨t, ht, htB, _⟩ | ⟨t, ht, _, hAt⟩
    · apply htB
      calc
        t * B = t * ((B * A) * B) := congrArg (fun M : Mat.{u} => t * M) hBA_mul_B.symm
        _ = (t * (B * A)) * B := (mul_assoc t (B * A) B).symm
        _ = 0 := by rw [ht, zero_mul]
    · apply hAt
      calc
        A * t = (A * (B * A)) * t := congrArg (fun M : Mat.{u} => M * t) hA_mul_BA.symm
        _ = A * ((B * A) * t) := mul_assoc A (B * A) t
        _ = 0 := by rw [ht, mul_zero]

  have hAdjacent : arc A B ∨ arc B A :=
    hClaim Mat.{u} hNoncommutative A B hDistinct hVertexA.1 hVertexB.1 hNilA hNilB
  exact hAdjacent.elim hNoAB hNoBA

/-- The two opposite units in the binary matrix ring have no arc in either direction. -/
theorem result : ¬ claim := refuteAt.{0}

end D5.S0.Certificates.Algebra.MekeraNilpotentAdjacencyRefutation
