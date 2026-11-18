/- GID: D5/S0/Certificates/Algebra/BergmanContractedAlgebra
   generality: G
   mirror-B: D5/B/S0/Certificates/Algebra/BergmanContractedAlgebra
   mirror-E: none(waiver:noncomputational)
   anchors: [mathlib/module/Mathlib.Algebra.Algebra.NonUnitalHom]
   utility: none
   digest: Contracted semigroup multiplication is associative and functorial without commutativity. -/

import D5.S0.Certificates.Algebra.BergmanQuestion15Refutation
import Mathlib.Algebra.Algebra.NonUnitalHom

/-! # Associative contracted algebras and induced maps -/

namespace D5.S0.Certificates.Algebra.BergmanContractedAlgebra

open BergmanQuestion15Refutation

universe u v w

section Basis
variable {F : Type v} {S : Type u} [Field F] [Zero S] [Mul S]

/-- The product of two scalar basis vectors uses the original contracted multiplication. -/
theorem single_mul (a b : {s : S // s ≠ 0}) (r t : F) :
    (Finsupp.single a r : Contracted F S) * Finsupp.single b t =
      (r * t) • delta F S (a.val * b.val) := by
  classical
  simp [HMul.hMul, Mul.mul, product, Finsupp.llift, Finsupp.lift_apply, smul_smul]

/-- Scalar multiplication commutes with multiplication by an algebra element. -/
noncomputable instance contractedSMulCommClass :
    SMulCommClass F (Contracted F S) (Contracted F S) where
  smul_comm r a b := by
    exact ((product F S a).map_smul r b).symm

/-- Scalars can pass between the two inputs of the contracted product. -/
noncomputable instance contractedScalarTower : IsScalarTower F (Contracted F S) (Contracted F S) where
  smul_assoc r a b := by
    change product F S (r • a) b = r • (product F S a b)
    rw [map_smul, LinearMap.smul_apply]

end Basis

section Associativity
variable {F : Type v} {S : Type u} [Field F] [SemigroupWithZero S]

/-- Basis images preserve semigroup multiplication, including products equal to zero. -/
theorem delta_mul (a b : S) :
    delta F S a * delta F S b = delta F S (a * b) := by
  classical
  by_cases ha : a = 0
  · simp [ha, delta]
  by_cases hb : b = 0
  · simp [hb, delta]
  simp only [delta, dif_neg ha, dif_neg hb, single_mul, one_mul, one_smul]

/-- Associativity needs no commutativity of the underlying semigroup. -/
noncomputable instance contractedRing : NonUnitalRing (Contracted F S) where
  mul_assoc f g h := by
    classical
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [add_mul, hf, hg]
    | single a r =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => simp only [mul_add, add_mul, hf, hg]
      | single b t =>
        induction h using Finsupp.induction_linear with
        | zero => simp
        | add f g hf hg => simp only [mul_add, hf, hg]
        | single c q =>
          rw [single_mul, single_mul]
          have da : (Finsupp.single a r : Contracted F S) = r • delta F S a.val := by
            simp [delta, a.property, Finsupp.smul_single]
          have dc : (Finsupp.single c q : Contracted F S) = q • delta F S c.val := by
            simp [delta, c.property, Finsupp.smul_single]
          rw [da, dc, smul_mul_assoc, mul_smul_comm, mul_smul_comm, smul_mul_assoc,
            delta_mul, delta_mul, smul_smul, smul_smul]
          simp only [mul_assoc, mul_left_comm, mul_comm]

end Associativity

section Maps
variable {F : Type v} {S : Type u} {T : Type w}
variable [Field F] [SemigroupWithZero S] [SemigroupWithZero T]

/-- Extend a zero-preserving semigroup map to the original contracted vector spaces. -/
noncomputable def map (f : S → T) : Contracted F S →ₗ[F] Contracted F T :=
  Finsupp.llift (S := F) (M := Contracted F T) (R := F)
    (X := {s : S // s ≠ 0}) (fun s => delta F T (f s.val))

private theorem map_single (f : S → T) (a : {s : S // s ≠ 0}) (r : F) :
    map (F := F) f (Finsupp.single a r) = r • delta F T (f a.val) := by
  classical
  simp [map, Finsupp.llift, Finsupp.lift_apply]

/-- A semigroup zero contributes no basis vector to the induced linear map. -/
theorem map_delta (f : S → T) (hzero : f 0 = 0) (s : S) :
    map (F := F) f (delta F S s) = delta F T (f s) := by
  classical
  by_cases hs : s = 0
  · simp [hs, hzero, delta]
  · simp only [delta, dif_neg hs, map_single, one_smul]

/-- The induced linear map preserves multiplication even when nonzero elements collapse to zero. -/
theorem map_mul (f : S → T) (hzero : f 0 = 0)
    (hmul : ∀ a b, f (a * b) = f a * f b) (a b : Contracted F S) :
    map (F := F) f (a * b) = map (F := F) f a * map (F := F) f b := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [add_mul, map_add, ha, hb]
  | single a r =>
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [mul_add, map_add, ha, hb]
    | single b t =>
      rw [single_mul, map_smul, map_delta f hzero, map_single, map_single,
        smul_mul_assoc, mul_smul_comm, delta_mul, smul_smul, hmul]

/-- A zero-preserving multiplicative map induces a homomorphism of nonunital algebras. -/
noncomputable def mapHom (f : S → T) (hzero : f 0 = 0)
    (hmul : ∀ a b, f (a * b) = f a * f b) :
    Contracted F S →ₙₐ[F] Contracted F T where
  toFun := map (F := F) f
  map_zero' := (map (F := F) f).map_zero
  map_add' := (map (F := F) f).map_add
  map_smul' := (map (F := F) f).map_smul
  map_mul' := map_mul f hzero hmul

end Maps

end D5.S0.Certificates.Algebra.BergmanContractedAlgebra
