import D5.S3.Arith.Lattices.PureCubicIntegralLattices
import Reg.Support.DependentFamily
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Field.ULift

open _root_.D5.S3.Arith.Lattices.PureCubicIntegralLattices
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial Module

namespace Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices
universe u

noncomputable section

abbrev signature : Signature where
  Params := ℤ
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ m n => -3 * ((m * n : ℤ) : ℚ) ^ 2) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ m n => -3 * ((m * n : ℤ) : ℚ) ^ 2 + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {K : Type u} [Field K] [CharZero K] [Algebra ℚ K]
    (pb : PowerBasis ℚ K) (h3 : pb.dim = 3)
    (m n c a k v : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hv : v = 1 ∨ v = -1)
    (hroot : pb.gen ^ 3 = ((m * n ^ 2 : ℤ) : K))
    (hcubic : c ^ 3 * m * n ^ 2 = 1 + 9 * a)
    (hcv : c ^ 2 * n = v + 3 * k),
    IsIntegral ℤ pb.gen ∧
    IsIntegral ℤ (pb.gen ^ 2 / (n : K)) ∧
    IsIntegral ℤ
      ((1 + (c : K) * pb.gen +
        (v : K) * (pb.gen ^ 2 / (n : K))) / 3) ∧
    ∃ b1 b2 : Basis (Fin 3) ℚ K,
      (b1 : Fin 3 → K) = ![(1 : K), pb.gen, pb.gen ^ 2 / (n : K)] ∧
      (b2 : Fin 3 → K) =
        ![(1 : K), pb.gen,
          (1 + (c : K) * pb.gen +
            (v : K) * (pb.gen ^ 2 / (n : K))) / 3] ∧
      Algebra.discr ℚ b1 = -27 * ((m * n : ℤ) : ℚ) ^ 2 ∧
      Algebra.discr ℚ b2 = R.readout () m n

private theorem ten_irreducible :
    Irreducible ((X : Polynomial ℚ) ^ 3 - C 10) := by
  have hnocubeInt (z : ℤ) : z ^ 3 ≠ 10 := by
    intro hz
    have hz7 : (z : ZMod 7) ^ 3 = (10 : ZMod 7) := by
      simpa only [Int.cast_pow, Int.cast_ofNat] using
        congrArg (fun x : ℤ => (x : ZMod 7)) hz
    have hnone (w : ZMod 7) : w ^ 3 ≠ (10 : ZMod 7) := by
      fin_cases w <;> decide
    exact hnone (z : ZMod 7) hz7
  have hnocubeRat (r : ℚ) : r ^ 3 ≠ 10 := by
    intro hr
    have hInt : IsIntegral ℤ r := by
      apply IsIntegral.of_pow (n := 3) (by norm_num)
      rw [hr]
      exact isIntegral_algebraMap
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hInt
    apply hnocubeInt z
    rw [← hz] at hr
    apply (Int.cast_injective (α := ℚ))
    simpa only [algebraMap_int_eq, eq_intCast,
      Int.cast_pow, Int.cast_ofNat] using hr
  exact X_pow_sub_C_irreducible_of_prime (by norm_num : Nat.Prime 3) hnocubeRat

private noncomputable def tenPowerBasis
    [Fact (Irreducible ((X : Polynomial ℚ) ^ 3 - C 10))] :
    PowerBasis ℚ (AdjoinRoot ((X : Polynomial ℚ) ^ 3 - C 10)) :=
  AdjoinRoot.powerBasis (monic_X_pow_sub_C 10 (by norm_num : 3 ≠ 0)).ne_zero

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  letI : Fact (Irreducible ((X : Polynomial ℚ) ^ 3 - C 10)) := ⟨ten_irreducible⟩
  let K0 := AdjoinRoot ((X : Polynomial ℚ) ^ 3 - C 10)
  let K := ULift.{u} K0
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  let pb : PowerBasis ℚ K :=
    tenPowerBasis.map (ULift.algEquiv (R := ℚ)).symm
  have h3 : pb.dim = 3 := by
    change (tenPowerBasis).dim = 3
    simp [tenPowerBasis]
  have hroot0 : (tenPowerBasis).gen ^ 3 = (10 : K0) := by
    simpa [tenPowerBasis, K0] using root_X_pow_sub_C_pow 3 (10 : ℚ)
  have hroot : pb.gen ^ 3 = (((10 : ℤ) * 1 ^ 2 : ℤ) : K) := by
    apply (ULift.algEquiv (R := ℚ)).injective
    change (tenPowerBasis.gen : K0) ^ 3 = 10
    exact hroot0
  have hcubic : (1 : ℤ) ^ 3 * 10 * 1 ^ 2 = 1 + 9 * 1 := by norm_num
  have hcv : (1 : ℤ) ^ 2 * 1 = 1 + 3 * 0 := by norm_num
  have hv : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have hm : (10 : ℤ) ≠ 0 := by norm_num
  have hn : (1 : ℤ) ≠ 0 := by norm_num
  intro h
  obtain ⟨_, _, _, b1, b2, _, hvec, _, hdisc⟩ :=
    h (K := K) (pb := pb) (h3 := h3) 10 1 1 1 0 1 hm hn hv hroot hcubic hcv
  obtain ⟨_, _, _, b1', b2', _, hvec', _, hdisc'⟩ :=
    integral_cubic_lattices (K := K) pb h3 10 1 1 1 0 1 hm hn hv
      hroot hcubic hcv
  have heq : (b2 : Fin 3 → K) = (b2' : Fin 3 → K) := hvec.trans hvec'.symm
  have hdisceq : Algebra.discr ℚ b2 = Algebra.discr ℚ b2' :=
    congrArg (Algebra.discr ℚ) heq
  rw [hdisc, hdisc'] at hdisceq
  norm_num [rejected, realize] at hdisceq

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by exact integral_cubic_lattices,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      change Unit at i
      cases i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      change Unit at j
      cases j
      exact (h rfl).elim
    · intro i
      change Empty at i
      exact nomatch i
  dependence := by
    intro i
    change Unit at i
    cases i
    dsimp [arena, signature] at *
    refine ⟨1, 0, 1, ?_⟩
    norm_num [actual, realize]

register_information_theorem integral_cubic_lattices in arena
  readout via (realize signature
    (fun _ m n => -3 * ((m * n : ℤ) : ℚ) ^ 2) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Lattices.PureCubicIntegralLattices
    coordinates := #[6]
    readouts := #[{
      path := Array.replicate 18 "body" ++
        #["arg", "arg", "arg", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 7 }] })
  escape continues (open)

#print axioms registration

open Lean in
run_meta do
  let env ← getEnv
  let some row := TemplateBinding.records env |>.find? (fun row =>
      row.occurrence.key.theoremName == ``integral_cubic_lattices)
    | throwError "pure cubic lattice registration evidence is missing"
  match row.result with
  | .declaredValidated _ => pure ()
  | .declaredUnresolved diagnostic =>
      throwError "pure cubic lattice registration is unresolved: {diagnostic}"
  | .undeclared => throwError "pure cubic lattice registration is undeclared"

end
end Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices
