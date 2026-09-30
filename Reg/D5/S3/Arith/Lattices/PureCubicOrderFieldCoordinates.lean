import D5.S3.Arith.Lattices.PureCubicOrderFieldCoordinates
import Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

open _root_.D5.S3.Arith.Lattices.PureCubicOrderFieldCoordinates
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial Module
open _root_.Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices

namespace Reg.D5.S3.Arith.Lattices.PureCubicOrderFieldCoordinates
universe u
noncomputable section

abbrev signature : Signature where
  Params := ℤ
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ c n => c ^ 2 * n) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀
    {K : Type u} [Field K] [NumberField K]
    (pb : PowerBasis ℚ K) (h3 : pb.dim = 3)
    (m n c a k v : ℤ) (hmpos : 0 < m) (hnpos : 0 < n) (hcpos : 0 < c)
    (hmsq : Squarefree m) (hnsq : Squarefree n) (hcop : IsCoprime m n)
    (hv : v = 1 ∨ v = -1)
    (hroot : pb.gen ^ 3 = ((m * n ^ 2 : ℤ) : K))
    (hcubic : c ^ 3 * m * n ^ 2 = 1 + 9 * a)
    (hcv : c ^ 2 * n = v + 3 * k),
    let gamma : K :=
      (1 + (c : K) * pb.gen + (v : K) * (pb.gen ^ 2 / (n : K))) / 3
    let theta : K := (c : K) * pb.gen
    let beta : K := (1 + theta + theta ^ 2) / 3
    (∀ z : K, IsIntegral ℤ z ↔ ∃ u r s : ℤ,
      z = (u : K) + (r : K) * pb.gen + (s : K) * gamma) ∧
    (∀ u r s : ℤ,
      (∃ x y t : ℤ,
        (u : K) + (r : K) * pb.gen + (s : K) * gamma =
          (x : K) + (y : K) * theta + (t : K) * beta) ↔
        c ∣ r ∧ R.readout () c n ∣ s)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  letI : Fact (Irreducible ((X : Polynomial ℚ) ^ 3 - C 10)) := ⟨ten_irreducible⟩
  let K0 := AdjoinRoot ((X : Polynomial ℚ) ^ 3 - C 10)
  let K := ULift.{u} K0
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  letI : FiniteDimensional ℚ K := (ULift.algEquiv.{0, 0, u} (R := ℚ)).symm.toLinearEquiv.finiteDimensional
  letI : NumberField K := {}
  let pb : PowerBasis ℚ K := tenPowerBasis.map (ULift.algEquiv (R := ℚ)).symm
  have h3 : pb.dim = 3 := by
    change tenPowerBasis.dim = 3
    simp [tenPowerBasis]
  have hroot0 : tenPowerBasis.gen ^ 3 = (10 : K0) := by
    simpa [tenPowerBasis, K0] using root_X_pow_sub_C_pow 3 (10 : ℚ)
  have hroot : pb.gen ^ 3 = (((10 : ℤ) * 1 ^ 2 : ℤ) : K) := by
    apply (ULift.algEquiv (R := ℚ)).injective
    change (tenPowerBasis.gen : K0) ^ 3 = 10
    exact hroot0
  have hcop : IsCoprime (10 : ℤ) 1 := isCoprime_one_right
  have hsq : Squarefree (10 : ℤ) := by
    apply Int.squarefree_natCast.mpr
    change Squarefree (2 * 5 : ℕ)
    exact (Nat.squarefree_mul (by norm_num)).mpr
      ⟨(Nat.prime_iff.mp (by norm_num : Nat.Prime 2)).squarefree,
        (Nat.prime_iff.mp (by norm_num : Nat.Prime 5)).squarefree⟩
  intro h
  have hcriterion := (h pb h3 10 1 1 1 0 1
    (by norm_num) (by norm_num) (by norm_num)
    hsq (by simp) hcop (Or.inl rfl) hroot
    (by norm_num) (by norm_num)).2 0 0 1
  have hmem : ∃ x y t : ℤ,
      (0 : K) + (0 : K) * pb.gen + (1 : K) *
        ((1 + (1 : K) * pb.gen + (1 : K) * (pb.gen ^ 2 / (1 : K))) / 3) =
        (x : K) + (y : K) * ((1 : K) * pb.gen) + (t : K) *
          ((1 + (1 : K) * pb.gen + ((1 : K) * pb.gen) ^ 2) / 3) := by
    refine ⟨0, 0, 1, ?_⟩
    norm_num
  have hmem' := hmem
  simp only [Int.cast_zero, Int.cast_one] at hcriterion
  have hbad := (hcriterion.mp hmem').2
  change (0 : ℤ) ∣ 1 at hbad
  norm_num at hbad

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pure_cubic_order_field_coordinates, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      cases j
      exact (h rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    change ∃ c : ℤ, ∃ n₁ n₂ : ℤ, actual.readout () c n₁ ≠ actual.readout () c n₂
    refine ⟨1, 1, 2, ?_⟩
    norm_num [actual, realize]

register_information_theorem pure_cubic_order_field_coordinates in arena
  readout via (realize signature (fun _ c n => c ^ 2 * n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Lattices.PureCubicOrderFieldCoordinates
    coordinates := #[7]
    readouts := #[{
      path := Array.replicate 24 "body" ++
        #["arg", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms registration

open Lean in
run_meta do
  let env ← getEnv
  let some row := TemplateBinding.records env |>.find? (fun row =>
      row.occurrence.key.theoremName == ``pure_cubic_order_field_coordinates)
    | throwError "cubic field-coordinate registration evidence is missing"
  match row.result with
  | .declaredValidated _ => pure ()
  | .declaredUnresolved diagnostic =>
      throwError "cubic field-coordinate registration is unresolved: {diagnostic}"
  | .undeclared => throwError "cubic field-coordinate registration is undeclared"

end
end Reg.D5.S3.Arith.Lattices.PureCubicOrderFieldCoordinates
