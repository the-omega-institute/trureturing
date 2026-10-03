import D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct

open _root_.D5.S1.Scale
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct
open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

def signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => EisensteinOrder
  Anchor := Empty
  finiteAnchor := inferInstance

private def factor (j : ℕ) : EisensteinOrder :=
  orientedFactor ((goldenLucas (3 ^ j) - 1).toNat)

def actual : Realization signature :=
  realize signature (fun _ _ j => factor j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : EisensteinOrder)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (j : ℕ) (_hj : 1 ≤ j),
    let x : ℤ := goldenLucas (3 ^ j)
    let b : ℕ := (x - 1).toNat
    let B : ℕ := blockNorm b
    let eta : EisensteinOrder := R.readout () () j
    let lambda : EisensteinOrder := 1 + 2 * QuadraticAlgebra.omega
    eta = QuadraticAlgebra.omega * ((x : EisensteinOrder) + lambda) ∧
    QuadraticAlgebra.norm eta = (B : ℤ) ∧
    (9 : EisensteinOrder) ∣ eta - (1 + lambda ^ 3) ∧
    IsCoprime (Ideal.span {eta}) (Ideal.span {star eta}) ∧
    ∃ pi : ℕ → EisensteinOrder,
      (∀ p ∈ B.primeFactors,
        let P : Ideal EisensteinOrder := orientedIdeal b ⊔ Ideal.span {(p : EisensteinOrder)}
        P.IsPrime ∧
          (∀ Q : Ideal EisensteinOrder, Q.IsPrime →
            (p : EisensteinOrder) ∈ Q → eta ∈ Q → Q = P) ∧
          Ideal.span {pi p} = P ∧
          QuadraticAlgebra.norm (pi p) = (p : ℤ) ∧
          (3 : EisensteinOrder) ∣ pi p - 1 ∧
          p % 3 = 1) ∧
      eta = ∏ p ∈ B.primeFactors,
        (pi p) ^ padicValNat p (Nat.fib (fibonacciRank p))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h3 : goldenLucas 3 = 4 := by
    norm_num [goldenLucas, D5.S0.Carrier.trace, D5.S0.Carrier.phi, pow_succ]
  have hnorm := (h 1 (by decide)).2.1
  change QuadraticAlgebra.norm (0 : EisensteinOrder) =
    (blockNorm ((goldenLucas 3 - 1).toNat) : ℤ) at hnorm
  norm_num [h3, blockNorm, QuadraticAlgebra.norm_def] at hnorm

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨golden_cubic_primary_product, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    change ∃ (_ : Unit) (x y : ℕ), factor x ≠ factor y
    refine ⟨(), 1, 2, ?_⟩
    have h3 : goldenLucas 3 = 4 := by
      norm_num [goldenLucas, D5.S0.Carrier.trace, D5.S0.Carrier.phi, pow_succ]
    have h9 : goldenLucas 9 = 76 := by
      simpa [h3] using (golden_cubic_lucas_block 1 (by decide)).2.2.2.2.2
    intro h
    have him := congrArg QuadraticAlgebra.im h
    norm_num [factor, orientedFactor, h3, h9] at him

register_information_theorem
  _root_.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.golden_cubic_primary_product
  in arena
  readout via (realize signature (fun _ _ j => factor j) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "value"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end

end Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct
