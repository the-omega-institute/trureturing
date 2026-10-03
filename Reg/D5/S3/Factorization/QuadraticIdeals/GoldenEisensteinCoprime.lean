import D5.S3.Factorization.QuadraticIdeals.GoldenEisensteinCoprime
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.QuadraticIdeals.GoldenEisensteinCoprime

open _root_.D5.S1.Scale
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S3.Factorization.QuadraticIdeals.GoldenEisensteinCoprime
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

private def eta (j : ℕ) : EisensteinOrder :=
  ⟨-2, goldenLucas (3 ^ j) - 1⟩

def signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => EisensteinOrder
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ j => eta j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : EisensteinOrder)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (j : ℕ) (_hj : 1 ≤ j),
    let factor : EisensteinOrder := R.readout () () j
    IsCoprime (Ideal.span {factor}) (Ideal.span {star factor})

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h 1 (by decide)
  change IsCoprime (Ideal.span {(0 : EisensteinOrder)})
    (Ideal.span {star (0 : EisensteinOrder)}) at hzero
  have hcop : IsCoprime (0 : EisensteinOrder) 0 := by
    simpa using (Ideal.isCoprime_span_singleton_iff
      (0 : EisensteinOrder) (0 : EisensteinOrder)).mp hzero
  exact not_isCoprime_zero_zero hcop

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro j hj
    exact golden_eisenstein_conjugate_coprime j hj
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
    change ∃ (_ : Unit) (x y : ℕ), eta x ≠ eta y
    refine ⟨(), 1, 2, ?_⟩
    have h3 : goldenLucas 3 = 4 := by
      norm_num [goldenLucas, D5.S0.Carrier.trace, D5.S0.Carrier.phi, pow_succ]
    have h9 : goldenLucas 9 = 76 := by
      simpa [h3] using (golden_cubic_lucas_block 1 (by decide)).2.2.2.2.2
    intro h
    have him := congrArg QuadraticAlgebra.im h
    norm_num [eta, h3, h9] at him

register_information_theorem
  _root_.D5.S3.Factorization.QuadraticIdeals.GoldenEisensteinCoprime.golden_eisenstein_conjugate_coprime
  in arena
  readout via (realize signature (fun _ _ j => eta j) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.QuadraticIdeals.GoldenEisensteinCoprime
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "value"], stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end

end Reg.D5.S3.Factorization.QuadraticIdeals.GoldenEisensteinCoprime
