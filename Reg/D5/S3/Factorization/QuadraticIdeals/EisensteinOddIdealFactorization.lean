import D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization

open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

def signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Ideal EisensteinOrder
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ b => orientedIdeal b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (⊥ : Ideal EisensteinOrder)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (b : ℕ) (_hb : Odd b),
    R.readout () () b =
      ∏ p ∈ (blockNorm b).primeFactors,
        (orientedIdeal b ⊔ Ideal.span {(p : EisensteinOrder)}) ^
          (blockNorm b).factorization p

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h 1 (by decide)
  change (⊥ : Ideal EisensteinOrder) =
    ∏ p ∈ (blockNorm 1).primeFactors,
      (orientedIdeal 1 ⊔ Ideal.span {(p : EisensteinOrder)}) ^
        (blockNorm 1).factorization p at hzero
  rw [← eisenstein_odd_ideal_factorization 1 (by decide)] at hzero
  have heta : orientedFactor 1 ∈ orientedIdeal 1 := Ideal.mem_span_singleton_self _
  rw [← hzero] at heta
  have hz : orientedFactor 1 = 0 := by simpa only [Submodule.mem_bot] using heta
  have hr := congrArg QuadraticAlgebra.re hz
  norm_num [orientedFactor] at hr

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro b hb
    exact eisenstein_odd_ideal_factorization b hb
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
    change ∃ (_ : Unit) (x y : ℕ), orientedIdeal x ≠ orientedIdeal y
    refine ⟨(), 1, 3, ?_⟩
    intro heq
    have hC7 : (QuadraticAlgebra.C (7 : ℤ) : EisensteinOrder) = 7 := by
      norm_num [QuadraticAlgebra.C_eq_algebraMap]
    have h7 : (7 : EisensteinOrder) ∈ orientedIdeal 1 := by
      apply Ideal.mem_span_singleton.mpr
      have hc := ((eisenstein_odd_scalar_quotient 1 (by decide)).1 (7 : ℤ)).mpr
        (by norm_num [blockNorm])
      simpa only [hC7] using hc
    rw [heq] at h7
    have hdiv := ((eisenstein_odd_scalar_quotient 3 (by decide)).1 (7 : ℤ)).mp
      (by
        apply Ideal.mem_span_singleton.mp
        simpa only [orientedIdeal, hC7] using h7)
    norm_num [blockNorm] at hdiv

register_information_theorem
  _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.eisenstein_odd_ideal_factorization
  in arena
  readout via (realize signature (fun _ _ b => orientedIdeal b) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end

end Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization
