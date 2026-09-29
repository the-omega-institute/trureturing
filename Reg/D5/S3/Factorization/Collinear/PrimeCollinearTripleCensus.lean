import D5.S3.Factorization.Collinear.PrimeCollinearTripleCensus
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S3.Factorization.Collinear.PrimeCollinearTripleCensus

open _root_.D5.S3.Factorization.Collinear.PrimeCollinearTripleCensus
open _root_.D5.S3.Factorization.CollinearTripleTranslationOrbits
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => Nat.card (Triple p)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law r := ∀ p : ℕ, p.Prime →
    r.readout () () p = p * (p - 1) * Nat.choose p 3

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 3 Nat.prime_three
  norm_num [arena, rejected, realize] at hbad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro p hp
    simpa [arena, actual, realize] using card_triples_prime p hp,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 2, 3, ?_⟩
    have htwo : Nat.card (Triple 2) = 0 := by
      simpa using card_triples_prime 2 Nat.prime_two
    have hthree : Nat.card (Triple 3) = 6 := by
      simpa using card_triples_prime 3 Nat.prime_three
    change Nat.card (Triple 2) ≠ Nat.card (Triple 3)
    omega

register_information_theorem card_triples_prime in arena
  readout via (realize signature (fun _ _ p => Nat.card (Triple p)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.Collinear.PrimeCollinearTripleCensus
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Factorization.Collinear.PrimeCollinearTripleCensus
