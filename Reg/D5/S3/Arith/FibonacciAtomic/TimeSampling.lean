import D5.S3.Arith.FibonacciAtomic.TimeSampling
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.TimeSampling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => recoveryLimit n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 2 ≤ n →
    PairwiseRecovery n (Finset.range (recoveryLimit n)) ∧
      ∀ T : Finset ℕ, PairwiseRecovery n T → T.card ≤ R.readout () () n

theorem actual_law : arena.Law actual := pairwise_recovery_maximum

theorem singleton_recovery (n : ℕ) : PairwiseRecovery n {0} := by
  intro s hs t ht hst
  simp only [Finset.mem_singleton] at hs ht
  omega

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 2 le_rfl).2 {0} (singleton_recovery 2)
  change ({0} : Finset ℕ).card ≤ 0 at bad
  simp at bad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change recoveryLimit 1 ≠ recoveryLimit 2
    have hset : {p : ℕ | p.Prime ∧ p ∣ 1} = ∅ := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hp, hdiv⟩
      have heq := Nat.dvd_one.mp hdiv
      exact hp.ne_one heq
    have h1 : recoveryLimit 1 = 0 := by
      unfold recoveryLimit
      rw [hset]
      simp
    have h2 := (pairwise_recovery_maximum 2 le_rfl).2 {0} (singleton_recovery 2)
    simp only [Finset.card_singleton] at h2
    omega

register_information_theorem pairwise_recovery_maximum in arena
  readout via (realize signature (fun _ _ n => recoveryLimit n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.TimeSampling
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "arg", "body", "body", "arg"], stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling
