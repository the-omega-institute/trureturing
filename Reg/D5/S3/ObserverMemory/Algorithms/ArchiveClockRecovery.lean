import D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery
import Reg.Support.DependentFamily

open Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery

open _root_.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery

noncomputable section

universe uX uA uY

def signature : Signature where
  Params := Unit
  State := fun _ => Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ (n : Nat) => n ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ (_ : Nat) => (0 : Nat)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := forall {X : Type uX} {A : Type uA} {Y : Type uY},
    [Fintype X] -> [Fintype A] -> [Fintype Y] ->
    forall (n : Nat) (_hcard : Fintype.card X = n)
      (X0 : Set X) (_hX0 : X0.Nonempty) (S : System X A Y),
      List.TFAE [
        ArchiveRecoverable S X0,
        forall x, x ∈ X0 -> forall x', x' ∈ X0 -> forall word,
          SynchronizedPath S x x' word -> deltaSum S x x' word = 0,
        forall pair, SynchronouslyReachable S X0 pair -> forall a,
          SynchronizedEdge S pair a -> S.cost a pair.1 - S.cost a pair.2 = 0] ∧
      (Not (ArchiveRecoverable S X0) ->
        exists x, x ∈ X0 ∧ exists x', x' ∈ X0 ∧ exists word,
          Legal S x word ∧ Legal S x' word ∧
            visibleArchive S x word = visibleArchive S x' word ∧
            clock S x word ≠ clock S x' word ∧
            word.length <= R.readout () () n)

def ambiguitySystem :
    System (ULift.{uX} Bool) (ULift.{uA} Unit) (ULift.{uY} Unit) where
  domain := fun _ _ => True
  domainDecidable := fun _ _ => inferInstance
  successor := fun _ state => state
  reading := fun _ _ _ => ULift.up ()
  cost := fun _ state => if state.down then 1 else 0

theorem ambiguity_not_recoverable :
    ¬ ArchiveRecoverable ambiguitySystem Set.univ := by
  intro hrecoverable
  rcases hrecoverable with ⟨recover, hrecover⟩
  have hfalse := hrecover (ULift.up false) (Set.mem_univ _) [ULift.up ()] (by
    simp [Legal, ambiguitySystem])
  have htrue := hrecover (ULift.up true) (Set.mem_univ _) [ULift.up ()] (by
    simp [Legal, ambiguitySystem])
  simp [visibleArchive, clock, ambiguitySystem] at hfalse htrue
  omega

theorem rejected_law : ¬ arena.{uX, uA, uY}.Law rejected := by
  intro h
  have hspecial := h
    (X := ULift.{uX} Bool) (A := ULift.{uA} Unit) (Y := ULift.{uY} Unit)
    2 (by simp) Set.univ ⟨ULift.up false, Set.mem_univ _⟩ ambiguitySystem
  rcases hspecial.2 ambiguity_not_recoverable with
    ⟨x, _, x', _, word, _, _, _, hclock, hlength⟩
  have hzero : word.length = 0 := Nat.eq_zero_of_le_zero (by
    simpa [rejected, realize] using hlength)
  have hempty : word = [] := List.eq_nil_of_length_eq_zero hzero
  subst word
  simp [clock] at hclock

def registration : Registration arena.{uX, uA, uY}
    (arena.{uX, uA, uY}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro X A Y instX instA instY n hcard X0 hX0 S
    simpa only [actual, realize, signature] using
      (@archive_clock_recovery_and_finite_ambiguity
        X A Y instX instA instY n hcard X0 hX0 S)
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hji
        exact False.elim (hji (show j = i from @Subsingleton.elim Unit _ j i))
      · funext e
        exact nomatch e
    · intro i
      exact nomatch i
  dependence := by
    intro i
    change Unit at i
    rcases i with ⟨⟩
    refine ⟨(), (0 : Nat), (1 : Nat), ?_⟩
    change (0 : Nat) ^ 2 ≠ (1 : Nat) ^ 2
    exact Nat.zero_ne_one

register_information_theorem archive_clock_recovery_and_finite_ambiguity
  in arena
  readout via (realize signature (fun _ _ (n : Nat) => n ^ 2) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "body", "arg", "arg", "body", "arg", "arg", "arg",
        "arg", "arg"]
      stateBinder := 6 }] })
  escape continues (open)

#print axioms ambiguity_not_recoverable
#print axioms rejected_law
#print axioms registration

end

end Reg.D5.S3.ObserverMemory.Algorithms.ArchiveClockRecovery
