import D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling
open _root_.D5.S3.Arith.FibonacciAtomic.TimeSampling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ → ℕ → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p n => localGcd p n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ _ => 0) (fun e => nomatch e)

def signed (R : Realization signature) (p : ℕ) (n z : ℤ) (k : ℕ) : ℕ :=
  R.readout () p n z k

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p : ℕ}, p.Prime →
    ∀ (S : Finset ℕ), (∀ k ∈ S, 0 < k) →
    let r := zeroRank p
    let A := S.image (fun k => k % r)
    let T := if r = p + 1 then r - 1 else r
    ((∀ n z n' z' : ℤ,
      (∀ k ∈ S, signed R p n z k = localGcd p n' z' k) →
      ∀ k, 0 < k → localGcd p n z k = localGcd p n' z' k) ↔ T ≤ A.card) ∧
    ((∀ a b a' b' : ℕ,
      (∀ k ∈ S, sourceGcd p a b k = sourceGcd p a' b' k) →
      ∀ k, 0 < k → sourceGcd p a b k = sourceGcd p a' b' k) ↔ T ≤ A.card) ∧
    (A.card < T → ∀ Q, 0 < Q →
      let H := Q * p
      ∃ n z n' z' : ℤ, ∃ a b a' b' : ℕ,
        primitive p n z ∧ primitive p n' z' ∧
        a < H ∧ b < H ∧ a' < H ∧ b' < H ∧
        (∀ k, 0 < k → sourceGcd H a b k = Q * localGcd p n z k ∧
          sourceGcd H a' b' k = Q * localGcd p n' z' k) ∧
        (∀ k ∈ S, localGcd p n z k = localGcd p n' z' k ∧
          sourceGcd H a b k = sourceGcd H a' b' k) ∧
        ∀ B, ∃ t, B < t ∧ 0 < t ∧ t ∉ S ∧
          localGcd p n z t = p ∧ localGcd p n' z' t = 1 ∧
          sourceGcd H a b t = H ∧ sourceGcd H a' b' t = Q ∧
          sourceGcd H a' b' t = H / p)

theorem actual_law : arena.Law actual := by
  intro p hp S hS
  exact prime_phase_gcd_sampling hp S hS

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hS : ∀ k ∈ ({1} : Finset ℕ), 0 < k := by simp
  have hbad := h Nat.prime_two {1} hS
  have hthreshold := hbad.1.mp (by
    intro n z n' z' hobs k hk
    have hz := hobs 1 (Finset.mem_singleton_self 1)
    change 0 = localGcd 2 n' z' 1 at hz
    have hpos : 0 < localGcd 2 n' z' 1 :=
      Nat.gcd_pos_of_pos_right _ (by decide)
    omega)
  have hactual := (prime_phase_gcd_sampling Nat.prime_two {1} hS).1.mpr hthreshold
  have hobs : ∀ k ∈ ({1} : Finset ℕ), localGcd 2 0 1 k = localGcd 2 1 1 k := by
    intro k hk
    have heq : k = 1 := Finset.mem_singleton.mp hk
    subst k
    norm_num [localGcd]
  have heq := hactual 0 1 1 1 hobs 2 (by decide)
  norm_num [localGcd] at heq

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨2, 0, 1, ?_⟩
    intro heq
    have h := congrFun (congrFun heq 0) 2
    norm_num [actual, realize, localGcd] at h

register_information_theorem prime_phase_gcd_sampling in arena
  readout via (realize signature (fun _ p n => localGcd p n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body",
          "fn", "arg", "fn", "arg", "body", "body", "body",
          "body", "domain", "body", "body", "fn", "arg", "fn",
          "fn", "fn"]
        functionOperand := true }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling
