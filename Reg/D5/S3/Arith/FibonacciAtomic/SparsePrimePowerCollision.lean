import D5.S3.Arith.FibonacciAtomic.SparsePrimePowerCollision
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.SparsePrimePowerCollision
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.SparsePrimePowerCollision

abbrev signature : Signature where
  Params := Σ _p : ℕ, Σ _e : ℕ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ parameters value =>
    Nat.gcd value (parameters.2.2 * parameters.1 ^ parameters.2.1))
    (fun anchor => nomatch anchor)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun anchor => nomatch anchor)

abbrev arena : Arena where
  signature := signature
  Law observation := ∀ (p e Q : ℕ) (hp : p.Prime)
    (he : 2 ≤ e) (hQ : 0 < Q) (S : Finset ℕ)
    (hS : ∀ k ∈ S, 1 ≤ k) (hcard : S.card < threshold p e),
    ∃ n z n2 z2 : ℤ, ∃ a b a2 b2 : ℕ,
      ¬ ((p : ℤ) ∣ n ∧ (p : ℤ) ∣ z) ∧
      ¬ ((p : ℤ) ∣ n2 ∧ (p : ℤ) ∣ z2) ∧
      a < Q * p ^ e ∧ b < Q * p ^ e ∧
      a2 < Q * p ^ e ∧ b2 < Q * p ^ e ∧
      (∀ k : ℕ, 1 ≤ k →
        Nat.gcd (sourceObservation a b k) (Q * p ^ e) =
          Q * Nat.gcd (signedObservation n z k).natAbs (p ^ e) ∧
        Nat.gcd (sourceObservation a2 b2 k) (Q * p ^ e) =
          Q * Nat.gcd (signedObservation n2 z2 k).natAbs (p ^ e)) ∧
      (∀ k ∈ S,
        Nat.gcd (signedObservation n z k).natAbs (p ^ e) =
          Nat.gcd (signedObservation n2 z2 k).natAbs (p ^ e) ∧
        Nat.gcd (sourceObservation a b k) (Q * p ^ e) =
          Nat.gcd (sourceObservation a2 b2 k) (Q * p ^ e)) ∧
      (∀ B : ℕ, ∃ t : ℕ, B < t ∧ 1 ≤ t ∧ t ∉ S ∧
        Nat.gcd (signedObservation n z t).natAbs (p ^ e) = p ^ e ∧
        Nat.gcd (signedObservation n2 z2 t).natAbs (p ^ e) = p ^ (e - 1) ∧
        Nat.gcd (sourceObservation a b t) (Q * p ^ e) = Q * p ^ e ∧
        observation.readout () ⟨p, e, Q⟩ (sourceObservation a2 b2 t) = (Q * p ^ e) / p)

theorem actual_law : arena.Law actual := sparse_prime_power_gcd_collision

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have positive : 0 < threshold 2 2 := by
    have rankPositive (m : ℕ) (hm : 0 < m) : 0 <
        _root_.D5.S3.Arith.FibonacciAtomic.TimeSampling.zeroRank m := by
      let : NeZero m := ⟨hm.ne'⟩
      let step : ZMod m × ZMod m → ZMod m × ZMod m := fun state =>
        (state.2, state.1 + state.2)
      have injective : Function.Injective step := by
        intro state state2 equality
        have first := congrArg Prod.fst equality
        have second := congrArg Prod.snd equality
        dsimp [step] at first second
        exact Prod.ext (add_right_cancel (first ▸ second)) first
      let castState : ℕ × ℕ → ZMod m × ZMod m := fun state => (state.1, state.2)
      have semiconj : Function.Semiconj castState
          (fun state : ℕ × ℕ => (state.2, state.1 + state.2)) step := by
        intro state
        simp [castState, step]
      obtain ⟨period, positive, returning⟩ := injective.mem_periodicPts (0, 1)
      have zero : (Nat.fib period : ZMod m) = 0 := by
        have equality := congrArg Prod.fst (semiconj.iterate_right period (0, 1))
        simpa [Nat.fib, castState, returning.eq] using equality
      exact (Nat.sInf_mem (show Set.Nonempty {k : ℕ | 0 < k ∧ m ∣ Nat.fib k} from
        ⟨period, positive, (ZMod.natCast_eq_zero_iff _ _).mp zero⟩)).1
    have top := rankPositive 4 (by norm_num)
    have lower := rankPositive 2 (by norm_num)
    have lowerBound : _root_.D5.S3.Arith.FibonacciAtomic.TimeSampling.zeroRank 2 ≤ 3 :=
      Nat.sInf_le (by norm_num)
    have topBound : 3 < _root_.D5.S3.Arith.FibonacciAtomic.TimeSampling.zeroRank 4 := by
      have minimal := Nat.sInf_mem (show Set.Nonempty {k : ℕ | 0 < k ∧ 4 ∣ Nat.fib k} from
        ⟨6, by norm_num, by norm_num⟩)
      change 0 < _root_.D5.S3.Arith.FibonacciAtomic.TimeSampling.zeroRank 4 ∧
        4 ∣ Nat.fib (_root_.D5.S3.Arith.FibonacciAtomic.TimeSampling.zeroRank 4) at minimal
      have facts : ∀ k : ℕ, k ≤ 3 → 0 < k → ¬ 4 ∣ Nat.fib k := by
        intro k hk positive
        interval_cases k <;> norm_num at *
      by_contra bad
      exact facts _ (by omega) minimal.1 minimal.2
    unfold threshold
    norm_num only [Nat.reducePow, Nat.reduceSub]
    split_ifs <;> omega
  obtain ⟨n, z, n2, z2, a, b, a2, b2, primitive, primitive2,
    boundA, boundB, boundA2, boundB2, realization, agreement, separation⟩ :=
    law 2 2 1 Nat.prime_two le_rfl (by norm_num) ∅
      (by simp) (by simpa using positive)
  obtain ⟨time, later, positiveTime, outside, first, second, firstSource, secondSource⟩ := separation 0
  change 0 = (1 * 2 ^ 2) / 2 at secondSource
  norm_num at secondSource

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun role => ⟨rejected,
    fun other different => (different (Subsingleton.elim other role)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨⟨2, 2, 1⟩, 0, 1, ?_⟩
    change Nat.gcd 0 (1 * 2 ^ 2) ≠ Nat.gcd 1 (1 * 2 ^ 2)
    norm_num

register_information_theorem sparse_prime_power_gcd_collision in arena
  readout via (realize signature (fun _ parameters value =>
    Nat.gcd value (parameters.2.2 * parameters.1 ^ parameters.2.1))
    (fun anchor => nomatch anchor))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.SparsePrimePowerCollision
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateOperand := some #["fn", "arg"] }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.SparsePrimePowerCollision
