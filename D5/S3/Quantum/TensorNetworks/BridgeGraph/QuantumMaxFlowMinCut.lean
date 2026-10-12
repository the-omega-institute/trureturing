/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowMinCut
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowMinCut
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: QuantumMaxFlowMinCut for width-three bridge flow. -/

/-
proof_shape: result: content
escape_witness: result: QuantumMaxFlowMinCut.claim_of_hypotheses
admission_basis: open-problem-resolution (#14652; Proved)
Module content mechanism: claim_of_hypotheses: strong induction over simultaneous cone descent.
Direct frozen dependencies: none on the implementation baseline.
Utility: none; symbolic constructions and proofs for arbitrary dimensions,
not bounded enumeration, a checker, numeric reduction, or a certified instance.
Information-escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14762
-/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.CastlingDeficit
import D5.S3.Quantum.TensorNetworks.BridgeGraph.LongReservoir

set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowMinCut
open Matrix Module

open D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open D5.S3.Quantum.TensorNetworks.BridgeGraph.CastlingDeficit
open D5.S3.Quantum.TensorNetworks.BridgeGraph.LongReservoir
open Matrix Module
private theorem cone_descent {a b : ℕ} (ha : 0 < a) (hab : a ≤ b)
    (hq : a * a + b * b ≤ 3 * a * b) (hlarge : 2 * a ≤ b) :
    0 < 3 * a - b ∧ 3 * a - b ≤ a ∧ a < b ∧
      (3 * a - b) * (3 * a - b) + a * a ≤ 3 * (3 * a - b) * a := by
  have hbound := cone_bounds ha hq
  have hsub : (3 * a - b : ℕ) + b = 3 * a := Nat.sub_add_cancel hbound.le
  have hsubZ : ((3 * a - b : ℕ) : ℤ) = 3 * (a : ℤ) - (b : ℤ) := by omega
  have hqZ : (a : ℤ) * a + (b : ℤ) * b ≤ 3 * (a : ℤ) * b := by exact_mod_cast hq
  have hid : ((3 * a - b : ℕ) : ℤ) * (3 * a - b : ℕ) + (a : ℤ) * a -
      3 * (3 * a - b : ℕ) * (a : ℤ) = (a : ℤ) * a + (b : ℤ) * b - 3 * a * b := by
    rw [hsubZ]
    ring
  refine ⟨by omega, by omega, by omega, ?_⟩
  have hz : ((3 * a - b : ℕ) : ℤ) * (3 * a - b : ℕ) + (a : ℤ) * a ≤
      3 * (3 * a - b : ℕ) * (a : ℤ) := by omega
  exact_mod_cast hz

private theorem full_rank_of_descent (castling : Castling) {a b c d : ℕ}
    (hb : b ≤ 3 * a) (hd : d ≤ 3 * c)
    (hsmall : QMaxFlow (3 * a - b) a (3 * c - d) c =
      min ((3 * a - b) * c) (a * (3 * c - d))) :
    QMaxFlow a b c d = min (a * d) (b * c) := by
  have hu : (3 * a - b : ℕ) + b = 3 * a := Nat.sub_add_cancel hb
  have hv : (3 * c - d : ℕ) + d = 3 * c := Nat.sub_add_cancel hd
  have hbu : 3 * a - (3 * a - b) = b := by omega
  have hdv : 3 * c - (3 * c - d) = d := by omega
  have hcast := castling (3 * a - b) a (3 * c - d) c (by omega) (by omega)
  rw [hbu, hdv, hsmall] at hcast
  have hcuts : (3 * a - b) * c + b * c = a * (3 * c - d) + a * d := by
    nlinarith [congrArg (fun x : ℕ => x * c) hu,
      congrArg (fun x : ℕ => a * x) hv]
  have hcutsZ : (((3 * a - b) * c : ℕ) : ℤ) + ((b * c : ℕ) : ℤ) =
      ((a * (3 * c - d) : ℕ) : ℤ) + ((a * d : ℕ) : ℤ) := by exact_mod_cast hcuts
  have hmin1 := min_le_left ((3 * a - b) * c) (a * (3 * c - d))
  have hmin2 := min_le_right ((3 * a - b) * c) (a * (3 * c - d))
  rcases le_total ((3 * a - b) * c) (a * (3 * c - d)) with h | h
  · rw [min_eq_left h] at hcast
    have horder : a * d ≤ b * c := by omega
    rw [min_eq_left horder]
    omega
  · rw [min_eq_right h] at hcast
    have horder : b * c ≤ a * d := by omega
    rw [min_eq_right horder]
    omega

private theorem claim_of_hypotheses (base : BaseWitness) (castling : Castling)
    (widthTwo : WidthTwo) : ∀ a b c d : ℕ, 0 < a → a ≤ b → 0 < c → c ≤ d →
    a*a+b*b ≤ 3*a*b → c*c+d*d ≤ 3*c*d →
    QMaxFlow a b c d = min (a*d) (b*c) := by
  have main : ∀ n : ℕ, ∀ a b c d : ℕ, b + d = n →
      0 < a → a ≤ b → 0 < c → c ≤ d →
      a * a + b * b ≤ 3 * a * b → c * c + d * d ≤ 3 * c * d →
      QMaxFlow a b c d = min (a * d) (b * c) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b c d hn ha hab hc hcd hq hq'
      by_cases hsquare : a = b ∨ c = d
      · exact rationalWitness_full_rank (widthTwo a b c d ha hab hc hcd
          (hsquare.elim Or.inl (fun h => Or.inr (Or.inl h))))
      by_cases hb : 2 * a ≤ b
      · by_cases hd : 2 * c ≤ d
        · obtain ⟨hu, hua, hab', hqu⟩ := cone_descent ha hab hq hb
          obtain ⟨hv, hvc, hcd', hqv⟩ := cone_descent hc hcd hq' hd
          have hsmall := ih (a + c) (by omega) (3 * a - b) a (3 * c - d) c
            rfl hu hua hv hvc hqu hqv
          exact full_rank_of_descent castling (cone_bounds ha hq).le
            (cone_bounds hc hq').le hsmall
        · exact rationalWitness_full_rank (widthTwo a b c d ha hab hc hcd
            (Or.inr (Or.inr (Or.inl ⟨hb, by omega⟩))))
      · by_cases hd : 2 * c ≤ d
        · exact rationalWitness_full_rank (widthTwo a b c d ha hab hc hcd
            (Or.inr (Or.inr (Or.inr ⟨by omega, hd⟩))))
        · exact rationalWitness_full_rank
            (base a b c d ha (by omega) (by omega) hc (by omega) (by omega))
  intro a b c d ha hab hc hcd hq hq'
  exact main (b + d) a b c d rfl ha hab hc hcd hq hq'

def claim : Prop :=
  ∀ a b c d : ℕ, 0 < a → a ≤ b → 0 < c → c ≤ d →
    a * a + b * b ≤ 3 * a * b → c * c + d * d ≤ 3 * c * d →
    QMaxFlow a b c d = QMinCut a b c d ∧
      QMinCut a b c d = min (a * d) (b * c)

theorem result : claim := by
  intro a b c d ha hab hc hcd hq hq'
  have hflow := claim_of_hypotheses base_witness castling_proved widthTwo_proved
    a b c d ha hab hc hcd hq hq'
  have hcut := cone_QMinCut ha hc hq hq'
  exact ⟨le_antisymm (QMaxFlow_le_QMinCut a b c d)
    (by rw [hcut, hflow]), hcut⟩

end D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowMinCut
