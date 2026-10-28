import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.ThreeNegativeExchange
import Reg.Support.DependentFamily

/-! The actual source family and candidate readout retain the complete native
telescope. A lawful sourceSelection, whole-family variation/sensitivity and actual
observational dependence remain unresolved under issue #22063; the
source reconstruction below is not a completed Contract.Registration. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.MixedSuffixEnergy
open _root_.D5.S3.Combinatorics.Circle.TwoOppositeLargeExchange
open _root_.D5.S3.Combinatorics.Circle.ThreeNegativeExchange

namespace Reg.D5.S3.Combinatorics.Circle.ThreeNegativeExchange

structure Source where
  k : ℕ
  t : ℕ
  p : Fin k
  y : Fin k
  zpen : Fin k
  z : Fin k
  A : List (Fin k)
  T0 : List (Fin k)
  T1 : List (Fin k)
  T2 : List (Fin k)
  E : List (Fin k)

def word (q : Source) : List (Fin q.k) :=
  q.A ++ [hit q.k 2 q.p] ++ q.T0 ++ [q.y] ++ q.T1 ++ [q.zpen] ++
    q.T2 ++ [q.z] ++ q.E

def Assumptions (q : Source) : Prop :=
  3 ≤ q.k ∧ 0 < s q.k q.t q.p ∧
  Q q.k ≤ |s q.k q.t (hit q.k 1 q.p)| ∧
  N q.k < 3 * |s q.k q.t q.p| ∧ Legal q.k q.t (word q) ∧
  q.p ∉ word q ∧ hit q.k 1 q.p ∉ word q ∧
  (∀ a ∈ q.T0 ++ q.T1 ++ q.T2 ++ q.E, |s q.k q.t a| < Q q.k) ∧
  Q q.k ≤ -s q.k q.t q.y ∧ Q q.k ≤ -s q.k q.t q.zpen ∧ Q q.k ≤ -s q.k q.t q.z

def candidate (q : Source) (V : List (Fin q.k)) : Prop :=
  Legal q.k q.t V ∧ J q.k q.t V < J q.k q.t (word q)

abbrev signature : Signature where
  Params := Source
  State q := List (Fin q.k)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q V => candidate q V) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ q : Source, Assumptions q → ∃ V, R.readout () q V

abbrev sourceScope := type_of% (@actualSource_threeNegative_exchange_full)

theorem bridge : sourceScope ↔ arena.Law actual := by
  constructor
  · intro h q hq
    obtain ⟨hk, hp, hn, hex, hW, hpu, hnu, hs, hy, hzp, hz⟩ := hq
    exact h q.k q.t hk q.p q.y q.zpen q.z q.A q.T0 q.T1 q.T2 q.E
      hp hn hex hW hpu hnu hs hy hzp hz
  · intro h k t hk p y zpen z A T0 T1 T2 E hp hn hex hW hpu hnu hs hy hzp hz
    exact h ⟨k, t, p, y, zpen, z, A, T0, T1, T2, E⟩
      ⟨hk, hp, hn, hex, hW, hpu, hnu, hs, hy, hzp, hz⟩

theorem actual_law : arena.Law actual := bridge.mp (@actualSource_threeNegative_exchange_full)

#print axioms bridge
#print axioms actual_law

end Reg.D5.S3.Combinatorics.Circle.ThreeNegativeExchange
