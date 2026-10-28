import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.TailGateDeficiency
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.ExpandingSourcePath
open _root_.D5.S3.Combinatorics.Circle.MixedSuffixEnergy
open _root_.D5.S3.Combinatorics.Circle.TwoOppositeLargeExchange
open _root_.D5.S3.Combinatorics.Circle.ThreeLargePacketExchange
open _root_.D5.S3.Combinatorics.Circle.TailGateDeficiency
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.Combinatorics.Circle.TailGateDeficiency

structure Input where
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

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => Input) (fun _ => ℤ × ℤ)

def observed (w : Input) : ℤ × ℤ :=
  let f := s w.k w.t
  let c1 := mass f (w.A ++ [hit w.k 2 w.p] ++ w.T0 ++ [w.y] ++ w.T1)
  let c2 := mass f (w.A ++ [hit w.k 2 w.p] ++ w.T0 ++ [w.y] ++ w.T1 ++ [w.zpen] ++ w.T2)
  (C w.k - c1 + mass (fun i => -f i) (signPool (fun i => -f i) w.T2 (C w.k + f w.zpen + 1)),
    C w.k - c2 + mass f (signPool f w.T2 (C w.k + f w.z + 1)))

def actual : Realization signature :=
  realize signature (fun _ _ w => observed w) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ w => let delta := -s w.k w.t w.y - s w.k w.t w.p;
    (delta, delta)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀
    (k t : ℕ) (hk : 3 ≤ k) (p y zpen z : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ smallWord T0 T1 T2 E, |s k t i| < Q k)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hyhigh : s k t p < -s k t y)
    (hminimum : ∀ V : List (Fin k), Legal k t V →
      J k t (oldWord p y zpen z A T0 T1 T2 E) ≤ J k t V),
    let o := R.readout () () ⟨k, t, p, y, zpen, z, A, T0, T1, T2, E⟩
    o.1 < -s k t y - s k t p ∨ o.2 < -s k t y - s k t p

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  simp only [arena, rejected, realize] at h

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro r
  cases r
  let w : Input := ⟨3, 1, 0, 0, 0, 0, [], [], [], [], []⟩
  refine ⟨(), w, { w with A := [0] }, ?_⟩
  decide

def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.TailGateDeficiency.actualSource_threeNegative_twoGate_tail_deficiency)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Circle.TailGateDeficiency.actualSource_threeNegative_twoGate_tail_deficiency,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.TailGateDeficiency.actualSource_threeNegative_twoGate_tail_deficiency)
    (type_of% (realize signature (fun _ _ w => observed w) (fun e => nomatch e)))
    (ℤ × ℤ) Unit := {
  unitName := `D5.S3.Combinatorics.Circle.TailGateDeficiency.actualSource_threeNegative_twoGate_tail_deficiency.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.TailGateDeficiency.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => observed w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Reg.D5.S3.Combinatorics.Circle.TailGateDeficiency
