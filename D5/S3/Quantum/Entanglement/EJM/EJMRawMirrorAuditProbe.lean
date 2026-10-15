/- Transient registration proof candidate, not compiled or delivered.
   The full positive-dimension and row-count telescope is preserved. All three
   actual readouts are original operands; no Boolean-only surrogate is used.
   Contract source-selection and producer binding evidence remain separate
   obligations. This file claims no declared_validated registration. -/

import D5.S3.Quantum.Entanglement.EJM.EJMLocalCacheData
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace EJMRawMirrorAuditProbe
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMLocalCacheData
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

private abbrev Params := {n : ℕ // 0 < n} × {N : ℕ // 0 < N}
private abbrev State := MirrorRow × RawRow
private abbrev Pair (p : Params) := Partial (Fin p.1.val) (Fin 4) × ℤ

private def leftPair (p : Params) (x : State) : Pair p :=
  (partialEvent x.1.hash, x.1.lower)

private def rightPair (p : Params) (x : State) : Pair p :=
  ((row p.1.property p.2.property x.2).assignment,
    (row p.1.property p.2.property x.2).lower)

private abbrev signature : Signature where
  Params := Params
  State _ := State
  Role := Option Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output role p := match role with
    | none => Bool
    | some _ => Pair p
  Anchor := Empty
  finiteAnchor := inferInstance

private def actualReadout : ∀ role p, State → signature.Output role p
  | none, _, x => checkRawMirror x.1 x.2
  | some false, p, x => leftPair p x
  | some true, p, x => rightPair p x

private def actual : Realization signature :=
  realize signature actualReadout (fun e => nomatch e)

private def badGuard : Realization signature :=
  realize signature
    (fun role p x => match role with
      | none => true
      | some b => actualReadout (some b) p x)
    (fun e => nomatch e)

private def badLeft : Realization signature :=
  realize signature
    (fun role p x => match role with
      | none => actualReadout none p x
      | some false => ((leftPair p x).1, (leftPair p x).2 + 1)
      | some true => actualReadout (some true) p x)
    (fun e => nomatch e)

private def badRight : Realization signature :=
  realize signature
    (fun role p x => match role with
      | none => actualReadout none p x
      | some false => actualReadout (some false) p x
      | some true => ((rightPair p x).1, (rightPair p x).2 + 1))
    (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ p x,
    R.readout none p x = true →
      R.readout (some false) p x = R.readout (some true) p x

private def sourceStatement : Prop :=
  ∀ {n N : ℕ} (hn : 0 < n) (hN : 0 < N) (mirror : MirrorRow) (raw : RawRow),
    checkRawMirror mirror raw = true →
      partialEvent (n := n) mirror.hash = (row hn hN raw).assignment ∧
      mirror.lower = (row hn hN raw).lower

private theorem bridge : sourceStatement ↔ arena.Law actual := by
  constructor
  · intro h p x accepted
    exact Prod.ext (h p.1.property p.2.property x.1 x.2 accepted).1
      (h p.1.property p.2.property x.1 x.2 accepted).2
  · intro h n N hn hN mirror raw accepted
    have he := h (⟨n, hn⟩, ⟨N, hN⟩) (mirror, raw) accepted
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

private def one : Params := (⟨1, by decide⟩, ⟨1, by decide⟩)
private def zero : State := (⟨0, 0, 0, 0⟩, .terminal 0 0)
private def wrongHash : State := (⟨1, 0, 0, 0⟩, .terminal 0 0)
private def wrongLeftLower : State := (⟨0, 1, 0, 0⟩, .terminal 0 0)
private def wrongRightLower : State := (⟨0, 0, 0, 0⟩, .terminal 0 1)

private theorem badGuard_law : ¬ arena.Law badGuard := by
  intro h
  have he := congrFun (congrArg Prod.fst (h one wrongHash rfl)) (0 : Fin 1)
  have hv := congrArg (Option.map Fin.val) he
  change some (1 : ℕ) = some 0 at hv
  simp at hv

private theorem badLeft_law : ¬ arena.Law badLeft := by
  intro h
  have he := congrArg Prod.snd (h one zero rfl)
  change (0 : ℤ) + 1 = 0 at he
  omega

private theorem badRight_law : ¬ arena.Law badRight := by
  intro h
  have he := congrArg Prod.snd (h one zero rfl)
  change (0 : ℤ) = 0 + 1 at he
  omega

private def registration : Registration arena sourceStatement where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @checked_raw_mirror_eq, badLeft, badLeft_law⟩
  sensitivity := by
    constructor
    · intro role
      cases role with
      | none =>
        refine ⟨badGuard, ?_, rfl, badGuard_law⟩
        intro other different
        cases other with
        | none => exact (different rfl).elim
        | some b => cases b <;> rfl
      | some b =>
        cases b with
        | false =>
          refine ⟨badLeft, ?_, rfl, badLeft_law⟩
          intro other different
          cases other with
          | none => rfl
          | some b =>
            cases b with
            | false => exact (different rfl).elim
            | true => rfl
        | true =>
          refine ⟨badRight, ?_, rfl, badRight_law⟩
          intro other different
          cases other with
          | none => rfl
          | some b =>
            cases b with
            | false => rfl
            | true => exact (different rfl).elim
    · intro e
      nomatch e
  dependence := by
    intro role
    cases role with
    | none =>
      refine ⟨one, zero, wrongHash, ?_⟩
      decide
    | some b =>
      cases b with
      | false =>
        refine ⟨one, zero, wrongLeftLower, ?_⟩
        intro he
        have hv := congrArg Prod.snd he
        change (0 : ℤ) = 1 at hv
        omega
      | true =>
        refine ⟨one, zero, wrongRightLower, ?_⟩
        intro he
        have hv := congrArg Prod.snd he
        change (0 : ℤ) = scale at hv
        norm_num [scale] at hv

#print axioms bridge
#print axioms registration
end EJMRawMirrorAuditProbe
