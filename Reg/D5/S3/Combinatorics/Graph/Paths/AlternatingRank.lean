import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Paths.AlternatingRank
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.Paths.AlternatingRank
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Combinatorics.Graph.Paths.AlternatingRank

attribute [local instance] Classical.propDecidable

abbrev alternatingSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

def alternatingActual : Realization alternatingSignature :=
  realize alternatingSignature (fun _ _ n => alternatingRank n) (fun e => nomatch e)

def alternatingRejected : Realization alternatingSignature :=
  realize alternatingSignature (fun _ _ _ => 0) (fun e => nomatch e)

def alternatingArena : Arena where
  signature := alternatingSignature
  Law R := ∀ n : ℕ, 0 < n → R.readout () () n = -2

private theorem alternating_rejected : ¬ alternatingArena.Law alternatingRejected := by
  intro h
  have := h 1 (by omega)
  norm_num [alternatingRejected, realize] at this

private theorem alternating_dependence :
    ObservationalDependence alternatingSignature alternatingActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change alternatingRank 0 ≠ alternatingRank 1
  rw [alternating_rank 1 (by omega)]
  simp [alternatingRank, adjacency]

def alternatingRegistration : Registration alternatingArena
    (∀ n : ℕ, 0 < n → alternatingRank n = -2) where
  actual := alternatingActual
  bridge := Iff.rfl
  variation := ⟨alternating_rank, alternatingRejected, alternating_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    alternatingArena.Law alternatingActual alternatingRejected alternating_rejected
  dependence := alternating_dependence

noncomputable def alternating_registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Graph.Paths.AlternatingRank.alternating_rank)
    (type_of% (realize alternatingSignature (fun _ _ n => alternatingRank n)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Paths.AlternatingRank.alternating_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Paths.AlternatingRank.alternatingRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨alternatingArena⟩
  objectArena := .source ⟨alternatingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source alternatingArena ⟨alternatingRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize alternatingSignature (fun _ _ n => alternatingRank n)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Paths.AlternatingRank
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev rankSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin n) (Fin n) (ZMod 2)) (fun _ => ℕ)

def rankActual : Realization rankSignature :=
  realize rankSignature (fun _ _ A => A.rank) (fun e => nomatch e)

def rankRejected : Realization rankSignature :=
  realize rankSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rank_dependence : ObservationalDependence rankSignature rankActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change Matrix.rank (0 : Matrix (Fin 1) (Fin 1) (ZMod 2)) ≠ Matrix.rank 1
  simp

abbrev pathRankSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) (fun _ => ℕ)

def pathRankActual : Realization pathRankSignature :=
  realize pathRankSignature (fun _ _ A => A.rank) (fun e => nomatch e)

def pathRankRejected : Realization pathRankSignature :=
  realize pathRankSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem pathRank_dependence :
    ObservationalDependence pathRankSignature pathRankActual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change Matrix.rank (0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) (ZMod 2)) ≠ Matrix.rank 1
  simp

universe u

def separatorArena : Arena where
  signature := pathRankSignature
  Law R := ∀ {α : Type u} [Finite α] (π : Setoid α), π ≠ ⊤ →
    ∃ (n : ℕ) (_ : 0 < n) (c : Fin (n + 1) → α), ∀ σ : Setoid α,
      (∑ w : Fin n → Bool,
        (-1 : ℤ) ^ (Finset.univ.filter (fun j => w j = true)).card *
          (R.readout () n (maskedAdjacency σ c (adjacency w)) : ℤ)) =
            if σ ≤ π then -2 else 0

private theorem separator_rejected : ¬ separatorArena.{u}.Law pathRankRejected := by
  intro h
  let π : Setoid (ULift.{u} (Fin 2)) := ⊥
  have hπ : π ≠ ⊤ := by
    intro he
    have hh := Setoid.eq_top_iff.mp he ⟨0⟩ ⟨1⟩
    change (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) = ULift.up 1 at hh
    have := congrArg ULift.down hh
    exact (by decide : (0 : Fin 2) ≠ 1) this
  obtain ⟨n, hn, c, hc⟩ := h π hπ
  have hh := hc π
  norm_num [pathRankRejected, realize] at hh

def separatorRegistration : Registration separatorArena.{u}
    (∀ {α : Type u} [Finite α] (π : Setoid α), π ≠ ⊤ →
      ∃ (n : ℕ) (_ : 0 < n) (c : Fin (n + 1) → α), ∀ σ : Setoid α,
        (∑ w : Fin n → Bool,
          (-1 : ℤ) ^ (Finset.univ.filter (fun j => w j = true)).card *
            (maskedAdjacency σ c (adjacency w)).rank) = if σ ≤ π then -2 else 0) where
  actual := pathRankActual
  bridge := Iff.rfl
  variation := ⟨path_separator, pathRankRejected, separator_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    separatorArena.Law pathRankActual pathRankRejected separator_rejected
  dependence := pathRank_dependence

def independenceArena : Arena where
  signature := rankSignature
  Law R := ∀ (q : ℕ), 2 ≤ q →
    ∀ (a : {P : Finpartition (Finset.univ : Finset (Fin q)) //
      P.parts.card = 2 ∨ P.parts.card = 3} → ℝ),
      (∀ (N : ℕ) (A : Matrix (Fin N) (Fin N) (ZMod 2)),
        A.IsSymm → (∀ j, A j j = 0) → ∀ c : Fin N → Fin q,
          ∑ P, a P * (R.readout () N (maskedAdjacency (Setoid.ker P.val.part) c A) : ℝ) = 0) →
      ∀ P, a P = 0

private theorem independence_rejected : ¬ independenceArena.Law rankRejected := by
  intro h
  have hz := h 2 (by omega) (fun _ => 1) (by
    intro N A hsym hdiag c
    simp [rankRejected, realize])
  let P : {P : Finpartition (Finset.univ : Finset (Fin 2)) //
      P.parts.card = 2 ∨ P.parts.card = 3} := ⟨⊥, Or.inl (by
        simp [Finpartition.parts_bot])⟩
  exact (by norm_num : (1 : ℝ) ≠ 0) (hz P)

set_option maxHeartbeats 600000 in
-- The theorem telescope contains the finite two- and three-block partition subtype.
def independenceRegistration : Registration independenceArena
    (∀ (q : ℕ), 2 ≤ q →
      ∀ (a : {P : Finpartition (Finset.univ : Finset (Fin q)) //
        P.parts.card = 2 ∨ P.parts.card = 3} → ℝ),
        (∀ (N : ℕ) (A : Matrix (Fin N) (Fin N) (ZMod 2)),
          A.IsSymm → (∀ j, A j j = 0) → ∀ c : Fin N → Fin q,
            ∑ P, a P * ((maskedAdjacency (Setoid.ker P.val.part) c A).rank : ℝ) = 0) →
        ∀ P, a P = 0) where
  actual := rankActual
  bridge := Iff.rfl
  variation := ⟨partition_rank_independent, rankRejected, independence_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    independenceArena.Law rankActual rankRejected independence_rejected
  dependence := rank_dependence

noncomputable def separator_registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Graph.Paths.AlternatingRank.path_separator.{u})
    (type_of% (realize pathRankSignature (fun _ _ A => A.rank)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Paths.AlternatingRank.separator_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Paths.AlternatingRank.separatorRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨separatorArena.{u}⟩
  objectArena := .source ⟨separatorArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source separatorArena.{u} ⟨separatorRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pathRankSignature (fun _ _ A => A.rank)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Paths.AlternatingRank
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "body", "body", "fn", "arg", "arg", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def independence_registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Graph.Paths.AlternatingRank.partition_rank_independent)
    (type_of% (realize rankSignature (fun _ _ A => A.rank)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Paths.AlternatingRank.independence_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Paths.AlternatingRank.independenceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨independenceArena⟩
  objectArena := .source ⟨independenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source independenceArena ⟨independenceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rankSignature (fun _ _ A => A.rank)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Paths.AlternatingRank
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "domain", "body", "body", "body", "body",
        "body", "fn", "arg", "arg", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.Graph.Paths.AlternatingRank
