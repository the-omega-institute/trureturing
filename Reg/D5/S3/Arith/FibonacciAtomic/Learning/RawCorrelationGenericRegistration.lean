import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Arith.FibonacciAtomic
open D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities
open Law Filter LeanInformationAudit
open LiteralWindowEnd (Window first last)
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
local notation "sign" => (fun b : Bool => D5.S3.Arith.GoldenPell.signedInt (!b) 1)
namespace Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities

namespace ActiveFairTie
abbrev signature : Signature where
  Params := Unit
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ j => Binomial.fairTie j) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def sourceStatement.{u} : Prop := ∀ {α : Type u} [Fintype α] (a : α → Bool),
    (∑ u : α → Bool, if (∑ i, if a i then sign (u i) else 0) = 0 then
      (1 / 2 : ℝ) ^ (Fintype.card α) else 0) =
      Binomial.fairTie (Fintype.card {i : α // a i = true})
def arena.{u} : Arena where
  signature := signature
  Law R := ∀ {α : Type u} [Fintype α] (a : α → Bool),
    (∑ u : α → Bool, if (∑ i, if a i then sign (u i) else 0) = 0 then
      (1 / 2 : ℝ) ^ (Fintype.card α) else 0) =
      R.readout () () (Fintype.card {i : α // a i = true})

private theorem rejected_law.{u} : ¬ arena.{u}.Law rejected := by
  intro h
  let a : ULift.{u} (Fin 0) → Bool := fun x => Fin.elim0 x.down
  have hb := h a
  have hg := ActiveFair.active_fair_tie a
  change _ = (0 : ℝ) at hb
  rw [hg] at hb
  norm_num [Binomial.fairTie, a] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  norm_num [actual, realize, Binomial.fairTie]

def proof_record.{u} : Registration arena.{u} sourceStatement.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.ActiveFair.active_fair_tie.{u}, rejected, rejected_law.{u}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law.{u}⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit.{u} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.ActiveFair.active_fair_tie.{u})
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ j => Binomial.fairTie j) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.ActiveFair.active_fair_tie.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.ActiveFairTie.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨proof_record.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ j => Binomial.fairTie j) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[], readouts := #[{
      path := #["body","body","body","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end ActiveFairTie

namespace ProductPushforward
abbrev signature.{v} : Signature where
  Params := Σ β : Type v, Σ m : ℕ, Fin m → β
  State p := (Fin p.2.1 → p.1) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{v} : Realization signature.{v} :=
  realize signature.{v} (fun _ p F => F p.2.2) (fun e => nomatch e)
def rejected.{v} : Realization signature.{v} :=
  realize signature.{v} (fun _ p F => F p.2.2 + 1) (fun e => nomatch e)

def sourceStatement.{u,v} : Prop := ∀ {α : Type u} {β : Type v} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (p : α → ℝ) (q : β → ℝ)
    (hq : ∀ b, q b = ∑ a, if f a = b then p a else 0)
    (m : ℕ) (F : (Fin m → β) → ℝ),
    (∑ x : Fin m → α, F (fun i => f (x i)) * ∏ i, p (x i)) =
      ∑ y : Fin m → β, F y * ∏ i, q (y i)
def arena.{u,v} : Arena where
  signature := signature.{v}
  Law R := ∀ {α : Type u} {β : Type v} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (p : α → ℝ) (q : β → ℝ)
    (hq : ∀ b, q b = ∑ a, if f a = b then p a else 0)
    (m : ℕ) (F : (Fin m → β) → ℝ),
    (∑ x : Fin m → α, F (fun i => f (x i)) * ∏ i, p (x i)) =
      ∑ y : Fin m → β, R.readout () ⟨β,m,y⟩ F * ∏ i, q (y i)

private theorem rejected_law.{u,v} : ¬ arena.{u,v}.Law rejected.{v} := by
  intro h
  let α := ULift.{u} Unit
  let β := ULift.{v} Unit
  have hb := h (α := α) (β := β) (fun _ => ⟨()⟩) (fun _ => 1) (fun _ => 1)
    (by intro b; simp [α]) 0 (fun _ => 0)
  norm_num [rejected, realize, α, β] at hb

private theorem dependence.{v} : ObservationalDependence signature.{v} actual := by
  intro i
  let p : Σ β : Type v, Σ m : ℕ, Fin m → β := ⟨ULift.{v} Unit,0,fun j => Fin.elim0 j⟩
  refine ⟨p,(fun _ => 0),(fun _ => 1),?_⟩
  norm_num [actual, realize]

def proof_record.{u,v} : Registration arena.{u,v} sourceStatement.{u,v} where
  actual := actual.{v}
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Pushforward.product_pushforward.{u,v}, rejected.{v}, rejected_law.{u,v}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{v}, ?_, rfl, rejected_law.{u,v}⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit.{u,v} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Pushforward.product_pushforward.{u,v})
    (type_of% (realize.{v+1,v,0,0,0} signature.{v} (fun _ p F => F p.2.2) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Pushforward.product_pushforward.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.ProductPushforward.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u,v}⟩, objectArena := .source ⟨arena.{u,v}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u,v} ⟨proof_record.{u,v}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{v+1,v,0,0,0} signature.{v} (fun _ p F => F p.2.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[1,9,11], readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","arg","arg","body","fn","arg"],
      stateBinder := 10, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end ProductPushforward

namespace ExpectationVanishes
open FiniteTail
abbrev signature : Signature where
  Params := ℕ → ℝ
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ f j => f j) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def sourceStatement.{u,v} : Prop := ∀ {α : Type u} {ι : Type v} [Fintype α] (l : Filter ι)
    (q : ι → α → ℝ) (b : α → ℕ) (n : ι → ℕ) (f : ℕ → ℝ)
    (hq : ∀ᶠ t in l, ∀ a, 0 ≤ q t a) (hprob : ∀ᶠ t in l, ∑ a, q t a = 1)
    (hf0 : ∀ j, 0 ≤ f j) (hf1 : ∀ j, f j ≤ 1)
    (hf : Tendsto f atTop (𝓝 0))
    (htails : ∀ N, Tendsto (fun t => tail (q t) b (n t) N) l (𝓝 0)),
    Tendsto (fun t => expectation (q t) b (n t) f) l (𝓝 0)
def arena.{u,v} : Arena where
  signature := signature
  Law R := ∀ {α : Type u} {ι : Type v} [Fintype α] (l : Filter ι)
    (q : ι → α → ℝ) (b : α → ℕ) (n : ι → ℕ) (f : ℕ → ℝ)
    (hq : ∀ᶠ t in l, ∀ a, 0 ≤ q t a) (hprob : ∀ᶠ t in l, ∑ a, q t a = 1)
    (hf0 : ∀ j, 0 ≤ f j) (hf1 : ∀ j, f j ≤ 1)
    (hf : Tendsto (R.readout () f) atTop (𝓝 0))
    (htails : ∀ N, Tendsto (fun t => tail (q t) b (n t) N) l (𝓝 0)),
    Tendsto (fun t => expectation (q t) b (n t) f) l (𝓝 0)

private theorem rejected_law.{u,v} : ¬ arena.{u,v}.Law rejected := by
  intro h
  let α := ULift.{u} Unit
  let ι := ULift.{v} ℕ
  let l : Filter ι := Filter.map ULift.up atTop
  have hb := h (α := α) l (fun _ _ => 1) (fun _ => 1)
    (fun t => t.down) (fun _ => 1)
    (Filter.Eventually.of_forall (by intros; norm_num))
    (Filter.Eventually.of_forall (by intro t; simp [α]))
    (by intros; norm_num) (by intros; norm_num)
    (by exact tendsto_const_nhds)
    (by
      intro N
      apply tendsto_map'_iff.mpr
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop N] with t ht
      simp [FiniteTail.tail, FiniteTail.count, α, Nat.not_le_of_gt ht])
  have hb' := tendsto_map'_iff.mp hb
  have hz : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, FiniteTail.expectation, α] using hb'
  have heq : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hz
  norm_num at heq

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(fun j => (j : ℝ)),0,1,?_⟩
  norm_num [actual, realize]

def proof_record.{u,v} : Registration arena.{u,v} sourceStatement.{u,v} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.FiniteTail.expectation_vanishes.{u,v}, rejected, rejected_law.{u,v}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law.{u,v}⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit.{u,v} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.FiniteTail.expectation_vanishes.{u,v})
    (type_of% (realize.{0,0,0,0,0} signature (fun _ f j => f j) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.FiniteTail.expectation_vanishes.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.ExpectationVanishes.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u,v}⟩, objectArena := .source ⟨arena.{u,v}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u,v} ⟨proof_record.{u,v}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ f j => f j) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[7], readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","domain","fn","fn","arg"],
      stateBinder := 0, functionOperand := true,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end ExpectationVanishes

end Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities
