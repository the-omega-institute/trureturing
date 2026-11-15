import D5.S1.Words.SubstitutionPrefixEnvelope
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S1.Words.SubstitutionPrefixEnvelope
open _root_.D5.S1.Words.RankOneMorphismIterationBound (image)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.SubstitutionPrefixEnvelope
universe u
namespace prefix_envelope

abbrev signature : Signature where
  Params := Σ α : Type u, Σ _w : α → ℤ, Σ _f : α → List α, ℕ × ℕ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p a => charge p.2.1 ((image p.2.2.1 p.2.2.2.1 a).take p.2.2.2.2))
  (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} (w : α → ℤ) (f : α → List α)
    (M : ℤ) (B : ℕ) (H : ℕ → ℤ) (_hM : 0 ≤ M)
    (_hw : ∀ a, |w a| ≤ M) (_hf : ∀ a, (f a).length ≤ B)
    (_hH : ∀ j, 0 ≤ H j) (_hb : ∀ j a, |charge w (image f j a)| ≤ H j),
    ∀ j a t, |R.readout () ⟨α, w, f, j, t⟩ a| ≤
      M + (B : ℤ) * ∑ i ∈ Finset.range j, H i

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hh := h (α := ULift.{u} Unit) (fun _ => 0) (fun _ => []) 0 0 (fun _ => 1)
    (by norm_num) (by intro a; norm_num) (by intro a; simp)
    (by intro j; norm_num)
    (by intro j a; cases j <;> simp [image, charge,
      _root_.D5.S1.Words.RankOneMorphismIterationBound.subst]) 0 ⟨()⟩ 0
  norm_num [rejected, realize] at hh

def family : Registration arena.{u}
    (type_of% (@_root_.D5.S1.Words.SubstitutionPrefixEnvelope.prefix_envelope.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.SubstitutionPrefixEnvelope.prefix_envelope,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro _
    let w : ULift.{u} Bool → ℤ := fun b => if b.down then 1 else 0
    refine ⟨⟨ULift.{u} Bool, w, (fun a => [a]), 0, 1⟩, ⟨false⟩, ⟨true⟩, ?_⟩
    change (0 : ℤ) ≠ 1
    norm_num

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.SubstitutionPrefixEnvelope.prefix_envelope.{u})
    (type_of% actual.{u}) Unit Unit := {
  unitName := `D5.S1.Words.SubstitutionPrefixEnvelope.prefix_envelope.__information_unit,
  realizationName := `Reg.D5.S1.Words.SubstitutionPrefixEnvelope.prefix_envelope.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.SubstitutionPrefixEnvelope,
    definition := none, coordinates := #[0, 1, 2, 11, 13],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 12,
      functionOperand := false, stateOperand := some #["arg", "arg", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end prefix_envelope

namespace two_block_interval_bound
abbrev signature : Signature where
  Params := Σ α : Type u, α → ℤ
  State p := List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p v => charge p.2 v) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} (w : α → ℤ) (f : α → List α)
    (M : ℤ) (B : ℕ) (H : ℕ → ℤ) (_hM : 0 ≤ M)
    (_hw : ∀ a, |w a| ≤ M) (_hf : ∀ a, (f a).length ≤ B)
    (_hH : ∀ j, 0 ≤ H j) (_hb : ∀ j a, |charge w (image f j a)| ≤ H j)
    (j : ℕ) (a b : α) (v : List α) (_hv : v <:+: image f j a ++ image f j b),
    |R.readout () ⟨α, w⟩ v| ≤ 4 * (M + (B : ℤ) * ∑ i ∈ Finset.range j, H i)

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hh := h (α := ULift.{u} Unit) (fun _ => 0) (fun _ => []) 0 0 (fun _ => 1)
    (by norm_num) (by intro a; norm_num) (by intro a; simp)
    (by intro j; norm_num)
    (by intro j a; cases j <;> simp [image, charge,
      _root_.D5.S1.Words.RankOneMorphismIterationBound.subst])
    0 ⟨()⟩ ⟨()⟩ [] (by simp)
  norm_num [rejected, realize] at hh

def family : Registration arena.{u}
    (type_of% (@_root_.D5.S1.Words.SubstitutionPrefixEnvelope.two_block_interval_bound.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.SubstitutionPrefixEnvelope.two_block_interval_bound,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro _
    refine ⟨⟨ULift.{u} Unit, (fun _ => 1)⟩, [], [⟨()⟩], ?_⟩
    change (0 : ℤ) ≠ 1
    norm_num

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.SubstitutionPrefixEnvelope.two_block_interval_bound.{u})
    (type_of% actual.{u}) Unit Unit := {
  unitName := `D5.S1.Words.SubstitutionPrefixEnvelope.two_block_interval_bound.__information_unit,
  realizationName := `Reg.D5.S1.Words.SubstitutionPrefixEnvelope.two_block_interval_bound.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.SubstitutionPrefixEnvelope,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 14,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end two_block_interval_bound
end Reg.D5.S1.Words.SubstitutionPrefixEnvelope
