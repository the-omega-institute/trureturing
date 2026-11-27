import D5.S3.Combinatorics.Graph.Queries.WorldMixedForwardSuffix
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The joint probability bound tightens with the lower bound on fresh positions. -/

open LeanInformationAudit
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open _root_.D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw (Matches)
open _root_.D5.S3.Combinatorics.Graph.Queries.WorldMixedForwardSuffix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.Queries.WorldMixedForwardSuffix

noncomputable section
universe u v w

private abbrev signature : Signature where
  Params := Type u
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ _ n => suffixWeight n) (fun e => nomatch e)

private def zeroWeight : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {P : Type u} {V : Type v} {W : Type w} [Fintype P] [DecidableEq P]
    (π : PMF W) (choices : W → P → Bool → V)
    (_hChoice : ∀ w p, Function.Injective (choices w p))
    (earlier : P → Bool → Option V) (later : W → P → Bool → Option V)
    (seen : Finset P) (fresh : W → Finset P)
    (_hDisjoint : ∀ w, Disjoint seen (fresh w))
    (_hSeen : ∀ p, p ∈ seen ↔ ∃ b v, earlier p b = some v)
    (_hFresh : ∀ w p, p ∈ fresh w ↔ ∃ b v, later w p b = some v)
    (n : ℕ) (B : Set W) (_hLength : ∀ w ∈ B, n ≤ (fresh w).card),
    let Ω := P → Equiv.Perm Bool
    let table := uniformPmf Ω
    let μ : PMF (W × Ω) := π.bind fun w => table.map (Prod.mk w)
    let E : Set (W × Ω) := {x | Matches (choices x.1) earlier x.2}
    let F : Set (W × Ω) := {x | Matches (choices x.1) (later x.1) x.2}
    let weight := R.readout () P n
    μ.toOuterMeasure ((E ∩ Prod.fst ⁻¹' B) ∩ F) / μ.toOuterMeasure E ≤
      (μ.toOuterMeasure (E ∩ Prod.fst ⁻¹' B) / μ.toOuterMeasure E) * weight

private theorem zeroWeight_invalid : ¬ arena.{u,v,w}.Law zeroWeight := by
  classical
  intro h
  let P := ULift.{u} Empty
  let V := ULift.{v} Empty
  let W := ULift.{w} Unit
  let Ω := P → Equiv.Perm Bool
  let π : PMF W := PMF.pure ⟨()⟩
  let choices : W → P → Bool → V := fun _ p => isEmptyElim p
  let earlier : P → Bool → Option V := fun p => isEmptyElim p
  let later : W → P → Bool → Option V := fun _ => earlier
  let μ : PMF (W × Ω) := π.bind fun w => (uniformPmf Ω).map (Prod.mk w)
  let E : Set (W × Ω) := {x | Matches (choices x.1) earlier x.2}
  let F : Set (W × Ω) := {x | Matches (choices x.1) (later x.1) x.2}
  have hBad := h π choices (fun _ p => isEmptyElim p) earlier later ∅ (fun _ => ∅)
    (by simp) (fun p => isEmptyElim p) (fun _ p => isEmptyElim p)
    0 Set.univ (fun _ _ => Nat.zero_le _)
  change μ.toOuterMeasure ((E ∩ Prod.fst ⁻¹' Set.univ) ∩ F) / μ.toOuterMeasure E ≤
    (μ.toOuterMeasure (E ∩ Prod.fst ⁻¹' Set.univ) / μ.toOuterMeasure E) * 0 at hBad
  have hE : E = Set.univ := by
    ext x
    exact ⟨fun _ => trivial, fun _ p => isEmptyElim p⟩
  have hF : F = Set.univ := by
    ext x
    exact ⟨fun _ => trivial, fun _ p => isEmptyElim p⟩
  have hMass : μ.toOuterMeasure Set.univ = 1 :=
    (μ.toOuterMeasure_apply_eq_one_iff _).mpr (Set.subset_univ _)
  simp [hE, hF, hMass] at hBad

private theorem weight_varies :
    actual.{u}.readout () (ULift.{u} Unit) 0 ≠ actual.{u}.readout () (ULift.{u} Unit) 1 := by
  change suffixWeight 0 ≠ suffixWeight 1
  simp only [suffixWeight, pow_zero, pow_one, Nat.cast_one, Nat.cast_ofNat, inv_one]
  intro h
  have hinv := congrArg Inv.inv h
  norm_num at hinv

def evidence : Registration arena.{u,v,w} (type_of% (@joint_fresh_suffix_bound.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@joint_fresh_suffix_bound.{u,v,w}, zeroWeight, zeroWeight_invalid⟩
  sensitivity := ⟨fun i => ⟨zeroWeight, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, zeroWeight_invalid⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨ULift.{u} Unit, 0, 1, weight_varies.{u}⟩

def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@joint_fresh_suffix_bound.{u,v,w}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.WorldMixedForwardSuffix.joint_fresh_suffix_bound
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.WorldMixedForwardSuffix.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨evidence.{u,v,w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => suffixWeight n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.WorldMixedForwardSuffix
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Queries.WorldMixedForwardSuffix
