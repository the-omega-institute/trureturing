import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fermionic.WeightedSlaterPairCut
import Reg.Support.DependentFamily

/-! The ordinary marginal purity as a readout of the endpoint amplitudes. -/

namespace Reg.D5.S3.Quantum.Fermionic.WeightedSlaterPairCut

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Fermionic
open LeanInformationAudit Matrix WeightedSlaterPairCut OrderedSlaterCut SlaterPairCutRank

universe u
noncomputable section

private abbrev Parameters :=
  Σ ι : Type u, Σ _ : LinearOrder ι, Σ _ : Fintype ι, Σ m : ℕ, Σ n : ℕ,
    Σ I : Set ι, Σ _ : (Fin m × Bool) ↪ I, (Fin n × Bool) ↪ ↥(Iᶜ)

private abbrev signature : Signature where
  Params := Parameters.{u}
  State c := Fin (c.2.2.2.1 + c.2.2.2.2.1) → Bool → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

open Classical in
private def observe (c : Parameters.{u}) : signature.State c → ℂ :=
  match c with
  | ⟨_ι, _order, _finite, _m, _n, I, p, q⟩ => fun weight =>
    let B := orderedCut I (cutPairOrbitals p q weight)
    ((B * Bᴴ) ^ 2).trace

private def actual : Realization signature.{u} :=
  realize signature (fun _ => observe) (fun e => nomatch e)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [order : LinearOrder ι] [finite : Fintype ι]
      {m n : ℕ} {I : Set ι} (p : (Fin m × Bool) ↪ I) (q : (Fin n × Bool) ↪ ↥(Iᶜ)),
    ∀ (_hp : ∀ i, (p (i, false) : ι) < p (i, true))
      (_hq : ∀ j, (q (j, false) : ι) < q (j, true)) (weight : Fin (m + n) → Bool → ℂ),
    let A := alternationMatrix (fun i e => (p (i, e) : ι)) (fun j e => (q (j, e) : ι))
    let _B := orderedCut I (cutPairOrbitals p q weight)
    let leftMass (i : Fin m) (v : ZMod 2) :=
      weight (Fin.castAdd n i) (pickEndpoint v) * star (weight (Fin.castAdd n i) (pickEndpoint v))
    let rightMass (j : Fin n) (v : ZMod 2) :=
      weight (Fin.natAdd m j) (pickEndpoint v) * star (weight (Fin.natAdd m j) (pickEndpoint v))
    R.readout () ⟨ι, order, finite, m, n, I, p, q⟩ weight =
      ∑ z : Fin m → ZMod 2,
        (∏ i, ∑ v : ZMod 2, leftMass i v * leftMass i (v + z i)) *
          (∏ j, ∑ v : ZMod 2, rightMass j v * binarySign ((Aᵀ *ᵥ z) j * v)) ^ 2

private abbrev Sites := ULift.{u} (Fin 2)

private def leftPair : (Fin 1 × Bool) ↪ (Set.univ : Set Sites.{u}) where
  toFun i := ⟨⟨if i.2 then 1 else 0⟩, Set.mem_univ _⟩
  inj' := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hij : i = j := Subsingleton.elim _ _
    subst j
    have hsites := congrArg (fun v : (Set.univ : Set Sites.{u}) => v.val.down) h
    cases a <;> cases b <;> simp at hsites ⊢

private def rightPair : (Fin 0 × Bool) ↪ ↥((Set.univ : Set Sites.{u})ᶜ) where
  toFun i := i.1.elim0
  inj' i := i.1.elim0

private abbrev exampleParameters : Parameters.{u} :=
  ⟨Sites, inferInstance, inferInstance, 1, 0, Set.univ, leftPair, rightPair⟩

private theorem leftPair_ordered (i : Fin 1) :
    (leftPair.{u} (i, false) : Sites.{u}) < leftPair (i, true) := by
  have hi : i = 0 := Subsingleton.elim _ _
  rw [hi]
  decide

private theorem evaluated_one :
    actual.{u}.readout () exampleParameters (fun _ _ => 1) = 4 := by
  have h := orderedMarginal_purity leftPair.{u} rightPair leftPair_ordered
    (fun j => j.elim0) (fun _ _ => 1)
  change actual.{u}.readout () exampleParameters (fun _ _ => 1) = _ at h
  rw [h]
  norm_num [Fintype.card_fun, ZMod.card]

private theorem evaluated_zero :
    actual.{u}.readout () exampleParameters (fun _ _ => 0) = 0 := by
  have h := orderedMarginal_purity leftPair.{u} rightPair leftPair_ordered
    (fun j => j.elim0) (fun _ _ => 0)
  change actual.{u}.readout () exampleParameters (fun _ _ => 0) = _ at h
  rw [h]
  simp

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hbad := h leftPair.{u} rightPair leftPair_ordered (fun j => j.elim0) (fun _ _ => 1)
  norm_num [rejected, realize, Fintype.card_fun, ZMod.card] at hbad

def evidence : Registration arena.{u} (type_of% @orderedMarginal_purity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@orderedMarginal_purity.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨exampleParameters, fun _ _ => 0, fun _ _ => 1, by
    rw [evaluated_zero, evaluated_one]
    norm_num⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@orderedMarginal_purity.{u}) (Realization signature.{u}) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Fermionic.WeightedSlaterPairCut.orderedMarginal_purity
  realizationName := `Reg.D5.S3.Quantum.Fermionic.WeightedSlaterPairCut.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ => observe) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.WeightedSlaterPairCut
    definition := none
    coordinates := #[0, 3, 4, 5, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Fermionic.WeightedSlaterPairCut
