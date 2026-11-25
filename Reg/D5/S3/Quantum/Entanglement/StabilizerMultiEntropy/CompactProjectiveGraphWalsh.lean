import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Source-bound registration of the full-system Walsh law for the compact
projective graph family, with actual real orders as the state. -/
namespace Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators Classical

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (n : ℕ) → Finset (Fin (2^(n+1))) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ K => compactMomentFamily K) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K : ℝ), 1 < K →
    let observed := R.readout () () K
    (∀ n : ℕ, (∑ U : Finset (Fin (2^(n+1))), (-1:ℝ)^U.card * observed n U) =
      2 * ∏ j : Fin (n+1), (1 - (2:ℝ)^j.val / (2:ℝ)^(K-1))) ∧
    (∀ m : ℕ, (2:ℝ)^m < (2:ℝ)^(K-1) → (2:ℝ)^(K-1) < (2:ℝ)^(m+1) →
      (∑ U : Finset (Fin (2^(m+2))), (-1:ℝ)^U.card * observed (m+1) U) < 0)


private def total (g : signature.Output () ()) : ℝ :=
  ∑ U : Finset (Fin 4), (-1:ℝ)^U.card * g 1 U

private theorem total_two : total (compactMomentFamily 2) = 0 := by
  have e := (compact_projective_walsh 2 (by norm_num)).1 1
  change total (compactMomentFamily 2) = _ at e
  exact e.trans (by norm_num [Fin.prod_univ_succ, ← Nat.cast_ofNat (R := ℝ), Real.rpow_natCast])

private theorem total_three : total (compactMomentFamily 3) = 3/4 := by
  have e := (compact_projective_walsh 3 (by norm_num)).1 1
  change total (compactMomentFamily 3) = _ at e
  exact e.trans (by norm_num [Fin.prod_univ_succ, ← Nat.cast_ofNat (R := ℝ), Real.rpow_natCast])

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have e := (h 3 (by norm_num)).1 1
  change (∑ U : Finset (Fin (2^(1+1))), (-1:ℝ)^U.card * (0:ℝ)) = _ at e
  norm_num [Fin.prod_univ_succ, ← Nat.cast_ofNat (R := ℝ), Real.rpow_natCast] at e

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨(),2,3,?_⟩
  intro he
  have e : total (compactMomentFamily 2) = total (compactMomentFamily 3) := congrArg total he
  rw [total_two,total_three] at e
  norm_num at e

def source_registration : Registration arena (type_of% @compact_projective_walsh) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨compact_projective_walsh,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@compact_projective_walsh) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.compact_projective_walsh.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ K => compactMomentFamily K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh
