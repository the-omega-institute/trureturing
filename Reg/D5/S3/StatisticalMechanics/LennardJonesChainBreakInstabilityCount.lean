import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount
import Reg.Support.DependentFamily

/-! Source-bound audit of the broken-bond count in the clamped-chain inertia bounds. -/

namespace Reg.D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount

open _root_.D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe how many bonds exceed the inflection length as the displacement varies. -/
abbrev signature : Signature where
  Params := Σ _m : ℕ, ℝ
  State p := Fin (p.1 + 2) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p u =>
    (Finset.univ.filter (fun j => inflectionPoint < bondLength p.2 u j)).card)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => p.1 + 2) (fun e => nomatch e)

/-- Keep the full source telescope and both bounds on the positive spectrum. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (m : ℕ), 1 ≤ m → ∀ (d : ℝ), 0 < d →
    ∀ (u : Fin (m + 2) → ℝ), u 0 = 0 → u (Fin.last _) = 0 →
      (∀ n, force d u n = 0) → (∀ j, 0 < bondLength d u j) →
        ∀ k : ℕ, 1 ≤ k → r.readout () ⟨m, d⟩ u = k →
          ∀ h : (jacobian d u).IsHermitian,
            k - 1 ≤ (Finset.univ.filter (fun i => 0 < h.eigenvalues i)).card ∧
              (Finset.univ.filter (fun i => 0 < h.eigenvalues i)).card ≤ k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh : (jacobian (m := 1) 1 (fun _ => 0)).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [Subsingleton.elim j i, star_trivial]
  have hbad := h 1 (by norm_num) 1 (by norm_num) (fun _ => 0) rfl rfl
    (by intro n; simp [force, bondLength])
    (by intro j; norm_num [bondLength]) 3 (by norm_num) rfl hh
  have hcard := Finset.card_le_card
    (Finset.filter_subset (fun i => 0 < hh.eigenvalues i) Finset.univ)
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  have hlower := hbad.1
  norm_num at hlower
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, inflectionPoint + 1⟩, (fun _ => 0),
    (fun j => if j = 0 then inflectionPoint + 1 else 0), ?_⟩
  have hinf : 0 ≤ inflectionPoint := Real.rpow_nonneg (by norm_num) _
  have hlt : inflectionPoint < inflectionPoint + 1 := by linarith
  have hnlt : ¬ inflectionPoint < 0 := not_lt.mpr hinf
  have hj : ∀ j : Fin 1, j = 0 := fun j => Subsingleton.elim j 0
  norm_num [actual, realize, bondLength, Finset.univ_unique, hlt, hnlt, hj]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p u =>
    (Finset.univ.filter (fun j => inflectionPoint < bondLength p.2 u j)).card)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount
    definition := some {
      owner := `D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount
      name := `D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.claim
      path := #[] }
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "domain", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount
