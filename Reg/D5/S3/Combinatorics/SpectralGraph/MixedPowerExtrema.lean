import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema

namespace Reg.D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema

open _root_.D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema (result)
open _root_.D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation (graphPower)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open OmegaMath.MixedAdjacency OmegaMath.RealRayleigh SimpleGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

universe u

abbrev signature : Signature where
  Params := Σ V : Type u, Σ _ : Fintype V, Σ _ : DecidableEq V, Σ _ : ℕ, ℝ
  State p := SimpleGraph p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev observe (p : signature.{u}.Params) (G : SimpleGraph p.1) : ℝ :=
  @mixedTop p.1 p.2.1 p.2.2.1 (graphPower G p.2.2.2.1) p.2.2.2.2

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => (@Fintype.card p.1 p.2.1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} [f : Fintype V] [d : DecidableEq V] (G : SimpleGraph V),
    G.Connected → ∀ {k : ℕ}, 1 ≤ k → ∀ {α : ℝ}, 0 ≤ α → α < 1 →
    mixedTop (graphPower (pathGraph (Fintype.card V)) k) α ≤ mixedTop (graphPower G k) α ∧
    r.readout () ⟨V, f, d, k, α⟩ G ≤ (Fintype.card V : ℝ) - 1 ∧
    (mixedTop (graphPower G k) α = mixedTop (graphPower (pathGraph (Fintype.card V)) k) α ↔
      Fintype.card V ≤ k + 1 ∨ Nonempty (pathGraph (Fintype.card V) ≃g G)) ∧
    (mixedTop (graphPower G k) α = (Fintype.card V : ℝ) - 1 ↔ ∀ i j, G.dist i j ≤ k)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hle := (h (⊤ : SimpleGraph (ULift.{u} (Fin 1))) connected_top
    (k := 1) le_rfl (α := 0) le_rfl zero_lt_one).2.1
  change (Fintype.card (ULift.{u} (Fin 1)) : ℝ) ≤
    (Fintype.card (ULift.{u} (Fin 1)) : ℝ) - 1 at hle
  linarith

private theorem power_one {V : Type u} (G : SimpleGraph V) : graphPower G 1 = G := by
  ext i j
  change (i ≠ j ∧ G.edist i j ≤ (1 : ℕ∞)) ↔ G.Adj i j
  rw [edist_le_one_iff_adj_or_eq]
  exact ⟨fun ⟨hne, h⟩ => h.resolve_right hne, fun h => ⟨h.ne, Or.inl h⟩⟩

private theorem dependence : ∀ (i : Unit),
    ∃ p x y, (realize signature.{u} (fun _ => observe) (fun e => nomatch e)).readout i p x ≠
      (realize signature.{u} (fun _ => observe) (fun e => nomatch e)).readout i p y := by
  let V := ULift.{u} (Fin 2)
  intro i
  refine ⟨⟨V, inferInstance, inferInstance, 1, 0⟩, ⊥, ⊤, ?_⟩
  change mixedTop (graphPower (⊥ : SimpleGraph V) 1) 0 ≠
    mixedTop (graphPower (⊤ : SimpleGraph V) 1) 0
  rw [power_one, power_one]
  have botValue : mixedTop (⊥ : SimpleGraph V) 0 = 0 := by
    obtain ⟨x, _, hx, _⟩ := top_attained (mixedMatrix (⊥ : SimpleGraph V) 0)
    have zeroMatrix : mixedMatrix (⊥ : SimpleGraph V) 0 = 0 := by
      ext a b
      by_cases h : a = b <;> simp [mixedMatrix_apply, h]
    unfold mixedTop
    rw [← hx, zeroMatrix]
    simp [energy]
  rw [botValue]
  have topValue := (result (⊤ : SimpleGraph V) connected_top (k := 1) le_rfl
    (α := 0) le_rfl zero_lt_one).2.2.2.mpr (fun i j => by
      by_cases h : i = j
      · subst j
        simp
      · exact (dist_eq_one_iff_adj.mpr h).le)
  rw [power_one] at topValue
  rw [topValue]
  norm_num [V]

def sourceRegistration : Registration arena.{u} (type_of% @result.{u}) where
  actual := realize signature (fun _ => observe) (fun e => nomatch e)
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
      (@result.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema.unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨sourceRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ => observe) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema
    definition := none
    coordinates := #[0, 5, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.SpectralGraph.MixedPowerExtrema
