import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.CayleyColoring.NormalLimit

/-! The source variance depends on the actual recoloring count. -/

open Filter MeasureTheory ProbabilityTheory
open CayleyExactAudit CayleyReduction CayleyScheduler CayleyTreeProbability DiscardedOccupancy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped CayleyTreeProbability ProbabilityTheory Topology

namespace Reg.D5.S3.Combinatorics.Graph.CayleyColoring.NormalLimit

noncomputable section
universe u

abbrev Inputs :=
  Σ k : ℕ, Σ Palette : ℕ → Type u, Σ _ : (∀ N, ZMod k ↪ Palette N), ℕ

abbrev signature : Signature where
  Params := Inputs.{u}
  State p := SourceSample (p.2.2.2 + 1) p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => sourceCount (p.2.2.1 p.2.2.2) s) (fun e => nomatch e)

def zeroCount : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ (k : ℕ) (hk : 2 ≤ k) (Palette : ℕ → Type u)
    (embed : ∀ N, ZMod k ↪ Palette N)
    (_policy : ∀ (N : ℕ) (s : Colored (Fin (N + 1)) (ZMod k)),
      FreePolicy (K := Palette N) s.1.2.val),
    letI : NeZero k := ⟨by omega⟩
    (∀ᶠ N : ℕ in atTop,
      0 < Var[(fun s : SourceSample (N + 1) k =>
        (R.readout () ⟨k, Palette, embed, N⟩ s : ℝ)); sourceMeasure (N + 1) k]) ∧
    Tendsto (fun N => sourceStandardizedLaw (Nat.succ_pos N) hk (embed N)) atTop
      (𝓝 (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))

private def witnessPalette (_N : ℕ) : Type u := ULift.{u} ℕ

private def witnessEmbedding (_N : ℕ) : ZMod 2 ↪ witnessPalette.{u} _N where
  toFun x := ⟨x.val⟩
  inj' _ _ h := ZMod.val_injective 2 (congrArg ULift.down h)

private def witnessPolicy (N : ℕ) (s : Colored (Fin (N + 1)) (ZMod 2)) :
    FreePolicy (K := witnessPalette.{u} N) s.1.2.val := by
  intro _ color v _
  let used := (Finset.univ : Finset (Fin (N + 1))).sup fun w => (color w).down
  refine ⟨⟨used + 1⟩, fun w _ h => ?_⟩
  have bound : (color w).down ≤ used := Finset.le_sup (f := fun v => (color v).down) (Finset.mem_univ w)
  have eq := congrArg ULift.down h
  change used + 1 = (color w).down at eq
  omega

private theorem zeroCount_rejected : ¬ arena.{u}.Law zeroCount.{u} := by
  intro h
  have hp := (h 2 (by decide) witnessPalette.{u} witnessEmbedding.{u} witnessPolicy.{u}).1
  obtain ⟨N, hN⟩ := hp.exists
  have hzero :
      (fun s : SourceSample (N + 1) 2 =>
        (zeroCount.readout () ⟨2, witnessPalette.{u}, witnessEmbedding.{u}, N⟩ s : ℝ)) =
      (0 : SourceSample (N + 1) 2 → ℝ) := by
    funext s
    simp [zeroCount, realize]
  rw [hzero, variance_zero] at hN
  exact (lt_irrefl 0) hN

private theorem actual_depends : ObservationalDependence signature.{u} actual.{u} := by
  intro role
  cases role
  let p : Inputs.{u} := ⟨2, witnessPalette.{u}, witnessEmbedding.{u}, 1⟩
  refine ⟨p, ?_⟩
  by_contra! hconstant
  let : Nonempty (SourceSample 2 2) :=
    (Nat.card_ne_zero.mp (sample_spaces_positive (by decide : 2 ≤ 2) (0 : Fin 2)).1.ne').1
  let s : SourceSample 2 2 := Classical.choice inferInstance
  let : IsProbabilityMeasure (sourceMeasure 2 2) :=
    show IsProbabilityMeasure (uniform (SourceSample 2 2)) from inferInstance
  have hvar : 0 < Var[(fun t : SourceSample 2 2 =>
      (sourceCount (witnessEmbedding.{u} 1) t : ℝ)); sourceMeasure 2 2] := by
    rw [(source_moments (n := 2) (by decide) (by decide : 2 ≤ 2)
      (witnessEmbedding.{u} 1) (witnessPolicy.{u} 1)).2]
    exact literal_variance_positive (by decide : 2 ≤ 2) (by decide : 2 ≤ 2)
  have heq : (fun t : SourceSample 2 2 => (sourceCount (witnessEmbedding.{u} 1) t : ℝ)) =
      (fun _ => (sourceCount (witnessEmbedding.{u} 1) s : ℝ)) :=
    funext fun t => congrArg (fun z : ℕ => (z : ℝ)) (hconstant t s)
  rw [heq, ProbabilityTheory.variance, evariance] at hvar
  simp at hvar

def realization : Registration arena.{u} (type_of% (@colored_cayley_tree_clt.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@colored_cayley_tree_clt.{u}, zeroCount, zeroCount_rejected⟩
  sensitivity := by
    refine ⟨fun i => ⟨zeroCount, ?_, rfl, zeroCount_rejected⟩, fun a => nomatch a⟩
    intro j hij
    exact (hij (Subsingleton.elim (α := Unit) j i)).elim
  dependence := actual_depends

def countVarianceRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@colored_cayley_tree_clt.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `CayleyTreeProbability.colored_cayley_tree_clt.source_count
  realizationName := `Reg.D5.S3.Combinatorics.Graph.CayleyColoring.NormalLimit.realization
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨realization⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p s => sourceCount (p.2.2.1 p.2.2.2) s)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.CayleyColoring.NormalLimit
    definition := none
    coordinates := #[0, 2, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg",
        "body", "arg", "fn", "arg", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.CayleyColoring.NormalLimit
