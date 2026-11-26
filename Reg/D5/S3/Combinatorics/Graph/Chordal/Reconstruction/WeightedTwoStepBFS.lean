import D5.S3.Combinatorics.Graph.Chordal.Reconstruction.WeightedTwoStepBFS
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The residual along an edge as its second endpoint varies. -/

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.WeightedTwoStepBFS

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit SimpleGraph

noncomputable section

universe u

abbrev AnchorFamily {V : Type u} (G : SimpleGraph V) (r : V) :=
  (k : ℕ) → Component G r (k + 1) → V

abbrev Params := Σ V : Type u, Σ _ : Fintype V, Σ G : SimpleGraph V, Σ r : V,
  Σ _ : AnchorFamily G r, Σ _ : V → V → ℝ, Σ _ : V → V → ℝ, V

abbrev signature : Signature where
  Params := Params.{u}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def reader (p : Params.{u}) (v : p.1) : ℝ := by
  rcases p with ⟨V, inst, G, r, a, w, g, u⟩
  letI : Fintype V := inst
  let φ := twoStepBFSPotential G r a w g
  exact |g u v - (φ v - φ u)|

def actual : Realization signature.{u} :=
  realize signature (fun _ => reader) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 5) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [inst : Fintype V] {G : SimpleGraph V} (_hG : G.IsChordal)
    (_hc : G.Connected) {r : V} {a : AnchorFamily G r} {w g : V → V → ℝ}
    (_ha : ValidShadowAnchors G r a) (_hw : ValidPredecessorWeights G r w)
    (_hg : IsTriangleOneGain G g) {u v : V} (_huv : G.Adj u v),
    R.readout () ⟨V, inst, G, r, a, w, g, u⟩ v ≤ 4

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let V := ULift.{u} (Fin 2)
  let x : V := ⟨0⟩
  let y : V := ⟨1⟩
  let G := (⊤ : SimpleGraph V)
  have hxy : G.Adj x y := by
    change x ≠ y
    decide
  have hG : G.IsChordal := by
    intro z c hc hlen
    have hcard := hc.support_nodup.length_le_card
    have hs : Fintype.card V = 2 := by simp [V]
    rw [List.length_tail, c.length_support, hs] at hcard
    omega
  have hd (p q : V) : G.dist p q = if p = q then 0 else 1 := by
    by_cases he : p = q
    · subst q
      simp
    · exact (dist_eq_one_iff_adj.mpr he).trans (ite_eq_right he).symm
  have hc : G.Connected := by
    refine { preconnected := ?_, nonempty := ⟨x⟩ }
    intro p q
    by_cases he : p = q
    · subst q
      exact Reachable.rfl
    · exact (show G.Adj p q from he).reachable
  let a : AnchorFamily G x := fun _ _ => x
  have ha : ValidShadowAnchors G x a := by
    refine ⟨fun _ => rfl, fun k C => ?_⟩
    obtain ⟨z, _⟩ := C.nonempty_supp
    have hz := z.property
    change k + 2 ≤ G.dist x z.val at hz
    rw [hd] at hz
    split_ifs at hz <;> omega
  have hP (z b : V) : b ∈ bfsPred G x z ↔ b = x ∧ z ≠ x := by
    by_cases hz : z = x <;> by_cases hb : b = x <;>
      simp [bfsPred, CliqueBoundedBanach.predecessors, hd, hb, hz, G, Ne.symm]
  let w : V → V → ℝ := fun z b => if b = x ∧ z ≠ x then 1 else 0
  have hw : ValidPredecessorWeights G x w := by
    refine ⟨fun z b => by unfold w; split <;> norm_num,
      fun z b hb => ite_eq_right (fun he => hb ((hP z b).mpr he)), ?_⟩
    intro z hz
    have he : bfsPred G x z = {x} := by ext b; simp [hP, hz]
    rw [he, Finset.sum_singleton]
    simp [w, hz]
  have hg : IsTriangleOneGain G (fun _ _ => 0) := by
    simp [IsTriangleOneGain]
  have hbad := h hG hc ha hw hg hxy
  norm_num [rejected, realize] at hbad

private theorem changes_with_endpoint : ObservationalDependence signature.{u} actual := by
  classical
  intro _
  let V := ULift.{u} (Fin 2)
  let x : V := ⟨0⟩
  let y : V := ⟨1⟩
  let G := (⊥ : SimpleGraph V)
  let a : AnchorFamily G x := fun _ _ => x
  let g : V → V → ℝ := fun _ b => if b = y then 1 else 0
  let w : V → V → ℝ := fun _ _ => 0
  have he (b : V) : twoStepBFSPotential G x a w g b = 0 := by
    let d := G.dist x b
    have hz : d = 0 := by
      exact (dist_eq_zero_iff_eq_or_not_reachable).mpr
        (by by_cases hh : x = b; exact Or.inl hh; exact Or.inr (by simpa [G] using hh))
    have ht (k : ℕ) (hk : G.dist x b = k) :
        twoStepBFSPotential G x a w g b = potentialAt G x a w g b k hk := by
      subst k
      rfl
    exact ht 0 hz
  have hxy : x ≠ y := by decide
  refine ⟨⟨V, inferInstance, G, x, a, w, g, x⟩, x, y, ?_⟩
  change |g x x - (twoStepBFSPotential G x a w g x - twoStepBFSPotential G x a w g x)| ≠
    |g x y - (twoStepBFSPotential G x a w g y - twoStepBFSPotential G x a w g x)|
  norm_num [he, g, hxy]

def family : Registration arena.{u} (type_of% (@two_step_residual_bound.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@two_step_residual_bound.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := changes_with_endpoint

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@two_step_residual_bound.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `SimpleGraph.two_step_residual_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.WeightedTwoStepBFS.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.Reconstruction.WeightedTwoStepBFS
    definition := none
    coordinates := #[0, 2, 5, 6, 7, 8, 12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.WeightedTwoStepBFS
