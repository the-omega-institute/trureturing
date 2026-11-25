import D5.S3.Combinatorics.Graph.Chordal.TwoStepBFSAndBarycenterObstructions
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Observing the exact tower profile as the layer varies at each width. -/

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.TwoStepBFSAndBarycenterObstructions

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support
open LeanInformationAudit SimpleGraph

noncomputable section

abbrev towerSignature := SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℝ)

def towerActual : Realization towerSignature :=
  realize towerSignature
    (fun _ m i => (2 * (m : ℝ) - 1) - (2 * (m : ℝ) - 2) * (((m : ℝ) - 1) / m) ^ i)
    (fun e => nomatch e)

def towerRejected : Realization towerSignature :=
  realize towerSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev towerArena : Arena where
  signature := towerSignature
  Law R :=
    (∀ m n : ℕ, 2 ≤ m → 1 ≤ n →
      (barycenterTower m n).IsChordal ∧ (barycenterTower m n).Connected ∧
      IsTriangleOneGain (barycenterTower m n) (barycenterGain m n) ∧
      (∃ φ, IsPureBFSBarycenter (barycenterTower m n) none (barycenterGain m n) φ) ∧
      ∀ i : Fin n, ∀ j : Fin m, (barycenterTower m n).dist none (some (i, j)) = i.val + 1 ∧
        ∀ φ, IsPureBFSBarycenter (barycenterTower m n) none (barycenterGain m n) φ →
          φ (some (i, j)) = if j.val = 0 then 0 else R.readout () m i.val) ∧
    ∀ M : ℝ, ∃ m n : ℕ, 2 ≤ m ∧ 1 ≤ n ∧
      (barycenterTower m n).IsChordal ∧ (barycenterTower m n).Connected ∧
      IsTriangleOneGain (barycenterTower m n) (barycenterGain m n) ∧
      ∃ u v, (barycenterTower m n).Adj u v ∧ ∀ φ,
        IsPureBFSBarycenter (barycenterTower m n) none (barycenterGain m n) φ →
          M < |barycenterGain m n u v - (φ v - φ u)|

private theorem tower_rejected_law : ¬ towerArena.Law towerRejected := by
  intro h
  have hactual := pure_predecessor_barycenter_unbounded.1 2 1 (by decide) (by decide)
  obtain ⟨φ, hφ⟩ := hactual.2.2.2.1
  have hv := (hactual.2.2.2.2 0 1).2 φ hφ
  have hb := ((h.1 2 1 (by decide) (by decide)).2.2.2.2 0 1).2 φ hφ
  norm_num [towerRejected, realize] at hv hb
  linarith

def towerFamily : Registration towerArena
    (type_of% (@pure_predecessor_barycenter_unbounded)) where
  actual := towerActual
  bridge := Iff.rfl
  variation := ⟨pure_predecessor_barycenter_unbounded, towerRejected, tower_rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity towerArena.Law towerActual towerRejected tower_rejected_law
  dependence := by
    intro _
    refine ⟨2, 0, 1, ?_⟩
    norm_num [towerActual, realize]


abbrev Vertices (m N : ℕ) := Fin N × GadgetVertex m
abbrev Roots (m N : ℕ) := Vertices m N → ℝ
abbrev Gain (m N : ℕ) := Vertices m N → Vertices m N → ℝ
abbrev Anchors (m N : ℕ) :=
  (r : Vertices m N) → (l : ℕ) → Component (bridgedGadget m N) r (l + 1) → Vertices m N

abbrev ResidualParameters :=
  Σ m : ℕ, Σ N : ℕ, Σ _ : Roots m N, Σ _ : Anchors m N,
    Σ _ : Vertices m N → Gain m N, Σ _ : Gain m N, Vertices m N

abbrev residualSignature :=
  SingleDependentReadout.signature ResidualParameters (fun p => Vertices p.1 p.2.1) (fun _ => ℝ)

def residualReader (p : ResidualParameters) (v : Vertices p.1 p.2.1) : ℝ := by
  rcases p with ⟨m, N, μ, a, w, g, u⟩
  let φ := fun x => ∑ r, μ r * twoStepBFSPotential (bridgedGadget m N) r (a r) (w r) g x
  exact |g u v - (φ v - φ u)|

def residualActual : Realization residualSignature :=
  realize residualSignature (fun _ => residualReader) (fun e => nomatch e)

def residualRejected : Realization residualSignature :=
  realize residualSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev residualArena : Arena where
  signature := residualSignature
  Law R :=
    ∀ m N : ℕ, 2 ≤ m → 2 ≤ N →
      let G := bridgedGadget m N
      G.IsChordal ∧ G.Connected ∧
      ∀ (μ : Roots m N), (∀ r, 0 ≤ μ r) → (∑ r, μ r = 1) →
        ∀ (a : Anchors m N) (w : Vertices m N → Gain m N),
          (∀ r, ValidShadowAnchors G r (a r)) → (∀ r, ValidPredecessorWeights G r (w r)) →
          ∃ g : Gain m N, IsTriangleOneGain G g ∧ ∃ u v, G.Adj u v ∧
            let _Φ := fun x => ∑ r, μ r * twoStepBFSPotential G r (a r) (w r) g x
            4 - 4 / (m : ℝ) - 8 / (N : ℝ) ≤ R.readout () ⟨m, N, μ, a, w, g, u⟩ v

private theorem choices {m N : ℕ} (hG : (bridgedGadget m N).IsChordal)
    (hc : (bridgedGadget m N).Connected) :
    ∃ (a : Anchors m N) (w : Vertices m N → Gain m N),
      (∀ r, ValidShadowAnchors (bridgedGadget m N) r (a r)) ∧
      (∀ r, ValidPredecessorWeights (bridgedGadget m N) r (w r)) := by
  classical
  let G := bridgedGadget m N
  choose anchor spec using fun (r : Vertices m N) (l : ℕ) (C : Component G r (l + 2)) =>
    exists_shadow_anchor hG hc C
  let a (r : Vertices m N) : (l : ℕ) → Component G r (l + 1) → Vertices m N
    | 0, _ => r
    | l + 1, C => anchor r l C
  let P (r u : Vertices m N) := @CliqueBoundedBanach.predecessors _ G r u _ (Classical.decPred _)
  let w (r u b : Vertices m N) := if b ∈ P r u then ((P r u).card : ℝ)⁻¹ else 0
  refine ⟨a, w, fun r => ⟨fun _ => rfl, spec r⟩, fun r => ⟨?_, ?_, ?_⟩⟩
  · intro u b
    dsimp [w]
    split <;> positivity
  · intro u b hb
    exact ite_eq_right hb
  · intro u hu
    change ∑ b ∈ P r u, w r u b = 1
    have hd : G.dist r u = (G.dist r u - 1) + 1 := by
      have hp : G.dist r u ≠ 0 := fun h => hu (hc.dist_eq_zero_iff.mp h).symm
      omega
    obtain ⟨b, hb, hbd⟩ := exists_predecessor hd
    have hm : b ∈ P r u := by
      unfold P CliqueBoundedBanach.predecessors
      exact (@Finset.mem_filter _ _ (Classical.decPred _) _ _).mpr
        ⟨Finset.mem_univ _, hb, by omega⟩
    rw [Finset.sum_congr rfl (fun b hb => show w r u b = _ from ite_eq_left hb),
      Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀]
    exact_mod_cast (Finset.card_ne_zero.mpr ⟨b, hm⟩)

private theorem residual_rejected_law : ¬ residualArena.Law residualRejected := by
  classical
  intro h
  have hh := h 4 4 (by decide) (by decide)
  obtain ⟨a, w, ha, hw⟩ := choices hh.1 hh.2.1
  let o : Vertices 4 4 := (0, .root)
  let μ : Roots 4 4 := fun r => if r = o then 1 else 0
  have hμ (r) : 0 ≤ μ r := by dsimp [μ]; split <;> norm_num
  obtain ⟨g, _, u, v, _, hbad⟩ := hh.2.2 μ hμ (by simp [μ]) a w ha hw
  norm_num [residualRejected, realize] at hbad

def residualFamily : Registration residualArena
    (type_of% (@twoStepBFS_root_averaging_lower_bound)) where
  actual := residualActual
  bridge := Iff.rfl
  variation := ⟨twoStepBFS_root_averaging_lower_bound, residualRejected, residual_rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity residualArena.Law
    residualActual residualRejected residual_rejected_law
  dependence := by
    classical
    intro _
    let u : Vertices 2 2 := (0, .root)
    let v : Vertices 2 2 := (1, .root)
    let g : Gain 2 2 := fun _ x => if x = v then 1 else 0
    refine ⟨⟨2, 2, fun _ => 0, fun r _ _ => r, fun _ _ _ => 0, g, u⟩, u, v, ?_⟩
    have h : u ≠ v := by decide
    norm_num [residualActual, residualReader, realize, g, h]

def towerAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pure_predecessor_barycenter_unbounded) (Realization towerSignature) Unit Unit where
  unitName := `SimpleGraph.pure_predecessor_barycenter_unbounded.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.TwoStepBFSAndBarycenterObstructions.towerFamily
  realizationSource := none
  generated := false
  arena := .source ⟨towerArena⟩
  objectArena := .source ⟨towerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source towerArena ⟨towerFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize towerSignature towerActual.readout towerActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.TwoStepBFSAndBarycenterObstructions
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "body", "body", "arg", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg","arg","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def residualAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@twoStepBFS_root_averaging_lower_bound) (Realization residualSignature) Unit Unit where
  unitName := `SimpleGraph.twoStepBFS_root_averaging_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.TwoStepBFSAndBarycenterObstructions.residualFamily
  realizationSource := none
  generated := false
  arena := .source ⟨residualArena⟩
  objectArena := .source ⟨residualArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source residualArena ⟨residualFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize residualSignature residualActual.readout residualActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.TwoStepBFSAndBarycenterObstructions
    definition := none
    coordinates := #[0,1,5,8,9,12,13]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "arg", "body", "arg", "body", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Chordal.TwoStepBFSAndBarycenterObstructions
