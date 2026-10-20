import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.MaskedCycles.StabilizerMaskedCycleRank
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Entanglement.MaskedCycles.StabilizerMaskedCycleRank
open _root_.D5.S3.Quantum.Entanglement.MaskedCycles.StabilizerMaskedCycleRank
open _root_.D5.S3.Combinatorics.Graph.Walks
open _root_.D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators Classical
open SimpleGraph Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u

abbrev signature : Signature where
  Params := Type u
  State V := Matrix V V F2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := Matrix V V F2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ Γ => Γ) (fun e => Empty.elim e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ Γ => fun i _ => Γ i i) (fun e => Empty.elim e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {n q : ℕ} [NeZero n] (ζ : Closure) (hζ : IsPrimitiveRoot ζ n)
    {V : Type u} [Fintype V] [DecidableEq V]
    (Γ : Matrix V V F2) (hs : Γ.IsSymm) (hd : ∀ u, Γ u u = 0)
    (col : V → Fin q) (t : Fin (q - 1) → ZMod n)
    (C : (maskedGraph Γ hs hd col t).ConnectedComponent) {k : ℕ}
    (z : cycleGraph (2 * (k + 2)) ≃g C.toSimpleGraph),
    (componentCircuit Γ hs hd col t C ((WeightedCycleWalk.parityIso k).trans z)).IsCycle ∧
    (componentCircuit Γ hs hd col t C ((WeightedCycleWalk.parityIso k).trans z)).length =
      2 * (k + 2) ∧
    (((weightedMatrix ζ (r.readout () V Γ) col t).submatrix
        (fun u : C => u.val) (fun u : C => u.val)).rank : ℤ) -
      (((mask Γ col t).submatrix (fun u : C => u.val) (fun u : C => u.val)).rank : ℤ) =
      if WeightedVertexProducts.alpha (edgeWeight ζ col t)
        (componentCircuit Γ hs hd col t C ((WeightedCycleWalk.parityIso k).trans z)) = 1 then 0 else 2

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  letI : NeZero (3 : F2) := ⟨by decide⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Closure 3
  let V := ULift.{u} (Fin 2 ⊕ Fin 2)
  let G : SimpleGraph V := (evenCycleGraph 0).comap ULift.down
  let Γ : Matrix V V F2 := G.adjMatrix F2
  have hs : Γ.IsSymm := G.isSymm_adjMatrix
  have hd : ∀ u, Γ u u = 0 := by intro u; simp [Γ]
  let col : V → Fin 2 := fun u => match u.down with | Sum.inl _ => 0 | Sum.inr _ => 1
  let t : Fin 1 → ZMod 3 := fun _ => 1
  let H := maskedGraph Γ hs hd col t
  have hH : H = G := by
    ext u v
    rcases u with ⟨u⟩
    rcases v with ⟨v⟩
    fin_cases u <;> fin_cases v <;>
      norm_num [H, maskedGraph, Γ, G, col, t, characterValue, delta, evenCycleGraph,
        SimpleGraph.adjMatrix_apply]
  let e₀ : evenCycleGraph 0 ≃g G := (SimpleGraph.Iso.comap Equiv.ulift (evenCycleGraph 0)).symm
  have hcE : (evenCycleGraph 0).Connected :=
    (WeightedCycleWalk.parityIso 0).connected_iff.mpr connected_cycleGraph_add_one
  have hc : H.Connected := hH.symm ▸ e₀.connected_iff.mp hcE
  let C := H.connectedComponentMk (⟨Sum.inl 0⟩ : V)
  have hmem (u : V) : u ∈ C := ConnectedComponent.sound (hc.preconnected u ⟨Sum.inl 0⟩)
  let inc : H ≃g C.toSimpleGraph := {
    toEquiv := {
      toFun u := ⟨u, hmem u⟩
      invFun u := u.val
      left_inv _ := rfl
      right_inv _ := rfl }
    map_rel_iff' := Iff.rfl }
  let eH : evenCycleGraph 0 ≃g H := hH.symm ▸ e₀
  let z : cycleGraph 4 ≃g C.toSimpleGraph :=
    (WeightedCycleWalk.parityIso 0).symm.trans (eH.trans inc)
  let l : V := ⟨Sum.inl 0⟩
  let r : V := ⟨Sum.inr 0⟩
  let B := (mask Γ col t).submatrix (fun u : C => u.val) (fun u : C => u.val)
  have hblocks : ¬ ∃ D ∈ (fibrePartition t).val, col l ∈ D ∧ col r ∈ D := by
    change ¬ ∃ D ∈ (partyPartition t).classes, col l ∈ D ∧ col r ∈ D
    rw [← Setoid.rel_iff_exists_classes]
    change ¬ (characterValue t (col l) = characterValue t (col r))
    decide
  have hentry : B (inc l) (inc r) = 1 := by
    change (if ∃ D ∈ (fibrePartition t).val, col l ∈ D ∧ col r ∈ D then 0 else Γ l r) = 1
    rw [if_neg hblocks]
    simp [Γ, G, l, r, evenCycleGraph]
  have hsmall : B.submatrix (fun _ : Fin 1 => inc l) (fun _ : Fin 1 => inc r) = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    exact hentry
  have hpos := Matrix.rank_submatrix_le B (fun _ : Fin 1 => inc l) (fun _ : Fin 1 => inc r)
  rw [hsmall, Matrix.rank_one, Fintype.card_fin] at hpos
  have hh := @h 3 2 inferInstance ζ hζ V inferInstance inferInstance Γ hs hd col t C 0 z
  have hdelta := hh.2.2
  have hz : rejected.readout () V Γ = 0 := by ext i j; exact hd i
  have hwz : weightedMatrix ζ (rejected.readout () V Γ) col t = 0 := by
    rw [hz]
    simp [weightedMatrix]
  simp only [hwz, Matrix.submatrix_zero, Pi.zero_apply, Matrix.rank_zero] at hdelta
  change (0 : ℤ) - (B.rank : ℤ) = _ at hdelta
  split_ifs at hdelta <;> omega

private theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro i
  refine ⟨ULift.{u} (Fin 2), 0, (fun i j => if i.down = j.down then 0 else 1), ?_⟩
  intro h
  have hh := congrArg (fun M : Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) F2 => M ⟨0⟩ ⟨1⟩) h
  change (0 : F2) = 1 at hh
  exact zero_ne_one hh

def source_registration : Registration arena.{u} (type_of% @component_rank_difference_alpha.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨component_rank_difference_alpha, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@component_rank_difference_alpha.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.MaskedCycles.StabilizerMaskedCycleRank.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.MaskedCycles.StabilizerMaskedCycleRank.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ Γ => Γ) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.MaskedCycles.StabilizerMaskedCycleRank
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "fn", "arg", "arg", "arg", "fn", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Quantum.Entanglement.MaskedCycles.StabilizerMaskedCycleRank
