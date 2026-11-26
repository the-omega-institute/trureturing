import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedRankTwoParity
import Mathlib.FieldTheory.Finiteness

/-! Exact negative degrees constrain which edge vectors the parity test must distinguish. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.checkUnivs false

open scoped Matrix
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedCycleRank
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedRankTwoParity

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedRankTwoParity

private abbrev degreeSignature.{u} : Signature.{u + 1, u, 0, u, 0} where
  Params := Σ V : Type u, Σ _ : Fintype V, Σ _ : DecidableEq V,
    Σ G : SimpleGraph V, DecidableRel G.Adj
  State p := p.2.2.2.1.edgeSet → ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual.{u} : Realization degreeSignature.{u} :=
  realize degreeSignature
    (fun _ p w => @negativeDegree _ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 w) Empty.elim

private def rejected.{u} : Realization degreeSignature.{u} :=
  realize degreeSignature (fun _ _ _ => 0) Empty.elim

private abbrev degreeArena.{u} : Arena where
  signature := degreeSignature.{u}
  Law R := ∀ {V : Type u} [vType : Fintype V] [vEq : DecidableEq V] (G : SimpleGraph V)
    [adj : DecidableRel G.Adj], G.IsBipartite →
    residualRank (incidence G) = 2 →
    ∀ (q : V → ℤ) (F w₀ : G.edgeSet → ZMod 2), negativeDegree G F = q →
    (incidence G).mulVecLin w₀ = (fun v => (q v : ZMod 2)) →
    F + w₀ ∉ LinearMap.range (incidence G)ᵀ.mulVecLin →
    ∃ ell : (G.edgeSet → ZMod 2) →ₗ[ZMod 2] ZMod 2,
      ∀ F', R.readout () ⟨V, vType, vEq, G, adj⟩ F' = q →
        (F' + w₀ ∈ LinearMap.range (incidence G)ᵀ.mulVecLin ↔ ell (F + F') = 1)

private def thetaEdges : Finset (Sym2 (Fin 6)) :=
  {s(0, 1), s(0, 2), s(2, 3), s(3, 1), s(0, 4), s(4, 5), s(5, 1)}

private def theta.{u} : SimpleGraph (ULift.{u} (Fin 6)) where
  Adj u v := s(u.down, v.down) ∈ thetaEdges
  symm := ⟨by
    intro a b h
    rw [Sym2.eq_swap (a := b.down) (b := a.down)]
    exact h⟩
  loopless := ⟨by decide⟩

private instance thetaAdjDecidable.{u} : DecidableRel theta.{u}.Adj :=
  fun u v => inferInstanceAs (Decidable (s(u.down, v.down) ∈ thetaEdges))

private theorem theta_bipartite.{u} : theta.{u}.IsBipartite := by
  let L : Set (ULift.{u} (Fin 6)) := fun v => v.down = 0 ∨ v.down = 3 ∨ v.down = 5
  let R : Set (ULift.{u} (Fin 6)) := fun v => v.down = 1 ∨ v.down = 2 ∨ v.down = 4
  apply SimpleGraph.isBipartite_iff_exists_isBipartiteWith.mpr
  refine ⟨L, R, ⟨Set.disjoint_left.mpr ?_, ?_⟩⟩
  · have h : ∀ v : ULift.{u} (Fin 6),
        (v.down = 0 ∨ v.down = 3 ∨ v.down = 5) →
          ¬ (v.down = 1 ∨ v.down = 2 ∨ v.down = 4) := by decide
    exact fun {_} => h _
  · let : DecidablePred (· ∈ L) :=
      fun v => inferInstanceAs (Decidable (v.down = 0 ∨ v.down = 3 ∨ v.down = 5))
    let : DecidablePred (· ∈ R) :=
      fun v => inferInstanceAs (Decidable (v.down = 1 ∨ v.down = 2 ∨ v.down = 4))
    have h : ∀ a b, theta.Adj a b → (a ∈ L ∧ b ∈ R) ∨ (a ∈ R ∧ b ∈ L) := by decide
    exact fun {_ _} => h _ _

private theorem rank_from_image {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (B : Matrix V E (ZMod 2)) (n : ℕ)
    (h : (Finset.univ.image B.mulVecLin).card = 2 ^ n) : B.rank = n := by
  let S := Finset.univ.image B.mulVecLin
  have hs : (S : Set (V → ZMod 2)) = LinearMap.range B.mulVecLin := by
    ext v
    simp [S, LinearMap.mem_range]
  let : Fintype (LinearMap.range B.mulVecLin) :=
    Fintype.ofEquiv S (Set.equivOfEq hs)
  have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.range B.mulVecLin)
  change Fintype.card (LinearMap.range B.mulVecLin) = 2 ^ B.rank at hc
  have hr : Fintype.card (LinearMap.range B.mulVecLin) = S.card := by
    rw [← Fintype.card_coe S]
    exact Fintype.card_congr (Set.equivOfEq hs).symm
  exact (Nat.pow_right_injective (by decide : 1 < 2)) (hc.symm.trans (hr.trans h))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem theta_rank.{u} : residualRank (incidence theta.{u}) = 2 := by
  have hi : (incidence theta.{u}).rank = 5 := rank_from_image _ _ (by decide)
  have hl : (incidence theta.{u} * (incidence theta.{u})ᵀ).rank = 5 :=
    rank_from_image _ _ (by decide)
  have hc : Fintype.card theta.{u}.edgeSet = 7 := by decide
  have h := residual_rank_add_twice_rank (incidence theta.{u})
  omega

private def square.{u} (i : Fin 6) (e : theta.{u}.edgeSet) : ZMod 2 :=
  if ∀ v ∈ e.val, v.down = 0 ∨ v.down = 1 ∨ v.down = i ∨ v.down = i + 1 then 1 else 0

private theorem rejected_law.{u} : ¬ degreeArena.{u}.Law rejected.{u} := by
  intro h
  let B := incidence theta.{u}
  let x := square.{u} 2
  let y := square.{u} 4
  have hx : B.mulVecLin x = 0 := by decide
  have hcut : ∀ z : ULift.{u} (Fin 6) → ZMod 2,
      Bᵀ.mulVecLin z ≠ x ∧ Bᵀ.mulVecLin z ≠ y ∧ Bᵀ.mulVecLin z ≠ x + y := by decide
  have outside (w : theta.{u}.edgeSet → ZMod 2)
      (hw : ∀ z, Bᵀ.mulVecLin z ≠ w) : w ∉ LinearMap.range Bᵀ.mulVecLin :=
    fun ⟨z, hz⟩ => hw z hz
  have hF : negativeDegree theta.{u} 0 = 0 := by decide
  obtain ⟨ell, test⟩ := h theta.{u} theta_bipartite theta_rank 0 0 x hF hx
    (by rw [zero_add]; exact outside x (fun z => (hcut z).1))
  have hx₁ : ell x = 1 := by
    have hxCut : x + x ∈ LinearMap.range Bᵀ.mulVecLin := by
      rw [ZModModule.add_self]
      exact Submodule.zero_mem _
    simpa using (test x rfl).mp hxCut
  have hy₀ : ell y = 0 := by
    have hn : y + x ∉ LinearMap.range Bᵀ.mulVecLin := by
      rw [add_comm]
      exact outside _ (fun z => (hcut z).2.2)
    have hh : ell y ≠ 1 := fun h => hn ((test y rfl).mpr (by simpa using h))
    exact (show ∀ a : ZMod 2, a ≠ 1 → a = 0 by decide) _ hh
  have hxy := (test (x + y) rfl).mpr (by simp [hx₁, hy₀])
  have hsum : x + y + x = y := by rw [add_comm x y, add_assoc, ZModModule.add_self, add_zero]
  rw [hsum] at hxy
  exact outside y (fun z => (hcut z).2.1) hxy

noncomputable def degreeEvidence.{u} :
    Registration degreeArena.{u} (type_of% (@exact_factor_switching_iff_parity.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_factor_switching_iff_parity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨rejected, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, rejected_law⟩
    · intro anchor
      exact nomatch anchor
  dependence := by
    rintro ⟨⟩
    refine ⟨⟨ULift.{u} (Fin 6), inferInstance, inferInstance, theta, inferInstance⟩,
      (fun _ => 0), (fun _ => 1), ?_⟩
    intro eqRows
    exact (by decide :
      negativeDegree theta.{u} (fun _ => 0) ⟨0⟩ ≠
        negativeDegree theta.{u} (fun _ => 1) ⟨0⟩) (congrFun eqRows ⟨0⟩)

noncomputable def degreeRegistration.{u} :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exact_factor_switching_iff_parity.{u}) (Realization degreeSignature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedRankTwoParity.exact_factor_switching_iff_parity.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedRankTwoParity.degreeEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨degreeArena.{u}⟩
  objectArena := .source ⟨degreeArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source degreeArena.{u} ⟨degreeEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize degreeSignature.{u}
    (fun _ p w => @negativeDegree _ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 w) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedRankTwoParity
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "body", "domain", "fn", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedRankTwoParity
