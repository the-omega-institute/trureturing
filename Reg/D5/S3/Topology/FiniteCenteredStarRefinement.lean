import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.FiniteCenteredStarRefinement

/-! The source-family proofs below do not supply a raw source-selection binding.
No completed four-slot registration is asserted. The missing source binding is
tracked at https://github.com/the-omega-institute/trureturing/issues/29762. -/

noncomputable section

namespace Reg.D5.S3.Topology.FiniteCenteredStarRefinement

open Set
open _root_.D5.S3.Topology.FiniteCenteredStarRefinement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u

structure Inputs where
  X : Type u
  topology : TopologicalSpace X
  compact : CompactSpace X
  hausdorff : T2Space X
  n : ℕ
  V : Fin n → Set X
  open_cover : ∀ j, IsOpen (V j)
  covers : ∀ x, ∃ j, x ∈ V j

attribute [instance] Inputs.topology Inputs.compact Inputs.hausdorff

def signature : Signature where
  Params := Inputs.{u}
  State P := P.X → Set P.X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.X → Set P.X
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ U => U) (fun e => nomatch e)

def erased : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ P : Inputs.{u}, ∃ (U : P.X → Set P.X) (s : Finset P.X),
    (∀ c, IsOpen (U c)) ∧ (∀ c, c ∈ R.readout () P U c) ∧
    (∀ x, ∃ c ∈ s, x ∈ U c) ∧
    ∀ c ∈ s, ∃ j, ∀ d ∈ s, (U c ∩ U d).Nonempty → U d ⊆ P.V j

abbrev source_scope := type_of% (@exists_finite_centered_star_refinement.{u})

theorem source_bridge : source_scope.{u} ↔ arena.{u}.Law actual := by
  constructor
  · intro h P
    exact @h P.X P.topology P.compact P.hausdorff P.n P.V P.open_cover P.covers
  · intro h X topology compact hausdorff n V hopen hcover
    exact h ⟨X, topology, compact, hausdorff, n, V, hopen, hcover⟩

theorem actual_positive : arena.{u}.Law actual :=
  source_bridge.mp (@exists_finite_centered_star_refinement.{u})

def testInput : Inputs.{u} where
  X := PUnit.{u+1}
  topology := inferInstance
  compact := inferInstance
  hausdorff := inferInstance
  n := 1
  V _ := univ
  open_cover _ := isOpen_univ
  covers x := ⟨0, mem_univ x⟩

theorem erased_fails : ¬ arena.{u}.Law erased := by
  intro h
  obtain ⟨U, s, hopen, hcenter, hcover, hstar⟩ := h testInput
  exact hcenter PUnit.unit

def family : Registration arena.{u} source_scope.{u} where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim (α := Unit) _ _))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨testInput, (fun _ => ∅), (fun _ => univ), ?_⟩
    change (fun _ : PUnit.{u+1} => (∅ : Set PUnit.{u+1})) ≠ (fun _ => univ)
    intro h
    exact Set.empty_ne_univ (congrFun h PUnit.unit)

end Reg.D5.S3.Topology.FiniteCenteredStarRefinement
