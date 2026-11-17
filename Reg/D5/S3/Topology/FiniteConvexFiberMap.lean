import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.FiniteConvexFiberMap

/-! The exact source-family proofs do not supply a raw source-selection binding.
No completed four-slot registration is asserted. The missing source binding is
tracked at https://github.com/the-omega-institute/trureturing/issues/29762. -/

noncomputable section

namespace Reg.D5.S3.Topology.FiniteConvexFiberMap

open Set
open _root_.D5.S3.Topology.FiniteConvexFiberMap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u v

structure Inputs where
  X : Type u
  E : Type v
  topology : TopologicalSpace X
  compact : CompactSpace X
  hausdorff : T2Space X
  normed : NormedAddCommGroup E
  scalar : NormedSpace ℝ E
  n : ℕ
  V : Fin n → Set X
  open_cover : ∀ j, IsOpen (V j)
  covers : ∀ x, ∃ j, x ∈ V j
  B : X → Set E
  N : Fin n → Set E
  K : Set E
  L : Set E
  R : Set E
  O : Set X
  convexK : Convex ℝ K
  convexL : Convex ℝ L
  convexN : ∀ j, Convex ℝ (N j)
  fiberK : ∀ x, B x ⊆ K
  fiberN : ∀ j x, x ∈ V j → B x ⊆ N j
  zeroN : ∀ j, (0 : E) ∉ N j
  forbidden : ∀ j, Disjoint (N j) R ∨ V j ⊆ O
  slice : L ∩ R ⊆ {0}
  a : X → E
  member : ∀ x, a x ∈ B x
  slice_member : ∀ x ∈ O, a x ∈ L

attribute [instance] Inputs.topology Inputs.compact Inputs.hausdorff Inputs.normed Inputs.scalar

abbrev signature : Signature where
  Params := Inputs.{u,v}
  State P := C(P.X, P.E)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := C(P.X, P.E)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ A => A) (fun e => nomatch e)

def erased : Realization signature.{u,v} :=
  realize signature (fun _ P _ => ContinuousMap.const P.X 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ P : Inputs.{u,v}, ∃ A : C(P.X, P.E),
    (∀ x, R.readout () P A x ∈ P.K) ∧ (∀ x, R.readout () P A x ∉ P.R) ∧
    ∀ x b, b ∈ P.B x → (0 : P.E) ∉ segment ℝ b (R.readout () P A x)

abbrev source_scope := type_of%
  (@_root_.D5.S3.Topology.FiniteConvexFiberMap.exists_continuous_ray_avoiding_fiber_map.{u,v})

theorem source_bridge : source_scope.{u,v} ↔ arena.{u,v}.Law actual := by
  constructor
  · intro h P
    exact @h P.X P.E P.topology P.compact P.hausdorff P.normed P.scalar
      P.n P.V P.open_cover P.covers P.B P.N P.K P.L P.R P.O
      P.convexK P.convexL P.convexN P.fiberK P.fiberN P.zeroN P.forbidden P.slice
      P.a P.member P.slice_member
  · intro h X E topology compact hausdorff normed scalar n V hopen hcover
      B N K L R O hK hL hN hBK hVN hzero hNR hLR a ha haL
    exact h ⟨X, E, topology, compact, hausdorff, normed, scalar, n, V, hopen, hcover,
      B, N, K, L, R, O, hK, hL, hN, hBK, hVN, hzero, hNR, hLR, a, ha, haL⟩

theorem actual_positive : arena.{u,v}.Law actual :=
  source_bridge.mp (@exists_continuous_ray_avoiding_fiber_map.{u,v})

def testInput : Inputs.{u,v} where
  X := PUnit.{u+1}
  E := ULift.{v} ℝ
  topology := inferInstance
  compact := inferInstance
  hausdorff := inferInstance
  normed := inferInstance
  scalar := inferInstance
  n := 1
  V _ := univ
  open_cover _ := isOpen_univ
  covers x := ⟨0, mem_univ x⟩
  B _ := {1}
  N _ := {1}
  K := {1}
  L := ∅
  R := {0}
  O := ∅
  convexK := convex_singleton _
  convexL := convex_empty
  convexN _ := convex_singleton _
  fiberK _ := Subset.rfl
  fiberN _ _ _ := Subset.rfl
  zeroN _ := by simp
  forbidden _ := Or.inl (by simp)
  slice := by simp
  a _ := 1
  member _ := rfl
  slice_member _ hx := False.elim hx

theorem erased_fails : ¬ arena.{u,v}.Law erased := by
  intro h
  obtain ⟨A, hK, hR, hsegments⟩ := h testInput
  exact hR PUnit.unit rfl

def family : Registration arena.{u,v} source_scope.{u,v} where
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
    refine ⟨testInput, ContinuousMap.const _ (0 : ULift.{v} ℝ),
      ContinuousMap.const _ (1 : ULift.{v} ℝ), ?_⟩
    intro h
    have hval := congrArg (fun f : C(PUnit.{u+1}, ULift.{v} ℝ) => f PUnit.unit) h
    exact zero_ne_one hval

end Reg.D5.S3.Topology.FiniteConvexFiberMap
