/- GID: D5/S3/Topology/FiniteMatchingAssociativity
   generality: I
   mirror-B: D5/B/S3/Topology/FiniteMatchingAssociativity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: Matching composition and its internal circle exponent are associative. -/

/-
admission_basis: open-problem-resolution (#27843; Refuted)
escape_witness: none (the settlement of the external open problem is the new content)
Qualified-name abbreviations:
PlanarDiagramAlgebra = D5.S3.Combinatorics.PerfectMatchings.PlanarDiagramAlgebra
BrauerZeroMonoid = D5.S3.Topology.BrauerZeroMonoid
FiniteMatchingAssociativity = D5.S3.Topology.FiniteMatchingAssociativity
adjoinUnmarked = D5.S3.Topology.FiniteMatchingAssociativity.adjoinUnmarked
attachedTripleEquiv = D5.S3.Topology.FiniteMatchingAssociativity.attachedTripleEquiv
disjointComponents = D5.S3.Topology.FiniteMatchingAssociativity.disjointComponents
rotateTripleEquiv = D5.S3.Topology.FiniteMatchingAssociativity.rotateTripleEquiv
sumClosedEquiv = D5.S3.Topology.FiniteMatchingAssociativity.sumClosedEquiv
tripleInventory = D5.S3.Topology.FiniteMatchingAssociativity.tripleInventory

Direct frozen dependencies (declaration statement_ids):
D5/S3/Topology/FiniteMatchingClosure.Boundary
  sha256:2d22740b62cc9ff6a486d404f032436c21abd62130e080eb9e91719ecefa9bc6
D5/S3/Topology/FiniteMatchingClosure.Component
  sha256:5642ad6195d55697fcc1797d055319337e1d732d175cb3aea76182cc0cdf9f7c
D5/S3/Topology/FiniteMatchingClosure.GluingVertex
  sha256:2873fa2a1f75c9adf399c1499e565f4decd91b7e781101ccf50953cc74270d38
D5/S3/Topology/FiniteMatchingClosure.Matching
  sha256:fd9df4ba1fc572f200a8c9ff58f36e53a205ade28d7c790a87120a8723a6cdb9
D5/S3/Topology/FiniteMatchingClosure.casesOn
  sha256:4831315c0e2a5353509695daf5258e46eac0327c012f220fe76b8c79b52d039c
D5/S3/Topology/FiniteMatchingClosure.component
  sha256:c03bf702b492a3e83913d14d733d79ae45b49e152d146fa6b487bd400bdef2fc
D5/S3/Topology/FiniteMatchingClosure.contractionEquiv
  sha256:b9724ea28e62cb3a74b5c6f3bb144d6e06ebf94bf52e5e306136a4e4ab8793d1
D5/S3/Topology/FiniteMatchingClosure.fixedPointFree
  sha256:7e2300a12c5c75ab082a687677905e6360d7f3c6ba04162ecd59d5c5f03f894e
D5/S3/Topology/FiniteMatchingClosure.gluingStep
  sha256:5f0c850b2826e9242805007733c91dcd594d0043ee187d56bbf311ea6dca3dbe
D5/S3/Topology/FiniteMatchingClosure.identityMatching
  sha256:4e81ed32fda7d78d7b0879b1359e8b4456fd02d02a1bddfc3866467d3101eef3
D5/S3/Topology/FiniteMatchingClosure.involutive
  sha256:153fd34f58fbe013110af6f5ce1b505d74a30fa7da480f91bb0275be04b78417
D5/S3/Topology/FiniteMatchingClosure.lower
  sha256:8232a839f72e7adde0adb94de8ecb0a05332d55fecb1c39297fdf1004bfe385c
D5/S3/Topology/FiniteMatchingClosure.mate
  sha256:28b6db6a4ff9477dd543699cd3439ba967d854c089c412870c9eb135520ccf46
D5/S3/Topology/FiniteMatchingClosure.mk
  sha256:4fc3fe85063d058b492fafe29ae20fa10dfffad523cd690c888db9e20db73eae
D5/S3/Topology/FiniteMatchingClosure.outer
  sha256:d962ee2ed76436876ed38e6413daad33e94b6a3b28cb5a94d0d73e495fcdc336
D5/S3/Topology/FiniteMatchingClosure.twoStep
  sha256:23c7c26ee3555ebcaa2b2ec6e6bf31358f6aad5ffb1ba99a7192aa238252e5ae
D5/S3/Topology/FiniteMatchingClosure.upper
  sha256:309e20095fb12ab4fc92c4112b496243ab83320fbd86654313448dc3898ae826
D5/S3/Topology/FiniteMatchingComposition.Piece
  sha256:e72dfa50ef04ae4d4e6de55d69e4dc57394cad0a583db1c27c79b96530667750
D5/S3/Topology/FiniteMatchingComposition.composite
  sha256:916faedcd34e169a2fbdf6728df71f94600d26fc1f3c6b285d74c8f06225beff
D5/S3/Topology/FiniteMatchingComposition.composite_component_iff
  sha256:be312f600ea4ca4bbcccb5b57ae14d3f2185e967de1270a0e82c21fbe8136ff9
D5/S3/Topology/FiniteMatchingComposition.halfEdgeInternalComponent
  sha256:a04c7bf2d678925c55b5d2f7f9efa98f42d82193a9df56f676671df2304d3d6e
D5/S3/Topology/FiniteMatchingComposition.halfEdgeStep
  sha256:e69270f68620c6cf1c2ed2a5e10366812ee45336d79a74b56fc32ba1f344af88
D5/S3/Topology/FiniteMatchingComposition.instFiniteHalfEdgeInternalComponent
  sha256:4607dc2755ab7323ae81ba7023cc9e43c9bd09ab393bacbd8ee1bb8432218bf7
D5/S3/Topology/FiniteMatchingComposition.internalLoopCount
  sha256:93bdce1ab5e61437907986b6f2bdde47b0b5f569fbacb1d341051b76d3d98b2c
D5/S3/Topology/FiniteMatchingComposition.outerPiece
  sha256:6c21173b5d70ba5684e939385e1dada6eacb74080d881a04c316994d0bbfb2fb
D5/S3/Topology/FiniteMatchingComposition.piecesMate
  sha256:fdcd9c399baea0d8d59316b5afc30b29bce9cada400909e1a4bd08353972343f
D5/S3/Topology/FiniteMatchingComposition.piecesPerm
  sha256:a81b0ecde851ecf043055e8d0b04a77ca43406b09951e6cc70e37cf2de0ad565
D5/S3/Topology/FiniteMatchingComposition.seamPerm
  sha256:2bd72984b5e26bd5e7a6da3a4a5674caf55288cd9e08a2c672a3a9ed630d0f22
D5/S3/Topology/FiniteMatchingComposition.triple_component_iff
  sha256:19eab152d52ef11b7d1c34af8aae61f133707a6dfda28d367bbabc49ec0d4acd
D5/S3/Topology/FiniteMatchingSewing.Unmarked
  sha256:51025aed499100a934d7498a706d4c012735645288a824635224888a194143ec
D5/S3/Topology/FiniteMatchingSewing.closedCount
  sha256:22cb8fa984f4608633141f421d85534aad888d0c7ef282a924a687e10b2360b8
D5/S3/Topology/FiniteMatchingSewing.closedStackStep
  sha256:a15e5e19dec3574852765d9432868e2155b5afe52c05b280714d181f975fd2c6
D5/S3/Topology/FiniteMatchingSewing.closedStack_card
  sha256:6d2b8de2ac6184bfee0a14def3ecbabe19b839e832fd1718544294beebee4818
D5/S3/Topology/FiniteMatchingSewing.closedWire
  sha256:253b4239dd34d1946dcfcfe72a10d1ff72bb54c3c5c53ba540847e41f48a9b26
D5/S3/Topology/FiniteMatchingSewing.closed_weight_cyclic
  sha256:da9180e672dc9a1d4173e7ae2125d00cd54f8460c1c5321767bcdb389a7b862b
D5/S3/Topology/FiniteMatchingSewing.componentMap
  sha256:eb039b6c7a758935f9e6f56038573c49664c80ffe12d7ec4080210d5cc7020c5
D5/S3/Topology/FiniteMatchingSewing.matching_component_iff
  sha256:02c4353eec69cc698c1e8d4327caa03d89ba7d57c3d4800db740fa228492d490
D5/S3/Topology/FiniteMatchingSewing.sewStep
  sha256:e75254402356f209e67014f026306f4b496ad2ec36d5edb160a09f9fdaf2b9ec
D5/S3/Topology/FiniteMatchingSewing.sewingInventory
  sha256:0e2af229a000fd77e9a398c99d58eee39b9f06b3ca269d183cd7bea1f7cdec03
matchingPartition: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.composite_assoc,
  FiniteMatchingAssociativity.matching_graph
matching_graph: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.matching_product
matching_product: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.composite_assoc
composite_assoc: proof_shape=bind-only; consumers=PlanarDiagramAlgebra.concat_assoc,
  BrauerZeroMonoid.multiply_assoc
disjointStep: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.adjoinUnmarked,
  FiniteMatchingAssociativity.adjoinUnmarked._proof_1
disjointLabel: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.disjointComponents,
  FiniteMatchingAssociativity.disjointComponents._proof_1
disjointComponents: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.adjoinUnmarked,
  FiniteMatchingAssociativity.adjoinUnmarked._proof_1
adjoinBoundary: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.adjoinUnmarked,
  FiniteMatchingAssociativity.adjoinUnmarked._proof_1
sumMatching: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.adjoin_endpoint,
  FiniteMatchingAssociativity.sumClosedEquiv
adjoin_endpoint: proof_shape=bind-only;
  consumers=FiniteMatchingAssociativity.tripleInventory._proof_1
adjoinUnmarked: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.tripleInventory
sumWire: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.attachedStep,
  FiniteMatchingAssociativity.attachedTripleEquiv._proof_2
sumToPiece: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.sumClosedEquiv,
  FiniteMatchingAssociativity.sumClosedEquiv._proof_1
pieceToSum: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.sumClosedEquiv,
  FiniteMatchingAssociativity.sumClosedEquiv._proof_1
sumClosedEquiv: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.tripleInventory
Triple: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.attachedTripleEquiv,
  FiniteMatchingAssociativity.attachedTripleEquiv._proof_2
tripleMate: proof_shape=bind-only;
  consumers=FiniteMatchingAssociativity.attachedTripleEquiv._proof_2,
  FiniteMatchingAssociativity.attachedTripleEquiv._proof_3
tripleWire: proof_shape=bind-only;
  consumers=FiniteMatchingAssociativity.attachedTripleEquiv._proof_2,
  FiniteMatchingAssociativity.attachedTripleEquiv._proof_3
tripleStep: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.attachedTripleEquiv,
  FiniteMatchingAssociativity.attachedTripleEquiv._proof_2
attachedStep: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.attachedTripleEquiv,
  FiniteMatchingAssociativity.attachedTripleEquiv._proof_2
attachedTripleEquiv: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.tripleInventory
tripleInventory: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.triple_card
rotateTriple: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.rotateTripleEquiv,
  FiniteMatchingAssociativity.rotateTripleEquiv._proof_1
unrotateTriple: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.rotateTripleEquiv,
  FiniteMatchingAssociativity.rotateTripleEquiv._proof_1
rotateTripleEquiv: proof_shape=bind-only;
  consumers=FiniteMatchingAssociativity.internalLoopCount_cocycle
triple_card: proof_shape=bind-only; consumers=FiniteMatchingAssociativity.internalLoopCount_cocycle
internalLoopCount_cocycle: proof_shape=bind-only;
  consumers=FiniteMatchingAssociativity.internalLoopCount_pos_assoc
internalLoopCount_pos_assoc: proof_shape=bind-only; consumers=BrauerZeroMonoid.multiply_assoc
-/
import D5.S3.Topology.FiniteMatchingClosure
import D5.S3.Topology.FiniteMatchingComposition
import D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSourceMonoids
import D5.S3.Topology.FiniteMatchingSewing

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace D5.S3.Topology.FiniteMatchingAssociativity
open D5.S3.Topology.FiniteMatchingClosure
open D5.S3.Topology.FiniteMatchingComposition
open D5.S3.Topology.FiniteMatchingSewing
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSourceMonoids

private def matchingPartition {N : ℕ} (d : Matching (Boundary N)) : Setoid (Boundary N) :=
  involutionSetoid ⟨d.mate, d.mate, d.involutive, d.involutive⟩ d.involutive

private theorem matching_graph {N : ℕ} (d e : Matching (Boundary N)) :
    productGraph (matchingPartition d) (matchingPartition e) =
      Relation.EqvGen.setoid (gluingStep d e) := by
  apply le_antisymm
  · apply Setoid.eqvGen_le
    intro u v h
    rcases h with ⟨x,y,rfl,rfl,h⟩ | ⟨x,y,rfl,rfl,h⟩
    · rcases h with rfl | h
      · exact .refl _
      · exact .rel _ _ (Or.inl ⟨x,rfl,congrArg upper h.symm⟩)
    · rcases h with rfl | h
      · exact .refl _
      · exact .rel _ _ (Or.inr ⟨x,rfl,congrArg lower h.symm⟩)
  · apply Setoid.eqvGen_le
    intro u v h
    rcases h with ⟨x,rfl,rfl⟩ | ⟨x,rfl,rfl⟩
    · exact .rel _ _ (Or.inl ⟨x,d.mate x,rfl,rfl,Or.inr rfl⟩)
    · exact .rel _ _ (Or.inr ⟨x,e.mate x,rfl,rfl,Or.inr rfl⟩)

private theorem matching_product {N : ℕ} (d e : Matching (Boundary N)) :
    matchingPartition (composite d e) =
      partitionProduct (matchingPartition d) (matchingPartition e) := by
  change matchingPartition (composite d e) =
    Setoid.comap exteriorEmbedding (productGraph (matchingPartition d) (matchingPartition e))
  rw [matching_graph]
  ext x y
  change (x = y ∨ (composite d e).mate x = y) ↔
    Relation.EqvGen (gluingStep d e) (outer x) (outer y)
  have h := triple_component_iff d e x y
  simp only [component, Quotient.eq] at h
  change Relation.EqvGen (gluingStep d e) (outer x) (outer y) ↔
    y = x ∨ y = (composite d e).mate x at h
  constructor
  · rintro (he | he)
    · exact h.mpr (Or.inl he.symm)
    · exact h.mpr (Or.inr he.symm)
  · intro he
    rcases h.mp he with he | he
    · exact Or.inl he.symm
    · exact Or.inr he.symm

/-- The underlying perfect matching is independent of the stacking brackets.
Internal components are discarded by composite; no loop-weight law is asserted. -/
theorem composite_assoc {N : ℕ} (d e f : Matching (Boundary N)) :
    composite (composite d e) f = composite d (composite e f) := by
  have hs : matchingPartition (composite (composite d e) f) =
      matchingPartition (composite d (composite e f)) := by
    rw [matching_product, matching_product, matching_product, matching_product,
      partitionProduct_assoc]
  have hm : (composite (composite d e) f).mate = (composite d (composite e f)).mate := by
    funext x
    have h : (matchingPartition (composite d (composite e f))).r x
        ((composite (composite d e) f).mate x) := by
      rw [← hs]
      exact Or.inr rfl
    rcases h with h | h
    · exact False.elim ((composite (composite d e) f).fixedPointFree x h.symm)
    · exact h.symm
  generalize composite (composite d e) f = a at hm ⊢
  generalize composite d (composite e f) = b at hm ⊢
  cases a
  cases b
  cases hm
  rfl


private def disjointStep {X Y : Type*} (r : X → X → Prop) (s : Y → Y → Prop) :
    X ⊕ Y → X ⊕ Y → Prop
  | .inl x, .inl y => r x y
  | .inr x, .inr y => s x y
  | _, _ => False

private def disjointLabel {X Y : Type*} (r : X → X → Prop) (s : Y → Y → Prop) :
    X ⊕ Y → Component r ⊕ Component s :=
  Sum.elim (fun x => .inl (component r x)) (fun y => .inr (component s y))

private def disjointComponents {X Y : Type*} (r : X → X → Prop) (s : Y → Y → Prop) :
    Component (disjointStep r s) ≃ Component r ⊕ Component s where
  toFun := Quotient.lift (disjointLabel r s) (by
    intro x y h
    induction h with
    | rel x y h =>
      cases x <;> cases y
      · exact congrArg Sum.inl (Quotient.sound (.rel _ _ h))
      · exact False.elim h
      · exact False.elim h
      · exact congrArg Sum.inr (Quotient.sound (.rel _ _ h))
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)
  invFun := Sum.elim
    (componentMap r (disjointStep r s) Sum.inl (fun _ _ h => .rel _ _ h))
    (componentMap s (disjointStep r s) Sum.inr (fun _ _ h => .rel _ _ h))
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ x => cases x <;> rfl
  right_inv q := by
    cases q with
    | inl q => induction q using Quotient.inductionOn with | _ x => rfl
    | inr q => induction q using Quotient.inductionOn with | _ x => rfl

private def adjoinBoundary {X B Y : Type*} (a : B → X) : B ⊕ Y → X ⊕ Y :=
  Sum.map a id

private def sumMatching {B Y : Type*} (d : Matching B) (f : Matching Y) : Matching (B ⊕ Y) where
  mate := Sum.map d.mate f.mate
  involutive x := by
    cases x with
    | inl b => exact congrArg Sum.inl (d.involutive b)
    | inr y => exact congrArg Sum.inr (f.involutive y)
  fixedPointFree x := by
    cases x with
    | inl b => exact fun h => d.fixedPointFree b (Sum.inl.inj h)
    | inr y => exact fun h => f.fixedPointFree y (Sum.inr.inj h)

private theorem adjoin_endpoint {X B Y : Type*} (r : X → X → Prop) (a : B → X)
    (d : Matching B) (f : Matching Y)
    (hend : ∀ b c, component r (a b) = component r (a c) ↔ c = b ∨ c = d.mate b)
    (b c : B ⊕ Y) :
    component (disjointStep r (fun x y => y = f.mate x)) (adjoinBoundary a b) =
      component (disjointStep r (fun x y => y = f.mate x)) (adjoinBoundary a c) ↔
      c = b ∨ c = (sumMatching d f).mate b := by
  rw [← (disjointComponents r (fun x y => y = f.mate x)).injective.eq_iff]
  cases b <;> cases c
  · change Sum.inl (component r (a _)) = Sum.inl (component r (a _)) ↔ _
    simpa only [Sum.inl.injEq, sumMatching, Sum.map_inl] using hend _ _
  · change Sum.inl (component r (a _)) = Sum.inr (component _ _) ↔ _
    simp only [Sum.inl_ne_inr, sumMatching, Sum.map_inl, Sum.inr_ne_inl, or_self]
  · change Sum.inr (component _ _) = Sum.inl (component r (a _)) ↔ _
    simp only [Sum.inr_ne_inl, sumMatching, Sum.map_inr, Sum.inl_ne_inr, or_self]
  · change Sum.inr (component (fun x y => y = f.mate x) _) =
      Sum.inr (component (fun x y => y = f.mate x) _) ↔ _
    simpa only [Sum.inr.injEq, sumMatching, Sum.map_inr, id_eq] using matching_component_iff f _ _

private def adjoinUnmarked {X B Y : Type*} (r : X → X → Prop) (a : B → X)
    (f : Matching Y) :
    Unmarked (disjointStep r (fun x y => y = f.mate x)) (adjoinBoundary a) ≃
      Unmarked r a := by
  let E := disjointComponents r (fun x y => y = f.mate x)
  have hex (q : Unmarked (disjointStep r (fun x y => y = f.mate x)) (adjoinBoundary a)) :
      ∃ c : Component r, E q.1 = Sum.inl c := by
    cases h : E q.1 with
    | inl c => exact ⟨c,rfl⟩
    | inr c =>
      exfalso
      induction c using Quotient.inductionOn with
      | _ y => exact q.2 (.inr y) (E.injective (by
          change Sum.inr (component _ y) = E q.1
          exact h.symm))
  let F : Unmarked (disjointStep r (fun x y => y = f.mate x)) (adjoinBoundary a) →
      Unmarked r a := fun q =>
    ⟨Classical.choose (hex q), fun b hb => q.2 (.inl b) (E.injective (by
        change Sum.inl (component r (a b)) = E q.1
        rw [Classical.choose_spec (hex q), hb]))⟩
  have hF (q) : E q.1 = Sum.inl (F q).1 := Classical.choose_spec (hex q)
  let G : Unmarked r a →
      Unmarked (disjointStep r (fun x y => y = f.mate x)) (adjoinBoundary a) := fun q =>
    ⟨E.symm (.inl q.1), by
      intro b hb
      have he := congrArg E hb
      rw [E.apply_symm_apply] at he
      cases b with
      | inl b => exact q.2 b (Sum.inl.inj he)
      | inr y =>
        change Sum.inr (component _ y) = Sum.inl q.1 at he
        exact Sum.inr_ne_inl he⟩
  exact {
    toFun := F
    invFun := G
    left_inv := by
      intro q
      apply Subtype.ext
      apply E.injective
      exact (E.apply_symm_apply (.inl (F q).1)).trans (hF q).symm
    right_inv := by
      intro q
      apply Subtype.ext
      apply Sum.inl.inj
      exact (hF (G q)).symm.trans (E.apply_symm_apply (.inl q.1))
  }

private def sumWire {N : ℕ} : Boundary N ⊕ Boundary N → Boundary N ⊕ Boundary N
  | .inl b => .inr ((identityMatching N).mate b)
  | .inr b => .inl ((identityMatching N).mate b)

private def sumToPiece {N : ℕ} : Boundary N ⊕ Boundary N → Piece N :=
  Sum.elim (fun b => (false,b)) (fun b => (true,b))

private def pieceToSum {N : ℕ} : Piece N → Boundary N ⊕ Boundary N
  | (false,b) => .inl b
  | (true,b) => .inr b

private def sumClosedEquiv {N : ℕ} (d f : Matching (Boundary N)) :
    Component (twoStep (sumMatching d f).mate sumWire) ≃
      Component (closedStackStep d f) := by
  apply contractionEquiv _ _ sumToPiece pieceToSum
    (by rintro ⟨l,b⟩; cases l <;> rfl)
  · intro x y h
    rcases h with h | h <;> subst y
    · cases x <;> exact .rel _ _ (Or.inl rfl)
    · rcases x with ⟨b,i⟩ | ⟨b,i⟩ <;> cases b <;> exact .rel _ _ (Or.inr rfl)
  · intro x y h
    rcases h with h | h <;> subst y
    · rcases x with ⟨l,b⟩; cases l <;> exact .rel _ _ (Or.inl rfl)
    · rcases x with ⟨l,b,i⟩; cases l <;> cases b <;> exact .rel _ _ (Or.inr rfl)
  · intro x; cases x <;> exact .refl _

private abbrev Triple (N : ℕ) := Piece N ⊕ Boundary N

private def tripleMate {N : ℕ} (d e f : Matching (Boundary N)) : Triple N → Triple N
  | .inl b => .inl (piecesMate d e b)
  | .inr b => .inr (f.mate b)

private def tripleWire {N : ℕ} : Triple N → Triple N
  | .inl (false,(false,i)) => .inr (true,i)
  | .inl (false,(true,i)) => .inl (true,(false,i))
  | .inl (true,(false,i)) => .inl (false,(true,i))
  | .inl (true,(true,i)) => .inr (false,i)
  | .inr (false,i) => .inl (true,(true,i))
  | .inr (true,i) => .inl (false,(false,i))

private def tripleStep {N : ℕ} (d e f : Matching (Boundary N)) :=
  twoStep (tripleMate d e f) tripleWire

private def attachedStep {N : ℕ} (d e f : Matching (Boundary N)) :=
  sewStep (disjointStep (halfEdgeStep d e) (fun x y => y = f.mate x))
    (adjoinBoundary outerPiece) sumWire

private def attachedTripleEquiv {N : ℕ} (d e f : Matching (Boundary N)) :
    Component (attachedStep d e f) ≃ Component (tripleStep d e f) := by
  apply contractionEquiv _ _ id id (fun _ => rfl)
  · intro x y h
    rcases h with h | ⟨b,rfl,rfl⟩
    · cases x with
      | inl x =>
        cases y with
        | inl y =>
          rcases h with h | h <;> subst y
          · exact .rel _ _ (Or.inl rfl)
          · rcases x with ⟨l,b,i⟩; cases l <;> cases b
            · exact .refl _
            · exact .rel _ _ (Or.inr rfl)
            · exact .rel _ _ (Or.inr rfl)
            · exact .refl _
        | inr y => exact False.elim h
      | inr x =>
        cases y with
        | inl y => exact False.elim h
        | inr y => subst y; exact .rel _ _ (Or.inl rfl)
    · rcases b with ⟨b,i⟩ | ⟨b,i⟩ <;> cases b <;> exact .rel _ _ (Or.inr rfl)
  · intro x y h
    rcases h with h | h <;> subst y
    · cases x
      · exact .rel _ _ (Or.inl (Or.inl rfl))
      · exact .rel _ _ (Or.inl rfl)
    · rcases x with ⟨l,b,i⟩ | ⟨b,i⟩
      · cases l <;> cases b
        · exact .rel _ _ (Or.inr ⟨.inl (false,i),rfl,rfl⟩)
        · exact .rel _ _ (Or.inl (Or.inr rfl))
        · exact .rel _ _ (Or.inl (Or.inr rfl))
        · exact .rel _ _ (Or.inr ⟨.inl (true,i),rfl,rfl⟩)
      · cases b
        · exact .rel _ _ (Or.inr ⟨.inr (false,i),rfl,rfl⟩)
        · exact .rel _ _ (Or.inr ⟨.inr (true,i),rfl,rfl⟩)
  · intro x; exact .refl _

private def tripleInventory {N : ℕ} (d e f : Matching (Boundary N)) :
    Component (tripleStep d e f) ≃
      halfEdgeInternalComponent d e ⊕ Component (closedStackStep (composite d e) f) :=
  (attachedTripleEquiv d e f).symm.trans
    ((sewingInventory
      (disjointStep (halfEdgeStep d e) (fun x y => y = f.mate x))
      (adjoinBoundary outerPiece) (sumMatching (composite d e) f) sumWire
      (adjoin_endpoint (halfEdgeStep d e) outerPiece (composite d e) f
        (composite_component_iff d e))).trans
      (Equiv.sumCongr (adjoinUnmarked (halfEdgeStep d e) outerPiece f)
        (sumClosedEquiv (composite d e) f)))

private def rotateTriple {N : ℕ} : Triple N → Triple N
  | .inl (false,b) => .inr b
  | .inl (true,b) => .inl (false,b)
  | .inr b => .inl (true,b)

private def unrotateTriple {N : ℕ} : Triple N → Triple N
  | .inl (false,b) => .inl (true,b)
  | .inl (true,b) => .inr b
  | .inr b => .inl (false,b)

private def rotateTripleEquiv {N : ℕ} (d e f : Matching (Boundary N)) :
    Component (tripleStep d e f) ≃ Component (tripleStep e f d) := by
  apply contractionEquiv _ _ rotateTriple unrotateTriple
    (by rintro (⟨l,b⟩ | b); cases l <;> rfl; rfl)
  · intro x y h
    rcases h with h | h <;> subst y
    · rcases x with ⟨l,b⟩ | b
      · cases l <;> exact .rel _ _ (Or.inl rfl)
      · exact .rel _ _ (Or.inl rfl)
    · rcases x with ⟨l,b,i⟩ | ⟨b,i⟩
      · cases l <;> cases b <;> exact .rel _ _ (Or.inr rfl)
      · cases b <;> exact .rel _ _ (Or.inr rfl)
  · intro x y h
    rcases h with h | h <;> subst y
    · rcases x with ⟨l,b⟩ | b
      · cases l <;> exact .rel _ _ (Or.inl rfl)
      · exact .rel _ _ (Or.inl rfl)
    · rcases x with ⟨l,b,i⟩ | ⟨b,i⟩
      · cases l <;> cases b <;> exact .rel _ _ (Or.inr rfl)
      · cases b <;> exact .rel _ _ (Or.inr rfl)
  · rintro (⟨l,b⟩ | b)
    · cases l <;> exact .refl _
    · exact .refl _

private theorem triple_card {N : ℕ} (d e f : Matching (Boundary N)) :
    Nat.card (Component (tripleStep d e f)) =
      internalLoopCount d e + internalLoopCount (composite d e) f +
        closedCount (composite (composite d e) f) := by
  rw [Nat.card_congr (tripleInventory d e f), Nat.card_sum, closedStack_card]
  exact (Nat.add_assoc _ _ _).symm

/-- Both bracketings remove exactly the same number of closed components. -/
theorem internalLoopCount_cocycle {N : ℕ} (d e f : Matching (Boundary N)) :
    internalLoopCount d e + internalLoopCount (composite d e) f =
      internalLoopCount e f + internalLoopCount d (composite e f) := by
  have h := Nat.card_congr (rotateTripleEquiv d e f)
  rw [triple_card, triple_card] at h
  have hc := closed_weight_cyclic (composite e f) d
  rw [composite_assoc] at h
  omega

theorem internalLoopCount_pos_assoc {N : ℕ} (d e f : Matching (Boundary N)) :
    (0 < internalLoopCount d e ∨ 0 < internalLoopCount (composite d e) f) ↔
      (0 < internalLoopCount e f ∨ 0 < internalLoopCount d (composite e f)) := by
  have h := internalLoopCount_cocycle d e f
  omega

end D5.S3.Topology.FiniteMatchingAssociativity
