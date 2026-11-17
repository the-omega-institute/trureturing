/- GID: D5/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/AraujoSignedFactorLifting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Brauer complete-mapping existence constructions and classification. -/

/-
admission_basis: escape-witness
escape_witness: D5.S3.Combinatorics.PerfectMatchings.AraujoSignedFactorLifting.rank_three_signed_factor
proof_shape: content — coordinateMul_spec, coordinateMul_assoc, coordinateMul_preserving, rankedDiagram_mul, coordinate_factorization, coordinate_product_factorization, coordinateSandwich_some_iff, coordinateSandwich_diagonal, coordinateSandwich_product, halfCanonicalEntry_sandwich, rees_s3_lift, pair_triangle_potential, oneTriangle_potential, finite_signed_residual_transversal, half_signed_quotient_transversal, rank_two_signed_factor, rank_three_signed_factor
proof_shape: bind-only — coordinatePartition, coordinatePartition_injective, coordinateMul, coordinateCenter, rankedDiagram_group_injective, coordinateSandwich, halfMarked, halfThroughLabels, halfMarkedCard, halfMarked_no_extra_fixed, halfMiddleTransport, halfMiddleTransport_connected, halfSandwichEntry, half_sandwich_sign, PerfectMarkedHalf, halfMarkedEquiv, partialBrauerRankEquiv, perfectMarkedTripleEquiv, rankPerfectCoordinatesEquiv, swapRankBrauerCoordinates, brauerRankHalfDiagramEquiv, halfRanked, halfLabelChange, halfCanonicalEntry, halfCanonicalEntry_ordered, gauge_two_product, gauge_three_product, half_canonical_sign_gauge, canonical_cycle_two_sign, canonical_cycle_three_sign, reesProjection, s3SignSection, s3LiftEntry, s3LiftEntry_sign, s3LiftEntry_injective, s3LiftProduct_injective, signedPattern, residualRows, residualColumns, residualProducts, residualSwitch, signed_residual_transversal, rees_group_transport, symmetricTwoSignEquiv, halfMatrix
Direct frozen dependencies (declaration statement_id):
D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.endpointPairing sha256:d5fe3010047acb473686bcb77f6a2d93e8abda0a4b57e07f73cd492d884645bb
D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.endpoint_pairing_fixed_point_free sha256:f38f799a458169dd8462c2f2d261dd3b31ab484d67cf3072fc90e32441e69122
D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.endpoint_pairing_involutive sha256:68a971affeadeb943cd77ab25c00a899390e1744f4dfd8ebba1ee658748ebd3b
D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.endpoint_pairing_reattach_same_cycle sha256:80531d01c5f8e8e12fe05303348e4bb896d99ae17e8b09fcabf422650c76dbe1
D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Connected sha256:6d8b0931bcb5ff204447a86b31378e1915c6cc1d8fca5b690ecfbafce8be9e46
D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.connected_iff_rotation_orbits sha256:7ad1cdbc41eb6395cdc5d770c9601e3a8cad541996c47297f2c2a9207e7a4cad
D5.S3.Zeros.Convolution.PerfectMatchingCount.FixedPointFreeInvolution sha256:6a2fd619f7f0c220bed4d3b853cca9527379a8bd42cefa9403ca65d4b3210aac
D5.S3.Zeros.Convolution.PerfectMatchingCount.card_fixedPointFreeInvolution_mul sha256:f668778ce789801ae29ef9f459aca650eb978ac4b6ca4160af5447a4367a38a9
D5.S3.Zeros.Convolution.PerfectMatchingCount.instFintypeFixedPointFreeInvolution sha256:662e2e6ff37d64412b2e0ed0ce1cccc25fbfa080efcb06596f49226b5ef90dbc
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24053
-/


import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega
import Mathlib.GroupTheory.Perm.Basic
import Lean.Elab.Tactic.LibrarySearch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Order.Setoid.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Tauto
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.Int.Order.Units
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Lucas
import D5.S3.Zeros.Convolution.PerfectMatchingCount
import D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerCoordinates
import D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerHalfTriangles
import D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerOverlayTransport
import D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSourceMonoids
import D5.S0.Certificates.Groups.AraujoSymmetricCompleteMappings

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

namespace D5.S3.Combinatorics.PerfectMatchings.AraujoSignedFactorLifting

open Equiv
open scoped BigOperators
open D5.S3.Zeros.Convolution.PerfectMatchingCount
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerCoordinates
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerHalfTriangles
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerOverlayTransport
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerOverlayTransport
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSourceMonoids

noncomputable abbrev coordinatePartition {n : ℕ} (d : DiagramCoordinates (Fin n)) : (Setoid (Bool × Fin n)) :=
  involutionSetoid (coordinatePerm d) (coordinateMateInvolutive d)

theorem coordinatePartition_injective {n : ℕ} : Function.Injective
    (coordinatePartition : DiagramCoordinates (Fin n) → (Setoid (Bool × Fin n))) := by
  intro d e h
  exact coordinatePerm_injective (involutionSetoid_injective _ _
    (coordinateMateInvolutive d) (coordinateMateInvolutive e) h)

noncomputable def coordinateMul {n : ℕ} (d e : DiagramCoordinates (Fin n)) :
    DiagramCoordinates (Fin n) :=
  (partialBrauerCoordinateEquiv n).symm
    ⟨partitionProduct (coordinatePartition d) (coordinatePartition e),
      partitionProductPartialClosed
        ⟨coordinatePartition d,involutionSetoidBlockLeTwo
          (coordinatePerm d) (coordinateMateInvolutive d)⟩
        ⟨coordinatePartition e,involutionSetoidBlockLeTwo
          (coordinatePerm e) (coordinateMateInvolutive e)⟩⟩

theorem coordinateMul_spec {n : ℕ} (d e : DiagramCoordinates (Fin n)) :
    partitionProduct (coordinatePartition d) (coordinatePartition e) =
      coordinatePartition (coordinateMul d e) := by
  have h := congrArg Subtype.val ((partialBrauerCoordinateEquiv n).apply_symm_apply
    (⟨partitionProduct (coordinatePartition d) (coordinatePartition e),
      partitionProductPartialClosed
        ⟨coordinatePartition d,involutionSetoidBlockLeTwo
          (coordinatePerm d) (coordinateMateInvolutive d)⟩
        ⟨coordinatePartition e,involutionSetoidBlockLeTwo
          (coordinatePerm e) (coordinateMateInvolutive e)⟩⟩ : PartialBrauer n))
  exact h.symm

private theorem coordinateMul_assoc {n : ℕ} (d e f : DiagramCoordinates (Fin n)) :
    coordinateMul (coordinateMul d e) f = coordinateMul d (coordinateMul e f) := by
  apply coordinatePartition_injective
  rw [← coordinateMul_spec,← coordinateMul_spec,← coordinateMul_spec,← coordinateMul_spec]
  exact partitionProduct_assoc _ _ _

private theorem coordinateMul_preserving {n : ℕ} (d e : DiagramCoordinates (Fin n))
    (w : d.lower.through ≃ e.upper.through)
    (hw : ∀ x : d.lower.through, (middleOverlay d.lower e.upper).r x (w x)) :
    coordinateMul d e = coordinateConcat d e w := by
  apply coordinatePartition_injective
  rw [← coordinateMul_spec]
  exact coordinate_product_preserving d e w hw

theorem rankedDiagram_mul {n r : ℕ} (A D E : RankedHalf (Fin n) r)
    (g h : Equiv.Perm (Fin r)) :
    coordinateMul (rankedDiagram A g D) (rankedDiagram D h E) =
      rankedDiagram A (g * h) E := by
  rw [coordinateMul_preserving _ _ (Equiv.refl _) (fun x => Relation.EqvGen.refl x.val)]
  dsimp only [coordinateConcat,rankedDiagram]
  congr 1
  apply Equiv.ext
  intro x
  simp [Equiv.Perm.mul_def]

private noncomputable def coordinateCenter {n r : ℕ} (O D E : RankedHalf (Fin n) r) :
    DiagramCoordinates (Fin n) :=
  coordinateMul (rankedDiagram O 1 D) (rankedDiagram E 1 O)

private theorem coordinate_factorization {n r : ℕ} (O A D : RankedHalf (Fin n) r)
    (g : Equiv.Perm (Fin r)) :
    rankedDiagram A g D = coordinateMul (rankedDiagram A g O) (rankedDiagram O 1 D) := by
  rw [rankedDiagram_mul,mul_one]

private theorem coordinate_product_factorization {n r : ℕ} (O A D E F : RankedHalf (Fin n) r)
    (g h : Equiv.Perm (Fin r)) :
    coordinateMul (rankedDiagram A g D) (rankedDiagram E h F) =
      coordinateMul (rankedDiagram A g O)
        (coordinateMul (coordinateCenter O D E) (rankedDiagram O h F)) := by
  have h₁ := coordinate_factorization O A D g
  have h₂ : rankedDiagram E h F =
      coordinateMul (rankedDiagram E 1 O) (rankedDiagram O h F) := by
    rw [rankedDiagram_mul,one_mul]
  rw [h₁,h₂]
  simp only [coordinateMul_assoc,coordinateCenter]

theorem rankedDiagram_group_injective {n r : ℕ} (A D : RankedHalf (Fin n) r) :
    Function.Injective (fun g : Equiv.Perm (Fin r) => rankedDiagram A g D) := by
  intro g h he
  have hf : rankedCoordinatesEquiv (Fin n) r (A,g,D) =
      rankedCoordinatesEquiv (Fin n) r (A,h,D) := Subtype.ext he
  exact congrArg (fun v => v.2.1) ((rankedCoordinatesEquiv (Fin n) r).injective hf)

noncomputable def coordinateSandwich {n r : ℕ} (O D E : RankedHalf (Fin n) r) :
    Option (Equiv.Perm (Fin r)) := by
  classical
  exact if h : ∃ p : Equiv.Perm (Fin r), coordinateCenter O D E = rankedDiagram O p O then
    some (Classical.choose h) else none

private theorem coordinateSandwich_some_iff {n r : ℕ} (O D E : RankedHalf (Fin n) r)
    (p : Equiv.Perm (Fin r)) :
    coordinateSandwich O D E = some p ↔ coordinateCenter O D E = rankedDiagram O p O := by
  classical
  unfold coordinateSandwich
  split
  · rename_i h
    have hc := Classical.choose_spec h
    constructor
    · intro he
      cases Option.some.inj he
      exact hc
    · intro he
      exact congrArg some ((rankedDiagram_group_injective O O) (hc.symm.trans he))
  · rename_i h
    constructor
    · intro he
      cases he
    · intro he
      exact (h ⟨p,he⟩).elim

theorem coordinateSandwich_diagonal {n r : ℕ} (O D : RankedHalf (Fin n) r) :
    coordinateSandwich O D D = some 1 := by
  apply (coordinateSandwich_some_iff O D D 1).mpr
  unfold coordinateCenter
  rw [rankedDiagram_mul,one_mul]

theorem coordinateSandwich_product {n r : ℕ} (O A D E F : RankedHalf (Fin n) r)
    (g h p : Equiv.Perm (Fin r)) (hp : coordinateSandwich O D E = some p) :
    coordinateMul (rankedDiagram A g D) (rankedDiagram E h F) =
      rankedDiagram A (g * p * h) F := by
  rw [coordinate_product_factorization O,(coordinateSandwich_some_iff O D E p).mp hp,
    rankedDiagram_mul,rankedDiagram_mul,mul_assoc]

attribute [local instance] Classical.propDecidable

private noncomputable def halfMarked {n r : ℕ} (D : HalfDiagram n r) : MarkedHalf (Fin n) where
  through := {x | x ∈ D.1.val}
  mate := halfPermutation D
  involutive := halfPermutationInvolutive D
  fixes x hx := (halfPermutationFixed D x).mpr hx

private noncomputable def halfThroughLabels {n r : ℕ} (D : HalfDiagram n r) :
    (halfMarked D).through ≃ Fin r :=
  (D.1.val.orderIsoOfFin D.1.property).toEquiv.symm

private theorem halfMarkedCard {n r : ℕ} (D : HalfDiagram n r) :
    Nat.card (halfMarked D).through = r := by
  simpa only [Nat.card_fin] using Nat.card_congr (halfThroughLabels D)

private theorem halfMarked_no_extra_fixed {n r : ℕ} (D : HalfDiagram n r)
    (x : Fin n) (hx : x ∉ (halfMarked D).through) : (halfMarked D).mate x ≠ x :=
  fun h => hx ((halfPermutationFixed D x).mp h)

private noncomputable def halfMiddleTransport {n r : ℕ} {D E : HalfDiagram n r}
    (w : OverlayTransport (halfPermutation D) (halfPermutation E)) :
    (halfMarked D).through ≃ (halfMarked E).through :=
  ((Equiv.subtypeEquivRight (halfPermutationFixed D)).symm.trans w.transport).trans
    (Equiv.subtypeEquivRight (halfPermutationFixed E))

private theorem halfMiddleTransport_connected {n r : ℕ} {D E : HalfDiagram n r}
    (w : OverlayTransport (halfPermutation D) (halfPermutation E))
    (x : (halfMarked D).through) :
    (middleOverlay (halfMarked D) (halfMarked E)).r x (halfMiddleTransport w x) :=
  w.connected ((Equiv.subtypeEquivRight (halfPermutationFixed D)).symm x)

private noncomputable def halfSandwichEntry {n r : ℕ} {D E : HalfDiagram n r}
    (w : OverlayTransport (halfPermutation D) (halfPermutation E)) : Equiv.Perm (Fin r) :=
  (((halfThroughLabels D).symm.trans (halfMiddleTransport w)).trans (halfThroughLabels E)).symm

private theorem half_sandwich_sign {n r : ℕ} (D E : HalfDiagram n r)
    (w : OverlayTransport (halfPermutation D) (halfPermutation E)) :
    Equiv.Perm.sign (halfSandwichEntry w) = halfTransportSign D E w := by
  rw [halfSandwichEntry,Equiv.Perm.sign_symm]
  congr 1

private abbrev PerfectMarkedHalf (n r : ℕ) := {H : MarkedHalf (Fin n) //
  Nat.card H.through = r ∧ ∀ x ∉ H.through, H.mate x ≠ x}

private noncomputable def halfMarkedEquiv (n r : ℕ) : HalfDiagram n r ≃ PerfectMarkedHalf n r := by
  let f : HalfDiagram n r → PerfectMarkedHalf n r :=
    fun D => ⟨halfMarked D,halfMarkedCard D,halfMarked_no_extra_fixed D⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨T,p⟩ ⟨U,q⟩ he
    have hv : halfMarked ⟨T,p⟩ = halfMarked ⟨U,q⟩ := congrArg Subtype.val he
    have ht : T = U := by
      apply Subtype.ext
      apply Finset.coe_injective
      exact congrArg MarkedHalf.through hv
    subst U
    congr 1
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    have hm := congrArg (fun H : MarkedHalf (Fin n) => H.mate x.val) hv
    simpa only [halfMarked,halfPermutation,Equiv.Perm.subtypeCongr.right_apply _ _ x.property] using hm
  · intro H
    let T : ThroughSets n r := ⟨H.val.through.toFinset,by
      simpa only [Set.toFinset_card,Nat.card_eq_fintype_card] using H.property.1⟩
    have hn (x : {x : Fin n // x ∉ T.val}) : H.val.mate x.val ∉ T.val := by
      have hx : x.val ∉ H.val.through := by simpa [T] using x.property
      have hm := (half_mate_mem H.val x.val).not.mpr hx
      simpa [T] using hm
    let p : Equiv.Perm {x : Fin n // x ∉ T.val} :=
      Function.Involutive.toPerm (fun x => ⟨H.val.mate x,hn x⟩)
        (fun x => Subtype.ext (H.val.involutive x))
    have hp : Function.Involutive p := fun x => Subtype.ext (H.val.involutive x)
    have hpf : ∀ x, p x ≠ x := by
      intro x he
      apply H.property.2 x.val (by simpa [T] using x.property)
      exact congrArg Subtype.val he
    refine ⟨⟨T,⟨p,hp,hpf⟩⟩,?_⟩
    apply Subtype.ext
    change halfMarked ⟨T,⟨p,hp,hpf⟩⟩ = H.val
    apply markedHalf_ext
    · ext x
      simp [halfMarked,T]
    · apply Equiv.ext
      intro x
      by_cases hx : x ∈ H.val.through
      · have ht : x ∈ T.val := Set.mem_toFinset.mpr hx
        exact ((halfPermutationFixed ⟨T,⟨p,hp,hpf⟩⟩ x).mpr ht).trans
          (H.val.fixes x hx).symm
      · have ht : x ∉ T.val := by simpa [T] using hx
        exact Equiv.Perm.subtypeCongr.right_apply _ _ ht

noncomputable def partialBrauerRankEquiv (n r : ℕ) :
    (RankedHalf (Fin n) r × Equiv.Perm (Fin r) × RankedHalf (Fin n) r) ≃
      {a : PartialBrauer n // partialBrauerRank a = r} :=
  (rankedCoordinatesEquiv (Fin n) r).trans
    ((partialBrauerCoordinateEquiv n).subtypeEquiv (fun d => by
      change diagramRank d = r ↔
        diagramRank ((partialBrauerCoordinateEquiv n).symm (partialBrauerCoordinateEquiv n d)) = r
      rw [(partialBrauerCoordinateEquiv n).symm_apply_apply]))

private noncomputable def perfectMarkedTripleEquiv (n r : ℕ) :
    (PerfectMarkedHalf n r × Equiv.Perm (Fin r) × PerfectMarkedHalf n r) ≃
    {v : RankedHalf (Fin n) r × Equiv.Perm (Fin r) × RankedHalf (Fin n) r //
      (∀ x ∉ v.1.val.through, v.1.val.mate x ≠ x) ∧
      (∀ x ∉ v.2.2.val.through, v.2.2.val.mate x ≠ x)} where
  toFun v := ⟨(⟨v.1.val,v.1.property.1⟩,v.2.1,⟨v.2.2.val,v.2.2.property.1⟩),
    v.1.property.2,v.2.2.property.2⟩
  invFun v := (⟨v.val.1.val,v.val.1.property,v.property.1⟩,v.val.2.1,
    ⟨v.val.2.2.val,v.val.2.2.property,v.property.2⟩)
  left_inv v := rfl
  right_inv v := rfl

private noncomputable def rankPerfectCoordinatesEquiv (n r : ℕ) :
    {v : RankedHalf (Fin n) r × Equiv.Perm (Fin r) × RankedHalf (Fin n) r //
      (∀ x ∉ v.1.val.through, v.1.val.mate x ≠ x) ∧
      (∀ x ∉ v.2.2.val.through, v.2.2.val.mate x ≠ x)} ≃
    {d : {d : DiagramCoordinates (Fin n) // diagramRank d = r} //
      ∀ v, coordinatePerm d.val v ≠ v} :=
  (rankedCoordinatesEquiv (Fin n) r).subtypeEquiv (fun v => by
    rw [coordinate_fixed_point_free_iff]
    rfl)

private noncomputable def swapRankBrauerCoordinates (n r : ℕ) :
    {d : {d : DiagramCoordinates (Fin n) // diagramRank d = r} //
      ∀ v, coordinatePerm d.val v ≠ v} ≃
    {d : BrauerCoordinates n // diagramRank d.val = r} where
  toFun d := ⟨⟨d.val.val,d.property⟩,d.val.property⟩
  invFun d := ⟨⟨d.val.val,d.property⟩,d.val.property⟩
  left_inv d := rfl
  right_inv d := rfl

noncomputable def brauerRankHalfDiagramEquiv (n r : ℕ) :
    (HalfDiagram n r × Equiv.Perm (Fin r) × HalfDiagram n r) ≃
      {a : Brauer n // brauerRank a = r} :=
  (Equiv.prodCongr (halfMarkedEquiv n r)
    (Equiv.prodCongr (Equiv.refl _) (halfMarkedEquiv n r))).trans
    ((perfectMarkedTripleEquiv n r).trans
      ((rankPerfectCoordinatesEquiv n r).trans
        ((swapRankBrauerCoordinates n r).trans
          ((brauerCoordinateEquiv n).subtypeEquiv (fun d => by
            change diagramRank d.val = r ↔
              diagramRank ((brauerCoordinateEquiv n).symm (brauerCoordinateEquiv n d)).val = r
            rw [(brauerCoordinateEquiv n).symm_apply_apply])))))

noncomputable def halfRanked {n r : ℕ} (D : HalfDiagram n r) : RankedHalf (Fin n) r :=
  ⟨halfMarked D,halfMarkedCard D⟩

private noncomputable def halfLabelChange {n r : ℕ} (D : HalfDiagram n r) : Equiv.Perm (Fin r) :=
  (rankedLabels (halfRanked D)).symm.trans (halfThroughLabels D)

private noncomputable def halfCanonicalEntry {n r : ℕ} {D E : HalfDiagram n r}
    (w : OverlayTransport (halfPermutation D) (halfPermutation E)) : Equiv.Perm (Fin r) :=
  (((rankedLabels (halfRanked D)).symm.trans (halfMiddleTransport w)).trans
    (rankedLabels (halfRanked E))).symm

private theorem halfCanonicalEntry_sandwich {n r : ℕ} (O : RankedHalf (Fin n) r)
    (D E : HalfDiagram n r)
    (w : OverlayTransport (halfPermutation D) (halfPermutation E)) :
    coordinateSandwich O (halfRanked D) (halfRanked E) = some (halfCanonicalEntry w) := by
  apply (coordinateSandwich_some_iff _ _ _ _).mpr
  unfold coordinateCenter
  rw [coordinateMul_preserving _ _ (halfMiddleTransport w) (halfMiddleTransport_connected w)]
  dsimp only [coordinateConcat,rankedDiagram]
  congr 1

private theorem halfCanonicalEntry_ordered {n r : ℕ} (D E : HalfDiagram n r)
    (w : OverlayTransport (halfPermutation D) (halfPermutation E)) :
    halfLabelChange D * halfCanonicalEntry w * (halfLabelChange E)⁻¹ = halfSandwichEntry w := by
  dsimp only [halfLabelChange,halfCanonicalEntry,halfSandwichEntry,halfRanked]
  apply Equiv.ext
  intro x
  simp [Equiv.Perm.mul_apply,Equiv.Perm.inv_def,Equiv.symm_trans_apply]

private theorem gauge_two_product {G : Type} [CommGroup G] (a b x y : G) :
    (a * x * b⁻¹) * (b * y * a⁻¹) = x * y := by
  calc
    _ = a * (x * y) * a⁻¹ := by simp [mul_assoc]
    _ = (x * y) * (a * a⁻¹) := by ac_rfl
    _ = x * y := by simp

private theorem gauge_three_product {G : Type} [CommGroup G] (a b c x y z : G) :
    (a * x * b⁻¹) * (b * y * c⁻¹) * (c * z * a⁻¹) = x * y * z := by
  calc
    _ = a * (x * y * z) * a⁻¹ := by simp [mul_assoc]
    _ = (x * y * z) * (a * a⁻¹) := by ac_rfl
    _ = x * y * z := by simp

private theorem half_canonical_sign_gauge {n r : ℕ} (D E : HalfDiagram n r)
    (w : OverlayTransport (halfPermutation D) (halfPermutation E)) :
    Equiv.Perm.sign (halfLabelChange D) * Equiv.Perm.sign (halfCanonicalEntry w) *
      (Equiv.Perm.sign (halfLabelChange E))⁻¹ = halfTransportSign D E w := by
  have h := congrArg Equiv.Perm.sign (halfCanonicalEntry_ordered D E w)
  simpa only [map_mul,map_inv,half_sandwich_sign] using h

private theorem canonical_cycle_two_sign {n r : ℕ} (w : SignedHalfCycles n r)
    (D : HalfDiagram n r) (hD : D ∉ w.cycles.triangle) :
    Equiv.Perm.sign (halfCanonicalEntry (w.transport D)) *
      Equiv.Perm.sign (halfCanonicalEntry (w.transport (w.cycles.perm D))) = 1 := by
  let f : HalfDiagram n r → ℤˣ := fun E => Equiv.Perm.sign (halfLabelChange E)
  let p : HalfDiagram n r → ℤˣ := fun E => Equiv.Perm.sign (halfCanonicalEntry (w.transport E))
  let q : HalfDiagram n r → ℤˣ := fun D => halfTransportSign D (w.cycles.perm D) (w.transport D)
  have hg (E : HalfDiagram n r) : f E * p E * (f (w.cycles.perm E))⁻¹ = q E :=
    half_canonical_sign_gauge E (w.cycles.perm E) (w.transport E)
  have h₀ := hg D
  have h₁ := hg (w.cycles.perm D)
  rw [w.cycles.outsideSquare D hD] at h₁
  change p D * p (w.cycles.perm D) = 1
  calc
    _ = (f D * p D * (f (w.cycles.perm D))⁻¹) *
        (f (w.cycles.perm D) * p (w.cycles.perm D) * (f D)⁻¹) :=
      (gauge_two_product _ _ _ _).symm
    _ = q D * q (w.cycles.perm D) := by rw [h₀,h₁]
    _ = 1 := w.twoSign D hD

private theorem canonical_cycle_three_sign {n r : ℕ} (w : SignedHalfCycles n r)
    (D : HalfDiagram n r) (hD : D ∈ w.cycles.triangle) :
    Equiv.Perm.sign (halfCanonicalEntry (w.transport D)) *
      Equiv.Perm.sign (halfCanonicalEntry (w.transport (w.cycles.perm D))) *
      Equiv.Perm.sign (halfCanonicalEntry (w.transport (w.cycles.perm (w.cycles.perm D)))) = -1 := by
  let f : HalfDiagram n r → ℤˣ := fun E => Equiv.Perm.sign (halfLabelChange E)
  let p : HalfDiagram n r → ℤˣ := fun E => Equiv.Perm.sign (halfCanonicalEntry (w.transport E))
  let q : HalfDiagram n r → ℤˣ := fun D => halfTransportSign D (w.cycles.perm D) (w.transport D)
  have hg (E : HalfDiagram n r) : f E * p E * (f (w.cycles.perm E))⁻¹ = q E :=
    half_canonical_sign_gauge E (w.cycles.perm E) (w.transport E)
  have h₀ := hg D
  have h₁ := hg (w.cycles.perm D)
  have h₂ := hg (w.cycles.perm (w.cycles.perm D))
  rw [w.cycles.triangleCube D hD] at h₂
  change p D * p (w.cycles.perm D) * p (w.cycles.perm (w.cycles.perm D)) = -1
  calc
    _ = (f D * p D * (f (w.cycles.perm D))⁻¹) *
        (f (w.cycles.perm D) * p (w.cycles.perm D) * (f (w.cycles.perm (w.cycles.perm D)))⁻¹) *
        (f (w.cycles.perm (w.cycles.perm D)) * p (w.cycles.perm (w.cycles.perm D)) * (f D)⁻¹) :=
      (gauge_three_product _ _ _ _ _ _).symm
    _ = q D * q (w.cycles.perm D) * q (w.cycles.perm (w.cycles.perm D)) := by rw [h₀,h₁,h₂]
    _ = -1 := w.threeSign D hD

open Equiv
open scoped BigOperators
open D5.S3.Zeros.Convolution.PerfectMatchingCount
open D5.S0.Certificates.Groups.AraujoSymmetricCompleteMappings
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerCoordinates
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerHalfTriangles
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerOverlayTransport

private noncomputable def reesProjection {I G Q : Type} (chi : G → Q)
    (x : (I × G × I)) : (I × Q × I) := (x.1,chi x.2.1,x.2.2)

private noncomputable def s3SignSection (q : ℤˣ) : Equiv.Perm (Fin 3) :=
  if q = 1 then 1 else Equiv.swap 0 1

private noncomputable def s3LiftEntry (p : Equiv.Perm (Fin 3)) (q v : ℤˣ)
    (g : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 3) :=
  p⁻¹ * (s3SignSection q)⁻¹ * (g * (s3SignSection q)⁻¹) *
    s3SignSection (q * Equiv.Perm.sign p * v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem s3LiftEntry_sign : ∀ (p g : Equiv.Perm (Fin 3)) (q v : ℤˣ),
    Equiv.Perm.sign g = q → Equiv.Perm.sign (s3LiftEntry p q v g) = v := by decide

private theorem s3LiftEntry_injective (p : Equiv.Perm (Fin 3)) (q v : ℤˣ) :
    Function.Injective (s3LiftEntry p q v) := by
  intro g h he
  unfold s3LiftEntry at he
  exact mul_right_cancel (mul_left_cancel (mul_right_cancel he))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem s3LiftProduct_injective : ∀ (p g h : Equiv.Perm (Fin 3)) (q v : ℤˣ),
    Equiv.Perm.sign g = q → Equiv.Perm.sign h = q →
    g*p*s3LiftEntry p q v g = h*p*s3LiftEntry p q v h → g = h := by decide

private noncomputable def signedPattern {I : Type}
    (P : I → I → Option (Equiv.Perm (Fin 3))) : I → I → Option ℤˣ :=
  fun d e => (P d e).map Equiv.Perm.sign

private theorem rees_s3_lift {I : Type} [Finite I]
    (P : I → I → Option (Equiv.Perm (Fin 3)))
    (w : ReesTransversal (signedPattern P)) : Nonempty (ReesTransversal P) := by
  classical
  let chi := (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ)
  let project : (I × (Equiv.Perm (Fin 3)) × I) → (I × ℤˣ × I) := reesProjection chi
  let entry : (I × ℤˣ × I) → Equiv.Perm (Fin 3) :=
    fun b => (P b.2.2 (w.alpha b).1).getD 1
  have hp (b : (I × ℤˣ × I)) : P b.2.2 (w.alpha b).1 = some (entry b) := by
    have h := w.product b
    cases hs : P b.2.2 (w.alpha b).1 with
    | none => simp [reesProduct,signedPattern,hs] at h
    | some p => simpa only [entry,hs,Option.getD_some]
  let af : (I × (Equiv.Perm (Fin 3)) × I) → (I × (Equiv.Perm (Fin 3)) × I) := fun x =>
    ((w.alpha (project x)).1,
      s3LiftEntry (entry (project x)) (chi x.2.1) (w.alpha (project x)).2.1 x.2.1,
      (w.alpha (project x)).2.2)
  let tf : (I × (Equiv.Perm (Fin 3)) × I) → (I × (Equiv.Perm (Fin 3)) × I) := fun x =>
    (x.1,x.2.1 * entry (project x) * (af x).2.1,(af x).2.2)
  have hpa (x : (I × (Equiv.Perm (Fin 3)) × I)) : project (af x) = w.alpha (project x) := by
    change ((w.alpha (project x)).1,
      chi (s3LiftEntry (entry (project x)) (chi x.2.1) (w.alpha (project x)).2.1 x.2.1),
      (w.alpha (project x)).2.2) = _
    exact Prod.ext rfl (Prod.ext (s3LiftEntry_sign _ _ _ _ rfl) rfl)
  have hpt (x : (I × (Equiv.Perm (Fin 3)) × I)) : project (tf x) = w.theta (project x) := by
    have h := w.product (project x)
    unfold reesProduct signedPattern at h
    rw [hp] at h
    simp only [Option.map_some] at h
    have he := Option.some.inj h
    change (x.1,chi (x.2.1 * entry (project x) * (af x).2.1),(af x).2.2) = _
    rw [map_mul,map_mul]
    have hg := congrArg (fun b => b.2.1) (hpa x)
    change chi (af x).2.1 = _ at hg
    rw [hg]
    exact he
  have hai : Function.Injective af := by
    intro x y he
    have hb : project x = project y := w.alpha.injective (by
      rw [← hpa x,← hpa y]
      exact congrArg project he)
    have he' := congrArg (fun b => b.2.1) he
    change s3LiftEntry (entry (project x)) (chi x.2.1) (w.alpha (project x)).2.1 x.2.1 =
      s3LiftEntry (entry (project y)) (chi y.2.1) (w.alpha (project y)).2.1 y.2.1 at he'
    have hq : chi x.2.1 = chi y.2.1 := congrArg (fun b => b.2.1) hb
    rw [hb,hq] at he'
    exact Prod.ext (congrArg (fun b : (I × ℤˣ × I) => b.1) hb)
      (Prod.ext (s3LiftEntry_injective _ _ _ he') (congrArg (fun b => b.2.2) hb))
  have hti : Function.Injective tf := by
    intro x y he
    have hb : project x = project y := w.theta.injective (by
      rw [← hpt x,← hpt y]
      exact congrArg project he)
    have he' := congrArg (fun b => b.2.1) he
    change x.2.1 * entry (project x) * s3LiftEntry (entry (project x)) (chi x.2.1)
      (w.alpha (project x)).2.1 x.2.1 = y.2.1 * entry (project y) *
      s3LiftEntry (entry (project y)) (chi y.2.1) (w.alpha (project y)).2.1 y.2.1 at he'
    have hq : chi x.2.1 = chi y.2.1 := congrArg (fun b => b.2.1) hb
    rw [hb,hq] at he'
    have hg := s3LiftProduct_injective (entry (project y)) x.2.1 y.2.1 (chi y.2.1)
      (w.alpha (project y)).2.1 hq rfl he'
    exact Prod.ext (congrArg (fun b : (I × ℤˣ × I) => b.1) hb) (Prod.ext hg (congrArg (fun b => b.2.2) hb))
  refine ⟨⟨Equiv.ofBijective af ⟨hai,Finite.surjective_of_injective hai⟩,
    Equiv.ofBijective tf ⟨hti,Finite.surjective_of_injective hti⟩,?_⟩⟩
  intro x
  change reesProduct P x (af x) = some (tf x)
  unfold reesProduct
  change (P x.2.2 (w.alpha (project x)).1).map _ = _
  have hpX := hp (project x)
  change P x.2.2 (w.alpha (project x)).1 = some (entry (project x)) at hpX
  rw [hpX]
  rfl

private noncomputable def residualRows {I : Type} (c : I → ℤˣ) :
    ((I × I) × ℤˣ) ≃ (I × ℤˣ × I) where
  toFun x := (x.1.1,c x.1.2*x.2,x.1.2)
  invFun x := ((x.1,x.2.2),(c x.2.2)⁻¹*x.2.1)
  left_inv := by rintro ⟨⟨i,d⟩,t⟩; simp [←mul_assoc]
  right_inv := by rintro ⟨i,g,d⟩; simp [←mul_assoc]

private noncomputable def residualColumns {I : Type} [Group I] (c : I → ℤˣ) :
    ((I × I) × ℤˣ) ≃ (I × ℤˣ × I) where
  toFun x := (x.1.2,(-c x.1.2)*x.2,x.1.1*x.1.2)
  invFun x := ((x.2.2*x.1⁻¹,x.1),(-c x.1)⁻¹*x.2.1)
  left_inv := by rintro ⟨⟨i,d⟩,t⟩; simp [←mul_assoc]
  right_inv := by rintro ⟨i,g,d⟩; simp [←mul_assoc]

private noncomputable def residualProducts {I : Type} [Group I] :
    ((I × I) × ℤˣ) ≃ (I × ℤˣ × I) where
  toFun x := (x.1.1,-x.2,x.1.1*x.1.2)
  invFun x := ((x.1,x.1⁻¹*x.2.2),-x.2.1)
  left_inv := by rintro ⟨⟨i,d⟩,t⟩; simp [←mul_assoc]
  right_inv := by rintro ⟨i,g,d⟩; simp [←mul_assoc]

private noncomputable def residualSwitch {I : Type} (rho : Equiv.Perm I) :
    Equiv.Perm ((I × I) × ℤˣ) := by
  classical
  exact {
    toFun := fun x => if x.2 = 1 then x else ((x.1.1,rho x.1.2),x.2)
    invFun := fun x => if x.2 = 1 then x else ((x.1.1,rho.symm x.1.2),x.2)
    left_inv := by rintro ⟨⟨i,d⟩,t⟩; by_cases h : t = 1 <;> simp [h]
    right_inv := by rintro ⟨⟨i,d⟩,t⟩; by_cases h : t = 1 <;> simp [h] }

private theorem signed_residual_transversal {I : Type} [Group I]
    (P : I → I → Option ℤˣ) (rho : Equiv.Perm I) (w c : I → ℤˣ)
    (hd : ∀ i, P i i = some 1) (hw : ∀ i, P i (rho i) = some (w i))
    (hc : ∀ i, c (rho i) = -w i * c i) : Nonempty (ReesTransversal P) := by
  let rows := residualRows c
  let cols := residualColumns c
  let prods : ((I × I) × ℤˣ) ≃ (I × ℤˣ × I) := residualProducts
  let sw := residualSwitch rho
  let alpha := (rows.symm.trans sw).trans cols
  let theta := (rows.symm.trans sw).trans prods
  refine ⟨⟨alpha,theta,?_⟩⟩
  intro x
  obtain ⟨⟨⟨i,d⟩,t⟩,rfl⟩ := rows.surjective x
  dsimp only [alpha,theta,Equiv.trans_apply]
  simp only [rows.symm_apply_apply]
  change reesProduct P (rows ((i,d),t)) (cols (sw ((i,d),t))) =
    some (prods (sw ((i,d),t)))
  obtain rfl | rfl := Int.units_eq_one_or t
  · simp [reesProduct,rows,cols,prods,sw,residualRows,residualColumns,
      residualProducts,residualSwitch,hd,mul_assoc]
  · simp [reesProduct,rows,cols,prods,sw,residualRows,residualColumns,
      residualProducts,residualSwitch,hw,hc,mul_comm,mul_left_comm,mul_assoc]

private theorem pair_triangle_potential {I : Type} [LinearOrder I]
    (rho : Equiv.Perm I) (z : I) (w : I → ℤˣ)
    (hn : ∀ x, rho x ≠ x) (h3 : rho (rho (rho z)) = z)
    (h20 : rho (rho z) ≠ z)
    (h2 : ∀ x, x ≠ z → x ≠ rho z → x ≠ rho (rho z) → rho (rho x) = x)
    (hw2 : ∀ x, x ≠ z → x ≠ rho z → x ≠ rho (rho z) → w x * w (rho x) = 1)
    (hw3 : w z * w (rho z) * w (rho (rho z)) = -1) :
    ∃ c : I → ℤˣ, ∀ x, c (rho x) = -w x * c x := by
  classical
  let c : I → ℤˣ := fun x => if x = z then 1 else
    if x = rho z then -w z else if x = rho (rho z) then w z * w (rho z) else
    if x < rho x then 1 else -w (rho x)
  have h10 := hn z
  have h21 := hn (rho z)
  have hc0 : c z = 1 := ite_eq_left rfl
  have hc1 : c (rho z) = -w z := by simp [c,h10]
  have hc2 : c (rho (rho z)) = w z * w (rho z) := by simp [c,h20,h21]
  refine ⟨c,?_⟩
  intro x
  by_cases hx0 : x = z
  · subst x
    rw [hc1,hc0,mul_one]
  by_cases hx1 : x = rho z
  · subst x
    rw [hc2,hc1]
    simp [mul_comm]
  by_cases hx2 : x = rho (rho z)
  · subst x
    rw [h3,hc0,hc2]
    calc
      1 = -(w z * w (rho z) * w (rho (rho z))) := by rw [hw3]; simp
      _ = -w (rho (rho z)) * (w z * w (rho z)) := by
        simp [mul_comm,mul_left_comm,mul_assoc]
  have hy0 : rho x ≠ z := fun h => hx2 (rho.injective (h.trans h3.symm))
  have hy1 : rho x ≠ rho z := fun h => hx0 (rho.injective h)
  have hy2 : rho x ≠ rho (rho z) := fun h => hx1 (rho.injective h)
  have hs := h2 x hx0 hx1 hx2
  by_cases hl : x < rho x
  · have hl' : ¬rho x < x := not_lt.mpr hl.le
    simp [c,hx0,hx1,hx2,hy0,hy1,hy2,hl,hs,hl']
  · have hl' : rho x < x := lt_of_le_of_ne (le_of_not_gt hl) (hn x)
    have hp := hw2 x hx0 hx1 hx2
    simp [c,hx0,hx1,hx2,hy0,hy1,hy2,hl,hs,hl',hp]


private theorem rees_group_transport {I G Q : Type} [Group G] [Group Q]
    (e : G ≃* Q) (P : I → I → Option G)
    (w : ReesTransversal (fun d j => (P d j).map e)) : Nonempty (ReesTransversal P) := by
  let t : (I × G × I) ≃ (I × Q × I) := (Equiv.refl I).prodCongr (e.toEquiv.prodCongr (Equiv.refl I))
  let alpha := (t.trans w.alpha).trans t.symm
  let theta := (t.trans w.theta).trans t.symm
  have hm (x y : (I × G × I)) :
      (reesProduct P x y).map t =
        reesProduct (fun d j => (P d j).map e) (t x) (t y) := by
    cases hp : P x.2.2 y.1 with
    | none => simp [reesProduct,t,hp]
    | some p => simp [reesProduct,t,hp,map_mul]
  refine ⟨⟨alpha,theta,?_⟩⟩
  intro x
  apply (Equiv.optionCongr t).injective
  change (reesProduct P x (alpha x)).map t = some (t (theta x))
  rw [hm]
  have ha : t (alpha x) = w.alpha (t x) := (Equiv.eq_symm_apply t).mp rfl
  have ht : t (theta x) = w.theta (t x) := (Equiv.eq_symm_apply t).mp rfl
  rw [ha,ht]
  exact w.product (t x)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private noncomputable def symmetricTwoSignEquiv : Equiv.Perm (Fin 2) ≃* ℤˣ :=
  MulEquiv.ofBijective (Equiv.Perm.sign : Equiv.Perm (Fin 2) →* ℤˣ) (by decide)

private theorem oneTriangle_potential {I : Type} [Fintype I]
    (rho : OneTrianglePermutation I) (w : I → ℤˣ)
    (hw2 : ∀ x, x ∉ rho.triangle → w x * w (rho.perm x) = 1)
    (hw3 : ∀ x, x ∈ rho.triangle →
      w x * w (rho.perm x) * w (rho.perm (rho.perm x)) = -1) :
    ∃ c : I → ℤˣ, ∀ x, c (rho.perm x) = -w x * c x := by
  classical
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  have htpos : 0 < Nat.card rho.triangle := by rw [rho.triangleCard]; decide
  obtain ⟨⟨z,hz⟩⟩ := (Nat.card_pos_iff.mp htpos).1
  have h3 := rho.triangleCube z hz
  have h20 : rho.perm (rho.perm z) ≠ z := by
    intro he
    have hh := congrArg rho.perm he
    exact rho.noFixed z (hh.symm.trans h3)
  have h10 := rho.noFixed z
  have h21 := rho.noFixed (rho.perm z)
  let T : Finset I := {z,rho.perm z,rho.perm (rho.perm z)}
  have hsub : (↑T : Set I) ⊆ rho.triangle := by
    intro x hx
    have h1 := (rho.triangleInvariant z).mp hz
    have h2 := (rho.triangleInvariant (rho.perm z)).mp h1
    simp only [T,Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hz
    · exact h1
    · exact h2
  have hTcard : Fintype.card (↑T : Set I) = 3 := by
    simp [T,Ne.symm h10,Ne.symm h20,Ne.symm h21]
  have htricard : Fintype.card rho.triangle = 3 := by
    simpa only [Nat.card_eq_fintype_card] using rho.triangleCard
  have heq : (↑T : Set I) = rho.triangle := Set.eq_of_subset_of_card_le hsub (by
    rw [htricard,hTcard])
  have hout (x : I) (h0 : x ≠ z) (h1 : x ≠ rho.perm z)
      (h2 : x ≠ rho.perm (rho.perm z)) : x ∉ rho.triangle := by
    intro hx
    have hxT : x ∈ T := by change x ∈ (↑T : Set I); rw [heq]; exact hx
    simp [T,h0,h1,h2] at hxT
  exact pair_triangle_potential rho.perm z w rho.noFixed h3 h20
    (fun x h0 h1 h2 => rho.outsideSquare x (hout x h0 h1 h2))
    (fun x h0 h1 h2 => hw2 x (hout x h0 h1 h2)) (hw3 z hz)

private theorem finite_signed_residual_transversal {I : Type} [Fintype I]
    (P : I → I → Option ℤˣ) (rho : OneTrianglePermutation I) (w : I → ℤˣ)
    (hd : ∀ i, P i i = some 1) (hw : ∀ i, P i (rho.perm i) = some (w i))
    (hw2 : ∀ x, x ∉ rho.triangle → w x * w (rho.perm x) = 1)
    (hw3 : ∀ x, x ∈ rho.triangle →
      w x * w (rho.perm x) * w (rho.perm (rho.perm x)) = -1) :
    Nonempty (ReesTransversal P) := by
  classical
  have htpos : 0 < Nat.card rho.triangle := by rw [rho.triangleCard]; decide
  obtain ⟨⟨z,hz⟩⟩ := (Nat.card_pos_iff.mp htpos).1
  letI : Nonempty I := ⟨z⟩
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  let e : I ≃ Multiplicative (ZMod (Fintype.card I)) :=
    (Fintype.equivFin I).trans ((ZMod.finEquiv (Fintype.card I)).toEquiv.trans Multiplicative.ofAdd)
  letI : Group I := e.group
  obtain ⟨c,hc⟩ := oneTriangle_potential rho w hw2 hw3
  exact signed_residual_transversal P rho.perm w c hd hw hc

noncomputable def halfMatrix {n r : ℕ} (O : RankedHalf (Fin n) r) :
    HalfDiagram n r → HalfDiagram n r → Option (Equiv.Perm (Fin r)) :=
  fun D E => coordinateSandwich O (halfRanked D) (halfRanked E)

private theorem half_signed_quotient_transversal {n r : ℕ} (O : RankedHalf (Fin n) r)
    (w : SignedHalfCycles n r) :
    Nonempty (ReesTransversal (fun D E => (halfMatrix O D E).map Equiv.Perm.sign)) := by
  apply finite_signed_residual_transversal _ w.cycles
    (fun D => Equiv.Perm.sign (halfCanonicalEntry (w.transport D)))
  · intro D
    simp only [halfMatrix,coordinateSandwich_diagonal,Option.map_some,map_one]
  · intro D
    rw [halfMatrix,halfCanonicalEntry_sandwich O D (w.cycles.perm D) (w.transport D)]
    rfl
  · exact canonical_cycle_two_sign w
  · exact canonical_cycle_three_sign w

theorem rank_two_signed_factor (k : ℕ) (O : RankedHalf (Fin (6+4*k)) 2) :
    Nonempty (ReesTransversal (halfMatrix O)) := by
  obtain ⟨w⟩ := rank_two_signed_half_cycles k
  obtain ⟨v⟩ := half_signed_quotient_transversal O w
  exact rees_group_transport symmetricTwoSignEquiv (halfMatrix O) v

theorem rank_three_signed_factor (k : ℕ) (O : RankedHalf (Fin (7+4*k)) 3) :
    Nonempty (ReesTransversal (halfMatrix O)) := by
  obtain ⟨w⟩ := rank_three_signed_half_cycles k
  obtain ⟨v⟩ := half_signed_quotient_transversal O w
  exact rees_s3_lift (halfMatrix O) v

end D5.S3.Combinatorics.PerfectMatchings.AraujoSignedFactorLifting
