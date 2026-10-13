/- GID: D5/S3/ConceptDynamics/Coding/ResetStandardBeamGeometry
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetStandardBeamGeometry
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: The native even reset action computed from actual numbered whole-ray images. -/
import D5.S3.ConceptDynamics.Coding.ResetAlternatingHistories
import D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms
import D5.S3.ConceptDynamics.Coding.StandardBeamCoordinates
import D5.S3.ConceptDynamics.Coding.StandardTaggedBeams
import D5.S3.ConceptDynamics.Coding.StandardBeamPushforward
import D5.S3.ConceptDynamics.Coding.NativeIntegralRowTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetStandardBeamGeometry

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap (GroupMat Edge)
open D5.S3.ConceptDynamics.Coding.FixedBlockRigidity (expandedGraph)
open D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open D5.S3.ConceptDynamics.Coding.StandardBeamGeometry
open D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms
open D5.S3.ConceptDynamics.Coding.StandardBeamEndpointRows
open D5.S3.ConceptDynamics.Coding.StandardBeamColimitCuts
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
  (DimensionGroup VertexModule transition vertex stationaryTransition actual_expansion_adjacency)
open scoped BigOperators Matrix

abbrev ResetGraph (q : ℕ) := expandedGraph (resetMatrix q)
abbrev ResetHistory (q : ℕ) := History (ResetGraph q)

/-- Exact concrete domain: every homeomorphism commuting with UNIT shift. -/
abbrev ResetFullAut (q : ℕ) := FullAut (ResetGraph q)

/-- The real even H is a member of the full domain. This consumes both the
constructed square-lift H and its equality with the original finite table. -/
def evenAut (q : ℕ) (hq : 0 < q) (he : Even q) : ResetFullAut q := by
  refine ⟨resetAlternatingWholeRayHomeomorph q hq he, ?_⟩
  intro x
  change (Alternating.resetNumberedData q hq).squares.H
      (Alternating.resetFiniteForgetting q hq he)
      (FiniteWindowTableCriterion.shift (ResetGraph q) x) =
    FiniteWindowTableCriterion.shift (ResetGraph q)
      ((Alternating.resetNumberedData q hq).squares.H
        (Alternating.resetFiniteForgetting q hq he) x)
  rw [reset_generic_H_eq_applyTable q hq he, reset_generic_H_eq_applyTable q hq he]
  exact FiniteWindowTableCriterion.applyTable_shift _ _ _ _ x

/-- Genuine image-beam construction for EVERY h and EVERY positive q,
including the deterministic q=1 graph. -/
def resetImageBeam (q : ℕ) (hq : 0 < q) (h : ResetFullAut q) (U : Beam (ResetGraph q)) :
    Beam (ResetGraph q) :=
  imageBeam (ResetGraph q) (Alternating.reset_expanded_essential q hq) h U

/-- The essential choices produce the actual stage-basis past, at every integer cut. -/
def resetBasisHistory (q : ℕ) (hq : 0 < q) (p : Fin q × Sign) (n : ℤ) : ResetHistory q :=
  vertexHistory (ResetGraph q) (Alternating.reset_expanded_essential q hq) p n

private theorem counted_edge_ext {q : ℕ} {M : GroupMat Sign q q} (e f : Edge M)
    (hs : e.source = f.source) (ht : e.target = f.target) (hl : e.label = f.label)
    (hn : e.number.val = f.number.val) : e = f := by
  rcases e with ⟨i, j, g, a⟩
  rcases f with ⟨i', j', g', b⟩
  dsimp only at hs ht hl hn
  subst i'
  subst j'
  subst g'
  exact congrArg (fun a => Edge.mk i j g a) (Fin.ext hn)

/-- A full numbered edge fiber, not just a cardinality assertion about a matrix. -/
def expandedEdgeFiberEquiv {q : ℕ} (M : GroupMat Sign q q) (p t : Fin q × Sign) :
    {r : Edge M × Sign // (expandedGraph M).source r = p ∧
      (expandedGraph M).target r = t} ≃ Fin ((M p.1 t.1).coeff (p.2⁻¹ * t.2)) where
  toFun r := ⟨r.val.1.number.val, by
    have hs := congrArg Prod.fst r.property.1
    have ht := congrArg Prod.fst r.property.2
    have hh := congrArg Prod.snd r.property.1
    have hg := congrArg Prod.snd r.property.2
    change r.val.1.source = p.1 at hs
    change r.val.1.target = t.1 at ht
    change r.val.2 = p.2 at hh
    change r.val.2 * r.val.1.label = t.2 at hg
    have hl : r.val.1.label = p.2⁻¹ * t.2 := by
      have hm : p.2 * r.val.1.label = t.2 := by simpa only [hh] using hg
      calc
        _ = p.2⁻¹ * (p.2 * r.val.1.label) := by simp
        _ = p.2⁻¹ * t.2 := by rw [hm]
    simpa only [hs, ht, hl] using r.val.1.number.isLt⟩
  invFun k := ⟨(⟨p.1, t.1, p.2⁻¹ * t.2, k⟩, p.2), rfl, by
    apply Prod.ext
    · rfl
    · simp [expandedGraph]⟩
  left_inv r := by
    apply Subtype.ext
    apply Prod.ext
    · apply counted_edge_ext
      · exact (congrArg Prod.fst r.property.1).symm
      · exact (congrArg Prod.fst r.property.2).symm
      · have hh := congrArg Prod.snd r.property.1
        have hg := congrArg Prod.snd r.property.2
        change r.val.2 = p.2 at hh
        change r.val.2 * r.val.1.label = t.2 at hg
        change p.2⁻¹ * t.2 = r.val.1.label
        rw [← hg, ← hh]
        simp
      · rfl
    · exact (congrArg Prod.snd r.property.1).symm
  right_inv k := Fin.ext rfl

/-- Counting each actual expanded numbered edge identifies its integer
adjacency with the ORIGINAL native transport's coefficient matrix. -/
theorem expanded_adjacency_eq {q : ℕ} (M : GroupMat Sign q q) :
    adjacency (expandedGraph M) = NativeIntegralRowTransport.expansionMatrix M := by
  classical
  funext p t
  let G := expandedGraph M
  let F := {e : Out G p // G.target e.val = t}
  let e : F ≃ {r : Edge M × Sign // G.source r = p ∧ G.target r = t} := {
    toFun r := ⟨r.val.val, r.val.property, r.property⟩
    invFun r := ⟨⟨r.val, r.property.1⟩, r.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc : Fintype.card F = (M p.1 t.1).coeff (p.2⁻¹ * t.2) := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (e.trans (expandedEdgeFiberEquiv M p t))
  have hcount : adjacency G p t = (Fintype.card F : ℤ) := by
    change (∑ e : Out G p, (Pi.single (G.target e.val) (1 : ℤ) : Fin q × Sign → ℤ)) t = _
    simp only [Finset.sum_apply, Pi.single_apply, F, Fintype.card_subtype,
      Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : G.target e.val = t
    · simp [he]
    · simp [he, Ne.symm he]
  rw [hcount, hc]
  rfl

/-- Literal row transition on the actual graph equals v -> vB of the native
coordinate transport. actual_expansion_adjacency is consumed inside transport_transition. -/
theorem graph_rowTransition_eq {q : ℕ} (M : GroupMat Sign q q) :
    StandardBeamCoordinates.rowTransition (expandedGraph M) =
      NativeIntegralRowTransport.rowTransition M := by
  unfold StandardBeamCoordinates.rowTransition NativeIntegralRowTransport.rowTransition
  rw [expanded_adjacency_eq]

abbrev EvenOut (q : ℕ) (alpha : ResetHistory q) (n : ℤ) :=
  {r : Edge ((1 : GroupMat Sign q q) + resetMatrix q) × Sign //
    (expandedGraph ((1 : GroupMat Sign q q) + resetMatrix q)).source r =
      (expandedGraph (resetMatrix q)).target (alpha.val n)}

/-- SAME-CUT concrete image finiteness. Actual NumberedData, forgetting,
all guards/q2 cases and arbitrary futures are supplied by the imported family. -/
theorem even_image_atCut (q : ℕ) (hq : 0 < q) (he : Even q)
    (alpha : ResetHistory q) (n : ℤ) :
    AtCut (ResetGraph q) ((evenAut q hq he).val '' ray (ResetGraph q) alpha n) n := by
  have h := reset_even_same_cut_whole_rays q hq he alpha n
  change AtCut (ResetGraph q)
    (resetAlternatingWholeRayHomeomorph q hq he '' ray (ResetGraph q) alpha n) n
  have hu : resetAlternatingWholeRayHomeomorph q hq he '' ray (ResetGraph q) alpha n =
      ⋃ r : EvenOut q alpha n, ray (ResetGraph q) (resetRayRepresentative q hq alpha n r) n := h.1
  rw [hu]
  exact atCut_iUnion (ResetGraph q) _ n (fun r =>
    ray_atCut (ResetGraph q) (Alternating.reset_expanded_essential q hq)
      (resetRayRepresentative q hq alpha n r) n)

theorem endpointRow_set_congr {V E : Type*} (G : DirectedMultigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] {U W : Set (History G)} (n : ℤ)
    [Finite (Parts G U n)] [Finite (Parts G W n)] (h : U = W) :
    endpointRow G U n = endpointRow G W n := by
  cases h
  rfl

/-- Concrete actual-image row: every NUMBERED outgoing edge of 1+A
contributes one whole ray at the unchanged cut. -/
theorem even_image_endpointRow (q : ℕ) (hq : 0 < q) (he : Even q)
    (alpha : ResetHistory q) (n : ℤ) :
    letI : Finite (Parts (ResetGraph q)
      ((evenAut q hq he).val '' ray (ResetGraph q) alpha n) n) :=
        (even_image_atCut q hq he alpha n).1
    endpointRow (ResetGraph q) ((evenAut q hq he).val '' ray (ResetGraph q) alpha n) n =
      (Pi.single (endpoint (ResetGraph q) alpha n) 1) ᵥ*
        NativeIntegralRowTransport.expansionMatrix ((1 : GroupMat Sign q q) + resetMatrix q) := by
  classical
  have h := reset_even_same_cut_whole_rays q hq he alpha n
  letI : Finite (Parts (ResetGraph q)
    ((evenAut q hq he).val '' ray (ResetGraph q) alpha n) n) :=
      (even_image_atCut q hq he alpha n).1
  have hu : (evenAut q hq he).val '' ray (ResetGraph q) alpha n =
      ⋃ r : EvenOut q alpha n, ray (ResetGraph q) (resetRayRepresentative q hq alpha n r) n := h.1
  letI : Finite (Parts (ResetGraph q)
      (⋃ r : EvenOut q alpha n, ray (ResetGraph q) (resetRayRepresentative q hq alpha n r) n) n) :=
    (atCut_iUnion (ResetGraph q) _ n (fun r =>
      ray_atCut (ResetGraph q) (Alternating.reset_expanded_essential q hq) _ n)).1
  rw [endpointRow_set_congr (ResetGraph q) n hu]
  rw [endpointRow_disjointUnion (ResetGraph q) (Alternating.reset_expanded_essential q hq)
    (fun r : EvenOut q alpha n => resetRayRepresentative q hq alpha n r) n h.2.2.1]
  rw [← expanded_adjacency_eq, Matrix.single_vecMul]
  simp only [one_smul, Matrix.row, adjacency]
  apply Finset.sum_congr rfl
  intro r _
  exact congrArg (fun p : Fin q × Sign => (Pi.single p (1 : ℤ) : Fin q × Sign → ℤ))
    (h.2.1 r)

/-- The native transition at 1+A is literally id+T over the full Z[C2] row. -/
theorem native_transition_one_add {q : ℕ} (A : GroupMat Sign q q) (z : VertexModule Sign q) :
    transition ((1 : GroupMat Sign q q) + A) z = z + transition A z := by
  change z ᵥ* InertGroupBlockConjugacy.integerMatrix (1 + A) = z + z ᵥ*
    InertGroupBlockConjugacy.integerMatrix A
  rw [map_add, map_one, Matrix.vecMul_add, Matrix.vecMul_one]

private theorem toNative_stage {q : ℕ} (M : GroupMat Sign q q) (N : ℕ)
    (v : NativeIntegralRowTransport.ExpandedRow q) :
    NativeIntegralRowTransport.toNativeLimit M
      (stage (NativeIntegralRowTransport.rowTransition M) N v) =
      stage (transition M) N (NativeIntegralRowTransport.basisEquiv q v) :=
  NativeIntegralRowTransport.toNativeLimit_stage M N v

/-- SAME native stage of the ACTUAL even image of an ACTUAL ray. This is a
geometric computation before a group-completion isomorphism is installed. -/
theorem even_image_native_stage (q : ℕ) (hq : 0 < q) (he : Even q)
    (alpha : ResetHistory q) (N : ℕ) :
    letI : Finite (Parts (ResetGraph q)
      ((evenAut q hq he).val '' ray (ResetGraph q) alpha (N : ℤ)) (N : ℤ)) :=
        (even_image_atCut q hq he alpha (N : ℤ)).1
    NativeIntegralRowTransport.limitEquiv (resetMatrix q)
      (stage (NativeIntegralRowTransport.rowTransition (resetMatrix q)) N
        (endpointRow (ResetGraph q)
          ((evenAut q hq he).val '' ray (ResetGraph q) alpha (N : ℤ)) (N : ℤ))) =
      ((LinearMap.id : Module.End ℤ (DimensionGroup (resetMatrix q))) +
        Theta (transition (resetMatrix q)))
        (stage (transition (resetMatrix q)) N
          (vertex (endpoint (ResetGraph q) alpha (N : ℤ)).1
            (endpoint (ResetGraph q) alpha (N : ℤ)).2)) := by
  let p := endpoint (ResetGraph q) alpha (N : ℤ)
  letI : Finite (Parts (ResetGraph q)
    ((evenAut q hq he).val '' ray (ResetGraph q) alpha (N : ℤ)) (N : ℤ)) :=
      (even_image_atCut q hq he alpha (N : ℤ)).1
  rw [even_image_endpointRow]
  change NativeIntegralRowTransport.toNativeLimit (resetMatrix q)
      (stage (NativeIntegralRowTransport.rowTransition (resetMatrix q)) N
        (NativeIntegralRowTransport.rowTransition (1 + resetMatrix q)
          (NativeIntegralRowTransport.rowVertex p.1 p.2))) = _
  rw [toNative_stage,
    NativeIntegralRowTransport.transport_transition]
  have hv : NativeIntegralRowTransport.basisEquiv q
      (NativeIntegralRowTransport.rowVertex p.1 p.2) = vertex p.1 p.2 := by
    rw [← NativeIntegralRowTransport.decode_vertex]
    exact NativeIntegralRowTransport.encode_decode _
  rw [hv, native_transition_one_add, map_add, LinearMap.add_apply, LinearMap.id_apply,
    Theta_stage]

/-- Original graph row colimit to the original native DimensionGroup,
using equality of actual numbered adjacency and the coefficient isomorphism. -/
def resetRowLimitEquiv (q : ℕ) :
    StandardBeamCoordinates.RowLimit (ResetGraph q) ≃ₗ[ℤ] DimensionGroup (resetMatrix q) :=
  (LinearEquiv.cast (R := ℤ)
    (M := fun T : Module.End ℤ (NativeIntegralRowTransport.ExpandedRow q) =>
      InertGroupBlockConjugacy.StationaryModule T)
    (graph_rowTransition_eq (resetMatrix q))).trans
      (NativeIntegralRowTransport.limitEquiv (resetMatrix q))

theorem resetRowLimitEquiv_stage (q N : ℕ) (v : Fin q × Sign → ℤ) :
    resetRowLimitEquiv q (stage (StandardBeamCoordinates.rowTransition (ResetGraph q)) N v) =
      stage (transition (resetMatrix q)) N (NativeIntegralRowTransport.basisEquiv q v) := by
  rw [resetRowLimitEquiv, LinearEquiv.trans_apply, cast_stage]
  exact NativeIntegralRowTransport.toNativeLimit_stage (resetMatrix q) N v

theorem resetRowLimitEquiv_intStage (q : ℕ) (n : ℤ) (v : Fin q × Sign → ℤ) :
    resetRowLimitEquiv q (intStage (StandardBeamCoordinates.rowTransition (ResetGraph q)) n v) =
      intStage (transition (resetMatrix q)) n (NativeIntegralRowTransport.basisEquiv q v) := by
  rw [resetRowLimitEquiv, LinearEquiv.trans_apply, cast_intStage]
  change NativeIntegralRowTransport.toNativeLimit (resetMatrix q)
      (stage (NativeIntegralRowTransport.rowTransition (resetMatrix q)) n.toNat
        (((NativeIntegralRowTransport.rowTransition (resetMatrix q)) ^ (-n).toNat) v)) = _
  simp only [stage, NativeIntegralRowTransport.toNativeLimit_stage,
    NativeIntegralRowTransport.transport_power]
  rfl

/-- An intrinsic coordinate of an actual beam, independent of its selected cut.
This is a function on actual subsets, used by the group-completion equivalence in StandardBeamIdentification. -/
def resetBeamCoordinate (q : ℕ) (U : Beam (ResetGraph q)) : DimensionGroup (resetMatrix q) :=
  resetRowLimitEquiv q (StandardBeamCoordinates.beamCoordinate (ResetGraph q) U)

def resetRayBeam (q : ℕ) (hq : 0 < q) (alpha : ResetHistory q) (n : ℤ) : Beam (ResetGraph q) :=
  ⟨ray (ResetGraph q) alpha n,
    n, ray_atCut (ResetGraph q) (Alternating.reset_expanded_essential q hq) alpha n⟩

/-- An actual ray at ANY integer cut is the original native vertex class. -/
theorem resetBeamCoordinate_ray (q : ℕ) (hq : 0 < q) (alpha : ResetHistory q) (n : ℤ) :
    resetBeamCoordinate q (resetRayBeam q hq alpha n) =
      intStage (transition (resetMatrix q)) n
        (vertex (endpoint (ResetGraph q) alpha n).1 (endpoint (ResetGraph q) alpha n).2) := by
  unfold resetBeamCoordinate
  rw [StandardBeamCoordinates.beamCoordinate_at (ResetGraph q)
      (Alternating.reset_expanded_essential q hq) _ n
        (ray_atCut (ResetGraph q) (Alternating.reset_expanded_essential q hq) alpha n)]
  change resetRowLimitEquiv q
    (StandardBeamCoordinates.coordinateAt (ResetGraph q) (ray (ResetGraph q) alpha n) n
      (ray_atCut (ResetGraph q) (Alternating.reset_expanded_essential q hq) alpha n)) = _
  rw [StandardBeamCoordinates.coordinateAt_ray (ResetGraph q)
    (Alternating.reset_expanded_essential q hq), resetRowLimitEquiv_intStage]
  congr 1
  change NativeIntegralRowTransport.basisEquiv q
    (NativeIntegralRowTransport.rowVertex (endpoint (ResetGraph q) alpha n).1
      (endpoint (ResetGraph q) alpha n).2) = _
  rw [← NativeIntegralRowTransport.decode_vertex]
  exact NativeIntegralRowTransport.encode_decode _

/-- Shift of the actual ray SET is sent to true Theta, including n=0 and the
negative geometric cut -1. This does not yet assert rho(S) on a beam group. -/
theorem reset_actual_shift_ray_coordinate (q : ℕ) (hq : 0 < q) (alpha : ResetHistory q) (n : ℤ) :
    let U : Beam (ResetGraph q) :=
      ⟨FiniteWindowTableCriterion.shift (ResetGraph q) '' ray (ResetGraph q) alpha n, by
        rw [shift_ray]
        exact ⟨n - 1, ray_atCut (ResetGraph q) (Alternating.reset_expanded_essential q hq)
          (FiniteWindowTableCriterion.shift (ResetGraph q) alpha) (n - 1)⟩⟩
    resetBeamCoordinate q U = Theta (transition (resetMatrix q))
      (resetBeamCoordinate q (resetRayBeam q hq alpha n)) := by
  dsimp only
  have he : (⟨FiniteWindowTableCriterion.shift (ResetGraph q) '' ray (ResetGraph q) alpha n,
      by rw [shift_ray]; exact ⟨n - 1, ray_atCut (ResetGraph q)
        (Alternating.reset_expanded_essential q hq) _ _⟩⟩ : Beam (ResetGraph q)) =
      resetRayBeam q hq (FiniteWindowTableCriterion.shift (ResetGraph q) alpha) (n - 1) := by
    apply Subtype.ext
    exact shift_ray (ResetGraph q) alpha n
  rw [he, resetBeamCoordinate_ray, resetBeamCoordinate_ray, shift_ray_endpoint, intStage_shift]

/-- REAL concrete group-completion consumer: the actual even image beam
is equivalent to its disjoint tagged numbered whole-ray components. -/
theorem even_image_tagged_group (q : ℕ) (hq : 0 < q) (he : Even q)
    (alpha : ResetHistory q) (n : ℤ) :
    let hG := Alternating.reset_expanded_essential q hq
    let I := EvenOut q alpha n
    let W : I → Beam (ResetGraph q) := fun r =>
      resetRayBeam q hq (resetRayRepresentative q hq alpha n r) n
    StandardTaggedBeams.objectGroup (ResetGraph q) hG
      (StandardTaggedBeams.singleton (ResetGraph q)
        (resetImageBeam q hq (evenAut q hq he) (resetRayBeam q hq alpha n))) =
      StandardTaggedBeams.objectGroup (ResetGraph q) hG
        (StandardTaggedBeams.family (ResetGraph q) W) := by
  have hs := reset_even_same_cut_whole_rays q hq he alpha n
  have hu : resetImageBeam q hq (evenAut q hq he) (resetRayBeam q hq alpha n) =
      (⟨⋃ r : EvenOut q alpha n,
        ray (ResetGraph q) (resetRayRepresentative q hq alpha n r) n,
        n, atCut_iUnion (ResetGraph q) _ n (fun r =>
          ray_atCut (ResetGraph q) (Alternating.reset_expanded_essential q hq) _ n)⟩ :
          Beam (ResetGraph q)) := by
    apply Subtype.ext
    exact hs.1
  dsimp only
  rw [hu]
  exact StandardTaggedBeams.disjointUnion_group (ResetGraph q)
    (Alternating.reset_expanded_essential q hq)
    (fun r : EvenOut q alpha n => resetRayRepresentative q hq alpha n r) n hs.2.2.1

/-- F is concretely consumed on the actual reset image object. This is the
forward Grothendieck-to-row map; its inverse is in StandardBeamIdentification. -/
theorem even_image_F_native (q : ℕ) (hq : 0 < q) (he : Even q)
    (alpha : ResetHistory q) (N : ℕ) :
    resetRowLimitEquiv q
      (StandardTaggedBeams.F (ResetGraph q) (Alternating.reset_expanded_essential q hq)
        (StandardTaggedBeams.objectGroup (ResetGraph q) (Alternating.reset_expanded_essential q hq)
          (StandardTaggedBeams.singleton (ResetGraph q)
            (resetImageBeam q hq (evenAut q hq he) (resetRayBeam q hq alpha (N : ℤ)))))) =
      ((LinearMap.id : Module.End ℤ (DimensionGroup (resetMatrix q))) +
        Theta (transition (resetMatrix q)))
        (stage (transition (resetMatrix q)) N
          (vertex (endpoint (ResetGraph q) alpha (N : ℤ)).1
            (endpoint (ResetGraph q) alpha (N : ℤ)).2)) := by
  let G := ResetGraph q
  let hG := Alternating.reset_expanded_essential q hq
  let I := EvenOut q alpha (N : ℤ)
  let W : I → Beam G := fun r =>
    resetRayBeam q hq (resetRayRepresentative q hq alpha (N : ℤ) r) (N : ℤ)
  have hn : StandardTaggedBeams.Normalized G (StandardTaggedBeams.family G W) (N : ℤ) :=
    fun r => ray_atCut G hG _ (N : ℤ)
  letI (r : I) : Finite (Parts G (W r).val (N : ℤ)) := (hn r).1
  letI (r : I) : Finite (Parts G
    (ray G (resetRayRepresentative q hq alpha (N : ℤ) r) (N : ℤ)) (N : ℤ)) :=
      (ray_atCut G hG _ (N : ℤ)).1
  letI : Finite (Parts G
    ((evenAut q hq he).val '' ray G alpha (N : ℤ)) (N : ℤ)) :=
      (even_image_atCut q hq he alpha (N : ℤ)).1
  have hs := reset_even_same_cut_whole_rays q hq he alpha (N : ℤ)
  have hr : StandardTaggedBeams.row G (StandardTaggedBeams.family G W) (N : ℤ) hn =
      endpointRow G ((evenAut q hq he).val '' ray G alpha (N : ℤ)) (N : ℤ) := by
    rw [StandardTaggedBeams.row_byTag]
    rw [show StandardTaggedBeams.instFintypeTag G (StandardTaggedBeams.family G W) =
      inferInstanceAs (Fintype I) from Subsingleton.elim _ _]
    change (∑ r : I, endpointRow G
      (ray G (resetRayRepresentative q hq alpha (N : ℤ) r) (N : ℤ)) (N : ℤ)) = _
    simp_rw [endpointRow_ray G hG]
    have hu : (evenAut q hq he).val '' ray G alpha (N : ℤ) =
        ⋃ r : I, ray G (resetRayRepresentative q hq alpha (N : ℤ) r) (N : ℤ) := hs.1
    letI : Finite (Parts G
      (⋃ r : I, ray G (resetRayRepresentative q hq alpha (N : ℤ) r) (N : ℤ)) (N : ℤ)) :=
      (atCut_iUnion G _ (N : ℤ) (fun r => ray_atCut G hG _ (N : ℤ))).1
    rw [endpointRow_set_congr G (N : ℤ) hu,
      endpointRow_disjointUnion G hG _ (N : ℤ) hs.2.2.1]
  rw [even_image_tagged_group q hq he alpha (N : ℤ), StandardTaggedBeams.F_objectGroup]
  rw [StandardTaggedBeams.objectValue_at G hG (StandardTaggedBeams.family G W) (N : ℤ) hn,
    intStage_nat, resetRowLimitEquiv_stage, hr]
  have ht := even_image_native_stage q hq he alpha N
  change NativeIntegralRowTransport.toNativeLimit (resetMatrix q)
    (stage (NativeIntegralRowTransport.rowTransition (resetMatrix q)) N
      (endpointRow G ((evenAut q hq he).val '' ray G alpha (N : ℤ)) (N : ℤ))) = _ at ht
  rw [toNative_stage] at ht
  exact ht


/-- The FULL representation is already implemented on the GEOMETRIC integer
beam group, for every positive q. Its conjugation onto DimensionGroup is consumed by
ResetFullStandardBeamRepresentation.nativeEquiv and rho. -/
def resetFullBeamRepresentation (q : ℕ) (hq : 0 < q) :
    ResetFullAut q →*
      (StandardTaggedBeams.BeamGroup (ResetGraph q) (Alternating.reset_expanded_essential q hq) ≃ₗ[ℤ]
        StandardTaggedBeams.BeamGroup (ResetGraph q) (Alternating.reset_expanded_essential q hq)) :=
  StandardBeamPushforward.fullBeamRepresentation (ResetGraph q)
    (Alternating.reset_expanded_essential q hq)

/-- Concrete action calculation: actual H_q acts, then the REAL forward
geometric F followed by exact native transport gives id+Theta at every ray stage. -/
theorem reset_fullBeam_even_stage (q : ℕ) (hq : 0 < q) (he : Even q)
    (alpha : ResetHistory q) (N : ℕ) :
    resetRowLimitEquiv q
      (StandardTaggedBeams.F (ResetGraph q) (Alternating.reset_expanded_essential q hq)
        (resetFullBeamRepresentation q hq (evenAut q hq he)
          (StandardTaggedBeams.objectGroup (ResetGraph q) (Alternating.reset_expanded_essential q hq)
            (StandardTaggedBeams.singleton (ResetGraph q) (resetRayBeam q hq alpha (N : ℤ)))))) =
      ((LinearMap.id : Module.End ℤ (DimensionGroup (resetMatrix q))) +
        Theta (transition (resetMatrix q)))
        (stage (transition (resetMatrix q)) N
          (vertex (endpoint (ResetGraph q) alpha (N : ℤ)).1
            (endpoint (ResetGraph q) alpha (N : ℤ)).2)) := by
  rw [resetFullBeamRepresentation, StandardBeamPushforward.fullBeamRepresentation_object]
  exact even_image_F_native q hq he alpha N

end D5.S3.ConceptDynamics.Coding.ResetStandardBeamGeometry
