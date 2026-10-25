import CFMPGenericEndpoint1147Transient
import D5.S3.Geometry.Hyperideal.S4OppositePairAction
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions
  (RawFacePairing Occurrence faceEdge edgeVertices)
open D5.S3.Geometry.Hyperideal.S4OppositePairAction (edgeIndex)
open D5.S3.Geometry.Gluing.ActualLinkCornerChains (Dart)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate (sigma)
open D5.S3.Geometry.Gluing.RawFaceEndpointCandidate
open private sigma_endpoint_iff sigma_inverse paired_twice
  from CFMPRawFaceCapSlice1053Transient
variable {T : Type*}
-- All declarations are temporary exact checks, with no canonical admission claim.
abbrev OrderedEnd (T : Type*) := {d : Dart T // d.1.2 ≠ d.2}
def occ (d : Dart T) : Occurrence T := (d.1.1, edgeIndex d.1.2 d.2)
def swap (d : Dart T) : Dart T := ((d.1.1,d.2),d.1.2)
private theorem index_pair_iff (j k : Fin 4) (hjk : j ≠ k) (e : Fin 6) :
    edgeIndex j k = e ↔
      (j = (edgeVertices e).1 ∧ k = (edgeVertices e).2) ∨
      (j = (edgeVertices e).2 ∧ k = (edgeVertices e).1) := by
  fin_cases j <;> fin_cases k <;> fin_cases e <;> simp_all [edgeIndex,edgeVertices]
private theorem face_excludes_endpoints (f : Fin 4) (n : Fin 3) :
    f ≠ (edgeVertices (faceEdge f n)).1 ∧ f ≠ (edgeVertices (faceEdge f n)).2 := by
  fin_cases f <;> fin_cases n <;> decide
private theorem slot_for_pair (f j k : Fin 4) (hjk : j ≠ k) (hfj : f ≠ j) (hfk : f ≠ k) :
    ∃ n : Fin 3, edgeIndex j k = faceEdge f n := by
  fin_cases f <;> fin_cases j <;> fin_cases k <;>
    simp_all [edgeIndex,faceEdge,Fin.exists_fin_succ]
private theorem face_ne_of_index (f j k : Fin 4) (n : Fin 3) (hjk : j ≠ k)
    (h : edgeIndex j k = faceEdge f n) : f ≠ j ∧ f ≠ k := by
  rcases (index_pair_iff j k hjk _).mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact face_excludes_endpoints f n
  · exact ⟨(face_excludes_endpoints f n).2,(face_excludes_endpoints f n).1⟩
private theorem index_of_membership (j k : Fin 4) (e : Fin 6) (hjk : j ≠ k)
    (hj : j = (edgeVertices e).1 ∨ j = (edgeVertices e).2)
    (hk : k = (edgeVertices e).1 ∨ k = (edgeVertices e).2) : edgeIndex j k = e := by
  apply (index_pair_iff j k hjk e).mpr
  rcases hj with hj | hj <;> rcases hk with hk | hk
  · exact False.elim (hjk (hj.trans hk.symm))
  · exact Or.inl ⟨hj,hk⟩
  · exact Or.inr ⟨hj,hk⟩
  · exact False.elim (hjk (hj.trans hk.symm))
private theorem transported_index (P : RawFacePairing T) (x : T × Fin 4) (n : Fin 3)
    (j k : Fin 4) (hjk : j ≠ k) (h : edgeIndex j k = faceEdge x.2 n) :
    edgeIndex (sigma P x j) (sigma P x k) =
      faceEdge (P.facePair x).2 (P.faceMap x n) := by
  have hp := (index_pair_iff j k hjk _).mp h
  have hj : j = (edgeVertices (faceEdge x.2 n)).1 ∨
      j = (edgeVertices (faceEdge x.2 n)).2 := hp.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hk : k = (edgeVertices (faceEdge x.2 n)).1 ∨
      k = (edgeVertices (faceEdge x.2 n)).2 := hp.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
  exact index_of_membership _ _ _ ((sigma P x).injective.ne hjk)
    ((sigma_endpoint_iff P x n j).mp hj) ((sigma_endpoint_iff P x n k).mp hk)
theorem dart_step_occ (P : RawFacePairing T) {d e : Dart T}
    (hd : d.1.2 ≠ d.2) (h : DartStep P d e) : P.edgeStep (occ d) (occ e) := by
  obtain ⟨f,hfj,hfk,rfl⟩ := h
  obtain ⟨n,hn⟩ := slot_for_pair f d.1.2 d.2 hd hfj hfk
  refine ⟨(d.1.1,f),n,?_,?_⟩
  · change (d.1.1,edgeIndex d.1.2 d.2) = (d.1.1,faceEdge f n)
    exact Prod.ext rfl hn
  · change ((P.facePair (d.1.1,f)).1,
      edgeIndex (sigma P (d.1.1,f) d.1.2) (sigma P (d.1.1,f) d.2)) = _
    exact Prod.ext rfl (transported_index P (d.1.1,f) n d.1.2 d.2 hd hn)
theorem dart_related_unequal (P : RawFacePairing T) {d e : Dart T}
    (h : DartRelated P d e) : d.1.2 ≠ d.2 ↔ e.1.2 ≠ e.2 := by
  constructor
  · intro hd
    exact ((dart_chain_flags P _ h).mp ⟨hd,rfl⟩).1
  · intro he
    exact ((dart_chain_flags P _ h.symm).mp ⟨he,rfl⟩).1
theorem dart_related_occ (P : RawFacePairing T) {d e : Dart T}
    (hd : d.1.2 ≠ d.2) (h : DartRelated P d e) :
    Relation.EqvGen P.edgeStep (occ d) (occ e) := by
  have lift : ∀ {d e : Dart T}, DartRelated P d e → d.1.2 ≠ d.2 →
      Relation.EqvGen P.edgeStep (occ d) (occ e) := by
    intro d e hde
    induction hde with
    | rel d e h => exact fun hd => Relation.EqvGen.rel _ _ (dart_step_occ P hd h)
    | refl d => exact fun _ => Relation.EqvGen.refl _
    | symm d e h ih => exact fun hd => (ih ((dart_related_unequal P h).mpr hd)).symm
    | trans d e f h _ ih₁ ih₂ =>
      exact fun hd => (ih₁ hd).trans _ _ _ (ih₂ ((dart_related_unequal P h).mp hd))
  exact lift h hd
/-- The lift keeps the given original face and edge slot, not merely adjacency. -/
theorem edge_step_lift_port (P : RawFacePairing T) (x : T × Fin 4) (n : Fin 3)
    (d : OrderedEnd T) (hi : occ d.val = (x.1,faceEdge x.2 n)) :
    ∃ e : OrderedEnd T, x.2 ≠ d.val.1.2 ∧ x.2 ≠ d.val.2 ∧
      e.val = dartMove P x.2 d.val ∧
      occ e.val = ((P.facePair x).1,faceEdge (P.facePair x).2 (P.faceMap x n)) := by
  rcases x with ⟨t,f⟩
  have ht : d.val.1.1 = t := congrArg Prod.fst hi
  subst t
  have hn : edgeIndex d.val.1.2 d.val.2 = faceEdge f n := congrArg Prod.snd hi
  have hf := face_ne_of_index f d.val.1.2 d.val.2 n d.property hn
  let e : OrderedEnd T := ⟨dartMove P f d.val,
    (sigma P (d.val.1.1,f)).injective.ne d.property⟩
  refine ⟨e,hf.1,hf.2,rfl,?_⟩
  change ((P.facePair (d.val.1.1,f)).1,
    edgeIndex (sigma P (d.val.1.1,f) d.val.1.2) (sigma P (d.val.1.1,f) d.val.2)) = _
  exact Prod.ext rfl (transported_index P (d.val.1.1,f) n _ _ d.property hn)
theorem edge_step_lift (P : RawFacePairing T) (d : OrderedEnd T) (o : Occurrence T)
    (h : P.edgeStep (occ d.val) o) :
    ∃ e : OrderedEnd T, DartStep P d.val e.val ∧ occ e.val = o := by
  obtain ⟨x,n,hi,ho⟩ := h
  obtain ⟨e,hfj,hfk,he,hocc⟩ := edge_step_lift_port P x n d hi
  exact ⟨e,⟨x.2,hfj,hfk,he⟩,hocc.trans ho.symm⟩
theorem edge_step_symm (P : RawFacePairing T) {i j : Occurrence T}
    (h : P.edgeStep i j) : P.edgeStep j i := by
  obtain ⟨x,n,rfl,rfl⟩ := h
  refine ⟨P.facePair x,P.faceMap x n,rfl,?_⟩
  rw [paired_twice P x,P.mapInverse]
theorem dart_move_reverse (P : RawFacePairing T) (d : Dart T) (f : Fin 4) :
    dartMove P (P.facePair (d.1.1,f)).2 (dartMove P f d) = d := by
  apply Prod.ext
  · apply Prod.ext
    · change (P.facePair (P.facePair (d.1.1,f))).1 = d.1.1
      rw [paired_twice P (d.1.1,f)]
    · change sigma P (P.facePair (d.1.1,f)) (sigma P (d.1.1,f) d.1.2) = d.1.2
      rw [sigma_inverse P (d.1.1,f),Equiv.symm_apply_apply]
  · change sigma P (P.facePair (d.1.1,f)) (sigma P (d.1.1,f) d.2) = d.2
    rw [sigma_inverse P (d.1.1,f),Equiv.symm_apply_apply]
def Component (P : RawFacePairing T) (d0 : OrderedEnd T) :=
  {d : OrderedEnd T // DartRelated P d0.val d.val}
def OccurrenceFiber (P : RawFacePairing T) (o0 : Occurrence T) :=
  {o : Occurrence T // P.edgeLabel o.1 o.2 = P.edgeLabel o0.1 o0.2}
def componentMap (P : RawFacePairing T) (d0 : OrderedEnd T)
    (d : Component P d0) : OccurrenceFiber P (occ d0.val) :=
  ⟨occ d.val.val, by
    have h : P.edgeLabel (occ d0.val).1 (occ d0.val).2 =
        P.edgeLabel (occ d.val.val).1 (occ d.val.val).2 :=
      Quotient.sound (dart_related_occ P d0.property d.property)
    exact h.symm⟩
def Reach (P : RawFacePairing T) (d0 : OrderedEnd T) (o : Occurrence T) : Prop :=
  ∃ d : OrderedEnd T, DartRelated P d0.val d.val ∧ occ d.val = o
theorem reach_edge_step_iff (P : RawFacePairing T) (d0 : OrderedEnd T)
    {i j : Occurrence T} (h : P.edgeStep i j) : Reach P d0 i ↔ Reach P d0 j := by
  have lift {i j : Occurrence T} (h : P.edgeStep i j) (hi : Reach P d0 i) : Reach P d0 j := by
    obtain ⟨d,hd,hdi⟩ := hi
    have hstep : P.edgeStep (occ d.val) j := by rw [hdi]; exact h
    obtain ⟨e,he,hej⟩ := edge_step_lift P d j hstep
    exact ⟨e,hd.trans _ _ _ (Relation.EqvGen.rel _ _ he),hej⟩
  exact ⟨lift h,lift (edge_step_symm P h)⟩
theorem reach_chain_iff (P : RawFacePairing T) (d0 : OrderedEnd T)
    {i j : Occurrence T} (h : Relation.EqvGen P.edgeStep i j) :
    Reach P d0 i ↔ Reach P d0 j := by
  induction h with
  | rel i j h => exact reach_edge_step_iff P d0 h
  | refl i => rfl
  | symm i j _ ih => exact ih.symm
  | trans i j k _ _ ih₁ ih₂ => exact ih₁.trans ih₂
theorem componentMap_surjective (P : RawFacePairing T) (d0 : OrderedEnd T) :
    Function.Surjective (componentMap P d0) := by
  intro o
  have h : Relation.EqvGen P.edgeStep (occ d0.val) o.val :=
    (Quotient.exact o.property).symm
  have hr : Reach P d0 (occ d0.val) := ⟨d0,Relation.EqvGen.refl _,rfl⟩
  obtain ⟨d,hd,ho⟩ := (reach_chain_iff P d0 h).mp hr
  exact ⟨⟨d,hd⟩,Subtype.ext ho⟩
private theorem index_dichotomy (j k l m : Fin 4) (hjk : j ≠ k) (hlm : l ≠ m)
    (h : edgeIndex j k = edgeIndex l m) : (j = l ∧ k = m) ∨ (j = m ∧ k = l) := by
  fin_cases j <;> fin_cases k <;> fin_cases l <;> fin_cases m <;> simp_all [edgeIndex]
theorem occurrence_dichotomy {d e : Dart T} (hd : d.1.2 ≠ d.2) (he : e.1.2 ≠ e.2)
    (h : occ d = occ e) : d = e ∨ e = swap d := by
  have ht : d.1.1 = e.1.1 := by
    change (occ d).1 = (occ e).1
    exact congrArg Prod.fst h
  have hi : edgeIndex d.1.2 d.2 = edgeIndex e.1.2 e.2 := congrArg Prod.snd h
  rcases index_dichotomy _ _ _ _ hd he hi with ⟨hj,hk⟩ | ⟨hj,hk⟩
  · exact Or.inl (Prod.ext (Prod.ext ht hj) hk)
  · exact Or.inr (Prod.ext (Prod.ext ht.symm hk.symm) hj.symm)
theorem swap_swap (d : Dart T) : swap (swap d) = d := rfl
theorem dart_step_swap (P : RawFacePairing T) {d e : Dart T} (h : DartStep P d e) :
    DartStep P (swap d) (swap e) := by
  obtain ⟨f,hfj,hfk,rfl⟩ := h
  exact ⟨f,hfk,hfj,rfl⟩
theorem dart_related_swap (P : RawFacePairing T) {d e : Dart T} (h : DartRelated P d e) :
    DartRelated P (swap d) (swap e) := by
  induction h with
  | rel d e h => exact Relation.EqvGen.rel _ _ (dart_step_swap P h)
  | refl d => exact Relation.EqvGen.refl _
  | symm d e _ ih => exact ih.symm
  | trans d e f _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂
theorem dart_related_swap_iff (P : RawFacePairing T) (d e : Dart T) :
    DartRelated P (swap d) (swap e) ↔ DartRelated P d e := by
  constructor
  · intro h; simpa only [swap_swap] using dart_related_swap P h
  · exact dart_related_swap P
def LocalNoEdgeReversal (P : RawFacePairing T) (d0 : OrderedEnd T) : Prop :=
  ¬ DartRelated P d0.val (swap d0.val)
theorem componentMap_injective (P : RawFacePairing T) (d0 : OrderedEnd T)
    (hNR : LocalNoEdgeReversal P d0) : Function.Injective (componentMap P d0) := by
  intro d e h
  have ho : occ d.val.val = occ e.val.val := congrArg Subtype.val h
  rcases occurrence_dichotomy d.val.property e.val.property ho with heq | hswap
  · exact Subtype.ext (Subtype.ext heq)
  · have h0 : DartRelated P d0.val (swap d.val.val) := by
      rw [← hswap]
      exact e.property
    exact False.elim (hNR (h0.trans _ _ _ (dart_related_swap P d.property.symm)))
def componentEquivOccurrenceFiber (P : RawFacePairing T) (d0 : OrderedEnd T)
    (hNR : LocalNoEdgeReversal P d0) : Component P d0 ≃ OccurrenceFiber P (occ d0.val) :=
  Equiv.ofBijective (componentMap P d0)
    ⟨componentMap_injective P d0 hNR,componentMap_surjective P d0⟩
theorem componentEquivOccurrenceFiber_apply (P : RawFacePairing T) (d0 : OrderedEnd T)
    (hNR : LocalNoEdgeReversal P d0) (d : Component P d0) :
    (componentEquivOccurrenceFiber P d0 hNR d).val = occ d.val.val := rfl
end D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate.dart_step_occ,
      ``D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate.dart_related_occ,
      ``D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate.edge_step_lift_port,
      ``D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate.edge_step_lift,
      ``D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate.dart_move_reverse,
      ``D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate.reach_chain_iff,
      ``D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate.componentMap_surjective,
      ``D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate.occurrence_dichotomy,
      ``D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate.dart_related_swap_iff,
      ``D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate.componentMap_injective,
      ``D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate.componentEquivOccurrenceFiber,
      ``D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate.componentEquivOccurrenceFiber_apply] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1163 original occurrence target absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1163 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP1163 CHECKED {name} axioms={axioms}"
