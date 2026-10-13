/- GID: D5/S3/Geometry/Hyperideal/BoundedFacePathTransport
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/BoundedFacePathTransport
   mirror-E: none(waiver:arbitrary-ordered-field-face-transport)
   anchors: []
   utility: none
   digest: Weighted actual corner paths lift endpoint changes with a per-component mass bound. -/

import D5.S3.Geometry.Hyperideal.EdgeStarTransitions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Geometry.Hyperideal.BoundedFacePathTransport

open D5.S3.Geometry.Hyperideal.EdgeStarTransitions

abbrev Corner (T : Type*) := T × Fin 4
abbrev Dart (T : Type*) := (T × Fin 4) × Fin 3

def faceVertex : Fin 4 → Fin 3 → Fin 4 :=
  ![![1, 2, 3], ![3, 2, 0], ![3, 1, 0], ![2, 1, 0]]

def endpoint {T : Type*} (i : Dart T) : Corner T :=
  (i.1.1, faceVertex i.1.2 i.2)

def reverseDart {T : Type*} (p : RawFacePairing T) (i : Dart T) : Dart T :=
  (p.facePair i.1, p.faceMap i.1 i.2)

def vertexStep {T : Type*} (p : RawFacePairing T) (c d : Corner T) : Prop :=
  ∃ i : Dart T, endpoint i = c ∧ endpoint (reverseDart p i) = d

def GlobalVertex {T : Type*} (p : RawFacePairing T) :=
  Quotient (Relation.EqvGen.setoid (vertexStep p))

def vertexLabel {T : Type*} (p : RawFacePairing T) (c : Corner T) : GlobalVertex p :=
  Quotient.mk _ c

def cornerGraph {T : Type*} (p : RawFacePairing T) : SimpleGraph (Corner T) where
  Adj c d := c ≠ d ∧ vertexStep p c d
  symm := ⟨by
    intro c d h
    rcases h.2 with ⟨i, hi, hj⟩
    have hp : p.facePair (p.facePair i.1) = i.1 := by
      have h := congrArg (fun e : Equiv.Perm (T × Fin 4) => e i.1) p.pairInvolutive
      simpa using h
    refine ⟨h.1.symm, reverseDart p i, hj, ?_⟩
    simpa [reverseDart, hp, p.mapInverse] using hi⟩
  loopless := ⟨by intro c h; exact h.1 rfl⟩

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def slotSign (r n : Fin 3) : K := if r = n then 1 else -1

def localTemplate {T : Type*} [DecidableEq T] (i : Dart T) (o : Occurrence T) : K :=
  if i.1.1 = o.1 then
    ∑ n : Fin 3, if faceEdge i.1.2 n = o.2 then slotSign i.2 n / 2 else 0
  else 0

def actualLift {T : Type*} (A : Dart T → K) (o : Occurrence T) : K :=
  ∑ f : Fin 4, ∑ r : Fin 3, ∑ n : Fin 3,
    if faceEdge f n = o.2 then A ((o.1, f), r) * slotSign r n / 2 else 0

noncomputable def selectedDart {T : Type*} (p : RawFacePairing T)
    {u v : Corner T} (h : (cornerGraph p).Adj u v) : Dart T :=
  Classical.choose h.2

noncomputable def walkDarts {T : Type*} (p : RawFacePairing T)
    {u v : Corner T} : (cornerGraph p).Walk u v → List (Dart T)
  | .nil => []
  | .cons h w => selectedDart p h :: walkDarts p w

def dartEdge {T : Type*} (p : RawFacePairing T) (i : Dart T) : Sym2 (Corner T) :=
  s(endpoint i, endpoint (reverseDart p i))

noncomputable def pathChi {T : Type*} [DecidableEq T]
    (p : RawFacePairing T) {u v : Corner T} (w : (cornerGraph p).Walk u v)
    (i : Dart T) : K :=
  ((walkDarts p w).count i : K) - ((walkDarts p w).count (reverseDart p i) : K)

def dartDivergence {T : Type*} [Fintype T] [DecidableEq T]
    (A : Dart T → K) (c : Corner T) : K :=
  ∑ i : Dart T, A i * (if endpoint i = c then 1 else 0)

def incident (j : Fin 6) (v : Fin 4) : Prop :=
  (edgeVertices j).1 = v ∨ (edgeVertices j).2 = v

instance (j : Fin 6) (v : Fin 4) : Decidable (incident j v) := by
  unfold incident; infer_instance

noncomputable def cornerTotalMap {T : Type*} [Fintype T] :
    (Occurrence T → K) →ₗ[K] (Corner T → K) :=
  LinearMap.pi fun c => ∑ j : Fin 6,
    if incident j c.2 then LinearMap.proj (R := K) (φ := fun _ : Occurrence T => K) (c.1, j)
    else 0

noncomputable def edgeTotalMap {T : Type*} [Fintype T] (p : RawFacePairing T) :
    (Occurrence T → K) →ₗ[K] (p.GlobalEdge → K) := by
  classical
  exact LinearMap.pi fun e => ∑ o : Occurrence T,
    if p.edgeLabel o.1 o.2 = e then
      LinearMap.proj (R := K) (φ := fun _ : Occurrence T => K) o else 0

open Classical in
set_option maxHeartbeats 2000000 in
-- Inlining all transport facts and incidence tables puts the whole chain in one proof.
theorem bounded_face_path_transport {T : Type*} [Fintype T] [DecidableEq T]
    {S : Type*} [Fintype S] (p : RawFacePairing T)
    (source target : S → Corner T)
    (sameComponent : ∀ s, vertexLabel p (source s) = vertexLabel p (target s))
    (weight : S → K) (hw : ∀ s, 0 ≤ weight s)
    (bound : K)
    (hbound : ∀ b : GlobalVertex p,
      (∑ s, if vertexLabel p (source s) = b then weight s else 0) ≤ bound) :
    ∃ a : Occurrence T → K,
      edgeTotalMap p a = 0 ∧
      (∀ c, -(cornerTotalMap a c) =
        ∑ s, weight s * ((if source s = c then 1 else 0) -
          (if target s = c then 1 else 0))) ∧
      (∀ o, |a o| ≤ 3 * bound) := by
  classical
  have reverseDart_involutive (p : RawFacePairing T) :
      Function.Involutive (reverseDart p) := by
    intro i
    have hp : p.facePair (p.facePair i.1) = i.1 := by
      have h := congrArg (fun e : Equiv.Perm (T × Fin 4) => e i.1) p.pairInvolutive
      simpa using h
    simp [reverseDart, hp, p.mapInverse]
  have label_reachable (p : RawFacePairing T) {c d : Corner T}
      (h : vertexLabel p c = vertexLabel p d) : (cornerGraph p).Reachable c d := by
    have he : Relation.EqvGen (vertexStep p) c d := Quotient.exact h
    clear h
    induction he with
    | rel c d h =>
        by_cases hc : c = d
        · subst d; exact SimpleGraph.Reachable.refl c
        · exact (cornerGraph p).adj_le_reachable c d ⟨hc, h⟩
    | refl c => exact SimpleGraph.Reachable.refl c
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have actual_six_slots (A : Dart T → K) (t : T) (j : Fin 6) :
      actualLift A (t, j) =
        ((∑ r : Fin 3, A ((t, (edgeFaces j).1), r) * slotSign r (edgeFaceSlots j).1) +
         (∑ r : Fin 3, A ((t, (edgeFaces j).2), r) * slotSign r (edgeFaceSlots j).2)) / 2 := by
    fin_cases j <;>
      simp [actualLift, edgeFaces, edgeFaceSlots, faceEdge,
        Fin.sum_univ_four, Fin.sum_univ_three] <;> ring
  have actual_six_slot_bound (A : Dart T → K) (B : K)
      (hA : ∀ i, |A i| ≤ B) (o : Occurrence T) : |actualLift A o| ≤ 3 * B := by
    have hs (t : T) (f : Fin 4) (n : Fin 3) :
        |∑ r : Fin 3, A ((t, f), r) * slotSign r n| ≤ 3 * B := by
      calc
        _ ≤ ∑ r : Fin 3, |A ((t, f), r) * slotSign r n| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _r : Fin 3, B := by
          apply Finset.sum_le_sum
          intro r _
          have hsign : |(slotSign r n : K)| = 1 := by
            unfold slotSign; split_ifs <;> simp
          simpa [abs_mul, hsign] using hA ((t, f), r)
        _ = 3 * B := by simp
    rw [actual_six_slots]
    rw [abs_div, abs_of_pos (show (0 : K) < 2 by norm_num)]
    have h := abs_add_le
      (∑ r : Fin 3, A ((o.1, (edgeFaces o.2).1), r) * slotSign r (edgeFaceSlots o.2).1)
      (∑ r : Fin 3, A ((o.1, (edgeFaces o.2).2), r) * slotSign r (edgeFaceSlots o.2).2)
    have h₁ := hs o.1 (edgeFaces o.2).1 (edgeFaceSlots o.2).1
    have h₂ := hs o.1 (edgeFaces o.2).2 (edgeFaceSlots o.2).2
    apply (div_le_iff₀ (show (0 : K) < 2 by norm_num)).mpr
    linarith
  have selectedDart_endpoints (p : RawFacePairing T)
      {u v : Corner T} (h : (cornerGraph p).Adj u v) :
      endpoint (selectedDart p h) = u ∧
        endpoint (reverseDart p (selectedDart p h)) = v :=
    Classical.choose_spec h.2
  have stepLabel (i : Dart T) :
      vertexLabel p (endpoint i) = vertexLabel p (endpoint (reverseDart p i)) := by
    apply Quotient.sound
    exact Relation.EqvGen.rel _ _ ⟨i, rfl, rfl⟩
  have walkLabels {u v : Corner T} (w : (cornerGraph p).Walk u v) :
      ∀ i ∈ walkDarts p w,
        vertexLabel p (endpoint i) = vertexLabel p u ∧
        vertexLabel p (endpoint (reverseDart p i)) = vertexLabel p u := by
    induction w with
    | nil => simp [walkDarts]
    | @cons u v z h w ih =>
        intro i hi
        have hs := selectedDart_endpoints p h
        have huv : vertexLabel p u = vertexLabel p v := by
          simpa only [hs.1, hs.2] using stepLabel (selectedDart p h)
        simp only [walkDarts, List.mem_cons] at hi
        rcases hi with hi | hi
        · subst i
          rw [hs.1, hs.2]
          exact ⟨rfl, huv.symm⟩
        · exact ⟨(ih i hi).1.trans huv.symm, (ih i hi).2.trans huv.symm⟩
  have pathOff {u v : Corner T} (w : (cornerGraph p).Walk u v) (i : Dart T)
      (hi : vertexLabel p (endpoint i) ≠ vertexLabel p u) :
      (pathChi p w i : K) = 0 := by
    have hn : i ∉ walkDarts p w := by
      intro hm
      exact hi (walkLabels w i hm).1
    have hrn : reverseDart p i ∉ walkDarts p w := by
      intro hm
      have he := (walkLabels w (reverseDart p i) hm).1
      exact hi ((stepLabel i).trans he)
    simp [pathChi, List.count_eq_zero.mpr hn, List.count_eq_zero.mpr hrn]
  -- Recursive selection preserves actual darts and controls their edge counts.
  have walkDarts_count_le_edges
      (p : RawFacePairing T) {u v : Corner T} (w : (cornerGraph p).Walk u v)
      (i : Dart T) : (walkDarts p w).count i ≤ w.edges.count (dartEdge p i) := by
    classical
    induction w with
    | nil => simp [walkDarts]
    | @cons u v z h w ih =>
        have hs := selectedDart_endpoints p h
        have he : dartEdge p (selectedDart p h) = s(u, v) := by
          simp [dartEdge, hs.1, hs.2]
        by_cases hi : selectedDart p h = i
        · subst i
          simpa [walkDarts, SimpleGraph.Walk.edges_cons, he] using Nat.succ_le_succ ih
        · simp only [walkDarts, List.count_cons, beq_iff_eq, hi, if_false,
            SimpleGraph.Walk.edges_cons]
          split_ifs <;> omega
  have pathChi_antisymmetric
      (p : RawFacePairing T) {u v : Corner T} (w : (cornerGraph p).Walk u v)
      (i : Dart T) : pathChi p w (reverseDart p i) = -(pathChi p w i : K) := by
    simp [pathChi, reverseDart_involutive p i]
  have actual_path_dart_load
      (p : RawFacePairing T) {u v : Corner T} (w : (cornerGraph p).Walk u v)
      (hw : w.IsPath) (i : Dart T) : |(pathChi p w i : K)| ≤ 1 := by
    have hi : (walkDarts p w).count i ≤ 1 :=
      (walkDarts_count_le_edges p w i).trans (hw.isTrail.count_edges_le_one _)
    have hj : (walkDarts p w).count (reverseDart p i) ≤ 1 :=
      (walkDarts_count_le_edges p w (reverseDart p i)).trans (hw.isTrail.count_edges_le_one _)
    have hiK : ((walkDarts p w).count i : K) ≤ 1 := by exact_mod_cast hi
    have hjK : ((walkDarts p w).count (reverseDart p i) : K) ≤ 1 := by exact_mod_cast hj
    have hi0 : (0 : K) ≤ ((walkDarts p w).count i : K) := Nat.cast_nonneg _
    have hj0 : (0 : K) ≤ ((walkDarts p w).count (reverseDart p i) : K) := Nat.cast_nonneg _
    rw [pathChi, abs_le]
    constructor <;> linarith
  have pathChi_cons (p : RawFacePairing T)
      {u v z : Corner T} (h : (cornerGraph p).Adj u v) (w : (cornerGraph p).Walk v z) :
      (pathChi p (.cons h w) : Dart T → K) =
        Pi.single (selectedDart p h) 1 - Pi.single (reverseDart p (selectedDart p h)) 1 +
          pathChi p w := by
    classical
    ext i
    have hr : selectedDart p h = reverseDart p i ↔
        reverseDart p (selectedDart p h) = i := by
      constructor
      · intro he; rw [he, reverseDart_involutive p i]
      · intro he
        have hh := congrArg (reverseDart p) he
        simpa only [reverseDart_involutive p (selectedDart p h)] using hh
    simp only [pathChi, walkDarts, List.count_cons, beq_iff_eq, Nat.cast_add,
      Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    simp only [hr, eq_comm]
    split_ifs <;> simp <;> ring
  have path_telescopes
      (p : RawFacePairing T) {u v : Corner T} (w : (cornerGraph p).Walk u v)
      (c : Corner T) : dartDivergence (pathChi p w : Dart T → K) c =
        (if u = c then 1 else 0) - (if v = c then 1 else 0) := by
    classical
    induction w with
    | nil => simp [dartDivergence, pathChi, walkDarts]
    | @cons u v z h w ih =>
        rw [pathChi_cons]
        simp only [dartDivergence, Pi.add_apply, Pi.sub_apply, add_mul, sub_mul,
          Finset.sum_add_distrib, Finset.sum_sub_distrib] at ih ⊢
        have hs (i : Dart T) :
            (∑ j : Dart T, (Pi.single i 1 : Dart T → K) j *
              (if endpoint j = c then 1 else 0)) = (if endpoint i = c then 1 else 0) := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hj; simp [Pi.single_eq_of_ne hj]
          · simp
        rw [hs, hs, (selectedDart_endpoints p h).1, (selectedDart_endpoints p h).2, ih]
        ring
  have weighted_actual_path_load
      (source target : S → Corner T)
      (paths : ∀ s, (cornerGraph p).Walk (source s) (target s))
      (simple : ∀ s, (paths s).IsPath) (weight : S → K)
      (hw : ∀ s, 0 ≤ weight s) (i : Dart T) :
      |∑ s, weight s * pathChi p (paths s) i| ≤
        ∑ s, if vertexLabel p (source s) = vertexLabel p (endpoint i)
          then weight s else 0 := by
    calc
      _ ≤ ∑ s, |weight s * pathChi p (paths s) i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, if vertexLabel p (source s) = vertexLabel p (endpoint i)
          then weight s else 0 := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hs : vertexLabel p (source s) = vertexLabel p (endpoint i)
        · simp only [hs, if_true]
          rw [abs_mul, abs_of_nonneg (hw s)]
          simpa using mul_le_mul_of_nonneg_left
            (actual_path_dart_load p (paths s) (simple s) i) (hw s)
        · rw [pathOff (paths s) i (Ne.symm hs), mul_zero, abs_zero]
          simp [hs]
  have cornerTotalMap_apply
      (a : Occurrence T → K) (c : Corner T) :
      cornerTotalMap a c = ∑ j : Fin 6, if incident j c.2 then a (c.1, j) else 0 := by
    simp only [cornerTotalMap, LinearMap.pi_apply, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro j _; split_ifs <;> simp
  have edgeTotalMap_apply (p : RawFacePairing T)
      (a : Occurrence T → K) (e : p.GlobalEdge) :
      edgeTotalMap p a e = ∑ o : Occurrence T,
        if p.edgeLabel o.1 o.2 = e then a o else 0 := by
    classical
    simp only [edgeTotalMap, LinearMap.pi_apply, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro o _; split_ifs <;> simp
  have template_eq_sum_single (i : Dart T) :
      (localTemplate i : Occurrence T → K) =
        ∑ n : Fin 3, Pi.single (i.1.1, faceEdge i.1.2 n) (slotSign i.2 n / 2) := by
    classical
    ext o
    rcases o with ⟨t, j⟩
    simp only [Finset.sum_apply]
    by_cases ht : i.1.1 = t
    · simp [localTemplate, ht, Pi.single_apply, Prod.mk.injEq, eq_comm]
    · simp [localTemplate, ht, Prod.mk.injEq, Ne.symm ht]
  have actualLift_eq_sum_template
      (A : Dart T → K) : actualLift A = ∑ i : Dart T, A i • localTemplate i := by
    classical
    ext o
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Fintype.sum_prod_type]
    symm
    rw [Finset.sum_eq_single o.1]
    · simp [localTemplate, actualLift, Finset.mul_sum, mul_ite, mul_div_assoc]
    · intro t _ ht; simp [localTemplate, ht]
    · simp
  have cornerTotal_template (i : Dart T) :
      cornerTotalMap (localTemplate i : Occurrence T → K) = -Pi.single (endpoint i) 1 := by
    classical
    ext c
    rcases i with ⟨⟨t, f⟩, r⟩
    rcases c with ⟨u, v⟩
    by_cases ht : t = u
    · subst u
      fin_cases f <;> fin_cases r <;> fin_cases v <;>
        simp [cornerTotalMap_apply, localTemplate, slotSign, incident, edgeVertices,
          faceEdge, endpoint, faceVertex, Fin.sum_univ_six, Fin.sum_univ_three] <;> norm_num
    · simp [cornerTotalMap_apply, localTemplate, ht, endpoint,
        Prod.mk.injEq, Ne.symm ht]
  have edgeTotal_single
      (p : RawFacePairing T) (o : Occurrence T) (w : K) :
      edgeTotalMap p (Pi.single o w) =
        (Pi.single (p.edgeLabel o.1 o.2) w : p.GlobalEdge → K) := by
    classical
    ext e
    rw [edgeTotalMap_apply, Finset.sum_eq_single o]
    · by_cases he : p.edgeLabel o.1 o.2 = e
      · subst e; simp
      · simp [he]
    · intro q _ hq; simp [Pi.single_eq_of_ne hq]
    · simp
  have edgeTotal_template_reverse
      (p : RawFacePairing T) (i : Dart T) :
      edgeTotalMap p (localTemplate (reverseDart p i) : Occurrence T → K) =
        edgeTotalMap p (localTemplate i) := by
    classical
    rw [template_eq_sum_single, template_eq_sum_single, map_sum, map_sum]
    simp only [edgeTotal_single]
    have he (n : Fin 3) :
        p.edgeLabel i.1.1 (faceEdge i.1.2 n) =
          p.edgeLabel (p.facePair i.1).1
            (faceEdge (p.facePair i.1).2 (p.faceMap i.1 n)) := by
      apply Quotient.sound
      exact Relation.EqvGen.rel _ _ ⟨i.1, n, rfl, rfl⟩
    have hs (n : Fin 3) : (slotSign (p.faceMap i.1 i.2) (p.faceMap i.1 n) : K) =
        slotSign i.2 n := by simp [slotSign, (p.faceMap i.1).injective.eq_iff]
    symm
    calc
      _ = ∑ n : Fin 3,
          (Pi.single (p.edgeLabel (p.facePair i.1).1
            (faceEdge (p.facePair i.1).2 (p.faceMap i.1 n)))
            ((slotSign (p.faceMap i.1 i.2) (p.faceMap i.1 n) : K) / 2) : p.GlobalEdge → K) := by
        apply Finset.sum_congr rfl
        intro n _; rw [he n, hs n]
      _ = _ := Equiv.sum_comp (p.faceMap i.1)
        (fun n : Fin 3 => (Pi.single (p.edgeLabel (p.facePair i.1).1
          (faceEdge (p.facePair i.1).2 n))
          ((slotSign (p.faceMap i.1 i.2) n : K) / 2) : p.GlobalEdge → K))
  have actualLift_edge_zero
      (p : RawFacePairing T) (A : Dart T → K)
      (hA : ∀ i, A (reverseDart p i) = -A i) : edgeTotalMap p (actualLift A) = 0 := by
    classical
    rw [actualLift_eq_sum_template, map_sum]
    simp only [map_smul]
    let S : p.GlobalEdge → K := ∑ i : Dart T, A i • edgeTotalMap p (localTemplate i)
    have he : (∑ i : Dart T, A (reverseDart p i) •
        edgeTotalMap p (localTemplate (reverseDart p i))) = S :=
      Equiv.sum_comp ((reverseDart_involutive p).toPerm (reverseDart p))
        (fun i : Dart T => A i • edgeTotalMap p (localTemplate i))
    have hn : (∑ i : Dart T, A (reverseDart p i) •
        edgeTotalMap p (localTemplate (reverseDart p i))) = -S := by
      simp_rw [hA, edgeTotal_template_reverse, neg_smul]
      exact Finset.sum_neg_distrib (fun i : Dart T => A i • edgeTotalMap p (localTemplate i))
    have hS : S = -S := he.symm.trans hn
    change S = 0
    ext e
    have hh := congrFun hS e
    simp only [Pi.neg_apply] at hh
    change S e = 0
    linarith
  have actualLift_corner_divergence
      (A : Dart T → K) (c : Corner T) :
      -(cornerTotalMap (actualLift A) c) = dartDivergence A c := by
    classical
    rw [actualLift_eq_sum_template, map_sum]
    simp only [map_smul, cornerTotal_template, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.neg_apply, Pi.single_apply, dartDivergence]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : endpoint i = c
    · simp only [if_pos hi, if_pos hi.symm, mul_one, mul_neg, neg_neg]
    · simp only [if_neg hi, if_neg (Ne.symm hi), mul_zero, neg_zero]
  have hp (s : S) : ∃ w : (cornerGraph p).Walk (source s) (target s), w.IsPath :=
    (label_reachable p (sameComponent s)).exists_isPath
  choose paths simple using hp
  let A : Dart T → K := fun i => ∑ s, weight s * pathChi p (paths s) i
  have hanti (i : Dart T) : A (reverseDart p i) = -A i := by
    simp [A, pathChi_antisymmetric, Finset.sum_neg_distrib]
  have hload (i : Dart T) : |A i| ≤ bound :=
    (weighted_actual_path_load source target paths simple weight hw i).trans
      (hbound (vertexLabel p (endpoint i)))
  refine ⟨actualLift A, actualLift_edge_zero p A hanti, ?_,
    actual_six_slot_bound A bound hload⟩
  intro c
  rw [actualLift_corner_divergence]
  unfold dartDivergence A
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  have ht := path_telescopes p (paths s) c
  dsimp [dartDivergence] at ht
  rw [ht]

#print axioms bounded_face_path_transport

end D5.S3.Geometry.Hyperideal.BoundedFacePathTransport
