/- GID: D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/AraujoBrauerCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Brauer complete-mapping existence constructions and classification. -/

/-
admission_basis: escape-witness
escape_witness: D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerCoordinates.coordinate_product_preserving
proof_shape: content — coordinate_product_preserving, coordinate_product_upper_subset, coordinate_product_lower_subset
proof_shape: bind-only — MarkedHalf, DiagramCoordinates, half_mate_mem, coordinateMate, coordinateMateInvolutive, coordinatePerm, coordinatePerm_apply, rowMate, rowMate_involutive, rowHalf, cross_forward, cross_backward, extractCoordinates, coordinate_reconstruction, markedHalf_ext, rowHalf_coordinate_upper, rowHalf_coordinate_lower, coordinatePerm_injective, involutionCoordinateEquiv, partialBrauerCoordinateEquiv, diagramRank, diagramRank_lower, partialBrauerRank, BrauerCoordinates, coordinate_fixed_point_free_iff, brauerCoordinateEquiv, brauerRank, markedHalf_finite, diagramCoordinates_finite, partialBrauer_finite, brauer_finite, RankedHalf, rankedLabels, rankedDiagram, rankedDiagram_rank, rankedCoordinatesEquiv, small_partition_identification, product_upper_singleton, product_lower_singleton, middleOverlay, coordinateConcat, coordinate_upper_pair, coordinate_lower_pair, coordinate_upper_cross, coordinate_upper_singleton, coordinate_lower_singleton, MarkedHalf.through, MarkedHalf.mate, MarkedHalf.involutive, MarkedHalf.fixes, DiagramCoordinates.upper, DiagramCoordinates.lower, DiagramCoordinates.transport
Direct frozen dependencies (declaration statement_id):
D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.endpointPairing sha256:d5fe3010047acb473686bcb77f6a2d93e8abda0a4b57e07f73cd492d884645bb
D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.endpoint_pairing_fixed_point_free sha256:f38f799a458169dd8462c2f2d261dd3b31ab484d67cf3072fc90e32441e69122
D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.endpoint_pairing_involutive sha256:68a971affeadeb943cd77ab25c00a899390e1744f4dfd8ebba1ee658748ebd3b
D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.endpoint_pairing_reattach_same_cycle sha256:80531d01c5f8e8e12fe05303348e4bb896d99ae17e8b09fcabf422650c76dbe1
D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Connected sha256:6d8b0931bcb5ff204447a86b31378e1915c6cc1d8fca5b690ecfbafce8be9e46
D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.connected_iff_rotation_orbits sha256:7ad1cdbc41eb6395cdc5d770c9601e3a8cad541996c47297f2c2a9207e7a4cad
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
import D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSourceMonoids

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

namespace D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerCoordinates

open Equiv
open scoped BigOperators
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSourceMonoids

structure MarkedHalf (X : Type) where
  through : Set X
  mate : Equiv.Perm X
  involutive : Function.Involutive mate
  fixes : ∀ x ∈ through, mate x = x

structure DiagramCoordinates (X : Type) where
  upper : MarkedHalf X
  lower : MarkedHalf X
  transport : upper.through ≃ lower.through

theorem half_mate_mem {X : Type} (H : MarkedHalf X) (x : X) :
    H.mate x ∈ H.through ↔ x ∈ H.through := by
  constructor
  · intro hx
    have he : x = H.mate x := (H.involutive x).symm.trans (H.fixes _ hx)
    exact he.symm ▸ hx
  · intro hx
    simpa only [H.fixes x hx] using hx

noncomputable def coordinateMate {X : Type} (d : DiagramCoordinates X) : Bool × X → Bool × X := by
  classical
  exact fun v => match v with
    | (false,x) => if h : x ∈ d.upper.through then (true, d.transport ⟨x,h⟩) else
        (false,d.upper.mate x)
    | (true,x) => if h : x ∈ d.lower.through then (false, d.transport.symm ⟨x,h⟩) else
        (true,d.lower.mate x)

theorem coordinateMateInvolutive {X : Type} (d : DiagramCoordinates X) :
    Function.Involutive (coordinateMate d) := by
  classical
  rintro ⟨b,x⟩
  cases b
  · by_cases hx : x ∈ d.upper.through
    · simp only [coordinateMate,dif_pos hx,dif_pos (d.transport ⟨x,hx⟩).property]
      exact Prod.ext rfl (congrArg Subtype.val (d.transport.symm_apply_apply ⟨x,hx⟩))
    · have hm := (half_mate_mem d.upper x).not.mpr hx
      simp only [coordinateMate,dif_neg hx,dif_neg hm,d.upper.involutive x]
  · by_cases hx : x ∈ d.lower.through
    · simp only [coordinateMate,dif_pos hx,dif_pos (d.transport.symm ⟨x,hx⟩).property]
      exact Prod.ext rfl (congrArg Subtype.val (d.transport.apply_symm_apply ⟨x,hx⟩))
    · have hm := (half_mate_mem d.lower x).not.mpr hx
      simp only [coordinateMate,dif_neg hx,dif_neg hm,d.lower.involutive x]

noncomputable def coordinatePerm {X : Type} (d : DiagramCoordinates X) : Equiv.Perm (Bool × X) :=
  Function.Involutive.toPerm (coordinateMate d) (coordinateMateInvolutive d)

@[simp] theorem coordinatePerm_apply {X : Type} (d : DiagramCoordinates X) (v : Bool × X) :
    coordinatePerm d v = coordinateMate d v := Eq.symm (Prod.ext rfl rfl)

private noncomputable def rowMate {X : Type} (p : Equiv.Perm (Bool × X)) (b : Bool) (x : X) : X := by
  classical
  exact if (p (b,x)).1 = b then (p (b,x)).2 else x

private theorem rowMate_involutive {X : Type} (p : Equiv.Perm (Bool × X))
    (hp : Function.Involutive p) (b : Bool) : Function.Involutive (rowMate p b) := by
  classical
  intro x
  by_cases hx : (p (b,x)).1 = b
  · have he : p (b,(p (b,x)).2) = (b,x) := by
      have h : (b,(p (b,x)).2) = p (b,x) := Prod.ext hx.symm rfl
      rw [h,hp (b,x)]
    simp only [rowMate,hx,ite_true,he]
  · simp only [rowMate,hx,ite_false]

private noncomputable def rowHalf {X : Type} (p : Equiv.Perm (Bool × X))
    (hp : Function.Involutive p) (b : Bool) : MarkedHalf X where
  through := {x | (p (b,x)).1 ≠ b}
  mate := Function.Involutive.toPerm (rowMate p b) (rowMate_involutive p hp b)
  involutive := rowMate_involutive p hp b
  fixes x hx := by
    classical
    exact if_neg hx

private theorem cross_forward {X : Type} (p : Equiv.Perm (Bool × X))
    (hp : Function.Involutive p) (x : X) (hx : (p (false,x)).1 ≠ false) :
    p (true,(p (false,x)).2) = (false,x) := by
  have hr : (p (false,x)).1 = true := Bool.eq_true_of_not_eq_false hx
  have he : (true,(p (false,x)).2) = p (false,x) := Prod.ext hr.symm rfl
  rw [he,hp (false,x)]

private theorem cross_backward {X : Type} (p : Equiv.Perm (Bool × X))
    (hp : Function.Involutive p) (x : X) (hx : (p (true,x)).1 ≠ true) :
    p (false,(p (true,x)).2) = (true,x) := by
  have hr : (p (true,x)).1 = false := Bool.eq_false_of_not_eq_true hx
  have he : (false,(p (true,x)).2) = p (true,x) := Prod.ext hr.symm rfl
  rw [he,hp (true,x)]

private noncomputable def extractCoordinates {X : Type} (p : Equiv.Perm (Bool × X))
    (hp : Function.Involutive p) : DiagramCoordinates X where
  upper := rowHalf p hp false
  lower := rowHalf p hp true
  transport := {
    toFun x := ⟨(p (false,x)).2,by
      change (p (true,(p (false,x)).2)).1 ≠ true
      rw [cross_forward p hp x x.property]
      simp⟩
    invFun x := ⟨(p (true,x)).2,by
      change (p (false,(p (true,x)).2)).1 ≠ false
      rw [cross_backward p hp x x.property]
      simp⟩
    left_inv x := Subtype.ext (congrArg Prod.snd (cross_forward p hp x x.property))
    right_inv x := Subtype.ext (congrArg Prod.snd (cross_backward p hp x x.property)) }

private theorem coordinate_reconstruction {X : Type} (p : Equiv.Perm (Bool × X))
    (hp : Function.Involutive p) : coordinatePerm (extractCoordinates p hp) = p := by
  classical
  apply Equiv.ext
  rintro ⟨b,x⟩
  cases b
  · by_cases hx : (p (false,x)).1 = false
    · have hv : (false,(p (false,x)).2) = p (false,x) := Prod.ext hx.symm rfl
      simp only [coordinatePerm_apply,coordinateMate,extractCoordinates,rowHalf,Set.mem_setOf_eq,
        dif_neg (not_not.mpr hx)]
      change (false,rowMate p false x) = p (false,x)
      rw [rowMate,if_pos hx]
      exact hv
    · have hr := Bool.eq_true_of_not_eq_false hx
      have hv : (true,(p (false,x)).2) = p (false,x) := Prod.ext hr.symm rfl
      simpa only [coordinatePerm_apply,coordinateMate,extractCoordinates,rowHalf,Set.mem_setOf_eq,Equiv.coe_fn_mk,Equiv.symm_mk,
        dif_pos hx] using hv
  · by_cases hx : (p (true,x)).1 = true
    · have hv : (true,(p (true,x)).2) = p (true,x) := Prod.ext hx.symm rfl
      simp only [coordinatePerm_apply,coordinateMate,extractCoordinates,rowHalf,Set.mem_setOf_eq,
        dif_neg (not_not.mpr hx)]
      change (true,rowMate p true x) = p (true,x)
      rw [rowMate,if_pos hx]
      exact hv
    · have hr := Bool.eq_false_of_not_eq_true hx
      have hv : (false,(p (true,x)).2) = p (true,x) := Prod.ext hr.symm rfl
      simpa only [coordinatePerm_apply,coordinateMate,extractCoordinates,rowHalf,Set.mem_setOf_eq,Equiv.coe_fn_mk,Equiv.symm_mk,
        dif_pos hx] using hv

theorem markedHalf_ext {X : Type} {A B : MarkedHalf X}
    (hT : A.through = B.through) (hm : A.mate = B.mate) : A = B := by
  cases A
  cases B
  cases hT
  cases hm
  rfl

private theorem rowHalf_coordinate_upper {X : Type} (d : DiagramCoordinates X) :
    rowHalf (coordinatePerm d) (coordinateMateInvolutive d) false = d.upper := by
  classical
  apply markedHalf_ext
  · ext x
    change (coordinatePerm d (false,x)).1 ≠ false ↔ x ∈ d.upper.through
    by_cases hx : x ∈ d.upper.through <;> simp [coordinatePerm_apply,coordinateMate,hx]
  · ext x
    change rowMate (coordinatePerm d) false x = d.upper.mate x
    by_cases hx : x ∈ d.upper.through
    · simp [rowMate,coordinatePerm_apply,coordinateMate,hx,d.upper.fixes x hx]
    · simp [rowMate,coordinatePerm_apply,coordinateMate,hx]

private theorem rowHalf_coordinate_lower {X : Type} (d : DiagramCoordinates X) :
    rowHalf (coordinatePerm d) (coordinateMateInvolutive d) true = d.lower := by
  classical
  apply markedHalf_ext
  · ext x
    change (coordinatePerm d (true,x)).1 ≠ true ↔ x ∈ d.lower.through
    by_cases hx : x ∈ d.lower.through <;> simp [coordinatePerm_apply,coordinateMate,hx]
  · ext x
    change rowMate (coordinatePerm d) true x = d.lower.mate x
    by_cases hx : x ∈ d.lower.through
    · simp [rowMate,coordinatePerm_apply,coordinateMate,hx,d.lower.fixes x hx]
    · simp [rowMate,coordinatePerm_apply,coordinateMate,hx]

theorem coordinatePerm_injective {X : Type} :
    Function.Injective (coordinatePerm : DiagramCoordinates X → Equiv.Perm (Bool × X)) := by
  classical
  intro d e h
  have hh :
      (⟨coordinatePerm d,coordinateMateInvolutive d⟩ :
        {p : Equiv.Perm (Bool × X) // Function.Involutive p}) =
      ⟨coordinatePerm e,coordinateMateInvolutive e⟩ := Subtype.ext h
  have hu := congrArg (fun p : {p : Equiv.Perm (Bool × X) // Function.Involutive p} =>
    rowHalf p.val p.property false) hh
  have hl := congrArg (fun p : {p : Equiv.Perm (Bool × X) // Function.Involutive p} =>
    rowHalf p.val p.property true) hh
  rw [rowHalf_coordinate_upper,rowHalf_coordinate_upper] at hu
  rw [rowHalf_coordinate_lower,rowHalf_coordinate_lower] at hl
  cases d with
  | mk du dl dt =>
    cases e with
    | mk eu el et =>
      dsimp only at hu hl
      subst eu
      subst el
      congr 1
      apply Equiv.ext
      intro x
      apply Subtype.ext
      have hx := congrArg (fun p : Equiv.Perm (Bool × X) => (p (false,x.val)).2) h
      simpa only [coordinatePerm_apply,coordinateMate,dif_pos x.property] using hx

private noncomputable def involutionCoordinateEquiv (X : Type) :
    DiagramCoordinates X ≃ {p : Equiv.Perm (Bool × X) // Function.Involutive p} :=
  Equiv.ofBijective (fun d => ⟨coordinatePerm d,coordinateMateInvolutive d⟩) (by
    constructor
    · intro d e h
      exact coordinatePerm_injective (congrArg Subtype.val h)
    · rintro ⟨p,hp⟩
      exact ⟨extractCoordinates p hp,Subtype.ext (coordinate_reconstruction p hp)⟩)

noncomputable def partialBrauerCoordinateEquiv (n : ℕ) :
    DiagramCoordinates (Fin n) ≃ PartialBrauer n :=
  (involutionCoordinateEquiv (Fin n)).trans (partialPartitionEquivInvolution ((Bool × Fin n)))

noncomputable def diagramRank {X : Type} [Finite X] (d : DiagramCoordinates X) : ℕ :=
  Nat.card d.upper.through

theorem diagramRank_lower {X : Type} [Finite X] (d : DiagramCoordinates X) :
    diagramRank d = Nat.card d.lower.through := Nat.card_congr d.transport

noncomputable def partialBrauerRank {n : ℕ} (d : PartialBrauer n) : ℕ :=
  diagramRank ((partialBrauerCoordinateEquiv n).symm d)

abbrev BrauerCoordinates (n : ℕ) :=
  {d : DiagramCoordinates (Fin n) // ∀ v, coordinatePerm d v ≠ v}

theorem coordinate_fixed_point_free_iff {X : Type} (d : DiagramCoordinates X) :
    (∀ v, coordinatePerm d v ≠ v) ↔
      (∀ x ∉ d.upper.through, d.upper.mate x ≠ x) ∧
      (∀ x ∉ d.lower.through, d.lower.mate x ≠ x) := by
  classical
  constructor
  · intro hf
    constructor
    · intro x hx hm
      apply hf (false,x)
      simp only [coordinatePerm_apply,coordinateMate,dif_neg hx,hm]
    · intro x hx hm
      apply hf (true,x)
      simp only [coordinatePerm_apply,coordinateMate,dif_neg hx,hm]
  · rintro ⟨hu,hl⟩ ⟨b,x⟩ h
    cases b
    · by_cases hx : x ∈ d.upper.through
      · have hh := congrArg Prod.fst h
        simpa [coordinatePerm_apply,coordinateMate,hx] using hh
      · exact hu x hx (by
          simpa only [coordinatePerm_apply,coordinateMate,dif_neg hx] using congrArg Prod.snd h)
    · by_cases hx : x ∈ d.lower.through
      · have hh := congrArg Prod.fst h
        simpa [coordinatePerm_apply,coordinateMate,hx] using hh
      · exact hl x hx (by
          simpa only [coordinatePerm_apply,coordinateMate,dif_neg hx] using congrArg Prod.snd h)

noncomputable def brauerCoordinateEquiv (n : ℕ) : BrauerCoordinates n ≃ Brauer n := by
  let f : BrauerCoordinates n → Brauer n := fun d =>
    brauerOfMatching (coordinatePerm d.val) (coordinateMateInvolutive d.val) d.property
  apply Equiv.ofBijective f
  constructor
  · intro d e h
    apply Subtype.ext
    apply coordinatePerm_injective
    exact involutionSetoid_injective _ _ (coordinateMateInvolutive d.val)
      (coordinateMateInvolutive e.val) (congrArg Subtype.val h)
  · intro a
    obtain ⟨p,hp,hpf,he⟩ := brauer_matching_representation a
    let d := extractCoordinates p hp
    have hd : coordinatePerm d = p := coordinate_reconstruction p hp
    refine ⟨⟨d,by simpa only [hd] using hpf⟩,?_⟩
    apply Subtype.ext
    change involutionSetoid (coordinatePerm d) (coordinateMateInvolutive d) = a.val
    simpa only [hd] using he

noncomputable def brauerRank {n : ℕ} (a : Brauer n) : ℕ :=
  diagramRank ((brauerCoordinateEquiv n).symm a).val

private instance markedHalf_finite {X : Type} [Finite X] : Finite (MarkedHalf X) := by
  classical
  letI := Fintype.ofFinite X
  exact Finite.of_injective (fun H : MarkedHalf X => (H.through,H.mate)) (by
    intro A B h
    exact markedHalf_ext (congrArg Prod.fst h) (congrArg Prod.snd h))

private instance diagramCoordinates_finite {X : Type} [Finite X] : Finite (DiagramCoordinates X) := by
  classical
  letI := Fintype.ofFinite X
  exact Finite.of_injective coordinatePerm coordinatePerm_injective

private instance partialBrauer_finite (n : ℕ) : Finite (PartialBrauer n) :=
  Finite.of_surjective (partialBrauerCoordinateEquiv n) (partialBrauerCoordinateEquiv n).surjective

private instance brauer_finite (n : ℕ) : Finite (Brauer n) :=
  Finite.of_surjective (brauerCoordinateEquiv n) (brauerCoordinateEquiv n).surjective

abbrev RankedHalf (X : Type) [Finite X] (r : ℕ) :=
  {H : MarkedHalf X // Nat.card H.through = r}

noncomputable def rankedLabels {X : Type} [Finite X] {r : ℕ} (A : RankedHalf X r) :
    A.val.through ≃ Fin r := by
  letI := Fintype.ofFinite A.val.through
  exact Fintype.equivFinOfCardEq (by simpa only [← Nat.card_eq_fintype_card] using A.property)

noncomputable def rankedDiagram {X : Type} [Finite X] {r : ℕ}
    (A : RankedHalf X r) (g : Equiv.Perm (Fin r)) (D : RankedHalf X r) :
    DiagramCoordinates X where
  upper := A.val
  lower := D.val
  transport := ((rankedLabels A).trans g.symm).trans (rankedLabels D).symm

theorem rankedDiagram_rank {X : Type} [Finite X] {r : ℕ}
    (A : RankedHalf X r) (g : Equiv.Perm (Fin r)) (D : RankedHalf X r) :
    diagramRank (rankedDiagram A g D) = r := A.property

noncomputable def rankedCoordinatesEquiv (X : Type) [Finite X] (r : ℕ) :
    (RankedHalf X r × Equiv.Perm (Fin r) × RankedHalf X r) ≃
      {d : DiagramCoordinates X // diagramRank d = r} where
  toFun a := ⟨rankedDiagram a.1 a.2.1 a.2.2,rankedDiagram_rank _ _ _⟩
  invFun d := (⟨d.val.upper,d.property⟩,
    (((rankedLabels ⟨d.val.upper,d.property⟩).symm.trans d.val.transport).trans
      (rankedLabels ⟨d.val.lower,(diagramRank_lower d.val).symm.trans d.property⟩)).symm,
    ⟨d.val.lower,(diagramRank_lower d.val).symm.trans d.property⟩)
  left_inv := by
    rintro ⟨A,g,D⟩
    dsimp only [rankedDiagram]
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Prod.ext
      · apply Equiv.ext
        intro x
        change (rankedLabels A) ((rankedLabels A).symm
          (g ((rankedLabels D) ((rankedLabels D).symm x)))) = g x
        simp only [Equiv.apply_symm_apply]
      · apply Subtype.ext
        rfl
  right_inv := by
    rintro ⟨⟨A,D,t⟩,hd⟩
    dsimp only [rankedDiagram]
    apply Subtype.ext
    dsimp only
    congr 1
    apply Equiv.ext
    intro x
    simp

/-- Prescribed pairs and isolated singletons determine a partition with blocks of size at most two. -/
private theorem small_partition_identification {X : Type} [Finite X] (q : Setoid X)
    (hq : ∀ x, Nat.card {y : X // q.r x y} ≤ 2)
    (t : Equiv.Perm X) (ht : Function.Involutive t)
    (hpair : ∀ x, q.r x (t x))
    (hfixed : ∀ x, t x = x → ∀ y, q.r x y → y = x) :
    q = involutionSetoid t ht := by
  obtain ⟨p,hp,he⟩ := partial_partition_involution_representation q hq
  have hpt : p = t := by
    ext x
    by_cases hx : t x = x
    · have hrel : q.r x (p x) := by rw [← he]; exact Or.inr rfl
      exact (hfixed x hx (p x) hrel).trans hx.symm
    · have hrel := hpair x
      rw [← he] at hrel
      exact hrel.resolve_left (Ne.symm hx)
  simpa only [hpt] using he.symm

/-- A singleton in the upper exterior row stays isolated in every literal product. -/
private theorem product_upper_singleton {n : ℕ} (p q : (Setoid (Bool × Fin n))) (x : Fin n)
    (hx : ∀ y, p.r (false,x) y → y = (false,x))
    (y : (Bool × Fin n)) (h : (partitionProduct p q).r (false,x) y) : y = (false,x) := by
  let isolate : (Fin 3 × Fin n) → Prop := fun v => v = (0,x)
  have hle : productGraph p q ≤ Setoid.ker isolate := by
    apply Setoid.eqvGen_le
    intro u v he
    change (u = (0,x)) = (v = (0,x))
    apply propext
    rcases he with ⟨a,b,rfl,rfl,hab⟩ | ⟨a,b,rfl,rfl,hab⟩
    · constructor
      · intro ha
        have hae : a = (false,x) := firstEmbedding_injective ha
        subst a
        exact congrArg firstEmbedding (hx b hab)
      · intro hb
        have hbe : b = (false,x) := firstEmbedding_injective hb
        subst b
        exact congrArg firstEmbedding (hx a (p.symm hab))
    · rcases a with ⟨ab,ai⟩
      rcases b with ⟨bb,bi⟩
      cases ab <;> cases bb <;> simp [secondEmbedding]
  have hy := hle h
  change ((exteriorEmbedding (false,x)) = (0,x)) = (exteriorEmbedding y = (0,x)) at hy
  have hey : exteriorEmbedding y = exteriorEmbedding (false,x) := (eq_iff_iff.mp hy).mp rfl
  rcases y with ⟨yb,yi⟩
  cases yb <;> simpa [exteriorEmbedding,Prod.mk.injEq] using hey

/-- A singleton in the lower exterior row stays isolated in every literal product. -/
private theorem product_lower_singleton {n : ℕ} (p q : (Setoid (Bool × Fin n))) (x : Fin n)
    (hx : ∀ y, q.r (true,x) y → y = (true,x))
    (y : (Bool × Fin n)) (h : (partitionProduct p q).r (true,x) y) : y = (true,x) := by
  let isolate : (Fin 3 × Fin n) → Prop := fun v => v = (2,x)
  have hle : productGraph p q ≤ Setoid.ker isolate := by
    apply Setoid.eqvGen_le
    intro u v he
    change (u = (2,x)) = (v = (2,x))
    apply propext
    rcases he with ⟨a,b,rfl,rfl,hab⟩ | ⟨a,b,rfl,rfl,hab⟩
    · rcases a with ⟨ab,ai⟩
      rcases b with ⟨bb,bi⟩
      cases ab <;> cases bb <;> simp [firstEmbedding]
    · constructor
      · intro ha
        have hae : a = (true,x) := secondEmbedding_injective ha
        subst a
        exact congrArg secondEmbedding (hx b hab)
      · intro hb
        have hbe : b = (true,x) := secondEmbedding_injective hb
        subst b
        exact congrArg secondEmbedding (hx a (q.symm hab))
  have hy := hle h
  change ((exteriorEmbedding (true,x)) = (2,x)) = (exteriorEmbedding y = (2,x)) at hy
  have hey : exteriorEmbedding y = exteriorEmbedding (true,x) := (eq_iff_iff.mp hy).mp rfl
  rcases y with ⟨yb,yi⟩
  cases yb <;> simpa [exteriorEmbedding,Prod.mk.injEq] using hey

abbrev middleOverlay {X : Type} (D E : MarkedHalf X) : Setoid X :=
  Relation.EqvGen.setoid (fun x y => D.mate x = y ∨ E.mate x = y)

def coordinateConcat {X : Type} (d e : DiagramCoordinates X)
    (w : d.lower.through ≃ e.upper.through) : DiagramCoordinates X where
  upper := d.upper
  lower := e.lower
  transport := (d.transport.trans w).trans e.transport

private theorem coordinate_upper_pair {X : Type} (d : DiagramCoordinates X) (x : X) :
    (involutionSetoid (coordinatePerm d) (coordinateMateInvolutive d)).r
      (false,x) (false,d.upper.mate x) := by
  classical
  by_cases hx : x ∈ d.upper.through
  · exact Or.inl (Prod.ext rfl (d.upper.fixes x hx).symm)
  · right
    simp only [coordinatePerm_apply,coordinateMate,dif_neg hx]

private theorem coordinate_lower_pair {X : Type} (d : DiagramCoordinates X) (x : X) :
    (involutionSetoid (coordinatePerm d) (coordinateMateInvolutive d)).r
      (true,x) (true,d.lower.mate x) := by
  classical
  by_cases hx : x ∈ d.lower.through
  · exact Or.inl (Prod.ext rfl (d.lower.fixes x hx).symm)
  · right
    simp only [coordinatePerm_apply,coordinateMate,dif_neg hx]

private theorem coordinate_upper_cross {X : Type} (d : DiagramCoordinates X)
    (x : d.upper.through) :
    (involutionSetoid (coordinatePerm d) (coordinateMateInvolutive d)).r
      (false,x) (true,d.transport x) := by
  classical
  right
  simp only [coordinatePerm_apply,coordinateMate,dif_pos x.property]

private theorem coordinate_upper_singleton {X : Type} (d : DiagramCoordinates X)
    (x : X) (hx : x ∉ d.upper.through) (hm : d.upper.mate x = x)
    (y : Bool × X)
    (hy : (involutionSetoid (coordinatePerm d) (coordinateMateInvolutive d)).r (false,x) y) :
    y = (false,x) := by
  classical
  rcases hy with hy | hy
  · exact hy.symm
  · simpa only [coordinatePerm_apply,coordinateMate,dif_neg hx,hm] using hy.symm

private theorem coordinate_lower_singleton {X : Type} (d : DiagramCoordinates X)
    (x : X) (hx : x ∉ d.lower.through) (hm : d.lower.mate x = x)
    (y : Bool × X)
    (hy : (involutionSetoid (coordinatePerm d) (coordinateMateInvolutive d)).r (true,x) y) :
    y = (true,x) := by
  classical
  rcases hy with hy | hy
  · exact hy.symm
  · simpa only [coordinatePerm_apply,coordinateMate,dif_neg hx,hm] using hy.symm

/-- Middle paths that biject all marked endpoints give the literal rank-preserving product. -/
theorem coordinate_product_preserving {n : ℕ} (d e : DiagramCoordinates (Fin n))
    (w : d.lower.through ≃ e.upper.through)
    (hw : ∀ x : d.lower.through, (middleOverlay d.lower e.upper).r x (w x)) :
    partitionProduct
      (involutionSetoid (coordinatePerm d) (coordinateMateInvolutive d))
      (involutionSetoid (coordinatePerm e) (coordinateMateInvolutive e)) =
    involutionSetoid (coordinatePerm (coordinateConcat d e w))
      (coordinateMateInvolutive (coordinateConcat d e w)) := by
  classical
  let p := involutionSetoid (coordinatePerm d) (coordinateMateInvolutive d)
  let q := involutionSetoid (coordinatePerm e) (coordinateMateInvolutive e)
  let G := productGraph p q
  let c := coordinateConcat d e w
  have hmid : middleOverlay d.lower e.upper ≤ Setoid.comap (fun x => (1,x)) G := by
    apply Setoid.eqvGen_le
    intro x y hxy
    rcases hxy with hxy | hxy
    · subst y
      exact Relation.EqvGen.rel _ _ (Or.inl
        ⟨(true,x),(true,d.lower.mate x),rfl,rfl,coordinate_lower_pair d x⟩)
    · subst y
      exact Relation.EqvGen.rel _ _ (Or.inr
        ⟨(false,x),(false,e.upper.mate x),rfl,rfl,coordinate_upper_pair e x⟩)
  have hcross (x : d.upper.through) :
      (partitionProduct p q).r (false,x) (true,c.transport x) := by
    have h₁ : G.r (0,x) (1,d.transport x) :=
      Relation.EqvGen.rel _ _ (Or.inl
        ⟨(false,x),(true,d.transport x),rfl,rfl,coordinate_upper_cross d x⟩)
    have h₂ : G.r (1,d.transport x) (1,w (d.transport x)) := hmid (hw (d.transport x))
    have h₃ : G.r (1,w (d.transport x)) (2,c.transport x) :=
      Relation.EqvGen.rel _ _ (Or.inr
        ⟨(false,w (d.transport x)),(true,c.transport x),rfl,rfl,
          coordinate_upper_cross e (w (d.transport x))⟩)
    exact G.trans h₁ (G.trans h₂ h₃)
  apply small_partition_identification (partitionProduct p q)
    (partitionProductPartialClosed
      (⟨p,involutionSetoidBlockLeTwo _ _⟩ : PartialBrauer n)
      (⟨q,involutionSetoidBlockLeTwo _ _⟩ : PartialBrauer n))
    (coordinatePerm c) (coordinateMateInvolutive c)
  · rintro ⟨b,x⟩
    cases b
    · by_cases hx : x ∈ d.upper.through
      · change (partitionProduct p q).r (false,x) (coordinateMate c (false,x))
        have hxc : x ∈ c.upper.through := hx
        simp only [coordinateMate,dif_pos hxc]
        exact hcross ⟨x,hx⟩
      · have hh : (partitionProduct p q).r (false,x) (false,d.upper.mate x) :=
          Relation.EqvGen.rel _ _ (Or.inl
            ⟨(false,x),(false,d.upper.mate x),rfl,rfl,coordinate_upper_pair d x⟩)
        simpa only [coordinatePerm_apply,coordinateMate,coordinateConcat,c,dif_neg hx] using hh
    · by_cases hx : x ∈ e.lower.through
      · change (partitionProduct p q).r (true,x) (coordinateMate c (true,x))
        have hxc : x ∈ c.lower.through := hx
        simp only [coordinateMate,dif_pos hxc]
        have hh := (partitionProduct p q).symm (hcross (c.transport.symm ⟨x,hx⟩))
        simpa only [c.transport.apply_symm_apply] using hh
      · have hh : (partitionProduct p q).r (true,x) (true,e.lower.mate x) :=
          Relation.EqvGen.rel _ _ (Or.inr
            ⟨(true,x),(true,e.lower.mate x),rfl,rfl,coordinate_lower_pair e x⟩)
        simpa only [coordinatePerm_apply,coordinateMate,coordinateConcat,c,dif_neg hx] using hh
  · rintro ⟨b,x⟩ hfix y hy
    cases b
    · have hx : x ∉ d.upper.through := by
        intro hx
        have hh := congrArg Prod.fst hfix
        simpa [coordinatePerm_apply,coordinateMate,coordinateConcat,c,hx] using hh
      have hm : d.upper.mate x = x := by
        simpa only [coordinatePerm_apply,coordinateMate,coordinateConcat,c,dif_neg hx] using congrArg Prod.snd hfix
      exact product_upper_singleton p q x (coordinate_upper_singleton d x hx hm) y hy
    · have hx : x ∉ e.lower.through := by
        intro hx
        have hh := congrArg Prod.fst hfix
        simpa [coordinatePerm_apply,coordinateMate,coordinateConcat,c,hx] using hh
      have hm : e.lower.mate x = x := by
        simpa only [coordinatePerm_apply,coordinateMate,coordinateConcat,c,dif_neg hx] using congrArg Prod.snd hfix
      exact product_lower_singleton p q x (coordinate_lower_singleton e x hx hm) y hy

/-- Concatenation can only remove upper through vertices. -/
theorem coordinate_product_upper_subset {n : ℕ} (d e t : DiagramCoordinates (Fin n))
    (hprod : partitionProduct
      (involutionSetoid (coordinatePerm d) (coordinateMateInvolutive d))
      (involutionSetoid (coordinatePerm e) (coordinateMateInvolutive e)) =
      involutionSetoid (coordinatePerm t) (coordinateMateInvolutive t)) :
    t.upper.through ⊆ d.upper.through := by
  classical
  intro x hxt
  by_contra hxd
  let p := involutionSetoid (coordinatePerm d) (coordinateMateInvolutive d)
  let q := involutionSetoid (coordinatePerm e) (coordinateMateInvolutive e)
  have hp : (partitionProduct p q).r (false,x) (false,d.upper.mate x) :=
    Relation.EqvGen.rel _ _ (Or.inl
      ⟨(false,x),(false,d.upper.mate x),rfl,rfl,coordinate_upper_pair d x⟩)
  have hm : d.upper.mate x = x := by
    rw [hprod] at hp
    change (false,x) = (false,d.upper.mate x) ∨
      coordinatePerm t (false,x) = (false,d.upper.mate x) at hp
    rcases hp with hp | hp
    · exact (congrArg Prod.snd hp).symm
    · have hh := congrArg Prod.fst hp
      simpa [coordinatePerm_apply,coordinateMate,hxt] using hh
  have hc : (partitionProduct p q).r (false,x) (true,t.transport ⟨x,hxt⟩) := by
    rw [hprod]
    exact coordinate_upper_cross t ⟨x,hxt⟩
  have hh := product_upper_singleton p q x (coordinate_upper_singleton d x hxd hm) _ hc
  have hf := congrArg Prod.fst hh
  cases hf

/-- Concatenation can only remove lower through vertices. -/
theorem coordinate_product_lower_subset {n : ℕ} (d e t : DiagramCoordinates (Fin n))
    (hprod : partitionProduct
      (involutionSetoid (coordinatePerm d) (coordinateMateInvolutive d))
      (involutionSetoid (coordinatePerm e) (coordinateMateInvolutive e)) =
      involutionSetoid (coordinatePerm t) (coordinateMateInvolutive t)) :
    t.lower.through ⊆ e.lower.through := by
  classical
  intro x hxt
  by_contra hxe
  let p := involutionSetoid (coordinatePerm d) (coordinateMateInvolutive d)
  let q := involutionSetoid (coordinatePerm e) (coordinateMateInvolutive e)
  have hp : (partitionProduct p q).r (true,x) (true,e.lower.mate x) :=
    Relation.EqvGen.rel _ _ (Or.inr
      ⟨(true,x),(true,e.lower.mate x),rfl,rfl,coordinate_lower_pair e x⟩)
  have hm : e.lower.mate x = x := by
    rw [hprod] at hp
    change (true,x) = (true,e.lower.mate x) ∨
      coordinatePerm t (true,x) = (true,e.lower.mate x) at hp
    rcases hp with hp | hp
    · exact (congrArg Prod.snd hp).symm
    · have hh := congrArg Prod.fst hp
      simpa [coordinatePerm_apply,coordinateMate,hxt] using hh
  have hc : (partitionProduct p q).r (true,x) (false,t.transport.symm ⟨x,hxt⟩) := by
    rw [hprod]
    right
    simp only [coordinatePerm_apply,coordinateMate,dif_pos hxt]
  have hh := product_lower_singleton p q x (coordinate_lower_singleton e x hxe hm) _ hc
  have hf := congrArg Prod.fst hh
  cases hf

end D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerCoordinates
