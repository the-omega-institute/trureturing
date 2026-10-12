/- GID: D5/S3/Geometry/Gluing/FiniteZeroGuardedClosure
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/FiniteZeroGuardedClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: Finite zero-guarded identifications admit uniform transport and a closed relation. -/

import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Logic.Relation
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Hausdorff

open Topology
set_option autoImplicit false

namespace D5.S3.Geometry.Gluing.FiniteZeroGuardedClosure

open scoped Classical in
/-- Uniform zero-footprint transport and finite closed pieces for the generated relation. -/
theorem uniform_transport_and_closed_relation {T I A : Type*} [Fintype T] [Fintype I]
    [TopologicalSpace A] [T2Space A] [Zero A]
    [TopologicalSpace T] [DiscreteTopology T]
    (S : Set (I → A))
    (hInvariant : ∀ (rho : Equiv.Perm I) (z : I → A),
      z ∈ S → (fun i => z (rho.symm i)) ∈ S)
    (next : T × I → T) (sigma : T × I → Equiv.Perm I) :
    let K : Type _ := ↥S
    let permute : Equiv.Perm I → K → K := fun rho z =>
      ⟨fun i => z.val (rho.symm i), hInvariant rho z.val z.property⟩
    let X := T × K
    let seam : X → X → Prop := fun a b => ∃ f : I,
      a.2.val f = 0 ∧ b = (next (a.1,f), permute (sigma (a.1,f)) a.2)
    let R : X → X → Prop := Relation.EqvGen seam
    let guard (t u : T) (rho : Equiv.Perm I) (Z : Finset I) : Prop :=
      ∀ z : K, (∀ i ∈ Z, z.val i = 0) → R (t, z) (u, permute rho z)
    let State := T × T × Equiv.Perm I × Finset I
    (∀ a b : X, R a b ↔
      ∃ (rho : Equiv.Perm I) (Z : Finset I),
        guard a.1 b.1 rho Z ∧
        (∀ i ∈ Z, a.2.val i = 0) ∧ b.2 = permute rho a.2) ∧
    (∃ pieces : State → Set (X × X),
      (∀ s : State, IsClosed (pieces s)) ∧
      ({ab : X × X | R ab.1 ab.2} = ⋃ s : State, pieces s) ∧
      Fintype.card State = (Fintype.card T)^2 *
        Nat.factorial (Fintype.card I) * 2^(Fintype.card I)) ∧
    IsClosed {ab : X × X | R ab.1 ab.2} := by
  classical
  let K : Type _ := ↥S
  let permute : Equiv.Perm I → K → K := fun rho z =>
    ⟨fun i => z.val (rho.symm i), hInvariant rho z.val z.property⟩
  let X := T × K
  let seam : X → X → Prop := fun a b => ∃ f : I,
    a.2.val f = 0 ∧ b = (next (a.1,f), permute (sigma (a.1,f)) a.2)
  let R : X → X → Prop := Relation.EqvGen seam
  -- Coordinate actions respect inverse and multiplication.
  have hpermId (z : K) : permute 1 z = z := by
    apply Subtype.ext
    funext i
    rfl
  have hpermLeft (rho : Equiv.Perm I) (z : K) :
      permute rho.symm (permute rho z) = z := by
    apply Subtype.ext
    funext i
    change z.val (rho.symm (rho i)) = z.val i
    rw [Equiv.symm_apply_apply]
  have hpermRight (rho : Equiv.Perm I) (z : K) :
      permute rho (permute rho.symm z) = z := by
    apply Subtype.ext
    funext i
    change z.val (rho (rho.symm i)) = z.val i
    rw [Equiv.apply_symm_apply]
  have hpermComp (tau rho : Equiv.Perm I) (z : K) :
      permute tau (permute rho z) = permute (tau * rho) z := by
    apply Subtype.ext
    funext i
    rfl
  have hpermAt (rho : Equiv.Perm I) (z : K) (i : I) :
      (permute rho z).val (rho i) = z.val i := by
    change z.val (rho.symm (rho i)) = z.val i
    rw [Equiv.symm_apply_apply]
  have hpermContinuous (rho : Equiv.Perm I) : Continuous (permute rho) := by
    exact (continuous_pi fun i =>
      (continuous_apply (rho.symm i)).comp continuous_subtype_val).subtype_mk
        (fun z => (permute rho z).property)
  classical
  let guard (t u : T) (rho : Equiv.Perm I) (Z : Finset I) : Prop :=
    ∀ z : K, (∀ i ∈ Z, z.val i = 0) → R (t, z) (u, permute rho z)
  -- Every generated path transports a fixed finite zero footprint uniformly.
  have hguardForward (a b : X) (hr : R a b) :
      ∃ (rho : Equiv.Perm I) (Z : Finset I),
        guard a.1 b.1 rho Z ∧
        (∀ i ∈ Z, a.2.val i = 0) ∧ b.2 = permute rho a.2 := by
    induction hr with
    | rel a b hs =>
      obtain ⟨f, hf, rfl⟩ := hs
      refine ⟨sigma (a.1, f), {f}, ?_, ?_, rfl⟩
      · intro z hz
        exact Relation.EqvGen.rel _ _
          ⟨f, hz f (Finset.mem_singleton_self f), rfl⟩
      · intro i hi
        have hi' : i = f := Finset.mem_singleton.mp hi
        simpa only [hi'] using hf
    | refl a =>
      refine ⟨1, ∅, ?_, ?_, (hpermId a.2).symm⟩
      · intro z _
        simpa only [hpermId] using Relation.EqvGen.refl (r := seam) (a.1, z)
      · simp
    | symm a b hr ih =>
      obtain ⟨rho, Z, hg, hz, hb⟩ := ih
      refine ⟨rho.symm, Z.image rho, ?_, ?_, ?_⟩
      · intro w hw
        have hzero : ∀ i ∈ Z, (permute rho.symm w).val i = 0 := by
          intro i hi
          change w.val (rho i) = 0
          exact hw (rho i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
        have hh : R (a.1, permute rho.symm w) (b.1, w) := by
          simpa only [hpermRight] using hg (permute rho.symm w) hzero
        exact Relation.EqvGen.symm _ _ hh
      · intro j hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        rw [hb]
        exact (hpermAt rho a.2 i).trans (hz i hi)
      · rw [hb, hpermLeft]
    | trans a b c hab hbc ihab ihbc =>
      obtain ⟨rho, Z, hgr, hz, hb⟩ := ihab
      obtain ⟨tau, W, hgt, hw, hc⟩ := ihbc
      refine ⟨tau * rho, Z ∪ W.image rho.symm, ?_, ?_, ?_⟩
      · intro z hzw
        have hzeroZ : ∀ i ∈ Z, z.val i = 0 := fun i hi =>
          hzw i (Finset.mem_union.mpr (Or.inl hi))
        have hzeroW : ∀ i ∈ W, (permute rho z).val i = 0 := by
          intro i hi
          exact hzw (rho.symm i)
            (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i, hi, rfl⟩)))
        have hh := Relation.EqvGen.trans _ _ _ (hgr z hzeroZ)
          (hgt (permute rho z) hzeroW)
        simpa only [hpermComp] using hh
      · intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · exact hz i hi
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
          have h := hw j hj
          rw [hb] at h
          exact h
      · rw [hc, hb, hpermComp]
  -- Apply uniform transport to the actual source to recover the related pair.
  have hguardIff (a b : X) : R a b ↔
      ∃ (rho : Equiv.Perm I) (Z : Finset I),
        guard a.1 b.1 rho Z ∧
        (∀ i ∈ Z, a.2.val i = 0) ∧ b.2 = permute rho a.2 := by
    constructor
    · exact hguardForward a b
    · rintro ⟨rho, Z, hg, hz, hb⟩
      have hh := hg a.2 hz
      have ha : (a.1, a.2) = a := by
        cases a
        rfl
      have hb' : (b.1, permute rho a.2) = b := by
        apply Prod.ext
        · rfl
        · exact hb.symm
      simpa only [ha, hb'] using hh
  -- Fixed tags, a permutation and a zero footprint determine a closed piece.
  let State := T × T × Equiv.Perm I × Finset I
  let piece (s : State) : Set (X × X) := {ab |
    guard s.1 s.2.1 s.2.2.1 s.2.2.2 ∧
    ab.1.1 = s.1 ∧ ab.2.1 = s.2.1 ∧
    (∀ i ∈ s.2.2.2, ab.1.2.val i = 0) ∧
    ab.2.2 = permute s.2.2.1 ab.1.2}
  have hpieceClosed (s : State) : IsClosed (piece s) := by
    by_cases hg : guard s.1 s.2.1 s.2.2.1 s.2.2.2
    · have hlabel1 : IsClosed {ab : X × X | ab.1.1 = s.1} :=
        isClosed_eq continuous_fst.fst continuous_const
      have hlabel2 : IsClosed {ab : X × X | ab.2.1 = s.2.1} :=
        isClosed_eq continuous_snd.fst continuous_const
      have hzero : IsClosed {ab : X × X |
          ∀ i ∈ s.2.2.2, ab.1.2.val i = 0} := by
        have heq : {ab : X × X | ∀ i ∈ s.2.2.2, ab.1.2.val i = 0} =
            ⋂ i : I, ⋂ (_hi : i ∈ s.2.2.2),
              {ab : X × X | ab.1.2.val i = 0} := by
          ext ab
          simp only [Set.mem_ofPred_eq, Set.mem_iInter]
        rw [heq]
        exact isClosed_iInter fun i => isClosed_iInter fun _ =>
          isClosed_eq
            ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst.snd))
            continuous_const
      have hgraph : IsClosed {ab : X × X |
          ab.2.2 = permute s.2.2.1 ab.1.2} :=
        isClosed_eq continuous_snd.snd (hpermContinuous s.2.2.1 |>.comp continuous_fst.snd)
      have heq : piece s =
          {ab : X × X | ab.1.1 = s.1} ∩
          ({ab : X × X | ab.2.1 = s.2.1} ∩
          ({ab : X × X | ∀ i ∈ s.2.2.2, ab.1.2.val i = 0} ∩
          {ab : X × X | ab.2.2 = permute s.2.2.1 ab.1.2})) := by
        ext ab
        simp only [piece, Set.mem_ofPred_eq, Set.mem_inter_iff, hg, true_and]
      rw [heq]
      exact hlabel1.inter (hlabel2.inter (hzero.inter hgraph))
    · have heq : piece s = ∅ := by
        ext ab
        simp only [piece, Set.mem_ofPred_eq, hg, false_and, Set.mem_empty_iff_false]
      rw [heq]
      exact isClosed_empty
  have hRPieces : {ab : X × X | R ab.1 ab.2} = ⋃ s : State, piece s := by
    ext ab
    constructor
    · intro hr
      obtain ⟨rho, Z, hg, hz, hb⟩ := (hguardIff ab.1 ab.2).mp hr
      apply Set.mem_iUnion.mpr
      refine ⟨(ab.1.1, ab.2.1, rho, Z), ?_⟩
      exact ⟨hg, rfl, rfl, hz, hb⟩
    · intro h
      obtain ⟨s, hg, ht, hu, hz, hb⟩ := Set.mem_iUnion.mp h
      have hh := hg ab.1.2 hz
      have ha : (s.1, ab.1.2) = ab.1 := by
        apply Prod.ext
        · exact ht.symm
        · rfl
      have hb' : (s.2.1, permute s.2.2.1 ab.1.2) = ab.2 := by
        apply Prod.ext
        · exact hu.symm
        · exact hb.symm
      simpa only [Set.mem_ofPred_eq, ha, hb'] using hh
  have hRClosed : IsClosed {ab : X × X | R ab.1 ab.2} := by
    rw [hRPieces]
    exact isClosed_iUnion_of_finite hpieceClosed
  -- Count the finite indexing factors.
  have hStateCard : Fintype.card State = (Fintype.card T)^2 *
      Nat.factorial (Fintype.card I) * 2^(Fintype.card I) := by
    simp only [State, Fintype.card_prod, Fintype.card_perm,
      Fintype.card_finset, pow_two, Nat.mul_assoc]
  exact ⟨hguardIff, ⟨piece, hpieceClosed, hRPieces, hStateCard⟩, hRClosed⟩

end D5.S3.Geometry.Gluing.FiniteZeroGuardedClosure
