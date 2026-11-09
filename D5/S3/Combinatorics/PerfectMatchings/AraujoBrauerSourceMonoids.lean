/- GID: D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Brauer complete-mapping existence constructions and classification. -/

/-
admission_basis: escape-witness
escape_witness: D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSourceMonoids.partitionProduct_assoc
proof_shape: content — comap_sup_map_of_comap_le, comap_sup_map, flatten_left, flatten_right, partitionProduct_assoc, partitionProduct_identity_right, expandedProjection_graph, expanded_product_relation, partitionProduct_involution_representation, partitionProductPartialClosed, partitionProduct_brauer_closed, source_monoids_exist
proof_shape: bind-only — blockSize, Brauer, PartialBrauer, firstEmbedding, secondEmbedding, exteriorEmbedding, productGraphEdge, partitionProduct, BrauerSourceMonoid, PartialBrauerSourceMonoid, involutionSetoid, involutionSetoidBlockTwo, unique_mate, partitionMate, partitionMate_spec, partitionMate_involutive, partitionMatePerm, partition_involution_representation, brauerOfMatching, brauer_matching_representation, small_unique_mate, smallPartitionMate, smallPartitionMate_related, smallPartitionMate_eq_other, smallPartitionMate_involutive, smallPartitionMatePerm, involutionSetoidBlockLeTwo, partial_partition_involution_representation, involutionSetoid_injective, partialPartitionEquivInvolution, partial_brauer_matching_representation, inv_eq_self_iff_involutive, partial_matching_card_mod_two, partial_matching_card_even, interfaceExtension, map_rel_iff_of_injective, map_comap_pullback, innerLeft, innerRight, outerLeft, outerRight, innerLeft_injective, innerRight_injective, outerLeft_injective, outerRight_injective, firstEmbedding_injective, secondEmbedding_injective, left_pullback, right_pullback, productGraph, productGraph_eq_sup, compress_left, compress_right, middle_embedding_eq, last_embedding_eq, first_embedding_eq, fourGraph, identityPartition, exterior_first_leg, exterior_second_leg, partitionProduct_identity_left, identityPartition_brauer, involution_sameCycle, overlay_endpoint_characterization, expandedGlueFun, expandedGlue_involutive, expandedGlue, expandedProjection, expandedExterior, expandedProjection_glue, expandedFixedEquiv, expandedMatching_involutive, expandedGraph, expandedProjection_kernel, brauerSourceAlgebra, partialBrauerSourceAlgebra, brauerSource, partialBrauerSource, BrauerSourceMonoid.algebra, BrauerSourceMonoid.multiplication, PartialBrauerSourceMonoid.algebra, PartialBrauerSourceMonoid.multiplication
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
import D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing
import D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

namespace D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSourceMonoids

open Equiv
open scoped BigOperators
open D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing
open D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit

noncomputable def blockSize {n : ℕ} (p : (Setoid (Bool × Fin n))) (x : (Bool × Fin n)) : ℕ :=
  Nat.card {y : (Bool × Fin n) // p.r x y}

def Brauer (n : ℕ) := {p : (Setoid (Bool × Fin n)) // ∀ x : (Bool × Fin n), blockSize p x = 2}
def PartialBrauer (n : ℕ) := {p : (Setoid (Bool × Fin n)) // ∀ x : (Bool × Fin n), blockSize p x ≤ 2}

/-- The first partition occupies rows 0 and 1 of the product graph. -/
def firstEmbedding {n : ℕ} (x : (Bool × Fin n)) : Fin 3 × Fin n :=
  (if x.1 then 1 else 0, x.2)

/-- The second partition occupies rows 1 and 2 of the product graph. -/
def secondEmbedding {n : ℕ} (x : (Bool × Fin n)) : Fin 3 × Fin n :=
  (if x.1 then 2 else 1, x.2)

/-- Exterior vertices are in rows 0 and 2; internal components are discarded. -/
def exteriorEmbedding {n : ℕ} (x : (Bool × Fin n)) : Fin 3 × Fin n :=
  (if x.1 then 2 else 0, x.2)

def productGraphEdge {n : ℕ} (p q : (Setoid (Bool × Fin n)))
    (u v : Fin 3 × Fin n) : Prop :=
  (∃ x y : (Bool × Fin n), firstEmbedding x = u ∧ firstEmbedding y = v ∧ p.r x y) ∨
  (∃ x y : (Bool × Fin n), secondEmbedding x = u ∧ secondEmbedding y = v ∧ q.r x y)

/-- Source multiplication: exterior vertices share a block exactly when connected in the product graph. -/
abbrev partitionProduct {n : ℕ} (p q : (Setoid (Bool × Fin n))) : (Setoid (Bool × Fin n)) :=
  Setoid.comap exteriorEmbedding (Relation.EqvGen.setoid (productGraphEdge p q))

/-- Laws and closure are bundled, without postulating them; claim explicitly requires existence. -/
structure BrauerSourceMonoid (n : ℕ) where
  algebra : Monoid (Brauer n)
  multiplication : ∀ a b : Brauer n,
    (algebra.mul a b).val = partitionProduct a.val b.val

structure PartialBrauerSourceMonoid (n : ℕ) where
  algebra : Monoid (PartialBrauer n)
  multiplication : ∀ a b : PartialBrauer n,
    (algebra.mul a b).val = partitionProduct a.val b.val

/-- The equivalence classes of an involution have size one or two. -/
def involutionSetoid {X : Type*} (p : Equiv.Perm X) (hp : Function.Involutive p) : Setoid X where
  r x y := x = y ∨ p x = y
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro x y h
      rcases h with h | h
      · exact Or.inl h.symm
      · right
        rw [← h]
        exact hp x
    trans := by
      intro x y z hxy hyz
      rcases hxy with rfl | hxy
      · exact hyz
      · rcases hyz with rfl | hyz
        · exact Or.inr hxy
        · exact Or.inl ((hp x).symm.trans ((congrArg p hxy).trans hyz)) }

theorem involutionSetoidBlockTwo {X : Type*} (p : Equiv.Perm X)
    (hp : Function.Involutive p) (hn : ∀ x, p x ≠ x) (x : X) :
    Nat.card {y : X // (involutionSetoid p hp).r x y} = 2 := by
  let self : {y : X // (involutionSetoid p hp).r x y} := ⟨x,Or.inl rfl⟩
  apply (Nat.card_eq_two_iff' self).mpr
  refine ⟨⟨p x,Or.inr rfl⟩, ?_, ?_⟩
  · intro h
    exact hn x (congrArg Subtype.val h)
  · intro y hy
    apply Subtype.ext
    rcases y.property with h | h
    · exact (hy (Subtype.ext h.symm)).elim
    · exact h.symm

private theorem unique_mate {X : Type*} (q : Setoid X)
    (hq : ∀ x, Nat.card {y : X // q.r x y} = 2) (x : X) :
    ∃! y : X, q.r x y ∧ y ≠ x := by
  obtain ⟨y,hy,hu⟩ := (Nat.card_eq_two_iff' (⟨x,q.refl x⟩ : {y : X // q.r x y})).mp (hq x)
  refine ⟨y.val, ⟨y.property, fun h => hy (Subtype.ext h)⟩, ?_⟩
  intro z hz
  exact congrArg Subtype.val (hu ⟨z,hz.1⟩ (fun h => hz.2 (congrArg Subtype.val h)))

private noncomputable def partitionMate {X : Type*} (q : Setoid X)
    (hq : ∀ x, Nat.card {y : X // q.r x y} = 2) : X → X :=
  fun x => Classical.choose (unique_mate q hq x)

private theorem partitionMate_spec {X : Type*} (q : Setoid X)
    (hq : ∀ x, Nat.card {y : X // q.r x y} = 2) (x : X) :
    (q.r x (partitionMate q hq x) ∧ partitionMate q hq x ≠ x) ∧
    (∀ y, q.r x y ∧ y ≠ x → y = partitionMate q hq x) :=
  Classical.choose_spec (unique_mate q hq x)

private theorem partitionMate_involutive {X : Type*} (q : Setoid X)
    (hq : ∀ x, Nat.card {y : X // q.r x y} = 2) :
    Function.Involutive (partitionMate q hq) := by
  intro x
  have hx := (partitionMate_spec q hq x).1
  exact ((partitionMate_spec q hq (partitionMate q hq x)).2 x
    ⟨q.symm hx.1, Ne.symm hx.2⟩).symm

private noncomputable def partitionMatePerm {X : Type*} (q : Setoid X)
    (hq : ∀ x, Nat.card {y : X // q.r x y} = 2) : Equiv.Perm X :=
  Function.Involutive.toPerm (partitionMate q hq) (partitionMate_involutive q hq)

private theorem partition_involution_representation {X : Type*} (q : Setoid X)
    (hq : ∀ x, Nat.card {y : X // q.r x y} = 2) :
    ∃ p : Equiv.Perm X, ∃ hp : Function.Involutive p,
      (∀ x, p x ≠ x) ∧ involutionSetoid p hp = q := by
  let p := partitionMatePerm q hq
  have hp : Function.Involutive p := partitionMate_involutive q hq
  refine ⟨p,hp, fun x => (partitionMate_spec q hq x).1.2, ?_⟩
  ext x y
  change (x = y ∨ partitionMate q hq x = y) ↔ q.r x y
  constructor
  · rintro (rfl | h)
    · exact q.refl x
    · exact h ▸ (partitionMate_spec q hq x).1.1
  · intro h
    by_cases he : x = y
    · exact Or.inl he
    · exact Or.inr ((partitionMate_spec q hq x).2 y ⟨h,Ne.symm he⟩).symm

noncomputable def brauerOfMatching {n : ℕ} (p : Equiv.Perm ((Bool × Fin n)))
    (hp : Function.Involutive p) (hn : ∀ x, p x ≠ x) : Brauer n :=
  ⟨involutionSetoid p hp, involutionSetoidBlockTwo p hp hn⟩

theorem brauer_matching_representation {n : ℕ} (a : Brauer n) :
    ∃ p : Equiv.Perm ((Bool × Fin n)), ∃ hp : Function.Involutive p,
      (∀ x, p x ≠ x) ∧ involutionSetoid p hp = a.val :=
  partition_involution_representation a.val a.property

private theorem small_unique_mate {X : Type*} [Finite X] (q : Setoid X)
    (hq : ∀ x, Nat.card {y : X // q.r x y} ≤ 2) (x : X)
    (he : ∃ y, q.r x y ∧ y ≠ x) : ∃! y, q.r x y ∧ y ≠ x := by
  obtain ⟨y,hy,hne⟩ := he
  let self : {z : X // q.r x z} := ⟨x,q.refl x⟩
  have hn : Nontrivial {z : X // q.r x z} :=
    ⟨⟨⟨y,hy⟩,self,fun h => hne (congrArg Subtype.val h)⟩⟩
  have hc : Nat.card {z : X // q.r x z} = 2 := by
    letI : Fintype {z : X // q.r x z} := Fintype.ofFinite _
    have hl : 1 < Nat.card {z : X // q.r x z} := by
      exact Finite.one_lt_card_iff_nontrivial.mpr hn
    have hu := hq x
    omega
  obtain ⟨z,hz,hu⟩ := (Nat.card_eq_two_iff' self).mp hc
  refine ⟨z.val,⟨z.property,fun h => hz (Subtype.ext h)⟩,?_⟩
  intro w hw
  exact congrArg Subtype.val (hu ⟨w,hw.1⟩ (fun h => hw.2 (congrArg Subtype.val h)))

private noncomputable def smallPartitionMate {X : Type*} [Finite X] (q : Setoid X)
    (hq : ∀ x, Nat.card {y : X // q.r x y} ≤ 2) (x : X) : X :=
  by
  classical
  exact if he : ∃ y, q.r x y ∧ y ≠ x then
    Classical.choose (small_unique_mate q hq x he) else x

private theorem smallPartitionMate_related {X : Type*} [Finite X] (q : Setoid X)
    (hq : ∀ x, Nat.card {y : X // q.r x y} ≤ 2) (x : X) :
    q.r x (smallPartitionMate q hq x) := by
  classical
  unfold smallPartitionMate
  split
  · rename_i he
    exact (Classical.choose_spec (small_unique_mate q hq x he)).1.1
  · exact q.refl x

private theorem smallPartitionMate_eq_other {X : Type*} [Finite X] (q : Setoid X)
    (hq : ∀ x, Nat.card {y : X // q.r x y} ≤ 2) (x y : X)
    (hy : q.r x y) (hne : y ≠ x) : smallPartitionMate q hq x = y := by
  classical
  have he : ∃ z, q.r x z ∧ z ≠ x := ⟨y,hy,hne⟩
  unfold smallPartitionMate
  rw [dite_eq_left he]
  exact ((Classical.choose_spec (small_unique_mate q hq x he)).2 y ⟨hy,hne⟩).symm

private theorem smallPartitionMate_involutive {X : Type*} [Finite X] (q : Setoid X)
    (hq : ∀ x, Nat.card {y : X // q.r x y} ≤ 2) :
    Function.Involutive (smallPartitionMate q hq) := by
  intro x
  by_cases hx : smallPartitionMate q hq x = x
  · rw [hx,hx]
  · exact smallPartitionMate_eq_other q hq _ x
      (q.symm (smallPartitionMate_related q hq x)) (Ne.symm hx)

private noncomputable def smallPartitionMatePerm {X : Type*} [Finite X] (q : Setoid X)
    (hq : ∀ x, Nat.card {y : X // q.r x y} ≤ 2) : Equiv.Perm X :=
  Function.Involutive.toPerm (smallPartitionMate q hq) (smallPartitionMate_involutive q hq)

theorem involutionSetoidBlockLeTwo {X : Type*} (p : Equiv.Perm X)
    (hp : Function.Involutive p) (x : X) :
    Nat.card {y : X // (involutionSetoid p hp).r x y} ≤ 2 := by
  let f : Bool → {y : X // (involutionSetoid p hp).r x y} :=
    fun b => if b then ⟨p x,Or.inr rfl⟩ else ⟨x,Or.inl rfl⟩
  have hf : Function.Surjective f := by
    intro y
    rcases y.property with h | h
    · exact ⟨false,Subtype.ext h⟩
    · exact ⟨true,Subtype.ext h⟩
  simpa using Nat.card_le_card_of_surjective f hf

theorem partial_partition_involution_representation {X : Type*} [Finite X] (q : Setoid X)
    (hq : ∀ x, Nat.card {y : X // q.r x y} ≤ 2) :
    ∃ p : Equiv.Perm X, ∃ hp : Function.Involutive p,
      involutionSetoid p hp = q := by
  let p := smallPartitionMatePerm q hq
  have hp : Function.Involutive p := smallPartitionMate_involutive q hq
  refine ⟨p,hp,?_⟩
  ext x y
  change (x = y ∨ smallPartitionMate q hq x = y) ↔ q.r x y
  constructor
  · rintro (rfl | h)
    · exact q.refl x
    · exact h ▸ smallPartitionMate_related q hq x
  · intro h
    by_cases he : y = x
    · exact Or.inl he.symm
    · exact Or.inr (smallPartitionMate_eq_other q hq x y h he)

theorem involutionSetoid_injective {X : Type*}
    (p q : Equiv.Perm X) (hp : Function.Involutive p) (hq : Function.Involutive q)
    (he : involutionSetoid p hp = involutionSetoid q hq) : p = q := by
  apply Equiv.ext
  intro x
  have h₁ : x = p x ∨ q x = p x := by
    change (involutionSetoid q hq).r x (p x)
    rw [← he]
    exact Or.inr rfl
  rcases h₁ with h₁ | h₁
  · have h₂ : x = q x ∨ p x = q x := by
      change (involutionSetoid p hp).r x (q x)
      rw [he]
      exact Or.inr rfl
    exact h₂.elim (fun h₂ => h₁.symm.trans h₂) id
  · exact h₁.symm

noncomputable def partialPartitionEquivInvolution (X : Type*) [Finite X] :
    {p : Equiv.Perm X // Function.Involutive p} ≃
      {q : Setoid X // ∀ x, Nat.card {y : X // q.r x y} ≤ 2} := by
  let f : {p : Equiv.Perm X // Function.Involutive p} →
      {q : Setoid X // ∀ x, Nat.card {y : X // q.r x y} ≤ 2} :=
    fun p => ⟨involutionSetoid p.val p.property,involutionSetoidBlockLeTwo p.val p.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q h
    exact Subtype.ext (involutionSetoid_injective p.val q.val p.property q.property
      (congrArg Subtype.val h))
  · intro q
    obtain ⟨p,hp,he⟩ := partial_partition_involution_representation q.val q.property
    exact ⟨⟨p,hp⟩,Subtype.ext he⟩

private theorem partial_brauer_matching_representation {n : ℕ} (a : PartialBrauer n) :
    ∃ p : Equiv.Perm ((Bool × Fin n)), ∃ hp : Function.Involutive p,
      involutionSetoid p hp = a.val :=
  partial_partition_involution_representation a.val a.property

theorem inv_eq_self_iff_involutive {X : Type*} (p : Equiv.Perm X) :
    p⁻¹ = p ↔ Function.Involutive p := by
  constructor
  · intro h x
    exact (congrArg (fun f : Equiv.Perm X => f (p x)) h).symm.trans (p.symm_apply_apply x)
  · exact Function.Involutive.symm_eq_self_of_involutive p


private theorem partial_matching_card_mod_two {X : Type*} [Fintype X] :
    Nat.ModEq 2 (Nat.card (Equiv.Perm X))
      (Nat.card {p : Equiv.Perm X // Function.Involutive p}) := by
  classical
  let f : Function.End (Equiv.Perm X) := Inv.inv
  have hpow : f ^ 2 = 1 := by
    exact (isPeriodicPt_mul_iff_pow_eq_one f).mp rfl
  have h := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) (f := f)
    (by simpa using hpow)
  have hc := Nat.card_congr (Equiv.subtypeEquivRight (fun p : Equiv.Perm X => inv_eq_self_iff_involutive p))
  rw [Fintype.card_eq_nat_card,Fintype.card_eq_nat_card] at h
  change Nat.ModEq 2 (Nat.card (Equiv.Perm X))
    (Nat.card {p : Equiv.Perm X // p⁻¹ = p}) at h
  rw [hc] at h
  exact h

theorem partial_matching_card_even {X : Type*} [Fintype X]
    (hx : 2 ≤ Fintype.card X) :
    Even (Nat.card {p : Equiv.Perm X // Function.Involutive p}) := by
  classical
  have he : 2 ∣ Nat.card (Equiv.Perm X) := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm]
    exact Nat.dvd_factorial (by decide) hx
  have hm := partial_matching_card_mod_two (X := X)
  apply even_iff_two_dvd.mpr
  apply Nat.dvd_of_mod_eq_zero
  exact hm.symm.trans (Nat.modEq_zero_iff_dvd.mpr he)

private def interfaceExtension {X Y : Type*} (R : Setoid X) (i : Y → X) (S : Setoid Y)
    (hRS : Setoid.comap i R ≤ S) : Setoid X where
  r x y := R.r x y ∨ ∃ a b, R.r x (i a) ∧ S.r a b ∧ R.r (i b) y
  iseqv := {
    refl := fun x => Or.inl (R.refl x)
    symm := by
      intro x y h
      rcases h with h | ⟨a,b,hxa,hab,hby⟩
      · exact Or.inl (R.symm h)
      · exact Or.inr ⟨b,a,R.symm hby,S.symm hab,R.symm hxa⟩
    trans := by
      intro x y z hxy hyz
      rcases hxy with hxy | ⟨a,b,hxa,hab,hby⟩
      · rcases hyz with hyz | ⟨c,d,hyc,hcd,hdz⟩
        · exact Or.inl (R.trans hxy hyz)
        · exact Or.inr ⟨c,d,R.trans hxy hyc,hcd,hdz⟩
      · rcases hyz with hyz | ⟨c,d,hyc,hcd,hdz⟩
        · exact Or.inr ⟨a,b,hxa,hab,R.trans hby hyz⟩
        · exact Or.inr ⟨a,d,hxa,S.trans hab (S.trans (hRS (R.trans hby hyc)) hcd),hdz⟩ }

private theorem comap_sup_map_of_comap_le {X Y : Type*} (R : Setoid X) (i : Y → X)
    (S : Setoid Y) (hRS : Setoid.comap i R ≤ S) :
    Setoid.comap i (R ⊔ S.map i) = S := by
  apply le_antisymm
  · have hR : R ≤ interfaceExtension R i S hRS := fun _ _ h => Or.inl h
    have hS : S.map i ≤ interfaceExtension R i S hRS := by
      apply Setoid.gc_map_comap.le_iff_le.mpr
      intro a b hab
      exact Or.inr ⟨a,b,R.refl _,hab,R.refl _⟩
    intro a b hab
    have h := (sup_le hR hS) hab
    rcases h with h | ⟨c,d,hac,hcd,hdb⟩
    · exact hRS h
    · exact S.trans (hRS hac) (S.trans hcd (hRS hdb))
  · exact (Setoid.comap_monotone i le_sup_right).trans' Setoid.le_comap_map

private theorem comap_sup_map {X Y : Type*} (R : Setoid X) (i : Y → X) (S : Setoid Y) :
    Setoid.comap i (R ⊔ S.map i) = Setoid.comap i R ⊔ S := by
  have h₀ : (Setoid.comap i R).map i ≤ R := Setoid.gc_map_comap.l_u_le R
  have h₁ : R ⊔ (Setoid.comap i R ⊔ S).map i = R ⊔ S.map i := by
    rw [Setoid.gc_map_comap.l_sup,← sup_assoc,sup_eq_left.mpr h₀]
  rw [← h₁]
  exact comap_sup_map_of_comap_le R i _ le_sup_left

private theorem map_rel_iff_of_injective {X Y : Type*} (R : Setoid X)
    (i : X → Y) (hi : Function.Injective i) (x y : Y) :
    (R.map i).r x y ↔ (∃ a b, R.r a b ∧ i a = x ∧ i b = y) ∨ x = y := by
  have hker : Setoid.ker i ≤ R := by
    intro a b h
    have h' : a = b := hi h
    exact h' ▸ R.refl a
  change (R.map i : Y → Y → Prop) x y ↔ _
  rw [Setoid.coe_map_of_ker_le R i hker]
  rfl

private theorem map_comap_pullback {W X Y Z : Type*}
    (R : Setoid X) (a : W → X) (b : W → Y) (i : X → Z) (j : Y → Z)
    (hi : Function.Injective i) (hj : Function.Injective j) (hb : Function.Injective b)
    (hcomm : ∀ w, i (a w) = j (b w))
    (hpb : ∀ x y, i x = j y → ∃ w, a w = x ∧ b w = y) :
    Setoid.comap j (R.map i) = (Setoid.comap a R).map b := by
  ext y z
  change (R.map i).r (j y) (j z) ↔ ((Setoid.comap a R).map b).r y z
  rw [map_rel_iff_of_injective R i hi,map_rel_iff_of_injective _ b hb]
  constructor
  · rintro (⟨x,x',hxx',hxy,hxz⟩ | he)
    · obtain ⟨w,hwx,hwy⟩ := hpb x y hxy
      obtain ⟨w',hwx',hwy'⟩ := hpb x' z hxz
      exact Or.inl ⟨w,w',by simpa only [Setoid.comap_rel,hwx,hwx'] using hxx',hwy,hwy'⟩
    · exact Or.inr (hj he)
  · rintro (⟨w,w',hww',hwy,hwz⟩ | rfl)
    · exact Or.inl ⟨a w,a w',hww',(hcomm w).trans (congrArg j hwy),
        (hcomm w').trans (congrArg j hwz)⟩
    · exact Or.inr rfl

private def innerLeft {n : ℕ} (v : (Fin 3 × Fin n)) : (Fin 4 × Fin n) := (v.1.castSucc,v.2)
private def innerRight {n : ℕ} (v : (Fin 3 × Fin n)) : (Fin 4 × Fin n) := (v.1.succ,v.2)
private def outerLeft {n : ℕ} (v : (Fin 3 × Fin n)) : (Fin 4 × Fin n) :=
  (if v.1 = 0 then 0 else if v.1 = 1 then 2 else 3,v.2)
private def outerRight {n : ℕ} (v : (Fin 3 × Fin n)) : (Fin 4 × Fin n) :=
  (if v.1 = 2 then 3 else v.1.castSucc,v.2)

private theorem innerLeft_injective {n : ℕ} : Function.Injective (@innerLeft n) := by
  rintro ⟨a,x⟩ ⟨b,y⟩ h
  fin_cases a <;> fin_cases b <;> simp_all [innerLeft,Prod.mk.injEq]
private theorem innerRight_injective {n : ℕ} : Function.Injective (@innerRight n) := by
  rintro ⟨a,x⟩ ⟨b,y⟩ h
  fin_cases a <;> fin_cases b <;> simp_all [innerRight,Prod.mk.injEq]
private theorem outerLeft_injective {n : ℕ} : Function.Injective (@outerLeft n) := by
  rintro ⟨a,x⟩ ⟨b,y⟩ h
  fin_cases a <;> fin_cases b <;> simp_all [outerLeft,Prod.mk.injEq]
private theorem outerRight_injective {n : ℕ} : Function.Injective (@outerRight n) := by
  rintro ⟨a,x⟩ ⟨b,y⟩ h
  fin_cases a <;> fin_cases b <;> simp_all [outerRight,Prod.mk.injEq]
theorem firstEmbedding_injective {n : ℕ} : Function.Injective (@firstEmbedding n) := by
  rintro ⟨a,x⟩ ⟨b,y⟩ h
  cases a <;> cases b <;> simp_all [firstEmbedding,Prod.mk.injEq]
theorem secondEmbedding_injective {n : ℕ} : Function.Injective (@secondEmbedding n) := by
  rintro ⟨a,x⟩ ⟨b,y⟩ h
  cases a <;> cases b <;> simp_all [secondEmbedding,Prod.mk.injEq]

private theorem left_pullback {n : ℕ} (x y : (Fin 3 × Fin n)) (h : innerLeft x = outerLeft y) :
    ∃ w : (Bool × Fin n), exteriorEmbedding w = x ∧ firstEmbedding w = y := by
  rcases x with ⟨a,x⟩
  rcases y with ⟨b,y⟩
  fin_cases a <;> fin_cases b <;> simp [innerLeft,outerLeft,Prod.mk.injEq] at h
  all_goals first
    | exact ⟨(false,x),rfl,Prod.ext rfl h⟩
    | exact ⟨(true,x),rfl,Prod.ext rfl h⟩

private theorem right_pullback {n : ℕ} (x y : (Fin 3 × Fin n)) (h : innerRight x = outerRight y) :
    ∃ w : (Bool × Fin n), exteriorEmbedding w = x ∧ secondEmbedding w = y := by
  rcases x with ⟨a,x⟩
  rcases y with ⟨b,y⟩
  fin_cases a <;> fin_cases b <;> simp [innerRight,outerRight,Prod.mk.injEq] at h
  all_goals first
    | exact ⟨(false,x),rfl,Prod.ext rfl h⟩
    | exact ⟨(true,x),rfl,Prod.ext rfl h⟩

abbrev productGraph {n : ℕ} (p q : (Setoid (Bool × Fin n))) : Setoid ((Fin 3 × Fin n)) :=
  Relation.EqvGen.setoid (productGraphEdge p q)

private theorem productGraph_eq_sup {n : ℕ} (p q : (Setoid (Bool × Fin n))) :
    productGraph p q = p.map firstEmbedding ⊔ q.map secondEmbedding := by
  apply le_antisymm
  · apply Setoid.eqvGen_le
    intro u v he
    rcases he with ⟨x,y,rfl,rfl,h⟩ | ⟨x,y,rfl,rfl,h⟩
    · have hl : p.map firstEmbedding ≤ p.map firstEmbedding ⊔ q.map secondEmbedding := le_sup_left
      exact hl (Relation.EqvGen.rel _ _ ⟨x,y,h,rfl,rfl⟩)
    · have hl : q.map secondEmbedding ≤ p.map firstEmbedding ⊔ q.map secondEmbedding := le_sup_right
      exact hl (Relation.EqvGen.rel _ _ ⟨x,y,h,rfl,rfl⟩)
  · apply sup_le
    · apply Setoid.gc_map_comap.le_iff_le.mpr
      intro x y h
      exact Relation.EqvGen.rel _ _ (Or.inl ⟨x,y,rfl,rfl,h⟩)
    · apply Setoid.gc_map_comap.le_iff_le.mpr
      intro x y h
      exact Relation.EqvGen.rel _ _ (Or.inr ⟨x,y,rfl,rfl,h⟩)

private theorem compress_left {n : ℕ} (p q : (Setoid (Bool × Fin n))) :
    Setoid.comap outerLeft ((productGraph p q).map innerLeft) =
      (partitionProduct p q).map firstEmbedding := by
  apply map_comap_pullback (productGraph p q) exteriorEmbedding firstEmbedding
    innerLeft outerLeft innerLeft_injective outerLeft_injective firstEmbedding_injective
  · rintro ⟨b,i⟩
    cases b <;> rfl
  · exact left_pullback

private theorem compress_right {n : ℕ} (p q : (Setoid (Bool × Fin n))) :
    Setoid.comap outerRight ((productGraph p q).map innerRight) =
      (partitionProduct p q).map secondEmbedding := by
  apply map_comap_pullback (productGraph p q) exteriorEmbedding secondEmbedding
    innerRight outerRight innerRight_injective outerRight_injective secondEmbedding_injective
  · rintro ⟨b,i⟩
    cases b <;> rfl
  · exact right_pullback

private theorem middle_embedding_eq {n : ℕ} :
    (@innerRight n) ∘ firstEmbedding = innerLeft ∘ secondEmbedding := by
  funext x
  rcases x with ⟨b,i⟩
  cases b <;> rfl

private theorem last_embedding_eq {n : ℕ} :
    (@outerLeft n) ∘ secondEmbedding = innerRight ∘ secondEmbedding := by
  funext x
  rcases x with ⟨b,i⟩
  cases b <;> rfl

private theorem first_embedding_eq {n : ℕ} :
    (@outerRight n) ∘ firstEmbedding = innerLeft ∘ firstEmbedding := by
  funext x
  rcases x with ⟨b,i⟩
  cases b <;> rfl

private abbrev fourGraph {n : ℕ} (p q r : (Setoid (Bool × Fin n))) : Setoid ((Fin 4 × Fin n)) :=
  p.map (innerLeft ∘ firstEmbedding) ⊔ q.map (innerLeft ∘ secondEmbedding) ⊔
    r.map (innerRight ∘ secondEmbedding)

private theorem flatten_left {n : ℕ} (p q r : (Setoid (Bool × Fin n))) :
    Setoid.comap outerLeft (fourGraph p q r) = productGraph (partitionProduct p q) r := by
  have hinner : (productGraph p q).map innerLeft =
      p.map (innerLeft ∘ firstEmbedding) ⊔ q.map (innerLeft ∘ secondEmbedding) := by
    rw [productGraph_eq_sup,Setoid.gc_map_comap.l_sup,Setoid.map_map,Setoid.map_map]
  have hr : (r.map secondEmbedding).map outerLeft = r.map (innerRight ∘ secondEmbedding) := by
    rw [Setoid.map_map,last_embedding_eq]
  change Setoid.comap outerLeft
    ((p.map (innerLeft ∘ firstEmbedding) ⊔ q.map (innerLeft ∘ secondEmbedding)) ⊔
      r.map (innerRight ∘ secondEmbedding)) = _
  rw [← hinner,← hr,comap_sup_map,compress_left,productGraph_eq_sup]

private theorem flatten_right {n : ℕ} (p q r : (Setoid (Bool × Fin n))) :
    Setoid.comap outerRight (fourGraph p q r) = productGraph p (partitionProduct q r) := by
  have hinner : (productGraph q r).map innerRight =
      q.map (innerLeft ∘ secondEmbedding) ⊔ r.map (innerRight ∘ secondEmbedding) := by
    rw [productGraph_eq_sup,Setoid.gc_map_comap.l_sup,Setoid.map_map,Setoid.map_map,
      middle_embedding_eq]
  have hp : (p.map firstEmbedding).map outerRight = p.map (innerLeft ∘ firstEmbedding) := by
    rw [Setoid.map_map,first_embedding_eq]
  change Setoid.comap outerRight
    ((p.map (innerLeft ∘ firstEmbedding) ⊔ q.map (innerLeft ∘ secondEmbedding)) ⊔
      r.map (innerRight ∘ secondEmbedding)) = _
  rw [sup_assoc,← hinner,← hp,sup_comm ((p.map firstEmbedding).map outerRight),
    comap_sup_map,compress_right,productGraph_eq_sup,sup_comm]

theorem partitionProduct_assoc {n : ℕ} (p q r : (Setoid (Bool × Fin n))) :
    partitionProduct (partitionProduct p q) r = partitionProduct p (partitionProduct q r) := by
  change Setoid.comap exteriorEmbedding (productGraph (partitionProduct p q) r) =
    Setoid.comap exteriorEmbedding (productGraph p (partitionProduct q r))
  rw [← flatten_left,← flatten_right]
  change Setoid.comap (outerLeft ∘ exteriorEmbedding) (fourGraph p q r) =
    Setoid.comap (outerRight ∘ exteriorEmbedding) (fourGraph p q r)
  have he : (@outerLeft n) ∘ exteriorEmbedding = outerRight ∘ exteriorEmbedding := by
    funext x
    rcases x with ⟨b,i⟩
    cases b <;> rfl
  rw [he]

/-- The source identity partition joins precisely the two rows at each label. -/
@[instance_reducible] def identityPartition (n : ℕ) : (Setoid (Bool × Fin n)) := Setoid.ker Prod.snd

private theorem exterior_first_leg {n : ℕ} (p : (Setoid (Bool × Fin n))) (x : (Bool × Fin n)) :
    Relation.EqvGen (productGraphEdge p (identityPartition n))
      (exteriorEmbedding x) (firstEmbedding x) := by
  rcases x with ⟨b,i⟩
  cases b
  · exact Relation.EqvGen.refl _
  · apply Relation.EqvGen.rel
    right
    exact ⟨(true,i),(false,i),rfl,rfl,rfl⟩

private theorem exterior_second_leg {n : ℕ} (p : (Setoid (Bool × Fin n))) (x : (Bool × Fin n)) :
    Relation.EqvGen (productGraphEdge (identityPartition n) p)
      (exteriorEmbedding x) (secondEmbedding x) := by
  rcases x with ⟨b,i⟩
  cases b
  · apply Relation.EqvGen.rel
    left
    exact ⟨(false,i),(true,i),rfl,rfl,rfl⟩
  · exact Relation.EqvGen.refl _

private theorem partitionProduct_identity_right {n : ℕ} (p : (Setoid (Bool × Fin n))) :
    partitionProduct p (identityPartition n) = p := by
  ext x y
  constructor
  · intro h
    let collapse : Fin 3 × Fin n → (Bool × Fin n) := fun v => (decide (v.1 ≠ 0),v.2)
    have hc : ∀ a b, productGraphEdge p (identityPartition n) a b →
        p.r (collapse a) (collapse b) := by
      intro a b he
      rcases he with ⟨u,v,rfl,rfl,huv⟩ | ⟨u,v,rfl,rfl,huv⟩
      · rcases u with ⟨ub,ui⟩; rcases v with ⟨vb,vi⟩
        cases ub <;> cases vb <;> simpa [collapse,firstEmbedding] using huv
      · have hi : u.2 = v.2 := huv
        have ha : collapse (secondEmbedding u) = (true,u.2) := by
          rcases u with ⟨b,i⟩; cases b <;> rfl
        have hb : collapse (secondEmbedding v) = (true,v.2) := by
          rcases v with ⟨b,i⟩; cases b <;> rfl
        rw [ha,hb,hi]
    have hl : Relation.EqvGen.setoid (productGraphEdge p (identityPartition n)) ≤
        Setoid.comap collapse p := Setoid.eqvGen_le hc
    have he := hl h
    have hx : collapse (exteriorEmbedding x) = x := by
      rcases x with ⟨b,i⟩; cases b <;> rfl
    have hy : collapse (exteriorEmbedding y) = y := by
      rcases y with ⟨b,i⟩; cases b <;> rfl
    change p.r (collapse (exteriorEmbedding x)) (collapse (exteriorEmbedding y)) at he
    simpa only [hx,hy] using he
  · intro h
    let G := Relation.EqvGen.setoid (productGraphEdge p (identityPartition n))
    have hmid : G.r (firstEmbedding x) (firstEmbedding y) :=
      Relation.EqvGen.rel _ _ (Or.inl ⟨x,y,rfl,rfl,h⟩)
    exact G.trans (exterior_first_leg p x) (G.trans hmid (G.symm (exterior_first_leg p y)))

theorem partitionProduct_identity_left {n : ℕ} (p : (Setoid (Bool × Fin n))) :
    partitionProduct (identityPartition n) p = p := by
  ext x y
  constructor
  · intro h
    let collapse : Fin 3 × Fin n → (Bool × Fin n) := fun v => (decide (v.1 = 2),v.2)
    have hc : ∀ a b, productGraphEdge (identityPartition n) p a b →
        p.r (collapse a) (collapse b) := by
      intro a b he
      rcases he with ⟨u,v,rfl,rfl,huv⟩ | ⟨u,v,rfl,rfl,huv⟩
      · have hi : u.2 = v.2 := huv
        have ha : collapse (firstEmbedding u) = (false,u.2) := by
          rcases u with ⟨b,i⟩; cases b <;> rfl
        have hb : collapse (firstEmbedding v) = (false,v.2) := by
          rcases v with ⟨b,i⟩; cases b <;> rfl
        rw [ha,hb,hi]
      · rcases u with ⟨ub,ui⟩; rcases v with ⟨vb,vi⟩
        cases ub <;> cases vb <;> simpa [collapse,secondEmbedding] using huv
    have hl : Relation.EqvGen.setoid (productGraphEdge (identityPartition n) p) ≤
        Setoid.comap collapse p := Setoid.eqvGen_le hc
    have he := hl h
    have hx : collapse (exteriorEmbedding x) = x := by
      rcases x with ⟨b,i⟩; cases b <;> rfl
    have hy : collapse (exteriorEmbedding y) = y := by
      rcases y with ⟨b,i⟩; cases b <;> rfl
    change p.r (collapse (exteriorEmbedding x)) (collapse (exteriorEmbedding y)) at he
    simpa only [hx,hy] using he
  · intro h
    let G := Relation.EqvGen.setoid (productGraphEdge (identityPartition n) p)
    have hmid : G.r (secondEmbedding x) (secondEmbedding y) :=
      Relation.EqvGen.rel _ _ (Or.inr ⟨x,y,rfl,rfl,h⟩)
    exact G.trans (exterior_second_leg p x) (G.trans hmid (G.symm (exterior_second_leg p y)))

theorem identityPartition_brauer (n : ℕ) (x : (Bool × Fin n)) :
    blockSize (identityPartition n) x = 2 := by
  let e : {y : (Bool × Fin n) // (identityPartition n).r x y} ≃ Bool := {
    toFun := fun y => y.val.1
    invFun := fun b => ⟨(b,x.2),rfl⟩
    left_inv := by
      intro y
      apply Subtype.ext
      exact Prod.ext rfl y.property
    right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (by simp)


private theorem involution_sameCycle {X : Type*} [Finite X] (p : Equiv.Perm X)
    (hp : Function.Involutive p) (x y : X) : p.SameCycle x y ↔ x = y ∨ p x = y := by
  have hpow : p ^ 2 = 1 := by exact Equiv.ext hp
  have ho : orderOf p ≤ 2 := Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one hpow)
  constructor
  · intro h
    obtain ⟨i,hi,hix⟩ := h.exists_pow_eq'
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · exact Or.inl (by simpa using hix)
    · exact Or.inr (by simpa using hix)
  · rintro (rfl | h)
    · exact Equiv.Perm.SameCycle.refl _ _
    · exact h ▸ (Equiv.Perm.SameCycle.refl p x).apply_right

private theorem overlay_endpoint_characterization {X : Type*} [Finite X]
    (s r : Equiv.Perm X) (hs : Function.Involutive s) (hr : Function.Involutive r)
    (x y : {z : X // r z = z}) :
    Relation.EqvGen (fun u v => s u = v ∨ r u = v) (x : X) (y : X) ↔
      x = y ∨ endpointPairing s r hs hr x = y := by
  letI : Std.Symm (fun u v : X => s u = v ∨ r u = v) := ⟨by
    intro u v h
    rcases h with h | h
    · left; rw [← h]; exact hs u
    · right; rw [← h]; exact hr u⟩
  rw [Relation.EqvGen.eqvGen_eq_reflTransGen]
  change Connected s r x y ↔ _
  rw [connected_iff_rotation_orbits s r hs hr]
  have he : s (x : X) = (s * r) x := by simp [Equiv.Perm.mul_apply,x.property]
  rw [he,Equiv.Perm.sameCycle_apply_left,or_self]
  have h := endpoint_pairing_reattach_same_cycle s r hs hr 1 x y
  have h' : (s * r).SameCycle x y ↔ (endpointPairing s r hs hr).SameCycle x y := by
    simpa using h
  rw [h',involution_sameCycle _ (endpoint_pairing_involutive s r hs hr)]

private def expandedGlueFun {n : ℕ} : ((Bool × Fin n) ⊕ (Bool × Fin n)) → ((Bool × Fin n) ⊕ (Bool × Fin n))
  | .inl (false,i) => .inl (false,i)
  | .inl (true,i) => .inr (false,i)
  | .inr (false,i) => .inl (true,i)
  | .inr (true,i) => .inr (true,i)

private theorem expandedGlue_involutive {n : ℕ} :
    Function.Involutive (@expandedGlueFun n) := by
  intro x
  rcases x with ⟨b,i⟩ | ⟨b,i⟩ <;> cases b <;> rfl

private def expandedGlue {n : ℕ} : Equiv.Perm (((Bool × Fin n) ⊕ (Bool × Fin n))) :=
  Function.Involutive.toPerm expandedGlueFun expandedGlue_involutive


private def expandedProjection {n : ℕ} : ((Bool × Fin n) ⊕ (Bool × Fin n)) → (Fin 3 × Fin n) :=
  Sum.elim firstEmbedding secondEmbedding

private def expandedExterior {n : ℕ} (x : (Bool × Fin n)) : ((Bool × Fin n) ⊕ (Bool × Fin n)) :=
  if x.1 then Sum.inr x else Sum.inl x

private theorem expandedProjection_glue {n : ℕ} (x : ((Bool × Fin n) ⊕ (Bool × Fin n))) :
    expandedProjection (expandedGlue x) = expandedProjection x := by
  rcases x with ⟨b,i⟩ | ⟨b,i⟩ <;> cases b <;> rfl

private def expandedFixedEquiv (n : ℕ) : (Bool × Fin n) ≃ {z : ((Bool × Fin n) ⊕ (Bool × Fin n)) // expandedGlue z = z} where
  toFun x := ⟨expandedExterior x,by rcases x with ⟨b,i⟩; cases b <;> rfl⟩
  invFun x := match x.val with
    | .inl (_,i) => (false,i)
    | .inr (_,i) => (true,i)
  left_inv := by rintro ⟨b,i⟩; cases b <;> rfl
  right_inv := by
    rintro ⟨x,hx⟩
    apply Subtype.ext
    rcases x with ⟨b,i⟩ | ⟨b,i⟩ <;> cases b
    · rfl
    · cases hx
    · cases hx
    · rfl

private theorem expandedMatching_involutive {n : ℕ} (p q : Equiv.Perm ((Bool × Fin n)))
    (hp : Function.Involutive p) (hq : Function.Involutive q) :
    Function.Involutive (Equiv.sumCongr p q) := by
  intro x
  cases x with
  | inl x => exact congrArg Sum.inl (hp x)
  | inr x => exact congrArg Sum.inr (hq x)

private abbrev expandedGraph {n : ℕ} (p q : Equiv.Perm ((Bool × Fin n))) : Setoid (((Bool × Fin n) ⊕ (Bool × Fin n))) :=
  Relation.EqvGen.setoid (fun u v => Equiv.sumCongr p q u = v ∨ expandedGlue u = v)

private theorem expandedProjection_kernel {n : ℕ} (p q : Equiv.Perm ((Bool × Fin n))) :
    Setoid.ker expandedProjection ≤ expandedGraph p q := by
  intro u v h
  cases u with
  | inl x =>
    cases v with
    | inl y =>
      have he := firstEmbedding_injective h
      subst y
      exact Relation.EqvGen.refl _
    | inr y =>
      rcases x with ⟨a,i⟩
      rcases y with ⟨b,j⟩
      cases a <;> cases b <;> simp [Setoid.ker,expandedProjection,firstEmbedding,
        secondEmbedding,Prod.mk.injEq] at h
      subst j
      exact Relation.EqvGen.rel _ _ (Or.inr rfl)
  | inr x =>
    cases v with
    | inr y =>
      have he := secondEmbedding_injective h
      subst y
      exact Relation.EqvGen.refl _
    | inl y =>
      rcases x with ⟨a,i⟩
      rcases y with ⟨b,j⟩
      cases a <;> cases b <;> simp [Setoid.ker,expandedProjection,firstEmbedding,
        secondEmbedding,Prod.mk.injEq] at h
      subst j
      exact Relation.EqvGen.rel _ _ (Or.inr rfl)

private theorem expandedProjection_graph {n : ℕ} (p q : Equiv.Perm ((Bool × Fin n)))
    (hp : Function.Involutive p) (hq : Function.Involutive q) :
    (expandedGraph p q).map expandedProjection =
      productGraph (involutionSetoid p hp) (involutionSetoid q hq) := by
  apply le_antisymm
  · apply Setoid.gc_map_comap.le_iff_le.mpr
    apply Setoid.eqvGen_le
    intro u v he
    rcases he with he | he
    · subst v
      cases u with
      | inl x => exact Relation.EqvGen.rel _ _ (Or.inl ⟨x,p x,rfl,rfl,Or.inr rfl⟩)
      | inr x => exact Relation.EqvGen.rel _ _ (Or.inr ⟨x,q x,rfl,rfl,Or.inr rfl⟩)
    · subst v
      change (productGraph (involutionSetoid p hp) (involutionSetoid q hq)).r
        (expandedProjection u) (expandedProjection (expandedGlue u))
      rw [expandedProjection_glue]
  · apply Setoid.eqvGen_le
    intro u v he
    rcases he with ⟨x,y,rfl,rfl,h⟩ | ⟨x,y,rfl,rfl,h⟩
    · change x = y ∨ p x = y at h
      rcases h with rfl | h
      · exact (Setoid.map (expandedGraph p q) expandedProjection).refl _
      · exact Relation.EqvGen.rel _ _ ⟨Sum.inl x,Sum.inl y,
          Relation.EqvGen.rel _ _ (Or.inl (congrArg Sum.inl h)),rfl,rfl⟩
    · change x = y ∨ q x = y at h
      rcases h with rfl | h
      · exact (Setoid.map (expandedGraph p q) expandedProjection).refl _
      · exact Relation.EqvGen.rel _ _ ⟨Sum.inr x,Sum.inr y,
          Relation.EqvGen.rel _ _ (Or.inl (congrArg Sum.inr h)),rfl,rfl⟩

private theorem expanded_product_relation {n : ℕ} (p q : Equiv.Perm ((Bool × Fin n)))
    (hp : Function.Involutive p) (hq : Function.Involutive q) :
    partitionProduct (involutionSetoid p hp) (involutionSetoid q hq) =
      Setoid.comap expandedExterior (expandedGraph p q) := by
  have he : (@expandedProjection n) ∘ expandedExterior = exteriorEmbedding := by
    funext x
    rcases x with ⟨b,i⟩
    cases b <;> rfl
  change Setoid.comap exteriorEmbedding
    (productGraph (involutionSetoid p hp) (involutionSetoid q hq)) = _
  rw [← expandedProjection_graph p q hp hq,← he,Setoid.comap_comp,
    Setoid.comap_map_of_ker_le expandedProjection _ (expandedProjection_kernel p q)]

/-- The literal product is the involution induced by the existing endpoint-pairing supplier. -/
private theorem partitionProduct_involution_representation {n : ℕ}
    (p q : Equiv.Perm ((Bool × Fin n))) (hp : Function.Involutive p) (hq : Function.Involutive q) :
    ∃ t : Equiv.Perm ((Bool × Fin n)), ∃ ht : Function.Involutive t,
      partitionProduct (involutionSetoid p hp) (involutionSetoid q hq) = involutionSetoid t ht ∧
      ((∀ x, p x ≠ x) → (∀ x, q x ≠ x) → ∀ x, t x ≠ x) := by
  let s := Equiv.sumCongr p q
  have hs : Function.Involutive s := expandedMatching_involutive p q hp hq
  have hr : Function.Involutive (@expandedGlue n) := expandedGlue_involutive
  let e := expandedFixedEquiv n
  let P := D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.endpointPairing s expandedGlue hs hr
  have hP : Function.Involutive P :=
    D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.endpoint_pairing_involutive s expandedGlue hs hr
  let f : (Bool × Fin n) → (Bool × Fin n) := fun x => e.symm (P (e x))
  have hf : Function.Involutive f := by
    intro x
    simpa only [f,e.apply_symm_apply,e.symm_apply_apply] using congrArg e.symm (hP (e x))
  let t : Equiv.Perm ((Bool × Fin n)) := ⟨f,f,hf,hf⟩
  refine ⟨t,hf,?_,?_⟩
  · rw [expanded_product_relation p q hp hq]
    ext x y
    have h := overlay_endpoint_characterization s expandedGlue hs hr (e x) (e y)
    change (expandedGraph p q).r (expandedExterior x) (expandedExterior y) ↔ x = y ∨ f x = y
    constructor
    · intro hxy
      rcases h.mp hxy with he | he
      · exact Or.inl (e.injective he)
      · exact Or.inr ((congrArg e.symm he).trans (e.symm_apply_apply y))
    · rintro (rfl | he)
      · exact (expandedGraph p q).refl _
      · apply h.mpr
        right
        have h' := congrArg e he
        simpa only [f,e.apply_symm_apply] using h'
  · intro hpf hqf x hx
    have hsfree : ∀ z, s z ≠ z := by
      intro z hz
      cases z with
      | inl z => exact hpf z (Sum.inl.inj hz)
      | inr z => exact hqf z (Sum.inr.inj hz)
    have hPf := D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.endpoint_pairing_fixed_point_free
      s expandedGlue hs hr hsfree (e x)
    apply hPf
    change e.symm (P (e x)) = x at hx
    have h := congrArg e hx
    simpa only [e.apply_symm_apply] using h

theorem partitionProductPartialClosed {n : ℕ} (a b : PartialBrauer n) (x : (Bool × Fin n)) :
    blockSize (partitionProduct a.val b.val) x ≤ 2 := by
  obtain ⟨p,hp,he⟩ := partial_brauer_matching_representation a
  obtain ⟨q,hq,hf⟩ := partial_brauer_matching_representation b
  obtain ⟨t,ht,hprod,_⟩ := partitionProduct_involution_representation p q hp hq
  rw [← he,← hf,hprod]
  exact involutionSetoidBlockLeTwo t ht x

private theorem partitionProduct_brauer_closed {n : ℕ} (a b : Brauer n) (x : (Bool × Fin n)) :
    blockSize (partitionProduct a.val b.val) x = 2 := by
  obtain ⟨p,hp,hpn,he⟩ := brauer_matching_representation a
  obtain ⟨q,hq,hqn,hf⟩ := brauer_matching_representation b
  obtain ⟨t,ht,hprod,hn⟩ := partitionProduct_involution_representation p q hp hq
  rw [← he,← hf,hprod]
  exact involutionSetoidBlockTwo t ht (hn hpn hqn) x

private noncomputable def brauerSourceAlgebra (n : ℕ) : Monoid (Brauer n) where
  mul a b := ⟨partitionProduct a.val b.val,partitionProduct_brauer_closed a b⟩
  one := ⟨identityPartition n,identityPartition_brauer n⟩
  mul_assoc a b c := Subtype.ext (partitionProduct_assoc a.val b.val c.val)
  one_mul a := Subtype.ext (partitionProduct_identity_left a.val)
  mul_one a := Subtype.ext (partitionProduct_identity_right a.val)

private noncomputable def partialBrauerSourceAlgebra (n : ℕ) : Monoid (PartialBrauer n) where
  mul a b := ⟨partitionProduct a.val b.val,partitionProductPartialClosed a b⟩
  one := ⟨identityPartition n,fun x => (identityPartition_brauer n x).le⟩
  mul_assoc a b c := Subtype.ext (partitionProduct_assoc a.val b.val c.val)
  one_mul a := Subtype.ext (partitionProduct_identity_left a.val)
  mul_one a := Subtype.ext (partitionProduct_identity_right a.val)

private noncomputable def brauerSource (n : ℕ) : BrauerSourceMonoid n where
  algebra := brauerSourceAlgebra n
  multiplication _ _ := rfl

private noncomputable def partialBrauerSource (n : ℕ) : PartialBrauerSourceMonoid n where
  algebra := partialBrauerSourceAlgebra n
  multiplication _ _ := rfl

theorem source_monoids_exist (n : ℕ) :
    (∃ _B : BrauerSourceMonoid n, True) ∧ (∃ _PB : PartialBrauerSourceMonoid n, True) :=
  ⟨⟨brauerSource n,True.intro⟩,⟨partialBrauerSource n,True.intro⟩⟩

end D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSourceMonoids
