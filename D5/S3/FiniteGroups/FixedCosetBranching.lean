/- GID: D5/S3/FiniteGroups/FixedCosetBranching
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/FixedCosetBranching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Support and cardinality of fixed left cosets from two conjugation counts. -/

import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Subgroup.Centralizer
import OmegaBuild.Commands

/-!
The degree-`g` count in Davydov–Simmons (arXiv:1603.04650, Remark 2.22,
Theorem 4.8 at `(g, 1)`, and §4.3) uses the fixed left cosets for the
action of `g` on `G ⧸ K`. The quotient map and the conjugation map
partition the same set of lifts, with fibers given by translates of `K`
and of the centralizer of `g`, respectively.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.FiniteGroups.FixedCosetBranching

open scoped BigOperators Pointwise

variable {G : Type*} [Group G] (K : Subgroup G) (g : G)

/-- Left cosets fixed by left multiplication by `g`. -/
abbrev FixedCosets := ↥(MulAction.fixedBy (G ⧸ K) g)

/-- The intersection of the ambient conjugacy class of `g` with `K`. -/
abbrev ConjugatesIn := ↥((ConjClasses.mk g).carrier ∩ (K : Set G))

/-- Representatives whose inverse conjugation carries `g` into `K`. -/
abbrev ConjugatingElements := {x : G // x⁻¹ * g * x ∈ K}

/-- The left coset of `x` is fixed exactly when `x⁻¹ * g * x` lies in `K`. -/
private theorem mk_mem_fixedBy_iff (x : G) :
    (x : G ⧸ K) ∈ MulAction.fixedBy (G ⧸ K) g ↔ x⁻¹ * g * x ∈ K := by
  rw [MulAction.mem_fixedBy, MulAction.Quotient.smul_coe K, smul_eq_mul, eq_comm]
  simpa only [mul_assoc] using (QuotientGroup.eq (s := K) (a := x) (b := g * x))

/-- Send a representative to its fixed left coset. -/
def toFixedCoset (x : ConjugatingElements K g) : FixedCosets K g :=
  ⟨(x.val : G ⧸ K), (mk_mem_fixedBy_iff K g x.val).mpr x.property⟩

private theorem toFixedCoset_surjective : Function.Surjective (toFixedCoset K g) := by
  intro q
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (s := K) q.val
  have hfixed : (x : G ⧸ K) ∈ MulAction.fixedBy (G ⧸ K) g := hx.symm ▸ q.property
  exact ⟨⟨x, (mk_mem_fixedBy_iff K g x).mp hfixed⟩, Subtype.ext hx⟩

/-- Send a representative to the conjugate `x⁻¹ * g * x` in `K`. -/
def toConjugate (x : ConjugatingElements K g) : ConjugatesIn K g := by
  have hconj : IsConj g (x.val⁻¹ * g * x.val) :=
    isConj_iff.mpr ⟨x.val⁻¹, by rw [inv_inv]⟩
  exact ⟨x.val⁻¹ * g * x.val, ⟨hconj, x.property⟩⟩

private theorem toConjugate_surjective : Function.Surjective (toConjugate K g) := by
  intro z
  have hz : IsConj g z.val := z.property.1
  obtain ⟨a, ha⟩ := isConj_iff.mp hz
  have heq : (a⁻¹)⁻¹ * g * a⁻¹ = z.val := by simpa only [inv_inv] using ha
  have hmem : (a⁻¹)⁻¹ * g * a⁻¹ ∈ K := heq.symm ▸ z.property.2
  exact ⟨⟨a⁻¹, hmem⟩, Subtype.ext heq⟩

/-- Fixed left cosets exist exactly when the ambient conjugacy class meets `K`. -/
theorem fixedCosets_nonempty_iff :
    Nonempty (FixedCosets K g) ↔ ((ConjClasses.mk g).carrier ∩ (K : Set G)).Nonempty := by
  constructor
  · rintro ⟨q⟩
    obtain ⟨x, _⟩ := toFixedCoset_surjective K g q
    exact ⟨(toConjugate K g x).val, (toConjugate K g x).property⟩
  · rintro ⟨z, hz⟩
    obtain ⟨x, _⟩ := toConjugate_surjective K g ⟨z, hz⟩
    exact ⟨toFixedCoset K g x⟩

/-- A representative of a fixed coset identifies the quotient fiber with `K`. -/
def fixedCosetFiberEquiv (q : FixedCosets K g) (x : G) (hx : (x : G ⧸ K) = q.val) :
    {y : ConjugatingElements K g // toFixedCoset K g y = q} ≃ K := by
  have hcoset (y : G) : y ∈ x • (K : Set G) ↔ (y : G ⧸ K) = q.val := by
    rw [← QuotientGroup.eq_class_eq_leftCoset K x]
    change ((y : G ⧸ K) = (x : G ⧸ K)) ↔ _
    rw [hx]
  refine (show {y : ConjugatingElements K g // toFixedCoset K g y = q} ≃
    ↥(x • (K : Set G)) from ?_).trans (Subgroup.leftCosetEquivSubgroup x)
  refine
    { toFun := fun y => ⟨y.val.val, (hcoset _).mpr (congrArg Subtype.val y.property)⟩
      invFun := fun y => ?_
      left_inv := ?_
      right_inv := ?_ }
  · have hy := (hcoset y.val).mp y.property
    have hfixed : (y.val : G ⧸ K) ∈ MulAction.fixedBy (G ⧸ K) g := hy.symm ▸ q.property
    exact ⟨⟨y.val, (mk_mem_fixedBy_iff K g y.val).mp hfixed⟩, Subtype.ext hy⟩
  · intro y
    rfl
  · intro y
    rfl

private theorem same_conjugate_iff (x y : G) :
    y⁻¹ * g * y = x⁻¹ * g * x ↔ y * x⁻¹ ∈ Subgroup.centralizer ({g} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc
      y * x⁻¹ * g = y * (x⁻¹ * g * x) * x⁻¹ := by simp [mul_assoc]
      _ = y * (y⁻¹ * g * y) * x⁻¹ := by rw [h]
      _ = g * (y * x⁻¹) := by simp [← mul_assoc]
  · intro h
    calc
      y⁻¹ * g * y = y⁻¹ * (g * (y * x⁻¹)) * x := by simp [mul_assoc]
      _ = y⁻¹ * (y * x⁻¹ * g) * x := by rw [h]
      _ = x⁻¹ * g * x := by simp [← mul_assoc]

/-- A lift of a conjugate identifies the conjugation fiber with the centralizer of `g`. -/
def conjugateFiberEquiv (z : ConjugatesIn K g) (x : G) (hx : x⁻¹ * g * x = z.val) :
    {y : ConjugatingElements K g // toConjugate K g y = z} ≃
      Subgroup.centralizer ({g} : Set G) := by
  let C := Subgroup.centralizer ({g} : Set G)
  have hcoset (y : G) :
      y ∈ MulOpposite.op x • (C : Set G) ↔ y⁻¹ * g * y = z.val := by
    rw [mem_rightCoset_iff]
    change y * x⁻¹ ∈ Subgroup.centralizer ({g} : Set G) ↔ _
    rw [← same_conjugate_iff g x y, hx]
  refine (show {y : ConjugatingElements K g // toConjugate K g y = z} ≃
    ↥(MulOpposite.op x • (C : Set G)) from ?_).trans (Subgroup.rightCosetEquivSubgroup x)
  refine
    { toFun := fun y => ⟨y.val.val, (hcoset _).mpr (congrArg Subtype.val y.property)⟩
      invFun := fun y => ?_
      left_inv := ?_
      right_inv := ?_ }
  · have hy := (hcoset y.val).mp y.property
    have hmem : y.val⁻¹ * g * y.val ∈ K := hy.symm ▸ z.property.2
    exact ⟨⟨y.val, hmem⟩, Subtype.ext hy⟩
  · intro y
    rfl
  · intro y
    rfl

private theorem card_eq_card_mul_of_fiber_card {A B : Type*} [Finite A] [Finite B]
    (f : A → B) (n : ℕ) (hfiber : ∀ b, Nat.card {a : A // f a = b} = n) :
    Nat.card A = Nat.card B * n := by
  letI := Fintype.ofFinite B
  calc
    Nat.card A = Nat.card (Σ b : B, {a : A // f a = b}) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv f).symm
    _ = ∑ b : B, Nat.card {a : A // f a = b} := Nat.card_sigma
    _ = Nat.card B * n := by
      simp only [hfiber, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
        Nat.card_eq_fintype_card]

/-- Counting representatives by the two maps gives the number of degree-`g` labels. -/
theorem card_fixedCosets_mul_card_subgroup [Finite G] :
    Nat.card (FixedCosets K g) * Nat.card K =
      Nat.card (Subgroup.centralizer ({g} : Set G)) * Nat.card (ConjugatesIn K g) := by
  have hFixed := card_eq_card_mul_of_fiber_card (toFixedCoset K g) (Nat.card K) fun q => by
    obtain ⟨x, hx⟩ := toFixedCoset_surjective K g q
    exact Nat.card_congr (fixedCosetFiberEquiv K g q x.val (congrArg Subtype.val hx))
  have hConj := card_eq_card_mul_of_fiber_card (toConjugate K g)
      (Nat.card (Subgroup.centralizer ({g} : Set G))) fun z => by
    obtain ⟨x, hx⟩ := toConjugate_surjective K g z
    exact Nat.card_congr (conjugateFiberEquiv K g z x.val (congrArg Subtype.val hx))
  calc
    _ = Nat.card (ConjugatingElements K g) := hFixed.symm
    _ = Nat.card (ConjugatesIn K g) * Nat.card (Subgroup.centralizer ({g} : Set G)) := hConj
    _ = _ := Nat.mul_comm _ _

end D5.S3.FiniteGroups.FixedCosetBranching
