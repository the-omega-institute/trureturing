/- GID: D5/S3/Combinatorics/Lattices/EuclideanSaturation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Lattices/EuclideanSaturation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bases of primitive submodules extend through a torsion-free quotient. -/

import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Abel
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain

/-! Integral basis extension by splitting the torsion-free quotient. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Lattices.EuclideanSaturation

attribute [-instance] AddCommGroup.toIntModule

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

/-- A primitive submodule has torsion-free quotient. -/
private theorem quotientTorsionFree (N : Submodule ℤ M)
    (hsat : ∀ (n : ℤ) (x : M), n ≠ 0 → n • x ∈ N → x ∈ N) :
    Module.IsTorsionFree ℤ (M ⧸ N) := by
  refine Module.IsTorsionFree.of_smul_eq_zero ?_
  intro n q h
  by_cases hn : n = 0
  · exact Or.inl hn
  · right
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      have hz := int_smul_eq_zsmul (inferInstance : Module ℤ M) n x
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hsat n x hn (hz ▸ h))

/-- Saturation by a characteristic-zero vector-space span implies primitivity. -/
private theorem quotientTorsionFreeOfSpan {K : Type*} [Field K] [CharZero K] [Module K M]
    (A B : Submodule ℤ M)
    (hsat : ∀ x : M, x ∈ A → x ∈ Submodule.span K (B : Set M) → x ∈ B) :
    Module.IsTorsionFree ℤ (A ⧸ B.comap A.subtype) := by
  refine quotientTorsionFree (B.comap A.subtype) ?_
  intro n x hn hx
  change (x : M) ∈ B
  apply hsat x x.property
  have hx' : (n : K) • (x : M) ∈ Submodule.span K (B : Set M) := by
    rw [Int.cast_smul_eq_zsmul K]
    exact Submodule.subset_span hx
  exact (Submodule.smul_mem_iff _ (Int.cast_ne_zero.mpr hn)).mp hx'

private def splitSum (N : Submodule ℤ M) (s : (M ⧸ N) →ₗ[ℤ] M) :
    (N × (M ⧸ N)) →ₗ[ℤ] M :=
  N.subtype.comp (LinearMap.fst ℤ N (M ⧸ N)) +
    s.comp (LinearMap.snd ℤ N (M ⧸ N))

private theorem splitSum_bijective (N : Submodule ℤ M) (s : (M ⧸ N) →ₗ[ℤ] M)
    (hs : N.mkQ.comp s = LinearMap.id) : Function.Bijective (splitSum N s) := by
  have hsq (x : M ⧸ N) : N.mkQ (s x) = x := congrArg (fun f => f x) hs
  have hsn (x : N) : N.mkQ (x : M) = 0 :=
    (Submodule.Quotient.mk_eq_zero N).mpr x.property
  constructor
  · intro x y hxy
    have hq := congrArg N.mkQ hxy
    have hsecond : x.2 = y.2 := by
      change N.mkQ ((x.1 : M) + s x.2) = N.mkQ ((y.1 : M) + s y.2) at hq
      simpa only [map_add, hsn, hsq, zero_add] using hq
    have hfirst : x.1 = y.1 := by
      apply Subtype.ext
      simpa [splitSum, hsecond] using hxy
    exact Prod.ext hfirst hsecond
  · intro x
    have hx : x - s (N.mkQ x) ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero]
      change N.mkQ (x - s (N.mkQ x)) = 0
      rw [map_sub, hsq, sub_self]
    refine ⟨(⟨x - s (N.mkQ x), hx⟩, N.mkQ x), ?_⟩
    simp [splitSum]

private def meetLeft (A B : Submodule ℤ M) : Submodule ℤ A :=
  (A ⊓ B).comap A.subtype

private def meetRight (A B : Submodule ℤ M) : Submodule ℤ B :=
  (A ⊓ B).comap B.subtype

private def leftMeetEquiv (A B : Submodule ℤ M) :
    (A ⊓ B : Submodule ℤ M) ≃ₗ[ℤ] meetLeft A B where
  toFun x := ⟨⟨x, x.property.1⟩, x.property⟩
  invFun x := ⟨((x : A) : M), x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def rightMeetEquiv (A B : Submodule ℤ M) :
    (A ⊓ B : Submodule ℤ M) ≃ₗ[ℤ] meetRight A B where
  toFun x := ⟨⟨x, x.property.2⟩, x.property⟩
  invFun x := ⟨((x : B) : M), x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def sumSplit (A B : Submodule ℤ M)
    (sA : (A ⧸ meetLeft A B) →ₗ[ℤ] A) (sB : (B ⧸ meetRight A B) →ₗ[ℤ] B) :
    ((A ⊓ B : Submodule ℤ M) × ((A ⧸ meetLeft A B) × (B ⧸ meetRight A B))) →ₗ[ℤ]
      (A ⊔ B : Submodule ℤ M) :=
  (Submodule.inclusion (inf_le_left.trans le_sup_left)).comp
      (LinearMap.fst ℤ (A ⊓ B : Submodule ℤ M) _) +
    (Submodule.inclusion le_sup_left).comp
      (sA.comp ((LinearMap.fst ℤ _ _).comp
        (LinearMap.snd ℤ (A ⊓ B : Submodule ℤ M) _))) +
    (Submodule.inclusion le_sup_right).comp
      (sB.comp ((LinearMap.snd ℤ _ _).comp
        (LinearMap.snd ℤ (A ⊓ B : Submodule ℤ M) _)))

private theorem sumSplit_bijective (A B : Submodule ℤ M)
    (sA : (A ⧸ meetLeft A B) →ₗ[ℤ] A) (sB : (B ⧸ meetRight A B) →ₗ[ℤ] B)
    (hsA : (meetLeft A B).mkQ.comp sA = LinearMap.id)
    (hsB : (meetRight A B).mkQ.comp sB = LinearMap.id) :
    Function.Bijective (sumSplit A B sA sB) := by
  have hqA (q : A ⧸ meetLeft A B) : (meetLeft A B).mkQ (sA q) = q :=
    congrArg (fun f => f q) hsA
  have hqB (q : B ⧸ meetRight A B) : (meetRight A B).mkQ (sB q) = q :=
    congrArg (fun f => f q) hsB
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    have hx' := congrArg Subtype.val hx
    change (x.1 : M) + (sA x.2.1 : M) + (sB x.2.2 : M) = 0 at hx'
    have haB : (sA x.2.1 : M) ∈ B := by
      have haeq : (sA x.2.1 : M) = -((x.1 : M) + (sB x.2.2 : M)) := by
        apply eq_neg_iff_add_eq_zero.mpr
        simpa only [add_assoc, add_left_comm, add_comm] using hx'
      rw [haeq]
      exact B.neg_mem (B.add_mem x.1.property.2 (sB x.2.2).property)
    have hxa : x.2.1 = 0 := by
      rw [← hqA x.2.1]
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (show (sA x.2.1 : M) ∈ A ⊓ B from ⟨(sA x.2.1).property, haB⟩)
    have hbA : (sB x.2.2 : M) ∈ A := by
      have hbeq : (sB x.2.2 : M) = -(x.1 : M) := by
        apply eq_neg_iff_add_eq_zero.mpr
        simpa only [hxa, map_zero, Submodule.coe_zero, add_zero, add_comm] using hx'
      rw [hbeq]
      exact A.neg_mem x.1.property.1
    have hxb : x.2.2 = 0 := by
      rw [← hqB x.2.2]
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (show (sB x.2.2 : M) ∈ A ⊓ B from ⟨hbA, (sB x.2.2).property⟩)
    have hxc : x.1 = 0 := by
      apply Subtype.ext
      simpa only [hxa, hxb, map_zero, Submodule.coe_zero, add_zero] using hx'
    exact Prod.ext hxc (Prod.ext hxa hxb)
  · intro x
    obtain ⟨a, b, hab⟩ := Submodule.mem_sup'.mp x.property
    let qa := (meetLeft A B).mkQ a
    let qb := (meetRight A B).mkQ b
    have ha : a - sA qa ∈ meetLeft A B := by
      rw [← Submodule.Quotient.mk_eq_zero]
      change (meetLeft A B).mkQ (a - sA qa) = 0
      rw [map_sub, hqA]
      exact sub_self _
    have hb : b - sB qb ∈ meetRight A B := by
      rw [← Submodule.Quotient.mk_eq_zero]
      change (meetRight A B).mkQ (b - sB qb) = 0
      rw [map_sub, hqB]
      exact sub_self _
    let c : (A ⊓ B : Submodule ℤ M) :=
      ⟨((a - sA qa : A) : M) + ((b - sB qb : B) : M),
      (A ⊓ B).add_mem ha hb⟩
    refine ⟨(c, qa, qb), ?_⟩
    apply Subtype.ext
    change (c : M) + (sA qa : M) + (sB qb : M) = (x : M)
    dsimp [c]
    rw [← hab]
    abel

/-- Simultaneous bases with a common intersection block. -/
structure Adapted {ι : Type*} (A B : Submodule ℤ M)
    (c : Module.Basis ι ℤ (A ⊓ B : Submodule ℤ M)) where
  a : Module.Basis (ι ⊕ Fin (Module.finrank ℤ (A ⧸ meetLeft A B))) ℤ A
  b : Module.Basis (ι ⊕ Fin (Module.finrank ℤ (B ⧸ meetRight A B))) ℤ B
  total : Module.Basis
    (ι ⊕ (Fin (Module.finrank ℤ (A ⧸ meetLeft A B)) ⊕
      Fin (Module.finrank ℤ (B ⧸ meetRight A B)))) ℤ (A ⊔ B : Submodule ℤ M)
  a_left : ∀ i, (a (Sum.inl i) : M) = c i
  b_left : ∀ i, (b (Sum.inl i) : M) = c i
  total_left : ∀ i, (total (Sum.inl i) : M) = c i
  total_a : ∀ i, (total (Sum.inr (Sum.inl i)) : M) = a (Sum.inr i)
  total_b : ∀ i, (total (Sum.inr (Sum.inr i)) : M) = b (Sum.inr i)

/-- The intersection and the two quotient bases give an integral basis of the sum. -/
private def adaptedBases {ι : Type*} (A B : Submodule ℤ M)
    [Module.Finite ℤ A] [Module.Finite ℤ B]
    [Module.IsTorsionFree ℤ (A ⧸ meetLeft A B)]
    [Module.IsTorsionFree ℤ (B ⧸ meetRight A B)]
    (c : Module.Basis ι ℤ (A ⊓ B : Submodule ℤ M)) : Adapted A B c := by
  letI : Module.Free ℤ (A ⧸ meetLeft A B) :=
    Module.free_of_finite_type_torsion_free'
  letI : Module.Free ℤ (B ⧸ meetRight A B) :=
    Module.free_of_finite_type_torsion_free'
  let splittingA := Module.projective_lifting_property (meetLeft A B).mkQ
    (LinearMap.id : (A ⧸ meetLeft A B) →ₗ[ℤ] _) (meetLeft A B).mkQ_surjective
  let sA := Classical.choose splittingA
  have hsA := Classical.choose_spec splittingA
  let splittingB := Module.projective_lifting_property (meetRight A B).mkQ
    (LinearMap.id : (B ⧸ meetRight A B) →ₗ[ℤ] _) (meetRight A B).mkQ_surjective
  let sB := Classical.choose splittingB
  have hsB := Classical.choose_spec splittingB
  let eA := ((leftMeetEquiv A B).prodCongr
        (LinearEquiv.refl ℤ (A ⧸ meetLeft A B))).trans
    (LinearEquiv.ofBijective (splitSum (meetLeft A B) sA)
      (splitSum_bijective (meetLeft A B) sA hsA))
  let eB := ((rightMeetEquiv A B).prodCongr
        (LinearEquiv.refl ℤ (B ⧸ meetRight A B))).trans
    (LinearEquiv.ofBijective (splitSum (meetRight A B) sB)
      (splitSum_bijective (meetRight A B) sB hsB))
  let eS := LinearEquiv.ofBijective (sumSplit A B sA sB)
    (sumSplit_bijective A B sA sB hsA hsB)
  let qA := Module.finBasis ℤ (A ⧸ meetLeft A B)
  let qB := Module.finBasis ℤ (B ⧸ meetRight A B)
  refine ⟨(c.prod qA).map eA, (c.prod qB).map eB,
    (c.prod (qA.prod qB)).map eS, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro i
    simp [eA, eB, eS, leftMeetEquiv, rightMeetEquiv, splitSum, sumSplit,
      Module.Basis.map_apply, Module.Basis.prod_apply,
      LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply]

/-- Saturated submodules admit compatible intersection and sum bases. -/
def adaptedBasesOfSaturated {K : Type*} [Field K] [CharZero K] [Module K M]
    {ι : Type*} (L A B : Submodule ℤ M) [Module.Finite ℤ A] [Module.Finite ℤ B]
    (hAL : A ≤ L) (hBL : B ≤ L)
    (hA : ∀ x : M, x ∈ L → x ∈ Submodule.span K (A : Set M) → x ∈ A)
    (hB : ∀ x : M, x ∈ L → x ∈ Submodule.span K (B : Set M) → x ∈ B)
    (c : Module.Basis ι ℤ (A ⊓ B : Submodule ℤ M)) : Adapted A B c := by
  letI : Module.IsTorsionFree ℤ (A ⧸ meetLeft A B) :=
    quotientTorsionFreeOfSpan (K := K) A (A ⊓ B) fun x hx hxspan =>
      ⟨hx, hB x (hAL hx)
        ((Submodule.span_mono (show (A ⊓ B : Set M) ⊆ B from inf_le_right)) hxspan)⟩
  letI : Module.IsTorsionFree ℤ (B ⧸ meetRight A B) :=
    quotientTorsionFreeOfSpan (K := K) B (A ⊓ B) fun x hx hxspan =>
      ⟨hA x (hBL hx)
        ((Submodule.span_mono (show (A ⊓ B : Set M) ⊆ A from inf_le_left)) hxspan), hx⟩
  exact adaptedBases A B c

end D5.S3.Combinatorics.Lattices.EuclideanSaturation
