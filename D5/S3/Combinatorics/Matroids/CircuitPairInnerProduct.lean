/- GID: D5/S3/Combinatorics/Matroids/CircuitPairInnerProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/CircuitPairInnerProduct
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: The signed cross pairing of two matroid circuit summands. -/

module

public import D5.S3.Combinatorics.Matroids.CircuitCycleDecomposition
public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic.Ring

/-! The cross pairing of oriented circuit lifts factors through contraction of their union. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped Matroid

namespace D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct

open OrderedCycleFactorization CircuitCycleDecomposition
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)

variable {V : Type*} [LinearOrder V]

/-- The union has two more elements than its rank. -/
def UnionNullityTwo (M : Matroid V) (C D : Finset V) : Prop :=
  M.eRk (↑(C ∪ D) : Set V) + 2 = (↑(C ∪ D).card : ℕ∞)

private abbrev twoErases (C D : Finset V) (x y : V) :=
  C.erase x ∪ D.erase y

private lemma twoErases_eq {C D : Finset V} {x y : V}
    (hx : x ∈ C \ D) (hy : y ∈ D \ C) :
    twoErases C D x y = ((C ∪ D).erase x).erase y := by
  ext a
  simp only [twoErases, mem_union, mem_erase, mem_sdiff] at *
  aesop

private lemma twoErases_nullity_iff {M : Matroid V} {C D : Finset V} {x y : V}
    (hC : M.IsCircuit (C : Set V)) (hD : M.IsCircuit (D : Set V))
    (hx : x ∈ C \ D) (hy : y ∈ D \ C) :
    M.Indep (↑(twoErases C D x y) : Set V) ↔ UnionNullityTwo M C D := by
  have hxC := (mem_sdiff.mp hx).1
  have hyD := (mem_sdiff.mp hy).1
  have hyx : y ≠ x := fun h => (mem_sdiff.mp hy).2 (h.symm ▸ hxC)
  have hcl : M.closure (↑(twoErases C D x y) : Set V) =
      M.closure (↑(C ∪ D) : Set V) := by
    simp only [twoErases, coe_union]
    rw [M.closure_union_congr_left (circuit_erase_basis hC hxC).closure_eq_closure,
      M.closure_union_congr_right (circuit_erase_basis hD hyD).closure_eq_closure]
  have hrank : M.eRk (↑(twoErases C D x y) : Set V) = M.eRk (↑(C ∪ D) : Set V) := by
    rw [← M.eRk_closure_eq (↑(twoErases C D x y) : Set V), hcl, M.eRk_closure_eq]
  have hcard : (twoErases C D x y).card + 2 = (C ∪ D).card := by
    rw [twoErases_eq hx hy,
      card_erase_of_mem (mem_erase.mpr ⟨hyx, mem_union_right _ hyD⟩),
      card_erase_of_mem (mem_union_left _ hxC)]
    have hpos := card_pos.mpr ⟨y, mem_erase.mpr ⟨hyx, mem_union_right C hyD⟩⟩
    rw [card_erase_of_mem (mem_union_left D hxC)] at hpos
    omega
  rw [Matroid.indep_iff_eRk_eq_encard_of_finite (by simp), hrank, Set.encard_coe_eq_coe_finsetCard,
    UnionNullityTwo, ← hcard, Nat.cast_add, Nat.cast_ofNat]
  exact ⟨fun h => congrArg (· + 2) h,
    fun h => ENat.add_left_injective_of_ne_top (by norm_num : (2 : ℕ∞) ≠ ⊤) h⟩

private lemma twoErases_basis {M : Matroid V} {C D : Finset V} {x y : V}
    (hC : M.IsCircuit (C : Set V)) (hD : M.IsCircuit (D : Set V))
    (hx : x ∈ C \ D) (hy : y ∈ D \ C) (h : UnionNullityTwo M C D) :
    M.IsBasis (↑(twoErases C D x y) : Set V) (↑(C ∪ D) : Set V) := by
  refine Matroid.isBasis_iff_indep_subset_closure.mpr
    ⟨(twoErases_nullity_iff hC hD hx hy).mpr h, ?_, ?_⟩
  · exact_mod_cast union_subset_union (erase_subset x C) (erase_subset y D)
  · rw [coe_union, twoErases, coe_union]
    exact Set.union_subset
      ((circuit_erase_basis hC (mem_sdiff.mp hx).1).subset_closure.trans
        (M.closure_subset_closure Set.subset_union_left))
      ((circuit_erase_basis hD (mem_sdiff.mp hy).1).subset_closure.trans
        (M.closure_subset_closure Set.subset_union_right))

private lemma exclusive_nonempty {M : Matroid V} {C D : Finset V}
    (hC : M.IsCircuit (C : Set V)) (hD : M.IsCircuit (D : Set V)) (hCD : C ≠ D) :
    (C \ D).Nonempty := by
  by_contra h
  have hsub : C ⊆ D := sdiff_eq_empty_iff_subset.mp (not_nonempty_iff_eq_empty.mp h)
  exact hCD (coe_injective ((hD.eq_of_not_indep_subset hC.not_indep
    (by exact_mod_cast hsub))))

private lemma nullity_comm {M : Matroid V} {C D : Finset V} (h : UnionNullityTwo M C D) :
    UnionNullityTwo M D C := by simpa only [UnionNullityTwo, union_comm D C] using h

private lemma residual_circuit_right {M : Matroid V} {C D : Finset V}
    (hC : M.IsCircuit (C : Set V)) (hD : M.IsCircuit (D : Set V)) (hCD : C ≠ D)
    (h : UnionNullityTwo M C D) :
    (M ／ (C : Set V)).IsCircuit (↑(D \ C) : Set V) := by
  obtain ⟨x, hx⟩ := exclusive_nonempty hC hD hCD
  have hA := circuit_erase_basis hC (mem_sdiff.mp hx).1
  rw [coe_sdiff, Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep]
  refine ⟨hD.contract_dep_of_not_subset ?_, fun y hy => ?_⟩
  · obtain ⟨y, hy⟩ := exclusive_nonempty hD hC hCD.symm
    exact fun hs => (mem_sdiff.mp hy).2 (hs (mem_sdiff.mp hy).1)
  · have hy' : y ∈ D \ C := mem_sdiff.mpr hy
    have heq : ((D : Set V) \ (C : Set V)) \ {y} ∪ ↑(C.erase x) =
        (↑(twoErases C D x y) : Set V) := by
      ext a
      simp only [twoErases, coe_union, coe_erase, Set.mem_union, Set.mem_sdiff,
        Set.mem_singleton_iff, mem_coe, mem_sdiff] at *
      have hxa : a = x → a ∉ D := fun ha => ha.symm ▸ hx.2
      have hya : a = y → a ∉ C := fun ha => ha.symm ▸ hy.2
      tauto
    rw [hA.contract_indep_iff, heq]
    exact ⟨(twoErases_basis hC hD hx hy' h).indep,
      Set.disjoint_sdiff_right.mono_right Set.sdiff_subset⟩

private lemma circuits_ne_of_union_nullity_two {M : Matroid V} {C D : Finset V}
    (hC : M.IsCircuit (C : Set V)) (h : UnionNullityTwo M C D) : C ≠ D := by
  rintro rfl
  rw [UnionNullityTwo, union_self, ← Set.encard_coe_eq_coe_finsetCard,
    ← hC.eRk_add_one_eq] at h
  have hfinite : M.eRk (C : Set V) ≠ ⊤ :=
    (lt_of_le_of_lt (M.eRk_le_encard _) (by simp)).ne
  have htwo : (2 : ℕ∞) = 1 := ENat.add_right_injective_of_ne_top hfinite h
  norm_num at htwo

/-- At nullity two, each exclusive difference is a circuit after contracting the other circuit. -/
theorem residual_circuits {M : Matroid V} {C D : Finset V}
    (hC : M.IsCircuit (C : Set V)) (hD : M.IsCircuit (D : Set V))
    (h : UnionNullityTwo M C D) :
    (M ／ (C : Set V)).IsCircuit (↑(D \ C) : Set V) ∧
      (M ／ (D : Set V)).IsCircuit (↑(C \ D) : Set V) := by
  have hCD := circuits_ne_of_union_nullity_two hC h
  exact ⟨residual_circuit_right hC hD hCD h,
    residual_circuit_right hD hC hCD.symm (nullity_comm h)⟩

private lemma missing_vertices_exclusive [Finite V] {M : Matroid V} {C D F : Finset V} {x y : V}
    (hC : M.IsCircuit (C : Set V)) (hD : M.IsCircuit (D : Set V)) (hCD : C ≠ D)
    (hF : M.IsBase (F : Set V)) (hx : x ∈ C) (hy : y ∈ D)
    (hFC : F ∩ C = C.erase x) (hFD : F ∩ D = D.erase y) :
    x ∈ C \ D ∧ y ∈ D \ C := by
  let := Fintype.ofFinite V
  have hxF : x ∉ F := fun hm => notMem_erase x C (hFC ▸ mem_inter.mpr ⟨hm, hx⟩)
  have hyF : y ∉ F := fun hm => notMem_erase y D (hFD ▸ mem_inter.mpr ⟨hm, hy⟩)
  have hne : x ≠ y := by
    rintro rfl
    exact hCD ((circuit_eq_circuitAt ⟨C, hC, hx⟩ hF hFC).trans
      (circuit_eq_circuitAt ⟨D, hD, hy⟩ hF hFD).symm)
  refine ⟨mem_sdiff.mpr ⟨hx, fun hxD => hxF ?_⟩, mem_sdiff.mpr ⟨hy, fun hyC => hyF ?_⟩⟩
  · exact (mem_inter.mp (hFD.symm ▸ mem_erase.mpr ⟨hne, hxD⟩)).1
  · exact (mem_inter.mp (hFC.symm ▸ mem_erase.mpr ⟨hne.symm, hyC⟩)).1

private lemma unionBasis_of_shared {M : Matroid V} {C D F : Finset V} {x y : V}
    (hC : M.IsCircuit (C : Set V)) (hD : M.IsCircuit (D : Set V))
    (hF : M.IsBase (F : Set V)) (hx : x ∈ C \ D) (hy : y ∈ D \ C)
    (hFC : F ∩ C = C.erase x) (hFD : F ∩ D = D.erase y) :
    UnionNullityTwo M C D := by
  apply (twoErases_nullity_iff hC hD hx hy).mp
  apply hF.indep.subset
  have hsub : twoErases C D x y ⊆ F := by
    rw [twoErases, ← hFC, ← hFD]
    exact union_subset inter_subset_left inter_subset_left
  exact_mod_cast hsub

variable [Fintype V]

/-- The ambient coordinate inner product of two oriented circuit lifts. -/
def circuitPairing (C D : Finset V) (w v : Chain V) : ℤ :=
  ∑ F : Finset V, signedJoin C (simplexBoundary C) w F *
    signedJoin D (simplexBoundary D) v F

private lemma lift_nonzero {M : Matroid V} {C F : Finset V}
    (hC : M.IsCircuit (C : Set V)) {w : Chain V} (hw : TopCycle (M ／ (C : Set V)) w)
    (hn : signedJoin C (simplexBoundary C) w F ≠ 0) :
    M.IsBase (F : Set V) ∧ ∃ x ∈ C, F ∩ C = C.erase x := by
  exact ⟨by_contra fun hF => hn ((join_topCycle hC hw).vanishes _ hF),
    simplexBoundary_support.mp (left_ne_zero_of_mul (right_ne_zero_of_mul hn))⟩

/-- Distinct circuit lifts pair to zero when the union has nullity other than two. -/
theorem circuitPairing_eq_zero {M : Matroid V} {C D : Finset V}
    (hC : M.IsCircuit (C : Set V)) (hD : M.IsCircuit (D : Set V)) (hCD : C ≠ D)
    (h : ¬ UnionNullityTwo M C D)
    (w : topCycles (M ／ (C : Set V))) (v : topCycles (M ／ (D : Set V))) :
    circuitPairing C D w.val v.val = 0 := by
  apply sum_eq_zero
  intro F _
  by_contra hn
  obtain ⟨hF, x, hx, hFC⟩ := lift_nonzero hC w.prop (left_ne_zero_of_mul hn)
  obtain ⟨_, y, hy, hFD⟩ := lift_nonzero hD v.prop (right_ne_zero_of_mul hn)
  obtain ⟨hxP, hyQ⟩ := missing_vertices_exclusive hC hD hCD hF hx hy hFC hFD
  exact h (unionBasis_of_shared hC hD hF hxP hyQ hFC hFD)

omit [Fintype V] in
private lemma shuffle_sq (A B : Finset V) : shuffleSign A B * shuffleSign A B = 1 :=
  sign_sq _

omit [Fintype V] in
private lemma shuffle_union_left {A B : Finset V} (h : Disjoint A B) (T : Finset V) :
    shuffleSign (A ∪ B) T = shuffleSign A T * shuffleSign B T := by
  rw [shuffleSign, sum_union h, pow_add]
  rfl

omit [Fintype V] in
private lemma shuffle_union_right (A : Finset V) {B T : Finset V} (h : Disjoint B T) :
    shuffleSign A (B ∪ T) = shuffleSign A B * shuffleSign A T := by
  have hfilter (a : V) : Disjoint (B.filter (· < a)) (T.filter (· < a)) :=
    h.mono (filter_subset _ _) (filter_subset _ _)
  simp only [shuffleSign, filter_union, card_union_of_disjoint (hfilter _),
    sum_add_distrib, pow_add]

omit [Fintype V] in
private lemma shuffle_swap {A B : Finset V} (h : Disjoint A B) :
    shuffleSign A B * shuffleSign B A = (-1) ^ (A.card * B.card) := by
  rw [shuffleSign, shuffleSign, ← pow_add]
  congr 1
  simp only [Finset.card_filter]
  rw [sum_comm (s := B) (t := A), ← sum_add_distrib]
  calc
    _ = ∑ a ∈ A, ∑ _b ∈ B, (1 : ℕ) := by
      apply sum_congr rfl
      intro a ha
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro b hb
      have hab : a ≠ b := fun he => disjoint_left.mp h ha (he.symm ▸ hb)
      rcases lt_or_gt_of_ne hab with hab | hba
      · simp [hab, not_lt_of_gt hab]
      · simp [hba, not_lt_of_gt hba]
    _ = _ := by simp

omit [Fintype V] in
private lemma partition_boundary_sign {C D : Finset V} {x : V} (hx : x ∈ C \ D) :
    insertionSign (C.erase x) x =
      shuffleSign (C ∩ D) (C \ D) *
        (shuffleSign (C ∩ D) ((C \ D).erase x) *
          (-1) ^ (C ∩ D).card * insertionSign ((C \ D).erase x) x) := by
  have hxD := (mem_sdiff.mp hx).2
  have hnot := notMem_erase x C
  have hS : C.erase x ∩ D = C ∩ D := by
    ext a
    simp only [mem_inter, mem_erase]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨fun he => hxD (he ▸ h.2), h.1⟩, h.2⟩⟩
  have hP : C.erase x \ D = (C \ D).erase x := by
    ext a
    simp only [mem_sdiff, mem_erase]
    tauto
  have hsign := right_insertion_sign (C.erase x) D hnot
  rw [hS, hP, insert_erase hx] at hsign
  rw [← hsign]
  calc
    _ = (shuffleSign (C ∩ D) (C \ D) * shuffleSign (C ∩ D) (C \ D)) *
        insertionSign (C.erase x) x := by rw [shuffle_sq, one_mul]
    _ = _ := by ring

private abbrev sharedFace (C D : Finset V) (x y : V) (T : Finset V) :=
  T ∪ twoErases C D x y

omit [Fintype V] in
private lemma sharedFace_parts {C D T : Finset V} {x y : V}
    (hx : x ∈ C \ D) (hy : y ∈ D \ C) (hT : Disjoint T (C ∪ D)) :
    sharedFace C D x y T ∩ C = C.erase x ∧
    sharedFace C D x y T ∩ D = D.erase y ∧
    sharedFace C D x y T \ C = T ∪ (D \ C).erase y ∧
    sharedFace C D x y T \ D = T ∪ (C \ D).erase x ∧
    sharedFace C D x y T \ (C ∪ D) = T := by
  simp only [mem_sdiff] at hx hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ext a <;>
    simp only [sharedFace, twoErases, mem_inter, mem_union, mem_sdiff, mem_erase]
  all_goals
    have hxa : a = x → a ∉ D := fun he => he.symm ▸ hx.2
    have hya : a = y → a ∉ C := fun he => he.symm ▸ hy.2
    have ht : a ∈ T → a ∉ C ∧ a ∉ D := fun ha =>
      ⟨fun hc => disjoint_left.mp hT ha (mem_union_left _ hc),
       fun hd => disjoint_left.mp hT ha (mem_union_right _ hd)⟩
    tauto

omit [Fintype V] in
private lemma split_erase {C D : Finset V} {x : V} (hx : x ∈ C \ D) :
    C.erase x = (C ∩ D) ∪ (C \ D).erase x := by
  ext a
  simp only [mem_erase, mem_union, mem_inter, mem_sdiff] at *
  have hxa : a = x → a ∉ D := fun he => he.symm ▸ hx.2
  tauto

/-- The common relative orientation of the two circuit lifts. -/
def pairSign (C D : Finset V) : ℤ :=
  shuffleSign (C ∩ D) (C \ D) * shuffleSign (C ∩ D) (D \ C) *
    (-1) ^ (((C \ D).card - 1) * ((D \ C).card - 1))

omit [Fintype V] in
private lemma sharedFace_sign {C D T : Finset V} {x y : V}
    (hx : x ∈ C \ D) (hy : y ∈ D \ C) (hT : Disjoint T (C ∪ D)) :
    (shuffleSign (C.erase x) (T ∪ (D \ C).erase y) * insertionSign (C.erase x) x) *
      (shuffleSign (D.erase y) (T ∪ (C \ D).erase x) * insertionSign (D.erase y) y) =
      pairSign C D * (restrictionSign (D \ C) y T * restrictionSign (C \ D) x T) := by
  let S := C ∩ D
  let A := (C \ D).erase x
  let B := (D \ C).erase y
  have hSA : Disjoint S A := by
    apply disjoint_left.mpr
    simp only [S, A, mem_inter, mem_sdiff, mem_erase]
    tauto
  have hSB : Disjoint S B := by
    apply disjoint_left.mpr
    simp only [S, B, mem_inter, mem_sdiff, mem_erase]
    tauto
  have hAB : Disjoint A B := by
    apply disjoint_left.mpr
    simp only [A, B, mem_sdiff, mem_erase]
    tauto
  have hTA : Disjoint T A := hT.mono_right ((erase_subset _ _).trans
    (sdiff_subset.trans subset_union_left))
  have hTB : Disjoint T B := hT.mono_right ((erase_subset _ _).trans
    (sdiff_subset.trans subset_union_right))
  rw [partition_boundary_sign hx, partition_boundary_sign hy, inter_comm D C]
  have hC : C.erase x = S ∪ A := split_erase hx
  have hD : D.erase y = S ∪ B := by simpa only [S, inter_comm D C] using split_erase hy
  have hsignC : shuffleSign (C.erase x) (T ∪ B) =
      shuffleSign S T * shuffleSign S B * (shuffleSign A T * shuffleSign A B) := by
    rw [hC, shuffle_union_left hSA, shuffle_union_right S hTB, shuffle_union_right A hTB]
  have hsignD : shuffleSign (D.erase y) (T ∪ A) =
      shuffleSign S T * shuffleSign S A * (shuffleSign B T * shuffleSign B A) := by
    rw [hD, shuffle_union_left hSB, shuffle_union_right S hTA, shuffle_union_right B hTA]
  rw [hsignC, hsignD]
  change _ = pairSign C D *
    ((insertionSign B y * shuffleSign B T) * (insertionSign A x * shuffleSign A T))
  calc
    _ = ((shuffleSign S T * shuffleSign S T) *
          (shuffleSign S A * shuffleSign S A) *
          (shuffleSign S B * shuffleSign S B) *
          ((-1 : ℤ) ^ S.card * (-1) ^ S.card)) *
        ((shuffleSign A B * shuffleSign B A) *
          (shuffleSign S (C \ D) * shuffleSign S (D \ C)) *
          ((insertionSign B y * shuffleSign B T) *
            (insertionSign A x * shuffleSign A T))) := by ring
    _ = _ := by
      rw [shuffle_sq, shuffle_sq, shuffle_sq, sign_sq, shuffle_swap hAB]
      simp only [one_mul]
      have ha : A.card = (C \ D).card - 1 := card_erase_of_mem hx
      have hb : B.card = (D \ C).card - 1 := card_erase_of_mem hy
      rw [ha, hb, pairSign]
      ring

/-- The sum of signed restrictions over the deleted vertices of a circuit. -/
noncomputable def aggregateRestriction (M : Matroid V) (K : Finset V) (z : Chain V) :
    Chain V := fun T => ∑ x ∈ K, restrictChain M K x z T

omit [Fintype V] in
private lemma residual_contract (M : Matroid V) (C D : Finset V) :
    M ／ (C : Set V) ／ (↑(D \ C) : Set V) = M ／ (↑(C ∪ D) : Set V) := by
  rw [Matroid.contract_contract, coe_sdiff, coe_union]
  congr 1
  ext a
  simp only [Set.mem_sdiff, Set.mem_union]
  tauto

omit [Fintype V] in
private lemma sharedFace_weight {M : Matroid V} {C D T : Finset V} {x y : V}
    (hx : x ∈ C \ D) (hy : y ∈ D \ C) (hT : (M ／ (↑(C ∪ D) : Set V)).IsBase (T : Set V))
    (w v : Chain V) :
    signedJoin C (simplexBoundary C) w (sharedFace C D x y T) *
        signedJoin D (simplexBoundary D) v (sharedFace C D x y T) =
      pairSign C D *
        (restrictChain (M ／ (C : Set V)) (D \ C) y w T *
          restrictChain (M ／ (D : Set V)) (C \ D) x v T) := by
  classical
  have hd := contract_base_disjoint hT
  obtain ⟨hC, hD, hcompC, hcompD, _⟩ := sharedFace_parts hx hy hd
  have hTC := (residual_contract M C D).symm ▸ hT
  have hTD := (residual_contract M D C).symm ▸ (union_comm C D ▸ hT)
  rw [signedJoin, signedJoin, hC, hD, hcompC, hcompD,
    simplexBoundary_erase (mem_sdiff.mp hx).1, simplexBoundary_erase (mem_sdiff.mp hy).1,
    restrictChain, restrictChain, ite_eq_left hTC, ite_eq_left hTD]
  generalize w (T ∪ (D \ C).erase y) = a
  generalize v (T ∪ (C \ D).erase x) = b
  calc
    _ = ((shuffleSign (C.erase x) (T ∪ (D \ C).erase y) * insertionSign (C.erase x) x) *
        (shuffleSign (D.erase y) (T ∪ (C \ D).erase x) * insertionSign (D.erase y) y)) *
        (a * b) := by ring
    _ = _ := by rw [sharedFace_sign hx hy hd]; ring

/-- At nullity two the integral cross pairing factors through the contraction of the union. -/
theorem circuitPairing_factor {M : Matroid V} {C D : Finset V}
    (hC : M.IsCircuit (C : Set V)) (hD : M.IsCircuit (D : Set V))
    (h : UnionNullityTwo M C D)
    (w : topCycles (M ／ (C : Set V))) (v : topCycles (M ／ (D : Set V))) :
    circuitPairing C D w.val v.val =
      pairSign C D * ∑ T : Finset V,
        aggregateRestriction (M ／ (C : Set V)) (D \ C) w.val T *
          aggregateRestriction (M ／ (D : Set V)) (C \ D) v.val T := by
  classical
  have hCD := circuits_ne_of_union_nullity_two hC h
  let bases := (univ : Finset (Finset V)).filter
    (fun (T : Finset V) => (M ／ (↑(C ∪ D) : Set V)).IsBase (T : Set V))
  let shared := (univ : Finset (Finset V)).filter (fun (F : Finset V) =>
    M.IsBase (F : Set V) ∧
      ∃ x ∈ C \ D, ∃ y ∈ D \ C, F ∩ C = C.erase x ∧ F ∩ D = D.erase y)
  let weight := fun F =>
    signedJoin C (simplexBoundary C) w.val F * signedJoin D (simplexBoundary D) v.val F
  have hsum : circuitPairing C D w.val v.val = ∑ F ∈ shared, weight F := by
    symm
    apply sum_subset (subset_univ _)
    intro F _ hn
    by_contra hw
    obtain ⟨hF, x, hx, hFC⟩ := lift_nonzero hC w.prop (left_ne_zero_of_mul hw)
    obtain ⟨_, y, hy, hFD⟩ := lift_nonzero hD v.prop (right_ne_zero_of_mul hw)
    obtain ⟨hxP, hyQ⟩ := missing_vertices_exclusive hC hD hCD hF hx hy hFC hFD
    exact hn (mem_filter.mpr ⟨mem_univ _, hF, x, hxP, y, hyQ, hFC, hFD⟩)
  have hbase {T : Finset V} (hT : T ∈ bases) :
      (M ／ (↑(C ∪ D) : Set V)).IsBase (T : Set V) := (mem_filter.mp hT).2
  calc
    _ = ∑ F ∈ shared, weight F := hsum
    _ = ∑ t ∈ bases ×ˢ ((C \ D) ×ˢ (D \ C)),
        weight (sharedFace C D t.2.1 t.2.2 t.1) := by
      symm
      apply sum_bij (fun t _ => sharedFace C D t.2.1 t.2.2 t.1)
      · rintro ⟨T, x, y⟩ ht
        obtain ⟨hT, hx, hy⟩ := by simpa only [mem_product] using ht
        have hb := hbase hT
        have hd := contract_base_disjoint hb
        obtain ⟨hFC, hFD, _⟩ := sharedFace_parts hx hy hd
        have hF := (contract_base_iff (twoErases_basis hC hD hx hy h) hd).mp hb
        exact mem_filter.mpr ⟨mem_univ _, hF, x, hx, y, hy, hFC, hFD⟩
      · rintro ⟨T, x, y⟩ ht ⟨T', x', y'⟩ ht' he
        obtain ⟨hT, hx, hy⟩ := by simpa only [mem_product] using ht
        obtain ⟨hT', hx', hy'⟩ := by simpa only [mem_product] using ht'
        obtain ⟨hFC, hFD, _, _, hFT⟩ :=
          sharedFace_parts hx hy (contract_base_disjoint (hbase hT))
        obtain ⟨hFC', hFD', _, _, hFT'⟩ :=
          sharedFace_parts hx' hy' (contract_base_disjoint (hbase hT'))
        exact Prod.ext (hFT.symm.trans (he ▸ hFT')) (Prod.ext
          ((erase_inj C (mem_sdiff.mp hx).1).mp (hFC.symm.trans (he ▸ hFC')))
          ((erase_inj D (mem_sdiff.mp hy).1).mp (hFD.symm.trans (he ▸ hFD'))))
      · intro F hF
        obtain ⟨hb, x, hx, y, hy, hFC, hFD⟩ := (mem_filter.mp hF).2
        have hpart : F ∩ (C ∪ D) = twoErases C D x y := by
          rw [inter_union_distrib_left, hFC, hFD]
        have hface : sharedFace C D x y (F \ (C ∪ D)) = F := by
          change F \ (C ∪ D) ∪ twoErases C D x y = F
          rw [← hpart, sdiff_union_inter]
        have hT := (contract_base_iff (twoErases_basis hC hD hx hy h)
          disjoint_sdiff.symm).mpr (hface.symm ▸ hb)
        exact ⟨(F \ (C ∪ D), x, y), mem_product.mpr
          ⟨mem_filter.mpr ⟨mem_univ _, hT⟩, mem_product.mpr ⟨hx, hy⟩⟩, hface⟩
      · intros
        rfl
    _ = pairSign C D * ∑ T ∈ bases,
        aggregateRestriction (M ／ (C : Set V)) (D \ C) w.val T *
          aggregateRestriction (M ／ (D : Set V)) (C \ D) v.val T := by
      rw [sum_product, mul_sum]
      apply sum_congr rfl
      intro T hT
      rw [sum_product, aggregateRestriction, aggregateRestriction, mul_comm
          (∑ y ∈ D \ C, restrictChain (M ／ (C : Set V)) (D \ C) y w.val T),
        sum_mul, mul_sum]
      apply sum_congr rfl
      intro x hx
      rw [mul_sum, mul_sum]
      apply sum_congr rfl
      intro y hy
      rw [mul_comm (restrictChain (M ／ (D : Set V)) (C \ D) x v.val T)]
      exact sharedFace_weight hx hy (hbase hT) w.val v.val
    _ = _ := by
      congr 1
      apply sum_subset (subset_univ _)
      intro T _ hT
      have hn : ¬ (M ／ (C : Set V) ／ (↑(D \ C) : Set V)).IsBase (T : Set V) := by
        rw [residual_contract]
        exact fun hB => hT (mem_filter.mpr ⟨mem_univ _, hB⟩)
      simp only [aggregateRestriction, restrictChain, ite_eq_right hn, sum_const_zero, zero_mul]

private lemma aggregateRestriction_topCycle {M : Matroid V} {K : Finset V}
    (hK : M.IsCircuit (K : Set V)) (z : topCycles M) :
    TopCycle (M ／ (K : Set V)) (aggregateRestriction M K z.val) := by
  classical
  have hrestr (x : V) (hx : x ∈ K) :
      restrictChain M K x z.val ∈ topCycles (M ／ (K : Set V)) := by
    obtain ⟨E, hE, _⟩ := circuit_cycle_decomposition M x (hK.subset_ground hx)
    let C : CircuitThrough M x := ⟨K, hK, hx⟩
    have hchain : (E z C).val = restrictChain M K x z.val := by
      funext T
      exact hE z C T
    exact hchain ▸ (E z C).prop
  have hsum := Submodule.sum_mem (topCycles (M ／ (K : Set V))) fun x hx => hrestr x hx
  have heq : (∑ x ∈ K, restrictChain M K x z.val) = aggregateRestriction M K z.val := by
    funext T
    exact sum_apply T K (fun x => restrictChain M K x z.val)
  exact heq ▸ hsum

private lemma aggregateRestriction_join {M : Matroid V} {K : Finset V}
    (w : topCycles (M ／ (K : Set V))) (T : Finset V) :
    aggregateRestriction M K (signedJoin K (simplexBoundary K) w.val) T =
      (K.card : ℤ) * w.val T := by
  classical
  by_cases hT : (M ／ (K : Set V)).IsBase (T : Set V)
  · rw [aggregateRestriction]
    calc
      _ = ∑ _x ∈ K, w.val T := by
        apply sum_congr rfl
        intro x hx
        obtain ⟨hpart, hdiff⟩ := split_circuit_face (contract_base_disjoint hT) x
        rw [restrictChain, ite_eq_left hT, signedJoin, hpart, hdiff, simplexBoundary_erase hx]
        calc
          _ = (restrictionSign K x T * restrictionSign K x T) * w.val T := by
            unfold restrictionSign
            ring
          _ = _ := by rw [restrictionSign_sq, one_mul]
      _ = _ := by simp
  · rw [w.prop.vanishes _ hT, mul_zero]
    simp only [aggregateRestriction, restrictChain, ite_eq_right hT, sum_const_zero]

/-- Rational augmented top cycles in the same ambient face coordinates. -/
def rationalTopCycles (M : Matroid V) : Submodule ℚ (Finset V → ℚ) where
  carrier := {z |
    (∀ F : Finset V, ¬ M.IsBase (F : Set V) → z F = 0) ∧
      ∀ R : Finset V, (∑ x ∈ univ \ R, (insertionSign R x : ℚ) * z (insert x R)) = 0}
  zero_mem' := ⟨fun _ _ => rfl, fun _ => by simp⟩
  add_mem' := by
    rintro z w ⟨hzB, hzR⟩ ⟨hwB, hwR⟩
    refine ⟨fun F hF => by simp [hzB F hF, hwB F hF], fun R => ?_⟩
    simp only [Pi.add_apply, mul_add, sum_add_distrib, hzR R, hwR R, zero_add]
  smul_mem' := by
    rintro c z ⟨hzB, hzR⟩
    refine ⟨fun F hF => by simp [hzB F hF], fun R => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← mul_sum, hzR R, mul_zero]

private def castChain (z : Chain V) (F : Finset V) : ℚ := z F

private lemma mem_rationalTopCycles_iff {M : Matroid V} {z : Chain V} :
    castChain z ∈ rationalTopCycles M ↔ TopCycle M z := by
  change ( (∀ F : Finset V, ¬ M.IsBase (F : Set V) → (z F : ℚ) = 0) ∧
    ∀ R : Finset V, (∑ x ∈ univ \ R, (insertionSign R x : ℚ) * (z (insert x R) : ℚ)) = 0) ↔ _
  constructor
  · rintro ⟨hB, hR⟩
    exact ⟨fun F hF => by exact_mod_cast hB F hF, fun R => by
      unfold boundaryOn
      exact_mod_cast hR R⟩
  · intro h
    exact ⟨fun F hF => by exact_mod_cast h.vanishes F hF, fun R => by
      exact_mod_cast h.cycle R⟩

private lemma exists_integral_multiple {M : Matroid V} (z : rationalTopCycles M) :
    ∃ (c : ℚ) (w : topCycles M), c ≠ 0 ∧ castChain w.val = c • z.val := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) z.val
  choose w hw using hd
  have hd0 : (d : ℤ) ≠ 0 := nonZeroDivisors.ne_zero d.property
  have hcast : castChain w = ((d : ℤ) : ℚ) • z.val := by
    funext F
    simpa [castChain, Algebra.smul_def] using hw F
  exact ⟨(d : ℤ), ⟨w, mem_rationalTopCycles_iff.mp
    (hcast.symm ▸ (rationalTopCycles M).smul_mem ((d : ℤ) : ℚ) z.prop)⟩,
    by exact_mod_cast hd0, hcast⟩

/-- The oriented circuit lift on rational coordinate chains. -/
def rationalLift (K : Finset V) : (Finset V → ℚ) →ₗ[ℚ] (Finset V → ℚ) where
  toFun z F := (shuffleSign (F ∩ K) (F \ K) * simplexBoundary K (F ∩ K) : ℤ) * z (F \ K)
  map_add' z w := by funext F; exact mul_add _ _ _
  map_smul' c z := by funext F; exact mul_left_comm _ _ _

omit [Fintype V] in
private lemma rationalLift_cast (K : Finset V) (z : Chain V) :
    rationalLift K (castChain z) = castChain (signedJoin K (simplexBoundary K) z) := by
  funext F
  simp only [rationalLift, LinearMap.coe_mk, AddHom.coe_mk, castChain, signedJoin, Int.cast_mul,
    mul_assoc]

private lemma rationalLift_mem {M : Matroid V} {K : Finset V} (hK : M.IsCircuit (K : Set V))
    (z : rationalTopCycles (M ／ (K : Set V))) :
    rationalLift K z.val ∈ rationalTopCycles M := by
  obtain ⟨c, w, hc, hw⟩ := exists_integral_multiple z
  have hlift := congrArg (rationalLift K) hw
  rw [rationalLift_cast, map_smul] at hlift
  have hz := mem_rationalTopCycles_iff.mpr (join_topCycle hK w.prop)
  have hscaled : c • rationalLift K z.val ∈ rationalTopCycles M := hlift ▸ hz
  have h := (rationalTopCycles M).smul_mem c⁻¹ hscaled
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h

open scoped Classical in
private noncomputable def rationalAggregate (M : Matroid V) (K : Finset V) :
    (Finset V → ℚ) →ₗ[ℚ] (Finset V → ℚ) where
  toFun z T := if (M ／ (K : Set V)).IsBase (T : Set V) then
    ∑ x ∈ K, (restrictionSign K x T : ℚ) * z (T ∪ K.erase x)
    else 0
  map_add' z w := by
    funext T
    by_cases hT : (M ／ (K : Set V)).IsBase (T : Set V)
    · simp only [ite_eq_left hT, Pi.add_apply, mul_add, sum_add_distrib]
    · simp only [ite_eq_right hT, Pi.add_apply, zero_add]
  map_smul' c z := by
    funext T
    by_cases hT : (M ／ (K : Set V)).IsBase (T : Set V)
    · simp only [ite_eq_left hT, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← mul_sum,
        RingHom.id_apply]
    · simp only [ite_eq_right hT, Pi.smul_apply, smul_zero]

omit [Fintype V] in
private lemma rationalAggregate_cast (M : Matroid V) (K : Finset V) (z : Chain V) :
    rationalAggregate M K (castChain z) = castChain (aggregateRestriction M K z) := by
  classical
  funext T
  by_cases hT : (M ／ (K : Set V)).IsBase (T : Set V)
  · simp only [rationalAggregate, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left hT, castChain,
      aggregateRestriction, restrictChain, Int.cast_sum, Int.cast_mul]
  · simp only [rationalAggregate, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_right hT, castChain,
      aggregateRestriction, restrictChain, sum_const_zero, Int.cast_zero]

private lemma rationalAggregate_mem {M : Matroid V} {K : Finset V}
    (hK : M.IsCircuit (K : Set V)) (z : rationalTopCycles M) :
    rationalAggregate M K z.val ∈ rationalTopCycles (M ／ (K : Set V)) := by
  obtain ⟨c, w, hc, hw⟩ := exists_integral_multiple z
  have hagg := congrArg (rationalAggregate M K) hw
  rw [rationalAggregate_cast, map_smul] at hagg
  have hz := mem_rationalTopCycles_iff.mpr (aggregateRestriction_topCycle hK w)
  have hscaled :
      c • rationalAggregate M K z.val ∈ rationalTopCycles (M ／ (K : Set V)) := hagg ▸ hz
  have h := (rationalTopCycles (M ／ (K : Set V))).smul_mem c⁻¹ hscaled
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h

private lemma rationalAggregate_join {M : Matroid V} {K : Finset V}
    (z : rationalTopCycles (M ／ (K : Set V))) :
    rationalAggregate M K (rationalLift K z.val) = (K.card : ℚ) • z.val := by
  obtain ⟨c, w, hc, hw⟩ := exists_integral_multiple z
  have h := congrArg ((rationalAggregate M K).comp (rationalLift K)) hw
  rw [map_smul, LinearMap.comp_apply, LinearMap.comp_apply, rationalLift_cast,
    rationalAggregate_cast] at h
  have hscaled :
      castChain (aggregateRestriction M K (signedJoin K (simplexBoundary K) w.val)) =
        (K.card : ℚ) • castChain w.val := by
    funext T
    change ((aggregateRestriction M K (signedJoin K (simplexBoundary K) w.val) T : ℤ) : ℚ) =
      (K.card : ℚ) * (w.val T : ℚ)
    rw [aggregateRestriction_join]
    push_cast
    rfl
  rw [hscaled, hw, smul_comm] at h
  exact (smul_right_injective _ hc) h.symm

private noncomputable def rationalRestrictionMap {M : Matroid V} {K : Finset V}
    (hK : M.IsCircuit (K : Set V)) :
    rationalTopCycles M →ₗ[ℚ] rationalTopCycles (M ／ (K : Set V)) :=
  ((rationalAggregate M K).comp (rationalTopCycles M).subtype).codRestrict _
    (rationalAggregate_mem hK)

private lemma rationalRestrictionMap_surjective {M : Matroid V} {K : Finset V}
    (hK : M.IsCircuit (K : Set V)) : Function.Surjective (rationalRestrictionMap hK) := by
  intro z
  have hcard : (K.card : ℚ) ≠ 0 := by
    exact_mod_cast (card_ne_zero.mpr (show K.Nonempty from hK.nonempty))
  let w : rationalTopCycles M := ⟨rationalLift K z.val, rationalLift_mem hK z⟩
  refine ⟨(K.card : ℚ)⁻¹ • w, Subtype.ext ?_⟩
  rw [map_smul]
  change (K.card : ℚ)⁻¹ • rationalAggregate M K (rationalLift K z.val) = z.val
  rw [rationalAggregate_join z, smul_smul, inv_mul_cancel₀ hcard, one_smul]

private def rationalDot : (Finset V → ℚ) →ₗ[ℚ] (Finset V → ℚ) →ₗ[ℚ] ℚ :=
  dotProductBilin ℚ ℚ

/-- The rational bilinear pairing of the two oriented circuit lifts. -/
def rationalCircuitPairing (M : Matroid V) (C D : Finset V) :
    rationalTopCycles (M ／ (C : Set V)) →ₗ[ℚ]
      rationalTopCycles (M ／ (D : Set V)) →ₗ[ℚ] ℚ :=
  (dotProductBilin ℚ ℚ).compl₁₂
    ((rationalLift C).comp (rationalTopCycles (M ／ (C : Set V))).subtype)
    ((rationalLift D).comp (rationalTopCycles (M ／ (D : Set V))).subtype)

private lemma rationalPairing_factor {M : Matroid V} {C D : Finset V}
    (hC : M.IsCircuit (C : Set V)) (hD : M.IsCircuit (D : Set V))
    (h : UnionNullityTwo M C D)
    (w : rationalTopCycles (M ／ (C : Set V))) (v : rationalTopCycles (M ／ (D : Set V))) :
    rationalCircuitPairing M C D w v =
      (pairSign C D : ℚ) * dotProduct
        (rationalAggregate (M ／ (C : Set V)) (D \ C) w.val)
        (rationalAggregate (M ／ (D : Set V)) (C \ D) v.val) := by
  obtain ⟨c, a, hc, ha⟩ := exists_integral_multiple w
  obtain ⟨d, b, hd, hb⟩ := exists_integral_multiple v
  have hint :
      dotProduct (castChain (signedJoin C (simplexBoundary C) a.val))
          (castChain (signedJoin D (simplexBoundary D) b.val)) =
        (pairSign C D : ℚ) * dotProduct
          (castChain (aggregateRestriction (M ／ (C : Set V)) (D \ C) a.val))
          (castChain (aggregateRestriction (M ／ (D : Set V)) (C \ D) b.val)) := by
    simpa only [dotProduct, castChain, ← Int.cast_mul, ← Int.cast_sum, circuitPairing] using
      congrArg (fun n : ℤ => (n : ℚ)) (circuitPairing_factor hC hD h a b)
  rw [← rationalLift_cast, ← rationalLift_cast, ← rationalAggregate_cast, ← rationalAggregate_cast,
    ha, hb, map_smul, map_smul, map_smul, map_smul] at hint
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul] at hint
  change dotProduct (rationalLift C w.val) (rationalLift D v.val) = _
  apply mul_left_cancel₀ (mul_ne_zero hc hd)
  calc
    _ = d * (c * dotProduct (rationalLift C w.val) (rationalLift D v.val)) := by ring
    _ = _ := by rw [hint]; ring

omit [Fintype V] in
private lemma pairSign_isUnit (C D : Finset V) : IsUnit (pairSign C D) := by
  unfold pairSign shuffleSign
  have h : IsUnit (-1 : ℤ) := isUnit_neg_one
  exact ((h.pow _).mul (h.pow _)).mul (h.pow _)

private noncomputable def unionRestrictionMap {M : Matroid V} {C D : Finset V}
    (hQ : (M ／ (C : Set V)).IsCircuit (↑(D \ C) : Set V)) :
    rationalTopCycles (M ／ (C : Set V)) →ₗ[ℚ] rationalTopCycles (M ／ (↑(C ∪ D) : Set V)) :=
  (LinearEquiv.ofEq _ _ (congrArg rationalTopCycles (residual_contract M C D))).toLinearMap.comp
    (rationalRestrictionMap hQ)

private lemma unionRestrictionMap_surjective {M : Matroid V} {C D : Finset V}
    (hQ : (M ／ (C : Set V)).IsCircuit (↑(D \ C) : Set V)) :
    Function.Surjective (unionRestrictionMap hQ) :=
  (LinearEquiv.ofEq _ _ (congrArg rationalTopCycles (residual_contract M C D))).surjective.comp
    (rationalRestrictionMap_surjective hQ)

/-- The rank of the rational circuit cross pairing is the top-cycle dimension after
contracting the union. -/
theorem circuitPairing_rank {M : Matroid V} {C D : Finset V}
    (hC : M.IsCircuit (C : Set V)) (hD : M.IsCircuit (D : Set V))
    (h : UnionNullityTwo M C D) :
    Module.finrank ℚ (LinearMap.range (rationalCircuitPairing M C D)) =
      Module.finrank ℚ (rationalTopCycles (M ／ (↑(C ∪ D) : Set V))) := by
  obtain ⟨hQ, hP⟩ := residual_circuits hC hD h
  let U := rationalTopCycles (M ／ (↑(C ∪ D) : Set V))
  let A : rationalTopCycles (M ／ (C : Set V)) →ₗ[ℚ] U :=
    unionRestrictionMap hQ
  let e : rationalTopCycles (M ／ (↑(D ∪ C) : Set V)) ≃ₗ[ℚ] U :=
    LinearEquiv.ofEq _ _ (by rw [union_comm D C])
  let B : rationalTopCycles (M ／ (D : Set V)) →ₗ[ℚ] U :=
    e.toLinearMap.comp (unionRestrictionMap hP)
  have hA : Function.Surjective A := unionRestrictionMap_surjective hQ
  have hB : Function.Surjective B := e.surjective.comp (unionRestrictionMap_surjective hP)
  let G : U →ₗ[ℚ] rationalTopCycles (M ／ (D : Set V)) →ₗ[ℚ] ℚ :=
    (pairSign C D : ℚ) • rationalDot.compl₁₂ U.subtype (U.subtype.comp B)
  have hcomp : rationalCircuitPairing M C D = G.comp A := by
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro v
    exact rationalPairing_factor hC hD h w v
  have hinj : Function.Injective G := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    obtain ⟨v, hv⟩ := hB z
    have hzero := DFunLike.congr_fun hz v
    change (pairSign C D : ℚ) * dotProduct z.val (B v).val = 0 at hzero
    rw [hv] at hzero
    have hsign : (pairSign C D : ℚ) ≠ 0 := by exact_mod_cast (pairSign_isUnit C D).ne_zero
    exact Subtype.ext (dotProduct_self_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hsign))
  rw [hcomp, LinearMap.range_comp_of_range_eq_top G (LinearMap.range_eq_top.mpr hA),
    LinearMap.finrank_range_of_inj hinj]

end D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct
