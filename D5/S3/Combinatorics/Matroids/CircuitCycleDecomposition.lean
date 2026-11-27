/- GID: D5/S3/Combinatorics/Matroids/CircuitCycleDecomposition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/CircuitCycleDecomposition
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Integral circuit decomposition of augmented matroid top cycles. -/

module

public import D5.S3.Combinatorics.Matroids.OrderedCycleFactorization
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! Signed restriction to circuit contractions and reconstruction by oriented joins. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped Matroid

namespace D5.S3.Combinatorics.Matroids.CircuitCycleDecomposition

open OrderedCycleFactorization
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Integral augmented chains supported on bases and killed by the boundary. -/
def topCycles (M : Matroid V) : Submodule ℤ (Chain V) where
  carrier := {z | TopCycle M z}
  zero_mem' := ⟨fun _ _ => rfl, fun R => by simp [boundaryOn]⟩
  add_mem' := by
    intro z w hz hw
    refine ⟨fun F hF => by simp [hz.vanishes F hF, hw.vanishes F hF], fun R => ?_⟩
    simp only [boundaryOn, Pi.add_apply, mul_add, sum_add_distrib]
    change boundaryOn univ z R + boundaryOn univ w R = 0
    rw [hz.cycle, hw.cycle, add_zero]
  smul_mem' := by
    intro n z hz
    refine ⟨fun F hF => by simp [hz.vanishes F hF], fun R => ?_⟩
    change (∑ x ∈ univ \ R, insertionSign R x * (n * z (insert x R))) = 0
    simp only [mul_left_comm _ n, ← mul_sum]
    change n * boundaryOn univ z R = 0
    rw [hz.cycle, mul_zero]

/-- A circuit whose vertex set contains the distinguished element. -/
abbrev CircuitThrough (M : Matroid V) (e : V) :=
  {C : Finset V // M.IsCircuit (C : Set V) ∧ e ∈ C}

omit [Fintype V] in
def restrictionSign (C : Finset V) (e : V) (T : Finset V) : ℤ :=
  insertionSign (C.erase e) e * shuffleSign (C.erase e) T

omit [Fintype V] in
lemma restrictionSign_sq (C : Finset V) (e : V) (T : Finset V) :
    restrictionSign C e T * restrictionSign C e T = 1 := by
  unfold restrictionSign insertionSign shuffleSign
  rw [← pow_add, sign_sq]

open scoped Classical in
omit [Fintype V] in
noncomputable def restrictChain (M : Matroid V) (C : Finset V) (e : V) (z : Chain V) :
    Chain V := fun T =>
  if (M ／ (C : Set V)).IsBase (T : Set V) then
    restrictionSign C e T * z (T ∪ C.erase e)
  else 0

/-- Signed boundary transport at every ridge disjoint from the circuit. -/
private lemma boundary_restrictChain {M : Matroid V} {C : Finset V} {e : V}
    (hC : M.IsCircuit (C : Set V)) (heC : e ∈ C) {z : Chain V}
    (hz : ∀ F : Finset V, ¬ M.IsBase (F : Set V) → z F = 0)
    {S : Finset V} (hS : Disjoint S C) :
    boundaryOn univ (restrictChain M C e z) S =
      (restrictionSign C e S * (-1) ^ (C.erase e).card) *
        boundaryOn univ z (S ∪ C.erase e) := by
  let A := C.erase e
  let R := S ∪ A
  let U := (univ \ C) \ S
  have hR := split_circuit_face hS e
  have hsubset : U ⊆ univ \ R := by
    intro x hx
    have hxC := (mem_sdiff.mp (mem_sdiff.mp hx).1).2
    have hxS := (mem_sdiff.mp hx).2
    exact mem_sdiff.mpr ⟨mem_univ _, fun hm => (mem_union.mp hm).elim hxS
      (fun ha => hxC (mem_of_mem_erase ha))⟩
  have hleft : boundaryOn univ (restrictChain M C e z) S =
      ∑ x ∈ U, insertionSign S x * restrictChain M C e z (insert x S) := by
    symm
    apply sum_subset
    · exact fun x hx => mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hx).2⟩
    · intro x hx hxU
      have hxC : x ∈ C := by simpa [U, (mem_sdiff.mp hx).2] using hxU
      have hbase : ¬ (M ／ (C : Set V)).IsBase (↑(insert x S) : Set V) :=
        fun h => disjoint_left.mp (contract_base_disjoint h) (mem_insert_self _ _) hxC
      rw [restrictChain, ite_eq_right hbase, mul_zero]
  have hright : boundaryOn univ z R = ∑ x ∈ U, insertionSign R x * z (insert x R) := by
    symm
    apply sum_subset hsubset
    intro x hx hxU
    have hxR := (mem_sdiff.mp hx).2
    have hxS : x ∉ S := fun h => hxR (mem_union_left _ h)
    have hxC : x ∈ C := by simpa [U, hxS] using hxU
    have hxe : x = e := by
      by_contra hne
      exact hxR (mem_union_right _ (mem_erase.mpr ⟨hne, hxC⟩))
    subst x
    have hbase : ¬ M.IsBase (↑(insert e R) : Set V) := by
      intro hB
      apply hC.not_indep
      apply hB.indep.subset
      have h : C ⊆ insert e R := by
        rw [← insert_erase heC]
        exact insert_subset_insert e (subset_union_right (s₁ := S))
      exact_mod_cast h
    rw [hz _ hbase, mul_zero]
  change _ = (restrictionSign C e S * (-1) ^ A.card) * boundaryOn univ z R
  rw [hleft, hright, mul_sum]
  apply sum_congr rfl
  intro x hx
  have hxC := (mem_sdiff.mp (mem_sdiff.mp hx).1).2
  have hxR := (mem_sdiff.mp (hsubset hx)).2
  have hdis : Disjoint (insert x S) C := disjoint_left.mpr fun y hy hyC =>
    (mem_insert.mp hy).elim (fun h => hxC (h ▸ hyC))
      (fun hyS => disjoint_left.mp hS hyS hyC)
  have hsign := right_insertion_sign R C hxR
  have hRA : R ∩ C = A := hR.1
  have hRS : R \ C = S := hR.2
  rw [hRA, hRS] at hsign
  have hsqS : insertionSign S x * insertionSign S x = 1 := sign_sq _
  have hsqR : insertionSign R x * insertionSign R x = 1 := sign_sq _
  have htransport :
      insertionSign S x * shuffleSign A (insert x S) =
        shuffleSign A S * (-1) ^ A.card * insertionSign R x := by
    calc
      _ = (insertionSign R x * insertionSign R x) *
          (insertionSign S x * shuffleSign A (insert x S)) := by rw [hsqR, one_mul]
      _ = (insertionSign R x * shuffleSign A (insert x S)) *
          (insertionSign R x * insertionSign S x) := by ring
      _ = (insertionSign S x * insertionSign S x) *
          (shuffleSign A S * (-1) ^ A.card * insertionSign R x) := by rw [hsign]; ring
      _ = _ := by rw [hsqS, one_mul]
  have hbase := contract_base_iff (circuit_erase_basis hC heC) hdis
  have hinsert : insert x S ∪ C.erase e = insert x R := insert_union _ _ _
  by_cases hb : (M ／ (C : Set V)).IsBase (↑(insert x S) : Set V)
  · rw [restrictChain, ite_eq_left hb, hinsert, restrictionSign, restrictionSign]
    calc
      _ = insertionSign A e * (insertionSign S x * shuffleSign A (insert x S)) *
          z (insert x R) := by ring
      _ = _ := by rw [htransport]; ring
  · have hb' : ¬ M.IsBase (↑(insert x R) : Set V) :=
      fun h => hb (hbase.mpr (hinsert.symm ▸ h))
    rw [restrictChain, ite_eq_right hb, hz _ hb', mul_zero, mul_zero, mul_zero]

private lemma restrictChain_topCycle {M : Matroid V} {C : Finset V} {e : V}
    (hC : M.IsCircuit (C : Set V)) (heC : e ∈ C) {z : Chain V} (hz : TopCycle M z) :
    TopCycle (M ／ (C : Set V)) (restrictChain M C e z) := by
  refine ⟨fun T hT => by rw [restrictChain, ite_eq_right hT], fun S => ?_⟩
  by_cases hS : Disjoint S C
  · rw [boundary_restrictChain hC heC hz.vanishes hS, hz.cycle, mul_zero]
  · apply sum_eq_zero
    intro x _
    have h : ¬ (M ／ (C : Set V)).IsBase (↑(insert x S) : Set V) :=
      fun hB => hS ((contract_base_disjoint hB).mono_left (subset_insert x S))
    rw [restrictChain, ite_eq_right h, mul_zero]

lemma join_topCycle {M : Matroid V} {C : Finset V} (hC : M.IsCircuit (C : Set V))
    {w : Chain V} (hw : TopCycle (M ／ (C : Set V)) w) :
    TopCycle M (signedJoin C (simplexBoundary C) w) := by
  refine ⟨fun F hF => ?_, fun R => ?_⟩
  · by_contra hn
    have hp := right_ne_zero_of_mul hn
    obtain ⟨x, hx, hA⟩ := simplexBoundary_support.mp (left_ne_zero_of_mul hp)
    have hT : (M ／ (C : Set V)).IsBase (↑(F \ C) : Set V) := by
      by_contra h
      exact right_ne_zero_of_mul hp (hw.vanishes _ h)
    have hunion : F \ C ∪ C.erase x = F := by rw [← hA, sdiff_union_inter]
    exact hF (hunion ▸ (contract_base_iff (circuit_erase_basis hC hx) disjoint_sdiff.symm).mp hT)
  · rw [boundaryOn_signedJoin, boundaryOn_complement hw, simplexBoundary, boundaryOn_squared]
    simp

private noncomputable def restrict (M : Matroid V) (e : V) (z : topCycles M)
    (C : CircuitThrough M e) : topCycles (M ／ (C.val : Set V)) :=
  ⟨restrictChain M C.val e z.val, restrictChain_topCycle C.prop.1 C.prop.2 z.prop⟩

open scoped Classical in
private noncomputable def reconstruct (M : Matroid V) (e : V)
    (w : (C : CircuitThrough M e) → topCycles (M ／ (C.val : Set V))) : topCycles M :=
  ∑ C : CircuitThrough M e,
    ⟨signedJoin C.val (simplexBoundary C.val) (w C).val, join_topCycle C.prop.1 (w C).prop⟩

open scoped Classical in
private lemma reconstruct_apply {M : Matroid V} {e : V}
    (w : (C : CircuitThrough M e) → topCycles (M ／ (C.val : Set V))) (F : Finset V) :
    (reconstruct M e w).val F =
      ∑ C : CircuitThrough M e, signedJoin C.val (simplexBoundary C.val) (w C).val F := by
  rw [reconstruct, Submodule.coe_sum]
  exact map_sum (Pi.evalAddMonoidHom (fun _ : Finset V => ℤ) F) _ _

lemma circuit_eq_circuitAt {M : Matroid V} {e : V}
    (C : CircuitThrough M e) {F : Finset V} (hF : M.IsBase (F : Set V))
    (hpart : F ∩ C.val = C.val.erase e) : C.val = circuitAt M F e := by
  apply coe_injective
  change (C.val : Set V) = ↑((M.fundCircuit e (F : Set V)).toFinite.toFinset)
  rw [Set.Finite.coe_toFinset]
  apply C.prop.1.eq_fundCircuit_of_subset hF.indep
  intro x hx
  by_cases hxe : x = e
  · exact Set.mem_insert_iff.mpr (Or.inl hxe)
  · exact Set.mem_insert_of_mem _
      (mem_inter.mp (hpart.symm ▸ mem_erase.mpr ⟨hxe, hx⟩)).1

private lemma circuitAt_of_base {M : Matroid V} {e : V} (he : e ∈ M.E)
    {F : Finset V} (hF : M.IsBase (F : Set V)) (heF : e ∉ F) :
    let C := circuitAt M F e
    M.IsCircuit (C : Set V) ∧ e ∈ C ∧ F ∩ C = C.erase e := by
  classical
  let C := circuitAt M F e
  have hC : (C : Set V) = M.fundCircuit e (F : Set V) := Set.Finite.coe_toFinset _
  refine ⟨by rw [hC]; exact hF.fundCircuit_isCircuit he heF, ?_, ?_⟩
  · change e ∈ (C : Set V)
    rw [hC]
    exact M.mem_fundCircuit _ _
  · apply coe_injective
    rw [coe_inter, coe_erase, hC, M.fundCircuit_sdiff_eq_inter heF, Set.inter_comm]

private lemma reconstruct_coord {M : Matroid V} {e : V}
    (w : (C : CircuitThrough M e) → topCycles (M ／ (C.val : Set V)))
    (C : CircuitThrough M e) {F : Finset V} (hF : M.IsBase (F : Set V))
    (hpart : F ∩ C.val = C.val.erase e) :
    (reconstruct M e w).val F = restrictionSign C.val e (F \ C.val) * (w C).val (F \ C.val) := by
  classical
  have heF : e ∉ F := fun h => notMem_erase e C.val (hpart ▸ mem_inter.mpr ⟨h, C.prop.2⟩)
  rw [reconstruct_apply, sum_eq_single C]
  · rw [signedJoin, hpart, simplexBoundary_erase C.prop.2, restrictionSign]
    ring
  · intro D _ hDC
    by_contra h
    obtain ⟨x, _, hpartD⟩ := simplexBoundary_support.mp
      (left_ne_zero_of_mul (right_ne_zero_of_mul h))
    have hxe : x = e := by
      by_contra hne
      exact heF (mem_inter.mp (hpartD.symm ▸ mem_erase.mpr ⟨Ne.symm hne, D.prop.2⟩)).1
    subst x
    exact hDC (Subtype.ext ((circuit_eq_circuitAt D hF hpartD).trans
      (circuit_eq_circuitAt C hF hpart).symm))
  · simp

/-- The boundary at a base with `e` removed recovers its coefficient. -/
private lemma eq_of_eq_away_from {M : Matroid V} {e : V} {z w : Chain V}
    (hz : TopCycle M z) (hw : TopCycle M w)
    (haway : ∀ F, e ∉ F → z F = w F) :
    z = w := by
  funext F
  by_cases heF : e ∈ F
  · let R := F.erase e
    have heR : e ∉ R := notMem_erase _ _
    have hs : ∑ x ∈ univ \ R, insertionSign R x * (z (insert x R) - w (insert x R)) = 0 := by
      calc
        _ = boundaryOn univ z R - boundaryOn univ w R := by
          simp only [boundaryOn, mul_sub, sum_sub_distrib]
        _ = _ := by rw [hz.cycle, hw.cycle, sub_zero]
    rw [sum_eq_single e] at hs
    · rw [insert_erase heF] at hs
      exact sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_left (insertionSign_ne_zero _ _))
    · intro x _ hxe
      rw [haway _ (by simp [Ne.symm hxe, heR]), sub_self, mul_zero]
    · exact fun hm => (hm (mem_sdiff.mpr ⟨mem_univ _, heR⟩)).elim
  · exact haway F heF

private lemma reconstruct_restrict {M : Matroid V} {e : V} (he : e ∈ M.E)
    (z : topCycles M) : reconstruct M e (restrict M e z) = z := by
  apply Subtype.ext
  apply eq_of_eq_away_from (e := e) (reconstruct M e (restrict M e z)).prop z.prop
  intro F heF
  by_cases hF : M.IsBase (F : Set V)
  · obtain ⟨hC, heC, hpart⟩ := circuitAt_of_base he hF heF
    let C : CircuitThrough M e := ⟨circuitAt M F e, hC, heC⟩
    have hunion : F \ C.val ∪ C.val.erase e = F := by
      rw [← hpart, sdiff_union_inter]
    have hT := (contract_base_iff (circuit_erase_basis hC heC) disjoint_sdiff.symm).mpr
      (hunion.symm ▸ hF)
    rw [reconstruct_coord (restrict M e z) C hF hpart]
    change _ * restrictChain M C.val e z.val (F \ C.val) = z.val F
    rw [restrictChain, ite_eq_left hT, hunion, ← mul_assoc, restrictionSign_sq, one_mul]
  · exact ((reconstruct M e (restrict M e z)).prop.vanishes _ hF).trans (z.prop.vanishes _ hF).symm

private lemma restrict_reconstruct (M : Matroid V) (e : V)
    (w : (C : CircuitThrough M e) → topCycles (M ／ (C.val : Set V))) :
    restrict M e (reconstruct M e w) = w := by
  funext C
  apply Subtype.ext
  funext T
  change restrictChain M C.val e (reconstruct M e w).val T = (w C).val T
  by_cases hT : (M ／ (C.val : Set V)).IsBase (T : Set V)
  · have hd := contract_base_disjoint hT
    obtain ⟨hpart, hsdiff⟩ := split_circuit_face hd e
    have hF := (contract_base_iff (circuit_erase_basis C.prop.1 C.prop.2) hd).mp hT
    rw [restrictChain, ite_eq_left hT, reconstruct_coord w C hF hpart, hsdiff,
      ← mul_assoc, restrictionSign_sq, one_mul]
  · rw [restrictChain, ite_eq_right hT, (w C).prop.vanishes _ hT]

open scoped Classical in
/-- The integral linear equivalence, together with its signed restriction and join formulas. -/
theorem circuit_cycle_decomposition (M : Matroid V) (e : V)
    (he : e ∈ M.E) :
    ∃ E : topCycles M ≃ₗ[ℤ] ((C : CircuitThrough M e) → topCycles (M ／ (C.val : Set V))),
      (∀ z C T, (E z C).val T =
        if (M ／ (C.val : Set V)).IsBase (T : Set V) then
          insertionSign (C.val.erase e) e * shuffleSign (C.val.erase e) T *
            z.val (T ∪ C.val.erase e)
        else 0) ∧
      ∀ w F, (E.symm w).val F =
        ∑ C : CircuitThrough M e, signedJoin C.val (simplexBoundary C.val) (w C).val F := by
  let E : topCycles M ≃ₗ[ℤ] ((C : CircuitThrough M e) → topCycles (M ／ (C.val : Set V))) :=
    { toFun := restrict M e
      invFun := reconstruct M e
      left_inv := reconstruct_restrict he
      right_inv := restrict_reconstruct M e
      map_add' := by
        intro z w
        funext C
        apply Subtype.ext
        funext T
        change restrictChain M C.val e (z.val + w.val) T =
          restrictChain M C.val e z.val T + restrictChain M C.val e w.val T
        by_cases hT : (M ／ (C.val : Set V)).IsBase (T : Set V)
        · simp only [restrictChain, ite_eq_left hT, Pi.add_apply, mul_add]
        · simp only [restrictChain, ite_eq_right hT, add_zero]
      map_smul' := by
        intro n z
        funext C
        apply Subtype.ext
        funext T
        change restrictChain M C.val e (n • z.val) T = n * restrictChain M C.val e z.val T
        by_cases hT : (M ／ (C.val : Set V)).IsBase (T : Set V)
        · simp only [restrictChain, ite_eq_left hT, Pi.smul_apply, smul_eq_mul, mul_left_comm]
        · simp only [restrictChain, ite_eq_right hT, mul_zero] }
  exact ⟨E, fun _ _ _ => rfl, reconstruct_apply⟩

end D5.S3.Combinatorics.Matroids.CircuitCycleDecomposition
