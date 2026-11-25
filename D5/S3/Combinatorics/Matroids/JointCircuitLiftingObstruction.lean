/- GID: D5/S3/Combinatorics/Matroids/JointCircuitLiftingObstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/JointCircuitLiftingObstruction
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: The saturation quotient of joint circuit restriction and its rank-one direct-sum order. -/

module

public import D5.S3.Combinatorics.Matroids.DirectSumCircuitTorsion
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Integral joint circuit lifting obstructions -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Module TensorProduct
open scoped Matroid

namespace D5.S3.Combinatorics.Matroids.JointCircuitLiftingObstruction

open DirectSumCircuitTorsion
open OrderedCycleFactorization (Chain TopCycle boundaryOn shuffleSign)
open CircuitCycleDecomposition (restrictChain restrictionSign topCycles)
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)
open IntegralCircuitImage (aggregateRestrict)
open JointCircuitGramCertificate (Circuit Passive)

variable {V : Type*} [Fintype V] [LinearOrder V] {M N : Matroid V} {L R : Finset V}

omit [Fintype V] in
private lemma rankOne_pair_isCircuit {P : Matroid V} {S : Finset V}
    (hS : (S : Set V) = P.E)
    (hbase : ∀ F : Finset V, P.IsBase (F : Set V) ↔ ∃ x ∈ S, F = {x})
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) :
    P.IsCircuit (↑({x, y} : Finset V) : Set V) := by
  have hxB : P.IsBase (↑({x} : Finset V) : Set V) := (hbase _).mpr ⟨x, hx, rfl⟩
  have hyB : P.IsBase (↑({y} : Finset V) : Set V) := (hbase _).mpr ⟨y, hy, rfl⟩
  have hS' : (↑({x, y} : Finset V) : Set V) ⊆ P.E := by
    rw [← hS, coe_subset]
    exact insert_subset hx (singleton_subset_iff.2 hy)
  rw [Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep]
  constructor
  · apply (Matroid.not_indep_iff hS').mp
    intro hi
    have he := hxB.eq_of_subset_indep hi (by
      rw [coe_subset]
      simp)
    have hyx : y ∈ (↑({x} : Finset V) : Set V) := by rw [he]; simp
    exact hne (by simpa [eq_comm] using hyx)
  · intro a ha
    have ha' : a = x ∨ a = y := by simpa using ha
    rcases ha' with rfl | rfl
    · simpa [hne, hne.symm] using hyB.indep
    · simpa [hne, hne.symm] using hxB.indep

omit [Fintype V] in
private lemma rankOne_circuit_eq_pair {P : Matroid V} {S C : Finset V}
    (hS : (S : Set V) = P.E)
    (hbase : ∀ F : Finset V, P.IsBase (F : Set V) ↔ ∃ x ∈ S, F = {x})
    (hC : P.IsCircuit (C : Set V)) :
    ∃ x ∈ S, ∃ y ∈ S, x < y ∧ C = {x, y} := by
  obtain ⟨x, hx⟩ := hC.nonempty
  have hxS : x ∈ S := by
    change x ∈ (S : Set V)
    rw [hS]
    exact hC.subset_ground hx
  have hd : (C.erase x).Nonempty := by
    by_contra he
    have he' := not_nonempty_iff_eq_empty.mp he
    have hC' : C = {x} := by rw [← insert_erase hx, he', insert_empty_eq]
    exact hC.not_indep (((hbase C).mpr ⟨x, hxS, hC'⟩).indep)
  obtain ⟨y, hy⟩ := hd
  have hyS : y ∈ S := by
    change y ∈ (S : Set V)
    rw [hS]
    exact hC.subset_ground (mem_of_mem_erase hy)
  have hneq := ne_of_mem_erase hy
  have hpair := rankOne_pair_isCircuit hS hbase hxS hyS hneq.symm
  have hsub : (↑({x, y} : Finset V) : Set V) ⊆ (C : Set V) := by
    rw [coe_subset]
    exact insert_subset hx (singleton_subset_iff.2 (mem_of_mem_erase hy))
  have hEq : C = {x, y} := by
    exact_mod_cast (hC.eq_of_not_indep_subset hpair.not_indep hsub).symm
  rcases lt_or_gt_of_ne hneq.symm with hlt | hlt
  · exact ⟨x, hxS, y, hyS, hlt, hEq⟩
  · exact ⟨y, hyS, x, hxS, hlt, hEq.trans (pair_comm x y)⟩

omit [Fintype V] in
private lemma rankOne_pair_contract_base {P : Matroid V} {S : Finset V}
    (hS : (S : Set V) = P.E)
    (hbase : ∀ F : Finset V, P.IsBase (F : Set V) ↔ ∃ x ∈ S, F = {x})
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) (T : Finset V) :
    (P ／ (↑({x, y} : Finset V) : Set V)).IsBase (T : Set V) ↔ T = ∅ := by
  let C : Finset V := {x, y}
  have hxC : x ∈ C := by simp [C]
  have hyC : y ∈ C := by simp [C]
  have hC := rankOne_pair_isCircuit hS hbase hx hy hne
  have hfacet : C.erase x = {y} := by simp [C, hne]
  have hB := OrderedCycleFactorization.circuit_erase_basis hC hxC
  constructor
  · intro ht
    have hd := OrderedCycleFactorization.contract_base_disjoint ht
    obtain ⟨z, _, hz⟩ := (hbase _).mp
      ((OrderedCycleFactorization.contract_base_iff hB hd).mp ht)
    rw [hfacet] at hz
    have he : y = z := by
      have hm : y ∈ T ∪ {y} := by simp
      simpa [hz] using hm
    subst z
    apply eq_empty_iff_forall_notMem.2
    intro a ha
    have hm : a ∈ T ∪ {y} := mem_union_left _ ha
    have hae : a = y := by simpa [hz] using hm
    exact Finset.disjoint_left.mp hd (hae ▸ ha) hyC
  · rintro rfl
    apply (OrderedCycleFactorization.contract_base_iff hB (show Disjoint ∅ C by simp)).mpr
    rw [empty_union, hfacet]
    exact (hbase _).mpr ⟨y, hy, rfl⟩

private lemma rankOne_circuitRow_pair {P : Matroid V} {S : Finset V}
    (hS : (S : Set V) = P.E)
    (hbase : ∀ F : Finset V, P.IsBase (F : Set V) ↔ ∃ x ∈ S, F = {x})
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (T : Finset V) :
    circuitRow P {x, y} T =
      if T = ∅ then cycleEvaluation P {y} - cycleEvaluation P {x} else 0 := by
  have hb := rankOne_pair_contract_base hS hbase hx hy hxy.ne T
  by_cases hT : T = ∅
  · subst T
    rw [ite_eq_left rfl]
    ext z
    change aggregateRestrict P {x, y} z.val ∅ = z.val {y} - z.val {x}
    have hx' : ({x, y} : Finset V).erase x = {y} := by simp [hxy.ne]
    have hy' : ({x, y} : Finset V).erase y = {x} := by
      rw [pair_comm, erase_insert (by simpa using hxy.ne.symm)]
    have hpos : restrictionSign ({x, y} : Finset V) x ∅ = 1 := by
      simp [restrictionSign, hx', insertionSign, shuffleSign, filter_singleton, hxy.not_gt]
    have hneg : restrictionSign ({x, y} : Finset V) y ∅ = -1 := by
      simp [restrictionSign, hy', insertionSign, shuffleSign, filter_singleton, hxy]
    simp only [aggregateRestrict, Finset.sum_apply, sum_pair hxy.ne, restrictChain,
      hb, ite_true, hpos, hneg, hx', hy', empty_union, one_mul, neg_one_mul]
    ring
  · rw [ite_eq_right hT]
    ext z
    change aggregateRestrict P {x, y} z.val T = 0
    simp only [aggregateRestrict, Finset.sum_apply, restrictChain, hb,
      ite_eq_right hT, sum_const_zero]

private lemma rankOne_singletons_span {P : Matroid V} {S : Finset V}
    (hbase : ∀ F : Finset V, P.IsBase (F : Set V) ↔ ∃ x ∈ S, F = {x}) :
    Submodule.span ℤ {f | ∃ x ∈ S, cycleEvaluation P {x} = f} = ⊤ := by
  apply top_unique
  rw [← cycleEvaluation_span P]
  apply Submodule.span_le.2
  rintro _ ⟨F, rfl⟩
  by_cases hF : P.IsBase (F : Set V)
  · obtain ⟨x, hx, rfl⟩ := (hbase F).mp hF
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  · have he : cycleEvaluation P F = 0 := LinearMap.ext fun z => z.prop.vanishes F hF
    rw [he]
    exact Submodule.zero_mem _

private lemma rankOne_sum_evaluation {P : Matroid V} {S : Finset V}
    (hbase : ∀ F : Finset V, P.IsBase (F : Set V) ↔ ∃ x ∈ S, F = {x}) :
    (∑ x ∈ S, cycleEvaluation P {x}) = 0 := by
  ext z
  simp only [LinearMap.sum_apply, LinearMap.zero_apply]
  change (∑ x ∈ S, z.val {x}) = 0
  have hvan (x : V) (hx : x ∉ S) : z.val {x} = 0 := by
    apply z.prop.vanishes
    intro hb
    obtain ⟨y, hy, he⟩ := (hbase {x}).mp hb
    exact hx ((singleton_inj.mp he).symm ▸ hy)
  have hsum := z.prop.cycle ∅
  simp only [boundaryOn, sdiff_empty, insertionSign, filter_empty, card_empty, pow_zero,
    one_mul, insert_empty_eq] at hsum
  calc
    ∑ x ∈ S, z.val {x} = ∑ x, z.val {x} :=
      sum_subset (subset_univ S) fun x _ hx => hvan x hx
    _ = 0 := hsum

private lemma rankOne_eval_equal_in_cokernel {P : Matroid V} {S : Finset V}
    (hS : (S : Set V) = P.E)
    (hbase : ∀ F : Finset V, P.IsBase (F : Set V) ↔ ∃ x ∈ S, F = {x})
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    (Submodule.Quotient.mk (cycleEvaluation P {x}) : TransposeCokernel P) =
      Submodule.Quotient.mk (cycleEvaluation P {y}) := by
  have hrelation (a b : V) (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) :
      (Submodule.Quotient.mk (cycleEvaluation P {b}) : TransposeCokernel P) =
        Submodule.Quotient.mk (cycleEvaluation P {a}) := by
    have he := rankOne_circuitRow_pair hS hbase ha hb hab ∅
    rw [ite_eq_left rfl] at he
    have hrow : circuitRow P {a, b} ∅ ∈ (jointRestriction P).dualMap.range := by
      rw [range_dual_jointRestriction]
      exact Submodule.subset_span
        (circuitRow_mem_rows (rankOne_pair_isCircuit hS hbase ha hb hab.ne) ∅)
    rw [he] at hrow
    exact (Submodule.Quotient.eq _).2 hrow
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · exact (hrelation x y hx hy hxy).symm
  · rfl
  · exact hrelation y x hy hx hyx

private lemma rankOne_cokernel_generator {P : Matroid V} {S : Finset V}
    (hS : (S : Set V) = P.E)
    (hbase : ∀ F : Finset V, P.IsBase (F : Set V) ↔ ∃ x ∈ S, F = {x})
    {e : V} (he : e ∈ S) :
    let g : TransposeCokernel P := Submodule.Quotient.mk (cycleEvaluation P {e})
    (∀ x : TransposeCokernel P, ∃ a : ℤ, a • g = x) ∧ S.card • g = 0 := by
  let q := (jointRestriction P).dualMap.range.mkQ
  let g : TransposeCokernel P := q (cycleEvaluation P {e})
  change (∀ x : TransposeCokernel P, ∃ a : ℤ, a • g = x) ∧ S.card • g = 0
  have hclass (x : V) (hx : x ∈ S) : q (cycleEvaluation P {x}) = g :=
    rankOne_eval_equal_in_cokernel hS hbase hx he
  constructor
  · intro x
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have htop : ⊤ ≤ (Submodule.span ℤ {g}).comap q := by
      rw [← rankOne_singletons_span hbase]
      apply Submodule.span_le.2
      rintro _ ⟨y, hy, rfl⟩
      change q (cycleEvaluation P {y}) ∈ Submodule.span ℤ {g}
      rw [hclass y hy]
      exact Submodule.subset_span (Set.mem_singleton g)
    exact Submodule.mem_span_singleton.mp (htop (show f ∈ ⊤ from Submodule.mem_top))
  · have hzero := congrArg q (rankOne_sum_evaluation hbase)
    rw [map_sum, map_zero] at hzero
    calc
      S.card • g = ∑ _x ∈ S, g := by rw [sum_const]
      _ = ∑ x ∈ S, q (cycleEvaluation P {x}) :=
        sum_congr rfl (fun x hx => (hclass x hx).symm)
      _ = 0 := hzero

private lemma rankOne_cycle_of_sum_zero {P : Matroid V} {S : Finset V}
    (hbase : ∀ F : Finset V, P.IsBase (F : Set V) ↔ ∃ x ∈ S, F = {x})
    {z : Chain V}
    (hsupport : ∀ F, (¬ ∃ x ∈ S, F = {x}) → z F = 0)
    (hzero : ∑ x ∈ S, z {x} = 0) : TopCycle P z := by
  refine ⟨fun F hF => hsupport F (fun ht => hF ((hbase F).mpr ht)), ?_⟩
  intro F
  by_cases hF : F = ∅
  · subst F
    simp only [boundaryOn, sdiff_empty, insertionSign, filter_empty, card_empty, pow_zero,
      one_mul, insert_empty_eq]
    rw [← sum_subset (subset_univ S) (fun x _ hx => hsupport {x} ?_)]
    · exact hzero
    · rintro ⟨y, hy, heq⟩
      exact hx ((singleton_inj.mp heq).symm ▸ hy)
  · unfold boundaryOn
    apply sum_eq_zero
    intro x hx
    rw [hsupport, mul_zero]
    rintro ⟨y, _, heq⟩
    have hxy : x = y := by
      have hmem := mem_insert_self x F
      rw [heq, mem_singleton] at hmem
      exact hmem
    have hFx : F ⊆ {x} := by
      rw [hxy]
      exact subset_insert x F |>.trans_eq heq
    have hxF := (mem_sdiff.mp hx).2
    apply hF
    apply eq_empty_iff_forall_notMem.2
    intro v hv
    have hvx := mem_singleton.mp (hFx hv)
    exact hxF (hvx ▸ hv)

private lemma rankOne_constant_residue_cycle {P : Matroid V} {S : Finset V}
    (hbase : ∀ F : Finset V, P.IsBase (F : Set V) ↔ ∃ x ∈ S, F = {x})
    {e : V} (he : e ∈ S) :
    ∃ z : topCycles P, ∀ x ∈ S,
      z.val {x} = 1 - if x = e then (S.card : ℤ) else 0 := by
  classical
  let z : Chain V := fun F =>
    if ∃ x ∈ S, F = {x} then 1 - if F = {e} then (S.card : ℤ) else 0 else 0
  have hvalue (x : V) (hx : x ∈ S) :
      z {x} = 1 - if x = e then (S.card : ℤ) else 0 := by
    unfold z
    rw [ite_eq_left ⟨x, hx, rfl⟩]
    simp only [singleton_inj]
  have hzero : ∑ x ∈ S, z {x} = 0 := by
    rw [sum_congr rfl hvalue, sum_sub_distrib, sum_ite_eq', ite_eq_left he, sum_const]
    simp
  exact ⟨⟨z, rankOne_cycle_of_sum_zero hbase
    (fun F hF => ite_eq_right hF) hzero⟩, hvalue⟩

private lemma rankOne_ground_nonempty {P : Matroid V} {S : Finset V}
    (hbase : ∀ F : Finset V, P.IsBase (F : Set V) ↔ ∃ x ∈ S, F = {x}) :
    S.Nonempty := by
  classical
  obtain ⟨B, hB⟩ := P.exists_isBase
  obtain ⟨x, hx, _⟩ := (hbase (Set.toFinite B).toFinset).mp
    (by simpa only [Set.Finite.coe_toFinset] using hB)
  exact ⟨x, hx⟩

private lemma cyclic_equiv_zmod {G : Type*} [AddCommGroup G] (n : ℕ)
    (q : G →ₗ[ℤ] ZMod n) (g : G) (hqg : q g = 1)
    (hgen : ∀ x : G, ∃ a : ℤ, a • g = x) (hAnn : (n : ℤ) • g = 0) :
    Nonempty (G ≃ₗ[ℤ] ZMod n) := by
  have hq (a : ℤ) : q (a • g) = (a : ZMod n) := by
    rw [map_smul, hqg, zsmul_eq_mul, mul_one]
  refine ⟨LinearEquiv.ofBijective q ⟨?_, ?_⟩⟩
  · intro x y hxy
    obtain ⟨a, ha⟩ := hgen x
    obtain ⟨b, hb⟩ := hgen y
    rw [← ha, ← hb, hq, hq] at hxy
    have hcast : ((a - b : ℤ) : ZMod n) = 0 := by simp [hxy]
    obtain ⟨d, hd⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) n).mp hcast
    rw [← ha, ← hb]
    apply sub_eq_zero.mp
    rw [← sub_smul, hd, mul_comm, mul_smul, hAnn, smul_zero]
  · intro x
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
    exact ⟨a • g, hq a⟩

/-- A rank-one matroid whose bases are the ground singletons has cyclic transpose cokernel
of order the ground cardinality. -/
theorem rank_one_transpose_cokernel (P : Matroid V) (S : Finset V)
    (hS : (S : Set V) = P.E)
    (hbase : ∀ F : Finset V, P.IsBase (F : Set V) ↔ ∃ x ∈ S, F = {x}) :
    Nonempty (TransposeCokernel P ≃ₗ[ℤ] ZMod S.card) := by
  classical
  obtain ⟨e, he⟩ := rankOne_ground_nonempty hbase
  obtain ⟨z, hz⟩ := rankOne_constant_residue_cycle hbase he
  let f : Dual ℤ (topCycles P) →ₗ[ℤ] ZMod S.card :=
    (Int.castAddHom (ZMod S.card)).toIntLinearMap.comp (Dual.eval ℤ (topCycles P) z)
  have hf (x : V) (hx : x ∈ S) : f (cycleEvaluation P {x}) = 1 := by
    change (z.val {x} : ZMod S.card) = 1
    rw [hz x hx]
    by_cases heq : x = e <;> simp [heq]
  let U := (jointRestriction P).dualMap.range
  have hU : U ≤ f.ker := by
    change (jointRestriction P).dualMap.range ≤ _
    rw [range_dual_jointRestriction]
    apply Submodule.span_le.2
    rintro _ ⟨⟨C, T⟩, rfl⟩
    change f (circuitRow P C.val T) = 0
    obtain ⟨x, hx, y, hy, hxy, hC⟩ := rankOne_circuit_eq_pair hS hbase C.prop
    rw [hC, rankOne_circuitRow_pair hS hbase hx hy hxy T]
    split <;> simp [hf x hx, hf y hy]
  let q := U.liftQ f hU
  let g : TransposeCokernel P := Submodule.Quotient.mk (cycleEvaluation P {e})
  obtain ⟨hgen, hAnn⟩ := rankOne_cokernel_generator hS hbase he
  exact cyclic_equiv_zmod _ q g (hf e he) hgen (by exact_mod_cast hAnn)

private lemma zmod_tensor_gcd (m n : ℕ) :
    Nonempty ((ZMod m ⊗[ℤ] ZMod n) ≃ₗ[ℤ] ZMod (m.gcd n)) := by
  let a := (ZMod.castHom (Nat.gcd_dvd_left m n) (ZMod (m.gcd n))).toAddMonoidHom.toIntLinearMap
  let b := (ZMod.castHom (Nat.gcd_dvd_right m n) (ZMod (m.gcd n))).toAddMonoidHom.toIntLinearMap
  let q := (LinearMap.mul' ℤ (ZMod (m.gcd n))).comp (TensorProduct.map a b)
  let g : ZMod m ⊗[ℤ] ZMod n := (1 : ZMod m) ⊗ₜ[ℤ] (1 : ZMod n)
  have hq : q g = 1 := by
    change LinearMap.mul' ℤ _ (TensorProduct.map a b ((1 : ZMod m) ⊗ₜ[ℤ] (1 : ZMod n))) = 1
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply]
    change ZMod.castHom (Nat.gcd_dvd_left m n) (ZMod (m.gcd n)) (1 : ZMod m) *
      ZMod.castHom (Nat.gcd_dvd_right m n) (ZMod (m.gcd n)) (1 : ZMod n) = 1
    rw [map_one, map_one, mul_one]
  have hg : Submodule.span ℤ {g} = ⊤ := by
    apply top_unique
    have hspan : Submodule.span ℤ {t : ZMod m ⊗[ℤ] ZMod n |
        ∃ x : ZMod m, ∃ y : ZMod n, x ⊗ₜ[ℤ] y = t} = ⊤ :=
      TensorProduct.span_tmul_eq_top ℤ (ZMod m) (ZMod n)
    refine hspan ▸ (Submodule.span_le.2 ?_)
    rintro _ ⟨x, y, rfl⟩
    obtain ⟨i, rfl⟩ := ZMod.intCast_surjective x
    obtain ⟨j, rfl⟩ := ZMod.intCast_surjective y
    apply Submodule.mem_span_singleton.mpr
    refine ⟨i * j, ?_⟩
    calc
      (i * j) • g = (i • (1 : ZMod m)) ⊗ₜ[ℤ] (j • (1 : ZMod n)) := by
        rw [← smul_tmul', tmul_smul, smul_smul]
      _ = _ := by simp [zsmul_eq_mul]
  have hm : (m : ℤ) • g = 0 := by
    change (m : ℤ) • ((1 : ZMod m) ⊗ₜ[ℤ] (1 : ZMod n)) = 0
    rw [smul_tmul']
    simp [zsmul_eq_mul]
  have hn : (n : ℤ) • g = 0 := by
    change (n : ℤ) • ((1 : ZMod m) ⊗ₜ[ℤ] (1 : ZMod n)) = 0
    rw [← tmul_smul]
    simp [zsmul_eq_mul]
  have hAnn : (m.gcd n : ℤ) • g = 0 := by
    rw [Nat.gcd_eq_gcd_ab, add_smul, mul_comm (m : ℤ), mul_comm (n : ℤ), mul_smul, mul_smul,
      hm, hn, smul_zero, smul_zero, add_zero]
  exact cyclic_equiv_zmod _ q g hq
    (fun x => Submodule.mem_span_singleton.mp (hg.symm ▸ (show x ∈ ⊤ from Submodule.mem_top))) hAnn

/-- For a block-ordered direct sum of rank-one loopless matroids, the integral transpose
cokernel is cyclic of order the greatest common divisor of the two ground cardinalities. -/
private theorem rank_one_sum_transpose_cokernel (h : Disjoint M.E N.E)
    (hL : (L : Set V) = M.E) (hR : (R : Set V) = N.E)
    (horder : ∀ x ∈ L, ∀ y ∈ R, x < y)
    (hM : ∀ F : Finset V, M.IsBase (F : Set V) ↔ ∃ x ∈ L, F = {x})
    (hN : ∀ F : Finset V, N.IsBase (F : Set V) ↔ ∃ x ∈ R, F = {x}) :
    Nonempty (TransposeCokernel (M.disjointSum N h) ≃ₗ[ℤ] ZMod (L.card.gcd R.card)) := by
  obtain ⟨_, _, _, _, e, _⟩ := joint_circuit_transpose_cokernel_tensor h hL hR horder
  obtain ⟨a⟩ := rank_one_transpose_cokernel M L hL hM
  obtain ⟨b⟩ := rank_one_transpose_cokernel N R hR hN
  obtain ⟨c⟩ := zmod_tensor_gcd L.card R.card
  exact ⟨(e.symm.trans (TensorProduct.congr a b)).trans c⟩

private theorem torsion_cokernel_dual {X Y ι : Type*} [AddCommGroup X] [AddCommGroup Y]
    [_root_.Finite ι] (A : X →ₗ[ℤ] Y) (hinj : Function.Injective A) (basis : Basis ι ℤ Y) :
    Nonempty ((Dual ℤ X ⧸ A.dualMap.range) ≃ₗ[ℤ]
      Submodule.torsion ℤ (Y ⧸ A.range)) := by
  classical
  let : Fintype ι := Fintype.ofFinite _
  let P := A.range
  let normal := P.smithNormalForm basis
  let s := normal.2
  let e := LinearEquiv.ofInjective A hinj
  let d := s.bN.map e.symm
  let q := P.mkQ
  have hA i : A (d i) = s.a i • s.bM (s.f i) := by
    change A (e.symm (s.bN i)) = _
    exact (congrArg Subtype.val (e.apply_symm_apply (s.bN i))).trans (s.snf i)
  have ha i : s.a i ≠ 0 := by
    intro haz
    exact s.bN.ne_zero i (Subtype.ext (by simpa [haz] using s.snf i))
  let F : Dual ℤ X →ₗ[ℤ] Y := d.dualBasis.constr ℤ fun i => s.bM (s.f i)
  have hF (a : Dual ℤ X) :
      F a = ∑ i : Fin normal.1, a (d i) • s.bM (s.f i) := by
    calc
      F a = F (∑ i : Fin normal.1, d.dualBasis.repr a i • d.dualBasis i) :=
        congrArg F (d.dualBasis.sum_repr a).symm
      _ = _ := by
        rw [map_sum]
        simp only [map_smul, F, Basis.constr_basis, Basis.dualBasis_repr]
  have hFcoord (a : Dual ℤ X) (i : Fin normal.1) : s.bM.repr (F a) (s.f i) = a (d i) := by
    rw [hF, map_sum]
    simp [Finsupp.finsetSum_apply, Basis.repr_self, Finsupp.single_apply,
      EmbeddingLike.apply_eq_iff_eq]
  have hFt (a : Dual ℤ X) : q (F a) ∈ Submodule.torsion ℤ (Y ⧸ A.range) := by
    rw [hF, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    apply Submodule.smul_mem
    rw [Submodule.mem_torsion_iff]
    refine ⟨⟨s.a i, mem_nonZeroDivisors_iff_ne_zero.mpr (ha i)⟩, ?_⟩
    change s.a i • q (s.bM (s.f i)) = 0
    rw [← map_smul, ← s.snf i]
    exact (Submodule.Quotient.mk_eq_zero P).mpr (s.bN i).prop
  let T := (q.comp F).codRestrict (Submodule.torsion ℤ (Y ⧸ A.range)) hFt
  have hker : T.ker = A.dualMap.range := by
    apply le_antisymm
    · intro a h
      have hFa : F a ∈ P :=
        (Submodule.Quotient.mk_eq_zero P).mp (congrArg Subtype.val h)
      let v : P := ⟨F a, hFa⟩
      let b : Dual ℤ Y := s.bM.constr ℤ fun j =>
        if hj : j ∈ Set.range s.f then s.bN.repr v (Classical.choose hj) else 0
      refine ⟨b, d.ext fun i => ?_⟩
      change b (A (d i)) = a (d i)
      rw [hA, map_smul]
      have hi : s.f i ∈ Set.range s.f := ⟨i, rfl⟩
      have hchoose : Classical.choose hi = i := s.f.injective (Classical.choose_spec hi)
      have hb : b (s.bM (s.f i)) = s.bN.repr v i := by
        dsimp only [b]
        rw [Basis.constr_basis, dite_eq_left hi, hchoose]
      rw [hb]
      have hs := s.repr_apply_embedding_eq_repr_smul v (i := i)
      rw [map_smul, Finsupp.smul_apply] at hs
      exact hs.symm.trans (hFcoord a i)
    · rintro _ ⟨b, rfl⟩
      apply Subtype.ext
      change q (F (A.dualMap b)) = 0
      apply (Submodule.Quotient.mk_eq_zero P).mpr
      rw [hF]
      apply Submodule.sum_mem
      intro i _
      change b (A (d i)) • s.bM (s.f i) ∈ P
      rw [hA, map_smul, smul_eq_mul, mul_comm, mul_smul, ← hA]
      exact Submodule.smul_mem _ _ (LinearMap.mem_range_self A (d i))
  have hsurj : Function.Surjective T := by
    intro t
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective P t.val
    change q y = t.val at hy
    have hout (j : ι) (hj : j ∉ Set.range s.f) : s.bM.repr y j = 0 := by
      obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff t.val).mp t.prop
      have hNy : (n : ℤ) • y ∈ P := by
        apply (Submodule.Quotient.mk_eq_zero P).mp
        change q ((n : ℤ) • y) = 0
        rw [map_smul, hy]
        exact hn
      have hv := s.repr_eq_zero_of_notMem_range ⟨(n : ℤ) • y, hNy⟩ hj
      change s.bM.repr ((n : ℤ) • y) j = 0 at hv
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul] at hv
      exact (mul_eq_zero.mp hv).resolve_left
        (mem_nonZeroDivisors_iff_ne_zero.mp n.prop)
    let a : Dual ℤ X := d.dualBasis.equivFun.symm fun i => s.bM.repr y (s.f i)
    have ha' (i : Fin normal.1) : a (d i) = s.bM.repr y (s.f i) := by
      rw [← Basis.dualBasis_equivFun]
      dsimp only [a]
      rw [LinearEquiv.apply_symm_apply]
    have heq : F a = y := by
      apply s.bM.repr.injective
      ext j
      by_cases hj : j ∈ Set.range s.f
      · obtain ⟨i, rfl⟩ := hj
        exact (hFcoord a i).trans (ha' i)
      · have hi : ∀ i : Fin normal.1, s.f i ≠ j := fun i h => hj ⟨i, h⟩
        rw [hout j hj, hF, map_sum]
        simp [Finsupp.finsetSum_apply, Basis.repr_self, hi]
    refine ⟨a, Subtype.ext ?_⟩
    change q (F a) = t.val
    rw [heq]
    exact hy
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (T.quotKerEquivOfSurjective hsurj)⟩

private noncomputable def jointTargetBasis (P : Matroid V) :
    Basis (Σ C : Circuit P, Passive (P ／ (C.val : Set V))) ℤ (JointTarget P) :=
  Basis.ofEquivFun
    ((LinearEquiv.piCongrRight (fun C : Circuit P => cycleCoordinates (P ／ (C.val : Set V)))).trans
      (LinearEquiv.piCurry ℤ (fun (_ : Circuit P) _ => ℤ)).symm)

/-- The integral lifting obstruction is the torsion in the quotient of the joint target by the
image of the source cycles. -/
noncomputable abbrev JointLiftingObstruction (P : Matroid V) :=
  Submodule.torsion ℤ (JointTarget P ⧸ (jointRestriction P).range)

/-- Integral tuples with a nonzero integer multiple in the joint image. -/
noncomputable abbrev JointSaturatedImage (P : Matroid V) : Submodule ℤ (JointTarget P) :=
  (JointLiftingObstruction P).comap (jointRestriction P).range.mkQ

/-- The joint image submodule in its saturation. -/
noncomputable abbrev JointImageInSaturation (P : Matroid V) :
    Submodule ℤ (JointSaturatedImage P) :=
  (jointRestriction P).range.comap (JointSaturatedImage P).subtype

private noncomputable def saturatedProjection (P : Matroid V) :
    JointSaturatedImage P →ₗ[ℤ] JointLiftingObstruction P :=
  ((jointRestriction P).range.mkQ.comp (JointSaturatedImage P).subtype).codRestrict _
    fun y => y.prop

private lemma saturatedProjection_ker (P : Matroid V) :
    (saturatedProjection P).ker = JointImageInSaturation P := by
  ext y
  change saturatedProjection P y = 0 ↔ y.val ∈ (jointRestriction P).range
  exact ⟨fun hy => (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hy),
    fun hy => Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr hy)⟩

private lemma saturatedProjection_surjective (P : Matroid V) :
    Function.Surjective (saturatedProjection P) := by
  intro y
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective (jointRestriction P).range y.val
  have hs : x ∈ JointSaturatedImage P := by
    change Submodule.Quotient.mk x ∈ JointLiftingObstruction P
    exact hx.symm ▸ y.prop
  exact ⟨⟨x, hs⟩, Subtype.ext hx⟩

/-- Smith coordinates identify the torsion in the joint restriction cokernel with its
integral transpose cokernel. The saturation quotient maps to the torsion submodule by
sending a saturated tuple to its original quotient class. -/
theorem joint_lifting_obstruction_equiv (P : Matroid V) {e : V} (he : e ∈ P.E) :
    ∃ comparison : (JointSaturatedImage P ⧸ JointImageInSaturation P) ≃ₗ[ℤ]
        JointLiftingObstruction P,
      (∀ y : JointSaturatedImage P, (comparison (Submodule.Quotient.mk y)).val =
        Submodule.Quotient.mk y.val) ∧
      Nonempty (JointLiftingObstruction P ≃ₗ[ℤ] TransposeCokernel P) := by
  obtain ⟨iso⟩ := torsion_cokernel_dual (jointRestriction P) (jointRestriction_injective he)
    (jointTargetBasis P)
  refine ⟨(Submodule.quotEquivOfEq _ _ (saturatedProjection_ker P).symm).trans
    ((saturatedProjection P).quotKerEquivOfSurjective (saturatedProjection_surjective P)),
    ?_, ⟨iso.symm⟩⟩
  intro y
  rfl

/-- The finite integral obstruction for the direct sum of two rank-one loopless matroids
is cyclic of order the greatest common divisor of their ground cardinalities. -/
theorem rank_one_sum_joint_lifting_obstruction (h : Disjoint M.E N.E)
    (hL : (L : Set V) = M.E) (hR : (R : Set V) = N.E)
    (horder : ∀ x ∈ L, ∀ y ∈ R, x < y)
    (hM : ∀ F : Finset V, M.IsBase (F : Set V) ↔ ∃ x ∈ L, F = {x})
    (hN : ∀ F : Finset V, N.IsBase (F : Set V) ↔ ∃ x ∈ R, F = {x}) :
    Nonempty ((JointSaturatedImage (M.disjointSum N h) ⧸
      JointImageInSaturation (M.disjointSum N h)) ≃ₗ[ℤ] ZMod (L.card.gcd R.card)) := by
  obtain ⟨e, he⟩ := rankOne_ground_nonempty hM
  have hground : e ∈ (M.disjointSum N h).E := by
    rw [Matroid.disjointSum_ground_eq, ← hL]
    exact Or.inl he
  obtain ⟨comparison, _, ⟨a⟩⟩ := joint_lifting_obstruction_equiv _ hground
  obtain ⟨b⟩ := rank_one_sum_transpose_cokernel h hL hR horder hM hN
  exact ⟨(comparison.trans a).trans b⟩

end D5.S3.Combinatorics.Matroids.JointCircuitLiftingObstruction
