/- GID: D5/S3/Combinatorics/Matroids/JointCircuitGramCertificate
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/JointCircuitGramCertificate
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Signed adjointness and the integral Gram certificate for joint circuit restriction. -/

module

public import D5.S3.Combinatorics.Matroids.IntegralCircuitImage
public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Joint circuit restriction and the integral Gram certificate -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Matrix
open scoped Matroid

namespace D5.S3.Combinatorics.Matroids.JointCircuitGramCertificate

open OrderedCycleFactorization IntegralCircuitImage
open CircuitCycleDecomposition (topCycles CircuitThrough circuit_cycle_decomposition
  restrictChain restrictionSign join_topCycle)

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- A circuit of the original matroid, represented by its finite vertex set. -/
abbrev Circuit (M : Matroid V) := {K : Finset V // M.IsCircuit (K : Set V)}

/-- A basis at which all internal exchanges admit a smaller vertex. -/
abbrev Passive (M : Matroid V) := {B : Finset V // PassiveBase M B}

omit [Fintype V] in
private lemma facet_join_apply {K T : Finset V} (hd : Disjoint T K) {a : V}
    (ha : a ∈ K) (w : Chain V) :
    signedJoin K (simplexBoundary K) w (T ∪ K.erase a) = restrictionSign K a T * w T := by
  obtain ⟨hi, hs⟩ := split_circuit_face hd a
  have h := facet_join hd ha
  rw [signedJoin, hi, hs, simplex, ite_eq_left rfl, mul_one] at h
  simp only [signedJoin, hi, hs, ← h, mul_assoc]

/-- The aggregate is adjoint to the oriented join in ordinary integral face coordinates. -/
theorem aggregate_adjoint {M : Matroid V} {K : Finset V} (z : Chain V)
    (w : topCycles (M ／ (K : Set V))) :
    dotProduct (aggregateRestrict M K z) w.val =
      dotProduct z (signedJoin K (simplexBoundary K) w.val) := by
  classical
  let N := M ／ (K : Set V)
  let bases := univ.filter fun T : Finset V => N.IsBase (T : Set V)
  let faces := univ.filter fun F : Finset V =>
    N.IsBase (↑(F \ K) : Set V) ∧ simplexBoundary K (F ∩ K) ≠ 0
  let leftTerm (p : V × Finset V) := restrictionSign K p.1 p.2 *
    z (p.2 ∪ K.erase p.1) * w.val p.2
  let rightTerm (F : Finset V) := z F * signedJoin K (simplexBoundary K) w.val F
  have hleft : dotProduct (aggregateRestrict M K z) w.val =
      ∑ p ∈ K ×ˢ bases, leftTerm p := by
    rw [sum_product, dotProduct]
    rw [← sum_subset (show bases ⊆ univ from filter_subset _ _)]
    · simp only [aggregateRestrict, Finset.sum_apply, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro T hT
      have hb := (mem_filter.mp hT).2
      simp [leftTerm, restrictChain, N, hb]
    · intro T _ hT
      rw [w.prop.vanishes T (fun h => hT (mem_filter.mpr ⟨mem_univ _, h⟩)), mul_zero]
  have hright : dotProduct z (signedJoin K (simplexBoundary K) w.val) =
      ∑ F ∈ faces, rightTerm F := by
    symm
    apply sum_subset (filter_subset _ _)
    intro F _ hF
    change rightTerm F = 0
    by_cases hb : N.IsBase (↑(F \ K) : Set V)
    · have he : simplexBoundary K (F ∩ K) = 0 :=
        not_ne_iff.mp (fun hn => hF (mem_filter.mpr ⟨mem_univ _, hb, hn⟩))
      simp [rightTerm, signedJoin, he]
    · simp [rightTerm, signedJoin, w.prop.vanishes _ hb]
  rw [hleft, hright]
  refine sum_bij (fun p _ => p.2 ∪ K.erase p.1) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨ha, hT⟩ := mem_product.mp hp
    have hb := (mem_filter.mp hT).2
    obtain ⟨hi, hs⟩ := split_circuit_face (contract_base_disjoint hb) p.1
    exact mem_filter.mpr ⟨mem_univ _, by rwa [hs],
      simplexBoundary_support.mpr ⟨p.1, ha, hi⟩⟩
  · rintro ⟨a, T⟩ hp ⟨b, U⟩ hq he
    obtain ⟨ha, hT⟩ := mem_product.mp hp
    obtain ⟨hb, hU⟩ := mem_product.mp hq
    obtain ⟨hiT, hsT⟩ := split_circuit_face (contract_base_disjoint (mem_filter.mp hT).2) a
    obtain ⟨hiU, hsU⟩ := split_circuit_face (contract_base_disjoint (mem_filter.mp hU).2) b
    have hTU := hsT.symm.trans ((congrArg (· \ K) he).trans hsU)
    have hab := hiT.symm.trans ((congrArg (· ∩ K) he).trans hiU)
    have heq : a = b := by
      by_contra hn
      exact notMem_erase a K (hab ▸ mem_erase.mpr ⟨hn, ha⟩)
    exact Prod.ext heq hTU
  · intro F hF
    obtain ⟨hT, hA⟩ := (mem_filter.mp hF).2
    obtain ⟨a, ha, hA⟩ := simplexBoundary_support.mp hA
    exact ⟨(a, F \ K), mem_product.mpr ⟨ha, mem_filter.mpr ⟨mem_univ _, hT⟩⟩,
      by rw [← hA, sdiff_union_inter]⟩
  · intro p hp
    obtain ⟨ha, hT⟩ := mem_product.mp hp
    simp only [rightTerm, leftTerm, facet_join_apply (contract_base_disjoint (mem_filter.mp hT).2) ha]
    ring

end D5.S3.Combinatorics.Matroids.JointCircuitGramCertificate
