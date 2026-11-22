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
open scoped Matroid Classical

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
private theorem aggregate_adjoint {M : Matroid V} {K : Finset V} (z : Chain V)
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
    simp only [rightTerm, leftTerm,
      facet_join_apply (contract_base_disjoint (mem_filter.mp hT).2) ha]
    ring


/-- The integral top cycle with unit coordinate at the given passive basis. -/
noncomputable def normalizedCycle {M : Matroid V} (B : Passive M) : topCycles M :=
  let h := (normalized_factorization M B.val B.prop).1.exists
  ⟨h.choose, h.choose_spec.toTopCycle⟩

private lemma normalizedCycle_coord {M : Matroid V} (B D : Passive M) :
    (normalizedCycle B).val D.val = if D = B then 1 else 0 := by
  classical
  have h := (normalized_factorization M B.val B.prop).1.exists.choose_spec.coordinate
    D.val D.prop
  simpa only [normalizedCycle, Subtype.ext_iff] using h

private noncomputable def fromCoordinates (M : Matroid V) (x : Passive M → ℤ) : topCycles M :=
  ∑ B, x B • normalizedCycle B

private lemma fromCoordinates_apply {M : Matroid V} (x : Passive M → ℤ) (F : Finset V) :
    (fromCoordinates M x).val F = ∑ B, x B * (normalizedCycle B).val F := by
  rw [fromCoordinates, Submodule.coe_sum, Finset.sum_apply]
  rfl

private lemma fromCoordinates_coord {M : Matroid V} (x : Passive M → ℤ) (D : Passive M) :
    (fromCoordinates M x).val D.val = x D := by
  classical
  rw [fromCoordinates_apply]
  simp [normalizedCycle_coord]

private lemma fromCoordinates_cycle {M : Matroid V} (z : topCycles M) :
    fromCoordinates M (fun B => z.val B.val) = z := by
  apply Subtype.ext
  apply topCycle_ext (fromCoordinates M _).prop z.prop
  exact fun F hF => fromCoordinates_coord (fun B => z.val B.val) ⟨F, hF⟩

/-- The Gram matrix in the normalized passive-basis coordinates. -/
noncomputable def gram (M : Matroid V) : Matrix (Passive M) (Passive M) ℤ :=
  fun B D => dotProduct (normalizedCycle B).val (normalizedCycle D).val

private lemma gram_mulVec {M : Matroid V} (x : Passive M → ℤ) (B : Passive M) :
    (gram M).mulVec x B = dotProduct (normalizedCycle B).val (fromCoordinates M x).val := by
  classical
  rw [fromCoordinates, Submodule.coe_sum, dotProduct_sum]
  apply sum_congr rfl
  intro D _
  rw [Submodule.coe_smul, dotProduct_smul]
  exact mul_comm _ _

private lemma dotProduct_cycle_expansion {M : Matroid V} (z w : topCycles M) :
    dotProduct z.val w.val =
      ∑ B : Passive M, dotProduct z.val (normalizedCycle B).val * w.val B.val := by
  classical
  conv_lhs => rw [← fromCoordinates_cycle w, fromCoordinates, Submodule.coe_sum, dotProduct_sum]
  apply sum_congr rfl
  intro B _
  rw [Submodule.coe_smul, dotProduct_smul]
  exact mul_comm _ _

private lemma cycle_eq_of_pairings {M : Matroid V} (u v : topCycles M)
    (h : ∀ B : Passive M,
      dotProduct u.val (normalizedCycle B).val = dotProduct v.val (normalizedCycle B).val) :
    u = v := by
  have he : dotProduct (u - v : topCycles M).val (u - v : topCycles M).val = 0 := by
    rw [dotProduct_cycle_expansion]
    apply sum_eq_zero
    intro B _
    rw [Submodule.coe_sub, sub_dotProduct, h B, sub_self, zero_mul]
  exact sub_eq_zero.mp (Subtype.ext (dotProduct_self_eq_zero.mp he))

private lemma gram_det_ne_zero (M : Matroid V) : (gram M).det ≠ 0 := by
  classical
  let C : Matrix (Finset V) (Passive M) ℤ := fun F B => (normalizedCycle B).val F
  have hC : Function.Injective C.mulVec := by
    intro x y h
    funext B
    have hcoord (v : Passive M → ℤ) : (C.mulVec v) B.val = v B := by
      rw [← fromCoordinates_coord v B, fromCoordinates_apply]
      apply sum_congr rfl
      intro D _
      exact mul_comm _ _
    rw [← hcoord x, ← hcoord y, h]
  have hG : gram M = Cᵀ * C := by
    ext B D
    rw [Matrix.mul_apply]
    rfl
  have hpos : (gram M).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · apply Matrix.IsHermitian.ext
      intro B D
      change dotProduct (normalizedCycle D).val (normalizedCycle B).val = _
      exact dotProduct_comm _ _
    · intro x hx
      rw [hG, ← mulVec_mulVec, star_trivial, dotProduct_mulVec, vecMul_transpose]
      have hn : C.mulVec x ≠ 0 := fun h => hx (hC (h.trans (mulVec_zero C).symm))
      exact lt_of_le_of_ne (sum_nonneg fun i _ => mul_self_nonneg ((C.mulVec x) i))
        (Ne.symm (fun h => hn (dotProduct_self_eq_zero.mp h)))
  exact hpos.det_pos.ne'

/-- The source pairing vector obtained from the signed restrictions at a fixed pivot. -/
noncomputable def pivotPairing {M : Matroid V} (e : V)
    (y : (K : Circuit M) → topCycles (M ／ (K.val : Set V))) (B : Passive M) : ℤ :=
  ∑ K : CircuitThrough M e,
    dotProduct (y ⟨K.val, K.prop.1⟩).val (restrictChain M K.val e (normalizedCycle B).val)

private lemma pivotPairing_aggregate {M : Matroid V} {e : V} (he : e ∈ M.E)
    (z : topCycles M) (y : (K : Circuit M) → topCycles (M ／ (K.val : Set V)))
    (hy : ∀ K : Circuit M, aggregateRestrict M K.val z.val = (y K).val) (B : Passive M) :
    pivotPairing e y B = dotProduct z.val (normalizedCycle B).val := by
  classical
  obtain ⟨E, hE, hinv⟩ := circuit_cycle_decomposition M e he
  have hjoin : (normalizedCycle B).val =
      ∑ K : CircuitThrough M e,
        signedJoin K.val (simplexBoundary K.val) (E (normalizedCycle B) K).val := by
    funext F
    simpa only [E.symm_apply_apply, Finset.sum_apply] using hinv (E (normalizedCycle B)) F
  rw [hjoin, dotProduct_sum, pivotPairing]
  apply sum_congr rfl
  intro K _
  rw [← aggregate_adjoint, hy ⟨K.val, K.prop.1⟩]
  congr 1
  funext T
  exact (by simpa only [restrictChain, restrictionSign] using hE (normalizedCycle B) K T :
    (E (normalizedCycle B) K).val T = restrictChain M K.val e (normalizedCycle B).val T).symm

private lemma exists_gram_solution_iff (M : Matroid V)
    (hG : (gram M).det ≠ 0) (b : Passive M → ℤ) :
    (∃ x : Passive M → ℤ, (gram M).mulVec x = b) ↔
      ∀ B, (gram M).det ∣ ((gram M).adjugate.mulVec b) B := by
  let G := gram M
  change (∃ x, G.mulVec x = b) ↔ ∀ B, G.det ∣ (G.adjugate.mulVec b) B
  constructor
  · rintro ⟨x, rfl⟩ i
    rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
    exact dvd_mul_right _ _
  · intro h
    choose x hx using h
    have hcleared : G.adjugate.mulVec b = G.det • x := funext hx
    have hsolve := G.mulVec_cramer b
    rw [cramer_eq_adjugate_mulVec, hcleared, mulVec_smul] at hsolve
    exact ⟨x, funext fun i => mul_left_cancel₀ hG (congrFun hsolve i)⟩

set_option maxHeartbeats 700000 in
/-- Signed adjointness and the compatibility and Gram divisibility criterion for a unique
integral lift of the joint circuit readouts. The empty passive index set has determinant one. -/
theorem joint_circuit_gram_certificate (M : Matroid V) (e : V) (he : e ∈ M.E) :
    (∀ (K : Circuit M) (z : topCycles M) (w : topCycles (M ／ (K.val : Set V))),
      dotProduct (aggregateRestrict M K.val z.val) w.val =
        dotProduct z.val (signedJoin K.val (simplexBoundary K.val) w.val)) ∧
    (gram M).det ≠ 0 ∧ (IsEmpty (Passive M) → (gram M).det = 1) ∧
    ∀ y : (K : Circuit M) → topCycles (M ／ (K.val : Set V)),
      (∃! z : topCycles M, ∀ K : Circuit M, aggregateRestrict M K.val z.val = (y K).val) ↔
      (∀ (K : Circuit M) (T : Passive (M ／ (K.val : Set V))),
        dotProduct (y K).val (normalizedCycle T).val =
          ∑ B : Passive M, pivotPairing e y B *
            signedJoin K.val (simplexBoundary K.val) (normalizedCycle T).val B.val) ∧
      ∀ B : Passive M, (gram M).det ∣ ((gram M).adjugate.mulVec (pivotPairing e y)) B := by
  classical
  have hdet := gram_det_ne_zero M
  refine ⟨fun _ z w => aggregate_adjoint z.val w, hdet, fun _ => det_isEmpty, ?_⟩
  intro y
  constructor
  · rintro ⟨z, hz, _⟩
    constructor
    · intro K T
      rw [← hz K, aggregate_adjoint,
        dotProduct_cycle_expansion z ⟨_, join_topCycle K.prop (normalizedCycle T).prop⟩]
      exact sum_congr rfl (fun B _ => congrArg (· * _) (pivotPairing_aggregate he z y hz B).symm)
    · apply (exists_gram_solution_iff M hdet (pivotPairing e y)).mp
      refine ⟨fun B => z.val B.val, funext fun B => ?_⟩
      rw [gram_mulVec, fromCoordinates_cycle, dotProduct_comm, pivotPairing_aggregate he z y hz]
  · rintro ⟨hcompat, hdiv⟩
    obtain ⟨x, hx⟩ := (exists_gram_solution_iff M hdet (pivotPairing e y)).mpr hdiv
    let z := fromCoordinates M x
    have hpair (B : Passive M) : dotProduct z.val (normalizedCycle B).val = pivotPairing e y B := by
      rw [dotProduct_comm, ← gram_mulVec, hx]
    refine ⟨z, fun K => ?_, fun w hw => ?_⟩
    · let A : topCycles (M ／ (K.val : Set V)) :=
        ⟨aggregateRestrict M K.val z.val, aggregate_topCycle K.prop z.prop⟩
      apply congrArg Subtype.val (show A = y K from ?_)
      apply cycle_eq_of_pairings
      intro T
      change dotProduct (aggregateRestrict M K.val z.val) (normalizedCycle T).val = _
      rw [aggregate_adjoint, hcompat K T,
        dotProduct_cycle_expansion z ⟨_, join_topCycle K.prop (normalizedCycle T).prop⟩]
      exact sum_congr rfl (fun B _ => congrArg (· * _) (hpair B))
    · apply cycle_eq_of_pairings
      intro B
      rw [hpair, pivotPairing_aggregate he w y hw]

end D5.S3.Combinatorics.Matroids.JointCircuitGramCertificate
