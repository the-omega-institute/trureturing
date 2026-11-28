/- GID: D5/S3/Matrix/QubitProductSectors
   generality: G
   mirror-B: none(waiver:covered-by-pure-gnsextension-sectors-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A common qubit observable algebra with two reference product vacua. -/

import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Algebra.Order.Star.Prod
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Group.Action.Prod
import D5.S3.Matrix.QubitProductOperators
import D5.S3.Topology.InfiniteProducts.TailProducts
import D5.S3.OperatorAlgebra.VectorStateDistance

/-! Omega original.

A common qubit observable algebra with two reference product vacua.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped InnerProductSpace BigOperators ComplexOrder Topology CStarAlgebra
open Filter Set Omega.Analysis.TailProducts

namespace Omega.QubitProduct

/-- Phase-aligned overlaps of the two qubit reference sequences. -/
abbrev Overlaps := ℕ → Set.Icc (0 : ℝ) 1

def overlaps (r : Overlaps) (k : ℕ) : ℝ := r k

private def rotationUnitary (r : Overlaps) (k : ℕ) : unitary (Matrix Bool Bool ℂ) :=
  ⟨rotation (r k), rotation_unitary (r k) (r k).2⟩

private def operatorRotation (r : Overlaps) (k : ℕ) : unitary Operator :=
  ⟨localAction k (rotation (r k)), by
    have h := (rotationUnitary r k).2
    change star (rotation (r k)) * rotation (r k) = 1 ∧
      rotation (r k) * star (rotation (r k)) = 1 at h
    constructor
    · rw [← localAction_star, ← localAction_mul, h.1, localAction_one]
    · rw [← localAction_star, ← localAction_mul, h.2, localAction_one]⟩

private def generator (r : Overlaps) (k : ℕ) (M : Matrix Bool Bool ℂ) :
    Operator × Operator :=
  (localAction k M, localAction k (Unitary.conjStarAlgAut ℂ _ (rotationUnitary r k) M))

private def localAlgebra (r : Overlaps) : StarSubalgebra ℂ (Operator × Operator) :=
  StarAlgebra.adjoin ℂ (Set.range fun p : ℕ × Matrix Bool Bool ℂ => generator r p.1 p.2)

/-- Norm closure of the common algebra of local qubit observables. -/
def pairAlgebra (r : Overlaps) : StarSubalgebra ℂ (Operator × Operator) :=
  (localAlgebra r).topologicalClosure

instance closedPairAlgebra (r : Overlaps) : IsClosed (pairAlgebra r : Set (Operator × Operator)) :=
  StarSubalgebra.isClosed_topologicalClosure _

set_option synthInstance.maxHeartbeats 120000 in
instance orderedPairAlgebra (r : Overlaps) : StarOrderedRing (pairAlgebra r) := by
  let : IsScalarTower ℝ Operator Operator :=
    ⟨fun c a b => by ext x; simp [mul_apply_eq_comp]⟩
  let : SMulCommClass ℝ Operator Operator :=
    ⟨fun c a b => by ext x; simp [mul_apply_eq_comp, ContinuousLinearMap.map_smul_of_tower]⟩
  let : NonnegSpectrumClass ℝ (Operator × Operator) :=
    CStarAlgebra.instNonnegSpectrumClass
  let : NonUnitalClosedEmbeddingContinuousFunctionalCalculus ℂ
      (Operator × Operator) IsStarNormal :=
    IsStarNormal.instNonUnitalContinuousFunctionalCalculus
  let : NonUnitalContinuousFunctionalCalculus ℝ (Operator × Operator) IsSelfAdjoint :=
    by
      exact IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus (A := Operator × Operator)
  let : StarModule ℝ (Operator × Operator) :=
    ⟨fun c a => by
      have hsmul (b : Operator × Operator) : c • b = (c : ℂ) • b := rfl
      rw [hsmul, star_smul, show star c = c from rfl, hsmul]
      simp⟩
  exact Subtype.starOrderedRing (𝕜 := ℂ) (pairAlgebra r)

def firstRep (r : Overlaps) : pairAlgebra r →⋆ₐ[ℂ] Operator :=
  (StarAlgHom.fst ℂ Operator Operator).comp (pairAlgebra r).subtype

def secondRep (r : Overlaps) : pairAlgebra r →⋆ₐ[ℂ] Operator :=
  (StarAlgHom.snd ℂ Operator Operator).comp (pairAlgebra r).subtype

/-- A local observable embedded in the common algebra of the two reference sequences. -/
def site (r : Overlaps) (k : ℕ) (M : Matrix Bool Bool ℂ) : pairAlgebra r :=
  ⟨generator r k M, (StarSubalgebra.le_topologicalClosure _)
    (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self (k, M)))⟩

@[simp] theorem firstRep_site (r : Overlaps) (k : ℕ) (M : Matrix Bool Bool ℂ) :
    firstRep r (site r k M) = localAction k M := rfl

@[simp] theorem secondRep_site (r : Overlaps) (k : ℕ) (M : Matrix Bool Bool ℂ) :
    secondRep r (site r k M) =
      localAction k (rotation (r k) * M * star (rotation (r k))) := rfl

/-- The first vacuum evaluates a product of local observables as the
product of their single-site vacuum expectations. -/
theorem first_vacuum_product (r : Overlaps) (M : ℕ → Matrix Bool Bool ℂ) (s n : ℕ) :
    ⟪basisVector ∅, firstRep r (block (fun k => site r k (M k)) s n)
      (basisVector ∅)⟫_ℂ = ∏ k ∈ Finset.range n, M (s + k) false false := by
  rw [inner_basisVector_left, map_block (firstRep r)]
  simp only [firstRep_site, block_diag, bit, Finset.notMem_empty, decide_false]

/-- The second vacuum evaluates a product of local observables using the
phase-aligned unit ray at each site. -/
theorem second_vacuum_product (r : Overlaps) (M : ℕ → Matrix Bool Bool ℂ) (s n : ℕ) :
    ⟪basisVector ∅, secondRep r (block (fun k => site r k (M k)) s n)
      (basisVector ∅)⟫_ℂ =
      ∏ k ∈ Finset.range n,
        (rotation (r (s + k)) * M (s + k) * star (rotation (r (s + k)))) false false := by
  rw [inner_basisVector_left, map_block (secondRep r)]
  simp only [secondRep_site, block_diag, bit, Finset.notMem_empty, decide_false]

theorem second_vacuum_projection_product (r : Overlaps) (s n : ℕ) :
    ⟪basisVector ∅, secondRep r (block (fun k => site r k vacuumMatrix) s n)
      (basisVector ∅)⟫_ℂ = (tailPrefix (overlaps r) s n ^ 2 : ℝ) := by
  rw [second_vacuum_product]
  simp [tailPrefix, overlaps, conjugate_vacuum_diag, ← Complex.ofReal_prod, Finset.prod_pow]

private theorem secondRep_site_symm (r : Overlaps) (k : ℕ) (M : Matrix Bool Bool ℂ) :
    secondRep r (site r k ((Unitary.conjStarAlgAut ℂ _ (rotationUnitary r k)).symm M)) =
      localAction k M := by
  change localAction k ((Unitary.conjStarAlgAut ℂ _ (rotationUnitary r k))
    ((Unitary.conjStarAlgAut ℂ _ (rotationUnitary r k)).symm M)) = _
  rw [StarAlgEquiv.apply_symm_apply]

private theorem reaches_basis {r : Overlaps} (π : pairAlgebra r →⋆ₐ[ℂ] Operator)
    (hπ : ∀ k M, ∃ a, π a = localAction k M) (S : Configuration) :
    ∃ a : pairAlgebra r, π a (basisVector ∅) = basisVector S := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp [one_apply_eq_self]⟩
  | insert k S hk ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨b, hb⟩ := hπ k flipMatrix
    exact ⟨b * a, by rw [map_mul, mul_apply_eq_comp, ha, hb, flip_basis]; simp [toggle, hk]⟩

private theorem cyclic {r : Overlaps} (π : pairAlgebra r →⋆ₐ[ℂ] Operator)
    (hπ : ∀ k M, ∃ a, π a = localAction k M) :
    DenseRange (fun a : pairAlgebra r => π a (basisVector ∅)) := by
  let orbit : pairAlgebra r →ₗ[ℂ] Carrier :=
    (ContinuousLinearMap.apply ℂ Carrier (basisVector ∅)).toLinearMap.comp π.toLinearMap
  intro x
  change x ∈ closure (Set.range orbit)
  have hs := lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x
  apply mem_closure_of_tendsto hs
  apply Eventually.of_forall
  intro s
  change ∑ S ∈ s, lp.single 2 S (x S) ∈ Set.range orbit
  change ∑ S ∈ s, lp.single 2 S (x S) ∈ LinearMap.range orbit
  apply Submodule.sum_mem
  intro S _
  have hmem : basisVector S ∈ LinearMap.range orbit := reaches_basis π hπ S
  have hm := (LinearMap.range orbit).smul_mem (x S) hmem
  simpa only [basisVector, ← lp.single_smul, smul_eq_mul, mul_one] using hm

theorem first_cyclic (r : Overlaps) :
    DenseRange (fun a : pairAlgebra r => firstRep r a (basisVector ∅)) :=
  cyclic (firstRep r) (fun k M => ⟨site r k M, rfl⟩)

theorem second_cyclic (r : Overlaps) :
    DenseRange (fun a : pairAlgebra r => secondRep r a (basisVector ∅)) :=
  cyclic (secondRep r) (fun k M => ⟨_, secondRep_site_symm r k M⟩)

private theorem vacuum_ray (x : Carrier)
    (hx : ∀ k, localAction k vacuumMatrix x = x) : x = x ∅ • basisVector ∅ := by
  apply lp.ext
  funext S
  by_cases hS : S = ∅
  · subst S; simp [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  have h := congrArg (fun y : Carrier => y S) (hx k)
  have hz : x S = 0 := by
    rw [localAction_vacuum] at h
    simpa [bit, hk] using h.symm
  simp [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hz, Ne.symm hS]

private theorem scalar_commutant {r : Overlaps} (π : pairAlgebra r →⋆ₐ[ℂ] Operator)
    (hπ : ∀ k M, ∃ a, π a = localAction k M) (T : Operator)
    (hT : ∀ a, π a * T = T * π a) : ∃ c : ℂ, T = c • 1 := by
  let Ω := basisVector ∅
  have hfix (k : ℕ) : localAction k vacuumMatrix (T Ω) = T Ω := by
    obtain ⟨a, ha⟩ := hπ k vacuumMatrix
    have he := congrArg (fun P : Operator => P Ω) (hT a)
    change π a (T Ω) = T (π a Ω) at he
    rwa [ha, show localAction k vacuumMatrix Ω = Ω from vacuum_fixed k] at he
  refine ⟨T Ω ∅, operator_ext (fun S => ?_)⟩
  obtain ⟨a, ha⟩ := reaches_basis π hπ S
  have h := congrArg (fun P : Operator => P Ω) (hT a)
  simp only [mul_apply_eq_comp] at h
  rw [← ha, ← h, vacuum_ray _ hfix]
  simp

theorem first_scalar_commutant (r : Overlaps) (T : Operator)
    (hT : ∀ a, firstRep r a * T = T * firstRep r a) : ∃ c : ℂ, T = c • 1 :=
  scalar_commutant (firstRep r) (fun k M => ⟨site r k M, rfl⟩) T hT

theorem second_scalar_commutant (r : Overlaps) (T : Operator)
    (hT : ∀ a, secondRep r a * T = T * secondRep r a) : ∃ c : ℂ, T = c • 1 :=
  scalar_commutant (secondRep r) (fun k M => ⟨_, secondRep_site_symm r k M⟩) T hT


private def rotationBlock (r : Overlaps) (s n : ℕ) : unitary Operator :=
  block (fun k => star (operatorRotation r k)) s n

private theorem coe_rotationBlock (r : Overlaps) (s n : ℕ) :
    (rotationBlock r s n : Operator) = block (fun k => localAction k (star (rotation (r k)))) s n := by
  change (unitary Operator).subtype (block (fun k => star (operatorRotation r k)) s n) = _
  rw [map_block (unitary Operator).subtype]
  congr 1
  funext k
  exact (localAction_star k _).symm

private theorem rotationBlock_norm (r : Overlaps) (s n : ℕ) (x : Carrier) :
    ‖(rotationBlock r s n : Operator) x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (rotationBlock r s n).2 x

private theorem commute_rotationBlocks (r : Overlaps) (n m : ℕ) :
    Commute (rotationBlock r n m : Operator) (rotationBlock r 0 n : Operator) := by
  rw [coe_rotationBlock, coe_rotationBlock]
  induction m with
  | zero => simp
  | succ m ih =>
      rw [block_succ]
      exact (localAction_commute_block (by omega) _ _).mul_left ih

private theorem rotationBlock_sq_dist (r : Overlaps) (s n : ℕ) :
    ‖(rotationBlock r s n : Operator) (basisVector ∅) - basisVector ∅‖ ^ 2 =
      2 * (1 - tailPrefix (overlaps r) s n) := by
  rw [norm_sub_sq (𝕜 := ℂ), rotationBlock_norm, norm_basisVector]
  have hinner : ⟪basisVector ∅, (rotationBlock r s n : Operator) (basisVector ∅)⟫_ℂ =
      (tailPrefix (overlaps r) s n : ℂ) := by
    rw [inner_basisVector_left, coe_rotationBlock, block_diag]
    simp [tailPrefix, overlaps, Complex.ofReal_prod]
  rw [← inner_conj_symm, hinner]
  simp
  ring

private theorem tailRot_dist_le (r : Overlaps) (n m : ℕ) :
    ‖(rotationBlock r 0 (n + m) : Operator) (basisVector ∅) -
        (rotationBlock r 0 n : Operator) (basisVector ∅)‖ ^ 2 ≤
      2 * (∑ k ∈ Finset.range m, (1 - overlaps r (n + k))) := by
  have he : (rotationBlock r 0 (n + m) : Operator) =
      (rotationBlock r n m : Operator) * (rotationBlock r 0 n : Operator) := by
    simp only [coe_rotationBlock]
    rw [block_add, Nat.zero_add]
  rw [he, (commute_rotationBlocks r n m).eq, mul_apply_eq_comp, ← map_sub,
    rotationBlock_norm, rotationBlock_sq_dist]
  exact mul_le_mul_of_nonneg_left
    (one_sub_tailPrefix_le_sum (overlaps r) (fun k => (r k).2) n m) (by norm_num)

private theorem vacuumRotations_cauchy (r : Overlaps)
    (hs : Summable (fun k => 1 - overlaps r k)) :
    CauchySeq (fun n => (rotationBlock r 0 n : Operator) (basisVector ∅)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hc := hs.hasSum.tendsto_sum_nat.cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (ε ^ 2 / 2) (by positivity)
  have hdist (n m : ℕ) (hn : N ≤ n) (hm : n ≤ m) :
      dist ((rotationBlock r 0 m : Operator) (basisVector ∅))
        ((rotationBlock r 0 n : Operator) (basisVector ∅)) < ε := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hsum := hN (n + k) (by omega) n hn
    rw [Real.dist_eq, Finset.sum_range_add] at hsum
    have ht := tailRot_dist_le r n k
    have hle := (abs_lt.mp hsum).2
    rw [dist_eq_norm]
    nlinarith [sq_nonneg (‖(rotationBlock r 0 (n + k) : Operator) (basisVector ∅) -
      (rotationBlock r 0 n : Operator) (basisVector ∅)‖ - ε)]
  refine ⟨N, fun n hn m hm => ?_⟩
  rcases le_total n m with h | h
  · rw [dist_comm]
    exact hdist n m hn h
  · exact hdist m n hm h

private theorem rotationBlock_intertwines_site (r : Overlaps) (n k : ℕ) (hk : k < n)
    (M : Matrix Bool Bool ℂ) :
    (rotationBlock r 0 n : Operator) * (generator r k M).2 =
      (generator r k M).1 * (rotationBlock r 0 n : Operator) := by
  let N := rotation (r k) * M * star (rotation (r k))
  change (rotationBlock r 0 n : Operator) * localAction k N =
    localAction k M * (rotationBlock r 0 n : Operator)
  simp only [coe_rotationBlock]
  induction n with
  | zero => omega
  | succ n ih =>
    rw [block_succ, Nat.zero_add]
    by_cases he : k = n
    · subst n
      have hcomm := localAction_commute_block (k := k) (s := 0) (n := k)
        (Or.inr (by simp)) N (fun j => star (rotation (r j)))
      have hU := (rotation_unitary (r k) (r k).2).1
      have hconj : star (rotation (r k)) * N = M * star (rotation (r k)) := by
        dsimp [N]
        rw [← mul_assoc (star (rotation (r k))) (rotation (r k) * M),
          ← mul_assoc, hU, one_mul]
      rw [mul_assoc, ← hcomm.eq, ← mul_assoc, ← localAction_mul, hconj,
        localAction_mul, mul_assoc]
    · have hcomm := localAction_comm he M (star (rotation (r n)))
      rw [mul_assoc, ih (by omega), ← mul_assoc, ← hcomm.eq, mul_assoc]

private theorem generator_intertwines_eventually (r : Overlaps) (a : Operator × Operator)
    (ha : a ∈ localAlgebra r) :
    ∀ᶠ n : ℕ in atTop, (rotationBlock r 0 n : Operator) * a.2 =
      a.1 * (rotationBlock r 0 n : Operator) := by
  unfold localAlgebra at ha
  induction ha using StarAlgebra.adjoin_induction with
  | mem b hb =>
    obtain ⟨⟨k, M⟩, rfl⟩ := hb
    filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    exact rotationBlock_intertwines_site r n k (by omega) M
  | algebraMap c => exact Eventually.of_forall fun n => by simp [Algebra.commutes]
  | add b c _ _ hb hc =>
    filter_upwards [hb, hc] with n hbn hcn
    simp [mul_add, add_mul, hbn, hcn]
  | mul b c _ _ hb hc =>
    filter_upwards [hb, hc] with n hbn hcn
    simp only [Prod.snd_mul, Prod.fst_mul, ← mul_assoc, hbn]
    rw [mul_assoc b.1, hcn, ← mul_assoc]
  | star b _ hb =>
    filter_upwards [hb] with n hn
    let U : Operator := rotationBlock r 0 n
    have hu : star U * U = 1 := (rotationBlock r 0 n).2.1
    have hv : U * star U = 1 := (rotationBlock r 0 n).2.2
    have h := congrArg star hn
    rw [star_mul, star_mul] at h
    change star b.2 * star U = star U * star b.1 at h
    change U * star b.2 = star b.1 * U
    calc
      U * star b.2 = U * (star b.2 * star U) * U := by rw [mul_assoc, mul_assoc, hu, mul_one]
      _ = star b.1 * U := by rw [h, ← mul_assoc U, hv, one_mul]

/-- Summable overlap deficits produce a unit vector in the first representation
whose expectation is the second product vacuum state. -/
theorem equivalent_vacuum (r : Overlaps) (hs : Summable (fun k => 1 - overlaps r k)) :
    ∃ v : Carrier, ‖v‖ = 1 ∧ ∀ a : pairAlgebra r,
      ⟪v, firstRep r a v⟫_ℂ = ⟪basisVector ∅, secondRep r a (basisVector ∅)⟫_ℂ := by
  let Ω := basisVector ∅
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete (vacuumRotations_cauchy r hs)
  refine ⟨v, ?_, ?_⟩
  · exact tendsto_nhds_unique hv.norm
      (by simpa only [rotationBlock_norm, norm_basisVector] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  · let f : Operator × Operator → ℂ := fun a => ⟪v, a.1 v⟫_ℂ
    let g : Operator × Operator → ℂ := fun a => ⟪Ω, a.2 Ω⟫_ℂ
    have hclosed : IsClosed {a | f a = g a} := isClosed_eq (by fun_prop) (by fun_prop)
    suffices hsub : (localAlgebra r : Set (Operator × Operator)) ⊆ {a | f a = g a} by
      intro a
      exact (closure_minimal hsub hclosed) a.2
    intro a ha
    have hSeq := hv.inner (𝕜 := ℂ) ((a.1.continuous.tendsto v).comp hv)
    have hconst : Tendsto (fun n => ⟪(rotationBlock r 0 n : Operator) Ω,
        a.1 ((rotationBlock r 0 n : Operator) Ω)⟫_ℂ) atTop (𝓝 (g a)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [generator_intertwines_eventually r a ha] with n hn
      rw [← mul_apply_eq_comp, ← hn, mul_apply_eq_comp]
      exact (Unitary.inner_map_map (rotationBlock r 0 n) Ω (a.2 Ω)).symm
    exact tendsto_nhds_unique hSeq hconst
/-- Divergent overlap deficits force every bounded intertwiner to vanish. -/
theorem intertwiner_zero_of_not_summable (r : Overlaps)
    (hs : ¬ Summable (fun k => 1 - overlaps r k)) (T : Operator)
    (hT : ∀ a x, T (firstRep r a x) = secondRep r a (T x)) : T = 0 := by
  let w := T (basisVector ∅)
  let M (k : ℕ) := rotation (r k) * vacuumMatrix * star (rotation (r k))
  have hfix (k : ℕ) : localAction k (M k) w = w := by
    simpa only [firstRep_site, secondRep_site, vacuum_fixed, M, w] using
      (hT (site r k vacuumMatrix) (basisVector ∅)).symm
  have hMstar (k : ℕ) : star (M k) = M k := by
    simp only [M, star_mul, star_star, vacuumMatrix_star, mul_assoc]
  have hMproj (k : ℕ) : M k * M k = M k := by
    have hu := Unitary.star_mul_self_of_mem (rotation_unitary (r k) (r k).2)
    let U := rotation (r k)
    change (U * vacuumMatrix * star U) * (U * vacuumMatrix * star U) = _
    calc
      _ = U * vacuumMatrix * (star U * U) * vacuumMatrix * star U := by noncomm_ring
      _ = M k := by rw [show star U * U = 1 from hu, mul_one,
        mul_assoc U vacuumMatrix vacuumMatrix, vacuumMatrix_mul]
  have hw : w = 0 := by
    apply lp.ext
    funext S
    let s := S.sup id + 1
    have hbit (k : ℕ) : bit (s + k) S = false := by
      have hm : s + k ∉ S := by
        intro h
        have hle := Finset.le_sup (f := id) h
        dsimp [id, s] at *
        omega
      simp [bit, hm]
    let P : ℕ → Operator := block (fun k => localAction k (M k)) s
    have hp_succ (n : ℕ) : P (n + 1) = localAction (s + n) (M (s + n)) * P n := rfl
    have hPfix (n : ℕ) : P n w = w := by
      induction n with
      | zero => simp [P, one_apply_eq_self]
      | succ n ih => rw [hp_succ, mul_apply_eq_comp, ih, hfix]
    have hPcomm (n : ℕ) : Commute (localAction (s + n) (M (s + n))) (P n) :=
      localAction_commute_block (Or.inr le_rfl) _ _
    have hPstar (n : ℕ) : star (P n) = P n := by
      induction n with
      | zero => simp [P]
      | succ n ih =>
        rw [hp_succ, star_mul, ← localAction_star, hMstar, ih]
        exact (hPcomm n).eq.symm
    have hPproj (n : ℕ) : P n * P n = P n := by
      induction n with
      | zero => simp [P]
      | succ n ih =>
        rw [hp_succ, (hPcomm n).symm.mul_mul_mul_comm, ih, ← localAction_mul, hMproj]
    have hnorm (n : ℕ) : ‖P n (basisVector S)‖ ^ 2 = tailPrefix (overlaps r) s n ^ 2 := by
      rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
        ← ContinuousLinearMap.star_eq_adjoint, hPstar, ← ContinuousLinearMap.mul_def,
        hPproj, inner_basisVector_left]
      change (block (fun k => localAction k (M k)) s n (basisVector S) S).re = _
      rw [block_diag, tailPrefix, ← Finset.prod_pow]
      simp only [M, hbit, conjugate_vacuum_diag, Bool.false_eq_true, ite_false, overlaps,
        ← Complex.ofReal_prod, Complex.ofReal_re]
    have hp : ∀ k, overlaps r k ∈ Set.Icc (0 : ℝ) 1 := fun k => (r k).2
    have hlim := ((tailPrefix_tendsto (overlaps r) hp s).pow 2).mul_const (‖w‖ ^ 2)
    rw [tailProduct_eq_zero_of_not_summable (overlaps r) hp hs s, zero_pow (by decide), zero_mul] at hlim
    have hbound (n : ℕ) : ‖w S‖ ^ 2 ≤ tailPrefix (overlaps r) s n ^ 2 * ‖w‖ ^ 2 := by
      have heq : inner ℂ (P n (basisVector S)) w = w S := by
        rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
          hPstar, hPfix, inner_basisVector_left]
      rw [← heq, ← hnorm, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
    have hz : ‖w S‖ ^ 2 ≤ 0 := ge_of_tendsto' hlim hbound
    change w S = 0
    exact norm_eq_zero.mp (by nlinarith only [hz])
  apply ContinuousLinearMap.ext
  intro x
  have heq := (first_cyclic r).equalizer T.continuous (continuous_const (y := (0 : Carrier)))
    (show T ∘ (fun a : pairAlgebra r => firstRep r a (basisVector ∅)) = _ by
      funext a
      change T (firstRep r a (basisVector ∅)) = 0
      rw [hT, show T (basisVector ∅) = 0 from hw, map_zero])
  exact congrFun heq x


/-- The norm limit of the finite pure-state distances bounds every vacuum expectation test. -/
theorem vacuum_distance_upper (r : Overlaps) (a : pairAlgebra r) :
    ‖⟪basisVector ∅, firstRep r a (basisVector ∅)⟫_ℂ -
      ⟪basisVector ∅, secondRep r a (basisVector ∅)⟫_ℂ‖ ≤
      2 * Real.sqrt (1 - tailProduct (overlaps r) 0 ^ 2) * ‖a‖ := by
  let Ω := basisVector ∅
  let C := 2 * Real.sqrt (1 - tailProduct (overlaps r) 0 ^ 2)
  let lhs (b : Operator × Operator) := ‖⟪Ω, b.1 Ω⟫_ℂ - ⟪Ω, b.2 Ω⟫_ℂ‖
  have hclosed : IsClosed {b : Operator × Operator | lhs b ≤ C * ‖b‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  suffices hsub : (localAlgebra r : Set (Operator × Operator)) ⊆
      {b : Operator × Operator | lhs b ≤ C * ‖b‖} by
    exact (closure_minimal hsub hclosed) a.2
  intro b hb
  change lhs b ≤ C * ‖b‖
  have hp := tailPrefix_tendsto (overlaps r) (fun k => (r k).2) 0
  have hlim : Tendsto (fun n => 2 * Real.sqrt (1 - tailPrefix (overlaps r) 0 n ^ 2) * ‖b‖)
      atTop (𝓝 (C * ‖b‖)) := by
    exact (((tendsto_const_nhds.sub (hp.pow 2)).sqrt).const_mul 2).mul_const ‖b‖
  apply ge_of_tendsto hlim
  filter_upwards [generator_intertwines_eventually r b hb] with n hn
  let W := rotationBlock r 0 n
  let v := (W : Operator) Ω
  have hinner : ⟪Ω, v⟫_ℂ = (tailPrefix (overlaps r) 0 n : ℂ) := by
    rw [inner_basisVector_left]
    change ((rotationBlock r 0 n : Operator) Ω) ∅ = _
    rw [coe_rotationBlock, block_diag]
    simp [tailPrefix, overlaps, Complex.ofReal_prod]
  have hnorm : ‖v‖ = 1 := by
    change ‖(rotationBlock r 0 n : Operator) Ω‖ = 1
    rw [rotationBlock_norm, norm_basisVector]
  have hcoeff : ⟪Ω, b.2 Ω⟫_ℂ = ⟪v, b.1 v⟫_ℂ := by
    change _ = ⟪(W : Operator) Ω, b.1 ((W : Operator) Ω)⟫_ℂ
    rw [← mul_apply_eq_comp, ← hn, mul_apply_eq_comp]
    exact (Unitary.inner_map_map W Ω (b.2 Ω)).symm
  dsimp [lhs]
  rw [hcoeff]
  exact (Omega.OperatorAlgebra.VectorStateDistance.norm_expectation_sub_le Ω v
    (norm_basisVector _) hnorm _ hinner b.1).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le b) (by positivity))

end Omega.QubitProduct
