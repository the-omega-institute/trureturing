/- GID: D5/S3/Combinatorics/Graph/KyFanGap/BlowUp
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/KyFanGap/BlowUp
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Basic]
   utility: none
   digest: Blow-up lower bounds and convergence of normalized graph Ky Fan maxima. -/

import D5.S3.Combinatorics.Graph.KyFanGap.Upper
import Mathlib.Analysis.SpecificLimits.Basic

/-! Independent-class blow-ups and their normalized asymptotic maximum. -/

noncomputable section

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators InnerProductSpace
open Filter Topology

namespace D5.S3.Combinatorics.Graph.KyFanGap

private theorem kyFan_prefix_mono {k l n : ℕ} (hkl : k ≤ l)
    (A : Matrix (Fin n) (Fin n) ℝ) : kyFan k A ≤ kyFan l A := by
  simp only [kyFan, D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.kyFanSum,
    Fin.sum_univ_eq_sum_range]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkl)
    (by intros; exact (Matrix.toEuclideanLin A).singularValues_nonneg _)

private theorem kyFan_min_dimension {k n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    kyFan (min k n) A = kyFan k A := by
  by_cases h : k ≤ n
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega)]
    exact (kyFan_eq_of_ge (by omega) A).symm

private theorem sum_fin_product {m t : ℕ} (f : Fin m × Fin t → ℝ) :
    (∑ a : Fin (m * t), f (finProdFinEquiv.symm a)) = ∑ i, ∑ j, f (i, j) := by
  rw [← Fintype.sum_prod_type]
  exact Equiv.sum_comp finProdFinEquiv.symm f

def blowUpMatrix {m t : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (m * t)) (Fin (m * t)) ℝ :=
  fun i j => A (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1

private def replicateVector {m : ℕ} (t : ℕ) (v : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin (m * t)) :=
  WithLp.toLp 2 (fun a => v (finProdFinEquiv.symm a).1 / Real.sqrt t)

private theorem replicate_inner {m t : ℕ} (ht : 1 ≤ t)
    (v w : EuclideanSpace ℝ (Fin m)) :
    ⟪replicateVector t v, replicateVector t w⟫_ℝ = ⟪v, w⟫_ℝ := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  simp only [PiLp.inner_apply, Real.inner_apply, replicateVector]
  rw [sum_fin_product (fun z : Fin m × Fin t =>
    v z.1 / Real.sqrt t * (w z.1 / Real.sqrt t))]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt ht0.le]
  field_simp [ne_of_gt ht0]

private theorem replicate_matrix {m t : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) :
    Matrix.toEuclideanLin (blowUpMatrix (t := t) A) (replicateVector t v) =
      (t : ℝ) • replicateVector t (Matrix.toEuclideanLin A v) := by
  ext a
  change (∑ b, A (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm b).1 *
    (v (finProdFinEquiv.symm b).1 / Real.sqrt t)) =
      (t : ℝ) * ((∑ j, A (finProdFinEquiv.symm a).1 j * v j) / Real.sqrt t)
  rw [sum_fin_product (fun z : Fin m × Fin t =>
    A (finProdFinEquiv.symm a).1 z.1 * (v z.1 / Real.sqrt t))]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    _ = (∑ i, (t : ℝ) * (A (finProdFinEquiv.symm a).1 i * v i)) / Real.sqrt t := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [← Finset.mul_sum]
      ring

private def replicateWitness {k m t : ℕ} (ht : 1 ≤ t) (W : SignedWitness k m) :
    SignedWitness k (m * t) where
  vectors i := replicateVector t (W.vectors i)
  orthonormal_vectors := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [replicate_inner ht]
    exact orthonormal_iff_ite.mp W.orthonormal_vectors i j
  signs := W.signs
  signs_sq := W.signs_sq

private theorem replicate_pairing {k m t : ℕ} (ht : 1 ≤ t)
    (W : SignedWitness k m) (A : Matrix (Fin m) (Fin m) ℝ) :
    signedPairing (replicateWitness ht W) (blowUpMatrix (t := t) A) =
      (t : ℝ) * signedPairing W A := by
  simp only [signedPairing, replicateWitness]
  simp_rw [replicate_matrix, inner_smul_right, replicate_inner ht]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem blowUpAdjMatrix {m t : ℕ} (G : SimpleGraph (Fin m)) :
    (blowUpMatrix (t := t) (G.adjMatrix ℝ)).IsAdjMatrix where
  zero_or_one i j := (G.isAdjMatrix_adjMatrix ℝ).zero_or_one _ _
  symm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact (G.isSymm_adjMatrix (α := ℝ)).apply _ _
  apply_diag i := (G.isAdjMatrix_adjMatrix ℝ).apply_diag _

theorem kyFan_blowUp_le_xi {k m t : ℕ} (ht : 1 ≤ t)
    (G : SimpleGraph (Fin m)) :
    (t : ℝ) * kyFan k (G.adjMatrix ℝ) ≤ xi k (m * t) := by
  classical
  obtain ⟨W, hW⟩ := exists_signed_pairing_eq_kyFan (Nat.min_le_right k m) (G.adjMatrix ℝ)
    (G.isSymm_adjMatrix (α := ℝ))
  have hsymm := (blowUpAdjMatrix (t := t) G).symm
  have h := signed_pairing_le_kyFan (replicateWitness ht W)
    (blowUpMatrix (t := t) (G.adjMatrix ℝ)) hsymm
  rw [replicate_pairing ht, hW, kyFan_min_dimension] at h
  refine (h.trans (kyFan_prefix_mono (Nat.min_le_left k m) _)).trans ?_
  let H := (blowUpAdjMatrix (t := t) G).toGraph
  have hH : H.adjMatrix ℝ = blowUpMatrix (t := t) (G.adjMatrix ℝ) :=
    (blowUpAdjMatrix (t := t) G).adjMatrix_toGraph_eq
  rw [← hH]
  exact Finset.le_sup' (fun H : SimpleGraph (Fin (m * t)) => kyFan k (H.adjMatrix ℝ))
    (Finset.mem_univ H)

private def padVector {m n : ℕ} (e : Fin m ↪ Fin n)
    (v : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin n) :=
  ∑ i, v i • EuclideanSpace.single (e i) 1

private theorem pad_inner {m n : ℕ} (e : Fin m ↪ Fin n)
    (v w : EuclideanSpace ℝ (Fin m)) :
    ⟪padVector e v, padVector e w⟫_ℝ = ⟪v, w⟫_ℝ := by
  have hv := (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin n)).comp e e.injective
  simpa [padVector, PiLp.inner_apply, Real.inner_apply, mul_comm] using
    hv.inner_sum (fun i => v i) (fun i => w i) Finset.univ

private theorem inner_matrix_single {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    ⟪EuclideanSpace.single i 1,
      Matrix.toEuclideanLin A (EuclideanSpace.single j 1)⟫_ℝ = A i j := by
  rw [EuclideanSpace.inner_single_left]
  simp only [map_one, one_mul]
  change Matrix.mulVec A (Pi.single j 1) i = A i j
  rw [Matrix.mulVec_single_one]
  rfl

private theorem pad_quadratic {m n : ℕ} (e : Fin m ↪ Fin n)
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hAB : ∀ i j, B (e i) (e j) = A i j) (v : EuclideanSpace ℝ (Fin m)) :
    ⟪padVector e v, Matrix.toEuclideanLin B (padVector e v)⟫_ℝ =
      ⟪v, Matrix.toEuclideanLin A v⟫_ℝ := by
  simp only [padVector, map_sum, map_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, inner_matrix_single, hAB,
    conj_trivial]
  simp only [PiLp.inner_apply, Real.inner_apply]
  change (∑ i, v i * (∑ j, v j * A j i)) =
    ∑ i, v i * (∑ j, A i j * v j)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private def padWitness {k m n : ℕ} (e : Fin m ↪ Fin n) (W : SignedWitness k m) :
    SignedWitness k n where
  vectors i := padVector e (W.vectors i)
  orthonormal_vectors := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [pad_inner]
    exact orthonormal_iff_ite.mp W.orthonormal_vectors i j
  signs := W.signs
  signs_sq := W.signs_sq

set_option maxHeartbeats 800000 in
private theorem kyFan_le_xi_of_embedding {k m n : ℕ}
    (e : Fin m ↪ Fin n) (G : SimpleGraph (Fin m)) :
    kyFan k (G.adjMatrix ℝ) ≤ xi k n := by
  classical
  let H := G.map e
  obtain ⟨W, hW⟩ := exists_signed_pairing_eq_kyFan (Nat.min_le_right k m) (G.adjMatrix ℝ)
    (G.isSymm_adjMatrix (α := ℝ))
  have h := signed_pairing_le_kyFan (padWitness e W) (H.adjMatrix ℝ)
    (H.isSymm_adjMatrix (α := ℝ))
  have hp : signedPairing (padWitness e W) (H.adjMatrix ℝ) =
      signedPairing W (G.adjMatrix ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    apply pad_quadratic
    intro a b
    simp [H, SimpleGraph.adjMatrix_apply]
  rw [hp, hW, kyFan_min_dimension] at h
  refine (h.trans (kyFan_prefix_mono (Nat.min_le_left k m) _)).trans ?_
  convert (Finset.le_sup' (fun J : SimpleGraph (Fin n) =>
    letI : DecidableRel J.Adj := Classical.decRel _
    kyFan k (J.adjMatrix ℝ)) (Finset.mem_univ H)) using 1
  · congr 1
    ext a b
    by_cases hab : H.Adj a b <;> simp [SimpleGraph.adjMatrix_apply, hab]
  · rfl

theorem xi_mono {k m n : ℕ} (hmn : m ≤ n) : xi k m ≤ xi k n := by
  classical
  apply Finset.sup'_le
  intro G hG
  exact kyFan_le_xi_of_embedding (Fin.castLEEmb hmn) G

theorem xi_blowUp {k m t : ℕ} (ht : 1 ≤ t) :
    (t : ℝ) * xi k m ≤ xi k (m * t) := by
  classical
  obtain ⟨G, hG, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun G : SimpleGraph (Fin m) => kyFan k (G.adjMatrix ℝ))
  change xi k m = kyFan k (G.adjMatrix ℝ) at hmax
  rw [hmax]
  exact kyFan_blowUp_le_xi ht G

def normalizedSupremum (k : ℕ) : ℝ :=
  ⨆ m : ℕ, xi k (m + k) / (m + k)

private theorem xi_le_upper (k n : ℕ) : xi k n ≤ (1 + Real.sqrt k) * n / 2 := by
  classical
  apply Finset.sup'_le
  intro G hG
  exact kyFan_le_of_zero_one (G.adjMatrix ℝ) (G.isSymm_adjMatrix (α := ℝ))
    (G.isAdjMatrix_adjMatrix ℝ).zero_or_one

private theorem normalized_value_le {k n : ℕ} (hn : 0 < n) :
    xi k n / n ≤ (1 + Real.sqrt k) / 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ hn0).2
  convert xi_le_upper k n using 1 <;> ring

private theorem normalized_bddAbove {k : ℕ} (hk : 1 ≤ k) :
    BddAbove (Set.range (fun m : ℕ => xi k (m + k) / (m + k))) := by
  refine ⟨(1 + Real.sqrt k) / 2, ?_⟩
  rintro _ ⟨m, rfl⟩
  simpa only [Nat.cast_add] using (normalized_value_le (k := k) (n := m + k) (by omega))

private theorem floor_ratio_identity {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (x : ℝ) :
    (1 - ((n % m : ℕ) : ℝ) / n) * (x / m) = ((n / m : ℕ) : ℝ) * x / n := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h : ((n % m : ℕ) : ℝ) + (m : ℝ) * ((n / m : ℕ) : ℝ) = n := by
    exact_mod_cast Nat.mod_add_div n m
  field_simp [hm0, hn0]
  nlinarith [congrArg (fun y : ℝ => y * x) h]

private theorem xi_floor_lower {k m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    (1 - ((n % m : ℕ) : ℝ) / n) * (xi k m / m) ≤ xi k n / n := by
  have ht : 1 ≤ n / m := (Nat.le_div_iff_mul_le hm).2 (by simpa using hmn)
  have h := (xi_blowUp (k := k) ht).trans (xi_mono (Nat.mul_div_le n m))
  rw [floor_ratio_identity hm (hm.trans_le hmn)]
  exact div_le_div_of_nonneg_right h (by positivity)

theorem tendsto_xi_div {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => xi k n / n) atTop (nhds (normalizedSupremum k)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨j, hj⟩ := exists_lt_of_lt_ciSup ha
    let m := j + k
    have hm : 0 < m := by omega
    have hg : Tendsto (fun n : ℕ =>
        (1 - ((n % m : ℕ) : ℝ) / n) * (xi k m / m)) atTop
        (nhds (xi k m / m)) := by
      convert (tendsto_const_nhds.sub (tendsto_mod_div_atTop_nhds_zero_nat hm)).mul
        (tendsto_const_nhds (x := xi k m / m)) using 1 <;> simp
    have hj' : a < xi k m / m := by simpa [m, Nat.cast_add] using hj
    have hag := (tendsto_order.mp hg).1 a hj'
    filter_upwards [hag, eventually_ge_atTop m] with n hn hmn
    exact hn.trans_le (xi_floor_lower hm hmn)
  · intro a ha
    filter_upwards [eventually_ge_atTop k] with n hn
    have h := le_ciSup (normalized_bddAbove hk) (n - k)
    have he : n - k + k = n := Nat.sub_add_cancel hn
    have h' : xi k n / n ≤ normalizedSupremum k := by
      simpa only [normalizedSupremum, ← Nat.cast_add, he] using h
    exact h'.trans_lt ha

end D5.S3.Combinatorics.Graph.KyFanGap
