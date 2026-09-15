/- GID: D5/S3/Observer/Monodromy/TransvectionLieGeneration
   generality: G
   mirror-B: D5/B/S3/Observer/Monodromy/TransvectionLieGeneration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Connected transvection frames generate the full skew-adjoint Lie algebra; stars have cubic certificates. -/

import D5.S3.Observer.Monodromy.TraceSymplecticCertificate
import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# Constructive Lie generation from a transvection pairing graph

The matrices are the actual increments of TransvectionTraceReconstruction.
Pairing-graph reachability generates every symmetric dyad multiplied by H.
For nondegenerate alternating H, these span the standard Mathlib Lie algebra
`skewAdjointMatricesLieSubalgebra H`. A star has explicit bracket-length-three
certificates even when some leaf-leaf pairings vanish.

This is a constructive specialization of classical transvection-generation
methods, not a new solution of the order-two Fano monodromy problem. It removes
a generation assumption for a verified lift; it does not construct that lift.
Yelton, arXiv:1703.10917v5, Proposition 3.1 and Remark 3.4, is prior art for
connected pairing graphs and diameter-dependent generation in an l-adic setting.
The Zariski-closure consequence in characteristic zero is proved in the theory
text and is not a theorem about algebraic groups exported by this Lean module.
-/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Monodromy.TransvectionLieGeneration

open D5.S3.Observer.Monodromy.TransvectionTraceReconstruction

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- The actual symmetric dyad `(E_ij + E_ji) H`, also defined for i=j. -/
def cross (H : Matrix I I K) (i j : I) : Matrix I I K :=
  fun r c => (if r = i then H j c else 0) + (if r = j then H i c else 0)

/-- Edges are nonzero entries of the actual pairing matrix. -/
def PairingConnected (H : Matrix I I K) : Prop :=
  ∀ i j, Relation.ReflTransGen (fun u v => H u v ≠ 0) i j

/-- The standard, unbounded Lie closure of the actual generator set. -/
def generated (H : Matrix I I K) : LieSubalgebra K (Matrix I I K) :=
  LieSubalgebra.lieSpan K (Matrix I I K) (Set.range (increment H))

@[simp] theorem cross_self (H : Matrix I I K) (i : I) :
    cross H i i = (2 : K) • increment H i := by
  ext r c
  by_cases h : r = i <;> simp [cross, increment, h, two_mul]

theorem cross_symm (H : Matrix I I K) (i j : I) :
    cross H i j = cross H j i := by
  ext r c
  simp [cross, add_comm]

private theorem product_entry (H : Matrix I I K) (i j r c : I) :
    (increment H i * increment H j) r c =
      if r = i then H i j * H j c else 0 := by
  classical
  by_cases h : r = i
  · subst r
    simp [Matrix.mul_apply, increment]
  · simp [Matrix.mul_apply, increment, h]

/-- An edge gives the corresponding cross direction in one commutator. -/
theorem bracket_increment (H : Matrix I I K)
    (hs : ∀ i j, H i j = -H j i) (i j : I) :
    ⁅increment H i, increment H j⁆ = H i j • cross H i j := by
  change increment H i * increment H j - increment H j * increment H i = _
  ext r c
  simp only [Matrix.sub_apply, product_entry, Matrix.smul_apply, smul_eq_mul, cross]
  rw [hs j i]
  split_ifs <;> ring

private theorem cross_mul_increment (H : Matrix I I K) (i j k r c : I) :
    (cross H i j * increment H k) r c =
      (if r = i then H j k * H k c else 0) +
      (if r = j then H i k * H k c else 0) := by
  classical
  simp [Matrix.mul_apply, cross, increment, add_mul, Finset.sum_add_distrib]

private theorem increment_mul_cross (H : Matrix I I K) (i j k r c : I) :
    (increment H k * cross H i j) r c =
      if r = k then H k i * H j c + H k j * H i c else 0 := by
  classical
  by_cases h : r = k
  · subst r
    simp [Matrix.mul_apply, cross, increment, mul_add, Finset.sum_add_distrib]
  · simp [Matrix.mul_apply, increment, h]

/-- The transport identity propagating an observable cross direction along an edge. -/
theorem bracket_cross_increment (H : Matrix I I K)
    (hs : ∀ i j, H i j = -H j i) (i j k : I) :
    ⁅cross H i j, increment H k⁆ =
      H j k • cross H i k + H i k • cross H j k := by
  change cross H i j * increment H k - increment H k * cross H i j = _
  ext r c
  simp only [Matrix.sub_apply, cross_mul_increment, increment_mul_cross,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, cross]
  rw [hs k i, hs k j]
  split_ifs <;> ring

private theorem cross_mem_of_edge (H : Matrix I I K)
    (hs : ∀ i j, H i j = -H j i)
    (L : LieSubalgebra K (Matrix I I K))
    (hN : ∀ i, increment H i ∈ L) (i j : I) (hij : H i j ≠ 0) :
    cross H i j ∈ L := by
  have h := L.smul_mem (H i j)⁻¹ (L.lie_mem (hN i) (hN j))
  rwa [bracket_increment H hs, smul_smul, inv_mul_cancel₀ hij, one_smul] at h

/-- A path in the actual pairing graph gives a Lie word expression for its endpoints.
No nondegeneracy or common anchor is needed in this propagation theorem. -/
theorem cross_mem_of_reachable (H : Matrix I I K)
    (hs : ∀ i j, H i j = -H j i)
    (L : LieSubalgebra K (Matrix I I K))
    (hN : ∀ i, increment H i ∈ L) {i j : I}
    (hpath : Relation.ReflTransGen (fun u v => H u v ≠ 0) i j) :
    cross H i j ∈ L := by
  induction hpath with
  | refl =>
      rw [cross_self]
      exact L.smul_mem 2 (hN i)
  | @tail j k _ hjk ih =>
      have hedge := cross_mem_of_edge H hs L hN j k hjk
      have hstep := L.sub_mem (L.lie_mem ih (hN k))
        (L.smul_mem (H i k) hedge)
      rw [bracket_cross_increment H hs, add_sub_cancel_right] at hstep
      have h := L.smul_mem (H j k)⁻¹ hstep
      rwa [smul_smul, inv_mul_cancel₀ hjk, one_smul] at h

/-- Symmetric matrices have a concrete half-sum decomposition into the cross matrices. -/
theorem symmetric_cross_expansion (H S : Matrix I I K)
    (hS : ∀ i j, S i j = S j i) (h2 : (2 : K) ≠ 0) :
    (∑ i, ∑ j, (S i j / 2) • cross H i j) = S * H := by
  classical
  ext r c
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, cross,
    mul_add, Finset.sum_add_distrib]
  have hleft : (∑ i, ∑ j, (S i j / 2) * (if r = i then H j c else 0)) =
      ∑ j, (S r j / 2) * H j c := by
    rw [Finset.sum_comm]
    simp [mul_ite]
  have hright : (∑ i, ∑ j, (S i j / 2) * (if r = j then H i c else 0)) =
      ∑ i, (S i r / 2) * H i c := by simp [mul_ite]
  rw [hleft, hright, ← Finset.sum_add_distrib, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hS i r]
  field_simp [h2]
  <;> ring

private theorem increment_mem_skew (H : Matrix I I K)
    (hs : ∀ i j, H i j = -H j i) (i : I) :
    increment H i ∈ skewAdjointMatricesLieSubalgebra H := by
  change (increment H i).transpose * H = H * (-increment H i)
  ext r c
  simp only [Matrix.mul_neg, Matrix.neg_apply]
  have hl : ((increment H i).transpose * H) r c = H i r * H i c := by
    simp [Matrix.mul_apply, Matrix.transpose_apply, increment]
  have hr : (H * increment H i) r c = H r i * H i c := by
    simp [Matrix.mul_apply, increment]
  rw [hl, hr, hs r i]
  ring

private theorem skew_has_symmetric_factor (H X : Matrix I I K)
    (hs : ∀ i j, H i j = -H j i) (hdet : H.det ≠ 0)
    (hX : X ∈ skewAdjointMatricesLieSubalgebra H) :
    ∃ S : Matrix I I K, (∀ i j, S i j = S j i) ∧ X = S * H := by
  have hu : IsUnit H.det := isUnit_iff_ne_zero.mpr hdet
  have hHI : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hu
  have hIH : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hu
  have ht : H.transpose = -H := by
    ext i j
    exact hs j i
  have hqmul : (H⁻¹).transpose * H = -1 := by
    have he := congrArg Matrix.transpose hHI
    have he' : -((H⁻¹).transpose * H) = 1 := by
      simpa only [Matrix.transpose_mul, ht, Matrix.mul_neg, Matrix.transpose_one] using he
    exact neg_eq_iff_eq_neg.mp he'
  have hq : (H⁻¹).transpose = -H⁻¹ := by
    calc
      (H⁻¹).transpose = ((H⁻¹).transpose * H) * H⁻¹ := by
        rw [Matrix.mul_assoc, hHI, Matrix.mul_one]
      _ = -H⁻¹ := by rw [hqmul]; simp
  change X.transpose * H = H * (-X) at hX
  have hcomm : H⁻¹ * X.transpose = -(X * H⁻¹) := by
    calc
      H⁻¹ * X.transpose = (H⁻¹ * X.transpose) * (H * H⁻¹) := by
        rw [hHI, Matrix.mul_one]
      _ = H⁻¹ * (X.transpose * H) * H⁻¹ := by simp only [Matrix.mul_assoc]
      _ = H⁻¹ * (H * (-X)) * H⁻¹ := by rw [hX]
      _ = (H⁻¹ * H) * (-X) * H⁻¹ := by simp only [Matrix.mul_assoc]
      _ = -(X * H⁻¹) := by rw [hIH]; simp
  have hsym : (X * H⁻¹).transpose = X * H⁻¹ := by
    rw [Matrix.transpose_mul, hq, Matrix.neg_mul, hcomm, neg_neg]
  refine ⟨X * H⁻¹, ?_, ?_⟩
  · intro i j
    exact (congrArg (fun M : Matrix I I K => M i j) hsym).symm
  · rw [Matrix.mul_assoc, hIH, Matrix.mul_one]

/-- Connectedness and the actual determinant suffice for full Lie generation.
The conclusion is equality with Mathlib's genuine skew-adjoint Lie subalgebra. -/
theorem generated_eq_skewAdjoint (H : Matrix I I K)
    (hs : ∀ i j, H i j = -H j i)
    (hdet : H.det ≠ 0) (h2 : (2 : K) ≠ 0)
    (hconnected : PairingConnected H) :
    generated H = skewAdjointMatricesLieSubalgebra H := by
  apply le_antisymm
  · apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    exact increment_mem_skew H hs i
  · intro X hX
    obtain ⟨S, hS, hXS⟩ := skew_has_symmetric_factor H X hs hdet hX
    rw [hXS, ← symmetric_cross_expansion H S hS h2]
    apply (generated H).toSubmodule.sum_mem
    intro i _
    apply (generated H).toSubmodule.sum_mem
    intro j _
    apply (generated H).smul_mem
    apply cross_mem_of_reachable H hs (generated H) _ (hconnected i j)
    intro k
    exact LieSubalgebra.subset_lieSpan ⟨k, rfl⟩

/-- The star chart has an explicit cubic-length certificate for every leaf pair.
Leaf-leaf pairings may vanish; the only denominators are anchor-edge pairings. -/
theorem cross_cubic_certificate (H : Matrix I I K)
    (hs : ∀ i j, H i j = -H j i) (a i j : I)
    (hi : H a i ≠ 0) (hj : H a j ≠ 0) :
    cross H i j =
      (-(H a i * H a j)⁻¹) • ⁅increment H i, ⁅increment H a, increment H j⁆⁆ +
        (H i j / (H a i)^2) • ⁅increment H a, increment H i⁆ := by
  have hflip : ⁅increment H i, cross H a j⁆ =
      -(H j i • cross H a i + H a i • cross H j i) := by
    rw [lie_skew, bracket_cross_increment H hs]
  rw [bracket_increment H hs a j, lie_smul, hflip,
    bracket_increment H hs a i, hs j i, cross_symm H j i]
  ext r c
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  field_simp [hi, hj]
  <;> ring

/-- Nonzero anchor pairings imply connectedness of the actual pairing relation. -/
theorem connected_of_star (H : Matrix I I K)
    (hs : ∀ i j, H i j = -H j i) (a : I)
    (hstar : ∀ i, i ≠ a → H a i ≠ 0) : PairingConnected H := by
  intro i j
  have hia : Relation.ReflTransGen (fun u v => H u v ≠ 0) i a := by
    by_cases hi : i = a
    · subst i
      exact .refl
    · have hedge : H i a ≠ 0 := by rw [hs i a]; exact neg_ne_zero.mpr (hstar i hi)
      exact .tail .refl hedge
  by_cases hj : j = a
  · simpa [hj] using hia
  · exact .tail hia (hstar j hj)

/-- Nonzero rescaling of each actual rank-one generator preserves its Lie closure. -/
theorem generated_row_scale (H : Matrix I I K) (c : I → K)
    (hc : ∀ i, c i ≠ 0) :
    generated (fun i j => c i * H i j) = generated H := by
  have hi : ∀ i, increment (fun i j => c i * H i j) i = c i • increment H i := by
    intro i
    ext r j
    by_cases h : r = i <;> simp [increment, h]
  apply le_antisymm
  · apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [hi]
    exact (generated H).smul_mem (c i) (LieSubalgebra.subset_lieSpan ⟨i, rfl⟩)
  · apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    have hmem : increment (fun i j => c i * H i j) i ∈
        generated (fun i j => c i * H i j) :=
      LieSubalgebra.subset_lieSpan ⟨i, rfl⟩
    have h := (generated (fun i j => c i * H i j)).smul_mem (c i)⁻¹ hmem
    rwa [hi, smul_smul, inv_mul_cancel₀ (hc i), one_smul] at h

/-- The previous trace reconstruction now has full Lie generation, not only an
invariant-form certificate. The input contains no generation hypothesis. -/
theorem recovered_generated_eq_skewAdjoint
    (a : I) (p : I → K) (t : I → I → K)
    (hp : ∀ i, i ≠ a → p i ≠ 0)
    (ht : ∀ i, t i i = 0) (hts : ∀ i j, t i j = -t j i)
    (hdet : (recoveredGram a p t).det ≠ 0) (h2 : (2 : K) ≠ 0) :
    generated (recoveredGram a p t) =
      skewAdjointMatricesLieSubalgebra
        (TraceSymplecticCertificate.recoveredForm a p t) := by
  let J := TraceSymplecticCertificate.recoveredForm a p t
  have hs : ∀ i j, J i j = -J j i :=
    (TraceSymplecticCertificate.recoveredForm_alternating a p t hp ht hts).2
  have hjdet : J.det ≠ 0 :=
    (TraceSymplecticCertificate.form_nondegenerate_iff a p t hp).mpr hdet
  have hstar : ∀ i, i ≠ a → J a i ≠ 0 := by
    intro i hi
    simp [J, TraceSymplecticCertificate.recoveredForm,
      TraceSymplecticCertificate.symplecticWeight, recoveredGram, hi]
  have hw : ∀ i, TraceSymplecticCertificate.symplecticWeight a p i ≠ 0 := by
    intro i
    by_cases hi : i = a
    · simp [TraceSymplecticCertificate.symplecticWeight, hi]
    · simp [TraceSymplecticCertificate.symplecticWeight, hi, hp i hi]
  have hscale : generated J = generated (recoveredGram a p t) :=
    generated_row_scale (recoveredGram a p t)
      (TraceSymplecticCertificate.symplecticWeight a p) hw
  rw [← hscale]
  exact generated_eq_skewAdjoint J hs hjdet h2 (connected_of_star J hs a hstar)

#print axioms generated_eq_skewAdjoint
#print axioms cross_cubic_certificate
#print axioms recovered_generated_eq_skewAdjoint

end D5.S3.Observer.Monodromy.TransvectionLieGeneration
