/- GID: D5/S3/Quantum/Divergence/UniversalCommonCenter
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UniversalCommonCenter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite semidefinite common-center inference for quadratic matrix epigraphs. -/

import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Inner
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Proj
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! A common complex center from all positive-definite matrix-weighted quadratic tests.
proof_shape: content; admission_basis: escape-witness.
escape_witness: epigraph_closed, consumed by exists_common_center_of_posDef_trace_inf_le.
The downstream Umegaki coefficient comparison is not asserted here. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace RealInnerProductSpace
open Set Filter Topology
open Matrix

namespace D5.S3.Quantum.Divergence.UniversalCommonCenter

open HermitianMat

private def inclusion {r a : Type*} [DecidableEq a] (X : Matrix r r ℂ) : Matrix (r × a) (r × a) ℂ :=
  Matrix.kronecker X (1 : Matrix a a ℂ)

private def residual {r a : Type*} [DecidableEq r] [DecidableEq a]
    (A : Matrix (r × a) (r × a) ℂ) (X : Matrix r r ℂ) :
    Matrix (r × a) (r × a) ℂ := A - inclusion X

private def gram {r a : Type*} [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]
    (A : Matrix (r × a) (r × a) ℂ) (X : Matrix r r ℂ) :
    Matrix (r × a) (r × a) ℂ := residual A X * Matrix.conjTranspose (residual A X)

private def hermitianOf {n : Type*} (M : Matrix n n ℂ) (hM : M.IsHermitian) : HermitianMat n ℂ :=
  ⟨M, hM⟩

private def centerEpigraph {r a : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a]
    (A B : Matrix (r × a) (r × a) ℂ) : Set (HermitianMat (r × a) ℂ) :=
  {E | ∃ X : Matrix r r ℂ, (E.mat + B - gram A X).PosSemidef}

private lemma gram_posSemidef {r a : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a]
    (A : Matrix (r × a) (r × a) ℂ) (X : Matrix r r ℂ) :
    (gram A X).PosSemidef := by
  exact Matrix.posSemidef_self_mul_conjTranspose (residual A X)

private lemma gram_isHermitian {r a : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a]
    (A : Matrix (r × a) (r × a) ℂ) (X : Matrix r r ℂ) :
    (gram A X).IsHermitian := (gram_posSemidef A X).isHermitian

private lemma epigraph_nonempty {r a : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a]
    (A B : Matrix (r × a) (r × a) ℂ) (hB : B.IsHermitian) :
    (centerEpigraph A B).Nonempty := by
  refine ⟨hermitianOf (gram A 0 - B) ((gram_isHermitian A 0).sub hB), 0, ?_⟩
  convert Matrix.PosSemidef.zero (n := r × a) (R := ℂ) using 1
  change gram A 0 - B + B - gram A 0 = 0
  abel

private lemma epigraph_upward {r a : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a]
    (A B : Matrix (r × a) (r × a) ℂ)
    {E P : HermitianMat (r × a) ℂ} (hE : E ∈ centerEpigraph A B)
    (hP : 0 ≤ P) : E + P ∈ centerEpigraph A B := by
  obtain ⟨X, hX⟩ := hE
  refine ⟨X, ?_⟩
  convert hX.add (HermitianMat.zero_le_iff.mp hP) using 1
  simp only [HermitianMat.mat_add]
  abel

private lemma gram_convex_remainder {n : Type*} [Fintype n]
    (Q R : Matrix n n ℂ) (s t : ℝ) (hst : s + t = 1) :
    s • (Q * Qᴴ) + t • (R * Rᴴ) -
      (s • Q + t • R) * (s • Q + t • R)ᴴ =
      (s * t) • ((Q - R) * (Q - R)ᴴ) := by
  have hs : s = 1 - t := by linarith
  subst s
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sub, star_trivial, mul_add, add_mul, mul_sub, sub_mul,
    smul_mul_assoc, mul_smul_comm]
  module

private lemma residual_convex {r a : Type*} [DecidableEq r] [DecidableEq a]
    (A : Matrix (r × a) (r × a) ℂ) (X Y : Matrix r r ℂ)
    (s t : ℝ) (hst : s + t = 1) :
    residual A (s • X + t • Y) = s • residual A X + t • residual A Y := by
  ext ⟨i, b⟩ ⟨j, c⟩
  simp only [residual, inclusion, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sub_apply,
    Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
  have hc : (s : ℂ) + t = 1 := by exact_mod_cast hst
  linear_combination -A (i, b) (j, c) * hc

private lemma epigraph_convex {r a : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a]
    (A B : Matrix (r × a) (r × a) ℂ) : Convex ℝ (centerEpigraph A B) := by
  intro E hE F hF s t hs ht hst
  obtain ⟨X, hX⟩ := hE
  obtain ⟨Y, hY⟩ := hF
  refine ⟨s • X + t • Y, ?_⟩
  have hQ := (Matrix.posSemidef_self_mul_conjTranspose
    (residual A X - residual A Y)).smul (mul_nonneg hs ht)
  have h := ((hX.smul hs).add (hY.smul ht)).add hQ
  convert h using 1
  rw [gram, residual_convex A X Y s t hst]
  have he := gram_convex_remainder (residual A X) (residual A Y) s t hst
  change _ = s • (_ + B - _) + t • (_ + B - _) + _
  rw [← he]
  simp only [HermitianMat.mat_add, HermitianMat.mat_smul]
  dsimp only [gram]
  have hs' : s = 1 - t := by linarith
  rw [hs']
  module

private lemma gram_trace_entries {r a : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a]
    (A : Matrix (r × a) (r × a) ℂ) (X : Matrix r r ℂ) :
    (gram A X).trace.re = ∑ i, ∑ j, ‖residual A X i j‖ ^ 2 := by
  simp [gram, Matrix.trace, Matrix.mul_apply, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]

private lemma residual_entry_bound {r a : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a]
    (A : Matrix (r × a) (r × a) ℂ) (X : Matrix r r ℂ) (i j : r × a) :
    ‖residual A X i j‖ ^ 2 ≤ (gram A X).trace.re := by
  rw [gram_trace_entries]
  exact (Finset.single_le_sum (fun k _ => sq_nonneg ‖residual A X i k‖)
    (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg
      (fun l _ => sq_nonneg ‖residual A X k l‖)) (Finset.mem_univ i))

private lemma epigraph_closed {r a : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a] [Nonempty a]
    (A B : Matrix (r × a) (r × a) ℂ) : IsClosed (centerEpigraph A B) := by
  let : NormedAddCommGroup (Matrix r r ℂ) :=
    inferInstanceAs (NormedAddCommGroup (r → r → ℂ))
  let : NormedSpace ℝ (Matrix r r ℂ) :=
    inferInstanceAs (NormedSpace ℝ (r → r → ℂ))
  let : FirstCountableTopology (HermitianMat (r × a) ℂ) :=
    inferInstanceAs (FirstCountableTopology {M : (r × a) → (r × a) → ℂ // Matrix.IsHermitian M})
  rw [← isSeqClosed_iff_isClosed]
  intro E E₀ hE hlim
  choose X hX using hE
  have hc : Continuous (fun E : HermitianMat (r × a) ℂ => (E.mat + B).trace.re) := by
    unfold Matrix.trace
    fun_prop
  obtain ⟨R, hR, hbound⟩ := (Metric.isBounded_range_of_tendsto _
    ((hc.tendsto E₀).comp hlim)).exists_pos_norm_le
  have htr (k : ℕ) : (gram A (X k)).trace.re ≤ R := by
    have hp := (Complex.nonneg_iff.mp (hX k).trace_nonneg).1
    rw [Matrix.trace_sub, Complex.sub_re] at hp
    have hb := hbound _ ⟨k, rfl⟩
    change |((E k).mat + B).trace.re| ≤ R at hb
    linarith [le_abs_self (((E k).mat + B).trace.re)]
  let a₀ : a := Classical.choice inferInstance
  have hentry (k : ℕ) (i j : r) :
      ‖X k i j‖ ≤ ‖A (i, a₀) (j, a₀)‖ + Real.sqrt R := by
    have hs := (residual_entry_bound A (X k) (i, a₀) (j, a₀)).trans (htr k)
    have hn : ‖residual A (X k) (i, a₀) (j, a₀)‖ ≤ Real.sqrt R := by
      exact (Real.le_sqrt (norm_nonneg _) hR.le).mpr hs
    have he : X k i j = A (i, a₀) (j, a₀) - residual A (X k) (i, a₀) (j, a₀) := by
      simp [residual, inclusion]
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add_right hn _)
  let S : ℝ := (∑ i : r, ∑ j : r, ‖A (i, a₀) (j, a₀)‖) + Real.sqrt R
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hnorm (k : ℕ) : ‖X k‖ ≤ S := by
    apply (pi_norm_le_iff_of_nonneg hS).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg hS).mpr
    intro j
    exact (hentry k i j).trans (add_le_add_left
      ((Finset.single_le_sum (fun l _ => norm_nonneg (A (i, a₀) (l, a₀)))
        (Finset.mem_univ j)).trans
        (Finset.single_le_sum (fun l _ => Finset.sum_nonneg
          (fun m _ => norm_nonneg (A (l, a₀) (m, a₀)))) (Finset.mem_univ i))) _)
  obtain ⟨X₀, _, φ, hφ, hXlim⟩ := (isCompact_closedBall (0 : Matrix r r ℂ) S).tendsto_subseq
    (fun k => by simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm k)
  refine ⟨X₀, ?_⟩
  have hcont : Continuous (fun p : HermitianMat (r × a) ℂ × Matrix r r ℂ =>
      p.1.mat + B - gram A p.2) := by
    unfold gram residual inclusion Matrix.kronecker Matrix.kroneckerMap
    fun_prop
  exact HermitianMat.Matrix.PosSemiDef_isClosed.mem_of_tendsto
    ((hcont.tendsto (E₀, X₀)).comp
      ((hlim.comp hφ.tendsto_atTop).prodMk_nhds hXlim))
    (Eventually.of_forall fun k => hX (φ k))

private lemma trace_gram_nonneg {r a : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a]
    (A : Matrix (r × a) (r × a) ℂ) (X : Matrix r r ℂ)
    (Z : Matrix (r × a) (r × a) ℂ) (hZ : Z.PosSemidef) :
    0 ≤ (Z * gram A X).trace.re := by
  have h := HermitianMat.inner_ge_zero
    (A := hermitianOf Z hZ.isHermitian)
    (B := hermitianOf (gram A X) (gram_isHermitian A X))
    (HermitianMat.zero_le_iff.mpr hZ)
    (HermitianMat.zero_le_iff.mpr (gram_posSemidef A X))
  exact h

private lemma trace_inf_psd {r a : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a]
    (A B : Matrix (r × a) (r × a) ℂ)
    (htrace : ∀ Z : Matrix (r × a) (r × a) ℂ, Z.PosDef →
      sInf (Set.range (fun X : Matrix r r ℂ => (Z * gram A X).trace.re)) ≤
        (Z * B).trace.re)
    (Z : Matrix (r × a) (r × a) ℂ) (hZ : Z.PosSemidef) :
    sInf (Set.range (fun X : Matrix r r ℂ => (Z * gram A X).trace.re)) ≤
      (Z * B).trace.re := by
  let v := sInf (Set.range (fun X : Matrix r r ℂ => (Z * gram A X).trace.re))
  have hv (e : ℝ) (he : 0 < e) : v ≤ ((Z + e • 1) * B).trace.re := by
    have hpos : (Z + e • (1 : Matrix (r × a) (r × a) ℂ)).PosDef :=
      Matrix.PosDef.posSemidef_add hZ (Matrix.PosDef.one.smul he)
    apply le_trans _ (htrace _ hpos)
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨X, rfl⟩
    have hbdd : BddBelow (Set.range (fun X : Matrix r r ℂ => (Z * gram A X).trace.re)) :=
      ⟨0, by rintro _ ⟨Y, rfl⟩; exact trace_gram_nonneg A Y Z hZ⟩
    have hle := csInf_le hbdd (Set.mem_range_self X)
    change v ≤ _ at hle
    have hnon := trace_gram_nonneg A X (e • (1 : Matrix (r × a) (r × a) ℂ))
      (Matrix.PosSemidef.one.smul he.le)
    simp only [add_mul, Matrix.trace_add, Complex.add_re] at *
    linarith
  have hc : Continuous (fun e : ℝ => ((Z + e • (1 : Matrix (r × a) (r × a) ℂ)) * B).trace.re) := by
    unfold Matrix.trace
    fun_prop
  have hlim : Tendsto (fun e : ℝ => ((Z + e • (1 : Matrix (r × a) (r × a) ℂ)) * B).trace.re)
      (𝓝[>] 0) (𝓝 ((Z * B).trace.re)) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (Filter.mem_of_superset self_mem_nhdsWithin fun e he => hv e he)

/-- Universal positive-definite trace tests yield one general complex matrix center. -/
theorem exists_common_center_of_posDef_trace_inf_le
    {r a : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a] [Nonempty a]
    (A B : Matrix (r × a) (r × a) ℂ) (hB : B.IsHermitian)
    (htrace : ∀ Z : Matrix (r × a) (r × a) ℂ, Z.PosDef →
      sInf (Set.range (fun X : Matrix r r ℂ =>
        (Z * ((A - Matrix.kronecker X (1 : Matrix a a ℂ)) *
          (A - Matrix.kronecker X (1 : Matrix a a ℂ))ᴴ)).trace.re))
        ≤ (Z * B).trace.re) :
    ∃ X : Matrix r r ℂ,
      (B - (A - Matrix.kronecker X (1 : Matrix a a ℂ)) *
        (A - Matrix.kronecker X (1 : Matrix a a ℂ))ᴴ).PosSemidef := by
  classical
  suffices hzero : (0 : HermitianMat (r × a) ℂ) ∈ centerEpigraph A B by
    simpa only [centerEpigraph, Set.mem_ofPred_eq, HermitianMat.mat_zero, zero_add,
      gram, residual, inclusion] using hzero
  by_contra hn
  let : LocallyConvexSpace ℝ (HermitianMat (r × a) ℂ) :=
    NormedSpace.toLocallyConvexSpace
  obtain ⟨f, u, hu, hsep⟩ := geometric_hahn_banach_point_closed
    (epigraph_convex A B) (epigraph_closed A B) hn
  have hu0 : 0 < u := by simpa using hu
  let Z : HermitianMat (r × a) ℂ := (InnerProductSpace.toDual ℝ _).symm f
  have hZf (E : HermitianMat (r × a) ℂ) : ⟪Z, E⟫_ℝ = f E :=
    InnerProductSpace.toDual_symm_apply
  have hZ : 0 ≤ Z := by
    apply (HermitianMat.nonneg_iff_inner_nonneg Z).mpr
    intro P hP
    rw [hZf]
    obtain ⟨E, hE⟩ := epigraph_nonempty A B hB
    by_contra! hp
    let t : ℝ := (|f E| + |u| + 1) / (-f P)
    have ht : 0 ≤ t := div_nonneg (by positivity) (neg_nonneg.mpr hp.le)
    have hh := hsep (E + t • P) (epigraph_upward A B hE (smul_nonneg ht hP))
    simp only [map_add, map_smul, smul_eq_mul] at hh
    have he : t * f P = -(|f E| + |u| + 1) := by
      dsimp [t]
      field_simp [ne_of_lt hp]
      <;> ring
    rw [he] at hh
    linarith [le_abs_self (f E), neg_abs_le u]
  have hlower : u + (Z.mat * B).trace.re ≤
      sInf (Set.range (fun X : Matrix r r ℂ => (Z.mat * gram A X).trace.re)) := by
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨X, rfl⟩
    let E := hermitianOf (gram A X - B) ((gram_isHermitian A X).sub hB)
    have hE : E ∈ centerEpigraph A B := by
      refine ⟨X, ?_⟩
      convert Matrix.PosSemidef.zero (n := r × a) (R := ℂ) using 1
      change gram A X - B + B - gram A X = 0
      abel
    have hh := hsep E hE
    rw [← hZf, HermitianMat.inner_eq_re_trace] at hh
    change u < (Z.mat * (gram A X - B)).trace.re at hh
    simp only [mul_sub, Matrix.trace_sub, Complex.sub_re] at hh
    linarith
  have hupper := trace_inf_psd A B (by simpa only [gram, residual, inclusion] using htrace)
    Z.mat (HermitianMat.zero_le_iff.mp hZ)
  linarith

#print axioms exists_common_center_of_posDef_trace_inf_le

end D5.S3.Quantum.Divergence.UniversalCommonCenter
