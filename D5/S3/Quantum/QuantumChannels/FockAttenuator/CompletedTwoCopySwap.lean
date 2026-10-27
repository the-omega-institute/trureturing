/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/CompletedTwoCopySwap
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/CompletedTwoCopySwap
   mirror-E: none(waiver:completed-two-copy-identity)
   anchors: []
   utility: none
   digest: Completed coherent-frame action used by the actual two-copy swap. -/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.DisplacementCovariance
import D5.S3.Quantum.Analysis.TraceClass.ColumnSynthesis
import D5.S3.Quantum.Analysis.TraceClass.Spectral
import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.FermionicCorrelationalBound.CompletedTensorSlaterGeometry
import D5.S3.Quantum.Analysis.TraceClass.TraceAlgebra
import D5.S3.Quantum.Analysis.TraceClass.GeneralIdeal
import Mathlib.Analysis.Normed.Ring.InfiniteSum

noncomputable section
open scoped TensorProduct InnerProductSpace BigOperators ENNReal NNReal ComplexOrder
set_option backward.isDefEq.respectTransparency false
open Filter Topology

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.CompletedCoefficientOperator
open BeamSplitter DisplacementCovariance HilbertSchmidt
open private reindex_basis from D5.S3.Quantum.Analysis.TraceClass.Spectral

abbrev H := lp (fun _ : ℕ => ℂ) 2
abbrev H2 := lp (fun _ : ℕ => H) 2

private def occupationBasis : HilbertBasis ℕ ℂ H := default

private theorem slice_square_sum (w : H2) : HasSum (fun n => ‖w n‖ ^ 2) (‖w‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w

private theorem coefficient_data (w : H2) :
    ∃ C : H →L[ℂ] H, IsHilbertSchmidt C ∧
      ∀ n, C (occupationBasis n) = w n := by
  let e : ℕ ≃ Set.range occupationBasis :=
    Equiv.ofInjective occupationBasis occupationBasis.orthonormal.linearIndependent.injective
  obtain ⟨b, hb⟩ := reindex_basis occupationBasis e.symm
  have hv : Summable (fun i : Set.range occupationBasis => ‖w (e.symm i)‖ ^ 2) :=
    e.symm.summable_iff.mpr (slice_square_sum w).summable
  obtain ⟨C, hC, hHS, _, _⟩ :=
    exists_hilbertSchmidt_of_square_summable_columns b (fun i => w (e.symm i)) hv
  refine ⟨C, hHS, fun n => ?_⟩
  simpa only [hb, Equiv.symm_apply_apply] using hC (e n)

/-- Its columns are the actual completed output slices, including infinite support. -/
def coefficientOperator (w : H2) : H →L[ℂ] H := (coefficient_data w).choose

private theorem coefficient_hs (w : H2) : IsHilbertSchmidt (coefficientOperator w) :=
  (coefficient_data w).choose_spec.1

private theorem coefficient_column (w : H2) (n : ℕ) :
    coefficientOperator w (occupationBasis n) = w n := (coefficient_data w).choose_spec.2 n

/-- The operator made from actual matrix columns reproduces the existing reduced
operator. No spectral data or analytic-purity assumption enters this equality. -/
theorem coefficient_mul_adjoint (w : H2) :
    coefficientOperator w * star (coefficientOperator w) = purePartialTrace w := by
  apply ContinuousLinearMap.ext
  intro x
  have hc := (occupationBasis.hasSum_repr ((ContinuousLinearMap.adjoint
      (coefficientOperator w)) x)).mapL (coefficientOperator w)
  have hc' : HasSum (fun n => inner ℂ (w n) x • w n)
      ((coefficientOperator w * star (coefficientOperator w)) x) := by
    simpa only [map_smul, HilbertBasis.repr_apply_apply, coefficient_column,
      ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.mul_apply] using hc
  have hs : Summable (fun n => InnerProductSpace.rankOne ℂ (w n) (w n)) := by
    apply Summable.of_norm
    simpa only [InnerProductSpace.norm_rankOne, ← sq] using (slice_square_sum w).summable
  have hm := hs.hasSum.mapL (ContinuousLinearMap.apply ℂ H x)
  have hm' : HasSum (fun n => inner ℂ (w n) x • w n) (purePartialTrace w x) := by
    simpa only [purePartialTrace, mixture, ContinuousLinearMap.apply_apply,
      InnerProductSpace.rankOne_apply] using hm
  exact hc'.unique hm'

/-- Positivity and trace class refer to the existing completed reduced operator. -/
theorem partial_trace_positive_traceClass (w : H2) :
    0 ≤ purePartialTrace w ∧ IsTraceClass (purePartialTrace w) := by
  rw [← coefficient_mul_adjoint]
  exact ⟨mul_star_self_nonneg _, isTraceClass_mul_star_of_isHilbertSchmidt (coefficient_hs w)⟩

/-- The physical balanced two-photon output is obtained from the published
completed beam splitter, with no support restriction on the input. -/
def balancedFockTwoOutput (a : H) : H2 :=
  beamSplitter (1 / 2) (by norm_num) (tensor a (lp.single 2 2 1))

private theorem tensor_norm_sq (v w : H) : ‖tensor v w‖ ^ 2 = ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
  have ht := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (tensor v w)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at ht
  rw [ht]
  change (∑' n, ‖w n • v‖ ^ 2) = _
  simp only [norm_smul, mul_pow]
  have hw : HasSum (fun n => ‖w n‖ ^ 2) (‖w‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
  rw [hw.summable.tsum_mul_right, hw.tsum_eq, mul_comm]

end D5.S3.Quantum.QuantumChannels.FockAttenuator.CompletedCoefficientOperator

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.TwoCopyEnvironment
open BeamSplitter DisplacementCovariance CompletedCoefficientOperator

/-- The environment state after the actual center/difference rotation. -/
def rotatedEnvironment : H2 :=
  beamSplitter (1 / 2) (by norm_num) (fockPair 2 2)

private theorem balanced_square : Real.sqrt (1 / 2 : ℝ) ^ 2 = 1 / 2 :=
  Real.sq_sqrt (by norm_num)

private theorem sqrt_twenty_four : Real.sqrt (24 : ℝ) = 2 * Real.sqrt 6 := by
  rw [show (24 : ℝ) = 4 * 6 by norm_num, Real.sqrt_mul (by norm_num)]
  norm_num

/-- This finite expansion is inside the completed beam-splitter space, with the
same sign convention as `beamUnitary_fock`. -/
theorem rotated_environment_expansion :
    rotatedEnvironment = ((Real.sqrt 6 / 4 : ℝ) : ℂ) • fockPair 4 0 -
      (1 / 2 : ℂ) • fockPair 2 2 +
      ((Real.sqrt 6 / 4 : ℝ) : ℂ) • fockPair 0 4 := by
  unfold rotatedEnvironment beamSplitter
  rw [beamUnitary_fock]
  norm_num [fockExpansion, Fin.sum_univ_succ, Nat.choose]
  have h2 : (Real.sqrt (1 / 2 : ℝ) : ℂ) ^ 2 = 1 / 2 := by
    calc
      _ = ((Real.sqrt (1 / 2 : ℝ) ^ 2 : ℝ) : ℂ) := (Complex.ofReal_pow _ _).symm
      _ = ((1 / 2 : ℝ) : ℂ) := congrArg Complex.ofReal balanced_square
      _ = _ := by norm_num
  have hf2 : (Real.sqrt (2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hfne : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  simp only [sqrt_twenty_four]
  push_cast
  match_scalars <;> field_simp
  all_goals ring_nf
  all_goals simp_all only [show (4 : ℕ) = 2 * 2 by omega, pow_mul]
  all_goals norm_num

end D5.S3.Quantum.QuantumChannels.FockAttenuator.TwoCopyEnvironment

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.CompletedTwoCopySwap
open BeamSplitter CompletedCoefficientOperator
open D5.S3.Quantum.FermionicCorrelationalBound.OccupationHilbertContractions
open D5.S3.Quantum.FermionicCorrelationalBound.CompletedTensorSlaterGeometry
open HilbertSchmidt
open private reindex_basis from D5.S3.Quantum.Analysis.TraceClass.Spectral
open private tensorHilbertBasis_repr_tmul from
  D5.S3.Quantum.FermionicCorrelationalBound.CompletedTensorSlaterGeometry

abbrev FourModes := UniformSpace.Completion (H2 ⊗[ℂ] H2)

private theorem fock_pair_single (m n : ℕ) :
    fockPair m n = lp.single 2 n (lp.single 2 m (1 : ℂ)) := by
  apply lp.ext
  funext j
  by_cases hj : j = n
  · subst j
    simp [fockPair, tensor, lp.single_apply]
  · simp [fockPair, tensor, lp.single_apply, hj]

private theorem fock_pairs_orthonormal :
    Orthonormal ℂ (fun p : ℕ × ℕ => fockPair p.1 p.2) := by
  classical
  rw [orthonormal_iff_ite]
  intro p q
  rw [fock_pair_single, fock_pair_single, lp.inner_single_left]
  by_cases h2 : q.2 = p.2
  · rw [h2]
    simp only [lp.single_apply, Pi.single_eq_same, lp.inner_single_left]
    by_cases h1 : q.1 = p.1
    · have hpq : p = q := Prod.ext h1.symm h2.symm
      simp [lp.single_apply, Pi.single_apply, h1, hpq]
    · have hpq : p ≠ q := fun h => h1 (congrArg Prod.fst h).symm
      simp [lp.single_apply, h1, hpq]
  · have hpq : p ≠ q := fun h => h2 (congrArg Prod.snd h).symm
    simp [lp.single_apply, h2, hpq]

private theorem fock_pairs_total :
    (Submodule.span ℂ (Set.range (fun p : ℕ × ℕ => fockPair p.1 p.2)))ᗮ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hc (m n : ℕ) : x n m = 0 := by
    have hi := (Submodule.mem_orthogonal _ _).mp hx _
      (Submodule.subset_span ⟨(m, n), rfl⟩)
    change inner ℂ (fockPair m n) x = 0 at hi
    rw [fock_pair_single, lp.inner_single_left, lp.inner_single_left] at hi
    simpa only [RCLike.inner_apply, map_one, one_mul, mul_one] using hi
  have hz : x = 0 := by
    apply lp.ext
    funext n
    apply lp.ext
    funext m
    exact hc m n
  exact hz ▸ Submodule.zero_mem _

private def fockBasis : HilbertBasis (ℕ × ℕ) ℂ H2 :=
  HilbertBasis.mkOfOrthogonalEqBot fock_pairs_orthonormal fock_pairs_total

private theorem fock_basis_apply (p : ℕ × ℕ) : fockBasis p = fockPair p.1 p.2 := by
  rw [fockBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

private theorem fock_basis_repr (w : H2) (p : ℕ × ℕ) :
    fockBasis.repr w p = w p.2 p.1 := by
  rw [HilbertBasis.repr_apply_apply, fock_basis_apply, fock_pair_single,
    lp.inner_single_left, lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, one_mul, mul_one]

private def oneBasis : HilbertBasis ℕ ℂ H := default

private def fourBasis : HilbertBasis ((ℕ × ℕ) × (ℕ × ℕ)) ℂ FourModes :=
  tensorHilbertBasis fockBasis fockBasis

private theorem four_basis_product (x y : H2) (p : (ℕ × ℕ) × (ℕ × ℕ)) :
    fourBasis.repr ((x ⊗ₜ[ℂ] y : H2 ⊗[ℂ] H2) : FourModes) p =
      fockBasis.repr x p.1 * fockBasis.repr y p.2 := by
  exact tensorHilbertBasis_repr_tmul fockBasis fockBasis x y p.1 p.2

private def fourPermutation (e : Equiv.Perm ((ℕ × ℕ) × (ℕ × ℕ))) :
    FourModes ≃ₗᵢ[ℂ] FourModes :=
  fourBasis.repr.trans ((coordinateEquiv e).trans fourBasis.repr.symm)

private theorem four_permutation_repr
    (e : Equiv.Perm ((ℕ × ℕ) × (ℕ × ℕ))) (x : FourModes)
    (p : (ℕ × ℕ) × (ℕ × ℕ)) :
    fourBasis.repr (fourPermutation e x) p = fourBasis.repr x (e.symm p) := by
  simp only [fourPermutation, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  change coordinateRename e.toEmbedding (fourBasis.repr x) p = _
  have h := coordinateRename_image e.toEmbedding (fourBasis.repr x) (e.symm p)
  change coordinateRename e.toEmbedding (fourBasis.repr x) (e (e.symm p)) = _ at h
  simpa only [e.apply_symm_apply] using h

private def retainedPermutation : Equiv.Perm ((ℕ × ℕ) × (ℕ × ℕ)) where
  toFun p := ((p.2.1, p.1.2), (p.1.1, p.2.2))
  invFun p := ((p.2.1, p.1.2), (p.1.1, p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exchange only the two retained factors in the completed four-mode space.
This is a bounded unitary, rather than a finite matrix with a cutoff. -/
def retainedSwap : FourModes ≃ₗᵢ[ℂ] FourModes :=
  fourPermutation retainedPermutation

private def regroupPermutation : Equiv.Perm ((ℕ × ℕ) × (ℕ × ℕ)) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Regroup (input1,environment1),(input2,environment2) as the input pair and
environment pair. All four occupation indices and all completed tails remain. -/
def regroup : FourModes ≃ₗᵢ[ℂ] FourModes := fourPermutation regroupPermutation

private theorem regroup_product (a e b f : H) :
    regroup ((tensor a e ⊗ₜ[ℂ] tensor b f : H2 ⊗[ℂ] H2) : FourModes) =
      ((tensor a b ⊗ₜ[ℂ] tensor e f : H2 ⊗[ℂ] H2) : FourModes) := by
  apply fourBasis.repr.injective
  apply lp.ext
  funext p
  rw [show regroup = fourPermutation regroupPermutation from rfl,
    four_permutation_repr, four_basis_product, four_basis_product]
  simp only [fock_basis_repr]
  change (e p.2.1 * a p.1.1) * (f p.2.2 * b p.1.2) =
    (b p.1.2 * a p.1.1) * (f p.2.2 * e p.2.1)
  ring

private def differencePermutation : Equiv.Perm ((ℕ × ℕ) × (ℕ × ℕ)) where
  toFun p := ((p.1.1, p.2.2), (p.2.1, p.1.2))
  invFun p := ((p.1.1, p.2.2), (p.2.1, p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exchange only the input and environment difference modes after regrouping. -/
def differenceSwap : FourModes ≃ₗᵢ[ℂ] FourModes := fourPermutation differencePermutation

private def twoCopyMap (U : H2 →L[ℂ] H2) : FourModes →L[ℂ] FourModes :=
  (TensorProduct.mapL U U).completion

private theorem two_copy_map_product (U : H2 →L[ℂ] H2) (x y : H2) :
    twoCopyMap U ((x ⊗ₜ[ℂ] y : H2 ⊗[ℂ] H2) : FourModes) =
      ((U x ⊗ₜ[ℂ] U y : H2 ⊗[ℂ] H2) : FourModes) := by
  simp only [twoCopyMap, ContinuousLinearMap.completion_apply_coe,
    TensorProduct.mapL_tmul]

private theorem environment_coefficient (p : ℕ × ℕ) :
    fockBasis.repr TwoCopyEnvironment.rotatedEnvironment p =
      if p = (4, 0) then ((Real.sqrt 6 / 4 : ℝ) : ℂ)
      else if p = (2, 2) then (-1 / 2 : ℂ)
      else if p = (0, 4) then ((Real.sqrt 6 / 4 : ℝ) : ℂ) else 0 := by
  have hb (m n : ℕ) : fockBasis.repr (fockPair m n) p =
      if p = (m, n) then 1 else 0 := by
    change fockBasis.repr (fockPair (m, n).1 (m, n).2) p = _
    rw [← fock_basis_apply, HilbertBasis.repr_self, lp.single_apply]
    simp only [Pi.single_apply, eq_comm]
  rw [TwoCopyEnvironment.rotated_environment_expansion]
  simp only [map_add, map_sub, map_smul, lp.coeFn_add, lp.coeFn_sub,
    lp.coeFn_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hb]
  by_cases h40 : p = (4, 0)
  · subst p
    norm_num
  by_cases h22 : p = (2, 2)
  · subst p
    norm_num
  by_cases h04 : p = (0, 4)
  · subst p
    norm_num
  · simp [h40, h22, h04]

private def environmentWeight (n : ℕ) : ℝ :=
  if n = 0 then 3 / 8 else if n = 2 then 1 / 4 else if n = 4 then 3 / 8 else 0

private theorem difference_swap_row (v : H2) (p : ℕ × ℕ) :
    let x : FourModes := ((v ⊗ₜ[ℂ] TwoCopyEnvironment.rotatedEnvironment :
      H2 ⊗[ℂ] H2) : FourModes)
    (∑' q : ℕ × ℕ, inner ℂ (fourBasis.repr x (p, q))
      (fourBasis.repr (differenceSwap x) (p, q))).re =
        environmentWeight p.2 * ‖fockBasis.repr v p‖ ^ 2 := by
  dsimp only
  simp only [differenceSwap, four_permutation_repr, four_basis_product]
  change (∑' q : ℕ × ℕ, inner ℂ
    (fockBasis.repr v p * fockBasis.repr TwoCopyEnvironment.rotatedEnvironment q)
    (fockBasis.repr v (p.1, q.2) *
      fockBasis.repr TwoCopyEnvironment.rotatedEnvironment (q.1, p.2))).re = _
  rw [tsum_eq_sum (s := ({(4, 0), (2, 2), (0, 4)} : Finset (ℕ × ℕ)))
    (fun q hq => by
      have h40 : q ≠ (4, 0) := fun h => hq (by simp [h])
      have h22 : q ≠ (2, 2) := fun h => hq (by simp [h])
      have h04 : q ≠ (0, 4) := fun h => hq (by simp [h])
      simp [environment_coefficient, h40, h22, h04])]
  have ha : ‖((Real.sqrt 6 / 4 : ℝ) : ℂ)‖ ^ 2 = 3 / 8 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have hself (z a : ℂ) : (inner ℂ (z * a) (z * a)).re = ‖z‖ ^ 2 * ‖a‖ ^ 2 := by
    change RCLike.re (inner ℂ (z * a) (z * a)) = _
    rw [inner_self_eq_norm_sq, norm_mul, mul_pow]
  have he4 (d : ℕ) : fockBasis.repr TwoCopyEnvironment.rotatedEnvironment (4, d) =
      if d = 0 then ((Real.sqrt 6 / 4 : ℝ) : ℂ) else 0 := by
    simp [environment_coefficient, Prod.mk.injEq]
  have he2 (d : ℕ) : fockBasis.repr TwoCopyEnvironment.rotatedEnvironment (2, d) =
      if d = 2 then (-1 / 2 : ℂ) else 0 := by
    simp [environment_coefficient, Prod.mk.injEq]
  have he0 (d : ℕ) : fockBasis.repr TwoCopyEnvironment.rotatedEnvironment (0, d) =
      if d = 4 then ((Real.sqrt 6 / 4 : ℝ) : ℂ) else 0 := by
    simp [environment_coefficient, Prod.mk.injEq]
  simp only [he4, he2, he0]
  have hb : ‖(-(1 / 2) : ℂ)‖ ^ 2 = 1 / 4 := by norm_num [norm_div]
  rcases p with ⟨c, d⟩
  by_cases h0 : d = 0
  · subst d
    norm_num only [environmentWeight, ite_true, ite_false,
      mul_zero, inner_zero_left, inner_zero_right, add_zero, zero_add]
    change (inner ℂ (fockBasis.repr v (c, 0) * ((Real.sqrt 6 / 4 : ℝ) : ℂ))
      (fockBasis.repr v (c, 0) * ((Real.sqrt 6 / 4 : ℝ) : ℂ))).re = _
    rw [hself, ha]
    ring
  by_cases h2 : d = 2
  · subst d
    norm_num only [environmentWeight, ite_true, ite_false,
      mul_zero, inner_zero_left, inner_zero_right, add_zero, zero_add]
    change (inner ℂ (fockBasis.repr v (c, 2) * (-(1 / 2) : ℂ))
      (fockBasis.repr v (c, 2) * (-(1 / 2) : ℂ))).re = _
    rw [hself, hb]
    ring
  by_cases h4 : d = 4
  · subst d
    norm_num only [environmentWeight, ite_true, ite_false,
      mul_zero, inner_zero_left, inner_zero_right, add_zero, zero_add]
    change (inner ℂ (fockBasis.repr v (c, 4) * ((Real.sqrt 6 / 4 : ℝ) : ℂ))
      (fockBasis.repr v (c, 4) * ((Real.sqrt 6 / 4 : ℝ) : ℂ))).re = _
    rw [hself, ha]
    ring
  · norm_num only [environmentWeight, h0, h2, h4, ite_true, ite_false,
      mul_zero, inner_zero_right, add_zero, zero_add, Complex.zero_re, zero_mul]

/-- Completed-space swap compression against the actual rotated two-copy
environment. Every center coordinate of v and every infinite tail is retained. -/
theorem difference_swap_compression (v : H2) :
    let x : FourModes := ((v ⊗ₜ[ℂ] TwoCopyEnvironment.rotatedEnvironment :
      H2 ⊗[ℂ] H2) : FourModes)
    (inner ℂ x (differenceSwap x)).re ≤ 3 / 8 * ‖v‖ ^ 2 := by
  dsimp only
  let x : FourModes := ((v ⊗ₜ[ℂ] TwoCopyEnvironment.rotatedEnvironment :
    H2 ⊗[ℂ] H2) : FourModes)
  let F (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
    inner ℂ (fourBasis.repr x p) (fourBasis.repr (differenceSwap x) p)
  have hF : Summable F := lp.summable_inner _ _
  have hrows := Complex.hasSum_re hF.prod.hasSum
  have hinner : inner ℂ x (differenceSwap x) = ∑' p : ℕ × ℕ, ∑' q : ℕ × ℕ, F (p, q) := by
    rw [← fourBasis.repr.inner_map_map, lp.inner_eq_tsum]
    exact hF.tsum_prod
  have hnorm : HasSum (fun p => ‖fockBasis.repr v p‖ ^ 2) (‖v‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] using
      lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (fockBasis.repr v)
  have hweight (n : ℕ) : 0 ≤ environmentWeight n ∧ environmentWeight n ≤ 3 / 8 := by
    unfold environmentWeight
    split_ifs <;> norm_num
  have hbound (p : ℕ × ℕ) :
      environmentWeight p.2 * ‖fockBasis.repr v p‖ ^ 2 ≤
        (3 / 8) * ‖fockBasis.repr v p‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (hweight p.2).2 (sq_nonneg _)
  have hweighted : Summable (fun p => environmentWeight p.2 * ‖fockBasis.repr v p‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg (hweight p.2).1 (sq_nonneg _))
      hbound (hnorm.summable.mul_left (3 / 8))
  rw [hinner, ← hrows.tsum_eq]
  change (∑' p, (∑' q, F (p, q)).re) ≤ _
  simp_rw [show ∀ p, (∑' q, F (p, q)).re =
    environmentWeight p.2 * ‖fockBasis.repr v p‖ ^ 2 from fun p => difference_swap_row v p]
  calc
    _ ≤ ∑' p, (3 / 8) * ‖fockBasis.repr v p‖ ^ 2 :=
      Summable.tsum_le_tsum hbound hweighted (hnorm.summable.mul_left _)
    _ = _ := (hnorm.mul_left (3 / 8)).tsum_eq

#print axioms difference_swap_compression

/-- Recover the coherent action of the published beam unitary from its actual
isometric-extension definition. This is used to compare four-mode bounded maps. -/
private theorem beam_coherent (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1) (z : ℂ × ℂ) :
    beamUnitary t r h (exponentialPair z) = exponentialPair (rotate t r z) := by
  have hlin (c : (ℂ × ℂ) →₀ ℂ) :
      beamUnitary t r h (Finsupp.linearCombination ℂ exponentialPair c) =
        Finsupp.linearCombination ℂ (exponentialPair ∘ rotate t r) c := by
    unfold beamUnitary
    exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ c
  simpa only [Finsupp.linearCombination_single, one_smul, Function.comp_apply] using
    hlin (Finsupp.single z (1 : ℂ))

/- The next two auxiliary arguments lift the local totalness argument in the
published BeamSplitter construction. That proof is a local `have`, so it is not
an importable declaration. The consumers here are the completed four-mode map
comparison below, not a second endpoint for the existing coherent action. -/
private theorem exponential_total (v : H)
    (hv : ∀ z : ℂ, inner ℂ v (exponentialVector z) = 0) : v = 0 := by
  let P : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ
    (fun n => (starRingEnd ℂ) (v n) / (Real.sqrt (n.factorial : ℝ) : ℂ))
  have hs : HasFPowerSeriesAt (fun z : ℂ => inner ℂ v (exponentialVector z)) P 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [] with z
    simp only [zero_add]
    apply HasSum.congr_fun (lp.hasSum_inner v (exponentialVector z))
    intro n
    simp only [P, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
      exponentialVector, exponentialCoeff, RCLike.inner_apply]
    ring
  rw [show (fun z : ℂ => inner ℂ v (exponentialVector z)) = 0 from funext hv] at hs
  apply lp.ext
  funext n
  have hc := congrArg (fun Q : FormalMultilinearSeries ℂ ℂ ℂ => Q.coeff n) hs.eq_zero
  simp only [P, FormalMultilinearSeries.coeff_ofScalars] at hc
  change (starRingEnd ℂ) (v n) / (Real.sqrt (n.factorial : ℝ) : ℂ) = 0 at hc
  have hne : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by
    norm_cast
    exact (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
  have hz := (div_eq_zero_iff.mp hc).resolve_right hne
  simpa using hz

private theorem exponential_pair_total (v : H2)
    (hv : ∀ z : ℂ × ℂ, inner ℂ v (exponentialPair z) = 0) : v = 0 := by
  let P (a : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ
    (fun n => inner ℂ (v n) (exponentialVector a) / (Real.sqrt (n.factorial : ℝ) : ℂ))
  have hs (a : ℂ) : HasFPowerSeriesAt (fun z : ℂ => inner ℂ v (exponentialPair (a, z))) (P a) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [] with z
    simp only [zero_add]
    apply HasSum.congr_fun (lp.hasSum_inner v (exponentialPair (a, z)))
    intro n
    simp only [P, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
      exponentialPair, tensor, exponentialVector, exponentialCoeff, inner_smul_right]
    ring
  apply lp.ext
  funext n
  apply exponential_total
  intro a
  have hh := hs a
  rw [show (fun z : ℂ => inner ℂ v (exponentialPair (a, z))) = 0 from
    funext (fun z => hv (a, z))] at hh
  have hc := congrArg (fun Q : FormalMultilinearSeries ℂ ℂ ℂ => Q.coeff n) hh.eq_zero
  simp only [P, FormalMultilinearSeries.coeff_ofScalars] at hc
  change inner ℂ (v n) (exponentialVector a) / (Real.sqrt (n.factorial : ℝ) : ℂ) = 0 at hc
  have hne : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by
    norm_cast
    exact (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
  exact (div_eq_zero_iff.mp hc).resolve_right hne

private theorem exponential_pair_span_dense :
    Dense (Submodule.span ℂ (Set.range exponentialPair) : Set H2) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm ?_ bot_le
  intro v hv
  have hz : v = 0 := exponential_pair_total v (fun z =>
    Submodule.inner_left_of_mem_orthogonal
      (K := Submodule.span ℂ (Set.range exponentialPair))
      (Submodule.subset_span (Set.mem_range_self z)) hv)
  simp [hz]

private theorem four_clm_ext (T U : FourModes →L[ℂ] FourModes)
    (h : ∀ z w : ℂ × ℂ,
      T ((exponentialPair z ⊗ₜ[ℂ] exponentialPair w : H2 ⊗[ℂ] H2) : FourModes) =
      U ((exponentialPair z ⊗ₜ[ℂ] exponentialPair w : H2 ⊗[ℂ] H2) : FourModes)) : T = U := by
  let J (x : H2) : H2 →L[ℂ] FourModes :=
    (UniformSpace.Completion.toComplL : H2 ⊗[ℂ] H2 →L[ℂ] FourModes).comp
      (TensorProduct.mkL ℂ H2 H2 x)
  have hx (z : ℂ × ℂ) (y : H2) : T (J (exponentialPair z) y) = U (J (exponentialPair z) y) := by
    have heq : T.comp (J (exponentialPair z)) = U.comp (J (exponentialPair z)) :=
      ContinuousLinearMap.ext_on exponential_pair_span_dense (by
        rintro _ ⟨w, rfl⟩
        exact h z w)
    exact congrArg (fun L : H2 →L[ℂ] FourModes => L y) heq
  have hall (x y : H2) : T ((x ⊗ₜ[ℂ] y : H2 ⊗[ℂ] H2) : FourModes) =
      U ((x ⊗ₜ[ℂ] y : H2 ⊗[ℂ] H2) : FourModes) := by
    let K : H2 →L[ℂ] FourModes :=
      (UniformSpace.Completion.toComplL : H2 ⊗[ℂ] H2 →L[ℂ] FourModes).comp
        ((TensorProduct.mkL ℂ H2 H2).flip y)
    have heq : T.comp K = U.comp K := ContinuousLinearMap.ext_on
      exponential_pair_span_dense (by
        rintro _ ⟨z, rfl⟩
        exact hx z y)
    exact congrArg (fun L : H2 →L[ℂ] FourModes => L x) heq
  apply ContinuousLinearMap.ext
  intro x
  refine UniformSpace.Completion.induction_on (p := fun x => T x = U x) x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => exact hall x y
  | add x y hx hy => simpa only [UniformSpace.Completion.coe_add, map_add, hx, hy]

private theorem retained_swap_product (a e b f : H) :
    retainedSwap ((tensor a e ⊗ₜ[ℂ] tensor b f : H2 ⊗[ℂ] H2) : FourModes) =
      ((tensor b e ⊗ₜ[ℂ] tensor a f : H2 ⊗[ℂ] H2) : FourModes) := by
  apply fourBasis.repr.injective
  apply lp.ext
  funext p
  rw [show retainedSwap = fourPermutation retainedPermutation from rfl,
    four_permutation_repr, four_basis_product, four_basis_product]
  simp only [fock_basis_repr]
  change (e p.1.2 * a p.2.1) * (f p.2.2 * b p.1.1) =
    (e p.1.2 * b p.1.1) * (f p.2.2 * a p.2.1)
  ring

private theorem difference_swap_product (a e b f : H) :
    differenceSwap ((tensor a e ⊗ₜ[ℂ] tensor b f : H2 ⊗[ℂ] H2) : FourModes) =
      ((tensor a f ⊗ₜ[ℂ] tensor b e : H2 ⊗[ℂ] H2) : FourModes) := by
  apply fourBasis.repr.injective
  apply lp.ext
  funext p
  rw [show differenceSwap = fourPermutation differencePermutation from rfl,
    four_permutation_repr, four_basis_product, four_basis_product]
  simp only [fock_basis_repr]
  change (e p.2.2 * a p.1.1) * (f p.1.2 * b p.2.1) =
    (f p.1.2 * a p.1.1) * (e p.2.2 * b p.2.1)
  ring

private def halfRoot : ℝ := Real.sqrt (1 / 2)

private theorem half_root_sq : halfRoot ^ 2 = 1 / 2 :=
  Real.sq_sqrt (by norm_num)

private theorem half_root_complex_sq : (halfRoot : ℂ) ^ 2 = 1 / 2 := by
  calc
    _ = ((halfRoot ^ 2 : ℝ) : ℂ) := (Complex.ofReal_pow _ _).symm
    _ = ((1 / 2 : ℝ) : ℂ) := congrArg Complex.ofReal half_root_sq
    _ = _ := by norm_num

private def balancedUnitary : H2 ≃ₗᵢ[ℂ] H2 :=
  beamUnitary halfRoot halfRoot (by nlinarith [half_root_sq])

private def relativeUnitary : H2 ≃ₗᵢ[ℂ] H2 :=
  beamUnitary halfRoot (-halfRoot) (by nlinarith [half_root_sq])

private def pairMap (U : H2 ≃ₗᵢ[ℂ] H2) : FourModes →L[ℂ] FourModes :=
  twoCopyMap U.toContinuousLinearEquiv.toContinuousLinearMap

private theorem pair_map_product (U : H2 ≃ₗᵢ[ℂ] H2) (x y : H2) :
    pairMap U ((x ⊗ₜ[ℂ] y : H2 ⊗[ℂ] H2) : FourModes) =
      ((U x ⊗ₜ[ℂ] U y : H2 ⊗[ℂ] H2) : FourModes) :=
  two_copy_map_product _ x y

private theorem pair_map_norm (U : H2 ≃ₗᵢ[ℂ] H2) (x : FourModes) :
    ‖pairMap U x‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on (p := fun x => ‖pairMap U x‖ = ‖x‖) x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro t
  simp only [pairMap, twoCopyMap, ContinuousLinearMap.completion_apply_coe,
    UniformSpace.Completion.norm_coe]
  have hU : (U.toContinuousLinearEquiv.toContinuousLinearMap : H2 →ₗ[ℂ] H2) =
      U.toLinearIsometry.toLinearMap := by
    ext y
    rfl
  simpa only [TensorProduct.mapL_apply, TensorProduct.mapIsometry_apply, hU] using
    (TensorProduct.mapIsometry U.toLinearIsometry U.toLinearIsometry).norm_map t

private def pairIsometry (U : H2 ≃ₗᵢ[ℂ] H2) : FourModes →ₗᵢ[ℂ] FourModes :=
  { (pairMap U).toLinearMap with norm_map' := pair_map_norm U }

private theorem pair_map_inner (U : H2 ≃ₗᵢ[ℂ] H2) (x y : FourModes) :
    inner ℂ (pairMap U x) (pairMap U y) = inner ℂ x y :=
  (pairIsometry U).inner_map_map x y

private theorem relative_balanced (x : H2) : relativeUnitary (balancedUnitary x) = x := by
  have heq : relativeUnitary.toContinuousLinearEquiv.toContinuousLinearMap.comp
      balancedUnitary.toContinuousLinearEquiv.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ H2 := by
    apply ContinuousLinearMap.ext_on exponential_pair_span_dense
    rintro _ ⟨z, rfl⟩
    change relativeUnitary (balancedUnitary (exponentialPair z)) = exponentialPair z
    rw [show balancedUnitary (exponentialPair z) =
      exponentialPair (rotate halfRoot halfRoot z) from beam_coherent _ _ _ _,
      show relativeUnitary (exponentialPair (rotate halfRoot halfRoot z)) =
      exponentialPair (rotate halfRoot (-halfRoot) (rotate halfRoot halfRoot z)) from
        beam_coherent _ _ _ _]
    apply congrArg exponentialPair
    have hs := half_root_complex_sq
    apply Prod.ext <;> simp only [rotate, Complex.ofReal_neg]
    all_goals ring_nf
    all_goals simp only [hs]
    all_goals ring
  exact congrArg (fun L : H2 →L[ℂ] H2 => L x) heq

private theorem balanced_is_published :
    balancedUnitary = beamSplitter (1 / 2) (by norm_num) := by
  unfold balancedUnitary beamSplitter halfRoot
  congr 1 <;> norm_num

private theorem relative_environment :
    relativeUnitary (fockPair 2 2) = TwoCopyEnvironment.rotatedEnvironment := by
  rw [TwoCopyEnvironment.rotated_environment_expansion]
  unfold relativeUnitary
  rw [beamUnitary_fock]
  norm_num [fockExpansion, Fin.sum_univ_succ, Nat.choose]
  have h2 := half_root_complex_sq
  have h24 : Real.sqrt (24 : ℝ) = 2 * Real.sqrt 6 := by
    rw [show (24 : ℝ) = 4 * 6 by norm_num, Real.sqrt_mul (by norm_num)]
    norm_num
  have hf2 : (Real.sqrt (2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hfne : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  simp only [h24]
  push_cast
  match_scalars <;> field_simp
  all_goals ring_nf
  all_goals simp_all only [show (4 : ℕ) = 2 * 2 by omega, pow_mul]
  all_goals norm_num

/-- Rotate the input copies and environment copies separately into their
center/difference coordinates. It acts on the entire completed four-mode space. -/
def centerDifference : FourModes →L[ℂ] FourModes :=
  (pairMap relativeUnitary).comp regroup.toContinuousLinearEquiv.toContinuousLinearMap

private theorem center_difference_inner (x y : FourModes) :
    inner ℂ (centerDifference x) (centerDifference y) = inner ℂ x y := by
  rw [centerDifference, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    pair_map_inner]
  exact regroup.inner_map_map x y

private theorem retained_swap_coherent (z w : ℂ × ℂ) :
    retainedSwap ((exponentialPair z ⊗ₜ[ℂ] exponentialPair w : H2 ⊗[ℂ] H2) : FourModes) =
      ((exponentialPair (w.1, z.2) ⊗ₜ[ℂ] exponentialPair (z.1, w.2) : H2 ⊗[ℂ] H2) : FourModes) :=
  retained_swap_product _ _ _ _

private theorem difference_swap_coherent (z w : ℂ × ℂ) :
    differenceSwap ((exponentialPair z ⊗ₜ[ℂ] exponentialPair w : H2 ⊗[ℂ] H2) : FourModes) =
      ((exponentialPair (z.1, w.2) ⊗ₜ[ℂ] exponentialPair (w.1, z.2) : H2 ⊗[ℂ] H2) : FourModes) :=
  difference_swap_product _ _ _ _

private theorem regroup_coherent (z w : ℂ × ℂ) :
    regroup ((exponentialPair z ⊗ₜ[ℂ] exponentialPair w : H2 ⊗[ℂ] H2) : FourModes) =
      ((exponentialPair (z.1, w.1) ⊗ₜ[ℂ] exponentialPair (z.2, w.2) : H2 ⊗[ℂ] H2) : FourModes) :=
  regroup_product _ _ _ _

/-- Actual bounded-map conjugation: the retained swap between the two output
copies becomes an exchange of the two difference modes. No finite-support or
energy premise is part of this completed-space equality. -/
theorem balanced_swap_conjugation :
    centerDifference.comp ((pairMap relativeUnitary).comp
      (retainedSwap.toContinuousLinearEquiv.toContinuousLinearMap.comp (pairMap balancedUnitary))) =
    differenceSwap.toContinuousLinearEquiv.toContinuousLinearMap.comp centerDifference := by
  apply four_clm_ext
  intro z w
  have hb (z : ℂ × ℂ) : balancedUnitary (exponentialPair z) =
      exponentialPair (rotate halfRoot halfRoot z) := beam_coherent _ _ _ _
  have hr (z : ℂ × ℂ) : relativeUnitary (exponentialPair z) =
      exponentialPair (rotate halfRoot (-halfRoot) z) := beam_coherent _ _ _ _
  have hc (z w : ℂ × ℂ) : centerDifference
      ((exponentialPair z ⊗ₜ[ℂ] exponentialPair w : H2 ⊗[ℂ] H2) : FourModes) =
      ((exponentialPair (rotate halfRoot (-halfRoot) (z.1, w.1)) ⊗ₜ[ℂ]
        exponentialPair (rotate halfRoot (-halfRoot) (z.2, w.2)) :
          H2 ⊗[ℂ] H2) : FourModes) := by
    change pairMap relativeUnitary (regroup _) = _
    rw [regroup_coherent, pair_map_product, hr, hr]
  change centerDifference (pairMap relativeUnitary (retainedSwap
    (pairMap balancedUnitary
      ((exponentialPair z ⊗ₜ[ℂ] exponentialPair w : H2 ⊗[ℂ] H2) : FourModes)))) =
    differenceSwap (centerDifference
      ((exponentialPair z ⊗ₜ[ℂ] exponentialPair w : H2 ⊗[ℂ] H2) : FourModes))
  rw [pair_map_product, hb, hb, retained_swap_coherent, pair_map_product, hr, hr,
    hc, hc, difference_swap_coherent]
  have hs := half_root_complex_sq
  have hs3 : (halfRoot : ℂ) ^ 3 = (halfRoot : ℂ) / 2 := by
    linear_combination (halfRoot : ℂ) * hs
  congr 2 <;> apply congrArg exponentialPair <;> apply Prod.ext
  all_goals simp only [rotate, Complex.ofReal_neg]
  all_goals ring_nf
  all_goals simp only [hs, hs3]
  all_goals ring

#print axioms balanced_swap_conjugation

private def environmentFirst : Equiv.Perm ((ℕ × ℕ) × (ℕ × ℕ)) where
  toFun p := ((p.1.2, p.2.2), (p.1.1, p.2.1))
  invFun p := ((p.2.1, p.1.1), (p.2.2, p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual retained-swap expectation is the Gram square sum of the
completed discarded-mode slices. The proof reorders an absolutely convergent
Hilbert inner-product series, so arbitrary infinite support is included. -/
theorem retained_swap_gram (w : H2) :
    let x : FourModes := ((w ⊗ₜ[ℂ] w : H2 ⊗[ℂ] H2) : FourModes)
    inner ℂ x (retainedSwap x) =
      ∑' jk : ℕ × ℕ, (‖inner ℂ (w jk.1) (w jk.2)‖ ^ 2 : ℂ) := by
  dsimp only
  let x : FourModes := ((w ⊗ₜ[ℂ] w : H2 ⊗[ℂ] H2) : FourModes)
  let F (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
    inner ℂ (fourBasis.repr x p) (fourBasis.repr (retainedSwap x) p)
  have hF : Summable F := lp.summable_inner _ _
  have hFr : Summable (F ∘ environmentFirst.symm) := environmentFirst.symm.summable_iff.mpr hF
  have hrow (jk : ℕ × ℕ) :
      (∑' mn : ℕ × ℕ, F (environmentFirst.symm (jk, mn))) =
        (‖inner ℂ (w jk.1) (w jk.2)‖ ^ 2 : ℂ) := by
    have hleft : HasSum (fun m => inner ℂ (w jk.1 m) (w jk.2 m))
        (inner ℂ (w jk.1) (w jk.2)) := lp.hasSum_inner _ _
    have hright : HasSum (fun m => inner ℂ (w jk.2 m) (w jk.1 m))
        (inner ℂ (w jk.2) (w jk.1)) := lp.hasSum_inner _ _
    have hmul := tsum_mul_tsum_of_summable_norm hleft.summable.norm hright.summable.norm
    have hterm (mn : ℕ × ℕ) : F (environmentFirst.symm (jk, mn)) =
        inner ℂ (w jk.1 mn.1) (w jk.2 mn.1) *
          inner ℂ (w jk.2 mn.2) (w jk.1 mn.2) := by
      dsimp only [F, x]
      rw [show retainedSwap = fourPermutation retainedPermutation from rfl,
        four_permutation_repr, four_basis_product, four_basis_product]
      simp only [fock_basis_repr]
      change inner ℂ (w jk.1 mn.1 * w jk.2 mn.2)
        (w jk.1 mn.2 * w jk.2 mn.1) = _
      simp only [RCLike.inner_apply, map_mul]
      ring
    simp_rw [hterm]
    rw [← hmul, hleft.tsum_eq, hright.tsum_eq]
    rw [← inner_conj_symm (w jk.2) (w jk.1), RCLike.mul_conj]
    norm_cast
  calc
    _ = ∑' p, F p := by
      rw [← fourBasis.repr.inner_map_map, lp.inner_eq_tsum]
    _ = ∑' p, F (environmentFirst.symm p) := (environmentFirst.symm.tsum_eq F).symm
    _ = ∑' jk, ∑' mn, F (environmentFirst.symm (jk, mn)) := hFr.tsum_prod
    _ = _ := tsum_congr hrow

#print axioms retained_swap_gram

/-- Trace class of the actual square, used without a finite-rank premise. -/
private theorem reduced_square_traceClass (w : H2) :
    IsTraceClass (DisplacementCovariance.purePartialTrace w ^ 2) := by
  simpa only [pow_two, mul_one] using isTraceClass_mul_mul
    (A := DisplacementCovariance.purePartialTrace w) (B := 1)
    (partial_trace_positive_traceClass w).2

private theorem reduced_square_gram (w : H2) :
    trace (DisplacementCovariance.purePartialTrace w ^ 2) (reduced_square_traceClass w) =
      ∑' jk : ℕ × ℕ, (‖inner ℂ (w jk.1) (w jk.2)‖ ^ 2 : ℂ) := by
  let C := coefficientOperator w
  let D : H →L[ℂ] H := star C * C
  have hC : IsHilbertSchmidt C := coefficient_hs w
  have hD : IsTraceClass D := isTraceClass_star_mul_self_of_isHilbertSchmidt hC
  have hDHS : IsHilbertSchmidt D := isHilbertSchmidt_mul_left hC
  have hD2 : IsTraceClass (D ^ 2) := by
    simpa only [pow_two, mul_one] using isTraceClass_mul_mul (A := D) (B := 1) hD
  have hDs : IsSelfAdjoint D := IsSelfAdjoint.of_nonneg (star_mul_self_nonneg C)
  let e : ℕ ≃ Set.range oneBasis :=
    Equiv.ofInjective oneBasis oneBasis.orthonormal.linearIndependent.injective
  obtain ⟨b, hb⟩ := reindex_basis oneBasis e.symm
  have hdiag (i : Set.range oneBasis) : inner ℂ (b i) ((D ^ 2) (b i)) =
      (‖D (b i)‖ ^ 2 : ℂ) := by
    have hadj : ContinuousLinearMap.adjoint D = D :=
      (ContinuousLinearMap.star_eq_adjoint D).symm.trans hDs
    calc
      _ = inner ℂ (b i) (ContinuousLinearMap.adjoint D (D (b i))) := by
        rw [hadj, pow_two, ContinuousLinearMap.mul_apply]
      _ = inner ℂ (D (b i)) (D (b i)) :=
        ContinuousLinearMap.adjoint_inner_right D _ _
      _ = _ := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have hd := (summable_trace_diagonal_of_isTraceClass hD2 b).hasSum
  rw [← trace_eq_of_hilbertBasis hD2 b] at hd
  have hd' : HasSum (fun n : ℕ => (‖D (oneBasis n)‖ ^ 2 : ℂ)) (trace (D ^ 2) hD2) := by
    apply HasSum.congr_fun (e.hasSum_iff.mpr hd)
    intro n
    change (‖D (oneBasis n)‖ ^ 2 : ℂ) =
      inner ℂ (b (e n)) ((D ^ 2) (b (e n)))
    rw [hdiag, hb, Equiv.symm_apply_apply]
  have hnorm : Summable (fun n : ℕ => ‖D (oneBasis n)‖ ^ 2) := by
    have hn := e.summable_iff.mpr
      (summable_norm_sq_apply_of_hilbertBasis (Set.range oneBasis) b hDHS)
    apply hn.congr
    intro n
    change ‖D (b (e n))‖ ^ 2 = _
    rw [hb, Equiv.symm_apply_apply]
  have hcol (n : ℕ) : C (oneBasis n) = w n := coefficient_column w n
  have hmatrix (n k : ℕ) : oneBasis.repr (D (oneBasis n)) k = inner ℂ (w k) (w n) := by
    rw [HilbertBasis.repr_apply_apply]
    change inner ℂ (oneBasis k) ((star C * C) (oneBasis n)) = _
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, hcol, hcol]
  have hrow (n : ℕ) : HasSum (fun k => ‖inner ℂ (w k) (w n)‖ ^ 2)
      (‖D (oneBasis n)‖ ^ 2) := by
    have hh := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num)
      (oneBasis.repr (D (oneBasis n)))
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hmatrix,
      LinearIsometryEquiv.norm_map] using hh
  have hjoint : Summable (fun nk : ℕ × ℕ => ‖inner ℂ (w nk.2) (w nk.1)‖ ^ 2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun n => (hrow n).summable, ?_⟩
    simpa only [(hrow _).tsum_eq] using hnorm
  have htraceGram : trace (D ^ 2) hD2 =
      ∑' jk : ℕ × ℕ, (‖inner ℂ (w jk.1) (w jk.2)‖ ^ 2 : ℂ) := by
    calc
      _ = ∑' n, (‖D (oneBasis n)‖ ^ 2 : ℂ) := hd'.tsum_eq.symm
      _ = ∑' n, ∑' k, (‖inner ℂ (w k) (w n)‖ ^ 2 : ℂ) := by
        apply tsum_congr
        intro n
        simpa only [Complex.ofReal_pow] using
          (Complex.hasSum_ofReal.mpr (hrow n)).tsum_eq.symm
      _ = ∑' nk : ℕ × ℕ, (‖inner ℂ (w nk.2) (w nk.1)‖ ^ 2 : ℂ) :=
        by simpa only [Complex.ofReal_pow] using
          (Complex.hasSum_ofReal.mpr hjoint.hasSum).summable.tsum_prod.symm
      _ = _ := by
        apply tsum_congr
        intro jk
        rw [norm_inner_symm]
  have hright : IsTraceClass (D * star C) := by
    simpa only [one_mul] using isTraceClass_mul_mul (A := 1) (B := star C) hD
  have hcycle := trace_mul_cycle (A := C) hright
  have htrace : trace (DisplacementCovariance.purePartialTrace w ^ 2)
      (reduced_square_traceClass w) = trace (D ^ 2) hD2 := by
    simpa only [D, ← coefficient_mul_adjoint, pow_two, mul_assoc] using hcycle
  exact htrace.trans htraceGram

/-- The trace-square/retained-swap identity for the actual completed reduced
operator. Both sides use the original vector, without an assumed purity bound. -/
theorem partial_trace_square_swap (w : H2) :
    trace (DisplacementCovariance.purePartialTrace w ^ 2) (reduced_square_traceClass w) =
      inner ℂ ((w ⊗ₜ[ℂ] w : H2 ⊗[ℂ] H2) : FourModes)
        (retainedSwap ((w ⊗ₜ[ℂ] w : H2 ⊗[ℂ] H2) : FourModes)) := by
  rw [retained_swap_gram]
  exact reduced_square_gram w

#print axioms partial_trace_square_swap

/-- All-input purity of the actual completed balanced Fock-two output. The
input can have arbitrary infinite support, and zero input is included. -/
theorem balanced_fock_two_purity (a : H) :
    (trace (DisplacementCovariance.purePartialTrace (balancedFockTwoOutput a) ^ 2)
      (reduced_square_traceClass _)).re ≤ (3 / 8) * ‖a‖ ^ 4 := by
  let e : H := lp.single 2 2 1
  let b : H2 := tensor a e
  let u : FourModes := ((b ⊗ₜ[ℂ] b : H2 ⊗[ℂ] H2) : FourModes)
  let x : FourModes := ((balancedFockTwoOutput a ⊗ₜ[ℂ] balancedFockTwoOutput a :
    H2 ⊗[ℂ] H2) : FourModes)
  let v : H2 := relativeUnitary (tensor a a)
  have hx : pairMap balancedUnitary u = x := by
    rw [pair_map_product, balanced_is_published]
    rfl
  have hinv : pairMap relativeUnitary x = u := by
    rw [← hx, pair_map_product, pair_map_product, relative_balanced]
  have hu : centerDifference u =
      ((v ⊗ₜ[ℂ] TwoCopyEnvironment.rotatedEnvironment : H2 ⊗[ℂ] H2) : FourModes) := by
    change pairMap relativeUnitary (regroup u) = _
    rw [show u = ((tensor a e ⊗ₜ[ℂ] tensor a e : H2 ⊗[ℂ] H2) : FourModes) from rfl,
      regroup_product, pair_map_product]
    change ((v ⊗ₜ[ℂ] relativeUnitary (fockPair 2 2) : H2 ⊗[ℂ] H2) : FourModes) = _
    rw [relative_environment]
  have hswap : centerDifference (pairMap relativeUnitary (retainedSwap x)) =
      differenceSwap (centerDifference u) := by
    have h := congrArg (fun L : FourModes →L[ℂ] FourModes => L u)
      balanced_swap_conjugation
    change centerDifference (pairMap relativeUnitary
      (retainedSwap (pairMap balancedUnitary u))) =
        differenceSwap (centerDifference u) at h
    simpa only [hx] using h
  have hexpect : inner ℂ x (retainedSwap x) =
      inner ℂ (centerDifference u) (differenceSwap (centerDifference u)) := by
    calc
      _ = inner ℂ (pairMap relativeUnitary x)
          (pairMap relativeUnitary (retainedSwap x)) :=
        (pair_map_inner relativeUnitary _ _).symm
      _ = inner ℂ (centerDifference (pairMap relativeUnitary x))
          (centerDifference (pairMap relativeUnitary (retainedSwap x))) :=
        (center_difference_inner _ _).symm
      _ = _ := by rw [hinv, hswap]
  have hnorm : ‖v‖ ^ 2 = ‖a‖ ^ 4 := by
    rw [show v = relativeUnitary (tensor a a) from rfl, LinearIsometryEquiv.norm_map]
    rw [tensor_norm_sq]
    ring
  rw [partial_trace_square_swap]
  change (inner ℂ x (retainedSwap x)).re ≤ _
  rw [hexpect, hu]
  simpa only [hnorm] using difference_swap_compression v

#print axioms balanced_fock_two_purity

end D5.S3.Quantum.QuantumChannels.FockAttenuator.CompletedTwoCopySwap
