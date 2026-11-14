/- GID: D5/S3/Quantum/Measurements/RelevantSpaceQuantumKac
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/RelevantSpaceQuantumKac
   mirror-E: none(waiver:finite-dimensional-operator-theorem)
   anchors: []
   utility: none
   digest: Faithful finite monitored orbits give contraction on the actual relevant space. -/

import D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Kraus words and projection monitoring on their actual reachable space. -/

noncomputable section

open Matrix Filter Topology
open D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace

namespace D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {n : Type*} {α : Type} [Fintype n] [DecidableEq n]

private theorem reachable_le_of_invariant (K : α → Matrix n n ℂ)
    (ρ : Matrix n n ℂ) (S : Submodule ℂ (EuclideanSpace ℂ n))
    (hρ : matrixSupport ρ ≤ S)
    (hK : ∀ a, ∀ v ∈ S, (K a).toEuclideanLin v ∈ S) :
    reachableSpace K ρ ≤ S := by
  apply iSup_le
  intro l
  apply Submodule.span_le.mpr
  rintro y ⟨w, _hw, v, hv, rfl⟩
  have hw : ∀ w : List α, (krausWord K w).toEuclideanLin v ∈ S := by
    intro w
    induction w with
    | nil => simpa [krausWord, Matrix.toEuclideanLin, Matrix.toLpLin_one] using hρ hv
    | cons a w ih =>
        simpa only [krausWord, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
          LinearMap.comp_apply] using hK a _ ih
  exact hw w

/-- The original Kraus family and its actual no-return branches generate the
same reachable space. This holds for every Hermitian initial matrix `P`;
the pure-state projection case is Appendix A, equation (A9). -/
theorem monitored_reachable_space_eq (K : α → Matrix n n ℂ)
    (P : Matrix n n ℂ) (hP : P.IsHermitian) :
    reachableSpace (fun a => (1 - P) * K a) P = reachableSpace K P := by
  have hinitial (J : α → Matrix n n ℂ) : matrixSupport P ≤ reachableSpace J P := by
    apply le_iSup_of_le 0
    intro v hv
    exact Submodule.subset_span ⟨[], by simp, v, hv,
      by simp [krausWord, Matrix.toEuclideanLin, Matrix.toLpLin_one]⟩
  have hPmap (J : α → Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
      P.toEuclideanLin v ∈ reachableSpace J P := by
    apply hinitial J
    rw [matrixSupport_eq_range hP]
    exact ⟨v, rfl⟩
  apply le_antisymm
  · apply reachable_le_of_invariant _ _ _ (hinitial K)
    intro a v hv
    have hKv := reachable_kraus_invariant K P a v hv
    have hsub := (reachableSpace K P).sub_mem hKv (hPmap K ((K a).toEuclideanLin v))
    simpa only [sub_mul, one_mul, map_sub, Matrix.toEuclideanLin,
      Matrix.toLpLin_mul_same, LinearMap.sub_apply, LinearMap.comp_apply] using hsub
  · apply reachable_le_of_invariant _ _ _ (hinitial (fun a => (1 - P) * K a))
    intro a v hv
    have hQv := reachable_kraus_invariant (fun a => (1 - P) * K a) P a v hv
    have hsum := (reachableSpace (fun a => (1 - P) * K a) P).add_mem hQv
      (hPmap (fun a => (1 - P) * K a) ((K a).toEuclideanLin v))
    simpa only [sub_mul, one_mul, map_sub, Matrix.toEuclideanLin,
      Matrix.toLpLin_mul_same, LinearMap.sub_apply, LinearMap.comp_apply,
      sub_add_cancel] using hsum

private theorem support_coercivity_order (R PiC : Matrix n n ℂ)
    (hR : R.PosSemidef) (C : Submodule ℂ (EuclideanSpace ℂ n))
    (hC : matrixSupport R = C)
    (hPiC : PiC.toEuclideanLin = C.starProjection.toLinearMap)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hb : ∀ x ∈ C, μ * ‖x‖ ^ 2 ≤ (inner ℂ x (R.toEuclideanLin x)).re) :
    (μ : ℂ) • PiC ≤ R := by
  have hPiCpos : PiC.PosSemidef := by
    rw [← Matrix.isPositive_toEuclideanLin_iff, hPiC]
    exact C.isSymmetricProjection_starProjection.isPositive
  have horth : Cᗮ = LinearMap.ker R.toEuclideanLin := by
    rw [← hC, matrixSupport, Submodule.orthogonal_orthogonal]
  have hproject (x : EuclideanSpace ℂ n) :
      R.toEuclideanLin x = R.toEuclideanLin (C.starProjection x) := by
    have hz : R.toEuclideanLin (x - C.starProjection x) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [← horth]
      exact C.sub_starProjection_mem_orthogonal x
    simpa only [map_sub, sub_eq_zero] using hz
  have hrange (x : EuclideanSpace ℂ n) : R.toEuclideanLin x ∈ C := by
    rw [← hC, matrixSupport_eq_range hR.isHermitian]
    exact ⟨x, rfl⟩
  rw [Matrix.le_iff, ← Matrix.isPositive_toEuclideanLin_iff]
  refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (hR.isHermitian.sub ((hPiCpos.smul (Complex.zero_le_real.mpr hμ)).isHermitian)), ?_⟩
  intro x
  let y := C.starProjection x
  have hRy : C.starProjection (R.toEuclideanLin y) = R.toEuclideanLin y :=
    C.starProjection_eq_self_iff.mpr (hrange y)
  have hqR : inner ℂ x (R.toEuclideanLin x) = inner ℂ y (R.toEuclideanLin y) := by
    calc
      _ = inner ℂ x (R.toEuclideanLin y) := by rw [hproject x]
      _ = inner ℂ x (C.starProjection (R.toEuclideanLin y)) := by rw [hRy]
      _ = inner ℂ y (R.toEuclideanLin y) :=
        (C.inner_starProjection_left_eq_right x (R.toEuclideanLin y)).symm
  have hqPiC : (inner ℂ x (PiC.toEuclideanLin x)).re = ‖y‖ ^ 2 := by
    rw [hPiC]
    change (inner ℂ x (C.starProjection x)).re = ‖y‖ ^ 2
    have hh := C.inner_starProjection_left_eq_right x (C.starProjection x)
    rw [C.starProjection_eq_self_iff.mpr (C.starProjection_apply_mem x)] at hh
    rw [← hh]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have h := hb y (C.starProjection_apply_mem x)
  rw [inner_re_symm]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    inner_sub_right, inner_smul_right, RCLike.re_eq_complex_re,
    Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hqR, hqPiC]
  linarith

open scoped Matrix.Norms.Elementwise in
private theorem hasSum_of_positive_block (K : α → Matrix n n ℂ) [Fintype α]
    (c : α → ℝ) (hc : ∀ a, 0 ≤ c a) (P PiC : Matrix n n ℂ)
    (hP : P.PosSemidef) (hPiC : PiC.PosSemidef)
    (hstep : weightedCP K c PiC = PiC - P)
    (N : ℕ) (hN : 1 ≤ N) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hblock : (weightedCP K c)^[N] PiC ≤ (q : ℂ) • PiC) :
    HasSum (fun k => (weightedCP K c)^[k] P) PiC := by
  let T := weightedCP K c
  have hm : Monotone T := weightedCP_mono K c hc
  have hscale {A B : Matrix n n ℂ} (h : A ≤ B) (r : ℝ) (hr : 0 ≤ r) :
      (r : ℂ) • A ≤ (r : ℂ) • B := by
    rw [Matrix.le_iff, ← smul_sub]
    exact (Matrix.le_iff.mp h).smul (Complex.zero_le_real.mpr hr)
  have hpos (k : ℕ) (X : Matrix n n ℂ) (hX : X.PosSemidef) :
      (T^[k] X).PosSemidef := by
    induction k with
    | zero => exact hX
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact weightedCP_psd K c hc ih
  have hTI : T PiC ≤ PiC := by
    rw [hstep, sub_le_self_iff]
    exact Matrix.nonneg_iff_posSemidef.mpr hP
  have hPI : P ≤ PiC := by
    have h := Matrix.nonneg_iff_posSemidef.mpr (hpos 1 PiC hPiC)
    change 0 ≤ T PiC at h
    rw [hstep, sub_nonneg] at h
    exact h
  have hanti : Antitone (fun k => T^[k] PiC) := by
    apply antitone_nat_of_succ_le
    intro k
    rw [Function.iterate_succ_apply]
    exact (hm.iterate k) hTI
  have hb (j : ℕ) : T^[j * N] PiC ≤ ((q ^ j : ℝ) : ℂ) • PiC := by
    induction j with
    | zero => simp
    | succ j ih =>
        rw [Nat.succ_mul, Nat.add_comm, Function.iterate_add_apply]
        calc
          T^[N] (T^[j * N] PiC) ≤ T^[N] (((q ^ j : ℝ) : ℂ) • PiC) :=
            (hm.iterate N) ih
          _ = ((q ^ j : ℝ) : ℂ) • T^[N] PiC := by
            simpa only [Module.End.pow_apply] using (T ^ N).map_smul ((q ^ j : ℝ) : ℂ) PiC
          _ ≤ ((q ^ j : ℝ) : ℂ) • ((q : ℂ) • PiC) :=
            hscale hblock (q ^ j) (pow_nonneg hq j)
          _ = ((q ^ (j + 1) : ℝ) : ℂ) • PiC := by
            rw [smul_smul, pow_succ, Complex.ofReal_mul]
  have hall (k : ℕ) : T^[k] PiC ≤ ((q ^ (k / N) : ℝ) : ℂ) • PiC :=
    (hanti (Nat.div_mul_le_self k N)).trans (hb (k / N))
  have htrace {A B : Matrix n n ℂ} (h : A ≤ B) : A.trace.re ≤ B.trace.re := by
    have ht := (Complex.nonneg_iff.mp (Matrix.le_iff.mp h).trace_nonneg).1
    simp only [Matrix.trace_sub, Complex.sub_re] at ht
    linarith
  have hbound (k : ℕ) : (T^[k] PiC).trace.re ≤ q ^ (k / N) * PiC.trace.re := by
    simpa only [Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using htrace (hall k)
  have htrlim := geometric_trace_tendsto K c hc PiC hPiC N hN q hq hq1 hbound
  have hnormlim : Tendsto (fun k => ‖T^[k] PiC‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _)
      (fun k => psd_norm_le_trace _ (hpos k PiC hPiC)) htrlim
  have hlim : Tendsto (fun k => T^[k] PiC) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnormlim
  have htel (k : ℕ) : ∑ j ∈ Finset.range k, T^[j] P = PiC - T^[k] PiC := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih, Function.iterate_succ_apply]
        have hlin : T^[k] (PiC - P) = T^[k] PiC - T^[k] P := by
          simpa only [Module.End.pow_apply] using (T ^ k).map_sub PiC P
        rw [hstep, hlin]
        abel
  have hpart : Tendsto (fun k => ∑ j ∈ Finset.range k, T^[j] P) atTop (𝓝 PiC) := by
    simp_rw [htel]
    simpa using tendsto_const_nhds.sub hlim
  have hsI := geometric_orbit_summable K c hc PiC hPiC N hN q hq hq1 hbound
  have hsP : Summable (fun k => T^[k] P) := by
    have hst : Summable (fun k => (T^[k] PiC).trace.re) :=
      (Complex.hasSum_re (hsI.hasSum.mapL
        (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n ℂ ℂ)))).summable
    apply hst.of_norm_bounded
    intro k
    exact (psd_norm_le_trace _ (hpos k P hP)).trans
      (htrace ((hm.iterate k) hPI))
  have heq := tendsto_nhds_unique hsP.hasSum.tendsto_sum_nat hpart
  exact heq ▸ hsP.hasSum

/-- The actual monitored orbit sums to the projection onto the original
Kraus reachable space. The initial matrix may be a projection of any rank.
Unitality is required only on that reachable space; trace preservation is
not needed for this operator identity. -/
theorem relevant_projection_hasSum (K : α → Matrix n n ℂ) [Fintype α]
    (P PiC : Matrix n n ℂ) (hP : P.PosSemidef) (hPP : P * P = P)
    (hPiC : PiC.toEuclideanLin = (reachableSpace K P).starProjection.toLinearMap)
    (hunital : weightedCP K (fun _ => 1) PiC = PiC) :
    HasSum (fun k => (weightedCP (fun a => (1 - P) * K a) (fun _ => 1))^[k] P) PiC := by
  let C := reachableSpace K P
  let J : α → Matrix n n ℂ := fun a => (1 - P) * K a
  let T := weightedCP J (fun _ => 1)
  have hPiCpos : PiC.PosSemidef := by
    rw [← Matrix.isPositive_toEuclideanLin_iff, hPiC]
    exact C.isSymmetricProjection_starProjection.isPositive
  have hinit : matrixSupport P ≤ C := by
    apply le_iSup_of_le 0
    intro x hx
    exact Submodule.subset_span ⟨[], by simp, x, hx,
      by simp [krausWord, Matrix.toEuclideanLin, Matrix.toLpLin_one]⟩
  have hPiCP : PiC * P = P := by
    apply Matrix.toEuclideanLin.injective
    apply LinearMap.ext
    intro x
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
    change PiC.toEuclideanLin (P.toEuclideanLin x) = P.toEuclideanLin x
    rw [hPiC]
    apply C.starProjection_eq_self_iff.mpr
    apply hinit
    rw [matrixSupport_eq_range hP.isHermitian]
    exact ⟨x, rfl⟩
  have hPPiC : P * PiC = P := by
    have h := congrArg Matrix.conjTranspose hPiCP
    simpa [Matrix.conjTranspose_mul, hP.isHermitian.eq, hPiCpos.isHermitian.eq] using h
  have hmon (X : Matrix n n ℂ) :
      T X = (1 - P) * weightedCP K (fun _ => 1) X * (1 - P) := by
    simp only [T, J, weightedCP, LinearMap.coe_mk, AddHom.coe_mk,
      Complex.ofReal_one, one_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.isHermitian.eq,
      Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  have hstep : T PiC = PiC - P := by
    rw [hmon, hunital, sub_mul, one_mul, hPPiC, mul_sub, mul_one,
      sub_mul, hPiCP, hPP]
    abel
  obtain ⟨L, μ, hμ, hs, hb⟩ := finite_reachable_faithful_sum J (fun _ => 1)
    (fun _ => by norm_num) P hP
  have hC : reachableSpace J P = C := monitored_reachable_space_eq K P hP.isHermitian
  let ν : ℝ := min μ (1 / 2)
  have hν : 0 < ν := lt_min hμ (by norm_num)
  have hνμ : ν ≤ μ := min_le_left _ _
  have hν1 : ν ≤ 1 / 2 := min_le_right _ _
  have hRpos : (orbitSum J (fun _ => 1) P L).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro k _
    suffices ∀ k, ((weightedCP J (fun _ => 1))^[k] P).PosSemidef from this k
    intro k
    induction k with
    | zero => exact hP
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact weightedCP_psd J _ (fun _ => by norm_num) ih
  have hcoercive : (ν : ℂ) • PiC ≤ orbitSum J (fun _ => 1) P L := by
    apply support_coercivity_order _ PiC hRpos C (hs.trans hC) hPiC ν hν.le
    intro x hx
    exact (mul_le_mul_of_nonneg_right hνμ (sq_nonneg ‖x‖)).trans
      (hb x (hC.symm ▸ hx))
  have htel (k : ℕ) : ∑ j ∈ Finset.range k, T^[j] P = PiC - T^[k] PiC := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih, Function.iterate_succ_apply, hstep]
        have hlin : T^[k] (PiC - P) = T^[k] PiC - T^[k] P := by
          simpa only [Module.End.pow_apply] using (T ^ k).map_sub PiC P
        rw [hlin]
        abel
  have hblock : T^[L + 1] PiC ≤ ((1 - ν : ℝ) : ℂ) • PiC := by
    change (ν : ℂ) • PiC ≤ ∑ j ∈ Finset.range (L + 1), T^[j] P at hcoercive
    rw [htel] at hcoercive
    have hr : ((1 - ν : ℝ) : ℂ) • PiC = PiC - (ν : ℂ) • PiC := by
      rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    rw [hr]
    exact le_sub_iff_add_le.mpr (by
      simpa [add_comm] using (le_sub_iff_add_le.mp hcoercive))
  exact hasSum_of_positive_block J (fun _ => 1) (fun _ => by norm_num)
    P PiC hP hPiCpos hstep (L + 1) (by omega) (1 - ν)
    (by linarith) (by linarith) hblock

private theorem survival_difference_moments (s : ℕ → ℝ) (a : ℝ)
    (hs : HasSum s a) (hanti : Antitone s) :
    HasSum (fun k => s k - s (k + 1)) (s 0) ∧
      HasSum (fun k => (k + 1 : ℝ) * (s k - s (k + 1))) a := by
  classical
  let p : ℕ → ℝ := fun k => s k - s (k + 1)
  have hp : ∀ k, 0 ≤ p k := fun k => sub_nonneg.mpr (hanti (Nat.le_succ k))
  have hps : Summable p := hs.summable.sub ((summable_nat_add_iff 1).mpr hs.summable)
  have htail (i : ℕ) : HasSum (fun k => p (k + i)) (s i) := by
    have hshift := (hasSum_nat_add_iff' i).mpr hs
    have hshift' := (hasSum_nat_add_iff' (i + 1)).mpr hs
    have hh := hshift.sub hshift'
    have heq : a - ∑ k ∈ Finset.range i, s k -
        (a - ∑ k ∈ Finset.range (i + 1), s k) = s i := by
      rw [Finset.sum_range_succ]
      ring
    rw [heq] at hh
    simpa only [p, Nat.add_assoc] using hh
  let f : ℕ × ℕ → ℝ := fun z => if z.1 ≤ z.2 then p z.2 else 0
  have hrow (i : ℕ) : HasSum (fun j => f (i, j)) (s i) := by
    apply (hasSum_nat_add_iff' i).mp
    have hzero : ∑ j ∈ Finset.range i, f (i, j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [f, if_neg (Nat.not_le.mpr (Finset.mem_range.mp hj))]
    rw [hzero, sub_zero]
    simpa only [f, Nat.le_add_left, ite_true] using htail i
  have hf : Summable f := (summable_prod_of_nonneg (fun z => by
    dsimp [f]
    split_ifs
    · exact hp _
    · exact le_rfl)).mpr ⟨fun i => (hrow i).summable, by
      simpa only [(hrow _).tsum_eq] using hs.summable⟩
  have htotal : HasSum f a := by
    have hh := hf.hasSum.prod_fiberwise hrow
    exact hh.unique hs ▸ hf.hasSum
  have hcol (j : ℕ) : HasSum (fun i => f (i, j)) ((j + 1 : ℝ) * p j) := by
    have heq : (fun i => f (i, j)) =
        fun i => if i ∈ Finset.range (j + 1) then p j else 0 := by
      funext i
      simp only [f, Finset.mem_range, Nat.lt_succ_iff]
    rw [heq]
    have hh := hasSum_sum_of_ne_finset_zero (s := Finset.range (j + 1))
      (f := fun i => if i ∈ Finset.range (j + 1) then p j else 0)
      (fun i hi => by simp only [if_neg hi])
    have hval : (∑ i ∈ Finset.range (j + 1),
        if i ∈ Finset.range (j + 1) then p j else 0) = (j + 1 : ℝ) * p j := by
      calc
        _ = ∑ _i ∈ Finset.range (j + 1), p j :=
          Finset.sum_congr rfl (fun i hi => if_pos hi)
        _ = _ := by simp
    exact hval ▸ hh
  refine ⟨by simpa only [Nat.add_zero] using htail 0, ?_⟩
  have hswap : HasSum (fun z : ℕ × ℕ => f (z.2, z.1)) a :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr htotal
  exact hswap.prod_fiberwise hcol

private theorem projection_trace (C : Submodule ℂ (EuclideanSpace ℂ n))
    (PiC : Matrix n n ℂ)
    (hPiC : PiC.toEuclideanLin = C.starProjection.toLinearMap) :
    PiC.trace = (Module.finrank ℂ C : ℂ) := by
  have ht : LinearMap.trace ℂ _ PiC.toEuclideanLin = PiC.trace := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact PiC.trace_toLin_eq _
  rw [← ht, hPiC]
  have hi := C.isIdempotentElem_starProjection.toLinearMap.isProj_range.trace
  have hr : LinearMap.range C.starProjection.toLinearMap = C := C.range_starProjection
  simpa only [hr] using hi

/-- Quantum Kac for the actual monitored Kraus history. The dimension is that
of the original reachable space, and the channel need only fix its projection. -/
theorem relevant_space_quantum_kac (K : α → Matrix n n ℂ) [Fintype α]
    (P PiC : Matrix n n ℂ) (hP : P.PosSemidef) (hPP : P * P = P)
    (htrP : P.trace = 1)
    (hTP : ∑ a, (K a)ᴴ * K a = 1)
    (hPiC : PiC.toEuclideanLin = (reachableSpace K P).starProjection.toLinearMap)
    (hunital : weightedCP K (fun _ => 1) PiC = PiC) :
    let E := weightedCP K (fun _ => 1)
    let F := weightedCP (fun a => (1 - P) * K a) (fun _ => 1)
    let p := fun k => (P * E (F^[k] P)).trace.re
    HasSum (fun k => F^[k] P) PiC ∧ (∀ k, 0 ≤ p k) ∧
      HasSum p 1 ∧ HasSum (fun k => (k + 1 : ℝ) * p k)
        (Module.finrank ℂ (reachableSpace K P) : ℝ) := by
  classical
  dsimp only
  let E := weightedCP K (fun _ => 1)
  let F := weightedCP (fun a => (1 - P) * K a) (fun _ => 1)
  let s : ℕ → ℝ := fun k => (F^[k] P).trace.re
  have hseries := relevant_projection_hasSum K P PiC hP hPP hPiC hunital
  have hmon (X : Matrix n n ℂ) : F X = (1 - P) * E X * (1 - P) := by
    simp only [F, E, weightedCP, LinearMap.coe_mk, AddHom.coe_mk,
      Complex.ofReal_one, one_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.isHermitian.eq,
      Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  have htp (X : Matrix n n ℂ) : (E X).trace = X.trace := by
    simp only [E, weightedCP, LinearMap.coe_mk, AddHom.coe_mk,
      Complex.ofReal_one, one_smul, Matrix.trace_sum]
    simp_rw [Matrix.trace_mul_cycle]
    rw [← Matrix.trace_sum, ← Matrix.sum_mul, hTP, Matrix.one_mul]
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hPP]
    abel
  have hloss (k : ℕ) : (P * E (F^[k] P)).trace.re = s k - s (k + 1) := by
    have ht : (F (F^[k] P)).trace = (E (F^[k] P)).trace -
        (P * E (F^[k] P)).trace := by
      rw [hmon, Matrix.trace_mul_cycle, hQ,
        Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub]
    rw [htp] at ht
    dsimp [s]
    rw [Function.iterate_succ_apply', ht, Complex.sub_re]
    ring
  have hpos (k : ℕ) : (F^[k] P).PosSemidef := by
    induction k with
    | zero => exact hP
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact weightedCP_psd _ _ (fun _ => by norm_num) ih
  have hp (k : ℕ) : 0 ≤ (P * E (F^[k] P)).trace.re := by
    have hh := (weightedCP_psd K (fun _ => 1) (fun _ => by norm_num)
      (hpos k)).mul_mul_conjTranspose_same P
    have ht := hh.trace_nonneg
    have heq : (P * E (F^[k] P) * Pᴴ).trace = (P * E (F^[k] P)).trace := by
      rw [hP.isHermitian.eq, Matrix.trace_mul_cycle, hPP]
    rw [heq] at ht
    exact (Complex.nonneg_iff.mp ht).1
  have hs : HasSum s PiC.trace.re :=
    Complex.hasSum_re (hseries.mapL
      (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n ℂ ℂ)))
  have hanti : Antitone s := by
    apply antitone_nat_of_succ_le
    intro k
    exact sub_nonneg.mp ((hloss k) ▸ hp k)
  have hm := survival_difference_moments s PiC.trace.re hs hanti
  have hs0 : s 0 = 1 := by simp [s, htrP]
  have hdim : PiC.trace.re = (Module.finrank ℂ (reachableSpace K P) : ℝ) := by
    rw [projection_trace _ PiC hPiC]
    simp
  refine ⟨hseries, hp, ?_, ?_⟩
  · simpa only [hloss, hs0] using hm.1
  · simpa only [hloss, hdim] using hm.2

#print axioms monitored_reachable_space_eq
#print axioms relevant_projection_hasSum
#print axioms relevant_space_quantum_kac

end D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac
