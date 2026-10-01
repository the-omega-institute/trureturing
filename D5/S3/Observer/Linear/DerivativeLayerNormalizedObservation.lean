/- GID: D5/S3/Observer/Linear/DerivativeLayerNormalizedObservation
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Algebra.Exponential, mathlib/module/Mathlib.Analysis.InnerProductSpace.Projection.Basic]
   utility: none
   digest: Resolve the actual derivative filtration and uniformly approximate its all-layer normalized exponential observation. -/

import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

/-!
The finite derivative kernels determine the layers and projections used below.
The result includes their resolution on the observable complement and a single
uniform bound for the complete normalized observation, including empty layers.
Utility is none: this is a symbolic orthogonal-filtration and analytic estimate,
not a finite enumeration, checker, numerical reduction, or certified instance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.Linear.DerivativeLayerNormalizedObservation

open ContinuousLinearMap Finset
open scoped Function InnerProductSpace RealInnerProductSpace ENNReal NNReal

/-- The actual derivative layers resolve the observable complement, and the
normalized exponential observation converges there at a uniform linear rate. -/
theorem derivative_layer_normalized_observation
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (B : V →ₗ[ℝ] V) (C : V →ₗ[ℝ] W) :
    let n := Module.finrank ℝ V
    let N : ℕ → Submodule ℝ V := fun j =>
      ⨅ k : Fin j, LinearMap.ker (C.comp (B ^ (k : ℕ)))
    let U : Submodule ℝ V := (N n)ᗮ
    let E : Fin n → Submodule ℝ V := fun j => N j ⊓ (N (j + 1))ᗮ
    let b : V →L[ℝ] V := B.toContinuousLinearMap
    let c : V →L[ℝ] W := C.toContinuousLinearMap
    let L : Fin n → (V →L[ℝ] V) →L[ℝ] (U →L[ℝ] W) := fun j =>
      ((ContinuousLinearMap.compL ℝ U V W) c).comp
        ((ContinuousLinearMap.compL ℝ U V V).flip
          ((E j).starProjection.comp U.subtypeL))
    let F : ℝ → ℝ → U →L[ℝ] W := fun T s =>
      ∑ j : Fin n, (T ^ (j : ℕ))⁻¹ • L j (NormedSpace.exp ((T * s) • b))
    let F₀ : ℝ → U →L[ℝ] W := fun s =>
      ∑ j : Fin n, (s ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) • L j (b ^ (j : ℕ))
    (∀ x : U, (∑ j : Fin n, (E j).starProjection (x : V)) = (x : V)) ∧
      ∃ Ksum : ℝ, 0 ≤ Ksum ∧
        ∀ T : ℝ, 0 < T → T * ‖b‖ < 1 →
          ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖F T s - F₀ s‖ ≤ Ksum * T := by
  classical
  intro n N U E b c L F F₀
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  letI (j : Fin n) : CompleteSpace (E j) := FiniteDimensional.complete ℝ (E j)
  have hN (j : ℕ) (z : V) :
      z ∈ N j ↔ ∀ k : ℕ, k < j → C ((B ^ k) z) = 0 := by
    constructor
    · intro hz k hk
      have hzk := ((Submodule.mem_iInf _).mp hz) (⟨k, hk⟩ : Fin j)
      simpa only [N, LinearMap.mem_ker, LinearMap.comp_apply] using hzk
    · intro hz
      apply (Submodule.mem_iInf _).mpr
      intro k
      exact LinearMap.mem_ker.mpr (hz k k.isLt)
  have hNnest {j k : ℕ} (hjk : j ≤ k) : N k ≤ N j := by
    intro z hz
    exact (hN j z).2 (fun q hq => (hN k z).1 hz q (lt_of_lt_of_le hq hjk))
  have hNzero : N 0 = ⊤ := by
    apply top_unique
    intro z _
    exact (hN 0 z).2 (fun k hk => by omega)
  have hstep (j : ℕ) :
      N (j + 1) ⊔ ((N (j + 1))ᗮ ⊓ N j) = N j := by
    letI : (N (j + 1)).HasOrthogonalProjection :=
      Submodule.HasOrthogonalProjection.ofCompleteSpace _
    exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
      (hNnest (Nat.le_succ j))
  let S : ℕ → Submodule ℝ V := fun m =>
    (Finset.range m).sup (fun j => N j ⊓ (N (j + 1))ᗮ)
  have hspan (m : ℕ) : N 0 = N m ⊔ S m := by
    induction m with
    | zero => simp [S]
    | succ m ih =>
        calc
          N 0 = N m ⊔ S m := ih
          _ = (N (m + 1) ⊔ (N m ⊓ (N (m + 1))ᗮ)) ⊔ S m := by
            rw [inf_comm, hstep]
          _ = N (m + 1) ⊔ S (m + 1) := by
            simp [S, Finset.range_add_one, Finset.sup_insert,
              sup_assoc, sup_comm, sup_left_comm]
  have hS : S n = ⨆ j : Fin n, E j := by
    apply le_antisymm
    · change (Finset.range n).sup (fun j => N j ⊓ (N (j + 1))ᗮ) ≤
        ⨆ j : Fin n, E j
      apply Finset.sup_le
      intro j hj
      exact le_iSup_of_le (⟨j, Finset.mem_range.mp hj⟩ : Fin n) le_rfl
    · apply iSup_le
      intro j
      exact Finset.le_sup (s := Finset.range n) (f := fun k =>
        N k ⊓ (N (k + 1))ᗮ) (Finset.mem_range.mpr j.isLt)
  have htop : N n ⊔ (⨆ j : Fin n, E j) = ⊤ := by
    rw [← hS, ← hspan n, hNzero]
  have hEsub (j : Fin n) : E j ≤ U := by
    have hn : N n ≤ N ((j : ℕ) + 1) := hNnest (Nat.succ_le_of_lt j.isLt)
    exact le_trans inf_le_right (Submodule.orthogonal_le hn)
  have hpair : Pairwise ((· ⟂ ·) on E) := by
    intro i j hij
    have hlt : (i : ℕ) < j ∨ (j : ℕ) < i := lt_or_gt_of_ne (Fin.val_ne_of_ne hij)
    rcases hlt with hlt | hlt
    · apply Submodule.isOrtho_iff_le.mpr
      have hji : N j ≤ N ((i : ℕ) + 1) := hNnest (Nat.succ_le_of_lt hlt)
      exact (le_trans inf_le_right (Submodule.orthogonal_le hji)).trans
        (Submodule.orthogonal_le inf_le_left)
    · apply Submodule.isOrtho_comm.mpr
      apply Submodule.isOrtho_iff_le.mpr
      have hij' : N i ≤ N ((j : ℕ) + 1) := hNnest (Nat.succ_le_of_lt hlt)
      exact (le_trans inf_le_right (Submodule.orthogonal_le hij')).trans
        (Submodule.orthogonal_le inf_le_left)
  have horth : OrthogonalFamily ℝ (fun j => E j)
      (fun j => (E j).subtypeₗᵢ) := OrthogonalFamily.of_pairwise hpair
  have hUsup (x : U) : (x : V) ∈ ⨆ j : Fin n, E j := by
    have hxTop : (x : V) ∈ N n ⊔ (⨆ j : Fin n, E j) := by
      rw [htop]
      trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hxTop
    have hzU : z ∈ U := (iSup_le fun j => hEsub j) hz
    have hyU : y ∈ U := by
      have hyEq : y = (x : V) - z := by rw [← hyz]; abel
      rw [hyEq]
      exact U.sub_mem x.property hzU
    have hy0 : y = 0 := by
      have h : y ∈ N n ⊓ (N n)ᗮ := ⟨hy, hyU⟩
      simpa only [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] using h
    have hzEq : z = (x : V) := by simpa only [hy0, zero_add] using hyz
    rw [← hzEq]
    exact hz
  have hresolve (x : U) :
      (∑ j : Fin n, (E j).starProjection (x : V)) = (x : V) :=
    horth.sum_projection_of_mem_iSup (x : V) (hUsup x)
  have hvanish (j : Fin n) (k : ℕ) (hk : k < (j : ℕ)) :
      L j (b ^ k) = 0 := by
    have hbpow : (b ^ k : V →L[ℝ] V) = (B ^ k).toContinuousLinearMap := by
      change (Module.End.toContinuousLinearMap V B) ^ k =
        Module.End.toContinuousLinearMap V (B ^ k)
      exact (map_pow (Module.End.toContinuousLinearMap V) B k).symm
    rw [hbpow]
    apply ContinuousLinearMap.ext
    intro x
    have hp : (E j).starProjection (x : V) ∈ N (j : ℕ) :=
      ((E j).starProjection_apply_mem (x : V)).1
    have hzero := (hN (j : ℕ) _).1 hp k hk
    change C ((B ^ k) ((E j).starProjection (x : V))) = 0
    exact hzero
  have hall : ∀ j : Fin n, ∃ K : ℝ, 0 ≤ K ∧
      ∀ T : ℝ, 0 < T → T * ‖b‖ < 1 →
        ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖(T ^ (j : ℕ))⁻¹ • L j (NormedSpace.exp ((T * s) • b)) -
            (s ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) • L j (b ^ (j : ℕ))‖ ≤
            K * T := by
    intro j
    let taylor : ℕ → (V →L[ℝ] V) → V →L[ℝ] V := fun m x =>
      ∑ k ∈ Finset.range m, ((Nat.factorial k : ℝ)⁻¹) • x ^ k
    have huniform :
        ∃ a ∈ Set.Ioo (0 : ℝ) 1, ∃ C₀ > 0,
          ∀ (x : V →L[ℝ] V), ‖x‖ < 1 → ∀ m : ℕ,
            ‖NormedSpace.exp x - taylor m x‖ ≤ C₀ * (a * ‖x‖) ^ m := by
      have hr : 0 < (NormedSpace.expSeries ℝ (V →L[ℝ] V)).radius := by
        rw [NormedSpace.expSeries_radius_eq_top]
        exact ENNReal.zero_lt_top
      have hp := NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos hr
      have hball : ((1 : ℝ≥0) : ℝ≥0∞) <
          (NormedSpace.expSeries ℝ (V →L[ℝ] V)).radius := by
        rw [NormedSpace.expSeries_radius_eq_top]
        simp
      obtain ⟨a, ha, C₀, hC, hbound⟩ := hp.uniform_geometric_approx' hball
      refine ⟨a, ha, C₀, hC, ?_⟩
      intro x hx m
      have h := hbound x (by
        simpa only [Metric.mem_ball, dist_zero_right, NNReal.coe_one] using hx) m
      simpa only [zero_add, FormalMultilinearSeries.partialSum,
        NormedSpace.expSeries_apply_eq, NNReal.coe_one, div_one, taylor] using h
    have hfirst (u : ℝ) :
        L j (taylor (j + 1) (u • b)) =
          (u ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) • L j (b ^ (j : ℕ)) := by
      unfold taylor
      rw [map_sum]
      simp only [map_smul, smul_pow, smul_smul]
      have hsum :
          (∑ k ∈ Finset.range (j + 1), ((Nat.factorial k : ℝ)⁻¹ * u ^ k) •
            L j (b ^ k)) =
          ((Nat.factorial (j : ℕ) : ℝ)⁻¹ * u ^ (j : ℕ)) • L j (b ^ (j : ℕ)) := by
        apply Finset.sum_eq_single (j : ℕ)
        · intro k hk hkj
          have hkj' : k < (j : ℕ) := by
            have := Finset.mem_range.mp hk
            omega
          rw [hvanish j k hkj', smul_zero]
        · intro hj
          exact (hj (Finset.mem_range.mpr (Nat.lt_succ_self (j : ℕ)))).elim
      rw [hsum]
      congr 1
      ring
    obtain ⟨a, ha, C₀, hC, hbound⟩ := huniform
    have ha0 : 0 ≤ a := ha.1.le
    have hC0 : 0 ≤ C₀ := hC.le
    let K : ℝ := ‖L j‖ * C₀ * (a * ‖b‖) ^ ((j : ℕ) + 1)
    refine ⟨K, by dsimp [K]; positivity, ?_⟩
    intro T hT hTB s hs
    have hTs : 0 ≤ T * s := mul_nonneg hT.le hs.1
    have hx : ‖(T * s) • b‖ ≤ T * ‖b‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hTs]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right hT.le hs.2) (norm_nonneg _)
    have hrem := hbound ((T * s) • b) (hx.trans_lt hTB) ((j : ℕ) + 1)
    have hb : ‖L j (NormedSpace.exp ((T * s) • b)) -
        ((T * s) ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) • L j (b ^ (j : ℕ))‖ ≤
          ‖L j‖ * C₀ * (a * (T * ‖b‖)) ^ ((j : ℕ) + 1) := by
      rw [← hfirst (T * s), ← map_sub]
      calc
        _ ≤ ‖L j‖ * ‖NormedSpace.exp ((T * s) • b) -
            taylor ((j : ℕ) + 1) ((T * s) • b)‖ := (L j).le_opNorm _
        _ ≤ ‖L j‖ * (C₀ * (a * ‖(T * s) • b‖) ^ ((j : ℕ) + 1)) :=
          mul_le_mul_of_nonneg_left hrem (norm_nonneg _)
        _ ≤ ‖L j‖ * (C₀ * (a * (T * ‖b‖)) ^ ((j : ℕ) + 1)) := by gcongr
        _ = _ := by ring
    have hp : T ^ (j : ℕ) ≠ 0 := pow_ne_zero _ (ne_of_gt hT)
    have hsimpl : (T ^ (j : ℕ))⁻¹ •
        (((T * s) ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) • L j (b ^ (j : ℕ))) =
          (s ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) • L j (b ^ (j : ℕ)) := by
      rw [smul_smul, mul_pow]
      congr 1
      field_simp [hp]
    rw [← hsimpl, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (pow_pos hT (j : ℕ)))]
    calc
      _ ≤ (T ^ (j : ℕ))⁻¹ *
          (‖L j‖ * C₀ * (a * (T * ‖b‖)) ^ ((j : ℕ) + 1)) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (pow_nonneg hT.le _))
      _ = K * T := by
        dsimp [K]
        simp only [mul_pow, pow_succ]
        field_simp [hp, ne_of_gt hT]
        <;> ring
  choose K hK hbound using hall
  refine ⟨hresolve, ∑ j : Fin n, K j, Finset.sum_nonneg (fun j _ => hK j), ?_⟩
  intro T hT hTb s hs
  have hsum : F T s - F₀ s =
      ∑ j : Fin n,
        ((T ^ (j : ℕ))⁻¹ • L j (NormedSpace.exp ((T * s) • b)) -
          (s ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) • L j (b ^ (j : ℕ))) := by
    simp only [F, F₀, Finset.sum_sub_distrib]
  rw [hsum]
  calc
    ‖∑ j : Fin n,
        ((T ^ (j : ℕ))⁻¹ • L j (NormedSpace.exp ((T * s) • b)) -
          (s ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) • L j (b ^ (j : ℕ)))‖
        ≤ ∑ j : Fin n,
          ‖(T ^ (j : ℕ))⁻¹ • L j (NormedSpace.exp ((T * s) • b)) -
            (s ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ)) • L j (b ^ (j : ℕ))‖ :=
          norm_sum_le _ _
    _ ≤ ∑ j : Fin n, K j * T :=
      Finset.sum_le_sum (fun j _ => hbound j T hT hTb s hs)
    _ = (∑ j : Fin n, K j) * T := by rw [Finset.sum_mul]


end D5.S3.Observer.Linear.DerivativeLayerNormalizedObservation
