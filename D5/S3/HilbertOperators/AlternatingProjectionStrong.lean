/- GID: D5/S3/HilbertOperators/AlternatingProjectionStrong
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/AlternatingProjectionStrong
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Alternating projection powers converge strongly on arbitrary complete Hilbert spaces. -/

module

public import Mathlib.Analysis.InnerProductSpace.MeanErgodic
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # Strong convergence of two alternating orthogonal projections

The classical von Neumann theorem is proved by projection energy, asymptotic
regularity, and a fixed-window upgrade of the native mean ergodic theorem.
The result is pointwise norm convergence without an angle or dimension bound.

Literature: H. H. Bauschke, F. Deutsch and H. Hundal,
*Characterizing arbitrarily slow convergence in the method of alternating
projections*, arXiv:0710.2387v1, Theorem 1.1; C. Badea, S. Grivaux and
V. Müller, *The rate of convergence in the method of alternating projections*,
arXiv:1006.2047v1, equation (1.1). -/

@[expose] public section

open Filter Function
open scoped Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
namespace D5.S3.HilbertOperators.AlternatingProjectionStrong

section Normed
variable {k : Type u} [RCLike k]
variable {H : Type v} [NormedAddCommGroup H] [NormedSpace k H]

private theorem tendsto_pow_of_regular (T : H →L[k] H) (hT : ‖T‖ ≤ 1) (x p : H)
    (hp : T p = p)
    (hreg : Tendsto (fun n : ℕ => (T ^ (n + 1)) x - (T ^ n) x) atTop (𝓝 0))
    (havg : Tendsto (fun m : ℕ => birkhoffAverage k (T : H → H) id m x) atTop (𝓝 p)) :
    Tendsto (fun n : ℕ => (T ^ n) x) atTop (𝓝 p) := by
  classical
  have hpow (n : ℕ) (z : H) : (T ^ n) z = (T : H → H)^[n] z := by
    exact congrFun (FunLike.coe_pow_eq_iterate T n) z
  have hshift (m : ℕ) :
      Tendsto (fun n : ℕ => (T ^ (n + m)) x - (T ^ n) x) atTop (𝓝 0) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have h := (hreg.comp (tendsto_add_atTop_nat m)).add ih
      simpa only [Function.comp_apply, Nat.succ_eq_add_one, Nat.add_assoc,
        sub_add_sub_cancel, add_zero] using h
  have hwindow (m : ℕ) (hm : m ≠ 0) :
      Tendsto (fun n : ℕ => (T ^ n) (birkhoffAverage k (T : H → H) id m x) - (T ^ n) x)
        atTop (𝓝 0) := by
    have heq (n : ℕ) :
        (T ^ n) (birkhoffAverage k (T : H → H) id m x) - (T ^ n) x =
          (m : k)⁻¹ • ∑ i ∈ Finset.range m, ((T ^ (n + i)) x - (T ^ n) x) := by
      rw [birkhoffAverage, birkhoffSum, map_smul, map_sum]
      simp only [id_eq, ← hpow, ← mul_apply_eq_comp, ← pow_add]
      rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_range,
        ← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm), one_smul]
    simp_rw [heq]
    simpa using (tendsto_finsetSum (Finset.range m) (fun i _ => hshift i)).const_smul (m : k)⁻¹
  have hcontract (n : ℕ) (z : H) : ‖(T ^ n) z‖ ≤ ‖z‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp]
      have ht : ‖T ((T ^ n) z)‖ ≤ ‖(T ^ n) z‖ := by
        simpa only [one_mul] using T.le_of_opNorm_le hT ((T ^ n) z)
      exact ht.trans ih
  have hfixed (n : ℕ) : (T ^ n) p = p := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', mul_apply_eq_comp, ih, hp]
  have hbound (n m : ℕ) : ‖(T ^ n) x - p‖ ≤
      ‖(T ^ n) (birkhoffAverage k (T : H → H) id m x) - (T ^ n) x‖ +
      ‖birkhoffAverage k (T : H → H) id m x - p‖ := by
    let a := birkhoffAverage k (T : H → H) id m x
    calc
      ‖(T ^ n) x - p‖ ≤ ‖(T ^ n) x - (T ^ n) a‖ + ‖(T ^ n) a - p‖ := by
        simpa only [sub_add_sub_cancel] using
          norm_add_le ((T ^ n) x - (T ^ n) a) ((T ^ n) a - p)
      _ ≤ ‖(T ^ n) a - (T ^ n) x‖ + ‖a - p‖ := by
        rw [norm_sub_rev ((T ^ n) x) ((T ^ n) a)]
        apply add_le_add le_rfl
        calc
          ‖(T ^ n) a - p‖ = ‖(T ^ n) (a - p)‖ := by rw [map_sub, hfixed]
          _ ≤ ‖a - p‖ := hcontract n (a - p)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp havg (ε / 2) (half_pos hε)
  let m := max M 1
  have hm : m ≠ 0 := by dsimp [m]; omega
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hwindow m hm) (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have ha : ‖birkhoffAverage k (T : H → H) id m x - p‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hM m (le_max_left M 1)
  have hb : ‖(T ^ n) (birkhoffAverage k (T : H → H) id m x) - (T ^ n) x‖ < ε / 2 := by
    simpa only [dist_zero_right] using hN n hn
  rw [dist_eq_norm]
  exact (hbound n m).trans_lt (by linarith)
end Normed

variable {k : Type u} [RCLike k]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace k H] [CompleteSpace H]

private theorem alternating_energy (U V : ClosedSubmodule k H) (z : H) :
    ‖(U.toSubmodule.starProjection ∘L V.toSubmodule.starProjection) z - z‖ ^ 2 ≤
      2 * (‖z‖ ^ 2 - ‖(U.toSubmodule.starProjection ∘L V.toSubmodule.starProjection) z‖ ^ 2) := by
  let a := V.toSubmodule.starProjection z
  let b := U.toSubmodule.starProjection a
  have hV := V.toSubmodule.norm_sq_eq_add_norm_sq_starProjection z
  have hU := U.toSubmodule.norm_sq_eq_add_norm_sq_starProjection a
  rw [V.toSubmodule.starProjection_orthogonal_val] at hV
  rw [U.toSubmodule.starProjection_orthogonal_val] at hU
  have htri : ‖z - b‖ ≤ ‖z - a‖ + ‖a - b‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (z - a) (a - b)
  have hsq : ‖z - b‖ ^ 2 ≤ (‖z - a‖ + ‖a - b‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 htri
  change ‖b - z‖ ^ 2 ≤ 2 * (‖z‖ ^ 2 - ‖b‖ ^ 2)
  rw [norm_sub_rev b z]
  dsimp only [a, b] at *
  nlinarith [sq_nonneg (‖z - V.toSubmodule.starProjection z‖ -
    ‖V.toSubmodule.starProjection z - U.toSubmodule.starProjection (V.toSubmodule.starProjection z)‖)]

private theorem alternating_regular (U V : ClosedSubmodule k H) (x : H) :
    Tendsto (fun n : ℕ =>
      ((U.toSubmodule.starProjection ∘L V.toSubmodule.starProjection) ^ (n + 1)) x -
      ((U.toSubmodule.starProjection ∘L V.toSubmodule.starProjection) ^ n) x)
      atTop (𝓝 0) := by
  let T := U.toSubmodule.starProjection ∘L V.toSubmodule.starProjection
  have hnorm (z : H) : ‖T z‖ ≤ ‖z‖ :=
    (U.toSubmodule.norm_starProjection_apply_le _).trans
      (V.toSubmodule.norm_starProjection_apply_le _)
  have hpow (n : ℕ) : (T ^ (n + 1)) x = T ((T ^ n) x) := by
    rw [pow_succ', mul_apply_eq_comp]
  have hanti : Antitone (fun n : ℕ => ‖(T ^ n) x‖ ^ 2) := by
    apply antitone_nat_of_succ_le
    intro n
    have h := hnorm ((T ^ n) x)
    change ‖(T ^ (n + 1)) x‖ ^ 2 ≤ ‖(T ^ n) x‖ ^ 2
    rw [hpow]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 h
  have hbdd : BddBelow (Set.range (fun n : ℕ => ‖(T ^ n) x‖ ^ 2)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; positivity⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  have hdrop : Tendsto
      (fun n : ℕ => 2 * (‖(T ^ n) x‖ ^ 2 - ‖(T ^ (n + 1)) x‖ ^ 2))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (hlim.sub (hlim.comp (tendsto_add_atTop_nat 1))))
  have hsq : Tendsto (fun n : ℕ => ‖(T ^ (n + 1)) x - (T ^ n) x‖ ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _)
      (fun n => ?_) hdrop
    rw [hpow]
    exact alternating_energy U V ((T ^ n) x)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt

/-- The actual nonaveraged powers of the product of the two orthogonal
projections converge in norm to the projection onto their intersection. -/
theorem tendsto_alternating_projection_pow (U V : ClosedSubmodule k H) (x : H) :
    Tendsto (fun n : ℕ => ((U.toSubmodule.starProjection ∘L V.toSubmodule.starProjection) ^ n) x)
      atTop (𝓝 ((U ⊓ V).toSubmodule.starProjection x)) := by
  let T := U.toSubmodule.starProjection ∘L V.toSubmodule.starProjection
  have hT : ‖T‖ ≤ 1 := by
    calc
      ‖T‖ ≤ ‖U.toSubmodule.starProjection‖ * ‖V.toSubmodule.starProjection‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul U.toSubmodule.starProjection_norm_le
        V.toSubmodule.starProjection_norm_le (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hfix : T.eqLocus (1 : H →L[k] H) = (U ⊓ V).toSubmodule := by
    ext z
    change T z = z ↔ z ∈ U.toSubmodule ∧ z ∈ V.toSubmodule
    constructor
    · intro hz
      have hU : z ∈ U.toSubmodule := by
        rw [← hz]
        exact U.toSubmodule.starProjection_apply_mem _
      have hVnorm : ‖V.toSubmodule.starProjection z‖ = ‖z‖ := by
        apply le_antisymm (V.toSubmodule.norm_starProjection_apply_le z)
        calc
          ‖z‖ = ‖T z‖ := congrArg norm hz.symm
          _ ≤ ‖V.toSubmodule.starProjection z‖ := U.toSubmodule.norm_starProjection_apply_le _
      exact ⟨hU, (V.toSubmodule.mem_iff_norm_starProjection z).mpr hVnorm⟩
    · intro hz
      change U.toSubmodule.starProjection (V.toSubmodule.starProjection z) = z
      rw [V.toSubmodule.starProjection_eq_self_iff.mpr hz.2,
        U.toSubmodule.starProjection_eq_self_iff.mpr hz.1]
  let p := (U ⊓ V).toSubmodule.starProjection x
  have hp : T p = p := by
    change p ∈ T.eqLocus (1 : H →L[k] H)
    rw [hfix]
    exact (U ⊓ V).toSubmodule.starProjection_apply_mem x
  have havg : Tendsto (fun m : ℕ => birkhoffAverage k (T : H → H) id m x)
      atTop (𝓝 p) := by
    have h := T.tendsto_birkhoffAverage_orthogonalProjection hT x
    change Tendsto (fun m : ℕ => birkhoffAverage k (T : H → H) id m x)
      atTop (𝓝 ((T.eqLocus (1 : H →L[k] H)).starProjection x)) at h
    have hproj : (T.eqLocus (1 : H →L[k] H)).starProjection x = p := by
      apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      · change T p = p
        exact hp
      · intro w hw
        apply (U ⊓ V).toSubmodule.starProjection_inner_eq_zero x w
        rwa [hfix] at hw
    simpa only [hproj] using h
  exact tendsto_pow_of_regular T hT x p hp (alternating_regular U V x) havg

end D5.S3.HilbertOperators.AlternatingProjectionStrong
