/- GID: D5/S3/HilbertOperators/FiniteCyclicProjectionStrong
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/FiniteCyclicProjectionStrong
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Every finite ordered product of Hilbert space orthogonal projections converges strongly under iteration. -/

module

public import D5.S3.HilbertOperators.AlternatingProjectionStrong

/-! # Strong convergence of a finite cyclic product of orthogonal projections

The first listed subspace acts first. The empty product is the identity,
and the intersection of the empty family is the whole space.

Literature: Omer Ginat, *The method of alternating projections*,
arXiv:1809.05858v1, Section 4.2, Theorem 4.2, states Halperin's theorem
for at least two closed subspaces of a real or complex Hilbert space.
The statements below also include empty and singleton lists. -/

@[expose] public section

open Filter Function
open scoped Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
namespace D5.S3.HilbertOperators.FiniteCyclicProjectionStrong

variable {k : Type u} [RCLike k]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace k H] [CompleteSpace H]

/-- The ordered product of the actual orthogonal projections; the head acts first. -/
def cycle : List (ClosedSubmodule k H) → H →L[k] H
  | [] => 1
  | U :: Us => cycle Us ∘L U.toSubmodule.starProjection

private theorem norm_cycle_le (Us : List (ClosedSubmodule k H)) (z : H) :
    ‖cycle Us z‖ ≤ ‖z‖ := by
  induction Us generalizing z with
  | nil => simp [cycle]
  | cons U Us ih =>
    exact (ih (U.toSubmodule.starProjection z)).trans
      (U.toSubmodule.norm_starProjection_apply_le z)

private theorem cycle_fixed_iff (Us : List (ClosedSubmodule k H)) (z : H) :
    cycle Us z = z ↔ ∀ U ∈ Us, z ∈ U := by
  induction Us with
  | nil => simp [cycle]
  | cons U Us ih =>
    constructor
    · intro hz
      have hnorm : ‖U.toSubmodule.starProjection z‖ = ‖z‖ := by
        apply le_antisymm (U.toSubmodule.norm_starProjection_apply_le z)
        calc
          ‖z‖ = ‖cycle (U :: Us) z‖ := congrArg norm hz.symm
          _ ≤ ‖U.toSubmodule.starProjection z‖ := norm_cycle_le Us _
      have hU : z ∈ U := (U.toSubmodule.mem_iff_norm_starProjection z).mpr hnorm
      have htail : cycle Us z = z := by
        simpa only [cycle, ContinuousLinearMap.comp_apply,
          U.toSubmodule.starProjection_eq_self_iff.mpr hU] using hz
      simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hU (ih.mp htail)
    · intro hz
      have hU := hz U (List.mem_cons_self ..)
      have htail : cycle Us z = z := ih.mpr (fun V hV => hz V (List.mem_cons_of_mem U hV))
      simpa only [cycle, ContinuousLinearMap.comp_apply,
        U.toSubmodule.starProjection_eq_self_iff.mpr hU] using htail

private theorem cycle_energy (Us : List (ClosedSubmodule k H)) (z : H) :
    ‖cycle Us z - z‖ ^ 2 ≤
      (2 : ℝ) ^ Us.length * (‖z‖ ^ 2 - ‖cycle Us z‖ ^ 2) := by
  induction Us generalizing z with
  | nil => simp [cycle]
  | cons U Us ih =>
    let a := U.toSubmodule.starProjection z
    let b := cycle Us a
    let C : ℝ := 2 ^ Us.length
    have htail : ‖b - a‖ ^ 2 ≤ C * (‖a‖ ^ 2 - ‖b‖ ^ 2) := ih a
    have hpyth := U.toSubmodule.norm_sq_eq_add_norm_sq_starProjection z
    rw [U.toSubmodule.starProjection_orthogonal_val] at hpyth
    have hproj : ‖z‖ ^ 2 = ‖a‖ ^ 2 + ‖z - a‖ ^ 2 := by
      simpa only [a, add_comm] using hpyth
    have htri : ‖b - z‖ ≤ ‖b - a‖ + ‖z - a‖ := by
      simpa only [sub_add_sub_cancel, norm_sub_rev a z] using
        norm_add_le (b - a) (a - z)
    have hsq : ‖b - z‖ ^ 2 ≤ (‖b - a‖ + ‖z - a‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 htri
    have hC : 1 ≤ C := one_le_pow₀ (by norm_num) _
    have hscale : 0 ≤ (C - 1) * ‖z - a‖ ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hC) (sq_nonneg _)
    change ‖b - z‖ ^ 2 ≤ 2 ^ (Us.length + 1) * (‖z‖ ^ 2 - ‖b‖ ^ 2)
    rw [pow_succ]
    change ‖b - z‖ ^ 2 ≤ C * 2 * (‖z‖ ^ 2 - ‖b‖ ^ 2)
    nlinarith [sq_nonneg (‖b - a‖ - ‖z - a‖)]

private theorem cycle_regular (Us : List (ClosedSubmodule k H)) (x : H) :
    Tendsto (fun n : ℕ => (cycle Us ^ (n + 1)) x - (cycle Us ^ n) x)
      atTop (𝓝 0) := by
  let T := cycle Us
  have hpow (n : ℕ) : (T ^ (n + 1)) x = T ((T ^ n) x) := by
    rw [pow_succ', mul_apply_eq_comp]
  have hanti : Antitone (fun n : ℕ => ‖(T ^ n) x‖ ^ 2) := by
    apply antitone_nat_of_succ_le
    intro n
    rw [hpow]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (norm_cycle_le Us _)
  have hbdd : BddBelow (Set.range (fun n : ℕ => ‖(T ^ n) x‖ ^ 2)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; positivity⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  have hdrop : Tendsto
      (fun n : ℕ => (2 : ℝ) ^ Us.length *
        (‖(T ^ n) x‖ ^ 2 - ‖(T ^ (n + 1)) x‖ ^ 2)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (hlim.sub (hlim.comp (tendsto_add_atTop_nat 1)))
  have hsq : Tendsto (fun n : ℕ => ‖(T ^ (n + 1)) x - (T ^ n) x‖ ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hdrop
    rw [hpow]
    exact cycle_energy Us ((T ^ n) x)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt

/-- Powers of every fixed finite ordered product of orthogonal projections
converge strongly to the actual projection onto the common intersection. -/
theorem tendsto_cycle_pow (Us : List (ClosedSubmodule k H)) (x : H) :
    Tendsto (fun n : ℕ => (cycle Us ^ n) x)
      atTop (𝓝 ((sInf {U | U ∈ Us}).toSubmodule.starProjection x)) := by
  let T := cycle Us
  let M : ClosedSubmodule k H := sInf {U | U ∈ Us}
  have hT : ‖T‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (fun z => by simpa only [one_mul] using norm_cycle_le Us z)
  have hfix : T.eqLocus (1 : H →L[k] H) = M.toSubmodule := by
    ext z
    change cycle Us z = z ↔ z ∈ sInf {U | U ∈ Us}
    simpa only [ClosedSubmodule.mem_sInf, Set.mem_setOf_eq] using cycle_fixed_iff Us z
  let p := M.toSubmodule.starProjection x
  have hp : T p = p := by
    change p ∈ T.eqLocus (1 : H →L[k] H)
    rw [hfix]
    exact M.toSubmodule.starProjection_apply_mem x
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
        apply M.toSubmodule.starProjection_inner_eq_zero x w
        rwa [hfix] at hw
    simpa only [hproj] using h
  exact AlternatingProjectionStrong.tendsto_pow_of_regular T hT x p hp (cycle_regular Us x) havg

end D5.S3.HilbertOperators.FiniteCyclicProjectionStrong
