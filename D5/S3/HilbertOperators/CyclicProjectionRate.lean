/- GID: D5/S3/HilbertOperators/CyclicProjectionRate
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/CyclicProjectionRate
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Linear regularity characterizes uniform geometric cyclic convergence. -/

module

public import D5.S3.HilbertOperators.FiniteCyclicProjectionStrong

/-! # Linear regularity and the energy rate for cyclic projections

The cycle uses the actual ordered family, with the first listed factor acting first.
The inclination estimate is classical; see Badea, Grivaux and Müller,
arXiv:1006.2047, Section 4.1. -/

@[expose] public section
open Function
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
namespace D5.S3.HilbertOperators.CyclicProjectionRate
open FiniteCyclicProjectionStrong
variable {k : Type u} [RCLike k]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace k H] [CompleteSpace H]

/-- A member of the actual family detects the distance to its common intersection. -/
def LinearRegular (Us : List (ClosedSubmodule k H)) (ell : ℝ) : Prop :=
  ∀ x : H, ∃ U ∈ Us, ell * ‖x - (sInf {V | V ∈ Us}).toSubmodule.starProjection x‖ ≤
    ‖x - U.toSubmodule.starProjection x‖

private theorem initial_residual_sqrt (Us : List (ClosedSubmodule k H)) (z : H)
    (V : ClosedSubmodule k H) (hV : V ∈ Us) :
    ‖z - V.toSubmodule.starProjection z‖ ≤ (Us.length : ℝ) *
      Real.sqrt (‖z‖ ^ 2 - ‖cycle Us z‖ ^ 2) := by
  induction Us generalizing z with
  | nil => simp at hV
  | cons U Us ih =>
    let a := U.toSubmodule.starProjection z
    let E : ℝ := ‖z‖ ^ 2 - ‖cycle (U :: Us) z‖ ^ 2
    have ht : ‖cycle (U :: Us) z‖ ≤ ‖a‖ := norm_cycle_le Us a
    have ha : ‖a‖ ≤ ‖z‖ := U.toSubmodule.norm_starProjection_apply_le z
    have hp := U.toSubmodule.norm_sq_eq_add_norm_sq_starProjection z
    rw [U.toSubmodule.starProjection_orthogonal_val] at hp
    have ht2 : ‖cycle (U :: Us) z‖ ^ 2 ≤ ‖a‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 ht
    have ha2 : ‖a‖ ^ 2 ≤ ‖z‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 ha
    have hE : 0 ≤ E := by dsimp [E]; linarith
    have hs : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE
    have hfirst : ‖z - a‖ ≤ Real.sqrt E := by
      have hp' : ‖z‖ ^ 2 = ‖a‖ ^ 2 + ‖z - a‖ ^ 2 := by
        simpa only [a, add_comm] using hp
      nlinarith [Real.sqrt_nonneg E, norm_nonneg (z - a)]
    have hlen : 0 ≤ (Us.length : ℝ) := Nat.cast_nonneg _
    simp only [List.mem_cons] at hV
    rcases hV with rfl | hV
    · change ‖z - a‖ ≤ ((Us.length + 1 : ℕ) : ℝ) * Real.sqrt E
      push_cast
      nlinarith [Real.sqrt_nonneg E]
    · have hi := ih a hV
      have hsmono : Real.sqrt (‖a‖ ^ 2 - ‖cycle Us a‖ ^ 2) ≤ Real.sqrt E := by
        apply Real.sqrt_le_sqrt
        change ‖a‖ ^ 2 - ‖cycle Us a‖ ^ 2 ≤ ‖z‖ ^ 2 - ‖cycle Us a‖ ^ 2
        linarith
      have hr : ‖z - V.toSubmodule.starProjection z‖ ≤
          ‖z - a‖ + ‖a - V.toSubmodule.starProjection a‖ := by
        rw [← V.toSubmodule.starProjection_orthogonal_val z,
          ← V.toSubmodule.starProjection_orthogonal_val a]
        calc
          ‖V.toSubmoduleᗮ.starProjection z‖ =
              ‖V.toSubmoduleᗮ.starProjection (z - a) + V.toSubmoduleᗮ.starProjection a‖ := by
                rw [← map_add, sub_add_cancel]
          _ ≤ ‖V.toSubmoduleᗮ.starProjection (z - a)‖ + ‖V.toSubmoduleᗮ.starProjection a‖ :=
            norm_add_le _ _
          _ ≤ ‖z - a‖ + ‖V.toSubmoduleᗮ.starProjection a‖ :=
            add_le_add (V.toSubmoduleᗮ.norm_starProjection_apply_le _) le_rfl
      change ‖z - V.toSubmodule.starProjection z‖ ≤
        ((Us.length + 1 : ℕ) : ℝ) * Real.sqrt E
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hsmono hlen]


private theorem initial_residual_energy (Us : List (ClosedSubmodule k H)) (z : H)
    (V : ClosedSubmodule k H) (hV : V ∈ Us) :
    ‖z - V.toSubmodule.starProjection z‖ ^ 2 ≤ (Us.length : ℝ) ^ 2 *
      (‖z‖ ^ 2 - ‖cycle Us z‖ ^ 2) := by
  have h := initial_residual_sqrt Us z V hV
  have he : 0 ≤ ‖z‖ ^ 2 - ‖cycle Us z‖ ^ 2 :=
    sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (norm_cycle_le Us z))
  have hh := (sq_le_sq₀ (norm_nonneg (z - V.toSubmodule.starProjection z))
    (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))).2 h
  simpa only [mul_pow, Real.sq_sqrt he] using hh

private theorem centered_residual_energy (Us : List (ClosedSubmodule k H)) (x : H)
    (V : ClosedSubmodule k H) (hV : V ∈ Us) :
    let p := (sInf {U | U ∈ Us}).toSubmodule.starProjection x
    ‖x - V.toSubmodule.starProjection x‖ ^ 2 ≤ (Us.length : ℝ) ^ 2 *
      (‖x - p‖ ^ 2 - ‖cycle Us x - p‖ ^ 2) := by
  let p := (sInf {U | U ∈ Us}).toSubmodule.starProjection x
  have hp : ∀ U ∈ Us, p ∈ U := by
    have h := (sInf {U : ClosedSubmodule k H | U ∈ Us}).toSubmodule.starProjection_apply_mem x
    change p ∈ sInf {U : ClosedSubmodule k H | U ∈ Us} at h
    simpa only [ClosedSubmodule.mem_sInf, Set.mem_ofPred_eq] using h
  have hfix : cycle Us p = p := (cycle_fixed_iff Us p).mpr hp
  have hpV : V.toSubmodule.starProjection p = p :=
    V.toSubmodule.starProjection_eq_self_iff.mpr (hp V hV)
  have h := initial_residual_energy Us (x - p) V hV
  simpa only [map_sub, hpV, hfix, sub_sub_sub_cancel_right] using h


private theorem projection_cycle (Us : List (ClosedSubmodule k H))
    (M : ClosedSubmodule k H) (hM : ∀ U ∈ Us, M ≤ U) (x : H) :
    M.toSubmodule.starProjection (cycle Us x) = M.toSubmodule.starProjection x := by
  induction Us generalizing x with
  | nil => rfl
  | cons U Us ih =>
    change M.toSubmodule.starProjection (cycle Us (U.toSubmodule.starProjection x)) = _
    rw [ih (fun V hV => hM V (List.mem_cons_of_mem U hV))]
    exact DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le
      (show M.toSubmodule ≤ U.toSubmodule from hM U (List.mem_cons_self ..))) x

omit [CompleteSpace H] in
private theorem length_pos (Us : List (ClosedSubmodule k H)) (hne : Us ≠ []) :
    0 < (Us.length : ℝ) := by
  exact_mod_cast List.length_pos_iff.mpr hne

/-- The inclination energy rate for the actual ordered cyclic product. -/
theorem geometric_rate (Us : List (ClosedSubmodule k H)) (hne : Us ≠ [])
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hreg : LinearRegular Us ell)
    (n : ℕ) (x : H) :
    ‖(cycle Us ^ n) x - (sInf {U | U ∈ Us}).toSubmodule.starProjection x‖ ^ 2 ≤
      (1 - ell ^ 2 / (Us.length : ℝ) ^ 2) ^ n *
        ‖x - (sInf {U | U ∈ Us}).toSubmodule.starProjection x‖ ^ 2 := by
  let P := (sInf {U : ClosedSubmodule k H | U ∈ Us}).toSubmodule.starProjection
  let q : ℝ := 1 - ell ^ 2 / (Us.length : ℝ) ^ 2
  have hm := length_pos Us hne
  have hm1 : 1 ≤ (Us.length : ℝ) := by
    exact_mod_cast (List.length_pos_iff.mpr hne)
  have hm2 : 0 < (Us.length : ℝ) ^ 2 := sq_pos_of_pos hm
  have hq : 0 ≤ q := by
    dsimp [q]
    have : ell ^ 2 ≤ (Us.length : ℝ) ^ 2 := by nlinarith
    exact sub_nonneg.mpr ((div_le_one hm2).mpr this)
  have hP (z : H) : P (cycle Us z) = P z :=
    projection_cycle Us _ (fun U hU => sInf_le hU) z
  have hstep (z : H) : ‖cycle Us z - P z‖ ^ 2 ≤ q * ‖z - P z‖ ^ 2 := by
    obtain ⟨U, hU, hr⟩ := hreg z
    have he := centered_residual_energy Us z U hU
    change ‖z - U.toSubmodule.starProjection z‖ ^ 2 ≤
      (Us.length : ℝ) ^ 2 * (‖z - P z‖ ^ 2 - ‖cycle Us z - P z‖ ^ 2) at he
    have hs : (ell * ‖z - P z‖) ^ 2 ≤ ‖z - U.toSubmodule.starProjection z‖ ^ 2 :=
      (sq_le_sq₀ (mul_nonneg hell.le (norm_nonneg _)) (norm_nonneg _)).mpr hr
    have hd : ell ^ 2 / (Us.length : ℝ) ^ 2 * (Us.length : ℝ) ^ 2 = ell ^ 2 :=
      div_mul_cancel₀ _ (ne_of_gt hm2)
    dsimp [q]
    nlinarith
  have hPn (j : ℕ) : P ((cycle Us ^ j) x) = P x := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', mul_apply_eq_comp, hP, ih]
  change ‖(cycle Us ^ n) x - P x‖ ^ 2 ≤ q ^ n * ‖x - P x‖ ^ 2
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' (cycle Us) n, mul_apply_eq_comp]
    calc
      ‖cycle Us ((cycle Us ^ n) x) - P x‖ ^ 2 ≤
          q * ‖(cycle Us ^ n) x - P x‖ ^ 2 := by simpa only [hPn] using hstep ((cycle Us ^ n) x)
      _ ≤ q * (q ^ n * ‖x - P x‖ ^ 2) := mul_le_mul_of_nonneg_left ih hq
      _ = q ^ (n + 1) * ‖x - P x‖ ^ 2 := by ring

private theorem displacement_le (Us : List (ClosedSubmodule k H)) (x : H)
    (r : ℝ) (hr : ∀ U ∈ Us, ‖x - U.toSubmodule.starProjection x‖ ≤ r) :
    ‖cycle Us x - x‖ ≤ (Us.length : ℝ) * r := by
  induction Us with
  | nil => simp [cycle]
  | cons U Us ih =>
    have ht := ih (fun V hV => hr V (List.mem_cons_of_mem U hV))
    have hU := hr U (List.mem_cons_self ..)
    calc
      ‖cycle (U :: Us) x - x‖ =
          ‖cycle Us (U.toSubmodule.starProjection x - x) + (cycle Us x - x)‖ := by
            simp only [cycle, ContinuousLinearMap.comp_apply, map_sub, sub_add_sub_cancel]
      _ ≤ ‖cycle Us (U.toSubmodule.starProjection x - x)‖ + ‖cycle Us x - x‖ := norm_add_le _ _
      _ ≤ ‖U.toSubmodule.starProjection x - x‖ + (Us.length : ℝ) * r :=
        add_le_add (norm_cycle_le Us _) ht
      _ ≤ ((U :: Us).length : ℝ) * r := by
        rw [norm_sub_rev]
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        nlinarith

/-- Positive same-family linear regularity is equivalent to a uniform geometric rate. -/
theorem linear_regular_iff_uniform_geometric (Us : List (ClosedSubmodule k H))
    (hne : Us ≠ []) :
    (∃ ell : ℝ, 0 < ell ∧ ell ≤ 1 ∧ LinearRegular Us ell) ↔
      ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ (n : ℕ) (x : H),
        ‖(cycle Us ^ n) x - (sInf {U | U ∈ Us}).toSubmodule.starProjection x‖ ^ 2 ≤
          q ^ n * ‖x - (sInf {U | U ∈ Us}).toSubmodule.starProjection x‖ ^ 2 := by
  have hm := length_pos Us hne
  have hm1 : 1 ≤ (Us.length : ℝ) := by exact_mod_cast (List.length_pos_iff.mpr hne)
  constructor
  · rintro ⟨ell, h0, h1, hr⟩
    refine ⟨1 - ell ^ 2 / (Us.length : ℝ) ^ 2, ?_, ?_, geometric_rate Us hne ell h0 h1 hr⟩
    · have : ell ^ 2 ≤ (Us.length : ℝ) ^ 2 := by nlinarith
      exact sub_nonneg.mpr ((div_le_one (sq_pos_of_pos hm)).mpr this)
    · have : 0 < ell ^ 2 / (Us.length : ℝ) ^ 2 := div_pos (sq_pos_of_pos h0) (sq_pos_of_pos hm)
      linarith
  · rintro ⟨q, hq0, hq1, hrate⟩
    let a := Real.sqrt q
    have ha0 : 0 ≤ a := Real.sqrt_nonneg q
    have ha2 : a ^ 2 = q := Real.sq_sqrt hq0
    have ha1 : a < 1 := by nlinarith
    let ell := (1 - a) / (Us.length : ℝ)
    have he0 : 0 < ell := div_pos (sub_pos.mpr ha1) hm
    have he1 : ell ≤ 1 := (div_le_one hm).mpr (by linarith)
    refine ⟨ell, he0, he1, ?_⟩
    intro x
    classical
    have hne' : Us.toFinset.Nonempty := by
      obtain ⟨U, hU⟩ := List.exists_mem_of_ne_nil Us hne
      exact ⟨U, List.mem_toFinset.mpr hU⟩
    obtain ⟨U, hU, hmax⟩ := Us.toFinset.exists_max_image
      (fun V => ‖x - V.toSubmodule.starProjection x‖) hne'
    refine ⟨U, List.mem_toFinset.mp hU, ?_⟩
    let p := (sInf {U : ClosedSubmodule k H | U ∈ Us}).toSubmodule.starProjection x
    have hd := displacement_le Us x ‖x - U.toSubmodule.starProjection x‖
      (fun V hV => hmax V (List.mem_toFinset.mpr hV))
    have hs : ‖cycle Us x - p‖ ^ 2 ≤ q * ‖x - p‖ ^ 2 := by
      simpa only [pow_one] using hrate 1 x
    have hnorm : ‖cycle Us x - p‖ ≤ a * ‖x - p‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha0 (norm_nonneg _))).mp
      simpa only [mul_pow, ha2] using hs
    have htri : ‖x - p‖ ≤ ‖cycle Us x - x‖ + ‖cycle Us x - p‖ := by
      simpa only [sub_add_sub_cancel, norm_sub_rev x (cycle Us x)] using
        norm_add_le (x - cycle Us x) (cycle Us x - p)
    have hh : (1 - a) * ‖x - p‖ ≤ (Us.length : ℝ) *
        ‖x - U.toSubmodule.starProjection x‖ := by nlinarith
    change ell * ‖x - p‖ ≤ ‖x - U.toSubmodule.starProjection x‖
    dsimp [ell]
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hm).mpr (by nlinarith only [hh])

end D5.S3.HilbertOperators.CyclicProjectionRate
