/- GID: D5/S3/Quantum/SpinChains/NearestNeighborFreezingUniqueMinimum
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/NearestNeighborFreezingUniqueMinimum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The nearest-neighbor chain potential has a unique minimum at its site configuration. -/

/-
proof_shape: result: content; existence: content
escape_witness: existence constructs a strictly increasing site by Gaussian decay and an
interior maximum (preregistered step 4, form (1)); square completion U = 2N + Σ F_i² is
a local have inside result (preregistered step 2, public conclusion form (2)).
Uniqueness of the increasing site configuration is a local step, with no separate declaration.
Information-escape registration is paused under CLAUDE.md §3.9.
admission_basis: open-problem-resolution (#11857; Proved)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators Topology
open Filter

namespace D5.S3.Quantum.SpinChains.NearestNeighborFreezingUniqueMinimum

/-- The site equations (6), with cyclic indices. -/
def Sites {N : ℕ} (ξ : Fin N → ℝ) : Prop :=
  ∀ i, ξ i = 1 / (ξ i - ξ ((finRotate N).symm i)) + 1 / (ξ i - ξ ((finRotate N) i))

/-- The potential in Eq. (31), with all three displayed sums. -/
def U {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  (∑ i, x i ^ 2) +
    (∑ i, 2 / (x i - x ((finRotate N) i)) ^ 2) +
    (∑ i, 2 / ((x i - x ((finRotate N).symm i)) * (x i - x ((finRotate N) i))))

/-- The unique-minimum claim for every chain length at least three. -/
def claim : Prop :=
  ∀ N ≥ 3, ∃ ξ : Fin N → ℝ, StrictMono ξ ∧ Sites ξ ∧
    ∀ x : Fin N → ℝ, StrictMono x → U x ≥ U ξ ∧ (U x = U ξ → x = ξ)

private def g {N : ℕ} (x : Fin N → ℝ) (i : Fin N) : ℝ :=
  1 / (x i - x ((finRotate N).symm i)) + 1 / (x i - x ((finRotate N) i))

private def F {N : ℕ} (x : Fin N → ℝ) (i : Fin N) : ℝ := x i - g x i

private def gaussianWeight {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  (∏ i, |x i - x ((finRotate N) i)|) * Real.exp (-(∑ i, x i ^ 2) / 2)

private def logWeight {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  (∑ i, Real.log (x i - x ((finRotate N) i))) - (∑ i, x i ^ 2) / 2


private theorem existence {N : ℕ} (hN : 3 ≤ N) :
    ∃ ξ : Fin N → ℝ, StrictMono ξ ∧ Sites ξ := by
  have gaussian_continuous {N : ℕ} (_hN : 3 ≤ N) : Continuous (@gaussianWeight N) := by
    have hprod : Continuous (fun x : Fin N → ℝ => ∏ i, |x i - x ((finRotate N) i)|) := by
      apply continuous_finsetProd Finset.univ
      intro i hi
      exact continuous_abs.comp (continuous_apply i |>.sub (continuous_apply ((finRotate N) i)))
    have hsum : Continuous (fun x : Fin N → ℝ => ∑ i, x i ^ 2) := by
      apply continuous_finsetSum
      intro i hi
      exact (continuous_apply i).pow 2
    exact hprod.mul (Real.continuous_exp.comp ((hsum.neg).div_const 2))
  have gaussian_decay {N : ℕ} (hN : 3 ≤ N) :
      Tendsto (@gaussianWeight N) (cocompact (Fin N → ℝ)) (𝓝 0) := by
    let Q : (Fin N → ℝ) → ℝ := fun x => (2 * ‖x‖) ^ N * Real.exp (-(‖x‖)^2 / 2)
    have hq : Tendsto Q (cocompact (Fin N → ℝ)) (𝓝 0) := by
      have hs := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := (1/2 : ℝ)) (by norm_num) (N : ℝ)
      have hn := tendsto_norm_cocompact_atTop (E := Fin N → ℝ)
      have hc : Tendsto (fun r : ℝ => (2*r)^N * Real.exp (-r^2/2)) atTop (𝓝 0) := by
        have hs' : Tendsto (fun r : ℝ => |r| ^ (N : ℝ) * Real.exp (-(1/2 : ℝ) * r ^ 2)) (cocompact ℝ) (𝓝 0) := by simpa using hs
        have hs'' := hs'.mono_left atTop_le_cocompact
        have hc0 := hs''.const_mul ((2 : ℝ) ^ N)
        have heq : (fun r : ℝ => (2 : ℝ)^N * (|r| ^ (N : ℝ) * Real.exp (-(1/2 : ℝ) * r ^ 2))) =ᶠ[atTop]
            (fun r : ℝ => (2*r)^N * Real.exp (-r^2/2)) := by
          filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
          rw [abs_of_nonneg hr, Real.rpow_natCast]
          rw [show -(1/2 : ℝ) * r ^ 2 = -r ^ 2 / 2 by ring]
          rw [mul_pow]
          ring
        simpa using Filter.Tendsto.congr' heq hc0
      exact hc.comp hn
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hq
    · filter_upwards [] with x
      exact mul_nonneg (Finset.prod_nonneg fun i hi => abs_nonneg _) (Real.exp_pos _).le
    · filter_upwards [] with x
      have hprod : ∏ i, |x i - x ((finRotate N) i)| ≤ (2 * ‖x‖) ^ N := by
        calc
          ∏ i, |x i - x ((finRotate N) i)| ≤ ∏ _i : Fin N, (2 * ‖x‖) := by
            apply Finset.prod_le_prod
            · intro i hi; positivity
            · intro i hi
              calc
                |x i - x ((finRotate N) i)| = ‖x i - x ((finRotate N) i)‖ := by rw [Real.norm_eq_abs]
                _ ≤ ‖x i‖ + ‖x ((finRotate N) i)‖ := norm_sub_le _ _
                _ ≤ ‖x‖ + ‖x‖ := add_le_add (norm_le_pi_norm x i) (norm_le_pi_norm x ((finRotate N) i))
                _ = 2 * ‖x‖ := by ring
          _ = (2 * ‖x‖) ^ N := by simp [Finset.prod_const]
      have hsum : ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2 := by
        letI : NeZero N := ⟨by omega⟩
        obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup Finset.univ (by simp) (fun j => ‖x j‖₊)
        have hi' : ‖x i‖₊ = ‖x‖₊ := by
          change ‖x i‖₊ = Finset.univ.sup (fun b => ‖x b‖₊)
          exact hmax.symm
        have hi'' : ‖x i‖ = ‖x‖ := congrArg (fun z : NNReal => (z : ℝ)) hi'
        have hs : x i ^ 2 ≤ ∑ j, x j ^ 2 := by
          apply Finset.single_le_sum (fun j hj => sq_nonneg (x j)) hi
        calc
          ‖x‖ ^ 2 = ‖x i‖ ^ 2 := by rw [hi'']
          _ = x i ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
          _ ≤ ∑ j, x j ^ 2 := hs
      have hexp : Real.exp (-(∑ i, x i ^ 2) / 2) ≤ Real.exp (-‖x‖ ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        linarith
      dsimp [gaussianWeight, Q]
      gcongr
  have exp_L_eq_P {N : ℕ} (hN : 3 ≤ N) {x : Fin N → ℝ}
      (hx : StrictMono x) : Real.exp (logWeight x) = gaussianWeight x := by
    haveI : NeZero N := ⟨by omega⟩
    have hn : ∀ i : Fin N, (finRotate N) i ≠ i := by
      intro i he
      have he' : (1 : Fin N) = 0 := add_left_cancel (show i + 1 = i + 0 by simpa [finRotate_apply] using he)
      have := congrArg Fin.val he'
      simpa [Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 < N)] using this
    have hg : ∀ i, x i - x ((finRotate N) i) ≠ 0 := by
      intro i h
      have hne : i ≠ (finRotate N) i := fun e => hn i e.symm
      exact hne (hx.injective (sub_eq_zero.mp h))
    dsimp [logWeight, gaussianWeight]
    rw [Real.exp_sub, Real.exp_sum, div_eq_mul_inv, ← Real.exp_neg]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      rw [← Real.log_abs, Real.exp_log (abs_pos.mpr (hg i))]
    · congr 1
      ring
  have gaussian_maximum {N : ℕ} (hN : 3 ≤ N) :
      ∃ ξ : Fin N → ℝ, StrictMono ξ ∧ IsLocalMax gaussianWeight ξ := by
    classical
    haveI : NeZero N := ⟨by omega⟩
    have hn : ∀ i : Fin N, (finRotate N) i ≠ i := by
      intro i he
      have he' : (1 : Fin N) = 0 := add_left_cancel (show i + 1 = i + 0 by simpa [finRotate_apply] using he)
      have := congrArg Fin.val he'
      simpa [Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 < N)] using this
    let x₀ : Fin N → ℝ := fun i => (i.val : ℝ)
    have hm₀ : StrictMono x₀ := by
      intro i j hij
      change (i.val : ℝ) < (j.val : ℝ)
      exact_mod_cast hij
    have hp₀ : 0 < gaussianWeight x₀ := by
      apply mul_pos _ (Real.exp_pos _)
      apply Finset.prod_pos
      intro i hi
      exact abs_pos.mpr (sub_ne_zero.mpr (fun he => hn i (hm₀.injective he).symm))
    have he : ∀ᶠ x in cocompact (Fin N → ℝ), gaussianWeight x ≤ gaussianWeight x₀ := by
      exact ((gaussian_decay hN).eventually (gt_mem_nhds hp₀)).mono fun x hx => hx.le
    obtain ⟨ξ, hξ, hmax⟩ := (gaussian_continuous hN).continuousOn.exists_isMaxOn'
      (s := {x : Fin N → ℝ | Monotone x}) isClosed_monotone hm₀.monotone
      (he.filter_mono inf_le_left)
    have hpξ : 0 < gaussianWeight ξ := hp₀.trans_le (hmax hm₀.monotone)
    have hgξ : ∀ i, ξ i - ξ ((finRotate N) i) ≠ 0 := by
      intro i hz
      have hzP : gaussianWeight ξ = 0 := by
        dsimp [gaussianWeight]
        have hzabs : |ξ i - ξ ((finRotate N) i)| = 0 := abs_eq_zero.mpr hz
        rw [Finset.prod_eq_zero (Finset.mem_univ i) hzabs, zero_mul]
      linarith
    change Monotone ξ at hξ
    have hsξ : StrictMono ξ := by
      intro i j hij
      have hh : ∀ k : ℕ, ∀ a b : Fin N, b.val = a.val + k → a ≤ b →
          k = 0 ∨ ξ a < ξ b := by
        intro k
        induction k with
        | zero => intro a b hab hle; exact Or.inl rfl
        | succ k ih =>
          intro a b hab hle
          let c : Fin N := ⟨a.val + 1, by omega⟩
          have hnac : (finRotate N) a = c := by
            apply Fin.ext
            simp only [finRotate_apply, Fin.val_add, Fin.val_one]
            dsimp [c]
            rw [Nat.mod_eq_of_lt (by omega : 1 < N)]
            rw [Nat.mod_eq_of_lt (by omega : a.val + 1 < N)]
          have hac : ξ a < ξ c := by
            apply lt_of_le_of_ne (hξ (by change a.val ≤ c.val; dsimp [c]; omega))
            intro he
            apply hgξ a
            rw [hnac]
            exact sub_eq_zero.mpr he
          rcases ih c b (by dsimp [c]; omega) (by change c.val ≤ b.val; dsimp [c]; omega) with hk | hcb
          · have hbc : b = c := by apply Fin.ext; dsimp [c]; omega
            exact Or.inr (hbc ▸ hac)
          · exact Or.inr (hac.trans hcb)
      rcases hh (j.val - i.val) i j (by omega) (le_of_lt hij) with hzero | hlt
      · have hEq : i = j := Fin.ext (by omega)
        exact (ne_of_lt hij) hEq |>.elim
      · exact hlt
    have hc : {x : Fin N → ℝ | Monotone x} ∈ 𝓝 ξ := by
      have hopen : IsOpen {x : Fin N → ℝ | StrictMono x} := by
        have heq : {x : Fin N → ℝ | StrictMono x} =
            ⋂ i : Fin N, ⋂ j : Fin N, {x : Fin N → ℝ | i < j → x i < x j} := by
          ext x; simp [StrictMono]
        rw [heq]
        apply isOpen_iInter_of_finite
        intro i
        apply isOpen_iInter_of_finite
        intro j
        by_cases hij : i < j
        · simpa [hij] using isOpen_lt (continuous_apply i) (continuous_apply j)
        · simp [hij]
      exact Filter.mem_of_superset (hopen.mem_nhds hsξ) (fun x hx => hx.monotone)
    exact ⟨ξ, hsξ, hmax.isLocalMax hc⟩
  have L_update_deriv {N : ℕ} (hN : 3 ≤ N) {ξ : Fin N → ℝ}
      (hξ : StrictMono ξ) (i : Fin N) :
      HasDerivAt (fun t : ℝ => logWeight (Function.update ξ i t))
        (1 / (ξ i - ξ ((finRotate N).symm i)) + 1 / (ξ i - ξ ((finRotate N) i)) - ξ i) (ξ i) := by
    haveI : NeZero N := ⟨by omega⟩
    have hn : ∀ k : Fin N, (finRotate N) k ≠ k := by
      intro k he
      have he' : (1 : Fin N) = 0 := add_left_cancel (show k + 1 = k + 0 by simpa [finRotate_apply] using he)
      have := congrArg Fin.val he'
      simpa [Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 < N)] using this
    have hg : ∀ k, ξ k - ξ ((finRotate N) k) ≠ 0 := by
      intro k h
      have hne : k ≠ (finRotate N) k := fun e => hn k e.symm
      exact hne (hξ.injective (sub_eq_zero.mp h))
    have hgp : ∀ k, ξ k - ξ ((finRotate N).symm k) ≠ 0 := by
      intro k
      have h := hg ((finRotate N).symm k)
      have hi : (finRotate N) ((finRotate N).symm k) = k := by simp
      have h' : ξ ((finRotate N).symm k) - ξ k ≠ 0 := by simpa [hi] using h
      intro hz
      apply h'
      linarith
    have hu : ∀ k : Fin N, HasDerivAt (fun t : ℝ => (Function.update ξ i t) k)
        (if k = i then 1 else 0) (ξ i) := by
      intro k
      by_cases hki : k = i
      · subst k
        simpa [Function.update_apply] using (hasDerivAt_id' (ξ i))
      · simpa [Function.update_apply, hki] using (hasDerivAt_const (ξ i) (ξ k))
    have hself : Function.update ξ i (ξ i) = ξ := Function.update_eq_self i ξ
    have hlog : ∀ k : Fin N, HasDerivAt (fun t : ℝ =>
        Real.log (((fun t => (Function.update ξ i t) k) - (fun t => (Function.update ξ i t) ((finRotate N) k))) t))
        (((if k = i then 1 else 0) - (if (finRotate N) k = i then 1 else 0)) /
          (ξ k - ξ ((finRotate N) k))) (ξ i) := by
      intro k
      have hinner := (hu k).sub (hu ((finRotate N) k))
      have hlg := hinner.log (by
        change (Function.update ξ i (ξ i)) k - (Function.update ξ i (ξ i)) ((finRotate N) k) ≠ 0
        rw [hself]
        exact hg k)
      simpa [hself] using hlg
    have hsum0 := HasDerivAt.fun_sum (u := Finset.univ) (fun k hk => hlog k)
    have hcoeff : (∑ k, (((if k = i then 1 else 0) - (if (finRotate N) k = i then 1 else 0)) /
          (ξ k - ξ ((finRotate N) k)))) =
        1 / (ξ i - ξ ((finRotate N).symm i)) + 1 / (ξ i - ξ ((finRotate N) i)) := by
      have hA : (∑ k, (if k = i then 1 else 0) / (ξ k - ξ ((finRotate N) k))) =
          1 / (ξ i - ξ ((finRotate N) i)) := by
        rw [show (∑ k, (if k = i then 1 else 0) / (ξ k - ξ ((finRotate N) k))) =
            Finset.sum (Finset.univ : Finset (Fin N)) (fun k => if k = i then 1 / (ξ k - ξ ((finRotate N) k)) else 0) by
              apply Finset.sum_congr rfl; intro k hk; by_cases hki : k = i <;> simp [hki]]
        rw [Finset.sum_eq_single i]
        · simp [hg i]
        · intro b hb hbi; simp [hbi]
        · simp
      have hB : (∑ k, (if (finRotate N) k = i then 1 else 0) / (ξ k - ξ ((finRotate N) k))) =
          1 / (ξ i - ξ ((finRotate N).symm i)) * (-1) := by
        rw [show (∑ k, (if (finRotate N) k = i then 1 else 0) / (ξ k - ξ ((finRotate N) k))) =
            Finset.sum (Finset.univ : Finset (Fin N)) (fun k => if (finRotate N) k = i then 1 / (ξ k - ξ ((finRotate N) k)) else 0) by
              apply Finset.sum_congr rfl
              intro k hk
              by_cases hki : (finRotate N) k = i
              · simp [hki]
              · simp only [hki, if_false, zero_div]]
        rw [Finset.sum_eq_single ((finRotate N).symm i)]
        · have hi : (finRotate N) ((finRotate N).symm i) = i := by simp
          rw [hi]
          simp only [if_true]
          rw [one_div, one_div]
          rw [show ξ ((finRotate N).symm i) - ξ i = -(ξ i - ξ ((finRotate N).symm i)) by ring]
          field_simp [hgp i]

        · intro b hb hbi
          have hnk : (finRotate N) b ≠ i := by
            intro hni
            apply hbi
            apply (finRotate N).injective
            simpa  using hni
          simp only [hnk, if_false, zero_div]
        · simp
      rw [show (∑ k, (((if k = i then 1 else 0) - (if (finRotate N) k = i then 1 else 0)) /
          (ξ k - ξ ((finRotate N) k)))) =
          (∑ k, ((if k = i then 1 else 0) / (ξ k - ξ ((finRotate N) k)) -
            (if (finRotate N) k = i then 1 else 0) / (ξ k - ξ ((finRotate N) k)))) by
            apply Finset.sum_congr rfl
            intro k hk
            rw [sub_div]]
      rw [Finset.sum_sub_distrib, hA, hB]
      field_simp [hgp i, hg i]
      ring
    have hsum : HasDerivAt
        (fun t : ℝ => ∑ k, Real.log (((fun t => (Function.update ξ i t) k) -
          (fun t => (Function.update ξ i t) ((finRotate N) k))) t))
        (1 / (ξ i - ξ ((finRotate N).symm i)) + 1 / (ξ i - ξ ((finRotate N) i))) (ξ i) := by
      rw [← hcoeff]
      exact hsum0
    have hquadraw0 := HasDerivAt.div_const
        (HasDerivAt.fun_sum (u := Finset.univ) (fun k hk => (hu k).mul (hu k))) 2
    have hquadraw1 : HasDerivAt
        (fun t : ℝ => (∑ k, (Function.update ξ i t) k * (Function.update ξ i t) k) / 2)
        ((∑ k, ((if k = i then 1 else 0) * Function.update ξ i (ξ i) k +
            Function.update ξ i (ξ i) k * (if k = i then 1 else 0))) / 2) (ξ i) := by
      simpa only [Pi.mul_apply] using hquadraw0
    have hquadraw : HasDerivAt
        (fun t : ℝ => (∑ k, (Function.update ξ i t) k * (Function.update ξ i t) k) / 2)
        (ξ i) (ξ i) := by
      convert hquadraw1 using 1
      rw [hself]
      have h1 : (∑ k : Fin N, (if k = i then 1 else 0) * ξ k) = ξ i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro b hb hbi; simp [hbi]
        · simp
      have h2 : (∑ k : Fin N, ξ k * (if k = i then 1 else 0)) = ξ i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro b hb hbi; simp [hbi]
        · simp
      rw [Finset.sum_add_distrib, h1, h2]
      ring
    have hquad : HasDerivAt
        (fun t : ℝ => (∑ k, (Function.update ξ i t) k ^ 2) / 2)
        (ξ i) (ξ i) := by
      simpa [pow_two] using hquadraw
    change HasDerivAt
      ((fun t : ℝ => ∑ k, Real.log ((Function.update ξ i t) k - (Function.update ξ i t) ((finRotate N) k))) -
        (fun t : ℝ => (∑ k, (Function.update ξ i t) k ^ 2) / 2))
      (1 / (ξ i - ξ ((finRotate N).symm i)) + 1 / (ξ i - ξ ((finRotate N) i)) - ξ i) (ξ i)
    exact hsum.sub hquad
  have lambda_local_max {N : ℕ} (hN : 3 ≤ N) :
      ∃ ξ : Fin N → ℝ, StrictMono ξ ∧ IsLocalMax logWeight ξ := by
    obtain ⟨ξ, hξ, hP⟩ := gaussian_maximum hN
    have hopen : IsOpen {x : Fin N → ℝ | StrictMono x} := by
      have heq : {x : Fin N → ℝ | StrictMono x} =
          ⋂ i : Fin N, ⋂ j : Fin N, {x : Fin N → ℝ | i < j → x i < x j} := by
        ext x; simp [StrictMono]
      rw [heq]
      apply isOpen_iInter_of_finite
      intro i
      apply isOpen_iInter_of_finite
      intro j
      by_cases hij : i < j
      · simpa [hij] using isOpen_lt (continuous_apply i) (continuous_apply j)
      · simp [hij]
    have hEq : ∀ᶠ x in 𝓝 ξ, Real.exp (logWeight x) = gaussianWeight x := by
      filter_upwards [hopen.mem_nhds hξ] with x hx
      exact exp_L_eq_P hN hx
    have hL : IsLocalMax logWeight ξ := by
      filter_upwards [hP, hEq] with x hxP hxEq
      have hE : Real.exp (logWeight x) ≤ Real.exp (logWeight ξ) := by
        rw [hxEq, exp_L_eq_P hN hξ]
        exact hxP
      exact (Real.exp_le_exp).mp hE
    exact ⟨ξ, hξ, hL⟩

  obtain ⟨ξ, hξ, hL⟩ := lambda_local_max hN
  refine ⟨ξ, hξ, ?_⟩
  intro i
  have hcont : ContinuousAt (fun t : ℝ => Function.update ξ i t) (ξ i) :=
    continuousAt_const.update i continuousAt_id
  have hpath : IsLocalMax (fun t : ℝ => logWeight (Function.update ξ i t)) (ξ i) := by
    have ht : Tendsto (fun t : ℝ => Function.update ξ i t) (𝓝 (ξ i)) (𝓝 ξ) := by
      simpa only [Function.update_eq_self] using hcont.tendsto
    have he := ht.eventually hL
    change ∀ᶠ t in 𝓝 (ξ i), logWeight (Function.update ξ i t) ≤ logWeight (Function.update ξ i (ξ i))
    simpa only [Function.update_eq_self] using he
  have hz := hpath.hasDerivAt_eq_zero (L_update_deriv hN hξ i)
  linarith

theorem result : claim := by
  have sites_unique {N : ℕ} (hN : 3 ≤ N) {x y : Fin N → ℝ}
      (hx : StrictMono x) (hy : StrictMono y) (sx : Sites x) (sy : Sites y) : x = y := by
    have hn : ∀ i : Fin N, (finRotate N) i ≠ i := by
      intro i
      haveI : NeZero N := ⟨by omega⟩
      simp only [finRotate_apply]
      intro he
      have he' : (1 : Fin N) = 0 := add_left_cancel (show i + 1 = i + 0 by simpa using he)
      have := congrArg Fin.val he'
      simpa [Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 < N)] using this
    have signs : ∀ i, 0 < (x i - x ((finRotate N) i)) * (y i - y ((finRotate N) i)) := by
      intro i
      rcases lt_or_gt_of_ne (hn i).symm with hi | hi
      · exact mul_pos_of_neg_of_neg (sub_neg.mpr (hx hi)) (sub_neg.mpr (hy hi))
      · exact mul_pos (sub_pos.mpr (hx hi)) (sub_pos.mpr (hy hi))
    let δ := fun i => x i - y i
    have pair : ∑ i, δ i * (g x i - g y i) =
        -(∑ i, ((x i - x ((finRotate N) i)) - (y i - y ((finRotate N) i))) ^ 2 /
          ((x i - x ((finRotate N) i)) * (y i - y ((finRotate N) i)))) := by
      have reindex : ∑ i, δ i * (1 / (x i - x ((finRotate N).symm i)) - 1 / (y i - y ((finRotate N).symm i))) =
          ∑ i, δ ((finRotate N) i) * (1 / (x ((finRotate N) i) - x i) - 1 / (y ((finRotate N) i) - y i)) := by
        rw [← Equiv.sum_comp (finRotate N) (fun i => δ i *
          (1 / (x i - x ((finRotate N).symm i)) - 1 / (y i - y ((finRotate N).symm i))))]
        simp only [Equiv.symm_apply_apply]
      calc
        _ = (∑ i, δ i * (1 / (x i - x ((finRotate N).symm i)) - 1 / (y i - y ((finRotate N).symm i)))) +
            ∑ i, δ i * (1 / (x i - x ((finRotate N) i)) - 1 / (y i - y ((finRotate N) i))) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          dsimp [g]
          ring
        _ = _ := by
          rw [reindex, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _
          have hu := (mul_pos_iff.mp (signs i))
          have hux : x i - x ((finRotate N) i) ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt (signs i))).1
          have huy : y i - y ((finRotate N) i) ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt (signs i))).2
          have hux' : x ((finRotate N) i) - x i ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hux).symm
          have huy' : y ((finRotate N) i) - y i ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp huy).symm
          dsimp [δ]
          field_simp
          <;> ring
    have zero : ∑ i, δ i * (g x i - g y i) = ∑ i, δ i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show g x i = x i from (sx i).symm, show g y i = y i from (sy i).symm]
      dsimp [δ]
      ring
    have hpos : 0 ≤ ∑ i, ((x i - x ((finRotate N) i)) - (y i - y ((finRotate N) i))) ^ 2 /
          ((x i - x ((finRotate N) i)) * (y i - y ((finRotate N) i))) :=
      Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (signs i).le
    have hz : ∑ i, δ i ^ 2 = 0 := by
      have : 0 ≤ ∑ i, δ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      linarith [pair, zero]
    have allzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (δ i))).mp hz
    funext i
    have := allzero i (Finset.mem_univ i)
    have : δ i = 0 := sq_eq_zero_iff.mp this
    exact sub_eq_zero.mp this
  have square_completion {N : ℕ} (hN : 3 ≤ N) {x : Fin N → ℝ}
      (hx : StrictMono x) : U x = 2 * N + ∑ i, F x i ^ 2 := by
    haveI : NeZero N := ⟨by omega⟩
    have hn : ∀ i : Fin N, (finRotate N) i ≠ i := by
      intro i
      haveI : NeZero N := ⟨by omega⟩
      simp only [finRotate_apply]
      intro he
      have he' : (1 : Fin N) = 0 := add_left_cancel (show i + 1 = i + 0 by simpa using he)
      have := congrArg Fin.val he'
      simpa [Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 < N)] using this
    have hg : ∀ i, x i - x ((finRotate N) i) ≠ 0 := by
      intro i h
      have hne : i ≠ (finRotate N) i := fun e => hn i e.symm
      exact hne (hx.injective (sub_eq_zero.mp h))
    have hgp : ∀ i, x i - x ((finRotate N).symm i) ≠ 0 := by
      haveI : NeZero N := ⟨by omega⟩
      intro i
      have h := hg ((finRotate N).symm i)
      have hi : (finRotate N) ((finRotate N).symm i) = i := by simp
      have h' : x ((finRotate N).symm i) - x i ≠ 0 := by simpa [hi] using h
      intro hz
      apply h'
      linarith
    have reindex : ∀ f : Fin N → ℝ, (∑ i, f ((finRotate N) i)) = ∑ i, f i :=
      fun f => Equiv.sum_comp (finRotate N) f
    have pair : ∑ i, x i * g x i = N := by
      have hprev : ∑ i, x i / (x i - x ((finRotate N).symm i)) =
          ∑ i, x ((finRotate N) i) / (x ((finRotate N) i) - x i) := by
        rw [← reindex (fun i => x i / (x i - x ((finRotate N).symm i)))]
        simp only [Equiv.symm_apply_apply]
      calc
        _ = (∑ i, x i / (x i - x ((finRotate N).symm i))) + ∑ i, x i / (x i - x ((finRotate N) i)) := by
          simp only [g, mul_add, mul_one_div, Finset.sum_add_distrib]
        _ = ∑ i : Fin N, (1 : ℝ) := by
          rw [hprev, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          have h := hg i
          have h' : x ((finRotate N) i) - x i ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp h).symm
          have hs : x ((finRotate N) i) - x i = -(x i - x ((finRotate N) i)) := by ring
          rw [hs]
          field_simp [h]
          ring
        _ = N := by simp
    have hprevsq : ∑ i, (1 / (x i - x ((finRotate N).symm i))) ^ 2 =
        ∑ i, (1 / (x i - x ((finRotate N) i))) ^ 2 := by
      rw [← reindex (fun i => (1 / (x i - x ((finRotate N).symm i))) ^ 2)]
      apply Finset.sum_congr rfl
      intro i _
      simp [finRotate_apply, finRotate_symm_apply]
      have hs : x (i + 1) - x i = -(x i - x (i + 1)) := by ring
      rw [hs]
      simp [div_eq_mul_inv, pow_two]
      ring
    have hgsq : ∑ i, g x i ^ 2 =
        (∑ i, 2 / (x i - x ((finRotate N) i)) ^ 2) +
        ∑ i, 2 / ((x i - x ((finRotate N).symm i)) * (x i - x ((finRotate N) i))) := by
      calc
        _ = (∑ i, (1 / (x i - x ((finRotate N).symm i))) ^ 2) +
            (∑ i, (1 / (x i - x ((finRotate N) i))) ^ 2) +
            ∑ i, 2 / ((x i - x ((finRotate N).symm i)) * (x i - x ((finRotate N) i))) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          dsimp [g]
          simp [div_eq_mul_inv, pow_two]
          ring
        _ = _ := by
          rw [hprevsq, ← Finset.sum_add_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          simp [div_eq_mul_inv, pow_two]
          ring
    have hexpand : ∑ i, F x i ^ 2 =
        (∑ i, x i ^ 2) - 2 * (∑ i, x i * g x i) + ∑ i, g x i ^ 2 := by
      calc
        _ = ∑ i, (x i ^ 2 - 2 * (x i * g x i) + g x i ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp [F]
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          congr 1
          rw [← Finset.mul_sum]
    rw [hexpand, pair, hgsq]
    dsimp [U]
    ring
  intro N hN
  obtain ⟨ξ, hξ, sξ⟩ := existence hN
  refine ⟨ξ, hξ, sξ, ?_⟩
  intro x hx
  have hξsq := square_completion hN hξ
  have hxsq := square_completion hN hx
  have hFξ : ∀ i, F ξ i = 0 := by
    intro i
    dsimp [F, g]
    exact sub_eq_zero.mpr (sξ i)
  have hsumξ : ∑ i, F ξ i ^ 2 = 0 := by simp [hFξ]
  have hUξ : U ξ = 2 * N := by linarith [hξsq, hsumξ]
  have hnonneg : 0 ≤ ∑ i, F x i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  constructor
  · rw [hUξ]
    linarith [hxsq]
  · intro heq
    have hsum : ∑ i, F x i ^ 2 = 0 := by linarith [hxsq, hUξ]
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (F x i))).mp hsum
    have sx : Sites x := by
      intro i
      dsimp [F] at hzero
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp (hzero i (Finset.mem_univ i)))
    exact sites_unique hN hx hξ sx sξ

end D5.S3.Quantum.SpinChains.NearestNeighborFreezingUniqueMinimum
