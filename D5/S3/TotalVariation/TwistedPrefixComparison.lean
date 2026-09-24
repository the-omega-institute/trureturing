/- GID: D5/S3/TotalVariation/TwistedPrefixComparison
   generality: G
   mirror-B: D5/B/S3/TotalVariation/TwistedPrefixComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compare complete twisted prefixes under explicit kernel estimates. -/

import D5.S3.TotalVariation.TwistedResetPaths
import D5.S3.TotalVariation.Pinsker

open scoped BigOperators
open D5.S3.TotalVariation.TwistedResetPaths
open D5.S3.TotalVariation.Pinsker
namespace D5.S3.TotalVariation.TwistedPrefixComparison

/-- A start state and every subsequent state of a complete n-transition prefix. -/
abbrev Prefix (k n : ℕ) := State k × (Fin n → State k)

/-- Normalize the actual closing-path sum by the positive twisted loop mass. -/
noncomputable def twistedLaw (k : ℕ) (p : ℝ) (n G : ℕ) (v : Prefix k n) : ℝ :=
  twistedPrefixMass k p n G v.1 v.2 / loopMass k p (n + G)

/-- Complete Markov path law with initial mass vector `π`. -/
noncomputable def referenceLaw (k : ℕ) (p : ℝ) (n : ℕ)
    (π : State k → ℝ) (v : Prefix k n) : ℝ :=
  π v.1 * pathWeight k p n v.1 v.2

/-- A pointwise gap estimate transfers to the entire prefix with a coefficient depending on
loop length, not the number of available suffix states. The row normalization and reference
mass assumptions are explicit; no stationarity or numerical mixing rate is asserted here.
The high-suffix tail is the actual reference mass. No small-error premise is needed. -/
theorem complete_prefix_comparison_of_estimates
    (k : ℕ) (hk : 2 ≤ k) (p : ℝ) (hp : 0 < p) (n G : ℕ) (hL : 2 ≤ n + G)
    (hrow : ∀ s, ∑ t, kernel k p s t = 1)
    (π : State k → ℝ) (hπ : ∀ s, 0 ≤ π s) (hπsum : ∑ s, π s = 1)
    (hflip : ∀ s, π (flip s) = π s)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hmix : ∀ s t, |(kernel k p ^ G) s t - π t| ≤ ε) :
    totalVariation (twistedLaw k p n G) (referenceLaw k p n π) ≤
      2 * (n + G : ℕ) * ε + ∑ s : State k with n + G ≤ s.2.val, π s := by
  classical
  let W : Prefix k n → ℝ := fun v => twistedPrefixMass k p n G v.1 v.2
  let P : Prefix k n → ℝ := referenceLaw k p n π
  let Z := loopMass k p (n + G)
  let E := 2 * (n + G : ℕ) * ε + ∑ s : State k with n + G ≤ s.2.val, π s
  have hQ (x y : State k) : 0 ≤ kernel k p x y := by
    have hh (j : Fin k) : 0 ≤ suffixWeight k p j :=
      Finset.sum_nonneg fun a _ => pow_nonneg hp.le _
    unfold kernel
    split_ifs
    · exact div_nonneg hp.le (hh _)
    · exact div_nonneg (mul_nonneg hp.le (hh _)) (hh _)
    · exact le_rfl
  have hw : ∀ (m : ℕ) (s : State k) (v : Fin m → State k),
      0 ≤ pathWeight k p m s v := by
    intro m
    induction m with
    | zero => intro s v; exact zero_le_one
    | succ m ih => intro s v; exact mul_nonneg (hQ _ _) (ih _ _)
  have hrows : ∀ (m : ℕ) (s : State k),
      (∑ v : Fin m → State k, pathWeight k p m s v) = 1 := by
    intro m
    induction m with
    | zero => intro s; simp [pathWeight]
    | succ m ih =>
      intro s
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (m + 1) => State k)]
      rw [Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, pathWeight, Fin.cons_zero, Fin.cons_succ]
      simp_rw [← Finset.mul_sum, ih, mul_one]
      exact hrow s
  have hW (v : Prefix k n) : 0 ≤ W v := by
    dsimp [W]
    rw [twisted_prefix_marginal]
    exact mul_nonneg (hw _ _ _) (Matrix.pow_apply_nonneg hQ _ _ _)
  have hWsum : ∑ v, W v = Z := by
    rw [Fintype.sum_prod_type]
    exact twisted_prefix_total_mass k p n G
  have hPsum : ∑ v, P v = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [P, referenceLaw]
    simp_rw [← Finset.mul_sum, hrows, mul_one]
    exact hπsum
  have hZ : 0 < Z := loop_mass_pos k hk p hp (n + G) hL
  let B : Finset (State k) := Finset.univ.filter fun s => s.2.val < n + G
  have hcard : B.card ≤ 2 * (n + G) := by
    let f : {s // s ∈ B} → Bool × Fin (n + G) :=
      fun s => (s.val.1, ⟨s.val.2.val, (Finset.mem_filter.mp s.property).2⟩)
    have hf : Function.Injective f := by
      intro a b heq
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun x : Bool × Fin (n + G) => x.1) heq
      · apply Fin.ext
        exact congrArg (fun x : Bool × Fin (n + G) => x.2.val) heq
    have h := Fintype.card_le_of_injective f hf
    simpa using h
  have hlocal (s : State k) :
      (∑ v : Fin n → State k, |W (s,v) - P (s,v)|) ≤
        if s.2.val < n + G then ε else π s := by
    by_cases hs : s.2.val < n + G
    · rw [if_pos hs]
      calc
        (∑ v : Fin n → State k, |W (s,v) - P (s,v)|) =
            ∑ v : Fin n → State k, pathWeight k p n s v *
              |(kernel k p ^ G) (endpoint n s v) (flip s) - π (flip s)| := by
          apply Finset.sum_congr rfl
          intro v _
          dsimp [W, P, referenceLaw]
          rw [twisted_prefix_marginal, hflip]
          rw [show pathWeight k p n s v * (kernel k p ^ G) (endpoint n s v) (flip s) -
              π s * pathWeight k p n s v = pathWeight k p n s v *
                ((kernel k p ^ G) (endpoint n s v) (flip s) - π s) by ring,
            abs_mul, abs_of_nonneg (hw _ _ _)]
        _ ≤ ∑ v : Fin n → State k, pathWeight k p n s v * ε := by
          apply Finset.sum_le_sum
          intro v _
          exact mul_le_mul_of_nonneg_left (hmix _ _) (hw _ _ _)
        _ = ε := by rw [← Finset.sum_mul, hrows, one_mul]
    · rw [if_neg hs]
      have hc : n + G ≤ s.2.val := Nat.le_of_not_gt hs
      simp only [W, P, referenceLaw, twisted_prefix_support k p hp.le n G s _ hc,
        zero_sub, abs_neg]
      simp_rw [abs_of_nonneg (mul_nonneg (hπ _) (hw _ _ _)), ← Finset.mul_sum,
        hrows, mul_one]
      exact le_rfl
  have hraw : (∑ v, |W v - P v|) ≤ E := by
    rw [Fintype.sum_prod_type]
    calc
      _ ≤ ∑ s : State k, if s.2.val < n + G then ε else π s :=
        Finset.sum_le_sum fun s _ => hlocal s
      _ = (B.card : ℝ) * ε + ∑ s : State k with n + G ≤ s.2.val, π s := by
        rw [Finset.sum_ite]
        simp only [Finset.sum_const, nsmul_eq_mul]
        simp only [B, not_lt]
      _ ≤ E := by
        dsimp [E]
        gcongr
        exact_mod_cast hcard
  have hmass : |Z - 1| ≤ E := by
    calc
      |Z - 1| = |∑ v, (W v - P v)| := by rw [Finset.sum_sub_distrib, hWsum, hPsum]
      _ ≤ ∑ v, |W v - P v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ E := hraw
  have hnormalize : (∑ v, |W v / Z - W v|) = |1 - Z| := by
    calc
      (∑ v, |W v / Z - W v|) = ∑ v, (|1 - Z| / Z) * W v := by
        apply Finset.sum_congr rfl
        intro v _
        rw [show W v / Z - W v = ((1 - Z) / Z) * W v by field_simp,
          abs_mul, abs_div, abs_of_pos hZ, abs_of_nonneg (hW v)]
      _ = (|1 - Z| / Z) * Z := by rw [← Finset.mul_sum, hWsum]
      _ = |1 - Z| := div_mul_cancel₀ _ hZ.ne'
  have hnorm : (∑ v, |W v / Z - P v|) ≤ 2 * E := by
    calc
      (∑ v, |W v / Z - P v|) ≤ ∑ v, (|W v / Z - W v| + |W v - P v|) := by
        apply Finset.sum_le_sum
        intro v _
        simpa only [sub_add_sub_cancel] using abs_add_le (W v / Z - W v) (W v - P v)
      _ = |1 - Z| + ∑ v, |W v - P v| := by rw [Finset.sum_add_distrib, hnormalize]
      _ ≤ 2 * E := by rw [abs_sub_comm 1 Z]; linarith
  change (1 / 2 : ℝ) * ∑ v, |W v / Z - P v| ≤ E
  linarith

#print axioms complete_prefix_comparison_of_estimates
end D5.S3.TotalVariation.TwistedPrefixComparison
