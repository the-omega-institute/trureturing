/- GID: D5/S3/Fourier/Concentration/CommonSpectralPerturbations
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/CommonSpectralPerturbations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Summable moment budgets give a common choice of finite spectral offsets. -/

import D5.S3.Fourier.Concentration.FiniteSpectralPerturbation

/-! A finite common-choice estimate for nonnegative spectral moment excesses. -/

set_option autoImplicit false

noncomputable section

open Finset
open D5.S3.Fourier.Concentration.FiniteSpectralPerturbation
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

namespace D5.S3.Fourier.Concentration.CommonSpectralPerturbations

private theorem finite_common_choice {A K : Type*} [Fintype A] [Nonempty A]
    (tests : Finset K) (loss : K → A → ℝ) (meanBound threshold : K → ℝ)
    (hnonneg : ∀ k ∈ tests, ∀ a, 0 ≤ loss k a)
    (hthreshold : ∀ k ∈ tests, 0 < threshold k)
    (hmean : ∀ k ∈ tests, (∑ a : A, loss k a) ≤ (Fintype.card A : ℝ) * meanBound k)
    (hbudget : (∑ k ∈ tests, meanBound k / threshold k) < 1) :
    ∃ a : A, ∀ k ∈ tests, loss k a ≤ threshold k := by
  classical
  by_contra! h
  let failed (k : K) (a : A) : ℝ := if threshold k < loss k a then 1 else 0
  have hpointwise (a : A) : 1 ≤ ∑ k ∈ tests, failed k a := by
    obtain ⟨k, hk, hbad⟩ := h a
    simpa [failed, hbad] using
      (single_le_sum (f := fun k => failed k a)
        (fun i _ => by dsimp [failed]; split_ifs <;> positivity) hk)
  have hfailed (k : K) (hk : k ∈ tests) :
      ∑ a : A, failed k a ≤ (Fintype.card A : ℝ) * (meanBound k / threshold k) := by
    have hpart :
        (∑ a : A, failed k a) * threshold k ≤ ∑ a : A, loss k a := by
      rw [sum_mul]
      apply sum_le_sum
      intro a _
      by_cases ha : threshold k < loss k a
      · simpa [failed, ha] using ha.le
      · simpa [failed, ha] using hnonneg k hk a
    have hq := (le_div_iff₀ (hthreshold k hk)).2 (hpart.trans (hmean k hk))
    simpa only [mul_div_assoc] using hq
  have hcard : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have hle : (Fintype.card A : ℝ) ≤
      (Fintype.card A : ℝ) * ∑ k ∈ tests, meanBound k / threshold k := by
    calc
      _ = ∑ _ : A, (1 : ℝ) := by simp
      _ ≤ ∑ a : A, ∑ k ∈ tests, failed k a := sum_le_sum fun a _ => hpointwise a
      _ = ∑ k ∈ tests, ∑ a : A, failed k a := sum_comm
      _ ≤ ∑ k ∈ tests, (Fintype.card A : ℝ) * (meanBound k / threshold k) :=
        sum_le_sum hfailed
      _ = _ := (mul_sum ..).symm
  exact (not_lt_of_ge hle) (by simpa using mul_lt_mul_of_pos_left hbudget hcard)

private theorem lift_finite_mean {J : Type*} [DecidableEq J]
    (M : J → ℕ) {U V : Finset J} (hVU : V ⊆ U)
    (loss : ((j : V) → Fin (M j + 2)) → ℝ) {bound : ℝ}
    (hmean : (∑ x, loss x) ≤ (Fintype.card ((j : V) → Fin (M j + 2)) : ℝ) * bound) :
    (∑ x : ((j : U) → Fin (M j + 2)), loss (fun i : V => x ⟨i, hVU i.2⟩)) ≤
      (Fintype.card ((j : U) → Fin (M j + 2)) : ℝ) * bound := by
  classical
  let T := {j : U // (j : J) ∉ V}
  let From := (j : U) → Fin (M j + 2)
  let View := (j : V) → Fin (M j + 2)
  let Rest := (j : T) → Fin (M j.1 + 2)
  let part := Equiv.piEquivPiSubtypeProd (fun j : U => (j : J) ∈ V)
    (fun j : U => Fin (M j + 2))
  let index : {j : U // (j : J) ∈ V} ≃ V :=
    { toFun := fun j => ⟨j.1.val, j.2⟩
      invFun := fun j => ⟨⟨j.val, hVU j.2⟩, j.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let first := Equiv.piCongrLeft (fun j : V => Fin (M j + 2)) index
  let e : From ≃ View × Rest := part.trans (Equiv.prodCongr first (Equiv.refl Rest))
  have heq (x : From) : (e x).1 = fun j : V => x ⟨j, hVU j.2⟩ := by
    apply first.symm.injective
    funext j
    simp only [e, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.refl_apply, first,
      Equiv.symm_apply_apply, Equiv.piCongrLeft_symm_apply]
    rfl
  have hs : (∑ x : From, loss (fun i : V => x ⟨i, hVU i.2⟩)) =
      ∑ y : View × Rest, loss y.1 := by
    exact Fintype.sum_equiv e _ _ (fun x => congrArg loss (heq x).symm)
  have hcard : Fintype.card From = Fintype.card View * Fintype.card Rest := by
    simpa only [Fintype.card_prod] using Fintype.card_congr e
  change (∑ x : From, loss (fun i : V => x ⟨i, hVU i.2⟩)) ≤ (Fintype.card From : ℝ) * bound
  rw [hs, Fintype.sum_prod_type, hcard, Nat.cast_mul]
  simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
  rw [mul_comm (Fintype.card View : ℝ), mul_assoc]
  exact mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg _)

private theorem exists_for_finite_tests {J K : Type*} [DecidableEq J]
    (M : J → ℕ) (support : K → Finset J) (tests : Finset K)
    (loss : ∀ k, (((j : support k) → Fin (M j + 2)) → ℝ))
    (meanBound threshold : K → ℝ)
    (hnonneg : ∀ k ∈ tests, ∀ x, 0 ≤ loss k x)
    (hthreshold : ∀ k ∈ tests, 0 < threshold k)
    (hmean : ∀ k ∈ tests, (∑ x, loss k x) ≤
      (Fintype.card ((j : support k) → Fin (M j + 2)) : ℝ) * meanBound k)
    (hbudget : (∑ k ∈ tests, meanBound k / threshold k) < 1) :
    ∃ x : (j : J) → Fin (M j + 2), ∀ k ∈ tests, loss k (fun j => x j) ≤ threshold k := by
  classical
  let U := tests.biUnion support
  have hsub (k : K) (hk : k ∈ tests) : support k ⊆ U :=
    fun _ hi => mem_biUnion.mpr ⟨k, hk, hi⟩
  let localLoss (k : K) (x : (j : U) → Fin (M j + 2)) : ℝ :=
    if hk : k ∈ tests then loss k (fun j => x ⟨j, hsub k hk j.2⟩) else 0
  have hlocalNonneg (k : K) (hk : k ∈ tests) (x : (j : U) → Fin (M j + 2)) :
      0 ≤ localLoss k x := by
    simpa only [localLoss, dite_eq_left hk] using hnonneg k hk (fun j => x ⟨j, hsub k hk j.2⟩)
  have hlocalMean (k : K) (hk : k ∈ tests) :
      (∑ x : (j : U) → Fin (M j + 2), localLoss k x)
        ≤ (Fintype.card ((j : U) → Fin (M j + 2)) : ℝ) * meanBound k := by
    simpa only [localLoss, dite_eq_left hk] using
      lift_finite_mean M (hsub k hk) (loss k) (hmean k hk)
  obtain ⟨x, hx⟩ :=
    finite_common_choice tests localLoss meanBound threshold
      hlocalNonneg hthreshold hlocalMean hbudget
  refine ⟨fun j => if hj : j ∈ U then x ⟨j, hj⟩ else 0, fun k hk => ?_⟩
  simpa only [localLoss, dite_eq_left hk, dite_eq_left (hsub k hk (Subtype.property _))] using hx k hk

private theorem exists_for_all_finite_support_tests {J K : Type*} [DecidableEq J]
    (M : J → ℕ) (support : K → Finset J)
    (loss : ∀ k, (((j : support k) → Fin (M j + 2)) → ℝ))
    (meanBound threshold : K → ℝ)
    (hnonneg : ∀ k x, 0 ≤ loss k x)
    (hthreshold : ∀ k, 0 < threshold k)
    (hmean : ∀ k, (∑ x, loss k x) ≤
      (Fintype.card ((j : support k) → Fin (M j + 2)) : ℝ) * meanBound k)
    (hbudget : ∀ tests : Finset K, (∑ k ∈ tests, meanBound k / threshold k) < 1) :
    ∃ x : (j : J) → Fin (M j + 2), ∀ k, loss k (fun j => x j) ≤ threshold k := by
  let good (k : K) : Set ((j : J) → Fin (M j + 2)) :=
    {x | loss k (fun j => x j) ≤ threshold k}
  have hclosed (k : K) : IsClosed (good k) := by
    change IsClosed ((Finset.restrict (π := fun j => Fin (M j + 2)) (support k)) ⁻¹'
      {y | loss k y ≤ threshold k})
    exact (isClosed_discrete _).preimage (Finset.continuous_restrict (support k))
  have hfinite (tests : Finset K) : (⋂ k ∈ tests, good k).Nonempty := by
    obtain ⟨x, hx⟩ := exists_for_finite_tests M support tests loss meanBound threshold
      (fun k _ => hnonneg k) (fun k _ => hthreshold k) (fun k _ => hmean k) (hbudget tests)
    exact ⟨x, Set.mem_iInter.mpr fun k => Set.mem_iInter.mpr fun hk => hx k hk⟩
  obtain ⟨x, hx⟩ := CompactSpace.iInter_nonempty hclosed hfinite
  exact ⟨x, fun k => Set.mem_iInter.mp hx k⟩

private def diagonalMass {J : Type*} [Fintype J] [DecidableEq J]
    (w : J → ℝ) (p : ℕ) : ℝ :=
  ∑ m ∈ piAntidiag univ p, monomialWeight w m ^ 2

private def offDiagonalMass {J : Type*} [Fintype J] [DecidableEq J]
    (w : J → ℝ) (p : ℕ) : ℝ :=
  (∑ j, w j) ^ (2 * p) - diagonalMass w p

private theorem collision_between {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (p : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    diagonalMass w p ≤ tailCollisionMass g w p η ∧
    tailCollisionMass g w p η ≤ (∑ j, w j) ^ (2 * p) := by
  let s := piAntidiag (univ : Finset J) p
  let c := monomialWeight w
  let freq := monomialFrequency g
  let E (m n : J → ℕ) := if |freq m - freq n| ≤ η then c m * c n else 0
  have hc (m : J → ℕ) : 0 ≤ c m := monomialWeight_nonneg w hw m
  have hcSum : (∑ m ∈ s, c m) = (∑ j, w j) ^ p := by
    symm
    exact sum_pow_eq_sum_piAntidiag univ w p
  change (∑ m ∈ s, c m ^ 2) ≤ (∑ m ∈ s, ∑ n ∈ s, E m n) ∧
    (∑ m ∈ s, ∑ n ∈ s, E m n) ≤ (∑ j, w j) ^ (2 * p)
  constructor
  · apply sum_le_sum
    intro m hm
    have h := single_le_sum (f := E m) (fun n _ => by
      dsimp [E]
      split_ifs
      · exact mul_nonneg (hc m) (hc n)
      · exact le_rfl) hm
    simpa [E, pow_two, hη] using h
  · rw [mul_comm 2 p, pow_mul, ← hcSum]
    have hproduct : (∑ n ∈ s, c n) ^ 2 = ∑ m ∈ s, ∑ n ∈ s, c m * c n := by
      rw [pow_two, sum_mul]
      exact sum_congr rfl (fun m _ => mul_sum ..)
    rw [hproduct]
    apply sum_le_sum
    intro m _
    apply sum_le_sum
    intro n _
    dsimp [E]
    split_ifs
    · exact (le_rfl : c m * c n ≤ c m * c n)
    · exact mul_nonneg (hc m) (hc n)

/-- A single perturbation meets all the finite-resolution budgets in the family. -/
theorem exists_common_nearby_collision_bounds {J K : Type*} [DecidableEq J]
    (M : J → ℕ) (g ε : J → ℝ) (hε : ∀ j, 0 < ε j)
    (support : K → Finset J) (w : ∀ k, support k → ℝ)
    (hw : ∀ k j, 0 ≤ w k j) (p : K → ℕ) (η ρ b : K → ℝ)
    (hη : ∀ k, 0 ≤ η k) (hb : ∀ k, 0 < b k)
    (hρ : ∀ k (j : support k),
      ((min (M j + 2) (1 + ⌊η k * ((M j : ℝ) + 1) / ε j⌋₊) : ℕ) : ℝ) /
        (M j + 2) ≤ ρ k)
    (hbudget : ∀ tests : Finset K, ∑ k ∈ tests,
      (if 0 < offDiagonalMass (w k) (p k) then ρ k / b k else 0) < 1) :
    ∃ g' : J → ℝ, (∀ j, |g' j - g j| ≤ ε j) ∧
      ∀ k, tailCollisionMass (fun j : support k => g' j) (w k) (p k) (η k) ≤
        diagonalMass (w k) (p k) + b k * offDiagonalMass (w k) (p k) := by
  classical
  let D (k : K) := diagonalMass (w k) (p k)
  let B (k : K) := offDiagonalMass (w k) (p k)
  let E (k : K) (x : (j : support k) → Fin (M j + 2)) :=
    tailCollisionMass (fun j : support k => g j + offset (ε j) (x j)) (w k) (p k) (η k)
  let loss (k : K) (x : (j : support k) → Fin (M j + 2)) :=
    if 0 < B k then (E k x - D k) / B k else 0
  let rate (k : K) := if 0 < B k then ρ k else 0
  have hbetween (k : K) (x : (j : support k) → Fin (M j + 2)) :
      D k ≤ E k x ∧ E k x ≤ D k + B k := by
    have h := collision_between (fun j : support k => g j + offset (ε j) (x j))
      (w k) (hw k) (p k) (hη k)
    refine ⟨h.1, h.2.trans_eq ?_⟩
    dsimp [D, B, offDiagonalMass]
    ring
  have hnonneg (k : K) (x : (j : support k) → Fin (M j + 2)) : 0 ≤ loss k x := by
    dsimp only [loss]
    split_ifs with hk
    · exact div_nonneg (sub_nonneg.mpr (hbetween k x).1) hk.le
    · exact le_rfl
  have hmean (k : K) :
      (∑ x, loss k x) ≤ (Fintype.card ((j : support k) → Fin (M j + 2)) : ℝ) * rate k := by
    by_cases hk : 0 < B k
    · have hbound : (∑ x, E k x) ≤
          (Fintype.card ((j : support k) → Fin (M j + 2)) : ℝ) *
            (D k + ρ k * B k) :=
        sum_grid_collisionMass_le (fun j : support k => M j)
          (fun j => g j) (w k) (fun j => ε j) (hw k) (p k)
          (fun j => hε j) (hη k) (hρ k)
      simp only [loss, rate, ite_eq_left hk, ← sum_div, sum_sub_distrib, sum_const, card_univ,
        nsmul_eq_mul]
      apply (div_le_iff₀ hk).mpr
      linarith only [hbound]
    · simp [loss, rate, hk]
  have hbudget' (tests : Finset K) : ∑ k ∈ tests, rate k / b k < 1 := by
    refine lt_of_eq_of_lt (sum_congr rfl ?_) (hbudget tests)
    intro k _
    by_cases hk : 0 < B k <;> simp [rate, B, hk] at *
  obtain ⟨x, hx⟩ := exists_for_all_finite_support_tests M support loss rate b
    hnonneg hb hmean hbudget'
  refine ⟨fun j => g j + offset (ε j) (x j), ?_, ?_⟩
  · intro j
    rw [add_sub_cancel_left]
    exact offset_abs_le (hε j).le (x j)
  · intro k
    change E k (fun j => x j) ≤ D k + b k * B k
    by_cases hk : 0 < B k
    · have hz := hx k
      dsimp only [loss] at hz
      rw [ite_eq_left hk, div_le_iff₀ hk] at hz
      linarith only [hz]
    · have hpair := hbetween k (fun j => x j)
      have hzero : B k = 0 := le_antisymm (le_of_not_gt hk) (by linarith only [hpair.1, hpair.2])
      simpa [hzero] using hpair.2

#print axioms exists_common_nearby_collision_bounds

end D5.S3.Fourier.Concentration.CommonSpectralPerturbations
