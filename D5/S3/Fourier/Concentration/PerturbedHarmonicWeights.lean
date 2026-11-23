/- GID: D5/S3/Fourier/Concentration/PerturbedHarmonicWeights
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/PerturbedHarmonicWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An explicit harmonic-weight majorant on each permitted perturbation interval. -/

import D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

/-! Weight envelopes for comparing collision tests before and after spectral perturbations. -/

set_option autoImplicit false

noncomputable section

open Finset
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

namespace D5.S3.Fourier.Concentration.PerturbedHarmonicWeights

private theorem harmonicWeight_perturbed_le {a x y r : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hrx : r < x) (hnear : |y - x| ≤ r) :
    y / (a + y ^ 2) ≤ (x / (x - r)) * (x / (a + x ^ 2)) := by
  obtain ⟨hl, hu⟩ := abs_le.mp hnear
  have ht : 0 < x - r := sub_pos.mpr hrx
  have hx : 0 < x := hr.trans_lt hrx
  have hy : 0 < y := by linarith
  have hlow : y * (x - r) ≤ y ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_left (show x - r ≤ y by linarith) hy.le
  have hhigh : y * (x - r) ≤ x ^ 2 := by
    calc
      _ ≤ (x + r) * (x - r) :=
        mul_le_mul_of_nonneg_right (show y ≤ x + r by linarith) ht.le
      _ = x ^ 2 - r ^ 2 := by ring
      _ ≤ x ^ 2 := sub_le_self _ (sq_nonneg _)
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  calc
    _ = a * (y * (x - r)) + x ^ 2 * (y * (x - r)) := by ring
    _ ≤ a * x ^ 2 + x ^ 2 * y ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hhigh ha)
        (mul_le_mul_of_nonneg_left hlow (sq_nonneg _))
    _ = _ := by ring

private def extendDegree {J : Type*} (s : Finset J) :
    (s → ℕ) ↪ (J → ℕ) := by
  classical
  refine ⟨fun m j => if hj : j ∈ s then m ⟨j, hj⟩ else 0, ?_⟩
  intro m n h
  funext j
  simpa only [dite_eq_left j.property] using congrFun h j.val

private theorem extendDegree_of_mem {J : Type*} (s : Finset J) (m : s → ℕ) (j : s) :
    extendDegree s m j = m j := by
  classical
  change (if h : j.val ∈ s then m ⟨j.val, h⟩ else 0) = m j
  exact dite_eq_left j.property

private theorem extendDegree_of_not_mem {J : Type*} (s : Finset J) (m : s → ℕ)
    {j : J} (hj : j ∉ s) : extendDegree s m j = 0 := by
  classical
  change (if h : j ∈ s then m ⟨j, h⟩ else 0) = 0
  exact dite_eq_right hj

private theorem sum_extendDegree {J A : Type*} [Fintype J] [AddCommMonoid A]
    (s : Finset J) (m : s → ℕ) (f : J → ℕ → A) (hf : ∀ j, f j 0 = 0) :
    (∑ j, f j (extendDegree s m j)) = ∑ j : s, f j (m j) := by
  classical
  rw [← sum_subset (subset_univ s) (fun j _ hj => by rw [extendDegree_of_not_mem s m hj, hf j])]
  rw [sum_subtype s (fun _ => Iff.rfl)]
  exact sum_congr rfl fun j _ => congrArg (f j) (extendDegree_of_mem s m j)

private theorem prod_extendDegree {J A : Type*} [Fintype J] [CommMonoid A]
    (s : Finset J) (m : s → ℕ) (f : J → ℕ → A) (hf : ∀ j, f j 0 = 1) :
    (∏ j, f j (extendDegree s m j)) = ∏ j : s, f j (m j) := by
  classical
  rw [← prod_subset (subset_univ s) (fun j _ hj => by rw [extendDegree_of_not_mem s m hj, hf j])]
  rw [prod_subtype s (fun _ => Iff.rfl)]
  exact prod_congr rfl fun j _ => congrArg (f j) (extendDegree_of_mem s m j)

private theorem monomialWeight_extendDegree {J : Type*} [Fintype J]
    (s : Finset J) (m : s → ℕ) (w : J → ℝ) :
    monomialWeight w (extendDegree s m) = monomialWeight (fun j : s => w j) m := by
  have hcount := sum_extendDegree s m (fun _ k => k) (fun _ => rfl)
  have hfactorial := prod_extendDegree s m (fun _ k => k.factorial) (fun _ => rfl)
  have hweight := prod_extendDegree s m (fun j k => w j ^ k) (fun _ => pow_zero _)
  simp only [monomialWeight, Nat.multinomial, hcount, hfactorial, hweight]

private theorem monomialWeight_mono {J : Type*} [Fintype J]
    {u v : J → ℝ} (hu : ∀ j, 0 ≤ u j) (huv : ∀ j, u j ≤ v j) (m : J → ℕ) :
    monomialWeight u m ≤ monomialWeight v m := by
  unfold monomialWeight
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact prod_le_prod₀ (fun j _ => pow_nonneg (hu j) _)
    (fun j _ => pow_le_pow_left₀ (hu j) (huv j) _)

private def pairContribution {J : Type*} [Fintype J]
    (g w : J → ℝ) (η : ℝ) (m n : J → ℕ) : ℝ :=
  if |monomialFrequency g m - monomialFrequency g n| ≤ η
    then monomialWeight w m * monomialWeight w n else 0

private theorem collision_sub_diagonal {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (p : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    tailCollisionMass g w p η - diagonal w p =
      ∑ m ∈ piAntidiag univ p, ∑ n ∈ (piAntidiag univ p).erase m,
        pairContribution g w η m n := by
  change (∑ m ∈ piAntidiag univ p, ∑ n ∈ piAntidiag univ p,
    pairContribution g w η m n) - (∑ m ∈ piAntidiag univ p, monomialWeight w m ^ 2) = _
  rw [← sum_sub_distrib]
  refine sum_congr rfl (fun m hm => ?_)
  rw [← sum_erase_add _ _ hm]
  simp [pairContribution, hη, pow_two]

/-- Restricting the support and decreasing its nonnegative weights can only decrease
the contribution from distinct near-colliding degree vectors. -/
private theorem collision_excess_le_of_support_and_weights {J : Type*}
    [Fintype J] [DecidableEq J] (s : Finset J) (g v : J → ℝ) (u : s → ℝ)
    (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) (huv : ∀ j : s, u j ≤ v j)
    (p : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    tailCollisionMass (fun j : s => g j) u p η - diagonal u p ≤
      tailCollisionMass g v p η - diagonal v p := by
  classical
  rw [collision_sub_diagonal _ _ _ hη, collision_sub_diagonal _ _ _ hη]
  let e := extendDegree s
  have hdegree (m : s → ℕ) (hm : m ∈ piAntidiag univ p) :
      e m ∈ piAntidiag (univ : Finset J) p := by
    rw [mem_piAntidiag] at hm ⊢
    exact ⟨(sum_extendDegree s m (fun _ k => k) (fun _ => rfl)).trans hm.1,
      fun j _ => mem_univ j⟩
  have hfreq (m : s → ℕ) :
      monomialFrequency g (e m) = monomialFrequency (fun j : s => g j) m :=
    sum_extendDegree s m (fun j k => (k : ℝ) * g j) (fun j => by simp)
  have hweight (m : s → ℕ) : monomialWeight u m ≤ monomialWeight v (e m) := by
    rw [monomialWeight_extendDegree]
    exact monomialWeight_mono hu huv m
  have hpos (m n : J → ℕ) : 0 ≤ pairContribution g v η m n := by
    unfold pairContribution
    split_ifs
    · exact mul_nonneg (monomialWeight_nonneg v hv m) (monomialWeight_nonneg v hv n)
    · exact le_rfl
  apply sum_le_sum_of_injOn e e.injective.injOn
  · intro b hb
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hb
    exact hdegree m hm
  · intro m _
    apply sum_le_sum_of_injOn e e.injective.injOn
    · intro b hb
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hb
      obtain ⟨hne, hn⟩ := mem_erase.mp hn
      exact mem_erase.mpr ⟨fun he => hne (e.injective he), hdegree n hn⟩
    · intro n _
      unfold pairContribution
      rw [hfreq, hfreq]
      split_ifs
      · exact mul_le_mul (hweight m) (hweight n) (monomialWeight_nonneg u hu n)
          (monomialWeight_nonneg v hv (e m))
      · exact le_rfl
    · exact fun n _ _ => hpos (e m) n
  · exact fun m _ _ => sum_nonneg (fun n _ => hpos m n)

/-- A test on an enlarged reference support bounds the collision excess for the
perturbed cutoff, with the harmonic weights recomputed on that cutoff. -/
theorem collision_excess_le_on_perturbed_cutoff {J : Type*} [DecidableEq J]
    (V : Finset J) (g g' radius : J → ℝ) {a R X T η : ℝ}
    (ha : 0 ≤ a) (hR : ∀ j, radius j ≤ R) (hnear : ∀ j, |g' j - g j| ≤ radius j)
    (hpositive : ∀ j : V, radius j < g j)
    (hcover : ∀ j, X - R < g j → g j ≤ T + R → j ∈ V)
    (p : ℕ) (hη : 0 ≤ η) :
    (∀ j, X < g' j → g' j ≤ T → j ∈ V) ∧
    let s := (univ : Finset V).filter (fun j : V => X < g' j ∧ g' j ≤ T)
    let u : s → ℝ := fun j => g' j.val / (a + (g' j.val) ^ 2)
    let v : V → ℝ := fun j => (g j / (g j - radius j)) * (g j / (a + (g j) ^ 2))
    tailCollisionMass (fun j : s => g' j.val) u p η - diagonal u p ≤
      tailCollisionMass (fun j : V => g' j) v p η - diagonal v p := by
  classical
  constructor
  · intro j hjX hjT
    obtain ⟨hl, hu⟩ := abs_le.mp ((hnear j).trans (hR j))
    exact hcover j (by linarith) (by linarith)
  · intro s u v
    have hr (j : J) : 0 ≤ radius j := (abs_nonneg _).trans (hnear j)
    have hx (j : V) : 0 < g j := (hr j).trans_lt (hpositive j)
    have hy (j : V) : 0 < g' j := by
      have hl := (abs_le.mp (hnear j)).1
      linarith [hpositive j]
    apply collision_excess_le_of_support_and_weights s (fun j : V => g' j) v u _ _ _ p hη
    · intro j
      exact div_nonneg (hy j.val).le (by positivity)
    · intro j
      have hgap := sub_pos.mpr (hpositive j)
      exact mul_nonneg (div_nonneg (hx j).le hgap.le)
        (div_nonneg (hx j).le (by positivity))
    · exact fun j => harmonicWeight_perturbed_le ha (hr j.val) (hpositive j.val) (hnear j.val)

end D5.S3.Fourier.Concentration.PerturbedHarmonicWeights
