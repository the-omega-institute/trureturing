/- GID: D5/S3/Entropy/Forgetting/DeterministicEntropyEquality
   generality: G
   mirror-B: D5/B/S3/Entropy/Forgetting/DeterministicEntropyEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Classify equality and strict loss for deterministic finite entropy pushforwards. -/

/- Library-search audit trail (2026-08-15):
   * Pinned-mathlib searches for finite Shannon entropy, deterministic pushforwards, equality,
     injectivity on support, `negMulLog`, and strict merging found no matching theorem.
   * The repository supplies the deterministic nonincrease theorem, injective relabeling invariance,
     and the exact zero-conditional-entropy classification on nonzero-marginal slices.
   * The proof identifies those slices with the positive-mass fibers of the forgetting map.
     Zero-mass fibers are deliberately excluded, since their artificial conditional laws carry no
     information.
-/

import D5.S3.Entropy.ConditionalEntropyEquality
import D5.S3.Entropy.Forgetting.CapacityMonotone
import D5.S3.Entropy.Relabeling.InjectiveInvariance

namespace D5.S3.Entropy.Forgetting.DeterministicEntropyEquality

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.ConditionalEntropyEquality
open D5.S3.Entropy.EntropyNonneg
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.Relabeling.InjectiveInvariance

private theorem pushforward_entropy_le {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X → ℝ) (f : X → Y) (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    shannonEntropy (pushforward f p) ≤ shannonEntropy p := by
  classical
  have hexists : ∃ x, p x ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : ∑ x, p x = 0 := Finset.sum_eq_zero fun x _ => h x
    rw [hp.2] at hzero
    norm_num at hzero
  rcases hexists with ⟨x₀, hx₀⟩
  let fRange : X → Set.range f := fun x => ⟨f x, ⟨x, rfl⟩⟩
  let inclusion : Set.range f → Y := fun y => y.1
  let q : Set.range f → ℝ := pushforward fRange p
  letI : Nonempty X := ⟨x₀⟩
  letI : Nonempty (Set.range f) := ⟨fRange x₀⟩
  have hsurjective : Function.Surjective fRange := by
    intro y
    rcases y.property with ⟨x, hx⟩
    refine ⟨x, Subtype.ext ?_⟩
    exact hx
  have hq_le : shannonEntropy q ≤ shannonEntropy p := by
    change shannonEntropy (pushforward fRange p) ≤ shannonEntropy p
    exact (deterministic_forgetting_entropy_capacity_monotone p fRange hp hsurjective).1
  have hinclusion : Function.Injective inclusion := by
    intro y₁ y₂ h
    exact Subtype.ext h
  have hpushforward :
      Function.extend inclusion q (fun _ => 0) = pushforward f p := by
    funext y
    by_cases hy : y ∈ Set.range f
    · let yr : Set.range f := ⟨y, hy⟩
      have hextend : Function.extend inclusion q (fun _ => 0) (inclusion yr) = q yr :=
        hinclusion.extend_apply q (fun _ => 0) yr
      change Function.extend inclusion q (fun _ => 0) (inclusion yr) = pushforward f p y
      rw [hextend]
      simp only [q, pushforward]
      apply Finset.sum_congr rfl
      intro x _
      simp [fRange, yr]
    · have hnot_range : ¬ ∃ yr, inclusion yr = y := by
        rintro ⟨yr, hyr⟩
        rcases yr.property with ⟨x, hx⟩
        apply hy
        exact ⟨x, hx.trans hyr⟩
      rw [Function.extend_apply' _ _ _ hnot_range]
      simp only [pushforward]
      symm
      apply Finset.sum_eq_zero
      intro x _
      have hxy : f x ≠ y := fun h => hy ⟨x, h⟩
      simp [hxy]
  calc
    shannonEntropy (pushforward f p) = shannonEntropy q := by
      rw [← hpushforward]
      exact shannonEntropy_extend_injective hinclusion q
    _ ≤ shannonEntropy p := hq_le

/-- A deterministic pushforward preserves entropy exactly when its map is injective on the
support of the input law. Atoms of zero mass impose no injectivity requirement. -/
theorem pushforward_entropy_eq_iff_injective_on_support
    {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X → ℝ) (f : X → Y) (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    shannonEntropy (pushforward f p) = shannonEntropy p ↔
      Set.InjOn f {x | p x ≠ 0} := by
  classical
  let joint : Y × X → ℝ := fun z => if f z.2 = z.1 then p z.2 else 0
  have hjoint_nonneg : ∀ z, 0 ≤ joint z := by
    intro z
    simp only [joint]
    split_ifs
    · exact hp.1 z.2
    · exact le_rfl
  have hmarginal : marginal joint = pushforward f p := by
    funext y
    rfl
  have hjoint_entropy : shannonEntropy joint = shannonEntropy p := by
    rw [shannonEntropy, Fintype.sum_prod_type]
    calc
      (∑ y, ∑ x, Real.negMulLog (if f x = y then p x else 0)) =
          ∑ x, ∑ y, Real.negMulLog (if f x = y then p x else 0) := Finset.sum_comm
      _ = ∑ x, Real.negMulLog (p x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_eq_single (f x)]
        · simp
        · intro y _ hy
          simp [Ne.symm hy]
        · simp
      _ = shannonEntropy p := rfl
  have hchain := entropy_chain_rule joint hjoint_nonneg
  rw [hmarginal, hjoint_entropy] at hchain
  have hzero :
      shannonEntropy (pushforward f p) = shannonEntropy p ↔
        conditionalEntropy joint = 0 := by
    constructor <;> intro h <;> linarith
  rw [hzero, conditional_entropy_eq_zero_iff_point_mass_on_support joint hjoint_nonneg]
  constructor
  · intro hpoint x₁ hx₁ x₂ hx₂ hfx
    change p x₁ ≠ 0 at hx₁
    change p x₂ ≠ 0 at hx₂
    let y := f x₁
    have hfx₁ : f x₁ = y := rfl
    have hfx₂ : f x₂ = y := by simpa [y] using hfx.symm
    have hx₁_pos : 0 < p x₁ := lt_of_le_of_ne (hp.1 x₁) (Ne.symm hx₁)
    have hmarginal_pos : 0 < marginal joint y := by
      rw [marginal]
      calc
        0 < joint (y, x₁) := by simpa [joint, hfx₁] using hx₁_pos
        _ ≤ ∑ x, joint (y, x) :=
          Finset.single_le_sum (fun x _ => hjoint_nonneg (y, x)) (Finset.mem_univ x₁)
    rcases hpoint y (ne_of_gt hmarginal_pos) with ⟨x₀, hconditional⟩
    have hconditional_ne (x : X) (hx : p x ≠ 0) (hxy : f x = y) :
        conditional joint y x ≠ 0 := by
      rw [conditional]
      exact div_ne_zero (by simpa [joint, hxy] using hx) (ne_of_gt hmarginal_pos)
    have hx₁_eq : x₁ = x₀ := by
      by_contra hne
      have heval := congrFun hconditional x₁
      rw [if_neg hne] at heval
      exact hconditional_ne x₁ hx₁ hfx₁ heval
    have hx₂_eq : x₂ = x₀ := by
      by_contra hne
      have heval := congrFun hconditional x₂
      rw [if_neg hne] at heval
      exact hconditional_ne x₂ hx₂ hfx₂ heval
    exact hx₁_eq.trans hx₂_eq.symm
  · intro hinjective y hmarginal_ne
    have hexists : ∃ x, f x = y ∧ p x ≠ 0 := by
      by_contra h
      push Not at h
      apply hmarginal_ne
      rw [marginal]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hxy : f x = y
      · simp [joint, hxy, h x hxy]
      · simp [joint, hxy]
    rcases hexists with ⟨x₀, hfx₀, hx₀⟩
    have hmarginal_eq : marginal joint y = p x₀ := by
      rw [marginal, Finset.sum_eq_single x₀]
      · simp [joint, hfx₀]
      · intro x _ hne
        by_cases hxy : f x = y
        · have hx_zero : p x = 0 := by
            by_contra hx
            exact hne (hinjective hx hx₀ (hxy.trans hfx₀.symm))
          simp [joint, hxy, hx_zero]
        · simp [joint, hxy]
      · simp
    refine ⟨x₀, ?_⟩
    funext x
    rw [conditional, hmarginal_eq]
    by_cases hxx₀ : x = x₀
    · subst x
      simp [joint, hfx₀, hx₀]
    · by_cases hxy : f x = y
      · have hx_zero : p x = 0 := by
          by_contra hx
          exact hxx₀ (hinjective hx hx₀ (hxy.trans hfx₀.symm))
        simp [joint, hxy, hx_zero, hxx₀]
      · simp [joint, hxy, hxx₀]

/-- A deterministic pushforward loses entropy strictly exactly when its map identifies two
nonzero-mass atoms. -/
theorem pushforward_entropy_lt_iff_not_injective_on_support
    {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X → ℝ) (f : X → Y) (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    shannonEntropy (pushforward f p) < shannonEntropy p ↔
      ¬ Set.InjOn f {x | p x ≠ 0} := by
  have hle := pushforward_entropy_le p f hp
  have heq := pushforward_entropy_eq_iff_injective_on_support p f hp
  constructor
  · intro hlt hinjective
    exact (ne_of_lt hlt) (heq.2 hinjective)
  · intro hnot_injective
    exact lt_of_le_of_ne hle fun h => hnot_injective (heq.1 h)

end D5.S3.Entropy.Forgetting.DeterministicEntropyEquality
