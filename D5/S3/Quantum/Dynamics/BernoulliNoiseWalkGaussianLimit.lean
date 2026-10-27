/- GID: D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every localized quantum Bernoulli noise walk has the standard Gaussian limit. -/

import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Bernoulli

/-! The localized quantum Bernoulli noise walk of C. Wang, C. Wang, Y. Tang and S. Ren,
Advances in Mathematical Physics 2018, Article 2507265, DOI 10.1155/2018/2507265 (CC BY 4.0).
The creation and annihilation operators act on the finite-subset orthonormal basis.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit

abbrev BernoulliSpace := lp (fun _ : Finset ℕ => ℂ) 2
private def flipIndex (k : ℕ) : Equiv.Perm (Finset ℕ) where
  toFun σ := symmDiff σ {k}
  invFun σ := symmDiff σ {k}
  left_inv σ := symmDiff_symmDiff_cancel_right {k} σ
  right_inv σ := symmDiff_symmDiff_cancel_right {k} σ
private def flipOperator (k : ℕ) : BernoulliSpace →ₗᵢ[ℂ] BernoulliSpace where
  toFun φ := ⟨fun σ => φ (flipIndex k σ), memℓp_gen
    ((flipIndex k).summable_iff.mpr ((lp.memℓp φ).summable (by norm_num)))⟩
  map_add' φ ψ := by ext σ; rfl
  map_smul' c φ := by ext σ; rfl
  norm_map' φ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal)]
    congr 1
    exact (flipIndex k).tsum_eq (fun σ : Finset ℕ => ‖φ σ‖ ^ (2 : ENNReal).toReal)
private def mask (s : Set (Finset ℕ)) : BernoulliSpace →L[ℂ] BernoulliSpace := by
  classical
  exact LinearMap.mkContinuous
    { toFun := fun φ => ⟨fun σ => if σ ∈ s then φ σ else 0,
        (lp.memℓp φ).mono' (fun σ => by split_ifs <;> simp)⟩
      map_add' := by
        intro φ ψ
        ext σ
        change (if σ ∈ s then φ σ + ψ σ else 0) =
          (if σ ∈ s then φ σ else 0) + (if σ ∈ s then ψ σ else 0)
        split_ifs <;> simp
      map_smul' := by
        intro c φ
        ext σ
        change (if σ ∈ s then c * φ σ else 0) = c * (if σ ∈ s then φ σ else 0)
        split_ifs <;> simp }
    1 (fun φ => by
      rw [one_mul]
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro σ
      change ‖if σ ∈ s then φ σ else 0‖ ≤ ‖φ σ‖
      split_ifs <;> simp)
def annihilation (k : ℕ) : BernoulliSpace →L[ℂ] BernoulliSpace :=
  (mask {σ | k ∉ σ}).comp (flipOperator k).toContinuousLinearMap
def creation (k : ℕ) : BernoulliSpace →L[ℂ] BernoulliSpace :=
  (mask {σ | k ∈ σ}).comp (flipOperator k).toContinuousLinearMap

/-- The source's right operator, the positive flip projection. -/
def R (k : ℕ) : BernoulliSpace →L[ℂ] BernoulliSpace :=
  (1 / 2 : ℂ) • (creation k + annihilation k + ContinuousLinearMap.id ℂ BernoulliSpace)

/-- The source's left operator, the negative of the negative flip projection. -/
def L (k : ℕ) : BernoulliSpace →L[ℂ] BernoulliSpace :=
  (1 / 2 : ℂ) • (creation k + annihilation k - ContinuousLinearMap.id ℂ BernoulliSpace)

/-- Equations (53) and (16): the localized state and its walk recursion. -/
def walk (φ : BernoulliSpace) : ℕ → ℤ → BernoulliSpace :=
  Nat.rec (fun x => if x = 0 then φ else 0)
    (fun n ψ x => R n (ψ (x - 1)) + L n (ψ (x + 1)))

/-- The squared amplitude law of the position divided by the square root of time. -/
def walkLaw (φ : BernoulliSpace) (n : ℕ) : Measure ℝ :=
  ∑ x ∈ Finset.Icc (-(n : ℤ)) n,
    ENNReal.ofReal (‖walk φ n x‖ ^ 2) • Measure.dirac ((x : ℝ) / Real.sqrt n)

private def branch : ℕ → Finset ℕ → BernoulliSpace →L[ℂ] BernoulliSpace :=
  Nat.rec (fun _ => ContinuousLinearMap.id ℂ BernoulliSpace)
    (fun n b σ => (if n ∈ σ then -L n else R n).comp (b σ))

private def displacement (n : ℕ) (σ : Finset ℕ) : ℤ := (n : ℤ) - 2 * σ.card

private def phaseStep (k : ℕ) (u : ℝ) : BernoulliSpace →L[ℂ] BernoulliSpace :=
  (Real.cos u : ℂ) • ContinuousLinearMap.id ℂ BernoulliSpace +
    ((Real.sin u : ℂ) * Complex.I) • (flipOperator k).toContinuousLinearMap

private def phaseProduct : ℕ → ℝ → BernoulliSpace →L[ℂ] BernoulliSpace :=
  Nat.rec (fun _ => ContinuousLinearMap.id ℂ BernoulliSpace)
    (fun n p u => (phaseStep n u).comp (p u))

private lemma flipIndex_of_mem (k : ℕ) (σ : Finset ℕ) (hk : k ∈ σ) :
    flipIndex k σ = σ.erase k := by
  change symmDiff σ {k} = σ.erase k
  ext j
  by_cases hj : j = k <;> simp [Finset.mem_symmDiff, hj, hk]

private lemma flipIndex_of_notMem (k : ℕ) (σ : Finset ℕ) (hk : k ∉ σ) :
    flipIndex k σ = insert k σ := by
  change symmDiff σ {k} = insert k σ
  ext j
  by_cases hj : j = k <;> simp [Finset.mem_symmDiff, hj, hk]

private lemma flip_basis (k : ℕ) (σ : Finset ℕ) :
    flipOperator k (lp.single 2 σ (1 : ℂ)) = lp.single 2 (flipIndex k σ) (1 : ℂ) := by
  ext τ
  change (Pi.single σ (1 : ℂ) : Finset ℕ → ℂ) (flipIndex k τ) =
    (Pi.single (flipIndex k σ) (1 : ℂ) : Finset ℕ → ℂ) τ
  have he : flipIndex k τ = σ ↔ τ = flipIndex k σ := by
    constructor
    · intro h
      have hh := congrArg (flipIndex k) h
      change symmDiff (symmDiff τ {k}) {k} = flipIndex k σ at hh
      rwa [symmDiff_symmDiff_cancel_right] at hh
    · intro h
      rw [h]
      exact symmDiff_symmDiff_cancel_right {k} σ
  simp only [Pi.single_apply]
  exact if_congr he rfl rfl

private lemma mask_apply (s : Set (Finset ℕ)) (φ : BernoulliSpace) (σ : Finset ℕ) :
    mask s φ σ = s.indicator φ σ := by
  classical
  rfl

private lemma mask_basis (s : Set (Finset ℕ)) [DecidablePred (· ∈ s)] (σ : Finset ℕ) :
    mask s (lp.single 2 σ (1 : ℂ)) = if σ ∈ s then lp.single 2 σ (1 : ℂ) else 0 := by
  classical
  split_ifs with hs
  · ext τ
    rw [mask_apply]
    by_cases ht : τ = σ
    · subst τ; rw [Set.indicator_of_mem hs]
    · have h0 := lp.single_apply_ne (E := fun _ : Finset ℕ => ℂ) 2 σ (1 : ℂ) ht
      by_cases hτ : τ ∈ s
      · rw [Set.indicator_of_mem hτ]
      · rw [Set.indicator_of_notMem hτ, h0]
  · ext τ
    rw [mask_apply]
    by_cases ht : τ = σ
    · subst τ; rw [Set.indicator_of_notMem hs]; rfl
    · have h0 := lp.single_apply_ne (E := fun _ : Finset ℕ => ℂ) 2 σ (1 : ℂ) ht
      by_cases hτ : τ ∈ s
      · rw [Set.indicator_of_mem hτ, h0]; rfl
      · rw [Set.indicator_of_notMem hτ]; rfl

private lemma annihilation_basis (k : ℕ) (σ : Finset ℕ) :
    annihilation k (lp.single 2 σ (1 : ℂ)) =
      if k ∈ σ then lp.single 2 (σ.erase k) (1 : ℂ) else 0 := by
  classical
  rw [annihilation, ContinuousLinearMap.comp_apply]
  change mask {τ : Finset ℕ | k ∉ τ} (flipOperator k (lp.single 2 σ (1 : ℂ))) = _
  rw [flip_basis, mask_basis]
  by_cases hk : k ∈ σ
  · rw [flipIndex_of_mem k σ hk]
    simp only [Set.mem_ofPred_eq, Finset.notMem_erase, not_false_eq_true, ite_true, ite_eq_left hk]
  · rw [flipIndex_of_notMem k σ hk]
    simp only [Set.mem_ofPred_eq, Finset.mem_insert_self, not_true_eq_false, ite_false,
      ite_eq_right hk]

private lemma creation_basis (k : ℕ) (σ : Finset ℕ) :
    creation k (lp.single 2 σ (1 : ℂ)) =
      if k ∈ σ then 0 else lp.single 2 (insert k σ) (1 : ℂ) := by
  classical
  rw [creation, ContinuousLinearMap.comp_apply]
  change mask {τ : Finset ℕ | k ∈ τ} (flipOperator k (lp.single 2 σ (1 : ℂ))) = _
  rw [flip_basis, mask_basis]
  by_cases hk : k ∈ σ
  · rw [flipIndex_of_mem k σ hk]
    simp only [Set.mem_ofPred_eq, Finset.notMem_erase, ite_false, ite_eq_left hk]
  · rw [flipIndex_of_notMem k σ hk]
    simp only [Set.mem_ofPred_eq, Finset.mem_insert_self, ite_true, ite_eq_right hk]

private lemma flip_involution (k : ℕ) (φ : BernoulliSpace) :
    flipOperator k (flipOperator k φ) = φ := by
  ext σ
  change φ (symmDiff (symmDiff σ {k}) {k}) = φ σ
  rw [symmDiff_symmDiff_cancel_right]

private lemma flip_commute (k j : ℕ) (φ : BernoulliSpace) :
    flipOperator k (flipOperator j φ) = flipOperator j (flipOperator k φ) := by
  ext σ
  change φ (symmDiff (symmDiff σ {k}) {j}) = φ (symmDiff (symmDiff σ {j}) {k})
  rw [symmDiff_right_comm]

private lemma flip_selfadjoint (k : ℕ) (φ ψ : BernoulliSpace) :
    inner ℂ (flipOperator k φ) ψ = inner ℂ φ (flipOperator k ψ) := by
  have h := (flipOperator k).inner_map_map φ (flipOperator k ψ)
  rwa [flip_involution] at h

private lemma operators_eq_flip (k : ℕ) :
    creation k + annihilation k = (flipOperator k).toContinuousLinearMap := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro σ
  apply ContinuousLinearMap.ext
  intro c
  change (creation k + annihilation k) (lp.single 2 σ c) =
    flipOperator k (lp.single 2 σ c)
  have hs : (lp.single 2 σ c : BernoulliSpace) = c • lp.single 2 σ (1 : ℂ) := by
    simpa only [smul_eq_mul, mul_one] using
      lp.single_smul (E := fun _ : Finset ℕ => ℂ) 2 σ c (1 : ℂ)
  rw [hs, map_smul, map_smul]
  apply congrArg (fun η : BernoulliSpace => c • η)
  rw [add_apply, annihilation_basis, creation_basis, flip_basis]
  by_cases hk : k ∈ σ
  · rw [ite_eq_left hk, ite_eq_left hk, zero_add, flipIndex_of_mem k σ hk]
  · rw [ite_eq_right hk, ite_eq_right hk, add_zero, flipIndex_of_notMem k σ hk]

private lemma right_apply (k : ℕ) (φ : BernoulliSpace) :
    R k φ = (1 / 2 : ℂ) • (flipOperator k φ + φ) := by
  rw [R, operators_eq_flip]
  rfl

private lemma left_apply (k : ℕ) (φ : BernoulliSpace) :
    L k φ = (1 / 2 : ℂ) • (flipOperator k φ - φ) := by
  rw [L, operators_eq_flip]
  rfl

private lemma projections (k : ℕ) :
    (R k).comp (R k) = R k ∧ (L k).comp (L k) = -L k ∧
    (R k).comp (L k) = 0 ∧ (L k).comp (R k) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    apply ContinuousLinearMap.ext
    intro φ
    simp only [ContinuousLinearMap.comp_apply, neg_apply,
      zero_apply, right_apply, left_apply, map_add, map_sub, map_smul, flip_involution]
    module

private lemma walk_support (φ : BernoulliSpace) (n : ℕ) (x : ℤ)
    (hx : (n : ℤ) < |x|) : walk φ n x = 0 := by
  induction n generalizing x with
  | zero =>
    have h : x ≠ 0 := by intro h; subst x; norm_num at hx
    exact ite_eq_right h
  | succ n ih =>
    have hm : (n : ℤ) < |x - 1| := by
      have hh := abs_add_le (x - 1) 1
      rw [sub_add_cancel, abs_one] at hh
      omega
    have hp : (n : ℤ) < |x + 1| := by
      have hh := abs_sub (x + 1) 1
      rw [add_sub_cancel_right, abs_one] at hh
      omega
    rw [walk.eq_1]
    change R n (walk φ n (x - 1)) + L n (walk φ n (x + 1)) = 0
    rw [ih (x - 1) hm, ih (x + 1) hp, map_zero, map_zero, add_zero]

private lemma branch_step (n : ℕ) (σ : Finset ℕ) (φ : BernoulliSpace) :
    branch (n + 1) σ φ =
      if n ∈ σ then -L n (branch n σ φ) else R n (branch n σ φ) := by
  rw [branch.eq_1]
  change (if n ∈ σ then -L n else R n) (branch n σ φ) = _
  split_ifs <;> rfl

private lemma branch_congr (n : ℕ) (σ τ : Finset ℕ)
    (h : ∀ k, k < n → (k ∈ σ ↔ k ∈ τ)) : branch n σ = branch n τ := by
  revert h
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    change (if n ∈ σ then -L n else R n).comp (branch n σ) =
      (if n ∈ τ then -L n else R n).comp (branch n τ)
    simp only [h n (Nat.lt_succ_self n),
      ih (fun k hk => h k (Nat.lt_succ_of_lt hk))]

private lemma branch_insert (n : ℕ) (σ : Finset ℕ) :
    branch n (insert n σ) = branch n σ := by
  apply branch_congr
  intro k hk
  simp only [Finset.mem_insert, ne_of_lt hk, false_or]

private lemma flip_right_commute (k j : ℕ) (φ : BernoulliSpace) :
    flipOperator k (R j φ) = R j (flipOperator k φ) := by
  rw [right_apply, right_apply, map_smul, map_add, flip_commute]

private lemma flip_left_commute (k j : ℕ) (φ : BernoulliSpace) :
    flipOperator k (L j φ) = L j (flipOperator k φ) := by
  rw [left_apply, left_apply, map_smul, map_sub, flip_commute]

private lemma branch_eigen (n : ℕ) (σ : Finset ℕ) (φ : BernoulliSpace)
    (k : ℕ) (hk : k < n) :
    flipOperator k (branch n σ φ) =
      (if k ∈ σ then (-1 : ℂ) else 1) • branch n σ φ := by
  revert hk
  induction n with
  | zero => intro hk; omega
  | succ n ih =>
    intro hk
    by_cases hkn : k = n
    · subst k
      have hp := projections n
      have hsum (ζ : BernoulliSpace) : flipOperator n ζ = R n ζ + L n ζ := by
        rw [right_apply, left_apply]
        module
      have hrr := congrArg
        (fun a : BernoulliSpace →L[ℂ] BernoulliSpace => a (branch n σ φ)) hp.1
      have hll := congrArg
        (fun a : BernoulliSpace →L[ℂ] BernoulliSpace => a (branch n σ φ)) hp.2.1
      have hrl := congrArg
        (fun a : BernoulliSpace →L[ℂ] BernoulliSpace => a (branch n σ φ)) hp.2.2.1
      have hlr := congrArg
        (fun a : BernoulliSpace →L[ℂ] BernoulliSpace => a (branch n σ φ)) hp.2.2.2
      change R n (R n (branch n σ φ)) = R n (branch n σ φ) at hrr
      change L n (L n (branch n σ φ)) = -L n (branch n σ φ) at hll
      change R n (L n (branch n σ φ)) = 0 at hrl
      change L n (R n (branch n σ φ)) = 0 at hlr
      rw [branch_step]
      by_cases hn : n ∈ σ
      · simp only [hn, ite_true, map_neg, neg_smul, one_smul]
        rw [hsum, hrl, hll, zero_add]
      · simp only [hn, ite_false, one_smul]
        rw [hsum, hrr, hlr, add_zero]
    · have hk' : k < n := by omega
      rw [branch_step]
      by_cases hn : n ∈ σ
      · simp only [hn, ite_true, map_neg]
        rw [flip_left_commute, ih hk', map_smul, smul_neg]
      · simp only [hn, ite_false]
        rw [flip_right_commute, ih hk', map_smul]

private lemma branch_orthogonal (n : ℕ) (σ τ : Finset ℕ)
    (hσ : σ ⊆ Finset.range n) (hτ : τ ⊆ Finset.range n) (hne : σ ≠ τ)
    (φ ψ : BernoulliSpace) : inner ℂ (branch n σ φ) (branch n τ ψ) = 0 := by
  classical
  obtain ⟨k, hk⟩ := not_forall.mp (fun h => hne (Finset.ext h))
  have hkn : k < n := by
    by_cases hks : k ∈ σ
    · exact Finset.mem_range.mp (hσ hks)
    · have hkt : k ∈ τ := by tauto
      exact Finset.mem_range.mp (hτ hkt)
  have hh := flip_selfadjoint k (branch n σ φ) (branch n τ ψ)
  rw [branch_eigen n σ φ k hkn, branch_eigen n τ ψ k hkn,
    inner_smul_left, inner_smul_right] at hh
  by_cases hks : k ∈ σ
  · have hkt : k ∉ τ := by intro ht; exact hk (by simp only [hks, ht])
    simp only [ite_eq_left hks, ite_eq_right hkt, map_neg, map_one, neg_mul, one_mul] at hh
    linear_combination -hh / 2
  · have hkt : k ∈ τ := by tauto
    simp only [ite_eq_right hks, ite_eq_left hkt, map_one, neg_mul, one_mul] at hh
    linear_combination hh / 2

private lemma orthogonal_norm_sum (s : Finset (Finset ℕ)) (v : Finset ℕ → BernoulliSpace)
    (h : ∀ σ ∈ s, ∀ τ ∈ s, σ ≠ τ → inner ℂ (v σ) (v τ) = 0) :
    ‖∑ σ ∈ s, v σ‖ ^ 2 = ∑ σ ∈ s, ‖v σ‖ ^ 2 := by
  have hh : inner ℂ (∑ σ ∈ s, v σ) (∑ σ ∈ s, v σ) =
      ∑ σ ∈ s, inner ℂ (v σ) (v σ) := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [inner_sum]
    apply Finset.sum_eq_single σ
    · intro τ hτ hτσ
      exact h σ hσ τ hτ hτσ.symm
    · intro hh
      exact (hh hσ).elim
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), hh, map_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (v σ)).symm

private lemma branch_resolution (n : ℕ) (φ : BernoulliSpace) :
    ∑ σ ∈ (Finset.range n).powerset, branch n σ φ = φ := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.powerset_empty, Finset.sum_singleton]; rfl
  | succ n ih =>
    calc
      _ = (∑ σ ∈ (Finset.range n).powerset, R n (branch n σ φ)) +
          ∑ σ ∈ (Finset.range n).powerset, -L n (branch n σ φ) := by
        rw [Finset.range_add_one, Finset.sum_powerset_insert (Finset.notMem_range_self (n := n))]
        apply congrArg₂ (fun a b : BernoulliSpace => a + b)
        · apply Finset.sum_congr rfl
          intro σ hσ
          have hn : n ∉ σ :=
            fun h => Finset.notMem_range_self (n := n) ((Finset.mem_powerset.mp hσ) h)
          rw [branch_step, ite_eq_right hn]
        · apply Finset.sum_congr rfl
          intro σ hσ
          rw [branch_step, ite_eq_left (Finset.mem_insert_self n σ), branch_insert]
      _ = ∑ σ ∈ (Finset.range n).powerset, branch n σ φ := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro σ hσ
        rw [right_apply, left_apply]
        module
      _ = φ := ih

private lemma displacement_bound (n : ℕ) (σ : Finset ℕ) (hσ : σ ⊆ Finset.range n) :
    displacement n σ ∈ Finset.Icc (-(n : ℤ)) n := by
  have hc := Finset.card_le_card hσ
  rw [Finset.card_range] at hc
  rw [displacement]
  rw [Finset.mem_Icc]
  constructor <;> omega

private lemma walk_expansion (φ : BernoulliSpace) (n : ℕ) (x : ℤ) :
    walk φ n x =
      ∑ σ ∈ (Finset.range n).powerset.filter (fun σ => displacement n σ = x),
        ((-1 : ℂ) ^ σ.card) • branch n σ φ := by
  classical
  induction n generalizing x with
  | zero =>
    rw [Finset.range_zero, Finset.powerset_empty, Finset.sum_filter, Finset.sum_singleton]
    simp [walk, displacement, branch, eq_comm]
  | succ n ih =>
    change R n (walk φ n (x - 1)) + L n (walk φ n (x + 1)) = _
    rw [ih (x - 1), ih (x + 1)]
    simp_rw [Finset.sum_filter]
    rw [Finset.range_add_one, Finset.sum_powerset_insert (Finset.notMem_range_self (n := n))]
    simp only [map_sum]
    apply congrArg₂ (fun a b : BernoulliSpace => a + b)
    · apply Finset.sum_congr rfl
      intro σ hσ
      have hn : n ∉ σ :=
        fun h => Finset.notMem_range_self (n := n) ((Finset.mem_powerset.mp hσ) h)
      have hd : displacement (n + 1) σ = x ↔ displacement n σ = x - 1 := by
        unfold displacement
        push_cast
        omega
      rw [branch_step, ite_eq_right hn]
      by_cases hx : displacement n σ = x - 1
      · rw [ite_eq_left hx, ite_eq_left (hd.mpr hx), map_smul]
      · rw [ite_eq_right hx, ite_eq_right (mt hd.mp hx), map_zero]
    · apply Finset.sum_congr rfl
      intro σ hσ
      have hn : n ∉ σ :=
        fun h => Finset.notMem_range_self (n := n) ((Finset.mem_powerset.mp hσ) h)
      have hd : displacement (n + 1) (insert n σ) = x ↔ displacement n σ = x + 1 := by
        unfold displacement
        rw [Finset.card_insert_of_notMem hn]
        push_cast
        omega
      rw [branch_step, ite_eq_left (Finset.mem_insert_self n σ), branch_insert]
      by_cases hx : displacement n σ = x + 1
      · rw [ite_eq_left hx, ite_eq_left (hd.mpr hx), map_smul,
          Finset.card_insert_of_notMem hn, pow_succ]
        module
      · rw [ite_eq_right hx, ite_eq_right (mt hd.mp hx), map_zero]

private lemma walk_exact_law (φ : BernoulliSpace) (n : ℕ) (x : ℤ) :
    ‖walk φ n x‖ ^ 2 =
      ∑ σ ∈ (Finset.range n).powerset.filter (fun σ => displacement n σ = x),
        ‖branch n σ φ‖ ^ 2 := by
  let s := (Finset.range n).powerset.filter (fun σ => displacement n σ = x)
  change ‖walk φ n x‖ ^ 2 = ∑ σ ∈ s, ‖branch n σ φ‖ ^ 2
  by_cases hx : (n : ℤ) < |x|
  · have hs : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro σ hσ
      obtain ⟨hσ, hσx⟩ := Finset.mem_filter.mp hσ
      have hb := Finset.mem_Icc.mp (displacement_bound n σ (Finset.mem_powerset.mp hσ))
      rw [hσx] at hb
      exact (not_le_of_gt hx) (abs_le.mpr hb)
    rw [walk_support φ n x hx, hs, Finset.sum_empty]
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)]
  · rw [walk_expansion]
    have ho : ∀ σ ∈ s, ∀ τ ∈ s, σ ≠ τ →
        inner ℂ (((-1 : ℂ) ^ σ.card) • branch n σ φ)
          (((-1 : ℂ) ^ τ.card) • branch n τ φ) = 0 := by
      intro σ hσ τ hτ hne
      have hh := branch_orthogonal n σ τ
        (Finset.mem_powerset.mp (Finset.mem_filter.mp hσ).1)
        (Finset.mem_powerset.mp (Finset.mem_filter.mp hτ).1) hne φ φ
      rw [inner_smul_left, inner_smul_right, hh, mul_zero, mul_zero]
    rw [orthogonal_norm_sum s _ ho]
    apply Finset.sum_congr rfl
    intro σ hσ
    simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

private lemma branch_parseval (φ : BernoulliSpace) (n : ℕ) :
    ∑ σ ∈ (Finset.range n).powerset, ‖branch n σ φ‖ ^ 2 = ‖φ‖ ^ 2 := by
  have hh := orthogonal_norm_sum (Finset.range n).powerset (fun σ => branch n σ φ)
    (fun σ hσ τ hτ hne => branch_orthogonal n σ τ
      (Finset.mem_powerset.mp hσ) (Finset.mem_powerset.mp hτ) hne φ φ)
  rw [branch_resolution] at hh
  exact hh.symm

private lemma walk_mass (φ : BernoulliSpace) (n : ℕ) :
    ∑ x ∈ Finset.Icc (-(n : ℤ)) n, ‖walk φ n x‖ ^ 2 = ‖φ‖ ^ 2 := by
  simp_rw [walk_exact_law]
  rw [Finset.sum_fiberwise_of_maps_to (fun σ hσ =>
    displacement_bound n σ (Finset.mem_powerset.mp hσ))]
  exact branch_parseval φ n

private lemma walkLaw_probability (φ : BernoulliSpace) (hφ : ‖φ‖ = 1) (n : ℕ) :
    IsProbabilityMeasure (walkLaw φ n) := by
  constructor
  rw [walkLaw, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => sq_nonneg ‖walk φ n x‖), walk_mass, hφ]
  norm_num

private lemma phaseStep_spectral (k : ℕ) (u : ℝ) (φ : BernoulliSpace) :
    phaseStep k u φ = Complex.exp ((u : ℂ) * Complex.I) • R k φ -
      Complex.exp (-(u : ℂ) * Complex.I) • L k φ := by
  change (Real.cos u : ℂ) • φ + ((Real.sin u : ℂ) * Complex.I) • flipOperator k φ = _
  rw [right_apply, left_apply, Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  module

private lemma phaseProduct_expansion (n : ℕ) (u : ℝ) (φ : BernoulliSpace) :
    phaseProduct n u φ = ∑ σ ∈ (Finset.range n).powerset,
      Complex.exp ((displacement n σ : ℂ) * u * Complex.I) • branch n σ φ := by
  induction n with
  | zero =>
    rw [Finset.range_zero, Finset.powerset_empty, Finset.sum_singleton]
    simp [phaseProduct, branch, displacement]
  | succ n ih =>
    rw [phaseProduct.eq_1]
    change phaseStep n u (phaseProduct n u φ) = _
    rw [ih, map_sum, Finset.range_add_one,
      Finset.sum_powerset_insert (Finset.notMem_range_self (n := n)), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ hσ
    have hn : n ∉ σ := fun h => Finset.notMem_range_self ((Finset.mem_powerset.mp hσ) h)
    rw [map_smul, phaseStep_spectral, branch_step, ite_eq_right hn,
      branch_step, ite_eq_left (Finset.mem_insert_self n σ), branch_insert]
    have hp : (displacement (n + 1) σ : ℂ) * u * Complex.I =
        (displacement n σ : ℂ) * u * Complex.I + (u : ℂ) * Complex.I := by
      unfold displacement
      push_cast
      ring
    have hm : (displacement (n + 1) (insert n σ) : ℂ) * u * Complex.I =
        (displacement n σ : ℂ) * u * Complex.I + -(u : ℂ) * Complex.I := by
      unfold displacement
      rw [Finset.card_insert_of_notMem hn]
      push_cast
      ring
    rw [hp, hm, Complex.exp_add, Complex.exp_add]
    module

private lemma branch_inner (n : ℕ) (σ : Finset ℕ) (hσ : σ ⊆ Finset.range n)
    (φ : BernoulliSpace) :
    inner ℂ φ (branch n σ φ) = ((‖branch n σ φ‖ ^ 2 : ℝ) : ℂ) := by
  calc
    _ = inner ℂ (∑ τ ∈ (Finset.range n).powerset, branch n τ φ) (branch n σ φ) := by
      rw [branch_resolution]
    _ = ∑ τ ∈ (Finset.range n).powerset, inner ℂ (branch n τ φ) (branch n σ φ) := by
      rw [sum_inner]
    _ = inner ℂ (branch n σ φ) (branch n σ φ) := by
      apply Finset.sum_eq_single σ
      · intro τ hτ hτσ
        exact branch_orthogonal n τ σ (Finset.mem_powerset.mp hτ) hσ hτσ φ φ
      · intro hh
        exact (hh (Finset.mem_powerset.mpr hσ)).elim
    _ = ((‖branch n σ φ‖ ^ 2 : ℝ) : ℂ) := by
      convert (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (branch n σ φ)) using 1
      push_cast
      congr 1

private lemma charFun_formula (φ : BernoulliSpace) (n : ℕ) (t : ℝ) :
    charFun (walkLaw φ n) t =
      inner ℂ φ (phaseProduct n (t / Real.sqrt n) φ) := by
  classical
  calc
    _ = ∑ x ∈ Finset.Icc (-(n : ℤ)) n,
        ∑ σ ∈ (Finset.range n).powerset.filter (fun σ => displacement n σ = x),
          Complex.exp ((displacement n σ : ℂ) * (t / Real.sqrt n) * Complex.I) *
            ((‖branch n σ φ‖ ^ 2 : ℝ) : ℂ) := by
      rw [charFun_apply_real, walkLaw, integral_finsetSum_measure]
      · simp only [integral_smul_measure, integral_dirac,
          ENNReal.toReal_ofReal (sq_nonneg _), Complex.real_smul]
        apply Finset.sum_congr rfl
        intro x hx
        rw [walk_exact_law, Complex.ofReal_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro σ hσ
        have hxσ := (Finset.mem_filter.mp hσ).2
        have he : (t : ℂ) * Complex.ofReal ((x : ℝ) / Real.sqrt n) * Complex.I =
            (displacement n σ : ℂ) * (t / Real.sqrt n) * Complex.I := by
          rw [hxσ]
          push_cast
          ring
        rw [he, mul_comm]
      · intro x hx
        exact (integrable_dirac (by simp)).smul_measure (by simp)
    _ = ∑ σ ∈ (Finset.range n).powerset,
        Complex.exp ((displacement n σ : ℂ) * (t / Real.sqrt n) * Complex.I) *
          ((‖branch n σ φ‖ ^ 2 : ℝ) : ℂ) :=
      Finset.sum_fiberwise_of_maps_to
        (fun σ hσ => displacement_bound n σ (Finset.mem_powerset.mp hσ)) _
    _ = inner ℂ φ (phaseProduct n (t / Real.sqrt n) φ) := by
      rw [phaseProduct_expansion, inner_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [inner_smul_right, branch_inner n σ (Finset.mem_powerset.mp hσ) φ]
      simp only [Complex.ofReal_div]

private lemma phaseProduct_isometry (n : ℕ) (u : ℝ) (φ : BernoulliSpace) :
    ‖phaseProduct n u φ‖ = ‖φ‖ := by
  have hs (k : ℕ) (ψ : BernoulliSpace) : ‖phaseStep k u ψ‖ = ‖ψ‖ := by
    apply (LinearMap.norm_map_iff_inner_map_map (phaseStep k u)).mpr ?_ ψ
    intro η ζ
    change inner ℂ ((Real.cos u : ℂ) • η +
      ((Real.sin u : ℂ) * Complex.I) • flipOperator k η)
      ((Real.cos u : ℂ) • ζ +
        ((Real.sin u : ℂ) * Complex.I) • flipOperator k ζ) = inner ℂ η ζ
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      map_mul, Complex.conj_ofReal, Complex.conj_I, (flipOperator k).inner_map_map,
      flip_selfadjoint]
    have hc : (Real.cos u : ℂ) ^ 2 + (Real.sin u : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq u
    calc
      _ = ((Real.cos u : ℂ) ^ 2 + (Real.sin u : ℂ) ^ 2) * inner ℂ η ζ := by
        ring_nf
        simp only [Complex.I_sq]
        ring
      _ = inner ℂ η ζ := by rw [hc, one_mul]
  induction n with
  | zero => rfl
  | succ n ih =>
    change ‖phaseStep n u (phaseProduct n u φ)‖ = ‖φ‖
    rw [hs, ih]

private lemma flip_subset_iff (k m : ℕ) (hk : k < m) (σ : Finset ℕ) :
    flipIndex k σ ⊆ Finset.range m ↔ σ ⊆ Finset.range m := by
  have h (τ : Finset ℕ) (hτ : τ ⊆ Finset.range m) :
      flipIndex k τ ⊆ Finset.range m := by
    intro j hj
    change j ∈ symmDiff τ {k} at hj
    rcases Finset.mem_symmDiff.mp hj with hj | hj
    · exact hτ hj.1
    · have hjk : j = k := Finset.mem_singleton.mp hj.1
      subst j
      exact Finset.mem_range.mpr hk
  constructor
  · intro hσ
    have hh := h (flipIndex k σ) hσ
    change symmDiff (symmDiff σ {k}) {k} ⊆ Finset.range m at hh
    rwa [symmDiff_symmDiff_cancel_right] at hh
  · exact h σ

private lemma phaseProduct_support (η : BernoulliSpace) (m n : ℕ)
    (hnm : n ≤ m) (hη : ∀ σ : Finset ℕ, ¬σ ⊆ Finset.range m → η σ = 0) (u : ℝ) :
    ∀ σ : Finset ℕ, ¬σ ⊆ Finset.range m → phaseProduct n u η σ = 0 := by
  revert hnm
  induction n with
  | zero => intro _; exact hη
  | succ n ih =>
    intro hnm σ hσ
    have hn : n < m := lt_of_lt_of_le (Nat.lt_succ_self n) hnm
    have hf : ¬flipIndex n σ ⊆ Finset.range m :=
      fun h => hσ ((flip_subset_iff n m hn σ).mp h)
    change (Real.cos u : ℂ) * phaseProduct n u η σ +
      ((Real.sin u : ℂ) * Complex.I) * phaseProduct n u η (flipIndex n σ) = 0
    rw [ih (Nat.le_of_succ_le hnm) σ hσ, ih (Nat.le_of_succ_le hnm) _ hf]
    simp only [mul_zero, add_zero]

private lemma tail_cross_zero (η : BernoulliSpace) (m n : ℕ) (hmn : m ≤ n)
    (hη : ∀ σ : Finset ℕ, ¬σ ⊆ Finset.range m → η σ = 0) (u : ℝ) :
    inner ℂ η (flipOperator n (phaseProduct n u η)) = 0 := by
  have hηn : ∀ σ : Finset ℕ, ¬σ ⊆ Finset.range n → η σ = 0 := by
    intro σ hσ
    exact hη σ (fun h => hσ (h.trans (Finset.range_mono hmn)))
  rw [← flip_selfadjoint, lp.inner_eq_tsum]
  suffices hz : ∀ σ : Finset ℕ,
      inner ℂ (flipOperator n η σ) (phaseProduct n u η σ) = 0 by
    simp only [hz, tsum_zero]
  intro σ
  by_cases hσ : σ ⊆ Finset.range n
  · have hnσ : n ∉ σ := fun h => (Nat.lt_irrefl n) (Finset.mem_range.mp (hσ h))
    have hflip : ¬flipIndex n σ ⊆ Finset.range m := by
      intro hh
      have hn : n ∈ flipIndex n σ := by
        change n ∈ symmDiff σ {n}
        exact Finset.mem_symmDiff.mpr (Or.inr ⟨Finset.mem_singleton_self n, hnσ⟩)
      have := Finset.mem_range.mp (hh hn)
      omega
    change inner ℂ (η (flipIndex n σ)) (phaseProduct n u η σ) = 0
    rw [hη _ hflip, inner_zero_left]
  · rw [phaseProduct_support η n n le_rfl hηn u σ hσ, inner_zero_right]

private lemma finite_tail_factorization (η : BernoulliSpace) (m n : ℕ) (hmn : m ≤ n)
    (hη : ∀ σ : Finset ℕ, ¬σ ⊆ Finset.range m → η σ = 0) (u : ℝ) :
    inner ℂ η (phaseProduct n u η) =
      (Real.cos u : ℂ) ^ (n - m) * inner ℂ η (phaseProduct m u η) := by
  induction n, hmn using Nat.le_induction with
  | base => simp only [Nat.sub_self, pow_zero, one_mul]
  | succ n hmn ih =>
    change inner ℂ η ((Real.cos u : ℂ) • phaseProduct n u η +
      ((Real.sin u : ℂ) * Complex.I) • flipOperator n (phaseProduct n u η)) = _
    rw [inner_add_right, inner_smul_right, inner_smul_right,
      tail_cross_zero η m n hmn hη u, mul_zero, add_zero, ih]
    have hn : n + 1 - m = (n - m) + 1 := by omega
    rw [hn, pow_succ]
    ring

private lemma cosine_gaussian_limit (t : ℝ) :
    Tendsto (fun n : ℕ => (Real.cos (t / Real.sqrt n) : ℂ) ^ n)
      atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  let p : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  let ν : Measure ℝ := bernoulliMeasure 1 (-1) p
  have h0 : (∫ x : ℝ, x ∂ν) = 0 := by
    change (∫ x : ℝ, x ∂bernoulliMeasure 1 (-1) p) = 0
    rw [integral_bernoulliMeasure]
    norm_num [p]
  have h1 : (∫ x : ℝ, x ^ 2 ∂ν) = 1 := by
    change (∫ x : ℝ, x ^ 2 ∂bernoulliMeasure 1 (-1) p) = 1
    rw [integral_bernoulliMeasure]
    norm_num [p]
  have hc (u : ℝ) : charFun ν u = (Real.cos u : ℂ) := by
    rw [charFun_apply_real]
    change (∫ x : ℝ, Complex.exp ((u : ℂ) * x * Complex.I)
      ∂bernoulliMeasure 1 (-1) p) = _
    rw [integral_bernoulliMeasure]
    simp only [p, Complex.ofReal_one, Complex.ofReal_neg, mul_one, mul_neg_one]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.real_smul]
    norm_num
    ring
  have hh := tendsto_charFun_inv_sqrt_mul_pow (P := ν) (X := id)
    measurable_id.aemeasurable h0 h1 t
  simpa only [Measure.map_id, hc, div_eq_inv_mul] using hh

private lemma phaseProduct_continuous (n : ℕ) (η : BernoulliSpace) :
    Continuous (fun u : ℝ => phaseProduct n u η) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    change Continuous (fun u : ℝ => (Real.cos u : ℂ) • phaseProduct n u η +
      ((Real.sin u : ℂ) * Complex.I) • flipOperator n (phaseProduct n u η))
    exact ((Complex.continuous_ofReal.comp Real.continuous_cos).smul ih).add
      (((Complex.continuous_ofReal.comp Real.continuous_sin).mul continuous_const).smul
        ((flipOperator n).continuous.comp ih))

private lemma phaseProduct_zero (n : ℕ) (η : BernoulliSpace) :
    phaseProduct n 0 η = η := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (Real.cos 0 : ℂ) • phaseProduct n 0 η +
      ((Real.sin 0 : ℂ) * Complex.I) • flipOperator n (phaseProduct n 0 η) = η
    simpa only [Real.cos_zero, Real.sin_zero, Complex.ofReal_one, Complex.ofReal_zero,
      one_smul, zero_mul, zero_smul, add_zero] using ih

private lemma finite_matrix_limit (η : BernoulliSpace) (m : ℕ)
    (hη : ∀ σ : Finset ℕ, ¬σ ⊆ Finset.range m → η σ = 0) (t : ℝ) :
    Tendsto (fun n : ℕ => inner ℂ η (phaseProduct n (t / Real.sqrt n) η))
      atTop (𝓝 ((‖η‖ ^ 2 : ℝ) * Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  have hu : Tendsto (fun n : ℕ => t / Real.sqrt n) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
        tendsto_natCast_atTop_atTop)).const_mul t
  have hc : Tendsto (fun n : ℕ => (Real.cos (t / Real.sqrt n) : ℂ)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.cos_zero, Complex.ofReal_one] using
      ((Complex.continuous_ofReal.comp Real.continuous_cos).tendsto 0).comp hu
  have hp : Tendsto (fun n : ℕ => (Real.cos (t / Real.sqrt n) : ℂ) ^ (n - m))
      atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
    have hh := (cosine_gaussian_limit t).div (hc.pow m) (by simp)
    simp only [one_pow, div_one] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop m, hc.eventually_ne (by norm_num : (1 : ℂ) ≠ 0)]
      with n hn hn0
    change (Real.cos (t / Real.sqrt n) : ℂ) ^ n /
      (Real.cos (t / Real.sqrt n) : ℂ) ^ m = _
    rw [pow_sub₀ _ hn0 hn, div_eq_mul_inv]
  have hf : Tendsto (fun n : ℕ => inner ℂ η (phaseProduct m (t / Real.sqrt n) η))
      atTop (𝓝 ((‖η‖ ^ 2 : ℝ) : ℂ)) := by
    have hh := (((continuous_const : Continuous (fun _ : ℝ => η)).inner
      (𝕜 := ℂ) (phaseProduct_continuous m η)).tendsto 0).comp hu
    convert hh using 1 <;> simp only [Function.comp_def, phaseProduct_zero,
      inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    congr 1
  have hh := hp.mul hf
  rw [mul_comm] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop m] with n hn
  exact (finite_tail_factorization η m n hn hη (t / Real.sqrt n)).symm

private lemma finite_vectors_dense (φ : BernoulliSpace) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : BernoulliSpace, ∃ m : ℕ,
      (∀ σ : Finset ℕ, ¬σ ⊆ Finset.range m → η σ = 0) ∧ ‖φ - η‖ < ε := by
  classical
  obtain ⟨s, hs⟩ := ((lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) φ).eventually
    (Metric.ball_mem_nhds φ hε)).exists
  let η : BernoulliSpace := ∑ σ ∈ s, lp.single 2 σ (φ σ)
  let m : ℕ := (s.biUnion id).sup id + 1
  refine ⟨η, m, ?_, ?_⟩
  · intro σ hσ
    change (∑ τ ∈ s, lp.single 2 τ (φ τ)) σ = 0
    rw [lp.coeFn_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro τ hτ
    apply lp.single_apply_ne
    intro he
    subst τ
    apply hσ
    intro j hj
    apply Finset.mem_range.mpr
    have hjb : j ∈ s.biUnion id := Finset.mem_biUnion.mpr ⟨σ, hτ, hj⟩
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hjb)
  · change dist η φ < ε at hs
    simpa only [dist_eq_norm, norm_sub_rev] using hs

private lemma matrix_lipschitz (n : ℕ) (u : ℝ) (φ η : BernoulliSpace) :
    ‖inner ℂ φ (phaseProduct n u φ) - inner ℂ η (phaseProduct n u η)‖ ≤
      (‖φ‖ + ‖η‖) * ‖φ - η‖ := by
  have he : inner ℂ φ (phaseProduct n u φ) - inner ℂ η (phaseProduct n u η) =
      inner ℂ (φ - η) (phaseProduct n u φ) +
      inner ℂ η (phaseProduct n u (φ - η)) := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ ‖inner ℂ (φ - η) (phaseProduct n u φ)‖ +
        ‖inner ℂ η (phaseProduct n u (φ - η))‖ := norm_add_le _ _
    _ ≤ ‖φ - η‖ * ‖phaseProduct n u φ‖ +
        ‖η‖ * ‖phaseProduct n u (φ - η)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = (‖φ‖ + ‖η‖) * ‖φ - η‖ := by
      rw [phaseProduct_isometry, phaseProduct_isometry]
      ring

private lemma matrix_gaussian_limit (φ : BernoulliSpace) (hφ : ‖φ‖ = 1) (t : ℝ) :
    Tendsto (fun n : ℕ => inner ℂ φ (phaseProduct n (t / Real.sqrt n) φ))
      atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  let z : ℂ := Complex.exp (-(t : ℂ) ^ 2 / 2)
  have hz : ‖z‖ ≤ 1 := by
    have he : charFun (gaussianReal 0 1) t = z := by
      simp only [charFun_gaussianReal, NNReal.coe_one, Complex.ofReal_zero,
        Complex.ofReal_one, mul_zero, zero_mul, one_mul, zero_sub]
      congr 1
      ring
    rw [← he]
    exact norm_charFun_le_one t
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ : ℝ := min 1 (ε / 12)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨η, m, hη, hd⟩ := finite_vectors_dense φ δ hδ
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε / 12 := min_le_right _ _
  have hη2 : ‖η‖ ≤ 2 := by
    have hh := norm_le_norm_add_norm_sub φ η
    rw [hφ] at hh
    linarith
  have hdiff : |‖η‖ - 1| ≤ ‖φ - η‖ := by
    simpa only [hφ, abs_sub_comm] using abs_norm_sub_norm_le φ η
  have hsq : |‖η‖ ^ 2 - 1| ≤ 3 * ‖φ - η‖ := by
    calc
      |‖η‖ ^ 2 - 1| = |‖η‖ - 1| * (‖η‖ + 1) := by
        rw [← abs_of_nonneg (show 0 ≤ ‖η‖ + 1 by positivity), ← abs_mul]
        congr 1
        ring
      _ ≤ ‖φ - η‖ * (‖η‖ + 1) :=
        mul_le_mul_of_nonneg_right hdiff (by positivity)
      _ ≤ 3 * ‖φ - η‖ := by nlinarith [norm_nonneg (φ - η)]
  have ht : ‖((‖η‖ ^ 2 : ℝ) : ℂ) * z - z‖ ≤ 3 * ‖φ - η‖ := by
    rw [← sub_one_mul, norm_mul]
    calc
      _ ≤ ‖((‖η‖ ^ 2 : ℝ) : ℂ) - 1‖ * 1 :=
        mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ = |‖η‖ ^ 2 - 1| := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, mul_one]
      _ ≤ 3 * ‖φ - η‖ := hsq
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (finite_matrix_limit η m hη t)
    (ε / 3) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn
  have ha := matrix_lipschitz n (t / Real.sqrt n) φ η
  rw [hφ] at ha
  have ha' : ‖inner ℂ φ (phaseProduct n (t / Real.sqrt n) φ) -
      inner ℂ η (phaseProduct n (t / Real.sqrt n) η)‖ ≤ 3 * ‖φ - η‖ := by
    nlinarith [norm_nonneg (φ - η)]
  have hb : ‖inner ℂ η (phaseProduct n (t / Real.sqrt n) η) -
      ((‖η‖ ^ 2 : ℝ) : ℂ) * z‖ < ε / 3 := by
    simpa only [dist_eq_norm] using hN n hn
  rw [dist_eq_norm]
  have hc := norm_sub_le_norm_sub_add_norm_sub
    (inner ℂ φ (phaseProduct n (t / Real.sqrt n) φ))
    (inner ℂ η (phaseProduct n (t / Real.sqrt n) η)) z
  have hc' := norm_sub_le_norm_sub_add_norm_sub
    (inner ℂ η (phaseProduct n (t / Real.sqrt n) η))
    (((‖η‖ ^ 2 : ℝ) : ℂ) * z) z
  change ‖inner ℂ φ (phaseProduct n (t / Real.sqrt n) φ) - z‖ < ε
  linarith

/-- Every unit localized initial state has the classical standard Gaussian scaling limit. -/
theorem result (φ : BernoulliSpace) (hφ : ‖φ‖ = 1) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ y, f y ∂(walkLaw φ n)) atTop
      (𝓝 (∫ y, f y ∂(gaussianReal 0 1))) := by
  let μ : ℕ → ProbabilityMeasure ℝ :=
    fun n => ⟨walkLaw φ n, walkLaw_probability φ hφ n⟩
  let γ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hc : Tendsto μ atTop (𝓝 γ) := by
    apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
    intro t
    change Tendsto (fun n => charFun (walkLaw φ n) t) atTop
      (𝓝 (charFun (gaussianReal 0 1) t))
    simp only [charFun_formula, charFun_gaussianReal, zero_mul, mul_zero,
      NNReal.coe_one, Complex.ofReal_zero, Complex.ofReal_one, one_mul, zero_sub]
    convert matrix_gaussian_limit φ hφ t using 2
    congr 1
    ring
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hc f

end D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit
