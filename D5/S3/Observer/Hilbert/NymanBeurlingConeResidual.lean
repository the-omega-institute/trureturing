/- GID: D5/S3/Observer/Hilbert/NymanBeurlingConeResidual
   generality: I
   mirror-B: D5/B/S3/Observer/Hilbert/NymanBeurlingConeResidual
   mirror-E: none(waiver:noncomputational-structural-bridge)
   anchors: []
   utility: none
   digest: The actual complex Nyman closed-span residual is the real-cone residual and dual witness. -/

import D5.S3.Observer.Hilbert.NymanBeurlingFiniteGramDistance
import D5.S3.Quantum.Completion.BoundedInverseLimitReconstruction
import D5.S3.Observer.Separation.MoreauDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Hilbert.NymanBeurlingConeResidual

open Set MeasureTheory
open scoped InnerProductSpace
open D5.S3.Observer.Hilbert.NymanBeurlingFiniteGramDistance
open D5.S3.Quantum.Completion.BoundedInverseLimitReconstruction
open D5.S3.Observer.Separation.ConeResidualWitness
open D5.S3.Observer.Separation.MoreauDecomposition

/-- The actual infinite arithmetic completion, owned by cumulativeSpace. -/
abbrev M : Submodule ℂ Carrier := cumulativeSpace shell

/-- The source indicator target, without a new representative or measure. -/
abbrev chi : Carrier := target

theorem shell_monotone : Monotone shell := by
  intro n m hnm
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hnm⟩, rfl⟩

theorem shell_zero : shell 0 = ⊥ := by
  simp [shell]

theorem cumulative_eq_closure_union :
    (M : Set Carrier) = closure (⋃ n : ℕ, (shell n : Set Carrier)) := by
  change closure (↑(⨆ n, shell n) : Set Carrier) = _
  rw [Submodule.coe_iSup_of_directed shell shell_monotone.directed_le]

theorem shell_union_eq_positive_union :
    (⋃ n : ℕ, (shell n : Set Carrier)) =
      ⋃ n : ℕ, ⋃ (_ : 0 < n), (shell n : Set Carrier) := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by omega, shell_monotone (by omega) hn⟩
  · rintro ⟨n, _, hn⟩
    exact ⟨n, hn⟩

theorem cumulative_eq_closure_positive_union :
    (M : Set Carrier) =
      closure (⋃ n : ℕ, ⋃ (_ : 0 < n), (shell n : Set Carrier)) := by
  rw [cumulative_eq_closure_union, shell_union_eq_positive_union]

theorem shell_le_cumulative (n : ℕ) : shell n ≤ M :=
  le_trans (le_iSup shell n) (⨆ k, shell k).le_topologicalClosure

theorem sourceVector_mem (n : ℕ) :
    sourceVector (n + 1) (by omega) ∈ shell (n + 1) ∧
      sourceVector (n + 1) (by omega) ∈ M := by
  have h : sourceVector (n + 1) (by omega) ∈ shell (n + 1) :=
    Submodule.subset_span ⟨⟨n, by omega⟩, rfl⟩
  exact ⟨h, shell_le_cumulative (n + 1) h⟩

theorem complex_smul_mem (c : ℂ) {s : Carrier} (hs : s ∈ M) : c • s ∈ M :=
  M.smul_mem c hs

theorem residualSpace_eq : residualSpace shell = M.orthogonal := rfl

private instance cumulative_complete : CompleteSpace M :=
  (Submodule.isClosed_topologicalClosure (⨆ n, shell n)).completeSpace_coe

/-- Scalar restriction keeps the full complex subspace as the cone's closed set. -/
def K : ProperCone ℝ Carrier where
  toSubmodule := (M.restrictScalars ℝ).restrictScalars {r : ℝ // 0 ≤ r}
  isClosed' := Submodule.isClosed_topologicalClosure _

theorem mem_cone (x : Carrier) : x ∈ K ↔ x ∈ M := Iff.rfl

/-- The existing L2 real pairing equals the real part of its complex pairing. -/
theorem real_inner_eq (x y : Carrier) : inner ℝ x y = (inner ℂ x y).re := by
  simp only [L2.inner_def]
  exact integral_re (L2.integrable_inner (𝕜 := ℂ) x y)

/-- Compare the independently supplied nearest point and complex projection. -/
theorem coneProjection_eq (x : Carrier) : coneProjection K x = M.starProjection x := by
  have hp := Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex
      K.nonempty K.isClosed.isComplete K.convex x)
  have hmem : coneProjection K x ∈ M := hp.1
  have hmin : ‖x - coneProjection K x‖ = ⨅ w : (M : Set Carrier), ‖x - w‖ := hp.2
  exact (Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem
    ((M.norm_eq_iInf_iff_inner_eq_zero hmem).mp hmin)).symm

theorem cone_residual_eq (x : Carrier) :
    x - coneProjection K x = M.orthogonal.starProjection x := by
  rw [coneProjection_eq, Submodule.starProjection_orthogonal_val]

private theorem real_annihilator_iff (w : Carrier) :
    (∀ s ∈ M, inner ℝ s w = 0) ↔ w ∈ M.orthogonal := by
  constructor
  · intro h s hs
    apply Complex.ext
    · simpa only [real_inner_eq, Complex.zero_re] using h s hs
    · have hi := h (Complex.I • s) (M.smul_mem Complex.I hs)
      simpa [real_inner_eq, inner_smul_left, Complex.mul_re, Complex.mul_im] using hi
  · intro h s hs
    rw [real_inner_eq, Submodule.inner_right_of_mem_orthogonal hs h]
    rfl

theorem mem_innerDual_iff (w : Carrier) :
    w ∈ ProperCone.innerDual (K : Set Carrier) ↔ w ∈ M.orthogonal := by
  rw [← real_annihilator_iff]
  constructor
  · intro hw s hs
    have hp := ProperCone.mem_innerDual.mp hw hs
    have hn := ProperCone.mem_innerDual.mp hw (M.neg_mem hs)
    rw [inner_neg_left] at hn
    exact le_antisymm (by linarith) hp
  · intro hw
    rw [ProperCone.mem_innerDual]
    intro s hs
    exact le_of_eq (hw s hs).symm

/-- Polar membership uses the existing Moreau convention: the negative is dual. -/
theorem mem_polar_iff (w : Carrier) :
    -w ∈ ProperCone.innerDual (K : Set Carrier) ↔ w ∈ M.orthogonal := by
  rw [mem_innerDual_iff, Submodule.neg_mem_iff]

theorem cone_signs (w : Carrier) :
    (w ∈ ProperCone.innerDual (K : Set Carrier) ↔ ∀ s ∈ K, 0 ≤ inner ℝ s w) ∧
      (-w ∈ ProperCone.innerDual (K : Set Carrier) ↔ ∀ s ∈ K, inner ℝ w s ≤ 0) := by
  constructor
  · exact ⟨fun h s hs => ProperCone.mem_innerDual.mp h hs,
      fun h => ProperCone.mem_innerDual.mpr (fun _ hs => h _ hs)⟩
  · constructor
    · intro h s hs
      have hn := ProperCone.mem_innerDual.mp h hs
      simpa only [inner_neg_right, neg_nonneg, real_inner_comm] using hn
    · intro h
      apply ProperCone.mem_innerDual.mpr
      intro s hs
      simpa only [inner_neg_right, neg_nonneg, real_inner_comm] using h s hs

/-- Independently defined source-side orthogonal residual. -/
def rNB : Carrier := M.orthogonal.starProjection chi

/-- The source-side orthogonal projection of the indicator. -/
def pNB : Carrier := M.starProjection chi

/-- The negative source residual is the canonical real-dual witness. -/
def wNB : Carrier := -rNB

theorem nyman_beurling_cone_residual :
    chi = pNB + rNB ∧ pNB ∈ M ∧ rNB ∈ M.orthogonal ∧
      inner ℂ pNB rNB = 0 ∧ rNB = chi - coneProjection K chi ∧
      wNB ∈ ProperCone.innerDual (K : Set Carrier) ∧
      -rNB ∈ ProperCone.innerDual (K : Set Carrier) ∧
      (∀ s : Carrier, s ∈ M → inner ℂ wNB s = 0 ∧ inner ℝ wNB s = 0) ∧
      inner ℝ wNB chi = -‖rNB‖ ^ 2 ∧ (rNB = 0 ↔ chi ∈ M) ∧
      (chi ∉ M → inner ℝ wNB chi < 0) := by
  have hp : pNB ∈ M := M.starProjection_apply_mem chi
  have hr : rNB ∈ M.orthogonal := M.orthogonal.starProjection_apply_mem chi
  have hpr : inner ℂ pNB rNB = 0 := Submodule.inner_right_of_mem_orthogonal hp hr
  have heq : rNB = chi - coneProjection K chi := (cone_residual_eq chi).symm
  have hx : chi = pNB + rNB := by
    obtain ⟨⟨q, r⟩, ⟨hq, hdual, _, hsum⟩, _⟩ := moreau_decomposition K chi
    have horth : r ∈ M.orthogonal := (mem_polar_iff r).mp hdual
    have hqeq : M.starProjection chi = q :=
      Submodule.eq_starProjection_of_mem_orthogonal' hq horth hsum
    have hreq : rNB = r := by
      rw [rNB, Submodule.starProjection_orthogonal_val, hqeq, hsum]
      simp
    simpa only [pNB, hqeq, hreq] using hsum
  have hd := cone_residual_observer_duality K chi
  have hw : wNB ∈ ProperCone.innerDual (K : Set Carrier) := by
    simpa only [← heq, wNB] using hd.1
  have hsign : inner ℝ wNB chi = -‖rNB‖ ^ 2 := by
    have hrp : inner ℝ rNB pNB = 0 := by
      rw [real_inner_eq, Submodule.inner_left_of_mem_orthogonal hp hr]
      rfl
    simp only [wNB, hx, inner_neg_left, inner_add_right, hrp, neg_zero, zero_add,
      real_inner_self_eq_norm_sq]
  refine ⟨hx, hp, hr, hpr, heq, hw, hw, ?_, hsign, ?_, ?_⟩
  · intro s hs
    have hc : inner ℂ wNB s = 0 := by
      rw [wNB, inner_neg_left, Submodule.inner_left_of_mem_orthogonal hs hr, neg_zero]
    exact ⟨hc, by rw [real_inner_eq, hc]; rfl⟩
  · rw [heq, sub_eq_zero, coneProjection_eq, eq_comm, Submodule.starProjection_eq_self_iff]
  · intro hchi
    have hnot : chi ∉ K := hchi
    simpa only [← heq, wNB] using (hd.2 hnot).2.2

#print axioms coneProjection_eq
#print axioms cone_residual_eq
#print axioms mem_innerDual_iff
#print axioms mem_polar_iff
#print axioms nyman_beurling_cone_residual

end D5.S3.Observer.Hilbert.NymanBeurlingConeResidual
