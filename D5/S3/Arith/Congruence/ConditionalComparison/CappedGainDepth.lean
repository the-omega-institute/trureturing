/- GID: D5/S3/Arith/Congruence/ConditionalComparison/CappedGainDepth
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Finite depth gains and their positive-mixture representation. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/CappedGainDepth.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.CappedGainLift
import D5.S3.Arith.Congruence.ConditionalComparison.Runs

/-!
# Finite depth gains and their positive-mixture representation

All depth sums are finite. The depth cut-off is arbitrary, not a numerical
assumption about the covering system. It is later chosen above every depth
in the given finite family.
-/

namespace Erdos7.CappedGain

variable {ι : Type*} [DecidableEq ι]

def depthLe (depth : ι → ℕ) (d : ℕ) (S : Finset ι) : Finset ι :=
  S.filter fun x ↦ depth x ≤ d

@[simp] theorem depthLe_empty (depth : ι → ℕ) (d : ℕ) : depthLe depth d ∅ = ∅ := by
  simp [depthLe]

theorem depthLe_mono (depth : ι → ℕ) (d : ℕ) {A B : Finset ι} (h : A ⊆ B) :
    depthLe depth d A ⊆ depthLe depth d B := Finset.filter_subset_filter _ h

theorem depthLe_depth_mono (depth : ι → ℕ) (S : Finset ι) {a b : ℕ} (h : a ≤ b) :
    depthLe depth a S ⊆ depthLe depth b S := by
  intro x hx
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
    (Finset.mem_filter.mp hx).2.trans h⟩

@[simp] theorem depthLe_inter (depth : ι → ℕ) (d : ℕ) (A B : Finset ι) :
    depthLe depth d (A ∩ B) = depthLe depth d A ∩ depthLe depth d B := by
  ext x
  simp [depthLe]
  tauto

@[simp] theorem depthLe_union (depth : ι → ℕ) (d : ℕ) (A B : Finset ι) :
    depthLe depth d (A ∪ B) = depthLe depth d A ∪ depthLe depth d B := by
  ext x
  simp [depthLe]
  tauto

theorem depthLe_eq (depth : ι → ℕ) (d : ℕ) (S : Finset ι)
    (h : ∀ x ∈ S, depth x ≤ d) : depthLe depth d S = S :=
  Finset.filter_eq_self.mpr h

def beta (p : ℚ) (d : ℕ) : ℚ := (p - 1) / p ^ d

theorem beta_nonneg {p : ℚ} (hp : 1 ≤ p) (d : ℕ) : 0 ≤ beta p d := by
  unfold beta
  positivity

theorem beta_antitone {p : ℚ} (hp : 1 ≤ p) : Antitone (beta p) := by
  intro a b hab
  unfold beta
  apply div_le_div_of_nonneg_left (sub_nonneg.mpr hp) (by positivity)
  exact pow_le_pow_right₀ hp hab

theorem beta_one_le {p : ℚ} (hp : 1 ≤ p) : beta p 1 ≤ 1 := by
  have hp0 : 0 < p := by linarith
  simp only [beta, pow_one]
  exact (div_le_one hp0).mpr (by linarith)

def gain (p : ℚ) (D : ℕ) (depth : ι → ℕ) (F : Finset ι → ℚ) (S : Finset ι) : ℚ :=
  ∑ d ∈ Finset.range D, beta p (d + 1) *
    (F (depthLe depth (d + 1) S) - F (depthLe depth d S))

def phi (p r : ℚ) (D : ℕ) (depth : ι → ℕ) (F : Finset ι → ℚ) (S : Finset ι) : ℚ :=
  F (depthLe depth 0 S) + r * gain p D depth F S

def depthRun (p r : ℚ) (D : ℕ) (hp : 1 ≤ p) (hr : 0 ≤ r)
    (hcap : r * beta p 1 ≤ 1) : RunSpec D where
  survival d := if d ≤ D then if d = 0 then 1 else r * beta p d else 0
  survival_zero := by simp
  survival_after := by simp
  antitone_step := by
    intro d hd
    by_cases hd' : d + 1 ≤ D
    · by_cases hd0 : d = 0
      · subst d
        simpa [hd'] using hcap
      · simp only [hd, hd', hd0, Nat.add_eq_zero_iff, Nat.one_ne_zero,
          and_false, if_true, if_false]
        exact mul_le_mul_of_nonneg_left (beta_antitone hp (Nat.le_succ d)) hr
    · simp only [hd, hd', if_true, if_false]
      split_ifs
      · norm_num
      · exact mul_nonneg hr (beta_nonneg hp d)

@[simp] theorem depthRun_survival_pos {p r : ℚ} {D d : ℕ}
    (hp : 1 ≤ p) (hr : 0 ≤ r) (hcap : r * beta p 1 ≤ 1)
    (hd0 : d ≠ 0) (hd : d ≤ D) :
    (depthRun p r D hp hr hcap).survival d = r * beta p d := by
  simp [depthRun, hd, hd0]

/-- Abel summation identifies the increment formula with a probability mixture. -/
theorem phi_eq_expect {p r : ℚ} (D : ℕ) (depth : ι → ℕ) (F : Finset ι → ℚ)
    (hp : 1 ≤ p) (hr : 0 ≤ r) (hcap : r * beta p 1 ≤ 1) (S : Finset ι) :
    phi p r D depth F S =
      (depthRun p r D hp hr hcap).law.expect (fun d ↦ F (depthLe depth d S)) := by
  rw [(depthRun p r D hp hr hcap).expect_eq_abel (fun d ↦ F (depthLe depth d S))]
  unfold phi gain
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [depthRun_survival_pos hp hr hcap (by omega) (by simpa using Finset.mem_range.mp hd)]
  ring

theorem gain_nonneg {p : ℚ} (hp : 1 ≤ p) (D : ℕ) (depth : ι → ℕ)
    {F : Finset ι → ℚ} (hF : Increasing F) (S : Finset ι) :
    0 ≤ gain p D depth F S := by
  apply Finset.sum_nonneg
  intro d _
  apply mul_nonneg (beta_nonneg hp _)
  exact sub_nonneg.mpr (hF (depthLe_depth_mono depth S (Nat.le_succ d)))

theorem depth_increment_increasing (depth : ι → ℕ) (d : ℕ)
    {F : Finset ι → ℚ} (hF : Supermodular F) (hInc : Increasing F) :
    Increasing (fun S ↦ F (depthLe depth (d + 1) S) - F (depthLe depth d S)) := by
  intro A B hAB
  have h := hF (depthLe depth (d + 1) A) (depthLe depth d B)
  have hi : depthLe depth (d + 1) A ∩ depthLe depth d B = depthLe depth d A := by
    ext x
    simp only [depthLe, Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hxA, _⟩, _, hd⟩
      exact ⟨hxA, hd⟩
    · rintro ⟨hxA, hd⟩
      exact ⟨⟨hxA, by omega⟩, hAB hxA, hd⟩
  have hu : depthLe depth (d + 1) A ∪ depthLe depth d B ⊆ depthLe depth (d + 1) B :=
    Finset.union_subset (depthLe_mono depth _ hAB)
      (depthLe_depth_mono depth B (Nat.le_succ d))
  rw [hi] at h
  have hm := hInc hu
  linarith

theorem gain_increasing {p : ℚ} (hp : 1 ≤ p) (D : ℕ) (depth : ι → ℕ)
    {F : Finset ι → ℚ} (hF : Supermodular F) (hInc : Increasing F) :
    Increasing (gain p D depth F) := by
  intro A B hAB
  exact Finset.sum_le_sum fun d _ ↦
    mul_le_mul_of_nonneg_left (depth_increment_increasing depth d hF hInc hAB)
      (beta_nonneg hp _)

theorem phi_increasing {p r : ℚ} (D : ℕ) (depth : ι → ℕ)
    (hp : 1 ≤ p) (hr : 0 ≤ r) (hcap : r * beta p 1 ≤ 1)
    {F : Finset ι → ℚ} (hInc : Increasing F) : Increasing (phi p r D depth F) := by
  intro A B hAB
  simp only [phi_eq_expect D depth F hp hr hcap]
  exact FiniteLaw.expect_mono _ (fun d ↦ hInc (depthLe_mono depth d hAB))

theorem phi_supermodular {p r : ℚ} (D : ℕ) (depth : ι → ℕ)
    (hp : 1 ≤ p) (hr : 0 ≤ r) (hcap : r * beta p 1 ≤ 1)
    {F : Finset ι → ℚ} (hF : Supermodular F) : Supermodular (phi p r D depth F) := by
  intro A B
  simp only [phi_eq_expect D depth F hp hr hcap]
  rw [← FiniteLaw.expect_add, ← FiniteLaw.expect_add]
  apply FiniteLaw.expect_mono
  intro d
  simpa only [depthLe_inter, depthLe_union] using hF (depthLe depth d A) (depthLe depth d B)

@[simp] theorem gain_empty (p : ℚ) (D : ℕ) (depth : ι → ℕ) (F : Finset ι → ℚ) :
    gain p D depth F ∅ = 0 := by simp [gain]

end Erdos7.CappedGain
