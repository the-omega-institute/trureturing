/- GID: D5/S3/Arith/Congruence/ConditionalComparison/CappedGainRearrangement
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Depth rearrangement for arbitrary finite sets of individual labels. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/CappedGainRearrangement.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.CappedGainDepth
import D5.S3.Arith.Congruence.ConditionalComparison.RankedRearrangement
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Depth rearrangement for arbitrary finite sets of individual labels

The enumeration is a bijection, sorted by depth. It does not identify labels
sharing a depth, residue, or earlier projection. The law may have arbitrary
dependence between its label events.
-/

namespace Erdos7.CappedGain

variable {ι : Type*} [DecidableEq ι]

def pullLabels {n : ℕ} (e : Fin n → ι) (A : Finset ℕ) : Finset ι :=
  (Finset.univ.filter fun i : Fin n ↦ (i : ℕ) ∈ A).image e

@[simp] theorem pullLabels_empty {n : ℕ} (e : Fin n → ι) : pullLabels e ∅ = ∅ := by
  simp [pullLabels]

theorem pullLabels_mono {n : ℕ} (e : Fin n → ι) {A B : Finset ℕ} (h : A ⊆ B) :
    pullLabels e A ⊆ pullLabels e B := by
  apply Finset.image_subset_image
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h (Finset.mem_filter.mp hi).2⟩

theorem pullLabels_inter {n : ℕ} (e : Fin n → ι) (he : Function.Injective e)
    (A B : Finset ℕ) : pullLabels e (A ∩ B) = pullLabels e A ∩ pullLabels e B := by
  unfold pullLabels
  rw [← Finset.image_inter _ _ he]
  congr 1
  ext i
  simp

theorem pullLabels_union {n : ℕ} (e : Fin n → ι) (A B : Finset ℕ) :
    pullLabels e (A ∪ B) = pullLabels e A ∪ pullLabels e B := by
  unfold pullLabels
  rw [← Finset.image_union]
  congr 1
  ext i
  simp

theorem pullLabels_image_val {n : ℕ} (e : Fin n → ι) (A : Finset (Fin n)) :
    pullLabels e (A.image Fin.val) = A.image e := by
  unfold pullLabels
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hji⟩
    have heq : j = i := Fin.ext hji
    simpa [heq] using hj
  · intro hi
    exact ⟨i, hi, rfl⟩

theorem pullLabels_rankSet {n : ℕ} (e : Fin n → ι) (depth : ι → ℕ) (d : ℕ) :
    pullLabels e (rankSet (fun i ↦ depth (e i)) d) =
      depthLe depth d (Finset.univ.image e) := by
  have he : pullLabels e (rankSet (fun i ↦ depth (e i)) d) =
      (Finset.univ.filter fun i ↦ depth (e i) ≤ d).image e := by
    unfold pullLabels
    congr 1
    ext i
    simp [rankSet, rankNat, i.isLt]
  rw [he]
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, depthLe]
  constructor
  · rintro ⟨i, hd, rfl⟩
    exact ⟨⟨i, rfl⟩, hd⟩
  · rintro ⟨⟨i, rfl⟩, hd⟩
    exact ⟨i, hd, rfl⟩

/-- Rearrangement against an arbitrary finite run law, on an arbitrary
finite ambient set. Every individual label is retained in the proof. -/
theorem finite_run_rearrangement {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (S : Finset ι) (active : Ω → Finset ι)
    (hactive : ∀ ω, active ω ⊆ S) (depth : ι → ℕ)
    {D : ℕ} (R : RunSpec D) (hdepth : ∀ x ∈ S, depth x ≤ D)
    {F : Finset ι → ℚ} (hF : Supermodular F) (hInc : Increasing F)
    (hmarg : ∀ x ∈ S, μ.prob (fun ω ↦ x ∈ active ω) ≤ R.survival (depth x)) :
    μ.expect (fun ω ↦ F (active ω)) ≤
      R.law.expect (fun d ↦ F (depthLe depth d S)) := by
  classical
  let n := Fintype.card ↥S
  let e₀ : Fin n ≃ ↥S := (Fintype.equivFin ↥S).symm
  let rank₀ : Fin n → ℕ := fun i ↦ depth (e₀ i).1
  let eS : Fin n ≃ ↥S := (Tuple.sort rank₀).trans e₀
  let e : Fin n → ι := fun i ↦ (eS i).1
  have he : Function.Injective e := Subtype.val_injective.comp eS.injective
  have himage : Finset.univ.image e = S := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (eS i).2
    · intro hx
      exact ⟨eS.symm ⟨x, hx⟩, by simp [e]⟩
  let rank : Fin n → ℕ := fun i ↦ depth (e i)
  have hsorted : RankSorted rank := by
    intro i j hij
    exact Tuple.monotone_sort rank₀ hij
  have hrank : ∀ i, rank i ≤ D := fun i ↦ hdepth (e i) (eS i).2
  let F' : Finset ℕ → ℚ := fun A ↦ F (pullLabels e A)
  have hF' : Supermodular F' := by
    intro A B
    simpa only [F', pullLabels_inter e he, pullLabels_union] using
      hF (pullLabels e A) (pullLabels e B)
  have hInc' : Increasing F' := fun _ _ h ↦ hInc (pullLabels_mono e h)
  let active' : Ω → Finset ℕ := fun ω ↦
    (Finset.univ.filter fun i : Fin n ↦ e i ∈ active ω).image Fin.val
  have hactive' : ∀ ω, active' ω ⊆ Finset.range n := by
    intro ω i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr j.isLt
  have hpull : ∀ ω, pullLabels e (active' ω) = active ω := by
    intro ω
    change pullLabels e ((Finset.univ.filter fun i : Fin n ↦ e i ∈ active ω).image Fin.val) = _
    rw [pullLabels_image_val]
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hx
      have hxS := hactive ω hx
      rw [← himage] at hxS
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxS
      exact ⟨i, hx, rfl⟩
  have hmarg' : ∀ i < n,
      μ.prob (fun ω ↦ i ∈ active' ω) ≤ R.survival (rankNat rank i) := by
    intro i hi
    let j : Fin n := ⟨i, hi⟩
    have hprob : μ.prob (fun ω ↦ i ∈ active' ω) = μ.prob (fun ω ↦ e j ∈ active ω) := by
      apply μ.prob_congr
      intro ω
      simp only [active', Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨k, hk, hkval⟩
        have hkj : k = j := Fin.ext hkval
        simpa [hkj] using hk
      · intro hj
        exact ⟨j, hj, rfl⟩
    rw [hprob]
    simpa [rankNat, rank, hi, j] using hmarg (e j) (eS j).2
  have h := bernoulli_rearrangement μ hF' hInc' n active' hactive'
    (fun i ↦ R.survival (rankNat rank i)) hmarg'
  rw [← run_expect_rankSet_eq R rank hsorted hrank F'] at h
  have hleft : μ.expect (fun ω ↦ F' (active' ω)) = μ.expect (fun ω ↦ F (active ω)) := by
    apply μ.expect_congr
    intro ω
    simp only [F', hpull]
  have hright : R.law.expect (fun d ↦ F' (rankSet rank d)) =
      R.law.expect (fun d ↦ F (depthLe depth d S)) := by
    apply R.law.expect_congr
    intro d
    simp only [F', rank, pullLabels_rankSet, himage]
  rwa [hleft, hright] at h

theorem depth_rearrangement {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (S : Finset ι) (active : Ω → Finset ι)
    (hactive : ∀ ω, active ω ⊆ S) (depth : ι → ℕ) {D : ℕ}
    (hdepth : ∀ x ∈ S, depth x ≤ D) {p r : ℚ}
    (hp : 1 ≤ p) (hr : 0 ≤ r) (hcap : r * beta p 1 ≤ 1)
    {F : Finset ι → ℚ} (hF : Supermodular F) (hInc : Increasing F)
    (hmarg : ∀ x ∈ S, depth x ≠ 0 →
      μ.prob (fun ω ↦ x ∈ active ω) ≤ r * beta p (depth x)) :
    μ.expect (fun ω ↦ F (active ω)) ≤ phi p r D depth F S := by
  rw [phi_eq_expect D depth F hp hr hcap]
  apply finite_run_rearrangement μ S active hactive depth _ hdepth hF hInc
  intro x hx
  by_cases hd : depth x = 0
  · simpa only [hd, RunSpec.survival_zero] using μ.prob_le_one (fun ω ↦ x ∈ active ω)
  · rw [depthRun_survival_pos hp hr hcap hd (hdepth x hx)]
    exact hmarg x hx hd

end Erdos7.CappedGain
