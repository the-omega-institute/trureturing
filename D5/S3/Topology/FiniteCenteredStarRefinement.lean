/- GID: D5/S3/Topology/FiniteCenteredStarRefinement
   generality: G
   mirror-B: D5/B/S3/Topology/FiniteCenteredStarRefinement
   mirror-E: none(waiver:abstract-topological-construction)
   anchors: [mathlib/module/Mathlib.Topology.PartitionOfUnity]
   utility: none
   digest: Finite continuous coordinates construct centered open star refinements on compact Hausdorff spaces. -/

import Mathlib.Topology.PartitionOfUnity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Centered finite refinements from partitions of unity on compact Hausdorff spaces. -/

set_option autoImplicit false

open Set Topology
open scoped BigOperators

noncomputable section

namespace D5.S3.Topology.FiniteCenteredStarRefinement

/-- A finite open cover of a compact Hausdorff space has a finite centered open
star refinement. Every intersecting refinement member is contained in the same
original member, including its chosen center. -/
theorem exists_finite_centered_star_refinement
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {n : ℕ} (V : Fin n → Set X) (hVo : ∀ j, IsOpen (V j))
    (hVc : ∀ x, ∃ j, x ∈ V j) :
    ∃ (U : X → Set X) (s : Finset X),
      (∀ c, IsOpen (U c)) ∧ (∀ c, c ∈ U c) ∧
      (∀ x, ∃ c ∈ s, x ∈ U c) ∧
      ∀ c ∈ s, ∃ j, ∀ d ∈ s, (U c ∩ U d).Nonempty → U d ⊆ V j := by
  classical
  obtain ⟨f, hfsub, hfsum, hfnonneg, hfcp⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact hVo isCompact_univ
      (by simpa only [subset_def, mem_univ, true_implies, mem_iUnion] using hVc)
  let δ : ℝ := 1 / (4 * ((n : ℝ) + 1))
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let U : X → Set X := fun c => {x | ∀ j, |f j x - f j c| < δ}
  have hUo : ∀ c, IsOpen (U c) := by
    intro c
    change IsOpen {x | ∀ j : Fin n, |f j x - f j c| < δ}
    simp only [setOf_forall]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt (((f j).continuous.sub continuous_const).abs) continuous_const
  have hUc : ∀ c, c ∈ U c := by
    intro c j
    simpa only [sub_self, abs_zero] using hδ
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUo
    (by intro x _; exact mem_iUnion.mpr ⟨x, hUc x⟩)
  refine ⟨U, s, hUo, hUc, ?_, ?_⟩
  · intro x
    obtain ⟨c, hc⟩ := mem_iUnion.mp (hs (mem_univ x))
    obtain ⟨hc, hx⟩ := mem_iUnion.mp hc
    exact ⟨c, hc, hx⟩
  · intro c hc
    have hsum : ∑ j, f j c = 1 := by
      simpa only [Finset.sum_apply, Pi.one_apply] using hfsum (mem_univ c)
    have hlarge : ∃ j, 3 * δ < f j c := by
      by_contra! h
      have hle := Finset.sum_le_sum (s := Finset.univ) (fun j _ => h j)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hsum] at hle
      dsimp [δ] at hle
      have : (n : ℝ) * (3 * (1 / (4 * ((n : ℝ) + 1)))) < 1 := by
        calc
          (n : ℝ) * (3 * (1 / (4 * ((n : ℝ) + 1)))) =
              (3 * (n : ℝ)) / (4 * ((n : ℝ) + 1)) := by ring
          _ < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      linarith
    obtain ⟨j, hj⟩ := hlarge
    refine ⟨j, ?_⟩
    intro d hd ⟨w, hwc, hwd⟩ x hx
    have hxc := hx j
    have hwcj := hwc j
    have hwdj := hwd j
    have hpos : 0 < f j x := by
      have h₁ := (abs_lt.mp hxc).1
      have h₂ := (abs_lt.mp hwcj).1
      have h₃ := (abs_lt.mp hwdj).2
      linarith
    exact hfsub j (subset_closure (by exact hpos.ne' : x ∈ Function.support (f j)))

end D5.S3.Topology.FiniteCenteredStarRefinement
