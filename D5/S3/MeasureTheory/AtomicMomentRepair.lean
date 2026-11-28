/- GID: D5/S3/MeasureTheory/AtomicMomentRepair
   generality: G
   mirror-B: none(waiver:covered-by-atomic-moment-repair-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Small changes in a finite family of signed atoms can be repaired exactly by a fixed basis of admissible moment vectors at arbitrarily small additional cost. -/

import Mathlib.Analysis.Normed.Module.FiniteDimension
import OmegaBuild.Commands

/-!
Omega original.

Small changes in a finite family of signed atoms can be repaired exactly by
a fixed basis of admissible moment vectors at arbitrarily small additional cost. -/

compile_only_with_mathlib

open Set
open scoped BigOperators

namespace Omega.MeasureTheory.AtomicMomentRepair

/-- Replace each old atom by an admissible atom and restore the original
moment using a fixed admissible basis with total correction cost below ε. -/
theorem exists_exact_moment_repair
    {Atom E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype κ]
    (moment : Atom → E) (admissible : Set Atom) (basisNode : κ → admissible)
    (basis : Module.Basis κ ℝ E)
    (hBasis : ∀ j, basis j = moment (basisNode j))
    (oldMoment : ι → E) (weight : ι → ℝ)
    (hApprox : ∀ i, oldMoment i ∈ closure (moment '' admissible))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (node : ι → admissible) (correction : κ → ℝ),
      (∑ i, weight i • moment (node i)) + (∑ j, correction j • moment (basisNode j)) =
        (∑ i, weight i • oldMoment i) ∧ (∑ j, |correction j|) < ε := by
  classical
  let residual (candidate : ι → E) : E :=
    (∑ i, weight i • oldMoment i) - ∑ i, weight i • candidate i
  let cost (candidate : ι → E) : ℝ :=
    ∑ j, |basis.equivFunL (residual candidate) j|
  have hResidual : Continuous residual := by
    dsimp only [residual]
    fun_prop
  have hCost : Continuous cost := by
    dsimp only [cost]
    fun_prop
  have hProduct : oldMoment ∈ closure (Set.univ.pi fun _ : ι => moment '' admissible) :=
    mem_closure_pi.mpr fun i _ => hApprox i
  have hOldCost : cost oldMoment = 0 := by simp [cost, residual]
  obtain ⟨candidate, hCheap, hAdmissible⟩ :=
    mem_closure_iff.mp hProduct {candidate | cost candidate < ε}
      (isOpen_lt hCost continuous_const) (show cost oldMoment < ε by simpa [hOldCost])
  have hNode : ∀ i, ∃ x ∈ admissible, moment x = candidate i :=
    fun i => hAdmissible i (mem_univ i)
  choose x hx hMoment using hNode
  refine ⟨fun i => ⟨x i, hx i⟩, basis.equivFunL (residual candidate), ?_, hCheap⟩
  change (∑ i, weight i • moment (x i)) +
    (∑ j, basis.equivFunL (residual candidate) j • moment (basisNode j)) = _
  simp_rw [hMoment, ← hBasis]
  change (∑ i, weight i • candidate i) +
    (∑ j, basis.repr (residual candidate) j • basis j) = _
  rw [basis.sum_repr]
  exact add_sub_cancel _ _

end Omega.MeasureTheory.AtomicMomentRepair
