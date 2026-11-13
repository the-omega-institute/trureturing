/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Geometry/RealAlgebraic/Semialgebraic/Topology
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Geometry/RealAlgebraic/Semialgebraic/Topology
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Selected finite connected partition and closure source for boundary recovery. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Source: TauCetiProject/TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9.
Selection: Semialgebraic/Topology.isSemialgebraic_setOf_dist_eval_lt and IsSemialgebraic.closure.
Adaptation: D5 import routes and selection of consumed declarations; mathematical telescopes
and proof bodies are retained. License: docs/reports/licenses/TauCeti-LICENSE.txt.
Retire each adaptation when the actual pinned mathlib supplies an equivalent declaration,
replacing its consumers by direct applications of that pinned owner.
No independent mathematical novelty or escape credit is claimed.
-/
module

public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Geometry.RealAlgebraic.CAD.Existence
public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image
public import Mathlib.Topology.MetricSpace.Pi

public section
open Function MvPolynomial Set
namespace TauCeti
variable {σ τ : Type*}

/-- The locus where the sup distance between two polynomial maps is less than the value of a
polynomial is semialgebraic. -/
theorem isSemialgebraic_setOf_dist_eval_lt [Fintype σ] (p q : σ → MvPolynomial τ ℝ)
    (r : MvPolynomial τ ℝ) :
    IsSemialgebraic
      {z : τ → ℝ | dist (fun i => eval z (p i)) (fun i => eval z (q i)) < eval z r} := by
  convert (isSemialgebraic_eval_pos r).inter (IsSemialgebraic.iInter fun i =>
    (isSemialgebraic_eval_lt (-r) (p i - q i)).inter
      (isSemialgebraic_eval_lt (p i - q i) r)) using 1
  ext z
  simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, map_neg, map_sub]
  refine ⟨fun h => ?_, fun ⟨hr, h⟩ => ?_⟩
  · have hr : 0 < eval z r := dist_nonneg.trans_lt h
    exact ⟨hr, fun i => abs_lt.1 (by simpa [Real.dist_eq] using (dist_pi_lt_iff hr).1 h i)⟩
  · exact (dist_pi_lt_iff hr).2 fun i => by simpa [Real.dist_eq] using abs_lt.2 (h i)

/-- The closure of a semialgebraic subset of `σ → ℝ` is semialgebraic. -/
theorem IsSemialgebraic.closure [Finite σ] {s : Set (σ → ℝ)} (hs : IsSemialgebraic s) :
    IsSemialgebraic (closure s) := by
  cases nonempty_fintype σ
  -- In the coordinates `(σ ⊕ Unit) ⊕ σ`, a point `z` encodes a centre `x = z ∘ inl ∘ inl`, a
  -- radius `ε = z (inl (inr ()))` and a point `y = z ∘ inr`; `T` says `y ∈ s` and `dist x y < ε`.
  let T : Set ((σ ⊕ Unit) ⊕ σ → ℝ) := (fun z => z ∘ Sum.inr) ⁻¹' s ∩
    {z | dist (fun i => eval z (X (.inl (.inl i)))) (fun i => eval z (X (.inr i))) <
      eval z (X (.inl (.inr ())))}
  have hT : IsSemialgebraic T :=
    (hs.preimage_comp _).inter (isSemialgebraic_setOf_dist_eval_lt _ _ _)
  -- Projecting away `y`, then the radius among the `ε > 0` for which no such `y` exists, gives
  -- the complement of the closure.
  let A : Set (σ ⊕ Unit → ℝ) := (fun z => z ∘ Sum.inl) '' T
  have hB : IsSemialgebraic ((fun w : σ ⊕ Unit → ℝ => w ∘ Sum.inl) ''
      ({w | 0 < eval w (X (.inr ()))} ∩ Aᶜ)) :=
    ((isSemialgebraic_eval_pos _).inter hT.image_comp_inl.compl).image_comp_inl
  convert hB.compl using 1
  ext x
  have hA (ε : ℝ) : Sum.elim x (fun _ => ε) ∈ A ↔ ∃ y ∈ s, dist x y < ε := by
    constructor
    · rintro ⟨z, ⟨hzs, hzd⟩, hz⟩
      refine ⟨z ∘ Sum.inr, hzs, ?_⟩
      have hx : (fun i => z (.inl (.inl i))) = x := funext fun i => congrFun hz (.inl i)
      have hε : z (.inl (.inr ())) = ε := congrFun hz (.inr ())
      simpa [hx, hε, Function.comp_def] using hzd
    · rintro ⟨y, hys, hy⟩
      exact ⟨Sum.elim (Sum.elim x fun _ => ε) y, ⟨hys, by simpa using hy⟩, rfl⟩
  simp only [Metric.mem_closure_iff, mem_compl_iff, mem_image, mem_inter_iff, mem_ofPred_eq,
    eval_X, not_exists, not_and]
  refine ⟨fun h w ⟨hw, hwA⟩ hwx => hwA ?_, fun h ε hε => ?_⟩
  · have hw' : w = Sum.elim x fun _ => w (.inr ()) := by
      ext (i | ⟨⟩)
      · exact congrFun hwx i
      · rfl
    rw [hw', hA]
    exact h _ hw
  · by_contra hne
    exact h (Sum.elim x fun _ => ε) ⟨hε, fun hA' => hne ((hA ε).1 hA')⟩ rfl


end TauCeti
