/- GID: D5/S1/Digit/Infinite/SixCellPositiveMarginObstruction
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SixCellPositiveMarginObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary connected instruments with at most six cells have no positive uniform margin. -/

import D5.S1.Digit.Infinite.ClosedObservationGraphRealization
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Monotone
import Mathlib.Order.Interval.Set.ProjIcc
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SixCellPositiveMarginObstruction

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open scoped Topology

/-- An actual cell includes only scalars in the source support. -/
def cell {q : ℕ} (Q : ℝ → Fin q) (i : Fin q) : Set ℝ :=
  {x | x ∈ stateInterval false ∧ Q x = i}

/-- Every fibre is a nonempty connected interval; the cell numbering is arbitrary. -/
def connectedInstrument {q : ℕ} (Q : ℝ → Fin q) : Prop :=
  ∀ i, IsConnected (cell Q i)

/-- Closed cell rectangles distinguish all legal labelled branch points. -/
def closedGridPure {q : ℕ} (Q : ℝ → Fin q) : Prop :=
  ∀ (i j : Fin q) (l m : Label) (y z : ℝ),
    y ∈ stateInterval (outgoing l) → z ∈ stateInterval (outgoing m) →
    y ∈ closure (cell Q j) → z ∈ closure (cell Q j) →
    branch l y ∈ closure (cell Q i) → branch m z ∈ closure (cell Q i) → l = m

private lemma parameters : (8 / 13 : ℝ) < t ∧ t < 5 / 8 ∧
    t ^ 2 = 1 - t ∧ g = 2 * t - 1 ∧ t ^ 4 = 2 - 3 * t := by
  have hp : 0 < t := inv_pos.mpr Real.goldenRatio_pos
  have hs : t ^ 2 + t = 1 := by
    change (Real.goldenRatio⁻¹) ^ 2 + Real.goldenRatio⁻¹ = 1
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  have h3 : t ^ 3 = 2 * t - 1 := by
    nlinarith [congrArg (fun x : ℝ => t * x) hs]
  refine ⟨?_, ?_, by linarith, h3, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith [congrArg (fun x : ℝ => t ^ 2 * x) hs]

private lemma realize (l : Label) {y : ℝ} (hy : y ∈ stateInterval (outgoing l)) :
    ∃ x : LegalDigits, window x 0 = l ∧ kappa x = branch l y ∧
      kappa (originalT x) = y := by
  obtain ⟨_, hrange, hrec, hprepend, _⟩ :=
    D5.S1.Digit.Infinite.ClosedObservationGraphRealization.closed_observation_graph_realization
  rw [← hrange] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  obtain ⟨x, hx, _⟩ := hprepend false l (outgoing l) z ⟨by simp, rfl⟩ hz
  refine ⟨x, hx.2.1, ?_, ?_⟩
  · rw [(hrec x).1, hx.2.1, hx.2.2, hzy]
  · rw [hx.2.2, hzy]

private lemma branch_support (l : Label) {y : ℝ}
    (hy : y ∈ stateInterval (outgoing l)) : branch l y ∈ stateInterval false := by
  obtain ⟨x, _, hx, _⟩ := realize l hy
  rw [← hx]
  rw [← D5.S1.Digit.Infinite.ClosedObservationGraphRealization.closed_observation_graph_realization.2.1]
  exact ⟨x, by simp [stateAddress], rfl⟩

private lemma purity_of_correct {q : ℕ} (Q : ℝ → Fin q)
    (d : Fin q × Fin q → Label) {η : ℝ} (hη : 0 < η)
    (hcorrect : ∀ x : LegalDigits, ∀ e₀ e₁ : ℝ, |e₀| < η → |e₁| < η →
      d (Q (Set.projIcc (-1) (1 + t) (by linarith [parameters.1]) (kappa x + e₀)),
         Q (Set.projIcc (-1) (1 + t) (by linarith [parameters.1])
           (kappa (originalT x) + e₁))) = window x 0) : closedGridPure Q := by
  intro i j l m y z hyl hzm hy hz hly hmz
  have decode (a : Label) (b : ℝ) (hb : b ∈ stateInterval (outgoing a))
      (hbj : b ∈ closure (cell Q j)) (hbi : branch a b ∈ closure (cell Q i)) :
      d (i, j) = a := by
    obtain ⟨x, hxl, hx, hxt⟩ := realize a hb
    obtain ⟨u, hu, heu⟩ := Real.mem_closure_iff.mp hbi η hη
    obtain ⟨v, hv, hev⟩ := Real.mem_closure_iff.mp hbj η hη
    have hc := hcorrect x (u - kappa x) (v - kappa (originalT x))
      (by simpa [hx] using heu) (by simpa [hxt] using hev)
    rw [add_sub_cancel, add_sub_cancel] at hc
    simp only [Set.projIcc_of_mem (show u ∈ Set.Icc (-1) (1 + t) from hu.1),
      Set.projIcc_of_mem (show v ∈ Set.Icc (-1) (1 + t) from hv.1)] at hc
    simpa only [hu.2, hv.2, hxl] using hc
  exact (decode l y hyl hy hly).symm.trans (decode m z hzm hz hmz)

private lemma ordered_relabel {q : ℕ} (Q : ℝ → Fin q) (hQ : connectedInstrument Q) :
    ∃ e : Fin q ≃ Fin q, MonotoneOn (fun x => e (Q x)) (stateInterval false) := by
  classical
  choose r hr using fun i => (hQ i).nonempty
  have hrinj : Function.Injective r := by
    intro i j h
    exact (hr i).2.symm.trans (h ▸ (hr j).2)
  let s := Finset.univ.image r
  have hcard : s.card = q := by
    rw [Finset.card_image_of_injective _ hrinj, Finset.card_fin]
  let a := s.orderEmbOfFin hcard
  have ha (i : Fin q) : a i ∈ s := s.orderEmbOfFin_mem hcard i
  have har (i : Fin q) : r (Q (a i)) = a i := by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (ha i)
    rw [← hj, (hr j).2]
  have hf : Function.Injective (fun i => Q (a i)) := by
    intro i j hij
    apply a.injective
    rw [← har i, ← har j, hij]
  let f : Fin q ≃ Fin q := Equiv.ofBijective (fun i => Q (a i))
    ⟨hf, (Fintype.injective_iff_surjective.mp hf)⟩
  have haX (i : Fin q) : a i ∈ stateInterval false := by
    rw [← har i]; exact (hr _).1
  refine ⟨f.symm, ?_⟩
  intro x hx y hy hxy
  by_contra h
  have hij : f.symm (Q y) < f.symm (Q x) := lt_of_not_ge h
  have hab := a.strictMono hij
  have hax : Q (a (f.symm (Q x))) = Q x := f.apply_symm_apply (Q x)
  have hay : Q (a (f.symm (Q y))) = Q y := f.apply_symm_apply (Q y)
  have hne : Q x ≠ Q y := by intro he; simp [he] at hij
  by_cases hle : a (f.symm (Q y)) ≤ x
  · have hc := (hQ (Q y)).Icc_subset ⟨haX _, hay⟩ ⟨hy, rfl⟩ ⟨hle, hxy⟩
    exact hne hc.2
  · have hc := (hQ (Q x)).Icc_subset ⟨hx, rfl⟩ ⟨haX _, hax⟩
      ⟨(lt_of_not_ge hle).le, hab.le⟩
    exact hne (hay.symm.trans hc.2).symm

end D5.S1.Digit.Infinite.SixCellPositiveMarginObstruction
