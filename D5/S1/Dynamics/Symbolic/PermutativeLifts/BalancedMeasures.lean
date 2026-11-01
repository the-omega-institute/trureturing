/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual balanced subshift phases control invariant probability measures. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedSubshift
import D5.S1.Dynamics.Symbolic.PermutativeLifts.SparseDisagreement
import Mathlib.Dynamics.Ergodic.EmpiricalMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Topology.Instances.ZMod

/-! Invariant measures on the actual recognizable balanced-word subshift.
The phase is the physical offset of its unique marked decoder.
The new public theorem escape audits are unfinished under issue #24726. -/

set_option autoImplicit false

open Set MeasureTheory SymbolicDynamics.FullShift
open scoped BigOperators

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.Balanced

noncomputable section

local instance (n : ℕ) : NeZero (height n) := ⟨Nat.ne_of_gt (height_pos n)⟩

/-- The actual decoder's physical phase in the finite cyclic height group. -/
def phase (n : ℕ) (y : BalancedPoint) : ZMod (height n) :=
  ((decode n y).1 0).2.val

theorem continuous_phase (n : ℕ) : Continuous (phase n) := by
  exact (continuous_of_discreteTopology : Continuous
    (fun s : TileState (balancedWord n) => (s.2.val : ZMod (height n)))).comp
      ((continuous_apply 0).comp (continuous_subtype_val.comp (continuous_decode n)))

theorem phase_shift (n : ℕ) (g : ℤ) (y : BalancedPoint) :
    phase n (shiftBalanced g y) = (g : ZMod (height n)) + phase n y := by
  have hd := congrArg
    (fun x : MarkedTiling (balancedWord n) => ((x.1 0).2.val : ZMod (height n)))
    (decode_shift n g y)
  have ht : phase n (shiftBalanced g y) =
      (((decode n y).1 (g + 0)).2.val : ZMod (height n)) := by
    exact hd
  have hg := congrArg
    (fun i : ℤ => (((decode n y).1 i).2.val : ZMod (height n))) (add_zero g)
  exact ht.trans (hg.trans (SparseDisagreement.offset_cast (balancedWord n) (height n)
    (balancedWord_length n) (decode n y) g))

theorem continuous_shiftBalanced (g : ℤ) : Continuous (shiftBalanced g) := by
  exact ((continuous_shift g).comp continuous_subtype_val).subtype_mk _

/-- Krylov--Bogolyubov applies to the actual nonempty compact balanced subshift. -/
theorem exists_balanced_invariant_probability :
    ∃ μ : Measure BalancedPoint,
      MeasurePreserving (shiftBalanced 1) μ μ ∧ IsProbabilityMeasure μ := by
  obtain ⟨μ, hμ, _, hp⟩ :=
    exists_measurePreserving_probabilityMeasure (continuous_shiftBalanced 1)
  exact ⟨μ, hμ, hp⟩

private theorem measurableSet_phase_fiber (n : ℕ) (j : ZMod (height n)) :
    MeasurableSet (phase n ⁻¹' {j}) :=
  (isClosed_singleton.preimage (continuous_phase n)).measurableSet

/-- Every invariant probability has the uniform distribution on each actual
finite cyclic phase factor. -/
theorem phase_fiber_measure (μ : Measure BalancedPoint) [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shiftBalanced 1) μ μ)
    (n : ℕ) (j : ZMod (height n)) :
    μ.real (phase n ⁻¹' {j}) = 1 / (height n : ℝ) := by
  have hstep (a : ZMod (height n)) :
      μ.real (phase n ⁻¹' {a + 1}) = μ.real (phase n ⁻¹' {a}) := by
    have hp : shiftBalanced 1 ⁻¹' (phase n ⁻¹' {a + 1}) = phase n ⁻¹' {a} := by
      ext y
      simp only [mem_preimage, mem_singleton_iff, phase_shift, Int.cast_one]
      constructor
      · intro h
        exact add_left_cancel (h.trans (add_comm a 1))
      · intro h
        rw [h, add_comm]
    have h := hμ.measureReal_preimage (measurableSet_phase_fiber n (a + 1)).nullMeasurableSet
    rw [hp] at h
    exact h.symm
  have hnat (k : ℕ) : μ.real (phase n ⁻¹' {(k : ZMod (height n))}) =
      μ.real (phase n ⁻¹' {0}) := by
    induction k with
    | zero => simp only [Nat.cast_zero]
    | succ k ih => simpa only [Nat.cast_add, Nat.cast_one] using (hstep k).trans ih
  have hall (a : ZMod (height n)) : μ.real (phase n ⁻¹' {a}) =
      μ.real (phase n ⁻¹' {0}) := by
    simpa only [ZMod.natCast_zmod_val] using hnat a.val
  have hsum := sum_measureReal_preimage_singleton (μ := μ) (f := phase n) Finset.univ
    (fun a _ => measurableSet_phase_fiber n a)
  have hnorm : (height n : ℝ) * μ.real (phase n ⁻¹' {0}) = 1 := by
    simpa only [hall, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
      Finset.coe_univ, preimage_univ, probReal_univ] using hsum
  rw [hall]
  apply (eq_div_iff (by exact_mod_cast (Nat.ne_of_gt (height_pos n)))).2
  nlinarith

/-- A finite collection of phases has its exact normalized counting mass. -/
theorem phase_finset_measure (μ : Measure BalancedPoint) [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shiftBalanced 1) μ μ)
    (n : ℕ) (S : Finset (ZMod (height n))) :
    μ.real (phase n ⁻¹' (S : Set (ZMod (height n)))) = S.card / (height n : ℝ) := by
  rw [← sum_measureReal_preimage_singleton S (fun a _ => measurableSet_phase_fiber n a)]
  simp [phase_fiber_measure μ hμ n, div_eq_mul_inv]

/-- Membership depends only on a specified finite signed window. -/
def WindowDetermined (t : ℤ) (r : ℕ) (C : Set BalancedPoint) : Prop :=
  ∀ x y : BalancedPoint,
    (∀ k : ℕ, k < r → x.1 (t + (k : ℤ)) = y.1 (t + (k : ℤ))) → (x ∈ C ↔ y ∈ C)

/-- Phases whose complete fibre lies inside the event. No fibre representative is chosen. -/
def goodPhases (n : ℕ) (C : Set BalancedPoint) : Finset (ZMod (height n)) :=
  @Finset.filter _ (fun j => ∀ y : BalancedPoint, phase n y = j → y ∈ C)
    (Classical.decPred _) Finset.univ

private theorem phase_nat_eq (n : ℕ) (x y : BalancedPoint)
    (h : phase n x = phase n y) :
    ((decode n x).1 0).2.val = ((decode n y).1 0).2.val := by
  have hx : ((decode n x).1 0).2.val < height n := by
    simpa only [balancedWord_length] using ((decode n x).1 0).2.isLt
  have hy : ((decode n y).1 0).2.val < height n := by
    simpa only [balancedWord_length] using ((decode n y).1 0).2.isLt
  have hv := congrArg ZMod.val h
  simpa only [phase, ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] using hv

private theorem phase_event_sandwich (n : ℕ) (t : ℤ) (r : ℕ) (C : Set BalancedPoint)
    (hC : WindowDetermined t r C) :
    (phase n ⁻¹' (goodPhases n C : Set (ZMod (height n)))) ⊆ C ∧
    C ⊆ (phase n ⁻¹' (goodPhases n C : Set (ZMod (height n)))) ∪
      (phase n ⁻¹' (SparseDisagreement.badPhases
        (SparseDisagreement.wordDisagreements (balancedWord n) (height n)
          (balancedWord_length n)) t r : Set (ZMod (height n)))) := by
  classical
  constructor
  · intro y hy
    exact (Finset.mem_filter.mp hy).2 y rfl
  · intro y hy
    by_cases hb : phase n y ∈ SparseDisagreement.badPhases
      (SparseDisagreement.wordDisagreements (balancedWord n) (height n)
        (balancedWord_length n)) t r
    · exact Or.inr hb
    · apply Or.inl
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro z hz
      have hw := SparseDisagreement.same_phase_window (balancedWord n) (height n)
        (balancedWord_length n) (decode n y) (decode n z) (phase_nat_eq n y z hz.symm)
        t r hb
      have hread : ∀ k : ℕ, k < r → y.1 (t + (k : ℤ)) = z.1 (t + (k : ℤ)) := by
        intro k hk
        simpa only [read_decode] using hw k hk
      exact (hC y z hread).mp hy

/-- The mass of every finite-window event lies in one common phase-counting
interval whose width is the exceptional-phase fraction. -/
theorem window_event_measure_squeeze (μ : Measure BalancedPoint) [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shiftBalanced 1) μ μ)
    (n : ℕ) (t : ℤ) (r : ℕ) (C : Set BalancedPoint) (hC : WindowDetermined t r C) :
    (goodPhases n C).card / (height n : ℝ) ≤ μ.real C ∧
      μ.real C ≤ (goodPhases n C).card / (height n : ℝ) +
        (SparseDisagreement.badPhases
          (SparseDisagreement.wordDisagreements (balancedWord n) (height n)
            (balancedWord_length n)) t r).card / (height n : ℝ) := by
  obtain ⟨hl, hu⟩ := phase_event_sandwich n t r C hC
  constructor
  · rw [← phase_finset_measure μ hμ n]
    exact measureReal_mono hl
  · calc
      μ.real C ≤ μ.real _ := measureReal_mono hu
      _ ≤ μ.real _ + μ.real _ := measureReal_union_le _ _
      _ = _ := by rw [phase_finset_measure μ hμ n, phase_finset_measure μ hμ n]

end

end D5.S1.Dynamics.Symbolic.PermutativeLifts.Balanced
