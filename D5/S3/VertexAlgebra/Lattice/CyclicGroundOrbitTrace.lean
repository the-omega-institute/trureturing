/- GID: D5/S3/VertexAlgebra/Lattice/CyclicGroundOrbitTrace
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/CyclicGroundOrbitTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual cyclic ground-orbit power traces with retained cocycle phase. -/

import D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitFixedSpace
import Mathlib.LinearAlgebra.Trace

/-!
The finite span here is the literal span of the distinct zero-oscillator
ground states on one first-return charge orbit.  Its trace is computed in the
actual orbit basis.  The power action keeps the cocycle phase supplied by the
corrected lattice lift; the non-returning branch vanishes because a nontrivial
cyclic shift has no diagonal entries.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitTrace

open CyclicGroundOrbitBasis CyclicGroundOrbitFixedSpace CyclicIsometryLift
open RootlessLowGrades LatticePositiveEnergy
open LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open scoped BigOperators

private def cycleIndex (d n : ℕ) (i : Fin d) : Fin d :=
  ⟨(n + i.1) % d, Nat.mod_lt _ (by
    have hne : d ≠ 0 := by
      intro h
      exact Fin.elim0 (h ▸ i)
    exact Nat.pos_of_ne_zero hne)⟩

private theorem cycle_period_pos
    (D : LatticeData) (g : Charge D ≃+ Charge D) (a : NormFour D)
    (m : ℕ) (hm : 0 < m) (hperiod : Function.IsPeriodicPt g m a.1) :
    0 < Function.minimalPeriod g a.1 := by
  exact Function.IsPeriodicPt.minimalPeriod_pos (f := g) (n := m) (x := a.1) hm hperiod

private theorem cycle_linearIndependent
    (D : LatticeData) (g : Charge D ≃+ Charge D) (a : NormFour D)
    (m : ℕ) (hm : 0 < m) (hperiod : Function.IsPeriodicPt g m a.1) :
    LinearIndependent ℂ
      (fun i : Fin (Function.minimalPeriod g a.1) =>
        Finsupp.single (g^[i.1] a.1) (1 : Oscillator D)) := by
  let d := Function.minimalPeriod g a.1
  have hd : 0 < d := cycle_period_pos (D := D) (g := g) (a := a) (m := m) hm hperiod
  have hinj : Function.Injective
      (fun i : Fin d =>
        ((g^[i.1] a.1, (0 : LatticePositiveEnergy.Exponent D)) :
          LatticePositiveEnergy.Label D)) := by
    intro i j hij
    apply Fin.ext
    apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod i.2 j.2).mp
    exact congrArg Prod.fst hij
  have hb : (fun i : Fin d =>
      Finsupp.single (g^[i.1] a.1) (1 : Oscillator D)) =
      (fun i : Fin d => carrierBasis D
        ((g^[i.1] a.1, (0 : LatticePositiveEnergy.Exponent D)) :
          LatticePositiveEnergy.Label D)) := by
    funext i
    simp [carrierBasis_apply]
  rw [hb]
  exact (carrierBasis D).linearIndependent.comp _ hinj

private def cycleBasis
    (D : LatticeData) (g : Charge D ≃+ Charge D) (a : NormFour D)
    (m : ℕ) (hm : 0 < m) (hperiod : Function.IsPeriodicPt g m a.1) :
    Module.Basis (Fin (Function.minimalPeriod g a.1)) ℂ
      (groundCycleSpan D g a) := by
  exact Module.Basis.span (cycle_linearIndependent D g a m hm hperiod)

private theorem cycleBasis_apply
    (D : LatticeData) (g : Charge D ≃+ Charge D) (a : NormFour D)
    (m : ℕ) (hm : 0 < m) (hperiod : Function.IsPeriodicPt g m a.1)
    (i : Fin (Function.minimalPeriod g a.1)) :
    (cycleBasis D g a m hm hperiod i : Carrier D) =
      Finsupp.single (g^[i.1] a.1) (1 : Oscillator D) := by
  change (Module.Basis.span (cycle_linearIndependent D g a m hm hperiod) i : Carrier D) = _
  rw [Module.Basis.coe_span_apply]

private theorem cycle_iterate_index
    (D : LatticeData) (g : Charge D ≃+ Charge D) (a : NormFour D)
    (m : ℕ) (_hm : 0 < m) (_hperiod : Function.IsPeriodicPt g m a.1) (n : ℕ)
    (i : Fin (Function.minimalPeriod g a.1)) :
    g^[n] (g^[i.1] a.1) =
      g^[(cycleIndex (Function.minimalPeriod g a.1) n
        i).1] a.1 := by
  rw [← Function.iterate_add_apply, cycleIndex,
    Function.iterate_mod_minimalPeriod_eq]

private theorem cycle_span_stable
    (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ b c, bilinear D (g b) (g c) = bilinear D b c)
    (chi : Charge D →+ F₂) (a : NormFour D)
    (m : ℕ) (hm : 0 < m) (hperiod : Function.IsPeriodicPt g m a.1) (n : ℕ)
    (v : Carrier D) (hv : v ∈ groundCycleSpan D g a) :
    (corrected D g chi ^ n) v ∈ groundCycleSpan D g a := by
  classical
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    rw [corrected_ground_pow_single D g hg, cycle_iterate_index D g a m hm hperiod]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self _))
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    simpa only [map_smul] using Submodule.smul_mem _ r hx

private def cycleAction {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Submodule ℂ V) (T : V →ₗ[ℂ] V)
    (hstable : ∀ v : S, T v.1 ∈ S) : Module.End ℂ S :=
  (T.domRestrict S).codRestrict S hstable

private def groundCycleAction
    (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ b c, bilinear D (g b) (g c) = bilinear D b c)
    (chi : Charge D →+ F₂) (a : NormFour D)
    (m : ℕ) (hm : 0 < m) (hperiod : Function.IsPeriodicPt g m a.1) (n : ℕ) :
    Module.End ℂ (groundCycleSpan D g a) :=
  cycleAction (groundCycleSpan D g a) (corrected D g chi ^ n).toLinearMap
    (fun v => cycle_span_stable D g hg chi a m hm hperiod n v.1 v.2)

private theorem cycle_index_eq_self_iff
    (D : LatticeData) (g : Charge D ≃+ Charge D) (a : NormFour D)
    (m : ℕ) (hm : 0 < m) (hperiod : Function.IsPeriodicPt g m a.1) (n : ℕ)
    (i : Fin (Function.minimalPeriod g a.1)) :
    cycleIndex (Function.minimalPeriod g a.1) n
        i = i ↔
      Function.minimalPeriod g a.1 ∣ n := by
  let d := Function.minimalPeriod g a.1
  have hd : 0 < d := Function.IsPeriodicPt.minimalPeriod_pos hm hperiod
  constructor
  · intro hi
    have hfix : g^[n] (g^[i.1] a.1) = g^[i.1] a.1 := by
      rw [cycle_iterate_index D g a m hm hperiod n i, hi]
    have hfix' : g^[i.1] (g^[n] a.1) = g^[i.1] a.1 := by
      simpa only [← Function.iterate_add_apply, Nat.add_comm] using hfix
    have hperiodn : g^[n] a.1 = a.1 :=
      (g.injective.iterate i.1).eq_iff.mp hfix'
    exact (Function.isPeriodicPt_iff_minimalPeriod_dvd).mp hperiodn
  · intro hdvd
    apply Fin.ext
    apply Eq.symm
    apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod i.2
      (cycleIndex d n i).2).mp
    rw [cycleIndex, Function.iterate_mod_minimalPeriod_eq]
    have hperiodn : g^[n] a.1 = a.1 :=
      (Function.isPeriodicPt_iff_minimalPeriod_dvd).mpr hdvd
    have hadd : n + i.1 = i.1 + n := Nat.add_comm _ _
    rw [hadd, Function.iterate_add_apply, hperiodn]

/-- The actual trace of the corrected power on the ground cycle span. -/
def correctedGroundCycleTrace
    (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ b c, bilinear D (g b) (g c) = bilinear D b c)
    (chi : Charge D →+ F₂) (a : NormFour D)
    (m : ℕ) (hm : 0 < m) (hperiod : Function.IsPeriodicPt g m a.1) (n : ℕ) : ℂ :=
  letI : Module.Finite ℂ (groundCycleSpan D g a) :=
    Module.Finite.of_basis (cycleBasis D g a m hm hperiod)
  LinearMap.trace ℂ (groundCycleSpan D g a)
    (@groundCycleAction D g hg chi a m hm hperiod n)

private def cycleActionSubtype
    (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ b c, bilinear D (g b) (g c) = bilinear D b c)
    (chi : Charge D →+ F₂) (a : NormFour D)
    (m : ℕ) (hm : 0 < m) (hperiod : Function.IsPeriodicPt g m a.1) (n : ℕ)
    (b : groundCycleSpan D g a) : groundCycleSpan D g a :=
  ⟨(corrected D g chi ^ n) b.1,
    cycle_span_stable D g hg chi a m hm hperiod n b.1 b.2⟩

private theorem cycleActionSubtype_basis
    (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ b c, bilinear D (g b) (g c) = bilinear D b c)
    (chi : Charge D →+ F₂) (a : NormFour D)
    (m : ℕ) (hm : 0 < m) (hperiod : Function.IsPeriodicPt g m a.1) (n : ℕ)
    (i : Fin (Function.minimalPeriod g a.1)) :
    cycleActionSubtype D g hg chi a m hm hperiod n
        (cycleBasis D g a m hm hperiod i) =
      ⟨correctedGroundPhase D g chi n (g^[i.1] a.1) •
          (cycleBasis D g a m hm hperiod
            (cycleIndex (Function.minimalPeriod g a.1) n i) : Carrier D),
        Submodule.smul_mem _ _
          (cycleBasis D g a m hm hperiod
            (cycleIndex (Function.minimalPeriod g a.1) n i)).property⟩ := by
  apply Subtype.ext
  change (corrected D g chi ^ n) (cycleBasis D g a m hm hperiod i : Carrier D) =
    correctedGroundPhase D g chi n (g^[i.1] a.1) •
      (cycleBasis D g a m hm hperiod
        (cycleIndex (Function.minimalPeriod g a.1) n i) : Carrier D)
  rw [cycleBasis_apply, corrected_ground_pow_single D g hg chi n (g^[i.1] a.1),
    cycle_iterate_index D g a m hm hperiod n i, cycleBasis_apply]

private theorem cycleTrace_eq_sum
    (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ b c, bilinear D (g b) (g c) = bilinear D b c)
    (chi : Charge D →+ F₂) (a : NormFour D)
    (m : ℕ) (hm : 0 < m) (hperiod : Function.IsPeriodicPt g m a.1) (n : ℕ) :
    correctedGroundCycleTrace D g hg chi a m hm hperiod n =
      ∑ i : Fin (Function.minimalPeriod g a.1),
        if cycleIndex (Function.minimalPeriod g a.1) n
            i = i
        then correctedGroundPhase D g chi n (g^[i.1] a.1) else 0 := by
  letI : Module.Finite ℂ (groundCycleSpan D g a) :=
    Module.Finite.of_basis (cycleBasis D g a m hm hperiod)
  rw [correctedGroundCycleTrace, LinearMap.trace_eq_matrix_trace ℂ
    (cycleBasis D g a m hm hperiod)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change (cycleBasis D g a m hm hperiod).repr
      (cycleActionSubtype D g hg chi a m hm hperiod n
        (cycleBasis D g a m hm hperiod i)) i = _
  rw [cycleActionSubtype_basis D g hg chi a m hm hperiod n i]
  change (cycleBasis D g a m hm hperiod).repr
      (correctedGroundPhase D g chi n (g^[i.1] a.1) •
        cycleBasis D g a m hm hperiod
          (cycleIndex (Function.minimalPeriod g a.1) n i)) i = _
  rw [map_smul, Module.Basis.repr_self]
  by_cases h : cycleIndex (Function.minimalPeriod g a.1) n i = i
  · simp [h]
  · simp [h]

/-- Every power has the literal phase sum on the returning orbit vectors; a
non-returning power has zero trace. -/
theorem corrected_ground_cycle_power_trace
    (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ b c, bilinear D (g b) (g c) = bilinear D b c)
    (chi : Charge D →+ F₂) (a : NormFour D)
    (m : ℕ) (hm : 0 < m) (hperiod : Function.IsPeriodicPt g m a.1) (n : ℕ) :
    correctedGroundCycleTrace D g hg chi a m hm hperiod n =
      if Function.minimalPeriod g a.1 ∣ n then
        ∑ i : Fin (Function.minimalPeriod g a.1),
          correctedGroundPhase D g chi n (g^[i.1] a.1)
      else 0 := by
  rw [cycleTrace_eq_sum D g hg chi a m hm hperiod n]
  by_cases hdvd : Function.minimalPeriod g a.1 ∣ n
  · have hi : ∀ i : Fin (Function.minimalPeriod g a.1),
        cycleIndex (Function.minimalPeriod g a.1) n
          i = i := by
      intro i
      exact (cycle_index_eq_self_iff D g a m hm hperiod n i).mpr hdvd
    simp [hdvd, hi]
  · have hi : ∀ i : Fin (Function.minimalPeriod g a.1),
        cycleIndex (Function.minimalPeriod g a.1) n
          i ≠ i := by
      intro i hi'
      exact hdvd ((cycle_index_eq_self_iff D g a m hm hperiod n i).mp hi')
    simp [hdvd, hi]

abbrev corrected_ground_cycle_power_statement : Prop :=
  type_of% (@corrected_ground_cycle_power_trace)

theorem corrected_ground_cycle_power_trace_observed (s : Bool) :
    (s = true) ↔
      (if s then corrected_ground_cycle_power_statement else False) := by
  cases s
  · simp
  · have h : corrected_ground_cycle_power_statement :=
      corrected_ground_cycle_power_trace
    simpa using h

end D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitTrace
