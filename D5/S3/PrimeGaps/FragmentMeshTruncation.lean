/- GID: D5/S3/PrimeGaps/FragmentMeshTruncation
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   digest: Bound changes of the actual fragment mass mesh cell by a proved small-fragment tail and an explicit boundary-strip probability. -/

import D5.S3.PrimeGaps.FragmentLaw

/-!
# Truncation through a discontinuous mass mesh

The upstream first moment already controls the deleted fragment mass. A floor
readout additionally needs a boundary strip. This module proves that separation
for the actual finite-measure state space, without assuming that the floor is
continuous or that the retained mass avoids every boundary. The boundary
probability remains in the conclusion; it is not an unproved numerical cap.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace PrimeGap186

/-- Delete exactly the fragment locations in `(0, epsilon]`. -/
noncomputable def retainedFragments (epsilon : ℝ) (c : FiniteMeasure ℝ) :
    FiniteMeasure ℝ :=
  c.restrict (Set.Ioc (0 : ℝ) epsilon)ᶜ

/-- The deleted weighted mass, expressed as a real number. -/
noncomputable def deletedFragmentMass (epsilon : ℝ) (c : FiniteMeasure ℝ) : ℝ :=
  c (Set.Ioc (0 : ℝ) epsilon)

/-- The retained and deleted masses partition the original finite measure. -/
theorem retained_deleted_mass (epsilon : ℝ) (c : FiniteMeasure ℝ) :
    ((retainedFragments epsilon c).mass : ℝ) + deletedFragmentMass epsilon c =
      (c.mass : ℝ) := by
  have he := measure_add_measure_compl (μ := (c : Measure ℝ))
    (s := Set.Ioc (0 : ℝ) epsilon) measurableSet_Ioc
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    ← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    ← FiniteMeasure.ennreal_mass] at he
  have hn : c (Set.Ioc (0 : ℝ) epsilon) +
      c (Set.Ioc (0 : ℝ) epsilon)ᶜ = c.mass := by exact_mod_cast he
  have hr : (c (Set.Ioc (0 : ℝ) epsilon) : ℝ) +
      (c (Set.Ioc (0 : ℝ) epsilon)ᶜ : ℝ) = (c.mass : ℝ) := by exact_mod_cast hn
  simpa [retainedFragments, deletedFragmentMass, FiniteMeasure.restrict_mass,
    add_comm] using hr

/-- The upstream Markov estimate applied to the real-valued deleted mass. -/
theorem deletedFragmentMass_tail (zeta epsilon delta : ℝ)
    (hzeta : 0 < zeta) (hepsilon : 0 ≤ epsilon) (hdelta : 0 < delta) :
    fragmentLaw zeta {c | delta ≤ deletedFragmentMass epsilon c} ≤
      ENNReal.ofReal (min epsilon zeta) / ENNReal.ofReal delta := by
  have hsets : {c : FiniteMeasure ℝ | delta ≤ deletedFragmentMass epsilon c} =
      {c : FiniteMeasure ℝ | ENNReal.ofReal delta ≤
        (c : Measure ℝ) (Set.Ioc (0 : ℝ) epsilon)} := by
    ext c
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    change (delta ≤ (c (Set.Ioc (0 : ℝ) epsilon) : ℝ)) ↔ _
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_le_ofReal_iff (c _).coe_nonneg).symm
  rw [hsets]
  exact fragmentLaw_small_seed_tail zeta epsilon delta hzeta hepsilon hdelta

/-- A nonnegative increment crossing a mesh cell either reaches the prescribed
size or starts within that size of the next mesh boundary. -/
theorem floor_mesh_crossing_alternative
    (x d h delta : ℝ) (hx : 0 ≤ x) (hd : 0 ≤ d) (hh : 0 < h)
    (hcross : ⌊(x + d) / h⌋₊ ≠ ⌊x / h⌋₊) :
    delta ≤ d ∨ ((⌊x / h⌋₊ : ℝ) + 1) * h - delta ≤ x := by
  by_cases hlarge : delta ≤ d
  · exact Or.inl hlarge
  right
  have hmono : ⌊x / h⌋₊ ≤ ⌊(x + d) / h⌋₊ :=
    Nat.floor_mono (div_le_div_of_nonneg_right (by linarith) hh.le)
  have hnat : ⌊x / h⌋₊ + 1 ≤ ⌊(x + d) / h⌋₊ := by omega
  have hlow : ((⌊x / h⌋₊ : ℝ) + 1) ≤ (x + d) / h := by
    have hcast : ((⌊x / h⌋₊ + 1 : ℕ) : ℝ) ≤
        (⌊(x + d) / h⌋₊ : ℝ) := by exact_mod_cast hnat
    exact (by simpa only [Nat.cast_add, Nat.cast_one] using hcast).trans
      (Nat.floor_le (div_nonneg (add_nonneg hx hd) hh.le))
  have hmul := (le_div_iff₀ hh).mp hlow
  have hsmall : d < delta := lt_of_not_ge hlarge
  linarith

/-- Actual fragment-cell errors split into a certified small-mass tail plus an
explicit retained-mass boundary-strip probability. No anti-concentration
assumption is silently supplied for the second term. -/
theorem fragment_mesh_change_probability
    (zeta epsilon delta h : ℝ)
    (hzeta : 0 < zeta) (hepsilon : 0 ≤ epsilon)
    (hdelta : 0 < delta) (hh : 0 < h) :
    fragmentLaw zeta {c : FiniteMeasure ℝ |
      ⌊(c.mass : ℝ) / h⌋₊ ≠
        ⌊((retainedFragments epsilon c).mass : ℝ) / h⌋₊} ≤
      ENNReal.ofReal (min epsilon zeta) / ENNReal.ofReal delta +
        fragmentLaw zeta {c : FiniteMeasure ℝ |
          ((⌊((retainedFragments epsilon c).mass : ℝ) / h⌋₊ : ℝ) + 1) * h - delta ≤
            ((retainedFragments epsilon c).mass : ℝ)} := by
  have hsub : {c : FiniteMeasure ℝ |
      ⌊(c.mass : ℝ) / h⌋₊ ≠
        ⌊((retainedFragments epsilon c).mass : ℝ) / h⌋₊} ⊆
      {c : FiniteMeasure ℝ | delta ≤ deletedFragmentMass epsilon c} ∪
      {c : FiniteMeasure ℝ |
        ((⌊((retainedFragments epsilon c).mass : ℝ) / h⌋₊ : ℝ) + 1) * h - delta ≤
          ((retainedFragments epsilon c).mass : ℝ)} := by
    intro c hc
    apply floor_mesh_crossing_alternative
      ((retainedFragments epsilon c).mass : ℝ) (deletedFragmentMass epsilon c)
      h delta (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) hh
    simpa only [retained_deleted_mass] using hc
  calc
    _ ≤ fragmentLaw zeta
        ({c : FiniteMeasure ℝ | delta ≤ deletedFragmentMass epsilon c} ∪
          {c : FiniteMeasure ℝ |
            ((⌊((retainedFragments epsilon c).mass : ℝ) / h⌋₊ : ℝ) + 1) * h - delta ≤
              ((retainedFragments epsilon c).mass : ℝ)}) := measure_mono hsub
    _ ≤ fragmentLaw zeta {c | delta ≤ deletedFragmentMass epsilon c} +
        fragmentLaw zeta {c : FiniteMeasure ℝ |
          ((⌊((retainedFragments epsilon c).mass : ℝ) / h⌋₊ : ℝ) + 1) * h - delta ≤
            ((retainedFragments epsilon c).mass : ℝ)} := measure_union_le _ _
    _ ≤ _ := add_le_add_right
      (deletedFragmentMass_tail zeta epsilon delta hzeta hepsilon hdelta) _

#print axioms retained_deleted_mass
#print axioms deletedFragmentMass_tail
#print axioms floor_mesh_crossing_alternative
#print axioms fragment_mesh_change_probability

end PrimeGap186
