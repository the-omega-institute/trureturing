/- GID: D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedFinite
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedFinite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite neutral spans for fixed charged ground states and single oscillators. -/

import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralFinite
import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2ChargedOscillator
import Mathlib.RingTheory.Finiteness.Lattice

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.ActualFixedC2

open ActualLeechHyperbolic (leechData)
open LatticeGeneratingFieldLocality LatticeInvolution LatticeSugawaraCurrents

noncomputable section

local instance chargedFiniteFixedCarrierGroup (D : LatticeData) : AddCommGroup (FixedCarrier D) :=
  (fixedSpace D).addCommGroup

attribute [local instance] fixedQuotientRing fixedQuotientAlgebra

/-- The ground class and one first oscillator class per basis direction. -/
def leechChargedSingleGenerator (c : Charge leechData) :
    Option (Fin leechData.rank) → FixedC2Quotient leechData
  | none => (fixedC2 leechData).mkQ (fixedGroundOrbit leechData c)
  | some i => (fixedC2 leechData).mkQ (fixedFirstOscillator leechData i c)

/-- The sum of the images of the neutral subspace under right multiplication
by the ground class and the first oscillator classes. -/
def leechChargedSingleSpan (c : Charge leechData) : Submodule ℂ (FixedC2Quotient leechData) :=
  ⨆ g : Option (Fin leechData.rank),
    (neutralImage leechData).map ((fixedQuotientProduct leechData).flip
      (leechChargedSingleGenerator c g))

theorem leech_charged_single_span_finite (c : Charge leechData) :
    FiniteDimensional ℂ (leechChargedSingleSpan c) := by
  let : FiniteDimensional ℂ (neutralImage leechData) := by
    rw [neutral_image_eq_fixed_neutral_image]
    exact leech_fixed_neutral_image_finite
  unfold leechChargedSingleSpan
  infer_instance

private theorem leech_neutral_one_mem : (1 : FixedC2Quotient leechData) ∈ neutralImage leechData := by
  rw [neutral_image_eq_fixed_neutral_image, leech_neutral_image_eq_low_adjoin]
  exact (Algebra.adjoin ℂ (Set.range (lowNeutralQuadratic leechData))).one_mem

private theorem leech_neutral_mul_mem {a b : FixedC2Quotient leechData}
    (ha : a ∈ neutralImage leechData) (hb : b ∈ neutralImage leechData) :
    a * b ∈ neutralImage leechData := by
  rw [neutral_image_eq_fixed_neutral_image, leech_neutral_image_eq_low_adjoin] at ha hb ⊢
  exact (Algebra.adjoin ℂ (Set.range (lowNeutralQuadratic leechData))).mul_mem ha hb

theorem leech_charged_single_generator_mem (c : Charge leechData)
    (g : Option (Fin leechData.rank)) :
    leechChargedSingleGenerator c g ∈ leechChargedSingleSpan c := by
  apply Submodule.mem_iSup_of_mem g
  exact ⟨1, leech_neutral_one_mem, one_mul _⟩

theorem leech_charged_ground_class_mem (c : Charge leechData) :
    (fixedC2 leechData).mkQ (fixedGroundOrbit leechData c) ∈ leechChargedSingleSpan c :=
  leech_charged_single_generator_mem c none

theorem leech_charged_single_span_mul_mem (c : Charge leechData)
    {a b : FixedC2Quotient leechData} (ha : a ∈ neutralImage leechData)
    (hb : b ∈ leechChargedSingleSpan c) : a * b ∈ leechChargedSingleSpan c := by
  change b ∈ (leechChargedSingleSpan c).comap (fixedQuotientProduct leechData a)
  have hle : leechChargedSingleSpan c ≤
      (leechChargedSingleSpan c).comap (fixedQuotientProduct leechData a) := by
    apply iSup_le
    intro g
    rintro _ ⟨n, hn, rfl⟩
    change a * (n * leechChargedSingleGenerator c g) ∈ leechChargedSingleSpan c
    rw [← mul_assoc]
    apply Submodule.mem_iSup_of_mem g
    exact ⟨a * n, leech_neutral_mul_mem ha hn, rfl⟩
  exact hle hb

/-- Stability under the actual neutral `(-1)` action on representatives. -/
theorem leech_charged_single_span_mode_mem (c : Charge leechData)
    {u v : FixedCarrier leechData}
    (hu : (fixedC2 leechData).mkQ u ∈ neutralImage leechData)
    (hv : (fixedC2 leechData).mkQ v ∈ leechChargedSingleSpan c) :
    (fixedC2 leechData).mkQ (fixedMode leechData u (-1) v) ∈ leechChargedSingleSpan c := by
  rw [← fixed_quotient_mul_mk]
  exact leech_charged_single_span_mul_mem c hu hv

/-- Every neutral quadratic, with arbitrary indices, lies in the neutral image. -/
theorem neutral_pair_class_mem_neutral_image (D : LatticeData) (i j : Fin D.rank)
    (k l : ℕ) : pairClass D i j k l ∈ neutralImage D := by
  rw [neutral_image_eq_fixed_neutral_image]
  exact ⟨neutralPair D i j k l, ⟨_, rfl⟩, rfl⟩

/-- Every single oscillator on a nonzero Leech charge has class in the
same finite-dimensional neutral module as the ground class. -/
theorem leech_charged_oscillator_class_mem (c : Charge leechData) (hc : c ≠ 0)
    (i : Fin leechData.rank) (k : ℕ) :
    (fixedC2 leechData).mkQ (fixedChargedOscillator leechData i k c) ∈ leechChargedSingleSpan c := by
  cases k with
  | zero =>
    rw [fixed_charged_oscillator_zero]
    exact leech_charged_single_generator_mem c (some i)
  | succ k =>
    let S := (leechChargedSingleSpan c).comap (fixedC2 leechData).mkQ
    change fixedChargedOscillator leechData i (k + 1) c ∈ S
    apply fixed_higher_oscillator_mem leechData c (leech_charge_norm_ge_four c hc) k S _ _ i
    · intro v hv
      change (fixedC2 leechData).mkQ v ∈ leechChargedSingleSpan c
      have hzero : (fixedC2 leechData).mkQ v = 0 :=
        (Submodule.Quotient.mk_eq_zero (fixedC2 leechData)).mpr hv
      rw [hzero]
      exact Submodule.zero_mem _
    · intro j
      change (fixedC2 leechData).mkQ (chargeQuadraticMode leechData j k c
        (fixedGroundOrbit leechData c)) ∈ leechChargedSingleSpan c
      rw [charge_quadratic_mode_eq_fixedMode]
      apply leech_charged_single_span_mode_mem c _ (leech_charged_ground_class_mem c)
      rw [map_sum]
      refine Submodule.sum_mem _ fun l _ => ?_
      rw [map_smul]
      exact Submodule.smul_mem _ _ (neutral_pair_class_mem_neutral_image leechData j l k 0)

#print axioms leech_charged_single_span_finite
#print axioms leech_charged_ground_class_mem
#print axioms leech_charged_single_span_mode_mem
#print axioms leech_charged_oscillator_class_mem

end
end D5.S3.VertexAlgebra.Lattice.ActualFixedC2
