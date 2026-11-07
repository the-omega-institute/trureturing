/- GID: D5/S3/VertexAlgebra/Lattice/CyclicGroundOrbitFixedSpace
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/CyclicGroundOrbitFixedSpace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First-return phases classify the actual charge-cycle ground fixed space. -/

import D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitBasis
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
The span is the literal span of zero-oscillator ground vectors on one actual
charge cycle. Coefficient transport is derived from the corrected lattice
operator, not assumed as a monomial representation. A supported fixed vector
is reconstructed from its starting coefficient. Nontrivial first-return
holonomy annihilates that coefficient, even if a longer operator period closes.

proof_shape: content
admission_basis: escape-witness
escape_witness: coefficient transport and reconstruction inside the actual
finite charge-cycle span, including the shorter-return phase obstruction.
The existing cyclic lift supplies its actual power formula; Mathlib supplies
minimal-period positivity and distinctness. No rootlessness, positive form,
whole-shell finiteness, grade-two count or coherent full-group lift is used.
The monomial-cycle principle is classical linear algebra; no novelty is claimed.
utility: none; this is an unrestricted algebraic classification.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitFixedSpace

open CyclicGroundOrbitBasis CyclicIsometryLift RootlessLowGrades
open LatticeGeneratingFieldLocality LatticePositiveEnergy
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open scoped BigOperators

open private corrected_pow_single orbitExponent from
  D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
open private geometric_shift from
  D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitBasis

/-- Literal zero-oscillator ground span on the first-return charge cycle. -/
def groundCycleSpan (D : LatticeData) (g : Charge D ≃+ Charge D)
    (a : NormFour D) : Submodule ℂ (Carrier D) :=
  Submodule.span ℂ (Set.range (fun i : Fin (Function.minimalPeriod g a.1) =>
    Finsupp.single (g^[i.1] a.1) (1 : Oscillator D)))

private def coeff (D : LatticeData) (b : Charge D) : Carrier D →ₗ[ℂ] ℂ :=
  (carrierBasis D).coord (b, 0)

private theorem coeff_ground (D : LatticeData) (b c : Charge D) :
    coeff D c (Finsupp.single b (1 : Oscillator D)) = if b = c then 1 else 0 := by
  classical
  change ((Finsupp.single b (1 : Oscillator D)) c).coeff 0 = _
  by_cases h : b = c <;> simp [h]

private def phase (D : LatticeData) (g : Charge D ≃+ Charge D)
    (chi : Charge D →+ F₂) (j : ℕ) (b : Charge D) : ℂ :=
  complexSign (orbitExponent D g j b + chi (orbitNorm D g j b))

private theorem power_ground (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ b c, bilinear D (g b) (g c) = bilinear D b c)
    (chi : Charge D →+ F₂) (j : ℕ) (b : Charge D) :
    (corrected D g chi ^ j) (Finsupp.single b (1 : Oscillator D)) =
      phase D g chi j b • Finsupp.single (g^[j] b) (1 : Oscillator D) := by
  simpa only [map_one, phase] using corrected_pow_single D g hg chi j b 1

private theorem cycle_coeff (D : LatticeData) (g : Charge D ≃+ Charge D)
    (a : NormFour D) (k : Fin (Function.minimalPeriod g a.1))
    (c : Fin (Function.minimalPeriod g a.1) → ℂ) :
    coeff D (g^[k.1] a.1)
      (∑ i, c i • Finsupp.single (g^[i.1] a.1) (1 : Oscillator D)) = c k := by
  classical
  simp only [map_sum, map_smul, coeff_ground, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hik
    have hne : g^[i.1] a.1 ≠ g^[k.1] a.1 := by
      intro h
      exact hik (Fin.ext ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
        i.2 k.2).mp h))
    simp [hne]
  · simp

private theorem transport (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ b c, bilinear D (g b) (g c) = bilinear D b c)
    (chi : Charge D →+ F₂) (a : NormFour D) (j : ℕ)
    (v : Carrier D) (hv : v ∈ groundCycleSpan D g a) :
    coeff D (g^[j] a.1) ((corrected D g chi ^ j) v) =
      phase D g chi j a.1 * coeff D a.1 v := by
  classical
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    rw [power_ground D g hg, map_smul, coeff_ground, coeff_ground]
    have hinj : Function.Injective (g^[j]) := g.injective.iterate j
    by_cases hi : g^[i.1] a.1 = a.1
    · simp [hi]
    · simp [hi, hinj.eq_iff]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy, mul_add]
  | smul r x _ hx =>
    simp only [map_smul, hx, smul_eq_mul]
    ring

private theorem orbit_sum (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ b c, bilinear D (g b) (g c) = bilinear D b c)
    (chi : Charge D →+ F₂) (a : NormFour D) :
    phaseFilteredGroundOrbit D g chi (Function.minimalPeriod g a.1) a =
      ∑ i : Fin (Function.minimalPeriod g a.1), phase D g chi i.1 a.1 •
        Finsupp.single (g^[i.1] a.1) (1 : Oscillator D) := by
  simp only [phaseFilteredGroundOrbit, chargeGroundVector, power_ground D g hg]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

private theorem orbit_coordinate (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ b c, bilinear D (g b) (g c) = bilinear D b c)
    (chi : Charge D →+ F₂) (a : NormFour D)
    (hd : 0 < Function.minimalPeriod g a.1) :
    coeff D a.1 (phaseFilteredGroundOrbit D g chi (Function.minimalPeriod g a.1) a) = 1 := by
  have h := cycle_coeff D g a ⟨0, hd⟩ (fun i => phase D g chi i.1 a.1)
  rw [orbit_sum D g hg chi a]
  simpa [phase, orbitExponent, orbitNorm, complexSign] using h

private theorem fixed_power (D : LatticeData) (g : Charge D ≃+ Charge D)
    (chi : Charge D →+ F₂) (v : Carrier D)
    (hv : v ∈ correctedFixedSpace D g chi) (j : ℕ) :
    (corrected D g chi ^ j) v = v := by
  have hf : corrected D g chi v = v := by
    exact sub_eq_zero.mp hv
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hf]

private theorem reconstruct (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ b c, bilinear D (g b) (g c) = bilinear D b c)
    (chi : Charge D →+ F₂) (a : NormFour D) (v : Carrier D)
    (hs : v ∈ groundCycleSpan D g a) (hf : v ∈ correctedFixedSpace D g chi) :
    v = coeff D a.1 v •
      phaseFilteredGroundOrbit D g chi (Function.minimalPeriod g a.1) a := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hs
  have hcoeff (i : Fin (Function.minimalPeriod g a.1)) :
      c i = phase D g chi i.1 a.1 * coeff D a.1 v := by
    have ht := transport D g hg chi a i.1 v hs
    rw [fixed_power D g chi v hf] at ht
    conv_lhs at ht => rw [← hc, cycle_coeff]
    exact ht
  conv_lhs => rw [← hc]
  rw [orbit_sum D g hg chi a, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hcoeff, smul_smul, mul_comm]

private theorem orbit_mem (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ b c, bilinear D (g b) (g c) = bilinear D b c)
    (chi : Charge D →+ F₂) (a : NormFour D) :
    phaseFilteredGroundOrbit D g chi (Function.minimalPeriod g a.1) a ∈
      groundCycleSpan D g a := by
  classical
  rw [orbit_sum D g hg chi a]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- First-return holonomy decides the actual orbit-supported fixed space.
The orbit sum has starting coefficient one and is nonzero in either branch. -/
theorem first_return_ground_fixed_space
    (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ b c, bilinear D (g b) (g c) = bilinear D b c)
    (chi : Charge D →+ F₂) (a : NormFour D)
    (m : ℕ) (hm : 0 < m) (hperiod : g^[m] a.1 = a.1) :
    let d := Function.minimalPeriod g a.1
    let u := phaseFilteredGroundOrbit D g chi d a
    (groundCycleSpan D g a ⊓ correctedFixedSpace D g chi =
      if (corrected D g chi ^ d) (chargeGroundVector D a) = chargeGroundVector D a
      then Submodule.span ℂ {u} else ⊥) ∧
    (carrierCoeffEquiv D u) (a.1, 0) = 1 ∧ u ≠ 0 := by
  classical
  dsimp only
  let d := Function.minimalPeriod g a.1
  let u := phaseFilteredGroundOrbit D g chi d a
  have hd : 0 < d := Function.IsPeriodicPt.minimalPeriod_pos hm hperiod
  have hcoord : coeff D a.1 u = 1 := orbit_coordinate D g hg chi a hd
  have hne : u ≠ 0 := by
    intro h
    have hh := hcoord
    rw [h, map_zero] at hh
    exact zero_ne_one hh
  refine ⟨?_, hcoord, hne⟩
  by_cases hr : (corrected D g chi ^ d) (chargeGroundVector D a) = chargeGroundVector D a
  · rw [ite_eq_left hr]
    have huf : u ∈ correctedFixedSpace D g chi := by
      change corrected D g chi u - u = 0
      apply sub_eq_zero.mpr
      change corrected D g chi (∑ j ∈ Finset.range d,
        (corrected D g chi ^ j) (chargeGroundVector D a)) = _
      rw [geometric_shift, hr, add_sub_cancel_right]
      rfl
    apply le_antisymm
    · intro v hv
      rw [reconstruct D g hg chi a v hv.1 hv.2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
    · apply Submodule.span_le.mpr
      rintro v (rfl : v = u)
      exact ⟨orbit_mem D g hg chi a, huf⟩
  · rw [ite_eq_right hr]
    apply le_antisymm
    · intro v hv
      have hvu := reconstruct D g hg chi a v hv.1 hv.2
      have heq := fixed_power D g chi v hv.2 1
      simp only [pow_one] at heq
      rw [hvu, map_smul] at heq
      change coeff D a.1 v • corrected D g chi u = coeff D a.1 v • u at heq
      have hshift : corrected D g chi u = u +
          (corrected D g chi ^ d) (chargeGroundVector D a) - chargeGroundVector D a :=
        geometric_shift (corrected D g chi) d (chargeGroundVector D a)
      have hz : coeff D a.1 v •
          ((corrected D g chi ^ d) (chargeGroundVector D a) - chargeGroundVector D a) = 0 := by
        rw [hshift, smul_sub, smul_add] at heq
        rw [smul_sub]
        have hcanc : coeff D a.1 v • u +
            (coeff D a.1 v • (corrected D g chi ^ d) (chargeGroundVector D a) -
              coeff D a.1 v • chargeGroundVector D a) = coeff D a.1 v • u + 0 := by
          simpa only [sub_eq_add_neg, add_assoc, add_zero] using heq
        exact add_left_cancel hcanc
      have hc : coeff D a.1 v = 0 := (smul_eq_zero.mp hz).resolve_right
        (sub_ne_zero.mpr hr)
      exact (Submodule.mem_bot ℂ).mpr (by simpa [hc] using hvu)
    · exact bot_le

end D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitFixedSpace
