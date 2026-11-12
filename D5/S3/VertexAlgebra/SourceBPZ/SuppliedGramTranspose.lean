/- GID: D5/S3/VertexAlgebra/SourceBPZ/SuppliedGramTranspose
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceBPZ/SuppliedGramTranspose
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original all-state BPZ for a supplied two-sided complex inverse Gram matrix. -/

import D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose
import D5.S3.VertexAlgebra.SourceMobius.OriginalCarrier
import Batteries.Tactic.OpenPrivate

/-!
The original source pairing, fields and charged-word transpose are retained.
Only the passage from the polynomial source flow to the supplied Sugawara
operator, and its finite linear collection, are reconstructed here. The two
complex inverse identities are supplied directly. No integer determinant-unit
hypothesis is used. The cutoff is the actual finite oscillator support of the
source, including the zero source; no finiteness of an entire energy grade is
asserted. The rank and signed integer energy are unrestricted.

This reuses the finite normal-product BPZ argument in AllStateTranspose,
following Bakalov--Kac, math/0402315v1, section 4.1. No novelty is asserted.
This exported source has not been compiled in this source-only flight.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.SourceBPZ.SuppliedGramTranspose

open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeSugawaraCurrents LatticePositiveEnergy
open SourceMobius OriginalSourcePairing MvPolynomial
open LatticeHalfFockFiniteCorrection (sourceWeight)
open private leftPair rightPair polynomialPair_monomial word_transpose
  occurrences_weight from D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose

set_option maxHeartbeats 2000000 in
-- Consumed by sourcePairing_allState below; the word proof itself is reused.
private theorem supplied_monomial_transpose (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α : Charge D) (e : Index D →₀ ℕ) (R : ℕ)
    (hR : e.weight (sourceWeight D) ≤ R) (m : ℤ) (u v : Carrier D) :
    leftPair D m u v (Finsupp.single α (monomial e 1)) =
      (-1 : ℂ)^(chargeEnergy D α+(e.weight (sourceWeight D) : ℤ)) *
        ∑ j ∈ Finset.range (R+1), (j.factorial : ℂ)⁻¹ *
          rightPair D (2*(chargeEnergy D α+(e.weight (sourceWeight D) : ℤ))-j-m-2) u v
            ((sugawaraMode D H 1 ^ j) (Finsupp.single α (monomial e 1))) := by
  have h := word_transpose D α (occurrences D e) m u v
  rw [occurrences_product, occurrences_weight] at h
  have killed : ((sectorL1 D α).toLinearMap ^ (R+1)) (monomial e 1) = 0 :=
    Module.End.pow_map_zero_of_le (Nat.add_le_add_right hR 1)
      (sectorL1_monomial_bound D α e 1)
  rw [flowPolynomial_eq_sum D α _ R killed, map_sum] at h
  simp only [polynomialPair_monomial, map_smul, smul_eq_mul] at h
  rw [h]
  apply congrArg (fun z : ℂ =>
    (-1 : ℂ)^(chargeEnergy D α+(e.weight (sourceWeight D) : ℤ)) * z)
  apply Finset.sum_congr rfl
  intro j hj
  rw [sugawara_pow_single D H hHG hGH]
  rw [show 2*(chargeEnergy D α+(e.weight (sourceWeight D) : ℤ))-m-2-j =
      2*(chargeEnergy D α+(e.weight (sourceWeight D) : ℤ))-j-m-2 by omega]
  rfl

set_option maxHeartbeats 2000000 in
/-- All homogeneous original sources and arbitrary charged descendants obey
the literal BPZ identity for the supplied two-sided complex inverse Gram
matrix. The common cutoff is computed from the source's actual finite
charge and monomial supports, independently of the sign of its energy. -/
theorem sourcePairing_allState (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (d m : ℤ) (a : Carrier D) (ha : a ∈ grade D d) (u v : Carrier D) :
    sourcePairing D (((Y D a)[[m]]) u) v =
      (-1 : ℂ)^d * ∑ j ∈ Finset.range (a.support.sup
        (fun α => weightedTotalDegree (sourceWeight D) (a α)) + 1),
        (j.factorial : ℂ)⁻¹ * sourcePairing D u
          (((Y D ((sugawaraMode D H 1 ^ j) a))[[2*d-(j : ℤ)-m-2]]) v) := by
  classical
  let R := a.support.sup (fun α => weightedTotalDegree (sourceWeight D) (a α))
  let T : Carrier D →ₗ[ℂ] ℂ := ∑ j ∈ Finset.range (R+1),
    (j.factorial : ℂ)⁻¹ •
      (rightPair D (2*d-j-m-2) u v).comp (sugawaraMode D H 1 ^ j)
  have applyT (b : Carrier D) : T b = ∑ j ∈ Finset.range (R+1),
      (j.factorial : ℂ)⁻¹ * rightPair D (2*d-j-m-2) u v
        ((sugawaraMode D H 1 ^ j) b) := by
    simp only [T, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, smul_eq_mul]
  change leftPair D m u v a = (-1 : ℂ)^d * ∑ j ∈ Finset.range (R+1),
    (j.factorial : ℂ)⁻¹ * rightPair D (2*d-j-m-2) u v
      ((sugawaraMode D H 1 ^ j) a)
  rw [← applyT]
  have basis (α : Charge D) (hα : α ∈ a.support) (e : Index D →₀ ℕ)
      (he : e ∈ (a α).support) :
      leftPair D m u v (Finsupp.single α (monomial e 1)) =
        (-1 : ℂ)^d * T (Finsupp.single α (monomial e 1)) := by
    have energy_eq : energy D (α,e) = d := by
      by_contra hn
      exact (MvPolynomial.mem_support_iff.mp he) ((mem_grade_iff D d a).mp ha (α,e) hn)
    have degree : chargeEnergy D α+(e.weight (sourceWeight D) : ℤ) = d := energy_eq
    have hR : e.weight (sourceWeight D) ≤ R :=
      (le_weightedTotalDegree (sourceWeight D) he).trans
        (Finset.le_sup (f := fun α => weightedTotalDegree (sourceWeight D) (a α)) hα)
    have h := supplied_monomial_transpose D H hHG hGH α e R hR m u v
    rw [degree] at h
    simpa only [T, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      smul_eq_mul] using h
  have expansion : a = ∑ α ∈ a.support, ∑ e ∈ (a α).support,
      (a α).coeff e • Finsupp.single α (monomial e 1) := by
    calc
      a = ∑ α ∈ a.support, Finsupp.single α (a α) := (Finsupp.sum_single a).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro α hα
        conv_lhs => arg 2; rw [(a α).as_sum]
        rw [Finsupp.single_finsetSum]
        apply Finset.sum_congr rfl
        intro e he
        simp only [Finsupp.smul_single, smul_monomial, smul_eq_mul, mul_one]
  rw [expansion]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  apply Finset.sum_congr rfl
  intro e he
  rw [basis α hα e he]
  ring

end D5.S3.VertexAlgebra.SourceBPZ.SuppliedGramTranspose
