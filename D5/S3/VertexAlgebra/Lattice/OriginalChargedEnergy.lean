/- GID: D5/S3/VertexAlgebra/Lattice/OriginalChargedEnergy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/OriginalChargedEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original integer charged fields and the canonical matter Hermitian norm. -/

import D5.S3.VertexAlgebra.SourceBPZ.TransverseHermitian
import D5.S3.VertexAlgebra.SourceBPZ.ChargedRawTranspose
import D5.S3.VertexAlgebra.LatticeActualStateFieldCalculus
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators VertexOperator
open ComplexConjugate

namespace D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy

open LatticeGeneratingFieldLocality LatticeInvolution LatticePositiveEnergy
open SourceBPZ.OriginalMatterHermitian SourceBPZ.OriginalSourcePairing
open SourceBPZ.TransverseHermitian OriginalGram
open LatticeSugawaraCurrents LatticeAllStateField LatticeAllStateReconstruction

variable {D : LatticeData}

private theorem full_frame_matrix (hD : (gramReal D).PosDef) :
    (RC D hD)ᵀ * LatticeSugawaraConformal.gramComplex D * RC D hD = 1 := by
  have hG : (SC D hD)ᵀ * SC D hD = LatticeSugawaraConformal.gramComplex D := by
    ext i j
    exact SC_gram D hD i j
  rw [← hG]
  calc
    _ = (SC D hD * RC D hD)ᵀ * (SC D hD * RC D hD) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [SC_mul_RC]; simp

private def fullFrame (hD : (gramReal D).PosDef) : RealOrthonormalFrame D D.rank where
  B j i := RC D hD i j
  real_B j i := by simp [RC]
  orthonormal j k := by
    have h := congrFun (congrFun (full_frame_matrix hD) j) k
    change (∑ i, (∑ l, RC D hD l j * (D.G l i : ℂ)) * RC D hD i k) = _ at h
    rw [Matrix.one_apply] at h
    change (∑ i, ∑ l, RC D hD i j * (D.G i l : ℂ) * RC D hD l k) = _
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul] at h
    exact h

private def fullOscillatorEquiv (hD : (gramReal D).PosDef) :
    Oscillator D ≃ₐ[ℂ] Oscillator D :=
  OriginalCurrentMetric.substitutionEquiv
    (fun _ => RC D hD) (fun _ => SC D hD)
    (fun _ => RC_mul_SC D hD) (fun _ => SC_mul_RC D hD)

private theorem fullFrame_phi (hD : (gramReal D).PosDef) :
    phi (fullFrame hD) = (fullOscillatorEquiv hD).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro x
  rfl

private theorem fullFrame_surjective (hD : (gramReal D).PosDef) :
    Function.Surjective (transverseEmbed (fullFrame hD)) := by
  intro v
  let x : Charge D →₀ Oscillator D :=
    v.mapRange (fullOscillatorEquiv hD).symm (map_zero _)
  refine ⟨x, ?_⟩
  ext a
  change phi (fullFrame hD) ((fullOscillatorEquiv hD).symm (v a)) = v a
  rw [fullFrame_phi]
  exact (fullOscillatorEquiv hD).apply_symm_apply (v a)

private theorem original_positive (hD : (gramReal D).PosDef) {v : Carrier D}
    (hv : v ≠ 0) : (Hm v v).im = 0 ∧ 0 < (Hm v v).re := by
  obtain ⟨x, rfl⟩ := fullFrame_surjective hD v
  apply Hm_self_strict_positive
  intro hx
  apply hv
  simp [hx, transverseEmbed]

private theorem original_nonnegative (hD : (gramReal D).PosDef) (v : Carrier D) :
    0 ≤ (Hm v v).re := by
  by_cases hv : v = 0
  · subst v
    simp [Hm]
  · exact (original_positive hD hv).2.le

private def normD (v : Carrier D) : ℝ := Real.sqrt (Hm v v).re

private theorem normD_sq (hD : (gramReal D).PosDef) (v : Carrier D) :
    normD v ^ 2 = (Hm v v).re :=
  Real.sq_sqrt (original_nonnegative hD v)

private theorem charged_weight (hD : (gramReal D).PosDef) (a : Charge D)
    (ha : a ≠ 0) :
    0 < (chargeEnergy D a).toNat ∧
      ((chargeEnergy D a).toNat : ℤ) = bilinear D a a / 2 := by
  have hn := chargeEnergy_nonneg D hD a
  have hz := (chargeEnergy_eq_zero_iff D hD a).not.mpr ha
  exact ⟨Int.toNat_pos.mpr (lt_of_le_of_ne hn (Ne.symm hz)), Int.toNat_of_nonneg hn⟩

end D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy
