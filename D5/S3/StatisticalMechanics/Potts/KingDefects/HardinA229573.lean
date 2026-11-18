/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229573
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/HardinA229573
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact registered one-defect king-colouring identities for OEIS A229573. -/
/-
admission_basis: open-problem-resolution (#30641; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229573.result, HardinA229578.result)
result: proof_shape=bind-only; consumers=HardinA229578.result
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm

/-! The literal OEIS assertion with its published threshold. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229573

theorem result (n : ℕ) (hn : 5 < n) :
    (KingGrid.T n 3 : ℤ) = 6*(KingGrid.T (n-1) 3 : ℤ)-13*(KingGrid.T (n-2) 3 : ℤ)+
      12*(KingGrid.T (n-3) 3 : ℤ)-4*(KingGrid.T (n-4) 3 : ℤ) := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+6 := ⟨n-6,by omega⟩
  have h0 := KingClosedForm.width_three (m+6) (by omega)
  have h1 := KingClosedForm.width_three (m+5) (by omega)
  have h2 := KingClosedForm.width_three (m+4) (by omega)
  have h3 := KingClosedForm.width_three (m+3) (by omega)
  have h4 := KingClosedForm.width_three (m+2) (by omega)
  push_cast at h0 h1 h2 h3 h4 ⊢
  norm_num [pow_succ] at h0 h1 h2 h3 h4 ⊢
  have hz : 4*((KingGrid.T (m+6) 3 : ℤ)-
      6*(KingGrid.T (m+5) 3 : ℤ)+13*(KingGrid.T (m+4) 3 : ℤ)-
      12*(KingGrid.T (m+3) 3 : ℤ)+4*(KingGrid.T (m+2) 3 : ℤ))=0 := by
    linear_combination h0-6*h1+13*h2-12*h3+4*h4
  omega

#check @result
#print axioms result
end D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229573
