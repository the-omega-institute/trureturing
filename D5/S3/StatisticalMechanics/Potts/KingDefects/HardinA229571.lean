/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229571
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/HardinA229571
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact registered one-defect king-colouring identities for OEIS A229571. -/
/-
admission_basis: open-problem-resolution (#30641; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229571.result)
result: proof_shape=bind-only; consumers=none (registered settlement result)
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm

/-! The literal OEIS assertion with its published threshold. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229571

theorem result (n : ℕ) (hn : 9 ≤ n) :
    (KingGrid.T n n : ℤ) = 9*(KingGrid.T (n-1) (n-1) : ℤ)-33*(KingGrid.T (n-2) (n-2) : ℤ)+
      63*(KingGrid.T (n-3) (n-3) : ℤ)-
      66*(KingGrid.T (n-4) (n-4) : ℤ)+36*(KingGrid.T (n-5) (n-5) : ℤ)-
      8*(KingGrid.T (n-6) (n-6) : ℤ) := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+9 := ⟨n-9,by omega⟩
  have h0 := KingClosedForm.diagonal_closed (m+9) (by omega)
  have h1 := KingClosedForm.diagonal_closed (m+8) (by omega)
  have h2 := KingClosedForm.diagonal_closed (m+7) (by omega)
  have h3 := KingClosedForm.diagonal_closed (m+6) (by omega)
  have h4 := KingClosedForm.diagonal_closed (m+5) (by omega)
  have h5 := KingClosedForm.diagonal_closed (m+4) (by omega)
  have h6 := KingClosedForm.diagonal_closed (m+3) (by omega)
  push_cast at h0 h1 h2 h3 h4 h5 h6 ⊢
  norm_num [pow_succ] at h0 h1 h2 h3 h4 h5 h6 ⊢
  have hz : 2*((KingGrid.T (m+9) (m+9) : ℤ)-9*(KingGrid.T (m+8) (m+8) : ℤ)+
      33*(KingGrid.T (m+7) (m+7) : ℤ)-63*(KingGrid.T (m+6) (m+6) : ℤ)+
      66*(KingGrid.T (m+5) (m+5) : ℤ)-36*(KingGrid.T (m+4) (m+4) : ℤ)+
      8*(KingGrid.T (m+3) (m+3) : ℤ))=0 := by
    linear_combination h0-9*h1+33*h2-63*h3+66*h4-36*h5+8*h6
  omega

#check @result
#print axioms result
end D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229571
