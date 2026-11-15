/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229578
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/HardinA229578
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The seven empirical column recurrences of the literal OEIS A229578 table. -/
/-
admission_basis: open-problem-resolution (#30641; Proved)
escape_witness: KingPath.tail_counts (parametric induction for zero/one equality tails; propagated through path_count and width_one_large to the k = 1 recurrence)
result: proof_shape=content; consumers=none (registered settlement result)
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingPath
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm
import D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229573
import D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229574
import D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229575
import D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229576
import D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229577

/-! All seven column formulas with their literal published thresholds. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229578

theorem result :
    (∀ n : ℕ, 6 < n → (KingGrid.T n 1 : ℤ) =
      8*(KingGrid.T (n-1) 1 : ℤ)-22*(KingGrid.T (n-2) 1 : ℤ)+
        24*(KingGrid.T (n-3) 1 : ℤ)-9*(KingGrid.T (n-4) 1 : ℤ)) ∧
    (∀ n : ℕ, 3 < n → (KingGrid.T n 2 : ℤ) =
      4*(KingGrid.T (n-1) 2 : ℤ)-4*(KingGrid.T (n-2) 2 : ℤ)) ∧
    (∀ n : ℕ, 5 < n → (KingGrid.T n 3 : ℤ) =
      6*(KingGrid.T (n-1) 3 : ℤ)-13*(KingGrid.T (n-2) 3 : ℤ)+
        12*(KingGrid.T (n-3) 3 : ℤ)-4*(KingGrid.T (n-4) 3 : ℤ)) ∧
    (∀ n : ℕ, 7 < n → (KingGrid.T n 4 : ℤ) =
      6*(KingGrid.T (n-1) 4 : ℤ)-13*(KingGrid.T (n-2) 4 : ℤ)+
        12*(KingGrid.T (n-3) 4 : ℤ)-4*(KingGrid.T (n-4) 4 : ℤ)) ∧
    (∀ n : ℕ, 7 < n → (KingGrid.T n 5 : ℤ) =
      6*(KingGrid.T (n-1) 5 : ℤ)-13*(KingGrid.T (n-2) 5 : ℤ)+
        12*(KingGrid.T (n-3) 5 : ℤ)-4*(KingGrid.T (n-4) 5 : ℤ)) ∧
    (∀ n : ℕ, 7 < n → (KingGrid.T n 6 : ℤ) =
      6*(KingGrid.T (n-1) 6 : ℤ)-13*(KingGrid.T (n-2) 6 : ℤ)+
        12*(KingGrid.T (n-3) 6 : ℤ)-4*(KingGrid.T (n-4) 6 : ℤ)) ∧
    (∀ n : ℕ, 7 < n → (KingGrid.T n 7 : ℤ) =
      6*(KingGrid.T (n-1) 7 : ℤ)-13*(KingGrid.T (n-2) 7 : ℤ)+
        12*(KingGrid.T (n-3) 7 : ℤ)-4*(KingGrid.T (n-4) 7 : ℤ)) := by
  refine ⟨?_,?_,HardinA229573.result,HardinA229574.result,
    HardinA229575.result,HardinA229576.result,HardinA229577.result⟩
  swap
  · intro n hn
    obtain ⟨m,rfl⟩ : ∃ m, n=m+4 := ⟨n-4,by omega⟩
    have h0 := KingClosedForm.width_two (m+4) (by omega)
    have h1 := KingClosedForm.width_two (m+3) (by omega)
    have h2 := KingClosedForm.width_two (m+2) (by omega)
    push_cast at h0 h1 h2 ⊢
    norm_num [pow_succ] at h0 h1 h2 ⊢
    linear_combination h0-4*h1+4*h2
  intro n hn
  obtain ⟨m,rfl⟩ : ∃ m, n=m+7 := ⟨n-7,by omega⟩
  have h0 := KingPath.width_one_large (m+7) (by omega)
  have h1 := KingPath.width_one_large (m+6) (by omega)
  have h2 := KingPath.width_one_large (m+5) (by omega)
  have h3 := KingPath.width_one_large (m+4) (by omega)
  have h4 := KingPath.width_one_large (m+3) (by omega)
  push_cast at h0 h1 h2 h3 h4 ⊢
  norm_num [pow_succ] at h0 h1 h2 h3 h4 ⊢
  have hz : 54*((KingGrid.T (m+7) 1 : ℤ)-8*(KingGrid.T (m+6) 1 : ℤ)+
      22*(KingGrid.T (m+5) 1 : ℤ)-24*(KingGrid.T (m+4) 1 : ℤ)+
        9*(KingGrid.T (m+3) 1 : ℤ))=0 := by
    linear_combination h0-8*h1+22*h2-24*h3+9*h4
  omega

#check @result
#print axioms result
end D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229578
