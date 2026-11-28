/- GID: D5/S3/Combinatorics/Turnpike/SubsetRelations/Check256
   generality: G
   mirror-B: none(waiver:covered-by-pruned-subset-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete numerical relation with closed rank-block masks -/

module
public import D5.S3.Combinatorics.Turnpike.SubsetRelations.Check246
/-! Omega original.
# Complete numerical relation with closed rank-block masks
-/
@[expose] public section
namespace Omega.Turnpike.SubsetCertificate
namespace Numeric256
def τ : Triangle 7 := ⟨(2,5,6),by decide⟩
set_option maxRecDepth 10000
private theorem row_0 : ∀ b c : Fin 12,
    (0,b,c) ∈ numericAtoms τ ↔
      values 0 + values b = values c ∧
      ((0 : Fin 12) ≠ b ∨ 2 ≤ μ 0) ∧ ProductAllowed μ τ (0,b,c) := by
  unfold ProductAllowed RankAllowed
  decide +kernel
private theorem row_1 : ∀ b c : Fin 12,
    (1,b,c) ∈ numericAtoms τ ↔
      values 1 + values b = values c ∧
      ((1 : Fin 12) ≠ b ∨ 2 ≤ μ 1) ∧ ProductAllowed μ τ (1,b,c) := by
  unfold ProductAllowed RankAllowed
  decide +kernel
private theorem row_2 : ∀ b c : Fin 12,
    (2,b,c) ∈ numericAtoms τ ↔
      values 2 + values b = values c ∧
      ((2 : Fin 12) ≠ b ∨ 2 ≤ μ 2) ∧ ProductAllowed μ τ (2,b,c) := by
  unfold ProductAllowed RankAllowed
  decide +kernel
private theorem row_3 : ∀ b c : Fin 12,
    (3,b,c) ∈ numericAtoms τ ↔
      values 3 + values b = values c ∧
      ((3 : Fin 12) ≠ b ∨ 2 ≤ μ 3) ∧ ProductAllowed μ τ (3,b,c) := by
  unfold ProductAllowed RankAllowed
  decide +kernel
private theorem row_4 : ∀ b c : Fin 12,
    (4,b,c) ∈ numericAtoms τ ↔
      values 4 + values b = values c ∧
      ((4 : Fin 12) ≠ b ∨ 2 ≤ μ 4) ∧ ProductAllowed μ τ (4,b,c) := by
  unfold ProductAllowed RankAllowed
  decide +kernel
private theorem row_5 : ∀ b c : Fin 12,
    (5,b,c) ∈ numericAtoms τ ↔
      values 5 + values b = values c ∧
      ((5 : Fin 12) ≠ b ∨ 2 ≤ μ 5) ∧ ProductAllowed μ τ (5,b,c) := by
  unfold ProductAllowed RankAllowed
  decide +kernel
private theorem row_6 : ∀ b c : Fin 12,
    (6,b,c) ∈ numericAtoms τ ↔
      values 6 + values b = values c ∧
      ((6 : Fin 12) ≠ b ∨ 2 ≤ μ 6) ∧ ProductAllowed μ τ (6,b,c) := by
  unfold ProductAllowed RankAllowed
  decide +kernel
private theorem row_7 : ∀ b c : Fin 12,
    (7,b,c) ∈ numericAtoms τ ↔
      values 7 + values b = values c ∧
      ((7 : Fin 12) ≠ b ∨ 2 ≤ μ 7) ∧ ProductAllowed μ τ (7,b,c) := by
  unfold ProductAllowed RankAllowed
  decide +kernel
private theorem row_8 : ∀ b c : Fin 12,
    (8,b,c) ∈ numericAtoms τ ↔
      values 8 + values b = values c ∧
      ((8 : Fin 12) ≠ b ∨ 2 ≤ μ 8) ∧ ProductAllowed μ τ (8,b,c) := by
  unfold ProductAllowed RankAllowed
  decide +kernel
private theorem row_9 : ∀ b c : Fin 12,
    (9,b,c) ∈ numericAtoms τ ↔
      values 9 + values b = values c ∧
      ((9 : Fin 12) ≠ b ∨ 2 ≤ μ 9) ∧ ProductAllowed μ τ (9,b,c) := by
  unfold ProductAllowed RankAllowed
  decide +kernel
private theorem row_10 : ∀ b c : Fin 12,
    (10,b,c) ∈ numericAtoms τ ↔
      values 10 + values b = values c ∧
      ((10 : Fin 12) ≠ b ∨ 2 ≤ μ 10) ∧ ProductAllowed μ τ (10,b,c) := by
  unfold ProductAllowed RankAllowed
  decide +kernel
private theorem row_11 : ∀ b c : Fin 12,
    (11,b,c) ∈ numericAtoms τ ↔
      values 11 + values b = values c ∧
      ((11 : Fin 12) ≠ b ∨ 2 ≤ μ 11) ∧ ProductAllowed μ τ (11,b,c) := by
  unfold ProductAllowed RankAllowed
  decide +kernel
theorem complete : ∀ r : Fin 12 × Fin 12 × Fin 12,
    r ∈ numericAtoms τ ↔
      values r.1 + values r.2.1 = values r.2.2 ∧
      (r.1 ≠ r.2.1 ∨ 2 ≤ μ r.1) ∧ ProductAllowed μ τ r := by
  rintro ⟨a,b,c⟩
  fin_cases a
  · exact row_0 b c
  · exact row_1 b c
  · exact row_2 b c
  · exact row_3 b c
  · exact row_4 b c
  · exact row_5 b c
  · exact row_6 b c
  · exact row_7 b c
  · exact row_8 b c
  · exact row_9 b c
  · exact row_10 b c
  · exact row_11 b c
end Numeric256
end Omega.Turnpike.SubsetCertificate
