import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement
import Reg.Support.DependentFamily

/-! Four-slot source-bound registrations for coarse three-block partition refinements. -/

namespace Reg.D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement

open _root_.D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

private theorem bot2_parts :
    (⊥ : PartyPartition 2).parts = ({({0} : Finset (Fin 2)), {1}} : Finset (Finset (Fin 2))) := by
  ext s
  simp only [Finpartition.mem_bot_iff, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Fin.exists_fin_two, eq_comm]

private theorem singleton0_ne_singleton1 : ({0} : Finset (Fin 2)) ≠ {1} := by
  intro he
  have hm : (0 : Fin 2) ∈ ({1} : Finset (Fin 2)) := he ▸ Finset.mem_singleton_self 0
  simp at hm

namespace Stirling

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m => m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∀ {m : ℕ}, 1 ≤ m → Nat.stirlingSecond (R.readout () () m) 2 = 2 ^ (m - 1) - 1) ∧
    (∀ {q : ℕ}, 1 ≤ q →
      2 * (Nat.stirlingSecond q 2 + Nat.stirlingSecond q 3) = 3 ^ (q - 1) - 1 ∧
      ((3 : ℝ) ^ (q - 1) - 1) / 2 =
        (Nat.stirlingSecond q 2 : ℝ) + (Nat.stirlingSecond q 3 : ℝ)) ∧
    (∀ (q k : ℕ), (partitionsOfCard q k).card = Nat.stirlingSecond q k) ∧
    (∀ {q : ℕ} {σ : PartyPartition q}, σ ∈ partitionsOfCard q 2 →
      ((partitionsOfCard q 3).filter (fun π => π ≤ σ)).card + 2 =
        ∑ B ∈ σ.parts, 2 ^ (B.card - 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.1 (m := 2) (by decide)
  simp [rejected, realize, Nat.stirlingSecond_eq_zero_of_lt] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 0, 1, Nat.zero_ne_one⟩

def source_registration :
    Registration arena (type_of% @stirling_and_three_block_refinement_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨stirling_and_three_block_refinement_count, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩
      exact ⟨rejected, fun ⟨⟩ hj => (hj rfl).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@stirling_and_three_block_refinement_count)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement.Stirling.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement.Stirling.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Stirling

namespace Inversion

abbrev signature : Signature where
  Params := ℕ
  State q := PartyPartition q → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := PartyPartition q → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ r => r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∀ {q : ℕ}, 3 ≤ q → ∀ (r : PartyPartition q → ℝ),
      ∑ σ ∈ twoOrThreePartitions q, r σ =
        ∑ π ∈ partitionsOfCard q 3, upperRankSum r π +
        ∑ σ ∈ partitionsOfCard q 2,
          ((3 : ℝ) - ∑ B ∈ σ.parts, (2 : ℝ) ^ (B.card - 1)) * upperRankSum r σ) ∧
    (∀ {q : ℕ} (c r : PartyPartition q → ℝ),
      ∑ ρ ∈ nontrivialPartitions q,
        c ρ * ((3 : ℝ) ^ (2 - (ρ.parts.card : ℤ)) * upperRankSum r ρ) =
      ∑ σ ∈ twoOrThreePartitions q, coarseWeight c σ * R.readout () q r σ) ∧
    (∀ {q : ℕ} (w : PartyPartition q → ℝ),
      ∃ c : PartyPartition q → ℝ,
        (∀ ρ ∉ twoOrThreePartitions q, c ρ = 0) ∧
        ∀ σ ∈ twoOrThreePartitions q, coarseWeight c σ = w σ) ∧
    (∀ {q : ℕ} (r₁ r₂ : PartyPartition q → ℝ),
      (∀ σ ∈ partitionsOfCard q 2, upperRankSum r₁ σ = upperRankSum r₂ σ) →
      (∀ π ∈ partitionsOfCard q 3, upperRankSum r₁ π = upperRankSum r₂ π) →
      (∀ σ ∈ twoOrThreePartitions q, r₁ σ = r₂ σ) ∧
      (∀ ρ : PartyPartition q, upperRankSum r₁ ρ = upperRankSum r₂ ρ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let one2 : PartyPartition 2 → ℝ := fun _ => 1
  let bot2 : PartyPartition 2 := ⊥
  have hb := h.2.1 (q := 2) one2 one2
  simp only [rejected, realize, mul_zero, Finset.sum_const_zero] at hb
  have hcard : bot2.parts.card = 2 := by simp [bot2]
  have hnt : bot2 ∈ nontrivialPartitions 2 := by simp [nontrivialPartitions, hcard]
  have h23 : bot2 ∈ (twoOrThreePartitions 2).filter (fun σ => bot2 ≤ σ) := by
    simp [twoOrThreePartitions, partitionsOfCard, hcard]
  have hurs_nonneg : ∀ ρ : PartyPartition 2, 0 ≤ upperRankSum one2 ρ := fun ρ =>
    Finset.sum_nonneg (fun _ _ => by norm_num [one2])
  have hurs_bot : 1 ≤ upperRankSum one2 bot2 :=
    Finset.single_le_sum (f := one2) (fun _ _ => by norm_num [one2]) h23
  have hterm_nonneg : ∀ ρ ∈ nontrivialPartitions 2,
      0 ≤ one2 ρ * ((3 : ℝ) ^ (2 - (ρ.parts.card : ℤ)) * upperRankSum one2 ρ) :=
    fun ρ _ => mul_nonneg (by norm_num [one2])
      (mul_nonneg (zpow_nonneg (by norm_num) _) (hurs_nonneg ρ))
  have hsingle := Finset.single_le_sum hterm_nonneg hnt
  rw [hb] at hsingle
  have h1 : (1 : ℝ) ≤
      one2 bot2 * ((3 : ℝ) ^ (2 - (bot2.parts.card : ℤ)) * upperRankSum one2 bot2) := by
    rw [hcard]
    simpa [one2] using hurs_bot
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  have h0 := congrFun he ⊥
  norm_num [actual, realize] at h0

def source_registration :
    Registration arena (type_of% @coarse_upper_sum_reduction_and_triangular_inversion) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨coarse_upper_sum_reduction_and_triangular_inversion, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩
      exact ⟨rejected, fun ⟨⟩ hj => (hj rfl).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@coarse_upper_sum_reduction_and_triangular_inversion)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement.Inversion.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement.Inversion.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "fn", "arg", "body", "body", "body", "arg", "arg", "body", "arg", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Inversion

namespace Bipartite

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => 2 * n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {N q : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2)), Γ.IsSymm →
    ∀ (col : Fin N → Fin q) {σ : PartyPartition q}, σ ∈ partitionsOfCard q 2 →
    ∀ {X Y : Finset (Fin q)}, σ.parts = {X, Y} → X ≠ Y →
    partitionRank Γ col σ = R.readout () () (offDiagBlock Γ col X Y).rank

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let G0 : Matrix (Fin 0) (Fin 0) (ZMod 2) := 0
  have hbot : (⊥ : PartyPartition 2) ∈ partitionsOfCard 2 2 := by simp [partitionsOfCard]
  have hb := @h 0 2 G0 Matrix.isSymm_zero Fin.elim0 ⊥ hbot {0} {1} bot2_parts
    singleton0_ne_singleton1
  have hr0 : partitionRank G0 Fin.elim0 (⊥ : PartyPartition 2) = 0 :=
    Nat.eq_zero_of_le_zero ((maskedAdj G0 Fin.elim0 ⊥).rank_le_card_width.trans (by simp))
  rw [hr0] at hb
  norm_num [rejected, realize] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration :
    Registration arena (type_of% @bipartite_masked_antidiagonal_rank) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bipartite_masked_antidiagonal_rank, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩
      exact ⟨rejected, fun ⟨⟩ hj => (hj rfl).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@bipartite_masked_antidiagonal_rank)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement.Bipartite.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement.Bipartite.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => 2 * n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Bipartite

end
end Reg.D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement
