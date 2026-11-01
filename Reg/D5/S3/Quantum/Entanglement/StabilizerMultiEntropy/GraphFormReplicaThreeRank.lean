import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphFormReplicaThreeRank
import Reg.Support.DependentFamily

/-! Four-slot source-bound registrations for graph-form replica-three rank sums. -/

namespace Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphFormReplicaThreeRank

open _root_.D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphFormReplicaThreeRank
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
open _root_.D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence
open _root_.D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open _root_.D5.S3.QuadraticForms.TernaryTranslationQuadraticNormalForm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

private local instance instDecidableRelKer {α β : Type} [DecidableEq β] (g : α → β) :
    DecidableRel (Setoid.ker g) :=
  fun x y => inferInstanceAs (Decidable (g x = g y))

private def Gamma0 : Matrix (Fin 0) (Fin 0) (ZMod 2) := 0

private def psi0 : (Fin 0 → Fin 2) → ℂ := graphState Gamma0

private theorem psi0_graphForm : IsGraphFormOf Gamma0 psi0 := by
  refine ⟨Matrix.isSymm_zero, fun u => Fin.elim0 u, Fin.elim0, 1,
    fun u => Fin.elim0 u, norm_one, ?_⟩
  funext x
  rw [one_smul]
  simp only [Matrix.mulVec, dotProduct, tensorOp, Matrix.of_apply, Finset.univ_eq_empty,
    Finset.prod_empty, one_mul]
  rw [Fintype.sum_unique]
  exact congrArg psi0 (Subsingleton.elim _ _)

private theorem psi0_norm : (∑ x : Fin 0 → Fin 2, ‖psi0 x‖ ^ 2) = 1 :=
  (graph_form_existence_and_replica_rank_formula.2.2 Gamma0 psi0 psi0_graphForm
    (Fin.elim0 : Fin 0 → Fin 1) ∅ (Finset.notMem_empty 0)
    (fun _ ht => False.elim (ht (funext fun i => Fin.elim0 i)))).1

private theorem bot2_parts :
    (⊥ : PartyPartition 2).parts = ({({0} : Finset (Fin 2)), {1}} : Finset (Finset (Fin 2))) := by
  ext s
  simp only [Finpartition.mem_bot_iff, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Fin.exists_fin_two, eq_comm]

private theorem singleton0_ne_singleton1 : ({0} : Finset (Fin 2)) ≠ {1} := by
  intro he
  have hm : (0 : Fin 2) ∈ ({1} : Finset (Fin 2)) := he ▸ Finset.mem_singleton_self 0
  simp at hm

namespace A

abbrev signature : Signature where
  Params := ℕ
  State N := (Fin N → Fin 2) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ N := (Fin N → Fin 2) → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ψ => ψ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∀ {N q : ℕ} (col : Fin N → Fin q) (ψ : (Fin N → Fin 2) → ℂ),
      (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1 → Z 1 q col (R.readout () N ψ) = 1) ∧
    (∀ {N : ℕ} (ψ : (Fin N → Fin 2) → ℂ),
      StabilizedBy pauliSet ψ → (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1 →
      ∃ Γ : Matrix (Fin N) (Fin N) (ZMod 2), IsGraphFormOf Γ ψ) ∧
    (∀ {N q : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2)) (ψ : (Fin N → Fin 2) → ℂ),
      IsGraphFormOf Γ ψ →
      ∀ (col : Fin N → Fin q) (P : Finset (Fin (q - 1) → ZMod 3)),
        (0 : Fin (q - 1) → ZMod 3) ∉ P →
        (∀ t : Fin (q - 1) → ZMod 3, t ≠ 0 → (t ∈ P ↔ -t ∉ P)) →
        (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1 ∧
        0 < (Z 3 q col ψ).re ∧ (Z 3 q col ψ).im = 0 ∧
        Z 3 q col ψ =
          ((2 : ℂ) ^ (∑ t : {t : Fin (q - 1) → ZMod 3 // t ∈ P},
            (C Γ (delta col) t.val).rank))⁻¹)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.1 (N := 0) (q := 1) Fin.elim0 psi0 psi0_norm
  rw [show rejected.readout () 0 psi0 = (fun _ => 0) from rfl, Z_one] at hb
  simp at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨0, 0, (fun _ => 1), ?_⟩
  intro he
  have h0 := congrFun he Fin.elim0
  change (0 : ℂ) = 1 at h0
  exact zero_ne_one h0

def src : Registration arena (type_of% @graph_form_existence_and_replica_rank_formula) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨graph_form_existence_and_replica_rank_formula, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩
      exact ⟨rejected, fun ⟨⟩ hj => (hj rfl).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@graph_form_existence_and_replica_rank_formula)
      (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphFormReplicaThreeRank.A.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphFormReplicaThreeRank.A.src
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨src⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ψ => ψ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphFormReplicaThreeRank
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end A

namespace B

abbrev signature : Signature where
  Params := ℕ
  State q := Fin (q - 1) → ZMod 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := Fin (q - 1) → ZMod 3
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∀ {q : ℕ} (t : Fin (q - 1) → ZMod 3), charPartition (-t) = charPartition (R.readout () q t)) ∧
    (∀ {q : ℕ}, 2 ≤ q → ∀ (P : Finset (Fin (q - 1) → ZMod 3)),
      (0 : Fin (q - 1) → ZMod 3) ∉ P →
      (∀ t : Fin (q - 1) → ZMod 3, t ≠ 0 → (t ∈ P ↔ -t ∉ P)) →
      Set.BijOn charPartition (P : Set (Fin (q - 1) → ZMod 3))
        (twoOrThreePartitions q : Set (PartyPartition q)) ∧
      (P.card : ℝ) = ((3 : ℝ) ^ (q - 1) - 1) / 2 ∧
      ((3 : ℝ) ^ (q - 1) - 1) / 2 =
        (Nat.stirlingSecond q 2 : ℝ) + (Nat.stirlingSecond q 3 : ℝ)) ∧
    (∀ {N q : ℕ}, 2 ≤ q → ∀ (Γ : Matrix (Fin N) (Fin N) (ZMod 2))
      (ψ : (Fin N → Fin 2) → ℂ), IsGraphFormOf Γ ψ → ∀ (col : Fin N → Fin q),
      S 3 q col ψ = (Real.log 2 / (2 * (3 : ℝ) ^ (q - 2))) *
        ∑ π ∈ twoOrThreePartitions q, (partitionRank Γ col π : ℝ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let t1 : Fin (2 - 1) → ZMod 3 := fun _ => 1
  have hb := h.1 (q := 2) t1
  simp only [rejected, realize] at hb
  have hm0 : (0 : Fin 2) ∈ (charPartition (0 : Fin (2 - 1) → ZMod 3)).part 1 := by
    rw [charPartition, Finpartition.mem_part_ofSetoid_iff_rel, Setoid.ker_def]
    decide
  have hm1 : (0 : Fin 2) ∉ (charPartition (-t1)).part 1 := by
    rw [charPartition, Finpartition.mem_part_ofSetoid_iff_rel, Setoid.ker_def]
    decide
  rw [← hb] at hm0
  exact hm1 hm0

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨2, 0, (fun _ => 1), ?_⟩
  intro he
  have h0 := congrFun he 0
  simp only [actual, realize] at h0
  exact (by decide : (0 : ZMod 3) ≠ 1) h0

def src : Registration arena (type_of% @replica_three_coarse_partition_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨replica_three_coarse_partition_sum, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩
      exact ⟨rejected, fun ⟨⟩ hj => (hj rfl).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@replica_three_coarse_partition_sum)
      (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphFormReplicaThreeRank.B.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphFormReplicaThreeRank.B.src
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨src⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphFormReplicaThreeRank
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end B

namespace C

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∀ {N q : ℕ}, 2 ≤ q → ∀ (ψ : (Fin N → Fin 2) → ℂ),
      StabilizedBy pauliSet ψ → (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1 →
      ∀ (col : Fin N → Fin q) (τ : Equiv.Perm (Fin q)),
        S 3 q (τ ∘ col) ψ = S 3 q col ψ) ∧
    (∀ {N q k : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2)) (ψ : (Fin N → Fin 2) → ℂ),
      IsGraphFormOf Γ ψ → ∀ (col : Fin N → Fin q) (π : PartyPartition q),
        2 ≤ π.parts.card → ∀ (B : Fin k ≃ π.parts),
          S 3 k (coarseCol π B col) ψ = coarseMultiEntropy π col ψ ∧
          coarseMultiEntropy π col ψ =
            (Real.log 2 / (2 * (3 : ℝ) ^ (π.parts.card - 2))) *
              ∑ σ ∈ (twoOrThreePartitions q).filter (fun σ => π ≤ σ),
                (partitionRank Γ col σ : ℝ)) ∧
    (∀ {N q : ℕ}, 2 ≤ q → ∀ (ψ : (Fin N → Fin 2) → ℂ),
      StabilizedBy pauliSet ψ → (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1 →
      ∀ (col : Fin N → Fin q),
        coarseMultiEntropy (⊥ : PartyPartition q) col ψ = S 3 q col ψ) ∧
    (∀ {N q : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2)) (ψ : (Fin N → Fin 2) → ℂ),
      IsGraphFormOf Γ ψ → ∀ (col : Fin N → Fin q) {σ : PartyPartition q},
        σ ∈ partitionsOfCard q 2 → ∀ {X Y : Finset (Fin q)},
          σ.parts = {X, Y} → X ≠ Y →
          coarseMultiEntropy σ col ψ =
            Real.log 2 * R.readout () () (offDiagBlock Γ col X Y).rank)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbot : (⊥ : PartyPartition 2) ∈ partitionsOfCard 2 2 := by simp [partitionsOfCard]
  have hb := @h.2.2.2 0 2 Gamma0 psi0 psi0_graphForm Fin.elim0 ⊥ hbot {0} {1}
    bot2_parts singleton0_ne_singleton1
  have ht := party_symmetry_coarse_graining_and_bipartite_entropy.2.2.2 Gamma0 psi0
    psi0_graphForm Fin.elim0 hbot bot2_parts singleton0_ne_singleton1
  have hr0 : (offDiagBlock Gamma0 (Fin.elim0 : Fin 0 → Fin 2) {0} {1}).rank = 0 :=
    Nat.eq_zero_of_le_zero
      ((offDiagBlock Gamma0 (Fin.elim0 : Fin 0 → Fin 2) {0} {1}).rank_le_card_width.trans
        (by simp))
  rw [ht, hr0] at hb
  simp only [rejected, realize, Nat.cast_zero, mul_zero, mul_one] at hb
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def src : Registration arena
    (type_of% @party_symmetry_coarse_graining_and_bipartite_entropy) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨party_symmetry_coarse_graining_and_bipartite_entropy, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩
      exact ⟨rejected, fun ⟨⟩ hj => (hj rfl).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@party_symmetry_coarse_graining_and_bipartite_entropy)
      (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphFormReplicaThreeRank.C.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphFormReplicaThreeRank.C.src
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨src⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphFormReplicaThreeRank
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end C

end
end Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphFormReplicaThreeRank
