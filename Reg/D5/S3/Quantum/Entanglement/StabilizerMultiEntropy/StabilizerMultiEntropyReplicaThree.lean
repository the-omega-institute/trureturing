import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.StabilizerMultiEntropyReplicaThree
import Reg.Support.DependentFamily

/-! Four-slot source-bound registrations for replica-three stabilizer multi-entropy reductions. -/

namespace Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.StabilizerMultiEntropyReplicaThree

open _root_.D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphFormReplicaThreeRank
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.StabilizerMultiEntropyReplicaThree
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
open _root_.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
open _root_.D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence
open _root_.D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open _root_.D5.S3.Quantum.FiniteDimensional
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

private def Gamma0 : Matrix (Fin 0) (Fin 0) (ZMod 2) := 0

private def psi0 : (Fin 0 → Fin 2) → ℂ := fun _ => 1

private theorem psi0_norm : (∑ x : Fin 0 → Fin 2, ‖psi0 x‖ ^ 2) = 1 := by
  simp [psi0, Finset.sum_const]

private theorem psi0_stab : StabilizedBy pauliSet psi0 := by
  refine ⟨?_, 0, Fin.elim0, fun a => Fin.elim0 a, fun w => ⟨fun _ => ?_, fun _ a => Fin.elim0 a⟩⟩
  · intro he
    have h0 := congrFun he Fin.elim0
    norm_num [psi0] at h0
  · refine ⟨w Fin.elim0, funext fun x => ?_⟩
    rw [Subsingleton.elim x Fin.elim0]
    simp [psi0]

private theorem psi0_graphForm : IsGraphFormOf Gamma0 psi0 := by
  refine ⟨Matrix.isSymm_zero, fun u => Fin.elim0 u, Fin.elim0, 1,
    fun u => Fin.elim0 u, norm_one, ?_⟩
  funext x
  rw [one_smul]
  simp only [Matrix.mulVec, dotProduct, tensorOp, Matrix.of_apply, Finset.univ_eq_empty,
    Finset.prod_empty, one_mul]
  rw [Fintype.sum_unique]
  simp [psi0, graphState, graphAmp,
    D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.normalExponent]

private theorem psi0_S_zero (q : ℕ) (hq : 2 ≤ q) (col : Fin 0 → Fin q) :
    S 3 q col psi0 = 0 := by
  rw [replica_three_coarse_partition_sum.2.2 hq Gamma0 psi0 psi0_graphForm col]
  have hr0 : ∀ π : PartyPartition q, partitionRank Gamma0 col π = 0 := fun π =>
    Nat.eq_zero_of_le_zero ((maskedAdj Gamma0 col π).rank_le_card_width.trans (by simp))
  simp [hr0]

private theorem psi0_coarse_zero {q : ℕ} (π : PartyPartition q) (hπ : 2 ≤ π.parts.card)
    (col : Fin 0 → Fin q) : coarseMultiEntropy π col psi0 = 0 :=
  psi0_S_zero π.parts.card hπ _

private def GammaBell : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 0]

private def psiBell : (Fin 2 → Fin 2) → ℂ := graphState GammaBell

private theorem psiBell_graphForm : IsGraphFormOf GammaBell psiBell := by
  refine ⟨by ext i j; fin_cases i <;> fin_cases j <;> decide,
    by intro u; fin_cases u <;> decide,
    fun _ => 1, 1, fun _ => one_mem _, norm_one, ?_⟩
  have htop : tensorOp (fun _ : Fin 2 => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    ext x y
    simp only [tensorOp, Matrix.of_apply, Matrix.one_apply, Fin.prod_univ_two]
    by_cases h0 : x 0 = y 0 <;> by_cases h1 : x 1 = y 1 <;>
      simp [h0, h1, funext_iff, Fin.forall_fin_two]
  rw [htop, Matrix.one_mulVec, one_smul]
  rfl

private theorem psiBell_norm : (∑ x : Fin 2 → Fin 2, ‖psiBell x‖ ^ 2) = 1 :=
  (graph_form_existence_and_replica_rank_formula.2.2 GammaBell psiBell psiBell_graphForm
    (fun _ => (0 : Fin 1)) ∅ (Finset.notMem_empty 0)
    (fun _ ht => False.elim (ht (funext fun i => Fin.elim0 i)))).1

private theorem psiBell_eval (a b : Fin 2) :
    psiBell ![a, b] = if a = 1 ∧ b = 1 then -(2 : ℂ)⁻¹ else (2 : ℂ)⁻¹ := by
  have hr : (((2 : ℝ) ^ (-(2 : ℝ) / 2) : ℝ) : ℂ) = (2 : ℂ)⁻¹ := by
    have hexp : -(2 : ℝ) / 2 = -1 := by norm_num
    rw [hexp, Real.rpow_neg_one]
    norm_num
  have hexp :
      (D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.normalExponent GammaBell
        (fun i : Fin 2 => ((![a, b] : Fin 2 → Fin 2) i : ZMod 2))).val =
        if a = 1 ∧ b = 1 then 1 else 0 := by
    fin_cases a <;> fin_cases b <;> decide
  have hamp : graphAmp GammaBell ![a, b] = if a = 1 ∧ b = 1 then -1 else 1 := by
    change (-1 : ℂ) ^
      (D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.normalExponent GammaBell
        (fun i : Fin 2 => ((![a, b] : Fin 2 → Fin 2) i : ZMod 2))).val = _
    rw [hexp]
    split_ifs <;> norm_num
  change (((2 : ℝ) ^ (-(2 : ℝ) / 2) : ℝ) : ℂ) * graphAmp GammaBell ![a, b] = _
  rw [hr, hamp]
  split_ifs <;> ring

private def bellOps : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![![pauliMatrix .X, pauliMatrix .Z], ![pauliMatrix .Z, pauliMatrix .X]]

private theorem sum_fin2_vec (f : (Fin 2 → Fin 2) → ℂ) :
    (∑ y : Fin 2 → Fin 2, f y) = f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1] := by
  let e : Fin 2 × Fin 2 ≃ (Fin 2 → Fin 2) :=
    { toFun := fun p => ![p.1, p.2]
      invFun := fun y => (y 0, y 1)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun y => by ext i; fin_cases i <;> rfl }
  have he : (∑ p : Fin 2 × Fin 2, f (e p)) = ∑ y : Fin 2 → Fin 2, f y := e.sum_comp f
  rw [← he, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  dsimp [e]
  ring

private theorem bellOp0_apply (w : (Fin 2 → Fin 2) → ℂ) :
    (tensorOp (bellOps 0) *ᵥ w) ![0, 0] = w ![1, 0] ∧
    (tensorOp (bellOps 0) *ᵥ w) ![0, 1] = -w ![1, 1] ∧
    (tensorOp (bellOps 0) *ᵥ w) ![1, 0] = w ![0, 0] ∧
    (tensorOp (bellOps 0) *ᵥ w) ![1, 1] = -w ![0, 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.mulVec, dotProduct, sum_fin2_vec, tensorOp, Matrix.of_apply,
      Fin.prod_univ_two, bellOps, pauliMatrix, qubitX, qubitZ, Matrix.cons_val_zero,
      Matrix.cons_val_one] <;>
    ring

private theorem bellOp1_apply (w : (Fin 2 → Fin 2) → ℂ) :
    (tensorOp (bellOps 1) *ᵥ w) ![0, 0] = w ![0, 1] ∧
    (tensorOp (bellOps 1) *ᵥ w) ![0, 1] = w ![0, 0] ∧
    (tensorOp (bellOps 1) *ᵥ w) ![1, 0] = -w ![1, 1] ∧
    (tensorOp (bellOps 1) *ᵥ w) ![1, 1] = -w ![1, 0] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.mulVec, dotProduct, sum_fin2_vec, tensorOp, Matrix.of_apply,
      Fin.prod_univ_two, bellOps, pauliMatrix, qubitX, qubitZ, Matrix.cons_val_zero,
      Matrix.cons_val_one] <;>
    ring

private theorem psiBell_stab : StabilizedBy pauliSet psiBell := by
  refine ⟨?_, 2, bellOps, ?_, fun w => ⟨?_, ?_⟩⟩
  · intro he
    have h00 := congrFun he ![0, 0]
    rw [psiBell_eval] at h00
    norm_num at h00
  · have hp : ∀ p, pauliMatrix p ∈ pauliSet :=
      fun p => ⟨1, Set.mem_insert 1 _, p, (one_smul _ _).symm⟩
    intro a i
    fin_cases a <;> fin_cases i <;> simpa [bellOps] using hp _
  · intro hw
    have hw0 := hw 0
    have hw1 := hw 1
    have e10 : w ![1, 0] = w ![0, 0] := (bellOp0_apply w).1.symm.trans (congrFun hw0 ![0, 0])
    have e01 : w ![0, 1] = w ![0, 0] := (bellOp1_apply w).1.symm.trans (congrFun hw1 ![0, 0])
    have e11' : -w ![1, 1] = w ![0, 1] := (bellOp0_apply w).2.1.symm.trans (congrFun hw0 ![0, 1])
    have e11 : w ![1, 1] = -w ![0, 0] := by rw [← neg_neg (w ![1, 1]), e11', e01]
    have h2 : (2 : ℂ) * (2 : ℂ)⁻¹ = 1 := by norm_num
    have hfin2 : ∀ u : Fin 2, u = 0 ∨ u = 1 := by decide
    have p00 : psiBell ![0, 0] = (2 : ℂ)⁻¹ := by rw [psiBell_eval]; norm_num
    have p01 : psiBell ![0, 1] = (2 : ℂ)⁻¹ := by rw [psiBell_eval]; norm_num
    have p10 : psiBell ![1, 0] = (2 : ℂ)⁻¹ := by rw [psiBell_eval]; norm_num
    have p11 : psiBell ![1, 1] = -(2 : ℂ)⁻¹ := by rw [psiBell_eval]; norm_num
    refine ⟨2 * w ![0, 0], funext fun x => ?_⟩
    have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
    rw [hx]
    rcases hfin2 (x 0) with h0 | h0 <;> rcases hfin2 (x 1) with h1 | h1
    · rw [h0, h1]; change w ![0, 0] = 2 * w ![0, 0] * psiBell ![0, 0]
      rw [p00]; linear_combination -w ![0, 0] * h2
    · rw [h0, h1, e01]; change w ![0, 0] = 2 * w ![0, 0] * psiBell ![0, 1]
      rw [p01]; linear_combination -w ![0, 0] * h2
    · rw [h0, h1, e10]; change w ![0, 0] = 2 * w ![0, 0] * psiBell ![1, 0]
      rw [p10]; linear_combination -w ![0, 0] * h2
    · rw [h0, h1, e11]; change -w ![0, 0] = 2 * w ![0, 0] * psiBell ![1, 1]
      rw [p11]; linear_combination w ![0, 0] * h2
  · rintro ⟨c, rfl⟩ a
    rw [Matrix.mulVec_smul]
    congr 1
    funext x
    have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
    rw [hx]
    fin_cases a
    · obtain ⟨h00, h01, h10, h11⟩ := bellOp0_apply psiBell
      rcases Fin.eq_zero_or_eq_succ (x 0) with r0 | ⟨j0, r0⟩ <;>
        rcases Fin.eq_zero_or_eq_succ (x 1) with r1 | ⟨j1, r1⟩
      · rw [r0, r1]; change (tensorOp (bellOps 0) *ᵥ psiBell) ![0, 0] = _
        rw [h00, psiBell_eval, psiBell_eval]; norm_num
      · fin_cases j1; rw [r0, r1]; change (tensorOp (bellOps 0) *ᵥ psiBell) ![0, 1] = _
        rw [h01, psiBell_eval, psiBell_eval]; norm_num
      · fin_cases j0; rw [r0, r1]; change (tensorOp (bellOps 0) *ᵥ psiBell) ![1, 0] = _
        rw [h10, psiBell_eval, psiBell_eval]; norm_num
      · fin_cases j0; fin_cases j1; rw [r0, r1]
        change (tensorOp (bellOps 0) *ᵥ psiBell) ![1, 1] = _
        rw [h11, psiBell_eval, psiBell_eval]; norm_num
    · obtain ⟨h00, h01, h10, h11⟩ := bellOp1_apply psiBell
      rcases Fin.eq_zero_or_eq_succ (x 0) with r0 | ⟨j0, r0⟩ <;>
        rcases Fin.eq_zero_or_eq_succ (x 1) with r1 | ⟨j1, r1⟩
      · rw [r0, r1]; change (tensorOp (bellOps 1) *ᵥ psiBell) ![0, 0] = _
        rw [h00, psiBell_eval, psiBell_eval]; norm_num
      · fin_cases j1; rw [r0, r1]; change (tensorOp (bellOps 1) *ᵥ psiBell) ![0, 1] = _
        rw [h01, psiBell_eval, psiBell_eval]; norm_num
      · fin_cases j0; rw [r0, r1]; change (tensorOp (bellOps 1) *ᵥ psiBell) ![1, 0] = _
        rw [h10, psiBell_eval, psiBell_eval]; norm_num
      · fin_cases j0; fin_cases j1; rw [r0, r1]
        change (tensorOp (bellOps 1) *ᵥ psiBell) ![1, 1] = _
        rw [h11, psiBell_eval, psiBell_eval]; norm_num

private theorem psiBell_S_pos : 0 < S 3 2 id psiBell := by
  rw [replica_three_coarse_partition_sum.2.2 (by decide : 2 ≤ 2)
    GammaBell psiBell psiBell_graphForm id]
  have hmask : maskedAdj GammaBell id (⊥ : PartyPartition 2) = GammaBell := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [maskedAdj, GammaBell]
    · have hne : (⊥ : PartyPartition 2).part 0 ≠ (⊥ : PartyPartition 2).part 1 := by
        rw [(⊥ : PartyPartition 2).part_eq_of_mem
            (Finpartition.mem_bot_iff.mpr ⟨0, Finset.mem_univ 0, rfl⟩)
            (Finset.mem_singleton_self 0),
          (⊥ : PartyPartition 2).part_eq_of_mem
            (Finpartition.mem_bot_iff.mpr ⟨1, Finset.mem_univ 1, rfl⟩)
            (Finset.mem_singleton_self 1)]
        intro he
        have hm : (0 : Fin 2) ∈ ({1} : Finset (Fin 2)) := he ▸ Finset.mem_singleton_self 0
        simp at hm
      simp [maskedAdj, hne]
    · have hne : (⊥ : PartyPartition 2).part 1 ≠ (⊥ : PartyPartition 2).part 0 := by
        rw [(⊥ : PartyPartition 2).part_eq_of_mem
            (Finpartition.mem_bot_iff.mpr ⟨1, Finset.mem_univ 1, rfl⟩)
            (Finset.mem_singleton_self 1),
          (⊥ : PartyPartition 2).part_eq_of_mem
            (Finpartition.mem_bot_iff.mpr ⟨0, Finset.mem_univ 0, rfl⟩)
            (Finset.mem_singleton_self 0)]
        intro he
        have hm : (1 : Fin 2) ∈ ({0} : Finset (Fin 2)) := he ▸ Finset.mem_singleton_self 1
        simp at hm
      simp [maskedAdj, hne]
    · simp [maskedAdj, GammaBell]
  have hsq : GammaBell * GammaBell = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  have hrank : 2 ≤ partitionRank GammaBell id (⊥ : PartyPartition 2) := by
    unfold partitionRank
    rw [hmask]
    have h1 := Matrix.rank_mul_le_left GammaBell GammaBell
    rw [hsq, Matrix.rank_one, Fintype.card_fin] at h1
    exact h1
  have hbot : (⊥ : PartyPartition 2) ∈ twoOrThreePartitions 2 := by
    simp [twoOrThreePartitions, partitionsOfCard]
  have hsum : (2 : ℝ) ≤ ∑ π ∈ twoOrThreePartitions 2, (partitionRank GammaBell id π : ℝ) :=
    le_trans (by exact_mod_cast hrank)
      (Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) hbot)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpref : 0 < Real.log 2 / (2 * (3 : ℝ) ^ (2 - 2)) := by norm_num; linarith
  exact mul_pos hpref (lt_of_lt_of_le (by norm_num) hsum)

namespace A

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => (3 : ℝ) * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {N q : ℕ}, 3 ≤ q → ∀ (ψ : (Fin N → Fin 2) → ℂ),
    StabilizedBy pauliSet ψ → (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1 →
    ∀ (col : Fin N → Fin q),
    S 3 q col ψ = (3 : ℝ) ^ (2 - (q : ℤ)) *
      (∑ π ∈ partitionsOfCard q 3, R.readout () () (coarseMultiEntropy π col ψ) +
       ∑ σ ∈ partitionsOfCard q 2,
         ((3 : ℝ) - ∑ B ∈ σ.parts, (2 : ℝ) ^ (B.card - 1)) * coarseMultiEntropy σ col ψ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := @h 0 3 le_rfl psi0 psi0_stab psi0_norm Fin.elim0
  rw [psi0_S_zero 3 (by decide) Fin.elim0] at hb
  have h2z : ∑ σ ∈ partitionsOfCard 3 2,
      ((3 : ℝ) - ∑ B ∈ σ.parts, (2 : ℝ) ^ (B.card - 1)) * coarseMultiEntropy σ Fin.elim0 psi0 =
      0 :=
    Finset.sum_eq_zero fun σ hσ => by
      have hc : σ.parts.card = 2 := (Finset.mem_filter.mp hσ).2
      rw [psi0_coarse_zero σ (by omega) Fin.elim0, mul_zero]
  have hcard3 : (partitionsOfCard 3 3).card = 1 := by
    rw [stirling_and_three_block_refinement_count.2.2.1 3 3, Nat.stirlingSecond_self]
  rw [h2z] at hb
  simp only [rejected, realize, Finset.sum_const, hcard3, nsmul_eq_mul, Nat.cast_one, one_mul,
    add_zero] at hb
  norm_num at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def src : Registration arena (type_of% @replica_three_two_and_three_party_reduction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨replica_three_two_and_three_party_reduction, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩
      exact ⟨rejected, fun ⟨⟩ hj => (hj rfl).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@replica_three_two_and_three_party_reduction)
      (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.StabilizerMultiEntropyReplicaThree.A.u
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.StabilizerMultiEntropyReplicaThree.A.src
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨src⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => (3 : ℝ) * x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner :=
      `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.StabilizerMultiEntropyReplicaThree
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end A

namespace B

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
  Law R := ∀ {q : ℕ}, 2 ≤ q → ∀ (c : PartyPartition q → ℝ),
    (∀ {N : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2)) (ψ : (Fin N → Fin 2) → ℂ),
      IsGraphFormOf Γ ψ → ∀ (col : Fin N → Fin q),
        ∑ ρ ∈ nontrivialPartitions q, c ρ * coarseMultiEntropy ρ col ψ =
          (Real.log 2 / 2) *
            ∑ σ ∈ twoOrThreePartitions q,
              coarseWeight c σ * R.readout () () (partitionRank Γ col σ)) ∧
    ((∀ σ ∈ twoOrThreePartitions q, coarseWeight c σ = 0) →
      ∀ {N : ℕ} (ψ : (Fin N → Fin 2) → ℂ),
        StabilizedBy pauliSet ψ → (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1 →
        ∀ (col : Fin N → Fin q),
          ∑ ρ ∈ nontrivialPartitions q, c ρ * coarseMultiEntropy ρ col ψ = 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let one2 : PartyPartition 2 → ℝ := fun _ => 1
  have hb := (@h 2 le_rfl one2).1 Gamma0 psi0 psi0_graphForm Fin.elim0
  have hlhs : ∑ ρ ∈ nontrivialPartitions 2, one2 ρ * coarseMultiEntropy ρ Fin.elim0 psi0 = 0 :=
    Finset.sum_eq_zero fun ρ hρ => by
      rw [psi0_coarse_zero ρ (Finset.mem_filter.mp hρ).2 Fin.elim0, mul_zero]
  rw [hlhs] at hb
  simp only [rejected, realize, mul_one] at hb
  let bot2 : PartyPartition 2 := ⊥
  have hcard : bot2.parts.card = 2 := by simp [bot2]
  have h23 : bot2 ∈ twoOrThreePartitions 2 := by
    simp [twoOrThreePartitions, partitionsOfCard, hcard]
  have hnt_le : bot2 ∈ (nontrivialPartitions 2).filter (fun ρ => ρ ≤ bot2) := by
    simp [nontrivialPartitions, hcard]
  have hcw_nonneg : ∀ σ : PartyPartition 2, 0 ≤ coarseWeight one2 σ := fun σ =>
    Finset.sum_nonneg fun _ _ => mul_nonneg (zpow_nonneg (by norm_num) _) (by norm_num [one2])
  have hcw_bot : 1 ≤ coarseWeight one2 bot2 := by
    unfold coarseWeight
    have hs := Finset.single_le_sum
      (f := fun ρ : PartyPartition 2 => (3 : ℝ) ^ (2 - (ρ.parts.card : ℤ)) * one2 ρ)
      (fun _ _ => mul_nonneg (zpow_nonneg (by norm_num) _) (by norm_num [one2])) hnt_le
    simpa [one2, hcard] using hs
  have hsum : 1 ≤ ∑ σ ∈ twoOrThreePartitions 2, coarseWeight one2 σ :=
    le_trans hcw_bot (Finset.single_le_sum (fun σ _ => hcw_nonneg σ) h23)
  have hlog : 0 < Real.log 2 / 2 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hrhs : 0 < (Real.log 2 / 2) * ∑ σ ∈ twoOrThreePartitions 2, coarseWeight one2 σ :=
    mul_pos hlog (lt_of_lt_of_le zero_lt_one hsum)
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def src : Registration arena
    (type_of% @coarse_linear_combination_and_vanishing_criterion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨coarse_linear_combination_and_vanishing_criterion, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩
      exact ⟨rejected, fun ⟨⟩ hj => (hj rfl).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@coarse_linear_combination_and_vanishing_criterion)
      (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.StabilizerMultiEntropyReplicaThree.B.u
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.StabilizerMultiEntropyReplicaThree.B.src
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
    owner :=
      `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.StabilizerMultiEntropyReplicaThree
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "body", "body",
        "body", "body", "arg", "arg", "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end B

namespace C

abbrev signature : Signature where
  Params := ℕ
  State N' := (Fin N' → Fin 2) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ N' := (Fin N' → Fin 2) → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ψ' => ψ') (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {N N' q : ℕ}, 2 ≤ q →
    ∀ (ψ : (Fin N → Fin 2) → ℂ) (ψ' : (Fin N' → Fin 2) → ℂ),
    StabilizedBy pauliSet ψ → (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1 →
    StabilizedBy pauliSet ψ' → (∑ x : Fin N' → Fin 2, ‖ψ' x‖ ^ 2) = 1 →
    ∀ (col : Fin N → Fin q) (col' : Fin N' → Fin q),
    (∀ σ ∈ partitionsOfCard q 2,
      coarseMultiEntropy σ col ψ = coarseMultiEntropy σ col' ψ') →
    (∀ π ∈ partitionsOfCard q 3,
      coarseMultiEntropy π col ψ = coarseMultiEntropy π col' ψ') →
    (∀ ρ ∈ nontrivialPartitions q,
      coarseMultiEntropy ρ col ψ = coarseMultiEntropy ρ col' ψ') ∧
    S 3 q col ψ = S 3 q col' (R.readout () N' ψ')

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (@h 2 2 2 le_rfl psiBell psiBell psiBell_stab psiBell_norm
    psiBell_stab psiBell_norm id id (fun _ _ => rfl) (fun _ _ => rfl)).2
  have hs0 : S 3 2 id (0 : (Fin 2 → Fin 2) → ℂ) = 0 := by
    simp [S, Z_one]
  simp only [rejected, realize, hs0] at hb
  linarith [psiBell_S_pos]

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨0, 0, (fun _ => 1), ?_⟩
  intro he
  have h0 := congrFun he Fin.elim0
  change (0 : ℂ) = 1 at h0
  exact zero_ne_one h0

def src : Registration arena
    (type_of% @coarse_two_three_data_determine_replica_three_multi_entropies) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨coarse_two_three_data_determine_replica_three_multi_entropies, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩
      exact ⟨rejected, fun ⟨⟩ hj => (hj rfl).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@coarse_two_three_data_determine_replica_three_multi_entropies)
      (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.StabilizerMultiEntropyReplicaThree.C.u
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.StabilizerMultiEntropyReplicaThree.C.src
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨src⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ψ' => ψ') (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner :=
      `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.StabilizerMultiEntropyReplicaThree
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end C

end
end Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.StabilizerMultiEntropyReplicaThree
