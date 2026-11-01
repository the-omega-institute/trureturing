/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphFormReplicaThreeRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Graph-form replica-three rank sum over two- and three-block party partitions. -/

import D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement
import D5.S3.Combinatorics.Partitions.TernaryPartitionOrbit
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Replica-three stabilizer multi-entropy via graph forms and coarse party partitions
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphFormReplicaThreeRank

open scoped BigOperators
open Matrix
open D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement
open D5.S3.Combinatorics.Partitions.TernaryPartitionOrbit
open D5.S3.QuadraticForms.TernaryTranslationQuadraticNormalForm
open D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse

private local instance instDecidableRelSetoidKer {α β : Type} [DecidableEq β] (g : α → β) :
    DecidableRel (Setoid.ker g) :=
  fun x y ↦ inferInstanceAs (Decidable (g x = g y))

/-- Normalized `N`-qubit graph state `|Γ⟩ = 2^{-N/2} ∑_x (-1)^{∑_{u < v} Γ_{uv} x_u x_v} |x⟩`. -/
def graphState {N : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2)) : (Fin N → Fin 2) → ℂ :=
  ((((2 : ℝ) ^ (-(N : ℝ) / 2) : ℝ) : ℂ)) • graphAmp Γ

/-- Predicate asserting that `Γ` is a symmetric zero-diagonal graph form of the pure state `ψ`
up to single-qubit unitaries and a unit-modulus global phase. -/
def IsGraphFormOf {N : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2))
    (ψ : (Fin N → Fin 2) → ℂ) : Prop :=
  Γ.IsSymm ∧ (∀ u : Fin N, Γ u u = 0) ∧
    ∃ (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ) (lam : ℂ),
      (∀ u : Fin N, U u ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
      ‖lam‖ = 1 ∧ ψ = lam • (tensorOp U *ᵥ graphState Γ)

/-- Standard replica translation vector `δ_c ∈ (ℤ/3)^{q-1}`, zero on the last party. -/
def partyDelta {q : ℕ} (c : Fin q) : Fin (q - 1) → ZMod 3 :=
  fun i ↦ if (i : ℕ) = (c : ℕ) then 1 else 0

/-- Evaluation `f_t(c) = t · δ_c` of a ternary replica character `t` on party `c`. -/
def charEval {q : ℕ} (t : Fin (q - 1) → ZMod 3) (c : Fin q) : ZMod 3 :=
  ∑ i : Fin (q - 1), t i * partyDelta c i

/-- Partition `π_t` of the `q` parties into the nonempty fibres of `charEval t`. -/
def charPartition {q : ℕ} (t : Fin (q - 1) → ZMod 3) : PartyPartition q :=
  Finpartition.ofSetoid (Setoid.ker (charEval t))

/-- Replica-three multi-entropy `S_3^{(|π|)}(π)` of a state `ψ` coarse-grained along `π`. -/
def coarseMultiEntropy {N q : ℕ} (π : PartyPartition q) (col : Fin N → Fin q)
    (ψ : (Fin N → Fin 2) → ℂ) : ℝ :=
  S 3 π.parts.card (coarseCol π π.parts.equivFin.symm col) ψ

private lemma rpow_neg_half_sq (N : ℕ) :
    ((2 : ℝ) ^ (-(N : ℝ) / 2)) ^ 2 = ((2 : ℝ) ^ N)⁻¹ := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(N : ℝ) / 2)) 2,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hexp : -(N : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(N : ℝ) := by norm_num
  rw [hexp, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]

private lemma graphForm_scalar_rewrite {N : ℕ} {Γ : Matrix (Fin N) (Fin N) (ZMod 2)}
    {ψ : (Fin N → Fin 2) → ℂ} (hΓψ : IsGraphFormOf Γ ψ) :
    ∃ (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ),
      (∀ u, U u ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
      star c * c = ((2 : ℂ) ^ N)⁻¹ ∧ ψ = c • (tensorOp U *ᵥ graphAmp Γ) := by
  obtain ⟨_, _, U, lam, hU, hlam, hψ⟩ := hΓψ
  let r : ℝ := (2 : ℝ) ^ (-(N : ℝ) / 2)
  refine ⟨U, lam * (r : ℂ), hU, ?_, by rw [hψ, graphState, Matrix.mulVec_smul, smul_smul]⟩
  have hlam' : star lam * lam = 1 := by
    simpa only [Complex.star_def, hlam, one_pow, Complex.ofReal_one] using Complex.conj_mul' lam
  have hr : (r : ℂ) * (r : ℂ) = ((2 : ℂ) ^ N)⁻¹ := by
    simpa [sq] using congrArg Complex.ofReal (rpow_neg_half_sq N)
  calc star (lam * (r : ℂ)) * (lam * (r : ℂ))
      = (star lam * lam) * ((r : ℂ) * (r : ℂ)) := by simp [Complex.conj_ofReal]; ring
    _ = ((2 : ℂ) ^ N)⁻¹ := by rw [hlam', one_mul, hr]

/-- Normalization at replica one, existence of a graph form for every normalized pure qubit
stabilizer state, and the positive-real replica-three contraction rank formula on graph forms. -/
theorem graph_form_existence_and_replica_rank_formula :
    (∀ {N q : ℕ} (col : Fin N → Fin q) (ψ : (Fin N → Fin 2) → ℂ),
      (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1 → Z 1 q col ψ = 1) ∧
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
            (C Γ (delta col) t.val).rank))⁻¹) := by
  refine ⟨fun col ψ hn ↦ by rw [Z_one, hn, Complex.ofReal_one], ?_, ?_⟩
  · intro N ψ hstab hn
    obtain ⟨U, Γ, c, hU, hsymm, hdiag, hψ⟩ := stabilizer_graph_normal_form ψ hstab
    have hc : star c * c = ((2 : ℂ) ^ N)⁻¹ :=
      graph_scalar_norm Γ U hU c (by simpa only [← hψ] using hn)
    let r : ℝ := (2 : ℝ) ^ (-(N : ℝ) / 2)
    have hrpos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
    have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
    have hnormc : ‖c‖ = r := by
      have h1 : (((‖c‖ ^ 2 : ℝ)) : ℂ) = star c * c := by
        simpa only [Complex.ofReal_pow, starRingEnd_apply] using (Complex.conj_mul' c).symm
      have h2 : ‖c‖ ^ 2 = r ^ 2 :=
        (Complex.ofReal_injective (by simpa using h1.trans hc)).trans (rpow_neg_half_sq N).symm
      nlinarith [norm_nonneg c, hrpos]
    let lam : ℂ := (r : ℂ)⁻¹ * c
    have hlam : ‖lam‖ = 1 := by
      simp only [lam, norm_mul, norm_inv, Complex.norm_of_nonneg hrpos.le, hnormc]
      exact inv_mul_cancel₀ hrpos.ne'
    refine ⟨Γ, hsymm, hdiag, U, lam, hU, hlam, ?_⟩
    rw [hψ, graphState, Matrix.mulVec_smul, smul_smul]; congr 1
    dsimp only [lam]; rw [mul_comm ((r : ℂ)⁻¹) c, mul_assoc, inv_mul_cancel₀ hrne, mul_one]
  · intro N q Γ ψ hΓψ col P h0 hP
    obtain ⟨U, c, hU, hc, hψ⟩ := graphForm_scalar_rewrite hΓψ
    have hnorm : (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1 := by
      have hz1 : Z 1 1 (fun _ ↦ 0) ψ = 1 := by
        rw [hψ, Z_local_scalar 1 1 (fun _ ↦ 0) (graphAmp Γ) U hU c, Z_smul, hc]
        simp only [one_pow, pow_one, Z_one]
        have hgn : (∑ x : Fin N → Fin 2, ‖graphAmp Γ x‖ ^ 2) = (2 : ℝ) ^ N := by
          classical
          simp [graphAmp.eq_1, norm_pow]
        rw [hgn, Complex.ofReal_pow, Complex.ofReal_ofNat]
        exact inv_mul_cancel₀ (pow_ne_zero N (by norm_num))
      rw [Z_one] at hz1; exact Complex.ofReal_injective (by simpa using hz1)
    have hZ3 : Z 3 q col ψ = ((2 : ℂ) ^ (∑ t : {t : Fin (q - 1) → ZMod 3 // t ∈ P},
        (C Γ (delta col) t.val).rank))⁻¹ := by
      rw [hψ, Z_local_scalar 3 q col (graphAmp Γ) U hU c, Z_smul, hc]
      exact graph_count Γ (fun u v ↦ (hΓψ.1.apply u v).symm) col P h0 hP
    refine ⟨hnorm, ?_, ?_, hZ3⟩
    · rw [hZ3, ← Complex.ofReal_ofNat, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
        Complex.ofReal_re]; positivity
    · rw [hZ3, ← Complex.ofReal_ofNat, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
        Complex.ofReal_im]

private lemma partyPartition_eq_iff {q : ℕ} {P₁ P₂ : PartyPartition q} :
    P₁ = P₂ ↔ ∀ a b : Fin q, P₁.part a = P₁.part b ↔ P₂.part a = P₂.part b := by
  refine ⟨fun h _ _ ↦ h ▸ Iff.rfl, fun h ↦ Finpartition.ext (Finset.ext fun B ↦ ?_)⟩
  have hpart : ∀ a : Fin q, P₁.part a = P₂.part a := fun a ↦ Finset.ext fun b ↦ by
    rw [P₁.mem_part_iff_part_eq_part (Finset.mem_univ b) (Finset.mem_univ a), h b a,
      ← P₂.mem_part_iff_part_eq_part (Finset.mem_univ b) (Finset.mem_univ a)]
  have hmem : ∀ P : PartyPartition q, B ∈ P.parts ↔ ∃ a : Fin q, P.part a = B := fun P ↦
    ⟨fun hB ↦ ⟨(P.nonempty_of_mem_parts hB).choose,
        P.part_eq_of_mem hB (P.nonempty_of_mem_parts hB).choose_spec⟩,
     fun ⟨a, ha⟩ ↦ ha ▸ P.part_mem.mpr (Finset.mem_univ a)⟩
  rw [hmem P₁, hmem P₂]; exact exists_congr fun a ↦ by rw [hpart a]

private lemma ofSetoid_ker_part_eq {q : ℕ} {β : Type} [DecidableEq β]
    (g : Fin q → β) (a b : Fin q) :
    (Finpartition.ofSetoid (Setoid.ker g)).part a =
      (Finpartition.ofSetoid (Setoid.ker g)).part b ↔ g a = g b := by
  rw [← (Finpartition.ofSetoid (Setoid.ker g)).mem_part_iff_part_eq_part
      (Finset.mem_univ a) (Finset.mem_univ b),
    Finpartition.mem_part_ofSetoid_iff_rel, Setoid.ker_def, eq_comm]

private lemma card_parts_ofSetoid_ker {q : ℕ} {β : Type} [DecidableEq β] (g : Fin q → β) :
    (Finpartition.ofSetoid (Setoid.ker g)).parts.card =
      ((Finset.univ : Finset (Fin q)).image g).card := by
  let P : PartyPartition q := Finpartition.ofSetoid (Setoid.ker g)
  refine Finset.card_bij (fun B hB ↦ g (P.nonempty_of_mem_parts hB).choose)
    (fun _ _ ↦ Finset.mem_image_of_mem g (Finset.mem_univ _))
    (fun B₁ h₁ B₂ h₂ heq ↦ ?_) (fun y hy ↦ ?_)
  · have hp := (ofSetoid_ker_part_eq g _ _).mpr heq
    rwa [P.part_eq_of_mem h₁ (P.nonempty_of_mem_parts h₁).choose_spec,
      P.part_eq_of_mem h₂ (P.nonempty_of_mem_parts h₂).choose_spec] at hp
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hy
    have hB : P.part a ∈ P.parts := P.part_mem.mpr (Finset.mem_univ a)
    exact ⟨P.part a, hB, (ofSetoid_ker_part_eq g _ a).mp
      (P.part_eq_of_mem hB (P.nonempty_of_mem_parts hB).choose_spec)⟩

private lemma charEval_lt {q : ℕ} (t : Fin (q - 1) → ZMod 3) {c : Fin q}
    (hc : (c : ℕ) < q - 1) : charEval t c = t ⟨c.1, hc⟩ := by
  unfold charEval partyDelta
  rw [Finset.sum_eq_single ⟨c.1, hc⟩]
  · simp
  · intro i _ hne; simp [show (i : ℕ) ≠ (c : ℕ) from fun h ↦ hne (Fin.ext h)]
  · intro h; exact False.elim (h (Finset.mem_univ _))

private lemma charEval_last {q : ℕ} (t : Fin (q - 1) → ZMod 3) {c : Fin q}
    (hc : (c : ℕ) = q - 1) : charEval t c = 0 := by
  unfold charEval partyDelta
  exact Finset.sum_eq_zero fun i _ ↦ by simp [show (i : ℕ) ≠ (c : ℕ) by omega]

private def optFinEquiv {q : ℕ} (hq : 1 ≤ q) : Option (Fin (q - 1)) ≃ Fin q where
  toFun | none => ⟨q - 1, by omega⟩ | some i => ⟨i.1, by omega⟩
  invFun c := if h : (c : ℕ) < q - 1 then some ⟨c.1, h⟩ else none
  left_inv x := by cases x with | none => simp | some i => simp [i.isLt]
  right_inv c := by
    by_cases h : (c : ℕ) < q - 1
    · simp [h]
    · have hc : (c : ℕ) = q - 1 := by omega
      ext; simp [hc]

private lemma charEval_eq_anchored {q : ℕ} (hq : 1 ≤ q)
    (t : Fin (q - 1) → ZMod 3) (c : Fin q) :
    charEval t c = anchored t ((optFinEquiv hq).symm c) := by
  by_cases h : (c : ℕ) < q - 1
  · simp [optFinEquiv, h, anchored, charEval_lt t h]
  · have hc : (c : ℕ) = q - 1 := by omega
    simp [optFinEquiv, h, anchored, charEval_last t hc]

private lemma charPartition_eq_iff_samePartition {q : ℕ} (hq : 1 ≤ q)
    (t₁ t₂ : Fin (q - 1) → ZMod 3) :
    charPartition t₁ = charPartition t₂ ↔ SamePartition (anchored t₁) (anchored t₂) := by
  rw [partyPartition_eq_iff]; simp_rw [charPartition, ofSetoid_ker_part_eq, charEval_eq_anchored hq]
  exact ⟨fun h x y ↦ by
      simpa only [Equiv.symm_apply_apply] using h (optFinEquiv hq x) (optFinEquiv hq y),
    fun h a b ↦ h ((optFinEquiv hq).symm a) ((optFinEquiv hq).symm b)⟩

private lemma C_eq_maskedAdj {N q : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2))
    (col : Fin N → Fin q) (t : Fin (q - 1) → ZMod 3) :
    C Γ (delta col) t = maskedAdj Γ col (charPartition t) := by
  ext u v
  change (if charEval t (col u) = charEval t (col v) then 0 else Γ u v) =
    if (charPartition t).part (col u) = (charPartition t).part (col v) then 0 else Γ u v
  simp only [charPartition, ofSetoid_ker_part_eq]

/-- Opposite nonzero replica characters biject onto party partitions into two or three blocks,
yielding the Stirling counting identity and the coarse-partition rank sum for `S_3^{(q)}`. -/
theorem replica_three_coarse_partition_sum :
    (∀ {q : ℕ} (t : Fin (q - 1) → ZMod 3), charPartition (-t) = charPartition t) ∧
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
        ∑ π ∈ twoOrThreePartitions q, (partitionRank Γ col π : ℝ)) := by
  have hneg : ∀ {q : ℕ} (t : Fin (q - 1) → ZMod 3), charPartition (-t) = charPartition t := by
    intro q t; rw [partyPartition_eq_iff]; intro a b
    simp_rw [charPartition, ofSetoid_ker_part_eq]
    have hev : ∀ c : Fin q, charEval (-t) c = -charEval t c := fun c ↦ by
      simp [charEval, neg_mul, Finset.sum_neg_distrib]
    rw [hev a, hev b]; exact neg_inj
  have hbij_count : ∀ {q : ℕ}, 2 ≤ q → ∀ (P : Finset (Fin (q - 1) → ZMod 3)),
      (0 : Fin (q - 1) → ZMod 3) ∉ P →
      (∀ t : Fin (q - 1) → ZMod 3, t ≠ 0 → (t ∈ P ↔ -t ∉ P)) →
      Set.BijOn charPartition (P : Set (Fin (q - 1) → ZMod 3))
        (twoOrThreePartitions q : Set (PartyPartition q)) ∧
      (P.card : ℝ) = ((3 : ℝ) ^ (q - 1) - 1) / 2 ∧
      ((3 : ℝ) ^ (q - 1) - 1) / 2 =
        (Nat.stirlingSecond q 2 : ℝ) + (Nat.stirlingSecond q 3 : ℝ) := by
    intro q hq P h0 hP
    have hq1 : 1 ≤ q := by omega
    have hmaps : Set.MapsTo charPartition (P : Set (Fin (q - 1) → ZMod 3))
        (twoOrThreePartitions q : Set (PartyPartition q)) := by
      intro t htP
      obtain ⟨i, hi⟩ := Function.ne_iff.mp (show t ≠ 0 from fun h ↦ h0 (h ▸ htP))
      have hcard := card_parts_ofSetoid_ker (charEval t)
      have hle3 : ((Finset.univ : Finset (Fin q)).image (charEval t)).card ≤ 3 := by
        simpa [ZMod.card] using
          Finset.card_le_univ ((Finset.univ : Finset (Fin q)).image (charEval t))
      let c₁ : Fin q := ⟨i.1, by omega⟩
      let c₀ : Fin q := ⟨q - 1, by omega⟩
      have hsub : ({0, t i} : Finset (ZMod 3)) ⊆ Finset.univ.image (charEval t) := by
        intro z hz; rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact (charEval_last t (c := c₀) rfl) ▸
            Finset.mem_image_of_mem _ (Finset.mem_univ c₀)
        · exact (charEval_lt t (c := c₁) i.isLt) ▸
            Finset.mem_image_of_mem _ (Finset.mem_univ c₁)
      have hge2 : 2 ≤ ((Finset.univ : Finset (Fin q)).image (charEval t)).card :=
        Finset.card_pair hi.symm ▸ Finset.card_le_card hsub
      change charPartition t ∈ twoOrThreePartitions q
      simp only [twoOrThreePartitions, partitionsOfCard, Finset.mem_union,
        Finset.mem_filter, Finset.mem_univ, true_and]
      change (Finpartition.ofSetoid (Setoid.ker (charEval t))).parts.card = 2 ∨
        (Finpartition.ofSetoid (Setoid.ker (charEval t))).parts.card = 3; omega
    have hinj : Set.InjOn charPartition (P : Set (Fin (q - 1) → ZMod 3)) := by
      intro t₁ ht₁ t₂ ht₂ heq
      have huniq := D5.S3.Combinatorics.Partitions.TernaryPartitionOrbit.result
        (P : Set (Fin (q - 1) → ZMod 3)) hP t₁ (fun h ↦ h0 (h ▸ ht₁))
      exact (huniq.unique ⟨ht₂, (charPartition_eq_iff_samePartition hq1 t₁ t₂).mp heq⟩
        ⟨ht₁, fun _ _ ↦ Iff.rfl⟩).symm
    have hsurj : Set.SurjOn charPartition (P : Set (Fin (q - 1) → ZMod 3))
        (twoOrThreePartitions q : Set (PartyPartition q)) := by
      intro π hπ
      let c₀ : Fin q := ⟨q - 1, by omega⟩
      let B₀ : Finset (Fin q) := π.part c₀
      have hB₀ : B₀ ∈ π.parts := π.part_mem.mpr (Finset.mem_univ c₀)
      let rem := π.parts.erase B₀
      have hπcard : π.parts.card = 2 ∨ π.parts.card = 3 := by
        simpa [twoOrThreePartitions, partitionsOfCard] using hπ
      have hrem_eq : rem.card = π.parts.card - 1 := Finset.card_erase_of_mem hB₀
      have hrem_card : rem.card = 1 ∨ rem.card = 2 := by omega
      let eRem := rem.equivFin
      let nzVal : Fin rem.card → ZMod 3 := fun j ↦ if (j : ℕ) = 0 then 1 else 2
      have hnz_ne : ∀ j : Fin rem.card, nzVal j ≠ 0 := fun j ↦ by
        dsimp [nzVal]; split_ifs <;> decide
      have hnz_inj : Function.Injective nzVal := by
        intro j₁ j₂ hj; dsimp [nzVal] at hj
        by_cases h1 : (j₁ : ℕ) = 0 <;> by_cases h2 : (j₂ : ℕ) = 0
        · exact Fin.ext (h1.trans h2.symm)
        · simp only [h1, h2, ↓reduceIte] at hj
          exact False.elim ((by decide : (1 : ZMod 3) ≠ 2) hj)
        · simp only [h1, h2, ↓reduceIte] at hj
          exact False.elim ((by decide : (2 : ZMod 3) ≠ 1) hj)
        · have := j₁.isLt; have := j₂.isLt; exact Fin.ext (by omega)
      let f : Fin q → ZMod 3 := fun c ↦
        if h : π.part c = B₀ then 0
        else nzVal (eRem ⟨π.part c, Finset.mem_erase.mpr ⟨h, π.part_mem.mpr (Finset.mem_univ c)⟩⟩)
      have hf₀ : f c₀ = 0 := by simp [f, B₀]
      have hf_ker : ∀ a b : Fin q, f a = f b ↔ π.part a = π.part b := fun a b ↦ by
        refine ⟨fun hab ↦ ?_, fun hab ↦ ?_⟩
        · dsimp [f] at hab
          by_cases ha : π.part a = B₀ <;> by_cases hb : π.part b = B₀
          · exact ha.trans hb.symm
          · simp only [ha, hb, ↓reduceDIte] at hab; exact False.elim (hnz_ne _ hab.symm)
          · simp only [ha, hb, ↓reduceDIte] at hab; exact False.elim (hnz_ne _ hab)
          · simp only [ha, hb, ↓reduceDIte] at hab
            exact congrArg Subtype.val (eRem.injective (hnz_inj hab))
        · dsimp [f]
          by_cases ha : π.part a = B₀
          · have hb : π.part b = B₀ := hab.symm.trans ha
            simp only [ha, hb, ↓reduceDIte]
          · have hb : π.part b ≠ B₀ := fun h ↦ ha (hab.trans h)
            simp only [ha, hb, ↓reduceDIte]; congr 2; exact Subtype.ext hab
      let u : Fin (q - 1) → ZMod 3 := fun i ↦ f ⟨i.1, by omega⟩
      have hchar_u : ∀ c : Fin q, charEval u c = f c := fun c ↦ by
        by_cases hc : (c : ℕ) < q - 1
        · exact charEval_lt u hc
        · have heq : c = c₀ := Fin.ext (by dsimp [c₀]; omega)
          rw [heq, charEval_last u rfl, hf₀]
      have hu_ne : u ≠ 0 := by
        obtain ⟨B₁, hB₁⟩ := (Finset.card_pos.mp (by omega) : rem.Nonempty)
        obtain ⟨c₁, hc₁B⟩ := π.nonempty_of_mem_parts (Finset.mem_of_mem_erase hB₁)
        have hneB₀ : π.part c₁ ≠ B₀ :=
          (π.part_eq_of_mem (Finset.mem_of_mem_erase hB₁) hc₁B).symm ▸ (Finset.mem_erase.mp hB₁).1
        have hfc₁ : f c₁ ≠ 0 := by simp only [f, hneB₀, ↓reduceDIte]; exact hnz_ne _
        have hlt₁ : (c₁ : ℕ) < q - 1 := by
          by_contra hnlt
          exact hfc₁ ((Fin.ext (by dsimp [c₀]; omega) : c₁ = c₀) ▸ hf₀)
        exact fun hu0 ↦ hfc₁ (congrFun hu0 ⟨c₁.1, hlt₁⟩)
      have hπu : charPartition u = π := partyPartition_eq_iff.mpr fun a b ↦ by
        rw [charPartition, ofSetoid_ker_part_eq, hchar_u a, hchar_u b, hf_ker a b]
      obtain ⟨v, ⟨hvP, hsame⟩, _⟩ := D5.S3.Combinatorics.Partitions.TernaryPartitionOrbit.result
        (P : Set (Fin (q - 1) → ZMod 3)) hP u hu_ne
      exact ⟨v, hvP, hπu ▸ ((charPartition_eq_iff_samePartition hq1 u v).mpr hsame).symm⟩
    have hbij : Set.BijOn charPartition (P : Set (Fin (q - 1) → ZMod 3))
        (twoOrThreePartitions q : Set (PartyPartition q)) := ⟨hmaps, hinj, hsurj⟩
    have hPcard : P.card = (twoOrThreePartitions q).card :=
      Finset.card_bij (fun t _ ↦ charPartition t)
        (fun t ht ↦ hmaps ht) (fun _ h₁ _ h₂ ↦ hinj h₁ h₂)
        (fun π hπ ↦ let ⟨t, ht, heq⟩ := hsurj hπ; ⟨t, ht, heq⟩)
    have hstirl := stirling_and_three_block_refinement_count
    have hdisj : Disjoint (partitionsOfCard q 2) (partitionsOfCard q 3) :=
      Finset.disjoint_left.mpr fun _ h₁ h₂ ↦ by
        have c1 := (Finset.mem_filter.mp h₁).2; have c2 := (Finset.mem_filter.mp h₂).2; omega
    have h23card : (twoOrThreePartitions q).card =
        Nat.stirlingSecond q 2 + Nat.stirlingSecond q 3 := by
      rw [twoOrThreePartitions, Finset.card_union_of_disjoint hdisj,
        hstirl.2.2.1 q 2, hstirl.2.2.1 q 3]
    have hhalf := (hstirl.2.1 hq1).2
    refine ⟨hbij, ?_, hhalf⟩; rw [hPcard, h23card, Nat.cast_add, hhalf]
  refine ⟨hneg, hbij_count, fun hq Γ ψ hΓψ col ↦ ?_⟩
  obtain ⟨P, h0, hP⟩ := representatives_exist ( _ - 1)
  have hrep := graph_form_existence_and_replica_rank_formula.2.2 Γ ψ hΓψ col P h0 hP
  rw [entropy_formula ψ hrep.1 _ col Γ P hrep.2.2.2]; congr 1
  have hbij := (hbij_count hq P h0 hP).1
  refine Finset.sum_bij (fun t _ ↦ charPartition t)
    (fun t ht ↦ hbij.mapsTo ht) (fun _ h₁ _ h₂ ↦ hbij.injOn h₁ h₂)
    (fun π hπ ↦ let ⟨t, ht, heq⟩ := hbij.surjOn hπ; ⟨t, ht, heq⟩)
    (fun t _ ↦ by unfold partitionRank; rw [C_eq_maskedAdj])

private def pullPartyPartition {q k : ℕ} (m : Fin q → Fin k)
    (ρ : PartyPartition k) : PartyPartition q :=
  Finpartition.ofSetoid (Setoid.ker (fun c : Fin q ↦ ρ.part (m c)))

private lemma pullPartyPartition_bijOn {q k : ℕ} (m : Fin q → Fin k)
    (hm : Function.Surjective m) :
    let π₀ : PartyPartition q := Finpartition.ofSetoid (Setoid.ker m)
    Set.BijOn (pullPartyPartition m)
      (twoOrThreePartitions k : Set (PartyPartition k))
      (((twoOrThreePartitions q).filter (fun σ ↦ π₀ ≤ σ) : Finset (PartyPartition q)) :
        Set (PartyPartition q)) := by
  intro π₀
  have hcard : ∀ ρ : PartyPartition k, (pullPartyPartition m ρ).parts.card = ρ.parts.card := by
    intro ρ; rw [pullPartyPartition, card_parts_ofSetoid_ker]
    congr 1; ext D; simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨fun ⟨c, hc⟩ ↦ hc ▸ ρ.part_mem.mpr (Finset.mem_univ (m c)), fun hD ↦ ?_⟩
    obtain ⟨j, hj⟩ := ρ.nonempty_of_mem_parts hD
    obtain ⟨c, rfl⟩ := hm j; exact ⟨c, ρ.part_eq_of_mem hD hj⟩
  have hmaps : Set.MapsTo (pullPartyPartition m) (twoOrThreePartitions k : Set (PartyPartition k))
      (((twoOrThreePartitions q).filter (fun σ ↦ π₀ ≤ σ) : Finset _) : Set _) := by
    intro ρ hρ
    have h23 : pullPartyPartition m ρ ∈ twoOrThreePartitions q := by
      simp only [twoOrThreePartitions, partitionsOfCard, Finset.mem_coe, Finset.mem_union,
        Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢; rwa [hcard ρ]
    refine Finset.mem_filter.mpr ⟨h23, fun A hA ↦ ?_⟩
    obtain ⟨c₀, hc₀⟩ := π₀.nonempty_of_mem_parts hA
    refine ⟨(pullPartyPartition m ρ).part c₀,
      (pullPartyPartition m ρ).part_mem.mpr (Finset.mem_univ c₀), fun c hc ↦ ?_⟩
    have hmc : m c = m c₀ := (ofSetoid_ker_part_eq m c c₀).mp
      ((π₀.part_eq_of_mem hA hc).trans (π₀.part_eq_of_mem hA hc₀).symm)
    rw [((pullPartyPartition m ρ).mem_part_iff_part_eq_part
      (Finset.mem_univ c) (Finset.mem_univ c₀)), pullPartyPartition, ofSetoid_ker_part_eq, hmc]
  have hinj : Set.InjOn (pullPartyPartition m)
      (twoOrThreePartitions k : Set (PartyPartition k)) := by
    intro ρ₁ _ ρ₂ _ heq; rw [partyPartition_eq_iff] at heq ⊢; intro j₁ j₂
    obtain ⟨c₁, rfl⟩ := hm j₁; obtain ⟨c₂, rfl⟩ := hm j₂
    have h12 := heq c₁ c₂
    rwa [pullPartyPartition, ofSetoid_ker_part_eq, pullPartyPartition, ofSetoid_ker_part_eq] at h12
  refine ⟨hmaps, hinj, fun σ hσ ↦ ?_⟩
  obtain ⟨hσ23, hle⟩ := Finset.mem_filter.mp hσ
  have hconst : ∀ c₁ c₂ : Fin q, m c₁ = m c₂ → σ.part c₁ = σ.part c₂ := fun c₁ c₂ hmc ↦ by
    obtain ⟨D, hD, hAD⟩ := hle (π₀.part_mem.mpr (Finset.mem_univ c₁))
    have hc₁D : c₁ ∈ D := hAD (π₀.mem_part (Finset.mem_univ c₁))
    have hc₂A : c₂ ∈ π₀.part c₁ := by
      rw [π₀.mem_part_iff_part_eq_part (Finset.mem_univ c₂) (Finset.mem_univ c₁)]
      exact (ofSetoid_ker_part_eq m c₂ c₁).mpr hmc.symm
    exact (σ.part_eq_of_mem hD hc₁D).trans (σ.part_eq_of_mem hD (hAD hc₂A)).symm
  choose sec hsec using hm
  let ρ : PartyPartition k := Finpartition.ofSetoid (Setoid.ker (fun j : Fin k ↦ σ.part (sec j)))
  have hpull : pullPartyPartition m ρ = σ := partyPartition_eq_iff.mpr fun c₁ c₂ ↦ by
    rw [pullPartyPartition, ofSetoid_ker_part_eq]
    dsimp only [ρ]
    rw [ofSetoid_ker_part_eq,
      hconst (sec (m c₁)) c₁ (hsec (m c₁)), hconst (sec (m c₂)) c₂ (hsec (m c₂))]
  have hρ23 : ρ ∈ twoOrThreePartitions k := by
    simp only [twoOrThreePartitions, partitionsOfCard, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and] at hσ23 ⊢; rwa [← hcard ρ, hpull]
  exact ⟨ρ, hρ23, hpull⟩

private lemma partitionRank_comp {N q k : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2))
    (col : Fin N → Fin q) (m : Fin q → Fin k) (ρ : PartyPartition k) :
    partitionRank Γ (m ∘ col) ρ = partitionRank Γ col (pullPartyPartition m ρ) := by
  unfold partitionRank; congr 1; ext u v
  change (if ρ.part (m (col u)) = ρ.part (m (col v)) then 0 else Γ u v) =
    if (pullPartyPartition m ρ).part (col u) = (pullPartyPartition m ρ).part (col v)
      then 0 else Γ u v
  simp only [pullPartyPartition, ofSetoid_ker_part_eq]

/-- Party-label permutation invariance of `S_3^{(q)}`, block-order independence and upper-sum
formula for coarse-grained multi-entropies `S_3^{(k)}(π)`, recovery of `S_3^{(q)}` at the discrete
partition, and the bipartite off-diagonal rank formula `S_3^{(2)}({X, Y}) = log 2 · rank Γ_{X,Y}`. -/
theorem party_symmetry_coarse_graining_and_bipartite_entropy :
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
              ∑ σ ∈ (twoOrThreePartitions q).filter (fun σ ↦ π ≤ σ),
                (partitionRank Γ col σ : ℝ)) ∧
    (∀ {N q : ℕ}, 2 ≤ q → ∀ (ψ : (Fin N → Fin 2) → ℂ),
      StabilizedBy pauliSet ψ → (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1 →
      ∀ (col : Fin N → Fin q),
        coarseMultiEntropy (⊥ : PartyPartition q) col ψ = S 3 q col ψ) ∧
    (∀ {N q : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2)) (ψ : (Fin N → Fin 2) → ℂ),
      IsGraphFormOf Γ ψ → ∀ (col : Fin N → Fin q) {σ : PartyPartition q},
        σ ∈ partitionsOfCard q 2 → ∀ {X Y : Finset (Fin q)},
          σ.parts = {X, Y} → X ≠ Y →
          coarseMultiEntropy σ col ψ = Real.log 2 * ((offDiagBlock Γ col X Y).rank : ℝ)) := by
  have hcoarse_any : ∀ {N q k : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2))
      (ψ : (Fin N → Fin 2) → ℂ), IsGraphFormOf Γ ψ →
      ∀ (col : Fin N → Fin q) (π : PartyPartition q), 2 ≤ π.parts.card →
      ∀ (B : Fin k ≃ π.parts),
        S 3 k (coarseCol π B col) ψ =
          (Real.log 2 / (2 * (3 : ℝ) ^ (π.parts.card - 2))) *
            ∑ σ ∈ (twoOrThreePartitions q).filter (fun σ ↦ π ≤ σ),
              (partitionRank Γ col σ : ℝ) := by
    intro N q k Γ ψ hΓψ col π hπ2 B
    have hk : k = π.parts.card := by
      simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_congr B
    let m : Fin q → Fin k := fun c ↦ B.symm (partOf π c)
    have hm_surj : Function.Surjective m := fun j ↦ by
      obtain ⟨c, hc⟩ := π.nonempty_of_mem_parts (B j).2
      have hp : partOf π c = B j := Subtype.ext (π.part_eq_of_mem (B j).2 hc)
      exact ⟨c, by dsimp [m]; rw [hp, Equiv.symm_apply_apply]⟩
    have hker : Finpartition.ofSetoid (Setoid.ker m) = π :=
      partyPartition_eq_iff.mpr fun a b ↦ by
        rw [ofSetoid_ker_part_eq]; dsimp [m, partOf]
        exact ⟨fun h ↦ congrArg Subtype.val (B.symm.injective h),
          fun h ↦ congrArg B.symm (Subtype.ext h)⟩
    change S 3 k (m ∘ col) ψ = _
    have hk2 : 2 ≤ k := by omega
    rw [replica_three_coarse_partition_sum.2.2 hk2 Γ ψ hΓψ (m ∘ col)]
    congr 1
    · rw [hk]
    · have hbij := pullPartyPartition_bijOn m hm_surj; dsimp only at hbij; rw [hker] at hbij
      exact Finset.sum_bij (fun ρ _ ↦ pullPartyPartition m ρ)
        (fun ρ hρ ↦ hbij.mapsTo hρ) (fun _ h₁ _ h₂ ↦ hbij.injOn h₁ h₂)
        (fun σ hσ ↦ let ⟨ρ, hρ, heq⟩ := hbij.surjOn hσ; ⟨ρ, hρ, heq⟩)
        (fun ρ _ ↦ congrArg Nat.cast (partitionRank_comp Γ col m ρ))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N q hq ψ hstab hn col τ
    obtain ⟨Γ, hΓψ⟩ := graph_form_existence_and_replica_rank_formula.2.1 ψ hstab hn
    rw [replica_three_coarse_partition_sum.2.2 hq Γ ψ hΓψ (τ ∘ col),
      replica_three_coarse_partition_sum.2.2 hq Γ ψ hΓψ col]; congr 1
    have hbij := pullPartyPartition_bijOn (τ : Fin q → Fin q) τ.surjective
    dsimp only at hbij
    have hbot : Finpartition.ofSetoid (Setoid.ker (τ : Fin q → Fin q)) =
        (⊥ : PartyPartition q) := partyPartition_eq_iff.mpr fun a b ↦ by
      rw [ofSetoid_ker_part_eq, τ.injective.eq_iff,
        (⊥ : PartyPartition q).part_eq_of_mem
          (Finpartition.mem_bot_iff.mpr ⟨a, Finset.mem_univ a, rfl⟩) (Finset.mem_singleton_self a),
        (⊥ : PartyPartition q).part_eq_of_mem
          (Finpartition.mem_bot_iff.mpr ⟨b, Finset.mem_univ b, rfl⟩) (Finset.mem_singleton_self b),
        Finset.singleton_inj]
    rw [hbot, Finset.filter_true_of_mem (fun _ _ ↦ bot_le)] at hbij
    exact Finset.sum_bij (fun ρ _ ↦ pullPartyPartition τ ρ)
      (fun ρ hρ ↦ hbij.mapsTo hρ) (fun _ h₁ _ h₂ ↦ hbij.injOn h₁ h₂)
      (fun σ hσ ↦ let ⟨ρ, hρ, heq⟩ := hbij.surjOn hσ; ⟨ρ, hρ, heq⟩)
      (fun ρ _ ↦ congrArg Nat.cast (partitionRank_comp Γ col τ ρ))
  · intro N q k Γ ψ hΓψ col π hπ2 B
    have hB := hcoarse_any Γ ψ hΓψ col π hπ2 B
    have hdef : coarseMultiEntropy π col ψ = _ :=
      hcoarse_any Γ ψ hΓψ col π hπ2 π.parts.equivFin.symm
    exact ⟨hB.trans hdef.symm, hdef⟩
  · intro N q hq ψ hstab hn col
    obtain ⟨Γ, hΓψ⟩ := graph_form_existence_and_replica_rank_formula.2.1 ψ hstab hn
    have hbot_card : (⊥ : PartyPartition q).parts.card = q := by simp
    have hbot2 : 2 ≤ (⊥ : PartyPartition q).parts.card := by omega
    unfold coarseMultiEntropy
    rw [(hcoarse_any Γ ψ hΓψ col (⊥ : PartyPartition q) hbot2
      (⊥ : PartyPartition q).parts.equivFin.symm), hbot_card,
      Finset.filter_true_of_mem (fun _ _ ↦ bot_le),
      ← replica_three_coarse_partition_sum.2.2 hq Γ ψ hΓψ col]
  · intro N q Γ ψ hΓψ col σ hσ X Y hparts hXY
    have hσcard : σ.parts.card = 2 := (Finset.mem_filter.mp hσ).2
    have hform : coarseMultiEntropy σ col ψ = _ :=
      hcoarse_any Γ ψ hΓψ col σ (by omega) σ.parts.equivFin.symm
    have hfilter : (twoOrThreePartitions q).filter (fun τ ↦ σ ≤ τ) = {σ} := by
      ext τ; simp only [Finset.mem_filter, Finset.mem_singleton]
      refine ⟨fun ⟨hτ, hle⟩ ↦ ?_, fun h ↦ h.symm ▸ ⟨Finset.mem_union_left _ hσ, le_rfl⟩⟩
      rcases Finset.mem_union.mp hτ with hτ2 | hτ3
      · have h2card : τ.parts.card = 2 := (Finset.mem_filter.mp hτ2).2
        obtain ⟨D, hD, hXD⟩ := hle (by simp [hparts] : X ∈ σ.parts)
        obtain ⟨E, hE, hYE⟩ := hle (by simp [hparts] : Y ∈ σ.parts)
        have hXuniv : X ∪ Y = Finset.univ := by simpa [hparts] using σ.sup_parts
        have hDE : D ≠ E := fun h ↦ by
          have hDu : D = Finset.univ := Finset.Subset.antisymm (Finset.subset_univ _)
            (hXuniv ▸ Finset.union_subset hXD (h ▸ hYE))
          have hsub : τ.parts ⊆ {Finset.univ} := fun F hF ↦ Finset.mem_singleton.mpr
            (τ.eq_of_mem_parts hF (hDu ▸ hD) (τ.nonempty_of_mem_parts hF).choose_spec
              (Finset.mem_univ _))
          have hle1 : τ.parts.card ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
          omega
        have hdisjDE : Disjoint D E := τ.disjoint hD hE hDE
        have hXD_eq : X = D := Finset.Subset.antisymm hXD fun x hxD ↦ by
          rcases Finset.mem_union.mp (hXuniv.symm ▸ Finset.mem_univ x) with hxX | hxY
          · exact hxX
          · exact False.elim (Finset.disjoint_left.mp hdisjDE hxD (hYE hxY))
        have hYE_eq : Y = E := Finset.Subset.antisymm hYE fun y hyE ↦ by
          rcases Finset.mem_union.mp (hXuniv.symm ▸ Finset.mem_univ y) with hyX | hyY
          · exact False.elim (Finset.disjoint_left.mp hdisjDE (hXD hyX) hyE)
          · exact hyY
        refine Finpartition.ext (Finset.eq_of_subset_of_card_le (fun F hF ↦ ?_) (by omega)).symm
        rw [hparts, Finset.mem_insert, Finset.mem_singleton] at hF
        exact hF.elim (fun h ↦ h ▸ hXD_eq.symm ▸ hD) (fun h ↦ h ▸ hYE_eq.symm ▸ hE)
      · have := (Finset.mem_filter.mp hτ3).2; have := Finpartition.card_mono hle; omega
    rw [hform, hσcard, hfilter, Finset.sum_singleton,
      bipartite_masked_antidiagonal_rank Γ hΓψ.1 col hσ hparts hXY]
    push_cast; norm_num; ring

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphFormReplicaThreeRank
