/- GID: D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stirling refinement counts, triangular poset inversion, and bipartite masked ranks. -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Coarse three-block partition refinements, triangular inversion, and bipartite masked ranks
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement

open scoped BigOperators
open Matrix

/-- Set partitions of the `q` labelled parties `Fin q`. -/
abbrev PartyPartition (q : ℕ) : Type :=
  Finpartition (Finset.univ : Finset (Fin q))

instance instDecidableLEPartyPartition {q : ℕ} : DecidableLE (PartyPartition q) :=
  fun P Q ↦ inferInstanceAs (Decidable (∀ b ∈ P.parts, ∃ c ∈ Q.parts, b ≤ c))

/-- Set partitions of `Fin q` into exactly `k` nonempty blocks. -/
def partitionsOfCard (q k : ℕ) : Finset (PartyPartition q) :=
  Finset.univ.filter (fun π ↦ π.parts.card = k)

/-- Set partitions of `Fin q` into two or three blocks. -/
def twoOrThreePartitions (q : ℕ) : Finset (PartyPartition q) :=
  partitionsOfCard q 2 ∪ partitionsOfCard q 3

/-- Set partitions of `Fin q` with at least two blocks. -/
def nontrivialPartitions (q : ℕ) : Finset (PartyPartition q) :=
  Finset.univ.filter (fun π ↦ 2 ≤ π.parts.card)

/-- The block of `π` containing party `c`, bundled as an element of `π.parts`. -/
def partOf {q : ℕ} (π : PartyPartition q) (c : Fin q) : π.parts :=
  ⟨π.part c, π.part_mem.mpr (Finset.mem_univ c)⟩

/-- Coarse-grained colouring determined by a party partition `π` and a block listing `B`. -/
def coarseCol {N q k : ℕ} (π : PartyPartition q) (B : Fin k ≃ π.parts)
    (col : Fin N → Fin q) : Fin N → Fin k :=
  fun u ↦ B.symm (partOf π (col u))

/-- Adjacency matrix over `ZMod 2` masked to pairs of qubits lying in distinct blocks of `π`. -/
def maskedAdj {N q : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2))
    (col : Fin N → Fin q) (π : PartyPartition q) : Matrix (Fin N) (Fin N) (ZMod 2) :=
  fun u v ↦ if π.part (col u) = π.part (col v) then 0 else Γ u v

/-- Rank over `ZMod 2` of the partition-masked adjacency matrix `maskedAdj Γ col π`. -/
def partitionRank {N q : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2))
    (col : Fin N → Fin q) (π : PartyPartition q) : ℕ :=
  (maskedAdj Γ col π).rank

/-- Rectangular off-diagonal block of `Γ` with rows in party subset `X` and columns in `Y`. -/
def offDiagBlock {N q : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2))
    (col : Fin N → Fin q) (X Y : Finset (Fin q)) :
    Matrix {u : Fin N // col u ∈ X} {v : Fin N // col v ∈ Y} (ZMod 2) :=
  fun u v ↦ Γ u.1 v.1

/-- Upper sum of a partition function `r` over two- and three-block coarsenings `σ ≥ ρ`. -/
def upperRankSum {q : ℕ} (r : PartyPartition q → ℝ) (ρ : PartyPartition q) : ℝ :=
  ∑ σ ∈ (twoOrThreePartitions q).filter (fun σ ↦ ρ ≤ σ), r σ

/-- Weighted refinement sum collecting the scaled coefficients of nontrivial refinements of `σ`. -/
def coarseWeight {q : ℕ} (c : PartyPartition q → ℝ) (σ : PartyPartition q) : ℝ :=
  ∑ ρ ∈ (nontrivialPartitions q).filter (fun ρ ↦ ρ ≤ σ),
    (3 : ℝ) ^ (2 - (ρ.parts.card : ℤ)) * c ρ

private lemma disjoint_partitionsOfCard (q : ℕ) {k₁ k₂ : ℕ} (h : k₁ ≠ k₂) :
    Disjoint (partitionsOfCard q k₁) (partitionsOfCard q k₂) :=
  Finset.disjoint_left.mpr fun _ h₁ h₂ ↦
    h ((Finset.mem_filter.mp h₁).2.symm.trans (Finset.mem_filter.mp h₂).2)

private lemma stirlingSecond_two_formula {m : ℕ} (hm : 1 ≤ m) :
    Nat.stirlingSecond m 2 = 2 ^ (m - 1) - 1 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hm
  induction d with
  | zero => simp [Nat.stirlingSecond_eq_zero_of_lt]
  | succ d ih =>
    have hpos : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have hstep : (d + 1 + 1).stirlingSecond 2 =
        2 * (d + 1).stirlingSecond 2 + (d + 1).stirlingSecond 1 := rfl
    rw [hstep, ih (Nat.succ_pos d), Nat.stirlingSecond_one_right d]
    simp only [Nat.add_sub_cancel, pow_succ']; omega

private lemma stirlingSecond_two_add_three {q : ℕ} (hq : 1 ≤ q) :
    2 * (Nat.stirlingSecond q 2 + Nat.stirlingSecond q 3) = 3 ^ (q - 1) - 1 ∧
    ((3 : ℝ) ^ (q - 1) - 1) / 2 = (Nat.stirlingSecond q 2 : ℝ) + (Nat.stirlingSecond q 3 : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hq
  have hnat : 2 * ((d + 1).stirlingSecond 2 + (d + 1).stirlingSecond 3) = 3 ^ d - 1 := by
    induction d with
    | zero => simp [Nat.stirlingSecond_eq_zero_of_lt]
    | succ d ih =>
      have hpos : 1 ≤ 3 ^ d := Nat.one_le_pow d 3 (by decide)
      have h2 : (d + 1 + 1).stirlingSecond 2 =
          2 * (d + 1).stirlingSecond 2 + (d + 1).stirlingSecond 1 := rfl
      have h3 : (d + 1 + 1).stirlingSecond 3 =
          3 * (d + 1).stirlingSecond 3 + (d + 1).stirlingSecond 2 := rfl
      rw [h2, h3, Nat.stirlingSecond_one_right d, pow_succ']
      have ih' := ih (Nat.succ_pos d); omega
  refine ⟨by simpa using hnat, ?_⟩
  have hpos : 1 ≤ 3 ^ d := Nat.one_le_pow d 3 (by decide)
  have hreal : (2 : ℝ) * (((d + 1).stirlingSecond 2 : ℝ) + ((d + 1).stirlingSecond 3 : ℝ)) + 1 =
      (3 : ℝ) ^ d := by
    exact_mod_cast (show 2 * ((d + 1).stirlingSecond 2 + (d + 1).stirlingSecond 3) + 1 = 3 ^ d
      by omega)
  simp only [Nat.add_sub_cancel]; linarith

private def fibreSet {q n : ℕ} (s : Finset (Fin q)) (f : s → Fin n) (c : Fin n) : Finset (Fin q) :=
  s.filter (fun a ↦ ∃ ha : a ∈ s, f ⟨a, ha⟩ = c)

private def fibrePart {q n : ℕ} (s : Finset (Fin q)) (f : s → Fin n) : Finpartition s :=
  Finpartition.ofErase ((Finset.univ : Finset (Fin n)).image (fibreSet s f))
    (Set.PairwiseDisjoint.supIndep fun A hA B hB hAB ↦ by
      rw [Finset.mem_coe, Finset.mem_image] at hA hB
      obtain ⟨c₁, _, rfl⟩ := hA; obtain ⟨c₂, _, rfl⟩ := hB
      refine Finset.disjoint_left.mpr fun a ha₁ ha₂ ↦ hAB ?_
      obtain ⟨_, _, hc₁⟩ := Finset.mem_filter.mp ha₁
      obtain ⟨_, _, hc₂⟩ := Finset.mem_filter.mp ha₂
      rw [← hc₁, hc₂])
    (Finset.ext fun a ↦ by
      simp only [fibreSet, Finset.sup_image, Function.id_comp, Finset.mem_sup, Finset.mem_univ,
        Finset.mem_filter, true_and]
      exact ⟨fun ⟨_, ha, _⟩ ↦ ha, fun ha ↦ ⟨f ⟨a, ha⟩, ha, ha, rfl⟩⟩)

private lemma mem_fibrePart_iff {q n : ℕ} {s : Finset (Fin q)} (f : s → Fin n)
    {B : Finset (Fin q)} :
    B ∈ (fibrePart s f).parts ↔ B.Nonempty ∧ ∃ c : Fin n, fibreSet s f c = B := by
  simp only [fibrePart, Finpartition.ofErase_parts, Finset.bot_eq_empty, Finset.mem_erase,
    Finset.mem_image, Finset.mem_univ, true_and, Finset.nonempty_iff_ne_empty]

private lemma fibre_eval_eq {q n : ℕ} {s : Finset (Fin q)} (f : s → Fin n)
    {B : Finset (Fin q)} {c : Fin n} (hc : fibreSet s f c = B)
    {a : Fin q} (haB : a ∈ B) (_has : a ∈ s) : f ⟨a, _has⟩ = c := by
  obtain ⟨_, _, hfa⟩ := Finset.mem_filter.mp (hc.symm ▸ haB); exact hfa

private def fibreColour {q n : ℕ} (s : Finset (Fin q)) (f : s → Fin n) :
    (fibrePart s f).parts ↪ Fin n where
  toFun B :=
    let hne := (fibrePart s f).nonempty_of_mem_parts B.2
    f ⟨hne.choose, (fibrePart s f).le B.2 hne.choose_spec⟩
  inj' B₁ B₂ h := by
    obtain ⟨_, c₁, hc₁⟩ := (mem_fibrePart_iff f).mp B₁.2
    obtain ⟨_, c₂, hc₂⟩ := (mem_fibrePart_iff f).mp B₂.2
    have h1 := (fibrePart s f).nonempty_of_mem_parts B₁.2
    have h2 := (fibrePart s f).nonempty_of_mem_parts B₂.2
    have hv₁ := fibre_eval_eq f hc₁ h1.choose_spec ((fibrePart s f).le B₁.2 h1.choose_spec)
    have hv₂ := fibre_eval_eq f hc₂ h2.choose_spec ((fibrePart s f).le B₂.2 h2.choose_spec)
    have hce : c₁ = c₂ := hv₁.symm.trans (h.trans hv₂)
    exact Subtype.ext (hc₁.symm.trans ((congrArg (fibreSet s f) hce).trans hc₂))

private lemma sigma_part_ext {q n : ℕ} {s : Finset (Fin q)}
    {P₁ P₂ : Finpartition s} {g₁ : P₁.parts ↪ Fin n} {g₂ : P₂.parts ↪ Fin n} (hP : P₁ = P₂)
    (hg : ∀ (a : Fin q) (ha : a ∈ s),
      g₁ ⟨P₁.part a, P₁.part_mem.mpr ha⟩ = g₂ ⟨P₂.part a, P₂.part_mem.mpr ha⟩) :
    (⟨P₁, g₁⟩ : Σ P : Finpartition s, (P.parts ↪ Fin n)) = ⟨P₂, g₂⟩ := by
  subst hP; congr 1; apply DFunLike.ext; rintro ⟨B, hB⟩
  obtain ⟨a, haB⟩ := P₁.nonempty_of_mem_parts hB
  have has : a ∈ s := P₁.le hB haB
  have hpart : (⟨P₁.part a, P₁.part_mem.mpr has⟩ : P₁.parts) = ⟨B, hB⟩ :=
    Subtype.ext (P₁.part_eq_of_mem hB haB)
  simpa only [hpart] using hg a has

private def partitionEmbeddingEquivFun {q n : ℕ} (s : Finset (Fin q)) :
    (Σ P : Finpartition s, (P.parts ↪ Fin n)) ≃ (s → Fin n) where
  toFun p x := p.2 ⟨p.1.part x.1, p.1.part_mem.mpr x.2⟩
  invFun f := ⟨fibrePart s f, fibreColour s f⟩
  left_inv := by
    rintro ⟨P, g⟩
    set f : s → Fin n := fun x ↦ g ⟨P.part x.1, P.part_mem.mpr x.2⟩
    have hfib : ∀ (B : Finset (Fin q)) (hB : B ∈ P.parts), fibreSet s f (g ⟨B, hB⟩) = B := by
      intro B hB; ext b; simp only [fibreSet, f, Finset.mem_filter]
      refine ⟨fun ⟨hbs, _, hgb⟩ ↦ ?_, fun hbB ↦ ⟨P.le hB hbB, P.le hB hbB, ?_⟩⟩
      · have hpart : P.part b = B := congrArg Subtype.val (g.injective hgb)
        rw [← hpart]; exact P.mem_part hbs
      · exact congrArg g (Subtype.ext (P.part_eq_of_mem hB hbB))
    have hP : fibrePart s f = P := Finpartition.ext (Finset.ext fun B ↦ by
      rw [mem_fibrePart_iff]
      refine ⟨?_, fun hB ↦ ⟨P.nonempty_of_mem_parts hB, g ⟨B, hB⟩, hfib B hB⟩⟩
      rintro ⟨⟨a, haB⟩, _, rfl⟩
      obtain ⟨has, _, rfl⟩ := Finset.mem_filter.mp haB
      rw [hfib (P.part a) (P.part_mem.mpr has)]; exact P.part_mem.mpr has)
    refine sigma_part_ext hP fun a has ↦ ?_
    change fibreColour s f ⟨(fibrePart s f).part a, _⟩ = _
    have hB : (fibrePart s f).part a ∈ (fibrePart s f).parts := (fibrePart s f).part_mem.mpr has
    obtain ⟨_, c, hc⟩ := (mem_fibrePart_iff f).mp hB
    have hne := (fibrePart s f).nonempty_of_mem_parts hB
    exact (fibre_eval_eq f hc hne.choose_spec ((fibrePart s f).le hB hne.choose_spec)).trans
      (fibre_eval_eq f hc ((fibrePart s f).mem_part has) has).symm
  right_inv f := funext fun ⟨a, has⟩ ↦ by
    change fibreColour s f ⟨(fibrePart s f).part a, _⟩ = f ⟨a, has⟩
    have hB : (fibrePart s f).part a ∈ (fibrePart s f).parts := (fibrePart s f).part_mem.mpr has
    obtain ⟨_, c, hc⟩ := (mem_fibrePart_iff f).mp hB
    have hne := (fibrePart s f).nonempty_of_mem_parts hB
    exact (fibre_eval_eq f hc hne.choose_spec ((fibrePart s f).le hB hne.choose_spec)).trans
      (fibre_eval_eq f hc ((fibrePart s f).mem_part has) has).symm

private lemma card_finpartition_parts_eq {q : ℕ} (s : Finset (Fin q)) (k : ℕ) :
    (Finset.univ.filter (fun P : Finpartition s ↦ P.parts.card = k)).card =
      Nat.stirlingSecond s.card k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hks : k ≤ s.card
    · have hpow : k ^ s.card = ∑ j ∈ Finset.range (s.card + 1),
          (Finset.univ.filter (fun P : Finpartition s ↦ P.parts.card = j)).card *
            k.descFactorial j := by
        have hcard : Fintype.card (Σ P : Finpartition s, (P.parts ↪ Fin k)) = k ^ s.card := by
          rw [Fintype.card_congr (partitionEmbeddingEquivFun s), Fintype.card_fun,
            Fintype.card_fin, Fintype.card_coe]
        rw [← hcard, Fintype.card_sigma]
        simp_rw [show ∀ P : Finpartition s, Fintype.card (P.parts ↪ Fin k) =
          k.descFactorial P.parts.card from fun P ↦ by
            rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe]]
        rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Finpartition s)))
          (t := Finset.range (s.card + 1)) (g := fun P ↦ P.parts.card)
          (fun P _ ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le P.card_parts_le_card))]
        exact Finset.sum_congr rfl fun j _ ↦ by
          rw [Finset.sum_congr rfl (fun P hP ↦ by rw [(Finset.mem_filter.mp hP).2]),
            Finset.sum_const, smul_eq_mul]
      have heq := hpow.symm.trans (Nat.pow_eq_sum_stirlingSecond_mul_descFactorial k s.card)
      have hmem : k ∈ Finset.range (s.card + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hks)
      rw [← Finset.add_sum_erase _ _ hmem] at heq
      conv_rhs at heq => rw [← Finset.add_sum_erase _ _ hmem]
      have hrest : ∑ j ∈ (Finset.range (s.card + 1)).erase k,
          (Finset.univ.filter (fun P : Finpartition s ↦ P.parts.card = j)).card *
            k.descFactorial j =
        ∑ j ∈ (Finset.range (s.card + 1)).erase k,
          Nat.stirlingSecond s.card j * k.descFactorial j :=
        Finset.sum_congr rfl fun j hj ↦ by
          rcases lt_or_gt_of_ne (Finset.mem_erase.mp hj).1 with hlt | hgt
          · rw [ih j hlt]
          · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hgt, mul_zero, mul_zero]
      rw [hrest] at heq
      have hmul := Nat.add_right_cancel heq
      rw [Nat.descFactorial_self] at hmul
      exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos k) hmul
    · have hlt : s.card < k := Nat.lt_of_not_ge hks
      rw [Nat.stirlingSecond_eq_zero_of_lt hlt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun P _ hP ↦ absurd (hP ▸ P.card_parts_le_card) (not_le_of_gt hlt)

private def joinTwo {q : ℕ} {X Y : Finset (Fin q)} (hdisj : Disjoint X Y)
    (hunion : X ∪ Y = Finset.univ) (P : Finpartition X) (Q : Finpartition Y) :
    PartyPartition q where
  parts := P.parts ∪ Q.parts
  supIndep := Set.PairwiseDisjoint.supIndep fun A hA C hC hAC ↦ by
    rw [Finset.mem_coe, Finset.mem_union] at hA hC
    rcases hA with hA | hA <;> rcases hC with hC | hC
    · exact P.disjoint hA hC hAC
    · exact hdisj.mono (P.le hA) (Q.le hC)
    · exact hdisj.symm.mono (Q.le hA) (P.le hC)
    · exact Q.disjoint hA hC hAC
  sup_parts := by rw [Finset.sup_union, P.sup_parts, Q.sup_parts, Finset.sup_eq_union, hunion]
  bot_notMem := fun h ↦ (Finset.mem_union.mp h).elim P.bot_notMem Q.bot_notMem

private lemma refinement_two_block_equiv_card {q : ℕ} {σ : PartyPartition q}
    (hσ : σ ∈ partitionsOfCard q 2) :
    ((partitionsOfCard q 3).filter (fun π ↦ π ≤ σ)).card + 2 =
      ∑ B ∈ σ.parts, 2 ^ (B.card - 1) := by
  obtain ⟨X, Y, hXY, hparts⟩ := Finset.card_eq_two.mp (Finset.mem_filter.mp hσ).2
  have hXmem : X ∈ σ.parts := by simp [hparts]
  have hYmem : Y ∈ σ.parts := by simp [hparts]
  have hdisj : Disjoint X Y := σ.disjoint hXmem hYmem hXY
  have hunion : X ∪ Y = Finset.univ := by simpa [hparts] using σ.sup_parts
  have hXne : X.Nonempty := σ.nonempty_of_mem_parts hXmem
  have hYne : Y.Nonempty := σ.nonempty_of_mem_parts hYmem
  have hsub_or : ∀ {π : PartyPartition q}, π ≤ σ → ∀ {A}, A ∈ π.parts → A ⊆ X ∨ A ⊆ Y := by
    intro π hle A hA; obtain ⟨D, hD, hAD⟩ := hle hA
    rw [hparts, Finset.mem_insert, Finset.mem_singleton] at hD
    exact hD.elim (fun h ↦ Or.inl (h ▸ hAD)) (fun h ↦ Or.inr (h ▸ hAD))
  have hsplit : ∀ {π : PartyPartition q}, π ≤ σ →
      (π.parts.filter (· ⊆ X)).sup id = X ∧ (π.parts.filter (· ⊆ Y)).sup id = Y := by
    intro π hπσ; refine ⟨Finset.ext fun a ↦ ?_, Finset.ext fun a ↦ ?_⟩ <;>
      simp only [Finset.mem_sup, Finset.mem_filter, id_eq]
    · refine ⟨fun ⟨A, ⟨_, hAX⟩, haA⟩ ↦ hAX haA, fun haX ↦ ?_⟩
      obtain ⟨A, hA, haA⟩ := π.exists_mem (Finset.mem_univ a)
      exact (hsub_or hπσ hA).elim (fun h ↦ ⟨A, ⟨hA, h⟩, haA⟩)
        (fun h ↦ False.elim (Finset.disjoint_left.mp hdisj haX (h haA)))
    · refine ⟨fun ⟨A, ⟨_, hAY⟩, haA⟩ ↦ hAY haA, fun haY ↦ ?_⟩
      obtain ⟨A, hA, haA⟩ := π.exists_mem (Finset.mem_univ a)
      exact (hsub_or hπσ hA).elim
        (fun h ↦ False.elim (Finset.disjoint_left.mp hdisj (h haA) haY))
        (fun h ↦ ⟨A, ⟨hA, h⟩, haA⟩)
  let S3 := (partitionsOfCard q 3).filter (fun π ↦ π ≤ σ)
  let PX (k : ℕ) := (Finset.univ : Finset (Finpartition X)).filter (fun P ↦ P.parts.card = k)
  let QY (k : ℕ) := (Finset.univ : Finset (Finpartition Y)).filter (fun Q ↦ Q.parts.card = k)
  let Pairs := PX 2 ×ˢ QY 1 ∪ PX 1 ×ˢ QY 2
  have hdisjPairs : Disjoint (PX 2 ×ˢ QY 1) (PX 1 ×ˢ QY 2) :=
    Finset.disjoint_left.mpr fun ⟨_, _⟩ h₁ h₂ ↦ by
      simp only [PX, QY, Finset.mem_product, Finset.mem_filter] at h₁ h₂; omega
  have hbij : S3.card = Pairs.card := by
    refine Finset.card_bij
      (fun π hπ ↦
        (π.ofSubset (Finset.filter_subset (· ⊆ X) π.parts) (hsplit (Finset.mem_filter.mp hπ).2).1,
         π.ofSubset (Finset.filter_subset (· ⊆ Y) π.parts) (hsplit (Finset.mem_filter.mp hπ).2).2))
      (?_) (?_) (?_)
    · intro π hπ
      have hcard3 : π.parts.card = 3 := (Finset.mem_filter.mp (Finset.mem_filter.mp hπ).1).2
      have hle : π ≤ σ := (Finset.mem_filter.mp hπ).2
      have hPQdisj : Disjoint (π.parts.filter (· ⊆ X)) (π.parts.filter (· ⊆ Y)) :=
        Finset.disjoint_left.mpr fun A hAX hAY ↦ by
          obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts (Finset.mem_filter.mp hAX).1
          exact Finset.disjoint_left.mp hdisj ((Finset.mem_filter.mp hAX).2 hx)
            ((Finset.mem_filter.mp hAY).2 hx)
      have hPQunion : π.parts.filter (· ⊆ X) ∪ π.parts.filter (· ⊆ Y) = π.parts :=
        Finset.ext fun A ↦ by
          simp only [Finset.mem_union, Finset.mem_filter]
          exact ⟨fun h ↦ h.elim And.left And.left,
            fun hA ↦ (hsub_or hle hA).elim (fun h ↦ Or.inl ⟨hA, h⟩) (fun h ↦ Or.inr ⟨hA, h⟩)⟩
      have hsum : (π.parts.filter (· ⊆ X)).card + (π.parts.filter (· ⊆ Y)).card = 3 := by
        rw [← Finset.card_union_of_disjoint hPQdisj, hPQunion, hcard3]
      have hPpos : 1 ≤ (π.parts.filter (· ⊆ X)).card := Finset.card_pos.mpr
        ((π.ofSubset (Finset.filter_subset (· ⊆ X) π.parts) (hsplit hle).1).parts_nonempty
          (Finset.nonempty_iff_ne_empty.mp hXne))
      have hQpos : 1 ≤ (π.parts.filter (· ⊆ Y)).card := Finset.card_pos.mpr
        ((π.ofSubset (Finset.filter_subset (· ⊆ Y) π.parts) (hsplit hle).2).parts_nonempty
          (Finset.nonempty_iff_ne_empty.mp hYne))
      simp only [Pairs, PX, QY, Finset.mem_union, Finset.mem_product, Finset.mem_filter,
        Finset.mem_univ, true_and, Finpartition.ofSubset_parts]
      omega
    · intro π₁ h₁ π₂ h₂ heq
      have hu : ∀ {π : PartyPartition q}, π ≤ σ →
          π.parts = π.parts.filter (· ⊆ X) ∪ π.parts.filter (· ⊆ Y) := fun hle ↦
        Finset.ext fun C ↦ by
          simp only [Finset.mem_union, Finset.mem_filter]
          exact ⟨fun hC ↦ (hsub_or hle hC).elim (fun h ↦ Or.inl ⟨hC, h⟩) (fun h ↦ Or.inr ⟨hC, h⟩),
            fun h ↦ h.elim And.left And.left⟩
      have hXeq : π₁.parts.filter (· ⊆ X) = π₂.parts.filter (· ⊆ X) :=
        congrArg (fun p ↦ p.1.parts) heq
      have hYeq : π₁.parts.filter (· ⊆ Y) = π₂.parts.filter (· ⊆ Y) :=
        congrArg (fun p ↦ p.2.parts) heq
      apply Finpartition.ext
      rw [hu (Finset.mem_filter.mp h₁).2, hu (Finset.mem_filter.mp h₂).2, hXeq, hYeq]
    · rintro ⟨P, Q⟩ hPQ
      let π := joinTwo hdisj hunion P Q
      have hPQdisj : Disjoint P.parts Q.parts := Finset.disjoint_left.mpr fun A hA hC ↦ by
        obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hA
        exact Finset.disjoint_left.mp hdisj (P.le hA hx) (Q.le hC hx)
      have hle : π ≤ σ := fun A hA ↦
        (Finset.mem_union.mp hA).elim (fun h ↦ ⟨X, hXmem, P.le h⟩) (fun h ↦ ⟨Y, hYmem, Q.le h⟩)
      have hcard3 : π.parts.card = 3 := by
        change (P.parts ∪ Q.parts).card = 3; rw [Finset.card_union_of_disjoint hPQdisj]
        simp only [Pairs, PX, QY, Finset.mem_union, Finset.mem_product, Finset.mem_filter] at hPQ
        rcases hPQ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega
      refine ⟨π, by simp [S3, partitionsOfCard, hcard3, hle], Prod.ext ?_ ?_⟩ <;> ext A <;>
        simp only [Finpartition.ofSubset_parts, π, joinTwo, Finset.mem_filter, Finset.mem_union]
      · refine ⟨fun ⟨h, hAX⟩ ↦ h.elim id fun hQ ↦ ?_, fun hP ↦ ⟨Or.inl hP, P.le hP⟩⟩
        obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts hQ
        exact False.elim (Finset.disjoint_left.mp hdisj (hAX hx) (Q.le hQ hx))
      · refine ⟨fun ⟨h, hAY⟩ ↦ h.elim (fun hP ↦ ?_) id, fun hQ ↦ ⟨Or.inr hQ, Q.le hQ⟩⟩
        obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hP
        exact False.elim (Finset.disjoint_left.mp hdisj (P.le hP hx) (hAY hx))
  rw [hbij, Finset.card_union_of_disjoint hdisjPairs, Finset.card_product, Finset.card_product]
  simp only [PX, QY, card_finpartition_parts_eq]
  have hXc : 1 ≤ X.card := Finset.card_pos.mpr hXne
  have hYc : 1 ≤ Y.card := Finset.card_pos.mpr hYne
  obtain ⟨dx, hdx⟩ := Nat.exists_eq_add_of_le' hXc
  obtain ⟨dy, hdy⟩ := Nat.exists_eq_add_of_le' hYc
  rw [stirlingSecond_two_formula hXc, stirlingSecond_two_formula hYc, hparts, Finset.sum_pair hXY,
    hdx, hdy, Nat.stirlingSecond_one_right dx, Nat.stirlingSecond_one_right dy]
  have hpx : 1 ≤ 2 ^ dx := Nat.one_le_two_pow
  have hpy : 1 ≤ 2 ^ dy := Nat.one_le_two_pow
  simp only [Nat.add_sub_cancel]; omega

/-- Stirling numbers of the second kind count fixed-cardinality party partitions and the
three-block refinements of any two-block party partition. -/
theorem stirling_and_three_block_refinement_count :
    (∀ {m : ℕ}, 1 ≤ m → Nat.stirlingSecond m 2 = 2 ^ (m - 1) - 1) ∧
    (∀ {q : ℕ}, 1 ≤ q →
      2 * (Nat.stirlingSecond q 2 + Nat.stirlingSecond q 3) = 3 ^ (q - 1) - 1 ∧
      ((3 : ℝ) ^ (q - 1) - 1) / 2 =
        (Nat.stirlingSecond q 2 : ℝ) + (Nat.stirlingSecond q 3 : ℝ)) ∧
    (∀ (q k : ℕ), (partitionsOfCard q k).card = Nat.stirlingSecond q k) ∧
    (∀ {q : ℕ} {σ : PartyPartition q}, σ ∈ partitionsOfCard q 2 →
      ((partitionsOfCard q 3).filter (fun π ↦ π ≤ σ)).card + 2 =
        ∑ B ∈ σ.parts, 2 ^ (B.card - 1)) :=
  ⟨fun hm ↦ stirlingSecond_two_formula hm, fun hq ↦ stirlingSecond_two_add_three hq,
   fun q k ↦ by simpa [partitionsOfCard] using card_finpartition_parts_eq Finset.univ k,
   fun hσ ↦ refinement_two_block_equiv_card hσ⟩

private lemma eq_of_le_of_card_parts_eq {q : ℕ} {P Q : PartyPartition q}
    (hle : P ≤ Q) (hcard : P.parts.card = Q.parts.card) : P = Q := by
  let f : Q.parts → P.parts := fun C ↦
    ⟨(Finpartition.exists_le_of_le hle C.2).choose,
      (Finpartition.exists_le_of_le hle C.2).choose_spec.1⟩
  have hfle : ∀ C : Q.parts, (f C).1 ⊆ C.1 := fun C ↦
    (Finpartition.exists_le_of_le hle C.2).choose_spec.2
  have hfinj : Function.Injective f := fun C₁ C₂ hf ↦ by
    obtain ⟨y, hy⟩ := P.nonempty_of_mem_parts (f C₁).2
    exact Subtype.ext (Q.eq_of_mem_parts C₁.2 C₂.2 (hfle C₁ hy) (hfle C₂ (hf ▸ hy)))
  have hfsum : ∑ C : Q.parts, (f C).1.card = ∑ C : Q.parts, C.1.card := by
    have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hfinj, by rw [Fintype.card_coe, Fintype.card_coe, hcard]⟩
    calc ∑ C : Q.parts, (f C).1.card = ∑ A : P.parts, A.1.card :=
          Fintype.sum_bijective f hbij _ _ (fun _ ↦ rfl)
      _ = ∑ C ∈ Q.parts, C.card := by
          rw [Finset.sum_coe_sort P.parts Finset.card, P.sum_card_parts, Q.sum_card_parts]
      _ = ∑ C : Q.parts, C.1.card := (Finset.sum_coe_sort Q.parts Finset.card).symm
  have hsub : Q.parts ⊆ P.parts := fun C hC ↦ by
    have hceq := (Finset.sum_eq_sum_iff_of_le (s := (Finset.univ : Finset Q.parts))
      (fun D _ ↦ Finset.card_le_card (hfle D))).mp hfsum ⟨C, hC⟩ (Finset.mem_univ _)
    have heqC : (f ⟨C, hC⟩).1 = C := Finset.eq_of_subset_of_card_le (hfle ⟨C, hC⟩) hceq.ge
    rw [← heqC]; exact (f ⟨C, hC⟩).2
  exact (Finpartition.ext (Finset.eq_of_subset_of_card_le hsub hcard.le)).symm

private lemma filter_le_eq_singleton {q k : ℕ} {σ : PartyPartition q}
    (hσ : σ ∈ partitionsOfCard q k) :
    (partitionsOfCard q k).filter (fun τ ↦ σ ≤ τ) = {σ} ∧
    (partitionsOfCard q k).filter (fun ρ ↦ ρ ≤ σ) = {σ} := by
  have hk : σ.parts.card = k := (Finset.mem_filter.mp hσ).2
  refine ⟨Finset.ext fun τ ↦ ?_, Finset.ext fun ρ ↦ ?_⟩ <;>
    simp only [Finset.mem_filter, partitionsOfCard, Finset.mem_univ, true_and,
      Finset.mem_singleton]
  · refine ⟨fun ⟨hτ, hle⟩ ↦ (eq_of_le_of_card_parts_eq hle (hk.trans hτ.symm)).symm, ?_⟩
    rintro rfl; exact ⟨hk, le_rfl⟩
  · refine ⟨fun ⟨hρ, hle⟩ ↦ eq_of_le_of_card_parts_eq hle (hρ.trans hk.symm), ?_⟩
    rintro rfl; exact ⟨hk, le_rfl⟩

private lemma upperRankSum_eq_self_of_card_two {q : ℕ} (r : PartyPartition q → ℝ)
    {σ : PartyPartition q} (hσ : σ ∈ partitionsOfCard q 2) :
    upperRankSum r σ = r σ := by
  have hk : σ.parts.card = 2 := (Finset.mem_filter.mp hσ).2
  have hf3 : (partitionsOfCard q 3).filter (fun τ ↦ σ ≤ τ) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun τ hτ hle ↦ by
      have hτ3 := (Finset.mem_filter.mp hτ).2; have hm := Finpartition.card_mono hle; omega
  unfold upperRankSum twoOrThreePartitions
  rw [Finset.filter_union, (filter_le_eq_singleton hσ).1, hf3, Finset.union_empty,
    Finset.sum_singleton]

private lemma upperRankSum_eq_of_card_three {q : ℕ} (r : PartyPartition q → ℝ)
    {π : PartyPartition q} (hπ : π ∈ partitionsOfCard q 3) :
    upperRankSum r π = r π + ∑ σ ∈ (partitionsOfCard q 2).filter (fun σ ↦ π ≤ σ), r σ := by
  have hdisj : Disjoint ((partitionsOfCard q 2).filter (fun σ ↦ π ≤ σ))
      ((partitionsOfCard q 3).filter (fun σ ↦ π ≤ σ)) :=
    (disjoint_partitionsOfCard q (by decide)).mono (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)
  unfold upperRankSum twoOrThreePartitions
  rw [Finset.filter_union, Finset.sum_union hdisj, (filter_le_eq_singleton hπ).1,
    Finset.sum_singleton, add_comm]

/-- Counting three-block refinements expresses any sum over two- and three-block party partitions
through two- and three-block upper sums, while the poset transpose is surjective and upper-sum data
on two- and three-block partitions uniquely determine all two- and three-block values. -/
theorem coarse_upper_sum_reduction_and_triangular_inversion :
    (∀ {q : ℕ}, 3 ≤ q → ∀ (r : PartyPartition q → ℝ),
      ∑ σ ∈ twoOrThreePartitions q, r σ =
        ∑ π ∈ partitionsOfCard q 3, upperRankSum r π +
        ∑ σ ∈ partitionsOfCard q 2,
          ((3 : ℝ) - ∑ B ∈ σ.parts, (2 : ℝ) ^ (B.card - 1)) * upperRankSum r σ) ∧
    (∀ {q : ℕ} (c r : PartyPartition q → ℝ),
      ∑ ρ ∈ nontrivialPartitions q,
        c ρ * ((3 : ℝ) ^ (2 - (ρ.parts.card : ℤ)) * upperRankSum r ρ) =
      ∑ σ ∈ twoOrThreePartitions q, coarseWeight c σ * r σ) ∧
    (∀ {q : ℕ} (w : PartyPartition q → ℝ),
      ∃ c : PartyPartition q → ℝ,
        (∀ ρ ∉ twoOrThreePartitions q, c ρ = 0) ∧
        ∀ σ ∈ twoOrThreePartitions q, coarseWeight c σ = w σ) ∧
    (∀ {q : ℕ} (r₁ r₂ : PartyPartition q → ℝ),
      (∀ σ ∈ partitionsOfCard q 2, upperRankSum r₁ σ = upperRankSum r₂ σ) →
      (∀ π ∈ partitionsOfCard q 3, upperRankSum r₁ π = upperRankSum r₂ π) →
      (∀ σ ∈ twoOrThreePartitions q, r₁ σ = r₂ σ) ∧
      (∀ ρ : PartyPartition q, upperRankSum r₁ ρ = upperRankSum r₂ ρ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q _hq r
    rw [twoOrThreePartitions, Finset.sum_union (disjoint_partitionsOfCard q (by decide))]
    have hsum3 : ∑ π ∈ partitionsOfCard q 3, upperRankSum r π =
        ∑ π ∈ partitionsOfCard q 3, r π +
        ∑ π ∈ partitionsOfCard q 3, ∑ σ ∈ (partitionsOfCard q 2).filter (fun σ ↦ π ≤ σ), r σ := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun π hπ ↦ upperRankSum_eq_of_card_three r hπ
    have hswap : ∑ π ∈ partitionsOfCard q 3,
          ∑ σ ∈ (partitionsOfCard q 2).filter (fun σ ↦ π ≤ σ), r σ =
        ∑ σ ∈ partitionsOfCard q 2,
          (((partitionsOfCard q 3).filter (fun π ↦ π ≤ σ)).card : ℝ) * r σ := by
      simp_rw [Finset.sum_filter]; rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ ↦ by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hsum2 : ∑ σ ∈ partitionsOfCard q 2,
          ((3 : ℝ) - ∑ B ∈ σ.parts, (2 : ℝ) ^ (B.card - 1)) * upperRankSum r σ =
        ∑ σ ∈ partitionsOfCard q 2,
          (1 - (((partitionsOfCard q 3).filter (fun π ↦ π ≤ σ)).card : ℝ)) * r σ :=
      Finset.sum_congr rfl fun σ hσ ↦ by
        rw [upperRankSum_eq_self_of_card_two r hσ]
        have hrefR : (((partitionsOfCard q 3).filter (fun π ↦ π ≤ σ)).card : ℝ) + 2 =
            ∑ B ∈ σ.parts, (2 : ℝ) ^ (B.card - 1) := by
          exact_mod_cast refinement_two_block_equiv_card hσ
        congr 1; linarith
    have hcomb : ∑ σ ∈ partitionsOfCard q 2,
          (((partitionsOfCard q 3).filter (fun π ↦ π ≤ σ)).card : ℝ) * r σ +
        ∑ σ ∈ partitionsOfCard q 2,
          (1 - (((partitionsOfCard q 3).filter (fun π ↦ π ≤ σ)).card : ℝ)) * r σ =
        ∑ σ ∈ partitionsOfCard q 2, r σ := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hsum3, hswap, hsum2]; linarith
  · intro q c r
    unfold upperRankSum coarseWeight
    simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_filter]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by split_ifs <;> ring
  · intro q w
    let c : PartyPartition q → ℝ := fun ρ ↦
      if ρ.parts.card = 3 then 3 * w ρ
      else if ρ.parts.card = 2 then
        w ρ - ∑ π ∈ (partitionsOfCard q 3).filter (fun π ↦ π ≤ ρ), w π
      else 0
    refine ⟨c, fun ρ hρ ↦ ?_, fun σ hσ ↦ ?_⟩
    · simp only [twoOrThreePartitions, partitionsOfCard, Finset.mem_union,
        Finset.mem_filter, Finset.mem_univ, true_and] at hρ
      push Not at hρ; simp [c, hρ.1, hρ.2]
    · have hsupp : ∀ ρ ∈ (nontrivialPartitions q).filter (fun ρ ↦ ρ ≤ σ),
          ρ ∉ (twoOrThreePartitions q).filter (fun ρ ↦ ρ ≤ σ) →
          (3 : ℝ) ^ (2 - (ρ.parts.card : ℤ)) * c ρ = 0 := fun ρ hρ1 hρ2 ↦ by
        have hnot : ρ ∉ twoOrThreePartitions q := fun h ↦
          hρ2 (Finset.mem_filter.mpr ⟨h, (Finset.mem_filter.mp hρ1).2⟩)
        simp only [twoOrThreePartitions, partitionsOfCard, Finset.mem_union,
          Finset.mem_filter, Finset.mem_univ, true_and] at hnot
        push Not at hnot; simp [c, hnot.1, hnot.2]
      have hsub : (twoOrThreePartitions q).filter (fun ρ ↦ ρ ≤ σ) ⊆
          (nontrivialPartitions q).filter (fun ρ ↦ ρ ≤ σ) := fun ρ hρ ↦ by
        simp only [Finset.mem_filter, twoOrThreePartitions, partitionsOfCard,
          nontrivialPartitions, Finset.mem_union, Finset.mem_univ, true_and] at hρ ⊢
        rcases hρ with ⟨h | h, hle⟩ <;> exact ⟨by omega, hle⟩
      unfold coarseWeight; rw [← Finset.sum_subset hsub hsupp]
      have hdisj : Disjoint ((partitionsOfCard q 2).filter (fun ρ ↦ ρ ≤ σ))
          ((partitionsOfCard q 3).filter (fun ρ ↦ ρ ≤ σ)) :=
        (disjoint_partitionsOfCard q (by decide)).mono (Finset.filter_subset _ _)
          (Finset.filter_subset _ _)
      rw [twoOrThreePartitions, Finset.filter_union, Finset.sum_union hdisj]
      rcases Finset.mem_union.mp hσ with hσ2 | hσ3
      · have hσcard : σ.parts.card = 2 := (Finset.mem_filter.mp hσ2).2
        rw [(filter_le_eq_singleton hσ2).2, Finset.sum_singleton]
        have hcσ : (3 : ℝ) ^ (2 - (σ.parts.card : ℤ)) * c σ =
            w σ - ∑ π ∈ (partitionsOfCard q 3).filter (fun π ↦ π ≤ σ), w π := by simp [c, hσcard]
        have hc3 : ∑ ρ ∈ (partitionsOfCard q 3).filter (fun ρ ↦ ρ ≤ σ),
            (3 : ℝ) ^ (2 - (ρ.parts.card : ℤ)) * c ρ =
            ∑ ρ ∈ (partitionsOfCard q 3).filter (fun ρ ↦ ρ ≤ σ), w ρ :=
          Finset.sum_congr rfl fun ρ hρ ↦ by
            have hρcard : ρ.parts.card = 3 := (Finset.mem_filter.mp (Finset.mem_filter.mp hρ).1).2
            simp only [c, hρcard, ↓reduceIte]; norm_num; ring
        rw [hcσ, hc3]; ring
      · have hσcard : σ.parts.card = 3 := (Finset.mem_filter.mp hσ3).2
        have hf2 : (partitionsOfCard q 2).filter (fun ρ ↦ ρ ≤ σ) = ∅ :=
          Finset.filter_eq_empty_iff.mpr fun ρ hρ hle ↦ by
            have hρ2 := (Finset.mem_filter.mp hρ).2; have hm := Finpartition.card_mono hle; omega
        rw [hf2, (filter_le_eq_singleton hσ3).2, Finset.sum_empty, zero_add, Finset.sum_singleton]
        simp only [c, hσcard, ↓reduceIte]; norm_num; ring
  · intro q r₁ r₂ h2 h3
    have h2eq : ∀ σ ∈ partitionsOfCard q 2, r₁ σ = r₂ σ := fun σ hσ ↦ by
      linarith [upperRankSum_eq_self_of_card_two r₁ hσ,
        upperRankSum_eq_self_of_card_two r₂ hσ, h2 σ hσ]
    have h3eq : ∀ π ∈ partitionsOfCard q 3, r₁ π = r₂ π := fun π hπ ↦ by
      have hsub : ∑ σ ∈ (partitionsOfCard q 2).filter (fun σ ↦ π ≤ σ), r₁ σ =
          ∑ σ ∈ (partitionsOfCard q 2).filter (fun σ ↦ π ≤ σ), r₂ σ :=
        Finset.sum_congr rfl fun σ hσ ↦ h2eq σ (Finset.mem_filter.mp hσ).1
      linarith [upperRankSum_eq_of_card_three r₁ hπ,
        upperRankSum_eq_of_card_three r₂ hπ, h3 π hπ]
    have hall : ∀ σ ∈ twoOrThreePartitions q, r₁ σ = r₂ σ := fun σ hσ ↦
      (Finset.mem_union.mp hσ).elim (h2eq σ) (h3eq σ)
    exact ⟨hall, fun ρ ↦ Finset.sum_congr rfl fun σ hσ ↦ hall σ (Finset.mem_filter.mp hσ).1⟩

/-- For any symmetric matrix over `ZMod 2` and any two-block party partition `σ = {X, Y}`,
the partition-masked adjacency matrix is permutation-equivalent to a symmetric anti-diagonal
block matrix and therefore has rank equal to twice the rank of the off-diagonal block `Γ_{X,Y}`. -/
theorem bipartite_masked_antidiagonal_rank {N q : ℕ}
    (Γ : Matrix (Fin N) (Fin N) (ZMod 2)) (hΓ : Γ.IsSymm)
    (col : Fin N → Fin q) {σ : PartyPartition q} (_hσ : σ ∈ partitionsOfCard q 2)
    {X Y : Finset (Fin q)} (hparts : σ.parts = {X, Y}) (hXY : X ≠ Y) :
    partitionRank Γ col σ = 2 * (offDiagBlock Γ col X Y).rank := by
  classical
  have hXmem : X ∈ σ.parts := by simp [hparts]
  have hYmem : Y ∈ σ.parts := by simp [hparts]
  have hdisj : Disjoint X Y := σ.disjoint hXmem hYmem hXY
  have hunion : X ∪ Y = Finset.univ := by simpa [hparts] using σ.sup_parts
  have hnotX_Y : ∀ u : Fin N, col u ∉ X → col u ∈ Y := fun u hn ↦
    (Finset.mem_union.mp (hunion.symm ▸ Finset.mem_univ (col u))).resolve_left hn
  let IX := {u : Fin N // col u ∈ X}
  let IY := {v : Fin N // col v ∈ Y}
  let e : IX ⊕ IY ≃ Fin N :=
    { toFun := Sum.elim Subtype.val Subtype.val
      invFun := fun u ↦ if h : col u ∈ X then Sum.inl ⟨u, h⟩ else Sum.inr ⟨u, hnotX_Y u h⟩
      left_inv := fun s ↦ by
        rcases s with ⟨u, hu⟩ | ⟨v, hv⟩
        · simp [hu]
        · simp [show col v ∉ X from fun hX ↦ Finset.disjoint_left.mp hdisj hX hv]
      right_inv := fun u ↦ by by_cases h : col u ∈ X <;> simp [h] }
  let B : Matrix IX IY (ZMod 2) := offDiagBlock Γ col X Y
  have hsub : (maskedAdj Γ col σ).submatrix e e = Matrix.fromBlocks 0 B Bᵀ 0 := by
    ext (u | u) (v | v)
    · simp [e, maskedAdj, σ.part_eq_of_mem hXmem u.2, σ.part_eq_of_mem hXmem v.2]
    · simp [e, maskedAdj, B, offDiagBlock,
        σ.part_eq_of_mem hXmem u.2, σ.part_eq_of_mem hYmem v.2, hXY]
    · simpa [e, maskedAdj, B, offDiagBlock, σ.part_eq_of_mem hYmem u.2,
        σ.part_eq_of_mem hXmem v.2, hXY.symm, Matrix.transpose_apply] using
        (hΓ.apply u.1 v.1).symm
    · simp [e, maskedAdj, σ.part_eq_of_mem hYmem u.2, σ.part_eq_of_mem hYmem v.2]
  let M : Matrix (IX ⊕ IY) (IX ⊕ IY) (ZMod 2) := Matrix.fromBlocks 0 B Bᵀ 0
  have hrankEq : partitionRank Γ col σ = M.rank := by
    unfold partitionRank; rw [← (maskedAdj Γ col σ).rank_submatrix e e, hsub]
  let rangeEquiv : LinearMap.range M.mulVecLin ≃ₗ[ZMod 2]
      (LinearMap.range B.mulVecLin) × (LinearMap.range Bᵀ.mulVecLin) :=
    { toFun := fun w ↦
        (⟨w.1 ∘ Sum.inl, by
            obtain ⟨z, hz⟩ := w.2; refine ⟨z ∘ Sum.inr, funext fun i ↦ ?_⟩
            simpa only [M, Matrix.mulVecLin_apply, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec,
              zero_add, Sum.elim_inl, Function.comp_apply] using congrFun hz (Sum.inl i)⟩,
         ⟨w.1 ∘ Sum.inr, by
            obtain ⟨z, hz⟩ := w.2; refine ⟨z ∘ Sum.inl, funext fun j ↦ ?_⟩
            simpa only [M, Matrix.mulVecLin_apply, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec,
              add_zero, Sum.elim_inr, Function.comp_apply] using congrFun hz (Sum.inr j)⟩)
      invFun := fun p ↦
        ⟨Sum.elim p.1.1 p.2.1, by
          obtain ⟨y, hy⟩ := p.1.2; obtain ⟨x, hx⟩ := p.2.2
          refine ⟨Sum.elim x y, funext fun s ↦ ?_⟩; rcases s with i | j
          · simpa only [M, Matrix.mulVecLin_apply, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec,
              zero_add, Sum.elim_inl, Sum.elim_comp_inr] using congrFun hy i
          · simpa only [M, Matrix.mulVecLin_apply, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec,
              add_zero, Sum.elim_inr, Sum.elim_comp_inl] using congrFun hx j⟩
      map_add' := fun _ _ ↦ by ext <;> rfl
      map_smul' := fun _ _ ↦ by ext <;> rfl
      left_inv := fun _ ↦ by ext (i | j) <;> rfl
      right_inv := fun _ ↦ by ext <;> rfl }
  rw [hrankEq, Matrix.rank, LinearEquiv.finrank_eq rangeEquiv, Module.finrank_prod]
  change B.rank + Bᵀ.rank = 2 * B.rank; rw [Matrix.rank_transpose, two_mul]

end D5.S3.Combinatorics.Partitions.CoarseThreeBlockRefinement
