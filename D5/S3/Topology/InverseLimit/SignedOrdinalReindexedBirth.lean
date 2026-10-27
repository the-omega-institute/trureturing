/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Total tag decoding preserves whole birth enumerations and ordinary reads. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalReindexCodes

/-! Holes decode to ordinary zero while every tag retains its own code. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function
open scoped Ordinal Cardinal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalReindexedBirth

open SignedProperLimit SignedBirthEnumeration SignedOrdinalHistoryBirth
open SignedOrdinalHistoryState SignedOrdinalReindexCodes

variable {θ : Stage} {C : Set (Cube (ord θ))} (W : BirthPack C)

/-- The inverse on the code image, with ordinary zero filling every hole. -/
noncomputable def decodeTag (δ : Label) : Tag W := by
  classical
  exact if h : ∃ z, code W z = δ then Classical.choose h else zeroTag W

theorem decode_code (z : Tag W) : decodeTag W (code W z) = z := by
  classical
  have h : ∃ y, code W y = code W z := ⟨z, rfl⟩
  simp only [decodeTag, dite_eq_left h]
  exact code_injective W (Classical.choose_spec h)

private theorem decode_hole (δ : Label) (hδ : Hole W δ) :
    decodeTag W δ = zeroTag W := by
  classical
  change ¬ ∃ z, code W z = δ at hδ
  simp only [decodeTag, dite_eq_right hδ]

private theorem decode_zero : decodeTag W zeroLabel = zeroTag W := by
  rw [← code_zero W]
  exact decode_code W (zeroTag W)

/-- Coloring an ordinary-zero occurrence leaves its decoded original tag fixed. -/
theorem ordinaryIndex_decode (d a : Label) :
    decodeTag W (ordinaryIndex W d a) = .inl d := by
  classical
  unfold ordinaryIndex
  split_ifs with hd hc
  · subst d
    rcases hc.2 with hz | hh
    · rw [hz]
      exact decode_zero W
    · exact decode_hole W _ hh
  · subst d
    exact decode_zero W
  · exact decode_code W (.inl d)

/-- One label for both the support read and the original measure target. -/
noncomputable def eventIndex (z : Tag W) (a : Label) : Label :=
  match z with
  | .inl d => ordinaryIndex W d a
  | .inr p => code W (.inr p)

theorem eventIndex_decode (z : Tag W) (a : Label) :
    decodeTag W (eventIndex W z a) = z := by
  cases z with
  | inl d => exact ordinaryIndex_decode W d a
  | inr p => exact decode_code W (.inr p)

theorem eventIndex_le (z : Tag W) (a : Label) (ha : Occurs W z a) :
    eventIndex W z a ≤ a := by
  cases z with
  | inl d => exact ordinaryIndex_le W d a ha
  | inr p => exact code_le_occurrence W (.inr p) a ha

/-- Every new label is assigned cofinally often on its own fixed birth row. -/
theorem eventIndex_cofinal (δ base : Label) :
    ∃ a : Label, base < a ∧ ∃ z : Tag W, Occurs W z a ∧ eventIndex W z a = δ := by
  classical
  by_cases hδ : δ ∈ Set.range (code W)
  · obtain ⟨z, rfl⟩ := hδ
    by_cases hz : z = zeroTag W
    · subst z
      obtain ⟨a, hb, _, _, ha, he⟩ := hole_cofinal W zeroLabel base (Or.inl rfl)
      exact ⟨a, hb, zeroTag W, ha, he.trans (code_zero W).symm⟩
    · obtain ⟨a, hb, ha⟩ := occurs_cofinal W z base
      refine ⟨a, hb, z, ha, ?_⟩
      cases z with
      | inl d =>
        have hd : d ≠ zeroLabel := by
          intro hd
          exact hz (congrArg Sum.inl hd)
        simp only [eventIndex, ordinaryIndex, ite_eq_right hd]
      | inr p => rfl
  · obtain ⟨a, hb, _, _, ha, he⟩ := hole_cofinal W δ base (Or.inr hδ)
    exact ⟨a, hb, zeroTag W, ha, he⟩

/-- The decoded old measure label is eligible whenever its new label is eligible. -/
noncomputable def measureIndex (δ : Label) : {d : Label // d ≤ δ} := by
  classical
  refine ⟨target W (decodeTag W δ), ?_⟩
  by_cases h : ∃ z, code W z = δ
  · have he : code W (decodeTag W δ) = δ := by
      simpa only [decodeTag, dite_eq_left h] using Classical.choose_spec h
    exact (target_le_code W (decodeTag W δ)).trans he.le
  · have he : decodeTag W δ = zeroTag W := by
      simp only [decodeTag, dite_eq_right h]
    rw [he]
    exact show (0 : Ordinal.{0}) ≤ δ.1 from bot_le

/-- A delayed support is independent of its old measure target. The original
ordinary codes keep both whole enumerations onto, and V and B stay fixed. -/
noncomputable def reindexBirth (delayedSupport : SupportFamily C) : BirthPack C where
  U δ := match decodeTag W δ with
    | .inl d => W.U d
    | .inr _ => delayedSupport
  Uonto := by
    intro V
    obtain ⟨d, hd⟩ := W.Uonto V
    refine ⟨code W (.inl d), ?_⟩
    change (match decodeTag W (code W (.inl d)) with
      | .inl e => W.U e | .inr _ => delayedSupport) = V
    rw [decode_code]
    exact hd
  B := W.B
  Bonto := W.Bonto
  V := W.V
  nu δ := W.nu (measureIndex W δ).1
  nuonto := by
    intro μ
    obtain ⟨d, hd⟩ := W.nuonto μ
    refine ⟨code W (.inl d), ?_⟩
    change W.nu (target W (decodeTag W (code W (.inl d)))) = μ
    rw [decode_code]
    exact hd

/-- Every tag reads both enumerations at the same new label, including every
colored ordinary-zero event and every delayed target at every stage. -/
theorem event_read (delayedSupport : SupportFamily C) (z : Tag W) (a : Label) :
    (reindexBirth W delayedSupport).U (eventIndex W z a) =
      (match z with | .inl d => W.U d | .inr _ => delayedSupport) ∧
    (reindexBirth W delayedSupport).nu (eventIndex W z a) = W.nu (target W z) := by
  constructor
  · change (match decodeTag W (eventIndex W z a) with
      | .inl e => W.U e | .inr _ => delayedSupport) = _
    rw [eventIndex_decode]
  · change W.nu (target W (decodeTag W (eventIndex W z a))) = _
    rw [eventIndex_decode]

end D5.S3.Topology.InverseLimit.SignedOrdinalReindexedBirth
