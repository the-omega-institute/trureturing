/- GID: D5/S3/Combinatorics/Geometry/MiuraCoreColumns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraCoreColumns
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Occupied columns and frozen runs are controlled by actual extrema. -/

/- Finite proofs adapted from Chakshu Gupta, https://github.com/ChakshuGupta13/lab,
commit 0bf8c67f7f5a2e8d44fb88c19fb80337221bbc11,
math/gupta2026degseq/lean/OrigamiCone/OrigamiCone/.
DegreeExtrema.lean: 46a99738b47a3e105a1dc02cdb507aac74bdf884.
SequelEd.lean: 0f95aba54002836654f9b836359d6d392295fd74.
SequelEdActiveCol.lean: bd8603c6642d546d3c635602f4d6bd93374ee848.
SequelEdFrozenCol.lean: b495f2b3adabc743698aa8018def3a66aae8953a.
CC BY 4.0; see docs/reports/miura-suppliers/lab-NOTICE.txt and lab-LICENSE.txt.
Namespaces, imports and selected declaration boundaries are adapted.
Retire these transplants when equivalent suppliers exist in pinned mathlib. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraHeightEnvelope
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Prod

/-! Finite signed contraction and its exact full-grid invariants. -/

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraCoreColumns

open MiuraHeightEnvelope

noncomputable section

variable {m n : ℕ}

instance decAdj (p q : Cell m n) : Decidable (adj p q) := by
  unfold adj; infer_instance

instance decStrictLocalMax (h : Cell m n → ℤ) (v : Cell m n) :
    Decidable (IsStrictLocalMax h v) := by unfold IsStrictLocalMax; infer_instance

instance decStrictLocalMin (h : Cell m n → ℤ) (v : Cell m n) :
    Decidable (IsStrictLocalMin h v) := by unfold IsStrictLocalMin; infer_instance

def IsStrictLocalExtremum (h : Cell m n → ℤ) (v : Cell m n) : Prop :=
  IsStrictLocalMax h v ∨ IsStrictLocalMin h v

instance decStrictLocalExtremum (h : Cell m n → ℤ) (v : Cell m n) :
    Decidable (IsStrictLocalExtremum h v) := by
  unfold IsStrictLocalExtremum; infer_instance

def numExtrema (h : Cell m n → ℤ) : ℕ :=
  (Finset.univ.filter (IsStrictLocalExtremum h)).card

open MiuraHeightEnvelope Finset

variable {m n : ℕ}

def activeColumn (h : Cell m n → ℤ) (j : Fin n) : Prop :=
  ∃ i : Fin m, IsStrictLocalExtremum h (i, j)

instance {h : Cell m n → ℤ} : DecidablePred (activeColumn h) := by
  intro j; unfold activeColumn; infer_instance

def numActiveColumns (h : Cell m n → ℤ) : ℕ :=
  (Finset.univ.filter (activeColumn h)).card

theorem numActiveColumns_le_numExtrema (h : Cell m n → ℤ) :
    numActiveColumns h ≤ numExtrema h := by
  unfold numActiveColumns numExtrema
  set E : Finset (Cell m n) := Finset.univ.filter (IsStrictLocalExtremum h) with hE
  set A : Finset (Fin n) := Finset.univ.filter (activeColumn h) with hA
  suffices A ⊆ E.image Prod.snd by
    calc A.card
        ≤ (E.image Prod.snd).card := Finset.card_le_card this
      _ ≤ E.card := Finset.card_image_le
  intro j hj
  rw [Finset.mem_filter] at hj
  obtain ⟨_, i, hi⟩ := hj
  rw [Finset.mem_image]
  refine ⟨(i, j), ?_, rfl⟩
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hi⟩

def frozenRunStart (h : Cell m n → ℤ) (j : Fin n) : Prop :=
  ¬ activeColumn h j ∧ (j.val = 0 ∨ (0 < j.val ∧ activeColumn h ⟨j.val - 1, by omega⟩))

instance {h : Cell m n → ℤ} : DecidablePred (frozenRunStart h) := by
  intro j; unfold frozenRunStart; infer_instance

def numFrozenRuns (h : Cell m n → ℤ) : ℕ :=
  (Finset.univ.filter (frozenRunStart h)).card

theorem numFrozenRuns_le (h : Cell m n → ℤ) (hn : 0 < n)
    (h0 : activeColumn h ⟨0, hn⟩)
    (hlast : activeColumn h ⟨n - 1, by omega⟩) :
    numFrozenRuns h + 1 ≤ numActiveColumns h := by
  unfold numFrozenRuns numActiveColumns
  set S : Finset (Fin n) := Finset.univ.filter (frozenRunStart h) with hS
  set A : Finset (Fin n) := Finset.univ.filter (activeColumn h) with hA
  have hlast_mem : (⟨n - 1, by omega⟩ : Fin n) ∈ A := by
    rw [hA, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hlast⟩
  have hjpos : ∀ j ∈ S, 0 < j.val := by
    intro j hj
    rw [hS, Finset.mem_filter] at hj
    obtain ⟨_, hfrz⟩ := hj
    rcases hfrz.2 with h0' | ⟨hpos, _⟩
    · exfalso
      apply hfrz.1
      have : j = ⟨0, hn⟩ := by ext; omega
      rw [this]; exact h0
    · exact hpos
  have h_inj : ∀ j₁ ∈ S, ∀ j₂ ∈ S, j₁.val - 1 = j₂.val - 1 → j₁ = j₂ := by
    intro j₁ hj₁ j₂ hj₂ heq
    have p₁ := hjpos j₁ hj₁
    have p₂ := hjpos j₂ hj₂
    ext; omega
  have h_sub : S.image (fun j => (⟨j.val - 1, by omega⟩ : Fin n))
      ⊆ A.erase ⟨n - 1, by omega⟩ := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨j, hjS, hxeq⟩ := hx
    have hjpos' := hjpos j hjS
    rw [hS, Finset.mem_filter] at hjS
    obtain ⟨_, hfrz⟩ := hjS
    rw [Finset.mem_erase]
    constructor
    · intro hcontra
      rw [← hxeq] at hcontra
      have : j.val - 1 = n - 1 := by
        have := Fin.val_eq_of_eq hcontra
        simpa using this
      have hjlt := j.isLt
      omega
    · rw [hA, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hfrz.2 with h0' | ⟨_, hact⟩
      · omega
      · rw [← hxeq]; exact hact
  have h_card_image : (S.image (fun j => (⟨j.val - 1, by omega⟩ : Fin n))).card = S.card :=
    Finset.card_image_of_injOn (fun a ha b hb hab => h_inj a ha b hb (by
      have := Fin.val_eq_of_eq hab; simpa using this))
  have h_le : S.card ≤ (A.erase ⟨n - 1, by omega⟩).card := by
    rw [← h_card_image]; exact Finset.card_le_card h_sub
  rw [Finset.card_erase_of_mem hlast_mem] at h_le
  have hA_pos : 0 < A.card := Finset.card_pos.mpr ⟨_, hlast_mem⟩
  omega

theorem numFrozenRuns_lt_numExtrema (h : Cell m n → ℤ) (hn : 0 < n)
    (h0 : activeColumn h ⟨0, hn⟩)
    (hlast : activeColumn h ⟨n - 1, by omega⟩) :
    numFrozenRuns h + 1 ≤ numExtrema h :=
  le_trans (numFrozenRuns_le h hn h0 hlast) (numActiveColumns_le_numExtrema h)

open MiuraHeightEnvelope

variable {m n : ℕ}

def frozenColumn (h : Cell m n → ℤ) (j : Fin n) : Prop :=
  ∃ (_ : 0 < j.val) (hj1 : j.val + 1 < n),
    ∀ i : Fin m,
      h (i, ⟨j.val - 1, by omega⟩) + h (i, ⟨j.val + 1, hj1⟩) = 2 * h (i, j)

theorem frozenColumn_not_active (h : Cell m n → ℤ)
    (j : Fin n) (hfrz : frozenColumn h j) :
    ¬ activeColumn h j := by
  obtain ⟨hj0, hj1, hsym⟩ := hfrz
  rintro ⟨i, hext⟩
  set jL : Fin n := ⟨j.val - 1, by omega⟩ with hjL
  set jR : Fin n := ⟨j.val + 1, hj1⟩ with hjR
  have hadjL : adj ((i, j) : Cell m n) (i, jL) := by
    unfold adj gdist; simp only [hjL]; omega
  have hadjR : adj ((i, j) : Cell m n) (i, jR) := by
    unfold adj gdist; simp only [hjR]; omega
  have hsum : (h (i, jL) - h (i, j)) + (h (i, jR) - h (i, j)) = 0 := by
    have hs := hsym i; omega
  rcases hext with hmax | hmin
  ·
    have hL := hmax (i, jL) hadjL
    have hR := hmax (i, jR) hadjR
    omega
  ·
    have hL := hmin (i, jL) hadjL
    have hR := hmin (i, jR) hadjR
    omega

end

end D5.S3.Combinatorics.Geometry.MiuraCoreColumns
