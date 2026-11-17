/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The reflected-column restriction of the frozen width-six proper successor image. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed owner adapters on the live path of HardinA229752.result)
extend: proof_shape=bind-only; consumers=proper_extend,raw_extend,raw_iff_owner
raw5: proof_shape=bind-only; consumers=raw_extend,raw_iff_owner,weighted
proper_extend: proof_shape=bind-only; consumers=raw_iff_owner,transition_counts
raw_extend: proof_shape=bind-only; consumers=raw_iff_owner
raw_iff_owner: proof_shape=bind-only; consumers=weighted
weighted: proof_shape=bind-only; consumers=transition_counts
owner_matrix: proof_shape=bind-only; consumers=transition_counts
transition_counts: proof_shape=bind-only; consumers=Width5.Certificate.transition_counts
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.ZeroTemperature
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData

/-! Proper successor rows are exact images of the original zone relation. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.ZeroTemperature
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip

set_option maxRecDepth 100000

def extend (p : Row) : Width6.Data.Row := ![p 0, p 1, p 2, p 3, p 4, p 3]

def raw5 (p r : Row) : Prop :=
  bondDefects between p r + bondDefects horizontal r r = 0

private local instance (p r : Row) : Decidable (raw5 p r) :=
  inferInstanceAs (Decidable (_ = 0))

set_option maxHeartbeats 2000000 in
theorem proper_extend (p : Row) :
    bondDefects Width6.Data.horizontal (extend p) (extend p) = 0 ↔
      bondDefects Width5.Data.horizontal p p = 0 := by
  simp only [bondDefects, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp [Width5.Data.horizontal, Width6.Data.horizontal,
    D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData.horizontal,
    D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData.horizontal,
    extend, Fin.forall_fin_succ, ne_comm] <;> tauto

set_option maxHeartbeats 2000000 in
theorem raw_extend (p r : Row) :
    Width6.ZeroTemperature.raw (extend p) (extend r) ↔ raw5 p r := by
  simp only [Width6.ZeroTemperature.raw, raw5, Nat.add_eq_zero_iff,
    bondDefects, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp [Width5.Data.between, Width6.Data.between,
    Width5.Data.horizontal, Width6.Data.horizontal,
    D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData.horizontal,
    D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData.horizontal,
    extend, Fin.forall_fin_succ, ne_comm] <;> tauto

theorem raw_iff_owner (p r : Row)
    (hp : bondDefects Width5.Data.horizontal p p = 0) :
    raw5 p r ↔ ∃ v ∈ offsetChoices (Width6.ZeroTemperature.offsets (extend p)),
      r = fun j => v ^^^ p j := by
  rw [← raw_extend, Width6.ZeroTemperature.raw_iff_shift _ _
    ((proper_extend p).mpr hp)]
  constructor
  · rintro ⟨v, hv, he⟩
    refine ⟨v, hv, ?_⟩
    funext j
    have h := congrFun he j.castSucc
    fin_cases j <;> simpa [extend] using h
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v, hv, ?_⟩
    funext j
    fin_cases j <;> rfl

private theorem weighted (p : Row) (hp : bondDefects horizontal p p = 0)
    (w : Row → ℤ) :
    (∑ r : Row, if raw5 p r then w r else 0) =
      ∑ v ∈ offsetChoices (Width6.ZeroTemperature.offsets (extend p)),
        w (fun j => v ^^^ p j) := by
  classical
  have hi : Function.Injective (fun v : Fin 4 => fun j : Fin 5 => v ^^^ p j) := by
    intro a b hab
    have h := congrFun hab 0
    change a ^^^ p 0 = b ^^^ p 0 at h
    rw [Fin.xor_comm a (p 0), Fin.xor_comm b (p 0)] at h
    exact xor_cancel (p 0) a b |>.mp h
  have hs : Finset.univ.filter (raw5 p) =
      (offsetChoices (Width6.ZeroTemperature.offsets (extend p))).image
        (fun v => fun j => v ^^^ p j) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    simpa only [eq_comm] using raw_iff_owner p r hp
  rw [← Finset.sum_filter, hs, Finset.sum_image]
  exact fun _ _ _ _ h => hi h

private theorem owner_matrix (p : Row) (hp : bondDefects horizontal p p = 0)
    (s : Fin 43) :
    (∑ v ∈ offsetChoices (Width6.ZeroTemperature.offsets (extend p)),
      if cl (fun j => v ^^^ p j) 0 = s then (1 : ℤ) else 0) = T (cl p 0) s := by
  have hc (v : Fin 4) : cl (fun j => v ^^^ p j) 0 = cl p 0 := by
    simp only [cl, xor_cancel]
  simp_rw [hc]
  have table :
      (∀ s : Fin 43, T 15 s = if 15 = s then 1 else 0) ∧
      (∀ s : Fin 43, T 17 s = if 17 = s then 2 else 0) ∧
      (∀ s : Fin 43, T 30 s = 0) := by decide +kernel
  have h : ∀ a b c d : Fin 4,
      let q : Row := ![0, a, b, c, d]
      bondDefects horizontal q q = 0 →
      (cl q 0 = 15 ∧ (offsetChoices (Width6.ZeroTemperature.offsets (extend q))).card = 1) ∨
      (cl q 0 = 17 ∧ (offsetChoices (Width6.ZeroTemperature.offsets (extend q))).card = 2) ∨
      (cl q 0 = 30 ∧ (offsetChoices (Width6.ZeroTemperature.offsets (extend q))).card = 0) := by
    intro a b
    fin_cases a <;> fin_cases b <;> decide +kernel
  let q : Row := fun j => p 0 ^^^ p j
  have heq : q = ![0, q 1, q 2, q 3, q 4] := by
    funext j
    fin_cases j <;> simp [q]
  have hpq : bondDefects horizontal q q = 0 := by
    simpa only [bondDefects, q, xor_cancel] using hp
  have hcl : cl q 0 = cl p 0 := by simp only [q, cl, xor_cancel]
  have hoff : Width6.ZeroTemperature.offsets (extend q) =
      Width6.ZeroTemperature.offsets (extend p) := by
    funext j
    fin_cases j <;> simp [Width6.ZeroTemperature.offsets, extend, q] <;>
      exact (Fin.xor_comm 0 _).trans (Fin.xor_zero _)
  have hh := h (q 1) (q 2) (q 3) (q 4)
  rw [← heq] at hh
  rcases hh hpq with ⟨hc, hn⟩ | ⟨hc, hn⟩ | ⟨hc, hn⟩
  · rw [hcl] at hc
    rw [hoff] at hn
    rw [hc, table.1]
    simp [hn]
  · rw [hcl] at hc
    rw [hoff] at hn
    rw [hc, table.2.1]
    simp [hn]
  · rw [hcl] at hc
    rw [hoff] at hn
    rw [hc, table.2.2]
    simp [hn, ← Finset.card_eq_zero]

theorem transition_counts (p : Row) (hp : bondDefects horizontal p p = 0)
    (s : Fin 43) :
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ 0 ∧
      cl r (0 - (bondDefects between p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p 0) s := by
  have hw := weighted p hp (fun r => if cl r 0 = s then (1 : ℤ) else 0)
  have ho := owner_matrix p hp s
  calc
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ 0 ∧
        cl r (0 - (bondDefects between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) =
        ∑ r : Row, if raw5 p r then (if cl r 0 = s then (1 : ℤ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases h : raw5 p r
      · have hz : bondDefects between p r + bondDefects horizontal r r = 0 := h
        simp [hz, h]
      · have hn : ¬ bondDefects between p r + bondDefects horizontal r r ≤ 0 := by
          change ¬ _ = 0 at h
          omega
        simp [hn, h]
    _ = ∑ v ∈ offsetChoices (Width6.ZeroTemperature.offsets (extend p)),
        if cl (fun j => v ^^^ p j) 0 = s then (1 : ℤ) else 0 := hw
    _ = T (cl p 0) s := ho

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.ZeroTemperature
