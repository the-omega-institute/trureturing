/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229753.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature.transition_counts
   digest: The frozen zone owner's exact proper successor image. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed owner adapters on the live path of HardinA229753.result)
twoRows: proof_shape=bind-only; consumers=raw_pair,exact_image
raw: proof_shape=bind-only; consumers=raw_pair,raw_iff_shift,weighted
raw_pair: proof_shape=bind-only; consumers=exact_image
exact_image: proof_shape=bind-only; consumers=raw_iff_shift
offsets: proof_shape=bind-only; consumers=raw_iff_shift,weighted
raw_iff_shift: proof_shape=bind-only; consumers=weighted
weighted: proof_shape=bind-only; consumers=transition_counts
owner_matrix: proof_shape=bind-only; consumers=transition_counts
transition_counts: proof_shape=bind-only; consumers=Width6.Certificate.transition_counts
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData

/-! Proper zero-defect successors are the exact allowed-shift image of the frozen owner. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.ZeroTemperature
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip

set_option maxRecDepth 100000


def twoRows (p r : Row) : Fin 2 × Fin 6 → Fin 4 :=
  fun ij => if ij.1 = 0 then p ij.2 else r ij.2

def raw (p r : Row) : Prop :=
  bondDefects between p r + bondDefects horizontal r r = 0

private local instance (p r : Row) : Decidable (raw p r) :=
  inferInstanceAs (Decidable (_ = 0))

set_option maxHeartbeats 2000000 in
private theorem raw_pair (p r : Row) :
    Proper (twoRows p r) ↔ bondDefects horizontal p p = 0 ∧ raw p r := by
  simp only [Proper, twoRows, Prod.forall, Fin.forall_fin_succ, Fin.isValue,
    Nat.reduceAdd, Fin.val_zero, Fin.val_succ, Fin.succ_zero_eq_one,
    Finset.card_eq_zero, Finset.filter_eq_empty_iff, bondDefects, raw,
    Nat.add_eq_zero_iff, between, horizontal,
    D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData.horizontal,
    Finset.mem_image, Fin.exists_fin_succ]
  simp [ne_comm]
  tauto

private theorem exact_image (p r : Row) (hp : bondDefects horizontal p p = 0) :
    raw p r ↔ ∃ u : Fin 2 → Fin 4,
      (u, fun j => p 0 ^^^ p j) ∈ D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.zones 2 ∧
      ∀ j, p j = u 0 ^^^ (p 0 ^^^ p j) ∧ r j = u 1 ^^^ (p 0 ^^^ p j) := by
  constructor
  · intro hr
    have hc := (raw_pair p r).mpr ⟨hp, hr⟩
    let c := (⟨twoRows p r, hc⟩ : {c // Proper c})
    let z := D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.zoneEquiv (by decide : 0 < 2) c
    refine ⟨fun i => twoRows p r (i, 0), ?_, ?_⟩
    · have hz := z.property
      change ((fun i => twoRows p r (i, 0)),
        (fun j => twoRows p r (0, 0) ^^^ twoRows p r (0, j))) ∈ D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.zones 2 at hz
      exact hz
    · intro j
      have h := congrArg (fun c => c.val)
        ((D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.zoneEquiv (by decide : 0 < 2)).symm_apply_apply c)
      exact ⟨(congrFun h (0, j)).symm, (congrFun h (1, j)).symm⟩
  · rintro ⟨u, hz, he⟩
    let z : {z // z ∈ D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.zones 2} := ⟨(u, fun j => p 0 ^^^ p j), hz⟩
    have hc : Proper (fun ij : Fin 2 × Fin 6 => u ij.1 ^^^ (p 0 ^^^ p ij.2)) :=
      ((D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.zoneEquiv (by decide : 0 < 2)).symm z).property
    have hfun : (fun ij : Fin 2 × Fin 6 => u ij.1 ^^^ (p 0 ^^^ p ij.2)) =
        twoRows p r := by
      funext ij
      rcases ij with ⟨i, j⟩
      fin_cases i
      · exact (he j).1.symm
      · exact (he j).2.symm
    rw [hfun] at hc
    exact ((raw_pair p r).mp hc).2

def offsets (p : Row) : Row := fun j => p 0 ^^^ p j

theorem raw_iff_shift (p r : Row) (hp : bondDefects horizontal p p = 0) :
    raw p r ↔ ∃ v ∈ D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.offsetChoices (offsets p),
      r = fun j => v ^^^ p j := by
  constructor
  · intro hr
    obtain ⟨u, hz, he⟩ := (exact_image p r hp).mp hr
    have ho := (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.zones_iff 1 u (offsets p)).mp hz
    have hu0 : u 0 = p 0 := by simpa using (he 0).1.symm
    refine ⟨u 0 ^^^ u 1, ho.2 (0 : Fin 1), ?_⟩
    funext j
    rw [hu0, Fin.xor_comm (p 0) (u 1), Fin.xor_assoc (show 4 = 2^2 from rfl)]
    exact (he j).2
  · rintro ⟨v, hv, rfl⟩
    have hoff : D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.offsetOK (offsets p) := by
      change p 0 ^^^ p 0 = 0 ∧ ∀ j : Fin 5,
        (p 0 ^^^ p j.castSucc) ^^^ (p 0 ^^^ p j.succ) ≠ 0
      refine ⟨Fin.xor_self _, fun j => ?_⟩
      rw [xor_shift]
      apply (xor_nonzero _ _).mpr
      have hmem : (j.castSucc, j.succ) ∈ horizontal := by
        change (j.castSucc, j.succ) ∈
          Finset.univ.image (fun k : Fin 5 => (k.castSucc, k.succ))
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      exact (Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hp)) hmem
    let u : Fin 2 → Fin 4 := ![p 0, v ^^^ p 0]
    have hz : (u, offsets p) ∈ D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.zones 2 := by
      apply (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.zones_iff 1 u (offsets p)).mpr
      refine ⟨hoff, ?_⟩
      intro i
      fin_cases i
      change p 0 ^^^ (v ^^^ p 0) ∈ offsetChoices (offsets p)
      rw [Fin.xor_comm v (p 0), xor_right_cancel]
      exact hv
    apply (exact_image p _ hp).mpr
    refine ⟨u, hz, fun j => ?_⟩
    constructor
    · simpa [u, xor_right_cancel]
    · simpa [u, xor_right_cancel, Fin.xor_assoc (show 4 = 2^2 from rfl)]

private theorem weighted (p : Row) (hp : bondDefects horizontal p p = 0) (w : Row → ℤ) :
    (∑ r : Row, if raw p r then w r else 0) =
      ∑ v ∈ D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.offsetChoices (offsets p), w (fun j => v ^^^ p j) := by
  classical
  have hi : Function.Injective (fun v : Fin 4 => fun j : Fin 6 => v ^^^ p j) := by
    intro a b hab
    have h := congrFun hab 0
    change a ^^^ p 0 = b ^^^ p 0 at h
    rw [Fin.xor_comm a (p 0), Fin.xor_comm b (p 0)] at h
    exact (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.xor_cancel (p 0) a b).mp h
  have hs : Finset.univ.filter (raw p) =
      (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.offsetChoices (offsets p)).image (fun v => fun j => v ^^^ p j) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    simpa only [eq_comm] using raw_iff_shift p r hp
  rw [← Finset.sum_filter, hs, Finset.sum_image]
  exact fun _ _ _ _ h => hi h

set_option maxHeartbeats 0 in
private theorem owner_matrix (p : Row) (hp : bondDefects horizontal p p = 0) (s : Fin 96) :
    (∑ v ∈ offsetChoices (offsets p),
      if cl (fun j => v ^^^ p j) 0 = s then (1 : ℤ) else 0) = T (cl p 0) s := by
  have hc (v : Fin 4) : cl (fun j => v ^^^ p j) 0 = cl p 0 := by
    simp only [cl, xor_cancel]
  simp_rw [hc]
  have table :
      (∀ s : Fin 96, T 71 s = if 71 = s then 1 else 0) ∧
      (∀ s : Fin 96, T 75 s = if 75 = s then 2 else 0) ∧
      (∀ s : Fin 96, T 90 s = 0) := by decide +kernel
  have h : ∀ a b c d e : Fin 4,
      let q : Row := ![0, a, b, c, d, e]
      bondDefects horizontal q q = 0 →
      (cl q 0 = 71 ∧ (offsetChoices q).card = 1) ∨
      (cl q 0 = 75 ∧ (offsetChoices q).card = 2) ∨
      (cl q 0 = 90 ∧ (offsetChoices q).card = 0) := by
    intro a b
    fin_cases a <;> fin_cases b <;> decide +kernel
  let q := offsets p
  have heq : q = ![0, q 1, q 2, q 3, q 4, q 5] := by
    funext j
    fin_cases j <;> simp [q, offsets]
  have hpq : bondDefects horizontal q q = 0 := by
    simpa only [bondDefects, q, offsets, xor_cancel] using hp
  have hcl : cl q 0 = cl p 0 := by simp only [q, offsets, cl, xor_cancel]
  have hh := h (q 1) (q 2) (q 3) (q 4) (q 5)
  rw [← heq] at hh
  rcases hh hpq with ⟨hc, hn⟩ | ⟨hc, hn⟩ | ⟨hc, hn⟩
  · rw [hcl] at hc
    rw [hc, table.1]
    change (offsetChoices (offsets p)).card = _ at hn
    simp [hn, ← Finset.card_eq_zero]
  · rw [hcl] at hc
    rw [hc, table.2.1]
    change (offsetChoices (offsets p)).card = _ at hn
    simp [hn, ← Finset.card_eq_zero]
  · rw [hcl] at hc
    rw [hc, table.2.2]
    change (offsetChoices (offsets p)).card = _ at hn
    simp [hn, ← Finset.card_eq_zero]

theorem transition_counts (p : Row) (hp : bondDefects horizontal p p = 0) (s : Fin 96) :
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ 0 ∧
      cl r (0 - (bondDefects between p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p 0) s := by
  have hw := weighted p hp (fun r => if cl r 0 = s then (1 : ℤ) else 0)
  have ho := owner_matrix p hp s
  calc
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ 0 ∧
        cl r (0 - (bondDefects between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) =
        ∑ r : Row, if raw p r then (if cl r 0 = s then (1 : ℤ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases h : raw p r
      · have hz : bondDefects between p r + bondDefects horizontal r r = 0 := h
        simp [hz, h]
      · have hn : ¬ bondDefects between p r + bondDefects horizontal r r ≤ 0 := by
          change ¬ _ = 0 at h
          omega
        simp [hn, h]
    _ = ∑ v ∈ D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.offsetChoices
        (offsets p), if cl (fun j => v ^^^ p j) 0 = s then (1 : ℤ) else 0 := hw
    _ = T (cl p 0) s := ho

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.ZeroTemperature
