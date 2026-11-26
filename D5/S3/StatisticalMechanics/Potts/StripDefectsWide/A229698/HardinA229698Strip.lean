/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698Strip.finite_certificate
   digest: The two-defect extension of the five-row HA quotient. -/

/-
admission_basis: open-problem-resolution (#31594; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229698Strip.result)
a: proof_shape=bind-only; consumers=scale_count, result
finite_certificate: proof_shape=bind-only; consumers=count_transfer, result
count_transfer: proof_shape=bind-only; consumers=result
scale_count: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #31594)
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripCut
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripCut
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripPowers
import Mathlib.Logic.Equiv.Fin.Basic

/-! Exact three-colour counts on five-row HA strips with two defects. -/

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698Strip
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal (Col)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical canonical_pattern_card)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
  (bondDefects defects literalCount lumped_count forward forward_eq forward_shift)
open D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590
open HardinA229590StripData (between boundary cross)
open HardinA229698StripData

set_option maxRecDepth 100000
set_option Elab.async false

def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun A : Fin 5 × Fin n → Fin 3 =>
    @Canonical (Fin 5 × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun A : Fin 5 × Fin n → Fin 3 =>
    defects ∅ between (List.ofFn fun j i => A (i, j)) = 2 ∧
    (@Canonical (Fin 5 × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A)).card

set_option maxHeartbeats 0 in
theorem finite_certificate :
    (∀ p (d : Fin 3) (s : Fin 41 ⊕ (Fin 41 ⊕ Fin 41)),
      (∑ r : Fin 5 → Fin 3, if cross p r ≤ d.val ∧
        cl (boundary r) (d.val - cross p r) = s then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ s : Fin 41 ⊕ (Fin 41 ⊕ Fin 41),
      (∑ r : Fin 5 → Fin 3, if cl (boundary r) 2 = s then (1 : ℤ) else 0) = initial s) ∧
    (T ^ (6+21)).mulVec terminal =
      ∑ j : Fin 21, coefficients j • (T ^ (6+j.val)).mulVec terminal :=
  ⟨HardinA229698StripCut.transition_counts, HardinA229698StripCut.initial_counts,
    HardinA229698StripPowers.power_polynomial⟩

attribute [local irreducible] a T initial terminal cl

set_option maxHeartbeats 0 in
private theorem count_transfer (m : ℕ) :
    (literalCount (q := 3) ∅ between 2 (m+1) : ℤ) =
      dotProduct initial ((T ^ m).mulVec terminal) := by
  apply lumped_count ∅ between boundary cross (fun (_ : Col) d => d ≤ 2)
    cl T initial terminal 2
  · intro r t
    simp only [cross, HardinA229590StripCut.column_boundary]
  · intro p d hd
    by_cases h0 : d = 0
    · simp [terminal, cl, h0, HardinA229590StripData.terminal, HardinA229590StripData.cl]
    · by_cases h2 : d = 2
      · simp [terminal, cl, h2]
      · simp [terminal, cl, h2, HardinA229590StripData.terminal, HardinA229590StripData.cl, h0]
  · intro p d hd r hr
    change d - (cross p r + bondDefects ∅ r r) ≤ 2
    omega
  · intro p d hd s
    simpa only [bondDefects, Finset.filter_empty, Finset.card_empty, add_zero] using
      finite_certificate.1 p ⟨d, by omega⟩ s
  · intro r hr
    change 2 - bondDefects ∅ r r ≤ 2
    omega
  · intro s
    simpa only [bondDefects, Finset.filter_empty, Finset.card_empty,
      zero_le, true_and, Nat.sub_zero] using finite_certificate.2.1 s

set_option maxHeartbeats 0 in
private theorem scale_count (m : ℕ) : literalCount (q := 3) ∅ between 2 (m + 1) = 6 * a (m + 1) := by
  classical
  let S : (Fin 5 × Fin (m + 1) → Fin 3) → Prop := fun A =>
    defects ∅ between (List.ofFn fun j i => A (i, j)) = 2
  have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ A, S (e ∘ A) ↔ S A := by
    intro e A
    change defects ∅ between _ = 2 ↔ _
    rw [show (List.ofFn fun j i => (e ∘ A) (i, j)) =
      (List.ofFn fun j i => A (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
      D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer.relabel_defects]
  have nonconstant : ∀ A, S A → ∃ x y, A x ≠ A y := by
    intro A h
    by_contra he
    push Not at he
    have const : A = fun _ => A (0, 0) := funext fun x => he x (0, 0)
    change defects ∅ between _ = 2 at h
    rw [const] at h
    simp only [List.ofFn_const] at h
    rw [D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer.constant_defects] at h
    have cards : (∅ : Finset (Fin 5 × Fin 5)).card = 0 ∧ between.card = 9 := by decide +kernel
    rw [cards.1, cards.2] at h
    omega
  have orbit := @canonical_pattern_card (Fin 5 × Fin (m + 1)) inferInstance
    (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective) S invariant nonconstant
  let e := Equiv.arrowCongr (Equiv.prodComm (Fin (m + 1)) (Fin 5)) (Equiv.refl (Fin 3))
  have card := Fintype.card_congr (e.subtypeEquiv (p := fun A =>
    defects ∅ between (List.ofFn fun i j => A (i, j)) = 2) (q := S) (fun _ => Iff.rfl))
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at orbit card
  unfold literalCount a
  convert card.trans orbit using 1
  apply congrArg (fun x : ℕ => 6 * x)
  apply congrArg Finset.card
  ext A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]

set_option maxHeartbeats 0 in
theorem result (n : ℕ) :
    (a (n + 28) : ℤ) = 48 * (a (n + 27) : ℤ) - 960 * (a (n + 26) : ℤ) + 10468 * (a (n + 25) : ℤ) - 68685 * (a (n + 24) : ℤ) + 282276 * (a (n + 23) : ℤ) - 718624 * (a (n + 22) : ℤ) + 997536 * (a (n + 21) : ℤ) - 166467 * (a (n + 20) : ℤ) - 2005784 * (a (n + 19) : ℤ) + 3520224 * (a (n + 18) : ℤ) - 1956780 * (a (n + 17) : ℤ) - 1660207 * (a (n + 16) : ℤ) + 3547332 * (a (n + 15) : ℤ) - 2236608 * (a (n + 14) : ℤ) - 28632 * (a (n + 13) : ℤ) + 1014720 * (a (n + 12) : ℤ) - 774528 * (a (n + 11) : ℤ) + 307392 * (a (n + 10) : ℤ) - 71424 * (a (n + 9) : ℤ) + 9216 * (a (n + 8) : ℤ) - 512 * (a (n + 7) : ℤ) := by
  have bridge (m : ℕ) : dotProduct initial ((T ^ m).mulVec terminal) =
      6 * (a (m+1) : ℤ) := by
    rw [← count_transfer, scale_count]
    push_cast
    rfl
  have hf : forward T.transpose terminal (6+21) =
      ∑ j : Fin 21, coefficients j • forward T.transpose terminal (6+j.val) := by
    simpa only [forward_eq, ← Matrix.transpose_pow, Matrix.vecMul_transpose] using
      finite_certificate.2.2
  have h := forward_shift T.transpose terminal initial 21 6 coefficients hf n
  have pairing (m : ℕ) :
      dotProduct terminal ((T.transpose ^ m).mulVec initial) =
        dotProduct initial ((T ^ m).mulVec terminal) := by
    rw [← Matrix.transpose_pow, Matrix.mulVec_transpose, dotProduct_comm,
      ← Matrix.dotProduct_mulVec]
  simp_rw [pairing, bridge] at h
  norm_num only [coefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
    Fin.val_succ, Fin.val_one, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Nat.reduceAdd, Nat.add_assoc] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698Strip
