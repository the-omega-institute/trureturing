/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Literal
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Literal
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.finite_certificate
   digest: Literal width-six two-defect HDA count and its labelled count. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn

open D5.S3.StatisticalMechanics.Potts.StripDefects
open D5.S3.Combinatorics.TraceAvoidingArrays

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Literal

open HardinA229637RowColumn (T horiz betw)
open HardinA229584StripData (horizontal)
open WidthSix.HardinA229532StripData (between)
open DefectTransfer (defects literalCount)
open HardinA233177Canonical (Canonical canonical_pattern_card)

set_option Elab.async false

private theorem same_horizontal : horiz 6 = horizontal := by decide +kernel
private theorem same_between : betw 6 = between := by decide +kernel

private def ExactTwo {n : ℕ} (A : Fin n × Fin 6 → Fin 3) : Prop :=
  defects horizontal between (List.ofFn fun i j => A (i, j)) = 2

theorem six_labellings (m : ℕ) :
    literalCount (q := 3) horizontal between 2 (m + 1) = 6 * T (m + 1) 6 := by
  classical
  let order : LinearOrder (Fin (m + 1) × Fin 6) :=
    LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective
  have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ A : Fin (m + 1) × Fin 6 → Fin 3,
      ExactTwo (e ∘ A) ↔ ExactTwo A := by
    intro e A
    unfold ExactTwo
    rw [show (List.ofFn fun i j => (e ∘ A) (i, j)) =
      (List.ofFn fun i j => A (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
      DefectTransfer.relabel_defects]
  have nonconstant : ∀ A : Fin (m + 1) × Fin 6 → Fin 3, ExactTwo A →
      ∃ x y, A x ≠ A y := by
    intro A h
    by_contra he
    push Not at he
    have const : A = fun _ => A (0, 0) := funext fun x => he x (0, 0)
    unfold ExactTwo at h
    rw [const, List.ofFn_const, DefectTransfer.constant_defects] at h
    have hh : horizontal.card = 5 := by decide +kernel
    rw [hh] at h
    omega
  have orbit := @canonical_pattern_card (Fin (m + 1) × Fin 6) inferInstance order
    ExactTwo invariant nonconstant
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at orbit
  unfold literalCount T
  rw [same_horizontal, same_between]
  convert orbit using 1
  all_goals
    try apply congrArg (fun x : ℕ => 6 * x)
    apply congrArg Finset.card
    ext A
    simp [ExactTwo]

#print axioms six_labellings

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Literal
