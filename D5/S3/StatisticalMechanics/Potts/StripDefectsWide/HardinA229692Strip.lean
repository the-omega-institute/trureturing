/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692Strip.finite_certificate
   digest: Exact-budget transfer for Hardin's registered defective colourings. -/

/-
admission_basis: open-problem-resolution (#31329; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229692Strip.result)
class_relabel: proof_shape=bind-only; consumers=tail_counts
tail_counts: proof_shape=bind-only; consumers=finite_certificate
a: proof_shape=bind-only; consumers=result
finite_certificate: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #31329)
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup0
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup1
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup2
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup3
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup4
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692.HardinA229692StripClassGroup5
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripCut
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripForward
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584Strip
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Logic.Equiv.Fin.Basic

/-! Literal row-major canonical counts and row transfer. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692Strip
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229584StripData (Row Boundary horizontal antidiagonal boundary cross)
open HardinA229692StripData
open DefectTransfer (bondDefects defects literalCount lumped_count forward forward_shift)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical canonical_pattern_card)

/-- Literal row-major canonical arrays at the exact defect budget. -/
def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun A : Fin n × Fin 6 → Fin 3 =>
    @Canonical (Fin n × Fin 6)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun A : Fin n × Fin 6 → Fin 3 =>
    defects horizontal antidiagonal (List.ofFn fun i j => A (i, j)) = 2 ∧
    (@Canonical (Fin n × Fin 6)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A)).card

private theorem class_relabel (e : Equiv.Perm (Fin 3)) (p : Boundary) (d : ℕ) :
    cl (e ∘ p) d = cl p d := by
  have hc := D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.class_relabel
    e (p 0, p 1, p 2, p 3, p 4)
  change D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.cls
    (e (p 0), e (p 1), e (p 2), e (p 3), e (p 4)) = _ at hc
  simp only [cl, HardinA229584StripData.Valid, HardinA229584Strip.class_relabel,
    Function.comp_apply, e.injective.eq_iff, hc]
  rfl

private theorem tail_counts (s : Fin 36) (p : Boundary) (d : Fin 3) (hp : Valid p d.val) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s.natAdd 32
      then (1 : ℤ) else 0) = T (cl p d.val) (s.natAdd 32) := by
  by_cases ho : d.val ≤ 1 ∧ HardinA229584StripData.Valid p d.val
  · exact HardinA229692StripCut.old_counts p ⟨d.val, by omega⟩ ho.2 s
  ·
    obtain ⟨p', ⟨hnormal, e, he⟩, _⟩ :=
      D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.canonical_exists_unique p
    have hv : Valid p' d.val := by
      rw [he]
      simpa only [Valid, Function.comp_apply, e.injective.eq_iff] using hp
    have hnew : ¬ (d.val ≤ 1 ∧ HardinA229584StripData.Valid p' d.val) := by
      intro h
      apply ho
      rw [he] at h
      simpa only [HardinA229584StripData.Valid, Function.comp_apply,
        e.injective.eq_iff] using h
    have hT :
        (∑ r : Row, if cross p' r + bondDefects horizontal r r ≤ d.val ∧
          cl (boundary r) (d.val - (cross p' r + bondDefects horizontal r r)) = s.natAdd 32
          then (1 : ℤ) else 0) = T (cl p' d.val) (s.natAdd 32) := by
      fin_cases s
      · exact A229692.HardinA229692StripClassGroup0.transition_counts0 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup0.transition_counts1 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup0.transition_counts2 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup0.transition_counts3 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup0.transition_counts4 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup0.transition_counts5 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup1.transition_counts6 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup1.transition_counts7 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup1.transition_counts8 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup1.transition_counts9 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup1.transition_counts10 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup1.transition_counts11 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup2.transition_counts12 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup2.transition_counts13 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup2.transition_counts14 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup2.transition_counts15 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup2.transition_counts16 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup2.transition_counts17 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup3.transition_counts18 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup3.transition_counts19 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup3.transition_counts20 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup3.transition_counts21 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup3.transition_counts22 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup3.transition_counts23 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup4.transition_counts24 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup4.transition_counts25 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup4.transition_counts26 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup4.transition_counts27 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup4.transition_counts28 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup4.transition_counts29 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup5.transition_counts30 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup5.transition_counts31 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup5.transition_counts32 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup5.transition_counts33 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup5.transition_counts34 p' d hv hnormal hnew
      · exact A229692.HardinA229692StripClassGroup5.transition_counts35 p' d hv hnormal hnew
    rw [he] at hT
    let E : Row ≃ Row := Equiv.piCongrRight fun _ : Fin 6 => e
    rw [← E.sum_comp] at hT
    change (∑ r : Row, if cross (e ∘ p) (e ∘ r) +
      bondDefects horizontal (e ∘ r) (e ∘ r) ≤ d.val ∧
      cl (boundary (e ∘ r)) (d.val - (cross (e ∘ p) (e ∘ r) +
        bondDefects horizontal (e ∘ r) (e ∘ r))) = s.natAdd 32 then (1 : ℤ) else 0) =
      T (cl (e ∘ p) d.val) (s.natAdd 32) at hT
    simpa only [HardinA229584Strip.cross_relabel, HardinA229584Strip.horizontal_relabel,
      show ∀ r : Row, boundary (e ∘ r) = e ∘ boundary r from fun _ => rfl,
      class_relabel] using hT

theorem finite_certificate :
    (∀ p (d : Fin 3), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ r : Row,
      cross p r + bondDefects horizontal r r ≤ d.val →
      Valid (boundary r) (d.val - (cross p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ s : Fin 68,
      (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
        cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 2 →
      Valid (boundary r) (2 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 68, (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl (boundary r) (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 11, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 11 = ∑ j : Fin 9, (![531441, -1771470, 2460375, -1842183, 803115, -205200, 29368, -2145, 75] j : ℤ) • W ⟨2 + j.val, by omega⟩ := by
  refine ⟨HardinA229692StripCertificate.structural_certificate.1,
    HardinA229692StripCertificate.structural_certificate.2.1, ?_,
    HardinA229692StripCertificate.structural_certificate.2.2.1,
    HardinA229692StripCertificate.structural_certificate.2.2.2,
    HardinA229692StripForward.forward_certificate.1,
    HardinA229692StripForward.forward_certificate.2⟩
  intro p d hp s
  by_cases hs : s.val < 32
  · let j : Fin 32 := ⟨s.val, hs⟩
    have he : s = j.castAdd 36 := rfl
    rw [he]
    exact HardinA229692StripCut.leading_counts p d hp j
  · let j : Fin 36 := ⟨s.val - 32, by omega⟩
    have he : s = j.natAdd 32 := Fin.ext (by dsimp [j]; omega)
    rw [he]
    exact tail_counts j p d hp

attribute [local irreducible] a T initial terminal W cl

/-- The registered recurrence at every index at least 12. -/
theorem result (n : ℕ) :
    (a (n + 12) : ℤ) = 75 * a (n + 11) - 2145 * a (n + 10) + 29368 * a (n + 9) - 205200 * a (n + 8) + 803115 * a (n + 7) - 1842183 * a (n + 6) + 2460375 * a (n + 5) - 1771470 * a (n + 4) + 531441 * a (n + 3) := by
  have labelled (m : ℕ) :
      (literalCount (q := 3) horizontal antidiagonal 2 (m + 1) : ℤ) =
        dotProduct initial ((T ^ m).mulVec terminal) := by
    apply lumped_count horizontal antidiagonal boundary cross Valid cl T initial terminal 2
      HardinA229584Strip.edge
    · intro p d h
      exact finite_certificate.1 p ⟨d, by have hd : d ≤ 2 := h.1; omega⟩ h
    · intro p d h r hr
      exact finite_certificate.2.1 p ⟨d, by have hd : d ≤ 2 := h.1; omega⟩ h r hr
    · intro p d h s
      exact finite_certificate.2.2.1 p ⟨d, by have hd : d ≤ 2 := h.1; omega⟩ h s
    · exact finite_certificate.2.2.2.1
    · exact finite_certificate.2.2.2.2.1
  have tab (i : Fin 12) : forward T initial i.val = W i := by
    induction i using Fin.induction with
    | zero => exact finite_certificate.2.2.2.2.2.1.1.symm
    | succ i ih =>
      rw [forward, Fin.val_succ, Function.iterate_succ_apply']
      change Matrix.vecMul (forward T initial i.val) T = W i.succ
      change forward T initial i.val = W i.castSucc at ih
      rw [ih]
      exact (finite_certificate.2.2.2.2.2.1.2 i).symm
  have poly : forward T initial (2 + 9) =
      ∑ j : Fin 9, (![531441, -1771470, 2460375, -1842183, 803115, -205200, 29368, -2145, 75] j : ℤ) • forward T initial (2 + j.val) := by
    rw [tab ⟨11, by omega⟩]
    simp_rw [show ∀ j : Fin 9, forward T initial (2 + j.val) = W ⟨2 + j.val, by omega⟩
      from fun j => tab ⟨2 + j.val, by omega⟩]
    exact finite_certificate.2.2.2.2.2.2
  have scale (m : ℕ) : literalCount (q := 3) horizontal antidiagonal 2 (m + 1) = 6 * a (m + 1) := by
    classical
    let S : (Fin (m + 1) × Fin 6 → Fin 3) → Prop := fun A =>
      defects horizontal antidiagonal (List.ofFn fun i j => A (i, j)) = 2
    have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ A, S (e ∘ A) ↔ S A := by
      intro e A
      change defects horizontal antidiagonal _ = 2 ↔ _
      rw [show (List.ofFn fun i j => (e ∘ A) (i, j)) =
        (List.ofFn fun i j => A (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
        DefectTransfer.relabel_defects]
    have nonconstant : ∀ A, S A → ∃ x y, A x ≠ A y := by
      intro A h
      by_contra he
      push_neg at he
      have const : A = fun _ => A (0, 0) := funext fun x => he x (0, 0)
      change defects horizontal antidiagonal _ = 2 at h
      rw [const] at h
      simp only [List.ofFn_const] at h
      rw [DefectTransfer.constant_defects] at h
      have cards : horizontal.card = 5 ∧ antidiagonal.card = 5 := by decide +kernel
      rw [cards.1, cards.2] at h
      omega
    have orbit := @canonical_pattern_card (Fin (m + 1) × Fin 6) inferInstance
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective) S invariant nonconstant
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at orbit
    unfold literalCount a
    convert orbit using 1
    apply congrArg (fun x : ℕ => 6 * x)
    apply congrArg Finset.card
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
  have bridge (m : ℕ) :
      dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
    rw [← labelled, scale]
    push_cast
    rfl
  have h := forward_shift T initial terminal 9 2 ![531441, -1771470, 2460375, -1842183, 803115, -205200, 29368, -2145, 75] poly n
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
  have h2 := bridge (n + 2)
  have h3 := bridge (n + 3)
  have h4 := bridge (n + 4)
  have h5 := bridge (n + 5)
  have h6 := bridge (n + 6)
  have h7 := bridge (n + 7)
  have h8 := bridge (n + 8)
  have h9 := bridge (n + 9)
  have h10 := bridge (n + 10)
  have h11 := bridge (n + 11)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  rw [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11] at h
  norm_num only [Nat.reduceAdd, zero_add] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692Strip
