/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripCertificate
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692Strip.finite_certificate
   digest: Exact two-defect width-six HA transfer. -/

/-
admission_basis: open-problem-resolution (#31329; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229692Strip.result)
OwnerCol: proof_shape=bind-only; consumers=pushforward_class_counts, new_counts
classifier_image: proof_shape=bind-only; consumers=new_counts
extension_multiplicity: proof_shape=bind-only; consumers=new_counts
pushforward_class_counts: proof_shape=bind-only; consumers=new_counts
new_counts: proof_shape=bind-only; consumers=structural_certificate
structural_certificate: proof_shape=bind-only; consumers=HardinA229692Strip.finite_certificate
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripCut
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripCertificate
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229584StripData (Row Boundary horizontal antidiagonal boundary cross)
open HardinA229692StripData
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev OwnerCol :=
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.Col

private theorem classifier_image : ∀ p : Boundary,
    cl p 0 = (zeroClassImage
      (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.cls
        (p 0, p 1, p 2, p 3, p 4))).natAdd 32 := by
  decide +kernel

private theorem extension_multiplicity : ∀ p : Boundary,
    (∑ x : Fin 3, if bondDefects horizontal (Fin.cons x p) (Fin.cons x p) = 2
      then (1 : ℤ) else 0) = extensionMultiplicity
        (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.cls
          (p 0, p 1, p 2, p 3, p 4)) := by
  decide +kernel

private theorem pushforward_class_counts (f : Fin 41 → ℤ) :
    (∑ c : OwnerCol, f
      (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.cls c)) =
    ∑ k : Fin 41,
      D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.classWeights k * f k := by
  let cls := D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.cls
  calc
    _ = ∑ c : OwnerCol, ∑ k : Fin 41, (if cls c = k then (1 : ℤ) else 0) * f k := by
      apply Finset.sum_congr rfl
      intro c _
      simp [cls]
    _ = ∑ k : Fin 41, (∑ c : OwnerCol, if cls c = k then (1 : ℤ) else 0) * f k := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by
      dsimp only [cls]
      simp_rw [D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.initial_class_counts]

private theorem new_counts (j : Fin 36) :
    (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl (boundary r) (2 - bondDefects horizontal r r) = j.natAdd 32
      then (1 : ℤ) else 0) = initial (j.natAdd 32) := by
  have hcut (r : Row) :
      (bondDefects horizontal r r ≤ 2 ∧
        cl (boundary r) (2 - bondDefects horizontal r r) = j.natAdd 32) ↔
      bondDefects horizontal r r = 2 ∧ cl (boundary r) 0 = j.natAdd 32 := by
    by_cases h : bondDefects horizontal r r = 2
    · simp only [h, le_refl, Nat.sub_self, true_and]
    · constructor
      · rintro ⟨hr, hc⟩
        have hd : 0 < 2 - bondDefects horizontal r r := by omega
        have hv := congrArg Fin.val hc
        simp only [cl, ite_eq_left hd, Fin.val_castAdd, Fin.val_natAdd] at hv
        have := (HardinA229584StripData.cl (boundary r)
          (2 - bondDefects horizontal r r - 1)).isLt
        omega
      · rintro ⟨hr, _⟩
        exact (h hr).elim
  simp_rw [hcut]
  rw [← (Fin.consEquiv (fun _ : Fin 6 => Fin 3)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  change (∑ p : Boundary, ∑ x : Fin 3,
    if bondDefects horizontal (Fin.cons x p) (Fin.cons x p) = 2 ∧
      cl p 0 = j.natAdd 32 then (1 : ℤ) else 0) = _
  simp_rw [classifier_image]
  simp_rw [(Fin.natAdd_injective 36 32).eq_iff]
  simp_rw [and_comm, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp_rw [extension_multiplicity]
  have tuple_sum (f : OwnerCol → ℤ) :
      (∑ p : Boundary, f (p 0, p 1, p 2, p 3, p 4)) = ∑ c : OwnerCol, f c := by
    simpa [Fintype.sum_prod_type] using
      (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip.label_sum
        (fun p => f (p 0, p 1, p 2, p 3, p 4)))
  rw [tuple_sum (fun c => if zeroClassImage
    (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.cls c) = j then
      extensionMultiplicity
        (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.cls c) else 0)]
  change (∑ c : OwnerCol, if zeroClassImage
    (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.cls c) = j then
      extensionMultiplicity
        (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.cls c) else 0) = _
  rw [pushforward_class_counts
    (fun k => if zeroClassImage k = j then extensionMultiplicity k else 0)]
  simp only [initial, Fin.append_right, mul_ite, mul_zero]

/-- Acceptance, preservation of the exact budget, and the initial vector. -/
theorem structural_certificate :
    (∀ p (d : Fin 3), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ r : Row,
      cross p r + bondDefects horizontal r r ≤ d.val →
      Valid (boundary r) (d.val - (cross p r + bondDefects horizontal r r))) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 2 →
      Valid (boundary r) (2 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 68, (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl (boundary r) (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) := by
  refine ⟨by decide +kernel, ?_, ?_, ?_⟩
  · intro p d hp r hr
    have ht := HardinA229584StripCertificate.tail_bound r
    change d.val ≤ 2 ∧ _ ≤ 2 - d.val at hp
    constructor
    · omega
    · omega
  · intro r hr
    have ht := HardinA229584StripCertificate.tail_bound r
    constructor <;> omega
  · intro s
    by_cases hs : s.val < 32
    · let j : Fin 32 := ⟨s.val, hs⟩
      change (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
        cl (boundary r) (2 - bondDefects horizontal r r) = j.castAdd 36
        then (1 : ℤ) else 0) = initial (j.castAdd 36)
      have hcut (r : Row) :
          (bondDefects horizontal r r ≤ 2 ∧
            cl (boundary r) (2 - bondDefects horizontal r r) = j.castAdd 36) ↔
          bondDefects horizontal r r ≤ 1 ∧
            HardinA229584StripData.cl (boundary r) (1 - bondDefects horizontal r r) = j :=
        HardinA229692StripCut.active_cut r (bondDefects horizontal r r)
          (⟨2, by decide⟩ : Fin 3) j (show (0 : ℕ) < 2 from by decide)
      simp_rw [hcut]
      simpa only [initial, Fin.append_left] using
        HardinA229584StripCertificate.structural_certificate.2.2.2.1 j
    · let j : Fin 36 := ⟨s.val - 32, by omega⟩
      have he : s = j.natAdd 32 := Fin.ext (by dsimp [j]; omega)
      rw [he]
      exact new_counts j

end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripCertificate
