/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.finite_certificate
   digest: The integer recurrence for canonical one-defect width-7 arrays. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229585Strip.result)
cellOrder: proof_shape=bind-only; consumers=Normal, scale_count
Normal: proof_shape=bind-only; consumers=a, scale_count
decidableNormal: proof_shape=bind-only; consumers=a
a: proof_shape=bind-only; consumers=result
edge: proof_shape=bind-only; consumers=count_transfer
class_relabel: proof_shape=bind-only; consumers=transition_counts
horizontal_relabel: proof_shape=bind-only; consumers=transition_counts
cross_relabel: proof_shape=bind-only; consumers=transition_counts
transition_counts: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=bind-only; consumers=count_transfer, powers_table, polynomial_relation
count_transfer: proof_shape=bind-only; consumers=result
powers_table: proof_shape=bind-only; consumers=polynomial_relation, result
polynomial_relation: proof_shape=bind-only; consumers=result
scale_count: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=external sequence A229585
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass0
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass1
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass2
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass3
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass4
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass5
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass6
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass7
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass8
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass9
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass10
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass11
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass12
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass13
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass14
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass15
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass16
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass17
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass18
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass19
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass20
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass21
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass22
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block0.HardinA229585StripClass23
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass24
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass25
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass26
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass27
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass28
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass29
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass30
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass31
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass32
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass33
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass34
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass35
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass36
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass37
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass38
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass39
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass40
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass41
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass42
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass43
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass44
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass45
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass46
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass47
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass48
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass49
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass50
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass51
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass52
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass53
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass54
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass55
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass56
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass57
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass58
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass59
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass60
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass61
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass62
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass63
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass64
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass65
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass66
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass67
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass68
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass69
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass70
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block2.HardinA229585StripClass71
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass0
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass1
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass2
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass3
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass4
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass5
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass6
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass7
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass8
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass9
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass10
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass11
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass12
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass13
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass14
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass15
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass16
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass17
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass18
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass19
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass20
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass21
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass22
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block0.HardinA229585StripClass23
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass24
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass25
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass26
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass27
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass28
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass29
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass30
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass31
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass32
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass33
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass34
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass35
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass36
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass37
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass38
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass39
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass40
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass41
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass42
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass43
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass44
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass45
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass46
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass47
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass48
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass49
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass50
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass51
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass52
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass53
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass54
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass55
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass56
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass57
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass58
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass59
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass60
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass61
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass62
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass63
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass64
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass65
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass66
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass67
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass68
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass69
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass70
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block2.HardinA229585StripClass71
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Logic.Equiv.Fin.Basic

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects defects literalCount continuation lumped_count forward forward_shift)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical canonical_pattern_card)
open HardinA229585StripData

private abbrev cellOrder (n : ℕ) : LinearOrder (Fin n × Fin 7) :=
  LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective
private def Normal {n : ℕ} (A : Fin n × Fin 7 → Fin 3) : Prop :=
  @Canonical (Fin n × Fin 7) (cellOrder n).toLT 3 A
private instance decidableNormal {n : ℕ} (A : Fin n × Fin 7 → Fin 3) : Decidable (Normal A) := by
  unfold Normal Canonical
  change Decidable (∀ (i : Fin n × Fin 7) (b : Fin 3), b < A i →
    ∃ j : Fin n × Fin 7, finProdFinEquiv j < finProdFinEquiv i ∧ A j = b)
  infer_instance

/-- The finite filter ranges over every three-colour array of the indicated shape. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin n × Fin 7 → Fin 3 =>
    defects horizontal antidiagonal (List.ofFn fun i j => A (i, j)) = 1 ∧ Normal A).card

private theorem edge (r t : Row) : bondDefects antidiagonal r t = cross (boundary r) t := by
  unfold cross bondDefects
  apply congrArg Finset.card
  ext e
  by_cases he : e ∈ antidiagonal
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    rfl
  · simp [he]

private theorem class_relabel (e : Equiv.Perm (Fin 3)) (p : Boundary) (d : ℕ) :
    cl (e ∘ p) d = cl p d := by
  simp only [cl, Function.comp_apply, e.injective.eq_iff]

private theorem horizontal_relabel (e : Equiv.Perm (Fin 3)) (r : Row) :
    bondDefects horizontal (e ∘ r) (e ∘ r) = bondDefects horizontal r r := by
  simp only [bondDefects, Function.comp_apply, e.injective.eq_iff]

private theorem cross_relabel (e : Equiv.Perm (Fin 3)) (p : Boundary) (r : Row) :
    cross (e ∘ p) (e ∘ r) = cross p r := by
  unfold cross bondDefects
  apply congrArg Finset.card
  ext a
  by_cases ha : a ∈ antidiagonal
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    simp only [Finset.mem_filter, Fin.cons_succ, Function.comp_apply, e.injective.eq_iff]
  · simp [ha]

private theorem transition_counts (p : Boundary) (d : Fin 2) (hp : Valid p d.val)
    (s : Fin 72) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p d.val) s := by
  obtain ⟨p', ⟨hnormal, e, he⟩, _⟩ :=
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.canonical_exists_unique p
  have hv : Valid p' d.val := by
    rw [he]
    simpa only [Valid, Function.comp_apply, e.injective.eq_iff] using hp
  have hT :
      (∑ r : Row, if cross p' r + bondDefects horizontal r r ≤ d.val ∧
        cl (boundary r) (d.val - (cross p' r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p' d.val) s := by
    fin_cases d
    · fin_cases s
      · exact Budget0.Block0.HardinA229585StripClass0.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass1.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass2.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass3.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass4.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass5.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass6.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass7.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass8.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass9.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass10.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass11.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass12.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass13.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass14.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass15.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass16.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass17.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass18.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass19.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass20.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass21.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass22.transition_counts p' hv hnormal
      · exact Budget0.Block0.HardinA229585StripClass23.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass24.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass25.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass26.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass27.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass28.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass29.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass30.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass31.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass32.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass33.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass34.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass35.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass36.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass37.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass38.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass39.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass40.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass41.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass42.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass43.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass44.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass45.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass46.transition_counts p' hv hnormal
      · exact Budget0.Block1.HardinA229585StripClass47.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass48.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass49.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass50.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass51.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass52.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass53.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass54.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass55.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass56.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass57.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass58.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass59.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass60.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass61.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass62.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass63.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass64.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass65.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass66.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass67.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass68.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass69.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass70.transition_counts p' hv hnormal
      · exact Budget0.Block2.HardinA229585StripClass71.transition_counts p' hv hnormal
    · fin_cases s
      · exact Budget1.Block0.HardinA229585StripClass0.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass1.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass2.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass3.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass4.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass5.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass6.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass7.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass8.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass9.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass10.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass11.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass12.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass13.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass14.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass15.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass16.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass17.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass18.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass19.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass20.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass21.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass22.transition_counts p' hv hnormal
      · exact Budget1.Block0.HardinA229585StripClass23.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass24.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass25.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass26.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass27.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass28.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass29.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass30.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass31.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass32.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass33.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass34.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass35.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass36.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass37.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass38.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass39.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass40.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass41.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass42.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass43.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass44.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass45.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass46.transition_counts p' hv hnormal
      · exact Budget1.Block1.HardinA229585StripClass47.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass48.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass49.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass50.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass51.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass52.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass53.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass54.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass55.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass56.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass57.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass58.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass59.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass60.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass61.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass62.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass63.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass64.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass65.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass66.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass67.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass68.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass69.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass70.transition_counts p' hv hnormal
      · exact Budget1.Block2.HardinA229585StripClass71.transition_counts p' hv hnormal
  rw [he] at hT
  let E : Row ≃ Row := Equiv.piCongrRight fun _ : Fin 7 => e
  rw [← E.sum_comp] at hT
  change (∑ r : Row, if cross (e ∘ p) (e ∘ r) +
    bondDefects horizontal (e ∘ r) (e ∘ r) ≤ d.val ∧
    cl (boundary (e ∘ r)) (d.val - (cross (e ∘ p) (e ∘ r) +
      bondDefects horizontal (e ∘ r) (e ∘ r))) = s then (1 : ℤ) else 0) =
    T (cl (e ∘ p) d.val) s at hT
  simpa only [cross_relabel, horizontal_relabel,
    show ∀ r : Row, boundary (e ∘ r) = e ∘ boundary r from fun _ => rfl,
    class_relabel] using hT

/-- Counts, budget preservation and the integer polynomial certificate. -/
theorem finite_certificate :
    (∀ p (d : Fin 2), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ r : Row,
      cross p r + bondDefects horizontal r r ≤ d.val →
      Valid (boundary r) (d.val - (cross p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 72,
      (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
        cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 1 →
      Valid (boundary r) (1 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 72, (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl (boundary r) (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 10, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 10 = ∑ j : Fin 8, (![-656100, 1574640, -1513404, 750384, -206469, 31428, -2466, 84] j : ℤ) • W ⟨2 + j.val, by omega⟩ := by
  obtain ⟨hz, hn, hi, hv, hw, hp⟩ := HardinA229585StripCertificate.structural_certificate
  exact ⟨hz, hn, transition_counts, hi, hv, hw, hp⟩

private theorem count_transfer (n : ℕ) :
    (literalCount (q := 3) horizontal antidiagonal 1 (n + 1) : ℤ) =
      dotProduct initial ((T ^ n).mulVec terminal) := by
  apply lumped_count horizontal antidiagonal boundary cross Valid cl T initial terminal 1 edge
  · intro p d h
    exact finite_certificate.1 p ⟨d, by have := h.1; omega⟩ h
  · intro p d h r hr
    exact finite_certificate.2.1 p ⟨d, by have := h.1; omega⟩ h r hr
  · intro p d h s
    exact finite_certificate.2.2.1 p ⟨d, by have := h.1; omega⟩ h s
  · exact finite_certificate.2.2.2.1
  · exact finite_certificate.2.2.2.2.1

private theorem powers_table (i : Fin 11) : forward T initial i.val = W i := by
  induction i using Fin.induction with
  | zero => exact finite_certificate.2.2.2.2.2.1.1.symm
  | succ i ih =>
    rw [forward, Fin.val_succ, Function.iterate_succ_apply']
    change Matrix.vecMul (forward T initial i.val) T = W i.succ
    change forward T initial i.val = W i.castSucc at ih
    rw [ih]
    exact (finite_certificate.2.2.2.2.2.1.2 i).symm

private theorem polynomial_relation :
    forward T initial (2 + 8) =
      ∑ j : Fin 8, (![-656100, 1574640, -1513404, 750384, -206469, 31428, -2466, 84] j : ℤ) • forward T initial (2 + j.val) := by
  rw [powers_table ⟨10, by omega⟩]
  simp_rw [show ∀ j : Fin 8, forward T initial (2 + j.val) = W ⟨2 + j.val, by omega⟩
    from fun j => powers_table ⟨2 + j.val, by omega⟩]
  exact finite_certificate.2.2.2.2.2.2

private theorem scale_count (n : ℕ) (hn : 1 ≤ n) :
    literalCount (q := 3) horizontal antidiagonal 1 n = 6 * a n := by
  classical
  let S : (Fin n × Fin 7 → Fin 3) → Prop := fun A =>
    defects horizontal antidiagonal (List.ofFn fun i j => A (i, j)) = 1
  have hinv : ∀ e : Equiv.Perm (Fin 3), ∀ A, S (e ∘ A) ↔ S A := by
    intro e A
    have hm : (List.ofFn fun i j => (e ∘ A) (i, j)) =
        (List.ofFn fun i j => A (i, j)).map (fun r => e ∘ r) := by
      rw [List.map_ofFn]
      rfl
    change defects horizontal antidiagonal _ = 1 ↔ _
    rw [hm, DefectTransfer.relabel_defects]
  have huse : ∀ A, S A → ∃ i j, A i ≠ A j := by
    intro A ha
    by_contra hh
    push_neg at hh
    let z : Fin n × Fin 7 := (⟨0, by omega⟩, 0)
    have he : A = fun _ => A z := funext fun i => hh i z
    change defects horizontal antidiagonal _ = 1 at ha
    rw [he] at ha
    simp only [List.ofFn_const] at ha
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [DefectTransfer.constant_defects] at ha
    have hc : horizontal.card = 6 ∧ antidiagonal.card = 6 := by decide +kernel
    rw [hc.1, hc.2] at ha
    omega
  have h := @canonical_pattern_card (Fin n × Fin 7) inferInstance (cellOrder n) S hinv huse
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, S] at h
  unfold literalCount a Normal
  convert h using 1
  apply congrArg (fun x : ℕ => 6 * x)
  apply congrArg Finset.card
  ext A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

attribute [local irreducible] a

/-- Hardin's width-seven recurrence, valid from row count nine. -/
theorem result (n : ℕ) :
    (a (n + 9) : ℤ) = 84 * a (n + 8) - 2466 * a (n + 7) +
      31428 * a (n + 6) - 206469 * a (n + 5) + 750384 * a (n + 4) -
      1513404 * a (n + 3) + 1574640 * a (n + 2) - 656100 * a (n + 1) := by
  have bridge (m : ℕ) :
      dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
    rw [← count_transfer, scale_count (m + 1) (by omega)]
    push_cast
    rfl
  have table (i : Fin 11) :
      dotProduct (W i) terminal = 6 * (a (i.val + 1) : ℤ) := by
    rw [← powers_table i, DefectTransfer.forward_eq, ← Matrix.dotProduct_mulVec, bridge]
  have first (i : Fin 2) :
      dotProduct (W ⟨8 + i.val, by omega⟩) terminal =
        ∑ j : Fin 8, (![-656100, 1574640, -1513404, 750384, -206469, 31428, -2466, 84] j : ℤ) *
          dotProduct (W ⟨0 + i.val + j.val, by omega⟩) terminal := by
    revert i
    decide +kernel
  rcases n with _ | _ | n
  · have h := first 0
    simp_rw [table] at h
    norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.add_assoc, Nat.add_zero] at h
    linarith
  · have h := first 1
    simp_rw [table] at h
    norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.add_assoc, Nat.add_zero] at h
    linarith
  · have h := forward_shift T initial terminal 8 2 ![-656100, 1574640, -1513404, 750384, -206469, 31428, -2466, 84] polynomial_relation n
    simp_rw [bridge] at h
    norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.add_assoc, Nat.add_zero] at h
    linarith

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
