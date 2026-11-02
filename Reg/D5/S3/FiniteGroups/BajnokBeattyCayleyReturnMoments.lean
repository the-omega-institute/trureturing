import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyCayleyReturnMoments
import Reg.Support.DependentFamily

/-! Complete original-telescope DependentFamily proof evidence for
`D5.S3.FiniteGroups.BajnokBeattyCayleyReturnMoments.first_return_moment_defect`.
The typed outer Contract.Registration compiled, but actual scoped discovery failed
with contract.discovery:rigid_universes. The four-slot audit is UNFINISHED:
https://github.com/the-omega-institute/trureturing/issues/24448#issuecomment-6586650727
Only genuine kernel-checked family proof terms are retained here; no
`declared_validated` status is claimed. The full rooted-walk and trace conclusion
is preserved in the closed law, observing the actual group-order family. -/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyCayleyReturnMoments
open _root_.D5.S3.FiniteGroups.BajnokBeattyCayleyReturnMoments
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

private theorem audit_vertices_finite (p t : ℤ) (hp3 : 3 ≤ p) (ht : 2 ≤ t) :
    Finite (ZMod p.natAbs × ZMod (p * (((6*t-1)^2-9)/2)).natAbs) := by
  have hp : 0 < p := by omega
  have hf : ((6*t-1)^2-9)/2 = (3*t+1)*(6*t-4) := by
    have h : (6*t-1)^2-9 = 2*((3*t+1)*(6*t-4)) := by ring
    rw [h]
    omega
  have hD : 0 < ((6*t-1)^2-9)/2 := by
    rw [hf]
    exact mul_pos (by omega) (by omega)
  letI : NeZero p.natAbs := ⟨Int.natAbs_ne_zero.mpr hp.ne'⟩
  letI : NeZero (p * (((6*t-1)^2-9)/2)).natAbs :=
    ⟨Int.natAbs_ne_zero.mpr (mul_pos hp hD).ne'⟩
  infer_instance

abbrev momentSignature : Signature where
  Params := Unit
  State _ := ℤ × ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def groupOrder (pt : ℤ × ℤ) : ℤ :=
  (Nat.card (ZMod pt.1.natAbs × ZMod (pt.1 * (((6*pt.2-1)^2-9)/2)).natAbs) : ℤ)

noncomputable def actualMoment : Realization momentSignature :=
  realize momentSignature (fun _ _ pt => groupOrder pt) (fun e => nomatch e)

noncomputable def rejectedMoment : Realization momentSignature :=
  realize momentSignature (fun _ _ pt => groupOrder pt + 1) (fun e => nomatch e)

abbrev momentArena : Arena where
  signature := momentSignature
  Law R := ∀ (p t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t),
    let m : ℤ := 6 * t - 1
    let D : ℤ := (m ^ 2 - 9)/2
    let H := ZMod p.natAbs × ZMod (p * D).natAbs
    let N : ℤ := p ^ 2 * D
    let n : ℕ := (p * (m - 3)).toNat
    letI : Finite H := audit_vertices_finite p t hp3 ht
    letI : Fintype H := Fintype.ofFinite H
    let C19 : SimpleGraph H := graph (q19 p D t)
    let C33 : SimpleGraph H := graph (q33 p D t)
    let A19 : Matrix H H ℂ := C19.adjMatrix ℂ
    let A33 : Matrix H H ℂ := C33.adjMatrix ℂ
    R.readout () () (p,t) = N ∧
    (∀ k : ℕ, k < n → ∀ x : H,
      Nat.card {w : C19.Walk x x // w.length = k} =
        Nat.card {w : C33.Walk x x // w.length = k}) ∧
    (∀ x : H, Nat.card {w : C33.Walk x x // w.length = n} =
      Nat.card {w : C19.Walk x x // w.length = n} + 2) ∧
    (∀ k : ℕ, k < n → Matrix.trace (A19 ^ k) = Matrix.trace (A33 ^ k)) ∧
    Matrix.trace (A33 ^ n) - Matrix.trace (A19 ^ n) = 2 * (N : ℂ)

private theorem actual_law : momentArena.Law actualMoment := by
  exact first_return_moment_defect

private theorem rejected_law : ¬ momentArena.Law rejectedMoment := by
  intro h
  have bad := (h 3 2 (by norm_num) (by decide) (by norm_num)).1
  have good := (first_return_moment_defect 3 2 (by norm_num) (by decide) (by norm_num)).1
  change groupOrder (3,2) + 1 = 504 at bad
  change groupOrder (3,2) = 504 at good
  omega

noncomputable def momentSource : Registration momentArena
    (type_of% first_return_moment_defect) where
  actual := actualMoment
  bridge := Iff.rfl
  variation := ⟨actual_law, rejectedMoment, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedMoment, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (3,2), (5,2), ?_⟩
    have h3 := (first_return_moment_defect 3 2 (by norm_num) (by decide) (by norm_num)).1
    have h5 := (first_return_moment_defect 5 2 (by norm_num) (by decide) (by norm_num)).1
    change groupOrder (3,2) = 504 at h3
    change groupOrder (5,2) = 1400 at h5
    change groupOrder (3,2) ≠ groupOrder (5,2)
    omega

end Reg.D5.S3.FiniteGroups.BajnokBeattyCayleyReturnMoments
