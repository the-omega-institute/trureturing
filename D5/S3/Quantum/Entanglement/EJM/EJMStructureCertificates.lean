/- GID: D5/S3/Quantum/Entanglement/EJM/EJMStructureCertificates
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMStructureCertificates
   mirror-E: none(waiver:actual-exact-certificate-premise)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.associated_lower_le_score; premises=D5/S3/Quantum/Entanglement/EJM/EJMStructureCertificates.triangle_structure,D5/S3/Quantum/Entanglement/EJM/EJMStructureCertificates.singleton_structure
   digest: Every actual local row passes the exact structural check. -/

/-
admission_basis: escape-witness
This delivery supplies the complete actual numerical premises for local
row and cache soundness. The consumed receipts are not independent
positive finite-instance results. Numerical
normalization and consumed binding helpers supply no separate escape.
Public targets: triangle_structure, singleton_structure.
Each private chunk and public receipt has proof_shape: bind-only. The public
interval dispatch consumes every chunk covering all 41294 triangle rows and
8689 singleton rows. These receipts discharge checkStructure on the actual
partial actions and row interpreters; the generic checked_structure_and_terminals
consumer derives checkRow acceptance only when actual terminal inequalities
are also proved. No centered-score arithmetic is supplied by structure alone.
Both receipts are consumed by EJMLocalBoundAcceptance and, through its
accepted row bounds, by EJMCacheSoundness.associated_lower_le_score.
The concrete numeric premises listed in the utility header must be
kernel-checked in this delivery, with the same original functions,
finite domains, partial rows and inequality direction. Pending sources
or external producer validations do not fulfill those premises.
Four-slot registration remains unfinished under issue #16309. The
specific public targets below lack a compiled original-source
realization bridge, enrolled readout and variation/sensitivity evidence;
this is a missing-registration statement, not a template-support claim.
-/

import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock0
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock1
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock2
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock3
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock4
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock5
import D5.S3.Quantum.Entanglement.EJM.EJMStructureSingletonBlock0
import D5.S3.Quantum.Entanglement.EJM.EJMStructureSingletonBlock1
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Quantum.Entanglement.EJM.EJMStructureCertificates
open D5.S0.Certificates.FinitePartialBoundDAG
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport

/-- All original 41294 rows are covered by exact disjoint kernel intervals. -/
theorem triangle_structure (i : Fin 41294) :
    checkStructure trianglePartialAct triangleRows i = true := by
  by_cases h0 : i.val < 8192
  ·
    let j : Fin 8192 := ⟨i.val - 0, by have h := i.isLt; omega⟩
    have he : (⟨0 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock0.accepted j
  by_cases h1 : i.val < 16384
  ·
    let j : Fin 8192 := ⟨i.val - 8192, by have h := i.isLt; omega⟩
    have he : (⟨8192 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock1.accepted j
  by_cases h2 : i.val < 24576
  ·
    let j : Fin 8192 := ⟨i.val - 16384, by have h := i.isLt; omega⟩
    have he : (⟨16384 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock2.accepted j
  by_cases h3 : i.val < 32768
  ·
    let j : Fin 8192 := ⟨i.val - 24576, by have h := i.isLt; omega⟩
    have he : (⟨24576 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock3.accepted j
  by_cases h4 : i.val < 40960
  ·
    let j : Fin 8192 := ⟨i.val - 32768, by have h := i.isLt; omega⟩
    have he : (⟨32768 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock4.accepted j
  let j : Fin 334 := ⟨i.val - 40960, by have h := i.isLt; omega⟩
  have he : (⟨40960 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
    apply Fin.ext
    dsimp [j] <;> omega
  simpa only [he] using EJMStructureTriangleBlock5.accepted j

#print axioms triangle_structure

/-- All original 8689 rows are covered by exact disjoint kernel intervals. -/
theorem singleton_structure (i : Fin 8689) :
    checkStructure singletonPartialAct singletonRows i = true := by
  by_cases h0 : i.val < 8192
  ·
    let j : Fin 8192 := ⟨i.val - 0, by have h := i.isLt; omega⟩
    have he : (⟨0 + j.val, by have h := j.isLt; omega⟩ : Fin 8689) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureSingletonBlock0.accepted j
  let j : Fin 497 := ⟨i.val - 8192, by have h := i.isLt; omega⟩
  have he : (⟨8192 + j.val, by have h := j.isLt; omega⟩ : Fin 8689) = i := by
    apply Fin.ext
    dsimp [j] <;> omega
  simpa only [he] using EJMStructureSingletonBlock1.accepted j

#print axioms singleton_structure
end D5.S3.Quantum.Entanglement.EJM.EJMStructureCertificates
