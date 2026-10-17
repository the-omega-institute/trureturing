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
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock6
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock7
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock8
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock9
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock10
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock11
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock12
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock13
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock14
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock15
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock16
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock17
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock18
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock19
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock20
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock21
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock22
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock23
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock24
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock25
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock26
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock27
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock28
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock29
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock30
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock31
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock32
import D5.S3.Quantum.Entanglement.EJM.EJMStructureTriangleBlock33
import D5.S3.Quantum.Entanglement.EJM.EJMStructureSingletonBlock0
import D5.S3.Quantum.Entanglement.EJM.EJMStructureSingletonBlock1
import D5.S3.Quantum.Entanglement.EJM.EJMStructureSingletonBlock2
import D5.S3.Quantum.Entanglement.EJM.EJMStructureSingletonBlock3
import D5.S3.Quantum.Entanglement.EJM.EJMStructureSingletonBlock4
import D5.S3.Quantum.Entanglement.EJM.EJMStructureSingletonBlock5
import D5.S3.Quantum.Entanglement.EJM.EJMStructureSingletonBlock6
import D5.S3.Quantum.Entanglement.EJM.EJMStructureSingletonBlock7
import D5.S3.Quantum.Entanglement.EJM.EJMStructureSingletonBlock8
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Quantum.Entanglement.EJM.EJMStructureCertificates
open D5.S0.Certificates.FinitePartialBoundDAG
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport

/-- All original 41294 rows are covered by exact disjoint kernel intervals. -/
theorem triangle_structure (i : Fin 41294) :
    checkStructure trianglePartialAct triangleRows i = true := by
  by_cases h0 : i.val < 4096
  ·
    let j : Fin 4096 := ⟨i.val - 0, by have h := i.isLt; omega⟩
    have he : (⟨0 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock0.accepted j
  by_cases h1 : i.val < 6144
  ·
    let j : Fin 2048 := ⟨i.val - 4096, by have h := i.isLt; omega⟩
    have he : (⟨4096 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock1.accepted j
  by_cases h2 : i.val < 8192
  ·
    let j : Fin 2048 := ⟨i.val - 6144, by have h := i.isLt; omega⟩
    have he : (⟨6144 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock2.accepted j
  by_cases h3 : i.val < 10240
  ·
    let j : Fin 2048 := ⟨i.val - 8192, by have h := i.isLt; omega⟩
    have he : (⟨8192 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock3.accepted j
  by_cases h4 : i.val < 12288
  ·
    let j : Fin 2048 := ⟨i.val - 10240, by have h := i.isLt; omega⟩
    have he : (⟨10240 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock4.accepted j
  by_cases h5 : i.val < 13312
  ·
    let j : Fin 1024 := ⟨i.val - 12288, by have h := i.isLt; omega⟩
    have he : (⟨12288 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock5.accepted j
  by_cases h6 : i.val < 14336
  ·
    let j : Fin 1024 := ⟨i.val - 13312, by have h := i.isLt; omega⟩
    have he : (⟨13312 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock6.accepted j
  by_cases h7 : i.val < 15360
  ·
    let j : Fin 1024 := ⟨i.val - 14336, by have h := i.isLt; omega⟩
    have he : (⟨14336 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock7.accepted j
  by_cases h8 : i.val < 16384
  ·
    let j : Fin 1024 := ⟨i.val - 15360, by have h := i.isLt; omega⟩
    have he : (⟨15360 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock8.accepted j
  by_cases h9 : i.val < 17408
  ·
    let j : Fin 1024 := ⟨i.val - 16384, by have h := i.isLt; omega⟩
    have he : (⟨16384 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock9.accepted j
  by_cases h10 : i.val < 18432
  ·
    let j : Fin 1024 := ⟨i.val - 17408, by have h := i.isLt; omega⟩
    have he : (⟨17408 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock10.accepted j
  by_cases h11 : i.val < 19456
  ·
    let j : Fin 1024 := ⟨i.val - 18432, by have h := i.isLt; omega⟩
    have he : (⟨18432 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock11.accepted j
  by_cases h12 : i.val < 20480
  ·
    let j : Fin 1024 := ⟨i.val - 19456, by have h := i.isLt; omega⟩
    have he : (⟨19456 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock12.accepted j
  by_cases h13 : i.val < 21504
  ·
    let j : Fin 1024 := ⟨i.val - 20480, by have h := i.isLt; omega⟩
    have he : (⟨20480 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock13.accepted j
  by_cases h14 : i.val < 22528
  ·
    let j : Fin 1024 := ⟨i.val - 21504, by have h := i.isLt; omega⟩
    have he : (⟨21504 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock14.accepted j
  by_cases h15 : i.val < 23552
  ·
    let j : Fin 1024 := ⟨i.val - 22528, by have h := i.isLt; omega⟩
    have he : (⟨22528 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock15.accepted j
  by_cases h16 : i.val < 24576
  ·
    let j : Fin 1024 := ⟨i.val - 23552, by have h := i.isLt; omega⟩
    have he : (⟨23552 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock16.accepted j
  by_cases h17 : i.val < 25600
  ·
    let j : Fin 1024 := ⟨i.val - 24576, by have h := i.isLt; omega⟩
    have he : (⟨24576 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock17.accepted j
  by_cases h18 : i.val < 26624
  ·
    let j : Fin 1024 := ⟨i.val - 25600, by have h := i.isLt; omega⟩
    have he : (⟨25600 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock18.accepted j
  by_cases h19 : i.val < 27648
  ·
    let j : Fin 1024 := ⟨i.val - 26624, by have h := i.isLt; omega⟩
    have he : (⟨26624 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock19.accepted j
  by_cases h20 : i.val < 28672
  ·
    let j : Fin 1024 := ⟨i.val - 27648, by have h := i.isLt; omega⟩
    have he : (⟨27648 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock20.accepted j
  by_cases h21 : i.val < 29696
  ·
    let j : Fin 1024 := ⟨i.val - 28672, by have h := i.isLt; omega⟩
    have he : (⟨28672 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock21.accepted j
  by_cases h22 : i.val < 30720
  ·
    let j : Fin 1024 := ⟨i.val - 29696, by have h := i.isLt; omega⟩
    have he : (⟨29696 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock22.accepted j
  by_cases h23 : i.val < 31744
  ·
    let j : Fin 1024 := ⟨i.val - 30720, by have h := i.isLt; omega⟩
    have he : (⟨30720 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock23.accepted j
  by_cases h24 : i.val < 32768
  ·
    let j : Fin 1024 := ⟨i.val - 31744, by have h := i.isLt; omega⟩
    have he : (⟨31744 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock24.accepted j
  by_cases h25 : i.val < 33792
  ·
    let j : Fin 1024 := ⟨i.val - 32768, by have h := i.isLt; omega⟩
    have he : (⟨32768 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock25.accepted j
  by_cases h26 : i.val < 34816
  ·
    let j : Fin 1024 := ⟨i.val - 33792, by have h := i.isLt; omega⟩
    have he : (⟨33792 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock26.accepted j
  by_cases h27 : i.val < 35840
  ·
    let j : Fin 1024 := ⟨i.val - 34816, by have h := i.isLt; omega⟩
    have he : (⟨34816 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock27.accepted j
  by_cases h28 : i.val < 36864
  ·
    let j : Fin 1024 := ⟨i.val - 35840, by have h := i.isLt; omega⟩
    have he : (⟨35840 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock28.accepted j
  by_cases h29 : i.val < 37888
  ·
    let j : Fin 1024 := ⟨i.val - 36864, by have h := i.isLt; omega⟩
    have he : (⟨36864 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock29.accepted j
  by_cases h30 : i.val < 38912
  ·
    let j : Fin 1024 := ⟨i.val - 37888, by have h := i.isLt; omega⟩
    have he : (⟨37888 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock30.accepted j
  by_cases h31 : i.val < 39936
  ·
    let j : Fin 1024 := ⟨i.val - 38912, by have h := i.isLt; omega⟩
    have he : (⟨38912 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock31.accepted j
  by_cases h32 : i.val < 40960
  ·
    let j : Fin 1024 := ⟨i.val - 39936, by have h := i.isLt; omega⟩
    have he : (⟨39936 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureTriangleBlock32.accepted j
  let j : Fin 334 := ⟨i.val - 40960, by have h := i.isLt; omega⟩
  have he : (⟨40960 + j.val, by have h := j.isLt; omega⟩ : Fin 41294) = i := by
    apply Fin.ext
    dsimp [j] <;> omega
  simpa only [he] using EJMStructureTriangleBlock33.accepted j

#print axioms triangle_structure

/-- All original 8689 rows are covered by exact disjoint kernel intervals. -/
theorem singleton_structure (i : Fin 8689) :
    checkStructure singletonPartialAct singletonRows i = true := by
  by_cases h0 : i.val < 1024
  ·
    let j : Fin 1024 := ⟨i.val - 0, by have h := i.isLt; omega⟩
    have he : (⟨0 + j.val, by have h := j.isLt; omega⟩ : Fin 8689) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureSingletonBlock0.accepted j
  by_cases h1 : i.val < 2048
  ·
    let j : Fin 1024 := ⟨i.val - 1024, by have h := i.isLt; omega⟩
    have he : (⟨1024 + j.val, by have h := j.isLt; omega⟩ : Fin 8689) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureSingletonBlock1.accepted j
  by_cases h2 : i.val < 3072
  ·
    let j : Fin 1024 := ⟨i.val - 2048, by have h := i.isLt; omega⟩
    have he : (⟨2048 + j.val, by have h := j.isLt; omega⟩ : Fin 8689) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureSingletonBlock2.accepted j
  by_cases h3 : i.val < 4096
  ·
    let j : Fin 1024 := ⟨i.val - 3072, by have h := i.isLt; omega⟩
    have he : (⟨3072 + j.val, by have h := j.isLt; omega⟩ : Fin 8689) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureSingletonBlock3.accepted j
  by_cases h4 : i.val < 5120
  ·
    let j : Fin 1024 := ⟨i.val - 4096, by have h := i.isLt; omega⟩
    have he : (⟨4096 + j.val, by have h := j.isLt; omega⟩ : Fin 8689) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureSingletonBlock4.accepted j
  by_cases h5 : i.val < 6144
  ·
    let j : Fin 1024 := ⟨i.val - 5120, by have h := i.isLt; omega⟩
    have he : (⟨5120 + j.val, by have h := j.isLt; omega⟩ : Fin 8689) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureSingletonBlock5.accepted j
  by_cases h6 : i.val < 7168
  ·
    let j : Fin 1024 := ⟨i.val - 6144, by have h := i.isLt; omega⟩
    have he : (⟨6144 + j.val, by have h := j.isLt; omega⟩ : Fin 8689) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureSingletonBlock6.accepted j
  by_cases h7 : i.val < 8192
  ·
    let j : Fin 1024 := ⟨i.val - 7168, by have h := i.isLt; omega⟩
    have he : (⟨7168 + j.val, by have h := j.isLt; omega⟩ : Fin 8689) = i := by
      apply Fin.ext
      dsimp [j] <;> omega
    simpa only [he] using EJMStructureSingletonBlock7.accepted j
  let j : Fin 497 := ⟨i.val - 8192, by have h := i.isLt; omega⟩
  have he : (⟨8192 + j.val, by have h := j.isLt; omega⟩ : Fin 8689) = i := by
    apply Fin.ext
    dsimp [j] <;> omega
  simpa only [he] using EJMStructureSingletonBlock8.accepted j

#print axioms singleton_structure

end D5.S3.Quantum.Entanglement.EJM.EJMStructureCertificates
