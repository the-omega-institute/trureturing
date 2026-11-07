/- GID: D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Assembly.raw_cut_00337; premises=D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_00155,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_00172,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_00176,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_00475,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_00509,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_00559,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_00610,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_00620,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_00636,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_00643,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_00652,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_00726,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_00727,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_00792,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_00884,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_00913,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_01043,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_01083,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_singleton_01106,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_triangle_00242,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_triangle_00301,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_triangle_00302,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_triangle_00326,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_triangle_01015,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_triangle_01397,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/MirrorsInitial.mirror_triangle_01645
   digest: The first twenty-six full literal MirrorRows match their original canonical row indices; equality covers hash, lower, slots and edges. -/

/- Source-only complete Tail442 checkpoint candidate. Kernel acceptance pending. -/
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.Helper

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalStateConcrete
open EJMCacheState (Cache triangleStep singletonStep step lower)
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
open EJMPartialBoundData (scale)
open Tail442V2.Helper
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)

def mirror_singleton_00155_row : EJMLocalCacheData.MirrorRow :=
  ⟨894500, (952963357779615), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_00155 :
    mirror_singleton_00155_row = EJMSingletonCacheData.mirror ⟨155, by decide⟩ := by
  have fields :
      mirror_singleton_00155_row.hash = (EJMSingletonCacheData.mirror ⟨155, by decide⟩).hash ∧
      mirror_singleton_00155_row.lower = (EJMSingletonCacheData.mirror ⟨155, by decide⟩).lower ∧
      mirror_singleton_00155_row.slots = (EJMSingletonCacheData.mirror ⟨155, by decide⟩).slots ∧
      mirror_singleton_00155_row.edges = (EJMSingletonCacheData.mirror ⟨155, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨155, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 894500 = hash ∧ (952963357779615 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_00155
def mirror_singleton_00172_row : EJMLocalCacheData.MirrorRow :=
  ⟨53875, (2306107857696825), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_00172 :
    mirror_singleton_00172_row = EJMSingletonCacheData.mirror ⟨172, by decide⟩ := by
  have fields :
      mirror_singleton_00172_row.hash = (EJMSingletonCacheData.mirror ⟨172, by decide⟩).hash ∧
      mirror_singleton_00172_row.lower = (EJMSingletonCacheData.mirror ⟨172, by decide⟩).lower ∧
      mirror_singleton_00172_row.slots = (EJMSingletonCacheData.mirror ⟨172, by decide⟩).slots ∧
      mirror_singleton_00172_row.edges = (EJMSingletonCacheData.mirror ⟨172, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨172, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 53875 = hash ∧ (2306107857696825 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_00172
def mirror_singleton_00176_row : EJMLocalCacheData.MirrorRow :=
  ⟨522625, (-1003991002449435), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_00176 :
    mirror_singleton_00176_row = EJMSingletonCacheData.mirror ⟨176, by decide⟩ := by
  have fields :
      mirror_singleton_00176_row.hash = (EJMSingletonCacheData.mirror ⟨176, by decide⟩).hash ∧
      mirror_singleton_00176_row.lower = (EJMSingletonCacheData.mirror ⟨176, by decide⟩).lower ∧
      mirror_singleton_00176_row.slots = (EJMSingletonCacheData.mirror ⟨176, by decide⟩).slots ∧
      mirror_singleton_00176_row.edges = (EJMSingletonCacheData.mirror ⟨176, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨176, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 522625 = hash ∧ (-1003991002449435 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_00176
def mirror_singleton_00475_row : EJMLocalCacheData.MirrorRow :=
  ⟨818900, (87789602294940), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_00475 :
    mirror_singleton_00475_row = EJMSingletonCacheData.mirror ⟨475, by decide⟩ := by
  have fields :
      mirror_singleton_00475_row.hash = (EJMSingletonCacheData.mirror ⟨475, by decide⟩).hash ∧
      mirror_singleton_00475_row.lower = (EJMSingletonCacheData.mirror ⟨475, by decide⟩).lower ∧
      mirror_singleton_00475_row.slots = (EJMSingletonCacheData.mirror ⟨475, by decide⟩).slots ∧
      mirror_singleton_00475_row.edges = (EJMSingletonCacheData.mirror ⟨475, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨475, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 818900 = hash ∧ (87789602294940 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_00475
def mirror_singleton_00509_row : EJMLocalCacheData.MirrorRow :=
  ⟨894525, (231226270487940), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_00509 :
    mirror_singleton_00509_row = EJMSingletonCacheData.mirror ⟨509, by decide⟩ := by
  have fields :
      mirror_singleton_00509_row.hash = (EJMSingletonCacheData.mirror ⟨509, by decide⟩).hash ∧
      mirror_singleton_00509_row.lower = (EJMSingletonCacheData.mirror ⟨509, by decide⟩).lower ∧
      mirror_singleton_00509_row.slots = (EJMSingletonCacheData.mirror ⟨509, by decide⟩).slots ∧
      mirror_singleton_00509_row.edges = (EJMSingletonCacheData.mirror ⟨509, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨509, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 894525 = hash ∧ (231226270487940 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_00509
def mirror_singleton_00559_row : EJMLocalCacheData.MirrorRow :=
  ⟨194525, (-664188621543720), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_00559 :
    mirror_singleton_00559_row = EJMSingletonCacheData.mirror ⟨559, by decide⟩ := by
  have fields :
      mirror_singleton_00559_row.hash = (EJMSingletonCacheData.mirror ⟨559, by decide⟩).hash ∧
      mirror_singleton_00559_row.lower = (EJMSingletonCacheData.mirror ⟨559, by decide⟩).lower ∧
      mirror_singleton_00559_row.slots = (EJMSingletonCacheData.mirror ⟨559, by decide⟩).slots ∧
      mirror_singleton_00559_row.edges = (EJMSingletonCacheData.mirror ⟨559, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨559, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 194525 = hash ∧ (-664188621543720 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_00559
def mirror_singleton_00610_row : EJMLocalCacheData.MirrorRow :=
  ⟨398275, (-163178568758205), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_00610 :
    mirror_singleton_00610_row = EJMSingletonCacheData.mirror ⟨610, by decide⟩ := by
  have fields :
      mirror_singleton_00610_row.hash = (EJMSingletonCacheData.mirror ⟨610, by decide⟩).hash ∧
      mirror_singleton_00610_row.lower = (EJMSingletonCacheData.mirror ⟨610, by decide⟩).lower ∧
      mirror_singleton_00610_row.slots = (EJMSingletonCacheData.mirror ⟨610, by decide⟩).slots ∧
      mirror_singleton_00610_row.edges = (EJMSingletonCacheData.mirror ⟨610, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨610, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 398275 = hash ∧ (-163178568758205 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_00610
def mirror_singleton_00620_row : EJMLocalCacheData.MirrorRow :=
  ⟨413900, (1105558261378935), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_00620 :
    mirror_singleton_00620_row = EJMSingletonCacheData.mirror ⟨620, by decide⟩ := by
  have fields :
      mirror_singleton_00620_row.hash = (EJMSingletonCacheData.mirror ⟨620, by decide⟩).hash ∧
      mirror_singleton_00620_row.lower = (EJMSingletonCacheData.mirror ⟨620, by decide⟩).lower ∧
      mirror_singleton_00620_row.slots = (EJMSingletonCacheData.mirror ⟨620, by decide⟩).slots ∧
      mirror_singleton_00620_row.edges = (EJMSingletonCacheData.mirror ⟨620, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨620, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 413900 = hash ∧ (1105558261378935 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_00620
def mirror_singleton_00636_row : EJMLocalCacheData.MirrorRow :=
  ⟨429525, (-358764225189825), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_00636 :
    mirror_singleton_00636_row = EJMSingletonCacheData.mirror ⟨636, by decide⟩ := by
  have fields :
      mirror_singleton_00636_row.hash = (EJMSingletonCacheData.mirror ⟨636, by decide⟩).hash ∧
      mirror_singleton_00636_row.lower = (EJMSingletonCacheData.mirror ⟨636, by decide⟩).lower ∧
      mirror_singleton_00636_row.slots = (EJMSingletonCacheData.mirror ⟨636, by decide⟩).slots ∧
      mirror_singleton_00636_row.edges = (EJMSingletonCacheData.mirror ⟨636, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨636, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 429525 = hash ∧ (-358764225189825 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_00636
def mirror_singleton_00643_row : EJMLocalCacheData.MirrorRow :=
  ⟨195150, (1373508743368125), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_00643 :
    mirror_singleton_00643_row = EJMSingletonCacheData.mirror ⟨643, by decide⟩ := by
  have fields :
      mirror_singleton_00643_row.hash = (EJMSingletonCacheData.mirror ⟨643, by decide⟩).hash ∧
      mirror_singleton_00643_row.lower = (EJMSingletonCacheData.mirror ⟨643, by decide⟩).lower ∧
      mirror_singleton_00643_row.slots = (EJMSingletonCacheData.mirror ⟨643, by decide⟩).slots ∧
      mirror_singleton_00643_row.edges = (EJMSingletonCacheData.mirror ⟨643, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨643, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 195150 = hash ∧ (1373508743368125 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_00643
def mirror_singleton_00652_row : EJMLocalCacheData.MirrorRow :=
  ⟨445150, (-1186920101255070), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_00652 :
    mirror_singleton_00652_row = EJMSingletonCacheData.mirror ⟨652, by decide⟩ := by
  have fields :
      mirror_singleton_00652_row.hash = (EJMSingletonCacheData.mirror ⟨652, by decide⟩).hash ∧
      mirror_singleton_00652_row.lower = (EJMSingletonCacheData.mirror ⟨652, by decide⟩).lower ∧
      mirror_singleton_00652_row.slots = (EJMSingletonCacheData.mirror ⟨652, by decide⟩).slots ∧
      mirror_singleton_00652_row.edges = (EJMSingletonCacheData.mirror ⟨652, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨652, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 445150 = hash ∧ (-1186920101255070 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_00652
def mirror_singleton_00726_row : EJMLocalCacheData.MirrorRow :=
  ⟨1385775, (3774710211090), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_00726 :
    mirror_singleton_00726_row = EJMSingletonCacheData.mirror ⟨726, by decide⟩ := by
  have fields :
      mirror_singleton_00726_row.hash = (EJMSingletonCacheData.mirror ⟨726, by decide⟩).hash ∧
      mirror_singleton_00726_row.lower = (EJMSingletonCacheData.mirror ⟨726, by decide⟩).lower ∧
      mirror_singleton_00726_row.slots = (EJMSingletonCacheData.mirror ⟨726, by decide⟩).slots ∧
      mirror_singleton_00726_row.edges = (EJMSingletonCacheData.mirror ⟨726, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨726, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 1385775 = hash ∧ (3774710211090 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_00726
def mirror_singleton_00727_row : EJMLocalCacheData.MirrorRow :=
  ⟨292025, (-478597344940260), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_00727 :
    mirror_singleton_00727_row = EJMSingletonCacheData.mirror ⟨727, by decide⟩ := by
  have fields :
      mirror_singleton_00727_row.hash = (EJMSingletonCacheData.mirror ⟨727, by decide⟩).hash ∧
      mirror_singleton_00727_row.lower = (EJMSingletonCacheData.mirror ⟨727, by decide⟩).lower ∧
      mirror_singleton_00727_row.slots = (EJMSingletonCacheData.mirror ⟨727, by decide⟩).slots ∧
      mirror_singleton_00727_row.edges = (EJMSingletonCacheData.mirror ⟨727, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨727, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 292025 = hash ∧ (-478597344940260 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_00727
def mirror_singleton_00792_row : EJMLocalCacheData.MirrorRow :=
  ⟨585275, (-898675145353440), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_00792 :
    mirror_singleton_00792_row = EJMSingletonCacheData.mirror ⟨792, by decide⟩ := by
  have fields :
      mirror_singleton_00792_row.hash = (EJMSingletonCacheData.mirror ⟨792, by decide⟩).hash ∧
      mirror_singleton_00792_row.lower = (EJMSingletonCacheData.mirror ⟨792, by decide⟩).lower ∧
      mirror_singleton_00792_row.slots = (EJMSingletonCacheData.mirror ⟨792, by decide⟩).slots ∧
      mirror_singleton_00792_row.edges = (EJMSingletonCacheData.mirror ⟨792, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨792, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 585275 = hash ∧ (-898675145353440 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_00792
def mirror_singleton_00884_row : EJMLocalCacheData.MirrorRow :=
  ⟨1382775, (150360734144985), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_00884 :
    mirror_singleton_00884_row = EJMSingletonCacheData.mirror ⟨884, by decide⟩ := by
  have fields :
      mirror_singleton_00884_row.hash = (EJMSingletonCacheData.mirror ⟨884, by decide⟩).hash ∧
      mirror_singleton_00884_row.lower = (EJMSingletonCacheData.mirror ⟨884, by decide⟩).lower ∧
      mirror_singleton_00884_row.slots = (EJMSingletonCacheData.mirror ⟨884, by decide⟩).slots ∧
      mirror_singleton_00884_row.edges = (EJMSingletonCacheData.mirror ⟨884, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨884, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 1382775 = hash ∧ (150360734144985 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_00884
def mirror_singleton_00913_row : EJMLocalCacheData.MirrorRow :=
  ⟨995275, (-651058434611130), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_00913 :
    mirror_singleton_00913_row = EJMSingletonCacheData.mirror ⟨913, by decide⟩ := by
  have fields :
      mirror_singleton_00913_row.hash = (EJMSingletonCacheData.mirror ⟨913, by decide⟩).hash ∧
      mirror_singleton_00913_row.lower = (EJMSingletonCacheData.mirror ⟨913, by decide⟩).lower ∧
      mirror_singleton_00913_row.slots = (EJMSingletonCacheData.mirror ⟨913, by decide⟩).slots ∧
      mirror_singleton_00913_row.edges = (EJMSingletonCacheData.mirror ⟨913, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨913, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 995275 = hash ∧ (-651058434611130 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_00913
def mirror_singleton_01043_row : EJMLocalCacheData.MirrorRow :=
  ⟨679530, (-2582553837844890), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_01043 :
    mirror_singleton_01043_row = EJMSingletonCacheData.mirror ⟨1043, by decide⟩ := by
  have fields :
      mirror_singleton_01043_row.hash = (EJMSingletonCacheData.mirror ⟨1043, by decide⟩).hash ∧
      mirror_singleton_01043_row.lower = (EJMSingletonCacheData.mirror ⟨1043, by decide⟩).lower ∧
      mirror_singleton_01043_row.slots = (EJMSingletonCacheData.mirror ⟨1043, by decide⟩).slots ∧
      mirror_singleton_01043_row.edges = (EJMSingletonCacheData.mirror ⟨1043, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨1043, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 679530 = hash ∧ (-2582553837844890 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_01043
def mirror_singleton_01083_row : EJMLocalCacheData.MirrorRow :=
  ⟨1385780, (-357354293568090), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_01083 :
    mirror_singleton_01083_row = EJMSingletonCacheData.mirror ⟨1083, by decide⟩ := by
  have fields :
      mirror_singleton_01083_row.hash = (EJMSingletonCacheData.mirror ⟨1083, by decide⟩).hash ∧
      mirror_singleton_01083_row.lower = (EJMSingletonCacheData.mirror ⟨1083, by decide⟩).lower ∧
      mirror_singleton_01083_row.slots = (EJMSingletonCacheData.mirror ⟨1083, by decide⟩).slots ∧
      mirror_singleton_01083_row.edges = (EJMSingletonCacheData.mirror ⟨1083, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨1083, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 1385780 = hash ∧ (-357354293568090 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_01083
def mirror_singleton_01106_row : EJMLocalCacheData.MirrorRow :=
  ⟨902155, (-1192642712695980), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_singleton_01106 :
    mirror_singleton_01106_row = EJMSingletonCacheData.mirror ⟨1106, by decide⟩ := by
  have fields :
      mirror_singleton_01106_row.hash = (EJMSingletonCacheData.mirror ⟨1106, by decide⟩).hash ∧
      mirror_singleton_01106_row.lower = (EJMSingletonCacheData.mirror ⟨1106, by decide⟩).lower ∧
      mirror_singleton_01106_row.slots = (EJMSingletonCacheData.mirror ⟨1106, by decide⟩).slots ∧
      mirror_singleton_01106_row.edges = (EJMSingletonCacheData.mirror ⟨1106, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMSingletonCacheData.mirror ⟨1106, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 902155 = hash ∧ (-1192642712695980 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_singleton_01106
def mirror_triangle_00242_row : EJMLocalCacheData.MirrorRow :=
  ⟨2866250, (-4210815426559560), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_00242 :
    mirror_triangle_00242_row = EJMTriangleCacheData.mirror ⟨242, by decide⟩ := by
  have fields :
      mirror_triangle_00242_row.hash = (EJMTriangleCacheData.mirror ⟨242, by decide⟩).hash ∧
      mirror_triangle_00242_row.lower = (EJMTriangleCacheData.mirror ⟨242, by decide⟩).lower ∧
      mirror_triangle_00242_row.slots = (EJMTriangleCacheData.mirror ⟨242, by decide⟩).slots ∧
      mirror_triangle_00242_row.edges = (EJMTriangleCacheData.mirror ⟨242, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨242, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 2866250 = hash ∧ (-4210815426559560 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_00242
def mirror_triangle_00301_row : EJMLocalCacheData.MirrorRow :=
  ⟨2991375, (-2662784195384040), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_00301 :
    mirror_triangle_00301_row = EJMTriangleCacheData.mirror ⟨301, by decide⟩ := by
  have fields :
      mirror_triangle_00301_row.hash = (EJMTriangleCacheData.mirror ⟨301, by decide⟩).hash ∧
      mirror_triangle_00301_row.lower = (EJMTriangleCacheData.mirror ⟨301, by decide⟩).lower ∧
      mirror_triangle_00301_row.slots = (EJMTriangleCacheData.mirror ⟨301, by decide⟩).slots ∧
      mirror_triangle_00301_row.edges = (EJMTriangleCacheData.mirror ⟨301, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨301, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 2991375 = hash ∧ (-2662784195384040 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_00301
def mirror_triangle_00302_row : EJMLocalCacheData.MirrorRow :=
  ⟨4944500, (-3893165080248990), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_00302 :
    mirror_triangle_00302_row = EJMTriangleCacheData.mirror ⟨302, by decide⟩ := by
  have fields :
      mirror_triangle_00302_row.hash = (EJMTriangleCacheData.mirror ⟨302, by decide⟩).hash ∧
      mirror_triangle_00302_row.lower = (EJMTriangleCacheData.mirror ⟨302, by decide⟩).lower ∧
      mirror_triangle_00302_row.slots = (EJMTriangleCacheData.mirror ⟨302, by decide⟩).slots ∧
      mirror_triangle_00302_row.edges = (EJMTriangleCacheData.mirror ⟨302, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨302, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 4944500 = hash ∧ (-3893165080248990 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_00302
def mirror_triangle_00326_row : EJMLocalCacheData.MirrorRow :=
  ⟨3307625, (-22283621971065), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_00326 :
    mirror_triangle_00326_row = EJMTriangleCacheData.mirror ⟨326, by decide⟩ := by
  have fields :
      mirror_triangle_00326_row.hash = (EJMTriangleCacheData.mirror ⟨326, by decide⟩).hash ∧
      mirror_triangle_00326_row.lower = (EJMTriangleCacheData.mirror ⟨326, by decide⟩).lower ∧
      mirror_triangle_00326_row.slots = (EJMTriangleCacheData.mirror ⟨326, by decide⟩).slots ∧
      mirror_triangle_00326_row.edges = (EJMTriangleCacheData.mirror ⟨326, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨326, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 3307625 = hash ∧ (-22283621971065 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_00326
def mirror_triangle_01015_row : EJMLocalCacheData.MirrorRow :=
  ⟨4495025, (6920275813517430), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_01015 :
    mirror_triangle_01015_row = EJMTriangleCacheData.mirror ⟨1015, by decide⟩ := by
  have fields :
      mirror_triangle_01015_row.hash = (EJMTriangleCacheData.mirror ⟨1015, by decide⟩).hash ∧
      mirror_triangle_01015_row.lower = (EJMTriangleCacheData.mirror ⟨1015, by decide⟩).lower ∧
      mirror_triangle_01015_row.slots = (EJMTriangleCacheData.mirror ⟨1015, by decide⟩).slots ∧
      mirror_triangle_01015_row.edges = (EJMTriangleCacheData.mirror ⟨1015, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨1015, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 4495025 = hash ∧ (6920275813517430 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_01015
def mirror_triangle_01397_row : EJMLocalCacheData.MirrorRow :=
  ⟨6725005, (5172784952197590), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_01397 :
    mirror_triangle_01397_row = EJMTriangleCacheData.mirror ⟨1397, by decide⟩ := by
  have fields :
      mirror_triangle_01397_row.hash = (EJMTriangleCacheData.mirror ⟨1397, by decide⟩).hash ∧
      mirror_triangle_01397_row.lower = (EJMTriangleCacheData.mirror ⟨1397, by decide⟩).lower ∧
      mirror_triangle_01397_row.slots = (EJMTriangleCacheData.mirror ⟨1397, by decide⟩).slots ∧
      mirror_triangle_01397_row.edges = (EJMTriangleCacheData.mirror ⟨1397, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨1397, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 6725005 = hash ∧ (5172784952197590 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_01397
def mirror_triangle_01645_row : EJMLocalCacheData.MirrorRow :=
  ⟨6725630, (1071971890325700), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_01645 :
    mirror_triangle_01645_row = EJMTriangleCacheData.mirror ⟨1645, by decide⟩ := by
  have fields :
      mirror_triangle_01645_row.hash = (EJMTriangleCacheData.mirror ⟨1645, by decide⟩).hash ∧
      mirror_triangle_01645_row.lower = (EJMTriangleCacheData.mirror ⟨1645, by decide⟩).lower ∧
      mirror_triangle_01645_row.slots = (EJMTriangleCacheData.mirror ⟨1645, by decide⟩).slots ∧
      mirror_triangle_01645_row.edges = (EJMTriangleCacheData.mirror ⟨1645, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨1645, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 6725630 = hash ∧ (1071971890325700 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_01645

end D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalStateConcrete
