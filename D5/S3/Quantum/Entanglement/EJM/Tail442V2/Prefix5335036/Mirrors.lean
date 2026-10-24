/- GID: D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/Mirrors
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/Mirrors
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Assembly.raw_cut_00337; premises=D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/Mirrors.mirror_triangle_00173,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/Mirrors.mirror_triangle_00196,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/Mirrors.mirror_triangle_00197,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/Mirrors.mirror_triangle_00407,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/Mirrors.mirror_triangle_01381,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/Mirrors.mirror_triangle_01603,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/Mirrors.mirror_triangle_01629,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/Mirrors.mirror_triangle_01885,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/Mirrors.mirror_triangle_02047,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/Mirrors.mirror_triangle_03181,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/Mirrors.mirror_triangle_03586,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/Mirrors.mirror_triangle_03759,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/Mirrors.mirror_triangle_03770,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/Mirrors.mirror_triangle_03939,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/Mirrors.mirror_triangle_04041
   digest: Fifteen complete literal MirrorRows and their exact original indexed row equalities support the local transitions of prefix 5335036. -/

/- Source-only complete original Tail442 context. Kernel acceptance pending. -/
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.Helper
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.Mirrors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335036
open EJMCacheState (Cache CachedLocal triangleStep singletonStep step lower)
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
open EJMPartialBoundData (scale)
open Tail442V2.Helper
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open scoped BigOperators

def mirror_triangle_00173_row : EJMLocalCacheData.MirrorRow :=
  ⟨2819375, (-6835820754953190), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_00173 :
    mirror_triangle_00173_row = EJMTriangleCacheData.mirror ⟨173, by decide⟩ := by
  have fields :
      mirror_triangle_00173_row.hash = (EJMTriangleCacheData.mirror ⟨173, by decide⟩).hash ∧
      mirror_triangle_00173_row.lower = (EJMTriangleCacheData.mirror ⟨173, by decide⟩).lower ∧
      mirror_triangle_00173_row.slots = (EJMTriangleCacheData.mirror ⟨173, by decide⟩).slots ∧
      mirror_triangle_00173_row.edges = (EJMTriangleCacheData.mirror ⟨173, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨173, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 2819375 = hash ∧ (-6835820754953190 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_00173
def mirror_triangle_00196_row : EJMLocalCacheData.MirrorRow :=
  ⟨2835000, (-4029008020694475), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_00196 :
    mirror_triangle_00196_row = EJMTriangleCacheData.mirror ⟨196, by decide⟩ := by
  have fields :
      mirror_triangle_00196_row.hash = (EJMTriangleCacheData.mirror ⟨196, by decide⟩).hash ∧
      mirror_triangle_00196_row.lower = (EJMTriangleCacheData.mirror ⟨196, by decide⟩).lower ∧
      mirror_triangle_00196_row.slots = (EJMTriangleCacheData.mirror ⟨196, by decide⟩).slots ∧
      mirror_triangle_00196_row.edges = (EJMTriangleCacheData.mirror ⟨196, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨196, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 2835000 = hash ∧ (-4029008020694475 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_00196
def mirror_triangle_00197_row : EJMLocalCacheData.MirrorRow :=
  ⟨4788125, (-5361019680273075), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_00197 :
    mirror_triangle_00197_row = EJMTriangleCacheData.mirror ⟨197, by decide⟩ := by
  have fields :
      mirror_triangle_00197_row.hash = (EJMTriangleCacheData.mirror ⟨197, by decide⟩).hash ∧
      mirror_triangle_00197_row.lower = (EJMTriangleCacheData.mirror ⟨197, by decide⟩).lower ∧
      mirror_triangle_00197_row.slots = (EJMTriangleCacheData.mirror ⟨197, by decide⟩).slots ∧
      mirror_triangle_00197_row.edges = (EJMTriangleCacheData.mirror ⟨197, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨197, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 4788125 = hash ∧ (-5361019680273075 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_00197
def mirror_triangle_00407_row : EJMLocalCacheData.MirrorRow :=
  ⟨1331275, (3540906576290265), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_00407 :
    mirror_triangle_00407_row = EJMTriangleCacheData.mirror ⟨407, by decide⟩ := by
  have fields :
      mirror_triangle_00407_row.hash = (EJMTriangleCacheData.mirror ⟨407, by decide⟩).hash ∧
      mirror_triangle_00407_row.lower = (EJMTriangleCacheData.mirror ⟨407, by decide⟩).lower ∧
      mirror_triangle_00407_row.slots = (EJMTriangleCacheData.mirror ⟨407, by decide⟩).slots ∧
      mirror_triangle_00407_row.edges = (EJMTriangleCacheData.mirror ⟨407, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨407, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 1331275 = hash ∧ (3540906576290265 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_00407
def mirror_triangle_01381_row : EJMLocalCacheData.MirrorRow :=
  ⟨6646880, (4277590094494080), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_01381 :
    mirror_triangle_01381_row = EJMTriangleCacheData.mirror ⟨1381, by decide⟩ := by
  have fields :
      mirror_triangle_01381_row.hash = (EJMTriangleCacheData.mirror ⟨1381, by decide⟩).hash ∧
      mirror_triangle_01381_row.lower = (EJMTriangleCacheData.mirror ⟨1381, by decide⟩).lower ∧
      mirror_triangle_01381_row.slots = (EJMTriangleCacheData.mirror ⟨1381, by decide⟩).slots ∧
      mirror_triangle_01381_row.edges = (EJMTriangleCacheData.mirror ⟨1381, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨1381, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 6646880 = hash ∧ (4277590094494080 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_01381
def mirror_triangle_01603_row : EJMLocalCacheData.MirrorRow :=
  ⟨3238130, (5998646811427725), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_01603 :
    mirror_triangle_01603_row = EJMTriangleCacheData.mirror ⟨1603, by decide⟩ := by
  have fields :
      mirror_triangle_01603_row.hash = (EJMTriangleCacheData.mirror ⟨1603, by decide⟩).hash ∧
      mirror_triangle_01603_row.lower = (EJMTriangleCacheData.mirror ⟨1603, by decide⟩).lower ∧
      mirror_triangle_01603_row.slots = (EJMTriangleCacheData.mirror ⟨1603, by decide⟩).slots ∧
      mirror_triangle_01603_row.edges = (EJMTriangleCacheData.mirror ⟨1603, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨1603, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 3238130 = hash ∧ (5998646811427725 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_01603
def mirror_triangle_01629_row : EJMLocalCacheData.MirrorRow :=
  ⟨6647505, (6198059968141860), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_01629 :
    mirror_triangle_01629_row = EJMTriangleCacheData.mirror ⟨1629, by decide⟩ := by
  have fields :
      mirror_triangle_01629_row.hash = (EJMTriangleCacheData.mirror ⟨1629, by decide⟩).hash ∧
      mirror_triangle_01629_row.lower = (EJMTriangleCacheData.mirror ⟨1629, by decide⟩).lower ∧
      mirror_triangle_01629_row.slots = (EJMTriangleCacheData.mirror ⟨1629, by decide⟩).slots ∧
      mirror_triangle_01629_row.edges = (EJMTriangleCacheData.mirror ⟨1629, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨1629, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 6647505 = hash ∧ (6198059968141860 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_01629
def mirror_triangle_01885_row : EJMLocalCacheData.MirrorRow :=
  ⟨6648130, (2871463766973165), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_01885 :
    mirror_triangle_01885_row = EJMTriangleCacheData.mirror ⟨1885, by decide⟩ := by
  have fields :
      mirror_triangle_01885_row.hash = (EJMTriangleCacheData.mirror ⟨1885, by decide⟩).hash ∧
      mirror_triangle_01885_row.lower = (EJMTriangleCacheData.mirror ⟨1885, by decide⟩).lower ∧
      mirror_triangle_01885_row.slots = (EJMTriangleCacheData.mirror ⟨1885, by decide⟩).slots ∧
      mirror_triangle_01885_row.edges = (EJMTriangleCacheData.mirror ⟨1885, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨1885, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 6648130 = hash ∧ (2871463766973165 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_01885
def mirror_triangle_02047_row : EJMLocalCacheData.MirrorRow :=
  ⟨5088755, (2135021175528150), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_02047 :
    mirror_triangle_02047_row = EJMTriangleCacheData.mirror ⟨2047, by decide⟩ := by
  have fields :
      mirror_triangle_02047_row.hash = (EJMTriangleCacheData.mirror ⟨2047, by decide⟩).hash ∧
      mirror_triangle_02047_row.lower = (EJMTriangleCacheData.mirror ⟨2047, by decide⟩).lower ∧
      mirror_triangle_02047_row.slots = (EJMTriangleCacheData.mirror ⟨2047, by decide⟩).slots ∧
      mirror_triangle_02047_row.edges = (EJMTriangleCacheData.mirror ⟨2047, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨2047, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 5088755 = hash ∧ (2135021175528150 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_02047
def mirror_triangle_03181_row : EJMLocalCacheData.MirrorRow :=
  ⟨943805, (2866678673661075), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_03181 :
    mirror_triangle_03181_row = EJMTriangleCacheData.mirror ⟨3181, by decide⟩ := by
  have fields :
      mirror_triangle_03181_row.hash = (EJMTriangleCacheData.mirror ⟨3181, by decide⟩).hash ∧
      mirror_triangle_03181_row.lower = (EJMTriangleCacheData.mirror ⟨3181, by decide⟩).lower ∧
      mirror_triangle_03181_row.slots = (EJMTriangleCacheData.mirror ⟨3181, by decide⟩).slots ∧
      mirror_triangle_03181_row.edges = (EJMTriangleCacheData.mirror ⟨3181, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨3181, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 943805 = hash ∧ (2866678673661075 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_03181
def mirror_triangle_03586_row : EJMLocalCacheData.MirrorRow :=
  ⟨944430, (4122035173680060), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_03586 :
    mirror_triangle_03586_row = EJMTriangleCacheData.mirror ⟨3586, by decide⟩ := by
  have fields :
      mirror_triangle_03586_row.hash = (EJMTriangleCacheData.mirror ⟨3586, by decide⟩).hash ∧
      mirror_triangle_03586_row.lower = (EJMTriangleCacheData.mirror ⟨3586, by decide⟩).lower ∧
      mirror_triangle_03586_row.slots = (EJMTriangleCacheData.mirror ⟨3586, by decide⟩).slots ∧
      mirror_triangle_03586_row.edges = (EJMTriangleCacheData.mirror ⟨3586, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨3586, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 944430 = hash ∧ (4122035173680060 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_03586
def mirror_triangle_03759_row : EJMLocalCacheData.MirrorRow :=
  ⟨791305, (3676348850225415), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_03759 :
    mirror_triangle_03759_row = EJMTriangleCacheData.mirror ⟨3759, by decide⟩ := by
  have fields :
      mirror_triangle_03759_row.hash = (EJMTriangleCacheData.mirror ⟨3759, by decide⟩).hash ∧
      mirror_triangle_03759_row.lower = (EJMTriangleCacheData.mirror ⟨3759, by decide⟩).lower ∧
      mirror_triangle_03759_row.slots = (EJMTriangleCacheData.mirror ⟨3759, by decide⟩).slots ∧
      mirror_triangle_03759_row.edges = (EJMTriangleCacheData.mirror ⟨3759, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨3759, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 791305 = hash ∧ (3676348850225415 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_03759
def mirror_triangle_03770_row : EJMLocalCacheData.MirrorRow :=
  ⟨166305, (3650541478758720), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_03770 :
    mirror_triangle_03770_row = EJMTriangleCacheData.mirror ⟨3770, by decide⟩ := by
  have fields :
      mirror_triangle_03770_row.hash = (EJMTriangleCacheData.mirror ⟨3770, by decide⟩).hash ∧
      mirror_triangle_03770_row.lower = (EJMTriangleCacheData.mirror ⟨3770, by decide⟩).lower ∧
      mirror_triangle_03770_row.slots = (EJMTriangleCacheData.mirror ⟨3770, by decide⟩).slots ∧
      mirror_triangle_03770_row.edges = (EJMTriangleCacheData.mirror ⟨3770, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨3770, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 166305 = hash ∧ (3650541478758720 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_03770
def mirror_triangle_03939_row : EJMLocalCacheData.MirrorRow :=
  ⟨945055, (10197944485530165), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_03939 :
    mirror_triangle_03939_row = EJMTriangleCacheData.mirror ⟨3939, by decide⟩ := by
  have fields :
      mirror_triangle_03939_row.hash = (EJMTriangleCacheData.mirror ⟨3939, by decide⟩).hash ∧
      mirror_triangle_03939_row.lower = (EJMTriangleCacheData.mirror ⟨3939, by decide⟩).lower ∧
      mirror_triangle_03939_row.slots = (EJMTriangleCacheData.mirror ⟨3939, by decide⟩).slots ∧
      mirror_triangle_03939_row.edges = (EJMTriangleCacheData.mirror ⟨3939, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨3939, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 945055 = hash ∧ (10197944485530165 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_03939
def mirror_triangle_04041_row : EJMLocalCacheData.MirrorRow :=
  ⟨948180, (4808755408250430), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_04041 :
    mirror_triangle_04041_row = EJMTriangleCacheData.mirror ⟨4041, by decide⟩ := by
  have fields :
      mirror_triangle_04041_row.hash = (EJMTriangleCacheData.mirror ⟨4041, by decide⟩).hash ∧
      mirror_triangle_04041_row.lower = (EJMTriangleCacheData.mirror ⟨4041, by decide⟩).lower ∧
      mirror_triangle_04041_row.slots = (EJMTriangleCacheData.mirror ⟨4041, by decide⟩).slots ∧
      mirror_triangle_04041_row.edges = (EJMTriangleCacheData.mirror ⟨4041, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨4041, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 948180 = hash ∧ (4808755408250430 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_04041

end D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335036
