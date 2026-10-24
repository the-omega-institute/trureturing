/- GID: D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Mirrors
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Mirrors
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Assembly.raw_cut_00337; premises=D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Mirrors.mirror_triangle_00157,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Mirrors.mirror_triangle_00196,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Mirrors.mirror_triangle_00280,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Mirrors.mirror_triangle_00291,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Mirrors.mirror_triangle_01429,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Mirrors.mirror_triangle_01677,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Mirrors.mirror_triangle_01909,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Mirrors.mirror_triangle_02066,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Mirrors.mirror_triangle_02564,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Mirrors.mirror_triangle_02576,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Mirrors.mirror_triangle_02642,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Mirrors.mirror_triangle_03153,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Mirrors.mirror_triangle_03563,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Mirrors.mirror_triangle_03931,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Mirrors.mirror_triangle_04037
   digest: Fifteen complete literal MirrorRows and their exact original indexed row equalities support the local transitions of prefix 5335037. -/

/- Source-only complete original Tail442 context. Kernel acceptance pending. -/
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.Helper
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.Mirrors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037
open EJMCacheState (Cache CachedLocal triangleStep singletonStep step lower)
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
open EJMPartialBoundData (scale)
open Tail442V2.Helper
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open scoped BigOperators

def mirror_triangle_00157_row : EJMLocalCacheData.MirrorRow :=
  ⟨3238125, (-4325860378526505), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_00157 :
    mirror_triangle_00157_row = EJMTriangleCacheData.mirror ⟨157, by decide⟩ := by
  have fields :
      mirror_triangle_00157_row.hash = (EJMTriangleCacheData.mirror ⟨157, by decide⟩).hash ∧
      mirror_triangle_00157_row.lower = (EJMTriangleCacheData.mirror ⟨157, by decide⟩).lower ∧
      mirror_triangle_00157_row.slots = (EJMTriangleCacheData.mirror ⟨157, by decide⟩).slots ∧
      mirror_triangle_00157_row.edges = (EJMTriangleCacheData.mirror ⟨157, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨157, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 3238125 = hash ∧ (-4325860378526505 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_00157
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
def mirror_triangle_00280_row : EJMLocalCacheData.MirrorRow :=
  ⟨2835125, (-4739636064577050), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_00280 :
    mirror_triangle_00280_row = EJMTriangleCacheData.mirror ⟨280, by decide⟩ := by
  have fields :
      mirror_triangle_00280_row.hash = (EJMTriangleCacheData.mirror ⟨280, by decide⟩).hash ∧
      mirror_triangle_00280_row.lower = (EJMTriangleCacheData.mirror ⟨280, by decide⟩).lower ∧
      mirror_triangle_00280_row.slots = (EJMTriangleCacheData.mirror ⟨280, by decide⟩).slots ∧
      mirror_triangle_00280_row.edges = (EJMTriangleCacheData.mirror ⟨280, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨280, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 2835125 = hash ∧ (-4739636064577050 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_00280
def mirror_triangle_00291_row : EJMLocalCacheData.MirrorRow :=
  ⟨2913250, (-5282270092971690), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_00291 :
    mirror_triangle_00291_row = EJMTriangleCacheData.mirror ⟨291, by decide⟩ := by
  have fields :
      mirror_triangle_00291_row.hash = (EJMTriangleCacheData.mirror ⟨291, by decide⟩).hash ∧
      mirror_triangle_00291_row.lower = (EJMTriangleCacheData.mirror ⟨291, by decide⟩).lower ∧
      mirror_triangle_00291_row.slots = (EJMTriangleCacheData.mirror ⟨291, by decide⟩).slots ∧
      mirror_triangle_00291_row.edges = (EJMTriangleCacheData.mirror ⟨291, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨291, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 2913250 = hash ∧ (-5282270092971690 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_00291
def mirror_triangle_01429_row : EJMLocalCacheData.MirrorRow :=
  ⟨6881255, (1547377933952760), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_01429 :
    mirror_triangle_01429_row = EJMTriangleCacheData.mirror ⟨1429, by decide⟩ := by
  have fields :
      mirror_triangle_01429_row.hash = (EJMTriangleCacheData.mirror ⟨1429, by decide⟩).hash ∧
      mirror_triangle_01429_row.lower = (EJMTriangleCacheData.mirror ⟨1429, by decide⟩).lower ∧
      mirror_triangle_01429_row.slots = (EJMTriangleCacheData.mirror ⟨1429, by decide⟩).slots ∧
      mirror_triangle_01429_row.edges = (EJMTriangleCacheData.mirror ⟨1429, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨1429, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 6881255 = hash ∧ (1547377933952760 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_01429
def mirror_triangle_01677_row : EJMLocalCacheData.MirrorRow :=
  ⟨6881880, (1182776615186985), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_01677 :
    mirror_triangle_01677_row = EJMTriangleCacheData.mirror ⟨1677, by decide⟩ := by
  have fields :
      mirror_triangle_01677_row.hash = (EJMTriangleCacheData.mirror ⟨1677, by decide⟩).hash ∧
      mirror_triangle_01677_row.lower = (EJMTriangleCacheData.mirror ⟨1677, by decide⟩).lower ∧
      mirror_triangle_01677_row.slots = (EJMTriangleCacheData.mirror ⟨1677, by decide⟩).slots ∧
      mirror_triangle_01677_row.edges = (EJMTriangleCacheData.mirror ⟨1677, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨1677, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 6881880 = hash ∧ (1182776615186985 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_01677
def mirror_triangle_01909_row : EJMLocalCacheData.MirrorRow :=
  ⟨7195005, (4274493570749220), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_01909 :
    mirror_triangle_01909_row = EJMTriangleCacheData.mirror ⟨1909, by decide⟩ := by
  have fields :
      mirror_triangle_01909_row.hash = (EJMTriangleCacheData.mirror ⟨1909, by decide⟩).hash ∧
      mirror_triangle_01909_row.lower = (EJMTriangleCacheData.mirror ⟨1909, by decide⟩).lower ∧
      mirror_triangle_01909_row.slots = (EJMTriangleCacheData.mirror ⟨1909, by decide⟩).slots ∧
      mirror_triangle_01909_row.edges = (EJMTriangleCacheData.mirror ⟨1909, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨1909, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 7195005 = hash ∧ (4274493570749220 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_01909
def mirror_triangle_02066_row : EJMLocalCacheData.MirrorRow :=
  ⟨5245005, (3568591555390680), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_02066 :
    mirror_triangle_02066_row = EJMTriangleCacheData.mirror ⟨2066, by decide⟩ := by
  have fields :
      mirror_triangle_02066_row.hash = (EJMTriangleCacheData.mirror ⟨2066, by decide⟩).hash ∧
      mirror_triangle_02066_row.lower = (EJMTriangleCacheData.mirror ⟨2066, by decide⟩).lower ∧
      mirror_triangle_02066_row.slots = (EJMTriangleCacheData.mirror ⟨2066, by decide⟩).slots ∧
      mirror_triangle_02066_row.edges = (EJMTriangleCacheData.mirror ⟨2066, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨2066, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 5245005 = hash ∧ (3568591555390680 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_02066
def mirror_triangle_02564_row : EJMLocalCacheData.MirrorRow :=
  ⟨4854505, (4768678450750305), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_02564 :
    mirror_triangle_02564_row = EJMTriangleCacheData.mirror ⟨2564, by decide⟩ := by
  have fields :
      mirror_triangle_02564_row.hash = (EJMTriangleCacheData.mirror ⟨2564, by decide⟩).hash ∧
      mirror_triangle_02564_row.lower = (EJMTriangleCacheData.mirror ⟨2564, by decide⟩).lower ∧
      mirror_triangle_02564_row.slots = (EJMTriangleCacheData.mirror ⟨2564, by decide⟩).slots ∧
      mirror_triangle_02564_row.edges = (EJMTriangleCacheData.mirror ⟨2564, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨2564, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 4854505 = hash ∧ (4768678450750305 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_02564
def mirror_triangle_02576_row : EJMLocalCacheData.MirrorRow :=
  ⟨2370130, (4134508150426290), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_02576 :
    mirror_triangle_02576_row = EJMTriangleCacheData.mirror ⟨2576, by decide⟩ := by
  have fields :
      mirror_triangle_02576_row.hash = (EJMTriangleCacheData.mirror ⟨2576, by decide⟩).hash ∧
      mirror_triangle_02576_row.lower = (EJMTriangleCacheData.mirror ⟨2576, by decide⟩).lower ∧
      mirror_triangle_02576_row.slots = (EJMTriangleCacheData.mirror ⟨2576, by decide⟩).slots ∧
      mirror_triangle_02576_row.edges = (EJMTriangleCacheData.mirror ⟨2576, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨2576, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 2370130 = hash ∧ (4134508150426290 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_02576
def mirror_triangle_02642_row : EJMLocalCacheData.MirrorRow :=
  ⟨4104505, (8503459090306635), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_02642 :
    mirror_triangle_02642_row = EJMTriangleCacheData.mirror ⟨2642, by decide⟩ := by
  have fields :
      mirror_triangle_02642_row.hash = (EJMTriangleCacheData.mirror ⟨2642, by decide⟩).hash ∧
      mirror_triangle_02642_row.lower = (EJMTriangleCacheData.mirror ⟨2642, by decide⟩).lower ∧
      mirror_triangle_02642_row.slots = (EJMTriangleCacheData.mirror ⟨2642, by decide⟩).slots ∧
      mirror_triangle_02642_row.edges = (EJMTriangleCacheData.mirror ⟨2642, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨2642, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 4104505 = hash ∧ (8503459090306635 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_02642
def mirror_triangle_03153_row : EJMLocalCacheData.MirrorRow :=
  ⟨787555, (4452400422698865), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_03153 :
    mirror_triangle_03153_row = EJMTriangleCacheData.mirror ⟨3153, by decide⟩ := by
  have fields :
      mirror_triangle_03153_row.hash = (EJMTriangleCacheData.mirror ⟨3153, by decide⟩).hash ∧
      mirror_triangle_03153_row.lower = (EJMTriangleCacheData.mirror ⟨3153, by decide⟩).lower ∧
      mirror_triangle_03153_row.slots = (EJMTriangleCacheData.mirror ⟨3153, by decide⟩).slots ∧
      mirror_triangle_03153_row.edges = (EJMTriangleCacheData.mirror ⟨3153, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨3153, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 787555 = hash ∧ (4452400422698865 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_03153
def mirror_triangle_03563_row : EJMLocalCacheData.MirrorRow :=
  ⟨788180, (1576456270479090), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_03563 :
    mirror_triangle_03563_row = EJMTriangleCacheData.mirror ⟨3563, by decide⟩ := by
  have fields :
      mirror_triangle_03563_row.hash = (EJMTriangleCacheData.mirror ⟨3563, by decide⟩).hash ∧
      mirror_triangle_03563_row.lower = (EJMTriangleCacheData.mirror ⟨3563, by decide⟩).lower ∧
      mirror_triangle_03563_row.slots = (EJMTriangleCacheData.mirror ⟨3563, by decide⟩).slots ∧
      mirror_triangle_03563_row.edges = (EJMTriangleCacheData.mirror ⟨3563, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨3563, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 788180 = hash ∧ (1576456270479090 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_03563
def mirror_triangle_03931_row : EJMLocalCacheData.MirrorRow :=
  ⟨788805, (6406381636322850), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_03931 :
    mirror_triangle_03931_row = EJMTriangleCacheData.mirror ⟨3931, by decide⟩ := by
  have fields :
      mirror_triangle_03931_row.hash = (EJMTriangleCacheData.mirror ⟨3931, by decide⟩).hash ∧
      mirror_triangle_03931_row.lower = (EJMTriangleCacheData.mirror ⟨3931, by decide⟩).lower ∧
      mirror_triangle_03931_row.slots = (EJMTriangleCacheData.mirror ⟨3931, by decide⟩).slots ∧
      mirror_triangle_03931_row.edges = (EJMTriangleCacheData.mirror ⟨3931, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨3931, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 788805 = hash ∧ (6406381636322850 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_03931
def mirror_triangle_04037_row : EJMLocalCacheData.MirrorRow :=
  ⟨166930, (3874565080286355), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_04037 :
    mirror_triangle_04037_row = EJMTriangleCacheData.mirror ⟨4037, by decide⟩ := by
  have fields :
      mirror_triangle_04037_row.hash = (EJMTriangleCacheData.mirror ⟨4037, by decide⟩).hash ∧
      mirror_triangle_04037_row.lower = (EJMTriangleCacheData.mirror ⟨4037, by decide⟩).lower ∧
      mirror_triangle_04037_row.slots = (EJMTriangleCacheData.mirror ⟨4037, by decide⟩).slots ∧
      mirror_triangle_04037_row.edges = (EJMTriangleCacheData.mirror ⟨4037, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨4037, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 166930 = hash ∧ (3874565080286355 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_04037

end D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037
