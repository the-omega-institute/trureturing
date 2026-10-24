/- GID: D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Assembly.raw_cut_00337; premises=D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_01897,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_02016,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_02058,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_03169,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_03197,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_03602,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_03910,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_03943,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_04045,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_04894,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_05011,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_05047,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_05068,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_06929,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_07245,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_07614,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_07758,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_09773,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_10343,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_10859,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_11011,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_13064,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_13555,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_14655,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Mirrors.mirror_triangle_14775
   digest: The remaining twenty-five full literal MirrorRows match their original canonical row indices after importing the initial twenty-six full-row receipts. -/

/- Source-only complete Tail442 checkpoint candidate. Kernel acceptance pending. -/
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.Helper
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.MirrorsInitial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalStateConcrete
open EJMCacheState (Cache triangleStep singletonStep step lower)
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
open EJMPartialBoundData (scale)
open Tail442V2.Helper
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)

def mirror_triangle_01897_row : EJMLocalCacheData.MirrorRow :=
  ⟨6726255, (5236499333225160), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_01897 :
    mirror_triangle_01897_row = EJMTriangleCacheData.mirror ⟨1897, by decide⟩ := by
  have fields :
      mirror_triangle_01897_row.hash = (EJMTriangleCacheData.mirror ⟨1897, by decide⟩).hash ∧
      mirror_triangle_01897_row.lower = (EJMTriangleCacheData.mirror ⟨1897, by decide⟩).lower ∧
      mirror_triangle_01897_row.slots = (EJMTriangleCacheData.mirror ⟨1897, by decide⟩).slots ∧
      mirror_triangle_01897_row.edges = (EJMTriangleCacheData.mirror ⟨1897, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨1897, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 6726255 = hash ∧ (5236499333225160 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_01897
def mirror_triangle_02016_row : EJMLocalCacheData.MirrorRow :=
  ⟨4820005, (6887235943730415), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_02016 :
    mirror_triangle_02016_row = EJMTriangleCacheData.mirror ⟨2016, by decide⟩ := by
  have fields :
      mirror_triangle_02016_row.hash = (EJMTriangleCacheData.mirror ⟨2016, by decide⟩).hash ∧
      mirror_triangle_02016_row.lower = (EJMTriangleCacheData.mirror ⟨2016, by decide⟩).lower ∧
      mirror_triangle_02016_row.slots = (EJMTriangleCacheData.mirror ⟨2016, by decide⟩).slots ∧
      mirror_triangle_02016_row.edges = (EJMTriangleCacheData.mirror ⟨2016, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨2016, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 4820005 = hash ∧ (6887235943730415 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_02016
def mirror_triangle_02058_row : EJMLocalCacheData.MirrorRow :=
  ⟨5166880, (1192543756641510), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_02058 :
    mirror_triangle_02058_row = EJMTriangleCacheData.mirror ⟨2058, by decide⟩ := by
  have fields :
      mirror_triangle_02058_row.hash = (EJMTriangleCacheData.mirror ⟨2058, by decide⟩).hash ∧
      mirror_triangle_02058_row.lower = (EJMTriangleCacheData.mirror ⟨2058, by decide⟩).lower ∧
      mirror_triangle_02058_row.slots = (EJMTriangleCacheData.mirror ⟨2058, by decide⟩).slots ∧
      mirror_triangle_02058_row.edges = (EJMTriangleCacheData.mirror ⟨2058, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨2058, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 5166880 = hash ∧ (1192543756641510 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_02058
def mirror_triangle_03169_row : EJMLocalCacheData.MirrorRow :=
  ⟨1256305, (2813456401431585), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_03169 :
    mirror_triangle_03169_row = EJMTriangleCacheData.mirror ⟨3169, by decide⟩ := by
  have fields :
      mirror_triangle_03169_row.hash = (EJMTriangleCacheData.mirror ⟨3169, by decide⟩).hash ∧
      mirror_triangle_03169_row.lower = (EJMTriangleCacheData.mirror ⟨3169, by decide⟩).lower ∧
      mirror_triangle_03169_row.slots = (EJMTriangleCacheData.mirror ⟨3169, by decide⟩).slots ∧
      mirror_triangle_03169_row.edges = (EJMTriangleCacheData.mirror ⟨3169, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨3169, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 1256305 = hash ∧ (2813456401431585 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_03169
def mirror_triangle_03197_row : EJMLocalCacheData.MirrorRow :=
  ⟨1021930, (1282909046263845), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_03197 :
    mirror_triangle_03197_row = EJMTriangleCacheData.mirror ⟨3197, by decide⟩ := by
  have fields :
      mirror_triangle_03197_row.hash = (EJMTriangleCacheData.mirror ⟨3197, by decide⟩).hash ∧
      mirror_triangle_03197_row.lower = (EJMTriangleCacheData.mirror ⟨3197, by decide⟩).lower ∧
      mirror_triangle_03197_row.slots = (EJMTriangleCacheData.mirror ⟨3197, by decide⟩).slots ∧
      mirror_triangle_03197_row.edges = (EJMTriangleCacheData.mirror ⟨3197, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨3197, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 1021930 = hash ∧ (1282909046263845 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_03197
def mirror_triangle_03602_row : EJMLocalCacheData.MirrorRow :=
  ⟨1022555, (3612924594486480), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_03602 :
    mirror_triangle_03602_row = EJMTriangleCacheData.mirror ⟨3602, by decide⟩ := by
  have fields :
      mirror_triangle_03602_row.hash = (EJMTriangleCacheData.mirror ⟨3602, by decide⟩).hash ∧
      mirror_triangle_03602_row.lower = (EJMTriangleCacheData.mirror ⟨3602, by decide⟩).lower ∧
      mirror_triangle_03602_row.slots = (EJMTriangleCacheData.mirror ⟨3602, by decide⟩).slots ∧
      mirror_triangle_03602_row.edges = (EJMTriangleCacheData.mirror ⟨3602, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨3602, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 1022555 = hash ∧ (3612924594486480 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_03602
def mirror_triangle_03910_row : EJMLocalCacheData.MirrorRow :=
  ⟨7244430, (3573807452020260), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_03910 :
    mirror_triangle_03910_row = EJMTriangleCacheData.mirror ⟨3910, by decide⟩ := by
  have fields :
      mirror_triangle_03910_row.hash = (EJMTriangleCacheData.mirror ⟨3910, by decide⟩).hash ∧
      mirror_triangle_03910_row.lower = (EJMTriangleCacheData.mirror ⟨3910, by decide⟩).lower ∧
      mirror_triangle_03910_row.slots = (EJMTriangleCacheData.mirror ⟨3910, by decide⟩).slots ∧
      mirror_triangle_03910_row.edges = (EJMTriangleCacheData.mirror ⟨3910, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨3910, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 7244430 = hash ∧ (3573807452020260 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_03910
def mirror_triangle_03943_row : EJMLocalCacheData.MirrorRow :=
  ⟨1335680, (9235839040306515), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_03943 :
    mirror_triangle_03943_row = EJMTriangleCacheData.mirror ⟨3943, by decide⟩ := by
  have fields :
      mirror_triangle_03943_row.hash = (EJMTriangleCacheData.mirror ⟨3943, by decide⟩).hash ∧
      mirror_triangle_03943_row.lower = (EJMTriangleCacheData.mirror ⟨3943, by decide⟩).lower ∧
      mirror_triangle_03943_row.slots = (EJMTriangleCacheData.mirror ⟨3943, by decide⟩).slots ∧
      mirror_triangle_03943_row.edges = (EJMTriangleCacheData.mirror ⟨3943, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨3943, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 1335680 = hash ∧ (9235839040306515 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_03943
def mirror_triangle_04045_row : EJMLocalCacheData.MirrorRow :=
  ⟨1338805, (3024408706128810), 0x0, 0x0⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_04045 :
    mirror_triangle_04045_row = EJMTriangleCacheData.mirror ⟨4045, by decide⟩ := by
  have fields :
      mirror_triangle_04045_row.hash = (EJMTriangleCacheData.mirror ⟨4045, by decide⟩).hash ∧
      mirror_triangle_04045_row.lower = (EJMTriangleCacheData.mirror ⟨4045, by decide⟩).lower ∧
      mirror_triangle_04045_row.slots = (EJMTriangleCacheData.mirror ⟨4045, by decide⟩).slots ∧
      mirror_triangle_04045_row.edges = (EJMTriangleCacheData.mirror ⟨4045, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨4045, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 1338805 = hash ∧ (3024408706128810 : ℤ) = lower ∧
      0x0 = slots ∧ 0x0 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_04045
def mirror_triangle_04894_row : EJMLocalCacheData.MirrorRow :=
  ⟨5225625, (-4201684945245060), 0x1110000000, 0x7b068038c0001920000b1⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_04894 :
    mirror_triangle_04894_row = EJMTriangleCacheData.mirror ⟨4894, by decide⟩ := by
  have fields :
      mirror_triangle_04894_row.hash = (EJMTriangleCacheData.mirror ⟨4894, by decide⟩).hash ∧
      mirror_triangle_04894_row.lower = (EJMTriangleCacheData.mirror ⟨4894, by decide⟩).lower ∧
      mirror_triangle_04894_row.slots = (EJMTriangleCacheData.mirror ⟨4894, by decide⟩).slots ∧
      mirror_triangle_04894_row.edges = (EJMTriangleCacheData.mirror ⟨4894, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨4894, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 5225625 = hash ∧ (-4201684945245060 : ℤ) = lower ∧
      0x1110000000 = slots ∧ 0x7b068038c0001920000b1 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_04894
def mirror_triangle_05011_row : EJMLocalCacheData.MirrorRow :=
  ⟨5413250, (-5745918533447820), 0x1100000000, 0x99000049c00023ac100ca⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_05011 :
    mirror_triangle_05011_row = EJMTriangleCacheData.mirror ⟨5011, by decide⟩ := by
  have fields :
      mirror_triangle_05011_row.hash = (EJMTriangleCacheData.mirror ⟨5011, by decide⟩).hash ∧
      mirror_triangle_05011_row.lower = (EJMTriangleCacheData.mirror ⟨5011, by decide⟩).lower ∧
      mirror_triangle_05011_row.slots = (EJMTriangleCacheData.mirror ⟨5011, by decide⟩).slots ∧
      mirror_triangle_05011_row.edges = (EJMTriangleCacheData.mirror ⟨5011, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨5011, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 5413250 = hash ∧ (-5745918533447820 : ℤ) = lower ∧
      0x1100000000 = slots ∧ 0x99000049c00023ac100ca = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_05011
def mirror_triangle_05047_row : EJMLocalCacheData.MirrorRow :=
  ⟨3100750, (-3767395861956090), 0x1100000000, 0xa1c3004cc60025adc00f7⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_05047 :
    mirror_triangle_05047_row = EJMTriangleCacheData.mirror ⟨5047, by decide⟩ := by
  have fields :
      mirror_triangle_05047_row.hash = (EJMTriangleCacheData.mirror ⟨5047, by decide⟩).hash ∧
      mirror_triangle_05047_row.lower = (EJMTriangleCacheData.mirror ⟨5047, by decide⟩).lower ∧
      mirror_triangle_05047_row.slots = (EJMTriangleCacheData.mirror ⟨5047, by decide⟩).slots ∧
      mirror_triangle_05047_row.edges = (EJMTriangleCacheData.mirror ⟨5047, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨5047, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 3100750 = hash ∧ (-3767395861956090 : ℤ) = lower ∧
      0x1100000000 = slots ∧ 0xa1c3004cc60025adc00f7 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_05047
def mirror_triangle_05068_row : EJMLocalCacheData.MirrorRow :=
  ⟨5729500, (-5129574458509410), 0x1000000000, 0x85809780005255202510b00e5⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_05068 :
    mirror_triangle_05068_row = EJMTriangleCacheData.mirror ⟨5068, by decide⟩ := by
  have fields :
      mirror_triangle_05068_row.hash = (EJMTriangleCacheData.mirror ⟨5068, by decide⟩).hash ∧
      mirror_triangle_05068_row.lower = (EJMTriangleCacheData.mirror ⟨5068, by decide⟩).lower ∧
      mirror_triangle_05068_row.slots = (EJMTriangleCacheData.mirror ⟨5068, by decide⟩).slots ∧
      mirror_triangle_05068_row.edges = (EJMTriangleCacheData.mirror ⟨5068, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨5068, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 5729500 = hash ∧ (-5129574458509410 : ℤ) = lower ∧
      0x1000000000 = slots ∧ 0x85809780005255202510b00e5 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_05068
def mirror_triangle_06929_row : EJMLocalCacheData.MirrorRow :=
  ⟨3053130, (3290808264032835), 0x1100000000, 0x2c9800160c000ae6000563⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_06929 :
    mirror_triangle_06929_row = EJMTriangleCacheData.mirror ⟨6929, by decide⟩ := by
  have fields :
      mirror_triangle_06929_row.hash = (EJMTriangleCacheData.mirror ⟨6929, by decide⟩).hash ∧
      mirror_triangle_06929_row.lower = (EJMTriangleCacheData.mirror ⟨6929, by decide⟩).lower ∧
      mirror_triangle_06929_row.slots = (EJMTriangleCacheData.mirror ⟨6929, by decide⟩).slots ∧
      mirror_triangle_06929_row.edges = (EJMTriangleCacheData.mirror ⟨6929, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨6929, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 3053130 = hash ∧ (3290808264032835 : ℤ) = lower ∧
      0x1100000000 = slots ∧ 0x2c9800160c000ae6000563 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_06929
def mirror_triangle_07245_row : EJMLocalCacheData.MirrorRow :=
  ⟨3053755, (1147730450175855), 0x1100000000, 0x34580019ec000cd600065b⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_07245 :
    mirror_triangle_07245_row = EJMTriangleCacheData.mirror ⟨7245, by decide⟩ := by
  have fields :
      mirror_triangle_07245_row.hash = (EJMTriangleCacheData.mirror ⟨7245, by decide⟩).hash ∧
      mirror_triangle_07245_row.lower = (EJMTriangleCacheData.mirror ⟨7245, by decide⟩).lower ∧
      mirror_triangle_07245_row.slots = (EJMTriangleCacheData.mirror ⟨7245, by decide⟩).slots ∧
      mirror_triangle_07245_row.edges = (EJMTriangleCacheData.mirror ⟨7245, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨7245, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 3053755 = hash ∧ (1147730450175855 : ℤ) = lower ∧
      0x1100000000 = slots ∧ 0x34580019ec000cd600065b = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_07245
def mirror_triangle_07614_row : EJMLocalCacheData.MirrorRow :=
  ⟨3679380, (3307036714581600), 0x1000000000, 0x3b98001dbc300ece18075b⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_07614 :
    mirror_triangle_07614_row = EJMTriangleCacheData.mirror ⟨7614, by decide⟩ := by
  have fields :
      mirror_triangle_07614_row.hash = (EJMTriangleCacheData.mirror ⟨7614, by decide⟩).hash ∧
      mirror_triangle_07614_row.lower = (EJMTriangleCacheData.mirror ⟨7614, by decide⟩).lower ∧
      mirror_triangle_07614_row.slots = (EJMTriangleCacheData.mirror ⟨7614, by decide⟩).slots ∧
      mirror_triangle_07614_row.edges = (EJMTriangleCacheData.mirror ⟨7614, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨7614, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 3679380 = hash ∧ (3307036714581600 : ℤ) = lower ∧
      0x1000000000 = slots ∧ 0x3b98001dbc300ece18075b = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_07614
def mirror_triangle_07758_row : EJMLocalCacheData.MirrorRow :=
  ⟨3682505, (1398142651988355), 0x1000000000, 0x40880020343210121907fe⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_07758 :
    mirror_triangle_07758_row = EJMTriangleCacheData.mirror ⟨7758, by decide⟩ := by
  have fields :
      mirror_triangle_07758_row.hash = (EJMTriangleCacheData.mirror ⟨7758, by decide⟩).hash ∧
      mirror_triangle_07758_row.lower = (EJMTriangleCacheData.mirror ⟨7758, by decide⟩).lower ∧
      mirror_triangle_07758_row.slots = (EJMTriangleCacheData.mirror ⟨7758, by decide⟩).slots ∧
      mirror_triangle_07758_row.edges = (EJMTriangleCacheData.mirror ⟨7758, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨7758, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 3682505 = hash ∧ (1398142651988355 : ℤ) = lower ∧
      0x1000000000 = slots ∧ 0x40880020343210121907fe = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_07758
def mirror_triangle_09773_row : EJMLocalCacheData.MirrorRow :=
  ⟨1146930, (606370992812130), 0x1100000000, 0x6698c0330c601946300c7d⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_09773 :
    mirror_triangle_09773_row = EJMTriangleCacheData.mirror ⟨9773, by decide⟩ := by
  have fields :
      mirror_triangle_09773_row.hash = (EJMTriangleCacheData.mirror ⟨9773, by decide⟩).hash ∧
      mirror_triangle_09773_row.lower = (EJMTriangleCacheData.mirror ⟨9773, by decide⟩).lower ∧
      mirror_triangle_09773_row.slots = (EJMTriangleCacheData.mirror ⟨9773, by decide⟩).slots ∧
      mirror_triangle_09773_row.edges = (EJMTriangleCacheData.mirror ⟨9773, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨9773, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 1146930 = hash ∧ (606370992812130 : ℤ) = lower ∧
      0x1100000000 = slots ∧ 0x6698c0330c601946300c7d = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_09773
def mirror_triangle_10343_row : EJMLocalCacheData.MirrorRow :=
  ⟨1147555, (-87362076084465), 0x1100000000, 0x7518003a4c001d06000e77⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_10343 :
    mirror_triangle_10343_row = EJMTriangleCacheData.mirror ⟨10343, by decide⟩ := by
  have fields :
      mirror_triangle_10343_row.hash = (EJMTriangleCacheData.mirror ⟨10343, by decide⟩).hash ∧
      mirror_triangle_10343_row.lower = (EJMTriangleCacheData.mirror ⟨10343, by decide⟩).lower ∧
      mirror_triangle_10343_row.slots = (EJMTriangleCacheData.mirror ⟨10343, by decide⟩).slots ∧
      mirror_triangle_10343_row.edges = (EJMTriangleCacheData.mirror ⟨10343, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨10343, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 1147555 = hash ∧ (-87362076084465 : ℤ) = lower ∧
      0x1100000000 = slots ∧ 0x7518003a4c001d06000e77 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_10343
def mirror_triangle_10859_row : EJMLocalCacheData.MirrorRow :=
  ⟨1773180, (205669866724140), 0x1000000000, 0x7d88003eb4301f4a180f9d⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_10859 :
    mirror_triangle_10859_row = EJMTriangleCacheData.mirror ⟨10859, by decide⟩ := by
  have fields :
      mirror_triangle_10859_row.hash = (EJMTriangleCacheData.mirror ⟨10859, by decide⟩).hash ∧
      mirror_triangle_10859_row.lower = (EJMTriangleCacheData.mirror ⟨10859, by decide⟩).lower ∧
      mirror_triangle_10859_row.slots = (EJMTriangleCacheData.mirror ⟨10859, by decide⟩).slots ∧
      mirror_triangle_10859_row.edges = (EJMTriangleCacheData.mirror ⟨10859, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨10859, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 1773180 = hash ∧ (205669866724140 : ℤ) = lower ∧
      0x1000000000 = slots ∧ 0x7d88003eb4301f4a180f9d = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_10859
def mirror_triangle_11011_row : EJMLocalCacheData.MirrorRow :=
  ⟨1776305, (-135581274979605), 0x1000000000, 0x81680040a400204c001022⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_11011 :
    mirror_triangle_11011_row = EJMTriangleCacheData.mirror ⟨11011, by decide⟩ := by
  have fields :
      mirror_triangle_11011_row.hash = (EJMTriangleCacheData.mirror ⟨11011, by decide⟩).hash ∧
      mirror_triangle_11011_row.lower = (EJMTriangleCacheData.mirror ⟨11011, by decide⟩).lower ∧
      mirror_triangle_11011_row.slots = (EJMTriangleCacheData.mirror ⟨11011, by decide⟩).slots ∧
      mirror_triangle_11011_row.edges = (EJMTriangleCacheData.mirror ⟨11011, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨11011, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 1776305 = hash ∧ (-135581274979605 : ℤ) = lower ∧
      0x1000000000 = slots ∧ 0x81680040a400204c001022 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_11011
def mirror_triangle_13064_row : EJMLocalCacheData.MirrorRow :=
  ⟨2378770, (-5523568639213170), 0x1111111100, 0x183ea0081e10000c5e00008a⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_13064 :
    mirror_triangle_13064_row = EJMTriangleCacheData.mirror ⟨13064, by decide⟩ := by
  have fields :
      mirror_triangle_13064_row.hash = (EJMTriangleCacheData.mirror ⟨13064, by decide⟩).hash ∧
      mirror_triangle_13064_row.lower = (EJMTriangleCacheData.mirror ⟨13064, by decide⟩).lower ∧
      mirror_triangle_13064_row.slots = (EJMTriangleCacheData.mirror ⟨13064, by decide⟩).slots ∧
      mirror_triangle_13064_row.edges = (EJMTriangleCacheData.mirror ⟨13064, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨13064, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 2378770 = hash ∧ (-5523568639213170 : ℤ) = lower ∧
      0x1111111100 = slots ∧ 0x183ea0081e10000c5e00008a = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_13064
def mirror_triangle_13555_row : EJMLocalCacheData.MirrorRow :=
  ⟨862545, (1173284590010715), 0x1111111100, 0x1863880831a58c0d46000187⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_13555 :
    mirror_triangle_13555_row = EJMTriangleCacheData.mirror ⟨13555, by decide⟩ := by
  have fields :
      mirror_triangle_13555_row.hash = (EJMTriangleCacheData.mirror ⟨13555, by decide⟩).hash ∧
      mirror_triangle_13555_row.lower = (EJMTriangleCacheData.mirror ⟨13555, by decide⟩).lower ∧
      mirror_triangle_13555_row.slots = (EJMTriangleCacheData.mirror ⟨13555, by decide⟩).slots ∧
      mirror_triangle_13555_row.edges = (EJMTriangleCacheData.mirror ⟨13555, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨13555, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 862545 = hash ∧ (1173284590010715 : ℤ) = lower ∧
      0x1111111100 = slots ∧ 0x1863880831a58c0d46000187 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_13555
def mirror_triangle_14655_row : EJMLocalCacheData.MirrorRow :=
  ⟨4773295, (1835820815938200), 0x1111111100, 0x4c88c23e037e98c0db89002e3⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_14655 :
    mirror_triangle_14655_row = EJMTriangleCacheData.mirror ⟨14655, by decide⟩ := by
  have fields :
      mirror_triangle_14655_row.hash = (EJMTriangleCacheData.mirror ⟨14655, by decide⟩).hash ∧
      mirror_triangle_14655_row.lower = (EJMTriangleCacheData.mirror ⟨14655, by decide⟩).lower ∧
      mirror_triangle_14655_row.slots = (EJMTriangleCacheData.mirror ⟨14655, by decide⟩).slots ∧
      mirror_triangle_14655_row.edges = (EJMTriangleCacheData.mirror ⟨14655, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨14655, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 4773295 = hash ∧ (1835820815938200 : ℤ) = lower ∧
      0x1111111100 = slots ∧ 0x4c88c23e037e98c0db89002e3 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_14655
def mirror_triangle_14775_row : EJMLocalCacheData.MirrorRow :=
  ⟨4820170, (2239825678155975), 0x1111111100, 0x4c8808c403ef5bc10b8000489⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem mirror_triangle_14775 :
    mirror_triangle_14775_row = EJMTriangleCacheData.mirror ⟨14775, by decide⟩ := by
  have fields :
      mirror_triangle_14775_row.hash = (EJMTriangleCacheData.mirror ⟨14775, by decide⟩).hash ∧
      mirror_triangle_14775_row.lower = (EJMTriangleCacheData.mirror ⟨14775, by decide⟩).lower ∧
      mirror_triangle_14775_row.slots = (EJMTriangleCacheData.mirror ⟨14775, by decide⟩).slots ∧
      mirror_triangle_14775_row.edges = (EJMTriangleCacheData.mirror ⟨14775, by decide⟩).edges := by
    decide +kernel
  generalize mirrorEqual : EJMTriangleCacheData.mirror ⟨14775, by decide⟩ = actualRow at *
  cases actualRow with
  | mk hash lower slots edges =>
    change 4820170 = hash ∧ (2239825678155975 : ℤ) = lower ∧
      0x1111111100 = slots ∧ 0x4c8808c403ef5bc10b8000489 = edges at fields
    rcases fields with ⟨rfl, rfl, rfl, rfl⟩
    rfl

#print axioms mirror_triangle_14775

end D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalStateConcrete
