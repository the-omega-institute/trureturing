/- GID: D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/LowerBounds
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/LowerBounds
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Assembly.raw_cut_00337; premises=D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/LowerBounds.child0_lower_exact,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/LowerBounds.child1_lower_exact,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/LowerBounds.child2_lower_exact,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/LowerBounds.child3_lower_exact
   digest: The signed lower fields at all sixteen triangle and sixteen singleton placements yield four exact literal child-cache totals for prefix 5335036. -/

/- Source-only complete original Tail442 context. Kernel acceptance pending. -/
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335036.Literals
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.LowerBounds

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

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
/-- Exact total of this context's 32 actual literal lower fields. -/
theorem child0_lower_exact : lower childCache0 = (18625063898967435 : ℤ) := by
  calc
    lower childCache0 =
      (-4201684945245060 + (-6835820754953190 + (1865553770312505 + (1262634598340115 + (3290808264032835 + (4277590094494080 + (-6559354420406970 + (2678425505744625 + (205669866724140 + (10197944485530165 + (2735694921288420 + (5257607032772640 + (1438485558252015 + (1104415892618220 + (3540906576290265 + (1173284590010715 + (0 : ℤ))))))))))))))))) +
      (-796264733604795 + (-163178568758205 + (-163178568758205 + (-77470194940320 + (-254342200779030 + (1373508743368125 + (-1413962239765530 + (-2582553837844890 + (196326233704965 + (231226270487940 + (-1917671049571095 + (231226270487940 + (-285053766387390 + (1185183765582180 + (2306107857696825 + (-677001117756600 + (0 : ℤ))))))))))))))))) := by
        simp only [lower, childCache0, D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.LowerBounds.sum_lower_vecCons, Fin.sum_univ_zero]
    _ = (18625063898967435 : ℤ) := by decide +kernel

#print axioms child0_lower_exact

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
/-- Exact total of this context's 32 actual literal lower fields. -/
theorem child1_lower_exact : lower childCache1 = (3835537824183975 : ℤ) := by
  calc
    lower childCache1 =
      (-3767395861956090 + (-4029008020694475 + (1865553770312505 + (1262634598340115 + (1147730450175855 + (2135021175528150 + (-6559354420406970 + (2678425505744625 + (606370992812130 + (2866678673661075 + (2735694921288420 + (5257607032772640 + (1438485558252015 + (1104415892618220 + (5998646811427725 + (-5523568639213170 + (0 : ℤ))))))))))))))))) +
      (-796264733604795 + (1105558261378935 + (1105558261378935 + (-77470194940320 + (-254342200779030 + (87789602294940 + (-1413962239765530 + (-1192642712695980 + (196326233704965 + (-898675145353440 + (-1917671049571095 + (-898675145353440 + (-285053766387390 + (1185183765582180 + (-651058434611130 + (-677001117756600 + (0 : ℤ))))))))))))))))) := by
        simp only [lower, childCache1, D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.LowerBounds.sum_lower_vecCons, Fin.sum_univ_zero]
    _ = (3835537824183975 : ℤ) := by decide +kernel

#print axioms child1_lower_exact

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
/-- Exact total of this context's 32 actual literal lower fields. -/
theorem child2_lower_exact : lower childCache2 = (11389369148556945 : ℤ) := by
  calc
    lower childCache2 =
      (-5129574458509410 + (-4210815426559560 + (1865553770312505 + (1262634598340115 + (1398142651988355 + (6198059968141860 + (-6559354420406970 + (2678425505744625 + (-135581274979605 + (4808755408250430 + (2735694921288420 + (5257607032772640 + (1438485558252015 + (1104415892618220 + (3676348850225415 + (2239825678155975 + (0 : ℤ))))))))))))))))) +
      (-796264733604795 + (-1186920101255070 + (-1186920101255070 + (-77470194940320 + (-254342200779030 + (-478597344940260 + (-1413962239765530 + (3774710211090 + (196326233704965 + (150360734144985 + (-1917671049571095 + (150360734144985 + (-285053766387390 + (1185183765582180 + (-651058434611130 + (-677001117756600 + (0 : ℤ))))))))))))))))) := by
        simp only [lower, childCache2, D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.LowerBounds.sum_lower_vecCons, Fin.sum_univ_zero]
    _ = (11389369148556945 : ℤ) := by decide +kernel

#print axioms child2_lower_exact

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
/-- Exact total of this context's 32 actual literal lower fields. -/
theorem child3_lower_exact : lower childCache3 = (9498669563148675 : ℤ) := by
  calc
    lower childCache3 =
      (-5745918533447820 + (-5361019680273075 + (1865553770312505 + (1262634598340115 + (3307036714581600 + (2871463766973165 + (-6559354420406970 + (2678425505744625 + (-87362076084465 + (4122035173680060 + (2735694921288420 + (5257607032772640 + (1438485558252015 + (1104415892618220 + (3650541478758720 + (1835820815938200 + (0 : ℤ))))))))))))))))) +
      (-796264733604795 + (-358764225189825 + (-358764225189825 + (-77470194940320 + (-254342200779030 + (-664188621543720 + (-1413962239765530 + (-357354293568090 + (196326233704965 + (952963357779615 + (-1917671049571095 + (952963357779615 + (-285053766387390 + (1185183765582180 + (-1003991002449435 + (-677001117756600 + (0 : ℤ))))))))))))))))) := by
        simp only [lower, childCache3, D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.LowerBounds.sum_lower_vecCons, Fin.sum_univ_zero]
    _ = (9498669563148675 : ℤ) := by decide +kernel

#print axioms child3_lower_exact


end D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335036
