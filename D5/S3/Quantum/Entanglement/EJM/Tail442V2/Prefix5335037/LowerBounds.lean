/- GID: D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/LowerBounds
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/LowerBounds
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Assembly.raw_cut_00337; premises=D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/LowerBounds.child0_lower_exact,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/LowerBounds.child1_lower_exact,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/LowerBounds.child2_lower_exact,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/LowerBounds.child3_lower_exact
   digest: The signed lower fields at all sixteen triangle and sixteen singleton placements yield four exact literal child-cache totals for prefix 5335037. -/

/- Source-only complete original Tail442 context. Kernel acceptance pending. -/
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.Literals
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.LowerBounds

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

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
/-- Exact total of this context's 32 actual literal lower fields. -/
theorem child0_lower_exact : lower childCache0 = (20686156202449920 : ℤ) := by
  calc
    lower childCache0 =
      (-4201684945245060 + (-4029008020694475 + (1865553770312505 + (6460109652110205 + (3290808264032835 + (1547377933952760 + (-6559354420406970 + (2095296664249425 + (205669866724140 + (6406381636322850 + (2735694921288420 + (7149964582782840 + (2920236133147515 + (1104415892618220 + (4134508150426290 + (1173284590010715 + (0 : ℤ))))))))))))))))) +
      (-1332405757900035 + (-163178568758205 + (-163178568758205 + (1122701304282285 + (-2088316202709555 + (1373508743368125 + (-2088316202709555 + (-2582553837844890 + (-56977704107415 + (231226270487940 + (-1563864346626855 + (231226270487940 + (-285053766387390 + (122977158053295 + (2306107857696825 + (-677001117756600 + (0 : ℤ))))))))))))))))) := by
        simp only [lower, childCache0, D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.LowerBounds.sum_lower_vecCons, Fin.sum_univ_zero]
    _ = (20686156202449920 : ℤ) := by decide +kernel

#print axioms child0_lower_exact

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
/-- Exact total of this context's 32 actual literal lower fields. -/
theorem child1_lower_exact : lower childCache1 = (1002147724083870 : ℤ) := by
  calc
    lower childCache1 =
      (-3767395861956090 + (-4739636064577050 + (1865553770312505 + (6460109652110205 + (1147730450175855 + (3568591555390680 + (-6559354420406970 + (2095296664249425 + (606370992812130 + (4452400422698865 + (2735694921288420 + (7149964582782840 + (2920236133147515 + (1104415892618220 + (-4325860378526505 + (-5523568639213170 + (0 : ℤ))))))))))))))))) +
      (-1332405757900035 + (1105558261378935 + (1105558261378935 + (1122701304282285 + (-2088316202709555 + (87789602294940 + (-2088316202709555 + (-1192642712695980 + (-56977704107415 + (-898675145353440 + (-1563864346626855 + (-898675145353440 + (-285053766387390 + (122977158053295 + (-651058434611130 + (-677001117756600 + (0 : ℤ))))))))))))))))) := by
        simp only [lower, childCache1, D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.LowerBounds.sum_lower_vecCons, Fin.sum_univ_zero]
    _ = (1002147724083870 : ℤ) := by decide +kernel

#print axioms child1_lower_exact

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
/-- Exact total of this context's 32 actual literal lower fields. -/
theorem child2_lower_exact : lower childCache2 = (16997489943731115 : ℤ) := by
  calc
    lower childCache2 =
      (-5129574458509410 + (-2662784195384040 + (1865553770312505 + (6460109652110205 + (1398142651988355 + (1182776615186985 + (-6559354420406970 + (2095296664249425 + (-135581274979605 + (3874565080286355 + (2735694921288420 + (7149964582782840 + (2920236133147515 + (1104415892618220 + (8503459090306635 + (2239825678155975 + (0 : ℤ))))))))))))))))) +
      (-1332405757900035 + (-1186920101255070 + (-1186920101255070 + (1122701304282285 + (-2088316202709555 + (-478597344940260 + (-2088316202709555 + (3774710211090 + (-56977704107415 + (150360734144985 + (-1563864346626855 + (150360734144985 + (-285053766387390 + (122977158053295 + (-651058434611130 + (-677001117756600 + (0 : ℤ))))))))))))))))) := by
        simp only [lower, childCache2, D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.LowerBounds.sum_lower_vecCons, Fin.sum_univ_zero]
    _ = (16997489943731115 : ℤ) := by decide +kernel

#print axioms child2_lower_exact

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
/-- Exact total of this context's 32 actual literal lower fields. -/
theorem child3_lower_exact : lower childCache3 = (14735460027853110 : ℤ) := by
  calc
    lower childCache3 =
      (-5745918533447820 + (-5282270092971690 + (1865553770312505 + (6460109652110205 + (3307036714581600 + (4274493570749220 + (-6559354420406970 + (2095296664249425 + (-87362076084465 + (1576456270479090 + (2735694921288420 + (7149964582782840 + (2920236133147515 + (1104415892618220 + (4768678450750305 + (1835820815938200 + (0 : ℤ))))))))))))))))) +
      (-1332405757900035 + (-358764225189825 + (-358764225189825 + (1122701304282285 + (-2088316202709555 + (-664188621543720 + (-2088316202709555 + (-357354293568090 + (-56977704107415 + (952963357779615 + (-1563864346626855 + (952963357779615 + (-285053766387390 + (122977158053295 + (-1003991002449435 + (-677001117756600 + (0 : ℤ))))))))))))))))) := by
        simp only [lower, childCache3, D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.LowerBounds.sum_lower_vecCons, Fin.sum_univ_zero]
    _ = (14735460027853110 : ℤ) := by decide +kernel

#print axioms child3_lower_exact


end D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037
