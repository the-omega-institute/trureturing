/- GID: D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/LowerBounds
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/LowerBounds
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Assembly.raw_cut_00337; premises=D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/LowerBounds.sum_lower_vecCons,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/LowerBounds.child0_lower_exact,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/LowerBounds.child1_lower_exact,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/LowerBounds.child2_lower_exact,D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/LowerBounds.child3_lower_exact
   digest: A generic vector-constructor summation identity yields the exact signed sum of all sixteen triangle and sixteen singleton lower fields for each child cache. -/

/- Source-only candidate. Not deployed, elaborated or kernel accepted.
   Existing full-cache transition obligations and original Accepted semantics
   are unchanged. Each arithmetic fact below reads the literal child cache;
   no row-state, hash, slots or edges equality is substituted by a lower value.
   No build or cache writes are authorized for this preparation. -/
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.Literals
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.LowerBounds

open EJMCacheState (Cache CachedLocal lower)
open EJMPartialBoundData (scale)
open Tail442V2.CanonicalStateConcrete
open scoped BigOperators

/-- Expand one vector constructor without computing a Finset enumeration.
The readout retains its original row parameter; it does not inspect a state,
recompute a transition or reopen the large canonical mirror lookup. -/
theorem sum_lower_vecCons {N n : ℕ} (head : CachedLocal N)
    (tail : Fin n → CachedLocal N) :
    (∑ k : Fin (n + 1), ((Matrix.vecCons head tail) k).row.lower) =
      head.row.lower + ∑ k : Fin n, (tail k).row.lower := by
  rw [Fin.sum_univ_succ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
/-- Exact total from all 16 triangle and 16 singleton literal lower fields. -/
theorem child0_lower_exact : lower childCache0 = (18606457232991810 : ℤ) := by
  calc
    lower childCache0 =
      (-4201684945245060 + (-4210815426559560 + (1865553770312505 + (2816047426178805 + (3290808264032835 + (5172784952197590 + (-6559354420406970 + (4518758583607905 + (205669866724140 + (9235839040306515 + (2735694921288420 + (5878616855633340 + (437651695546065 + (1104415892618220 + (2813456401431585 + (1173284590010715 + (0 : ℤ))))))))))))))))) +
      (-2123687996166555 + (-163178568758205 + (-163178568758205 + (-76651588980330 + (-2640919924324500 + (1373508743368125 + (-651058434611130 + (-2582553837844890 + (-679745453815155 + (231226270487940 + (-1138150299469365 + (231226270487940 + (-285053766387390 + (-631159819853745 + (2306107857696825 + (-677001117756600 + (0 : ℤ))))))))))))))))) := by
        simp only [lower, childCache0, sum_lower_vecCons, Fin.sum_univ_zero]
    _ = (18606457232991810 : ℤ) := by decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
/-- Exact total from all 16 triangle and 16 singleton literal lower fields. -/
theorem child1_lower_exact : lower childCache1 = (1714852503522795 : ℤ) := by
  calc
    lower childCache1 =
      (-3767395861956090 + (-2662784195384040 + (1865553770312505 + (2816047426178805 + (1147730450175855 + (1192543756641510 + (-6559354420406970 + (4518758583607905 + (606370992812130 + (1282909046263845 + (2735694921288420 + (5878616855633340 + (437651695546065 + (1104415892618220 + (6887235943730415 + (-5523568639213170 + (0 : ℤ))))))))))))))))) +
      (-2123687996166555 + (1105558261378935 + (1105558261378935 + (-76651588980330 + (-2640919924324500 + (87789602294940 + (-651058434611130 + (-1192642712695980 + (-679745453815155 + (-898675145353440 + (-1138150299469365 + (-898675145353440 + (-285053766387390 + (-631159819853745 + (-651058434611130 + (-677001117756600 + (0 : ℤ))))))))))))))))) := by
        simp only [lower, childCache1, sum_lower_vecCons, Fin.sum_univ_zero]
    _ = (1714852503522795 : ℤ) := by decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
/-- Exact total from all 16 triangle and 16 singleton literal lower fields. -/
theorem child2_lower_exact : lower childCache2 = (10062141904509240 : ℤ) := by
  calc
    lower childCache2 =
      (-5129574458509410 + (-22283621971065 + (1865553770312505 + (2816047426178805 + (1398142651988355 + (1071971890325700 + (-6559354420406970 + (4518758583607905 + (-135581274979605 + (3024408706128810 + (2735694921288420 + (5878616855633340 + (437651695546065 + (1104415892618220 + (6920275813517430 + (2239825678155975 + (0 : ℤ))))))))))))))))) +
      (-2123687996166555 + (-1186920101255070 + (-1186920101255070 + (-76651588980330 + (-2640919924324500 + (-478597344940260 + (-651058434611130 + (3774710211090 + (-679745453815155 + (150360734144985 + (-1138150299469365 + (150360734144985 + (-285053766387390 + (-631159819853745 + (-651058434611130 + (-677001117756600 + (0 : ℤ))))))))))))))))) := by
        simp only [lower, childCache2, sum_lower_vecCons, Fin.sum_univ_zero]
    _ = (10062141904509240 : ℤ) := by decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
/-- Exact total from all 16 triangle and 16 singleton literal lower fields. -/
theorem child3_lower_exact : lower childCache3 = (10896463891502280 : ℤ) := by
  calc
    lower childCache3 =
      (-5745918533447820 + (-3893165080248990 + (1865553770312505 + (2816047426178805 + (3307036714581600 + (5236499333225160 + (-6559354420406970 + (4518758583607905 + (-87362076084465 + (3612924594486480 + (2735694921288420 + (5878616855633340 + (437651695546065 + (1104415892618220 + (3573807452020260 + (1835820815938200 + (0 : ℤ))))))))))))))))) +
      (-2123687996166555 + (-358764225189825 + (-358764225189825 + (-76651588980330 + (-2640919924324500 + (-664188621543720 + (-651058434611130 + (-357354293568090 + (-679745453815155 + (952963357779615 + (-1138150299469365 + (952963357779615 + (-285053766387390 + (-631159819853745 + (-1003991002449435 + (-677001117756600 + (0 : ℤ))))))))))))))))) := by
        simp only [lower, childCache3, sum_lower_vecCons, Fin.sum_univ_zero]
    _ = (10896463891502280 : ℤ) := by decide +kernel

#print axioms sum_lower_vecCons
#print axioms child0_lower_exact
#print axioms child1_lower_exact
#print axioms child2_lower_exact
#print axioms child3_lower_exact

end D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState.LowerBounds
