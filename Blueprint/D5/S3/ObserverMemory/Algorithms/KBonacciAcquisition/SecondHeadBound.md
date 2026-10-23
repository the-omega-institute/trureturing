# Weighted second-head certificate

## Abstract

A uniform weighted common-table certificate gives the original second-head necessary inequality.

**Theorem 1.1 (Uniform second-head necessary bound).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/SecondHeadBound.second_head_bound`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/SecondHeadBound.second_head_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m at least four, real amplitude sequence a with 0 at most a(i) at most one at every i, real cap epsilon at least zero, and one PMF w on OriginalScheduledWitnessTables.Catalog false m, assume that for every low word b the total variation between the evaluation pushforward of w and PreselectedResidualBound.finiteTarget m a b is at most ofReal(epsilon). Then (m-2)(m+1) epsilon is at least (m-3)a(1)+(m-2) times the sum of a(t) for 2 at most t at most m-1, minus (m-3). Natural subtractions in the Lean statement agree with integer subtraction because m is at least four. The finite result requires neither a strict cutoff nor antitonicity. It uses a single law on whole deterministic tables before quantification over all words, including the finite all-positive word.

The rows are exactly Continuation Definition 117.1. In original one-based coordinates, h_k has its only one at k for 2 at most k at most m-1 and event {0,1}, weight one. The word g=10...0 has event {0,2}, weight one; g_k has ones at 1,k for 3 at most k at most m-1, event {2}, weight one. For 3 at most n at most m-2, w_n=1^(n-1)0^(m-n+1) has event {n}, weight m-3, and v_n=1^(n-1)0 1^(m-n-1)0 has event {n}, weight one. The last two chain rows w_(m-1),w_m have weight m-2, as does the all-positive row with event {0}. Empty ranges have no rows. Rows are retained with their multiplicities, even if words or events coincide.

At fixed seed, Catalog supplies a preselected schedule of at most two actual requests. Its distinct address set extends to two distinct low coordinates i<j; view_congr transfers equal replies at those coordinates to equal chronological views and equal output. This also covers empty schedules, singletons, repetitions and reverse order. For each of the four reply cells, sum the weights of rows in the cell whose event contains the chosen label. In original coordinates j<m the upper bounds for cells 00,01,10,11 are m-3,1,m-2,m-2; when j=m they are m-2,0,m-2,m-2. The proof counts the sparse h rows by removing queried coordinates, counts g_k with their shared first coordinate, and combines each later label's chain and punctured rows. Their weights sum to m-2. In a nonlast 00 cell the punctured row is absent and the chain weight is at most m-3; in 01 a chain row is absent and the punctured contribution is at most one. Thus the seed-fixed weighted score is at most 3(m-2), uniformly in symbolic m.

The total row weight is M_m=(m-2)(m+1). The selected target score is T_m=2m-3+(m-3)a(1)+(m-2) times the sum over 2 at most t at most m-1 of a(t). The first-zero computation is checked for each row family. Averaging the deterministic score under the same PMF gives S_m at most 3(m-2). Every complete event has target mass at most epsilon plus its actual mass, by the all-word TV cap. In particular {0,1} and {0,2} are independent union-event constraints; the proof does not derive either from singleton constraints. Summing with the actual nonnegative weights gives T_m-M_m epsilon at most S_m and hence the displayed inequality.

For the original Theorem 117.2 application, the source is x=(r,g), where r is prime and ceil(F_r/10) at most g at most floor(F_r/5), with static N(x)=1+F_r g. Natural address i is original prime index i+1. The tape carrier is the full disjoint union of the B_j and P_j interval blocks; theta_j is the B_1 point 1/(j+2). Zero-based a(k) is original a_(k+1), while output labels themselves are not shifted. The selected target at first absence n is (1-a_n) delta(theta_0)+a_n delta(theta_n). Retain every original positive nonincreasing profile bounded by one and converging to zero, zero advice, one source-independent common seed, arbitrary original addresses, sourcewise almost-sure finite handoff, and the hard budget of two actual requests counting repetitions. No law on the source set is used, and the original consumer still runs on the same source and handed tape.

The existing original full-carrier necessity transport accepts arbitrary finite length and a nonnegative closed cap directly. Apply it at L=m and at the supremum of the original sourcewise TV errors. It supplies precisely one PMF on whole Catalog false m tables with the all-word cap in this theorem. The measurable projection fixes the low marks and sends every other original output to the base mark; finite-pattern actual witnesses supply the all-positive bookkeeping word without introducing an infinite all-positive source. This application needs no bound on competitor addresses or output support, no condition on a_(m+1), no resizing by an active cutoff, and no positive-cap limit. The original e=0 and e=1 endpoints and all profile plateaus remain included. The resulting original inequality is (m-2)(m+1)e_a(A) at least (m-3)a_2+(m-2) times the sum of a_n for 3 at most n at most m, minus (m-3).

For stopped acquisitions, the existing completeTable inclusion maps Catalog true m to Catalog false m without changing any word output, hence the same common-law cap and inequality hold. The full-source exact applications are transient applications of the existing transport and this theorem, rather than a second generic transport API. The weighted query-cell compatibility relation is the mathematical content here; existing source transport, PMF arithmetic and TV contraction are reused. The result is necessary and asserts no sufficiency or uniform stopped synthesis. It makes no literature novelty claim.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/SecondHeadBound.second_head_bound`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound](PreselectedResidualBound.md)
