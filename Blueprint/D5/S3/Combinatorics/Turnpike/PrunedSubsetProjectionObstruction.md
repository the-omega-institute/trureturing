# All subset cuts do not complete the pruned spine projection

## Abstract

An assignment for a realizable seven-point input satisfies every subset cut and has no full triangle lift.

The ordered numerical relation and triangle marginals follow Elder, Marçais and Kingsford, WABI 2026, Sections 3.1–3.3, Proposition 10 and System 11. DOI: 10.4230/LIPIcs.WABI.2026.20, CC BY 4.0. The exact rank-pruned all-subset comparison and seven-point countercertificate are repository-derived internal mathematics. No external named conjecture, priority, minimum-size or algorithmic-performance claim is made.

Publication indices are one-based; Lean subtracts one. I contains every interval i<j, Delta every triangle i<j<k, and S every endpoint-spine triangle (1,j,k). Admissible inputs have n≥3, d≥1, strictly decreasing positive real y, and positive integer multiplicities mu whose sum is choose(n,2). Realizes(y,mu,x) requires a strictly increasing real ruler and its entire distance multiset with exactly those multiplicities. This is an input premise; no fractional P is assumed to be the distance assignment of a ruler.

R is the complete ordered relation y_a+y_b=y_c with guard a≠b or mu_a≥2. Both orders of unequal summands occur. Let M_0=0 and M_q=sum_{r≤q}mu_r. The closed rank block [M_{q−1}+1,M_q] is allowed on ij exactly when M_q≥i(n−j+1) and M_{q−1}+1≤choose(n,2)−choose(j−i+1,2)+1. A_ij,q is its indicator. This is intersection of closed integer intervals.

D_A retains every real coordinate P_ij,q, with 0≤P_ij,q≤A_ij,q, every row sum one, and every label column sum mu_q. For H=Delta or S, the projection F^A_H uses its own existential T on H×R. Every triangle block is nonnegative, sums to one, has all three full label marginals P_ij,P_jk,P_ik, and satisfies T_tau,(a,b,c)≤A_ij,a A_jk,b A_ik,c. The entire same P is compared, and the full T is independent of the spine T.

For each triangle and position pair u<v in {1,2,3}, let w be the other position. For every two label subsets U,V, C(U,V) contains precisely the labels r_w of complete guarded relation triples r with all three masks allowed, r_u∈U and r_v∈V. SubsetCuts requires p^u(U)+p^v(V)≤1+p^w(C(U,V)) for every triangle, pair, U and V. Empty U, V and C and every zero-mass label are included.

**Definition 1.1 (The universal comparison).**

$$\left(\operatorname{claim}: \operatorname{Prop}\right) = \left(\forall \left(n: \operatorname{Nat}\right), \left(\forall \left(d: \operatorname{Nat}\right), \left(\forall \left(y: \operatorname{Fin}\left(d\right) \to \operatorname{Real}\right), \left(\forall \left(\mu: \operatorname{Fin}\left(d\right) \to \operatorname{Nat}\right), \left(\left(\operatorname{Admissible}\left(n, d, y, \mu\right)\right) \Rightarrow \left(\left(\exists \left(x: \operatorname{Fin}\left(n\right) \to \operatorname{Real}\right), \operatorname{Realizes}\left(y, \mu, x\right)\right) \Rightarrow \left(\forall \left(P: \operatorname{I}\left(n\right) \to \left(\operatorname{Fin}\left(d\right) \to \operatorname{Real}\right)\right), \left(\left(\left(\operatorname{Member}\left(P, \operatorname{PrunedProjection}\left(y, \mu, \operatorname{Delta}\right)\right)\right) \Rightarrow \left(\left(\operatorname{Member}\left(P, \operatorname{PrunedProjection}\left(y, \mu, \operatorname{S}\right)\right)\right) \land \left(\operatorname{SubsetCuts}\left(y, \mu, P\right)\right)\right)\right) \land \left(\left(\left(\operatorname{Member}\left(P, \operatorname{PrunedProjection}\left(y, \mu, \operatorname{S}\right)\right)\right) \land \left(\operatorname{SubsetCuts}\left(y, \mu, P\right)\right)\right) \Rightarrow \left(\operatorname{Member}\left(P, \operatorname{PrunedProjection}\left(y, \mu, \operatorname{Delta}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Turnpike/PrunedSubsetProjectionObstruction.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* C. S. Elder, Guillaume Marçais, Carl Kingsford (2026). *Turnpike with Uncertain Measurements: Triangle-Equality Integer Programming with a Deterministic Recovery Guarantee*. DOI: [10.4230/LIPIcs.WABI.2026.20](https://doi.org/10.4230/LIPIcs.WABI.2026.20). URL: <https://drops.dagstuhl.de/storage/00lipics/lipics-vol390-wabi2026/html/LIPIcs.WABI.2026.20/LIPIcs.WABI.2026.20.html>.

*Commentary.*

The claim is the universal equality F^A_Delta={P∈F^A_S:SubsetCuts(P)} for every originally admissible realizable input. It does not replace the event by a finite restriction, arbitrary relation, global joint distribution, integral assignment, scalar feasibility comparison or extra presolve.

The actual instance is n=7, d=12, ruler x=(0,4,6,9,10,11,12), labels y=(12,11,10,9,8,7,6,5,4,3,2,1), and multiplicities mu=(1,1,1,1,1,1,3,2,2,2,3,3). Lean checks strict increase, every interval difference, and every multiplicity. All assignment and spine masses below have denominator 50. Labels and vertices in the tables are zero-based; omitted coordinates are exactly zero.

Complete assignment P: for each interval ij the entries q:z mean P_ij,q=z/50. SubsetCertificateData.numerator gives every entry, including every omitted zero. The row totals, common column counts, coordinate bounds and closed rank masks are checked as integer identities before transfer to real numbers.

0,1: 6:8; 7:2; 8:4; 9:6; 10:10; 11:20.

0,2: 4:4; 5:4; 6:11; 7:11; 9:6; 10:14.

0,3: 3:19; 6:14; 8:14; 9:3.

0,4: 2:20; 4:13; 6:14; 7:3.

0,5: 1:30; 2:6; 4:9; 5:2; 6:3.

0,6: 0:50.

1,2: 8:9; 9:7; 10:4; 11:30.

1,3: 6:6; 7:16; 8:2; 9:12; 10:14.

1,4: 5:9; 6:14; 7:16; 8:11.

1,5: 3:16; 4:6; 5:13; 6:4; 7:11.

1,6: 1:20; 2:10; 3:6; 4:4; 5:2; 6:8.

2,3: 8:2; 9:12; 10:13; 11:23.

2,4: 6:3; 7:8; 8:12; 9:16; 10:11.

2,5: 5:6; 6:20; 7:13; 8:7; 9:4.

2,6: 2:14; 3:6; 5:11; 6:11; 7:4; 8:4.

3,4: 8:1; 9:3; 10:24; 11:22.

3,5: 6:3; 7:11; 8:12; 9:5; 10:19.

3,6: 3:3; 4:14; 6:14; 9:19.

4,5: 7:3; 9:7; 10:15; 11:25.

4,6: 5:3; 6:14; 8:13; 10:20.

5,6: 6:3; 7:2; 8:9; 10:6; 11:30.

Complete spine weights: each triangle followed by (a,b,c):z means mass z/50 at that ordered relation triple. The Lean raw table pads blocks to ten entries with zero weights. weightedAtoms_sum and weightedAtoms_marginal prove normalization and full marginals after summing coincident atoms; raw_masks proves every positive weight satisfies the propagated product mask.

0,1,2: (6,10,4):4; (6,11,5):4; (7,11,6):2; (8,11,7):4; (9,9,6):6; (10,8,6):3; (10,9,7):1; (10,11,9):6; (11,8,7):6; (11,11,10):14.

0,1,3: (6,9,3):8; (7,8,3):2; (8,7,3):3; (8,10,6):1; (9,6,3):6; (10,10,8):10; (11,7,6):13; (11,9,8):4; (11,10,9):3.

0,1,4: (6,8,2):8; (7,7,2):2; (8,6,2):4; (9,5,2):6; (10,6,4):10; (11,5,4):3; (11,7,6):14; (11,8,7):3.

0,1,5: (6,7,1):8; (7,6,1):2; (8,5,1):4; (9,4,1):6; (10,3,1):10; (11,3,2):6; (11,5,4):9; (11,6,5):2; (11,7,6):3.

0,1,6: (6,6,0):8; (7,5,0):2; (8,4,0):4; (9,3,0):6; (10,2,0):10; (11,1,0):20.

0,2,3: (4,11,3):4; (5,10,3):4; (6,9,3):11; (7,11,6):11; (9,9,6):1; (9,11,8):5; (10,8,6):2; (10,10,8):9; (10,11,9):3.

0,2,4: (4,10,2):4; (5,9,2):4; (6,8,2):4; (6,10,4):7; (7,7,2):8; (7,9,4):3; (9,9,6):6; (10,6,4):3; (10,8,6):8; (10,9,7):3.

0,2,5: (4,9,1):4; (5,8,1):4; (6,7,1):11; (7,6,1):11; (9,5,2):6; (10,6,4):9; (10,7,5):2; (10,8,6):3.

0,2,6: (4,8,0):4; (5,7,0):4; (6,6,0):11; (7,5,0):11; (9,3,0):6; (10,2,0):14.

0,3,4: (3,11,2):19; (6,8,2):1; (6,10,4):13; (8,10,6):11; (8,11,7):3; (9,9,6):3.

0,3,5: (3,10,1):19; (6,7,1):11; (6,8,2):3; (8,6,2):3; (8,8,4):9; (8,9,5):2; (9,9,6):3.

0,3,6: (3,9,0):19; (6,6,0):14; (8,4,0):14; (9,3,0):3.

0,4,5: (2,11,1):20; (4,9,1):7; (4,10,2):6; (6,7,1):3; (6,10,4):9; (6,11,5):2; (7,11,6):3.

0,4,6: (2,10,0):20; (4,8,0):13; (6,6,0):14; (7,5,0):3.

0,5,6: (1,11,0):30; (2,10,0):6; (4,8,0):9; (5,7,0):2; (6,6,0):3.

The complete numerical relation table is proved equal to the guarded arithmetic relation with the three rank masks, in twelve first-label shards for each of the 35 triangles. Its triples are not assumed valid. Positive support is exactly the labels with nonzero numerator, and every omitted P coordinate is proved zero. Intersecting arbitrary U,V with the corresponding supports preserves their P masses; the resulting completion is a subset of the original complete completion, whose extra mass is nonnegative.

To certify all subsets without enumerating every U,V pair, fix a triangle, a position pair, and U in the positive support of p^u. The certificate provides a separate sparse nonnegative integer flow on allowed triples with r_u∈U. Its total is at least the numerator mass of p^u(U), its r_v marginal is bounded coordinatewise by the numerator of p^v, and its r_w marginal is bounded by that of p^w. Lean checks all 3,200 such U cases and all 14,574 listed nonzero flow atoms with decide and kernel reduction. These separate flows need not coexist as a triangle coupling.

For arbitrary V, every flow atom has r_v outside V or has r_w in C(U,V). Split its mass accordingly. The outside mass is at most p^v(V-complement), and the inside mass is at most p^w(C(U,V)); double counting only enlarges the bound. Thus p^u(U)≤p^v(V-complement)+p^w(C), and p^v has total one, giving the original subset cut. Omega.Turnpike.partialFlow_cut proves this finite-sum argument over arbitrary dimensions and nonnegative integer weights. The division by 50 and support extension then prove every original real inequality.

For the full-lift obstruction set f(k)=1,4,−2 for residues k=0,1,2 modulo 3, and g(k)=−2,4,1 for those residues. Lean checks f(y_a)+f(y_b)+g(y_c)≥0 on all complete numerical triples y_a+y_b=y_c, without removing zero-marginal labels or requiring a mask. Any nonnegative full triangle block therefore has nonnegative expected potential. The finite weighted marginal identity rewrites that expectation into the three prescribed marginal expectations.

**Theorem 1.2 (Refutation at the same entire P).**

$$\neg \left(\forall \left(n: \operatorname{Nat}\right), \left(\forall \left(d: \operatorname{Nat}\right), \left(\forall \left(y: \operatorname{Fin}\left(d\right) \to \operatorname{Real}\right), \left(\forall \left(\mu: \operatorname{Fin}\left(d\right) \to \operatorname{Nat}\right), \left(\left(\operatorname{Admissible}\left(n, d, y, \mu\right)\right) \Rightarrow \left(\left(\exists \left(x: \operatorname{Fin}\left(n\right) \to \operatorname{Real}\right), \operatorname{Realizes}\left(y, \mu, x\right)\right) \Rightarrow \left(\forall \left(P: \operatorname{I}\left(n\right) \to \left(\operatorname{Fin}\left(d\right) \to \operatorname{Real}\right)\right), \left(\left(\left(\operatorname{Member}\left(P, \operatorname{PrunedProjection}\left(y, \mu, \operatorname{Delta}\right)\right)\right) \Rightarrow \left(\left(\operatorname{Member}\left(P, \operatorname{PrunedProjection}\left(y, \mu, \operatorname{S}\right)\right)\right) \land \left(\operatorname{SubsetCuts}\left(y, \mu, P\right)\right)\right)\right) \land \left(\left(\left(\operatorname{Member}\left(P, \operatorname{PrunedProjection}\left(y, \mu, \operatorname{S}\right)\right)\right) \land \left(\operatorname{SubsetCuts}\left(y, \mu, P\right)\right)\right) \Rightarrow \left(\operatorname{Member}\left(P, \operatorname{PrunedProjection}\left(y, \mu, \operatorname{Delta}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Turnpike/PrunedSubsetProjectionObstruction.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. S. Elder, Guillaume Marçais, Carl Kingsford (2026). *Turnpike with Uncertain Measurements: Triangle-Equality Integer Programming with a Deterministic Recovery Guarantee*. DOI: [10.4230/LIPIcs.WABI.2026.20](https://doi.org/10.4230/LIPIcs.WABI.2026.20). URL: <https://drops.dagstuhl.de/storage/00lipics/lipics-vol390-wabi2026/html/LIPIcs.WABI.2026.20/LIPIcs.WABI.2026.20.html>.

*Commentary.*

At zero-based triangle (1,3,5), corresponding to publication triangle (2,4,6), the three expectations are −17/25, −2/25 and 29/50. Their sum is −9/50, contradicting nonnegativity. Hence no independent full T exists for this same entire P, even before imposing full T masks. This P lies in the rank-pruned spine projection and satisfies every subset cut. The result has literal type Not claim.

This is a finite exact refutation of the stated universal projection equality. It does not assert a smallest counterexample, algorithmic speed, resolution of an externally named conjecture, or a sufficient characterization of the full projection. The general sparse partial-flow bound is reusable; the remaining data and finite checks serve this one countercertificate.

## References

- Truth anchor: `D5/S3/Combinatorics/Turnpike/PrunedSubsetProjectionObstruction.claim`
- Truth anchor: `D5/S3/Combinatorics/Turnpike/PrunedSubsetProjectionObstruction.result`
