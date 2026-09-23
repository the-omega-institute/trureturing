# Actual original classes can make the current uniform kernel suboptimal for two-step survival

This is an ordinary mathematical counterexample with an exact finite check. It refutes the claim that the source's particular uniform-on-G current-loss minimizer must maximize two-step survival under the same fixed caps. It does not refute the source current-loss lemma, identify the old law with report466's constructed law, or certify a uniform improvement for arbitrary original families.

## Original family and one old law

Let K=945=3^3·5·7, q=23, r=29. The old original classes are 0 mod3, 0 mod5, 0 mod7. Use the uniform probability μ on their 432 actual survivors modulo945. Its full Haar-density cap is 35/16 and its complete nonunit cylinder-query sum is 653/432. Thus this is a full-support old law, not a Dirac source.

Add 0 mod23, 0 mod29 and 25 mod69, the latter having old phase1 mod3 and q phase2. List the divisors of945 increasingly:

    d_j = 1,3,5,7,9,15,21,27,35,45,63,105,135,189,315,945.

For each j=1,...,16, add one original class of modulus 667d_j with CRT phases

    old ≡1 mod d_j, q ≡1 mod23, r ≡j mod29.

All 22 numerical moduli are distinct odd integers greater than one. In particular the d=1 cross label is retained. Their literal residues are:

| Modulus | Residue | Modulus | Residue |
|---:|---:|---:|---:|
| 3 | 0 | 5 | 0 |
| 7 | 0 | 23 | 0 |
| 29 | 0 | 69 | 25 |
| 667 | 1 | 2001 | 553 |
| 3335 | 3106 | 4669 | 323 |
| 6003 | 208 | 10005 | 2761 |
| 14007 | 5314 | 18009 | 1864 |
| 23345 | 2416 | 30015 | 28981 |
| 42021 | 27532 | 70035 | 12076 |
| 90045 | 18631 | 126063 | 65206 |
| 210105 | 21736 | 630315 | 608581 |

Every class has a private integer, recorded and checked in the JSON. The full family misses196561. It is an actual noncovering family used to compare kernels, not a covering counterexample.

## The two kernels use the same caps and29 continuation

Fix C23=11/5 and C29=7/3. The first is the source's stage23 cap; the second is the same capped-kernel formula with threshold16 at29, as in the retained two-stage comparison schedule. Every density here is relative to full-coordinate Haar measure. At zero-probability histories use the same explicit capped current-loss formula under both strategies; it remains normalized and within the same caps.

For an old survivor h, the actual23 good set is

    G_h={1,...,22}\{2} if h≡1 mod3,
    G_h={1,...,22} otherwise.

Its size is21 or22, so the source current-loss kernel is uniform on G_h. The cap11/5 permits it, and its current mixed loss is zero on every old history in the support.

At q-coordinate u≠1, only the pure29 digit0 is forbidden, and the29 current-loss kernel survives with probability1. At u=1, exactly

    t(h)=#{d|945: h≡1 mod d}=τ(gcd(h−1,945))

cross classes are active. Their29 phases are distinct, so the good29 set has size28−t(h). The fixed capped current-loss29 kernel therefore has surviving probability

    f_h(1)=min(1, (7/3)(28−t(h))/29).

If h=1 mod945, then t=16 and f_h(1)=28/29. For any other h, gcd(h−1,945) is proper; every proper divisor of945 has at most12 divisors. Hence t≤12 and f_h(1)=1. No hidden probabilistic independence is used.

In particular, h=1 and h=4 have the same current23 good set and the same current optimal loss0, but different continuation scores at u=1. A summary sufficient only for the current23 operation does not determine the two-step value. The extra information comes from active original29 labels, not from changing the input residues.

Keep this same29 kernel as a function of (h,u) under both strategies. At the exceptional point (h,u)=(1,1), its12 good29 digits have density7/3. The16 mixed-bad digits each have density1/16, and the pure digit has density0. This integrates to1 and leaves28/29 surviving mass. At every other point the kernel is uniform on its actual29 good set and has density at most29/16<7/3.

The alternative23 kernel changes only h=1: use the uniform law on G_1\{1}, which has20 digits. Its density23/20<11/5; it still assigns zero mass to every current23 bad point. At all other old histories retain the baseline kernel. Both strategies thus have pointwise minimal current loss0 and the same old marginal. The alternative chooses its23 transition using the full fixed family and actual old history, never an auxiliary comparison variable or the as-yet-unsampled29 digit. The source's section *Conditional kernels and absolute losses* explicitly permits dependence on the complete fixed family and earlier actual coordinates; it excludes auxiliary comparison variables. Its edition and attribution are fixed in the [library entry](../../../../../Library/Arith/schroeder2026nine.md).

For the source strategy, the exceptional old history has final conditional mass

    (20+28/29)/21=608/609.

Every other old history has final conditional mass1. Therefore

    baseline final mass = 1−1/(432·609)=263087/263088,
    alternative final mass = 1,
    exact gain = 1/263088 >0.

The gain changes the actual final mass, not merely its upper comparison or a physical moment before deletion. If full support on the original final survivors is required, mix the two normalized23 kernels equally before applying the same29 kernel. This keeps all caps and pointwise current optimality, is positive on every actual survivor, and gives gain1/526176. No separate old law or independently favorable29 strategy is spliced in.

For seven actual old primes, append the original pure classes0 mod11,13,17,19 and tensor μ with the corresponding uniform nonzero laws. The old period is43648605, the family has26 labels, the old cap is323323/110592 and its query sum is7037029/2985984. The same two-step gain remains1/263088. These obey the published scalar bounds but are not asserted to be the particular report466 law.

## Reuse and the finite-prefix implementation interface

The general optimization below is already weighted fractional knapsack. It requires no new theorem, wrapper, or Lean declaration. [Chapter04c](../../problem-details/04c-full-history-capped-laws-and-exact-global-optimization.md), sections2–3 already gives the exact backward optimum and original-label-signature trie compression, implemented in [the existing Bellman program](../../frontier/source-budgets/capped_head_bellman.py). Its integer-cardinality caps use uniform k-child choices; the present caps give rational capacities11/115 and7/87 per23/29 leaf and therefore use the existing fractional allocation form at a boundary atom. [Profile-note04](../001-064/04-the-weighted-upper-quantile-lemma.md) gives that weighted upper-quantile interface; [note16](../001-064/16-a-common-dual-test-law-for-redistributing-charged-bad-mass.md) KR2 directly reuses `FractionalKnapsackDual.fractional_knapsack_strong_duality` and `greedy_attains_duality`. This is a use of those interfaces, not a new DP or compression result.

For one actual old history h, compile the pure-q antichain, q-axis antichain and original cross q-prefixes into a finite prefix partition of V_q, the pure-q survivors. A block atom A_j has exact Haar weight w_j; its q-good flag and the list of active original r-prefixes are constant. Form the latter prefix union with the actual pure-r and r-axis sets, retaining each original phase. The exact remaining r mass g_j is computed by its minimal forbidden-prefix antichain. Then

    ψ_j = 1_(A_j⊂G_q) min(1,C_r g_j).

This is a partition by finitely many relevant prefixes, not enumeration of the complete K q^H r^J period. Different original labels may generate the same prefix; union computation can merge the geometry while their original identities remain available for inventory accounting. Old histories can likewise be grouped only when their actual activation patterns agree; their weights must come from the same supplied old law.

Assume both pure-survivor capacities are feasible: C_q H(V_q)≥1 and C_r H(V_r)≥1. The r-stage continuation is its actual capped current-loss optimizer; an arbitrary fixed r kernel would instead supply its own actual surviving probability as the score. A normalized q kernel is a mass vector p_j satisfying

    0≤p_j≤C_q w_j,    Σ_j p_j=1.

Its two-step mass is Σ_j p_j ψ_j. Sort positive scores downward and fill each atom to capacity until total mass1. Split the boundary mass if needed; the corresponding density is constant p_j/w_j on that atom, so no subdivision of a physical leaf or new outcome is required. If positive-score capacity is insufficient, fill the zero-score q-good atoms before q-bad atoms. This tie rule ensures the selected optimizer also minimizes the current q loss. All score data come from the fixed original input before the kernel is sampled; they are not unobserved future outcomes.

The exact threshold optimality certificate is: for some λ, positive weight atoms with ψ_j>λ are saturated, those with ψ_j<λ have zero mass, and atoms with ψ_j=λ supply the remaining normalization. Zero-score ties follow the good-before-bad rule above. Equivalently there is no donor i with p_i>0 and recipient j with p_j<C_q w_j such that ψ_j>ψ_i. These are the existing finite-knapsack primal conditions, not an additional arithmetic theorem.

A directly consumable improvement certificate needs less data than the complete optimum. On an uncharged history with g=H(G_q)>1/C_q, the source density on G_q is d0=1/g. Choose disjoint measurable D,R⊂G_q with positive exact weights a=H(D), b=H(R). Transfer any

    0<ε≤min(d0 a, (C_q−d0)b)

from the uniform distribution on D to the uniform distribution on R. The resulting normalized kernel has unchanged zero current loss and obeys the same cap. Its exact two-step gain is

    ε [ E_H(ψ|R) − E_H(ψ|D) ].

One may replace the bracket by a certified lower separation of the scores. Integrate this gain under the same old law. For the fixture, h=1 has D={1}, R=G_1\{1}, ε=1/21 and score separation1/29. Hence its conditional gain is1/609 and its global gain is1/263088. Half that transfer provides the full-support version.

If g≤1/C_q, minimizing current loss forces densityC_q on every positive-Haar q-good point, and this good-side reweighting cannot improve survival without changing current loss or the cap. If g>1/C_q but ψ is constant on G_q, reweighting it gives no gain. On a finite positive-weight partition, nonconstant ψ and strict cap slack give a positive exchange. These are exactly the saturation and score-separation checks to retain; merely knowing q/r marginal loads or an unweighted variance does not supply their same-law integrated value.

## Existing results and the narrow additional conclusion

Note16 already treats good-side changes: SI3–SI4 distinguish natural-cap saturation from global-cap slack, and GC1–GC6 give a PG1/17 original-family perturbation improving the actual supported Γ at every finite height. Its final survivor mass stays fixed. Therefore good-side freedom, the global-cap distinction, quantile optimization and variance bounds are not new results here.

[Note327](../321-384/327-actual-two-prime-survival-needs-a-masked-moment.md) fixes the23 kernel and compares two original families with equal scalar29 readings but different masked moments and final mass. Its counterexample proves an information deficit, while the present fixture fixes one family and changes one feasible kernel to improve actual mass. [Note22](../001-064/22-comparing-the-two-killed-steps.md) supplies fixed killed-continuation comparisons, actual mask/pair entries and finite error accounting; it does not assert current-loss optimality for two-stage survival.

The useful additional finite result is thus limited to the actual22-label counterexample at the specified23/29 source caps and its reusable input contract. It does not make the source comparison vertices into attainable original phase configurations. To obtain a uniform seven-core gain, one still needs a lower bound under the chosen source law on the actual score separation times available exchange mass. Source caches do not retain this joint original-inventory profile.

The baseline and half-mixture both give positive weight to every original survivor. In this finite carrier, each has positive final mass exactly when the original survivor set is nonempty. Changing the strategy cannot create an uncovered integer; the purpose is to improve estimates for the same set. Full support alone supplies no positive lower bound before nonemptiness is established. The present family is already covered by existing small-support noncoverage results, so this counterexample enlarges no proven noncoverage range.

## Exact check

The [exact checker](../../frontier/cover-geometry/future_aware_two_prime_survival.py) reconstructs every numerical original label, checks269352 actual good23 CRT points against all22 labels, checks both normalized capped kernels and all private witnesses, and computes the two final masses with rational arithmetic. It also checks the independent seven-prime padding constants. Its [result data](../../frontier/cover-geometry/future_aware_two_prime_survival.json) retain the original labels and numerical outcomes. Run from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/future_aware_two_prime_survival.py
```

The default output is exact JSON on stdout; optional `--output PATH` writes it to the chosen file.

All assertions use explicit exceptions. These finite checks are not an end-to-end Lean proof or an unrestricted Erdős #7 result.
