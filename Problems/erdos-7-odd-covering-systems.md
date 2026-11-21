---
slug: erdos-7-odd-covering-systems
bibkey: bloom2026erdos
doi: null
url: https://www.erdosproblems.com/7
triage: wall
motivation_gids:
  - D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity
---

# Erdős #7: odd covering systems

## Problem

The [problem page](https://www.erdosproblems.com/7) asks:

> Is there a distinct covering system all of whose moduli are odd?

The negative target is the following unrestricted assertion. For every finite
set `D ⊂ ℕ` with `d > 1` and `d` odd for every `d ∈ D`, and every assignment
`a : D → ℤ`, there exists `z ∈ ℤ` such that

\[
  \forall d\in D,\qquad d\nmid z-a(d).
\]

Divisibility is in the integers. Set membership enforces distinct moduli;
there is no bound on their sizes, exponents, number, or total prime support.
A refutation requires a finite family satisfying exactly these conditions
whose classes cover every integer. The page remained open when read on
28 September 2026. The results below do not settle this unrestricted assertion.

The complete results and proofs are organized below. Each link opens the corresponding mathematical section; all original assumptions, bounds and open obligations are retained.

### Results and proofs

- [If a distinct odd cover has least modulus 9 and omits 15 and 21, then it must use both 33 and 45](#necessary-small-moduli-when-the-least-modulus-is-nine)
- [RH gives an explicit prime-weighted continuation with cutoffs 449, 2543 and 8231](#a-prime-weighted-continuation-using-rh)
- [Passing every complete prime marginal requires at least six support primes; with exactly six, five monotone survivor-profile exclusions leave only seventeen prime sets, with arbitrary heights and residues. These are necessary conditions, not feasible constructions or a solution of the unrestricted problem](../Library/Arith/lettlsun2008cosets.md#existing-survivor-laws-restrict-simultaneous-complete-marginal-feasibility)
- [Actual tight rows can be individually coverable yet admit no common original phases: a complete odd-wheel CRT graph passes every clique budget and has a sharp positive defect on its tight region; other rows remain below one, so this is not a new global noncoverage range](../Library/Arith/lettlsun2008cosets.md#common-original-phases-can-obstruct-all-tight-rows)
- [A blocked joint-loss tree forces private leaves or a doubled multiplicity budget; removing the height factor requires one distribution across blocked fibres. Two odd noncovers defeat the local geometric shortcut, while the complete-source projection count rejects both](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/375-deep-prime-prefix-projections-and-tree-contraction.md#9-liability-multiplicity-and-the-missing-distribution-of-blocked-fibres)
- [The true joint loss after deleting low-height originals gives a necessary-and-sufficient prime-absorption test; extremal covers require a common blocking law avoiding every retained event, and an actual even control separates this from both the old filter and an unsafe individual-private shortcut](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/375-deep-prime-prefix-projections-and-tree-contraction.md#8-joint-liability-gives-the-exact-absorption-criterion)
- [Two different complete, exactly valued prime-coordinate averages recover every original numerical label and phase when moduli are distinct; finite-field height peeling preserves the actual source, while a period24 even control separates support-prime average lower bounds from whole coverage](../Library/Arith/lettlsun2008cosets.md#complete-prime-coordinate-averages-identify-distinct-original-labels)
- [Absorbing a larger prime into new higher digits of a smaller prime gives a live-cofactor blocker and the necessary bound q-r<=H*tau(M)-1; an actual irredundant even cover contracts14 to8, and a filtered-only control separates retained from discarded events](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/375-deep-prime-prefix-projections-and-tree-contraction.md#7-live-cofactors-obstruct-absorbing-a-larger-prime-into-new-higher-digits)
- [Original descendants raise the private-hull closure threshold from d to the largest original multiple of d; a same-phase group gives an exact repair budget for the complete private region, and a ten-class odd noncover passes every old PH5 test but admits the stronger reduction](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#10-descendant-assisted-private-hull-closure-and-phase-group-repair-budgets)
- [A reciprocal private-hull pair admits an exact source-preserving swap: after repairing both complete private regions, only the points with exactly those two old owners remain at risk; any surviving descendant then gives a strict cardinality descent, while comparable pairs only simplify one hull condition and crossed pairs remain open](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#176-reciprocal-private-hull-swaps-leave-one-exact-joint-liability)
- [If a reciprocal private-hull pair has at least two receiving descendants, its occupied lcm transfers the exact remaining liability to the lcm's complete private region; every repair needs at least as many classes as deleted descendants, and every divisor of the lcm hull must remain in the retained label palette](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#177-an-occupied-lcm-transfers-a-reciprocal-swap-to-complete-private-liability)
- [An irredundant odd noncover with every normalized prime class satisfies all scalar directional inequalities at every actual private point and every divisor cut, but still has a hole; numerical moduli repeat, and thinning to distinct labels destroys the prime13 demand](../Library/Arith/lettlsun2008cosets.md#prime-normalization-and-all-private-scalar-cuts-do-not-force-line-coverage)
- [The463-class obstruction also excludes every mixed-prime common-center relocation batch:1603 actual parent-phase options are contradicted by private and joint-owner point constraints; one five-parent control preserves all858 supplied private points but loses a jointly covered integer, and arbitrary pure-prime tails retain the exclusion](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/450-499/450-weighted-original-depths-and-the-uniform-lift-boundary.md#138-mixed-child-primes-also-forbid-every-common-center-relocation-batch)
- [At one original private point, every affine quotient cut reduces exactly to a prime-depth suffix; arbitrarily high divisor-closed, irredundant odd families pass all those cuts and every shell-mean test at that point and prime while leaving holes on the same prime line](../Library/Arith/lettlsun2008cosets.md#arbitrary-quotient-cuts-collapse-to-the-same-depth-suffixes)
- [Mixed parent-divisor and crossed carriers have an exact allocation threshold: a26-class divisor-closed odd family contracts to24 using only three proper cofactor divisors where the all-crossed route requires seven](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#9-mixing-three-carrier-types-lowers-the-exact-divisor-requirement)
- [The463-class obstruction resists every size of same-prime centered parent relocation, even with all children retained:858 verified private points exclude1658 options without enumerating subset sizes; arbitrary pure-prime tails preserve this at arbitrarily small positive hole density](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/450-499/450-weighted-original-depths-and-the-uniform-lift-boundary.md#137-every-size-of-same-prime-centered-parent-relocation-is-blocked)
- [Two actual composite-parent patterns permit joint two-class reductions, including one at every ternary height; divisor-closed irredundant families contract26 to24 and18 to16 with no lost covered points although either separate contraction fails, while occurrence in every hypothetical cover remains open](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#6-a-mixed-root-cross-permits-a-joint-composite-parent-contraction)
- [Every original literal4555 height-two maximum74 source admits one common law with Gamma1225 at most9-7/11026; shared-row reduction and one fixed mixture close the final stratum of this fixed-head source class, while arbitrary heights and original outside-cofactor lifting remain open](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#one-common-law-below-nine-for-the-complete-original-maximum74-class)
- [Every current maximal mass18 entry can be lowered globally or yields an already supplied cut; outside those branches, one shared unit of capacity reduction can be assigned to all current bad entries, with RC74 supplying the additional common-query regularization](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#current-maximal-mass18-entries-admit-global-capacity-reductions)
- [Two safe half-unit transports decrease one common balanced74 potential in at most four steps; exact complete-source controls verify both moves, while terminal actual-support traps and universal accessibility remain unresolved](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#safe-half-unit-transports-decrease-one-common-balanced74-potential)
- [A jointly minimal set of dangerous mass18 blocks forces one-inactive77, two-inactive80 or three-inactive83 cuts; only the five exact83 shapes lie outside the listed suppliers, but lowering a sum is not yet a common-law proof](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#joint-selected-block-minimization-yields-a-controlled-inactive-root-cut)
- [Every actual cut through80 with at least two inactive roots admits one law bounded by2865/319; exact three-inactive83 cuts leave five explicit complete-fibre profiles requiring further suppliers](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#two-inactive-cuts-through80-and-the-exact-three-inactive83-boundary)
- [A463-class irredundant divisor-closed noncover defeats both low-excess suppliers under every outside law; CRT extensions preserve the obstruction with arbitrarily many support primes, arbitrary tail heights, and arbitrarily small positive uncovered density, leaving exact whole-cover structure essential](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/450-499/450-weighted-original-depths-and-the-uniform-lift-boundary.md#13-irredundancy-and-divisor-closure-do-not-supply-a-low-excess-law)
- [Deleting189 individually contained classes from the original452-class phase obstruction preserves its entire covered set and leaves zero phase excess at one outside point; this applies to that input, while the different463-class irredundant obstruction admits no such reduction](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/450-499/450-weighted-original-depths-and-the-uniform-lift-boundary.md#124-containment-reduction-removes-this-particular-obstruction)
- [A selected balanced74 mass18 block either lowers globally to at most17.5 or yields an already supplied one-inactive77/three-inactive82 actual cut; a complete282-point source verifies lowering18 to0, with simultaneous common-law handling supplied by RC74](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#a-selected-mass18-block-can-be-lowered-or-supplies-an-existing-actual-source-law)
- [T3-good whole block support permits one mass18 transport with fine bound2175/7; together with mass18.5 repair this gives the conditional balanced74 law9313/1036, with the remaining T3-bad blocks handled by the later RC74 whole-source mixture](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#t3-good-actual-support-repairs-the-mass18-half-integral-obstruction)
- [Balanced value74 admits support-uniform mass18.5 transport with fine bound1835/6; a unique mass18 flow refutes universal fixed-external repair, leaving a precise joint-flow condition for the conditional1331/148 law](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#balanced-value74-admits-mass185-transport-but-fixed-external-mass18-repair-can-fail)
- [Every original height-two4555 source of maximum flow75 or76 admits one law with Gamma1225 at most3572/397; three-inactive cuts through82 are supplied, while its particular source-capacity obstruction at maximum74 is bypassed by the later RC74 theorem](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#every-original-maximum-flow75-or76-source-has-a-common-law-below-nine)
- [Four classified original children and an arbitrary fifth admit one actual law bounded by2779/323; all2,985,984 coarse queries and complete-source controls support the supplier for both remaining partial and11113 public3 profiles](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#an-unrestricted-original-fifth-child-supplies-the-two-remaining-public3-profiles)
- [Fourteen actual private points and one joint public law supply eight nonpartial public-cost3/4 cut profiles with bound3572/397; two original-source controls exclude the automatic three-exterior-label bridge for11113](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#fourteen-private-points-supply-eight-nonpartial-public3-and-public4-profiles)
- [Two public labels and a complete clean full root admit one actual law; the shared-column bound4252/477 supplies all five one-inactive public-cost2 profiles through77, with public costs3–4 supplied by the later fourteen-point consumers; the unrestricted lift remains open](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#two-public-labels-on-a-clean-full-root-supply-one-common-law)
- [One-inactive cuts through77 with public prefix cost0 or1 admit a common law below nine; three tight full11222 roots have an explicit law bounded by80/9 via the shared49/7/35 queries. The subsequent two-public-label supplier handles cost2; the later fourteen-point consumers handle costs3–4; the unrestricted lift remains open](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#one-inactive-root-with-public-prefix-cost-zero-or-one)
- [Every actual cut below80 with at least two inactive roots supplies one law at most2865/319; complete fibres and a four-owner public-singleton argument close the entire two-inactive C75/C76 obstruction branch](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#any-actual-cut-below80-with-at-least-two-inactive-roots-supplies-one-law)
- [A452-class literal noncover has merged phase excess above both reserve thresholds at every outside survivor, refuting an unconditional low-excess supplier under every supported law; whole-cover structure is still needed](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/450-499/450-weighted-original-depths-and-the-uniform-lift-boundary.md#12-a-literal-noncover-forbids-every-unconditional-low-excess-law)
- [Retained numerical weights replace depth multiplicity by outside-support incidence under one common law; explicit conditional criteria allow arbitrary retained heights and positive phase collisions, while shared-cylinder examples separate merged envelopes from divergent row costs](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/450-499/450-weighted-original-depths-and-the-uniform-lift-boundary.md#11-retained-weights-pay-arbitrary-depth-multiplicity-under-one-outside-law)
- [Every complete full12222 source admits one original-source law with Gamma1225 at most2865/319; graph reductions and a complete128-layout classification finish the specified C75/C76 three-inactive-root lists, with the whole75/76 classes supplied by the later RC76 theorem; RC74 supplies maximum74, while arbitrary-height lifting remains open](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#every-complete-full12222-source-admits-a-common-law-below-nine)
- [Sharp mass19 transport and maximum-flow terminal synchronization give conditional74–76 laws; complete actual sources refute universal terminal-cap feasibility despite good common laws, motivating one joint coarse-cap flow criterion](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#mass19-transport-terminal-synchronization-and-conditional-balance-consumers)
- [Every complete monochromatic anchor supplies a law below nine; two singleton and two double fibres allow an arbitrary fifth fibre, and gap12/gap222 permit arbitrary remaining fibres, supplying three further C75 shapes](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#every-complete-monochromatic-anchor-supplies-a-common-law-below-nine)
- [Every complete full11222 source admits one common law with Gamma1225 at most503/56; distinct-label punctures and all64 root-query layouts supply the final C76 three-inactive-root shape, with the remaining one-inactive branches addressed by later reductions](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#every-complete-full11222-support-has-one-common-law-below-nine)
- [A full root with one public and five private candidates admits one common law with Gamma1225 at most503/56; exact shared-query certificates supply the entire full/public1/private11111 family](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#a-public-singleton-and-five-private-candidates-at-a-full-root)
- [Four complete double fibres at the gap admit one actual common law with Gamma1225 at most719/80; normalized original trees retain the complete shared-label exclusion, supplying gap2222 without a minimum-cut or standalone premise](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#four-complete-double-fibres-at-the-gap-admit-one-common-law)
- [Small complete anchors supply seven further three-inactive-root cut shapes; retaining global fine-label exclusion gives common laws for three to eight sparse labels, with the whole75/76 classes supplied by the later RC76 theorem; RC74 supplies maximum74, while the arbitrary outside-cofactor lift remains open](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#small-complete-anchors-supply-additional-common-laws-below-nine)
- [One fixed anchor per retained numerical modulus supplies an actual outside law with zero phase excess when its row budget is below one; a pure-survivor bound and bad-depth incidence at most48 give an explicit sufficient class, without solving the arbitrary-family lift](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/450-499/450-weighted-original-depths-and-the-uniform-lift-boundary.md#10-anchor-phases-give-a-same-law-arithmetic-supplier)
- [Every literal4555 height-two actual source of maximum flow77 has one common law with Gamma1225 at most2078/231: asymmetric capacities and exact-cut uncrossing close this finite stratum; the later RC76 theorem supplies75/76; RC74 supplies maximum74, while the arbitrary outside-cofactor lift remains unresolved](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#asymmetric-root-capacities-supply-the-complete-maximum-flow77-class)
- [Whole coverage forces weighted excess of distinct retained phases at every outside survivor; one-law phase merging retains the exact subtraction. Section12 rules out an unconditional strict reverse for arbitrary families, leaving a whole-cover-specific bridge open](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/450-499/450-weighted-original-depths-and-the-uniform-lift-boundary.md#9-whole-coverage-needs-weighted-excess-of-distinct-projected-phases)
- [Every exact77 cut with one inactive root admits one actual common law below nine: a bounded residual-cycle step handles the gap root, and integer budgets reduce the full-root case to IF77](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#one-inactive-full-root-has-no-remaining-partial-child-exact77-profile)
- [Avoiding each five-block set is sufficient for one common phase law; failure forces a minimal two-to-five-block hitting family, without making that family a negative law certificate](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#avoiding-every-five-block-set-is-a-sufficient-joint-bridge)
- [Two remaining capacity78 profiles admit actual common laws: gap2222/full22222 has bound249/28, and full12222/full12222 has1385/154 including its fourth-column exception](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#the-private-gap2222full22222-profile-admits-a-common-law)
- [An exact capacity77 cut with two inactive roots admits one actual common law with Gamma1225 at most1385/154; capacity78 reduces to nine private cost shapes, while the unrestricted cofactor lift remains open](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md#two-inactive-roots-at-exact-capacity77-admit-one-common-law)
- [Occupancy-aware restrictions and weighted root caps give one law below nine for four-root height-(2,2) product-tree blockers with at most one full five-child fibre](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/445-occupied-branch-restrictions-and-weighted-root-caps.md)
- [Uniform subtree restrictions couple both prefix trees under one actual law; three robust first-five roots give Gamma6125 at most2024/225 without a fixed good-fibre selector](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/444-uniform-subtree-restrictions-couple-two-prefix-trees.md)
- [One finite flow couples row and tree-prefix caps with optimal joint factor q/m; isolated ternary five-prefix sources admit one law below nine through five-height22 and every finite seven-height](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/443-one-supported-law-couples-rows-and-tree-prefixes.md)
- [Minimum coarse sources admit matching lifts and two height strips below nine; joint mod25 fibres give a separate bound eight, while a 540-point blocker refutes automatic mod175 fibre matching](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/442-minimum-coarse-sources-lift-through-actual-fibres.md)
- [Integer joint moments improve actual-family height lifting with full cofactor tests; a four-atom joint witness limits what the four retained budgets alone can certify](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/441-integer-joint-moments-improve-two-axis-height-lifting.md)
- [A literal mod-35 mixture separates equal coarse-marginal and scalar-Gamma summaries; joint layout price profiles retain exact finite-fibre contraction and expose the additional conditions for dynamic boundary sufficiency](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/440-joint-test-profiles-as-composable-boundaries.md)
- [Fixed coarse marginals have an exact coprime free-coordinate completion cost; actual residual lifting retains a joint minimax obligation, and the original H1 scalar formula fails to reach nine at finite heights](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/439-actual-residual-lifting-and-exact-free-coordinate-cost.md)
- [Separated capacity-six flows and shared weak/grid blocks give common laws at most five; a distinct star construction remains below 46/9, with exact limits on support extraction and weak-child deletion](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/438-separated-weak-supports-and-common-laws.md)
- [Four roots with three nonsingleton children each and cross-root disjoint original exact pairs admit a common law below five; an exact capacity-flow formula removes the pair-extraction requirement](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/437-four-root-nonsingleton-sources-admit-a-common-law-below-five.md)
- [For one fixed original family, identical clique-DP keys count correctly but cannot answer a newly authorized archive read; actual branch records and CRT cells give distinct task-specific repairs using existing task-completion interfaces](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/436-self-observation-refines-a-count-sufficient-clique-state.md)
- [Minimum height-two sources are exactly three five-matchings and admit the sharp universal budget 68/15; every admissible source has an actual nine-point joint flow, while the weighted common-law condition remains additional](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/435-minimum-height-two-sources-and-a-nine-point-flow.md)
- [Every four-root, three-child, two-neighbor source with disjoint root pair sets admits one explicit original-label law of cost at most 149/30; larger-neighborhood controls delimit extraction and correctly aligned height lifting retains its actual-residual premise](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/434-four-root-pair-sources-admit-a-common-law-below-five.md)
- [Chordal overlap certificates have an exact active-component remainder; on all nonunit divisors of 945 their forced-coprime optimum is 175 survivors, improving the optimal forest bound 141 while leaving a gap to the existing sharp minimum 191](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/433-chordal-overlap-certificates-and-their-exact-finite-limits.md)
- [Actual four-root matching, rectangle and shared-column selections give common laws at five-height two; keeping the inherited seven phase shared yields the stronger bound five for two weak-root geometries, while an arbitrary-height source compression preserves every five-column projection](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/432-four-root-source-selections-and-the-shared-column-boundary.md)
- [At five-height two and seven-height one, three actual first-five fibres each meeting every child-by-column 3-by-5 rectangle admit one probability with complete independent-layout cost at most 46/9; this includes every three-root source satisfying the full product-tree test](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/431-three-robust-five-roots-admit-a-height-two-common-law.md)
- [The existing height-lifting formulas cannot carry the supplied first-five-layer constants to the all-height target nine; a precise same-law coarse/fine tradeoff is also refuted for the existing seven prescribed cap components, leaving free source-law selection open](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/430-same-law-height-lifting-needs-a-new-seed-tradeoff.md)
- [A sharp height-two cap-flow bound of 46/9 closes the remaining finite-height case: at five-height one, every source on four allowed rows with the full five-ary projection tree and all six pairwise ternary trees admits one probability meeting the complete independent-layout target at every seven-height](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/429-phase-conflict-cap-flow-closes-the-height-two-bound.md)
- [At five-height one, freely weighting any seven fixed full-five and pair-ternary cap laws gives a universal bound 407237/70076 below six and the finite target at every seven-height K at least three; a literal height-two fixed-component game has exact value 46/9](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/427-shared-row-cap-mixtures-break-the-six-barrier.md)
- [At five- and seven-heights three, legal fixed cap components can defeat every mixture of their weights even though the source has a good law; two actual laws with identical complete coordinate marginals have exact joint moments 328/27 and 5776/729](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/428-fixed-cap-components-do-not-transport-across-five-adic-depth.md)
- [Two exact eight-prime cores omitting 7 admit arbitrary seven-vertex attachments under the inherited Chapter 31 and ordinary-source premises; extendible core Haar density exceeds 1/2200000](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/69-eight-prime-cores-omitting-seven.md)
- [An eight-prime core {3,5,7,13,17,19,23,29} omitting 11 admits arbitrary seven-vertex attachments under the inherited Chapter 31 and ordinary-source premises; extendible core Haar density exceeds 1/2200000](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/68-eight-prime-core-omitting-eleven.md)
- [Complete shared-root query tables, an exact binary flow/cut certificate and rational first9-prefix charges strengthen the unchanged actual-law credit to16.8681002893431; a feasible relaxed assignment bounds the remaining room in this refinement.](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/67-shared-root-prefix-bounds-for-the-actual-survivor-law.md)
- [An exact shared-phase triangle correction sharpens the unchanged actual-law credit; uniform layout averaging caps the complete seven-prime triangle replacement, and finite positive measures refute a universal common-CRT-center restriction.](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/66-shared-phase-triangles-and-common-center-obstruction.md)
- [Complete survivor-cylinder queries and exact small-modulus controls certify a fixed-law credit, while independent support counts place the entire E154 independent-marginal-max tau1 method strictly below the credit required at B16384; joint layout improvements remain outside this ceiling.](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/65-independent-survivor-marginal-ceiling-at-the-fixed-cutoff.md)
- [An attained full-history adaptive order among core7 coordinates lowers the exact seven-phase154 bad mass; its complete positive policy is reconstructed on actual leaves, and the three retained stop-loss thresholds are unique real-threshold minima of their fixed directed upper envelopes.](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/64-adaptive-core-policy-and-continuous-stoploss-optima.md)
- [A common squared-load stop-loss threshold strengthens same-law conditioning for every complete divisor layout; all1362 exact square-threshold bounds are independently reproduced from the complete verified product tables.](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/63-squared-load-stoploss-continuation.md)
- [Enlarging the stop certifies the attained seven-phase head atB32768, and its full outside-D7 smooth extension atB65536, with every directed stage independently reproduced.](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/62-expanded-stopping-cutoffs-for-the-seven-phase-head.md)
- [Coordinatewise retention transports the exact auxiliary budget lower bound; combined with the fixed positive cylinder polynomial it excludes a full relative1/50000 box of all finite head-depth caps.](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/61-coordinate-retention-and-profile-neighborhood-obstruction.md)
- [A fixed positive cylinder cover yields a38-term multiaffine survivor bound at new caps on all20 head coordinates, with every coefficient independently reproduced.](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/60-positive-cylinder-covers-across-head-profiles.md)
- [Globally injective terminal phases reduce core-first optimization; a seven-phase family defeats the fixed balanced-profile budget for every adaptive order while retaining an uncovered integer and154 private class witnesses.](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/59-terminal-phase-elimination-and-uniform-balanced-profile-obstruction.md)
- [An adaptive five-prime initial block recovers fixed-phase noncoverage where all 120 fixed block orders fail the same budget; a cylinder dual excludes scheduling-only recovery of the fixed D7 allowance](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/58-adaptive-initial-block-recovery-and-all-schedule-budget-obstruction.md)
- [A balanced depth profile enlarges the fixed 154-class noncoverage result to the degree-seven exponent frontier with unrestricted original tails](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/57-balanced-depth-profile-and-degree-seven-frontier.md)
- [Joint exponent frontier D9 extends the fixed 154-class noncoverage law; a cylinder-cover dual sharply bounds a literal 105 family](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/56-exponent-frontiers-and-cylinder-cover-certificates.md)
- [Adaptive read-once head orders retain conditional comparison and strictly improve a family of period 315; the joint atom-cap obstruction persists](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md)
- [Depth-profile laws prove noncoverage for the literal 154-class head, arbitrary sixth-power smooth head additions and unrestricted original tails](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/54-depth-profile-head-laws-with-unrestricted-original-tails.md)
- [Exact optimization of full-prefix capped head laws, arbitrary fixed head order, and complete counterexamples to the universal 9/20 threshold](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/04c-full-history-capped-laws-and-exact-global-optimization.md#full-history-capped-laws-and-exact-global-optimization)
- [Shared small-prime budgets prove noncoverage through six or seven predecessor supports, with full Haar density and two exact limits of the complete support-Shearer envelope](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/53-shared-small-prime-budgets-for-six-or-seven-predecessor-supports.md)
- [Two exact predecessor supports in arbitrary order, or four in numerical order, give noncoverage with full Haar density; a large-prime inventory may grow as p to the one-quarter](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/52-two-or-four-exact-predecessor-supports.md)
- [At most two cycles per original incidence component gives noncoverage at arbitrary ranks and heights, full Haar density and unrestricted large-prime continuation](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/51-incidence-bicyclic-components-with-arbitrary-original-heights.md)
- [At most five distinct mixed supports per prime gives noncoverage at arbitrary ranks and heights, with full Haar density from actual conditional avoidance ratios](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/50-prime-support-incidence-at-most-five.md)
- [Arbitrary-rank prime-support incidence pseudoforests are noncovering, with height-independent full Haar density and unrestricted large-prime continuation](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/49-incidence-pseudoforests-with-arbitrary-original-heights.md)
- [Prime-support incidence forests admit simultaneous original-label extensions, a full Haar density bound and an unchanged-source attachment budget](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/48-incidence-forests-with-arbitrary-original-heights.md)
- [An anchored order with at most four earlier neighbours is noncovering: a record-minimum potential pays for arbitrary prime order and gives full Haar density greater than (107/240000)(5/12)^M](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/44-anchored-four-predecessor-orders-via-record-minimum-potential.md)
- [In arbitrarily many naturally ordered prime coordinates, identical complete AP event laws leave a sharp nonzero interval of half-threshold first-hit costs](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/43-sharp-first-hit-ambiguity-with-identical-complete-event-laws.md)
- [The complete original-AP event law can agree while first-hit costs differ; a two-level cap-aware LP has exact optimum 97/5775](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/42-two-level-fixed-colors-and-first-hit-moment-obstruction.md)
- [Natural increasing prime order with at most four smaller neighbours gives full Haar density greater than (3/800)(11/24)^M, including books with three private primes per page](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/41-natural-four-predecessor-orders-are-noncovering.md)
- [The fixed-order independent-run scalar ledger has global minimum 1.002553… over all real thresholds; actual cofactor colors require a stronger joint comparison](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/40-fixed-order-scalar-threshold-barrier-and-cofactor-colors.md)
- [An order anchored at 3,5 with 7 first and at most three earlier neighbours per later prime gives explicit full Haar density, allowing arbitrary overlap and large-prime continuation](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/39-anchored-three-predecessor-orders-are-noncovering.md)
- [An eight-prime core containing 3,5,7,11 admits arbitrary seven-vertex attachments; extendible core Haar density exceeds 1/2200000](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/38-eight-prime-cores-containing-three-five-seven-eleven.md)
- [All eight-prime cores containing 3,5 admit arbitrary seven-vertex attachments under the inherited Chapter 23/31 and ordinary-source premises; extendible core Haar density exceeds 1/2200000](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/70-all-eight-prime-cores-containing-three-five.md)
- [Audit of a claimed global nonexistence proof: the kernel-localization step is unproved, the extension allocation omits prime-power reuse, and the renormalization inequality has the wrong sign](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/71-audit-of-global-nonexistence-claim.md)
- [SRCT exact-two-9 nonexistence would imply the distinct odd-covering conjecture, but its repeated-layer gain bound fails; exact transport and every fixed-size nonnegative fractional union-capacity refinement lose positivity under some actual fresh-prime extensions](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/75-srct-exact-two-quantifier-audit.md)
- [An abstract 36-point source satisfies all selected prime-chain tree conditions and saturated-prefix caps, but every supported law fails the proposed full-history cap bridge and a finite-depth stop-loss comparison](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/388-saturated-chain-blockers-do-not-supply-conditional-caps.md)
- [The same 36-point source has exact complete-layout second moment 21/4 and all-height supremum 256543/32400 under uniform lifts; the direct second-moment comparison survives although the stronger conditional and convex bridges fail](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/389-saturated-chain-source-has-small-complete-layout-second-moment.md)
- [Every 5-by-7 root set meeting all three-by-five rectangles and using at least five columns admits one supported law with full-layout second moment at most 4; a support classification and Hall argument also bound independent uniform tail lifts](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/390-two-prime-root-blockers-admit-a-common-second-moment-law.md)
- [A diagonal depth-two source meets both full-tree conditions but has minimax second moment 33/5 above the proposed 529/81: the all-root finite-height extension fails, while the excluded-root arithmetic subclass remains unresolved](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/391-diagonal-prefix-sources-obstruct-the-finite-height-moment-comparison.md)
- [A normalized seven-point source has root minimax 631/166, but its identical optimal product fails at height two while a different product succeeds; the exact column-cap tradeoff also shows that root cost at most 4 requires a column of mass at least 1/4](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/392-root-optimal-laws-do-not-tensorize-the-full-layout-bound.md)
- [One compatible seed-and-tail probability on repeated type-B sources satisfies the full arbitrary-layout comparison at every pair of positive heights; its uniform bound is 67803771/7658816 below 9](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/393-two-digit-seed-controls-repeated-type-b-sources-at-all-heights.md)
- [Standalone tree blocking need not pass to joint prefix fibres; an explicit 116-point source still admits a common full-layout law bounded by 335/54](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/394-standalone-tree-blocking-need-not-pass-to-joint-prefix-fibres.md)
- [Every 5-by-7 source meeting all three-by-five rectangles admits a common root law with second moment at most 4, without any standalone column-count premise](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/395-root-rectangle-blockers-need-no-standalone-projection-condition.md)
- [A row containing a complete five-ary 7-tree, with ternary trees in each pair of the other three rows, supplies a common full-layout law at every depth K at least 2; its uniform bound is 60709/10800 below 6](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/396-a-heavy-row-controls-all-seven-adic-depths.md)
- [If every union of three of the four rows contains a five-ary 7-tree, a stationary mixture gives one common full-layout law at every positive depth, with uniform bound 51/10; no pairwise ternary premise is needed](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/397-stationary-row-mixtures-control-all-seven-adic-depths.md)
- [For each of the six exact root types A–F, the full product and standalone tree conditions supply a common law satisfying the finite comparison at every seven-adic depth, without repeated tail geometry; arbitrary larger root supports remain outside this theorem](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/398-six-exact-root-types-control-arbitrary-seven-adic-tails.md)
- [A five-ary projection tree and at most two second seven-digits in each joint root cell give a common law with uniform bound 231/50; an explicit all-height family satisfies the full tree tests while containing no same-height component from the heavy-row, stationary-mixture or exact-root classes](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/350-399/399-sparse-second-digits-control-sources-outside-fixed-subclasses.md)
- [An exact tree-rank dual removes the source variable from the common-law problem; a literal-layout counterexample rules out averaging deterministic bounds, and a constructive tail-coupling criterion keeps full joint realizability](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/400-literal-layout-mixtures-and-exact-tree-rank-duality.md)
- [A recursive family attaining the minimum source size has one law for all original divisor phases at every height, with uniform comparison margin 43/1764; translated leaf colourings extend the construction beyond fixed-row private branches](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/401-a-recursive-minimum-source-has-one-law-at-every-height.md)
- [For every source with the six pairwise ternary trees and full five-ary projection, one actual law has independent-layout second moment below 168/25; this universal estimate still exceeds the required limiting constant six](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/402-one-common-law-with-a-universal-row-compatible-bound.md)
- [Sources of sharp minimum size at height at least two have a five-column root with either one two-surplus child or two one-surplus children; exact partition rules constrain the latter tails without supplying a new second-moment law](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/403-root-structure-of-sharp-minimum-sources.md)
- [A single full-and-pair-tree mixture has universal second moment below 309/50; actual witness choices rule out reaching six by a fixed mixing coefficient alone](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/404-a-sharper-common-law-and-its-witness-choice-boundary.md)
- [Four private terminal row children give one law with exact moment at most 19/5 at height at least two; refinement preserves a sharp two-surplus source family without proving inheritance for arbitrary sources](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/405-terminal-private-rows-control-sharp-two-surplus-sources.md)
- [Two admissible continuing root fibres and three distinct-row private full trees admit one law below the finite target; four admissible root fibres give another sufficient condition](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/406-actual-root-fibres-admit-one-law-below-the-target.md)
- [Actual sources obstruct a stationary row-weight recipe for every mixing coefficient; eight clean-tree signatures cannot constrain fixed row polytopes under uniformly faster-than-ternary prefix decay](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/407-limits-of-stationary-row-mixtures-and-finite-signature-summaries.md)
- [A balanced labelled five-tree supplies one law below the finite target at every height at least two; admissible sources need not admit that selection](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/408-a-balanced-five-tree-selection-controls-all-heights.md)
- [Two finite tail budgets preserve one actual common law through arbitrary ternary prefix depth; a nonuniform law resolves the balanced-selection boundary family with margin greater than 3/25](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/409-ternary-prefixes-preserve-terminal-common-laws.md)
- [Three initial ternary levels permit independently varying stopping depths and one actual law with margin greater than 7/225; a height-eight law lies outside every synchronized 409 certificate](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/410-an-initial-ternary-budget-allows-asynchronous-stopping.md)
- [Exact future survivor counts have canonical joint histogram at gcd(L,lcm(future)); actual odd-distinct histories refute dynamic sufficiency of separate next-action histograms](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/411-exact-continuation-state-is-a-joint-residue-histogram.md)
- [A larger finite-height five-tree criterion; a sharp minimum source blocks every uniform ternary root law but admits one five-tree law with margin at least 16/225](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/412-a-sharper-five-tree-law-crosses-the-ternary-root-obstruction.md)
- [One actual mixed centre and four independently shaped monochromatic ternary tails admit a common law; fixed root weights 65/197 and 33/197 allow central row cap 18/65](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/413-an-actual-mixed-centre-and-four-ternary-tails-admit-one-law.md)
- [Same-projection row transport gives one actual law for an explicit concentrated sharp source at every height K at least 10, with margin 9/100; a literal K=2 layout refutes the same fixed recipe](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/414-same-projection-transport-controls-concentrated-sharp-sources.md)
- [Even witness-dependent mixture coefficients fail the finite target on one fixed family of actual components, at every height; two original layouts give an exact segment obstruction](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/415-adaptive-coefficients-cannot-meet-the-finite-target.md)
- [Exact arbitrary-height separation retains all independent original phases; different actual laws succeed on the concentrated sharp sources at heights three and four](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/416-exact-independent-layout-tree-separation-and-actual-laws.md)
- [Exact prefix disagreement improves the same concentrated-source law to every height K at least seven, with margin 1/15 and no change of source or phase quantifiers](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/417-prefix-local-disagreement-extends-the-same-law-to-height-seven.md)
- [Every concentrated sharp source in the explicit family admits one actual common law, for all K at least two with uniform margin 107/2700; exact heights five and six close the finite gap](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/418-concentrated-sharp-sources-admit-a-common-law-at-every-height.md)
- [A finite-prefix transport lemma makes the missing-3 and missing-5 source-coordinate maps explicit; exact finite checks pass, while the new source and attachment budgets remain open](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/72-uniform-prefix-transport-and-missing-anchor-interface.md)
- [Exact source-row and attachment-budget audit for selected eight-prime cores missing 3 and/or 5; transport, root orientation and gluing remain open](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/73-missing-anchor-eight-core-source-audit.md)
- [A book of N four-prime pages has full Haar density greater than (67/4000)(3/16)^N, supplying a computable cutoff for arbitrary large-prime constraints joining head pages](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/37-full-density-and-large-prime-continuation-for-spine-books.md)
- [Arbitrarily many four-prime pages sharing the spine {3,5} are noncovering, with a uniform positive measure of common boundary configurations admitting all page extensions](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/36-common-spine-books-of-four-prime-pages.md)
- [One actual block on the first eight odd primes admits arbitrarily many seven-vertex attachments; extendible core configurations have Haar density greater than 1/1200000](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/35-eight-prime-core-with-seven-vertex-attachments.md)
- [Fixed prime graphs with blocks of at most seven vertices have a uniform head-density bound and a computable cutoff for unrestricted large-prime tails, including tail classes joining the whole head](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/34-uniform-head-density-from-thick-block-domains.md)
- [At most seven prime divisors up to 100000, or eight up to 100000000 using the attributed eight-prime density theorem, admit arbitrarily many larger primes without any graph restriction](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md)
- [Six specified root-block heads admit arbitrarily many primes above 10000, with arbitrary original heights and supports; all other graph blocks may have up to seven vertices](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/32-conditional-root-measures-and-unrestricted-prime-tails.md)
- [Every prime-interaction graph with blocks of at most seven vertices is noncovering, with arbitrary total prime count, original heights, and residues](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/31-seven-vertex-block-noncoverage-with-actual-prime-measures.md)
- [Every prime-interaction graph with blocks of at most six vertices is noncovering: transported six-prime prefix measures pay all actual attachments, with arbitrary total prime count and heights](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/30-six-prime-prefix-measures-close-all-six-vertex-blocks.md)
- [Actual conditioned heads admit explicitly bounded sparse prime tails of arbitrary finite size, retaining every mixed support](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/27-sparse-tail-extensions-of-conditioned-heads.md)
- [Literal modulus 5 or 15 absence, or agreement of their residues modulo 5, pays every remaining six-vertex block under the actual pure-class invariant](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/26-literal-pure-classes-and-six-vertex-residue-branches.md)
- [Six-vertex block fees reduce the remaining root-3 cases to fifty explicit prime cores, with arbitrary original heights and residues retained](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/25-six-vertex-block-fees-and-a-finite-prime-core-frontier.md)
- [The unique root reserve and shared descendant budget reduce the fifty six-vertex prime cores to twelve, retaining arbitrary original heights and residues](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/28-unique-root-reserve-and-shared-descendant-budget.md)
- [Outside-root fee savings and actual prime ownership reduce the twelve six-vertex core types to six, preserving original heights and residues](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/29-outside-root-savings-and-prime-ownership.md)
- [Literal prime-power residue conflicts bound queries under the actual conditional survivor law, with dependent digits retained](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/24-laminar-prefix-conflicts-under-actual-conditioning.md)
- [Actual conditional kernels close every five-vertex block and an unbounded large-prime block regime under arbitrary recursive attachments](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/23-conditional-kernels-and-recursive-block-noncoverage.md)
- [Two shared parent layers give fees for exceptional 3,5,11,13,17 and 3,7,11,13,17 blocks with established block descendants](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/22-two-layer-profiles-for-two-further-five-prime-blocks.md)
- [A shared first-root profile gives a fee for one exceptional 3,5,7,11,13 block, with arbitrary established block descendants](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/21-coupled-first-root-profiles-and-an-exceptional-five-prime-block.md)
- [Original AP three-color intersections can exceed the proposed residual threshold: a complete 510-label control](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/20-original-ap-three-color-intersections-can-exceed-the-residual-threshold.md)
- [Five-prime parent envelopes and the limits of scalar prefix budgets](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/19-five-prime-parent-envelopes-and-the-cofactor-allocation-barrier.md)
- [Five-prime cores with singly attached trees or specified cactus graphs: all-height noncoverage and exact weighted extension bounds](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/18-five-prime-cores-with-tree-and-cactus-attachments.md)
- [Two-prime separator kernels: exact gluing, a common-law sufficient criterion, and original-AP probes that recover the joint extension counts](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/17-two-prime-separator-interfaces-and-exact-count-probes.md)
- [Four-vertex blocks and arbitrary cycle blocks: noncoverage from a common descendant budget, retaining all four-prime labels and heights](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/06c-four-vertex-blocks-and-cycle-breaking-vertices.md#four-vertex-blocks-with-a-common-descendant-budget)
- [Every original prime graph with at most one cycle per component is noncovering, at arbitrary heights and residues](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/06-block-saturation-and-the-actual-crossing-budget.md#arbitrary-odd-pseudoforests-are-noncovering)
- [Every original cactus prime graph is noncovering: arbitrarily many cycles joined at articulation primes, with all heights and residues retained](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/06b-arbitrary-odd-cactus-graphs-are-noncovering.md#arbitrary-odd-cactus-graphs-are-noncovering)
- [Current bounds and comparisons](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/01-current-bounds-and-comparisons.md)
- [Actual AP(4,5): layout costs and complete finite-core tails](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/001-064/35-ap45-layout-costs-and-complete-core-tails.md)
- [Original-layout distance forces a Jensen loss](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/001-064/34-original-layout-distance-forces-a-jensen-loss.md)
- [Retained and removed events: the complete convex-cost bound](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/profile-notes/001-064/33-retained-and-removed-original-events-control-convex-costs.md)

## A prime-weighted continuation using RH

Let a finite family have distinct odd moduli greater than one and arbitrary
fixed residues. Write the distinct prime factors of its LCM in increasing
order. Each row gives a sufficient condition for an uncovered integer.
All prime-power heights, including those of the head primes inside mixed
moduli, are unrestricted. The number of prime factors above the indicated
cutoff is unrestricted.

| Cutoff \(B\) | Maximum number of prime factors at most \(B\) | Additional condition |
| ---: | ---: | --- |
| 449 | 7 | Every such family |
| 2543 | 8 | Every such family |
| 8231 | 9 | If the ninth prime is at most \(B\), it is at least 271 |

These are ordinary proofs using the published RH result and the existing
survivor measure constructions. Alpöge's Lean declaration has type
\(\mathrm{RiemannHypothesis}\) without hypotheses. The independent
statement comparison and axiom audit verify that declaration against
Mathlib. The analytic step below only needs ordinary RH.
[Proof declaration](https://github.com/the-omega-institute/riemann-hypothesis/blob/1ef6c4e2e944fb2784ecf3168a84810bf50ca6db/src/Main.lean) ·
[Statement comparison](https://math.mit.edu/~drew/grh/con-leche-compare.log) ·
[Axiom audit](https://math.mit.edu/~drew/grh/audit.log)

### Survivor measures and continuation

Take the actual primes at most \(B\) as the head. Resolve their finite
coordinates at the full heights required by the original family. The
head submeasure avoids the classes supported entirely in the head. Its
mass is at least \(m\), and the integral of the fourth power of every
complete divisor query is at most \(K\). Such a query counts hits against
one fixed residue for each divisor of the head period, including the
unit. Hölder bounds the integral of any product of four queries by the
same \(K\) on this measure. The following source bounds apply, with
unused head coordinates padded when necessary.

| Head | \(m\) | \(K\) | Source |
| --- | ---: | ---: | --- |
| At most seven primes | \(7235955529/450000000000\) | \(82461631627375/127401984\) | [Seven-prime source and fourth moment, HM1–HM6](https://github.com/the-omega-institute/trureturing-experiments/blob/80d407671ff57ec39cec5e7244b2fee1df2059c3/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md) |
| At most eight primes | \(1/33750\) | \(590500\) | [Capped eight-prime source, (1)–(5)](https://github.com/the-omega-institute/trureturing-experiments/blob/80d407671ff57ec39cec5e7244b2fee1df2059c3/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/750-799/779-the-original-capped-source-lowers-the-general-eight-prime-tail-cutoff.md) |
| Nine primes, ninth at least 271 | \(1/2500000\) | \(450000\) | [Nine-prime source, (1)–(5)](https://github.com/the-omega-institute/trureturing-experiments/blob/80d407671ff57ec39cec5e7244b2fee1df2059c3/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/750-799/780-a-ninth-prime-from271-admits-an-unrestricted-larger-tail.md) |

For the last row with at most eight head primes, use the eight-prime
source and the cutoff of 2543. In the nine-prime case the separation
condition is imposed on the actual ninth prime.

Process the larger actual primes in increasing order and charge each
remaining class at its largest prime. For \(t=1/(p-1)\), put
\[
 A(t)=15t+50t^2+60t^3+24t^4,\quad
 c_\delta=\frac{27}{256\delta^3(1-\delta)},\quad
 g_\delta(t)=1+\frac{A(t)}{1-\delta}.
\]
The fourth-moment continuation bounds the absolute loss at a prime by
\(Kc_\delta t^4\), with next fourth-moment allowance \(Kg_\delta(t)\).
It uses the actual forbidden fraction \(\beta(x)\) on the \(p\)-fibre
over each old point \(x\), restricting Haar to the allowed points and
dividing by \(1-\min(\beta(x),\delta)\). The mass loss is thus the integral
of \((\beta-\delta)_+/(1-\delta)\). All old cofactors and phases remain
those of the original classes. At each new exponent, distinctness gives
at most one phase per old divisor. This is the hypothesis used in the
complete-query estimate. The inequalities hold for each \(0<\delta<1\),
so the clipping parameter can be fixed separately for each prime before
processing the family. [Quartic continuation, HM7–HM13](https://github.com/the-omega-institute/trureturing-experiments/blob/80d407671ff57ec39cec5e7244b2fee1df2059c3/docs/reports/erdos7-odd-covering/profile-notes/arithmetic/700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md)

### Every prime above the computation range

Set \(T=200000\) and use \(\delta=2/5\) for \(p>T\). The binomial
coefficients give \(g_{2/5}(t)\le(1+t)^{25}\) for \(t\ge0\).
For \(x\ge T\), the reciprocal prime-product bound gives
\[
 \prod_{T<p\le x}\frac p{p-1}
 \le \frac{243}{241}\frac{\log x}{\log T},
 \qquad 11<\log T<13.
\]
Indeed \(3^{11}<T\) and \((27/10)^{13}>T\). The constant follows by dividing
the upper bound at \(x\) by the lower bound at \(T\) and using
\(\log T>11\). [Rosser–Schoenfeld, Theorem 8](../Library/Arith/rosser1962approximate.md)

With \(\vartheta(x)=\sum_{p\le x}\log p\), write
\(E(x)=\vartheta(x)-x\). Under RH,
\(|E(x)|\le\sqrt{x}(\log x)^2/(8\pi)\) for \(x\ge T\), by weakening
Lee–Nosal's explicit bound. Since \((\log x)^2/\sqrt{x}\) decreases
for \(x\ge T\), \(|E(x)|\le\varepsilon x\) throughout this range, where
\(\varepsilon=169/(24\cdot447)\). [Lee–Nosal, Theorem 1.2(3)](https://arxiv.org/abs/2312.05628)

Let \(f(x)=(\log x)^{24}/x^4\). It is positive and decreasing over
\([T,\infty)\). Partial summation over the primes strictly greater than \(T\)
gives
\[
 \sum_{p>T}\log(p) f(p)
 = \int_T^\infty f(x)\,dx-E(T)f(T)-\int_T^\infty E(x)f'(x)\,dx
 \le (1+\varepsilon)\int_T^\infty f(x)\,dx+2\varepsilon T f(T).
\]
The endpoint at infinity vanishes since \(xf(x)\to0\).
In the prime loss bound use
\((p-1)^{-4}\le (T/(T-1))^4p^{-4}\), then apply the product
bound to all moment multipliers from \(T\) to \(p\).
After dividing out the moment allowance at \(T\), the resulting prime
sum is at most
\[
 R=\frac{5625}{2048}\left(\frac{243}{241}\right)^{25}
       \frac{T}{(T-1)^4}
 \left[
 \frac{1+\varepsilon}{33}
   \sum_{j=0}^{25}\frac{25!}{(25-j)!\,33^j}
   +\frac{2\varepsilon}{11}
 \right].
\]
For the integral, use \(f(x)\le (\log x)^{25}/(11x^4)\) and integrate by
parts repeatedly. The integral of \((\log x)^{25}/x^4\) is
\((\log T)^{25}/(3T^3)\) times the displayed factorial sum with
\(3\log T\) in place of 33. The endpoint term uses
\(T f(T)=(\log T)^{25}/(T^3\log T)\).
These estimates bound the full infinite comparison sum and therefore
every finite choice of original primes above \(T\).

### Exact cutoffs

Put \(S=10^{24}\) and start with \(u=\lceil SR\rceil=44446336\).
Visit every prime in \((B,T]\) in decreasing order. At each such prime
replace \(u\) by
\[
 \min_{\delta\in\{1/4,\,3/10,\,1/3,\,3/8,\,2/5\}}
 \left\lceil Sc_\delta/(p-1)^4+g_\delta(1/(p-1))u\right\rceil .
\]
A minimizing parameter at each step fixes the forward clipping schedule.
The recurrence is an upper bound on the remaining loss per unit of
moment allowance, multiplied by \(S\). Missing any scheduled prime only
decreases this allowance because the loss term is nonnegative and
\(g_\delta\ge1\). All inputs and rounding operations are rational. The
table gives the integer replay values and strict lower bounds for the
final live mass \(m-Ku/S\).

| \(B\) | Primes in \((B,T]\) | Final \(u\) | Final live mass greater than |
| ---: | ---: | ---: | ---: |
| 449 | 17897 | 24477013422083484 | \(1/5000\) |
| 2543 | 17612 | 49669053146940 | \(3/10^7\) |
| 8231 | 16952 | 888884725255 | \(1/10^{12}\) |

Positive live mass gives a point on the finite CRT carrier avoiding
every original class, hence an uncovered integer. In particular, any odd
distinct cover would need at least eight support primes at most 449 and
at least nine at most 2543. If its ninth prime is at least 271, it would
also need a tenth prime at most 8231. Extending these bounds to all
possible small-prime supports requires a stronger survivor estimate
for the head.

### The second-moment threshold at 73

Suppose a probability on the full-height survivors of the head at 73 has
\(\max_L\mathbb E L^2\le139.1\), with the maximum over complete divisor
queries as above. Then the whole original family is noncovering. The
proof tracks the mass lost and the second moment on the same
submeasure. In this scalar continuation, even optimal clipping at each
prime can certify a threshold strictly below \(139.26\) when every
prime above 73 may occur. The known star family at 73 forces a second
moment greater than \(139.59\) for every supported probability.
[Star family](https://github.com/the-omega-institute/trureturing-experiments/blob/80d407671ff57ec39cec5e7244b2fee1df2059c3/docs/reports/erdos7-odd-covering/problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md)

At an intermediate step write \(m\) for the live mass, \(K\) for a bound
on every complete-query second moment, and \(D\) for the actual mass
deleted by the next prime \(p\). Put
\[
 a_p=\frac{3p-1}{(p-1)^2},\qquad b_p=\frac{1}{4(p-1)^2}.
\]
The same restricted kernel gives \(D\le Kb_p/(\delta(1-\delta))\).
This follows from \((y-\delta)_+\le y^2/(4\delta)\), by completing each
old cofactor query and bounding each product by Cauchy–Schwarz. In the
enlarged second moment, the term with both new exponents zero loses at
least \(D\), since the corresponding old complete query contains the
unit term and is everywhere at least one. The other exponent pairs use
the cylinder cap \(p^{-j}/(1-\delta)\) at their maximum depth \(j\).
There are \(2j+1\) such pairs. Thus
\[
 m'=m-D,\qquad K'\le\left(1+\frac{a_p}{1-\delta}\right)K-D.
\]
The loss credit uses the same \(D\) in both bounds. [Second-moment continuation, T1–T6](https://github.com/the-omega-institute/trureturing-experiments/blob/80d407671ff57ec39cec5e7244b2fee1df2059c3/docs/reports/erdos7-odd-covering/problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md)

For a continuation requiring \(m'>vK'\), with \(0\le v<1\), the
preceding step can use the sufficient threshold
\[
 \Phi_p(v)=v+\min_{0<\delta\le1/2}
 \left\{\frac{b_p(1-v)}{\delta}
       +\frac{b_p(1-v)+a_pv}{1-\delta}\right\}
 =v+\left(\sqrt{b_p(1-v)}+\sqrt{b_p(1-v)+a_pv}\right)^2 .
\]
Indeed the worst loss permitted by the scalar bounds is the largest
one, since it reduces \(m'-vK'\) by \((1-v)D\). If that loss
can exhaust the live mass, the scalar bounds already allow zero
survival. The minimizer is
\(\sqrt{b_p(1-v)}/(\sqrt{b_p(1-v)}+\sqrt{b_p(1-v)+a_pv})\).
The formula increases on \(0\le v\le1/4\). The sum of the two
radicands increases there since \(a_p>2b_p\), and their product
has derivative at least \(b_p(a_p-3b_p)/2>0\).
Also \(\Phi_p(v)\ge v\) on \(0\le v<1\), so a missing prime can
be skipped. A scalar threshold that reaches \(1/4\) already
excludes any head with \(m/K\le1/4\).

For primes beyond \(T=5000000\), take \(\delta=1/2\) and use
\(1+2a_p\le(p/(p-1))^6\). Dropping the loss credit gives a
sufficient terminal bound. In the preceding partial summation use
\(f(x)=(\log x)^5/x^2\), \(15<\log T<16\) and
\(\varepsilon=16^2/(24\cdot2236)\). The log bounds follow from
\((11/4)^{15}<T<(27/10)^{16}\) and \(27/10<e<11/4\).
The prime-product and Chebyshev bounds give this terminal threshold
per unit of second moment:
\[
 R_2=\left(\frac{451}{449}\right)^6\frac{T}{(T-1)^2}
 \frac{1}{15}\left[
 (1+\varepsilon)\sum_{j=0}^{5}\frac{5!}{(5-j)!\,15^j}
 +2\varepsilon\right].
\]
The factorial sum comes from integrating \((\log x)^5/x^2\).
The boundary term again accounts for the possible negative error
in \(\vartheta(T)-T\).

Use \(S=10^{24}\) and visit all 348492 primes in \((73,T]\) in
decreasing order. For an integer \(u\), put \(X=S-u\),
\(Y=X+4(3p-1)u\), and \(d=4(p-1)^2\). Then the floor of
\(S\Phi_p(u/S)\) is
\[
 u+\left\lfloor\frac{X+Y+\lfloor\sqrt{4XY}\rfloor}{d}\right\rfloor .
\]
One more than the floor gives a strict upper rounding. The replay
starting from \(\lceil SR_2\rceil=19978401471981184\) and rounding
up at each step ends at \(7187192385814385692968\). Its ratio to
\(S\) is less than \(1/139.1\), so the stated head moment suffices.
Starting from zero and rounding down gives \(7181063643367434956708\),
whose ratio to \(S\) is greater than \(1/139.26\). This replay
bounds the best scalar threshold from below even for a tail that
ends at \(T\), with every prime in \((73,T]\). The upper replay
keeps all values below \(1/4\), which verifies the monotonicity domain
for both comparisons. The star family rules out reaching all heads
by uniformly improving this second-moment continuation alone.

## Necessary small moduli when the least modulus is nine

A distinct odd cover whose least modulus is \(9\) must include at least
one of \(15,21,33\) and at least one of \(15,21,45\). In particular, if
\(15\) and \(21\) are both absent, then \(33\) and \(45\) must both occur.
The proof below only needs the absence of \(3,5,7\) and one of the two
displayed triples. It permits arbitrary original phases, arbitrary
prime-power heights and any finite prime support.

For context, Dai, Li, Li and Yi prove that the least modulus of a
distinct odd cover belongs to \(\{3,5,7,9\}\) and its least common
multiple is divisible by \(45\). Their bound on the least modulus
makes the case \(9\) the largest remaining minimum. The conclusion
here constrains the numerical moduli in that case.
[Dai–Li–Li–Yi, Theorems 1.1 and 1.2](https://arxiv.org/abs/2611.15110v1)

### Comparison with pure powers removed

For each prime \(p\) normalize Haar on the complement of all actual
pure \(p\)-power classes. Let \(b_p=1\) if \(p\in\{3,5,7\}\) and
\(b_p=0\) otherwise. The least permitted pure exponent is at least
\(b_p+1\). The distinct pure labels therefore delete mass at most
\(\sum_{e\ge b_p+1}p^{-e}=p^{-b_p}/(p-1)\).
Write \(d_p=p-1-p^{-b_p}\). In this normalized reference law every
depth-\(e\) cylinder has mass at most \((p-1)p^{-e}/d_p\).

Through prime \(6997\) use the normalized distortion kernel at
clipping parameter \(\delta_p\) relative to that reference measure.
It preserves the earlier marginal, leaves every pure class outside
its support, and charges the actual forbidden mixed union of
reference fraction \(\alpha\) by \((\alpha-\delta_p)_+/(1-\delta_p)\).
The conditional depth-\(e\) cap after distortion is \(c_pp^{-e}\),
where \(c_p=(p-1)/(d_p(1-\delta_p))\). The chosen parameters give
\(0<c_p\le p\). Primes absent in the original period may be padded to
positive height, with no forbidden classes. As in the preceding
proofs, use all actual heights, including digits used only by later
classes. [Distortion and scalar comparison, Lemmas 2.1, 2.4 and Theorem 2.6](https://arxiv.org/abs/2611.15110v1)

For the old coordinates let \(T_q\) be independent comparison
exponents with \(\Pr(T_q\ge e)=c_q q^{-e}\) for \(e\ge1\).
Write \(D=\prod_{q<p}(1+T_q)\), and let \(\sigma=\min(T_3,2)\)
after processing \(3\), with \(\sigma=0\) initially. Let \(E_p\)
be the set of exponents \(a\) such that \(3^a p\) belongs to the
selected absent triple. The two triples are \(\{15,21,33\}\) and
\(\{15,21,45\}\).

Complete the mixed cofactor inventory with one test phase per
eligible numerical cofactor and current exponent. Distinct full
moduli justify this completion at every exponent. The unit cofactor
is excluded because its class is pure. The additional forbidden
labels in \(E_p\) occur at current exponent one, so their weight is
removed there. Under the convex comparison, the completed mixed
weight at prime \(p\) is
\[
 \frac{D-1-r_p(\sigma)}{d_p},\qquad
 r_p(s)=\frac{p-1}{p}\sum_{a\in E_p}\mathbf1_{\{s\ge a\}}.
\]
Indeed the auxiliary cofactors are divisors of \(\prod_{q<p}q^{T_q}\).
Each nonunit cofactor contributes \(\sum_{e\ge1}(p-1)p^{-e}/d_p=1/d_p\).
Each missing cofactor \(3^a\) at current exponent one removes
\((p-1)/(pd_p)\) exactly when \(T_3\ge a\). This comparison uses
nonnegative weights on the permitted labels before evaluating the
positive part, so the subtraction represents absent slots in the
same comparison and the same original family. Put
\(U_p(s)=1+\delta_p d_p+r_p(s)\). The actual stage loss is at most
\[
 \frac{\mathbb E(D-U_p(\sigma))_+}{d_p(1-\delta_p)} .
\]
For every complete divisor query, the same comparison applied to
the square bounds its second moment at the end of the prefix by
\[
 K=\prod_{3\le p\le6997,\ p\ {\rm prime}}
       \left(1+c_p\frac{3p-1}{(p-1)^2}\right).
\]
All these estimates hold on the same distortion law. Restrict it
once to the event that survives every stage through \(6997\).
The restricted measure has mass at least one minus the sum of
stage losses, and its second moment is still bounded by \(K\).

### Exact prefix calculation and infinite continuation

Use the following \(\delta_p\) in hundredths. The first row lists
inclusive upper endpoints, with each interval starting just above
the previous endpoint.

| Upper endpoint | 3 | 5 | 7 | 11 | 13 | 17 | 19 | 23 | 29 | 31 | 37 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| \(100\delta_p\) | 0 | 0 | 0 | 12 | 18 | 20 | 18 | 24 | 26 | 24 | 20 |

| Upper endpoint | 41 | 43 | 47 | 53 | 101 | 211 | 419 | 839 | 1679 | 3359 | 6997 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| \(100\delta_p\) | 28 | 26 | 26 | 28 | 28 | 30 | 30 | 30 | 30 | 28 | 26 |

Keep all states \((j,s)\) with \(1\le j\le1850\) and \(0\le s\le2\),
using \(S=10^{24}\) and upper integer values for
\(S\Pr(D=j,\sigma=s)\). Start with mass \(S\) at \((1,0)\).
At a prime \(p\), each multiplier \(i=1+T_p\) maps \(j\) to \(ij\).
At \(3\) set \(s\) to \(\min(i-1,2)\). At other primes retain \(s\).
Multiply the stored integers by the ceilings of
\(S\Pr(1+T_p=i)\), sum by destination, divide by \(S\), and round each
state upward. The multiplier masses at \(i=1\) and \(i\ge2\) are
\(1-c_p/p\) and \(c_p(p-1)/p^i\), respectively. Larger states cannot
return to the retained range because every multiplier is at least one.

Independently carry upper bounds for the full mean of \(D\) and its
second moment, starting each at \(S\). The update factors are
\(1+c_p/(p-1)\) and \(1+c_p(3p-1)/(p-1)^2\), with rounding upward.
Before each update, use the exact loss numerator
\[
 \mathbb E(D-U_p(\sigma))_+
 =\mathbb E D-\mathbb E U_p(\sigma)
   +\sum_{j,s}(U_p(s)-j)_+\Pr(D=j,\sigma=s).
\]
Every positive term in the sum is retained. The expectation of
\(U_p(\sigma)\) uses the exact probabilities
\(\Pr(T_3\ge a)=6/(5\cdot3^a)\) for the only nonzero \(E_p\), because
\(\delta_3=0\) and \(c_3=6/5\). Thus all terms replaced by upper bounds
have nonnegative coefficients. Round each stage loss up at scale \(S\)
before summing.

Apply the preceding second-moment continuation to the restricted
measure at \(6997\), using RH for the infinite remainder. Its same
upper replay, starting at \(5000000\) and stopping before processing
\(6997\) in decreasing order, gives
\[
 v=\frac{27144070771294538066}{S}.
\]
The finite prefix passes if its remaining mass is greater than \(Kv\).
The following table gives the exact scaled integers for the prefix
bounds and the resulting strict mass margin.

| Absent moduli in addition to \(3,5,7\) | \(S\) times the sum of loss bounds | \(S\) times the moment bound | Remaining mass minus \(Kv\), greater than |
| --- | ---: | ---: | ---: |
| \(15,21,33\) | 938773600338587870460242 | 1908984849362909824839827392 | \(9/1000\) |
| \(15,21,45\) | 935988366744625136574530 | 1908984849362909824839827392 | \(12/1000\) |

Every later class is processed by the standard continuation, including
pure powers of larger primes. The final positive live mass gives an
integer outside the original classes by CRT. This rules out the two
missing-label patterns while leaving open the case with least modulus
\(9\) and either \(15\) or \(21\), and the case with both \(33\) and
\(45\) and neither \(15\) nor \(21\).

## Motivation

[Read this section](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/02-current-bounds-and-comparisons.md#motivation).

- <a id="independent-finite-lcm-exclusion-through-11486474"></a>[Independent finite lcm exclusion through 11486474](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/02-current-bounds-and-comparisons.md#independent-finite-lcm-exclusion-through-11486474)
- <a id="reuse-of-the-5040-and-divisor-sum-work"></a>[Reuse of the 5040 and divisor-sum work](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/02-current-bounds-and-comparisons.md#reuse-of-the-5040-and-divisor-sum-work)
- <a id="unrestricted-tails-from-the-5040-odd-heads"></a>[Unrestricted tails from the 5040 odd heads](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/02-current-bounds-and-comparisons.md#unrestricted-tails-from-the-5040-odd-heads)
- <a id="adaptive-kernels-lower-the-unrestricted-cutoff-to-19"></a>[Adaptive kernels lower the unrestricted cutoff to 19](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/03-adaptive-kernels-lower-the-unrestricted-cutoff-to-19.md#adaptive-kernels-lower-the-unrestricted-cutoff-to-19)
- <a id="homogeneous-cylinder-capacities-and-the-extremal-comb"></a>[Homogeneous cylinder capacities and the extremal comb](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/03-adaptive-kernels-lower-the-unrestricted-cutoff-to-19.md#homogeneous-cylinder-capacities-and-the-extremal-comb)
- <a id="sharp-tail-profiles-of-maximal-cylinder-caps"></a>[Sharp tail profiles of maximal cylinder caps](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/03-adaptive-kernels-lower-the-unrestricted-cutoff-to-19.md#sharp-tail-profiles-of-maximal-cylinder-caps)

## Gap

[Read this section](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/03-adaptive-kernels-lower-the-unrestricted-cutoff-to-19.md#gap).


## Route

[Read this section](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/03-adaptive-kernels-lower-the-unrestricted-cutoff-to-19.md#route).

- <a id="a-complete-star-family-refutes-the-unrestricted-gamma-73-bound"></a>[A complete star family refutes the unrestricted Gamma-73 bound](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md#a-complete-star-family-refutes-the-unrestricted-gamma-73-bound)
- <a id="the-actual-complete-forbidden-assignment"></a>[The actual complete forbidden assignment](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md#the-actual-complete-forbidden-assignment)
- <a id="a-constant-potential-coordinate-distribution"></a>[A constant-potential coordinate distribution](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md#a-constant-potential-coordinate-distribution)
- <a id="an-exact-depth-eight-lower-certificate"></a>[An exact depth-eight lower certificate](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md#an-exact-depth-eight-lower-certificate)
- <a id="two-legal-complete-layout-distributions"></a>[Two legal complete-layout distributions](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md#two-legal-complete-layout-distributions)
- <a id="a-pointwise-dual-bound-for-every-survivor-probability"></a>[A pointwise dual bound for every survivor probability](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md#a-pointwise-dual-bound-for-every-survivor-probability)
- <a id="verification-scope"></a>[Verification scope](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md#verification-scope)
- <a id="irredundancy-does-not-repair-the-universal-head-target"></a>[Irredundancy does not repair the universal head target](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md#irredundancy-does-not-repair-the-universal-head-target)
- <a id="complete-star-heads-cannot-be-completed-by-arbitrary-odd-tails"></a>[Complete star heads cannot be completed by arbitrary odd tails](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md#complete-star-heads-cannot-be-completed-by-arbitrary-odd-tails)
- <a id="one-actual-head-law-at-every-positive-height"></a>[One actual head law at every positive height](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md#one-actual-head-law-at-every-positive-height)
- <a id="normalized-tail-kernels-preserve-the-original-labels"></a>[Normalized tail kernels preserve the original labels](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md#normalized-tail-kernels-preserve-the-original-labels)
- <a id="a-simultaneous-complete-layout-moment-under-the-same-law"></a>[A simultaneous complete-layout moment under the same law](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md#a-simultaneous-complete-layout-moment-under-the-same-law)
- <a id="exact-positive-part-certificate-and-the-bbmst-stop"></a>[Exact positive-part certificate and the BBMST stop](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md#exact-positive-part-certificate-and-the-bbmst-stop)
- <a id="arbitrary-cross-point-1113-heads-and-full-height-continuation"></a>[Arbitrary cross-point 11/13 heads and full-height continuation](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md#arbitrary-cross-point-1113-heads-and-full-height-continuation)
- <a id="unrestricted-axis-deletions-a-complete-head-bound"></a>[Unrestricted axis deletions: a complete head bound](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/05-unrestricted-axis-deletions-a-complete-head-bound.md#unrestricted-axis-deletions-a-complete-head-bound)
- <a id="a-continuation-criterion-for-an-arbitrary-correlated-head"></a>[A continuation criterion for an arbitrary correlated head](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/05-unrestricted-axis-deletions-a-complete-head-bound.md#a-continuation-criterion-for-an-arbitrary-correlated-head)
- <a id="block-saturation-and-the-actual-crossing-budget"></a>[Block saturation and the actual crossing budget](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/06-block-saturation-and-the-actual-crossing-budget.md#block-saturation-and-the-actual-crossing-budget)
- <a id="moment-bounds-preserve-the-original-labels"></a>[Moment bounds preserve the original labels](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/06-block-saturation-and-the-actual-crossing-budget.md#moment-bounds-preserve-the-original-labels)
- <a id="arbitrary-three-prime-heads-with-sparse-tail-interactions"></a>[Arbitrary three-prime heads with sparse tail interactions](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/06-block-saturation-and-the-actual-crossing-budget.md#arbitrary-three-prime-heads-with-sparse-tail-interactions)
- <a id="every-positive-height-star-head-admits-the-required-broad-law"></a>[Every positive-height star head admits the required broad law](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/06-block-saturation-and-the-actual-crossing-budget.md#every-positive-height-star-head-admits-the-required-broad-law)
- <a id="matching-tails-cannot-complete-a-star"></a>[Matching tails cannot complete a star](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/06-block-saturation-and-the-actual-crossing-budget.md#matching-tails-cannot-complete-a-star)
- <a id="star-forests-arbitrarily-many-centres-of-unbounded-degree"></a>[Star forests: arbitrarily many centres of unbounded degree](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/06-block-saturation-and-the-actual-crossing-budget.md#star-forests-arbitrarily-many-centres-of-unbounded-degree)
- <a id="arbitrary-forests-a-bound-independent-of-depth-and-degree"></a>[Arbitrary forests: a bound independent of depth and degree](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/06-block-saturation-and-the-actual-crossing-budget.md#arbitrary-forests-a-bound-independent-of-depth-and-degree)
- <a id="a-bounded-number-of-cycle-breaking-vertices-in-each-component"></a>[A bounded number of cycle-breaking vertices in each component](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/06c-four-vertex-blocks-and-cycle-breaking-vertices.md#a-bounded-number-of-cycle-breaking-vertices-in-each-component)
- <a id="ordered-local-kernels-unbounded-feedback-sets-and-treewidth"></a>[Ordered local kernels: unbounded feedback sets and treewidth](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md#ordered-local-kernels-unbounded-feedback-sets-and-treewidth)
- <a id="bounded-tail-support-permits-arbitrary-co-occurrence-graphs"></a>[Bounded tail support permits arbitrary co-occurrence graphs](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md#bounded-tail-support-permits-arbitrary-co-occurrence-graphs)
- <a id="the-support-restriction-is-needed-only-below-a-finite-largest-prime"></a>[The support restriction is needed only below a finite largest prime](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md#the-support-restriction-is-needed-only-below-a-finite-largest-prime)
- <a id="why-scalar-deletion-and-unrestricted-message-energy-do-not-suffice"></a>[Why scalar deletion and unrestricted message energy do not suffice](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md#why-scalar-deletion-and-unrestricted-message-energy-do-not-suffice)
- <a id="a-degree-two-core-with-arbitrarily-many-pendant-leaves"></a>[A degree-two core with arbitrarily many pendant leaves](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md#a-degree-two-core-with-arbitrarily-many-pendant-leaves)
- <a id="absorbing-a-finite-set-of-hub-primes"></a>[Absorbing a finite set of hub primes](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md#absorbing-a-finite-set-of-hub-primes)
- <a id="every-full-star-completion-needs-positive-mixed-tail-capacity"></a>[Every full star completion needs positive mixed-tail capacity](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md#every-full-star-completion-needs-positive-mixed-tail-capacity)
- <a id="exact-constants-and-the-remaining-unrestricted-obligation"></a>[Exact constants and the remaining unrestricted obligation](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md#exact-constants-and-the-remaining-unrestricted-obligation)
- <a id="arbitrary-head-transfer-by-the-joint-load-invariant"></a>[Arbitrary-head transfer by the joint-load invariant](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md#arbitrary-head-transfer-by-the-joint-load-invariant)
- <a id="exact-feasibility-of-a-complete-survivor-kernel-with-cylinder-caps"></a>[Exact feasibility of a complete-survivor kernel with cylinder caps](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md#exact-feasibility-of-a-complete-survivor-kernel-with-cylinder-caps)
- <a id="transfer-retaining-the-actual-forbidden-fibre-geometry"></a>[Transfer retaining the actual forbidden-fibre geometry](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md#transfer-retaining-the-actual-forbidden-fibre-geometry)
- <a id="forced-loss-on-an-actual-pure-prime-forbidden-root"></a>[Forced loss on an actual pure-prime forbidden root](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md#forced-loss-on-an-actual-pure-prime-forbidden-root)
- <a id="sharpness-of-the-cofactor-lower-bound"></a>[Sharpness of the cofactor lower bound](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md#sharpness-of-the-cofactor-lower-bound)
- <a id="comparison-with-the-current-head-estimates"></a>[Comparison with the current head estimates](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md#comparison-with-the-current-head-estimates)
- <a id="why-this-does-not-automatically-improve-the-pure-survivor-base"></a>[Why this does not automatically improve the pure-survivor base](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md#why-this-does-not-automatically-improve-the-pure-survivor-base)
- <a id="actual-forbidden-class-projection-and-its-open-quantitative-input"></a>[Actual forbidden-class projection and its open quantitative input](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md#actual-forbidden-class-projection-and-its-open-quantitative-input)
- <a id="exact-saturation-despite-actual-mixed-deletion"></a>[Exact saturation despite actual mixed deletion](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md#exact-saturation-despite-actual-mixed-deletion)
- <a id="verification"></a>[Verification](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md#verification)
- <a id="literature-boundary"></a>[Literature boundary](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md#literature-boundary)
- <a id="exact-continuation-from-the-conditional-73-head-seed"></a>[Exact continuation from the conditional 73-head seed](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md#exact-continuation-from-the-conditional-73-head-seed)
- <a id="quantitative-extension-of-the-old-prime-powers"></a>[Quantitative extension of the old prime powers](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/09-quantitative-extension-of-the-old-prime-powers.md#quantitative-extension-of-the-old-prime-powers)
- <a id="one-stage-smoothing-of-the-height-lift"></a>[One-stage smoothing of the height lift](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/09-quantitative-extension-of-the-old-prime-powers.md#one-stage-smoothing-of-the-height-lift)
- <a id="a-four-prime-head-and-a-restricted-noncoverage-theorem"></a>[A four-prime head and a restricted noncoverage theorem](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/10-a-four-prime-head-and-a-restricted-noncoverage-theorem.md#a-four-prime-head-and-a-restricted-noncoverage-theorem)
- <a id="an-actual-layout-improvement-from-incompatible-ternary-roots"></a>[An actual-layout improvement from incompatible ternary roots](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/11-current-bounds-and-comparisons.md#an-actual-layout-improvement-from-incompatible-ternary-roots)
- <a id="coupling-the-shared-zero-exponent-layout"></a>[Coupling the shared zero-exponent layout](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/12-coupling-the-shared-zero-exponent-layout.md#coupling-the-shared-zero-exponent-layout)
- <a id="the-shared-zero-exponent-envelope-for-arbitrary-outside-prime"></a>[The shared zero-exponent envelope for arbitrary outside prime](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/12-coupling-the-shared-zero-exponent-layout.md#the-shared-zero-exponent-envelope-for-arbitrary-outside-prime)
- <a id="proof-of-the-envelope"></a>[Proof of the envelope](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/12-coupling-the-shared-zero-exponent-layout.md#proof-of-the-envelope)
- <a id="transporting-actual-layouts-through-outside-lcm-blocks"></a>[Transporting actual layouts through outside lcm blocks](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/12-coupling-the-shared-zero-exponent-layout.md#transporting-actual-layouts-through-outside-lcm-blocks)
- <a id="intermediate-four-prime-bound-from-shared-survivor-densities"></a>[Intermediate four-prime bound from shared survivor densities](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/12-coupling-the-shared-zero-exponent-layout.md#intermediate-four-prime-bound-from-shared-survivor-densities)
- <a id="one-common-product-law"></a>[One common product law](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/12-coupling-the-shared-zero-exponent-layout.md#one-common-product-law)
- <a id="five-strictly-improved-independent-projection-coefficients"></a>[Five strictly improved independent projection coefficients](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/12-coupling-the-shared-zero-exponent-layout.md#five-strictly-improved-independent-projection-coefficients)
- <a id="retaining-v35-in-the-compatible-layout-transfer"></a>[Retaining v35 in the compatible-layout transfer](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/12-coupling-the-shared-zero-exponent-layout.md#retaining-v35-in-the-compatible-layout-transfer)
- <a id="exact-e70-profile-sum-and-six-inequalities"></a>[Exact e7=0 profile sum and six inequalities](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/12-coupling-the-shared-zero-exponent-layout.md#exact-e70-profile-sum-and-six-inequalities)
- <a id="exact-verification-and-continuation"></a>[Exact verification and continuation](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/12-coupling-the-shared-zero-exponent-layout.md#exact-verification-and-continuation)
- <a id="shared-cofactor-refinement-of-the-four-prime-head-p2"></a>[Shared-cofactor refinement of the four-prime head (P2)](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/12-coupling-the-shared-zero-exponent-layout.md#shared-cofactor-refinement-of-the-four-prime-head-p2)
- <a id="a-positive-atomic-representation-of-the-extremal-three-prime-densities"></a>[A positive atomic representation of the extremal three-prime densities](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/13-a-positive-atomic-representation-of-the-extremal-three-prime-densities.md#a-positive-atomic-representation-of-the-extremal-three-prime-densities)
- <a id="nonuniform-two-root-survivor-laws"></a>[Nonuniform two-root survivor laws](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/13-a-positive-atomic-representation-of-the-extremal-three-prime-densities.md#nonuniform-two-root-survivor-laws)
- <a id="complete-survivor-parameters-and-positivity"></a>[Complete-survivor parameters and positivity](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/13-a-positive-atomic-representation-of-the-extremal-three-prime-densities.md#complete-survivor-parameters-and-positivity)
- <a id="weighted-layout-and-cylinder-inequalities"></a>[Weighted layout and cylinder inequalities](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/13-a-positive-atomic-representation-of-the-extremal-three-prime-densities.md#weighted-layout-and-cylinder-inequalities)
- <a id="explicit-balanced-law-and-full-continuous-domain-certificate"></a>[Explicit balanced law and full continuous-domain certificate](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/13-a-positive-atomic-representation-of-the-extremal-three-prime-densities.md#explicit-balanced-law-and-full-continuous-domain-certificate)
- <a id="uniform-fallback-preserving-the-r-bound"></a>[Uniform fallback preserving the R bound](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/13-a-positive-atomic-representation-of-the-extremal-three-prime-densities.md#uniform-fallback-preserving-the-r-bound)
- <a id="coherent-propagation-to-three-primes-and-its-limitation"></a>[Coherent propagation to three primes and its limitation](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/13-a-positive-atomic-representation-of-the-extremal-three-prime-densities.md#coherent-propagation-to-three-primes-and-its-limitation)
- <a id="search-result-and-reuse-boundary"></a>[Search result and reuse boundary](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/13-a-positive-atomic-representation-of-the-extremal-three-prime-densities.md#search-result-and-reuse-boundary)
- <a id="a-universal-nonuniform-law-below-the-sharp-uniform-bound"></a>[A universal nonuniform law below the sharp uniform bound](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/13-a-positive-atomic-representation-of-the-extremal-three-prime-densities.md#a-universal-nonuniform-law-below-the-sharp-uniform-bound)
- <a id="actual-parameters-and-the-law"></a>[Actual parameters and the law](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/13-a-positive-atomic-representation-of-the-extremal-three-prime-densities.md#actual-parameters-and-the-law)
- <a id="preserving-the-zero-exponent-layout"></a>[Preserving the zero-exponent layout](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/13-a-positive-atomic-representation-of-the-extremal-three-prime-densities.md#preserving-the-zero-exponent-layout)
- <a id="the-adaptive-rule-and-its-exact-certificate"></a>[The adaptive rule and its exact certificate](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/13-a-positive-atomic-representation-of-the-extremal-three-prime-densities.md#the-adaptive-rule-and-its-exact-certificate)
- <a id="downstream-use-and-boundary"></a>[Downstream use and boundary](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/13-a-positive-atomic-representation-of-the-extremal-three-prime-densities.md#downstream-use-and-boundary)
- <a id="a-shared-parameter-improvement-for-arbitrary-three-prime-heights"></a>[A shared-parameter improvement for arbitrary three-prime heights](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/14-a-shared-parameter-improvement-for-arbitrary-three-prime-heights.md#a-shared-parameter-improvement-for-arbitrary-three-prime-heights)
- <a id="signed-deletion-with-both-initial-ternary-test-prefixes"></a>[Signed deletion with both initial ternary test prefixes](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/14-a-shared-parameter-improvement-for-arbitrary-three-prime-heights.md#signed-deletion-with-both-initial-ternary-test-prefixes)
- <a id="a-uniform-survivor-obstruction-and-sharpness-at-two-primes"></a>[A uniform-survivor obstruction and sharpness at two primes](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/14-a-shared-parameter-improvement-for-arbitrary-three-prime-heights.md#a-uniform-survivor-obstruction-and-sharpness-at-two-primes)
- <a id="geometry-for-every-finite-height"></a>[Geometry for every finite height](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/14-a-shared-parameter-improvement-for-arbitrary-three-prime-heights.md#geometry-for-every-finite-height)
- <a id="one-whole-test-layout-and-its-exact-integral"></a>[One whole test layout and its exact integral](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/14-a-shared-parameter-improvement-for-arbitrary-three-prime-heights.md#one-whole-test-layout-and-its-exact-integral)
- <a id="strict-monotonicity-exact-positive-numerators"></a>[Strict monotonicity: exact positive numerators](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/14-a-shared-parameter-improvement-for-arbitrary-three-prime-heights.md#strict-monotonicity-exact-positive-numerators)
- <a id="limit-and-sharpness-of-the-uniform-two-prime-constant"></a>[Limit and sharpness of the uniform two-prime constant](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/14-a-shared-parameter-improvement-for-arbitrary-three-prime-heights.md#limit-and-sharpness-of-the-uniform-two-prime-constant)
- <a id="scope-of-the-conclusion"></a>[Scope of the conclusion](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/14-a-shared-parameter-improvement-for-arbitrary-three-prime-heights.md#scope-of-the-conclusion)
- <a id="a-nonuniform-law-for-the-rectangular-obstruction-family"></a>[A nonuniform law for the rectangular obstruction family](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/14-a-shared-parameter-improvement-for-arbitrary-three-prime-heights.md#a-nonuniform-law-for-the-rectangular-obstruction-family)
- <a id="exact-tensorization-for-two-fixed-depth-two-tree-shapes"></a>[Exact tensorization for two fixed depth-two tree shapes](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/15-exact-tensorization-for-two-fixed-depth-two-tree-shapes.md#exact-tensorization-for-two-fixed-depth-two-tree-shapes)
- <a id="coherent-constant-potential-does-not-bound-actual-gamma"></a>[Coherent constant potential does not bound actual Gamma](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/15-exact-tensorization-for-two-fixed-depth-two-tree-shapes.md#coherent-constant-potential-does-not-bound-actual-gamma)
- <a id="the-boundary-of-scalar-fibre-reweighting"></a>[The boundary of scalar fibre reweighting](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/15-exact-tensorization-for-two-fixed-depth-two-tree-shapes.md#the-boundary-of-scalar-fibre-reweighting)
- <a id="1-the-scalar-certificate-and-its-optimal-weight"></a>[1. The scalar certificate and its optimal weight](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/15-exact-tensorization-for-two-fixed-depth-two-tree-shapes.md#1-the-scalar-certificate-and-its-optimal-weight)
- <a id="2-sharp-bounded-second-moment-loss-and-optimized-t6"></a>[2. Sharp bounded second-moment loss and optimized T6](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/15-exact-tensorization-for-two-fixed-depth-two-tree-shapes.md#2-sharp-bounded-second-moment-loss-and-optimized-t6)
- <a id="3-hard-fibre-trimming-is-dominated"></a>[3. Hard fibre trimming is dominated](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/15-exact-tensorization-for-two-fixed-depth-two-tree-shapes.md#3-hard-fibre-trimming-is-dominated)
- <a id="4-concrete-obstruction-to-scalar-capacity-closure"></a>[4. Concrete obstruction to scalar capacity closure](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/15-exact-tensorization-for-two-fixed-depth-two-tree-shapes.md#4-concrete-obstruction-to-scalar-capacity-closure)
- <a id="5-consequence-at-the-current-four-prime-seed"></a>[5. Consequence at the current four-prime seed](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/15-exact-tensorization-for-two-fixed-depth-two-tree-shapes.md#5-consequence-at-the-current-four-prime-seed)
- <a id="random-tail-extensions-give-pointwise-layout-certificates"></a>[Random tail extensions give pointwise layout certificates](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/15-exact-tensorization-for-two-fixed-depth-two-tree-shapes.md#random-tail-extensions-give-pointwise-layout-certificates)
- <a id="a-random-extension-of-an-arbitrary-complete-layout"></a>[A random extension of an arbitrary complete layout](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/15-exact-tensorization-for-two-fixed-depth-two-tree-shapes.md#a-random-extension-of-an-arbitrary-complete-layout)
- <a id="exact-center-probabilities-on-a-pure-survivor-tree"></a>[Exact center probabilities on a pure survivor tree](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/15-exact-tensorization-for-two-fixed-depth-two-tree-shapes.md#exact-center-probabilities-on-a-pure-survivor-tree)
- <a id="combining-the-core-and-outside-potentials"></a>[Combining the core and outside potentials](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/15-exact-tensorization-for-two-fixed-depth-two-tree-shapes.md#combining-the-core-and-outside-potentials)
- <a id="the-fixed-rational-certificate"></a>[The fixed rational certificate](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/15-exact-tensorization-for-two-fixed-depth-two-tree-shapes.md#the-fixed-rational-certificate)
- <a id="canonical-conflict-resampling-and-the-exact-shearer-query-ratio"></a>[Canonical conflict resampling and the exact Shearer query ratio](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md#canonical-conflict-resampling-and-the-exact-shearer-query-ratio)
- <a id="structural-hypotheses"></a>[Structural hypotheses](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md#structural-hypotheses)
- <a id="rare-query-proof-of-1"></a>[Rare-query proof of (1)](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md#rare-query-proof-of-1)
- <a id="one-univariate-ray-checks-every-induced-subgraph"></a>[One univariate ray checks every induced subgraph](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md#one-univariate-ray-checks-every-induced-subgraph)
- <a id="congruence-and-complete-layout-specialization"></a>[Congruence and complete-layout specialization](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md#congruence-and-complete-layout-specialization)
- <a id="the-star-family-also-defeats-a-universal-conflict-shearer-head-criterion"></a>[The star family also defeats a universal conflict-Shearer head criterion](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md#the-star-family-also-defeats-a-universal-conflict-shearer-head-criterion)
- <a id="exact-public-source-locators"></a>[Exact public source locators](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md#exact-public-source-locators)

## Falsifier

[Read this section](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md#falsifier).


## Evidence

[Read this section](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md#evidence).


## Triage

[Read this section](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md#triage).


## ASSUMED-UNVERIFIED

[Read this section](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md#assumed-unverified).
