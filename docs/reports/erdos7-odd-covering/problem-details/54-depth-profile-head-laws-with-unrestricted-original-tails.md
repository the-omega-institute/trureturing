# 54. Depth profiles for fixed head laws and unrestricted original tails

The original unrestricted distinct odd-modulus covering problem remains open.
This result fixes the 154 original head congruences in
[the literal table in Chapter 04c](04c-full-history-capped-laws-and-exact-global-optimization.md#7-a-complete-survivor-count-obstruction-defeats-every-fixed-order) and allows arbitrary additional distinct odd
moduli whose largest prime factor exceeds 73. Neither their prime support nor
their exponents, including exponents in their small-prime cofactors, are
bounded. Under the conditional comparison and BBMST continuation inputs used
by [Chapter 04b](04b-arbitrary-star-head-residues-with-unrestricted-tails.md) and
[Chapter 04, (US1)–(US12)](04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md),
the resulting finite family does not cover. The cutoff corollary below also
allows additional 73-smooth head moduli containing a prime sixth power.

The head is fixed literally; this is not a universal assertion for arbitrary
residues or arbitrary collections of 73-smooth head moduli. Removing any of
these head congruences preserves this noncoverage consequence. Additional 73-smooth head congruences with every prime exponent at most five
remain outside the statement.

The new interface is ordinary mathematics with exact rational computation.
It introduces no Lean theorem. The row problem is a standard laminar-capacity
linear program/min-cost flow; the application, compressed original-label
optimizer and these particular profile constants are a repository derivation.
No priority or novelty claim is made for the underlying optimization method.

## Original source, state and full conditional law

The head primes, in their fixed numerical processing order, are

    3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73.

The actual head heights are

    5,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1.

Each congruence keeps its original numerical modulus, literal residue, ID and
all its prime-power requirements. At an inter-coordinate Bellman state,
retain the next axis and all original IDs whose already exposed requirements
match. If any such label has no remaining requirements, its forbidden event
has occurred. Otherwise the remaining union indicator depends on exactly
these IDs and their original remaining requirements.

This is a memoization key for the head-union objective with its fixed profiles,
not permission to discard actual sampled coordinates. Two prefixes with the
same key may give different later cofactor responses. The actual joint law
still lives on full coordinate tuples, and subsequent tail kernels receive
the full prefix. Exact future-tail optimization would require retaining those
additional target requirements. The tail kernels retain the full prefix and
satisfy their conditional caps there; the consumer bounds aggregate expected
tail charges and layout moments under the resulting common actual law.

At every full preceding-coordinate prefix, the next coordinate row must obey
absolute cylinder-mass caps

    sum_(x congruent a modulo p^e) mu_p(x | full earlier prefix) <= r_(p,e).

These are not probabilities conditional on a parent p-adic cylinder. Caps are
deterministic and the order is fixed before sampling. Null-prefix rows may be
filled with the uniform row. Actual head coordinates need not be independent.
The arithmetic input, policy information availability and chosen processing
order are separate structures; this order is not a physical causality claim.

## Why the row optimizer must retain ancestors

For a node u at depth e let F_u(t) be the least downstream expected cost of
placing mass t in its descendants subject to all descendant capacities. At a
leaf it is a linear segment of length r_H and slope equal to that leaf's
continuation value. At a parent, merge the children's nondecreasing marginal
cost segments and retain the cheapest total mass up to r_e. Stable ordering
among equal slopes preserves each child's segment prefix. This realizes the
infimal convolution of the child costs and gives a feasible optimal row.
At the root the required mass is 1; r_e >= p^(-e) supplies uniform feasibility.

A complete constant-cost subtree at depth d has capacity

    c_d = min_(d<=j<=H) p^(j-d) r_j.

Summing depth-j capacities proves the upper bound; uniform mass on the actual
subtree proves attainment. It can therefore be represented by one slope
segment, retaining its location under the original ancestors. At each actual
parent, homogeneous missing children may be pooled after accounting for their
individual subtree capacities. This does not permit pooling across distinct
ancestors before those ancestors have imposed their caps.

For example, for a ternary depth-two row with r=(1,1/3,1/3), nine leaf costs
have three zeros and six ones. Concentrating the zero leaves in one depth-one
cylinder gives minimum 2/3. Distributing one zero under each depth-one cylinder
gives minimum 0. Thus identical cost histograms do not retain the optimization
problem. This is an abstract row example, not a new congruence counterexample.

Backward application of these row minima is exact: each permitted conditional
row can be pasted at each full prefix, and the actual fixed-label terminal
payoff is used. The finite rational segment construction supplies an actual
joint law. The flat profile r_e=min(1,p^(H-e)/k) reproduces exactly the old
average-of-k-cheapest-leaves operator; all its proper-cylinder constraints
already follow from the leaf cap. New profiles can change the feasible law.

## One rational profile and the achieved head mass

In the following table r_0=1 and each row lists r_1 through r_H.

| p | Profile |
|---|---|
| 3 | 283/440, 27/121, 9/121, 3/121, 1/110 |
| 5 | 163/504, 11/126, 11/630 |
| 7 | 49/229, 7/229, 1/229 |
| 11 | 121/970, 121/9700 |
| 13 | 143/1410, 11/1410 |
| 17 | 17/230, 1/230 |
| 19 | 19/321, 11/3210 |
| 23 | 11/210 |
| 29 | 11/270 |
| 31 | 11/290 |
| 37 | 1/35 |
| 41 | 1/39 |
| 43 | 1/41 |
| 47 | 1/45 |
| 53 | 1/51 |
| 59 | 1/57 |
| 61 | 1/59 |
| 67 | 1/65 |
| 71 | 1/69 |
| 73 | 1/71 |

For the fixed original 154 labels, exact Bellman evaluation gives

    epsilon = 850282109320449012581343404003218456990123
              /2126237451649555718697975632038158000000000
            = 0.3998998835528891... .

This is the actual forbidden-head mass of the constructed full-prefix law,
not a sum of independently attainable stage optima or a rearranged label
family. The same leaf IDs and all original phases are used throughout.

## Uniform extension to arbitrary later cofactor heights

Let H_p be the listed head height and let H'_p>=H_p resolve the entire enlarged
family, including all later cofactors. After generating the coarse joint law,
append independent uniform extra p-adic digits to each coordinate:

    X_p = x_p + p^(H_p) U_p,
    U_p uniform on {0,...,p^(H'_p-H_p)-1}.

The extra digits are independent of the entire coarse law. Conditioning on
the preceding full coordinates reveals their coarse coordinates and extra
independent digits, so it leaves the next coarse conditional row unchanged.
For e<=H_p its caps are unchanged; for H_p<e<=H'_p the cap is

    r_(p,e) = r_(p,H_p) p^(H_p-e).

The head union depends only on the old coordinates, so epsilon is unchanged.
This constructs a single actual full-height law for every finite enlarged
family; it never truncates an original cofactor requirement.

The infinite auxiliary height law with these extended tails dominates every
finite lifted auxiliary height. Its moment factors are

    E(1+K_p) = 1 + sum_(e=1..H_p) r_(p,e) + r_(p,H_p)/(p-1),

    E[(1+K_p)^2] = 1 + sum_(e=1..H_p)(2e+1) r_(p,e)
                  + r_(p,H_p)[(2H_p+1)/(p-1) + 2p/(p-1)^2].

These additional terms are charged in the certificate below. Merely reusing
finite-height moments would not justify the unrestricted-cofactor statement.

## Recomputed common-law continuation budget

For every tail prime q>73 use the existing normalized conditional kernel with
delta=2/5. Its auxiliary tails are

    Pr(K_q>=e)=c_q q^(-e),  c_q=5(q-1)/(3(q-2)), e>=1.

Every original mixed label d*q^e retains its actual cofactor cylinder; for
each fixed d, distinct numerical moduli give sum_e (q-1)q^(-e)<=1. Completing
all nonunit cofactor exponent types is an upper bound after conditional
comparison. For D_q=product_(odd prime p<q)(1+K_p), define

    C_B = sum_(73<q<=B prime)
          E[(D_q-1-(q-2)delta)_+] / ((q-2)(1-delta)),
    J_B = product_(odd p<=B) E[(1+K_p)^2].

Independence is used only for these auxiliary heights. Actual normalized tail
kernels preserve the entire prior joint law, including the head mass epsilon.
Thus head loss, tail charges and all layout moments belong to one actual law.

At B=16384, covering all 1879 tail-prime stages and global prime index 1900,
directed integer arithmetic gives

    C_B <= Cbar = 467101552960255339/1000000000000000000,
    J_B <= Jbar = 559058126433247751329/62500000000000000.

With lambda_0=1-epsilon-Cbar, these bounds give lambda_0>0.13299. Each complete
layout load includes the unit divisor, so L^2>=1. Condition only once on the
common surviving event after B. Simultaneously for all complete layouts,

    E[L^2 | survive] <= 1+(Jbar-1)/lambda_0 < 67250.

The existing certified short stopping threshold is T=326059/4=81514.75.
Equivalently the exact upper bound on the total sufficient score is

    epsilon+Cbar+(Jbar-1)/(T-1)
      =112855677875458768744658421656207338288797194181556030793
       /115545058716265981643344740784033601115000000000000000000
      <1.

This meets the existing BBMST continuation interface, including its
simultaneous complete-layout moment requirement. Its conclusion supplies a
residue avoiding the entire finite family. If the actual family ends before
the stopping point, positive common avoiding mass already suffices by CRT.

## Recovering additional high-power head congruences

The same actual lifted law also treats certain additional head labels. For
any nonnegative head exponent tuple `e=(e_p)`, iterative conditional
expectation and the full-prefix cylinder caps give, for every actual residue,

    Pr(X is in that original congruence class) <= product_p R_(p,e_p),

where `R_(p,0)=1` and `R_(p,e)` is the displayed finite profile followed by its
geometric extension. This iteration uses the conditional cap at each actual
prefix and then averages over that prefix; it does not replace the actual law
by an independent product. Distinct numerical moduli imply that each exponent
tuple occurs at most once, irrespective of the selected residues.

For a cutoff h, summing the positive upper bounds over all tuples with some
`e_p>h` therefore bounds any finite union of such added original head classes
by

    E_h = product_p (1+sum_(e>=1) R_(p,e))
          - product_p (1+sum_(1<=e<=h) R_(p,e)).

The geometric tails make these sums finite. They are bounds on events of the
same actual full-height law used for the original head and all subsequent
kernels. The head-union loss is at most `epsilon+E_h`; normalized tail kernels
preserve it. Only after the tail stages through B do we condition on the
common avoiding event. Thus the general cutoff recovery criterion is

    epsilon+E_h+Cbar+(Jbar-1)/(T-1) < 1.

More generally, `epsilon` can be the bad-union mass of any supplied truncated
head law with these full-prefix caps, provided its corresponding tail charge
and complete-layout moment bounds are established under that same law. This
is a sufficient criterion, not a theorem that a suitable law always exists.

All original 154 head moduli have every prime exponent at most five. For the
present profile, the exact certificate computes

    E_5 = 0.017422423684502572...,
    epsilon+E_5+Cbar+(Jbar-1)/(T-1) = 0.9941468213291367... < 1.

A short rational proof uses four separately checked strict upper bounds:

    epsilon < 2/5,  Cbar < 47/100,  Jbar < 9000,  E_5 < 7/400.

Consequently the enlarged common surviving event has mass greater than
`9/80`, and every complete layout satisfies

    E[L^2 | enlarged survive] < 1+8999/(9/80)
                              = 719929/9 < 326059/4,
    326059/4 - 719929/9 = 54815/36 > 0.

This proves noncoverage after adding arbitrary finitely many distinct
73-smooth congruence classes, each with a modulus divisible by `p^6` for some
odd prime `p<=73`, together with the already unrestricted classes whose
largest prime factor exceeds 73. All added residues and finite exponents are
arbitrary. Any subset of the original 154 classes is also allowed. The bound
`67250` above applies to the original fixed-head baseline; the enlarged
head uses the separate bound `719929/9` proved here.

## Verification and limits

The retained [laminar verifier](../frontier/source-budgets/verify_depth_profile_laminar.py)
checks 168 generic row LPs and 224 full-CRT row LPs. Every floating LP solution
is converted to rational primal and dual witnesses, with feasibility,
multiplier signs, reduced costs and equal objectives verified exactly.
Twenty-four small actual joint laws are expanded and checked against original
congruences and every full-prefix cylinder cap. The old 78- and 154-label
flat-cap values are exactly recovered. Its
[complete result](../certificates/source_norms/source-budgets/depth_profile_laminar_verification.json)
retains all small-law inputs and values.

The separate [original-leaf head verifier](../frontier/source-budgets/verify_depth_profile_head.py)
recovers the new 154-label epsilon using 45,029 states, 3,363,080 actual leaf
costs and 8,203,324 exact ancestor-cap checks, without importing the candidate
trie or row optimizer. Its
[complete result](../certificates/source_norms/source-budgets/depth_profile_head_verification.json)
binds the original literal source and supplied profile.

The [directed budget producer](../frontier/source-budgets/depth_profile_tail_budget.py)
and [independent divisor-convolution verifier](../frontier/source-budgets/verify_depth_profile_tail_budget.py)
agree on all 1,879 prime stages, the complete moment and charge bounds, and
the short stopping criterion. Their
[full stage certificate](../certificates/source_norms/source-budgets/depth_profile_tail_budget.json)
and [independent result](../certificates/source_norms/source-budgets/depth_profile_tail_verification.json)
retain the exact fractions. The
[head producer](../frontier/source-budgets/depth_cap_bellman.py) reads the
[actual profile input](../frontier/source-budgets/depth_profile_head_input.json)
and obtains the labels only from Chapter 04c's canonical producer. All
programs expose `--write` and `--check`; arithmetic checks remain active with
Python `-O`. The LP discovery verifier additionally uses NumPy and SciPy.

The ordinary analytic inputs are the conditional comparison in
[Schroeder, Section 3](../../../../Library/Arith/schroeder2026noncoverage.md)
and [BBMST, Theorem 6.1](../../../../Library/Arith/balister2018covering.md),
with the transfer derived in Chapter 04. These finite computations do not
formalize those analytic inputs in Lean.

This result changes the caps and recomputes their costs. It does not repair
the disproved old fixed-cap universal bound. The original two counterexamples
and their uncovered integers remain valid. No universal existence theorem for
successful profiles has been proved, and the total number of compressed
Bellman states is not asserted to have a uniform polynomial bound.
