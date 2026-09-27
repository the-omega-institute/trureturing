---
bibkey: schroeder2026maximumdensity
authors: Michael Schroeder
year: 2026
title: "Erdős Problem 278: Formulas and Complexity of Maximum Covered Density"
doi: 10.5281/zenodo.22874487
url: https://michaelschroeder.ai/research/Erdos278/companion
claim: "Exact maximum-density optimization through saturated labelled local trees and avoidance profiles; completion-dependent local partition necessity; distinct-modulus covering hardness uses even moduli."
strata_touched:
  - D5/S3/Arith/Congruence/ActualCylinderChain
license: "Paper, documentation and original audit outputs: CC BY 4.0; original Lean/Python/build code: Apache 2.0; third-party rights retained. No upstream code is copied here."
triage: anchor
---

# Maximum covered density, local states, and the odd-covering boundary

## Source and verification scope

Michael Schroeder, version 1, published 22 September 2026 at
<https://doi.org/10.5281/zenodo.22874487>. The Zenodo record identifies that
date and record 22874487; the package README's statement that the DOI was
reserved describes packaging, before the public deposit.

Archive: <https://michaelschroeder.ai/research/Erdos278/erdos278-zenodo-v1.zip>.
Its 6,900,049 bytes have SHA-256
`cd176b03de604405e5d6672da6e3ae684e49a0c3dff9e98f358581f59910ccea`
and MD5 `417f33b1d6afeb0ef6fa7a46d5083c56`, agreeing with the supplied
SHA-256 list and Zenodo checksum respectively.
The manuscript `output/latex/erdos-278-publication-v1.tex` has SHA-256
`52be86f3f2711bf4c0af98959e1ebb9ec98cfcfe937e0566d897b1d3853875c7`.
The package's `RIGHTS.md` assigns the component licenses in the front matter.

The statements and ordinary proofs cited below were read, including their
quantifiers. The upstream Lean companion was **not built or kernel-replayed
locally** for this note. Its `lean/PUBLICATION_SCOPE.md` reports Lean 4.32.2,
mathlib `905b95818eb32af7874a58b427f50c1711a5e96c`, and selected structural
proofs for supplied coprime coordinates. It explicitly excludes the full
complexity classifications, factorization-free algorithm/runtime,
list-to-set covering reduction and deterministic star reductions. Neither
that scope statement nor the exact controls below is local Lean certification.

## Exact original-label optimization

For a fixed finite set A={m_1,...,m_r}, m_i>1, let

    U(A)=min_a |{x mod L: x != a_i mod m_i for all i}|/L,
    L=lcm(m_1,...,m_r).

Every original modulus retains its label, prime exponents and independently
chosen residue. Sections 4–7, labels `thm:saturation`, `cor:kernel`,
`thm:tensor` and `thm:master`, give the following exact reduction.

At prime p and depth h, live labels have v_p(m_i)>=h and share the preceding
digits. An optimal residue vector exists in which each live block B uses
exactly min(p,|B|) nonempty next-digit children. Retain the indexed child
partition, the stopping exponent of every label, and all further partitions;
forget only the names of the digit children. Call this finite local state
sigma_p. The proof moves a single label from a crowded child to an unused
child, using submodularity of union measure under **uniform CRT measure**.
It cannot reduce covered density. Sequential moves preserve earlier splits.

For a fixed state, let B_p be the random subset of labels whose p-adic
requirements hold at a uniform p-adic residue. Its law mu_(p,sigma_p) has
at most d_p+1 positive atoms, where d_p is the number of incident labels.
This is a bound for one fixed state, not the union of all state supports.
The global uncovered indicator gives the exact nonnegative formula

    U(A)=min_(sigma_p) sum_(B_p) [prod_p mu_(p,sigma_p)(B_p)]
                    prod_i (1-prod_(p|m_i) 1_(i in B_p)).             (MD1)

The decision sigma is made before the chance masks are sampled. Reversing
the minimum and sum changes the optimization problem. As A is finite,
all saturated state products having positive value in MD1 is equivalent
to noncoverage for **every original residue vector** on A. This is an exact
reduction, not a uniform positive bound over all odd A.

Independent rooted-tree digit permutations preserve uniform CRT measure
and carry the labelled cylinders together. They are a precise lossless
change of representation. They do not justify transporting an arbitrary
nonuniform supported probability without also transporting that probability.
Moreover, union-density maximization differs from the repository's
worst-case squared-load objective Gamma. The saturation theorem does not
permit restricting Gamma's adversarial independent phases to saturated ones.

## What a safe DP boundary must retain

Fuse primes that involve the same label set I. If C is the intersection
of their local masks, retain every avoidance coordinate

    phi(T)=Pr(C intersect T is empty),       T subset I.

For a fixed outside completion xi, the global uncovered objective is

    u(sigma,xi)=sum_(T subset I) lambda_xi(T) phi_sigma(T),
    lambda_xi(T)>=0,     sum_T lambda_xi(T)<=1.                       (MD2)

The coefficients retain the joint outside relationships, not only separate
marginals. A profile can be deleted if it is coordinatewise at least a
convex combination of **other currently available** profiles. Multiplying
by MD2 shows that at least one of those actual alternatives is no worse
for the fixed completion. The alternative may depend on xi. This does
not produce one alternative that dominates for every completion, and does
not replace the actual supported pre-phase law used by the repository's
minimax problem. These are `thm:domination` and `prop:frontier`.

Section 13 gives a sharp limitation (`thm:arithmetic`,
`cor:deletionmodel`). Fix a prime p, d>p, and a partition pi of d original
labels into p nonempty blocks. There are distinct private primes q_i>p
such that pi is the unique optimal p-fibre partition for A={p q_i}, up
to naming the fibres. Empty-fibre competitors are included. Consequently
no rule depending only on this squarefree local incidence may omit any
partition while guaranteeing an optimizer for **every private completion**.
For odd p these are already distinct odd moduli with two prime factors.
Different target partitions use different numerical completions.

The proof first assigns rational weights with each target block of weight
one and no other subset of weight one. It then selects private primes in
narrow reciprocal windows and bounds the cubic remainder in the product
expansion. Thus unique local necessity is an arithmetic statement, not just
an abstract convex separation. A deterministic version permits composite
pairwise-coprime cofactors (`cor:constructive`); taking c=2p in
`lem:generalwindows` makes those cofactors odd when p is odd. This is a
direct specialization of the source construction, not a new Lean theorem.

## Odd threshold optimization can be hard while zero coverage is settled

The source's `prop:star` gives, for pairwise-coprime m_i>1 all coprime to 3,

    U({3} union {3m_i})
       =(1/3) min_(B subset [n])
           [prod_(i in B)(1-1/m_i)+prod_(i outside B)(1-1/m_i)].       (MD3)

Every factor is positive; in particular

    U >= (2/3) prod_i (1-1/m_i) > 0.

Hence U>0 for every finite member of this family, for all original phases.
Choosing a residue for modulus 3 covers one
fibre; an optimizer places the other classes in the two remaining fibres.
CRT proves MD3 and realizes every bipartition. The repository's existing
[incidence-forest result](../../docs/reports/erdos7-odd-covering/problem-details/48-incidence-forests-with-arbitrary-original-heights.md)
already includes this noncoverage geometry with wider height/support
allowances. It is not a new noncoverage case; the relevant addition is its
separation from exact threshold optimization complexity.

The deterministic positive-threshold reduction in `thm:stardecision` also
works with **all moduli odd**. Here is the complete parity specialization.
Given positive PARTITION weights W_i with sum 2T and W_i<=T, set

    w_i=W_i/T,    eta=1/(64T^2),    s=128nT^2.

In `lem:generalwindows`, choose c=6 instead of c=3. Select distinct integers
a_i as the first unused integer >=ceil(s/w_i), and put

    R=6 prod_(i<j)|a_i-a_j|,     m_i=R a_i+1,     t=sR.             (MD4)

Then the m_i are odd, distinct, pairwise coprime, and coprime to 3. Indeed
each is coprime to R; any common divisor of two also divides a_i-a_j and
hence R. The source's window argument still gives

    t/w_i <= m_i <= (1+eta)t/w_i,       t>=6s>=64T^2.

Let X=sum_i 1/m_i and define the computable rational threshold

    theta=[4t^2-2t^2 X-sum_i w_i^2+2+T^-2]/(6t^2).                (MD5)

The threshold is positive: X<=2/t and sum_i w_i^2<=2 make its numerator
at least 4t^2-4t+T^-2>0. The source's uniform expansion
(`lem:starseparation`) now applies unchanged:
if a balanced partition exists, U<=theta-1/(8t^2T^2); otherwise
U>=theta+1/(8t^2T^2). All construction steps and output bit lengths are
polynomial in the binary input. Empty inputs map to ({3,15},2/3);
odd-total or overweight inputs map to ({3,15},1/3). The fixed density is
U({3,15})=3/5, so these also preserve the answer and oddness.

A bipartition is a polynomial-bit certificate for U<theta by MD3. Thus the
positive-threshold language remains NP-complete under deterministic
many-one reductions on this all-odd distinct family. This conclusion is
a direct ordinary specialization of the cited written reduction. It is
not a new complexity formalization or an independence result.

This separates three questions on the **same** original arithmetic:

* optimizing exact positive uncovered density can encode PARTITION;
* the zero test U=0 is always false on this star family;
* no undecidability or Gödel conclusion follows from the first statement.

The paper's separate covering-hardness result (`cor:distinctcover`) uses
powers-of-two masks to distinctify a repeated odd list. Its output can be
entirely even. It establishes no hardness reduction for unrestricted
distinct-odd complete covering. Removing those masks would invalidate that
reduction; the odd intermediate list has repeated moduli.

## Graph width and the remaining #7 gap

The source distinguishes three graphs: the graph on moduli with edges
gcd(m_i,m_j)>1, the prime–modulus incidence graph, and the graph on primes
that co-occur in a modulus. Only the first graph supplies the treewidth
parameter in `thm:fpt`. Given its width-tau decomposition, exact optimization
and optimizer recovery use g(Delta) 2^(tau+1) poly(b) bit operations, with
Delta<=tau+1 and b the binary input length. The gcd-free construction avoids
assuming supplied prime factorizations. The paper's runtime argument is an
ordinary proof, outside its stated Lean scope.

The odd stars in MD3 have a prime–modulus incidence tree and a complete
noncoprime graph. Therefore small incidence width is not the above
tractability hypothesis. The existence of an exact algorithm for every
finite A also supplies no uniform proof of U(A)>0 for every distinct odd A.

For the repository, MD1–MD2 give an exact route for preserving local states
and their joint completion data. They do not establish the universal
supported-law bound in report 400, remove the disagreement hypothesis of
report 422, or discharge the average-charge budget of ActualCylinderChain.
Those comparisons and unrestricted Erdős #7 remain unresolved.

## Reproducible parity and threshold controls

The original research program
[odd_star_threshold_bridge.py](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/odd_star_threshold_bridge.py)
implements MD3–MD5 with exact integers and fractions. It constructs instances
from supplied positive weights and independently tests the source subset-sum
answer against the target star minimum. The default run checks 462 inputs:
the empty tuple, singleton weights 1–5, and all nondecreasing tuples of
length 2–6 with entries 1–5. There are 176 YES and 286 NO answers; the
largest constructed modulus uses 269 bits. It checks oddness, distinctness,
coprimality, every construction window, and the rational separation margin.

A separate literal-period check enumerates all 315 independent normalized
phase vectors for {3,15,21}, with the modulus-3 residue fixed by translation.
It finds 58 holes per 105 positions, agreeing with MD3. The input (1,1)
produces {3,4611,4629} with

    0 < U=1580034/2371591
        < theta=22366609747975/33571710959616.

This is an exact counterexample to inferring complete coverage from a YES
positive-threshold answer. The finite checks validate the implementation on
their stated inputs; they do not prove the general reduction. No upstream
Python executable or Lean source is imported by the program.
