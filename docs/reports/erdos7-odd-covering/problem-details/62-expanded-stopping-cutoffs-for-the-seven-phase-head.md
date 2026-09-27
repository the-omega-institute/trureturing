# 62. Enlarged stopping cutoffs for the actual seven-phase head

For the actual seven-phase 154-class input and the unchanged balanced
full-depth caps, a directed upper calculation gives a sufficient baseline
score below 1 at B=32768. At B=65536 it remains below 1 after adding the
entire D7-complement allowance for additional distinct 73-smooth moduli.
The ordinary comparison and BBMST continuation are the analytic inputs.
All 6521 exact stages, all full moments and all three complete retained
state tables are reproduced by a separate output-divisor calculation.
The [complete budget certificate](../certificates/source_norms/source-budgets/expanded_stop_budget.json)
and [independent certificate](../certificates/source_norms/source-budgets/expanded_stop_budget_verification.json)
retain the exact inequalities.

## Actual law, complete coordinates, and allowed added moduli

The [actual input](../frontier/source-budgets/uniform_phase_capacity_input.json)
from [Chapter 59](59-terminal-phase-elimination-and-uniform-balanced-profile-obstruction.md)
is the complete list of 154 original pairs (modulus,residue),
all twenty named odd primes from 3 through 73, and their full finite
balanced depth-cap profiles. Its SHA-256 is

    ea227d216660f496ecb3a2c89dbc145605f0ad83c94e5996a7ee76d746ea712b.

The seven changed residues remain globally fixed. The family does not
cover the integers: 34 is outside all its classes. This elementary fact
is not a substitute for the continuation theorem about added classes.
The exact attainable minimum bad mass for full-history laws in the fixed
numerical head order is

    epsilon = 159049786725785092501063718513057031733423
              /417584159586671492708261718750000000000000.

Both the actual-leaf full20 recurrence and the collapsed7 recurrence give
this value. The complete head proof is given below, and the
[head certificate](../certificates/source_norms/source-budgets/expanded_stop_head.json)
retains all exact input profiles and both recurrences' results.
This is an attained law in one fixed order, sufficient for the existence
claim here; no all20 adaptive optimum is asserted.

Choose complete prime-power heights for the entire finite original
family, including old-prime cofactors of classes ending after the stop.
At a head prime p, extend the attained coarse law using independent
uniform extra digits. Its full-history cylinder caps become

    R_p(e)=r_p(e),                         1<=e<=H_p,
    R_p(e)=r_p(H_p) p^(H_p-e),             e>H_p.

This lift preserves the original 154-class bad mass. Process every
prime q from 79 through the last prime at most B using the normalized
pure-survivor full-history kernels with delta=2/5. Unused primes can be
padded. Keep complete original labels and cofactor residues. Distinctness
is required of full original moduli, not of projected cofactors.

Write D7 for the exponent downset

    0<=e_p<=5 for all twenty p, and sum_p e_p<=7.

All 154 numerical head moduli lie in D7. The stronger statement permits
any finite collection of additional distinct 73-smooth moduli outside
D7, with arbitrary fixed residues, as well as unrestricted original
moduli whose largest prime exceeds 73. The latter have no support,
exponent, graph, or prime-count restriction. Extra smooth moduli inside
D7 are not licensed by this certificate. The value 79 is the first tail
prime, not a number of additional smooth classes.

Under the same actual normalized law, every full head cylinder has mass
at most the product of its relevant R_p(e_p). Summing over the complement
of D7 therefore bounds all allowed extra smooth labels by

    E7 = product_p sum_(e>=0) R_p(e)
         - sum_(sum e_p<=7, all e_p<=5) product_p R_p(e_p)
       = 12178662955108141168417081005254705201720160394907142987095108822695559960850758564670622557276071555190196990071501791348394597770358678684960015024861915465372036169824624949
         /312197802707202287652441956932779087248084177416077732471611176007832957992945071464388489195781968726093002603002352860875704688558080000000000000000000000000000000000000000000
       = 0.0390094448119163... .

This is the same complement-D7 sum proved in
[Chapter 57](57-balanced-depth-profile-and-degree-seven-frontier.md).
The product is auxiliary union accounting. Actual coordinates need not
be independent. The producer recomputes the complete 101 coefficients
of product_p sum_(e=0)^5 R_p(e)z^e and the full infinite total, and checks
this fraction against the existing exponent-frontier certificate.
Since the caps are unchanged, this charge remains valid at either new B.
No extra smooth label is charged as one of the q>73 tail labels.

## Independent auxiliary costs and directed integer arithmetic

For each head prime, let an independent auxiliary height K_p have tail
R_p. For each later q, put c_q=5(q-1)/(3(q-2)) and

    Pr(K_q>=e)=c_q/q^e, e>=1.

These auxiliary objects dominate the required same-law loads by the
existing conditional comparison; they do not identify the physical law
with a product law. Define D_(<q)=product_(p<q)(1+K_p), and

    C_B=sum_(79<=q<=B) E[(5D_(<q)-(2q+1))_+]/[3(q-2)],
    J_B=E[product_(p<=B)(1+K_p)^2].

The producer uses Q=10^18, and retains every product state 1 through
26214. Every queried index is at most
floor((2*65521+1)/5)=26208. Positive integer products beyond the retained
range cannot later reenter it.

For every retained atom f=1+K, let A_f=ceil(Q Pr(1+K=f)). Positive
geometric atoms smaller than 1/Q are assigned A_f=1, never zero. If
W_d/Q is an upper bound on the previous exact mass, the update is

    W'_n = ceil(sum_(df=n) W_d A_f / Q).

Every coefficient is nonnegative, so this remains an upper bound.
The candidate iterates factors f and previous products d and sums all
terms before its single upward rounding at each output n. No floating
arithmetic enters the directed recurrence.

Full moments are kept separately, with upward rounding after each exact
factor multiplication. Head factors, including every geometric high
digit and every discarded high product, are

    E(1+K_p)=1+sum_(e=1)^H r_e+r_H/(p-1),
    E(1+K_p)^2=1+sum_(e=1)^H(2e+1)r_e
                +r_H[(2H+1)/(p-1)+2p/(p-1)^2].

Tail factors are

    E(1+K_q)=1+c_q/(q-1),
    E(1+K_q)^2=1+c_q(3q-1)/(q-1)^2.

For a=2q+1, the exact identity

    E[(5D-a)_+]=5 E[D]-a
                 +sum_(d<=floor(a/5))(a-5d)Pr(D=d)

has nonnegative coefficients on all approximated inputs and an exact
negative constant. Substituting upper bounds and dividing upward by
3(q-2) therefore gives a certified upper charge. The complete single
sweep stores all 6521 triples (q,upper charge times Q,cumulative times Q).
It also retains exact full moments and complete low-state tables at each
checkpoint. Its first 1879 triples, C and J agree exactly with the
existing B=16384 calculation despite the larger retained table.

## Threshold direction and sufficient inequalities

The global stopping index is k=pi(B), including 2 and absent primes.
The actual consecutive boundary primes are

| B | k | p_k | p_(k+1) | Number of q>73 stages |
|---:|---:|---:|---:|---:|
| 32768 | 3512 | 32749 | 32771 | 3491 |
| 65536 | 6542 | 65521 | 65537 | 6521 |

The existing [stopping library](../verify_finite_continuation.py),
function `stopping_threshold(k)`, uses
24 positive atanh terms, exact binary range reduction, and downward
rounding of logarithms on a 10^(-18) grid. The bracket is checked positive
before squaring. It gives a rational T_lower no greater than

    T_k=k(log k+log log k-3)^2.

At each cutoff, the directed exact inputs are:

| B | C_upper | J_upper |
|---:|---:|---:|
| 32768 | 526593380398558313/1000000000000000000 | 2781057433062889372119/200000000000000000 |
| 65536 | 529729584173247533/1000000000000000000 | 19188422562862582061189/1000000000000000000 |

The two threshold lower bounds are, respectively,

    23162022956803485314052844267149430367551
    /125000000000000000000000000000000000,

    518029814737781787029537945359170411871
    /1250000000000000000000000000000000.

The exact rational scores, retained without decimal rounding in
the complete budget certificate, satisfy:

| B | epsilon+C_upper+(J_upper-1)/(T_lower-1) | With E7 added |
|---:|---:|---:|
| 32768 | 0.9825127538989533... | 1.0215221987108696... |
| 65536 | 0.9569095215170104... | 0.9959189663289267... |

Thus B=32768 passes the baseline test and B=65536 passes both tests.
The exact D7 margin at B=65536 exceeds 0.004081. The B=32768 D7 upper
score being above one only says that these allowances do not establish
that stronger statement there; it is not a lower bound on any actual
loss or a noncoverage counterexample.

Let E be zero for the baseline or E7 for the stronger statement. The
same unconditioned physical law supplies epsilon, the extra head bound E,
the cumulative tail charge C_B, and the simultaneous moment J_B. Its
common avoiding event after the chosen cutoff has mass at least

    lambda=1-epsilon-E-C_upper>0.

Let S be that single common avoiding event and write s=Pr(S)>=lambda.
For every complete layout, choose its fixed residue independently for
each divisor as allowed by the existing conditional comparison. This
does not require all layout residues to be reductions of one CRT center.
Its load L satisfies L>=1 pointwise and E[L^2]<=J_upper under the same
unconditioned law. Therefore

    E[L^2 1_S] = E[L^2]-E[L^2 1_(S^c)]
               <= J_upper-(1-s),
    E[L^2 | S] <= 1+(J_upper-1)/s
               <= 1+(J_upper-1)/lambda.

All layouts use this same S and this same law. Condition only once.
The [joint-layout transfer](08-arbitrary-head-transfer-by-the-joint-load-invariant.md)
then gives

    Gamma<=1+(J_upper-1)/lambda<T_lower<=T_k.

The score denominator is T_lower-1. BBMST Theorem 6.1 applies at k>=10
and continues at p_(k+1) using the standard uniform-base kernels and
delta=1/2. It yields noncoverage for every finite remainder of the
original family. If there is no remainder, the positive avoiding mass
already gives noncoverage.

The old fixed-B fixed-T obstructions remain true with their original
scope. These new successes change B while keeping the input geometry
and balanced caps fixed; they do not prove a universal head-law existence
statement, license arbitrary extra head labels inside D7, or settle
unrestricted Erdős #7.


## Attainment and exact calculation of the head law

For each coordinate, direct exact checks give

    r_(p,e)=p^(H_p-e) r_(p,H_p), 1<=e<=H_p.

Consequently a probability distribution satisfying its actual leaf caps
also satisfies every proper ancestor cap, since an ancestor is the
disjoint union of exactly p^(H_p-e) actual leaves. The root still has
total mass one. Each supplied leaf cap is at least the uniform atom
mass, so every row has enough total capacity. All 32 depth identities
and the complete original CRT period are verified.

At an actual prefix, retain the bitmask of all original labels matching
that prefix. A matching label whose requirements have all been read makes
the terminal bad event certain. If no labels remain, its probability is
zero. Otherwise each actual next-coordinate leaf has a continuation bad
value. Leaves with the same remaining label mask have identical
continuation values, but retain their exact multiplicity. If that
multiplicity is n, the aggregate row capacity is n r_(p,H_p).

The minimum expected continuation value is obtained by filling these
groups in increasing cost order until total probability one has been
assigned. This is the fractional-knapsack exchange argument: moving mass
from a more expensive nonempty group to a cheaper unsaturated group
cannot increase the objective. Each group mass can be split among its
actual leaves under their individual caps. Thus every row minimum is
attainable by an actual probability row, not a relaxation.

If r_(p,H_p)=a_p/u_p in lowest terms, this filling uses integer mass
units a_p and u_p. The downstream denominator at coordinate i is the
product of the remaining u_p. Backward induction therefore uses exact
integer arithmetic throughout. Pasting each minimizing row at each full
history gives an attained finite joint law. The active-label mask is a
sufficient computational state because the caps are history independent
and every remaining original condition is fully specified by that mask.
The realized full tuple is retained; memoization does not delete digits.

A second recurrence stops after the seven core coordinates 3 through 19.
The remaining thirteen coordinates have height one, and each of the 76
noncore labels involves exactly one of them. At a complete core tuple
avoiding all 78 core-only labels, let d_q count the distinct actual
forbidden residues still active at terminal prime q. The maximum terminal
survival is exactly

    product_q min(1,r_q(q-d_q)).

The row bound is attainable by putting as much probability as permitted
on the allowed atoms; remaining mass fits on forbidden atoms because
q r_q>=1. The product is attained in the fixed terminal order. Taking its
complement supplies the bad continuation value at each core tuple.

Independent evaluation of both recurrences gives

    epsilon=
      159049786725785092501063718513057031733423
      /417584159586671492708261718750000000000000
      =0.3808807951029895...,

    survival=
      258534372860886400207198000236942968266577
      /417584159586671492708261718750000000000000.

The full20 recurrence has 44,975 states and 3,376,330 actual local leaf
evaluations. The collapsed7 recurrence has 35,558 states and 3,191,384
actual local leaf evaluations, including 5,232 terminal core states.
The latter performs 397,632 terminal label-incidence checks. Both evaluate
the original literal congruences through their exact prime-power gcd
factors and agree as rational numbers.


The [head program](../frontier/source-budgets/expanded_stop_head.py)
imports no head optimizer. It reads the original numerical moduli and
actual changed residues, checks all full prime-power alphabets, and
implements both recurrences directly. These give an attained optimum
only for the specified numerical order.

## Independent divisor calculation and short rational conclusions

The [budget producer](../frontier/source-budgets/expanded_stop_budget.py)
uses the existing factor-to-multiples upward update. The
[independent program](../frontier/source-budgets/verify_expanded_stop_budget.py)
imports neither that update nor the producer. For each target integer n,
it explicitly enumerates its actual divisor pairs (f,n/f), sums every
upper product W(n/f)A(f), and then takes one upward division by Q.
It obtains all 6521 stage triples and all three complete state-table
digests exactly. There are 1,771,008,455 divisor terms and 80,913,331
positive-part correction terms over 20 head and 6521 tail updates.
Its separate trial-division inventory verifies all global prime indices
and the actual next prime after each cutoff, including 65537.

For an independent derivation of the full head moments, condition on
K_p>=H_p and write K_p=H_p+G, where

    E[G]=1/(p-1), E[G^2]=(p+1)/(p-1)^2.

Add each exact atom below H_p to this complete conditional tail. For a
later q, K_q is zero with probability 1-c_q/q and otherwise 1+G.
Consequently the independent first factor is

    1-c_q/q+(c_q/q)(2+E[G]),

and its second factor is

    1-c_q/q+(c_q/q)(4+4E[G]+E[G^2]).

These yield exactly the full moments used by the producer. The
independent complement-D7 coefficients are inherited from Chapter 57's
logarithmic-derivative calculation, and the same exact stopping library
is reused with its checked downward direction.

The exact independent certificate also verifies these shorter rational
chains. Since epsilon<381/1000, at B=32768 one has

    C_upper<527/1000, J_upper<13906, T_lower>185000,
    lambda>23/250,
    Gamma<1+13905/(23/250)=3476273/23<185000<T_k.

At B=65536, use E7<1/25 as well:

    C_upper<53/100, J_upper<19189, T_lower>414000,
    lambda>49/1000,
    Gamma<1+19188/(49/1000)=19188049/49<414000<T_k.

All three programs support `--write` and `--check` under
`python3 -B -I -S -O`, with required checks active under optimization.
The producer certificate retains all 101 complement-polynomial
coefficients and each checkpoint's full table of indices 0 through
26214 (index zero is unused), as well as every exact threshold, charge,
full moment, score, survival bound and Gamma bound. Sources bind complete
logical certificate bytes; their semantic parts preserve all values.
These results are ordinary proofs and exact integer calculations, with
no new Lean declaration or universal head-profile existence assertion.
