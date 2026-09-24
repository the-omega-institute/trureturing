# 55. Adaptive read-once head orders and conditional comparison

A coordinate order may depend on the actual coordinates already read while
retaining the same independent-auxiliary convex comparison. The full decision
transcript must satisfy deterministic cylinder caps, and every original
coordinate and label keeps its identity. An explicit eleven-class family of
period 315 has an adaptive head law of bad mass zero, while every fixed order
has minimum bad mass at least `1/60` under the same caps.

This is ordinary mathematics with exact finite computation. The existing
Lean conditional comparison has a fixed coordinate chain; the adaptive
extension below is not claimed to be kernel-verified. The one-coordinate
comparison is the existing nested-marginal rearrangement from
[Schroeder, Section 3](../../../../Library/Arith/schroeder2026noncoverage.md).
No priority claim is made. The unrestricted distinct odd covering problem
remains open, and the fixed 154-label atom-cap obstruction in
[Chapter 04c](04c-full-history-capped-laws-and-exact-global-optimization.md)
continues to apply to adaptive orders.

## Exact hypotheses and conclusion

Let P be a finite set of original coordinate names and J a finite set of original labels. Coordinate p has finite value space X_p. For every label j and coordinate p fix the event A_(j,p) in X_p and deterministic cap r_(j,p) in [0,1]. Fix w_j >= 0 and a nonnegative increasing convex function phi on the nonnegative reals.

A finite decision tree samples each coordinate exactly once. At a node h its next coordinate p(h) belongs to the remaining set S(h) and is determined by the observed full-coordinate transcript. The conditional row mu_h on X_p obeys

    mu_h(A_(j,p)) <= r_(j,p)

for every j. These are caps conditional on the complete actual decision transcript, including the chosen coordinate. It is enough that they hold at every positive-probability node; other rows may be filled by any permitted row. Earlier full values stay fixed after sampling. The global events, label identities, weights and caps do not change with a branch. The tree may depend on all fixed problem data.

The output is one actual tuple X. With independent uniform auxiliaries U_p, one for each original coordinate name, the conclusion is

    E phi(sum_j w_j product_(p in P) 1_(A_(j,p))(X_p))
      <= E phi(sum_j w_j product_(p in P) 1_(U_p <= r_(j,p))).

The same U_p is shared across all labels j. No nesting of the original events is required. For depth profiles take r_(j,p)=r_(p,e_(j,p)); e=0 has cap 1. Auxiliary independence is a property of the upper comparison, not a property of the actual tuple.

## Proof with the necessary strengthened induction

For any remaining set S and any nonnegative vector b define

    B_S(b) = E_(U_S) phi(sum_j b_j product_(p in S) 1_(U_p <= r_(j,p))).

At every node h let b_j=w_j times the product of that label's indicators on all coordinates already read. More generally, the induction hypothesis is uniform over every admissible subtree on S and every nonnegative b; this strengthened statement permits the masks arising in each branch. For S empty the claim is equality.

Fix a node h with S nonempty and its selected coordinate p. For each x in X_p set b^x_j=b_j 1_(A_(j,p))(x). Applying the induction hypothesis to the actual continuation subtree at h,x gives its conditional terminal expectation at most B_(S minus {p})(b^x). The remaining subtree may choose a different order at every later node; it still has exactly the same remaining coordinate set and deterministic cap data.

Average this inequality against the row mu_h. Exchange the finite expectation in x with the independent auxiliary expectation in U_(S minus {p}). For each fixed auxiliary realization put

    c_j = b_j product_(q in S minus {p}) 1_(U_q <= r_(j,q)).

The c_j are now fixed nonnegative constants. The one-coordinate nested-marginal comparison applies to mu_h and gives

    E_(x ~ mu_h) phi(sum_j c_j 1_(A_(j,p))(x))
      <= E_(U_p) phi(sum_j c_j 1_(U_p <= r_(j,p))).

Averaging over the independent suffix auxiliaries produces exactly B_S(b). The expression is indexed by the original remaining set S and does not depend on which p was selected. This proves the induction and the root conclusion. Nonnegativity permits the same exchange via Tonelli; for the finite input all values are bounded by phi(sum_j w_j). Countable nonnegative label completion follows separately by monotone convergence.

There is no step that conditions the actual unobserved coordinates on auxiliary values. Each auxiliary expectation is introduced only after a pointwise-in-history subtree bound, and then integrated against the actual selected row. There is also no assumption that the final actual law satisfies caps in every fixed numerical coordinate order.

A randomized coordinate choice is also allowed if its randomizer is included in the transcript and the selected row caps hold after this conditioning. For each selected p the same B_S(b) upper bound holds, so averaging over that choice preserves the result.

## The same comparison as a potential

Equivalently, define the potential at a transcript h by

    Z(h)=B_(S(h))(b(h)),
    B_S(b)=E_(U_S) phi(sum_j b_j product_(i in S)1_(U_i<=r_(j,i))),

where b_j(h) is w_j multiplied by that label's actual indicators on the
coordinates already read. The same one-coordinate argument gives
E[Z(next transcript)|h]<=Z(h), whatever legal next coordinate h selects.
Thus Z is a bounded-horizon supermartingale. The initial value is the full
auxiliary comparison; after all coordinates are read, the remaining set is
empty and Z equals the actual terminal payoff. The dependency-aware state
(remaining names, surviving original requirements) supplies the potential;
the step number alone does not. This is an ordinary reformulation of the
same proof, not a separate physical time or entropy assertion.

For completeness, at a node with remaining set S and chosen coordinate p,
fix the independent auxiliary tuple for `S minus {p}`. Its indicators mask
the incoming nonnegative weights. The one-coordinate comparison then bounds
the row average after p by the corresponding average over an independent
`U_p`. Averaging over the suffix auxiliaries gives
`E[Z(next transcript)|h]<=B_S(b(h))=Z(h)`. This is the same local inequality
used by the induction; a bounded number of read-once steps reaches the exact
terminal payoff. The two formulations use the same actual experiment and
introduce no order-dependent replacement of the original events.

## A strict separation on actual original congruences

An actual strict separation uses the original classes

    3:1, 5:4, 7:1, 9:5, 15:12, 21:2,
    35:31, 45:18, 63:18, 105:90, 315:110.

The moduli are all eleven nonunit divisors of 315 and are pairwise distinct
and odd. Coordinate moduli are 9, 5, 7, with reciprocal atom caps 1/4, 1/3, 1/5.
The ternary proper depth-one cap is 3/4. The six fixed prime orders have exact
minimum head bad masses

    (3,5,7):1/60, (3,7,5):1/30, (5,3,7):1/20,
    (5,7,3):1/30, (7,3,5):1/15, (7,5,3):1/15.

An adaptive policy attains 0. First sample the coordinate modulo 9 uniformly
from {2,3,6,8}. If it is 2, next read the coordinate modulo 7. If it is 3, 6 or 8,
next read the coordinate modulo 5. Complete the last coordinate with the
certified row for that full transcript. There are 60 distinct CRT outcomes,
each of mass 1/60, and all avoid every one of the eleven original classes.
The [complete certificate](../certificates/source_norms/source-budgets/adaptive_head_bellman.json)
retains every row, all 60 CRT support points and their exact masses. The same actual law
violates at least one fixed-order conditional atom cap in every fixed order;
there is no contradiction with those strictly positive fixed-order minima.


For this fixed family, the [adaptive Bellman producer](../frontier/source-budgets/adaptive_head_bellman.py)
retains all original IDs and their remaining requirements. Its memoization
key consists of the remaining named-coordinate set and the still-matching
original label IDs. At each state it minimizes over the next coordinate,
then applies Chapter 54's exact laminar row operator to that coordinate's
actual p-adic tree. The feasible rows and the fixed head-union payoff depend
only on this key, so backward induction is exact for this objective. Actual
coordinate values remain in the generated law; a future objective with
additional requirements may need a larger key.

The displayed 315 witness uses flat leaf caps. The producer checks that its
entire depth profile is `r_e=min(1,p^(H-e)/k)` before reconstructing rows by
averaging the k cheapest actual leaves. The general adaptive Bellman operator
still uses the laminar-cap solver and is not restricted to flat profiles.

The [independent original-CRT verifier](../frontier/source-budgets/verify_adaptive_head_bellman.py)
enumerates all 315 actual CRT tuples before evaluating its full-coordinate
recurrences. It imports neither the candidate Bellman procedure nor its
laminar row operator. It recovers every fixed-order minimum, the zero adaptive
minimum, and the full 60-point law, checking all 141 full-transcript depth-cap
conditions. Its [complete result](../certificates/source_norms/source-budgets/adaptive_head_verification.json)
retains every reachable row and support point. Both programs read the single
[literal 315 input](../frontier/source-budgets/adaptive_head_input_315.json),
expose `--write` and `--check`, and keep all arithmetic checks active under
Python `-O`.

## Head transfer and the numerical tail schedule

Generate the entire head using one admissible adaptive read-once tree, then
start the existing tail-prime schedule in increasing numerical order. For
each fixed original cofactor load, the theorem supplies the same independent
auxiliary convex bound as a fixed head order. This includes the positive-part
functions used for tail charges and the square used for complete-layout
moments. Consequently the profile-dependent `C_B` and `J_B` of
[Chapter 54](54-depth-profile-head-laws-with-unrestricted-original-tails.md)
remain valid when its fixed-order head law is replaced by an adaptive head
law satisfying the same caps and all the other normalized-kernel hypotheses.
The head bad-union mass epsilon must be measured under that one actual law;
the comparison theorem does not itself give a small epsilon.

These are aggregate expected charge and layout-moment bounds under the common
actual law. They are not bounds on every individual prefix's moment. The
normalized tail kernels preserve the full earlier joint law, and conditioning
on the common avoiding event is performed only once as in Chapter 04.

The tail order is an actual stage obligation. At the q-stage, the original
cofactors of labels assigned to q must already have been exposed, and the
standard charge uses `D_q=product_(odd prime p<q)(1+K_p)`. Sampling q before an
unread cofactor does not supply that stage construction. The symmetry of the
auxiliary comparison does not justify arbitrary adaptation of this numerical
tail schedule. A different schedule would require its own valid original
assignment, kernel and charge proof.

If later cofactors need greater head heights, the uniform extra-digit
extension of Chapter 54 remains available: run the coarse adaptive policy,
choose the next coordinate from its observed coarse transcript, and append
independent uniform extra digits when that coordinate is read. At a full
transcript, previous extra digits reveal no further coarse information. The
selected coarse row keeps its caps, and each deeper cylinder has cap
`r_(p,H_p) p^(H_p-e)`. This retains all original cofactor requirements and
uses the same infinite auxiliary envelope. It does not claim the final law
has those conditional caps in every fixed prime order.

## Selection information, fixed labels and the unchanged obstruction

A randomized coordinate choice is admissible when its randomizer is included
in the transcript and the selected row's caps hold after that conditioning.
The same remaining-set bound holds for every selected coordinate, so averaging
over that choice preserves the comparison. Choosing from observed values is
a sufficient condition ensuring that selection itself reveals no unread
coordinate value. A choice that peeks at unread values cannot reuse caps
conditioned only on a shorter observed tuple.

For example, let X and Y be independent uniform ternary coordinates. Choose X
first when X=0 and choose Y otherwise. Conditional on selecting X, its zero
residue has probability 1, not `1/3`. The unconditional uniform marginals do
not validate that node's cap. If the full-transcript caps truly do hold, the
induction applies; undisclosed selection information is the obstruction.

Original labels cannot change with the branch. A uniform ternary coordinate
has probability `1/3` for each fixed residue, but choosing the label residue
to equal the observed value produces probability 1 and defines a different
problem. Read-once also excludes overwriting a sampled coordinate until its
event succeeds. Actual values, original labels and their masks persist through
the full decision tree.

Adaptive ordering does not defeat the old 154-label joint atom cap. Apply the
comparison theorem to one full original-coordinate atom, with weight 1 and
`phi(t)=t`. Its mass is at most the product of its terminal coordinate caps,
namely `1/K` for the old profiles. This argument covers randomized strategies
as well as deterministic ones. For the literal family in Chapter 04c,

    K = 4385364744027208669814574741078700875,
    S = 2254630674715456873605308528779445940,
    11K-20S = 3146398689990157895854151576276790825 > 0.

The actual avoiding set has S residues, so every such adaptive law has
survival mass at most `S/K<11/20`. Thus it cannot attain the old 55% survival
target under those unchanged caps. This is an obstruction to that law class,
not a covering system. The 315 example proves a strict enlargement beyond the
union of the six fixed-order classes while respecting this all-law boundary.

The source relation is exact: the existing
[fixed-chain comparison](../../../../D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison.lean)
and [capped rearrangement](../../../../D5/S3/Arith/Congruence/ConditionalComparison/CappedGainRearrangement.lean)
supply the one-coordinate mechanism. The ordinary proof here changes the
outer induction to the remaining named-coordinate set. Its head-only consumer
retains the original numerical-tail obligations and the published BBMST
continuation input in [Chapter 04](04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md).
