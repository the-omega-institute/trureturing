# 63. A squared-load stop-loss continuation from the same actual law

Use the actual seven-phase family, attained numerical-order head law and
complete product tables from
[Chapter 62](62-expanded-stopping-cutoffs-for-the-seven-phase-head.md).
The following conditioning bound is general. Fix one actual probability
law mu after all normalized kernels through a
chosen cutoff. Let S be the common event avoiding the original head,
allowed extra head classes and processed tail. Suppose mu(S)>=lambda>0.
For every complete divisor layout b, let L_b>=1 be its load. Each divisor
has its own fixed residue; residues at different divisors need not agree
with one common CRT center. No layout changes in response to a sample.

If 0<=tau<T and simultaneously for every such b,

    E_mu[(L_b^2-tau)_+] <= K_tau,

then pointwise

    L_b^2 1_S <= tau 1_S + (L_b^2-tau)_+.

Integrating and dividing by mu(S) proves

    E_mu[L_b^2 | S] <= tau + K_tau/lambda.

For lambda=1-epsilon-E-C>0 it is therefore sufficient that

    epsilon+E+C+K_tau/(T-tau) < 1.

The single event S and the single law mu are used for all layouts. The
threshold tau is a common deterministic certificate parameter. It is not
chosen separately on different sample histories. At tau=1 the bound
reduces to the existing (J-1)/(T-1) criterion, since every load includes
the unit divisor.

## Existing comparison supplies the premise

The full-history capped comparison in
[Chapter 54](54-depth-profile-head-laws-with-unrestricted-original-tails.md)
and [Chapter 55](55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md)
applies to any
nonnegative increasing convex function of the complete load. On u>=0,
phi(u)=(u^2-tau)_+ is nonnegative, increasing and convex. On all real u,
the function max(max(u,0)^2-tau,0) is an increasing convex extension with
exactly the same values on these nonnegative loads. The actual
complete layout is therefore dominated by the same independent auxiliary
product D=product_p(1+K_p), including every geometric higher digit. Thus

    E_mu[(L_b^2-tau)_+] <= E[(D^2-tau)_+].

This comparison does not assert independence of the actual coordinates,
compatibility of the test-layout residues, or independence of S and L_b.
BBMST Theorem 6.1 can be applied after the same one-time conditioning,
using a rational T no greater than its true stopping threshold.

## Directed finite evaluation

For the positive integer-valued D and any nonnegative tau,

    E[(D^2-tau)_+] = E[D^2]-tau
                     +sum_{d^2<=tau}(tau-d^2) Pr(D=d).

All coefficients on the probability terms are nonnegative. Substituting
the already audited full second-moment upper bound J_upper and each
audited low-product upper mass W_d/Q gives the sound upper bound

    K_upper(tau)=J_upper-tau
                  +sum_{d^2<=tau}(tau-d^2)W_d/Q.

No high-product probability is discarded: the full second moment still
includes it. The negative constant tau is exact. The retained product
table through 26214 contains every d queried here (at most 643).

The [prefix-sum program](../frontier/source-budgets/square_stoploss_curve.py)
checks all square thresholds tau=t^2<T at each of the three
existing checkpoints. It retains every exact score, not only the selected
minimum. The chosen thresholds and independently reproduced exact upper
scores are:

| B | tau | baseline score | score including E7 |
|---:|---:|---:|---:|
| 16384 | 2304 | 1.0188456150321639... | 1.0578550598440801... |
| 32768 | 9216 | 0.9797143771732649... | 1.0187238219851813... |
| 65536 | 16384 | 0.9544537292542283... | 0.9934631740661447... |

These use the independently attained fixed numerical-order head loss
0.3808807951029895..., not the smaller all-law lower bound from a dual
cylinder cover. In particular the displayed B=16384 calculation does
not certify this primal law. Its score exceeding one is not a proof
that every head law or every stronger comparison fails.

At B=65536 the extra allowance E7 is unchanged: it permits arbitrary
finite additional distinct 73-smooth moduli only outside the downset
0<=e_p<=5 and sum e_p<=7. All original q>73 tail classes are still allowed
with arbitrary finite support, heights and residues. Arbitrary changes
to the specified 154 head residues or added classes inside D7 are not
licensed. This strengthens the fixed-input continuation margin without
settling the unrestricted odd-covering conjecture.

The argument is a standard truncated-moment / stop-loss conditioning
bound. No novelty or new Lean proof is claimed. A separate
[direct-sum program](../frontier/source-budgets/verify_square_stoploss_curve.py),
without the producer's prefix accumulation, checks all 1362
thresholds and 340752 individual mass terms. Every exact stop-loss bound,
score and selected threshold agrees. The ordinary proof review also
checks all layouts, full higher digits and the one common law and event.
Both calculations support `--write` and `--check` under
`python3 -B -I -S -O`, with every required check active under optimization.


## Complete numerical certificate and scope

The [curve certificate](../certificates/source_norms/source-budgets/square_stoploss_curve.json)
and [independent direct-sum certificate](../certificates/source_norms/source-budgets/square_stoploss_curve_verification.json)
retain every threshold row. There are respectively 287, 431 and 644 rows
at B=16384,32768,65536, for a total of 1362. Each row contains t, tau=t^2,
the full rational K_upper(tau), and both exact sufficient scores.
The independent certificate additionally retains both conditioned Gamma
bounds, both margins, and the improvement over tau=1 at each selected
threshold. The selected t values are 48,96,128.

The producer maintains prefix sums sum_(d<=t)W_d and
sum_(d<=t)d^2 W_d. The independent program evaluates every sum
sum_(d<=t)(t^2-d^2)W_d afresh, using 340,752 mass summands. It verifies
that tau=0 recovers J_upper and tau=1 recovers J_upper-1 and the earlier
score. The full state-table digests, moments, actual head value and all
source dependencies are checked against Chapter 62's independent
certificate. No tail sweep is needed for this calculation.

For each cutoff the table contains every nonnegative integer t with
t^2<T, and the program chooses a minimum over those rows. No minimum over
all real thresholds, altered head laws, different head phases or changed
profile caps is asserted. An upper score above one at the old cutoff
proves insufficiency only of that tested upper certificate.

The conditioning expression tau+E[(X-tau)_+]/lambda is standard. See
Rockafellar and Uryasev, [Conditional Value-at-Risk for General Loss
Distributions](https://sites.math.washington.edu/~rtr/papers/rtr187-CVaR2.pdf),
author version of November 28, 2001, Section 3, equation (27) and
Theorem 10, which allow distributions with atoms. Taking
lambda=1-alpha gives their usual parameterization. The elementary
pointwise proof above establishes the needed event-conditioning bound;
the covering conclusion also uses the same-law comparison and BBMST
interface explicitly retained from Chapter 62.
