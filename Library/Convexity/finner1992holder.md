---
bibkey: finner1992holder
authors: Helmut Finner
year: 1992
title: A Generalization of Holder's Inequality and Some Probability Inequalities
doi: 10.1214/aop/1176989534
claim: Finner's product-measure inequality and its separated-incidence equality classification concern coordinate-supported factors; the normalized ENNReal classification requires additional correspondence proofs.
strata_touched:
  - D5/S3/Combinatorics/Hypergraphs/FinnerProductMeasure
  - D5/S3/Analytic/Measure/NormalizedHolderEquality
license: citation-only
triage: anchor
---
<!-- GID: D5/L/Convexity/finner1992holder -->
# Finner's product-measure inequality

The original article is in *The Annals of Probability* 20(4), 1893–1901.
Its bibliographic metadata identifies the classical source. The original full text
has not been read: the publisher presents an access challenge.

## Verified locator

DOI: 10.1214/aop/1176989534

Directly read restatement: https://arxiv.org/html/2610.29041v1#S1.SS1

## Verified mathematical scope

Jonathan Bennett and Sewook Oh, *Stability for the adjoint Finner inequality
and improved lower bounds on the k-plane transform*, arXiv:2610.29041v1,
Section 1.1, equations (1.4) and (1.5), restate the product-measure inequality.
For coordinate supports S_j and finite exponents q_j at least one, the incidence
constraint is the balanced equality: the sum of 1/q_j over supports containing
each coordinate is one. The nonnegative factors belong to the corresponding
finite L^{q_j} spaces. The integral of their product after coordinate projection
is bounded above by the product of these norms.

## Formal representation and boundary

`FinnerProductMeasure.finner_product_measure` uses a finite dependent product of
arbitrary measurable probability spaces, the actual `Measure.pi` of the coordinate
measures, and `DependsOn` for coordinate support. Its functions take values in
ENNReal and its nonnegative weights are real. Each coordinate's incidence sum
need only be at most one. The conclusion compares the integral of the product of
the powered factors with the product of their full-product-law integrals raised
to the same powers.

The balanced finite-norm restatement supplies mathematical context; it is not
used as a Lean premise. Weak budgets, empty index sets, empty supports, zero
weights, and zero or infinite factor values are included in the proved ENNReal
statement. In the proof, a unit factor absorbs the slack in a coordinate's budget.
Measurable constant extraction applies even when the extracted constant is
infinite. Marginal integration then removes coordinates one at a time without
changing the underlying product law.

The Lean suppliers are Mathlib's `ENNReal.lintegral_mul_prod_norm_pow_le`,
the measurable ENNReal real-power instance, `lintegral_mul_const`, and the
`lmarginal` composition and measurability theorems. The local-to-global
coordinate induction is supplied by the formalization. This is a formal proof
of a classical inequality; no mathematical originality is claimed. No source
code or substantial article text is reproduced.

## Equality in the directly read restatement

In the paragraph following equation (1.6), Bennett and Oh attribute to Finner
an equality classification for the balanced inequality (1.5). Write
M_i = {j : i belongs to S_j}. When M_i differs from M_k for distinct
coordinates i and k, the positive finite norm branch relevant here has equality
precisely when there are positive constants
c_j and one common family of nonnegative coordinate functions H_i such that

    g_j(P_j x)^{q_j} = c_j product_{i in S_j} H_i(x_i)

almost everywhere. The exponents in that restatement are finite real numbers
q_j >= 1. This paragraph is a secondary-source attribution: the original
Finner article remains unread. The displayed representation concerns the
q_j-th powers, rather than the unpowered g_j. Neither this attribution nor
Theorem 1.1 of Bennett and Oh is a Lean supplier in this repository.

## Correspondence with normalized full-product factors

The normalized equality target uses measurable ENNReal functions f_j on the
full dependent product, with DependsOn(f_j,S_j), positive real w_j, balanced
coordinate sums, injective i -> M_i, and masses
m_j = integral_mu f_j satisfying 0 < m_j < infinity. Its asserted conclusion
uses a single measurable family h_i with integral_mu_i h_i = 1 and

    f_j(x) = m_j product_{i in S_j} h_i(x_i)

mu-almost everywhere for every j. This is an additional classification target;
`finner_product_measure` proves the inequality and supplies no equality
classification.

Several reductions preserve the original target. Balance and positive weights
imply that M_i cannot be a proper subset of M_k: summing the positive weights
in the nonempty difference would contradict the two sums being one. Thus
injectivity makes the distinct M_i incomparable. In particular, if w_j = 1
and S_j is nonempty, every coordinate in S_j has incidence set {j}; injectivity
then makes S_j a singleton. If i belongs to a nonempty S_j, its balance equation
also gives w_j <= 1. Therefore q_j = 1/w_j is finite and at least one for
nonempty supports, including the endpoint q_j = 1. An empty S_j imposes no
upper bound on w_j. DependsOn(f_j,empty) makes f_j constant; since mu is a
probability measure, this constant is exactly m_j. Its powered scalar can be
extracted before comparison with the finite-q_j formulation.

For the support-space correspondence, choose an anchor in each X_i; probability
of the coordinate space implies nonemptiness. Extend a point of the S_j product
by these anchors outside S_j. The extension is measurable coordinate by
coordinate, so composing f_j with it gives a measurable support-space factor.
DependsOn gives pointwise recovery after coordinate projection. The projection
from the full product probability law to the support product preserves measure;
this is the integral and almost-everywhere transport required by this reduction.
With g_j = f_j^{w_j} on that support product and q_j = 1/w_j, the identity
w_j q_j = 1 identifies g_j^{q_j} with f_j and its q_j-power integral with m_j.
Finite mass permits replacement of infinity values on null sets by finite values
when comparing with real-valued L^{q_j} factors. This does not assume that f_j
is positive almost everywhere.

Suppose a measurable common representation f_j = c_j product H_i is already
available, with each c_j positive and finite. Put a_i = integral_mu_i H_i.
Tonelli gives m_j = c_j product_{i in S_j} a_i, since all coordinates outside
S_j carry probability mass one. A positive finite product in ENNReal forces
every included a_i to be positive and finite: a zero factor makes the product
zero, and, once zeros are excluded, an infinite factor makes the product
infinite. Balance covers every coordinate. Consequently h_i = H_i/a_i is
measurable and has integral one, and cancellation gives exactly the coefficient
m_j in every row. The normalization uses the same a_i for every incident row,
so it preserves common profiles. Empty supports give f_j = c_j = m_j.

Conversely, a normalized common representation gives the pointwise identity
for its representing functions

    product_j (m_j product_{i in S_j} h_i(x_i))^{w_j}
      = (product_j m_j^{w_j}) product_i h_i(x_i).

Distribute real powers over the finite ENNReal products, interchange the two
finite products, and combine the positive exponents incident to each i. Their
sum is one. A coordinate not incident to a particular row contributes the unit
factor in that row. ENNReal's zero/infinity product convention is retained;
no cancellation at a point is needed. Tonelli and the unit coordinate integrals
make the integral of the final coordinate product one. Finite intersections of
the rowwise full-measure sets transport the original almost-everywhere
representations through this identity. This direction needs neither incidence
injectivity nor positive conditional slice integrals.

When I is empty, the product probability space is a singleton up to its Dirac
representation, every support is empty, and the representation reduces to the
constant-mass identities above. If J is empty and I is nonempty, balance is
inconsistent. If both are empty, the two products and the integral equal one
and the profile family is empty. Duplicate rows S_j remain allowed throughout.

The support-intersection step can be expressed directly in the actual product
model. If f and g are almost everywhere equal, f depends on S, and g is
measurable and depends on T, then h = lmarginal(mu,S-complement,g) is a
measurable representative of f depending on S intersect T. Indeed,
marginalizing a function that depends on S over its complement leaves it
pointwise fixed, since the integrated law is a probability measure. Fubini
transports the almost-everywhere equality to almost every complementary
slice, so the marginals of f and g agree almost everywhere. Integrating the
S-complement coordinates also removes them from g's possible dependencies,
leaving exactly T intersect S. This argument applies to measurable ENNReal
functions without an integrability or positivity assumption.

For a fixed coordinate i, incomparability of incidence sets gives
intersection_{j in M_i} S_j = {i}. Thus a common measurable representative
of normalized conditional slices, on one and the same product probability
law, can be reduced by support intersections to a function of x_i alone.
The missing hypothesis at this step is actual almost-everywhere equality of
those conditional slices under that law. Equality information only where a
product of marginal masses is positive does not supply it globally. A change
to a law with normalized coordinate densities also needs an explicit recovery
argument for each original row on the original product law.

There is also an explicit normalized candidate family without a slice-positivity
assumption. Choose j(i) in M_i, which exists by balance, and an anchor a in the
full product. For each i define

    h_i(t) = m_{j(i)}^{-1}
      lmarginal(mu,I-minus-{i},f_{j(i)})(update(a,i,t)).

Measurability follows from measurable marginal integration and measurable
coordinate insertion. The marginal insertion identity, followed by integration
over i, gives the original full-product mass m_{j(i)}. Multiplying by its
inverse therefore gives integral_mu_i h_i = 1, using exactly its positive
finite mass. The canonical-profile strengthening asks for every original j
to satisfy the almost-everywhere identity
f_j = m_j product_{i in S_j} h_i for this simultaneously chosen family.
Unit integrals and the support-intersection bridge alone do not give that
identity.

`ProperSupportMarginalGluing.finner_equality_iff_common_profiles` proves the
existential equality classification directly under the original product law.
Its supports are finite coordinate sets; on finite I this represents every set
of coordinates. It includes positive finite original masses and strictly
positive balanced real weights, separated coordinate incidence patterns,
empty supports and types, repeated row supports, weight one, unrestricted
empty-row weights, positive-measure zeros and null infinities. The theorem
does not prescribe the above profiles for every incident-row choice. That
canonical-choice strengthening remains a separate correspondence question.

## Finite normalized Holder under one arbitrary measure

Let J be any finite type, mu any measure on a measurable space X, and let
q_j:X->ENNReal be mu-almost-everywhere measurable with integral_mu q_j=1.
For strictly positive real w_j with sum_j w_j=1,

    integral_mu(product_j q_j(x)^{w_j}) = 1
      iff q_j = q_k mu-almost everywhere for all j,k.

The declaration `NormalizedHolderEquality.lintegral_prod_rpow_eq_one_iff`
has exactly these premises. It requires neither probability nor sigma-finiteness.
The empty index type is included with its inconsistent weight-sum premise;
the singleton weight is one. Zeros on positive-measure sets and infinity on
null sets are allowed. Finite unit integrals give finiteness almost everywhere,
which suffices to combine powers of a common density without pointwise
positivity.

Bennett and Oh, Section 1.1 between equations (1.5) and (1.6), identify the
full-support specialization as the classical multilinear Holder inequality.
Their subsequent equality paragraph concerns coordinate profiles under the
incidence separation condition. It is not an exact citation for the Lean
theorem's AEMeasurable ENNReal endpoints. Those endpoints and the arbitrary
measure scope are supplied by its proof from Mathlib's arbitrary-measure binary
equality theorem `ENNReal.lintegral_mul_eq_one_iff_of_lintegral_rpow_eq_one`,
with real conjugate exponents, and the finite inequality
`ENNReal.lintegral_prod_norm_pow_le`. A finite-family induction normalizes
the remaining weights, forces the remaining product's integral to be one,
and applies the binary equality criterion. The reverse direction integrates
the almost-everywhere common density. No mathematical originality is claimed.

This criterion applies to normalized factors on a common measure. It supplies
no recovery theorem across conditional slices of zero mass and does not prove
the common-coordinate-profile classification for Finner's full marginal chain.

## Proper-support assembly in the stability proof

Directly read proof: https://arxiv.org/html/2610.29041v1#S2.SS1

Bennett and Oh, Section 2.1, first consider the case in which every support is
proper. Deleting a coordinate outside a target row leaves that row unchanged.
The lower-dimensional factorization supplies coordinate profiles given by the
one-coordinate marginals of fixed incident rows. Marginal composition identifies
these profiles independently of the coordinate deleted. Every proper-support row
can therefore use the same family. The exact gluing implication takes concrete
normalized factorizations of the deleted marginals as premises; it does not assume
positive slice masses.

The full-support branch of the source separates full-support rows, rescales the
proper-row weights by the positive remaining incidence budget, and uses a global
Holder step. At exact equality, simultaneous almost-everywhere substitution
replaces the stability estimates for products. A proof of marginal gluing alone
does not establish either that full-support reduction or the complete induction
from the original saturation hypothesis.

## Exact equality by induction on the active coordinates

The full equality declaration uses the same ambient product law at every
inductive stage. Normalize each original row to have integral one. Marginal
integration over any one coordinate preserves these integrals. The pointwise
marginal estimate gives a lower bound of one on the weighted-product integral
of the deleted rows, and Finner on their smaller supports gives an upper bound
of one. The remaining incidence patterns and balance equations are unchanged.
The smaller-active-set conclusion supplies all deleted-marginal factorizations
needed by proper-support gluing.

For at least two active coordinates, remove the full-support rows' common
incidence mask. Strict positivity and separation imply that the residual
budget r is positive. Divide the proper-row weights by r. Their product Q
has integral at most one by Finner, while a global Holder bound and saturation
of the original product imply that its integral raised to r is at least one.
Thus Q has integral one. Apply proper-support gluing at that cardinality,
then normalized Holder to Q and the full-support rows. Every full row equals
the same product Q almost everywhere. The singleton case instead uses Holder
only on the incident rows and treats every empty-support row as constant one;
the empty case uses only these constant rows. Finite product interchange and
Tonelli prove the converse. Positive finite scalar normalization restores
exactly the original row masses. These are Lean implications, without invoking
the literature's classification as an unproved premise.
