# A source selector is weaker than full labelled-pair demand

[Index](../../../marked_head_profile.md) · [Endpoint capacity](845-endpoint-capacity-forces-singleton-charges.md) · [Whole-cover surplus](846-whole-cover-surplus-decomposition-for-endpoint-capacity.md) · [BBMST audit](../../../../problem-details/76-global-repair-literature-audit.md)

Reports 845--846 study a deliberately strong endpoint adapter: on each actual
source outcome it asks the surviving originals to pay one unit for every
labelled numerical collision pair. The original Erdős #7 route does not have
that requirement. It needs a source-preserving collision selector or union
charge that meets the BBMST conditional-cap and strict-budget hypotheses.
Consequently, the endpoint obstruction is a boundary result for that adapter
class, not a contradiction to the unrestricted problem.

## 1. Two different demands

For a source outcome \(\omega\), let \(k_c(\omega)\) be the number of surviving labels in an output numerical column \(c\), and put

\[
 N(\omega)=\sum_c\binom{k_c(\omega)}2.
\]

The demand imposed by the full-pair adapter is

\[
 D_{\mathrm{pair}}(\omega)=N(\omega).
\tag{1}
\]

Report 844 proves \(N(\omega)\ge1\) for every source outcome in its common
source. That lower bound only says that the family of collision events covers
the source. A selector can choose one event from that family on each outcome.
Its source-level demand is instead

\[
 D_{\mathrm{sel}}(\omega)=1,
\tag{2}
\]

or, for a fractional selector, a nonnegative collection of event weights whose
sum is one. The selected event must still retain its original labels, phases,
common source and legal continuation. Nothing in the selector condition asks
all \(N(\omega)\) labelled pairs to receive separate unit payments.

Since \(N\ge1\), (1) is strictly stronger than (2) whenever a source outcome
has more than one labelled pair. The positive-mass event in report 845 on
which endpoint-only capacity is less than \(N\) therefore rules out only the
full-pair contract. It does not rule out a selector or union charge.

## 2. The published BBMST interface is a moment condition

The reusable BBMST statement recorded in report 76 is the phase-sensitive
condition

\[
 \sum_i\min\!\left\{M_i^{(1)},
 \frac{M_i^{(2)}}{4\delta_i(1-\delta_i)}\right\}<1,
\tag{3}
\]

where the second term is built from the square of an actual conditional union
fraction. It is not the pointwise requirement \(N(\omega)\) in (1). For one
output column of modulus \(n\), suppose its \(k\) surviving phases are distinct.
Its union fraction in the common endpoint coordinate is

\[
 \alpha=\frac{k}{n},
 \qquad
 \alpha^2=\frac{k^2}{n^2}
       =\frac{k+2\binom{k}{2}}{n^2}.
\tag{4}
\]

Thus a collision pair contributes with the two factors \(n^{-2}\) in the
second-moment interface. The full-pair demand in (1) counts the same pair with
unit weight. If phases coincide, the union is smaller still; replacing it by
\(k/n\) is then an upper bound, not an identity.

This distinction is quantitative. In the abstract single-column pattern
\(n=11,k=11\) with all phases distinct, \(N=55\) while the union fraction is
\(\alpha=1\) and its square is \(1\). The endpoint contract would request 55
units before any tree or conditional-cap restriction, whereas the BBMST
second-moment term sees a unit union. This finite pattern is only an
accounting example; it is not an Erdős #7 covering counterexample.

## 3. What the source-global collision result supplies

The common-source result supplies the following reusable facts:

1. the collision events cover the same actual source, so at least one
   collision event is available at every source outcome;
2. the numerical modulus and original label of every surviving endpoint are
   retained;
3. fixed-column collision moments can be averaged under the one common source
   law.

It does not supply a selector whose charges have the BBMST tree/rank form, and
it does not supply the strict version of (3). Selecting one pair pointwise is
only a set-theoretic step: the selected pair may have the wrong endpoint
capacity, wrong depth reuse, or no admissible continuation after the selected
collision is exposed.

The actual missing bridge must therefore construct, under one joint source
law, a family of selector or union charges \(Q_h\) satisfying all of the
following at once:

\[
\begin{aligned}
&\text{the selected collision event covers the source;}\\
&\text{each charge preserves its literal phase and original label;}\\
&\text{the conditional BaseCaps and depth/rank constraints hold;}\\
&\mathbb E[\mathrm{totalCharge}]<1.
\end{aligned}
\tag{5}
\]

The last line is a strict global budget. A conditional owner partition with
total charge exactly one, or a scalar inequality \(N\le C_*W\), cannot replace
it. Conversely, the singleton lower bound in report 845 remains a genuine
necessary condition for the narrower adapter that caps each literal endpoint
and demands the full \(N\) units.

## 4. Consequence for the current proof target

The correct next target is not to force the scalar whole-cover inequality

\[
N\le C_*W
\tag{6}
\]

as a necessary property of every odd cover. Equation (6) is the feasibility
condition for the full-pair endpoint relaxation used in reports 845--846. It
may be useful as a diagnostic for that relaxation, but proving or refuting it
would not settle unrestricted Erdős #7 by itself.

The main route remains open at the source-preserving adapter in (5): either
derive the BBMST second moments from the common-source collision geometry, or
construct a whole-cover replacement that preserves all original phases and
distinct moduli. No proof of noncoverage, and no covering counterexample, is
claimed here.
