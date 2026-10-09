# Prime Triplet Wheel

## Abstract

This module separates three different observables for the diameter-six templates
\[
H_+=\{0,2,6\},\qquad H_-=\{0,4,6\}.
\]
The ordered gap readout distinguishes orientation, while the unordered pair-distance
support does not. Finite wheel calculations then separate an origin-fixed prefix from a
translation-invariant three-point correlation. The Lean layer proves the general
reflection theorem behind the candidate-space symmetry at every nonzero modulus. The
finite values at \(W=30\) and \(W=210\) remain explicit arithmetic witnesses; they make
no claim about infinitude or asymptotic counts of actual prime triplets.

## Definitions

For a finite offset set \(H\), a modulus \(W\), and a representative \(r\), the candidate predicate is
\[
\operatorname{wheelAdmissible}(W,H,r)
\iff
\forall h\in H,\ \gcd(r+h,W)=1.
\]

The finite residue set is
\[
R_{H,W}
=
\{r<W:\operatorname{wheelAdmissible}(W,H,r)\}.
\]

The fixed-origin prefix count is
\[
P_{H,W}(b)
=
\#\{1\le r\le b:\operatorname{wheelAdmissible}(W,H,r)\}.
\]

The ordered three-point candidate correlation is
\[
C^{(3)}_{H,W}(s,t)
=
\#
\left\{
r<W:
\begin{array}{l}
a_{H,W}(r)=1,\\
a_{H,W}(r+s)=1,\\
a_{H,W}(r+t)=1
\end{array}
\right\},
\]
where the shifted representatives are reduced modulo \(W\).

For a nonzero modulus, the Lean file works in \(ZMod\,W\). It defines
\[
A_+(a)\iff \operatorname{IsUnit}(a)\land
\operatorname{IsUnit}(a+2)\land
\operatorname{IsUnit}(a+6),
\]
\[
A_-(a)\iff \operatorname{IsUnit}(a)\land
\operatorname{IsUnit}(a+4)\land
\operatorname{IsUnit}(a+6),
\]
and the affine reflection
\[
\rho_W(a)=-a-6.
\]

## Finite wheel audit

The finite arithmetic audit gives
\[
R_{H_+,30}=\{11,17\},\qquad
R_{H_-,30}=\{7,13\},
\]
hence
\[
P_{H_+,30}(10)=0,\qquad P_{H_-,30}(10)=1.
\]

After the \(7\)-layer is added,
\[
C^{(3)}_{H_+,210}(6,30)=1,\qquad
C^{(3)}_{H_-,210}(6,30)=0.
\]
For \(0<s<t<30\), the corresponding \(W=210\) candidate triple counts vanish
for both orientations. These are finite wheel certificates used by the theory audit.
They are not statements about the infinitude, density, or asymptotic distribution of
prime triplets.

## Machine-checked general theorem

The Lean declarations in
D5/S3/Arith/PrimeTripletWheel.lean are:

- reflected_gapDifference;
- reflect_involutive;
- plus_reflect_iff;
- reflectEquiv;
- candidate_space_card_eq.

The general direction declaration uses the integer gap difference
\[
d(g_1,g_2)=g_2-g_1
\]
and proves that reversing the ordered gaps negates the direction. The concrete
templates in the finite audit use the normalised theory convention
\(\chi=(g_2-g_1)/2\), with values \(+1\) and \(-1\). If the unnormalised
integer difference is used instead, its values are \(+2\) and \(-2\).

The pair-distance object in the original finite audit is an unordered distance
support, a Finset, rather than a multiplicity-sensitive multiset. In this
diameter-six example both templates have support \(\{2,4,6\}\).

The central general result is
\[
A_+(a)\iff A_-(\rho_W(a)),
\qquad
\rho_W(\rho_W(a))=a.
\]
Therefore \(\rho_W\) induces an equivalence
\[
\{a: A_+(a)\}\simeq \{a:A_-(a)\}
\]
and
\[
\#\{a:A_+(a)\}=\#\{a:A_-(a)\}
\]
for every nonzero modulus \(W\). The result is a candidate-space cardinality
symmetry. It does not identify the two origin-fixed prefix functions, and it does
not identify the labelled three-point correlations once an observation chart or a
translation quotient is fixed.

## Relation to the pyramid fiber

The wheel candidate results provide a finite arithmetic readout. The AURIC pyramid
provides the corresponding hidden-fiber readout. Equal three-dimensional marginal
coordinates can coexist with different joint coordinates \(\kappa\). The \(30\)-layer
and \(210\)-layer therefore refine different parts of the observation kernel:

- modulus \(30\) separates an absolute-origin chart;
- modulus \(210\) separates an ordered three-point direction after the earlier
  translation symmetry is quotiented;
- pairwise candidate readout remains degenerate at the selected witness;
- the general reflection theorem preserves total candidate cardinality while allowing
  chart-dependent escape at a fixed prefix or labelled span.

The arithmetic layer is consequently a typed observation interface for the pyramid:
candidate density is a marginal-like quantity, the origin or span label is a chart
coordinate, and the ordered three-point direction is a hidden fiber coordinate until
a three-point readout resolves it.

Actual prime-triplet counting is intentionally outside this theorem package. A later
analytic layer may connect the finite wheel predicates to prime indicators, but that
connection requires its own hypotheses and proof.
