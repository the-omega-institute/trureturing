# Prime Triplet Wheel

## Abstract

This module formalizes the finite arithmetic layer behind the two diameter-six templates
\[
H_+=\{0,2,6\},\qquad H_-=\{0,4,6\}.
\]
It separates three finite observables: ordered gap chirality, unordered pair distances, and wheel candidate correlations. The checked witness is
\[
P_{H_+,30}(10)=0,\qquad P_{H_-,30}(10)=1,
\]
together with
\[
C^{(3)}_{H_+,210}(6,30)=1,\qquad
C^{(3)}_{H_-,210}(6,30)=0.
\]
The first is an origin-sensitive separation at modulus \(30\); the second is a fixed-span three-point separation after the \(7\)-layer is added. The formalization concerns finite wheel candidates only. It makes no assertion about the infinitude or asymptotic count of actual prime triplets.

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
\#\left\{
r<W:
\begin{array}{l}
a_{H,W}(r)=1,\\
a_{H,W}(r+s)=1,\\
a_{H,W}(r+t)=1
\end{array}
\right\},
\]
where additions in the second and third terms are reduced modulo \(W\).

## Machine-checked finite results

**Theorem 1 (ordered gap chirality).** With
\[
\chi(a,b,c)=(c-b)-(b-a),
\]
the two templates satisfy
\[
\chi(0,2,6)=2,\qquad \chi(0,4,6)=-2.
\]

**Theorem 2 (same unordered pair distances).**
\[
\{2,4,6\}
=
\{|h_i-h_k|:i<k\}
\]
for both templates.

**Theorem 3 (origin-sensitive modulus-30 separation).**
\[
R_{H_+,30}=\{11,17\},\qquad
R_{H_-,30}=\{7,13\},
\]
and therefore
\[
P_{H_+,30}(10)=0,\qquad P_{H_-,30}(10)=1.
\]

**Theorem 4 (translation-invariant three-point witness).**
\[
C^{(3)}_{H_+,210}(6,30)=1,\qquad
C^{(3)}_{H_-,210}(6,30)=0.
\]

**Theorem 5 (first positive witness).** For \(0<s<t<30\), the corresponding \(W=210\) candidate triple counts vanish for both templates. Thus the \((6,30)\) witness is the first positive-span certificate in this finite window.

The Lean declarations are in
D5/S3/Arith/PrimeTripletWheel.lean:

- tripletPlus_chirality
- tripletMinus_chirality
- triplet_pairDistances_equal
- wheelResidues_30_plus
- wheelResidues_30_minus
- wheelPrefix_30_separates
- wheelTriple_210_separates
- wheelTriple_no_smaller_positive_span

## Relation to the pyramid fiber

The wheel candidate results provide a finite arithmetic readout. The AURIC pyramid provides the corresponding hidden-fiber readout. Equal three-dimensional marginal coordinates can coexist with different joint coordinates \(\kappa\). The \(30\)-layer and \(210\)-layer therefore refine different parts of the observation kernel:

- modulus \(30\) separates an absolute-origin chart;
- modulus \(210\) separates an ordered three-point direction after quotienting by the earlier translation symmetry;
- the pairwise candidate readout remains degenerate at the selected witness.

Actual prime-triplet counting is intentionally outside the theorem package. The finite wheel statements can be used as certified observations when a later model adds empirical or analytic prime data.
