[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

<a id="literal-pure-classes-and-six-vertex-residue-branches"></a>
# Literal classes 5 and 15 pay three branches of every six-vertex block

Let an original finite congruence family have pairwise distinct odd
moduli greater than 1. If every block of its prime-interaction graph
has at most six vertices, the family is noncovering under any of the
following conditions:

1. The literal original modulus 5 is absent.
2. The literal original modulus 15 is absent.
3. Both are present and their residues agree modulo 5.

All original finite prime-power heights, residues, and complete supports
are retained. Absence of modulus 5 allows moduli 25, 125, and all other
original labels. Absence of modulus 15 allows 45, 75, and all other
original labels. The third condition does not require the residue of
15 to agree with any pure-3 class.

The result strengthens the existing conditional-kernel fees on all fifty
root-3 child-prime sets left by
[Chapter 25](25-six-vertex-block-fees-and-a-finite-prime-core-frontier.md).
The other six-vertex sets and every legal non-3 orientation are already
paid there. This is an ordinary mathematical argument with exact rational
checks, not a Lean-certified result. The unrestricted problem remains
open: the fifty sets with both literal classes present and different
mod-5 residues, and unrestricted larger dense blocks, are not paid here.

## 1. Preserve the actual pure-class union in the recursive invariant

Use the unchanged fee schedule of
[Chapter 23](23-conditional-kernels-and-recursive-block-noncoverage.md):
\[
 f(5)=\frac7{24},\quad f(7)=\frac18,\quad f(11)=\frac1{24},\quad
 f(13)=\frac1{48},\qquad f(q)=2^{-(q-1)/2}\quad(q\ge17),
 \tag{LP1}
\]
with \(c_5=3/10\) and \(c_q=2/(q-1)\) for \(q\ge7\).
Components containing 3 are rooted at 3. All children are at least 5.
For \(q\ge5\), let \(P_q\) be the actual union of original pure-\(q\) classes,
\(D_q\) the actual strict descendant prime set, and
\(e_q=\sum_{r\in D_q}f(r)\). The actual full coordinate domain
\(V_q\), including extension through strict descendants, satisfies
the strengthened invariant
\[
 H_q(V_q)\ge 1-H_q(P_q)-c_qe_q.
 \tag{LP2}
\]

This strengthening follows from the exact recursion, not from the
weaker numerical invariant (CK4) alone. At a leaf it is immediate.
For a parent, its domain is its full coordinate space minus \(P_q\)
and the outgoing block blockers. The outgoing assigned child-prime
charges are disjoint subsets of \(D_q\). The local blocker fees and
the union bound therefore return (LP2). Conversely, original numerical
distinctness gives
\[
 H_q(P_q)\le\sum_{a\ge1}q^{-a}=\frac1{q-1},
\]
so (LP2) supplies (CK4) to every inherited local theorem. Those local
estimates return (LP2) at non-3 parents. The new root-3 estimates below
require (LP2) at children and complete the separate root union bound
in Section 3. Finite bottom-up induction consequently closes without
assuming an improved pure-class budget before its premise is verified.

For a remaining five-child tuple \(J\) in Chapter 25, put
\[
 M=\sum_{q\in J}f(q),\qquad E=\frac{187}{384}-M,
 \qquad d_q=1-\frac1{q-1}-c_qE,
 \qquad b_q=\frac1{(q-1)d_q}.
 \tag{LP3}
\]
All fifty tuples contain 5 and 7. Each actual descendant expense is at
most \(E\), because the descendant sets avoid the current block and
the total prime fee is at most \(187/384\). The simultaneous choices
\(e_q=E\) only provide a dominating rectangle; they do not spend the
same external prime fee several times in an actual system. The improved
total bound \(1493/3072\) of Chapter 25 is not needed for the local
computations in this chapter.

For \(\varnothing\ne S\subseteq J\), write
\(b_S=\prod_{q\in S}b_q\). At parent cutoff \(t=1\), the baseline
support weights are \(b_q\) on singletons and \(2b_S\) on larger
supports: one mixed contribution from old internal classes and one
from the matching parent-exponent-1 classes. These weights bound the
original event unions under the product of the actual child-domain laws.

## 2. Two changes to the same conditional-kernel calculation

If literal modulus 5 is absent, (LP2) and distinctness give
\[
 H_5(P_5)\le\sum_{a\ge2}5^{-a}=\frac1{20},\qquad
 H_5(V_5)\ge d_5+\frac15.
 \tag{LP4}
\]
Replace \(b_5\) by
\[
 b'_5=\frac1{4(d_5+1/5)},
 \tag{LP5}
\]
and leave the other coordinate caps unchanged. Use products \(b'_S\)
both in the shallow support weights and in the deep cofactor budgets.
No remaining original class is removed by this estimate.

For either of the other two literal conditions, keep the baseline
densities and all deep budgets \(b_S\). At parent exponent 1, the
singleton-5 cofactors are \(5,25,125,\ldots\). The leading cofactor
5 is exactly the original modulus 15. If that label is absent, its
event is absent. If its residue agrees modulo 5 with the present
pure class 5, its child cylinder is empty on the actual \(V_5\).
This holds for every full parent word and for the label's actual
mod-3 residue. Thus the singleton-5 shallow weight improves to
\[
 \frac1{d_5}\sum_{a\ge2}5^{-a}=\frac{b_5}{5}.
 \tag{LP6}
\]
Other singleton weights remain \(b_q\), mixed weights remain
\(2b_S\), and all original deep labels remain charged to their full
original cofactor budgets. In particular this does not discard all
labels divisible by 15.

Here is the common probability transfer, including its joint-law
requirement. Let
\(\nu=\bigotimes_{q\in J}H_q(\,\cdot\mid V_q)\). For each full
parent word \(x\), let \(R_x\) avoid the actual old internal classes
and the actual parent-exponent-1 classes matching \(x\). Group these
events by complete support, and use the applicable dominating vector
\(v\) just specified. Define the residual polynomial by
\[
 Z_A(v)=\sum_{\substack{\mathcal F\text{ an unordered family of}\\
                 \text{pairwise-disjoint nonempty subsets of }A}}
                 (-1)^{|\mathcal F|}\prod_{S\in\mathcal F}v_S,
 \qquad Z_\varnothing=1.
 \tag{LP7}
\]
For both modifications on every one of the fifty tuples, the exact
certificate verifies \(Z_A(v)>0\) for all 31 nonempty \(A\subseteq J\).
As in (CK8), the support-intersection Shearer atoms then certify every
induced support graph polynomial, not only the top residual.

The conditional inequality used in (CK10), namely Scott--Sokal
Theorem 4.1(a), equation (4.3), gives \(\nu(R_x)>0\) and, for an actual
deep child cylinder \(C\) with complete support \(S\),
\[
 \nu(C\mid R_x)\le \nu(C)\frac{Z_{J\setminus S}(v)}{Z_J(v)}.
 \tag{LP8}
\]
This uses the actual survivor kernel at the same \(x\). It does not
replace that joint law by a fixed child law independent of the parent.
For a wholly blocked \(x\), the original deep labels cover \(R_x\).
Integrating this necessary load over the original parent Haar marginal,
and counting each original full cofactor at most once at each parent
exponent, gives
\[
 H_3(B)\le K(v,b):=
 \frac{\sum_{\varnothing\ne S\subseteq J}
                  b_S Z_{J\setminus S}(v)}{6Z_J(v)}.
 \tag{LP9}
\]
In the missing-5 branch substitute \(b'_S\) for \(b_S\).
Here \(B\) is the block-only blocker before deleting pure-3 classes,
and \(1/6=\sum_{a\ge2}3^{-a}\) bounds the actual finite parent-depth
sum. If the original parent height is 1, there are no deep labels;
the same argument has zero actual deep load. No height truncation is
imposed on any original coordinate.

## 3. Every one of the fifty remaining prime sets pays its fee

The finite certificate applies both modifications to exactly the
`remaining_root3_tuples` of Chapter 25. It proves
\[
 K(v,b)<M
 \tag{LP10}
\]
in all 100 evaluations, and equality of the two modified estimates
for each tuple. The unique largest cost-to-fee ratio occurs at
\(J=(5,7,11,13,17)\) and equals
\[
 \frac{36076675217866752}{39401015219888225}<1.
 \tag{LP11}
\]
For this tuple the original conservative budget gives
\[
 M=\frac{371}{768},\quad E=\frac1{256},\qquad
 d=\left(\frac{1917}{2560},\frac{213}{256},\frac{1151}{1280},
          \frac{469}{512},\frac{1919}{2048}\right),
\]
\[
 b=\left(\frac{640}{1917},\frac{128}{639},\frac{128}{1151},
          \frac{128}{1407},\frac{128}{1919}\right).
\]
The missing-5 branch replaces \(d_5\) by \(2429/2560\) and \(b_5\)
by \(640/2429\). The other branches replace only the singleton-5
shallow weight by \(b_5/5\). Both yield
\[
 K_* =\frac{328823862662848}{743415381507325},\qquad
 M-K_* =\frac{23270380014150311}{570943012997625600}>0.
 \tag{LP12}
\]
The minimum nonempty residuals are, respectively,
\[
 \frac{743415381507325}{4823616463291773},\qquad
 \frac{743415381507325}{3806864042869629}.
\]

Together with Chapter 25, (LP10) proves the opening noncoverage statement
by (LP2)'s bottom-up induction. The enlarged recursive class can also
contain any other block types with the same established local fee
invariant, including Chapter 23's large-child regime. The local literal
premise is needed only at a previously unpaid root-3 block. Since every
such block contains 3, 5, and 7, and distinct graph blocks share at most
one vertex, there is at most one such block in the entire graph.

The refined total budget from Chapter 25 still gives
\[
 H_3(V_3)\ge\frac{43}{3072},\qquad
 U_{\rm full}\ge\frac{43}{3072Q_{\rm off}}
 \tag{LP13}
\]
when prime 3 is present. Here \(Q_{\rm off}\) includes all original
non-3 prime-power coordinates in the entire family, including other
components. If 3 is absent, the original-coordinate witness construction
still gives an uncovered residue. The full-density estimate is not a
height-uniform positive constant, because \(Q_{\rm off}\) can grow.

## 4. The equality holds algebraically at every cutoff at least one

The equality in (LP12) is not particular to the fifty tuples. Fix a
child prime \(q\), put \(\beta=b_q=1/((q-1)d_q)\), and define
\[
 \delta=\frac{q-1}{q}\beta,\qquad \lambda=1+\delta.
 \tag{LP14}
\]
Removing the literal pure-\(q\) class from its worst pure-power budget
raises the density lower bound by \(1/q\), so its new cap is
\(\beta'=\beta/\lambda\). At any integer cutoff \(t\ge1\), compare
two changes to the same baseline \(v=w+tb\):

- Change I divides both \(b_S\) and \(v_S\) by \(\lambda\) whenever
  \(q\in S\), reflecting the improved coordinate density.
- Change R keeps all \(b_S\), but removes the literal shallow label
  \(pq\), reducing only \(v_{\{q\}}\) by \(\delta\), from
  \(t\beta\) to \((t-1+1/q)\beta\).

A disjoint support family contains at most one support containing
\(q\). Separating the terms using that coordinate proves, for
\(q\in A\),
\[
 Z_I(A)=\frac{Z_{\rm base}(A)+\delta Z_{\rm base}(A\setminus\{q\})}
                   {\lambda}
        =\frac{Z_R(A)}{\lambda}.
 \tag{LP15}
\]
If \(q\notin A\), both residuals equal the baseline residual. This
also proves equivalence of the two full strict-residual conditions.

For \(L=\sum_{S\ne\varnothing}b_SZ_{J\setminus S}\), each summand
is divided by \(\lambda\) under I relative to R: if \(q\in S\)
the product \(b_S\) scales and its residual does not; otherwise the
residual scales and the product does not. Consequently
\[
 L_I=L_R/\lambda,\qquad Z_I(J)=Z_R(J)/\lambda,
 \qquad \frac{L_I}{Z_I(J)}=\frac{L_R}{Z_R(J)}.
 \tag{LP16}
\]
The common parent factor \(1/[p^t(p-1)]\) is unchanged. This proves
identity of the two estimates whenever either strict region holds;
it does not assert strictness at every cutoff. At \(t=0\), the
literal label \(pq\) is not shallow, so this removal has no such
probability interpretation.

## 5. Exact certificate and prior structure

The standard-library program
[six_vertex_pure_residue_certificate.py](../frontier/cover-geometry/six_vertex_pure_residue_certificate.py)
and its [exact data](../frontier/cover-geometry/six_vertex_pure_residue_certificate.json)
consume the explicitly supplied Chapter 25 certificate. They check its
fifty distinct ordered prime tuples and record its SHA256. For both
modifications on every tuple, all 31 nonempty residuals are evaluated
by a coordinate recurrence and independently by enumeration of the
203 unordered disjoint-support families. Every row must have strict
residuals and cost strictly below its assigned fee; these are assertions,
not a printed success count. The data retain the complete tuples,
densities, caps, residuals, costs, fee margins, and both scaling vectors.

The program also checks (LP15)--(LP16) at the evaluated cutoff \(t=1\).
The arbitrary-cutoff conclusion is the algebraic proof above, not a
finite computational extrapolation. The actual-pure recursion and
conditional probability transfer likewise remain ordinary proofs.
Python 3.10 or later is required; optimized `-O` execution is rejected.
From the repository root run:

```sh
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/six_vertex_pure_residue_certificate.py --frontier docs/reports/erdos7-odd-covering/frontier/cover-geometry/six_vertex_conditional_kernel_certificate.json --output /tmp/six-vertex-pure-residue-certificate.json
```

The missing or incompatible original-cofactor mechanism and the need
for common actual conditional laws already occur in
[profile note 306](../profile-notes/257-320/306-common-actual-j-rows-restore-the-vanished-columns.md).
The increment here is the corresponding improvement to the present
conditional-kernel fees on the complete fifty-set frontier, the
actual-pure induction, and the exact ratio identity. The probability
tool is the existing Scott--Sokal conditional inequality cited in
Chapter 23, [arXiv:cond-mat/0309352v2](https://arxiv.org/abs/cond-mat/0309352v2).

The remaining literal branch has both original moduli 5 and 15 present
with different residues modulo 5. A product-law cylinder overlap need
not survive conditioning on the actual old classes. Paying that branch
requires a bound that retains collision, deletion, and cap slack under
one common law. This chapter supplies no such bound and no uniform fee
for unrestricted larger dense blocks.

There is a further limitation on interpreting these branches as progress
against a hypothetical extremal counterexample.
[Profile note 350](../profile-notes/321-384/350-extremal-paired-branch-and-source-support.md)
chooses a cover minimizing first its cardinality and then its modulus
sum. Its modulus set is divisor-closed, and classes with distinct
comparable moduli are disjoint. In any such family containing 15,
modulus 5 must therefore occur with a different mod-5 residue. The
missing-5 and same-residue branches do not newly exclude these extremal
families. The result here enlarges the proved recursive local class;
it does not remove the remaining extremal obstruction. Choosing an
extremal family and performing the cited prime compression are existence
reductions, not Haar-preserving transports of an arbitrary original
family or its conditioned laws.
