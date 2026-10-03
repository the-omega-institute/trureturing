# Filaseta–Kalogirou excess and the owner/flow interface

The Filaseta–Kalogirou result is a useful whole-cover input, but its reciprocal
excess and bounded-overlap conclusions do not yet supply a source-preserving
lower bound for the private-point flow, the shared-route cost \(\Lambda_H\), or
an EB1 replacement. The obstruction is a mismatch of supports and of what the
three quantities remember. This records the exact interface and the missing
obligation.

The cited source is the author version of [Filaseta–Kalogirou](../../../../../../Library/Arith/filaseta2026reciprocalgap.md). The private-point notation is that of
[report 385, §§233–238](385-private-congruence-hulls-and-crossed-modulus-closure.md),
and the original-Haar overlap accounting is in [report 347](../../321-384/347-original-overlap-leakage-gives-a-uniform-reciprocal-gap.md).

## 1. What the reciprocal-excess theorem actually gives

Let
\[
  C_i=[a_i]_{m_i},\qquad
  \mu=\text{uniform measure on }\mathbb Z/Q\mathbb Z,
  \qquad L(x)=\sum_i\mathbf 1_{C_i}(x),
\]
where the moduli are finite, distinct and odd, and suppose the classes cover
\(\mathbb Z\). Then
\[
  H_{\rm cov}:=\sum_i\frac1{m_i}-1
       =\int (L-1)_+\,d\mu.
  \tag{FK1}
\]
The equality uses whole coverage. Filaseta–Kalogirou supplies a positive
uniform lower bound for this scalar and, in the odd specialization, a positive
lower bound for an original-Haar union of cross-largest-prime overlap events.
It also supplies at least one intersecting pair of original classes with
bounded numerical moduli.

These are statements about the original labels and the original Haar law. They
retain the original phases, but they do not select an owner, a private point,
a hole fibre, or a continuation operation. In particular, the bounded pair
need not be a reciprocal private-hull pair.

## 2. The exact owner-partition translation

Choose any measurable owner partition \((P_i)_i\) of the covered carrier with
\(P_i\subseteq C_i\) and the \(P_i\) disjoint. Put
\[
 d_i=\mu(C_i\setminus P_i).
\]
Every point with multiplicity \(L(x)\) contributes exactly \(L(x)-1\) to
\(\sum_i d_i\), independently of the owner rule. Hence
\[
 \sum_i d_i=H_{\rm cov},
 \qquad
 H_{\rm cov}=\int_{\{L\ge2\}}(L-1)\,d\mu.
 \tag{FK2}
\]
If \(G\) is any of the Filaseta–Kalogirou overlap unions, then
\[
 G\subseteq\{L\ge2\},
 \qquad \mu(G)\le H_{\rm cov}.
 \tag{FK3}
\]
At a point of \(G\), at least one active label is a non-owner, so the same
inequality also follows from the owner deficits. There is no converse: a lower
bound on \(H_{\rm cov}\) does not give a lower bound for any specified owner
atom or for a complete two-owner region
\[
 K_{i,j}=(C_i\cap C_j)\setminus\bigcup_{k\ne i,j}C_k.
\]
An FK intersecting pair may have every point of its intersection covered by a
third label, and its moduli may be coprime or incomparable. Thus its positive
intersection mass does not produce \(\mu(K_{i,j})>0\).

## 3. Why this does not feed the private-point flow

For a fixed internal period \(H\), report 385 routes each external label through
an actual hole fibre \(r\in U_H\) and an actual private bucket point \(t\). A
saturated flow \(z\) has coordinate cost
\[
 \Gamma_H(z)=\sum_v(p(v)-1)|R_v(z)|,
\]
and the shared-route relaxation is
\[
 \Lambda_H\le\Gamma_H(z)\le\mathcal B_H.
 \tag{FK4}
\]
The sets \(\mathsf E_i(H)\), capacities \(M_{v,r}\), and common-route condition
in \(\Lambda_H\) depend on the original phase of each label and on which
private buckets survive on each \(H\)-fibre. None of them is determined by the
single scalar (FK1) or by the FK bounded pair.

There is also a literal support separation at the prime-bucket level. With
\(O_p\) the original union of earlier-largest-prime buckets and
\(F_p=B_{\min,p}\cap O_p\) the FK overlap event,
\[
 F_p\subseteq O_p,
 \qquad U_p:=O_p^c,
 \qquad F_p\cap U_p=\varnothing.                 \tag{FK5}
\]
Every law \(\nu_p\) supported on the pre-stage survivor \(U_p\) therefore has
\(\nu_p(F_p)=0\), even when \(\mu(F_p)>0\). A killed or conditioned source law
cannot inherit the positive original-Haar overlap mass by restriction. This is
the same support issue that prevents replacing an original-Haar overlap by a
private-fibre source in §347.

A flow bucket is component-private; after choosing the remaining component
coordinates in its capacity product it yields a global private witness (a point
of multiplicity one). Thus the flow sinks live on the private stratum, whereas
(FK1) and the FK overlap events live on multiplicity at least two. A
source-preserving bridge would have to transport between these strata while
retaining every label, phase, and capacity. No such transport is supplied by
Filaseta–Kalogirou or by (FK2).

## 4. Why the bounded pair does not give an EB1 replacement

An EB1 replacement needs more than two intersecting classes. A valid move must
preserve whole coverage and numerical distinctness while reducing the selected
lexicographic cost. Existing reciprocal-hull moves require a compatible private
hull, a nonempty complete owner region, and receiving labels whose phases and
moduli do not collide. Filaseta–Kalogirou gives only
\[
 C_i\cap C_j\ne\varnothing,
 \qquad m_i,m_j\le K
\]
for some pair. It does not give any of:

* a noncoprime divisibility relation or the required reciprocal hull;
* a complete two-owner region \(K_{i,j}\);
* receiving descendants at the rephased modulus;
* a collision-free replacement using the same original source.

Consequently the implication
\[
 \text{FK bounded intersecting pair}
 \Longrightarrow
 \text{strict EB1 replacement}
 \tag{FK6}
\]
is not established. The owner identity (FK2) cannot repair (FK6): it counts
all non-owner mass and does not identify a legal replacement packet.

## 5. The exact bridge still required

To combine the two lines of work, one needs a theorem with all of the following
quantifiers in one common CRT source:

1. Under the whole-cover and EB1 hypotheses, select an FK overlap atom (or a
   positive-mass family of them) whose original labels and phases are retained.
2. Map that atom to actual \((r,t)\) flow edges, with \(r\in U_H\), preserving
   the private-fibre phase sets \(\mathsf E_i(H)\) and the capacities
   \(M_{v,r}\).
3. Prove that the map is capacity-safe and yields a strict lower bound on the
   same \(\Lambda_H\) that appears in (FK4), or else construct a collision-free
   EB1 replacement from the same labels.
4. Keep the source law explicit: original Haar mass cannot be silently replaced
   by a killed survivor law or by independently optimized conditional laws.

The available results prove each side separately but do not prove this joint
transport. The finite controls in report 385 §234–§235 and the cross-pair
Haar controls in report 842 show why local payment inequalities without the
whole-cover transport cannot serve as that bridge. Therefore the current
conclusion is a precise open obligation, not a reciprocal-excess proof of
noncoverage and not a counterexample to Erdős #7.
