# CFMP provenance after Uemura (2026)

## Purpose

This note records a literature update without rewriting the historical
CFMP results. Soichiro Uemura, “Local combinatorial criteria for geometric
hyper-ideal triangulations via combinatorial Ricci flow,” arXiv:2609.34108v1
(28 September 2026), proves a valence-dependent invariant-box criterion.
The relevant primary statements are Theorem 4.2 (the classical parameter
C=2) and Theorem 5.5 / Corollary 5.9 (the parameterized boxes).

Uemura's C=2 criterion uses

  gamma_n = 6/(2+cos(2*pi/n)) - 1,
  b_n = 2 for 6 <= n <= 9,
  b_n = 1 + 8*(1-cos(2*pi/n))/(1+cos(2*pi/n)) for n >= 10,

with canonical box [gamma_v, b_v] on an edge of valence v. Only edges of
valence 6--9 require an angle-sum check; valence at least 10 is controlled
by the invariant-box argument.

## Exact scope comparison

The abstract barrier/co-volume mechanism is related to the proof in
CFMP_EIGHT_TRIANGLE_CLUSTERS.md and CFMP_DEGREE10_STAR.md, but the
canonical Uemura box is a different box. It must not be silently substituted
for the narrower heterogeneous boxes in those files.

The generic three-edge theorem with degree-eight lows and arbitrary high
degrees at least 12 is not a direct corollary of Uemura Theorem 4.2. For the
homogeneous three-star endpoint with adjacent high valences 12 and opposite
valence 12, the C=2 canonical endpoint

  phi(2,2,2,gamma_12,b_12,b_12)

is strictly greater than 1/sqrt(2), so the corresponding single angle is
strictly less than pi/4. Thus the generic theorem's incidence estimate
remains an independent certificate.

## The explicit degree-ten witness

The 16-tetrahedron witness in CFMP_DEGREE10_STAR.md has edge degrees
[8,8,8,8,8,8,10,38]. Its exact topology and heterogeneous box

  [11/8, 2] on degree 8,
  [11/10, 71/50] on degree 10,
  [1009/1000, 21/20] on degree 38

remain independent computed certificates.

Its geometric-existence conclusion is also covered by Uemura Theorem 4.2
after checking the actual occurrence data in Uemura's canonical box. For a
degree-eight target, the possible adjacent-high/opposite patterns reduce to

  (10,10;38), (10,38;38), (10,38;10), (38,38;38), (38,38;10).

Using the exact endpoint expression

  phi(2,b_n2,b_n3,gamma_m,b_n5,b_n6),

rational Taylor enclosures from 333/106 < pi < 355/113 give strict
lower-angle bounds (in the order of those five patterns)

  28*pi/125, 31*pi/125, 32*pi/125, 7*pi/25, 29*pi/100.

The six degree-eight edge stars in the explicit pairing have weighted sums
of these bounds

  (1037/500)*pi, (258/125)*pi, (1097/500)*pi,
  (213/100)*pi, (1093/500)*pi, (113/50)*pi,

all strictly greater than 2*pi. Theorem 4.2 then controls the degree-ten
and degree-38 edges automatically. This is a finite corollary check of
Uemura's criterion, not a claim that the heterogeneous box itself appears
in Uemura.

Accordingly, cite the explicit degree-ten theorem for its exact
heterogeneous endpoint certificate and explicit topology, while recording
its bare geometric-existence conclusion as independently re-verified by
Uemura's later criterion. No historical theorem statement is changed and no
priority claim is made against arXiv:2609.34108.

## Primary source

- Uemura, arXiv:2609.34108v1:
  https://arxiv.org/html/2609.34108v1
  (Theorem 4.2, Theorem 5.5, Corollary 5.9).

## 1. Canonical-box criterion on the original quotient

Keep a finite connected orientable ideal triangulation of a compact 3-manifold whose every boundary component has negative Euler characteristic and actual edge degrees at least six. Every occurrence is counted through the original face-generated edge quotient P. No label regularity, distinctness, or independently adjustable local lengths is assumed.

Uemura, arXiv:2609.34108v1, Condition5.4 and Theorem5.5 use one common C in (3/2,1+sqrt2]. For c_n=cos(2pi/n), write

    Gamma_n(C)=(C+2-c_n)/(C+c_n),
    B_n(C)=C                              (6<=n<=9),
    B_n(C)=1+2C^2(1-c_n)/(1+c_n)           (n>=10).

The canonical box is Q_C=product_e[Gamma_d(e)(C),B_d(e)(C)]. Lemma5.2 proves 1<Gamma_n<B_n<=C. Condition5.4 requires the actual total angle at each degree6--9 edge to exceed2pi for every box assignment on its upper face x_e=C. Theorem3.5 is separate: it requires minimum degree7 and at most two actual quotient labels in every tetrahedron meeting a degree7--9 edge. Those hypotheses cannot be inferred from the minimum-six assumption.

Primary source: [Uemura, arXiv:2609.34108v1](https://arxiv.org/html/2609.34108v1), Lemma 5.2, Condition 5.4 and Theorem 5.5. For actual group incidence, see [group transport](CFMP_GEOMETRIC_REALIZATION_GROUP_TRANSPORT.md), §§122–124.

## 2. Adjacent low-degree slots obstruct every allowed parameter

Suppose an actual edge e has degree d(e) in {6,7}. Suppose every one of the four adjacent local slots at every occurrence of e has global degree at most9. No bound is imposed on its opposite slots. Then Uemura Condition5.4 fails at e for every allowed C.

Proof. Define one global assignment, simultaneously for all labels, by

    x_f=B_d(f)(C).

This lies in Q_C by Lemma5.2. The target and all its adjacent slots read C. Every opposite value o satisfies 1<o<=C. In the standard order (12,13,14,34,24,23), each target occurrence therefore reads

    (C,C,C,o,C,C).

Direct substitution in the native six-variable cosine formula gives

    phi(C,C,C,o,C,C)
      = [2C^2-(C-1)o]/[C-1+2C^2]
      >= phi(C,C,C,C,C,C)=C/(2C-1).

The denominator is positive. The raw value is positive because o<=C, and is strictly less than1 because o>1. Thus clamping causes no ambiguity. Each actual target angle is at most

    beta(C)=arccos(C/(2C-1)).

For d(e)=6, C/(2C-1)>1/2 implies beta(C)<pi/3, so the total is strictly below2pi.

For degree7, beta is increasing in C. At C_max=1+sqrt2, its cosine is

    q=(3+sqrt2)/7.

Put c=cos(2pi/7). We have c>1/2 and

    p(c)=0,  p(x)=8x^3+4x^2-4x-1.

The identity follows from 1+2cos(2pi/7)+2cos(4pi/7)+2cos(6pi/7)=0. On x>=1/2, p'(x)=24x^2+8x-4>0. Also q>1/2 and

    p(q)=(-263+204sqrt2)/343>0,

since 2*204^2=83232>263^2=69169. Hence q>c, so beta(C)<=arccos q<2pi/7. Again the total angle is strictly below2pi. This proves failure of the full quantified static condition, not merely failure of a tabulated lower-angle estimate.

All repeated occurrences read the same global x_f. A high-degree label appearing as an opposite slot at one occurrence cannot create an inconsistency: the hypothesis only forbids that label in an adjacent slot anywhere in this particular target star. The same global assignment handles every occurrence simultaneously.

Consequently, if Condition5.4 holds for some allowed C, every degree6 or degree7 edge must have at least one actual occurrence with an adjacent degree>=10 slot. This is a necessary condition for this specific box criterion, not for geometricity.

## 3. Actual group-theoretic counterexample to automatic transfer

Use the existing group-transport construction §123.1, with twelve tetrahedra indexed0,...,11 and permutations

    U=(1,2,0,5,3,4,7,8,6,11,9,10),
    V=(0,2,8,7,6,10,1,5,4,3,9,11).

The complete face pairing is, for every index i,

    f_0(i) paired with f_3(U(i)), vertex map(3,0,1,2),
    f_1(i) paired with f_2(V(i)), vertex map(3,2,0,1),

with inverse maps on reverse faces. The group construction uses the transitive right action on C\A5, C generated by a5-cycle. Its low and high three-step returns have cycles

    low: (0 2)(1 8)(3 10)(4 7)(5 6)(9 11),
    high: (0 1 6)(2 3 4)(5 11 10)(7 9 8).

Each three-step return restores the ordered endpoints. Thus the actual quotient has six degree6 edges and four degree9 edges, with no edge reversal. The face maps are odd, the dual graph is connected, and the boundary-link theorem in §122 gives one closed orientable link with (V,E,F)=(20,72,48), hence genus3. These incidence and topology conclusions are those of group-transport §§122–123.

Every local slot has actual degree6 or9. The theorem applies at every degree6 edge, so no allowed C can satisfy Uemura's full Condition5.4 for this actual manifold triangulation. The separate local-bichromatic theorem cannot apply because the minimum degree is6. The unified symmetric/pair-min Corollary5.9 implies Condition5.4, so it also cannot certify this triangulation for any allowed C.

The triangulation is nevertheless geometric: the already proved role-balanced construction assigns

    x_low=(3+sqrt5)/2,  x_high=(1+3sqrt5)/4.

The exact role angle identities give2pi on the length-two low return circles and the length-three high return circles. This reuses the existing geometric theorem rather than claiming a new realization. As a separate consistency check, x_low>1+sqrt2, so this known solution lies outside every canonical Q_C. Indeed 1+sqrt5>2sqrt2 by squaring positive sides.

The regular A5 action in §123 likewise has sixty tetrahedra, thirty degree6 edges, twenty degree9 edges, and one genus11 boundary. It has the identical obstruction.

## 4. Unbounded family without changing any local degree

For the twelve-tetrahedron genus3-boundary manifold N, chi(N)=chi(boundary N)/2=-2. Connectedness, nonempty boundary and orientability imply b0=1,b3=0, hence b1=b2+3>=3. Its fundamental group therefore surjects onto Z and then onto Z/nZ for every n>=1. Take the associated connected ordinary n-sheeted covering and lift the actual ideal triangulation.

Every original edge star lifts without ramification: each lifted edge has the same complete local occurrence circle and the same degree6 or9 as its base edge. Each base open tetrahedron and open edge has n lifts, so the lifted triangulation has12n tetrahedra,6n degree6 edges and4n degree9 edges. Boundary components cover the original genus3 boundary, so all still have genus at least2. The lifted geometric metric realizes the same lifted triangulation. Its Euler characteristic is -2n, distinguishing the manifolds for distinct n.

Every lifted degree6 star still has only degree6/9 adjacent slots, so the complete canonical-box condition fails throughout this unbounded actual-manifold family, for every allowed C. This ordinary covering argument is distinct from the central group lift of §124, which changes return orders and is ramified at the original low edges.

## 5. Scope of the obstruction

Main §8 already shows a different failure of independent-opposite-endpoint certificates at degrees8/9. The existing Uemura provenance note handles a specific degree8/10/38 witness and a comparison at C=2. Here the obstruction concerns the full shared-quotient Condition5.4, all its allowed parameters, and retained minimum-six group/cover examples. It does not make a claim about every possible invariant box, Uemura's abstract invariant-box theorem3.2, or geometricity of unclassified minimum-six triangulations.
