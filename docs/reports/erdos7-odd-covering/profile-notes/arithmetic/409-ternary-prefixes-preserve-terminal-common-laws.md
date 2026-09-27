[Index](../../marked_head_profile.md) · [Actual root-fibre laws](406-actual-root-fibres-admit-one-law-below-the-target.md) · [Balanced selection and its boundary](408-a-balanced-five-tree-selection-controls-all-heights.md)

# Ternary prefixes preserve terminal laws under two finite budgets

One actual probability can be assembled from independently varying
terminal probabilities under a complete ternary prefix tree. Two
finite numerical budgets suffice to preserve the original-label
second-moment target through arbitrarily many prefix levels. Applied
to the concentrating sources of report 408, this gives a strict
all-height bound even where every balanced five-tree selection fails.

These are ordinary analytic proofs and exact research constructions,
not Lean-certified results. The assumptions below concern actual
supported terminal probabilities; their existence is not inferred
for arbitrary admissible sources. Unrestricted Erdős #7 remains open.

## One supported law with independently varying tails

Let `h>=0`, `d>=1`, and `K=h+d`. Let `P` be the leaves of an actual
complete ternary tree of depth `h` in the seven-adic prefix tree,
with low digits first. Thus `|P|=3^h`, and every selected prefix at
depth `a<=h` has exactly `3^(h-a)` descendants in `P`.

For each `u in P`, let `eta_u` be an actual probability on a possibly
different subset of `{1,2,3,4} x Z/7^d`. Require its embedded support

\[
 i_u(r,y)=(r,u+7^h y)
\]

to lie in the given global source `R`. Different tails may have
different supports, row marginals and probabilities. Prefix-preserving
tail relabellings and independent row permutations are allowed, provided
the bounds below hold for the resulting actual probabilities.

Suppose uniformly in `u` that every row has mass at most `beta`, and
that for `1<=j<=d` every pure prefix of depth `j` has mass at most
`m_j` and every row/prefix cell has mass at most `c_j`. All these
probabilities are chosen before the adversary chooses layout phases.
Define

\[
 \nu=3^{-h}\sum_{u\in P}(i_u)_*\eta_u.
 \tag{TP1}
\]

The components have disjoint prefix supports, so this is one probability
supported on `R`. At depth `0<=a<=h`, every pure prefix has mass at most
`3^(-a)` and every row/prefix cell has mass at most `beta*3^(-a)`.
Indeed the prefix contains `3^(h-a)` terminal components, each of
total mass `3^(-h)` and each with conditional row mass at most `beta`.
At depth `h+j`, the corresponding caps are `3^(-h)*m_j` and
`3^(-h)*c_j`, since that prefix meets at most one terminal component.

Retain the independent original divisor labels
`1,5,7,35,...,7^K,5*7^K`. For an assignment `a_q mod q` to each
label, write

\[
 D(x)=\sum_{q\mid5\cdot7^K}{\bf1}_{x\equiv a_q\pmod q},
 \qquad
 \Gamma_{1,K}(\nu)=\max_{(a_q)}\mathbb E_\nu[D^2].
 \tag{TP2}
\]

Here `R` is identified by CRT with the selected four rows in the
five-coordinate and the seven-coordinate. A phase in the unused fifth
row simply gives an empty event. Distinct labels retain independent
phases even when their intersections have the same LCM.

At maximum seven-adic depth `a`, there are `2a+1` ordered depth
pairs. The pure/pure type is bounded by the pure-prefix cap and
the other three types by the row/prefix cap. Incompatible phases
give empty intersections. Expanding the square under TP1 therefore gives

\[
 \Gamma_{1,K}(\nu)\le U_h
 :=A S_h(1/3)+3^{-h}\sum_{j=1}^{d}(2h+2j+1)b_j,
 \tag{TP3}
\]

where

\[
 A=1+3\beta,\qquad b_j=m_j+3c_j,\qquad
 S_h(1/3)=\sum_{a=0}^{h}(2a+1)3^{-a}
 =3-(h+2)3^{-h}.
\]

This includes `h=0` and the depth-zero row contribution. All intersection
bounds concern the same probability TP1.

## Two finite budgets suffice at every prefix height

Put

\[
 B=\sum_{j=1}^{d}b_j,\qquad
 C=\sum_{j=1}^{d}(2j+1)b_j,\qquad z=3^{-d}.
\]

The finite target is `2t_K=6-2(K+2)/3^K`. Direct subtraction gives

\[
 2t_{h+d}-U_h
 =3(2-A)+3^{-h}
 \left[h(A-2B-2z)+2A-C-2(d+2)z\right].
 \tag{TP4}
\]

Consequently the finite interface

\[
 \boxed{
 \beta\le\frac13,\qquad
 A-2B\ge2z,\qquad
 2A-C\ge2(d+2)z
 }
 \tag{TP5}
\]

suffices for `Gamma<=2t_(h+d)` for every `h>=0`. The comparison is
strict if `beta<1/3`, or if the bracket in TP4 is strictly positive
at the stated height. These are sufficient envelope conditions, not
necessary conditions on a good law. Failure of TP5 does not prove
failure of the source minimax comparison.

## A two-level tail gives a uniform strict margin

The selected 25-leaf probability on the 28-point source in report 408 has

\[
 \beta=\frac8{25},\qquad
 (m_1,c_1)=\left(\frac15,\frac4{25}\right),\qquad
 (m_2,c_2)=\left(\frac1{25},\frac1{25}\right).
 \tag{TP6}
\]

For this profile,

\[
 A=\frac{49}{25},\quad B=\frac{21}{25},\quad C=\frac{71}{25},
 \qquad A-2B-\frac29=\frac{13}{225},
 \qquad 2A-C-\frac89=\frac{43}{225}.
\]

Thus every prefix height satisfies

\[
 \boxed{
 \Gamma_{1,h+2}(\nu)\le U_h
 =\frac{147}{25}-\frac{7h+27}{25\,3^h}
 }
 \tag{TP7}
\]

and the exact finite margin is

\[
 \boxed{
 2t_{h+2}-U_h
 =\frac3{25}+\frac{13h+43}{225\,3^h}>\frac3{25}.
 }
 \tag{TP8}
\]

The limiting upper bound is `147/25<6`; TP8 establishes the stronger
finite-height comparison directly.

## The balanced-selection boundary still admits a good law

Report 408 constructs sources `R_h` by starting with its 28-point
height-two source and adding, at each new root, three continuing
copies and two private full-five trees in a fixed dominant row.
The continuing columns `0,1,2` at all `h` levels form an actual
complete ternary prefix tree. Every terminal prefix contains a copy
of the original height-two source.

Use its selected 25-point probability in each terminal fibre, with
mass `3^(-h)` per fibre, and give zero mass to the added private
pieces. TP6--TP8 apply for every `h`. At `h>=2`, report 408 shows
that no uniform full-five selection on this source meets its balance
criterion. Nevertheless TP1 is an actual common law below the finite
target. This settles that particular family, not all admissible sources.

The same proof permits independently varying terminal probabilities
and tail embeddings satisfying TP6. Neither independence of the row
and seven-coordinate within a tail nor equality of the tails is assumed.

## Exact controls and existing-result boundary

[ternary_prefix_tail_common_law.py](../../frontier/cover-geometry/ternary_prefix_tail_common_law.py)
provides a general profile test, actual-law constructor and verifier,
and the boundary-family consumer. The profile interface accepts arbitrary
positive tail depth. Its exact controls include independently relabelled
tails, a distinct depth-one profile, and 24 malformed-input rejections.
Validation remains active with Python optimization enabled.

For prefix heights `0,1,2,3`, the boundary sources have
`28,134,652,3206` points and the laws have `25,75,225,675` positive
atoms. The exact upper bounds and margins are

| Prefix height | Bound | Target margin |
| --- | --- | --- |
| 0 | `24/5` | `14/45` |
| 1 | `407/75` | `137/675` |
| 2 | `1282/225` | `104/675` |
| 3 | `1307/225` | `811/6075` |

These controls check the implementations; TP1--TP8 prove the all-height
claims. The shared tree API validates actual prefix inclusion.

Report 376 transports common tree caps across prime coordinates;
report 393 repeats a two-coordinate paired-digit seed; reports 397
and 406 use stationary or one-root mixtures under different source
conditions. The original-label LCM shell count is reused here.
The additional interface is the explicit finite pair of budgets `B,C`
preserved through an arbitrarily long actual ternary prefix. No claim
of literature originality is made. The unrestricted source-law theorem
and Erdős #7 remain unresolved.
