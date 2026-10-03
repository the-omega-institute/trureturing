[Index](../../../marked_head_profile.md) · [Deep prime-prefix transport](375-deep-prime-prefix-projections-and-tree-contraction.md) · [Extremal source support](../../321-384/350-extremal-paired-branch-and-source-support.md) · [Private liability](385-private-congruence-hulls-and-crossed-modulus-closure.md)

# A source-global substitution has an unavoidable coupled collision

The deep prime-prefix transport in report 375 can be sharpened without
changing its source or phase contract. Fix a safe coordinate for one
smaller support prime and use one compatible rooted-tree embedding for the
larger prime at every original label. The pullbacks then cover a complete
new carrier and use fewer original labels. Consequently an EB1 extremizer
cannot have pairwise distinct output numerical moduli: every such common
source map has a collision. Averaging the collisions over the safe
coordinate and the common embedding gives an exact lower bound that keeps
the original phase correlations.

This is a structural obstruction and a quantitative target for the
remaining proof. It is not itself a contradiction: an upper bound below
one for the same collision moment, or a complete-liability repair for the
collisions, is still required.

## 1. Safe source coordinate and one common embedding

Assume a distinct odd whole cover exists and choose an EB1-minimal one,

\[
 \mathcal C=\{A_d=\alpha_d\pmod d:d\in D\},
 \qquad Q=\operatorname{lcm}(D).
\]

Use the divisor closure and comparable-class disjointness from report 350.
Choose support primes \(r<s\), write

\[
 Q=r^A s^B M,\qquad \gcd(M,rs)=1,
\]
and let

\[
 U_r=\{u\pmod {r^A}:
 u\not\equiv\alpha_{r^a}\pmod {r^a}\ (1\le a\le A)\}.
\]

The pure \(r\)-power classes are disjoint, so

\[
 \frac{|U_r|}{r^A}
 =1-\sum_{a=1}^{A}r^{-a}>0. \tag{SC1}
\]

Choose one compatible embedding of rooted digit trees

\[
 \theta_b:\mathbb Z/r^b\mathbb Z\hookrightarrow
 \mathbb Z/s^b\mathbb Z,
 \qquad 0\le b\le B,
\]

commuting with reduction. The image is obtained by choosing \(r\) children
at each selected node of the \(s\)-ary tree. The choices are shared by
all original labels; no phase is reselected per fibre.

For \(u\in U_r\), put \(N=r^B M\) and define one source map

\[
 F_{u,\theta}(z)\equiv
 \begin{cases}
 u&\pmod {r^A},\\
 \theta_B(z\bmod r^B)&\pmod {s^B},\\
 z&\pmod M.
 \end{cases} \tag{SC2}
\]

CRT makes this an injection from \(\mathbb Z/N\mathbb Z\) into the
original period. For an original label write

\[
 d=r^{a(d)}s^{b(d)}m(d),\qquad \gcd(m(d),rs)=1.
\]

Its pullback is empty unless

\[
 u\equiv\alpha_d\pmod {r^{a(d)}}
 \quad\text{and}\quad
 \alpha_d\bmod s^{b(d)}\in\operatorname{im}(\theta_{b(d)}). \tag{SC3}
\]

When nonempty, the pullback is one class of numerical modulus

\[
 \widehat d=r^{b(d)}m(d). \tag{SC4}
\]

The phase is forced by the inverse of \(\theta_{b(d)}\) modulo
\(r^{b(d)}\), together with the original phase modulo \(m(d)\). Thus all
surviving output classes have one original source.

The pure \(r\)-power labels are killed by \(u\in U_r\), so no surviving
pullback has modulus one. The source image is covered by the original
whole cover, hence all nonempty pullbacks cover \(\mathbb Z/N\mathbb Z\).
At least \(A\) original labels disappear, so there are fewer than
\(|D|\) output identities.

## 2. EB1 forces a collision in every common-source map

Group original labels by their output numerical modulus. For fixed \(b,m\),
let

\[
 \mathcal P_{b,m}=
 \{\{d,d'\}: d=r^a s^b m,\ d'=r^{a'}s^b m, a<a',\ r^b m>1\}.
 \tag{SC5}
\]

If every output numerical modulus had at most one surviving original,
the pullbacks would be a distinct odd nonunit whole cover with fewer than
\(|D|\) classes, contradicting the first EB1 coordinate. Therefore, for
every \(u\in U_r\) and every compatible \(\theta\), at least one pair in
\(\bigcup_{b,m}\mathcal P_{b,m}\) survives together:

\[
\boxed{\text{every common-source map has at least one output-label
 collision}.} \tag{SC6}
\]

Here a surviving pair means that both individual pullback classes are
nonempty under the same source map.  It does not require one source point to
satisfy both original congruences: the free \(M\)-coordinate can realize each
phase separately.  Different \(m\)-phases therefore remain different output
phases while still giving a numerical-modulus collision.

The collision is numerical, not a duplicate phase. If two surviving labels
in one \(\mathcal P_{b,m}\) had equal output phase, compatibility of the
same \(u\) gives equality of the original phases modulo \(r^a\), and the
common inverse image under \(\theta_b\) gives equality modulo \(s^bm\).
Thus \(A_{d'}\subseteq A_d\), contradicting irredundancy.

This uses the complete source image in (SC2), so it pays the whole covering
liability automatically. It does not select private points separately,
drop higher-owner strata, or replace the original phases.

## 3. A top-layer localization

Let

\[
 T_s=\{d\in D:v_s(d)=B\},\qquad
 L_s=\operatorname{lcm}\{d/s^B:d\in T_s\}.
\]

If \(r\nmid L_s\), every top-layer cofactor is \(r\)-free. Distinct top
labels then have distinct \(m(d)\), hence distinct output moduli
\(r^B m(d)\). A top output cannot collide with a lower output because the
\(r\)-exponents are respectively \(B\) and \(b<B\). Consequently (SC6)
strengthens to

\[
 \boxed{\text{for every }(u,\theta),
 \text{a collision occurs at some }b<B.} \tag{SC7}
\]

This condition is about the top cofactor palette, not absence of \(r\) from
the whole period. Initial-segment support does not imply \(r\nmid L_s\).

## 4. The exact coupled collision moment

Choose \(u\) uniformly from \(U_r\). Independently choose a compatible
embedding by taking a uniformly random \(r\)-subset of the \(s\) children at
each selected node. All labels use this one random tree.

For a pair \(d,d'\in\mathcal P_{b,m}\), define its exact safe-coordinate
factor

\[
 \rho_{d,d'}=
 \frac{|\{u\in U_r:
 u\equiv\alpha_d\pmod {r^a},\ u\equiv\alpha_{d'}\pmod {r^{a'}}\}|}{|U_r|}.\tag{SC8}
\]

Let \(w,w'\) be the original \(s^b\)-prefixes. If \(w=w'\), the probability
that both are in the common embedded tree is

\[
 \kappa_{r,s}(w,w')=\left(\frac rs\right)^b. \tag{SC9}
\]

If their first differing lowest-significant digit occurs after \(\ell<b\)
common digits, then the shared tree choice gives

\[
 \kappa_{r,s}(w,w')=
 \left(\frac rs\right)^\ell
 \frac{r(r-1)}{s(s-1)}
 \left(\frac rs\right)^{2(b-\ell-1)}. \tag{SC10}
\]

The middle factor is essential: the two distinct children must be selected
by the same \(r\)-subset. Treating the two paths as independent replaces
it by an incorrect product.

Define

\[
 \Psi_{r,s}(\mathcal C)=
 \sum_{\{d,d'\}\in\mathscr P_{r,s}}
 \rho_{d,d'}\,\kappa_{r,s}(w_d,w_{d'}), \tag{SC11}
\]

where \(\mathscr P_{r,s}=\bigcup_{b,m}\mathcal P_{b,m}\). Let \(X(u,\theta)\)
be the number of surviving collision pairs. By (SC6), \(X\ge1\) pointwise;
linearity of expectation therefore gives

\[
 \boxed{\Psi_{r,s}(\mathcal C)=\mathbb E[X]\ge1.} \tag{SC12}
\]

Under \(r\nmid L_s\), (SC7) gives the lower-layer version

\[
 \boxed{\sum_{\substack{\{d,d'\}\in\mathscr P_{r,s}\\b(d)<B}}
 \rho_{d,d'}\,\kappa_{r,s}(w_d,w_{d'})\ge1.} \tag{SC13}
\]

No independence between different pair events is used. The same source
coordinate and the same embedding create the joint law.

## 5. What this changes and what remains open

The useful new target is an upper bound

\[
 \Psi_{r,s}(\mathcal C)<1
 \tag{SC14}
\]

for at least one support-prime pair of every hypothetical EB1 cover. Such
an upper bound would contradict (SC12) and settle the cover by a genuine
whole-source argument. A different route is to retain the collision pairs,
cover their complete deleted liability, and prove strict EB1 descent.

The present moment is not an activation-budget lower bound. Its summands
are pairs of original labels, while the blocker budget in report 385 is
indexed by actual quotient atoms. Charging both without a proved map risks
double counting. Likewise, choosing a different safe \(u\) or a different
tree for each column proves only \(\forall\)column\(\exists\) choices, not
the required common \(\exists(u,\theta)\forall\)columns.

The result therefore narrows the unrestricted obligation to a source-global
collision estimate while retaining all original labels, phases, distinct
numeric moduli, and whole-cover quantifiers. It does not claim a
counterexample or a proof of Erdős #7.

## 6. Exact finite kernel check

The accompanying checker enumerates all compatible depth-one and depth-two
embeddings for small \(r<s\), and verifies (SC9)--(SC10) by exact rational
counting. It also verifies the factorization of a pair-survival probability
into the independent safe-coordinate factor (SC8) and the common-tree
factor. The divisor-closed local family in the
[follow-up checker](../../../frontier/cover-geometry/source-global-collision-moment/collision_moment_no_cap.py)
keeps equal cofactor phases as an explicit valid special case.
It is a kernel check for the new finite probability identity; it does not
instantiate the universal EB1 hypothesis or certify (SC12) for an unknown
cover.

## 7. Terminal siblings share one complete lower liability

Keep the original whole cover and common source of Section 1, and put
\(K=|D|\). Let \(u_0=\alpha_{r^A}\bmod r^A\),
\(v=u_0\bmod r^{A-1}\), and \(u_0=v+j_0r^{A-1}\).
For \(j\ne j_0\), put \(u_j=v+jr^{A-1}\). All these
\(r-1\) coordinates belong to \(U_r\): a lower pure power
matching \(v\) would contain the original pure \(r^A\) class,
contrary to comparable-class disjointness.

Fix one tree \(\theta\). Write \(d=r^{a_d}k_d\), where
\(k_d=s^{b_d}m_d\), and set
\(\pi(k_d)=r^{b_d}m_d=n_d\). On these cofactor divisors,
\(\pi\) preserves divisibility, gcd and lcm. When its
\(s\)-prefix survives, let \(C_d=\gamma_d\bmod n_d\)
be the forced cofactor output from SC3--SC4. Its phase does not depend
on the choice of a matching \(r\)-coordinate.

Let \(\mathcal L\) consist of original labels with \(a_d<A\),
\(\alpha_d\equiv v\pmod{r^{a_d}}\), and surviving
\(s\)-prefix. Let \(\mathcal T_j\) consist of labels with
\(a_d=A\), \(\alpha_d\equiv u_j\pmod{r^A}\), and surviving
\(s\)-prefix. The output of each actual source
\(F_{u_j,\theta}\) is literally
\(\mathcal L\sqcup\mathcal T_j\). Thus on
\(X=\mathbb Z/N\mathbb Z\),
\[
 E=X\setminus\bigcup_{d\in\mathcal L}C_d,
 \qquad E\subseteq\bigcup_{d\in\mathcal T_j}C_d
 \quad(j\ne j_0). \tag{SC15}
\]
The inclusion uses original whole coverage on each complete source
image. The lower family and its complement are shared, rather than
chosen separately for each sibling.

Put \(\mathcal T=\bigsqcup_{j\ne j_0}\mathcal T_j\).
The numerical outputs \(n_d\) are pairwise distinct on
\(\mathcal T\): \(n_d\) recovers \(k_d\) and therefore
the original label \(r^Ak_d\). Moreover,
\[
 |\mathcal L|+|\mathcal T|\le K-A. \tag{SC16}
\]
These are disjoint subsets of the original identities, and omit all
\(r,r^2,\ldots,r^A\). No output has modulus one. At every point
of \(E\), at least one supplier from each sibling is present, with
distinct numerical outputs. Deleting any at most \(r-2\) members
of the pooled top family therefore leaves all of \(E\) covered.

Use the same CRT formula to define the auxiliary map
\(F_{u_0,\theta}\), although \(u_0\notin U_r\). No nonpure
original of \(r\)-height \(A\) can have phase \(u_0\) on
that coordinate: it would be contained in the pure original.
Consequently
\[
 E=F_{u_0,\theta}^{-1}
       \bigl(\operatorname{Priv}(A_{r^A})\bigr). \tag{SC17}
\]
Here privacy is relative to the entire original family. The complete
terminal private fan is already available in
[report 385, Section 148](385-private-congruence-hulls-and-crossed-modulus-closure.md#148-complete-cofactor-private-fans-see-height-one-top-primes),
and terminal deletion liabilities in its
[Section 98](385-private-congruence-hulls-and-crossed-modulus-closure.md#98-terminal-singularity-forces-a-prime-singleton-and-one-occupied-ancestor).
SC15--SC17 connect that existing fan to one common-tree output family
and its original-label budget; no new general private-fan theorem is
being claimed.

## 8. A repaired lower family forces simultaneous occupied-slot ancestry

Suppose first that \(\mathcal L\) admits a full divisor matching:
choose distinct \(h_d>1\) with \(h_d\mid n_d\). Keep the
forced phases and put
\[
 \mathcal B=\{\gamma_d\bmod h_d:d\in\mathcal L\},
 \qquad H=\{h_d:d\in\mathcal L\}.
\]
Let \(\beta_h\) be the phase occupying \(h\). The family
\(\mathcal B\) covers the entire union of the lower classes.
Append all pooled top outputs with unoccupied numerical labels:
\[
 \mathcal F=\mathcal B\cup
       \{C_d:d\in\mathcal T,\ n_d\notin H\},
 \qquad |\mathcal F|\le K-A<K. \tag{SC18}
\]
All its moduli are distinct odd nonunits and divide \(N\). If it
covered \(X\), it would cover all integers and contradict EB1.
Hence it has a hole \(z\). Containment of the lower union gives
\(z\in E\). Every top supplier at that same point satisfies
\[
 d\in\mathcal T,\ z\in C_d
 \ \Longrightarrow\
 n_d\in H,\quad
 \gamma_d\not\equiv\beta_{n_d}\pmod{n_d}. \tag{SC19}
\]
Otherwise its unoccupied output, or its occupied containing class,
would cover \(z\). This applies to every supplier, not merely a
choice of one per sibling.

Put \(x=F_{u_0,\theta}(z)\). By SC17 this is an actual private
point of the pure \(r^A\) class. Its complete terminal supplier
family is
\[
 \mathcal S(x)=\{r^Ak\in D\setminus\{r^A\}:
       \alpha_{r^Ak}\equiv x\pmod{r^{A-1}},\
       \alpha_{r^Ak}\equiv x\pmod k\}. \tag{SC20}
\]
Every member has a non-own terminal digit. Since \(x\)'s entire
\(s\)-path is in the fixed tree, every member survives that same
tree and covers \(z\) in the pooled output. SC15 gives
\(|\mathcal S(x)|\ge r-1\). Distinct top outputs and matched
slots induce an injection \(\Phi_x:\mathcal S(x)\to\mathcal L\),
where \(h_{\Phi_x(d)}=n_d\). In original coordinates it satisfies
\[
 \begin{gathered}
 d=r^Ak,\qquad \Phi_x(d)=r^ak',\qquad a<A,\qquad k\mid k',\\
 \alpha_{\Phi_x(d)}\equiv x\pmod{r^a},\qquad
 \alpha_{\Phi_x(d)}\not\equiv x\pmod k.
 \end{gathered} \tag{SC21}
\]
The divisibility follows by applying \(\pi^{-1}\) to the slot
inclusion. Agreement on a cofactor divisor is equivalent to agreement
on its substituted divisor: prefix compatibility and injectivity of
\(\theta\) give this on the prime-power coordinate, and the
\(M\)-coordinate is unchanged. SC19 therefore gives the last
inequality in SC21. The same source \(x\) and matching account for
the entire fan. This is not a lower bound of \(r-1\) on the
matching deficit of any single sibling source.

There is a finite sufficient test for successful pooled repair. Take
the reserved, phase-incompatible top outputs, color them by terminal
sibling, and join different colors when
\[
 \gamma_d\equiv\gamma_e\pmod{\gcd(n_d,n_e)}.
 \tag{SC22}
\]
Equivalently their original cofactor phases agree modulo
\(\gcd(k_d,k_e)\). Any hole of \(\mathcal F\) supplies an
\((r-1)\)-clique, by taking one covering supplier of each color at
that hole. Thus clique number at most \(r-2\) forces a whole cover
and contradicts EB1. An existing clique need not lie outside
\(\mathcal B\), so the converse is not asserted. For \(r=3\),
one incompatible occupied top slot cannot block this pooled repair;
all outside reservations must be included when counting slots.

The complete-liability construction also applies to a more general
family \(\mathcal B\) of distinct nonunit divisor slots covering
the entire lower union. With
\[
 \sigma=K-|\mathcal L|-|\mathcal T|\ge A,\qquad
 e=|\mathcal B|-|\mathcal L|,\qquad
 b=|\{d\in\mathcal T:n_d\in H\}|,
\]
its exact size and strict count condition are
\[
 |\mathcal F|=K-\sigma+e-b,\qquad e-b<\sigma. \tag{SC23}
\]
SC19 and the clique implication still hold under this strict count
condition. The original-label injection SC21 additionally needs the
specified matching provenance; it does not follow for an arbitrary
lower replacement. Moving a lower phase must pay its whole old
liability before SC23 can be used.

## 9. Height one removes the lower matching hypothesis

When \(A=1\), every lower original is \(r\)-free, so
\(d\mapsto n_d=\pi(d)\) is injective on \(\mathcal L\).
Use the identity matching \(h_d=n_d\). For every common tree,
SC19--SC21 then force a private point of the pure \(r\) class
whose complete terminal suppliers \(rk\) have their original
parents \(k\) surviving that same tree, with incompatible parent
phases. At least \(r-1\) such parent-child pairs occur together.
The parent disagreement is required by comparable disjointness; it
is not itself a contradiction.

Neither the all-height existence of a lower repair nor exclusion of
these simultaneous reservations has been established. A useful next
step must force an affordable lower repair and a free top supplier at
every remaining liability point for some common tree. Merely deriving
another collision at a separately chosen source does not do that.

The simultaneous fan obstruction can already occur in a noncover for
every tree. Take \(r=3,s=5,A=B=1\) and
\[
 0\bmod3,\quad0\bmod5,\quad0\bmod7,\quad0\bmod11,
 \quad1\bmod21,\quad23\bmod33. \tag{SC24}
\]
This family is divisor-closed, has initial odd-prime support, and has
disjoint comparable classes. In the displayed order, private integers
are \(3,5,7,11,1,23\). Every tree contains a nonzero \(5\)-digit;
take that digit, \(x\equiv0\pmod3\), and
\(x\equiv1\pmod7,\pmod{11}\). This is a private point of
the original pure 3 class. Its two terminal siblings are covered by
21 and 33 respectively. Both suppliers and their parents 7 and 11
are \(5\)-free, so they survive every tree, with incompatible
parent and child phases at both reserved slots.

Nevertheless, SC24 leaves 416 of its 1155 residues uncovered. On
the nonzero ternary roots the missing counts are respectively
\(4\cdot5\cdot10=200\) and \(4\cdot6\cdot9=216\).
Thus it fails the complete-liability inclusions SC15, even though
it realizes a saturated private fan, the ancestry, and the numerical
budget. A proof needs the whole family of inclusions in SC15; existence
of one blocked fan or avoidance of an isolated clique cannot replace
them. This example neither satisfies EB1 whole coverage nor refutes
a conclusion with that hypothesis.

## 10. A cofactor ideal rigidly blocks classwise lower repair

There is a tree-independent obstruction to the matching premise at
higher \(r\)-height. Put
\[
 G=\{g\in D:g>1,\ \gcd(g,rs)=1\}. \tag{SC25}
\]
This is a divisor ideal excluding one. Every original \(g\in G\)
always belongs to \(\mathcal L\), with unchanged output
\(C_g=\alpha_g\bmod g\).

Consider a proposed lower replacement by distinct nonunit AP moduli,
where each complete lower output class must be contained in a single
replacement AP. Different demands may share a replacement if its
phase is compatible. By the existing whole-class containment test
[DM4 in report 844](../600-649/844-collision-moment-needs-cofactor-packing.md#6-whole-output-classes-admit-an-exact-divisor-matching-test),
an AP containing \(C_g\) must use a divisor \(1<h\mid g\)
and its forced phase.

Induction on \(g\in G\) in numerical order forces its own slot
\(g\) with phase \(\alpha_g\). Indeed, a proper divisor
\(h\) belongs to \(G\), so its slot has already been forced
to \(\alpha_h\). Original comparable-class disjointness excludes
\(\alpha_g\equiv\alpha_h\pmod h\). No such proper divisor
can contain \(C_g\), leaving only its own numerical slot and phase.
Thus every slot in \(G\) is occupied with its original phase in
any classwise-containment repair, even if compatible grouping is allowed.

Suppose there is an original label
\[
 d=r^ag,\qquad1\le a<A,\qquad g\in G,\qquad
 \alpha_d\equiv v\pmod{r^a}. \tag{SC26}
\]
Its output \(\alpha_d\bmod g\) belongs to the lower family for
every tree. Any containing nonunit AP has modulus \(h\mid g\),
hence \(h\in G\). But \(h\mid d\) and comparable disjointness
give \(\alpha_d\not\equiv\alpha_h\pmod h\). Every possible
slot has already been forced to that incompatible original phase.
Therefore SC26 rules out every classwise-containment repair, including
full divisor matching and compatible grouping, regardless of its allowed
number of replacement classes. It does not rule out splitting one
complete class among several APs whose union covers it.

Equivalently, for fixed \(r,A,v\), let
\[
 G_r(v)=\gcd\{k:r^ak\in D,\ \gcd(k,r)=1,\
           1\le a<A,\ \alpha_{r^ak}\equiv v\pmod{r^a}\},
 \tag{SC27}
\]
with gcd of the empty set defined to be zero. A necessary condition
for classwise lower repair using replacement prime \(s\) is
\(s\mid G_r(v)\). For any violating cofactor \(k\), divisor
closure puts \(k\) in \(G\) and SC26 applies; \(k=1\)
cannot occur because no lower pure \(r\)-power matches \(v\).
In particular,
\(G_r(v)=1\) excludes this repair route for every replacement
prime. This is an obstruction to the specified repair route, not a
contradiction to the original hypothetical cover. At \(A=1\) the
set is empty and it imposes no restriction, consistently with Section 9.

The prime-slot instance of this rigidity appears in report 844,
Section 7. The argument here extends it to the full cofactor divisor
ideal and identifies when the high-layer lower family cannot be handled
classwise. A more general repair must explicitly pay the complete
liabilities of splitting or replacing those classes and satisfy SC23.
Sections 7--10 are ordinary mathematical deductions; no new Lean
verification, originality claim, or unrestricted noncoverage is asserted.
