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

## 11. An explicit digit split can spend the pooled deletion budget

The rigidity in Section 10 concerns containment of each whole class in
one replacement. The existing full-class digit split in
[report 385, LP2--LP4](385-private-congruence-hulls-and-crossed-modulus-closure.md#200-a-vacant-lower-prime-layer-gives-a-whole-cover-descent)
can instead be used inside SC18. The following is its concrete
interface with the pooled budget, not a new general splitting theorem.

Suppose \(C=\alpha_d\bmod m\) is one lower output with
\(d=r^am\), \(1\le a<A\), and \(\gcd(m,rs)=1\).
Supply a family \(\mathcal B_0\) of distinct odd nonunit divisor
slots of \(N\) covering the entire union of all other lower outputs,
with \(|\mathcal B_0|=|\mathcal L|-1\). This existence is a
hypothesis. Put
\[
 H_0=\operatorname{moduli}(\mathcal B_0),\quad
 H_T=\{n_d:d\in\mathcal T\},\quad b_0=|H_0\cap H_T|,
\]
\[
 V=\{rh:h\mid m,\ rh\notin H_0\},\qquad
 v_0=|V\setminus H_T|,\quad v_1=|V\cap H_T|.
 \tag{SC28}
\]
The divisor \(h=1\) is allowed: its candidate modulus is \(r>1\).
All these labels divide \(N\), since \(m\mid M\) and \(B\ge1\).
Use the actual value \(\sigma=K-|\mathcal L|-|\mathcal T|\).
If the integer interval
\[
 \boxed{
 \max\{0,r-v_0,r-\sigma-b_0\}
 \ \le t\le\
 \min\{v_1,r-2-b_0\}
 }
 \tag{SC29}
\]
is nonempty, choose \(t\) labels from \(V\cap H_T\) and
\(r-t\) from \(V\setminus H_T\). Assign the resulting distinct
labels \(rh_j\) bijectively to the digits \(0\le j<r\), with
replacement phases
\[
 z\equiv j\pmod r,\qquad z\equiv\alpha_d\pmod{h_j}.
 \tag{SC30}
\]
This is precisely the LP digit construction: the \(r\) classes
cover the entire \(C\). Add them to \(\mathcal B_0\), producing
one actual lower repair \(\mathcal B\). Its excess count and its
reserved top slots are
\[
 e=r-1,\qquad b=b_0+t\le r-2,\qquad e-b<\sigma.
 \tag{SC31}
\]
These counts come from the chosen slots before invoking EB1. At most
\(r-2\) members of the pooled top family are discarded, so SC15
still covers all of \(E\). The lower union is covered by
\(\mathcal B\), and SC23 gives a distinct odd whole cover with
strictly fewer than \(K\) classes. Thus a hypothetical EB1 cover
cannot supply both the stated \(\mathcal B_0\) and SC29.
For \(r=3,\sigma=2,b_0=0\), the criterion is exactly
\(v_0\ge2\) and \(v_1\ge1\): two vacant non-top slots and one
top slot fund a three-piece split, while at most one top class is lost.

Counting all reservations as losses is conservative. Given any actual
lower repair, let \(\ell\) count the reserved top classes not
contained in any member of that repair. SC15 still pays the whole
complement if \(\ell\le r-2\), while SC23 still uses the full
\(b\). A split slot \(rh_j\) retains its same-slot top class
exactly when that class has phase \(\alpha_d\bmod h_j\) and
\(j\bmod r\). Such compatibility must hold for the same chosen
labels and digit assignment. In particular the candidate \(h_j=m\),
if it is a top slot, cannot be a compatible reservation: its original
top label is \(r^Asm\), divisible by \(r^am\); the matching
lower \(r\)-prefix and comparable disjointness force different
phases modulo \(m\).

The split pieces can also pay a top class jointly, without any one
piece containing it. Denote the classes in SC30 by \(D_j\) and put
\(L_h=\operatorname{lcm}_j h_j\). For an \(r\)-free top output
\(C_n=\gamma\bmod n\), both \(n\) and all \(h_j\) divide
\(M\). The existing tailwise union test
[JCE2 in report 385](385-private-congruence-hulls-and-crossed-modulus-closure.md#139-compatible-shallow-certificates-force-a-complete-joint-escape)
reduces to
\[
 C_n\subseteq\bigcup_jD_j
 \quad\Longleftrightarrow\quad
 L_h\mid n\ \text{ and }\ \gamma\equiv\alpha_d\pmod{L_h}.
 \tag{SC32}
\]
Indeed, \(C_n\) has every \(r\)-digit, and on digit \(j\)
only \(D_j\) can serve it. Thus its cofactor AP must be contained
in each \(\alpha_d\bmod h_j\). This tests the split union
alone; \(\mathcal B_0\) may supply additional coverage.
If \(L_h=m\), no such top can pass SC32: its original label is
\(r^An\), divisible by \(r^am\), and the common lower
\(r\)-prefix together with SC32 would contradict comparable
disjointness. This particular service channel therefore needs a proper
cofactor divisor \(L_h<m\), as well as the actual phase agreement.

More generally the same SC15 argument uses the whole-union loss count
\[
 \ell_{\cup}=\#\{d\in\mathcal T:n_d\in H,\quad
                       C_d\not\subseteq\bigcup\mathcal B\}.
 \tag{SC33}
\]
The two conditions \(\ell_{\cup}\le r-2\) and
\(e-b<\sigma\) suffice. Every unreserved top is retained and
every reserved top outside this loss set is fully paid by the same
\(\mathcal B\). SC32 supplies one concrete way to certify that
payment. No selected point or separately optimized digit assignment
replaces containment of a complete top class.

No partial-fibre saving follows from the cofactor ideal alone. The
liability \(J=C\setminus\bigcup_{g\in G}C_g\) is
\((\mathbb Z/r^B\mathbb Z)\times J_M\); if nonempty, each
of its cofactor fibres has all \(r\) first digits. Subtracting
additional \(s\)-bearing lower service can reduce that liability,
but then its actual full complement must be used. The positive
retained-service term of report 385 Section 240 is unavailable under
its inherited definitions, as corrected by
[PB8 in Section 242](385-private-congruence-hulls-and-crossed-modulus-closure.md#242-exact-private-bucket-factorization-and-the-section-240-service-correction).

Neither a suitable \(\mathcal B_0\) nor a nonempty interval SC29
has been forced from the original inventory. In particular
\(\tau(m)<r\) already prevents this particular full-digit split.
The unresolved step is an arithmetic supply of these simultaneous
slots and full lower coverage, or another paid split construction.
This application has no new Lean verification and does not settle
unrestricted Erdős #7.

## 12. Complete lower liability can force an exact ten-class fan repair

The local conditions in SC24 do not guarantee an affordable repair even
if arbitrary new odd moduli and arbitrary heights are permitted. The
following refinement gives an exact repair cost and a sharp residual
density. It is a noncover, so the complete service inclusions SC15 remain
an essential hypothesis of the whole-cover problem.

Write \(a(n)\) for \(a\bmod n\), and take the original family
\[
 \mathcal C=\{0(3),0(5),0(7),0(11),1(21),23(33),
                  16(35),46(55),3(77)\}. \tag{SC34}
\]
It has \(K=9\), period \(1155\), modulus sum \(247\),
divisor-closed numerical labels, initial odd-prime support, and disjoint
comparable classes. In the displayed order, private integers are
\(6,5,7,11,1,23,16,46,157\). Its reciprocal sum is
\(19/21<1\), and it leaves 380 residues of its period uncovered.
Thus it does not satisfy EB1 or even the necessary whole-cover density
condition.

Use \(r=3,s=5,A=B=1,M=77\) and the common tree
\(\theta(j)=j\) for \(0\le j<3\). The literal source is
\[
 F_u(z)\equiv u\pmod3,\qquad
 F_u(z)\equiv\theta(z\bmod3)\pmod5,\qquad
 F_u(z)\equiv z\pmod{77}.
\]
The inherited lower and top families on period \(231\) are
\[
 \mathcal L=\{0(3),0(7),0(11),16(21),13(33),3(77)\},
 \qquad \mathcal T_1=\{1(7)\},\quad
 \mathcal T_2=\{1(11)\}. \tag{SC35}
\]
All phases are forced by the source. With
\(E=\mathbb Z\setminus\bigcup\mathcal L\), the complete-fan
locus is
\[
 V=E\cap1(77)=1(231)\cup155(231). \tag{SC36}
\]
At every point of \(V\), \(F_0(z)\) is private to the original
pure 3 class, and its complete fan is exactly \(\{21,33\}\).
The two parent slots 7 and 11 survive at their incompatible phase zero.
Here \(|\mathcal L|=6\), \(|\mathcal T|=2\), and \(\sigma=1\).

For any finite family \(\mathcal F\) of distinct odd nonunit AP
moduli, with arbitrary phases and no bound on its primes or heights,
\[
 \bigcup\mathcal L\subseteq\bigcup\mathcal F,\quad
 |\mathcal F|\le9
 \quad\Longrightarrow\quad
 \operatorname{dens}\!\left(1(77)\setminus\bigcup\mathcal F\right)
       \ge\frac1{693}. \tag{SC37}
\]
The density uses a common period of 231 and all repair moduli.
Furthermore,
\[
 \min\{|\mathcal F|:
       \bigcup\mathcal L\cup1(77)\subseteq\bigcup\mathcal F\}
       =10. \tag{SC38}
\]
Both bounds are attained. Covering this target is exactly preserving the
entire lower union and covering every complete-fan point.

### The published small-cover bound forces five complete lower classes

Reuse Simpson's whole-period irredundant-cover bound, already cited in
[report 343, Section 2](../../321-384/343-original-prefix-sat-reductions-and-transport-obstructions.md),
from [Corollary 2, pages 151--152](https://doi.org/10.4064/aa-45-2-145-152):
\[
 k\ge1+f(N),\qquad f(N)=\sum_p v_p(N)(p-1). \tag{SC39}
\]
Here \(N\) is the lcm of the entire irredundant subcover. A redundant
cover must first be reduced and its lcm recomputed. No disjointness
assumption is imposed.

A proper odd cover with each numerical modulus used at most twice and
at most nine classes must have exactly nine classes and lcm 45.
Indeed, SC39 restricts an irredundant subcover to
\[
 N\in\{3,5,7,9,15,21,25,27,45,81\}.
\]
At a prime-power period \(p^a\), its reciprocal sum is at most
\(2\sum_{j=1}^a p^{-j}<1\). At period \(3p\), for \(p=5,7\),
a root missed by the at most two modulus-3 classes receives relative
mass at most \(4/p<1\) from the modulus-\(p\) and modulus-\(3p\)
classes. Only 45 remains, and SC39 then requires all nine classes.
In particular, no such cover has at most eight classes, and a nine-class
one cannot contain a class of modulus 7 or 11.

Suppose now \(|\mathcal F|\le9\) and it covers the lower union.
The class \(0(3)\) is forced. Otherwise restriction to \(0(3)\)
has proper relative moduli \(d/\gcd(d,3)\), each occurring at most
twice. A relative modulus divisible by 3 has at most one original
numerical preimage. The preceding classification would require nine
classes of period 45, but their reciprocal sum is at most
\[
 \frac13+\frac19+\frac25+\frac1{15}+\frac1{45}
       =\frac{14}{15}<1.
\]

The classes \(0(7)\) and \(0(11)\) are forced as well. If \(0(7)\)
is absent, restriction to it again has proper odd relative moduli of
multiplicity at most two. All nine restrictions must be essential and
have period 45. Thus all original repair moduli are \(\ell\) or
\(7\ell\), with \(1<\ell\mid45\). They are coprime to 11 and
on the other required class \(0(11)\) have total relative mass at most
\[
 \frac87\sum_{1<\ell\mid45}\frac1\ell
       =\frac{88}{105}<1.
\]
If \(0(11)\) is absent, the symmetric bound on \(0(7)\) is
\((12/11)(11/15)=4/5<1\).

Next restrict to the entire \(16(21)\). The forced classes \(0(3)\)
and \(0(7)\) vanish, leaving at most seven active classes. If
\(16(21)\) itself is absent, all restrictions are proper: its other
containing divisor slots 3 and 7 are already occupied incompatibly.
SC39 restricts a minimal relative subcover to
\(N\in\{3,5,7,9,15,27\}\). For a relative \(3^j\), the only
numerical preimages are \(3^{j+1}\) and \(7\cdot3^{j+1}\),
so a pure 3-power period has total mass less than one. A relative
index 5 or 7 has at most four preimages, giving mass at most \(4/5\)
or \(4/7\). The only remaining period is 15, which needs seven
essential classes. But the forced \(0(11)\) has a nonempty relative
index-11 restriction and cannot belong to that subcover. Excluding it
leaves at most six classes, a contradiction. Interchanging 7 and 11
gives the same conclusion for \(13(33)\); the forced \(0(7)\)
then cannot belong to a period-15 core. Hence \(\mathcal F\) contains
the exact five classes
\[
 0(3),\quad0(7),\quad0(11),\quad16(21),\quad13(33).
 \tag{SC40}
\]

### Four further labels cannot pay both cofactor pairs

Consider the four complete period-231 fibres
\[
 W=\{1,155,157,80\}\pmod{231}.
\]
Their \((3,7,11)\)-coordinates, in this order, are
\((1,1,1),(2,1,1),(1,3,3),(2,3,3)\).
The first pair is the fan; the second is part of the old \(3(77)\)
liability. Every class in SC40 misses \(W\).

Give these four complete fibres equal normalized mass. For any further
class \(a(n)\), put \(g=\gcd(n,231)\), \(\delta=n/g\).
CRT gives the exact formula, including arbitrary new primes and heights,
\[
 \mu_W(a(n))=
 \frac{|\{w\in\{1,155,157,80\}:w\equiv a\pmod g\}|}
      {4\delta}. \tag{SC41}
\]
The only unused numerical divisors of 231 are 77 and 231. Every other
available label has \(\delta>1\). If \(\delta\ge5\), its mass
is at most \(1/5\). If \(\delta=3\), its modulus has exact
3-adic exponent two and fixes one of the two old ternary roots; its
mass is at most \(1/6\). The same \(1/5\) bound holds when
normalized on either of the two cofactor pairs alone.

There are at most four further labels. If neither 77 nor 231 is used,
they cover at most \(4/5\) of \(W\), leaving ordinary density
at least \(4/(5\cdot231)\). If only 231 is used, their covered
mass is at most \(1/4+3/5\), leaving \(3/(5\cdot231)\).
If only 77 is used, that class misses at least one full cofactor pair,
and the other three cover at most \(3/5\) of that pair, leaving
\(4/(5\cdot231)\). If both are used, their union misses at least
one full period-231 fibre. Each of the remaining two classes has a
proper odd relative index on that fibre and covers at most one third
of it. This leaves density at least \(1/(3\cdot231)\).
The smallest of these four lower bounds is \(1/693\).
Since \(\mathcal F\) covers the old \(3(77)\), any uncovered
part of \(W\) belongs to the fan pair. This proves SC37.

### Equality repairs and the exact budget boundary

The following actual families attain the bounds:
\[
 \mathcal F_9=\mathcal L\cup\{1(231),2(9),50(63)\},
 \qquad
 1(77)\setminus\bigcup\mathcal F_9=386(693),
\]
\[
 \mathcal F_{10}=\mathcal F_9\cup\{89(99)\}.
 \tag{SC42}
\]
The latter covers the entire target and has distinct odd nonunit labels.
On the fan at old ternary root 2, its last three added classes have
next ternary residues 2, 5 and 8 modulo 9; their cofactor conditions are
respectively empty, 1 modulo 7, and 1 modulo 11. The other fan root is
paid by \(1(231)\). Its numerical modulus sum is 554, without a
claim of minimum sum among ten-class repairs.

For this comparison enlarge the SC18 repair palette to arbitrary odd
nonunit moduli, and pull \(E\), the lower outputs and both top classes
back to their common period with the repair. The same literal union and
slot count give \(|\mathcal F|=8+e-b\). The attaining family is
itself a lower repair with both top slots reserved; its modulus-9 labels
are not available in the original divisor-only palette at \(N=231\).
Consequently the exact minimum, among complete lower repairs whose
resulting family also covers the complete fan, is
\[
 \min(e-b)=2>\sigma=1. \tag{SC43}
\]
Thus neither a strict count descent nor an equal-count descent is
available for this fixed source and target. This obstruction includes
arbitrary split repairs, new primes and unbounded exponents; it does
not assume classwise containment or restrict the repair to the old
period.

It does not obstruct every common tree. Omitting old 5-root 1 makes
the two lower outputs from 35 and 55 disappear. Nor does it supply
SC15: the source point \(z=2\) lies in \(E\) and is missed by
both top families. Raising the omitted-label budget also changes the
comparison: the same minimum \(e-b=2\) ties at \(\sigma=2\)
and is affordable in class count when \(\sigma\ge3\).
The unrestricted missing step remains a repair or exclusion using
the full whole-cover service conditions, with the actual height budget.

The displayed source maps, privacy witnesses and equality families have
been checked over their complete finite periods. The unrestricted
repair lower bound is the preceding argument using SC39, not a
bounded search over replacement moduli. These are ordinary mathematical
deductions reusing the cited covering theorem; no new Lean verification
or unrestricted Erdős #7 conclusion is asserted.

## 13. Released original chains fund a complete root-and-patch repair

The ternary rigid-ideal regime has a count supply stronger than merely
\(\sigma\ge A\). It does not supply the patch phases. Keep the same
hypothetical EB1 whole cover, common source, lower family and terminal
pool of Sections 7--10. For a labelled family \(\mathcal A\), write
\(U_{\mathcal A}=\bigcup_{d\in\mathcal A}C_d\).
Choose a retained subfamily \(\mathcal R\subseteq\mathcal L\) with
\[
 G\subseteq\mathcal R,\qquad
 d\mapsto n_d\text{ injective on }\mathcal R,\qquad
 r\notin H_{\mathcal R}:=\{n_d:d\in\mathcal R\}.
 \tag{SC44}
\]
The choice \(\mathcal R=G\) always satisfies this contract. Set
\(t=|\mathcal L|-|\mathcal R|\). Its exact released-or-omitted
original-label budget is
\[
 \Delta=\sigma+t=K-|\mathcal R|-|\mathcal T|.
 \tag{SC45}
\]
This counts original labels, including nonsurviving ones; it does not
assert that their surviving liabilities have already been paid.

### Arithmetic supply of the count budget

From the original numerical inventory define
\[
 p_0=\#\{(a,g):1\le a<A,\ g\in G,\ r^ag\in D\}.
\]
For a finite set \(\mathcal H\) of distinct nonunit divisors of
\(M\) with \(rh\notin H_{\mathcal R}\) for every \(h\in\mathcal H\),
also define
\[
 p_1(\mathcal H)=\#\{(a,h):0\le a<A,\ h\in\{1\}\cup\mathcal H,
                                      \ r^ash\in D\}.
\]
Then the original labels give the unconditional count inequality
\[
 \Delta\ge A+p_0+p_1(\mathcal H). \tag{SC46}
\]
The \(A\) pure \(r\)-powers belong to neither \(\mathcal R\) nor
\(\mathcal T\). An original counted by \(p_0\) has height below
\(A\) and so is not a top label. If it survives, its output slot
\(g\) is already occupied in \(\mathcal R\) by original \(g\);
otherwise it is an omission. In either case that original is counted
in \(\Delta\). The same argument applies to \(p_1\), because its
output slot \(rh\) is deliberately excluded from \(\mathcal R\).
These three original-label families are disjoint, distinguished by
cofactor one, nonunit \(s\)-free cofactor, and \(s\)-valuation one.
This proves SC46 without using any later hole or reservation conclusion.

Since original \(s\in D\), \(p_1(\varnothing)\ge1\). If
\(r^ag\in D\) for \(1\le a<A\), \(g\in G\), divisor closure
also gives
\[
 p_0\ge a(\tau(g)-1).
\]
In particular SC26 implies
\[
 \Delta\ge A+p_0+1\ge4. \tag{SC47}
\]
The weaker assumption \(p_0>0\) already suffices for this bound:
matching the chosen prefix determines whether these originals are
released or omitted, not whether they contribute to the budget.

### Pay complete lower liability and every displaced top

Choose an output root \(\rho\bmod r\) and purchase the whole class
\(S_\rho=\rho\bmod r\). Its slot is free in \(\mathcal R\).
Let
\[
 H_0=H_{\mathcal R}\cup\{r\},\qquad
 \mathcal T_0=\{d\in\mathcal T:n_d\in H_0\},
\]
and form the complete liability
\[
 Y=(U_{\mathcal L}\cup U_{\mathcal T_0})
       \setminus(U_{\mathcal R}\cup S_\rho). \tag{SC48}
\]
It includes all old lower service and every top class whose slot is
already displaced. In particular every \(r\)-free top output has a
nonunit modulus in \(G\), by original divisor closure, and is included
in this accounting. Retaining its parent phase does not preserve that
top class automatically.

For \(j\ne\rho\), let
\[
 P_j=\{z\bmod M:z\in Y,\ z\equiv j\pmod r\},\qquad
 \mathcal J=\{j\ne\rho:P_j\ne\varnothing\},\quad k=|\mathcal J|.
\]
These are complete projections, including every higher \(r\)-digit
lift. For each nonempty \(P_j\), choose \(y_j\in P_j\) and set
\[
 \Gamma_j=\gcd\bigl(M,\{y-y_j:y\in P_j\}\bigr).
 \tag{SC49}
\]
This is the existing whole-liability hull PH3--PH4 of report 385,
applied to the actual projection. A singleton gives \(\Gamma_j=M\).
For \(1<h\mid\Gamma_j\), the class
\[
 B_{j,h}=\{z:z\equiv j\pmod r,\ z\equiv y_j\pmod h\}
 \tag{SC50}
\]
has modulus \(rh\mid N\) and pays every point of \(Y\) in root \(j\).

Let \(\mathcal V_j\) contain precisely those \(h>1\) dividing
\(\Gamma_j\) for which \(rh\notin H_{\mathcal R}\) and either
no top occupies slot \(rh\), or its complete class is contained in
\(S_\rho\), or its class equals \(B_{j,h}\). These are explicit
sufficient tests for retaining old top service. A top at that numerical
slot has original label \(r^Ash\). Its first original \(s\)-digit
is \(\theta_1(\rho)\) in the whole-root alternative; equality with
the patch requires digit \(\theta_1(j)\) and cofactor phase
\(y_j\bmod h\). No phases from different sources are combined.

Suppose distinct choices \(h_j\in\mathcal V_j\), \(j\in\mathcal J\),
exist. Take the actual lower repair
\[
 \mathcal B=\{C_d:d\in\mathcal R\}\cup\{S_\rho\}
               \cup\{B_{j,h_j}:j\in\mathcal J\}. \tag{SC51}
\]
Its labels are distinct odd nonunit divisors of \(N\). SC48--SC50
pay all lower outputs and all top classes occupying \(H_0\). Every
further top displaced by a patch has its whole old service paid by
that patch or by \(S_\rho\), by the definition of its menu. Thus
\(\mathcal B\), together with every unreserved top, covers
\(U_{\mathcal L}\cup U_{\mathcal T}=X\). This proves complete
coverage directly, including all old liabilities.

For the actual reserved-top count
\(b=|\{d\in\mathcal T:n_d\in\operatorname{moduli}(\mathcal B)\}|\),
SC23 now reads
\[
 |\mathcal F|=K-\Delta+1+k-b,
 \qquad e=1+k-t. \tag{SC52}
\]
The inequality SC46 can use the same selected set
\(\mathcal H=\{h_j:j\in\mathcal J\}\). If a selected patch slot
is occupied by a top, divisor closure supplies all \(A\) originals
\(sh_j,rsh_j,\ldots,r^{A-1}sh_j\) counted in \(p_1(\mathcal H)\).
Their surviving liabilities were included in SC48; this extra count
supply does not waive their coverage.

For any odd \(r\), a further supplied case occurs when \(A\ge2\)
and each selected \(h_j\) has \(rh_j\in D\) or \(sh_j\in D\).
Choose one such original donor per patch. An \(rh_j\) donor supplies
a \(p_0\) entry, since divisor closure puts \(h_j\) in \(G\);
an \(sh_j\) donor supplies a \(p_1\) entry. Distinct patches have
distinct donors, and original \(s\) supplies one more \(p_1\) entry.
Thus \(p_0+p_1(\mathcal H)\ge k+1\), and SC46--SC52 give
\[
 |\mathcal F|\le K-A-b<K.
\]
This is already a strict class-count descent, with no equal-count
modulus-sum case left to settle. Donor existence does not supply the
required simultaneous safe phase choices.

### A necessary ternary menu obstruction

Take \(r=3\) and \(p_0>0\), in particular the SC26 rigidity regime.
Then \(k\le2\), and SC47--SC52 give
\[
 |\mathcal F|\le K-4+3-b<K.
\]
Hence every hypothetical EB1 cover, at every fixed common tree,
retained family SC44 and choice of \(\rho\), must satisfy
\[
 \begin{array}{ll}
 k=0:&\text{impossible},\\
 k=1:&\mathcal V_j=\varnothing,\\
 k=2:&\mathcal V_{j_1}=\varnothing\ \text{or}\
       \mathcal V_{j_2}=\varnothing\ \text{or}\
       \mathcal V_{j_1}=\mathcal V_{j_2}=\{h\}
       \text{ for some }h.
 \end{array} \tag{SC53}
\]
For two nonempty menus, equality to the same singleton is exactly the
failure to choose distinct numerical cofactors. This does not require
a new matching theorem. The strict funding comes from original-label
inventory even if \(b=0\). The allowed-menu service tests are
conservative: SC53 does not classify every possible split or every
possible way to cover a displaced top.

### The pure source root couples the patch liability to its credit

If the original pure \(s\)-class survives, denote its output root by
\(j_s\), so \(\theta_1(j_s)=\alpha_s\bmod s\). Comparable
original disjointness forces every other \(s\)-bearing original to
avoid that first \(s\)-digit. Consequently no top class is contained
in \(S_{j_s}\): purchasing that root pays the pure-\(s\) lower output,
but pays no top by the whole-root alternative above.

If instead \(\rho\ne j_s\), then
\[
 P_{j_s}=(\mathbb Z/M\mathbb Z)
              \setminus\bigcup_{g\in G}(\alpha_g\bmod g).
 \tag{SC54}
\]
Indeed, the lower pure-\(s\) output supplies the entire root before
subtraction. Every retained \(s\)-bearing output avoids it, while the
retained \(s\)-free originals are exactly \(G\): any higher original
\(r^ag\) would collide with its retained \(g\)-slot. Subtracting
\(U_{\mathcal R}\) therefore removes precisely the indicated
cofactor union, at all higher output digits. If this complete complement
has hull one, its menu is empty. Choosing \(\rho=j_s\) avoids this
particular liability but forfeits the whole-root top service just
identified.

Thus the count cost of this simultaneous repair is supplied in the
ternary rigid regime. The remaining task is to force some actual
\(\theta,\mathcal R,\rho\) with feasible whole-liability menus, or
to derive a contradiction from the universal obstruction SC53. Neither
existence has been established. The argument reuses the digit split,
whole-liability hull and SC23 accounting; it is ordinary mathematics,
without new Lean verification or a conclusion for unrestricted Erdős #7.

## 14. Existing deep projection bounds constrain the complete cofactor complement

The complete complement in SC54 inherits the deep projection theorem
of [report 375, Sections 1--4](375-deep-prime-prefix-projections-and-tree-contraction.md#1-complete-fibres-and-the-blocked-tree-count).
This reuses the existing whole-source transport and tree duality; no
new prime-substitution theorem is needed.

For the same actual original family put
\[
 K_G=(\mathbb Z/M\mathbb Z)
                 \setminus\bigcup_{g\in G}(\alpha_g\bmod g).
\]
Let \(\mathcal C_0\) be all original classes whose moduli are
\(r\)-free, on the complete carrier \(\mathbb Z/(s^BM)\mathbb Z\),
and let \(R_r\) be their complement. Original \(r\) occurs, so
\(|\mathcal C_0|<K\). Minimum cardinality makes \(R_r\) nonempty;
otherwise \(\mathcal C_0\) would already be a smaller distinct odd
whole cover. Every original in \(G\) lies in \(\mathcal C_0\), and
its membership depends only on the \(M\)-coordinate. Consequently
\[
 \operatorname{pr}_M(R_r)\subseteq K_G. \tag{SC56}
\]
In particular \(K_G\ne\varnothing\). This inclusion uses the same
actual original phases throughout.

Fix a prime \(q\mid M\) with \(q>r\), and put
\(H_q=v_q(M)\), \(t_q=q-r+1\). Apply report 375 DP6 with smaller
prime \(r\), larger prime \(q\), and its residual \(R_r\).
Together with SC56, that result says that
\[
 \operatorname{pr}_{q^{H_q}}(K_G)
 \text{ contains a complete }t_q\text{-ary depth-}H_q
 \text{ subtree of the }q\text{-ary prefix tree}. \tag{SC57}
\]
Prefixes read digits from lowest to highest. In particular, for every
\(1\le h\le H_q\),
\[
 |\operatorname{pr}_{q^h}(K_G)|\ge(q-r+1)^h. \tag{SC58}
\]
The same report's DP7 supplies a probability on actual \(R_r\)
with mass at most \(t_q^{-h}\) on every \(q^h\)-cylinder. Push it
forward through \(\operatorname{pr}_M\). Its support lies in \(K_G\)
by SC56, and the same bound holds for every \(0\le h\le H_q\).
These are, for each \(q\), one law controlling all its depths;
neither DP7 nor this projection supplies one law controlling all
primes simultaneously. Nor can the separate counts SC58 be multiplied
to obtain a joint CRT volume.

For \(x\in K_G\), define its complete hull by
\[
 \Gamma_G=\gcd\bigl(M,\{y-x:y\in K_G\}\bigr).
\]
The definition is independent of representatives and the base point,
as in PH3--PH4. A prime \(q\mid\Gamma_G\) would make the entire
\(q\)-projection a singleton. SC58 excludes every \(q>r\), while
\(q=r\) is absent from \(M\). Hence all prime divisors of
\(\Gamma_G\) are smaller than \(r\). Since \(M\) is odd,
\[
 r=3\quad\Longrightarrow\quad\Gamma_G=1. \tag{SC55}
\]
The case \(M=1\) gives the same value directly.

Now take \(r=3\). Whenever the pure-\(s\) output survives at root
\(j_s\), choosing \(\rho\ne j_s\) in Section 13 forces
\(P_{j_s}=K_G\), a nonempty set with hull one. Thus
\(\mathcal V_{j_s}=\varnothing\) for every retained family SC44.
More precisely, its complete cofactor projection occupies at least
\((q-2)^h\) residues modulo every \(q^h\mid M\), by SC58.
The certified one-root construction can succeed only by buying
\(\rho=j_s\), or by choosing a common tree that omits the pure-\(s\)
root. In the first case it receives no whole-root top-service credit,
as already shown in Section 13. A different slot-safety test alone
cannot provide a single nonunit-cofactor patch for the full \(K_G\).

These consequences concern the complete complement, not the smaller
individual residuals \(J_g\) or projections obtained after retaining
additional service. They assert neither independent coordinates nor
a uniform lower density. The remaining patch-existence problem
persists. This is an ordinary application of the existing projection
theorem, without new Lean verification or unrestricted noncoverage.
