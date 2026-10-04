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

For the original ternary height, the active EB1 scope is $A\ge2$.
Report 385 HPA1 and NF73 already exclude $A=1$; Section 28 records
their joint scope. The height-one deductions in Sections 21--27
therefore describe an excluded premise, while their explicit patch
constructions remain available under their stated set-cover conditions.

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

## 15. A single larger neighbour is excluded in the extremal cover

The remaining condition \(p_0>0\) in Section 13 follows automatically
when \(A\ge2\). The useful input is again
[report 375 DP7](375-deep-prime-prefix-projections-and-tree-contraction.md#4-a-dual-subtree-and-a-supported-probability-for-one-prime),
applied to one larger prime, not a proposed common law for all primes.

First suppose every original modulus divisible by \(r\) has the form
\(r^as^b\), with \(1\le a\le A\), \(0\le b\le B\).
The complete \(r\)-free residual \(R_r\) of Section 14 is nonempty.
Set \(t=s-r+1\ge3\). DP7 supplies one probability \(\nu_s\)
on this actual residual, on the full \(s^BM\)-carrier, such that
\[
 \nu_s([c]\bmod s^b)\le t^{-b}\qquad(0\le b\le B).
\]
Use the following single probability on the original full CRT carrier:
\[
 \mu=\operatorname{Haar}(\mathbb Z/r^A\mathbb Z)\otimes\nu_s.
\]
All original \(r\)-free classes have \(\mu\)-mass zero. For an
original modulus \(r^as^b\), its actual CRT event has mass at most
\(r^{-a}t^{-b}\). Independence here is part of this explicitly
chosen product law; \(\nu_s\) retains all correlations between the
\(s\)-coordinate and \(M\). There is no exchange of witnesses or
probabilities between different prime projections.

Numerical distinctness allows at most one original for each pair
\((a,b)\). Whole coverage and the finite union bound would therefore
require
\[
 \begin{aligned}
 1
 &\le\sum_{a=1}^A r^{-a}\sum_{b=0}^B t^{-b}\\
 &=\frac{1-r^{-A}}{r-1}\,
       \frac{t(1-t^{-(B+1)})}{t-1}\\
 &<\frac{t}{(r-1)(t-1)}\le\frac34,
 \end{aligned} \tag{SC59}
\]
a contradiction. Thus, in this minimum-cardinality cover, a support prime cannot have
all its mixed-modulus neighbours confined to one larger prime. This statement has
no height-one restriction.

Now assume \(A\ge2\) and \(p_0=0\). Any original
\(r^as^bm\), with \(a\ge1\), \(m>1\), and \(m\mid M\),
would have original divisors \(m\in G\) and \(rm\in D\).
Since \(1<A\), the latter contributes to \(p_0\), a contradiction.
Hence every \(r\)-bearing original would be of the excluded form
\(r^as^b\). It follows that
\[
 A\ge2\quad\Longrightarrow\quad p_0\ge1. \tag{SC60}
\]
At \(A=1\), the defining range for \(p_0\) is empty, so this
argument makes no corresponding assertion.

### Complete original columns supply the released-label budget

The complete original column count gives another lower bound without
using SC60. Let \(\mathcal C\) be all nonunit \(r\)-free cofactors
\(k\) for which \(r^ak\in D\) for some \(a\ge0\). Divisor
closure supplies one complete column
\(k,rk,\ldots,r^{h(k)}k\), where \(0\le h(k)\le A\).
Set
\[
 n_0=|\mathcal C|,\qquad
 m=\#\{k\in\mathcal C:h(k)=A\},\qquad
 L_{<A}=\#\{d\in D:1\le v_r(d)<A,\ d/r^{v_r(d)}>1\}.
\]
These partition the original labels, together with the \(A\) pure
\(r\)-powers, so
\[
 K=A+n_0+L_{<A}+m.
\]
All surviving outputs from one column have the same numerical slot
\(\pi(k)\). SC44 therefore retains at most one label per column.
The column \(k=s\) exists and has output slot \(r\), which SC44
excludes. Hence \(|\mathcal R|\le n_0-1\). The top pool contains
only nonpure height-\(A\) originals, so \(|\mathcal T|\le m\).
In particular the exact identity SC45 yields
\[
 \begin{aligned}
 \Delta
 &=A+L_{<A}+(n_0-|\mathcal R|)+(m-|\mathcal T|)\\
 &\ge A+L_{<A}+1\\
 &\ge A+(A-1)m+1.
 \end{aligned} \tag{SC61}
\]
The last inequality uses the \(A-1\) lower mixed originals in every
top column. Distinct columns have distinct \(r\)-free parts, so no
original label is counted twice. No survival or phase match with the
selected lower prefix is required.

The existing private terminal fan of original \(r^A\), used in
Section 7 and [report 371, Section 2](371-private-top-fans-and-ancestor-cuts.md#2-the-private-top-fan-has-an-escaping-first-ancestor),
supplies \(m\ge r-1\). For clarity, only its highest-digit argument
is needed: take one actual private point, keep all other coordinates
and its \(r^{A-1}\)-prefix fixed, and vary the last digit. Each of
the \(r-1\) other siblings needs a nonpure original of height exactly
\(A\); a lower-height owner would also cover the private point.
One original cannot cover two such full residues, so their cofactors
are distinct. This argument also applies when \(A=1\); it does
not use the later ancestor conclusion in report 371 that assumes
\(A\ge2\). Thus
\[
 \Delta\ge r(A-1)+2\qquad(A\ge1). \tag{SC62}
\]
This reuses the actual fan and original ancestor inventory; it is not
a new companion-class theorem.

The counting argument uses only \(\mathcal R\subseteq\mathcal L\),
output-slot injectivity and exclusion of slot \(r\). It does not use
\(G\subseteq\mathcal R\). Thus SC61--SC62 remain valid for any
retained family satisfying those three conditions: it may choose a
different actually surviving lower representative in a column or omit
an original \(G\)-class. Every retained phase must still come from
that actual label. Such a choice changes the complete omitted service;
SC54 and the \(K_G\) hull conclusion cannot automatically be carried
over to this different family.

For any complete legal repair retaining \(\mathcal R\), buying one
root \(S_\rho\), adding \(c\) other classes and omitting \(b\)
reserved tops, the actual count is
\[
 |\mathcal F|=K-\Delta+1+c-b.
\]
Here all retained and added numerical moduli must be distinct, and
all omitted service must be covered by the final family. SC62 gives
strict count descent whenever \(c-b\le r(A-1)\). In particular,
at \(r=3,A=2\) the budget is at least five, and a one-root repair can
afford three further classes when \(b=0\). For every odd \(r\)
and \(A\ge2\), the \(r-1\) one-per-root patches of Section 13
are funded without an additional donor hypothesis. An occupied-top
rescue counts as an added class in \(c\); its removed old top is
counted once in \(b\). Neither count grants free service.

SC59--SC62 are consumers of the existing single-prime law and actual
terminal fan. They exclude the \(p_0=0,A\ge2\) branch and enlarge
the available repair budget, but do not provide the simultaneous
patches. The original \(A=1\) branch is excluded by the independent
results cited in Section 28. This is ordinary mathematical
analysis without new Lean verification or unrestricted noncoverage.

## 16. Omitting heavily occupied source roots funds more patches at every height

Let \(N_s=\#\{d\in D:s\mid d\}\), and write
\(\alpha_s\) for the first root of the original pure \(s\)-class.
Require the common tree \(\theta\) to retain \(\alpha_s\) at its
first level. Every other \(s\)-bearing original avoids this root:
its modulus is comparable with \(s\), so its original class is
disjoint from the pure \(s\)-class. For each other first root \(\xi\),
let \(n_\xi\) count the original \(s\)-bearing labels with that root.
These are counts of the original labels, including all their heights,
and satisfy
\[
 \sum_{\xi\ne\alpha_s}n_\xi=N_s-1.
\]
Choose the other \(r-1\) retained first roots to have the smallest
loads. The omitted \(s-r\) roots then contain at least
\[
 z_\theta\ge
 \left\lceil\frac{(s-r)(N_s-1)}{s-1}\right\rceil \tag{SC63}
\]
original labels. Here \(z_\theta\) counts all \(s\)-bearing originals
whose complete prefix is rejected by the common tree. Every compatible
extension of the selected first level satisfies SC63; deeper choices
can only add rejected labels. This is one common tree for every column.

For any terminal prefix \(v\) used in Section 7, none of the rejected
labels can belong to \(\mathcal R\) or \(\mathcal T\). In addition,
all \(A\) pure \(r\)-powers are absent. The original pure \(s\)-class
survives the source restriction, but cannot belong to \(\mathcal R\)
because its output slot is \(r\); it is not a height-\(A\) top.
These three sets of omitted original labels are disjoint. Therefore
every retained family allowed in Section 15 satisfies
\[
 \Delta\ge A+1+z_\theta
 \ge A+1+
 \left\lceil\frac{(s-r)(N_s-1)}{s-1}\right\rceil,
 \qquad A\ge1. \tag{SC64}
\]
The count uses only original membership and omission. It does not
require the retained lower representatives to be the original \(G\)
classes, or any independence between first roots and cofactor phases.
At \(A=1\), if \(\mathcal R=\mathcal L\setminus\{s\}\), every
other original either survives in this retained family or the pooled
tops, or is counted by \(z_\theta\). Then
\(\Delta=2+z_\theta\) exactly. Smaller retained families only give
the lower bound.

Let \(P>s\) be the largest support prime. Directly reuse
[report 385 NF66](385-private-congruence-hulls-and-crossed-modulus-closure.md#56-the-original-cover-needs-enough-small-prime-labels-to-block-compression),
which gives \(N_s\ge P-s+2\) for this same EB1 cover, with no
height restriction. At \(r=3,s=5\), SC64 and the oddness of \(P\)
give \(\Delta\ge A+(P-1)/2\). SC62 also holds for the chosen tree,
so the two bounds combine as
\[
 \boxed{\Delta\ge\max\{3A-1,\ A+(P-1)/2\}.} \tag{SC65}
\]
They cannot be added: the original ancestors counted in SC61 may
already be among the rejected labels counted in SC64.

The same report's [NF72--NF73](385-private-congruence-hulls-and-crossed-modulus-closure.md#58-reuse-the-height-one-source-before-resolving-individual-collision-phases)
give stronger existing inputs. The height count NF72 yields
\(N_s\ge P-s+1+B\). Thus in SC65 one may use
\[
 D(A,B,P)=\max\left\{3A-1,\
 A+1+\left\lceil\frac{P+B-5}{2}\right\rceil\right\}
 \le\Delta. \tag{SC65a}
\]
When \(A=1\), NF73 directly reuses report 708's ordinary
thirteen-prime height-one noncoverage result and gives \(P\ge47\).
Consequently \(\Delta\ge24\) in that branch, without repeating
its retained exact arithmetic or asserting new Lean verification.

Using the attributed nine-prime support theorem recorded in
[Schroeder's source entry](../../../../../../Library/Arith/schroeder2026nine.md),
report 385 NF68 gives \(P\ge29\). Under this source input,
SC65 yields \(\Delta\ge A+14\); for \(A\ge2\) this is at least
sixteen. Together with the \(A=1\) bound above, the uniform lower
bound is sixteen. The source entry records
the pinned edition and its completed finite-geometry verification;
no complete local kernel replay of the arbitrary-height source
theorem is asserted. The parameter bound SC65 does not need this
additional numerical input.

Consequently a complete legal one-root repair using this tree gives
strict descent whenever
\[
 c-b\le D(A,B,P)-2. \tag{SC66}
\]
With the source inputs above, fourteen net additional classes
are funded at every \(A\ge1\), and twenty-two when \(A=1\).
All patch and rescue classes still
count in \(c\), and each removed old top counts once in \(b\).
Coverage, numerical-slot uniqueness and the complete displaced
service remain required. In particular SC66 supplies a budget,
not a construction of compatible patches. This is ordinary
mathematical analysis without new Lean verification.

## 17. Changing retained representatives preserves the unbought pure-root obstruction

Fix actual retained families \(\mathcal R\) and
\(\mathcal T_+\subseteq\mathcal T\), with all their numerical
output slots distinct. As in Section 15, require
\(\mathcal R\subseteq\mathcal L\) and exclude output slot \(r\),
but do not require \(G\subseteq\mathcal R\). Let \(\mathcal F_0\)
consist of the retained output classes whose original labels have
\(b(d)=0\). Their moduli are distinct nonunit divisors of \(M\).
Moreover
\[
 |\mathcal F_0|\le|\mathcal R|+|\mathcal T|<K.
\]
Define their complete cofactor complement using their actual phases:
\[
 K_{\mathcal F_0}=(\mathbb Z/M\mathbb Z)
                    \setminus\bigcup\mathcal F_0. \tag{SC67}
\]
Global minimum cardinality makes this set nonempty: otherwise
\(\mathcal F_0\) would itself be a smaller distinct odd whole cover.
It need not equal the old \(K_G\).

The contraction in [report 375 DP4--DP5](375-deep-prime-prefix-projections-and-tree-contraction.md#2-one-common-source-map-for-the-selected-subtree)
applies to \(\mathcal F_0\) itself. Fix \(q\mid M\), \(q>r\),
and \(H_q=v_q(M)\). If the complement of the \(q^{H_q}\)-projection
of \(K_{\mathcal F_0}\) contained a complete \(r\)-ary subtree,
every full cofactor fibre selected by that tree would be covered by
\(\mathcal F_0\). The DP4 source map would pull these classes back
to a whole cover with at most \(|\mathcal F_0|<K\) classes. All
input moduli are \(r\)-free, so the DP5 output-modulus map is
injective and its outputs are odd nonunits. This contradicts the
same global minimum \(K\); no claim that \(\mathcal F_0\) was
an original subfamily is needed.

The existing dual-tree argument DP6--DP7 therefore gives
\[
 \begin{gathered}
 \operatorname{pr}_{q^{H_q}}K_{\mathcal F_0}
 \text{ contains a complete }(q-r+1)\text{-ary subtree},\\
 |\operatorname{pr}_{q^h}K_{\mathcal F_0}|\ge(q-r+1)^h
 \qquad(1\le h\le H_q).
 \end{gathered} \tag{SC68}
\]
For each such \(q\), it also supplies one probability supported on
this new complete complement with all its \(q^h\)-cylinder masses
at most \((q-r+1)^{-h}\). These probabilities are separate for
different primes. They are not the old law on \(R_r\), and no
common balanced probability is inferred. The complete congruence
hull of \(K_{\mathcal F_0}\) has only prime factors smaller than
\(r\); in particular it equals one when \(r=3\).

Suppose now that \(\theta\) retains the original pure \(s\) first
root, whose output root is \(j_s\), and that the bought root is
\(\rho\ne j_s\). Every other \(s\)-bearing original is disjoint
from the pure \(s\)-class, hence its output avoids \(j_s\).
The pure \(s\) original itself is excluded by the reserved slot
\(r\). Thus on this root the retained lower and top service is
exactly \(\mathcal F_0\), independently of all higher \(r\)-digits.
The complete residual after this retained service and the bought
root consequently has the exact slice
\[
 \{j_s\}\times\{\text{all higher }r\text{-digit tails}\}
             \times K_{\mathcal F_0}. \tag{SC69}
\]
At \(r=3\), its periodic lift to the integers has full difference
gcd exactly \(r\): the cofactor hull is one and all higher
\(r\)-digits are free. Any single AP containing this whole
periodic slice must have modulus dividing \(r\). For a nonunit
modulus it must be the class \(j_s\bmod r\), but that numerical
slot is already used by \(S_\rho\). Therefore at least two new
classes must meet and together cover this slice in any legal repair.
The conclusion also permits patch moduli outside the old period;
containment in one AP still imposes the same difference-gcd condition.

Changing lower representatives or keeping more distinct-slot tops
does not remove this single-patch obstruction. Nothing here says
that another root has the same complete cofactor residual. Buying
\(j_s\), or omitting the pure \(s\) source root from the common
tree, removes the premise supplying SC69. Multiple patches may
still cover the slice; neither their existence nor their exclusion
is proved. SC67--SC69 reuse the existing contraction on a newly
specified actual AP family and have no new Lean verification.

## 18. A funded unbought-root repair needs more than one cofactor prime

Fix \(r=3,s=5\), retain the pure \(5\) source root in the common
tree, and buy \(\rho\ne j_5\). Allow any actual lower representatives
as in Section 17. Consider a proposed complete repair, with all its
numerical moduli distinct, and restrict its added patch moduli to
divisors of \(N=3^BM\). Let \(c=c_0+c_+\) count respectively the
added \(3\)-free and \(3\)-bearing classes, and let \(b\) count all
actually omitted tops. Suppose its net count satisfies
\(c-b\le\Delta-2\), as ensured by SC66's sufficient budget.

Put every final \(3\)-free class, including all \(c_0\) added
patches, into \(\mathcal F'_0\). Numerical uniqueness and the
actual retained count give
\[
 |\mathcal F'_0|
 \le K-\Delta-b+c_0
 =K-\Delta+(c-b)-c_+
 \le K-2-c_+<K. \tag{SC70}
\]
Its moduli divide \(M\). Reuse Section 17's DP4--DP7 application
on this enlarged family. Its complete complement
\(K_0=(\mathbb Z/M\mathbb Z)\setminus\bigcup\mathcal F'_0\)
is nonempty, and for each fixed \(q\mid M\) it supports a
probability \(\nu_q\) satisfying
\[
 \nu_q([a]\bmod q^f)\le(q-2)^{-f}
 \qquad(0\le f\le v_q(M)). \tag{SC71}
\]
The probability is chosen after absorbing the new \(3\)-free
patches. No positive mass of the old probability is presumed to
remain after that change.

Every retained old \(3\)-bearing output arises from a
\(5\)-bearing original other than pure \(5\), and so avoids
\(j_5\). The bought root also avoids it. The added
\(3\)-bearing patches must therefore cover the entire slice
\[
 \{j_5\}\times\{\text{all higher }3\text{-digit tails}\}\times K_0.
 \tag{SC72}
\]
Suppose all their cofactors are one or powers of a single fixed
\(q\mid M\). Since \(\gcd(M,15)=1\), this prime is at least
seven. The possible patch moduli are \(3^a\) and \(3^a q^f\).
The pure slot \(3\) is already used by \(S_\rho\), so a pure
power requires \(a\ge2\).

On SC72 use Haar probability on the complete higher-digit tail,
independent of \(\nu_q\). A patch whose first root is \(j_5\)
has mass at most \(3^{1-a}(q-2)^{-f}\); a patch on another root
has mass zero. Distinct numerical slots allow at most one patch
for each \((a,f)\). Writing \(H_q=v_q(M)\), the union mass is
bounded by
\[
 \begin{aligned}
 \mu(U_{\rm patches})
 &\le\sum_{a=2}^{B}3^{1-a}
   +\left(\sum_{a=1}^{B}3^{1-a}\right)
        \left(\sum_{f=1}^{H_q}(q-2)^{-f}\right)\\
 &<\frac12+\frac{3}{2(q-3)}\le\frac78<1.
 \end{aligned} \tag{SC73}
\]
The empty pure-power sum when \(B=1\) is allowed. The contradiction
does not depend on an upper bound for the number of patches:
even using every available slot in this single-prime palette fails.
Thus any funded repair in this setting must use at least two primes
of \(M\) among the cofactors of its added \(3\)-bearing classes.
They need not occur together in one modulus. Added \(3\)-free
patches may use arbitrary divisors of \(M\); they were already
absorbed in SC70.

A separate consequence allows arbitrary composite cofactors but
assumes they all contain a fixed \(q\mid M\). The distinct pure
\(3\)-power patches occupy less than half of the complete root
tail. Choose one actual tail avoiding all of them. At that same
tail the active nonpure patches must cover all of \(K_0\), and
each has \(\nu_q\)-mass at most \(1/(q-2)\). Hence at least
\(q-2\) nonpure \(3\)-bearing patches are required. If \(d\)
counts the added pure \(3\)-powers, any chosen net budget \(F\)
with \(c-b\le F\) consequently requires
\[
 b\ge c_0+d+q-2-F. \tag{SC74}
\]
For example, if all these nonpure cofactors contain the largest
prime \(P\ge29\), at least twenty-seven are needed. Choosing
the sufficient uniform budget \(F=14\) then requires
\(b\ge13+c_0+d\). This is a necessary reservation count, not
a contradiction: those tops can only be omitted if their entire
lost service is covered elsewhere. The actual budget may exceed
fourteen, and a lower bound for \(\Delta\) supplies no upper
bound on what a repair can afford.

SC70--SC74 reuse the existing single-prime supported law on the
final actual \(3\)-free family. They exclude a specific repair
palette and quantify a different common-factor condition. They
neither provide a common probability for different primes nor
exclude mixed-prime repair, purchase of \(j_5\), or source trees
omitting that root. No new Lean verification is claimed.

## 19. Successful repairs can normalize the bought root while freezing the sources

Prime-class relocation is an existing covering-system operation:
[Harrington--Sun--Wong, Lemma 3.1, pages 6--7](https://arxiv.org/pdf/2104.00602v1)
attributes it to Hammer--Harrington--Marotta and preserves the numerical
moduli and the other prime-modulus classes. The following extra avoidance
condition identifies when all of a specified retained family can remain
fixed. It is needed here because unrestricted relocation alone does not
promise to preserve those source phases.

Let $q$ be prime. Suppose a numerically distinct family
$$
 \mathcal B\cup\{[\beta]_q\}\cup\mathcal P
 \quad\text{covers all integers},\qquad \alpha\ne\beta\pmod q,
 \tag{SC75}
$$
and every $q$-bearing class in $\mathcal B$ avoids $[\alpha]_q$.
Replace the pure class by $[\alpha]_q$. For a patch of modulus
$q^e t$, $q\nmid t$, whose $q$-coordinate is
$\alpha+qu\pmod{q^e}$, change that coordinate to
$\beta+qu\pmod{q^e}$ and keep its $t$-coordinate. Leave all other
patches and all of $\mathcal B$ fixed. The new family still covers,
with exactly the same numerical moduli.

To prove this, work on a common CRT period containing all patch primes
and heights. The new pure class covers the $\alpha$-root; all roots
other than $\alpha,\beta$ retain their old coverage. For a point $x$
on the $\beta$-root, change only its first $q$-digit to $\alpha$,
obtaining $y$. Old coverage of $y$ could not come from the old pure
class or a $q$-bearing member of $\mathcal B$. A $q$-free owner of
$y$ also covers $x$; a $q$-bearing patch owner has been moved to cover
$x$. This pays the complete carrier, including every omitted top's
service. No density approximation or restriction to divisors of $N$
is used.

If the original pure $s$ survives at output root $j_s$, all other
$s$-bearing originals avoid its source root by comparable disjointness.
Thus every $r$-bearing member of
$\mathcal B=\mathcal R\cup(\mathcal T\setminus\mathcal T_0)$
avoids $j_s$. The excluded slot $r$ ensures that the original pure
$s$ is not already in this fixed family. Applying SC75 with $q=r$
shows, for fixed $\theta,\mathcal R,\mathcal T_0$ and patch moduli,
$$
 \boxed{\text{a complete repair with some bought root exists}
 \iff \text{one with bought root }j_s\text{ exists}.} \tag{SC76}
$$
The equivalence preserves $c,b,\Delta$, modulus sum, and every retained
source identity and phase. In particular the heavy-root tree of
Section 16 may use $S_{j_s}$ without losing any successful repair.
Sections 17--18 constrain repairs which insist on a different root;
those restrictions need not be overcome to prove repair existence.
SC76 itself supplies no patch family.

There is a second application at an occupied prime slot $q\mid M$.
If $\mathcal R$ uses the surviving source $r^a q$ there instead of
the original $q$, take $\alpha$ to be the original $q$-phase and
$\beta$ the chosen representative's phase. The original $q$ is
always an available lower source. Every other retained $q$-bearing
source avoids $\alpha$. SC75 replaces this one representative by
the original $q$ and changes only patch phases. Here that one source
identity does change; the other retained source identities stay fixed.
Successive operations at different primes alter different CRT
coordinates, so all occupied prime $M$-slots can simultaneously use
their original representatives without changing the counts or slots.
Vacant slots are not filled for free. At $A=1$ each lower slot already
has its unique source, so this representative choice adds no freedom.

The same argument applies to a slot $q^e$ when the old and original
phases have the same $(e-1)$-prefix: move only their last digit inside
that parent. Source classes with smaller $q$-height are unchanged by
the move, and those with height at least $e$ avoid the original cell.
Different parent prefixes and general composite slots have no such
invariance supplied here. Their normalization remains unproved.

## 20. A private-point tree can remove every lower pure-cofactor column

For this construction let $r<s$ and assume $A\le s-r$. Choose one
actual private point $z$ of the original pure $r^A$ class. Fix its
terminal prefix $v\pmod{r^{A-1}}$ and write $\zeta$ for its full
$s$-coordinate. At depth $b\ge1$ forbid the prefixes
$$
 F_b=\{\alpha_{r^a s^b}\bmod s^b:
    0\le a<A,\ r^a s^b\in D,
    \ \alpha_{r^a s^b}\equiv v\pmod{r^a}\}.
 \tag{SC77}
$$
There are at most $A$ of them at each depth, and none is the prefix
of $\zeta$: otherwise its lower original would cover $z$.
At every retained node select $r$ children avoiding these forbidden
prefixes, and at a node on $\zeta$ retain its next child. The inequality
$A\le s-r$ guarantees that both requirements can be met. Continuing
to depth $B$ constructs one compatible tree for all original labels.

Every lower pure-cofactor original $r^a s^b$, $a<A$, is now absent:
it either misses the old $r$-prefix or its $s$-prefix is forbidden.
The source restrictions on the safe siblings still give the whole-cover
identities SC15. The private point and its complete actual terminal fan
survive together, since every supplier at a sibling of $z$ has an
$s$-prefix on the retained path $\zeta$. This is one common-source
construction, not separate choices for different suppliers.

Divisor closure supplies the $B$ original pure-$s$ columns. Their
output slots are all absent from $\mathcal L$, hence
$|\mathcal R|\le n_0-B$ in the notation of SC61. Reuse its complete
column inventory $L_{<A}\ge(A-1)m$ and $m\ge r-1$ to obtain
$$
 \begin{aligned}
 \Delta&=A+L_{<A}+(n_0-|\mathcal R|)+(m-|\mathcal T|)\\
 &\ge A+(A-1)m+B\ge r(A-1)+B+1.
 \end{aligned} \tag{SC78}
$$
A complete one-root repair therefore strictly descends whenever
$c-b\le r(A-1)+B-1$. In particular $r=3,A=2$ allows $B+2$ net
patches; $A=1$ allows $B-1$. The construction omits the original
pure-$s$ root, so SC76's retained-root premise does not apply to this
tree. Nor is this necessarily the load-minimizing tree of Section 16:
its bound cannot be added to that tree's budget without proving a
single tree realizes both choices. Mixed-cofactor collisions and their
complete repair remain unresolved.

## 21. Height-one source inventory forces at least three permanent occupied tops

Let $r=3,s=5,A=1$, and define the actual divisor ideal
$$
 \mathcal C_M=\{m\mid M:\ 3\cdot5^b m\in D
                      \text{ for some }0\le b\le B\},\qquad
 n_b=\#\{m\mid M:3\cdot5^b m\in D\}.
 \tag{SC79}
$$
It contains one, $n_0=|\mathcal C_M|$, and $n_{b+1}\le n_b$.
These are counts in the original family, before choosing a tree.

Directly reuse the common-chain inventory
[report 378 SF7--SF9](378-saturated-prime-fibres-and-mixed-tail-incidence.md#3-chain-prices-for-the-actual-3-bearing-originals).
At height one its mixed-source bound is two. Including the pure
original $3$, of price one, gives
$$
 \sum_{3\cdot5^b m\in D}\gamma_{\mathscr P}(5^b m)\ge3,
 \qquad
 \sum_{b=0}^{B}n_b3^{-b}\ge3
       \quad\text{for the chain }\mathscr P=(5).
 \tag{SC80}
$$
Each selected chain uses one probability on the actual residual.
A multiple-coordinate class is bounded by the minimum of its caps,
never their product. Since the last sum is strictly less than
$3n_0/2$, it already requires $n_0\ge3$.

In fact $n_0=3$ is impossible. A three-element divisor ideal is
either $\{1,q,q^2\}$ or $\{1,q,q'\}$, with primes
$7\le q<q'$ in the second case. Put
$S(t)=\sum_{b\ge0}\min\{3^{-b},t\}$.
For the first shape take the common chain $5<q$. Its second cap
base is $q-4\ge3$, so the total original price is at most
$$
 S(1)+S(1/3)+S(1/9)
 =\frac32+\frac56+\frac7{18}=\frac{49}{18}<3.
$$
For the second shape use $5<q<q'$. If $q=7$, its last two bases
are at least $3,5$; if $q\ge11$, they are at least $7,3$.
Monotonicity of $S$ bounds both cases by
$$
 S(1)+S(1/3)+S(1/5)
 =\frac32+\frac56+\frac{17}{30}=\frac{29}{10}<3.
$$
Both contradict SC80. These upper bounds only enlarge the finite
original inventory to geometric tails; no simultaneous attainability
of the caps is required.

Every nonunit $m\in\mathcal C_M$ forces originals $3m$ and $m$
by divisor closure. The former lies on a safe ternary root, and both
are $5$-free. They survive every common tree and occupy the same
output slot $m$ in $\mathcal T$ and $\mathcal L$. Hence, writing
$b_0=\#\{t\in\mathcal T:n_t\in\operatorname{slots}(\mathcal L)\}$,
$$
 \boxed{|\mathcal C_M|\ge4,\qquad b_0\ge|\mathcal C_M|-1\ge3.}
 \tag{SC81}
$$
The permanent occupied slots here are all $3$-free. In particular
the $b_0=2$ branch is absent under the actual whole-cover hypothesis.

The same existing price inequality also excludes a single-prime
$M$-palette of any height. If every $m\in\mathcal C_M$ is a power
of one $q\ge7$, the chain $5<q$ bounds the total finite inventory
strictly below
$$
 \sum_{a,b\ge0}3^{-\max(a,b)}
 =\sum_{j\ge0}(2j+1)3^{-j}=3,
$$
again contradicting SC80. Thus at least two primes of $M$ occur in
the cofactors of the actual $3$-bearing originals. They need not
occur together in a single modulus.

Finally reuse the original count $N_3\ge P-1$ and the height-one
support bound $P\ge47$ from
[report 385 NF73](385-private-congruence-hulls-and-crossed-modulus-closure.md#58-reuse-the-height-one-source-before-resolving-individual-collision-phases).
Together with SC79--SC81 they give
$$
 P-1\le N_3=\sum_{b=0}^{B}n_b
 \le(B+1)|\mathcal C_M|\le(B+1)(b_0+1),
 \qquad
 b_0\ge\max\left\{3,
       \left\lceil\frac{P-1}{B+1}\right\rceil-1\right\}.
 \tag{SC82}
$$
Consequently $b_0=3,4,5$ requires $B\ge11,9,7$, respectively.
This estimate alone does not exclude larger finite $B$. It reuses
SF9's common probability and NF73's source inventory. Section 28's
independent exclusion of original $A=1$ applies at every finite $B$.

## 22. A small occupied seed forces an actual phase stop in finite lcm repair

Keep $A=1,r=3,s=5$ and choose the heavy-root tree of Section 16.
Set $\mathcal R=\mathcal L\setminus\{5\}$ and buy $S_{j_5}$,
so that the retained lower family together with that root is exactly
$\mathcal L$. Let
$$
 \mathcal B_0=\{t\in\mathcal T:
                 n_t\in\operatorname{slots}(\mathcal L)\},
 \qquad b_0=|\mathcal B_0|.
 \tag{SC83}
$$
Start from $\mathcal L\cup(\mathcal T\setminus\mathcal B_0)$.
Its moduli are distinct and its count is below $K$, so EB1 gives an
actual hole. At every stage keep all of $\mathcal L$ and all patches
already added. An actual current hole $x$ is in $E$. Each top color
has a supplier at $x$ by SC15, and every such supplier must be among
the tops already removed. Choose one $d,e$ of opposite colors.
Their actual intersection is the CRT class
$$
 I=C_d\cap C_e=[x]_{\ell},\qquad
 \ell=\operatorname{lcm}(n_d,n_e).
 \tag{SC84}
$$
The phase is forced by the common hole. This uses the same elementary
intersection mechanism as
[report 385 OL1--OL3](385-private-congruence-hulls-and-crossed-modulus-closure.md#177-an-occupied-lcm-transfers-a-reciprocal-swap-to-complete-private-liability);
that report's reciprocal-private-hull hypotheses are not presumed here.

If $\ell$ is occupied by a lower class or a previous patch, its
phase differs from $x\pmod\ell$, since otherwise $x$ was covered.
This is an actual occupied-phase stop. If the slot is occupied by
an unremoved top, replace that top by $I$ and record its removal.
If it is unused, add $I$. In each successful step the numerical
moduli remain distinct. Replacing a top can expose other points;
they remain part of the next complete hole set and are never treated
as already paid.

Let $k$ count successful steps and $f$ those whose slot was not an
unremoved top slot. There are $c=k$ patches and
$b=b_0+k-f$ removed tops, so
$$
 c-b=f-b_0.
$$
Every newly used modulus is an lcm of some nonempty subset of the
initial $b_0$ top moduli. Indeed this holds for the initial removed
tops, and each replacement adds exactly the join of two already
removed moduli. A successful slot is new among the patches and is
not any singleton seed slot, because those remain occupied by
$\mathcal L$. Thus
$$
 k\le2^{b_0}-b_0-1,
 \qquad c-b=f-b_0\le2^{b_0}-2b_0-1.
 \tag{SC85}
$$
Coincident subset lcms only reduce these upper bounds. A return to
an earlier patch slot is a phase stop, not another successful step;
no strict-increase assertion for every dependency edge is needed.

The two initial colors sharpen this count. Write $u,v\ge1$ for
their seed counts, $u+v=b_0$. Every generated modulus has a seed
subset representation containing both initial colors. The first
generation joins opposite-color seeds; any later generated parent
already carries both initial colors, whatever its actual top color.
Thus
$$
 k\le(2^u-1)(2^v-1),\qquad
 c-b\le(2^u-1)(2^v-1)-b_0.
 \tag{SC86}
$$
These representations track numerical lcms only. A newly removed
top keeps its own original phase; its class is not presumed to equal
the intersection of the seed classes in its numerical representation.

For $b_0=3,4,5$, SC86 gives at most $3,9,21$ successful steps and
net costs at most $0,5,16$. Each lies within the twenty-two net
patches funded at height one by Section 16. Every intermediate
family therefore still has fewer than $K$ classes, so it has another
actual hole. The process cannot stop with coverage or continue
indefinitely: it must encounter an occupied-phase stop within the
stated number of successful steps. Every queried hole lifts through
SC17 to an actual private point of the original pure $3$ class.

There is a stronger bound when every initial seed slot is $3$-free.
All generated lcms then divide $M$. If such a slot $n$ is a top
slot, its original label is $3n$, so divisor closure supplies its
$5$-free lower parent $n$. That parent always lies in $\mathcal L$.
Consequently this top was already in $\mathcal B_0$; no successful
step can replace an unremoved top. The removed set remains exactly
$\mathcal B_0$, and every successful slot is the lcm of one of the
$uv$ initial opposite-color pairs. Hence
$$
 k=f\le uv,\qquad
 c-b\le uv-b_0\le\left\lfloor\frac{b_0^2}{4}\right\rfloor-b_0.
 \tag{SC87}
$$
For $3\le b_0\le11$ the last bound is at most nineteen, so the
same funded phase-stop conclusion follows, after at most $uv$
successes. This requires all seeds to be $3$-free; SC81 alone only
supplies three permanent $3$-free seeds.

The inventory sometimes forces this extra hypothesis: if
$P-1>(B+1)b_0$, SC82 gives $|\mathcal C_M|=b_0+1$, whose
nonunit members already account for every seed. For example this
also settles the budget for six seeds split $1+5$. SC86 gives net
cost at most twenty-five, funded by Section 16 whenever $P+B\ge54$.
SC82 requires $B\ge6$. The only remaining parameters are
$P=47,B=6$, and then $46\le7|\mathcal C_M|$ forces
$|\mathcal C_M|=7$. All six seeds are $3$-free, so SC87 instead
gives at most five successes and net cost at most minus one.

In these branches finite lcm expansion cannot exhaust the proven
budget before it meets an incompatible occupied slot. Repairing
that stop would require changing an occupied lower or patch class
and paying its complete old service. SC76 does not provide that
composite-slot exchange. The complete repair at original $A\ge2$
remains unresolved; the height-one cases are already excluded by
Section 28's reused results. No new Lean verification is claimed for
Sections 19--22.

## 23. Three fresh-five layers repair the whole hole set of flat seeds

Keep $A=1,r=3,s=5$, but let $\theta$ be any common tree retaining
the original pure $5$ root. It need not minimize the surviving load.
Keep all of $\mathcal L$, put $\mathcal R=\mathcal L\setminus\{5\}$,
and use the original pure $5$ output as the bought root $[j_5]_3$.
Write $\mathcal B_0,b_0$ as in SC83 and define the complete hole set
on the integers by
$$
 \mathcal F_0=\mathcal L\cup(\mathcal T\setminus\mathcal B_0),
 \qquad H_0=\mathbb Z\setminus\bigcup\mathcal F_0.
$$
These are periodic pullbacks of the corresponding subsets of $X$.
If $\mathcal U,\mathcal V$ are the two colors of $\mathcal B_0$,
SC15 gives
$$
 H_0\subseteq\left(\bigcup\mathcal U\right)
                   \cap\left(\bigcup\mathcal V\right),
 \qquad H_0\cap[j_5]_3=\varnothing. \tag{SC88}
$$
This is the full liability of deleting $\mathcal B_0$, not just a
chosen opposite-color intersection or the larger set $E$.

Suppose every seed modulus divides $M$. Its actual class therefore
has no $3$- or $5$-condition. Let $\alpha,\beta\in\{0,1,2\}$ be
the two roots other than $j_5$. Add the following classes. In a
supplier column, intersect the displayed cell with every actual
class of that color, preserving its cofactor phase.

| New modulus factor | Unconditional class | Copies of $\mathcal U$ | Copies of $\mathcal V$ |
|---|---|---|---|
| $5$ | $[0]_5$ | $[1]_5\cap C$ | $[2]_5\cap C$ |
| $15$ | $[3]_5\cap[\alpha]_3$ | $[3]_5\cap[\beta]_3\cap C$ | $[4]_5\cap[\alpha]_3\cap C$ |
| $45$ | $[4]_5\cap[\beta]_9$ | $[4]_5\cap[\beta+3]_9\cap C$ | $[4]_5\cap[\beta+6]_9\cap C$ |

Every point of $H_0$ satisfies both supplier unions. New $5$-roots
$0,1,2$ are covered by the first row. Root $3$ is covered on its
$\alpha,\beta$ branches by the second row. On root $4$ the second
row covers the $\alpha$ branch, and the third row covers the three
modulo-$9$ children of its $\beta$ branch. The already retained
pure output $3$ class covers the remaining ternary root.

The patch moduli are exactly
$$
 \{5,15,45\}\cdot
 \bigl(\{1\}\cup\{n_t:t\in\mathcal B_0\}\bigr). \tag{SC89}
$$
All are distinct: within one row the cofactor moduli are distinct,
and the rows have different $3$-valuations. Every patch contains
$5$, whereas every old output modulus is $5$-free. Thus there is
no collision with a retained class. CRT supplies each displayed
phase. One can work on $\operatorname{lcm}(N,45)$; this new
$5$-coordinate is not the old coordinate already transported by
$\theta$.

The construction reuses the digit splitting and complete-service
mechanism of [report 385 DR7](385-private-congruence-hulls-and-crossed-modulus-closure.md#10-descendant-assisted-private-hull-closure-and-phase-group-repair-budgets)
and its explicit CRT realization LP3--LP4 in Section 200. Here the
three available service menus are the unconditional class and the
two actual seed unions. The additional conclusion is one simultaneous
repair with distinct labels, rather than separately priced repairs
whose labels might collide. No lower class or unremoved top changes.
The exact count is
$$
 c=3(b_0+1),\qquad b=b_0,\qquad c-b=2b_0+3,
 \qquad
 |\mathcal F_{\rm new}|=K-\Delta+2b_0+4. \tag{SC90}
$$
Consequently $\Delta\ge2b_0+5$ contradicts EB1 in this flat-seed
case. Unlike SC87, this repairs all holes; it does not end at an
occupied-phase stop.

There is a stronger omission budget on this same tree, even when
some seed moduli contain $3$. For every nonpure original top $3k$,
divisor closure supplies the original lower parent $k>1$. Its
original ternary root is safe, so a retained $5$-prefix puts it in
$\mathcal T$. Both members of the pair $(k,3k)$ survive exactly
when that top belongs to $\mathcal B_0$: at height one there is
no other original lower representative of its numerical slot.
There are $N_3-1$ such pairs and $b_0$ surviving pairs. Each other
pair contributes at least one rejected original to $z_\theta$.
Different pairs are disjoint, since their parents are $3$-free and
their tops have original $3$-height one. A $5$-free pair always
survives, so every charged rejection is indeed counted by
$z_\theta$. SC64 therefore gives
$$
 z_\theta\ge N_3-1-b_0,
 \qquad \Delta=2+z_\theta\ge N_3-b_0+1. \tag{SC91}
$$
No independently optimized tree or root count has been added.
Combining SC90--SC91, a flat-seed family is impossible whenever
$$
 N_3\ge3b_0+4. \tag{SC92}
$$
In fact its repaired cover would have at most
$K-N_3+3b_0+3<K$ classes, all distinct, odd and greater than one.

## 24. Existing joint source counts sharpen the flat-seed obstruction

Let $\nu$ denote the number of actual support primes; the substitution
prime $s$ remains $5$. Directly reuse
[report 385 NF79 and NF82](385-private-congruence-hulls-and-crossed-modulus-closure.md#60-the-two-first-root-branches-share-one-original-label-inventory).
At original height one these supply
$$
 \nu\ge14,\quad P\ge47,\quad N_3\ge P+\nu-5\ge56,
 \quad
 t_p:=\#\{d\in D:3p\mid d\}\ge p-6\quad(p\mid M),
 \quad t_P\ge P-3. \tag{SC93}
$$
The last, stronger largest-prime count is established by the two
first-root groups in NF82's height-one proof. These are counts in
one actual original family. Their scalar values must not in general
be added, because a label may contain several support primes.
The inherited height-one support input has the ordinary proof and
verification scope recorded at NF73; no new kernel replay is supplied.

Since $p\ge7$, every $t_p$ is positive and divisor closure forces
original $3p$. Consequently $\mathcal C_M$ contains one and every
support prime of $M$. More precisely, if $d_+$ counts seeds with
positive output $3$-height, then
$$
 \{n_t:t\in\mathcal B_0,\ 3\nmid n_t\}
       =\mathcal C_M\setminus\{1\},
 \qquad b_0=|\mathcal C_M|-1+d_+\ge\nu-2+d_+.
 \tag{SC94}
$$
The forward inclusion uses the original $3m$ behind a flat top;
the reverse inclusion is SC81's permanent parent/top pair. This
improves the small-ideal inventory in Section 21 by reusing the
already established mixed-prime count.

SC92--SC93 immediately exclude all-flat seed families with
$b_0\le17$, for every tree retaining the pure $5$ root. The parameter
form is
$$
 d_+=0\quad\Longrightarrow\quad
 b_0\ge\left\lceil\frac{N_3-3}{3}\right\rceil
 \ge\left\lceil\frac{P+\nu-8}{3}\right\rceil. \tag{SC95}
$$
For comparison with the support count, $P\ge3\nu+4$. Indeed,
count $3$ and all candidates $6j\pm1$ from $5$ through $P$, and
remove the composites $25,35$. For $P=6k+1$ this leaves at most
$2k-1$ odd primes, and for $P=6k-1$ at most $2k-2$.
Both yield the displayed inequality. Thus $N_3\ge4\nu-1$.

If $b_0=\nu-2$, SC94 forces $d_+=0$ and SC92 excludes it.
If $b_0=\nu-1$ and $d_+=0$, SC92 again excludes it. Therefore
$$
 \boxed{b_0\ge\nu-1\ge13,\qquad
 b_0=\nu-1\ \Longrightarrow\
 d_+=1,\quad
 \mathcal C_M=\{1\}\cup\{p:p\mid M\}.} \tag{SC96}
$$
These conclusions do not require the heavy-root optimization.
The old scalar lower bound three is not the active minimum under
these reused source premises.

The same inventory also controls the original $5$-height. Write
$\mathcal C_P=\{m\in\mathcal C_M:P\mid m\}$. Each member
contributes at most $B+1$ original labels counted by $t_P$. The
unit and the $\nu-3$ other support primes are distinct $P$-free
members of $\mathcal C_M$. Hence
$$
 P-3\le t_P\le(B+1)|\mathcal C_P|
 \le(B+1)(b_0-d_+-\nu+3). \tag{SC97}
$$
At equality in SC96, $\mathcal C_P=\{P\}$, so $B\ge P-4$.
This uses original columns, not independently realizable marginal
inventories. It is compatible with arbitrary finite larger heights.

## 25. One nonflat seed of height at least two has a complete paid repair

Suppose $d_+=1$ and write $b=b_0$. Let the exceptional seed class
be $D_*=[a]_{3^h m}$, $h\ge1$, with $m\mid M$. Divisor closure
puts $m$ in $\mathcal C_M$; if $m>1$, its flat top is a seed.
Put $D_*$ in the first top color and let $\mathcal U,\mathcal V$
be the remaining flat classes in the two colors. There are $b-1$
flat classes. Orient $\alpha$ in Section 23 to the first output
$3$-root of $D_*$ and let $\beta$ be the other unbought root.
The first root is not $j_5$, because every original $5$-bearing
class other than pure $5$ avoids that pure class's root.

Run the same table on these flat classes. It uses $3b$ patches.
The full original hole set obeys
$$
 H_0\subseteq\left(\bigcup\mathcal U\cup D_*\right)
                    \cap\bigcup\mathcal V.
$$
On root $\beta$, both flat menus still cover $H_0$. On root
$\alpha$, the table covers new $5$-roots $0,2,3,4$ using the
unconditional or second-color menu. Thus every remaining hole lies in
$$
 H_0\cap D_*\cap[1]_5. \tag{SC98}
$$
This conclusion remains valid when $\mathcal U$ is empty.

If $h\ge3$, add $D_*\cap[1]_5$, of modulus $5\cdot3^h m$.
Its $3$-height differs from every table slot. This gives $c=3b+1$
and net cost $2b+1$, with no displaced patch service.

If $h=2$, the needed modulus $45m$ is occupied by a table patch.
Replace that patch by $D_*\cap[1]_5$. The displaced patch lies
in a cell $[4]_5\cap[w]_9$ with $w\equiv\beta\pmod3$.
On that cell $D_*$ is absent, so both flat menus cover every point
of $H_0$. Add
$$
 [4]_5\cap[w]_{27},\qquad
 [4]_5\cap[w+9]_{27}\cap C\ (C\in\mathcal U),\qquad
 [4]_5\cap[w+18]_{27}\cap C\ (C\in\mathcal V).
 \tag{SC99}
$$
These $b$ patches cover all newly exposed points of $H_0$. Their
moduli $135$ and $135n_C$ are distinct and fresh. Points outside
$H_0$ retain their owner in $\mathcal F_0$, so no other service
is lost. The replacement has zero net count and the final patch
count is $c=4b$. Work on $\operatorname{lcm}(N,135)$ if the new
third ternary digit exceeds the old output height.

Together with SC91, these give the complete-cover contradictions
$$
 \boxed{
 \begin{aligned}
 d_+=1,\ h\ge3,\ N_3\ge3b_0+2&\quad\Longrightarrow\quad\bot,\\
 d_+=1,\ h=2,\ N_3\ge4b_0+1&\quad\Longrightarrow\quad\bot.
 \end{aligned}} \tag{SC100}
$$
The count $N_3\ge56$ excludes respectively $b_0\le18$ and
$b_0\le13$ in these two cases. The construction does not require
prime flat cofactors. At $b_0=\nu-1$, the stronger parameter count
$N_3\ge4\nu-1$ funds both repairs. Thus the unique nonflat seed
in SC96 has $h=1$, and its modulus is either $3$ or $3p$ for a
support prime $p\mid M$.

The next construction handles a single nonflat seed of any height at
a larger cost, without requiring its cofactor to be prime or its
phase to match a flat supplier. It uses additional $5$-digits so
its labels cannot collide with this section's initial table.

## 26. A deeper fresh-five packet excludes the minimum collision inventory

The remaining single-seed liability in SC98 has a second complete
repair. Keep $d_+=1$, write $b=b_0$ and $v=|\mathcal V|$, and
use the first output root $\alpha$ of $D_*$. After the $3b$-patch
table, all remaining holes belong to
$$
 R=[1]_5\cap[\alpha]_3\cap\bigcup\mathcal V. \tag{SC101}
$$
It is enough to cover this entire set. This does not require the
exceptional cofactor $m$ to be nonunit or prime, nor any agreement
between its phase and a flat supplier's phase.

Add the following classes. A row with $\mathcal V$ means one
intersection with each actual $C\in\mathcal V$; rows labelled
one have no cofactor constraint. Take $\alpha\in\{0,1,2\}$.

| New $5$-condition | New $3$-condition | Cofactor menu | Numerical moduli |
|---|---|---|---|
| $[1]_{25}$ | none | one | $25$ |
| $[6]_{25}$ | none | $\mathcal V$ | $25n_C$ |
| $[11]_{25}$ | $[\alpha]_3$ | one | $75$ |
| $[16]_{25}$ | $[\alpha]_3$ | $\mathcal V$ | $75n_C$ |
| $[21]_{25}$ | $[\alpha]_9$ | one | $225$ |
| $[21]_{25}$ | $[\alpha+3]_9$ | $\mathcal V$ | $225n_C$ |
| $[21]_{125}$ | none | one | $125$ |
| $[46]_{125}$ | none | $\mathcal V$ | $125n_C$ |
| $[71]_{125}$ | $[\alpha]_3$ | one | $375$ |
| $[96]_{125}$ | $[\alpha]_3$ | $\mathcal V$ | $375n_C$ |
| $[121]_{125}$ | $[\alpha+6]_9$ | one | $1125$ |

For a point of $R$, its second $5$-digit gives one of the five
residues $1,6,11,16,21$ modulo $25$. The first four are covered
by the first four rows, since the point has root $\alpha$ and an
actual $\mathcal V$ supplier. At residue $21$, the next two rows
cover two of the three modulo-$9$ children of $\alpha$. If its
child is $\alpha+6$, the five possible residues modulo $125$ are
$21,46,71,96,121$, covered by the last five rows. Thus the whole
set $R$ is covered.

There are six unconditional classes and five copies of the second
color, for a total of $6+5v$ new patches. All their moduli have
$5$-valuation two or three. They avoid every old output, whose
$5$-valuation is zero, and every patch of the first table, whose
$5$-valuation is one. Within this new packet, the pair of $3$- and
$5$-valuations and the distinct cofactor $1$ or $n_C\mid M$
determine each numerical modulus uniquely. CRT supplies each
phase, on $\operatorname{lcm}(N,1125)$ if necessary. No old
class or provisional patch is removed.

Consequently one nonflat seed of any height admits a complete
repair with
$$
 c=3b_0+6+5v,\qquad 1\le v\le b_0-1. \tag{SC102}
$$
The lower bound on $v$ follows from SC88 and EB1's actual initial
hole. More generally SC91 gives a simple comparison for any full
repair keeping $\mathcal F_0$ and adding $c$ classes:
$$
 |\mathcal F_{\rm new}|=K-\Delta+1+c-b_0\le K-N_3+c.
 \tag{SC103}
$$
Thus SC102 contradicts EB1 whenever
$$
 N_3\ge3b_0+7+5v.
 \quad\text{In particular }N_3\ge8b_0+2\text{ is sufficient.}
 \tag{SC104}
$$
This packet reuses the same actual-supplier CRT splitting as
Section 23, but places the second packet in a disjoint range of
$5$-valuations. Its coverage is a whole-set assertion on $R$,
not just a pointwise selection of a convenient supplier.

At the minimum inventory $b_0=\nu-1$, SC96 gives
$\mathcal C_M=\{1\}\cup\{p:p\mid M\}$. Under this specific
condition, the original inventories counted by distinct $t_p$
in SC93 are disjoint. A label divisible by $3p$ and $3q$ for
$p\ne q$ would force $pq\in\mathcal C_M$, a contradiction.
The original pure $3$ is outside all of them. It is therefore
legitimate here to add the lower bounds, using $P-3$ instead of
$P-6$ for the largest prime:
$$
 N_3\ge 1+\sum_{p\mid M}(p-6)+3. \tag{SC105}
$$
This is disjoint counting in the same original family. It does
not assert the inequality for general composite cofactor ideals.

There are $\nu-2$ different odd primes of $M$, all at least seven.
In increasing order $p_j\ge2j+5$, so SC105 implies
$$
 N_3\ge(\nu-2)^2+4\ge8\nu-6=8b_0+2
 \qquad(\nu\ge14). \tag{SC106}
$$
For the middle inequality the difference is
$\nu^2-12\nu+14$, which is positive at fourteen and increasing
thereafter. In the smallest support case, the primes from seven
through forty-seven sum to $318$, so the actual prime list gives
$N_3\ge250$, stronger than the elementary bound used in SC106.
Every finite larger original $5$-height remains allowed.

SC96 supplies exactly one nonflat seed in this minimum branch,
and SC104--SC106 pay its entire repair. Hence the branch is
impossible, regardless of the exceptional seed's height or phase:
$$
 \boxed{A=1\quad\Longrightarrow\quad
 b_0\ge\nu\ge14
 \quad\text{for every common tree retaining pure }5.} \tag{SC107}
$$
This pays the exceptional seed without changing any occupied lower
phase. Larger collision inventories
can contain composite cofactors, so the disjointness behind SC105
then fails; multiple nonflat seeds can also impose different
ternary roots on the remaining liability. These are limitations of
this packet argument, not remaining EB1 height-one cases: Section 28
excludes that entire premise. The generic repair construction is
ordinary mathematics, without new Lean verification or a proof or
refutation of unrestricted Erdős #7.

## 27. Equality with the support count requires two separated nonflat seeds

Suppose $b_0=\nu$. SC94 gives $d_+\le2$. If $d_+=0$, the
flat packet has $c=3\nu+3<N_3$, since SC93 and $P\ge3\nu+4$
give $N_3\ge4\nu-1$. SC103 therefore excludes this case.

If $d_+=1$, then $\mathcal C_M$ consists of one, all $\nu-2$
support primes of $M$, and exactly one additional member. Divisor
closure forces this additional member to be $p^2$ or $pq$ for
different support primes $p,q$. In the square case the inventories
$t_r$ for different primes remain disjoint. In the product case
only the $p$ and $q$ inventories can intersect: any other overlap
would force a second composite member of $\mathcal C_M$. Remove
the smaller of $p,q$ from the count. At least $\nu-3$ mutually
disjoint prime inventories remain, still including $P$. Reusing
the same counts as SC105--SC106 yields
$$
 N_3\ge(\nu-3)^2+4\ge8\nu+2
 \qquad(\nu\ge14). \tag{SC108}
$$
The difference for the last inequality is
$\nu^2-14\nu+11$, positive at fourteen and increasing thereafter.
SC102 uses at most $8b_0+1=8\nu+1$ patches, so this case also
contradicts SC103. Consequently
$$
 \boxed{b_0=\nu\quad\Longrightarrow\quad
 d_+=2,\qquad
 \mathcal C_M=\{1\}\cup\{p:p\mid M\}.} \tag{SC109}
$$
The original cofactor inventory is again prime-only, so SC105
applies without deleting any prime inventory.

The two nonflat seeds cannot both have the same original top
color and the same first output $3$-root. If they did, put them
in the first color, orient that root as $\alpha$, and run the
Section 23 table on the $\nu-2$ flat seeds. Its cost is
$3(\nu-1)$. On root $\beta$ the first color's flat menu covers
all of $H_0$; on root $\alpha$ the second color is entirely flat.
Exactly the argument for SC98 leaves all holes in SC101's set
$R$. One copy of Section 26's packet repairs that entire set,
including the service of both exceptional seeds. The total is
$$
 c=3(\nu-1)+6+5|\mathcal V|
 \le8\nu-7<(\nu-2)^2+4\le N_3. \tag{SC110}
$$
All labels remain distinct by their separate $5$-valuations.
SC103 gives the contradiction.

Thus at equality $b_0=\nu$ the two exceptional seeds must differ
in original top color or in their first output $3$-root. These
are different coordinates: the first is an original safe sibling,
the second encodes an original $5$-root through $\theta$. This packet
argument alone does not exclude the other two-seed configurations,
but its EB1 height-one premise is already excluded by Section 28.
For more composite cofactors, shared original inventories must be
counted with their actual overlaps. At original $A\ge2$, the
additional lower-source liabilities remain part of the whole-cover
obligation; no finite local configuration has been substituted for
an unrestricted cover or noncoverage proof.

## 28. The existing support bound excludes original ternary height one

For the same globally EB1-minimal original whole cover, write
$P=P^+(Q)$ and $H_p=v_p(Q)$. Reuse
[report 385 HPA1](385-private-congruence-hulls-and-crossed-modulus-closure.md#151-height-coded-prime-absorption-bounds-the-entire-original-support):
$$
 P<p^{2H_p+1}\qquad(p\text{ prime},\ p\mid Q).
$$
HPA1 applies before any concentration or small-shared-support
hypothesis. Its one-source transport retains every original cofactor
and lower mixed height. Its complete AP enclosures have distinct
numerical labels and omit the original pure larger-prime class.
EB1 compares against all distinct odd whole covers, so larger output
heights and a changed output period are permitted.

If $A=H_3=1$, this bound gives $P<27$. For that same original
family, [report 385 NF73](385-private-congruence-hulls-and-crossed-modulus-closure.md#58-reuse-the-height-one-source-before-resolving-individual-collision-phases)
reuses report 708 TH3 and gives $P\ge47$. The two existing bounds
exclude $A=1$ at every finite original $5$-height and every choice
of original phases. This uses their ordinary mathematical evidence;
no additional Lean verification is claimed. HPA12 states the same
height exclusion using the separately attributed nine-prime theorem;
that external reduction is not needed for the HPA1--NF73 route here.

Consequently the EB1 height-one inventory bounds in Sections 21--27
are conditional consequences on an already excluded branch, not
further restrictions on a remaining class of minimal counterexamples.
The explicit set-cover packets in Sections 23, 25 and 26 retain
their constructive content whenever their actual supplier menus,
hole containment and numerical-slot conditions hold. Those conditions
must be checked anew in an application at larger original height.

For this transport-and-repair approach, the live original scope is
$A\ge2$. Reuse report 385 HPA/HPM together with SC61--SC62, the
same-tree heavy-root bound, and the $A=2$ private-point construction
SC77--SC78. Budgets from different common trees are not additive.
The missing bridge is a complete repair, or a stronger one-source
transport, that preserves all service of discarded lower originals
as well as omitted tops. In particular, the height-one containment
of the entire hole in both top-color unions cannot be assumed for
lower-representative losses at $A\ge2$. Unrestricted Erdős #7
remains unresolved.

## 29. Two cofactor envelopes retain the complete lower-and-top liability

Keep the hypothetical EB1-minimal whole cover of Section 7, specialize
$r=3,s=5$, and allow arbitrary original height $A\ge2$. Fix one
original terminal prefix and one common tree $\theta$. Thus
$Q=3^A5^BM$, $(M,15)=1$, and the resulting families
$\mathcal L,\mathcal T_1,\mathcal T_2$ satisfy SC15. Here the
subscripts $1,2$ name the two safe terminal siblings; they do not
prescribe their numerical ternary residues. Write
$\mathcal T=\mathcal T_1\sqcup\mathcal T_2$ and regard each output
class $C_d$ as its periodic preimage in $\mathbb Z$. This preserves
its complete service when a fresh output $5$-coordinate is introduced.

Choose $\mathcal R\subseteq\mathcal L$ with at most one actual
representative per numerical output modulus and with output slot $3$
absent. Buy one root $S=[j]_3$. Define the full mandatory omitted-top
set and the retained family by
$$
 \begin{aligned}
 \mathcal B
 &=\{t\in\mathcal T:
       n_t\in\{n_d:d\in\mathcal R\}\cup\{3\}\},
       &b&=|\mathcal B|,\\
 \mathcal F_0
 &=\mathcal R\cup\{S\}\cup(\mathcal T\setminus\mathcal B).
 \end{aligned}
$$
The union denotes a family of APs: their numerical moduli are pairwise
distinct. In particular, every top whose numerical slot is occupied by
$\mathcal R$ or the bought root has been removed, regardless of its
phase or whether its service lies inside $S$.

### Exact count through the original cofactor columns

Let $n_0=\#\{d\in D:3\nmid d\}$ and
$N_3=\#\{d\in D:3\mid d\}$, so $K=n_0+N_3$.
Every surviving source has a nonunit cofactor
$k=5^{b_d}m_d$ after its original $3$-power is removed: lower pure
$3$-powers miss the fixed terminal prefix, and the pure $3^A$ top
misses both safe siblings. Divisor closure puts $k$ in $D$.
The map
$$
 \pi(5^{b_d}m_d)=3^{b_d}m_d
$$
is injective on these $3$-free cofactors. The bought slot $3$ is
$\pi(5)$, and original $5$ belongs to $D$. Consequently the distinct
slots in $\mathcal F_0$ inject into the $n_0$ original $3$-free
columns. With $z=n_0-|\mathcal F_0|\ge0$ and the same
$\Delta=K-|\mathcal R|-|\mathcal T|$ as SC45, the exact identities are
$$
 \boxed{
 |\mathcal F_0|=K-N_3-z,
 \qquad \Delta+b-1=N_3+z.
 } \tag{SC111}
$$
Thus adding a fresh distinct patch family of size $c$ gives
$|\mathcal F_{\rm new}|=K-N_3-z+c$. This count applies at every
original height. It does not identify the entire hole with an
intersection of the original top menus.

### Separate the two kinds of missing service

Define the complete hole and its disjoint decomposition by
$$
 H=\mathbb Z\setminus\bigcup\mathcal F_0,
 \qquad H_{\rm low}=H\cap\bigcup\mathcal L,
 \qquad H_{\rm top}=H\setminus\bigcup\mathcal L.
$$
Choose actual source subfamilies
$$
 \begin{gathered}
 \mathcal W\subseteq\mathcal L\setminus\mathcal R,
 \qquad H_{\rm low}\subseteq\bigcup_{w\in\mathcal W}C_w,\\
 \mathcal B_i\subseteq\mathcal B\cap\mathcal T_i,
 \qquad H_{\rm top}\subseteq\bigcup_{t\in\mathcal B_i}C_t
 \quad(i=1,2),\\
 \ell=|\mathcal W|,
 \qquad \tau=|\mathcal B_1|+|\mathcal B_2|.
 \end{gathered} \tag{SC112}
$$
Taking every discarded lower class not contained in $S$ supplies
$\mathcal W$. Taking every omitted top of each color not contained
in $S$ supplies $\mathcal B_i$: SC15 supplies a top of each color
at every point outside $\bigcup\mathcal L$, and a retained top
cannot contain a point of $H$. Smaller choices require the displayed
whole-set containments. In general $\tau\le b$; equality is not
part of SC112.

For each original $d=3^{a_d}5^{b_d}m_d$, the output $C_d$ keeps its
original residue $\gamma_d\pmod{m_d}$. Make two requests for every
$w\in\mathcal W$ and one for every
$t\in\mathcal B_1\cup\mathcal B_2$. Assume there are integers
$$
 h_{w,1},h_{w,2}\mid m_w,
 \qquad h_t\mid m_t,
$$
all greater than one and globally pairwise distinct. This means
$2\ell+\tau$ different numerical labels, including between the two
colors and between all lower and top requests. They need not be
pairwise coprime; every one divides $M$ and hence is coprime to $15$.
Let $\mathcal J$ be their set. Form the two flat envelope menus
$$
 \begin{aligned}
 \mathcal U
 &=\{[\gamma_w]_{h_{w,1}}:w\in\mathcal W\}
     \cup\{[\gamma_t]_{h_t}:t\in\mathcal B_1\},\\
 \mathcal V
 &=\{[\gamma_w]_{h_{w,2}}:w\in\mathcal W\}
     \cup\{[\gamma_t]_{h_t}:t\in\mathcal B_2\}.
 \end{aligned}
$$
Each envelope contains the whole output of its own source because
its modulus divides $m_d$. An envelope with label $h$ need not have
the phase of the original $h$-class; that original class is not
being relabeled or rephased. Only the added classes below use the
envelope's forced source phase.

If $x\in H_{\rm low}$, an actual $w\in\mathcal W$ containing
$x$ supplies an envelope in each menu. If $x\in H_{\rm top}$,
its actual suppliers in $\mathcal B_1$ and $\mathcal B_2$ do the
same. These two cases give the full packet premise
$$
 \boxed{
 H\subseteq\left(\bigcup\mathcal U\right)
             \cap\left(\bigcup\mathcal V\right),
 \qquad H\cap S=\varnothing.
 } \tag{SC113}
$$
In particular a discarded lower class receives two guaranteed
whole-class enclosures; its points are not assumed to have owners
in both original top colors.

Apply the three-row packet of Section 23 to SC113, with $j$ in
place of $j_5$ and these two flat menus. That packet's coverage
argument uses precisely this containment and avoidance of the bought
root, so its original height-one application imposes no additional
height restriction here. Its new numerical labels are
$$
 \{5,15,45\}\cdot(\{1\}\cup\mathcal J),
 \qquad c=3(1+2\ell+\tau). \tag{SC114}
$$
The different $3$-valuations distinguish rows and the different
$3,5$-free cofactors distinguish labels within a row. All new moduli
are odd nonunits divisible by $5$; every modulus in $\mathcal F_0$
is $5$-free. Thus all labels are distinct and fresh. The common
period can be $5\,3^{\max(B,2)}M$, and every retained phase stays
fixed. The entire integer hole $H$ is covered, including all lower
and displaced-top service.

Combining SC111 and SC114 gives the sufficient descent criterion
$$
 \boxed{
 3(1+2\ell+\tau)<N_3+z
 \quad\Longrightarrow\quad |\mathcal F_{\rm new}|<K.
 } \tag{SC115}
$$
Every EB1 family admitting the complete source assignment above must
therefore satisfy $N_3+z\le3+6\ell+3\tau$. This conclusion retains
the full original inventory and one common source tree.

## 30. Disjoint original columns pay the cofactor-envelope repair

For each $h\mid M$, including $h=1$, define
$$
 w(h)=\#\{(a,b):1\le a\le A,\ 0\le b\le B,
                         \ 3^a5^bh\in D\}.
$$
Unique factorization partitions the original $3$-bearing labels:
$$
 N_3=\sum_{h\mid M}w(h).
$$
These columns are disjoint even when $h\mid h'$: the index is the
entire $3,5$-free cofactor, not the set of labels divisible by a
chosen prime. Since $|\mathcal J|=2\ell+\tau$, the exact saving
of Section 29's completed repair is
$$
 \begin{aligned}
 K-|\mathcal F_{\rm new}|
 ={}&z+w(1)-3+\sum_{h\in\mathcal J}(w(h)-3)\\
 &+\sum_{\substack{h\mid M\\h\notin\mathcal J\cup\{1\}}}w(h).
 \end{aligned} \tag{SC116}
$$
In particular, $w(1)\ge4$ and $w(h)\ge3$ for every assigned
$h\in\mathcal J$ suffice for strict descent. No extra donor class
is removed from $\mathcal F_0$: these counts bound the difference
$K-|\mathcal F_0|$ already proved in SC111. They add no unrecorded
service liability.

If a requested divisor $h$ comes from original
$d=3^{a_d}5^{b_d}m_d$ with $h\mid m_d$, divisor closure supplies
all distinct original labels
$$
 3^i5^jh,\qquad 1\le i\le a_d,\quad 0\le j\le b_d.
$$
Consequently $w(h)\ge a_d(b_d+1)$. Pure $3,\ldots,3^A$ together
with the divisors $3^i5^j$ for $1\le i\le a_d$ and
$1\le j\le b_d$ also give $w(1)\ge A+a_db_d$. Define
$$
 \rho=\max\bigl(
 \{a_db_d:d\in\mathcal W\cup\mathcal B_1\cup\mathcal B_2\}
 \cup\{0\}\bigr).
$$
The shared unit column satisfies $w(1)\ge A+\rho$; the maximum
cannot be replaced by a sum of source contributions. Applying these
bounds separately to the globally distinct requested columns yields
$$
 \boxed{
 \begin{aligned}
 K-|\mathcal F_{\rm new}|\ge\Xi
 :={}&z+A+\rho-3\\
 &+2\sum_{w\in\mathcal W}\bigl(a_w(b_w+1)-3\bigr)\\
 &+\sum_{t\in\mathcal B_1\cup\mathcal B_2}
                          \bigl(A(b_t+1)-3\bigr).
 \end{aligned}
 } \tag{SC117}
$$
Here $a_t=A$ for every selected top. The summands may be negative;
SC117 does not discard those deficits. The sufficient condition
$\Xi\ge1$ contradicts EB1. If it fails, the unassigned columns
still present in SC116 can contribute to the saving, so failure is
not evidence that a complete repair is impossible.

## 31. An anchored height-two branch has a complete paid repair

Set $A=2$ and use the private-point tree SC77--SC78 with $r=3,s=5$.
It preserves one actual private point of original $9$ and removes
every lower pure-cofactor original. Choose exactly one representative
from every surviving lower numerical slot, preferring its actual
height-zero original whenever that original survives. There is no
lower slot $3$, because all lower pure-cofactor columns have vanished.
Every discarded lower source then has
$$
 a_w=1,\qquad m_w>1.
$$
Indeed, a lower column has at most its original heights zero and
one; its height-zero member cannot be discarded by this preference,
and a column with only one survivor loses nothing. All its survivors
have nonunit $M$-cofactor by the anchored-tree property.

If a top of output modulus $3$ survives, choose the bought root $S$
with that top's exact output phase. It is unique because top output
moduli are injective. Its entire class is then absorbed by $S$.
If no such top survives, choose any root. No other pure-cofactor
top can be mandatory: its output is $3^b$, whereas $\mathcal R$
has no pure-cofactor slot, and the bought root occupies only $3$.
Let $\epsilon=1$ when the pure output-$3$ top is omitted and
absorbed, and $\epsilon=0$ otherwise.

For the following explicit choice, take $\mathcal B_1,\mathcal B_2$
to contain **all** remaining mandatory tops of their respective colors,
including any nonpure top whose service already lies in $S$. They
have $m_t>1$, satisfy SC112, and obey
$$
 b=\tau+\epsilon. \tag{SC118}
$$
Choose any $\mathcal W$ satisfying the complete lower-service
condition SC112. Under the globally distinct divisor assignment of
Section 29, SC117 specializes to
$$
 \begin{aligned}
 \Xi={}&z-1+\rho
        +2\sum_{w\in\mathcal W}(b_w-2)
        +\sum_{t\in\mathcal B_1\cup\mathcal B_2}(2b_t-1),\\
 \rho={}&\max\bigl(
       \{b_w:w\in\mathcal W\}
       \cup\{2b_t:t\in\mathcal B_1\cup\mathcal B_2\}
       \cup\{0\}\bigr).
 \end{aligned} \tag{SC119}
$$
Suppose that assignment exists and
$$
 b_w\ge2\quad(w\in\mathcal W),
 \qquad b_t\ge1\quad(t\in\mathcal B_1\cup\mathcal B_2).
$$
If there is at least one request, then $\rho\ge2$, all lower
summands in SC119 are nonnegative, and each top summand is at least
one. Hence
$$
 \boxed{
 \Xi\ge z+1+\tau,
 \qquad |\mathcal F_{\rm new}|\le K-(z+1+\tau)<K.
 } \tag{SC120}
$$
If there are no requests, SC112 makes both parts of $H$ empty, so
$\mathcal F_0$ itself covers. SC111 and $N_3\ge A=2$ already give
strict descent, without adding the three unconditional packet rows.
This excludes the stated height-two branch with arbitrary finite
$5$-height and arbitrary finite support and heights in $M$. It does
not use a lower bound for the largest support prime or the attributed
nine-prime theorem.

There is a separate payment test from the same anchored tree.
SC78 gives $\Delta\ge B+4$, while SC114 and SC118 give
$c-b=3+6\ell+2\tau-\epsilon$. The count
$|\mathcal F_{\rm new}|=K-\Delta+1+c-b$ therefore strictly descends
whenever
$$
 \boxed{6\ell+2\tau\le B-1+\epsilon.} \tag{SC121}
$$
This uses the anchored budget as an alternative to SC116--SC119,
not as additional credit. A smaller pair of top subfamilies may
still satisfy SC112 and use fewer requests, but then SC118 is
unavailable: its actual mandatory count remains $b$, and the exact
budget test is $3+6\ell+3\tau-b\le B+2$.

For example, suppose one discarded lower class supplies the whole
remaining hole, and there are no mandatory nonpure tops. If its
cofactor $m$ is composite, choose two different nonunit divisors of
$m$ for its two requests. The packet uses nine classes. For $m=77$
one choice is $h_{w,1}=7,h_{w,2}=11$, giving labels
$$
 5,15,45,\quad35,105,315,\quad55,165,495.
$$
Their cofactor phases are reductions of that same actual discarded
class. SC121 pays this complete repair for $B\ge7-\epsilon$,
without restricting the lost output's ternary height. The condition
that this one source supplies the entire remaining hole is essential.

The global assignment remains a substantive hypothesis. A prime
cofactor offers only one nonunit divisor and cannot supply two
different requests on its own. Different lower or top sources can
compete for the same divisor pool. At $A>2$ the anchored argument
above does not remove all lower pure-cofactor sources, which have no
nonunit $M$-divisor at all. Shallow assigned columns can also fail to
pay their three packet rows. SC116 retains those deficits and the
unused inventory exactly. What is not established is that some
single source tree, retained family and complete supplier choice
always admit a globally distinct divisor assignment satisfying
SC115, or a different complete packet for the unassignable sources.
These are ordinary mathematical sufficient conditions; they do not
constitute a Lean verification or an unrestricted resolution of
Erdős #7.

## 32. Four nonunit output divisors per source pay a complete repair

Keep Section 29's one actual source tree, retained family
$\mathcal F_0$, complete integer hole $H$, and exact count SC111.
Thus every retained modulus is $5$-free and
$|\mathcal F_0|=K-N_3-z$, with $z\ge0$. Assume $A\ge2$.
Choose a finite family $\mathcal W_*$ of actual discarded lower or
omitted top sources such that
$$
 \begin{gathered}
 H\subseteq\bigcup_{d\in\mathcal W_*}C_d,\qquad
 d=3^{a_d}5^{b_d}m_d,\quad m_d\ge1,\quad m_d\mid M,\\
 C_d=[\eta_d]_{3^{b_d}m_d},\qquad 3\cdot5^{b_d}m_d\in D.
 \end{gathered} \tag{SC122}
$$
The phase $\eta_d$ is the actual output phase of that source under
the fixed tree. In particular, its ternary part is not replaced by
the original phase of an unrelated divisor. The containment concerns
all of $H$, including every integer lift and all discarded lower
service; it is not a condition only on individual private points.

For every fixed common tree, the following retained-family choice
supplies SC122 before imposing the matching below. Choose exactly
one actual lower representative in every surviving numerical slot
except $3$. These representatives may be chosen by their actual
phases; no preference for original height zero is required. If
$15\notin D$ and original $5$ survives, buy its exact output class
$S=C_5$; otherwise choose any root. Form the full mandatory top
set and $\mathcal F_0$ as in Section 29 using these choices.

A discarded lower source in a slot other than $3$ shares its
cofactor $k=5^bm$ with the retained representative. The two distinct
original labels have different $3$-heights, so at least one height
is positive. Divisor closure supplies $3k\in D$, even when the
discarded source itself has height zero. In slot $3$, the cofactor
is $k=5$. If there is any positive-height original in this column,
then $15\in D$ supplies the same qualification. Otherwise the only
possible discarded source is original $5$, and the chosen $S$ pays
its whole output. Thus every point of $H_{\rm low}$ has a
discarded lower supplier satisfying the inventory condition in
SC122. For a point of
$H_{\rm top}$, SC15 supplies a top owner in either fixed safe
color. That owner is mandatory, since a retained top would cover
a point of $H$; its original height is $a_d=A\ge1$.

Take these qualified discarded lower suppliers together with
the mandatory tops of one fixed color, omitting any source already
contained in $S$. This finite family covers all of $H$, including
every integer lift, and satisfies SC122 for every $A\ge2$.
Pure-cofactor sources are permitted. The retained phases, all
supplier phases and both terminal-color cover identities come
from the same original family and the same $\theta$; no
private-point anchoring or second optimized tree is required.

### Match complete numerical slots, allowing the cofactor to repeat

For each supplier define its finite slot menu
$$
 \mathcal N_d
 =\{3^j h:0\le j\le b_d,\quad h\mid m_d,\quad 3^jh>1\}
 =\{n>1:n\mid3^{b_d}m_d\}.
 \tag{SC123}
$$
Request four slots $n_{d,r}=3^{j_{d,r}}h_{d,r}\in\mathcal N_d$,
one for each $r=1,2,3,4$, with all requested numerical slots
globally distinct. The same $h$ may occur in different requests
provided their $j$ values differ. In particular $h=1$ is allowed
when $j\ge1$; only the unit slot $j=0,h=1$ is excluded. This is
a larger menu than the globally distinct $M$-divisor assignment in
Section 29, and it remains meaningful for a pure-cofactor source
$m_d=1$.

The finite Hall theorem, applied to four copies of each supplier,
gives exactly the condition
$$
 \left|\bigcup_{d\in\mathcal X}\mathcal N_d\right|
       \ge4|\mathcal X|
 \qquad\text{for every }\mathcal X\subseteq\mathcal W_*.
 \tag{SC124}
$$
This reuses the demand-copy matching method of
[report 385, Section 64](385-private-congruence-hulls-and-crossed-modulus-closure.md#64-the-common-literal-zero-root-makes-deep-feasibility-a-static-hall-condition)
and the nested-slot method DP12 in its
[Section 69](385-private-congruence-hulls-and-crossed-modulus-closure.md#69-cross-cofactor-divisor-payment-reduces-exactly-to-nonconcentrated-ancestors); no new matching
theorem is needed. The condition is global: separate four-slot
menus for individual sources do not imply SC124.

### Four nonzero roots cover the complete service of every supplier

Buy the class $[0]_5$. For every matched request add the CRT class
$$
 B_{d,r}
 =\{x:x\equiv r\pmod5,\quad
         x\equiv\eta_d\pmod{n_{d,r}}\},
 \qquad r=1,2,3,4.
 \tag{SC125}
$$
This is the existing whole-class root splitting used in
[report 385, Section 200, LP3--LP4](385-private-congruence-hulls-and-crossed-modulus-closure.md#200-a-vacant-lower-prime-layer-gives-a-whole-cover-descent),
with source-dependent divisor labels. Indeed
$n_{d,r}\mid3^{b_d}m_d$ and $5\nmid n_{d,r}$, so every point
of $C_d$ in the root $r$ belongs to $B_{d,r}$. Its root-zero
points belong to $[0]_5$. SC122 therefore makes these classes
cover the whole hole $H$; points outside $H$ retain their owner
in $\mathcal F_0$.

The added numerical labels are $5$ and the $5n_{d,r}$. They are
pairwise distinct odd nonunits, since all $n_{d,r}$ are different
and greater than one. They are all fresh relative to the $5$-free
family $\mathcal F_0$. Every retained phase stays fixed. For
$\mathcal W_*\ne\varnothing$ this complete repair uses exactly
$c=1+4|\mathcal W_*|$ added classes; write
$\mathcal F_{\rm new}=\mathcal F_0\cup\{[0]_5\}\cup\{B_{d,r}\}$.

### Each matched slot has its own original donor

For the requested slot $n=3^jh$, use the numerical original donor
$3\cdot5^jh$. The column qualification $3\cdot5^{b_d}m_d\in D$
in SC122 and divisor closure supply it, because $j\le b_d$ and
$h\mid m_d$. The donor need not divide the particular discarded
original when that source has height zero. It may even be the
original supplying a retained representative: SC111 already counts
the full original column. Its phase is not used for the added patch,
and no further original is deleted from $\mathcal F_0$.

Because $(h,15)=1$, the correspondence
$3^jh\longmapsto3\cdot5^jh$ is injective. Hence the globally
distinct requests give $4|\mathcal W_*|$ different original
$3$-bearing labels, even when their cofactors repeat. If $h>1$,
the donor has a nonunit $3,5$-free factor. If $h=1$, then $j\ge1$
and the donor contains $5$. In either case it is not one of the
original pure labels $3,\ldots,3^A$. Thus
$$
 N_3\ge4|\mathcal W_*|+A,\qquad
 K-|\mathcal F_{\rm new}|
 =N_3+z-(1+4|\mathcal W_*|)
 \ge A+z-1\ge1.
 \tag{SC126}
$$
This is a strict whole-cover descent under SC122 and SC124. It
uses the original inventory already present in SC111, without
adding a second repair budget or leaving donor service unpaid.
If $\mathcal W_*=\varnothing$, SC122 gives $H=\varnothing$;
then $\mathcal F_0$ itself covers and SC111 gives strict descent
without adding any patch.

### The full common-cofactor menu has an exact height threshold

Suppose all chosen sources have the same cofactor $m\ge1$ and
order them so that $b_1\le\cdots\le b_t$. Write $\tau(m)$ for
the number of positive divisors of $m$. Because $(m,3)=1$, the
full menu of supplier $i$ has exactly
$(b_i+1)\tau(m)-1$ slots: every pair $(j,h)$ gives a different
divisor, and only $(0,1)$ is removed. These menus are nested.
The existing nested-slot matching criterion DP12 therefore gives
exactly
$$
 \boxed{(b_i+1)\tau(m)-1\ge4i\qquad(1\le i\le t).}
 \tag{SC127}
$$
This is necessary and sufficient for the four-request assignment
within this full common-cofactor menu, not for every possible
repair. It allows different actual phases for all sources; only
the numerical slots are assigned injectively. In particular:

- If $m$ is prime, SC127 is equivalent to $b_i\ge2i$.
- If $m=1$, SC127 is equivalent to $b_i\ge4i$.

If the entire hole lies in one actual source with prime cofactor
$m$, output height $b_d\ge2$ and the column qualification SC122,
use slots $3,m,3m,9m$. The five added labels are
$$
 5,\quad15,\quad5m,\quad15m,\quad45m.
$$
The four distinct original donors are
$15,3m,15m,75m$. None is a pure power of $3$. Each added phase
is given by SC125, using the same actual source residue reduced
at the chosen divisor. The pure $3$-powers provide the strict
saving in SC126. A prime cofactor at $b_d=2$ has five nonunit
output divisors, even though it has only one nonunit $M$-divisor.

Likewise a single actual pure-cofactor source with $b_d\ge4$
uses slots $3,9,27,81$, added labels $5,15,45,135,405$, and original
donors $15,75,375,1875$. This application still requires
the column qualification and complete hole containment. No positive lower bound
for $m_d-1$ enters the service or donor argument.

The original column must contain a positive-height label to justify
this payment; the discarded source itself need not have positive
height. The retained-family choice above guarantees that qualification
for the complete supplier family. An arbitrarily discarded height-zero
source without it need not have the required donors. The remaining
unproved step is SC124 for some
complete source choice on one common tree: sources may still
compete for too few nonunit output divisors. The result reuses
whole-class splitting, Hall matching and the original divisor
inventory. It does not provide a new general matching theorem,
a Lean verification or a literature-priority claim.

## 33. A common liability hull can replace several source requests

Keep Section 32's retained family and its actual phases.
If $H=\varnothing$, the existing count already gives a descent.
Otherwise put $N=3^BM$, the common $5$-free period, choose $w\in H$,
and define
$$
 V_3=\{3^b h>1:3\cdot5^b h\in D,\ (h,15)=1\},
 \qquad
 \Gamma_H=\gcd\bigl(N,\{x-w:x\in H\}\bigr).
 \tag{SC128}
$$
The set $V_3$ uses the whole original inventory, not only selected
suppliers. It consists of nonunit divisors of $N$ and is closed
under taking nonunit divisors. Each member has its own original
donor under the map of Section 32. The hull can be computed in
one complete $N$-period. Reuse
[report 385, PH3--PH4](385-private-congruence-hulls-and-crossed-modulus-closure.md#2-the-complete-private-region-supplies-more-than-divisor-closure),
as already applied to complete liabilities in SC49: for $n\mid N$,
$H\subseteq[w]_n$ exactly when $n\mid\Gamma_H$. The set here is
the entire $H_{\rm low}\cup H_{\rm top}$, not a union of separately
chosen private regions.

Suppose there are four distinct nonunit slots
$n_1,\ldots,n_4\in V_3$ dividing $\Gamma_H$. Add $[0]_5$ and
the four classes $[r]_5\cap[w]_{n_r}$, $r=1,2,3,4$.
They cover all of $H$ and have distinct fresh labels $5,5n_1,\ldots,5n_4$.
Membership in $V_3$ supplies an actual original donor for each slot,
without requiring a selected supplier whose whole output it contains.
Section 32's donor
injection and pure-power count therefore give
$$
 \left|\{n\in V_3:n\mid\Gamma_H\}\right|\ge4
 \quad\Longrightarrow\quad
 |\mathcal F_{\rm new}|=|\mathcal F_0|+5
       \le K-(A+z-1)<K.
 \tag{SC129}
$$
The patch phase is fixed by the actual hole point $w$; agreement
with an original donor phase is not assumed. A divisor of $\Gamma_H$
outside $V_3$ does not receive this automatic donor payment.

### Group sources only when their actual phases admit a common enclosure

For a complete qualified supplier family as in SC122, partition
$\mathcal W_*$ into nonempty groups $X$.
Writing $n_d=3^{b_d}m_d$, choose $d_X\in X$ and put
$$
 \Gamma_X
 =\gcd\bigl(\{n_d:d\in X\},
             \{\eta_d-\eta_{d_X}:d\in X\}\bigr).
 \tag{SC130}
$$
The existing union-hull rule in
[report 385, Section 85](385-private-congruence-hulls-and-crossed-modulus-closure.md#85-the-three-actual-square-residuals-have-no-further-congruence-concentration)
identifies this as the common congruence hull of the whole union
$\bigcup_{d\in X}C_d$. For every $n\mid\Gamma_X$, that union
lies in $[\eta_{d_X}]_n$; the numerical divisibility alone would
not establish the phase agreement.

Assume each group has four nonunit divisors $n_{X,r}\mid\Gamma_X$,
with all these slots globally distinct. Use one shared class
$[0]_5$ and the classes $[r]_5\cap[\eta_{d_X}]_{n_{X,r}}$.
Each group is covered on every $5$-root, so SC122 pays the entire
hole. Every selected slot divides the output modulus of each source
in its group and, by the column qualification, belongs to $V_3$.
If there are $g$ groups,
the same donor injection gives
$$
 N_3\ge4g+A,\qquad
 |\mathcal F_{\rm new}|=K-N_3-z+1+4g
       \le K-(A+z-1)<K.
 \tag{SC131}
$$
Singleton groups recover Section 32's four-request assignment.
Allowing larger groups is a weaker sufficient condition: it can use
one packet for several sources whose actual phases agree on enough
common divisors. It does not assume that Hall failure supplies such
agreement.

### Equal numerical menus can have different common hulls

For a prime $m>5$, compare the two pairs of actual APs
$$
 \begin{array}{c|c|c}
 C_1&C_2&\text{common hull}\\\hline
 [0]_{27m}&[9m]_{27m}&9m\\
 [0]_{27m}&[1]_{27m}&1.
 \end{array}
 \tag{SC132}
$$
Both pairs have $b_1=b_2=3$ and the same seven nonunit output
divisors, so the eight individual requests fail SC124. In the first
pair the two APs are distinct, but their common hull has the four
different divisors $3,m,3m,9m$. One group therefore has the packet
above. In the second pair no nonunit AP contains their whole union.
Both pairs avoid $[2]_3$.

These are interface examples of periodic APs, not asserted realizations
of a complete EB1 original cover. They separate numerical menu data
from the actual phase relation needed by a common packet. Neither
SC129 nor the grouped condition has been forced for some common tree
and retained family in every hypothetical cover. The result reuses
the existing congruence hull and the complete service and donor checks
of Section 32; it asserts no new Lean verification or unrestricted
noncoverage theorem.

## 34. The whole original inventory pays shallow complete-source repairs

Keep the same actual retained family $\mathcal F_0$, bought root
$S=[j]_3$ and complete integer hole $H$ from Section 29. Thus
$H\cap S=\varnothing$ and
$|\mathcal F_0|=K-N_3-z$ with $z\ge0$. A finite fresh repair
with $c$ classes gives strict descent whenever $c<N_3+z$.
This uses the full original inventory already present in SC111;
matching each patch to a different supplier divisor is sufficient
for payment but is not necessary.

The packets below reuse Sections 23 and 26. Their additional
application is to the complete lower-and-top liability at arbitrary
original height $A\ge2$. No height-one assertion that both top colors
cover the whole hole is imported: each required containment is stated
for this actual $H$.

### One unbought root and a small cofactor menu

Suppose $\alpha\ne j\pmod3$, and let
$C_i=[\eta_i]_{m_i}$ for $1\le i\le t$, where the numerical
$m_i>1$ are odd, distinct and coprime to $15$. Assume
$$
 H\subseteq[\alpha]_3\cap\bigcup_{i=1}^t C_i.
 \tag{SC133}
$$
The classes may be cofactor projections of actual suppliers, or other
enclosures whose containment SC133 has been established on the same
source. Neither numerical divisibility alone nor a list of selected
private points supplies SC133.

Use Section 26's packet with this cofactor menu, starting at fresh
$5$-depth one rather than two. The source of that packet already
has a fixed first $5$-digit; removing that fixed digit gives the
following explicit instance. Write $\alpha\in\{0,1,2\}$.
In a menu row add one class for every $C_i$.

| New $5$-condition | New $3$-condition | Cofactor menu | Numerical moduli |
|---|---|---|---|
| $[0]_5$ | none | one | $5$ |
| $[1]_5$ | none | $C_i$ | $5m_i$ |
| $[2]_5$ | $[\alpha]_3$ | one | $15$ |
| $[3]_5$ | $[\alpha]_3$ | $C_i$ | $15m_i$ |
| $[4]_5$ | $[\alpha]_9$ | one | $45$ |
| $[4]_5$ | $[\alpha+3]_9$ | $C_i$ | $45m_i$ |
| $[4]_{25}$ | none | one | $25$ |
| $[9]_{25}$ | none | $C_i$ | $25m_i$ |
| $[14]_{25}$ | $[\alpha]_3$ | one | $75$ |
| $[19]_{25}$ | $[\alpha]_3$ | $C_i$ | $75m_i$ |
| $[24]_{25}$ | $[\alpha+6]_9$ | one | $225$ |

For a point of the right side of SC133, the first four rows pay
the first four $5$-roots. On the remaining root, the next two rows
pay two of the three next ternary digits. Its last ternary child
has five next $5$-digits, all paid by the last five rows. This is
the same complete-lift coverage argument as SC101--SC102.
There are six unconditional classes and five classes per cofactor.
The pairs of $3$- and $5$-valuations distinguish the six rows of
numerical factors, and the distinct $3,5$-free cofactors distinguish
labels within each row. All new labels contain $5$, while every
retained modulus is $5$-free. Consequently
$$
 \boxed{
 c=6+5t,\qquad
 K-|\mathcal F_{\rm new}|=N_3+z-(6+5t),\qquad
 6+5t<N_3+z\ \Longrightarrow\ |\mathcal F_{\rm new}|<K.
 } \tag{SC134}
$$
No retained phase changes, and all points outside $H$ retain their
old owner. For $t=0$, SC133 instead makes $H$ empty, and no packet
is needed.

The existing all-height inventory bounds give useful automatic
payment. [Report 385, NF67](385-private-congruence-hulls-and-crossed-modulus-closure.md#56-the-original-cover-needs-enough-small-prime-labels-to-block-compression)
gives $N_3\ge P-1$. Together with the repository's existing
seven-support-prime exclusion recorded there, it gives $N_3\ge22$.
The stronger [NF82](385-private-congruence-hulls-and-crossed-modulus-closure.md#60-the-two-first-root-branches-share-one-original-label-inventory)
gives $N_3\ge31$ in every height case, retaining its separately
attributed nine-prime-support premise and ordinary evidence scope.
Thus SC133 is impossible for an EB1 cover in either stated branch:
$$
 \begin{array}{c|c|c}
 \text{reused inventory bound}&\text{number of cofactors}&
             \text{maximum packet cost}\\\hline
 N_3\ge22&1\le t\le3&21\\
 N_3\ge31&1\le t\le4&26.
 \end{array}
 \tag{SC135}
$$
The general criterion remains SC134. At $t=5$ the packet costs
$31$; the lower bound $N_3\ge31$ alone does not give strict
descent. These rows share one $H$ and one root $\alpha$.
Different roots, or different phases at the same numerical $m_i$,
cannot be combined by simply adding their separate packet costs.

### A flat composite source uses the existing nine-class packet

Suppose the entire hole lies in $C=[\eta]_m$, where
$(m,15)=1$ and $m$ is odd and composite. Choose two distinct nonunit
divisors $h_1,h_2\mid m$. The same actual source supplies both
enclosures $[\eta]_{h_1}$ and $[\eta]_{h_2}$. Hence
$$
 H\subseteq[\eta]_{h_1}\cap[\eta]_{h_2},\quad H\cap S=\varnothing,
 \qquad
 \operatorname{moduli}(\mathcal B)
     =\{5,15,45\}\cdot\{1,h_1,h_2\},\quad c=9.
 \tag{SC136}
$$
Section 23's table, as already applied to two enclosures in
Section 29, covers this whole liability with those nine distinct
fresh labels. It can serve both unbought ternary roots; SC133 is
not required. The sufficient payment condition is $9<N_3+z$,
already supplied by $N_3\ge22$. This uses the whole inventory,
so the particular three-row donor bounds in SC117 are unnecessary
for this application.

### A complete shallow prime class has exact fresh-five cost eleven

Let $m\ge7$ be prime and let $C=[\eta]_{3m}$ be a complete
integer AP. Among finite families of distinct odd numerical moduli
all divisible by $5$, with arbitrary other prime factors, heights
and phases, the exact minimum number of classes covering $C$ is
$$
 \boxed{\min|\mathcal B|=11.} \tag{SC137}
$$
The single-cofactor instance of the table above attains eleven,
with labels
$\{5,15,45,25,75,225\}\cup m\{5,15,45,25,75\}$.
Its construction covers the entire $C$ and does not use any
retained service. In an application to $H$, if its ternary root
is $j$ then $H\subseteq C$ makes $H$ empty; otherwise SC134
with $t=1$ pays the complete repair.

For the lower bound, suppose a repair of at most ten classes
covers $C$, and pull it back along $x=\eta+3m u$. Discard
empty restrictions and reduce to an irredundant cover of the
whole integer parameter line. Every induced relative index is
$\delta=d/\gcd(d,3m)$ and is divisible by $5$. Reuse the
published Simpson whole-LCM bound SC39: for the actual LCM $L$
of this irredundant cover, its cardinality $k$ satisfies
$k\ge1+f(L)$.

If $L$ has a prime factor $q\ge7$, then
$k\ge1+4+(q-1)\ge11$, a contradiction. Otherwise $L$ is
supported on $3,5$. Every remaining original repair label must
then be $3^j5^\ell h$ with $h\in\{1,m\}$, and its relative
index is $3^{\max(j-1,0)}5^\ell$. Numerical distinctness permits
at most four preimages of a fixed index $5^\ell$, and at most two
preimages of a fixed index $3^a5^\ell$ for $a\ge1$.

If all relative indices are powers of $5$, their finite reciprocal
sum is strictly less than $4\sum_{\ell\ge1}5^{-\ell}=1$, so they
cannot cover. If all relative $5$-heights equal one, at most four
index-five classes can pay four first $5$-roots. On an unpaid
root the remaining classes have at most two relative restrictions
of each index $3^a$, whose finite total mass is strictly below
$2\sum_{a\ge1}3^{-a}=1$. This also cannot cover. Therefore
the actual irredundant LCM must satisfy
$$
 v_3(L)\ge1,\qquad v_5(L)\ge2,\qquad
 k\ge1+f(L)\ge1+2+8=11.
 \tag{SC138}
$$
This proves the lower bound by reusing SC39, not by restricting
the search to the displayed attaining labels. The minimum concerns
covering the entire $C$ using only $5$-bearing new classes. A
smaller actual $H\subsetneq C$, help from other retained classes,
or repairs using $5$-free labels can have a different minimum.

### A flat prime envelope cannot be repaired within its one-prime palette

Let $m\ge7$ be prime, $C=[\eta]_m$ and
$P=C\setminus S$. Consider all possible fresh labels
$3^j5^k m^e$, with $j,e\ge0$ and $k\ge1$, allowing
arbitrary finite depths and arbitrary phases, but only one class
per numerical modulus. Normalize Haar probability on the entire
periodic set $P$, including every higher-digit lift.

The maximal mass factor in the ternary coordinate is one for
$j=0$ and $3^{1-j}/2$ for $j\ge1$. The $5$ factor is
$5^{-k}$. The $m$ factor is one for $e=0,1$ and $m^{1-e}$
for $e\ge2$. These bounds use a single product law on this
complete envelope; incompatible phases only decrease the mass.
Summing even the entire infinite numerical palette gives
$$
 \begin{aligned}
 \mu(U_{\rm patches})
 &\le
 \left(1+\sum_{j\ge1}\frac{3^{1-j}}2\right)
 \left(\sum_{k\ge1}5^{-k}\right)
 \left(2+\sum_{e\ge2}m^{1-e}\right)\\
 &=\frac7{16}\left(2+\frac1{m-1}\right)
 \le\frac{91}{96}<1.
 \end{aligned}
 \tag{SC139}
$$
Thus no finite family in this palette covers the complete
$C\setminus S$, regardless of its class budget. Restricting to
$e=0,1$ gives the smaller bound $7/8$. More powers of the same
cofactor prime therefore do not repair this obstruction. Additional
cofactor primes or $5$-free repair classes are outside the claim.
Most importantly, an actual smaller hole $H\subsetneq C\setminus S$
need not carry this product law, so SC139 does not rule out repairing
that $H$ or constitute an EB1 noncovering example.

These consumers separate a failure of the four-slot assignment from
a failure of every permitted repair. A complete one-root liability
with a small cofactor menu, and a complete flat composite-source
liability, are already paid by existing packets and inventory bounds.
The missing step is to force suitable complete containments for one
actual tree, or to handle the remaining phase and palette patterns.
No new matching theorem, Lean verification or unrestricted odd
noncoverage result is asserted.

## 35. Two equal output labels can obstruct grouping and repair in a fixed palette

Keep $A\ge2$ and fix one actual common source map $F_u$ under the
same tree. Suppose that two comparable originals
$d_i=3^{a_i}5^2m$, with $0\le a_1<a_2\le A$ and prime $m>5$,
both survive under that map. Their actual outputs are
$$
 C_i=[\eta_i]_{9m},\qquad
 \eta_1\not\equiv\eta_2\pmod{9m},\qquad
 \mathcal N_1=\mathcal N_2=\{3,9,m,3m,9m\}.
 \tag{SC140}
$$
The phase inequality reuses comparable-class disjointness and the
common-source pullback property from
[report 844, Section 1](../600-649/844-collision-moment-needs-cofactor-packing.md#1-a-positive-term-is-not-a-phase-collision).
It is not inferred from the numerical collision alone.

### A larger selected family cannot repair this pair by four-slot grouping

Each single supplier has five slots and passes its four-request test.
Together they request eight slots from the same five-slot pool, giving
an inclusion-minimal supplier deficit of three in SC124.

More strongly, every selected supplier family containing this pair
fails SC131, regardless of its other suppliers and their partition.
If the pair belongs to different groups, each group's hull divides
$9m$. Those two groups still need eight globally distinct nonunit
divisors from the same five-slot pool. If the pair belongs to the
same group, its hull divides
$\gcd(9m,\eta_1-\eta_2)$, a proper divisor of $9m$. Every proper
divisor of $9m$ has at most three nonunit divisors, so that group
cannot receive four slots. Adding suppliers to either group only
reduces its hull. This argument uses the union-hull rule SC130;
larger original donor inventory does not enlarge a whole-class hull.

### Separated ternary and cofactor phases exclude arbitrary finite splitting

Impose the additional phase conditions
$$
 \eta_1\not\equiv\eta_2\pmod3,\qquad
 \eta_1\not\equiv\eta_2\pmod m,\qquad E=C_1\cup C_2.
 \tag{SC141}
$$
They do not follow from SC140. Consider any finite family
$\mathcal P$ of APs with
pairwise distinct numerical moduli in the complete set
$$
 \{3^j5^kh:j\ge0,\ k\ge1,\ h\in\{1,m\}\}.
$$
Their phases are arbitrary. This family may split either source into
arbitrarily many pieces and may use arbitrary finite $3$- and
$5$-depths; it need not follow a four-request or grouping assignment.

Choose integers $J\ge2$ and $L\ge1$ bounding all added exponents
$j$ and $k$. Give $E$ its normalized uniform measure $\mu_E$ in
the common period $3^J5^Lm$. Each $C_i$ has mass $1/2$, and its
$5$-coordinate is unrestricted. The complete-fibre CRT calculation
of SC41 gives the following upper bounds for an AP of each modulus:
$$
 \begin{array}{c|cc}
 &h=1&h=m\\\hline
 j=0&5^{-k}&\tfrac12 5^{-k}\\
 j=1,2&\tfrac12 5^{-k}&\tfrac12 5^{-k}\\
 j\ge3&\tfrac12 3^{2-j}5^{-k}&\tfrac12 3^{2-j}5^{-k}.
 \end{array}
 \tag{SC142}
$$
For $j=0,h=m$, the two distinct cofactor phases permit at most one
source. For $j\ge1$, the two distinct ternary roots likewise
permit at most one source. Beyond height two, fixing additional
ternary digits retains only the fraction $3^{2-j}$ of that complete
source class. These bounds hold for every choice of added phases.

Distinct numerical moduli permit at most one AP per triple $(j,k,h)$.
Consequently the union bound over all slots in the finite rectangle gives
$$
 \begin{aligned}
 \mu_E\!\left(\bigcup\mathcal P\right)
 &\le\sum_{k=1}^{L}5^{-k}
      \left(1+\frac12+2+\sum_{j=3}^{J}3^{2-j}\right)\\
 &=\left(1-5^{-L}\right)
      \left(1-\frac{3^{2-J}}8\right)<1.
 \end{aligned}
 \tag{SC143}
$$
Thus no such finite family covers the complete $E$. Equivalently,
the infinite slot capacities sum to exactly one, while every finite
slot set has strictly smaller total capacity. This reuses the
finite-capacity strictness of
[report 385, VH2--VH3](385-private-congruence-hulls-and-crossed-modulus-closure.md#20-actual-mixed-column-heights-determine-the-available-repair-forest)
and its
[two-fibre capacity argument](385-private-congruence-hulls-and-crossed-modulus-closure.md#202-the-old-cofactor-palette-cannot-cheaply-repair-two-full-fibres),
with the two actual phase restrictions above.

### The selected pair and its complete service remain conditional

The first obstruction concerns a selected supplier family that
contains both actual outputs. It does not force every complete
supplier choice to contain that pair. SC15 supplies all top service
with either fixed safe color, and changing retained representatives,
replacing suppliers or combining suppliers from the two colors may
avoid the pair. Outputs from different common maps cannot be assigned
the same-source phase inequality without a separate argument.

The capacity obstruction concerns the entire union $E$, not merely
$E\cap H$. It applies to an actual repair only when that complete
service remains unpaid by the retained classes. Neither the existence
of this pair in a hypothetical EB1 cover nor the inclusion $E\subseteq H$
is established here. New cofactor types, including $m^2$, lie outside
the specified set of allowed moduli. The result gives a concrete
limit on grouping and deeper splitting within that set, not an
unrestricted odd-covering obstruction or a Lean verification.

## 36. Original donor depth funds a complete multilevel repair

Keep the one-source setup and complete qualified supplier family
$\mathcal W_*$ of SC122. For a nonunit divisor $s=3^b h$ of
$N=3^BM$, put $\chi(s)=5^b h$, where $(h,15)=1$. Define the
actual original inventories
$$
 \mathcal V^{(t)}
 =\{s>1:s\mid N,\quad3^t\chi(s)\in D\},
 \qquad 1\le t\le A.
 \tag{SC144}
$$
Thus $\mathcal V^{(1)}$ is exactly $V_3$ in SC128; the superscript
here denotes original $3$-height. Divisor closure gives
$\mathcal V^{(t+1)}\subseteq\mathcal V^{(t)}$. Every original
$3$-bearing label that is not a pure $3$-power has one and only one
form $3^t\chi(s)$ with $s\in\mathcal V^{(t)}$. Consequently
$$
 N_3=A+\sum_{t=1}^A|\mathcal V^{(t)}|,
 \qquad
 \mathcal P_{d,t}=\mathcal N_d\cap\mathcal V^{(t)}.
 \tag{SC145}
$$
The reserved $A$ labels are $3,3^2,\ldots,3^A$.
SC122 gives $\mathcal P_{d,1}=\mathcal N_d$. More generally,
$3^t\chi(n_d)\in D$ gives $\mathcal P_{d,t}=\mathcal N_d$,
even if the discarded supplier itself has height zero. These are
counts in the original divisor inventory, with no reassignment of
an original phase and no further deletion from $\mathcal F_0$.

### A complete prefix allocation automatically pays every added class

For each supplier, partition its four nonzero first $5$-roots into
a finite complete $5$-adic prefix family, with leaf depths at most
$A$. A leaf at depth $t$ is a residue $u\bmod5^t$ with
$u\not\equiv0\pmod5$. Assign that leaf a slot
$s\in\mathcal P_{d,t}$. Require that all assigned slots at a
fixed depth be numerically distinct across all suppliers; a slot
may recur at different depths.

Add $[0]_5$ and, for each assigned leaf, the CRT class
$[u]_{5^t}\cap[\eta_d]_s$ of modulus $5^t s$.
Every point of every complete $C_d$ either belongs to $[0]_5$ or
to one of its prefix leaves. Since $s\mid n_d$, it satisfies the
corresponding actual-phase congruence. This covers all of $H$ by
SC122, including all integer lifts. All new labels are odd and
$5$-bearing, hence fresh relative to $\mathcal F_0$.
Their $5$-valuations and same-depth slot distinctness make them
pairwise different; the pure label $5$ is separate because $s>1$.

The numerical donor for a leaf $(t,s)$ is $3^t\chi(s)$.
All donors are distinct and none is a reserved pure $3$-power.
If $L_t$ leaves are assigned at depth $t$, SC111 and SC145 give
the exact count
$$
 \begin{aligned}
 c&=1+\sum_{t=1}^A L_t,\\
 K-|\mathcal F_{\rm new}|
  &=A+z-1+\sum_{t=1}^A\bigl(|\mathcal V^{(t)}|-L_t\bigr)
    \ge A+z-1\ge1.
 \end{aligned}
 \tag{SC146}
$$
The prefix allocation is a hypothesis; its payment follows from
the actual inventories. Pure slots $s=3^b$, $b\ge1$, are included:
their donors $3^t5^b$ are not pure $3$-powers. If the complete
supplier family is empty, use $\mathcal F_0$ without any patch.

This applies the existing prefix and demand-copy matching methods
of [report 385, Sections 64 and 69](385-private-congruence-hulls-and-crossed-modulus-closure.md#64-the-common-literal-zero-root-makes-deep-feasibility-a-static-hall-condition)
and its [whole-class construction in Section 200](385-private-congruence-hulls-and-crossed-modulus-closure.md#200-a-vacant-lower-prime-layer-gives-a-whole-cover-descent).
The additional relation is the depth-specific original donor
$3^t\chi(s)$ and its exact decomposition of SC111's budget.

### Height two has an explicit pair of global Hall tests

At $A=2$, choose $k_d\in\{0,1,2,3,4\}$ first roots of each
supplier to defer. It requests $4-k_d$ slots at depth one and
$5k_d$ slots at depth two. Applying the existing finite Hall
theorem to those demand copies separately at each depth gives
exactly
$$
 \begin{aligned}
 \left|\bigcup_{d\in X}\mathcal N_d\right|
   &\ge4|X|-\sum_{d\in X}k_d,\\
 \left|\bigcup_{d\in X}
          (\mathcal N_d\cap\mathcal V^{(2)})\right|
   &\ge5\sum_{d\in X}k_d
       \qquad(X\subseteq\mathcal W_*),\\
 c&=1+4|\mathcal W_*|+4\sum_{d\in\mathcal W_*}k_d.
 \end{aligned}
 \tag{SC147}
$$
These are necessary and sufficient for this independent two-level
prefix allocation, not for every possible repair. SC146 pays it
whenever both global tests hold. In particular, deferring one root
of a depth-two supplier can remove one failed first-level request
if its second-level menu has five slots and all the first-level
inequalities, after that demand reduction, hold. A local deficient
block alone does not establish these tests for the complete family.

### One compatible root can be shared without grouping whole sources

Let $d,e$ be distinct suppliers, and suppose a nonunit slot $s_0$
divides $n_d,n_e$ and $\eta_d-\eta_e$. Use one shared class
$[1]_5\cap[\eta_d]_{s_0}$ for their first root. They each need
three remaining first-level slots; every other supplier needs four.
After reserving $s_0$, the exact remaining matching condition is
$$
 \left|\left(\bigcup_{a\in X}\mathcal N_a\right)
           \setminus\{s_0\}\right|
 \ge4|X|-|X\cap\{d,e\}|
 \qquad(X\subseteq\mathcal W_*).
 \tag{SC148}
$$
The shared $[0]_5$, shared first-root class and all assigned
remaining classes give $c=4|\mathcal W_*|$. There are
$4|\mathcal W_*|-1$ distinct nonpure first-layer donors, so the
same count gives saving at least $A+z-1$. Only one compatible
slot is required; SC131's four-slot whole-group hull is unnecessary.
The source phases and all other retained service stay fixed.

### Two complete outputs of modulus $27p$ admit eight or thirteen classes

Let $p\ge7$ be prime. Suppose two actual suppliers on the fixed
common tree are $C_1=[u]_{27p}$ and $C_2=[v]_{27p}$, their union
contains all of $H$, and $9\cdot5^3p\in D$. The last condition
holds, in particular, for the output pair of originals
$3\cdot5^3p$ and $9\cdot5^3p$. Divisor closure supplies all
seven slots $3,9,27,p,3p,9p,27p$ at each of depths one and two,
and sixteen original $3$-bearing divisors of $9\cdot5^3p$.

If $u\equiv v\pmod p$, share the first root using slot $p$.
On roots $2,3,4$, use slots $3,9,27$ for $C_1$ and
$3p,9p,27p$ for $C_2$. With the shared $[0]_5$, this gives
$$
 \begin{gathered}
 \text{labels }5,\ 5p,\ 15,45,135,\ 15p,45p,135p,\\
 c=8,\qquad K-|\mathcal F_{\rm new}|\ge8+z.
 \end{gathered}
 \tag{SC149}
$$
Every listed nonpure class carries its supplier phase reduced
modulo the assigned slot; the $p$-phase is common. For example,
$v-u=p$ gives a common hull with only one nonunit divisor, so
SC131 does not apply but this root-local sharing does.

There is also a complete repair for arbitrary $u,v$. Assign the
following slots, again always using the named supplier's actual
phase modulo the slot:

| Supplier | Residues at the new $5$-boundary | Slots in the same order |
| --- | --- | --- |
| $C_1$ | $1,2,3,4\pmod5$ | $3,9,27,p$ |
| $C_2$ | $1,2,3\pmod5$ | $3p,9p,27p$ |
| $C_2$ | $4,9,14,19,24\pmod{25}$ | $3,9,27,p,3p$ |

Together with $[0]_5$, the numerical labels and count are
$$
 \begin{gathered}
 5;\quad15,45,135,5p,15p,45p,135p;
 \quad75,225,675,25p,75p,\\
 c=13,\qquad K-|\mathcal F_{\rm new}|\ge3+z.
 \end{gathered}
 \tag{SC150}
$$
The last row partitions precisely the unserved fourth root of
$C_2$. The twelve nonpure donors are distinct original divisors
of $9\cdot5^3p$. Thus this repairs both complete APs at every
integer lift even when their common hull is the unit. The
seven-slot failure of SC124 for this pair does not obstruct a
paid two-level repair. For a pair inside a larger supplier family,
these local assignments still require a globally compatible
allocation; the hypothesis that this pair covers all $H$ cannot
be dropped merely because its own repair is paid.

### Thirteen is optimal only within the stated common-divisor palette

Let two complete APs have common odd $5$-free modulus $n>1$ and
$\gcd(n,u-v)=1$. Restrict repairs to exactly one shared pure
class $[0]_5$ and distinct labels $5^t s$, where $t\ge1$,
$s>1$, and $s\mid n$. Write $J=\tau(n)-1$.
A nonpure class can meet only one of the two APs: meeting both
would force $s\mid u-v$. On the AP it meets, its relative
mass is $5^{-t}$. Summing the two normalized AP masses therefore
gives the strict finite-family bound
$$
 2\le\frac25+\sum_{\text{used }(t,s)}5^{-t}
       <\frac25+\frac J4,
 \qquad\text{hence }J\ge7.
 \tag{SC151}
$$
For $J=7$, at most seven of the eight source/nonzero-root pairs
can receive a depth-one class. If $m\le7$ pairs receive such
service, each remaining pair requires at least five classes of
depth at least two, since each covers at most one fifth of that
root's relative mass. Thus the total number of classes is at least
$1+m+5(8-m)\ge13$. For $n=27p$, SC150 attains it.

This optimum concerns the complete two-AP service and the specified
palette. It allows arbitrary phases and arbitrary finite $5$-depth
inside that palette, but no extra pure $5$-powers or shadow labels
outside the nonunit divisors of $n$. It gives no lower bound for a
smaller actual $H$ or for unrestricted repairs. The five-slot pair
$n=9p$ still fails this palette at every finite $5$-depth, whereas
the seven-slot pair $n=27p$ has the explicit repair above.

SC144--SC150 provide further paid sufficient conditions. They do
not show that some common tree, representative choice and complete
supplier family must satisfy one of the global allocations.
Total donor inventory does not guarantee availability in each
$\mathcal P_{d,t}$, and separate favorable choices cannot be
combined into a different source. These are ordinary mathematical
deductions using the cited matching, prefix and divisor methods;
they are not Lean verification or an unrestricted resolution of
Erdős #7.

## 37. A nonunit common hull pays two equal-cofactor sources at output height two

Keep the actual retained family $\mathcal F_0$ and its complete
integer hole $H$, with $|\mathcal F_0|=K-N_3-z$ and $z\ge0$.
Every retained numerical modulus is $5$-free. Let $m>1$ be odd
and coprime to $15$. Suppose two complete output enclosures satisfy
$$
 C_1=[u]_{9m},\qquad C_2=[v]_{9m},\qquad
 H\subseteq C_1\cup C_2,\qquad \gcd(9m,u-v)>1.
 \tag{SC152}
$$
Then sixteen distinct fresh $5$-bearing classes cover this entire
union. Under the existing $N_3\ge22$ bound they give strict descent.
The containment is for all of $H$, with the actual source phases;
it is not a claim about two chosen private points or only omitted
top service.

If $u\equiv v\pmod{3m}$, both classes already lie in one complete
$3m$ enclosure, and SC134 with $t=1$ gives eleven classes. For
prime $m$, SC137 gives its exact complete-enclosure minimum. The
consumer below covers the remaining nonunit-hull pairs. Distinct
cofactors in a common first ternary root are already handled by
SC134 with $t=2$; they are not treated as a new packet here.

### A common first ternary root has an explicit sixteen-class repair

First assume $u\equiv v\pmod3$. Write $\alpha$ for their common
residue modulo $3$, $\rho_i$ for their respective residues modulo
$9$, and $r_i$ for their respective residues modulo $m$. Choose
$0\le\beta<9$ representing $\rho_2$. Add the CRT classes in
the following table. A condition marked none is unrestricted.

| Numerical label | $5$-condition | $3$-condition | $m$-condition |
| --- | --- | --- | --- |
| $5$ | $0\pmod5$ | none | none |
| $15$ | $3\pmod5$ | $\alpha\pmod3$ | none |
| $5m$ | $2\pmod5$ | none | $r_1\pmod m$ |
| $45$ | $2\pmod5$ | $\rho_2\pmod9$ | none |
| $15m$ | $4\pmod5$ | $\alpha\pmod3$ | $r_2\pmod m$ |
| $45m$ | $4\pmod5$ | $\rho_1\pmod9$ | $r_1\pmod m$ |
| $25$ | $1\pmod{25}$ | none | none |
| $75$ | $11\pmod{25}$ | $\alpha\pmod3$ | none |
| $25m$ | $6\pmod{25}$ | none | $r_1\pmod m$ |
| $225$ | $16\pmod{25}$ | $\rho_1\pmod9$ | none |
| $225m$ | $21\pmod{25}$ | $\rho_1\pmod9$ | $r_1\pmod m$ |
| $75m$ | $21\pmod{25}$ | $\alpha\pmod3$ | $r_2\pmod m$ |
| $135$ | $1\pmod5$ | $\beta+9\pmod{27}$ | none |
| $135m$ | $1\pmod5$ | $\beta+18\pmod{27}$ | $r_2\pmod m$ |
| $675$ | $6\pmod{25}$ | $\beta\pmod{27}$ | none |
| $675m$ | $16\pmod{25}$ | $\beta\pmod{27}$ | $r_2\pmod m$ |

First roots $0$ and $3$ modulo $5$ are paid on both sources by
labels $5$ and $15$. On root $2$, labels $5m$ and $45$ pay
$C_1$ and $C_2$ respectively. On root $4$, labels $45m$ and
$15m$ do the same. Only root $1\pmod5$ remains.

For $C_1$ in that root, its five residues $1,6,11,16,21$ modulo
$25$ are paid respectively by $25,25m,75,225,225m$. For $C_2$,
residues $1,11,21$ are paid by $25,75,75m$. At its remaining
residues $6,16$, split its complete ternary prefix $\rho_2$ into
the three children $\beta,\beta+9,\beta+18\pmod{27}$.
Labels $135,135m$ pay the latter two children throughout root
$1\pmod5$. At child $\beta$, labels $675,675m$ pay residues
$6,16\pmod{25}$ respectively. Thus every point of both complete
APs is covered, including all higher-digit lifts.

The numerical label set is exactly
$$
 \{5,25\}\cdot\{1,3,9,27\}\cdot\{1,m\}.
 \tag{SC153}
$$
Its sixteen labels are distinct because $m>1$ and $(m,15)=1$;
they are odd nonunits because $m$ is odd. They all contain $5$,
so none collides with $\mathcal F_0$. Their phases exist by CRT.
The common comparison period may be enlarged to
$\operatorname{lcm}(N,675m)$. This adds a third output ternary
digit even when the old output height was two; it does not require
an original label of $5$-height three or an extra original donor.

### A common cofactor phase uses the same numerical labels

Alternatively assume $u\equiv v\pmod m$, with no requirement
on their ternary roots. Let $r$ be that common phase and put
$\alpha_i=\rho_i\bmod3$. Replace four rows in the preceding
table as follows:

| Old label and role | Replacement label | $5$-condition | $3$-condition | $m$-condition |
| --- | --- | --- | --- | --- |
| $15$, shared root $3$ | $5m$ | $3\pmod5$ | none | $r\pmod m$ |
| $5m$, source $1$ root $2$ | $15$ | $2\pmod5$ | $\alpha_1\pmod3$ | none |
| $75$, shared residue $11$ | $25m$ | $11\pmod{25}$ | none | $r\pmod m$ |
| $25m$, source $1$ residue $6$ | $75$ | $6\pmod{25}$ | $\alpha_1\pmod3$ | none |

In the unchanged $15m$ and $75m$ rows use $\alpha_2$ as their
ternary phase. Every $m$-bearing row now uses $r$. The other
source-specific phases and the three children of $\rho_2$ stay
as displayed.

The shared root $3$ and shared residue $11$ now use the common
$m$-phase. In root $1\pmod5$, source $1$ is paid on residues
$1,6,11,16,21\pmod{25}$ by $25,75,25m,225,225m$.
Source $2$ is paid on $1,11,21$ by $25,25m,75m$, and its
remaining $6,16$ residues have exactly the same three-child
coverage as before. Roots $0,2,4$ are also covered by their
displayed rows. Thus the same sixteen distinct labels cover the
complete union without a common ternary root.

### A proper common divisor suffices, and the original inventory pays

Under SC152, if $3\mid u-v$, use the first table at $m$.
Otherwise take $h=\gcd(m,u-v)>1$, enclose both original classes
in their actual reductions modulo $9h$, and use the second table
at $h$. The enlarged union still contains every point of $H$,
and $h$ is odd and coprime to $15$. This proves the stated
nonunit-hull case also for composite $m$.

No retained class is deleted or changed. Therefore
$$
 c=16,\qquad K-|\mathcal F_{\rm new}|=N_3+z-16,
 \qquad N_3+z\ge17\ \Longrightarrow\ |\mathcal F_{\rm new}|<K.
 \tag{SC154}
$$
NF67 and the existing seven-support-prime exclusion, already
applied in SC135, give $N_3\ge22$ and saving at least $6+z$.
This pays from the whole original inventory in SC111, not from
a new divisor assignment for each shadow label. Actual suppliers
of moduli $3^{b_i}m$ with $b_i\ge2$ may be enclosed in their
actual reductions modulo $9m$ before this argument, provided
SC152's full-hole containment and nonunit hull are established.

The upper bound sixteen is not asserted to be optimal. Within
the two equal-cofactor enclosures of SC152, the remaining case
has unit common hull. This does not force an arbitrary whole
cover to have only two suppliers or a nonunit hull, and it does
not make several separately paid packets numerically compatible.
The construction is a specific consumer of the complete CRT and
prefix splits in Sections 12 and 26; it asserts no new general
covering theorem, Lean verification or unrestricted resolution
of Erdős #7.

## 38. Two complete actual sources do not force the height-two prefix allocation

Consider the following finite original family:
$$
 A=2,\qquad B=3,\qquad M=7,\qquad
 D=\{d>1:d\mid7875\},\qquad |D|=23.
 \tag{SC155}
$$
The notation $a(d)$ denotes the original AP $[a]_d$. Each table
cell gives its class followed by an actual private point. The two
pure ternary classes are $1(3)$ with private point $4$, and
$0(9)$ with private point $9$; the remaining classes are:

| $b$ | $5^b$ column | $3\cdot5^b$ column | $9\cdot5^b$ column |
| --- | --- | --- | --- |
| 1 | $1(5);\ 6$ | $12(15);\ 12$ | $29(45);\ 29$ |
| 2 | $5(25);\ 5$ | $60(75);\ 60$ | $128(225);\ 128$ |
| 3 | $25(125);\ 650$ | $300(375);\ 2175$ | $2(1125);\ 2$ |

| $b$ | $5^b7$ column | $3\cdot5^b7$ column | $9\cdot5^b7$ column |
| --- | --- | --- | --- |
| 0 | $0(7);\ 14$ | $15(21);\ 15$ | $23(63);\ 23$ |
| 1 | $30(35);\ 65$ | $45(105);\ 465$ | $185(315);\ 185$ |
| 2 | $150(175);\ 1550$ | $375(525);\ 1950$ | $300(1575);\ 1875$ |
| 3 | $375(875);\ 1250$ | $1125(2625);\ 3750$ | $7125(7875);\ 7125$ |

For every comparable pair $d\mid e$, the displayed phases disagree
modulo $d$. Every listed private point $x_d$ satisfies
$x_d\equiv\alpha_d\pmod d$ and
$x_d\not\equiv\alpha_e\pmod e$ for all $e\ne d$.
Thus the family is irredundant as a representation of its union.
It is a **noncover**: 1910 residues remain uncovered.
In particular $125$ is uncovered and lies in $2\pmod3$, with
$125\equiv8\pmod9$. Irredundancy here does not mean minimality
among whole covering systems.

### The same actual tree gives two complete source covers

Use the ternary-to-quinary digit inclusion
$$
 \theta_3(z)=z_0+5z_1+25z_2,
 \qquad z=z_0+3z_1+9z_2,\quad z_i\in\{0,1,2\},
$$
and the two actual source maps
$$
 F_u(z)\equiv u\pmod9,\qquad
 F_u(z)\equiv\theta_3(z\bmod27)\pmod{125},\qquad
 F_u(z)\equiv z\pmod7,
 \qquad u\in\{3,6\}.
 \tag{SC156}
$$
These are precisely the two safe terminal siblings of the original
pure $9$ class $0(9)$; the pure $3$ class is $1(3)$.

The common lower family consists of the six pure-cofactor outputs
$$
 1(3),2(3),\quad3(9),6(9),\quad9(27),18(27).
$$
They cover exactly the complement of $0(27)$. The eight remaining
lower outputs have ternary phase zero and the following $7$-phases,
listed for $b=0,1,2,3$:
$$
 a=0:\ (0,2,3,4),\qquad a=1:\ (1,3,4,5).
$$
On $0(27)$ these cover exactly the $7$-phases $0,1,2,3,4,5$.
Consequently the complete shared lower complement is
$$
 E=[27]_{189},\qquad
 C_{1575}=[27]_{63},\qquad C_{7875}=[27]_{189}.
 \tag{SC157}
$$
The $u=3$ source has the surviving top $300(1575)$, whose output
is $[27]_{63}$. The $u=6$ source has the surviving top
$7125(7875)$, whose output is $[27]_{189}$. Each contains $E$.
Thus SC15 holds with nonempty $E$, and both actual source families
cover all 189 source residues and all their integer lifts.

### Complete suppliers exist, but SC147 fails for every retained choice

The two flat lower outputs, from originals $7$ and $21$, have
private traces $[0]_{189}$ and $[162]_{189}$ relative to the
entire pooled source family. Each trace lies in the ternary root
zero. There are two lower outputs in each of the seven slots
$3,9,27,7,21,63,189$. Retaining one at each slot other than $3$
and buying $S$ gives $2^6\cdot3=192$ choices.

At least one of the output-$3$ lower sources is necessary in any
complete supplier family for every one of these choices, even if
the suppliers may use both top colors. The following two source
points are private relative to the entire pooled output family:

| Original | Complete output | Private source point | Its $3,7$ coordinates |
| --- | --- | --- | --- |
| $5$ | $[1]_3$ | $13$ | $(1,6)$ |
| $15$ | $[2]_3$ | $20$ | $(2,6)$ |

All other pure lower outputs and both tops have ternary root zero.
The flat lower outputs have $7$-phases zero and one; all remaining
lower outputs also have ternary root zero. Thus the table directly
certifies privacy. Slot $3$ is absent from the retained lower
family, and a single bought root can absorb at most one of the
two private points. The other stays in $H$ and forces its unique
source into every complete supplier family. Its singleton menu is
$\{3\}$ at both donor depths, whereas SC147 requires
$$
 4-k_d\le1,\qquad5k_d\le1,\qquad
 k_d\in\{0,1,2,3,4\},
 \tag{SC158}
$$
which is impossible. This proves the failure for all retained choices
without an enumeration of their combinations.

For $S=[1]_3$ or $[2]_3$, whichever of
the flat $7$-column lower sources is discarded also retains a
private trace in the hole and is necessary. These are 128 of the
192 choices. For $S=[0]_3$, those two particular flat traces are
absorbed, but the output-$3$ obstruction remains.

All surviving tops occupy slots already held by lower representatives.
Thus $|\mathcal F_0|=7$, $N_3=16$, $n_0=7$ and $z=0$, exactly
as in SC111. The discarded lower sources and either safe top color
do form a complete qualified supplier family as in SC122. The
failure is specific to forcing SC147 on this fixed common tree;
it does not exclude another repair or another tree.

### The total inventory and support can grow arbitrarily

For any finite set of new primes $q>7$, add exactly three labels
per prime, with phases specified by
$$
 [0]_q,\qquad [2]_3\cap[1]_q,\qquad [8]_9\cap[2]_q.
 \tag{SC159}
$$
Their moduli are $q,3q,9q$. The enlarged label set remains
divisor-closed. Within a new column the distinct $q$-phases give
comparable disjointness; the only old comparable labels are $3$
and $9$, whose phases disagree with these new classes. Distinct
new prime columns have no other comparability.

In both selected source maps, the new $3q$ and $9q$ classes vanish
because the old ternary coordinate has first digit zero. The new
$q$ class is a unique lower representative and is retained. Both
complete source covers therefore persist. CRT lifts of old private
points and of the old uncovered point $125$ with every new
$q$-coordinate equal to $3$ avoid all added classes. For a new
class at one prime $q$, lift the old hole $125$ with that coordinate
equal to $0$, $1$ or $2$ respectively, and every other new prime
coordinate equal to $3$. These are private points of the three
new classes, because $125\equiv8\pmod9$.

Thus the enlarged family remains globally irredundant and a
noncover. The old source-private lower traces persist with all new
coordinates equal to $3$, so the same failure of SC147 remains.
With $r$ added primes, the exact counts are
$$
 K=23+3r,\qquad N_3=16+2r,\qquad n_0=7+r,\qquad z=0.
 \tag{SC160}
$$
Both inventory and support grow without bound. The extra donor slots do not
belong to the necessary old source's menu $\{3\}$.

The inventory can also grow while fixing the support. For each new prime
$q$, choose a finite height $T_q\ge1$. For $1\le t\le T_q$ set
$$
 \alpha_{a,t}=3\sum_{i=0}^{t-2}q^i+a q^{t-1},\qquad a=0,1,2,
$$
where the sum is empty at $t=1$. At level $t$ add
$[\alpha_{0,t}]_{q^t}$,
$[2]_3\cap[\alpha_{1,t}]_{q^t}$ and
$[8]_9\cap[\alpha_{2,t}]_{q^t}$.
All earlier $q$-digits are $3$ and the last digit is $a$.
Two different depths disagree at the earlier leaf digit, and the
three classes at one depth have different last digits. Including
every depth up to $T_q$ preserves divisor closure. All old private
points and the old hole lift with every new $q$-digit equal to $3$.
A new private point uses the old hole $125$, its specified leaf,
and all other new digits $3$. This proves the same privacy and
noncoverage conclusions as above.

On the two selected safe sources, only the $q^t$ classes survive;
each has its own unique retained lower slot. The source-private
points forcing the old menu $\{3\}$ persist on the all-$3$ new
coordinates. Writing $R=\sum_q T_q$, the counts become
$$
 K=23+3R,\qquad N_3=16+2R,\qquad n_0=7+R,\qquad z=0.
$$
For example take the eight new primes
$11,13,17,19,23,29,31,37$, with $T_{11}=6$ and all other
$T_q=1$. Then $R=13$, $K=62$, $N_3=42$, the largest support
prime is $P=37$, and the support size is $s=11$. This particular
noncover meets the numerical bounds NF67, $N_3\ge36$, and NF82,
$N_3\ge41$. It also meets the coarse range, support, forced-label
and height conditions displayed in GHA10--GHA11: the highest
nonternary exponent is $H_{11}=6\le12$, and every required
$3q^{H_q}$ is present. None of these scalar or coarse label
conditions removes its fixed-source allocation obstruction.

This does not assert every necessary EB1 condition. In the same
example, relative to $p=37,q=3$, NF66 has $h_0=20,h_1=2$,
so both alternatives $h_0\ge36$ and $h_0+h_1\ge37$ fail.
The example therefore leaves the stronger whole-cover column
constraints available; it does not refute them.

This construction separates SC15, SC111, SC122, actual common-source
geometry, divisor closure, comparable disjointness and global
irredundancy from the full original-cover hypothesis. It does not
satisfy global EB1 and does not establish an obstruction to an
unrestricted paid repair. The missing forcing argument must use
more than these fixed-source conditions and a total inventory bound.

The [finite checker](../../../frontier/source-budgets/a2_two_complete_sources.py)
constructs the original phases, verifies divisor closure, comparable
disjointness, private points, both complete pullbacks, and all 192
representative/root choices. Its [exact result](../../../frontier/source-budgets/a2_two_complete_sources.json)
records the counts used above. The unbounded prime extension is
the displayed CRT argument, not an enlarged-period enumeration.
These are ordinary mathematical deductions and finite checks, not
Lean verification.

## 39. Three coprime active columns admit a complete paid repair at original height two

Keep one actual common tree, the retained family $\mathcal F_0$,
its bought root $S=[j]_3$, and the whole hole $H$ of SC111.
Assume $A=2$ and choose exactly one actual lower representative
at each surviving numerical slot other than $3$, as in SC122.
Call an omitted top or discarded lower active if
its actual output AP intersects $H$. Suppose every active output
has one of the numerical labels
$$
 n_i=3^{b_i}m_i,\qquad 1\le i\le k\le3,\qquad
 b_i\ge2,\quad m_i>1,\quad m_i\mid M,\quad
 \gcd(m_i,m_j)=1\ (i\ne j).
 \tag{SC161}
$$
Each listed slot has an active supplier; unused slots are removed.
There is only one listed output height per cofactor. In particular,
all $m_i$ are odd and coprime to $15$. This condition concerns all
active discarded lower service as well as both omitted top colors.
It makes no claim that an arbitrary minimal cover admits this
profile.

Under SC161 there is a family of distinct fresh odd $5$-bearing
classes covering all $H$, of size at most $N_3-1$. Thus an EB1
whole cover cannot have this profile for any such fixed choice.
The construction below uses cross-color intersections to reduce
what must be repaired; it does not assume the independent allocation
SC147.

### Actual intersections, rather than both full top unions, suffice

Let $U$ be the union of the active discarded lowers, and let
$B_c$ be the union of the active omitted tops of color $c$.
The already established full-service decomposition SC112 gives
$$
 H\subseteq U\cup(B_1\cap B_2).
 \tag{SC162}
$$
Indeed, a point of $H$ belonging to a lower output must belong
to a discarded one. Every other point has an actual top owner
in each color by SC15. Neither owner can be retained, because
the point lies in $H$. This argument includes the discarded lower
liability; it does not replace $H$ by the top-only complement.

A fixed output slot has at most two lower originals, at heights
$a=0,1$. Keeping one representative leaves at most one discarded
lower there. It has at most one top original, at height $a=2$,
which belongs to at most one color. Hence, writing $\ell$ for the
number of active lowers and $t$ for the number of active tops,
$$
 \ell\le k,\qquad t\le k.
 \tag{SC163}
$$
Every active slot has the original qualification
$3\cdot5^{b_i}m_i\in D$: for a discarded $a=0$ supplier use
its retained positive-height peer as in Section 32, and for an
$a=1$ supplier or top use its own divisor. Divisor closure gives
three different labels $3m_i,15m_i,75m_i$ per column, as well as
$3,15,75$ and the original pure label $9$. Therefore
$$
 N_3\ge3k+4.
 \tag{SC164}
$$
If $t\ge1$, each top additionally supplies $9m_i,45m_i,225m_i$
in its own column, and any one top supplies the two remaining
unit-column labels $45,225$. Thus
$$
 N_3\ge3k+3t+6\qquad(t\ge1).
 \tag{SC165}
$$
All labels counted here are original and distinct. No original
product column $m_im_j$ is assumed.

### Three root classes per nonunit cofactor

Enclose each active lower in its actual reduction
$L_i^*=[\alpha_i]_{9m_i}$. It stays in an unbought ternary root,
since its original output intersects $H$ and $b_i\ge2$.
Among the at most three lowers, choose a largest group $G$ sharing
one ternary root $g$. If there are no lowers, take $G$ empty and
omit every class whose phase uses $g$. Otherwise
$$
 \ell-|G|\le1.
 \tag{SC166}
$$
For any enclosure $[a]_{9h}$ used below, with odd $h>1$ and
$(h,15)=1$, cover its new $5$-roots $2,3,4$ by the three classes
$$
 [2]_5\cap[a]_h,\qquad
 [3]_5\cap[a]_{3h},\qquad
 [4]_5\cap[a]_{9h}.
 \tag{SC167}
$$
Their numerical labels are $5h,15h,45h$. Buy the single shared
class $[0]_5$ as well. Only root $1\pmod5$ then remains on each
enclosure. All phases in this construction are actual reductions
or CRT combinations of the displayed source phases.

If either active top color is empty, SC162 says the lower
enclosures cover $H$. Cover root $1$ of the group $G$ by
$[1]_5\cap[g]_3$, of label $15$. If the one possible leftover
lower exists, cover its root $1$ by
$[1]_5\cap[\alpha_i]_9$, of label $45$. The cost is at most
$1+3\ell+2\le3k+3<N_3$ by SC164. If there are no lowers either,
$H$ is empty and no patch is needed. The same lower-only repair
applies whenever $B_1\cap B_2$ is empty.

### Two top colors force a shared intersection phase

Now assume both colors are present and have a nonempty intersection.
Form the bipartite graph of active tops, with an edge for every
nonempty actual intersection across the colors. It has
$2\le t\le3$ vertices, so all its edges share a vertex and
$$
 1\le e\le t-1\le2.
 \tag{SC168}
$$
For an edge between distinct slots $i,j$, the true intersection
has modulus $3^{\max(b_i,b_j)}m_im_j$. Enclose it in its actual
reduction $I_{ij}^*=[\gamma_{ij}]_{9m_im_j}$.
Every edge shares one top vertex, whose output fixes a residue
modulo $9$. Consequently all $\gamma_{ij}$ have the same residue
$\gamma\pmod9$. SC162 yields
$$
 H\subseteq\bigcup L_i^*\ \cup\!\bigcup I_{ij}^*.
 \tag{SC169}
$$
Apply SC167 both to each lower enclosure and to each edge enclosure,
using respectively $h=m_i$ and $h=m_im_j$. On root $1\pmod5$,
use $[1]_5\cap[g]_3$ for $G$ and
$[1]_5\cap[\gamma]_9$ for every edge enclosure. These are the
pure labels $15$ and $45$.

There is at most one leftover lower $L_j^*$. For that lower,
partition root $1$ into its five children modulo $25$. Enumerate
$s_u$, $0\le u\le4$, as the five distinct divisors
$3,9,m_j,3m_j,9m_j$ of $9m_j$, and add
$$
 [1+5u]_{25}\cap[\alpha_j]_{s_u}\qquad(0\le u\le4).
 \tag{SC170}
$$
Every point of $L_j^*$ in root $1$ lies in one of these children
and satisfies its divisor condition. These five numerical labels
are $75,225,25m_j,75m_j,225m_j$.

### Global distinctness and payment

At $5$-depth one the cofactor parts are $1$, the singletons $m_i$,
and the edge products $m_im_j$. Pairwise coprimality and $m_i>1$
make all distinct subsets in this list have different products.
The $3$-powers distinguish the three rows for each cofactor.
The shared labels $5,15,45$ are also distinct. The five possible
extra labels in SC170 have $5$-depth two, so are fresh relative
to all those labels and distinct from each other.

Every new modulus is odd, greater than one and divisible by $5$;
none collides with the unchanged $5$-free $\mathcal F_0$.
SC169 and the exhaustive $5$-digit partitions cover all of $H$
at every integer lift. No old class is deleted to pay for this
repair. Its cost satisfies
$$
 \begin{aligned}
 c&\le1+3\ell+3e+2+5\\
  &\le3k+3t+5<N_3,\\
 |\mathcal F_0\cup\mathcal P|
  &=K-N_3-z+c\le K-z-1<K.
 \end{aligned}
 \tag{SC171}
$$
The second inequality uses SC168 and SC165. Omitting unused shared
or leftover classes only lowers the cost. The product-cofactor
labels require no invented donor columns: their payment is this
whole original-count comparison, not a separate donor assignment.

The conservative bounds for $(k,t)=(2,2),(3,2),(3,3)$ are
respectively $c\le17,20,23$ against $N_3\ge18,21,24$.
No external support-size lower bound is needed here. This removes
a residual branch with both unbought ternary roots and arbitrary
actual cofactor phases, using SC112's two-color service rather
than repairing both top unions in full.

For four active columns the two combinatorial savings used above
need not hold: two lowers may lie outside the largest root group,
and the top graph may be a $K_{2,2}$ or have separated components
with different modulo-$9$ phases. Other unhandled profiles include
$b=0,1$, unit or overlapping cofactors, multiple active heights
in one cofactor, and $A>2$ with several discarded lowers at a slot.
No assertion forces the general problem into SC161. This is an
ordinary constructive deduction using the existing CRT, prefix
and source-service primitives, not Lean verification or an
unrestricted resolution of Erdős #7.

## 40. Four coprime active columns admit a complete paid repair

Use the complete-hole setup of Section 39, with original ternary
height $A=2$, exactly one retained lower representative at every
surviving slot other than $3$, and exactly four active output slots

$$
n_i=3^{b_i}m_i,\qquad 1\le i\le4,\qquad b_i\ge2,\qquad m_i>1,\quad m_i\mid M,
\qquad (m_i,m_j)=1\quad(i\ne j).
$$

There is only one active height per cofactor. Keep the same actual
retained family, bought root, common source tree, and all discarded
lower service. Let $\ell\le4$ be the number of active discarded
lowers and $t\le4$ the number of active tops. Let $G$ be the
bipartite graph of actual nonempty cross-color top intersections;
write $e=|E(G)|$. Isolated active tops are still counted in $t$
and in the original inventory.

The existing complete-service statement gives

$$
H\subseteq\bigcup L_i^*\ \cup\!\bigcup_{ij\in E(G)}I_{ij}^*,
\qquad
L_i^*=[\alpha_i]_{9m_i},\qquad
I_{ij}^*=[\gamma_{ij}]_{9m_im_j}.
\tag{SC172}
$$

These are reductions of actual lower classes and actual top
intersections. All enclosures lie in the two unbought ternary roots.
The cofactor labels occurring here are globally different: distinct
singleton and edge subsets of the four pairwise coprime nonunits have
different products. Reuse the three rows SC167 for every enclosure
and add $[0]_5$. This costs $1+3\ell+3e$ and leaves only the
new root $[1]_5$ of (SC172) to cover.

### Count the second original ternary layer outside the largest prime

Let $P$ be the largest original support prime. The existing
seven-support-prime exclusion gives $P\ge23$. In the same original
inventory put

$$
c_h=\#\{d\in D:P\nmid d,\ v_3(d)=h\}\quad(h=1,2),
\qquad t_P=\#\{d\in D:3P\mid d\}.
$$

Since $A=2$, these are disjoint and exhaustive for the
3-bearing original labels: $N_3=c_1+c_2+t_P$.
Reuse [Report 385 NF66](385-private-congruence-hulls-and-crossed-modulus-closure.md#56-the-original-cover-needs-enough-small-prime-labels-to-block-compression) at $(p,q)=(P,3)$: its two alternatives are
$c_1\ge P-1$ or $c_1+t_P\ge P$. In either case

$$
N_3\ge P-1+c_2.
\tag{SC173}
$$

If $t\ge1$, each active top supplies its actual original label
$9\cdot5^{b_i}m_i$, with $b_i\ge2$. Divisor closure supplies
the pure labels $9,45,225$. It also supplies
$9m_i,45m_i,225m_i$ for each top column. Because the $m_i$
are pairwise coprime, at most one contains $P$. Thus at least
$t-1$ of these nonunit columns are P-free. Their three labels
and the three unit-column labels are all distinct and have exact
original ternary height two. Therefore

$$
c_2\ge3+3(t-1)=3t,\qquad
N_3\ge22+3t\quad(t\ge1).
\tag{SC174}
$$

For $t=0$, SC173 still gives $N_3\ge22$. These bounds count
one actual original inventory. They neither sum different
prime-by-prime optima nor subtract any retained class.

### A shared completion for at most two residual enclosures

Suppose at most two still-unpaid enclosures are
$[\delta_a]_{9h_a}$, with distinct $h_a>1$, all in a common
ternary root $r$. Add

$$
[1]_{25},\qquad [6]_{25}\cap[r]_3,
$$

and, for each residual enclosure, add

$$
[11]_{25}\cap[\delta_a]_{h_a},\qquad
[16]_{25}\cap[\delta_a]_{3h_a},\qquad
[21]_{25}\cap[\delta_a]_{9h_a}.
\tag{SC175}
$$

The five children of $[1]_5$ are exhausted. For $r_0\in\{1,2\}$
residual enclosures the cost is $2+3r_0$, hence at most eight.
For no residual enclosure add nothing. The numerical labels are
$25,75$ and $25h_a,75h_a,225h_a$; they are distinct and have
5-adic depth two, disjoint from all SC167 labels and from the pure
labels $5,15,45$. This is a direct shared application of the
existing complete-prefix construction, not a new general theorem.

### Connected nonisolated top graph, including K2,2

Along an edge, its two actual top phases agree modulo 9. If all
nonisolated top vertices belong to one connected component, every
edge enclosure therefore has one common modulo-9 phase $\gamma$.
Let $R=\gamma\bmod3$, and let $R'$ be the other unbought root.
Let $a$ and $b$ count the lower enclosures in $R$ and $R'$,
respectively, so $a+b=\ell\le4$.

There are two legal ways to use the available pure labels 15 and 45
on the remaining root $[1]_5$:

* Use $[1]_5\cap[R]_3$, covering every edge and all $a$ lower
  enclosures in $R$. If $b>0$, use the pure label 45 for one
  lower enclosure in $R'$. At most $\max(b-1,0)$ lower
  enclosures remain. If $b=0$, nothing remains.
* Use $[1]_5\cap[R']_3$, covering the $b$ lower enclosures,
  and $[1]_5\cap[\gamma]_9$, covering every edge. At most
  $a$ lower enclosures remain in $R$.

If $b>0$, then

$$
\min(b-1,a)\le1\qquad(a+b\le4).
\tag{SC176}
$$

Thus at most one residual lower needs SC175, at cost five. The complete
repair has

$$
c\le1+3\ell+3e+2+5\le20+3e.
\tag{SC177}
$$

With at most four top vertices, a bipartite graph has $e\le t$.
The only cyclic possibility is the complete $K_{2,2}$, where
$e=t=4$. SC174 now gives

$$
c\le20+3e\le20+3t\le N_3-2.
\tag{SC178}
$$

This includes the four-edge K2,2 case, where $c\le32$ and
$N_3\ge34$, as well as three-edge stars or paths, smaller
connected components, and any isolated top vertices.

### Two nontrivial components

With at most four vertices, two nontrivial components consist of two
disjoint edges. Consequently $t=4$, $e=2$, and $N_3\ge34$.
The two edge enclosures may have different modulo-9 phases.

If their first ternary roots differ, use the pure label 15 for the
root containing at least half the lower enclosures. It covers that
root's edge and lowers. Use the pure label 45 for the other edge.
At most two lower enclosures remain, all in the other ternary root.

If the two edges share a ternary root $R$, let $a$ and $b$
again count the lowers in $R$ and its other unbought root.
Using label 15 for $R$, then label 45 for one opposite-root
lower, leaves at most $\max(b-1,0)$ enclosures; when $b=0$
it leaves none. Alternatively, label 15 covers all $b$ opposite
lowers and label 45 covers one edge, leaving at most $a+1$
enclosures, all in $R$. For $b>0$,

$$
\min(b-1,a+1)\le2\qquad(a+b\le4).
\tag{SC179}
$$

Thus in either case SC175 pays the residual at cost at most eight.
The globally distinct repair satisfies

$$
c\le1+3\ell+3e+2+8\le29<N_3.
\tag{SC180}
$$

No equality of the two components' reference phases was assumed.

### No actual cross-color intersection

Then SC172 contains only lowers. If there are no lowers, the hole is
empty and no patch is required. Otherwise choose a largest ternary-root group
for pure label 15, and use pure label 45 for one lower outside it,
if any. At most one lower remains, because $\ell\le4$. The same
completion gives $c\le20$. SC173 gives $N_3\ge22$, including
when no active top exists. The no-top case does not follow just from
the weaker local inventory bound $N_3\ge16$; its stated payment
uses the existing global bound.

### Complete payment and remaining scope

All constructed moduli are odd, distinct, and contain 5. The original
retained family is 5-free and unchanged. Each construction covers
the full right side of SC172 and therefore the whole integer hole and
all lifts. It follows that

$$
|\mathcal F_0\cup\mathcal P|=K-N_3-z+c<K.
\tag{SC181}
$$

Thus the entire four-column profile is excluded for an EB1 whole
cover under the existing support-prime bound. Together with Section
39, this covers at most four active pairwise coprime nonunit
cofactors, one active output height per cofactor, and all those
heights at least two. It does not force an arbitrary whole cover
to have this profile. Cases with five or more active columns,
overlapping or unit cofactors, output heights zero or one, multiple
active heights per cofactor, and original ternary height greater
than two remain outside this construction. All arguments here are
ordinary constructive mathematics reusing NF66, prefix splitting
and complete source service; no new Lean verification or finite
enumeration is claimed.

## 41. Four safe menus pay every qualified single-height cofactor column

The full original cover supplies more actual menus than the two
selected terminal siblings. This section uses four of them to pay
a complete repair with no bound on the number of cofactor columns.
The hypotheses concern the actual active sources in those menus;
they are not asserted to hold for every EB1 family.

### Fixed source and complete liability

Set original ternary height $A=2$. Normalize the original pure classes
to $1\pmod3$ and $0\pmod9$. Fix one common substitution tree $\theta$.
Choose height-zero originals as lower representatives wherever they
survive, and absorb the original $5$ output in the bought root $S$
when necessary. Thus the complete hole $H$ of the actual retained
family $\mathcal F_0$ avoids every height-zero output. Keep the exact
original inventory identity

$$
|\mathcal F_0|=K-N_3-z,\qquad z\ge0.
$$

Let $L_0,L_2$ be the actual outputs of original ternary height one
on old first roots zero and two. Let $T_u$ contain actual original
height-two outputs on old word $u$. Only sources whose full output
AP intersects $H$ are called active; other sources may be omitted.
The same-tree whole-cover hypothesis gives the complete containments

$$
\begin{aligned}
H&\subseteq(L_0\cup T_3)\cap(L_0\cup T_6),\\
H&\subseteq(L_2\cup T_2)\cap(L_2\cup T_5)\cap(L_2\cup T_8).
\end{aligned}
\tag{SC182}
$$

At the same output point $x\in H$, apply each actual source map
$F_{u,\theta}$. The original whole cover supplies an owner of each
image. None can have original ternary height zero, because its
common output would then contain $x$, contrary to the retained
choice. The owner therefore belongs to the displayed height-one
or height-two menu for that safe word. Removing inactive sources
does not change this service.

These contain the entire lower-and-top liability at every integer
lift. Outer sources need not be literal omitted members of the
inner-sibling retained construction: the displayed containments,
rather than that membership, supply their service.

Choose any two of the three outer words. For definiteness use $2,5$
and omit $8$. Let $\ell$ count all active sources in $L_0\sqcup L_2$,
and let $t$ count active tops in $T_3\sqcup T_6\sqcup T_2\sqcup T_5$.

### A concrete profile with no restriction on the number of columns

Assume every source used by these four menus has output modulus
$n_d=3^{b_m}m$, where $m\mid M$, $m\ge1$, $(m,15)=1$, and there is only one
used output height $b_m$ per numerical cofactor $m$. Require
$b_m\ge2$ for $m>1$ and, if the unit cofactor is used, $b_1\ge3$.
The different cofactors need only be numerically different; they
may overlap or divide one another. They need not be pairwise
coprime. The unused outer color imposes no additional hypothesis.

A fixed $m$ then has at most one used lower original
$3\cdot5^{b_m}m$ and at most one used top original
$9\cdot5^{b_m}m$. The lower belongs to just one of $L_0,L_2$;
the top belongs to just one of the five old words. In the selected
four menus, the lower is requested twice and a selected top once.

Add $[0]_5$. Give the four other new roots to the four complete
menus in the following order:

| New root modulo $5$ | Complete actual source menu |
|---|---|
| $1$ | $L_0\cup T_3$ |
| $2$ | $L_0\cup T_6$ |
| $3$ | $L_2\cup T_2$ |
| $4$ | $L_2\cup T_5$ |

For an active lower with nonunit cofactor $m$, assign the slots $m$ and
$3m$ to its two requested roots, in the displayed order. For a
selected active top assign slot $9m$ to its one root. If no lower
is present in that cofactor, assigning the top slot $m$ instead
is also valid and leaves the count unchanged.

For the unit cofactor, use slots $3,9$ for the lower's two roots
and slot $27$ for the selected top's root. If there is no lower,
the top may instead use slot $3$. These slots divide its output
modulus under the stated height condition and are all nonunits.

For every request by actual source $d$ on new root $r$, with its
assigned slot $s$, add the CRT class

$$
P_{d,r}=[r]_5\cap[\eta_d]_s,
\tag{SC183}
$$

where $C_d=[\eta_d]_{n_d}$ is that source's actual output. Since
$s\mid n_d$, this patch contains all of $C_d$ on its assigned
new root. The four displayed complete containments therefore
cover every point of $H$ on roots $1,2,3,4$; the bought new class
covers root zero. No agreement between different source phases
is required, and no retained class is removed or rephased.

### Global distinctness and original payment

Within a nonunit cofactor, the requests use different slots among
$m,3m,9m$; the unit cofactor uses different slots among $3,9,27$.
Across different cofactors, the unique decomposition
$3^jm$ with $(m,3)=1$ prevents every numerical collision, even
when $m\mid m'$. All slots are greater than one, so their new
labels $5s$ are distinct from the shared $5$. They are also
distinct from all $5$-free labels in $\mathcal F_0$.

Each request $s=3^jm$ has its original donor
$3\cdot5^jm$. The actual lower or top source and divisor closure
supply this label because $j\le b_m$. The donor map is injective
across all assigned slots. A donor with $m>1$ has a nonunit cofactor;
a donor with $m=1$ has $j\ge1$ and hence contains $5$. Thus the
original pure labels $3,9$ remain separate. Those two originals
have old ternary phases $1\pmod3$ and $0\pmod9$, respectively,
so they are not themselves safe-menu suppliers. Hence

$$
c=1+2\ell+t,\qquad
N_3\ge2+2\ell+t,\qquad
|\mathcal F_0\cup\mathcal P|
=K-N_3-z+c\le K-z-1<K.
\tag{SC184}
$$

There is no dependence on the number of active cofactors and no
need for an original product column $m_im_j$. The count pays the
whole patch from the original inventory already present in the
retained-family identity. If there are no requests, the complete
containments make $H$ empty and no patch is needed.

### Exact shallow boundary of this same construction

With one used height $b_m$ per cofactor, put
$$
r_m=2\mathbf1_{\text{active lower}}+
\mathbf1_{\text{selected active top}},\qquad
r_m\le b_m+1\ (m>1),\qquad r_1\le b_1.
\tag{SC185}
$$
These are the exact capacities for this explicit per-column
assignment. For $m>1$, inject the requests into
$m,3m,\ldots,3^{b_m}m$. Thus a nonunit lower-only column needs
$b_m\ge1$, a nonunit top-only column permits $b_m=0$, and a
nonunit column with both needs $b_m\ge2$.

For $m=1$, the available nonunit slots are
$3,9,\ldots,3^{b_1}$, so the same construction needs $r_1\le b_1$.
A pure top alone therefore needs $b_1\ge1$, a pure lower alone
needs $b_1\ge2$, and a pure lower together with a selected pure top
needs $b_1\ge3$. The original donors still avoid both reserved pure
ternary labels. These conditions include the complete unit-column
liability rather than assuming that the bought root absorbs it.

Selecting the omitted outer color may remove
the top request from otherwise deficient columns; this does not
change the original lower obligations.

Multiple used heights at one cofactor are not automatically
included. The argument does not make the
Section 38 noncover into a whole cover: that construction lacks
the outer complete-menu containments used here.

### Reuse boundary

SC125 supplies the actual-phase root patch; SC126 and SC145--SC146
supply its original donor injection. [Report 385, Section 123](385-private-congruence-hulls-and-crossed-modulus-closure.md#123-whole-private-donor-obligations-can-be-reassigned-to-spare-original-labels)
already assigns complete source menus to different new roots. The change is the complete liability
assigned to each root: four different safe menus serve all of
$H$, so a lower is copied twice and a selected top only once.
SC124 and SC147 instead independently assign all four nonzero
roots to every source in one complete family. Their failure does
not test this four-menu construction.

SC113--114 similarly consume complete menus, but flattening to
$3$-free cofactors would discard the distinct slots $m,3m,9m$
used here. SC136 need not be applied to separate intersections.
The three-column restriction and pairwise-coprime hypothesis of
SC161--171 are absent in this profile because no cofactor
products or star-intersection graph is used.

This is a concrete consumer of those existing primitives, not a
new general Hall or CRT theorem or a literature-priority claim.
It is ordinary constructive mathematics, without new Lean
verification or a resolution of unrestricted Erdős #7.

## 42. Multiple output heights have an exact four-menu prefix-capacity test

Keep the five actual same-tree menus and the height-zero-priority
retained choice of Section 41. Reuse the nested initial-segment
matching criterion of Report 385 DP12, and the actual-phase root
patch and original donor injection of SC183--184. This gives a
concrete extension of the four-menu construction to multiple output
heights at the same cofactor. It is a test for this allocation,
not a claim that all actual whole covers pass it.

For each numerical cofactor $m\mid M$, let $L_m(h)$ count active
lower sources in $L_0\sqcup L_2$ with cofactor $m$ and output
height at most $h$. Let $T_m(h)$ count all active safe tops with
those bounds, across the five colors. Let $T_{c,m}(h)$ count just
the tops of outer color $c\in\{2,5,8\}$ with those bounds.
All height thresholds $h$ are nonnegative integers. All counts refer
to the same fixed tree and complete hole $H$.

Choose one outer color $c$ to omit. Assign the two inner menus and
the two remaining outer menus to the four fresh nonzero roots.
Each lower then requests two root patches; every selected top
requests one. A request at height $b$ uses a slot retaining the
entire numerical cofactor:

$$
\{3^jm:0\le j\le b\}\quad(m>1),\qquad
\{3^j:1\le j\le b\}\quad(m=1).
\tag{SC186}
$$

The slot must be different for every request at this new 5-depth.
No proper cofactor divisor or extra phase sharing is used in this
particular construction. Put $\delta_m=\mathbf1_{m>1}$. The exact
condition for these requests to admit an assignment is

$$
\exists c\in\{2,5,8\}\quad
\forall m\mid M\quad\forall h\ge0,\qquad
2L_m(h)+T_m(h)-T_{c,m}(h)\le h+\delta_m.
\tag{SC187}
$$

For necessity, every request of height at most $h$ has to use one
of the $h+\delta_m$ slots of that cofactor through height $h$.
For sufficiency at a fixed $c$, process all requests in one
cofactor in increasing height, breaking equal-height ties
arbitrarily. Give each request the smallest unused eligible index
$j$. At a request of height $b$, the prefix inequality at $h=b$
says that all requests encountered through that height fit in the
eligible initial segment. This is the existing DP12 matching rule.
Different cofactors cannot collide because $3^jm$ has a unique
3-free part. It is enough to test heights actually occurring in a
request: the left side is constant between them and the right side
increases.

The single omitted color $c$ must work for every column and every
height at once. Choosing a different omitted color separately for
each inequality would fail to specify four complete source menus.
For $m=1,h=0$ the right side is zero. This excludes every unit
height-zero request, consistently with the fact that original
pure $3$ and $9$ are not safe-menu sources.

Give each assigned request its SC183 CRT patch at the designated
fresh root. Its slot divides the actual source modulus, so each
complete source keeps its service on that root. Divisor closure
supplies the original donor $3\cdot5^jm$: the source is either
$3\cdot5^bm$ or $9\cdot5^bm$ and $j\le b$. Donors are
distinct across requests. Nonunit cofactors separate them from
pure $3,9$, while unit cofactors use $j\ge1$ and contain $5$.
With $R_c$ the total number of selected requests, SC184 becomes

$$
c_{\rm patch}=1+R_c,\qquad
N_3\ge2+R_c,\qquad
|\mathcal F_0\cup\mathcal P|\le K-z-1<K.
\tag{SC188}
$$

Thus SC187 suffices for a complete paid repair at arbitrary used
heights and arbitrarily many, possibly overlapping cofactors.
The one-height capacities SC185 are its direct special case.

Contrapositively, an EB1 whole cover must give, for each choice of
omitted outer color $c$, at least one cofactor and height for which

$$
2L_m(h)+T_m(h)-T_{c,m}(h)>h+\delta_m.
\tag{SC189}
$$

These witnesses may be different for the three choices. Such a
violation obstructs only this allocation using full cofactor
slots. Additional divisor slots, common phase enclosures, deeper
fresh prefixes or different complete menus can still give a
repair. No unproved implication from numerical congestion to an
original whole-cover contradiction is used here.

This reuses the existing nested Hall calculation and donor
construction with the four-menu demand counts; it adds no new
general matching theorem, finite enumeration or Lean verification.

## 43. Three complete top colors admit a paid repair after two cofactor projections

Keep original ternary height $A=2$, one common source tree $\theta$,
the fixed retained family $\mathcal F_0$ and its bought root
$S=[s]_3$. Its complete integer hole and exact inventory satisfy
$$
H=\mathbb Z\setminus\bigcup\mathcal F_0,\qquad
|\mathcal F_0|=K-N_3-z,\qquad z\ge0.
$$
Every retained modulus is $5$-free. If $H$ is empty, the retained
family itself gives strict descent, so suppose $H\ne\varnothing$.

An actual safe top source has original label, output and cofactor
$$
d_t=9\cdot5^{b_t}m_t,\qquad
C_t=[\eta_t]_{n_t},\qquad
n_t=3^{b_t}m_t>1,\qquad m_t\mid M,\quad(m_t,15)=1.
$$
The output labels $n_t$ are globally distinct across all safe top
colors. The excluded label $n_t=1$ would be original pure $9$,
whose old word is not safe. Unit cofactors at positive output
height remain allowed.

Choose finite subfamilies $\mathcal P,\mathcal Q,\mathcal R$ from
three different actual top colors, each serving the entire hole:
$$
H\subseteq\bigcup_{t\in\mathcal P}C_t,\qquad
H\subseteq\bigcup_{t\in\mathcal Q}C_t,\qquad
H\subseteq\bigcup_{t\in\mathcal R}C_t.
\tag{SC190}
$$
Assume the cofactors in $\mathcal P\sqcup\mathcal Q$ are nonunit
and numerically pairwise distinct. Put
$$
J=\{m_t:t\in\mathcal P\sqcup\mathcal Q\},
\qquad n_r\notin J\cup3J\quad(r\in\mathcal R).
\tag{SC191}
$$
The last condition excludes exactly a direct source in $\mathcal R$
with cofactor in $J$ and output height zero or one. No coprimality
between different cofactors is assumed. Within $\mathcal R$,
cofactors may repeat at different heights, may be units, and may
overlap all other cofactors. The required service is all of $H$,
including any discarded lower liability; covering just its top-only
part does not meet the premise.

### Actual phases and complete coverage

Let $\alpha,\beta$ be the two ternary roots other than $s$ and put
$E_t=[\eta_t]_{m_t}$ for $t\in\mathcal P\sqcup\mathcal Q$.
Each $E_t$ encloses the whole actual $C_t$. Add the following APs:

| New condition | Actual suppliers or enclosures | Numerical labels |
|---|---|---|
| $[0]_5$ | none | $5$ |
| $[1]_5$ | $E_t$, $t\in\mathcal P$ | $5m_t$ |
| $[2]_5$ | $E_t$, $t\in\mathcal Q$ | $5m_t$ |
| $[3]_5$ | $C_t$, $t\in\mathcal R$ | $5n_t$ |
| $[4]_5\cap[\alpha]_3$ | $E_t$, $t\in\mathcal P$ | $15m_t$ |
| $[4]_5\cap[\beta]_3$ | $E_t$, $t\in\mathcal Q$ | $15m_t$ |

Each row means intersection with every listed source or enclosure.
All intersections are single APs by CRT. Their cofactor phases are
reductions of the actual source phases. Only the enlarged enclosures
drop ternary information; no actual source or retained phase changes.

For every $x\in H$, the three complete menus supply its new roots
$1,2,3$, and the shared class supplies root zero. On root four,
$x$ has ternary residue $\alpha$ or $\beta$ because it avoids the
retained $S$. Use its $\mathcal P$ enclosure in the first case and
its $\mathcal Q$ enclosure in the second. This covers every integer
lift of the whole $H$. Points outside $H$ keep their old owner.

The projected labels are distinct because the cofactors in $J$
are distinct and the two rows have different ternary valuations.
The direct labels $5n_r$ are distinct by original top-label
uniqueness. Their only possible collisions with projected labels
are $n_r=m\in J$ or $n_r=3m\in3J$, precisely the excluded cases.
They cannot equal $5$ because $n_r>1$. In particular, a unit
cofactor in $\mathcal R$ produces $5\cdot3^{b_r}$ with $b_r\ge1$,
which does not collide with any nonunit-cofactor projected label.
All new labels are odd nonunits divisible by $5$, hence fresh
relative to $\mathcal F_0$.

### Original inventory pays both projected rows

Write
$$
\chi(3^bm)=5^bm,\qquad
V_a=\{n>1:3^a\chi(n)\in D\}\quad(a=1,2).
$$
The exact original partition is $N_3=2+|V_1|+|V_2|$, reserving
the original pure labels $3,9$. The set
$$
W=J\sqcup\{n_r:r\in\mathcal R\}
$$
is disjoint and has size $p+q+r$, where $p,q,r$ are the three
family sizes. Divisor closure puts every $w\in W$ in both $V_1$
and $V_2$. In particular, a projected cofactor $m_t$ is paid by
the original pair $3m_t,9m_t$ even when its top source had higher
output height. A direct source is paid from
$3\chi(n_r),9\chi(n_r)$.

The pairs for different $w$ are disjoint by unique factorization:
$\chi$ is injective and its values are $3$-free. Since $w>1$,
none is the reserved original $3$ or $9$. For a unit cofactor
in $\mathcal R$, both labels contain a positive power of $5$.
Thus
$$
\begin{aligned}
c&=1+2p+2q+r,\\
N_3&\ge2+2p+2q+2r,\\
|\mathcal F_0\cup\mathcal B|
&\le K-(1+r+z)<K.
\end{aligned}
\tag{SC192}
$$
No further retained class is deleted to pay this repair. This is
a comparison against the original inventory already present in
the exact count for $\mathcal F_0$.

### Three complete colors cannot all use one common height

Fix an output height $h\ge0$. Suppose three distinct safe colors
each cover all $H$ using only their actual top sources at height
$h$. Across those three families, cofactors are numerically
distinct: equal cofactors would duplicate the original label
$9\cdot5^h m$. If a unit-cofactor source occurs, it belongs to
only one family; assign that family to the direct role
$\mathcal R$. The other two families have nonunit cofactors,
and the direct cofactors differ from theirs. All packet conditions
then hold, giving strict descent.

Writing $T_{u,h}$ for the union of safe color $u$'s actual top
outputs at height $h$, this gives

$$
\#\{u\in\{2,3,5,6,8\}:H\subseteq T_{u,h}\}\le2
\qquad(h\ge0).
\tag{SC193}
$$

Consequently an EB1 family has at most two top colors capable of
covering all $H$ at any one fixed output height. This includes
heights zero and one, arbitrarily many cofactor columns, and
arbitrary common prime factors among different cofactors. It does
not assert that any color has such a fixed-height complete subcover.

The five-safe relation supplies three complete outer top colors
when $H\cap L_2=\varnothing$. Under that hypothesis, those three
complete covers cannot all be supplied at one common height.

### Four complete top colors cannot survive at arbitrary heights

There is also a direct use of the existing complete-menu root
allocation with no height or cofactor restriction. If four safe
top colors each cover all $H$, assign them to the four nonzero
fresh roots and add $[0]_5$. Each selected top uses its actual
output slot once, giving globally distinct labels $5n_t>5$.
The complete patch costs at most $1+|V_2|<N_3+z$, contradicting
EB1. Therefore, for the full top-color unions and their deficits,

$$
E_u=H\setminus T_u,\qquad
\#\{u\in\{2,3,5,6,8\}:E_u\ne\varnothing\}\ge2.
\tag{SC194}
$$

The complete five-menu containments locate these deficits:
$E_3,E_6\subseteq L_0$ and $E_2,E_5,E_8\subseteq L_2$.
This is direct reuse of the complete-menu construction, with no
new general patch theorem. It does not force three complete top
colors or the cofactor conditions SC191.

### Two complete flat colors force a third-color liability on the paired $45m$ family

Suppose $\mathcal P,\mathcal Q$ are complete top subcovers of $H$
in two different colors, both using output height zero. Let
$\mathcal R$ be the entire actual top family of a third color,
also covering all $H$. The cofactors in
$J=\{m_t:t\in\mathcal P\sqcup\mathcal Q\}$ are nonunit and
globally distinct because the corresponding originals are $9m_t$.

Delete from $\mathcal R$ the subfamily
$$
\mathcal B_J
=\{r\in\mathcal R:b_r=1,\ m_r\in J\},\qquad
\mathcal R_{\rm good}=\mathcal R\setminus\mathcal B_J.
$$
No remaining source can have $b_r=0,m_r\in J$: its original $9m_r$
would duplicate one already assigned to a different top color.
All remaining sources therefore satisfy $n_r\notin J\cup3J$.
If they still covered $H$, the paid packet would contradict EB1.
Hence
$$
H\setminus\bigcup_{r\in\mathcal R_{\rm good}}C_r
\ne\varnothing.
\tag{SC195}
$$
At any point $x$ in this nonempty set, the complete third color
has an owner, and every third-color owner belongs to
$\mathcal B_J$. Each such owner is an actual original $45m$,
with an actual original $9m$ in $\mathcal P$ or $\mathcal Q$.
Thus this whole $45m$ subfamily cannot be deleted simultaneously
without losing complete third-color service.

The conclusion does not single out an individually indispensable
$45m$ original: several members may serve the same residual
liability. It also does not say that the paired $9m$ source owns
$x$, or that the paired source phases agree. When
$H\cap L_2=\varnothing$, the statement applies to any two flat
complete subcovers among the three outer colors, taking the
remaining outer color as $\mathcal R$.

These are constructive uses of complete actual source service,
CRT root splitting and the original inventory identity. They do
not force the packet hypotheses in the remaining configurations,
assert literature priority, supply Lean verification, or resolve
unrestricted Erdős #7.

## 44. A single inner-deficit lower forces an identical opposite-root top partner

Keep the original height-two whole cover, one common substitution
tree, the actual retained family $\mathcal F_0$, and its complete
integer hole $H$ from the five-safe-menu construction. In
particular, every retained modulus is 5-free and

$$
|\mathcal F_0|=K-N_3-z,\qquad
N_3=2+|V_1|+|V_2|,\qquad z\ge0.
\tag{SC196}
$$

Here $V_a=\{n>1:3^a\chi(n)\in D\}$, with
$\chi(3^bm)=5^bm$ for $(m,15)=1$. The separately counted
originals are the pure classes of moduli 3 and 9. Use the
normalization $1\pmod3$ and $0\pmod9$ for these classes.
The two inner safe words are 3 and 6, and the three outer safe
words are 2, 5 and 8. Every safe top is an actual original
$9\chi(n_t)$, with nonunit output modulus $n_t>1$.

Write $T_u$ for the union of the actual active top outputs of
safe color $u$. Outputs from different top suppliers have
different numerical moduli, including across colors: equal
$n_t$ would give the same original numerical label
$9\chi(n_t)$. This uniqueness does not assert that a lower and
a top cannot have the same output modulus.

Assume the three outer colors each cover the entire hole, and one
actual lower source from $L_0$ contains both inner deficits:

$$
H\subseteq T_2\cap T_5\cap T_8,\qquad
E_u=H\setminus T_u,\qquad
E_3\cup E_6\subseteq C_\ell=[\eta_\ell]_n,
\quad n>1.
\tag{SC197}
$$

The lower has actual original label $3\chi(n)$, so
$n\in V_1$ and $|V_1|\ge1$. Other lower sources may meet
$H$; SC197 does not say that $C_\ell$ covers all of $H$.
For example, the five-menu containments imply SC197 if
$H\cap L_2=\varnothing$ and this is the only active $L_0$
source.

Under EB1, there must be a unique active safe top supplier $t$
with output modulus $n$. Its color $c$ lies in
$\{2,5,8\}$, and its actual output equals the lower output:

$$
C_t=C_\ell.
\tag{SC198}
$$

Furthermore, put

$$
D_c=H\setminus
\bigcup_{\substack{v\text{ active top of color }c\\v\ne t}}C_v.
\tag{SC199}
$$

Then both complete-liability intersections are nonempty:

$$
D_c\cap E_3\ne\varnothing,
\qquad
D_c\cap E_6\ne\varnothing.
\tag{SC200}
$$

The two witnesses may coincide. SC199 credits all other actual
same-color top service; it is not just a chosen private trace.

### Omit either inner color before assigning the four fresh roots

If $H$ is empty, the retained family already contradicts EB1,
so assume $H\ne\varnothing$. Choose one inner color
$j\in\{3,6\}$ to omit, and let $k$ be the other. The four
menus

$$
T_2,\quad T_5,\quad T_8,\quad C_\ell\cup T_k
\tag{SC201}
$$

all cover $H$. For the fourth menu, a point not in $T_k$
belongs to $E_k\subseteq C_\ell$. Assign these menus to fresh
5-roots 1, 2, 3 and 4 respectively; add $[0]_5$. As in the
existing actual-phase root patch, a supplier $[\eta]_q$
assigned to root $r$ contributes

$$
[r]_5\cap[\eta]_q
$$

with numerical modulus $5q$. All output moduli are coprime to
5, so these are CRT classes. The four complete menus cover the
whole hole at every lift; $\mathcal F_0$ remains unchanged.

Top-output uniqueness leaves only one possible numerical collision:
the lower's label $5n$ with a top at output modulus $n$.
If no active safe top has this modulus, every label is distinct.
If such a top belongs to inner color 3 or 6, choose that color as
the omitted $j$. Again every added label is distinct. Tops on
unsafe original words do not occur in these menus and cannot cause
a collision. Since $n>1$ and every safe top has $n_t>1$, no
supplier patch coincides with the shared label 5.

In either collision-free case the cost is at most

$$
c\le2+|V_2|<2+|V_1|+|V_2|+z=N_3+z.
\tag{SC202}
$$

Every new modulus contains 5 and is therefore fresh relative to
$\mathcal F_0$. SC196 gives a distinct odd whole cover with fewer
than $K$ classes, contradicting EB1. Hence the unique partner
exists and has an outer color $c$.

### Move the omitted inner color to the entire deleted liability

Fix either $j=3$ or $j=6$, and start with the allocation SC201.
Remove the outer partner $t$'s patch from its assigned new root
$r_c$. Place every top supplier of the omitted color $j$ at
that same root. The resulting menu at $r_c$ is exactly

$$
\left(\bigcup_{\substack{v\text{ active top of color }c\\v\ne t}}
C_v\right)\cup T_j.
\tag{SC203}
$$

All other fresh-root menus are unchanged. Every safe top is now
used once, except for the deleted partner; the lower is used once.
Thus all numerical labels are distinct and the cost is at most

$$
c\le1+1+(|V_2|-1)=1+|V_2|<N_3+z.
\tag{SC204}
$$

The changed root covers the entire hole exactly when
$D_c\subseteq T_j$, equivalently when
$D_c\cap E_j=\varnothing$. To justify the converse on actual
integers, choose a common 5-free period $N$ for
$\mathcal F_0$ and all displayed outputs. If
$x\in D_c\setminus T_j$, CRT gives an integer $y$ satisfying

$$
y\equiv x\pmod N,\qquad y\equiv r_c\pmod5.
$$

It remains in $H$ and outside SC203, and all patches on other fresh
roots miss it. Conversely, if $D_c\subseteq T_j$, SC203 covers
every point of $H$ at that root, while SC201 pays the other roots.
This equivalence uses the whole liability after deleting the top,
including points not private to that top before choosing a color.

If either $D_c\cap E_3$ or $D_c\cap E_6$ were empty, choose
the corresponding omitted inner color and use SC203. The paid repair
would contradict EB1. This proves both nonemptiness statements in
SC200; neither inner color's deficit was discarded.

### The forced overlap determines the actual output phase

The outer color $T_c$ covers $H$, so SC199 implies
$D_c\subseteq C_t$. By SC197, $E_3\cup E_6\subseteq C_\ell$.
Either witness from SC200 therefore lies in $C_t\cap C_\ell$.
These two complete APs have the same numerical modulus $n$,
so their residues modulo $n$ are equal and SC198 follows.

The word "opposite" concerns the old ternary source root: the
lower belongs to old first root zero, whereas its outer top partner
belongs to old first root two. Equality of their output APs is
compatible with original comparable-disjointness, because their
original APs already disagree modulo 3. Thus SC198--SC200 identify a
necessary remaining same-source structure; they do not themselves
contradict EB1 or resolve arbitrary lower-deficit configurations.

This is an ordinary constructive consequence of the existing
five-menu service, actual-phase root patch and inventory identities.
It uses no new enumeration, independent source optimization, or
Lean verification.

## 45. The identical-output partner has an original parent-private boundary

Keep the single-inner-deficit hypotheses and their forced partner:
one actual lower $\ell\in L_0$, an outer top $t$ of color
$c\in\{2,5,8\}$, and

$$
C_\ell=C_t=[\eta]_n,\qquad
D_c\cap E_3\ne\varnothing,\qquad
D_c\cap E_6\ne\varnothing.
\tag{SC205}
$$

All sets, original phases and maps use the same original family
and the same substitution tree. Put $n=3^bm$ and
$w=\chi(n)=5^bm>1$, with $(m,15)=1$. The two original
numerical labels are $3w$ and $9w$. Report 388 SC2--SC4 gives
their actual phases from one common inverse tree coordinate.
Equality of the output APs therefore implies equality of their
original residues modulo $w$; denote that residue by $a$.
Their original first ternary roots remain different: zero for
the lower and two for the outer top.

### The original cofactor parent must have private points in both roots

Original divisor closure supplies the original label $w$.
Write its actual phase as $a_w\pmod w$. Comparable-original
disjointness gives $a_w\ne a$, because otherwise its class
would contain the original lower $3w$.

The original parent phase group

$$
J_a=\{M\in D:w\mid M,\ M>w,\ \alpha_M\equiv a\pmod w\}
$$

contains both $3w$ and $9w$. Reuse Report 385 DR1--DR5:
moving the original $w$-class to $a\pmod w$ and deleting
the whole $J_a$ leaves exactly the complete original private
region $P_w$. Since $|J_a|\ge2$, DR5 gives

$$
3w\nmid\Gamma_w,
\tag{SC206}
$$

where $\Gamma_w$ is the hull of the complete original private
region, not of a selected source trace. Every point of $P_w$
already has residue $a_w\pmod w$. If all such points had one
residue modulo 3, they would lie in one AP modulo $3w$, contrary
to SC206 and the existing private-hull equivalence. The original
pure class $[1]_3$ excludes root one from $P_w$. Consequently

$$
P_w\cap[0]_3\ne\varnothing,
\qquad
P_w\cap[2]_3\ne\varnothing.
\tag{SC207}
$$

The root-zero private points also avoid the original pure
$[0]_9$, so their old words lie in $\{3,6\}$. SC207 does
not require both of those words, and its two private points need
not have the same complete cofactor coordinate.

These private points have $w$-phase $a_w$, whereas the paired
lower/top classes and their source witnesses have $w$-phase
$a$. They cannot be identified with one another. SC207 is a direct
consumer of the existing crowded-parent result, not a new general
parent-exchange theorem.

### With one active inner lower and no outer lower, the deficit witnesses are private

For this paragraph impose the additional conditions

$$
H\cap L_2=\varnothing,
\qquad
\ell\text{ is the only active source in }L_0.
\tag{SC208}
$$

Choose, separately for $j=3,6$, any

$$
x_j\in D_c\cap E_j.
$$

Both original image points are then private to their indicated
original labels:

$$
F_{j,\theta}(x_j)\in P_{3w},
\qquad
F_{c,\theta}(x_j)\in P_{9w}.
\tag{SC209}
$$

To check the first assertion, use the exact original-owner
pullback SC2--SC4. The point $x_j\in H$ misses every
height-zero output by the retained-source convention of the
five-menu construction. At old word $j$, any height-one owner
has its output in $L_0$. Only $\ell$ can contain a point
of $H$, by SC208; an inactive output cannot contain $x_j$.
Height-two owners have color $j$, and none contains $x_j$
because $x_j\in E_j$. The lower does contain $x_j$, since
the two deficits lie in $C_\ell$. Thus it is the unique owner
in the entire original family.

For the second assertion, height-zero ownership is excluded in
the same way. A height-one owner at old word $c$ would belong
to $L_2$, excluded by SC208. Among height-two owners, only color
$c$ is compatible. The definition of $D_c$ excludes every
other top of that color, while $T_c$ covers $H$, so $t$
owns the point. This proves unique original ownership.

For each fixed $j$, the two points in SC209 share the complete
original 3-free coordinate: their 5-coordinate is the same
$\theta_B(x_j\bmod3^B)$, and their $M$-coordinate is the
same $x_j\bmod M$. Only the old ternary word changes from
$j$ to $c$. The witnesses $x_3,x_6$ may differ; no common
point of $D_c\cap E_3\cap E_6$ is asserted.

In particular the complete private region of the original lower
meets both inner words:

$$
P_{3w}\cap[3]_9\ne\varnothing,
\qquad
P_{3w}\cap[6]_9\ne\varnothing,
\qquad 9w\nmid\Gamma_{3w}.
\tag{SC210}
$$

Without SC208, an inner image can also have another active
$L_0$-owner and an outer image can have an $L_2$-owner.
SC205 alone therefore does not make its witnesses original-private.

### What the existing exchanges do and do not pay

Applying DR1 instead to the original parent $3w$, at the
outer top's projected phase, absorbs that top and any other
proper descendants in the same phase. Its exact liability is
the entire original $P_{3w}$. It is not merely
$F_{3,\theta}(E_3)\cup F_{6,\theta}(E_6)$: that selected
tree may omit original 5-prefixes, and the deficits impose no
condition on all other original-private points.

Under SC208, SC210 also rules out repairing that complete liability
with a single freed $9w$-class, regardless of its new phase.
The original lower's private region has two distinct residues
modulo $9w$. The reciprocal-hull swap of Report 385 RH1--RH6
likewise does not apply to the pair $(3w,9w)$, because it would
require $9w\mid\Gamma_{3w}$. Its other divisibility,
$3w\mid\Gamma_{9w}$, is automatic but insufficient.

The original $w$-parent exchange has a different exact
liability, $P_w$, as in SC207. Any proposal to pay that move must
cover this full region using labels outside $D\setminus J_a$,
with the class-count and, at equality, modulus-sum budgets of DR2.
Two private witnesses do not certify such coverage.

Report 385 OHL6--OHL7 supplies a complete-hole exchange for a
packet of original full-height top labels at one common ternary
word and one fixed first auxiliary-prime digit, with one fixed
code per original. The present pair has different original
ternary heights and different old roots, so that packet interface
does not directly apply to it. A larger proposed packet would
need its actual complete deletion-hole projection and a lawful
fixed-code covering of every required new branch; SC205 or SC209
does not provide those universal conditions.

Thus the parent bridge and SC209 give additional necessary
structure, but no complete paid elimination of the identical
partner has been obtained. The remaining obligation is a legal
repair of one specified complete original liability, or another
whole-hole construction, under the actual shared phases and
original numerical inventory. These are ordinary deductions
from existing owner, private-hull and exchange results, without
new enumeration or Lean verification.

## 46. Five coprime active columns reduce to one equality boundary

Keep the complete-hole setup of Sections 39--40: original ternary
height two, exactly one retained actual lower per surviving slot
other than $3$, and all active discarded lower and omitted top
outputs in five slots

$$
n_i=3^{b_i}m_i,\qquad b_i\ge2,\qquad m_i>1,\quad m_i\mid M,
\qquad(m_i,15)=1,\qquad(m_i,m_j)=1\quad(i\ne j).
$$

There is one active height per cofactor. Let $\ell\le5$ count
active discarded lowers, $t\le5$ active tops, and $e$ the edges
in the actual cross-color top-intersection graph. Isolated active
tops count in $t$. The complete lower-plus-edge enclosure formula
SC172 still holds. All its enclosures lie in the two unbought
output ternary roots.

### Original inventory, including the forced largest-prime child

Report 385 Section 250 obtains $P\ge29$ by combining GHA10 with
[Report 792](../750-799/792-optimal-fixed-leaf-weights-admit-the-complete1200-tail.md).
GHA10 gives $P<135$. If at most eight support primes occurred,
all would lie in Report 792's small-prime set and every original
would satisfy its ternary-height bound two, contradicting its
noncoverage conclusion. At least nine odd support primes force
$P\ge29$. GHA10 alone supplies the upper bound and the forced
labels, not this lower bound.

Use Section 40's disjoint counts $N_3=c_1+c_2+t_P$. GHA10
supplies the actual original $3P^{H_P}$, so $t_P\ge1$.
NF66 says $c_1\ge P-1$ or $c_1+t_P\ge P$. Both alternatives
therefore give

$$
N_3\ge P+c_2.
\tag{SC211}
$$

For $t\ge1$, the same count as SC174 gives $c_2\ge3t$:
the unit labels $9,45,225$ and three labels from every $P$-free
top column are distinct, and at most one pairwise-coprime column
contains $P$. Consequently

$$
N_3\ge P+3t\qquad(t\ge1).
\tag{SC212}
$$

No original product column is counted. For $t=0$ the weaker
existing $N_3\ge P-1$ already suffices below.

### A complete repair for each intersection-graph shape

Apply SC167 to all $\ell$ lower enclosures and all $e$ edge
enclosures, and add $[0]_5$. This costs $1+3\ell+3e$ and
leaves only their new root $[1]_5$. Complete it with pure labels
$15,45$ and SC175.

If all nonisolated top vertices are connected, edge compatibility
propagates one actual residue $\gamma\pmod9$. Let $R$ be its
first ternary root, and let $a,b$ count the lower enclosures in
$R$ and the other unbought root. The two Section 40 choices
leave at most $\min(b-1,a)$ lowers when $b>0$, and none when
$b=0$. Since $a+b\le5$, at most two remain, all in one root.
SC175 costs at most eight, hence

$$
c\le1+3\ell+3e+2+8\le26+3e.
\tag{SC213}
$$

A simple bipartite graph on $t\le5$ vertices has
$e\le\lfloor t^2/4\rfloor$. For $t\le4$ this gives
$c\le26+3t<29+3t\le N_3$. For $t=5,e\le5$, it gives
$c\le41<44\le N_3$. Only $e=6$ remains, forcing $K_{2,3}$.

If there are two nontrivial components, their sizes are $2+2$
(possibly with an isolated vertex) or $2+3$, so $e\le3$.
Each component has a common actual modulo-9 phase. If their first
roots differ, pure $15$ covers the root with at least half the
lowers, and pure $45$ covers the entire other component; at most
two lowers remain in that other root. If both components share
$R$, either pure $15$ covers $R$ and pure $45$ one opposite
lower, or pure $15$ covers the opposite root and pure $45$ the
larger component. The smaller component has one edge. When
$b>0$, at most $\min(b-1,a+1)\le2$ enclosures remain, all in
one root; when $b=0$, the first choice leaves none. Thus

$$
c\le26+3e\le35<N_3,
\tag{SC214}
$$

because $t\ge4$ gives $N_3\ge29+12=41$.

If $e=0$, only lower enclosures need repair. Pure $15$ covers
a largest root group. At most two lowers lie outside it; pure
$45$ covers one, and at most one needs SC175's five-class packet.
Thus $c\le1+15+2+5=23<N_3$. If there are no lowers either,
$H$ is empty and no patch is needed.

These graph cases are exhaustive. Every residual cofactor is a
different singleton or edge product of the pairwise-coprime
nonunits $m_i$. All remain $3,5$-free, so the Section 40
distinctness proof applies to every patch. The entire enclosure
union is covered, including all discarded lower service; the
retained family stays fixed.

### The only unpaid count boundary

For $P\ge31$, even $K_{2,3}$ has $c\le44<46\le N_3$.
For $P=29$, strict descent follows unless all of the following
necessary conditions hold:

$$
\begin{gathered}
\ell=t=5,\qquad G=K_{2,3},\qquad N_3=44,\qquad z=0,\\
c_2=15,\qquad c_1+t_P=29,\qquad (a,b)=(2,3).
\end{gathered}
\tag{SC215}
$$

Indeed, $\ell\le4$ gives $c\le41$. With $\ell=5$, any
root split other than $(2,3)$ leaves at most one residual lower,
again giving $c\le41$. In the remaining case SC211--212 give
$N_3\ge44$; if $N_3>44$ or $z>0$, the complete patch still
strictly reduces the original class count.

The equality $c_2=15$ forces exactly one top cofactor to contain
$29$; otherwise the unit column and all five top columns give
$c_2\ge18$. Each of the four $29$-free cofactors must be a
prime. Any proper nonunit divisor would supply an additional
$29$-free original height-two label, different from all counted
columns by pairwise coprimality. The $29$-bearing cofactor must
be a pure power of $29$, since another prime divisor would
similarly supply an extra $29$-free column. Moreover every
$b_i=2$, because any $b_i\ge3$ supplies the additional unit
label $9\cdot5^3$. Up to reordering,

$$
(m_1,\ldots,m_5)=(q_1,q_2,q_3,q_4,29^h),\qquad
b_i=2,
\tag{SC216}
$$

where $h\ge1$ and the $q_i$ are distinct support primes other
than $3,5,29$.

### The lower phases are forced as well

If two of the three outside-root lowers shared their modulo-9
phase, the first pure-$15$/pure-$45$ choice would cover both
with label $45$ and leave at most one residual, giving $c\le41$.
If either inside-root lower had phase $\gamma$, the other
choice would again leave at most one residual.

If the two inside-root lowers instead shared a phase
$\delta\ne\gamma$, complete their residual enclosures
$[\eta_h]_{9h}$ with seven classes. Use the shared classes

$$
[1]_{25},\qquad [6]_{25}\cap[R]_3,\qquad
[11]_{25}\cap[\delta]_9,
$$

with labels $25,75,225$. For each of the two distinct nonunit
cofactors $h$, use

$$
[16]_{25}\cap[\eta_h]_h,\qquad
[21]_{25}\cap[\eta_h]_{3h},
$$

with labels $25h,75h$. All five children of $[1]_5$ are covered;
the common phase $\delta$ makes the third child valid for both
enclosures. The seven labels are distinct by their 3-valuations
and $3,5$-free cofactors, and are fresh at 5-depth two. This
gives $c\le34+2+7=43<N_3$.

Thus the two inside-root lowers occupy exactly the two children
other than $\gamma$, and the three outside-root lowers occupy
all three children of that root. If the bought root is $S=[s]_3$,
the five lower phases must be

$$
\{\alpha_i\bmod9:1\le i\le5\}
=\{v\bmod9:v\not\equiv s\pmod3,\ v\ne\gamma\pmod9\}.
\tag{SC217}
$$

At the remaining boundary SC215--217 the proved comparison is
only $c\le N_3$ with $z=0$. This supplies neither strict
class-count descent nor a modulus-sum descent. It does not show
that the boundary is realizable or impossible, and $44$ is an
upper bound for this construction, not a lower bound for all
repairs. The construction uses the existing source packets and
inventory bounds; it adds no Lean verification or enumeration,
and the unrestricted problem remains unresolved.

## 47. Two different fresh roots share the common top phase

Keep the same actual retained family and complete integer hole as
Report 388 Section 46. In its remaining five-column branch, let

$$
L_i=[\alpha_i]_{9m_i}\quad(1\le i\le5)
$$

be the five complete lower enclosures. The $m_i>1$ are pairwise
coprime and coprime to 15. Let the six actual cross-color top
intersections in $K_{2,3}$ have complete enclosures

$$
I_{ij}=[\beta_{ij}]_{9m_im_j},
\qquad \beta_{ij}\equiv\gamma\pmod9.
$$

The complete-service statement already gives

$$
H\subseteq\bigcup_{i=1}^5L_i\ \cup\!\bigcup_{ij\in E}I_{ij}.
\tag{SC218}
$$

Write $R=\gamma\bmod3$, and write $R'$ for the other
unbought ternary root. Exactly two lower enclosures lie in $R$
and three lie in $R'$. No further restriction on their modulo-9
phases or their cofactor phases is needed below. In particular,
the construction covers the distinct phases in SC217 without
identifying any lower phase with a top phase.

Add these three shared classes:

$$
[0]_5,\qquad [2]_5\cap[R]_3,\qquad
[1]_5\cap[\gamma]_9.
\tag{SC219}
$$

Their numerical moduli are 5, 15 and 45. The last two classes
occupy different fresh 5-roots. They jointly pay two roots of
every top-intersection enclosure.

### Three classes for each lower enclosure

For a lower in root $R$, add

$$
[1]_5\cap[\alpha_i]_{m_i},\qquad
[3]_5\cap[\alpha_i]_{3m_i},\qquad
[4]_5\cap[\alpha_i]_{9m_i}.
\tag{SC220}
$$

For a lower in root $R'$, add instead

$$
[2]_5\cap[\alpha_i]_{m_i},\qquad
[3]_5\cap[\alpha_i]_{3m_i},\qquad
[4]_5\cap[\alpha_i]_{9m_i}.
\tag{SC221}
$$

Each lower uses the three distinct numerical labels
$5m_i,15m_i,45m_i$. A root-$R$ lower is now entirely
covered: SC219 pays roots zero and two, and SC220 pays the other
three. A root-$R'$ lower has only its fresh root one left.

### Two classes for each top-intersection enclosure

For each of the six edges $ij$, add

$$
[3]_5\cap[\beta_{ij}]_{m_im_j},\qquad
[4]_5\cap[\beta_{ij}]_{3m_im_j}.
\tag{SC222}
$$

These have labels $5m_im_j$ and $15m_im_j$. Every point
of $I_{ij}$ on fresh roots zero, one and two is already paid
by SC219, because it has the actual phase $\gamma\pmod9$.
SC222 pays roots three and four. This covers every edge enclosure
completely, without replacing it by an independently chosen top
phase or assuming an original product column exists.

### The three residual lower enclosures share the depth-two prefix patch

For the three lowers in $R'$, reuse the explicit shared prefix
rows of SC175, with all three actual cofactors. Add the shared
classes

$$
[1]_{25},\qquad[6]_{25}\cap[R']_3
\tag{SC223}
$$

and, for each of those three lowers, add

$$
[11]_{25}\cap[\alpha_i]_{m_i},\qquad
[16]_{25}\cap[\alpha_i]_{3m_i},\qquad
[21]_{25}\cap[\alpha_i]_{9m_i}.
\tag{SC224}
$$

The five children $1,6,11,16,21\pmod{25}$ exhaust the
remaining fresh root one. SC223--SC224 therefore cover the complete
residual portions of all three lower enclosures, at every higher
integer lift. They cost $2+3\cdot3=11$ classes. SC175's
displayed rows apply verbatim; only the number of cofactors in
this application is three instead of at most two.

### Global distinctness and strict payment

At fresh 5-depth one, the cofactor parts are the unit, the five
singletons $m_i$, and the six edge products $m_im_j$.
Distinct subsets of pairwise coprime nonunits have different
products, so these parts are all different. The 3-valuations
separate the labels within each part. At fresh 5-depth two,
the labels are $25,75$ and the nine labels
$25m_i,75m_i,225m_i$ for the three residual lowers; these
are likewise different. Different 5-depths cannot collide.

All 41 labels are odd nonunits divisible by 5. Every retained
modulus is 5-free, so they are fresh against the unchanged
$\mathcal F_0$. All displayed phases are compatible CRT
conditions taken from the same actual enclosures. The complete
count is

$$
c=3+3\cdot5+2\cdot6+(2+3\cdot3)=41.
\tag{SC225}
$$

By SC218 and the complete branch checks above, the construction
covers all of $H$. SC212 gives $N_3\ge44$ in this five-top
branch, so

$$
|\mathcal F_0\cup\mathcal P|
=K-N_3-z+41\le K-z-3<K.
\tag{SC226}
$$

Thus SC215--SC217 cannot occur in an EB1 whole cover. The repair
already works at the earlier $(a,b)=(2,3)$, $K_{2,3}$ stage:
it does not require the prime/power classification SC216 or the
five distinct lower phases SC217. Together with Section 46's
other graph branches, this closes the stated five-column profile.
No claim forces an arbitrary cover into that profile. This is an
ordinary explicit application of existing CRT, prefix, and
complete-service constructions; no new enumeration or Lean
verification is claimed.

## 48. A single-deficit lower forces a small complete-deficit hull

Keep precisely the same-source hypotheses of Section 44. Original
ternary height is two; the retained family is 5-free, includes the
bought root $S$, and leaves the complete integer hole $H$.
With inactive sources omitted, assume

$$
H\subseteq T_2\cap T_5\cap T_8,\qquad
E_j=H\setminus T_j\ (j=3,6),\qquad
E=E_3\cup E_6\subseteq C_\ell=[\eta_\ell]_n,\quad n>1,
\tag{SC227}
$$

where $\ell$ is an actual lower in $L_0$. Other lower sources
may meet $H$. No uniqueness assumption on $\ell$ is added.
Write $v_a=|V_a|$, so $N_3=2+v_1+v_2$, $v_2\le v_1$, and
$v_1\ge1$ because of this actual lower. The exact count remains
$|\mathcal F_0|=K-N_3-z$, $z\ge0$.

Both $E_3$ and $E_6$ are nonempty. Otherwise one inner color and
the three outer colors would be four complete top colors, contrary
to SC194. Let $N$ be a common odd, 5-free period of the retained
family and every displayed output. Choose $w\in E$ and define
the complete congruence hull by

$$
\Gamma=\gcd\bigl(N,\{x-w:x\in E\bmod N\}\bigr),
\qquad n\mid\Gamma.
\tag{SC228}
$$

Reuse the existing congruence-hull equivalence: for $e\mid N$,
$E\subseteq[w]_e$ exactly when $e\mid\Gamma$.

### Every nonunit enclosure requires a different actual outer color

Take any nonunit divisor $e$ of $\Gamma$ and put $B=[w]_e$.
This is an enclosure of both deficits, even if it has not yet
been identified with an actual source. Repeat Section 44's
four-menu construction with $B$ in place of $C_\ell$:
the three outer menus and $B\cup T_k$, where one inner color
$j$ is omitted and $k$ is the other, all cover $H$.

At distinct nonzero fresh roots, the top patches use labels $5q$
for their actual output moduli $q$, while $B$ uses $5e$.
The only possible collision is with the unique active safe top
of output modulus $e$. If it is absent, there is no collision;
if its color is inner, omit that color. Either case gives cost
at most $2+v_2<N_3+z$, contradicting EB1. Thus this top exists
in an outer color $c_e$.

Delete that top's patch from its assigned root and put the omitted
inner color $j$ there. Let

$$
D_e=H\setminus
\bigcup_{\substack{v\text{ top of color }c_e\\v\ne t_e}}C_v.
$$

Every safe top is used at most once, except that $t_e$ is deleted;
the enclosure is used once. The patch costs at most $1+v_2$.
Its only uncovered part is the designated fresh-root restriction
of $D_e\cap E_j$. The complete liability, including all other
same-color service, is the one used in Section 44. If it were
empty, the patch would be paid. Applying this for both inner
colors forces

$$
D_e\cap E_3\ne\varnothing,\qquad
D_e\cap E_6\ne\varnothing,\qquad
C_{t_e}=B=[w]_e.
\tag{SC229}
$$

For the last equality, $D_e\subseteq C_{t_e}$ because its outer
color covers $H$. Either witness is also in $E\subseteq B$.
Two APs of the same numerical modulus $e$ that meet are equal.
The original actual lower is used for the count reserve $v_1\ge1$;
there was no assumption that the virtual enclosure was already
an independently available source. Since $e\mid N$, its label
is odd and 5-free throughout this argument.

If distinct divisors $e,f>1$ of $\Gamma$ had the same outer
color, the union defining $D_e$ would still contain $C_{t_f}$.
But $C_{t_f}$ contains all of $E$, contradicting SC229. Hence

$$
e\longmapsto c_e\text{ is injective on }
\{e>1:e\mid\Gamma\},\qquad \tau(\Gamma)\le4.
\tag{SC230}
$$

This applies to incomparable divisors as well as to comparable
ones. It does not combine the two liability witnesses into one.

### The original inventory pays a small packet at the deficient root

NF66 and the existing $P\ge23$ bound give
$N_3\ge P-1+c_2\ge23$: the original pure $9$ contributes
one to $c_2$. Therefore

$$
23\le2+v_1+v_2\le2+2v_1,
\qquad v_1\ge11.
\tag{SC231}
$$

For any enclosure $B$ above, fix either omitted inner color $j$.
After deleting its forced outer partner and transferring $T_j$,
the only remaining responsibility is

$$
[r_e]_5\cap D_e\cap E_j,
\qquad c_{\rm base}\le1+v_2.
\tag{SC232}
$$

Suppose a packet of $q$ distinct 5-bearing APs covers a 5-free
periodic enclosure of $D_e\cap E_j$ outside $S$. Move the whole packet one fresh
5-digit deeper at root $r_e$. Explicitly, a class becomes

$$
[a]_{5^h}\cap[\beta]_s
\longmapsto
[r_e+5a]_{5^{h+1}}\cap[\beta]_s,
\qquad (s,5)=1,\quad h\ge1.
\tag{SC233}
$$

This keeps every 5-free phase fixed. To verify coverage, take
a residual point $x$ on root $r_e$ and let $5^d$ be the largest
5-depth in the packet. Use CRT to choose an auxiliary $y$ with
$y\equiv(x-r_e)/5\pmod{5^d}$ and $y\equiv x$ modulo a
common 5-free period of the enclosure, $S$, and all packet
conditions. It belongs to the same enclosure outside $S$, so
some original packet class covers $y$; its shifted class covers
$x$. Integer division alone is not used to transport the 5-free
coordinates.

All shifted labels have 5-depth at least two. The menu labels
have depth one and retained labels depth zero, so no collision
is introduced. Whenever $q\le v_1$,

$$
c\le1+v_2+q\le N_3-1.
\tag{SC234}
$$

The transferred inner menu already covers the entire part of
$D_e$ outside $E_j$. Thus the packet pays the complete remaining
liability, not just a chosen trace of the deleted top.

Two existing packets apply immediately:

| Enclosure of the residual | Existing complete packet | Cost $q$ |
|---|---|---:|
| $[w]_m\setminus S$, $(m,15)=1$, $m$ composite | SC136 | $9$ |
| $[w]_{3p}$, $p>5$ prime | SC137 | $11$ |

Both fit SC231. Consequently $\Gamma$ has no composite 3-free
part and no divisor $3p$ for a prime $p>5$. Together with SC230,
this leaves only

$$
\Gamma\in\{3,9,27\}\cup\{p:p>5\text{ prime}\}.
\tag{SC235}
$$

### A fifteen-class complete-prefix packet excludes 27

Suppose $E\subseteq[\eta]_{27}$, choosing $0\le\eta<27$.
Instantiate the existing complete-prefix construction with three
5-levels. Put $w_h=5^h-1$, including $w_0=0$, and take

$$
\begin{aligned}
A_{h,j}&=[w_{h-1}+j5^{h-1}]_{5^h}\cap[\eta]_{3^j}
&& (1\le h\le3,\ 0\le j\le3),\\
B_h&=[w_h]_{5^h}\cap[\eta+27(h-1)]_{81}
&& (1\le h\le3).
\end{aligned}
\tag{SC236}
$$

The modulus-one condition for $j=0$ is void. The fifteen
numerical labels are exactly

$$
\{5^h3^j:1\le h\le3,\ 0\le j\le4\}.
\tag{SC237}
$$

They are pairwise distinct. A point of $[\eta]_{27}$ whose
first non-4 digit among its first three 5-digits is $j$ at
depth $h$ is covered by $A_{h,j}$. If all three digits are
4, its residue modulo $81$ is one of $\eta,\eta+27,\eta+54$,
so one of $B_1,B_2,B_3$ covers it. This covers the entire AP
and every higher lift, with no finite enumeration.

For payment, SC229 forces an actual top of output modulus $27$,
whose original label is $9\cdot125$. Divisor closure supplies
the four $P$-free original height-two labels $9,45,225,1125$.
Use the existing height-two support bound $P\ge29$ from Section
46 and SC211. Then

$$
c_2\ge4,\qquad N_3\ge P+c_2\ge33,\qquad v_1\ge16.
\tag{SC238}
$$

Apply SC233 to the fifteen-class packet at the deficient root
for enclosure $[\eta]_{27}$. It is fresh against every base
menu and gives $c\le v_2+16\le N_3-2$, a strict descent.
This payment uses the existing stronger original support bound;
it needs no special reuse of first-depth partner labels or
assumption about the output-81 source.

### Remaining complete-deficit hulls and their actual partners

The combined conclusion is

$$
n\mid\Gamma,\qquad
\Gamma\in\{3,9\}\cup\{p:p>5\text{ prime}\}.
\tag{SC239}
$$

For every nonunit divisor of this hull, its actual outer partner
and both complete-liability witnesses are still required by
SC229. The possibilities for the original identical-output pair
are therefore:

| Actual lower output $n$ | Possible complete union hull $\Gamma$ | Original lower and top labels |
|---|---|---|
| $3$ | $3$ or $9$ | $15,45$ |
| $9$ | $9$ | $75,225$ |
| prime $p>5$ | $p$ | $3p,9p$ |

If $\Gamma=9$, the forced top outputs $[w]_3$ and $[w]_9$
have different outer colors and compatible actual phases.

In the prime case there is a further restriction on each complete
inner deficit:

$$
\Gamma(E_3)=\Gamma(E_6)=p.
\tag{SC240}
$$

Each individual hull is divisible by $p$. If one were larger,
it would have either a composite 3-free divisor or a divisor
$3p$. Starting with the already forced union partner at $p$,
transfer that particular inner color $j$. Its complete residual
$D_p\cap E_j$ lies in the individual enclosure. Shift SC136's
nine-class or SC137's eleven-class packet there and use SC234,
contradicting EB1. No separate partner for an individual hull
is needed.

These statements concern complete congruence hulls. They do not
say a deficit equals its enclosing AP, make its private witnesses
coincide, or pay the original ancestor liability $P_{\chi(n)}$.
Section 45's distinction between that full original region and
the selected source images remains necessary. In particular,
SC139 prevents covering the full flat-prime envelope outside $S$
with only its one-prime palette; actual smaller deficits may
still admit repairs. The three displayed hull alternatives, the
forcing of SC227 in a general whole cover, and arbitrary original
ternary height remain unresolved. These are ordinary constructive
deductions using existing enclosure, prefix and inventory
results, without a new Lean verification or a resolution of #7.

## 49. Small hulls constrain the complete residuals and their common outer responsibility

Keep the complete same-source hypotheses SC227 and the surviving
hull alternatives SC239. For each nonunit $e\mid\Gamma$, retain
the actual outer partner $t_e$, its color $c_e$, and the complete
post-deletion color responsibility $D_e$ from SC229. Write

$$
R_{e,j}=D_e\cap E_j,\qquad j\in\{3,6\}.
\tag{SC241}
$$

Every such set is nonempty. For any nonempty periodic set $X$ below,
$\Gamma_N(X)$ denotes its complete congruence hull in the same
common odd, 5-free period $N$. No hull is computed from selected
private witnesses.

### The ternary alternatives have a fifteen-class repair reserve

If $\Gamma\in\{3,9\}$, SC229 supplies the actual outer top
of output modulus 3, whose original label is 45. The original
$P$-free height-two inventory therefore contains both 9 and 45.
The existing bounds $P\ge29$ and SC211 give

$$
c_2\ge2,\qquad N_3\ge P+c_2\ge31,
\qquad v_1\ge15.
\tag{SC242}
$$

The last inequality uses $N_3=2+v_1+v_2\le2+2v_1$.
When $\Gamma=9$, the additional actual partner of output modulus
9 supplies the original label 225, so $c_2\ge3$ and
$N_3\ge32$. Thus the same reserve remains valid. These are
actual original numerical labels; no independent supplier phases
are chosen.

Consequently SC233 can shift the fifteen-class complete-27 packet
SC236 into any one deficient fresh root of a base construction
costing at most $1+v_2$. The total costs at most
$1+v_2+15\le N_3-1$. The nine-class composite enclosure packet
SC136 and the eleven-class complete-$3p$ packet SC137 are also
affordable. Shifted labels have fresh 5-depth at least two, whereas
base menu labels have depth one and retained labels depth zero.

### Complete partner residuals cannot acquire deeper hulls

The resulting restrictions are

$$
\begin{array}{c|c|c}
\Gamma & e & \Gamma_N(R_{e,j})\\\hline
3 & 3 & \text{one of }3,9\\
9 & 3\text{ or }9 & 9\\
p>5\text{ prime} & p & p.
\end{array}
\tag{SC243}
$$

For the first two rows, $R_{e,j}\subseteq E$ makes its hull
divisible by $\Gamma$. If the residual hull has a prime factor
$p>5$, the entire residual lies in one class modulo $3p$.
If it is divisible by 27, the entire residual lies in one class
modulo 27. Apply the respective eleven- or fifteen-class packet
at the exact deficient root SC232. Each produces a strict descent
by SC242. Since $N$ is odd and 5-free, only the displayed hulls
remain.

For the prime row, the residual hull is divisible by $p$. Any
larger hull has either a composite 3-free divisor or a divisor
$3p$. The nine- or eleven-class packet then pays the complete
residual using the original reserve $v_1\ge11$ in SC231. This
extends the SC240 enclosure argument to $D_p\cap E_j$ itself;
it does not assume the stronger reserve SC242 for that branch.

The two complete inner deficits obey the same hull restrictions:

$$
\begin{aligned}
\Gamma=3&\ \Longrightarrow\
  \Gamma_N(E_j)\in\{3,9\},\\
\Gamma=9&\ \Longrightarrow\
  \Gamma_N(E_j)=9.
\end{aligned}
\tag{SC244}
$$

Indeed $R_{3,j}\subseteq E_j\subseteq E$ gives
$\Gamma\mid\Gamma_N(E_j)\mid\Gamma_N(R_{3,j})$.
The prime case for $E_j$ is already SC240. None of these
statements identifies a residual or deficit with its full enclosing
AP, and no new actual partner at a residual-hull divisor is assumed.

### Two different outer partners have a common complete responsibility

Assume now $\Gamma=9$. Let $a=c_3$, $b=c_9$, and let $c$
be the third outer color. SC230 gives $a\ne b$. Both actual
partner outputs

$$
C_{t_3}=[w]_3,\qquad C_{t_9}=[w]_9
$$

contain all of $E$. Partition all actual safe top suppliers into
four menus:

$$
\begin{aligned}
\mathcal M_1&=T_3\cup C_{t_3},\\
\mathcal M_2&=T_6\cup C_{t_9},\\
\mathcal M_3&=
 \bigcup_{\substack{v\text{ of color }a\\v\ne t_3}}C_v
 \ \cup\!
 \bigcup_{\substack{v\text{ of color }b\\v\ne t_9}}C_v,\\
\mathcal M_4&=T_c.
\end{aligned}
\tag{SC245}
$$

Removing a partner means removing its supplier, while retaining
all other same-color service. Each top supplier occurs once.
The first two menus cover $H$ because their added partners
contain the respective complete inner deficits. The fourth covers
$H$ by SC227. The complete part missed by the third menu is
exactly

$$
R_*=H\setminus\mathcal M_3=D_3\cap D_9.
\tag{SC246}
$$

Assign the four menus to distinct nonzero fresh 5-roots and add
$[0]_5$. Top output moduli are globally distinct, so all added
labels $5q$ are distinct. Every retained label is 5-free. The
base patch costs at most $1+v_2$, and its only remaining hole
is the third menu's root restriction of the entire $R_*$.
An empty $R_*$ would therefore contradict EB1 by a strict
class-count descent.

Furthermore, $D_3\subseteq C_{t_3}$ and
$D_9\subseteq C_{t_9}$ imply $R_*\subseteq[w]_9$.
The same eleven- and fifteen-class packet argument used for SC243
excludes any additional prime factor or additional ternary depth
in its hull. Thus

$$
\boxed{D_3\cap D_9\ne\varnothing,\qquad
       \Gamma_N(D_3\cap D_9)=9.}
\tag{SC247}
$$

The separate incidences $D_e\cap E_j\ne\varnothing$ in
SC229 do not by themselves imply this common outer responsibility.
SC245 supplies a new whole-hole comparison proving it. No point
common to $R_*,E_3,E_6$ is asserted.

If the additional condition $H\cap L_2=\varnothing$ holds,
every $x\in R_*$ gives simultaneous original-private points
for labels 45 and 225 at old words $a$ and $b$, with the same
complete original 3-free coordinate. The owner check is the one
in SC209: height-zero owners miss $H$, height-one owners at
these outer words would lie in $L_2$, and $D_3,D_9$ exclude
all other top owners in the respective colors. This assertion
requires no uniqueness of the inner lower. Without the displayed
condition, the two points are not claimed private.

The complete original private regions of the ancestors 5 and 25
remain separate obligations. SC247 does not cover either one,
and neither the 3 nor the 9 hull alternative is excluded. These
are ordinary deductions using existing complete packets and
inventory bounds, without new enumeration or Lean verification.

## 50. The fresh height-two transport charges the two actual mixed layers

These inventory constraints apply to the same original EB1 whole
cover with ternary height $A=2$, without the single-deficit premise
SC227. For an actual support prime $p\ge23$, write

$$
\begin{aligned}
t_p&=\#\{d\in D:3p\mid d\},\\
u_p&=\#\{d\in D:p\mid d,\ v_3(d)=1\},\\
v_p&=\#\{d\in D:p\mid d,\ v_3(d)=2\}.
\end{aligned}
\tag{SC248}
$$

Thus $t_p=u_p+v_p$. Here $v_p$ denotes this cardinality, not
a prime valuation. Every count uses the original numerical labels
and their actual phases.

The all-root injection inequality
[Report 385 NF104](385-private-congruence-hulls-and-crossed-modulus-closure.md#65-all-root-injections-charge-every-deleted-mixed-original)
gives

$$
\boxed{t_p\ge p-8,\qquad
       v_p>0\ \Longrightarrow\ t_p\ge p-7.}
\tag{SC249}
$$

### Apply the existing transport at its fresh third ternary level

Take the actual pure 3 and 9 guards and use ternary prefix height
three. The 15 live prefixes modulo 27 lie in the two first-3
branches in groups of sizes six and nine. No original label has
ternary height three, so the collision reservations at this depth
are empty. NF79 already gives $t_p\ge p-15>0$. Consequently
NF104 forbids a full injection of these live prefixes into all
$p$ first roots, avoiding the actual mixed forbidden lists.
The pure-$p$ root zero is allowed: NF104 pays the strict reduction
by deleting mixed originals. No new common-witness map or generic
matching theorem is needed.

The existing Hall obstruction supplies a nonempty live-prefix set
$I$, of size $k\le15$, and first-$p$ roots $W$ forbidden at
every prefix of $I$, with

$$
|W|\ge p-k+1.
\tag{SC250}
$$

If $I$ lies in one first-3 branch, $k\le9$. Distinct roots
of $W$ require different original mixed labels, giving
$t_p\ge|W|\ge p-8$. If $I$ meets both first-3 branches,
each root of $W$ requires at least two originals, because an
original has only one first-3 root. Thus

$$
t_p\ge2|W|\ge2(p-14)\ge p-8.
\tag{SC251}
$$

This proves the first part of SC249. No mixed original is charged
once for every deeper prefix that it forbids.

### A height-two mixed original cannot pay a whole three-word branch alone

Assume $v_p>0$. In the one-branch case, $k\le7$ already gives
$t_p\ge p-6$. If $k=8$ or $9$, the prefixes of $I$ meet
all three old modulo-9 words of that branch. An actual mixed
original of ternary height two forbids only one of these old words;
an original of height one can forbid the whole branch.

At each root of $W$, either there is a height-one supplier or
there must be at least three height-two suppliers, one for each
old word. Suppliers at different first-$p$ roots are disjoint
original labels. Even crediting all the original mixed inventory
therefore gives

$$
u_p+\frac{v_p}{3}\ge|W|,
\qquad
 t_p=u_p+v_p\ge |W|+\left\lceil\frac{2v_p}{3}\right\rceil\ge |W|+1.
\tag{SC252}
$$

The last step uses integrality and $v_p\ge1$. Hence
$t_p\ge p-7$. The same weighted charge is valid for $k=7$,
although it is unnecessary for this lower bound. In the two-branch
case, $p\ge23$ gives
$2(p-14)\ge p-7$. This proves the second part of SC249.
Higher $p$ digits and all other coordinates remain those in the
existing transport; none allows a height-two original to forbid
a different old modulo-9 word.

For the largest support prime $P\ge47$, the existing GHA10
consequence supplies $9P^{H_P}\in D$, so $v_P>0$.
Initial-segment support gives at least 14 odd support primes, and
NF83 gives $c_1\ge s-5\ge9$ for the $P$-free height-one
inventory. Thus the same original counts satisfy

$$
P\ge47\ \Longrightarrow\
 c_1+t_P\ge P+2,\qquad N_3\ge P+c_2+2.
\tag{SC253}
$$

This constrains the joint $c_1,c_2,t_P$ inventory. It does not
replace the existing NF82 bound by a uniformly stronger total
$N_3$ bound; neither estimate supplies an upper bound on the
inventory.

### The first-root equality has an actual phase restriction

A separate consequence retains information lost by the scalar
counts. Let $p\ge17$ be an actual support prime and suppose

$$
c_1+t_p=p,\qquad t_p\ge3,
\tag{SC254}
$$

where $c_1$ is now the $p$-free height-one inventory. Use the
actual NF66 collision set $T$ and $D_0=(\mathbb Z/p\mathbb Z)
\setminus T$, and let $d_0=|D_0|$. Then
$d_0\ge p-c_1=t_p\ge3$. The NF66 graph has two live first-3
roots. A deficient set containing both would require
$t_p\ge2(d_0-1)\ge2t_p-2$, contrary to $t_p\ge3$.
Its obstruction is therefore a singleton root $b$.

The singleton counting chain forces equality everywhere:

$$
t_p\ge |D_0\cap F_b|\ge d_0\ge t_p.
\tag{SC255}
$$

Consequently $|T|=c_1$, and all $t_p$ mixed originals have
pairwise different first-$p$ roots, exactly $D_0$, and the same
first-3 root $b$. This is a statement about all original mixed
suppliers, not just those used in a selected Hall witness.

At fresh ternary height three, let $\ell_{\rm opp}$ be the
number of live prefixes in the other first-3 branch. It is six
or nine. Every root of $T$ is allowed at every live prefix,
whereas every root of $D_0$ is allowed at every opposite-branch
prefix. If
$c_1+\min(t_p,\ell_{\rm opp})\ge15$, first assign as many
opposite prefixes as needed to distinct roots of $D_0$, and
assign the remaining prefixes to distinct roots of $T$. This
would be an all-root injection forbidden by NF104. Therefore

$$
c_1+\min(t_p,\ell_{\rm opp})\le14,
\qquad
c_1\le14-\ell_{\rm opp}\in\{5,8\}.
\tag{SC256}
$$

For the second implication, $t_p\le\ell_{\rm opp}$ would
make the first left side equal $p\ge17$, a contradiction.
Unlike NF75's pure-root deletion version, this application may
use the entire $T$, including zero, because $t_p>0$.
The equality restriction is useful also for smaller support primes;
SC253 already excludes the equality when $p=P\ge47$.

All arguments are consumers of the existing original-cover
transport, Hall charge and forced-label results. They use no
independently optimized source, new enumeration or Lean
verification, and leave arbitrary-height noncoverage unresolved.

## 51. The full height-two first-root inventory equality is impossible

Keep one original EB1 whole cover of ternary height two. Let $P$ be
its largest support prime, $G=H_P$, and define

$$
\begin{aligned}
c_1&=\#\{d\in D:P\nmid d,\ v_3(d)=1\},\\
c_2&=\#\{d\in D:P\nmid d,\ v_3(d)=2\},\\
u&=\#\{d\in D:P\mid d,\ v_3(d)=1\},\\
v&=\#\{d\in D:P\mid d,\ v_3(d)=2\},\qquad t=u+v.
\end{aligned}
$$

The existing height-two support restriction gives $P\ge29$ and
at least nine support primes. No single-deficit or cofactor-profile
hypothesis is imposed. The complete inventory satisfies

$$
\boxed{c_1+t\ge P+1,\qquad N_3\ge P+c_2+1.}
\tag{SC257}
$$

The $P\ge47$ branch retains the stronger SC253. The new step is
to exclude the equality throughout the remaining support range,
using the original highest $P$-levels and actual phase structure.

### The next-to-last prime level has an actual height-two label

First reuse the qualified profile bound
[Report 385 GHA9](385-private-congruence-hulls-and-crossed-modulus-closure.md#250-pure-power-guards-sharpen-the-single-prime-absorption-and-full-height-tail-bounds).
For any actual support prime $q\ge17$, write $G_q=H_q$.
GHA10 supplies the original label $3q^{G_q}$. If $G_q\ge2$
and $9q^{G_q-1}$ were absent, divisor closure and the full-height
label would force the two profile heights
$h_{G_q-1}=h_{G_q}=1$. Apply GHA9 with its base prime 3,
other prime $q$, original ternary height 2, and $k=G_q-1$.
It would give

$$
q\le\max\{3^{\max(2,1+1+1)-2}\cdot5,\ 3^2\}
 =15,
$$

a contradiction. Therefore

$$
q\ge17,\ G_q\ge2\ \Longrightarrow\ 9q^{G_q-1}\in D.
\tag{SC258}
$$

For $q=P$, all $G-1$ distinct labels
$9P,\ldots,9P^{G-1}$ are then present. If $G=1$, the empty
list gives the same bound. Hence

$$
v\ge G-1,\qquad G\le v+1.
\tag{SC259}
$$

This does not prescribe any phase or infer a product of separately
forced labels.

There is also an exact original-label counting bound. Every
height-one mixed label is uniquely $3P^a w$ with
$1\le a\le G$ and $(w,3P)=1$. Divisor closure supplies its
original label $3w$, counted in $c_1$. The map
$3P^a w\mapsto(a,3w)$ is injective, including $w=1$ and all
higher $P$-tails. Thus

$$
u\le c_1G.
\tag{SC260}
$$

### Equality forces a small combined shallow and top inventory

Suppose $c_1+t=P$. NF79 gives $t\ge P-15\ge14$, and
NF83 with at least nine support primes gives $c_1\ge4$.
SC254--SC255 therefore apply: the original mixed labels have
pairwise different first-$P$ roots, exactly the complement $D_0$
of the collision set $T$, and they all have one first-3 root $b$.
Moreover $|T|=c_1$.

Use the same fresh height-three all-root graph as SC250. A live
prefix in the opposite first-3 branch has every $P$-root as a
neighbor, because no mixed original has that first-3 root. A
Hall-deficient set $I$ therefore cannot contain such a prefix:
its whole left side has only 15 vertices, fewer than $P$.
It must lie in branch $b$, which has at most nine live prefixes.

If $I$ lies in a single old modulo-9 word, then $|I|\le3$,
whereas all $c_1\ge4$ roots of $T$ are neighbors. This also
cannot be deficient. Thus $I$ meets at least two old words.
At the unique first-$P$ root of any height-two mixed label, that
label forbids at most one of those words; some other member of
$I$ is allowed there. Every one of the $v$ height-two roots is
therefore a neighbor. At a height-one mixed root the unique label
forbids the entire branch, so it supplies no neighbor of $I$.
The root sets are disjoint and exhaust all $P$ roots, giving the
exact neighborhood and its necessary bound

$$
|\mathcal N(I)|=c_1+v<|I|\le9,
\qquad c_1+v\le8.
\tag{SC261}
$$

This uses the unique actual mixed-root structure forced by the
assumed equality. It is not a bound imposed on general
nonequality configurations.

### Complete prime heights make that equality numerically impossible

Combine the same inventory constraints SC259--SC261:

$$
\begin{aligned}
P=c_1+u+v
 &\le c_1+c_1G+v\\
 &\le c_1(v+2)+v\\
 &\le c_1(9-c_1)+8
 \le28.
\end{aligned}
\tag{SC262}
$$

For the last inequality, the integer $c_1$ satisfies
$(c_1-4)(c_1-5)\ge0$, so $c_1(9-c_1)\le20$.
The contradiction with $P\ge29$ excludes every instance of the
equality, not just the cases with $P\ge47$.

Finally NF66 says $c_1\ge P-1$ or $c_1+t\ge P$.
In its first case NF79 gives
$c_1+t\ge(P-1)+(P-15)>P$. In the second case SC262 excludes
equality. Integrality proves $c_1+t\ge P+1$, and adding the
disjoint $c_2$ inventory proves SC257.

The result strengthens the same-source joint inventory restriction.
It does not provide an upper bound on $N_3$ or eliminate the
whole height-two branch. The proof reuses the existing profile
transport and all-root Hall interface, with no new enumeration or
Lean verification.

## 52. The common prefix source bounds complete original private hulls

The small output hulls can be transported back to the original
private regions, provided the source images are actually private.
The required transport preserves congruence depth without requiring
an affine source map.

Keep original ternary height two and write
$Q=9\cdot5^BM$, $N_0=3^BM$, with $(M,15)=1$.
Use the one fixed source SC2 with safe old word $u$:

$$
F_u(x)\equiv u\pmod9,\qquad
F_u(x)\equiv\theta_B(x\bmod3^B)\pmod{5^B},\qquad
F_u(x)\equiv x\pmod M.
$$

For a nonempty set $X$ in the output carrier, let
$\Gamma_{N_0}(X)=3^h m$, where $0\le h\le B$ and $m\mid M$.
Then its image has the exact original-carrier hull

$$
\boxed{\Gamma_Q(F_u(X))
       =9\cdot5^h m=9\chi(\Gamma_{N_0}(X)).}
\tag{SC263}
$$

At the 3-coordinate, $h$ is the largest level at which every
point of $X$ has the same prefix. Compatibility of the maps
$\theta_b$ makes their images agree modulo $5^h$. If $h<B$,
two points have different next 3-prefixes, and injectivity of
$\theta_{h+1}$ makes the corresponding next 5-prefixes different.
Thus the exact common 5-depth is $h$. The endpoint $h=B$ is
limited by the original carrier itself. Every prime coordinate
in $M$ is copied literally, and the old ternary coordinate is
fixed modulo 9. This proves SC263 prime by prime. It neither
identifies the image with an AP nor treats $\theta$ as affine.

All output moduli divide $N_0$, and $B\ge1$ makes the bought
modulo-3 root periodic there too. Thus the complete residuals in
Sections 48--49 have $N_0$ as a period. Their previously computed
hulls are unchanged: the hull of a complete periodic integer set
is the gcd of all its actual differences from one point, including
its periods. If such an image is contained in the complete original
private region $P_d$, then

$$
d\mid\Gamma_Q(P_d)\mid9\chi(\Gamma_{N_0}(X)).
\tag{SC264}
$$

The second divisibility has this direction because a congruence
holding throughout $P_d$ also holds on its subset $F_u(X)$.
It does not assert that this subset accounts for all original
private points.

### Outer private hulls require no unique inner lower

Keep SC227 and impose only

$$
H\cap L_2=\varnothing.
\tag{SC265}
$$

For every partner $t_e$ and inner color $j$, the whole source
image $F_{c_e}(R_{e,j})$ lies in $P_{9\chi(e)}$. This is the
SC209 owner check: height-zero owners miss $H$, height-one
owners at the outer word would have outputs in $L_2$, and $D_e$
excludes all other top owners of that color. Uniqueness of the
active inner lower is not needed for this assertion.

If $\Gamma=9$, apply this check simultaneously to the complete
$R_*=D_3\cap D_9$ of SC247, whose hull is exactly 9. Both
outer images have hull 225, and SC264 gives

$$
\Gamma_Q(P_{225})=225,\qquad
\Gamma_Q(P_{45})\in\{45,225\}.
\tag{SC266}
$$

If $\Gamma=p>5$ is prime, SC243 gives
$\Gamma_{N_0}(R_{p,j})=p$. Its image hull is $9p$, so

$$
\Gamma_Q(P_{9p})=9p.
\tag{SC267}
$$

If $\Gamma=3$, the residual hulls belong to $\{3,9\}$.
The same argument gives $\Gamma_Q(P_{45})\in\{45,225\}$,
with equality 45 if either residual has hull 3. Any displayed
value not dividing $Q$ is excluded; in particular $B=1$ rules
out 225.

### A unique inner lower adds the two different old words

Now impose all of SC208: in addition to SC265, the designated
$\ell$ is the only active source in $L_0$. Its actual output
modulus is $n$. The same owner check gives

$$
F_3(R_{n,3})\cup F_6(R_{n,6})\subseteq P_{3\chi(n)}.
\tag{SC268}
$$

Both sets are nonempty, and their old modulo-9 words are 3 and 6.
The complete private region therefore has ternary hull depth
exactly one. The witnesses need not have the same cofactor
coordinate or arise from a common point of the two residuals.

Combining SC264 with the residual hulls in SC243 gives

$$
\begin{array}{c|c|c}
\text{complete union hull }\Gamma&\text{actual lower }n&
 \text{complete original lower-private hull}\\\hline
9&9&\Gamma_Q(P_{75})=75\\
9&3&\Gamma_Q(P_{15})\in\{15,75\}\\
3&3&\Gamma_Q(P_{15})\in\{15,75\}\\
p>5\text{ prime}&p&\Gamma_Q(P_{3p})=3p.
\end{array}
\tag{SC269}
$$

For the first two rows, each image hull is 225; reducing its
ternary depth to one and retaining the original label gives the
listed possibilities. For the third row, an image hull is either
45 or 225, so the same conclusion holds, with equality 15 if
either residual has hull 3. For the last row each image hull is
$9p$, and the two old words remove its extra factor 3. Again
$B=1$ rules out the value 75.

### In the prime branch the complete parent hull is also flat

In the last row of SC269, let the common original $p$-phase of
$3p,9p$ be $a$ and the original pure-$p$ phase be $a_p\ne a$,
choosing both digit representatives in $\{0,\ldots,p-1\}$.
Reuse the original private-reset map
[Report 357 PT6](../../321-384/357-original-private-swaps-and-prime-reset-transport.md):
reset the first $p$ digit of every point of $P_{3p}$ from $a$
to $a_p$, keeping the complete higher $p$ tail and every other
coordinate. The image lies in $P_p$. Indeed, all $p$-free
originals remain false, while every other $p$-bearing original
avoids the root occupied by $A_p$, by comparable-original
disjointness.

On $P_{3p}$ the old first digit is fixed, so this reset is one
constant CRT translation: it adds $a_p-a$ modulo $p^{H_p}$ and
zero modulo $Q/p^{H_p}$. Its image therefore has the same
complete hull $3p$, even when the higher tail varies. By subset
inclusion and the original label,

$$
p\mid\Gamma_Q(P_p)\mid3p.
$$

SC206 excludes $3p\mid\Gamma_Q(P_p)$ for this original
crowded phase group. Hence the three complete private hulls are

$$
\boxed{\Gamma_Q(P_p)=p,\qquad
       \Gamma_Q(P_{3p})=3p,\qquad
       \Gamma_Q(P_{9p})=9p.}
\tag{SC270}
$$

This conclusion retains SC208. It asserts complete congruence
hulls, not equality of any private region with its original AP.
The reciprocal-hull swap for $3p,9p$ still lacks
$9p\mid\Gamma_Q(P_{3p})$; the flat hull does not pay that move.
Likewise SC266 supplies no extra descendant whose deletion would
make a swap of 45 and 225 strictly improving. The complete
ancestor liabilities and the forcing of SC265 or SC208 remain
open. These deductions use the fixed common source and existing
private-region interfaces, without enumeration or Lean verification.

## 53. A complete output-root transport forces service outside the paired prime group

Keep SC227 in its prime branch: the actual inner lower has output
$C_\ell=[a]_p$, where $p>5$ is prime. Its original label is
$3p$, and its unique outer partner has original label $9p$ and
old word $c\in\{2,5,8\}$. Both originals have first-$p$ phase
$a$, while the original pure-$p$ class has phase $a_p\ne a$.
Assume that the complete original group at phase $a$ is

$$
J_a=\{3p,9p\}.
\tag{SC271}
$$

All repeated prime heights and other cofactors remain allowed
outside this group. The construction below changes explicitly
specified output phases. It does not identify the resulting mixed
menus with simultaneous pullbacks of one modified original cover.

For this section, let every $T_u$ include all actual safe top
outputs with nonempty pullback through the fixed tree $\theta$,
including outputs disjoint from the old $H$. Restoring such outputs
does not change $E_j=H\setminus T_j$, and the total number of
top suppliers is still at most $v_2$, with globally distinct
numerical output labels. Keeping these outputs is necessary when
classifying original owners at points outside the old hole.

### The two other outer colors have no $p$-bearing tops

Let $X_p$ be the complete cofactor region avoiding all original
$p$-free classes. At first-$p$ root $a$, every point with cofactor
in $X_p$ must have an owner in $J_a$. SC271 restricts its
ternary coordinate to first root zero or old word $c$. The
original pure classes $[1]_3$ and $[0]_9$ also miss $X_p$,
so its entire ternary projection satisfies

$$
\operatorname{pr}_9(X_p)\subseteq\{3,6,c\}.
\tag{SC272}
$$

Every original $p$-bearing class has a private point by EB1
irredundancy. Its full cofactor lies in $X_p$; equivalently the
existing prime-private reset into $P_p$ preserves that cofactor.
Thus any $p$-bearing original top has old word in $\{3,6,c\}$.
All tops in either of the other two outer colors are $p$-free.
Their complete output unions are invariant under every permutation
of the first output $p$ digit. This conclusion uses the complete
group SC271, not only the two selected source traces.

### The transported whole hole has one exact additional liability

Fix any first-$p$ digit $b\ne a$. On the complete output carrier
$N_0=3^BM$, let $\phi_b$ interchange digits $a,b$, preserving
every higher $p$ digit and every other prime coordinate. Extend
sets by all integer lifts of the carrier. An AP whose modulus
contains $p$ has a fixed first digit; on that AP the map is a
constant CRT translation and preserves its numerical modulus.
An AP with $p$-free modulus is invariant.

Define the candidate retained family and inner menus by

$$
\begin{aligned}
\mathcal F_0'&=\phi_b(\mathcal F_0),&
H'&=\phi_b(H),\\
T_j'&=\phi_b(T_j)\quad(j=3,6),&
C_\ell'&=[b]_p.
\end{aligned}
\tag{SC273}
$$

Leave all three outer menus unchanged. The retained moduli remain
distinct and 5-free, $|\mathcal F_0'|=|\mathcal F_0|$, and the
bought modulo-3 root $S$ is fixed. The exact inner deficits are
$H'\setminus T_j'=\phi_b(E_j)\subseteq[b]_p$.
Both nonpartner outer menus still cover $H'$ by SC272.

For color $c$, service outside the two exchanged $p$ fibres is
unchanged, and the new $a$ fibre is covered by its partner
$t_p=[a]_p$. Thus the only new responsibility is the full fibre

$$
Z_b=\phi_b(H\cap[a]_p)\setminus T_c,
\qquad H'\subseteq T_c\ \Longleftrightarrow\ Z_b=\varnothing.
\tag{SC274}
$$

This tests the whole transported hole at that fibre, including
points outside the selected inner deficits.

### Vanishing of that liability gives a complete strict descent

Suppose $Z_b=\varnothing$. Assign $T_2,T_5,T_8$ and
$C_\ell'\cup T_k'$ to the four nonzero fresh 5-roots, where
$\{j,k\}=\{3,6\}$; add $[0]_5$. A supplier $[\eta]_q$
at fresh root $r$ gives $[r]_5\cap[\eta]_q$, of numerical
modulus $5q$. The only repeated label is $5p$, from the lower
and the outer partner.

Delete the partner patch and add the entire omitted inner menu
$T_j'$ at that same root. The deleted responsibility is

$$
D_c'=H'\setminus
 \bigcup_{\substack{t\text{ top of color }c\\t\ne t_p}}C_t
 \subseteq[a]_p.
$$

The inclusion follows from $H'\subseteq T_c$. In contrast,
$H'\setminus T_j'\subseteq[b]_p$. Since $b\ne a$, the
omitted inner menu covers all of $D_c'$. Every fresh-root menu
therefore covers the entire $H'$, and the transformed retained
family covers its complement.

Every top occurs once except the deleted partner; the lower occurs
once. Global top-label uniqueness removes all remaining duplicate
labels, and every new modulus is an odd nonunit divisible by 5,
fresh relative to $\mathcal F_0'$. The total count is

$$
|\mathcal F_0'\cup\mathcal B|
 \le K-N_3-z+(1+v_2)=K-1-v_1-z<K.
\tag{SC275}
$$

This is an explicit whole-cover construction with legal distinct
moduli. Its coverage and count do not require its mixed menus to
come from a common modified source. EB1 consequently forces

$$
\boxed{Z_b\ne\varnothing\quad\text{for every }b\ne a.}
\tag{SC276}
$$

The root $b=a_p$ is included: the construction acts on output
APs and leaves the original cover, including its pure-$p$ class,
available for the subsequent owner comparison.

### Every forced gap has an actual supplier of a restricted role

Now add only $H\cap L_2=\varnothing$. For each $b\ne a$,
choose $y\in Z_b$ and put $x=\phi_b(y)$. Then
$x\in H\cap[a]_p$ and $y$ has first-$p$ phase $b$. Apply
the unchanged original source map $F_c$ to $y$. Original whole
coverage supplies an owner. It cannot have ternary height two:
all tops of color $c$ with nonempty pullback were included in
$T_c$, while $y\notin T_c$.

The owner therefore has ternary height zero or height one at
the outer first-3 root 2. It must contain $p$. Otherwise its
membership is unchanged between $F_c(x)$ and $F_c(y)$:
a height-zero owner contradicts the convention that $H$ misses
every height-zero output, and a height-one outer owner contradicts
$H\cap L_2=\varnothing$. Its first-$p$ phase is $b$.
Different roots require different original labels. Hence

$$
\boxed{\begin{gathered}
\text{Each of the }p-1\text{ roots }b\ne a\text{ has an actual}\\
p\text{-bearing supplier of ternary height zero, or height one}\\
\text{at outer first-3 root }2.
\end{gathered}}
\tag{SC277}
$$

At $b=a_p$ the original pure-$p$ class supplies the required
role. Higher $p$ exponents and all other cofactors remain arbitrary.
Neither SC276 nor SC277 uses the unique-active-$L_0$ hypothesis.

These statements do not force a $b$ with $Z_b=\varnothing$ or
establish a contradiction among the supplier requirements. They
do not eliminate SC271 or the prime branch. If $|J_a|\ge3$, other
$p$-bearing tops can occur in the other outer colors, whose full
transported liabilities would also need payment. The result is an
ordinary phase-explicit construction using the existing private
reset and complete-menu interfaces, without new enumeration or
Lean verification.

## 54. The two inner deficits have a common point and a small common-overlap hull

Keep precisely SC227 and the surviving alternatives SC239. Define

$$
I=E_3\cap E_6=H\setminus(T_3\cup T_6).
\tag{SC278}
$$

Then $I$ is nonempty. For its complete congruence hull, choose
$x_0\in I$ and write $\Delta=\Gamma_N(I)$ in one common odd,
5-free period $N$. The phase anchor belongs to the intersection;
an arbitrary earlier point of $E_3\cup E_6$ need not have its
finer congruence phase.

### One root retains exactly the common inner deficit

Assign the four menus

$$
T_2,\qquad T_5,\qquad T_8,\qquad T_3\cup T_6
\tag{SC279}
$$

to four distinct nonzero fresh 5-roots, and add $[0]_5$.
Every actual safe top supplier occurs once. Its patch has the
unchanged output phase and numerical label $5n_t$; top-output
uniqueness makes these labels pairwise distinct. They differ from
5 because every $n_t>1$, and from every retained modulus because
those are 5-free.

The first three menus cover the whole $H$. At the fourth root,
the only remaining responsibility is the root restriction of the
entire $I$. Points outside $H$ retain their original
$\mathcal F_0$ service. The base cost is at most $1+v_2$.
If $I$ were empty, the resulting whole cover would have at most
$K-N_3-z+1+v_2=K-(1+v_1+z)<K$ classes. Hence EB1 forces
$I\ne\varnothing$.

### The existing packets bound its complete hull

Because $I\subseteq E_3\cup E_6$, its hull is divisible by
$\Gamma$. The exact remaining alternatives are

$$
\boxed{
\begin{aligned}
\Gamma=3&\ \Longrightarrow\ \Delta\in\{3,9\},\\
\Gamma=9&\ \Longrightarrow\ \Delta=9,\\
\Gamma=p>5\text{ prime}&\ \Longrightarrow\ \Delta=p.
\end{aligned}}
\tag{SC280}
$$

To prove them, shift a complete packet one 5-level deeper at the
deficient root by SC233. A packet of $q$ classes gives total cost
at most $1+v_2+q$, strictly below $N_3+z$ whenever $q\le v_1$.
The shifted labels have 5-depth at least two, whereas the base
labels have depth one and the retained labels depth zero. The
shift keeps all 5-free phases fixed and covers every integer lift
of the remaining liability.

For $\Gamma\in\{3,9\}$, SC242 already gives $v_1\ge15$.
A prime factor $p>5$ in $\Delta$ supplies the complete enclosure
$[x_0]_{3p}$, paid by SC137's eleven-class packet. A factor 27
supplies $[x_0]_{27}$, paid by SC236's fifteen-class packet.
Thus only the two displayed ternary possibilities remain. This
payment requires no actual top of output modulus 27.

For $\Gamma=p>5$, use $v_1\ge11$ from SC231. Any
$\Delta>p$ has either a composite 3-free divisor or the divisor
$3p$. The nine-class SC136 packet or eleven-class SC137 packet
then covers the complete corresponding enclosure outside $S$.
Since $I\subseteq H$ avoids $S$, this pays the whole remaining
responsibility and contradicts EB1.

For any nonunit divisor $d\mid\Delta$, the actual safe top
menus must contain a supplier of output modulus $d$. Otherwise,
one additional patch $[r]_5\cap[x_0]_d$ at the deficient root
is numerically fresh and covers all of $I$. Its total cost is
at most $2+v_2=N_3-v_1<N_3+z$. In particular,

$$
\Gamma=3,\ \Delta=9
\quad\Longrightarrow\quad
\text{an active safe top has output modulus }9.
\tag{SC281}
$$

This is numerical occupancy only. It supplies neither that top's
color nor equality of its actual phase with the overlap enclosure.

### Common inner privacy and the full union use the same source

Now impose SC208. For every $x\in I$, both source images are
private to the same actual original lower:

$$
F_3(x),F_6(x)\in P_{3\chi(n)}.
\tag{SC282}
$$

They have the same complete original 3-free coordinate and differ
only in the old ternary word. This follows from the existing owner
check: $x\in H$ misses all height-zero outputs, the designated
lower is the only active $L_0$ source, and $x$ misses both inner
top menus. It does not make either outer image private or place
$x$ in any $D_e$.

For the lower-private hull one can use the entire deficits, not
only the intersections $R_{e,j}$. The same check gives
$F_j(E_j)\subseteq P_{3\chi(n)}$ separately for $j=3,6$.
Put

$$
Y=F_3(E_3)\cup F_6(E_6).
$$

Both old words occur, so $Y$ has ternary hull depth exactly one.
At every other prime, its coordinate projection is exactly the
common source projection of the whole union $E=E_3\cup E_6$.
The prefix-depth argument of SC263 therefore gives

$$
\Gamma_Q(Y)=3\chi(\Gamma),\qquad
3\chi(n)\mid\Gamma_Q(P_{3\chi(n)})\mid3\chi(\Gamma).
\tag{SC283}
$$

This calculation retains every point in the two complete deficit
images; it does not choose or identify their individual witnesses.
In the $\Gamma=3$ branch one has $n=3$, so it sharpens the
corresponding SC269 row to

$$
\boxed{\Gamma=3\ \Longrightarrow\ \Gamma_Q(P_{15})=15
       \quad\text{under SC208}.}
\tag{SC284}
$$

For $\Gamma=9,n=3$, the two values 15 and 75 remain possible
from this argument. For $\Gamma=9,n=9$ and for the prime
branch, SC283 recovers the already established exact lower-private
hulls 75 and $3p$.

The overlap and private-hull conclusions do not cover any complete
original ancestor liability and do not force a common point with
$D_3\cap D_9$. The three original hull branches and the forcing
of SC227 or SC208 remain unresolved. These are ordinary deductions
from the fixed source, actual full menus and existing packets,
without new enumeration or Lean verification.

## 55. Every transported inner deficit keeps a full flat-prime responsibility

Keep the prime branch and all notation of Section 53, including the
complete original group $J_a=\{3p,9p\}$. Every $T_u$ again contains
all actual safe top outputs with nonempty pullback, even those disjoint
from the old $H$. Fix $b\ne a$ and $j\in\{3,6\}$, and let $k$ be
the other inner color. The transformed retained family, whole hole and
inner menus are those of SC273; the outer menus remain unchanged.

### The same patch has an exact residual without the extra coverage test

Run Section 53's patch without assuming $Z_b=\varnothing$: place
the three outer menus and $C_\ell'\cup T_k'$ at the four nonzero
fresh 5-roots, add $[0]_5$, then remove the outer partner and move
$T_j'$ to its former root. Both nonpartner outer menus cover $H'$
by SC272, and $C_\ell'\cup T_k'$ covers $H'$ by SC273.
The changed root has menu $(T_c\setminus\{t_p\})\cup T_j'$.
Its exact missing service is

$$
\begin{aligned}
R_{b,j}
&=H'\setminus\bigl((T_c\setminus\{t_p\})\cup T_j'\bigr)\\
&=\phi_b(E_j)\setminus T_c
 \subseteq[b]_p.
\end{aligned}
\tag{SC285}
$$

The last equality uses $H'\setminus T_j'=\phi_b(E_j)$ and
the disjoint phases $\phi_b(E_j)\subseteq[b]_p$ and
$C_{t_p}=[a]_p$. In particular, no missing point at the new
$a$ fibre is discarded. The only remaining integer liability is
the restriction of the complete $R_{b,j}$ to this one fresh root.
The other roots and the complement of $H'$ are already covered.

The original supplier indexing, distinct numerical labels and count
are exactly those checked in SC275. Every top occurs once except
the removed partner; the transformed lower occurs once. The base
cost remains at most $1+v_2$.

Consequently the complete residual satisfies

$$
\boxed{
R_{b,j}\ne\varnothing,\qquad
\Gamma_{N_0}(R_{b,j})=p
\quad(b\ne a,\ j=3,6).
}
\tag{SC286}
$$

An empty residual would give SC275's strict whole-cover descent.
For the hull statement, $R_{b,j}\subseteq[b]_p$ makes its hull a
multiple of $p$. If it were larger, it would have a divisor $3p$
or a composite 3-free divisor. The eleven-class SC137 packet or
nine-class SC136 packet encloses the entire residual; in the second
case use $R_{b,j}\subseteq H'$ and $H'\cap S=\varnothing$.
Shift the packet one fresh 5-level deeper by SC233. Its labels are
fresh against both the depth-one base menus and the 5-free retained
family. The existing $v_1\ge11$ bound pays either packet, giving
at most $1+v_2+v_1=N_3-1$ new classes and hence strict descent.
SC257's stronger original inventory remains available but is not
needed for this payment.

This concerns each full transported residual. It does not follow
merely from SC240's hulls of the larger $E_j$, nor assume that any
residual equals its enclosing AP.

### Actual original roles cover each entire residual

Now add only $H\cap L_2=\varnothing$. For a first-$p$ root $b$,
let $\mathcal A_b$ be all actual original suppliers whose nonempty
output pullbacks have first-$p$ phase $b$, whose original labels
contain $p$, and whose original ternary height is zero or is one
at outer first-3 root 2. Retain original labels as supplier identities;
a height-zero original and its height-one multiple are different
suppliers even if their numerical output moduli agree.

For every $y\in R_{b,j}$ put $x=\phi_b(y)$. Then $x\in E_j\subseteq H$
and $y\notin T_c$. The unchanged original point $F_c(y)$ has an
owner by whole coverage. Since $T_c$ includes every actual top
pullback, the owner has height zero or is an outer lower. If its
label were $p$-free, its membership would be unchanged from
$F_c(y)$ to $F_c(x)$, contrary respectively to the retained
height-zero convention or $H\cap L_2=\varnothing$. Its original
first-$p$ phase is $b$. Thus the same actual family supplies the
complete containments

$$
R_{b,3}\cup R_{b,6}\subseteq
 \bigcup_{d\in\mathcal A_b}C_d,
\qquad
\sum_{b\ne a}|\mathcal A_b|\ge2p-3.
\tag{SC287}
$$

For the count, if $b\ne a,a_p$, one supplier cannot cover all of
either residual. Its output modulus $q$ divides $N_0$, so such
coverage and SC286 would force $q\mid p$. It is $p$-bearing,
hence $q=p$. The only possible original role labels with that
output are $p$ and $3p$: the former is at $a_p$, and the latter
is the designated inner lower at $a$, so neither belongs to
$\mathcal A_b$. Therefore $|\mathcal A_b|\ge2$ at each of the
$p-2$ other roots. At $b=a_p$ the original pure-$p$ class provides
one supplier. Different roots have disjoint original identities,
which proves the stated total.

The two residuals at a fixed root may use the same two suppliers;
no additional factor of two is counted. Higher $p$ exponents,
other prime powers and cofactor overlaps remain arbitrary. In
particular, SC287 counts original roles, not automatically released
labels or extra copies of the existing $N_3$ payment inventory.

### Reverse transport retains the paired original-private incidence

The inverse images have a stronger same-source location:

$$
X_{b,j}:=\phi_b(R_{b,j})\subseteq D_p\cap E_j,
\qquad \Gamma_{N_0}(X_{b,j})=p.
\tag{SC288}
$$

This inclusion uses $J_a=\{3p,9p\}$ and does not itself require
absence of outer lowers. Indeed, $x\in X_{b,j}$ has first-$p$
phase $a$. Any other top of color $c$ containing $x$ cannot be
$p$-bearing: it would be another original in $J_a$. If it is
$p$-free, it also contains $\phi_b(x)\in R_{b,j}$, contrary to
SC285. Thus $x\in D_p$. On the fixed first-$p$ slice $b$,
$\phi_b$ is a constant CRT translation, so it preserves the hull.

Under $H\cap L_2=\varnothing$, the owner check SC265 places
$F_c(X_{b,j})$ inside the complete $P_{9p}$. If the sole-active-
$L_0$ condition is imposed as well, SC268 also places
$F_j(X_{b,j})$ inside $P_{3p}$. Consequently, under SC208,

$$
F_j(X_{b,j})\subseteq P_{3p},\qquad
F_c(X_{b,j})\subseteq P_{9p},\qquad
\Gamma_Q(F_j(X_{b,j}))=
\Gamma_Q(F_c(X_{b,j}))=9p.
\tag{SC289}
$$

For every individual $x\in X_{b,j}$ the two private images have
the same complete original 3-free coordinate. The original role
service at $F_c(\phi_b(x))$ differs only in the first $p$ digit.
All three points therefore use one specified source and the same
higher prime-power coordinates. Sets for different $b$ or different
$j$ need not share a point. In particular, SC278 does not supply
a point of $I\cap D_p$ or a common point for all these transported
responsibilities.

### The two-label phase also partitions the complete parent-private source

The existing prime-private product can be read exactly in this
phase group. In original CRT coordinates write $T_p$ for all higher
$p$ digits, and split the complete $p$-free complement from SC272 as

$$
X_p^{\rm in}=X_p\cap[0]_3,\qquad
X_p^{\rm out}=X_p\cap[c]_9,
\qquad X_p=X_p^{\rm in}\sqcup X_p^{\rm out}.
$$

The original prime-private product of
[Report 364](../../321-384/364-singleton-cofactor-ideal-and-forced-colors.md)
and the complete
owner list $J_a=\{3p,9p\}$ give

$$
\begin{aligned}
P_{3p}&=\{a\}\times T_p\times X_p^{\rm in},\\
P_{9p}&=\{a\}\times T_p\times X_p^{\rm out},\\
P_p&=\{a_p\}\times T_p\times X_p,\\
\rho(P_{3p})\sqcup\rho(P_{9p})&=P_p,
\end{aligned}
\tag{SC290}
$$

where $\rho$ is the existing first-$p$ reset from $a$ to $a_p$,
with every higher digit and other coordinate fixed. These are
complete original private sets. At root $a$ the two displayed
owners are disjoint, and every other possible owner is $p$-free;
privacy is therefore exactly avoidance of those $p$-free classes.
No selected source trace is substituted for $X_p$.

One further actual-role restriction reuses this product and
[Report 385 PH5](385-private-congruence-hulls-and-crossed-modulus-closure.md#2-the-complete-private-region-supplies-more-than-divisor-closure).
Every original $p$-bearing outer lower $d=3p^e m$, with
$(m,3p)=1$, has all of its private points at old word $c$: their
first ternary root is 2, and their full cofactor lies in $X_p$,
whose only such word is $c$. Hence $3d\mid\Gamma_Q(P_d)$.
Since $1<3d/p<d$, PH5 supplies the actual original height-two
label $3d/p=9p^{e-1}m$. These labels are distinct for distinct
outer lowers at fixed $p$. Their original phases remain whatever
the original cover specifies; they are neither fresh labels nor
asserted service for the transported residual.

The reset partition and the additional original labels do not pay
all responsibility created by moving these phases. SC286--SC289
strengthen the complete source-incidence requirements at every
other $p$ root, but no argument here forces one of these residuals
to vanish or to admit an affordable repair. The $2p-3$ role count
is not a contradiction and supplies no upper bound on the original
inventory. Eliminating $J_a=\{3p,9p\}$, the branch $|J_a|\ge3$,
and unrestricted odd distinct covering remains open. The deductions
use existing complete packets, private reset and hull interfaces;
there is no new enumeration or Lean verification.


## 56. The complete parent liability has only three strict two-class quotient types

Keep SC227 in the prime branch $\Gamma=p>5$, full SC208, and
$J_a=\{3p,9p\}$. Fix the same original cover, period $Q$, numerical
label set $D$, actual phases and substitution tree. The original
$p$-class has phase $a_p\ne a$, and the original $9p$-class has
old ternary word $c\in\{2,5,8\}$.
[Report 385 DR1](385-private-congruence-hulls-and-crossed-modulus-closure.md)
moves the original $p$-class to phase $a$ and deletes the whole
$J_a$. Its complete hole is exactly the original private set $P_p$.
At most two added classes preserve the class-count budget; with
two classes, strict modulus-sum improvement requires their sum
to be less than $3p+9p=12p$. The legal numerical palette is exactly

$$
\{m\in\mathbb Z:m>1,\ m\text{ odd}\}
 \setminus\bigl(D\setminus\{3p,9p\}\bigr).
$$

The moved $p$-class remains retained, so $p$ is unavailable. The
released labels $3p,9p$ are available. The classification below
allows every legal odd repair modulus, without initially assuming
that it divides $Q$.

### Three complete original-private pieces and their exact hulls

Using the first-$p$ reset $\rho$ from SC290, define

$$
\begin{aligned}
K_j&=\rho\bigl(P_{3p}\cap[j]_9\bigr),\qquad j\in\{3,6\},\\
K_c&=\rho(P_{9p}),\\
P_p&=K_3\sqcup K_6\sqcup K_c,\\
\Gamma_Q(K_3)&=\Gamma_Q(K_6)=\Gamma_Q(K_c)=9p,\\
\Gamma_Q(K_3\cup K_6)&=3p,\qquad
\Gamma_Q(P_p)=p.
\end{aligned}
\tag{SC291}
$$

These are nonempty complete original pieces. For $j=3,6$, the
original AP puts $P_{3p}\cap[j]_9$ inside a single $9p$-class,
while SC289 supplies a nonempty contained image of exact hull
$9p$. The subset-hull divisibility therefore makes the complete
section's hull exactly $9p$. On the fixed first-$p$ slice, $\rho$
is one constant CRT translation and preserves that hull. SC270
gives the same conclusion for the outer piece. The two inner
words differ by $3\pmod9$, so their union has hull $3p$; adding
the outer piece gives hull $p$, as in SC270. Likewise
$K_3\cup K_c$ and $K_6\cup K_c$ both have hull $p$. No selected
SC289 image is identified with the complete $P_p$.

For any nonempty $Q$-periodic integer set $W$, containment
$W\subseteq[\eta]_m$ makes $m$ divide every integer difference
of points of $W$. In particular, $x,x+Q\in W$ gives $m\mid Q$,
and then $m\mid\Gamma_Q(W)$. Thus these complete-hull restrictions
also apply to arbitrary proposed moduli not already known to divide $Q$.

### The full strict two-class palette and its joint phase condition

Let $\omega(n)$ count the distinct prime factors of $n$. Define
the set of actual numerical vacancy pairs by

$$
\mathcal P_p=
\left\{(q,n):
\begin{array}{l}
q\in\{5,7,11\},\quad q\ne p,\quad pq\notin D,\\
n>1,\quad n\mid Q,\quad n\notin D,\quad(n,3p)=1,\\
\omega(n)\ge2,\quad n<(12-q)p
\end{array}
\right\}.
\tag{SC292}
$$

A strict repair of this direct parent move by at most two classes
must use exactly two classes, with moduli $pq,n$ for some
$(q,n)\in\mathcal P_p$. Their actual APs and complete coverage
condition are

$$
B_{pq}=[a_p]_p\cap[\beta]_q,\qquad
B_n=[\gamma]_n,\qquad
P_p\subseteq[\beta]_q\cup[\gamma]_n.
\tag{SC293}
$$

The last containment is tested on all of $P_p$, where the first
term already has first-$p$ phase $a_p$. Both cofactors are $3$-free
and $p$-free. All three complete old-word pieces must therefore
use the same pair of cofactor phases; the condition cannot be
optimized separately at each word or checked on just one $R_{b,j}$.

Conversely, actual vacancies and phases satisfying SC292--SC293
would cover the entire DR1 hole. The moved $p$-class covers every
old point of the deleted $3p,9p$ classes, and every other original
class stays fixed. The repair labels are legal and distinct, the
class count is unchanged, and the modulus sum strictly decreases.
Thus any EB1 configuration under these hypotheses must satisfy
the joint escape condition

$$
\forall(q,n)\in\mathcal P_p,\quad\forall\beta\bmod q,\quad
\forall\gamma\bmod n,\qquad
P_p\setminus\bigl([\beta]_q\cup[\gamma]_n\bigr)
\ne\varnothing.
\tag{SC294}
$$

### Why no other at-most-two-class strict repair is possible

Zero classes cannot cover nonempty $P_p$. A single covering class
would have nonunit modulus dividing $\Gamma_Q(P_p)=p$, so its
label would have to be the retained $p$. Hence one class is impossible.

First consider a two-class repair containing $3p$. A $3p$-class
meeting $P_p$ must have first-$p$ phase $a_p$. At first ternary
root zero it covers all of $K_3\cup K_6$, leaving complete $K_c$;
the other modulus must divide $9p$. Among those nonunit divisors,
$3,9,p$ remain occupied and $3p$ is the first repair label, so
only the released $9p$ is legal, with phase forced by $K_c$.
At first ternary root two, the other class must cover the whole
inner union of hull $3p$, leaving no different legal divisor label.
At root one, or with a wrong first-$p$ phase, the $3p$-class
misses $P_p$ and reduces the proposal to an impossible one-class
repair. Thus the only legal two-class repair containing $3p$
is the neutral $\{3p,9p\}$ reset, still of sum $12p$.

If both repair moduli contain $p$ and neither is $3p$, their
quotients by $p$ are distinct odd integers at least $5$. Their
sum is at least $(5+7)p=12p$, precluding strict improvement.

If neither repair modulus contains $p$, retain all original
$p$-free classes and add the two repairs. Their numerical labels
are fresh against $D$, since both released labels contain $p$.
The complete prime-private product SC290 shows that every point
outside the original $p$-free classes has its $p$-free coordinate
in $X_p$. On the full first-$p$ slice $a_p$, the two repairs cover
this coordinate set. Since both repairs are $p$-free, their
coverage extends to every $p$ coordinate. If their labels use
new primes or larger exponents, use a common CRT carrier containing
those labels as well. The resulting cover is a distinct odd whole
cover with at most $K-N_p+2<K$ classes, where $N_p\ge3$ counts
the original $p$-bearing classes and includes the actual labels
$p,3p,9p$. This contradicts EB1. The argument uses the complete
$P_p$ and does not apply to a selected private residual.

Exactly one repair modulus therefore contains $p$. Write it as
$m=p^h r$, with $(p,r)=1$, and write the other repair as $B_n$,
where $p\nmid n$. The set $P_p\setminus B_n$ is nonempty:
otherwise $n\mid\Gamma_Q(P_p)=p$, contradicting $n>1$ and
$p\nmid n$. Take $x$ in this set and a $p$-free common multiple
$L_*$ of $Q/p^{v_p(Q)}$, $n$ and $r$. Along all integers

$$
x+pL_*k,\qquad k\in\mathbb Z,
$$

all non-$p$ coordinates and the first $p$ digit stay fixed. The
complete private product keeps every such point in $P_p$ and
outside $B_n$, while $k$ ranges through every later $p$ digit.
If $h\ge2$, one $p^h r$-class contains only a proper subfamily
of this entire tail, so it cannot cover all these points. Hence
$h=1$. This also excludes repair heights above the original
$p$-height: the complete integer private set retains all higher
integer lifts.

Thus $m=pu$ for an odd $u>1$ with $(p,u)=1$. The strict sum
budget gives $u<12$, so $u\in\{3,5,7,9,11\}$. The case
$u=3$ is already excluded. If $u=9$, a $9p$-repair at old word
$c$ leaves the full inner union of hull $3p$; its only nonunit
$p$-free divisor $3$ is still occupied. At word $3$ or $6$, the
repair leaves respectively $K_6\cup K_c$ or $K_3\cup K_c$,
each of hull $p$, with no nonunit $p$-free divisor. Other old
words or a wrong $p$ phase miss $P_p$. Hence $u=9$ cannot work
with a $p$-free second class either.

Only $u=q\in\{5,7,11\}$ with $q\ne p$ remains. Initial-segment
prime support and $P\ge29$ put every such $q$ in the actual
support, so $pq\mid Q$. The nonempty set $P_p\setminus B_{pq}$
is $Q$-periodic. If a single $n$-class covers it, any point and
its $Q$-translate belong to that class, forcing $n\mid Q$.
This excludes both new prime factors and excessive exponents;
it is not an initial restriction of the repair search.

The modulus $n$ cannot contain $3$. If its first ternary root is
zero, $B_{pq}$ alone must cover complete $K_c$; if it is two,
$B_{pq}$ must cover the whole inner union; if it is one,
$B_{pq}$ must cover all of $P_p$. These targets have hulls
$9p,3p,p$ respectively, none divisible by $pq$ because $q>3$.
This excludes every positive ternary height of $n$ and gives
$(n,3p)=1$.

Neither remaining label $pq,n$ is a released $3p$ or $9p$, so
both must be absent from $D$. Divisor closure puts every prime-power
divisor of $Q$ in the original inventory. A missing divisor
$n\mid Q$ must therefore have $\omega(n)\ge2$. Finally, the
strict sum budget gives $n<(12-q)p$, completing all necessary
conditions of SC292.

Actual original pure-prime phases impose further necessary tests.
The phase $\beta$ must differ from the original pure-$q$ phase.
For each prime $\ell\mid n$, the phase $\gamma\bmod\ell$
must differ from the original pure-$\ell$ phase; otherwise that
repair is contained in an unchanged original class and misses
all of $P_p$. If $q\mid n$, one also needs
$\beta\ne\gamma\pmod q$, since equal phases in SC293 would
enclose all of $P_p$ in one $q$-class, contradicting its hull $p$.
These local tests do not replace the full joint containment SC293.

### The prime-seven mechanism boundary

For $p=7$, the modulus $n$ is coprime to $3,7$ and has at least
two distinct prime factors, so $n\ge5\cdot11=55$. The option
$q=5$ requires $n<49$, the option $q=11$ requires $n<7$, and
$q=7$ is excluded by $q\ne p$. Therefore

$$
\mathcal P_7=\varnothing.
\tag{SC295}
$$

This excludes strict repair of this direct parent move within its
at-most-two-class budget. It does not exclude $J_a=\{21,63\}$
or the original whole cover. For general $p$, the remaining test
is the actual simultaneous vacancies $pq,n$ and the full joint
phase condition SC293. Existing role-supplier counts and the
forced labels $3d/p$ do not supply that containment. Larger
exchanges can release additional labels, but must pay the complete
joint hole of all moved parents and suppliers; this two-class
classification does not rule them out.

## 57. A missing common inner-outer point forces three full cylinders and a quotient collision

Keep the same original cover and tree, SC227, $\Gamma=p>5$,
full SC208, and $J_a=\{3p,9p\}$. Let $c$ again be the actual
old word of the original $9p$-class, $t_p$ its output supplier,
$I=E_3\cap E_6$, and $R_j=D_p\cap E_j$. The following are
complete-source consequences of $I\cap D_p=\varnothing$;
nonemptiness of that intersection is not assumed.

The retained family is the actual $\mathcal F_0$ of Sections 29,
32 and 41. It may contain retained lowers, retained tops and the
bought root $S$. Every member other than $S$ is an actual output
from this original family and tree. No additional identity
$\mathcal F_0=\mathcal R\cup\{S\}$ is imposed.

### Every higher-p tail is retained on the first-digit root

Write the common output period as $N_0=p^G L$, with $(p,L)=1$,
and put $T=\mathbb Z/p^{G-1}\mathbb Z$. On the first-digit root
$[a]_p$, use the actual CRT coordinates $x_p=a+pt$ and $x_L=\xi$,
where $t\in T$. For $W\subseteq\mathbb Z/L\mathbb Z$, write
its full lift as

$$
\Lambda_a(W)=
\{x\bmod N_0:x_p=a+pt,\ t\in T,\ x_L\in W\}.
$$

Any original $p$-bearing class occurring at first-digit root $a$
belongs to $J_a$, hence is $3p$ or $9p$. Because $p>5$, the
same-tree outputs retain this first digit. Both of these classes
have output $[a]_p$ and neither can be retained in $\mathcal F_0$,
since nonempty $E\subseteq H\cap[a]_p$ would then be covered.
The bought root $S$ has modulus $3$ and is $p$-free. Consequently
all retained $p$-bearing outputs miss the entire $[a]_p$ cylinder,
not only one residual inside it.

Likewise, all $p$-bearing tops of the two inner words miss
$[a]_p$; the only $p$-bearing top at this root in outer color
$c$ is the partner $t_p$. Let $U$ be the complement on
$\mathbb Z/L\mathbb Z$ of all retained $p$-free classes. Let
$V_3,V_6$ be the unions of the respective actual $p$-free top
outputs, and let $V_c$ be the union of the actual $p$-free tops
of color $c$ other than the partner. Then

$$
\begin{aligned}
H\cap[a]_p&=\Lambda_a(U),\\
E_j&=\Lambda_a(U\setminus V_j),\qquad j\in\{3,6\},\\
D_p&=\Lambda_a(U\setminus V_c).
\end{aligned}
\tag{SC296}
$$

Here $E_j\subseteq[a]_p$ follows from SC227. For the last
identity, first use complete coverage of $H$ by $T_c$ to obtain
$D_p\subseteq C_{t_p}=[a]_p$, and then use the absence of every
other $p$-bearing top of that color. Tops active on $H$ suffice;
including all actual tops preserves their service on these
targets. Each identity retains every higher $p$ tail.

### Three disjoint complete bases when the triple intersection is empty

Assume $I\cap D_p=\varnothing$ and define, in the same quotient,

$$
\begin{aligned}
A&=U\setminus(V_3\cup V_6),\\
B&=U\setminus(V_3\cup V_c),\\
C&=U\setminus(V_6\cup V_c).
\end{aligned}
$$

Every pairwise intersection equals
$U\setminus(V_3\cup V_6\cup V_c)$, so the bases are pairwise
disjoint. SC280 and SC243 give

$$
\begin{aligned}
\Lambda_a(A)&=I,\qquad
\Lambda_a(B)=R_3,\qquad
\Lambda_a(C)=R_6,\\
A,B,C&\ne\varnothing,\qquad
\Gamma_L(A)=\Gamma_L(B)=\Gamma_L(C)=1.
\end{aligned}
\tag{SC297}
$$

The hull identity uses the whole tail: for every nonempty $W$,
independent CRT coordinates give
$\Gamma_{N_0}(\Lambda_a(W))=p\Gamma_L(W)$, including when $G=1$.
Each of the three full lifts has hull $p$, hence each base has hull one.

For every indicated base point $\xi$ and every $t\in T$, the
three actual source maps applied to the same output point give
the following complete incidences.

| Base | Old word $3$ | Old word $6$ | Old word $c$ |
|---|---|---|---|
| $A$ | Private to original $3p$ | Private to original $3p$ | Covered by an actual $p$-free top |
| $B$ | Private to original $3p$ | Covered by an actual $p$-free top | Private to original $9p$ |
| $C$ | Covered by an actual $p$-free top | Private to original $3p$ | Private to original $9p$ |

Privacy uses full SC208: the sole active inner lower is $3p$,
$H\cap L_2=\varnothing$, and the retained convention excludes
height-zero owners. Once the corresponding top menu is absent,
only the displayed original owner remains. The covering assertions
come from service of $I$ by color $c$ without $t_p$, of $R_3$
by $T_6$, and of $R_6$ by $T_3$. The condition on $J_a$ forces
all these actual suppliers to be $p$-free. Consequently each
serving menu also covers its target's saturation through every
first-$p$ root and every higher tail, with all other coordinates
fixed. This does not identify any one cylinder with the whole
$P_p$ or the whole $X_p$ of SC290.

Each serving menu requires at least two distinct actual top
suppliers. If one nonunit $p$-free output modulus $q$ enclosed
its whole target, the target's complete hull $p$ would force
$q\mid p$, a contradiction. Top originals at the three different
old words have disjoint identities, giving at least six different
actual $p$-free top suppliers in total. SC288 also retains the
exact cross service

$$
\begin{aligned}
X_{b,3}&\subseteq R_3\subseteq T_6^{p\text{-free}},\\
X_{b,6}&\subseteq R_6\subseteq T_3^{p\text{-free}},
\qquad b\ne a.
\end{aligned}
\tag{SC298}
$$

Six is one count on the common original family, not a count
multiplied by $p-1$. The same two suppliers of one color may
serve several $b$-dependent sets. These containments do not
identify points belonging to different sets.

### The whole quotient cover retains a different-phase numerical collision

By SC296, the empty triple intersection is equivalent to
$U\subseteq V_3\cup V_6\cup V_c$. Thus the following family
of full actual APs covers all of $\mathbb Z/L\mathbb Z$, and
therefore all integers:

$$
\mathcal G=
\mathcal F_0^{p\text{-free}}
\cup\mathcal T_3^{p\text{-free}}
\cup\mathcal T_6^{p\text{-free}}
\cup\bigl(\mathcal T_c\setminus\{t_p\}\bigr)^{p\text{-free}}.
\tag{SC299}
$$

Here $\mathcal T_u$ denotes the actual supplier family, while
$T_u$ denotes its union of APs. Lift any quotient point $\xi$
to first-$p$ root $a$. If the lift is outside $H$, a retained
$p$-free class covers it. If it is in $H$, the empty triple
intersection supplies one of the three top menus. Every member
modulus divides $L$ and its membership is independent of the
$p$ tail, so this proves coverage of the whole quotient, not a
selected trace.

Retained moduli are internally distinct, and top output moduli
are globally distinct across colors: equal top output moduli
would repeat the original numerical label $9\chi(q)$. Counting
supplier occurrences gives

$$
|\mathcal G|\le|\mathcal F_0|+v_2
=K-N_3-z+v_2=K-2-v_1-z<K.
\tag{SC300}
$$

This upper bound may count an AP appearing both as retained and
as a menu member twice; that only weakens the bound and loses
no liability. Every numerical repetition crosses the retained/top
partition. If every repetition had equal actual phase, merging
identical APs would produce a distinct odd whole cover with fewer
than $K$ classes, contrary to EB1. Hence at least one pair satisfies

$$
\begin{gathered}
q>1,\qquad p\nmid q,\qquad
[\alpha]_q\in\mathcal F_0,\\
[\beta]_q\in
\mathcal T_3\cup\mathcal T_6\cup
\bigl(\mathcal T_c\setminus\{t_p\}\bigr),\qquad
\alpha\not\equiv\beta\pmod q.
\end{gathered}
\tag{SC301}
$$

The retained end may be the bought root $S$, in which case
$q=3$. Otherwise it has an actual original source, potentially
a lower or a retained top. Thus SC301 is not universally a
collision between two original suppliers, and its repeated label
has not been released or paid for.

The common data here are the original cover and substitution
tree. The family $\mathcal G$ mixes old words $3,6,c$; no single
map $F_{u,\theta}$ has been shown to realize all its members.
SC6 concerns two original sources surviving at the same old word,
where different phases follow directly from original irredundancy.
It therefore cannot be applied directly as the source of SC299.
The conditional conclusion here is the specified three-color
$p$-free whole cover. The final inference from a smaller whole
cover to a different-phase collision reuses the same EB1
minimality principle.

This branch still requires either an exclusion of the three
complete bases under the actual AP geometry or a repair paying
the full liability of a specified SC301 collision. Hull-one bases,
six suppliers and the count bound alone do not provide either
step or imply $I\cap D_p\ne\varnothing$. A finite model of
only the local three-color membership table, without the actual
retained family and the full parent-private partition SC290,
would not refute the desired common-point implication. These
two sections give ordinary mathematical deductions without Lean
verification. Eliminating $J_a=\{3p,9p\}$ and unrestricted odd
distinct covering remain unresolved.

## 58. Four complete outer-lower residual menus force a paid descent

Keep the prime branch of Sections 53 and 55, on the same original
EB1 cover and the same fixed tree $\theta$. Thus original ternary
height is two, $p>5$, and the complete original group is
$J_a=\{3p,9p\}$. The original $3p$ is the designated inner lower,
the original $9p$ has outer word $c$, and original pure $p$ has
phase $a_p\ne a$. All actual safe top outputs with nonempty
pullback remain in the menus, as required in Section 53.

For $b\ne a$ and $j\in\{3,6\}$, retain the entire residual
$R_{b,j}=\phi_b(E_j)\setminus T_c$ from SC285. The transformed
retained family has $K-N_3-z$ classes, and SC285 covers every
remaining integer except one fresh-5-root restriction of $R_{b,j}$
at a base cost at most $1+v_2$. Here
$N_3=2+v_1+v_2$, $v_2\le v_1$, and $z\ge0$.

The stronger original inventory SC257 applies to this same source.
Its prime $P$ is the largest original support prime, whether or not
$P=p$, and its count is
$c_2=\#\{d\in D:P\nmid d,\ v_3(d)=2\}$. Pure $9$ gives
$c_2\ge1$, and the existing height-two support restriction gives
$P\ge29$. Consequently

$$
2+2v_1\ge N_3\ge P+c_2+1\ge31,
\qquad \boxed{v_1\ge15.}
\tag{SC302}
$$

### A complete menu retains the actual original supplier identities

For $b\notin\{a,a_p\}$, let $\mathcal G_b$ consist of all
actual original outer lowers with first-$p$ phase $b$ and labels
$d=3n_d$ satisfying $p\mid n_d$ and $\gcd(n_d,15)=1$.
Their original ternary root is 2 and their original 5-height is
zero. Hence their output classes are literally
$C_d=[\eta_d]_{n_d}$, where $\eta_d=a_d\bmod n_d$; the
fixed tree changes none of these cofactor phases.

The numerical $n_d$ are distinct across the whole family of roots,
since the original labels $3n_d$ are distinct. They differ from
1 and $p$: the only original $3p$ is the designated inner lower
at phase $a$. Say that a root is eligible if one of its two
complete residuals has this service:

$$
\exists j\in\{3,6\},\qquad
R_{b,j}\subseteq\bigcup_{d\in\mathcal G_b}C_d.
\tag{SC303}
$$

This condition concerns every point of $R_{b,j}$, including all
integer lifts and all higher-prime-power coordinates. No enclosure
hull is substituted for that set.

### One common-p menu and one actual menu give a single packet

Suppose a subfamily of $r$ actual suppliers gives SC303 for a
fixed $b,j$, and write its classes as $[\eta_i]_{n_i}$.
SC285 and the retained bought root $S=[s]_3$ give

$$
R:=R_{b,j}\subseteq[b]_p\cap
       \bigcup_{i=1}^r[\eta_i]_{n_i},
\qquad R\cap S=\varnothing.
$$

Apply the existing two-menu, three-row packet SC88--SC89, or its
complete-service form SC113--SC114, to the two menus
$\{[b]_p\}$ and $\{[\eta_i]_{n_i}:1\le i\le r\}$.
SC233 shifts it one fresh 5-level deeper, preserving every
cofactor phase.

For the explicit phases, assign the deficient outer color $c$ to
fresh root 1. The SC285 base consists of $[0]_5$, the two other
outer menus at roots 2 and 3, $C_\ell'\cup T_k'$ at root 4,
and $(T_c\setminus\{t_p\})\cup T_j'$ at root 1, where
$\{j,k\}=\{3,6\}$. Each supplier is intersected with its
assigned fresh root. Its sole remaining liability is $[1]_5\cap R$.
Put $\lambda_t=1+5t\pmod{25}$ for $0\le t\le4$, and let
$\alpha,\beta\in\{0,1,2\}$ be the two roots other than $s$.
The last column below has one class for every $i$.

| New modulus factor | Unconditional class | Common $p$-class | Actual supplier classes |
|---|---|---|---|
| $25$ | $[\lambda_0]_{25}$ | $[\lambda_1]_{25}\cap[b]_p$ | $[\lambda_2]_{25}\cap[\eta_i]_{n_i}$ |
| $75$ | $[\lambda_3]_{25}\cap[\alpha]_3$ | $[\lambda_3]_{25}\cap[\beta]_3\cap[b]_p$ | $[\lambda_4]_{25}\cap[\alpha]_3\cap[\eta_i]_{n_i}$ |
| $225$ | $[\lambda_4]_{25}\cap[\beta]_9$ | $[\lambda_4]_{25}\cap[\beta+3]_9\cap[b]_p$ | $[\lambda_4]_{25}\cap[\beta+6]_9\cap[\eta_i]_{n_i}$ |

These are single CRT classes. The complete-service proof of
SC88--SC89 applies to every integer in $[1]_5\cap R$: both
supplier menus cover $R$, and its ternary root is never $s$.
The retained family and the SC285 base already cover every other
integer. Thus this is one simultaneous completion of the exact
liability, with labels and cost

$$
\{25,75,225\}\cdot\{1,p,n_1,\ldots,n_r\},
\qquad c_{\rm packet}=6+3r.
\tag{SC304}
$$

Within each row the cofactors $1,p,n_1,\ldots,n_r$ are
distinct. Different rows have different 3-valuations, since all
these cofactors are 3-free. Every packet label has 5-valuation
two, every base label has 5-valuation one, and every retained
label is 5-free. Hence all numerical labels are distinct, odd
and greater than one. The common $p$-classes are shared once
across the actual menu; there is no assembly of separate packets
with repeated labels.

The complete output cover therefore satisfies

$$
\begin{aligned}
K'&\le K-N_3-z+(1+v_2)+(6+3r)\\
  &=K+5+3r-v_1-z,\\
6+3r\le v_1+z&\quad\Longrightarrow\quad K'\le K-1<K.
\end{aligned}
\tag{SC305}
$$

The construction uses the phase-transformed output family already
specified by SC273. Its coverage does not require those mixed
menus to be simultaneous pullbacks of a modified original cover.

### The same original inventory pays a repair among four roots

Suppose four distinct roots outside $\{a,a_p\}$ are eligible.
At each choose one successful inner color and one complete actual
menu, of size $r_b$. Different roots use disjoint original labels,
because every original has only one first-$p$ phase. All selected
labels count in $v_1$.

Two further members of that same $v_1$ inventory belong to none of
these menus. The first is the designated inner $3p$. For the second,
initial-segment support and $P\ge29$ permit a support prime
$q\in\{17,19\}\setminus\{p\}$. Report 385 GHA10 supplies
the actual original $3q^{H_q}$, and divisor closure supplies the
actual original $3q$. Equivalently, Report 385 Section 60 already
supplies this shallow label. It is a nonpure height-one original,
so it counts in $v_1$, and it is $p$-free, so it cannot occur
in any $\mathcal G_b$. It differs from $3p$. Thus, without
adding any independently optimized inventory,

$$
\sum_{\text{four roots }b}r_b\le v_1-2,
\qquad 4r\le v_1-2,
\quad r:=\min_b r_b.
\tag{SC306}
$$

If $r\le3$, then $6+3r\le15\le v_1$ by SC302. If $r\ge4$,
then $6+3r\le4r+2\le v_1$ by SC306. In both cases SC305
constructs a distinct odd whole cover with at most $K-1-z$ classes,
contrary to EB1. Therefore

$$
\boxed{\#\{b\notin\{a,a_p\}:b\text{ satisfies SC303}\}\le3.}
\tag{SC307}
$$

Only the least-cost repair is executed. The other three complete
menus certify its affordability using disjoint identities in the
one original cover. The reserved $3p$ and $3q$ are not extra
credit beyond $N_3$; they reduce the menu share of the existing
$v_1$ term in SC305. The successful inner colors at different
roots need not agree.

### At least p-5 roots require service outside these outer-lower menus

Now impose $H\cap L_2=\varnothing$. There are $p-2$ roots
outside $\{a,a_p\}$. By SC307, at least $p-5$ of them are
not eligible, and at each such root both complete residuals fail
SC303. Consequently there is a set $B$ of at least $p-5$ roots
such that

$$
\forall b\in B\ \forall j\in\{3,6\}\ \exists y_{b,j},\qquad
 y_{b,j}\in R_{b,j}\setminus\bigcup_{d\in\mathcal G_b}C_d.
\tag{SC308}
$$

Every original owner of $F_c(y_{b,j})$ is then a $p$-bearing
height-zero original or a $p$-bearing outer lower of positive
original 5-height. Indeed, the full top convention and
$y_{b,j}\notin T_c$ exclude every top owner. The same-source
owner argument of SC287, using $H\cap L_2=\varnothing$, excludes
$p$-free owners. The defining exclusion in SC308 removes the
remaining 5-free outer lowers. Whole original coverage ensures
that an owner exists.

The witnesses for $j=3$ and $j=6$ need not coincide. SC307 itself
does not require absence of outer lowers on $H$, or the
sole-active-inner-lower condition of SC208; the additional
hypothesis is used only for this owner classification. No bound
here repairs the service supplied by the remaining two original
roles, forces SC227 or SC208, or covers arbitrary original
ternary height. These are ordinary deductions from the existing
packet and original inventory, without enumeration or Lean
verification; elimination of the entire paired-prime branch and
unrestricted odd distinct covering remain unresolved.

## 59. The pure-prime root exhausts the transported visibility of the outer private region

Keep SC227 in its prime branch, SC271, and Section 53's convention
that every safe top with nonempty pullback through the fixed tree
is included. Use the actual retained family and the cylinder
notation of SC296, including every retained top and the bought
root. The argument for SC296 uses neither SC208 nor the
empty-triple-intersection alternative of Section 57.

Put
$$
W_j=U\setminus(V_j\cup V_c),\qquad j\in\{3,6\}.
$$
The existing cylinder identities immediately give
$$
D_p\cap E_j=\Lambda_a(W_j).
\tag{SC309}
$$
This retains every higher $p$ digit. It does not identify the
cylinder with the entire AP $[a]_p$.

### The pure-prime root realizes the whole generator

Write the output CRT coordinates as $(b,t,\xi)$, where the
$p$-coordinate is $b+pt$, $t\in T$, and
$\xi\in\mathbb Z/L\mathbb Z$. For $b\ne a$, let
$B_b\subseteq T\times\mathbb Z/L\mathbb Z$ consist of the
pairs whose point at first digit $b$ belongs to an actual
$p$-bearing top of color $c$. Subtracting the $p$-free tops first
in SC285 gives the exact equality
$$
R_{b,j}
=\{b\}\times\bigl((T\times W_j)\setminus B_b\bigr).
\tag{SC310}
$$
The $p$-bearing top condition may depend on all higher $p$ digits;
none is discarded in $B_b$.

Let $a_p$ be the phase of the original pure-$p$ class. No other
$p$-bearing original can have first digit $a_p$, since its whole
class would then be contained in that pure-$p$ class and be
redundant. In particular $B_{a_p}=\varnothing$. Therefore SC288
sharpens to
$$
\boxed{
X_{a_p,j}=\phi_{a_p}(R_{a_p,j})
=D_p\cap E_j
=\bigcup_{b\ne a}X_{b,j}.}
\tag{SC311}
$$
The union includes the original pure-$p$ root. Every other reset
residual is a subset of the same complete cylinder; taking more
first-digit roots cannot enlarge it. These equalities do not
require a common point of $I$ and $D_p$.

### Exactly which original-private points are seen

Now impose full SC208. Write the original period as
$Q=9p^G W$, where $(W,3p)=1$, and set
$$
Z_u=\{w\in\mathbb Z/W\mathbb Z:(u,w)\in X_p\},
\qquad u\in\{3,6,c\}.
$$
Let $\Theta:\mathbb Z/L\mathbb Z\to\mathbb Z/W\mathbb Z$
be the actual common non-$p$ source map: it sends the output
ternary digits through the fixed original $5$-prefix tree and
copies every other coordinate. The complete private product
SC290 and the same-source owner check give
$$
\begin{aligned}
W_j&=U\cap\Theta^{-1}(Z_j\cap Z_c),\\
\Theta(W_3\cup W_6)
&=\Theta(U)\cap Z_c\cap(Z_3\cup Z_6).
\end{aligned}
\tag{SC312}
$$
For the forward inclusion in the first line, each point of
$\Lambda_a(W_j)$ lies in $E_j\cap D_p$: SC208 makes its inner
image private to $3p$ and its outer image private to $9p$.
Conversely, $\xi\in U$ supplies the actual hole condition.
Membership of $\Theta(\xi)$ in both sections excludes every
$p$-free original owner at the two indicated old words, while
SC271 excludes every competing $p$-bearing top there. Thus the
output point lies in $E_j\cap D_p$ for every higher $p$ tail.
The second line is the image of the first for both inner words.

Define the complete portion seen by all transported residuals as
$$
\mathcal V=
\bigcup_{\substack{b\ne a\\j\in\{3,6\}}}
F_c(X_{b,j}).
$$
In original coordinates ordered as first $p$ digit, higher $p$
tail, old ternary word and remaining cofactor, SC311--SC312 and
SC290 yield
$$
\begin{aligned}
\mathcal V
&=\{a\}\times T\times\{c\}\times
  \bigl(Z_c\cap\Theta(U)\cap(Z_3\cup Z_6)\bigr),\\
P_{9p}\setminus\mathcal V
&=\{a\}\times T\times\{c\}\times
  \bigl(Z_c\setminus[\Theta(U)\cap(Z_3\cup Z_6)]\bigr).
\end{aligned}
\tag{SC313}
$$
The missing cofactor set includes original $5$-prefixes absent
from the image of $\Theta$, prefixes present in that image but
excluded by the actual retained-hole mask $U$, and cofactors
private at word $c$ but at neither inner word. These are three
disjoint possibilities when tested in that order. Every such
cofactor carries its full higher-$p$ tail.

Consequently these residuals exhaust the complete original
$P_{9p}$ exactly when
$$
Z_c\subseteq\Theta(U)\cap(Z_3\cup Z_6).
\tag{SC314}
$$
No such inclusion follows from the residual hulls or their
nonemptiness. The pure-$p$ root already realizes the entire
visible set, so additional rootwise witnesses cannot fill the
missing part of SC313. This identifies a complete outstanding
liability; it supplies no repair of it, no released numerical
labels and no new descent. The statements are ordinary
same-source consequences of SC285, SC288, SC290 and SC296,
without new enumeration or Lean verification.

## 60. A shared prime ladder pays repeated positive-height outer-lower service

Keep Section 58's original EB1 cover of ternary height two, SC227
in its prime branch, the complete group $J_a=\{3p,9p\}$ with
$p>5$, and one fixed source tree $\theta$. Keep every actual safe
top with nonempty pullback as in Section 53. Fix $b\ne a$ and
$j\in\{3,6\}$, and write $R=R_{b,j}$. SC285 supplies
$R\subseteq[b]_p$, $R\cap S=\varnothing$ for the bought root
$S=[s]_3$, and a base whose only remaining integer liability is
one fresh-5-root restriction of the entire $R$. Its cost is at
most $1+v_2$, on top of $K-N_3-z$ retained classes, where
$N_3=2+v_1+v_2$.

Suppose a finite family $\mathcal W$ of actual original outer
lowers at first-$p$ phase $b$ supplies complete service:

$$
\begin{gathered}
R\subseteq\bigcup_{d\in\mathcal W}C_d,\qquad
d=3\cdot5^{h_d}m_d,\qquad p\mid m_d,\quad(m_d,15)=1,\\
C_d=[\eta_d]_{3^{h_d}m_d}.
\end{gathered}
\tag{SC315}
$$

The ternary prefix of $\eta_d$ is the actual output prefix under
the same tree. The containment includes all integer lifts and all
higher prime-power coordinates. It does not replace $R$ by a
hull or require agreement between different supplier phases.

### Two divisor requests cover each supplier's remaining service

For each source use the numerical menu

$$
\mathcal N_d=
\{3^e t:0\le e\le h_d,\ t\mid m_d,\ p\mid t\}
 \setminus\{p,3p\}.
\tag{SC316}
$$

Suppose two slots $s_{d,3},s_{d,4}\in\mathcal N_d$ per source
can be assigned with all slots globally distinct. This reuses the
divisor-slot construction SC125--SC126; the complete residual's
common $p$-phase and avoidance of $S$ reduce the requests to two.
The concrete profile below supplies the allocation automatically.

Normalize the deficient fresh root to 1. Put
$\lambda_t=1+5t\pmod{25}$ for $0\le t\le4$, and let
$\alpha,\beta$ be the two modulo-3 roots other than $s$.
Add four common classes and the two assigned classes per source:

$$
\begin{gathered}
[\lambda_0]_{25},\qquad
[\lambda_1]_{25}\cap[b]_p,\\
[\lambda_2]_{25}\cap[\alpha]_3,\qquad
[\lambda_2]_{25}\cap[\beta]_3\cap[b]_p,\\
[\lambda_t]_{25}\cap[\eta_d]_{s_{d,t}}
\quad(d\in\mathcal W,\ t=3,4).
\end{gathered}
\tag{SC317}
$$

These are single CRT classes. For an integer in $[1]_5\cap R$,
the first two common classes cover second 5-digits 0 and 1.
At digit 2 its ternary root is $\alpha$ or $\beta$, and the
other two common classes cover both cases. At digit 3 or 4,
SC315 supplies an actual owner; the assigned slot divides that
owner's output modulus and retains its actual phase. Thus every
integer in the complete remaining liability is covered. The
retained family and SC285 base cover every other integer.

The four common numerical labels are $25,25p,75,75p$.
Every source slot is $p$-bearing, so it differs from 1 and 3;
SC316 also excludes $p,3p$. Hence the globally distinct source
labels $25s_{d,t}$ differ from all common labels. Every packet
label has 5-valuation two, every base label has 5-valuation one,
and every retained label is 5-free. All output moduli are
therefore distinct odd nonunits. The packet costs
$4+2|\mathcal W|$ classes. Its coverage does not require the
mixed output menus to be pullbacks of a modified original cover.

### Actual height-one donors pay both requests and the common classes

For a slot $3^e t$, use the original donor $3\cdot5^e t$.
It divides its actual source $3\cdot5^{h_d}m_d$, so divisor
closure supplies it. The donor map is injective, and every donor
is a nonpure original of ternary height one counted in $v_1$.
The donor's phase supplies no patch phase: SC317 uses only the
actual source phase. No additional original service is deleted.

Four other actual $v_1$ labels are outside this donor image.
One is the designated $3p$, because slot $p$ was excluded.
The largest original prime satisfies $P\ge29$ as in SC302.
Initial-segment support therefore permits three distinct primes
$q_1,q_2,q_3\in\{17,19,23,29\}\setminus\{p\}$.
Report 385 GHA10 and divisor closure supply the actual labels
$3q_i$; its Section 60 also supplies these shallow labels directly.
They are $p$-free, whereas every assigned donor is $p$-bearing.
They differ from one another and from $3p$. Consequently

$$
\begin{aligned}
v_1&\ge2|\mathcal W|+4,\\
K'&\le K-N_3-z+(1+v_2)+(4+2|\mathcal W|)\\
  &=K+3+2|\mathcal W|-v_1-z
   \le K-1-z<K.
\end{aligned}
\tag{SC318}
$$

This uses one original inventory. The four reserved labels pay
the common classes by count; they need no phase agreement with
those classes. The $v_2$ inventory already used by the SC285 base
is not counted again. Thus any complete menu admitting the stated
two-slot assignment contradicts EB1.

### One repeated positive-height column always admits the assignment

Suppose every source in SC315 has $h_d\ge1$ and $m_d\ne p$.
Permit one cofactor $m_*$ to occur at arbitrarily many distinct
positive heights; every other numerical cofactor occurs in at
most one selected source. Different cofactors may overlap or
divide one another, and their actual phases remain arbitrary.

For each source outside the special column assign its two slots
$m_d,3m_d$. For a special source at height $h$, use the menu

$$
\{3^e m_*:0\le e\le h\}
 \ \cup\ \{3^e p:2\le e\le h\}.
\tag{SC319}
$$

These two ladders are disjoint and have $(h+1)+(h-1)=2h$ slots
for every $h\ge1$. Their menus are nested. At most $h$ special
sources have height at most $h$: two at the same height would
have the same actual original label $3\cdot5^h m_*$.
Ordering the special heights $h_1<\cdots<h_t$ gives

$$
2i\le2h_i
=\#\bigl(\{3^e m_*:0\le e\le h_i\}
          \cup\{3^e p:2\le e\le h_i\}\bigr).
\tag{SC320}
$$

There is an explicit assignment: give the first special source
$m_*,3m_*$, and give source $i\ge2$ the slots
$3^i m_*,3^i p$. They divide its output modulus because
$h_i\ge i$. They are all distinct, and unique 3-free parts
separate them from all nonspecial columns. The common $p$-ladder
starts at exponent two and avoids $p,3p$. Every slot lies in
SC316. SC318 therefore excludes this concrete complete-service
profile without a further matching hypothesis.
The special column may be absent, recovering one positive height
per cofactor with no restriction on the number of cofactors.

Pure-$p$ sources are excluded from this automatic profile. Their
putative slots $p,3p$ are precisely the forbidden ones. Merely
requiring a pure-$p$ source to have positive height does not pay it.

### Several repeated columns share one joint prime-ladder capacity

For a source with $m\ne p$ and height $h$, now restrict its menu
to its private ladder $\{3^e m:0\le e\le h\}$ together with
the common ladder $\{3^e p:2\le e\le h\}$. A source with
$m=p$ has only that common ladder. Each common numerical slot
occurs once across all columns.

Let $L_m(h)$ count the selected actual sources with cofactor $m$
and height at most $h$. Sums over cofactors below range over the
finitely many cofactors occurring in $\mathcal W$. For integers
$H\ge0$ define

$$
\delta_m(H)=\max_{0\le h\le H}(2L_m(h)-h-1)_+
\quad(m\ne p),\qquad
c(H)=\max(H-1,0).
\tag{SC321}
$$

The existing finite Hall theorem, applied to two copies of each
source, gives the following exact condition for this restricted
private-plus-common allocation:

$$
\boxed{2L_p(H)+\sum_{m\ne p}\delta_m(H)\le c(H)
       \quad\text{for every integer }H\ge0.}
\tag{SC322}
$$

For necessity, fix $H$. In every column with
$\delta_m(H)>0$, choose a prefix height attaining that maximum
and include all sources in the prefix. A positive maximum is
attained at an actual source height: between occurring heights
the count is constant and $2L_m(h)-h-1$ decreases. Include also
all pure-$p$ sources through $H$. After its private slots are
subtracted, each non-$p$ column has request surplus
$\delta_m(H)$. The pure-$p$ sources have no private slots,
and all common slots lie among the $c(H)$ slots through $H$.
Hall's inequality forces SC322. An empty chosen subset gives
zero demand and satisfies it immediately.

For sufficiency, take any nonempty subset $X$ of sources and
let $H$ be its largest height. For each represented $m\ne p$,
write $X_m$ for that column's subset and $h_m$ for its largest
height. Its private union has $h_m+1$ slots. These unions are
disjoint from one another and from the common union, which has
exactly $c(H)$ slots. The remaining demand obeys

$$
\begin{aligned}
2|X|-\sum_{\substack{m\ne p\\X_m\ne\varnothing}}(h_m+1)
&=2|X_p|+
  \sum_{\substack{m\ne p\\X_m\ne\varnothing}}
       (2|X_m|-h_m-1)\\
&\le2L_p(H)+\sum_{m\ne p}\delta_m(H)
 \le c(H).
\end{aligned}
\tag{SC323}
$$

Thus every subset passes the two-request Hall test. This is a
joint condition: separate bounds $\delta_m(H)\le c(H)$ would
spend the same common ladder repeatedly. Proper cofactor-divisor
slots in SC316 may improve an allocation that fails SC322;
necessity is asserted only for the restricted ladders.

At $H=0$ the common capacity is zero. A height-zero source in a
non-$p$ column has one private slot for two requests and makes
$\delta_m(0)\ge1$; a pure-$p$ height-zero source has no slot.
Both are correctly rejected by this restricted-ladder test;
proper-divisor slots in SC316 can give a different allocation.
A pure-$p$ source of height one
also has no slot, and one of height two has only $9p$.
A single pure-$p$ source of height three can use $9p,27p$ when
other columns have not spent that common capacity. All these
cases are covered by SC322 without a second private $p$-column.
It suffices to test zero and heights occurring in the actual
selected family: between them the left side is constant and
the right side is nondecreasing.

For positive-height outer lowers, actual-label uniqueness gives
$L_m(h)\le h$. A column with at most one such source has
$\delta_m(H)=0$; the one repeated column in SC319 has
$\delta_{m_*}(H)\le c(H)$. With no pure-$p$ source this
recovers the automatic profile directly from SC322.

SC125--SC126 provide the actual-phase divisor patch and donor
injection; SC148 provides common-root sharing; SC187 and DP12
provide the nested matching rule. Section 41's two requests per
lower use four complete safe-color menus for the whole $H$.
Here only one actual outer-lower menu of $R$ is assumed, and
SC317 explicitly pays the other three fresh subroots using its
common $p$-phase and avoidance of $S$.

The argument does not force outer lowers to cover any complete
$R$: SC287 also permits original height-zero owners. Nor does
it force the general repeated-column allocation. Deeper fresh-5
splitting alone cannot replace the missing actual supplier
geometry by the entire prime envelope: SC139 already excludes
that envelope's one-prime palette, with capacity at most $91/96$
and at most $7/8$ when only cofactor types $1,p$ are used.
The actual residual can be smaller and is the set repaired here.
The height-zero role, unrestricted repeated-column service, the
full paired-prime branch and unrestricted odd distinct covering
remain unresolved. These are ordinary mathematical deductions;
no new enumeration or Lean verification is asserted.

## 61. A complete positive-height menu with an extra cofactor is impossible

Keep the exact SC285 setup: one original EB1 cover of ternary
height two, SC227 in its prime branch $p>5$, the complete original
group $J_a=\{3p,9p\}$, one fixed source tree, and every actual
safe top with nonempty pullback, including those inactive on the
old $H$. Fix $b\ne a$ and $j\in\{3,6\}$, and put
$R=R_{b,j}=\phi_b(E_j)\setminus T_c$. Thus
$R\subseteq[b]_p$ and $R\cap S=\varnothing$, where $S=[s]_3$
is the bought ternary root. Normalize the deficient fresh root
to 1. The retained family and SC285 base cover every integer
outside $[1]_5\cap R$, at cost at most
$K-N_3-z+(1+v_2)$, with $N_3=2+v_1+v_2$ and $z\ge0$.

Under these hypotheses, no finite actual outer-lower menu
consisting entirely of the following sources can cover $R$:

$$
\begin{gathered}
R\subseteq\bigcup_{d\in\mathcal W}C_d,\qquad
d=3\cdot5^{h_d}p^{k_d}q_d,\\
h_d,k_d\ge1,\qquad q_d>1,\qquad(q_d,15p)=1,\\
C_d=[\eta_d]_{n_d},\qquad n_d=3^{h_d}p^{k_d}q_d,
\qquad r=|\mathcal W|.
\end{gathered}
\tag{SC324}
$$

The phases are the actual output phases at first-$p$ root $b$
in that same tree. Complete service means every integer of $R$,
including every higher prime-power tail. The cofactor $q_d$ is
an integer, not necessarily a prime; different cofactors may
overlap or divide one another. The heights and columns may
repeat without a bound. Original-label uniqueness makes the
triples $(h_d,k_d,q_d)$ distinct. SC286 gives $R\ne\varnothing$,
so a complete menu has $r\ge1$.

### Projection counts for one actual family

For a nonempty $X\subseteq\mathcal W$, use the coordinate
projections of its actual triples and write

$$
\begin{gathered}
x=|X|,\qquad A=|\pi_{hk}X|,\qquad B=|\pi_{hq}X|,\qquad
C=|\pi_{kq}X|,\qquad n=|\pi_qX|,\\
x^2\le ABC.
\end{gathered}
\tag{SC325}
$$

The inequality is the finite projection inequality in
Balister--Bollobás, *Projections, Entropy and Sumsets*,
[arXiv:0711.1151v1, Section 2, equation (4)](https://arxiv.org/html/0711.1151v1#S2.E4),
applied to the finite subset of $\mathbb Z^3$ with the uniform
two-cover $\{\{h,k\},\{h,q\},\{k,q\}\}$ of its coordinates.
It requires neither a product-shaped set nor independence.
All projections are of the same $X$.

Two arithmetic consequences suffice:

$$
\begin{aligned}
1\le x\le26&\quad\Longrightarrow\quad A+B+C\ge x+1,\\
x\ge15&\quad\Longrightarrow\quad A+B+C\ge19.
\end{aligned}
\tag{SC326}
$$

For the first, $A+B+C\le x$ and AM--GM would give
$x^2\le ABC\le(x/3)^3$, forcing $x\ge27$. For the second,
$A+B+C\le18$ would give $x^2\le ABC\le6^3=216<225\le x^2$.
The integral bounds in SC326 follow.

### Up to twenty-six sources: two Hall requests with four reserved donors

Suppose $1\le r\le26$. Fix one actual source $d_0\in\mathcal W$
and its output modulus $n_0$ once, before choosing any subset.
Give each source the full divisor menu

$$
\mathcal N_d=\{t\in\mathbb N:t\mid n_d\}
                  \setminus\{1,3,p,3p,n_0\},\qquad
\mathcal N(X)=\bigcup_{d\in X}\mathcal N_d.
\tag{SC327}
$$

These menus allow $p$-free slots. The coverage argument of
SC317 needs only a divisor of the actual output, while its
four common labels require exclusion of $1,3,p,3p$.
The extra global exclusion of $n_0$ reserves the donor $d_0$.

For every nonempty $X$, its divisor union contains the five
families below before the exclusions in SC327:

| Numerical slots | Index set | Number |
|---|---|---:|
| $3^hp^kq$ | actual triples in $X$ | $x$ |
| $3^hp^k$ | $\pi_{hk}X$ | $A$ |
| $3^hq$ | $\pi_{hq}X$ | $B$ |
| $p^kq$ | $\pi_{kq}X$ | $C$ |
| $q$ | $\pi_qX$ | $n$ |

Each entry divides an output belonging to $X$. Unique
factorization, $h,k\ge1$ and $(q,15p)=1$ show that the five
families are pairwise disjoint and have the stated sizes:
their positive or zero 3- and $p$-valuations and the presence
or absence of $q>1$ distinguish the rows. None contains
$1,3,p$. Removing $3p$ deletes at most one slot from the
second row. Removing the fixed $n_0$ deletes at most one
further slot, which can occur only in the first row. This
holds even when $d_0\notin X$ or $n_0$ divides another output.
Since $n\ge1$, SC326 gives

$$
|\mathcal N(X)|\ge x+A+B+C+n-2\ge2x
\qquad(\varnothing\ne X\subseteq\mathcal W).
\tag{SC328}
$$

Apply finite Hall to two demand copies of each source. Any
subset of demand copies has an underlying source set $X$,
the same neighbor union $\mathcal N(X)$, and at most $2x$
demands. Hence SC328 supplies two slots $s_{d,3},s_{d,4}$ per
source, all globally distinct. Use them in SC317. On fresh
second digits 3 and 4, a point of $R$ lies in an actual $C_d$;
the corresponding divisor-phase patch covers it. The other
three digits are covered by SC317's four common classes.
The source labels $25s_{d,t}$ differ from $25,75,25p,75p$
by SC327, and from one another by Hall. All have 5-height two,
so they are fresh against the depth-one base and the 5-free
retained family. This is a complete repair of cost $4+2r$.

Write any assigned slot uniquely as $s_{d,t}=3^e u$, with
$(u,15)=1$. The donor map and four extra original labels are

$$
D(3^e u)=3\cdot5^e u,\qquad
\{3p,15,15p,d_0\}\cap
 \{D(s_{d,t}):d\in\mathcal W,\ t=3,4\}=\varnothing.
\tag{SC329}
$$

The map is injective. Each donor divides its actual source,
so divisor closure supplies it as an original label. Since
every slot exceeds 1, every donor is nonpure of ternary height
one and is counted in $v_1$. The four displayed extra labels
also divide $d_0$ and are distinct, because $h_0,k_0\ge1$ and
$q_0>1$. Their inverse slots are $p,3,3p,n_0$, all globally
excluded. Thus the same original inventory pays the repair:

$$
\begin{aligned}
v_1&\ge2r+4,\\
K'&\le K-N_3-z+(1+v_2)+(4+2r)\\
  &=K+3+2r-v_1-z\le K-1-z<K.
\end{aligned}
\tag{SC330}
$$

The donor phases are not patch phases; every patch retains its
actual source phase. No additional original service is deleted,
and no $v_2$ label already used by the base is counted again.

### Twenty-two common classes leave one request per actual source

For the larger-menu repair, use the following relative
certificate. Its integer target is

$$
\zeta\bmod3\ne2,\qquad \zeta\bmod5\ne4.
\tag{SC331}
$$

| Relative modulus | First residue | Second residue |
|---|---:|---:|
| $5$ | $2$ | $3$ |
| $25$ | $10$ | $15$ |
| $125$ | $0$ | $75$ |
| $15$ | $1$ | $6$ |
| $75$ | $55$ | $70$ |
| $375$ | $25$ | $175$ |
| $45$ | $0$ | $15$ |
| $225$ | $25$ | $75$ |
| $1125$ | $100$ | $850$ |
| $135$ | $30$ | $120$ |
| $675$ | $345$ | $480$ |

All relative moduli divide $3375$. The complete-period check
has $1800$ target residues and zero uncovered target residues.
The following direct CRT proof establishes the coverage without
a cardinality-minimality claim.

If $\zeta$ is 2 or 3 modulo 5, the corresponding modulus-5
class covers it. If it is 1 modulo 5, its ternary root is
1 or 0, covered respectively by 1 or 6 modulo 15. It remains
to consider $\zeta\equiv0\pmod5$. The children 10 and 15
modulo 25 are covered directly.

On either child 5 or 20 modulo 25, ternary root 1 uses 55 or
70 modulo 75, respectively. At ternary root 0, the modulo-9
children 0 and 6 use 0 and 15 modulo 45. On the remaining
child 3 modulo 9, the modulo-27 children 3 and 12 use 30 and
120 modulo 135. The last child 21 modulo 27 uses 480 modulo
675 on child 5 modulo 25, and 345 modulo 675 on child 20.

The remaining branch is $\zeta\equiv0\pmod{25}$. Its children
0 and 75 modulo 125 are covered directly. On the other three
children 25, 50 and 100 modulo 125, ternary root 1 at the
first two uses 25 and 175 modulo 375, respectively. At child
100, its modulo-9 children 1 and 4 use 100 and 850 modulo
1125; child 7 uses 25 modulo 225. For ternary root 0 on
all three remaining modulo-125 children, modulo-9 children
0 and 6 use 0 and 15 modulo 45, and child 3 uses 75 modulo
225. These branches exhaust SC331.

Choose an integer representative $s$ and put $\delta=s-2$.
For $x\equiv1\pmod5$, write $u=(x-1)/5$ and define the unique
relative CRT coordinate modulo $3375$ by

$$
\zeta\equiv x-\delta\pmod{27},\qquad
\zeta\equiv u\pmod{125}.
\tag{SC332}
$$

Then $\zeta\bmod3\ne2$ exactly when $x\notin S$, and
$\zeta\bmod5\ne4$ exactly when $u\bmod5\ne4$. For a table
entry of relative modulus $3^\alpha5^\ell$ and residue $c$,
transport it to the CRT class

$$
x\equiv c+\delta\pmod{3^\alpha},\qquad
x\equiv1+5c\pmod{5^{\ell+1}}.
\tag{SC333}
$$

Omit the ternary condition when $\alpha=0$. In each row give
the first class no $p$-condition and the second the additional
condition $x\equiv b\pmod p$. Every point of $R$ satisfies
that condition. As $p>5$, these are single nonempty CRT
classes with numerical labels

$$
3^\alpha5^{\ell+1},\qquad
3^\alpha5^{\ell+1}p.
\tag{SC334}
$$

The 22 labels are distinct: their prime valuations recover
the row and the choice of $p$-condition. Their 5-heights range
from two to four, so they are fresh against the depth-one
base and the 5-free retained family. They cover all of
$[1]_5\cap R$ except possibly $u\equiv4\pmod5$, namely
$[21]_{25}\cap R$. Add one actual-source patch for each $d$:

$$
[21]_{25}\cap C_d\qquad(d\in\mathcal W),
\qquad\text{with modulus }25n_d.
\tag{SC335}
$$

The assumed complete service in SC324 covers that entire
last child. The labels $n_d$ are distinct because their
3-valuations and 3-free parts recover the original labels.
Every $q_d>1$ has a prime factor outside $\{3,5,p\}$, so
none of the labels $25n_d$ can equal a common label in SC334.
Their 5-height is two, again fresh against the base and
retained family. The total cost is $22+r$, with all integer
lifts and higher prime-power coordinates covered.

This packet uses actual extra-cofactor suppliers on the fifth
child. It does not assert that the common classes alone cover
the entire prime envelope, and therefore does not contradict
SC139's one-prime-envelope obstruction.

### At least fifteen sources: one original inventory pays the packet

Now suppose $r\ge15$ and take the projection counts of the
full $\mathcal W$ in SC325. Divisor closure supplies these
five pairwise disjoint families of original $v_1$ labels:

| Original labels | Index set | Number |
|---|---|---:|
| $3\cdot5^hp^kq$ | actual triples in $\mathcal W$ | $r$ |
| $3\cdot5^hp^k$ | $\pi_{hk}\mathcal W$ | $A$ |
| $3\cdot5^hq$ | $\pi_{hq}\mathcal W$ | $B$ |
| $3p^kq$ | $\pi_{kq}\mathcal W$ | $C$ |
| $3q$ | $\pi_q\mathcal W$ | $n$ |

Every label divides an actual source. The same valuation and
cofactor distinctions used for the slot table prove the
counts and disjointness. Two further actual labels $3p$ and
$15$ divide every source and occur in none of the five rows.
There is no separate count for $15p$, which can already
belong to the second row, or for a reserved source. Therefore

$$
v_1\ge r+A+B+C+n+2\ge r+22,
\tag{SC336}
$$

where SC326 gives $A+B+C\ge19$ and nonemptiness gives $n\ge1$.
The complete large-menu payment is

$$
\begin{aligned}
K'&\le K-N_3-z+(1+v_2)+(22+r)\\
  &=K+21+r-v_1-z\le K-1-z<K.
\end{aligned}
\tag{SC337}
$$

Both repairs use the same original cover, tree, full residual,
retained family and original inventory. One selects a repair
according to $r$; their donor budgets are not added. The
ranges $1\le r\le26$ and $r\ge15$ cover every nonempty finite
menu. Either repair contradicts EB1, proving the claimed
impossibility of SC324 without any restriction on the number
of columns, repeated heights, prime-power heights or overlaps
among the numerical cofactors.

The hypothesis $q>1$ is stronger than $m\ne p$ in Section 60:
pure $p^k$ cofactors with $k\ge2$ are outside this result.
Section 60 includes some such pure-power sources, so the two
results have overlapping scopes; this section does not contain
its entire range. Sources with $h=0$ and original ternary-height-zero
owners also remain outside the theorem. No complete outer-lower
service, SC227, designated group or privacy hypothesis is forced
here. Original ternary heights above two, the full paired-prime
branch and unrestricted Erdős #7 remain unresolved. This is an
ordinary mathematical deduction using the cited projection
inequality and actual-source repairs; no Lean verification or
new certificate enumeration is asserted.

## 62. Raw output slots leave a separate top inventory for complete repair

Keep Section 61's single original cover, prime branch, complete
group and fixed source tree. Fix $b\notin\{a,a_p\}$ and
$j\in\{3,6\}$, with $R=R_{b,j}$. Reuse the original inventories
from Sections 43--44:

$$
\chi(3^h m)=5^h m,\qquad
V_a=\{n>1:3^a\chi(n)\in D\},\qquad
v_a=|V_a|,\qquad N_3=2+v_1+v_2.
\tag{SC338}
$$

Here $m$ is coprime to $15$. The inventory $V_2$ counts all
nonpure original ternary-height-two labels, not just those with
live pullbacks. Let $\mathscr T$ be the numerical output indices
of all safe tops with nonempty pullback through the fixed tree,
including those inactive on the old $H$, and put
$\tau=|\mathscr T|$. Original uniqueness and divisor closure give
$\mathscr T\subseteq V_1$ and $\tau\le v_2$.

The literal SC285 base retains $K-N_3-z$ classes and adds exactly
$1+\tau$ classes with labels
$\{5\}\cup\{5n:n\in\mathscr T\}$. At index $p$, the transformed
lower replaces the removed partner. Its exact whole integer hole
is $[1]_5\cap R$.

### Preserve full source phases in each unoccupied raw slot

Choose actual $p$-bearing original height-zero suppliers or outer
lowers at first-$p$ phase $b$, with nonempty outputs
$C_d=[\eta_d]_{n_d}$. Original height zero here means ternary
height zero; their original 5-heights are unrestricted. Require
their $n_d$ to be distinct and to avoid $\mathscr T$. Each
$n_d=3^{h_d}m_d$ is 5-free and satisfies $p\mid m_d$. Add

$$
[1]_5\cap C_d,\qquad\text{with numerical label }5n_d.
\tag{SC339}
$$

These are single CRT classes at the full actual source phases.
Their labels are mutually distinct, avoid every base label, and
have 5-valuation one, so they are fresh against the retained
family. No height or cofactor projection changes their service.

Let $A$ be the union of the selected outputs. Let $f$ count their
indices in $V_1$ and $o$ those outside $V_1$, and put
$e=v_1-\tau-f$. The occupied top indices and the selected $V_1$
indices are disjoint, so $e\ge0$. The resulting family
$\mathcal B_{\rm raw}$ has exact hole and cardinality

$$
\begin{aligned}
\mathbb Z\setminus\bigcup\mathcal B_{\rm raw}
  &=[1]_5\cap\widehat R,\qquad \widehat R=R\setminus A,\\
|\mathcal B_{\rm raw}|
  &=K-(2+v_1+v_2)-z+(1+\tau)+f+o\\
  &=K-1-v_2-z-e+o.
\end{aligned}
\tag{SC340}
$$

A height-zero supplier outside $V_1$ is charged in $o$; no
corresponding original lower is assumed to exist. In particular,
$\widehat R=\varnothing$ and $o\le v_2+z+e$ already contradict
EB1 by this exact count.

One compatible choice first takes all actual outer lowers at $b$
whose indices avoid $\mathscr T$, then all height-zero outputs
with indices in $V_1\setminus\mathscr T$ not used by those lowers,
then a chosen subfamily of height-zero outputs outside $V_1$.
Original uniqueness within each role and these exclusions make
the selected numerical indices distinct. This installs only the
selected output union. In particular, a height-zero output whose
slot was assigned to a lower remains unserved unless another
selected class actually covers it.

### Existing same-height tops pay the remaining positive-height menu

For the following completion assume the stronger raw-budget
condition

$$
o\le z+e,\qquad \sigma=z+e-o\ge0,\qquad
|\mathcal B_{\rm raw}|=K-1-v_2-\sigma.
\tag{SC341}
$$

Suppose a finite family $\mathcal W$ of actual outer lowers
provides complete service for the remaining mask, with

$$
\begin{gathered}
d=3\cdot5^h p^k q,\qquad h,k\ge1,\qquad
q>1,\quad(q,15p)=1,\\
C_d=[\eta_d]_{3^h p^k q},\qquad
\widehat R\subseteq\bigcup_{d\in\mathcal W}C_d,\qquad
9\cdot5^h p^k q\in D\quad(d\in\mathcal W).
\end{gathered}
\tag{SC342}
$$

The last condition requires each supplier's same-height original
top to exist numerically. Its phase need not match the lower's,
and its pullback need not be live. In particular, it holds when
each supplier output index $n_d$, $d\in\mathcal W$, belongs
to $\mathscr T$. The construction
uses only $\widehat R\subseteq[b]_p$ and
$\widehat R\cap S=\varnothing$; no hull identity for this smaller
mask is assumed.

If $\widehat R$ is empty, SC341 already gives a strict descent.
Otherwise put $r=|\mathcal W|\ge1$. Reuse Section 61's two packet
constructions and its divisor-slot allocation, but pay them from
the original top inventory $V_2$.

For $1\le r\le26$, choose one source output $n_0$. The existing
two-copy Hall allocation gives two slots per source, all distinct,
excluding $1,3,p,3p,n_0$. For every assigned slot $s=3^a t$,
use the original top donor $9\cdot5^a t$. It divides the actual
top in SC342, so divisor closure supplies it. This map is
injective and every donor belongs to $V_2$. Four further donors
are present and excluded from that image:

$$
9p,\quad45,\quad45p,\quad9\chi(n_0),
\qquad v_2\ge2r+4.
\tag{SC343}
$$

Their indices are the four distinct forbidden slots
$p,3,3p,n_0$. Positivity of $h,k$ and $q>1$ separates them.
SC317's four common classes plus two actual-phase divisor
patches per source therefore cover the complete hole at cost
$4+2r\le v_2$.

For $r\ge15$, write $A_{hk},A_{hq},A_{kq},A_q$ for the
four projection counts of the same actual $\mathcal W$ used in
Section 61. The source tops and their divisors give the disjoint
families
$9\cdot5^h p^k q$, $9\cdot5^h p^k$,
$9\cdot5^h q$, $9p^k q$, and $9q$.
The two additional top labels $9p,45$ lie outside them. Thus the
same published projection inequality gives

$$
v_2\ge r+A_{hk}+A_{hq}+A_{kq}+A_q+2
     \ge r+22.
\tag{SC344}
$$

Section 61's 22 common classes and one actual-source patch per
supplier complete the hole at cost $22+r\le v_2$. These two
ranges cover every nonempty finite menu. Both packets have
5-valuation at least two, so all their labels are fresh against
the retained family and the entire depth-one raw/base family.
Their internal distinctness is the one proved in Section 61.
In either case the completed cover satisfies

$$
K'\le K-1-v_2-\sigma+c_{\rm packet}
   \le K-1-\sigma<K.
\tag{SC345}
$$

The accounting uses two disjoint parts of the original $N_3$
partition. The $\tau$ occupied top indices and the $f$ qualified
raw indices were charged to lower labels $3\chi(n)$ in $V_1$.
The new packet is paid by different original labels $9\chi(n)$
in $V_2$. Even when a donor's top output was already used at
depth one, its original top label was not counted in that
$V_1$ charge. Divisor tops need not have live output service,
and no donor phase is used as a patch phase.

Consequently, under SC341 the entire post-absorption residual
cannot be served by a menu satisfying SC342. This is a separate
top-inventory payment, not a reuse of Section 61's already-spent
lower-inventory conclusion. It applies to either inner color
separately and requires no common witness between them.
It does not combine this packet with a separately paid flat-menu
packet. Mixtures with original height-zero service, zero original
5-height or pure $p$-power cofactors, forcing the branch
hypotheses, and unrestricted odd distinct covering remain
unresolved. These are ordinary mathematical deductions and
reuse of the preceding packet constructions; no new Lean
verification or enumeration is asserted.

## 63. Occupied flat top slots leave residual witnesses at many prime roots

Keep Section 62's one original cover, ternary height two, prime
branch, complete group $J_a=\{3p,9p\}$ and fixed tree $\theta$.
Retain its inventories $V_1,V_2$, the full safe-top index set
$\mathscr T$ and $\tau=|\mathscr T|$. In particular, every safe
top with nonempty pullback is included, even when inactive on
the old $H$. The following choices and comparisons all concern
this same original family. No absence of outer lowers on $H$
is imposed until the final owner classification.

### One compatible raw selection at each first-prime root

For each $b\notin\{a,a_p\}$, consider actual $p$-bearing suppliers
at first-$p$ phase $b$ with nonempty outputs
$C_d=[\eta_d]_{n_d}$. An outer lower has original label
$3\chi(n_d)$ and old first-3 root 2. A height-zero supplier has
original label $\chi(n_d)$; height zero here means ternary height
zero, with no restriction on its original 5-height.

Let $n(\mathcal U)=\{n_d:d\in\mathcal U\}$ for a supplier
family. Define $\mathcal L_b^\circ$ to contain all these outer
lowers whose indices avoid $\mathscr T$, and let
$\mathcal H_b^\circ$ contain all these height-zero suppliers
whose indices lie in
$V_1\setminus(\mathscr T\cup n(\mathcal L_b^\circ))$.
Let $\mathcal O_b$ contain all these height-zero suppliers with
indices outside $V_1$. Put

$$
\begin{gathered}
f_b=|\mathcal L_b^\circ|+|\mathcal H_b^\circ|,\qquad
e_b=v_1-\tau-f_b\ge0,\\
\mathcal O_b^*\subseteq\mathcal O_b,\qquad
o_b=|\mathcal O_b^*|\le z+e_b,\qquad
\sigma_b=z+e_b-o_b\ge0,\\
A_b=\bigcup_{d\in\mathcal L_b^\circ\cup
                    \mathcal H_b^\circ\cup\mathcal O_b^*}C_d.
\end{gathered}
\tag{SC346}
$$

Choose $\mathcal O_b^*$ once at each root, for both inner colors.
An empty choice always satisfies its budget. Original numerical
uniqueness makes the indices distinct within each height role;
the displayed exclusions separate the roles. Moreover
$\mathscr T\subseteq V_1$, so the indices of $\mathcal O_b^*$
also avoid $\mathscr T$. Thus SC339 installs all of $A_b$
simultaneously at the deficient fresh root, with actual phases.

For either $j\in\{3,6\}$, SC340--341 give the exact hole and
count of this raw-installed family:

$$
\begin{aligned}
\mathbb Z\setminus\bigcup\mathcal B_{{\rm raw},b,j}
  &=[1]_5\cap\widehat R_{b,j},\qquad
    \widehat R_{b,j}=R_{b,j}\setminus A_b,\\
|\mathcal B_{{\rm raw},b,j}|
  &=K-1-v_2-\sigma_b.
\end{aligned}
\tag{SC347}
$$

Only the selected output union is installed. A height-zero
output whose numerical slot was assigned to a lower is not
included unless another selected output covers it. Its complete
remaining service stays in $\widehat R_{b,j}$.

### The flat suppliers at occupied top slots

Let $\mathcal G_b^\bullet$ consist of all actual outer lowers
at first-$p$ phase $b$ with original labels $d=3n_d$, where
$p\mid n_d$, $(n_d,15)=1$, and $n_d\in\mathscr T$. These have
original 5-height zero. Their outputs are the actual cofactor
classes $C_d=[\eta_d]_{n_d}$. Define

$$
\begin{gathered}
r_b=|\mathcal G_b^\bullet|,\qquad
G_b^\bullet=\bigcup_{d\in\mathcal G_b^\bullet}C_d,\\
Y_{b,j}=R_{b,j}\setminus(A_b\cup G_b^\bullet)
       =\widehat R_{b,j}\setminus G_b^\bullet.
\end{gathered}
\tag{SC348}
$$

The output indices of these flat suppliers are distinct across
all roots, since $n_d$ identifies the original label $3n_d$.
They differ from $1$ and $p$: all are $p$-bearing, and the unique
original $3p$ is the designated inner lower at phase $a$.
Every flat outer lower belongs either to $\mathcal L_b^\circ$
or to $\mathcal G_b^\bullet$. Hence the service removed in
SC348 contains all the flat outer-lower service of Section 58,
and can additionally remove the other selected raw-slot service.

If $Y_{b,j}=\varnothing$, the entire $\widehat R_{b,j}$ is
covered by $\mathcal G_b^\bullet$. It lies in $[b]_p$ and avoids
$S$. SC304 therefore completes this exact remaining liability
with its common-$p$ menu and actual flat-supplier menu. For
$r_b>0$, its cost and labels are

$$
c_b=6+3r_b,\qquad
\{25,75,225\}\cdot
   \bigl(\{1,p\}\cup n(\mathcal G_b^\bullet)\bigr).
\tag{SC349}
$$

The cofactors within a row are distinct and 3-free; the three
rows have different 3-valuations. Every packet label has
5-valuation two, so it is fresh against every depth-one raw
addition and base patch and every 5-free retained label.
No flat source phase changes. If $r_b=0$ and $Y_{b,j}$ is
empty, then $\widehat R_{b,j}$ is empty and SC347 already
gives a strict descent without a packet.

### Five actual top indices remain outside all these flat menus

The partner index $p$ lies in $\mathscr T$ and belongs to none
of the families $n(\mathcal G_b^\bullet)$, because its lower
is inner. Four further unavailable indices come from the two
nonpartner outer colors.

By SC271--272, all tops in those two colors are $p$-free, and
each color's full output union covers the transported hole
$H'$. Each color has at least two tops. Indeed, if one consisted
of a single output $[\eta]_n$, then it would contain the
nonempty full $R_{b,j}\subseteq H'$. Its modulus divides the
common output period, so SC286 would give
$n\mid\Gamma(R_{b,j})=p$. This contradicts $n>1$ and
$p\nmid n$. A color with no top cannot cover $R_{b,j}$ either.

Global top-label uniqueness makes these four $p$-free indices
distinct, including across the two colors. They differ from
$p$, and no $p$-bearing flat supplier can use them. Different
roots have disjoint flat-supplier indices because every
original $3n$ has one first-$p$ phase. Consequently, for any
four distinct roots outside $\{a,a_p\}$,

$$
\sum_b r_b\le\tau-5.
\tag{SC350}
$$

This reserve uses the complete $R_{b,j}$ and its SC286 hull,
not the smaller masks $\widehat R_{b,j}$ or $Y_{b,j}$. The top
at an occupied supplier index is counted numerically; its phase
is not identified with the lower's phase or with the point
being repaired.

### Four completed masks would pay one strict whole-cover repair

Suppose four distinct roots each have $Y_{b,j}=\varnothing$
for some inner color $j$, which may differ between roots.
Select a root with smallest $r=r_b$. The case $r=0$ already
contradicts SC347. For $r\ge1$, the one original top inventory
gives

$$
4r\le\sum_b r_b\le\tau-5\le v_2-5,
\qquad 6+3r\le4r+5\le v_2.
\tag{SC351}
$$

Execute only this root's raw installation and SC349 packet.
Its complete distinct odd output cover has
$K'\le K-1-v_2-\sigma_b+(6+3r)\le K-1-\sigma_b<K$ classes,
contrary to EB1. Therefore, for any choices in SC346,

$$
\boxed{
\#\{b\notin\{a,a_p\}:
       Y_{b,3}\ne\varnothing\ \text{and}\ Y_{b,6}\ne\varnothing\}
\ge p-5.
}
\tag{SC352}
$$

The other three roots certify the selected repair's affordability
through distinct actual flat lower labels and their occupied
top indices. No $f_b$, $e_b$, $o_b$ or $\sigma_b$ values are
summed across roots. The $v_2$ allowance is exactly the remainder
in SC347 after the raw construction's $V_1$ charge.

### The flat packet has one exact incomplete-service mask

For any fixed $b,j$, one can also apply SC349 without assuming
$Y_{b,j}$ empty. Use SC304's $\lambda_t=1+5t\pmod{25}$ and
the two roots $\alpha,\beta$ outside $S$. After installing the
raw classes and all these flat packet classes, the exact whole
integer hole is

$$
\begin{aligned}
&[\lambda_2]_{25}\cap Y_{b,j}\\
{}\cup{}&[\lambda_4]_{25}\cap[\alpha]_3\cap Y_{b,j}\\
{}\cup{}&[\lambda_4]_{25}\cap[\beta+6]_9\cap Y_{b,j}.
\end{aligned}
\tag{SC353}
$$

At a point of $\widehat R_{b,j}\cap G_b^\bullet$, both menus
supply SC304's complete service. At a point of $Y_{b,j}$ every
flat supplier entry fails, while the common-$p$ entries hold.
The unconditional and common entries cover children
$\lambda_0,\lambda_1,\lambda_3$. At $\lambda_4$ they cover
the modulo-9 children $\beta$ and $\beta+3$, leaving precisely
the last two terms of SC353. Child $\lambda_2$ has only the
failed flat entries.

The mask $Y_{b,j}$ is 5-free periodic. CRT makes its
$[\lambda_2]_{25}$ intersection nonempty whenever the mask is
nonempty. Thus this packet completes the raw residual exactly
when $Y_{b,j}$ is empty. SC353 asserts a coverage identity for
any packet size; a paid completion still needs the displayed
budget inequality.

### Actual owners of the surviving points

Now additionally impose $H\cap L_2=\varnothing$. For each root
counted in SC352 and each inner color, choose a point in
$Y_{b,j}$. The unchanged original point $F_c(y)$ has an owner.
SC287's same-source argument excludes top owners and $p$-free
owners, leaving a $p$-bearing height-zero original or an outer
lower at first-$p$ phase $b$.

Every surviving outer-lower owner must have

$$
d=3\cdot5^h m,\qquad h>0,\qquad
p\mid m,\quad(m,15)=1,\qquad 3^h m\in\mathscr T.
\tag{SC354}
$$

All flat lowers were removed from the mask by $A_b$ or
$G_b^\bullet$, and every positive-height lower whose index
avoids $\mathscr T$ was removed by $A_b$. The original top
$9\cdot5^h m$ in SC354 therefore exists and has a nonempty
safe pullback through the same tree. Its actual phase is not
asserted to match the lower or to own the surviving point.

A surviving height-zero owner instead has an index in
$\mathscr T$, an index assigned to a lower in
$\mathcal L_b^\circ$, or belongs to
$\mathcal O_b\setminus\mathcal O_b^*$. In the second case the
two same-index output APs have different phases. An intersection
would give one unchanged original source point belonging to
both comparable original classes $\chi(n)$ and $3\chi(n)$,
making the larger class redundant. Thus this is an actual phase
collision whose omitted service was retained in the mask.

SC352 and the packet comparison do not require the added
no-$L_2$ premise; it is used only for this owner classification.
The two inner witnesses need not coincide, and neither smaller
mask is asserted to retain hull $p$. This flat packet and the
positive-height packet of Section 62 are separate alternatives:
their costs and $v_2$ credits are not added, and neither result
pays an arbitrary mixture of the remaining roles. Original
height-zero service, the coupled surviving columns, forcing the
branch hypotheses, and unrestricted odd distinct covering remain
unresolved. These are ordinary deductions from the existing
raw-slot ledger, complete residuals and SC304 packet; no new
Lean verification or enumeration is asserted.

## 64. A fixed positive-height column pays both original source roles

Keep the single original cover, prime branch, complete group
$J_a=\{3p,9p\}$ and fixed tree of Sections 61--62. Fix
$b\notin\{a,a_p\}$ and an inner color $j$, and write
$R=R_{b,j}$. Every actual safe top with nonempty pullback is
included. The SC285 family covers exactly the complement of
$[1]_5\cap R$ and has size at most $K-1-v_1-z$. The full
residual lies in $[b]_p$, avoids the bought root $S=[s]_3$,
and is nonempty by SC286. Use the original inventories and
map $\chi$ from SC338.

Fix $k\ge1$ and $q>1$ with $(q,15p)=1$. Suppose a finite
family $\mathcal W$ of actual height-zero or outer-lower sources
provides complete service, with

$$
\begin{gathered}
R\subseteq\bigcup_{d\in\mathcal W}C_d,\qquad
d\in\{5^{h_d}p^kq,\ 3\cdot5^{h_d}p^kq\},\qquad h_d\ge1,\\
C_d=[\eta_d]_{n_d},\qquad n_d=3^{h_d}p^kq,\qquad
3\cdot5^{h_d}p^kq\in D\quad(d\in\mathcal W),\qquad
r=|\mathcal W|\ge1.
\end{gathered}
\tag{SC355}
$$

The source phases are the actual output phases at first-$p$
root $b$ in that same tree. The last membership in SC355
requires an actual lower counterpart for each height-zero
source; an outer lower supplies it itself. This qualification
concerns numerical inventory, without requiring a live or
phase-compatible counterpart.

Original-label uniqueness allows at most two sources at each
height, one of each role. Both actual sources remain separate
when their numerical output moduli agree. Their output APs are
disjoint: an intersection would put the same original point
$F_c(y)$ in two comparable original classes, making the larger
class redundant. The packet below only uses their separate
actual phases and complete service; it does not need this
disjointness as an additional premise.

### Four nested divisor ladders serve both roles

For a source of height $h$, use the divisor menu

$$
\begin{aligned}
\mathcal N_h
&=\{3^e u:0\le e\le h,\ u\in\{1,p^k,q,p^kq\}\}
       \setminus\{1,p,3,3p\},\\
|\mathcal N_h|
&=\begin{cases}4h,&k=1,\\4h+2,&k\ge2.\end{cases}
\end{aligned}
\tag{SC356}
$$

Unique factorization separates the four ladders, and every
entry divides the source's actual output modulus. The menus
are nested as $h$ increases. Before exclusions they have
$4(h+1)$ entries. For $k=1$ all four excluded slots occur;
for $k\ge2$ only $1,3$ occur.

For a nonempty source subset $X\subseteq\mathcal W$, let
$H_X=\max_{d\in X}h_d$. Its neighbor union is exactly
$\mathcal N_{H_X}$. At most two sources occur at each of the
heights $1,\ldots,H_X$, so

$$
\left|\bigcup_{d\in X}\mathcal N_{h_d}\right|
  =|\mathcal N_{H_X}|\ge4H_X\ge2|X|.
\tag{SC357}
$$

Finite Hall applied to two demand copies of every source
therefore supplies globally distinct slots
$s_{d,3},s_{d,4}\in\mathcal N_{h_d}$. A subset of demand
copies has the neighbor union of its underlying source set
and at most twice as many demands, so SC357 checks all Hall
inequalities, including the prefixes with both roles at every
height.

Apply SC317 with these slots, using Section 61's allowance
for $p$-free divisors. Its four common labels are
$25,25p,75,75p$. On each of the other two second-level fresh
5-roots, source $d$ receives the patch with its own phase
reduced to $s_{d,t}$ and numerical label $25s_{d,t}$. The
four forbidden slots prevent common-label collisions, and
Hall prevents all source-label collisions. Every new label
has 5-valuation two, so it is fresh against the depth-one
base and the 5-free retained family. Complete source service
gives a repair of the entire integer liability at cost
$4+2r$, including every higher prime-power tail.

### The lower inventory pays the complete original residual

For an assigned slot $s=3^e u$, use the original lower donor
$3\chi(s)=3\cdot5^e u$. It divides the actual counterpart
in SC355. The donor map is injective and every assigned
$s>1$, giving $2r$ distinct nonpure labels counted in $v_1$.

The existing support bound $P\ge29$, initial-segment support
and Report 385 GHA10 supply the actual lower $3t$ for every
$t\in\{17,19,23,29\}$. Choose one prime
$t\in\{17,19,23,29\}\setminus\{p,q\}$. Its index lies
outside all four ladders: $t$ differs from $1,p^k,q,p^kq$
and is 3-free. This remains true when $q$ is composite and
$t\mid q$, since each ladder retains the entire cofactor $q$.
The four additional original donors are

$$
\{3p,15,15p,3t\}\cap
\{3\chi(s_{d,i}):d\in\mathcal W,\ i=3,4\}
=\varnothing.
\tag{SC358}
$$

The first three divide every qualified counterpart and have
the excluded indices $p,3,3p$; the fourth has the outside
index $t$. They are pairwise distinct and nonpure. Thus

$$
\begin{aligned}
v_1&\ge2r+4,\\
K'&\le K-1-v_1-z+(4+2r)\le K-1-z<K.
\end{aligned}
\tag{SC359}
$$

Consequently no complete menu satisfying SC355 exists under
EB1. Both phases in a repeated output slot have been covered
with distinct fresh labels. No retained phase is changed,
and donor phases are not used as patch phases.

### An unspent lower index or an extra top pays the post-raw version

Now use the raw construction SC339--341, with the same
$p$-bearing raw-source restriction, distinct raw indices and
avoidance of $\mathscr T$. Thus
$e=v_1-\tau-f\ge0$, $\sigma=z+e-o$ and the exact remaining
hole is $[1]_5\cap\widehat R$. Assume the stronger raw-budget
condition and complete mixed menu

$$
\begin{gathered}
o\le z,\qquad \sigma\ge e\ge0,\qquad
|\mathcal B_{\rm raw}|=K-1-v_2-\sigma,\\
\widehat R\subseteq\bigcup_{d\in\mathcal W}C_d,\qquad
d\in\{5^{h_d}p^kq,\ 3\cdot5^{h_d}p^kq\},\qquad h_d\ge1,\\
C_d=[\eta_d]_{3^{h_d}p^kq},\qquad
9\cdot5^{h_d}p^kq\in D\quad(d\in\mathcal W).
\end{gathered}
\tag{SC360}
$$

Here $k,q$ are fixed as above. The numerical same-height top
condition implies the lower qualification, but requires no
live pullback or phase-compatible top. If $\widehat R$ is
empty, the raw count already gives descent. Otherwise put
$r=|\mathcal W|\ge1$ and apply the same four-ladder Hall
allocation and $4+2r$ packet to this entire remaining mask.
Only its containment in $[b]_p$ and avoidance of $S$ are used;
no hull identity is needed for $\widehat R$.

The actual top donors $9\chi(s_{d,i})$ divide the tops in
SC360 and give $2r$ different $V_2$ entries. Three further
top donors $9p,45,45p$ have the excluded indices $p,3,3p$,
so

$$
v_2\ge2r+3.
\tag{SC361}
$$

Use the same external support prime $t$ as in SC358. Its
actual lower gives $t\in V_1$. Since all selected raw indices
are $p$-bearing and $t\ne p$, none of the $f$ qualified raw
indices equals $t$. There are two exhaustive cases:

$$
\begin{array}{ll}
t\in\mathscr T:
  &9t\in D\text{ is an additional top donor},\quad
    v_2\ge2r+4,\\
t\notin\mathscr T:
  &e\ge1,\quad\sigma\ge e\ge1,\quad v_2\ge2r+3.
\end{array}
\tag{SC362}
$$

In the first case, the index $t$ is outside the four ladders
and outside $\{p,3,3p\}$, so this top donor has not already
been counted. In the second case, $t$ belongs to neither the
occupied top indices nor the selected qualified raw indices,
and hence contributes to the exact remainder $e$. In either
case the same original inventories satisfy

$$
v_2+\sigma\ge2r+4,\qquad
K'\le K-1-v_2-\sigma+(4+2r)\le K-1<K.
\tag{SC363}
$$

The packet's labels have 5-valuation two and remain fresh
against the entire raw/base family. The payment uses either
an additional original top or an unspent lower index already
present in SC340's exact remainder. It never spends an occupied
or selected lower index again. In particular, it covers $k=1$
with both roles present at every positive height.

The stronger condition $o\le z$ is essential to this argument:
SC341 alone permits the outside-$V_1$ raw additions to consume
the full remainder $e$. The result requires one fixed $q,k$,
positive original 5-heights, actual lower or top counterparts,
and complete service for the stated full residual. It does
not combine independently paid packets, force these source
conditions, or pay arbitrary mixtures of different columns.
Zero original 5-height, pure $p$-power cofactors, unqualified
height-zero service and unrestricted odd distinct covering
remain unresolved. These are ordinary deductions from the
actual-source packet and original inventories; no Lean
verification or new enumeration is asserted.

## 65. A mixed cofactor downset pays positive-height service with pure powers

Keep the same original EB1 cover of ternary height two, SC227 in
its prime branch $p>5$, the complete group $J_a=\{3p,9p\}$,
one fixed source tree, and all actual safe tops with nonempty
pullback. The selected mask is either the complete SC285 residual
$R=R_{b,j}$ or the exact post-absorption mask $\widehat R$ of
SC340. In both cases it lies in $[b]_p$ and avoids the bought
root $S$. Every containment below includes all integer lifts
and every higher prime-power tail.

Suppose one finite nonempty menu $\mathcal W$ of actual original
suppliers covers the selected mask. Each supplier has original
ternary height zero or is an outer lower, and its nonempty output
has first-$p$ phase $b$. Require distinct numerical outputs:

$$
\begin{gathered}
C_d=[\eta_d]_{n_d},\qquad n_d=3^hp^kq,\\
h,k\ge1,\qquad q\ge1,\qquad(q,15p)=1,\\
r=|\mathcal W|=|\{n_d:d\in\mathcal W\}|.
\end{gathered}
$$

The phases are the actual output phases through that tree.
The full numerical cofactor $q$ may equal 1 or be composite;
different cofactors may overlap or divide one another.
Distinct numerical outputs make the triples $(h,k,q)$ distinct.
This is an explicit hypothesis: two original roles with the same
output modulus and different phases cannot be counted as two
such triples. The positive $h$ is the original 5-height, not the
original ternary height.

Assume the selected mask is nonempty, so $r\ge1$. SC286 already
excludes an empty full residual; an empty post-absorption mask
under SC341 already gives a strict descent.

### Three pure-power labels are the complete numerical exception

Reuse the 22 common classes and actual-source patches of
SC331--SC335. Every source patch has numerical label $25n_d$.
The common labels have $p$-exponent zero or one; those of
5-height two have ternary exponents zero through three.
Consequently the exact collision condition in the stated
positive-height source range is

$$
25n_d\text{ is a common label}
\quad\Longleftrightarrow\quad
q=1,\ k=1,\ h\in\{1,2,3\}.
\tag{SC364}
$$

The exceptional output indices are $3p,9p,27p$; their lower
counterpart labels $3\chi(n)$ are $15p,75p,375p$.
Pure outputs with $k\ge2$ or $h\ge4$ are fresh against the
common labels. The explicit distinct-output hypothesis separates
all source patches from one another. No additional phase
condition is needed for numerical freshness.

For menus consisting entirely of outer lowers, those three
counterparts are the actual source labels. Each has one actual
first-$p$ root, so at most three roots can have an outer-lower
menu containing an exceptional label. This count is restricted
to that role; numerical output indices can recur across different
roles. It supplies no complete service at any other root.

### Count the coordinate downsets in one original inventory

Assume every $n_d$ avoids $\{3p,9p,27p\}$. Fix
$i\in\{1,2\}$ and use SC338's inventories $V_i$,
$v_i=|V_i|$. Explicitly require the original counterpart

$$
3^i\chi(n_d)=3^i5^hp^kq\in D
\qquad(d\in\mathcal W).
$$

For $i=1$ this lower qualification is automatic for an actual
outer lower, but is an additional hypothesis for an original
height-zero supplier. For $i=2$ the top counterpart must exist,
as in SC342. Its phase need not match the source's, and its
pullback need not be live. The counterpart supplies only an
original inventory entry; it never supplies a replacement phase.

For each occurring numerical $q$, let $\mathcal S_q$ be the
set of its source pairs $(h,k)$, and define the downset

$$
\mathcal D_q=
\{(e,f)\in\mathbb N_0^2:
  \exists(h,k)\in\mathcal S_q,\ e\le h,\ f\le k\}.
$$

Put $\mathcal S_1=\mathcal D_1=\varnothing$ and $r_0=0$ if no
pure source occurs. Let $Q_+$ be the set of occurring cofactors
$q>1$ and $\mathcal D_*=\bigcup_q\mathcal D_q$. Divisor closure supplies
all the following original donor labels:

$$
\begin{array}{ll}
3^i5^ep^fq,
  &(q\in Q_+,\ (e,f)\in\mathcal D_q),\\
3^i5^ep^f,
  &((e,f)\in\mathcal D_*\setminus\{(0,0)\}).
\end{array}
$$

For $q>1$, even $(e,f)=(0,0)$ gives a nonpure original counted
in $v_i$. Different numerical $q$ give disjoint families:
removing the factors $3,5,p$ recovers $q$, including when one
cofactor divides another. The second family is disjoint from
all of them. Its excluded unit-coordinate member is the pure
original $3^i$, which does not belong to $V_i$. Therefore

$$
v_i\ge |\mathcal D_*|-1+
                  \sum_{q\in Q_+}|\mathcal D_q|.
\tag{SC365}
$$

Every donor divides the qualified original counterpart
$3^i\chi(n_d)$ of a source.
Other proper cofactor divisors can supply additional labels;
SC365 does not count them. The bound uses one original $D$ and
one fixed inventory $V_i$.

Let $H_*,J_*$ be the maximum $h,k$ across $\mathcal W$, and
let $H_q,J_q$ be the respective maxima within $\mathcal S_q$
for $q\in Q_+$. Define

$$
\begin{gathered}
t=\min(H_*,3),\qquad n=|Q_+|,\\
\Delta=H_*+J_*+t+
       \sum_{q\in Q_+}(H_q+J_q+1).
\end{gathered}
\tag{SC366}
$$

The axes of $\mathcal D_*$ contain $H_*+J_*+1$ points.
Its positive quadrant contains all $r_0=|\mathcal S_1|$
pure-source pairs, as well as the $t$ points
$(1,1),\ldots,(t,1)$. These points are absent from
$\mathcal S_1$ by SC364's exclusions and belong to
$\mathcal D_*$ because a maximum-height source has $k\ge1$.
Thus $|\mathcal D_*|-1\ge r_0+H_*+J_*+t$.
For each $q\in Q_+$, its $H_q+J_q+1$ axis points are disjoint
from its $r_q=|\mathcal S_q|$ positive source pairs, so
$|\mathcal D_q|\ge r_q+H_q+J_q+1$. Since
$r=r_0+\sum_{q\in Q_+}r_q$, SC365 gives

$$
v_i\ge r+\Delta.
\tag{SC367}
$$

The heights, prime-power heights and cofactors can all repeat.
No independent optimization of the coordinate sets or original
inventories is used. This count adds no matching hypothesis
to the complete actual service.

### Seventy-nine sources automatically supply the required margin

For every menu satisfying the exclusions above,

$$
r\ge79\quad\Longrightarrow\quad
\Delta\ge22\quad\Longrightarrow\quad v_i\ge r+22.
\tag{SC368}
$$

To prove the threshold, write
$U=H_*+\sum_{q\in Q_+}H_q$ and
$V=J_*+\sum_{q\in Q_+}J_q$. The pure-source pairs lie in
the $H_*\times J_*$ rectangle with the $t$ excluded points
removed. Each other layer has $r_q\le H_qJ_q$. Hence

$$
r\le H_*J_*-t+\sum_{q\in Q_+}H_qJ_q\le UV-t.
\tag{SC369}
$$

If $H_*\ge3$ and $\Delta\le21$, then $t=3$ and
$U+V=\Delta-3-n\le18$. AM--GM gives $UV\le81$, so $r\le78$.
If $H_*=2$, every $H_q\le2$ and the direct count gives
$r\le2V-2$. Now $U\ge2+n$ and
$\Delta=U+V+2+n\le21$ imply $V\le17-2n$, hence $r\le32$.
If $H_*=1$, every $H_q=1$, so $U=1+n$ and $r\le V-1$.
The bound $\Delta=V+2+2n\le21$ gives $r\le18$.
These cases prove SC368.

The sufficient threshold uses only the displayed donors. For
example, the pure $9\times9$ positive grid with $(1,1),(2,1),
(3,1)$ removed has 78 source indices and 99 displayed nonunit
donor indices, a margin of 21. This is an inventory example,
not an actual EB1 realization or an optimality claim for
repairs. In an actual source, at least three forced original
labels $3\ell$, with
$\ell\in\{17,19,23,29\}\setminus\{p\}$, lie outside that
pure grid and give additional $V_1$ donors. SC368 does not use
those labels or any unspent raw slack.

### The same packet pays the complete selected mask

Under SC364's exclusions, SC331--SC335 supplies one packet of
$22+r$ classes. The common classes cover the first four fresh
children of the entire selected mask, and
$[21]_{25}\cap C_d$ for $d\in\mathcal W$ covers the last.
All labels are distinct and have 5-height at least two, so
are fresh against every depth-one raw/base class and the
5-free retained family. Every source phase, integer lift and
higher prime-power coordinate is preserved.

On the full SC285 residual require the lower counterparts and
use $i=1$. Whenever $\Delta\ge22$, SC367 gives

$$
\begin{aligned}
K'&\le K-N_3-z+(1+v_2)+(22+r)\\
  &=K+21+r-v_1-z\le K-1-z<K.
\end{aligned}
\tag{SC370}
$$

On the exact post-absorption mask, assume SC341, the
qualified original top counterparts and $\Delta\ge22$, and use $i=2$. Then

$$
\begin{aligned}
|\mathcal B_{\rm raw}|&=K-1-v_2-\sigma,
   \qquad\sigma\ge0,\\
K'&\le K-1-v_2-\sigma+(22+r)
   \le K-1-\sigma<K.
\end{aligned}
\tag{SC371}
$$

These are two applications of one donor count; the two
inventories are not added in either payment. SC368 excludes
all the stipulated complete menus with $r\ge79$, and the
explicit condition $\Delta\ge22$ can also pay smaller menus.
The result allows pure $p^k$ outputs mixed with arbitrary
extra-cofactor outputs and both stated original roles, while
retaining distinct numerical outputs, qualified counterparts
and the three numerical exceptions.

### Small-menu interfaces still require more than the source count

A universal packet of cost at most $4r+5$ using only new
classes of 5-height at least two fails at $r=1$ for the
abstract post-absorption mask interface. Let that mask be a
complete class $C$ modulo $3p$, outside the bought root and
at first-$p$ phase $b$, serviced by output $n=3p$. Its original
lower counterpart label is $15p$, and the liability is
$[1]_5\cap C$. Pulling back $x=1+5y$ divides every nonempty
new numerical label by 5 injectively, giving a cover of a
complete class modulo $3p$ by distinct 5-bearing labels.
SC137 therefore requires at least eleven classes. The proposed
allowance $4r+5$ would be nine.

This does not realize the mask in an EB1 cover. SC286 rules
out such one-source service for the full $R$, whose hull is
$p$. The exact raw mask can have a different hull; SC341 gives
no replacement hull identity. Additional actual geometry,
original budget, a base exchange or an available depth-one
slot remains outside this lower-bound interface.

There is also a numerical obstruction to reducing all small
mixed menus to SC317's two-request divisor test. For distinct
primes $q_1,q_2\notin\{3,5,p\}$, the four flat outputs
$pq_1,p^2q_1,pq_2,p^2q_2$ have just seven divisor slots after
excluding $1,3,p,3p$. Adding the positive-height output
$3pq_1$ supplies only two further slots, $3q_1,3pq_1$.
The capacities eight and ten required for four and five
sources therefore fail. These are allocation examples, not
whole-cover counterexamples; SC304 already supplies a
different packet for the entirely flat menu.

SC370--SC371 leave open menus containing the output indices
$3p,9p,27p$, smaller menus with insufficient $\Delta$,
unqualified original height-zero ownership, repeated numerical
outputs with different phases, zero original 5-height, forcing
complete service or the branch hypotheses, and unrestricted
odd distinct covering. These are ordinary mathematical deductions using
the existing packets and original divisor closure; no new
Lean verification is asserted.

## 66. A virtual partner removes the actual lower phase condition

Use one original EB1 whole cover of ternary height two, one
fixed source tree, and the retained family $\mathcal F_0$ of
Section 41. Choose height-zero representatives wherever they
survive, absorbing the original pure-5 output in the bought root
$S=[s]_3$ when necessary. Thus the complete hole
$H=\mathbb Z\setminus\bigcup\mathcal F_0$ avoids every
height-zero output. Let $N_0=3^BM$ be the construction's common
5-free output period. Retained numerical labels are distinct
odd 5-free nonunits. The original counts
remain $N_3=2+v_1+v_2$ and
$|\mathcal F_0|=K-N_3-z$, with $z\ge0$. Every safe top menu
contains all nonempty actual pullbacks, including those inactive
on this $H$. Write $\mathcal T_u$ for its family and $T_u$ for
its union. Let $\mathscr T$ be their numerical output-index set,
$\tau=|\mathscr T|$; then $\mathscr T\subseteq V_1$ and
$\tau\le v_2$ by the original supplier indexing and divisor
closure. A numerical top index has only one original supplier.

The following entrance condition replaces the actual lower
and complete phase-group assumptions of SC227 and Section 55:

$$
\begin{gathered}
p>5\text{ prime},\qquad c\in\{2,5,8\},\qquad
\{u,v\}=\{2,5,8\}\setminus\{c\},\\
C_*=[a]_p\in\mathcal T_c
   \text{ is the actual output of original }9p,\\
H\subseteq T_u\cap T_v,\qquad
E_j=H\setminus T_j\ (j=3,6),\qquad
E_3\cup E_6\subseteq[a]_p.
\end{gathered}
\tag{SC372}
$$

Neither $H\subseteq T_c$, an actual inner lower enclosing the
deficits, phase equality between original $3p$ and $9p$, nor
$J_a=\{3p,9p\}$ is assumed. The original numerical label $3p$
exists by divisor closure, but it is not used as the enclosing
AP. The two nonpartner outer menus may contain $p$-bearing
tops.

### Three complete outer menus reach this entrance at a prime hull

Suppose instead that all three outer menus cover $H$. If $H$
is empty, retention already gives a strict whole-cover descent.
Otherwise SC194's four-complete-top construction shows that
both $E_3,E_6$ are nonempty. Put $E=E_3\cup E_6$, and suppose
its complete congruence hull in the common 5-free period is
the prime $p>5$. Thus $E\subseteq[a]_p$ for one residue
$a$ modulo $p$.

The virtual-enclosure argument preceding SC229 still applies
without an actual enclosing lower. Use $[a]_p$ as the fourth
menu's enclosure. If the unique top index $p$ is absent, or
is in an inner color that can be omitted, the resulting
distinct patch costs at most $2+v_2$. Nonempty $H$ and a
complete outer menu give $v_2\ge1$, and divisor closure gives
$v_1\ge v_2$. Hence $2+v_2<N_3+z$, a contradiction.

The top therefore exists in an outer color $c$. Remove that
top from its root and transfer the omitted inner menu there.
The exact remaining service is $D_p\cap E_j$ as in SC229,
where $D_p$ is the responsibility of that whole outer color
after removing its index-$p$ top. If it were empty, the
base cost $1+v_2$ would give descent. Since $T_c$ covers $H$,
every point of $D_p$ lies in the deleted top. A residual
point also lies in $E\subseteq[a]_p$. The deleted top has
modulus $p$, so its actual AP is exactly $[a]_p$. Consequently

$$
\left.
\begin{gathered}
H\subseteq T_2\cap T_5\cap T_8,\\
\Gamma(E_3\cup E_6)=p>5\text{ prime}
\end{gathered}
\right\}
\quad\Longrightarrow\quad\text{SC372}.
\tag{SC373}
$$

This reuses the complete-enclosure collision argument with
the count reserve supplied by the nonempty outer menu. It
does not rephase any original class. The hull-one and ternary
hull alternatives are not treated by SC373, and three complete
outer menus have not been forced for a general original source.

### Move the nonpartner outer menus with the retained family

Assume SC372. Fix $b\ne a$ and $j\in\{3,6\}$, with $k$ the
other inner color. Let $\phi_b$ interchange the first-$p$
digits $a,b$, preserving every higher $p$-digit and every
other output coordinate. It acts on the full common period
and extends periodically to integers. A $p$-free AP is fixed.
On any AP whose modulus contains $p$, its first digit is
fixed, so the operation is one constant CRT translation on
that AP. Thus every actual output remains an AP of the same
numerical modulus. Set

$$
\mathcal F'_0=\phi_b(\mathcal F_0),\qquad
H'=\phi_b(H),\qquad B_b=[b]_p.
\tag{SC374}
$$

Keep $\mathcal T_c$ unchanged. Transport the two nonpartner
outer menus and both inner menus by $\phi_b$. A candidate
family retains $\mathcal F'_0$ and uses these fresh-root
placements; placing an AP $C$ at root $r$ means $[r]_5\cap C$:

| Fresh first-5 root | Family placed at that root |
|---|---|
| $0$ | the whole root $[0]_5$ |
| $1$ | $(\mathcal T_c\setminus\{C_*\})\cup\phi_b(\mathcal T_j)$ |
| $2$ | $\phi_b(\mathcal T_u)$ |
| $3$ | $\phi_b(\mathcal T_v)$ |
| $4$ | $\{B_b\}\cup\phi_b(\mathcal T_k)$ |

$B_b$ is a virtual repair AP, not an asserted output of
original $3p$. These are specified transformations of one
source, assembled into one candidate integer family; no new
common original configuration is assumed for the transformed
menus.

Outside $H'$, retention covers every integer. At roots 2 and
3, SC372 gives $H'\subseteq\phi_b(T_u)\cap\phi_b(T_v)$.
At root 4, $H'\setminus\phi_b(T_k)=\phi_b(E_k)\subseteq B_b$.
At root 1 the exact missing service is

$$
\begin{aligned}
R_{b,j}
&=H'\setminus\left(
  \bigcup(\mathcal T_c\setminus\{C_*\})\cup\phi_b(T_j)
  \right)\\
&=\phi_b(E_j)\setminus T_c\subseteq[b]_p,\\
\mathbb Z\setminus\bigcup\mathcal B_{b,j}
&=[1]_5\cap R_{b,j}.
\end{aligned}
\tag{SC375}
$$

The second equality uses the disjoint phases
$\phi_b(E_j)\subseteq[b]_p$ and $C_*=[a]_p$. In particular,
there is no extra liability at the new $a$-fiber. Completeness
of $T_c$ on the old $H$ was not needed: the transferred inner
menu covers the entire complement of $\phi_b(E_j)$ in $H'$.

### The numerical interface and full residual hull are unchanged

Every safe top occurs once, except $C_*$, whose index $p$ is
replaced by $B_b$. The numerical labels and exact count are

$$
\begin{aligned}
\operatorname{Mod}(\mathcal B_{b,j})
 &=\operatorname{Mod}(\mathcal F_0)
     \cup\{5\}\cup\{5n:n\in\mathscr T\},\\
|\mathcal B_{b,j}|
 &=|\mathcal F_0|+1+\tau\\
 &=K-1-v_1-v_2-z+\tau\le K-1-v_1-z.
\end{aligned}
\tag{SC376}
$$

Retained labels are 5-free; every other label has 5-valuation
one. Top indices are distinct and exceed 1, so no $5n$ equals
5. Removal of $C_*$ leaves exactly one use of $5p$. All
labels are odd and exceed 1.

An empty $R_{b,j}$ would contradict EB1 through SC375--SC376.
Also $R_{b,j}\subseteq H'$ avoids $S$, which $\phi_b$ fixes.
The original inventory bound $v_1\ge11$ of SC231 does not
use phase alignment: its inputs are NF66, the support bound,
the original pure 9 and $v_2\le v_1$. Reuse the complete
enclosure packets SC136--SC137, shifted below fresh root 1
by SC233. A hull strictly larger than $p$ has either a
divisor $3p$ or a composite 3-free divisor; respectively the
eleven- or nine-class packet would cover the entire residual.
Its labels have 5-valuation at least two and its cost is at
most $v_1$, so SC376 would give a strict descent. Therefore

$$
R_{b,j}\ne\varnothing,\qquad
R_{b,j}\cap S=\varnothing,\qquad
\Gamma_{N_0}(R_{b,j})=p,
\qquad b\ne a,\ j=3,6.
\tag{SC377}
$$

This concerns each complete residual, not selected witnesses
or a claim that it fills its enclosing AP.

### Owner comparison still uses the unchanged original source

For this paragraph add $H\cap L_2=\varnothing$. Let
$\mathcal A_b$ contain all actual $p$-bearing suppliers at
first-$p$ phase $b$ whose original ternary height is zero,
or is one at outer first-3 root 2. Keep original identities
and actual output phases, even when different roles share
one numerical output index.

For $y\in R_{b,j}$, put $x=\phi_b(y)\in E_j\subseteq H$.
Apply the unchanged original source map $F_c$ to $y$.
Whole original coverage gives an owner. Since $y\notin T_c$
and every nonempty top pullback of color $c$ was retained
in that menu, its owner has height zero or is an outer lower.
If it were $p$-free, membership would be unchanged between
$F_c(y)$ and $F_c(x)$. Height-zero priority would then put
$x$ in the retained union, or the outer lower would put it
in $H\cap L_2$, both contradictions. Hence

$$
H\cap L_2=\varnothing
\quad\Longrightarrow\quad
R_{b,3}\cup R_{b,6}\subseteq
\bigcup_{d\in\mathcal A_b}C_d.
\tag{SC378}
$$

This exhaustive role check is not needed when complete
service by a specified actual menu is separately assumed.
No supplier-count bound that excludes original $3p$ from
an outer role is imported: its phase and root are unrestricted
here.

### The established menu repairs use the same two separate inventories

If a full $R_{b,j}$ is served by actual outer lowers of the
form SC324, Section 61's two alternative packets apply
without changing their constructions or donor counts.
Their inputs are complete service, $R\subseteq[b]_p$,
$R\cap S=\varnothing$, distinct actual output indices and
the original $V_1$ divisor inventory. The donor $3p$ is
used only as a numerical label, not as a patch phase.
Moving nonpartner outer menus changes none of the base
labels or these original divisibilities. The chosen packet
has cost at most $v_1$, giving

$$
K'\le |\mathcal B_{b,j}|+v_1
   =K-1-z-(v_2-\tau)<K.
\tag{SC379}
$$

For raw absorption, choose actual $p$-bearing height-zero or
outer-lower suppliers at $b$ with distinct indices outside
$\mathscr T$, as in SC339. Let $A$ be their actual output union, let $f$
count selected indices in $V_1$, let $o$ count those outside,
and put $e=v_1-\tau-f\ge0$. Adding $[1]_5\cap C_d$ at each
selected index gives exactly

$$
\begin{aligned}
\widehat R&=R_{b,j}\setminus A,\\
\mathbb Z\setminus\bigcup\mathcal B_{\rm raw}
  &=[1]_5\cap\widehat R,\\
|\mathcal B_{\rm raw}|&=K-1-v_2-z-e+o.
\end{aligned}
\tag{SC380}
$$

The occupied numerical interface is precisely SC376. No
lower counterpart is assumed for a height-zero supplier
counted in $o$. Under $o\le z+e$, set
$\sigma=z+e-o\ge0$. If the complete remaining mask has
SC342's actual positive-height extra-cofactor lower service,
with every required same-height original top in $D$, reuse
SC343--SC345's separate $V_2$ payment. No top phase alignment
or live top pullback is needed for those numerical donors.
The completion has cost at most $v_2$ and fresh 5-valuation
at least two, hence

$$
K'\le K-1-v_2-\sigma+v_2=K-1-\sigma<K.
\tag{SC381}
$$

For example, let $\mathcal W_b^{\rm top}$ consist of every
actual outer lower at $b$ satisfying SC342's numerical shape
and same-height-top requirement. For every admissible raw
selection with $o\le z+e$, EB1 forces the concrete remainder

$$
\widehat R\setminus
\bigcup_{d\in\mathcal W_b^{\rm top}}C_d\ne\varnothing.
\tag{SC382}
$$

Otherwise this finite menu would complete the mask and SC381
would contradict minimality. Under SC378's extra lower-exclusion
condition, a remaining point has actual owners outside that
qualified menu: height-zero service, zero original 5-height,
pure-$p$-power cofactors or positive-height sources without the
required original top. The count and every selected phase
belong to the same original cover throughout.

The virtual construction does not establish the complete
phase-group condition, the $p$-free nature of nonpartner
outer colors, the original private-region product formulas
or the reverse-transport inclusions of SC288--SC313. None
is needed for SC375--SC382. Forcing SC372, the hull-one and
remaining ternary-hull branches, complete mixed-role service
with affordable raw selection, and original ternary heights
above two remain unresolved. This is an ordinary source-qualified construction
and reuse of existing packets, not a Lean-verified result or
a resolution of unrestricted Erdős #7.

## 67. Extra-cofactor menus leave one original donor unspent

The packets of Sections 61--62 admit a stronger payment bound.
Use the same actual outer-lower menu, with distinct numerical
outputs
$n_d=3^{h_d}p^{k_d}q_d$, where $h_d,k_d\ge1$, $q_d>1$ and
$(q_d,15p)=1$. Every phase belongs to the one original source.
Assume their actual output union covers the complete selected
mask in $[b]_p\setminus S$, with the depth-one base interface
used by those packets.
For $i=1$, the actual lower itself gives
$3\chi(n_d)\in D$. For $i=2$, additionally require every
same-height original top $9\chi(n_d)\in D$ as in SC342.
Write $r\ge1$ for the number of sources. Then the existing
complete-mask packet can be chosen with cost

$$
c_{\rm packet}\le v_i-1.
\tag{SC383}
$$

No packet or source phase changes. The extra unit comes from
reserving one more original divisor in the small-menu case
and using the next integral projection bound in the large case.

### Reserve the cofactor of one actual source

Suppose $1\le r\le15$ and fix $d_0$, with output $n_0$ and
cofactor $q_0$. For a nonempty source subset $X$, use the
same projections as SC325, with $x=|X|$ and
$A+B+C=|\pi_{hk}X|+|\pi_{hq}X|+|\pi_{kq}X|$.
The published projection inequality gives $x^2\le ABC$.
In this range,

$$
A+B+C\ge x+2.
\tag{SC384}
$$

Indeed, the opposite integral bound would imply
$27x^2\le(x+1)^3$ by AM--GM, whereas for $1\le x\le15$

$$
(x+1)^3=x^3+3x^2+3x+1
 \le(x+7)x^2\le22x^2<27x^2.
$$

Give each source the divisor menu

$$
\mathcal N_d=\{t:t\mid n_d\}
 \setminus\{1,3,p,3p,n_0,q_0\}.
\tag{SC385}
$$

The five disjoint projection families in Section 61 have
$x+A+B+C+n$ entries, where $n=|\pi_qX|\ge1$. None contains
$1,3,p$. Deleting $3p,n_0,q_0$ removes at most three entries
from this union, even if the chosen $d_0$ is not in $X$ or
its cofactor divides other source cofactors. Consequently

$$
\left|\bigcup_{d\in X}\mathcal N_d\right|
 \ge x+A+B+C+n-3\ge2x.
\tag{SC386}
$$

The existing two-copy Hall allocation therefore still assigns
two distinct divisor slots to every actual source. Use exactly
SC317's four-common-class packet and those actual-phase
divisor patches, of total cost $4+2r$.

For each assigned slot $t$ count the original donor
$3^i\chi(t)$. It divides the qualified original counterpart,
and the donor map is injective. Five further original donors
have the excluded indices $p,3,3p,n_0,q_0$:

$$
3^ip,\quad3^i5,\quad3^i5p,\quad
3^i\chi(n_0),\quad3^iq_0.
\tag{SC387}
$$

They all divide that same qualified counterpart. They are
distinct because $h_0,k_0\ge1$, $q_0>1$ and $(q_0,15p)=1$.
None is pure ternary and none is an assigned donor. Hence
$v_i\ge2r+5$, proving SC383 in this range. These original
donor phases are not used as patch phases.

### Sixteen sources force the next integral margin

For $r\ge16$, apply the projection inequality to the whole
menu. A projection sum at most 19 would give
$27r^2\le19^3=6859$, contrary to
$27\cdot16^2=6912$. Thus $A+B+C\ge20$. The same five
original donor families and two additional labels used in
SC336 or SC344 give

$$
v_i\ge r+A+B+C+n+2\ge r+23.
\tag{SC388}
$$

Reuse the $22+r$ packet of SC331--SC335. It again costs at
most $v_i-1$. The ranges $r\le15$ and $r\ge16$ exhaust all
nonempty finite menus. Each packet has 5-valuation at least
two and remains fresh against any depth-one base with the
same interface. No two packet budgets are added.

### One additional raw source is affordable

For either the original raw construction SC340 or the virtual
partner construction SC380, keep distinct selected raw
indices outside $\mathscr T$ and their actual phases. Its
exact count is $K-1-v_2-z-e+o$. If the complete remaining
mask is nonempty and has SC342's qualified top service,
SC383 gives

$$
\begin{aligned}
o&\le z+e+1,\qquad \epsilon=z+e+1-o\ge0,\\
K'&\le K-1-v_2-z-e+o+(v_2-1)
     =K-1-\epsilon<K.
\end{aligned}
\tag{SC389}
$$

If the mask is empty, these two base constructions have
the actual $9p$ top, so $v_2\ge1$ and their raw count is
at most $K-v_2<K$ under the same bound. Thus one may replace
the raw-budget hypothesis $o\le z+e$ by $o\le z+e+1$ for
this particular completion. It does not install a second
phase at an occupied numerical index or supply a missing
original top.

### An absent top slot can pay a virtual enclosure

Keep Section 66's original source, retained family, full
menus and inventories, but replace its entrance SC372 by the
following assumptions. For some prime $p>5$ dividing
$N_0$, residue $a$
and two outer colors $u,v$, with remaining outer color $c$,

$$
H\subseteq T_u\cap T_v,\qquad
E_3\cup E_6\subseteq[a]_p,\qquad
p\notin\mathscr T.
\tag{SC390}
$$

No actual top partner is postulated. For any $b\ne a$ and
inner $j$, use Section 66's placement table, placing the
entire unchanged $\mathcal T_c$ at root 1 alongside
$\phi_b(\mathcal T_j)$. There is no partner to remove.
The other roots and the retained family are exactly as in
that table, including the virtual $[b]_p$ at root 4.
The new numerical label $5p$ is available by SC390.

The same rootwise identities give the complete hole and count

$$
\begin{aligned}
\mathbb Z\setminus\bigcup\mathcal B
  &=[1]_5\cap R_{b,j},\qquad
    R_{b,j}=\phi_b(E_j)\setminus T_c,\\
|\mathcal B|
  &=|\mathcal F_0|+2+\tau
    =K-v_1-v_2-z+\tau.
\end{aligned}
\tag{SC391}
$$

Every top index is used once and the virtual index $p$ is
used once. Retained labels are 5-free, all added labels have
5-valuation one, and no top index is 1 or $p$. Thus all
candidate labels are distinct odd nonunits. The residual
still lies in $[b]_p\setminus S$; no interpretation as an
original private region is added.

If $R_{b,j}$ has complete actual outer-lower service of
SC324's positive-height extra-cofactor form, apply SC383
with $i=1$. The original inventory now pays both the existing
packet and the additional virtual slot:

$$
K'\le K-v_1-v_2-z+\tau+(v_1-1)
   =K-1-z-(v_2-\tau)<K.
\tag{SC392}
$$

An empty residual already contradicts SC391 and $v_1\ge11$.
As in SC377, a larger-than-$p$ residual hull would be paid
by a nine- or eleven-class enclosure packet, using the
stronger global $v_1\ge15$ from SC257, $P\ge29$ and pure
original 9. Thus the complete residual has hull $p$, but the
packet comparison SC392 only needs its containment and
avoidance of $S$.

SC390 is a separate absent-slot entrance; it does not settle
the cases where a top already occupies $p$ at an unsuitable
color or phase. Neither SC390 nor complete qualified lower
service has been forced from a general cover. The extra unit
does not resolve arbitrary mixed roles, missing counterparts
or higher original ternary height. These are ordinary
deductions from the existing projection inequality and packet
constructions; no new Lean verification or enumeration is
asserted.

## 68. Ternary residuals force original 5-heights and pay small menus

Use Section 66's one original EB1 cover of ternary height two,
fixed tree $\theta$, height-zero-priority retained family
$\mathcal F_0$, bought root $S=[s]_3$, common 5-free period
$N_0$, and full actual safe top menus. Retain its inventories
$V_1,V_2$, output-index set $\mathscr T$ and $\tau=|\mathscr T|$.
Thus $H=\mathbb Z\setminus\bigcup\mathcal F_0$ avoids all
original height-zero outputs,
$|\mathcal F_0|=K-(2+v_1+v_2)-z$, and $\tau\le v_2$.
Assume

$$
H\subseteq T_2\cap T_5\cap T_8,\qquad
E_j=H\setminus T_j\ (j=3,6),\qquad
\Gamma_{N_0}(E_3\cup E_6)=g\in\{3,9\}.
\tag{SC393}
$$

An empty $H$ already gives descent, and SC194 makes both
inner deficits nonempty. Write $E_3\cup E_6\subseteq[w]_g$.
For every nonunit $e\mid g$, SC229's virtual-enclosure
argument supplies an actual outer top $C_e=[w]_e$, of original
label $9\chi(e)$ and color $c_e$. Its count reserve needs no
actual enclosing lower: a nonempty complete outer menu gives
$v_2\ge1$ and hence $v_1\ge1$, exactly as in SC373.
For $g=9$, SC230 puts the partners at indices 3 and 9 in
different outer colors. Their original labels are 45 and 225.
The actual 45 and the existing global inventory bound give
$v_1\ge15$ by SC242.

### Preserve congruence prefixes while moving the ternary enclosure

Put $a=w\bmod3\ne s$. For $g=3$, choose $e=3$ and let
$\psi$ exchange the two first ternary roots outside $S$,
retaining higher output ternary digits and all other prime
coordinates. For $g=9$, choose $e=9$ and any
$\beta\bmod9$ with $\beta\bmod3\ne s$ and
$\beta\ne w\bmod9$. A rooted ternary-tree automorphism
$\psi$ takes $[w]_9$ to $[\beta]_9$ while preserving $S$.
For either of the two targets with $\beta\bmod3=a$, exchange
the corresponding second-digit children within root $a$ and
fix all first digits. For the other three targets, exchange
the unbought first roots and permute the children in the
destination branch. Higher output tails remain fixed.

These permutations preserve every congruence partition of
the common output carrier and fix nonternary coordinates.
Each 5-free AP therefore remains one AP with the same
numerical modulus, on all periodic integer lifts. Put $d=2$
for a within-root exchange and $d=1$ for a first-root exchange.
Then $\psi$ fixes ternary prefixes of length $d-1$.
The common tree $\theta$ commutes with truncation, so
$F_c(x)$ and $F_c(\psi(x))$ have the same original 5-prefix
through depth $d-1$. No affine property of $\theta$ or
agreement of higher original 5-digits is required.

Fix $j\in\{3,6\}$ and use Section 66's placement with
$c=c_e$, virtual partner $B=\psi(C_e)$, and $\psi$ in place
of $\phi_b$. Thus transport $\mathcal F_0$, the two
nonpartner outer menus and both inner menus; keep
$\mathcal T_c$ unchanged except for removing its supplier
$C_e$ at fresh root 1. The partner index $e$ is replaced
once by $B$ at fresh root 4. The rootwise proof of SC375
applies because $\psi(E_j)$ and $C_e$ have disjoint residues
modulo $e$. Consequently the entire integer hole, numerical
interface and exact count are

$$
\begin{aligned}
R_{\psi,j}&=\psi(E_j)\setminus T_c,\\
\mathbb Z\setminus\bigcup\mathcal B_{\psi,j}
  &=[1]_5\cap R_{\psi,j},\\
\operatorname{Mod}(\mathcal B_{\psi,j})
  &=\operatorname{Mod}(\mathcal F_0)
      \cup\{5\}\cup\{5n:n\in\mathscr T\},\\
|\mathcal B_{\psi,j}|
  &=K-1-v_1-v_2-z+\tau\le K-1-v_1-z.
\end{aligned}
\tag{SC394}
$$

Every safe top index occurs once; all exceed one. Retained
labels have 5-valuation zero and added labels valuation one,
so the candidate labels are distinct odd nonunits. There is
no responsibility left at another fresh root or outside
$\psi(H)$. The transformed menus need not arise from a new
common original cover.

EB1 makes $R_{\psi,j}$ nonempty. It avoids $S$ and lies in
the transported enclosure. Reuse SC137's eleven-class
complete-$3p$ packet and SC236's fifteen-class complete-27
packet, inserted by SC233 at fresh root 1. Their costs are
at most $v_1$, so SC394 gives the same hull restrictions as
SC243:

$$
g=3\Longrightarrow\Gamma_{N_0}(R_{\psi,j})\in\{3,9\},
\qquad
g=9\Longrightarrow\Gamma_{N_0}(R_{\psi,j})=9.
\tag{SC395}
$$

Indeed any additional prime factor is greater than 5 and
gives a complete $3p$ enclosure, while additional ternary
depth gives an enclosure modulo 27. In the $g=9$ branch,
one may also use $e=3$ and the first-root exchange; the same
count and hull-nine conclusion hold.

### Within-root exchange forces at least two original 5-levels

Assume additionally $H\cap L_2=\varnothing$. For
$y\in R_{\psi,j}$ put $x=\psi^{-1}(y)\in E_j\subseteq H$,
and inspect an original owner of $F_c(y)$. It cannot have
ternary height two: every nonempty actual top pullback at
$c$ is included in the unchanged $T_c$, which $y$ avoids.
The owner has ternary height zero or is an outer lower.

If its original 5-height were below $d$, its membership
would be unchanged at $F_c(x)$: the original ternary
condition, required original 5-prefix and all other
coordinates agree. A height-zero owner contradicts
height-zero-priority retention, while an outer lower
contradicts $H\cap L_2=\varnothing$. Hence the complete
residual is served by actual outputs satisfying

$$
n=3^h m,\qquad h\ge d,\qquad (m,15)=1,
\quad\text{from height-zero owners or outer lowers}.
\tag{SC396}
$$

Thus a first-root exchange forces original 5-height at
least one; either within-root exchange in the hull-nine
branch forces height at least two. This does not force
$m>1$, a lower or top numerical counterpart, or distinct
output indices across the two original roles. The
$g=3$ conclusion here is a transport and owner interface;
the new paid menu result below concerns modulo-9 residuals.

### Three common classes leave two requests per actual source

Let $R=R_{\psi,j}\subseteq[\beta]_9$ be a complete SC394
residual. Suppose a finite actual menu $\mathcal W$, of
either original role, serves all of $R$, with outputs

$$
R\subseteq\bigcup_{d\in\mathcal W}C_d,\qquad
C_d=[\eta_d]_{n_d},\qquad
n_d=3^{h_d}m_d,\quad
h_d\ge2,\quad m_d>1,\quad(m_d,15)=1,
\tag{SC397}
$$

and pairwise distinct numerical indices $n_d$. This is
service of the complete mask, not selected witnesses.
Write $r=|\mathcal W|$ and $\lambda_t=1+5t\bmod25$.
Three common classes cover its first three fresh children:

$$
[\lambda_0]_{25},\qquad
[\lambda_1]_{25}\cap[\beta]_3,\qquad
[\lambda_2]_{25}\cap[\beta]_9.
\tag{SC398}
$$

For each source assign two globally distinct slots
$s_{d,3},s_{d,4}\mid n_d$, excluding $1,3,9$, and add
$[\lambda_t]_{25}\cap[\eta_d]_{s_{d,t}}$ for $t=3,4$.
These actual-phase divisor patches cover everything served
by that source on their respective children. Their labels
$25s_{d,t}$ avoid the three common labels $25,75,225$.
The packet costs $3+2r$, has distinct labels of 5-valuation
two, is fresh against SC394, and covers every integer lift
of the entire hole.

For a nonempty source subset $X$, put $x=|X|$, let $c_X$
count its distinct numerical cofactors $m$, and let
$H_X=\max_{d\in X}h_d$. Its full divisor union
$\mathcal N(X)=\bigcup_{d\in X}\{s:s\mid n_d,\ s\notin
\{1,3,9\}\}$ contains three disjoint families: its $x$
actual outputs, the $2c_X$ indices $m,3m$, and the
$H_X-2$ unit-cofactor indices $3^3,\ldots,3^{H_X}$.
Numerical distinctness also bounds the number of pairs
$(h,m)$. Therefore

$$
|\mathcal N(X)|\ge x+2c_X+H_X-2,\qquad
x\le(H_X-1)c_X,\qquad
x\le7\Longrightarrow|\mathcal N(X)|\ge2x.
\tag{SC399}
$$

For the final implication, $c_X=1$ or $H_X\le3$ is
immediate. If $H_X=4$, then $c_X\le2$ gives
$x\le3c_X\le2c_X+2$, while $c_X\ge3$ gives
$2c_X+2\ge8$. If $H_X\ge5$ and $c_X\ge2$, then
$2c_X+H_X-2\ge7$. The existing finite Hall theorem on
two copies per source, as used in SC328, now assigns the
two slots whenever $r\le7$.

### One original inventory pays six sources, or a qualified seventh

If $r\le6$, the packet costs $3+2r\le15\le v_1$, so

$$
K'\le K-1-v_1-v_2-z+\tau+(3+2r)
   \le K-1-z<K.
\tag{SC400}
$$

This uses the actual global reserve SC242. It permits
height-zero suppliers without lower counterparts, provided
their output indices are distinct.

For $r=7$, additionally require
$3\chi(n_d)\in D$ for every source, which holds
automatically for actual outer lowers. Let
$\mathcal N=\mathcal N(\mathcal W)$. SC399 gives
$|\mathcal N|\ge14$. Divisor closure supplies a distinct
original lower donor $3\chi(s)$ for every $s\in\mathcal N$.
The further original labels 15 and 75 have excluded indices
3 and 9. If $|\mathcal N|\ge15$, these already give
$v_1\ge17$.

If $|\mathcal N|=14$, some prime
$\ell\in\{17,19,23,29\}$ divides none of the $m_d$.
Otherwise $\mathcal N$ would contain the eight distinct
indices $\ell,3\ell$ for those four primes, as well as
the seven actual outputs of 3-height at least two, giving
at least fifteen indices. The original initial prime
support and $P\ge29$, together with Report 385 GHA10,
supply the actual lower $3\ell$. Its index $\ell$ is
outside the full $\mathcal N$, not merely outside a chosen
matching, and differs from 3 and 9. Thus in either case

$$
r=7,\quad 3\chi(n_d)\in D\ (d\in\mathcal W)
\quad\Longrightarrow\quad
v_1\ge17=3+2r.
\tag{SC401}
$$

SC400 again gives strict descent. All credits are distinct
labels in one original $V_1$ inventory. No donor phase
replaces an actual patch phase, and no original top budget
is added to this payment.

### Two sibling targets impose a concrete original-inventory condition

Assume $g=9$. For either sibling residue $\beta\bmod9$
with $\beta\bmod3=w\bmod3$ and $\beta\ne w\bmod9$, use
its within-root exchange $\psi_\beta$. Let
$\mathcal W_\beta$ contain all actual outer lowers with
output prefix $\beta\bmod9$, original 5-height at least
two and nonunit 3,5-free cofactor. Their output indices
are distinct because their original lower labels are
distinct. For either inner color $j$, SC400--SC401 force

$$
|\mathcal W_\beta|\le7
\quad\Longrightarrow\quad
R_{\psi_\beta,j}\setminus
\bigcup_{d\in\mathcal W_\beta}C_d\ne\varnothing.
\tag{SC402}
$$

Under $H\cap L_2=\varnothing$, every original owner at a
point of this remainder is height zero or an outer lower
with $m=1$; SC396 still forces its original 5-height to
be at least two. An outer lower with $m>1$ owning such a
point would have the specified prefix and belong to
$\mathcal W_\beta$.

In particular, if the residuals at both sibling targets
are completely served by these nonunit-cofactor outer
lowers, choosing either inner color at each target, then
each $\mathcal W_\beta$ has at least eight members.
The different modulo-9 prefixes make these sixteen
original identities disjoint. Their original labels
have the form $3\cdot5^h m$, $h\ge2$, $m>1$.
The actual labels 15,75 and
$3\ell$ for $\ell\in\{17,19,23,29\}$ lie outside both
families. Consequently this conditional complete service
requires

$$
v_1\ge16+2+4=22.
\tag{SC403}
$$

This counts one original inventory; it does not add the
budgets of two alternative repairs.

### Boundaries of the small-menu conclusion

At eight numerical sources, the full-divisor allocation
can fail: take heights $2,3,4,5$ in each of two distinct
prime-cofactor columns. After excluding $1,3,9$, their
divisor union has fifteen slots for sixteen requests.
This is a boundary of this allocation, not an EB1
realization or a failure of every possible repair.

Pure-cofactor service remains a separate obstacle.
Reuse SC139's complete-envelope mass argument on
$C=[\beta]_9$. A class of numerical label
$3^a5^\ell$, $\ell\ge1$, has relative $C$-mass at most
$5^{-\ell}$ for $a=0,1,2$, and at most
$3^{2-a}5^{-\ell}$ for $a\ge3$. The sum over all
available numerical labels is

$$
\left(3+\sum_{a\ge3}3^{2-a}\right)
\sum_{\ell\ge1}5^{-\ell}
=\frac78<1.
\tag{SC404}
$$

Thus no finite distinct packet from this pure $\{3,5\}$
palette covers the complete modulo-9 AP. After SC233
inserts it at the deficient root, these relative 5-levels
become absolute levels at least two. Smaller actual
residuals, extra cofactor primes and unused absolute
depth-one slots are outside this obstruction; no claim
identifies the full AP with an actual EB1 residual.

The ternary permutation changes the original 5-prefix
selected by $\theta$. It supplies SC396, not an independent
nonternary-prime phase or Section 61's extra-cofactor
projection. Complete mixed service with repeated numerical
outputs, pure-5-power original parts and larger menus is
not excluded. Three complete outer menus have not been
forced for a general cover, and original ternary heights
above two remain untreated here. These are ordinary
mathematical deductions using existing packets and finite
Hall; no new Lean verification is asserted. Unrestricted
Erdős #7 remains unresolved.

## 69. A pure-power parent branch forces private projection and actual phases

Fix one original EB1 whole distinct odd cover
$\mathcal C=\{A_d=[\rho_d]_d:d\in D\}$. Let $\ell,q$ be
distinct original support primes and write
$Q=\ell^Hq^GW$, where $(W,\ell q)=1$ and $H,G\ge1$.
The coding prime $\ell$ will later be 3; neither prime denotes
the partner in Section 66. All deletions, phases, heights and
private regions in this section belong to this one original
cover.

### One literal parent prefix has a complete joint liability

For $1\le t\le G$, put $k=t-1$ and use the original pure
class $A_{q^t}$ supplied by divisor closure. Define

$$
\begin{gathered}
\gamma_t=\rho_{q^t}\pmod{q^t},\qquad
u_t=\gamma_t\pmod{q^k},\\
J_t=\{d\in D:v_q(d)\ge t,\
                    \rho_d\equiv u_t\pmod{q^k}\},\\
E_t=(\mathbb Z/Q\mathbb Z)
             \setminus\bigcup_{d\notin J_t}A_d.
\end{gathered}
\tag{SC405}
$$

The parent condition is void when $k=0$. Thus $J_t$ is the
entire original family in that parent branch of $q$-height
at least $t$, including $q^t$ itself. Every original outside
$J_t$ is retained unchanged.

Let $I_t$ contain the retained lower-height originals
$d=\ell^a q^j m$ with $j\le k$ and
$\rho_d\equiv u_t\pmod{q^j}$. In the complete
$(\ell^H,W)$ carrier put

$$
X_t=(\mathbb Z/\ell^H\mathbb Z\times\mathbb Z/W\mathbb Z)
 \setminus\bigcup_{\ell^a q^j m\in I_t}
             ([\rho_d]_{\ell^a}\times[\rho_d]_m).
$$

Conditions modulo 1 are void. In CRT coordinates $(v,z,w)$,
the full joint hole and the complete original private region
satisfy

$$
\begin{aligned}
E_t
 &=\{(v,z,w):z\equiv u_t\pmod{q^k},\ (v,w)\in X_t\},\\
P_{q^t}
 &=\{(v,z,w):z\equiv\gamma_t\pmod{q^t},\ (v,w)\in X_t\}.
\end{aligned}
\tag{SC406}
$$

Inside the parent cylinder, a retained lower-$q$ original has
membership independent of all later $q$-digits. A retained
higher-$q$ original has a different parent prefix and misses
the entire cylinder. Outside that cylinder all removed
originals were absent, so original coverage is already retained.
This proves the first equality.

For the second, another original of $q$-height at least $t$
cannot meet $A_{q^t}$: its class would then be contained in
the pure $q^t$ class, contradicting irredundancy. The remaining
originals are exactly those whose compatible conditions were
removed in defining $X_t$. No union of individual private
traces replaces $E_t$.

Define the actual projection and the two local height parameters
by

$$
\begin{gathered}
\Lambda_t=\pi_{\ell^H}(X_t)=\pi_{\ell^H}(P_{q^t}),\qquad
s_t=|\Lambda_t|,\\
a_t=\max_{d\in J_t}v_\ell(d),\qquad
b_t=\max_{\substack{d\in D\\v_q(d)=k}}v_\ell(d),\\
1\le s_t\le T_\ell(H)
 =\ell^H-\frac{\ell^H-1}{\ell-1},\qquad
0\le a_t\le b_t\le H.
\end{gathered}
\tag{SC407}
$$

Privacy makes $s_t$ positive. Every pure-$\ell$ guard is
retained, so Report 385 GHA1 bounds the projection by the
actual guard-safe alphabet. The maximum defining $b_t$ exists:
pure $q^k$ supplies a label when $k>0$, and pure $\ell^H$
does so when $k=0$. To see $a_t\le b_t$, divide a label of
$J_t$ down to $q$-height $k$, retaining its $\ell$-height.
The resulting label is an original by divisor closure whenever
nonunit; the unit case has $\ell$-height zero and causes no
exception to the inequality. The bound $b_t$ is global at that
numerical $q$-height, without a phase restriction.

### The existing height code applies to this complete branch

Set

$$
\begin{gathered}
\omega=a_t+1,\qquad L_0=\max(H,a_t+b_t+1),\\
S_t=s_t\ell^{L_0-H},\qquad U_t=\ell^{a_t+1},\qquad
L_j=L_0+(j-1)\omega\quad(1\le j\le G-k).
\end{gathered}
\tag{SC408}
$$

The following sufficient condition would give a distinct odd
whole cover with at most $K-1$ classes:

$$
q-1\ge S_t
\quad\text{and}\quad
\bigl(t=G\ \text{or}\ q\ge U_t\bigr).
\tag{SC409}
$$

Reuse the prefix transport and shifted height encoding of
Report 385 Sections 153 and 250 on the initial alphabet

$$
\mathcal D_1=
\{c\bmod\ell^{L_0}:c\bmod\ell^H\in\Lambda_t\}.
$$

It has exactly $S_t$ entries. Inject it into the $q-1$ next
digits after $u_t$ excluding the actual next digit of
$A_{q^t}$. At every subsequent level each coded prefix has
$U_t=\ell^\omega$ extensions, injected into the $q$ next
digits. Fix these injections once, independently of original
labels and the complete $W$-coordinate. When $t=G$ there is
only the initial level, so no subsequent-alphabet bound is
required.

The source preserves the original $\ell^H$ coordinate, the
entire $W$ coordinate and the literal parent $u_t$, and uses
the one fixed code for the remaining $q$-digits. A full
comparison carrier is $\ell^{L_{G-k}}q^GW$; the original
$q$-axis has not been removed from the liability comparison.

Write a removed original as
$d=\ell^a q^{k+j}m$, where $1\le j\le G-k$,
$0\le a\le a_t$ and $m\mid W$. Its actual $q$-prefix
either has no inverse or specifies one prefix
$c_d\pmod{\ell^{L_j}}$. If this prefix meets the original
$\ell^a$ condition, its full inverse on the coding domain is
the one AP with conditions
$z\equiv u_t\pmod{q^k}$,
$z\equiv c_d\pmod{\ell^{L_j}}$ and
$z\equiv\rho_d\pmod m$. The prefix already has its
$\ell^H$ word in $\Lambda_t$, so no additional mask splits
that AP. Enclose each such inverse by

$$
\begin{gathered}
\kappa_j(a)=b_t+1+(j-1)(a_t+1)+a,\\
d'=\ell^{\kappa_j(a)}q^km,\qquad
B_d=[u_t]_{q^k}\cap[c_d]_{\ell^{\kappa_j(a)}}
                         \cap[\rho_d]_m,\\
b_t<\kappa_j(a)\le a_t+b_t+1+(j-1)(a_t+1)\le L_j.
\end{gathered}
\tag{SC410}
$$

These are whole odd nonunit APs with the actual original
cofactor phases. All candidates have $q$-height $k$ and
$\ell$-height exceeding $b_t$, so they cannot collide with
any retained original. For two candidates, the
$(\ell q)$-free part recovers $m$, and division with remainder
of $\kappa_j(a)-(b_t+1)$ by $a_t+1$ recovers $j-1$ and
$a$. Thus equal candidate labels would recover equal original
numerical labels.

For any integer missed by the retained originals, SC406 puts
its parent at $u_t$ and its complete $(\ell^H,W)$ coordinate
in $X_t$. Its code is therefore defined. Retained lower-$q$
membership is unchanged at its source point; retained
higher-$q$ originals miss the entire parent cylinder.
Original whole coverage consequently supplies a removed owner.
It is not $q^t$, whose next digit the code excludes. The
owner's exact inverse contains the integer, and SC410's
enclosure covers it. This proves coverage of the entire
joint hole and all integer lifts, using one common code.

The pure $q^t$ original contributes no candidate and every
other removed original contributes at most one. Hence

$$
K'\le K-|J_t|+(|J_t|-1)=K-1.
\tag{SC411}
$$

No modulus-sum comparison is required. EB1 rules out SC409,
so the following phase-local bounds hold for every $t$ in
the same original cover:

$$
\boxed{
\begin{array}{ll}
t=G:&q\le S_t,\\
t<G:&q\le\max\{S_t,U_t-1\}.
\end{array}}
\qquad
q\le\max\left\{\ell^{a_t+1},\
s_t\ell^{\max(0,a_t+b_t+1-H)}\right\}.
\tag{SC412}
$$

The rightmost expression is a convenient common weaker form.
The operational condition SC409 keeps the sharper final-level
case. No strict inequality $q<S_t$ is asserted: $S_t$ can
itself be prime, so its equality boundary cannot be discarded.

### Height two forces complete private-source spread

Now take $\ell=3$, $H=2$ and an original support prime
$q\ge29$. In the normalization of this report the pure 3
and 9 guards leave exactly
$\mathcal U=\{2,3,5,6,8\}$ modulo 9. Thus
$\Lambda_t\subseteq\mathcal U$, $1\le s_t\le5$ and
$U_t\le27<q$. SC412 gives

$$
q\le s_t3^{\max(0,a_t+b_t-1)}\le27s_t,
\qquad
\left|\pi_9(P_{q^t})\right|
\ge\left\lceil\frac q{27}\right\rceil
\quad(1\le t\le G).
\tag{SC413}
$$

Using the existing $P^+(Q)<135$ bound of GHA10, the required
projection sizes are

| Original support prime | Required safe words in each $\pi_9(P_{q^t})$ |
| --- | --- |
| $29\le q\le53$ | at least 2 |
| $59\le q\le79$ | at least 3 |
| $83\le q\le107$ | at least 4 |
| $109\le q\le131$ | all 5 |

The safe first-ternary roots contain two and three words,
respectively. Therefore $q\ge83$ forces every pure power's
complete private region to meet both roots. For $q\ge109$,
SC406 gives the stronger whole-cylinder statement

$$
\forall v\in\mathcal U\ \exists w\bmod W:\quad
\{(v,z,w):z\equiv u_t\pmod{q^{t-1}}\}\subseteq E_t.
\tag{SC414}
$$

The cofactor $w$ may depend on $v$ and $t$. Its entire
remaining $q$-tail is included in the joint hole; no common
cofactor for different words or different levels is asserted.

If $q\ge47$ and $a_t+b_t\le3$, the first bound in SC413
would give $q\le5\cdot9=45$. Thus

$$
\begin{gathered}
q\ge47\quad\Longrightarrow\quad a_t=b_t=2,\\
\exists d=9q^jm\in D:\quad
j\ge t,\quad(m,3q)=1,\quad
\rho_d\equiv\rho_{q^t}\pmod{q^{t-1}},\quad
\rho_d\not\equiv\rho_{q^t}\pmod{q^t}.
\end{gathered}
\tag{SC415}
$$

The last inequality is comparable-original disjointness.
At $t=G$ the witness has $j=G$. The global conclusion
$b_t=2$ is already supplied by GHA10's actual $9q^G$ and
divisor closure. SC415 additionally places a height-two
original inside the specified actual parent branch. It does
not prescribe the phase of the numerical label $9q^G$
itself. Parent branches at different $t$ may be nested, so
one original witness may satisfy several levels; they are
not counted as different labels.

### Cofactor-free guards impose literal cross-height phase exclusions

For a fixed $t$, let $\mathcal B_t$ be the union of safe
words removed by compatible lower-$q$ mixed pure labels:

$$
\mathcal B_t=
\bigcup_{\substack{a\in\{1,2\},\ 1\le j<t\\
  3^aq^j\in D,\,
  \rho_{3^aq^j}\equiv\gamma_t\ (\mathrm{mod}\ q^j)}}
\{v\in\mathcal U:v\equiv\rho_{3^aq^j}\pmod{3^a}\}.
$$

Every one of these is an actual retained original. Its
$q$-condition holds on the whole pure $q^t$ cylinder, and
it has no remaining cofactor condition. Consequently

$$
\Lambda_t\cap\mathcal B_t=\varnothing,\qquad
|\mathcal B_t|\le5-s_t
 \le5-\left\lceil\frac q{27}\right\rceil.
\tag{SC416}
$$

An original $3q^j$ cannot have the first-3 root occupied by
pure 3. Its compatible cylinder therefore removes at least
two safe words. An original $9q^j$ has one of the five safe
words, since otherwise a pure 3 or 9 guard would contain it.
It removes one safe word. Combining SC416 with
comparable-original disjointness gives the full tower
restrictions

$$
\begin{aligned}
q\ge83&\quad\Longrightarrow\quad
\rho_{q^t}\not\equiv\rho_{3q^j}
                   \pmod{q^{\min(t,j)}},\\
q\ge109&\quad\Longrightarrow\quad
\rho_{q^t}\not\equiv\rho_{9q^j}
                   \pmod{q^{\min(t,j)}}
\qquad(1\le t,j\le G).
\end{aligned}
\tag{SC417}
$$

For $j<t$ these are SC416's word exclusions. For $j\ge t$
they already follow because an intersecting mixed class
would be contained in $A_{q^t}$. All displayed numerical
labels exist by GHA10 and divisor closure in the stated
ranges. Thus SC417 excludes intersections of the literal
$q$-coordinate cylinders even across the heights where the
original full moduli are not comparable.

For $q\ge83$, at most one original $9q^j$, $j<t$, can have
a $q$-prefix compatible with pure $q^t$. Two different safe
words would violate $|\mathcal B_t|\le1$. If two such labels
had the same safe word, their compatible $q$-cylinders would
be nested, and the larger original modulus would give a
redundant AP. For $q\ge109$, no such compatible label is
possible by SC417.

The complete private hulls of Report 385 PH3 also satisfy

$$
q\ge29\Longrightarrow v_3(\Gamma_{q^t})\le1,
\qquad
q\ge83\Longrightarrow v_3(\Gamma_{q^t})=0.
\tag{SC418}
$$

The first conclusion uses two distinct modulo-9 private
words; the second uses both first-3 roots. It concerns the
entire original private region. Divisor closure does not
transfer the phase of a witness in SC415 to its numerical
divisors, and private-hull membership does not identify a
projection with its entire enclosing cylinder.

### Existing consumers and the remaining joint-source boundary

For $q\ge83$, every pure $q^t$ is nonconcentrated at the
first ternary root. Report 385 DP12 can therefore use its
entire pure-power index set $I_0=\{1,\ldots,G\}$, with its
existing simultaneous matching and complete-liability
conditions unchanged. The pure top $q^G$ also satisfies
the additional two-root premise of that report's TQ5.
Those results are reused; nonconcentration of all other
$q$-bearing originals does not follow from it.

No improved unconditional bound beyond $P^+(Q)<135$ is
obtained here. At $q\ge109$, the allowed local values
$a_t=b_t=2$ and $s_t=5$ retain the threshold $27\cdot5=135$.
The actual phase restrictions SC416--SC417 do not force a
violation of one of those inequalities. Distinct parent
branches have not been shown to supply disjoint witnesses
or independently spendable budgets.

In particular, SC414 has one cofactor choice per safe word;
it supplies neither two complete outer menus on a common
five-menu hole nor one prime enclosure of both inner
deficits. No entrance from Sections 66--68 is forced by
this projection statement. Excluding the remaining original
phases, obtaining a complete jointly paid exchange, and
unrestricted odd distinct covering remain unresolved.
These are ordinary deductions using the existing height
code and complete original liabilities; no Lean verification
or new enumeration is asserted.

## 70. Every occupied parent needs high originals in many different children

Keep the one original EB1 cover, its actual phases and the
factorization $Q=\ell^Hq^GW$ from Section 69. The source and
shifted height code of that section also apply to a literal
parent that contains no pure-power original. Excluding every
child containing a high-$\ell$ original then gives a count of
actual occupied children, with a simultaneous saving for all
excluded originals.

### The complete responsibility of an arbitrary occupied parent

Fix $0\le k<G$ and $u\bmod q^k$. Define

$$
\begin{gathered}
J_u=\{d\in D:v_q(d)>k,\ \rho_d\equiv u\pmod{q^k}\},\\
E_u=(\mathbb Z/Q\mathbb Z)
              \setminus\bigcup_{d\notin J_u}A_d.
\end{gathered}
\tag{SC419}
$$

Call $u$ occupied when $J_u\ne\varnothing$, and assume this
throughout. Irredundancy supplies a private point of any
chosen member of $J_u$, so $E_u\ne\varnothing$.

Let $I_u$ consist of the retained originals
$d=\ell^a q^j m$ with $j\le k$ and
$\rho_d\equiv u\pmod{q^j}$. Set

$$
\begin{gathered}
X_u=(\mathbb Z/\ell^H\mathbb Z\times\mathbb Z/W\mathbb Z)
 \setminus\bigcup_{\ell^a q^j m\in I_u}
       ([\rho_d]_{\ell^a}\times[\rho_d]_m),\\
E_u=\{(v,z,w):z\equiv u\pmod{q^k},\ (v,w)\in X_u\},\\
\Lambda_u=\pi_{\ell^H}(X_u),\qquad s_u=|\Lambda_u|,\\
1\le s_u\le T_\ell(H)
 =\ell^H-\frac{\ell^H-1}{\ell-1},\qquad
b_k=\max_{\substack{d\in D\\v_q(d)=k}}v_\ell(d)\le H.
\end{gathered}
\tag{SC420}
$$

The equality is the complete joint-hole identity SC406:
retained lower-$q$ membership is independent of the tail
above $k$, retained higher-$q$ classes miss this parent,
and outside the parent no removed original was present.
All pure-$\ell$ guards remain, giving the displayed bound
on $s_u$. The maximum defining $b_k$ exists by divisor
closure, using $q^k$ for $k>0$ and $\ell^H$ for $k=0$.
It is global at numerical $q$-height $k$, without a phase
restriction. No private region of a composite original is
substituted for $X_u$ or its projection.

Every one of the $q$ next children of $u$ contains an
actual member of $J_u$. To see this, fix $(v,w)\in X_u$,
choose any next $q$-digit and any remaining tail, and apply
original whole coverage to the resulting point of $E_u$.
Its owner belongs to $J_u$ and has that next digit. Hence
omitting any one child eliminates at least one original.

In particular, put $a_u=\max_{d\in J_u}v_\ell(d)$ and
reuse SC408--SC412 with $a_t,b_t,s_t$ replaced by
$a_u,b_k,s_u$. Divisor closure gives $a_u\le b_k$ exactly
as in SC407. With
$S_u=s_u\ell^{\max(0,a_u+b_k+1-H)}$, the same code gives

$$
\begin{array}{ll}
k=G-1:&q\le S_u,\\
k<G-1:&q\le\max\{S_u,\ell^{a_u+1}-1\}.
\end{array}
\tag{SC421}
$$

The pure-power hypothesis in Section 69 was needed for
the private-projection identity, not for this branchwise
absorption.

### Excluding every child containing a high original

For $d\in J_u$, let $\delta_u(d)$ be its actual next
$q$-digit after $u$. Fix $1\le r\le H$ and define

$$
\begin{gathered}
C_r(u)=\{\delta_u(d):d\in J_u,\ v_\ell(d)\ge r\},
\qquad c_r(u)=|C_r(u)|,\\
F=\begin{cases}
C_r(u),&c_r(u)>0,\\
\{\delta_0\},&c_r(u)=0,
\end{cases}
\qquad |F|=\max(1,c_r(u)),\\
n_{\rm ex}=|\{d\in J_u:\delta_u(d)\in F\}|
             \ge |F|\ge1.
\end{gathered}
\tag{SC422}
$$

Here $\delta_0$ is any next digit; every such child is
occupied by the preceding argument. Exclude exactly $F$
from the first coding step. All $n_{\rm ex}$ originals
in these children have empty inverse. Every original
that can have nonempty inverse has $\ell$-height $a<r$.

Use the same fixed prefix code with width $r$ and parameters

$$
\begin{gathered}
L_0=\max(H,b_k+r),\qquad
L_j=L_0+(j-1)r\quad(1\le j\le G-k),\\
\mathcal D_1=
 \{c\bmod\ell^{L_0}:c\bmod\ell^H\in\Lambda_u\},\\
S_r(u)=|\mathcal D_1|
 =s_u\ell^{\max(0,b_k+r-H)},\qquad U_r=\ell^r.
\end{gathered}
\tag{SC423}
$$

Inject $\mathcal D_1$ into the next digits outside $F$.
Each subsequent coded prefix has $\ell^r$ extensions,
injected into the $q$ next digits. Thus the sufficient
condition for this one replacement is

$$
q-\max(1,c_r(u))\ge S_r(u)
\quad\text{and}\quad
\bigl(k=G-1\ \text{or}\ q\ge\ell^r\bigr).
\tag{SC424}
$$

At $k=G-1$ only the initial alphabet is used. No bound
on a later alphabet is imposed at that level. Fix all
injections independently of original labels and of the
complete $W$-coordinate, as in Section 69. The source
preserves the $\ell^H$ word, the entire $W$ coordinate
and the parent $u$, and the full comparison carrier is
$\ell^{L_{G-k}}q^GW$.

For a removed original
$d=\ell^a q^{k+j}m$ with a nonempty inverse, one has
$0\le a<r$ and $1\le j\le G-k$. The inverse fixes one
prefix $c_d\bmod\ell^{L_j}$, already lying above
$\Lambda_u$ and compatible with the actual original
$\ell^a$ phase. Enclose it by the whole AP

$$
\begin{gathered}
\kappa_j(a)=b_k+1+(j-1)r+a,\qquad
d'=\ell^{\kappa_j(a)}q^km,\\
B_d=[u]_{q^k}\cap[c_d]_{\ell^{\kappa_j(a)}}
                      \cap[\rho_d]_m,\\
b_k<\kappa_j(a)\le b_k+r+(j-1)r\le L_j.
\end{gathered}
\tag{SC425}
$$

This is SC410 with the padded height bound $r-1$.
The global $b_k$ excludes collision with every retained
label. Division of $\kappa_j(a)-(b_k+1)$ by $r$ recovers
$j-1$ and $a$; together with $m$ this recovers the
original numerical label. Consequently the candidates
have pairwise distinct odd nonunit moduli, also distinct
from all retained originals.

For every integer missed by the retained family, SC420
places its complete $(\ell^H,W)$ coordinate in $X_u$,
so this one common source is defined. Retained membership
is unchanged at the source. Original whole coverage
supplies a removed owner outside the forbidden children,
whose exact inverse contains the integer and is enclosed
by SC425. Thus all of $E_u$, and every integer lift, is
covered. Each nonexcluded removed original supplies at
most one candidate, while all $n_{\rm ex}$ excluded
originals supply none. The exact class-count estimate is

$$
K'\le K-|J_u|+(|J_u|-n_{\rm ex})
       =K-n_{\rm ex}<K.
\tag{SC426}
$$

This is one simultaneous deletion and replacement in the
original cover. EB1 therefore rules out SC424.

### Necessary child counts at every height

Whenever $k=G-1$ or $q\ge\ell^r$, failure of SC424 gives
the exact integer obstruction

$$
q-\max(1,c_r(u))<S_r(u).
\tag{SC427}
$$

If also $q>S_r(u)$, the case $c_r(u)=0$ would have
$q-1\ge S_r(u)$ and is impossible. Hence

$$
\boxed{
\bigl(k=G-1\ \text{or}\ q\ge\ell^r\bigr)
\ \text{and}\ q>S_r(u)
\quad\Longrightarrow\quad
c_r(u)\ge q-S_r(u)+1.}
\tag{SC428}
$$

The strict condition $q>S_r(u)$ is retained: the local
alphabet size can be prime. A uniform all-height version
follows from $b_k\le H$ and $s_u\le T_\ell(H)$:

$$
S_r(u)\le\ell^rT_\ell(H),\qquad
q\ge\ell^rT_\ell(H)
\quad\Longrightarrow\quad
c_r(u)\ge q-\ell^rT_\ell(H)+1.
\tag{SC429}
$$

Here $\ell$ is odd, $H\ge1$ and $r\ge1$, so
$T_\ell(H)\ge2$. The threshold $\ell^rT_\ell(H)$ is
composite; equality with the support prime $q$ is
impossible. Thus the hypothesis implies both
$q>S_r(u)$ and $q\ge\ell^r$, including at nonterminal
levels. The sharper local statement SC428 also applies
at the last level when no later-alphabet bound is known.

For $\ell=3$ and $H=2$, every occupied parent has
$s_u\le5$ and $b_k\le2$. In particular,

$$
\begin{aligned}
S_1(u)&=s_u3^{\max(0,b_k-1)}\le3s_u\le15,\\
q\ge17&\quad\Longrightarrow\quad
c_1(u)\ge q-S_1(u)+1\ge q-3s_u+1\ge q-14.
\end{aligned}
\tag{SC430}
$$

This counts distinct next children containing an actual
original divisible by 3, including either allowed
ternary height. For the height-two originals,

$$
\begin{aligned}
S_2(u)&=s_u3^{b_k}\le9s_u\le45,\\
q\ge47&\quad\Longrightarrow\quad
c_2(u)\ge q-S_2(u)+1\ge q-9s_u+1\ge q-44.
\end{aligned}
\tag{SC431}
$$

Both conclusions hold for every occupied literal parent
at every $0\le k<G$. For example, $q=47$ requires
height-two originals in at least three children of each
occupied parent, and $q=131$ requires at least 87.
Using the exact $b_k$ in SC423 can strengthen these
bounds without any additional phase hypothesis.

### The counts add only within one prime and one level

Fix $q$ and $k$, and let $U_{q,k}$ be the occupied
parents modulo $q^k$. Distinct parents have disjoint
children, and one original of $q$-height greater than
$k$ specifies exactly one such parent and child. Choosing
one high original for each counted child therefore gives
the single-inventory inequality

$$
\#\{d\in D:v_\ell(d)\ge r,\ v_q(d)>k\}
 \ge\sum_{u\in U_{q,k}}c_r(u).
\tag{SC432}
$$

In particular, at ternary height two,

$$
\begin{aligned}
q\ge17:\qquad
\#\{d\in D:v_3(d)\ge1,\ v_q(d)>k\}
 &\ge\sum_{u\in U_{q,k}}(q-3s_u+1),\\
q\ge47:\qquad
\#\{d\in D:v_3(d)=2,\ v_q(d)>k\}
 &\ge\sum_{u\in U_{q,k}}(q-9s_u+1).
\end{aligned}
\tag{SC433}
$$

These sums use actual disjoint parent-child incidences
in one original inventory. They are not added across
different primes or different levels: the same original
can satisfy several prime-coordinate demands and can
witness nested parents. Nor do these child counts give
a common cofactor for different words, an aligned actual
$3p/9p$ pair, or coverage of the full five-menu residual.
The Section 66 entrance SC372 remains a separate joint
condition. These are ordinary deductions from the
stated EB1 hypotheses; no Lean verification of the
absorption or child-count conclusions is asserted.

## 71. Terminal donors sharpen the support cutoff and force shallow five-word occupancy

In the original ternary-height-two EB1 branch, the support range is

$$
29\le P^+(Q)\le113.
\tag{SC434}
$$

The exchange retains the actual pure prime-power original as a donor
for one short terminal prefix. Every replacement modulus decreases,
so EB1's modulus-sum tie-break applies even when the number of classes
is unchanged. The same construction sharpens each pure-power private
projection and forces exact-height-one phase occupancy at the largest
surviving primes. Every exchange uses one original cover and one
complete joint liability.

### One pure original terminates a short prefix

First allow arbitrary original height at the coding prime. Fix distinct
odd support primes $\ell,q$ and write
$Q=\ell^Hq^GW$, where $(W,\ell q)=1$ and $H,G\ge1$.
For $1\le t\le G$, put $k=t-1$ and use Section 69's actual
pure-parent data

$$
\begin{gathered}
u=\rho_{q^t}\pmod{q^k},\qquad
J=\{d\in D:v_q(d)>k,\ \rho_d\equiv u\pmod{q^k}\},\\
E=(\mathbb Z/Q\mathbb Z)\setminus\bigcup_{d\notin J}A_d
 =\{(v,z,w):z\equiv u\pmod{q^k},\ (v,w)\in X_t\},\\
\Lambda_t=\pi_{\ell^H}(X_t)
 =\pi_{\ell^H}(P_{q^t}),\qquad
s_t=|\Lambda_t|,\qquad1\le s_t\le T_\ell(H).
\end{gathered}
\tag{SC435}
$$

The exact set $X_t$ includes the entire $W$ coordinate and the
complement of all compatible retained lower-$q$ originals. All
originals outside $J$ remain unchanged. Set

$$
B=\ell^{H+1},\qquad N_t=Bs_t-\ell^H+1,
\qquad q>B.
\tag{SC436}
$$

Suppose $q\ge N_t$. Over the $s_t$ old words, the initial
prefixes of length $2H+1$ number $Bs_t$. Choose one prefix
$c\pmod{\ell^{H+1}}$ above an old word in $\Lambda_t$.
Replace all its $\ell^H$ fine extensions by this one short
leaf. The resulting prefix partition has exactly $N_t$ leaves.
Assign the short leaf to the actual next $q$-digit of $q^t$,
and assign the other leaves injectively to different next digits.

The short leaf terminates and is covered directly by
$[u]_{q^k}\cap[c]_{\ell^{H+1}}$. The actual donor $q^t$
has no coding-prime or $W$ condition, so it supplies the entire
leaf. On each other initial leaf use the existing continuing
prefix code, with $B$ extensions for every later $q$-digit.
The condition $q>B$ supplies all these injections. If $t=G$,
there are no later digits.

Fix this single code on the entire parent cylinder whose
$\ell^H$ word lies in $\Lambda_t$, without intersecting each
inverse with $X_t$. Preserve the old $\ell^H$ coordinate,
the whole $W$ coordinate and the parent $u$. A common comparison
carrier is $\ell^{L_{G-k}}q^GW$, where
$L_j=H+(H+1)j$. On a terminal leaf any remaining source
$q$-digits can be fixed arbitrarily; the donor covers every
such source. On the continuing part every digit is given by
the fixed prefix code.

Write a removed original as $d=\ell^a q^{k+j}m$, with
$0\le a\le H$, $1\le j\le G-k$ and $m\mid W$.
Its continuing inverse is empty or one AP with a prefix
$c_d\pmod{\ell^{L_j}}$, the parent $u$ and the actual
$m$-phase. The initial leaf already specifies an old word in
$\Lambda_t$, so this inverse needs no additional mask.
Enclose each nonempty inverse using

$$
\begin{gathered}
\kappa_j(a)=(H+1)j+a,\qquad
M(d)=\ell^{\kappa_j(a)}q^km,\\
B_d=[u]_{q^k}\cap[c_d]_{\ell^{\kappa_j(a)}}
                         \cap[\rho_d]_m,\qquad
H<\kappa_j(a)\le L_j,\\
\frac{M(d)}d=\left(\frac{B}{q}\right)^j<1.
\end{gathered}
\tag{SC437}
$$

The terminal donor has exactly the slot $j=1,a=0,m=1$,
so its replacement is $M(q^t)=Bq^k$. Its next digit is
used only by the terminal leaf, and it produces no continuing
replacement. Every other removed original contributes at most
one replacement. Every new modulus has coding-prime height
strictly above $H$, so it is fresh against every retained
original. Division of the exponent by $H+1$ recovers $j,a$;
the remaining cofactor recovers $m$. Thus all new numerical
moduli are pairwise distinct odd nonunits.

For every point of the full $E$, the source still has its
complete old $(\ell^H,W)$ coordinate in $X_t$. Retained
lower-$q$ membership is unchanged, and retained higher-$q$
originals miss the parent. Original whole coverage therefore
supplies an owner in $J$. A terminal output is directly
covered by its donor's replacement. A continuing output is
covered by the enclosure of its original owner's inverse.
Outside $E$, the unchanged retained family already covers.
This proves coverage of all integers.

Let $I\subseteq J$ be the originals that produce replacements,
including the terminal donor, and put $\Sigma=\sum_{d\in D}d$.
The one replacement family satisfies

$$
\begin{aligned}
K'&=K-|J|+|I|\le K,\\
\Sigma'
 &=\Sigma-\sum_{d\in J\setminus I}d
   -\sum_{d\in I}d\left[1-
       \left(\frac Bq\right)^{v_q(d)-k}\right]
 <\Sigma.
\end{aligned}
\tag{SC438}
$$

If $K'<K$, count minimality fails; if $K'=K$, modulus-sum
minimality fails. Thus EB1 excludes $q\ge N_t$, proving

$$
\boxed{q>\ell^{H+1}\quad\Longrightarrow\quad
q<\ell^{H+1}s_t-\ell^H+1\quad(1\le t\le G).}
\qquad
\boxed{P^+(Q)<\ell^{H+1}T_\ell(H)-\ell^H+1.}
\tag{SC439}
$$

For the second conclusion, any prime at most $\ell^{H+1}$
is already below the displayed threshold: $T_\ell(H)\ge2$
and $\ell^{H+1}>\ell^H$. The coding prime itself also lies
below it. The local hypothesis $q>\ell^{H+1}$ remains
essential to the stated strict modulus comparison. The
all-height cutoff still grows with $H$.

### Height two gives a strict endpoint and stronger private projections

Take $\ell=3$, $H=2$ and an original support prime $q\ge29$.
Then $B=27$ and $T_3(2)=5$. SC439 gives, for every pure
power in the same original cover,

$$
q<27s_t-8,\qquad
s_t\ge\left\lfloor\frac{q+8}{27}\right\rfloor+1,
\qquad1\le t\le G.
\tag{SC440}
$$

At $s_t=5,q=127$, the initial partition has exactly 127
leaves. No omitted original is required: every charged
modulus decreases strictly. Thus $127$ and $131$ are both
excluded. Combining the resulting prime cutoff with the
existing lower bound from Report 385 GHA10 gives SC434.

The complete private projections consequently satisfy

| Original support prime | Required safe words in every $\pi_9(P_{q^t})$ |
| --- | --- |
| $q\ge29$ | at least 2 |
| $q\ge47$ | at least 3 |
| $q\ge73$ | at least 4 |
| $q\ge101$ | all 5 |

Reuse Section 69's actual cofactor-free guard argument. A
compatible lower-$q$-height $3q^h$ removes at least two
safe words, and a compatible $9q^h$ removes its one safe
word. For $h\ge t$, compatibility is already excluded by
containment in the actual pure $q^t$ class. Hence the literal
phase restrictions sharpen to

$$
\begin{aligned}
q\ge73&\quad\Longrightarrow\quad
\rho_{q^t}\not\equiv\rho_{3q^h}\pmod{q^{\min(t,h)}},\\
q\ge101&\quad\Longrightarrow\quad
\rho_{q^t}\not\equiv\rho_{9q^h}\pmod{q^{\min(t,h)}}
\qquad(1\le t,h\le G).
\end{aligned}
\tag{SC441}
$$

The mixed numerical labels exist by GHA10 and divisor closure.
The cofactor points realizing different safe words may still
be different. The larger projection does not supply one common
cofactor cylinder.

### Two actual terminal donors at the first q-level

At $k=0$, actual $3q$ exists for $q\ge29$. Write
$c_0=\rho_q\pmod q$ and $c_1=\rho_{3q}\pmod q$.
These two digits differ by comparable-original disjointness.
A private point of $3q$ supplies a word of $\Lambda_1$ in
its actual first-3 root. Choose a depth-four prefix over this
word for the $3q$ terminal, and a disjoint depth-three prefix
for the $q$ terminal. Such a choice is possible even within
one old word, by using different depth-three subprefixes.

The two terminal leaves replace nine and three depth-five
leaves, saving eight and two, respectively. Their whole APs
have numerical labels $27$ and $81$, exactly the $q$ and
$3q$ donor slots in SC437. On the second leaf the preserved
first-3 root satisfies the actual $3q$ guard. The remaining
initial leaves continue as before, with neither terminal digit
assigned to a continuing leaf. The same source, decoder
and comparison SC438 therefore give

$$
q<27s_1-10.
\tag{SC442}
$$

In particular, $q=71$ forces $s_1\ge4$. This two-donor
statement uses the common root $k=0$. At deeper levels it
requires the two actual donors to share the chosen parent;
numerical presence alone does not provide that alignment.

### Almost every large-prime child has all five words at exact height one

Let $\mathcal A$ be the five actual safe words modulo 9
left by the original pure 3 and 9 guards. For a first-$q$
digit $c$, define

$$
\begin{gathered}
B(c)=\{z\in\mathcal A:\exists m\mid W,\ 9qm\in D,\
\rho_{9qm}\equiv c\pmod q,\
\rho_{9qm}\equiv z\pmod9\},\\
V_q=\{c\notin\{c_0,c_1\}:B(c)\ne\mathcal A\},
\qquad q\in\{107,109,113\}.
\end{gathered}
\tag{SC443}
$$

These are actual originals of exact $q$-height one; higher
$q$-height descendants are not counted. SC440 gives
$\Lambda_1=\mathcal A$ for these three primes. The necessary
bound is

$$
|V_q|\le\frac{123-q}{2}.
\tag{SC444}
$$

To prove it, put $r=(125-q)/2$, so $r$ is respectively
$9,8,6$. Suppose there are $r$ distinct defective digits
outside $\{c_0,c_1\}$. For each selected digit choose a
missing word $z(c)\in\mathcal A\setminus B(c)$, and let
$n_z$ count how many choices use word $z$. Then
$\sum_z n_z=r\le9$.

Each safe word has nine depth-four subprefixes. The actual
first-3 root of $3q$ contains at least two safe words.
Choose its terminal word $v$ avoiding any word with $n_z=9$;
there is at most one such word. Thus $n_v\le8$, and the
$3q$ terminal leaves room for all its requested depth-four
prefixes. Choose a different word for the $q$ terminal,
avoiding any word with $n_z\ge7$. There is at most one such
word, so this choice is possible among the other four safe
words. Its depth-three terminal consumes three depth-four
slots, leaving at least the six needed there. All other
words have nine slots. Hence all selected depth-four leaves
can be chosen disjointly from each other and both terminals.

The two terminals save ten initial leaves, and each selected
short continuing leaf saves two. The complete initial
partition therefore has

$$
135-8-2-2r=125-2r=q
\tag{SC445}
$$

leaves. Assign the prescribed leaves to their two donor digits
and their $r$ defective digits, and assign the remaining
ordinary depth-five leaves bijectively to the other digits.

At a short continuing leaf, the missing-word condition makes
every exact-$q$-height-one original of ternary height two
incompatible with the source. Thus its nonempty height-one
inverses have $a\le1$ and fit their SC437 labels in the
depth-four prefix. If $G\ge2$, give that short leaf 81
ternary extensions for the next $q$-digit; this is possible
because $q>81$. The resulting depth is $4+4=8$, exactly
the usual $3\cdot2+2$ depth. Use ordinary width three
thereafter. If $G=1$, no continuation is needed. Ordinary
initial depth-five leaves use the usual continuation throughout.

Consequently every deeper original still has at most one
continuing inverse at depth $3j+2$ and receives the same
numerical label $3^{3j+a}m$. The absence condition concerns
only exact height one; deeper descendants retain all their
original phases and heights. The terminals directly cover
their whole leaves. The common source preserves the entire
modulo-9 and $W$ coordinates, so SC435--SC438 again cover
the complete joint hole and give a forbidden EB1 descent.
Therefore $|V_q|<r$, proving SC444.

One original $9qm$ occupies only one child and one modulo-9
word. The corresponding actual inventories are therefore

| $q$ | Maximum defective nonterminal children | Minimum children with all five words | Minimum distinct originals $9qm$ |
| --- | --- | --- | --- |
| 107 | 8 | 97 | 485 |
| 109 | 7 | 100 | 500 |
| 113 | 5 | 106 | 530 |

The cofactors may depend on both the child and the word.
Neither their common incidence nor complete top-menu service
is asserted.

### Mixed terminal capacities constrain every occupied parent

There is also a branchwise version at an arbitrary occupied
terminal parent $u\bmod q^{G-1}$, for $q\ge29$. Keep
SC419--SC420's complete $E_u,X_u,\Lambda_u$ and put
$s_u=|\Lambda_u|$. Let $n_a$ count next children whose
maximum actual ternary height in $J_u$ is $a\in\{0,1,2\}$.
Every child is occupied, and
$n_0=q-c_1(u)$, $n_1=c_1(u)-c_2(u)$, $n_2=c_2(u)$.
Then

$$
\boxed{9n_0+3n_1+n_2
 =9q-6c_1(u)-2c_2(u)<27s_u.}
\tag{SC446}
$$

Indeed, if the capacity is at least $27s_u$, tile the whole
forest of $s_u$ old words by leaves of depths $3,4,5$.
Take $x_0=\min(n_0,3s_u)$ depth-three leaves, then
$x_1=\min(n_1,9s_u-3x_0)$ depth-four leaves, and use the
remaining $x_2=27s_u-9x_0-3x_1\le n_2$ depth-five leaves.
Choose the latter nodes below the unfilled earlier nodes,
so this is one prefix partition. Assign each leaf to a
different child of its type.

A used child has exactly one prefix. Every compatible
original $3^a q^Gm$ in it has $a$ at most that child's
maximum, so its inverse fits the fresh enclosure
$3^{3+a}q^{G-1}m$. The exponent and cofactor recover the
original numerical label. The same one-source argument
covers all of $E_u$; at most one replacement is charged to
each deleted original, and each charged modulus decreases
by the factor $27/q<1$. Thus SC438 applies even if every
child and every original is used. This proves the strict
inequality SC446 without an omitted-child requirement.

### The shallow phase inventory forces many mixed cofactors

Fix one of $q=107,109,113$. Distinct original numerical
labels $9qm$ have distinct cofactors $m$. By SC434 and
Report 385 GHA11, a $q$-free, 3-free cofactor with at most
one distinct prime factor has at most the following number
of available numerical values:

$$
\begin{aligned}
1+\sum_{\substack{5\le p\le113\text{ prime}\\p\ne q}}
 \left(10+\left\lfloor\frac{23}{p-1}\right\rfloor\right)
 &=1+15+13+12+4\cdot11+20\cdot10\\
 &=285.
\end{aligned}
\tag{SC447}
$$

This is an upper envelope allowing every prime through 113;
an absent support prime only reduces it. Subtracting it from
the distinct actual cofactors required by SC444 gives

$$
\begin{array}{c|ccc}
q&107&109&113\\ \hline
\#\{m:9qm\in D,\ (m,3q)=1,\ \omega(m)\ge2\}
 &\ge200&\ge215&\ge245.
\end{array}
\tag{SC448}
$$

Here $\omega(m)$ counts distinct prime factors. Every counted
original has at least four distinct prime factors including
3 and $q$. The bounds concern one fixed $q$ at a time;
the same original can occur in the inventories for different
$q$, and no common pair of cofactor primes is forced.

These phase and numerical conclusions do not supply a common
cofactor point or coverage of a complete residual. The
qualified whole-menu entrances of the earlier exchanges
remain separate obligations. SC439 applies at every finite
coding-prime height but still grows with that height;
unrestricted odd distinct covering remains open. These are
ordinary mathematical deductions, with no Lean verification
of the exchanges or their consequences asserted here.

## 72. Adjacent mixed heights suffice for the q-tail code

For distinct original support primes $p,q$, define the numerical
profile of the same original EB1 family by

$$
h_j=\max\{v_p(d):d\in D,\ v_q(d)=j\},\qquad
0\le j\le G=H_q.
$$

Original divisor closure gives
$h_0=H_p\ge h_1\ge\cdots\ge h_G$ and supplies every pure
$q^j$. The strengthened all-height necessary condition is

$$
\boxed{q<p^{h_k+h_{k+1}+1}\qquad(0\le k<G).}
\tag{SC449}
$$

Report 385 HPM5 remains valid but has the weaker exponent
$\max(H_p,h_k+h_{k+1}+1)$. The full old $p$ coordinate must
remain in the comparison carrier; the code need only read the
digits tested by the originals it transports. These are separate
requirements. No restriction to ternary height two is used here.

### One contraction of all q-tails

First consider any finite distinct odd whole cover with every
modulus dividing $p^Hq^GM$, where $(M,pq)=1$ and $p,q$ are
distinct odd primes. Fix $0\le k<G$, an actual pure original
$q^{k+1}$, and nonnegative bounds $A,B$ satisfying

$$
v_q(d)>k\ \Longrightarrow\ v_p(d)\le A,
\qquad
v_q(d)=k\ \Longrightarrow\ v_p(d)\le B.
\tag{SC450}
$$

Suppose $q>p^{A+B+1}$. Set

$$
w=A+1,\quad E_j=B+jw\quad(1\le j\le G-k),\qquad
N=p^{\max(H,E_{G-k})}q^kM.
\tag{SC451}
$$

For each parent $u\bmod q^k$, inject the complete first
$p^{E_1}$-symbol alphabet into $q-1$ next digits. At the actual
parent of the pure $q^{k+1}$ original, omit that original's next
digit; elsewhere omit any digit. Encode each later block of $w$
base-$p$ digits into one base-$q$ digit. Both alphabet sizes
are smaller than $q$. Fix all these compatible injections once,
independently of every cofactor and original owner. Write their
prefix maps as $\theta_{u,j}$.

For an output $z\bmod N$, put $u=z\bmod q^k$ and define one
source by CRT:

$$
\Psi(z)\equiv z\pmod{p^H},\qquad
\Psi(z)\equiv u+q^k\theta_{u,G-k}(z)\pmod{q^G},\qquad
\Psi(z)\equiv z\pmod M.
\tag{SC452}
$$

The maximum in SC451 makes this well-defined even when the
entire code reads fewer than $H$ old digits. Retain every original
with $q$-height at most $k$ unchanged. Every coordinate tested by
such an original is preserved, so it contains $z$ exactly when it
contains $\Psi(z)$.

A transported original is $d=p^aq^{k+j}m$, with $a\le A$,
$j\ge1$, and $m\mid M$. Its literal $q$ phase fixes one parent
and one tail prefix. Injectivity gives either no inverse or one
$p$ prefix $c_d\bmod p^{E_j}$. Since $a\le A<E_1\le E_j$,
the old $p^a$ test is constant on that prefix. If compatible, the
complete inverse is exactly

$$
z\equiv u_d\pmod{q^k},\qquad
z\equiv c_d\pmod{p^{E_j}},\qquad
z\equiv\rho_d\pmod m.
\tag{SC453}
$$

Higher old $p$ digits impose no further condition: this transported
original does not test them. There is no safe-word or private-region
mask. Enclose each nonempty inverse by truncating its $p$ prefix to

$$
\kappa_j(a)=B+1+(j-1)(A+1)+a,
\qquad
\widehat d=p^{\kappa_j(a)}q^km.
\tag{SC454}
$$

Here $B<\kappa_j(a)\le E_j$. A retained label below $q$-height
$k$ has different $q$-height; a retained label at height $k$ has
$p$-height at most $B$. Thus none equals a new label. For new
labels, quotient and remainder of $\kappa_j(a)-B-1$ by $A+1$
recover $j-1,a$, and the prime-free cofactor recovers $m$.
Original numerical distinctness excludes every new/new collision.
The moduli are odd nonunits and divide $N$.

For every output, original coverage of the one source SC452
supplies an owner. A retained owner covers that output unchanged;
a transported owner covers it through SC453 and its enclosure.
The actual pure $q^{k+1}$ original has empty inverse because its
own parent's code excludes its next digit. Each other original
produces at most one class. This is a whole cover with at most
$K-1$ classes. Moreover, every charged modulus satisfies

$$
\frac{\widehat d}{d}
=\frac{p^{B+1}}q
 \left(\frac{p^{A+1}}q\right)^{j-1}<1,
\tag{SC455}
$$

so its numerical modulus sum also decreases. The construction
requires neither divisor closure nor extremality; those hypotheses
are used only when forbidding the resulting reduction.

For the EB1 profile take $A=h_{k+1}$ and $B=h_k$. Its monotonicity
supplies SC450. Count minimality prohibits $q>p^{A+B+1}$.
Equality is impossible for distinct primes: an exponent one would
give $q=p$, and a larger exponent makes the right side composite.
This proves SC449, including $A=B=0$ and $k=G-1$.

### Repeated larger primes force actual penultimate mixed labels

For any integer $r\ge1$, divisor closure and SC449 give

$$
\boxed{G\ge2,\ q\ge p^{2r-1}
\quad\Longrightarrow\quad p^r q^{G-1}\in D.}
\tag{SC456}
$$

Indeed, absence of that original label would imply both
$h_{G-1},h_G\le r-1$, contradicting SC449 at $k=G-1$.
In particular,

$$
\boxed{p<q,\ H_q\ge2\ \Longrightarrow\ pq^{H_q-1}\in D,}
\qquad
\boxed{p<q,\ pq\notin D\ \Longrightarrow\ H_q=1.}
\tag{SC457}
$$

At $p=3$, this forces $3q^{G-1}$ for $q\ge5$,
$9q^{G-1}$ for $q\ge29$, and $27q^{G-1}$ for $q\ge251$,
provided $G\ge2$. If the required $p$-height exceeds the original
height, it excludes that height/support combination. These are
actual individual numerical labels. Their phases are not prescribed,
and labels forced for separate primes do not supply their product
as another original, a common cofactor point, or a complete menu.

### Opposite concentrated colors become flatter

Retain Report 385 CP1's original private-root color convention.
Opposite concentrated primes have no original multiple of their
product. Hence the larger member of any opposite pair has height
one, by SC457, with no assumption on shared primes or on $H_3$.

If original 5 and 7 have opposite colors $S_5,S_7$, the same
family consequently satisfies

$$
\begin{gathered}
H_7=1,\qquad H_5\le7,\qquad H_3\le28,\\
H_r=1\quad(r\in(S_5\cup S_7)\setminus\{5\}),\\
r<49\quad(r\in S_5),\qquad
r<5^{H_5+1}\le5^8\quad(r\in S_7).
\end{gathered}
\tag{SC458}
$$

The first assertion uses the missing product 35. The height bound
on 5 is the existing OCP8 value $6+\lfloor4/4\rfloor=7$;
OCP6 supplies the ternary bound. Every member of $S_7$ exceeds 5,
and every member of $S_5\setminus\{5\}$ exceeds 7, so CP1 and
SC457 give the other height-one assertions. Existing HPM1, using
the opposite coding prime and zero mixed height, gives the two
displayed prime bounds. None of these steps bounds every shared
prime or makes shared primes squarefree. If the shared set is
additionally a singleton, Report 385 section 165 excludes
$H_5=H_7=1$, sharpening that particular branch to $2\le H_5\le7$.

More generally, if the shared set avoids $\{5,7,11,13\}$, the
existing GM1 choice supplies an opposite pair $5,\ell$ with
$\ell\in\{7,11,13\}$. Then

$$
H_\ell=1,\qquad r<\ell^2\le169\quad(r\text{ in 5's color}).
\tag{SC459}
$$

Every prime in the opposite color has height one. Primes in 5's
color above $\ell$ have height one; the smaller members are not
flattened by this argument.

SC449 controls adjacent mixed layers, not the unrestricted value
of $H_3$. For example, numerical profiles with arbitrarily large
$h_0=\cdots=h_{G-1}$ and $h_G=0$ can satisfy its inequalities
when $q<p^{h_{G-1}+1}$; this is a profile boundary, not a whole-cover
example. A uniform bound on all relevant mixed layers, or a forced
missing product for every repeated prime, remains unavailable.
These constructions and consumers are ordinary mathematical
deductions. No Lean verification of SC449--SC459 is asserted.

## 73. A terminal donor can use the local height profile and retained guards

The terminal construction can combine the adjacent-layer code with
a finer projection supplied by retained pure-power guards. In the
original ternary-height-two branch this yields

$$
\boxed{q\ge43\ \Longrightarrow\ 9q^{H_q}\in D,}
\qquad
\boxed{q\ge13,\ H_q\ge2\ \Longrightarrow\ 9q^{H_q-1}\in D.}
\tag{SC460}
$$

These improve the thresholds 47 in Report 385 GHA10 and 17 in
SC258, respectively. They supply actual original numerical labels;
their phases and joint cofactor service are separate questions.

### A choice of projection resolution

Use one original EB1 family with $Q=p^Hq^GM$ as in Section 72.
Fix $0\le k<G$, put $A=h_{k+1}$, $B=h_k$, and take the actual
pure $q^{k+1}$ donor. Its parent is $u\bmod q^k$. Delete exactly
the originals of $q$-height above $k$ in that parent, retaining
all others. Section 69's complete liability is

$$
E_u=[u]_{q^k}\times X_u,
\qquad X_u\subseteq\mathbb Z/p^H\mathbb Z\times\mathbb Z/M\mathbb Z.
$$

Choose an integer resolution $\tau$ with
$A\le\tau\le\min(H,B+1)$ and define

$$
\Lambda_\tau=\pi_{p^\tau}(X_u)
 =\pi_{p^\tau}(P_{q^{k+1}}),\qquad s_\tau=|\Lambda_\tau|,
\qquad
1\le s_\tau\le T_p(\tau)
 =p^\tau-\frac{p^\tau-1}{p-1}.
\tag{SC461}
$$

The upper bound uses the retained original pure $p$-power guards
through height $\tau$. Their progressions are disjoint by original
irredundancy, and the donor's private region avoids all of them.
At $\tau=0$, both the projection size and $T_p(0)$ equal one.

Set $E_j=A+B+1+(j-1)(A+1)$. Above $\Lambda_\tau$ there are
$p^{E_1-\tau}s_\tau$ prefixes of depth $E_1$. Choose one prefix
of depth $B+1$ above a word of $\Lambda_\tau$ and replace all
its $p^A$ fine descendants by that one terminal leaf. The resulting
partition has

$$
N_\tau=p^{A+B+1-\tau}s_\tau-p^A+1
\tag{SC462}
$$

leaves. Suppose $q>p^{B+1}$ and $q\ge N_\tau$. Inject these
leaves into the next $q$ digits, assigning the short leaf the actual
donor digit. Every later continuing leaf uses $p^{A+1}$ extensions,
which fit because $A\le B$. No continuing leaf uses the initial
donor digit.

### The same complete source, with a shorter code

Fix the code on the whole selected parent whose low $p^\tau$ word
lies in $\Lambda_\tau$, without intersecting each inverse with
$X_u$. Preserve the full old $p^H$ and $M$ coordinates at one
source, together with parent $u$. Continuing source digits come
from the code; the terminal source uses the donor's next digit.
The common comparison carrier may be taken as

$$
p^{\max(H,E_{G-k})}q^GM.
\tag{SC463}
$$

Here the full $q^G$ factor is retained: unlike the global deletion
in Section 72, higher-$q$ originals in other parents remain
unchanged. For an output in $E_u$, the complete preserved
$(p^H,M)$ coordinate remains in $X_u$, so the source is again
in the full deletion hole.

A removed original $p^aq^{k+j}m$ has $a\le A<E_1$. Its literal
$q$ prefix determines at most one continuing prefix of depth
$E_j$. That prefix already lies above $\Lambda_\tau$; its old
$p^a$ test is constant, and its literal $m$ phase is preserved.
Thus each nonempty continuing inverse is one whole AP with no
additional projection mask. Enclose it using the same exponent
$\kappa_j(a)=B+1+(j-1)(A+1)+a$ as in SC454. The terminal
donor uses modulus $p^{B+1}q^k$, exactly the slot $j=1,a=0,m=1$.
Its digit has no continuing inverse, so it receives no second class.

Every new modulus has $q$-height $k$ and $p$-height above global
$B$. This excludes collisions with retained originals, including
those outside the chosen parent. Quotient and remainder by $A+1$
recover the original $j,a$; the prime-free cofactor recovers $m$.
This gives distinct odd nonunit labels. The global numerical bound
$B=h_k$ cannot be replaced by a maximum restricted to the chosen
parent: a retained class in another parent can still have the same
numerical modulus.

Every continuing point in $E_u$ is covered through an original
owner of its one source. The terminal class covers its full leaf,
and unchanged retained originals cover outside $E_u$. At most one
replacement is charged to each deleted original. Each charged
modulus, including the donor's, has ratio

$$
\frac{p^{B+1}}q
 \left(\frac{p^{A+1}}q\right)^{j-1}<1.
$$

Hence this one whole replacement has $K'\le K$ and
$\Sigma'<\Sigma$, contradicting EB1. The exact necessary condition
for every allowed projection resolution is therefore

$$
\boxed{q\le p^{B+1}\quad\text{or}\quad q<N_\tau.}
\tag{SC464}
$$

The first alternative is the modulus-sum condition and cannot be
dropped because the actual private projection happens to be small.
Distinct primality excludes equality $q=p^{B+1}$. In particular,
with

$$
C_\tau=p^{A+B+1-\tau}T_p(\tau)-p^A+1,
\qquad
\boxed{q<\max\{p^{B+1},C_\tau\},}
\tag{SC465}
$$

one obtains a uniform bound from the retained guards. The strongest
allowed guard resolution in this construction is
$\tau_* =\min(H,B+1)$: the identity
$T_p(t+1)=pT_p(t)-1$ makes the normalized guard count decrease.
Actual normalized projection sizes also do not increase under
refinement, since $s_{t+1}\le p s_t$.

For $A\ge1$, $C_\tau>p^{B+1}$, so the maximum in SC465 can
be removed. Indeed, putting $n=B+1$ and using $\tau\le n$ gives
$C_\tau\ge p^A(T_p(n)-1)+1\ge(3p^n-1)/2>p^n$.
For $A=0$ and $\tau>0$, instead $C_\tau<p^{B+1}$; SC465
retains the maximum. The unrefined choice $\tau=A$ is valid
in both cases and gives $q<p^{B+1}T_p(A)-p^A+1$.

### Two strict ternary endpoints

At $p=3,H=2$, all possible adjacent pairs have the following
values at $\tau_* =\min(2,B+1)$:

| $A$ | $B$ | $\tau_*$ | $C_{\tau_*}$ | $p^{B+1}$ |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 0 | 1 | 2 | 3 |
| 0 | 1 | 2 | 5 | 9 |
| 0 | 2 | 2 | 15 | 27 |
| 1 | 1 | 2 | 13 | 9 |
| 1 | 2 | 2 | 43 | 27 |
| 2 | 2 | 2 | 127 | 27 |

If $h_G\le1$, take $k=G-1$; all its rows have
$\max(C_{\tau_*},p^{B+1})\le43$, so SC465 gives $q<43$.
Consequently $q\ge43$ forces $h_G=2$ and the actual original
$9q^G$. At the endpoint $q=43,A=1,B=2$, all 43 leaves fit,
and $43>27$ still makes the modulus sum strictly smaller.

If $G\ge2$ and $h_{G-1}\le1$, the same cut has
$A\le B\le1$. Its three rows all have strict upper bound at
most 13. Thus $q\ge13$ forces $h_{G-1}=2$ and the original
$9q^{G-1}$. At $q=13,A=B=1$, the equal leaf count still gives
strict sum descent because $13>9$. These prove SC460.

The unrefined projection $\tau=A$ gives 52 for $A=1,B=2$;
it does not produce the new prime endpoint 43. The finer retained
guard information is essential to this improvement. The last row
recovers Section 71's strict cutoff 127 and hence its largest-prime
bound 113. No smaller uniform support cutoff or complete exclusion
of the height-two branch follows here. SC460--SC465 are ordinary
mathematical deductions, without a claim of Lean verification.
