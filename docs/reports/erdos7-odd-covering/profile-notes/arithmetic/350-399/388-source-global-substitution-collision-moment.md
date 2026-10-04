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
