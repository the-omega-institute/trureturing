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
