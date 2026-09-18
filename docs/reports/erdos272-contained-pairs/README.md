# A contained-pair injection for internally admissible centered families

This note proves three local results related to Erdős Problem 272: a
contained-pair injection, a three-avoider one-slack exclusion, and a
Boolean-square two-slack exclusion. The exclusions use the injection's
explicit construction. The note does not determine the unrestricted
extremum in that problem.

Write \([N]=\{1,\ldots,N\}\). A finite arithmetic progression (AP) may have
one or two elements. For a finite family \(\mathcal C\) of finite integer
sets, define its pair shadow by

\[
 S_2(\mathcal C)=
 \bigl\{\{x,y\}:x\ne y\text{ and }\{x,y\}\subseteq A
                 \text{ for some }A\in\mathcal C\bigr\}.
\]

## Theorem J (external-witness contained-pair injection)

For every integer \(N\geq 1\), every \(c\in[N]\), every finite family
\(\mathcal C\) of distinct subsets of \([N]\), and every \(W\subseteq[N]\),
assume that

1. \(c\in A\) for every \(A\in\mathcal C\);
2. \(A\cap B\) is a nonempty finite AP whenever \(A,B\in\mathcal C\) are
   distinct;
3. \(c\notin W\); and
4. \(A\cap W\) is a nonempty finite AP for every \(A\in\mathcal C\).

Then there is an injection

\[
 f:\mathcal C\longrightarrow S_2(\mathcal C)
 \quad\text{such that}\quad f(A)\subseteq A
 \quad(A\in\mathcal C).
\]

In particular, \(|\mathcal C|\leq |S_2(\mathcal C)|\). The members of
\(\mathcal C\) themselves are not assumed to be APs.

The internal condition 2 is essential. Without it, take \(N=4\), \(c=1\),
\(W=\{2,3,4\}\), and

\[
 \mathcal C=\bigl\{\{1\}\cup X:\varnothing\ne X\subseteq W\bigr\}.
\]

All seven external intersections are APs, but \(|S_2(\mathcal C)|=6\).
For example, the intersection of \(\{1,2,4\}\) with \([4]\) is the non-AP
set \(\{1,2,4\}\), so condition 2 fails exactly where it is needed.

## 1. Bad pairs and private pairs

Translate \(c\) to \(0\) for the proof. A pair \(\{u,v\}\), with
\(u,v\ne0\), is **bad** if \(\{0,u,v\}\) is not an AP. Equivalently, the
two nonzero integers are not related by

\[
 v\in\{-u,2u,u/2\}.
\]

We use the following private-pair lemma. Its determining-triple mechanism
is known from Simonovits--Sós (1981, proof of Theorem 3, printed p. 371),
and the bad-pair form used here is Yang's Theorem 5.2.

**Private-pair lemma.** Let \(\mathcal L\) be a finite family of distinct
sets, each containing \(0\) and at least three other integers, such that the
intersection of every two distinct members is an AP. Every member of
\(\mathcal L\) that is not itself an AP contains a bad pair contained in no
other member of \(\mathcal L\).

Here is a proof for completeness. The relation displayed above has no
triangle on the nonzero integers: after fixing one vertex \(a\), direct
comparison of its three possible partners with the partners of \(-a\),
\(2a\), or \(a/2\) gives no third vertex. Thus any member with three
nonzero elements contains a bad pair.

If distinct members contain the same bad pair \(\{u,v\}\), their
intersection is an AP through \(0,u,v\). Its difference \(\delta\) divides
\(\gcd(|u|,|v|)\), and both members contain every multiple of \(\delta\)
between \(\min(0,u,v)\) and \(\max(0,u,v)\). Call a bad pair with this
property *spanned*. A bad pair that is not spanned cannot occur in another
member.

Suppose, towards a contradiction, that every bad pair in a non-AP member
\(A\) is spanned. Choose the least positive spanning difference
\(\delta_0\). A pair spanned at \(\delta_0\) gives in \(A\) both
\(s\delta_0\) and \(2t\delta_0\) for some signs \(s,t\). If
\(w\in A\) is not divisible by \(\delta_0\), then
\(\{s\delta_0,w\}\) is bad unless \(w=s\delta_0/2\); its spanning
difference is then a proper divisor of \(\delta_0\). In the exceptional
case, \(\{s\delta_0/2,2t\delta_0\}\) is bad and has the same consequence.
Both contradict minimality. Hence \(A\subseteq\delta_0\mathbb Z\).

Scale by \(\delta_0\). The original spanning interval puts \(1\) or
\(-1\) in \(A\). If \(1\in A\), every \(w\geq3\) or \(w\leq-2\) in
\(A\) makes a bad pair with \(1\), and its only possible spanning
difference is \(1\). All intervening integers therefore lie in \(A\); the
remaining possible points \(-1,2\) create no gaps. If only \(-1\in A\),
the same argument either produces \(1\) from a point \(w\geq2\), or, by
reflection, fills the interval to the left. Thus \(A\) is an AP, the desired
contradiction. The lemma follows.

## 2. A universal matching for the AP members

Every AP through \(0\) with at least four terms is uniquely

\[
 Q(d,l,r)=\{-ld,(-l+1)d,\ldots,rd\},
 \qquad d\geq1,\quad l,r\geq0,\quad l+r\geq3.
\]

We construct, simultaneously for every such AP except \(Q(d,2,2)\), a
distinct contained bad pair. The construction is universal: restricting it
to the APs that occur in \(\mathcal C\) remains an injection.

Work one difference \(d\) at a time. Every image will have absolute gcd
\(d\), so images from different differences cannot collide. If
\(l,r\geq1\) and \(\gcd(l,r)=1\), assign the endpoint pair
\(\{-ld,rd\}\). It is bad: an opposite-sign pair with \(0\) forms an AP
only when \(l=r\), while the only coprime equal case \(l=r=1\) has only
three terms. These cross-sign images are distinct.

All remaining APs will use pairs \(d\{i,j\}\), or their negatives, with

\[
 1\leq i<j,\qquad \gcd(i,j)=1,
 \qquad \{i,j\}\ne\{1,2\}.
\]

Such a same-sign pair is bad: \(\{0,i,j\}\) is an AP exactly when
\(j=2i\), and primitivity then forces \(\{i,j\}=\{1,2\}\).

Assign the remaining APs to a side and a threshold:

* \(Q(d,l,0)\), \(l\geq3\): negative side, threshold \(l\);
* \(Q(d,0,r)\), \(r\geq3\): positive side, threshold \(r\);
* \(l>r\geq1\), \(\gcd(l,r)>1\): negative side, threshold \(l\);
* \(r>l\geq1\), \(\gcd(l,r)>1\): positive side, threshold \(r\);
* \(l=r=k\geq3\): negative side for odd \(k\), positive side for even
  \(k\).

The omitted diagonal \(l=r=2\) is precisely the centered five-term AP.
A task of threshold \(k\) may use any still-unused primitive pair on its
assigned side whose maximum is at most \(k\). Such a pair is contained in
the corresponding AP.

It remains to prove that the nested supplies never run out. Put

\[
 S(m)=\sum_{j=1}^{m}\varphi(j),\qquad \varphi(1)=1.
\]

For \(m\geq2\), one side has \(S(m)-2\) eligible primitive pairs through
threshold \(m\): \(\sum_{j=2}^m\varphi(j)=S(m)-1\), with \(\{1,2\}\)
then removed. Before diagonal tasks, the number of possible tasks through
threshold \(m\) on either side is at most

\[
 (m-2)+\sum_{j=2}^{m}(j-1-\varphi(j))
   =\frac{m(m+1)}2-S(m)-1.
\]

The first term counts one-sided tasks. At threshold \(j\), the second term
counts smaller positive coordinates not coprime to \(j\). Therefore the
remaining capacity is

\[
 R(m)=2S(m)-\frac{m(m+1)}2-1.
\]

If

\[
 4S(m)\geq m(m+2), \tag{1}
\]

then \(R(m)\geq(m-2)/2\), and integrality gives
\(R(m)\geq\lceil(m-2)/2\rceil\). The odd diagonal tasks through \(m\)
number \(\lceil(m-2)/2\rceil\), and the even ones number
\(\lfloor(m-2)/2\rfloor\). Thus every threshold prefix on each side has at
least as many pairs as tasks. Ordering the finitely many tasks by threshold
and choosing any unused eligible pair gives the required greedy injection.

This prefix argument also handles unequal ambient sides. For fixed \(d\),
the available negative and positive lengths are
\(\lfloor(c-1)/d\rfloor\) and \(\lfloor(N-c)/d\rfloor\). Removing tasks
that do not fit on the opposite side can only decrease each prefix demand,
and every assigned pair lies on the side whose threshold it respects. No
infinite matching or symmetric-window assumption is used.

## 3. The totient inequality

We prove (1) for every \(m\geq2\). Let

\[
 Z=\sum_{k\geq1}\frac1{k^2}.
\]

An integral tail estimate gives the entirely rational bound

\[
 Z\leq1+\frac14+\frac19+\frac1{16}+\frac1{25}+\frac15
   =\frac{5989}{3600}<\frac53. \tag{2}
\]

Every noncoprime ordered pair in \([m]^2\) has both coordinates divisible
by \(2\), by \(3\), or by some integer \(k\geq5\) coprime to \(6\).
The union bound and \(\lfloor m/k\rfloor^2\leq m^2/k^2\) give

\[
 \#\{(a,b)\in[m]^2:\gcd(a,b)>1\}
 \leq m^2\left(\frac14+\frac19+
   \sum_{\substack{k\geq5\\(k,6)=1}}\frac1{k^2}\right)
 =m^2\left(\frac23Z-\frac{23}{36}\right)
 <\frac{17}{36}m^2. \tag{3}
\]

There are exactly \(2S(m)-1\) coprime ordered pairs in \([m]^2\), by
partitioning them according to their larger coordinate. Hence (3) yields

\[
 4S(m)>\frac{19}{18}m^2+2.
\]

For \(m\geq35\), this is at least \(m(m+2)\), because

\[
 m^2-36m+36\geq1
\]

at \(m=35\) and the left side is increasing thereafter. The exact finite
base \(2\leq m\leq34\) is checked by the accompanying verifier. In that
range \(S(34)=360\), and equality in (1) occurs exactly at \(m=2,4,6\).
This completes the universal AP matching.

## 4. Proof of Theorem J

If \(\mathcal C=\varnothing\), take the empty map. Otherwise
\(\{c\}\notin\mathcal C\), since it has empty intersection with \(W\).

For every two-element member \(A=\{c,x\}\), condition 4 forces
\(x\in W\); assign \(f(A)=\{c,x\}\). For every three-element member
\(A=\{c,x,y\}\), assign \(f(A)=\{x,y\}\). These assignments are
injective within each size class.

Let \(\mathcal L\) be the members with at least four elements. Assign every
non-AP member a private bad pair using Section 1. Assign every AP member
other than a centered five-term AP its contained bad pair using Section 2.
These images are all noncenter pairs. Private pairs cannot collide with any
other large-member image, and the universal AP matching is injective.
Nor can one of these bad pairs collide with \(\{x,y\}\) assigned to the
three-element member \(\{c,x,y\}\): equality would make that member a
non-AP subset of a distinct large member, contrary to the internal
intersection hypothesis.

It remains to assign the exceptional APs

\[
 Q_d=\{c-2d,c-d,c,c+d,c+2d\}\subseteq[N].
\]

Put \(H=[N]\setminus(\{c\}\cup W)\). At most two of the four noncentral
points of \(Q_d\) lie in \(W\), because no three of
\(\{-2d,-d,d,2d\}\), and not all four, form an AP. Thus every \(Q_d\)
contains at least two points of \(H\). Conversely, a point \(x\ne c\) lies
in at most two exceptional APs: their differences can only be
\(|x-c|\) or \(|x-c|/2\), with the latter present only when integral.

For any subcollection \(\mathcal E\) of exceptional APs, count incidences
with their neighbors in \(H\). There are at least \(2|\mathcal E|\)
incidences, while each neighbor contributes at most two. Hence
\(|N_H(\mathcal E)|\geq|\mathcal E|\). Hall's theorem gives an injection
that chooses for each \(Q_d\) a contained hole \(h_d\in H\). Set
\(f(Q_d)=\{c,h_d\}\).

The Hall images are distinct. They cannot collide with a two-element
member's image, whose noncentral point lies in \(W\), and they contain
\(c\), so they cannot collide with any noncenter image. Every assigned pair
is contained in its source member, hence belongs to \(S_2(\mathcal C)\).
All cases are now assigned without collision, proving the theorem.

## 5. Three avoiders cannot preserve a one-slack shadow

**Theorem (three-avoider one-slack exclusion).** Let \(c\) be an integer,
let \(\mathcal C\) be a finite family of distinct finite integer sets all
containing \(c\), and let \(W_1,W_2,W_3\) be three distinct finite integer
sets avoiding \(c\). Assume that every intersection of two distinct members
of

\[
 \mathcal F=\mathcal C\cup\{W_1,W_2,W_3\}
\]

is a nonempty AP, and that

\[
 S_2(\mathcal F)=S_2(\mathcal C),
 \qquad |S_2(\mathcal C)|=|\mathcal C|+1.
\]

Then no such \(\mathcal C,W_1,W_2,W_3\) exist.

**Proof.** If \(\mathcal C\) is empty, the second equality reads \(0=1\),
so assume it is nonempty. All the sets involved are finite. After one common
translation they lie in some \([N]\), and translation preserves APs and pair
shadows, so Theorem J applies to \(\mathcal C\) with any one of the three
outsiders as its external witness.

Put

\[
 \mathcal O=\{W_1,W_2,W_3\},\qquad
 U=\bigcup_{A\in\mathcal C}(A\setminus\{c\}),\qquad
 E=\{e:\{c,e\}\in\mathcal C\}.
\]

For each \(W\in\mathcal O\), choose an injection \(f_W\) given by the
construction in the proof of Theorem J. Its image has size
\(|\mathcal C|\) in the \((|\mathcal C|+1)\)-element set
\(S_2(\mathcal C)\), so exactly one pair is missed. The construction has the
following more precise property. Its two-element sources give exactly the
center pairs \(\{c,e\}\) with \(e\in E\); its three-element and ordinary
large sources give noncenter pairs; and its exceptional centered five-term
APs give pairs \(\{c,h\}\) with \(h\notin W\). Consequently, if
\(y\in W\cap(U\setminus E)\), then \(\{c,y\}\in S_2(\mathcal C)\) but
\(\{c,y\}\) is not in the image of \(f_W\). Hence

\[
 |W\cap(U\setminus E)|\leq1. \tag{4}
\]

Every \(e\in E\) belongs to every outsider: the member \(\{c,e\}\) must
meet \(W\), while \(c\notin W\). Moreover, \(E\ne\varnothing\). Indeed, if
\(E\) were empty and some outsider \(W\) contained distinct points \(y,z\),
then \(\{y,z\}\in S_2(\mathcal F)=S_2(\mathcal C)\), so \(y,z\in U\),
contradicting (4). All three outsiders would therefore be singletons. Their
pairwise nonempty intersections would make those singletons identical,
contrary to their distinctness.

Fix \(e\in E\). If \(y\in W\setminus E\), then
\(\{e,y\}\in S_2(\mathcal F)=S_2(\mathcal C)\), and hence \(y\in U\).
Together with (4) and \(E\subseteq W\), this proves that every outsider has
the form

\[
 W=E\quad\text{or}\quad W=E\cup\{x\},\qquad x\notin E. \tag{5}
\]

Distinct outsiders therefore have pairwise intersection exactly \(E\), and
at least two of the three are extensions by distinct points. For an
extension \(W_x=E\cup\{x\}\), the point \(x\) lies in \(U\). The preceding
description of \(f_{W_x}\) shows that \(\{c,x\}\) is missed, so it is the
unique missed pair.

Fix one extension witness \(W_x\), and let

\[
 Q_d=\{c-2d,c-d,c,c+d,c+2d\},\qquad d\geq1,
\]

be any exceptional centered five-term AP in \(\mathcal C\). Consider its
four noncenter pairs

\[
 \mathcal P_d=\bigl\{
 \{c-2d,c-d\},\{c-2d,c+2d\},
 \{c-d,c+d\},\{c+d,c+2d\}
 \bigr\}. \tag{6}
\]

Each pair in \(\mathcal P_d\), together with \(c\), is a three-term AP.
None is the missed center pair \(\{c,x\}\), so all four occur in the image
of \(f_{W_x}\). In the construction of Theorem J, every nonexceptional
large member receives a bad pair relative to \(c\), while every exceptional
member receives a center pair. Thus a noncenter pair in (6) which completes
with \(c\) to an AP can only be the image of its actual three-element member.
It follows that

\[
 \{c\}\cup p\in\mathcal C\qquad(p\in\mathcal P_d). \tag{7}
\]

For any outsider \(W\), its intersection with each member in (7) is
nonempty. Therefore

\[
 D_W=W\cap(Q_d\setminus\{c\})
\]

meets all four pairs in (6). It is also an AP, because it equals
\(W\cap Q_d\). After translating \(c\) to \(0\) and scaling by \(d\), it is
an AP contained in \(\{-2,-1,1,2\}\). Such an AP has at most two points,
whereas a set meeting all four edges

\[
 \{-2,-1\},\{-2,2\},\{-1,1\},\{1,2\}
\]

has at least two. The only two-point covers are the two disjoint diagonals
\(\{-2,1\}\) and \(\{-1,2\}\). Thus every outsider has one of these two
traces on \(Q_d\).

Because distinct outsiders intersect exactly in \(E\), for \(i\ne j\) we
have

\[
 D_{W_i}\cap D_{W_j}=E\cap(Q_d\setminus\{c\}). \tag{8}
\]

Two of the three traces coincide. Their intersection is that entire
diagonal, so (8) says that this diagonal is the trace of \(E\). The third
trace must be the same diagonal as well, since the alternative is disjoint.
Hence every outsider has exactly the trace of \(E\) on every exceptional
\(Q_d\). In particular, no extension point belongs to an exceptional
centered five-term member of \(\mathcal C\).

Finally choose two extensions \(W_x=E\cup\{x\}\) and
\(W_y=E\cup\{y\}\), with \(x\ne y\). For the separately constructed
injection \(f_{W_y}\), the unique missed pair is \(\{c,y\}\). Since
\(\{c,x\}\in S_2(\mathcal C)\), the distinct pair \(\{c,x\}\) must be in
the image of \(f_{W_y}\). It cannot come from a two-element member because
\(x\notin E\), and the only other center-pair images in the construction
come from exceptional centered five-term APs containing \(x\). The previous
paragraph rules those out, a contradiction. Notice that the proof uses each
witness-specific Hall matching only through its own outside-witness
property; it never identifies the matchings for two different outsiders.
\(\square\)

## 6. A Boolean square cannot preserve a two-slack shadow

**Theorem (standalone Boolean-square exclusion).** Let \(c\) be an integer
and \(\mathcal C\) a finite family of distinct finite integer sets, all
containing \(c\). Define

\[
 E=\{e\ne c:\{c,e\}\text{ is a two-element member of }\mathcal C\},
 \qquad |E|\geq2.
\]

Let \(x,y\) be distinct integers outside \(E\cup\{c\}\), and put

\[
 D=E\cup\{x,y\},\qquad
 \mathcal O=\{E,E\cup\{x\},E\cup\{y\},D\},\qquad
 \mathcal F=\mathcal C\cup\mathcal O.
\]

Assume that every intersection of two distinct members of \(\mathcal F\)
is a nonempty AP. Then the two equalities

\[
 S_2(\mathcal F)=S_2(\mathcal C),\qquad
 |S_2(\mathcal C)|=|\mathcal C|+2
\]

cannot both hold.

**Proof.** Suppose both equalities hold, and write

\[
 U=\bigcup_{A\in\mathcal C}(A\setminus\{c\}).
\]

All outsiders avoid \(c\), so they are distinct from the centered members.
There is no singleton centered member, since it would miss \(E\).
The outsider intersections show that \(E\), \(E\cup\{x\}\), and
\(E\cup\{y\}\) are APs. Also \(\{x,y\}\in S_2(\mathcal C)\), by the
unchanged-shadow hypothesis, so some actual member contains both points.
In particular \(D\subseteq U\).

**Endpoint geometry.** Write
\(E=\{a,a+t,\ldots,a+(m-1)t\}\), with \(t>0\) and \(m\geq2\).
If \(m\geq3\), the step \(\delta\) of any one-point AP extension of
\(E\) divides \(t\). Its span gives
\((m-1)t\leq m\delta\), so the positive integer \(t/\delta\) is one.
The new point is therefore an immediate endpoint extension. Since the two
extensions are distinct,
\(\{x,y\}=\{a-t,a+mt\}\).

If \(m=2\), the possible extension points are \(a-t,a+2t,a+t/2\),
the midpoint being available only if integral. To exclude a midpoint
choice, let \(B\in\mathcal C\) contain \(x,y\), and put
\(H=B\cap E\ne\varnothing\). Its intersection with \(D\) is the AP
\(H\cup\{x,y\}\). In coordinates taking \(E\) to \(\{0,2\}\), the
extension points are \(-2,4,1\). For \(\{x,y\}=\{-2,1\}\), the gap
lists of \(H\cup\{x,y\}\) for \(H=\{0\},\{2\},\{0,2\}\) are
\((2,1),(3,1),(2,1,1)\); for \(\{x,y\}=\{1,4\}\), they are
\((1,3),(1,2),(1,1,2)\). None is an AP. Hence only the two exterior
extensions remain. These coordinates are used solely for this three-point
classification, not to change the position of \(c\).

Relabel \(x,y\) so that \(x<y\). In all cases \(D\) is an AP with step
\(t\), endpoints \(x,y\), and interior exactly \(E\).

**A saturated witness and unspanned choices.** Apply the construction of
Theorem J with witness \(D\). A common translation of all the finite sets
into some \([N]\) suffices to apply J; it carries \(c\) along with every
set and preserves AP and shadow relations. For each non-AP member of size at least four
(a crooked member), choose the *unspanned* bad pair furnished by the proof
in Section 1. Explicitly, a pair \(\{u,v\}\) in such a member \(A\) is
spanned if some positive
\(\delta\mid\gcd(|u-c|,|v-c|)\) satisfies

\[
 (c+\delta\mathbb Z)\cap
 [\min(c,u,v),\max(c,u,v)]\subseteq A.
\]

Section 1 proves that every crooked member has a bad pair for which no
such \(\delta\) exists: otherwise its least spanning difference forces
the entire member to be an AP. Moreover, a shared bad pair would be
spanned by the actual AP intersection. Thus these choices are private
among all members of size at least four, not merely among crooked members.

Let \(f\) be the resulting injection. Its only center-pair images come
from the two-element members and the exceptional five-term APs
\(Q_d=\{c-2d,c-d,c,c+d,c+2d\}\), whose chosen holes avoid \(D\).
Since \(x,y\notin E\), \(f\) omits \(\{c,x\}\) and \(\{c,y\}\).
They belong to the shadow and, by the two-slack equality, exhaust its
complement:

\[
 \operatorname{im}f=S_2(\mathcal C)\setminus
 \bigl\{\{c,x\},\{c,y\}\bigr\}. \tag{9}
\]

In this construction a good noncenter pair (one that completes with \(c\)
to an AP) can only be the image of its actual three-element member.
Thus \(\{x,y\}\) is bad: otherwise (9) forces
\(\{c,x,y\}\in\mathcal C\), a member missing \(E\).

**No exceptional packets and no off-witness points.** For every exceptional
\(Q_d\in\mathcal C\), all four good pairs in (6) are hit by (9), so their
four actual centered triples belong to \(\mathcal C\). The trace
\(E\cap(Q_d\setminus\{c\})\) is an AP meeting all four pairs.
As in Section 5, the only such traces are the diagonals
\(\{c-2d,c+d\}\) and \(\{c-d,c+2d\}\): no three or four noncentral
points of \(Q_d\) form an AP, and these are the only two-point covers of
the four-cycle. The traces of \(E\cup\{x\}\) and \(E\cup\{y\}\)
contain this diagonal and are APs as well, so neither can add another
\(Q_d\) point. Consequently \(x,y\notin Q_d\), and exactly the other
two noncentral points of \(Q_d\) lie in \(Z=U\setminus D\).

Let \(k\) be the number of exceptional members. There are exactly
\(|U|\) center pairs in the shadow, and (9) hits \(|U|-2\) of them.
The construction supplies exactly \(|E|+k\) center images. Therefore

\[
 k=|U|-|E|-2=|Z|. \tag{10}
\]

Each exceptional packet contains exactly two \(Z\) points. Each
\(z\in Z\) belongs to at most two packets: their radii can only be
\(|z-c|\) and \(|z-c|/2\). The \(2k=2|Z|\) incidences therefore force
every \(z\in Z\) to belong to exactly two packets.
Join those two packets by an edge for each \(z\). Distinct intersecting
packets have radii \(d,2d\). Their only possible common noncentral points
are \(c-2d,c+2d\); the \(E\) diagonal in \(Q_d\) contains exactly one
of these, so at most one is in \(Z\). The graph is consequently simple,
and each vertex has degree two, one edge for each of its two \(Z\) points.
But it is a finite subgraph of the dyadic forest with edges \(d\)--\(2d\).
In any nonempty such subgraph, a largest radius has at most the one
neighbor \(d/2\), contradicting degree two. Thus \(k=0\), and (10) gives

\[
 U=D. \tag{11}
\]

**The original endpoint source is an AP.** Let \(A\) be the unique source
with \(f(A)=\{x,y\}\). It is neither a two-element nor an exceptional
source, and cannot be a triple since that triple misses \(E\).
Hence \(|A|\geq4\). The trace \(P=A\cap D\) is an AP containing
\(x,y\) and at least one point of \(E\). Its endpoints are \(x,y\).
Write its step as \(h>0\), its neighbors at the endpoints as
\(u=x+h\) and \(v=y-h\), and \(y-x=nh\) with \(n\geq2\).

The pairs \(\{x,u\}\) and \(\{v,y\}\) are distinct from each other
and from \(\{x,y\}\). By (9), they have sources \(B_x,B_y\) distinct
from \(A\). The actual intersections
\(I_x=A\cap B_x\) and \(I_y=A\cap B_y\) are APs containing,
respectively, \(c,x,u\) and \(c,v,y\). Let their positive steps be
\(\delta_x,\delta_y\), and put

\[
 g=\gcd(|c-x|,y-x)=\gcd(|x-c|,|y-c|)>0.
\]

We have \(\delta_x\mid h\) and \(\delta_x\mid(c-x)\), hence
\(\delta_x\mid g\); similarly \(\delta_y\mid h\) and
\(\delta_y\mid(y-c)\), hence \(\delta_y\mid g\).
If \(c<x\), the interval of \(I_y\) contains \([c,y]\); since its
lattice contains \(c\) and its step divides \(g\), it contains the
entire \(g\)-step AP hull of \(c,x,y\). If \(c>y\), \(I_x\)
contains that hull on \([x,c]\). If \(x<c<y\), \(I_x\) contains all
\(c+g\mathbb Z\) points of \([x,c]\), and \(I_y\) contains all of
them in \([c,y]\). Their union again contains the entire hull.
These cases exhaust the possibilities since \(c\notin D\).
Thus \(\{x,y\}\) is spanned in \(A\), with spanning difference
\(g\). It cannot be the selected unspanned pair of a crooked source.
Therefore \(A\) is an ordinary AP of size at least four.

**The center is exterior on the actual witness lattice.** By (11), every
point of \(A\) other than \(c\) lies in \(D\subseteq x+t\mathbb Z\).
An AP of size at least four has an adjacent pair avoiding any specified
point: among its at least three adjacency edges, at most two touch that
point. Such a pair in \(A\) has both points in \(D\), so the positive
step \(s\) of \(A\) is an integer multiple of \(t\). Since \(A\)
contains \(c\) and a point of \(D\), this also gives
\(c\in x+t\mathbb Z\). The AP \(D\) contains *every* point of that
lattice in \([x,y]\), but does not contain \(c\). Hence
\(c<x\) or \(c>y\). This is a statement about the original integer
lattice, not an identification of \(D\cup\{c\}\) with an equally
sized interval. By (11), all other points of every centered member are
on the same side of \(c\). Every AP member therefore has endpoint
\(c\).

**A second contained injection.** Keep the two-element center images,
the triple noncenter images, and the crooked unspanned private bad pairs.
There are no exceptional packets. Each AP member of size at least four
now has the unique form

\[
 T=\{c,c+\varepsilon s,\ldots,c+\varepsilon ns\},
 \qquad \varepsilon\in\{-1,1\},\quad s>0,\quad n\geq3.
\]

Assign it its two consecutive points farthest from \(c\):

\[
 f'(T)=\{c+\varepsilon(n-1)s,c+\varepsilon ns\}.
\]

This pair is bad, since its two distances from \(c\) are \((n-1)s,ns\)
and \(n\ne2(n-1)\) for \(n\geq3\). It determines \(s\) by its gap,
\(\varepsilon\) by its side, and \(n\) by its far endpoint's distance
from \(c\); thus it determines the entire \(c\)-rooted progression.
Different AP sources cannot collide. Crooked images are private among
all large sources, so cannot collide with these or each other. A bad
large-source image cannot equal a triple image: the actual intersection
would then be the non-AP triple \(\{c\}\cup f'(T)\), or the analogous
triple for a crooked source. Center images cannot collide with noncenter
images, and the small-source assignments remain injective. Consequently
\(f'\) is a contained injection into \(S_2(\mathcal C)\).

Again \(f'\) omits \(\{c,x\}\) and \(\{c,y\}\), so the two-slack
equality forces it to hit every noncenter shadow pair, including
\(\{x,y\}\). That pair cannot be a triple image, since its centered
triple misses \(E\). It cannot be an AP image: any actual source
containing \(x,y\) meets \(E\), so contains a point strictly between
them, whereas the new AP image is an adjacent pair. Finally it cannot
be a crooked image: the original source \(A\) is a distinct large AP
containing \(x,y\), contradicting the crooked pair's privacy. No source
can supply the required image, a contradiction. \(\square\)

## Consequences and remaining boundary

If a globally admissible family \(\mathcal F\) has a member \(W\) avoiding
\(c\), apply Theorem J to the subfamily
\(\mathcal C=\{A\in\mathcal F:c\in A\}\). The global pairwise-intersection
condition supplies both the internal admissibility of \(\mathcal C\) and
the AP intersections \(A\cap W\), so

\[
 |\{A\in\mathcal F:c\in A\}|\leq
 |S_2(\{A\in\mathcal F:c\in A\})|.
\]

Theorem J alone does not simultaneously control all center choices or the
members outside that subfamily. The theorem in Section 5 rules out precisely
three distinct \(c\)-avoiding members when adding them leaves the centered
pair shadow unchanged and that shadow has one-pair slack. It does not supply
the upstream reductions needed to place every three-avoider configuration in
that equality regime. Section 6 excludes only the specified four-outsider
Boolean square with \(|E|\geq2\), unchanged shadow, and two-pair slack;
it is not a full four-avoider elimination and says nothing about five or
more avoiders. The shadow inequality
\(L:|\mathcal F|\leq|S_2(\mathcal F)|+1\) for every empty-core admissible
family remains unproved, as does the unrestricted all-\(N\) extremum.
The full Erdős Problem 272 remains open, and the solved-problem KPI
contribution of this note is zero.

## Source comparison and status

The determining/private mechanism is present in M. Simonovits and
V. T. Sós, *Intersection Properties of Subsets of Integers*, European
Journal of Combinatorics **2** (1981), 363--372, and in Zhanfu Yang,
*Exact values and exact upper bounds for families of integers with
arithmetic progression intersections (Erdős Problem #272)*,
arXiv:2607.23004v1 (25 July 2026), Theorem 5.2. Tibor Szabó,
*Intersection properties of subsets of integers*, European Journal of
Combinatorics **20** (1999), no. 5, 429--444, supplies the preceding
determining-triple, gcd-layer, totient-asymptotic, and construction
background.

Yang's version 1 already claims the finite extrema through \(N=12\)
(Theorem 1.1), the exact centered bound (Theorems 1.4 and 5.3), and the
private-pair theorem (Theorem 5.2); none is claimed here as new. On printed
page 5, Yang explicitly says that Lemma 3.3 counts covered witnesses rather
than matching each witness into its assigned member. In the inspected text,
neither Theorem J nor the universal containment-respecting matching of
Section 2 is stated, and no displayed result there directly implies J.

The hypotheses of Yang's Section 7 are materially different from those of
Section 5 above. Lemma 7.2 gives a private triple for a non-AP member of size
at least four. Theorem 7.5 assumes \(N\geq10^4\), \(|\mathcal F|>B(N)\),
and that every member of size at least four is an AP; Proposition 7.6
inherits that setting. Proposition 7.10 instead assumes a non-starred family
with a two-element member and gives a deduction involving the ambient bound
\(B(N)\); Corollary 7.11 additionally assumes \(|\mathcal F|>B(N)\). None of
those inspected statements is either the three-avoider one-slack exclusion
in Section 5 or the standalone Boolean-square two-slack exclusion in
Section 6. Both conclusions are local, with unchanged-shadow hypotheses
stronger in a different direction. Section 6 is a repo-derived paper
deduction from J's construction and the unspanned private-pair mechanism,
not an application of Yang's ambient-\([N]\) extremal bound.

These are bounded observations from Yang's version 1 and the supplied
current Erdős #272 and arXiv status pages, not a worldwide novelty or
priority guarantee. The supplied Erdős page records the problem as open and
lists zero proof claims; the supplied arXiv page lists Yang's version 1 and
still describes the unrestricted formula and kernel statement as
conjectural. These status snapshots are source inputs, not peer review. This
comparison does not certify every proof or computation in Yang's paper. The
current problem statement and open status used here are recorded by T. F.
Bloom,
*[Erdős Problem #272](https://www.erdosproblems.com/272)*, accessed
16 September 2026; the supplied status checks refreshed on 17 September
2026 again record open status, zero proof claims, and only Yang's version 1.
These bounded source checks do not establish worldwide novelty or validate
the present proof.

This report is an unformalized paper proof. It has no Lean implementation
and no kernel certification. The finite verifier uses exact integer
arithmetic, but establishes only the base \(m=2,\ldots,34\) in Section 3;
it does not test AP families, the matching, Hall's argument, Yang's
computations, either equality exclusion in Sections 5--6, or the
unrestricted problem. Independent review and repository CI are separate
from this paper proof.

Run it from the repository root, or replace the path by an absolute path
when running elsewhere:

```sh
python3 -I docs/reports/erdos272-contained-pairs/verify_totient_base.py
```

The program uses only the Python standard library, prints every exact
\(S(m)\) and slack \(4S(m)-m(m+2)\), and exits nonzero on any violated
inequality or endpoint check.
