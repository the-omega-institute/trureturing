# A contained-pair injection for internally admissible centered families

This note proves a local result related to Erdős Problem 272. It does not
determine the unrestricted extremum in that problem.

Write \([N]=\{1,\ldots,N\}\). A finite arithmetic progression (AP) may have
one or two elements. For a finite family \(\mathcal C\) of subsets of
\([N]\), define its pair shadow by

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

## Consequence and remaining boundary

If a globally admissible family \(\mathcal F\) has a member \(W\) avoiding
\(c\), apply Theorem J to the subfamily
\(\mathcal C=\{A\in\mathcal F:c\in A\}\). The global pairwise-intersection
condition supplies both the internal admissibility of \(\mathcal C\) and
the AP intersections \(A\cap W\), so

\[
 |\{A\in\mathcal F:c\in A\}|\leq
 |S_2(\{A\in\mathcal F:c\in A\})|.
\]

This does not simultaneously control all center choices or the members
outside that subfamily. In particular, the empty-core/global bound remains
unproved, the full Erdős Problem 272 remains open, and the solved-problem
KPI contribution of this note is zero.

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
than matching each witness into its assigned member. In the bounded source
comparison above, neither Theorem J nor the universal containment-respecting
matching of Section 2 is stated, and no statement there was found that
directly implies J. In particular, Yang's ambient cardinal bounds and
Proposition 7.10 do not produce an injection into the actual pair shadow.
This is a bounded observation, not a worldwide priority claim. It also does
not certify every proof or computation in Yang's paper. The current problem
statement and open status used here are recorded by T. F. Bloom,
*[Erdős Problem #272](https://www.erdosproblems.com/272)*, accessed
16 September 2026.

This report is an unformalized paper proof. It has no Lean implementation
and no kernel certification. The finite verifier uses exact integer
arithmetic, but establishes only the base \(m=2,\ldots,34\) in Section 3;
it does not test AP families, the matching, Hall's argument, Yang's
computations, or the unrestricted problem.

Run it from the repository root, or replace the path by an absolute path
when running elsewhere:

```sh
python3 -I docs/reports/erdos272-contained-pairs/verify_totient_base.py
```

The program uses only the Python standard library, prints every exact
\(S(m)\) and slack \(4S(m)-m(m+2)\), and exits nonzero on any violated
inequality or endpoint check.
