[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

<a id="common-spine-books-of-four-prime-pages"></a>
# Common-spine books of four-prime pages

Let \(\mathcal C\) be a finite family of congruence classes with pairwise
distinct odd moduli greater than one. Suppose the primes other than 3 and
5 can be partitioned into disjoint sets \(J_i\), each containing at most
two primes, such that every original modulus is supported on
\(\{3,5\}\cup J_i\) for some \(i\). In particular, no modulus contains
private primes from two different pages. There is no bound on the number
of pages, the number of original moduli, any prime-power height, or any
residue.

Then \(\mathcal C\) does not cover the integers. More precisely, on the
original complete 3- and 5-coordinates, let \(E\) consist of those words
admitting an avoiding extension through every page, including avoidance
of all original classes supported only on \(\{3,5\}\). Then
\[
 H_{35}(E)>\delta,
 \qquad
 \delta=\frac{968925187}{2025000000000}>0.
 \tag{BK1}
\]
Absent anchor coordinates may be added with no original constraints;
the Haar bound projects back to the original coordinates.

The prime-interaction graph may therefore be a subgraph of an arbitrarily
large book of \(K_4\)'s sharing the edge \(\{3,5\}\). Such a graph can
have one biconnected block of arbitrarily many vertices. This is outside
the previous restriction that every graph block have at most seven
vertices. It does not settle general edge-glued \(K_4\) graphs or
unrestricted Erdős #7.

This is an ordinary mathematical argument using the conditional
avoidance interface of [Chapter 23](23-conditional-kernels-and-recursive-block-noncoverage.md)
and the attributed ordinary source construction used in
[Chapter 30](30-six-prime-prefix-measures-close-all-six-vertex-blocks.md)
and [Chapter 31](31-seven-vertex-block-noncoverage-with-actual-prime-measures.md).
The accompanying exact-rational
certificate checks its finite inequalities. No Lean verification of
this theorem or of the source's all-height comparison is claimed.

## 1. Original coordinates and one-page boundary cost

Work on \(X_p=\mathbb Z/p^{h_p}\mathbb Z\), where \(h_p\) is the
maximum exponent of \(p\) in the entire original family, with uniform
law \(H_p\). Every original numerical modulus, complete exponent vector
and residue remains unchanged. Assign classes supported only on
\(\{3,5\}\) once to the common spine; every other class belongs to its
unique page. In particular, shared spine classes are not charged once
per page.

For a page with private primes \(q<r\), let \(V_q,V_r\) avoid its
original pure prime-power classes. Distinctness gives
\[
 H_q(V_q)\ge1-\sum_{e\ge1}q^{-e}=\frac{q-2}{q-1},
 \qquad b_q=\frac1{q-2},\quad b_r=\frac1{r-2}.
 \tag{BK2}
\]
Under the actual product law
\(\nu=H_q(\cdot\mid V_q)\otimes H_r(\cdot\mid V_r)\),
the sum of the probabilities of all literal cylinders with a given
nonempty private support \(S\) is at most
\(b_S=\prod_{p\in S}b_p\), when at most one original label is present
for each complete private exponent vector. This sums all positive
exponents, not only first digits.

Fix nonnegative cutoffs \(t_3,t_5\), and put
\[
 T=(t_3+1)(t_5+1)-1.
\]
At a fixed complete spine word, keep as shallow all classes whose anchor
exponents satisfy \(0\le a\le t_3\), \(0\le b\le t_5\). There are
\(T\) nonzero pairs \((a,b)\) in this rectangle. The zero pair supplies
only private mixed classes, because private pure classes have already
been removed. Therefore valid support caps are
\[
 v_{\{q\}}=Tb_q,\quad v_{\{r\}}=Tb_r,\quad
 v_{\{q,r\}}=(T+1)b_qb_r.
\]
Define
\[
 \begin{aligned}
 Z_q&=1-Tb_q,& Z_r&=1-Tb_r,\\
 Z&=(1-Tb_q)(1-Tb_r)-(T+1)b_qb_r\\
  &=1-T(b_q+b_r)+(T^2-T-1)b_qb_r,\\
 L&=b_qZ_r+b_rZ_q+b_qb_r
   =b_q+b_r+(1-2T)b_qb_r.
 \end{aligned}
 \tag{BK3}
\]
Assume \(Z_q,Z_r,Z>0\). These are all nonempty coordinate residuals
for the two-coordinate support system. The conditional Shearer
inequality used in Chapter 23 applies to the actual grouped shallow
events. If \(R_x\) is their avoiding set at spine word \(x\), then
\[
 \nu(R_x)\ge Z>0,\qquad
 \mu_x=\nu(\cdot\mid R_x),\qquad
 \mu_x(C)\le\nu(C)\frac{Z_{\{q,r\}\setminus S}}Z
 \tag{BK4}
\]
for every literal private cylinder \(C\) of support \(S\), with
\(Z_\varnothing=1\). These ratios refer to related events under the
same actual law. The law \(\mu_x\) may depend on the entire spine word.

Let \(B_{q,r}\subseteq X_3\times X_5\) be the set of spine words having
no avoiding private extension for this page, excluding spine-only
classes. A blocked word must have its entire shallow survivor covered
by matching deep labels. Integrate that union bound with respect to the
original joint law \(H_{35}=H_3\otimes H_5\). At each fixed exponent
pair \((a,b)\) and complete private cofactor \(d\), the original
numerical modulus \(3^a5^bd\) occurs at most once globally across its
residues. Its spine cylinder has mass \(3^{-a}5^{-b}\). Consequently
\[
 H_{35}(B_{q,r})\le K(q,r;t_3,t_5):=\frac LZ R(t_3,t_5),
 \tag{BK5}
\]
where
\[
 \begin{aligned}
 R(t_3,t_5)
 &=\sum_{\substack{a,b\ge0\\a>t_3\text{ or }b>t_5}}3^{-a}5^{-b}\\
 &=\frac{15}{8}\left(3^{-t_3-1}+5^{-t_5-1}
                         -3^{-t_3-1}5^{-t_5-1}\right).
 \end{aligned}
 \tag{BK6}
\]
In particular, both the \(a=0\) and \(b=0\) rows are included. A
cutoff beyond an original height merely inserts empty event families.
No class is replaced by a congruence for a prime divisor of its modulus.

Larger valid values of \(b_q,b_r\) can be inserted directly as event
caps in (BK3)--(BK5). This does not require an unproved monotonicity
assertion for the rational function \(L/Z\).

## 2. A summable cost for every remaining page

For a prime \(p\ge13\), let \(g(p)\) be the following safe cost for
a page whose smaller private prime is \(p\). For \(13\le p\le139\),
compare with the next prime \(p^+\) and use the specified rectangle in
(BK5). The actual larger prime is at least \(p^+\), so these are valid
dominating event caps.

| \(p\) | \(p^+\) | \((t_3,t_5)\) | \(g(p)\) |
|---:|---:|:---:|---:|
| 13 | 17 | (2,1) | 289/6480 |
| 17 | 19 | (3,1) | 133/5184 |
| 19 | 23 | (3,2) | 697/51840 |
| 23 | 29 | (4,2) | 2569/410400 |
| 29 | 31 | (4,3) | 5491/1620000 |
| 31 | 37 | (4,3) | 289/140000 |
| 37 | 41 | (5,3) | 13079/13608000 |
| 41 | 43 | (5,3) | 287/388800 |
| 43 | 47 | (5,4) | 111737/196830000 |
| 47 | 53 | (6,4) | 154019/554040000 |
| 53 | 59 | (7,4) | 60047/384912000 |
| 59 | 61 | (7,4) | 25181/233280000 |
| 61 | 67 | (7,5) | 15283/204120000 |
| 67 | 71 | (8,5) | 113767/2515050000 |
| 71 | 73 | (8,5) | 27461/852930000 |
| 73 | 79 | (8,5) | 168689/6889050000 |
| 79 | 83 | (8,5) | 207919/11263050000 |
| 83 | 89 | (9,6) | 4252363/359214750000 |
| 89 | 97 | (9,6) | 137173/21760650000 |
| 97 | 101 | (10,6) | 10976653/2657205000000 |
| 101 | 103 | (10,6) | 12508279/3675800250000 |
| 103 | 107 | (10,6) | 2807981/956593800000 |
| 107 | 109 | (10,7) | 2460341/1115370000000 |
| 109 | 113 | (10,7) | 189257/107163000000 |
| 113 | 127 | (11,7) | 2889137/2834352000000 |
| 127 | 131 | (11,7) | 799123/1364031900000 |
| 131 | 137 | (11,8) | 8447521/18748057500000 |
| 137 | 139 | (12,8) | 145445327/468332381250000 |
| 139 | 149 | (12,8) | 188014691/886842168750000 |

Every residual in (BK3) is strictly positive in these 29 rows, and
\[
 \sum_{13\le p\le139\text{ prime}}g(p)
 =\frac{129378033012643019407088509659194417}
        {1314113473353497969028644848080000000}
 <\frac{197}{2000}.
 \tag{BK7}
\]

For \(p\ge149\), set
\[
 n=\left\lfloor\sqrt{(p-2)/4}\right\rfloor,\qquad
 t_3=t_5=n-1,\qquad
 g(p)=\frac{15}{p-2}3^{-n}.
 \tag{BK8}
\]
To verify this cost, dominate both private caps by \(x=1/(p-2)\).
Here \(n\ge6\), \(T=n^2-1\ge2\), and \(Tx\le1/4\). Thus
\[
 Z_q=Z_r\ge\frac34,\quad
 Z=1-2Tx+(T^2-T-1)x^2\ge\frac12,\quad
 0<L\le2x,\quad R\le\frac{15}{4}3^{-n}.
\]
Substitution in (BK5) gives (BK8).

For the summation only, enlarge the primes \(p\ge149\) to all odd
integers \(p\ge147\). For each \(n\ge6\), the interval
\(4n^2\le p-2<4(n+1)^2\) contains exactly \(4n+2\) odd integers,
each with \(p-2\ge4n^2\). Therefore
\[
 \begin{aligned}
 \sum_{p\ge149\text{ prime}}g(p)
 &\le\sum_{n\ge6}\left(\frac{15}{n}+\frac{15}{2n^2}\right)3^{-n}\\
 &\le\left(\frac{45}{12}+\frac{45}{144}\right)3^{-6}
 =\frac{65}{11664}.
 \end{aligned}
 \tag{BK9}
\]
There are no primes between 139 and 149. Combining (BK7)--(BK9),
\[
 \sum_{p\ge13\text{ prime}}g(p)
 <\frac{197}{2000}+\frac{65}{11664}
 =\frac{75869}{729000}<S:=\frac{21}{200}.
 \tag{BK10}
\]
Disjoint private pairs have distinct smaller private primes. Thus the
sum of the actual page blockers is bounded by this single prime sum.
If a core has already used private primes \(u,v\ge13\), both are absent
from all remaining pages; the remaining sum is less than
\(S-g(u)-g(v)\), whether or not either would have been a page minimum.

## 3. Ordinary core measures retain the joint spine law

Use Michael Schroeder, *Nine Prime Divisors in Odd Distinct Covering
Systems*, version 1.0.1, DOI 10.5281/zenodo.22759614, specifically the
ordinary construction and comparison in Sections 3--5 and 8--9.
Chapter 30 records the source identity, inherited geometry and finite
measure transport; Chapter 31 gives the variable-actual-prime version.

The ordinary construction starts from \(\mathbf1_AH_{35}\), where
\(A\) avoids every completed spine-only class, and appends normalized
private-coordinate kernels followed by deletions. For every arbitrary
joint spine event \(D\), reverse integration gives
\[
 \mu(D\times X_{\mathrm{private}})
 \le H_{35}(A\cap D)\le H_{35}(D).
 \tag{BK11}
\]
This is source Lemma 3.2, equation (3.6), with arbitrary anchor part
\(D\) and no constrained later depth. It is a joint two-coordinate
bound, not an inference from the separate 3- and 5-marginals. Survivors
are never renormalized. Source coordinatewise normalizations preserve
the joint Haar inequality when undone.

The source's 32 basic anchor vertices are
\[
 (a,b,c,-1,j,0,0,0,-1),\quad
 a\in\{1,2\},\ b\in\{2,4\},\ c\in\{a,3-a\},\ 1\le j\le4.
\]
Their reserve in cell units of Haar mass \(1/135\) is
\[
 R_0=\frac{135}{4}+\gamma+(9-\gamma)
             \left(\frac{\mathbf1_{c=a}}5+\frac{\mathbf1_{j=a}}{20}\right),
 \qquad \gamma=3\mathbf1_{a=1}+\mathbf1_{b\equiv a\pmod3}.
 \tag{BK12}
\]
The ordinary completion of pure classes and the 15-class supplies this
reserve. No fixed-165 screen or special spatial deletion at 7 is used.
The source's completion preserves inclusion of the original covered
set; avoiding the completed family therefore avoids the original one.

The source reserve is affine and the ordinary losses are convex in the
basic anchor parameters, so the same vertex interpolation applies to
every prefix used below. Keeping no later stage gives an anchor-only
submeasure of mass at least \(1/4\). Keeping just the 7 and 11 stages,
with thresholds \((2,4)\), gives a four-coordinate submeasure satisfying
(BK11) and
\[
 \mu(X)\ge m_4:=\frac{697794991}{5400000000}>S.
 \tag{BK13}
\]

This four-coordinate measure can be transported from private primes
\((7,11)\) to any ordered actual private pair \((q,r)\) with
\(q\ge7,r\ge11\), while fixing the actual spine pointwise. For each
private prefix injection, pull back the original classes and construct
the source measure; then average its pushforwards over the finite set
of private digit shifts. Empty pullbacks are discarded; nonempty ones
retain their complete exponent vectors and distinctness. Because every
map fixes the spine, (BK11) holds for every pushforward and its average,
with mass still at least \(m_4\). Dependence of the source measure on
the injection is harmless because its domination holds separately for
each injection. Heights are those of the entire original family.

For actual private core primes \((7,11,u,v)\), \(13\le u<v\), use
the ordinary thresholds \((2,4,4,8)\). At a stage with prime \(p\)
and threshold \(t\), the kernel cap and denominator are
\[
 C_p=\frac{p-1}{p-1-t},\qquad \beta_p=p-1-t.
\]
The multiplier increments have tails \(\Pr(J_p\ge e)=C_p/p^e\) for
\(e\ge1\).
The inherited ordinary anchor geometry is unchanged; its multiplier
distribution and mean are recomputed using these actual parameters.
All thresholds and hinge ratios occur in the existing pinned geometry.
The table below gives certified lower masses \(m_6(u,v)\) from all
32 anchor vertices after these four stages.

The same numbers are valid lower proxies on the indicated prime ranges.
Indeed replacing an actual prime by a smaller allowed proxy increases
\(C_p/p^e\) at every depth and decreases the positive denominator.
Quantile coupling therefore orders the entire multiplier product and
its untruncated increasing hinge. Bound that proxy hinge by the source's
existing finite geometry and nonnegative exact-moment remainder. This
does not infer monotonicity from a difference of independently
truncated approximations. Both original numerical moduli and their
residues stay in the same actual core family.

## 4. Complete case split and the surviving joint boundary

If neither 7 nor 11 occurs, begin with the anchor reserve \(1/4\).
Every page has smaller private prime at least 13, and (BK10) leaves
joint boundary mass greater than \(1/4-S>\delta\).

If 7 and 11 occur in the same page, take that whole page as the core
and use (BK13). If just one of 7 and 11 occurs, take its whole page as
the core and transport (BK13) to its actual ordered private pair.
Every other private prime is at least 13. In either case the remaining
page blockers cost less than \(S\), leaving mass greater than
\[
 m_4-S=\frac{130794991}{5400000000}>\delta.
 \tag{BK14}
\]
There is no division by the core's mass in this comparison.

It remains that 7 and 11 occur in different pages. Their partners are
distinct primes \(u,v\ge13\); order them as \(u<v\). Take both
whole pages, together with every original spine-only class, as a single
six-coordinate core. Which of \(u,v\) is paired with 7 makes no
difference: the ordinary source bounds the full class inventory on
\(\{3,5,7,11,u,v\}\), so it covers either actual assignment.
Every remaining private pair avoids \(7,11,u,v\).

For each row below, \(D_g\) lists the fees definitely removable from
the global sum. For a large-prime range, use only the displayed fixed
fees and discard the other nonnegative discount. Each margin is
\(m_6+\sum_{p\in D_g}g(p)-S\).

| Actual prime range | Source proxy \((u_0,v_0)\) | \(m_6(u_0,v_0)\) | \(D_g\) | Exact positive margin |
|---|:---:|---:|:---:|---:|
| \(u\ge31,v>u\) | (31,37) | 24218314603/225000000000 | empty | 593314603/225000000000 |
| \(u=13,v\ge23\) | (13,23) | 5697682537/90000000000 | 13 | 2354142833/810000000000 |
| \((u,v)=(13,17)\) | (13,17) | 68006602781/1350000000000 | 13,17 | 7033450927/450000000000 |
| \((u,v)=(13,19)\) | (13,19) | 25384655303/450000000000 | 13,19 | 12763340909/1350000000000 |
| \(u=17,v\ge23\) | (17,23) | 4074330479/50000000000 | 17 | 8677018799/4050000000000 |
| \((u,v)=(17,19)\) | (17,19) | 101751614161/1350000000000 | 17,19 | 38364217483/4050000000000 |
| \(u=19,v\ge31\) | (19,31) | 20707484743/225000000000 | 19 | 968925187/2025000000000 |
| \((u,v)=(19,23)\) | (19,23) | 19501966951/225000000000 | 19,23 | 53109786121/38475000000000 |
| \((u,v)=(19,29)\) | (19,29) | 15372389347/168750000000 | 19,29 | 247249361/84375000000 |
| \(u=23,v\ge37\) | (23,37) | 15088439533/150000000000 | 23 | 47435660143/25650000000000 |
| \((u,v)=(23,29)\) | (23,29) | 14668420717/150000000000 | 23,29 | 187659827821/76950000000000 |
| \((u,v)=(23,31)\) | (23,31) | 16652320951/168750000000 | 23,31 | 14995812161/7481250000000 |
| \(u=29,v\ge31\) | (29,31) | 141066283163/1350000000000 | 29 | 11676349489/4050000000000 |

These 13 branches exhaust every ordered prime pair \(13\le u<v\).
The smallest margin is \(\delta\) in (BK1), at the range
\(u=19,v\ge31\).

Let \(\mu\) be the actual core submeasure in the applicable case and
\(\sigma\) its full joint spine marginal. It is supported on core-
extendable words, \(\sigma\le H_{35}\), and
\(\sigma(X_{35})\ge m\). Delete from this same measure the actual
remaining-page blockers. By (BK5), (BK10), and the discounts,
\[
 \sigma\left(X_{35}\setminus\bigcup_{i\text{ outside core}}B_i\right)
 \ge m-\sum_{i\text{ outside core}}H_{35}(B_i)>\delta.
 \tag{BK15}
\]
Every word still supporting this measure has an avoiding core extension
and an avoiding extension on each remaining page. The private coordinate
sets are disjoint, so these extensions concatenate while retaining the
same spine word. All original labels are assigned either to the core
or exactly one page. The resulting full tuple avoids the whole family.
Since \(\sigma\le H_{35}\), (BK15) also proves (BK1). The finite CRT
then supplies an uncovered integer residue.

For a page having just one private prime, add a new distinct dummy prime
larger than every original prime and 149, used by no original label.
Give it a full coordinate domain and exponent zero in every original
modulus. This is an additional independent coordinate, not replacement
of any original prime or numerical modulus. Each such page becomes a
two-private-prime page; removing dummy coordinates from an avoiding
tuple recovers the original problem. All dummies are different, so the
disjointness and summation argument remain valid. Pages with no private
coordinate are already part of the once-owned spine family.

## 5. Exact arithmetic and inherited verification boundary

The accompanying [spine_book_certificate.py](../frontier/cover-geometry/spine_book_certificate.py)
and its [exact output](../frontier/cover-geometry/spine_book_certificate.json)
check all 29 displayed
page costs and residuals, the exact finite sum and analytic-tail
constant, (BK13), and every one of the 13 core rows at all 32 basic
vertices. It imports only the pinned project helper
[six_prime_prefix_certificate.py](../frontier/cover-geometry/six_prime_prefix_certificate.py),
not the source author's verifier.
It reads the already certified 72 geometry batches with 51,840 integer
queries, verifies their existing hashes, and does not regenerate
geometry. The geometry SHA-256 is
`0f65a963f617867e87021c695a5ded8ad18cb1217857c0bbc7d49652b0f5fdd1`;
the helper SHA-256 is
`3077f18fd91bf8f3a45483690b5f2d1386f1f692dccd9a453c43c99a8746daf4`.

For each changed source-prime pair, the producer recomputes the exact
multiplier probabilities below 32 and the full product mean. All
thresholds are at most 8, so every required below-threshold probability
is retained exactly; the omitted upper range is handled by the inherited
exact-moment remainder. Costs are rounded upward to multiples of
\(10^{-10}\), and the lower mass is the minimum of the 32 reserve-minus-
cost values divided by 135.

These calculations check rational inequalities and explicit parameter
substitutions. The inherited geometry soundness, all-height ordinary
comparison, completion, actual kernel construction, joint marginal
domination, and the conditional page argument remain the mathematical
premises described above. Finite numerical success alone is not used
to assert the unbounded theorem: (BK8)--(BK10), the source coupling and
the exhaustive prime-range partition supply its infinite-range steps.
