[Problem index](../../../../Problems/erdos-7-odd-covering-systems.md) ·
[Anchored three-predecessor orders](39-anchored-three-predecessor-orders-are-noncovering.md) ·
[Natural four-predecessor orders](41-natural-four-predecessor-orders-are-noncovering.md)

# Anchored four-predecessor orders close through a record-minimum potential

Let the original congruence family be finite, with distinct odd numerical
moduli greater than one. Its actual prime-interaction graph joins two
primes exactly when an original modulus contains both. Adjoin absent
anchors 3, 5 and 7 as free coordinates. Suppose the graph admits an order
beginning \(3,5,7\) in which every subsequent prime has at most four earlier
neighbours, counting anchors and private primes together. The rest of the
order need not be numerical.

Write \(P_*\) for the actual primes at least seven, \(M=|P_*|\), and \(U\)
for the set avoiding all original classes on their complete finite CRT
coordinates. The conclusion is

\[
 H(U)>\frac{107}{240000}\prod_{p\in P_*}C_p^{-1}
 \ge\frac{107}{240000}\left(\frac5{12}\right)^M>0,
 \tag{RM1}
\]

where

\[
 C_7=\frac32,\quad C_{11}=\frac53,\quad C_{13}=\frac{65}{33},
 \qquad C_p=\frac{9(p-1)}{4(p-2)}\quad(p\ge17).
 \tag{RM2}
\]

There are no restrictions on original exponent heights, residues, number
of primes, or overlap of predecessor sets beyond this graph order. Free
coordinates do not enter \(P_*\) or the density product. This extends the
order classes of Chapters 39 and 41, with a different density bound. It
is an ordinary deduction with an exact rational certificate, not a new
Lean theorem, an optimization over all schedules, or unrestricted odd
distinct noncoverage.

## 1. One original family and one normalized law

For each actual prime \(p\), choose a finite coordinate resolving its
maximum height across **all** original moduli, including later-owned
labels. Let \(H_p\) be uniform. Delete the original pure \(p\)-power
classes to form \(V_p\). Numerical distinctness gives

\[
 H_p(V_p)\ge1-\sum_{e\ge1}p^{-e}=\frac{p-2}{p-1}>0,
 \qquad \nu_p=H_p(\cdot\mid V_p)\le c_pH_p,
 \quad c_p=\frac{p-1}{p-2}.
 \tag{RM3}
\]

In particular every original depth-\(e\) cylinder has \(\nu_p\)-mass
at most \(c_pp^{-e}\). For a free coordinate use \(\nu_p=H_p\).
Start with the fixed root law \(\nu_3\otimes\nu_5\). The union of
original mixed-root classes has probability at most

\[
 c_3c_5\sum_{a,b\ge1}3^{-a}5^{-b}=\frac13.
 \tag{RM4}
\]

Do not condition the root law on mixed-root avoidance. Assign every
remaining nonpure original class to its last prime in the certified
order. Its other prime factors are actual earlier neighbours of that
prime. This assigns each remaining original label once.

Use the schedule

\[
 \delta_7=\frac15,\quad\delta_{11}=\frac13,\quad
 \delta_{13}=\frac{29}{65},\quad\delta_p=\frac59\ (p\ge17).
 \tag{RM5}
\]

At a complete preceding word \(x\), let \(B_p(x)\) be the actual union
of the assigned forbidden cylinders, and put
\(\alpha=\nu_p(B_p(x))\). Define the density relative to \(\nu_p\) by

\[
 k_p(x,y)=
 \begin{cases}
 [1-\min(\alpha,\delta_p)]^{-1},&y\notin B_p(x),\\
 (\alpha-\delta_p)_+/[\alpha(1-\delta_p)],&y\in B_p(x),\ \alpha>0,\\
 0,&y\in B_p(x),\ \alpha=0.
 \end{cases}
 \tag{RM6}
\]

For every \(0<\delta_p<1\), integration separately over the forbidden
set and its complement proves

\[
 K_p(x,X_p)=1,\quad K_p(x,\cdot)\le\frac{\nu_p}{1-\delta_p},
 \quad K_p(x,B_p(x))=\frac{(\alpha-\delta_p)_+}{1-\delta_p}.
 \tag{RM7}
\]

When \(\alpha\le\delta_p\), all mass lies on the complement. When
\(\alpha>\delta_p\), the two masses are
\((1-\alpha)/(1-\delta_p)\) and
\((\alpha-\delta_p)/(1-\delta_p)\). At \(\alpha=1\), the kernel is
\(\nu_p\) and the fee is one. Thus fully forbidden fibres remain
present and charged. The value \(5/9>1/2\) is legitimate by this direct
calculation; no imported theorem restricted to thresholds at most one
half is being applied beyond its hypotheses.

Append the kernels in the certified order to obtain one law
\(\mathbb P=\nu_3\nu_5\prod K_p\). Later normalized kernels preserve
every earlier marginal. From (RM3), (RM5) and (RM7),

\[
 K_p(x,\cdot)\le C_pH_p,\qquad
 \frac{d\mathbb P}{dH}\le\frac83\prod_{p\in P_*}C_p.
 \tag{RM8}
\]

The actual kernels of free coordinates are Haar, with density one.
Equation (RM8) multiplies conditional density bounds in this single
joint law, not separate marginal estimates.

## 2. Original labels first, auxiliary completion second

Define independent auxiliary variables \(N_q=1+L_q\) by

\[
 \Pr(L_q\ge e)=C_qq^{-e}\quad(e\ge1),
 \qquad C_3=2,\quad C_5=4/3,
 \tag{RM9}
\]

with the remaining constants from (RM2). Every right side lies in
\([0,1]\) and decreases with depth.

For stage \(p\), let \(A\) be its earlier-neighbour set. Bound the
actual forbidden union by the finite sum of its **original** labelled
cylinders. A label with numerical modulus
\(p^e\prod_{q\in A}q^{f_q}\) has current-coordinate weight at most
\(c_pp^{-e}\); its predecessor factors retain their original residues.
The positive-depth caps in (RM9) hold conditional on the entire preceding
history. If only selected coordinates in \(A\) are retained, conditioning
again on their preceding subhistory preserves these deterministic caps by
the tower property. No independence of actual coordinates is needed.

Apply the unrestricted-arity
[conditional convex comparison](../../../../Library/Arith/schroeder2026noncoverage.md#conditional-comparison-and-the-unrestricted-positive-part-bound)
to that finite original labelled sum and the increasing convex function
\((u-\delta_p)_+/(1-\delta_p)\). One independent auxiliary uniform is
shared by all labels at each selected coordinate. Only **after** that
comparison, complete the nonnegative exponent tuples. Numerical
distinctness permits at most one original label for each entire exponent
vector, and
\(\sum_{e\ge1}c_pp^{-e}=1/(p-2)\). The assigned-violation probability
is consequently at most

\[
 \frac{\mathbb E\bigl(\prod_{q\in A}N_q-1-
                  \delta_p(p-2)\bigr)_+}
 {(p-2)(1-\delta_p)}.
 \tag{RM10}
\]

Pure labels have already been removed, giving the subtraction of one.
All original heights are included. Infinite geometric completion is
justified by monotone convergence and the finite moments below. It
does not identify different original labels or assume compatible residues.

The auxiliary laws are ordered at every depth:

\[
 N_3\succeq N_5\succeq N_7\succeq N_{11}
 \succeq N_{13}\succeq N_{17}\succeq\cdots.
 \tag{RM11}
\]

Their first positive tails are
\(2/3,4/15,3/14,5/33,5/33,12/85,\ldots\).
For \(p\ge17\),
\(C_p/p=(9/8)(1/p+1/(p-2))\) decreases with \(p\).
After the first tail, each comparison acquires another factor of the
smaller-to-larger prime ratio. This proves (RM11) at all depths, including
the tied first tails at 11 and 13.

Put \(A_0=N_3N_5N_7\) and

\[
 G(p,m)=\frac{\mathbb E(A_0N_m-1-\delta_p(p-2))_+}
 {(p-2)(1-\delta_p)}.
 \tag{RM12}
\]

If every exposed prime beyond seven is at least \(m\), any at most four
actual predecessors are dominated by the four independent slots
\(N_3,N_5,N_7,N_m\). To see this, order the queried primes numerically:
their first three laws fit the first three slots by (RM11), and a fourth
queried prime must be beyond seven and at least \(m\). Pad missing slots
with one, then use independent common-uniform couplings. This comparison
does not insert new prime factors into any original modulus.

## 3. Availability is retained by a record-minimum potential

Let \(S=\{11,13,17,19,23,29,31\}\). Append any absent members as free
coordinates at the end of the order. Their actual fees are zero. Start
with state \(m=37\), inspect the \(S\)-subsequence, and after a member
\(p\) update \(m\) to \(\min(m,p)\).

Before each such stage, every previously exposed prime beyond seven is
at least \(m\): an exposed prime below 37 is in \(S\) and has been
included in the record; all others are at least 37. Interspersed larger
primes cannot break this invariant. The stage is therefore bounded by
\(G(p,m)\). Appending the free members lets the record end at 11 without
changing the original covered set or adding a density factor.

For \(p\in S\setminus\{11\}\), use base charge \(G(p,11)\).
If \(p>m\), (RM11) bounds its fee by this base charge. For a new record
\(p<m\), use potentials satisfying

\[
 G(p,m)+V_p\le G(p,11)+V_m\quad(p\ge13),\qquad
 G(11,m)\le V_m.
 \tag{RM13}
\]

The following rational table satisfies every required inequality:

| State \(m\) | Ceiling for \(10^6G(m,11)\) | \(10^6V_m\) |
|---|---:|---:|
| 13 | 118226 | 186346 |
| 17 | 54761 | 180678 |
| 19 | 40053 | 175304 |
| 23 | 21957 | 169900 |
| 29 | 10490 | 165919 |
| 31 | 8544 | 164966 |
| 37 | — | 162773 |

Precisely, calculate in increasing order

\[
 V_m=10^{-6}\left\lceil10^6\max\left(
 \{G(11,m)\}\cup
 \{G(p,m)-G(p,11)+V_p:13\le p<m,\ p\in S\}
 \right)\right\rceil.
 \tag{RM14}
\]

This is a fixed finite certificate, not an assertion of globally optimal
potentials or thresholds. Set \(V_{11}=0\). Each record transition pays
its base charge plus \(V_m-V_p\); the transition to 11 pays its remaining
potential. The differences telescope, and all later stages in \(S\)
are nonrecords. Consequently, in **every** order,

\[
 \sum_{p\in S}\text{actual fee at }p
 \le\sum_{p\in S\setminus\{11\}}G(p,11)+V_{37}
 \le\frac{254031+162773}{10^6}
 =\frac{416804}{10^6}<\frac{417}{1000}.
 \tag{RM15}
\]

There is one global record state and one charge per actual prime. There
is no page-by-page reset. A late small prime has a higher own fee, but
before it appears its auxiliary coordinate is unavailable; (RM13)
quantifies the corresponding saving.

## 4. Exact finite fees and a complete infinite-prime tail

For \(\rho_q(n)=\Pr(N_q=n)\),

\[
 \rho_q(1)=1-C_q/q,\qquad
 \rho_q(n)=C_q(q-1)q^{-n}\quad(n\ge2).
 \tag{RM16}
\]

Let \(t_p=1+\delta_p(p-2)\). Since
\(\mathbb EA_0=2(4/3)(5/4)=10/3\), the identity
\(\mathbb E(Z-t)_+=\mathbb EZ-t+\mathbb E(t-Z)_+\) gives

\[
 G(p,m)=\frac{\displaystyle
 \frac{10}{3}\left(1+\frac{C_m}{m-1}\right)-t_p+
 \sum_{abcd\le\lfloor t_p\rfloor}(t_p-abcd)
     \rho_3(a)\rho_5(b)\rho_7(c)\rho_m(d)}
 {(p-2)(1-\delta_p)}.
 \tag{RM17}
\]

The sum is finite; the exact mean retains the entire omitted upper tail.
The potential table needs products at most 17. For example,

\[
 G(11,13)=\frac{6187181701}{33202669500}<\frac{186346}{10^6},
 \qquad
 G(13,11)=\frac{1022528098912183}{8648966325037500}
 <\frac{118226}{10^6}.
 \tag{RM18}
\]

Prime seven has only the two roots before it. Its product threshold is
two, its denominator four, and
\(\mathbb E(N_3N_5)=8/3\), \(\Pr(N_3N_5=1)=11/45\). Its fee is

\[
 F_7=\frac{8/3-2+11/45}{4}=\frac{41}{180}.
 \tag{RM19}
\]

Every prime \(p\ge37\) is bounded by \(G(p,11)\), whatever its place
in the actual order. For the nineteen primes \(37\le p<127\), (RM17)
uses products at most 62. The sums of individual ceilings in units
\(10^{-7}\) are:

| Primes | Ceiling numerator |
|---|---:|
| 37, 41, 43, 47, 53 | 141314 |
| 59, 61, 67, 71, 73 | 28921 |
| 79, 83, 89, 97 | 7468 |
| 101, 103, 107, 109, 113 | 3622 |

Their sum is \(181325/10^7<91/5000\).

For the remaining primes put \(Y=N_3N_5N_7N_{11}-1\). Complete
geometric tail sums give:

| Variable | \(\mathbb EN\) | \(\mathbb EN^2\) | \(\mathbb EN^3\) | \(\mathbb EN^4\) |
|---|---:|---:|---:|---:|
| \(N_3\) | 2 | 5 | 31/2 | 59 |
| \(N_5\) | 4/3 | 13/6 | 107/24 | 277/24 |
| \(N_7\) | 5/4 | 11/6 | 79/24 | 131/18 |
| \(N_{11}\) | 7/6 | 23/15 | 713/300 | 1664/375 |

Each entry follows from
\(\mathbb EN_q^k=1+C_q\sum_{e\ge1}((e+1)^k-e^k)q^{-e}\).
Independence and the binomial expansion give
\(\mathbb EY^4=25915494211/1296000\).
For \(u\ge0,t>0\),

\[
 (u-t)_+\le\frac{27u^4}{256t^3}.
 \tag{RM20}
\]

For \(u\ge t\), multiply by \(256t^3\) and use
\(27u^4-256t^3(u-t)=(3u-4t)^2(3u^2+8ut+16t^2)\ge0\);
for \(u<t\) the claim is immediate. Substituting
\(t=(5/9)(p-2)\) into (RM12) gives

\[
 G(p,11)\le\frac{177147}{128000}
                 \frac{\mathbb EY^4}{(p-2)^4}\quad(p\ge127).
 \tag{RM21}
\]

Overcounting primes by odd integers, and bounding a decreasing sum by
its first term plus its integral, yields

\[
 \begin{aligned}
 \sum_{\substack{p\ge127\\p\ \mathrm{prime}}}G(p,11)
 &\le\frac{177147}{128000}\frac{25915494211}{1296000}
       \left(\frac1{125^4}+\frac1{6\cdot125^3}\right)\\
 &=\frac{2474903781656289}{10^{18}}<\frac1{400}.
 \end{aligned}
 \tag{RM22}
\]

No original-height truncation or unproved estimate on prime density is
used. The [producer](../frontier/cover-geometry/anchored_four_record_potential_certificate.py)
and [exact data](../frontier/cover-geometry/anchored_four_record_potential_certificate.json)
reproduce all fees, potentials, record inequalities, complete moments and
this tail. The producer reuses Chapter 37's SHA-pinned mass and moment
helper. It additionally checks all 5040 orders of the seven tracked
primes; the largest computed comparison total is
\(0.41680064206413464\ldots<0.416804\), attained, for example, at
\((17,13,11,19,23,29,31)\). That finite order check corroborates (RM15);
the arbitrary-family argument is its invariant and telescoping proof.

## 5. Full survival and Haar transport

Combining (RM15), (RM19), the middle-prime table and (RM22), the total
actual nonroot fee is strictly less than

\[
 \frac{41}{180}+\frac{417}{1000}+\frac{91}{5000}+\frac1{400}
 =\frac{59893}{90000}<\frac23.
 \tag{RM23}
\]

Pure classes have probability zero under the constructed law. Mixed-root
classes cost at most \(1/3\), and every other original class has one
stage owner. The union bound in that same law gives

\[
 \mathbb P(U)>1-\frac13-\frac{59893}{90000}
 =\frac{107}{90000}.
 \tag{RM24}
\]

Apply (RM8) to \(U\) to obtain (RM1). The largest value of \(C_p\), for
actual \(p\ge7\), is \(C_{17}=12/5\); the later constants decrease.
The finite CRT therefore supplies an avoiding integer.

## 6. What the order extension adds

For a concrete graph outside both earlier order hypotheses, take a
\(K_5\) on \(\{3,5,7,11,13\}\), and connect 29 to exactly
\(3,5,7,11,17\). The order
\((3,5,7,29,11,13,17)\) has subsequent predecessor counts
\(3,4,4,1\). Natural order instead gives 29 five earlier neighbours,
and the \(K_5\) prevents any order with at most three predecessors.
Realize the fifteen graph edges by their distinct pair-product moduli;
one may also include labels supported inside the displayed \(K_5\),
including its full five-prime product, without adding an edge. Arbitrary
residues and heights on allowed supports are covered by the theorem as
long as the complete numerical moduli remain distinct. This is a graph
class comparison, not a claim that every anchored four-predecessor graph
has this shape.

Every \(\{3,5\}\)-book with disjoint private pages of at most three
primes also fits the natural order: each private prime has at most two
earlier roots and two earlier private neighbours. For one page and a
fixed complete root word \(s\), let \(e_i(s)\) be its conditional sum
of actual stage fees. If \(W_i(s)\) is its original private Haar
survival probability, the same conditional union and density bounds give

\[
 W_i(s)\ge\frac{(1-e_i(s))_+}{\prod_{p\in\mathrm{page}\ i}C_p},
 \qquad \mathbf1_{\{W_i(s)=0\}}\le e_i(s).
 \tag{RM25}
\]

All pages use the same \(\nu_3\otimes\nu_5\); integrating and summing
the fees gives the bound (RM23). Zero-page fibres remain allowed and
charged. A separate page partition is not needed for the main theorem.

The new ingredient is the finite availability potential (RM13), used
with a changed rational schedule. The normalized-kernel architecture,
conditional convex comparison, geometric completion and moment inequality
are existing methods. The certificate does not make a priority claim.
For five or more actual predecessors the four-slot domination in (RM12)
is unavailable; additional original-label information or a stronger
comparison is still required.
