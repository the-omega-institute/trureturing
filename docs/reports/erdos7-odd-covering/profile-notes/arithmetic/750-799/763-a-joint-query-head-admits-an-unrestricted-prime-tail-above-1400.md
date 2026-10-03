# Eight small prime divisors with a missing small prime and an unrestricted tail

Let `C={a_m mod m}` be a finite family with pairwise distinct odd numerical moduli `m>1`, and let `N` be its least common multiple. Suppose

\[
 \#\{p:p\mid N,\ p\le1400\}\le8,
 \qquad \{3,5,7,11\}\not\subseteq\{p:p\mid N\}.
 \tag{ET1}
\]

Then `C` does not cover the integers. All original prime-power exponents, residues and support arities are unrestricted. There is no bound on the finite number of prime divisors greater than1400. In particular this applies when11 does not divide `N` and at most eight prime divisors are at most1400.

The construction gives a final **distorted** submeasure of mass greater than `1/256` supported outside the original classes. This number is not asserted as a lower bound for the final Haar or natural density. The empty family is immediate.

The proof retains the [existing ordinary source](../../../problem-details/68-eight-prime-core-omitting-eleven.md) **together with its complete query-pair bound**, transports both on the same measure, and applies the [joint-load continuation](../../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md). It uses the ordinary source and analytic premises specified below. It is an ordinary mathematical synthesis with exact rational arithmetic, not an end-to-end Lean result.

## 1. The existing ordinary source and its joint domination

Use reference primes and the existing six later thresholds

\[
 P_0=(3,5,7,13,17,19,23,29),\qquad
 t=(2,4,4,8,8,12).
 \tag{ET2}
\]

Chapter68 already evaluates this ordinary source row. Before any graph-attachment charge, it supplies an avoiding submeasure `mu` for every finite distinct-modulus family on this support, with

\[
 m_0:=\frac{10237584019}{168750000000}
 \le\mu(X)\le1,\qquad
 \mu\le D_0H_{P_0},\qquad D_0=\frac{297}{20}.
 \tag{ET3}
\]

No graph attachments are used here. The source mass is a lower bound, not an assertion that all families or vertices have equal mass. Its ordinary construction starts from anchor Haar restricted to an actual set `A` and uses normalized conditional kernels with full-coordinate caps

\[
 (C_7,C_{13},C_{17},C_{19},C_{23},C_{29})
 =\left(\frac32,\frac32,\frac43,\frac95,\frac{11}{7},\frac74\right).
 \tag{ET4}
\]

Here are the applicable source conditions. In Schroeder, *Nine Prime Divisors in Odd Distinct Covering Systems*, edition1.0.1, the countable completion lemma permits selecting just all pure prime powers and the15-class. For15 the proper-divisor reciprocal sum is `8/15<1`; for a pure power it is less than `1/(p-1)<=1/2`. Completion can change selected residues, but preserves the original covered subset. It is used only on the pullback head family.

The basic `3,5` anchor has eight coarse triples and four pure-5 budget vertices. Its32 basic evaluations, reserve and four anchor-region weights do not depend on the later primes. No enlarged seven-fibre source and no prescribed165-projection is used. Each threshold satisfies `1<=t_q<=q-2`, so

\[
 \beta_q=q-1-t_q>0,\quad C_q=(q-1)/\beta_q<q,\quad
 C_q(1-1/(q-1))\ge1.
\]

The full-coordinate kernel is therefore feasible, with the untruncated convex loss majorant `[1+Z_q-t_q]_+/beta_q`. Ordered increments and weighted aggregation retain every complete exponent-vector label and give auxiliary runs with tails `Pr(J_q>=e)=C_q/q^e`. These runs are comparison variables; the actual coordinates need not be independent.

The ordinary geometric queries use the unchanged anchor and thresholds `t/m` for `t` in `{2,4,8,12}`. Exact anchor tails and the full multiplier first moment account for every omitted exponent. The existing Chapter68 evaluator recomputes the multiplier distributions and six costs at (ET2), then takes the minimum of all32 common-vertex ledgers. Convex upper costs and the affine reserve use the same vertex. This is the ordinary source adaptation of [Chapter31, SV16--SV26](../../../problem-details/31-seven-vertex-block-noncoverage-with-actual-prime-measures.md); it does not change only one denominator in a first-eight-primes calculation.

The inherited finite geometry consists of the72 batches /51,840 integer queries already used in Chapters30,31,68. The consumer below re-evaluates their rational source formulas, without regenerating the geometric maxima or replacing the ordinary countable-completion and all-height comparison arguments.

The joint density cap in (ET3) follows directly from the conditional kernel representation: the anchor density is at most one, each normalized kernel has its cap in (ET4), and deletions decrease density. Their product is `D_0=297/20`. This is a pointwise joint statement, not a product of unproved marginal independence assertions. The more useful query estimate below retains the same representation and the pure-anchor restrictions.

## 2. A complete query-pair bound on this same source

At any full finite source heights, index one query cylinder by every divisor of the full period, including the unit divisor. A query layout chooses its residue independently for each complete exponent vector. Write

\[
 L_{\mathbf a}(x)=\sum_d\mathbf1_{x\equiv a_d\pmod d},
 \qquad
 \Gamma_Q(\mu)=\max_{\mathbf a}\int L_{\mathbf a}(x)^2\,d\mu(x).
 \tag{ET5}
\]

Query residues need not be compatible with each other or with the original forbidden residues. This is Chapter33's homogeneous joint-load invariant.

Pure completion at the two anchor coordinates gives disjoint pure-power forbidden unions `P_3,P_5`, with

\[
 s_3:=H_3(P_3^c)=\frac12,\qquad
 s_5:=H_5(P_5^c)=\frac34,
 \qquad A\subseteq P_3^c\times P_5^c.
 \tag{ET6}
\]

Fix any two complete query cylinders and let `e_i,f_i` be their depths in coordinate `i`. If the two prefixes are incompatible, their intersection is empty. Otherwise the intersection fixes depth `n_i=max(e_i,f_i)` in each constrained coordinate.

Dominate the live measure by the law with the same normalized kernels before the deletions, extending kernels to deleted histories as in the source's domination and first-hit lemma. Reverse integration gives a factor `C_q/q^{n_q}` at a constrained later coordinate and1 at an unconstrained later coordinate. At an anchor coordinate `p` it gives at most `p^{-n_p}` for `n_p>0`, and `s_p` for `n_p=0`; the two anchor factors multiply because the initial set is contained in the product in (ET6). Thus, for every pair on this one source,

\[
 \mu(E_{\mathbf e}\cap E_{\mathbf f})
 \le g_3(n_3)g_5(n_5)
       \prod_{q\in P_0\setminus\{3,5\}}g_q(n_q),
 \tag{ET7}
\]

where `g_p(0)=s_p`, `g_p(n)=p^{-n}` for `p=3,5`, and `g_q(0)=1`, `g_q(n)=C_q q^{-n}` for later `q` and positive `n`.

There is only **one** conditional cap per constrained coordinate in a pair intersection, not its square: an intersection is a single prefix cylinder. At maximum depth `n>=1` there are exactly `(n+1)^2-n^2=2n+1` ordered nonnegative exponent pairs. Hence

\[
 a(p):=\sum_{n\ge1}\frac{2n+1}{p^n}
      =\frac{3p-1}{(p-1)^2}.
 \tag{ET8}
\]

Summing (ET7) over every ordered divisor pair and enlarging each finite height sum to its convergent infinite sum proves, for every layout and every original source family,

\[
 \begin{aligned}
 \Gamma_Q(\mu)&\le G_0\!:=
   (s_3+a(3))(s_5+a(5))
   \prod_{q\in P_0\setminus\{3,5\}}(1+C_q a(q))\\
 &=\frac52\cdot\frac{13}{8}\cdot\frac{11}{6}
   \cdot\frac{67}{48}\cdot\frac{121}{96}\cdot\frac{59}{45}
   \cdot\frac{94}{77}\cdot\frac{267}{224}\\
 &=\frac{26010182627}{1040449536}<25.
 \end{aligned}
 \tag{ET9}
\]

All factors belong to the same physical conditional-kernel law that has mass at least `m_0`. The estimates do not combine separately optimized query laws. Undoing the source's Haar-preserving tree normalizations preserves the family of all prefix queries; finite projection preserves their integrals. Therefore `(mass>=m_0, Gamma<=G_0)` holds for the original source coordinates at any full original heights.

## 3. Average the measure and its query bound together

The general head condition is an ordered eight-prime tuple `r_1<...<r_8` with

\[
 r_i\ge(P_0)_i\quad(1\le i\le8).
 \tag{ET10}
\]

Actual head primes need not include3,5 or7. Choose finite coordinate heights resolving the whole original family, including every head exponent in tail-touching originals. Heights can be enlarged for source anchor resolution; original cylinders are simply lifted.

Use the finite prefix injections from Schroeder's AppendixC averaged prime replacement lemma. Independently at each coordinate and digit position, choose a uniform shift modulo `r_i` and send a source digit `u` to `u+shift mod r_i`. Since `(P_0)_i<=r_i`, each digit map is injective, and the product `F` is prefix preserving. The pullback of any target cylinder is empty or one source cylinder with the same complete exponent vector.

For each `F`, pull back **only the head-only original subfamily** and discard empty cylinders. Distinct nonzero exponent vectors are preserved. Apply the ordinary source construction to that family, obtaining `mu_F` which avoids it, has mass at least `m_0`, and satisfies the uniform query bound (ET9). Choose such a measure for each of the finitely many `F` and define

\[
 \mu_H=\mathbb E_F F_*\mu_F.
 \tag{ET11}
\]

This is one measure supported on the actual head survivor set, with `m_0<=mu_H(X)<=1`. Its choice may depend on `F`. No independence between `mu_F` and the injection is required.

For a fixed **target** query layout `L`, `L o F` is a partial source query layout: there is at most one nonempty source cylinder for each complete exponent vector. Fill each missing entry with any source cylinder. Since all summands are nonnegative, the resulting complete source load dominates `L o F` pointwise. Consequently, separately for every `F`,

\[
 \int(L\circ F)^2\,d\mu_F\le G_0.
\]

Averaging first and taking the maximum over target layouts afterwards gives

\[
 \Gamma_Q(\mu_H)
 =\max_L\mathbb E_F\int(L\circ F)^2\,d\mu_F
 \le G_0.
 \tag{ET12}
\]

This transports the full joint query bound, not just marginal cylinder bounds. It does not assume that independently optimal pullback laws can be combined: every `mu_F` already has the uniform bound for **all** its queries.

For completeness, the joint density cap also survives: applying `mu_F<=D_0 H_{P_0}` before averaging gives `mu_H(E)<=D_0 E_F H_{P_0}(F^{-1}E)=D_0 H_R(E)`, because each fixed source word has a uniform random target image. The continuation uses (ET12) directly and keeps the mass `m_0` on this same measure.

No graph-root, attachment or gluing obligation from Chapter73 is used here. The finite transport proof operates on the entire head family and all its query labels.

## 4. Padding and the precise role of11

For (ET1), take `R` to contain **all** original prime divisors at most1400. Choose a prime `q_*` in `{3,5,7,11}` absent from the original LCM. If `|R|<8`, add unused odd primes at most1400 while always excluding `q_*`, until eight coordinates are present. There are enough candidates already among the first nine odd primes. Give added coordinates finite positive heights and add no forbidden class.

The padded tuple still misses `q_*`, so its fourth prime is at least13. Primality and ordering then imply all inequalities in (ET10); the first three inequalities hold for every ordered tuple of odd primes. Every original nonhead prime is an arbitrary element of `(1400,infinity)`. Padding has not moved an original tail prime into the head.

The prime11 can occur in the head when the missing prime is3,5 or7. It cannot be treated as a tail prime: the head contains all original primes below the cutoff. In the special no11 statement, 11 is absent from the entire original LCM. Padding adds no restriction on the original family; a surviving padded word projects to a surviving original word.

## 5. Quarter-clipped continuation and a fourth-power tail

Process the actual tail primes in increasing order. Assign each tail-touching original class to its largest tail prime, retaining its full earlier numerical modulus, exponent data and actual residue. Pure current-prime classes have earlier modulus1. Distinctness provides at most one original class per complete exponent vector; labels are not identified merely because their supports agree.

Use the [existing normalized full-coordinate kernel](../../../problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md) at

\[
 \delta=\frac14,\qquad C=\frac1{1-\delta}=\frac43.
 \tag{ET13}
\]

For an earlier full word `x`, let `B_x` be the actual current bad union, including all pure current classes, and let `alpha(x)` be its Haar proportion on the complete current coordinate. Put `theta=min(alpha,delta)`. The density relative to current Haar is `1/(1-theta)` off the bad set and `(alpha-delta)_+/((1-delta)alpha)` on it, with the latter interpreted as zero when `alpha=0`. This kernel is normalized on every history, including a completely forbidden fibre, and is bounded by `C=4/3`. It preserves the complete earlier joint measure.

Chapter08's homogeneous transfer and bad-mass estimate, with `a(q)` from (ET8), give

\[
 \Gamma_{Qq^{A_q}}(\nu K_q)
 \le\Gamma_Q(\nu)(1+\tfrac43 a(q)),
 \qquad
 (\nu K_q)(B_q)
 \le\frac{4\Gamma_Q(\nu)}{3(q-1)^2}.
 \tag{ET14}
\]

For the second inequality, the actual charge is `E_nu(alpha-delta)_+/(1-delta)`. The pointwise bound `(alpha-delta)_+<=alpha^2/(4delta)` and the original-label second-moment estimate `E_nu alpha^2<=Gamma_Q(nu)/(q-1)^2` prove it. The old measure is unnormalized throughout; no head mass is divided out. All original exponent labels, including the unit earlier modulus, remain in the query inventory.

Let `x=1/(q-1)`. Then `a(q)=3x+2x^2`, and

\[
 (1+x)^4-\bigl(1+\tfrac43 a(q)\bigr)
 =\frac{10}{3}x^2+4x^3+x^4\ge0.
 \tag{ET15}
\]

Thus the complete preceding-tail growth is bounded by a fourth power of the reciprocal prime product. The analytic premise is the ratio bound derived from [Rosser--Schoenfeld Theorem8, equations(3.28)--(3.29)](../../../../../../Library/Arith/rosser1962approximate.md):

\[
 \prod_{B<p\le z}\frac p{p-1}
 \le c_\ell\frac{\log z}{\log B},\qquad
 c_\ell=\frac{2\ell^2+1}{2\ell^2-1},
 \quad B\ge286,\ \ell\ge4,\ 3^\ell\le B,\ z\ge B.
 \tag{ET16}
\]

This is the same inspected analytic premise as Chapter33 SH11; no stronger prime-product estimate is introduced. For a current tail prime `q>B`, enlarge its preceding prime product to every prime in `(B,q]`. Combining (ET12)--(ET16) bounds the charge at `q` by

\[
 \frac43G_0 c_\ell^4
 \left(\frac{\log q}{\log B}\right)^4\frac1{(q-1)^2}.
\]

Since `q/(q-1)<=B/(B-1)`, enlarge the sum over actual tail primes to all integers greater than `B`. The function `(log z/log B)^4/z^2` decreases for `log z>2`; the stated parameters have `log B>ell>=4`. The decreasing-sum integral comparison and four integrations by parts give

\[
 \begin{aligned}
 \sum_{n>B}\frac{(\log n/\log B)^4}{n^2}
 &\le\int_B^\infty\frac{(\log z/\log B)^4}{z^2}\,dz\\
 &=\frac1B\sum_{h=0}^4\frac{4!}{(4-h)!(\log B)^h}
 \le\frac1B\sum_{h=0}^4\frac{4!}{(4-h)!\ell^h}.
 \end{aligned}
\]

Consequently the entire tail charge is at most

\[
 \frac43G_0\tau_4(B,\ell),\qquad
 \tau_4(B,\ell)=\frac{c_\ell^4}{B}
   \left(\frac B{B-1}\right)^2
   \sum_{h=0}^4\frac{4!}{(4-h)!\ell^h}.
 \tag{ET17}
\]

The denominator here is `B-1`: the current base is complete-coordinate Haar, with no external restricted-domain denominator. The number of tail primes and their original heights are unrestricted within the finite original family.

Keep every tail bad set in the physical measure until the final union deletion. Each later normalized kernel preserves the entire earlier law, and hence the mass of every earlier bad set and the head measure. The sum in (ET17) therefore pays all original tail classes under **one** final measure.

For `B=1400`, `ell=6`, one has `3^6=729<=1400`, `log B>6>2`, and `c_ell=73/71`. Exact arithmetic gives

\[
 \sum_{h=0}^4\frac{4!}{(4-h)!6^h}=\frac{115}{54},
 \qquad
 \tau_4(1400,6)=\frac{2286058400500}{1342865721551787},
\]

\[
 \frac43G_0\tau_4(1400,6)
 =\frac{2123599874749732432625}{37424571881219517431808}.
 \tag{ET18}
\]

After deleting the actual tail bad union, the same law leaves

\[
 \begin{aligned}
 \mu_{\mathrm{final}}(X)
 &\ge m_0-\frac43G_0\tau_4(1400,6)\\
 &=\frac{7170057912347323462181930867}
        {1827371673887671749600000000000}
 >\frac1{256}>0.
 \end{aligned}
 \tag{ET19}
\]

The remaining set avoids every original head-only and tail-touching class. A tuple in its finite CRT carrier supplies an integer avoiding the original family. No restriction on original heights, tail length or support arity entered this continuation. The mass in (ET19) belongs to the constructed distorted law; no uniform final Haar-density lower bound of that size is asserted.

## 6. Reuse and verification boundary

The paired source bound `(mass>=m_0,Gamma<=G_0)` and its transport retain the information needed by the existing quarter-clipped transfer. The fourth-power prime-product estimate follows from the elementary identity (ET15). The source row is the stronger existing Chapter68 ordinary row; no new source geometry or new weight search is needed. In particular this continuation does not depend on the shallow-outside p29 certificate. Bare eight-prime noncoverage was already covered by the attributed source's general theorem.

Chapter33 retains its more general eight-prime head result at cutoff100000000 and its seven-prime head result at cutoff100000. The current hypothesis excludes heads containing all of3,5,7,11 and does not contain those other results. It is not a solution of unrestricted Erdős #7. The missing3 subcase already has stronger bare noncoverage results in the literature; no first noncoverage claim is made for that subcase.

The [standard-library consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_eight_head_tail.py) pins the existing Chapter68 evaluator, its ordinary helper and its geometry JSON. It re-evaluates all32 source vertices and checks (ET4),(ET9),(ET15),(ET18),(ET19) with exact fractions. Its [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_eight_head_tail.json) must agree with fresh recomputation. A separate arithmetic implementation obtains the joint moment from the equivalent pair sum, evaluates the integral by its integration-by-parts recurrence, and reproduces the final exact charge and margin. It neither regenerates the geometric maxima nor proves the ordinary source reduction, transport or analytic prime-product theorem; those are the explicitly supplied mathematical premises and arguments above.

Run from the repository root:

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_eight_head_tail.py
```

The inherited evaluator requires assertions enabled. The consumer rejects optimization mode before reading or executing that helper.

The directly inspected [Schroeder edition1.0.1 archive](../../../../../../Library/Arith/schroeder2026nine.md) has SHA256 `9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c`. Its countable-completion, capped-kernel, first-hit domination, ordered comparison, basic anchor, exact remainder and averaged prime-replacement statements supply the named source interfaces. No new Lean verification is claimed.
