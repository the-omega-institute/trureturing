[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# Seven- and eight-prime heads with unrestricted large-prime tails

**Theorem.** Let a finite family of congruence classes have pairwise
distinct odd numerical moduli greater than one. If its least common
multiple has at most seven prime divisors at most 100000, the family
does not cover the integers. There is no bound on the number of prime
divisors greater than 100000, on any original exponent, or on the
number of primes dividing one modulus. No graph-block hypothesis is
required.

A second application, using Schroeder's attributed eight-prime
uncovered-density theorem, proves noncoverage when the least common
multiple has at most eight prime divisors at most 100000000, again
with arbitrary further primes. The two cutoffs trade head size for
tail size; neither restriction contains the other.

This is an ordinary mathematical deduction with exact rational
arithmetic. It uses Chapter 31's existing seven-coordinate measure,
Chapter 08's joint-load transfer, and the analytic prime-product
premise stated in Chapter 32. It is not an end-to-end Lean theorem
or a solution of unrestricted Erdős #7. An empty family is trivially
noncovering; the arguments below concern nonempty families.

## 1. The inherited seven-coordinate measure and its joint density

For the seven source primes

\[
 P_*=(3,5,7,11,13,17,19),
\]

Chapter 31's ordinary source construction with thresholds
\((2,4,4,8,8)\) gives, for every actual distinct-modulus family on
these coordinates, a positive submeasure \(\mu_*\) avoiding all its
classes and satisfying

\[
 m_*\le\mu_*(X)\le1,\qquad
 m_*={7235955529\over450000000000}>{2\over125}.
 \tag{SH1}
\]

This is the `children_lower_bounds=[5,7,11,13,17,19]` row of the
existing Chapter 31 certificate. The bound is the minimum of its
32 ordinary anchor-vertex ledgers. All geometric costs and their
infinite-depth remainders are inherited; they are not recomputed by
the small certificate accompanying this chapter. The outside-block
fee from that row is not subtracted: the present argument applies
directly to the entire family.

The construction also has the **joint**, pointwise density bound

\[
 \mu_*\le D_*H_{P_*},\qquad
 D_*={3\over2}{5\over3}{3\over2}\,2\,{9\over5}={27\over2}.
 \tag{SH2}
\]

Here is its source, independently of the marginal bounds. The anchor
measure is the unnormalized restriction \(H_{3,5}|_A\), with density
at most one. Each of the five later conditional kernels is normalized
for every complete earlier word and has pointwise density at most
the corresponding factor in (SH2), relative to its coordinate Haar
law. Their joint density is bounded by the product. Removing mixed
forbidden sets only decreases this density. The live measure is
never conditioned on survival. Haar-preserving normalizing tree
permutations leave the bound unchanged, and projection to any full
original finite heights also preserves it. Thus (SH2) does not infer
a joint bound by multiplying unconditional marginal bounds.

Both (SH1) and (SH2) hold at heights resolving the entire original
family, including classes that also contain later tail primes.

## 2. Transport to any seven actual odd primes

Let \(r_1<\cdots<r_7\) be arbitrary odd primes. Then \(r_i\ge p_i\)
for the ordered source list \(P_*\). At each digit position of each
coordinate independently choose a uniform additive shift modulo
\(r_i\). Mapping each source digit to its shifted value defines a
prefix-preserving injection from the source finite coordinate to the
target coordinate. Take each coordinate at least to its full original height. If needed,
pad the first source/target height to at least 3 and the second to
at least 2, so the anchor moduli 27 and 25 are resolved. Lift each
original cylinder without changing its residue condition. Denote
the resulting finite product injection by \(F\).

The inverse image of an original target congruence cylinder is
empty or a source cylinder with the same complete exponent vector.
Discard empty inverse images. Numerical distinctness of the original
moduli ensures distinct source moduli. For each of the finitely many
\(F\), choose a source measure \(\mu_F\) furnished by Section 1,
and define

\[
 \mu_H=\mathbb E_F F_*\mu_F.
 \tag{SH3}
\]

This measure avoids the actual target head family and has mass at
least \(m_*\) and at most one. For every target subset \(A\), the
pointwise source density bound gives

\[
 \mu_H(A)\le D_*\mathbb E_F H_{P_*}(F^{-1}A)
             =D_*H_R(A).
 \tag{SH4}
\]

For each fixed source word its random image is a uniform target
word, proving the equality. Although \(\mu_F\) depends on \(F\),
the density inequality is applied before averaging. No independence
of the coordinates of \(\mu_H\) is assumed or needed.

If fewer than seven actual primes occur below the cutoff, add
unused distinct odd primes below it to make seven coordinates and
initially give the unused coordinates height one, followed by the
anchor-height padding just described. This adds no forbidden
class and no condition to the original moduli. There are enough such
primes, for example the first seven odd primes already lie below the
cutoff. The theorem on the padded carrier gives an avoiding word
for the original coordinates by projection.

## 3. The existing homogeneous joint-load transfer

For the complete finite head period \(Q\), write

\[
 L_b(x)=\sum_{d\mid Q}\mathbf1_{x\equiv b_d\pmod d},\qquad
 \mathcal G_Q(\mu)=\max_b\int L_b(x)^2\,d\mu(x),
 \tag{SH5}
\]

including the unit divisor. The layout residues need not be
compatible. This is Chapter 08's \(\Gamma_Q\), extended there
homogeneously to arbitrary finite positive measures; it is not
the joint density cap \(D_*\).

Under product Haar measure, the intersection of two compatible
classes of moduli \(d,e\) has mass \(1/\operatorname{lcm}(d,e)\),
and an incompatible intersection has mass zero. Summing ordered
exponent pairs coordinatewise gives

\[
 \mathcal G_Q(H_R)
 \le M_2(R):=\prod_{p\in R}\left(1+{3p-1\over(p-1)^2}\right).
 \tag{SH6}
\]

Indeed, there are \(2a+1\) ordered nonnegative exponent pairs with
maximum \(a\), and
\(\sum_{a\ge1}(2a+1)p^{-a}=(3p-1)/(p-1)^2\).
Finite heights only decrease this sum. Equation (SH4) therefore
implies \(\mathcal G_Q(\mu_H)\le D_*M_2(R)\), regardless of head
correlations.

Take any finite set of new primes greater than an integer
\(B\ge286\), disjoint from the head. Process them in increasing
order, after all head coordinates. Assign every original tail-touching
class to its last tail coordinate. Its earlier modulus retains all
its complete head and earlier-tail exponents and its original
residues. Pure current-prime classes have earlier modulus 1 and
are included. No label is identified with another merely because
it has the same support.

At prime \(q\), let \(\nu\) be the current unnormalized measure
on the entire past. Use the **uniform law on the complete current
coordinate** as base, and let \(\alpha(x)\) be the proportion of
its actual current bad union, including pure powers. Chapter 08's
normalized capped-deletion kernel at threshold \(1/2\) has density

\[
 k_x(u)=
 \begin{cases}
 [1-\min(\alpha(x),1/2)]^{-1},&u\notin B_x,\\
 2(\alpha(x)-1/2)_+/\alpha(x),&u\in B_x.
 \end{cases}
 \tag{SH7}
\]

The second case is zero when \(\alpha=0\). This kernel is
normalized for every past word, including entirely forbidden
fibres, and its density relative to current Haar is at most 2.
Consequently it preserves the **entire** previous joint measure.
Chapter 08's (T1), or its homogeneous version (W1), gives

\[
 \mathcal G_{Qq^{H_q}}(\nu K_q)
 \le\mathcal G_Q(\nu)
 \left(1+2{3q-1\over(q-1)^2}\right).
 \tag{SH8}
\]

For completeness, applicability retains all original labels: at
each current exponent the earlier classes form a partial layout,
since at most one forbidden class has any given complete numerical
modulus. Complete it to a full layout, including the unit divisor.
For two exponent groups, weighted Cauchy--Schwarz bounds the old
product load by \(\mathcal G_Q(\nu)\). Each nonempty
current-prefix intersection has conditional mass at most
\(2q^{-\max(a,b)}\) given that same entire past. This is precisely
the pair counting in (T1); no product head law or head
conditional-prefix bounds are required.

The corresponding (T2) estimate is

\[
 \int\alpha^2\,d\nu
 \le\left(\sum_{a\ge1}q^{-a}\right)^2\mathcal G_Q(\nu)
 = {\mathcal G_Q(\nu)\over(q-1)^2}.
 \tag{SH9}
\]

The bad mass after the kernel is
\(2\int(\alpha-1/2)_+\,d\nu\le\int\alpha^2\,d\nu\).
Thus the current charge is at most the right side of (SH9).
No normalization of \(\nu\) enters either Cauchy--Schwarz or the
kernel formula. In particular, the head mass is not divided out.

Leave all tail bad sets in the physical measure until the final
union deletion. Every later kernel preserves each earlier bad-set
mass and the original head measure. The sum of the charges therefore
bounds the loss on **one and the same** final law. The whole final
mass before deletion equals the initial head mass, at most one.
Each tail marginal is bounded by \(2H_q\); all head marginal
bounds remain valid. Deleting the union only decreases these bounds.
Unlike the conditioned-domain construction of Chapter 32, this
application uses all original current forbidden classes on uniform
Haar and has no external descendant-domain or graph-fee hypothesis.

## 4. Uniform continuation over every large prime

For \(p\ge19\),

\[
 1+2{3p-1\over(p-1)^2}
 \le1+{2(3p-1)\over(p-1)(p-3)}
 \le1+{7\over p-1}
 \le\left({p\over p-1}\right)^7.
 \tag{SH10}
\]

Use the same analytic prime-product premise as Chapter 32:

\[
 \prod_{B<p\le z}{p\over p-1}
 \le c_\ell{\log z\over\log B},\qquad
 c_\ell={2\ell^2+1\over2\ell^2-1},
 \tag{SH11}
\]

for \(B\ge286\), integer \(\ell\ge4\), \(3^\ell\le B\),
and \(z\ge B\). Chapter 32 identifies the inspected pinned
Schroeder source, Lemma 8.2 (`lem:mertens`), and its
Rosser--Schoenfeld premise. The rational certificate here does not
prove this analytic estimate or improve its source-verification
status.

Starting from any head submeasure supported on avoidance of all
original head-only classes, of mass at least \(m\) and at most
one, and joint density at most \(D\), (SH8)--(SH11) bound the
total tail loss, with \((q-1)^{-2}\le(q-3)^{-2}\), by

\[
 D M_2(R)\,\tau_7(B,\ell),\qquad
 \tau_7(B,\ell)=
 {c_\ell^7\over B}\left({B\over B-3}\right)^2
 \sum_{h=0}^7{7!\over(7-h)!\ell^h}.
 \tag{SH12}
\]

This is Chapter 32's all-prime summation applied to the joint-load
seed. To recall its scope, enlarge the actual preceding-tail prime
product to every prime in \((B,q]\), and enlarge the tail charge
sum to every integer greater than \(B\). Since \(\log B>\ell\ge4\),
\((\log z)^7/z^2\) decreases on this interval, and its integral is

\[
 \int_B^\infty{(\log z/\log B)^7\over z^2}\,dz
 ={1\over B}\sum_{h=0}^7{7!\over(7-h)!(\log B)^h}.
\]

Replacing \(\log B\) by \(\ell\) in this positive sum proves
(SH12). Missing tail primes cause no problem. Head primes need not
be numerically below the tail: the artificial exposure order is
head first and tail increasing, and including additional primes in
the comparison product only enlarges it. For the headline theorem
the head is, in fact, chosen below \(B\).

We obtain the reusable sufficient condition

\[
 m>D M_2(R)\tau_7(B,\ell)
 \quad\Longrightarrow\quad\text{a complete original survivor}.
 \tag{SH13}
\]

If additional head-coordinate sets are to be removed, their actual
costs under the preserved head marginal must also be subtracted in
(SH13). No such extra obligations are used in the headline
application: all original primes are processed directly.

There is also a direct fixed-domain variant of the same existing
transfer. If a current base is \(H_q(\cdot\mid V_q)\), where
\(V_q\) avoids the pure classes and
\(H_q(V_q)\ge d_q/(q-1)\) with \(d_q\ge q-3\), the
kernel has Haar cap \(2(q-1)/d_q\), and the current charge is at
most \(\mathcal G_Q(\nu)/d_q^2\). Equation (SH10) and the
same \(\tau_7\) still apply. The tail marginal cap becomes
\(2(q-1)/d_q\); old marginals are still preserved. This variant
requires a proof of each actual domain bound. It is not used to
supply missing graph-block fees in the present theorem.

## 5. The numerical application

The function \((3p-1)/(p-1)^2\) decreases for \(p>1\). Therefore
any seven ordered odd primes have

\[
 M_2(R)\le M_2(P_*)={2263261\over110592},\qquad
 D_*M_2(R)\le{2263261\over8192}.
 \tag{SH14}
\]

Set \(B=100000\), \(\ell=10\); the analytic applicability
conditions hold, including \(3^{10}=59049\le100000\). Exact
rational arithmetic yields

\[
 {2263261\over8192}\tau_7(100000,10)
 ={482499472365859733223806367\over66602699562724767891160975360}
 <{29\over4000}.
 \tag{SH15}
\]

Combining (SH1) with (SH15), the remaining weighted survivor mass
is strictly greater than

\[
 {2\over125}-{29\over4000}={7\over800}>0.
 \tag{SH16}
\]

Choose as head every original prime at most 100000 and pad to seven
when necessary, as in Section 2. All other original primes are an
arbitrary finite subset of \((100000,\infty)\). Every class wholly
in the head was already avoided. Every other class was assigned
exactly once during continuation. Thus positive surviving measure
provides an avoiding tuple in the full finite CRT carrier and hence
an integer outside the original covering family.

The number in (SH16) is mass in the constructed distorted measure;
it is not a lower bound of that size for the original Haar density.
On the original period \(N\), existence alone gives Haar density
at least \(1/N\).

## 6. The attributed eight-prime density as another seed

Schroeder's *Nine Prime Divisors in Odd Distinct Covering Systems*,
edition 1.0.1, corollary `cor:uncovered-density`, states that any
family with at most eight odd prime divisors across its distinct
nonunit moduli leaves uncovered natural density at least
\(1/1002375\). Its complete prime powers and residues are unrestricted.
The [existing source entry](../../../../Library/Arith/schroeder2026nine.md)
records the inspected corollary, archive identity, local fresh
finite-geometry verification, and the boundary that the whole
arbitrary-height theorem has not been locally kernel-replayed.
The application below uses this attributed ordinary source theorem;
it does not turn that local verification into a complete Lean proof.

For any head of at most eight primes, apply that theorem to the
actual head-only subfamily and take
\(\mu_H=H|_U\), where \(U\) is its full survivor set. At heights
resolving the entire original family this has

\[
 \mu_H(X)\ge m_8={1\over1002375},\qquad \mu_H\le H.
 \tag{SH17}
\]

Indeed, the full head period is a multiple of the period of its
head-only subfamily; uniform lifting preserves its survivor density.
This applies even when a head prime occurs only in classes touching
the tail. Unused coordinates can also be padded to reach eight,
without changing classes or density. No randomized transport of
this particular seed is required.

The first eight odd primes majorize the Haar moment for every such
head, so

\[
 M_2(R)\le {4732273\over202752}.
 \tag{SH18}
\]

Take \(B_8=100000000\) and \(\ell_8=16\). The same transfer
gives tail loss at most

\[
 {4732273\over202752}\tau_7(100000000,16)
 = {1097047779531311514783771237357421875
    \over2741275994402057415260186461015293546201088}.
 \tag{SH19}
\]

Subtracting this from \(m_8\) gives exactly

\[
 {149238429672214457784436706088104344931633
  \over249798774989887481965584491260018624397574144000}
 >{1\over2000000}>0.
 \tag{SH20}
\]

Thus any family with at most eight prime divisors at most 100000000
and arbitrarily many larger prime divisors is noncovering. This
application has the additional attributed source premise just
specified. Its numerical cutoff and rational margin are checked
by the same standalone program.

## 7. Relation to existing results and verification

The arbitrary correlated-head transfer is already present in
Chapter 08; (SH8)--(SH9) are its homogeneous application with
threshold one half, including pure tail classes. Chapter 09 lifts old-prime heights and
does not supply the seven-coordinate positive seed. Chapter 31
supplies that seed and its exact mass calculation; (SH2)--(SH4)
expose and transport the joint density needed here. Chapter 32
supplies the analytic all-prime summation. The new application is
their explicit combination at the cutoff 100000, and the analogous
application of the existing eight-prime density at cutoff 100000000.

Within the inspected existing report, Chapter 03's arbitrary-height
\(3,5,7\) continuation omits 11, 13 and 17; its 315/945 rows have
restricted old heights. Chapter 27 requires a bounded reciprocal
tail sum. Chapter 31 bounds the size of every graph block. Chapter
32 allows specified six-coordinate heads. None of those stated
conclusions contains the present class with, for example, the first
seven odd primes and every prime in an arbitrarily long finite
interval above 100000, all in one block. Conversely, the current
cutoff restriction does not contain all their other classes. This
comparison is confined to the inspected statements, not a claim of
exhaustive literature novelty.

The standalone
[arithmetic program](../frontier/cover-geometry/seven_head_dense_tail_certificate.py)
reads the inherited Chapter 31 certificate, selects its exact
seven-prime row, checks the kernel-cap product, computes the Haar
second moment and rational tail allowance, and records the input
SHA-256 in its
[output](../frontier/cover-geometry/seven_head_dense_tail_certificate.json).
It also checks the second seed's moment and continuation arithmetic;
that seed's density theorem remains an attributed premise. The
program does not execute the inherited geometry or certify the
external analytic premise. Run from the repository root after the two
certificates are installed side by side:

```sh
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/seven_head_dense_tail_certificate.py --output /tmp/seven-head-dense-tail-certificate.json
```

The unrestricted problem still permits configurations satisfying
neither stated head-count/cutoff condition. The argument supplies
no uniform positive head reserve for all such configurations.
