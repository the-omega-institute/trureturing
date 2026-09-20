[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# Full density and large-prime continuation for common-spine books

**Full-density theorem.** Let a finite family have pairwise distinct odd
moduli greater than one. Suppose its primes other than 3 and 5 have a
partition into \(N\) nonempty private pages, each containing at most two
primes, such that every modulus is supported on the spine \(\{3,5\}\)
and at most one page. The full original Haar survivor proportion satisfies
\[
 H(U)>\varepsilon_N:=\frac{67}{4000}\left(\frac3{16}\right)^N>0.
 \tag{BD1}
\]
There is no restriction on original finite heights, residues, page count,
or the number of classes. For two-prime pages \(q_i<r_i\), the stronger
bound is
\[
 H(U)>\frac{67}{4000}
 \prod_i\frac{(q_i-2)(r_i-2)}{4(q_i-1)(r_i-1)}.
 \tag{BD2}
\]
For singleton pages the same expression holds after the free-coordinate
padding described below. In (BD1), \(N\) counts original nonempty pages;
a spine-only family has \(N=0\).

**Large-prime continuation.** Fix the head prime set \(P\) and a permitted
page partition. A computable cutoff \(B_0(P,N)\ge\max(\{286\}\cup P)\)
allows arbitrary further primes greater than \(B_0\), without coverage.
Only head-only classes must satisfy the book condition. Tail-touching
classes may join arbitrarily many head pages and tail primes.

The full-density proof uses the ordinary normalized kernels and labelled
conditional convex comparison of
[Schroeder's three-prime paper](../../../../Library/Arith/schroeder2026noncoverage.md),
version 1.0, revised 15 September 2026, Sections 2--3. The comparison
proposition itself has no three-prime-support hypothesis. The new
book-specific charge allocation gives a full-volume strengthening of
[Chapter 36](36-common-spine-books-of-four-prime-pages.md), without using
its anchor geometry. The continuation reuses
[Chapter 33](33-seven-small-primes-with-an-unrestricted-large-prime-tail.md).
These are ordinary deductions with exact rational calculations; no new
Lean verification, literature-priority claim, or solution of unrestricted
Erdős #7 is asserted.

## 1. One common spine law

Use the full prime-power CRT coordinates resolving every original height.
Write \(H_p\) for uniform probability on the \(p\)-coordinate. Let \(V_p\)
avoid all original pure classes \(p^e\), and put
\[
 H_p(V_p)\ge1-\sum_{e\ge1}p^{-e}=\frac{p-2}{p-1},\qquad
 \nu_p=H_p(\cdot\mid V_p),\quad c_p=\frac{p-1}{p-2}.
 \tag{BD3}
\]
Numerical distinctness permits at most one pure class per exponent. Thus
\(\nu_p\le c_pH_p\), and each original prefix of depth \(e\) has
\(\nu_p\)-probability at most \(c_pp^{-e}\).

Fix \(\nu=\nu_3\otimes\nu_5\). If \(B_S\) is the union of mixed
spine-only classes, each full label \(3^a5^b\), \(a,b\ge1\), occurs
at most once, so
\[
 \nu(B_S)\le\sum_{a,b\ge1}2\,3^{-a}\frac43\,5^{-b}=\frac13.
 \tag{BD4}
\]
We do not condition \(\nu\) on avoiding \(B_S\). All pages share this
same product law, and the mixed-spine fee is paid once. In particular the
original spine Haar reserve is at least
\((1/2)(3/4)(2/3)=1/4\). A normalized safe-head interface requiring
probability-one root survival is not applied to \(\nu\).

## 2. Actual normalized kernels, including zero-survival fibres

For each private pair \(q<r\), assign every nonpure page class containing
\(r\) to the \(r\)-stage; assign every other nonpure page class to the
\(q\)-stage. Spine-only classes were already assigned at the root.

At stage \(p\), let \(B_p(x)\) be the actual forbidden coordinate union
at the complete earlier word \(x\), and set
\(\alpha_p(x)=\nu_p(B_p(x))\). Use the density relative to \(\nu_p\)
\[
 k_p(x,y)=
 \begin{cases}
 (1-\min\{\alpha_p(x),1/2\})^{-1},&y\notin B_p(x),\\
 2(\alpha_p(x)-1/2)_+/\alpha_p(x),&y\in B_p(x).
 \end{cases}
 \tag{BD5}
\]
The second expression is zero when \(\alpha_p=0\). Direct integration
at every history proves normalization, \(0\le k_p\le2\), and
\[
 K_p(x,B_p(x))=2(\alpha_p(x)-1/2)_+.
 \tag{BD6}
\]
At \(\alpha_p=1\), \(K_p=\nu_p\): the completely forbidden fibre
is retained and charged one. No history is removed to make the kernel
well-defined.

Construct the single full law
\[
 \mathbb P(ds,dy)=\nu(ds)\prod_i
              K_{q_i}(s,dy_{q_i})K_{r_i}(s,y_{q_i},dy_{r_i}).
 \tag{BD7}
\]
Every factor is normalized. Later pages preserve earlier joint marginals,
and the spine marginal is exactly \(\nu\).

Define the page fee at a full spine word by
\[
 e_i(s)=2(\alpha_q(s)-1/2)_+
       +2\int(\alpha_r(s,y_q)-1/2)_+K_q(s,dy_q).
 \tag{BD8}
\]
Let \(W_i(s)\) be its original private Haar probability of avoiding all
page-owned classes, including its pure classes. Under the page kernel,
the union bound gives avoidance probability at least \((1-e_i(s))_+\).
Its density relative to \(H_q\otimes H_r\) is at most \(4c_qc_r\),
hence
\[
 W_i(s)\ge\frac{(1-e_i(s))_+}{4c_qc_r},\qquad
 \mathbf1_{\{W_i(s)=0\}}\le e_i(s).
 \tag{BD9}
\]
This retains the same joint spine word throughout; it neither multiplies
marginal probability caps nor chooses different good words for different
pages.

## 3. Compare original labelled loads before completing exponents

The source Proposition 3.2 compares nonnegative rectangle loads under
full-history conditional caps. Specifically, if
\(\Pr(X_j\in A_{\ell,j}\mid X_1,\ldots,X_{j-1})\le b_{\ell,j}\)
with deterministic caps, then, for nonnegative weights and increasing
convex \(h\),
\[
 \mathbb E h\!\left(\sum_\ell w_\ell\prod_j
                      \mathbf1_{A_{\ell,j}}(X_j)\right)
 \le\mathbb E h\!\left(\sum_\ell w_\ell\prod_j
                      \mathbf1_{\{U_j\le b_{\ell,j}\}}\right),
 \tag{BD10}
\]
where the \(U_j\) are independent uniforms. Each coordinate uses the
same uniform for every original label. The elementary proof replaces
the last coordinate by nested indicators: convexity makes the set
function of active labels supermodular, and its increasing increments
are bounded using the conditional caps. Backward induction completes
the replacement. Actual labels need not have compatible residues.

Use independent integer variables \(N_p=1+K_p^{\rm aux}\), with
\[
 \Pr(K_3^{\rm aux}\ge e)=2\,3^{-e},\quad
 \Pr(K_5^{\rm aux}\ge e)=\frac43\,5^{-e},\quad
 \Pr(K_*^{\rm aux}\ge e)=\frac{12}{5}\,7^{-e}\quad(e\ge1).
\]
The star denotes an auxiliary law, not an additional actual prime.
For every actual \(q\ge7\), (BD5) gives full-history prefix caps
\(2c_qq^{-e}\le(12/5)7^{-e}\); this follows since both \(c_q\)
and \(q^{-e}\) decrease with \(q\).

Put \(Y_0=N_3N_5-1\) and \(Y=N_3N_5N_*-1\), and define
\[
 F_0(p)=\frac2{p-2}\mathbb E(Y_0-(p-2)/2)_+,\qquad
 F(p)=\frac2{p-2}\mathbb E(Y-(p-2)/2)_+.
 \tag{BD11}
\]
At the first stage the original labels are \(3^a5^bq^e\), with
\(e\ge1\) and \(a+b>0\). First bound the actual forbidden union by
the sum of \(c_qq^{-e}\) times each label's actual spine indicator;
then apply (BD10) to this finite labelled sum with
\(h(u)=2(u-1/2)_+\). Only afterwards complete exponent tuples.
There is at most one original class per full tuple, and
\(\sum_{e\ge1}c_qq^{-e}=1/(q-2)\), giving comparison load
\(Y_0/(q-2)\). The resulting stage fee is at most \(F_0(q)\).

At the second stage the original labels are \(3^a5^bq^cr^e\), with
\(e\ge1\) and \(a+b+c>0\). The actual predecessor law is
\(\nu_3\nu_5K_q\). It satisfies exactly the conditional caps in
(BD10). The same labelled comparison followed by completion gives load
\((N_3N_5(1+K_q^{\rm aux})-1)/(r-2)\), dominated by
\(Y/(r-2)\). Thus
\[
 \int e_i\,d\nu\le F_0(q_i)+F(r_i),\qquad
 \sum_i\int e_i\,d\nu\le F_0(7)+\sum_{p\ge11\ {\rm prime}}F(p).
 \tag{BD12}
\]
For the last inequality, \(Y\ge Y_0\), actual private primes belong
to exactly one page, and 7 can only occur as a first stage. Adding absent
primes only enlarges this nonnegative bound. Full geometric sums cover
all heights; monotone convergence justifies the comparison completion.
No uniqueness of products of different modulus labels is assumed.

## 4. Six exact fees and an analytic remainder

The masses of \(N_3,N_5,N_*\) at 1 are respectively
\(1/3,11/15,23/35\). At \(n\ge2\) they are
\[
 u_n=4/3^n,\qquad v_n=16/(3\cdot5^n),\qquad
 w_n=72/(5\cdot7^n).
\]
Their product has mean \(56/15\). Using
\(\mathbb E(Z-a)_+=\mathbb EZ-a+\mathbb E(a-Z)_+\) gives the finite
exact formula
\[
 F(p)=\frac2{p-2}\left[\frac{56}{15}-\frac p2+
     \sum_{abc\le(p-1)/2}(p/2-abc)u_av_bw_c\right].
\]
For \(F_0\), omit the third factor and use mean \(8/3\). This yields
\(F_0(7)=8804/50625\) and
\(F(11)=253372547128/1722980109375\), with strict bounds:

| Charge | Strict upper bound |
|---|---:|
| \(F_0(7)\) | \(174/1000\) |
| \(F(11)\) | \(148/1000\) |
| \(F(13)\) | \(92/1000\) |
| \(F(17)\) | \(42/1000\) |
| \(F(19)\) | \(30/1000\) |
| \(F(23)\) | \(16/1000\) |

Their sum is less than \(251/500\). The first three full moments are

| Variable | \(\mathbb EN\) | \(\mathbb EN^2\) | \(\mathbb EN^3\) |
|---|---:|---:|---:|
| \(N_3\) | \(2\) | \(5\) | \(31/2\) |
| \(N_5\) | \(4/3\) | \(13/6\) | \(107/24\) |
| \(N_*\) | \(7/5\) | \(7/3\) | \(14/3\) |

Consequently \(\mathbb EY^3=92467/360\). For \(u\ge0,t>0\),
\((u-t)_+\le4u^3/(27t^2)\): for \(u\ge t\) this is the
nonnegative identity \((2u-3t)^2(u+3t)=4u^3-27t^2(u-t)\), and
for \(u<t\) it is immediate. Hence
\[
 \sum_{p\ge29\ {\rm prime}}F(p)
 \le\frac{32}{27}\frac{92467}{360}
          \sum_{j\ge0}(27+2j)^{-3}
 \le\frac{32}{27}\frac{92467}{360}
       \left(\frac1{27^3}+\frac1{4\cdot27^2}\right)
 =\frac{2866477}{23914845}<\frac3{25}.
\]
The second bound is the first term plus the integral of
\((27+2x)^{-3}\) over \([0,\infty)\). Thus
\[
 \sum_i\int e_i\,d\nu<\frac{251}{500}+\frac3{25}
 =\frac{311}{500}.
 \tag{BD13}
\]
The split at 29 is a calculation, not a restriction on permitted primes.

## 5. Full Haar density and removal of free coordinates

Under (BD7), all pure classes have probability zero. The mixed-spine
union costs at most \(1/3\), and every remaining class belongs to one
page stage. Therefore
\[
 \mathbb P(U)>1-\frac13-\frac{311}{500}=\frac{67}{1500}.
\]
The pointwise conditional kernel densities give the full joint bound
\[
 \frac{d\mathbb P}{dH}\le\frac83\prod_i4c_{q_i}c_{r_i}.
\]
Combining these two inequalities proves (BD2). Because \(q_i\ge7\)
and \(r_i\ge11\),
\[
 \frac1{4c_{q_i}c_{r_i}}\ge
 \frac{(7-2)(11-2)}{4(7-1)(11-1)}=\frac3{16},
 \tag{BD14}
\]
which proves (BD1). This uses full joint density domination, not a
product of separately obtained marginal caps. The finite CRT then
supplies an uncovered integer.

For a singleton page add a distinct unused dummy prime larger than all
original primes, with a free coordinate and exponent zero in every
original modulus. Its avoiding set is independent of this coordinate,
so projection preserves original Haar volume exactly. The number of
pages does not change, and (BD14) applies to every padded pair. Missing
spine coordinates may likewise be adjoined freely and removed. Finite
coordinate heights always resolve all original classes, including those
assigned to later stages; no exponent layer is discarded.

## 6. Some surviving spine words have no page extension

The integrated bound must not be replaced by universal pointwise
extension. Take root classes \(1\bmod3\) and \(1\bmod5\), with
page classes
\[
 (m,a)=(7,0),(21,15),(63,9),(189,108),
        (35,25),(105,75),(315,90).
\]
On the spine cylinder \(x_3=0\bmod27,\ x_5=0\bmod5\), these
forbid respectively every residue \(0,1,\ldots,6\bmod7\), although
the root classes are avoided. After deleting the pure class \(0\bmod7\),
all remaining private words are forbidden: \(\alpha_7=1\),
\(K_7=\nu_7\), and its fee is one. This is precisely the zero-fibre
case retained in (BD5).

Adding \(2\bmod1155\), where \(1155=3\cdot5\cdot7\cdot11\),
makes the actual prime interaction graph a full four-vertex clique.
It is nonredundant because the integer 2 avoids all preceding classes.
The moduli are distinct. This refutes universal extension at every
spine word, not the noncoverage theorem.

## 7. Fixed-head continuation to unrestricted large primes


Fix the actual head prime set \(P\) and a partition of its private
primes into \(N\) pages. Only classes supported entirely on \(P\)
are required to obey the book condition. Missing events or unused
head coordinates are allowed; adjoining such free coordinates does
not change the survivor proportion. Equivalently, if fewer actual
pages occur, their stronger bound implies (BD1) for this larger \(N\).

At head heights resolving the entire larger family, let \(U_H\)
avoid all original head-only classes, and take
\[
 \mu_H=H_P|_{U_H}.
\]
Uniform lifting to these heights preserves density, so
\[
 \mu_H(X)>\varepsilon_N,\qquad \mu_H\le H_P.
 \tag{BD15}
\]
The dummy coordinates have already been removed. They do not enter
\(P\), the head moment, or the cutoff.

Use Chapter 33's existing homogeneous joint-load continuation with
joint density cap \(D=1\) and
\[
 M_2(P)=\prod_{p\in P}\left(1+\frac{3p-1}{(p-1)^2}\right).
\]
For integers \(\ell\ge6\) put \(B=3^\ell\),
\(c_\ell=(2\ell^2+1)/(2\ell^2-1)\), and
\[
 \tau_7(B,\ell)=
 \frac{c_\ell^7}{B}\left(\frac B{B-3}\right)^2
 \sum_{h=0}^7\frac{7!}{(7-h)!\ell^h}.
 \tag{BD16}
\]
Increase \(\ell\) until
\[
 B\ge\max(\{286\}\cup P),\qquad
 M_2(P)\tau_7(B,\ell)<\frac{\varepsilon_N}{2}.
 \tag{BD17}
\]
This is an effective exact-rational search. It terminates because
\(3^{-\ell}\) tends to zero and all the other factors in (BD16)
remain bounded. Let its first successful \(B\) be \(B_0(P,N)\).
The original analytic requirements, including \(B\ge286\),
\(\ell\ge4\), and \(3^\ell\le B\), are then satisfied.

If every original prime outside \(P\) is greater than \(B_0\),
Chapter 33 bounds the total weighted tail deletion by less than
\(\varepsilon_N/2\). It processes every tail-touching original
class, including pure tail classes, using one sequence of normalized
full-coordinate kernels. Its finite positive measure retains a
complete avoiding tuple. No restriction is imposed on how many head
pages a tail class joins or how many further primes it contains.

The final weighted reserve is not identified with the same numerical
lower bound for final Haar density. The head \(P\) and partition are
fixed before selecting the cutoff. This is a sufficient gap condition
for continuation, not a statement that an arbitrary family already
has no primes in the gap. The argument inherits Chapter 33's stated
analytic prime-product premise and verification boundary.

## 8. Verification and scope

The self-contained program
[`spine_book_density_certificate.py`](../frontier/cover-geometry/spine_book_density_certificate.py)
checks the six exact complementary-tail sums, complete geometric moments,
cubic remainder constant, density factors and the actual zero-fibre
counterexample. Its
[`output`](../frontier/cover-geometry/spine_book_density_certificate.json)
records the rational values. It does not claim machine verification of
(BD10), the arbitrary-height reduction, or the full-density proof.

The source comparison and normalized kernel interfaces are already
recorded in the linked library entry, with their hypotheses and source
identity. The three-prime noncoverage endpoint is not used: these pages
can contain four-prime moduli, and the union of pages can have arbitrarily
many primes in one biconnected block. For example, the four private pairs
\((7,11),(13,17),(19,23),(29,31)\), each with a full four-prime class,
give a ten-vertex block sharing the spine.

The fixed three-factor auxiliary product works because the second private
stage has only one private predecessor. Arbitrary overlapping supports
need not admit this page partition. For them (BD12)'s fee bound has not
been established. The independent large-prime continuation still requires
its declared gap and inherits Chapter 33's analytic premise. Unrestricted
Erdős #7 remains open.
