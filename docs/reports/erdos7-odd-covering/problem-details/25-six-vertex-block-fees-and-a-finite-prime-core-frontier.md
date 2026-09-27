[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

<a id="six-vertex-block-fees-and-a-finite-prime-core-frontier"></a>
# Six-vertex block fees leave fifty specified root-3 child sets

Under the actual child-domain density invariant (CK4) of Chapter 23,
the unchanged fee schedule pays every six-vertex block with a legal
non-3 parent. At parent 3, it pays every five-child prime tuple except
the fifty explicit child-prime sets listed below. All original finite prime-power
heights, residues, and supports remain allowed. The fifty child-prime sets are
unresolved by these estimates; they are not covering constructions or
counterexamples to the fee claim.

This is an ordinary mathematical consequence of the conditional-kernel
estimate (CK12) and large-child theorem of
[Chapter 23](23-conditional-kernels-and-recursive-block-noncoverage.md),
the coupled first-root inequality (KR14) of
[Chapter 21](21-coupled-first-root-profiles-and-an-exceptional-five-prime-block.md),
and the exact finite certificate below. It is
not a Lean-certified result or a claim of unrestricted noncoverage.

## 1. Local hypotheses and the complete boundary

Use the existing fees
\[
 f(5)=7/24,\quad f(7)=1/8,\quad f(11)=1/24,\quad f(13)=1/48,
 \quad f(q)=2^{-(q-1)/2}\ (q\ge17),\quad F=187/384,
\]
with \(c_5=3/10\) and \(c_p=2/(p-1)\) for \(p\ge7\).
The local input is the actual density bound
\[
 H_q(V_q)\ge1-\frac1{q-1}-c_qe_q,
 \qquad e_q=\sum_{r\in D_q}f(r),
\]
where the strict descendant sets are disjoint and avoid the current
block. Components containing 3 are rooted at 3; all children are at
least 5, and the parent is distinct from its children.

For five children take the small-prime set
\[
 P_0=\{5,7,11,13,17,19,23,29,31,37,41\}.
\]
For every nonempty subset of \(j\le5\) small children, charge only
their fee sum \(C\), set \(E=F-C\), and replace the remaining sorted
children by the lower odd proxies \(43,45,47,49\), as needed. The
coordinate caps are
\[
 b_5(E)=\frac1{3-(6/5)E},\qquad b_q(E)=\frac1{q-2-2E}\ (q\ge7).
\]
There are \(\sum_{j=1}^5\binom{11}{j}=1023\) such rows. Direct
dominating-cap application of (CK12) pays 972 of them, with selected
cutoffs \(1\le t\le11\). When all five children are at least 43,
the analytic theorem applies because \(5(5+3)+3=43\).

The coefficient calculation for five children is
\[
 Z_J(w+tb)=\sum_{n=0}^5c_n(t)e_n(b),
\]
where \(e_n\) is elementary symmetric and
\[
\begin{aligned}
c_0&=1,&c_1&=-t,\\
c_2&=t^2-t-1,&c_3&=-t^3+3t^2+2t-1,\\
c_4&=t^4-6t^3+t^2+9t+2,\\
c_5&=-t^5+10t^4-15t^3-25t^2+9t+9.
\end{aligned}
\]
Selecting the block containing one designated element in a set partition
gives
\[
 c_n=-t c_{n-1}-(t+1)
       \sum_{r=2}^n\binom{n-1}{r-1}c_{n-r}.
\]
Differentiation gives \(L_t=-\partial_t Z_J(w+tb)\). The independent
certificate checks the coefficient identities against all 203 disjoint
support families, and reconstructs the 1023-row result with an independent
subset recurrence.

## 2. Every remaining non-3 orientation is paid

The 51 rows not paid at parent 3 consist of 44 fixed tuples and seven
one-large-child proxy rows. They all contain 5 and 7. At \(t=1\), all
their induced support residuals are strictly positive. For each row let
\(p_{\min}\) be the smallest prime at least 5 not among its fixed
children. For proxy rows, the actual fifth child is at least 43, so this
choice is legal: all these \(p_{\min}\) are in \(\{11,13,17,19\}\).

For any permitted non-3 parent \(p\ge p_{\min}\),
\[
 \frac{K_{p,1}}{c_p}=\frac3p K_{3,1}
 \le\frac3{p_{\min}}K_{3,1}<C.
\]
Every one of the 51 rows passes. Their worst ratio and smallest absolute
margin occur at
\[
 J=(5,7,13,17,19),\quad p_{\min}=11,\quad C=227/512,
\]
where
\[
 K_{3,1}=\frac{3937775843686559872}{6209563897833781095},
\]
\[
 \frac{(3/11)K_{3,1}}{C}
 =\frac{2016141231967518654464}{5168427017630317131405}
 <\frac25,
\]
\[
 C-\frac3{11}K_{3,1}
 =\frac{3152285785662798476941}{11657421290866618375680}
 >\frac14.
\]
The self-contained certificate records a non-3 comparison for every
boundary row, and retains the displayed worst exceptional comparison
in `worst_non3_initial_kernel_exception`.
The 972 previously paid rows use the usual (CK19) parent comparison,
including its stronger \(p=5\) factor. Thus no non-3 orientation remains
unresolved.

## 3. Exact first-root reduction

For each of the 51 remaining parent-3 rows set the target \(M=C\).
Every such target lies
strictly between \(1/3\) and \(2/3\). With
\(Z_0=Z_J(w)\) and
\(L_0=\sum_{S\ne\varnothing}b_SZ_{J\setminus S}(w)\), (KR14)
implies that a blocker of mass at least \(C\) would satisfy
\[
 \min_{0\le y_S\le b_S}
 \left[\frac13Z_J(w+y)
       +\left(C-\frac13\right)Z_J(w+b-y)\right]
 \le L_0/6.
\]
The whole box is strict. For every support \(S\), the objective's
partial derivative is at most the negative of
\[
 m_S=\frac13 Z_{J\setminus S}(w+b)
       -\left(C-\frac13\right)Z_{J\setminus S}(w).
\]
Whenever \(m_S>0\), a minimum assigns \(y_S=b_S\). The remaining
variables are separately affine, so their corners give the exact full
box minimum. For the 51 rows this forces 22 to 30 of the 31 supports,
leaving only 1 to 9 variables. The 5286 retained corner evaluations give
13 positive gaps: ten fixed tuples and three complete proxy families.
There are no zero gaps. The other 38 negative minima establish only
failure of this estimate.

The certificate records the exact minima, derivative margins, free
supports, corner counts, and minimizing allocations in each relevant
row's `KR` record. The three newly paid
proxy families have fixed small children
\((5,7,11,19)\), \((5,7,11,23)\), or \((5,7,13,23)\), and an
arbitrary fifth prime at least 43.

## 4. Four fixed-budget tails close the infinite remainder

For each remaining small four-tuple, fix
\(C_0=\sum_{q\in\mathrm{small4}}f(q)\) and \(E_0=F-C_0\).
The following sufficient odd proxies give strictly positive KR gaps at
target \(M=C_0\):

| Fixed four children | Tail proxy \(Q\) | Exact positive gap above \(L_0/6\) |
| --- | ---: | ---: |
| \(5,7,11,13\) | 75 | \(6174544633531/27667944459500400\) |
| \(5,7,11,17\) | 51 | \(79730632652803991/1029392676511196428032\) |
| \(5,7,13,17\) | 67 | \(10163479674040761/108746099441002400000\) |
| \(5,7,13,19\) | 51 | \(11971923218346148663/29671198905817434304000\) |

For every actual fifth prime \(q\ge Q\), each actual coordinate cap
is at most this fixed proxy cap: the actual outside expense is bounded
by \(E_0-f(q)\le E_0\), and the fifth prime is at least \(Q\).
Use these dominating caps directly in the same KR14 inequality. This
pays the smaller charge \(C_0\), and therefore the full child fee sum
\(C_0+f(q)\). No monotonicity of an optimized KR expression is assumed.
These are sufficient endpoints, not claims of smallest thresholds.

The actual fifth primes in the four finite intervals \(43\le q<Q\)
are respectively

- \(43,47,53,59,61,67,71,73\);
- \(43,47\);
- \(43,47,53,59,61\);
- \(43,47\).

All 17 corresponding actual tuples remain negative under the KR test
even using their full five-child fee and its smaller outside expense.
Their direct kernel controls also fail to pay: \(t=0,1\) are strict,
and \(t=2\) is the first nonstrict cutoff. Thus none is silently
discarded as already paid by the kernel bound.

The certificate retains these four endpoint certificates in `tails` and
all seventeen actual intermediate-prime records in `finite_tail_rows`.
Each includes its density caps and exact KR gap; the finite records also
include their kernel residuals at cutoffs zero, one, and two.

## 5. Removing one composite term pays the tail from 73

The fee majorant used so far can be sharpened without changing any fee
or invalidating a previous certificate. Its odd-integer tail includes
21, which is composite. Removing that term gives
\[
 \sum_{q\ge5\text{ prime}}f(q)
 \le \frac{23}{48}+\sum_{n=8}^{\infty}2^{-n}-2^{-10}
 =\frac{1493}{3072}=:F_*.
\]
For fixed children \(5,7,11,13\), retain the charge
\(C_0=23/48\), giving \(E_*=F_*-C_0=7/1024\). At the new
fifth-coordinate proxy 73 the same KR test has exact positive gap
\[
 \frac{4357883692674437}{35313726266855802000}>0.
\]
All residuals are strictly positive. Twenty-two support variables are
forced, leaving masks \(2,4,8,12,16,18,20,24,28\); all 512 corners
are checked. The same fixed dominating-cap argument pays every actual
fifth prime at least 73. Consequently \((5,7,11,13,73)\) is removed
from the remaining list. The other certificates continue to use their
valid, looser budget \(F\); they need not be recomputed at \(F_*\).

## 6. Complete remaining root-3 list and recursive scope

Each row below means the fixed four children followed by one of the
listed fifth primes. The rows contain exactly fifty distinct five-child
prime sets; all have parent 3. Each still permits arbitrary finite
original prime-power heights and residues, so this is not a list of fifty
finite AP systems.

| Fixed four children | Remaining fifth primes | Count |
| --- | --- | ---: |
| \(5,7,11,13\) | 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71 | 14 |
| \(5,7,11,17\) | 19, 23, 29, 31, 37, 41, 43, 47 | 8 |
| \(5,7,11,19\) | 23, 29, 31, 37 | 4 |
| \(5,7,11,23\) | 29 | 1 |
| \(5,7,13,17\) | 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61 | 11 |
| \(5,7,13,19\) | 23, 29, 31, 37, 41, 43, 47 | 7 |
| \(5,7,13,23\) | 29, 31 | 2 |
| \(5,7,17,19\) | 23, 29, 31 | 3 |

The accounting is 34 unresolved fixed rows plus 17 intermediate-prime
rows, minus the row paid by the refined tail from 73: \(34+17-1=50\).
No unresolved proxy family remains. The original 51 kernel-exception rows
included seven infinite families and are a different index set. Nor is
it claimed that every remaining row has been reoptimized with the
smaller global budget \(F_*\); the table records what the present
certificates leave unresolved.

The local conclusions use the same child-domain invariant and immediate
child-fee charges as Chapter 23. Its bottom-up induction therefore also
permits arbitrary six-vertex blocks except the fifty vertex sets obtained
by adjoining 3 to the listed tuples. All previously allowed blocks and
the existing large-child regime remain compatible with that induction.
Using \(F_*\), the root-coordinate reserve is at least
\[
 H_3(V_3)\ge\frac12-F_*=\frac{43}{3072}>0.
\]
The full original-Haar conclusion is
\(U_{\rm full}\ge43/(3072Q_{\rm off})\), with the same original
all-component denominator as in Chapter 23. If 3 is absent, the actual
witness construction gives at least one uncovered original residue.

Every listed child set contains 5 and 7, so each unresolved graph block
contains \(\{3,5,7\}\). Two distinct graph blocks share at most one
vertex. There can therefore be at most one such unresolved block in the
entire graph. A useful sufficient condition follows: if every block has
at most six vertices and no block contains 3, 5, and 7 together, the
family is noncovering. A component without prime 3 allows arbitrary
blocks on at most six vertices. The fifty-set exclusion above is the
more precise condition and does not exclude every six-vertex block
containing all three primes.

These observations reduce the unresolved six-vertex part to at most one
specified prime core with its actual descendant domains. They do not
bound its original exponent heights or enumerate its possible AP
families.

This extension still excludes the listed blocks and makes no uniform
claim for dense blocks of larger size with small children. The negative
finite certificate gaps are not evidence that those blocks can cover,
and these results do not settle unrestricted Erdős #7.


## 7. Self-contained exact certificate

The standard-library program
[six_vertex_conditional_kernel_certificate.py](../frontier/cover-geometry/six_vertex_conditional_kernel_certificate.py)
and its [exact data](../frontier/cover-geometry/six_vertex_conditional_kernel_certificate.json)
form one self-contained finite certificate. The program reads no other
result files. It reconstructs the 1023-row partition, the 972 kernel
certificates, the 13 additional KR certificates, the four fixed-budget
tails, all seventeen intermediate-prime rows, and the refined-budget
endpoint at 73. It also checks every boundary row's non-3 comparison and
the seventeen actual intermediate rows' non-3 comparisons.

The coefficient identities are checked symbolically against set
partitions. Every retained kernel certificate's induced polynomials
are checked by the elementary-symmetric formula, deletion recurrence,
and direct disjoint-support-family summation. The KR cases use explicit
strict derivative margins and exhaustive corners of the remaining
separately affine variables; their minimizing values are also checked
by deletion recurrence. These are finite exact checks. The conditional
probability theorem, the uniform domination argument, the unbounded
large-child proof, and the recursive assembly remain the ordinary
mathematical arguments described above.

The program requires Python 3.10 or later and rejects optimized `-O`
execution. From the repository root, reproduce the JSON with

```sh
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/six_vertex_conditional_kernel_certificate.py --output /tmp/six-vertex-conditional-kernel-certificate.json
```
