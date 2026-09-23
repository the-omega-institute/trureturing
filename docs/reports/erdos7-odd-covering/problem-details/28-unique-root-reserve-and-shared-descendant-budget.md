[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

<a id="unique-root-reserve-and-shared-descendant-budget"></a>
# The unique root-3 reserve leaves twelve specified child sets

Thirty-eight of the fifty root-3 child-prime sets left by
[Chapter 25](25-six-vertex-block-fees-and-a-finite-prime-core-frontier.md)
can be excluded by spending the unused global reserve at their unique
exceptional block. The result applies when every other block has an
established recursive fee. In particular, it improves Chapter 25's
noncoverage criterion for graphs whose blocks have at most six vertices:
only the twelve sets listed in Section 5 remain excluded by that criterion.
All original finite prime-power heights, residues, and supports are retained.
The twelve entries are prime sets, not twelve finite congruence systems.

The argument uses the unchanged coupled first-root inequality (KR14) of
[Chapter 21](21-coupled-first-root-profiles-and-an-exceptional-five-prime-block.md),
and the actual-domain recursion of
[Chapter 23](23-conditional-kernels-and-recursive-block-noncoverage.md).
The arithmetic certificate evaluates their existing finite inequalities.
The probability and graph-recursion implications are ordinary mathematical
proofs, not Lean-certified results.

## 1. Spend the reserve at the unique exceptional root block

Let the original congruence family be finite, with pairwise distinct odd
moduli greater than one. Root its prime block-cut component containing 3
at 3. Retain the fees
\[
 f(5)=\frac7{24},\quad f(7)=\frac18,\quad
 f(11)=\frac1{24},\quad f(13)=\frac1{48},\quad
 f(q)=2^{-(q-1)/2}\quad(q\ge17).
\]
Chapter 25's deletion of the composite-21 term gives the common bound
\[
 \sum_{q\ge5\text{ prime}}f(q)\le
 F_*:=\frac{1493}{3072},\qquad
 r:=\frac12-F_*=\frac{43}{3072}.
 \tag{UR1}
\]
Every exceptional six-vertex set left there contains \(\{3,5,7\}\).
Distinct graph blocks share at most one vertex, so at most one such
exceptional block \(K\) occurs in the whole graph. It contains the root
3 and therefore has parent 3. Write its five actual child primes as
\(J\), and put
\[
 C=\sum_{q\in J}f(q),\qquad E=F_*-C,\qquad
 M=\frac12-E=C+r.
 \tag{UR2}
\]
Every non-3 descendant block is in the established recursive class.
Thus the bottom-up induction proves, before estimating \(K\), the
actual child-domain bounds
\[
 H_q(V_q)\ge1-\frac1{q-1}-c_qe_q,\qquad
 e_q=\sum_{p\in D_q}f(p),\qquad e_q\le E,
 \tag{UR3}
\]
where \(c_5=3/10\), \(c_q=2/(q-1)\) for \(q\ge7\), and
\(D_q\) is the actual strict descendant set. These sets are pairwise
disjoint and avoid \(J\).

Let \(B_K\) be the block-only blocker on the original complete
3-coordinate, and let \(P_3\) be the union of the original pure-3
classes. The other outgoing root blocks have total certified blocker
mass at most \(E\): their charged immediate child sets are mutually
disjoint and avoid \(J\). Since \(H_3(P_3)\le1/2\), the exact
root recursion yields
\[
 H_3(V_3)\ge1-H_3(P_3)-H_3(B_K)
                  -\sum_{L\ne K}H_3(B_L)
             \ge M-H_3(B_K).
 \tag{UR4}
\]
Consequently \(H_3(B_K)<M\) is sufficient for positive root survival.
Private block sides glue at a common surviving root word, and distinct
components glue by CRT as in Chapter 23.

This spends the reserve once. It does not improve the uniform local fee
\(C\), change any non-3 recursive claim, or bound the prime-fee sum by
the new blocker target. After spending the reserve, the old lower bound
\(43/3072\) on root survival is replaced by the actual positive margin
in (UR4). All descendant bounds and outgoing-charge bounds refer to the
same original family; using their separate common upper bound \(E\)
only weakens those inequalities.

## 2. The exact coupled first-root certificate

For a nonnegative expense cap \(u\) and blocker target \(T\), set
\[
 b_5(u)=\frac1{3-(6/5)u},\qquad
 b_q(u)=\frac1{q-2-2u}\quad(q\ge7),\qquad
 b_S=\prod_{q\in S}b_q(u).
\]
Let \(w_S=0\) for singleton \(S\) and \(w_S=b_S\) otherwise.
For \(A\subseteq J\), define the support residual
\[
 Z_A(v)=\sum_{\mathcal F}
            (-1)^{|\mathcal F|}\prod_{S\in\mathcal F}v_S,
\]
where the sum ranges over families of pairwise disjoint nonempty
supports contained in \(A\), including the empty family. There are
203 such families when \(|A|=5\). Put
\[
 L_0=\sum_{\varnothing\ne S\subseteq J}b_SZ_{J\setminus S}(w).
\]
Under the strict-region hypotheses checked below, (KR14) says that a
blocker of mass at least \(T\), for \(1/3<T<2/3\), would imply
\[
 \min_{0\le y_S\le b_S}
 \left[\frac13Z_J(w+y)
       +\left(T-\frac13\right)Z_J(w+b-y)\right]\le\frac{L_0}{6}.
 \tag{UR5}
\]
Thus a strictly positive gap above \(L_0/6\) proves
\(H_3(B_K)<T\). All 32 induced residuals at \(w+b\) are strictly
positive in every retained row, giving the full strict box used by
(KR14). The existing conditional probability bound applies with these
dominating caps; no monotonicity of an optimized minimum is assumed.

For every nonempty support, the objective's partial derivative is at
most \(-m_S\), where
\[
 m_S=\frac13Z_{J\setminus S}(w+b)
        -\left(T-\frac13\right)Z_{J\setminus S}(w).
 \tag{UR6}
\]
When \(m_S>0\), the minimizing coordinate is \(y_S=b_S\).
The remaining coordinates are separately affine, so their complete
corner enumeration gives the exact minimum. The certificate recomputes
all derivative bounds at every target and cap; it does not reuse the
forced-support set of a different target.

For the fixed-reserve application take \(u=E\) and \(T=M\).
All fifty inherited tuples are recomputed. Their 12,440 free corners
give 31 positive and 19 negative gaps, with no zero gaps. The smallest
positive gap occurs at \(J=(5,7,11,13,43)\) and is
\[
 \frac{16315593837048237831107322855008746701}
 {53492794872230672809615562047262440816640}>0.
 \tag{UR7}
\]
The negative gaps show that this common-expense rectangle fails to
establish the required bound. They are not realizations by actual
arithmetic progressions.

## 3. Keep the actual shared descendant budget

A sharper application couples the core's distortion to the other
outgoing charges. Define
\[
 D=\bigsqcup_{q\in J}D_q,\qquad
 x=\sum_{q\in J}e_q=\sum_{p\in D}f(p),\qquad 0\le x\le E.
 \tag{UR8}
\]
Let \(A\) be the union of the charged immediate child sets of all
other outgoing root blocks. The block-cut tree gives
\(A\cap(J\cup D)=\varnothing\). Hence
\[
 \sum_{p\in A}f(p)\le F_*-C-x=E-x,
 \qquad e_q\le x\quad(q\in J).
\]
Each other root block uses the parent-3 fee coefficient 1. Substituting
its total charge bound into the exact root recursion gives
\[
 H_3(V_3)\ge M+x-H_3(B_K).
 \tag{UR9}
\]
These are inequalities on one actual family, retaining its descendant
sets and domains. No descendant expense is independently reassigned.

For an interval \([l,u]\) containing the actual \(x\), use the
coordinate caps \(b_q(u)\) and target \(T=M+l\). Every actual
child expense obeys \(e_q\le x\le u\), and
\(M+l\le M+x\). A positive gap in (UR5) therefore gives
\[
 H_3(B_K)<M+l\le M+x,
\]
and (UR9) proves positive root survival. A collection of such intervals
covering \([0,E]\) handles every possible actual expense without
asserting monotonicity of the optimized KR expression.

The following exact partitions cover seven additional tuples. Entries
are endpoints divided by \(E\); consecutive endpoints define one
closed interval.

| Actual children \(J\) | Partition endpoints \(x/E\) |
| --- | --- |
| \(5,7,11,13,41\) | \(0,1/2,1\) |
| \(5,7,11,17,29\) | \(0,1/8,1/4,1/2,1\) |
| \(5,7,11,17,31\) | \(0,1/2,1\) |
| \(5,7,13,17,29\) | \(0,1/4,1/2,1\) |
| \(5,7,13,17,31\) | \(0,1/2,1\) |
| \(5,7,13,19,29\) | \(0,1/2,1\) |
| \(5,7,17,19,23\) | \(0,1/2,1\) |

All seventeen intervals have strictly positive gaps, after 3,688 free
corner evaluations. The smallest occurs at
\(J=(5,7,11,13,41)\), \(l=0\), \(u=7167/2097152\), and is
\[
 \frac{100940323747930477708823537562792377}
 {5501376123406464765500334715636798193664}>0.
 \tag{UR10}
\]

## 4. The thirty-eight excluded root cores

Each row lists the four fixed children followed by one of the indicated
fifth primes. The first numeric column uses the fixed reserve; the
second uses the shared-budget partitions. These disjoint columns total
31 and 7 respectively.

| Fixed four children | Fixed-reserve fifth primes | Additional shared-budget fifth primes |
| --- | --- | --- |
| \(5,7,11,13\) | 43, 47, 53, 59, 61, 67, 71 | 41 |
| \(5,7,11,17\) | 37, 41, 43, 47 | 29, 31 |
| \(5,7,11,19\) | 29, 31, 37 | — |
| \(5,7,11,23\) | 29 | — |
| \(5,7,13,17\) | 37, 41, 43, 47, 53, 59, 61 | 29, 31 |
| \(5,7,13,19\) | 31, 37, 41, 43, 47 | 29 |
| \(5,7,13,23\) | 29, 31 | — |
| \(5,7,17,19\) | 29, 31 | 23 |

For every such actual child set, the unique core leaves a positive
root-domain mass, provided every other graph block has an established
recursive fee. The original finite congruence family is therefore
noncovering in that class, for every choice of its original heights
and residues.

## 5. The twelve remaining child sets and the boundary

The twelve sets below are precisely the fifty inherited entries minus
the thirty-eight just treated.

| Fixed four children | Remaining fifth primes | Count |
| --- | --- | ---: |
| \(5,7,11,13\) | 17, 19, 23, 29, 31, 37 | 6 |
| \(5,7,11,17\) | 19, 23 | 2 |
| \(5,7,11,19\) | 23 | 1 |
| \(5,7,13,17\) | 19, 23 | 2 |
| \(5,7,13,19\) | 23 | 1 |

Adjoin 3 to obtain the corresponding six-vertex graph blocks. In
particular, a graph all of whose blocks have at most six vertices is
noncovering if it contains none of these twelve blocks. Components
without 3 already satisfy Chapter 25's established recursive bounds.
More generally, all other previously certified recursive block classes
remain allowed.

No bound on the original prime-power heights has been imposed. The
remaining sets are not covering constructions, and this chapter makes
no minimality claim about the list under sharper estimates. It supplies
no unrestricted dense-small-prime block theorem and does not settle
Erdős #7. The literal-residue branches of Chapter 26 remain additional
criteria on the same actual families.

## 6. Portable exact certificate

The standard-library program
[unique_root_reserve_certificate.py](../frontier/cover-geometry/unique_root_reserve_certificate.py)
and its [exact data](../frontier/cover-geometry/unique_root_reserve_certificate.json)
recompute all fifty fixed-reserve rows and the seventeen shared-budget
intervals. The program reads the Chapter 25
[six-vertex certificate](../frontier/cover-geometry/six_vertex_conditional_kernel_certificate.json)
through its required `--inherited` argument. The input digest is pinned
as
`5fc133a5826747a04787e13a6ddc92c311d065cd54357a18c9f0e414bb45a571`.
No other program or hidden input file is loaded.

Every row retains the dominating coordinate caps, all 32 strict
residuals, all 31 derivative margins, the forced and free supports,
corner count, minimizing allocation, both residual values at that
allocation, \(L_0\), and exact gap. The certificate also checks the
complete inherited list, interval adjacency and endpoints, disjointness
of the two successful groups, and the exact remaining twelve sets.
Altogether it evaluates 2,144 induced residuals, 2,077 derivative
margins, and 16,128 free corners.

The arithmetic uses exact fractions and an integer expansion over all
203 disjoint support families, with minimizing residuals checked by
subset deletion. Independent reconstruction using elementary-symmetric
residuals and integer subset recurrence gives the same 67 minima,
forced/free sets, and 38/12 partition. These finite exact calculations
do not replace the probability, uniqueness, or recursion arguments.

The program requires Python 3.10 or later and rejects optimized `-O`
execution. From the repository root, reproduce the JSON with

```sh
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/unique_root_reserve_certificate.py --inherited docs/reports/erdos7-odd-covering/frontier/cover-geometry/six_vertex_conditional_kernel_certificate.json --output /tmp/unique-root-reserve-certificate.json
```
