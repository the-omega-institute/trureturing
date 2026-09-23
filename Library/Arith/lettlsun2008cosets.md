---
bibkey: lettlsun2008cosets
authors: "Günter Lettl; Zhi-Wei Sun"
year: 2008
title: "On covers of abelian groups by cosets"
doi: 10.48550/arXiv.math/0411144
url: https://arxiv.org/abs/math/0411144
claim: "An essential class in a finite cover imposes lower bounds on the number of classes and on weighted prime-specific mismatches at a private point."
strata_touched:
  - D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity
license: citation-only
triage: anchor
---

# Essential classes and weighted prime mismatches

Published in *Acta Arithmetica* 131 (2008), no. 4, pages 341–350.
The inspected [arXiv v2](https://arxiv.org/pdf/math/0411144v2) is dated
11 March 2008; the first preprint was posted 7 November 2004. The full
statements and proofs below were checked 16 September 2026.

Theorem 1.3 states that an essential class of index n in an m-cover by k
cosets of an abelian group satisfies `k >= m + f(n)`, where
`f(n) = sum_p v_p(n)(p-1)`. For an inclusion-minimal ordinary cover of
the integers this applies to every original modulus. The paper attributes
the integer, m=1 case to Znám (1975); it is not a new covering-system bound.

Theorem 2.1 gives more information. In an m-cover, at an integer a with
multiplicity exactly m, let N_a be the least common multiple of the moduli covering a.
Let I(p) contain precisely those other original labels s for which the
prime-to-p part of n_s divides a_s-a, but n_s itself does not. Then
`sum_(s in I(p)) p^(-(v_p(n_s)-v_p(a_s-a)-1)) >= v_p(N_a)(p-1)`.
In the ordinary-cover case, a private point of class t has `N_a=n_t`.

These are necessary conditions for an actual cover. Irredundancy of a
noncovering family does not supply their coverage premise, and an isolated
smooth head of a full covering system need not satisfy them. The
[Erdős #7 dossier](../../Problems/erdos-7-odd-covering-systems.md) uses these
results to retain original labels when studying head and tail coordinates.
No Lean implementation of these public theorems is supplied by this note.

No source text or code is vendored.

## Derived phase-shell accounting and active-depth cuts

The following is an ordinary finite-measure application of the weighted theorem above. Every quantity belongs to one fixed cover; it introduces no new source theorem or Lean declaration.

### The covering premise and pointwise demand

Fix one finite inclusion-minimal whole cover by original classes
\(C_s=a_s\pmod{m_s}\), with period \(L=\operatorname{lcm}_s m_s\).
Give \(X=\mathbb Z/L\mathbb Z\) uniform probability \(\mu\).
Let \(U_t\) be the region covered only by t, and M the region covered at
least twice. Inclusion minimality makes every \(U_t\) nonempty, while
whole coverage gives the disjoint partition

\[
 X=M\mathbin{\dot\cup}\coprod_tU_t.
\]

At every \(x\in U_t\), the full cover has global minimum multiplicity
1 and attains it at x. Thus both premises in Lettl--Sun Theorem 2.1 hold:
the family is a 1-cover everywhere and has multiplicity exactly 1 at x.
The lcm of the moduli of classes containing x is precisely \(m_t\).
Neither an irredundant noncover nor a nonminimum point of a whole cover
has this justification.

For a prime p dividing \(m_s\), write
\(e=v_p(m_s)\), \(d=m_s/p^e\), and define

\[
 E_{s,p,r}=\{x:x\equiv a_s\pmod{dp^r},\quad
                    x\not\equiv a_s\pmod{dp^{r+1}}\},
 \qquad0\le r<e,
\]
\[
 \alpha_{s,p,r}=p^{r+1-e}.
\]

The index s is in the theorem's directional set \(I_x(p)\) exactly when
d divides \(a_s-x\) and \(m_s\) does not. This is equivalent to membership
in exactly one of the displayed shells, with
\(r=v_p(a_s-x)<e\). The weight in the published theorem is then exactly
\(p^{-(e-r-1)}=\alpha_{s,p,r}\). Valuation at zero never arises;
changing the representative of x modulo L preserves every such depth.
If p does not divide \(m_s\), s cannot satisfy the directional predicate.
The published inequality therefore gives, at each \(x\in U_t\),

\[
 \sum_{s:p\mid m_s}\sum_{r<v_p(m_s)}
 \alpha_{s,p,r}\mathbf1_{E_{s,p,r}}(x)
 \ge v_p(m_t)(p-1).
\]

Integrating over \(U_t\) proves the proposed row demand for
\(B_{t,p;s,r}=\alpha_{s,p,r}\mu(U_t\cap E_{s,p,r})\).
When p does not divide \(m_t\), its demand is zero, but its B entries
need not vanish.

### Disjointness and complete columns

For a fixed s, shells at different depths of one prime are disjoint
because the first failure of p-adic agreement is unique. If p and q are
different primes, a p-shell requires agreement modulo the full q-part
of \(m_s\), whereas a q-shell requires failure of that agreement. Hence
these shells are disjoint too. All shells miss \(C_s\), and therefore
miss \(U_s\).

Since \(dp^{r+1}\) divides L, exact counting gives

\[
 \mu(E_{s,p,r})=\frac{p-1}{dp^{r+1}},\qquad
 \alpha_{s,p,r}\mu(E_{s,p,r})=\frac{p-1}{m_s},\qquad
 0<\alpha_{s,p,r}\le1.
\]

The partition of X yields the complete column identity

\[
 \sum_tB_{t,p;s,r}
 +\alpha_{s,p,r}\mu(M\cap E_{s,p,r})
 =\frac{p-1}{m_s}.
\]

Restricting the sum to \(p\mid m_t\) requires the additional term

\[
 V_{s,p,r}=\alpha_{s,p,r}
 \sum_{t:p\nmid m_t}\mu(U_t\cap E_{s,p,r}).
\]

This is a real missing quantity, not merely a notational possibility.
Use the minimal period-12 cover
\(0\bmod2,0\bmod3,1\bmod4,5\bmod6,7\bmod12\).
For supplier \(s=1\bmod4\), p=2 and r=1, the shell is
\(\{3,7,11\}\pmod{12}\), with weight 1. Its mass on retained
positive-demand private regions is 1/6, its overlap-region mass is zero,
and its omitted private mass is 1/12: residue 3 is private to the
modulus-3 class. Thus

\[
 \frac16+0+\frac1{12}=\frac14.
\]

The equality without V would read \(1/6=1/4\) and is false.

### Every demand-row subset gives a necessary cut

Let Q be any nonempty subset of positive-demand rows \((t,p)\), and let
\(T_Q\) contain the distinct target indices in those rows. Set
\(u_t=\mu(U_t)\), \(u_Q=\sum_{t\in T_Q}u_t\), and let
\(S_s(Q)\) denote all service from original supplier s to these rows.

At any point, at most one private region occurs, and at most one shell
of s occurs. Its weight is at most 1, and no shell occurs on \(U_s\).
Consequently

\[
 S_s(Q)\le u_Q-\mathbf1_{s\in T_Q}u_s.
\]

Within any one shell, the selected private regions are disjoint, so the
total service of that column is at most \((p-1)/m_s\). Only shells
meeting a selected \(U_t\) with matching row prime p contribute.
If \(\nu_Q(s,p)\) counts their depths, then

\[
 S_s(Q)\le\frac1{m_s}\sum_{p\mid m_s}(p-1)\nu_Q(s,p).
\]

Summing the row lower bounds and then both supplier upper bounds gives

\[
 \sum_{(t,p)\in Q}u_tv_p(m_t)(p-1)
 \le\sum_s\min\!\left(
 u_Q-\mathbf1_{s\in T_Q}u_s,
 \frac1{m_s}\sum_{p\mid m_s}(p-1)\nu_Q(s,p)\right).
\]

The same argument works for every Q; it does not combine capacities from
different covers. Replacing \(\nu_Q(s,p)\) by all depths \(v_p(m_s)\)
weakly increases each supplier bound. A missing depth need not make the
minimum smaller, because the target-mass branch can already be the
smaller branch. These are necessary subset cuts. No equivalence to a
max-flow realization, or sufficiency for an actual covering family, has
been established.

### Aggregate accounting and verification

Let \(f(m)=\sum_pv_p(m)(p-1)\), and sum the omitted private masses and
overlap masses over all columns to obtain V and W. Summing the complete
column identities, and then using all positive row demands, proves

\[
 \sum_tu_tf(m_t)+W+V\le\sum_s\frac{f(m_s)}{m_s}.
\]

For the period-12 control these four quantities are respectively
\(5/4\), \(5/12\), \(2/3\), and \(5/2\). The actual total service
on positive-demand rows is \(17/12\), so the column identity is exact
and the aggregate demand inequality has slack 1/6.

A single supplier shell may service several private regions, sharing its measured capacity; those points do not receive independent copies of that capacity. Dropping the nonnegative V term leaves a valid weaker aggregate inequality, while the complete column identity requires it.

The [standard-library replay](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/phase_shell_transport.py)
uses the [complete finite inputs](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/phase_shell_transport.input.json)
and retains the [full result](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/phase_shell_transport.json).
Run `--base <report-base> --check` under `python3 -B -I -S -O`.
All 1,688 checks remain active, including the original directional
predicate at every private point, full columns, cross-prime disjointness,
and each supplier's two separate bounds for all 134 nonempty row subsets.
For the period-12 cover, all 127 cuts pass; 88 strictly improve the
all-depth bound and 11 attain the demand. For the repeated odd cover
\(0,1,2\bmod3\), all seven cuts are tight. The latter has repeated
numerical moduli. The negative control \(0,1\bmod3\) is irredundant
but does not cover: at private point 0 its p=3 directional sum is 1,
below the putative demand 2.

These cuts provide necessary constraints with complete measured
capacities. The missing ingredient for the distinct-odd covering
problem remains a universal contradiction or further restrictions
forcing one; neither finite control supplies it. No literature
originality or formal verification is asserted for this derived interface.
