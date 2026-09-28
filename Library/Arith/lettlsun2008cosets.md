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

## Original-class reserves refine the same global shell cuts

The following ordinary derivation retains one actual whole cover, its original numerical labels, and all prime heights. It strengthens a specified capacity bound without asserting a universal violation for distinct odd moduli. The whole-cover family below contains even moduli: it tests exactly which structural arguments still need an all-odd hypothesis. These are derived results and controls, not claims attributed to Lettl--Sun or new Lean declarations.

### Exact original-class containment

Let `C_s = a_s mod m_s` be one finite irredundant whole cover, with period L, uniform probability μ on Z/LZ, disjoint nonempty private regions U_t, masses u_t, and overlap region M. For `p^e || m_s`, put `d=m_s/p^e` and

    E_c = C(a_s, d p^r) \ C(a_s, d p^(r+1)),
    c=(s,p,r), 0<=r<e,
    alpha_c=p^(r+1-e), kappa_c=(p-1)/m_s.

The phase-shell accounting above supplies the private-point Lettl–Sun row demands, complete column identity

    sum_t alpha_c μ(U_t ∩ E_c) + alpha_c μ(M ∩ E_c) = kappa_c,

and disjointness of all shells of a fixed supplier, across both prime and depth. These facts are reused here.

For **arbitrary** original moduli m_s,m_t, full-class containment is equivalent to

    C_t ⊆ E_(s,p,r)
      iff d p^(r+1) | m_t,
          d p^r | (a_t-a_s),
          d p^(r+1) does not divide (a_t-a_s).                 (A)

Proof. Put n=d p^r. Containment in C(a_s,n) requires and implies `n|m_t` and `n|(a_t-a_s)`. Subject to this, C_t misses C(a_s,pn) exactly when the two congruences are incompatible, namely `gcd(m_t,pn)` does not divide their residue difference. Since `n|m_t`, that gcd is either n or pn. The first cannot be incompatible; hence pn divides m_t and does not divide the residue difference. Conversely these conditions give containment and exclusion. This is valid on the period because every involved modulus divides L.

In particular (A) implies **p divides m_t**. Consequently `F_c={t:C_t⊆E_c}` has no member with `p∤m_t` and does not account for the zero-demand omitted-private term V. Private-region partial intersections with those classes can be positive and remain unaccounted for by this reserve.

Under the stronger hypotheses `s!=t` and `m_s|m_t`, write `Delta=m_s/gcd(m_s,a_t-a_s)`. Irredundancy gives Delta>1, since otherwise C_t⊆C_s. Formula (A) becomes

    C_t ⊆ E_(s,p,r) iff Delta=p^(e-r).

Thus a pure defect Delta=p^j gives the exact occupancy `p^(1-j)u_t` in the unique shell r=e-j. A mixed-prime defect gives no full-class occupancy in any supplier shell. This gives the divisor-defect specialization at arbitrary heights.

### The refined subset cut and its effective gain

Fix any nonempty set Q of positive-demand rows (t,p). Let `T_p={t:(t,p)∈Q}`, `T=union_p T_p`, and `u_Q=sum_(t∈T)u_t`, counting each private region once. For c=(s,p,r), set

    F_c={t:C_t⊆E_c},
    rho_c=alpha_c sum_(t∈F_c\T_p)u_t.

Selected service in that column is

    S_c=sum_(t∈T_p)alpha_c μ(U_t∩E_c).

The private regions in the selected sum and the forced omitted sum are distinct. Retaining those terms in the complete column identity and dropping only nonnegative terms proves

    S_c <= kappa_c-rho_c.                              (B)

Let A_s(Q) be precisely those columns of s whose selected service is positive. Define

    A_s=u_Q-1_(s∈T)u_s,
    C_s=sum_(c∈A_s(Q))kappa_c,
    R_s=sum_(c∈A_s(Q))rho_c,
    D(Q)=sum_((t,p)∈Q)u_t v_p(m_t)(p-1).

The separate target-mass bound `S_s<=A_s` remains valid: at every actual point at most one U_t occurs and at most one shell of s occurs, its weight is at most one, and shells miss U_s. Summing (B), applying this separate bound, then summing Lettl–Sun row demands proves

    D(Q) <= sum_s min(A_s,C_s-R_s).                    (C)

All quantities concern the same original cover and its actual private regions. The proof assumes no independent attainability of different branch laws. All off-row partial private occupancy and overlap occupancy not captured by F are still nonnegative discarded terms; they have not been solved or identified with zero.

The exact improvement over the old active-depth right side is

    sum_s [ R_s - (C_s-A_s)_+ ]_+.                    (D)

Indeed `min(A,C)-min(A,C-R)=[R-(C-A)_+]_+` for `A>=0` and `0<=R<=C`. This is a useful explicit consumer: a reserve is effective only after it exceeds the unused room between column and target-mass branches. Counting positive reserves alone does not prove a strict cut improvement.

The missing unrestricted arithmetic claim can now be stated precisely: from all-oddness and numerical distinctness, force some actual row set Q for which these original-region reserves, or additional measured partial occupancies, exceed the old cut slack after the masking term in (D). Neither positivity `u_t>=1/L` nor two-parent existence supplies such a uniform statement.

### Parent-square scope and bounded reuse

For this parent-label argument assume pairwise-distinct original numerical moduli, and assume that every invoked numerical parent or nonunit grandparent is present as an original label; a divisor-closed inventory is one sufficient condition for this existence, not a consequence of irredundancy alone. Fix distinct primes p,q and a common pair of global top exponents H_p,H_q. For children t attaining those exponents, the numerical parents `m_t/q` and `m_t/p` have exponent pairs `(H_p,H_q-1)` and `(H_p-1,H_q)`. Within this fixed stratum the two families are disjoint, and each fixed parent map is injective.

If a p-parent is active at the child's common lower source and irredundancy forces only a top p-digit disagreement, its residue defect against the child is p. Hence its top p-shell contains the entire child class, with weight one. The corresponding statement holds for q. The child private mass therefore reserves u_t in each named parent column whenever that child row is omitted and the column is actually active for another selected row.

Summing these reservations is valid because the original U_t are disjoint. A numerical supplier may contribute different prime columns, which are separately named and disjoint. For varying top exponents, numerical cross-type disjointness is false: at p=3,q=5, `225/5=135/3=45`. Both child moduli contain p and q. This arithmetic example is not asserted to be a cover; it shows exactly why the stratum restriction is needed. Column-indexed accounting remains sound in that setting.

A nonunit grandparent m_t/(pq) supplies an extra full-class reserve only when its defect is a pure prime power r^j, giving weight r^(1-j). A mixed defect gives no such shell reserve. Direct-parent reserves can be masked by (D), can service the child itself if its row is selected, and are irrelevant when their columns are inactive for Q.

### An infinite family of whole covers with even moduli

Take distinct odd primes p,q and `2<=b<=min(p-1,floor(q/2))`. Put

    A=p-1, B=q-b, C=b, h=max(A,B)-1, L=2^h p q,
    gamma_1=0, gamma_k=B+k-1 (2<=k<=C).

Use the original congruences

    D_j: 2^(j-1) mod 2^j,                      1<=j<=h;
    P_i: 0 mod 2^(i-1), i mod p,               1<=i<=A;
    Q_j: 0 mod 2^(j-1), j mod q,               1<=j<=B;
    T_k: 0 mod 2^(k-1), 0 mod p, gamma_k mod q, 1<=k<=C.

All moduli exceed one and are pairwise distinct. Each prime-support type has an initial interval of binary exponents, and C<=A,B; every nonunit divisor of a displayed modulus is displayed. The lcm is L.

For any nonzero binary coordinate z, exactly one D_j covers it, namely j=v_2(z)+1. At z=0, the P_i cover all nonzero p-phases, the Q_j cover q-phases 1..B, and the T_k fill exactly the missing strip `{0}×{0,B+1,...,q-1}`. Thus this is whole coverage.

Every P_i, Q_j and T_k has an actual private point at z=0, respectively high phases (i,0), (0,j), and (0,gamma_k). For D_j, use z=2^(j-1). The active line families leave a rectangle of size

    (p-min(j,A))(q-min(j,B)),

and at most min(j,C) T-cells are active. The rectangle is strictly larger:

* j<C: its factors are at least 2 and C+1;
* C<=j<A: its factors are at least 2 and C;
* j>=A: since j<=max(A,B)-1, necessarily j<B, so its factors are 1 and at least C+1.

An uncovered high cell in that rectangle is private to D_j. This proves irredundancy for all allowed parameters, including A>B and B>A.

Each T_k has exactly one private residue modulo L, because every nonzero binary coordinate is already covered by a D_j. At its private residue the same fixed 1×b strip occurs. Its actual numerical parents are P_k and Q_k, both active at lower source zero; for k>=2 the original nonunit grandparent is D_(k-1). The k=1 numerical grandparent is one and legitimately absent. The number of original labels divisible by p or q is `A+B+C=p+q-1`; the total is `h+p+q-1=1+f(L)`. These equalities are exact numerical counts, not an inference that an arbitrary original class has modulus L.

The family therefore disproves strip exclusion from the listed structural hypotheses with oddness removed. It does **not** supply a distinct odd covering, refute odd noncoverage, or show that mixed odd supports can simulate the binary mechanism. A literal replacement of a binary split by one odd-prime split would need r-1 different nonzero branches at the same numerical modulus; distinctness prevents that particular substitution. Whether more complicated mixed odd supports can perform the role remains open here.

### A strict consumer and exact controls

The [standard-library verifier](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-divisor-shell-reserves/original_divisor_shell_reserves.py) constructs CRT residues and actual residue bitmasks from the formulas. The [exact data](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-divisor-shell-reserves/original_divisor_shell_reserves.json) are reproduced by

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-divisor-shell-reserves/original_divisor_shell_reserves.py
```

Checks remain active under Python-O. Twelve parameter triples were checked, with periods

    60,336,8448,560,280,14080,7040,3520,1120,2464,28160,39424.

For each it checks complete coverage, distinctness, divisor closure, irredundancy, literal private masks, every full shell identity, cross-prime shell disjointness, the arithmetic iff (A) against literal containment for every target/column pair, every divisor-defect specialization, every integrated directional demand, all singleton row cuts, all prime-slice cuts and the full row cut. It checks every actual T singleton, both named parents, all available named grandparents, and the class-count equality. These are finite controls supporting the ordinary family proof, not exhaustive checks of arbitrary congruence covers.

At p=3,q=5,b=2, L=60, the classes in the order D,P,Q,T are

    1 mod2, 2 mod4, 1 mod3, 2 mod6, 1 mod5,
    2 mod10, 8 mod20, 0 mod15, 24 mod30.

The verifier checks each listed private witness `3,18,4,20,36,12,48,0,24` against actual covering multiplicity.

At p=5,q=11,b=4, h=6,L=3520, the private masses are:

    D1..D6: 1248,400,104,12,4,1 points;
    P1..P4: 4 points each;
    Q1..Q7 and T1..T4: 1 point each.

The singleton private residues are exactly Q5=1600, Q6=1920, Q7=2240, T4=3200. For Q={(D1,2),(Q5,11),(Q6,11),(Q7,11)}, supplier Q4 has target branch1251/3520. Its only active columns are:

    (Q4,2,0): capacity1/88, no full-class omitted reserve;
    (Q4,11,0): capacity10/88, omitted whole class exactly T4,
               reserve1/3520.

Thus the **full** forced-class refinement, not merely a one-reserve weakening, is exactly

    old minimum440/3520 -> refined minimum439/3520.

The actual selected service of Q4 is only7/704, so this strengthened capacity is still a loose upper bound. Across all suppliers the old cut is973/440=3892/1760, the refined cut is3887/1760, and the demand is639/1760. The total strict gain is5/1760. The actual even cover remains feasible, as required.

For fixed p,b and growing q, each T private mass is1/L and h=q-b-1 eventually. Its fractions of its parent capacities are

    2^(k-1-h)/(q(p-1)),  2^(k-1-h)/(p(q-1)),

and of its binary-grandparent capacity, when present,

    2^(k-1-h)/(pq).

All tend to zero. Thus no uniform positive relative saving follows from these parent/grandparent structural premises alone.

### Remaining unrestricted obligation

The exact effective gain in(D) separates forced occupancy from occupancy large enough to change the supplier minimum. An all-odd contradiction still requires a row set whose same-cover effective gains exceed the old cut slack, or further restrictions that provide an equally sufficient bound. Whole-class containment cannot recover the missing partial private intersections with zero-demand rows.

The fixed1225-head results in[Report449](../../docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/449-equality-sources-have-a-private-law-below-nine.md) and these original-label global cuts preserve different parts of the problem. The head law has not been lifted through every original outside-cofactor constraint; the global cut has not been shown to be violated for every distinct odd inventory. No unrestricted noncoverage conclusion, polyhedral independence from every earlier subset cut, or literature-originality claim follows from this increment.

## Global top shadows and original top-shell pair capacities

The following ordinary deductions combine the original phase-shell interface above with the proper-hyperplane form of [Balister–Bollobás–Morris–Sahasrabudhe–Tiba, Theorem1.2](balister2019erdos.md). They give necessary conditions for one actual distinct-odd whole cover, not an unrestricted contradiction, new Lean verification, or a claim of literature originality. Every numerical capacity below uses the SAME uniform probability on the original period. These capacities cannot be transferred to an independently chosen supported head law without a further measure-transport argument.

### One original uniform source and its global top digits

Fix one finite inclusion-minimal whole cover by original classes C_s=a_s mod m_s, with pairwise-distinct odd m_s>1. Let

    L=product_p p^H_p, R=rad(L)=product_p p, N=L/R,
    X=Z/LZ with uniform probability mu.

Split each prime coordinate, as a SET, into its lower digits and one global top digit:

    x_p=b_p+p^(H_p-1)y_p,
    0<=b_p<p^(H_p-1), 0<=y_p<p.

CRT gives X=B×Q, where B=product_p Z/p^(H_p-1)Z is identified with Z/NZ and Q=product_p F_p. Under the original uniform mu this is the product of uniform beta on B and uniform counting probability on Q. No additive-group splitting is asserted when H_p>1.

For each original label define

    T_s={p:v_p(m_s)=H_p}, P_A=product_(p in A)p,
    bar_m_s=m_s/P_(T_s),
    D_s={z in B:z=a_s mod bar_m_s}.

Then bar_m_s divides N. For p in T_s let theta_(s,p) be the top p-digit of a_s modulo p^H_p. At lower source z the class is inactive unless z belongs to D_s; if active, its slice is the top hyperplane

    H_s={y:y_p=theta_(s,p) for every p in T_s}.

An active label with T_s empty fills the whole Q. Distinct original moduli with a fixed top support A have distinct lower indices, since m_s=P_A bar_m_s. This observation does not identify labels with different A or independently relabel their phases.

The cited theorem says that a cover of the box formed by the first n odd-prime coordinate sizes by proper axis-parallel hyperplanes has two parallel members, meaning equal fixed-coordinate supports. Properness excludes the empty support; this is the exclusion of the modulus-one progression in its arithmetic interpretation and footnote2. The same conclusion holds for any n distinct odd primes q_1<...<q_n: restrict coordinate i to a subset of the size of the i-th odd prime. Discard empty intersections. Any presumed nonparallel cover restricts to another nonparallel cover with the same nonempty fixed-coordinate supports, contradicting the cited theorem.

### A private source forces a same-support, different-phase collision

For any selected family D of labels with T_t nonempty, write

    U_D=disjoint union_(t in D) U_t, u_D=sum_(t in D)u_t,
    Z_D=projection_B(U_D).

If x=(z,y) is private to a selected t, no empty-support label can be active at z: it would cover x as well as t. Whole coverage makes all active top slices cover Q. Collapse identical top hyperplanes before applying the preceding proper-hyperplane theorem. Two DISTINCT resulting hyperplanes have the same nonempty support but different phase vectors. Hence, with each unordered original pair counted once,

    U_D subset union_(s<t, T_s=T_t!=empty, theta_s!=theta_t)
                    projection_B^(-1)(D_s intersect D_t).        (TS1)

The collision occurs at the private point's OWN lower source. It need not involve that point's private owner, and the two phase vectors may differ at several primes.

For such a pair put c_st=beta(D_s intersect D_t). Its exact original-label CRT capacity is

    c_st=1/lcm(bar_m_s,bar_m_t)
           if a_s=a_t mod gcd(bar_m_s,bar_m_t),
         0 otherwise.                                          (TS2)

There is a private-region saving. On the common lower shadow the two same-support different-phase top hyperplanes are disjoint, each of density1/P_A, where A=T_s=T_t. A point of U_D cannot lie in H_s unless s belongs to D; otherwise it is also covered by an unselected label. The same applies to t. Therefore

    mu(U_D intersect projection_B^(-1)(D_s intersect D_t))
      <= [1-(2-1_(s in D)-1_(t in D))/P_A] c_st.                (TS3)

Combining(TS1) with this single-source bound gives

    u_D <= sum_(s<t, T_s=T_t!=empty, theta_s!=theta_t)
               [1-(2-1_(s in D)-1_(t in D))/P_(T_s)] c_st.     (TS4)

The saving is2/P_A if neither endpoint is selected,1/P_A if exactly one is, and zero if both are. The RHS counts each original pair over its actual lower-shadow intersection, not over an independently chosen branch law. It may count one private point several times, which is permitted for this upper bound but supplies no independent copies of the corresponding capacity.

A related phase-excess condition keeps distinct active phases rather than label multiplicity. Define

    K_A(z)=#{theta_s:T_s=A, z in D_s}.

At z in Z_D, choose one represented phase per support A. These hyperplanes are proper and nonparallel, so leave at least one top cell uncovered. All omitted distinct phases together cover that cell, because the complete active family covers Q. A union bound gives

    sum_(A!=empty) (K_A(z)-1)_+/P_A >=1/R,
    u_D/R <=sum_(A!=empty) (1/P_A)
                       integral_(U_D)(K_A(projection_B x)-1)_+ dmu(x).  (TS5)

Identical hyperplanes from different original labels are counted once in K_A. The density1/R is the density of one cell in the same finite Q, not an external resolution convention.

### Changed top phases supply p-1 distinct original labels

Fix p and select D subset{t:p in T_t}. At x=(z,y) in U_D change only its global top p-digit from y_p to a different a. The modified point leaves the private owner's class. Whole coverage supplies some original label s covering it. Privacy of x forces p in T_s: a label not fixing the global top p-digit would also cover x. It also forces

    theta_(s,p)=a,
    theta_(s,q)=y_q for q in T_s\{p},
    x in E_(s,p,H_p-1).                                    (TS6)

This is an original supplier shell with exponent v_p(m_s)=H_p and weight alpha=1. A fixed label cannot supply two different top p-phases, so the p-1 changes yield p-1 distinct suppliers. They all come from the same cover and the same private point. This elementary top-layer argument does not replace the full Lettl–Sun demand H_p(p-1), which also accounts for lower depths.

Let sigma_p be the number of distinct global supports T_s containing p. For r>=0 and M>=1 write r=Mq+b,0<=b<M, and put

    Pi(r,M)=b*q(q+1)/2+(M-b)*q(q-1)/2.

This is the minimum equal-bin pair count for r objects in M bins: whenever two occupancies differ by at least2, moving one object from the larger to the smaller decreases the pair count; a minimizer therefore has b occupancies q+1 and M-b occupancies q. Sorting the p-1 actual suppliers by T_s yields at least Pi(p-1,sigma_p) same-support supplier pairs at every selected private point.

Let R_p be the unordered original pairs(s,t) with equal top support A containing p, equal phases at every q in A\{p}, and different p-phases. For any pair in R_p, direct counting on the original product source gives

    mu(E_(s,p,H_p-1) intersect E_(t,p,H_p-1))
      =((p-2)/P_A)c_st.                                  (TS7)

Indeed the lower source must be in D_s intersect D_t; all other coordinates in A have their common fixed phase; and the top p-coordinate must avoid both distinct endpoint phases. Exactly p-2 p-phases remain. Coordinates outside A are unrestricted. Formula(TS7), including a zero CRT capacity, retains both original numerical labels and their actual phases.

Double-count selected private-point/supplier-pair incidences and then bound each incidence set by its full shell intersection. This proves

    Pi(p-1,sigma_p) u_D
       <= sum_((s,t) in R_p) ((p-2)/P_(T_s))c_st.           (TS8)

The p-2 coefficient is zero at p=2 and positive for odd p. The top-shadow collision(TS1), in contrast, also uses the odd-prime proper-hyperplane theorem. A collision differing at several primes does not automatically belong to any R_p.

If every selected target reaches both p and q at their global top heights, apply(TS8) twice to the SAME U_D and add. The LHS coefficient is Pi(p-1,sigma_p)+Pi(q-1,sigma_q), and the RHS is the sum of the two displayed pair capacities. This is an additive same-family consequence, not a product of separately optimized laws.

### Relation to the complete shell accounting

Every point on the left of(TS8) belongs to a target with p dividing m_t. Thus the double count uses positive-demand p-rows. It does not describe all other private points in those supplier columns. In particular the complete column identity above STILL contains the omitted-private term V from targets with p not dividing m_t, and its overlap term. Neither(TS8) nor the full-class containment reserves remove or recover V.

These pair capacities can constrain the same original private regions as the earlier parent reserves and subset cuts. Their savings cannot simply be added: a point may satisfy both a parent reserve and a parallel-pair constraint. Any combined dual must account for that common service explicitly. No polyhedral independence from all earlier cuts is claimed.

The unresolved implication is quantitative. One must force a selected D for which the RHS of(TS4) is smaller than u_D, or a choice of p and D for which the RHS of(TS8) is smaller than its LHS, or derive a comparably sufficient combined bound. The present hypotheses do not bound the unrestricted original pair inventory or total common-shadow capacity strongly enough. Also Pi(p-1,sigma_p)=0 whenever sigma_p>=p-1. A positive pair constraint is therefore not automatic from oddness alone. These necessary conditions do not yet overcome the earlier masked-slack obstruction or lift a freely chosen1225-head probability to the original uniform source.

### An18-label odd noncover separates collision from one-prime shell visibility

Take these original classes, with a private witness in the same row:

|m|3|5|7|9|15|21|25|35|45|49|63|75|105|175|225|315|525|1575|
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
|a|2|2|3|1|10|12|16|29|9|0|27|18|63|124|30|111|195|735|
|w|5|7|3|1|25|33|16|169|9|0|90|18|63|124|30|111|195|2310|

The modulus inventory is exactly all nonunit divisors of1575, together with49. It is odd, numerically distinct and divisor-closed above one. Every displayed witness belongs only to its own class, so the family is irredundant. It is NOT a whole cover: its period is L=11025, and exactly2415 residues are uncovered;4 is the least uncovered residue. Here N=105.

At lower source z=0 mod105 the only active labels are

    0 mod49:       T={7},   theta=0;
    30 mod225:     T={3,5}, theta=(1,1);
    735 mod1575:   T={3,5}, theta=(2,2).

The point0 is private to the modulus49 label. The unique active parallel pair is225 and1575, with common lower-shadow capacity1/105. The pair differs at BOTH top primes3 and5. Relative to point0 its endpoint defects are

    225/gcd(225,30)=15,
    1575/gcd(1575,735)=15.

Each defect is mixed, so neither endpoint places0 in any one-prime supplier shell. Direct checks of all their prime/depth shells confirm this. Thus oddness, numerical distinctness, divisor closure, irredundancy and an actual same-support phase collision do not, by themselves, make that collision visible in a one-prime shell.

The missing whole-cover premise is visible locally as well: changing only0's global top7-digit gives1575,3150,4725,6300,7875,9450, and all six are uncovered. There are no p-1 top7 suppliers at this point. The global top7 support inventory has only the modulus49 label, so sigma_7=1 and R_7 is empty. Its actual private mass is63/11025=1/175. Applying(TS8) WITHOUT whole coverage would falsely give3/35<=0. The program records the failed premise rather than claiming an odd-covering counterexample.

### Computable rejection tests on the fixed original noncover

The same literal eighteen-class family supplies an actual consumer for both necessary conditions. For a singleton D={t}, let C_t be the RHS of(TS4) divided by u_t. The test strictly rejects whole coverage precisely when C_t<1. No residue, numerical label, or probability law is optimized in computing these ratios.

|original target modulus m_t|u_t|C_t=TS4 RHS/u_t|strict rejection by this singleton TS4|
|---|---|---|---|
|9|76/1575|9/38|yes|
|25|34/2205|63/85|yes|
|45|4/441|63/50|no|
|49|1/175|2|no|
|63|4/525|23/12|no|
|75|11/1575|18/11|no|
|175|2/1575|9|no|
|225|34/11025|133/34|no|
|315|4/1575|23/4|no|
|525|2/1575|9|no|
|1575|2/3675|133/6|no|

These are exactly the top-touching labels; the remaining original labels have empty global top support and are outside this selected-target version. Selecting all eleven labels gives u_D=374/3675 and TS4 RHS=2/105, hence the ratio35/187<1.

For(TS8), compare its coefficient Pi(p-1,sigma_p) with its RHS/u_t at each singleton target. The complete prime-specific data are:

|p|sigma_p|Pi(p-1,sigma_p)|original target m_t : TS8 RHS/u_t|strict singleton rejection|
|---|---|---|---|---|
|3|2|0|9:5/76;45:7/20;63:5/12;225:35/34;315:5/4;1575:35/6|none|
|5|2|2|25:0;75:0;175:0;225:0;525:0;1575:0|all six listed targets|
|7|1|15|49:0|49|

Thus the two displayed tests detect different failures at fixed selections: target9 fails singleton(TS4), while its only top-prime(TS8) has coefficient zero; target49 passes its singleton(TS4) numerical comparison but fails(TS8) for p=7. This is a finite test comparison, not a claim of polyhedral independence from every previous cut. A failed necessary inequality certifies noncoverage of this fixed family; it does not settle unrestricted Erdős #7.

A reused even whole-cover control has period60 and literal classes

    1 mod2, 2 mod4, 1 mod3, 2 mod6, 1 mod5,
    2 mod10, 8 mod20, 0 mod15, 24 mod30.

Its private witnesses, in that order, are3,18,4,20,36,12,48,0,24. This is the p=3,q=5,b=2 case of the original-class parent-reserve family above. Exact enumeration confirms whole coverage and distinct numerical moduli. It does NOT furnish a failure of the odd top-shadow conclusions: for every top-touching singleton and their full union, the collision inclusion and weighted phase-excess comparison hold; all the displayed(TS4) comparisons also hold. In particular its full selected private union has mass1/6 and TS4 RHS3/2. The top-prime supplier and shell-pair checks also hold, including the zero coefficient at p=2. Therefore this reused even control is not evidence that(TS1), (TS4), or(TS5) extends beyond odd moduli, and is not a counterexample witnessing the necessity of oddness. The odd-coordinate premise remains part of the cited hyperplane theorem and the corresponding deductions.

### Exact reproduction and evidence boundary

The [standard-library verifier](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-top-shadow-shell-pairs/original_top_shadow_shell_pairs.py), with [exact data](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-top-shadow-shell-pairs/original_top_shadow_shell_pairs.json), retains literal original labels and one uniform residue source per control. It checks the18-class inventory, every listed private witness, complete coverage counts, all class/lower/top slice identities, original-pair CRT capacities, private-region saving bounds, and top-shell intersection identities. The data include all2415 uncovered residues of the noncover, its six uncovered top7-neighbors, every displayed singleton ratio, and the period60 even-control comparisons. The odd top-shadow assertions are guarded by the oddness premise; the even control only records their actual truth values. All whole-cover controls still check the actual suppliers and shell-pair inequality.

Positive whole-cover controls are the complete residue partitions modulo3,25 and225. Their numerical moduli are REPEATED; they are not candidates for Erdős #7. They check the conditional collision and phase-excess conclusions, p-1 distinct actual suppliers, same-support pair counts and(TS8). For the full selected private union the top-shell pair inequalities are exact:1=1 for p=3 and6=6 for p=5 in the relevant controls. The ordinary proofs use numerical distinctness only to record distinct lower indices at fixed support, so these repeated-label controls legitimately exercise the stronger common-source identities without pretending to witness a distinct odd cover.

Reproduce the controls with:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-top-shadow-shell-pairs/original_top_shadow_shell_pairs.py
```
 These are exact finite controls and ordinary proofs; none is Lean verification or a proof that every unrestricted distinct-odd inventory violates a necessary inequality.

## Source-local phase assignment and a stronger top-shell pair demand

Keep the same original classes, global top-digit decomposition, private regions and uniform probability mu as in(TS1)–(TS8). Fix a prime p and D subset{t:p in T_t}. Everything below is evaluated at the SAME actual x in U_D. The argument uses whole coverage to supply changed top phases; the odd-hyperplane theorem is not used in this refinement. It does not remove omitted-private V or change mu to a supported head law.

### The local incidence data contain more than a number of bins

For each alternative a!=y_p define the available-support set

    N_x(a)={T_s : s covers x^(p,a)}.

Equivalently, retain original labels s with x in E_(s,p,H_p-1), theta_(s,p)=a, and then project to their top support. At a private x these formulations agree: any label covering the changed point must fix the global top p-digit and agree with x on every other coordinate it fixes. No original label or residue may be independently changed between alternatives.

Whole coverage makes every N_x(a) nonempty. If any is empty, x^(p,a) is a literal uncovered residue and is recorded as such; there is no finite assignment cost at that x. In particular an infeasible assignment must NOT be given cost zero and integrated as though it were a whole-cover source.

Let

    sigma_p(x)=|union_(a!=y_p) N_x(a)|.

Replacing global sigma_p in the pointwise balanced-bin argument by sigma_p(x) is a direct localization of(TS8), not a separate substantial theorem. It still discards which alternatives can use which bins.

For a feasible source define

    phi_p(x)=min sum_A binom(n_A,2),

where the minimum ranges over assignments a |-> A_a in N_x(a), and n_A counts alternatives assigned to A. Each alternative is assigned once, not split fractionally. Since there are finitely many actual alternatives and labels, this minimum is attained. It is an ordinary finite convex assignment problem; one can realize it as a min-cost flow using support slots of incremental costs0,1,2,... .

Then

    phi_p(x) >= Pi(p-1,sigma_p(x)) >= Pi(p-1,sigma_p).

There is a stronger subset certificate. For any nonempty set J of alternative phases put N_x(J)=union_(a in J)N_x(a). Then

    phi_p(x) >= Pi(|J|,|N_x(J)|).                       (PA1)

Indeed any legal assignment places the alternatives in J among those bins; their equal-bin pairs are included among all equal-bin pairs. Maximizing(PA1) over J detects bottlenecks that the total local bin count misses. This is the Hall-type content: different phase subsets need not have access to all available bins.

One may also certify a lower bound without finding an optimal assignment. Give each actual support A a nonnegative integer k_A. For every feasible x,

    phi_p(x) >= sum_(a!=y_p) min_(A in N_x(a)) k_A
                         - sum_A k_A(k_A+1)/2.          (PA2)

For every integer occupancy n_A>=0,

    binom(n_A,2) - k_A n_A + k_A(k_A+1)/2
      =(n_A-k_A)(n_A-k_A-1)/2 >=0.

Sum this identity and use k_(A_a)>=min_(A in N_x(a))k_A for each phase. The maximum of zero and the displayed RHS is also a valid lower bound. No exact duality theorem is needed for this certificate. The k_A may be fixed in advance, or represented as explicit functions of x before integration; neither choice changes the original source law.

### Original supplier pairs pay the source-local demand

Choose any minimizing assignment at one feasible x. For each assigned support choose an ORIGINAL label s covering x^(p,a) with that support. Distinct phases force distinct original labels. Two selected labels assigned to the same A have different p-phases and match the same x at every other coordinate in A. Thus their unordered pair belongs to R_p from(TS7), and x lies in both original top p-shells. Different pairs of chosen labels are different original pairs.

Consequently, pointwise,

    phi_p(x) <= sum_((s,t) in R_p)
                   1_(E_(s,p,H_p-1) intersect E_(t,p,H_p-1))(x).

Integrating over the SAME selected private union, assuming whole coverage, gives

    integral_(U_D) phi_p(x) dmu(x)
      <= sum_((s,t) in R_p)
             mu(U_D intersect E_(s,p,H_p-1) intersect E_(t,p,H_p-1))
      <= sum_((s,t) in R_p) ((p-2)/P_(T_s)) c_st.       (PA3)

The final capacities are precisely the original-label CRT capacities from(TS2),(TS7). A source-local minimizer only proves a lower bound on how many actual pairs must be present. It does not choose a new probability measure, redistribute ownership between different actual sources, or choose residues after queries. There is no need to make the same minimizing assignment at different x; the inequality holds at every x against the fixed original pair-incidence sets before integrating.

More generally(PA3) applies to any explicitly selected W subset U_D on which every p-alternative really is covered, with U_D replaced by W. For a noncover with missing phases elsewhere, this is an integral over W ONLY. An assertion about the full U_D is not recovered by dropping infeasible points.

The refinement strengthens the LHS of(TS8); its final unrestricted pair-capacity RHS is unchanged. To contradict a whole cover, one still needs a lower bound on the source mass of actual phase bottlenecks together with a sufficiently small joint original pair budget. Neither arbitrary support diversity nor all common-shadow capacities have been controlled here. This is not a proof of unrestricted odd noncoverage or a head-law lift.

### Six original odd labels realize a strict0/1/3 hierarchy

Use the literal classes

    0 mod135, 1 mod5, 12 mod15, 18 mod45, 14 mod35, 44 mod55.

Their period is L=10395=3^3*5*7*11 and their common lower modulus is N=9. The six displayed residues0,1,12,18,14,44 respectively are private witnesses, so every original class is essential to its represented union; all numerical moduli are odd and distinct. The family is a NONCOVER: exact enumeration finds6856 uncovered residues. No divisor-closure claim is made.

Select target0 mod135, prime p=5, and its actual private point x=0. The four global top supports containing5 are

    {3,5}, {5}, {5,7}, {5,11}.

Thus the original global coefficient is Pi(4,4)=0. The actual changed top5 points and available original suppliers at x=0 are:

|alternative top5 phase|actual modified residue|supplier modulus|available supports|
|---|---|---|---|
|1|8316|5|{5}|
|2|6237|15|{5}|
|3|4158|45|{5}|
|4|2079|35 or55|{5,7} or{5,11}|

The local union has three bins, so merely localizing the count gives Pi(4,3)=1. But phases1,2,3 are ALL forced into the single support{5}. Therefore phi_5(0)=3, attained by assigning phase4 to either other support. The subset J={1,2,3} proves3 directly by(PA1); setting k_{5}=2 and the other support weights to zero proves the same value by(PA2).

This is a strict hierarchy at ONE actual common source:

    global balanced-bin bound0
      < local balanced-bin bound1
      < actual phase-assignment bound3.

The target has77 private points. Exactly17 of them have every alternative top5 phase supplied;60 have a missing phase4 and provide direct uncovered-neighbor witnesses. Among the feasible17 points, one has local-bin bound1 and sixteen have bound2; all have assignment cost3. Under the ORIGINAL uniform probability,

    integral_W Pi(4,sigma_5(x)) dmu=1/315,
    integral_W phi_5(x) dmu=17/3465,
    sum_(R_5)mu(W intersect E_s intersect E_t)=17/3465,
    sum_(R_5)((5-2)/P_(T_s))c_st=1/3.

Here W is explicitly the17 feasible private points, not the full77-point private region. The example witnesses a strict source-local improvement and exact restricted pair accounting; it does NOT violate(PA3), because17/3465<=1/3. The full-private phi integral is left undefined in the data, with all60 missing-phase points listed.

### A feasible zero-cost star marks the remaining scope

Use the actual classes0 mod15015,6 mod15,7 mod35,33 mod55,39 mod65. Their common period is15015=3*5*7*11*13; their moduli are odd and distinct. The first class has the unique private point0. Its four alternative top5 phases are supplied by the other four original classes, whose supports are respectively{3,5},{5,7},{5,11},{5,13}. Thus every phase is supplied on the entire selected private region, yet the local union has four bins and phi_5(0)=0. The original uniform integral and pair-capacity RHS are both zero.

This is a NONCOVER with exactly13080 uncovered residues. For example, modifying0 only in a nonzero top3 phase keeps its top5 phase zero; it leaves the full-period target and belongs to none of the four suppliers, all of which require a nonzero top5 phase. Therefore this control supplies no odd whole cover. It shows that numerical distinctness and complete supply along one selected prime do not themselves force positive-mass Hall cost. The required further input must use full coverage or compatible information from other directions.

The [standard-library program](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-top-phase-assignment/original_top_phase_assignment.py), with [exact data](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-top-phase-assignment/original_top_phase_assignment.json), checks these statements. Reproduce them with:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-top-phase-assignment/original_top_phase_assignment.py
```

The program also checks the actual distinct even L60 whole cover and a complete residue partition modulo25 (repeated moduli), keeping their scopes explicit. These are ordinary proofs and exact finite controls, not Lean verification.

## Arithmetic inventory, phase bottlenecks and actual owner budgets

These ordinary deductions retain one literal original class family, its actual private regions, global top phases and the uniform law on its original period. The quantitative obstruction to unrestricted Erdős #7 remains unproved. The noncovering families below disprove only proposed deductions from expressly weaker hypotheses, not the odd-covering conjecture. No Lean verification is claimed.

### What numerical distinctness actually controls

Fix a global top support A. Put

    M_A=product_(p in A)p^(H_p-1),
    N_A=product_(q outside A)q^(H_q-1).

Every original label with top support A has

    bar_m_s=M_A d_s, d_s divides N_A.

Distinct original moduli give distinct d_s. Hence there are at most product_(q outside A)H_q such labels. In particular a nontrivial same-support collision requires that A omit a prime q with H_q>=2; merely saying A is proper is weaker. If every global exponent is one, no same-support collision is possible, recovering the already cited square-free obstruction through(TS1). This is arithmetic bookkeeping of the original inventory, not a new proof of the public square-free theorem.

An explicit upper bound on the unweighted common-shadow capacity at A is

    sum_(s<t, T_s=T_t=A, theta_s!=theta_t)c_st
      <= 1/(2M_A) * [ product_(q outside A) F(q,H_q)
                           - product_(q outside A) G(q,H_q) ],

where

    F(q,h)=sum_(j=0)^(h-1)(2j+1)/q^j,
    G(q,h)=sum_(j=0)^(h-1)1/q^j.

Proof: c_st<=1/lcm(bar_m_s,bar_m_t), enlarge to every pair of distinct divisors d,e of N_A, count ordered pairs and subtract the diagonal. The double divisor sum factors prime by prime; exactly2j+1 ordered exponent pairs have maximum j. All inequalities retain their upper-bound direction. This bound does not preserve every phase and lower-shadow compatibility and need not be attained.

When all outside heights equal2, the two products contain1+3/q and1+1/q respectively. No uniform constant follows as the outside prime inventory grows. The following actual family shows that this is not solely an artifact of including composite or repeated lower indices.

### Distinct prime lower indices can carry arbitrarily large raw pair capacity

Let Q0,Q1 be disjoint nonempty finite sets of odd primes at least5, Q=Q0 union Q1, and let

    L=3 product_(q in Q)q^2.

For each q in Q0 take the class0 mod3q. For each q in Q1 take the unique residue a_q mod3q with a_q=0 modq and a_q=1 mod3. Also take1 modq^2 for every q in Q. Finally take one target a_* modL with a_*=2 mod3 and a_*=0 modq^2 for every q in Q.

All moduli are odd, greater than one and numerically distinct. The global top supports of the3q classes are all A={3}; their lower indices are the distinct primes q, and their top3 phases are0 or1. The q^2 classes have support{q}; the final target has full top support. For q in Q0 and r in Q1,

    c_qr=1/(qr),

so the actual cross-phase A-capacity is EXACTLY

    sum_(q in Q0,r in Q1)c_qr
      =(sum_(q in Q0)1/q)(sum_(r in Q1)1/r).

Every lower-shadow intersection is from this SAME original uniform source: all lower residues are zero for the3q labels. The familiar divergence of the prime reciprocal sum permits disjoint finite Q0,Q1 making this quantity arbitrarily large. The construction does not combine separately optimized phase configurations.

Every class has an actual private witness. For a3q class choose its stated top3 phase, q^2-coordinate zero, and every other r^2-coordinate2. For a1 modq^2 class choose top3 phase2, its q^2-coordinate1 and every other r^2-coordinate zero. The full-period target is private at a_*. CRT supplies each stated witness, and q>=5 makes the chosen zero,one,two coordinates distinct as needed.

Nevertheless this is a NONCOVER: top3 phase2 with every q^2-coordinate2 is uncovered. Thus oddness, numerical distinctness, irredundancy and the precise lower-index shape do not supply the missing whole-cover premise.

At the target's unique private point a_*, both alternate top3 phases ARE covered: the phase0 suppliers are all original Q0 labels, and the phase1 suppliers are all original Q1 labels. The feasible local assignment has one bin and phi_3(a_*)=1. But there are |Q0||Q1| raw original supplier pairs through that same point. Therefore

    integral_(U_*)phi_3 dmu=1/L,
    sum_(R_3)mu(U_* intersect E_s intersect E_t)=|Q0||Q1|/L.

The ratio of raw restricted pair service to the minimum assignment demand can grow arbitrarily, even with actual p-local coverage on the WHOLE selected private region. This does not preclude a proof using full coverage in all directions, but it rules out controlling that ratio by numerical distinctness and p-local coverage alone.

A small exact instance takes Q0={5,11}, Q1={7}. Its literal classes are

    296450 mod444675,
    0 mod15, 0 mod33, 7 mod21,
    1 mod25, 1 mod49, 1 mod121.

The period is444675. Exact enumeration finds355727 uncovered residues and verifies private witnesses296450,15,33,7,26,50,122 in this order. The target has one private point with phi_3=1, two raw same-support supplier pairs, and full raw pair-capacity RHS16/1155.

### The zero-demand boundary

The feasible zero-cost star in the preceding phase-assignment section already shows that oddness, original numerical distinctness and complete supply in one selected prime do not force positive Hall demand. That control and its evidence are not duplicated here. Full coverage or compatible information from additional directions must provide the missing premise.

### A fixed actual owner partition removes gratuitous supplier multiplicity

Choose a fixed total order of ORIGINAL labels, for example ascending numerical modulus. Define

    O_s=C_s minus union_(r earlier than s)C_r.

These actual owner sets are disjoint and partition the represented covered union. They do not alter any class, residue or source law. For p in T_s let tau_(s,p)x replace only the global top p-digit by theta_(s,p), and put

    F_(s,p)=E_(s,p,H_p-1) intersect tau_(s,p)^(-1)(O_s).

The definition uses the SAME owner partition for all x and all directions. At a selected private x with all p-alternatives covered, each alternative point has exactly one actual owner. Privacy makes that owner a top-p supplier, so exactly one F_(s,p) holds for each alternate phase. Consequently its chosen same-support pairs still pay phi_p(x).

The sharpened capacity bound is

    integral_(U_D)phi_p dmu
      <= sum_((s,t) in R_p)mu(U_D intersect F_(s,p) intersect F_(t,p))
      <= sum_((s,t) in R_p)mu(F_(s,p) intersect F_(t,p))
      <= sum_((s,t) in R_p)((p-2)/P_(T_s))c_st.        (OB1)

The full-U_D form retains the whole-cover premise; the explicitly feasible-subset form is also valid. At an arbitrary source point there are at most p-1 chosen top-p suppliers, hence

    sum_((s,t) in R_p)mu(F_(s,p) intersect F_(t,p))
      <= binom(p-1,2).                                (OB2)

This cap uses disjoint original ownership, not separately minimized pair capacities. It can be much smaller than the raw CRT sum. However the universal cap alone cannot force a contradiction: pointwise phi_p<=binom(p-1,2) too. Further arithmetic control must exploit the actual owner sets or combine compatible demands. The O_s include previous-class exclusions, so their capacities need not have the simple two-class CRT formula; evaluating them has retained, not eliminated, the joint difficulty.

In the Q0,Q1 family, the unique private target chooses just the first original supplier in each phase. Its restricted owner-pair service is1/L, exactly phi demand, instead of |Q0||Q1|/L. In the small period444675 instance, the FULL owner pair budget is74/5775, strictly below the raw16/1155=80/5775. The selected private budget is1/444675 instead of2/444675.

For the reused actual even period60 whole cover, the selected p=5 target1 mod5 has one private point. Ascending-original-modulus ownership reduces the full pair capacity from2/5 to1/10, while its private demand remains1/60. This is an exact capacity improvement in an actual whole cover, not a contradiction and not evidence of an odd cover. The complete repeated-modulus25 partition retains capacity6=binom(4,2), as expected. The [owner-budget program](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-top-joint-owner-budget/original_top_joint_owner_budget.py) and [exact owner data](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-top-joint-owner-budget/original_top_joint_owner_budget.json) check these owner inequalities and literal counts.

### Two-prime directions require one joint supplier rectangle

Let p!=q and select D so every target reaches both global top heights. At the SAME private x choose actual suppliers s_p(a) for every alternate p-phase and s_q(b) for every alternate q-phase. Labels within either direction are distinct. The two label sets are also disjoint: a label that covers a p-change must fix p to a value different from x_p; it therefore cannot cover a q-change, which retains x_p. Thus there are(p-1)(q-1) distinct ordered ORIGINAL cross-direction pairs through x.

For an original p-supplier s and q-supplier t put A=T_s, B=T_t, and let c_st be their original lower-shadow CRT capacity, with no equal-support assumption. The mixed-shell intersection is zero unless

* theta_(s,r)=theta_(t,r) for r in(A intersect B) minus{p,q};
* if p belongs to B, theta_(s,p)!=theta_(t,p);
* if q belongs to A, theta_(s,q)!=theta_(t,q).

When these conditions hold, direct counting in the SAME product source gives

    mu(E_(s,p,H_p-1) intersect E_(t,q,H_q-1))
      =c_st * (p-1)^[p notin B] * (q-1)^[q notin A]
                    /P_(A union B).                    (OB3)

The factors at p and q are one fixed allowed phase when the other label also fixes that coordinate, and respectively p-1 or q-1 allowed phases otherwise. All remaining fixed top coordinates have their common required value. The lower-shadow CRT condition can independently make c_st zero. Identical labels automatically have zero mixed-shell intersection.

Counting cross-direction suppliers before integrating proves

    (p-1)(q-1)u_D
      <= sum_(s:p in T_s, t:q in T_t)
            mu(U_D intersect E_(s,p,H_p-1) intersect E_(t,q,H_q-1))
      <= sum_(s:p in T_s, t:q in T_t) [the capacity in(OB3)]. (OB4)

This is a joint moment consequence of actual pointwise supply, not the product of two averaged inequalities. The same fixed owner partition gives a further valid replacement E by F in the joint demand and its upper bound. One must use that ONE partition for both directions; independently optimizing the two owner laws supplies no common rectangle certificate.

For several demanded primes J, fix ONE selected family D subset intersection_(p in J){t:p in T_t}, and use that SAME U_D for every direction. A single original label cannot be a top-shell supplier in two different directions at the same x: its one-prime defect directions are disjoint. Thus for a fixed unordered original pair{s,t}, the regions

    E_(s,p) intersect E_(t,q), p!=q in J,

are disjoint as the ordered direction pair varies (keep s,t in the fixed label order). Summing their capacities is therefore an actual union budget for that original pair. It does not provide separate capacity copies for separately optimized p,q tests. The sum of demands is sum_(p<q in J)(p-1)(q-1)u_D on one common private union. This describes which original pair/rectangle incidences a multi-direction argument must retain. No quantitative estimate forcing that joint budget below demand has been proved here, and no omitted-private V term is removed from the complete column identities.

### Exact mixed-direction controls

The [mixed-direction program](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-top-mixed-shell-pairs/original_top_mixed_shell_pairs.py), with [exact mixed data](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-top-mixed-shell-pairs/original_top_mixed_shell_pairs.json), checks(OB3) by literal residue enumeration, checks disjoint direction regions for each original unordered label pair, and counts actual joint supplier rectangles using one original owner partition. Under python3 -I -S -B -O it verifies21 formula instances for the six-label odd noncover,38 for the actual even period60 whole cover, and225 for the complete repeated-modulus15 partition. The respective nonzero intersection counts are14,31,120. Noncover private points missing any demanded phase are explicitly counted outside the feasible-region integral; they are never assigned zero demand. These controls do not supply an odd distinct whole cover.

Reproduce the two control sets with:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-top-joint-owner-budget/original_top_joint_owner_budget.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-top-mixed-shell-pairs/original_top_mixed_shell_pairs.py
```

## Actual owner-positive top shadows

Keep the original uniform mu, lower law beta, original congruence classes and global top decomposition X=B×Q. Fix the SAME original-label order and owner partition O_s=C_s minus union_(r earlier than s)C_r used in(OB1)–(OB4). Define the owned lower shadow

    Z_s=projection_B(O_s) subset D_s,
    c^own_st=beta(Z_s intersect Z_t).

These are actual projections of one owner partition. A Z_s need not be one residue class, so replacing its measure by the original two-class CRT capacity is only an upper bound, not an equality.

### Conditional odd-cover refinement

Assume whole coverage and fix any selected top-touching private family D. At a lower source z projected from U_D, the hyperplanes H_s for labels with z in Z_s still cover Q: every actual point(z,y) has an original owner s, and z belongs to that owner's Z_s. All these hyperplanes are proper, because an active empty-support original class would also cover the selected private point.

Apply the same proper-hyperplane odd-prime theorem to this owner-positive cover. It supplies two distinct-phase labels with the same nonempty support and BOTH owned lower shadows containing z. Thus

    U_D subset union_(s<t,T_s=T_t!=empty,theta_s!=theta_t)
                      projection_B^(-1)(Z_s intersect Z_t).

The previous private-region exclusion still applies on every such lower fibre, since the original endpoint hyperplanes each have density1/P_A and a selected private point cannot lie in an unselected endpoint's ORIGINAL class. Consequently

    u_D <= sum_(s<t,T_s=T_t=A!=empty,theta_s!=theta_t)
       [1-(2-1_(s in D)-1_(t in D))/P_A] c^own_st,
    c^own_st <= c_st.                                  (OS1)

This refines TS4 while sharing exactly the owner partition used by the top-shell and mixed-direction budgets. No owner sets or residues are optimized separately between the inequalities. The oddness theorem is used only where stated; a noncover or an even family does not inherit(OS1).

### One owner-positive label per support and phase in each lower fibre

At a fixed z, two active labels with the same support and phase define identical hyperplanes. The later one's entire fibre slice is covered by the earlier original class. Therefore the later label owns no point in that fibre. In particular

    sum_(s:T_s=A,theta_s=theta)1_(Z_s)(z) <=1.

Let K_A^own(z) count owner-positive labels with support A. It counts distinct phases and is at most P_A. Hence

    sum_(s<t,T_s=T_t=A,theta_s!=theta_t)c^own_st
      =integral_B binom(K_A^own(z),2) dbeta(z)
      <=binom(P_A,2).                                  (OS2)

This removes repeated copies of the SAME support-phase hyperplane created by distinct lower indices. It does not make different phase or support events independent. Under original numerical distinctness, the stronger arithmetic inventory bound still applies: nontrivial same-support pairs require an omitted prime with global exponent at least2.

Under the original uniform law, nonempty owner fibres contain at least one top cell and at most the original hyperplane's R/P_A cells. Thus

    P_A mu(O_s) <= beta(Z_s) <= R mu(O_s), R=|Q|.

The upper factor R can be large, so this alone gives no adequate bound for(OS1). A source-local pair appearing in(OS1) may differ in several top coordinates; owned positivity does not make it a one-prime shell pair at the selected private point. The exact mixed-direction incidence requirements and the omitted-private V term remain necessary where applicable.

### A tempting owner-mass cap is insufficient by itself

For a fixed p, the exact owner transport gives

    mu(F_(s,p))=(p-1)mu(O_s), p in T_s.

Each owned point of s has exactly p-1 preimages obtained by changing its top p-digit, all in E_(s,p). At any point of F_(s,p), at most p-2 other chosen p-suppliers can form same-support pairs with s. Summing incident pair capacities and dividing by two gives

    sum_((s,t) in R_p)mu(F_(s,p) intersect F_(t,p))
      <= binom(p-1,2) Omega_p,
    Omega_p=sum_(s:p in T_s)mu(O_s).                    (OS3)

This can be strictly smaller than the earlier absolute cap when Omega_p<1. However it CANNOT on its own violate the assignment demand: pointwise phi_p<=binom(p-1,2), and for selected D with every target reaching p one has u_D<=Omega_p. Thus

    integral_(U_D)phi_p dmu <=binom(p-1,2)u_D
                            <=binom(p-1,2)Omega_p

without any new covering argument. A strict improvement of this numerical ceiling is not a contradiction. An effective next bound must preserve which support or original owner is forced to supply which private region, or connect(OS1) to the SAME cross-direction owner budgets. No estimate forcing the required strict demand/capacity gap from unrestricted oddness and whole coverage has been established here.

These are ordinary conditional deductions, not Lean verification. They do not establish the unrestricted joint demand/capacity gap.

The [exact producer](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-owned-top-shadows/original_owned_top_shadows.py) and [data](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-owned-top-shadows/original_owned_top_shadows.json) use the seven-label odd distinct noncover above and the complete repeated-modulus15 cover. On the former, the raw same-support{3} shadow pair sum16/385 drops to the owned sum3/77. With ascending-modulus ownership, the labels0 mod15,0 mod33,7 mod21 have Z33=D33 minus D15, removing exactly1/385 from that sum. OS1 is NOT applied to this noncover. Its owner-shell capacity remains74/5775, from the same actual partition. On the repeated15 cover, OS2 gives105 and OS3 gives1 for p=3 and6 for p=5, equal to their bounds. This whole-cover control deliberately repeats numerical moduli and is not an Erdős #7 candidate.

Reproduce with:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original-owned-top-shadows/original_owned_top_shadows.py
```

## Private shell saturation leaves an overlap-separator obligation

The odd-DISTINCT case is not resolved here: no actual counterexample or general converse theorem has been established. The repository's existing private-point fan and shell results prove necessity under whole coverage, not sufficiency. There is, however, an explicit all-odd irredundant NONCOVER satisfying every private shell requirement once numerical moduli may repeat. Its construction below uses nineteen Boolean patterns and works for any five distinct odd primes. Thus the local condition is not equivalent to whole coverage for arbitrary original AP families; numerical distinctness is an essential remaining hypothesis in the precise question.

### 1. Exact predicate and a separator characterization

Let the finite original AP family have period

    L=product_p p^H_p,
    X=product_p Z/p^H_p,
    c(x)=number of original classes containing x.

Write H={c=0}, P={c=1}, and M={c>=2}. A private point x in P has a unique original owner t.

The STRONG all-depth shell predicate used here is:

    for every x in P and every p dividing m_t,
    every point with the same non-p CRT coordinates as x is covered.   (PS1)

This is an actual incidence requirement, not a weighted count. In target-owner prefix language, it requires coverage of all changes whose first p-adic disagreement with x is at any r<v_p(m_t), with every subsequent p-digit allowed. The p-coordinate values with unchanged owner prefix already lie in the owner class. If p does not divide m_t, its entire p-line also stays inside that class. Therefore (PS1) is exactly the assertion that every complete prime-coordinate line through EVERY private point is covered.

Define the Cartesian graph Gamma on X: two distinct points are adjacent when they differ in just one entire prime-power CRT coordinate. Then

    (PS1)  iff  no edge of Gamma joins P to H.                          (PS2)

Equivalently, every covered vertex adjacent to a hole has multiplicity at least two. This proof does not use oddness or distinctness: an edge to H cannot change a coordinate omitted by the private owner's modulus, and the remaining edges are precisely those required by PS1.

Consequently each connected component of the induced graph Gamma[X minus M] lies wholly in P or wholly in H. If the family is nonempty and irredundant, P is nonempty. If in addition Gamma[X minus M] is connected, PS1 forces H to be empty. In particular, PS1 implies whole coverage for a nonempty pairwise-disjoint family: then M is empty and the full Cartesian graph is connected.

For overlapping families this proof leaves a concrete gap: the overlap region M can separate the private region from the holes. To turn private shell saturation into a global theorem, one must control that SAME actual overlap separator using the original arithmetic. Individual private-row counts do not supply this control.

There is a weaker interpretation in which just one p-digit is changed and all other digits are held fixed. Its graph is the product of one K_p for each individual digit. The same no-P-to-H-edge characterization applies in that graph, but the weaker predicate need not be iterated through an intermediate overlap point, since that point is not private. The counterexample below is squarefree, so the two predicates coincide there and no such distinction is used to weaken the control.

### 2. A nineteen-pattern construction

Use five Boolean coordinates. A star is free, and a displayed 0 or 1 fixes that coordinate. The following family covers every Boolean word except 00000. Each row has exactly the private word displayed in the second column:

|pattern|its unique private Boolean word|
|---|---|
|`**001`|`11001`|
|`**010`|`11010`|
|`*0*10`|`10110`|
|`*0101`|`10101`|
|`0*1*0`|`01110`|
|`000*1`|`00011`|
|`001**`|`00111`|
|`01*0*`|`01101`|
|`010**`|`01011`|
|`01111`|`01111`|
|`10*00`|`10100`|
|`100**`|`10011`|
|`10111`|`10111`|
|`11000`|`11000`|
|`11011`|`11011`|
|`11100`|`11100`|
|`11101`|`11101`|
|`11110`|`11110`|
|`11111`|`11111`|

These are a finite truth-table certificate: the nineteen private words and the twelve multiply covered words exhaust all thirty-one nonzero words. Every weight-one word is multiply covered. Every private word has weight at least two, so changing any single coordinate cannot give 00000. Therefore EVERY neighbor of EVERY private word is covered, while 00000 is not covered.

This displays the separator in PS2: the hole's five neighbors all lie in M. The private region exists beyond that overlap boundary. The nineteen-pattern assertion can be checked directly on all thirty-two words; it does not rely on a SAT verdict.

### 3. Actual odd congruence classes, with their real private points

Choose any five distinct odd primes p_1,...,p_5 and L=product_i p_i. For an actual residue x define

    beta_i(x)=0 if x=0 mod p_i, and 1 otherwise.

For every pattern w, expand it into the following literal original APs. For every fixed zero coordinate, choose residue zero. For every fixed one coordinate, independently choose one actual nonzero residue r_i in {1,...,p_i-1}. The star coordinates impose no condition. CRT gives one original AP for each resulting choice:

    m_w=product_(i:w_i!=*) p_i,
    a_(w,r)=the CRT residue with those fixed coordinate values.       (PS3)

There are no identical AP copies: a full point determines at most one residue choice within each pattern, and different patterns with the same fixed support disagree on a zero/nonzero condition. Numerical moduli nevertheless REPEAT, both from nonzero-phase expansion and from patterns with the same support.

The exact multiplicity identity is

    c_actual(x)=number of Boolean patterns containing beta(x).       (PS4)

Indeed, a pattern containing beta(x) has exactly one expanded AP containing x, using x's actual nonzero residues; a pattern not containing beta(x) has none. Hence the ONLY actual uncovered residue is x=0 mod L.

Each expanded AP has an actual private point. Take its pattern's private Boolean word from the table, retain the AP's fixed residue choices, and choose zero or any nonzero residue in its free coordinates according to that word. CRT realizes all choices simultaneously. Identity PS4 then gives multiplicity exactly one. This proves irredundancy of EVERY expanded class, rather than just the existence of one private point per pattern.

Now start at any actual private point. Its Boolean image is a private word. Changing one prime coordinate either preserves that Boolean image or changes one Boolean bit. In the former case the actual point remains covered by PS4. In the latter the changed Boolean word is a covered neighbor from the preceding section, so PS4 again gives actual coverage. Therefore EVERY point on EVERY complete prime line through EVERY actual private point is covered. The phase changes are simultaneous properties of one fixed family; neither residues nor suppliers are chosen anew to satisfy a separate optimization.

This proves an explicit infinite structural family of finite odd irredundant noncovers satisfying PS1. It does NOT give distinct-modulus examples. Selecting just one residue from each repeated-modulus group does not preserve PS4 or PS1 and is not an admissible repair.

### 4. Compact exact control and remaining scope

At primes (3,5,7,11,13), L=15015. The expansion has 12292 actual APs on nine distinct numerical moduli. Their multiplicities by numerical modulus are

    105:12, 165:4, 273:6, 715:10, 1001:22,
    1365:12, 2145:2, 5005:72, 15015:12152.

Literal AP progression enumeration gives exactly one uncovered residue, 14692 private residues, and 322 overlap residues. Every expanded AP has a private point. The control verifies all 15015 pointwise multiplicities against PS4 and 572988 actual private-prime-line membership assertions. Its output keeps the nineteen pattern rows and compact counts, not a 12292-row class table.

The [compact producer](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/private-shell-saturation-odd-lift/private_shell_saturation_odd_lift.py) and [exact data](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/private-shell-saturation-odd-lift/private_shell_saturation_odd_lift.json) are reproduced by:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/private-shell-saturation-odd-lift/private_shell_saturation_odd_lift.py
```

The program uses only the standard library; its checks remain active under -O. These are ordinary finite calculations and a general CRT proof, not Lean verification.

The preceding original shell and owner budgets impose necessary demands under whole coverage. The odd-distinct noncover controls above have missing private phase neighbors, as does the outside-prime construction in [Report450](../../docs/reports/erdos7-odd-covering/profile-notes/arithmetic/450-499/450-weighted-original-depths-and-the-uniform-lift-boundary.md). Thus neither supplies the all-private, all-prime property proved for this repeated-modulus family. The five-coordinate construction is not claimed minimal.

Thus the remaining precise alternatives are still unresolved: either find an actual odd-DISTINCT PS1 noncover, or prove that numerical distinctness prevents an overlap separator between nonempty private and uncovered regions. The latter would make PS1 sufficient for whole coverage in that class, hence equivalent to whole coverage there; it would not by itself exclude odd distinct whole covers. A separate proof that no nonempty irredundant odd-distinct family can satisfy PS1 would imply the desired noncoverage theorem. These are different obligations and must not be conflated.

## Arbitrary quotient cuts collapse to the same depth suffixes

The following identities locate exactly what changes when the published
private-point inequality is applied after an arbitrary divisor cut. They
retain all original labels, residues and heights. They are ordinary
research-interface deductions, not a new attributed theorem or Lean
verification. The all-depth rows and their joint capacity accounting above
remain the existing interface.

Let the finite original classes be `C_j=a_j mod m_j`, let Q be their full
period, and let x be an actual private point with unique original owner t.
For this identity the family need not cover, be odd, or have distinct
moduli. Write c(y) for its actual covering multiplicity. Fix a prime p
of Q and put `H=v_p(Q)`, `e=v_p(m_t)`.

For any divisor L of Q, set `ell=v_p(L)`, `g_j=gcd(m_j,L)` and
`r_j=m_j/g_j`. On the actual fibre through x, write `z=x mod L` and
`u=(x-z)/L`. Original j is active exactly when `g_j | a_j-x`; its trace
has phase

    theta_j=((a_j-z)/g_j)*(L/g_j)^(-1) mod r_j.

When the original family is a whole cover this is a quotient cover,
possibly with repeated residual moduli, and u is private to t. The
published inequality applies for every prime; its right side is positive
precisely when `ell<e`, equivalently `p|r_t`.

### Labelwise cancellation of the other cut coordinates

Put `h_j=v_p(m_j)`. A quotient p-direction term occurs precisely when

    m_j/p^h_j | a_j-x,
    ell <= b_j:=v_p(a_j-x) < h_j.                    (QC1)

Indeed, at every prime different from p, activity supplies agreement up
to the cut depth and the quotient prime-free condition supplies all
remaining agreement. Together these are exactly agreement at the full
original prime-free modulus. At p, activity requires agreement to ell,
while the quotient mismatch requires failure before h_j. Consequently

    v_p(r_j)=h_j-ell,
    v_p(theta_j-u)=b_j-ell,
    p^(-(v_p(r_j)-v_p(theta_j-u)-1))=p^(1-h_j+b_j).

The valuations used here are strictly below their respective modulus
heights and are independent of the chosen integer representatives.
In particular, valuation at zero never occurs in a directional term.

Define the original shell service

    F_b(x,p)=sum_(j: m_j/p^h_j | a_j-x,
                    v_p(a_j-x)=b<h_j) p^(1-h_j+b),
    S_ell(x,p)=sum_(b=ell)^(H-1) F_b(x,p).

The entire quotient left side is EXACTLY S_ell. Thus the same original
private point of a WHOLE COVER gives

    S_ell(x,p)>=(e-ell)(p-1),   0<=ell<e,             (QC2)

and all other prime coordinates of L have disappeared. This is not a
replacement of actual phases by optimized phases. It is a term-by-term
identity for each original label. At ell>=e the theorem's right side
is zero; its inequality is simply S_ell>=0, also immediate from the
definition without coverage.

### The precise overlap-minus-hole identity

Let B_b(x,p), 0<=b<H, be the complete set of points agreeing with x at
all non-p coordinates and first disagreeing at p-depth b. Each such
shell has `(p-1)p^(H-b-1)` points. All averages below use its actual
uniform probability.

Owner t covers the entire shell exactly when b>=e. Every other class
meeting the line is in exactly one shell b_j; when b_j=b, its proportion
of B_b is `p^(1-h_j+b)/(p-1)`. Classes containing x other than t do not
exist. Hence

    F_b=(p-1)*(Avg_(B_b)c-1_(b>=e)).

Summing yields the identity, valid even for noncovers,

    S_ell-(e-ell)_+(p-1)
      =(p-1)*sum_(b=ell)^(H-1) Avg_(B_b)(c-1),
      0<=ell<=H.                                    (QC3)

For ell=H both sides are zero. Under whole coverage each summand is
nonnegative. On a noncover, overlap excess in one shell can pay for a
hole deficit in another shell within this scalar expression.

In particular, any nonnegative combination of these inequalities over
actual private points, primes and cuts has slack of the form

    sum_(y mod Q) K(y)*(c(y)-1),   K(y)>=0,           (QC4)

where K is the sum of the explicitly weighted uniform shell indicators.
The multiplicity is that of the SAME original family throughout. Such
aggregation requires an additional arithmetic bound on this common
weighted overlap if it is to give a contradiction; it cannot assign a
fresh capacity to each appearance of one supplier. The preceding
complete columns, omitted-private term, and reserve bounds address that
shared-budget issue and are not new consequences of changing L.

### Exactly which depth weights positive combinations can generate

For a fixed x,p with e>0, assign nonnegative coefficients w_ell to the
positive-demand rows ell=0,...,e-1, after combining cuts with equal p-depth. Their
combined slack is

    (p-1)*sum_(b=0)^(H-1) K_b Avg_(B_b)(c-1),
    K_b=sum_(ell=0)^min(b,e-1) w_ell.                (QC5)

Thus K_b is nonnegative and nondecreasing up to depth e-1, then
constant. Conversely every such weight sequence is obtained by
`w_0=K_0`, `w_ell=K_ell-K_(ell-1)`. This is the exact cone for the positive-demand
private-point rows; adding zero-demand rows is not included in this cone. Taking differences of two LOWER bounds is not an
admissible way to extract a single-shell lower bound.

### Two distinct-odd noncovers separate the three levels

First take

    0 mod9, 10 mod15, 7 mod21, 22 mod33, 13 mod39.

The displayed residues themselves are private witnesses, the moduli are
distinct and odd, and integer2 is uncovered. At x=0, p=3, H=e=2,
the shell services are `(4,0)`. The uncut inequality is satisfied with
equality, `4>=4`, but the ell=1 inequality fails, `0<2`. Thus the
suffix family really retains information lost by the one uncut sum.

Next take

    1 mod3, 0 mod9, 30 mod45, 21 mod63, 33 mod99.

Its period is3465. Its five displayed residues are private witnesses;
all numerical moduli are distinct and odd, and every comparable pair
of original classes is disjoint. Integer2 remains uncovered. At the
SINGLE private point x=0 and prime p=3, H=e=2. The first shell has
mean multiplicity1/2: the root1 branch is covered and the root2 branch
is missed. The second shell consists of roots3 and6 with multiplicities
2 and1, giving mean3/2. Therefore

    (F_0,F_1)=(1,3),
    S_0=4=2(p-1),   S_1=3>p-1.

Every divisor cut at this x,p passes its valid suffix inequality, yet
this complete p-line has holes. By QC5 every nonnegative combination
also passes. This does not assert the inequalities at every private
point, divisor closure, global minimality, or an odd covering example.
It rules out reconstructing shellwise coverage from all these scalar
cuts at one source.

The stronger private-line coverage condition PS1 above retains actual
incidence. Neither the cutoff sums nor the scalar shell averages are a
substitute for that condition. This distinction does not by itself
settle the original odd-distinct noncoverage problem.

### Arbitrary heights retain divisor closure and normalized prime classes

There is a second, different loss of information: even every shell mean
can reach its demand while individual branches remain uncovered. This
happens at one specified private point in a divisor-closed family at
arbitrary height.

Choose an odd prime p, an integer e>=2, and p-1 pairwise distinct odd
primes q_j different from p. Take the original numerical inventory

    D={p^k:1<=k<=e} union {p^r q_j:0<=r<=e}.

Its e+(p-1)(e+1) labels are distinct and divisor-closed above one. Set
its phases, using CRT for the mixed classes, as follows:

| Original label | p-adic condition | q_j condition |
|---|---|---|
| p^k, k<e | x=p^(k-1) mod p^k | none |
| p^e | x=0 mod p^e | none |
| q_j | none | x=1 mod q_j |
| p^r q_j, 1<=r<e | x=2p^(r-1) mod p^r | x=0 mod q_j |
| p^e q_j | x=p^(e-1) mod p^e | x=0 mod q_j |

All comparable original classes are disjoint. Nonzero displayed prefixes at different
heights have different first nonzero depths. At equal
heights r<e, the pure and mixed digit values are1 and2; at height e
they are0 and1. Each q_j-prime class has q_j-root1, disjoint from its
mixed descendants with q_j-root0. These exhaust the comparable pairs.

Every class has a private witness on Q=p^e product_j q_j. For a pure
p-class choose its displayed p-coordinate and put all q-coordinates2.
For a mixed class with q_j choose its displayed p-coordinate, put
q_j=0 and all other q-coordinates2. For the q_j-prime class choose
p-coordinate2p^(e-1), put q_j=1 and all other q-coordinates2. The
first nonzero p-depth and these actual cofactor roots exclude every
other original. Thus the family is irredundant.

At x=0 exactly p^e occurs. Freeze all q-coordinates to0. In shell
b<e-1, digit1 is covered once by the pure original; digit2 is covered
p-1 times by the mixed originals, and all other next digits are missed.
In shell e-1, only digit1 is covered, with multiplicity p-1; the other
p-2 branches are empty. Therefore

    Avg_(B_b)c=p/(p-1),  b<e-1,
    Avg_(B_(e-1))c=1,
    F_b=p,              b<e-1,
    F_(e-1)=p-1.

Every positive-demand suffix has slack

    S_ell-(e-ell)(p-1)=e-1-ell>=0, 0<=ell<e.

Yet the point with p-coordinate2p^(e-1) and all q-coordinates0 is a
hole on this same line. Even all individual shell means are sufficient
here for the scalar inequalities but insufficient for actual coverage.
A global translation by -1 normalizes every original prime class to
zero and moves the displayed private point to -1; all properties remain.

This is specifically a ONE-POINT, ONE-PRIME control. It does not satisfy
the private inequalities throughout the family. At the q_j-prime
private witness given above, no other original can meet its q_j-line:
the other q-prime roots are2, and the p-coordinate2p^(e-1) misses every
pure and mixed p-prefix. Its q_j-directional sum is0, strictly below
q_j-1. Thus it supplies no counterexample to the full system of
whole-cover necessary conditions.

### Fixed arithmetic controls

The accompanying standard-library verifier computes quotient traces
using modular inverses and independently computes the original shell
sums and full prime-line multiplicities. It checks every divisor cut
at the selected actual private points in three literal whole covers,
the two five-class noncovers, and normalized members of the general
family at p=3,e=2 and p=3,e=3 with q_j=5,7. No candidate search runs.

The whole covers have periods12,48,135, include original heights four
at2 and three at3, and have other prime components in their cuts. They
are even or have repeated moduli. The normalized controls have periods
315 and945, respectively8 and11 originals,84 and219 holes, and minimum
private-region size3. Their literal phases, private witnesses and
failed q_j-directions are retained in the output.

There are46048 labelwise quotient equalities and5476 shell-slack
identities at206 checked private points. Positive, zero and negative
slacks occur in the controls. The results are finite verification of
the identities' implementation; the general arguments are QC1--QC5
and the arbitrary-height construction above. No Lean result or
unrestricted odd-covering conclusion is claimed.

The [self-contained producer](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/quotient-private-shells/quotient_private_shells.py) and [exact output](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/quotient-private-shells/quotient_private_shells.json) retain the fixed controls. Reproduce with:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/quotient-private-shells/quotient_private_shells.py --output /tmp/e7_quotient_private_shells.json
```

## Prime normalization and all-private scalar cuts do not force line coverage

There is an explicit finite irredundant odd NONCOVER containing every
original prime class `0 mod p` for its support, satisfying the numerical
Lettl–Sun directional inequality at EVERY actual private point, for EVERY
prime and EVERY divisor cut. Numerical moduli repeat. Thus this is not a
distinct-odd example and not an application of the published theorem's
whole-cover premise. It separates simultaneous scalar inequalities from
actual private-line coverage even when the pure-prime reset applies.
The earlier PS1 noncover already satisfies all these scalar conditions.
The new distinction here is the presence of every normalized prime
class together with a failure of PS1 itself.

### One original family from the nineteen Boolean patterns

Reuse the nineteen patterns in the preceding private-shell construction.
Their complete32-word truth table has these properties:

* `00000` is the only uncovered Boolean word;
* each of the nineteen patterns has a private Boolean word;
* every private Boolean word has weight at least two;
* each of the five weight-one words has multiplicity exactly two.

Fix any five pairwise distinct odd primes `p_1,...,p_5`, and let
`Q=product_i p_i`. Add the five literal prime classes

    P_i = 0 mod p_i.

For every Boolean pattern w, expand its fixed coordinates as follows:

    fixed 0: actual residue1 mod p_i;
    fixed 1: independently choose r_i in {2,...,p_i-1};
    star: no condition, including no restriction against residue0.

Each choice produces one literal original AP by CRT, with modulus
`m_w=product_(i:w_i!=*) p_i`. Retain all these original labels. They are
odd, squarefree and greater than one. No two APs are identical, although
many have the SAME numerical modulus.

At a point with every coordinate nonzero, set
`beta_i(x)=0` for residue1 and `beta_i(x)=1` for residues2 through p_i-1.
Its actual mixed-class multiplicity is exactly the number of Boolean
patterns containing beta(x): exactly one phase choice of each matching
pattern contains x. Points with any zero coordinate are covered by at
least one P_i. Hence the unique actual hole is

    h=1 mod Q.                                           (AP1)

Every expanded mixed class has a genuine private point. Take its
pattern's private Boolean word, retain the class's fixed actual phases,
and choose actual1 or2 at every free coordinate according to that word.
All coordinates are nonzero, so no P_i is present, and the Boolean
multiplicity identity gives exactly one mixed owner. Each P_i is private
at the point x_i with coordinate i equal0 and every other coordinate
equal1. A mixed pattern fixing i cannot contain x_i; a pattern free at i
would otherwise contain the forbidden Boolean word00000. Thus the whole
original family is irredundant. In particular, comparable numerical
moduli carry disjoint classes, as follows for any irredundant AP family.

### All actual private points and all directions

Write c for the multiplicity of this one fixed family. Since h is the
only hole, any prime-coordinate line not containing h is fully covered.
The complete p_i-line through h has the exact multiplicity profile

    p_i-coordinate: 0, 1, 2, ..., p_i-1;
    multiplicity:  1, 0, 2, ..., 2.                     (AP2)

The first value is the private prime point x_i. The second is h. Every
remaining value corresponds to the weight-one Boolean word at coordinate
i, whose multiplicity is exactly two. There are no other prime classes
on this line. Thus x_i is its ONLY private point.

For any actual private point x with owner t and any p dividing Q, the
squarefree directional sum has an exact elementary form. If p divides
m_t, then no p-free label meets the p-line through x, and each active
p-bearing label meets it at one point. Since x has exactly one owner,

    LS_p(x)=sum_(y on the complete p-line through x)c(y)-1.  (AP3)

A fully covered line gives `LS_p(x)>=p-1`. A line containing h has only
the private source x_i described in AP2, for which

    LS_(p_i)(x_i)=2(p_i-2)>=p_i-1,                      (AP4)

because p_i>=3. Therefore every positive-demand directional inequality
holds at EVERY actual private point, not just one listed witness per
class.

If p does not divide the owner's modulus, the required right side is
zero and the directional sum is nonnegative. More explicitly, for
p|Q the unique p-free owner contributes p to its complete line, so the
sum is `sum_line c-p>=0`. If p does not divide Q, the directional index
set is empty and both sides are zero. This handles every prime.

Since Q is squarefree, for any divisor cut L each p-depth ell is0 or1.
The labelwise quotient identity QC1 identifies its directional left side
with the same original depth suffix. If p divides m_t and p does not
divide L, this is precisely AP3 with demand p-1. If p divides L,
ell=1=H and the directional suffix is exactly zero, as is the target
demand. If p does not divide L and does not divide the owner modulus,
ell=0 retains its nonnegative zero-demand original row. Thus ALL
divisor-cut inequalities hold simultaneously at
ALL original private points, with one unchanged family and its actual
phases. No fibre-dependent optimization is used.

Nevertheless PS1 fails at each of the five x_i: changing its p_i-coordinate
from0 to1 reaches the actual hole h. There are exactly five private-to-hole
prime-line incidences. This is consistent with
[Report450(PR3)](../../docs/reports/erdos7-odd-covering/profile-notes/arithmetic/450-499/450-weighted-original-depths-and-the-uniform-lift-boundary.md): PS1 would
imply whole coverage in a family containing an original prime, but the
scalar inequalities do not supply PS1.

### Complete finite arithmetic control

At primes `(3,5,7,11,13)`, Q=15015. Literal AP expansion and progression
enumeration give4198 original classes on14 numerical moduli,11307 actual
private residues,3707 overlap residues, and the single hole1. Every one
of the4198 classes has a private residue. The multiplicities by numerical
modulus are

    3:1, 5:1, 7:1, 11:1, 13:1,
    105:9, 165:3, 273:5, 715:9, 1001:20,
    1365:11, 2145:1, 5005:55, 15015:4080.

The [standard-library consumer](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/private-shell-saturation-odd-lift/all_private_scalar_prime_lift.py),
with its [exact result](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/private-shell-saturation-odd-lift/all_private_scalar_prime_lift.json),
reconstructs the literal classes and their
complete multiplicity function. It checks the Boolean identity at all
5760 all-nonzero coordinate points and all56535 private-point/support-prime
rows:30696 positive-demand rows and25839 zero-demand rows. All pass.
The five failures of the stronger PS1 incidence requirement are:

|p|actual private point|owner modulus|directional service|demand|
|---:|---:|---:|---:|---:|
|3|10011|3|2|2|
|5|9010|5|6|4|
|7|4291|7|10|6|
|11|13651|11|18|10|
|13|8086|13|22|12|

Every displayed point has all other prime coordinates1, and all five
lines reach the SAME hole1. Squarefreeness and QC1 justify the complete
cut family; the program does not substitute sampled cuts for that argument.
The standalone consumer requires an explicit output path and optionally
accepts any five distinct odd primes:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/private-shell-saturation-odd-lift/all_private_scalar_prime_lift.py --output /tmp/e7_all_private_scalar_prime_lift.json
```

Normal and optimized runs have identical default output bytes. An
independent reconstruction by successive CRT joins directly evaluates
the original directional predicates and agrees on all56535 rows; it
does not use AP3 to compute them. These finite controls do not replace
the arbitrary-prime construction proof.
These are ordinary exact finite calculations and a general CRT proof,
not Lean verification or a literature-priority claim.

### The numerical-distinctness obligation remains

This construction is not a distinct-modulus lift of the nineteen-pattern
family. It retains all phase copies needed for the multiplicity identity
and for the two suppliers on every nonzero weight-one branch. Its
numerical inventory is NOT divisor-closed: in the displayed control,
15 is absent although it divides the present modulus105. Thus this
family must not be combined with the distinct, divisor-closed463-family
obstruction as though one actual family satisfied both sets of hypotheses.

Merely keeping one original AP per numerical modulus, while retaining
the normalized prime classes, cannot repair this example. In the displayed
inventory, only eight numerical moduli contain13. At the retained private
point of the prime13 class, at most seven other original labels can
contribute to its directional sum, below the required12. Deleting other
classes leaves that original private point private. Thus the straightforward
thinning fails even the uncut inequality. More generally, the numbers
of numerical support types containing each coordinate are7,8,7,7,8,
including its prime class. The largest of five distinct odd primes is
at least13 and belongs to at most eight types, giving the same
obstruction regardless of the order assigned to the prime coordinates.

The simultaneous inequalities have therefore not supplied a sufficient
condition for line coverage in this repeated-modulus class. Whether
numerical distinctness together with the actual arithmetic constraints
of a hypothetical minimal odd cover closes this gap remains unresolved.
The example does not settle that stronger question.
