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

## Complete prime-coordinate averages identify distinct original labels

The following is an ordinary finite Fourier and arithmetic argument, not
Lean verification or a literature-priority claim. It uses the
primitive-character isolation mechanism of
[Report336](../../docs/reports/erdos7-odd-covering/profile-notes/321-384/336-maximal-label-fourier-overlap-and-uncovered-density.md)
and adds reduction in characteristic p and exact height-by-height
subtraction. Its conclusion concerns complete, exactly valued marginal
functions of one fixed original family. It does not turn scalar
Lettl–Sun inequalities into a proof of unrestricted odd noncoverage.

The layer-uniqueness statement is established prior work: Zhi-Wei Sun,
*On the range of a covering function*, Theorem 1.2,
[J. Number Theory 111 (2005), 190–196](https://doi.org/10.1016/j.jnt.2004.11.004),
[final preprint, arXiv math/0409279v2, p. 3](https://arxiv.org/pdf/math/0409279v2).
It states that two systems, each with distinct numerical moduli, are
identical if their multiplicity functions agree modulo an integer that
does not divide their joint least common multiple. For the layers below,
take that integer to be p: their moduli divide B and p does not divide B.
Positive moduli in the source include 1. Empty or singleton layers can
be handled by adding to BOTH systems the same two classes
0 mod(pB+1) and 0 mod(2pB+1), applying Sun's theorem, then removing them.
These two new numerical labels exceed B, are distinct and prime to p,
so each enlarged system still satisfies the source hypotheses. The
height-by-height reconstruction is consequently a short application
of this existing theorem. The finite-field calculation retained below
also specifies the coefficients used by the recognition procedure;
it is not a new uniqueness theorem or a new Lean formalization.

### Complete marginal and original-label reconstruction

Let A and A' be finite families of literal congruence classes, each
containing at most one class at every positive numerical modulus. Their inventories
may differ. Fix a common period Q divisible by every modulus in BOTH
families. For a prime p write Q=p^H B, with gcd(p,B)=1, and use the actual
CRT coordinates (u,y) in Z/(p^H) times Z/B. Let c_A be the multiplicity
function of A. Define

    M_p^A(y) = p^(-H) sum_(u mod p^H) c_A(u,y)
             = sum_(d=p^e m present in A) p^(-e) 1_(y=a_d mod m),
    L_p^A(y) = p^H M_p^A(y).                            (MR1)

Every m divides B; the second equality follows by counting the p^(H-e)
values of u meeting the original p-condition. The complete function
retains the label y of each cofactor residue and its exact rational
value. A histogram of values, a sampled subset of cofactors, a total
mean or only lower bounds on M_p are different observations.

If M_p^A=M_p^(A') pointwise, then the two numerical inventories are equal,
and for every original modulus d=p^e m their phases agree modulo m.
A single p-average does not recover the phase modulo p^e: the distinct
classes 0 mod p and 1 mod p have the same constant average 1/p.

Here is the finite-field uniqueness needed for the proof. Let p not
divide B, and let C,C' be families of classes at divisors of B with at
most one class per numerical modulus. Modulus 1 is allowed. If their
multiplicity functions agree pointwise modulo p, then C=C'. Choose a
finite field K of characteristic p containing a primitive B-th root
omega. For B>1 such a field exists because B divides p^f-1 for some f;
for B=1 use the prime field and omega=1. Suppose the families differ,
and select an m maximal under divisibility among their differing
numerical moduli. Absence is one possible difference. Set
eta=omega^(B/m), of exact order m. For an original class a mod n,

    sum_(y mod B) 1_(y=a mod n) eta^(-y)
      = 0                         if m does not divide n,
      = (B/n) eta^(-a)             if m divides n.       (MR2)

This is the finite geometric-sum identity. Every strict multiple of m
has identical data in C,C', so its difference cancels. The only remaining
contribution is either a signed nonzero root times B/m, or

    (B/m)(eta^(-a)-eta^(-a')).

The scalar B/m is nonzero in characteristic p. Distinct residues modulo
m give distinct roots because eta has exact order m. Thus this
coefficient cannot vanish, a contradiction. For m=1 the only possible
difference is presence versus absence; the constant character gives
the same nonzero contradiction. This proves the finite-field claim.

Now multiply the hypothesized equality in MR1 by p^H and reduce modulo
p. All terms of height e<H vanish. The surviving terms are the
multiplicity functions of the cofactor classes belonging to originals
of height H. There is at most one such class for each m: two would have
the same original numerical modulus p^H m. The finite-field claim
recovers this entire height, including absent labels and all p-free
phases. Its two exact rational contributions to M_p therefore coincide;
subtract them over the rationals, and repeat at height H-1. Continuing
to height 0 proves the reconstruction assertion. This exact subtraction
is essential: merely retaining congruence information would not justify
ignoring carries between heights. Pure p-power labels have m=1, so their
presence is recovered while their p-phase remains unobserved.

The argument also gives a finite recognition and reconstruction procedure
from the full integer table L_p, p, H and a field K with the stated root.
At each height, process m dividing B in decreasing numerical order in
the current table reduced modulo p. Subtract each already recovered
larger-modulus indicator. Its next coefficient in MR2 must be 0 or
(B/m)eta^(-a) for exactly one a modulo m, specifying absence or the
unique phase. Reject any other coefficient. After all m, check that the
ENTIRE residual function on Z/B is zero; checking just one coefficient
per conductor does not replace this step. Subtract the recovered layer's
actual integer multiplicity from the integer table, divide by p, and
continue. After height 0 the final integer residual must be zero. If
unit original moduli are forbidden, reject a recovered label with
e=0,m=1. These tests recognize the exact one-prime marginal images;
the original p-phases remain free. This procedure requires the whole
B-entry input table and exact finite-field arithmetic. No small-cost
bound or efficient access to an unavailable table is asserted.

An equivalent cyclotomic proof reduces a primitive m-th root modulo a
prime ideal over p after isolating the largest differing p-denominator.
There is no loss of distinct m-th roots when p does not divide m: the
reduction of X^m-1 is separable, and its factorization into all m roots
therefore has no repeated reductions. Passing to a finite extension
field is permitted and required when the roots do not lie in the prime
field. The finite-field argument above avoids this ideal notation.

For TWO different primes p and q, equality of both complete marginals
forces equality of the full original families. Each marginal identifies
the numerical inventory. At a fixed original modulus d, they recover
its phase modulo

    d/p^(v_p(d)) and d/q^(v_q(d)),

whose least common multiple is d. Hence the original phase modulo d is
uniquely determined. One may choose p and q from the prime support of Q
when it contains two primes. The proof also permits H=0 for a prime
outside the support: its coordinate is trivial and M_p=c_A on Z/Q.
No oddness, coverage, irredundancy or divisor closure is used.

### Exact arithmetic restrictions and the remaining covering gap

For any actual distinct-modulus family, L_p mod p must itself be the
multiplicity function, in characteristic p, of a family having at most
one cofactor class per numerical modulus. It is the top-height family.
After subtracting that exact layer and dividing the residual integer
function by p, the same restriction holds at the next height. Thus
arbitrary proposed exact marginal functions do not automatically have
an original distinct-modulus realization. Two prime marginals must
additionally reconstruct compatible phases of the SAME original labels.
Separate realization or separate optimization does not establish a
shared realization.

There is an exact converse once each proposed table passes the single-prime
recognition procedure. Let their recovered numerical inventories be D_p
and D_q. A common original distinct-modulus realization exists if and only if

    D_p=D_q, and for each d in this inventory,
    a_(p,d)=a_(q,d) mod gcd(d/p^(v_p(d)),d/q^(v_q(d))). (MR5)

Necessity follows from single-prime uniqueness. For sufficiency, apply
the generalized CRT separately at each original d to its two recovered
prime-free phases. Their moduli have lcm d, so MR5 produces exactly one
phase a_d modulo d. MR1 then verifies that this SAME assembled family
has both prescribed complete functions. Classes at different numerical
labels may overlap; no extra cross-label constraint is part of the
realization problem. Pure prime powers, an optional unit label, and
H=0 obey the same argument. The common realization is unique.

For example, at Q=105 the p=3 average of {0 mod105} and the q=5 average
of {1 mod105} are separately realizable and recover the same inventory.
Their recovered phases are0 modulo35 and1 modulo21, which disagree
modulo7, so they have no common distinct-label realization. MR5 decides
common realization of the exact tables; it does not decide whether that
realization covers all integers.

If the original family covers, MR1 necessarily gives M_p(y)>=1 for every
p and every y. A prime-owner Lettl–Sun row or weighted line inequality
can constrain these values; it does not specify their exact values.
Even knowing the exact complete functions would only identify the
family, not by itself exclude a covering family. The reconstruction
argument must not be applied to an inequality as though that inequality
supplied the function.

MR1 averages uniformly over the COMPLETE original p-coordinate, with
every actual cofactor y retained. A vector denoted `phase_weights`, when
formed after conditioning on survivors, a private region, a selected
head or any other event, is not MR1 merely because its entries are
weights on phases. Applying reconstruction to such conditional weights
requires a separate proof recovering all MR1 values, including removed
cofactors and the original averaging law. This section supplies no such
transport. Nor does it apply to independent fractional phase choices:
for a cofactor modulus m>1, convexifying one residue class uniformly over
all its phases erases its nontrivial primitive Fourier coefficient,
while an actual single class has a nonzero root coefficient in MR2.

A distinct-modulus control separates all NONTRIVIAL prime-coordinate
lower bounds, for the support primes p dividing Q, from whole coverage.
At period 24 take the classes

    0 mod2, 0 mod3, 1 mod4, 5 mod6,
    1 mod8, 11 mod12, 13 mod24.                       (MR3)

Their holes are exactly 7 and 19 modulo 24. In natural cofactor order,
complete uniform line averages are

    M_2 = [15,8,13]/8,
    M_3 = [4,8,4,3,4,6,4,3]/3.                       (MR4)

Every displayed value is at least 1, covering both support primes 2,3,
yet these are actual noncovering original classes with pairwise distinct
nonunit moduli. For p not dividing 24, H=0 and M_p=c_A, so its values at
7 and 19 are zero. The control does NOT satisfy the lower bound for
every prime including those outside the support. This example has EVEN
moduli and is REDUNDANT; it does not settle the same sufficiency question
under oddness, irredundancy or the full extremal hypotheses. In
particular it is not a counterexample to Erdős #7.

### Exact finite checks and hypothesis boundaries

The [standard-library program](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/private-shell-saturation-odd-lift/exact_prime_marginal_reconstruction.py),
with its [exact data](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/private-shell-saturation-odd-lift/exact_prime_marginal_reconstruction.json),
enumerates every optional residue choice at every nonunit divisor of
three fixed periods. Marginals use integer scaling by p^H throughout.

|Q|primes|original families|distinct single-prime functions|distinct paired functions|
|---:|:---:|---:|:---:|---:|
|12|2,3|5460|256,450|5460|
|45|3,5|176640|864,3200|176640|
|15|3,5|384|72,32|384|

Every one-prime collision has the same presence and p-free phase at
EVERY original numerical modulus. Every paired marginal identifies the
full family. The finite-field claim, now including optional modulus 1,
is also exhausted at (B,p)=(6,5),(10,3),(15,2),(9,2), respectively over
168,396,768,80 families. These checks do not replace the general proof.

The same consumer verifies MR3–MR4 both from original AP contributions
and from literal multiplicity counts on all 24 points. It also checks
that the outside-support p=5 marginal equals the full multiplicity table
and is zero at both holes. The program exhausts the stated finite
families; it does not implement the constructive decoder above. It retains the
following exact boundary controls:

* Repeated numerical labels allow a complete set of children to replace
  its parent: {0 mod5} and {0 mod15,5 mod15,10 mod15} have the same
  complete p=3 marginal at period 15.
* Repeated numerical labels also destroy two-prime identification:
  {0 mod15,1 mod15} and {6 mod15,10 mod15} have equal complete p=3 and
  p=5 marginals, while the original classes differ.
* Coprimality is essential in the isolated finite-field claim. At B=6
  and characteristic 2, {0 mod3,0 mod6} and {3 mod6} have equal
  multiplicity functions modulo 2, despite different distinct-label
  inventories. Here p divides B, outside that claim's hypothesis.

Reproduce the deterministic JSON with an explicit output path:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/private-shell-saturation-odd-lift/exact_prime_marginal_reconstruction.py --output /tmp/e7_exact_prime_marginal_reconstruction.json
```

Normal and optimized runs give identical output bytes. All validation
uses explicit checked conditions, not optimization-removable assertions.
An [independent C++ enumeration](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/private-shell-saturation-odd-lift/exact_prime_marginal_direct.cpp) instead constructs each literal integer
multiplicity table and sums its residue fibres directly. It agrees on
all182484 families, all six single-prime counts, and all three paired
counts. It also checks MR5 on all2882304 pairs of individually realizable
tables across the three periods, comparing the phase-compatibility test
with the independently enumerated set of actual paired tables. Exactly
182484 pairs are jointly realizable. These three periods have no nontrivial
common cofactor for the two selected primes. A separate period105 control
allows only the optional numerical label105: its106 families produce
36 and22 marginal tables. Of their792 pairs,106 have a common realization;
630 pairs have matching present inventories but conflicting phases modulo7,
and56 have different inventories. Every verdict agrees with literal
multiplicity enumeration. This checks the nontrivial common-cofactor
branch of MR5 without claiming an enumeration of all period105 inventories.
Neither checker implements the finite-field recognition procedure
described above; its general correctness follows from the ordinary proof.

```sh
c++ -std=c++17 -O2 docs/reports/erdos7-odd-covering/frontier/cover-geometry/private-shell-saturation-odd-lift/exact_prime_marginal_direct.cpp -o /tmp/e7_exact_prime_marginal_direct
/tmp/e7_exact_prime_marginal_direct
```

The unresolved #7 step is a uniform obstruction to actual odd distinct
whole-cover families. Injectivity of an exact observation and feasibility
of its lower-bound inequalities do not supply that obstruction.

## Common original phases can obstruct all tight rows

An exact prime average can identify the original labels while leaving
their phases in that prime direction free. These phases must work at
every actual cofactor simultaneously. The following ordinary
coloring application gives a joint obstruction and an exact defect
inside the tight-row region. It does not prove a new unrestricted
noncoverage range, and no Lean verification or literature priority is
claimed.

### From actual row slack to a shared phase constraint

Fix one original family and Q=p^H B, with H>=1 and gcd(p,B)=1. For
each original d_i=p^(e_i)m_i define its actual cofactor and prime events

    C_i={y mod B : y=a_i mod m_i},
    A_i={u mod p^H : u=a_i mod p^(e_i)},
    c(u,y)=sum_i 1_(A_i)(u)1_(C_i)(y).

Let S_p(y) be the fraction of missing p-coordinate values in the full
row at y, and E_p(y) the average of (c-1)_+ on that same row. Counting
excess and holes gives

    E_p(y)-S_p(y)=M_p(y)-1.

If y belongs to C_i intersect C_j and the actual prime prefixes A_i,A_j
are compatible, their intersection has measure p^(-max(e_i,e_j)).
Multiplicity is at least two there, hence

    S_p(y)>=p^(-max(e_i,e_j))-(M_p(y)-1).             (CB3)

This uses one actual row and needs no covering hypothesis. Define a
graph on the original numerical labels by putting an edge ij when
there is an actual cofactor witness y_ij in C_i intersect C_j with

    M_p(y_ij)-1<p^(-max(e_i,e_j)).                   (CB4)

Whole coverage would force incompatible prime prefixes at every edge.
Different edge witnesses can have different cofactors, but the prime
phase of one original class cannot vary between them.

A clique with sum_i p^(-e_i)>1 therefore certifies noncoverage: its
prime cylinders cannot all be pairwise disjoint, and a compatible
pair gives a positive lower bound in CB3 at its fixed witness. This
is the usual disjointness/Kraft argument. If all vertices of a
subgraph have one height h, their residues modulo p^h must instead
give a proper p^h-coloring of that entire subgraph. Bounding its clique
sizes does not in general establish such a coloring.

These statements also give quantitative bounds. If fixed witnesses
on a finite obstruction graph have positive gaps gamma_ij in CB3,
some violated edge implies a full-period hole density at least
min_ij gamma_ij/B. When an edge condition holds on a larger set of
cofactors, its CB3 bound can be integrated on that actual set, using
the same original uniform law.

Explicitly, choose any cofactor set T and any subset of original labels
all at one height 1<=h<=H, with s=p^h. Other original labels can have arbitrary
heights. Define

    w_ij(T)=(1/B) sum_(y in T intersect C_i intersect C_j)
                       (1+1/s-M_p(y))_+.

Let G_T have exactly the edges with w_ij(T)>0. If G_T is not
s-colorable, then

    Pr(hole and cofactor in T)>=min_(ij in G_T)w_ij(T)>0. (CB4a)

For any actual original phases, some edge has equal phases. Its prime
cylinders coincide, so CB3 and S_p>=0 imply the positive-part integrand
bound on every common cofactor. Integrating gives CB4a. The weights
use the same complete-family M_p and original Haar source throughout;
they do not arise from separately optimized laws.

### Scalar overlap tests are relaxations of the shared-phase constraint

The full CB4 constraint already contains a useful pair-overlap scalar
test. This test does not supply an additional obstruction when that
shared-phase constraint is satisfiable. For t>=0, put k=floor(t) and

    Phi(t)=k(k-1)/2+k(t-k).

This is convex, is zero on [0,1], and agrees with binom(n,2) at every
nonnegative integer n. Fix the original cofactor classes and heights,
and let G be either the CB4 graph or its exact-row subgraph, whose
edges have a common cofactor y with M_p(y)=1. Suppose ONE assignment
of the original prime phases makes the prime cylinders disjoint at
every edge of G. Its actual multiplicity c has the prescribed M_p,
whether or not this assignment covers. On that same uniform CRT source,

    average_y Phi(M_p(y)) <= Omega_2
      := average_(u,y) binom(c(u,y),2)
       = sum_(i<j) Pr(original_i intersect original_j)
      <= sum_(i<j, ij notin G, C_i intersect C_j nonempty)
                                      1/lcm(d_i,d_j).       (CB6)

The first inequality is convexity on each full prime row; it does not
assume c>=1. The last inequality holds because graph edges and
cofactor-incompatible pairs have zero intersection, while every
remaining pair contributes either zero or exactly 1/lcm(d_i,d_j).
Thus violation of CB6 certifies that G has no satisfying prime-prefix
assignment. It cannot exclude a table whose CB4 constraints already
have such an assignment. Using the full low-slack CB4 graph can reduce
the upper bound relative to the exact-row graph, but is still a scalar
relaxation of the same constraint. Rows with M_p<1 independently fail
the existing elementary marginal test.

A related active-label count also adds no new phase condition. If a
finite row contains n weights p^(-e_i), one selected weight is p^(-h),
and 1<=M_p<1+p^(-h), then n>=1+h(p-1). Indeed, removing that weight
leaves a sum S with 1-p^(-h)<=S<1. Carrying p equal-depth terms into
one term at the preceding depth never increases the term count. The
finite base-p expansion of S has its first h digits equal to p-1,
since floor(p^h S)=p^h-1. At least h(p-1) original remaining terms
are therefore required; h=0 is immediate. This consequence uses only
the already required M_p>=1 and reciprocal prime-power weights,
not a further private-point or whole-cover phase hypothesis.

These are ordinary consequences and limitations of existing conditions,
not new Lean declarations or an unrestricted noncoverage argument.

### A complete arithmetic obstruction with every clique budget valid

For any odd p and H>=1, put s=p^H. Let W_s be the join of a complete
graph on s-2 central vertices and a five-cycle of rim vertices. Its
largest clique has s vertices; a coloring needs s+1 colors, since
the central vertices use s-2 distinct colors and the rim needs three
additional colors. Every edge lies in a largest clique. There are
exactly five largest cliques, each containing all central vertices
and one rim edge.

Realize this complete compatibility graph with actual congruences.
For every nonedge {i,j}, choose a separate odd prime ell_ij different
from p, and impose conflicting residues0 and1 at its two endpoints.
Give each vertex its own further odd tag prime t_i with residue0.
All these primes are distinct. Let m_i be the product of the primes
assigned to i and b_i their CRT residue. For C_i=b_i mod m_i,

    C_i intersects C_j iff ij is an edge of W_s.

Every actual active set is therefore a clique. Conversely every
clique is an exact active set: satisfy its nonedge-coordinate
conditions, set its tags to0, and set every other tag to1. The
conditions are compatible because two members of a clique never
share a conflicting coordinate. CRT supplies one actual cofactor
point. This accounts for the COMPLETE cofactor domain, not a chosen
subgraph of additional unrecorded conflicts.

Take the original moduli d_i=p^H m_i with arbitrary phases alpha_i
modulo s and cofactor phases b_i. The tag primes make the numerical
moduli distinct and incomparable. They are all odd and nonunit.
The exact singleton active patterns give a private integer for each
original class under every phase assignment. The complete marginal is

    M_p(y)=#{i:y in C_i}/s<=1.

The tight rows M_p=1 are exactly the five largest-clique active
patterns. Each row separately admits a cover by assigning its s
active originals all s phases. Every clique of the COMPLETE tight-row
conflict graph has total prime weight at most one. The graph itself
is W_s, however, and its coloring obstruction shows that no common
assignment of original phases covers all tight rows.

For each largest clique K_j, put

    R_j=intersection_(i in K_j) C_i,
    mu_B(R_j)=1/lcm(m_i : i in K_j).

No other vertex can be active there, since it would enlarge a largest
clique. The five regions are pairwise disjoint. Every phase assignment
leaves at least one missing phase on at least one region. Thus

    Pr(hole and cofactor in union_j R_j)
       >=(1/s) min_j 1/lcm(m_i : i in K_j).           (CB5)

This is sharp over all original phase choices. Assign distinct
central phases and alternate the remaining two phases around the
rim, placing its unique equal-phase edge at a region of smallest
mass. Every other tight region is covered exactly once. The chosen
one has precisely one missing phase, attaining CB5. This argument
retains arbitrary H, the full original numerical labels and one
phase per label throughout.

### Exact finite control and the unrestricted boundary

The [tight-row program](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/private-shell-saturation-odd-lift/tight_row_phase_obstruction.py)
and [exact data](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/private-shell-saturation-odd-lift/tight_row_phase_obstruction.json)
use p=3,H=1, nonedge primes5,7,11,13,17 and tags19,23,29,31,37,41.
The actual cofactors and phases are

    m=(19,805,4147,2635,2849,9061),
    b=(0,0,0,1581,925,5084),
    d=3m=(57,2415,12441,7905,8547,27183).

The cofactor period is50708377254535 and the original period is
152125131763605. No enumeration of that full period is claimed.
The program checks all15 pairwise generalized-CRT conditions,
constructs all22 exact clique active patterns including the empty
one, and checks the complete list of five tight patterns. All729
original phase assignments are evaluated using literal congruences
at representatives of their fifteen p-fibre points. Every tight
row is independently coverable; every common assignment leaves
at least one of the fifteen points uncovered. The minimum is one,
attained by30 assignments. Exact CRT masses give the sharp minimum
over the ENTIRE tight region,

    1/1471442973.

An attaining phase vector is (0,1,2,1,2,2), giving literal original
residues (0,805,8294,4216,6623,5084) at the six displayed moduli.
It leaves zero missing phases on four tight regions and one on the
fifth. Normal and optimized
runs have identical result bytes, and all checks remain active with
Python optimization enabled:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/private-shell-saturation-odd-lift/tight_row_phase_obstruction.py --output /tmp/e7_tight_row_phase_obstruction.json
```

The generalized-CRT clique criterion is already used in
[Report433](../../docs/reports/erdos7-odd-covering/profile-notes/arithmetic/400-449/433-chordal-overlap-certificates-and-their-exact-finite-limits.md).
Coloring and Kraft bounds here are applications of existing
mathematics, not new general graph theorems. The quantitative result
concerns joint phase choices on the specified actual tight region.

Other cofactor rows in this construction have M_p=0,1/s,...,(s-1)/s.
It does not satisfy the whole-table lower bound M_p>=1, or that bound
for every support prime. Its overall noncoverage also follows from
the elementary density bound and its antichain inventory. What the
control separates is precise: every tight row is separately coverable
and every clique budget on their COMPLETE conflict graph passes,
yet a common phase assignment still leaves the exact positive defect
CB5. It does not enlarge the known unrestricted noncoverage range.

The missing #7 bridge is a theorem forcing a common-phase obstruction
or sufficient integrated CB3 defect in every hypothetical extremal
odd family. Exact marginal lower bounds, distinctness, irredundancy
and divisor closure have not been shown here to force it.

## Nonnegative integer two-prime margins retain a further covering condition

Fix one actual original family with full period L=P Q B, where
P=p^H, Q=q^G, p and q are distinct support primes, H,G>=1, and
gcd(B,pq)=1. Fix ONE actual cofactor z modulo B. On its complete
P-by-Q CRT slice let c_ij be the original multiplicity and put

    F_ij=c_ij-1, r_i=sum_j F_ij, s_j=sum_i F_ij,
    A_z=sum_(i,j) binom(c_ij,2)=sum_(i,j) g(F_ij),
    g(t)=t(t+1)/2.

The actual F is an integer matrix with entries at least -1. Whole
coverage would make all its entries nonnegative. Negative row or
column sums already fail the elementary prime-marginal bound. When
r,s are nonnegative, define

    T_Z(r,s)=min sum_(i,j) g(X_ij),
      X_ij nonnegative integers,
      sum_j X_ij=r_i, sum_i X_ij=s_j.                 (IT1)

Their equal integer totals guarantee a feasible matrix, and only
finitely many such matrices exist. A necessary covering condition is

    A_z >= T_Z(r,s) for every actual cofactor z.      (IT2)

This condition uses the row sums, column sums and overlap of the SAME
original family. The overlap is available directly from its literal
labels: write d_t=p^(e_t)q^(h_t)n_t and retain t exactly when
z=a_t mod n_t. For each retained pair whose phases agree modulo both
p^min(e_t,e_u) and q^min(h_t,h_u), add

    P Q / (p^max(e_t,e_u) q^max(h_t,h_u))             (IT3)

to A_z. All other pairs contribute zero. This is the exact number of
their common points on that slice, not an independently optimized
intersection bound. Neither the definition nor the computation assumes
an observer can obtain a complete marginal table at small cost.

### An exact separation from real-valued and pairwise conditions

For arbitrary P,Q>=3 form the signed integer matrix F with corner
F_00=-1, all other entries of its first row or first column equal to 1,
and every interior entry equal to 2. Then

    A=sum g(F_ij)=P+Q-2+3(P-1)(Q-1),
    T_Z(r,s)=A+1.                                   (IT4)

Here and below r,s are the actual sums of this F. To prove the lower
bound, take any feasible nonnegative integer X and set t=X_00>=0.
Relative to F, the corner changes by t+1; the first-row arm and the
first-column arm each change in total by -(t+1); the interior total
changes by t+1. For nonnegative integers x,

    g(x)-g(1)>=x-1,
    g(x)-g(2)>=3(x-2).

Both differences reduce to products of two consecutive integers
divided by 2. Summing over the three regions gives

    sum g(X_ij)-A >= g(t)+(t+1)>=1.

Increase the corner to 0, decrease one entry in each incident arm
from 1 to 0, and increase their common interior entry from 2 to 3.
This rectangle change preserves every margin and increases the cost
by exactly 1, proving IT4. No bounded search is used for this minimum.

The nonnegative REAL relaxation has a strictly smaller answer for
distinct odd prime powers P,Q. Put

    C=1/(P-1)+1/(Q-1)+1/((P-1)(Q-1)).

For fixed corner 0<=t<=min(P,Q)-2, convexity bounds each arm and the interior by
the cost of its constant average. Those averages are respectively
1-(t+1)/(Q-1), 1-(t+1)/(P-1), and
2+(t+1)/((P-1)(Q-1)). This is exactly the feasible corner range; these
averages preserve every original row and column sum. The exact minimum at that t differs
from A by

    t^2/2-1/2+C(t+1)^2/2.

This increases on t>=0, and t=0 is feasible. Thus

    T_R(r,s)=A-1/2+C/2.                              (IT5)

After exchanging the two axes if needed, distinct odd prime powers
have P>=3 and Q>=5, so C<=7/8 and T_R<=A-1/16<A.
The real relaxation therefore does not reject this actual F; the
nonnegative integer condition does.

For P=3,Q=5 the complete matrices are

    F = [-1 1 1 1 1]      X = [0 0 1 1 1]
        [ 1 2 2 2 2]          [0 3 2 2 2]
        [ 1 2 2 2 2]          [1 2 2 2 2].

Both have row sums (3,9,9) and column sums (1,5,5,5,5).
Their costs are 30 and 31. The nonnegative real optimum is 479/16,
attained by corner 0, first-row arms 3/4, first-column arms 1/2 and
interior 17/8. The ordinary unconstrained row/column L2 bound is 446/15,
also below 30. These values are exact rational arithmetic; the minimum
claims are proved by IT4--IT5 rather than inferred from a solver result.

### Realization by distinct odd numerical labels and the global boundary

The separation is realizable on one actual arithmetic slice at every
pair of distinct odd prime powers. For EACH of the c_ij=F_ij+1 copies
at a nonzero cell choose a fresh odd prime ell_t, different from p,q
and from every other tag. Take one original class with numerical
modulus P Q ell_t and CRT phases i mod P, j mod Q, 0 mod ell_t.
There are

    N=2(P+Q-2)+3(P-1)(Q-1)

such classes; N=36 for P=3,Q=5. All numerical moduli are odd, greater
than 1 and pairwise distinct. On the SAME auxiliary cofactor where
all tags equal 0, their multiplicity is exactly c. Each original has
a private witness: give it its prescribed p,q phases and tag 0, and
set every other tag to 1. Thus the family is irredundant as well.

Every original has prime heights H,G. On the selected slice, the
smallest p-marginal is 2(P-1)/P, with slack 1-2/P>=1/P; the q direction
has the analogous bound. The strict CB4 inequality never holds in
either slice graph. For P=3,Q=5 the p-marginals are
(4/3,8/3,8/3,8/3,8/3), and the q-marginals are (8/5,14/5,14/5).
Consequently IT2 rejects a slice whose ordinary marginal bounds and
both slice CB4 graphs do not reject, even though the continuous
transportation bound also passes.

This comparison is limited to the specified slice. If all auxiliary
tags instead equal 1, no original is active and the p- and q-marginals
are zero. The control is NOT a family passing all complete prime
marginal tests or all global CB4 constraints. It does not enlarge the
known unrestricted noncoverage range. A bridge to Erdős #7 still needs
an arithmetic argument forcing a marginal failure or an IT2 violation
in every hypothetical distinct odd cover, or a stronger compatible
condition if these tests can all pass. The inequalities and constructions
here are ordinary proofs, not new Lean verification or a priority claim.

### Private residual zeros do not rescue nonnegative transport potentials

Keep the SAME actual two-prime slice and F=c-1 from IT1. For an
integer k define the elementary discrete conjugate

    h(k)=max_(n>=0 integer)(k*n-g(n))
        =0 if k<=1, and k*(k-1)/2 if k>=2.

This follows from the successive differences g(n+1)-g(n)=n+1.
For arbitrary integer row and column potentials alpha_i,beta_j put
k_ij=alpha_i+beta_j. If E is a set of cells with ACTUAL F_ij=0, set

    D_E=alpha*r+beta*s-sum_((i,j) notin E) h(k_ij).

Any nonnegative integer table with the same margins and zeros on E
has cost at least D_E, by summing g(n)>=k*n-h(k). Thus a whole cover
with these actual zeros necessarily satisfies A_z>=D_E. No assertion
of strong duality or a new transportation theorem is needed here.
Write T_E(r,s) for the corresponding minimum cost, taking +infinity
when its feasible set is empty.

However, if EVERY cell has k_ij>=0, then

    A_z>=D_E                                       (IT6)

holds for EVERY actual multiplicity table, including tables with holes.
To prove this, write the exact difference as

    A_z-D_E=sum_((i,j) notin E)
                [g(F_ij)-k_ij*F_ij+h(k_ij)].        (IT7)

Covered cells have F_ij>=0 and nonnegative bracket by the defining
maximum for h. At a hole F_ij=-1, the bracket is k_ij+h(k_ij), again
nonnegative when k_ij>=0. Cells in E contribute zero because both
F and g(F) vanish and their conjugate penalties have been omitted.
This proves IT6 without using whole coverage, oddness or distinctness.

In particular, fix one literal original cylinder
C_t=I_t times J_t times K_t and its actual private region Pi_t.
On each cofactor z in K_t take

    alpha_i=a*1_(i in I_t), beta_j=b*1_(j in J_t), a,b>=0 integers,
    E_z={(i,j): (i,j,z) belongs to Pi_t}.

All these k are nonnegative. Summing IT6 over the SAME K_t therefore
gives, for any actual family, covering or not,

    sum_(z in K_t) A_z
      >=a*sum_(z in K_t) r_z(I_t)+b*sum_(z in K_t) s_z(J_t)
        -|K_t|*[|I_t||J_t|h(a+b)
                +|I_t|(Q-|J_t|)h(a)
                +(P-|I_t|)|J_t|h(b)]
        +|Pi_t|h(a+b).                              (IT8)

With a=b=1 this becomes

    Delta_t=sum_(z in K_t)[A_z-r_z(I_t)-s_z(J_t)]
                 +|K_t||I_t||J_t| >= |Pi_t|.         (IT9)

Every irredundant family, even a noncover, has |Pi_t|>=1 for each
original t. Consequently the target Delta_t<=0 is already impossible
for an irredundant family without assuming whole coverage. The private
point bonus does not supply a new covering obstruction. Expanding all
terms into exact original-label CRT intersection counts leaves this
conclusion unchanged; such an expansion changes no inequality.

There is an exact sign criterion for a potentially useful certificate.
Allow arbitrary signed integer alpha_i,beta_j, keep
k_ij=alpha_i+beta_j, and put

    H_-={(i,j): F_ij=-1 and k_ij<0}.

For these cells h(k_ij)=0. Partitioning IT7 gives

    A_z-D_E=P_E-sum_((i,j) in H_-) (-k_ij),          (IT10)

where P_E is the sum of the nonnegative brackets over covered cells
outside E and over holes with k_ij>=0. Hence D_E>A_z holds exactly
when the weighted negative-potential holes exceed P_E. In particular
negative k at an ACTUAL hole is necessary, not merely a negative
alpha or beta somewhere. Such negativity alone is not sufficient:
the covered-cell slack can still pay for it. IT10 is an identity on
the original table, not a way to obtain unknown hole locations for free.

Forced zeros can nevertheless strengthen the OPTIMIZED transportation
test even when every marginal and the ordinary optimized test pass.
Consider the actual integer residual table

    F = [0 2 -1]       r=(1,10,10), s=(12,8,1),
        [6 3  1]       A=sum g(F_ij)=59,
        [6 3  1]       E={(0,0)}.

All multiplicities F+1 are nonnegative, every residual margin is
strictly positive, and E is an actual residual zero. The two tables

    X = [1 0 0]       X_E = [0 1 0]
        [5 4 1]             [6 4 0]
        [6 4 0]             [6 3 1]

have the same margins and costs58 and60, respectively; X_E is zero
on E. For the unrestricted problem, alpha=(0,4,4), beta=(2,0,-3)
give alpha*r+beta*s=101 and sum h(k)=43, hence D_empty=58.
For the fixed-zero problem, alpha=(0,2,2), beta=(5,2,-1) give
alpha*r+beta*s=115 and sum_(notin E) h(k)=55, hence D_E=60.
Feasible tables and weak duality prove both minima exactly:

    T_Z(r,s)=58 <= A=59 < T_E(r,s)=60.              (IT11)

The fixed-zero certificate uses only r,s,A,E. It does not need the
hole location as an input. At the displayed actual hole its k is -1;
every covered cell outside E has zero bracket in IT7. Thus IT10
has P_E=0 and a negative-hole contribution of1, exactly matching
A-D_E=-1. The point of IT11 is the strict separation from the
ordinary optimized transport test, not merely T_E>T_Z.

This separation has a literal distinct-odd AP realization on one
common slice. Append two columns of F=0 to get a 3-by-5 table.
The new column margins are zero, forcing those columns to be zero
in EVERY feasible nonnegative table. Both minima and A are unchanged.
The dual beta vectors extend by (-4,-4) and (-2,-2), respectively,
without adding any conjugate penalty. All complete3- and5-marginals
on this slice are at least1; the new columns attain equality.

There are36 multiplicity copies in F+1. Give each one a different odd
prime tag ell_t outside{3,5}, and use the literal numerical modulus
15*ell_t with that cell's3- and5-phases and tag phase0. The moduli
are pairwise distinct odd nonunits. At the SAME cofactor where all
tags are0, the original multiplicity table is exactly the padded
table. The cell(0,0) has a unique original and is its actual private
point, supplying E. Every original also has a private witness with
its own tag0 and all other tags1, so the family is irredundant.

This is only a selected-slice separation. When all tags are1, no
original is active and the complete3- and5-marginals are zero. Each
tag prime also has a zero complete marginal: hold the3- and5-cell
different from its original's cell and all other tags at1. Hence
this is NOT a noncover passing all complete prime marginals, and it
does not enlarge the unrestricted noncoverage range. The exact
minimum proofs above use the explicit primal and dual witnesses;
independent enumeration of the43 feasible3-by-3 tables agrees.

For an inclusion-minimal whole cover, each original t must have SOME
actual private position (i,j,z) in its cylinder. A valid further test
may therefore reject all candidate positions by comparing A_z with
the corresponding fixed-zero transport minimum, keeping each slice's
own margins and actual overlap. Excluding every position for just
one t rules out that family's being an inclusion-minimal whole cover.
For a general family the conclusion is only that it does not cover
OR t is redundant. Under whole coverage the exclusion therefore
forces redundancy; with t independently known essential it forces
noncoverage. Universal #7 forcing still requires original-label
arithmetic that violates a genuinely coverage-dependent condition.
These are ordinary finite proofs, not new Lean verification.

### Private-zero separation survives complete private rows and columns

The IT11 example has a hole in the same row as its private point, so
it does not pass the strong private-shell condition even on that
selected two-prime slice. The following family separates the fixed-zero
transport test after imposing that further local condition as well.

For ANY integers P,Q>=3 define one actual residual table by

    F_00=-1;
    F_0j=F_i0=1 for i,j>0;
    F_11=0;
    F_ij=2 for every other i,j>0.

It has exactly one hole, at(0,0), and exactly one private cell, at(1,1).
They are in different rows AND columns, so both complete coordinate
lines through the private point are covered. Thus the slice satisfies
the no-private-to-hole-edge condition PS2 in both selected directions.
Every residual margin is strictly positive:

    r=(Q-2,2Q-3,2Q-1,...,2Q-1),
    s=(P-2,2P-3,2P-1,...,2P-1).

The actual overlap cost and both transport minima are

    A=P+Q-2+3*((P-1)*(Q-1)-1),
    T_Z(r,s)=A-1,
    T_E(r,s)=A+1, E={(1,1)}.                       (IT12)

Here T_E fixes the ONE actual residual zero. The claimed minima
have exact primal and dual witnesses at every P,Q.

For the ordinary minimum, change F_00 from-1 to0, F_01 and F_10
from1 to0, and F_11 from0 to1. This rectangle move preserves all
margins, makes the whole table nonnegative, and lowers its cost by1.
Use additive potentials

    alpha=(0,1,2,...,2), beta=(-1,0,1,...,1).

Each positive entry x of this repaired table satisfies
x<=alpha_i+beta_j<=x+1; each zero has alpha_i+beta_j<=1.
These are equality conditions in g(x)>=k*x-h(k), so the feasible
table and weak dual bound agree at A-1. No strong-duality assertion
or numerical minimization is needed.

For the fixed-zero minimum, instead repair the corner using rows0,2
and columns0,2: F_00 rises to0, F_02 and F_20 fall to0, and F_22
rises from2 to3. The private cell(1,1) remains zero. All margins
are preserved and the cost rises by1. Take

    alpha=(0,2,2,...,2), beta=(-1,1,1,...,1).

The potential sum is-1 at the hole,1 on the two arms, and3 on the
interior. Outside E every covered entry of the ORIGINAL F has zero
Fenchel slack, while the hole contributes-1. Removing the conjugate
penalty h(3)=3 at E therefore gives D_E=A+1 by IT7. Equivalently,
the repaired nonnegative table attains equality at every allowed
cell. These matching witnesses prove the fixed-zero minimum in IT12.

For P=3,Q=5 this gives

    F=[-1 1 1 1 1]
      [ 1 0 2 2 2]
      [ 1 2 2 2 2],
    r=(3,7,9), s=(1,3,5,5,5),
    T_Z=26 <= A=27 < T_E=28.

The complete selected-slice prime marginals are
M_3=(4/3,2,8/3,8/3,8/3) and M_5=(8/5,12/5,14/5), all strictly
above1. Independent enumeration of all2909 feasible3-by-5 tables
agrees with both minima; the universal result is proved by the
witnesses above, not by this enumeration.

To realize the family with original labels, take P=p^H and Q=q^G
for distinct odd primes p,q and arbitrary H,G>=1. Reuse the
[two-coordinate exponent-antichain construction, Report345 section5](../../docs/reports/erdos7-odd-covering/profile-notes/321-384/345-fixed-prime-fourier-obstruction-and-digit-relation-masks.md).
Choose just TWO further distinct odd primes r,s, neither equal to p,q,
and enumerate the F_ij+1 multiplicity copies by t=1,...,N, where

    N=sum_(i,j)(F_ij+1)=3P Q-P-Q-3.                 (IT13)

Assign copy t the literal modulus P Q r^t s^(N+1-t), its prescribed
p,q-cell, and zero phase on both auxiliary coordinates. These are
distinct odd nonunits on EXACTLY FOUR support primes. On the SAME
cofactor with auxiliary coordinates zero modulo r^N and s^N, the
exact table is F+1. The unique class at(1,1) supplies the true private
zero; its complete p- and q-lines are covered.

Every original has a private witness. Give its auxiliary coordinates
truncated valuations t and N+1-t, where valuation N means the zero
coordinate modulo the Nth prime power. Copy u is active only if
u<=t and N+1-u<=N+1-t, forcing u=t. Its assigned p,q-cell then gives
a private point, including the endpoint exponents. Equivalently, let
G_t=r^t s^(N+1-t) and let b_t mod P Q be its cell residue. With all
inverses taken modulo P Q, the literal integer

    w_t=G_t*(1+r*s*k_t),
    k_t=((b_t*G_t^(-1)-1)*(r*s)^(-1)) mod P Q

has the prescribed cell and exact auxiliary valuations, proving the
same isolation. This is an application of the existing construction,
not a new tagging principle. For P=3,Q=5 there are34 originals, with
support {3,5,7,11} when r=7,s=11.

The complete-row condition here applies only to the two selected
prime directions on this actual slice. It is NOT the global PS1
condition for all private points and all support primes. In particular,
changing the r-coordinate from0 to1, while retaining the private
p,q-cell and s-coordinate0, creates a hole. The cofactor r=s=1
also has zero complete p- and q-marginals. The complete r-marginal
is zero when the s-coordinate is1, and the complete s-marginal is
zero when the r-coordinate is1. Therefore the construction is neither an all-marginals-passing
noncover nor a global private-shell-saturated distinct-odd example.
It proves that selected-slice marginal feasibility, ordinary optimized
transport, and complete private lines together do not subsume the
fixed-zero transport test. Unrestricted #7 still requires a global
same-original-label forcing argument. These are ordinary proofs,
not new Lean verification or a claim of literature priority.

## Existing survivor laws restrict simultaneous complete marginal feasibility

The uniform-profile argument establishes MF1 through five support primes.
Under the stronger attributed common-law source premises specified below,
MF7 extends the exclusion through eight, and MF8 restricts the two largest
primes at support size nine. The source dependencies are kept explicit.

The existing product and complete-survivor laws imply more than a
noncoverage assertion for the following restricted task. For any
finite NONEMPTY family of congruence classes with pairwise distinct odd
numerical moduli greater than 1, arbitrary residues, actual period L>1
and at most FIVE support primes, at least one actual support prime r satisfies

    min_y M_r(y)<1.                                  (MF1)

Thus a nonempty odd-distinct noncover whose EVERY complete support-prime
marginal is at least 1 must use at least six primes. This is a reuse of
existing survivor estimates to restrict that stronger marginal-feasibility
search, not an enlarged noncoverage range for Erdős #7. Empty support
is excluded: when L=1 there is no support prime to select.

### Keep the target coordinate Haar while conditioning the others

Write L=product_p p^(H_p) and fix a target r. For each p other than r,
let U_p be the actual set avoiding every original pure-p-power class.
With normalized Haar on that coordinate, put

    delta_p=sum_(e=1..H_p)p^(-e),
    b_p=delta_p/(1-delta_p),
    s_p=Haar(U_p)>=1-delta_p>0,
    u_r=sum_(e=1..H_r)r^(-e).

Use the product of the uniform laws on these actual U_p, but keep the
ENTIRE r-coordinate Haar. This is the same pure-power survivor
construction used in [FC1, FC4 and PH1](../../docs/reports/erdos7-odd-covering/problem-details/02-current-bounds-and-comparisons.md),
with precisely one coordinate left unconditioned. On its cofactor
product law nu, Fubini gives

    E_nu M_r=E_(Haar_r times nu)c
      <=(1+u_r) product_(p!=r)(1+b_p)-1-sum_(p!=r)b_p. (MF2)

Indeed every anchor cylinder of depth e has conditional mass at most
p^(-e)/s_p<=p^(-e)/(1-delta_p). Sum the product bound over the complete
numerical exponent inventory; then omit the unit and every pure-anchor
slot. Such a pure slot is either absent or its actual event is disjoint
from U_p. All other missing labels only enlarge this upper bound. This
retains the original phases and one common product law. Conditioning
the r-coordinate as well would no longer give the complete M_r here.

The upper bound in MF2 increases in every b_p: its slope is
(1+u_r) product_(q!=p,r)(1+b_q)-1>0. Since
b_p<1/(p-2) and u_r<1/(r-1), choose r largest and compare the ordered
support with the first odd primes. The resulting height-uniform bounds
for support sizes 1,2,3,4 are respectively

    1/2, 1/2, 7/9, 74/75.

All are below 1. This argument includes arbitrary finite heights and
arbitrary residues. The finite-height formula, for the full-support
periods 11025=3^2*5^2*7^2 and 17325=3^2*5^2*7*11, gives respectively

    min M_7 <=2976/4655,
    min M_11<=4589/6270.

These are analytic all-phase exclusions for the complete-marginal
search at those periods, not solver UNSAT claims. The averaging sets
are the actual pure-power survivor products, which can depend on the
family; they are not the rectangle obtained by deleting first roots only.

### Apply the existing four-prime complete-survivor profile

More generally, take any probability mu on the cofactor carrier that
avoids every r-free original. Define its nonunit cylinder-cap sum

    R_mu=sum_(1<m | L/r^(H_r)) max_a mu(y=a mod m).

The r-free contributions to M_r vanish on mu. At each positive r-height
there is at most one original per cofactor m, and the unit cofactor
has mass 1. Therefore on this SAME law

    min_y M_r(y)<=E_mu M_r<=u_r(1+R_mu).              (MF3)

[The four-prime profile, P3--P5](../../docs/reports/erdos7-odd-covering/problem-details/10-a-four-prime-head-and-a-restricted-noncoverage-theorem.md)
already constructs the uniform law on the complete survivors of any
family supported on {3,5,7,11}, and proves R_mu<=1514/145, uniformly
in all phases and heights. The profile transfers coordinatewise to
any four ordered odd primes p_1<p_2<p_3<p_4: these are no smaller than
3,5,7,11. Here the transfer concerns the numerical BOUNDS, not a map
that transports an individual old configuration to a new one.

For completeness, label prime subsets by their coordinate indices.
Start from the empty-subset profile. If its predecessor coefficients
are bounded by the old ones, each new envelope term in P3 is no larger:
the primes in its denominator have only increased. Hence its entire
nonunit sum R is no larger. In P4, both the pure-cylinder factor
(p-1)/(p-2) and the deletion ratio R/(p-2) are no larger, so each old
admissible extension remains admissible with no larger coefficients.
Taking the minimum over these orders is legitimate because all orders
describe the SAME new uniform complete-survivor law. Induction over
subsets proves the claimed transfer and R_mu<=1514/145.

For exactly five support primes, choose the largest r>=13 and apply
that law to the four-prime r-free family. The prescribed cofactor
carrier may include unused coordinates or digits; uniform lifting
is part of the same cylinder-profile construction. MF3 now gives

    min_y M_r(y)< (1+1514/145)/(r-1)
                <=553/580<1.                        (MF4)

Together with MF2 this proves MF1. This use of P3--P5 introduces no new
profile computation, residue enumeration, Lean theorem or noncoverage
range. An old assertion that a hole merely exists would not imply MF1;
the existing complete-survivor LAW and its cylinder caps are the input.

### Uniform profiles restrict six support primes to seventeen prime sets

Suppose the original family has exactly six support primes and every
complete support-prime marginal is at least 1. Then its support must be
one of the following SEVENTEEN sets:

    {3,5,7,11,13,r},  r prime, 17<=r<=71;             (MF5a)
    {3,5,7,11,17,19}, {3,5,7,11,17,23};              (MF5b)
    {3,5,7,13,17,19}.                               (MF5c)

There are fourteen choices of r in MF5a. This is a necessary condition,
not an assertion that any listed set admits such a family. Every
finite exponent and every original residue remain unrestricted.
The stronger common-law application MF7 below excludes all seventeen
sets under its stated source premises.

Only five profile calculations are needed for the exclusion. In each
row below, remove the target r and apply the existing P3--P4 recurrence
to the five cofactor primes. It supplies the uniform probability on
the complete survivors of the actual r-free original family, with
nonunit cylinder-cap sum bounded by the displayed R. Its empty subset
is the base case; each of its 31 nonempty indexed subsets has an
admissible last-prime extension.

| Ordered six-prime support | Target r | Cofactor profile bound R | (1+R)/(r-1) |
|---|---:|---:|---:|
| 3,5,11,13,17,19 | 3 | 58495/63454 | 121949/126908 |
| 3,5,7,11,19,23 | 23 | 11159716533087/534598681841 | 5847157607464/5880585500251 |
| 3,5,7,11,17,29 | 29 | 1652775682537/66859985411 | 429908916987/468019897877 |
| 3,5,7,13,17,23 | 23 | 507203988220491/29060939613244 | 536264927833735/639340671491368 |
| 3,5,7,11,13,73 | 73 | 814972792/11609325 | 826582117/835871400 |

All five entries in the last column are strictly below 1. By MF3 each
row forces a deficient complete marginal. The subset induction used
above for MF4 applies without a restriction to four coordinates:
if an ordered six-prime support is coordinatewise at least a displayed
row, use the same indexed target. Its five-prime profile coefficients
and envelope sum are no larger, and its target denominator is no
smaller. Thus every such larger support is excluded too. This transports
the bounds to the new family's OWN complete-survivor law; no old
configuration, selected phase assignment, or optimized measure is
substituted for the actual new one.

Here is an exhaustive argument for the remaining supports, with no
bound on the initially proposed primes. Avoiding the first row forces
the three smallest primes to be 3,5,7: otherwise the third is at least
11 and the support dominates that row. Write the other three as a<b<c.
Avoiding the second row forces b<=17. If b=13, then a=11, and avoiding
the last row gives c<=71, precisely MF5a. If b=17, then a is 11 or 13.
For a=11, avoiding the third row gives c=19 or 23; for a=13, avoiding
the fourth gives c=19. These are MF5b--MF5c. No further ordered prime
cases remain.

The [existing exact profile verifier](../../docs/reports/erdos7-odd-covering/elementary-checks/verify_uniform_head_profile.py)
now checks these five parameters in addition to its original four-prime
ones. It evaluates the full infinite envelope sums by finite cutoff
cells and exact geometric tails. The all-residue, all-finite-height
conclusion comes from the profile induction and MF3, not from enumerating
residues or sampling heights. This is an ordinary proof and a restriction
of the stronger marginal-feasibility search; it is not a Lean result or
a settlement of unrestricted Erdős #7.

### Disjoint prime components cannot repair a deficient marginal

Join two support primes when an original numerical modulus contains
both, and let S_j be the connected components of this graph. Every
nonunit original belongs to exactly one component. In the actual CRT
coordinates, write its component multiplicity as c_j(x_j). Then

    c(x)=sum_j c_j(x_j),
    min c=sum_j min c_j.

For p in component j, complete uniform averaging in that p-coordinate
and minimization over the independent remaining coordinates give

    min M_p=min M_p^(j)+sum_(k!=j) min c_k.           (MF6)

These identities concern the same original family. A noncover has
min c=0, so every min c_k=0. Its complete marginals are therefore all
at least 1 exactly when the complete marginals of every component
are all at least 1. A nonempty odd-distinct NONCOVER passing the tests
can consequently be reduced to one connected component that also
passes. Every component of any such family must have at least six
support primes by MF1; any component with exactly six must have a
support in MF5. In particular, adding disjoint pure-prime tails to a
known noncover cannot repair its deficient old marginals. This reduction
does not assert that a connected family passes the tests, and supplies
no unproved existence of a covering or noncovering family on MF5.

### Query-independent survivor laws extend the marginal exclusion through eight primes

MF3 only requires one probability supported on the actual r-free
survivors; it does not require that probability to be uniform. The
common-law query bounds already proved in
[Report461](../../docs/reports/erdos7-odd-covering/profile-notes/arithmetic/450-499/461-query-stop-loss-gives-a-common-law-six-core-completion-margin.md)
and
[Report462, LS1](../../docs/reports/erdos7-odd-covering/profile-notes/arithmetic/450-499/462-the-final-stage-ledger-gives-a-seven-core-common-law.md)
therefore give the following stronger conclusion, under their attributed
source construction and comparison premises:

    1<=number of actual support primes<=8
       ==> some actual support prime r has min_y M_r(y)<1. (MF7)

The original moduli remain pairwise distinct odd integers greater than1;
all original phases and finite heights are arbitrary. The source is
Michael Schroeder's Nine Prime Divisors in Odd Distinct Covering Systems,
edition1.0.1. The source identity and local verification boundary are in
its [library entry](schroeder2026nine.md). MF7 applies the existing
common-law interfaces; it is not a new finite geometry calculation,
Lean result, or improvement of the known bare noncoverage range.

For six, seven or eight actual support primes choose the largest one r,
and let K=L/r^(H_r). Use the indicated law on the ACTUAL complete
survivors of the r-free original subfamily. It controls all cylinders
modulo every divisor of this fixed K, including query depths not used
by the r-free subfamily itself. The law is chosen before the later
layouts, and the same law serves every target height.

| Actual support size | r-free core size | Bound on R_mu from the common law | Smallest possible r | Bound on min M_r |
|---|---:|---|---:|---:|
|6|5|R_mu<10|17|<11/16|
|7|6|R_mu<14|19|<5/6|
|8|7|R_mu<=70874/3375|23|<74249/74250|

Indeed MF3 gives

    min M_r<=u_r*(1+R_mu),
    u_r=sum_(h=1..H_r)r^(-h)<1/(r-1).

The last entry is (1+70874/3375)/22=74249/74250<1.
The first two use the conservative bounds10 and14; Report461 gives
strictly smaller exact constants. MF1 handles support sizes one
through five. No coordinate average is taken under a conditioned
r-law: M_r remains the COMPLETE uniform r-coordinate average, and
only its cofactor is averaged under mu. Thus this deduction does
not replace a marginal by a different observable.

An empty r-free family or unused cofactor coordinates cause no extra
assumption. The source interfaces permit a family on AT MOST the
stated number of primes and any fixed resolving period; their finite
padding, transport and projection supply exactly the required carrier.
No compatible choice of laws over an infinite chain of periods is
needed, since the actual original family and its period are finite.

For eight support primes the quantitative gap relies on Report462's
uniform query functional LS5 and retained surplus LS6. It would NOT
follow just from the source's bare assertion that some survivor exists,
nor from the actual loss of an empty auxiliary23 family. The source's
finite geometry and rational certificate have been locally reproduced;
its full arbitrary-height comparison remains an attributed premise,
and no fresh full Lean replay is asserted here.

Consequently every nonempty odd-distinct family passing ALL complete
support-prime marginals must use at least NINE primes, under these
same source premises. The seventeen supports in MF5 remain valid
necessary restrictions furnished by the earlier uniform-profile
calculation, but MF7 excludes all of them using the stronger common
laws. They are not remaining cases of the full marginal-feasibility
problem. In particular MF6 now implies that every component of an
all-marginals-passing NONCOVER must contain at least nine primes.
No such actual noncover is constructed, and no result for arbitrary
support size is claimed.

### The same query extension restricts the two largest primes at support size nine

The one-prime query extension in
[Report463, PE6](../../docs/reports/erdos7-odd-covering/profile-notes/arithmetic/450-499/463-two-actual-prime-extensions-preserve-a-common-core-law.md)
also applies to MF3. Use the stronger seven-core input

    A=70871/3375,

from the relative-ledger deduction in
[Report466](../../docs/reports/erdos7-odd-covering/profile-notes/arithmetic/450-499/466-randomized-completion-retains-full-original-survivor-support.md).
This step retains that deduction's attributed source comparison and
compatible-screening premises. Full survivor support and the all-depth
compactness consequence of that report are not needed here.

For exactly nine support primes let q<r be the two largest, so q>=23.
Choose the fixed seven-core law on the actual subfamily avoiding both
q and r. Extend it through the actual q-bearing, r-free originals by
PE6, keeping the complete cofactor period required by the r-bearing
queries. Since q>A+2, the resulting one survivor law has

    R8(q)<=B_A(q):=((q-1)A+1)/(q-2-A).

Consequently the sufficient bound 1+B_A(q)<r-1 gives a deficient
complete r-marginal by MF3. Multiplying this bound comparison by the
positive denominator shows that it is exactly

    N_A(q,r)=(q-A-2)(r-A-2)-(A^2+A+1)>0.          (MF8)

Interchanging q and r proves a deficient complete q-marginal as well.
The two cofactor laws and two witnessing points can differ; this is
not a simultaneous choice of both minima under one law. Each argument
uses one law for all its own original-label queries. The algebraic
criterion is the existing symmetric PE9 criterion, now read as a
complete-marginal obstruction rather than only as bare noncoverage.

Thus a nine-support family passing all complete marginals must have
N_A(q,r)<=0. Its two largest primes obey the following exact necessary
bounds; the displayed upper endpoints need not themselves be prime.

| Eighth prime q | Upper bound on ninth prime r |
|---:|---:|
|23|1562545/4|
|29|2028271/20254|
|31|2183513/27004|
|37|2649239/47254|
|41|2959723/60754|

These are obtained by solving MF8 for
r<=A+2+(A^2+A+1)/(q-A-2), which decreases with q>A+2.
At q=43 the upper endpoint is3114965/67504<47, while the next support
prime must be at least47. Every larger q is excluded as well. Hence
the five q values in the table exhaust the possible eighth primes,
without bounding any original exponent. The seven smaller primes
remain subject to being distinct odd primes below q and all the
other original constraints. None of these necessary cases is claimed
feasible, and the table does not assert a new unrestricted or bare
noncoverage range.

### Nine-support marginal feasibility requires both small primes

A product-source calculation further restricts MF8. Any family on exactly
NINE support primes which passes all complete support-prime marginals
must contain BOTH3 and5. The original phases and finite heights remain
arbitrary. The sufficient common-law statement is

    p_i>=(3,7,11,13,17,19,23,29)_i, i=1,...,8
      ==> some actual complete-survivor law mu has R(mu)<25. (MF9)

Here the p_i are eight distinct increasing odd primes, and R sums the
maximal cylinder mass over ALL nonunit numerical labels supported on
these primes, at every depth. The one law is fixed before the query
phases. This ordinary deduction uses the product-source query comparison
in [Report528, FC10--FC11](../../docs/reports/erdos7-odd-covering/profile-notes/arithmetic/500-549/528-surviving-fibre-credits-control-arbitrary-phases-at-ternary-height-one.md),
which attributes the ordered-increment comparison to the pinned
Schroeder1.0.1 Lemma4.1. It uses no source geometry enumeration, new Lean
result or assertion of literature originality. No ternary-height-one
restriction from that report is imposed here: every pure-coordinate
law below avoids its actual complete pure-power family.

For each p use normalized Haar lambda_p on the set avoiding every actual
pure-p-power original. Its cylinder caps are C_p*p^(-e), where
C_p=(p-1)/(p-2). Set b_p=1/(p-2), take their independent product lambda,
and let U be the complete actual original survivor. Summing the mixed
original costs over the full numerical exponent inventory gives

    alpha=lambda(U)>=2+sum_p b_p-product_p(1+b_p).

Indeed the pure originals already have zero mass; each mixed numerical
label occurs at most once and has its one original phase. Its product
cap is summed once. For the least tuple in MF9 the right side is

    a0=1508/35343>21/500.

The mixed inventory product(1+b)-1-sum b increases in each b. Increasing
any coordinate prime therefore preserves this lower bound. In particular
U is nonempty, and mu=lambda restricted to U, divided by alpha, is a
well-defined probability on the SAME actual survivors. Extend the finite
source with Haar digits beyond its original period.

For any finite complete query layout L, including the unit cylinder, the
cited product comparison bounds E_lambda(L-4)_+ by E(M-4)_+, where

    M=product_p(1+J_p),
    Pr(J_p>=e)=C_p*p^(-e), e>=1,

and the auxiliary J_p are independent. These auxiliary runs do not
change the original or query phases. Every run tail decreases when p
increases, so the least tuple suffices for this increasing hinge. Write
u_p=1-C_p/p and v_p=C_p*(p-1)/p^2. For that tuple the exact products are

| Quantity | Exact value | Strict upper bound |
|---|---|---:|
|EM|8192/2295|357/100|
|Pr(M=1)=product u_p|11832238387771/63866647565721|93/500|
|Pr(M=2)=(product u_p)sum v_p/u_p|72637191863928552052076/206598808689370566884415|44/125|
|Pr(M=3)=(product u_p)sum v_p/(p*u_p)|12268544824377379531286911923212/133663091390368592953336191801045|23/250|

Since M is a positive integer, its exact hinge value h0 satisfies

    h0=EM-4+3Pr(M=1)+2Pr(M=2)+Pr(M=3)<231/250.

Restriction to U and L-1<=3+(L-4)_+ consequently give

    E_mu(L-1)<=3+h0/a0<3+(231/250)/(21/500)=25.

The fixed upper bound 3+h0/a0 is independent of query heights and phases.
After fixing mu, maximize each numerical query separately in any finite
exponent box, then exhaust all boxes. Monotone convergence gives
R(mu)<=3+h0/a0<25. Thus strictness is retained at the limit, and no
independently chosen survivor laws are combined.

If a nine-prime support omits3 or5, its eight smallest primes dominate
the tuple in MF9, while its largest prime r is at least31. Apply that law
to the actual r-free original subfamily, retaining all cofactor query
depths. MF3, with the ENTIRE r-coordinate still Haar, proves

    min_y M_r(y)<26/(r-1)<=13/15<1.

Hence such a family cannot pass every complete marginal. This restricts
the all-marginals search; it is not an enlarged bare noncoverage range.
It does not provide the missing arbitrary eight-core query bound when
both3 and5 are present. Nor does it settle the transport, root orientation
or attachment obligations of
[Chapter73](../../docs/reports/erdos7-odd-covering/problem-details/73-missing-anchor-eight-core-source-audit.md),
whose candidate source rows serve a different block-gluing interface.

### Nine-support marginal feasibility also requires seven

The necessary condition in MF9 strengthens to: a family on exactly NINE
support primes passing every complete support-prime marginal must contain
ALL of3,5,7. The new sufficient common-law bound is

    p_i>=(3,5,11,13,17,19,23,29)_i, i=1,...,8
      ==> some actual complete-survivor law mu has R(mu)<51/2. (MF10)

All original residues and finite heights remain arbitrary. The law is
chosen before every query phase and controls every numerical query depth.
This uses the existing P3--P4 uniform-survivor profile and the same
product-source query comparison as MF9. The profile alone has envelope
sum45.3823269762... at the least tuple, which does not give MF10. Its
survivor mass, combined with a different query estimate, does.

For a prime subset S let lambda_S be the product of normalized Haar on
the ACTUAL complete pure-coordinate survivors. Write U_S for the complete
actual survivor and alpha_S=lambda_S(U_S). Conditioning lambda_S on U_S
gives precisely the uniform survivor law used by P3--P4: the product law
has constant density on its pure-survivor product, which contains U_S.

Let c_S be the P3--P4 profile, R(c_S) its full envelope sum, and
C_p=(p-1)/(p-2). If A=S\{p} and b_(A,p)=R(c_A)/(p-2)<1, first condition
lambda_A on U_A, then append lambda_p. All old-only and pure-p originals
are already absent. The remaining mixed originals have total mass at
most b_(A,p), by the same complete numerical-label sum used in P4. Thus

    alpha_S>=alpha_A*(1-b_(A,p)).

Define a_empty=1 and

    a_S=max_p a_(S\{p})*(1-R(c_(S\{p}))/(p-2)),   (MF11)

where the maximum is over admissible predecessor extensions. Then
alpha_S>=a_S by induction. Every order describes the same original
source and survivor, so no separately optimal laws are combined.
For this specific recurrence there is also the identity

    a_S=product_(p in S) C_p / c_S(S).             (MF12)

Indeed the full-support instance of P4 is
c_S(S)=min_p c_A(A)*C_p/(1-b_(A,p)); substitute the induction hypothesis.
MF12 is a consequence of that construction, not a way to recover a
pure-source mass lower bound from an arbitrary Haar density cap.

At the least tuple in MF10, exact rational evaluation of all256 subsets
gives

    a_S=0.016392818285728736...>2/125.

Use the independent auxiliary runs from MF9 on this tuple and put
M=product_p(1+J_p). For the integer threshold16, its COMPLETE hinge is

    h=E(M-16)_+
     =product_p(1+1/(p-2))-16
       +sum_(m=1..15)(16-m)*Pr(M=m)
     =0.16778042796244585...<21/125.               (MF13)

The atoms below16 are a finite multiplicative convolution of
Pr(J_p=0)=1-C_p/p and
Pr(J_p=j)=C_p*(p-1)/p^(j+1) for j>=1. The mean in MF13 includes the
entire infinite tail; omitting atoms at16 or above does not truncate it.
The existing exact profile verifier checks the reserve recurrence,
MF12 at every subset, these two strict rational bounds, and the hinge
convolution in both coordinate orders.

For every finite complete query layout L including the unit cylinder,
the product comparison gives E_lambda(L-16)_+<=h. For the ONE law
mu=lambda_S restricted to U_S, divided by alpha_S, it follows that

    E_mu(L-1)<=15+h/alpha_S
              <=15+h/a_S<15+(21/125)/(2/125)=51/2.

The fixed margin is independent of layout phases and depths. Maximizing
the phases after fixing mu, and then exhausting finite exponent boxes,
proves the all-depth bound in MF10 with its strict margin intact.

Increasing the ordered primes does not increase any profile coefficient
or envelope cost: use the indexed-subset induction from MF4--MF5.
Every formerly admissible extension remains admissible. MF11 therefore
has no smaller reserve, by another subset induction. The auxiliary run
tails decrease as well, so MF13 has no larger hinge. These comparisons
transport bounds to the new family's own law; they do not transport
individual residues or combine sources from different families.

An exactly-nine-prime support omitting7 has eight smaller primes
dominating the tuple in MF10 and largest prime r>=31. Apply MF10 to its
actual r-free family, including every required query depth. MF3 gives

    min_y M_r(y)<(53/2)/(r-1)<=53/60<1.           (MF14)

Together with MF9 this proves necessity of3,5,7. No feasible family on
the remaining supports is supplied. The arbitrary eight-core query
bound when all three primes are present remains unresolved here.
[Chapter69](../../docs/reports/erdos7-odd-covering/problem-details/69-eight-prime-cores-omitting-seven.md)
uses two exact omitted-seven cores in a different attachment interface;
MF10 does not assert its gluing or transport obligations. This is an
ordinary deduction and exact arithmetic verification, not a new Lean
result, a literature-originality claim, or an enlarged bare noncoverage
range for Erdős#7.


### Common-query source laws force the first six odd support primes

The nine-support necessary condition strengthens further: a family
passing every complete support-prime marginal must contain

    3,5,7,11,13,17.                                  (MF15)

This deduction uses the same attributed ordinary source-construction,
arbitrary-label convex-comparison and finite transport premises as
[Report461](../../docs/reports/erdos7-odd-covering/profile-notes/arithmetic/450-499/461-query-stop-loss-gives-a-common-law-six-core-completion-margin.md).
Those premises are not re-proved by the exact arithmetic consumer.
The original residues and all finite heights remain arbitrary.

Fix ONE finite period K on the eight core primes resolving the original
family and every cofactor query to be used. For a probability nu on its
actual complete survivors, write

    R_K(nu)=sum_(1<d|K) max_b nu(b mod d).

For each proxy below, every coordinatewise larger ordered eight-prime
core has one law chosen before the query phases, with the stated strict
bound. No compatibility between laws chosen for different K is claimed.

| Omitted prime | Eight-prime proxy | Fixed query threshold k | Source mass lower | Query bound |
| --- | --- | ---: | --- | ---: |
|11|3,5,7,13,17,19,23,29|8|10237584019/168750000000|R_K<14|
|13|3,5,7,11,17,19,23,29|8|13939935091/337500000000|R_K<18|
|17|3,5,7,11,13,19,23,29|16|12314552263/675000000000|R_K<27|
|19|3,5,7,11,13,17,23,29|18|6130736807/450000000000|R_K<34|

The exact rational query upper bounds are approximately
13.2626300884,17.0993737229,26.2093835488,33.3554002713, respectively.
The first three rows use source deletion schedule (2,4,4,8,8,12);
the missing19 row uses (2,4,4,8,12,16). At each nonanchor prime q
the cap is C_q=(q-1)/(q-1-t_q). The missing19 caps have product77/2.
The missing11 mass agrees with Chapter68's source calculation. Its
separate block attachment and graph-gluing assumptions are not used here.

Retain the normalized predeletion kernels as sigma, then restrict to
the same source survivor event to obtain mu<=sigma. For a complete
query layout L including the unit cylinder,

    mu(L-1)<=(k-1)*mu(1)+sigma((L-k)_+).              (MF16)

Report461's ordered-increment comparison includes ALL six nonanchor
coordinates in the auxiliary product M=product_q(1+J_q), where
Pr(J_q>=e)=C_q/q^e. These independent runs are comparison variables,
not independent actual source coordinates. Let pi(m)=Pr(M=m), A0 be
the relaxed anchor carrier mass in135-cell units, W its full linear
bound, and F(x) its safe anchor hinge bound. Then

    135*sigma((L-k)_+)<=N(k),
    N(k)=sum_(m<k) m*pi(m)*F(k/m)
         +(E M-sum_(m<k)m*pi(m))*W
         -k*(1-sum_(m<k)pi(m))*A0.                  (MF17)

The mean E M=product_q(1+C_q/(q-1)) is complete. For m>=k the anchor
load is at least one, so the remaining hinge is exactly linear and
the tail mass and first moment suffice. No infinite tail is dropped.
If D is the same anchor reserve minus its six source losses, then
mu(1)>=D/135>0 and normalization yields

    R_K(muhat)<=k-1+N(k)/D.                          (MF18)

The cached anchor bounds have threshold nodes x=t/m for
t in{2,4,8,12},1<=m<t. For additional source or query ratios, use
a nonnegative secant between adjacent cached nodes; include x=1
with bound W-A0. Beyond the largest node12, use F(12). The actual
hinge is convex and nonincreasing in x, so these are upper bounds.
Every fixed-node bound is convex in the continuous anchor parameter;
the secant coefficients depend only on x, hence preserve that
convexity. W is convex, A0 affine, and the coefficient of W in MF17
is nonnegative. Thus N(k) remains convex in the anchor parameter.

The same safe extension applies to source deletion losses, including
the missing19 stage t=16. Chapter31 SV16 permits every integer
1<=t_i<=q_i-2. With the preceding-coordinate multiplier in place of
M, the source loss is bounded by N_i(t_i)/(q_i-1-t_i), a convex
function of the same anchor parameter. All new thresholds satisfy
this source-kernel condition; the source and query bounds therefore
refer to one law throughout.

For each row, use ONE k at all32 anchor vertices and check, with its
coarse bound C,

    (C-k+1)*(reserve-source_losses)-N(k)>0.          (MF19)

The reserve is affine, the unrounded source losses are convex, and
C-k+1>=0, so the left side is concave and the vertex inequalities
extend over every anchor simplex. Upward-rounded losses only make
the vertex checks conservative; rounding itself is not asserted to
be convex. These are joint inequalities at one source parameter,
not separately attained numerator and denominator optima.

Report460's finite random prefix injections transport the bound to
larger actual primes: each pulled-back query is empty or retains its
numerical exponent vector. Construct and push forward unnormalized
source laws, average, then normalize once. The inequality
mu(L-1)<=C*mu(1) is linear before normalization. It therefore holds
for one transported law and all layouts on the chosen K.

If an exactly-nine-prime family omits11,13 or17, its largest prime
r>=31 and the other eight primes dominate the corresponding proxy.
Choose K to resolve the actual r-free originals AND all original
r-cofactor queries. MF3 gives a marginal strictly below
15/30,19/30 or28/30, respectively. Each is below one; combining these
exclusions with MF9--MF14 proves MF15. Finite K already suffices for
this implication; no inverse-limit law is needed.

For omission of19, every largest prime r>=37 now gives
min M_r<35/(r-1)<=35/36<1. Hence the largest prime must be31.
The only nine-prime odd support below or equal to31 that omits19 is

    (3,5,7,11,13,17,23,29,31).

The basic comparison alone leaves this last support unresolved and
supplies no actual family passing all marginals. The charged refinement
below excludes it; the four coarse bounds above remain valid.

The existing [query-hinge consumer](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/finite-prefix-sources/query_stoploss_completion.py)
with `--eight-core-marginals` reproduces the four rows using exact
rationals, the pinned source geometry and explicit geometric tails.
This is an ordinary deduction and numerical verification, not new
Lean verification, a literature-priority claim, or an enlarged bare
noncoverage range for Erdős#7.


### Charged continuation also forces the seventh odd support prime

The missing19 eight-prime proxy admits the stronger bound

    R_K(nuhat)<29,
    nu(1)>=1032241751/56250000000>0.                  (MF20)

Here K is any fixed finite carrier supported on these eight core primes
and resolving the actual eight-core originals and parent31 cofactor-query
heights. The same unnormalized source nu
is supported on their complete actual survivors and is chosen before
the queried residue phases on K. This uses the attributed completed
source, capped-kernel, arbitrary-label and finite-transport hypotheses
of MF15--MF19, with the matched positive charged continuation detailed
in [Report462](../../docs/reports/erdos7-odd-covering/profile-notes/arithmetic/450-499/462-the-final-stage-ledger-gives-a-seven-core-common-law.md#an-eight-core-law-closes-the-missing-19-parent31-comparison).
The original phases and heights remain arbitrary. No compatibility
between laws for different K is claimed.

Keep the fixed source thresholds (2,4,4,8,12,16), product of caps77/2,
and query18. The first7 padded deletion, current loss and reduced
zero-depth component belong to ONE actual source kernel. At later
stages the ordinary multiplier law minus11/14 times the law omitting7
is a nonnegative submeasure; its ordinary contribution and the
matched kappa-weighted zero component are added as positive terms.
Both source losses and the final query use this same continuation.

For one common affine reserve R, source-loss functional L and query
hinge H in135-cell units, the certificate proves

    D=R-L>0, 12D-H>0,
    R_K(nuhat)<=17+H/D<29.                           (MF21)

The complete domain comprises32 basic vertices,56 mixed five-vertex
charts and all280 physical7-projections at each of two remaining
vertices. Its866 terminal bounds are28 basic,278 mixed,554 coarse7,
four exact current7 and two charged-continuation bounds. The minimum
D is3096725253/1250000000. The worst vertex query upper is approximately
28.90982372331657; every displayed strict comparison is checked with
exact rationals. Interpolation applies to the SAME positive actual
functional, with fixed thresholds and query. Pointwise minima of
upper screens and upward-rounded costs are only vertex estimates;
their convexity is not assumed. All geometric tails remain included.

Apply MF3 with distinguished parent31 to the last missing19 support:

    min M_31< (1+29)/30=1.

Combining this exclusion with MF15 and the earlier exclusion for
largest prime at least37 proves that an exactly-nine-prime family
passing every complete support-prime marginal must contain

    3,5,7,11,13,17,19.                              (MF22)

This leaves the other nine-prime supports and the unrestricted problem
unsettled; it makes no assertion about families with ten or more
support primes. The [portable exact consumer](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/finite-prefix-sources/missing19_joint_prefix.py)
uses the pinned basic72 geometry batches plus102 required additional
batches, with source identity and MIT license retained. Its
[exact output](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/finite-prefix-sources/missing19_joint_prefix.json)
records the positive mass, slack and complete domain counts. These
are ordinary mathematical deductions and finite arithmetic, not new
Lean verification or a literature-priority claim.

### Unrestricted fractional phases only recover the reciprocal test

For a fixed nonempty inventory D of nonunit numerical labels, allow one probability vector z_(d,a)
over ALL phases a mod d of each original label. Use this same vector
in every prime marginal. If sum_(d in D)1/d>=1, choosing every vector
uniform makes each expected original indicator equal to 1/d at every
point; all expected complete marginals are then the constant
sum_d 1/d>=1. Conversely, averaging any feasible marginal over its
whole cofactor carrier forces that reciprocal sum to be at least 1.

Thus, without fixed phases or additional restrictions, feasibility of
this fractional relaxation is equivalent to the ordinary reciprocal
condition. Writing its full dual does not restore one actual phase
per original label. Restrictions such as fixed pure phases, a prescribed
hole excluded by every original, or integral common-phase choices must
be kept if the relaxation is to supply further arithmetic information.
