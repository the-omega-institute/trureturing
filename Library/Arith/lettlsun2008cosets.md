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

The [standard-library verifier](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/original_divisor_shell_reserves.py) constructs CRT residues and actual residue bitmasks from the formulas. The [exact data](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/original_divisor_shell_reserves.json) are reproduced by

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original_divisor_shell_reserves.py
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

The fixed1225-head results in[Report449](../../docs/reports/erdos7-odd-covering/profile-notes/arithmetic/449-equality-sources-have-a-private-law-below-nine.md) and these original-label global cuts preserve different parts of the problem. The head law has not been lifted through every original outside-cofactor constraint; the global cut has not been shown to be violated for every distinct odd inventory. No unrestricted noncoverage conclusion, polyhedral independence from every earlier subset cut, or literature-originality claim follows from this increment.

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

The [standard-library verifier](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/original_top_shadow_shell_pairs.py), with [exact data](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/original_top_shadow_shell_pairs.json), retains literal original labels and one uniform residue source per control. It checks the18-class inventory, every listed private witness, complete coverage counts, all class/lower/top slice identities, original-pair CRT capacities, private-region saving bounds, and top-shell intersection identities. The data include all2415 uncovered residues of the noncover, its six uncovered top7-neighbors, every displayed singleton ratio, and the period60 even-control comparisons. The odd top-shadow assertions are guarded by the oddness premise; the even control only records their actual truth values. All whole-cover controls still check the actual suppliers and shell-pair inequality.

Positive whole-cover controls are the complete residue partitions modulo3,25 and225. Their numerical moduli are REPEATED; they are not candidates for Erdős #7. They check the conditional collision and phase-excess conclusions, p-1 distinct actual suppliers, same-support pair counts and(TS8). For the full selected private union the top-shell pair inequalities are exact:1=1 for p=3 and6=6 for p=5 in the relevant controls. The ordinary proofs use numerical distinctness only to record distinct lower indices at fixed support, so these repeated-label controls legitimately exercise the stronger common-source identities without pretending to witness a distinct odd cover.

Reproduce the controls with:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original_top_shadow_shell_pairs.py
```
 These are exact finite controls and ordinary proofs; none is Lean verification or a proof that every unrestricted distinct-odd inventory violates a necessary inequality.
