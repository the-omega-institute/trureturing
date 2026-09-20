[Index](../../marked_head_profile.md) · [Original source corrections](346-old-cylinder-tree-gluing-and-source-corrections.md) · [Filaseta–Kalogirou source](../../../../../Library/Arith/filaseta2026reciprocalgap.md)

# Actual overlap leakage in the Lewis–Rogers prefix bound

The following ordinary proof uses Filaseta–Kalogirou, [arXiv:2407.15280v1](https://arxiv.org/pdf/2407.15280v1), Lemma 3 and the Euler-product estimate on page 24:

> Every finite covering system of distinct moduli greater than one whose original \(\{2,3\}\)-smooth subfamily leaves Haar density \(\Delta\ge1/12\) uncovered satisfies
> \[
> \sum_i\frac1{m_i}-1>5\cdot10^{-52}.
> \]

In particular it applies to a hypothetical distinct odd cover, including one with modulus 3: its distinct 3-power classes have total density less than \(1/2\), so \(\Delta>1/2\). Using that stronger initial density in the same analytic bounds gives
\[
\boxed{\text{distinct odd cover}\quad\Longrightarrow\quad
\sum_i1/m_i-1>2\cdot10^{-43}.}
\]
These are quantitative excess statements, not nonexistence of such a cover. The comparison below is with the inspected 2024 author version; the journal-version constants have not been compared.

Section 6 strengthens the all-odd consequence to excess and minimal-bucket
overlap greater than \(10^{-11}\), and to original overlap-union mass
greater than \(10^{-20}\). It removes the even-prime factors from both
the prefix estimate and the fourth-moment tail proof. The general
\(\Delta\ge1/12\) statement above retains its original scope.

The constants in Sections 2–3 also hold for a smaller, localized quantity: the sum, over primes \(5\le p<p_N\), of the Haar mass where an original division-minimal \(p\)-bucket class meets an earlier-prime original class. Here \(N=1532030200000000000000\). Thus a hypothetical odd cover forces this cross-prime overlap sum to exceed \(2\cdot10^{-43}\), and the union of these overlap events has Haar mass greater than \(10^{-64}\). Internal repetition within one prime bucket cannot supply this required overlap. Sections 2–3 give the refinement without any irredundancy assumption.

## 1. One stage on the original Haar law

Fix the current prime \(p\). All classes in the current bucket have distinct \(p\)-smooth moduli divisible by \(p\), and \(O\) is the union of earlier-prime classes. Let
\[
B=\bigcup_{i\text{ current}}C_i,\qquad
S=\sum_{i\text{ current}}\frac1{m_i},\qquad
U=\mu(O^c).
\]
All measures use one complete original CRT period and its Haar probability \(\mu\). Choose those original current moduli \(m_j\) minimal under divisibility within the current bucket, and put
\[
B_{\min}=\bigcup_jC_j,\qquad
E_j=\{n\equiv a_j\pmod{m_j/p}\},\qquad E=\bigcup_j E_j.
\]
These are expansions of the selected original classes, not new original labels. Write
\[
M_p=\frac1{p-1}\prod_{q<p}\frac q{q-1},\quad
u=\mu(B_{\min}\cap O),\quad v=\mu(B\cap O),\quad
r=S-\mu(B)\ge0.
\]

The denominator-ideal step and Rogers comparison in FK, pp. 10–11, imply
\[
\boxed{S\le M_p\mu(E).}\tag{1}
\]
This part does not require disjointness. Indeed every current modulus is a multiple of one division-minimal original modulus. The sum of reciprocals over the complete \(p\)-smooth upward ideal is, by finite inclusion–exclusion and the convergent smooth Euler product,
\[
M_p\,\mu\left(\bigcup_j\{0\bmod(m_j/p)\}\right).
\]
Rogers' union-density comparison bounds this centered union above by the actual shifted union \(E\). The distinctness of original moduli is what permits \(S\) to be bounded by the ideal sum with each modulus counted once. The disjointness premise in FK's displayed (15) was used only for the separate identification \(\mu(B)=S\).

The union-density comparison also has a direct proof on the finite CRT carrier. Fix all coordinates except one prime coordinate. The active classes in that coordinate are prime-power prefixes, so their union has mass at least the largest individual mass. Moving all their residues to zero makes them nested, and their union has exactly that largest mass. This does not increase the union at any setting of the other coordinates. Integrating and repeating over every prime coordinate proves the centered-union inequality for arbitrary original residues. No pairwise disjointness is assumed.


For one class, because \(O\) is \(p\)-free,
\[
\mu(E_j\cap O)=p\mu(C_j\cap O).
\]
For the union, there is the stronger-than-label-sum bound
\[
\boxed{\mu(E\cap O)\le p\mu(B_{\min}\cap O)=pu.}\tag{2}
\]
To prove it at a fixed old point, take the active literal \(p\)-prefixes of the selected original classes. Keep their inclusion-maximal sets (the shortest surviving prefixes). They are disjoint. Removing a contained prefix does not change the expanded union, since the parent operation preserves containment. The union of their parents has mass at most the sum of parent masses, which is \(p\) times the original disjoint-union mass. Integrate this inequality on the old set \(O\). This works with varying original \(p\)-heights; it does not assert that all expansions arise from one common digit-erasure projection.

The exact survivor update is
\[
U_{\rm new}=U-\mu(B)+v=U-S+r+v.
\]
Combining (1), (2), and \(\mu(E)\le U+\mu(E\cap O)\) gives
\[
\boxed{U_{\rm new}\ge(1-M_p)U-pM_pu+v+r.}\tag{3}
\]
The original overlap already paid inside \(O\) must be returned in this subtraction. In particular, with \(e=v+r\) and \(u\le v\le e\),
\[
\boxed{U_{\rm new}\ge(1-M_p)U-(pM_p-1)e.}\tag{4}
\]
Retaining the different kinds of overlap gives the stronger form
\[
\boxed{U_{\rm new}\ge(1-M_p)U-(pM_p-1)u
       +(v-u)+r.}\tag{4a}
\]
Both correction terms \(v-u\) and \(r\) are nonnegative. In particular,
\(U_{\rm new}\ge(1-M_p)U-(pM_p-1)v+r\): internal multiplicity within the current bucket has a favorable sign, unlike overlap with the earlier union.
One can retain further measurable slack. For \(h=\mu(O^c\setminus E)\) and \(\lambda=\mu(E\cap O)\), (1) gives
\[
U_{\rm new}\ge(1-M_p)U+M_ph-M_p\lambda+v+r.
\]
No later argument requires discarding the nonnegative corrections; (4) is a convenient uniform relaxation.

## 2. The excess budget is shared exactly across prime stages

Process the complete original family by largest prime factor. At stage \(p\), let \(O_p\) be the actual union of every earlier bucket and define \(e_p\) as above. Then
\[
e_p=S_p-\mu(B_p\setminus O_p).
\]
The new-coverage sets \(B_p\setminus O_p\) are disjoint and partition the total union. Consequently
\[
\sum_p e_p
=\sum_i\frac1{m_i}-\mu\left(\bigcup_i C_i\right)
=\int (L-1)_+\,d\mu,
\]
where \(L\) is the actual original covering multiplicity. For a whole cover this is exactly
\[
H_{\rm cov}=\sum_i\frac1{m_i}-1.
\]
This is not the head's effective source parameter \(\rho\). No multiplicity, old state or original label is replaced by an independent copy.

Let \(p_i\) be the \(i\)-th prime and take \(i=3,\ldots,N-1\), starting with the complete \(\{2,3\}\)-smooth original family, so \(U_2=\Delta\). Empty buckets are permitted. For \(i\ge3\), \(0<M_{p_i}<1\): the first value is \(M_5=3/4\), and successive values have ratio \(p_i/(p_{i+1}-1)<1\). Furthermore
\[
A_i=p_iM_{p_i}-1=\prod_{q\le p_i}\frac q{q-1}-1
\]
is increasing. Iterating (4) and using \(\sum_{i=3}^{N-1}e_{p_i}\le H_{\rm cov}\) yields
\[
\boxed{U_{N-1}\ge
\Delta\prod_{i=3}^{N-1}(1-M_{p_i})-A_{N-1}H_{\rm cov}.}\tag{5}
\]
The complete original smooth buckets are used here, with all actual exponent heights and no modulus cutoff \(K\).

### A smaller budget: overlap between different prime buckets

At a point \(x\), let \(L(x)\) count all original classes containing \(x\), and let \(K(x)\) count the prime buckets whose unions contain \(x\). There is no multiplicity inside \(K\): each largest prime is counted at most once. Direct pointwise accounting gives, for any family, whether or not it covers,
\[
\sum_p v_p=\int(K-1)_+\,d\mu,\qquad
\sum_p r_p=\int(L-K)\,d\mu.
\]
Their sum is the earlier excess identity. The same identities hold on an initial segment, with \(L,K\) counting only that segment's classes. Thus repeatedly covering a point with classes from one bucket increases only the second account.

For \(3\le i<N\), write
\[
W_i=\prod_{j=i+1}^{N-1}(1-M_{p_j}),\qquad
b_i=(v_{p_i}-u_{p_i})+r_{p_i}\ge0,\qquad
T_{<N}=\sum_{i=3}^{N-1}u_{p_i}.
\]
Iterating (4a), instead of discarding all overlap distinctions in (4), proves
\[
U_{N-1}\ge\Delta\prod_{i=3}^{N-1}(1-M_{p_i})
 -\sum_{i=3}^{N-1}A_iW_i u_{p_i}
 +\sum_{i=3}^{N-1}W_i b_i.
\tag{5a}
\]
Since \(0<W_i\le1\) and \(A_i\le A_{N-1}\),
\[
\boxed{U_{N-1}\ge\Delta\prod_{i=3}^{N-1}(1-M_{p_i})
       -A_{N-1}T_{<N}.}\tag{5b}
\]
Here \(T_{<N}\le\sum_{i=3}^{N-1}v_{p_i}\le H_{\rm cov}\) for a whole cover. The classes defining each \(u_p\) are the division-minimal original classes of that same bucket; they are not contracted substitutes. Redundant original classes are allowed throughout.

## 3. The same FK tail law supplies a numerical gap

Use the distortion parameters of FK Lemma 1:
\[
\delta_i=0\quad(i<N),\qquad
\delta_i=95007347/1520117553\quad(i\ge N).
\]
The FK kernels preserve old marginals, and the initial zero parameters give exactly the full Haar law \(P_{N-1}=\mu\) (FK pp. 3–5). Hence under the final distorted law the union of the complete early buckets has probability \(1-U_{N-1}\). A whole cover therefore implies
\[
U_{N-1}\le\sum_{i=N}^{\infty}P_i(B_i).\tag{6}
\]
Only finitely many buckets are nonempty. If the original carrier has fewer prime coordinates, append zero-height coordinates; this changes no event or probability. FK's fourth-moment tail bound (9) and Lemmas 1–3 range over all actual original moduli and all heights, without a \(K\) restriction or an early disjointness hypothesis.

Take the integer
\[
N=1.5320302\cdot10^{21}=1532030200000000000000.
\]
FK Lemma 3, p. 7, states at \(\Delta=1/12\) that
\[
\frac1{12}\prod_{i=3}^{N-1}(1-M_{p_i})
-\sum_{i=N}^{\infty}P_i(B_i)
>4.7596769\cdot10^{-50}.\tag{7}
\]
For any actual \(\Delta\ge1/12\), the same bound holds with \(\Delta\) in place of \(1/12\). Combining (5)–(7) gives
\[
A_{N-1}H_{\rm cov}>4.7596769\cdot10^{-50}.\tag{8}
\]
No small-modulus pair-disjointness premise and no smooth-modulus tail cutoff are used.

The same inspected source, p. 24 immediately before (36), explicitly gives, for this same \(N=1.5320302\cdot10^{21}\),
\[
\prod_{j=1}^{N}\left(1+\frac1{p_j-1}\right)<94.
\]
Thus \(A_{N-1}<93\). The exact rational comparison
\[
93\,(5\cdot10^{-52})=4.65\cdot10^{-50}
<4.7596769\cdot10^{-50}
\]
and (8) prove
\[
\boxed{H_{\rm cov}>\frac{4.7596769\cdot10^{-50}}{93}
>5\cdot10^{-52}.}
\]
The product bound, like the Lemma 3 reserve, is a cited quantitative input. A weaker bound \(10^{-73}\) follows without the source's Euler-product estimate, using its prime bound as follows.

The deliberately coarse coefficient bound is
\[
A_{N-1}+1
=\prod_{q\le p_{N-1}}\frac q{q-1}
\le\prod_{n=2}^{p_{N-1}}\frac n{n-1}=p_{N-1}<p_N.
\]
The universal prime bound quoted in FK (23), for \(n\ge20\), is
\[
p_n<n(\log n+\log\log n-1/2).
\]
For this \(N\), \(\log N<50\) and \(\log\log N<4\), whence
\[
p_N<(107/2)N<10^{23}.
\]
These two logarithmic estimates can be certified using only rational powers: \(e>8/3\), \((8/3)^{50}>N\), and \((8/3)^4>50\). Therefore (8) proves
\[
\boxed{H_{\rm cov}>4.7596769\cdot10^{-73}>10^{-73}.}
\]

The imported quantitative ingredients are the published Lemma 3 bound (7) and the product bound on p. 24; a finite verifier of the rational bridge does not independently recompute the paper's billion-prime calculations. The additional argument is the overlap-sensitive prefix recurrence and its exact global accounting. Independent ordinary-proof review checked these interfaces. No Lean declaration, build, deposit or kernel certification is asserted here.


### The stronger initial density for odd moduli

Keep exactly the same integer \(N\), distortion parameters and Euler-product bound. In FK Section 6, Lemmas 1–2 are combined for **every** \(\Delta>0\); the density \(1/12\) specifies one numerical substitution, not an additional hypothesis of those analytic estimates. Set
\[
\begin{aligned}
\tau_1&=N(\log N+\log\log N-3/2),\\
\tau_2&=N(\log N+\log\log N-1/2),\\
T&=\frac{0.657743(\log\tau_2)^{16}}{\tau_2^3},\\
F_0&=\frac{5.8478233}{12}
\frac{\tau_1^{1.2173619}}{(\log\tau_1)^{16}}
\exp\!\left(-\frac{0.8913191}{\log\tau_1}\right).
\end{aligned}
\]
The source equation (24) bounds the reserve at \(\Delta=1/12\) below by \(T(F_0-1)\). An odd family has \(\Delta>1/2\), so the same analytic formula instead gives the strict lower bound \(T(6F_0-1)\). Only the positive prefix term is multiplied by six; the subtracted tail is unchanged.

The rational interval calculation below verifies
\[
\frac{T(6F_0-1)}{93}>2\cdot10^{-43}.
\]
Consequently (5)–(6) and \(A_{N-1}<93\) prove
\[
\boxed{\sum_i1/m_i-1>2\cdot10^{-43}}
\]
for every finite distinct odd cover with all moduli greater than one. The page-24 product depends only on the fixed \(N\), so it applies unchanged. The general \(\Delta\ge1/12\) bound above is retained.

### Localized numerical consequence

Substitute (5b) for (5) in exactly the same tail argument (6). The positive reserve now forces
\[
A_{N-1}T_{<N}>4.7596769\cdot10^{-50}
\]
in the general case, and \(A_{N-1}T_{<N}>T(6F_0-1)\) in the odd case. Consequently
\[
\boxed{T_{<N}>5\cdot10^{-52}\quad(\Delta\ge1/12),\qquad
       T_{<N}>2\cdot10^{-43}\quad\text{(odd cover)}.}
\tag{9}
\]
No new analytic input or numerical optimization is used. The favorable terms in (5a) can only increase the required weighted overlap.

Define the actual original overlap event
\[
G_{<N}=\bigcup_{i=3}^{N-1}(B_{\min,p_i}\cap O_{p_i}).
\]
There are \(N-3\) terms, so \(T_{<N}\le(N-3)\mu(G_{<N})\). Since
\((N-3)10^{-64}<2\cdot10^{-43}\), an odd cover satisfies
\[
\boxed{\mu(G_{<N})>10^{-64}.}\tag{10}
\]
Every point counted here lies in two original classes with different largest prime factors, both below \(p_N\). The moduli themselves still have arbitrary heights; a bound on largest prime factor is not a bound on modulus. The mass in (10) concerns a union of overlaps, not a selected pair or a multiplicity-weighted expectation.

This localization also states the transport obstruction precisely: at a \(p\)-stage, \(B_{\min,p}\cap O_p\) has zero mass under a law supported on the actual earlier survivor \(O_p^c\). A lower bound under original Haar therefore supplies no positive mass under that killed law. A separate relation to surviving completions is still required.

## 4. Reproducible checks and limits

The [geometry checker](../../frontier/cover-geometry/original_overlap_leakage.py) constructs original residue classes on their complete finite Haar periods. It checks the expanded-prefix union inequality, the denominator-ideal/Rogers bound, an exact identity retaining all discarded slacks, both versions of the overlap recurrence, and the distinct cross-prime/internal-multiplicity accounts. It also checks the iterated minimal-class budget against direct surviving sets. Its current fixtures contain 397 single-stage families and 73,885 period points, followed by 150 stage decompositions over 222,180 period points and 300 localized recurrence checks. A separate implementation checks 82 families, including 46 with redundant original classes, over 727,083 period points. These finite checks support implementation and detect counterexamples; the general argument in Sections 1–3 supplies the unbounded quantifiers.

The [rational interval checker](../../frontier/source-budgets/reciprocal_gap_source_interval.py) independently encloses the source equation (24) using logarithm and exponential series with rigorous remainder bounds and outward rational rounding. It returns a lower endpoint greater than \(4.7596769\cdot10^{-50}\). This recomputes the final numerical substitution conditional on the paper's analytic Lemmas 1–2 and prime bounds; it does not replay the paper's earlier large prime calculations. The page-24 Euler-product upper bound remains a cited analytic input. The final comparison \(93(5\cdot10^{-52})<4.7596769\cdot10^{-50}\) uses exact rational arithmetic. A separate interval computation for \(T(6F_0-1)\) gives a lower endpoint exceeding \(2.30481519943514\cdot10^{-41}\); division by 93 exceeds \(2\cdot10^{-43}\). It keeps all analytic inputs and parameters fixed.

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original_overlap_leakage.py
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/source-budgets/reciprocal_gap_source_interval.py
```

The comparison is with the inspected author version's \(\exp(-3.363054\cdot10^{21})\) bound. The journal DOI is 10.1090/tran/9670, but its PDF returned HTTP 403 during this check; no claim about priority or improvement over uninspected versions is made. The cited source is credited for the distortion method, analytic tail bounds and Rogers/Lewis ingredients.

This conclusion supplies a uniform cross-prime original-overlap lower bound, hence an excess lower bound, for every hypothetical distinct odd cover, including arbitrary prime-power heights. It supplies no conflicting upper bound and is not a proof of noncoverage. In particular, neither \(T_{<N}\) nor \(H_{\rm cov}\) can be replaced by the effective source parameter \(\rho\) or by excess under a killed or conditioned law. Such transport still needs its own argument.

## 5. Two excess-reduction operations do not preserve the hypotheses

An implication from one hypothetical distinct odd cover to such covers with excess tending to zero would contradict the uniform bound. The following two operations do not establish that implication. The restriction map reuses [341's literal affine pullback](341-conditional-future-avoidance-controls-the-current-prefix.md); the template obstruction reuses [336's primitive-character argument](336-maximal-label-fourier-overlap-and-uncovered-density.md), rather than asserting a new exact-cover theorem.

### Restriction and genuine residual-modulus collisions

Restrict original classes \(r_i\bmod m_i\) to \(a+d\mathbb Z\). A label is active exactly when \(g_i=\gcd(d,m_i)\) divides \(r_i-a\); its residual modulus is \(n_i=m_i/g_i\). On the same original Haar carrier, enlarged to a common period with \(d\) if necessary, put
\[
h_a=\sum_{i\text{ active}}1/n_i-1.
\]
Disintegration gives \(d^{-1}\sum_{a\bmod d}h_a=H_{\rm cov}\). Under whole coverage each \(h_a\ge0\), but a fibre with \(h_a\le H_{\rm cov}\) need not retain distinct nonunit moduli.

For a fixed fibre, let \(s_n\) count active labels of residual modulus \(n\), and \(k_n\) count their distinct residual residues. The mass removed by deduplicating identical events is
\[
D=\sum_n(s_n-k_n)/n.
\]
Retaining one residue at each available residual modulus additionally removes label mass
\[
C=\sum_{n:k_n>0}(k_n-1)/n.
\]
For any such selector, let \(U_{\rm sel}\) be its uncovered fraction and \(E_{\rm sel}\) its positive multiplicity excess. Its signed mass identity is exactly
\[
\boxed{U_{\rm sel}-E_{\rm sel}=C-(h_a-D).}
\]
If the original fibre covers, deduplication preserves coverage, so \(0\le D\le h_a\) and
\[
\max(0,C-h_a+D)\le U_{\rm sel}\le C.
\]
The upper bound follows because every newly uncovered point belongs to a deleted event. Thus collision deletion can create holes even when the original conditional excess is zero.

For an explicit original odd family, take
\[
0\bmod3,\qquad10\bmod15,\qquad50\bmod75.
\]
The classes are disjoint and each has a private point; their total covered density is \(31/75\). On the actual fibre \(0\bmod25\), writing \(x=25k\) gives exactly \(0,1,2\bmod3\). Here \(h_a=D=0\), \(C=2/3\), and every distinct-modulus selector leaves \(2/3\) uncovered. This family is globally a noncover. It refutes charging these collision deletions to existing overlap without a further hypothesis; it does not refute a claim that uses whole original odd coverage.

### Exact finite templates with a common inserted modulus set

Let a finite exact partition of \(\mathbb Z\) into odd-modulus progressions consist of retained classes and holes. Assume the retained moduli are pairwise distinct. Insert in every hole a covering family with the same nonempty set of distinct odd moduli \(\{m_i\}\), all greater than one, and exactly one class for each modulus. Different residues or affine automorphisms in different holes are allowed. A hole \(b\bmod D\) produces classes of moduli \(Dm_i\).

Every nontrivial such template produces repeated output moduli. Indeed, let \(M>1\) be the largest template modulus. Averaging the exact-cover multiplicity against a primitive \(M\)-character kills every smaller modulus, and gives
\[
\sum_{\text{template cells of modulus }M}e^{2\pi i a/M}=0.
\]
One summand cannot vanish, and two cannot cancel because \(-1\) is not an odd-order root of unity. Therefore at least three template cells have modulus \(M\). At most one is retained, so at least two holes have that modulus. Each inserted \(m_i\) consequently yields two distinct classes of modulus \(Mm_i\), lying in disjoint holes. Changing their residues cannot remove this collision. A one-cell template is either the inadmissible retained modulus 1 or a single unit-modulus hole, which leaves the input excess unchanged.

If the total hole density is \(\delta\), the output really does have excess \(\delta H_{\rm cov}\), with its repeated labels counted. For example, retaining \(1,2\bmod3\) and filling \(0\bmod3\) gives \(H_{\rm cov}/3\) but repeats retained modulus 3. Retaining \(0\bmod3\) and filling both other holes gives \(2H_{\rm cov}/3\) but repeats every inserted modulus \(3m_i\). The excess identity is valid; its output does not satisfy the distinctness hypothesis. Different inserted modulus sets or a globally coordinated deletion require their own proof and are not ruled out here.

The standalone [collision checker](../../frontier/cover-geometry/overlap_reduction_collisions.py) verifies the affine membership, all three disintegrations (signed excess, positive excess, and holes), and every selector on five fixtures: 522 complete-period points and 94 selectors. Four ternary transformations are checked at all 162 output-period points. The whole-cover fixtures are explicitly either a distinct cover with even moduli or an odd cover with repeated moduli; none is represented as a distinct odd cover. The general finite-template obstruction is the ordinary Fourier deduction above, not a conclusion inferred from those examples.

For the restricted covering problem, a sufficient interface must therefore preserve both residual covering behavior and the original-to-residual modulus collision relation. Recovering only the conditional covering fraction or its excess does not certify an admissible distinct-modulus continuation.

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/overlap_reduction_collisions.py
```

## 6. Odd-only ideals and fourth moments strengthen the uniform gap

For every hypothetical finite covering family of pairwise distinct odd
moduli greater than one, the same original Haar law satisfies
\[
\boxed{H_{\rm cov}\ge T^{\rm odd}_{<10^9}>10^{-11},
\qquad \mu(G^{\rm odd}_{<10^9})>10^{-20}.}
\tag{11}
\]
Here, with the prime indexing of Section 2,
\[
T^{\rm odd}_{<N}=\sum_{i=3}^{N-1}
 \mu(B_{\min,p_i}\cap O_{p_i}),\qquad
G^{\rm odd}_{<N}=\bigcup_{i=3}^{N-1}(B_{\min,p_i}\cap O_{p_i}).
\]
The classes defining these events are the same division-minimal original
classes used above. Every prime in these overlap events is less than
\(25\cdot10^9\). This bounds largest prime factors, not original moduli:
all original exponent heights and redundant classes remain allowed.

### Odd upward ideals on the original Haar carrier

Because all original moduli are odd, the upward ideal in Section 1 needs
only odd \(p\)-smooth multiples. The factor for the prime 2 disappears:
\[
m_p=\frac1{p-1}\prod_{3\le q<p}\frac q{q-1}=\frac{M_p}{2}.
\]
Inclusion–exclusion on the same division-minimal moduli gives the exact
odd ideal sum \(m_p\mu(E_{\rm centered})\). Indeed an intersection of
upward ideals has least modulus equal to the least common multiple of its
generators; its reciprocal sum is that modulus's reciprocal times
\(\prod_{3\le q\le p}q/(q-1)\). The centered expanded class has
\(p\) times the generator's reciprocal mass, giving the coefficient
\(m_p\). The finite original sum counts each modulus at most once and
is bounded by this convergent ideal sum. Rogers' comparison, still on
the original Haar carrier, therefore gives
\[
S\le m_p\mu(E).
\]
The expanded-prefix inequality \(\mu(E\cap O)\le pu\) is unchanged.
Consequently the overlap recurrence becomes
\[
U_{\rm new}\ge(1-m_p)U-(pm_p-1)u+(v-u)+r.
\tag{12}
\]
For \(p\ge5\), both \(m_p\in(0,1)\) and
\[
A_p^{\rm odd}:=pm_p-1
  =\prod_{3\le q\le p}\frac q{q-1}-1>0
\]
hold; the latter is increasing in \(p\). Iteration, with the same
nonnegative rebates as in (5a), gives
\[
U_{N-1}\ge\Delta\prod_{i=3}^{N-1}(1-M_{p_i}/2)
              -A_{p_{N-1}}^{\rm odd}T^{\rm odd}_{<N}.
\tag{13}
\]
The odd pure 3-power family has \(\Delta>1/2\). For \(0\le x<1\),
\((1-x/2)^2\ge1-x\), so FK Lemma 2 implies, for every \(N\ge10^9\),
\[
\Delta\prod_{i=3}^{N-1}(1-M_{p_i}/2)
>
\frac{\sqrt{3.84636486599}}{2p_N^{0.89131905}}
\exp\!\left(-\frac{0.44565955}{\log p_N}\right).
\tag{14}
\]
The initial density \(1/2\) is outside the square root. No original
Haar quantity is replaced by a survivor-conditioned law in (12)–(14).

### The odd fourth-moment tail omits a factor of 150

Use FK's original schedule \(\delta_i=0\) before \(N\) and
\(\delta_i=95007347/1520117553\) afterwards. In its fourth-moment
estimate (6), all four old cofactors divide the odd original period.
Thus in (7) the sum may be extended over odd smooth integers only. In
the Euler product (8), the factor for \(q=2\) is omitted. Since
\(p_1=2\) and \(\delta_1=0\), that omitted factor is exactly
\[
1+\frac{15\cdot2^3+5\cdot2^2+5\cdot2-1}{(2-1)^4}=150.
\]
Every remaining factor, including every positive threshold, is unchanged.
Accordingly the right-hand side of (9) is divided by 150 for each
\(i\ge N\). In the proof of Lemma 1, equations (18)–(21) bound this
Euler product multiplicatively, and the subsequent tail summation is
positive and linear in its constant. The same proof therefore yields
\[
\sum_{i\ge N}P_i(B_i)
 \le\frac{0.657743}{150}\frac{\log^{16}p_N}{p_N^3},
\qquad N\ge10^9.
\tag{15}
\]
This division uses the restricted cofactor sum and the proof of Lemma 1;
dividing that lemma's conclusion alone would not justify it. The
published prime estimates and large finite-product inputs remain cited
inputs. Empty buckets and zero-height even coordinates cause no change.

### One fixed index gives an exact numerical certificate

Fix \(N=10^9\). Since it is below
\(N_0=1532030200000000000000\), the same page-24 product bound used in
Section 3 gives
\[
A_{p_{N-1}}^{\rm odd}<94/2-1=46.
\]
Use the source prime bounds (23), rather than requiring the exact value
of the billionth prime:
\[
\tau_-=N(\log N+\log\log N-3/2)<p_N
 <\tau_+=N(\log N+\log\log N-1/2).
\]
The right-hand side of (14), as a function of \(p_N\), decreases when
\(1.7826381-0.8913191/(\log p_N)^2>0\). The function
\(\log^{16}p_N/p_N^3\) decreases when \(\log p_N>16/3\).
Both conditions hold throughout these prime bounds. Define
\[
R=\frac{\sqrt{3.84636486599}}{2\tau_+^{0.89131905}}
 \exp\!\left(-\frac{0.44565955}{\log\tau_+}\right),\qquad
F=\frac{0.657743}{150}\frac{\log^{16}\tau_-}{\tau_-^3}.
\]
The extended rational interval checker certifies
\[
\begin{aligned}
R-F&>5.49724440508628\cdot10^{-10},\\
(R-F)/46&>1.19505313154049\cdot10^{-11}>10^{-11},\\
(R-F)/[46(N-3)]&>1.19505313512565\cdot10^{-20}>10^{-20},\\
\tau_+&<25\cdot10^9.
\end{aligned}
\tag{16}
\]
The displayed decimals are rounded down from verified rational lower
endpoints. The checker uses only integer and rational interval operations
with explicit logarithm and exponential remainders; it also checks both
monotonicity conditions.

Before \(N\), the actual distorted law is exactly original Haar.
Under whole coverage the tail must cover all of its remaining mass,
so (6), (13)–(15) give
\[
46T^{\rm odd}_{<N}>R-F.
\]
The pointwise overlap accounting of Section 2 gives
\(H_{\rm cov}\ge T^{\rm odd}_{<N}\), and the union bound on the
\(N-3\) overlap events gives
\(T^{\rm odd}_{<N}\le(N-3)\mu(G^{\rm odd}_{<N})\).
These prove (11) and the stated prime range.

The geometry checker now additionally checks the odd ideal and its
signed slack identity on 397 original families, and the odd iterated
recurrence on 300 prefix steps. These finite checks do not supply the
unbounded quantifiers; those follow from the ideal, prefix and tail
arguments above. The interval checker does not recompute FK's large
prime products or certify the source lemmas. Neither checker is a Lean
proof. This is an odd-family specialization and extension of the cited
method, with no claim about priority over uninspected literature.

The stronger lower bound still has no conflicting upper bound on the
same overlap quantity. It therefore excludes low-overlap hypothetical
covers but does not resolve Erdős #7. The overlap events remain outside
the actual earlier survivor at their own prime stage; the source
transport limitation after (10) still applies.

## 7. A bounded pair of original moduli must already intersect

Every hypothetical finite odd distinct cover has two intersecting
original classes whose two numerical moduli are both less than
\(10^{718}\). In fact, put \(P=25\cdot10^9\) and \(K=P^{69}\).
There are two intersecting original classes with distinct moduli
\(m_1,m_2\le K<10^{718}\), and their largest prime factors are
different and both less than \(P\). No bound is asserted on the other
original moduli.

This is the bounded-pair target of the cited FK argument, now using the
odd overlap-union bound (11) and an elementary smooth reciprocal tail.
The comparison is with its inspected author-version cutoff
\(\exp(1.681527\cdot10^{21})\), not with uninspected later literature.

Let \(\mathcal S_P\) be all positive odd integers whose prime factors
are at most \(P\), and take
\[
r=\frac{13}{5},\qquad
\sigma=\frac{\log r}{\log P}\in(0,1).
\]
For every odd prime \(q\le P\), \(q^\sigma\le r<3\le q\).
With \(x=1/q\le1/3\), the exact five-term calculation gives
\[
1-(1-x)^5
 =x\sum_{j=0}^4(1-x)^j
 \ge x\sum_{j=0}^4(2/3)^j
 =\frac{211}{81}x>rx.
\]
All factors below are positive, so
\[
\prod_{\substack{q\le P\\q\text{ odd prime}}}
 (1-q^{-1+\sigma})^{-1}
\le\prod_{\substack{q\le P\\q\text{ odd prime}}}(1-r/q)^{-1}
<\left(\prod_{\substack{q\le P\\q\text{ odd prime}}}
          (1-1/q)^{-1}\right)^5<47^5.
\tag{17}
\]
For the last step use the same cited Euler product below 94 at
\(N_0=1532030200000000000000\), and remove its factor 2. Its range
includes all primes through \(P\): the elementary bound
\(p_{N_0}\ge N_0+1>P\) suffices. This range check is separate from
the earlier upper bound on \(p_{10^9}\).

There are finitely many primes through \(P\). Expanding their convergent
geometric series in (17) includes every possible original exponent height.
For \(m>K\), \(m^{-1}\le K^{-\sigma}m^{-1+\sigma}\), whence
\[
\sum_{\substack{m\in\mathcal S_P\\m>K}}\frac1m
\le K^{-\sigma}\sum_{m\in\mathcal S_P}m^{-1+\sigma}
<47^5r^{-69}<10^{-20}.
\tag{18}
\]
The usual positive-power weighting of the reciprocal tail, often called
Rankin's bound, is proved here by the displayed termwise inequality.
Both numerical comparisons are exact integer inequalities:
\[
47^5\,5^{69}\,10^{20}<13^{69},\qquad
(25\cdot10^9)^{69}<10^{718}.
\tag{19}
\]
They and the five-term comparison are checked by the existing geometry
checker; no numerical logarithms or enumeration of primes through \(P\)
are required for (17)–(19).

Let \(V\) be the union of original classes with \(P\)-smooth moduli
greater than \(K\). The same original Haar law and original numerical
distinctness give
\[
\mu(V)
\le\sum_{\substack{\text{original }i\\m_i>K,
                     \ m_i\in\mathcal S_P}}\frac1{m_i}
\le\sum_{\substack{m\in\mathcal S_P\\m>K}}\frac1m
<10^{-20},
\]
whereas (11) gives \(\mu(G^{\rm odd}_{<10^9})>10^{-20}\).
Choose an actual period point in \(G^{\rm odd}_{<10^9}\setminus V\).
It lies in a division-minimal original class of one early prime bucket
and in an original class of an earlier bucket. These are distinct,
intersect at the chosen point, and have different largest prime factors
less than \(P\). Neither modulus exceeds \(K\), since otherwise that
point would lie in \(V\). Thus the same pair satisfies all the claimed
bounds. No original label is discarded and no derived moduli are merged.

The result does not make a bounded search over all covering families
sufficient: only one intersecting pair is bounded, and all other labels
may still have arbitrary moduli. Its intersection need not carry the
whole aggregate overlap lower bound. It gives another necessary
condition for a hypothetical cover, not a contradiction to every such
cover or a resolution of Erdős #7.
