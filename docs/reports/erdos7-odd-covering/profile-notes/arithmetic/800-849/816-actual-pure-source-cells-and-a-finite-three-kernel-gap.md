# Actual pure-source cells and a finite three-kernel gap

Normalized Haar measure on the survivor of actual pure-prime originals has a smaller first-digit domain than the inherited cap polytope. At 5 the minimal closed convex outer sets for the four structural cases are two segments and two triangles. At each of the six other observed primes, the projected outer domain has two convex components. Their product has 256 cells and a menu of 7290 vertices.

This excludes the relaxed interior counterpoint in [Report814](814-three-kernels-cover-all-source-vertices-but-miss-a-strict-interior-point.md) as an actual pure-Haar source. Nevertheless, one explicit family of 46 distinct odd originals gives an actual pure source at which all three of Report814's fixed tables have a negative inherited h16 gate. Thus removing unrealizable source points does not repair that particular three-table collection.

These are ordinary mathematical results with exact rational verification, not Lean results or a resolution of unrestricted Erdős #7. The domain statements concern normalized Haar on the actual pure survivor; they do not describe every supported or thinned probability law satisfying the same cylinder caps.

The normalized actual-deficit simplex mechanism is already present in [Report542, NB3–NB4](../500-549/542-an-actual-sharp-nine-cell-interface-for-two-depth-stars.md), including all finite pure heights. [Report624](../600-649/624-arbitrary-central-pure-phases-admit-two-complete-boundary-gates.md) constructs thinned supported capacity laws, and [Report689](../650-699/689-actual-pure-support-averaging-gives-a-finite-all-height-query-interface.md) uses root-balanced laws. Their normalizations differ. This report specializes the actual-Haar mechanism to the categorical projections of [Report810](810-categorical-retained-kernels-give-a-finite-common-source-interface.md), gives their structural cell geometry, and constructs the finite three-table failure.

## 1. Actual deficits retain all pure heights

Fix a prime $q\ge 3$ and any finite family of actual pure originals $a_j\bmod q^j$, with at most one original for each numerical label $q^j$. Let $H_q$ be Haar probability on the $q$-adic integers, $S_q$ the pure survivor, and

$$
\lambda_q=\frac{H_q|_{S_q}}{H_q(S_q)}.
$$

All originals have their one fixed actual phase. Overlaps and redundancy are allowed, and no height bound is imposed uniformly over families.

If the label $q$ is absent, all $q$ first roots are initially live, with total mass $A=1$. If the label $q$ is present with phase $f$, root $f$ is initially removed and $A=(q-1)/q$. For each initially live root $i$, let $d_i$ be the actual Haar measure removed from that root by the **union** of the higher originals, those with $j\ge2$. Deletions inside the already removed root are not charged again. Then

$$
d_i\ge0,\qquad D=\sum_i d_i\le B_q:=\sum_{j\ge2}q^{-j}=\frac1{q(q-1)}<\frac1q.
$$

For a finite family, $D<B_q$. This bound needs no disjointness. The exact first-root probability is

$$
\lambda_q(i\bmod q)=\frac{1/q-d_i}{A-D}. \tag{PS1}
$$

If the pure $q$ original is present, its root $f$ has probability zero. The numerator and denominator in (PS1) use the same actual deletion union. Since $B_q<1/q$, higher originals alone cannot erase a whole first root. Therefore a first root has probability zero exactly when an actual pure $q$ original removes it.

## 2. Root bounds exclude the relaxed counterpoint

If $q$ is present, every live root satisfies

$$
\frac1q\le\lambda_q(i\bmod q)\le\frac{q-1}{q(q-2)}. \tag{PS2}
$$

If $q$ is absent, every root satisfies

$$
\frac{q-2}{q^2-q-1}\le\lambda_q(i\bmod q)\le\frac{q-1}{q^2-q-1}. \tag{PS3}
$$

Indeed, for fixed $D$, the probability is smallest when all deficit is in the specified root, and largest when none is there. The lower expression $(1/q-D)/(A-D)$ decreases with $D$, because $A>1/q$; the upper expression $(1/q)/(A-D)$ increases. Substituting the complete budget $B_q$ gives (PS2)–(PS3). These are closed outer endpoints; the nonzero extremal endpoints arise as limits of finite families.

At 5, every nonzero first-root probability is at least $3/19$. The Report814 relaxed interior point has root-1 probability $1/8$, and

$$
0<\frac18<\frac3{19}.
$$

That point cannot come from the normalized actual pure-Haar source in this class. This excludes that source point; it does not make any previously negative gate positive.

## 3. Minimal closed convex projections

Partition the initially live roots into nonempty observed categories. Write $a_c=k_c/q$ for the initial Haar mass of category $c$, so $a_c>B_q$ and $\sum_c a_c=A$. Aggregate the actual deficits into $d_c$. Then

$$
p_c=\frac{a_c-d_c}{A-D},\qquad d_c\ge0,\qquad \sum_c d_c=D\le B_q. \tag{PS4}
$$

The image of this continuous deficit relaxation is exactly

$$
P(a,B_q)=\left\{p\ge0:\sum_c p_c=1,\quad p_c\le\frac{a_c}{A-B_q}\text{ for every }c\right\}. \tag{PS5}
$$

One inclusion follows from $A-D\ge A-B_q$. Conversely, for $p$ satisfying (PS5), put $d_c=a_c-(A-B_q)p_c$. These deficits are nonnegative, sum to $B_q$, and reproduce $p$ in (PS4). This is an exact statement about the continuous relaxation, not a claim of finite-family realizability for arbitrary real deficits.

The vertices are

$$
p_b^{(c)}=\frac{a_b-B_q\mathbf1_{b=c}}{A-B_q}, \tag{PS6}
$$

one for each live category. At total deficit $B_q$, the map is affine and injective on the deficit simplex. Its concentrated deficits therefore give all vertices. The zero-deficit baseline is already their convex combination with weights $a_c/A$. A single live category gives a singleton.

Each set (PS5) is the **minimal closed convex outer set for its specified structural case**. To show sharpness, choose one live literal root $r$ in the category where deficit is to concentrate. Include the prescribed pure $q$ root $f$ when required, with $r\ne f$, and use the finite higher family

$$
r+q^{j-1}\pmod{q^j},\qquad 2\le j\le E.
$$

These higher cylinders are pairwise disjoint: when $i<j$, the $j$-phase reduces to $r\bmod q^i$, whereas the $i$-phase is $r+q^{i-1}\bmod q^i$. Their mass tends to $B_q$ inside the selected category as $E\to\infty$. Thus actual finite source vectors approach each vertex in (PS6). Every closed convex set containing all finite sources of the case must contain those vertices and their convex hull.

This proves sharpness of the closed convex hull. It does not assert exact finite realization of every interior point.

## 4. Four local cells at 5

Use the observed categories $\{0\},\{1\},\{2,3,4\}$ and write $p=(a,b,1-a-b)$. Projecting away which of 2, 3 or 4 is deleted gives four structural cells:

| actual pure-5 status | minimal closed convex outer cell |
| --- | --- |
| removes 0 | $\operatorname{conv}\{(0,1/5,4/5),(0,4/15,11/15)\}$ |
| removes 1 | $\operatorname{conv}\{(1/5,0,4/5),(4/15,0,11/15)\}$ |
| removes 2, 3 or 4 | $\operatorname{conv}\{(1/5,4/15,8/15),(4/15,1/5,8/15),(4/15,4/15,7/15)\}$ |
| absent | $\operatorname{conv}\{(3/19,4/19,12/19),(4/19,3/19,12/19),(4/19,4/19,11/19)\}$ |

The third cell is equivalently $a,b\le4/15$ and $a+b\ge7/15$, which imply $a,b\ge1/5$. The fourth is equivalently $a,b\le4/19$ and $a+b\ge7/19$, which imply $a,b\ge3/19$.

The four cells are disjoint and separated by positive gaps. In particular, the no-pure cell has $a+b\le8/19<7/15$, while the pure-other cell has $a+b\ge7/15$. The axis cells have a zero coordinate, whereas both coordinates are positive in the two triangles. Each cell is connected, so these four separated connected components cannot be covered by fewer convex subsets without enlarging their union.

Thus four is the minimum number of convex sets whose union is **exactly this stated outer union**. A larger one-cell convex hull remains a valid, weaker relaxation; the minimality statement does not exclude it.

## 5. Two binary components at each other prime

For the binary observation $\{0\}$ versus nonzero, a pure $q$ original with phase 0 gives $p_0=0$. A pure $q$ deleting another root gives

$$
p_0\in\left[\frac1q,\frac{q-1}{q(q-2)}\right],
$$

and absence of pure $q$ gives

$$
p_0\in\left[\frac{q-2}{q^2-q-1},\frac{q-1}{q^2-q-1}\right].
$$

The last two intervals overlap, because

$$
\frac{q-2}{q^2-q-1}<\frac1q<\frac{q-1}{q^2-q-1}.
$$

Their union is exactly the positive interval

$$
\left[\frac{q-2}{q^2-q-1},\frac{q-1}{q(q-2)}\right]. \tag{PS7}
$$

Hence the outer union has two convex components: the isolated zero and (PS7).

| prime | isolated point | positive interval |
| --- | --- | --- |
| 7 | 0 | $[5/41,6/35]$ |
| 11 | 0 | $[9/109,10/99]$ |
| 13 | 0 | $[11/155,12/143]$ |
| 17 | 0 | $[15/271,16/255]$ |
| 19 | 0 | $[17/341,18/323]$ |
| 23 | 0 | $[21/505,22/483]$ |

Merging the overlapping positive intervals forgets pure-presence metadata without enlarging their probability-set union. Retaining the metadata can still give additional query nullities.

The product of the four local-5 cells and two components at each other prime has $4\cdot2^6=256$ convex product cells, with $10\cdot3^6=7290$ distinct product vertices. These are a domain description and count. No gate sweep or optimization over the 7290-point menu is asserted here.

## 6. A finite actual source defeats all three old tables

Use these actual pure originals, all of depth at most 3:

$$
\begin{array}{ll}
q=5:&2\bmod5,\quad6\bmod25,\quad26\bmod125;\\
q\in\{7,11,13,17,19,23\}:&1\bmod q,\quad(2+q)\bmod q^2,\quad(2+q^2)\bmod q^3.
\end{array}
$$

Each prime's three cylinders are pairwise disjoint. These 21 pure labels are mutually distinct and distinct from the 25 anchor/selected labels in [Report808](808-a-second-reference-colour-retains-an-actual-opposing-phase-continuation.md). Together they give 46 distinct odd, nonunit originals, each with one fixed phase. No infinite family or limiting source is used.

At 5 the Haar survivor mass is $94/125$, and its categorical probability vector is

$$
\pi_5=(25/94,19/94,25/47).
$$

At every other $q$, the zero root is untouched and the survivor mass is $1-1/q-1/q^2-1/q^3$. Thus

$$
\pi_q(0)=\frac{q^2}{q^3-q^2-q-1}.
$$

Use this same actual pure-product source with each of the three fixed Report814 tables, retaining each table's own declared ternary weights $w$ and the inherited full-source normalization

$$
\mu=\frac{\lambda_w|_U}{\lambda_w(U)}.
$$

The table gate is

$$
G=12L(\pi,u)-H_{16}(r,v)-27K_Q(1+15r+216v)T_{1600},
$$

where $r=\max(w_4+w_7,w_2+w_5+w_8)$, $v=\max_lw_l$, $K_Q$ includes the pure-29 factor, and the complete inherited tail is $T_{1600}=4301685063112470380207/10^{30}$. The verifier reuses Report814's exact evaluator, literal selected phases, complete hinge and tail.

| fixed table | gate, decimal display | exact strict upper bound |
| --- | ---: | ---: |
| first table, point812 | -0.029209628090146076… | $-1/50$ |
| quarter table | -0.32418958437646217… | $-8/25$ |
| third table | -0.66025552158676… | $-13/20$ |

The source probabilities are reconstructed by enumerating survivors modulo $q^3$, independently of their closed formulas. The displayed decimals come from exact fractions. The selected-cylinder nullities and globally distinct numerical labels are checked on the same actual family.

This is one actual source point where all three specified full-source h16 certificates fail. It is not an actual covering, and does not show failure of an optimized new table or a different query/moment comparison. Subdivision alone cannot repair these three tables on the whole actual-source domain, since a cell containing this source still has no successful table among them.

## 7. What domain refinement changes

The closed convex hull of the four local-5 cells is exactly the old cap polygon

$$
P_5=\{(a,b):0\le a,b\le4/15,\quad a+b\ge1/5\}.
$$

Indeed, all four cells lie in $P_5$, and their vertices include each of its five vertices. Likewise, the convex hull of each binary outer union is the old interval $[0,(q-1)/(q(q-2))]$. Replacing the union by its global convex hull therefore loses this improvement. Its useful information lies in the structural cases, their disconnected geometry, and any retained root metadata.

The three source points used by the dual in [Report813](813-arbitrary-retained-kernels-give-a-uniform-head-and-an-all-threshold-query-obstruction.md) remain simultaneous limits of actual finite sources:

1. $\pi_5=(4/15,4/15,7/15)$ and all six other zero-root probabilities at their upper caps;
2. $\pi_5=(0,1/5,4/5)$, with only the 23-coordinate at its upper cap and the other five zero;
3. $\pi_5=(4/15,0,11/15)$ and all six other zero-root probabilities at their upper caps.

To construct the limits, use the finite combs of Section 3 in the required weak categories, independently at each prime. A zero probability is obtained by the actual pure original with phase 0. Pure-prime numerical labels at distinct primes are different, and none is a selected mixed label, so all coordinates can be realized simultaneously in one finite family at each depth.

For a fixed table, the retained mass and every common-colour envelope are finite polynomials or finite maxima of polynomials in $\pi$; thus $L$ and the gates are continuous. A global source floor valid at every actual finite source remains valid at each of these limits. Report813's strict negative shared-kernel bound consequently still rules out its one-kernel/global-floor comparison on the actual finite-source class. Membership in a convex hull alone would not justify this conclusion; the actual approximating families and continuity do.

The same continuity argument applies to the fixed-h16 shared-kernel obstruction in [Report815](815-retained-source-moments-have-a-three-point-common-kernel-obstruction.md), which uses the same three points and has a strictly negative bound for its retained-source moment gate. This does not extend Report815 to other thresholds. For any fixed shared kernel, a strictly negative limiting gate persists on sufficiently deep finite approximants.

The smaller nonconvex domain can still help a source-adaptive atlas, additional actual-root nullity information, or a different comparison. No new positive gate is asserted here. A proposed atlas must still use one coherent table on every point and query in each certified cell, prove its vertex inequalities, and cover the intended source domain.

## 8. Reproduction

The [verifier](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/actual_pure_source_domains.py), [certificate](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/actual_pure_source_domains_certificate.json), and [exact result](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/actual_pure_source_domains.json) use only the Python standard library. They reuse the existing parent-directory [Report814 evaluator](../../../frontier/cover-geometry/refined-capped-source/three_kernel_atlas_counterexample.py) and its [literal table certificate](../../../frontier/cover-geometry/refined-capped-source/three_kernel_atlas_counterexample_certificate.json).

From the artifact directory:

```sh
python3 -I -S -B actual_pure_source_domains.py
python3 -I -S -B -O actual_pure_source_domains.py
```

Both commands recompute and compare the saved result without writing it. Regeneration requires `--write-result`; alternate inputs use `--certificate`, `--result`, and `--source-dir`. The source directory defaults to the verifier's parent directory, so a portable copy must retain both Report814 dependency files one level above the three new artifacts, or explicitly supply `--source-dir`.

The computation checks the rational cell vertices, interval endpoints and counts, actual-union controls with overlap and redundant deep originals, the depth-3 actual source, the complete selected-label constraints, and three gates at that single source. It does not enumerate the 7290-point menu, run a solver, or infer an unrestricted covering result from finite tests.
