[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

<a id="seven-vertex-block-noncoverage-with-actual-prime-measures"></a>
# Every prime graph with blocks of at most seven vertices is noncovering

**Theorem.** Let a finite family of arithmetic progressions have pairwise
distinct odd moduli greater than one. Join two primes whenever both
divide one of its moduli. If every block of this prime graph has at most
seven vertices, the family leaves an integer uncovered. Original
prime-power heights and residues are arbitrary, and the total number
of primes is unrestricted.

The proof enlarges the actual-domain recursion of
[Chapter 23](23-conditional-kernels-and-recursive-block-noncoverage.md)
using the unchanged fees of
[Chapter 25](25-six-vertex-block-fees-and-a-finite-prime-core-frontier.md).
A complete finite boundary pays every new non-3 orientation and all
but 509 root-3 ranges. These ranges, together with the older six-vertex
fee exceptions, contain at most one actual graph block. A measure from
Schroeder's ordinary anchor calculation pays that block's remaining
attachment costs, using the marginal transport of
[Chapter 30](30-six-prime-prefix-measures-close-all-six-vertex-blocks.md).

This is an ordinary mathematical proof with exact finite certificates,
using the previously checked geometry of
[Schroeder's nine-prime paper](../../../../Library/Arith/schroeder2026nine.md),
version 1.0.1. No new Lean verification or unrestricted solution of
Erdős #7 is asserted. The proof specifies the source interface, its
parameter changes, the finite-to-infinite comparison, and the common
original family in every attachment estimate.

## 1. The original tree and its shared fees

Let \(h_p\) be the largest exponent of each prime \(p\) anywhere in the
original family, including attached blocks. Work on
\(X_p=\mathbb Z/p^{h_p}\mathbb Z\) with uniform probability \(H_p\).
A residue class is a product of prefix cylinders; distinct moduli
give distinct complete exponent vectors. The support of every mixed
class is a clique contained in one graph block. Pure classes belong
to their prime vertices.

Root the component containing 3 at 3; root each other component at any
of its primes. All child primes are at least 5. For a prime \(p\),
write \(D_p\) for its actual strict descendant primes. Let \(V_p\)
be the words admitting an avoiding extension through that descendant
subtree, including avoidance of the original pure classes at \(p\).
Retain
\[
 f(5)=\frac7{24},\quad f(7)=\frac18,\quad
 f(11)=\frac1{24},\quad f(13)=\frac1{48},\qquad
 f(q)=2^{-(q-1)/2}\quad(q\ge17),
\]
\[
 \sum_{q\ge5\ {\rm prime}}f(q)\le F_*:=\frac{1493}{3072}<\frac12,
 \qquad c_5=\frac3{10},\quad c_p=\frac2{p-1}\quad(p\ge7).
 \tag{SV1}
\]
This is Chapter 25's majorant after removing the composite-21 term.
The non-3 inductive invariant is
\[
 e_p:=\sum_{q\in D_p}f(q),\qquad
 H_p(V_p)\ge1-\frac1{p-1}-c_pe_p.
 \tag{SV2}
\]
Child descendant sets are disjoint and avoid the entire current block.
They are sets in one original family, not independent copies of an
expense allowance.

For a block with parent \(p\) and immediate children \(J\), let
\(B_{J\to p}\) consist of parent words having no avoiding child tuple
in \(\prod_{q\in J}V_q\). Parent-pure classes are excluded from this
block-only blocker. Its local fee has the form
\[
 H_p(B_{J\to p})\le c_p C\quad(p\ge5),\qquad
 H_3(B_{J\to3})\le C,
 \tag{SV3}
\]
where \(C\) is the fee sum of a specified subset of its actual
immediate children. Different outgoing blocks have disjoint such
charge sets.

## 2. The exact conditional-kernel test

Assume (SV2) for the actual child domains. If \(e_q\le E\), their
normalized product law has complete child-cylinder caps bounded by
products of
\[
 b_5(E)=\frac1{3-(6/5)E},\qquad
 b_q(E)=\frac1{q-2-2E}\quad(q\ge7).
 \tag{SV4}
\]
Indeed a depth-\(a\) cylinder has conditional mass at most
\(q^{-a}/H_q(V_q)\); summing all positive depths gives
\(1/((q-1)H_q(V_q))\le b_q\). Thus \(b_S\) pays the sum over all
complete positive exponent vectors on support \(S\), not merely
one cylinder. Larger positive coordinate bounds \(b_q\) can be
used directly.
Set \(b_S=\prod_{q\in S}b_q\),
\[
 w_S=\begin{cases}0,&|S|=1,\\b_S,&|S|\ge2,\end{cases}
 \qquad v_{t,S}=w_S+t b_S,
\]
and define
\[
 Z_A(v)=\sum_{\mathcal F}(-1)^{|\mathcal F|}
                     \prod_{S\in\mathcal F}v_S,\qquad Z_\varnothing=1.
\]
Here \(\mathcal F\) ranges over families of pairwise disjoint nonempty
supports in \(A\). Write
\[
 Z_t=Z_J(v_t),\qquad
 L_t=\sum_{\varnothing\ne S\subseteq J}b_SZ_{J\setminus S}(v_t).
 \tag{SV5}
\]
Chapter 23, (CK8)--(CK12), proves that an integer \(t\ge1\) with
\[
 Z_A(v_t)>0\quad(\varnothing\ne A\subseteq J)
 \tag{SV6}
\]
gives
\[
 H_p(B_{J\to p})\le K_{p,t}:=\frac{L_t}{p^t(p-1)Z_t}.
 \tag{SV7}
\]
It conditions the actual child product law on actual shallow avoidance
events, applies the conditional Shearer ratio for that same law, and
integrates deep original parent cylinders against \(H_p\). Each
complete child cofactor occurs at most once at each fixed original
parent exponent, globally across residues. All original heights and
literal classes are preserved.

For exact evaluation choose \(a\in A\) and use
\[
 Z_A(v_t)=Z_{A\setminus\{a\}}(v_t)
 -\sum_{\substack{\varnothing\ne S\subseteq A\\a\in S}}
       (t+\mathbf1_{|S|\ge2})b_S Z_{A\setminus S}(v_t).
 \tag{SV8}
\]
An independent route is
\[
 Z_A(v_t)=\sum_{n=0}^{|A|}d_n(t)e_n((b_q)_{q\in A}),\qquad
 d_0=1,
\]
\[
 d_n=-t d_{n-1}-(t+1)\sum_{r=2}^n
                  \binom{n-1}{r-1}d_{n-r},\qquad
 L_t=-\partial_t Z_J(v_t).
 \tag{SV9}
\]
Both methods check every coordinate residual; positivity of the top
polynomial alone would not establish (SV6).

## 3. Every non-3 seven-vertex block has its local fee

There are six immediate children. Put
\[
 P_0=\{5,7,11,13,17,19,23,29,31,37,41,43,47,53\}.
\]
If \(S=J\cap P_0\ne\varnothing\), let \(j=|S|\le6\), charge
\(C=\sum_{q\in S}f(q)\), and use \(E=F_*-C\).
Replace the remaining sorted children, only in the numerical bounds,
by the first \(6-j\) members of
\[
 (57,59,61,63,65).
 \tag{SV10}
\]
Every corresponding actual prime is at least its lower proxy, and
every actual descendant expense is at most \(E\). Formula (SV4)
therefore gives dominating coordinate caps. No residue space or CRT
is assigned to a composite proxy.

For parent \(p\ge7\), let \(p_{\min}\) be the smallest prime at least
7 outside \(S\). At most six small children are excluded, so
\[
 p_{\min}\le29<57,\qquad p\ge p_{\min},\qquad
 \frac{K_{p,t}}{c_p}=\frac{L_t}{2p^tZ_t}
                    \le\frac{L_t}{2p_{\min}^tZ_t}.
 \tag{SV11}
\]
The selected certificate makes the last expression strictly less
than \(C\). The bound \(p_{\min}<57\) ensures it is not an actual
large child.

Parent 5 is a separate legal orientation when \(5\notin S\). The
actual parent is absent from the immediate children and all their
strict descendants. The improved expense is therefore
\[
 E_5=F_*-C-f(5)=E-f(5).
 \tag{SV12}
\]
With caps \(b_q(E_5)\), the selected strict-region certificate gives
\[
 \frac{K_{5,t}}{c_5}=\frac{5L_t}{6\cdot5^t Z_t}<C.
 \tag{SV13}
\]
This subtraction uses actual exclusion of the parent from the
descendant sets, not an absence in a proxy notation.

The complete finite boundary is:

| Small children \(j\) | Boundary rows | Non-3 orientations paid | Root-3 rows paid |
| --- | ---: | ---: | ---: |
| 1 | 14 | 27 | 14 |
| 2 | 91 | 169 | 91 |
| 3 | 364 | 650 | 364 |
| 4 | 1001 | 1716 | 990 |
| 5 | 2002 | 3289 | 1897 |
| 6 | 3003 | 4719 | 2610 |
| Total | 6475 | 10570 | 5966 |

Each row is exactly one \(S\subseteq P_0\), \(1\le|S|\le6\), and
represents all its allowed large actual children. Every non-3 row
has all 64 coordinate residuals positive, including \(Z_\varnothing=1\),
and a positive fee margin, at a selected cutoff between 1 and 10.
If \(S=\varnothing\), all six children are at least 57. Chapter 23's
analytic large-child theorem applies because \(57=6(6+3)+3\), and
pays every legal parent by a charge on the actual smallest child.
Smaller blocks retain the non-3 fees of Chapters 23 and 25.

These local results assume only the actual child-domain invariant,
regardless of how the domains were constructed. Starting at the
leaves, outgoing blocks charge disjoint subsets of the parent's strict
descendants. Their blocker union \(W_p\) consequently satisfies
\[
 H_p(W_p)\le c_p e_p.
 \tag{SV14}
\]
Adding the original pure-class bound \(1/(p-1)\) proves (SV2) at
that parent. This closes the non-3 induction for all blocks of at
most seven vertices. Equation (SV14) is proved directly from block
fees; it is not obtained by subtracting upper bounds.

## 4. At most one block needs the global root reserve

The successful root entries in the table have \(K_{3,t}<C\), at
selected integer cutoffs between 1 and 15. The remaining 509 consist
of 11 four-small-child rows, 105 five-small-child rows, and 393
six-small-child rows. Their signatures are:

| Intersection with \(\{5,7,11,13\}\) | Rows |
| --- | ---: |
| \(\{5,7,11,13\}\) | 56 |
| \(\{5,7,11\}\) | 168 |
| \(\{5,7,13\}\) | 151 |
| \(\{5,7\}\) | 90 |
| \(\{5,11,13\}\) | 25 |
| \(\{7,11,13\}\) | 19 |

Every new exceptional child set contains at least two of \(\{5,7,11\}\).
Any two intersect. All fifty older six-vertex root fee exceptions
from Chapter 25 contain both 5 and 7; their child sets also intersect
every new exceptional set and one another. Since distinct graph
blocks share at most one vertex, and all these exceptions contain
3, at most one actual block belongs to their combined family.

The argument uses all fifty original six-vertex *fee* exceptions.
Later root-reserve closures do not turn them into local fees; in
particular Chapter 30 supplies no descendant fee. If there is no
exceptional block, the root union bound leaves
\[
 \frac12-F_*=\frac{43}{3072}>0.
 \tag{SV15}
\]
If the unique exception has six vertices, the earlier root arguments
remain valid: Section 3 proves the identical descendant invariant,
and uniqueness gives every other root block its local fee.
[Chapter 28](28-unique-root-reserve-and-shared-descendant-budget.md)
closes 38 of the fifty old sets, and Chapter 30 closes the remaining
twelve. Chapter 29 gives an additional reduction but is not needed
here. It remains to close a unique seven-vertex block in the 509
new exceptional ranges.

## 5. The ordinary source construction with variable later primes

We use the parameterized ordinary calculation in Schroeder, Sections
3--5 and 8. Neither the special first-7 deletions nor the fixed-165
screen nor the final eight-prime numerical theorem is invoked.

Keep anchor coordinates 3 and 5, and let the later physical primes
be \(q_1<\cdots<q_s\), all greater than 5. Choose **integer** thresholds
\[
 1\le t_i\le q_i-2,\qquad
 \beta_i=q_i-1-t_i,\qquad C_i=\frac{q_i-1}{\beta_i}.
 \tag{SV16}
\]
Then \(1<C_i\le q_i-1<q_i\), and
\[
 C_i\left(1-\frac1{q_i-1}\right)=\frac{q_i-2}{\beta_i}\ge1.
\]
Complete all pure prime-power classes and the 15-class by source
Lemma 2.2. The proper-divisor reciprocal condition holds for this
selected set. Completion may move selected residues but preserves
the original covered subset. It is an auxiliary construction on the
core; added classes do not alter the original graph tree.

Let \(A\) avoid every completed class supported on the anchor pair.
Start with the unnormalized measure \(H|_A\). At each later coordinate
source Lemma 3.1 supplies a normalized conditional kernel bounded by
\(C_i\), avoiding its pure forbidden set. With \(Z_i\) the source's
complete mixed-class load, deleting the actual mixed bad set costs
at most
\[
 \frac{[1+Z_i-t_i]_+}{\beta_i}.
 \tag{SV17}
\]
The kernel may depend on the complete family and earlier actual
coordinates. Survivors are never renormalized. Feasibility and the
loss majorant follow exactly as in source (3.1)--(3.3). Clipping the
majorant at 1 would invalidate the convex comparison and is not done.

Reverse integration of normalized kernels, as in source Lemma 3.2,
gives live-measure marginal caps \(1,1,C_1,\ldots,C_s\). In particular,
every subset \(D\) of a complete finite coordinate at \(q_i\) has
live mass at most \(C_iH_{q_i}(D)\). The cylinder bounds extend to
such subsets by summing disjoint equal-depth cylinders. No independence
of the live distorted coordinates is required.

### The same 32 basic anchor vertices

Haar-preserving prefix permutations normalize the completed 3-, 9-,
and 5-classes to \(0\pmod3\), \(1\pmod9\), and \(0\pmod5\).
The 15-class has representative \(a\in\{1,2\}\), the 27-class has
representative \(b\in\{2,4\}\), and the first digit \(c\) of the
25-class lies in \(\{a,3-a\}\). Put
\[
 K_{a,b}=\{x\pmod{135}:x\not\equiv0\ (3),1\ (9),b\ (27),
                                      0\ (5),a\ (15)\}.
\]
For the relative deeper pure-5 deletion \(D_h\) in nonzero column
\(h\), completion gives
\[
 D_h=\frac15\mathbf1_{h=c}+u_h,\qquad
 u_h\ge0,\qquad\sum_{h=1}^4u_h=\frac1{20}.
 \tag{SV18}
\]
The anchor reserve, in units of \(1/135\), is
\[
 R=\frac{135}{4}+\gamma+(9-\gamma)D_a,\qquad
 \gamma=3\mathbf1_{a=1}+\mathbf1_{b\equiv a\pmod3}.
 \tag{SV19}
\]
Indeed the completed pure 3- and 5-survivors have product mass
\(3/8\), all mixed 3--5 types have total reciprocal mass \(1/8\),
and the selected 15-class's already deleted part gives the displayed
credit. This uses no extra 75-class credit or completed 165-class.

For upper costs, ignore deeper pure-3 exclusions and retain the
pure-5 restriction. The zero extra-depth atoms are \(2/3\) at 3 and
\(4/5-D_h\) at 5. Positive extra depth \(u\ge1\) has mass
\(2/3^{u+1}\) at 3; positive depth \(v\ge1\) has mass \(4/5^{v+1}\)
at 5. These define the four positive anchor-region comparisons in
source Section 8.1. The simplex vertices are \(u=(1/20)e_j\),
\(1\le j\le4\). With the eight choices \((a,b,c)\), there are
exactly 32 basic vertices.

Each geometric maximum is convex in its nonnegative cell weights.
Positive expectations and positive omitted-region upper sums preserve
convexity, while the reserve is affine in the same simplex variable.
Thus the actual lower ledger is at least a convex combination of
the 32 vertex lower ledgers. Different stages are evaluated at the
same vertex; separately attained anchor optimizers are not combined.

### The complete distribution and exact remainder

Source Lemma 4.1 replaces earlier nonanchor cylinder loads by
independent auxiliary runs
\[
 \Pr(J_i=0)=1-\frac{C_i}{q_i},\qquad
 \Pr(J_i=j)=\frac{C_i(q_i-1)}{q_i^{j+1}}\ (j\ge1),\qquad
 \Pr(J_i\ge e)=\frac{C_i}{q_i^e}.
 \tag{SV20}
\]
This auxiliary independence makes no assertion about the actual
distorted coordinates. Complete exponent-vector distinctness and
source Section 4.1 give
\[
 M_i=\prod_{j<i}(1+J_j),\qquad
 \mathbb EM_i=\prod_{j<i}\left(1+\frac{C_j}{q_j-1}\right).
 \tag{SV21}
\]
The anchor categories stay \(3,9,27,5,15,45,135\), with coefficients
\[
 (1,1,1+u,1+v,1+v,1+v,(1+u)(1+v)).
\]
The identity \((q_i-1)\sum_{e\ge1}q_i^{-e}=1\) normalizes the
current exponent inventory after labelled convex comparison. Hence
changing later primes does not change the anchor geometry.

For nonnegative cell weights \(a_x\), let
\[
 \Phi_z(a;u,v)=\max_{(r_g)}\sum_{x\in K_{a,b}}a_x
 \left[1-z+\sum_g w_g(u,v)\mathbf1_{x\equiv r_g\pmod g}\right]_+.
\]
With \(A(a)=\sum_xa_x\), \(a_*=\max_xa_x\), and
\(h_g(a)=\max_r\sum_{x\equiv r\ (g)}a_x\), its full linear load is
\[
 \Lambda=A+h_3+h_9+(1+u)h_{27}
 +(1+v)(h_5+h_{15}+h_{45})+(1+u)(1+v)a_*.
 \tag{SV22}
\]
Let \(\mathcal A\) be the positive sum of the four anchor-region
expectations, including their cell-dependent zero atoms. Compute
\(F(z)\) by retaining \(u<12,v<9\) in \(\mathcal A[\Phi_z]\) and
using \(\Lambda\) outside that rectangle. Set \(A_0=\mathcal A[A]\)
and \(W=\mathcal A[\Lambda]\). The omitted depths are integrated
exactly, since the load is separately affine in \(u,v\), with at
most a \(uv\) term, and
\[
 \sum_{j\ge L}\frac{p-1}{p^{j+1}}=p^{-L},\qquad
 \sum_{j\ge L}\frac{j(p-1)}{p^{j+1}}
      =p^{-L}\left(L+\frac1{p-1}\right).
 \tag{SV23}
\]
For \(\pi_i(m)=\Pr(M_i=m)\), source Lemma 8.2 gives
\[
 N_i=\sum_{m<t_i}\pi_i(m)mF(t_i/m)
 +\left(\mathbb EM_i-\sum_{m<t_i}m\pi_i(m)\right)W
 -t_i\left(1-\sum_{m<t_i}\pi_i(m)\right)A_0.
 \tag{SV24}
\]
When \(m\ge t_i\), the hinge is linear and its exact maximum is
\(m\Lambda-t_iA\); its remaining mass and first moment suffice.
Every \(m<t_i\le12\) is in the stored range \(m<32\). All needed
ratios occur in the source cache:
\[
 \{t/m:t\in\{2,4,8,12\},\ 1\le m<t\}.
 \tag{SV25}
\]
The stage loss is at most \(N_i/\beta_i\). The certificate rounds
this upward to a multiple of \(10^{-10}\) in 135-cell units, then
subtracts it from the exact reserve. Every earlier multiplier law
and its full first moment is recomputed at the chosen primes and
caps; changing only the current denominator would not prove the bound.

### Integer lower proxies

For a fixed integer threshold suppose \(q_i\ge b_i\ge t_i+2\),
where \(b_i\) is an integer lower proxy. Put
\[
 \overline C_i=\frac{b_i-1}{b_i-1-t_i},\qquad
 \overline\beta_i=b_i-1-t_i.
\]
Then \(\overline C_i<b_i\), and for every \(e\ge1\),
\[
 \frac{C_i}{q_i^e}\le\frac{\overline C_i}{b_i^e},\qquad
 \beta_i\ge\overline\beta_i>0.
 \tag{SV26}
\]
The proxy tails therefore define a probability distribution. Couple
actual and proxy runs with common quantile uniforms. Products
\(\prod(1+J_i)\) and the **untruncated** ordinary hinge increase under
this coupling. First dominate that complete exact expectation by
the proxy expectation, then apply (SV24) with its positive
omitted-region bound to the proxy. Division by the smaller positive
proxy denominator keeps the upper direction. This does not assume
monotonicity of two separately truncated numerical upper bounds.
The marginal cap can be weakened to \(\overline C_i\), and the same
weakened cap is used in the attachment calculation.

## 6. Transport to the actual core with whole-coordinate caps

For ordered actual children \(J=(r_1,\ldots,r_6)\), if \(r_1=5\)
use anchors 3,5 and later physical primes \(r_2,\ldots,r_6\).
If \(r_1\ge7\), use source coordinates
\[
 (3,5,r_2,r_3,r_4,r_5,r_6)
\]
and transport the second coordinate to \(r_1\). The coordinate count
is seven throughout; no coordinate of a dependent measure is discarded.

For the finite transport, at each coordinate and digit position choose
an independent uniform additive shift modulo the target prime.
It gives a prefix-preserving product injection \(F\) from the source
space to the actual space. An original target cylinder pulls back to
an empty set or a cylinder with the same complete exponent vector.
Discard empty pullbacks, choose an avoiding source submeasure
\(\mu_F\) for the resulting family, and define
\[
 \nu=\mathbb E_F F_*(\mu_F).
 \tag{SV27}
\]
There are finitely many maps, so selection is finite. A uniform mass
lower bound \(m\) for every \(\mu_F\) survives averaging, as does
avoidance of the original target family. For an actual coordinate
subset \(D\), its source marginal cap implies, pointwise in \(F\),
\[
 \nu(y_i\in D)\le\alpha_i\mathbb E_F H_{p_i}(F_i^{-1}(D))
                  =\alpha_iH_{r_i}(D).
 \tag{SV28}
\]
Each fixed source word has uniform random image, proving the equality.
Dependence of \(\mu_F\) on \(F\) is allowed: the cap is applied
before averaging. The root cap is 1; when source 5 maps to \(r_1\),
its cap stays 1.

For a source measure on infinite prime-adic spaces, first undo its
Haar-preserving normalizing tree permutations and project to the
full original heights. Avoidance survives because the heights include
every original depth and completion preserved the original covered
subset. Marginal caps survive projection. Using heights from the
entire family ensures that every later attachment blocker is a
subset of the complete coordinate on which (SV28) was proved.

## 7. The common attachment budget and 490 ordinary closures

Fix the original family and its unique exceptional core. Let \(S\)
be the fixed small children of its boundary row, and put
\[
 E=F_*-\sum_{q\in S}f(q),\qquad
 e_r=\sum_{p\in D_r}f(p),\qquad x=\sum_{r\in J}e_r.
 \tag{SV29}
\]
Actual core children outside \(S\) also have fees; omitting their
fees merely enlarges \(E\). The union \(W_3\) of all other root
blockers has mass at most \(E-x\): its charged immediate-child
sets are disjoint from \(S\) and all core descendant sets.
For each core child, (SV14) gives \(H_r(W_r)\le c_re_r\).
The transported measure \(\nu\) already avoids all original pure
and mixed core classes. Its loss on the actual attachment cylinders
is therefore at most
\[
 \nu(x_3\in W_3)+\sum_{r\in J}\nu(x_r\in W_r)
       \le E-x+\sum_{r\in J}\alpha_rc_re_r.
 \tag{SV30}
\]
This is a union bound using marginal caps for the same realized
family, not a product of marginal survival probabilities.

For 490 of the 509 exceptional ranges use five later-stage thresholds
\[
 (2,4,4,8,8).
 \tag{SV31}
\]
All these rows contain 5. Their proxy source calculations satisfy
\[
 m_S>E,\qquad \alpha_rc_r\le\frac12\quad(r\in J),
 \tag{SV32}
\]
where \(m_S\) is the minimum of the 32 source vertex ledgers divided
by 135. Each ledger uses the complete proxy distributions at every
stage. The smallest certified difference among these 490 ranges is
\[
 \min(m_S-E)=\frac{7151035021}{540000000000}>0
 \tag{SV33}
\]
at \((5,11,13,17,19,23)\). Equation (SV30) bounds the loss by
\(E-x/2\le E\), leaving positive mass. Every allowed actual large
prime choice is covered by the proxy argument of Section 5.

## 8. Nineteen missing-5 ranges and its actual location

The other nineteen ranges have no core prime 5. They are precisely:

| Fixed first five children | Last actual child |
| --- | --- |
| \(7,11,13,17,19\) | \(23,29,31,37,41,43,47,53\), or any prime \(\ge57\) |
| \(7,11,13,17,23\) | \(29,31,37,41,43,47\) |
| \(7,11,13,17,29\) | \(31\) |
| \(7,11,13,19,23\) | \(29,31,37\) |

Use source anchors \((3,5)\), mapping 5 to actual child 7 as in
Section 6, and later-stage thresholds
\[
 (4,4,8,8,12).
 \tag{SV34}
\]
The ratios (SV25) already contain all required source geometry.
The resulting mass lower bound \(m_S\) and transported caps obey
\[
 \rho_S:=\max_{r\in J}\alpha_rc_r\le\frac13.
 \tag{SV35}
\]
Absence of 5 from the core alone does not authorize subtracting its
fee. Its actual location gives the following exhaustive cases.

### 5 is a strict descendant of a core child

Then \(x\ge f(5)\). Equation (SV30) gives
\[
 \mathrm{loss}\le E-(1-\rho_S)x
                   \le E-(1-\rho_S)f(5).
 \tag{SV36}
\]
The new source bound exceeds this quantity in all nineteen ranges.

### 5 is an immediate child of a different root block

There is a unique such block \(L\). Its child descendant sets avoid
both the fixed core set \(S\) and 5, so their expenses are at most
\(E-f(5)\). Let \(T_S\) be the first six primes at least 5 outside
\(S\), in increasing order. It starts with 5. The ordered actual
children of \(L\) are bounded below by the corresponding entries
of \(T_S\). Only fixed actual core primes are excluded. In
particular 57, which denotes a lower proxy for an unbounded range,
is not treated as an actual excluded prime.

Apply (SV4)--(SV7) with parent 3, expense \(E-f(5)\), and the
coordinate caps at \(T_S\). If \(L\) has fewer than six children,
adjoin independent auxiliary coordinates carrying no actual events.
The actual event families still satisfy the six-coordinate dominating
support vector, so the conditional-kernel proof remains valid. This
pads the comparison, without enlarging the original family or graph.
The certificate checks the full strict region and gives
\[
 H_3(B_L)\le K_S:=\frac{L_{t_S}}{2\cdot3^{t_S}Z_{t_S}}.
 \tag{SV37}
\]
The other root immediate charges avoid \(S\), 5, and all core
descendant sets. They total at most \(E-f(5)-x\). Thus
\[
 \mathrm{loss}\le K_S+E-f(5)-x+\rho_Sx
                     \le E-f(5)+K_S.
 \tag{SV38}
\]
This bounds actual blocker subsets under (SV28); it does not combine
independently optimized probability laws for different blocks.

### Every other location, including absence of 5

Here 5 is neither a core descendant nor an immediate child of any
other root block. It may be absent, belong to another connected
component, or be deeper in another root branch. Both the core
descendant sets and all charged immediate children of the other
root blocks exclude it. Therefore
\[
 \mathrm{loss}\le E-f(5)-x+\rho_Sx\le E-f(5).
 \tag{SV39}
\]
A deeper 5 in another branch is already covered by that branch's
non-3 induction; it creates no immediate charge at the root.

For every row the exact data establish both
\[
 m_S>E-(1-\rho_S)f(5),\qquad
 m_S>E-f(5)+K_S.
 \tag{SV40}
\]
Since \(K_S>0\), these imply \(m_S>E-f(5)\) as well. The smallest
second margin is
\[
 \frac{347828433856301714416342033242916540645822281183439}
 {68465433008878704122073007926530234931955200000000000}>0
 \tag{SV41}
\]
at \(J=(7,11,13,19,23,37)\), where
\(m_S=29980685579/168750000000\).
All three possible locations therefore leave positive core mass in
each of the nineteen ranges.

## 9. Gluing the actual avoiding extensions

Every six-child tuple has either a unique nonempty boundary subset
\(S\) or the analytic large-child proof. Every non-3 orientation
has the local domain invariant. At root 3 there are no fee exceptions,
one old six-vertex exception, or one new seven-vertex exception.
Section 4 handles the first two cases; Sections 5--8 close all 509
ranges in the last case by the 490 plus nineteen partition.

A surviving exceptional-core tuple avoids every original core pure
and mixed class. Its child coordinates avoid their actual outgoing
blockers, and therefore lie in their domains \(V_r\). Its root
coordinate avoids all other root blockers. Choose the avoiding
extensions at these same fixed words. Private block-tree sides are
disjoint, so the extensions glue. A component without 3 has a
positive root domain from (SV2); take a witness in every such
component and combine them by CRT.

This gives an uncovered residue modulo the original common period
\(N\), hence an uncovered integer. The full original Haar uncovered
proportion is positive and is at least \(1/N\). The core measure
surplus is not a uniform lower bound for the full-family uncovered
density.

## 10. Exact certificate and source inputs

The standalone
[producer](../frontier/cover-geometry/seven_block_certificate.py)
and its
[exact data](../frontier/cover-geometry/seven_block_certificate.json)
record the complete boundary, selected cutoffs, minimum coordinate
residuals, and fee ratios. The producer checks every one of the 64
coordinate residuals for each selected six-coordinate comparison.
The final core records retain each range, expense, successful
threshold schedule, marginal and attachment caps, minimum source
mass, worst basic vertex, and positive attachment surplus.
The nineteen missing-5 records also include the outside proxy,
expense, coordinate caps, cutoff, minimum residual, \(Z,L,K_S\),
and all three placement costs.

The calculation reuses Chapter 30's
[source helper](../frontier/cover-geometry/six_prime_prefix_certificate.py)
and
[ordinary geometry](../frontier/cover-geometry/six_prime_prefix_geometry.json).
No new geometry copy or geometric search is needed. From the
repository root:

    python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/seven_block_certificate.py --geometry docs/reports/erdos7-odd-covering/frontier/cover-geometry/six_prime_prefix_geometry.json --output /tmp/seven-block-certificate.json

The default helper is the existing adjacent Chapter 30 program;
an explicit helper path can also be supplied. Absolute input paths
allow execution from any working directory.

The ordinary geometry comes from the source version 1.0.1 archive
with SHA256

    9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c

and its original verifier has SHA256

    e3296d181686c0f1925e755583fdc4df2ffeb2bacbc36a77a2396bbe3b4a9135

These inputs contain the basic-anchor queries at (SV25) and the exact
linear remainders (SV22)--(SV23). Reusing the previously checked
geometry is not a rerun of the source's geometric search or an
extension of its Lean development.

The finite boundary has 10,570 selected non-3 certificates and 5,966
selected root certificates, totaling 1,058,304 checked coordinate
residuals. The nineteen outside-block certificates add 1,216.
The final source evaluation has 509 successful schedules, 16,288
basic-vertex evaluations and 81,440 stage bounds. Only the successful
final schedule for each range is needed in the result.

Independent arithmetic checks using elementary-symmetric polynomials,
derivatives, and separate ordinary distribution evaluation reproduce
the boundary and source bounds; a separate subset recurrence also
reproduces the nineteen outside-block comparisons. The source
interface, finite-to-infinite comparisons, and actual-family gluing
proved above supply the mathematical conditions which these numerical
checks alone would not establish.

Blocks with eight or more vertices remain outside this theorem.
