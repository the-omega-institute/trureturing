[Index](../../marked_head_profile.md) · [Previous](11-original9-higher-hinges-and-a-fixed-1113-continuation.md) · [Next](13-probability-capped-deletion-and-a-joint-observation-beyond-this-boundary.md)

<a id="complete-original-low-test-anchoring-at-arbitrary-prime-power-heights"></a>
### Complete original low-test anchoring at arbitrary prime-power heights

Retaining one complete original low test gives an all-height square
estimate in terms of its weighted cylinder caps.  Its PG1 specialization
below certifies the aligned2 test branch at \(\Gamma_{13}<146.919\).
The uniform PG1 bound over all low tests remains \(\Gamma_{13}<148.650\).

Let \(M_0=\prod_{p\in\mathcal P}p^{h_p}\), where \(\mathcal P\) is a finite
set of primes and \(h_p\ge1\).  Let \(\mu\) be any probability on a subset
of \(\mathbb Z/M_0\mathbb Z\), and let \(\lambda\) be its uniform independent
lift in the additional digits to any finite heights \(H_p\ge h_p\).
Fix one original low class \(C_d\) for every \(d\mid M_0\), including the
unit class, and put

\[
 B=\sum_{d\mid M_0}\mathbf1_{C_d},\qquad
 m_d(\sigma)=\max_{a\bmod d}\sigma(a\bmod d).
\]

Every complete fine test extending those classes has \(L=B+R\), where
\(R\) contains precisely its higher original modulus labels.  Set

\[
 S(d)=\{p:v_p(d)=h_p\},\quad
 a_d=\prod_{p\in S(d)}\frac p{p-1},\quad \gamma_d=a_d-1,
\]

\[
 b_{de}=\prod_{p\in S(d)\cap S(e)}\frac{p(p+1)}{(p-1)^2}
         \prod_{p\in S(d)\triangle S(e)}\frac p{p-1},\qquad
 \kappa_{de}=b_{de}-a_d-a_e+1.
\]

Then, uniformly over all those finite heights and higher test residues,

\[
 \mathbb E_\lambda L^2\le
 U(B):=\mathbb E_\mu B^2+
       2\sum_{d\mid M_0}\gamma_d m_d(B\mu)+
       \sum_{d,e\mid M_0}\kappa_{de}m_{\operatorname{lcm}(d,e)}(\mu).
 \tag{AF1}
\]

For proof, a higher label has the unique form
\(m=d\prod_p p^{t_p}\), with \(d=\gcd(m,M_0)\), \(t\ne0\), and
\(\operatorname{supp}(t)\subseteq S(d)\).  Its cross term with \(B\) is
at most \(\prod_p p^{-t_p}m_d(B\mu)\).  Two higher labels have either
empty intersection or a low cylinder modulo \(\operatorname{lcm}(d,e)\),
and their extra-digit intersection probability is at most
\(\prod_p p^{-\max(t_p,s_p)}\).  The sum over one nonzero exponent vector
is \(\gamma_d\).  Including both zero vectors and then removing their
two faces gives the double coefficient \(\kappa_{de}\), using

\[
 \sum_{r,s\ge0}p^{-\max(r,s)}=\frac{p(p+1)}{(p-1)^2}.
\]

All summands are nonnegative, so replacing finite exponent ranges by
these infinite sums is an upper bound.  Expanding \((B+R)^2\) proves
(AF1).  Original labels with equal low projection remain distinct.

This uses the moment framework of BBMST,
[arXiv:1811.03547, Theorem 3.2](https://arxiv.org/abs/1811.03547), and the
repository's saturated-label calculations (SH1)–(SH3), (SH8).  The
retained observation here is \(m_d(B\mu)\), with one fixed complete
\(B\), in place of separate low-cylinder intersection maxima.

<a id="the-same-complete-floor-inside-and-outside-a-finite-depth-box"></a>
#### The same complete floor inside and outside a finite depth box

Let the auxiliary variables be independent with
\(\Pr(Z_p=k)=(p-1)/p^{k+1}\), and set

\[
 w_d(z)=\prod_{p\in S(d)}(1+z_p),\qquad r_d(z)=w_d(z)-1,
\]

\[
 S_B(z)=\max_{(D_d)}\int
      \left(B+\sum_{d\mid M_0}r_d(z)\mathbf1_{D_d}\right)^2d\mu.
\]

Only the higher projected cylinders \(D_d\) vary.  Centering the
additional prefixes bounds their intersection probabilities as above.
At each auxiliary depth, average the active higher labels within each
projection and apply convexity only to that average, leaving \(B\)
fixed.  This gives

\[
 \mathbb E_\lambda L^2\le\mathbb E_Z S_B(Z). \tag{AF2}
\]

This is the full-low-label extension of the original9 separation in
(M9-2)–(M9-5).  The maximizing \(D_d\)'s may depend on \(z\); the upper
bound does not assert that one actual higher family attains all of them.
In particular, replacing the expression by
\(\sum_d w_d(z)\mathbf1_{C_d}\) with freely changing original \(C_d\)'s
would lose the fixed original test needed in the deleted energy.

For any finite depth box \(\mathcal B\), define

\[
 \epsilon=\Pr(Z\notin\mathcal B),\quad
 A_d=\mathbb E[\mathbf1_{Z\notin\mathcal B}r_d(Z)],\quad
 K_{de}=\mathbb E[\mathbf1_{Z\notin\mathcal B}r_d(Z)r_e(Z)].
\]

Expanding the square for the same \(B\) outside the box yields

\[
 \mathbb E_\lambda L^2\le
 \sum_{z\in\mathcal B}\Pr(Z=z)S_B(z)+\epsilon\mathbb E_\mu B^2
 +2\sum_d A_d m_d(B\mu)
 +\sum_{d,e}K_{de}m_{\operatorname{lcm}(d,e)}(\mu). \tag{AF3}
\]

Every tail coefficient is a nonnegative rational remainder of complete
geometric moments.  This formula still requires certified bounds for
its inside-box maxima.  The coefficient calculation alone does not
certify those maxima or optimize over all original low tests.

The same fixed test can also weight future charge observations.  Put
\(W_B=(C-B^2)_+\).  For an increasing convex \(\ell\)-Lipschitz cost
\(g\), with charge cylinders independent of the final test, define

\[
 H_{B,g}(z)=\max_{(D_d)}\int W_B\,
   g\left(\sum_d w_d(z)\mathbf1_{D_d}\right)d\mu.
\]

The usual auxiliary comparison applies after multiplication by the
nonnegative old-point weight \(W_B\).  Comparing a fixed charge layout
to its zero-depth load gives

\[
 H_{B,g}(z)\le H_{B,g}(0)+\ell\sum_d r_d(z)m_d(W_B\mu).
\]

Thus its complete outside contribution is bounded by
\(\epsilon H_{B,g}(0)+\ell\sum_d A_d m_d(W_B\mu)\).  The charge layout
remains independent of the fixed final \(B\); \(W_B\mu\) is not
renormalized.  These observations are under \(\lambda\), and the actual
higher-deletion transfer is still required before using them under
\(\nu=\lambda(\cdot\mid F)\).

<a id="a-concrete-aligned2-consumer-on-the-same-pg1-law"></a>
#### A concrete aligned2 consumer on the same PG1 law

Take \(M_0=315\), \(h=(2,1,1)\), and the unchanged canonical PG1
probability on its75 actual points.  For all twelve original low labels,
fix \(C_d=2\bmod d\).  The exact calculation gives

\[
 \mathbb E_\mu B^2=\frac{10606504844}{1000000007},\quad
 2\sum_d\gamma_dm_d(B\mu)=\frac{4754413927}{1000000007},
\]

\[
 \sum_{d,e}\kappa_{de}m_{\operatorname{lcm}(d,e)}(\mu)
   =\frac{74198115637}{24000000168},\qquad
 U(B)=\frac{442860166141}{24000000168}.
\]

The saved cross-term amount relative to independent intersection caps
is \(3949851830/3000000021\).  For every nonnegative low function \(f\),
the original higher-label union bound gives

\[
 \int_{F^c}f\,d\lambda\le\mathcal R(f\mu)
       :=\sum_d\gamma_dm_d(f\mu).
\]

Because \(L\ge B\), a head reference \(K\) satisfies

\[
 Q(\mathbb E_\nu L^2-K)
 \le U(B)+\mathcal R((K-B^2)_+\mu)-K,
 \qquad Q=\lambda(F).
 \tag{AF4}
\]

At \(K=29\), the positive part is necessary since \(B\) can equal12.
The exact deletion upper bound is \(37233260707/3000000021\), giving

\[
 e_B=\frac{14908748975}{8000000056},\qquad
 G_B(Q)\le29+\frac{e_B}{Q}.
\]

The existing source survival lower bound
\(q_0=25428074957/48000000336\) therefore gives
\(G_B\le826866667603/25428074957<32.517864\).

For the 11/13 consumer, the zero-tail tuple carries this complete
original \(B\).  Keep the existing unrestricted square bound for the
other tuples.  With \(M=4/3\) and \(P=1403/630\), its preconditioning
square bound is \(M G_B+(P-M)G\).  Using only the independent final
survival certificate gives \(\Gamma_{13,B}<149.020\).

The stronger current signed-charge criterion uses the same actual
source \(Q\).  In its final-root \((2,2)\) branch, replace only the
zero-tail contribution:

\[
 A_{\rm new}=A_{\rm old}+\frac43(29-33),\qquad
 B_{\rm new}=B_{\rm old}+\frac43(e_B-e_{22}),
\]

where \(e_{22}\) is the original9 square excess at reference33.  This
retains the already certified charge bounds and physical kernels.  The
resulting whole criterion is \(A_{\rm new}+B_{\rm new}/Q\), with

\[
 A_{\rm new}=-\frac{584839}{8470},\qquad
 B_{\rm new}=\frac{9318930413060408641498726373}
                   {262685549314111332327187500}>0.
\]

Its maximum is at \(q_0\) and is negative.  Applying the existing
positive final surviving mass gives the concrete consumer

\[
 \Gamma_{13,B}\le
 \frac{163558856448790578417793670359}
      {1113264631887138059499843750}<146.919. \tag{AF5}
\]

This fixes all twelve original low classes, not just roots \((2,2)\).
All higher original test residues and all finite physical heights
remain unrestricted.  Equation(AF5) does not replace the uniform
\(\Gamma_{13}<148.650\) bound over arbitrary low tests.

<a id="boundary-of-the-inexpensive-relaxation-and-replay"></a>
#### Boundary of the inexpensive relaxation and replay

The ordinary union-bound version of(AF4) does not uniformly dominate
the existing global head square bound.  The genuine low test
\(C_d=68\bmod d\), evaluated at reference33, gives

\[
 U(B)=\frac{463549739429}{24000000168},\qquad
 \mathcal R((33-B^2)_+\mu)=\frac{340267738535}{24000000168}.
\]

The resulting value of the explicit upper-bound functional is
\(862761418421/25428074957>33.929\), above the existing head bound
\(33.73365775325071\).  This is a boundary fixture for that inexpensive
relaxation, not a lower bound on the actual test moment.  A global
improvement must control the combined objective for every independent
low-test layout, or use a stronger observation.

`verify_pg1_anchored_square.py` and
`pg1_anchored_square_certificate.json` recompute these exact observations,
both consumers, the boundary fixture, and all first/second outside-box
coefficients for \((8,5,4)\).  Direct depth summation is checked against
factored one-prime moments.  The aligned2 outside square contribution
in(AF3) is \(26237873570245030831/918922731432459075000\); its inside
maxima are not evaluated by this certificate.  Existing survival and
charge inputs are separately verified hash-bound prerequisites.

These are ordinary general inequalities and exact rational consumers;
no new Lean declaration or general odd-covering resolution is claimed.
Replay from the repository root:

    python3 -I -O docs/reports/erdos7-odd-covering/verify_pg1_anchored_square.py

<a id="exact-signed-digit-optimization-with-the-old-load-fixed"></a>
### Exact signed digit optimization with the old load fixed

`ExactSignedDigitDP` optimizes the six original labels
`7,21,35,63,105,315` independently. Its input is the old support `X`, one
fixed load `A[x]`, and exact integer or rational tables `scores[y][i][k]`.
The returned maximum is over every original residue of those six labels.
`labels` gives a realizing residue modulo each original modulus; the
program recomputes its score directly. All seven digits participate,
and one representative of every distinct old cylinder, including an
empty cylinder when realizable, is retained.

For example, after importing the adjacent module:

```python
oracle = ExactSignedDigitDP(old_points)
result = oracle.optimize(old_loads, scores)
maximum = result['value']
original_residues = result['labels']
```

Each table row is indexed by the total load, including the old load;
provide entries from zero through `A[i]+6`. Zero tables represent absent
points. The constructor's old-cylinder states can be reused for multiple
queries. The production dependency is Python's standard library only.

For digit `y` and label subset `S`, the program computes exactly

\[
g_y(S)=\max_{(b_c)_{c\in S}}
 \sum_{x\in X}\phi_{xy}\left(A_x+
       \sum_{c\in S}1_{x\equiv b_c\pmod c}\right).
\]

Every original label belongs to precisely one digit block. Conditional
on this partition, different blocks have disjoint labels and physical
point sets, so their old-residue choices are independent. Conversely,
CRT realizes every block choice separately for each original modulus.
Thus `D[0]=0`, unreachable entries are `None`, and the recurrence
`new[S]=max(old[S xor T]+g_y[T] for T subset S)` gives exactly the
maximum. The nonzero baseline `g_y[empty]` is included once for each
digit. This is a finite optimization argument and an exact arithmetic
implementation; no Lean formalization is claimed.

The old-modulus label is a singleton on the old support. After fixing
the other old residues, its additional score is the largest pointwise
increment. Zero is also a candidate exactly when an empty old cylinder
exists. In particular, a full old carrier cannot replace a negative
singleton increment by zero. On PG1 the cylinder counts are
`1,3,5,6,8,17`; eliminating that singleton leaves 3024 old states across
all subset masks. Seven stages use 5103 subset transitions. The full
old-test search has 12240 mask combinations and 11808 distinct load
vectors; only this count, not an optimization over all those vectors,
is included here.

The existing `verify_point_geometry.FixedADP` supports the nonnegative
square bound. It adds independently maximized unary and pair terms to
form each block, with old-residue compatibility relaxed, and processes
digits 1 through 6. Its `point_fixedA_dp_exact.py` replay certifies those
integer upper-bound calculations, not the exact signed block problem.
The new program reuses the subset-partition structure while computing
each block by compatible old-residue enumeration.

After placing the files beside the canonical PG1 source, replay the
deterministic certificate with:

```text
python3 -I -O verify_exact_signed_digit_dp.py
```

The verifier reads the adjacent
`mod3_conditioned_geometry_certificate.json`, selects PG1, and binds
that source file's SHA-256. `--source PATH` selects another location
for the same canonical source. `--write` generates
`exact_signed_digit_dp_certificate.json`; the default operation compares
the complete exact recomputation with the stored certificate and does
not write. The certificate contains no timing fields. Twelve seeded
rational, signed, nonconvex fixtures agree with brute-force enumeration
of the original modulus residues. Other checks cover the nonzero
empty-block baseline, absent digit zero, empty singleton gain zero, and
the unavoidable gain −1 on a full old carrier.

On the actual PG1 law, fix each old residue to 2 modulo its cofactor.
At actual points 1 and 46, set the score to
`-mu(t)*(B(t)-A(t mod45)-1)^2`, and zero elsewhere. Both points have
weight numerator 14690784 and common denominator 1000000007. The
unrestricted optimum is 0; a common-digit restriction gives exactly
`-14690784/1000000007`. A realizing independent choice uses residues
4 modulo7 and 1 modulo21, with the other four labels at digit zero.
This gives a strict counterexample on the original carrier and law.

The concrete joint fixture is

\[
 E_\mu[\tfrac43(B+R)^2+\tfrac16(149-B^2)(L-4)_+].
\]

At depth `(1,1,1)`, `R` uses each higher-label multiplicity `w_d-1`
and `L` uses each full multiplicity `w_d`. Their fixed auxiliary
comparison residues are given in the certificate. These are independent
of the fixed original low classes defining `B`. Three points have negative
quadratic coefficient. With the old load fixed as above, the exact
optimum is `223040367109/3000000021`. The common-digit restriction gives
`223011181693/3000000021`, so independent digits improve the objective
by `9728472/1000000007`. A maximizing witness assigns digits5 to the
first five labels and digit4 to the old45 label, with original
residues `(5,5,12,5,47,32)` modulo `(7,21,35,63,105,315)`. The checker
replays those residues on all 75 actual points. This is a one-depth,
fixed-auxiliary instance with coefficients `4/3`, `1/6` and threshold4;
it is not a final continuation or all-height bound.

For the whole original315 floor objective, collect the moment and
weighted-charge terms into one point score table before this query.
This implementation then exactly eliminates the six original7 label
choices for one fixed old load and one fixed auxiliary profile. A
global certificate still needs every old load and a complete bound
over the auxiliary moment/charge profiles, including the omitted
depth tail. At each fixed collection of auxiliary depths, finite maxima over old
loads, auxiliary profiles, and final residues commute. This does not
interchange a maximum with an expectation over depths, and sampled
auxiliary profiles supply no upper bound for the complete maximum. No global-floor improvement follows
from the two fixtures above.

<a id="exact-optimization-of-arbitrary-point-scores-over-all-twelve-low-labels"></a>
### Exact optimization of arbitrary point scores over all twelve low labels

Fix the 75-point PG1 carrier and its original probability law from
`mod3_conditioned_geometry_certificate.json`. Its projection modulo 45 has
16 points. Put

\[
\mathcal C=\{1,3,5,9,15,45\},\qquad
\mathcal D=\mathcal C\cup7\mathcal C.
\]

For each \(d\in\mathcal D\), independently choose an original residue
\(a_d\bmod d\), and let

\[
B(x)=\sum_{d\in\mathcal D}\mathbf1_{x\equiv a_d\pmod d}.
\]

The \(d=1\) label is the constant low-test term; it is not a proposed
admissible modulus in an odd covering. For any supplied integer tables
\(s_x(k)\), \(x\) in the PG1 carrier and \(0\le k\le12\), the new oracle
computes exactly

\[
\max_{(a_d)_{d\in\mathcal D}}\sum_x s_x(B(x)).
\tag{AL1}
\]

Scores may have either sign and arbitrary curvature. Empty residue classes
and all seven digits, including zero, remain legal. This quantifies over all
twelve low-test labels for the supplied score table. It does not quantify
over an external family of auxiliary profiles or arbitrary physical heights;
those obligations remain with the caller.

Write \(x_i\) for the 16 old points. The old load is
\(A_i=\sum_{c\in\mathcal C}\mathbf1_{x_i\equiv a_c\pmod c}\).
Keeping one original residue for each distinct old-cylinder mask gives
\(1,3,5,6,8,17\) choices for the six cofactors, including empty masks.
The 12,240 combinations yield exactly 11,808 distinct realizable vectors
\(A\); one actual residue witness is retained for each vector.

For fixed \(A\), each label \(7c\) independently chooses a digit
\(y\bmod7\) and an old residue modulo \(c\). Coprimality makes these
choices equivalent to one original residue modulo \(7c\). For a subset
\(S\subseteq\mathcal C\), define

\[
H_y(S;A)=
\max_{(b_c)_{c\in S}}
\sum_i s_{y,i}\left(A_i+
  \sum_{c\in S}\mathbf1_{x_i\equiv b_c\pmod c}\right),
\tag{AL2}
\]

where absent physical points have identically zero tables. For subsets not
containing 45, the implementation enumerates all 3,024 old-residue states
across the 32 subsets. Adding label 45 either hits one old point or a legal
empty class. At a given state with loads \(k_i\), its exact best increment is

\[
\max\left(0,\max_i[s_{y,i}(k_i+1)-s_{y,i}(k_i)]\right).
\tag{AL3}
\]

The zero option is justified by an actual empty modulo-45 class on PG1.
It is not a monotonicity assumption.

Partition the six labels among the seven digits using

\[
V_0(\varnothing)=0,\qquad
V_{y+1}(S)=\max_{T\subseteq S}
  \bigl[V_y(S\setminus T)+H_y(T;A)\bigr],
\tag{AL4}
\]

with other initial states unreachable. The empty block
\(H_y(\varnothing;A)\) retains its actual score, which need not be zero.
Every original residue assignment induces exactly such a partition and
old-residue choices, and every choice in this recurrence lifts by CRT to
original residues. Thus \(V_7(\mathcal C)\) is the exact fixed-\(A\)
maximum. Maximizing it over all 11,808 realizable \(A\) proves (AL1).

`pg1_signed_score_oracle.py` accepts either `point_scores[75][13]`, in the
source PG1 point order, or `scores[7][16][13]`, in digit then old-point
order. The optional positive integer `denominator` gives the common score
denominator. It returns the exact maximum, twelve original residue labels,
and all 75 maximizing loads. The original Python signed optimizer checks
the maximizing old load, and a separate literal twelve-label evaluation
checks the reported score. The C++ executable is compiled temporarily from
the adjacent source, or supplied with `--binary`; raw inputs and complete
value tables are temporary. The driver checks

\[
4\sum_{y,i}\max_k|s_{y,i}(k)|<2^{61},
\]

which bounds all signed 64-bit score, difference, and recurrence
intermediates. The C++ raw-input format is an internal contract of this
guarded driver.

For the existing actual-coefficient fixture at depth \((1,1,1)\), retain
exactly the moment and charge auxiliary residues in
`exact_signed_digit_dp_certificate.json`. Reconstruct its objective as

\[
\mathbb E_\mu\left[
  \frac43(B+R)^2+\frac16(149-B^2)(L-4)_+
\right].
\tag{AL5}
\]

Here \(\mu\) is the same PG1 law with denominator \(N=1000000007\).
The integer score table is
\(w_x[8(k+R(x))^2+(149-k^2)(L(x)-4)_+]\), with denominator \(6N\).
Three actual points have negative quadratic coefficient. The exact
all-low-label maximum is

\[
\frac{80520608091}{1000000007}
=80.52060752735575\ldots .
\tag{AL6}
\]

One maximizing witness has residues
\((0,2,3,5,8,23)\) at moduli \((1,3,5,9,15,45)\), and
\((5,5,33,5,68,68)\) at moduli \((7,21,35,63,105,315)\).
The latter six all have digit 5. The maximum after restricting them to a
common digit, while still maximizing over every old \(A\), equals (AL6).
Thus the global independent-versus-common-digit gap for this particular
fixed auxiliary profile is zero.

The earlier fixed-\(A\) counterexample is unchanged: at old residues
\((0,2,2,2,2,2)\), the independent and common-digit maxima remain
\(223040367109/(3N)\) and \(223011181693/(3N)\), respectively, with
strict gap \(9728472/N>0\). Equality of the two maxima after optimizing
over all old loads does not imply equality at each old load, or validate a
common-digit restriction for other score tables.

`verify_pg1_all_low_scores.py` reconstructs (AL5) from the original
auxiliary residues and source weights, runs the complete optimization,
and compares 32 spread old loads, including the earlier fixed load, against
the original Python optimizer. It compares the deterministic
`pg1_all_low_scores_certificate.json` by default; only `--write` rewrites
the certificate. This is an exact finite optimization program and
certificate, not a Lean formalization or a solution of unrestricted #7.

<a id="a-reference-optimal-boundary-for-the-old-pg1-anchored-functional"></a>
### A reference-optimal boundary for the old PG1 anchored functional

Keep the actual PG1 low probability \(\mu\), its higher357 lift, the
original modulus labels and the actual survival event \(F\) unchanged.
Write \(Q=\Pr(F)\). The existing independent survival certificate gives

\[
 q_0=\frac{25428074957}{48000000336}\le Q\le1.
\]

For every \(d\mid315\), select the genuine original low class
\(47\pmod d\), including the constant class at \(d=1\), and let
\(B=\sum_{d\mid315}\mathbf1_{47\bmod d}\). The all-height AF1 estimate is

\[
 U(B)=\mathbb E_\mu B^2+
  2\sum_{d\mid315}\gamma_d m_d(B\mu)+K_{\rm high}
  =\frac{156034880279}{8000000056},
 \qquad K_{\rm high}=\frac{74198115637}{24000000168}.
\]

Here, with \(S(d)=\{p:v_p(d)=h_p\}\) and \(h=(2,1,1)\),

\[
 a_d=\prod_{p\in S(d)}\frac p{p-1},\quad \gamma_d=a_d-1,
 \quad
 b_{de}=\prod_{p\in S(d)\cap S(e)}\frac{p(p+1)}{(p-1)^2}
          \prod_{p\in S(d)\triangle S(e)}\frac p{p-1},
\]

and \(K_{\rm high}=\sum_{d,e}(b_{de}-a_d-a_e+1)
m_{\operatorname{lcm}(d,e)}(\mu)\). These are complete geometric moments,
with no finite-height cutoff.

Let \(R_{\rm old}\) be the existing grouped-deletion operator, including
its complete nonnegative remainder. Explicitly its groups are
\((9,45)\), \((5,15,45)\), the extra class at \(35\), and
\((7,21,35,63,105,315)\); its remaining cylinder coefficients are

\[
 \rho_d=\gamma_d-\frac12\mathbf1_{d\in\{9,45\}}
  -\frac14\mathbf1_{d\in\{5,15,45,35\}}
  -\frac16\mathbf1_{7\mid d}\ge0.
\]

The exact mass calculation is

\[
 R_{\rm old}(\mu)=\frac{22571925379}{48000000336}=1-q_0.
\]

For every real reference \(K\), define

\[
 e(K)=U(B)+R_{\rm old}\bigl((K-B^2)_+\mu\bigr)-K,
 \qquad H(K)=\max_{q_0\le Q\le1}\left(K+\frac{e(K)}Q\right).
\]

Then the exact result is

\[
 \boxed{\min_{K\in\mathbb R}H(K)
       =\frac{853585952201}{26129684197}
       =32.66728927014747\ldots.}                                      \tag{RB1}
\]

This is a boundary for **fixed AF1, fixed \(R_{\rm old}\), and the
independent interval \([q_0,1]\)**. It is not a lower bound for a true
moment or an upper bound over all low tests. It does not apply to a new
deletion operator, a larger certified survival, a stronger AF1 bound,
or a whole-cost criterion coupling other costs to the same \(Q\).
In particular it leaves open an improvement of the current uniform
head bound \(33.73365775325071\ldots\) to a value above (RB1).

For completeness, monotonicity, subadditivity and positive homogeneity
of \(R_{\rm old}\) give, whenever \(K_2-K_1=\Delta>0\),

\[
 -\Delta\le e(K_2)-e(K_1)\le-q_0\Delta.                              \tag{RB2}
\]

Indeed the difference of the positive-part inputs lies pointwise between
zero and \(\Delta\), and \(R_{\rm old}(\Delta\mu)=\Delta(1-q_0)\).
Thus \(e\) is continuous, strictly decreasing, and tends to opposite
infinities at the ends of the real line. It has a unique zero \(K_*\).
For \(e(K)\ge0\), \(H(K)=K+e(K)/q_0\) is nonincreasing by (RB2).
For \(e(K)\le0\), \(H(K)=K+e(K)=U(B)+R_{\rm old}((K-B^2)_+\mu)\)
is nondecreasing. Therefore the global minimum is \(H(K_*)=K_*\).
The negative excess retains the actual common denominator; it is not
independently divided by \(q_0\).

On \([32,33]\) the positive-part support is fixed to \(B\le5\).
Every feasible combined deletion witness is consequently affine in \(K\).
The exact endpoint oracles and one feasible original-residue witness give

\[
 R_{\rm old}((K-B^2)_+\mu)=\alpha K-\beta\quad(32\le K\le33),
 \quad\alpha=\frac{21870316139}{48000000336},\quad
 \beta=\frac{82623329473}{48000000336}.                              \tag{RB3}
\]

To see why the interior equality follows, the maximum of the witness
lines is convex and lies above this feasible line. Equality at both
endpoints forces equality throughout the interval by convexity. The
endpoint signed excesses are

\[
 e(32)=\frac{5812019299}{16000000112}>0,\qquad
 e(33)=-\frac{2173406575}{12000000084}<0.
\]

The unique zero is therefore in this interval, and (RB3) gives
\(K_*=(U(B)-\beta)/(1-\alpha)\), proving (RB1).

`verify_pg1_anchored_reference_boundary.py` reconstructs the law, AF1
coefficients, complete deletion remainder, exact endpoint maxima and
the realizing group and cylinder residues. It binds both canonical
PG1 and original9 source certificates by SHA256. It reuses the existing
`group_setup` and `group_oracle`; no depth-box square maxima are rerun.
The certificate contains rational results and witnesses, with no timing
or exploratory-search data. The default operation compares the entire
recomputation; `--write` explicitly regenerates it:

```text
python3 -I -O verify_pg1_anchored_reference_boundary.py
```

This is an ordinary proof with an exact arithmetic verifier; no new Lean
formalization is claimed.
