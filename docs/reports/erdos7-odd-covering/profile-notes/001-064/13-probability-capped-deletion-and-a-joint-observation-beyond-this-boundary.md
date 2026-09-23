[Index](../../marked_head_profile.md) · [Previous](12-complete-original-low-test-anchoring-at-arbitrary-prime-power-heights.md) · [Next](14-joint-observation-guidance-from-the-polynomial-closed-graphs.md)

<a id="probability-capped-deletion-and-a-joint-observation-beyond-this-boundary"></a>
### Probability-capped deletion and a joint observation beyond this boundary

On a finite support, the old operator has the form
\(R(v)=\max_{g\in\mathcal G}v\cdot g\) for nonnegative finite-measure
vectors \(v\), where \(\mathcal G\) is finite, nonempty and nonnegative.
Define

\[
 R_{\rm cap}(v)=\min_{0\le\sigma\le v}
       [\mathbf1\cdot(v-\sigma)+R(\sigma)].                           \tag{RC1}
\]

Using \(v=\mu f\) and \(\sigma=\mu h\) handles zero masses without any
division: conversely set \(h_x=\sigma_x/\mu_x\) only when \(\mu_x>0\),
and set \(h_x=0\) otherwise. If \(\theta\) is the actual conditional
deletion vector, \(0\le\theta\le1\) and \(\theta\cdot\sigma\le R(\sigma)\)
give \(\theta\cdot v\le R_{\rm cap}(v)\). The actual event is unchanged.

Finite LP duality gives

\[
 R_{\rm cap}(v)=\max_{r\in P}v\cdot r,\qquad
 P=\{r:0\le r\le1,\ \exists\bar g\in\operatorname{conv}\mathcal G,
       \ r\le\bar g\}.                                               \tag{RC2}
\]

In detail, use primal variables \(t,\sigma\ge0\), constraints
\(\sigma\le v\), \(g\cdot\sigma\le t\), and objective
\(\mathbf1\cdot v-\mathbf1\cdot\sigma+t\). Its dual has multipliers
\(\lambda_g,y_x\ge0\), \(\sum_g\lambda_g\le1\),
\(y_x+\sum_g\lambda_g g_x\ge1\). Both programs are feasible.
Minimizing \(y_x\) and filling any missing nonnegative \(\lambda\) mass
gives \(\max_{\bar g\in\operatorname{conv}\mathcal G}
\sum_x v_x\min(1,\bar g_x)\), equivalent to (RC2).
The downward closure in \(P\) is necessary; \(\operatorname{conv}
\mathcal G\cap[0,1]^X\) alone can be empty. The existing formal
prerequisite is `FiniteStrongDuality.ValidELP.strong_duality_of_both_feasible`
in `D5/S3/Analytic/Convexity/FiniteStrongDuality.lean`.

The capped operator is monotone and sublinear. For nonnegative costs
\(Z_j\ge b_j(x)\), coefficients \(a_j\ge0\), a common event \(F\), and
\(\mathbb E\sum_j a_jZ_j\le U\), put \(b=\sum_j a_jb_j\). Then

\[
 Q\left(\mathbb E\left[\sum_j a_jZ_j\mid F\right]-K\right)
 \le U-K+R_{\rm cap}((K-b)_+\mu).                                    \tag{RC3}
\]

If \(K=\sum_j a_jK_j\), the last deletion term is at most
\(\sum_j a_jR_{\rm cap}((K_j-b_j)_+\mu)\). Taking the positive part
after summing can exploit cancellation, and one maximizing deletion
vector can replace several independent maximizers. This proves a
comparison of bounds, not a strict PG1 improvement.

Since \(P\) is downward closed, its support function at a signed vector
equals its support function at that vector's positive part. If
\(q_{\rm cap}=1-R_{\rm cap}(\mu)>0\), the unique zero of
\(U-K+R_{\rm cap}((K-b)_+\mu)\) is therefore exactly

\[
 \max_{r\in P}
 \frac{U-\sum_x\mu_xb_xr_x}{1-\sum_x\mu_xr_x}.                       \tag{RC4}
\]

All denominators are at least \(q_{\rm cap}\); the same vector \(r\)
appears in the numerator and the survival probability. The maximization
is an upper relaxation, not an assertion of physical attainability.

For the AF1 head objective alone, fixing cross-cap witnesses produces
a nonnegative linear coefficient \(a_x\). Its capped point score obeys

\[
 k^2+a_xk+r_x(K-k^2)_+
 =\max\{k^2+a_xk,(1-r_x)k^2+a_xk+r_xK\},                             \tag{RC5}
\]

which is increasing and convex for \(k\ge0\), \(0\le r_x\le1\).
This permits removal of empty original classes from that head-only
maximization. It does not establish common-digit alignment or convexity
of a full joint charge objective containing additional negative
quadratic terms.

<a id="an-auxiliary-majorant-covering-every-original-low-test"></a>
### An auxiliary majorant covering every original low test

Another sufficient global bound retains the old operator. Express
\(U(B)+R_{\rm old}((K-B^2)_+\mu)\) as

\[
 K_{\rm high}+\max_{z_j\in Z_j}\sum_x
       [\mu_xB_x^2+\sum_j c_{j,x}(B_x)z_{j,x}],                        \tag{MX1}
\]

where cross-cap terms have \(c_{j,x}(k)=2\gamma_d\mu_xk\), remainder
caps have \(c_{j,x}(k)=\rho_d\mu_x(K-k^2)_+\), and the grouped term
has \(c_{j,x}(k)=\mu_x(K-k^2)_+\). Each \(Z_j\) is its complete cylinder
or grouped-witness family. These auxiliary maxima are independent in
the old upper functional; no joint physical realization is assumed.

Each separate witness satisfies \(0\le z_{j,x}\le1\). For the grouped
term, writing \(A\in\{0,1,2\}\), \(B_5\in\{0,1,2,3\}\),
\(E\in\{0,1\}\), \(S\in\{0,\ldots,6\}\), and \(b=B_5+E\), its
numerator is

\[
 24A+(2-A)[6b+(4-b)S]\le24A+24(2-A)=48.
\]

The complete old vector after adding remainders need not be bounded by
one and must remain separated into these auxiliary terms.
Choose nonnegative vectors \(q_j=(q_{j,x})_x\), fixed throughout the
maximization over \(B\), and put \(h_j(q)=\max_{z\in Z_j}q\cdot z\).
The pointwise inequality \(cz\le(c-q)_++qz\) yields

\[
 \max_B[U(B)+R_{\rm old}((K-B^2)_+\mu)]\le V(K;q),
\]
\[
 V(K;q)=K_{\rm high}+\max_B\sum_x
 [\mu_xB_x^2+\sum_j(c_{j,x}(B_x)-q_{j,x})_+]+\sum_jh_j(q_j).           \tag{MX2}
\]

The middle term can be evaluated by the exact independent-digit and
all-old-layout optimizer; every \(h_j\) needs its complete cap or group
oracle. Sampled witnesses give no upper certificate for \(h_j\).
For the actual same survival \(Q\), the resulting uniform head bound is

\[
 \Gamma\le
 \begin{cases}
 K+(V-K)/q_0,&V\ge K,\\
 V,&V\le K.
 \end{cases}                                                         \tag{MX3}
\]

In particular, \(V(T;q)\le T\) suffices for \(\Gamma\le T\).
Neither (RC1)--(RC5) nor (MX1)--(MX3) asserts that a concrete all-low-test
threshold has been met; each specifies an observation beyond the fixed
functional whose limitation is certified by (RB1).

<a id="a-finite-dual-obstruction-to-the-reference33-price-family"></a>
### A finite dual obstruction to the reference33 price family

For every nonnegative price vector in (MX2), at the fixed reference
\(K=33\), the unchanged PG1 law satisfies

\[
 V(33;q)\ge
 \frac{824892275704058867603}{24000000168000000000}
 >34.3705112470.                                                     \tag{MX4}
\]

Improving the existing uniform head bound \(G\) at this reference
would require

\[
 V(33;q)<33+q_0(G-33)
 =\frac{460223929211132040332029}{13783840971486886125000}
 <33.388656338.                                                       \tag{MX5}
\]

Thus this entire price family cannot improve that head bound at
reference33. This is a limitation of the upper-envelope family, not
a lower bound for an actual moment. Another reference, a different
majorant, and costs combined on one actual event remain outside it.

Here is the finite certificate argument. Prices can be restricted to
\(0\le q_{j,x}\le\max_{1\le k\le12}c_{j,x}(k)\): reducing a price
above that endpoint leaves its positive part zero and cannot increase
the nonnegative support function. Retain 34 actual twelve-label tests
in the maximum over \(B\), 60 actual group profiles in its support
function, and all original residues in every other cylinder support.
Restricting either maximum decreases (MX2), giving a lower relaxation
of its best achievable value.

The epigraph formulation of this relaxation has 15617 variables and
15677 inequalities. Positive-part variables are bounded by their
coefficient maxima, cylinder and group epigraphs by the supports of
those maxima, and the test epigraph by
\(144+\sum_{j,x}\max_k c_{j,x}(k)\). After normalization all variables
lie in \([0,1]\); these bounds preserve the minimum. For the negated
objective \(c^Tx\), integer constraints \(Ax\le b\), and any
nonnegative rational multiplier vector \(z\),

\[
 c^Tx\le b^Tz+\sum_j\max\{c_j-(A^Tz)_j,0\}
 \qquad(0\le x_j\le1).                                               \tag{MX6}
\]

The retained dual has 1536 nonzero entries. Exact evaluation of every
residual in (MX6), followed by negation and restoration of
\(K_{\rm high}\), gives (MX4). This argument requires the retained
profiles to be feasible; their completeness is unnecessary for a
lower relaxation. In contrast, evaluating an upper certificate in
(MX2) requires complete maximization.

`verify_pg1_maxplus_obstruction.py` reconstructs every test load and
group profile as original congruence classes on the 75 actual points,
the complete geometric coefficients, the epigraph matrix, and the
integer dual calculation. Its adjacent certificate binds both source
files by SHA256. The replay uses only the Python standard library,
with no numerical optimizer or floating-point premise:

```text
python3 -I -O verify_pg1_maxplus_obstruction.py
```

This is an ordinary finite dual argument with exact arithmetic evidence,
not a new Lean theorem or an improved uniform PG1 constant.

<a id="transfer-of-the-pg1-law-after-a-bounded-loss-of-low-mass"></a>
### Transfer of the PG1 law after a bounded loss of low mass

The all-height moment bound \(35\) now covers \(1,172\) carrier orbits
on the PG1 old45 shape, including \(53\) inclusion-minimal orbits.
The former support-containment transfer covered \(232\) orbits and one
minimal orbit. The increase follows from restricting the existing PG1
probability to another actual carrier while controlling the discarded
probability mass.

Let \(A\) be the fixed PG1 low carrier, \(\mu\) its certified law,
and \(\lambda\) its uniform lift to arbitrary finite physical 3/5/7
heights. For an arbitrary higher forbidden family with distinct original
moduli, let \(F\) be its actual survivor event. The source certificate
gives, simultaneously for every original-label test load \(L\),

\[
 Q=\lambda(F)\ge q_0=\frac{25428074957}{48000000336}>0,
 \qquad \mathbb E_\lambda[L^2\mid F]\le
 G=\frac{492647095380812739054683}{14604022456869186140625}.
\]

For another actual low carrier \(B\), write \(t=\mu(A\setminus B)<q_0\).
More generally, any same-law observation \(\mathbb E_\lambda[Z\mid F]\le C\)
with a pointwise floor \(Z\ge c\) transfers on this one target law as
\[
 \mathbb E_\lambda[Z\mid F\cap B]
 \le c+(C-c)\frac{q_0}{q_0-t}.                                     \tag{WL0}
\]
The proof below uses \(Z=L^2,c=1\); replacing \(L^2-1\) by \(Z-c\)
proves (WL0). The coordinate map and target law are chosen once per
carrier, independently of the test and of which observation is consumed.

The unit test class gives \(L\ge1\). Use the target's higher
forbidden family in the source theorem, so the higher event \(F\) is
unchanged. With \(s=\lambda(F\cap B^c)\le t\),

\[
 \mathbb E_\lambda[(L^2-1)\mathbf1_{F\cap B}]
 \le \mathbb E_\lambda[(L^2-1)\mathbf1_F]\le(G-1)Q.
\]

Since \(Q-s\ge q_0-t>0\), this proves

\[
 \mathbb E_\lambda[L^2\mid F\cap B]
 \le1+(G-1)\frac{Q}{Q-s}
 \le1+(G-1)\frac{q_0}{q_0-t}.                                      \tag{WL1}
\]

The target low law is \(\mu(\cdot\mid B)\); its uniform high lift,
conditioned on \(F\), is exactly \(\lambda(\cdot\mid F\cap B)\).
Under that normalized lift the survival lower bound is

\[
 q_{\rm target}\ge\frac{q_0-t}{1-t}>0.                              \tag{WL2}
\]

This normalization is separate from the actual \(Q\) and \(s\) used in
(WL1). The source and target low forbidden lists are not combined into
a new distinct-modulus family; the restricted measure is simply
supported on the target's allowed low points.

In particular the source bounds \(\mathbb E L\le5\) and
\(\mathbb E(L-2)_+\le3\) from the same original9 certificate become
\(\mathbb E L\le1+4q_0/(q_0-t)\) and
\(\mathbb E(L-2)_+\le3q_0/(q_0-t)\). Any existing source bounds
\(H_4\le C_4\), \(H_6\le C_6\) likewise transfer to
\(H_4\le C_4q_0/(q_0-t)\), \(H_6\le C_6q_0/(q_0-t)\), using floor
zero. These observations and the square bound hold on the same target
law and remain available to a subsequent 11/13 argument.

For target moment \(35\), (WL1) requires only

\[
 t\le t_{35}:=\frac{q_0(35-G)}{34}
  =\frac{2311711326201096983399}{117162648257638532062500}
  =0.019730787589554016\ldots.                                     \tag{WL3}
\]

With source denominator \(N=1000000007\), this is equivalent to an
integer discarded numerator at most \(19730787\). All \(75\) single
points and \(251\) of the \(2775\) unordered pairs meet the threshold.
Three points can meet it, but no four points can; the unrestricted
weighted matching below includes the three-point possibility.

The permitted old-coordinate maps preserve the old45 support and
permute mod9 children within their mod3 roots and mod5 columns. They
extend to full mod9/mod5 permutations by filling the missing children
and columns. A single common permutation of the six nonzero mod7
digits fixes digit zero. For each prime with baseline height \(h_0\),
extend the low permutation by
\(a+p^{h_0}z\mapsto\pi(a)+p^{h_0}z\). This preserves every lower
prefix and leaves higher digits unchanged. CRT therefore maps every
original cylinder to a cylinder of the **same original modulus**, at
every finite height, and preserves uniform high fibers. Pulling back
the target's higher family and tests makes (WL1)--(WL2) valid after
every permitted coordinate map. Row-dependent mod7 permutations are
not used.

For exact computation, write \(w_{s,i}\) for the PG1 weight numerator
at seven digit \(s\) and old row \(i\), with zero for absent points.
Let \(M_1,\ldots,M_6\) be the target's deletion masks, padded with
empty masks. For an allowed old map \(p\), the assignment cost is

\[
 C_p(s,j)=\sum_iw_{s,i}\mathbf1_{p(i)\in M_j}.
\]

The minimum discarded numerator is exactly
\(\min_p\min_{\pi\in S_6}\sum_sC_p(s,\pi(s))\). The verifier
evaluates all \(12\) old maps and all \(720\) digit permutations using
integers, then replays every chosen minimum on the \(75\) original
source points. The old-map group and the complete digit permutations
make eligibility invariant across each target orbit, justifying the
state counts from orbit sizes.

The complete domain is \(153,997\) actual mask states in \(34,160\)
orbits. It contains \(102,083\) essential states in \(21,524\) orbits
and \(10,554\) inclusion-minimal orbits. The essential and minimal
domains are independently reconstructed and checked against the
existing classification hashes. The resulting counts are:

| Admitted source loss | Actual states | Carrier orbits | Essential orbits | Minimal orbits |
|---|---:|---:|---:|---:|
| Zero | 1,648 | 232 | 1 | 1 |
| At most one point | 6,871 | 1,146 | 70 | 50 |
| At most two points, subject to (WL3) | 7,073 | 1,172 | 73 | 53 |
| Full weighted threshold (WL3) | 7,073 | 1,172 | 73 | 53 |

Thus the full weighted search adds \(5,425\) actual states, \(940\)
carrier orbits and \(52\) minimal orbits. The equality of the last two
rows is a computed result, not an assumption excluding three-point loss.

One newly covered minimal carrier has canonical deletion masks
\((1,2320,8456,25352,44378)\). Its certificate gives all eleven original
low modulus/residue pairs, reconstructs their actual complement, and
gives an allowed coordinate map under which only source point \(271\)
is lost. Its exact estimates are

\[
 t=\frac{14288471}{1000000007},\qquad
 \Gamma\le
 \frac{492253195359590634804683}{14210122435647081890625}
 <34.642<35.
\]

For the combined count, the existing C2 law covers \(152\) orbits and
one minimal orbit on `root2_other_same_column`. On
`root1_same_other_column`, the uniform box and row-weighted law cover
\(562+531-16=1077\) orbits and \(8+1=9\) minimal orbits; their overlap
is subtracted using their existing certificate. These two shapes and
the PG1 shape are distinct. Thus the combined target35 count increases
from \(1461\) to \(2401\) carrier orbits and from \(11\) to \(63\)
minimal orbits. Of the \(56966\) minimal orbits in the six-shape
classification, \(56903\) remain outside these certified domains.
These are conditional higher357 results; they do not complete the
unrestricted-prime continuation or settle the general odd-covering problem.

`verify_pg1_weighted_carrier_transfer.py` binds the six canonical source
certificates by SHA256, rebuilds the entire matching domain, and compares
the summary, witnesses and domain hashes with
`pg1_weighted_carrier_transfer_certificate.json`. It retains no duplicate
table of all \(34,160\) orbit calculations. Existing moment certificates
on the other two shapes are inherited, not rerun as new moment bounds.
No optimizer or network is needed. The default operation only compares;
`--write` explicitly regenerates the certificate:

```text
python3 -I -O verify_pg1_weighted_carrier_transfer.py
```

The conditioning and lifting arguments are ordinary all-height proofs
with an exact finite matching verifier. No new Lean finite-instance
endpoint is claimed.

Within the larger family of all \(2!3!4!=288\) normalized old-coordinate
maps, dropping the source-stabilizer restriction cannot extend this
particular transfer to another old shape. These maps fix the mod3 roots,
missing mod9 child4 and mod5 column0. The source mass on old rows mapped
outside the target old support is lost before any mod7 choice. Exact
enumeration gives the following minimum lost numerators, all with
denominator \(1000000007\):

| Target old shape | Minimum lost numerator |
|---|---:|
| `root1_same_other_column` | 120057768 |
| `root1_other_same_column` | 145937820 |
| `root1_other_other_column` | 87566988 |
| `root2_same_other_column` | 32378894 |
| `root2_other_same_column` | 83395212 |

Every value exceeds the permitted \(19730787\), independently of
subsequent mod7 permutations or mixed-label choices. On the source
shape exactly its twelve stabilizers pass this necessary old-row test.
The same verifier reconstructs all \(6\times288\) old-row losses and
checks each against the original 75-point calculation. This boundary
concerns the fixed PG1 probability, bound35 and specified normalized
map family; other probabilities and transfer constructions remain open.

<a id="exact-zero-depth-geometry-strengthens-the-same-pg1-law"></a>
### Exact zero-depth geometry strengthens the same PG1 law

Keeping one realizable layout for all twelve original low labels gives
the all-height bounds

\[
 G_{\rm new}=
 \frac{491665320264992331169931}{14604022456869186140625}
 <33.666432,\qquad
 \Gamma_{13}\le
 \frac{165356424839074723126151405953}
      {1113264631887138059499843750}<148.532901.                 \tag{ZD1}
\]

These use the same PG1 low probability, its uniform higher357 lift,
the target's actual higher357 survival event, and the same subsequent
11/13 kernels. All finite physical exponents and complete auxiliary tails
remain included. The mean and hinge estimates on this law still apply.
The improvement does not settle the other low geometries or the
unrestricted prime continuation.

For the original roots \((i,j)\), let \(H_{ij}(z)\) be the previously
certified minimum of the pure7 and fixed-A square relaxations. At
\(z=(0,0,0)\), there are no higher auxiliary labels. The all-low-label
integer oracle therefore computes the exact value

\[
 h_{ij}=\max_{\substack{\text{all twelve original low classes}\\
                         C_3=i,\ C_9=j}}
             \mathbb E_\mu B^2.                              \tag{ZD2}
\]

All 11808 distinct old loads are evaluated. The restriction to each
root pair is reconstructed from every original old-cylinder choice
before deduplication, so a load with several original-label realizations
retains every admissible root pair. The six seven-divisible labels keep
their independent digits, including digit zero and empty cylinders.
Each of the ten maximizing witnesses is independently evaluated by the
Python subset recurrence and by its literal twelve congruences on all
75 points. All ten values improve their previous relaxations. For the
source's worst pair \((2,2)\),

\[
 H_{22}(0)=\frac{11408985958}{1000000007},\qquad
 h_{22}=\frac{11331111635}{1000000007}.                         \tag{ZD3}
\]

At this depth each root's unrestricted digit optimum equals its common
digit optimum. Thus this particular gain comes from retaining the
realizable old-cylinder geometry, without requiring a strict gap between
those two digit maxima. Other signed costs have the distinct behavior
documented above.

The complete outside-box estimate (M9-5) remains valid with its exact
zero-depth term: for each actual layout its nonnegative square increment
is bounded by the same pair-cap polynomial increment, after which its
zero-depth square is at most \(h_{ij}\). For
\(\mathcal B=[0,8]\times[0,5]\times[0,4]\), write

\[
 p_0=\Pr(Z=0)=\frac{16}{35},\qquad
 \beta=\Pr(Z\in\mathcal B)
  =(1-3^{-9})(1-5^{-6})(1-7^{-5}).
\]

Replacing only that depth and the outside-box anchor therefore gives

\[
 U'_{ij}=U_{ij}-(p_0+1-\beta)(H_{ij}(0)-h_{ij}).               \tag{ZD4}
\]

The other 269 depth bounds and every outside increment coefficient are
unchanged. With the original deletion functional and reference33, put
\(e'_{ij}=U'_{ij}+R((33-b_{ij}^2)\mu)-33\). The common positive survival
bound is still \(q_0=25428074957/48000000336\). Applying (M9-6) gives
\(G_{\rm new}=33+\max(0,\max e'_{ij})/q_0\), the first value in (ZD1).
The maximum remains at \((2,2)\).

For the signed 11/13 consumer, let \(e_*\) and \(e'_*\) denote the old
and new root maxima. In each of its three complete criterion candidates,
replace the inverse-\(Q\) coefficient \(B_{ij}\) by

\[
 B'_{ij}=B_{ij}-(P-M)(e_*-e'_*)-M(e_{ij}-e'_{ij}),\qquad
 M=\frac43,\quad P=\frac{1403}{630}.                          \tag{ZD5}
\]

Every resulting coefficient remains positive. Consequently each complete
criterion is still largest at \(Q=q_0\); its constant and all charge
observations remain unchanged. Selecting complete candidates and then
maximizing over all final roots gives the second value in (ZD1), now
with worst roots \((2,5)\). Positive final survival is supplied by the
same independent bound as before. This remains above the square-only
17/19 seed threshold; it is an improved upper bound, not a lower bound
on the actual moment.

The bounded-loss transfer also permits the larger sufficient budget

\[
 t\le\frac{q_0(35-G_{\rm new})}{34}
  =\frac{143201953863449880529}{6891920485743443062500}
  =0.020778236510371237\ldots.                                \tag{ZD6}
\]

For the integer source weights this is a lost numerator of at most
20778236. The previously certified carrier counts remain valid; no
new complete orbit count is asserted for the larger budget.

`verify_pg1_exact_zero_depth.py` and
`pg1_exact_zero_depth_certificate.json` reconstruct (ZD2), the original
root domains, all complete geometric coefficients, (ZD4)--(ZD6), and the
prior rational criteria from hash-bound source certificates. The 269
nonzero-depth maxima and earlier charge geometry are inherited, separately
verified prerequisites. This is an ordinary all-height argument with an
exact arithmetic certificate, without a new Lean endpoint.

<a id="combining-all-original-root-floors-on-one-source-event"></a>
### Combining all original-root floors on one source event

The square and charge estimates can retain all their original-root floors
before using the higher357 deletion functional. Fix the final root pair
\(i\), put \(C=149\), \(W_i=C-b_i^2\), and write
\(g_j=(b_j-2)_+\). Because \(b_j\in\{1,2,3\}\), this also equals
\((2b_j-5)_+\), the floor for the second whole charge cost. Let

\[
 M=\frac43,\quad P=\frac{1403}{630},\quad
 c_1=\frac4{33},\quad c_2=\frac{50}{2541},\quad
 c_h=\frac{31}{5082},\quad c_0=\frac2{847}.
\]

The coefficients \(c_h,c_0\) include the complete multiplier tail from
13. Retain independent original-root pairs \(h,u,v\) for the other head
square, second whole charge and threshold-two hinge. Their joint floor is

\[
 f_{i,h,u,v}=M b_i^2+(P-M)b_h^2
                +c_2W_i g_u+c_hW_i g_v+c_0W_i.              \tag{JF1}
\]

The threshold-four and first whole costs have nonnegative floor zero;
their upper contributions remain present. Denote their existing
unconditional weighted upper bounds by \(U_{4,i}\) and \(U_{1,i}\),
and denote the second whole and hinge upper bounds by
\(U_{2,i,u}\) and \(U_{H,i,v}\). The ordinary source square bounds
\(U'_i,U'_h\) are those of (ZD4). Put

\[
 V_{i,h,u,v}=MU'_i+(P-M)U'_h+\frac{U_{4,i}}6+c_1U_{1,i}
               +c_2U_{2,i,u}+c_hU_{H,i,v}
               +c_0\mathbb E_\mu W_i.                     \tag{JF2}
\]

For each set of actual tests realizing these roots, its nonnegative
combined source cost \(Z\) satisfies \(Z\ge f_{i,h,u,v}\) and
\(\mathbb E_\lambda Z\le V_{i,h,u,v}\). These are bounds on the
same source law. No simultaneous attainment of the individual upper
bounds is assumed. Auxiliary mixtures are covered by their pure-root
vertices: their integral bound is affine, and the positive-part deletion
bound below is convex, in each such mixture. Empty original classes may
first be moved to nonempty classes at the nonnegative actual-cost level;
no monotonicity of the resulting signed criterion is assumed.

For any source reference \(K\), use the actual common event \(F\),
\(Q=\lambda(F)\), and the existing nonnegative deletion functional \(R\):

\[
 \begin{aligned}
 Q(\mathbb E_\nu Z-K)
 &=\mathbb E_\lambda Z-K
       +\mathbb E_\lambda[(K-Z)\mathbf1_{F^c}]\\
 &\le V_{i,h,u,v}-K+
       R\bigl((K-f_{i,h,u,v})_+\mu\bigr).                  \tag{JF3}
 \end{aligned}
\]

Thus all ten choices of each of \(h,u,v\) must be retained for each
of the ten final pairs. Combining their floors before the positive part
and deletion support can improve over taking separate deletion bounds.
This argument uses the published \(R\); it does not require the further
probability-capped functional \(R_{\rm cap}\).

Let \(\delta\) upper-bound the right side of (JF3) for all 10000
combinations. Since \(q_0\le Q\le1\), a valid source bound is

\[
 T=\begin{cases}K+\delta/q_0,&\delta\ge0,\\
                 K+\delta,&\delta<0.\end{cases}           \tag{JF4}
\]

The physical 11/13 estimate still uses \(C=149\), independently of
the auxiliary source reference \(K\). Its positive final survival
\(r\le1\) satisfies
\(r(\Gamma_{13}-C)\le\mathbb E_\nu Z-C\le T-C\).
When \(T<C\), this gives \(\Gamma_{13}\le T\); a negative source
excess is never divided by the smaller lower bound \(q_0\).

Keeping the separate criterion as a second bound sharpens (JF4). Put
\(E^S_j=U'_j+R((33-b_j^2)\mu)-33\), and for the final weight define

\[
 \begin{aligned}
 E^N_{i,u}&=U_{2,i,u}+R((444-W_i g_u)\mu)-444,\\
 E^H_{i,v}&=U_{H,i,v}+R((444-W_i g_v)\mu)-444,\\
 E^W_i&=\mathbb E_\mu W_i+R((b_i^2-1)\mu)-148.
 \end{aligned}
\]

All deletion inputs here are nonnegative. Applying the separate signed
inequalities on the same event gives

\[
 Q(\mathbb E_\nu Z-K)\le A Q+B_{i,h,u,v},\qquad
 A=33P+444(c_2+c_h)+148c_0-K,
\]
\[
 B_{i,h,u,v}=ME^S_i+(P-M)E^S_h+\frac{U_{4,i}}6+c_1U_{1,i}
                 +c_2E^N_{i,u}+c_hE^H_{i,v}+c_0E^W_i.       \tag{JF5}
\]

For the fixed \(K=297/2\), \(A=-803146/12705<0\). Hence
\(Aq_0+B_{i,h,u,v}\) is a rigorous upper bound on the source excess.
It also bounds the joint expression in (JF3): expand \(K-f\) as the
sum of the preceding nonnegative deletion costs and the nonnegative
constant \(-A\), and use the positive homogeneity and subadditivity
of \(R\), with \(R(\mu)=1-q_0\). In decreasing order of these separate
bounds, a combination can be skipped once its bound is no larger than
the greatest joint expression already evaluated. This covers all 10000
combinations with ten direct joint evaluations and 9990 justified skips.
Sixteen new distinct grouped-deletion evaluations suffice, with other
queries inherited from their hash-bound prior certificates.

Exact calculation with the new source squares gives

\[
 \delta=-\frac{167157392171127017840563}
                 {3898857874792004932500000},\qquad
 B_*:=\max B_{i,h,u,v}
   =\frac{35204985686553987468638773289}
          {1050742197256445329308750000}>0.
\]

Both inequalities apply for every \(Q\in[q_0,1]\). Therefore

\[
 \mathbb E_\nu Z\le
 \max_{q_0\le Q\le1}
 \left[K+\frac{\min(\delta,AQ+B_*)}{Q}\right].              \tag{JF6}
\]

The two terms inside this minimum are monotone after division by \(Q\):
\(\delta/Q\) increases because \(\delta<0\), whereas
\(A+B_*/Q\) decreases because \(B_*>0\). The maximum is consequently
found among the two endpoints and the unique crossing, if it lies in
the interval. Here the crossing

\[
 Q_* =\frac{19341582772973446474593583}
                 {36445882274521174135800000}
\]

lies in that interval and supplies the largest of the three exact
values. It follows that the same physical 11/13 law satisfies

\[
 \boxed{\displaystyle
 \Gamma_{13}\le
 \frac{3452976366440462440938598284408403}
      {23265022838471110091964891311550}
 <148.419213.}                                              \tag{JF7}
\]

`verify_pg1_common_source_floor.py` and
`pg1_common_source_floor_certificate.json` reconstruct the original
root domain, every pruning bound, the new grouped-deletion evaluations
and the three complete \(Q\) candidates. They bind the original
charge tables and the zero-depth certificate by hash; the full prior
profile geometry is a separately verified prerequisite. The remaining
arbitrary-prime continuation is open. This certificate supplies ordinary
exact arithmetic, not a new Lean theorem.
