[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](02-current-bounds-and-comparisons.md) · [Next](04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md)

<a id="adaptive-kernels-lower-the-unrestricted-cutoff-to-19"></a>
### Adaptive kernels lower the unrestricted cutoff to 19

Keep the same actual pure-head product law \(P_0\), but use the coupled
mixed-head bound \(M=82/135\) proved in (CM1)--(CM2). The full initial
auxiliary product has mean \(16/5\) and second moment \(325/18\).
All physical coordinate heights resolve the entire original family,
including classes whose largest prime has not yet been processed.
Its head caps remain \(2\cdot3^{-e},(4/3)5^{-e},(6/5)7^{-e}\).
For each successive prime \(q\ge19\), choose a deterministic integer
threshold \(1\le t_q\le q-2\), and set
\[
 s_q=q-1-t_q,\qquad
 \delta_q=\frac{t_q-1}{q-2},\qquad c_q=\frac{q-1}{s_q}.
 \tag{AD1}
\]
Then \(s_q\ge1\), \(0\le\delta_q<1\), and \(c_q<q\), so
\(\Pr(K_q\ge e)=c_qq^{-e}\) is a valid auxiliary height law.
The normalized actual kernel preserves every old marginal, including
\(P_0\), and satisfies these caps conditional on the entire history.
At \(t_q=1\), the kernel has \(\delta_q=0\) and equals the identity
density relative to the pure-survivor base law; this endpoint is valid.

Let \(D_q\) be the completed auxiliary product for the earlier primes
under this one fixed schedule, and put \(V_q(t)=\mathbb E(D_q-t)_+\).
The original-label comparison (PH3) and the full moment identities give
\[
 b_q\le\frac{V_q(t_q)}{s_q},\qquad
 \mathbb E D_{\mathrm{new}}=\mathbb E D_q(1+1/s_q),\qquad
 J_{\mathrm{new}}=J_q\left(1+\frac{3q-1}{s_q(q-1)}\right).
 \tag{AD2}
\]
Here \(J_q=\mathbb E D_q^2\) also bounds every complete-layout
second moment under the same actual law. Thus, starting with
\(\lambda=53/135\), each certified step updates
\(\lambda_{\mathrm{new}}=\lambda-V_q(t_q)/s_q\).
One final conditioning bounds the supported parameter by
\[
 \Gamma_{\mathrm{supported}}\le
 1+\frac{J_{\mathrm{new}}-1}{\lambda_{\mathrm{new}}}
 =1+\frac{(J_q-1)s_q+J_q(3q-1)/(q-1)}
              {\lambda s_q-V_q(q-1-s_q)}.
 \tag{AD3}
\]
Only positive denominators are admissible. Every subsequent auxiliary
distribution includes the previously chosen factor \(1+K_q\);
charges and moments from different schedules are never combined.

For finding a schedule, minimizing this one-step potential is a useful
finite search. Since \(D_q\) is integer-valued, \(V_q\) is affine
between integer thresholds, making (AD3) fractional-linear on each such
interval. A zero denominator approaches infinite cost. On the remaining
interval \(0<s<1\), write
\(V_q(q-1-s)=A+Bs\), where \(A\ge0\) and \(B\ge0\).
Feasibility forces \(\lambda>B\), and differentiating (AD3) gives
a negative numerator \(-(J_q-1)A-J_q(3q-1)(\lambda-B)/(q-1)\).
Thus \(s=1\) dominates that interval; integer thresholds suffice for
the local search. This asserts no global schedule optimality.
BBMST Section 6, Lemma 6.2 and equation (25) already use sequential
potential minimization; (AD3) uses the full stop-loss profile in place
of their scalar recurrence. The proof below needs only the admissibility
and exact replay of the selected schedule.

**Exact stopping certificate.** The fixed schedule has 1388 steps, one
for every prime from 19 through 11593. Its largest threshold is 3072.
The existing [verifier](../verify_star_block_obstruction.py)
recomputes `adaptive_head_stoploss` in the adjacent
[certificate](../certificates/star_block_obstruction_certificate.json).
It propagates the full first and second moments separately
and retains all product probabilities needed in
\[
 V_q(t)=\mathbb E D_q-t+
       \sum_{1\le d<t}(t-d)\Pr(D_q=d).
\]
All displayed data coefficients are nonnegative. Upward rounding on
the grid \(10^{-18}\) therefore gives upper bounds for the charges and
moments; discarded larger product states cannot return below a later
threshold, since every factor is at least one. The resulting bounds are
\[
 \begin{aligned}
 C&\le956616008688320979/10^{18}<1,\\
 J&\le2341844006153474338859/10^{18},\\
 \Gamma_{\mathrm{supported}}
 &\le\frac{2340887390144786017880}{43383991311679021}
 <53958
 <\frac{26988288270685431527657582636743677951}{5\cdot10^{32}}
 <k(\log k+\log\log k-3)^2,\qquad k=1395.
 \end{aligned}
 \tag{AD4}
\]
The global index is \(\pi(11593)=1395\), including 2 and all absent
primes. The rational stopping lower bound exceeds 53976 and is produced
by the existing positive-series logarithm bounds. Positive actual
survivor mass and (AD4) satisfy BBMST Theorem 6.1. After the one
conditioning, set \(i_0=k\), \(\mu_{i_0}=1\) and
\(\kappa=\Gamma_{\mathrm{supported}}\); (T1)--(T2) supply its
moment hypothesis for every later standard uniform-base kernel schedule.
No second division by the prefix survivor probability is needed.
The continuation and finite CRT handle all remaining tail primes. No bound on tail support,
exponents or graph structure is introduced. This proves the arbitrary
\(3^a5^b7^c\) row from prime 19. It remains an ordinary mathematical
proof with an exact arithmetic certificate, not an end-to-end Lean proof.
An independent implementation using target-state divisor convolution
reproduces every charge and the full retained-state digest; independent
trial division and positive-series logarithm bounds also give
\(k=1395\) and stopping threshold greater than 53976.

**Adaptive continuation of both 5040 odd heads from prime 13.** The
same argument applies to the finite head laws (PH2), retaining their
terminal atoms. For \(Q\mid315\), use head mean \(21/8\), second
moment \(399/40\) and mixed charge \(49/120\). For \(Q\mid945\),
these are \(45/16\), \(189/16\) and \(157/336\). Process every
tail prime from 13 with a fixed integer-threshold schedule as in (AD1).
The directed certificates give:

| Head bound | Last prime | Global index | Tail steps | Total charge upper | Supported \(\Gamma\) upper |
|---|---:|---:|---:|---|---|
| 315 | 1021 | 172 | 167 | \(808205363366166533/10^{18}\) | \(470837795264907661091/191794636633833467<2455\) |
| 945 | 32141 | 3448 | 3443 | \(243263384072888041/(25\cdot10^{16})\) | \(4873698555453475972051/26946463708447836<180866\) |

For the two rows the exact second-moment upper bounds are respectively
\(58955750078534228453/(125\cdot10^{15})\) and
\(974934321797953504843/(2\cdot10^{17})\). The verified BBMST
stopping lower bounds are
\[
 \begin{aligned}
 k=172:\quad&
 \frac{616354713939123394926331754277098284347}
      {25\cdot10^{34}}>2465>2455,\\
 k=3448:\quad&
 \frac{22610845432447282250071455861855940497071}
      {125\cdot10^{33}}>180886>180866.
 \end{aligned}                                     \tag{AD5}
\]
Both total charges are strictly below one. All comparisons and the
single final conditioning concern the same actual measure, so (AD5)
restarts BBMST and proves noncoverage with unrestricted tails from 13.
The existing verifier reproduces `finite_315_tail13_adaptive` and
`finite_945_tail13_adaptive` in its adjacent certificate, including
every selected threshold and charge.
The certificate retains 192 and 8192 low product states, respectively;
their omitted high-state contributions remain in the full moments.
As in the arbitrary-height case, the schedules are verified directly
without requiring a proof of global control optimality. The head
exponents bound the entire original family, including later-ending
moduli. Independent divisor-convolution implementations reproduce every
step and both full retained-state digests; independent prime counting
and positive-series logarithm bounds verify the displayed stopping
inequalities. These are ordinary proofs with exact certificates.

<a id="homogeneous-cylinder-capacities-and-the-extremal-comb"></a>
### Homogeneous cylinder capacities and the extremal comb

**Theorem.** Let \(p\ge2\), \(H\ge0\), and give every node of a full
\(p\)-ary tree at absolute depth \(d\) the same capacity \(\beta_d\ge0\).
A feasible flow is a nonnegative leaf measure whose mass below each
node does not exceed its capacity. A forbidden node has zero mass,
including all its descendants. Forbidden nodes have positive depth,
with at most one at each depth; redundant descendants are allowed. Among all
such forbidden assignments, the smallest maximum root flow is attained
by the comb with forbidden prefixes \((p-1)^{e-1}0\), \(1\le e\le H\).
Repeated digits are meant here. No monotonicity of the capacities is needed.

Let \(F_d\) be the full-subtree maximum and \(C_d\) the comb maximum.
Their recursions, evaluated from depth \(H\) upward, are
\[
 F_H=C_H=\beta_H,\qquad
 F_d=\min(\beta_d,pF_{d+1}),\qquad
 C_d=\min(\beta_d,(p-2)F_{d+1}+C_{d+1}).               \tag{HC1}
\]
Every actual assignment has maximum root flow at least \(C_0\).
In particular, if \(\beta_0=C_0=1\), every actual tree supports a
probability law with all these cylinder caps. The law may depend on
the actual forbidden prefixes and need not be the comb law.

**Proof.** An unblocked node's maximum is the minimum of its capacity
and the sum of its children's maxima. Attainment follows by splitting
any permitted mass among the children within their individual maxima,
then realizing these masses recursively; scaling handles all smaller
masses. This also covers zero capacities. Put
\(s_d=pF_{d+1}-F_d\ge0\). If child \(i\) has deficit \(\ell_i\) from
\(F_{d+1}\), the parent's deficit from \(F_d\) is exactly
\[
 F_d-\min(\beta_d,pF_{d+1}-\sum_i\ell_i)
       =(\sum_i\ell_i-s_d)_+.                        \tag{HC2}
\]
A directly forbidden child has deficit \(F_{d+1}\); its forbidden
descendants have no further effect.

A stronger induction keeps track of allowed absolute depths. For
\(A\subseteq\{d+1,\ldots,H\}\), define \(L_H(\varnothing)=0\) and
\[
 L_d(A)=\left[
 {\bf1}_{d+1\in A}F_{d+1}
 +L_{d+1}(A\cap\{d+2,\ldots,H\})-s_d
 \right]_+.                                         \tag{HC3}
\]
This is the comb deficit when it uses exactly the depths in \(A\).
At a selected depth the spine has one blocked child, \(p-2\) full
children and one continuing child; at an unselected depth it has
\(p-1\) full children and the continuation. The continuing terminal
leaf is allowed, giving the zero base deficit.

Downward induction proves that \(L_d\) is monotone in \(A\) and
superadditive for disjoint sets:
\(L_d(A\cup B)\ge L_d(A)+L_d(B)\).
For the latter, the next-depth indicators add, and the induction
hypothesis bounds the later loss of the union below by the sum.
The final positive-part step uses
\((u+v-s)_+\ge(u-s)_++(v-s)_+\) for \(u,v,s\ge0\):
if both exceed \(s\), the difference is \(s\); if exactly one does,
the other adds a nonnegative amount; otherwise the right side is zero.
Monotonicity follows directly from (HC3).

Now consider any actual nonforbidden node of depth \(d\) whose permitted
forbidden depths are \(A\). Let \(\epsilon\) indicate a directly blocked
child. For each other child let \(A_i\) be the set of deeper forbidden
depths occurring below it. These sets are pairwise disjoint because
globally at most one node is forbidden at each depth; they are contained
in \(A'=A\cap\{d+2,\ldots,H\}\). Discard redundant deletions inside a
directly forbidden child. Induction, superadditivity and monotonicity give
\[
 \sum_i\ell_i
 \le\epsilon F_{d+1}+\sum_i L_{d+1}(A_i)
 \le{\bf1}_{d+1\in A}F_{d+1}+L_{d+1}(A').
\]
Equation (HC2) bounds the parent's deficit by \(L_d(A)\). At the root
with every positive depth allowed, this is \(F_0-C_0\), proving (HC1)'s
extremal assertion. Missing or redundant exclusions cannot worsen it.

The theorem applies to distinct pure prime-power moduli because they
give at most one forbidden prefix at each depth. Homogeneity by depth
and this global multiplicity bound are essential hypotheses of the
argument; arbitrary node-dependent capacities or several exclusions at
one depth are outside its scope. It does not identify the maximum
complete-layout second moment of the resulting measure.

**Sharp scalar-cap boundary for the ternary comb.** At height \(H\ge1\),
forbid \(3^{e-1}-1\bmod3^e\), equivalently prefix \(2^{e-1}0\) in
least-significant-digit order. For any supported probability \(\mu\), put
\(\beta_e=\max_{r\bmod3^e}\mu(r)\) and \(R(\mu)=\sum_{e=1}^H\beta_e\).
Then
\[
 \min_\mu R(\mu)=1-2^{-H}.                            \tag{HC4}
\]
Indeed, let \(b_j\) be the mass escaping the spine through digit 1 at
depth \(j\), and \(S_e=\sum_{j\le e}\beta_j\). Before depth \(e\),
the spine carries \(1-\sum_{j<e}b_j\ge1-S_{e-1}\).
Its two allowed children each have mass at most \(\beta_e\), so
\(2\beta_e\ge1-S_{e-1}\) and \(S_e\ge(1+S_{e-1})/2\).
Starting with \(S_0=0\) yields the claimed lower bound.

For attainment, split each spine mass equally between its digit-1
escape and digit-2 continuation; make escaped suffixes uniform.
Escape \(j\) has mass \(2^{-j}\), and the final spine leaf has mass
\(2^{-H}\). At depth \(e\), a cylinder in an earlier escape \(j<e\)
has mass \(2^{-j}3^{-(e-j)}\le2^{-e}\), while the new escape and
continuing spine each have mass \(2^{-e}\). Thus \(\beta_e=2^{-e}\).
The uniform-survivor law instead has
\(R=(3^H-1)/(3^H+1)\), which is larger when \(H\ge2\).

The optimum in (HC4) tends to one. Consequently no fixed
\(\varepsilon>0\) improves the scalar bound to \(R\le1-\varepsilon\)
for every ternary family and height. With the usual independent 5/7
caps, the mixed-head max-cap envelope \((1+9R)/15\) tends to \(2/3\).
This is a limitation of that envelope; the actual bad mass has the
strictly smaller bound (CM1).

The scalar minimizer does not minimize every quantity used by the tail
argument. Its auxiliary height has \(\Pr(K\ge e)=2^{-e}\),
\(1\le e\le H\), and \(X=1+K\) obeys
\[
 \mathbb EX=2-2^{-H},\qquad
 \mathbb EX^2=6-(2H+5)2^{-H},\qquad
 \mathbb E(X-j)_+=2^{1-j}-2^{-H}\quad(1\le j\le H).
\]
The stop-loss function is linear between integer thresholds, equals
\(\mathbb EX-t\) for \(t\le1\), and is zero for \(t\ge H+1\).
At infinite height its values \(2^{1-j}\) exceed the uniform-survivor
auxiliary values \(3^{1-j}\) for every integer \(j\ge2\), and its second
moment is 6 instead of 5. Optimizing \(R\) alone therefore does not
supply a tail-profile improvement.

These are ordinary all-height proofs. The existing
[verifier](../verify_star_block_obstruction.py)
records **homogeneous_comb_capacity** in its
[certificate](../certificates/star_block_obstruction_certificate.json):
5832 exact flow comparisons over all 729 ternary height-three forbidden
assignments and eight capacity profiles, including nonmonotone and zero
caps, together with the binary-split laws at heights 1 through 6.
The finite checks supplement the proofs and are not Lean kernel proofs.
The general recursive comparison (HC1)--(HC3) is formalized by
[`HomogeneousCombCapacity.comb_le_actual_prefix_flow`](../../../../D5/S3/Arith/Congruence/HomogeneousCombCapacity.lean).
Its Boolean obstacle predicate is on actual finite words; the per-depth
count includes redundant forbidden descendants. It proves the comparison
for arbitrary \(p\ge2\), heights and nonnegative capacity profiles,
without assuming the deficit aggregation inequality. Its formal conclusion
compares the explicit min/sum recursions. The separate constructive theorem
[`PrefixCapacityRealization.exists_comb_capped_probability`](../../../../D5/S3/Arith/Congruence/PrefixCapacityRealization.lean)
now realizes these capacities by actual nonnegative leaf weights with total
mass one. Every forbidden prefix has zero mass, and every depth-\(d\)
prefix has probability at most \(\beta(d)/\mathrm{combFlow}\), provided
the comb flow is positive. Its proof constructs actual child measures and
scales their sums before applying the existing comparison. Both capacity
theorems work over any linearly ordered field, including the rationals;
the normalized rational weights directly form the imported `FiniteLaw`.
The licensed `ThreePrime/DistortionChain` supplies `PhysicalChain`, its
covered-probability bound, and `BaseCaps` propagation without a restriction
on the number of prime factors per modulus. The actual ordinary-cover
connection and residual-cylinder base-cap interface are formalized below;
cofactor completion and numerical stopping still have to be connected
in the end-to-end formalization.

The actual uniform survivor law is supplied by
[`PurePrefixResidualLaw.exists_exact_residual_law`](../../../../D5/S3/Arith/Congruence/PurePrefixResidualLaw.lean).
For every integer alphabet size \(p\ge3\), height \(H\ge0\) and one arbitrary
forbidden prefix at each positive depth, it removes prefixes with forbidden
ancestors, retaining a disjoint set \(R\) with the same forbidden union.
The theorem constructs the rational law on actual surviving words and
proves its positive normalizer
\(Z=1-\sum_{e\in R}p^{-e}\). For every test prefix \(u\) at depth \(d\),
a forbidden ancestor gives zero probability; otherwise its probability is
\[
 \frac{p^{-d}-\sum_{e\in R:\,f_e\text{ extends }u}p^{-e}}{Z}.
\]
The proof derives the disjoint decomposition from the given words, using
shortest forbidden ancestors and prefix nesting. Conditioning, individual
prefix counts and positivity are reused from the licensed development.
The actual ordinary-cover consumer is now formalized by
[`ActualCylinderChain.ordinary_cover_forces_charge_and_caps`](../../../../D5/S3/Arith/Congruence/ActualCylinderChain.lean).
For any finite distinct odd covering system, choose a cut after the first
\(b\) prime coordinates and any rational probability law \(\mu\) on their
full prime-power words. The head coordinates may be correlated. Assume
\(\mu\) gives probability one to avoiding every actual head-only cylinder.
For arbitrary rational tail thresholds \(0\le\delta_i<1\), the theorem
builds the actual full-history tail chain \(P_x\) at each fixed head point
and proves
\[
 1\le\mathbb E_\mu\bigl[\mathrm{totalCharge}(P_x)\bigr].
\]
The licensed CRT and prime-factorization interfaces supply the actual
cylinders and injective original depth labels. All original labels are
retained: different original moduli can have the same tail cofactor after
their head parts are removed. The live support induction proves pure-tail
prefix avoidance with probability one under the same joint law
\(\mu\mathbin{\mathrm{joint}}(x\mapsto P_x.\mathrm{law})\), including
zero-weight ambient points. Gluing the head to the tail diagonal words
transports ordinary coverage to a charged mixed-cylinder hit.
The same theorem derives `BaseCaps` for every \(P_x\) from the explicit
residual-cylinder inequalities
\(\Pr(C_{c,b+i})\le(1-\delta_i)\,\mathrm{survival}_{R_i}(e_{c,b+i})\).
It has no restriction on the number of prime factors per modulus. The
empty-head specialization recovers the pure-coordinate product-base result.

The head input resolves the **full** prime-power heights of the original
family. A finite315 law directly addresses a head dividing315; preserving
its marginal when higher head powers are added requires an additional
argument and is not assumed. Transporting a concrete arithmetic head law
to the full word interface, completing cofactor labels and proving an
average charge below one remain obligations for an end-to-end noncoverage
theorem. No numerical noncoverage endpoint is imported.

<a id="sharp-tail-profiles-of-maximal-cylinder-caps"></a>
#### Sharp tail profiles of maximal cylinder caps

The preceding scalar boundary extends to all positive-part thresholds.
Let \(p\ge3\) be any integer alphabet size, and let \(R_H\) be the actual
survivors of the same comb at height \(H\ge1\). Their number is
\(N_H=((p-2)p^H+1)/(p-1)\). For any probability \(\mu\) on \(R_H\),
let \(\beta_e(\mu)\) be its largest actual depth-\(e\) cylinder mass.
Then
\[
 \min_\mu\sum_{e=1}^H\beta_e(\mu)
     =\frac{1-(p-1)^{-H}}{p-2},\qquad
 \min_\mu\sum_{e=j}^H\beta_e(\mu)
     =\frac{p^{H-j+1}-1}{(p-2)p^H+1}\quad(2\le j\le H).
 \tag{HC5}
\]
The uniform survivor law attains all the second set of objectives
simultaneously. It need not attain the first. The proof of (HC4) extends
to the first identity: at each spine fork there are \(p-2\) escapes and
one continuation, giving
\((p-1)\beta_e\ge1-(p-2)S_{e-1}\), hence
\(S_e\ge(1+S_{e-1})/(p-1)\). Equal splitting between the \(p-1\) allowed
children, followed by uniform escaped suffixes, attains this lower bound.

Here is a matching transport dual for the second identity. Partition
\(R_H\) into its \(p-2\) full escape subtrees at each depth \(d\), each
with \(p^{H-d}\) leaves, plus the terminal spine singleton. Put
\(\lambda=(p^{H-j+1}-1)/((p-2)p^H+1)\). Supply at selected depth \(e\)
is \(p^{H-e}\); each escape group demands \(\lambda\) times its leaf
count, and the terminal singleton demands \(\lambda\). A depth can
supply a group only after its escape, and can supply the terminal only
at \(H\). Total supply equals total demand.

These availability sets are nested. For every \(k\ge j\), the groups
escaping at or after \(k\), together with the terminal, contain
\(((p-2)p^{H-k+1}+1)/(p-1)\) leaves and have available supply
\((p^{H-k+1}-1)/(p-1)\). Their demand fits because, writing
\(x=p^{H-k+1}\ge p\),
\[
 \lambda<\frac{p^{1-j}}{p-2}
 \le\frac1{p(p-2)}\le\frac1{p-1}
 \le\frac{x-1}{(p-2)x+1}.                            \tag{HC6}
\]
The last fraction increases with \(x\) and equals \(1/(p-1)\) at \(p\).
For \(k<j\) all supply is available and the corresponding demand is at
most the total; terminal demand is at most the last supply one. Thus a
greedy allocation, filling latest groups from latest available depths,
meets every demand. The suffix inequalities guarantee that the groups
with fewer available depths cannot exhaust their supply prematurely.

If \(q_{e,g}\) is supply assigned to a group of \(n_g\) leaves, give
each full depth-\(e\) cylinder in it dual weight \(q_{e,g}/n_g\).
Such a cylinder has \(p^{H-e}\) leaves. At every selected depth the
weights sum to one; every survivor leaf receives total weight
\(\lambda\). The terminal singleton is an ordinary depth-\(H\) cylinder
and is included. Therefore
\[
 \lambda=\sum_e\sum_C w_C\mu(C)
 \le\sum_{e=j}^H\beta_e(\mu).
\]
Under the uniform law, full cylinders attain
\(\beta_e=p^{H-e}/N_H\); summing them gives \(\lambda\), completing the
proof of (HC5).

These exact finite minima identify a limitation of the marginal-cap
comparison itself. The sequence \(\beta_e\) decreases, so it defines
an auxiliary \(K_H\) with \(\Pr(K_H\ge e)=\beta_e\) and \(K_H\le H\).
For \(X_H=1+K_H\), its integer positive-part values are
\(\mathbb E(X_H-j)_+=\sum_{e=j}^H\beta_e\). The minima in (HC5) converge
to \(1/(p-2)\) at \(j=1\), and to \(p^{1-j}/(p-2)\) at \(j\ge2\).
These are precisely the values of \(X_\infty=1+K_\infty\), where
\[
 \Pr(K_\infty\ge e)=\frac{p-1}{p-2}p^{-e}.
\]
For every fixed real-valued increasing convex function \(\phi\) on the
positive integers, the discrete expansion
\(\phi(x)=\phi(1)+a(x-1)+\sum_{j\ge2}b_j(x-j)_+\) has
\(a,b_j\ge0\). Applying (HC5) to any finite subset of terms, passing to
the lower limit and then taking the supremum of these partial sums gives
\[
 \liminf_{H\to\infty}\inf_{\mu\text{ on }R_H}
    \mathbb E\phi(X_H)\ge\mathbb E\phi(X_\infty).
\]
The uniform finite comb caps increase pointwise to the displayed infinite
caps, so monotone convergence supplies the reverse upper limit. Hence
\[
 \lim_{H\to\infty}\inf_{\mu\text{ on }R_H}
    \mathbb E\phi(X_H)=\mathbb E\phi(X_\infty),         \tag{HC7}
\]
including an infinite value on the right.

Thus changing a pure-coordinate marginal law while retaining only its
largest cylinder masses cannot give a fixed positive improvement in this
worst-case, unbounded-height comparison for any fixed increasing convex
cost. Multiplication by a fixed independent nonnegative auxiliary factor
preserves the needed convexity in this coordinate. This is not an
optimality claim about actual complete-layout loads, correlated head
laws, mixed-head union bounds, or height-dependent objectives. In
particular (CM1)'s improvement uses additional actual head information.

The certificate entry `comb_stoploss_dual_transport` constructs exact
primal and transport-dual witnesses for 84 objectives: \(p=3,5,7\),
\(2\le H\le8\), \(2\le j\le H\). It checks every depth budget and group
coverage with rational arithmetic. The all-height conclusions (HC5)--(HC7)
are the ordinary proofs above, with no new Lean declaration.

<a id="gap"></a>
## Gap

The universal joint-load target Γ73 is false. The complete star family,
with ternary height at least 31 and every other height at least 8, has explicit
survivors but forces `Γ_Q(μ)>139.59>138.877` for every survivor probability,
including correlated and nonuniform laws. The unrestricted Erdős #7 problem
remains open. The conditional prime-tail transfer and height-lifting estimates
remain valid, as does the restricted noncoverage theorem; their proposed
universal head input and all eight displayed finite-base targets are refuted.
A proof of #7 therefore needs a sufficient input that this star family does
not contradict, rather than a sharper proof of the same universal inequality.
The finite-height pure-coordinate CRT criterion and its independent two-block
refinement give `lcm > 11486474` for every hypothetical cover, independently
of the external lcm theorem. This is a finite lower
bound and does not control the unrestricted large-lcm branches.

For the specified complete star assignment, (US1)--(US12) now exclude
**every** tail completion by primes above 73, at arbitrary positive head
heights. The actual broad-branch law, conditional convex comparison and an
exact positive-part calculation reach a supported prefix with `Gamma<4331`
at prime 2039. The BBMST stopping threshold there is greater than 4732, so
all later moduli are unrestricted. This resolves the star's noncoverage
without asserting the false universal `Gamma_73` bound. Other head geometries
remain open. The earlier graph and block-saturation estimates retain their
quantitative survivor-mass and crossing-budget conclusions for subclasses;
for example, matching tails leave more than one tenth of the broad-branch
head points with an uncovered tail lift.

For arbitrary `{3,5,7}` heads the same criterion also proves noncoverage
when all other primes are at least 37 and their interaction graph has
maximum degree at most two, or when all other primes are at least 31 and
each interaction component has at most three vertices. These restrictions
allow arbitrary exponents and arbitrarily many primes in total.

The stronger graph criteria also exclude arbitrary `{3,5,7}` heads with
arbitrary forest tails from prime 17, `2`-degenerate tails from prime 19,
and `5`-degenerate tails, including all planar graphs, from prime 23.
The `20`-degenerate star bound additionally gives an explicit saturated-head
mass estimate above 73. These graph estimates allow unbounded maximum degree,
total prime support, exponents, feedback vertex number and treewidth; the
star theorem (US1)--(US12) now removes their graph restrictions entirely.
For the finite heads supplied by the 5040 connection, the stronger
supported-law bounds additionally exclude every planar tail from prime 17
when the head divides 315, and from prime 19 when it divides 945.
For the other heads, the original-modulus support criterion (RK1)--(RK5)
removes all graph restrictions: arbitrary `{3,5,7}` heads permit at most
two tail primes per modulus from 23, and heads dividing 315 or 945 permit
at most three from 17 or 19 respectively. These conditions allow complete
tail graphs of unbounded size. Moreover, (RK6)--(RK8) impose those support
bounds only on moduli with largest prime at most 8192 for 315 and 945,
or 32768 for arbitrary 357. Above those cutoffs, each original modulus may
have arbitrarily many tail prime factors. The unrestricted-tail theorem (PH1)--(PH7) now removes
these support restrictions entirely for the three stated head and prime-gap
hypotheses. Thus every hypothetical cover must involve at least one of
11, 13, 17, 19; their unrestricted interaction is not settled here.
The star row is superseded as a noncoverage result by (US1)--(US12).

**H73 — false**, with its universal candidate statement retained from
[the target preregistration](https://github.com/the-omega-institute/trureturing/issues/8167):
let `Q` be any product of arbitrary finite powers of odd primes at most 73.
Choose one residue `a_d` for every divisor `d > 1` of `Q`, and let
`R = {x ∈ ℤ/Qℤ : x ≢ a_d (mod d) for every such d}` be the complete survivor
set. For a probability `μ` supported on `R`, define

\[
 c_\mu(d)=\max_{b\in\mathbb Z/d\mathbb Z}\mu\{x:x\equiv b\pmod d\},\qquad
 \chi(1)=1,\quad \chi(p^e)=2e+1,
 \qquad \kappa_Q(\mu)=\sum_{d\mid Q}\chi(d)c_\mu(d),
\]

with `χ` multiplicative. H73 asserted that for every `Q` and every such residue
assignment there exists such a probability with `κ_Q(μ) ≤ 138877/1000`.
The height-four instance proved in Evidence has an explicit survivor and forces
`κ_Q(μ) > 1621563/10000 > 138877/1000` for every survivor probability, including
correlated ones. One finite height refutes the arbitrary-exponent assertion.
H73 is therefore unavailable as a sufficient input; it was never an equivalent
restatement of #7.

**Γ73 — false**, preregistered at the same issue: for every
such `Q` and residue family, a probability `μ` on its complete survivor set `R`
satisfies

\[
 \Gamma_Q(\mu)=
 \max_{(b_d)_{d\mid Q}}\mathbb E_\mu
 \left[\left(\sum_{d\mid Q}\mathbf1_{x\equiv b_d\pmod d}\right)^2\right]
 \le\frac{138877}{1000}.
\]

The maximum is over **one joint choice** of residues: each `b_d ∈ ℤ/dℤ` is
chosen once for the whole square. Residues for different divisors need not be
mutually compatible. This candidate replaced the separate-cylinder
cost; it was not a consequence of H73's failure. A lower bound for `κ_Q` gives no lower
bound for `Γ_Q`. The conditional transfer and finite-height calibration below do not establish Γ73.
The stronger demand that this law always be uniform is false: the rectangular
family below has uniform `Γ>142.3789923` but admits a nonuniform law with
`Γ<134.121`. That rectangular example alone does not refute the existential target;
the star family does.

<a id="route"></a>
## Route

The joint-load invariant retains actual residue intersections. Its transfer
and the restricted noncoverage results are established below. The star-family
refutation identifies why the proposed universal head input fails. The
positive-part proof (US1)--(US12) nevertheless excludes all tail completions
of that precise head assignment, using a later supported prefix seed.
