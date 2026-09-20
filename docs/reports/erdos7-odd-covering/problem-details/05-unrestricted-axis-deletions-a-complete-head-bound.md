[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md) · [Next](06-block-saturation-and-the-actual-crossing-budget.md)

<a id="unrestricted-axis-deletions-a-complete-head-bound"></a>
### Unrestricted axis deletions: a complete head bound

The [variable-rectangle construction](../profile-notes/001-064/04-the-weighted-upper-quantile-lemma.md#unrestricted-axis-deletions-and-the-optimal-scalar-clipped-bound)
removes the preceding axis restrictions at the level of the supported
head bound. For every family of distinct nonunit moduli dividing
`315·11^H·13^J`, with arbitrary finite `H,J≥1`, it constructs one complete
survivor probability satisfying

    Gamma <= 42723250051/1147550665 < 37.230.

No restriction on the number of deleted rows, columns, point holes, or
empty old fibres is imposed. The full `{3,5,7}` part must still divide 315.

If `A,B,D` are the three complete old loads dominating the original axis
and cross-point activation counts, the number of remaining first-digit
cells is at least `S=[(11-A)_+(13-B)-D]_+`. This retains the actual
rectangular overlap. The clipped subprobability law has old row mass
`min(1,C·S_actual/120)` and density at most `C` relative to the uniform
ten-by-twelve reference law. Empty fibres receive zero mass.

At `C=40/31`, the exact marginal-profile bound for the low surviving mass
is `74101/97929`. Uniform higher digits and the distinct original-label
count give higher deleted mass at most `24119/319920`, leaving mass at
least `229510133/336875760`. The weighted old square and the minimum-load
deletion saving yield the displayed complete head bound.

The same supported law has a full increasing-convex comparator: take
the upper `229510133/434678400` quantile of `X·N11·N13`, where `X` is the
published old 315 comparator and the independent auxiliaries have
`Pr(Np=1)=(p-2)/(p-1)` and `Pr(Np=k)=p^(1-k)` for `k≥2`. Its boundary is
at 3 and its exact mean is `1263555626/229510133`. This comparison mean
does not assert equality with the actual maximum head-load mean. At
heights `H=J=1`, the same clipping constant gives the stronger square
bound `99014608/3186343 < 31.075`.
The same law also satisfies the sharper actual first-moment bound
`1242116000/229510133 < 5.413`, by retaining the old marginal cap and
the unit-load saving during deletion. This is distinct from the
comparison distribution’s larger mean.

The certificate also settles the scalar clipping parameter globally.
A linear-fractional transformation gives one linear program with 30
variables and 3458 constraints, using every old marginal hinge bound
and the sharp square bound. Exact primal-dual equality proves that
`C=40/31` minimizes the all-height square certificate over every `C≥1`
with a positive certified denominator. This is optimality within the
specified marginal-information relaxation, not optimality among actual
survivor laws. Further improvement requires information omitted by that
certificate, such as weighted old test energy.

Retaining the [common old shape and actual survivor count](../profile-notes/001-064/04-the-weighted-upper-quantile-lemma.md#retaining-the-common-old-shape-and-survivor-count)
sharpens the same construction at the same `C=40/31` to

    Gamma <= 2167128283/58962460 < 36.755,
    sup_test E_nu L <= 24790300/4595881 < 5.395.

All test and activation loads share one of the six canonical 45 shapes
and the same actual 315 survivor count. The verifier recomputes all
27,720 old layouts and 144 common branches. At fixed deletion count,
the original cofactor cylinders lower-bound deleted load energy; the
existing five-term area inequality then applies with that branch's
mean, square and hinge bounds. The actual local rectangle's Gram diagonal
further saves `(9G+19)/496` from the square numerator: its clipping
density and surviving axis counts obey simultaneous coefficient bounds,
and each complete old block load is at least one. The 1372 possible
nonempty rectangle count triples are checked exactly. The square maximum is at the first shape
with 81 survivors. The same law admits the upper `68561/129600` quantile
of `X·N11·N13` as a full increasing-convex comparator, with boundary 3
and mean `1264886009/229953594`. These stronger bounds preserve the
full `315·11^H·13^J` scope and do not assert a new tail continuation.

The [actual rectangle hinge profile](../profile-notes/001-064/05-the-actual-rectangle-gives-two-further-square-savings.md#actual-rectangle-hinge-bounds-on-the-same-law)
additionally bounds the complete test-load hinges on this same law at
all integer thresholds from 4 through 12. With the joint-cost refinement,

    Theta_nu(6) <= 321137/403528 < 4/5.

Convex concentration and the sum of the largest surviving-count cell
loads give a geometric upper envelope with the actual clipping
denominator. Nine rational duals are checked by 26,078,976 integer
inequalities; a point-load endpoint argument covers the full finite
domain, and empty fibres are checked separately. Their averages use
only the existing old-shape and survivor-count bounds. The actual
mixed-hole count is bounded by its old activation load, and the
higher-exponent contribution and normalization retain the same one
of 144 branches. The new `actual_rectangle_hinge_profile` certificate
field stores every dual and the full-height bounds at thresholds
4--12. The entries additionally use the joint-cost refinement below. The
first prime-17 query in (AP2) at threshold 6 therefore costs at most
`321137/4035280`. Adjacent-knot interpolation is a valid
pointwise upper bound; the resulting curve is not asserted to be a
probability comparator. This is an ordinary exact-arithmetic result,
not a new Lean theorem or a completed unrestricted-tail certificate.

These results remove the axis hypothesis for the finite head estimate.
They do not supply the unrestricted-tail stopping certificate needed
to remove that hypothesis for every old configuration. The particular
96-point configuration in (BT1)--(BT8) does have a complete unrestricted-tail
certificate with arbitrary axis and point exclusions.

The fixed-count labelled deletion refinement now closes the finite-head
threshold-six target. On the first 17-point old shape, the five mixed-seven
labels are grouped by their nonzero seven digit; each group deletes a union
of its labelled old-cylinder sets. An anchored partition recurrence over
these unions gives exact deleted-cost lower bounds. Of 4,760 old-45 layouts,
only 72 and 120 require the exact recurrence for the two sharpened costs;
the resulting numerator caps at survivor counts 80, 81 and 82 are
`(1986,1986,1992)` and `(728,728,732)`. Applying those caps to the existing
144 branch transfer gives

    Theta_nu(6) <= 26114497/32685768 < 4/5,

with unique worst branch `root1_same_other_column`, 79 survivors. This is
an ordinary exact finite-head calculation for arbitrary finite 11/13 heights,
not a Lean theorem or an unrestricted-tail conclusion.

Keeping each whole convex cost on a single old layout and its labelled
deletion configuration further improves seven of the nine hinge bounds.
The `joint_cost_hinge_refinement` certificate recomputes 32 normalized costs
on all 27,720 layouts and 144 shape/count branches, yielding the stronger
`Theta_nu(6)<=321137/403528`, with the same worst branch N=79. It uses the
existing cheap deletion lower bounds for the whole cost and retains the
exact three-branch partition caps above. All higher-load and normalization
terms stay on the same branch. The result proof and integer numerator
bounds are retained in the [whole-cost derivation](../profile-notes/001-064/05-the-actual-rectangle-gives-two-further-square-savings.md#whole-convex-costs-on-one-old-layout-and-deletion-configuration).

The [signed-conditioning obstruction](../profile-notes/001-064/05-the-actual-rectangle-gives-two-further-square-savings.md#actual-obstruction-for-uniform-conditioning-and-its-signed-bound)
gives a complementary boundary. An actual family containing all 47
nonunit divisors of 45045 has 6872 survivors and forces
`Γ≥88555/3436` for its uniformly conditioned reference law. Its signed
sufficient criterion cannot certify a value below `192443/6473`.
These are different statements: the second number is not an actual
moment lower bound, and neither excludes other supported laws.

<a id="a-continuation-criterion-for-an-arbitrary-correlated-head"></a>
### A continuation criterion for an arbitrary correlated head

Let \(Q\) be a finite odd head period and let \(\mu\) be one fixed
probability supported on its actual survivors. It need not be uniform or a
product law. Every original modulus is a distinct nonunit divisor of
\(Q\prod_p p^{H_p}\), with odd tail primes coprime to \(Q\); all physical
heights resolve the entire original family, including later classes.
A complete head test layout chooses one residue for every divisor of
\(Q\), including the unit divisor. With its load denoted by \(L\), define
\[
 \Theta_\mu(t)=\max_L\mathbb E_\mu(L-t)_+\quad(t\ge0),
 \qquad G\ge\Gamma_Q(\mu)=\max_L\mathbb E_\mu L^2.       \tag{AP1}
\]
The maximum is over finitely many layouts, all fixed before sampling the
head point. The bound \(\Theta_\mu(t)\le G/(4t)\) for \(t>0\) is valid, but
retaining the profile can give a stronger continuation than this relaxation.

At every tail prime \(p\), use the normalized kernel (US4) relative to the
uniform law on its actual pure-power survivors, with \(0<\delta_p<1\).
Assume
\[
 c_p=\frac{p-1}{(p-2)(1-\delta_p)}\le p.
\]
The full-history conditional cylinder cap is \(c_pp^{-e}\). This condition
makes the following unclipped auxiliary height law a probability:
\(\Pr(K_p\ge e)=c_pp^{-e}\) for \(e\ge1\). Choose these heights independently
of each other and of the head point. If \(c_p>p\), clipped tails and their
recomputed moments are needed; the formulas below cannot be retained as stated.
For the current tail prime \(q\), put
\[
 N_q=\prod_{\text{tail }p<q}(1+K_p),\qquad
 T_q=1+(q-2)\delta_q,\qquad d_q=(q-2)(1-\delta_q)>0.
\]
Then its actual assigned mixed-union probability is at most
\[
 b_q=\frac{\mathbb E_K[N_q\Theta_\mu(T_q/N_q)]}{d_q}.    \tag{AP2}
\]

**Original labels and the single missing unit cofactor.** Fix a head point
\(x\). Apply [Schroeder's conditional comparison](../../../../Library/Arith/schroeder2026noncoverage.md)
only to the old tail coordinates. Keep each original modulus
\(m\tau q^e\) as its own label, where \(m\mid Q\) and \(\tau\) is the old
tail cofactor, with weight \(w_e=(q-1)q^{-e}\). Its actual head-cylinder
indicator is a fixed nonnegative coefficient at \(x\). The conditional
tail caps hold for the entire earlier history including \(x\), and do
not depend on \(x\); the auxiliary comparison uniforms may therefore be
chosen independently of \(x\) when integrating against \(\mu\).

For each full tuple \((\tau,e)\), original-modulus distinctness gives at
most one residue for each head divisor \(m\). Complete that partial head
layout to \(L_{\tau,e}\), choosing all missing residues in advance,
independently of \(x\). Fix such completions also for missing tuples and
depths. After comparison, exactly \(N_q\) auxiliary tail tuples are active,
including the unit tuple; tuples beyond a physical height add only
nonnegative completion terms. Index their completed head layouts by \(j\).
Pure \(q\)-power classes were already removed. Thus the pair consisting of
the unit tail tuple and unit head modulus is absent from the mixed load,
and completion of every current depth, using \(\sum_{e\ge1}w_e=1\), gives
\[
 R_q^{\rm compared}\le
       \sum_{j=1}^{N_q}\sum_{e\ge1}w_eL_{j,e}(x)-1.     \tag{AP3}
\]
The subtraction is exactly \(1\), not \(N_q\): a nonunit tail cofactor
with unit head factor is a legitimate original mixed label. Completing
missing current depths is necessary to subtract the full \(1\).

For fixed auxiliary heights the weights \(w_e/N_q\), indexed by \((j,e)\),
sum to one. The head loads are bounded by the divisor count of \(Q\), so
countable Jensen gives
\[
 \begin{aligned}
 \mathbb E_\mu\left(\sum_{j,e}w_eL_{j,e}-T_q\right)_+
 &\le\sum_{j,e}\frac{w_e}{N_q}
                 \mathbb E_\mu(N_qL_{j,e}-T_q)_+\\
 &\le N_q\Theta_\mu(T_q/N_q).
 \end{aligned}                                        \tag{AP4}
\]
The pure-survivor cylinder bound gives
\(\alpha_q\le R_q/(q-2)\). Combining (AP4) with the actual kernel's
violation formula \(\mathbb E(\alpha_q-\delta_q)_+/(1-\delta_q)\)
proves (AP2). No projected-modulus distinctness or actual nestedness is used.

**A moment and survivor bound for the same actual law.** Let \(\nu_B\)
be the law after a finite tail prefix through \(B\), without intermediate
conditioning. Group any complete fine test layout by its full tail
exponent tuple. Each group is a complete head layout fixed before \(x\)
is sampled. Tail-only comparison with the square function bounds its
aligned load by \(\sum_{j=1}^{N_B}L_j(x)\), where
\(N_B=\prod_{\text{tail }p\le B}(1+K_p)\). Jensen yields
\[
 \mathbb E_\mu\left(\sum_jL_j\right)^2
 \le N_B\sum_j\mathbb E_\mu L_j^2\le G N_B^2.
\]
This is uniform over all fine layouts under the same law \(\nu_B\), hence
\[
 \Gamma(\nu_B)\le J_B:=G\mathbb E N_B^2
 =G\prod_{\text{tail }p\le B}
       \left(1+c_p\frac{3p-1}{(p-1)^2}\right).          \tag{AP5}
\]
This follows from comparison and Jensen, without a Gamma tensorization
identity for the correlated head law. If \(C_B=\sum_{\text{tail }q\le B}b_q<1\), the
actual event \(E_B\) avoiding every prefix class has mass
\(\lambda\ge1-C_B>0\). The head and pure-tail classes already have zero
violation probability. Since every complete load has \(L^2\ge1\),
conditioning once gives a supported law satisfying
\[
 \Gamma\bigl(\nu_B(\,\cdot\mid E_B)\bigr)
 \le1+\frac{J_B-1}{1-C_B}.                             \tag{AP6}
\]
For BBMST continuation, require all head primes to be at most \(B\), retain
the full physical heights, and count every prime, including absent primes
and \(2\), in \(k=\pi(B)\). If \(k\ge10\) and the right side of (AP6) is
at most \(k(\log k+\log\log k-3)^2\), (T1)--(T6) and BBMST Theorem 6.1
exclude coverage by the entire family. The supported law may be correlated
and may have a different head marginal after this single conditioning.

**An exact finite low-state identity.** Put
\(M=\Theta_\mu(0)=\max_L\mathbb E_\mu L\), using its exact value.
Because \(L\ge1\), one has \(\Theta_\mu(t)=M-t\) for \(0\le t\le1\);
also \(\Theta_\mu(t)\ge M-t\) for every \(t\ge0\).
For a positive integer-valued \(N\) of finite mean and \(T>1\), splitting
at \(N\ge T\) therefore gives
\[
 \mathbb E[N\Theta_\mu(T/N)]
 =M\mathbb E N-T+
   \sum_{1\le n<T}\Pr(N=n)
      \underbrace{\bigl[n\Theta_\mu(T/n)-Mn+T\bigr]}_{\ge0}.
                                                               \tag{AP7}
\]
The sum is finite. For (AP2),
\(\mathbb E N_q=\prod_{\text{tail }p<q}(1+c_p/(p-1))\).
Thus each finite-prefix charge requires only this mean, finitely many
low-state probabilities and finitely many head-profile values. With the
exact \(M\), certified upper profile values yield nonnegative upper
corrections, so upward mean and probability bounds give a safe directed
bound. An unknown or rounded upper bound for \(M\) cannot be substituted
while retaining either equality (AP7) or its asserted nonnegative
corrections: the negative occurrences of \(M\) must also be justified.

For the complete-star broad law, (US1)--(US3) and conditional comparison
give \(\Theta_\mu(t)\le\mathbb E(D_{\rm head}-t)_+\) and
\(G\le\mathbb E D_{\rm head}^2\). Independence of the head auxiliaries
and \(N_q\) then reduces (AP2) to the positive-part bound for
\(D_{\rm head}N_q\) already certified in (US7)--(US12). That application
is complete. For arbitrary head geometry, constructing a supported law
with a sufficiently small profile to satisfy (AP2), (AP5) and (AP6)
remains a separate obligation. The criterion alone supplies no such
universal law; a lower bound on Gamma alone does not refute its existence.
This is an ordinary continuation proof, not a new Lean theorem.
