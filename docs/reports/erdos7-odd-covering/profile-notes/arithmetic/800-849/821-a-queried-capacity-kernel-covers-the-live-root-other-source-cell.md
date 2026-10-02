# A queried-capacity kernel covers the live root-other source cell

One rational retained kernel has a positive complete h16 continuation gate throughout the following source domain: an actual pure-5 original removes root 2, 3 or 4, and reference root 0 remains live at each of 7, 11, 13, 17, 19 and 23. The 23 actual selected mixed phases of [Report808](808-a-second-reference-colour-retains-an-actual-opposing-phase-continuation.md) remain fixed; all other finite pure phases and heights in this source class are allowed.

The exact minimum over the 192 vertices of the enclosing source cell is

$$
G_* = 0.03667044175855793\ldots>\frac9{250}.
$$

The fixed-cell block-concavity of [Report820](820-queried-colour-capacities-sharpen-complete-head-and-moment-bounds.md) extends this bound to the full continuous cell. With the unchanged complete [Report804](804-the-same23-label-source-admits-every-finite-prime-tail-above1600.md) continuation, the final distorted surviving mass of the process initialized from the retained-survivor law exceeds $1/750$.

This is ordinary mathematics with exact rational verification, not a Lean result or unrestricted Erdős #7. The result retains the fixed selected phases and prime support

$$
\{3,5,7,11,13,17,19,23,29\}\cup P,\qquad P\subset\{p\text{ prime}:p>1600\}\text{ finite}.
$$

Primes 31 through 1600 are excluded. This report does not include a deleted reference root at any of the six other observed primes, or absence of pure 5.

## 1. The actual source cell

Put $Q=(5,7,11,13,17,19,23)$, $C_q=(q-1)/(q-2)$, $c_q=C_q/q$, and $\ell_q=(q-2)/(q^2-q-1)$. At 5, the categories are $\{0\},\{1\},\{2,3,4\}$, with the triangle

$$
\begin{aligned}
A&=(1/5,4/15,8/15),\\
B&=(4/15,1/5,8/15),\\
C&=(4/15,4/15,7/15).
\end{aligned}
$$

At every other $q\in Q$, use the binary categories $\{0\}$ and nonzero, with $\pi_q(0)\in[\ell_q,c_q]$. Thus the full domain is

$$
\mathcal D=\operatorname{conv}\{A,B,C\}\times\prod_{q\in Q\setminus\{5\}}[\ell_q,c_q].
$$

It has $3\cdot2^6=192$ product vertices. [Report816](816-actual-pure-source-cells-and-a-finite-three-kernel-gap.md) proves that every normalized Haar law on an actual finite pure survivor in the stated class lies in this domain. At the six other primes, the pure label $q$ may be absent or may delete a nonzero root. Higher pure labels may have arbitrary fixed phases, subject to one original per numerical modulus. The endpoint description is a closed outer domain; exact finite realization of each endpoint is unnecessary for a lower bound throughout it.

The literal 25 anchors and selected originals are inherited from Report808, including $0\bmod3$, $1\bmod9$, and the opposing phase $11\bmod45$. Every selected cylinder is null for the same retained table. The complete head inventory charges all remaining allowed numerical labels and all ternary heights.

## 2. One source for the mass, hinge and moment

Let $w$ be a normalized law on ternary leaves $(4,7,2,5,8)$ and let $0\le u_l(s)\le w_l$ be a retained table on the 192 categorical patterns. It defines a genuine submeasure $\nu_u\le\lambda_w$. If $U$ is the complete old survivor, put

$$
\alpha=\nu_u(U),\qquad \mu_u=\frac{\nu_u|_U}{\alpha}.
$$

The positive gate below supplies $\alpha>0$. As in [Report815](815-retained-source-moments-have-a-three-point-common-kernel-obstruction.md), the hinge is dominated by the full product law $\lambda_w$, while the fourth moment uses the retained $\nu_u$ numerator. Both resulting estimates have the same retained-survivor denominator $\alpha$.

For a nonternary support $D$ and a subset $S\subseteq D$ marking depth exactly 1, Report820 defines $F_{D,S,h}$ by averaging unqueried coordinates against the same $\pi$ and maximizing one common queried-colour tuple. Each queried coordinate in $S$ contributes

$$
\rho_q(\kappa_q)=\frac{\min(c_q,\pi_q(\kappa_q))}{c_q}.
$$

The ternary type $h=0,1,2$ sums all leaves, one actual root, or one leaf respectively. Coordinates in $D\setminus S$ have arbitrary depth at least 2. On this actual-source cell every live colour exceeds $C_q/q^2$, so no deeper probability breakpoint is omitted.

The complete coefficients are

$$
\begin{aligned}
B_{D,S}&=\prod_{q\in S}c_q\prod_{q\in D\setminus S}\frac{C_q}{q(q-1)},\\
W_{D,S}&=\prod_{q\in S}15c_q\prod_{q\in D\setminus S}C_q\left(A_4(q)-\frac{15}{q}\right),\\
A_4(q)&=15t+50t^2+60t^3+24t^4,\qquad t=\frac1{q-1}.
\end{aligned}
$$

Each selected numerical label $3^h n$ is removed once from its exact $(D,S,h)$ inventory, with coefficient $C_D/n$. In particular, the selected 75 and 225 labels belong to the deep-5 type. Since the retained table is null on their actual cylinders, this removes already-null labels from the inventory. All residual coefficients remain nonnegative.

Let $\operatorname{loss}_{D,S,h}$ denote $B_{D,S}$ on the allowed shallow inventory, minus those selected coefficients, with $B_{D,S}/2$ additionally included for $h=2$. The allowed shallow supports have $|D|\ge2$ for $h=0$, and $D\ne\varnothing$ for $h=1,2$. The added half term includes $D=\varnothing$ and all higher pure ternary labels. Then

$$
\begin{aligned}
L(\pi,u)&=M(\pi,u)-\sum_{D,S,h}\operatorname{loss}_{D,S,h}F_{D,S,h},\\
K(\pi,u)&=\sum_{D,S}W_{D,S}\left(F_{D,S,0}+15F_{D,S,1}+216F_{D,S,2}\right).
\end{aligned}
$$

These are the complete all-height sums, with $3^7=2187$ nonternary depth types. The head bound gives $\alpha\ge L$. The moment includes every ordered four-query maximum-depth class; incompatible tuples contribute zero. Pure nonternary originals already define the actual $\lambda_q$ and are not charged again in the head.

At h16, write

$$
\begin{aligned}
r&=\max(w_4+w_7,w_2+w_5+w_8),\qquad v=\max_l w_l,\\
G(\pi,u,w)&=12L-H_{16}(r,v)-27T_{29}T_{1600}K,\\
T_{29}&=\frac{120361}{74088},\qquad
T_{1600}=\frac{4301685063112470380207}{10^{30}}.
\end{aligned}
$$

The actual pure-29 factor occurs once. The full hinge and tail are reconstructed exactly by the verifier.

## 3. The rational table and vertex certificate

The common weight vector is

$$
w=\frac1{10^8}(24248949,24248949,20974406,15263848,15263848).
$$

The [certificate](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/root_other_capacity_kernel_certificate.json) stores all 135 positive rational retained entries. Four equal their full leaf weight; 131 are strictly smaller. Every omitted entry is zero. The verifier checks $0\le u_l(s)\le w_l$, weight normalization, and all 750 selected-cylinder nullities among the 960 possible leaf-pattern entries.

At the three quinary corners, with the other six reference probabilities at their upper endpoints, the exact rational evaluations have these decimal displays:

| corner | $L$ | $K$ | $G$ |
| --- | ---: | ---: | ---: |
| $A$ | 0.041710948778887987… | 269344.6613928538… | 0.14208889074050518… |
| $B$ | 0.03290447523547694… | 267970.7747635251… | 0.03667044175855793… |
| $C$ | 0.03290472750087155… | 267986.7681776144… | 0.0366704512056966… |

The same table passes **all 192 product vertices**, including every combination of the six lower and upper live endpoints. The smallest gate is at $B$ with all six upper endpoints. Its full rational value and every vertex evaluation are stored in the [result](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/root_other_capacity_kernel.json). Every comparison with $9/250$ uses exact fractions; the decimals are displays only.

A source-adaptive change of table between these vertices is not used. At every source and for every query in this cell, the table and weight vector above remain the same.

## 4. Extension to the whole cell and full tail

On $\mathcal D$, the quinary singleton probabilities and the six binary reference probabilities stay on the affine branch of $\min(c_q,\pi_q)$. Each other-colour probability stays above its cap. The zero/live pattern is fixed.

For one candidate response in $F_{D,S,h}$, a local block appears either in its shallow queried capacity, in its unqueried-coordinate average, or as a constant deep factor. It never appears in both the capacity and the average. Every response is affine in each entire local probability block. Its maximum is block-convex; the nonnegative residual losses make $L$ block-concave, and the positive moment coefficients make $K$ block-convex. Thus $G$ is block-concave on $\mathcal D$.

Repeated convex interpolation in the seven local blocks gives

$$
G(\pi,u,w)\ge G_*>\frac9{250}\qquad(\pi\in\mathcal D).
$$

This argument relies on the stated structural cell. It makes no convexity claim across a zero/live change or an arbitrary probability breakpoint.

The hinge and moment debits are nonnegative, so $G>0$ implies $0<L\le\alpha$. Also $L\le M\le1$. Report804's complete allowed tail gives the final lower bound

$$
\begin{aligned}
\frac{12}{27}-\frac{H_{16}(r,v)+27T_{29}T_{1600}K}{27\alpha}
&\ge\frac{G}{27L}\\
&\ge\frac{G_*}{27}\\
&>\frac1{750}.
\end{aligned}
$$

The result therefore includes arbitrary finite pure heights, the actual pure-29 stage, and every allowed finite prime tail above 1600. It retains all other source and selected-phase conditions stated at the start.

## 5. Finite matrix semantics

The certificate can be represented by a finite LP with one common $u,w$. The three corners $A,B,C$ at the six upper endpoints admit an exact compression of the 2187 depth types. At those points the six other-prime shallow capacity multipliers all equal 1, so their depth-1/deep distinctions have identical response envelopes and their coefficients can be summed.

At $A$, shallow quinary colour 0 has multiplier $3/4$; at $B$, shallow colour 1 has multiplier $3/4$; all other multipliers are 1. Hence $A$ and $B$ each use 576 ternary epigraphs, and $C$ uses 384. Together with five weights, two caps $r,v$, one common gate variable, and 210 non-forced retained entries, this gives 1754 variables. The matrix has 40757 inequalities, one weight-normalization equality, and 365710 nonzero inequality coefficients. All moment-only epigraph classes remain present even when their head loss is zero.

Every epigraph bounds its exact linear common-colour response. The joint row at each source is

$$
\epsilon+H_r r+H_v v+
\sum_b\left(12\operatorname{loss}_b+27T_{29}T_{1600}W_b(1,15,216)_{h_b}\right)z_b
-12M\le-H_0.
$$

The three rows share one $u,w,r,v,\epsilon$ and use their own source envelopes. Exact reconstruction from all 2187 types verifies these matrix coefficients and their directions. The delivered positivity certificate is verified directly from its rational table and the complete 192 vertices; no optimizer, numerical feasibility tolerance, or claim of optimality is needed for reproduction.

## 6. Reproduction

The [consumer](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/root_other_capacity_kernel.py) uses only the Python standard library. It imports the existing parent-directory [Report814 evaluator](../../../frontier/cover-geometry/refined-capped-source/three_kernel_atlas_counterexample.py) for the literal source checks, full hinge, and exact tail, and reads that evaluator's [source certificate](../../../frontier/cover-geometry/refined-capped-source/three_kernel_atlas_counterexample_certificate.json). The queried-capacity head and moment are computed directly from their full depth-type inventories.

From the artifact directory:

```sh
python3 -I -S -B root_other_capacity_kernel.py
python3 -I -S -B -O root_other_capacity_kernel.py
```

Normal execution recomputes all 192 exact evaluations and compares the saved result without rewriting it. Regeneration requires `--write-result`; alternative paths use `--certificate`, `--result`, and `--source-dir`. The source directory defaults to the consumer's parent. A portable copy must retain both existing Report814 dependencies there, or explicitly supply their directory.

No solver installation, network request, or floating optimization result is used by this consumer. Its successful replay certifies the specified source cell and comparison, with the fixed-phase and prime-support limits above.
