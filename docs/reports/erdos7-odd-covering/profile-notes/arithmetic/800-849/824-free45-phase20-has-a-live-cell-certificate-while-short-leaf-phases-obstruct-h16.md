# Free45 phase20 has a live-cell certificate while short-leaf phases obstruct h16

Changing the actual modulus-45 phase from 11 to 20 admits one rational retained kernel with a positive complete h16 continuation gate throughout the root-other, fully live source cell. Its minimum over the cell's 192 product vertices is

$$
G_{20,*}=0.07211046526887831\ldots>\frac9{125}.
$$

The fixed-cell interpolation of [Report820](820-queried-colour-capacities-sharpen-complete-head-and-moment-bounds.md) extends this bound to every source in that cell. With the complete continuation of [Report804](804-the-same23-label-source-admits-every-finite-prime-tail-above1600.md), the final distorted surviving mass of the process initialized from the retained-survivor law exceeds $1/375$.

For actual phase 31, a rational weak-dual certificate instead gives

$$
G_{31,C}\le -0.18656447571285295\ldots<-\frac9{50}
$$

for the same h16 full-product-hinge/retained-moment comparison interface at source corner $C$. Every nonzero source-dependent dual multiplier concerns $C$ alone. This is an obstruction at that corner itself, not merely a conflict between three corners sharing one kernel. The comparison interface for phase 16 is equivalent by exchanging the two short ternary leaves, so the same obstruction applies there.

The positive claim has a specified live source cell. The negative claim excludes a positive certificate through this particular comparison at $C$; it does not show that an actual family covers, rule out sharper bounds or other constructions, or settle unrestricted Erdős #7. These are ordinary conditional mathematical results with exact rational checks, not new Lean results.

## 1. Literal originals and source domain

The actual originals are

    (3,0),(9,1),(15,10),(21,7),(45,phase),
    (33,22),(35,0),(39,13),(63,49),(51,34),(57,19),
    (55,0),(105,70),(75,25),(69,46),(65,0),(99,22),
    (77,0),(85,0),(117,13),(95,0),(165,55),(91,0),
    (147,49),(225,175).

Only `phase` changes. All other 24 originals, including the 3/9 anchors, are fixed. Thus there are 23 selected mixed numerical labels. The positive result uses `phase=20`; the negative comparison uses `phase=31`, with transport to `phase=16` specified below. In particular, changing an actual phase requires recomputing its selected-null cells; it is not a renaming of the old phase-11 table.

Let

$$
Q=(5,7,11,13,17,19,23),\quad
C_q=\frac{q-1}{q-2},\quad c_q=\frac{C_q}{q}.
$$

The generic cap $C_5=4/3$ is used throughout. The ternary leaves are $(4,7,2,5,8)$, with roots $(4,7)$ and $(2,5,8)$. At 5 the categories are $\{0\},\{1\},\{2,3,4\}$; at each other prime they are $\{0\}$ and its complement. There are $3\cdot2^6=192$ categorical patterns and 960 leaf-pattern entries.

The positive source cell is

$$
\mathcal D=\operatorname{conv}\{A,B,C\}
\times\prod_{q\in Q\setminus\{5\}}
\left[\frac{q-2}{q^2-q-1},\frac{q-1}{q(q-2)}\right],
$$

where

$$
A=(1/5,4/15,8/15),\quad
B=(4/15,1/5,8/15),\quad
C=(4/15,4/15,7/15).
$$

As in [Report816](816-actual-pure-source-cells-and-a-finite-three-kernel-gap.md), an actual pure-5 original removes root 2, 3 or 4, while reference root 0 stays live at 7, 11, 13, 17, 19 and 23. Finite higher pure phases and heights are arbitrary within this source contract. Every actual normalized local Haar survivor in this class lies in the stated outer cell. Exact finite realizability of an endpoint is not needed for the positive lower bound over the whole cell. Conversely, the negative endpoint comparison alone makes no claim about actual finite realizability.

The allowed prime support remains contained in $\{3,5,7,11,13,17,19,23,29\}$ and an arbitrary finite set of primes strictly above 1600. Primes 31 through 1600 remain excluded. The complete continuation and its inherited Rosser–Schoenfeld analytic premise are those of Report804. No assertion is made here for a dead reference category, a different pure-5 source cell, arbitrary mixed phases, or all free45 cases from [Report823](823-common-prefix-transport-reduces-the-free45-phase-to-three-cases.md).

## 2. One source and complete head, hinge and moment

Take a normalized ternary weight vector $w$ and a retained table $0\le u_l(s)\le w_l$. The selected-null cells have $u_l(s)=0$. Write $\nu_u\le\lambda_w$ for this genuine retained submeasure of the full product source, and let $U$ be the complete old survivor. The normalized source is always

$$
\alpha=\nu_u(U),\qquad \mu_u=\frac{\nu_u|_U}{\alpha}.
$$

The full product law dominates the nonnegative hinge numerator; the fourth moment uses the retained $\nu_u$ numerator. Both bounds use the same retained denominator $\alpha$. A full-product denominator is not substituted for the retained one.

For a support $D\subseteq Q$, shallow subset $S\subseteq D$, and ternary query type $h\in\{0,1,2\}$, let $F_{D,S,h}(\pi,u)$ be the maximum common-colour response. It averages over unqueried coordinates, multiplies a shallow queried colour by $\min(\pi_q,c_q)/c_q$, and takes respectively the all-leaf sum, a root sum, or a leaf value. Deep queried coordinates have depth at least 2. All live colour probabilities on this cell exceed $C_q/q^2$, so their deep multiplier is 1.

The full arithmetic coefficients are

$$
\begin{aligned}
B_{D,S}&=\prod_{q\in S}\frac{C_q}{q}
\prod_{q\in D\setminus S}\frac{C_q}{q(q-1)},\\
W_{D,S}&=\prod_{q\in S}\frac{15C_q}{q}
\prod_{q\in D\setminus S}C_q\left(a_4(q)-\frac{15}{q}\right),\\
a_4(q)&=\frac{15}{q-1}+\frac{50}{(q-1)^2}
 +\frac{60}{(q-1)^3}+\frac{24}{(q-1)^4}.
\end{aligned}
$$

The head loss coefficient is $B_{D,S}$ for nonpure residual types, minus every selected numerical-label deduction of that type, plus $B_{D,S}/2$ at ternary type 2. All these coefficients are nonnegative. In particular, the selected labels 75 and 225 are deducted in their depth-at-least-2 quinary type. The verifier reconstructs all $3^7=2187$ depth types before any equal-response aggregation.

Let $M=\nu_u(\Omega)$ and

$$
L=M-\sum_{D,S,h}\operatorname{loss}_{D,S,h}F_{D,S,h},\qquad
K=\sum_{D,S}W_{D,S}(F_{D,S,0}+15F_{D,S,1}+216F_{D,S,2}).
$$

Then $\alpha\ge L$. The factor 216 includes every ternary depth at least 2, since $9a_4(3)-45=216$. No height cutoff is imposed.

Set $r=\max(w_4+w_7,w_2+w_5+w_8)$ and $v=\max_l w_l$. The hinge $H_{16}(r,v)=H_0+H_r r+H_v v$ is reconstructed from the full mean and the exact finite correction below 16. Its coefficients are nonnegative. The once-only pure-29 multiplier and full tail are

$$
T_{29}=\frac{120361}{74088},\qquad
T_{1600}=\frac{4301685063112470380207}{10^{30}}.
$$

The latter includes every one of the 179 primes in $(1600,3000]$, with upward rational rounding and the complete analytic tail above 3000. The gate is

$$
G=12L-H_{16}(r,v)-27T_{29}T_{1600}K.
$$

## 3. Phase20: a fixed rational kernel over the whole live cell

The weight vector on leaves $(4,7,2,5,8)$ is

$$
w=\frac1{10^8}(22030622,22030623,13884439,21027158,21027158).
$$

The [literal certificate](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/free45_phase20_kernel_certificate.json) stores all 198 positive retained entries; omitted entries are zero. The actual phase-20 family forces 712 of the 960 entries to vanish, leaving 248 permissible entries. The consumer verifies every forced zero and every bound $0\le u_l(s)\le w_l$.

At the three quinary corners with the other six probabilities at their upper endpoints:

| Corner | $L$ | $K$ | $G$ |
|---|---:|---:|---:|
| $A$ | 0.04118424515677526… | 242887.5185906273… | 0.1514672628152493… |
| $B$ | 0.03455118462401511… | 241615.92105077044… | 0.07211046941469415… |
| $C$ | 0.034551184281382735… | 241615.9212321688… | 0.07211046526887831… |

The same rational table passes all 192 product vertices. The minimum is at $C$ with all other probabilities at their upper endpoints. The [exact result](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/free45_live_cell_and_comparison_obstruction.json) contains all rational evaluations and the full rational minimum; decimals above are displays.

On this fixed structural cell, every candidate queried response is affine in each local probability block: a block occurs either in a shallow capacity, in an unqueried average, or as a constant deep factor. It never occurs in both the capacity and average. The appropriate capacity branches remain fixed throughout $\mathcal D$. Maxima are block-convex, so the nonnegative head-loss and moment coefficients make $G$ block-concave. Repeated convex interpolation therefore gives

$$
G(\pi,u,w)\ge G_{20,*}>\frac9{125}\qquad(\pi\in\mathcal D).
$$

This does not interpolate across a zero/live change. Since $0<L\le\alpha$ and $L\le M\le1$, the complete continuation has distorted mass at least

$$
\frac{12}{27}-\frac{H_{16}(r,v)+27T_{29}T_{1600}K}{27\alpha}
\ge\frac{G}{27L}\ge\frac{G_{20,*}}{27}>\frac1{375}.
$$

This is a bound for the constructed distorted surviving law, not for original Haar density.

## 4. Phase31: an exact C-corner obstruction for this comparison

At $A,B,C$ with the other six probabilities at upper endpoints, the complete response coefficients compress to 576, 576 and 384 epigraph types. The compression groups responses that are exactly identical; all 2187 depth types and all 104,976 query menus are accounted for. For phase31 the literal selected-null count is 711, leaving 249 permissible retained entries.

The exact finite model has 1,793 variables, 43,446 inequalities, the equality $\sum_l w_l=1$, and objective maximizing $\epsilon$. Each point has its own epigraph variables, while $u,w,r,v,\epsilon$ are common. Its joint row is

$$
\epsilon+H_r r+H_v v+
\sum_b\left(12\operatorname{loss}_b+27T_{29}T_{1600}W_b(1,15,216)_{h_b}\right)z_b
-12M\le-H_0.
$$

All ordinary variables have bounds $[0,1]$; the actual epsilon box is $[-(H_0+H_r+H_v),12]$. Genuine response envelopes lie in $[0,1]$. The model's inequalities retain the complete head, full hinge and retained moment described above.

For any $Ax\le b$, $Ex=1$, and coordinate box $\ell_i\le x_i\le u_i$, take $y\ge0$ and a free scalar $\lambda$. Put

$$
\rho=c-A^\mathsf Ty-E^\mathsf T\lambda.
$$

Weak duality with an exact box correction gives

$$
c^\mathsf Tx\le b^\mathsf Ty+\lambda+
\sum_i\max(\rho_i\ell_i,\rho_i u_i).
$$

This follows by expanding $c^\mathsf Tx=y^\mathsf TAx+\lambda Ex+\rho^\mathsf Tx$ and bounding each term in its stated direction. It requires no floating feasibility or zero-residual assumption.

The [rational dual certificate](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/free45_phase31_dual_certificate.json) contains 480 positive row multipliers and one equality multiplier. The consumer reconstructs the exact matrix, recomputes all residuals, and applies the actual box to all variables including epsilon. There are 638 nonzero residual coordinates; their total box correction is only

$$
7.167815747631477\ldots\times10^{-11}.
$$

The resulting rational upper bound is strictly below $-9/50$. The three joint-row multipliers at zero-based row indices 16899, 33542 and 43445 are exactly $(0,0,1)$. Every other nonzero source-dependent multiplier is also from corner $C$. Thus deleting the $A$ and $B$ constraints preserves this certificate: no retained table, weight vector or source-dependent choice of those parameters can give a positive gate through this same comparison at $C$.

The artificial lower epsilon box does not weaken that obstruction: any positive gate would give a feasible positive epsilon within the box. More generally, gates below the lower box endpoint already lie below the displayed upper bound, while the remaining gates are covered by the certificate. The consumer retains the complete box correction rather than silently treating a nearly feasible numerical dual as exact.

## 5. Why phase16 inherits the comparison obstruction

Exchange short leaves 4 and 7. The selected categorical null unions for actual phase31 and phase16 transform into each other under this exchange. Four fixed higher cylinders are already contained in fixed lower ones:

$$
(63,49)\subseteq(21,7),\quad
(99,22)\subseteq(33,22),\quad
(117,13)\subseteq(39,13),\quad
(225,175)\subseteq(15,10).
$$

After removing these redundant null constraints, the base union is invariant under the short-leaf swap, and the modulus-45 null cylinder moves from ternary leaf 4 to leaf 7 while preserving its quinary root 1. The consumer checks every one of the 960 leaf-pattern nullities.

Transport $w_4\leftrightarrow w_7$ and $u_4(s)\leftrightarrow u_7(s)$. Root and all-leaf sums, $r,v$, numerical-label deductions, moment coefficients and the tail are unchanged; individual short-leaf epigraph menus are permuted. Consequently the complete comparison interface, including its C-corner optimum bound, is equivalent.

This is not a common prefix-tree transport of the literal actual family. At phase31 the fixed labels 45 and 63 share their ternary depth-2 prefix, whereas at phase16 they do not. A common tree automorphism preserves that relation. The two actual families remain distinct even though this retained-null comparison has the same obstruction.

## 6. Reproduction and remaining boundary

The [standalone consumer](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/free45_live_cell_and_comparison_obstruction.py) uses only the Python standard library and the two delivered rational certificates. It reconstructs the literal phase20 table, complete depth inventory, full hinge, once-only29 factor and full804 tail; evaluates all 192 fixed live vertices; reconstructs the exact phase31 matrix and weak-dual bound; and checks the phase31-to16 null-union transport. It needs neither a solver nor saved floating LP output.

From the artifact directory:

```sh
python3 -I -S -B free45_live_cell_and_comparison_obstruction.py
```

Normal execution checks the saved mathematical result without rewriting it. To create a new result at a new path, use `--write-result --result <new-path>`; the writer refuses to replace an existing result. The options `--certificate`, `--dual` and `--result` permit explicit paths.

The consumer's normal replay performs 96,826 checks. Independent mathematical review is recorded separately by the repository integration owner; this consumer's replay is not by itself an independent review or a Lean proof.

The remaining work is sharply separated: phase20 still needs treatment of other structural pure-source cells before any all-pure claim; phase31 and16 need a stronger comparison or a different construction at their obstructed source. An atlas can select different kernels away from $C$, but source-adaptive kernel selection alone cannot overcome the proved C-corner bound for this unchanged interface. None of these statements enlarges the allowed prime support or selected-phase contract.
