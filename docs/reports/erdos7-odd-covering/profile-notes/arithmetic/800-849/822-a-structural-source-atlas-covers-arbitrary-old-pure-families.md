# A structural source atlas covers arbitrary old pure families

For the fixed actual opposing-phase family, the restriction on the old pure-prime source is removed. Every finite choice of old pure originals, with arbitrary heights and phases, admits a positive continuation through the actual 29 stage and every finite prime tail strictly above 1600. The final distorted surviving mass of the process initialized from its assigned survivor law exceeds $1/2000$.

The new part covers all pure-5 originals with phase 2, 3 or 4. It uses a structural choice between two existing tables: the quarter table when at most one of the six other reference roots remains live, and the Report821 retained table when at least two remain live. Each entire source cell receives one fixed table and its own consistent normalization. Combining this atlas with [Report817](817-a-source-adaptive-atlas-covers-both-forbidden-reference-roots-at-five.md) and [Report819](819-absence-of-pure-five-gives-a-uniform-complete-continuation.md) exhausts the actual pure-source cases.

These are ordinary mathematical results with exact rational verification, not Lean results or unrestricted Erdős #7. The fixed mixed phases remain essential. Prime support is contained in

$$
\{3,5,7,11,13,17,19,23,29\}\cup P,\qquad P\subset\{p\text{ prime}:p>1600\}\text{ finite}.
$$

Primes 31 through 1600 remain excluded. The complete continuation uses [Report804](804-the-same23-label-source-admits-every-finite-prime-tail-above1600.md), including its inherited Rosser–Schoenfeld analytic prime-product bound.

## 1. The fixed phases and unrestricted pure-source choices

Use the literal anchors $0\bmod3$ and $1\bmod9$ and the 23 selected actual originals of [Report808](808-a-second-reference-colour-retains-an-actual-opposing-phase-continuation.md):

```text
(15,10),(21,7),(45,11),(33,22),(35,0),(39,13),
(63,49),(51,34),(57,19),(55,0),(105,70),(75,25),
(69,46),(65,0),(99,22),(77,0),(85,0),(117,13),
(95,0),(165,55),(91,0),(147,49),(225,175).
```

Each pair is (numerical modulus, actual phase). All originals have odd, nonunit, globally distinct numerical moduli. No selected original is rephased by source cell, table, or query.

The old prime support is $\{3\}\cup Q$, where $Q=(5,7,11,13,17,19,23)$. All remaining allowed head originals and higher ternary powers are charged by the complete inventory. The pure-$q$ originals for $q\in Q$ have arbitrary finite heights and actual phases, including presence or absence of the first label $q$. Their actual Haar survivor is normalized once to define $\lambda_q$. Higher pure ternary originals are included in the complete head loss.

This report removes the additional restrictions on those pure-source branches. It does not remove the displayed selected-phase conditions or admit the excluded intermediate primes.

## 2. A disjoint partition of the root-other source case

For $q\in Q$, put

$$
C_q=\frac{q-1}{q-2},\qquad c_q=\frac{C_q}{q},\qquad
\ell_q=\frac{q-2}{q^2-q-1}.
$$

At 5 use the categories $\{0\},\{1\},\{2,3,4\}$. When the actual pure-5 original removes 2, 3 or 4, [Report816](816-actual-pure-source-cells-and-a-finite-three-kernel-gap.md) places its law in the triangle $T$ with corners

$$
A=(1/5,4/15,8/15),\quad
B=(4/15,1/5,8/15),\quad
C=(4/15,4/15,7/15).
$$

At each of the six other primes, the observed categories are $\{0\}$ and nonzero. Report816 proves

$$
\pi_q(0)\in\{0\}\cup[\ell_q,c_q],\qquad \ell_q>0.
$$

The zero case occurs exactly when the actual pure-$q$ original removes root 0. Higher originals alone cannot erase an initially live first root. Every actual source therefore determines the unique set

$$
J=\{q\in\{7,11,13,17,19,23\}:\pi_q(0)>0\}.
$$

Its law belongs to the product cell

$$
D_J=T\times\prod_{q\in J}[\ell_q,c_q]\times\prod_{q\notin J}\{0\}.
$$

These 64 cells are pairwise disjoint, because zero is separated from every live interval by a positive gap. Their union contains every actual pure-5 root-other source. A cell has $3\cdot2^{|J|}$ distinct product vertices, so the union has

$$
\sum_J3\cdot2^{|J|}=3\cdot3^6=2187
$$

distinct vertices. The seven cells with $|J|\le1$ have $3+6\cdot6=39$ vertices. The remaining 57 cells have 2148. These geometric counts do not depend on numerical gate signs.

## 3. The assigned tables and their two normalizations

The assignment is fixed by the whole structural cell:

| source cell | fixed table | normalized survivor law | moment comparison |
| --- | --- | --- | --- |
| $|J|\le1$ | existing quarter table | $\lambda_w|_U/\lambda_w(U)$ | full-source fourth moment |
| $|J|\ge2$ | existing Report821 table | $\nu_u|_U/\nu_u(U)$ | queried-capacity retained fourth moment |

Here $U$ is the complete old survivor and $\nu_u\le\lambda_w$ is the retained submeasure. Once the actual source determines $J$, all its queries use the assigned table, law, and comparison. The two denominators are not combined at one source.

For the quarter branch, use exactly the [Report814](814-three-kernels-cover-all-source-vertices-but-miss-a-strict-interior-point.md) weights

$$
w=(1/4,1/4,1/6,1/6,1/6)
$$

on leaves $(4,7,2,5,8)$. All 210 K8-allowed entries retain their full leaf weight, and the 750 selected-cylinder-forbidden entries are zero. The retained table supplies the complete head floor

$$
\lambda_w(U)\ge\nu_u(U)\ge L_{\mathrm{full}}(\pi,u).
$$

The hinge and full fourth moment retain the full-source denominator $\lambda_w(U)$. With $r=1/2$, $v=1/4$, their h16 gate is

$$
G_{\mathrm{full}}=12L_{\mathrm{full}}-H_{16}(r,v)
-27K_Q(1+15r+216v)T_{1600}.
$$

The generic constant at 5 is still $C_5=4/3$. The complete head includes every residual numerical slot and higher ternary depth. The full moment factor $K_Q$ includes the actual pure-29 factor once.

For the retained branch, use exactly [Report821](821-a-queried-capacity-kernel-covers-the-live-root-other-source-cell.md)'s 135 positive rational entries and weight vector

$$
w=\frac1{10^8}(24248949,24248949,20974406,15263848,15263848).
$$

Its gate is the [Report820](820-queried-colour-capacities-sharpen-complete-head-and-moment-bounds.md) queried-capacity expression

$$
G_{\mathrm{ret}}=12L_{\mathrm{cap}}-H_{16}(r,v)
-27T_{29}T_{1600}K_{\mathrm{cap}},
$$

with the full-$\lambda_w$ hinge domination and retained-$\nu_u$ moment numerator, both divided by the same retained survivor mass $\nu_u(U)$ in the continuation estimate. The complete coefficients are

$$
T_{29}=\frac{120361}{74088},\qquad
T_{1600}=\frac{4301685063112470380207}{10^{30}}.
$$

No table entry, threshold, selected phase, or tail coefficient changes with the source point inside an assigned cell.

## 4. Dead queried colours disappear at every depth

The retained branch must respect the actual source's zero colours even for deeply queried coordinates. For a support $D$ and its depth-1 subset $S$, let $A_{l,D,\kappa}$ be the same-source average over unqueried coordinates. The queried-capacity envelope is

$$
F_{D,S,h}=\max_{\substack{\kappa\text{ live on all of }D\\\text{allowed root or leaf for }h}}
\left(\prod_{q\in S}\frac{\min(c_q,\pi_q(\kappa_q))}{c_q}\right)
A_{D,\kappa,h}.
$$

The live condition applies to **every** queried coordinate in $D$, including $D\setminus S$. A zero-probability colour supports no cylinder at any depth. Applying the zero factor only at depth 1 would leave spurious deep query terms. Unqueried coordinates are averaged against the same actual probabilities, including their zeros.

Each coordinate has the three complete types: unqueried, depth 1, and depth at least 2. The latter is summed by its full convergent series. With

$$
\begin{aligned}
B_{D,S}&=\prod_{q\in S}c_q\prod_{q\in D\setminus S}\frac{C_q}{q(q-1)},\\
W_{D,S}&=\prod_{q\in S}15c_q\prod_{q\in D\setminus S}C_q\left(A_4(q)-\frac{15}{q}\right),
\end{aligned}
$$

Report820's formulas give the complete head and moment. Each selected label is removed once from its exact type with coefficient $C_D/n$; all residual coefficients remain nonnegative. The higher ternary debit $B_{D,S}/2$ includes the empty nonternary support. The full moment uses ternary multipliers $1,15,216$. Thus all $3^7=2187$ nonternary depth types, arbitrary old heights, and the once-only pure-29 factor are retained.

The consumer includes a direct control with positive retained response only on a dead queried colour. Both its shallow and deep envelopes must be zero, while the same deep response at a live colour remains positive. This distinguishes the complete support rule from shallow clipping alone.

## 5. Every assigned cell has a strict positive gate

The exact evaluations of the fixed assigned tables give:

| assigned cells | vertices | exact-arithmetic minimum, decimal display | strict rational floor |
| --- | ---: | ---: | ---: |
| quarter, $|J|\le1$ | 39 | 0.24262508725035375… | $6/25$ |
| retained, $|J|\ge2$ | 2148 | 0.014229908681286006… | $7/500$ |

The quarter minimum is at $C$, with $π_7(0)=c_7$ and all five other reference probabilities zero. The retained minimum is at $C$, with $π_7(0)=c_7$, $π_{11}(0)=\ell_{11}$, and the other four reference probabilities zero. Complete rational values and every assigned vertex are retained in the result. All comparisons use exact fractions.

On each $D_J$, the zero/live pattern and the branches of $\min(c_q,\pi_q)$ are fixed. In a queried-capacity response, a local block occurs either in the shallow capacity factor, in the unqueried average, or as a constant deep factor. It never occurs twice. Every branch is affine in each whole local probability block; taking maxima makes the envelopes block-convex. The nonnegative head coefficients and moment coefficients make the retained gate block-concave, as proved in Report820.

The old quarter gate is also block-concave on its enclosing categorical domain, by the common-colour argument of [Report810](810-categorical-retained-kernels-give-a-finite-common-source-interface.md). Therefore each table's product-vertex lower bound extends throughout every cell assigned to it.

This is a structural atlas: all vertices of a given cell use the same table. It does not take a pointwise maximum of unrelated successful vertex certificates.

## 6. Positive distorted mass with the correct denominator

Within the chosen branch, let $\alpha$ denote its actual pre-normalization survivor mass: $\lambda_w(U)$ in the quarter branch and $\nu_u(U)$ in the retained branch. Let $L$ be that branch's complete floor and $D$ its nonnegative hinge-plus-tail debit. Positivity of $G=12L-D$ gives

$$
0<L\le\alpha,\qquad L\le M\le1.
$$

The final distorted surviving mass of the process initialized from that branch's normalized survivor law is at least

$$
\frac{12}{27}-\frac{D}{27\alpha}
\ge\frac{G}{27L}
\ge\frac{G}{27}.
$$

Both root-other branches consequently give

$$
\text{final distorted surviving mass}
>\frac{7}{13500}>\frac1{2000}.
$$

This is a bound for the distorted continuation measure, not a Haar-density bound or the surviving probability under the initial normalized law. Its positive supported mass on the finite CRT carrier supplies an uncovered integer.

## 7. All actual pure-source cases are exhausted

Because numerical moduli are distinct, the pure label 5 is either absent or has exactly one phase $f\in\{0,1,2,3,4\}$. The complete assignment is:

| actual pure-5 status | source theorem | positive continuation reserve |
| --- | --- | ---: |
| absent | Report819, with $C_5=20/19$ in every layer | $>29/100$ |
| phase 0 or 1 | Report817's certified source atlas | $>1/800$ |
| phase 2, 3 or 4 | the 64-cell structural atlas above | $>7/13500$ |

The first two rows already allow arbitrary actual pure inventories at the other observed primes. The third row exhausts their zero/live patterns by Section 2. Therefore these alternatives cover every actual old pure-source case for the fixed selected-phase family, and every assigned continuation has final distorted surviving mass greater than $1/2000$.

The sources and normalizations may differ between these disjoint cases. For a given actual family, one complete source is selected from its certified case and used for all its queries and subsequent stages. No argument requires one table or one denominator to work simultaneously across every case.

The remaining restrictions are the literal selected phases and the excluded prime range 31–1600. This closes the pure-source case split within that restricted theorem; it does not settle either remaining restriction or unrestricted Erdős #7.

## 8. Exact reproduction and dependencies

The [consumer](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/pure_source_structural_atlas.py), [certificate](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/pure_source_structural_atlas_certificate.json), and [result](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/pure_source_structural_atlas.json) use only the Python standard library. The consumer replays precisely the final assigned 39 quarter and 2148 retained vertices, their whole-cell assignment, and the strict positive bounds. It retains the dead-deep control and reconstructs the complete head, hinge, moment and rational prime-tail calculations.

Existing dependencies are the parent-directory [Report814 evaluator](../../../frontier/cover-geometry/refined-capped-source/three_kernel_atlas_counterexample.py) and [source certificate](../../../frontier/cover-geometry/refined-capped-source/three_kernel_atlas_counterexample_certificate.json), and the sibling [Report821 evaluator](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/root_other_capacity_kernel.py) and [135-entry certificate](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/root_other_capacity_kernel_certificate.json). The retained table is pinned by its exact certificate hash. The actual 25 phases and complete quarter table are checked from their literal source data.

From the artifact directory:

```sh
python3 -I -S -B pure_source_structural_atlas.py
python3 -I -S -B -O pure_source_structural_atlas.py
```

Normal execution recomputes the fixed certificate and compares the saved result without rewriting it. Regeneration requires `--write-result`; alternate paths use `--certificate`, `--result`, `--source-dir`, and `--kernel-dir`. By default the 814 dependencies are one directory above and the 821 dependencies are beside the consumer. Portable copies must retain that layout or supply the corresponding directories.

No solver, network access, or numerical optimizer status is needed. The consumer verifies the new root-other atlas and the arithmetic combining its reserve with the two earlier reserves. Report817 and Report819's source-case theorems, Report820's block-concavity proof, and Report804's analytic prime-product bound are mathematical premises; this numerical replay does not reprove them or claim Lean verification.
