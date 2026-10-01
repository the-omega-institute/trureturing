# 777. Four exact duals classify the reference height-flag envelopes

For the actual dictionary of
[774](774-fixed-single-axis-scales-fail-while-the-joint-envelope-passes.md)
at the reference outside primes $(11,13,17,19,23)$, the saturated geometric sufficient envelope of
[776](776-one-actual-dictionary-retains-a-positive-arbitrary23-height-reserve.md)
is strictly feasible for exactly two height-flag sets:

$$
\varnothing\quad\text{and}\quad\{23\}.
$$

Every one of the other30 flag sets has envelope cost strictly greater than mass for every nonzero common nonnegative old-row law. Four exact singleton duals suffice for this classification. Their scope is the stated conservative envelope, not existence of actual survivors, failure of all source constructions, or a covering counterexample. Unlike the positive theorem in776, the negative classification is restricted to the reference primes.

## 1. The same actual source and the same envelope

Keep the eleven core and55 singleton old phases in the pinned
[774 input](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_single_axis_obstruction_input.json).
Its SHA256 is
`3233f1c82a405ae6018bcad76b0274f14bce7f19a2bcf3bac741657452eec630`.
There are75 actual admissible rows, all with positive lower denominators $\ell_j(x)$. The query cap is

$$
Z_{d,J}(u)=\max_{a\bmod d}\sum_{x=a\pmod d}
\frac{u_x}{\prod_{j\in J}\ell_j(x)}.
$$

For a full-height flag set $F$, use $f_j=P_j/(P_j-1)$ when $j\in F$ and $f_j=1$ otherwise. The776 coefficient is

$$
\beta_F(d,J)=
\begin{cases}
\kappa(d),&J=\varnothing,\\
\bigl(\kappa(d)+1\bigr)f_j-1,&J=\{j\},\\
\bigl(\kappa(d)+1\bigr)\prod_{j\in J}f_j,&|J|\ge2.
\end{cases}
$$

Thus $C_F(u)=\sum_{d,J}\beta_F(d,J)Z_{d,J}(u)$. The full numerical-label accounting, pure higher-power terms, one-source construction and infinite geometric majorants are proved in776. There are382 possibly nonzero slots across all flags. A scenario with $r$ full axes uses $372+2r$ nonzero coefficients; the remaining zero budgets must also be respected by a dual.

All $u$ in this note refer to one common law over these75 actual rows. The phases, lower denominators and query cylinders are not chosen independently for different axes or different rows.

## 2. Four finite rational dual certificates

For one flag set $F$, choose nonnegative multipliers $\lambda_{d,J,a}$ satisfying

$$
\sum_{a\bmod d}\lambda_{d,J,a}\le\beta_F(d,J)
$$

for every numerical query slot. Define each actual row's load by

$$
L_F(x)=\sum_{d,J}
\frac{\lambda_{d,J,x\bmod d}}{\prod_{j\in J}\ell_j(x)}.
$$

If $L_F(x)\ge\eta_F$ on every row, then

$$
\begin{aligned}
C_F(u)
&\ge\sum_{d,J,a}\lambda_{d,J,a}
\sum_{x=a\pmod d}\frac{u_x}{\prod_{j\in J}\ell_j(x)}\\
&=\sum_xu_xL_F(x)
\ge\eta_F\sum_xu_x.
\end{aligned}
$$

This is a direct nonnegative weighted sum of cylinder inequalities, using one common $u$. It does not require numerical optimality or equality in any query maximum.

The
[dual literal](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_height_flag_duals_input.json)
contains the following four certificates. Every multiplier is an integer divided by $10^{10}$.

| Full singleton axis | Nonzero multipliers | Exact minimum row load $\eta_F$ | Minimizing row |
|---|---:|---|---:|
|11|439|$170752588300591/163296000000000$|307|
|13|439|$4193009390192663/4084080000000000$|242|
|17|440|$244211160455359/241920000000000$|244|
|19|440|$971999240425747/967680000000000$|244|

The bounds are respectively approximately1.045663019,1.026671708,1.009470736 and1.004463501. In particular, all four exceed $251/250$. Every certificate satisfies all382 exact slot budgets and all75 row inequalities. The minimizing row in each case is unique.

The literal SHA256 is
`138f004cd53b15a0e855ded9c36f3cd421bb753ca4fc48f4b44b80e0300df6fb`.
It pins both the unchanged774 source and the positive776 weight input. The exact budgets and row loads are retained, so verification does not depend on a solver's floating-point objective or feasibility tolerance.

## 3. Why four obstructions settle all32 flag scenarios

For fixed reference primes and this fixed dictionary,

$$
F\subseteq G\Longrightarrow
\beta_F(d,J)\le\beta_G(d,J)
\Longrightarrow C_F(u)\le C_G(u)
$$

for every common nonnegative $u$. The singleton coefficient increases by the nonnegative quantity $(\kappa(d)+1)(f_j-1)$; the multioutside coefficients are products of factors at least one. All query caps are nonnegative.

If $G$ contains any of11,13,17,19, choose that singleton $F$. Its dual gives

$$
C_G(u)\ge C_F(u)\ge\eta_F\sum_xu_x
>\frac{251}{250}\sum_xu_x.
$$

Exactly30 subsets contain one of those four axes. The only remaining flag sets are empty and $\{23\}$.

For those two,776 supplies the same common integer law of mass50001. Its $\{23\}$ cost ratio is

$$
\frac{35736603059510325866351}{35776201636903343616000}
<\frac{999}{1000},
$$

and the empty flag set costs no more. This completes the exact feasibility classification of this saturated envelope on this actual reference dictionary. The positive cases do not use an independently chosen law for each axis, and the negative cases hold for every possible common law.

## 4. Limits of the obstruction

The envelope replaces actual root membership by the conservative counts $\ell_j$ and pays separate cylinder maxima by a union bound. A dual obstruction to this envelope does not rule out sharper actual-root information, deletion-intersection credit, another source or another sufficient criterion. It does not give a covering configuration.

The coefficient formula sums complete geometric majorants for unbounded allowed heights. A strict lower bound for that saturated sufficient cost is not a claim that every finite truncation already has cost above mass, nor that an actual finite family attains the simultaneous worst-case charges. The positive776 result covers all finite heights because each actual finite deletion inventory is bounded by the majorant; this implication cannot be reversed to turn its failure into an actual covering theorem.

At larger ordered primes, the guaranteed denominators increase and the released geometric factors decrease. The resulting cost can shrink. Therefore the four negative certificates and the32-scenario classification above are statements at $(11,13,17,19,23)$ only. The positive fifth-axis certificate transports to larger primes by776's separate rowwise density argument.

The382 possible caps are a static sufficient-cost interface. Neither this classification nor a list of current cap values gives a closed transition boundary for arbitrary future fixed-phase deletions; see
[755](755-current-query-maxima-are-not-a-closed-continuation-boundary.md).
The all-dictionary source problem, further heights through stronger constructions, and unrestricted prime support remain unresolved by these certificates.

## 5. Exact reproduction

The standalone
[consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_height_flag_duals.py)
reconstructs the actual75 rows and all denominators from774, checks1528 exact multiplier budgets and300 exact row inequalities, and verifies coefficient domination for every excluded flag scenario. It also freshly recomputes the positive776 law's costs for the two feasible flags. The
[retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_height_flag_duals.json)
contains all budgets, row loads and the complete32-scenario classification.

A separate exact implementation uses integer row accumulators over $10^{10}\prod_j\ell_j(x)$, rather than summing the primary consumer's rational contributions. Every lower bound, row load, coefficient budget and minimizing row agrees. The minimal retained inputs preserve exactly the source, weights and multipliers of those independently checked literals. Explicit guards survive optimized Python, and ten malformed-certificate mutations are rejected. This is ordinary finite exact verification of the stated dual argument, not additional Lean verification or a solver-optimality claim.
