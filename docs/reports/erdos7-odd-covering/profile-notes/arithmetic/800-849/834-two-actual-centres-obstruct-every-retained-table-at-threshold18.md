# 834. Two fixed actual centres obstruct every retained table at threshold 18

For the specified infinite pure-comb source C, phase-31 selected family and inherited cap budget, no nonzero admissible first-colour K8 table can make the raw-source hinge criterion positive at h = 18, even when the tail debit is set to zero. This extends the obstruction of [Report 832](832-one-actual-common-centre-blocks-every-threshold-for-the-fixed-retained-table.md) from one retained table to every nonnegative table in this fixed interface, at this one threshold.

Two fixed actual common centres suffice. Write H_A and H_C for their raw integrated hinges, M for raw mass, and L for the inherited lower budget. The exact certificate proves the uniform bound

$$
\frac{H_A(18;u)+H_C(18;u)}2
\ge 10L(u)+\frac1{25}M(u)
\qquad\text{for every admissible }u\ge0.
$$

Thus for every nonzero table at least one of A or C has hinge strictly larger than 10L. The two centres and their equal mixture are fixed independently of u; the centre that violates the comparison may depend on u. The statement does not say that each centre separately obstructs every table. These are ordinary mathematical arguments and exact rational certificate checks, without a Lean or unrestricted Erdős #7 claim.

## Fixed source and admissible tables

Use Q = (5,7,11,13,17,19,23), ternary leaves (4,7,2,5,8) modulo 9, and the infinite pure-comb source of Report 832. For q = 5 the three first-colour probabilities are (4/15,4/15,7/15); for q > 5 they are

$$
\left(\frac{q-1}{q(q-2)},1-\frac{q-1}{q(q-2)}\right).
$$

There are 5·3·2^6 = 960 leaf/colour cells. The selected K8 congruences of the phase-31 family force 711 of them to zero, leaving 249 variables u_i. A cell i = (l,s) has positive mass

$$
m_i=\prod_{q\in Q}\pi_q(s_q),
\qquad M(u)=\sum_i m_i u_i.
$$

The raw measure is the leaf/colour density u applied to this one common product source, as in Report 832. No extra leaf-weight factor is inserted.

The original retained domain allows weights w_l ≥ 0 with sum w_l = 1 and 0 ≤ u_l(s) ≤ w_l. Its nonzero rays are exactly the nonnegative cone on the 249 allowed cells. Indeed, for any nonzero such u, set

$$
a=\sum_l\max_s u_l(s)>0,\qquad
\widetilde u=u/a,\qquad
\widetilde w_l=\max_s u_l(s)/a.
$$

Then the rescaled pair is legal. Conversely every legal table lies in the cone. All quantities used below are positively homogeneous. Since every m_i is positive, the normalization M = 1 represents every nonzero ray and imposes no u or cap upper boxes. The zero table remains legal in the original bounded domain, so the zero-tail comparison has maximum zero there, rather than a negative maximum.

For each of the 384 inherited C cap blocks b, let

$$
F_b(u)=\max_r\sum_i f_{b,r,i}u_i,
\qquad
L(u)=M(u)-\sum_b\ell_b F_b(u).
$$

The nonnegative coefficients f and losses ℓ are exactly those of [Report 824](824-free45-phase20-has-a-live-cell-certificate-while-short-leaf-phases-obstruct-h16.md). All 9,902 original C epigraph rows are retained. This argument concerns this inherited L; replacing it with a stronger actual survivor estimate is a separate problem.

## Actual whole-centre queries

Each centre supplies one compatible prime-power phase at every depth, hence one actual joint CRT assignment for every numerical label, including the unit. All higher digits are zero. The three named centres are:

| Centre | Ternary leaf modulo 9 | Root modulo 5 | Roots at 7,11,13,17,19,23 |
|---|---:|---:|---|
| A | 5 | 0 | all 3 |
| B | 8 | 1 | all 3 |
| C | 2 | 0 | all 3 |

A and B are the two envelope witnesses already present in Report 832. C uses the remaining leaf 2 within the same ternary root as A. Each centre is global: it is never chosen separately for different source cells.

Let b_(a,i) be the actual raw hinge of centre a on cell i at threshold 18. Using the local laws from Report 832,

$$
b_{a,i}=\mathbb E_i N_a-18m_i
+\sum_{n=1}^{17}(18-n)\Pr_i(N_a=n).
$$

The full mean is retained separately from the low atoms. This identity is exact and does not truncate geometric heights. Therefore

$$
H_a(18;u)=\sum_i b_{a,i}u_i.
$$

Every H_a is a lower bound on the raw supremum over all actual layout phases. No optimization inside a source sum is used.

## A concrete table shows why the missing centre matters

There is a rational M = 1 table with 140 positive entries that satisfies all 9,902 cap rows and has positive gates for both A and B. It is stored in the certificate and obeys the legal leaf-envelope rescaling above. Its exact gate minimum lies strictly between 3/5000 and 7/10000. Decimal displays are:

| Quantity | Value |
|---|---:|
| 10L | 0.22382525384326374 |
| H_A(18) | 0.22316032161231160 |
| H_B(18) | 0.22316032160986685 |
| H_C(18) | 0.32961221732378443 |
| Minimum A/B gate | 0.00066493223095212 |
| C gate | −0.10578696348052066 |

The C gate is exactly less than −1/10. Thus positivity of the two-cut necessary relaxation does not imply positivity for actual all-layout hinges. The same table, same source and same head budget distinguish the observations: adding the C query reveals a constraint absent from the A/B pair.

## Uniform dual certificate

Introduce z_b ≥ 0 and a free real variable ε. The cap rows and the three centre gates are

$$
\sum_i f_{b,r,i}u_i-z_b\le0,
$$

$$
\varepsilon+10\sum_b\ell_bz_b
+\sum_i(b_{a,i}-10m_i)u_i\le0
\qquad(a=A,B,C),
$$

with u_i ≥ 0 and M = 1. This gives 634 variables and 9,905 inequalities. There are no artificial z or ε upper boxes.

The stored exact dual consists of 517 nonzero nonnegative cap multipliers α_(b,r), the centre weights

$$
(\beta_A,\beta_B,\beta_C)=\left(\frac12,0,\frac12\right),
$$

and a rational λ satisfying

$$
-\frac{44}{1000}<\lambda<-\frac{43}{1000}<-\frac1{25}.
$$

Its displayed value is approximately −0.04323104546800277. This is a certified upper bound; no claim of an exact optimum is needed. The certificate checks

$$
\sum_r\alpha_{b,r}\le10\ell_b
\qquad\text{for all 384 blocks},
$$

and

$$
\sum_{b,r}\alpha_{b,r}f_{b,r,i}
+\frac{b_{A,i}+b_{C,i}}2
+(\lambda-10)m_i\ge0
\qquad\text{for all 249 cells}.
$$

Multiply the latter inequalities by u_i and sum. Each cap response is at most F_b(u), and the cap multiplier budget gives

$$
10L(u)-\frac{H_A(18;u)+H_C(18;u)}2
\le\lambda M(u)<-\frac1{25}M(u)
$$

for every nonzero u. At u = 0 the non-strict margin inequality also holds. This proves the stated uniform bound. The proof uses the same u in its mass, cap responses and both actual hinges.

It follows that retuning arbitrary retained first-colour cell weights cannot repair this source/head/raw-hinge interface at h = 18. Tightening a valid upper estimate of the raw all-layout hinge, or removing a nonnegative tail debit, cannot cross this obstruction. Other thresholds, sources, selected heads, phases, deeper state descriptions and actual-survivor normalizations remain outside this certificate.

## Reproducible exact result

[arbitrary_profile_common_centres.py](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/arbitrary_profile_common_centres.py) rebuilds the original C cap rows from the pinned Report 824 engine and obtains each named centre law from the pinned Report 832 local-law engine. It checks the saved 832 mass, L, both selected complete means and A's threshold-18 hinge without evaluating the 960-centre tensor again.

The portable semantic matrix identity is `62d4ef8576a9eaafaf8f11af2f319dcc64c35f52c5a98c444379844b6d81153c`. It binds all variables, the three centres, every inequality and the mass equality, without embedding filesystem paths. [arbitrary_profile_common_centres_certificate.json](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/arbitrary_profile_common_centres_certificate.json) retains the sparse A/B table and uniform dual. [arbitrary_profile_common_centres.json](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/arbitrary_profile_common_centres.json) contains the deterministic checked result.

All CLI inputs and output are explicit. The consumer runs exact standard-library arithmetic, invokes no optimizer, and compares the complete deterministic result by default; `--write-result` explicitly writes it. The prepared large matrix, floating solver output and source-cell law table are not required inputs.

Independent reconstruction checked the A/B cell laws and original cap rows, all 249 added C cell laws, and unchanged prior matrix rows. Final independent verification checked all 384 cap budgets, all 249 structured cell inequalities, all 633 nonnegative columns and the free ε identity; fourteen material mutations were rejected. This is exact rational computational evidence for the stated ordinary proof, not Lean verification.
