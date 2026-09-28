# Complete-query closure retains slot disagreement and weighted row tests

[Report731](731-selected-query-moments-do-not-force-five-direction-carving-positivity.md) separates bounds on selected formal query fields from the actual complete-query hypothesis. Two exact interfaces recover parts of the missing structure: independently recombining globally fixed numerical-divisor slots gives a disagreement correction, while weighted residue histograms give an exact variational characterization of the entire query family.

Both require actual residue incidence on one source. They do not reject every possible fine realization of the five-block formal example, prove five-prime positivity, or settle unrestricted covering. The identities use elementary finite probability and convex duality together with existing repository interfaces; they are not new Lean declarations or general probability novelty claims.

## One actual source and the entire numerical dictionary

Fix a finite period $M$, a source $E\subseteq\mathbb Z/M\mathbb Z$, and one probability $\mu$ on $E$. Let $\mathcal D$ be a finite set of distinct nonunit divisors of $M$. Each complete query chooses one globally fixed phase $a_d\bmod d$ at every numerical label:

$$
 L_a(x)=1+\sum_{d\in\mathcal D}\mathbf1_{\{x\equiv a_d\pmod d\}},
 \qquad
 \Gamma_3(\mu)=\max_a\mathbb E_\mu L_a^3.
 \tag{QC1}
$$

These are test phases; changing a query does not change the actual original congruence family or its survivor source. In the shallow23 application, $\{1\}\cup\mathcal D$ is the complete divisor inventory of $315\cdot11\cdot13\cdot17\cdot19\cdot23$, with 384 slots. The known bound is

$$
 \Gamma_3(\mu)\le G_3=\frac{906617738995}{159166336}.
 \tag{QC2}
$$

All phase choices in the following constructions are made before the source point is sampled.

## Independent slot recombination has an exact cubic correction

Choose actual complete queries $a^1,\ldots,a^k$. At each nonunit label $d$, independently select an index with probabilities $\lambda_{d,i}$. These probabilities may depend on the label but not on $x$. Write

$$
 b_{i,d}(x)=\mathbf1_{\{x\equiv a^i_d\pmod d\}},\qquad
 p_d(x)=\sum_i\lambda_{d,i}b_{i,d}(x),\qquad
 m(x)=1+\sum_d p_d(x).
 \tag{QC3}
$$

Every realized selection is a legal complete query with fixed phases. Conditional on $x$, its slot indicators are independent Bernoulli variables because the **artificial phase selections** are independent; the source coordinates need not be independent. Centering those indicators gives

$$
 \mathbb E_{\rm hybrid}L_{\rm hybrid}(x)^3
 =m(x)^3+\sum_d p_d(x)(1-p_d(x))(3m(x)+1-2p_d(x)).
 \tag{QC4}
$$

Indeed the centered second and third moments are $p_d(1-p_d)$ and $p_d(1-p_d)(1-2p_d)$; mixed terms with a singleton centered factor vanish. The correction is nonnegative. Integrating against the same source yields

$$
 \mathbb E_\mu\left[m^3+\sum_d p_d(1-p_d)(3m+1-2p_d)\right]\le\Gamma_3(\mu).
 \tag{QC5}
$$

If a claimed upper bound is violated, at least one literal hybrid query violates it. Conditional expectation can select such a fixed query one slot at a time when the necessary integrated moments can be computed. This is distinct from choosing a different maximizing phase at each source point.

For two equally selected parent queries $A,B$, let

$$
 m=(L_A+L_B)/2,\qquad
 \Delta(x)=\sum_d|b_{A,d}(x)-b_{B,d}(x)|.
$$

Then QC4 becomes

$$
 \mathbb E_{\rm hybrid}L_{\rm hybrid}^3=m^3+\frac34m\Delta,
 \qquad
 \mathbb E_\mu[m\Delta]\le\frac43\left(\Gamma_3(\mu)-\mathbb E_\mu m^3\right).
 \tag{QC6}
$$

The parent totals do not determine $\Delta$. At the actual residue $x=1$, use numerical labels $3,5$ and parent phases $(1,0)$ and $(0,1)$. Both loads are 2. Independent recombination has loads $1,2,2,3$, whose mean cube is 11; repeating the first parent has mean cube 8. The coherent fixed hybrid $(1,1)$ has cube 27.

Independent recombination need not increase the average parent cube:

$$
 \mathbb E_{\rm hybrid}L_{\rm hybrid}^3-\frac{L_A^3+L_B^3}{2}
 =\frac34m\left(\Delta-(L_A-L_B)^2\right).
 \tag{QC7}
$$

In particular, equal parent loads with nonzero slot disagreement have an extra cost. If both parents saturate the same cubic ceiling and have equal loads almost surely, QC6 forces their slot indicators to agree almost surely.

The bound $\Delta\ge|L_A-L_B|$ produces an aggregate-only necessary condition. Exact evaluation of this weaker condition for all 465 pairs in the rational five-atom table of Report731 gives a maximum

$$
 \frac{13741299654236397}{2500000000000}<G_3.
$$

Thus that projection does not reject the table. Integer incidence and full-query realization are still absent; passing the projection is not a feasibility certificate.

## Selected hybrids and the full query family differ

The maximum of the hybrid expectation over all slot probability simplices occurs at a fixed phase selection, since the expectation is multilinear in those probabilities. Therefore testing every mixture over selected alternatives is equivalent to testing their Cartesian recombination closure. That closure equals the entire phase dictionary only when every allowed residue alternative is present at every slot.

There is an actual selected-family example of this distinction. On the singleton old residue 0, give every selected query the same phases: 0 in sixteen nonunit divisor slots, 1 in all other slots. Every selected query and every hybrid has load 17. The full 384-slot dictionary also permits phase 0 everywhere, with load 384. Hence selected-hybrid cubes are $4913<G_3$, but the full-source cubic condition fails. This realizes the selected integer symbols of the seven-direction comparison while explicitly violating its omitted hypothesis.

Another limitation follows from the [existing full convex comparison](../../001-064/02-survivor-weighted-full-convex-comparison.md). If the selected hit sets form a chain under inclusion at each source point, choosing one whole parent with common weights $\lambda_i$ gives comonotone slot indicators with the same marginals as independent recombination. The existing Bernoulli rearrangement bounds every convex cost of the independent sum by the whole-parent mixture. Thus these common-weight hybrid tests add no constraint in that nested case. Slot-dependent weights are not covered by this comparison.

An abstract integer load table can be represented by nested artificial prefix slots. Such a representation need not consist of actual residue cylinders: alternatives at one true modulus are equal or disjoint, and different moduli have CRT compatibility requirements. Slot labels must retain those relations.

## Weighted row tests characterize the complete cubic maximum exactly

For a nonnegative function $t:E\to\mathbb R$, include the unit label and put

$$
 R_\mu(t^2)=\sum_{d\in\{1\}\cup\mathcal D}
       \max_{a\bmod d}\sum_{\substack{x\in E\\x\equiv a\pmod d}}\mu(x)t(x)^2.
$$

The weighted linear slot-max identity is already used in [Report584](../550-599/584-weighted-query-costs-retain-the-actual-damaged-branch.md). Applying it to

$$
 z^3-(3t^2z-2t^3)=(z-t)^2(z+2t)\ge0
$$

gives the exact characterization

$$
 \boxed{\Gamma_3(\mu)=\sup_{t\ge0}
       \left[3R_\mu(t^2)-2\mathbb E_\mu t^3\right].}
 \tag{QC8}
$$

For any $t$, the maximizing weighted histogram at each numerical divisor defines one complete query $B$. The scalar inequality bounds its score by $\mathbb EL_B^3\le\Gamma_3$. Conversely, choose a maximizing complete query $A$ and set $t=L_A$. The weighted maxima are at least the weighted value of $A$, so the score is at least $\Gamma_3$. A maximizing $t$ can therefore be taken to be an actual integer query load. This exact characterization is not a low-cost optimization guarantee.

Starting from an actual query $A$, choose the phase of each divisor to maximize its cylinder mass under the same weight $\mu L_A^2$. The resulting fixed query $B$ satisfies

$$
 \mathbb EL_B^3\ge3R_\mu(L_A^2)-2\mathbb EL_A^3\ge\mathbb EL_A^3.
 \tag{QC9}
$$

This supplies a checkable improvement or separating witness, extending the whole-phase replacement discipline of [Report23](../../001-064/23-actual-maximizing-tests-constrain-the-killed-pair-matrix.md). It is not a global solver: on the uniform eight units modulo 15, phases $(a_1,a_3,a_5,a_{15})=(0,1,2,1)$ are a fixed point under smallest-phase tie breaking, with cube $81/8$, while the exact maximum is $99/8$.

## Actual source concentration and CRT collision constraints

For an event $S\subseteq E$ of positive mass $s$, define

$$
 A_\mu(S)=\sum_{d\in\{1\}\cup\mathcal D}\max_{a\bmod d}\mu(S\cap[a]_d).
$$

One query attains all these weighted first-moment maxima simultaneously. Jensen on $S$, and the mandatory unit outside $S$, imply

$$
 \Gamma_3(\mu)\ge \frac{A_\mu(S)^3}{s^2}+1-s.
 \tag{QC10}
$$

Zero-mass events impose no extra condition. The version omitting $1-s$ follows from QC8 with $t=c\mathbf1_S$, optimized over $c$. Neither version replaces the full variational family.

For the complete shallow23 dictionary, a coherent centre $a$ means choosing phase $a\bmod d$ in every slot. Its load is $\tau(\gcd(x-a,M))$. Write $d=3^j\prod_{p\in T}p$. The cube has the exact expansion

$$
 L_a(x)^3=\sum_{d\mid M}w_d\mathbf1_{\{x\equiv a\pmod d\}},
 \qquad w_d=(1,7,19)_j\,7^{|T|}.
 \tag{QC11}
$$

The local coefficients are increments of $(j+1)^3$. Sampling one globally fixed centre from $\mu$ gives

$$
 \sum_{d\mid M}w_d\sum_{a\bmod d}\mu([a]_d)^2
 =\mathbb E_{x,a\ {\rm iid}\ \mu}\tau(\gcd(x-a,M))^3
 \le\Gamma_3(\mu).
 \tag{QC12}
$$

Sampling an independent centre at **each** slot instead gives QC5 with $p_d(x)=\mu([x]_d)$. These are two different legal query mixtures; neither assumes that the residue coordinates of $\mu$ are independent.

For a cylinder $C=[a]_m$ with $m\mid M$, average coherent centres uniformly over $C$. At every $x\in C$ the average cube is

$$
 K_3(m)=\sum_{d\mid M}w_d\frac{\gcd(d,m)}d.
$$

Since every cube outside $C$ is at least 1,

$$
 \mu(C)\le\frac{\Gamma_3(\mu)-1}{K_3(m)-1}.
 \tag{QC13}
$$

In this dictionary,

$$
 K_3(m)=c_3(v_3(m))
       \prod_{\substack{p\mid m\\p\ne3}}8
       \prod_{\substack{p\mid M,\ p\nmid m\\p\ne3}}(1+7/p),
$$

where $c_3(0)=49/9$, $c_3(1)=43/3$, $c_3(2)=27$.
For an actual point this specializes to

$$
 \mu(x)\le\frac{G_3-1}{384^3-1}
 =\frac{906458572659}{9012491837460608}.
 \tag{QC14}
$$

It requires at least 9943 actual support points. If the five formal probabilities in Report731 describe five disjoint blocks of actual points, the blocks require respectively at least $(3443,2789,1588,1143,981)$ points, total 9944. The actual carrier can be much larger. These are necessary size bounds, not a rejection of all fine embeddings. Applying an actual-point bound directly to a coarse latent block would be invalid.

## Exact verification and remaining scope

The [hybrid consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_query_hybrids.py) and [result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_query_hybrids.json) verify 512 binary incidence patterns and all 50,625 ordered pairs of the 225 complete queries modulo 15. The source is uniform on its eight units; its full cubic maximum is $99/8$, and the independent source-centred slot average is $315/32$.

The [variational consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_query_variational.py) and [result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_query_variational.json) enumerate the same complete query dictionary under four different full-support laws, checking 1920 query/event cases and 96 conditional-cylinder identities. The all-zero query has load 1 under all these laws, while the full maximum is $99/8$ for the uniform law and $69/2$ when point 1 has mass $1/2$ and each other point mass $1/14$. Selected fields do not determine the full-query constraint even on the same actual carrier.

An independent implementation checked the variational identity on four separately chosen laws and found its own suboptimal fixed points. The five-table aggregate projection and coherent concentration formulas were independently checked with exact rational arithmetic. No full 384-slot optimization or actual fine embedding has been completed. The interfaces identify information that a valid boundary must retain; positivity for arbitrary old heights and unrestricted prime support remains unresolved.
