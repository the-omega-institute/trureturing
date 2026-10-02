# 832. One actual common centre blocks every threshold for the fixed retained table

For the specified infinite pure-comb source C and unchanged retained table, one fixed actual common centre already prevents the raw-source hinge criterion from succeeding at any real threshold 0 ≤ h < 28. Its largest gate is approximately −0.07392128793. Even after formally removing the entire tail debit, the largest gate is approximately −0.02823903737. Both occur at h = 18. Exact rational comparisons certify the respective bounds −7/100 and −7/250.

Consequently, tightening a valid raw-source upper bound, refining its conditioning tree, or reducing the tail debit to zero cannot repair this same source/table/budget criterion. A successful route must change a mathematical ingredient that this calculation held fixed, or justify a different criterion such as an actual survivor-restricted estimate. This is a fixed-method obstruction, not an Erdős #7 counterexample.

This calculation concerns the specified infinite pure-comb source at point C, with the unchanged phase-31 retained table of [Report 827](827-retained-factorial-hinges-preserve-complete-heights-but-need-not-improve-the-gate.md) and the raw retained measure used inside the bound of [Report 830](830-selective-conditioning-preserves-complete-heights-but-the-fixed-candidate-chooses-the-root-stop.md). It supplies actual common-centre lower witnesses for one fixed method. It does not produce a finite original covering family, a lower witness after restricting the measure to survivors, or an unrestricted Erdős #7 conclusion. The statements below are ordinary mathematical arguments and exact rational computations, without a new Lean claim.

## Source and joint phase contract

Let Q = (5, 7, 11, 13, 17, 19, 23), and set

$$
\delta_q=\frac{q-1}{q-2}.
$$

Use the infinite pure-comb laws specified in [Report 831](831-clean-root-query-phases-admit-exact-incidence-states-but-small-prefix-tails-remain-too-large.md). Every depth-e cylinder along a clean root has actual probability δ_q/q^e. At q = 5 the colours are {0}, {1}, {2,3,4}, with respective probabilities 4/15, 4/15, 7/15 and clean roots 0, 1, 4. At every other q the colours are {0} and its complement, with probabilities δ_q/q and 1−δ_q/q and clean roots 0 and 3. Higher digits of each chosen centre are zero.

The ternary leaves are 4, 7, 2, 5, 8 modulo 9. Write β_l for Haar probability conditional on leaf l, and λ_q for the actual pure-comb coordinate law. With the same fixed table 0 ≤ u_l(s) ≤ w_l, the raw retained measure is

$$
\nu_u=\sum_l u_l(s(x))\left(\beta_l\otimes\bigotimes_{q\in Q}\lambda_q\right).
$$

There is no additional factor w_l: it is already the envelope constraining u_l. Each colour probability is inserted exactly once when integrating this density. The total mass is

$$
M=\sum_{l,s}u_l(s)\prod_q\pi_q(s_q).
$$

A common centre supplies one compatible residue at every prime-power depth. Every numerical label receives the CRT phase determined by that same centre. Thus one legal whole assignment supplies all phases jointly, including the unit label. The centre is a point of a product of p-adic spaces; its finite restrictions have ordinary CRT representatives. No single ordinary integer is required to represent all depths simultaneously.

There are 5·3·2^6 = 960 canonical common centres. For this particular source, an arbitrary common centre can be moved to a clean root of its colour without reducing any matching-depth tail. Mismatching colours always have local count one. An absent ternary leaf can be moved to a live leaf in its root, and an absent root can be moved to a live root. These moves preserve a common centre and do not decrease its integrated hinge under the stated categorical source, by conditional stochastic domination. Consequently the 960-centre maximum equals the maximum over all common centres on this source. It need not equal the maximum over independent per-label phase assignments.

## Exact local laws and complete means

The local nonternary count includes the exponent-zero label. Fix source colour s and centre colour c. Its unnormalized law has mass π_q(s). If s ≠ c, the count is one throughout that source colour. If s = c is live, its atoms are

$$
\rho_{q;c,s}(1)=\pi_q(s)-\frac{\delta_q}{q},\qquad
\rho_{q;c,s}(n)=\frac{\delta_q(q-1)}{q^n}\quad(n\ge2),
$$

with complete first moment

$$
\int N_q\,d\rho_{q;c,s}
=\pi_q(s)+\frac{\delta_q}{q-1}.
$$

A zero-probability source colour has the zero measure. The live-colour subtraction formula must not be applied to it.

The ternary count is one for different roots modulo 3 and two for different leaves in the same root. On the same leaf,

$$
\Pr(N_3=3+j)=\frac{2}{3^{j+1}},\qquad j\ge0,
\qquad \mathbb E N_3=\frac72.
$$

For centre c = (l_*, c_q), let a_(l_*,l) be respectively 1, 2 or 7/2. Conditional coordinate independence and the common retained density give the complete mean

$$
m_c=\sum_{l,s}u_l(s)\,a_{l_*,l}
\prod_q\left(\pi_q(s_q)+\mathbf1_{s_q=c_q}\frac{\delta_q}{q-1}\right).
$$

The full count is the product of the local counts. If ρ_c(n) denotes its mass at n, then for every real h ≥ 0,

$$
H_c(h)=\int(N_c-h)_+\,d\nu_u
=m_c-hM+\sum_{1\le n<h}(h-n)\rho_c(n).
$$

Therefore every threshold 0 ≤ h ≤ 28 is determined by the complete mean, mass, and atoms 1 through 27. Retaining these low atoms is not truncation of the first moment or of the geometric heights.

## Tensor integration and finite controls

Start from the retained density tensor indexed by source leaf, seven source colours and load one. For a nonternary coordinate, replace its source-colour index by the centre-colour index using multiplicative convolution:

$$
T_{\rm new}(\ldots,c,\ldots;n)
=\sum_s\sum_{d\mid n}
T_{\rm old}(\ldots,s,\ldots;d)\,
\rho_{q;c,s}(n/d).
$$

Then apply the analogous ternary transform. Transport complete mass and mean separately with their scalar local factors. No maximum is taken inside a source sum.

For the fixed dimensions and atoms 1 through 27, the direct index count is 1,824,000 low-atom terms and 38,400 scalar products. Two atom buffers have 51,840 positive-index slots; implementation arrays also retain an unused zero slot. These counts are not a bound on bytes or measured runtime.

The actual-source control uses q = 5 with disjoint deletions 2 modulo 5 and 8 modulo 25, density 25/19, and the same five ternary leaves. At period 675 there are 285 source points. All 15 centre histograms, for all 12 labels 3^a5^b with 0 ≤ a ≤ 3 and 0 ≤ b ≤ 2, agree exactly with the finite tensor laws. The controls also check complete geometric means, finite terminal atoms, dead colours, damaged paths, zero retained tables and invalid inputs.

## Threshold envelope and fixed-method bracket

Write

$$
H_{\rm centres}(h)=\max_c H_c(h).
$$

Each centre hinge is affine on every unit interval. Their maximum is convex there. Hence the gate

$$
G_{\rm centres}(h)=(28-h)L-T-H_{\rm centres}(h)
$$

is concave on each unit interval and can be positive between negative integer endpoints. The exact calculation constructs the rational upper hull and evaluates every hull breakpoint, with the unchanged L and tail debit T of Report 827.

For example, on [2,3], the two integer-load hinges

$$
H_A(h)=1-\frac h4,\qquad H_B(h)=\frac94-\frac{3h}4
$$

against budget 27/16−h/2 give gate −1/16 at both endpoints and +1/16 at h = 5/2. These arise from loads (4,1,1,1) and (3,3,3,1) on one uniform four-point source. This is a guard against incorrect envelope logic, not a congruence-centre construction.

Let D(h) be the unchanged Report 830 upper bound. The output is bracketed by

$$
H_{\rm centres}(h)\le H_{\rm all\ layouts}(h)\le D(h).
$$

The difference D−H_centres is the width of this bracket. A large width does not establish that D is loose by that amount. It can also reflect the restriction to common centres.

## The actual witness and numerical result

Let A be the common centre whose ternary leaf is 5 modulo 9, whose q = 5 root is 0, and whose other six roots are 3. All higher digits are zero. Its complete mean is

$$
m_A=\frac{2751961447745792}{1234563408203125}.
$$

Every integer threshold from 0 through 28 was evaluated with the complete mean and exact low atoms. Because this is one fixed centre, its gate is affine on each unit interval. The largest endpoint value therefore certifies every real threshold. The result is

$$
\begin{aligned}
\max_{0\le h\le28}\bigl((28-h)L-T-H_A(h)\bigr)
&< -\frac7{100},\\
\max_{0\le h\le28}\bigl((28-h)L-H_A(h)\bigr)
&< -\frac7{250}.
\end{aligned}
$$

Both exact maxima occur at h = 18, inside the allowed half-open threshold domain. They equal the corresponding gate maxima obtained from the full 960-centre envelope. The exact large rational values and sufficient witness data are in [common_center_hinge.json](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/common_center_hinge.json); the following decimals are display values only.

| Threshold | Actual common-centre maximum | Report 830 upper bound | Gate with unchanged tail |
|---|---:|---:|---:|
| 16 | 0.18215572268187222 | 0.29277688095662818 | −0.07594333278769060 |
| 18 | 0.15481790441561940 | 0.24590656954131340 | −0.07392128793085245 |

At h = 18, the budget without any tail debit is approximately 0.12657886704707325, already below the actual hinge 0.15481790441561940. The unchanged tail debit is approximately 0.04568225056230630. The zero-tail maximum is −0.02823903736854616 and is only an algebraic comparison of the same actual-source curves.

The full common-centre envelope has 29 affine pieces and uses two centres. For h up to an exact rational crossing near 5.94567246926 it selects ternary leaf 8, q = 5 root 1, and the other roots 3. Thereafter it selects A. The single A witness suffices for the uniform obstruction, so no threshold-dependent phase choice is needed to establish that obstruction. No uniqueness of an optimum outside the enumerated finite menu is asserted.

The bracket at h = 16 is

$$
0.18215572268187222\ldots
\le H_{\rm all\ layouts}(16)
\le 0.29277688095662818\ldots.
$$

Its width is approximately 0.11062115827475596. This does not identify the exact unrestricted-layout hinge, but its lower endpoint already exceeds the available fixed budget.

Independent integration directly sums the retained source cells for the two selected centres and reproduces their complete means, all 27 low atoms and all integer hinges. It checks the 29 envelope segments against the saved 960-centre laws and confirms the one-centre obstruction.

The exact replay integrates all 960 centres and verifies their mass, nonnegative atoms, complete mean, hinge shape and Report 830 bounds. It uses 1,824,000 low-atom terms, of which 456,477 have nonzero factors, and 38,400 scalar products; the largest resulting denominator has 768 bits. Independent tiny hull controls include every pair crossing and an interior point in every induced interval, in addition to the explicit negative-endpoint/positive-interior example.

[common_center_engine.py](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/common_center_engine.py) implements the generic exact integration and rational upper hull. [common_center_hinge.py](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/common_center_hinge.py) binds the three immutable dependencies before parsing them, reconstructs the fixed source/table and compares the entire deterministic result by default. Writing a new result requires the explicit `--write-result` option. Complete means and low atoms remain separate throughout. Runtime readings and transient full-centre tables do not enter deterministic result equality.

## A concrete finite-query witness on the same source

The strict obstruction is already visible to a predetermined finite query. Keep ternary exponents 0 through 8 and every nonternary exponent 0 through 4. This gives 9·5^7 = 703,125 distinct numerical labels, including the unit, all using the same centre A. This statement limits the queried labels; the source remains the infinite pure-comb probability law.

Let N be the complete load and N_fin this finite-box load. The pointwise inequality

$$
0\le (N-h)_+-(N_{\rm fin}-h)_+\le N-N_{\rm fin}
$$

holds for every h. Under the normalized leaf-envelope product measure that dominates raw ν_u, write

$$
\mu_q=\frac{q-1}{q-2},\qquad
\tau_q=\frac1{(q-2)q^4},\qquad
\tau_3=\frac1{2\cdot3^6},
$$

and set A_qprod = ∏_q μ_q and B_qprod = ∏_q(μ_q−τ_q). The ternary mixture has complete mean at most 7/2 and its finite-box mean loss is w_centre·τ_3 ≤ τ_3. Consequently

$$
\int(N-N_{\rm fin})\,d\nu_u
\le \frac72 A_{\rm qprod}
-\left(\frac72-\tau_3\right)B_{\rm qprod}
=\frac{4304442202937533526963407}{792436236483305563958469375}
<\frac1{100}.
$$

The bound is approximately 0.00543190985566221. It is evaluated from seven factors, without enumerating the labels or searching cutoffs. Combining it with the strict complete zero-tail bound −7/250 gives

$$
(28-h)L-\int(N_{\rm fin}-h)_+\,d\nu_u
<-\frac9{500}
\qquad(0\le h<28).
$$

Thus even a finite query family already witnesses a uniform negative gate after removal of the tail debit. It remains a query on the same infinite comb source. It is not an admissible finite original covering family or a statement about restriction to survivors.

## Remaining scope

Monotone exhaustion by finite numerical-label sets supplies a finite-query witness to a strict complete-query gap under this same comb source. It does not turn that source into an admissible finite original covering family. Likewise the actual lower witnesses above concern raw ν_u; restriction to survivors requires an additional justified transfer, such as the specific categorical-mask exception in Report 831.

A separate linear problem can choose an actual maximizing phase independently for each numerical label. Under the clean-source contract, the selector depends only on its nonternary support and ternary type 0, 1 or at least 2, giving 384 selector types. This maximizes the complete mean, and hence also the hinge for 0 ≤ h ≤ 1 because every load is at least one. It does not generally maximize the hinge for h > 1, where overlaps of the chosen phases matter. That 384-type layout has not been evaluated in this experiment.
