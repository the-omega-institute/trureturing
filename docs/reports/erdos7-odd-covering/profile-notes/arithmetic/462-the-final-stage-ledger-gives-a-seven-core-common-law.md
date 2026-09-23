# The retained final-stage certificate gives a seven-core common-law query bound

For every finite family with distinct nontrivial odd moduli m>1, supported on at most seven odd primes, and every finite core period K supported on those same core primes and resolving that family, there is one probability measure on its actual complete survivor set such that

\[
 R_K(\widehat\mu)=\sum_{1<d\mid K}\max_a\widehat\mu(a\bmod d)
 \le C_7=\frac{70874}{3375}=21-\frac1{3375},
 \qquad \widehat\mu\le455625\,\lambda_K.
 \tag{LS1}
\]

The measure is fixed before any query layout is selected. The source is Michael Schroeder's *Nine Prime Divisors in Odd Distinct Covering Systems*, edition 1.0.1; its identity and verification boundary are in the [library entry](../../../../../Library/Arith/schroeder2026nine.md). The statement extends the existing completion interface to a seven-prime core and any disjoint distinguished prime at least 23. It is an ordinary deduction from the attributed source comparison and the retained exact source certificate, not a new geometry enumeration, Lean certification, or an unrestricted Erdős #7 conclusion.

## Extracting a query bound from a final-stage certificate

The new bridge is the following general deduction. Let B>0 be a conversion factor between comparison units and measure units. Suppose a fixed nonzero finite live measure mu and numbers D,U,delta satisfy

\[
 0<D\le B,\quad U\ge0,\quad \delta>0,\quad
 \mu(1)\ge D/B,\quad D-U\ge\delta.
\]

Assume that, simultaneously for every complete query load L>=1,

\[
 B\int(L-\tau)_+\,d\mu\le\beta U,
 \qquad \tau\ge1,\quad\beta>0.
\]

Then the same normalized law obeys

\[
 \widehat\mu(L-1)
 \le\tau-1+\frac{\beta U}{D}
 \le\tau-1+\beta\left(1-\frac\delta D\right)
 \le\tau-1+\beta-\frac{\beta\delta}{B}.
 \tag{LS0}
\]

This follows from the pointwise inequality L-1<=(tau-1)+(L-tau)_+ and normalization. If beta=q-1-tau, its conclusion is R<=q-2-beta*delta/B. If in addition mu<=P*lambda, then the same probability has density at most BP/delta. The input U is a uniform comparison functional for all query layouts, not the actual deletion cost of a dummy final coordinate.

Here B=135, q=23, tau=12, beta=10, U=L23 and delta=4/1000. What remains to justify is that the attributed source supplies these hypotheses for one fixed seven-core measure; the sections below establish that map explicitly.

## The common reference measure

Work first on the seven reference primes 3,5,7,11,13,17,19. Apply the source completion and conditional-kernel construction. Source completion may move auxiliary selected residues, but its covered set contains the original covered set. The completed source family is fixed throughout the argument. Original query residues are not replaced by completed residues.

The completion can be fixed using only the original core family. Source Section 2 uses the selected set

\[
 \{p^e:e\ge1\}\cup\{15,21,35,45,63,75,105,165\}.
\]

Every selected mixed modulus has largest prime at most 11. The auxiliary pure 23-powers divide no core modulus and therefore impose no completion constraint on a selected core class. Fix the core completion first, and add the pure 23-family independently if using the eight-coordinate presentation. The explicit capped-kernel formula at q<=19 uses only the pure q-forbidden set and the mixed bad set ending at q. It can thus be chosen before any hypothetical 23-query labels are supplied. The source statement permits kernels to depend on the full fixed family; this argument selects the local formula whose data already lie in the core.

The source construction exposes the full coordinates in order. Keep the charged first-7 forbidden fibres, the fixed physical 165-projection at 11, and the ordinary later stages, with caps

\[
 (C_7,C_{11},C_{13},C_{17},C_{19})
 =(3/2,5/3,3/2,2,9/5).
\]

Stop immediately after 19, obtaining one unnormalized live measure \(\mu_7\). In applying the source's eight-coordinate comparison, the 23-coordinate is an auxiliary final-stage comparison only; it is not included in \(\mu_7\). Equivalently, embed the fixed seven-core family in the source carrier by adding a 23-coordinate without original mixed-23 classes. All earlier completed data and kernels can be fixed without reference to a later query. In source Section 2, the selected mixed completion moduli have largest prime at most 11. A pure-23 class neither divides an earlier selected mixed modulus nor is divisible by an earlier selected modulus. Fix the completion choices once; source Lemma 3.1 then defines each early kernel from its current pure and mixed sets. No query is supplied as an input to that process.

For the actual fixed anchor parameters and projections, let \(\mathsf R\) and \(L_q\) denote the source's finest common reserve and loss-upper functions in units of \(1/135\). Put

\[
 D_7=\mathsf R-L_7-L_{11}-L_{13}-L_{17}-L_{19}.
 \tag{LS2}
\]

First-hit accounting and the density caps give

\[
 \mu_7(1)\ge D_7/135,
 \qquad \mu_7\le(27/2)\lambda.
 \tag{LS3}
\]

All objects in (LS2) belong to the same completed family and continuous anchor parameters. The loss estimates are not separately optimized probabilities.

## Why the source final-stage numerator controls every complete query

A query layout selects one arbitrary residue \(a_d\) for each divisor of a fixed finite period K, including the unit divisor. Define

\[
 L(x)=\sum_{d\mid K}\mathbf1_{x\equiv a_d\pmod d}\ge1.
\]

The final source stage uses current prime 23, threshold 12 and denominator 10. It imposes no prescribed physical 23-projection. Its common numerator is obtained from the complete nonnegative exponent inventory and maximization over the unknown anchor projections, with all preceding caps and charged first-hit information retained.

To identify that inventory with the query, label every current exponent \(e\ge1\) by the same queried earlier residue for each nonunit d. Then

\[
 Z_{23}^L(x)=22\sum_{e\ge1}23^{-e}
                 \sum_{1<d\mid K}\mathbf1_{x\equiv a_d\pmod d}
 =L(x)-1,
 \tag{LS4}
\]

because \(22\sum_{e\ge1}23^{-e}=1\). Equation (LS4) is an identification of test labels, not an alteration of the forbidden family or of \(\mu_7\). One can first truncate the e-sum and then use monotone convergence. Unused exponent vectors may be filled arbitrarily in the comparison, which only enlarges its nonnegative load.

Source ordered-increment comparison permits arbitrary separately labelled phases. Reverse integration applies to the fixed earlier kernels; at 7 it uses the charged live-fibre comparison. Weighted aggregation permits arbitrary independent anchor phases. The positive first-hit formula replaces only the same zero-7 component and preserves all positive-depth caps. Hence the source final common upper function \(L_{23}\) satisfies, simultaneously for every layout,

\[
 135\int(L-12)_+\,d\mu_7\le 10L_{23}.
 \tag{LS5}
\]

The proxy \(L_{23}\) must not be replaced by the actual deletion in an empty dummy-23 family, which could be zero. It is the uniform complete-inventory upper comparison certified by the source. The source's bare noncoverage theorem alone would not establish (LS5); its explicit final-stage functional does.

For clarity, the retained post-7 comparison has spatial zero atom

\[
 \rho_{s(x)}=\frac1{14}(11,11,9,6,3)_{s(x)}
\]

and unchanged positive atoms \(9/7^{j+1}\). If the ordinary numerator is \(N\), and \(Z(a)\) omits 7 from the multiplier law, its common continuation numerator is

\[
 N-\frac{11}{14}Z(a)+\frac1{14}Z(\kappa a).
\]

This is a decomposition into matched positive comparison components, including the same omitted-depth majorants. It does not subtract unrelated upper bounds. Formula (LS5) inherits exactly this comparison and therefore all arbitrary-query phases remain compatible with the single \(\mu_7\).

## The retained all-branch certificate supplies a uniform gap

The source certificate has 28,001 terminal inequalities. It uses

\[
 \mathsf R^- =\lfloor1000\mathsf R\rfloor,
 \quad L^+=\left\lceil1000\sum_{q=7}^{23}L_q\right\rceil,
 \quad\mathsf R^- -L^+\ge4.
\]

Here \(q=7\) through 23 means 7,11,13,17,19,23. The integer-to-Haar denominator is 135000. Thus every terminal ledger has surplus at least

\[
 \delta=4/1000=1/250
\]

in 135-cell units, or \(\delta/135=1/33750\) in Haar units.

The source's explicit vertex interpolation and compatible-screening lemma apply to one finest common functional. Earlier stopping screens uniformly lower-bound that same functional; the continuous budgets use the same nonnegative vertex coefficients for the reserve and every positive comparison component. Therefore, for every actual completed family and all its continuous parameters,

\[
 D_7-L_{23}\ge\delta.
 \tag{LS6}
\]

This step uses the complete retained certificate hierarchy, not only its four deepest terminal examples, nor the minimum of unrelated query-dependent functionals. Since loss-upper functions are nonnegative and the reserve is a lower bound for the initial mass in cell units,

\[
 0<D_7\le\mathsf R\le135.
 \tag{LS7}
\]

## Normalize only once

Pointwise \(L-1\le11+(L-12)_+\). With (LS3), (LS5) and (LS6),

\[
 \int(L-1)\,d\widehat\mu_7
 \le11+\frac{10L_{23}}{135\mu_7(1)}
 \le11+\frac{10L_{23}}{D_7}
 \le21-\frac{10\delta}{D_7}
 \le21-\frac1{3375}.
 \tag{LS8}
\]

Every inequality concerns the same measure. At finite K, maxima for different divisors can be simultaneously selected as one complete query layout, yielding the bound on \(R_K\). Furthermore,

\[
 \mu_7(1)\ge D_7/135\ge1/33750,
 \quad
 \widehat\mu_7\le\frac{27/2}{1/33750}\lambda=455625\lambda.
 \tag{LS9}
\]

No unverified numerical improvement to an intermediate source loss is needed.

## Finite transport to actual odd primes

Use the unnormalized random-prefix transport from [report460](460-joint-five-prime-moments-give-a-parent-seventeen-completion-margin.md#transport-to-any-five-actual-odd-primes).

Order the actual core primes \(q_1<\cdots<q_7\), and reference primes \(p_i\in(3,5,7,11,13,17,19)\). Then \(q_i\ge p_i\). Resolve every original and queried coordinate height, padding the anchor heights as required by the source construction, and use the existing finite independent random digitwise prefix injections \(F\) from the reference carrier to the actual carrier.

For a fixed F, an original target cylinder pulls back to an empty set or one source cylinder with the same complete exponent vector. Distinct original numerical moduli therefore stay distinct after removing empty preimages. Choose one source live measure \(\mu_F\) for the pulled-back original family. Uniformly in F it has mass at least \(1/33750\), density at most \(27/2\) relative to source Haar, and

\[
 \int(L-1)\,d\mu_F\le C_7\mu_F(1)
\]

for every complete source query.

A target query pulls back to a partial source layout with its unit term retained. Complete missing terms arbitrarily; this only increases its load. Average the unnormalized pushforwards,

\[
 \mu_{\rm target}=\mathbb E_F F_*\mu_F,
\]

then normalize once. The query inequality averages with right side exactly \(C_7\mu_{\rm target}(1)\). Its validity for every source layout avoids any assumption of a common maximizing layout across F. The domination inequality is applied before averaging, and the random prefix shifts give \(\mathbb E_FF_*\lambda_{\rm source}=\lambda_{\rm target}\); thus the same density and mass constants hold. The measure avoids every original target class.

For fewer than seven primes pad with primes unused by the full original family and distinct from the distinguished parent, then project. This preserves original support avoidance, the query bound, and Haar domination. The parent need not exceed all core primes. The quantifiers concern one law for all layouts on each fixed finite period; no compatible choice of target laws across separately increasing periods is asserted.

## Distinguished parent at least 23 and retained tail bridge

Retain the original phase of every mixed modulus and define

\[
 \ell_{r,H}(x)=
 \sum_{\substack{r^e d\ \mathrm{original}\\1\le e\le H,\ 1<d\mid K}}
 r^{1-e}\mathbf1_{x\equiv a_{r^e d}\pmod d},
 \qquad B_{r,H}=r-\sum_{e=1}^H r^{1-e}.
\]

Pure r powers are excluded from the load and reserved in B. Missing original mixed labels contribute zero; each partial depth layout is bounded by a complete query.

Write \(\varepsilon=1/3375\). For any disjoint distinguished prime \(r\ge23\), the actual weighted mixed completion load satisfies under this same probability

\[
 \mathbb E\ell_{r,H}\le\frac{23}{22}(21-\varepsilon),
 \quad B_{r,H}\ge23-23/22=483/22.
\]

Take the actual good set

\[
 A=\{x\text{ in the actual core survivor set}:\ell_{r,H}(x)
 \le(23/22)(21-\varepsilon/2)\}.
\]

Markov's inequality and the density cap give

\[
 \widehat\mu(A)\ge\frac1{141749},\qquad
 \lambda(A)\ge\frac1{64584388125}>\frac1{65000000000},
\]

and pointwise on A,

\[
 \ell_{r,H}\le B_{r,H}-23/148500.
\]

The height-independent tail bridge of [report455](455-positive-mass-core-margins-give-height-independent-tail-cutoffs.md), in the distinguished-prime form of [report458](458-distinguished-prime-completion-removes-the-early-phase-restriction.md), may therefore use

\[
 \Lambda=65000000000,\quad
 J_1\le323323/110592,\quad J_2\le2263261/110592,
 \quad N=1330222484448.
\]

For any finite outside-prime set disjoint from rK and lying above cutoff \(B\ge3^{256}N^3\), its weighted tail is at most \(324\Lambda J_1/B<3^{-250}<23/148500\). The numerator 324ΛJ1 is 123140595703125/2. The final global conditioning may change the core marginal but retains its support in A, hence its pointwise core control. The expected total original weighted completion is strictly below B_{r,H}, so some actual r-free survivor admits an uncovered parent fibre. Original numerical moduli, all original phases, arbitrary finite heights and outside support sizes, and a single final probability law are retained.

## Relation to the earlier comparison and remaining scope

[Report461](461-query-stop-loss-gives-a-common-law-six-core-completion-margin.md) uses the basic anchor comparison before deletion and obtains a seven-core bound above 21 for all five tested thresholds. The present bridge retains the source's charged first-hit geometry, mixed-anchor refinement, fixed stage-11 information and complete common ledger. It therefore supplies additional joint information; it does not contradict the earlier stated numerical comparison.

The resulting seven-core completion certificate does not settle unrestricted Erdős #7, and it is not a new bare finite-prime noncoverage range. [Chapter33](../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md) already contains stronger bare head-and-tail noncoverage results. The additional result here is one supported law with a uniform original-query bound and an explicit distinguished-parent margin. Neither an arbitrary-core induction nor a bound for point-dependent adaptive query choices is proved.

## Source anchors and verification boundary

The source is `paper/main.tex` in edition 1.0.1, SHA-256 `73f78621a297650176cb796f763b9279eae9533efedbbb58405efc885ef41bb9`. Its load-bearing interfaces are:

- Section 2's completion, Section 3's explicit capped kernel and first-hit ledger, including the caps `(3/2,5/3,3/2,2,9/5,11/5)`.
- Section 4's ordered-increment comparison, complete exponent inventory and weighted aggregation, which permit arbitrary separate query phases.
- The charged-fibre comparison (`nu0`), and Section 8.3's matched positive-component replacement (`zero-replacement`).
- Section 9's explicit vertex interpolation and compatible-screening lemmas, for one common functional with fixed caps.
- Section 10's finite positivity certificate: 28,001 terminal rows, minimum integer surplus four, conversion denominator 135000.

The [exact consumer](../../frontier/cover-geometry/seven_core_last_stage_bridge.py) reads the existing terminal certificate (SHA-256 `a1720cea93f30e04f31db6b49700a7d5c2d0fcfe9dff2f63ea2e3130b08629ac`) and checks all 28,001 distinct rows, phase counts, every integer gap and the displayed derived rational constants. Its [output](../../frontier/cover-geometry/seven_core_last_stage_bridge.json) retains these counts, source identity and new constants; it does not copy the source rows.

The external input is `nine-prime-support/certificate/integer_certificate.json` extracted from the source edition 1.0.1 archive at [DOI 10.5281/zenodo.22759614](https://doi.org/10.5281/zenodo.22759614). The archive SHA-256 is `9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c`; the consumer independently checks the exact certificate SHA-256. Pass an existing extraction as follows, from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/seven_core_last_stage_bridge.py \
  --certificate /path/to/nine-prime-support/certificate/integer_certificate.json
```

The optimized-mode run passed. Checks remain active under `-O`. The `--certificate` input is required; `--output PATH` optionally writes the summary instead of JSON on stdout. No geometry, source producer, original screening traversal or Lean checker is invoked. The consumer verifies certificate arithmetic and new rational deductions. The source geometry maxima and arbitrary-height comparison remain attributed inputs, with the prior local verification boundary in the library entry; the common-law extraction and transport are ordinary mathematical proofs above.
