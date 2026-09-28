# The retained final-stage certificate gives a seven-core common-law query bound

For every finite family with distinct nontrivial odd moduli m>1, supported on at most seven odd primes, and every finite core period K supported on those same core primes and resolving that family, there is one probability measure on its actual complete survivor set such that

\[
 R_K(\widehat\mu)=\sum_{1<d\mid K}\max_a\widehat\mu(a\bmod d)
 \le C_7=\frac{70874}{3375}=21-\frac1{3375},
 \qquad \widehat\mu\le455625\,\lambda_K.
 \tag{LS1}
\]

The measure is fixed before any query layout is selected. The source is Michael Schroeder's *Nine Prime Divisors in Odd Distinct Covering Systems*, edition 1.0.1; its identity and verification boundary are in the [library entry](../../../../../../Library/Arith/schroeder2026nine.md). The statement extends the existing completion interface to a seven-prime core and any disjoint distinguished prime at least 23. It is an ordinary deduction from the attributed source comparison and the retained exact source certificate, not a new geometry enumeration, Lean certification, or an unrestricted Erdős #7 conclusion.

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

The resulting seven-core completion certificate does not settle unrestricted Erdős #7, and it is not a new bare finite-prime noncoverage range. [Chapter33](../../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md) already contains stronger bare head-and-tail noncoverage results. The additional result here is one supported law with a uniform original-query bound and an explicit distinguished-parent margin. Neither an arbitrary-core induction nor a bound for point-dependent adaptive query choices is proved.

[Report463](463-two-actual-prime-extensions-preserve-a-common-core-law.md) extends this same seven-core law by pure conditioning on new prime coordinates and one joint original-union deletion. It gives an explicit two-prime noncoverage criterion, retaining the unit old cofactor in every genuinely multi-prime new modulus.

[Report466](466-randomized-completion-retains-full-original-survivor-support.md) improves the common query bound to 21−4/3375 using the relative loss/reserve maximum of these same terminal rows. Averaging legal source choices additionally gives a law supported on every original survivor, with lower density one fifth of Haar on that set and the same upper cap455625. The coarser constants and consequences above remain valid.

## Source anchors and verification boundary

The source is `paper/main.tex` in edition 1.0.1, SHA-256 `73f78621a297650176cb796f763b9279eae9533efedbbb58405efc885ef41bb9`. Its load-bearing interfaces are:

- Section 2's completion, Section 3's explicit capped kernel and first-hit ledger, including the caps `(3/2,5/3,3/2,2,9/5,11/5)`.
- Section 4's ordered-increment comparison, complete exponent inventory and weighted aggregation, which permit arbitrary separate query phases.
- The charged-fibre comparison (`nu0`), and Section 8.3's matched positive-component replacement (`zero-replacement`).
- Section 9's explicit vertex interpolation and compatible-screening lemmas, for one common functional with fixed caps.
- Section 10's finite positivity certificate: 28,001 terminal rows, minimum integer surplus four, conversion denominator 135000.

The [exact consumer](../../../frontier/cover-geometry/seven-core-last-stage-bridge/seven_core_last_stage_bridge.py) reads the existing terminal certificate (SHA-256 `a1720cea93f30e04f31db6b49700a7d5c2d0fcfe9dff2f63ea2e3130b08629ac`) and checks all 28,001 distinct rows, phase counts, every integer gap and the displayed derived rational constants. Its [output](../../../frontier/cover-geometry/seven-core-last-stage-bridge/seven_core_last_stage_bridge.json) retains these counts, source identity and new constants; it does not copy the source rows.

The external input is `nine-prime-support/certificate/integer_certificate.json` extracted from the source edition 1.0.1 archive at [DOI 10.5281/zenodo.22759614](https://doi.org/10.5281/zenodo.22759614). The archive SHA-256 is `9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c`; the consumer independently checks the exact certificate SHA-256. Pass an existing extraction as follows, from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/seven-core-last-stage-bridge/seven_core_last_stage_bridge.py \
  --certificate /path/to/nine-prime-support/certificate/integer_certificate.json
```

The optimized-mode run passed. Checks remain active under `-O`. The `--certificate` input is required; `--output PATH` optionally writes the summary instead of JSON on stdout. No geometry, source producer, original screening traversal or Lean checker is invoked. The consumer verifies certificate arithmetic and new rational deductions. The source geometry maxima and arbitrary-height comparison remain attributed inputs, with the prior local verification boundary in the library entry; the common-law extraction and transport are ordinary mathematical proofs above.

## An eight-core law closes the missing-19 parent31 comparison

For a finite family of distinct nontrivial odd residue classes on the reference
primes `(3,5,7,11,13,17,23,29)`, and a fixed finite carrier K supported on
these eight primes and resolving that family and the parent31 cofactor-query
heights, the attributed completed-source construction
has one nonzero live measure mu, selected before the queried residue phases on K, for which

\[
 \sum_{1<d\mid K}\max_a\widehat\mu(a\bmod d)<29,
 \qquad \widehat\mu=\mu/\mu(1).
\]

This is an ordinary deduction from Schroeder's pinned 1.0.1 completion,
conditional-kernel, arbitrary-label and charged-fibre comparisons, together with
the exact finite computation below. It is not Lean verification or an
unrestricted odd-covering theorem. The additional hypotheses are those of the
source's finite distinct-modulus construction; no common maximizing query
labels, independent physical projections, or free changes of source law are
assumed.

### One construction before any query

Complete the fixed original family using the source selected set: pure powers
and `15,21,35,45,63,75,105,165`. The selected mixed moduli end at11, so completion
and the core kernels require no later query labels. The completed covered set
contains the original one. On this completed family fix the source capped
conditional-kernel construction through7,11,13,17,23,29, with

\[
 t=(2,4,4,8,12,16),\qquad
 C=(3/2,5/3,3/2,2,11/5,7/3).
\]

Every t is in `[1,p-2]`. The algebraic source comparison at a later prime p
uses its actual p and cap `(p-1)/(p-1-t)`; it does not depend on those primes
being consecutive. This is the same generic later-prime substitution used in
the retained ordinary eight-core consumer. The anchor primes3,5, selected
first7 projections and first7 cap3/2 are unchanged. The source caps are fixed
throughout all continuous vertices, projections and all tests.

At prime7 use the source charged-fibre enlargement. For each coarse cell x,
let T(x) be its actual active selected target digits and s(x) its number of
active selected classes. If targets coincide, enlarge T(x) deterministically
to exactly s(x) nonzero digits, adding the smallest unused digits as in the
source lemma. Declare their full first-digit cylinders forbidden together
with all remaining actual mixed7 classes. Define the capped kernel using
this enlarged bad set. Both the charged current loss and the reduced live
zero-depth atom concern this same padded process. This construction contains
all original deletions and is fixed before queries. It is kept even where an
ordinary screen ignores the improvement. There is only one actual law. At stage11 the physical165 constraint is part of the completed family;
this certificate releases its prescribed projection to the ordinary geometric
maximum as an upper comparison. No165-dependent choice of kernel is made at a
vertex. Likewise, all deeper pure3 holes may be retained in the actual source
while ignored by a uniform upper comparison. No new pure3 refinement or fixed165
geometry is needed here.

Normalize the selected anchor data by the source prefix permutations. The
canonical troublesome basic chart is `(a,b,c)=(2,4,1)`. Its actual45 class has
one of8 representatives `r=(4,7,8,11,16,22,31,34)`. Its actual75 class has a
projection `(d,k)` in `{1,2} x {1,2,3,4}` other than `(2,2)`. These are physical
source data fixed before testing, not independently optimized labels.

### The common positive functional

Let A be the actual anchor set avoiding every completed class supported on
{3,5}. The construction starts from Haar measure restricted to this single A.
Write R for a credited lower bound on135*Haar(A). The basic lower bound starts
with135*(3/8-1/8)=135/4, then restores the portion of the15-class already
charged as pure deletion. A mixed screen additionally restores corresponding
45 and75 overlap credits, all against the same A and the same original
union-bound charges. Changing screens does not change A or its measure.
The first7 padding occurs after initialization and is fully paid by L7;
it therefore does not require a different initial reserve. Under fixed
kernels and fixed deletions, transitions are positive linear operators of
initial measures. Enlarging the anchor comparison can only increase losses
and query integrals for these same kernels, exactly as the source mass lemma
states. Let L_p
be source loss upper functionals for the above fixed process, and set

\[
 D=R-\sum_pL_p.
\]

For any complete query layout, including its unit divisor, write

\[
 Q(x)=\sum_{d\mid K}{\bf1}_{x\equiv a_d\pmod d}\ge1.
\]

Use the source arbitrary-label comparison to bound

\[
 135\int(Q-18)_+\,d\mu\le H.
\]

The requested inequality is the single common-functional condition

\[
 D>0,\qquad 12D-H>0. \tag{M19-1}
\]

Indeed `mu(1)>=D/135` and `Q-1<=17+(Q-18)_+`, so

\[
 \widehat\mu(Q-1)\le17+H/D<29.
\]

The same measure serves all layouts. On fixed finite K, each divisor has
finitely many residue classes, so one may select simultaneously one maximizing
residue for every divisor after fixing the measure. No exchange of max and
choice of measure is involved.

The uniform query interpretation uses the source complete exponent inventory
and arbitrary separately labelled earlier residues, exactly as in retained
report462. The hypothetical last-query label inventory is a comparison, not a
new forbidden family or new kernel. Each current-depth copy can carry the same
chosen earlier residue; the geometric current-depth weights sum to one. Thus
the comparison holds for any query layout independently of the original
forbidden phases.

### Matched charged continuation, including the query

For the first7 comparison, the ordinary multiplier is `F7=1+J7`. Its zero-depth
atom has mass11/14 and its positive-depth atoms have masses `9/7^(j+1)` for
`j>=1`. For a physical projection xi let s(x) count its four selected
coincidences and let

\[
 \kappa_\xi(x)=(11,11,9,6,3)_{s(x)}.
\]

The charged zero component has spatial weight `kappa/14`. Positive first7
atoms stay unchanged. For any subsequent stage i, let `(nu_i,m_i)` be the
full multiplier law and mean before i; let `(nu_i^-,m_i^-)` omit7 but keep
exactly the same subsequent caps. The positive-depth submeasure is

\[
 \nu_i^+=\nu_i-\frac{11}{14}\nu_i^-,\qquad
 m_i^+=m_i-\frac{11}{14}m_i^-.
\]

Its atom weights are nonnegative and total mass3/14. The program checks the
atomwise nonnegativity with exact rational arithmetic. The charged upper
hinge is a positive sum

\[
 \mathsf E_{\nu_i^+}\,[F_{\rm ordinary}(t/M)M]
 +\frac1{14}\mathsf E_{\nu_i^-}\,[F_{\kappa}(t/M)M], \tag{M19-2}
\]

with the exact linear high-multiplier remainder in each component. Both
components refer to the same actual first7 deletion. Equation(M19-2) is used
for every subsequent source loss at11,13,17,23,29 and for the final query.
It does not subtract unrelated upper estimates. The two final A-projection
vertices have the following bounds under this comparison:

| j | R-query upper | `12D-H` |
|---|---:|---:|
|1|28.065220013702938|2.4365350884222634|
|3|27.088150326909023|5.451719642799413|

Here both nodes are `(2,4,1,8,j,2,1,0,-1)` and projection is `(1,4,7,14)`.
The exact fractions are in the computed result JSON.

### Why the screen hierarchy keeps the same law

The source compatible-screening lemma applies to the common positive
functional of the fixed charged construction. Releasing an anchor hole,
replacing `kappa<=11` by11, or releasing a prescribed projection to its
ordinary maximum gives an upper bound on that same functional. It does not
select a different probability or conditional kernel.

For a basic geometry row and its mixed refinement, the mixed cell set is a
subset of the basic cell set and the mixed nonnegative weight decreases
pointwise. Thus each mixed hinge maximum is at most the stored basic maximum.
The program checks this inclusion and weight inequality before any fallback.
It recomputes the mixed incidence sums and exact region mass for linear tail
bounds; it never substitutes a basic mass for a mixed mass in a negative
linear correction. Since every ordinary anchor load is at least1,
`(load-t)_+ <= load-1` for `t>=1`, so the mixed linear upper minus the exact
mixed mass is another valid pointwise bound.

A minimum of two such bounds is used only as a numerical bound at an individual
vertex. No convexity of the minimum is asserted. Likewise, rounding losses
upward is only a certified vertex estimate.

Vertices are comparison weight configurations, not instructions to construct
new probability measures or new kernels at each vertex. The actual family's
kernel was already fixed; the bound on it is evaluated on a convex weight
domain. The interpolated object is the true positive common functional

\[
 G=12\sum_p L_p+H.
\]

For fixed physical data it is built from nonnegative weighted hinge maxima
and positive expectations. Each geometric maximum is convex in its cell
weights. The continuous75 overlap budget is

\[
 t_h\ge0,\quad\sum_h t_h=1/20,\quad0\le e\le t_k.
\]

Its five vertex coefficients are `20(t_j-e*1_(j=k))` and `20e`.
They are nonnegative and sum to one. Cell weights and R have the same affine
interpolation, so `12R-G` at actual parameters is at least the same convex
combination of the certified vertex slacks. Ignored pure3 budgets are covered
uniformly; retaining them in the actual process can only improve these
screens, as in the source compatible-screening lemma.

Therefore it is legitimate for three vertices of the final `(r,d,k)=(8,2,1)`
chart to stop at the ordinary bound, while two vertices require charged
continuation. At every one of them the actual law is the same fixed charged
construction at that source's continuous parameters. At the latter two
vertices all280 physical projections are covered:554 node/projection pairs
pass the coarse7 screen, four pass the exact current7 screen, and the final
two pass(M19-2). Projection xi is discrete and fixed before interpolation.
All bounds use the same source thresholds and query18. No vertexwise choice
of actual law, schedule or query threshold occurs.

The complete finite domain is32 basic vertices, followed only on the canonical
basic chart by56 mixed discrete charts with five vertices each. The resulting
disjoint terminal coverage is:

| terminal comparison | number of rows |
|---|---:|
|basic,7 complete basic charts|28|
|mixed|278|
|coarse7|554|
|exact current7|4|
|charged continuation|2|
|total|866|

These counts are asserted by runtime checks. The full geometry carrier for
all280 mixed vertices is not enumerated: unsupported rows have the certified
pointwise basic domination above.

### Exact certificate and infinite-depth boundary

Across all866 terminal rows, the exact lower bounds are

\[
 D\ge\frac{3096725253}{1250000000}>0,
 \qquad
 \mu(1)\ge\frac{1032241751}{56250000000}>0.
\]

The minimum exact slack is approximately0.22340092258167663; the exact fraction
is saved in the output. The maximum vertex query bound is approximately
28.90982372331657, attained at a current7 B-projection screen. It is strictly
less than29 by an exact rational comparison. One should interpolate the
slacks or the inequality `H<12D`, not the displayed rounded ratios.

The product of caps is77/2. Hence the same normalized measure satisfies

\[
 \widehat\mu\le
 \frac{2165625000000}{1032241751}\lambda.
\]

Anchor depths are truncated only for finite exact geometry. Their omitted
regions use disjoint positive linear majorants and exact geometric probability
and first-moment sums. Later multipliers retain every atom below18 and use
exact full means for the rest. When a multiplier is at least a threshold, the
hinge is linear because the anchor load is at least1. All source and query
thresholds are at most18. Thus these calculations bound all exponent heights,
not just the listed low atoms. Ratios absent from the old15-point grid use
positive secants including the value at1, or monotonicity past the largest
grid point. No tail is silently discarded.

For any finite original family and fixed finite K, resolve its heights and
pad the source anchor heights as needed. The same source argument supplies the
law before all finite-K queries. For coordinatewise larger actual primes,
apply the retained finite independent digitwise prefix injections: a target
cylinder pulls back to an empty set or one source cylinder of the same
exponent vector, so distinct original moduli remain distinct after removing
empty preimages. Choose the source law before target queries for every fixed
injection, average the unnormalized pushforwards, and normalize once. The
uniform inequality `int(Q-1)dmu <29 mu(1)` and positive uniform mass lower
bound are preserved by that averaging. This asserts one law for every fixed
finite K, not compatibility of laws across different K.

In particular, parent31 has threshold `r-2=29`; the retained distinguished
parent completion argument gives a complete marginal strictly below1 on
support `(3,5,7,11,13,17,23,29,31)`, hence excludes a cover on that support.
Together with the earlier missing-prime exclusions, an exactly-nine-prime
family passing all complete marginals must contain3,5,7,11,13,17,19.
The implication uses the existing parent bridge and classification in
[MF15--MF22](../../../../../../Library/Arith/lettlsun2008cosets.md#common-query-source-laws-force-the-first-six-odd-support-primes);
it does not exclude the other nine-prime supports or families with ten or
more support primes.

### Portable retained artifacts and verification

The [consumer](../../../frontier/cover-geometry/finite-prefix-sources/missing19_joint_prefix.py)
reads the existing pinned basic72 geometry and its source certificate,
plus the [geometry extension](../../../frontier/cover-geometry/finite-prefix-sources/missing19_joint_prefix_geometry.json).
The extension contains exactly102 used batches and12,540 integer maxima,
including96 newly computed batches with9,471 maxima and six reused existing
A1 batches with3,069 maxima. It retains the source archive, verifier and C++
SHA256 identifiers, source URL, attribution and the full MIT license.

Its [exact output](../../../frontier/cover-geometry/finite-prefix-sources/missing19_joint_prefix.json)
retains the positive mass, slack and complete domain counts. From the
repository root, reproduce with Python3.9+ and its standard library:

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/finite-prefix-sources/missing19_joint_prefix.py
```

Only this extension is new input. The existing default query JSON is unchanged.
The consumer executes no C++ producer, reads no temporary probe directories,
and uses active `require` checks under normal Python and `-O`. Both modes
produce byte-identical JSON. Its geometry payload hashes bind every maximum
to the exact cells, weights, offsets and coefficient list. The extension file
itself is pinned, and every retained extension entry is checked as consumed.

The source file and geometry identities are recorded in the consumer and its
result JSON. The finite integer maxima come from the pinned
source enumerator; this verification does not upgrade the source theorem or
ordinary comparison adaptation to a Lean theorem.
