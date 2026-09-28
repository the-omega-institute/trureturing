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

## A fixed missing-23 comparison node closes under all eta14 phases

The following is a **local comparison certificate**, under the same attributed
source construction and completion hypotheses used above. The core is now
`(3,5,7,11,13,17,19,29)`, with source thresholds `(2,4,4,8,8,16)`.
Fix the finest comparison vertex and first selected projection

    node=(2,4,1,8,1,2,1,0,13),    xi7=(1,4,7,14).

The vertex specifies comparison weights; it is not an assertion that every
actual source has these parameters. At each of the five later primes
`11,13,17,19,29`, allow the actual projections of the four numerical labels
`3p,5p,9p,15p` to vary independently over

    E={1,2} x {1,2,3,4} x {2,4,5,7,8} x {14}.

Thus `|E|=40`. A single fixed padding rule and source schedule, evaluated at
this vertex, satisfy the strict target for all `40^5=102400000` parameter
tuples. All comparisons use query threshold16 and retain the original
selected label identities. Other vertices, other `xi7`, and other final
`15p` projections are **not covered by this certificate**. In particular it
does not exclude the entire missing-23 support or resolve unrestricted
Erdos#7. These are ordinary source-comparison deductions and exact rational
calculations, not new Lean verification.

### The same source supplies every current and query estimate

For each nonanchor prime `p>=7`, the sums over proper selected divisors of
`3p,5p,9p,15p`, including pure powers and the anchor class15, are respectively

    1/3+1/p, 1/5+1/p, 4/9+4/(3p), 3/5+23/(15p).

Each is strictly less than1. Selected labels belonging to different such
primes introduce no further divisibility. Thus the source completion lemma
applies to this whole selected inventory. On a fixed anchor cell, the active
selected first digits are nonzero after excluding the pure first digit.
Pad these deterministically to exactly as many distinct nonzero digits as
there are active selected labels, before any query, and charge all resulting
forbidden fibres. This is possible even when selected digits coincide,
since there are at most four selected labels and `p-1>=6` available digits.

The finite core cells at this vertex are

    C={x mod135: x mod3 !=0, x mod9 !=1, x mod27 !=4,
                  x mod5 !=0, x mod15 !=2, x mod45 !=8}.

The four selected projections at prime `p` define `s_p(x)` by counting the
equalities modulo `3,5,9,15`. With `cap_p=(p-1)/(p-1-t_p)`, the remaining
conditional mass is bounded by

    S_s=min(1,cap_p*(p-1-s)/p).

The ordered-increment zero component is `S_s-cap_p/p`; there is only one
separately forbidden pure first digit. The first three charged comparisons
therefore have zero components

    kappa7  =(11,11,9,6,3)/14,
    kappa11 =(28,28,28,28,25)/33,
    kappa13 =(23,23,23,23,21)/26,          s=0,1,2,3,4.

The accompanying positive components put, respectively, mass
`9/7^m`, `50/(3*11^m)`, and `18/13^m` at each integer multiplier `m>=2`.
These are positive components of one comparison functional. For example,
the joint zero11/zero13 component multiplies
`kappa11(s11(x))*kappa13(s13(x))` on the **same cell x**; no independent
randomization of the two fields is introduced.

For `p=17,19,29` the outgoing zero upper bounds are constant over every
`0<=s_p<=4`, namely `15/17,86/95,80/87`. The ordinary full multipliers at
these primes therefore bound the continuation of this same charged
construction. Using an ordinary current bound also requires the head-release
argument below; it does not mean changing to an unpadded actual process.

Here is the exact release principle. At a fixed multiplier and fixed anchor
depths, a selected numerical label contributes coefficient
`c=(p-1)/p` inside an ordinary head whose **total** coefficient is `M>=c`.
If its prescribed live residue is `s` and the remaining head chooses `r`,

    (M-c)*1_r+c*1_s
       =(1-c/M)*(M*1_r)+(c/M)*(M*1_s).

The weights in this convex combination are scalars for the entire cell
vector. A nonnegative weighted hinge is convex. Maximizing over every live
residue consequently bounds this split head by the corresponding ordinary
head. Apply this successively to any subset of the four selected heads.
An empty selected intersection contributes zero and is handled by
monotonicity. The geometry producer checks that nonempty selected residues belong to
the full head domain. In particular, a `5`-head can have total coefficient
`m(1+v)`; subtracting `c` from a bare `m`, or subtracting `m*c`, would be
incorrect.

For the finite current maxima, the seven ordinary category coefficients at
anchor depths `u,v` are

    m*(1,1,1+u,1+v,1+v,1+v,(1+u)(1+v))

on categories `(3,9,27,5,15,45,135)`, with baseline `m`. Extract `c` once
from the four selected categories and add `c*s_p(x)` to the spatial load.
The current numerator is its hinge at `t_p`, divided by `p-1-t_p`.
The prefix7 bound uses the source's equivalent baseline-zero form,
threshold1 and divisor4. Its positive tail majorant also has baseline zero;
the replay reproduces `L7<=10.4062667005` with that convention.

Releasing all four heads justifies the ordinary current bounds in some
routes. Releasing only the `3,5,9` heads retains the actual `15p` projection;
this is the tighter final route used below. These operations change upper
bounds on the same positive functional, not the source kernels, original
phases or permissions to choose a different law for a query.

### Three spatial fields and the positive transfer bound

Only three members of `E` have a four-way intersection with the core:

| Name | Projection | Four-way intersection in C |
|---|---|---|
| A | `(2,4,2,14)` | `{29,74,119}` |
| B | `(2,4,5,14)` | `{14,59,104}` |
| C | `(2,4,8,14)` | `{44,89,134}` |

All other37 intersections are empty. The simultaneous prefix permutation
`2 <-> 5 mod9`, preserving the mod5 coordinate, exchanges A and B. It
preserves the full core, every source region weight and the fixed `xi7`.
It transports each selected numerical label, including every later
projection, rather than merely exchanging an unlabelled overlap count.

The reference continuation has `(xi11,xi13)=(A,B)`. Complete current tables
give the following uniform upper bounds, separately for every later member
of `E`:

    L17<=3.6986331854, L19<=4.1096457772, L29<=1.9678563744.

Their maxima need not be attained by the same tuple: each is an upper bound
valid for every tuple under the same comparison construction. The current17
bound already releases the zero13 refinement and uses the full13 multiplier.

Changing a zero11 field from its reference can increase it by at most
`1/11` on its reference three cells. The analogous zero13 increase is at
most `1/13`. In each correction retain the other prime's **full** multiplier.
This bounds the cross term when both fields change; adding two independently
optimized actual laws would not establish the estimate.

The required three-cell hinge can be computed without new geometry. The
three cells share their `3,9,5,15,45` residues; the `27` and singleton heads
can both be placed on one cell. At anchor depths `u,v` and multiplier `m`,
the maximizing loads are

    m(6+3v), m(6+3v), m(6+3v)+m(1+u)(2+v).

After integrating the actual four anchor regions, this restricted functional
has mass3 and first-moment upper bound `189m/8`. Its exact positive-part
correction to `189m/8-3t` is obtained from

    2*max(0,t-m(6+3v))
      +max(0,t-m(6+3v)-m(1+u)(2+v)).

Only finitely many exceptional shallow-depth cases need enumeration; the
remaining correction is a constant geometric tail, summed exactly along
with the omitted masses and first moments. On these
cells the charged7 component is `9/14` at multiplier1 plus `9/7^m` at
`m>=2`, with total mass `6/7` and first moment `31/28`. The positive transfer uses
this component, full13 for the zero11 correction, and full11 for the zero13
correction. The zero11 addition to current17 is exactly

    1243323/10250240=0.121296964753996... .

No zero13 addition is charged again to current17, since its reference bound
already used full13. Both additions remain in current19 and current29 when
required. Numerical minima between this transfer and an ordinary bound are
upper estimates for the same functional; no convexity of those minima is
asserted.

### A uniform query16 closes the remaining comparisons

Release zero11 and zero13 to their full comparisons for the final query.
Keep the same charged7 spatial field. With

    cap_p=(p-1)/(p-1-t_p),
    Pr(M_p=1)=1-cap_p/p,
    Pr(M_p=m)=cap_p*(p-1)/p^m, m>=2,

compose the full multipliers for `11,13,17,19,29`. For the charged7 positive
part use mass `3/14` and first moment `13/28`; its zero part uses the stored
integer numerator field `(11,11,9,6,3)` divided by14. This gives the single query bound

    H16=32.37222665896469... <32.372227.

The rational value is retained in the [coverage result](../../../frontier/cover-geometry/finite-prefix-sources/missing23-eta14/coverage.json).
For multiplier `m<16`, positive secants between retained integer anchor
hinges give an upper bound. For `m>=16`, the ordinary anchor load is at
least1, so the hinge is affine and the exact omitted mass and first moment
suffice. The special argument at thresholds at most1 is `whole-t*mass`.
No infinite multiplier or anchor tail is dropped.

For a row with six current losses `L_p`, put

    D=135/4-sum_p L_p,
    G16=14*sum_p L_p+H16.

The source comparison supplies `R_query<=15+H16/D`. It is therefore enough
to certify the **linear slack**

    14*(135/4)-G16=14D-H16>0.

The complete disjoint routing of the1600 ordered `(xi11,xi13)` pairs is:

| Route | Number of pairs |
|---|---:|
| Earlier current tables and ordinary continuation |1562|
| Same-source three-cell positive transfer |37|
| `(C,C)`, current13 refinement and three released heads |1|

The first1562 pairs have `D>=2.5265145827`; the common query16 bound already
suffices. For the final `(C,C)` route the six losses are

    (10.4062667005,5.0397006462,5.6643071239,
       3.7563590447,4.2212861839,2.0223146834),

giving `D=2.6397656174`. Its current17 calculation retains **both** zero11
and zero13 fields on the same cells, as do its later calculations. Releasing
the other three selected heads makes the late bounds uniform over all40
projections at each of17,19,29; it does not require their Cartesian geometry
enumeration.

The worst retained row has query upper bound at most `28.9771304032<29`.
Rounding every individual current loss and `H16` upward to units of
`10^-6` still leaves, over the entire1600-pair domain,

    D>=2.316082,    14D-H16>=0.052921>0.

These are uniform bounds over the three remaining independent projection
choices, hence cover all `1600*40^3=40^5` declared tuples. The final query
threshold is16 throughout; the earlier query20 comparisons are used only
to identify a disjoint reuse route. They are not interpolated with query16
ratios. Future interpolation across continuous source weights must keep
the same actual padded kernel and the common positive functional `G16` and
prove the corresponding inequalities at the other vertices. This local
certificate supplies none of those still-missing vertex inequalities.

### Reproduction and verification boundary

The [portable checker](../../../frontier/cover-geometry/finite-prefix-sources/missing23-eta14/verify.py)
recomputes the multiplier products, exact tails, positive transfer and every
label route from fixed numerical inputs. Its literal manifest pin checks
those inputs and the retained source artifacts. The
[geometry replay program](../../../frontier/cover-geometry/finite-prefix-sources/missing23-eta14/geometry_replay.py)
reconstructs full geometry payloads and uses the attributed enumerator to
reproduce their integer maxima. Reading a pinned table is not reported as
independently recomputing that table.

The ordinary and charged7 base envelopes were regenerated in the portable
producer: eight batches and6048 integer maxima reproduce their masses,
first moments and all integer thresholds1 through28. The remaining current
bounds have a separate geometry replay surface. The full selected source,
enumerator and MIT attribution are retained with the package. Ordinary
arithmetic and the source-comparison argument, rather than Lean, carry this
local certificate.

From the repository root, the default checker prints its summary;
an explicit `--output PATH` writes the complete1600-route result to that path:

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/finite-prefix-sources/missing23-eta14/verify.py
```

The checker retains its checks under `-O`. The geometry replay uses normal
Python and the pinned source model's active assertions; that source model
deliberately rejects `-O`. Geometry regeneration requires a C++17 compiler
and an explicit fresh-rebuild request. The declared local scope remains
unchanged by either verification mode.

## The same fixed node permits all later phases

This extends the preceding fixed eta14 certificate. It fixes exactly the
same node `(2,4,1,8,1,2,1,0,13)`, `xi7=(1,4,7,14)`, source thresholds
`(2,4,4,8,8,16)` and query16. The projections at 11 and13 still range over
40 eta14 labels each. At 17,19,29 each projection now ranges independently
over all280 source labels, with last coordinate in `(1,4,7,8,11,13,14)`.
It does not extend the first two eta values, the node, xi7, or the entire
missing23 support.

The new domain has `1600*280^3=35123200000` tuples. All1600 prefix-label
pairs satisfy the common query16 criterion uniformly over their later
choices. The worst rational query upper rounded upward is `28.9603851962`,
at `(xi11,xi13)=(A,C)` or `(B,C)`, where
`A=(2,4,2,14)`, `B=(2,4,5,14)`, `C=(2,4,8,14)`.
Ceiling each of six losses and H16 to one millionth leaves
`D>=2.318861` and `14D-H16>=0.091827>0`.

### Source-preserving extension and routing

For each of five spatial-field pairs `AB,CC,CA,AA,FA`, [the new bounds](../../../frontier/cover-geometry/finite-prefix-sources/missing23-late280/bounds.json) record
the three partially released current bounds at every allowed eta.
`F=(2,3,2,14)` is a physical projection whose four-way intersection is
empty. The three selected heads 3,5,9 are released into their complete
contributing domains, while the actual selected15 head is retained.
Thus each recorded eta value bounds all40 first-three-coordinate choices;
no 280-cubed geometry enumeration is involved.

Each of these direct later comparisons retains all eight same-cell
zero/positive components at7,11,13. The inherited convex-release proof
uses a coefficient scalar across the whole cell vector and bounds the
same padded source. Earlier physical labels are not reselected. A flat
zero11 field is identical for all empty four-way intersections, so the FA
continuation applies to every such xi11 while each row still pays its
own current11 and current13 bound. This replaces only a continuation
upper comparison; it does not identify distinct actual source laws.

The exact prior permutation exchanges A and B, preserves C and eta,
and maps the entire allowed later projection domain to itself. It
transports `CA` to `CB`, `AA` to `BB`, and `FA` to the corresponding
empty11/B comparison. The consumer retains the individual prefix-label
costs under these transports.

For the general transfer reference AB, the current17 bound instead uses
full13. Its seven released eta bounds are refined at eta8 and eta11 by
all40 four-head values, and at eta14 by the older all40 table. The final
uniform current17 upper is `3.7130521644`, at eta13's released screen.
The current19 and29 reference bounds retain both zero fields; their
uniform uppers are `4.2109420471` and `2.0248867687`. Therefore the earlier
positive-transfer proof applies without a zero13 addition at17. It uses
both applicable additions at19/29.

The two new actual-C current13 refinements are

| physical xi13 | current13 upper |
|---|---:|
| `(2,4,2,14)` | `5.852992434` |
| `(2,3,2,14)` | `5.6272629423` |

The same permutation gives the third-coordinate5 cases. All other
current11/current13 inputs, H16, the transfer increments, infinite-tail
formulas, and completion/padding hypotheses come from the fixed prior
package. Both packages concern one source schedule and query16.

The disjoint selected routes are transfer1521, FA-direct74, AA-direct2,
CA-direct2, and CC1. AA and CC happen to have equal late numerical tables;
they were calculated separately, and no new general identity is inferred.
The worst later29 released bound occurs at eta8, so eta14 alone cannot be
asserted to be worst over the allowed eta values.

### Exact domain and numerical verification

The extended numerical input contains105 released values (five field pairs,
three current stages, seven eta choices), seven full13 current17 reference
values, two complete40-label current17 refinements, and two actual-C
current13 values. Each has a corresponding targeted producer command; all116
commands have reproduced the recorded values from complete-input geometry
caches, without a new geometry call in that reconstruction check.

Every `released` command begins with the eight positive components from
zero/positive choices at7,11,13, keeping their spatial zero products on the
same anchor cell. For later current19 or29 the intervening full17 or
full17/full19 multiplier laws are appended. The physical xi11/xi13 pair
remains the pair named by the row. In contrast, both full13 current17
commands use four zero7/zero11 components multiplied by the full13 law;
they do not retain a zero13 field. The current13-C command uses four
zero7/zero11 components before13 and the selected physical current13 label.
Thus these producer maps preserve precisely the different hypotheses needed
by the direct and transfer routes.

The old source completion, fixed padding, reserve and final H16 remain
unchanged. Every new estimate is an upper bound on that same construction.
For each ordered prefix pair, the arithmetic consumer takes the smallest
available valid six-loss sum, then verifies `D=135/4-sum L>0` and
`14D-H16>0`. The chosen routes partition all1600 prefix pairs and each
selected later bound is uniform over all280 allowed projections at its
prime. Consequently every one of their independent triples is covered;
no claim is made that separate stage maxima are simultaneously attained.

The smallest exact reserve lower bound is

$$
D=\frac{2876939530945115455363}{1240667948520000000000}.
$$

The exact minimum slack is approximately0.09186131983613406 and the
worst rational query upper is approximately28.9603851961421. The displayed
upward bound28.9603851962 and millionth certificate0.091827 are conservative.
The [consumer](../../../frontier/cover-geometry/finite-prefix-sources/missing23-late280/verify.py) checks only exact arithmetic and routing from pinned
numerical inputs; a cache replay is not an independent rerun of its integer
maxima. These results add no Lean declaration or kernel verification.

The extension covers neither the other eta11/eta13 slices nor other nodes
or xi7. Those change earlier spatial zero fields and must be treated as new
comparison domains. In particular no monotonicity in eta and no universal
worst-eta claim follows from this result.

Reproduction commands and verification layers are in the [extension package](../../../frontier/cover-geometry/finite-prefix-sources/missing23-late280/README.md).

## Two earlier phase slices close by monotone reuse

Keep the finest node `(2,4,1,8,1,2,1,0,13)`, `xi7=(1,4,7,14)`, source
schedule `(2,4,4,8,8,16)` and query16. The following new domain changes
only the last coordinate of xi11 to1 or4. For each of these two slices,
xi11 has40 allowed first-three-coordinate choices, xi13 has40 eta14
choices, and xi17,xi19,xi29 each independently range over all280 allowed
projections. Thus the two disjoint slices contain3200 prefix pairs and
`3200*280^3=70246400000` full tuples.

This is a fixed-node ordinary comparison certificate. It does not cover
another eta13, xi7 or anchor, or the whole missing23 support. Its current11
numerical inputs are reused attributed source bounds; this extension
requires no new geometry enumeration and adds no Lean verification.

### Attributed current11 inputs and the unchanged incoming prefix

The [source v1.0.1 archive](../../../../../../Library/Arith/schroeder2026nine.md)'s `nine-prime-support/certificate/closing.json`
records the following exact upward current11 bounds for state A1:

| eta11 | current11 upper |
|---|---:|
|1|`49538723779/10000000000`|
|4|`12457528149/2500000000`|
|7|`51353199569/10000000000`|
|8|`10534248179/2000000000`|
|11|`51724699137/10000000000`|
|13|`51353199569/10000000000`|
|14|`52980442211/10000000000`|

In the byte-pinned source verifier, the `main` representative selection
fixes A1 to the node above and xi7=(1,4,7,14); `fixed165` evaluates these
seven phase choices. Its incoming law contains only the already charged7
comparison. Its fixed current threshold is4 at11. Neither the later prime23
in the source theorem nor its later thresholds enter this calculation.
Replacing the later schedule with the already declared missing23 schedule
therefore changes no current11 input.

The source `fixed165` bound keeps the selected15 head and releases heads
3,5,9. Apply the already proved convex-release argument to the four-label
padded process, with the full class coefficient scalar across the cells.
Its current11 loss is bounded by exactly that fixed15 functional for the
physical eta11. Therefore the table above is uniform over the40 remaining
physical label choices in each slice. The original selected labels are
retained; a bound does not authorize changing them.

The archive SHA256 is
`9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c`,
and the extracted `closing.json` SHA256 is
`2fc48ecf06bc7ca256f7107648158fe92bff2052368b438267e6541e3eb07b1b`.
The source verifier SHA256 is
`e3296d181686c0f1925e755583fdc4df2ffeb2bacbc36a77a2396bbe3b4a9135`.
These identify the attributed numerical prerequisite, not a new independent
rerun of its maxima.

### One flat11 comparison controls current13 and later reads together

For any physical xi11 and any anchor cell x, put

$$
 \rho_{11}(x)=\min\{1,(5/3)(10-s_{11}(x))/11\}-5/33.
$$

Since `0<=s11(x)<=4`,

$$
 0\le\rho_{11}(x)\le28/33.
$$

The positive11 atoms remain `50/(3*11^m)` for `m>=2`. Replacing only its
zero atom by28/33 gives one common upper comparison. It dominates every
actual11 field pointwise on the same anchor cells, including the new
nonempty intersections in eta11=1 and4. No independence assumption or
random relabelling is used.

Every current13 functional is a nonnegative weighted hinge maximum and
is monotone in these spatial weights. Hence the earlier flat11 current13
table applies to each actual xi13 in eta14. The selected13 projection
is preserved in that lookup, and its padded current13 loss is fully paid.
Thus the current11 cost from the source table and the current13 cost from
the flat11 table are upper bounds for one process, not estimates assembled
from two independently chosen source laws.

The same domination persists through the later positive comparisons:
products retain all factors at the same anchor x and every kernel and
summand is nonnegative. In particular, the late280 `FA` table has exactly
the flat11 field28/33 and the prescribed13 field A. It is therefore a
valid continuation upper bound even when the actual xi11 field is not
empty. By the preserved prefix permutation, its transported table applies
to prescribed13 field B as well. No previous physical11 current label is
changed by this use of the flat comparison.

For other xi13, use the already established AB/B,A positive transfer:
fill the reference11 deficit, fill the reference13 deficit when its field
changes, and compare with the ordinary alternative. The reference17
functional uses full13 and receives no extra13 charge; the19/29
functionals retain the two zero fields and receive each applicable
positive addition. This is the same transfer proof and same source
schedule as the late280 certificate.

### Uniform strict bounds

For each of the3200 ordered prefix pairs, retain its actual label tuple
and record its zero11 support. The source current11 upper depends only on
eta11, while the current13 upper retains the actual xi13. Among the valid
late continuations select the smaller numerical upper bound. The resulting
disjoint routes consist of3040 transfer rows and160 flat11/A-or-B rows.
Every chosen late comparison is uniform over all280 projections at each
remaining prime.

With `D=135/4-sum L`, the same H16 gives `R_query<=15+H16/D`.
Exact rational calculation yields:

| eta11 slice | upward query upper | minimum millionth-rounded slack `14D-H16` |
|---|---:|---:|
|1|`28.7472240926`|`0.595197`|
|4|`28.9194656258`|`0.187251`|

The least exact reserve lower bound over both slices is

$$
 \frac{46560119126441}{20020000000000},
$$

and the millionth-rounded reserve remains at least2.325677. Both slices
therefore meet the strict query target29. The source schedule, padded
construction and query16 are unchanged throughout.

The [consumer](../../../frontier/cover-geometry/finite-prefix-sources/missing23-eta11-1-4/verify.py) pins the [source current11 input](../../../frontier/cover-geometry/finite-prefix-sources/missing23-eta11-1-4/source_current11.json) and the prior late280
consumer, whose own pins validate the inherited bounds. It exhaustively
checks all3200 rational inequalities; normal Python and optimized Python
retain the same exception checks. The separate source-current11 producer
uses the old pinned geometric engine and can rebuild each phase with an
explicit request. No new raw geometry is needed to derive this reuse
certificate from its stated numerical prerequisites.

The remaining complete eta11 slices7,8,11,13 with eta13=14 are not closed
by this certificate; other eta13 values are also unresolved. Their full
physical zero fields must remain explicit. The16 nonempty support fields
and one empty field offer a finite continuation index, while first-stage
current costs still require the actual numerical labels.

Reproduction commands and verification layers are in the [two-slice package](../../../frontier/cover-geometry/finite-prefix-sources/missing23-eta11-1-4/README.md).

## The remaining four eta11 slices at the same prefix

Fix the same A1 node `(2,4,1,8,1,2,1,0,13)`, xi7=(1,4,7,14), source
schedule `(2,4,4,8,8,16)` and query16. This increment treats eta11 in
`{7,8,11,13}`, keeps eta13=14, and permits each later prime17,19,29 all280
physical projections. Each eta11 slice has40 actual xi11 and40 actual
xi13 labels. The four disjoint slices thus contain6400 prefix pairs and
`6400*280^3=140492800000` full tuples.

The previous common-source comparison, fixed padding and exact infinite
remainders remain the mathematical hypotheses. The additional finite
upper bounds below are computed by the attributed integer geometry engine;
this is ordinary comparison mathematics and rational verification, not
new Lean verification.

### Exact current11 labels replace a coarse phase maximum

At each selected physical xi11, retain all four prescribed current heads
rather than immediately releasing the first three. The incoming
comparison is the same charged7 measure: its spatial zero7 component
plus its positive7 component. The threshold at11 remains4; the four
subtractions are each10/11 and the added current offset is
`(10/11)*s11(x)`. The exact small-multiplier geometry and linear remainders
are evaluated as in the existing producer.

The original source's phase-only upper bound is therefore replaced by a
smaller upper bound on the same padded current loss. This does not alter
the selected labels, earlier probability construction, or later source
schedule. The resulting maxima over all40 physical labels are:

| eta11 | maximum four-head current11 upper |
|---|---:|
|7|`4.7368193697`|
|8|`5.0799304760`|
|11|`4.8428666522`|
|13|`4.8134860188`|

There are128 explicitly enumerated representatives. The already proved
prefix permutation2↔5 modulo9 preserves the carrier, every source region
weight, fixed xi7, and the mod5 coordinate. It therefore preserves eta and
transports each physical cylinder. The other32 labels are its recorded
images, not new unconstrained optimizers. The checker verifies the160
label maps and equal transported costs.

Using the existing flat11 current13 table and later transfer bounds, a
uniform sufficient current11 target for every eta14 xi13 is
`4.9963896314`. All40 labels in eta7,11,13 and38 labels in eta8 meet
this conservative target. For the two remaining labels

$$
 D=(2,3,2,8),\qquad E=(2,3,5,8),
$$

the precise existing budgets leave six prefix pairs: each of D,E paired
with `(2,3,2,14)`, `(2,3,5,14)`, or `C=(2,4,8,14)`.

### Three current13 refinements and one continuation field pair

For xi11=D, its actual zero11 field is retained on the same anchor cells
when evaluating current13. The three direct four-head bounds are

| actual xi13 | current13 upper |
|---|---:|
|`(2,3,2,14)`|`5.5832079324`|
|`(2,3,5,14)`|`5.6477324318`|
|`(2,4,8,14)`|`5.7371194871`|

The simultaneous prefix permutation gives the E cases, interchanging the
first two selected13 labels and fixing C. These estimates include the
padded current13 cost. The first two, together with the existing late
bounds, resolve four of the six pairs.

For `(D,C)`, retain all eight same-cell zero/positive components at7,11,13
through the late comparisons. At each of17,19,29 release the selected
heads3,5,9 and keep its actual15-head phase. Evaluate the seven allowed
eta values separately. Every resulting value is uniform over all40
other physical label coordinates by the existing scalar-coefficient
convex-release proof. Thus the three stage maxima are valid uniformly
over all280 choices each:

$$
 (L_{17},L_{19},L_{29})
 \le(3.7708091560,4.2373978034,2.0296210340).
$$

The first two maxima occur at eta14 and the last at eta8. No universal
worst-eta assumption is used. The direct current17 bound here retains
zero13, unlike the older full13 reference used in the positive-transfer
route. The E,C continuation follows by the same source-preserving
permutation, which preserves every later eta and its full280 domain.
These direct bounds resolve the final two prefix pairs.

All other rows may still use the older flat11 current13 comparison and
positive-transfer or flat11/A-or-B continuations. Pointwise zero11
majorization and positive-kernel composition justify this reuse while
each row pays its actual current11 upper. Taking the smaller valid
numerical continuation bound does not change the actual source law.

### Common-query certificate and its extent

The disjoint selected routes are6078 transfer rows,320 flat11/A-or-B rows,
and2 direct D,C or E,C rows. For each row the consumer checks exactly

$$
 D_{\mathrm{live}}=135/4-\sum_q L_q>0,
 \qquad14D_{\mathrm{live}}-H_{16}>0.
$$

It uses the same H16 as the earlier increments. Consequently the final
query upper `15+H16/D_live` is strictly below29. The conservative results
for the four slices are:

| eta11 | upward query upper | minimum millionth-rounded slack |
|---|---:|---:|
|7|`27.5870278810`|`3.633939`|
|8|`28.9500381606`|`0.115893`|
|11|`28.1283559009`|`2.149281`|
|13|`27.9737716755`|`2.560601`|

The worst row is D paired with `(2,3,5,14)` and its transported counterpart.
The least exact reserve lower bound is

$$
 \frac{46458079200453}{20020000000000}.
$$

Even after rounding each of the six losses and H16 upward to one millionth,
the reserve is at least2.320580 and the strict slack is at least0.115893.

The new reconstruction surface consists of128 current11 representatives,
three current13 values, and21 direct late phase values:152 targeted
producer calls. Its data dependency is the existing byte-pinned source
producer, so no old source or large geometry table is duplicated. The
[consumer](../../../frontier/cover-geometry/finite-prefix-sources/missing23-eta11-rest/verify.py) pins [the new bounds](../../../frontier/cover-geometry/finite-prefix-sources/missing23-eta11-rest/bounds.json) and the preceding late280 consumer, validates
the explicit label transports, and checks all6400 rational inequalities.
Numerical upper-bound provenance, exact routing, and independent reruns of
integer maxima remain distinct verification layers.

Combining the three disjoint increments, **all280 physical xi11 choices**
are now covered while xi13 is still restricted to its40 eta14 choices;
the later three primes each allow280 choices. Their union contains
`280*40*280^3=245862400000` tuples at the same fixed node and xi7. The other
eta13 slices, other xi7, other comparison nodes, continuous interpolation,
and unrestricted Erdos#7 remain outside this conclusion.

Reproduction commands and verification layers are in the [four-slice package](../../../frontier/cover-geometry/finite-prefix-sources/missing23-eta11-rest/README.md).

## 固定 A1 与素数 7投影的全部后续相位闭合

保持 `missing23` 支撑 $(3,5,7,11,13,17,19,29)$、A1 节点
$(2,4,1,8,1,2,1,0,13)$、实际 $\xi_7=(1,4,7,14)$、阈值
$(2,4,4,8,8,16)$ 和查询 $16$。本节补齐
$\eta_{13}\in\{1,4,7,8,11,13\}$：$\xi_{11}$ 有全部 $280$ 个物理选择，
$\xi_{13}$ 有 $240$ 个选择，后三个素数各有独立的 $280$ 个物理选择。
本节的 $67\,200$ 个前缀对与前三个增量的 $11\,200$ 个
$\eta_{13}=14$ 前缀对不相交；合并后是在上述固定节点和固定 $\xi_7$ 下的
$280^5=1\,721\,036\,800\,000$ 个参数元组，不包含其他节点或其他 $\xi_7$。

### 同源八项分解的双零场上界

对当前仍存活的同一个实际原胞 $x$，记 $s_q(x)\in\{0,1,2,3,4\}$ 为
实际四个首根柱的交叠数。沿用同一比较过程的零部分

$$
z_q(x)=\min\!\left(1,C_q\frac{q-1-s_q(x)}q\right)-\frac{C_q}{q},
\qquad C_{11}=\frac53,\quad C_{13}=\frac32.
$$

枚举五个可能的交叠数给出

$$
0\le z_{11}(x)\le\frac{28}{33},\qquad
0\le z_{13}(x)\le\frac{23}{26}.
$$

其中素数 11的分子表是 $(28,28,28,28,25)$，素数 13的是
$(23,23,23,23,21)$。这两个逐点不等式不要求两个投影处于同一相位，
也不要求同时取到各自上界。

后续比较从 $7,11,13$ 各自的零/正部分展开成八项。对任意一项，
只把该项含有的 $z_{11}(x),z_{13}(x)$ 分别增大为上述常数；正部分的
原子、总质量、均值和共同原胞权重均沿用原值。所有权重和被积损失非负，
故同一项的乘积和、再对八项求和，仍给出原来那个实际过程的损失上界。
这一比较记为 FF。它是支配用的比较表达式，不被宣称为另一份实际可实现的
联合来源；因此不存在把两个不同来源的最优值强行拼在一起的步骤。

实现中的 `initial_parts()` 保留全部八项，`xi11=None,xi13=None`
仅让 `envelope` 把常数分子 $28,23$ 按齐次性提到外面。
尤其是素数 17处仍保留素数 13的零/正两部分。计算第十九、二十九素数时，
分别再乘入原阈值下的 `full(17,8)`、`full(19,8)`；每个当前素数仍只从
相应类别提取一次 $(q-1)/q$，不能重复扣除。

对当前 $3,5,9$ 首根选择作既有凸组合释放，保留实际 $15$ 相位。
每个素数核对全部七种相位以后得到

| 当前素数 | FF 的统一损失上界 | 最大值所在 $15$ 相位 |
|---:|---:|---:|
| $17$ | $3.7871241310$ | $14$ |
| $19$ | $4.2580372016$ | $14$ |
| $29$ | $2.0375647458$ | $14$ |

每行覆盖该当前素数全部 $280$ 个物理投影。数值输入由 $21$ 次明确的
阶段/相位重建命令承担，并非枚举后续的 $280^3$ 元组。

### 素数 13的一个 incoming field 即可覆盖所有实际第十一投影

计算当前素数 13损失时，仍支付各实际 $\xi_{11}$ 已取得的素数 11
损失界，只对后续使用的 $z_{11}$ 采用 $28/33$ 上界。
保持素数 7实际场不变，逐个保留素数 13四个首根标签，得到

| $\eta_{13}$ | 四十个当前物理投影的最大损失上界 |
|---:|---:|
| $1$ | $5.3503280249$ |
| $4$ | $5.4641334047$ |
| $7$ | $5.4090419889$ |
| $8$ | $5.7567487780$ |
| $11$ | $5.6147864510$ |
| $13$ | $5.5187391151$ |

每个相位直接重建第三坐标属于 $\{2,4,7,8\}$ 的 $32$ 个代表。
既有模 $27$ 前缀置换把模 $9$ 的 $2,5$ 两支互换，同时保持模 $5$，
保留原胞、各区域权重、类别分区、固定 $\xi_7$ 与所有 $15$ 相位。
它把当前第三坐标 $2$ 的标签连同完整来源对象运输到第三坐标 $5$，
恢复其余八个标签。六个相位合计 $192$ 个重建代表、$48$ 个明确运输标签。
这里 flat11 是常数场，自动被同一置换保持；没有自由置换模 $5$ 标签。

素数 11的实际损失表直接复用先前三个增量：$\eta_{11}=14$ 的四十标签表、
$\eta_{11}\in\{7,8,11,13\}$ 的一百六十标签表，以及有归属来源的
$\eta_{11}\in\{1,4\}$ 两个统一界。不以当前素数 13的上界替换已经支付的
素数 11损失，也没有重新选择素数 11的实际来源。

### A/B 的素数 17旧界可以与 FF 的后两界共同使用

仅当实际 $\xi_{11}$ 是
$A=(2,4,2,14)$ 或 $B=(2,4,5,14)$ 时，素数 17使用既有
`full13 reference17` 的统一界 $3.7130521644$。
`full(13,4)` 的零质量正是 $23/26$，正部分与 `pos13` 相同，故它逐点支配
任意实际素数 13投影对应的分解；这个素数 17界不限定实际 $\xi_{13}$。
A 与 B 的运输同时作用于整个来源和当前首根标签，并保留已核对的完整
当前投影域。其余素数 11投影使用 FF 的素数 17界。

无论选择哪一个素数 17界，第十九、二十九素数均使用 FF 的相应界。
各界分别约束同一实际过程各阶段的损失，故可以相加。
这不要求各个比较表达式的最大值同时可达，也没有改变实际第十一或第十三
投影；没有新增 `lift11` 或 `lift13`，更没有在 FF 界上重复收费。

### 完整有限域的严格读数

对每个实际前缀对，沿用共同查询分子 $H_{16}$，逐项检查

$$
D_{\mathrm{live}}=\frac{135}{4}-\sum_{q\in\{7,11,13,17,19,29\}}L_q>0,
\qquad 14D_{\mathrm{live}}-H_{16}>0.
$$

新域共有 $66\,720$ 对使用 FF 的三个后续界，另 $480$ 对使用 A/B 的旧
素数 17界与 FF 的后两个界。精确有理数核对覆盖全部 $67\,200$ 对，
输出压成 $42$ 个不相交、各含 $1\,600$ 对的相位块，并保留各块最坏证书。
新域的共同读数是

$$
D_{\mathrm{live}}\ge\frac{189780333}{80000000},\qquad
15+\frac{H_{16}}{D_{\mathrm{live}}}\le28.6461881576<29.
$$

把六个损失界及查询分子各自向上取整到百万分之一后，最小严格余量仍为
$0.839287$。新域最坏代表是
$\xi_{11}=A,\xi_{13}=(2,3,2,8)$；对称标签给出相同数值。
新域覆盖 $1\,475\,174\,400\,000$ 个参数元组，连同旧的
$\eta_{13}=14$ 域，固定节点全部 $280^5$ 元组的最大已核对查询上界为
$28.9603851962$。

这些结论使用普通数学支配论证、整数几何重建和精确有理数验证。
它们不是新增 Lean 形式化，也不延伸到其他 A1 以外节点、其他实际
$\xi_7$，或完整 missing23 分支的全称结算。

复现材料位于 [canonical 数据包](../../../frontier/cover-geometry/finite-prefix-sources/missing23-eta13-rest/)，
其中 [精确算术核对](../../../frontier/cover-geometry/finite-prefix-sources/missing23-eta13-rest/verify.py)
与 [运行及重建说明](../../../frontier/cover-geometry/finite-prefix-sources/missing23-eta13-rest/README.md)
分别承担有限域检查和明确的几何重建入口。

## 用同一原胞上的正差运输一个新的素数 7 投影

仍固定 A1 节点 $(2,4,1,8,1,2,1,0,13)$、原有 $44$ 个原胞、全部来源权重、
阈值 $(2,4,4,8,8,16)$ 和查询 $16$。前节对
$\xi_7^0=(1,4,7,14)$ 已覆盖后续五个素数各自全部 $280$ 个物理投影。
这里只考察两个明确的新投影：

$$
P=(2,4,7,4),\qquad Q=(2,4,2,14).
$$

原 source 的 `spatial()` 给出了各实际 $\xi_7$ 的当前素数 $7$ 损失上界公式，
但发布的 `integer_certificate.json` 只保存各终端行的总损失，不能把它
当作这些新投影的单独当前损失表。本节两项当前损失均重新按该公式计算。
source 的九素数最终结论及后续素数 $23$ 的原阈值不参与这次结算。

### 直接点态支配没有提供新投影

记

$$
z_7^\xi(x)=\frac{K(s_\xi(x))}{14},\qquad K=(11,11,9,6,3).
$$

对全部 $280$ 个投影和 $44$ 个原胞作有限核对，只有旧投影自身满足
$z_7^\xi\le z_7^{\xi^0}$。因此不能把旧证书直接用于一个新投影而不补充费用。
保持模 $3,9,27,5,15,45$ 各具名分区及四个区域权重的来源自同构也不能
移动旧投影：模 $3$ 两块的大小 $20,24$ 不同；模 $5$ 四块大小为
$14,5,11,14$，且权重区分同为 $14$ 的两个块；模 $9$ 的 $7$ 块在其
模 $3$ 父块中由大小固定。因而旧投影的模 $3,5,9,15$ 四个标签均固定，
其轨道为单点。本节需支付比较代价，不把新投影宣称为该对称轨道中的成员。

定义同一原胞上的正差

$$
\delta_\xi(x)=\bigl(z_7^\xi(x)-z_7^{\xi^0}(x)\bigr)_+.
$$

于是 $z_7^\xi\le z_7^{\xi^0}+\delta_\xi$。素数 $7$ 的正乘子部分不变。
对固定的后续物理标签，令 $\mathscr G$ 表示只来自素数 $7$ 零分量的
比较泛函，$\mathscr P$ 表示不随该投影改变的正分量贡献，并令完整比较损失
$\mathscr L_\xi=\mathscr P+\mathscr G(z_7^\xi)$。非负加权铰链、对合法布局
取最大值及非负积分使 $\mathscr G$ 单调且次可加，故

$$
\mathscr L_\xi\le\mathscr L_{\xi^0}+\mathscr G(\delta_\xi).
$$

第一项用已经覆盖全部后续标签的旧证书；第二项保留同一原胞权重、只增加
$\delta_\xi$ 的贡献。这不构造另一个实际同余族，也不把两个来源的独立最优
选择宣称为共同可达。取最大值的次可加性恰好允许分别求两个上界。

### 五项后续费用与查询分子一起支付

令 $\mathcal E_\delta(t)$ 是正差原胞权重下的 ordinary 铰链包络。
实现以整数分子 $14\delta(x)$ 乘原来源权重，最后统一除以 $14$。
当前四个固定首根的作用可按既有凸组合释放不等式放大到 ordinary 包络；
这给同一实际当前核的上界，不能在释放后再重复加入固定首根费用。

正差从素数 $7$ 的零部分进入，故初始乘子是 $M_{11}=1$，没有新增 `pos7`。
随后依次乘入原阈值下的完整比较乘子 $N_{11},N_{13},N_{17},N_{19},N_{29}$。
其零质量分别支配对应实际零场，正原子沿用原模型。记

$$
\mathcal P=\{11,13,17,19,29\},\qquad
M_q=\prod_{\substack{p\in\mathcal P\\p<q}}N_p.
$$

五项后续增量为

$$
\Delta_q=\frac{\mathbb E\,\mathcal E_\delta(t_q/M_q)M_q}{q-1-t_q},
\qquad q\in\{11,13,17,19,29\}.
$$

公式表示按乘子分布作齐次铰链积分；实际程序对低乘子用完整包络表，对高乘子
用精确剩余概率与一阶矩的线性上界。五个分母依次为 $6,8,8,10,12$。
最终查询的增量是在已经乘入 $N_{29}$ 后的同一铰链积分，阈值仍为 $16$，
没有损失分母：

$$
\Delta_H=\mathbb E\,\mathcal E_\delta\!\left(
\frac{16}{N_{11}N_{13}N_{17}N_{19}N_{29}}\right)
N_{11}N_{13}N_{17}N_{19}N_{29}.
$$

因此不能只给后续损失加费用而继续使用旧查询分子。这里的 ordinary/full
上界对全部后续物理标签统一，故无须重建它们的 $280^2$ 个前缀表。

### 旧共同下界不依赖舍入后的排序

旧完整域给出共同 $H_0>0$ 与
$15+H_0/D_i\le\overline R_0=28.9603851962$，其中各 $D_i>0$。
因此直接取

$$
D_*:=\frac{H_0}{\overline R_0-15}\le D_i.
$$

这是一个保守共同下界，不声称它是精确最小值。以此避免从舍入后的最大比值
所在行推断精确最小 $D_i$。对新投影，只需验证

$$
D'_*=D_*+L_7^0-L_7^\xi-\sum_q\Delta_q>0,
\qquad 14D'_*-(H_0+\Delta_H)>0.
$$

以上费用对全部旧标签统一，故一份验证同时运输完整 $280^5$ 个后续元组。

### 两个有限 pilot 区分了路线

对 $P=(2,4,7,4)$，正差仅在九个原胞上为 $2/14$，来源加权总质量为 $33/28$。
当前素数 $7$ 的损失上界为 $8.6384129072$，相对旧上界 $10.4062667005$ 少计
$1.7678537933$。后续五项增量及查询增量约为

| 项 | 增量 |
|---:|---:|
| 素数 $11$ | $0.2976207594$ |
| 素数 $13$ | $0.3387458941$ |
| 素数 $17$ | $0.1920203797$ |
| 素数 $19$ | $0.2240151819$ |
| 素数 $29$ | $0.0964227515$ |
| 查询分子 | $1.5542156049$ |

表中小数仅显示数值，证书使用完整有理数。按上述保守 $D_*$，新投影的统一
查询上界为 $26.5478851276<29$。把可用量向下、费用与查询分子向上取整到
百万分之一后，仍有 $D'_*\ge2.937889$、严格余量至少 $7.204003$。
所以这个新投影覆盖同一固定 A1 下全部 $280^5$ 个后续物理元组。

对 $Q=(2,4,2,14)$，正差质量为 $69/28$，被此路线丢弃的负差质量为
$453/140$。当前损失上界虽降到 $10.2215449381$，只保留正差的运输仍得到负的
共同 $D'_*$ 下界，因而不能结算。这项比较未能认证该投影，不反驳该实际投影的可行性，
也不能把负差质量直接从某个最大值上界中相减。

每个 pilot 仅新建四个当前损失批次、四个正差 ordinary 包络批次，分别为
$108$ 和 $3024$ 个整数查询。结论来自普通数学比较、整数几何重建与精确有理数
检查，不是新增 Lean 核验；没有扩展到第三个实际 $\xi_7$ 或其他节点。

复现见 [数据与运行说明](../../../frontier/cover-geometry/finite-prefix-sources/missing23-xi7-transport/README.md)、
[精确运输核对](../../../frontier/cover-geometry/finite-prefix-sources/missing23-xi7-transport/verify.py)
以及同包的明确几何重建入口。

## 用完整零分量与联合改进处理两个新的素数 7 投影

仍固定 missing23 的 A1 节点 `(2,4,1,8,1,2,1,0,13)`、素数集 `(3,5,7,11,13,17,19,29)`、阈值 `(2,4,4,8,8,16)`、初始余量 `135/4` 与最终查询 16。对素数 7 投影 `Q=(2,4,2,14)`，保留整个实际零七场 `(11,11,9,6,3)/14`，正七部分不变，得到当前损失上界 `10.2215449381`，最终共同 hinge 上界约 `32.466043606804874`。这里所有比较都针对同一实际来源及 padding；放平后续场只给逐对象上界，不声称各上界同时可达。

后续五级先分别保留模 15 相位、释放其余当前头，得到 35 个上界。再只细化当前 11 的相位 `4/7/8/13` 和当前 13 的相位 `4/7/8/13/14`，共九张各含 40 个真实标签的表；当前 13 使用放平 11 的上界。后续 17、19、29 的七相位统一损失上界分别为 `3.8046758456`、`4.2792453624`、`2.0467337265`。由此无需计算后续标签的两两几何网格。

唯一需要恢复实际 11 场的组合是 `X/X`，其中 `X=(1,4,7,4)`。它的四头交集为 `{34,79,124}`；每点积分来源质量为一，Q 的重叠数均为一，完整带七权质量为 `11/14+3/14=1`。实际零 11 场在每点比放平场少 `1/11`。当前 13 的四个固定头贡献 `48/13`，故对每个合法 layout、每份非负来源深度和每个乘子 `m≥1`，阈值四以上的 padded hinge 至少为 `m+48/13−4≥9/13`。除以当前 13 的损失分母八，得到统一改进

$$
L_{13}^{\mathrm{actual}}(X,X)
\le L_{13}^{\mathrm{flat}}(X)-\frac{27}{1144}.
$$

该不等式先在完整 padded 核上逐 layout 证明，再取最大与尾项上界；正 11 部分不变。它不是两个独立最大值或尾项上界作差。在相位四中，X 在两表中均为唯一峰，严格峰差分别为 `73284861/200000000` 与 `2673800669/10000000000`。

全部 `280²=78,400` 个前两级标签对，经精确有理数检查，仅 X/X 在扣除上述改进前未过门；扣除后全部通过。余下三层各用统一上界，故覆盖 Q 下全部 `280⁵=1,721,036,800,000` 个未来标签元组，查询上界不超过 `28.9678985746<29`。逐损失向上取整至百万分之一后，最小余量为 `2.324331`，最小严格 slack 为 `0.074590`。

保持模 5、交换模 27 树中模 9 为 2 和 5 的分支，可保持全部具名来源分割、44 点实际载体与四区域权重，并将 Q 运输为 `Q′=(2,4,5,14)`。同时运输所有后续标签，得到 Q′ 的同一完整 `280⁵` 结论。这是两份完整来源之间的运输，不是 Q 内部自对称，九张表均未使用 `32+8` 替代实际 40 标签。

结果、完整输入与可重放程序见 [数据及证明说明](../../../frontier/cover-geometry/finite-prefix-sources/missing23-xi7-q/README.md) 与 [精确算术检查](../../../frontier/cover-geometry/finite-prefix-sources/missing23-xi7-q/verify.py)。算术消费者正常模式与 `-O` 模式适用；几何最大值由单独的固定输入整数枚举重放。结论属于上述固定节点、来源与阈值下的普通数学及计算证据，不计作新增 Lean 核验，也不关闭 Erdős #7 的其他节点或无界问题。

## 用普通包络统一处理 255 个素数 7 投影

固定 missing23 来源节点 $(2,4,1,8,1,2,1,0,13)$，素数为
$(3,5,7,11,13,17,19,29)$，阈值为 $(2,4,4,8,8,16)$，最终查询为
$16$，保留量为 $135/4$。每个阶段的物理标签域都是

$$
\{1,2\}\times\{1,2,3,4\}\times\{2,4,5,7,8\}
\times\{1,4,7,8,11,13,14\},
$$

共有 $280$ 项。以下两种普通包络比较，对该固定节点下的
$255$ 个首标签 $\xi_7$ 分别认证其对应来源；每个已认证首标签均允许其后
$11,13,17,19,29$ 五阶段独立取全部 $280$ 个物理标签。

对任一实际 $\xi_7$，其源胞上的零乘子质量是
$K_7(s)/14$，其中 $K_7=(11,11,9,6,3)$，而完整正乘子质量是
$9/7^m$，$m\ge2$。逐胞以 $11/14$ 代替零质量，保留原来的全部
正乘子，恰得到 $\operatorname{full}(7,2)$：总质量为 $1$，一阶矩
为 $5/4$。这在每个胞和每个乘子上同时支配全部实际首标签，不把
不同来源上的几何最优值当作共同实现。

先沿 $\operatorname{full}(7,2)$，再逐次乘入
$\operatorname{full}(11,4)$、$\operatorname{full}(13,4)$、
$\operatorname{full}(17,8)$、$\operatorname{full}(19,8)$ 与
$\operatorname{full}(29,16)$，普通包络给出的五项损失上界依次是

$$
5.6613309293,\quad6.3779676675,\quad3.9940469465,
\quad4.5013887284,\quad2.1244751754.
$$

完整第 $29$ 阶段之后的查询铰链上界是
$H_{16}=33.15651876570184\ldots$。令 $L_7$ 为实际首标签的当前
损失上界，则充分条件为

$$
D=\frac{135}{4}-L_7-\sum_{p=11,13,17,19,29}L_p>0,
\qquad14D-H_{16}>0.
$$

全表中恰有 $240$ 个首标签通过这份共同上界。

对其余首标签中的 $37$ 个，另保留实际逐胞 $K_7(s)$ 加权的
普通零分量包络 $E_{\xi_7}$。在各阶段用完整的两个分量

$$
G(t,\operatorname{POS}_7M,E_0)
+\frac1{14}G(t,M,E_{\xi_7}),
$$

其中 $M$ 依次包含所有已经经过的后续 full 因子。当前损失除以
$p-1-t$，最终查询不除；正 $7$ 分量只计一次，所有无限尾的总质量
与一阶矩仍被保留。这额外认证 $15$ 个首标签，与前述 $240$ 项
不交。因此本比较共覆盖

$$
255\cdot280^5=438\,864\,384\,000\,000
$$

份完整六标签参数。最大的显示查询上界为 $28.9315451319<29$，
出现在 $\xi_7=(2,4,8,11)$；这只是向上取整后的查询界最大值，
不据此推定精确最小存活量。

另外 $25$ 个首标签不由本包结算：其中 $3$ 项未使用实际零包络，
另 $22$ 项未通过此种普通比较。它们不构成不可实现性结论，也不影响
其他独立证书。本结果限于这一个固定来源节点，不声明全部节点或
Erdős #7 已解决。

[数据及比较说明](../../../frontier/cover-geometry/finite-prefix-sources/missing23-xi7-ordinary/README.md)
保存全 $280$
项当前损失、$37$ 份实际零包络、精确有理数 consumer 与独立几何
重建入口；来源与基准程序固定为原 `missing23-eta14` 包。
consumer 的普通与 `-O` 执行同保留结果逐字节一致，检查保持启用。
几何 producer 分别支持 `--kind current280` 与 `--kind zero37`，
默认只读取明确给出的缓存，重建不枚举五阶段未来标签网格。
这是普通数学比较及有限计算证书，不是新增 Lean 核验。

这 $255$ 个首标签与前文的 $(1,4,7,14)$、$(2,4,2,14)$、
$(2,4,5,14)$ 不交。合并这些同节点证书，已认证首标签数为 $258$，
各自均覆盖全部 $280^5$ 个后续标签元组；余下 $22$ 个首标签
由下一节的共同来源比较补齐。前文的 $P=(2,4,7,4)$ 已包含在这 $255$ 项中，
不再重复计数。

## 固定 A1 节点全部七坐标标签的完整续接

仍固定 missing23 节点 `(2,4,1,8,1,2,1,0,13)`、素数集 `(3,5,7,11,13,17,19,29)`、阈值 `(2,4,4,8,8,16)`、初始余量 `135/4` 与查询 16。对前述统一比较尚未关闭的 22 个七坐标标签，保留各自的当前七损失上界，并补齐全部 `280⁵` 个后续物理标签元组。

逐原胞核对完整 K7 分子场 `(11,11,9,6,3)` 后，这 22 个标签共有 18 种分子场；再应用保持具名来源分割、44 点载体与全部四区域权重的模 9 分支 `2↔5` 整体运输，得到 16 组比较输入。19 个成员使用同胞分子场一致，3 个成员使用该坐标运输。这里“比较输入相同”仅指后续上界实际依赖的 K7 场、固定权重、正七律与阈值相同，不声称两份实际来源或概率律相同；每个成员的当前七损失仍单独保存。发生坐标运输时，全部后续标签一并运输。

每组先保留当前模 15 相位、释放其余三个当前头，得到五级各七相位的 35 个上界；再细化 14 张当前 11 或 13 的完整 40 标签表。这已关闭其中 18 个来源。对 `(1,3,7,8)`，尚余的四对恰为 `{A,B}²`，其中 `A=(2,4,2,14)`、`B=(2,4,5,14)`。两个实际 11 场下的当前 13 上界覆盖 A/A 与 A/B，源比较输入保持不变的 `2↔5` 运输覆盖 B/B 与 B/A，四对全部通过。

最后三来源是 `(1,4,7,4)`、`(1,4,7,7)`、`(1,4,7,13)`。令 `C=(2,4,8,14)`，每个来源只余 A/A、A/B、A/C、C/A 及其同时运输的共八对。对每个代表对，保存七、十一、十三的实际零场和全部八个零/正分量，重新计算后续 17/19/29 的 21 个相位上界，以及该同一联合比较输入的最终查询分子。每源 A/B 对另细化当前 17、相位 14 的完整 40 标签表，其余相位继续使用统一上界。总共只需 12 个联合代表接口和三张联合 17 表，没有构造 `280²` 的几何网格。

全部路由保持同一来源、同一前缀选择与同一 padding；后续 full 律只是非负核上的统一放大。当前 13、后续损失和最终查询不能分别从不同前缀拼取。普通情形由分离的统一最大值覆盖；需要条件路由的四组按完整 `78,400` 个前两级标签对核对，后续三层则被统一上界覆盖。最终得到

$$
15+\frac{H_{16}}{135/4-\sum_{i=1}^{6}L_i}
\le 28.9968048292<29.
$$

每项损失与查询分子均向上取整到百万分之一后，最小严格 slack 仍为 `0.007424`。因此这 22 个来源共覆盖 `22×280⁵=37,862,809,600,000` 个后续标签元组。与前述 255 个统一来源、旧来源及 Q/Q′ 的范围合并，恰好补齐该固定 A1 节点的 280 个第一标签；各范围互不重叠，合共覆盖 $280^6=481\,890\,304\,000\,000$ 份完整六标签参数。

完整输入、精确算术消费者及固定输入整数几何重放程序见[实验包及证明说明](../../../frontier/cover-geometry/finite-prefix-sources/missing23-xi7-remaining/README.md)与[精确路由核对](../../../frontier/cover-geometry/finite-prefix-sources/missing23-xi7-remaining/verify.py)。算术检查支持正常模式与 `-O`；整数几何重建另行核对。这是上述固定有限节点与阈值内的普通数学及计算证据，不计作新增 Lean 核验，也不扩张为其他 A1 节点或无界 Erdős #7 的结论。

## 同一来源上的顶点运输与连续参数边

The all-$280^6$ certificate above also applies to the source row $z=22$ and to the declared continuous edge between rows13 and22. This uses the same fixed chart $(a,b,c,r,d,k)=(2,4,1,8,2,1)$, caps, thresholds $(2,4,4,8,8,16)$ and query16. The current result does not supply all other source-budget vertices.

The source is Schroeder, *Nine Prime Divisors in Odd Distinct Covering Systems*, edition1.0.1, Sections5 and9 and the terminal-state normalization in Section10; the [library entry](../../../../../../Library/Arith/schroeder2026nine.md) records its provenance. The inspected `paper/main.tex` has SHA256 `73f78621a297650176cb796f763b9279eae9533efedbbb58405efc885ef41bb9`. Its explicit vertex interpolation and compatible-screening arguments are reused here for the stated missing23 schedule, with the vertex inequalities supplied by the preceding packages. The original seven-core/query12 theorem and the missing19/query18 certificate do not supply missing23/query16 vertex inequalities merely by substitution.

The physical domain remains $\Xi^6$, where $\Xi=\{1,2\}\times\{1,2,3,4\}\times\{2,4,5,7,8\}\times\{1,4,7,8,11,13,14\}$. Original terminal names A1 and B1 distinguish first-seven projections at the same budget vertex, so both are included in this domain. A3 and B3 use budget column $j=3$ and are not covered on that account.

### One fixed common comparison functional

Fix one actual completed family, its source chart and six physical projections,
and fix its actual padded kernels before any complete query is supplied. The
numerical weight interpolation below evaluates upper comparisons of this fixed
construction; it does not choose a new probability or actual kernel at a vertex.

On the fixed carrier

    C={x mod135: x mod3!=0, x mod9!=1, x mod27!=4,
                 x mod5!=0, x mod15!=2, x mod45!=8},

there are44 cells. The continuous comparison parameters are

    z_h>=0, sum_h z_h=1/2,
    h in {2,5,7,8,11,13,14,16,17,20,22,23,25,26};
    t_j>=0, sum_(j=1..4)t_j=1/20, 0<=e<=t_1.

Put `B={x in C:x mod3=2,x mod5=1}` and `D_j=(1/5)1_(j=1)+t_j`.
The zero-depth factors are

    A3(x)=2/3-z_(x mod27),
    A5(x)=4/5-D_(x mod5)-(1/5-e)1_B(x).

In each of four zero/positive-depth regions use `A3*A5`, `A3`, `A5` or1,
respectively. Positive depth masses `2/3^(u+1)` and `4/5^(v+1)` do not depend on
these budgets. These are comparison weights, not indicators of an actual
survivor set. The common finite carrier is C throughout; no union or intersection
of two unrelated actual source survivor sets is used. Deeper source exclusions
and the actual kernels remain those of the single family being bounded.

For fixed physical data, outgoing charged fields are functions of the selected
incidences on each cell. They do not depend on z,t,e. Their products, including
joint zero11/zero13 factors, multiply the same cell weight. Each geometric
functional has the form

    max_l sum_x w(x) [load_(l,xi)(x)-threshold]_+,

with fixed nonnegative load coefficients and physical heads. It is a maximum of
linear functions of w and hence convex in the full vector of nonnegative
weights. Positive multiplier expectations, positive region sums and positive
omitted-depth majorants preserve convexity. The current and query comparison
functions S_xi(w)=sum_p L_p(w) and H_xi(w)=H16(w) may therefore be defined from
one finest positive comparison, so that

    G_xi(w)=14*S_xi(w)+H_xi(w)

is convex. This assertion concerns the positive definition, not an arbitrary
subtraction of upper bounds. Different numerical routes may dominate this same
G at different vertices; their pointwise minimum need not be convex.

The source's first-hit and query comparison then give, for the one actual law,

    D=R-S_xi(w),        135*mu(1)>=D,
    135*integral (Q-16)_+ dmu <= H_xi(w)   for every complete query Q>=1.

Thus `D>0` and `14D-H_xi(w)>0` imply that its normalized complete-query readout
is at most `15+H_xi(w)/D<29`. Proving these domination statements for the fixed
construction is indispensable: abstract convexity alone does not supply them.

### The minimal vertex-extension lemma

Let V be a finite joint vertex set. For each permitted parameter theta suppose
there are common coefficients `lambda_v(theta)>=0`, summing to1, such that

    w(theta)=sum_v lambda_v w_v,      R(theta)=sum_v lambda_v R_v.

For every fixed physical tuple xi assume S_xi and H_xi are nonnegative convex
functions on the common weight vectors and give the fixed-law domination above.
For every v and xi, a numerical route may supply bounds

    S_xi(w_v)<=s_(v,xi),       H_xi(w_v)<=h_(v,xi),
    d_(v,xi)=R_v-s_(v,xi)>0,
    delta_(v,xi)=14*d_(v,xi)-h_(v,xi)>0.

Then, without changing the law, caps, threshold or physical tuple,

    D(theta)>=sum_v lambda_v d_(v,xi)>0,
    14D(theta)-H_xi(w(theta))>=sum_v lambda_v delta_(v,xi)>0.

Proof: apply convexity separately to S and H and subtract their upper bounds
from the affine reserve. Finite V and finite Xi^6 allow uniform minima if every
pair has certified strict inequalities. Alternatively a direct upper estimate
`G_xi(w_v)<=g_(v,xi)<14R_v` suffices for the slack; H>=0 then implies
`D>0`. In particular a uniform slack delta gives `D>=delta/14>0`.

The route may depend on `(v,xi)`; there is no requirement to use one numerical
route on all vertices. A fixed finite list of routes is sufficient exactly
when it covers all required vertex/physical tuples and every chosen route
bounds this same finest common functional. Coverage of different actual laws,
different thresholds or different caps does not meet the lemma's premise.

If a uniform numerical query bound q0>=15 is wanted, interpolate
`H+(q0-15)S <= (q0-15)R`, not the ratios H/D. This positive convex combination
also yields `H(theta)/D(theta)<=q0-15` when the endpoint D bounds are positive.

### Joint budget coefficients and what is still missing

The pure-5/overlap vertices are `(j,i)=(1,0),(2,0),(3,0),(4,0),(1,1)`.
The fourteen pure-3 vertices have `z_h=1/2` at one row h. Their70 joint weights
are interpolated by

    lambda_(h,j,0)=40*z_h*(t_j-e*1_(j=1)),
    lambda_(h,1,1)=40*z_h*e.

They are nonnegative, sum to1, and give the same interpolation for all four
region weight vectors and for the reserve

    gamma15=sum_(h mod3=2) z_h,
    gamma45=sum_(h mod9=8) z_h,
    B_eff=sum_(x in B)(1-z_(x mod27)),
    R=135/4+gamma15+(9-gamma15)D_2
      +gamma45+(3-gamma45)D_3+9/5-B_eff*(1/5-e).

Multiplying the two simplex decompositions proves these identities. Weights
and R are separately affine in z and (t,e), not jointly affine in their raw
concatenated coordinates. The joint70-vertex lift is the relevant convex
representation. The lemma is a reuse of source Section9, not new Lean content.

For this fixed chart, finite prefix-tree automorphisms preserving the named
anchor cylinders give the following row orbits:

    {13,22}, {7,16,25}, {2,5,11,14,20,23}, {8,17,26}.

Generators swap sibling leaves in each displayed mod9 branch and swap the
whole mod9 branches2 and5. They fix the mod3 and mod5 coordinates, the removed
27-row4 and the removed45 cylinder8, and transport every labelled physical
projection. With the source parameter transported as `(sigma z)_(sigma h)=z_h`,
each region satisfies `w_(sigma z,t,e)(sigma x)=w_(z,t,e)(x)`, and the reserve
is unchanged. These identities compare transported source vertices. The
standalone check verifies these statements for all70 vertices. Thus20
representatives (four row orbits times five pure-5/overlap vertices) suffice
under this verified symmetry reduction. The present certificate supplies one
such representative: row orbit{13,22}, `(j,i)=(1,0)`. The other19 representative
inequalities are not supplied by the present certificate. This is an explicit
proof-obligation list, not a proof that19 new enumerations are necessary;
uniform dominating screens or further proved relations may discharge several.

For the canonical coarse triple `(2,4,1)` there are also eight r representatives
`{4,7,8,11,16,22,31,34}` and seven allowed `(d,k)` pairs, hence56 discrete mixed
charts. Before symmetry, their fully refined product domain has `56*5*14=3920`
vertex descriptions. The original source's screens and the missing-19 screens
do not certify this whole domain for the changed missing-23 schedule/query16.
Other coarse triples must also either be uniformly screened in the changed
schedule or separately treated. No new geometry for any of these was run here.

### Free extension from z13 to z22 and their entire edge

Define sigma27 to exchange13 and22 and fix the other25 residues modulo27.
For all h>=3 extend it by

    sigma_(3^h)(x)=sigma27(x mod27)+27*floor(x/27) (mod 3^h).

Below depth3 use its induced prefix maps; here they are identity modulo3 and9.
Leave the 5-adic and all other prime coordinates unchanged. These compatible
finite bijections are measure-preserving prefix-tree automorphisms. Every
prime-power cylinder at every finite height maps to one cylinder of the same
height. Their CRT product therefore transports every queried numerical
modulus, original label identity and phase together. It fixes45 residues,
permutes27 leaves and135 cells, and transports arbitrary higher query labels;
it is not merely a symmetry of the four physical incidence counts.

The map fixes C and the chosen anchor/reference data. It sends the source
weight vertex z13 to z22, preserves every current and query geometric domain,
and fixes each physical xi coordinate modulo3,5,9,15 individually. Explicitly,
for every region rho and cell x in C,

    w_(22,rho)(sigma(x))=w_(13,rho)(x).

This transports two different endpoint weight fields; it does not assert that
sigma preserves the z13 weight field internally. Thus the
existing all-Xi^6 inequalities transport to z22 with exactly the same bounds,
without a new geometry computation. Actual kernels may be conjugated under
the map for the transport proof. During the subsequent interpolation they
remain those of the actual family, as stipulated above; endpoint weights are
not independently chosen actual laws.

For 0<=u<=1 take

    z13=u/2, z22=(1-u)/2, all other z_h=0,
    t1=1/20, t2=t3=t4=0, e=0.

The common C still has44 cells. Explicitly,

    A3^u(x)=2/3-(u/2)1_(x mod27=13)-((1-u)/2)1_(x mod27=22),
    A5(x)=4/5-(1/4)1_(x mod5=1)-(1/5)1_B(x).

Every region weight equals `u*w13+(1-u)*w22`. The reserve is identically
`R=135/4`: gamma15=gamma45=0 and `B_eff=9`. Apply the common-functional lemma
with the two endpoints. Every actual completed family whose budgets lie on
this edge satisfies both `D>0` and `14D-H16>0`, uniformly over Xi^6 and all
complete query layouts. The claim concerns actual families satisfying those
budgets; it does not assert that every relaxed edge point is realized by a
completed family. It neither expands the discrete chart nor changes t/e.

Every certified endpoint slack is inherited along the entire edge for its
physical tuple. Finiteness of Xi^6 and the certified route partition gives a
strictly positive uniform minimum, without computing or displaying its value.
The7424-millionth minimum belongs to the remaining22 subcertificate. By
itself it does not give a lower bound for the whole280-source domain. The later
positive-weight neighborhood proof explicitly aggregates all certificate
parts and verifies that the same number is a safe uniform lower bound; it is
not asserted to be the exact minimum of the actual slack. The inherited
strict inequalities already prove `<29`.

### Finite obstructions to unjustified extensions

1. One successful vertex does not certify a simplex. On theta in[0,1], let
   `R=1,H=0`. Both `S_good(theta)=0` and `S_bad(theta)=2*theta` are nonnegative
   affine functions and have identical certified data at theta0. The latter
   has D=0 at1/2 and D=-1 at1. No information confined to theta0 decides this.
2. Choosing different actual models at different vertices is invalid. With
   `S1=2*theta,S2=2*(1-theta),R=1,H=0`, each endpoint has a successful model,
   but at1/2 both have D=0. The minimum of the two affine costs is not convex.
   This is not a counterexample to compatible routes bounding one convex G.
3. Separate affinity is not joint affinity. `W(u,v)=uv` is zero at(0,1) and
   (1,0), but is1/4 at their midpoint. One needs the joint product vertices,
   not an arbitrary diagonal pair in raw budget coordinates.
4. Normalized ratios cannot be averaged as convex functions: endpoint pairs
   `(D,H)=(3,2),(1,0)` give mean ratio1/3, but midpoint ratio1/2. Interpolate
   the unnormalized common slack, or the fixed-q0 inequality above.

### Reproducibility and scope

The [finite structural checker](../../../frontier/cover-geometry/finite-prefix-sources/missing23-source-vertices/verify.py) and its [exact results](../../../frontier/cover-geometry/finite-prefix-sources/missing23-source-vertices/result.json) verify the ten prefix generators, all70 source-budget vertices under these maps, the280 physical labels, reserve identities, and exact examples of the joint interpolation and continuous edge. The general interpolation and arbitrary-height transport follow from the formulas above. Finite samples do not prove the whole continuous domain.

The program reads only the adjacent pinned source model and writes stdout. Run `python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/finite-prefix-sources/missing23-source-vertices/verify.py`. Its ordinary and optimized outputs agree. No geometric maximum is newly computed, no new Lean statement is added, and no all-missing23 or unrestricted Erdős #7 conclusion is asserted.

## A complete query obstructs universal transport to the next row orbit

Keep the same chart, `t1=1/20`, the other t coordinates zero, and `e=0`.
The closed edge has `z13=u/2,z22=(1-u)/2`, with `0<=u<=1`; the next row
orbit has representative `z7=1/2`. Both have reserve135/4 and equal total
comparison mass. Equal total mass does not imply domination of the permitted
queries. In particular, the following obstruction rules out a universal
fixed-query transport, while leaving comparison of the full maximum G16 open.

In ternary root1 the retained branches modulo9 are branch4, with leaves13,22
and removed leaf4, and branch7, with leaves7,16,25. Their zero-extra-depth
weights are `2/3-z_h` on retained leaves:

| Source | Branch4 mass | Branch7 mass |
| --- | ---: | ---: |
| Any point on the closed13/22 edge | 5/6 | 2 |
| Row7 vertex | 4/3 | 3/2 |

These numbers omit the common quinary factor. After summing the positive
ternary depths, the full retained weight in a leaf is `1-z_h`. The branch
masses then become `(3/2,3)` on the closed edge and `(2,5/2)` at row7.
The zero-depth masses alone must not be used to evaluate a finite cylinder
query on the whole comparison submeasure.

Define nu to be Haar measure restricted by the completed pure3 and pure5
families and by the selected15,45,75 anchors. This selected-anchor comparison
submeasure precedes the7,11,13,17,19,29 deletion kernels; it is not the final
live law, and other mixed constraints are not imposed here.

Take `K=27*5^8=10546875` and one query phase for each of its36 divisors
`3^e*5^f`, with `0<=e<=3`, `0<=f<=8`, including the unit divisor. The
quinary phase is2 modulo5^f. The ternary phase is4 modulo9 when e=2, and0
modulo3^e otherwise, with no restriction when e=0. CRT combines these into
one phase per numerical divisor. They are legal complete-query phases and do
not replace the original covering phases.

On the common carrier C, the e=1 and e=3 terms vanish. Put

    M(x5)=sum_(f=0..8) 1_(x5=2 mod5^f),       1<=M<=9.

The exact load and hinge are

    Q(x)=M(x5)*(1+1_(x3=4 mod9)),
    (Q(x)-16)_+=2*1_(x3=4 mod9)*1_(x5=2 mod5^8).

Indeed M=9 precisely on the displayed deepest5-cylinder, and otherwise the
load is at most16. The pure5 tail and selected75 hole lie in column1; column2
is retained. The selected15,45,75 holes all lie in ternary root2, so none
meets the root1 support of this hinge. The full retained branch4 masses give

    integral (Q-16)_+ dnu_edge = 3/K,
    integral (Q-16)_+ dnu_7    = 4/K.

Thus one legal complete query at the target threshold has strictly larger
readout at row7 than at every point on the certified edge. This does not
compare the maxima over all queries: the closed edge has more mass in
branch7, where a different query can have a larger readout. Nor does it
evaluate the final G16, which also contains all current losses and later
charged fields. It excludes the universal fixed-query domination that would
otherwise have been used to transfer the source certificate without an
additional argument.

### The excluded positive transports

Every tree automorphism preserving the named anchor leaf4 also preserves its
parent branch4. A convex mixture of these automorphisms cannot increase its
zero-depth mass from5/6 to4/3. Even if the removed leaf were initially allowed
to move, the unique zero leaf and positivity force each automorphism in an
exact mixture to put it back at4, with the same obstruction.

A broader, explicitly restricted matrix class fails too. On the six leaves
`(4,13,22,7,16,25)` at one fixed quinary coordinate, suppose P is nonnegative,
has column sums1 and row sums at most1, and its pullback of the branch4
indicator is constant on each source9 branch. The row-sum bound expresses
that a27-leaf query pulls back to a subconvex combination of27-leaf queries;
the last condition retains the9-cylinder type without splitting its leaves.

Since P is square, all its row sums equal1. Let a be any closed-edge weight
vector and b the row7 vector, both using the zero-depth weights above. If
`b=P*a`, the unique zero of a and `b_4=0` force `P_(4,4)=1`. Consequently
`P^T*1_branch4` is1 at source leaf4 and hence, by the branch-constancy
condition, on all three leaves of its branch. Its total is3 by the row sums,
so nonnegativity makes it zero on the other branch. Therefore

    sum_branch4 b = sum_branch4 a = 5/6,

contradicting the target mass4/3. A pointwise bound `b<=P*a` also fails: the
total masses agree, so mass preservation would force equality. These are
conditions on this proposed transport class, not necessary conditions on all
possible proofs about G16. In particular, an estimate using the actual joint
loss/query coefficients may still work without such a source transport.

The [exact complete-query check](../../../frontier/cover-geometry/finite-prefix-sources/missing23-source-vertices/verify-row7.py)
and [rational results](../../../frontier/cover-geometry/finite-prefix-sources/missing23-source-vertices/row7.json)
check the36 CRT labels, all18 combinations of M and branch membership, the
branch masses, and the strict integral difference1/K. The program writes only
stdout and reads no external files. Its ordinary and optimized outputs agree.
No geometry is evaluated. The general identities and matrix obstruction are
proved above; neither a new source vertex nor a new Lean result is claimed.

## An explicit continuous neighborhood from positive weight domination

The fixed chart now has a certified region beyond the13/22 edge: from any
point of that edge toward any permitted continuous budget of the same chart,
raw-parameter interpolation by any fraction at most `1/50000` preserves the
strict query bound29 for all `280^6` physical tuples. This conclusion reuses
the existing complete-tail estimates; it does not evaluate a new geometry or
close a full additional source vertex.

### Aggregating a common strict margin

The first-label partition is the disjoint union of ordinary255, the old
source `(1,4,7,14)`, Q/Q′, and remaining22. Within the old source, its four
disjoint prefix domains have1600,3200,6400 and67200 pairs, totaling280².
Their retained lower bounds for `14D-H16` are:

| Certified domain | Uniform lower bound for the slack |
| --- | ---: |
| Ordinary255 | greater than0.16291984 |
| Old source, eta11=eta13=14 | 0.091827 |
| Old source, eta11 in1,4 and eta13=14 | 0.187251 |
| Old source, eta11 in7,8,11,13 and eta13=14 | 0.115893 |
| Old source, eta13 different from14 | 0.839287 |
| Q/Q′ | 0.074590 |
| Remaining22 | 0.007424 |

The ordinary255 entry is recomputed from each retained current7 bound, its
declared continuation route and its full query bound; it is not inferred from
the largest rounded query ratio. For the other entries, the previously checked
millionth-rounded route certificates already give the displayed lower bounds.
Their geometry inputs and proofs retain their earlier verification scope.

Consequently

    delta0=7424/1000000=116/15625,
    R0=135/4,
    G_xi(w_edge)<=14R0-delta0=14765393/31250

hold uniformly over the whole physical domain and the entire certified edge.
Here delta0 is a safe common lower bound obtained by aggregating all the
certificate domains. It is not the exact minimum of the actual slack, nor of
all possible sharper numerical routes. The edge extension uses the already
proved transport and common-functional convexity.

### Order and scaling of the common positive functional

For one fixed actual construction, physical tuple and all declared interfaces,
the finest common positive functional has nonnegative layout coefficients:

    sum_x w(x)*c_(layout,x),        c_(layout,x)>=0.

Maximizing over a fixed layout family, adding positive stage contributions and
integrating the complete positive multiplier laws preserve monotonicity and
positive homogeneity. Hence the same `G_xi=14*S_xi+H_xi` used in the edge
proof satisfies

    w<=v  =>  G_xi(w)<=G_xi(v),
    G_xi(c*w)=c*G_xi(w)             for c>=0.

The ordered weight vector contains all four zero/positive-depth source regions.
Their complete tail measures are held fixed. No bounded-payoff approximation
or tail cutoff is required. These properties concern this positive defining
functional, not a minimum of route formulas or the subtraction of two upper
bounds. A route using a negative credit remains usable only through its
existing proof that it bounds the same positive functional.

### A reference point on the closed edge for every legal budget

Let theta=(z,t,e) be any allowed continuous budget in the fixed chart:

    z_h>=0, sum_h z_h=1/2,
    t_j>=0, sum_(j=1..4)t_j=1/20,       0<=e<=t1.

Write s=z13+z22 and set

    rho3=(8-6s)/5,
    zbar_h=2/3-(2/3-z_h)/rho3          for h=13,22,
    zbar_h=0                          otherwise.

Since `0<=s<=1/2`, one has `1<=rho3<=8/5`. The two nonzero reference
coordinates satisfy

    zbar_h-z_h=(2/3-z_h)*(1-1/rho3)>=0,
    zbar13+zbar22=4/3-(4/3-s)/rho3=1/2.

Thus zbar lies on the already certified edge. On those two rows the ratio of
the target zero-depth ternary factor to its reference factor equals rho3;
on every other retained row that ratio is at most1.

The reference quinary budget is `t0=(1/20,0,0,0), e0=0`. Its zero-depth
column1 factors are11/20 in ternary root1 and7/20 in ternary root2. The
corresponding target/reference ratios are

    A=(12-20t1)/11,
    B=(8-20t1+20e)/7.

Both are at least1. In the other columns the target factors only decrease.
The ternary increase can occur only on the two edge rows in root1. Therefore
all four source regions satisfy the simultaneous pointwise bound

    w(theta)<=rho(theta)*w(zbar,t0,0),
    rho(theta)=max(rho3*A,B).

This is also the exact maximum of these finite region-weight ratios: the
first term is attained at an edge row in root1/column1, and the second in
the positive-extra3 region at root2/column1. All reference weights are
strictly positive on the common carrier. This statement is about comparison
weights; it does not assert that each relaxed budget has an actual realizing
cover or that different actual kernels have been identified.

For `ga=sum_(h mod3=2)z_h` and `gr=sum_(h mod9=8)z_h`, the source reserve is

    R(theta)=R0+(6/5)*ga+(9-ga)*t2+gr+(3-gr)*t3+(9-ga)*e >= R0.

Indeed `B_eff=9-ga`, `D2=t2` and `D3=t3` in the earlier reserve formula.
Every additional term is nonnegative because `0<=ga,gr<=1/2`.

Monotonicity, scaling and the edge certificate now give the explicit
sufficient condition

    14R(theta)-rho(theta)*(14R0-delta0)>0.

Whenever it holds, `14D-H16>0` for every physical tuple. Since `H16>=0`,
it also gives `D>0`, so the actual complete-query readout remains below29.
This condition defines a relative open region containing the entire closed
edge, because the displayed expression is continuous and equals delta0 on
that edge.

### A uniform rational radius in raw parameter coordinates

Take any edge point thetaE and any permitted target thetaV in this chart.
For `0<=tau<=1`, interpolate their raw parameters:

    theta_tau=(1-tau)*thetaE+tau*thetaV.

This stays in the legal budget domain, including `e<=t1`. No joint affinity
of the weights is assumed. Instead, the explicit ratios imply

    rho3(theta_tau)<=1+3*tau/5,
    A(theta_tau)<=1+tau/11,
    B(theta_tau)<=1+tau/7.

For the last inequality use `eV<=t1V`. Also

    1+tau/7 <= (1+3*tau/5)*(1+tau/11)

for every nonnegative tau. Thus, uniformly in both endpoints,

    rho(theta_tau)<=(1+3*tau/5)*(1+tau/11).

At `tau0=1/50000`, the right side is `137501900003/137500000000` and

    14R0-rho_bound(tau0)*(14R0-delta0)
      =3845709003821/4296875000000000
      >0.000895001368.

The weight-multiplier bound increases with tau, so this positive slack lower bound holds for
all `0<=tau<=tau0`. This proves the claimed uniform neighborhood, including
simultaneous changes in the pure3, pure5 and overlap budgets. The fraction is
a radius in the stated interpolation, not an absolute Euclidean or TV radius.

The factor is allowed to exceed1 and is paid for by the existing strict
margin. Accordingly, the earlier row7 fixed-query obstruction does not
contradict this result. At the full row7 vertex the factor is8/5, and this
argument does not pay for that increase. Other discrete charts, the19
remaining joint representatives and unrestricted Erdős #7 remain unresolved.

The [portable exact checker](../../../frontier/cover-geometry/finite-prefix-sources/missing23-source-vertices/verify-tube.py)
and [results](../../../frontier/cover-geometry/finite-prefix-sources/missing23-source-vertices/tube.json)
pin the seven prior coverage files, check the complete first-label partition,
aggregate the lower margins, and check840 rational parameter cases with147840
cell/region comparisons. The continuous result follows from the formulas
above, not from the finite samples. The checker writes only stdout and reads
explicit adjacent project inputs. Normal and optimized modes agree; no new
geometry or Lean verification is claimed.

## Finite pure-power prefixes absorb arbitrary higher tails

The continuous neighborhood has a finite sufficient membership test. In the
same fixed chart,17 additional low-height pure-power phase conditions ensure
that every legally completed higher tail satisfies the query bound29. This
does not place an arbitrary odd cover in this subclass; the other prefix
patterns and discrete charts still require separate arguments.

### Budget coordinates are actual deletion masses

Use the same source definitions from Section5 of the cited paper. Completion
has one class at each pure-power height, and the pure classes for each prime
are disjoint. Write their phases as `a_(3^n)` and `a_(5^n)`. The selected
low classes are0 modulo3,1 modulo9,4 modulo27 and0 modulo5. The selected25
class and the selected75 quinary child are distinct children in column1.
Let `c75` be that actual75 phase modulo25, with its ternary root fixed at2.

The budget coordinates therefore have the exact sums

    z_h=sum_(n>=4) (27/3^n)*1_(a_(3^n) mod27=h),
    t_j=sum_(n>=3) (5/5^n)*1_(a_(5^n) mod5=j),
    e=sum_(n>=3) (5/5^n)*1_(a_(5^n) mod25=c75).

Each higher cylinder lies wholly in one of the displayed prefix classes.
In particular e is an overlap from this same completed source, measured in
the same column units as t1. It cannot be chosen independently afterward.

Put

    bad3=1-2*(z13+z22),
    bad5=1-20*(t1-e)=20*(sum_(j!=1)t_j+e).

Both lie in `[0,1]` and vanish on the certified edge. For `0<=tau<=1`, a
legal budget theta lies in

    (1-tau)*{certified edge}+tau*{legal continuous budget domain}

if and only if `max(bad3,bad5)<=tau`.

Necessity follows because both functions are affine and at most1 on the
domain. For sufficiency when `0<tau<1`, set `s=z13+z22>0` and choose an
edge point with ternary coordinates `(z13,z22)/(2s)`. Subtract `(1-tau)`
times this edge point and divide the remainder by tau. The ternary residual
is nonnegative precisely when `2s>=1-tau` and sums to1/2. The quinary
residual has

    tV1=(t1-(1-tau)/20)/tau,
    tVj=t_j/tau (j!=1),        eV=e/tau.

It sums to1/20, and `0<=eV<=tV1` follows precisely from `bad5<=tau`.
At tau=0 the hypotheses say theta itself is on the edge; at tau=1 every
legal theta is allowed. This includes the case s=0. The edge point in this
decomposition is an interpolation witness, distinct from the earlier zbar
chosen to optimize the weight ratio.

### The same tail must pay for both quinary alternatives

For integers `H3>=3,H5>=2`, impose the following prefix conditions:

* For `4<=n<=H3`, the actual completed3^n phase modulo27 lies in `{13,22}`.
* For `3<=n<=H5`, the actual completed5^n phase lies in column1 and its
  phase modulo25 differs from c75.

Every off-edge ternary deletion then has height above H3. Hence

    bad3 <= 2*sum_(n>H3) 27/3^n = 3^(3-H3)=alpha.

A quinary deletion contributing to bad5 either lies outside column1 or lies
inside c75, which is in column1. These alternatives are disjoint for the
same actual cylinder. All such cylinders have height above H5, so

    bad5 <= 20*sum_(n>H5) 5/5^n = 5^(2-H5)=beta.

There is one tail budget here, not two independent copies. Arbitrarily
large later heights and arbitrary legal later phases are included by the
infinite geometric sums.

The previous exact weight bound now implies

    rho <= max((1+3*alpha/5)*(1+beta/11), 1+beta/7).

Indeed `rho3=1+3*bad3/5`, while `A<=1+bad5/11` and `B=1+bad5/7`.
With `R>=R0` and `M0=14R0-delta0`, a sufficient uniform slack is

    delta_prefix=14R0-M0*max((1+3*alpha/5)*(1+beta/11),1+beta/7).

Two explicit choices give:

| H3 | H5 | Additional phase conditions | Certified slack lower bound |
| ---: | ---: | ---: | --- |
| 13 | 9 | 17 | `5479330098137/2642980957031250 > 0.00207316` |
| 14 | 8 | 17 | `1625223077149/528596191406250 > 0.00307460` |

For13/9 one also has `bad3<=1/59049` and `bad5<=1/78125`, both less than
the uniform raw radius1/50000. The direct ratio calculation gives the stronger
displayed margin. The14/8 choice uses the general sufficient region even
though its quinary tail exceeds that uniform radius. In each case all
`280^6` physical tuples, the same fixed source construction and all complete
query tails remain covered.

As a negative control,13/8 gives only
`-22218238121/176198730468750` from this lower screen. That does not prove
an actual failure, a query counterexample, or the necessity of17 conditions;
it only means this particular worst-case tail bound gives no certificate.

### The prefix hypotheses have legal realizations

For all n>=4, choose pure3 phases

    a_(3^n)=13+27*3^(n-4) mod3^n.

They retain row13. At two distinct heights the first added nonzero ternary
digit occurs in different positions, so the residues disagree modulo the
smaller modulus and the cylinders are disjoint. They also avoid all three
selected lower pure3 classes.

Choose a third25 child gamma in column1, different from both the selected25
child and c75, and set for all n>=3

    a_(5^n)=gamma+25*5^(n-3) mod5^n.

The same first-nonzero-digit argument gives disjoint pure5 cylinders. They
remain in column1 and avoid the selected25 class and the75 child. Such a
gamma exists because column1 has five children and only two were excluded.
A concrete choice has selected25 phase1, c75=6, gamma=11, and selected mixed
phases2 modulo15,8 modulo45,56 modulo75. The latter has ternary root2 and
quinary child6; each selected mixed class avoids its selected proper-divisor
classes.

This proves consistency of the source-prefix hypotheses with an infinite
completion. It is not a construction of an odd distinct cover, and it does
not allow phases from a prescribed hypothetical cover to be changed. A use
against such a cover must establish these conditions for its actual
completed source or handle the complementary prefix cases.

The [exact prefix checker](../../../frontier/cover-geometry/finite-prefix-sources/missing23-source-vertices/verify-prefix.py)
and [results](../../../frontier/cover-geometry/finite-prefix-sources/missing23-source-vertices/prefix.json)
reuse the pinned common-margin result, evaluate the rational infinite-tail
bounds, check finite phase legality, and include the13/8 negative screen.
The all-height conclusions follow from the displayed geometric series and
disjointness arguments. No new geometry or Lean verification is claimed.
