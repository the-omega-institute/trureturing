# The joint five-prime source gives a weighted completion margin at parent 17

For arbitrary original phases and finite heights on any core supported on at most five odd primes, the existing conditional-measure construction and prefix transport supply one complete-survivor probability whose nonunit cylinder sum is at most

\[
 C_5={27050781250\over1812390307}<15.
 \tag{JC1}
\]

Consequently every distinguished prime \(r\ge17\) outside that core admits an actual core set of Haar mass greater than \(1/20000\) on which the original \(r\)-weighted completion load is at most \(159/10\), with margin at least \(3/80\) below the whole-cover threshold. This is uniform in all original finite heights and arbitrary phase choices. It extends the weighted completion interface to a five-prime core; the existing seven- and eight-prime results already imply stronger bare noncoverage ranges.

The deduction consumes the ordinary source construction and exact vertex bounds of [Chapter30](../../problem-details/30-six-prime-prefix-measures-close-all-six-vertex-blocks.md) and the parameterized comparison in [Chapter31](../../problem-details/31-seven-vertex-block-noncoverage-with-actual-prime-measures.md), (SV16)–(SV24). Those chapters attribute the construction to Michael Schroeder's *Nine Prime Divisors in Odd Distinct Covering Systems*, edition 1.0.1. Its source identity and local verification boundary remain those in the [library entry](../../../../../Library/Arith/schroeder2026nine.md). No new Lean certification or unrestricted Erdős #7 result is claimed.

## The same five-prime measure before and after deletion

First work on the reference core \(\{3,5,7,11,13\}\), with period \(K\) resolving all core exponents in the complete original family and later queries. Apply the existing source construction to its actual core-only family, stopping after 13. The initial anchor submeasure is Haar restricted to the complete anchor avoid-set on the 3- and 5-coordinates. The later normalized conditional kernels at 7, 11 and 13 have respective complete-coordinate Haar caps

\[
 C_7=3/2,\qquad C_{11}=5/3,\qquad C_{13}=3/2.
 \tag{JC2}
\]

The source's auxiliary completion may add classes or change selected auxiliary residues while preserving inclusion of the original covered set. Thus the final surviving submeasure avoids every actual original class. The original classes and phases tested in the completion load below are retained unchanged. Auxiliary completion is not a licence to replace a query by its completed residue.

Keep the normalized kernels on the full history space, including histories that will be deleted. They define one predeletion measure \(\sigma\). Let \(\mu_5\le\sigma\) be its restriction to the source's complete surviving set. This is the same sequential construction as first-hit deletion: a later normalized kernel preserves the complete earlier marginal, and all forbidden events can be deleted from the common final law. The initial anchor mass is \(m_0=\sigma(1)\); it need not equal a source lower bound.

For each basic anchor parameter, write \(\mathsf R\) for the existing reserve lower bound in units of \(1/135\), \(\Delta=L_7+L_{11}+L_{13}\) for the sum of its three upper deletion costs, and \(W\) for its complete linear anchor-load upper bound in the same units. The source supplies

\[
 m_0\ge\mathsf R/135,\qquad
 \mu_5(1)\ge(\mathsf R-\Delta)/135.
 \tag{JC3}
\]

All three losses and \(W\) use the same anchor parameter. The three conditional cap factors give the complete nonanchor first-moment multiplier

\[
 M=\prod_{q=7,11,13}\left(1+{C_q\over q-1}\right)
   ={5\over4}{7\over6}{9\over8}={105\over64}.
 \tag{JC4}
\]

For any full test layout, with one independently chosen phase for each original core divisor including 1, reverse integration of the queried later coordinates bounds its predeletion mean by

\[
 \sigma(L)\le MW/135.
 \tag{JC5}
\]

One way to see this directly is to group the test divisors by their complete 7-, 11- and 13-exponents. Each group has its own permitted anchor layout, bounded by the same \(W\); conditional cylinder caps contribute \(C_q q^{-e_q}\) only at queried positive exponents. Their complete geometric sums are (JC4). This requires no independence of the actual coordinates.

The unit divisor makes \(L\ge1\) pointwise. Hence

\[
 \mu_5(L-1)\le\sigma(L-1)
 =\sigma(L)-m_0
 \le{MW-\mathsf R\over135}.
 \tag{JC6}
\]

The subtracted mass is the initial mass of this same predeletion measure. It is not a loss estimate or a separately chosen survivor probability. On normalizing \(\widehat\mu_5=\mu_5/\mu_5(1)\), equations (JC3) and (JC6) give

\[
 \widehat\mu_5(L-1)
 \le {MW-\mathsf R\over\mathsf R-\Delta}.
 \tag{JC7}
\]

At a fixed finite period, choose a maximizing phase separately for every nonunit divisor; these choices coexist in one complete layout. Therefore (JC7) bounds

\[
 R(\widehat\mu_5)=
 \sum_{1<d\mid K}\max_a\widehat\mu_5(a\bmod d).
 \tag{JC8}
\]

The source may be constructed on complete prime-adic coordinates and then projected to all finite heights resolving the original family and every later query. Projection preserves the mass, Haar cap and relevant cylinder probabilities. No truncated-state lift is assumed.

## The anchor first moment and the joint vertex calculation

Chapter31 (SV18) writes the deeper pure-5 deletion by root as

\[
 D_h={1\over5}\mathbf1_{h=c}+u_h,
 \qquad u_h\ge0,\qquad\sum_{h=1}^4u_h={1\over20}.
\]

The discrete parameters are \(a\in\{1,2\}\), \(b\in\{2,4\}\), and \(c\in\{a,3-a\}\). The four simplex vertices \(u=(1/20)e_j\) give the same 32 basic vertices used in the existing source certificate. The reserve is its (SV19), and \(W\) is the complete first moment \(\mathcal A[\Lambda]\) in (SV22)–(SV24), evaluated by the existing `linear_sum` formula. No new hinge geometry is required.

There is also a direct interpretation of this linear bound. For root \(h\in\{1,2,3,4\}\), let \(A_h\subset\mathbb Z/27\mathbb Z\) avoid the normalized shallow pure-3 classes and the completed normalized 15-class in that column, and put \(\delta_h=(1-D_h)/5\). For \(0\le a_3\le3\), count the allowed cells of \(A_h\) in each prefix modulo \(3^{a_3}\). Their weighted column sums bound queries with 5-exponent zero; their largest single weighted column bounds exponent one. At 5-exponent at least two use its literal cylinder mass bound \(5^{-e}\). Deeper 3-prefixes use \(3^{-e}\). Summing the two exact tails

\[
 \sum_{e\ge4}3^{-e}=1/54,\qquad
 \sum_{e\ge2}5^{-e}=1/20
\]

gives the same \(W/135\). Thus this is a complete all-height cylinder sum, not a finite-height sample. Ignoring further forbidden sets only enlarges its upper bound.

Crucially, the vertex argument checks the combined inequality

\[
 C_5(\mathsf R-\Delta)-(MW-\mathsf R)\ge0.
 \tag{JC9}
\]

Here \(\mathsf R\) is affine in the common \(u\), while \(W\) and every unrounded deletion-cost upper function are convex. The left side is therefore concave. Its nonnegativity at each vertex proves it throughout the simplex. Upward-rounded vertex losses remain safe in (JC9). This does not combine a minimum reserve with a maximum first moment attained at a different vertex.

The exact maximum of (JC7) over the 32 certified vertices is (JC1). It occurs at \((a,b,c)=(2,4,1)\), \(j\in\{1,3,4\}\), where

\[
 W={239\over2},\qquad \mathsf R={135\over4},\qquad
 \Delta={11437829079\over500000000}.
 \tag{JC10}
\]

The same rows give

\[
 \mu_5(1)\ge m_5={1812390307\over22500000000}>0.
 \tag{JC11}
\]

The predeletion joint Haar cap is the product in (JC2), namely \(15/4\); subsequent deletion only decreases density. Thus

\[
 \widehat\mu_5\le\Lambda_5\lambda,\qquad
 \Lambda_5={15/4\over m_5}
 ={84375000000\over1812390307}.
 \tag{JC12}
\]

The normalized first-moment bound and density cap apply to the same probability. Neither assertion treats the normalized survivor law as a product law or claims it is uniform on all actual survivors.

## Transport to any five actual odd primes

Let the actual core primes be \(q_1<\cdots<q_5\), and put \((p_1,\ldots,p_5)=(3,5,7,11,13)\). Then \(q_i\ge p_i\). Use the finite random prefix injections already employed in Chapter30, Section 3, and Chapter33, Section 2. At each digit of coordinate \(i\), choose an independent uniform additive shift modulo \(q_i\) and inject the source digits \(0,\ldots,p_i-1\) into their shifted target positions. Their product is an injection \(F:X_{\rm source}\to X_{\rm actual}\) preserving all prefix lengths. Resolve every original coordinate height; pad the first two source and target heights to at least three and two when needed for the source anchor calculation, then project back after the construction.

Pull back the actual core forbidden family by \(F\). A cylinder pulls back either to the empty set or to one source cylinder with the same complete exponent vector. Discard empty preimages. Distinct original numerical moduli retain distinct source exponent vectors, so the source family still has at most one class per numerical modulus. For each of the finitely many \(F\), choose a source submeasure \(\mu_F\) given by (JC1)–(JC12). It satisfies, simultaneously,

\[
 \mu_F(1)\ge m_5,\qquad \mu_F\le(15/4)H_{\rm source},\qquad
 \int(L_{\rm source}-1)\,d\mu_F\le C_5\mu_F(1)
\]

for every complete source test layout, and avoids the pulled-back original family.

Define the one unnormalized target measure

\[
 \mu_{\rm actual}=\mathbb E_F F_*\mu_F.
\]

It avoids every original target class and has mass at least \(m_5\). For any fixed target test layout, its pullback is a partial source layout: empty cylinders contribute zero, the unit cylinder remains the entire carrier, and there is at most one test for each source exponent vector. Completing its missing tests to a full layout only increases the load. Thus, for every \(F\),

\[
 \int(L_{\rm actual}\circ F-1)\,d\mu_F\le C_5\mu_F(1).
\]

Average this inequality before normalizing. Its right side becomes exactly \(C_5\mu_{\rm actual}(1)\), so normalization once gives the same bound \(R\le C_5\) for all target layouts. No common maximizing layout across different injections is required; the source inequality holds for every layout.

For the joint Haar cap, each fixed source word has a uniformly distributed target image under the random shifts. Therefore

\[
 \mu_{\rm actual}\le{15\over4}\,\mathbb E_F F_*H_{\rm source}
 ={15\over4}H_{\rm actual}.
\]

Although \(\mu_F\) depends on \(F\), its domination is applied before averaging. Consequently the same normalized density cap (JC12) holds. These inequalities all concern the same averaged target measure. The injection is used to construct that measure; the target original moduli and future query phases remain unchanged.

For fewer than five actual core primes, pad with odd primes unused in the complete original family and different from the distinguished prime, then project away those coordinates. Padding adds no forbidden class. Any target query can be completed on the padded carrier, so its load bound, Haar domination and support all descend to the original core. Thus the conclusion holds for any core of at most five odd primes, disjoint from the distinguished prime. The latter need not exceed every core prime. Below, \(K\) denotes the actual core period and \(\widehat\mu_5\) its transported normalized law.

## Positive Haar mass and a uniform parent margin

Let \(r\ge17\) be a distinguished prime disjoint from this actual core, and let \(H\ge1\) resolve every original \(r\)-exponent. Define the actual mixed core load

\[
 \ell_{r,H}(x)=
 \sum_{\substack{r^e d\ \mathrm{original}\\1\le e\le H,\ 1<d\mid K}}
 r^{1-e}\mathbf1_{x\equiv\alpha_{r^e d}\pmod d}.
 \tag{JC13}
\]

All original cofactor phases are arbitrary and retained. Pure powers of \(r\) are excluded and reserved in

\[
 B_{r,H}=r-\sum_{e=1}^H r^{1-e}
 \ge {255\over16}.
\]

Under the same \(\widehat\mu_5\), each depth layout has mean at most \(C_5\). Hence

\[
 \mathbb E\ell_{r,H}\le {17\over16}C_5
 ={255\over16}-\eta,
 \qquad
 \eta={2296247035\over28998244912}>{3\over40}.
 \tag{JC14}
\]

Let \(S\) be the complete actual \(r\)-free core survivor set and define

\[
 A=\{x\in S:\ell_{r,H}(x)\le159/10\}.
\]

Since \(159/10=255/16-3/80\), Markov's inequality and (JC14) give

\[
 \widehat\mu_5(A)>{1\over424},\qquad
 \lambda(A)>{1\over424\Lambda_5}
 ={1812390307\over35775000000000}>{1\over20000}.
 \tag{JC15}
\]

At every point of \(A\),

\[
 \ell_{r,H}\le159/10\le B_{r,H}-{3\over80}.
 \tag{JC16}
\]

The uniform Haar law conditioned on this actual \(A\) therefore has density below 20000. This last selection is one law for all the original completion tests; it does not optimize a separate probability for each event.

## Tail consumer and the next boundary

For arbitrary actual core primes the complete geometric sums are at most those of the five reference primes, because each factor decreases with its prime. The distinguished-prime version of report455, proved in [report458](458-distinguished-prime-completion-removes-the-early-phase-restriction.md), retains the auxiliary early cutoff \(\min(H,\lfloor\log_3q\rfloor)\). For every \(r\ge3\), late weights satisfy \(r^{1-e}\le3^{1-e}\), so its constants are unchanged. Applying that bridge to \(\lambda(\cdot\mid A)\), use

\[
 \Lambda=20000,\qquad
 J_1\le{1001\over384},\qquad J_2\le{7007\over480},\qquad
 N=\left\lceil20000\,{7007\over480}\right\rceil=291959.
 \tag{JC17}
\]

Every finite outside-prime set disjoint from \(rK\) and lying above

\[
 B\ge3^{256}\,291959^3
\]

then admits one actual \(r\)-free survivor law with core marginal supported on \(A\) and total original weighted tail completion at most

\[
 {324\cdot20000\cdot1001\over384B}<3^{-250}<{3\over80}.
 \tag{JC18}
\]

All finite outside heights and original support sizes are allowed. The core marginal can change under final global conditioning; its pointwise bound (JC16) is preserved. Adding (JC18) gives weighted completion strictly below \(B_{r,H}\).

This does not supply an arbitrary-core induction. With the same source schedule continued through 17, the multiplier becomes \((105/64)(9/8)\). The same 32-vertex ratio calculation then gives

\[
 \max {M_6W-\mathsf R\over\mathsf R-L_7-L_{11}-L_{13}-L_{17}}
 ={143701171875\over5231277137}>17.
 \tag{JC19}
\]

At the same tight vertex, even replacing the entire stage-17 loss by zero leaves

\[
 {M_6W-\mathsf R\over\mathsf R-L_7-L_{11}-L_{13}}
 ={9580078125\over557658556}>17.
 \tag{JC20}
\]

Thus improving only the last survival-loss bound, while keeping this source cap and predeletion numerator, cannot make this vertex comparison pass the parent-19 threshold. A smaller numerator or a bound on the nonunit load actually removed by deletion would supply information not retained in this estimate. This is a limitation of the specified source bounds and schedule, not an actual-phase counterexample or an impossibility result for other measures. In particular, (JC1) is a bound furnished by the construction; no optimality over all survivor laws is claimed.

The [linear-moment control](../../frontier/cover-geometry/five_core_joint_completion.py) and [exact data](../../frontier/cover-geometry/five_core_joint_completion.json) consume the existing source vertex certificate and recompute the all-height linear moment, the common-vertex inequalities and the displayed rational constants. They do not rerun source hinge geometry or certify the source's entire arbitrary-height proof. The optimized-mode run checks all 32 distinct basic vertices, their common-parameter interpolation inequalities, the three tight comparison vertices, every displayed derived rational constant, and the next-prefix estimate (JC19). The input certificate is bound by its SHA-256; the source geometry is not re-executed. The mathematical premises remain the attributed ordinary completion, normalized-kernel, convex-comparison and first-hit arguments specified above.


From the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/five_core_joint_completion.py
```

Output defaults to JSON on stdout; `--output PATH` selects a file. All new checks remain active under optimization.
