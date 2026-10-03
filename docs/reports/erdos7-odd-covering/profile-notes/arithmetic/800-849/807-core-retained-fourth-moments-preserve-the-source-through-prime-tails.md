# Core-retained fourth moments preserve the source through prime tails

Retaining the same decreasing core inside every fourth-query intersection
improves two conditional noncoverage certificates from
[Report805](805-changing-root-incidence-repairs-the-common-core-phase-obstruction.md).
The fixed product laws, actual phases, complete query thresholds and analytic
tail parameters remain those shown below. The supported source is explicitly
the normalized restriction to the intersection of the old survivor and the
core.

| Old pure-q originals, q in Q | Fixed five-leaf weights | Fixed query threshold | Allowed tail primes | New distorted mass floor |
|---|---|---:|---|---:|
|arbitrary finite phases and heights|(7/26,7/26,2/13,2/13,2/13)|16|strictly above3000|7/400|
|empty|(1/4,1/4,1/6,1/6,1/6)|12|strictly above1600|19/100|

Both rows allow arbitrary29-ending originals and all finite original
exponents. They retain Report805's23 selected-label null condition on one
common core. Every other old phase is arbitrary. Original numerical moduli
are pairwise distinct, odd and greater than1, and their support is contained
in

\[
\{3,5,7,11,13,17,19,23,29\}\cup\{p:p>B\},
\]

with the row's statedB. The primes31 throughB remain excluded. These are
ordinary conditional sufficient results with exact rational controls, not
new Lean verification or unrestricted Erdős#7.

## 1. Choose the core-restricted source explicitly

Let \(Q=\{5,7,11,13,17,19,23\}\), and use the live ternary leaves
\((4,7,2,5,8)\), with Haar digits above depth2. Actual pure3/9 originals
are handled in the common frame of Report805. Fix one reference digit
\(\xi_q\) for everyq and set \(E_q=\{x_q=\xi_q\bmod q\}\).
The coreG has no reference hit on short root1 and at most one reference
hit on long root2.

For everyq, use the normalized survivor law \(\lambda_q\) of its actual
pure-q originals. Their distinct numerical powers give cylinder caps
\(C_q/q^e\), where \(C_q=(q-1)/(q-2)\). Put

\[
\lambda=\lambda_3\otimes\bigotimes_{q\in Q}\lambda_q,
\qquad t_q=\lambda_q(E_q)\in[0,C_q/q].
\]

LetU be the complete actual old survivor, and define

\[
V=U\cap G,\qquad \alpha_V=\lambda(V),\qquad
\nu=\lambda|V/\alpha_V.                                      \tag{CG1}
\]

This definition matters: Report805 also discusses the normalized restriction
to the completeU. Here the moment proof uses support insideG, so it uses
the explicit, possibly smallerV. The product law\(\lambda\) and every
actual original phase are fixed throughout.

For a removed queried support \(D\subseteq Q\), write

\[
A_D=\prod_{q\notin D}(1-t_q),\qquad
B_D=A_D+\sum_{q\notin D}t_q\prod_{r\notin D,\ r\ne q}(1-t_r).
\]

For arbitrary fixed five-leaf weightsw, let \(s_A=w_4+w_7\),
\(s_B=w_2+w_5+w_8\), \(v_A=\max(w_4,w_7)\), and
\(v_B=\max(w_2,w_5,w_8)\). Retain the same intersection factors

\[
F_{D,0}=s_AA_D+s_BB_D,\quad
F_{D,1}=\max(s_AA_D,s_BB_D),\quad
F_{D,2}=\max(v_AA_D,v_BB_D).                           \tag{CG2}
\]

Report805's core-minus-deletions proof RI3–RI5 directly gives the stronger
source statement

\[
\alpha_V\ge L(t)=F_{\varnothing,0}
-\tfrac12\sum_D\beta_DF_{D,2}
-\sum_{D,j=0,1,2}R_{D,j}F_{D,j}.                      \tag{CG3}
\]

Here \(\beta_D=\prod_{q\in D}1/(q-2)\), and the nonnegativeR subtract
the selected numerical slots from their complete shallow support inventories.
The selected set is

\[
\{15,21,45,33,35,39,63,51,57,55,105,75,69,65,99,77,85,117,95,165,91,147,225\}.
\]

Every present original at these labels must be null on the oneG; absent
labels also cause no deletion. All other shallow labels and every height
above2 are charged completely. Thus(CG3) is a bound on\(\lambda(V)\),
not an assertion that its displayed rational lower bound equals actual mass.

The inherited source lower bounds remain

\[
L(t)\ge\frac{572908282021678}{19219130054499375}
\quad\text{for the7/26 law over its entire cap box},
\]

and, for the1/4 law with empty old pure-q inventories and\(t_q=1/q\),

\[
L(t)=\frac{44628705330203}{788477130441000}.           \tag{CG4}
\]

## 2. KeepG in every ordered query intersection

A complete query includes one independently chosen phase at every numerical
divisor of the full finite head period, including its unit term. Consider
any four such queries\(Q_1,\ldots,Q_4\). Expand their product as a sum
over ordered quadruples of numerical labels. In a compatible quadruple,
the four coordinate cylinders intersect in the cylinder of their greatest
coordinate depth. An incompatible intersection is empty. This uses the
actual phases within each tuple and assumes no nesting between unrelated
numerical query labels.

Suppose the positive nonternary maximum depths have supportD and values
\(e_q\ge1\), and the ternary maximum depth isj. On their intersection,
all queried first-digit hits inD are fixed. Forcing those hits to zero can
only enlarge the decreasing eventG. Product independence of the remaining
coordinates and the original cylinder caps therefore give

\[
\lambda\left(G\cap\bigcap_{i=1}^4A_i\right)
\le\prod_{q\in D}\frac{C_q}{q^{e_q}}
\begin{cases}
F_{D,0},&j=0,\\
F_{D,1},&j=1,\\
3^{2-j}F_{D,2},&j\ge2.
\end{cases}                                          \tag{CG5}
\]

There is oneCq factor for each active coordinate, not one for each query.
This is an upper bound on the actual common intersection; it does not
replace its source by separate optimizing laws.

There are\((j+1)^4-j^4\) ordered nonnegative exponent quadruples with
maximumj. The complete nonternary sum is

\[
A_4(q)=\sum_{j\ge1}\frac{(j+1)^4-j^4}{q^j}
=\frac{15}{q-1}+\frac{50}{(q-1)^2}
+\frac{60}{(q-1)^3}+\frac{24}{(q-1)^4}.
\]

The ternary coefficients are1 at depth0,15 at depth1, and

\[
\sum_{j\ge2}((j+1)^4-j^4)3^{2-j}
=9\left(A_4(3)-\frac{15}{3}\right)=216.               \tag{CG6}
\]

Depth2 contributes65, and every greater depth together contributes151.
All finite actual heights are bounded by these positive convergent sums.
Grouping(CG5) byD consequently proves

\[
\boxed{
\int_G Q_1Q_2Q_3Q_4\,d\lambda\le K_G(t)
:=\sum_{D\subseteq Q}
\left(\prod_{q\in D}C_qA_4(q)\right)
\left(F_{D,0}+15F_{D,1}+216F_{D,2}\right).
}                                                       \tag{CG7}
\]

The proof covers mixed products of four unrelated complete query layouts
directly. In particular, nonnegativity and\(V\subseteq G\) imply

\[
\int Q_1Q_2Q_3Q_4\,d\nu\le K_G(t)/\alpha_V.          \tag{CG8}
\]

The uncut product bound is recovered by replacing eachA andB by1:

\[
K_0=(1+15\max(s_A,s_B)+216\max_iw_i)
\prod_q(1+C_qA_4(q)).
\]

Each factor in(CG2) is bounded by its uncut value, so\(K_G(t)\le K_0\).

The maximum-depth expansion and the coefficient216 already occur in
[Report734 HM3–HM5](../700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md)
and [Report790 PC14](../750-799/790-shared-pair-deficits-admit-twenty-nine-at-a-depth-two-profile.md).
Report805 supplies the core intersection factors. The additional combination
here retains those support-dependent factors through the complete moment
sum. [Report735](../700-749/735-shape-specific-fourth-moments-on-the-unchanged-shallow-source.md)
has a different deletion-sensitive finite-source quartic comparison;
[Report535](../500-549/535-mixed-chain-moments-retain-shared-prime-correlations.md)
concerns overlapping chain exponential moments. No literature-priority
claim is made.

## 3. Preserve the same source through29 and the complete prime tail

Keep Report805's complete comparatorZ, full mean and hinge
\(H_h=\mathbb E(Z-h)_+\). Its arbitrary-phase convex-query bound applies
to any retained eventV, giving at one fixed thresholdh

\[
B(\nu)\le h+H_h/\alpha_V.                            \tag{CG9}
\]

Use the actual normalized pure29 survivor law\(\rho_{29}\), then restrict
\(\nu\otimes\rho_{29}\) by every remaining29-ending original without
renormalizing. Numerical distinctness allows one phase per old cofactor
at each positive29 depth. Pure29 conditioning removes the unit cofactor
exactly once. The resulting one supported measure has mass at least
\((28-h-H_h/\alpha_V)/27\).

SinceG uses only old coordinates, the same ordered-tuple calculation at29
multiplies(CG8) by

\[
T_{29}=1+\frac{28}{27}A_4(29).                        \tag{CG10}
\]

The actual29 restriction only decreases its unnormalized nonnegative
moments. Thus the same measure has complete mixed fourth-query cap
\(T_{29}K_G(t)/\alpha_V\).

Apply Report734's unnormalized live deletion and moment propagation with
\(\delta=2/7\), growth21 and the row's\((B,\ell)\). Its full tail charge is

\[
\tau(B,\ell)=\frac{21609}{10240}
\left(\frac{2\ell^2+1}{2\ell^2-1}\right)^{21}
\frac{B}{(B-1)^4}
\sum_{j=0}^{21}\frac{21!}{(21-j)!(3\ell)^j}.          \tag{CG11}
\]

The choices\((3000,7)\) and\((1600,6)\) satisfy\(B\ge286\),
\(\ell\ge4\),\(3^\ell\le B\) and\(4\ell\ge21\), and
\(1+(7/5)A_4(p)\le(1+1/(p-1))^{21}\) holds coefficientwise.
The inherited analytic input is the attributed Rosser–Schoenfeld
prime-product estimate used in Report734. There is no finite enumeration
cutoff on later primes or exponents.

The final distorted mass is therefore bounded below by

\[
\frac{28-h}{27}
-\frac{H_h+27T_{29}K_G(t)\tau}{27\alpha_V}.           \tag{CG12}
\]

The same actualt determines both the source lower bound and the moment.
No source mass is combined with a different law's moment or hinge.

## 4. A joint vertex certificate keeps the mass–moment relation

For each individualt-coordinate,\(F_{D,0}\) is affine and
\(F_{D,1},F_{D,2}\) are convex maxima of affine functions. ConsequentlyL
is separately concave and\(K_G\) is separately convex. For a fixedh and
a proposed floor\(0\le\varepsilon<(28-h)/27\), define

\[
\Psi_{h,\varepsilon}(t)
=(28-h-27\varepsilon)L(t)-H_h-27T_{29}\tau K_G(t).
                                                               \tag{CG13}
\]

Its coefficient ofL is positive, so it is separately concave. Positivity
at all128 cap-box endpoints implies positivity throughout the box.
Using\(\alpha_V\ge L(t)\) in(CG12) then gives final mass strictly
greater than\(\varepsilon\). The thresholdh is fixed over the entire box;
choosing a different threshold independently at each endpoint would not
be this certificate.

For the7/26 law, h16 and\((B,\ell)=(3000,7)\), all128 endpoint slacks
in(CG13) are positive at\(\varepsilon=7/400\). The least endpoint
reserve is at mask127 and is approximately0.017644747866727158.
The core moment there is exactly

\[
K_G=\frac{4535901350300942431484057447354761}
{15276689549517364480512000000}.                       \tag{CG14}
\]

For the1/4 law with empty old pure-q inventories, evaluate the one actual
vector\(t_q=1/q\). With h12 and\((B,\ell)=(1600,6)\), the reserve is
approximately0.19516658855720895, strictly above19/100. Its core moment is

\[
K_G=\frac{17720954214198193035803546186099}
{61969744266371520579000000}.                          \tag{CG15}
\]

These are numerical improvements over the respective uncut-moment
certificates0.015075518713312398 and0.18064743228781174. The new source
normalization is(CG1); those comparisons use the same inherited source
lower bounds and isolate the effect of retainingG in the moment estimate.

The7/26 fullbox at h16 and direct\((1600,6)\) instead has negative
endpoint reserve approximately−0.14482574730658498. This is a failed
sufficient bound, not an actual covering example or an impossibility
theorem for another continuation. Neither the1/4 Haar source mass nor
its1600 conclusion applies to arbitrary old pure-q inventories.

## 5. Exact controls and remaining scope

The [standalone consumer](../../../frontier/cover-geometry/refined-capped-source/core_retained_fourth.py),
[certificate](../../../frontier/cover-geometry/refined-capped-source/core_retained_fourth_certificate.json)
and [result](../../../frontier/cover-geometry/refined-capped-source/core_retained_fourth.json)
reconstruct the selected-label nullity, complete old inventories, source
responses, support moment coefficients, full hinges and tail constants.
Every decision uses exact fractions and remains active under optimized
Python. The result retains all endpoint moment/source pairs and all floor
slacks; no independently attained extrema are multiplied together.

A literal finite control uses the period45, the1/4 ternary law and Haar5,
restricted to the short-root no5-hit core. It exhausts all91125 independent
phase assignments for numerical query labels1,3,5,9,15,45. The actual
maximum raw fourth moment is1883/20; the corresponding finite-height
core-retained bound is1913/20, strictly below the uncut bound99.
The independent maximizing phases are\((1,1,4,1,31)\) at the five
nonunit labels. The control covers unrelated numerical phases and does
not impose nested queries.

The general arbitrary-height assertion uses(CG5)–(CG7), not this finite
test. Positive supported distorted mass gives an actual finite CRT
survivor and hence an uncovered integer. The displayed mass floors are
not Haar-density bounds of the same sizes. The selected-phase contract,
the source regime and the excluded intermediate primes remain essential.

The normal and optimized replays each complete227229 explicit checks with
exit0, as does optimized replay after relocating the three artifacts together.
Nine altered-input/result controls reject with exit1, including removal of
the core restriction from the source definition, a false selected phase,
an old pure5 original in the Haar case, an excessive mass floor and a forged
quartic coefficient. A separately written rational computation matches all256
source/moment endpoint pairs, both hinges and all three continuation rows.

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/core_retained_fourth.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/core_retained_fourth.py
```
