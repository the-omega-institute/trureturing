# The two-colour core obstructs every fixed-weight full-box certificate

Changing the five fixed ternary weights repairs the negative head-source
bound of [Report808](808-a-second-reference-colour-retains-an-actual-opposing-phase-continuation.md),
but cannot make its full-box, complete-hinge certificate pass the next
prime29. The exact best uniform head bound over ALL fixed nonnegative
normalized five-leaf weights is

\[
\boxed{
L_*=
\frac{336200091883260472703251032899944983319}
{45141777773985211600129643171985587854875}
=0.007447648463614773\ldots .}
\tag{WC1}
\]

Every weight choice has a complete first-query gate at least
0.022526522831384527..., giving the exact separation

\[
\boxed{L_*<\frac3{400}<\frac1{50}<\text{every universal first-query gate}.}
\tag{WC2}
\]

Thus further optimization of these fixed weights cannot repair this
particular full-box continuation, even before any large-prime tail charge.
This is a boundary of the stated source estimate and query comparison.
It does not assert that the actual survivor is empty, that its actual
query norm exceeds28, or that another source or estimate cannot work.
The result is ordinary rational mathematics, not Lean verification or a
resolution of unrestricted Erdős#7.

## 1. Keep the actual family, core and complete inventory fixed

Use Report808's actual25-original family: the Report803 phases with only
the modulus45 original changed to11 mod45. The live ternary leaves are
\((4,7,2,5,8)\). Write \(Q=\{5,7,11,13,17,19,23\}\), and retain
the one two-colour core

- leaves4,7: no zero-hit at anyq;
- leaves5,8: at most one zero-hit;
- leaf2: at most one zero-hit, and the5 digit is not1.

At5, the three categories have probabilities
\(t_5,u,1-t_5-u\) for digits0,1,other. They are mutually exclusive
categories of one coordinate. Different prime coordinates remain independent
under the original product source.

Retain the original universal caps \(C_q=(q-1)/(q-2)\) and the rectangular
relaxation

\[
0\le t_q\le C_q/q,\qquad0\le u\le4/15.               \tag{WC3}
\]

Every point of this rectangle has\(t_5+u\le8/15<1\), so its categorical
probability vector is valid. The same23 selected slots retain their
common-source null condition. The complete remaining numerical support
inventories and all ternary heights are exactly those of Report808.
The weights are the only variables in the present optimization.

For a queried supportD, replace queried5 by the safe digit2 and the other
queried coordinates by nonzero digits. This common replacement enlarges
every leaf core. At the remaining coordinates, letS_D be the short-leaf
response, T_D the special leaf2 response, and B_D the response of leaves5,8.
These are the probabilities in Report808 SC3–SC4. In particular, the
five response vector is

\[
(S_D,S_D,T_D,B_D,B_D),\qquad0\le T_D\le B_D.          \tag{WC4}
\]

Let\(R_{D,0},R_{D,1},R_{D,2}\) be the nonnegative complete shallow
residual coefficients, and let\(\beta_D=\prod_{q\in D}1/(q-2)\),
including\(\beta_\varnothing=1\). The full source certificate is

\[
L_w(t,u)=F_{\varnothing,0}
-\sum_D R_{D,0}F_{D,0}
-\sum_D R_{D,1}F_{D,1}
-\sum_D(\beta_D/2+R_{D,2})F_{D,2}.                   \tag{WC5}
\]

HereF0 is the weighted leaf sum, F1 the maximum of its two root sums,
andF2 the maximum of its five weighted leaves. The\(\beta_D/2\) term
retains every ternary height above2, including pure ternary powers.
No finite exponent truncation or new per-label phase choice is introduced.

The quantity in(WC5) is a guaranteed lower bound on the core-retained
survivor mass. It is not the actual mass itself.

## 2. Symmetry reduces all five weights to two variables

Average the weights of leaves4 and7, and separately average those of
leaves5 and8. The response vector(WC4) shows that these averages preserve
F0 and both root sums. They can only decrease the maximum weighted leafF2.
All of its loss coefficients in(WC5) are nonnegative. Therefore

\[
L_{\rm averaged}(t,u)\ge L_w(t,u)
\quad\text{at every point of(WC3)}.                 \tag{WC6}
\]

Thus it suffices, without loss in the maximum, to use

\[
w=(a,a,c,b,b),\qquad c=1-2a-2b,\qquad
a\ge0,\ b\ge0,\ a+b\le\tfrac12.                  \tag{WC7}
\]

At a fixed probability vector the three factors become

\[
F_{D,0}=2aS_D+cT_D+2bB_D,
\]
\[
F_{D,1}=\max(2aS_D,cT_D+2bB_D),\qquad
F_{D,2}=\max(aS_D,cT_D,bB_D).                         \tag{WC8}
\]

The objective is consequently a concave piecewise-affine function ofa,b.
This reduction includes zero weights and all asymmetric original choices.

## 3. An exact constant supporting plane certifies the continuous maximum

Take the shared all-upper source vector

\[
t_q=C_q/q,\qquad u=4/15.                             \tag{WC9}
\]

It is one vertex of the relaxation. Define

\[
D_*=65430690604068476533868297,
\]
\[
a_* =17711598555353210698668721/D_*,\quad
c_* =11177729466624241374403285/D_*,\quad
b_* =9414882013368906881063785/D_* .                 \tag{WC10}
\]

These weights satisfy(WC7). Direct rational evaluation of(WC5) givesL*.
Only two positive-coefficient maxima in(WC8) are tied there:

| Queried support | Loss coefficient | Equal maximizing leaf branches |
|---|---:|---|
|\(\{5\}\)|\(9/50\)|\(aS_D=cT_D\)|
|\(\{17\}\)|\(1/10\)|\(aS_D=bB_D\)|

Every other charged maximum has a unique maximizing branch. Retain that
branch as a global affine lower bound on its maximum. At the first tie,
replace the maximum by the convex combination
\((1-\theta)aS_D+\theta cT_D\); at the second use
\((1-\eta)aS_D+\eta bB_D\), with

\[
\theta=
\frac{2701584078171358017078739694}
{4122133508056314021633702711},\qquad
\eta=
\frac{3039600035676230795999866087}
{38931260909420743537651636715}.                      \tag{WC11}
\]

Both coefficients lie in[0,1]. Because the maxima are subtracted with
nonnegative coefficients, these branch replacements give a GLOBAL affine
upper bound onL. Substituting\(c=1-2a-2b\) and summing all terms gives
exactly

\[
\boxed{L(a,b;\text{WC9})\le0\cdot a+0\cdot b+L_* .} \tag{WC12}
\]

The standalone certificate reconstructs every active branch, both exact
ties and both rational mixtures; it verifies that the two slope
coefficients vanish exactly and the constant equalsL*. Equality holds at
(WC10). This constant supporting plane, rather than a numerical grid or
an unverified optimization solver, certifies the continuous maximum.

At the fixed law(WC10), all256 source vertices were evaluated exactly.
Their minimum isL*, attained at(WC9). For every fixed weight law,
L is separately concave in the eight source coordinates, as in Report808
SC8. The endpoint evaluations therefore prove

\[
\boxed{
\max_w\ \min_{(t,u)\text{ in(WC3)}} L_w(t,u)=L_* .}
\tag{WC13}
\]

The upper bound uses the single vertex(WC9) and(WC6),(WC12); the lower
bound uses the ONE fixed law(WC10) at all256 vertices. No vertex receives
its own separately optimized weights. In particular, weights can repair
the quarter-law's negative head-source certificate, but only up to(WC1)
within this full-box method.

## 4. A universal complete-hinge gate lies strictly above that maximum

For any nonnegative normalized five-leaf law, the complete-query
comparison has ternary root capr and leaf capv satisfying

\[
r=\max(w_4+w_7,w_2+w_5+w_8)\ge\tfrac12,\qquad
v=\max_iw_i\ge\tfrac15.                              \tag{WC14}
\]

Define a lower auxiliary run with

\[
\Pr(\underline J_3\ge1)=\tfrac12,\qquad
\Pr(\underline J_3\ge e)=\tfrac15\,3^{2-e}\quad(e\ge2).
\]

Keep the same independent nonternary comparison tails
\(\Pr(J_q\ge e)=C_q/q^e\), and put
\(\underline Z=(1+\underline J_3)\prod_q(1+J_q)\).
The pointwise tail inequalities(WC14) give stochastic domination of this
lower comparator by the full comparator for EVERY weight law. Hence

\[
H_h(w)=\mathbb E(Z_w-h)_+\ge
\underline H_h:=\mathbb E(\underline Z-h)_+.          \tag{WC15}
\]

The lower pairr=1/2,v=1/5 need not be jointly attainable by actual five-leaf
weights. Attainability is not required for this lower comparison: each
tail inequality holds for every actual weight law.

For the complete first-query upper bound\(h+H_h(w)/\alpha\) to be
strictly below28, its retained positive source bound would have to satisfy

\[
\alpha>\frac{H_h(w)}{28-h}\ge
\frac{\underline H_h}{28-h}\qquad(h<28).              \tag{WC16}
\]

The exact full mean used for the lower comparator is

\[
\mathbb E\underline Z=\frac95
\prod_q\left(1+\frac{C_q}{q-1}\right),
\]

and each hinge is obtained from this full mean plus its exact atoms belowh.
No high-exponent probability is truncated. The28 rational gates at
\(h=0,\ldots,27\) all exceed1/50. Their minimum occurs ath16 and is
approximately0.022526522831384527.

These integer thresholds also cover all real thresholds: the integer-valued
comparator makes its hinge affine between adjacent integers, and division
by\(28-h\) is monotone or constant on each such interval. Thresholds
\(h\ge28\) cannot yield a first-query upper bound below28, and negative
thresholds do no better than0 for a source lower bound\(\alpha\le1\).
For the final half-open interval\(27\le h<28\), explicitly

\[
\frac{\underline H_h}{28-h}
=\Pr(\underline Z\ge28)+\frac{\underline H_{28}}{28-h}.
\]

The complete\(\underline H_{28}>0\), so this expression increases and
its minimum is at27. The retained exact result also verifies this terminal
hinge and tail probability.

Combining(WC13),(WC15)–(WC16) gives(WC2) for every fixed five-leaf law.
The complete first-query upper bound supplied by this certificate cannot
be made smaller than28. This failure already precedes any fourth-moment
or prime-tail debit; changing only a later tail estimate cannot repair it.
It does not give a lower bound of28 on the actual query norm.

## 5. The cap vertex is approachable by actual finite pure inventories

The method obstruction above only needs membership of(WC9) in the declared
full box. There is also a common actual approach to it. For a finite depthE,
at5 remove the distinct pure originals

\[
2\bmod5,\qquad (3+5^{j-1})\bmod5^j\quad(2\le j\le E).
\]

These cylinders are pairwise disjoint and leave both first digits0 and1
untouched. At every otherq inQ remove

\[
1\bmod q,\qquad(2+q^{j-1})\bmod q^j\quad(2\le j\le E).
\]

These cylinders are also pairwise disjoint and leave first digit0
untouched. The normalized surviving probability of each retained queried
digit is

\[
\frac{1/q}{1-\sum_{j=1}^Eq^{-j}}
=\frac{q-1}{q(q-2+q^{-E})}\ \longrightarrow\ C_q/q.  \tag{WC17}
\]

At5 this same formula holds simultaneously for digits0 and1. All seven
prime coordinates use one finite original family; the selected mixed
classes retain their fixed phases and numerical labels.

The finite sum of continuous affine/max-affine expressions in(WC5) is
jointly continuous in source probabilities and weights. Compactness of
the weight simplex therefore makes convergence along(WC17) uniform over
weights. The strict gap(WC2) implies that sufficiently deep finite pure
inventories also defeat this same source-lower-bound/hinge certificate
for every fixed weight law. No numerical depthE is claimed here.

This observation does not assert simultaneous attainment of the many
mixed-cylinder loss caps, or convert the certificate failure into a
covering family. Actual joint intersections, sharper actual cylinder
caps, another retained core, another source, or another query comparison
remain outside the obstruction.

## 6. Exact verification and the change of research direction

The [consumer](../../../frontier/cover-geometry/refined-capped-source/all_weight_colour_obstruction.py),
[certificate](../../../frontier/cover-geometry/refined-capped-source/all_weight_colour_obstruction_certificate.json)
and [result](../../../frontier/cover-geometry/refined-capped-source/all_weight_colour_obstruction.json)
contain the actual family, original complete inventory, rational maximizing
law, two dual mixtures, every active branch, all256 fixed-law source values
and all28 full-hinge gates. The consumer uses no optimization dependency
and performs no search over weights. Its proof control is the exact
constant affine upper plane and the strict rational bracket(WC2).
An independent calculation also constructs an affine majorant directly
in the five original weights: all five coefficients equalL*. It agrees
with the256 source values, the28 gates and the real-threshold terminal
hinge. This checks the asymmetric-weight boundary independently of the
two-variable calculation.

Normal and optimized replay each complete71395 explicit checks with exit0.
Optimized replay also exits0 after relocating the three artifacts together.
Nine altered-input/result controls reject with exit1, including an
incorrect convex dual mixture, a missing tie, a wrong inventory coefficient,
a false source optimum and a forged zero-slope plane. The independent
terminal-hinge computation agrees exactly.

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/all_weight_colour_obstruction.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/all_weight_colour_obstruction.py
```

The positive part fixes the best head bound for this interface. The negative
part closes fixed-weight tuning as a route to its uniform29 continuation.
Further progress requires changing information or estimates used by the
certificate, such as retained phase-dependent intersections, more of the
actual pure inventory, a different core or a new common-source query bound.
The positive empty-pure theorem of Report808 remains valid under its own
source premise.
