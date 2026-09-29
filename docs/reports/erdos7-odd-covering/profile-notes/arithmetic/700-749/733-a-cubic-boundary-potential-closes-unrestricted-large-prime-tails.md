# A cubic boundary potential closes unrestricted large-prime tails

The four-direction source in [Report730](730-one-common-shallow-source-supports-four-arbitrary-fresh-prime-heights.md) supports an unlimited number of sufficiently large additional prime directions, each at arbitrary finite height. Two sufficient conditions follow.

Let the original family have pairwise distinct odd numerical moduli greater than one. Write $P_0=\{3,5,7,11,13,17,19,23\}$. The **old caps** mean $v_3(m)\le2$ and $v_p(m)\le1$ for every $p\in P_0\setminus\{3\}$.

| Cutoff $B$ | Number of actual support primes in $(23,B]$ | Where old caps are required |
| --- | ---: | --- |
| 4000 | at most four | every original modulus |
| 9000 | at most four | only original moduli supported entirely on primes at most $B$ |

Each row implies an uncovered integer. Primes greater than $B$ have no bound on their number, finite heights, or participation in mixed moduli. The second row also permits arbitrary old-prime exponents in every original containing a prime greater than $B$. All four intermediate-prime coordinates permit arbitrary finite heights in both rows.

These are restricted noncoverage results. They do not cover arbitrary old heights among the head-only originals or an unrestricted number of intermediate primes. [Chapter33](../../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md) and [Report709](709-twelve-and-thirteen-small-heads-admit-unrestricted-prime-tails.md) already treat unrestricted large-prime tails with other initial sources and a second-moment interface. The present contribution is a cubic absolute-mass interface and the resulting two cutoffs for the new source. It is an ordinary proof with exact rational certificates, not new Lean verification.

## An absolute reserve and one complete-query cubic bound

For a processed finite period $Q$, a complete query has one fixed phase per numerical divisor, including the unit:

$$
 L_a(x)=\sum_{d\mid Q}\mathbf1_{\{x\equiv a_d\pmod d\}}.
$$

Let $\nu$ be a nonnegative submeasure avoiding the already processed actual originals. Assume

$$
 \nu(1)\ge\rho,\qquad
 \int L_a^3\,d\nu\le K\quad\hbox{for every complete query }a.
 \tag{CT1}
$$

Hölder on this same unnormalized measure gives $\int L_aL_bL_c\,d\nu\le K$. No independently optimized sources are combined, and the measure is never divided by its surviving mass.

At a new prime $p$ of full required height $H$, assign all actual originals whose last unprocessed prime is $p$ to this step. Their earlier cofactors retain their entire numerical labels and original phases. At any exponent $e$, these cofactors form a partial complete query, because the original numerical moduli are distinct.

For each complete past state $x$, let $B_x$ be the actual forbidden union in the current coordinate and let $\beta(x)=H_p(B_x)\in[0,1]$. Distinguish it from the additive union-bound load

$$
 \alpha(x)=\sum_{\substack{\text{actual originals }d p^e\\p\nmid d}}
          p^{-e}\mathbf1_{\{x\equiv a_{dp^e}\pmod d\}},
 \qquad \beta(x)\le\alpha(x).
$$

Completing each partial earlier query and applying Hölder gives

$$
 \int\alpha^3\,d\nu\le K\theta_{p,H}^3,\qquad
 \theta_{p,H}=\sum_{e=1}^H p^{-e}\le\frac1{p-1}.
 \tag{CT2}
$$

Completion here is analytic padding of tests, not the addition or reuse of an actual original modulus.

## A dominated conditional kernel with explicit loss

Fix $0<\delta<1$. On the entire finite current coordinate use the good-part kernel

$$
 R_x(dy)=
 \frac{\mathbf1_{\{y\notin B_x\}}}{1-\min(\beta(x),\delta)}\,H_p(dy).
 \tag{CT3}
$$

It is a subprobability kernel for every past state. Its loss and full-depth cylinder caps are

$$
 1-R_x(1)=\frac{(\beta(x)-\delta)_+}{1-\delta},
 \qquad
 R_x([a]_{p^e})\le\frac{p^{-e}}{1-\delta}.
 \tag{CT4}
$$

In particular, a smaller surviving row mass does not multiply the cylinder cap. The entirely forbidden row $\beta=1$ gives the zero kernel; the entirely live row gives Haar. This is the good part of the existing capped-deletion construction. All previously excluded events remain excluded after applying it.

For $a\ge0$,

$$
 (a-\delta)_+\le\frac{4a^3}{27\delta^2},
$$

as follows by maximizing $(a-\delta)/a^3$ at $a=3\delta/2$. Thus the absolute loss at this step is at most

$$
 D=\frac{4K\theta_{p,H}^3}{27\delta^2(1-\delta)}.
 \tag{CT5}
$$

The cube bound also propagates. Decompose each enlarged complete query by its current exponent $e\in\{0,\ldots,H\}$, and expand a product of three such queries. The all-zero exponent term costs at most $K$, since the kernel has mass at most one. For a triple with maximum exponent $m>0$, its actual current-prefix intersection is empty or a single prefix; CT4 bounds its conditional mass by $p^{-m}/(1-\delta)$. Its earlier load product is bounded by CT1 and Hölder. There are $(m+1)^3-m^3$ ordered exponent triples with maximum $m$. Consequently

$$
 K'=K\left(1+\frac{A_{3,H}(p)}{1-\delta}\right),\qquad
 A_{3,H}(p)=\sum_{m=1}^H((m+1)^3-m^3)p^{-m}.
 \tag{CT6}
$$

This argument keeps all actual phases fixed before integration. It does not maximize a phase separately in different past states. It is the cubic version of the joint-load transfer in Chapter33; the all-moment lcm expansion also appears in [BBMST, Lemma3.6](https://arxiv.org/html/1811.03547#S3.SS1).

The all-height majorant is

$$
 A_3(p)=\frac{7p^2-2p+1}{(p-1)^3}.
 \tag{CT7}
$$

Taking $\delta=1/3$, a finite continuation at distinct primes $p_i$ therefore retains mass at least

$$
 \rho_0-\sum_i\frac{2K_{i-1}}{(p_i-1)^3},
 \qquad K_i=K_{i-1}\left(1+\frac32A_3(p_i)\right).
 \tag{CT8}
$$

The integral and bound at each step refer to its one current live measure. Telescoping the absolute losses proves CT8 without normalizing it.

## Summing every prime above a cutoff

Put $t=1/(p-1)$. Then $A_3(p)=7t+12t^2+6t^3$, and

$$
 1+\frac32A_3(p)\le(1+t)^{11}=\left(\frac p{p-1}\right)^{11}.
 \tag{CT9}
$$

The coefficient differences in degrees one, two and three are respectively $1/2,37,156$; all higher coefficients are nonnegative. Thus CT9 holds for every $p>1$.

Use the already cited [Chapter33 SH11](../../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md) consequence of Rosser--Schoenfeld's explicit reciprocal prime-product bounds:

$$
 \prod_{B<p\le z}\frac p{p-1}
 \le c_\ell\frac{\log z}{\log B},\qquad
 c_\ell=\frac{2\ell^2+1}{2\ell^2-1},
 \tag{CT10}
$$

for integer $B\ge286$, integer $\ell\ge4$, $3^\ell\le B$, and $z\ge B$. This is the inherited analytic premise; the exact rational consumer does not reprove that published theorem.

Enlarge the preceding actual-tail product to every prime in $(B,p]$. Enlarge the tail sum to every integer greater than $B$. Since $(\log z)^{11}/(z-1)^3$ decreases for $\log z>4$, sum-to-integral comparison and $(z-1)^{-3}\le(B/(B-1))^3z^{-3}$ give

$$
 \sum_{p>B}\frac{2K_{p^-}}{(p-1)^3}
 \le K_0\,\tau_{11}(B,\ell),
$$

$$
 \tau_{11}(B,\ell)=
 c_\ell^{11}\frac{B}{(B-1)^3}
 \sum_{j=0}^{11}\frac{11!}{(11-j)!(2\ell)^j}.
 \tag{CT11}
$$

To check the integral constant, repeated integration by parts yields

$$
 \int_B^\infty\frac{(\log z)^{11}}{z^3}\,dz
 =\frac{(\log B)^{11}}{2B^2}
  \sum_{j=0}^{11}\frac{11!}{(11-j)!(2\log B)^j}.
$$

The factor 2 in CT8 cancels this $1/2$. Replacing $\log B$ by $\ell$ in the positive sum gives CT11. The infinite comparison bounds every finite set of actual tail primes; no infinite original covering or infinite configuration is introduced.

## First initialization: keep the same source and the old caps

Write $q_1<q_2<q_3<q_4$ for the actual intermediate primes, padding unused coordinates if fewer occur. They satisfy $q_i\ge(29,31,37,41)_i$. Padding adds no forbidden original.

Report730 gives a live submeasure dominated by $\mu_{E_{23}}$ times Haar on these four full prime-power coordinates, with mass at least

$$
 \rho_4=\frac{21201970586591}{5920223700787200}.
 \tag{CT12}
$$

Its complete-query cube is at most

$$
 K_4=G_3\prod_{p\in\{29,31,37,41\}}(1+A_3(p))
 =\frac{5006518103820493161366055877}{391240726784822476800000}.
 \tag{CT13}
$$

Expand the three current exponent tuples under product Haar to obtain the factors $1+A_3(p)$. Restricting to the actual live submeasure only decreases each nonnegative integral. The factors decrease with $p$, since $A_3'(p)=(-7p^2-10p-1)/(p-1)^4<0$. This justifies the benchmark primes for any four actual intermediate primes.

Here every original, including those involving tail primes, must obey the old caps, so these are all the old cofactors later queries will require. Take $B=4000,\ell=7$. Exact arithmetic gives

$$
 \rho_4-K_4\tau_{11}(4000,7)>\frac1{2100}.
 \tag{CT14}
$$

The tail debit is approximately $0.00308820183432$, compared with reserve $0.00358127862361$. The strict comparison is performed as a rational inequality.

## Second initialization: reset to the full-height Haar survivor

For $B=9000$, impose the old caps only on head-only originals. Resolve every head coordinate at the heights required by the entire actual family. Let $U$ be the actual survivor of the head-only family, lifted to those full heights. Report730 implies

$$
 H_{\rm head}(U)\ge h_4
 =\frac{1110198785825664533}{18010359497054150553600}.
 \tag{CT15}
$$

Use the new, explicitly specified measure $\eta=H_{\rm head}|_U$. Its mass is at least $h_4$ and its density relative to full-height product Haar is at most one. No preservation of the preceding normalized $G_3$ bound is assumed.

Under product Haar, a compatible triple of congruences has mass equal to the reciprocal of its lcm; an incompatible triple has mass zero. Complete exponent-triple summation gives

$$
 \int L_a^3\,d\eta
 \le\prod_{p\in P_0\cup\{29,31,37,41\}}(1+A_3(p))
 =K_{\rm Haar}
 =\frac{904586065356754077622844547849353}
        {618450171621156480614400000000}.
 \tag{CT16}
$$

All old exponents in later tail-touching classes are now included in this full-height query bound. Larger intermediate primes or missing head coordinates reduce the displayed majorant.

At $B=9000,\ell=8$, exact arithmetic gives

$$
 h_4-K_{\rm Haar}\tau_{11}(9000,8)>\frac1{150000}.
 \tag{CT17}
$$

The debit is approximately $0.0000549258883234$, compared with initial mass $0.0000616422335161$. The same displayed bound at $B=8000,\ell=8$ fails; no optimality claim is made for 9000.

Every original tail-touching class is charged once at its last actual tail prime, including all mixed uses of earlier primes and all their original exponents. Positive final mass gives an actual avoiding point in the finite CRT period and hence an uncovered integer.

## Measure units, verification and the remaining problem

The bounds $1/2100$ and $1/150000$ are **final live-measure mass**, not Haar or natural density. If there are $s$ actual tail primes, each CT3 kernel has density at most $3/2$. One may separately infer Haar density greater than

$$
 \frac{104726}{6084351}\frac{(2/3)^s}{2100}
 \quad\hbox{in the first case},\qquad
 \frac{(2/3)^s}{150000}
 \quad\hbox{in the second case}.
$$

The [exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_cubic_prime_tail.py) pins and replays the Report730 source, verifies the cubic exponent counts and coefficientwise growth envelope, and recomputes both rational cutoff substitutions. Its [result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_cubic_prime_tail.json) retains the exact reserves, charges and positive margins. Separate arithmetic reconstructed the Report730 reserve and both cutoff bounds. An independent finite kernel example checked actual union fractions, absolute row loss and full-depth cylinder caps.

The published prime-product estimate, inherited source theorem and general kernel argument remain ordinary mathematical premises of the finite certificate; the program is not an end-to-end formal verification of them. The unresolved interfaces are now explicit: arbitrary old exponents among head-only originals, and more than four actual primes in the intermediate block. This theorem removes a bound on the number of sufficiently large primes, while preserving those two restrictions.
