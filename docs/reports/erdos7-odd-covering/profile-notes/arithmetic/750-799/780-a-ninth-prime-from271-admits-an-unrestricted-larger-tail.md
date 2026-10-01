# A ninth prime from271 preserves one source and an unrestricted larger tail

Let a finite family have pairwise-distinct odd numerical moduli greater than one and one fixed original residue per modulus. Suppose that

* at most eight prime divisors of its ENTIRE original LCM are smaller than271;
* at most nine prime divisors of that LCM are at most20000.

Then the family is noncovering. Original finite prime-power heights, mixed support sizes and the finite number of support primes above20000 are unrestricted. There is no missing-small-prime or prescribed phase-dictionary condition. The construction gives final distorted survivor mass greater than1/50000000.

In particular, every such family on at most nine support primes whose ninth prime, when present, is at least271 is noncovering. This includes the ordered support $(3,5,7,11,13,17,19,23,271)$, which has nine primes below6561 and hence is outside the eight-small-prime hypothesis of [779](779-the-original-capped-source-lowers-the-general-eight-prime-tail-cutoff.md).

The new step uses779's complete source/query profile to add a ninth full prime coordinate before its large-tail stage. This changes the admitted head family, not just the scalar tail cutoff. The two same-source updates reuse [771](771-stop-loss-profiles-preserve-the-ordinary-source-through-thirteen-primes.md) and [773](773-repeated-upper-mass-comparison-lowers-the-fourteen-prime-tail-cutoff.md); the final continuation reuses [734](../700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md). These are ordinary deductions and exact rational checks, not new Lean verification or a resolution of unrestricted Erdős #7.

## 1. The eight-prime source keeps its complete profile

For any fixed family on eight ordered odd head primes,779 supplies ONE physical measure $\mu_8$ of exact mass

$$
m_8=\frac1{33750},
$$

supported outside the actual head originals. It simultaneously satisfies, for every complete numerical-divisor layout $\Phi$ and nonnegative increasing convex $f$,

$$
\int f(L_\Phi)\,d\mu_8\le\int f(M)\,d\Pi_8.
\tag{1}
$$

Here $\Pi_8=\operatorname{Top}_{m_8}(\Pi)$, where $\Pi$ is779's product submeasure: the two actual pure-anchor factors $(3,1/2),(5,3/4)$ and capped factors

$$
(7,3/2),(11,5/3),(13,3/2),(17,2),(19,9/5),(23,11/5).
$$

The comparison has total mass $m_8$ and minimum load192. The actual source and this comparison work at the complete finite heights required by ALL original classes, including later tail-touching ones. The larger-prime transport, countable-completion boundary and original covered-set containment conditions are exactly those proved in779; no source is chosen after selecting $\Phi$.

Retain three complete comparison moments:

$$
W_8=\int M\,d\Pi_8,\qquad
G_8=\int M^2\,d\Pi_8,\qquad
K_8=\int M^4\,d\Pi_8.
$$

Exact geometric moments and the low-load atoms give

$$
\frac{W_8}{m_8}=268.90370180751904\ldots,\qquad
G_8=2.441036631641955\ldots,\qquad
K_8=590422.0422477094\ldots.
\tag{2}
$$

All infinite auxiliary tails are included. These numbers are moments of an outer comparison measure, not moments asserted equal to those of the actual source.

For this comparison,773's criterion $W_8<(q-1)m_8$ first holds at the prime271: it fails at269 and every smaller prime. This is only a boundary of the declared constant-clipping bound. It does not rule out a different source or phase-sensitive continuation at29.

## 2. Add the ninth coordinate with one actual kernel

First use the reference ninth prime $q=271$ and choose

$$
\delta=\frac{32}{45},\qquad
C=\frac1{1-\delta}=\frac{45}{13},\qquad
T=\delta(q-1)=192.
$$

The cap satisfies $C\le q$. Assign every head-only original using the ninth prime to this stage, retaining its entire old numerical cofactor and its actual globally fixed phase. At an old state $x$, let $\alpha(x)$ be the Haar fraction of its full new fibre covered by these originals. Distinctness provides at most one old phase query per complete cofactor at a fixed positive new exponent $e$.

The layouts at DIFFERENT exponents can have different old phases. Thus the valid bound is

$$
\alpha(x)\le\sum_{e\ge1}q^{-e}L_e(x),
$$

with the full-layout Jensen argument of771 using weights $(q-1)q^{-e}$. It does not replace all $L_e$ by one layout.

Use771's actual normalized conditional kernel capped by $C$, and then delete the actual new forbidden union. Its loss is at most

$$
D_9=\frac{\int(M-T)_+\,d\Pi_8}{(1-\delta)(q-1)}.
$$

Since the comparison has no mass below192, its stop loss at $T=192$ is exactly $W_8-192m_8$. Therefore

$$
D_9=\frac{W_8-192m_8}{78},\qquad
m_8-D_9=\frac{270m_8-W_8}{78}
       =0.0000004164475564979925\ldots
       >m_9:=\frac1{2500000}.
\tag{3}
$$

If the actual post-deletion mass is $v_9$, scale that SAME restricted source by $m_9/v_9\le1$. This fixes its mass to $m_9$ and preserves avoidance and all nonnegative cost inequalities. The scale is a mathematical existence construction depending on the original family, not on a query. The old marginal may change under deletion and scaling; no marginal-preservation claim is made.

Before the new actual restriction, conditional ordered increments and the labelled Jensen step give the comparison

$$
\Pi_8\times\pi_{271,45/13},\qquad M'=M(1+J),
$$

where

$$
\pi_{q,C}(0)=1-C/q,\qquad
\pi_{q,C}(j)=C(q-1)/q^{j+1}\quad(j\ge1).
$$

Restriction, common scaling and the upper-mass principle then give

$$
\Pi_9=\operatorname{Top}_{m_9}
             (\Pi_8\times\pi_{271,45/13}).
\tag{4}
$$

The resulting ONE actual source satisfies(1) with $\Pi_9$ for every complete nine-coordinate query and convex cost. The outer product law imposes no independence on its actual coordinates.

For any actual ninth prime $q\ge271$, use the same $\delta$ and $C$. The actual threshold $\delta(q-1)$ and loss denominator increase, while the auxiliary tails $C/q^e$ decrease. Hence its loss is at most(3), and its complete-query comparison is bounded by the same reference product in(4). The common target mass $m_9$ works uniformly. Its original prime is never replaced by a new numerical label inside the family.

## 3. The new profile has a controlled complete fourth moment

Appending the normalized cap factor multiplies a complete $k$th moment by

$$
\mathbb E(1+J)^k
=1+C\left(\mathbb E_{\rm Haar}(1+J)^k-1\right).
$$

For $t=1/(q-1)$, the required excess polynomials are

$$
A_1=t,\qquad A_2=3t+2t^2,\qquad
A_4=15t+50t^2+60t^3+24t^4.
$$

The complete untrimmed product fourth moment is

$$
K_8(1+\tfrac{45}{13}A_4(271))
=705372.7436955494\ldots.
$$

The same product comparison has total mass $m_8$. Exact low-load convolution gives

$$
(\Pi_8\times\pi_{271,45/13})(M'>640)
\le m_9\le
(\Pi_8\times\pi_{271,45/13})(M'\ge640).
$$

Let $a_n$ be the product's atom at $n$. Keeping its largest $m_9$ units of mass, including the required fraction of its atom at640, gives

$$
\begin{aligned}
K_9
&=K_8(1+\tfrac{45}{13}A_4(271))
  +640^4(m_9-m_8)
  +\sum_{n<640}(640^4-n^4)a_n\\
&=449493.5938281003\ldots<450000.
\end{aligned}
\tag{5}
$$

This is the complete fourth moment of $\Pi_9$. Only low comparison loads are enumerated; the untouched infinite moment supplies its entire high tail. It therefore bounds every complete actual fourth query on the SAME ninth source. Hölder supplies the mixed products of four layouts required by734.

The second upper-mass step is material: using only the untrimmed705372.7437 bound does not give the stated20000 tail cutoff with the prescribed mass $m_9$. No assertion of global optimality is made for either clipping parameter or cutoff.

## 4. Attach every remaining prime above20000

If there are at most eight original support primes at most20000,779 already applies because there are then at most eight at most6561. Its source mass conclusion is stronger than the lower bound claimed here.

Otherwise there are exactly nine original support primes at most20000. The first hypothesis forces the ninth to be at least271. Apply Sections1–3 to these nine primes and the actual head-only subfamily, using full old heights that also resolve every tail-touching original. All remaining support primes exceed $B=20000$.

Apply734's same quartic continuation with clipping parameter $2/5$ and growth exponent25. It retains every numerical label, old cofactor and original phase and bounds losses for any finite set of larger primes by

$$
450000\,\tau(B,\ell),
$$

where

$$
\tau(B,\ell)=\frac{5625}{6144}
\left(\frac{2\ell^2+1}{2\ell^2-1}\right)^{25}
\frac{B}{(B-1)^4}
\sum_{j=0}^{25}\frac{25!}{(25-j)!(3\ell)^j}.
$$

This analytic allowance is independent of head dimension once its common mixed fourth-query bound is supplied. Its conditions hold at $(B,\ell)=(20000,9)$, since $3^9=19683\le20000$ and $4\ell\ge25$. Exact arithmetic yields

$$
\frac1{2500000}-450000\,\tau(20000,9)
=0.000000021417799884540607\ldots
>\frac1{50000000}>0.
\tag{6}
$$

The actual live source remains outside every original class. Its positive mass gives an avoiding point in the finite CRT carrier and hence an integer survivor. Formula(6) is a distorted-mass lower bound, not a Haar-density assertion.

## 5. Scope and exact verification

The [consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/ninth_271_quantile_tail.py) reuses779's arithmetic functions, freshly recomputes and compares its retained data result, and checks the declared factors and source mass before reconstructing all640 initial low-load atoms, the complete first, second and fourth moments, the exact clipping charge, the appended cap law and the second upper-mass cutoff. Its [result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/ninth_271_quantile_tail.json) retains exact prescribed masses, clipping parameters and terminal analytic allowance and margin.

All large intermediate fractions are calculated exactly. To avoid retaining many-thousand-digit moment numerators, the result stores rational intervals with an inclusive lower endpoint and exclusive upper endpoint, each checked directly against its exact computed value. The positivity tests use the full fractions before this output formatting. These intervals are certified outward bounds, not floating-point inputs. The moment and cutoff identities are also checked by their split-atom and threshold forms. An unresolved finite window is rejected, as are invalid mass, factor, source-interface and analytic domains; guards remain active under Python optimization.

The source construction, the full-query transport theorem and the analytic prime-product estimate retain their attributed ordinary-proof status. Reusing a rational consumer is not a fresh kernel replay of the source theorem, and no new Lean result is asserted.

[467](../450-499/467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md) allows a nine-prime head with at most seven support primes below43, equivalently its last two ordered head primes are at least43 and47, followed by an unrestricted tail above5000000. Its hypothesis does not contain the new tuple with eighth prime23 and ninth271. Conversely, its ninth prime may be47, below this note's threshold. [766](766-nine-and-ten-prime-heads-with-a-missing-small-prime.md) and773 require a missing prime from $\{3,5,7,11\}$; the new class allows all four. The statements have different hypotheses and all remain valid.

The current source profile cannot supply a positive constant-clipping ledger for ninth prime269 or below, including29. That is a restriction of this comparison interface, not a counterexample to noncoverage or to a future phase-sensitive source. The present conclusion is the explicit separated nine-prime family and its unrestricted larger tail.
