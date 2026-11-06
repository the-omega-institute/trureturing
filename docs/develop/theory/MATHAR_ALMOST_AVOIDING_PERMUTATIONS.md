# Almost-avoiding permutation counts, Mathar recurrences, and rank comparison

## 1. Permutations, deletion, and the source series

**Definition 1.1 (Permutation classes and source attribution).** A permutation of length $n$ is a word containing each element of $\{1,\ldots,n\}$ once; for $n=0$ there is one empty word. A word contains a pattern $\beta$ if some subsequence has the same relative order as $\beta$. Standardization replaces the entries of a word of distinct integers by their ranks. For $t\in\mathbb N$, let $\operatorname{Av}_n(\beta)^{+t}$ consist of the permutations from which at most $t$ entries can be deleted so that the standardized remainder avoids $\beta$. Deleting at most one entry includes deleting none. Put

$$
 h_n=|\operatorname{Av}_n(321)^{+1}|,\qquad
 b_n=|\operatorname{Av}_n(231)^{+1}|.
$$

The algebraic and counting arguments below adapt Haobo Ma and Wenlin Zhang, *Mathar's recurrence in OEIS A174193: the counting formula and A174195*, v2, 3 November 2026, © 2026 the creators, [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). Ma's supplied affiliation is ChronoAI Pte Ltd, Singapore; Zhang's are National University of Singapore and ChronoAI Pte Ltd, Singapore. The recurrence questions are R. J. Mathar's FORMULA entries of 14 June 2016 in [A174193](https://oeis.org/A174193) and [A174195](https://oeis.org/A174195), whose entry creator is N. J. A. Sloane (26 November 2010). The prior enumeration used here is Robert Brignall, Shalosh B. Ekhad, Rebecca Smith and Vincent Vatter, *Almost avoiding permutations*, Discrete Mathematics **309** (2009), 6626–6631, [doi:10.1016/j.disc.2009.06.027](https://doi.org/10.1016/j.disc.2009.06.027), [arXiv:2007.15111v1](https://arxiv.org/abs/2007.15111v1). The 2020 deposit represents that 2009 work.

All polynomial and rational expressions below are evaluated in $\mathbb Q$ (and in $\mathbb R$ for limits); subtraction in them is ordinary field subtraction. A lagged sequence index is used only in its specified nonnegative range.

**Definition 1.2 (Algebraic series).** Let $s\in\mathbb Q[[x]]$ satisfy $s(0)=1$ and $s^2=1-4x$. Define $P,B$ and the cleared source equation by the following fraction, interpreted after cancellation of its $x^2$ factor:
$$
\begin{aligned}
 A(x)&=\frac{P(x)-B(x)\sqrt{1-4x}}{2x^2(1-x)(1-4x)^2}
       =\sum_{n\geq0}a_nx^n,\\
 P(x)&=1-8x+13x^2+24x^3-48x^4,\\
 B(x)&=1-6x+x^2+34x^3-26x^4-4x^5.
\end{aligned}
\tag{1}
$$
All series are over $\mathbb Q$, and the square root has constant term one.
Brignall, Ekhad, Smith and Vatter give this generating function as an
empirical candidate at the end of Section 2 of [Brignall–Ekhad–Smith–Vatter]; their
Proposition 3 and the subsequent hook-length calculation give a tableau
characterization and a finite sum for the actual almost-$321$-avoiding permutation counts.
Theorem 3 evaluates that sum and identifies it with
(1).
The differential-equation approach to recurrences for algebraic series is
classical: R. P. Stanley, *Differentiably finite power series*, European Journal of Combinatorics **1** (1980), 175–188, Theorems 1.5 and 2.1, [doi:10.1016/S0195-6698(80)80051-5](https://doi.org/10.1016/S0195-6698(80)80051-5). R. J. Mathar gives explicit constructions for generating functions involving polynomial roots in *P-finite recurrences from generating functions with roots of polynomials* (2021), [arXiv:2109.02112v1](https://arxiv.org/abs/2109.02112v1), §§2, 4. These general methods provide context for the fixed identities proved below.

**Notation 1.3.** Put
$$
 F(t)=t^4-5t^3+10t^2+14t-8,\qquad C_n=\binom{2n}{n}.
$$

**Theorem 1.** 
There is a unique series $A\in\mathbb Q[[x]]$ satisfying
(1), and its coefficients are
$$
 a_n=\frac{F(n)C_n}{2(n+1)(n+2)(2n-1)}-1\qquad(n\geq0).\tag{2}
$$
For every integer $n\geq4$ they satisfy Mathar's recurrence
$$
\begin{aligned}
0={}&-(n+2)(404489n-1866368)a_n\\
&+(3147815n^2-8680082n-14098754)a_{n-1}\\
&+2(-2336439n^2+652022n+14514849)a_{n-2}\\
&+8(-1044770n^2+10585023n-20370553)a_{n-3}\\
&+8(642982n-2004177)(2n-9)a_{n-4}.
\end{aligned}
\tag{3}
$$

**Proof.** 
The root $s$ exists by the formal binomial series. If $s_1,s_2$ are two such roots, then $(s_1-s_2)(s_1+s_2)=0$. Their sum has constant term two and is a unit, so $s_1=s_2$. The first two coefficients of $P-Bs$ vanish. After division by
$x^2$, the remaining denominator $2(1-x)(1-4x)^2$ is a unit. This proves
existence and uniqueness in $\mathbb Q[[x]]$; in particular the displayed
division by $x^2$ does not introduce negative powers.

The identities
$$
 P=(1-3x^2)(1-4x)^2,\qquad
 -B=(1-x)(-1+5x+4x^2-30x^3-4x^4)
$$
give the useful Laurent-series decomposition
$$
 A=-\frac1{1-x}+\frac1{2x}+\frac1{2x^2}
 +\left(-\frac1{2x^2}+\frac5{2x}+2-15x-2x^2\right)(1-4x)^{-3/2}.
 \tag{4}
$$
The binomial theorem gives
$[x^j](1-4x)^{-3/2}=(2j+1)C_j=:c_j$ for $j\geq0$.
Set $c_j=0$ for $j<0$. Extracting coefficients from
(4) yields
$$
 a_n=-1-\tfrac12c_{n+2}+\tfrac52c_{n+1}+2c_n-15c_{n-1}-2c_{n-2}.
$$
The ratios needed to simplify this expression are
$$
 \frac{(c_{n-2},c_{n-1},c_n,c_{n+1},c_{n+2})}{C_n}
 =\left(\frac{n(n-1)}{4(2n-1)},\frac n2,2n+1,
 \frac{2(2n+1)(2n+3)}{n+1},
 \frac{4(2n+1)(2n+3)(2n+5)}{(n+1)(n+2)}\right).
 \tag{5}
$$
These follow from $C_{n+1}/C_n=2(2n+1)/(n+1)$, including $n=0,1$
under the stated zero convention. Substitution proves (2). In particular $(a_0,a_1,a_2,a_3)=(1,1,2,6)$; at $n=0$ the denominator $2(n+1)(n+2)(2n-1)$ is $-4$, not zero.

Let $q_i(n)$ be the five coefficients in (3), in
increasing lag order. Their sum is the zero polynomial, so the constant
$-1$ in (2) contributes zero to the recurrence. For the
remaining term use
$$
 \frac{C_{n-i}}{C_n}=\prod_{j=0}^{i-1}\frac{n-j}{2(2n-2j-1)},
 \qquad 0\leq i\leq4.
$$
After multiplication by
$M(n)=4(n+1)(2n-1)(2n-3)(2n-5)(2n-7)$, the five summands become
$$
\begin{aligned}
T_0={}&-2(2n-7)(2n-5)(2n-3)(404489n-1866368)F(n),\\
T_1={}&(2n-7)(2n-5)(3147815n^2-8680082n-14098754)F(n-1),\\
T_2={}&-(n+1)(2n-7)(2336439n^2-652022n-14514849)F(n-2),\\
T_3={}&-2n(n+1)(1044770n^2-10585023n+20370553)F(n-3),\\
T_4={}&n(n-1)(n+1)(642982n-2004177)F(n-4).
\end{aligned}
$$
Expansion gives $T_0+T_1+T_2+T_3+T_4=0$: all coefficients in degrees
$0$ through $8$ vanish. Since $M(n)\ne0$ for $n\geq4$, this proves
(3). 
 $\square$

**Corollary 2.** 
The same coefficients satisfy the first-order relation
$$
 (n+3)F(n)(a_{n+1}+1)
 =2(2n-1)F(n+1)(a_n+1)\qquad(n\geq0).
$$

**Proof.** 
Insert (2) and the ratio $C_{n+1}/C_n$ above.
This proof uses no division by $F(n)$.
 $\square$

## 2. Evaluating the tableau sum

**Notation 2.1.** For a number $z$, write $(z)_{\underline r}=z(z-1)\cdots(z-r+1)$,
with $(z)_{\underline0}=1$.

**Theorem 3.** 
For every $n\geq0$, the number
$h_n=|\operatorname{Av}_n(321)^{+1}|$ equals $a_n$ in
(2). Thus (1) is its counting generating function.

**Proof.** 
Use the Robinson–Schensted correspondence, Greene's theorem, and the standard-tableau hook-length formula in the precise application of [Brignall–Ekhad–Smith–Vatter, Proposition 3 and §2]. If $\lambda$ is the insertion shape, the greatest size of a union of two increasing subsequences is $\lambda_1+\lambda_2$. A permutation can be made $321$-avoiding by one deletion exactly when this size is at least $n-1$: a $321$-avoider is a union of two increasing subsequences, and conversely such a union avoids a decreasing triple. Thus the allowed shapes have at most two rows or are $(k,n-k-1,1)$, with $\lfloor n/2\rfloor\le k\le n-2$.

RSK pairs of standard tableaux of shape $\lambda$ contribute $(f^\lambda)^2$ permutations. The at-most-two-row shapes give the Catalan count $C_n/(n+1)$. For the remaining shapes, the hook-length formula specializes to

$$
f^{(k,n-k-1,1)}=
\frac{n!(2k-n+2)}{(k+2)k!(n-k)(n-k-2)!}.
$$

This is the prior shape enumeration, with its hooks evaluated for these shapes. Consequently, for $n\ge2$,
$$
 h_n=\frac{C_n}{n+1}+\sum_{k=\lfloor n/2\rfloor}^{n-2}
 \left(\frac{n!(2k-n+2)}{(k+2)k!(n-k)(n-k-2)!}\right)^2.
 \tag{6}
$$
At $n=2$ the sum is empty. At $n=3$ it has the single shape $(1,1,1)$, whose tableau number is one, so $h_3=5+1=6$. The separate counts are $h_0=h_1=1$. Put $N=n+2$ and $j=n-k$. The summand before squaring becomes
$$
 \frac{(j-1)(N-j-1)(N-2j)}{N(N-1)}\binom Nj.
$$
Its square is unchanged under $j\mapsto N-j$. The terms $j=1,N-1$
vanish, as does the central term when $N$ is even; the terms $j=0,N$
each equal one. Therefore, writing
$w(j)=(j-1)^2(N-j-1)^2(N-2j)^2$, the sum in (6) is
$$
 \frac{1}{2N^2(N-1)^2}\sum_{j=0}^N w(j)\binom Nj^2-1.
 \tag{7}
$$
Vandermonde's identity gives, for $0\leq r\leq3$,
$$
 \sum_{j=0}^N(j)_{\underline r}(N-j)_{\underline r}\binom Nj^2
 =(N)_{\underline r}^2\binom{2N-2r}{N}.
 \tag{8}
$$
Indeed the left side is $(N)_{\underline r}^2$ times
$\sum_j\binom{N-r}{j-r}\binom{N-r}{j}$; taking the coefficient of
$x^{N-2r}$ in $(1+x)^{2N-2r}$ proves the identity when $N\ge2r$. If $N<2r$, each summand is zero because $j\ge r$ and $N-j\ge r$ cannot both hold, and $\binom{2N-2r}{N}=0$. This treats in particular $N=4,5$, $r=3$. Binomial coefficients with indices outside their range are zero; a negative coefficient index is not truncated to zero.
The polynomial identity
$$
\begin{aligned}
 w(j)={}&N^2(N-1)^2-N^2(N-1)j(N-j)\\
 &+(N^2-4N+12)(j)_{\underline2}(N-j)_{\underline2}
       -4(j)_{\underline3}(N-j)_{\underline3}
\end{aligned}
$$
reduces (8) to four terms. Their sum simplifies to
$$
 \sum_{j=0}^N w(j)\binom Nj^2
 =\frac{N^2(N-1)^3(N^3-12N^2+48N-60)}
 {4(2N-5)(2N-3)(2N-1)}\binom{2N}{N}.
 \tag{9}
$$
This simplification follows by replacing each binomial coefficient in
(8) by
$\binom{2N}{N}(N)_{\underline{2r}}/(2N)_{\underline{2r}}$;
all denominators are nonzero for $N\geq4$.
Since $\binom{2N}{N}/C_n=4(2n+1)(2n+3)/((n+1)(n+2))$,
(6)–(9) give
$$
 h_n=\frac{C_n}{n+1}
 +\frac{(n^3-6n^2+12n-4)C_n}{2(n+2)(2n-1)}-1=a_n.
$$
For $n=0,1$ both counts and (2) are one.
 $\square$

## 3. The cross-referenced series A174195

A174193 cross-references A174195, whose FORMULA section contains another
recurrence conjectured by Mathar on 14 June 2016 [OEIS A174195]. Write
$$
\begin{aligned}
 B_*(x)&=\sum_{n\geq0}b_nx^n
 =\frac{R(x)-S(x)(1-4x)^{3/2}}{-2x^2(1-4x)^{3/2}},\\
 R(x)&=1-5x-6x^2+45x^3-24x^4,\qquad S(x)=1+x-4x^2+x^3.
\end{aligned}
\tag{10}
$$
The identification of this series with the actual $b_n$ is the prior [Brignall–Ekhad–Smith–Vatter, Theorem 9]. Its essential-entry partition has the following precise reading. An entry is essential when deleting it leaves a $231$-avoider. Work in the nonavoiding part $\operatorname{Av}(231)^{+1}\setminus\operatorname{Av}(231)$, and let $c=(1-s)/(2x)$ be the Catalan series. Proposition 6's expression

$$E=x^2c'+xc-c+1$$

counts this nonavoiding part with an essential greatest entry: insertion into an avoider gives $x^2c'+xc$, and the subtraction $c-1$ removes ordinary avoiders. The cases used in Theorem 9 are disjoint: the greatest entry is absent from every $231$ occurrence; or it is essential; or it participates but is nonessential and there is a small essential entry; or it participates but is nonessential and there is no small essential entry. The last case is the large-essential-entry case of Proposition 8; its greatest entry must be nonessential, as in that proposition's figure caption and partition context. Here an essential entry is “small” when it is the minimum entry in every $231$ occurrence, and “large” when it is the minimum in none. Proposition 4 of the prior paper proves this dichotomy for essential entries of a nonavoider.

Using Propositions 5–8 with these hypotheses, their Theorem 9 gives the identity

$$
\begin{aligned}
 B_*={}&c+2xc(B_*-c)+E+x^4(c')^2+xcE\\
 &+x^2c'E+(x^2c'+x^2c-c+x+1)(c-1).
\end{aligned}
$$

The coefficient of $B_*$ after rearrangement is $1-2xc=s$, a unit. Substituting $c=(1-s)/(2x)$ and $s^2=1-4x$ gives (10), with its apparent poles canceled. Thus the quoted prior enumeration applies to the deletion-defined class. The nonessential-greatest-entry hypothesis is necessary for the disjoint reading: $3412$ has exactly the two $231$ occurrences on values $(3,4,1)$ and $(3,4,2)$, no small essential entry, and essential large entries $3$ and $4$. Omitting that hypothesis would overlap the essential-greatest-entry case. This clarification preserves the final prior generating-function theorem.

**Theorem 4.** 
Put $G(t)=2t^4-9t^3+19t^2+18t-24$. Then $b_0=b_1=1$, and
$$
 b_n=\frac{G(n)C_n}{4(n+1)(n+2)(2n-1)}\qquad(n\geq2).\tag{11}
$$
For $n\geq4$, Mathar's A174195 recurrence holds:
$$
\begin{aligned}
0={}&2(n+2)(2013n^2-10435n+41550)b_n\\
&+(4026n^3-128025n^2+34955n+59010)b_{n-1}\\
&-2(2n-5)(20130n^2-110855n+93819)b_{n-2}.
\end{aligned}
\tag{12}
$$
The left side is $13998$ at $n=2$ and $57576$ at $n=3$. These residuals rule out extending (12) to those indices. The OEIS FORMULA entry specifies no starting index; they do not contradict an explicitly stated Mathar range. Equation (12) has lag two and uses $b_2,b_3$ to start at $n=4$; $b_0,b_1$ are separate initial data. No minimal-order assertion is needed for either recurrence.

**Proof.** 
Rewrite (10) as
$$
 B_* =\frac1{2x^2}+\frac1{2x}-2+\frac x2
 +\left(-\frac1{2x^2}+\frac5{2x}+3-\frac{45}2x+12x^2\right)(1-4x)^{-3/2}.
$$
The negative-power coefficients cancel. Coefficient extraction using
(5) gives, for all $n\geq0$,
$$
 b_n=\frac{G(n)C_n}{4(n+1)(n+2)(2n-1)}
       -2\mathbf1_{n=0}+\tfrac12\mathbf1_{n=1}.
$$
For $n\geq4$, all three terms in (12) therefore use
(11). Multiply the normalized recurrence by
$8(n+1)(2n-3)(2n-1)$. Its numerator is
$$
\begin{aligned}
 &4(2n-3)(2013n^2-10435n+41550)G(n)\\
 &\quad +(4026n^3-128025n^2+34955n+59010)G(n-1)\\
 &\quad -(n+1)(20130n^2-110855n+93819)G(n-2)=0.
\end{aligned}
$$
All coefficients in degrees $0$ through $7$ vanish. The multiplier is
nonzero in this range, proving the recurrence. At $n=2,3$, substitute
$(b_0,b_1,b_2,b_3)=(1,1,2,6)$ to obtain the stated residuals.
 $\square$

**Corollary 5.** 
For every $n\geq2$,
$$
 (n+3)G(n)b_{n+1}=2(2n-1)G(n+1)b_n.
$$

**Proof.** 
Substitute (11) and $C_{n+1}/C_n=2(2n+1)/(n+1)$.
 $\square$

**Corollary 6.** 
For $n\geq2$,
$$
 b_n-a_n=1+\frac{n-4}{4(2n-1)}\binom{2n}{n}.
$$
In particular
$|\operatorname{Av}_n(231)^{+1}|>|\operatorname{Av}_n(321)^{+1}|$
for $n\geq4$. Both sequences satisfy
$a_n\sim b_n\sim 4^{n-1}\sqrt{n/\pi}$, and
$$
 b_n-a_n\sim\frac{4^n}{8\sqrt{\pi n}},\qquad
 \lim_{n\to\infty}n\frac{b_n-a_n}{b_n}=\frac12.
$$

**Proof.** 
Subtract (2) from (11) and use
$G(n)-2F(n)=(n+1)(n+2)(n-4)$. The difference is zero at $n=2,3$ and one at $n=4$; for larger $n$ it is positive since $C_n>0$. At $n=0,1$ the two counts are also equal, so $h_n=a_n\le b_n$ for every $n\ge0$.
For the asymptotics, Stirling's formula gives $C_n\sim4^n/\sqrt{\pi n}$,
and each rational prefactor in (2) and (11)
is asymptotic to $n/4$. Since $C_n\to\infty$, the constant $-1$ is negligible. More explicitly, $a_n/(nC_n/4)\to1$ and $b_n/(nC_n/4)\to1$. The exact difference gives $(b_n-a_n)/C_n\to1/8$, since $1/C_n\to0$ and $(n-4)/(4(2n-1))\to1/8$. Therefore

$$
 n\frac{b_n-a_n}{b_n}
 =\frac{(b_n-a_n)/C_n}{b_n/(nC_n)}
 \longrightarrow \frac{1/8}{1/4}=\frac12.
$$

The unscaled relative gap tends to zero. The $b_n$ asymptotic is the formula attributed to Václav Kotešovec in A174195, FORMULA, 23 August 2014; the calculation here supplies its derivation and the companion and gap constants.
 $\square$

**Corollary 7.** 
There is a length-preserving injection from
$\operatorname{Av}(321)^{+1}$ to $\operatorname{Av}(231)^{+1}$:
send the $r$th lexicographically ordered member of
$\operatorname{Av}_n(321)^{+1}$ to the $r$th member of
$\operatorname{Av}_n(231)^{+1}$.

**Proof.** 
For $n\leq3$ both classes contain every permutation of length $n$.
For $n\geq4$ Corollary 6 gives the required cardinality
inequality. Each ordered list is finite and can be constructed by testing
all permutations for avoidance after each single deletion, so the map
is defined and computable at every length. Distinct source permutations have distinct ranks and hence distinct images. Taking the disjoint union over $n$ preserves length, and images from different lengths cannot coincide. This proves the claimed injection without an efficiency bound.
 $\square$

This rank construction addresses the injection in [Brignall–Ekhad–Smith–Vatter, Problem 10];
it is not a local combinatorial correspondence between the two classes.

**Proposition 3.1 (Deletion distances zero and one).** For each $\beta\in\{231,321\}$ and $t\in\{0,1\}$, the actual counting series $\sum_{n\ge0}|\operatorname{Av}_n(\beta)^{+t}|x^n$ is rational in $x$ and the branch $s=\sqrt{1-4x}$ with $s(0)=1$.

**Proof.** At $t=0$, both classical avoidance counts are Catalan, so the series is $(1-s)/(2x)$. Its numerator starts with $2x$, so the quotient is a power series. At $t=1$, Theorem 3 and the prior almost-$231$ enumeration identify the two actual series with (1) and (10). The cancellations already proved at $x=0$ show these rational expressions define power series. $\square$

**Open question 3.2.** Brignall–Ekhad–Smith–Vatter, Conjecture 11, asks for the same assertion for every natural $t$. The cases $t\ge2$ remain open in this argument. Deleting at most $t$ entries is a different condition from having at most $t$ occurrences of the forbidden pattern.

## 追加锚（本行以下为增补区）

**Correction 3.3 (Scope of Corollary 7).** In the sentence after Corollary 7,
“addresses the injection” refers only to the existence of a length-preserving
injection. The combinatorial explanation requested immediately before
[Brignall–Ekhad–Smith–Vatter, §4, Problem 10, p. 8] is not supplied by this
argument. This clarification replaces any reading of that sentence as answering
Problem 10 in its requested explanatory sense. Corollary 7, its proof, the count
comparison, and all other results above remain valid.

**Proof.** The rank rule applies to any two finite totally ordered sets whose
cardinalities satisfy the required inequality. Corollary 6 supplies that
inequality here; Corollary 7 proves that the resulting map is computable,
injective, and length-preserving. This argument establishes no structural
correspondence between the two pattern-avoidance classes. The distinction is
also explicit after Corollary 7 and in the Problem 10 coverage row of Ma and
Zhang, *Mathar's recurrence in OEIS A174193: FORMULA, 14 June 2016: a tableau-sum
evaluation extending Brignall–Ekhad–Smith–Vatter (2009)*, v3, 4 November 2026
([CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)). $\square$
