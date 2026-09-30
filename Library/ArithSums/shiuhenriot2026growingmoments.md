---
bibkey: shiuhenriot2026growingmoments
authors: trureturing research synthesis
year: 2026
title: Fixed function classes and actual-core ranges for growing Robin moments
doi: null
url: https://doi.org/10.1017/S0305004114000280
claim: "Shiu, Nair–Tenenbaum and corrected Henriot impose function-class and sample-length conditions. Removing small primes gives uniform rough weights, but the resulting exact-core estimate does not reach the large actual cores needed by the current Fibonacci moment obstruction."
strata_touched: []
license: citation-only
triage: anchor
---

# Growing Robin moments and corrected short-sum estimates

This note records the named primary-source hypotheses and their parameter maps. The resulting Fibonacci application is a paper derivation, not a Lean proof or an exhaustive literature/novelty claim. The uniform theorem is quoted from Henriot's corrected 2014 statement; the original 2011 preprint alone is not used as the final authority.

## Actual parameter range

For the actual family

$$
V=F_r,\quad r\ge7\text{ prime},\quad I_r=[\lceil V/10\rceil,\lfloor V/5\rfloor]\cap\mathbb Z,
\quad N_g=1+Vg,
$$

write $A=\min N_g$, $X=\max N_g$, $T=|I_r|$,
$y=\log A$, $\ell=\log y$, $s=y\ell$, and $t=e^\gamma\ell$.
Thus $X\asymp V^2$, $T\asymp V$.

The original theorems do **not** supply a uniform estimate for $Z(n)^s$ with this growing $s$ by direct substitution. However, removing primes up to $w=s+1$ produces a family with genuinely fixed growth constants. This yields the following restricted bound, with a constant depending only on fixed $\eta\in(0,1)$:

$$
\boxed{
\sum_{\substack{g\in I_r\\ C_w(N_g)=C}} Z(N_g)^s
\ll_\eta \frac{T}{C\log w}Z(C)^s,
\qquad C\le V^{1-\eta},
}
\tag{R1}
$$

uniformly as prime $r\to\infty$, where
$C_w(n)=\prod_{p\le w}p^{v_p(n)}$ is the **complete actual** small-prime core. Empty core classes contribute zero. Formula (R1) includes both prime powers and the exact requirement that the cofactor have no prime factor at most $w$.

The restriction $C<V$ is substantive. The already derived necessary condition when $Q_r:=\sum_{g\in I_r}(Z(N_g)/t)^s\ge1$ identifies an actual squarefree core of size at least

$$
V^{2e^{-1/2}-o(1)}=V^{1.21306\ldots-o(1)}.
\tag{R2}
$$

Thus (R1) gives a sound uniform estimate on a restricted range but does not reach the configurations that remain dangerous. In particular it does not settle the large-divisor weighted-hit condition in the existing interface.

## Original sources and exact application conditions

### Shiu

P. Shiu, *A Brun-Titchmarsh theorem for multiplicative functions*, J. reine angew. Math. **313** (1980), 161–170, DOI [10.1515/crll.1980.313.161](https://doi.org/10.1515/crll.1980.313.161). The bibliographic title is sometimes transcribed as “Titschmarsh”.

Original scanned paper: [Göttingen article PDF](https://gdz.sub.uni-goettingen.de/download/pdf/PPN243919689_0313/LOG_0015.pdf). The function class on printed p.162 and Theorem 1 on printed p.163 were read from the page images, not inferred from OCR. The original has $0<\alpha,\beta<1/2$, and coprime positive residue/modulus $(a,q)=1$. In the original's variables,

$$
\sum_{\substack{x-h<n\le x\\n\equiv a\pmod q}}f(n)
\ll \frac{h}{\varphi(q)\log x}
\exp\!\left(\sum_{\substack{p\le x\\p\nmid q}}\frac{f(p)}p\right)
\tag{S1}
$$

provided $q<h^{1-\alpha}$ and $x^\beta<h\le x$. The class requires nonnegative multiplicativity and

$$
f(p^a)\le A_1^a,\qquad
\forall\varepsilon>0\ \exists A_2(\varepsilon):
 f(n)\le A_2(\varepsilon)n^\varepsilon.
\tag{S2}
$$

At the end of printed p.163 Shiu states that implied constants depend at most on $\alpha,\beta,f$. Henriot's introduction specifies the dependence through the corresponding class constants $A,B$. The restricted result stated above can be based directly on the corrected Henriot theorem, whose uniform class dependence is explicit, so it does not rely on suppressing Shiu's dependence on $f$.

### Nair–Tenenbaum

M. Nair and G. Tenenbaum, *Short sums of certain arithmetic functions*, Acta Math. **180** (1998), 119–144, DOI [10.1007/BF02392880](https://doi.org/10.1007/BF02392880).

Original author-hosted paper: [ShortSums.pdf](https://tenenb.perso.math.cnrs.fr/PPP/ShortSums.pdf); author bibliography item 73 confirms the journal citation. The PDF internally numbers its pages 1–21. Theorem 1 and Corollary 1 are on PDF p.6, and the class is defined in equation (1), PDF p.1.

Their class $\mathcal M_k(A_0,B_0,\varepsilon)$ consists of nonnegative functions satisfying

$$
F(m_1n_1,\ldots,m_kn_k)
\le \min\{A_0^{\Omega(m)},B_0m^\varepsilon\}
F(n_1,\ldots,n_k),\quad m=m_1\cdots m_k,
\tag{NT1}
$$

when $(m_j,n_j)=1$ for every $j$. For Theorem 1, the product polynomial $Q=\prod_j Q_j$ has degree $g$ and no fixed prime divisor. With

$$
A_0,B_0\ge1,\quad 0<\varepsilon<1/(8g^2),\quad0<\delta\le1,
\quad F\in\mathcal M_k(A_0,B_0,\varepsilon\delta/3),
$$

the estimate is uniform for

$$
x\ge c_0\|Q\|^\delta,\qquad x^{4g^2\varepsilon}\le h\le x.
\tag{NT2}
$$

The implied constant depends on $A_0,B_0,\varepsilon,\delta,k,r_Q,g,D$; $c_0$ has the same permitted dependencies except $D$. Here $r_Q$ is the number of irreducible factors and $D$ is their defined discriminant-related integer. Their norm is the maximum absolute coefficient.

Corollary 1 retains the condition that $Q$ have no fixed prime divisor, requires $1\le a\le q$ and $(q,Q(a))=1$, and changes the class to
$F\in\mathcal M_k(A_0,B_0,\varepsilon\beta\delta/6)$, and has
$1\le q\le h^{1-\beta}$, $x\ge c_1\|Q\|^{2\delta}$, and $x^{4g^2\varepsilon}\le h\le x$, with fixed $0<\varepsilon<1/(8g^2)$, $0<\beta<1$, $0<\delta\le1/(2g)$. This again leaves growth-parameter dependence. Pairwise coprime polynomial factors are needed for some simplified corollaries, not a license to treat two factors from the same integer as independent.

### Henriot and the indispensable erratum

K. Henriot, *Nair–Tenenbaum bounds uniform with respect to the discriminant*, Math. Proc. Cambridge Philos. Soc. **152** (2012), no.3, 405–424, DOI [10.1017/S0305004111000752](https://doi.org/10.1017/S0305004111000752). The original arXiv version read was [1102.1643v1, 8 February 2011](https://arxiv.org/html/1102.1643v1), especially class (2.10), Theorem 5 and Corollary 2. Its polynomial norm is the sum of the absolute coefficients.

The correction read in full is *Nair–Tenenbaum uniform with respect to the discriminant—ERRATUM*, Math. Proc. Cambridge Philos. Soc. **157** (2014), 375–377, first published 7 July 2014, DOI [10.1017/S0305004114000280](https://doi.org/10.1017/S0305004114000280), [publisher PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0305004114000280).

The erratum replaces $\widehat\rho_{\mathbf R}$ by $\breve\rho_{\mathbf R}$, adding joint exclusion conditions between distinct irreducible factors. It corrects certain uses of submultiplicativity. It also replaces $D^*$ by $a^*D^*$, where $a^*$ is the leading coefficient of $Q^*$, in the relevant exceptional-prime factors and corollaries. In its discussion of the joint-congruence error, the erratum states that the original upper bounds remain valid while the claimed sharpness/lower bound needed repair. The applications here use the corrected theorem and root counts, including the leading-coefficient condition, rather than treating that remark as permission to omit the other corrections.

New Theorem 5 (erratum p.377) requires primitive polynomials $Q_j$, their product of degree $g$, parameters $\alpha,\delta\in(0,1]$, $A_0,B_0\ge1$, and

$$
0<\varepsilon<\frac{\alpha}{50g(g+\delta^{-1})},
\qquad F\in\mathcal M_k(A_0,B_0,\varepsilon).
\tag{H1}
$$

Uniformly in

$$
x\ge C_0\|Q\|^\delta,\qquad x^\alpha<h\le x,
\tag{H2}
$$

it bounds the polynomial sum by

$$
h\prod_{g<p\le x}\left(1-\frac{\rho(p)}p\right)
\sum_{n_1\cdots n_{r_Q}\le x}
\widetilde F(n_1,\ldots,n_{r_Q})
\frac{\breve\rho_{\mathbf R}(n_1,\ldots,n_{r_Q})}
 {[n_1\kappa(n_1),\ldots,n_{r_Q}\kappa(n_{r_Q})]}.
\tag{H3}
$$

Both $C_0$ and the implied constant depend at most on $g,\alpha,\delta,A_0,B_0$. Henriot uses the global coprimality condition $(\prod m_j,\prod n_j)=1$ in the class definition. All applications below have one variable, so the distinction from Nair–Tenenbaum causes no additional assumption.

For $Q(g)=Vg+1$, $\rho(p^a)=1$ when $p\nmid V$ and is zero when $p\mid V$, for every $a\ge1$. The leading coefficient is $V$. A degree-one discriminant of 1 does not justify discarding $p\mid V$. Formula (H3), used below with its actual root counts, avoids that mistake.

## Two failures of direct full-moment substitution

Let $f_s(n)=Z(n)^s$. At $p=2,a=1$,

$$
A_0\ge (3/2)^s,
\qquad B_0(\varepsilon)\ge (3/2)^s2^{-\varepsilon}.
\tag{G1}
$$

These are necessary lower bounds for the parameters, not an estimate of the theorem's actual implicit constant. The originals do not assert that their constants stay bounded for these parameters. It would be invalid to substitute $s=y\log y$ and then keep the implied constant fixed.

Independently, Shiu's particular exponential majorant loses the local saturation of the moment Euler product. For this Fibonacci family, $2\nmid V$, so the exponent in (S1) contains

$$
\frac{f_s(2)}2=\frac{(3/2)^s}{2}.
\tag{G2}
$$

Its size already makes that raw majorant unusable at the Robin threshold. A better estimate would have to preserve the saturated local factors of $U(s)$, in addition to justifying uniform constants. Nair–Tenenbaum's unsimplified sums preserve more structure, but still carry the growing-class obstruction (G1).

## Fixed-class normalization after removing small primes

For real $s\ge1$, $w\ge s+1$, define two multiplicative functions:

$$
R_{s,w}(n)=\prod_{\substack{p^a\parallel n\\p>w}}Z(p^a)^s,
\qquad
J_{s,w}(n)=\mathbf1_{P^-(n)>w}\,Z(n)^s,
\tag{F1}
$$

with $P^-(1)=\infty$. The first ignores the small-prime factors. The second is supported on rough integers and is required to preserve **exact** core classes.

For $p>w,a\ge1$,

$$
1\le Z(p^a)^s\le (1-1/p)^{-s}
\le \exp\!\left(\frac{s}{p-1}\right)\le e.
\tag{F2}
$$

At primes at most $w$, the local values of $R$ are 1 and those of $J$ at positive powers are 0. Consequently both satisfy

$$
F(p^a)\le e\le e^a,\qquad F(n)\le e^{\omega(n)}.
\tag{F3}
$$

For every fixed $\varepsilon>0$, split primes at $e^{1/\varepsilon}$. This gives the explicit uniform estimate

$$
e^{\omega(n)}\le
\exp(\pi(e^{1/\varepsilon}))\, n^\varepsilon.
\tag{F4}
$$

Thus $A_0=e$ and $B_0=\exp(\pi(e^{1/\varepsilon}))$ work simultaneously for all $s,w$ above. For $J$, if $w\ge e^{1/\varepsilon}$, one can even take $B_0=1$; this improvement is not needed. The zeros of $J$ cause no problem for the upper-bound class.

The rough Euler excess is also uniformly small. For $p>w$, put

$$
U_p(s)=(1-1/p)\sum_{a\ge0}\frac{Z(p^a)^s}{p^a}.
$$

From (F2) and $e^u-1\le(e-1)u$ for $0\le u\le1$,

$$
1\le U_p(s)
\le1+\frac{e^{s/(p-1)}-1}{p}
\le1+\frac{(e-1)s}{p(p-1)}.
\tag{F5}
$$

The standard prime-counting upper bound, or PNT plus partial summation, gives

$$
\prod_{p>w}U_p(s)
\le \exp\!\left(O\!\left(\frac{s}{w\log w}\right)\right).
\tag{F6}
$$

For $w=s+1$, this exponent is $O(1/\log s)$. This is a valid uniform normalization; it does not control the discarded small-prime core distribution.

## Extracting an actual core: coprimality and both parameter maps

Fix a $w$-smooth integer $C$. If $(C,V)>1$, no $N_g$ has that core. Otherwise let $g_C\in\{0,\ldots,C-1\}$ be the unique solution of

$$
1+Vg_C\equiv0\pmod C.
$$

Writing $g=g_C+Ck$ gives the exact factorization

$$
N_g=C(Vk+b_C),\qquad b_C=(1+Vg_C)/C\in\mathbb Z,
\qquad (b_C,V)=1.
\tag{C1}
$$

Here $b_C\le V+1$, including $C=1,g_C=0,b_C=1$. A prime dividing both $b_C,V$ would divide $Cb_C-Vg_C=1$, proving coprimality. Thus $Q_C(k)=Vk+b_C$ is primitive, degree one, and has no fixed prime divisor. Its coefficient norm is $O(V)$, independently of $C$.

Since $C$ contains only primes at most $w$, exact core equality is equivalent to $P^-(Vk+b_C)>w$. In particular the cofactor is automatically coprime to $C$, and ordinary multiplicativity yields the exact identity

$$
\sum_{\substack{g\in I_r\\C_w(N_g)=C}}Z(N_g)^s
=Z(C)^s\sum_{k\in K_C}J_{s,w}(Vk+b_C),
\quad K_C=\{k:g_C+Ck\in I_r\}.
\tag{C2}
$$

**Shiu map.** Dividing $N_g=Cm$ gives
$m\equiv C^{-1}\pmod V$, with $m\asymp V^2/C$ and interval length $h_m\asymp V^2/C$. The original condition $V<h_m^{1-\alpha}$ becomes

$$
C\ll V^{\,2-1/(1-\alpha)}
=V^{(1-2\alpha)/(1-\alpha)}.
\tag{C3}
$$

For any fixed $0<\alpha<1/2$, this is a fixed power strictly below $V$. A sufficient uniform range is $C\le V^{1-\eta}$ after choosing a fixed $\alpha<\eta/(1+\eta)$. The interval-length condition is harmless there, since $h_m\asymp m$.

Combining $C\mid n$ with $n\equiv1\pmod V$ into modulus $CV$ and applying the coprime-residue Shiu theorem to $n$ would be invalid: the combined residue is divisible by $C$, hence is not coprime to $CV$ when $C>1$. One must divide out the actual core, as above, or use a theorem that explicitly permits that non-coprime condition.

**Corrected Henriot map.** In (C2), the index interval has position and length comparable to $V/C$ when $C\le V^{1-\eta}$. It is contained in a bounded number of intervals $(u,u+h]$ with $h=u\asymp V/C$; harmless endpoint adjustments are absorbed by this covering. Take the theorem parameters $\alpha_H=1/2$, $\delta_H=\eta/2$, and any fixed

$$
0<\varepsilon_H<\frac{1}{100(1+2/\eta)}.
$$

Then $u\gg V^\eta$ and $\|Q_C\|=O(V)$, so
$u\ge C_0\|Q_C\|^{\delta_H}$ holds uniformly for sufficiently large $V$. All class constants are fixed by the preceding normalization. This makes the theorem's hypotheses explicit, without treating its coefficient threshold as an absolute condition independent of interval length.

For $C>V$, $K_C$ contains at most one point, because the original multiplier interval has length less than $V$. The short-interval and coefficient hypotheses no longer supply the desired averaging. Uniformity in a polynomial's discriminant does not remove its required sample length.

## Derivation of the restricted exact-core bound

Apply (H3) to $J_{s,w}$ and $Q_C(k)=Vk+b_C$. Since $(V,b_C)=1$, prime-power root counts are 1 away from $V$ and 0 at primes dividing $V$. For one irreducible factor, the corrected congruence density is at most $1/a$, and zero unless $(a,V)=1$. Therefore the right side of (H3) is at most a fixed multiple of

$$
h\prod_{\substack{p\le u\\p\nmid V}}(1-1/p)
\prod_{\substack{p\le u\\p\nmid V}}
\left(\sum_{a\ge0}\frac{J_{s,w}(p^a)}{p^a}\right).
\tag{B1}
$$

This follows by first bounding the finite divisor sum by its nonnegative Euler product. If $w\le u$, cancellation prime by prime turns (B1) into

$$
h\prod_{\substack{p\le w\\p\nmid V}}(1-1/p)
\prod_{\substack{w<p\le u\\p\nmid V}}U_p(s).
\tag{B2}
$$

For the actual choice $w=s+1\asymp\log V\log\log V$, the condition $w\le u$ holds uniformly for $C\le V^{1-\eta}$. Equations (C2), (F6), and $h\asymp T/C$ prove the more explicit version

$$
\sum_{\substack{g\in I_r\\ C_w(N_g)=C}}Z(N_g)^s
\ll_\eta \frac{T}{C}Z(C)^s
\prod_{\substack{p\le w\\p\nmid V}}(1-1/p)
\exp\!\left(O\!\left(\frac{s}{w\log w}\right)\right).
\tag{B3}
$$

Finally, all primes dividing $F_r$ are at least $2r-1$. Hence
$\omega(V)\le\log V/\log(2r-1)$ and
$\log(V/\varphi(V))=O(1/\log r)$. Mertens' product estimate therefore gives

$$
\prod_{\substack{p\le w\\p\nmid V}}(1-1/p)
\ll\frac1{\log w},
$$

uniformly, which proves the paper implication (R1).

Replacing $J$ by $R$ in the same calculation loses the small-prime sieve factor and yields only $\ll_\eta(T/C)Z(C)^s$ for an upper bound obtained by dropping exact-core exclusions. This explains both the gain in (R1) and why exact core/cofactor coprimality cannot be silently discarded and then restored.


## Remaining joint estimate

The exact-core estimate above concerns the same integer and includes the rough-cofactor constraint. It covers $C\le V^{1-\eta}$ for fixed $\eta>0$. The actual-core condition from the existing FIB moment analysis under $Q_r\ge1$ supplies an actual core with $C\ge V^{2e^{-1/2}-o(1)}$; there is no interval average left for a fixed core above $V$. The degree-one discriminant, a fixed multiplicative class, and a coprime residue do not remove this sample-length gap.

The arbitrary-residue counterexample and the full small-core application are developed in §215 of the [FIB theory volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md). Neither is a Robin counterexample. This note does not assert that an applicable estimate is absent from all literature.
