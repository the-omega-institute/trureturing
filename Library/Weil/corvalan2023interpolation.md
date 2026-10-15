---
bibkey: corvalan2023interpolation
authors: Álvaro Corvalán
year: 2023
title: Interpolation and Extrapolation Statements equivalent to the Riemann Hypothesis
doi: null
url: https://arxiv.org/abs/2312.00211v3
claim: "The preprint proposes fixed-weight extrapolation closure criteria. Its printed dictionary and quantifier rewrites require calibration; the weighted norm construction admits the existing actual FIB target transport, but no required approximation estimate is supplied."
strata_touched: []
license: citation-only
triage: anchor
---

# Fixed-weight approximation and the actual FIB target

The inspected primary is [arXiv:2312.00211v3](https://arxiv.org/abs/2312.00211v3),
revised 1 June 2026. Its [PDF](https://arxiv.org/pdf/2312.00211v3) has
SHA256 `28ef4a091c67287cea59a93f9ef447450978257c3b0b6182860ce8bbac08f05e`;
the [author-source archive](https://arxiv.org/src/2312.00211v3) has SHA256
`f756d275cf3a72a42dabe55898ba6f5794e12ae904cbe9d8579df6d81341f71d`.
The selected definitions, Criterion 21, Theorem 24 and their supporting
arguments were read. This is a scoped source-applicability analysis and
paper application, without an independent whole-paper proof audit,
originality claim or Lean certification. The printed criterion is not
adopted without the normalization qualifications below.

## What the proposed sufficient condition actually asks for

Let

$$
E_\theta=(L^1(0,1),L^2(0,1))_{\theta,\infty;K},\qquad
\|f\|_{E_\theta}=\sup_{t>0}t^{-\theta}K(t,f;L^1,L^2),\qquad
p(\theta)=\frac2{2-\theta}.
$$

[Criterion 21](https://arxiv.org/html/2312.00211v3#Thmtheorem21),
author TeX label `N-B-with-extrapol`, proposes a positive fixed weight
$M$, tempered at $\theta=1$ and $O(1)$ there, such that

$$
\inf_{f\in\Phi}\sup_{0<\theta<1}
M(\theta)\|\chi-f\|_{E_\theta}=0,
\qquad \chi=\mathbf1_{(0,1)}.
\tag{I1}
$$

[Theorem 24](https://arxiv.org/html/2312.00211v3#Thmtheorem24),
label `strong Nyman-Beurling-Milman equivalence`, repeats the closure
formulation. The weight is chosen once. For each error tolerance, one
approximant must serve all interpolation parameters in the supremum;
neither the weight nor the approximant may be chosen separately after
observing each parameter. The paper supplies no coefficients or
truncation-dependent error bound attaining this closure.

The cited Jawerth–Milman input is
[Theorem 20](https://arxiv.org/html/2312.00211v3#Thmtheorem20),
label `M_delta`. It assumes a mutually closed Banach couple, tempered
weight and exact interpolation functors with characteristic function
$t^\theta$. The paper credits Milman's *Extrapolation and Optimal
Decompositions with Applications to Analysis*, Theorem 21, p.44.
This standard interpolation result is reused as a literature input;
its upstream proof is not reproved or independently certified here.

### Calibration before using the printed criterion

The following distinctions concern the actual displayed source formulas.
They do not establish that no corrected weighted criterion can hold.

- The source writes its dictionary constraint as
  $\sum_a c_a\rho(1/a)=0$ with $a\ge1$, where
  $\rho(u)=u-\lfloor u\rfloor$. At $a=1$ this uses $\rho(1)=0$.
  Consequently the printed dictionary admits $\rho_1$ alone and excludes
  an individual standard balanced probe
  $\rho_n-\rho_1/n$ for $n\ge2$. It is not literally the standard
  constraint $\sum_a c_a/a=0$. The definitions in the introduction,
  Theorem 4 and the later remarks retain this endpoint issue. The
  [existing classical criterion](baezduarte2002nyman.md) and the
  balanced natural generators in the
  [coefficient-functional application](baezduarte2000natural.md#published-coefficient-functionals-and-restricted-dictionaries)
  remain the separate dictionary suppliers.
- Immediately after its norm-closure statement, Criterion 21 changes
  $\inf_f\sup_\theta$ to $\sup_\theta\inf_f$. The same interchange
  recurs later. These expressions are not generally equal; (I1) is
  the uniform closure condition used here.
- In the reverse proof the bound $M(\theta)\le k$ does not justify
  the printed lower comparison by $k\|\chi-f\|$. At a fixed
  $\theta$ the valid consequence of a small weighted norm is division
  by the positive fixed value $M(\theta)$.
- Conditions only near $\theta=1$ do not control an arbitrary weight
  on the rest of $(0,1)$. A full-interval supremum needs a controlled
  extension there, or an explicitly restricted endpoint interval.

In particular, no RH equivalence for the source's literal printed
$\Phi$ is imported into the project. The useful object retained below
is its weighted norm, applied to an independently specified dictionary.

## A controlled weight and an independently specified dictionary

For definiteness take a fixed $a>0$ and

$$
M_a(\theta)=(1-\theta)^a,\qquad
\|f\|_{X_a}=\sup_{0<\theta<1}
(1-\theta)^a\|f\|_{E_\theta}.
\tag{I2}
$$

This weight is positive and bounded throughout the interval, and
$M_a((1+\theta)/2)=2^{-a}M_a(\theta)$ supplies the endpoint tempering.
It is an available choice, not a weight forced by the five FIB modes.
No equivalence with an unweighted $L^2$ norm is assumed.

On $(0,1)$ use the standard balanced natural span

$$
b_n(x)=\left\{\frac1{nx}\right\}
-\frac1n\left\{\frac1x\right\},\qquad
\mathcal V=\operatorname{span}\{b_n:n\ge2\}.
\tag{I3}
$$

Extend each function by zero outside $(0,1)$. The same formula for
$b_n$ on the half-line is already zero for $x>1$.
Write $W_a=\overline{\mathcal V}^{X_a}$; this closure is defined without
asserting that it contains $\chi$ or the FIB target. Its definition is
not a new RH criterion.

## The existing Binet transport acts in this norm

Reuse [FIB §391](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md),
including its actual coefficients and absolute inverse budget:

$$
q=\varphi^{-2},\qquad \beta_d=\log(1-(-q)^d),\qquad
\gamma*\beta=\beta*\gamma=\mathbf1,\qquad
\sum_d|\gamma_d|\le\frac1{\beta_1-T},\quad
T=\sum_{d\ge2}|\beta_d|<\beta_1.
$$

Here $\beta_d$ is a coefficient sequence, distinct from the ATOM
$\beta=\rho(\alpha)$. For the zero-extended convention define

$$
U_df(x)=\mathbf1_{(0,1/d)}(x)f(dx),\qquad
\mathscr B_\beta=\sum_{d\ge1}\beta_dU_d,\qquad
\mathscr B_\gamma=\sum_{d\ge1}\gamma_dU_d,\qquad
\Phi_\beta=\mathscr B_\beta\chi.
\tag{I4}
$$

These are the restrictions of the same support-preserving half-line
operators. They are not ordinary unrestricted unit-interval dilations.
The endpoint bounds are $\|U_d\|_{L^1}=d^{-1}$ and
$\|U_d\|_{L^2}=d^{-1/2}$. Applying the same operator to each term in
the defining $K$-functional decomposition therefore gives

$$
\|U_df\|_{X_a}\le d^{-1/2}\|f\|_{X_a}.
$$

Thus the existing absolute coefficient and inverse budgets give, in
the new specified norm as well,

$$
\|\mathscr B_\beta\|_{X_a\to X_a}\le B_{1/2},\qquad
\|\mathscr B_\gamma\|_{X_a\to X_a}\le G_{1/2},\qquad
\mathscr B_\gamma\mathscr B_\beta
=\mathscr B_\beta\mathscr B_\gamma=I,
\tag{I5}
$$

where $B_{1/2}=\sum_d|\beta_d|d^{-1/2}$ and
$G_{1/2}=\sum_d|\gamma_d|d^{-1/2}\le(\beta_1-T)^{-1}$.
No inverse theorem is reproved: this is the existing Dirichlet-inverse
transport applied with the common endpoint bound.

The dictionary is compatible with the same operation:

$$
U_db_n=b_{dn}-\frac1n b_d,\qquad b_1=0.
\tag{I6}
$$

Consequently each finite coefficient truncation of either transport
maps $\mathcal V$ into $\mathcal V$. Operator-norm convergence then
preserves $W_a$, and the inverse gives
$\mathscr B_\beta W_a=W_a$. In particular the actual-target error
budgets satisfy

$$
\frac{\operatorname{dist}_{X_a}(\chi,W_a)}{G_{1/2}}
\le\operatorname{dist}_{X_a}(\Phi_\beta,W_a)
\le B_{1/2}\operatorname{dist}_{X_a}(\chi,W_a).
\tag{I7}
$$

This transports both the target and the permissible closed span. It
provides no positive value, zero value or rate for either distance.
The earlier $L^2$ support classification is not silently transferred
to this different norm.

### Finite transport tails can be paid independently

For a finite balanced approximant $v\in\mathcal V$ and an integer $D\ge1$, use
$\mathscr B_{\beta,D}=\sum_{d\le D}\beta_dU_d$. The already supplied
bound $|\beta_d|\le q^d/(1-q)$ gives

$$
\|\mathscr B_\beta v-\mathscr B_{\beta,D}v\|_{X_a}
\le\frac{q^{D+1}}{(1-q)^2\sqrt{D+1}}\|v\|_{X_a}.
\tag{I8}
$$

Hence an actual finite approximant to the transported target can be
formed with the explicit error budget

$$
\|\Phi_\beta-\mathscr B_{\beta,D}v\|_{X_a}
\le B_{1/2}\|\chi-v\|_{X_a}
+\frac{q^{D+1}}{(1-q)^2\sqrt{D+1}}\|v\|_{X_a}.
\tag{I9}
$$

By (I6) the output still has finite balanced natural support. If the
input indices are at most $N$, the output indices are at most $DN$.
The exponentially small second term is a transport cost; the first
term is the unproved approximation estimate. A small transport tail
alone cannot make that first term small. Nor does (I9) assert that the
transported finite coefficients are the fixed natural prefixes
$e_n=(\mu*\beta)_n$ considered in §391.

## Remaining consumer

The source opens a norm choice for a future approximation argument.
Using it requires an actual balanced family $v_j$, one fixed weight,
and a proved common-parameter bound
$\|\chi-v_j\|_{X_a}\to0$, or the corresponding actual-target bound.
The displayed transport supplies neither. Any RH conclusion must
also use the classical criterion with its correct dictionary and the
required embeddings; it does not follow by importing the paper's
literal printed definition.

The five modes encode all natural indices and can organize the
finite support in (I6). Their legal seams and interval-length
conservation do not estimate this weighted approximation error. The
Robin same-integer signed integral remains unpaid. This application
reuses standard interpolation and the existing Binet inverse; it is
not a new supplier theorem, a proof of RH or a claim that the
weighted route outperforms existing approximation methods.

## Strength of a local cutoff block

The logarithmic Selberg coefficients are already discussed in
[Báez-Duarte 2002, Introduction, printed p.2](https://arxiv.org/pdf/math/0202141v2).
The classical source [Conrey–Myerson, arXiv:math/0002254v1,
Theorem 1 and Remark 1](https://arxiv.org/html/math/0002254v1)
distinguishes uniform convergence of its fractional-part sums from the
weighted integral near its moving endpoint. Its sums use
$\{nu\}/n$, whereas the actual residual below uses $\{t/n\}$;
its pointwise estimate is not an upper bound for this residual's local
quadratic energy. The following is a repo-derived paper application of
Mellin continuation to the specified coefficients, not a result stated
in Corvalán's paper, a new unconditional estimate, or a Lean-certified
implication. No originality of the Mellin obstruction is claimed.

For integers $N\ge3$ put

$$
L=\log N,\qquad a_{N,n}=\mu(n)\frac{\log(N/n)}{L}\quad(1\le n\le N),
\qquad c_N=\sum_{n\le N}\frac{a_{N,n}}n.
$$

For the actual balanced approximant
$v_N=-\sum_{2\le n\le N}a_{N,n}b_n$, its residual on
$1/(m+1)<x<1/m$ is

$$
R_N(m)=1+c_Nm-
\sum_{n\le\min(N,m)}a_{N,n}\lfloor m/n\rfloor.
$$

Thus, for integer $m\ge N$,
$R_N(m)=1+\sum_{n\le N}a_{N,n}\{m/n\}$. Define the actual local energy

$$
E_N=\sum_{m=N}^{N^2}\frac{|R_N(m)|^2}{m(m+1)}.
\tag{I10}
$$

A proposed supply $E_N\le C(1+\log N)^A$, with one finite $A\ge0$
and one $C$ for all sufficiently large integers $N$, already entails
RH by the argument below. The estimate cannot be treated as an
independently paid, weaker precursor to (I1). This is a one-way strength
analysis: neither this estimate nor a converse from RH is supplied.

### Passing integer cutoffs and cells without losing the actual source

For real $y>1$ and $t>0$ retain the same coefficients through

$$
S_y(t)=\log y+
\sum_{n\le y}\mu(n)\log(y/n)\{t/n\}.
$$

This is an auxiliary interpolation: at integer arguments
$S_N(m)=L R_N(m)$; within a cell its difference from the balanced
step residual is accounted for by (I12). If $N\le y<N+1$, the summation
indices agree and, uniformly for every real $t$,

$$
S_y(t)-S_N(t)
=\log(y/N)\left(1+\sum_{n\le N}\mu(n)\{t/n\}\right),
\qquad |S_y(t)-S_N(t)|\le2.
\tag{I11}
$$

For $m\le t<m+1$, all $\lfloor t/n\rfloor=\lfloor m/n\rfloor$.
Consequently

$$
S_N(t)-S_N(m)=(t-m)U_N,
\qquad U_N=\sum_{n\le N}\frac{\mu(n)\log(N/n)}n,
\qquad |U_N|\le L(1+\log N).
\tag{I12}
$$

Using $\int_m^{m+1}t^{-2}dt=1/[m(m+1)]$, equations (I11)–(I12)
and the assumed estimate yield

$$
\int_y^{2y}|S_y(t)|^2\frac{dt}{t^2}
\ll L^{A+2}+\frac{(1+L)^4}{N}.
\tag{I13}
$$

Indeed, all intersecting cells have $N\le m\le2N+1\le N^2$ for
$N\ge3$; the cell slope costs $O(|U_N|^2/N)$ and the cutoff correction
costs $O(1/N)$. On changing variables $t=qy$, (I13) gives, for some
fixed finite $B$,

$$
\|S_y(qy)\|_{L^2(1<q<2)}
\ll\sqrt y\,(1+\log y)^B.
\tag{I14}
$$

The small bounded range of $y$ is absorbed in the constant. These
steps use the actual step-function residual; they do not assume that
fractional parts are uniformly Lipschitz across their jumps.

### Mellin in the cutoff variable exposes a reciprocal-zeta factor

For every fixed smooth test function $h$ supported in $(1,2)$, set

$$
F_h(s)=\int_1^\infty\int_1^2
h(q)S_y(qy)\,dq\,y^{-s-1}dy.
$$

Equation (I14) and Cauchy–Schwarz make this integral and its
$s$-derivatives absolutely convergent on compact subsets of
$\Re s>1/2$. Thus $F_h$ is holomorphic there. Initially for $\Re s>1$,
absolute interchange and $y=nv$ give

$$
F_h(s)=\frac{\int_1^2h(q)dq}{s^2}
+\frac{H_h(s)}{\zeta(s)},
\qquad
H_h(s)=\int_1^2h(q)H_q(s)dq,
\quad
H_q(s)=\int_1^\infty\log v\,\{qv\}v^{-s-1}dv.
\tag{I15}
$$

Here $\sum\mu(n)n^{-s}=1/\zeta(s)$ is the classical Dirichlet
identity, reused on its absolute-convergence half-plane. The integrals
$H_q$ are holomorphic for $\Re s>0$ and locally uniformly bounded in
$q$ and $s$.

There is no common zero of $H_q(s)$ as $q$ runs through $(1,2)$.
For a fixed $s$ with $\Re s>0$, write

$$
J_q(s)=q^{-s}H_q(s)
=\int_q^\infty\log(t/q)\{t\}t^{-s-1}dt.
$$

Differentiation at $1<q<2$ gives

$$
\frac{d}{dq}\left(q\frac{d}{dq}J_q(s)\right)
=(q-1)q^{-s-1}\ne0.
\tag{I16}
$$

Hence $H_q(s)$ cannot vanish identically on any open subinterval of
$(1,2)$. If a nontrivial zero $\rho$ had $\Re\rho>1/2$, continuity
in $q$ would supply a smooth compactly supported $h$ with
$H_h(\rho)\ne0$. Multiply (I15) by $(s-1)\zeta(s)$; analytic
continuation extends the identity to $\Re s>1/2$. Evaluation at
$\rho\ne1$ forces $H_h(\rho)=0$, a contradiction. This argument
allows arbitrary zero multiplicity. The usual functional-equation
symmetry then gives RH.

Only a fixed proportional part of (I10) is needed for this obstruction.
If its upper endpoint is $2N$, restrict $q$ to $(5/4,7/4)$; for large
$N$ every intersecting cell lies in $[N,2N]$, while (I16) still prevents
a common zero. Thus discarding the remote part $2N<m\le N^2$ does
not make the proposed uniform polylogarithmic estimate an already
available supplier.

For the actual FIB application, (I5)–(I9) still transport any error
estimate that is genuinely supplied. They provide no value for (I10).
This strength analysis closes neither the required uniform approximation
nor the same-integer signed Robin margin.

## A paid low-denominator part of the actual residual

Reuse the [existing discrete large-sieve input](../Fourier/montgomery1978largesieve.md),
equation (1), namely Montgomery's Theorem 3, printed p.559, and the
duality in §4, Lemma 2. The following is a paper application to the
coefficients and residual of (I10); the classical large sieve is not
reproved. No unconditional bound for the complete energy is asserted.

Write $e(u)=\exp(2\pi i u)$ and retain the zero-frequency coefficient

$$
d_N=1+\frac12\sum_{n\le N}a_{N,n}(1-1/n),\qquad
T_N(m)=R_N(m)-d_N.
\tag{I17}
$$

The finite Fourier expansion of the periodic sawtooth at integer $m$ is

$$
\{m/n\}-\frac{n-1}{2n}
=-\frac1n\sum_{h=1}^{n-1}\frac{e(hm/n)}{1-e(-h/n)}.
$$

It follows by summing $j e(-hj/n)$ over $0\le j<n$; $n=1$ has an
empty sum. Merge every frequency $h/n=r/q$ into its reduced fraction
before applying a separation estimate. This gives, exactly for $m\ge N$,

$$
T_N(m)=\sum_{2\le q\le N}\ \sum_{\substack{1\le r<q\\(r,q)=1}}
B_{N,q,r}e(mr/q),\qquad
B_{N,q,r}=-\frac{b_{N,q}}{q(1-e(-r/q))},\qquad
b_{N,q}=\sum_{j\le N/q}\frac{a_{N,qj}}j.
\tag{I18}
$$

This retains all aliases of the original coefficients, rather than
assuming that the unreduced list is separated. Non-squarefree $q$ have
$b_{N,q}=0$. For squarefree $q$, the coefficient is the short coprime sum

$$
b_{N,q}=\frac{\mu(q)}{\log N}
\sum_{\substack{j\le N/q\\(j,q)=1}}
\frac{\mu(j)}j\log\frac{N}{qj}.
\tag{I19}
$$

This is exactly the existing logarithmic coprime Möbius sum
$\check m_q^{(1)}$ in the
[Zuniga-Alterman source note](../Asymptotics/zunigaalterman2026logmobius.md),
with $X=N/q$ and the prefactor $\mu(q)/\log N$. A fixed-$q$
asymptotic alone would not suffice when $q,X$ vary together. Instead,
reuse its uniform finite bound, obtained from Lemma 5.1, equation (5.2),
the positive convolution (7.6) and Lemma 7.2(a):

$$
|\check m_q^{(1)}(X)|\le2q/\varphi(q)\qquad(q\ge1,\ X>0).
$$

Here $\varphi(q)$ denotes Euler's totient, distinct from the golden
ratio used for the FIB geometry. It follows that
$|b_{N,q}|\le2q/[\varphi(q)\log N]$ for every squarefree $q\le N$,
including the short sums with $q$ close to $N$. Non-squarefree $q$
still contribute zero. This uses the source's uniform convolution
bound rather than inserting a fixed-parameter limit.

For $1\le Q\le N$, the coefficient energy therefore obeys

$$
V_N(Q):=\sum_{2\le q\le Q}\ \sum_{\substack{1\le r<q\\(r,q)=1}}
|B_{N,q,r}|^2\ll\frac{Q}{(\log N)^2}.
\tag{I20}
$$

Indeed, the elementary sine bound gives
$\sum_{r=1}^{q-1}|1-e(-r/q)|^{-2}\ll q^2$. Reuse the
[existing finite positive-moment bound](../ArithSums/weingartner2010distribution.md)
with $s=2$ and $X=Q$:
$\sum_{q\le Q}(q/\varphi(q))^2\le QW(2)$, where the fixed Euler
product $W(2)$ converges. Combining these two inputs proves (I20)
with a constant independent of $N,Q$. Neither input estimates the
signed quadratic cross terms of the residual.

Let $I$ be a consecutive integer interval in
$[M,2M)\cap[N,N^2]$, with integer $M\ge N$, and use the actual weight

$$
\|f\|_I^2=\sum_{m\in I}\frac{|f(m)|^2}{m(m+1)}.
$$

For $1\le Q\le N$, split (I18) as
$T_N=T_{N,\le Q}+T_{N,>Q}$. Distinct reduced fractions of denominator
at most $Q$ have circular separation at least $Q^{-2}$. In the quoted
dual large sieve, take these frequencies, the coefficients $B_{N,q,r}$,
and the actual interval $I$, whose length $H$ is at most $M$.
Since $m(m+1)\ge M^2$, (I20) gives

$$
\|T_{N,\le Q}\|_I^2
\ll\frac{Q(M+Q^2)}{M^2(\log N)^2}.
\tag{I21}
$$

In particular, if $Q^2\le M$, the weighted triangle inequality gives

$$
\left|\|R_N\|_I-\|d_N+T_{N,>Q}\|_I\right|
\le\|T_{N,\le Q}\|_I
\ll\frac{\sqrt{Q/M}}{\log N}\le\frac{M^{-1/4}}{\log N}.
\tag{I22}
$$

This is a norm error for removing a specified part, not an
orthogonal decomposition on the short interval. Take disjoint blocks
$I_j=[2^jN,2^{j+1}N)\cap[N,N^2]\cap\mathbb Z$ and
$Q_j=\lfloor\sqrt{2^jN}\rfloor$, keeping the nonempty blocks
$0\le j\le\lfloor\log_2 N\rfloor$. Define the retained residual
$\mathcal A_N(m)=d_N+T_{N,>Q_j}(m)$ for $m\in I_j$.
Applying (I21) on each block and summing the geometric factors $2^{-j/2}$
gives the whole crossing-block comparison

$$
\left|\sqrt{E_N}-\left(
\sum_{m=N}^{N^2}\frac{|\mathcal A_N(m)|^2}{m(m+1)}
\right)^{1/2}\right|\ll\frac{N^{-1/4}}{\log N}.
\tag{I23}
$$

Thus the discarded low-denominator part has an independently paid norm
bound on the complete block. The retained frequencies satisfy
$q>\sqrt M$ on the block at scale $M$; their coefficients in (I19)
involve only $j<N/\sqrt M$. The zero-frequency term remains tied to
the same coefficients:

$$
d_N=1+\frac12(S_N-c_N),\qquad
S_N=\sum_{n\le N}a_{N,n}
=\frac1{\log N}\int_1^N\frac{\mathcal M(t)}t\,dt,
\qquad \mathcal M(t)=\sum_{n\le t}\mu(n).
\tag{I24}
$$

At scale $M\asymp N$, applying the same large sieve to all denominators
would give the allowance $O(N/\log^2N)$, not a polylogarithmic bound.
Neither (I20) nor (I23) controls the retained signed cross terms or their
interaction with $d_N$. Separate bounds for $d_N$ and each component
are sufficient but need not be necessary, because the terms can cancel
on these finite intervals. A uniform polylogarithmic bound for the
retained norm squared would, by (I23) and the preceding strength
analysis, still entail RH.

Here $q$ is a reduced frequency denominator, not necessarily a prime.
The cut $q\le Q$ is a cut by frequency order, not by numerical
frequency magnitude or a single residue observation. Observing modulo
$D=\operatorname{lcm}(1,\ldots,Q)$ retains all orders dividing $D$,
including some greater than $Q$; for example $Q=3$ also retains order
$6$. Thus the paid spectral cut cannot silently replace the earlier
modulus-based visible/hidden cut.
The five FIB modes can encode the indices $q,j$; their separate address
statistics do not determine the joint condition $(q,j)=1$ or the
short Möbius sum (I19). Squarefree composite denominators are retained.
This application narrows the unestimated arithmetic part while
preserving the actual source, mean and weight. It supplies neither the
complete FIB approximation rate nor the same-integer Robin sign, and
has not been Lean compiled or claimed as an original large-sieve result.
