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
independently paid, weaker precursor to (I1). This implication is a
one-way strength analysis. The later classical-error application
supplies a paper converse only for the every-epsilon subpower version
of the first proportional block; no fixed polylogarithmic supplier is
established.

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
reproved. This reduction alone supplies no bound for the complete energy.

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

## A numerical-frequency cut of the same residual

A frequency's reduced denominator and its circular distance from an
integer are different observations. The same three inputs used in
(I20)–(I23) also pay for deleting frequencies away from integers. This
is another application to the actual coefficients, not a new
large-sieve theorem or a claim that the remaining quadratic form is
small. Write $L=\log N$ and let $0<\eta\le1/4$.

The elementary sine bound, including the case $\eta q<1$, gives

$$
\sum_{\substack{1\le r<q\\\|r/q\|\ge\eta}}
|1-e(-r/q)|^{-2}\ll\frac{q^2}{1+\eta q}.
$$

Here $\|t\|$ is distance to the nearest integer. Restricting the sum
to coprime numerators only decreases it. Apply the uniform coefficient
bound following (I19), then partial summation to the already supplied
finite moment $\sum_{q\le X}(q/\varphi(q))^2\le XW(2)$. The angular
coefficient energy satisfies

$$
V_{N,\eta}^{\rm away}:=
\sum_{2\le q\le N}\ \sum_{\substack{1\le r<q\\(r,q)=1\\\|r/q\|\ge\eta}}
|B_{N,q,r}|^2
\ll\frac1{L^2}\sum_{q\le N}\frac{(q/\varphi(q))^2}{1+\eta q}
\le\frac{W(2)\log(1+\eta N)}{\eta L^2}.
\tag{I25}
$$

For precision, the implied constant in the first inequality also
multiplies the final allowance. The final comparison for the weighted
positive-moment sum follows from integrating $(1+\eta t)^{-1}$ on
$0\le t\le N$; it does not use a fixed-moment limiting average in
place of a finite bound.

Retain the actual blocks $I_j$, $M_j=2^jN$ and $Q_j$ of (I23).
On each block define the exponential sum

$$
D_{N,\eta,j}(m)=
\sum_{Q_j<q\le N}\ \sum_{\substack{1\le r<q\\(r,q)=1\\\|r/q\|\ge\eta}}
B_{N,q,r}e(mr/q).
$$

Apply the same large sieve separately on dyadic denominator shells
$Q\le q<2Q$, $Q=2,4,\ldots$, truncated at $N$. On a shell,
the coefficient argument above gives the uniform allowance

$$
V_Q^{\rm away}\ll\frac1{\eta L^2}
\sum_{Q\le q<2Q}\frac{(q/\varphi(q))^2}{q}
\ll\frac1{\eta L^2}.
$$

This includes $\eta Q<1$. On each actual block keep the additional
$q>Q_j$ restriction: it only decreases that shell's coefficient
energy. The shell's separation cost is $O(Q^2)$, not $N^2$.
For the shell response $D_Q$ defined piecewise on these blocks,

$$
\|D_Q\|^2\ll V_Q^{\rm away}
\sum_j\frac{M_j+Q^2}{M_j^2}
\ll\frac1{\eta L^2}\left(\frac1N+\frac{Q^2}{N^2}\right).
$$

The full weighted norm is on $N\le m\le N^2$. Use its triangle
inequality across denominator shells only after this estimate.
There are $O(1+L)$ shells and $\sum_QQ\ll N$, so

$$
\left(\sum_j\|D_{N,\eta,j}\|_{I_j}^2\right)^{1/2}
\ll\frac1{\sqrt\eta\,L}
\left(\frac{1+L}{\sqrt N}+\frac{\sum_QQ}{N}\right)
\ll\frac1{\sqrt\eta\,L}.
\tag{I26}
$$

This uses the original large-sieve separation on every shell. It
avoids the extra logarithm that would result from applying the full
$N^2$ separation cost after merging all shell energies in (I25).
No improvement of arbitrary-coefficient separation by angular width
is assumed. The last block and endpoint $N^2$ remain included. Define the
retained response, for $m\in I_j$, by

$$
\mathcal C_{N,\eta}(m)=d_N+
\sum_{Q_j<q\le N}\ \sum_{\substack{1\le r<q\\(r,q)=1\\\|r/q\|<\eta}}
B_{N,q,r}e(mr/q).
$$

The deleted response is the sum of all low-denominator frequencies
and the high-denominator frequencies away from integers. These two
sets are disjoint; their functions need not be orthogonal on $I_j$.
Combining (I23), (I26) and the weighted triangle inequality yields

$$
\left|\sqrt{E_N}-\left(
\sum_{m=N}^{N^2}\frac{|\mathcal C_{N,\eta}(m)|^2}{m(m+1)}
\right)^{1/2}\right|
\ll\frac{N^{-1/4}}L+
\frac1{\sqrt\eta\,L}.
\tag{I27}
$$

All constants are independent of $N,\eta$. For example,
$\eta_N=(4\sqrt{\log N})^{-1}$ lies in $(0,1/4]$ for $N\ge3$,
and the right side is $O((\log N)^{-3/4})$. Thus an actual shrinking
angular region, together with the same complete-period mean, retains
the weighted norm up to a vanishing error. For the asymptotic choice
$\eta_N=(\log N)^{-a}$ this allowance tends to zero when $0<a<2$;
at $a=2$ it gives only $O(1)$. If $\eta\le1/N$, all nonzero
frequencies are deleted. The displayed angular allowance is then
at least $\sqrt N/L$; alternatively the unrestricted coefficient
bound (I20) gives the allowance $O(\sqrt N/L)$ directly. Taking an
arbitrarily narrow angular region therefore does not supply a
small-error reduction through these estimates.

The remaining frequencies satisfy both $q>\sqrt{M_j}$ and
$\|r/q\|<\eta_N$. They need not be nearly constant over a block:
$M_j\eta_N$ can grow. The symmetric angular cut preserves conjugate
pairing, so the retained and deleted responses remain real. It leaves all signed
correlations within the retained set and with $d_N$ unpaid. A bound
for an isolated reciprocal-phase Möbius sum would require a further
uniform summation and kernel correspondence before it could estimate
this complete norm. As with (I23), a uniform polylogarithmic bound
for the retained norm squared would still imply RH.

The earlier Mellin strength argument also has a quantitative
parameter substitution. For any one fixed $0\le\vartheta<1$, a bound
$E_N\ll N^\vartheta(1+\log N)^A$ for all sufficiently large integers
$N$, with one finite $A$, changes (I14) to
$\|S_y(qy)\|_2\ll y^{(1+\vartheta)/2}(1+\log y)^B$.
The same integral (I15) is then holomorphic for
$\Re s>(1+\vartheta)/2$, and (I16) excludes zeros in that strict
half-plane. Consequently any fixed power saving
$E_N\ll N^{1-\delta}(1+\log N)^A$, $0<\delta\le1$, would already
supply a fixed zero-free half-plane $\Re s>1-\delta/2$ at every
height. This is a parameter application of the preceding paper
argument, not an independently supplied bound. A saving parameter
that tends to zero with $N$ cannot be substituted for a fixed
$\delta$, and no conclusion on the boundary line is asserted.

This is a numerical-frequency observation of the same periodic
response. It is not the FIB composition rotation $C=MJ$, and no
arithmetic invariance under that active rotation is asserted. The
five-mode encoding can organize the retained indices without
supplying their Möbius cancellation. Equations (I25)–(I27) remain
paper applications of the cited existing inputs, without a new Lean
declaration or an originality claim.


## A numerator cut that follows the observation block

The same supplied inputs pay a narrower restriction on the circular
numerator $k(r,q)=\min(r,q-r)$, distinct from the angle $k(r,q)/q$.
For every integer $K\ge1$, the sine estimate used in (I25) gives

$$
\sum_{\substack{1\le r<q\\(r,q)=1\\k(r,q)>K}}
|B_{N,q,r}|^2\ll\frac{|b_{N,q}|^2}{K+1},\qquad
\sum_{2\le q\le N}\ \sum_{\substack{1\le r<q\\(r,q)=1\\k(r,q)>K}}
|B_{N,q,r}|^2\ll\frac{N}{(K+1)L^2}.
\tag{I28}
$$

Indeed, $|1-e(-r/q)|\ge4k(r,q)/q$, and at most two numerators have
a given positive $k$. Sum the tail of $k^{-2}$ and use the same
uniform $b_{N,q}$ bound and finite totient moment as in (I20).
When $K\ge q/2$ the corresponding tail is empty.

Fix $0<b<2$ and use the actual blocks and denominator cutoffs of
(I23). On block $I_j$, put

$$
K_j=\left\lceil\frac{N^2}{M_jL^b}\right\rceil.
$$

Let $G_{N,\eta,b,j}$ be the sum over the frequencies retained in
$\mathcal C_{N,\eta}$ for which $k(r,q)>K_j$, with their original
coefficients and phases. Its coefficient energy is bounded by (I28).
The original $N^{-2}$ separation, the actual weight and
$K_j+1\ge N^2/(M_jL^b)$ give

$$
\begin{aligned}
\sum_j\|G_{N,\eta,b,j}\|_{I_j}^2
&\ll\sum_j\frac{N(M_j+N^2)}{M_j^2(K_j+1)L^2}\\
&\ll L^{b-2}\left(\frac{1+\lfloor\log_2N\rfloor}{N}
+\sum_j\frac{N}{M_j}\right)
\ll L^{b-2}.
\end{aligned}
\tag{I29}
$$

The last geometric sum is at most two, and the other term is
uniformly bounded for $N\ge3$. Empty frequency sets
and the final singleton block require no exception.

Define $\mathcal C^{\rm num}_{N,\eta,b}$ on $I_j$ by retaining exactly
$q>Q_j$, $\|r/q\|<\eta$, and $k(r,q)\le K_j$, together with the
unchanged $d_N$. The added deletion intersects the previous retained
set, so no frequency is subtracted twice. Equations (I27)–(I29) give

$$
\left|\sqrt{E_N}-\|\mathcal C^{\rm num}_{N,\eta,b}\|\right|
\ll\frac{N^{-1/4}}L+
\frac1{\sqrt\eta\,L}
+L^{b/2-1}.
\tag{I30}
$$

Here the norm is the same weighted norm on the complete interval
$N\le m\le N^2$. The numerator deletion itself does not require an
angular restriction: dropping that restriction from its definition
still gives (I29), and comparison with the denominator-only retained
response has error $O(N^{-1/4}/L+L^{b/2-1})$.

For example, use $\eta=(4L^{3/2})^{-1}$ and $b=3/2$. The complete
comparison still costs $O(L^{-1/4})$, while the remaining circular
numerators also obey $k\le\lceil N/(2^jL^{3/2})\rceil$. For
$q\asymp N$ this restricts the angle to
$O(2^{-j}L^{-3/2}+N^{-1})$. This is a further paid restriction,
including an increasingly small numerator allowance on later blocks;
it is not a bound for the retained signed norm.

The original mean cannot be removed by rebinding the response at zero.
Although $R_N(0)=1$ and the exact full expansion can be written as
$1+\sum B_{N,q,r}(e(mr/q)-1)$, deleting a set in that expression
would remove $G(m)-G(0)$. Estimate (I29) controls $G(m)$ on the actual
blocks and does not separately control the constant $G(0)$.
Keeping the original $d_N$ preserves the paid estimate.

For $q>N/2$ the actual coefficient is
$b_{N,q}=\mu(q)\log(N/q)/L$. Even after (I30), the earliest block
contains $m\asymp N$, $k=1$, $q\asymp N$, with reciprocal-phase
parameter $mk\asymp N$. Results requiring a faster phase do not cover
that endpoint. The coprimality condition, exact Fourier kernel,
block-dependent cutoff and mean interaction all remain part of any
supplier obligation. This is a further application of the same cited
inputs, without a new supplier theorem, originality claim or Lean
verification.


## Reusing a known centered coefficient family

Ehm's [Gram-matrix and centering source](ehm2024grammatrices.md),
Section 8.2 and Proposition 8.1, already provides a correction to the
Selberg coefficients for centering the relevant moments. Its known
construction need not be reinvented. The linked application compares
that modified balanced family with the actual family here: the full
$L^2(0,1)$ norm cost is $O(1/\log N)$, and the difference of the
square roots of the actual local energies is
$O(\log N/\sqrt N)$, for any fixed correction constants.
The centering property additionally requires the source's stated
linear system. These allowances permit honest transfer of a future
complete estimate; the source leaves its signed inversion error
unestimated. They do not reuse the original squarefree Fourier
support for the modified coefficients, or supply the retained joint
bound in (I30).


## A complete energy allowance from the existing Mertens input

The [Ng source note](../Analytic/ng2004summatorymobius.md#reuse-of-the-unconditional-input)
already records the classical unconditional Vinogradov–Korobov
estimate for the actual $\mathcal M(x)=\sum_{n\le x}\mu(n)$.
Reuse it without proving a new Mertens theorem. For some fixed
$c_0>0$ and all sufficiently large $x$,

$$
|\mathcal M(x)|\ll x e^{-c_0\Xi(x)},\qquad
\Xi(x)=\frac{(\log x)^{3/5}}{(\log\log x)^{1/5}}.
$$

The existing source note also records the Lee–Leong v5 explicit
supplier. Only the asymptotic allowance above is used here; no
numerical constant or starting threshold is certified in this
application. It pays the following complete energy bound for the
original coefficients, mean and discrete weight:

$$
E_N\ll N e^{-c\Xi(N)}
\qquad\text{for some fixed }c>0.
\tag{I31}
$$

Here and below $N$ is a sufficiently large integer. To check the
actual parameters, fix $0<\kappa<c_0/8$ and put

$$
Y=N e^{-\kappa\Xi(N)},\qquad X=N e^{\kappa\Xi(N)}.
$$

Eventually $1<Y<N<X<N^2$. Uniformly for $Y\le x\le N$,
$\Xi(x)/\Xi(N)\to1$, since $\Xi(N)=o(\log N)$. Thus the known
Mertens input gives

$$
\sup_{Y\le x\le N}|\mathcal M(x)|
\ll N e^{-(c_0/2)\Xi(N)}.
$$

For the actual integer samples $N\le m\le X$, split the $n$-sum in
$R_N(m)$ at $Y$. Its part $n\le Y$ is bounded absolutely by $Y$.
On $[Y,N]$ set

$$
g_m(x)=\frac{\log(N/x)}L\{m/x\}.
$$

Its supremum plus total variation is $O(1+m/Y)$, including all
jumps. On smooth pieces the variation is bounded by
$\int_Y^N[1/(Lx)+m/x^2]dx$; there are $O(1+m/Y)$ jumps of size
at most one. Discrete Abel summation uses the actual values $g_m(n)$,
so no continuity convention at shared integer jumps is required.
The boundary $\mathcal M(\lfloor Y\rfloor)=\mathcal M(Y)$ is also
covered by the displayed bound. Consequently

$$
\begin{aligned}
|R_N(m)|
&\ll 1+Y+N e^{-(c_0/2)\Xi(N)}(1+m/Y)\\
&\ll N e^{-\kappa\Xi(N)}\qquad(N\le m\le X).
\end{aligned}
$$

The last step uses $m/Y\le e^{2\kappa\Xi(N)}$ and
$c_0/2>3\kappa$. The original telescoping weight now gives

$$
\sum_{N\le m\le X}\frac{|R_N(m)|^2}{m(m+1)}
\ll N e^{-2\kappa\Xi(N)}.
$$

For the entire remaining range $X<m\le N^2$, use
$|R_N(m)|\le1+N$ and
$\sum_{m>X}1/[m(m+1)]\le1/X$. Its energy is therefore at most
$O(N^2/X)=O(N e^{-\kappa\Xi(N)})$, proving (I31).
This argument never separates or optimizes the actual mean and
cross terms; it bounds the original residual itself.

For every fixed $A>0$, (I31) implies $E_N\ll_A N/(\log N)^A$.
This is a complete allowance, stronger than any one fixed
logarithmic saving, but supplies no fixed power saving:
$c\Xi(N)/\log N=c(\log N)^{-2/5}(\log\log N)^{-1/5}\to0$.
It therefore supplies neither the uniform polylogarithmic energy
needed by the earlier strength argument nor a fixed zero-free
half-plane. The exact FIB approximation rate and the same-integer
signed Robin estimate remain unresolved. Equation (I31) is a paper
application of the already owned classical input, without a new
Mertens result, originality claim or Lean certification.

## Classical RH errors calibrate the first proportional block

For the original coefficients and residual of (I10), distinguish the
first proportional block from the complete window:

$$
E_N^{\rm first}:=
\sum_{m=N}^{2N}\frac{|R_N(m)|^2}{m(m+1)}.
\tag{I32}
$$

The classical inputs are the RH consequences
$M(t)=\sum_{n\le t}\mu(n)\ll_\delta t^{1/2+\delta}$ for every fixed
$\delta>0$, and $\psi(t)-t\ll\sqrt t\log^2t$, where
$\psi(t)=\sum_{k\le t}\Lambda(k)$. Both are stated in
[Conrey, *Riemann's Hypothesis*, Section 3, printed p.6](https://aimath.org/~kaur/publications/90.pdf),
author draft of 28 April 2019, PDF SHA256
`6a704095b7359d17e27bd54eae3116c2ba621d2499e0b3c61c9c3a66c30619dc`.
They are reused, without a weak-Mertens mean-square hypothesis, zero
simplicity or a reciprocal-$\zeta'$ moment condition. The calculation
below is a paper application to the specified local residual, not an
originality claim for these classical criteria or a Lean certification.

A related discrete-window precedent is
[Gallardo-Gutiérrez–Seco, arXiv:2206.02654v6, Theorem 3.1 and (15),
printed pp.9–10](https://arxiv.org/pdf/2206.02654v6). At its parameter
$\sigma=1/2$, (15) uses the same weight $1/[m(m+1)]$ on a moving
window. Its residual, however, is
$1+\sum_{k\le N}\mu(k)(\{m/k\}-N\{m/N\}/k)$, without the
logarithmic Selberg coefficients. Its bound is used along a selected
subsequence. Neither identical cell weights nor that subsequence
supplies a bound for (I32).

Retain $U_N$ from (I12). The classical convolution identity
$\sum_{d\mid k}\mu(d)\log(N/d)=\Lambda(k)+L\mathbf1_{k=1}$ gives

$$
L R_N(m)=mU_N-\psi(m)+\mathcal T_N(m),\qquad
\mathcal T_N(m)=\sum_{N<n\le m}\mu(n)\log(N/n),\quad N\le m\le2N.
\tag{I33}
$$

Indeed, the full divisor sum over $k\le m$ is $\psi(m)+L$.
Its omitted $n>N$ terms have $\lfloor m/n\rfloor=1$ throughout this
block, including $m=2N$; the logarithmic weight at $n=N$ is zero.
Substitution in the exact residual formula gives (I33).

Under RH fix $0<\delta<1/2$. The Dirichlet identity for $1/\zeta$
and its derivative at 1 give the classical normalizations
$\sum\mu(n)/n=0$ and $\sum\mu(n)\log n/n=-1$; convergence and local
differentiation follow from the quoted Mertens bound. Abel summation
then gives the exact tails

$$
\begin{aligned}
U_N-1
&=\sum_{n>N}\frac{\mu(n)\log(n/N)}n
=-\int_N^\infty M(t)\frac{1-\log(t/N)}{t^2}\,dt
\ll_\delta N^{-1/2+\delta},\\
\mathcal T_N(m)
&=M(m)\log(N/m)+\int_N^m\frac{M(t)}t\,dt
\ll_\delta N^{1/2+\delta}.
\end{aligned}
\tag{I34}
$$

The second bound is uniform on $N\le m\le2N$. Combining (I33)–(I34)
with the quoted Chebyshev error and
$\sum_{m=N}^{2N}1/[m(m+1)]\le1/N$ yields

$$
E_N^{\rm first}\ll_\delta
\frac{N^{2\delta}}{L^2}+L^2.
\tag{I35}
$$

In particular RH implies $E_N^{\rm first}\ll_\varepsilon N^\varepsilon$
for every fixed $\varepsilon>0$. Conversely, use the existing
(I11)–(I16) argument on $J=(5/4,7/4)$. For every fixed positive
$\varepsilon$ its norm bound is
$O_\varepsilon(y^{(1+\varepsilon)/2}(1+\log y)^B)$ with finite $B$.
For each $\Re s>1/2$ choose a fixed $\varepsilon<2\Re s-1$ and apply
(I15) on a neighborhood of $s$. Its no-common-zero argument gives RH.
Thus the calibrated paper equivalence is

$$
\mathrm{RH}\quad\Longleftrightarrow\quad
\text{for every }\varepsilon>0,\quad
E_N^{\rm first}\ll_\varepsilon N^\varepsilon
\quad\text{for all sufficiently large integers }N.
\tag{I36}
$$

Constants and the lower cutoff may depend on $\varepsilon$; neither
$\delta$ nor $\varepsilon$ varies with $N$ in the estimates used.
This supplies no converse for a fixed polylogarithmic allowance, no
RH bound for the entire window $N\le m\le N^2$, and no optimal
Nyman–Beurling approximation rate.

There is a stronger known supplier with additional assumptions,
already cited in the FIB source, Section 391.3:
[Bettin–Conrey–Farmer, arXiv:1211.5191v1, Theorem 1, printed p.2](https://arxiv.org/pdf/1211.5191v1).
It uses these same logarithmic coefficients. Set
$\mathcal F_N(x)=\mathbf1_{(0,1)}(x)+\sum_{n\le N}a_{N,n}\{1/(nx)\}$
on the half-line and $\mathcal D_N=\|\mathcal F_N\|_2^2$.
The classical Mellin–Plancherel dictionary identifies this with that
paper's critical-line integral. On $m\le t<m+1$, $m\ge N$, the
exact relation is
$\mathcal F_N(1/t)=R_N(m)+c_N(t-m)$. Thus, for
$J_N=\int_{1/(2N+1)}^{1/N}|\mathcal F_N(x)|^2dx$,

$$
\left|\sqrt{E_N^{\rm first}}-\sqrt{J_N}\right|
\le\frac{|c_N|}{\sqrt N},\qquad
E_N^{\rm first}\le2\mathcal D_N+\frac{2|c_N|^2}N.
$$

The lower endpoint is $1/(2N+1)$ because the sample $m=2N$ contributes
its whole cell. The cited theorem assumes RH and, for some
$\delta>0$, $\sum_{|\Im\rho|\le T}|\zeta'(\rho)|^{-2}\ll T^{3/2-\delta}$;
the latter includes zero simplicity. It supplies
$\mathcal D_N\sim(2+\gamma-\log(4\pi))/\log N$, and hence
$E_N^{\rm first}\ll1/\log N$ under those complete assumptions.
This reuses the known stronger supplier with a paid cell comparison;
it does not remove its extra hypothesis or assert a first-block
asymptotic with the same constant.

A fixed polylogarithmic first-block allowance also constrains zero
multiplicity. If $E_N^{\rm first}\ll L^A$ with fixed $A\ge0$, the same
cell calculation on $J$ gives
$\|S_y(y\,\cdot)\|_{L^2(J)}\ll\sqrt y(1+\log y)^{A/2+1}$.
For a zero $\rho$ on the critical line choose $h\in C_c^\infty(J)$
with $H_h(\rho)\ne0$ using (I16). The Mellin integral obeys
$F_h(\rho+u)=O_h(u^{-A/2-2})$ as $u\downarrow0$.
The meromorphic right side of (I15) has a pole of order $m_\rho$ at
$\rho$, so

$$
m_\rho\le\lfloor A/2+2\rfloor.
\tag{I37}
$$

This uses meromorphic continuation near $\rho$, not holomorphy on
the boundary. The test function may depend on $\rho$ without changing
the exponent. The every-$\varepsilon$ condition in (I36) has no
controlled $\varepsilon$-dependence from which to deduce (I37).
An extra uniform multiplicity consequence does not establish that
the fixed polylogarithmic condition is strictly stronger than RH.

## Five-mode resolution as a paid cutoff sampling interface

The five modes can specify a sufficiently dense set of actual cutoff
parameters. They do not change the Möbius coefficients inside any
cutoff. The following application reuses (I11), the canonical finite
Zeckendorf interval bound and the legal-word count in
[the FIB source, Sections 105–106](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md),
with canonical decoding owned by the
[existing golden-window note](../Digit/mathlib2026goldenwindows.md).
It claims neither special Fibonacci cancellation nor an original
sampling theorem.

First retain an integer $N\ge3$, allow real $y\ge N$, and put
$\Delta=y-N$. Unlike (I11), new dictionary indices may now enter.
For every real $t$ the exact difference is

$$
\begin{aligned}
S_y(t)-S_N(t)
={}&\log(y/N)\left(1+\sum_{n\le N}\mu(n)\{t/n\}\right)\\
&+\sum_{N<n\le y}\mu(n)\log(y/n)\{t/n\}.
\end{aligned}
$$

The first term has magnitude at most $2\Delta$. There are at most
$\Delta$ new indices, each with logarithmic weight at most
$\log(y/N)\le\Delta/N$. Hence

$$
|S_y(t)-S_N(t)|\le2\Delta+\frac{\Delta^2}N\le3\Delta
\qquad(0\le\Delta\le N),
\tag{I38}
$$

uniformly in $t$, including across fractional-part jumps.

Let a fixed set $\mathcal Q\subseteq\mathbb N_{\ge3}$ have the left
coverage property: for every sufficiently large real $y$, there is
$N\in\mathcal Q$ with
$0\le y-N\le C\sqrt N(\log N)^B$, for fixed $C>0$ and $B\ge0$.
For $q\in J=(5/4,7/4)$, every cell meeting $qy$ then has its integer
left endpoint in $[N,2N]$ once $N$ is sufficiently large. Use (I12),
the actual weight $1/[m(m+1)]$, $y\asymp N$, and (I38), to obtain

$$
\|S_y(y\,\cdot)\|_{L^2(J)}^2
\ll NL^2E_N^{\rm first}+(1+L)^4+\Delta^2.
\tag{I39}
$$

Consequently the right side of (I36), restricted to all sufficiently
large $N\in\mathcal Q$ for each fixed $\varepsilon$, still implies
RH by the same Mellin argument. RH supplies that restricted condition
by (I35). This transfers the required inner Mellin window, without
claiming to reconstruct every full moving first-block energy from
one left sample.

Here is a concrete $\mathcal Q$ using exactly the five occupancy
modes. Use $F_0=0,F_1=1$, keep the separate unit bit, and group
$F_3,F_4,F_5=2,3,5$ and their subsequent triples into windows. For
$L\ge1$ and each integer

$$
F_{6L+3}\le n<F_{6L+9},
$$

form $Q_L(n)$ by replacing the lowest $L$ windows by `null`, retaining
all higher digits and the unit bit. Deletion preserves the
nonadjacency rule and seams. The canonical finite interval bound gives

$$
0\le n-Q_L(n)<F_{3L+3}.
$$

The leading digit has index at least $6L+3$ and is not deleted;
therefore $Q_L(n)$ stays in the same annulus. The standard Fibonacci
square identity yields

$$
F_{3L+3}^2
=(F_{3L+1}+F_{3L+2})^2
\le2(F_{3L+1}^2+F_{3L+2}^2)=2F_{6L+3}
\le2Q_L(n).
$$

Let $\mathcal Q$ be the union of these images. Every real $y\ge34$
has $n=\lfloor y\rfloor$ in one of these annuli. With $N=Q_L(n)$,

$$
0\le y-N<1+\sqrt{2N}\le2\sqrt N.
\tag{I40}
$$

There are $3L+6$ remaining high slots, indexed $3L+3$ through
$6L+8$. The known nonadjacent-word count and at most two choices
of unit bit give
$|\mathcal Q\cap[F_{6L+3},F_{6L+9})|\le2F_{3L+8}$.
Thus each annulus needs only $O(\sqrt{F_{6L+3}})$ distinct cutoff
points; the constant includes its fixed scale ratio. Combining
(I35), (I39) and (I40) gives the paper application

$$
\mathrm{RH}\quad\Longleftrightarrow\quad
\text{for every }\varepsilon>0,\quad
E_N^{\rm first}\ll_\varepsilon N^\varepsilon
\quad\text{for all sufficiently large }N\in\mathcal Q.
\tag{I41}
$$

The truncation creates a different integer cutoff; (I38) pays for that
change of source. It is not a lossless coarse observation of the same
integer. Each $R_N$ still includes every original $n\le N$ with its
original coefficient. A single sequence such as $F_{3L}$ has gaps of
order $N$ and is not justified by this square-root coverage argument.
Nor does this replace the separate $\lfloor N/d\rfloor$ schedule
issue for Binet convolution transport in the FIB source, Section 391.
The unresolved task is an unconditional, uniform signed energy bound
on this fixed set; the digit-count and gap bounds do not supply it.
No new Lean declaration or certified RH implication is asserted here.
