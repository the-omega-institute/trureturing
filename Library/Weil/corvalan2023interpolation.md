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


## Bracketing cutoffs by the published derivative-variation bound

A stronger cutoff interface follows by directly applying
[S. S. Dragomir, *Bounds for the deviation of a function from the chord
generated by its extremities*, Bull. Austral. Math. Soc. 78 (2008),
225–248, Theorem 5.2, (5.5), printed pp.234–235](https://doi.org/10.1017/S0004972708000671).
For an absolutely continuous real function whose derivative has a
bounded-variation representative, that theorem bounds the endpoint
chord error by

$$
|f(z)-\operatorname{chord}_{a,b}f(z)|
\le\frac{(z-a)(b-z)}{b-a}\operatorname{Var}_{[a,b]}(f')
\le\frac{b-a}{4}\operatorname{Var}_{[a,b]}(f').
$$

The theorem includes piecewise linear functions; its sharpness example
is an absolute-value function. The supplier is this published bound,
not a new interpolation theorem. Its application here keeps the
original coefficients and cutoff family.

Fix integers $3\le A<B$, put $h=B-A$, and freeze the observation
argument $t>0$. In the logarithmic cutoff coordinate $x$,

$$
f_t(x)=S_{e^x}(t)
=x+\sum_{n\le B}\mu(n)\{t/n\}(x-\log n)_+,
\qquad \log A\le x\le\log B.
\tag{I42}
$$

This is absolutely continuous and piecewise linear. Its right-slope
representative has variation at most
$\sum_{A<n\le B}|\mu(n)|\{t/n\}\le h$; choosing this representative
also handles the endpoint hinges. For $A\le y\le B$, define

$$
\eta=\frac{\log(y/A)}{\log(B/A)},\qquad
P_y(t)=(1-\eta)S_A(t)+\eta S_B(t).
$$

Dragomir's theorem applies to (I42) and gives, uniformly in $t$,

$$
|S_y(t)-P_y(t)|
\le\frac h4\log(B/A)\le\frac{h^2}{4A}.
\tag{I43}
$$

The improvement over (I38) uses both endpoint functions. It does not
claim that one endpoint alone has this quadratic cutoff error.

Retain $J=(5/4,7/4)$. If $B/A<8/7$, then $yJ$ lies inside both
$[A,2A]$ and $[B,2B]$. For either $K=A$ or $K=B$, (I12), the exact
cell weights and $y\asymp K$ give

$$
\|S_K(y\,\cdot)\|_{L^2(J)}^2
\ll K(\log K)^2E_K^{\rm first}+(1+\log K)^4.
$$

Indeed, the cell containing each $qy$ has its integer left endpoint
in $[K,2K]$; changing from $dq$ to $dt/y$ costs $1/y$, while removing
the energy weight costs $O(K^2)$. The within-cell slope contributes
$O(|U_K|^2)$, bounded by the fourth logarithmic power. Convexity for
the endpoint mixture and (I43) now yield

$$
\|S_y(y\,\cdot)\|_{L^2(J)}^2
\ll\sum_{K\in\{A,B\}}K(\log K)^2E_K^{\rm first}
 +(1+\log A)^4+\frac{h^4}{A^2}.
\tag{I44}
$$

Consequently a fixed unbounded set of integer cutoffs with consecutive
gaps $B-A\ll A^{3/4}(\log A)^C$, for a fixed $C\ge0$, is enough for
the every-$\varepsilon$ condition: suppose that for each
$\varepsilon>0$ there are constants $C_\varepsilon,N_\varepsilon$
such that $E_N^{\rm first}\le C_\varepsilon N^\varepsilon$ for every
sampled $N\ge N_\varepsilon$. Apply this at both bracketing cutoffs.
Using a smaller fixed $\varepsilon$ to absorb logarithms, (I44) gives
$\|S_y(y\,\cdot)\|_2^2\ll_\varepsilon y^{1+\varepsilon}$ for every
sufficiently large real $y$. The existing (I15)–(I16) argument excludes
zeros in $\Re s>1/2$ by choosing $\varepsilon<2\Re s-1$.
This is another paid cutoff application of that argument, not an
unconditional estimate for $E_N^{\rm first}$.

### A coarser grid using the actual five occupancy modes

The same canonical interval and legal-word bounds cited above supply
a concrete bracketing grid. For $L\ge1$ and each integer

$$
F_{12L+3}\le n<F_{12L+15},
$$

replace the lowest $3L$ triple windows by `null`, keeping all higher
digits and the separate unit bit. Write the output as
$\widetilde Q_L(n)$ and the union of these images as
$\mathcal Q_{\rm chord}$. The deleted positions are exactly
$F_3,\ldots,F_{9L+2}$, so the canonical interval bound gives

$$
0\le n-\widetilde Q_L(n)<F_{9L+3}.
$$

The leading digit has index at least $12L+3$, survives deletion, and
keeps the output in the original annulus. The elementary Fibonacci
bounds $\varphi^{k-2}\le F_k\le\varphi^{k-1}$ for $k\ge2$ imply

$$
F_{9L+3}\le\varphi^{5/4}\widetilde Q_L(n)^{3/4}.
$$

These annuli cover all integers at least $F_{15}=610$. Thus every
real $y\ge610$ has a sampled $N\le y$ with

$$
0\le y-N<(1+\varphi^{5/4})N^{3/4}.
\tag{I45}
$$

The lower endpoint of every annulus is itself retained. For consecutive
sampled points $A<B$, let $y\uparrow B$ through $(A,B)$. Every left
sample supplied by (I45) is at most $A$; monotonicity of
$x+(1+\varphi^{5/4})x^{3/4}$ gives
$B-A\le(1+\varphi^{5/4})A^{3/4}$. In particular $B/A\to1$, as
required for (I44); there is no cross-annulus gap exception.

The remaining high slots run from $9L+3$ through $12L+14$, a total
of $3L+12$ slots. The existing nonadjacent-word count and at most two
unit choices give

$$
|\mathcal Q_{\rm chord}\cap[F_{12L+3},F_{12L+15})|
\le2F_{3L+14}=O(F_{12L+3}^{1/4}).
\tag{I46}
$$

Combining the supplied conditional converse (I35) with (I44)–(I46)
therefore gives the paper application

$$
\mathrm{RH}\quad\Longleftrightarrow\quad
\text{for every }\varepsilon>0,\quad
E_N^{\rm first}\ll_\varepsilon N^\varepsilon
\quad\text{for all sufficiently large }N\in\mathcal Q_{\rm chord}.
\tag{I47}
$$

The gain is a coarser sufficient cutoff grid: $O(N^{1/4})$ points per
fixed-ratio annulus instead of the $O(N^{1/2})$ grid used with the
one-sided bound. Every sampled residual still uses all original
indices $n\le N$, with their original signed Möbius coefficients.
No digital orthogonality or special Fibonacci cancellation is assumed.
Both bracketing energies must be controlled uniformly; an almost-all
cutoff estimate cannot be substituted for that condition. The known
unconditional allowance (I31) remains insufficient, and no new
sufficient unconditional energy estimate or RH proof is supplied.
These are source-checked paper applications, without Lean certification.


## A paid deletion of original endpoint responses

The stronger all-short-interval Möbius saving recorded in the
[existing short-interval source](../Analytic/shortuniformity2026robininterfaces.md#a-stronger-error-on-longer-mobius-intervals)
controls an actual signed part of the original residual. This is an
application of that classical estimate, not a new Möbius theorem.
It uses the original centered response atoms from (I17)–(I18),
including all their Fourier aliases, rather than just a pair of
frequencies.

Set $L=\log N$ and $\Omega(N)=(L/\log L)^{1/3}$ for sufficiently
large integer $N$. Fix $0<\eta<1/24$, and take integer $Q,H$ with

$$
N/2<Q<Q+H\le N,\qquad H\ge Q^{7/12+2\eta}.
$$

The cited estimate with $\theta=7/12+\eta$ gives a constant
$c=c_\eta>0$ such that

$$
\max_{0\le u\le H}
\left|\sum_{Q<n\le Q+u}\mu(n)\right|
\ll_\eta H e^{-c\Omega(N)}.
\tag{I48}
$$

Here the maximum can be taken over integer $u$. For
$u\ge Q^{7/12+\eta}$, apply the source directly at the same start $Q$.
For shorter prefixes, the trivial bound is at most
$Q^{7/12+\eta}\le H Q^{-\eta}$. This power surplus absorbs the
exponential allowance since $\Omega(N)=o(\log N)$ and $Q\asymp N$.
The constant $c$ incorporates that scale comparison. Thus (I48)
is uniform over all the prefixes required by summation by parts;
it is not merely a bound for one full interval.

For the actual integer observations $N\le m\le2N$, define the
original-index centered band

$$
G_{N,Q,H}(m)=
\sum_{Q<n\le Q+H}\frac{\mu(n)\log(N/n)}L
 \left(\{m/n\}-\frac{n-1}{2n}\right).
\tag{I49}
$$

To apply (I48), retain the actual real weight

$$
w_m(x)=\frac{\log(N/x)}L
 \left(\frac{m+1/2}{x}-\lfloor m/x\rfloor-\frac12\right).
$$

On $[Q,Q+H]$, the ratio $m/x$ lies in $[1,4)$, so there are only
finitely many floor thresholds. On each smooth piece,
$|w_m'(x)|\ll1/(NL)$; every jump has magnitude $O(1/L)$.
The actual values at integer thresholds are the left-limit values,
and are included in its bounded variation. Consequently, uniformly
in $m,Q,H$,

$$
\|w_m\|_\infty+\operatorname{Var}_{[Q,Q+H]}(w_m)\ll L^{-1}.
$$

If $Q=N-H$, then $\log(N/x)\ll H/N$ throughout the band. Each
jump gains that factor, and integration of the continuous derivative
costs $O(H/(NL))$. Thus the endpoint band has the stronger bound

$$
\|w_m\|_\infty+\operatorname{Var}_{[N-H,N]}(w_m)
\ll\frac{H}{NL}.
\tag{I50}
$$

Discrete Abel summation uses the actual values $w_m(n)$, so it does
not discard any floor jump or endpoint. Combine (I48)–(I50) with
$\sum_{m=N}^{2N}1/[m(m+1)]<1/N$. In the same weighted first-block
norm as $E_N^{\rm first}$, this gives

$$
\begin{aligned}
\|G_{N,Q,H}\|_{\rm first}^2
 &\ll_\eta\frac{H^2}{NL^2}e^{-2c\Omega(N)},\\
\|G_{N,N-H,H}\|_{\rm first}^2
 &\ll_\eta\frac{H^4}{N^3L^2}e^{-2c\Omega(N)}.
\end{aligned}
\tag{I51}
$$

For any fixed $0<\lambda<c/2$, take an integer bandwidth
$H\asymp N^{3/4}e^{\lambda\Omega(N)}$. This satisfies the required
length and endpoint conditions eventually, because
$7/12+2\eta<3/4$ and $H=o(N)$. The second estimate gives

$$
\|G_{N,N-H,H}\|_{\rm first}^2
\ll_\eta L^{-2}e^{-(2c-4\lambda)\Omega(N)}=o(1).
\tag{I52}
$$

By comparison, summing absolute values before using Möbius cancellation
only gives the allowance $H^4/(N^3L^2)$, which at this bandwidth is
$\asymp L^{-2}e^{4\lambda\Omega(N)}$ and does not certify vanishing.
Thus the signed input pays an additional, quantitatively larger band.
Here $H$ is the width of the original dictionary-index band, not the
cutoff sampling gap used in (I43)–(I47).

Write $G_N=G_{N,N-H,H}$ and $Z_N=R_N-G_N$ on the same first block.
The full-period zero-frequency coefficient $d_N$ of (I17) is retained:
each original centered atom has zero mean on a common multiple of its
period. The mean over the first observation block need not be retained.
All remaining coefficients keep the original logarithmic cutoff $N$;
$Z_N$ is not identified with a residual reweighted at cutoff $N-H$.
The exact comparison is

$$
\begin{aligned}
E_N^{\rm first}
 &=\|Z_N\|_{\rm first}^2
   +2\Re\langle Z_N,G_N\rangle_{\rm first}
   +\|G_N\|_{\rm first}^2,\\
\left|\sqrt{E_N^{\rm first}}-\|Z_N\|_{\rm first}\right|
 &\le\|G_N\|_{\rm first}=o(1).
\end{aligned}
\tag{I53}
$$

A small norm of $G_N$ does not assert an $o(1)$ difference of squared
energies without a bound for the remaining norm and cross term.
Nor does it bound arbitrary Fourier subparts of $G_N$: an original
index $n$ includes reducible fractions $h/n$, so this is not a pure
band of reduced Fourier denominators. All those aliases travel together.

This pays one original-response deletion and leaves the other source
indices and their interaction with $d_N$ in $Z_N$. It gives no improved
complete-energy allowance over (I31), no sufficient unconditional
RH energy estimate and no same-integer signed Robin estimate.
The source application and derivation here are not Lean-certified.


## Pay the terminal covariance while retaining the endpoint

The [same short-interval source](../Analytic/shortuniformity2026robininterfaces.md#a-stronger-error-on-longer-mobius-intervals)
also records the Huxley prime-error estimate needed here. Reuse that
input and (I33), rather than replacing the original residual by a
separately centered or optimized one. The following application pays
the terminal fluctuation in the mixed term; two actual local moments
and the endpoint value remain.

Keep the same $N,L,\Omega(N)$ and $G_N$ as in (I48)–(I53), and put
$Q=N-H$, $K=2N$, $w_m=1/[m(m+1)]$. In this section choose a common
constant $c_\star>0$, small enough for the Möbius bound at $Q$, the
Möbius and prime-error bounds at $2Q$, and their scale comparisons.
This can decrease the constant $c$ used in (I48). Fix

$$
0<\lambda<c_\star/2,\qquad
H\asymp N^{3/4}e^{\lambda\Omega(N)},\qquad H\in\mathbb N.
$$

All statements are for sufficiently large integer $N$. In particular,
$H<N/3$. This is an explicitly restricted parameter family, not a
claim for every $\lambda$ allowed by the unreduced constant in (I52).

For auxiliary sums up to $2N$, write
$b_n=\mu(n)\log(N/n)$, always with the original cutoff $N$. Define

$$
A=\sum_{Q<n\le N}\frac{b_n}{n},\qquad
B=\sum_{Q<n\le N}b_n,\qquad
S_m=\sum_{Q<n\le m/2}b_n.
$$

The last sum is empty before the terminal interval. For $Q<n\le N$ and
$N\le m\le K$, $1\le m/n<3$, so
$\lfloor m/n\rfloor=1+\mathbf1_{2n\le m}$. The exact centered-atom
formula therefore gives

$$
LG_N(m)=(m+\tfrac12)A-\tfrac32B-S_m.
\tag{I54}
$$

Let $r=R_N(K)$ and keep the actual local moments

$$
P_0=\sum_{m=N}^{K}w_mR_N(m),\qquad
P_1=\sum_{m=N}^{K}w_m(m+\tfrac12)R_N(m).
$$

No assertion sets either moment to zero. Interchanging finite sums
and telescoping the original weight, including the sample $m=2n$,
gives

$$
D:=\sum_{m=N}^{K}w_mS_m
=\sum_{Q<n\le N}b_n\left(\frac1{2n}-\frac1{K+1}\right)
=\frac A2-\frac B{K+1}.
\tag{I55}
$$

Set $C_{N,H}=\langle R_N,G_N\rangle_{\rm first}$. These quantities
are real, and the exact mixed decomposition is

$$
\begin{aligned}
C_{N,H}&=\mathcal A_{N,H}
-\frac1L\sum_{m=N}^{K}w_mS_m(R_N(m)-r),\\
\mathcal A_{N,H}
&=\frac1L\left[
A(P_1-r/2)-B\left(\tfrac32P_0-\frac r{K+1}\right)
\right].
\end{aligned}
\tag{I56}
$$

In particular, the endpoint has been retained in $\mathcal A_{N,H}$;
subtracting it inside the terminal fluctuation has not removed it
from the original mixed term.

On the support of $S_m$ define

$$
V_\mu(m)=\sum_{m<n\le K}b_n,\qquad
V_\Lambda(m)=\psi(K)-\psi(m)-(K-m).
$$

Subtract (I33) at $m$ and $K$, using its original $U_N$. This yields

$$
L(R_N(m)-r)
=-(K-m)(U_N-1)+V_\Lambda(m)-V_\mu(m).
\tag{I57}
$$

Here the terms $b_n$ with $n>N$ occur only in the auxiliary identity
(I33); no new dictionary atoms or reweighted cutoff are introduced.

The prefix argument of (I48), applied at $Q$ and $2Q$, and discrete
Abel summation give

$$
\sup_m|S_m|\ll_\eta\frac{H^2}{N}e^{-c_\star\Omega(N)},\qquad
\sup_{2Q\le m\le K}|V_\mu(m)|
 +\sup_{2Q\le m\le K}|V_\Lambda(m)|
\ll_\eta H e^{-c_\star\Omega(N)}.
$$

For the second assertion the source interval starts at $2Q$ and has
length $2H$. Differences of its prefixes give the terminal sums.
The weight $\log(N/n)$ has bounded supremum plus variation on that
interval. Short prefixes for $\Lambda-1$ have the trivial bound
$O(u\log N)$; the fixed power margin between the source exponent
$7/12+\eta$ and $H\ge N^{7/12+2\eta}$ absorbs this logarithm and the
exponential allowance. Thus an all-prefix prime-error bound is used,
not just a bound for the full interval.

The unconditional VK–Mertens input already used in (I31) also pays
the exact tail from (I34), with its estimate changed to

$$
U_N-1=-\int_N^\infty M(t)
       \frac{1-\log(t/N)}{t^2}\,dt
\ll e^{-b\Xi(N)}\qquad\text{for some }b>0.
$$

Indeed that input makes the Abel tail integral absolutely convergent
and gives the normalizations $\sum\mu(n)/n=0$ and
$\sum\mu(n)\log n/n=-1$ by taking the right-hand limits of
$1/\zeta(s)$ and its derivative at $s=1$. After substituting
$u=\log t$, absorb the polynomial factor in
$\int_L^\infty(1+u)e^{-c_0\Xi(e^u)}du$ by decreasing the positive
exponential constant. No RH estimate from (I34) is used.

There are at most $2H$ samples with $S_m\ne0$, their total weight is
$O(H/N^2)$, and $K-m\le2H$ on this support. Consequently (I56)–(I57)
give the quantitative paid remainder

$$
\left|C_{N,H}-\mathcal A_{N,H}\right|
\ll_\eta\frac{H^4}{N^3L^2}
\left(e^{-2c_\star\Omega(N)}
     +e^{-b\Xi(N)-c_\star\Omega(N)}\right).
\tag{I58}
$$

This bounds the actual products on their common support; no
independence or separate optimizing configuration is assumed.
At the stated bandwidth the first allowance tends to zero since
$4\lambda<2c_\star$, and the second does so because
$\Xi(N)/\Omega(N)\to\infty$. Reuse (I52) for the smaller common
constant to obtain

$$
C_{N,H}=\mathcal A_{N,H}+o(1),\qquad
E_N^{\rm first}-\|R_N-G_N\|_{\rm first}^2
=2\mathcal A_{N,H}+o(1).
\tag{I59}
$$

The second identity retains the mean interaction already present in
(I53). It supplies an $o(1)$ error for replacing the terminal
covariance by its endpoint contribution, not an $o(1)$ estimate for
the complete mixed term or squared-energy difference. The unpaid
quantity is $\mathcal A_{N,H}$ with the displayed jointly realized
$A,B,P_0,P_1,r$. The old pointwise input for $R_N$ still gives only
an allowance of order
$H^2e^{-\kappa\Xi(N)-c_\star\Omega(N)}/(NL)$ for the complete mixed
term, which does not certify vanishing at this bandwidth. Full-space
moment centering does not set these local moments or endpoint to zero.
This is an application of existing short-interval estimates and the
owned residual identity, without a new distribution theorem,
originality claim, sufficient unconditional RH energy bound,
same-integer signed Robin estimate or Lean certification.

## Fixed-half-plane inputs sharpen the actual energy benchmark

The already recorded [OpenAI source](../Analytic/openai2026quasirh.md)
states a zero-free half-plane with boundary $7/8$. The
[Liu v2 source](../Analytic/liu2026quasirh.md), Theorem 27.1, improves
that boundary to $B_{\rm new}=0.874957019420098946\ldots$.
Use these as paper-level inputs, with their strict boundary and
principal-pole qualifications retained. Neither external Lean
closure has been independently compiled here. The following applies
those existing inputs to the actual family (I10); it is not a new
zero-free-region or Mertens theorem.

Here is the ordinary-integer analytic interface, including the
parameter change needed to use a fixed boundary other than $1/2$.
Suppose $1/2\le B<1$ and $\zeta$ has no zero in $\Re s>B$.
The classical zero-free-half-plane/Perron argument gives, for every
fixed $B<\beta<1$,

$$
M(x)\ll_\beta x^\beta,\qquad
\psi(x)-x\ll_\beta x^\beta.
\tag{I60}
$$

This is not obtained by simply renaming the RH exponent in the
Conrey quotation. The [fixed source snapshot's
logarithmic-control proof](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex),
label `lem:logarithmic-control`, supplies the classical disk argument:
Borel--Caratheodory followed by three circles uses a nonvanishing
regularized function, polynomial strip growth, and a bounded Euler
logarithm on a fixed disk to the right of one. Its stated functions
are Hecke functions and regularized $\zeta_F$, not the ordinary
integer Mertens function. To apply that argument here, use instead
$F(s)=(s-1)\zeta(s)/(s+1)$, with its removable nonzero value at one.
It has those same elementary growth and Euler-logarithm properties
and is nonvanishing on $\Re s>B$.
For any fixed $\sigma_0>B$ and $\eta>0$, the argument gives
$1/\zeta(\sigma+it)\ll_{\sigma_0,\eta}(3+|t|)^\eta$
on $\sigma\ge\sigma_0$; Cauchy's estimate also bounds the
logarithmic derivative by $O_{\sigma_0}(\log(3+|t|))$ on fixed
sub-strips away from the pole at one.

For the remaining interface reuse Koukoulopoulos,
[*The Distribution of Prime Numbers*, author's authorized preliminary
version](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf),
Theorem 7.2, printed p.71. The inspected PDF has SHA256
`1445e107bba9c89db6529aeb4bca3ecf01170fc2854a675f5ca6f288c77ea0a8`.
Its coefficient condition holds with $f(n)=\mu(n)$ and
$\theta=A=0$. Choose $B<\sigma_0<\beta$, initial line
$c=1+1/\log x$, and height $T=x^2$.
The shifted vertical integral is $O(x^{\sigma_0}T^\eta\log T)$,
the horizontal integrals are $O(xT^{\eta-1})$, and that theorem's
truncation error is $O(x\log x/T+1)$.
Take $0<\eta<(\beta-\sigma_0)/4$ to obtain the Mertens part of
(I60), with no residue at one for $1/\zeta$.
For the prime error directly use the same book's explicit formula,
Theorem 5.1, printed p.57, and its zero-counting Lemma 8.2(a),
printed p.84. With $T=x^2$ and $\Re\rho\le B$ they give
$\psi(x)-x\ll x^B\log^2x$, retaining every multiplicity and the
main term $x$. Absorbing the logarithm gives the second part of
(I60). Thus neither Perron nor the prime explicit formula is
reproved here. Only their ordinary-$\zeta$ parameter interface is
made explicit; the source's Hecke lemma is not quoted as a theorem
about ordinary integer Mertens sums.

Apply (I60) first to the exact identity (I33). Since $\beta<1$,
the same Abel tails and normalizations used in (I34) converge, now
with
$U_N-1\ll_\beta N^{\beta-1}$ and
$\mathcal T_N(m)\ll_\beta N^\beta$ uniformly on $N\le m\le2N$.
Thus the actual residual, including its mean and endpoint, satisfies
$|R_N(m)|\ll_\beta N^\beta/L$ there, and
$E_N^{\rm first}\ll_\beta N^{2\beta-1}/L^2$.

For the complete window reuse the bounded-variation splitting of
(I31), without changing any coefficient. Set $X=N^{2-\beta}$.
At each actual sample $N\le m\le X$, use
$Y=\sqrt{mN^\beta}$, so $1\le N^\beta\le Y\le N$.
The lower part has absolute bound $Y$ and the upper part uses
$\sup_{Y\le t\le N}|M(t)|\ll_\beta N^\beta$ with the already
proved variation allowance $O(1+m/Y)$. Consequently

$$
|R_N(m)|\ll_\beta 1+Y+N^\beta(1+m/Y)
\ll_\beta\sqrt{mN^\beta}.
$$

The original weight gives at most $O_\beta(N^\beta\log N)$ on this
range. On the whole remaining range $X<m\le N^2$, the existing
$|R_N(m)|\le1+N$ and telescoping weights give
$O(N^2/X)=O(N^\beta)$. Floors and ceilings at $X,Y$ only change
fixed constants. Choosing $\beta>B$ sufficiently close to $B$
and absorbing the logarithm yields, for every fixed $\varepsilon>0$,

$$
E_N^{\rm first}\ll_\varepsilon N^{2B-1+\varepsilon},\qquad
E_N\ll_\varepsilon N^{B+\varepsilon}.
\tag{I61}
$$

For $B=7/8$ these exponents are $3/4+\varepsilon$ and
$7/8+\varepsilon$. The stated Liu boundary gives respectively
$0.749914038840197892\ldots+\varepsilon$ and
$0.874957019420098946\ldots+\varepsilon$.
These fixed power savings improve the benchmark (I31) when its
classical VK input is supplemented by the cited fixed-half-plane
results. They neither alter what (I31)'s own input supplies nor
attain the every-$\varepsilon$ subpower first-block estimate (I36).
In particular $B_{\rm new}>1/2$ leaves a positive power in the
first-block allowance. Combining it with (I52) also fails to certify
vanishing of the full mixed term at the bandwidth of (I59).
The actual joint main term $\mathcal A_{N,H}$, the same-integer
signed Robin estimate, and RH remain unresolved. This is a scoped
application of the cited analytic inputs, without a mathematical
priority claim or Lean certification.

## A coupled Perron kernel for the unpaid joint main term

Retain the actual $A,B,P_0,P_1,r$ and $\mathcal A_{N,H}$ of (I56),
and the bandwidth and common constant of (I58)--(I59). Reuse the
Mellin kernel $H_q$ of (I15). Symmetric Mellin/Perron inversion is
used only at a fixed integer $N$ here; no zero-sum or contour-shift
estimate is assumed. This applies the classical inversion interface
to the jointly realized functional, rather than replacing its
coefficients or centering its local moments.

Put
$$
a=\frac{Q+1/2}{N},\qquad h=1-a=\frac{H-1/2}{N},\qquad
W_a(s)=\int_a^1x^{s-1}\log(1/x)\,dx
=\frac{1-a^s(1+s\log(1/a))}{s^2},
$$
with the removable value at zero. Write
$\mathscr P_s F=(2\pi i)^{-1}\lim_{T\to\infty}
\int_{c-iT}^{c+iT}F(s)\,ds$ for a fixed $c>1$.
The exact band inversion is
$$
B=\mathscr P_s\frac{N^sW_a(s)}{\zeta(s)},\qquad
A=\mathscr P_s\frac{N^{s-1}W_a(s-1)}{\zeta(s)}.
\tag{I62}
$$
The half-integer lower cut selects exactly $Q<n\le N$; the upper
weight is zero. Thus no lower-boundary half weight or changed
cutoff is hidden in this formula.

The residual inversion needs an additional integer-jump term. Set
$$
J_m=\sum_{\substack{n\mid m\\n\le N}}b_n
=\Lambda(m)-\mathbf1_{m>N}\mu(m)\log(N/m).
$$
The equality holds throughout $N\le m\le2N$, including both
endpoints: any omitted divisor must be $m$ itself. Then
$$
LR_N(m)=L-\frac{J_m}{2}
+\mathscr P_s\frac{N^sH_{m/N}(s)}{\zeta(s)}.
\tag{I63}
$$
Indeed, invert $\log v\{qv\}$ supported on $v\ge1$ and use the
absolutely convergent Dirichlet series on $\Re s=c$. At $n\mid m$
the fractional part jumps down by one, so symmetric inversion
returns its two-sided average and must be corrected by $-b_n/2$.
The factor $\log(N/N)=0$ removes a separate upper-cutoff jump.
For fixed $N$ these inversion limits follow from local bounded
variation and integrability in logarithmic coordinates.

For any function specified on the actual grid $m/N$, define
$$
\begin{aligned}
\mathfrak p_N(f)&=
\sum_{m=N}^{2N}w_m(m+\tfrac12)f(m/N)-\tfrac12f(2),\\
\mathfrak q_N(f)&=
\tfrac32\sum_{m=N}^{2N}w_mf(m/N)-\frac{f(2)}{2N+1},\\
p_N(v)&=\mathfrak p_N(H_\bullet(v)),\qquad
q_N(v)=\mathfrak q_N(H_\bullet(v)).
\end{aligned}
\tag{I64}
$$
Let $Z(m/N)=1-J_m/(2L)$ and set
$$
\begin{aligned}
\mathcal K_N(u,v)&=W_a(u-1)p_N(v)-NW_a(u)q_N(v),\\
E_{\rm grid}&=\frac{A\mathfrak p_N(Z)-B\mathfrak q_N(Z)}L.
\end{aligned}
$$
Substitution into (I56) gives the exact jointly signed expression
$$
\mathcal A_{N,H}=E_{\rm grid}
+\frac1{L^2}\mathscr P_u\mathscr P_v
\frac{N^{u+v-1}\mathcal K_N(u,v)}{\zeta(u)\zeta(v)}.
\tag{I65}
$$
Here the double symbol means the rectangular limit with independent
heights $T_u,T_v\to\infty$. Each finite double integral separates
into products of one-variable integrals from (I62)--(I64), whose
limits exist for this fixed $N$. This proves that rectangular limit,
without asserting absolute convergence, exchanging $N\to\infty$
with it, or authorizing a spectral contour shift. Both actual
$H_2$ endpoint terms remain present in $p_N$ and $q_N$.

There is a paid part of (I65). Since $J_m=O(L)$,
$\|Z\|_\infty=O(1)$, $\|\mathfrak p_N\|=O(1)$ and
$\|\mathfrak q_N\|=O(N^{-1})$. Reuse the short-interval bounds
underlying (I58), namely
$|A|\ll H^2N^{-2}e^{-c_\star\Omega}$ and
$|B|\ll H^2N^{-1}e^{-c_\star\Omega}$. They give
$$
E_{\rm grid}\ll
\frac{H^2}{N^2L}e^{-c_\star\Omega}=o(1).
\tag{I66}
$$
This pays the integer-jump and constant terms; it does not pay the
remaining double integral or replace $Z$ by a local mean.

The low-frequency kernel has an explicit calibration. Put
$$
\Phi(v)=\int_1^2\frac{q-3/2}{q^2}H_q(v)\,dq.
$$
Uniformly for $u$ in a fixed compact subset of $\mathbb C$ and $v$
in a fixed compact subset of $\Re v>0$, including any fixed order
of mixed derivatives, Taylor expansion and Riemann summation give
$$
\mathcal K_N(u,v)=\frac{h^2}{2}\Phi(v)
+O_{u,v}(h^3+h^2/N).
\tag{I67}
$$
In particular $p_N(v)-Nq_N(v)=\Phi(v)+O_v(1/N)$. Its endpoint
coefficient is $-1/2+N/(2N+1)=O(1/N)$, so this leading cancellation
has not deleted the endpoint from the exact formula.

For fixed simple nontrivial zeros $\rho,\sigma$, the corresponding
ordered double residue of the meromorphic integrand in (I65), with
the factor $L^{-2}$ included, is consequently
$$
\frac{H^2N^{\rho+\sigma-3}}{2L^2}
\left(\frac{\Phi(\sigma)}{\zeta'(\rho)\zeta'(\sigma)}+o(1)\right).
\tag{I68}
$$
This is a calculation for that fixed pair, not an asymptotic for
$\mathcal A_{N,H}$ and not an assumption that all zeros are simple.
At a conjugate pair its displayed prefactor has scale
$N^{2\Re\rho-3/2}e^{2\lambda\Omega}/L^2$. The coefficient may vanish,
other residues may cancel, and no spectral remainder has been paid.
Thus existence of a zero with real part greater than $1/2$ alone
does not turn this calculation into an obstruction to
$\mathcal A_{N,H}=o(1)$.

The missing uniformity is visible already in
$|W_a(\sigma+it)|\ll_\sigma\min(h^2,h/(1+|t|))$, from integration
by parts. The compact-set expansion (I67) cannot be inserted over
an entire Perron line; heights of order $1/h\asymp N/H$ and beyond
need their own reciprocal-zeta and joint cancellation estimates.
Equations (I62)--(I68) supply the actual coupled kernel and a paid
grid error, without a bound for that double integral, a new RH
criterion, a same-integer signed Robin estimate, a mathematical
priority claim or Lean certification.

## A paid rectangular truncation on the original Perron lines

Reuse Koukoulopoulos, *The Distribution of Prime Numbers*,
[Theorem 7.2, printed p.71, PDF p.82](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf),
the same truncated Perron input used for (I60), and the actual
short-interval coefficient bounds of (I66). The following application
pays a finite-height error in (I65). It does not estimate the integral
inside the retained rectangle or a remainder after shifting its lines.

Retain the sufficiently large integer parameter family of (I59),
including $H<N/3$. Put $X=Q+1/2$, retain $h=(H-1/2)/N$, and choose
$\kappa_N=1+1/\log X$. All finite integrals in this section use this same
line. Let $\mathscr P_{s,T}$ denote $(2\pi i)^{-1}$ times integration
from $\kappa_N-iT$ to $\kappa_N+iT$. For $U,V\ge2$, define
$$
\begin{aligned}
A_U&=\mathscr P_{s,U}\frac{N^{s-1}W_a(s-1)}{\zeta(s)},&
B_U&=\mathscr P_{s,U}\frac{N^sW_a(s)}{\zeta(s)},\\
R_V(m)&=Z(m/N)+\frac1L\mathscr P_{s,V}
\frac{N^sH_{m/N}(s)}{\zeta(s)}.
\end{aligned}
$$
Here $Z=1-J_m/(2L)$ is the exact grid correction of (I63).
Uniformly on the original integer grid,
$$
\begin{aligned}
|A-A_U|&\ll hL/U+h/N,\\
|B-B_U|&\ll NhL/U+h,\\
\max_{N\le m\le2N}|R_N(m)-R_V(m)|&\ll NL/V+1.
\end{aligned}
\tag{I69}
$$

To retain the short-band gain in the first two estimates, set
$M_U(x)=\mathscr P_{s,U}x^s/[s\zeta(s)]$ and
$f_\tau(x)=x^{-\tau}\log(N/x)$, $\tau=0,1$.
Apply the cited theorem to $\mu$, with $\theta=A=0$ in its notation.
Since $\kappa_N\ge1+1/\log x$ for $X\le x\le N$, it gives
$\sup_{X\le x\le N}|M(x)-M_U(x)|\ll NL/U+1$.
The weights decrease to zero at $N$ and satisfy
$$
f_\tau(X)+\int_X^N|f_\tau'(x)|\,dx
=2f_\tau(X)\ll hN^{-\tau}.
$$
Exact Abel summation gives, respectively for $B,A$,
$$
-f_\tau(X)M(X)-\int_X^Nf_\tau'(x)M(x)\,dx,\qquad \tau=0,1.
$$
Replacing $M$ by $M_U$ gives exactly $B_U,A_U$: exchange the finite
integrals and integrate the weights to recover $W_a(s)$ and
$W_a(s-1)$. Thus both cutoff terms travel together through the
same band. The lower endpoint $X$ is a half integer; the upper
weight is zero. Multiplying the uniform Perron error by the displayed
variation proves the first two rows of (I69), with no changed cutoff.

For the last row, elementary integration of the fractional-part
Mellin transform gives, for $1\le q\le2$ and $\Re s>1$,
$$
H_q(s)=\frac{q}{(s-1)^2}
+\frac{d}{ds}\left(\frac{1+q^s(\zeta(s)-1)}s\right).
\tag{I70}
$$
The floor thresholds $k\ge2$ supply the factor $\zeta(s)-1$;
the factor $\log v$ vanishes at the lower integration endpoint.
Writing $m=qN$, division by $\zeta(s)$ gives explicitly
$$
\begin{aligned}
\frac{N^sH_q(s)}{\zeta(s)}={}&
\frac{qN^s}{(s-1)^2\zeta(s)}
+\frac{m^s-N^s}{s^2\zeta(s)}\\
&+m^s\left(\frac{\log q}s-\frac1{s^2}\right)
+\frac{m^s}{s}\frac{\zeta'(s)}{\zeta(s)}
-\frac{m^s\log q}{s\zeta(s)}.
\end{aligned}
$$
Since $|1/\zeta(\kappa_N+it)|\le\zeta(\kappa_N)\ll L$,
the square-denominator pieces have tail $O(NL/V)$.
The remaining pieces are ordinary Perron integrals of
$\zeta'/\zeta$, $1/\zeta$ and the Dirichlet series $1$, evaluated
at $m=qN$, with the bounded coefficient $\log q$ where present.
The cited theorem for $\Lambda$, with $\theta=0,A=1$, gives
$O(NL^2/V+L)$; for $\mu$ and the sequence supported at $1$ it
gives $O(NL/V+1)$. At integer $m$, replacing full summation by the
symmetric Perron limit costs at most $O(L)$ for $\Lambda$ and
$O(1)$ for $\mu$. These costs are retained. Division by $L$ gives
the last row of (I69), including $m=N,2N$ and their original $J_m$.

Let $S=R_N-Z$, $S_V=R_V-Z$, and define the finite rectangle
$$
\mathcal M_N(U,V)=\frac1{L^2}
\mathscr P_{u,U}\mathscr P_{v,V}
\frac{N^{u+v-1}\mathcal K_N(u,v)}{\zeta(u)\zeta(v)}
=\frac{A_U\mathfrak p_N(S_V)-B_U\mathfrak q_N(S_V)}L.
\tag{I71}
$$
Finite integration and the actual finite grid justify the equality.
All endpoint terms of (I64) remain in this expression.
The original coefficients satisfy
$|A|+|B|/N\ll h^2e^{-c_\star\Omega}$, while
$\|S\|_\infty\ll N/L$ follows from
$\sum_{n\le N}\log(N/n)\ll N$ and $\|Z\|_\infty=O(1)$.
Together with the operator bounds used for (I66), (I69) therefore gives
$$
\begin{aligned}
|\mathcal A_{N,H}-E_{\rm grid}-\mathcal M_N(U,V)|
\ll{}&\frac{Nh}{UL}+\frac h{L^2}\\
&+\left(h^2e^{-c_\star\Omega}+\frac{hL}U+\frac hN\right)
  \left(\frac NV+\frac1L\right).
\end{aligned}
\tag{I72}
$$
This is a bound for the same jointly realized functional, using its
actual coefficients rather than independently optimized values.
Set $U=H$ and $V=\sqrt N$, and reuse the quantitative bound for
$E_{\rm grid}$ in (I66). At the bandwidth of (I59), (I72) yields
$$
\mathcal A_{N,H}
=\mathcal M_N(H,\sqrt N)
+O\!\left(\frac1L+
 e^{-(c_\star-2\lambda)\Omega}+\frac L{\sqrt N}\right)
=\mathcal M_N(H,\sqrt N)+o(1).
\tag{I73}
$$
The positive margin is exactly $2\lambda<c_\star$.
This baseline does not use the fixed zero-free half-plane of (I60).

If that input is adopted, retain its full premise: fixed
$1/2\le B<1$, no zeta zero in $\Re s>B$, and fixed $B<\beta<1$.
Then (I60)'s application gives $\|S\|_\infty\ll_\beta N^\beta/L$.
In the proof of (I72), replace only the first norm bound by this one
and take $U=HN^{\beta-1}$, $V=\sqrt N$. The same products give
$$
\mathcal A_{N,H}
=\mathcal M_N(HN^{\beta-1},\sqrt N)
+O_\beta\!\left(\frac1L+
 e^{-(c_\star-2\lambda)\Omega}+LN^{1/2-\beta}\right)
=\mathcal M_N(HN^{\beta-1},\sqrt N)+o(1).
\tag{I74}
$$
Here $\beta>1/2$, and constants may depend on this fixed $\beta$
and the adopted input. In particular the cited Liu boundary yields
$U\asymp N^{0.624957019420098946\ldots+\varepsilon}
 e^{\lambda\Omega}$ for fixed
$0<\varepsilon<1-B_{\rm new}$, with the paper-level source status
and uncompiled external Lean boundary of (I60)--(I61) unchanged.

These bounds pay the original-line rectangular truncation. They do
not give an absolute tail estimate or a zero-sum truncation after
contour deformation. The retained heights still extend beyond
$1/h\asymp N/H$; the compact expansion (I67) cannot be substituted
over those rectangles. A sufficiently strong estimate inside them,
the same-integer signed Robin estimate, and RH remain unresolved.
This is an application of the cited Perron theorem, without a
mathematical-priority claim or Lean certification.

## Transport the actual endpoint into a smooth common test

Retain the original bandwidth and fixed constants of (I58)--(I59),
including $0<2\lambda<c_\star$ and $H<N/3$. Put
$\epsilon_N=e^{-c_\star\Omega}$ and $v_N=e^{-b\Xi(N)}$, where $b>0$
is the unconditional tail constant used there. All quantities below
come from the same integer $N$, its actual band, and its original
endpoint. This applies the already owned uniform short-interval
estimates, the cell identity (I12), and the bump bounds cited below;
it is not a new cancellation theorem.

The actual coefficients contain a relation lost by separate norm bounds:
$$
\begin{aligned}
\delta_{N,H}:=A-B/N
 &=\sum_{Q<n\le N}\mu(n)\log(N/n)(1/n-1/N)
   \ll h^3\epsilon_N,\\
e_{N,H}:=B/(2N+1)-A/2
 &=-\delta_{N,H}/2-B/[2N(2N+1)]
   \ll h^3\epsilon_N.
\end{aligned}
\tag{I75}
$$
Indeed, the first sum's nonnegative real weight is decreasing, with
supremum plus variation $O(h^2/N)$. The same full-prefix Mobius bound
used in (I48) is $O(H\epsilon_N)$ on this band. Abel summation gives
the first row; the second uses $|B|\ll Nh^2\epsilon_N$ and $Nh\gg1$.
These bounds do not replace $e_{N,H}$ by a separately optimized value.

Use the existing real-argument interpolation
$\widetilde R_N(t)=S_N(t)/L$ from (I11)--(I12), and set
$I_j=\int_1^2q^{-j}\widetilde R_N(Nq)\,dq$, $j=1,2$.
This interpolation agrees with $R_N(m)$ at integers; the actual
balanced residual remains a step function on its original cells.
The cell slope is exactly $U_N/L$. Comparing the cell integrals of
$t^{-2}$ and $t^{-1}$ with the original samples, including $m=2N$,
gives
$$
\begin{aligned}
|P_1-I_1|+|NP_0-I_2|
 &\ll N^{-1}\max_{N\le m\le2N}|R_N(m)|+|U_N|/L
 \ll L^{-1},\\
\mathcal A_{N,H}
 &=L^{-1}\left(AI_1-\frac{3B}{2N}I_2+e_{N,H}r\right)
   +O(h^2\epsilon_N/L^2).
\end{aligned}
\tag{I76}
$$
For the last bounds reuse $U_N=O(1)$ from the unconditional tail and
$\max|R_N|\ll N/L$ from the original coefficients. The endpoint
$r=R_N(2N)$ in (I76) is unchanged.

The same uniform short-interval inputs pay the local real-argument
oscillations at both ends:
$$
\operatorname{osc}_{[N,N+Nh]}\widetilde R_N
+\operatorname{osc}_{[2N-Nh,2N]}\widetilde R_N
\ll \frac H L(\epsilon_N+v_N).
\tag{I77}
$$
To see this, (I33) holds throughout $N\le t\le2N$ with the weak
$\psi(t)$ and the actual sum over $N<n\le t$. Subtract at two
points. The linear term uses $U_N-1\ll v_N$; the other terms use
the full-prefix Mobius and $\Lambda-1$ bounds underlying (I58).
At the lower end apply that same uniform supplier near $N$; at the
upper end use its terminal prefixes. For all these starts,
$\Omega(x)-\Omega(N)=o(1)$, so the same chosen common constant works.
Short prefixes cost $O(uL)$ and real versus integer endpoints cost
$O(L)$ before division by $L$; the fixed power surplus in $H$
absorbs both in $H\epsilon_N$. Thus no jump is suppressed.

Here is an explicit mass-preserving construction. Fix nonnegative
$\rho\in C_c^\infty(0,1)$, supported in $[1/4,3/4]$, with
integral one, and put
$\chi(x)=\int_{-\infty}^x\rho(u)\,du$,
$\chi_h(q)=\chi((q-1)/h)\chi((2-q)/h)$ and
$$
\eta_{-,h}(q)=h^{-1}\rho((q-1)/h),\qquad
\eta_{+,h}(q)=h^{-1}\rho((2-q)/h).
$$
Let $\beta_{j,-}$ and $\beta_{j,+}$ be the integrals of
$(1-\chi_h(q))q^{-j}$ over $[1,1+h]$ and $[2-h,2]$, respectively,
and define
$$
w_{j,h}(q)=\chi_h(q)q^{-j}
 +\beta_{j,-}\eta_{-,h}(q)+\beta_{j,+}\eta_{+,h}(q),\qquad
w=A w_{1,h}-\frac{3B}{2N}w_{2,h}+e_{N,H}\eta_{+,h}.
$$
Each $w_{j,h}$ preserves the original $q^{-j}$ mass separately on
the two boundary intervals and equals it away from them.
Moreover $\beta_{j,\pm}=O(h)$ and
$\|w_{j,h}-q^{-j}\|_{L^1(1,2)}\ll h$.
The last term of $w$ transports the original endpoint to a normalized
average supported in $(2-h,2)$; it does not delete that endpoint.
Equations (I75)--(I77) give
$$
\begin{aligned}
w&\in C_c^\infty(1,2),&
\|w^{(k)}\|_\infty&\ll_k h^{2-k}\epsilon_N,\\
\mathcal A_{N,H}
 &=\frac1L\int_1^2w(q)\widetilde R_N(Nq)\,dq+O(\mathcal E_N),&
\mathcal E_N&=\frac{h^2\epsilon_N}{L^2}
 +\frac{H^4}{N^3L^2}(\epsilon_N^2+\epsilon_Nv_N)=o(1).
\end{aligned}
\tag{I78}
$$
For each boundary deformation, subtract the endpoint's constant
value before using (I77); its mass is zero. The resulting error is
$O(hH(\epsilon_N+v_N)/L)$ in each $I_j$.
The transported endpoint costs
$O(|e_{N,H}|H(\epsilon_N+v_N)/L^2)$ in the final functional.
These are exactly the allowances in (I78). At the original bandwidth,
$4\lambda<2c_\star$ and $\Xi/\Omega\to\infty$ pay them.
The common level has not been centered away:
$\int w=A\log2-3B/(4N)+e_{N,H}$ need not be zero.

## Retain the exact scalar channels before cutting smooth frequencies

Choose the preceding fixed profiles from the standard bump already
used in [the research volume, Lemma 31.1](../../docs/develop/theory/RH_RESEARCH_LANE_THEORY.md#31-完整高零点尾界与有限实尺度正性),
whose paper calculation gives
$\|\phi^{(k)}\|_1\le12^k(k!)^2$ for
$\phi(x)=e^{-1/(1-4x^2)}\mathbf1_{|x|<1/2}$.
The same cited Cauchy estimate also bounds $\|\phi^{(k)}\|_\infty$
by these constants, as required for the profile derivatives.
The related [Tlas source note](tlas2020bump.md) records the original
bump and its Fourier convention. This reuses the standard Gevrey
bound; no new bump or saddle theorem is asserted.
One may take $\rho(x)=2\phi(2x-1)/\int\phi$ and $\chi$ as above.
Leibniz bounds and the analytic coordinate $q=e^x$ then give fixed
$C>0$ such that, for $\kappa=\kappa_N$ and every integer $k\ge0$,
$$
\|\partial_x^k[e^{(\kappa+1)x}w(e^x)]\|_1
+\|\partial_x^k[x e^{(\kappa+1)x}w(e^x)]\|_1
\le C^{k+1}(k!)^2 h^{2-k}\epsilon_N.
$$
All integrals are over $0<x<\log2$ with zero extension; both
endpoints are flat. Constants are independent of $N,H,k$.
For example, expand $(q\partial_q)^k$ with Stirling numbers of the
second kind, and use $S(k,j)(j!)^2\le k^k k!\le e^k(k!)^2$;
products with the fixed analytic factors only change $C$.
Optimizing the integration-by-parts order, as for the cited bump,
gives fixed $a,C'>0$ and
$$
g_w(s)=\int_1^2w(q)q^s\,dq,\qquad
|g_w(\kappa_N+it)|+|g_w'(\kappa_N+it)|
\le C'h^2\epsilon_N e^{-a\sqrt{h|t|}}.
\tag{I79}
$$
The $h^{-k}$ costs are retained; these are not fixed-complexity tests.

Put $c_w=\int_1^2q w(q)\,dq$, $d_w=\int_1^2w(q)\,dq$ and
$B_{\rm all}=\sum_{n\le N}\mu(n)\log(N/n)$. Define
$$
\mathcal C_{N,H}=\frac{Nc_wU_N-d_wB_{\rm all}}{L^2},\qquad
\mathcal F_w(s)=\frac{\zeta'(s)}{\zeta(s)}\frac{g_w(s)}s
-\frac1{\zeta(s)}\left(\frac{g_w'(s)}s-\frac{g_w(s)}{s^2}\right).
$$
Fix $N,H$ and hold the resulting $w$ fixed during Mellin inversion.
On the original line, the exact smooth-moment identity is
$$
\frac1L\int_1^2w(q)\widetilde R_N(Nq)\,dq
=\mathcal C_{N,H}+\frac1{L^2}\mathscr P_s N^s\mathcal F_w(s).
\tag{I80}
$$
The integral on the right is absolutely convergent.
For verification, integrate (I70) against $w$. The full kernel is
$$
\frac{\int w(q)H_q(s)\,dq}{\zeta(s)}
=\frac{c_w}{(s-1)^2\zeta(s)}-\frac{d_w}{s^2\zeta(s)}
 +\frac{d}{ds}\frac{g_w(s)}s+\mathcal F_w(s).
$$
The two square-denominator inversions are exactly $Nc_wU_N$ and
$-d_wB_{\rm all}$. Integration by parts gives
$\mathscr P_s N^s(g_w/s)'=-Ld_w$; this cancels the literal
$d_w/L$ from $\widetilde R_N=1+\cdots$.
Equivalently, integrate the real-argument (I33); finite Dirichlet
summation and Mellin inversion give the same two scalar terms.
The $q$ integrals have no half-jump term, since the threshold set has
measure zero. The original integer endpoint has already been paid
by its transport in (I78).

For $|t|\ge2$, absolute Euler series on the original line give
$|1/\zeta(\kappa_N+it)|\ll L$ and
$|\zeta'/\zeta(\kappa_N+it)|\le-\zeta'(\kappa_N)/\zeta(\kappa_N)\ll L$.
Together with (I79), they prove the absolute tail bound, for $hT\ge1$,
$$
\frac1{L^2}\int_{|t|>T}
 |N^{\kappa_N+it}\mathcal F_w(\kappa_N+it)|\,dt
\ll\frac{Nh^2\epsilon_N}{L}e^{-a'\sqrt{hT}}
\tag{I81}
$$
for fixed $a'>0$. Indeed the remaining integral is bounded by a
constant times $\int_{\sqrt{hT}}^\infty e^{-au}du/u$.
Choose a sufficiently large fixed $C_0$ and
$T=C_0L^2/h$. Equations (I78)--(I81) yield
$$
\mathcal A_{N,H}
=\mathcal C_{N,H}+\frac1{L^2}\mathscr P_{s,T}N^s\mathcal F_w(s)+o(1),
\qquad T\asymp\frac NH(\log N)^2.
\tag{I82}
$$
For example $a'\sqrt{C_0}>1$ pays (I81), since
$Nh^2\epsilon_N\asymp N^{1/2}e^{-(c_\star-2\lambda)\Omega}$.
This uses the original $H\asymp N^{3/4}e^{\lambda\Omega}$ family,
without adopting the fixed-half-plane input (I60).

The scalar channels in $\mathcal C_{N,H}$ remain exact. Their sizes
and signs have not been paid separately, and they cannot be dropped.
Without extracting them, the complete smooth kernel retains only a
$1/t^2$ rational tail; smoothness alone would not justify (I82)'s
height. The useful change is a paid transport of the same endpoint
and a frequency remainder with an absolute bound. The joint bound
for $\mathcal C_{N,H}$ plus the retained integral is still missing.
No shifted zero-sum estimate, fixed-complexity nilsequence interface,
same-integer signed Robin bound, RH proof, mathematical-priority claim
or Lean certification follows from this application.

## Two smoothing scales allow a controlled full-residue shift

Retain the original integer family, bandwidth and constants of
(I58)--(I59), including $0<2\lambda<c_\star$, and the half-integer
cut $a=(Q+1/2)/N$ from (I62). This application uses the standard
smooth bump already cited in (I79), the complete kernel (I70), and
[Inoue's published good-height supplier](../Analytic/inoue2019mobiuszeta.md),
(IH1)--(IH2). It introduces no new good-height theorem. The new
interface controls the smoothing and contour errors for the complete
joint functional; it does not estimate its interior residue sum.

Fix a nonnegative even $\phi\in C_c^\infty(-1,1)$ with integral one,
obtained by normalizing the cited bump, and put
$$
F_\ell(s)=\int_{-1}^1\phi(t)e^{\ell ts}\,dt,\qquad 0<\ell\le1.
$$
On every fixed vertical strip, integration by parts gives
$F_\ell(\sigma+i\tau)\ll_{\phi,j}(1+\ell|\tau|)^{-j}$ for every
fixed integer $j\ge0$. Also $F_\ell(0)=1$ and $F_\ell'(0)=0$.
Only these existing smooth-bump properties are needed here.

Hold $a$ fixed while varying the real cutoff $x$, and define
$$
\begin{aligned}
A(x)&=\sum_{ax<n\le x}\mu(n)\log(x/n)/n,&
B(x)&=\sum_{ax<n\le x}\mu(n)\log(x/n),\\
\eta&=H^{-1},&
\widetilde A&=\int\phi(t)A(Ne^{\eta t})\,dt,\qquad
\widetilde B=\int\phi(t)B(Ne^{\eta t})\,dt.
\end{aligned}
$$
Here $A(N)=A$ and $B(N)=B$ with their original integer band. If
$|x-N|\le\Delta\ll H$, variation on the common part and the
$O(\Delta+1)$ endpoint integers give
$$
\begin{aligned}
|A(x)-A|&\ll h(\Delta+1)/N,&
|B(x)-B|&\ll h(\Delta+1),\\
|\widetilde A-A|&\ll N^{-1},&
|\widetilde B-B|&\ll1.
\end{aligned}
\tag{I83}
$$
Indeed the common log weight varies by $O(\Delta/N)$ and the
endpoint weights are $O(h)$. For this smoothing
$\Delta\ll N/H$ and $hN/H\asymp1$. No extra Mobius cancellation
is used in these differences.

For the residual use a different scale, moving both its cutoff and
its argument. Write
$$
S_x(t)=\log x+\sum_{n\le x}\mu(n)\log(x/n)\{t/n\},\qquad
\mathscr S_N(q)=S_N(qN),
$$
so $\mathscr S_N(m/N)=LR_N(m)$ at the original integer samples.
Set $\nu=N^{-1/2}$ and
$\widetilde S_N(q)=\int\phi(t)S_{Ne^{\nu t}}(qNe^{\nu t})\,dt$.
The real-cutoff version of (I33) is
$$
S_x(t)=tU_x-\psi(t)+\sum_{x<n\le t}\mu(n)\log(x/n),\qquad
U_x=\sum_{n\le x}\mu(n)\log(x/n)/n,\quad x\le t\le2x,
$$
with the same full-weight $\psi$ at integers. The divisor-convolution
proof of (I33) applies unchanged: any omitted divisor in this range
must be the integer itself. Between consecutive integers,
$(xU_x)'=U_x+\sum_{n\le x}\mu(n)/n=O(L^2)$, and $xU_x$ is
continuous at integer cutoffs. Prime jumps cost
$O((\Delta+1)L)$ when $|x-N|\le\Delta$; the final Mobius sum
changes by $O(\Delta+1)$. Uniformly for $1\le q\le2$, this gives
$$
\begin{aligned}
\|\widetilde S_N-\mathscr S_N\|_\infty&\ll\sqrt N L^2,\\
\|\widetilde S_N\|_\infty+\|\mathscr S_N\|_\infty&\ll N.
\end{aligned}
\tag{I84}
$$
The second row also follows directly from
$\sum_{n\le x}\log(x/n)\ll x$. The $+1$ in the variation bound
retains the integer jumps, including both original endpoints.
The actual balanced step residual has not been replaced by an
identical continuous function; (I84) pays the change of samples.

Keep exactly the discrete operators $\mathfrak p_N,\mathfrak q_N$
of (I64), whose sup-norm operator bounds are $O(1)$ and $O(N^{-1})$.
Define
$$
\widetilde{\mathcal A}_{N,H}
=\frac{\widetilde A\mathfrak p_N(\widetilde S_N)
      -\widetilde B\mathfrak q_N(\widetilde S_N)}{L^2}.
$$
Using (I83)--(I84) and the already owned
$|A|+|B|/N\ll h^2e^{-c_\star\Omega}$ yields
$$
|\mathcal A_{N,H}-\widetilde{\mathcal A}_{N,H}|
\ll_\phi L^{-2}+\sqrt N h^2e^{-c_\star\Omega}
\ll_\phi L^{-2}+e^{-(c_\star-2\lambda)\Omega}=o(1).
\tag{I85}
$$
For example, coefficient errors act on a residual bounded by $N$;
residual errors act on the original coefficients. Both smoothings
are deterministic linear operations on the same arithmetic data.
If the band coefficients were instead smoothed on spatial width
$\sqrt N$, this argument would leave $h\sqrt N/L^2$, which grows
at the original bandwidth. The distinct scales are essential to
this error estimate.

The absolutely convergent smoothed Mellin formulas on $\Re s=2$ are
$$
\begin{aligned}
\widetilde A
 &=\frac1{2\pi i}\int_{(2)}
   \frac{N^{u-1}W_a(u-1)F_\eta(u-1)}{\zeta(u)}\,du,\\
\widetilde B
 &=\frac1{2\pi i}\int_{(2)}
   \frac{N^uW_a(u)F_\eta(u)}{\zeta(u)}\,du,\\
\widetilde S_N(q)
 &=L+\frac1{2\pi i}\int_{(2)}
   \frac{N^vH_q(v)F_\nu(v)}{\zeta(v)}\,dv.
\end{aligned}
\tag{I86}
$$
These follow from (I62)--(I63) with the varying real cutoff. Each
integer jump occurs at a discrete set of smoothing parameters, of
measure zero, so the symmetric and actual values have equal
integrals. The literal average of $\log(Ne^{\nu t})$ is $L$ by
evenness. The two band multipliers are $F_\eta(u-1)$ and
$F_\eta(u)$; they cannot be factored into one common multiplier.

Apply the owned good-height theorem with $U=N^4$. It supplies one
$T_N\in[N^4,N^4+N^{4/3}]$ such that
$$
\sup_{-1\le\sigma\le2,\ \xi\in\{-1,1\}}
|\zeta(\sigma+i\xi T_N)|^{-1}\ll_\varepsilon T_N^\varepsilon.
$$
No RH, simple-zero hypothesis or negative moment of $\zeta'$ is
assumed. Let $\mathcal Z_N$ contain each distinct nontrivial zero
with $|\Im\rho|<T_N$ once. Define $a_N^\circ,b_N^\circ,z_N(q)$
as the sums of the full residues at $\rho\in\mathcal Z_N$ of the
three respective integrands in (I86), omitting the factor
$(2\pi i)^{-1}$. Multiple zeros are included through their complete
meromorphic residues. Moving the lines from $2$ to $-1$ gives
$$
\begin{aligned}
\widetilde A&=a_N^\circ+O_\phi(h^2N^{-2}+N^{-10}),\\
\widetilde B&=b_N^\circ+O_\phi(h^2N^{-1}+N^{-10}),\\
\widetilde S_N(q)&=\log(2\pi)+z_N(q)
              +O_\phi(N^{-1}L^2+N^{-10}),\qquad 1\le q\le2.
\end{aligned}
\tag{I87}
$$
The last error is uniform in $q$. Here are the contour costs and
all extra residues needed for this shift.

On the horizontal edges, standard polynomial growth on a slightly
wider fixed strip and Cauchy's estimate give $|\zeta'|\ll T_N^2$,
so the good-height bound gives
$|\zeta'/\zeta|\ll_\varepsilon T_N^{2+\varepsilon}$ there.
It does not give an $O(\log T_N)$ horizontal bound. Formula (I70)
therefore bounds $H_q/\zeta$ polynomially, uniformly in $q$.
As $T_N/H\ge N^3$ and $T_N/\sqrt N\ge N^{7/2}$, the fixed
integration-by-parts order $j=20$ in $F_\ell$ pays both horizontal
edges and the omitted original-line tails by $O_\phi(N^{-10})$.
For instance, the horizontal integrands are bounded by
$O(N^2T_N^{2+\varepsilon})$ before the smoothing multipliers;
each has width three, and their smoothing decay is at least
$N^{-60}$. The original-line tails can be integrated using the
same decay and the absolutely convergent Dirichlet series.

On the entire left line the functional equation, Stirling bounds
and the Euler series on $\Re(1-s)=2$ give
$$
|\zeta(-1+i\tau)|^{-1}\ll(1+|\tau|)^{-3/2},\qquad
|\zeta'/\zeta(-1+i\tau)|\ll\log(2+|\tau|).
$$
The complete identity (I70) and $a>2/3$ imply
$$
\begin{aligned}
|W_a(\sigma+i\tau)|&\ll h^2\quad(-2\le\sigma\le2),\\
\sup_{1\le q\le2}|H_q(-1+i\tau)/\zeta(-1+i\tau)|
 &\ll\frac{\log(2+|\tau|)}{1+|\tau|},\\
N^{-1}\int_{\mathbb R}
 \frac{\log(2+|\tau|)}{1+|\tau|}
 (1+\nu|\tau|)^{-20}\,d\tau&\ll N^{-1}L^2.
\end{aligned}
\tag{I88}
$$
Thus the full left-line integrals cost respectively $h^2N^{-2}$,
$h^2N^{-1}$ and $N^{-1}L^2$. Their tails above $T_N$ are also
$O_\phi(N^{-10})$. No absolute bound on interior residues is used.

There is no pole at $s=1$: the original integral for $H_q$ is
holomorphic on $\Re s>0$, and its apparent singularity in (I70)
is removable. At zero, (I70) gives
$$
H_q(s)=\frac1{2s^2}+O(1),\qquad
\frac{H_q(s)}{\zeta(s)}
 =-\frac1{s^2}+\frac{\log(2\pi)}s+O(1).
$$
Since $F_\nu'(0)=0$, the extra residue in the last integral of
(I86) is $-L+\log(2\pi)$. It cancels the literal $L$ and retains
the common level $\log(2\pi)$ in (I87). The band integrands have
no pole at zero, and no trivial zero is crossed before $\Re s=-1$.
This proves (I87) with every nonzero contour contribution accounted
for. The other application's formula (CH1b) in the Chirre--Helfgott
note requires $y>e^2T$, so it is not used at $y\asymp N,T\asymp N^4$;
only the owned good-height and functional-equation inputs are reused.

Using $p_N(v),q_N(v)$ from (I64), define the complete smoothed kernel
and finite double residue sum
$$
\begin{aligned}
\widetilde{\mathcal K}_N(u,v)
 &=\big[W_a(u-1)F_\eta(u-1)p_N(v)
       -NW_a(u)F_\eta(u)q_N(v)\big]F_\nu(v),\\
\Sigma_{N,H}
 &=\sum_{\rho,\sigma\in\mathcal Z_N}
 \operatorname{Res}_{u=\rho}\operatorname{Res}_{v=\sigma}
 \frac{N^{u+v-1}\widetilde{\mathcal K}_N(u,v)}{\zeta(u)\zeta(v)}\\
 &=a_N^\circ\mathfrak p_N(z_N)-b_N^\circ\mathfrak q_N(z_N).
\end{aligned}
\tag{I89}
$$
This is a finite sum of full residues, with no assumption about
simple zeros. From (I83)--(I87) and the original physical-space
bounds,
$\|z_N\|_\infty\ll N$ and
$|a_N^\circ|+|b_N^\circ|/N\ll h^2e^{-c_\star\Omega}+N^{-1}$.
They pay all cross terms from (I87); the retained constant contributes
$O((h^2e^{-c_\star\Omega}+N^{-1})/L^2)$.
Consequently
$$
\mathcal A_{N,H}=\frac{\Sigma_{N,H}}{L^2}
 +O_\phi\left(L^{-2}+e^{-(c_\star-2\lambda)\Omega}\right).
\tag{I90}
$$
Both $f(2)$ endpoint terms remain in the original discrete operators.
The full $W_a,H_q$ are used through the growing heights, without
substituting the fixed-compact expansion (I67).

The remaining estimate is $|\Sigma_{N,H}|=o(L^2)$ for each sufficiently
large original integer $N$ and its specified band. A fixed zero pair,
an average over $N$, or separately optimized residue sums do not give
that estimate. Equations (I83)--(I90) are a repository application of
existing analytic tools, with no mathematical-priority claim or Lean
certification. They control the errors in a full-residue representation;
they do not prove the joint cancellation, the complete same-integer
signed Robin bound, or RH.

## A larger denominator cut for the actual joint linear functional

Keep the original integer family of (I59), and put
$\epsilon_N=e^{-c_\star\Omega}$ and
$\Delta_\star=c_\star-2\lambda>0$. Reuse the complete reduced-frequency
expansion (I17)--(I19), including all aliases in $b_{N,q}$, its uniform
coefficient bound, and the finite first positive moment from
[Weingartner's existing source note](../ArithSums/weingartner2010distribution.md).
This application estimates a linear contribution to the original
joint functional, rather than the entire residual norm.

For an integer-grid function $f$, define
$$
\begin{aligned}
\mathscr J_N(f)
 &=\frac1L\left(\sum_{m=N}^{2N}k_{N,m}f(m)
                   +e_{N,H}f(2N)\right),\\
k_{N,m}&=\frac{A(m+\tfrac12)-\tfrac32B}{m(m+1)},&
e_{N,H}&=\frac B{2N+1}-\frac A2.
\end{aligned}
\tag{I91}
$$
Thus $\mathscr J_N(R_N)=\mathcal A_{N,H}$ exactly, with both original
endpoint contributions combined in their actual coefficient.
Let $T_{N,\le D}$ consist of every frequency in (I18) whose reduced
denominator is at most the integer $D$, where $2\le D\le N$.
In particular its coefficient $b_{N,q}$ still contains every
$qj\le N$, including $qj>D$; this is not a truncation of the original
coefficient dictionary.

The finite geometric sum and elementary sine bounds give
$$
\left|\sum_{m=u}^ve(mr/q)\right|\le\frac2{|1-e(r/q)|},\qquad
\sum_{r=1}^{q-1}|1-e(r/q)|^{-2}\ll q^2,\qquad
\sum_{r=1}^{q-1}|1-e(r/q)|^{-1}\ll q\log(2q).
$$
The already owned $|b_{N,q}|\le2q/[\varphi(q)L]$ and finite moment
$\sum_{q\le D}q/\varphi(q)\ll D$ therefore imply
$$
\begin{aligned}
\sup_{u\le v}\left|\sum_{m=u}^vT_{N,\le D}(m)\right|
 &\ll\sum_{q\le D}|b_{N,q}|q\ll D^2/L,\\
\sup_m|T_{N,\le D}(m)|
 &\ll\sum_{q\le D}|b_{N,q}|\log(2q)
 \ll D\log(2D)/L.
\end{aligned}
\tag{I92}
$$
Here $u,v$ are integers. Enlarging the numerator sums to all
$1\le r<q$ only increases these positive majorants. The second
finite moment $\sum q^2/\varphi(q)\ll D^2$ needed in the first
row follows at once by multiplying the first moment bound by $D$;
no new totient distribution theorem is used.

For the continuous extension of the actual weight,
$k_N(x)=[A(x+1/2)-3B/2]/[x(x+1)]$, differentiation gives
$$
\sup_{N\le x\le2N}|k_N(x)|+
\int_N^{2N}|k_N'(x)|\,dx
\ll\frac{|A|+|B|/N}{N}\ll\frac{h^2\epsilon_N}{N}.
$$
Discrete Abel summation with the first row of (I92), including both
integer endpoints, controls the sum in (I91). For its last term use
the actual relation $e_{N,H}\ll h^3\epsilon_N$ from (I75) and the
point-value bound in (I92). Consequently, uniformly for $2\le D\le N$,
$$
|\mathscr J_N(T_{N,\le D})|
\ll\frac{\epsilon_N}{L^2}
\left(\frac{h^2D^2}{N}+h^3D\log(2D)\right).
\tag{I93}
$$
The same $A,B$ are used in both terms; no independence or separate
optimal choice is introduced. The second term retains the endpoint,
and its additional factor $h$ uses the same-source relation (I75).

Put $\kappa_\star=\min(c_\star/2,\Delta_\star)>0$. For any fixed
$0\le\kappa\le\kappa_\star$, take
$D_N(\kappa)=\lfloor(\sqrt N/h)e^{\kappa\Omega}\rfloor$.
At the original bandwidth,
$2\le D_N(\kappa)\le N$ eventually and
$D_N(\kappa)\asymp N^{3/4}e^{(\kappa-\lambda)\Omega}$,
since $\Omega=o(L)$. Substitution into (I93) gives
$$
|\mathscr J_N(T_{N,\le D_N(\kappa)})|
\ll\frac{e^{-(c_\star-2\kappa)\Omega}}{L^2}
   +\frac{e^{-(\Delta_\star-\kappa)\Omega}}L=o(1).
\tag{I94}
$$
Both exponents are nonnegative throughout the stated closed range;
even at its upper endpoint the logarithmic denominators tend to
infinity. At $\kappa=0$ this recovers the smaller cut
$\lfloor\sqrt N/h\rfloor$ and the exponentially decaying bound.
The positive endpoint $\kappa_\star$ uses the remaining slack in
the same inequality, rather than an additional distribution theorem.

This is a pointwise-in-$N$ estimate for the complete frequency
component. The norm cut (I21) alone does not even pay the
$\kappa=0$ range: weighted Cauchy on the interior sum would give only
$O(h^2\epsilon_N\sqrt{D(1+D^2/N)}/L^2)$, whose allowance there
is of order $N^{1/8}e^{-(c_\star-\lambda/2)\Omega}/L^2$ and does
not tend to zero. The improvement comes from summing the oscillation
against the actual weight before taking its absolute value.

For the remaining cut choose $D_N=D_N(\kappa_\star)$, retain the
original constant $d_N$ from (I17), and put
$T_{N,>D_N}=R_N-d_N-T_{N,\le D_N}$. Linearity and (I94) give
$$
\mathcal A_{N,H}
=\mathscr J_N(d_N+T_{N,>D_N})
 +O\left(\frac{e^{-(c_\star-2\kappa_\star)\Omega}}{L^2}
        +\frac{e^{-(\Delta_\star-\kappa_\star)\Omega}}L\right).
\tag{I95}
$$
The retained aliases now have $q>D_N$ and $j\le N/q<N/D_N$
(up to the integer endpoint), but their joint coprimality and actual
Mobius signs remain. This reduced-denominator cut is not a cut by
prime size or the same as observing one modulus.

The constant must remain coupled to those frequencies. Directly
from (I64),
$\mathfrak p_N(1)-N\mathfrak q_N(1)=\log2-3/4+O(N^{-1})$,
whose limit is nonzero. Thus $A=B/N+O(h^3\epsilon_N)$ does not
annihilate the constant channel. The still missing estimate is
$\mathscr J_N(d_N+T_{N,>D_N})=o(1)$ with its actual coefficients
and endpoint. This is a project application of the owned Fourier,
coefficient and variation inputs, without a mathematical-priority
claim or Lean certification. It does not supply the full joint
bound, signed Robin inequality or RH.

A different proposed supplier, vanishing unweighted critical-line
mollifier error on the active height intervals, is ruled out by the
[Radziwill source and exact parameter map](radziwill2012mollifying.md).
That lower bound neither rules out the weighted Nyman--Beurling
norm tending to zero nor supplies a sign for the retained functional
in (I95).

## Preserve primitive-numerator cancellation at the endpoint

Keep the complete coefficients and actual functional of (I91).
For an integer $m$ and $q\ge2$, set
$$
\mathcal S_q(m)=\{m/q\}-\frac{q-1}{2q},\qquad
\Pi_q(m)=-\frac1q\sum_{\substack{1\le r<q\\(r,q)=1}}
 \frac{e(mr/q)}{1-e(-r/q)},
$$
and put $\mathcal S_1=\Pi_1=0$. Grouping the already owned finite sawtooth
expansion by reduced denominator and applying classical Mobius
inversion gives
$$
q\mathcal S_q(m)=\sum_{d\mid q}d\Pi_d(m),\qquad
\Pi_q(m)=\frac1q\sum_{d\mid q}\mu(q/d)d\mathcal S_d(m),\qquad
|\Pi_q(m)|\le\frac{\sigma(q)}{2q}.
\tag{I96}
$$
Indeed $|\mathcal S_d(m)|\le(d-1)/(2d)\le1/2$ on the integer grid.
The first equality retains every reduced denominator of the original
$q$-periodic response; inversion is applied to this finite divisor
identity before taking an absolute value. This reuses standard
Fourier grouping and Mobius inversion in the current application.

The [existing finite positive-moment bound](../ArithSums/weingartner2010distribution.md#finite-bridge-and-precise-application)
gives $\sum_{q\le D}(q/\varphi(q))^2\le DW(2)$, with the fixed
finite Euler product $W(2)$ defined there. The same source already
supplies $\sigma(q)/q\le q/\varphi(q)$, hence
$$
\sum_{q\le D}\frac{\sigma(q)}{\varphi(q)}
\le\sum_{q\le D}\left(\frac q{\varphi(q)}\right)^2
\le DW(2).
$$
No additional average-order estimate is needed.
Since $T_{N,\le D}(m)=\sum_{2\le q\le D}b_{N,q}\Pi_q(m)$ with the
same full aliases as in (I18), its owned coefficient bound and (I96)
now give
$$
\begin{aligned}
\sup_{m\in\mathbb Z}|T_{N,\le D}(m)|
 &\le\frac1L\sum_{q\le D}\frac{\sigma(q)}{\varphi(q)}
 \le\frac{DW(2)}L,\\
|\mathscr J_N(T_{N,\le D})|
 &\ll\frac{\epsilon_N}{L^2}
 \left(\frac{h^2D^2}{N}+h^3D\right),\qquad 2\le D\le N.
\end{aligned}
\tag{I97}
$$
For the second row, the interior sum uses the unchanged interval-sum
and variation bounds in (I92)--(I93). Its endpoint uses the first row
of (I97) and the actual $e_{N,H}\ll h^3\epsilon_N$ from (I75).
Thus the endpoint's factor $\log(2D)$ in the earlier bound is removed
by retaining cancellation between primitive numerators of each $q$.

With $\kappa_\star$ from (I94), fix any $0\le\eta<1$ and set
$$
\widehat D_N=
\left\lfloor\frac{\sqrt N}{h}e^{\kappa_\star\Omega}L^\eta\right\rfloor,
\qquad T_{N,>\widehat D_N}=R_N-d_N-T_{N,\le\widehat D_N}.
$$
For sufficiently large $N$, $2\le\widehat D_N\le N$ and
$\widehat D_N\asymp N^{3/4}e^{(\kappa_\star-\lambda)\Omega}L^\eta$.
Substituting this cut in (I97) and using linearity yields
$$
\mathcal A_{N,H}
=\mathscr J_N(d_N+T_{N,>\widehat D_N})
+O\left(
 e^{-(c_\star-2\kappa_\star)\Omega}L^{2\eta-2}
 +e^{-(\Delta_\star-\kappa_\star)\Omega}L^{\eta-2}
\right).
\tag{I98}
$$
Both exponential factors are bounded by one, and both logarithmic
powers tend to zero for each fixed $\eta<1$. No uniform convergence
as $\eta\uparrow1$ is asserted. At $\eta=0$ the same cut as (I95)
has a smaller endpoint allowance; every fixed $\eta>0$ also pays a
larger complete frequency sector.

The retained aliases have $q>\widehat D_N$ and $j<N/\widehat D_N$.
Their actual signs, coprimality, endpoint and constant channel remain
coupled. The still required estimate is
$\mathscr J_N(d_N+T_{N,>\widehat D_N})=o(1)$. This is a refinement
of the project application of existing arithmetic inputs, with no
mathematical-priority claim or Lean certification. It supplies no
complete same-integer signed Robin bound or RH proof.

The uniform estimate (I97) also permits using its two allowances
directly, without restricting the logarithmic gain to a fixed power.
Define
$$
\mathfrak D_{\mathrm{int}}
 =\frac{\sqrt N}{h}\epsilon_N^{-1/2}L,\qquad
\mathfrak D_{\mathrm{end}}
 =h^{-3}\epsilon_N^{-1}L^2,\qquad
D_N^\circ=
\left\lfloor
\frac{\min(\mathfrak D_{\mathrm{int}},\mathfrak D_{\mathrm{end}})}{\log L}
\right\rfloor.
\tag{I99}
$$
The original parameter family has
$h\asymp N^{-1/4}e^{\lambda\Omega}$, hence both allowances are
$N^{3/4}e^{O(\Omega)}$ times a fixed logarithmic power. Since
$\Omega=o(L)$, eventually $2\le D_N^\circ\le N$. Equation (I97)
then reads
$$
\begin{aligned}
|\mathscr J_N(T_{N,\le D_N^\circ})|
 &\ll
 \left(\frac{D_N^\circ}{\mathfrak D_{\mathrm{int}}}\right)^2
 +\frac{D_N^\circ}{\mathfrak D_{\mathrm{end}}}
 \ll\frac1{(\log L)^2}+\frac1{\log L}=o(1),\\
\mathcal A_{N,H}
 &=\mathscr J_N(d_N+T_{N,>D_N^\circ})
   +O(1/\log L),\qquad
T_{N,>D_N^\circ}=R_N-d_N-T_{N,\le D_N^\circ}.
\end{aligned}
\tag{I100}
$$
In the fixed regime $\Delta_\star\ge c_\star/2$, the interior
allowance is eventually smaller and
$D_N^\circ\asymp(\sqrt N/h)e^{c_\star\Omega/2}L/\log L$.
In the fixed regime $\Delta_\star<c_\star/2$, the endpoint allowance
is eventually smaller and
$D_N^\circ\asymp(\sqrt N/h)e^{\Delta_\star\Omega}L^2/\log L$.
These comparisons follow from
$\mathfrak D_{\mathrm{end}}/\mathfrak D_{\mathrm{int}}
\asymp e^{(\Delta_\star-c_\star/2)\Omega}L$;
the equality case belongs to the first regime.
Thus $D_N^\circ/\widehat D_N\to\infty$ for each fixed
$0\le\eta<1$ in (I98). This deduction uses the uniform finite-$D$
estimate (I97), rather than substituting a varying $\eta$ into its
fixed-parameter consequence (I98).

This is an optimization of the two existing error allowances,
with no additional cancellation theorem or mathematical-priority
claim. The original aliases, endpoint and constant are retained.
The still missing estimate is
$\mathscr J_N(d_N+T_{N,>D_N^\circ})=o(1)$; the larger paid sector
does not settle that estimate, the signed Robin bound or RH.

## Pay a complete top band of reduced denominators

Reuse the all-start classical short-interval Mobius estimate in the
[existing source contract](../Analytic/shortuniformity2026robininterfaces.md#a-stronger-error-on-longer-mobius-intervals).
Use its same fixed $\theta_0=7/12+\eta$ from (I48), with
$c_\star\le c_{\theta_0}$ as allowed by the original common-constant
choice in (I54)--(I59). Keep that $c_\star$, $\lambda$ and $H$ fixed.
No new Mobius distribution theorem is assumed or proved here.

For any fixed $C>0$, let the integer $W$ satisfy
$N^{3/4}e^{-C\Omega}\le W\le N^{3/4}e^{C\Omega}$, and put
$T_{\mathrm{top},W}=\sum_{N-W<q\le N}b_{N,q}\Pi_q$.
This band eventually has $q>N/2$, so its complete coefficients (I19)
have exactly the alias $j=1$. Apply the already owned inversion (I96)
and write $q=td$. Squarefreeness gives the exact finite identity
$$
T_{\mathrm{top},W}(m)
=\frac1L\sum_{t\le N}\frac{\mu(t)^2}{t}
 \sum_{\substack{(N-W)/t<d\le N/t\\(d,t)=1}}
 \mu(d)\log\frac N{td}\,\mathcal S_d(m).
\tag{I101}
$$
Indeed, on squarefree $q$, $\mu(q)\mu(q/d)=\mu(d)$;
$\mu(t)^2$, $\mu(d)$ and $(d,t)=1$ retain precisely those terms.
This is not a replacement of the original signs by absolute values.

Set $K=\lceil\epsilon_N^{-2}\rceil$ and
$U=\lceil\epsilon_N^{-4}\rceil$. For $t\le K$ put
$x=(N-W)/t$, $y=W/t$, and let $\mathcal S(t)$ be the positive
integers whose prime factors all divide $t$. The standard finite
Euler-factor convolution is
$$
\mu(n)\mathbf1_{(n,t)=1}
=\sum_{\substack{s\mid n\\s\in\mathcal S(t)}}\mu(n/s).
$$
For $s\le U$, the interval start $x/s=N\exp(O_C(\Omega))$ and
its full length $y/s=N^{3/4}\exp(O_C(\Omega))$. Moreover
$\Omega(x/s)=\Omega(N)+O_C(\Omega^2/L)=\Omega(N)+o(1)$.
Apply the same $\theta_0$ supplier to prefixes of admissible length;
shorter prefixes use the trivial bound. The fixed power surplus
$3/4-\theta_0>0$ absorbs the latter in $y\epsilon_N/s$.
Thus each such prefix is $O_C(y\epsilon_N/s)$, with the unchanged
exponential constant.

The tail $s>U$ must also be retained. Set
$P_t=\prod_{p\mid t}(1-p^{-1/2})^{-1}$. Ordering the distinct prime
factors and using $p_i\ge i+1$ gives
$P_t\le\exp(O(\sqrt{\log(2t)}))=\exp(O(\sqrt\Omega))$ for $t\le K$.
The convergent positive Euler product implies
$$
\sum_{\substack{s>U\\s\in\mathcal S(t)}}s^{-1}
\le U^{-1/2}P_t,\qquad
\#\{s\le N:s\in\mathcal S(t)\}\le\sqrt N P_t.
$$
An interval contains at most $y/s+1$ integers. Its total tail is
therefore at most $yU^{-1/2}P_t+\sqrt N P_t=O_C(y\epsilon_N)$.
Summing the small-$s$ bounds with
$\sum_{s\in\mathcal S(t)}s^{-1}=t/\varphi(t)$ yields
$$
\sup_{0\le u\le y}
\left|\sum_{\substack{x<d\le x+u\\(d,t)=1}}\mu(d)\right|
\ll_C\frac t{\varphi(t)}\frac Wt\epsilon_N,
\qquad t\le K.
\tag{I102}
$$
This uses the mother theorem on all those starts; the three scalar
bounds for $A,B,\delta_{N,H}$ alone would not imply (I102).

For integer $N\le m\le2N$, the actual weight on $[x,x+y]$ is
$$
w_{t,m}(z)=\log\frac N{tz}
\left(\frac{m+1/2}{z}-\lfloor m/z\rfloor-\frac12\right).
$$
At integer $z=d$ this equals the weight in (I101). Since
$tW/N=o(1)$ for $t\le K$, there are only $O(1)$ floor jumps, each
of size $O(W/N)$. On smooth pieces
$|w_{t,m}'|\ll t/N+Wt^2/N^2$. Consequently
$$
\|w_{t,m}\|_\infty+\operatorname{Var}_{[x,x+y]}w_{t,m}\ll_C W/N.
\tag{I103}
$$
The values at the actual integer thresholds are included. Abel
summation with (I102) controls the $t\le K$ terms in (I101) by
$O_C(W^2\epsilon_N/(NL))$, because the already owned first moment
$\sum_{t\le X}t/\varphi(t)\ll X$ gives
$\sum_t(t/\varphi(t))/t^2<\infty$ by dyadic summation.
For $t>K$, use $|\mathcal S_d(m)|\le1/2$ on the integer grid:
$$
\frac W{NL}\sum_{K<t\le N}\frac1t\left(\frac Wt+1\right)
\ll\frac{W^2}{NLK}+\frac WN
\ll_C\frac{W^2\epsilon_N}{NL}.
$$
Here $K^{-1}\le\epsilon_N^2$ and $W\epsilon_N\gg L$.
Thus the complete primitive band, including every coprime numerator,
satisfies
$$
\max_{N\le m\le2N}|T_{\mathrm{top},W}(m)|
\ll_C\frac{W^2\epsilon_N}{NL},\qquad
|\mathscr J_N(T_{\mathrm{top},W})|
\ll_C\frac{h^2W^2\epsilon_N^2}{NL^2}.
\tag{I104}
$$
For the second bound use the actual coefficients in (I91):
$\sum_{m=N}^{2N}|k_{N,m}|+|e_{N,H}|\ll h^2\epsilon_N$.
The term $e_{N,H}T_{\mathrm{top},W}(2N)$ is included.

Take
$$
W_N^\circ=\left\lfloor
\frac{\sqrt N}{h\epsilon_N}\frac L{\log L}\right\rfloor,
\qquad
\mathcal R_N^\circ
=d_N+\sum_{D_N^\circ<q\le N-W_N^\circ}b_{N,q}\Pi_q.
\tag{I105}
$$
This width remains in the stated $N^{3/4}\exp(O(\Omega))$ family.
Both $D_N^\circ$ and $W_N^\circ$ are $o(N)$, so the two deleted
bands are disjoint eventually. Equations (I100) and (I104) give
$$
|\mathscr J_N(T_{\mathrm{top},W_N^\circ})|
\ll(\log L)^{-2},\qquad
\mathcal A_{N,H}=\mathscr J_N(\mathcal R_N^\circ)+O(1/\log L).
\tag{I106}
$$
The width satisfies
$W_N^\circ/H\asymp e^{\Delta_\star\Omega}L/\log L\to\infty$.
A direct absolute-value estimate for the top band loses the extra
$\epsilon_N$ in its pointwise bound, giving at this width an
allowance $O(\epsilon_N^{-1}/(\log L)^2)$ that does not vanish.
The coprime-prefix estimate is the quantitative gain used here.

This is an application of existing short-interval and finite-moment
inputs to a reduced-denominator band, distinct from the original-index
band (I49). It makes no new-supplier, priority or Lean-certification
claim. Every remaining coefficient still uses the original cutoff
$N$ and its full alias list; $\mathcal R_N^\circ$ is not a residual
reweighted at $N-W_N^\circ$. The constant and endpoint are retained.
The estimate $\mathscr J_N(\mathcal R_N^\circ)=o(1)$ remains missing,
as do the complete same-integer signed Robin bound and RH proof.

The [Bettin--Chandee applicability note](bettin2018trilinear.md)
records the direct alias-split boundary and excludes the withdrawn
stronger Kloosterman-fraction claim from the available suppliers.

## A narrower numerator list for the interior linear functional

The numerator cut (I28)--(I30) controls the weighted residual norm.
Here use instead the bounded variation of the actual linear weight
in (I91)--(I93). This is a direct application of the same geometric
sum, sine and finite-moment inputs; it is not a new exponential-sum
estimate. Keep $D_N^\circ,W_N^\circ,\mathcal R_N^\circ$ from
(I99)--(I106), with every original coefficient and alias.

Define the finite transform of the interior weight by
$$
\mathscr F_N(\theta)=\sum_{m=N}^{2N}k_{N,m}e(m\theta).
$$
The geometric sum and the already supplied bound on
$\|k_N\|_\infty+\operatorname{Var}k_N$ give, by discrete Abel summation,
$$
|\mathscr F_N(\theta)|
\ll\frac{h^2\epsilon_N}{N\|\theta\|},
\qquad \theta\notin\mathbb Z.
\tag{I107}
$$
This uses the actual closed integer interval and both its boundary
values. It does not include the separate $e_{N,H}f(2N)$ term.

Write $r^*=\min(r,q-r)$. For any integer $s\ge1$, consider only
$D_N^\circ<q\le N-W_N^\circ$ and $r^*>s$. Using (I107),
$|1-e(-r/q)|\ge4r^*/q$ and the already owned first positive moment,
their complete contribution to the interior part of $\mathscr J_N$
is bounded by
$$
\begin{aligned}
\frac1L\sum_q\sum_{\substack{1\le r<q\\(r,q)=1\\r^*>s}}
\left|\frac{b_{N,q}\mathscr F_N(r/q)}{q(1-e(-r/q))}\right|
&\ll\frac{h^2\epsilon_N}{NL}
 \sum_{q\le N}q|b_{N,q}|\sum_{r^*>s}\frac1{(r^*)^2}\\
&\ll\frac{Nh^2\epsilon_N}{L^2s}.
\end{aligned}
\tag{I108}
$$
At most two numerators have any given $r^*$, so the inner tail is
$O(1/s)$. The other factor follows from
$\sum_{q\le N}q|b_{N,q}|\ll N^2/L$, exactly the finite-moment input
of (I92). Coprimality is relaxed only in the positive allowance;
the retained sum still has its actual coprime numerators.

Choose the integer cutoff
$$
s_N^\circ=\left\lceil
 \frac{Nh^2\epsilon_N\log L}{L^2}\right\rceil.
\tag{I109}
$$
Its argument tends to infinity, and
$$
s_N^\circ\asymp
 N^{1/2}e^{-\Delta_\star\Omega}\frac{\log L}{L^2},
\qquad s_N^\circ=o(D_N^\circ).
$$
The allowance in (I108) is $O(1/\log L)$, matching the paid error
in (I106).

The remaining finite scalar is
$$
\begin{aligned}
\mathcal C_N^\circ={}&d_N\mathscr F_N(0)\\
&-\sum_{D_N^\circ<q\le N-W_N^\circ}
 \ \sum_{\substack{1\le r<q\\(r,q)=1\\r^*\le s_N^\circ}}
 \frac{b_{N,q}\mathscr F_N(r/q)}{q(1-e(-r/q))}\\
&+e_{N,H}\mathcal R_N^\circ(2N),\\
\mathcal A_{N,H}={}&\frac{\mathcal C_N^\circ}{L}
 +O(1/\log L).
\end{aligned}
\tag{I110}
$$
The last line follows from (I106) and (I108). The interior sum has at
most $2Ns_N^\circ$ frequency entries, of order at most
$N^{3/2}e^{-\Delta_\star\Omega}\log L/L^2$. This is a bound on
that list, not on the cost of computing its coefficients or on the
complete endpoint. Conjugate pairing makes $\mathcal C_N^\circ$ real.

The endpoint remains the full $e_{N,H}\mathcal R_N^\circ(2N)$,
including its constant and every retained numerator. No high-numerator
endpoint deletion is paid by (I107)--(I108). In particular this is a
reduction of a linear functional, not replacement of the response by
one frequency-truncated function at every evaluation port.

The still missing estimate is $\mathcal C_N^\circ=o(L)$ for every
sufficiently large original integer $N$ in the fixed family. The paid
error makes this equivalent to $\mathcal A_{N,H}=o(1)$ within this
reduction; neither estimate is established here. The comparison
shrinks the internal list relative to (I30) at $m\asymp N$, where
that norm cut retains numerators up to $N/L^b$, $0<b<2$. It supplies
no new cancellation theorem, complete signed Robin bound, RH proof,
mathematical-priority claim or Lean certification.

## An angular cut that also pays the actual endpoint

Retain the same original $N,H,A,B,e_{N,H}$ and coefficients. The
following application strengthens the frequency reduction using
integer sample locations, the primitive inversion (I96), geometric
summation and the classical divisor bound. It also controls the
actual endpoint; it does not estimate the remaining signed sum.

For $V\ge2$, let $\Pi^{\rm far}_{q,V}$ denote the original primitive
Fourier sum $\Pi_q$ restricted to $\|r/q\|\ge1/V$, and put
$\Pi^{\rm near}_{q,V}=\Pi_q-\Pi^{\rm far}_{q,V}$. Define its
nonprimitive counterpart
$$
S_{d,V}(m)=-\frac1d
 \sum_{\substack{1\le r<d\\\|r/d\|\ge1/V}}
 \frac{e(mr/d)}{1-e(-r/d)},\qquad S_{1,V}=0.
$$
The cutoff depends only on the frequency value and is unchanged by
reduction. Therefore the same finite grouping and inversion as in
(I96) give, for any $\mathcal I\subseteq\{2,\ldots,N\}$,
$$
\begin{aligned}
\Pi^{\rm far}_{q,V}(m)
 &=\sum_{d\mid q}\frac{\mu(q/d)}{q/d}S_{d,V}(m),\\
T_{\mathcal I,V}(m)
 :=\sum_{q\in\mathcal I}b_{N,q}\Pi^{\rm far}_{q,V}(m)
 &=\sum_{d\le N}\gamma_{\mathcal I,N}(d)S_{d,V}(m),\\
\gamma_{\mathcal I,N}(d)
 &=\sum_{\substack{t\le N/d\\dt\in\mathcal I}}
 \frac{\mu(t)}t b_{N,dt}.
\end{aligned}
\tag{I111}
$$
Every $b_{N,dt}$ here keeps all of its original aliases. By
$dt/\varphi(dt)\le[d/\varphi(d)][t/\varphi(t)]$, the supplied
coefficient bound and first moment imply, uniformly in $\mathcal I$,
$$
|\gamma_{\mathcal I,N}(d)|
\ll\frac d{\varphi(d)}\frac{1+\log(N/d)}L
\ll\frac d{\varphi(d)}\le\tau(d).
\tag{I112}
$$
The harmonic weighted first moment follows by partial summation;
$\tau$ is the ordinary divisor-count function. These are positive
bounds on the exact regrouping, not replacement coefficients.

A discrete primitive for the truncated nonprimitive response is
$$
\begin{aligned}
P_{d,V}(m)&=\frac1{4d}
 \sum_{\substack{1\le r<d\\\|r/d\|\ge1/V}}
 \frac{e(mr/d)}{\sin^2(\pi r/d)},\qquad P_{1,V}=0,\\
P_{\mathcal I,V}(m)&=\sum_{d\le N}
 \gamma_{\mathcal I,N}(d)P_{d,V}(m),\\
P_{\mathcal I,V}(m+1)-P_{\mathcal I,V}(m)
 &=T_{\mathcal I,V}(m).
\end{aligned}
\tag{I113}
$$
Indeed $(e(x)-1)/(4\sin^2(\pi x))=-1/(1-e(-x))$ term by term.

For integer $m$ and $d\nmid m$, put
$j_d(m)=\min_{k\in\mathbb Z}|m-kd|$. It is a positive integer,
at most $d/2$. On the central numerator interval the supremum plus
total variation of the two coefficients in $S_{d,V}$ and $P_{d,V}$
is respectively $O(V/d)$ and $O(V^2/d)$. Abel summation in $r$,
using the geometric-sum bound $O(d/j_d(m))$, gives
$$
\begin{aligned}
|S_{d,V}(m)|&\ll V/j_d(m),&
|P_{d,V}(m)|&\ll V^2/j_d(m)&& (d\nmid m),\\
|S_{d,V}(m)|&\le1/2,&
|P_{d,V}(m)|&\ll V&& (d\mid m).
\end{aligned}
\tag{I114}
$$
For the second row the cutoff is symmetric under $r\mapsto d-r$,
and $[1-e(-x)]^{-1}+[1-e(x)]^{-1}=1$, which gives the first bound
also for a self-paired numerator. The sine bound gives the other:
$d\sum_{r\ge\max(1,\lceil d/V\rceil)}r^{-2}\ll V$. Thus exact
resonances are included without division by a zero distance.

Write $\tau_3(n)=\sum_{d\mid n}\tau(d)\le\tau(n)^2$. Directly
reuse the arbitrary-integer divisor bound in
[Nicolas's existing source note](../ArithSums/nicolas1971repartition.md#objective-and-arbitrary-integer-decomposition),
printed p.117, equations (6)--(8): for each fixed $0<\nu<1$, its
fixed maximizing reference gives $\tau(n)\ll_\nu n^\nu$.
No new divisor theorem is needed. If $j_d(m)=j>0$, then $d$ divides
$m-j$ or $m+j$. Hence (I112)--(I114) give
$$
\begin{aligned}
|T_{\mathcal I,V}(m)|
 &\ll\tau_3(m)+V\sum_{1\le j\le N/2}
  \frac{\tau_3(m-j)+\tau_3(m+j)}j,\\
|P_{\mathcal I,V}(m)|
 &\ll V\tau_3(m)+V^2\sum_{1\le j\le N/2}
  \frac{\tau_3(m-j)+\tau_3(m+j)}j,\\
\sup_{N\le m\le2N+1}|T_{\mathcal I,V}(m)|&\ll_\eta N^\eta V,\\
\sup_{N\le m\le2N+1}|P_{\mathcal I,V}(m)|&\ll_\eta N^\eta V^2
 \qquad(\eta>0\text{ fixed}).
\end{aligned}
\tag{I115}
$$
These suprema are over integers. All divisor arguments are positive
and at most $3N$. To obtain the final two lines, choose $\nu$
sufficiently small in the cited bound and absorb the harmonic
logarithm into the remaining fixed $N^\eta$ allowance. The constants
are independent of $V$ and $\mathcal I$.

Apply the exact discrete integration-by-parts identity
$$
\begin{aligned}
\sum_{m=N}^{2N}k_{N,m}T_{\mathcal I,V}(m)
={}&k_{N,2N}P_{\mathcal I,V}(2N+1)
 -k_{N,N}P_{\mathcal I,V}(N)\\
&-\sum_{m=N+1}^{2N}(k_{N,m}-k_{N,m-1})P_{\mathcal I,V}(m).
\end{aligned}
$$
The original weight variation and $|e_{N,H}|\ll h^3\epsilon_N$
therefore pay both terms of the unchanged functional:
$$
|\mathscr J_N(T_{\mathcal I,V})|
\ll_\eta\frac{N^\eta\epsilon_N}{L}
 \left(\frac{h^2V^2}{N}+h^3V\right).
\tag{I116}
$$
In particular the second allowance explicitly bounds
$|e_{N,H}T_{\mathcal I,V}(2N)|/L$. The exact $2N+1$ primitive
sample in integration by parts was included in (I115).

For any fixed $0<\kappa<1/4$, set
$$
\begin{aligned}
V_N&=\lfloor N^{3/4-\kappa}\rfloor,\\
\mathcal R_{N,\kappa}^\sharp(m)
 &=d_N+\sum_{D_N^\circ<q\le N-W_N^\circ}
  b_{N,q}\Pi^{\rm near}_{q,V_N}(m).
\end{aligned}
$$
Take $\eta=\kappa/4$ in (I116). Its two allowances are
$N^{\eta-2\kappa}e^{-\Delta_\star\Omega}/L$ and
$N^{\eta-\kappa}e^{(3\lambda-c_\star)\Omega}/L$.
Since $\Omega=o(\log N)$, (I106) and (I116) imply
$$
\begin{aligned}
|\mathscr J_N(T_{\mathcal I,V_N})|&\ll_\kappa N^{-\kappa/2},\\
\mathcal A_{N,H}
 &=\mathscr J_N(\mathcal R_{N,\kappa}^\sharp)
  +O(1/\log L)+O_\kappa(N^{-\kappa/2}),\\
\#\{\text{retained middle frequency entries}\}
 &\ll N^2/V_N+N\ll N^{5/4+\kappa}.
\end{aligned}
\tag{I117}
$$
In the first line use the retained denominator set for
$\mathcal I$. No condition $3\lambda<c_\star$ is added: a positive
subpower exponential in the second allowance is paid by the fixed
$N^{-\kappa}$ margin. Every retained numerator satisfies
$r^*<q/V_N\ll N^{1/4+\kappa}$.

Unlike the interior-only cut (I110), this reduction uses the same
truncated response at every original evaluation, including the
actual endpoint. The endpoint change is paid in (I116), rather than
assumed harmless. The count concerns frequency entries only, not
coefficient computation or overall arithmetic cost. The constant
$d_N$ and all original aliases remain. In particular $q>N/2$ still
has its actual $j=1$ alias, and $r=1,q-1$ remain in that sector.
There is no newly created second long averaging variable.

This is a repository application of existing finite Fourier,
integer-divisor and weight-variation inputs, not a new Möbius
cancellation theorem or a claim of mathematical priority. The
argument needs fixed $\kappa>0$ and supplies no uniform
$\kappa=0$ or varying-$\kappa$ endpoint. It has not been Lean
compiled. The remaining same-integer estimate
$\mathscr J_N(\mathcal R_{N,\kappa}^\sharp)=o(1)$, the complete
signed Robin inequality and RH remain unresolved.

## A fixed Mertens input sufficient for the original functional

Keep the original family (I59), its actual band, all coefficients and the
complete functional (I91). Suppose, as an additional input, that a fixed
$1/2\le b<5/8$ satisfies $\zeta(s)\ne0$ for $\Re s>b$.
Choose $b<\beta<5/8$. Reuse (I60) for both errors
$M(x)\ll_\beta x^\beta$ and $\psi(x)-x\ll_\beta x^\beta$;
no new zero-free or Mertens theorem is used.

On $Q\le t\le N$, the actual prefix $M(t)-M(Q)$ is
$O_\beta(N^\beta)$. The supremum plus variation of the weights
$\log(N/t)$, $\log(N/t)/t$ and
$\log(N/t)(1/t-1/N)$ is respectively $O(h)$, $O(h/N)$ and
$O(h^2/N)$. Here $H/N\asymp h=(H-1/2)/N$, so the original
half-integer convention and the strict lower cutoff do not change.
Abel summation, with those same prefixes, gives
$$
\begin{aligned}
|A|+|B|/N&\ll_\beta hN^{\beta-1},\\
|\delta_{N,H}|+|e_{N,H}|&\ll_\beta h^2N^{\beta-1}.
\end{aligned}
\tag{I118}
$$
For the second line use the exact endpoint identity (I75), including
$B/[2N(2N+1)]$, and $Nh\gg1$. This is a conditional estimate for
the actual endpoint, not its deletion.

The residual estimate already derived after (I60) is uniform on the
whole original integer grid, including $m=2N$:
$\sup|R_N(m)|\ll_\beta N^\beta/L$. Moreover the original weights
satisfy $\sum_{m=N}^{2N}|k_{N,m}|\ll |A|+|B|/N$.
Apply these facts and (I118) directly to (I91), retaining its endpoint:
$$
\begin{aligned}
|\mathcal A_{N,H}|=|\mathscr J_N(R_N)|
&\ll_\beta \frac{hN^{2\beta-1}}{L^2}\\
&\ll_\beta \frac{N^{2\beta-5/4}e^{\lambda\Omega}}{L^2}
=o(1).
\end{aligned}
\tag{I119}
$$
The last step uses fixed $\beta<5/8$ and $\Omega=o(\log N)$.
It applies to every sufficiently large original $N$ under the added
input, with the same actual $A,B$ and endpoint.

A global bound $M(x)\ll x^\vartheta$ for one fixed
$1/2\le\vartheta<5/8$ is also sufficient, with exponent slack.
Indeed the classical partial-summation formula for $1/\zeta$ is
holomorphic on $\Re s>\vartheta$ under that bound and agrees with
$1/\zeta$ on $\Re s>1$. Its continuation excludes zeros on the
former half-plane. Choose $\vartheta<\beta<5/8$ and reuse (I60).
The residual bound at the identical exponent $\vartheta$ is not being
deduced from bandwise Abel summation alone: (I33) also contains the
prime error. The slack supplies that error through the existing
analytic interface.

For example, the [existing local fourth-moment source application](../Analytic/verjovsky2026mobiussmoothing.md#a-fixed-local-fourth-moment-input-for-the-original-robin-functional)
identifies a sufficient input $\mathcal M_{4,c}(N)\ll N^\nu$ for
fixed $c>0$ and $0\le\nu<1/32$. That deterministic estimate is
not established here. The recorded boundaries near $7/8$ in the
OpenAI and Liu sources do not meet the $5/8$ hypothesis. This is a
conditional parameter application of existing theorems, not a new RH
criterion, an unconditional bound for (I117)'s retained near sector,
a mathematical-priority claim or Lean certification. The complete
signed Robin objective and RH remain unresolved.


## A sharper fixed fourth-moment input for the same functional

The [classical polynomial-evaluation application](../Analytic/verjovsky2026mobiussmoothing.md#classical-polynomial-evaluation-sharpens-the-fixed-moment-input)
gives a stronger interface than the first-derivative moment estimate
used above. Keep the original family (I59), the actual functional
(I91), and one fixed $c>0$. Assume, as an additional deterministic
input, that
$\mathcal M_{4,c}(N)\ll N^\nu$ for every sufficiently large integer
$N$, with one fixed $0\le\nu<1/8$. The source's same local arc and
Möbius coefficients are retained.

The cited application supplies
$$
|M(N)|\ll_c\sqrt{\log(2N)}
\left(\sqrt N\,\mathcal M_{4,c}(N)+1\right).
$$
Consequently, with $\theta=1/2+\nu$, for every fixed $\delta>0$,
$$
M(x)\ll_{c,\nu,\delta}x^{\theta+\delta}.
\tag{I120}
$$
The implied constants also retain the assumed moment-bound constant.
To use the required prime error, take any $\Re s>\theta$, choose
$0<\delta<\Re s-\theta$, and apply the already used
partial-summation continuation of $1/\zeta$ with (I120). This excludes
zeros throughout $\Re s>\theta$. Choose a fixed
$\theta<\beta<5/8$ and reuse (I60) for both $M(x)$ and
$\psi(x)-x$ at exponent $\beta$; there is no same-exponent
prime-error assertion obtained from bandwise Abel summation alone.

Apply (I118)--(I119) with this $\beta$. For every fixed $\eta>0$,
choose $\beta-\theta$ sufficiently small and absorb the original
$e^{\lambda\Omega}$ and logarithmic factors into the remaining
$N^\eta$ allowance. The result is
$$
|\mathcal A_{N,H}|=|\mathscr J_N(R_N)|
\ll_{c,\nu,\eta}N^{2\nu-1/4+\eta}.
\tag{I121}
$$
All original fixed parameters may also enter the constant. Taking
$0<\eta<1/4-2\nu$ gives $o(1)$ on every sufficiently large original
integer $N$. This reuses the complete functional, including
$e_{N,H}=B/(2N+1)-A/2$ and $m=2N$, with the same strict lower band
cutoff and half-integer convention. It supplies no uniform
$\nu=1/8$ endpoint or estimate for a moment hypothesis given only
on a subsequence.

Using the exact correlation identity in the same source application,
another sufficient input is
$\mathfrak C_{4,c}(N)\ll N^{5/2-\xi}$ for a fixed $0<\xi\le1/2$.
It gives $\nu=1/8-\xi/4$ and hence
$|\mathscr J_N(R_N)|\ll_\eta N^{-\xi/2+\eta}$, with decay when
$0<\eta<\xi/2$. This weakens the previously recorded
$N^{17/8-\xi}$ sufficient correlation input; it does not prove either
bound or replace the signed fourfold sum by a diagonal.

The new parameter range is a repository application of classical
polynomial evaluation, Taylor approximation and the already owned
analytic interfaces, without a mathematical-priority claim or Lean
certification. The deterministic moment or correlation bound remains
unpaid. The complete signed Robin estimate and RH remain unresolved.


## A single actual endpoint already obstructs a uniform response supplier

Keep (I59), the complete mean $d_N$ from (I17), and the cutoffs
of (I105) and (I117). The following is a repository-derived analytic
application, without a mathematical-priority claim or Lean certification.
Its finite-height input is the already cited Platt--Trudgian theorem;
no zero computation is repeated.

For $q>N/2$, the original alias sum has exactly $j=1$, so
$b_{N,q}=\mu(q)\log(N/q)/L$. Define only the first pair of its actual
harmonics, together with the unchanged original mean:
$$
\begin{aligned}
P_q^{(1)}(m)
 &=-\frac1q\left[\frac{e(m/q)}{1-e(-1/q)}
                  +\frac{e(-m/q)}{1-e(1/q)}\right],\\
R_N^{(1)}(m)
 &=d_N+\sum_{N/2<q\le N-W_N^\circ}
       \frac{\mu(q)\log(N/q)}L P_q^{(1)}(m).
\end{aligned}
\tag{I122}
$$
Eventually $D_N^\circ<N/2<N-W_N^\circ$ and $V_N<N/2$.
Both numerators $1,q-1$ therefore remain in (I117)'s near sector.
This selects actual terms of that response; it does not replace the
Möbius coefficients or assert that separately bounding this selection
is necessary to bound their signed total.

For any fixed $1/2\le\alpha<1$, the additional hypothesis
$$
L|R_N^{(1)}(2N)|\ll_\eta N^{\alpha+\eta}
\quad\text{for every fixed }\eta>0
\text{ and every sufficiently large original integer }N
\tag{I123}
$$
implies $\zeta(s)\ne0$ on $\Re s>\alpha$. In particular its
$\alpha=1/2$ case implies RH. The estimate (I123) remains unproved.

### Transferring the original endpoint without deleting its top cutoff

Pairing the two Fourier terms gives exactly
$$
P_q^{(1)}(m)=-\frac1q\left[\cos(2\pi m/q)
                     +\cot(\pi/q)\sin(2\pi m/q)\right].
$$
Since $q^{-1}\cot(\pi/q)=\pi^{-1}+O(q^{-2})$, at $m=2N$
this is $-\pi^{-1}\sin(4\pi N/q)+O(N^{-1})$ for $q>N/2$.
The accumulated error after multiplying $R_N^{(1)}$ by $L$ is $O(1)$.
For real $y>1$, put
$$
\begin{aligned}
F(y)={}&\log y
 +\frac12\sum_{n\le y}\mu(n)\log(y/n)(1-1/n)\\
 &-\frac1\pi\sum_{y/2<n\le y}
          \mu(n)\log(y/n)\sin(4\pi y/n).
\end{aligned}
\tag{I124}
$$
Its first two terms at $y=N$ are exactly $Ld_N$.
If $W=W_N^\circ$ and $w=N-q<W$, then
$\log(N/q)\le2w/N$ and
$|\sin(4\pi N/q)|=|\sin(4\pi w/q)|\le8\pi w/N$ eventually.
Both vanish at the actual top endpoint. Hence
$$
LR_N^{(1)}(2N)
 =F(N)+O(1+W^3/N^2),\qquad W^3/N^2=N^{1/4+o(1)}.
\tag{I125}
$$
This pays the original top cutoff using absolute values and requires
no extra condition $3\lambda<c_\star$. For $N\le y<N+1$, the common
terms in the first sum change by $O(N^{-1})$ each. The derivative of
each common summand in the second sum is
$$
\frac1y\sin(4\pi y/n)
 +\frac{4\pi}{n}\log(y/n)\cos(4\pi y/n)=O(N^{-1})
 \quad(n\asymp N).
$$
Only a bounded number of bounded terms enter or leave at its moving
limits. Thus $F(y)-F(N)=O(1)$. Together with (I123)--(I125), this
gives $F(y)\ll_\eta y^{\alpha+\eta}$ for every fixed $\eta>0$.

### A Mellin kernel with no high-height cancellation

Consequently $\widehat F(s)=\int_1^\infty F(y)y^{-s-1}\,dy$ is
holomorphic on $\Re s>\alpha$. Initially for $\Re s>1$, absolute
convergence and the classical Möbius Dirichlet series give
$$
\begin{aligned}
\widehat F(s)&=\frac1{s^2}-\frac1{2s^2\zeta(s+1)}
                         +\frac{K(s)}{\zeta(s)},\\
K(s)&=\frac1{2s^2}
 -\frac1\pi\int_1^2\log v\sin(4\pi v)v^{-s-1}\,dv.
\end{aligned}
\tag{I126}
$$
The term $1/(2s^2)$ in $K$ comes from the original mean and must
remain. Since $1/\zeta(s+1)$ is holomorphic on this larger half-plane,
the identity theorem continues the holomorphic identity
$$
(s-1)\zeta(s)\left[\widehat F(s)-\frac1{s^2}
                         +\frac1{2s^2\zeta(s+1)}\right]
 =(s-1)K(s)
\tag{I127}
$$
to $\Re s>\alpha$. A zero $\rho$ there, of any multiplicity
$m_\rho$, would force $\operatorname{ord}_\rho K\ge m_\rho$.
Neither zero simplicity nor a reciprocal-derivative moment is used.

Here the necessary cancellation can be ruled out at every high height:
$$
|K(s)|\ge |s|^{-2}
\qquad(1/2\le\Re s\le1,\ |\Im s|\ge2^{16}).
\tag{I128}
$$
To prove this quantitative bound, set $a=\log2$ and
$f(u)=u\sin(4\pi e^u)$. Then
$f(0)=f(a)=f'(0)=0$ and $f'(a)=8\pi a$.
Three integrations by parts in (I126) give
$$
\begin{aligned}
K(s)&=\frac{1/2+8a\,2^{-s}}{s^2}
                         -\frac{\mathcal B(s)}{\pi s^3},\\
\mathcal B(s)&=f''(0)-f''(a)2^{-s}
                      +\int_0^af'''(u)e^{-su}\,du.
\end{aligned}
$$
For $z=4\pi e^u$ the derivatives are
$$
\begin{aligned}
f''(u)&=(u+2)z\cos z-uz^2\sin z,\\
f'''(u)&=(u+3)z\cos z-(3u+3)z^2\sin z-uz^3\cos z.
\end{aligned}
$$
Using $0\le u\le a<1$, $z<32$ and $3<\pi<4$ yields
$|f''(0)|<32$, $|f''(a)|<96$ and
$\int_0^a|f'''(u)|\,du<4\cdot32+6\cdot32^2+32^3$.
Thus $|\mathcal B(s)|<39168<2^{16}$ for $\Re s\ge0$.
On $1/2\le\Re s\le1$,
$|1/2+8a2^{-s}|\ge4\log2-1/2>3/2$.
For $|s|\ge2^{16}$ the remainder in $s^2K(s)$ is less than
$1/\pi<1/3$, proving (I128).

For the remaining finite heights, directly reuse
[Platt--Trudgian, Theorem 1, printed p.2](https://arxiv.org/abs/2004.09765v1),
as already recorded in the
[finite-height source application](../Analytic/polak2026finiterobinca.md#finite-height-residual-bounds-at-the-actual-critical-clock).
Its verified height $3000175332800$ exceeds $2^{16}$.
Conjugation covers negative heights, and the classical absence of real
zeros in $(0,1)$ covers height zero. Thus there are no low-height zeros
with real part greater than $\alpha\ge1/2$; this does not assert
low-height nonvanishing of $K$. Every higher possible zero contradicts
(I127)--(I128). The standard zero-free region $\Re s\ge1$ completes
the stated half-plane conclusion. At $\alpha=1/2$, functional-equation
symmetry gives RH.

### The method boundary concerns the response supplier, not signed cancellation

The original coefficient budget in (I91) gives only
$$
|\mathscr J_N(f)|\ll\frac{h^2\epsilon_N}{L}\|f\|_\infty,
\qquad h^2\epsilon_N\asymp N^{-1/2}e^{-\Delta_\star\Omega},
$$
where the supremum is over the original integer grid $N\le m\le2N$.
A sufficient response bound through this budget alone would be
$$
\|R_N^{(1)}\|_\infty
 =o\!\left(L\sqrt N\,e^{\Delta_\star\Omega}\right).
\tag{I129}
$$
Since $L^2e^{\Delta_\star\Omega}=N^{o(1)}$, (I129) already implies
(I123) at $\alpha=1/2$, hence RH. The obstruction is specific to
one actual endpoint and a specified actual harmonic pair plus mean;
unlike the compact kernel discussion around (I68), its high-height
nonvanishing is quantitative.

This does not show that $\mathscr J_N(R_N^{(1)})=o(1)$ or
$\mathscr J_N(R_{N,\kappa}^\sharp)=o(1)$ implies RH. Their actual
signed weights can use joint relations or inter-sector cancellation
without supplying (I129). In particular the total endpoint coefficient
is $(k_{N,2N}+e_{N,H})/L=O(h^3\epsilon_N/L)$, which is smaller
than the budget used above; paying that contribution does not require
a square-root bound on the response itself. Nor does this invalidate
(I118)--(I119), which also improve the band coefficients under their
additional hypothesis. No new bound for the signed functional,
complete Robin inequality or RH follows from this method obstruction.


## An absolute contour estimate cannot relax the fixed half-plane threshold

Keep the original family (I59), its exact coupled kernel (I65), and the
additional fixed zero-free-half-plane premise of (I60):
$1/2\le b<1$ and no zero of $\zeta$ in $\Re s>b$.
Choose any fixed $b<\sigma,\tau<1$. There is a fixed compact real
interval $I$ of positive length such that, for every sufficiently large
original integer $N$, the finite absolute majorant satisfies
$$
\begin{aligned}
\mathfrak B_N(\sigma,\tau;I)
 &:={1\over L^2}\int_{1/(4h)}^{1/(2h)}\int_I
 \left|\frac{N^{\sigma+\tau-1+i(t+y)}
  \mathcal K_N(\sigma+it,\tau+iy)}
 {\zeta(\sigma+it)\zeta(\tau+iy)}\right|\,dy\,dt\\
 &\gg_{b,\sigma,\tau}{hN^{\sigma+\tau-1}\over L^2}.
\end{aligned}
\tag{I130}
$$
The interval and lower-bound constant depend only on fixed parameters.
This measures the cost of taking absolute values inside the two contour
integrals. It gives no lower bound on the signed functional. The
application below reuses (I60), (I64), (I70) and the already owned
expansion of $H_q$ at zero; no new classical mean-value theorem,
mathematical-priority claim or Lean certification is asserted.

### A nonzero part of the exact kernel survives at height comparable to 1/h

Use $\Phi$ from (I67). The integral defining $H_q$ is holomorphic on
$\Re v>0$. The expansion after (I88), uniform for $1\le q\le2$
by (I70), gives
$$
\Phi(v)={\log2-3/4\over2v^2}+O(1)\qquad(v\longrightarrow0).
\tag{I131}
$$
Here $\log2<3/4$, for example by the strict trapezoidal upper bound
for the convex function $1/x$ on $[1,2]$. Thus $\Phi$ is not
identically zero. The identity theorem implies that it cannot vanish
on the entire line $\tau+i\mathbb R$. Choose $I$ about a nonzero point
so that $|\Phi(\tau+iy)|$ is bounded below on $I$. The actual
$|1/\zeta(\tau+iy)|$ also has a positive minimum there: the segment
is compact, zero-free, and avoids the pole at one.

Put $G(z)=\int_0^1r e^{-izr}\,dr$. For $u=\sigma+it$ with
$1/4\le ht\le1/2$, substitute $x=1-hr$ into the original $W_a$.
Uniformly on this growing-height rectangle,
$-\log(1-hr)=hr+O(h^2)$,
$(1-hr)^{\sigma-1}=1+O_\sigma(h)$ and
$e^{it\log(1-hr)}=e^{-ihtr}(1+O(h))$. Consequently
$$
\begin{aligned}
W_a(u)&=h^2G(ht)+O_\sigma(h^3),\\
W_a(u-1)-W_a(u)
 &=\int_a^1x^{u-2}(1-x)\log(1/x)\,dx=O_\sigma(h^3).
\end{aligned}
$$
The second estimate holds for every real $t$. Reuse the fixed-compact
relations from (I64)--(I67),
$p_N(v)=O(1)$ and $p_N(v)-Nq_N(v)=\Phi(v)+O(1/N)$, to obtain
$$
\begin{aligned}
\mathcal K_N(u,v)
 &=W_a(u)[p_N(v)-Nq_N(v)]
    +[W_a(u-1)-W_a(u)]p_N(v)\\
 &=h^2G(ht)\Phi(v)+O(h^3+h^2/N).
\end{aligned}
\tag{I132}
$$
This calculation is uniform for $v=\tau+iy$, $y\in I$.
It does not extend the compact-$u$ error term of (I67) to this height.
Since $\Re G(z)\ge\cos(1/2)/2>0$ on $1/4\le z\le1/2$,
(I132) gives $|\mathcal K_N(u,v)|\gg h^2$ throughout the rectangle
for all sufficiently large $N$. Both original endpoint contributions
remain in $p_N,q_N$.

### Actual reciprocal-zeta mass supplies the full width of the rectangle

The reciprocal growth bound in (I60), with exponent allowance $1/2$,
is uniform for $\sigma\le\Re s\le2$ at large heights. The reciprocal
is holomorphic on $\Re s>b$, with a removable zero at the pole of
$\zeta$. Cauchy's theorem between the lines $\sigma$ and $2$ gives
$$
\int_T^{2T}{dt\over\zeta(\sigma+it)}
 =\int_T^{2T}{dt\over\zeta(2+it)}+O_{b,\sigma}(T^{1/2})
 =T+O_{b,\sigma}(T^{1/2}).
\tag{I133}
$$
For the final equality directly apply the absolutely convergent
Möbius Dirichlet series underlying (I62). Its $n=1$ term contributes
$T$; the remaining integral is at most
$2\sum_{n\ge2}n^{-2}/\log n<\infty$ in modulus. Thus
$\int_T^{2T}|1/\zeta(\sigma+it)|\,dt\ge T/2$ eventually.
Take $T=1/(4h)$. Combine this actual mass, the fixed-$v$ reciprocal
minimum and (I132). Since the modulus of the outer $N$-power is
$N^{\sigma+\tau-1}$, this proves (I130) for each sufficiently large
original integer, without an average over $N$ or zero-residue assumptions.

### The paid two-scale smoothing preserves the obstruction

The same lower bound holds with the complete smoothed kernel
$\widetilde{\mathcal K}_N$ of (I89) in place of $\mathcal K_N$:
$$
\widetilde{\mathfrak B}_N(\sigma,\tau;I)
 \gg_{b,\sigma,\tau}{hN^{\sigma+\tau-1}\over L^2}.
\tag{I134}
$$
Use exactly the already paid scales $\eta=H^{-1}$ and
$\nu=N^{-1/2}$. Their bump multipliers satisfy
$|F_\ell(s)-1|\le e^{\ell|s|}-1$ by positivity and unit mass of
$\phi$. On this rectangle $\eta|u|=O(\eta/h)\to0$,
$\eta|u-1|\to0$, and $\nu|v|\to0$, since
$\eta/h=1/(Hh)\asymp N/H^2\to0$. Hence all three multipliers in
(I89) tend uniformly to one here. The fixed-compact bounds also give
$Nq_N(v)=O(1)$, so its exact formula and (I132) imply
$\widetilde{\mathcal K}_N(u,v)-\mathcal K_N(u,v)=o(h^2)$
uniformly. The same positive lower bound therefore survives.
This uses the original smoothing scales and retains its actual scalar
and endpoint accounting; it introduces no new contour-shift claim.

### The limitation concerns taking absolute values on fixed lines

At the original bandwidth, the lower-bound scale is
$$
{hN^{\sigma+\tau-1}\over L^2}
 \asymp{N^{\sigma+\tau-5/4}e^{\lambda\Omega}\over L^2}.
\tag{I135}
$$
For $\sigma+\tau\ge5/4$ this tends to infinity, including equality,
because $\lambda>0$ and $\Omega/\log L\to\infty$. If $b\ge5/8$,
every pair of fixed lines $b<\sigma,\tau<1$ has this problem;
unequal fixed lines do not remove it. On equal lines the displayed
power is the same as the allowance in (I119).

Thus improving only an absolute bound for the growing-height coupled
kernel cannot relax that fixed-line threshold, even after the already
paid smoothing. An improved bound needs information beyond this absolute
majorant, such as signed oscillation in $N^{i(t+y)}$ or cancellation
with other parts of the exact functional. No necessity of $b<5/8$ for
the signed functional is proved,
and no conclusion about estimates on $N$-dependent lines is asserted.
The original same-source joint upper bound, complete signed Robin
estimate and RH remain unresolved.


### One same-source product remains under a fixed half-plane below 3/4

Retain the original family (I59), the exact functional (I91), and all
its integer-grid observations. Suppose, as an additional premise, that
$1/2\le b<3/4$ and $\zeta$ has no zeros in $\Re s>b$. Fix
$b<\beta<3/4$. The Abel argument in (I118) uses $\beta<1$ for its
coefficient estimates; the restriction $\beta<5/8$ enters only at
the final vanishing of (I119). Apply that same argument and the residual
estimate after (I60), without a new Mertens or prime-error theorem:
$$
|B|\ll_\beta hN^\beta,\qquad
|\delta_{N,H}|\ll_\beta h^2N^{\beta-1},\qquad
\max_{N\le m\le2N}|LR_N(m)|\ll_\beta N^\beta.
$$

Write $S_N(m)=LR_N(m)$ and, for $N\le m<2N$, put
$$
u_{N,m}=\frac{m+\tfrac12-\tfrac32N}{m(m+1)},\qquad
p_{N,m}=\frac{m+\tfrac12}{m(m+1)},\qquad
\mathscr T_N(f)=\sum_{m=N}^{2N-1}u_{N,m}f(m).
$$
The identity
$A=B/N+\delta_{N,H}$ in the original coefficients gives exactly
$$
\begin{aligned}
L^2\mathscr J_N(R_N)
={}&\frac BN\mathscr T_N(S_N)
 +\delta_{N,H}\sum_{m=N}^{2N-1}p_{N,m}S_N(m)\\
&+(k_{N,2N}+e_{N,H})S_N(2N).
\end{aligned}
\tag{I136}
$$
This is the full response, including its actual mean and every Fourier
alias. The endpoint is retained in its combined original coefficient.
Since $\sum_{m=N}^{2N-1}p_{N,m}\ll1$, and the exact coefficients of (I91) and (I75) give
$|k_{N,2N}+e_{N,H}|\ll|\delta_{N,H}|+|B|/N^2$, the last two
terms divided by $L^2$ have total bound
$$
\begin{aligned}
\left|\mathscr J_N(R_N)-\frac B{NL^2}\mathscr T_N(S_N)\right|
 &\ll_\beta\frac{h^2N^{2\beta-1}+hN^{2\beta-2}}{L^2}\\
 &\ll_\beta
 \frac{N^{2\beta-3/2}e^{2\lambda\Omega}
       +N^{2\beta-9/4}e^{\lambda\Omega}}{L^2}=o(1).
\end{aligned}
\tag{I137}
$$
Both fixed negative powers absorb their exponential-log factors when $\beta<3/4$.

Consequently, under this additional fixed-half-plane premise, the
original all-integer target $\mathscr J_N(R_N)=o(1)$ is equivalent to
$B\mathscr T_N(S_N)=o(NL^2)$ for those same integers and the specified
bandwidth. The coefficients and response in this product cannot be
chosen or optimized independently. This pays the secondary and endpoint
contributions over a wider range than (I119), but proves no new bound for
the remaining signed product and does not improve its $5/8$ sufficient
threshold. It is an application of the owned analytic estimates, not a
new cancellation theorem or a Lean-certified statement. The complete
signed Robin estimate and RH remain unresolved.


## A zero-density contour for the actual band coefficient

Keep the original integers, bandwidth and endpoint conventions of
(I59), (I62), (I83) and (I136). Suppose additionally that
$1/2\le b<\beta<3/4$ and $\zeta$ has no zeros in $\Re s>b$.
This section reuses the local disk argument already transported to
ordinary $\zeta$ in (I60), Inoue's owned good heights, and the published
Ingham estimate recorded in
[the finite Robin source note](../Analytic/polak2026finiterobinca.md#reuse-the-published-ingham-estimate-at-its-tabulated-endpoint).
The additional result is their application to the actual coefficient
$B$ and the complete same-integer functional, not a new disk theorem,
zero-density estimate, zero-free half-plane or mathematical-priority
claim. No Lean certification is asserted.

Write
$$
Z(\sigma,U)=\#\{\rho:\zeta(\rho)=0,\ \Re\rho\ge\sigma,
                         \ 0<\Im\rho\le U\},\qquad
\mathfrak d(\sigma)=\frac{3(1-\sigma)}{2-\sigma},
$$
counting multiplicities. Chourasiya--Simonič,
[arXiv:2507.15184v2](https://arxiv.org/html/2507.15184v2),
Corollary 1 and Table 1, cover $1/2\le\sigma\le1$ by closed
subintervals and imply, uniformly on the fixed substrip used here,
$Z(\sigma,U)\ll U^{\mathfrak d(\sigma)}\log^3(2U)$.
Their stated lower height is $3\cdot10^{12}$; the bounded lower
heights are included by increasing the implicit constant. This is
the published input, reused without reproof.

For every fixed $\xi>0$, the band coefficient satisfies
$$
|B|\ll_{b,\beta,\xi}
 N^\xi\bigl(hN^{1/2}+h^{2-\mathfrak d(\beta)}N^\beta\bigr)+1.
\tag{I138}
$$
The proof keeps the complete high-frequency decay of the actual
weight and charges the rightward contour excursions to zeros.

### The local reciprocal input and the original smoothing

Use exactly $\eta=H^{-1}$, $a=1-h$ and the multiplier of (I83),
(I86). Those formulas already give
$B=\widetilde B+O(1)$ and
$\widetilde B=(2\pi i)^{-1}\int_{(2)}
N^sW_a(s)F_\eta(s)/\zeta(s)\,ds$.
On a fixed real strip,
$$
|W_a(\sigma+it)|\ll h\min\{h,(1+|t|)^{-1}\}.
$$
Indeed, with $\ell=\log(1/a)\asymp h$, its exact expression is
$\int_0^\ell x e^{-\sigma x}e^{-itx}\,dx$.
The direct integral bounds it by $O(h^2)$; one integration by parts
bounds it by $O(h/|t|)$ because both the terminal value and total
variation of $xe^{-\sigma x}$ are $O(h)$.

Take the already supplied good height
$T\in[N^4,N^4+N^{4/3}]$ and write $Y=\log T$.
Choose a fixed sufficiently small $d>0$ with
$b+3d<\beta$, $1/2+3d<\beta$ and $d<10^{-3}$.
The local form of the disk argument used in (I60) supplies
$|1/\zeta(\sigma+it)|\ll_{d,\epsilon}(3+|t|)^\epsilon$
whenever $\sigma\ge1/2+2d$, $\sigma\le\beta$ and the rectangle
$\Re z>\sigma-d$, $|\Im z-t|\le Y$ is zero free, for $Y>2$.
Here is the parameter correspondence needed for that reuse.
In its cited `lem:logarithmic-control` disk proof, put
$a_0=\sigma-d$ and $e_0=d/8$.
The outer radius $2-a_0-2e_0=2-\sigma+3d/4$ about $2+it$
lies inside this rectangle; the control radius
$2-a_0-6e_0=2-\sigma+d/4$ contains the point $\sigma+it$.
Use the ordinary regularized function
$(s-1)\zeta(s)/(s+1)$, its classical polynomial strip growth and
bounded Euler logarithm, exactly as in (I60).
The printed Hecke/Dedekind statement is not being quoted as literally
an ordinary-$\zeta$ theorem. Only its already documented ordinary disk
argument is used, and that argument needs nonvanishing on the disk,
not a global zero-free half-plane with boundary $\sigma-d$.

### Count every excursion, including its horizontal joins

Put $g_d(x)=1/2+d\lceil(x-1/2)/d\rceil$. At
$4Y\le|t|\le T$, define
$$
c_T(t)=\max\left\{\frac12+2d,\quad
 g_d(\Re\rho)+2d:
 \Re\rho>\frac12,\ |\Im\rho-t|\le2Y\right\}.
\tag{I139}
$$
Ignore an empty zero set in the maximum. The fixed-half-plane
hypothesis implies $1/2+2d\le c_T(t)\le b+3d<\beta$.
Use the vertical pieces at $\Re s=c_T(t)$, joining their jumps
horizontally. For $|t|\le4Y$ use $\Re s=\beta$, with horizontal
connectors at $t=\pm4Y$; call the resulting contour $\Gamma$.
Every nontrivial zero inside the truncated rectangle lies strictly
to its left, so the shift from $\Re s=2$ crosses no poles of
$1/\zeta$. Its zero at one causes no residue.

The required local rectangle is zero free at every high-height
vertical piece. At a jump, zeros within distance $Y$ of that height
are present on both sides of the jump; the entering or leaving zeros
are at distance $2Y$. Thus the rectangle is zero free even at the
smaller real endpoint, and hence along the entire horizontal join.
The same reasoning applies to each connector from $c_T(\pm4Y)$
to $\beta$. Their reciprocal bound is local; these connectors need
not lie in $\Re s>b$. The low-height $\beta$ line instead uses the
global reciprocal bound already established in (I60).
Consequently $|1/\zeta(s)|\le N^{o_d(1)}$ on $\Gamma$.
The low-height line and its two connectors contribute
$\ll h^2N^\beta N^{o_d(1)}$.

Let $\Gamma^{\rm hi}$ contain only the high vertical pieces and their
jump joins, excluding the low-height line and both transition
connectors just paid. In a dyadic block
$U\le|t|\le2U$, $U\ge4Y$, separate the
baseline pieces, whose real parts are at most $1/2+4d$.
Their length is $O_d(U\log T)$, including horizontal joins:
the vertical length is $O(U)$ and there are $O(U\log U)$ possible
zero-window endpoints. For any remaining real strip
$\sigma\le\Re s<\sigma+d$, its total contour length satisfies
$$
\operatorname{length}(\Gamma^{\rm hi}_{\sigma,U})
 \ll_d Y Z(\sigma-3d,4U).
\tag{I140}
$$
For vertical pieces, a zero forcing the maximum into that strip
has $\Re\rho\ge\sigma-3d$, and each such zero influences at most
$4Y$ of vertical length. Each horizontal jump occurs at an endpoint
of a zero's influence interval. A zero responsible for raising or
lowering the maximum across the strip also has
$\Re\rho\ge\sigma-3d$; each zero supplies at most two such
endpoints and at most length $d$ in the strip per endpoint.
Positive and negative zeros are handled together by conjugation.
Since $U\ge4Y$, all responsible heights have absolute value below
$4U$. These charges prove (I140) for the complete contour pieces.

Use $|F_\eta|\ll1$ on this strip. The density bound, (I140), and
$\mathfrak d(\sigma-3d)=\mathfrak d(\sigma)+O(d)$ give the
following block bound, for a finite real mesh $\mathcal G_d$:
$$
\begin{aligned}
\int_{\Gamma^{\rm hi}\cap\{U\le|\Im s|\le2U\}}
 \left|\frac{N^sW_a(s)F_\eta(s)}{\zeta(s)}\right|\,|ds|
\ll_d{}&N^{O(d)+o_d(1)}h\min\{h,U^{-1}\}\\
 &\cdot\left(N^{1/2}U+
       \sum_{\sigma\in\mathcal G_d}
                   N^\sigma U^{\mathfrak d(\sigma)}\right).
\end{aligned}
\tag{I141}
$$
Here the nonbaseline mesh has $\sigma>1/2+3d$ and
$\sigma\le\beta$; the real-width cost $N^d$ and logarithms
are included in the displayed loss. With $U\le T\asymp N^4$,
the density-exponent displacement also costs only $N^{O(d)}$.

For the baseline, dyadic summation gives
$\sum_{U\le T}h\min(h,U^{-1})U\ll h\log T$.
For each fixed $\sigma>1/2$, $0<\mathfrak d(\sigma)<1$, and
splitting at $U=h^{-1}$ gives
$\sum_{U\le T}h\min(h,U^{-1})U^{\mathfrak d(\sigma)}
\ll_\sigma h^{2-\mathfrak d(\sigma)}$.
The original bandwidth has
$\log(1/h)/\log N=1/4+o(1)$. Moreover,
$$
\frac{d}{d\sigma}\log\bigl(N^\sigma h^{-\mathfrak d(\sigma)}\bigr)
 =\log N-\frac{3\log(1/h)}{(2-\sigma)^2}>0
 \qquad(1/2\le\sigma\le\beta<3/4)
$$
for all sufficiently large $N$.
Thus every nonbaseline term is bounded by the one at $\beta$.
The low-height allowance $h^2N^\beta N^{o_d(1)}$ is absorbed too.

The top and bottom edges use the owned good-height reciprocal bound
and the original multiplier's decay. For fixed $K=20$ they cost
$\ll_\epsilon N^2(h/T)T^\epsilon(T/H)^{-20}$.
The tails on the original line cost
$\ll N^2h(T/H)^{-20}$, since $1/\zeta(2+it)$ is bounded.
Both are $O(N^{-10})$ at the specified $T$ and $H$.
Choose $d$ small enough in terms of $b,\beta,\xi$, then take $N$
large enough to absorb all remaining logarithms and $N^{o_d(1)}$
into $N^\xi$. Finally (I83) restores the original integer-band
coefficient at cost $O(1)$. This proves (I138) for every sufficiently
large original integer, without an average over cutoffs.

### Apply the coefficient gain to the complete original functional

The existing (I136)--(I137) decomposition and
$|\mathscr T_N(S_N)|\ll_\beta N^\beta$ give
$$
\begin{aligned}
|\mathscr J_N(R_N)|\ll_{b,\beta,\xi}{}&
 \frac{N^\xi}{L^2}
 \left(hN^{\beta-1/2}
       +h^{2-\mathfrak d(\beta)}N^{2\beta-1}\right)\\
 &+\frac{h^2N^{2\beta-1}+hN^{2\beta-2}+N^{\beta-1}}{L^2}.
\end{aligned}
\tag{I142}
$$
The final $N^{\beta-1}/L^2$ is the cost of restoring the unsmoothed
$B$, acting on the actual response. The secondary coefficient and
the combined original endpoint retain their paid (I137) allowance.
The response, its mean and every alias remain unchanged.

Compared with (I119), the controlling term has gained
$h^{1-\mathfrak d(\beta)}=N^{-\gamma(\beta)+o(1)}$, where
$\gamma(\beta)=(2\beta-1)/(4(2-\beta))$.
The strict condition
$\gamma(\beta)>2\beta-5/4$ is equivalent, in the present range, to
$$
\beta<\beta_{\rm c}:=\frac{19-\sqrt{73}}{16}
 =0.653499765\ldots.
\tag{I143}
$$
Thus the additional zero-free-half-plane premise with $b<\beta_{\rm c}$
is sufficient for the complete same-integer target
$\mathscr J_N(R_N)=o(1)$, improving this application's previous
$5/8$ sufficient boundary. A convenient fixed value is $\beta=13/20$:
$\mathfrak d(\beta)=7/9$, and the controlling scale is
$$
\frac{h^{11/9}N^{3/10}}{L^2}
 \asymp\frac{N^{-1/180}e^{11\lambda\Omega/9}}{L^2}.
\tag{I144}
$$
Since $\Omega=o(\log N)$, under $b<13/20$ this gives
$|\mathscr J_N(R_N)|\ll_{b,\xi}N^{-1/180+\xi}$ for every fixed
$\xi>0$. The other powers at this checkpoint are
$-1/10$, $-1/5$, $-19/20$ and $-7/20$, all strictly smaller.

The gain comes from the length of the rightward excursions on a
variable contour, not from a smaller fixed-line double absolute
majorant. It therefore does not contradict (I130)--(I135).
It does not provide the zero-free-half-plane premise required here,
a new unconditional Robin bound, or a proof of RH. For larger $b$
the complete original signed estimate remains unresolved.
