# Recursive relational observation: completeness of native product pressure

## 1. Stationary sources, complete exports and late prediction

**Definition 1.1 (the original source and observation).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad h(\alpha)=h(\beta)=0,\qquad
h(\langle u,v\rangle)=1+\max\{h(u),h(v)\}.
$$

Pairing is free and ordered. Every finite word over $L,R$, including
$\varepsilon$, is a legal original-root literal. Write $r_t(a)$ for
its reply in $\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$;
traversal past a leaf gives absent. The homomorphic substitution is

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle u,v\rangle=\langle\rho u,\rho v\rangle.
$$

For each public integer $D\ge1$ put

$$
\mathcal F_D=\{\langle\alpha,v\rangle:h(v)\le D\},\qquad
W_D=\{q:|q|\le D-1\},\qquad
\mathcal P_D=\{Rq:q\in W_D\}.
\tag{NPC.1}
$$

One actual initial source remains stationary throughout preparation and
late acquisition. The iterates $\rho^kt$ specify prediction targets.
There is no subtree, equality, identity, age, copying, reset, navigation
or advice port. These are the carriers of [NDR, Definition 1.1][NDR]
and [FMR, Definition 1.2][FMR].

**Assumption 1.2 (the complete paid-export task).** One deterministic
effective preparation starts source-blind from public $D$ and common
source-independent tables, does not receive the later request, and
terminates on every $t\in\mathcal F_D$. Every source distinction is
acquired by charged literal Reads. It exports $E(t)$ before the request.
Its complete attained alphabet includes every accessible surviving
source distinction: selectors, control, operands, buffers, lengths,
allocation, handles, counters and accessible timing. Every other
accessible field is a function of $E(t)$ and public data. A separately
paid handoff/access service isolates all other preparation dependence
and supplies lawful entry. Isolation, continuity and authentication are
service premises.

Only after export, a public source-independent $p\in\mathcal P_D$ is
supplied. A common deterministic effective reader uses $E(t),D,p$ and
common tables. It makes zero Reads or one fresh Read of the same $t$
at any finite original-root literal chosen before the reply and before
any supplied count. It then produces $Z$, for which

$$
\operatorname{Dec}(Z,D,p,k)=r_{\rho^kt}(p)
\quad\text{for every }t\in\mathcal F_D,\ p\in\mathcal P_D,
\text{ and authentic subsequently supplied }k\ge0,
\tag{NPC.2}
$$

with no further Reads. Define $M_1(D)=\min|E[\mathcal F_D]|$ over
these jointly correct preparations and readers. Only the complete
attained alphabet is minimized. Preparation Reads, work/control,
installed tables, temporary storage, post-request workspace, final
predictor, submitted literal lengths and letters, count representation,
handoff, isolation, authentication, entry and physical time are separate
resource coordinates. This is [FMR, Assumption 1.3][FMR], with its full
variable-shape source and all-word reader class.

**Convention 1.3 (exact native notation).** In
[GenealogicalFiberTransport][D5G], `Source` is `FreeMagma Bool`, with
true for $\alpha$ and false for $\beta$, and `substitution` is $\rho$.
In [ActualTreeReadoutAcquisition][D5A], `Address` is `List Bool`, false
means $L$, true means $R$, and `Reply` and `readout` are the four-valued
maps of Definition 1.1. In [ActualLeafHistoryRigidity][D5L],
`subtree a u = some t` means that $a$ is an actually present original
occurrence with subtree $t$. In [NativeDepthPatterns][D5N],
`original_present_transport` has precisely that presence premise and
concludes

$$
(\rho^ku)|_a=\rho^kt\qquad(k\ge0).
\tag{NPC.3}
$$

Its `original_prefix_locality` assumes equality of all original replies
through the length of the requested word and gives equality of that
word's replies at every count. Its `depthEquiv` ranges over a dependent
sum of an actual pattern and its reached frontier, rather than a freely
supplied shape tag or a subtree input.

## 2. The unrestricted finite native relation family

**Convention 2.1 (the credited predictive factor).** Use the exact factor
of [AAR, Definition 12.2, Theorem 12.3 and Proposition 13.3][AAR]. Put
$s(r)=\#L(r)+2\#R(r)$ and $e(\alpha)=0,e(\beta)=1$. At an original
branch endpoint $\Gamma_q(u)=(0,0)$. Otherwise let the first original
leaf along $q$ have label $\ell$ at $a$, and write $q=ar$. Then

$$
\Gamma_q(u)=
\begin{cases}
(2-e(\ell),1-e(\ell)),&r=\varepsilon,\\
(s(r)+2-e(\ell),\mathbf1_{r\text{ ends in }R}),&r\ne\varepsilon.
\end{cases}
\tag{NPC.4}
$$

On its attained image, $\Gamma_q(u)=(b,c)$ has decoder

$$
\operatorname{Pred}((b,c),k)=
\begin{cases}
\mathsf{branch},&k\ge b,\\
\beta,&b\ge1,\ k=b-1,\\
\alpha,&c=1,\ k=b-2,\\
\mathsf{absent},&\text{otherwise}.
\end{cases}
\tag{NPC.5}
$$

Here $c=1$ implies $b\ge2$. This is $r_{\rho^ku}(q)$ for every
$k\ge0$. The full trajectory recovers $b$ as the first branch count
and $c$ as the indicator of an alpha stage. Equality of $\Gamma$ is
therefore exactly equality of trajectories, including initially absent
targets, and need not be equality of blocking-leaf descriptors. In
the original wrapper $\Gamma_{Rq}(\langle\alpha,v\rangle)=\Gamma_q(v)$
and $b\le2D$ for permitted requests. The last-edge guard in AAR's
atomic law makes a nonempty $L$-ending suffix have no alpha stage.

**Definition 2.2 (all joint competitors and complete templates).** Fix
$d\ge1$ and put

$$
C_0=\langle\alpha,\alpha\rangle,\qquad
S_1=\{\alpha,\beta,C_0\},\qquad
S_{d+1}=\{\alpha,\beta\}\sqcup
\{\langle x,y\rangle:x,y\in S_d\}.
\tag{NPC.6}
$$

Write $S=S_d$, $s=|S|$, $Q=W_d$, $g_q(x)=\Gamma_q(x)$ and
$r_a(x)=r_x(a)$ for $a,q\in W_d$. Let $\mathcal B_n$ contain every
nonempty $B\subseteq S^n$ such that, for every $(i,q)$, either
$g_q(x_i)$ is constant on $B$, or there are $j,a$ and a reply decoder
$\delta$ with

$$
g_q(x_i)=\delta(r_a(x_j))\qquad(x\in B).
\tag{NPC.7}
$$

The choices depend on $B,i,q$; self donors, off-target queries,
arbitrary correlations and all cycles are allowed. Set
$\mathcal B_0=\{\{()\}\}$.

A complete template $\Theta$ chooses for each $(i,q)$ a constant
equation $g_q(x_i)=z$, or an equation (NPC.7), with any donor $j$,
any $a\in W_d$, and any total decoder from the four replies to
$g_q(S)$. Let $C_\Theta$ be its simultaneous solution set. There are
finitely many such templates at each $n$, with no bound on $n$ or on
donor topology. [NDR, Theorem 2.2][NDR] identifies the maximum of every
nonnegative mass over $\mathcal B_n$ with its maximum over nonempty
$C_\Theta$; every $B\in\mathcal B_n$ is contained in such a solution
set on the same coordinates. No projection or independent encoding
is part of this saturation.

**Convention 2.3 (canonicalization, covers and rates).** On $S_d$, every
length-$d$ word returns alpha exactly when its length-$(d-1)$ parent
is branch, and absent otherwise; longer words are absent. [FMR, Lemma
2.2 and Lemma 6.2][FMR] therefore reduce every finite block experiment
to one boundary reply in that same block or to a constant. Its
Theorems 2.3–2.5 identify the full-task optimum with the paid canonical
cover optimum, preserving the complete attained alphabet.

Let $K_d(n)$ be the least number of members of $\mathcal B_n$ covering
$S^n$, and $K_d(0)=1$. [FMR, Theorems 3.3 and 6.3–6.4][FMR] give

$$
\begin{aligned}
\sigma_d&=\lim_{n\to\infty}\frac{\log_2K_d(n)}n
          =\inf_{n\ge1}\frac{\log_2K_d(n)}n,\\
\lambda&=\lim_{D\to\infty}2^{-D}\log_2M_1(D)
         =\sup_{d\ge1}2^{-d}\sigma_d,\\
0&\le\lambda-2^{-d}\sigma_d\le2^{-d}\phi,\qquad 0\le\phi\le1,
\end{aligned}
\tag{NPC.8}
$$

where $U_0=1$, $U_{h+1}=1+U_h^2$ and
$\phi=\lim_h2^{-h}\log_2U_h$. Also
$K_d(2^h)\le M_1(d+h)$ and
$M_1(D+1)\le M_1(D)^2+1$; the shifted endpoints
$2^{-D}\log_2(M_1(D)+1)$ decrease to $\lambda$.

All logarithms below are base two, with $0\log_2 0=0$. For a probability
$p$ on $S$, write $H(p)=-\sum_xp_x\log_2p_x$ and
$\operatorname{TV}(p,q)=\frac12\sum_x|p_x-q_x|$. Write $h_2$ for
binary entropy, $\omega_s(t)=h_2(t)+t\log_2s$, and use the monotone
majorant $\overline\omega_s(t)=h_2(\min\{t,1/2\})+t\log_2s$
when an upper bound on $t$ is substituted.

## 3. Fixed-value sections and native conditional shortening

**Lemma 3.1 (the native closure premises).** The families $\mathcal B_n$
are closed under nonempty restriction, coordinate permutations, products
on disjoint coordinate sets and adjoining fixed coordinates. If
$B\in\mathcal B_n$, $I\subseteq[n]$ and $z\in S^I$ is fixed, then
the section

$$
B[I=z]=\{x_{I^c}:x\in B,\ x_I=z\}
\tag{NPC.9}
$$

belongs to $\mathcal B_{n-|I|}$ whenever it is nonempty.

Proof. Choose one witness equation for each target on $B$. On a
nonempty restriction the same equations hold. A permutation merely
renames their coordinate indices. In a product, each coordinate uses
the witness in its own factor. A fixed coordinate has constant targets.

For a section, consider a target at a remaining coordinate. If its donor
is also remaining, its original equation still holds and is an allowed
one-donor equation. If its donor is $j\in I$, its right-hand side is
the fixed value $\delta(r_a(z_j))$, giving an allowed constant target.
An originally constant target remains constant. These statements exhaust
every target, including self donors and cyclic dependencies. When no
coordinates remain the nonempty section is $\{()\}$. $\square$

The fixed values in (NPC.9) are mathematical conditions on rows. They
are not supplied to an original reader, exported without charge, or
queried at an extra port. In particular the lemma asserts no deletion
or replacement of an actual stationary source.

**Convention 3.2 (the projection distinction).** [NCM, Proposition 6.1][NCM]
gives a five-row $B_*\subseteq S_3^2$ which is jointly admissible even
though both one-coordinate projections equal a locally inadmissible
five-state set $P$. Its paired witnesses serve every native target and
all authentic counts; Proposition 6.2 gives its paid full-family
realization. Thus arbitrary projection cannot replace (NPC.9). NDR's
donor-closed projection lemma has its additional donor-closure premise.
No such premise is needed for fixed-value sections.

## 4. Native types and their continuous concave profile

**Definition 4.1 (type maxima).** For $\nu\in\mathbb N^S$ with
$\sum_x\nu_x=n\ge1$, let $T_\nu$ be the words in $S^n$ with symbol
counts $\nu$. Define

$$
a_n(\nu)=\max_{B\in\mathcal B_n}|B\cap T_\nu|,\qquad
f_n(\nu/n)=\frac1n\log_2a_n(\nu).
\tag{NPC.10}
$$

These are exactly [NDR, Definition 3.1][NDR]'s template type maxima.
Singletons give $a_n(\nu)\ge1$; finiteness attains every maximum.
By restriction, an attaining type subset is itself admissible.

**Theorem 4.2 (uniform transfer between native types).** For two types
$\nu,\nu'$ of length $n$, put
$m=\frac12\sum_x|\nu_x-\nu'_x|$. Then

$$
\left|\log_2a_n(\nu)-\log_2a_n(\nu')\right|
\le\log_2\binom nm+m\log_2s
\le n\omega_s(m/n).
\tag{NPC.11}
$$

Proof. Put $c_x=\min\{\nu_x,\nu'_x\}$ and choose admissible
$A\subseteq T_\nu$ of size $a_n(\nu)$. In each row select $m$ positions
whose removed symbol counts are $\nu-c$, using any fixed rule.
Record their position set $I$ and their ordered value word $z$.
There are at most $\binom nm s^m$ records. Some record is selected
by at least $|A|/(\binom nm s^m)$ rows. Its full section $A[I=z]$
has at least that size and is admissible by Lemma 3.1. Every row has
remaining counts $c$; deletion is injective because all deleted values
were fixed. Append a fixed word with counts $\nu'-c$. The resulting
length-$n$ relation is admissible, has type $\nu'$, and has the same
size. This gives one direction of (NPC.11); exchange the types for
the other direction.

For $0<m<n$, the binomial probability
$\binom nm(m/n)^m(1-m/n)^{n-m}$ is at most one. Taking logarithms
gives the last inequality. At $m=0,n$ it holds directly. The loss is
uniform over all witness systems and all joint correlations. $\square$

**Theorem 4.3 (continuous native constant-composition capacity).** There
is a unique continuous function $\alpha_d$ on the probability simplex
$\Delta(S)$ such that, for every rational $p$ and every integer $r\ge1$
with $rp$ integral,

$$
\alpha_d(p)=\lim_{k\to\infty}f_{kr}(p)
            =\sup_{k\ge1}f_{kr}(p).
\tag{NPC.12}
$$

It is concave, satisfies $0\le\alpha_d(p)\le H(p)$ and

$$
|\alpha_d(p)-\alpha_d(q)|
\le\omega_s(\operatorname{TV}(p,q)).
\tag{NPC.13}
$$

Moreover

$$
u_n:=\max_{\nu:\,\sum_x\nu_x=n}
\left|f_n(\nu/n)-\alpha_d(\nu/n)\right|\longrightarrow0.
\tag{NPC.14}
$$

Proof. Lemma 3.1 gives
$a_{n+m}(\nu+\eta)\ge a_n(\nu)a_m(\eta)$.
For fixed rational $p$, the logarithms along lengths $kr$ are
nonnegative superadditive and bounded by $krH(p)$: each word in
$T_{krp}$ has iid $p$-probability $2^{-krH(p)}$, so the type size is
at most $2^{krH(p)}$. For a fixed integer $j$, write $k=\ell j+t$,
$0\le t<j$. Superadditivity and nonnegativity show that the liminf
of the normalized logarithms is at least the value at $jr$.
The limsup is at most their supremum. Taking the supremum over $j$
proves (NPC.12). Two permitted denominators have a common-multiple
subsequence, proving denominator independence.

For rational $p,q$, apply Theorem 4.2 at common-multiple lengths and
take limits. This gives (NPC.13). Since its right-hand side tends to
zero with total variation, it gives a unique continuous extension from
the dense rational simplex. Continuity of entropy preserves
$0\le\alpha_d\le H$ and (NPC.13) on the boundary as well.

For rational $p,q$ and rational $0<\theta<1$, choose lengths in the
ratio $\theta:(1-\theta)$ with integral constituent types. Products of
their attaining type sets have type $\theta p+(1-\theta)q$.
Letting both lengths tend through common multiples proves concavity
for these parameters; continuity supplies all real parameters.

Repeating any finite attaining type set shows
$f_n(\nu/n)\le\alpha_d(\nu/n)$. For the reverse asymptotic inequality,
take any sequence of lengths tending to infinity and types $\nu_n$
with $\nu_n/n\to p$. Fix a rational $r$ close to $p$ and $\epsilon>0$.
By (NPC.12) there is a fixed length $L$, with $Lr$ integral, and an
admissible type set with logarithmic size at least
$L(\alpha_d(r)-\epsilon)$. At length $n$, concatenate
$\lfloor n/L\rfloor$ copies and fill the fewer than $L$ remaining
coordinates by fixed symbols. Its type $\widetilde\nu_n/n$ tends to
$r$ and its logarithmic size per coordinate has liminf at least
$\alpha_d(r)-\epsilon$. Transfer that type to $\nu_n$ by (NPC.11).
It follows that

$$
\liminf_n f_n(\nu_n/n)
\ge\alpha_d(r)-\epsilon-\omega_s(\operatorname{TV}(r,p)).
$$

Let rational $r\to p$ and $\epsilon\downarrow0$. The opposite bound
already proved and continuity give $f_n(\nu_n/n)\to\alpha_d(p)$.
If (NPC.14) failed, compactness would give a subsequence of offending
empirical distributions converging to some $p$, contradicting this
sequential conclusion. The proof supplies convergence without a
specified computable rate for $u_n$. $\square$

The type-limit, concatenation and continuity methods have primary
analogues in [Vrana, Propositions 3.3–3.4][V]. There the function is a
graph spectral point, normalized, cohomomorphism-monotone, additive
under disjoint union and multiplicative under strong product. Those
graph hypotheses are not premises here: Lemma 3.1 and Theorem 4.2
provide the actual native section and transfer relations. No concavity
of $H-\alpha_d$ is assumed or needed.

## 5. Exact pressure and covering variational formulas

**Definition 5.1 (all-length product mass).** For $w:S\to[0,\infty)$
put

$$
\begin{aligned}
\Omega_w(B)&=\sum_{x\in B}\prod_{i=1}^nw(x_i),\\
A_n(w)&=\max_{B\in\mathcal B_n}\Omega_w(B),\qquad A_0(w)=1,\\
\beta_N(w)&=\max_{1\le n\le N}A_n(w)^{1/n},\qquad
\beta(w)=\sup_{n\ge1}A_n(w)^{1/n}.
\end{aligned}
\tag{NPC.15}
$$

For $w>0$, $P_d(w)=\log_2\beta(w)$ is precisely [NDR, Proposition
3.3][NDR]'s unrestricted pressure. Singletons and the full ambient
mass give

$$
\max_xw(x)\le\beta_N(w)\le\beta(w)\le\sum_xw(x).
\tag{NPC.16}
$$

**Theorem 5.2 (the native variational identities).** For fixed $d\ge1$,

$$
\sigma_d=\max_{p\in\Delta(S)}\{H(p)-\alpha_d(p)\},
\tag{NPC.17}
$$

and, for every strictly positive $w$,

$$
P_d(w)=\max_{p\in\Delta(S)}
\left\{\alpha_d(p)+\sum_xp_x\log_2w(x)\right\}.
\tag{NPC.18}
$$

Proof. For $p=\nu/n$, the standard finite type-size bounds are

$$
(n+1)^{-s}2^{nH(p)}\le|T_\nu|\le2^{nH(p)}.
\tag{NPC.19}
$$

Here is the needed elementary lower estimate. Under iid $p$, all words
of type $\nu$ have probability $2^{-nH(p)}$. That type has maximal
type probability: for any type $\eta$ with the same support condition,
its probability divided by that of $\nu$ is

$$
\prod_{x:\nu_x>0}\nu_x^{\eta_x-\nu_x}\frac{\nu_x!}{\eta_x!}.
$$

Every factor is at most one. For $\eta_x>\nu_x$, write its denominator
as a product of integers greater than $\nu_x$; for $\eta_x<\nu_x$,
write its numerator as a product of integers at most $\nu_x$.
If $\nu_x=0<\eta_x$, the other type has probability zero; common
zeros contribute one. At most $(n+1)^s$ types share total probability
one, so the modal type has probability at least $(n+1)^{-s}$.
This proves (NPC.19).

Put $R_n=\max_\nu|T_\nu|/a_n(\nu)$. [NDR, Theorem 3.2][NDR]
supplies, with $H_m=\sum_{j=1}^m1/j$,

$$
R_n\le K_d(n)\le H_{s^n}(n+1)^sR_n,
\qquad H_{s^n}\le1+n\ln s.
$$

The normalized logarithmic error tends to zero. Combine this with
(NPC.19), (NPC.14) and density of length-$n$ type grids in the
simplex to obtain (NPC.17), using the supplied limit for $K_d(n)$.
The maximum exists by continuity and compactness.

At fixed $n$, an iid word weight depends only on its type. Consequently

$$
\max_\nu a_n(\nu)\prod_xw(x)^{\nu_x}
\le A_n(w)\le
(n+1)^s\max_\nu a_n(\nu)\prod_xw(x)^{\nu_x}.
\tag{NPC.20}
$$

The lower bound uses an attaining admissible type subset. For the
upper bound, divide any admissible set into its type intersections.
Take logarithms, divide by $n$, and use (NPC.14), continuity and
density of the type grids. The limit is the right-hand side of
(NPC.18). Products in Lemma 3.1 also give
$A_{n+m}(w)\ge A_n(w)A_m(w)$, while
$A_n(w)\le(\sum_xw(x))^n$. The same superadditive quotient-and-remainder
argument as in Theorem 4.3, with a finite lower remainder bound, shows
that $n^{-1}\log_2A_n(w)$ tends to its supremum. Thus this limit is
$P_d(w)$ as defined in (NPC.15), proving (NPC.18). $\square$

The graph capacity/complementary-entropy relation discussed in
[Charpenay–Le Treust–Roumy, Theorem 7][CLR] is a related mature
type-method identity for specified graph products. Here (NPC.17) uses
NDR's native type-cover comparison. FMR §7's higher-arity obstruction
does not permit substitution of a pair-confusability graph.

**Theorem 5.3 (unrestricted product-pressure completeness).** At every
fixed native depth $d\ge1$,

$$
\boxed{\displaystyle
\sigma_d=\sup_{w>0}
\left\{\log_2\sum_xw(x)-P_d(w)\right\}.}
\tag{NPC.21}
$$

The supremum is unchanged when $w$ ranges over strictly positive
rational vectors, or over strictly positive rational probability
vectors. Every pressure in this formula retains all $n\ge1$ and all
$B\in\mathcal B_n$.

Proof. Write $\alpha=\alpha_d$,
$P(\theta)=\max_p\{\alpha(p)+p\cdot\theta\}$ and
$L(\theta)=\log_2\sum_x2^{\theta_x}$. Theorem 5.2 identifies
$P(\theta)=P_d(2^\theta)$. The finite Gibbs variational identity is
$L(\theta)=\max_p\{H(p)+p\cdot\theta\}$: subtracting the expression
in braces from $L$ is the nonnegative relative entropy of $p$ to the
probability proportional to $2^\theta$. These are standard finite
entropy and convex-duality intermediates.

For completeness, the precise concave duality needed is

$$
\alpha(p)=\inf_{\theta\in\mathbb R^S}
\{P(\theta)-p\cdot\theta\}\qquad(p\in\Delta(S)).
\tag{NPC.22}
$$

One inequality follows immediately from the definition of $P$.
For the other, the hypograph
$\{(q,t):q\in\Delta(S),\ t\le\alpha(q)\}$ is closed and convex,
by Theorem 4.3. Strictly separate it from
$(p,\alpha(p)+\epsilon)$ in the finite-dimensional affine space of
the simplex times $\mathbb R$, using the standard separation theorem
of [Rockafellar, §§11–12][R]. In an inequality with the hypograph on
the lower side, the coefficient of $t$ is nonnegative because the
hypograph is unbounded downward. It cannot be zero, since the
hypograph also contains $(p,\alpha(p))$ with the same base coordinate
as the separated point. Normalize that coefficient to one. For some
$\theta$ the separation then says
$P(\theta)-p\cdot\theta<\alpha(p)+\epsilon$.
Let $\epsilon\downarrow0$, proving (NPC.22), including boundary $p$.

It follows that

$$
\begin{aligned}
\sigma_d
&=\sup_p\sup_\theta
  \{H(p)+p\cdot\theta-P(\theta)\}\\
&=\sup_\theta\{L(\theta)-P(\theta)\}.
\end{aligned}
$$

Only two suprema are exchanged; there is no minimax assumption.
This proves (NPC.21). It uses no graph semiring, Shannon-cone
achievability, restricted donor topology or bounded-width premise.

If $\max_x|\log_2w(x)-\log_2v(x)|\le\delta$, every length-$n$
word mass changes by a factor between $2^{-n\delta}$ and
$2^{n\delta}$. Taking maxima and the all-length supremum gives
$|P_d(w)-P_d(v)|\le\delta$. The log of the total weight has the
same bound. Positive rational vectors are dense in this logarithmic
metric, so their endpoint error is at most $2\delta$. Finally
$P_d(cw)=\log_2c+P_d(w)$, and normalizing a rational positive vector
preserves rationality. This proves both restrictions. $\square$

## 6. Stable weights, an attained global minimizer and rational meshes

**Theorem 6.1 (all-length native weight stability).** For all nonnegative
$w,v$ and $N\ge1$,

$$
\beta_N(w+v)\le\beta_N(w)+\sum_xv(x),\qquad
\beta(w+v)\le\beta(w)+\sum_xv(x).
\tag{NPC.23}
$$

In particular $|\beta(w)-\beta(v)|\le\|w-v\|_1$. On the probability
simplex the sharper estimate is

$$
|\beta(\mu)-\beta(\nu)|\le\operatorname{TV}(\mu,\nu).
\tag{NPC.24}
$$

The same bounds hold for $\beta_N$.

Proof. For $B\in\mathcal B_n$, expand
$\prod_i(w(x_i)+v(x_i))$ by the positions $I$ using $v$. Sum first
over their fixed values $z$. Each nonempty complementary section is
admissible by Lemma 3.1, so its $w$-mass is at most $A_{n-|I|}(w)$.
Summing the $v$ factors over all $z$ gives $(\sum_xv(x))^{|I|}$.
Therefore

$$
\Omega_{w+v}(B)
\le\sum_{m=0}^n\binom nm A_{n-m}(w)
                  \left(\sum_xv(x)\right)^m.
\tag{NPC.25}
$$

For $n\le N$, use $A_{n-m}(w)\le\beta_N(w)^{n-m}$; when
$n=m$ this means $A_0=1$, with $0^0=1$ in that term. The binomial
theorem bounds (NPC.25) by
$(\beta_N(w)+\sum_xv(x))^n$. Maximize over $B,n\le N$.
Using $\beta$ instead gives the same result at every $n$, hence
(NPC.23).

Monotonicity and $w\le v+(w-v)_+$ imply
$\beta(w)\le\beta(v)+\sum_x(w(x)-v(x))_+$, and conversely
with $w,v$ exchanged. This gives the $\ell^1$ estimate. For two
probabilities both one-sided sums equal their total variation, giving
(NPC.24). The argument applies unchanged to $\beta_N$. $\square$

**Theorem 6.2 (one attained distribution for all lengths and competitors).**
Let $b_d=2^{-\sigma_d}$. Then

$$
\boxed{\displaystyle b_d=\min_{\mu\in\Delta(S)}\beta(\mu).}
\tag{NPC.26}
$$

There is a probability $\mu_d$ such that, simultaneously,

$$
\forall n\ge1\ \forall B\in\mathcal B_n,\qquad
\sum_{x\in B}\prod_i\mu_d(x_i)\le b_d^n.
\tag{NPC.27}
$$

Its coordinates may vanish. Moreover $1/s\le b_d\le1$.

Proof. Homogeneity gives
$\beta(cw)=c\beta(w)$. Normalize (NPC.21) to obtain
$\sigma_d=-\log_2\inf_{\mu>0,\,\sum\mu=1}\beta(\mu)$.
Theorem 6.1 makes $\beta$ continuous on the closed simplex.
Its strictly positive part is dense, and compactness attains the
same infimum on the closed simplex. By (NPC.16), every probability
satisfies $\beta(\mu)\ge\max_x\mu(x)\ge1/s$, so taking logarithms
is legitimate. This proves (NPC.26). By definition of $\beta$,
$A_n(\mu_d)^{1/n}\le b_d$ for every $n$, which proves (NPC.27).
Thus a single distribution works on every joint length and every
native relation; it is not a separate sequence of finite-length
dual optimizers. $\square$

**Definition 6.3 (rational global caps).** A rational pair $(\mu,C)$,
with $\mu\in\Delta(S)\cap\mathbb Q^S$ and $C>0$, is valid if

$$
\forall n\ge1\ \forall\text{ complete templates }\Theta
\text{ on }n\text{ coordinates},\qquad
\sum_{x\in C_\Theta}\prod_i\mu(x_i)\le C^n.
\tag{NPC.28}
$$

Empty solution sets have mass zero. NDR's saturation makes (NPC.28)
equivalent to the same inequality for every $B\in\mathcal B_n$,
and to $\beta(\mu)\le C$. The pair's block lower endpoint is
$-\log_2C$; its original-rate endpoint is $-2^{-d}\log_2C$.

**Theorem 6.4 (explicit finite rational parameter approximation).**
Fix $d$, $s=|S_d|$, and an integer $m\ge1$. The rational simplex grid

$$
G_m=\{k/m:k\in\mathbb N^S,\ \sum_xk_x=m\}
\tag{NPC.29}
$$

has $\binom{m+s-1}{s-1}$ points and satisfies

$$
b_d\le\min_{\mu\in G_m}\beta(\mu)
\le b_d+\frac{s-1}{m}.
\tag{NPC.30}
$$

There is also a strictly positive rational grid

$$
G_m^+=\{((k_x+1)/(m+s))_{x\in S}:k\in\mathbb N^S,
                                      \ \sum_xk_x=m\}
\tag{NPC.31}
$$

of the same cardinality, with all coordinates at least $1/(m+s)$,
for which the error in (NPC.30) is at most $2(s-1)/(m+s)$.
For either grid let $\delta$ denote its displayed error bound.
For every $\eta>0$ there is a grid point $\mu$ and a rational
$0<C\le1$ giving a valid cap with

$$
b_d\le C\le b_d+\delta+\eta,\qquad
0\le\sigma_d+\log_2C
\le\log_2\bigl(1+s(\delta+\eta)\bigr).
\tag{NPC.32}
$$

Thus the exact block lower endpoint can be approximated to any given
error by a finite, explicitly specified set of rational weight
parameters, with the all-length condition (NPC.28) retained.

Proof. Start from a minimizing $\mu_d$. Round down its first $s-1$
coordinates to multiples of $1/m$ and put the remainder in the last
coordinate. This gives $q\in G_m$ with
$\operatorname{TV}(q,\mu_d)<(s-1)/m$. Apply (NPC.24).
The number of integer compositions of $m$ is the stated binomial
coefficient.

For the positive grid put $\widetilde q=(mq+\mathbf1)/(m+s)$.
If $u$ is uniform on $S$, then
$\widetilde q=\frac m{m+s}q+\frac s{m+s}u$.
Since $\operatorname{TV}(u,\mu_d)\le1-1/s$, the triangle inequality
gives

$$
\operatorname{TV}(\widetilde q,\mu_d)
<\frac{s-1}{m+s}+\frac{s-1}{m+s}.
$$

Apply (NPC.24) again. This proves both grid estimates, without
knowledge of which grid point is near a minimizer.

Choose a rational cap at least $\beta(\mu)$ and at most
$b_d+\delta+\eta$. If $\beta(\mu)<1$, rational density permits
such a cap below or equal to one; if $\beta(\mu)=1$, use $C=1$.
Definition 6.3 gives validity. Every valid cap has $C\ge b_d$;
using $b_d\ge1/s$ gives

$$
\sigma_d+\log_2C=\log_2(C/b_d)
\le\log_2(1+s(\delta+\eta)).
$$

For example choose $m$ with $(s-1)/m\le\delta_0$ for the first
grid, or $2(s-1)/(m+s)\le\delta_0$ for the positive grid. Taking
$\log_2(1+s(\delta_0+\eta))$ below the desired block tolerance
gives the quantified approximation. No length cutoff enters this
parameter estimate. $\square$

## 7. Consequences for every original paid-export competitor

**Theorem 7.1 (all-original-competitor mass transport).** Let $d\ge1$
and let a probability $\mu$ and a real $C>0$ satisfy
$\beta(\mu)\le C$. For every $D\ge d$ and every original correct
preparation/reader pair of Assumption 1.2,

$$
|E[\mathcal F_D]|\ge
\left\lceil C^{-2^{D-d}}\right\rceil.
\tag{NPC.33}
$$

Hence the same bound holds for $M_1(D)$ and
$\lambda\ge-2^{-d}\log_2C$. In particular the attained $\mu_d$
gives the cap $C=2^{-\sigma_d}$ simultaneously at every $D\ge d$.

Proof. Put $h=D-d$ and $n=2^h$. Fix an actual perfect ordered binary
scaffold of height $h$ in the right subtree. At its frontier addresses
$a_1,\ldots,a_n$, all of length $h$, insert all tuples $x\in S_d^n$
of actual trees. The resulting $t_x=\langle\alpha,v_x\rangle$ have
right-subtree height at most $h+d=D$ and are distinct. They are one
mandatory slice of the full original variable-shape family.

For every block target $q\in W_d$, $p=Ra_iq$ is an original permitted
request, since $1\le|p|\le1+h+d-1=D$. The occurrence $Ra_i$ is
actually present in every source on this slice. Homomorphic transport
(NPC.3) therefore identifies the entire target trajectory with that
of $\Gamma_q(x_i)$ at every authentic count. This meets exactly
`original_present_transport`'s presence premise.

Restrict the same original complete code to this slice. On a fixed
code and request the decision to make zero Reads, or the literal
submitted, is fixed before any reply or supplied $k$. Account for
every finite word: the root and left-wrapper cone give fixed replies;
a right-cone word ending strictly above the frontier gives branch;
every other right-cone word enters one unique actual block $j$ with
an arbitrary finite suffix. Convention 2.3 replaces that suffix by
a function of one boundary reply in the same $j$, or by a constant.
It does not move it to the target block.

Equal selected boundary replies in a restricted code fiber therefore
give equal actual replies, identical final predictors, and equal
complete target trajectories by correctness for all $k$. Convention
2.1 makes the target factors equal. A zero-Read branch or constant
reply makes the factor constant on that fiber. Thus every nonempty
restricted fiber is a member of $\mathcal B_n$, retaining all its
correlations and every target's own witness choice.

Assign the analytical product law $\mu^n$ to the entire slice. Its
total mass is one and each restricted fiber has mass at most $C^n$.
The fibers form a partition, so their number is at least $C^{-n}$.
It is at most the original complete attained alphabet, proving the
ceiling. Minimize over original competitors, divide logarithms by
$2^D=2^dn$, and use the supplied rate limit to get the rate bound.
The last assertion follows from (NPC.27). $\square$

This transport is the all-word actual-scaffold restriction of [FMR,
Theorem 6.3][FMR] and [NDR, Proposition 3.3][NDR], with (NPC.26)'s
attained global cap. The product law is an analytical lower witness,
not a source prior, an observation, retained advice, or a choice of
source-dependent request. Fixed coordinates in Lemma 3.1 provide no
cut descriptor or selector to the reader. All actual blocks retain
their original occurrences; no artificial root is queried.

**Corollary 7.2 (exact rational-cap expression for the original rate).**
With validity as in Definition 6.3,

$$
\boxed{\displaystyle
\lambda=\sup_{d\ge1}
\sup_{\substack{\mu\in\Delta(S_d)\cap\mathbb Q^{S_d},\ C\in\mathbb Q_{>0}\\
                         (\mu,C)\text{ valid}}}
-2^{-d}\log_2C.}
\tag{NPC.34}
$$

The same supremum results if every $\mu$ is required strictly positive
and $C\le1$. For any $\epsilon>0$, one may first choose $d$ with
$2^{-d}\phi<\epsilon/2$ and then choose the rational mesh and cap
rounding with
$2^{-d}\log_2(1+s(\delta+\eta))<\epsilon/2$; the resulting valid
pair has original-rate endpoint greater than $\lambda-\epsilon$.

Proof. Theorem 7.1 bounds every endpoint by $\lambda$. Theorem 6.4
makes valid rational endpoints cofinal in $2^{-d}\sigma_d$, also
with strictly positive weights and $C\le1$. Apply (NPC.8); its
geometric error gives precisely the stated two contributions.
The depth choice can use $\phi\le1$. Mesh finiteness and this
choice do not decide the universal validity condition. $\square$

**Convention 7.3 (credited caps and separate attainment resources).**
[NCM, Theorems 3.3 and 4.1][NCM] already supply $\sigma_2=\log_2(25/17)$:
their integer weights have total $25$, all-joint cap $17$, and products
of their $H_\alpha$ attain that mass. [NCE, Theorems 6.1–6.2 and
Proposition 5.2][NCE] supply weights of total $429$, all-joint cap
$169$, and mass-attaining products for those chosen weights. Thus
their normalized vectors have respectively $\beta=17/25$ and
$\beta=169/429=13/33$. Equality for the latter chosen weight system
does not identify the minimum in (NPC.26). NCE's heavy-target
criterion is sufficient; its completeness is not a premise here.

Whenever a finite cover upper or the computed $M_1(D)$ in (NPC.8)
is used, its actual acquisition is [FMR, Theorems 2.3–2.5][FMR]'s scan
of every $Rq$, $q\in W_D$, on the stationary source. It uses at most
$2^D-1$ preparation Reads, maximum literal length $D$, and
$(D-1)2^D+1$ submitted letters on every source. The acquired boundary
computes the first-containing-member name; every other source
distinction is isolated under Assumption 1.2. A minimum cover's names
are all attained, since an unused member could be deleted.

At $n$ public prefix-free actual block occurrences $Ra_i$ with
$|a_i|\le H$, [FMR, Lemmas 3.1 and 6.2][FMR] instead gives
$n(2^d-1)$ Reads, maximum length $H+d$, and at most

$$
n\bigl((H+1)(2^d-1)+(d-2)2^d+2\bigr)
$$

submitted letters, by the actual literals $Ra_iw$, $w\in W_d$.
Their late queries are actual words at the selected original block.
The reply-to-factor table yields a predictor of at most
$\lceil\log_2(2D+1)\rceil+1$ bits for $(b,c)$, separately from
retained names and count representation. Cover generation, membership
work, installation, control, allocation, buffers, post-request space,
proof parameters and proof search remain separate resources.
Theorems 6.2 and 7.1 construct lower witnesses, not new attaining
encoders or physical isolation services.

## 8. The precise effective-certification premise

**Definition 8.1 (a sound cofinal cap verifier).** A cap verifier is a
total computable predicate $V(d,\mu,C,\pi)$ for $d\ge1$,
$\mu\in\Delta(S_d)\cap\mathbb Q^{S_d}$, $C\in\mathbb Q_{>0}$
and finite strings $\pi$. Soundness means that acceptance implies
(NPC.28) at that $d$, for every length and complete template. Cofinality means
that for every $d\ge1$ and rational $\epsilon>0$, some accepted pair
has

$$
-\log_2C>\sigma_d-\epsilon.
\tag{NPC.35}
$$

A sufficient stronger completeness premise is that for every rational
probability $\mu$ and rational $C>\beta(\mu)$, some finite $\pi$
is accepted. By Theorem 6.4 this stronger premise implies cofinality.
Existence of such a sound cofinal verifier is an additional premise;
it is not included in the closure, continuity or compactness assumptions.

**Theorem 8.2 (conditional effective approximation of the original rate).**
If a verifier satisfying Definition 8.1 exists, then for every positive
rational $\epsilon$ there is a terminating effective computation of
rational $l,u$ with $l\le\lambda\le u$ and $u-l<\epsilon$.

Proof. Enumerate all rational inputs and finite strings and run the
total verifier. Each acceptance gives the valid lower endpoint
$-2^{-d}\log_2C$ by Theorem 7.1. Keep the greatest certified rational
lower enclosure seen, including zero. Dovetail this enumeration with
the finite canonical-cover computations of $M_1(D)$ supplied by FMR,
keeping the least rational upper enclosure of
$2^{-D}\log_2(M_1(D)+1)$ seen. Rational logarithm enclosures can be
refined to arbitrary precision. Their validity follows from elementary
monotonicity and convergent rational series for the logarithm.

Soundness keeps $l\le\lambda\le u$. Cofinality, (NPC.8) and growing
$d$ make the supremum of accepted lower endpoints equal to $\lambda$.
The computed shifted uppers also tend to $\lambda$. Therefore a
finite stage has a true endpoint gap less than $\epsilon/2$ and
sufficiently fine logarithm enclosures have width less than the
remaining $\epsilon/2$. Stop when their rational gap is below
$\epsilon$. This stopping test is decidable and eventually succeeds.
The argument supplies no useful time, table-size or certificate-size
bound. $\square$

**Proposition 8.3 (finite refutations and the remaining quantifier).**
For rational $\mu,C$, invalidity of (NPC.28) is semidecidable by a
finite violating template. For every $N$, $\beta_N(\mu)$ is a
computable real, and $\beta_N(\mu)\uparrow\beta(\mu)$. These facts
and the explicit weight modulus in (NPC.24) specify no modulus of
this length convergence and no verifier satisfying Definition 8.1.

Proof. Enumerate $n$ and its finitely many complete templates. At a
fixed template, its mass and $C^n$ are exact rationals; a strict
violation is decidable. If (NPC.28) is false, some finite pair
$(n,\Theta)$ violates it, and enumeration eventually finds it.
At fixed $N$, all maxima $A_n(\mu)$ are finite rational computations;
their roots and finite maximum admit computable real enclosures.
The increasing-limit claim is the definition of $\beta$.

These conclusions provide lower enclosures of $\beta$, whereas a cap
requires an upper bound at every length. The proof of (NPC.14) uses
unquantified near-optimal rational-type block lengths and compactness.
Neither that proof nor (NPC.24), whose variables are weights at a fixed
native depth, provides a computable tail error in $N$. A cap verifier
is accordingly an additional hypothesis in Theorem 8.2, with its
soundness and cofinality separately required. This identifies a missing
premise, not a noncomputability or impossibility assertion. $\square$

The distinction between a Fekete limit and an effective error bound
is also discussed for graph/channel capacities in [Boche–Deppe,
Theorem 12 and Remarks 13 and 38][BD]. No reduction from this native
rate to a noncomputable graph/channel quantity is assumed. The effective
length error in NDR's (NDR.37), sharp $\lambda$, general exact
$M_1(D)$, and the wider mutual-recovery problem are distinct remaining
mathematical questions. Formula (NPC.34) is a semantic completeness
identity, and Theorem 8.2 is conditional on (NPC.35).

## 9. Shared realization and mathematical correspondence boundaries

**Convention 9.1 (equality-aware template sums).** For a fixed template,
its mass is

$$
\sum_{x\in S^n}\left(\prod_i\mu(x_i)\right)
                 \prod_{F\in\Theta}\mathbf1_F(x).
\tag{NPC.36}
$$

The standard finite-alphabet equality-node normalization of
[Al-Bashabsheh–Mao, §§3.2–3.3 and 4.2][AM] applies to this symbolic
sum: keep one representative for each original variable, replace its
constraint incidences by copies, impose equality of every copy to that
representative, and put $\mu$ only on the representative. Each original
assignment has exactly one equality-consistent lift and conversely,
with the same product weight, so the sum is exactly unchanged.
This is the cited equality-node identity as an intermediate
representation of (NPC.36), not a new native decomposition theorem.
Dropping equality changes the feasible assignments; attaching the
weight to every copy changes it to a power of that weight.

Copies in this sum are symbolic variables, not physical sources or
additional readable ports. A source-bearing experiment still names one
original block and one literal. The normalization yields no bound on
width, no universally cheap reblocking, and no all-size cap verifier.
NDR's Theorem 7.2 and Proposition 9.1 retain respectively their fixed-cut
repair obstruction and their particular family's faithful finer cut;
neither substitutes for a universal change-of-coordinates theorem.

**Convention 9.2 (other source interfaces).** The declaration
`target_family_minimal_quotient` in [TargetFamilyMinimalQuotient][D5T]
assumes that every target passively factors through one readout and
gives the joint-kernel universal property. It supplies no one-probe
repair geometry. The declaration `compact_observation_factorization`
in [CompactObservationFactorization][D5C] assumes a nonempty compact
source, finite discrete observation levels, continuous surjective
compatible observation maps with fibers forming a topological basis,
and a continuous finite readout. Its bounded-action conclusion also
requires a finite action type and continuous actions. Its conclusion
is finite-level factorization under those hypotheses, not an effective
native acquisition or pressure-convergence bound.

Under the paid service assumptions, the operational recovery retained
here is the supplied

$$
(E(t),D,p,\text{at most one actual reply})
\longrightarrow\Gamma_p(t)
\longleftrightarrow\bigl(r_{\rho^kt}(p)\bigr)_{k\ge0}.
$$

The inverse recovers the first branch count and alpha-stage flag.
It does not recover a full source, hidden history, unknown authentic
age, authentication, or physical space and time. Fixed-menu acquisition
in AAR §16 has its declared-menu timing; it does not provide the late
request or the later count before their prescribed stages.

**Convention 9.3 (primary hypotheses and attribution).** The native
section/type/pressure chain in §§3–7 is a repository-derived deduction
from the named native suppliers. The type bounds, entropy variational
identity, finite-dimensional separation and equality-node identity are
mature cited intermediates. No world-priority assertion is attached to
the native deductions. Besides the citations attached to their proofs,
the following primary correspondences fix the remaining transfer limits.

[Gogacz–Toruńczyk, Theorem 1 and Corollary 1][GT] concern a fixed
conjunctive-query schema and functional dependencies, with an
almost-entropic characterization and a submodular outer bound.
A native equation (NPC.7) gives
$H(g_q(X_i)\mid r_a(X_j))=0$ under one common law. The native state
alphabet and maps stay fixed while length and donor topology vary;
database achievability or a Shannon relaxation supplies neither
(NPC.21) nor a cofinal verifier. The proof here uses the actual
decoder equations throughout.

[Dyer–Richerby, §2][DR] define a finite-domain constraint language
whose instances have arbitrarily many variables. Native complete
templates are such finite instances of the unary/binary language in
NDR §2. Finite-instance counting and its complexity classification
provide no universal size cutoff for (NPC.28), and no bounded-width
or tractable-polymorphism property of this native language is assumed.

Repository citations and definition correspondences use revision
`b45e51761afc5b5f00d7d336389675c4354c2ed7` and only the specified
supplier statements. Theorems 5.3, 6.2 and 6.4 concern exact all-size mathematical
pressure, attainment and finite weight descriptions. They leave the
additional effective premise of Definition 8.1 explicit.

[NDR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DONOR_NETWORKS_AND_REPAIR_COST.md
[FMR]: RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[NCM]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CORRELATED_MEMORY_LOWER.md
[NCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CYCLIC_ENTROPY_LOWER.md
[AAR]: RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[D5G]: ../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean
[D5A]: ../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[D5L]: ../../../D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity.lean
[D5N]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[D5T]: ../../../D5/S3/ConceptDynamics/SufficiencyQuotient/TargetFamilyMinimalQuotient.lean
[D5C]: ../../../D5/S3/ObserverMemory/ProObjects/CompactObservationFactorization.lean
[V]: https://arxiv.org/html/1903.01857 "Péter Vrana, Probabilistic refinement of the asymptotic spectrum of graphs, Propositions 3.3–3.4"
[R]: https://doi.org/10.1515/9781400873173 "R. Tyrrell Rockafellar, Convex Analysis, §§11–12"
[CLR]: https://arxiv.org/html/2407.02281v2 "Nicolas Charpenay, Maël Le Treust and Aline Roumy, On the Linearization of Optimal Rates for Independent Zero-Error Source and Channel Problems, Theorem 7"
[AM]: https://arxiv.org/html/1209.3300v1 "Ali Al-Bashabsheh and Yongyi Mao, Normal Factor Graphs as Probabilistic Models, §§3.2–3.3 and 4.2"
[BD]: https://arxiv.org/html/2001.11442v3 "Holger Boche and Christian Deppe, Computability of the Zero-Error Capacity with Kolmogorov Oracle, Theorem 12 and Remarks 13 and 38"
[GT]: https://arxiv.org/html/1512.01808v1 "Tomasz Gogacz and Szymon Toruńczyk, Entropy bounds for conjunctive queries with functional dependencies, Theorem 1 and Corollary 1"
[DR]: https://arxiv.org/html/1003.3879v4 "Martin Dyer and David Richerby, An Effective Dichotomy for the Counting Constraint Satisfaction Problem, §2"

## 追加锚（本行以下为增补区）
