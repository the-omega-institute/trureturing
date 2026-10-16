# Recursive relational observation: native soft constraint pressure

This volume records ordinary mathematical deductions for the unchanged
native late-target task. It is theory reference input, not Lean-kernel
certification. The two soft carriers below are analytical relaxations;
they do not enlarge the source alphabet, an attained code fiber, or the
legal native solution sets.

## 1. Exact owned-seed carrier

**Definition 1.1 (canonical blocks and whole-block potentials).** Fix
$d\ge1$. Use the credited canonical alphabet

$$
S_1=\{\alpha,\beta,C_0\},\qquad C_0=\langle\alpha,\alpha\rangle,\qquad
S_{d+1}=\{\alpha,\beta\}\sqcup\{\langle x,y\rangle:x,y\in S_d\}.
$$

Let $W_d=\{q:|q|\le d-1\}$, $m_d=|W_d|=2^d-1$, and let
$\Gamma_q:S_d\to G_q$ be the credited complete temporal factor. Its
reply map $h_q:G_q\to\mathcal A$ satisfies
$h_q(\Gamma_q(u))=r_u(q)$, where
$\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$. The
root range has exactly three replies and every nonroot range has all
four; these values are obtained by the canonical trees along the path.

An owned-seed network on $n$ original blocks has a finite seed set $J$.
Each seed $c$ has a nonempty domain $T_c\subseteq\mathcal A$, a distinct
actual owner port $o_c=(i_c,q_c)$, and a table at every occurrence. A
port $(i,q)$ is prescribed either by a constant in $G_q$ or by
$B_{i,q}(s_c)$ for one seed $c$, with

$$
h_{q_c}(B_{o_c}(a))=a\qquad(a\in T_c).
\tag{SCP.1}
$$

The same seed variable is used at every repeated, self, or cyclic
occurrence. Put

$$
O_i=\{c:i_c=i\},\qquad
I_i=\{c:c\text{ occurs in at least one port of block }i\},\qquad
\nu(c)=|\{i:c\in I_i\}|.
$$

For $s\in\mathcal S:=\prod_{c\in J}T_c$, let $z_{i,q}(s)$ be the
prescribed factor. For arbitrary nonnegative whole-block weights
$w_i:S_d\to[0,\infty)$ define

$$
\Phi_i^{w_i}(s)=\sum_{u\in S_d}w_i(u)
       \prod_{q\in W_d}{\bf1}_{\{\Gamma_q(u)=z_{i,q}(s)\}},\qquad
Z_{\mathcal N}(w_1,\ldots,w_n)=\sum_{s\in\mathcal S}\prod_{i=1}^n\Phi_i^{w_i}(s).
\tag{SCP.2}
$$

RRN's two-way correspondence identifies this with the mass of the
corresponding complete native template. Each $\Phi_i$ is zero or the
weight of its uniquely reconstructed actual block. Thus each original
joint block weight is used exactly once, even when many ports share a
seed. If a domain is empty, the seed sum and the native solution set
are empty. With no seeds there is one empty assignment, whose value may
still be zero because of incompatible constants or zero weights.

For $L\ge1$, let $\mathfrak N_{d,L}(n)$ be the networks with
$\nu(c)\le L$; write $\mathfrak N_{d,\infty}(n)$ for the unrestricted
class. Define the hard pressures

$$
\beta_{d,L}(w)=\sup_{n\ge1}\sup_{\mathcal N\in\mathfrak N_{d,L}(n)}
 Z_{\mathcal N}(w,\ldots,w)^{1/n},\qquad \beta_d=\beta_{d,\infty}.
\tag{SCP.3}
$$

All lengths, arbitrary donor choices, repeated occurrences, cycles,
guards, compatibility zeros, and correlated whole-block weights remain
in these suprema.

**Definition 1.2 (owner multiplicity).** Set

$$
R_d=3\,4^{m_d-1}=3\,4^{\,2^d-2}.
\tag{SCP.4}
$$

At most $R_d$ joint owner-reply assignments can be chosen in one
original block: its owner ports are distinct, the root has at most three
reply values, and each other port has at most four. This counts owner
tuples, not independent child codes. No independence is assumed.

## 2. Exact owner-block deletion

**Theorem 2.1 (actual-owner block deletion).** Let $\mathcal N$ have
$n$ blocks and let $B\subseteq[n]$. Put
$H_B=\bigcup_{i\in B}O_i$ and
$T_{H_B}=\prod_{c\in H_B}T_c$. For every
$a\in T_{H_B}$, including an assignment that cannot be extended to a
globally compatible tuple, construct $\mathcal N^{B,a}$ by deleting the
blocks in $B$, replacing every surviving occurrence of a seed in $H_B$
by its constant value $B_{i,q}(a_c)$, and deleting those seeds and their
owner declarations. Keep every other seed, table, guard, and occurrence.
Then $\mathcal N^{B,a}$ is a valid owned-seed network on $n-|B|$ blocks,
and its incidences do not increase. For arbitrary nonnegative whole-
block weights,

$$
\sum_{s\in\mathcal S}\prod_{i\notin B}\Phi_i^{w_i}(s)
 =\sum_{a\in T_{H_B}}
 Z_{\mathcal N^{B,a}}((w_i)_{i\notin B}).
\tag{SCP.5}
$$

Moreover,

$$
|T_{H_B}|\le R_d^{|B|}.
\tag{SCP.6}
$$

**Proof.** A substituted value is in the same attained factor range
$G_q$, and every surviving seed retains its distinct owner and identity
(SCP.1). A seed owned in a deleted block has no remaining owner and all
of its surviving occurrences have become constants, so no dangling
variable remains. RRN's converse therefore supplies a complete native
template for the residual network, including its actual-tree guards.

Split the finite sum on the left of (SCP.5) according to the values
$a$ on $H_B$. For fixed $a$, the remaining factor vector in each
surviving block is exactly the old vector with those seed coordinates
substituted, hence the inner sum is the residual partition function.
No compatibility condition on a deleted block is imposed; this is why
nonextendable $a$ are harmless analytical sections. The owner ports in
each deleted block are distinct, so their domain product is bounded by
the root range three and the nonroot ranges four, giving (SCP.6).

If $B=[n]$, every seed is deleted because every seed has an owner and
the residual empty network has value one. Empty domains, singleton
domains, zero weights, self-donors, repeated occurrences, and cyclic
donors obey the same finite distributivity identity. No source subtree
is physically removed and no seed vector is exposed to a reader. $\square$

**Corollary 2.2 (deletion cost under a hard cap).** If a common weight
$w$ has $\beta_{d,L}(w)\le C$, then for every $B$,

$$
\sum_s\prod_{i\notin B}\Phi_i^w(s)
 \le R_d^{|B|}C^{\,n-|B|},
\tag{SCP.7}
$$

with $C^0=1$. This is valid for $L=\infty$ as well. It is a bound on
the exact once-owned carrier, not a product approximation of the block
weights.

## 3. Seed-table softening and its sharp floor

**Definition 3.1 (normalized owner kernels).** For a nonempty-domain
network choose, independently for each block, a probability kernel

$$
q_i:\prod_{c\in O_i}T_c\longrightarrow[0,1],\qquad
\sum_aq_i(a)=1,
\tag{SCP.8}
$$

where the empty owner product has its single empty tuple. The uniform
choice is strictly positive and satisfies $q_i(a)\ge4^{-m_d}$. For
$\varepsilon_i\ge0$ put

$$
\Phi_i^{\mathrm{ker},\varepsilon_i}(s)=\Phi_i^w(s)+\varepsilon_iq_i(s|_{O_i}),\qquad
Z^{\mathrm{ker},\boldsymbol\varepsilon}_{\mathcal N}
=\sum_s\prod_i\Phi_i^{\mathrm{ker},\varepsilon_i}(s).
\tag{SCP.9}
$$

This keeps exactly the old seeds, scopes, owners, and block weights.
For $\varepsilon_i>0$, the softened local table is positive at $s$
if and only if $\Phi_i^w(s)>0$ or $q_i(s|_{O_i})>0$. Hence full
support of every $q_i$ and positivity of every $\varepsilon_i$ suffice
for strictly positive local tables on the entire nonempty seed domain.
In particular, uniform kernels and a common $\varepsilon>0$ give
$\Phi_i^{\mathrm{ker},\varepsilon}(s)\ge\varepsilon4^{-m_d}$.
Normalization alone does not ensure this support condition.
Empty-domain networks still have value zero.

**Definition 3.2 (unnormalized floor).** Put instead

$$
\Phi_i^{\mathrm{fl},\varepsilon_i}(s)=\Phi_i^w(s)+\varepsilon_i,\qquad
Z^{\mathrm{fl},\boldsymbol\varepsilon}_{\mathcal N}
=\sum_s\prod_i\Phi_i^{\mathrm{fl},\varepsilon_i}(s).
\tag{SCP.10}
$$

The floor is per block, not per seed. A shared seed is never copied.
Both (SCP.9) and (SCP.10) are analytical partition carriers; their
positive or ghost assignments are not newly legal source states and do
not define attained code fibers.

**Theorem 3.3 (uniform additive pressure bounds).** Define the all-size
soft pressures by taking the supremum of the corresponding $n$th roots
over $\mathfrak N_{d,L}(n)$, denoted
$\beta^{\mathrm{ker}}_{d,L,\varepsilon}(w)$ and
$\beta^{\mathrm{fl}}_{d,L,\varepsilon}(w)$ in the homogeneous case.
The kernels may be any normalized nonnegative kernels of Definition
3.1, including kernels with zeros. Then

$$
\beta_{d,L}(w)\le\beta^{\mathrm{ker}}_{d,L,\varepsilon}(w)
 \le\beta_{d,L}(w)+\varepsilon,
\tag{SCP.11}
$$

and

$$
\beta_{d,L}(w)\le\beta^{\mathrm{fl}}_{d,L,\varepsilon}(w)
 \le\beta_{d,L}(w)+R_d\varepsilon.
\tag{SCP.12}
$$

For nonhomogeneous floors or kernels, if the hard cap is
$\beta_{d,L}(w)\le C$, then

$$
Z^{\mathrm{ker},\boldsymbol\varepsilon}_{\mathcal N}
 \le\prod_{i=1}^n(C+\varepsilon_i),\qquad
Z^{\mathrm{fl},\boldsymbol\varepsilon}_{\mathcal N}
 \le\prod_{i=1}^n(C+R_d\varepsilon_i).
\tag{SCP.13}
$$

Consequently the same inequalities hold whenever
$\sup_i\varepsilon_i\le\varepsilon$.

**Proof.** Expand the product over a subset $B$ of blocks at which the
added term is selected. For the kernel, conditioning on the owners of
$B$ gives (SCP.5), and the owner kernels sum to one over those owners.
Thus the term for $B$ is at most
$\varepsilon^{|B|}C^{n-|B|}$. The binomial theorem gives
$(C+\varepsilon)^n$. For the floor, the same conditioning leaves at
most $R_d^{|B|}$ assignments by (SCP.6), giving
$(C+R_d\varepsilon)^n$. Distinct deleted blocks have disjoint owner
sets, while every incoming shared seed is summed only once in the
residual section. This proves (SCP.13) and the pressure bounds.

More generally, let a nonnegative perturbation $\Psi_i(s)$ use the
same seed scope and define

$$
\kappa_i=\sum_{a\in\prod_{c\in O_i}T_c}
 \max_{b\in\prod_{c\in I_i\setminus O_i}T_c}\Psi_i(a,b),
\tag{SCP.14}
$$

with the empty-product conventions. The same proof gives
$Z(\Phi+\Psi)\le\prod_i(C+\kappa_i)$. The kernel has
$\kappa_i=\varepsilon_i$; the floor has
$\kappa_i=|\prod_{c\in O_i}T_c|\varepsilon_i\le R_d\varepsilon_i$.
This is a nonhomogeneous perturbation statement, not a claim that
heterogeneous block weights have one common pressure cap. $\square$

**Proposition 3.4 (sharpness of the floor constant).** The coefficient
$R_d$ in (SCP.12) is the smallest universal coefficient for the
unnormalized floor. Take $w=0$, give every port its own seed with the
full attained reply range at that port, and let every seed occur only in
its owner block. Then the hard partition is zero while every block has
exactly $R_d$ owner assignments, so

$$
Z^{\mathrm{fl},\varepsilon}_{\mathcal N}=(R_d\varepsilon)^n.
$$

No smaller coefficient can bound its $n$th root for all $n$. At depth
$d=1$, the same three independent root owners show the coefficient is
attained even for nonzero weights.

**Proposition 3.5 (a normalized kernel need not fill native zeros).**
At $d=1,n=1$, take one seed owned at the root, with full domain
$\{\alpha,\beta,\mathsf{branch}\}$ and owner table
$B(\alpha)=\Gamma_{\varnothing}(\alpha)$,
$B(\beta)=\Gamma_{\varnothing}(\beta)$,
$B(\mathsf{branch})=\Gamma_{\varnothing}(C_0)$.
In that order let $w=(1,0,0)$, $q=(1,0,0)$ and $\varepsilon=1$.
The softened local table is $(2,0,0)$, despite positive
$\varepsilon$ and normalization of $q$.

**Proof.** The three actual sources
$\langle\alpha,\alpha\rangle$, $\langle\alpha,\beta\rangle$ and
$\langle\alpha,C_0\rangle$ belong to $\mathcal F_1$ and give precisely
these seed replies at the original-root literal $R$. Each owner-table
entry has its declared reply and reconstructs the corresponding unique
state of $S_1$. Formula (SCP.9) therefore gives
$(1,0,0)+(1,0,0)=(2,0,0)$. This leaves (SCP.11)–(SCP.13) intact:
their proof uses nonnegativity and normalization, not full support.
$\square$

## 4. Complementary actual-tuple defect fugacity

**Definition 4.1 (defect carrier).** A complete native template $\Theta$
on $n$ canonical blocks has one target prescription for each $(i,q)$:
either a constant in $G_q$ or a donor reply followed by a total decoder.
For $x\in S_d^n$, let $v_\Theta(x)$ be the number of these prescriptions
that $x$ violates. For a probability $\mu$ and $0\le\varepsilon\le1$,

$$
Z^{\mathrm{def}}_{\Theta,\varepsilon}(\mu)
 =\sum_{x\in S_d^n}\prod_i\mu(x_i)
       \varepsilon^{v_\Theta(x)},\qquad 0^0=1.
\tag{SCP.15}
$$

The carrier is the ambient actual-tuple space $S_d^n$: a defective
$x$ is an analytical assignment, not a legal solution or an attained
code fiber. This differs from (SCP.9), whose carrier is the seed space
$\prod_cT_c$ and whose incompatible seed vectors may reconstruct no
actual tuple.

For $0<\varepsilon\le1$, the constraint factor
$\varepsilon^{v_\Theta(x)}$ is positive on all of $S_d^n$.
The complete weighted summand is strictly positive exactly on
$(\operatorname{supp}\mu)^n$; positivity on the entire ambient
actual-tuple space additionally requires full support of $\mu$.

**Theorem 4.2 (all-size defect-removal inequality).** Let
$A_{d,n}(\mu)$ be the hard maximum over complete templates on $n$
blocks, with $A_{d,0}=1$, and let
$A_{d,\varepsilon,n}(\mu)$ be the maximum of (SCP.15). Then

$$
A_{d,\varepsilon,n}(\mu)
 \le\sum_{B\subseteq[n]}\varepsilon^{|B|}A_{d,n-|B|}(\mu)
 =\sum_{k=0}^n\binom nk\varepsilon^kA_{d,n-k}(\mu).
\tag{SCP.16}
$$

Writing $\beta_{d,\varepsilon}(\mu)=\sup_n
A_{d,\varepsilon,n}(\mu)^{1/n}$, one has

$$
\beta_d(\mu)\le\beta_{d,\varepsilon}(\mu)
 \le\beta_d(\mu)+\varepsilon.
\tag{SCP.17}
$$

The same statements hold for the bounded-incidence subclass when the
defect carrier is restricted through its owned-seed representative.

**Proof.** For $x$, let $B(x)$ be the blocks containing at least one
violated target. Then $v_\Theta(x)\ge|B(x)|$. Fix $B=B(x)$ and the
actual values $a=x|_B$. Delete the blocks in $B$. A surviving target
whose donor lies in $B$ becomes a constant after substituting the reply
of $a$; a target whose donor survives is unchanged. By the definition
of $B$, every surviving target is satisfied, so the restriction
$x|_{B^c}$ belongs to the residual hard template. Sum first over the
deleted values; their probabilities sum to one. The residual mass is at
most $A_{d,n-|B|}(\mu)$, and summing over $B$ proves (SCP.16).
Since $A_{d,m}(\mu)\le\beta_d(\mu)^m$, the binomial theorem gives
$A_{d,\varepsilon,n}\le(\beta_d(\mu)+\varepsilon)^n$. Hard solutions
have defect zero, proving the lower inequality. The bounded-incidence
version deletes owner seeds and substitutes their shared values, so
incidence cannot increase. $\square$

For heterogeneous nonnegative weights $w_i$, put
$W_i=\sum_{u\in S_d}w_i(u)$. The same proof gives the exact-domain
bound

$$
\sum_x\prod_iw_i(x_i)\varepsilon^{v_\Theta(x)}
 \le\sum_{B\subseteq[n]}\varepsilon^{|B|}
 \left(\prod_{i\in B}W_i\right)
 A_{n-|B|}((w_i)_{i\notin B}),
\tag{SCP.18}
$$

where the final $A$ is the hard maximum with the displayed remaining
whole-block weights. No childwise factorization or independent recolor
is used.

## 5. Optimized semantic errors and rational parameters

**Proposition 5.1 (weight-optimized bounds).** Put

$$
b_{d,L}=\inf_{\mu\in\Delta(S_d)}\beta_{d,L}(\mu),\qquad
\tau_{d,L}=-\log_2 b_{d,L},
$$

and define $b^{\mathrm{ker}}_{d,L,\varepsilon}$,
$b^{\mathrm{fl}}_{d,L,\varepsilon}$, and $b^{\mathrm{def}}_{d,L,\varepsilon}$
by taking the corresponding infima over $\mu$. Then

$$
\begin{aligned}
0&\le -\log_2b_{d,L}+\log_2b^{\mathrm{ker}}_{d,L,\varepsilon}
 \le\log_2(1+s_d\varepsilon),\\
0&\le -\log_2b_{d,L}+\log_2b^{\mathrm{fl}}_{d,L,\varepsilon}
 \le\log_2(1+s_dR_d\varepsilon),\\
0&\le -\log_2b_{d,L}+\log_2b^{\mathrm{def}}_{d,L,\varepsilon}
 \le\log_2(1+s_d\varepsilon),
\end{aligned}
\tag{SCP.19}
$$

on exactly the domains defined above. Here $s_d=|S_d|$, and the lower
bound $b_{d,L}\ge1/s_d$ comes from a one-block constant network. For
$L=\infty$, $\tau_{d,\infty}=\sigma_d$ by the credited NPC identity.

**Proof.** The pointwise pressure bounds give
$b\le b^\star\le b+c\varepsilon$. Divide by
$b\ge1/s_d$ and take logarithms. No infimum is asserted to be attained
for an auxiliary soft pressure. $\square$

**Proposition 5.2 (rational approximation condition).** For every real
$\mu\in\Delta(S_d)$ and every $\delta>0$, there is a rational probability
$\nu$ supported on $\operatorname{supp}\mu$ with
$\nu(x)\le(1+\delta)\mu(x)$ for all $x$. For each of the three soft
carriers and every fixed rational $\varepsilon\ge0$,

$$
\beta^\star_{d,L,\varepsilon}(\nu)
 \le(1+\delta)\beta^\star_{d,L,\varepsilon}(\mu).
\tag{SCP.20}
$$

Thus each auxiliary infimum is unchanged when restricted to rational
probabilities. For the kernel carrier, strictly positive local tables
are guaranteed by full-support kernels and positive rational
$\varepsilon$; the floor needs only positive $\varepsilon$. For the
defect carrier, positive rational $\varepsilon\le1$ gives positivity
on the probability support as in Definition 4.1. A rational cap may
always be rounded upward after a semantic cap is established.

**Proof.** Approximate inside the finite support simplex. In the defect
carrier, every length-$n$ product mass gains at most
$(1+\delta)^n$. In the seed carriers, each baseline potential gains at
most $(1+\delta)$, and
$\Phi+\Psi\le(1+\delta)(\Phi+\Psi)$ because $\Psi$ is independent of
$\mu$, keeping the same kernels. The rational approximation may be
chosen positive on every point of $\operatorname{supp}\mu$, so the
defect carrier retains exactly that support; no original zero is filled.
Take $n$th roots and the all-size supremum. $\square$

The bounds (SCP.19) are semantic all-size statements. Finite evaluation
at a chosen length is only a lower approximation to a soft pressure; it
does not provide a length cutoff or a cofinal upper certificate.

## 6. The positive-model obligation and the near-one boundary

**Definition 6.1 (remaining positive verifier obligation).** A positive
cap verifier at fixed $(d,L)$ is a total computable predicate

$$
V^\star(d,L,\mu,\varepsilon,C,\pi)
$$

on rational $\mu$, rational $\varepsilon>0$ (also $\varepsilon\le1$ for
$\star=\mathrm{def}$), positive rational $C$, and a finite certificate
string $\pi$. Soundness requires acceptance to
prove, for every $n$ and every network in the same owned-seed class,

$$
Z^\star_{\mathcal N}(\mu,\ldots,\mu)\le C^n,
\tag{SCP.21}
$$

with the selected carrier $\star\in\{\mathrm{ker},\mathrm{fl},\mathrm{def}\}$
and its exact hypotheses. In the strictly positive kernel specialization
fix the uniform owner kernels of Definition 3.1; more generally a fixed
effective rational full-support kernel rule independent of $\mu$ may
be specified as part of the carrier. Arbitrary
normalized kernels remain covered by the additive bounds, but need not
define a strictly positive model. For the defect carrier the constraint
factors are positive; its complete weighted summands have support
$(\operatorname{supp}\mu)^n$. A result requiring positivity on all of
$S_d^n$ additionally requires full support of $\mu$.
For $\star=\mathrm{ker}$ or $\mathrm{fl}$ the
universal quantifier ranges over owned-seed networks; for
$\star=\mathrm{def}$ it ranges over complete native templates (the RRN
correspondence supplies the stated representation). Cofinality requires accepted endpoints whose
$-\log_2C$ approach $\tau_{d,L}$ as rational $\varepsilon\downarrow0$;
for the unrestricted class, letting $L\to\infty$ must additionally reach
$\sigma_d$. The verifier must quantify over arbitrary lengths, shared
seeds, repeated/self/cyclic donors, compatibility zeros, and complete
joint block weights. Neither a fixed finite catalog nor finite proof
enumeration supplies this obligation.

If such a verifier supplies $Z^\star\le C_0^n$, hard domination and the
credited SIR bound give

$$
\beta_d(\mu)\le4^{m_d/(L+1)}C_0.
\tag{SCP.22}
$$

For any rational $\widehat C$ with
$\widehat C^{L+1}\ge4^{m_d}C_0^{L+1}$, the credited NPC/FMR transport
therefore yields, for every $D\ge d$,

$$
M_1(D)\ge\left\lceil\widehat C^{-2^{D-d}}\right\rceil,\qquad
\lambda\ge-2^{-d}\log_2\widehat C.
\tag{SCP.23}
$$

The two losses are separate: the incidence loss is
$2m_d/(L+1)$ in block pressure, while the soft losses are respectively
$\log_2(1+s_d\varepsilon)$ and
$\log_2(1+s_dR_d\varepsilon)$ at the optimized semantic level.
These are credited SIR/NPC consequences, not a constructed verifier.

**Proposition 6.2 (source-specific near-one-gauge obstruction).** The
usual fixed near-one zero-free shortcut does not follow from strict
positivity in this native carrier. At $d=2$, take a cyclic seed network
with domains $\{\alpha,\beta,\mathsf{branch}\}$, actual root owners,
and one edge that swaps $\alpha$ and $\beta$ while fixing
$\mathsf{branch}$. Set $u(\alpha)=\alpha$, $u(\beta)=\beta$,
$u(\mathsf{branch})=C_0$ and use the attained root, left, and right
tables. Every seed has incidence two, and the only hard solution is
$C_0^n$.

Give the two leaf states mass $a=2/13$ each and all nine pair states
mass $b=1/13$. With $D=\operatorname{diag}(a,a,b)$, $J$ the all-one
matrix, and $P$ the transposition of the first two states, the exact
soft interpolation is

$$
f_n(v)=\operatorname{tr}((D+vJ)^nP),\qquad f_n(0)=b^n.
\tag{SCP.24}
$$

For $n\ge4$, put $t_n=4/(13\,2^n)$. The symmetric two-dimensional
block of $D+vJ$ gives
$f_n(-t_n)<0<f_n(0)$, so a real zero lies in $(-t_n,0)$. Hence the
all-one interpolation $P_n(z)=z^nf_n(1/z-1)$ has a zero

$$
1<z_n<\frac1{1-t_n},
$$

and no radius $r>1$ works uniformly over this nonempty native family.
For the strictly positive floor, the same calculation gives a zero of
$z^nf_n(1/z-1+\varepsilon)$ between
$1/(1-\varepsilon)$ and $1/(1-\varepsilon-t_n)$ whenever
$\varepsilon+t_n<1$. This defeats an $\varepsilon$-independent
near-one gauge, while saying nothing about a different certificate,
an $\varepsilon$-dependent radius, or computability.

The obstruction is only to this specified straight-line mechanism.
Strict positivity is neither a mixing theorem nor an effective
length-tail theorem. The checked Barvinok--Soberón condition that all
edge entries lie within $0.34/\Delta$ of one is not implied as
$\varepsilon\downarrow0$; the native table ratios diverge instead.

## 7. Paid original transport and evidence ceiling

**Theorem 7.1 (credited one-root-Read implementation).** Once a genuine
hard cap has been obtained from (SCP.21) and (SCP.22), the original
late-target interface is implemented by the credited representative
scan: before the request, read the actual original-root literals
$Rq$ for all $q\in W_D$, including absent replies. This uses at most
$2^D-1$ charged Reads, maximum address length $D$, and at most

$$
\sum_{\ell=0}^{D-1}(\ell+1)2^\ell=(D-1)2^D+1
$$

submitted letters. After a public target $p=Rq$ arrives, a constant
factor uses zero Reads; otherwise one actual original-root Read $Ra$ at
the installed representative owner is made before any authentic $k$.
The credited temporal decoder then returns every
$r_{\rho^k t}(p)$ without further Reads.

These are paid source scans and an isolated finite export. They do not
expose a seed vector, source identity, subtree, navigation port, ghost
assignment, or source-dependent topology. Work, installed tables,
workspace, final predictor size, address cost, authentication, handoff,
isolation, and physical time remain separate resources. If exactly the
cardinality of a nonminimal competitor must be preserved, the credited
fuller scan uses at most $2^{D+1}-1$ Reads and may change fibers; this
does not preserve its preparation cost.

**Convention 7.2 (unclosed objectives and attribution).** The deductions
in this volume are the owner deletion identity, its normalized and floor
perturbation bounds, and the complementary defect-fugacity inequality.
The native correspondence, incidence approximation, semantic minimum,
and paid transport are credited respectively to RRN/CBN, SIR, NPC, and
FMR/NPC. The literature sources below are search boundaries, not
transferred native theorems. No total positive verifier, effective
length modulus, sharp general $M_1(D)$, or full mutual recovery is
claimed. The credited numerical interval remains

$$
\frac18\log_2\frac{33}{13}\le\lambda<\frac3{16},\qquad M_1(3)=4.
\tag{SCP.25}
$$

No new endpoint is asserted. In particular, bounded incidence and
strict positivity do not imply bounded width, hyperfiniteness, mixing,
or a finite optimizer cutoff.

[SIR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SEED_INCIDENCE_REDUCTION.md
[RRN]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_REPRESENTATIVE_REPLY_NORMAL_FORM.md
[CBN]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md
[NPC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRODUCT_PRESSURE_COMPLETENESS.md
[FMR]: RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[NDR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DONOR_NETWORKS_AND_REPAIR_COST.md
[RCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RECURSIVE_CERTIFICATE_ESCAPE.md
[BS]: https://arxiv.org/abs/1406.1771v3
[BCKL]: https://arxiv.org/abs/1002.0115v1
[HLS]: https://arxiv.org/abs/1205.4356v2
[CLV]: https://arxiv.org/abs/2106.03366v3

## 追加锚（本行以下为增补区）

## 8. A finite public menu of actual native trees

**Convention 8.1 (the relative-completion question).** Sections 8–13
concern a same-template relative soft-to-hard premise. The additive
all-template supremum bounds in Theorems 3.3 and 4.2 and the optimized
semantic bounds in Proposition 5.1 retain their stated meanings. A
template with a small hard mass need not have a comparably small
relative soft correction. The example below makes that distinction on
actual native templates with a connected tree incidence graph.

All repository suppliers cited in these sections designate their
committed public versions at
`91170b89dfe9dd7eadc64d14d86d2157ed14abdf`. The intended consumer is the
joint completion/loss question in [COK, Open problem 9.3][SCP-COK] and
the unchanged all-size obligation in [GDB, Definition 11.1][SCP-GDB].
The deductions are ordinary mathematics, without Lean certification.

**Definition 8.2 (the eleven actual states and a public family index).**
Work at $d=2$. Write $A=\alpha$, $B=\beta$,
$C_0=\langle A,A\rangle$ and

$$
\mathcal G=\{\langle x,y\rangle:x,y\in\{A,B,C_0\}\},\qquad
S_2=\{A,B\}\sqcup\mathcal G,\qquad W_2=\{\varnothing,L,R\}.
$$

The credited [NCM, (NCM.14)][SCP-NCM] table is

$$
\begin{array}{c|ccc}
x&\Gamma_{\varnothing}(x)&\Gamma_L(x)&\Gamma_R(x)\\ \hline
A&(2,1)&(3,0)&(4,1)\\
B&(1,0)&(2,0)&(3,1)\\
\langle x_0,x_1\rangle&(0,0)&\gamma(x_0)&\gamma(x_1)
\end{array}
\qquad
\gamma(A)=(2,1),\quad\gamma(B)=(1,0),\quad\gamma(C_0)=(0,0).
\tag{SCP.26}
$$

Its full factor vector is injective. In either side column the two
root-leaf factors are distinct from each other and from all three
child factors.

A public family index consists of $b\in\mathcal G$, a leaf
$h\in\{A,B\}$, and $u\in\{A,B,b\}$. Let $f$ be the other leaf,
and let $\{v,w\}=\{A,B,b\}\setminus\{u\}$. The order of $v,w$
does not matter. Define

$$
\iota(\alpha)=A,\quad\iota(\beta)=B,\quad
\iota(\mathsf{branch})=b,\qquad
g(c)=\begin{cases}h,&\iota(c)=u,\\f,&\iota(c)\in\{v,w\}.
\end{cases}
\tag{SCP.27}
$$

There are exactly $9\cdot2\cdot3=54$ such indices. Each index
specifies a family at every integer $N\ge1$; the menu is fixed
independently of a weight law, an unknown source and a later target.

**Definition 8.3 (complete pinned and unpinned prescriptions).** For an
index and $N\ge1$ use the $2N$ ordered original blocks
$T_1,Y_1,\ldots,T_N,Y_N$. Seed $c_i$ is owned at the actual root
of $T_i$, with domain $\{\alpha,\beta,\mathsf{branch}\}$. Seed $s_i$
is owned at the actual root of $Y_i$, with domain $\{\alpha,\beta\}$.
Identify a leaf-valued $s_i$ with that actual leaf only in the formulas
below. Prescribe all three factors at $T_i$ by

$$
z_{T_i,q}=\Gamma_q(\iota(c_i))\qquad(q\in W_2).
\tag{SCP.28}
$$

The pinned network $\mathcal N_N$ prescribes at $Y_i$

$$
\begin{aligned}
z_{Y_i,\varnothing}&=\Gamma_{\varnothing}(s_i),&
z_{Y_i,L}&=\Gamma_L(g(c_i)),\\
z_{Y_i,R}&=\Gamma_R(s_{i+1})&& (i<N),\\
z_{Y_N,R}&=\Gamma_R(h).&&
\end{aligned}
\tag{SCP.29}
$$

The unpinned network $\mathcal N_N^0$ changes only the last
prescription, to $z_{Y_N,R}=\Gamma_R(s_N)$. The seeds, owners,
domains and incidence graph stay the same.

Here are explicit total native decoders for these networks. Every
occurrence of $c_i$ queries the actual root of $T_i$; every occurrence
of $s_i$ queries the actual root of $Y_i$. At each $T_i$ table send
the unused absent input to $\Gamma_q(A)$. At a $Y_i$ root table send
both unused branch and absent inputs to $\Gamma_{\varnothing}(A)$.
At every other table extend unused inputs by $\Gamma_q(A)$ for its
target $q$. Constants require zero Reads. On the declared domains,
the owner root factors have precisely their input replies. Off the
binary $Y_i$ domain the root equation has no fixed reply: branch
cannot equal the alpha reply of its prescribed factor, and absent
cannot be a root reply of any actual tree. Thus these are the total
guarded decoders of complete original native templates, denoted
$\Theta_N$ and $\Theta_N^0$, with no extra domain oracle.

**Theorem 8.4 (exact solutions, single defect and tree incidence).**
For every public index and every $N\ge1$,

$$
\begin{aligned}
C_{\Theta_N}&=\{x^h\},&
x^h&=(u,h,\ldots,u,h),\\
C_{\Theta_N^0}&=\{x^h\}\sqcup B_N,&
B_N&=\{(t_1,f,\ldots,t_N,f):t_i\in\{v,w\}\}.
\end{aligned}
\tag{SCP.30}
$$

In particular $|B_N|=2^N$. Every row of $B_N$ violates exactly
one of the $6N$ target prescriptions of $\Theta_N$, namely the last
$R$ prescription, and differs from $x^h$ in all $2N$ original
blocks. The block-seed incidence graph of either displayed network
is a connected tree on $4N$ vertices with $4N-1$ edges. Every seed
occurs in at most two distinct blocks and every block has degree at
most three.

Proof. By (SCP.26), the three equations at $T_i$ reconstruct exactly
$\iota(c_i)$. Its root reply is indeed $c_i$. The guarded root
equation at $Y_i$ forces that block to be the actual leaf $s_i$.
The two distinct leaf $L$ factors then give
$s_i=g(c_i)$. For $i<N$, the two distinct leaf $R$ factors give
$s_i=s_{i+1}$. The pinned final equation gives $s_N=h$.
Consequently all $s_i=h$ and all $\iota(c_i)=u$. Conversely that
tuple satisfies every equation. Without the pin, the common leaf
can also be $f$, and then each $\iota(c_i)$ may be $v$ or $w$.
The final unpinned equation is an identity. This proves both exact
solution descriptions, including exclusion of every other state in
the full eleven-state alphabet.

On a row of $B_N$, all pinned equations except the last agree with
the unpinned equations and hold. The last fails because
$\Gamma_R(f)\ne\Gamma_R(h)$. Also $t_i\ne u$ and $f\ne h$,
giving the stated block distance.

The edges are $c_iT_i$, $c_iY_i$, $s_iY_i$ for every $i$, and
$s_iY_{i-1}$ for $2\le i\le N$. These $4N-1$ edges connect all
$4N$ vertices: the $Y_i$ are linked successively by $s_{i+1}$,
and each $T_i$ and $s_1$ is attached to that chain. Hence the graph
is a tree, with the asserted degrees and distinct-block incidences.
Each compatible seed assignment has exactly one actual tuple and
vice versa, recovered from the actual owner roots. There are no
independent copies of a repeated reply. $\square$

## 9. Extensive sector selection and the three relative soft gaps

**Theorem 9.1 (exact joint boundary mass).** Let $\mu$ be any
probability on $S_2$ with positive masses on both leaves and on at
least one branch $b$. Other masses may be zero. In the public menu
choose $h$ to be a lighter leaf and $u$ to have minimum mass in
$\{A,B,b\}$, breaking ties arbitrarily. Put

$$
H=\mu(h),\quad F=\mu(f),\quad U=\mu(u),\quad
V=\mu(v),\quad W=\mu(w),\qquad
R=\frac{F(V+W)}{HU}.
\tag{SCP.31}
$$

Then $H,F,U,V,W>0$ and $R\ge2$. With the original product
counting law on the $2N$ blocks, each whole-block weight used once,

$$
\begin{aligned}
Z_N:=Z_{\mathcal N_N}(\mu)&=(HU)^N,\\
\mu^{\otimes2N}(B_N)&=[F(V+W)]^N=Z_NR^N,\\
Z_{\mathcal N_N^0}(\mu)&=Z_N(1+R^N).
\end{aligned}
\tag{SCP.32}
$$

Under the actual unpinned Gibbs law $P_N^0$ this gives

$$
P_N^0(s_N=h)=\frac1{1+R^N},\qquad
-\log_2P_N^0(s_N=h)=\log_2(1+R^N).
\tag{SCP.33}
$$

Proof. Multiply the $2N$ block weights on $x^h$. On $B_N$,
sum the independently enumerated choices $t_i\in\{v,w\}$ in
the explicit set (SCP.30), giving $F^N(V+W)^N$. This enumeration
is a property of this displayed set, not an independence assumption
on general native fibers or on the common Gibbs law. The two sectors
are disjoint, and the event $s_N=h$ is exactly the first sector.
Finally $F\ge H$ and $V,W\ge U$, proving $R\ge2$. The choice of
an index selects one of 54 already specified public families. No
comparison of real weights is an operation supplied to an observer.
$\square$

**Corollary 9.2 (weighted completion congestion).** Any mathematical
Markov kernel sending every row of $B_N$ into the unchanged hard
solution set $C_{\Theta_N}$ has weighted preimage congestion $R^N$
at its only output, relative to that output's original product weight.
A uniform input on $B_N$ has $N$ bits of selector entropy and its
image has entropy zero.

Proof. Every row must be sent to $x^h$ with probability one. Thus
the incoming weighted mass at that point is $Z_NR^N$, whereas its
reference weight is $Z_N$. The $2^N$ different selector strings
give the entropy assertion. This kernel is an analytical completion
map, not a physical operation on the stationary source. $\square$

This is a loss of joint weighted mass, not an exponential lower bound
on the original retained alphabet. The unpinned relation has only two
boundary sectors; splitting it by $s_N$ uses just two names. The small
number of boundary values does not bound their conditional mass ratio.

**Theorem 9.3 (relative gaps for all three specified carriers).** Use
the same law, public family and pinned network as in Theorem 9.1.
For every $0<\varepsilon\le1$, Definition 4.1's actual-tuple carrier
and Definitions 3.1–3.2's uniform owner-kernel and floor carriers obey

$$
\begin{aligned}
Z^{\mathrm{def}}_{\Theta_N,\varepsilon}(\mu)
 &\ge Z_N(1+\varepsilon R^N),\\
Z^{\mathrm{ker},\varepsilon}_{\mathcal N_N}(\mu)
 &\ge Z_N\left(1+\frac{\varepsilon}{2F}R^N\right),\\
Z^{\mathrm{fl},\varepsilon}_{\mathcal N_N}(\mu)
 &\ge Z_N\left(1+\frac{\varepsilon}{F}R^N\right).
\end{aligned}
\tag{SCP.34}
$$

For each of these three fixed carriers $\star$,

$$
\liminf_{N\to\infty}\frac1{2N}
 \log_2\frac{Z_N^\star(\varepsilon;\mu)}{Z_N}
 \ge\frac12\log_2R\ge\frac12.
\tag{SCP.35}
$$

The same lower limit holds along dyadic $N$. At the credited NCM
law $\mu(A)=\mu(B)=8/25$, $\mu(g)=1/25$ for every $g\in\mathcal G$,
choose $u=b$ and either $h$. Then $R=16$, so the right side of
(SCP.35) is two bits per original block.

Proof. Hard solutions contribute $Z_N$ to every carrier. Each
actual row of $B_N$ has exactly one violated prescription, so its
contribution to the defect carrier is its original weight times
$\varepsilon$. This proves the first bound.

For the seed carriers retain exactly the owned seeds of Definition
8.3. On the seed assignments of the free sector, all $T_i$
potentials are $\mu(t_i)$ and all $Y_i$ potentials except the last
are $F$. The final prescribed vector has root $f$, left factor
$\Gamma_L(f)$ and right factor $\Gamma_R(h)$. No actual state
has that vector: the root fixes the leaf $f$, whose right factor
differs. Hence the final hard potential is zero. Its owned tuple is
the one binary root seed $s_N$, so its uniform owner kernel is
$1/2$; all $T_i$ owner kernels are $1/3$ and all other $Y_i$
owner kernels are $1/2$.

In the nonnegative softened product, choose the added term only
at this final block and choose the original terms at all other
blocks. Summing these terms over the free-sector seed assignments
gives $\varepsilon\mu^{\otimes2N}(B_N)/(2F)$ for the kernel
and $\varepsilon\mu^{\otimes2N}(B_N)/F$ for the floor. Their
assignments are disjoint from the hard assignment. All remaining
terms are nonnegative. This proves the other two bounds, with no
weight placed on a seed occurrence in addition to its original block.

For each fixed $\varepsilon>0$, each bound has the form
$1+aR^N$, with $a>0$ independent of $N$. Its logarithm divided
by $2N$ tends to $\frac12\log_2R$. Substitution of the credited
law gives $R=16$. $\square$

The proof allows zero masses outside $\{A,B,b\}$. Uniform kernel
softening makes its local seed tables strictly positive even then;
the defect carrier's weighted support remains
$(\operatorname{supp}\mu)^{2N}$. No assertion here replaces a
normalized kernel having zeros by a positive kernel. The kernel
conclusion is for the fixed uniform rule, not arbitrary rules whose
mass at the final owner value could shrink with $N$.

## 10. The optimized consequence for a mandatory relative gate

**Definition 10.1 (the precise same-template gate).** At $d=2$ let
$\mathcal T_2(n)$ consist of complete templates together with a
specified valid owned-seed representation on $n$ original blocks,
whose block-seed incidence graph is a connected tree and whose seed
incidence is at most two. The representation, domains, guards and
whole-block potentials are part of this description. For
$\star\in\{\mathrm{def},\mathrm{ker},\mathrm{fl}\}$, use respectively
the underlying template's actual-tuple carrier, its uniform
owner-kernel carrier, or its floor carrier. For a probability $\mu$
let $\mathsf{Rel}_\star(\mu)$ mean that there exists a function
$e_\mu:(0,1]\to[0,\infty)$ with
$\lim_{\varepsilon\downarrow0}e_\mu(\varepsilon)=0$ such that

$$
\frac1n\log_2\frac{Z^\star_{\mathcal N,\varepsilon}(\mu)}
                         {Z_{\mathcal N}(\mu)}
 \le e_\mu(\varepsilon)
\quad\text{for every }n,\ (\Theta,\mathcal N)\in\mathcal T_2(n)
\text{ with }Z_{\mathcal N}(\mu)>0.
\tag{SCP.36}
$$

No computability of $e_\mu$ is assumed. A mandatory-relative-gate
cap method is any sound native cap verifier for which every accepted
label $(2,\mu,C)$ with $C<1$ must also imply
$\mathsf{Rel}_\star(\mu)$ for one fixed chosen carrier. All other
proof rules are unrestricted, but there is no bypass of this gate
for an accepted $C<1$. Soundness retains NPC Definition 8.1's
universal bound for all original complete templates, not just trees.

**Theorem 10.2 (uniform failure and weight-optimized gate obstruction).**
For each of the three specified carriers, if $\mu$ gives positive
mass to both leaves and any branch, then
$\mathsf{Rel}_\star(\mu)$ is false. Every accepted cap of a method
in Definition 10.1 has $C\ge1$, even if all probability laws with
support zeros are permitted. Consequently such a method is not
optimizer-cofinal at the credited
$\sigma_2=\log_2(25/17)>0$.

Proof. For the first assertion select the public family of Theorem
9.1. Theorem 8.4 places it in $\mathcal T_2(2N)$ and its hard mass
is positive. By (SCP.35), (SCP.36) would force
$e_\mu(\varepsilon)\ge\frac12\log_2R\ge1/2$ for every
$\varepsilon>0$, contradicting its required limit.

To cover the complementary supports, the credited local native
sets [NCM, (NCM.15)][SCP-NCM] include

$$
H_A=\{A\}\cup\mathcal G,\qquad
H_B=\{B\}\cup\mathcal G,\qquad \{A,B\}.
\tag{SCP.37}
$$

Their local witnesses can also be read directly from (SCP.26).
The root target uses its own root reply. For $H_A$, a side's
absent reply decodes to that side's root-leaf $A$ factor, while
its three present child replies decode to the corresponding
$\gamma$ value; $H_B$ is identical with $B$. On $\{A,B\}$ all
targets decode from the own root reply. Their products therefore
have complete native witnesses at every length.

If either leaf has zero mass, the support of $\mu$ is contained
in $H_A$ or $H_B$. If both leaves have positive mass but no branch
does, the support is contained in $\{A,B\}$. In every case one
displayed local set has mass one. Its products have mass one at
every length, and saturation by complete templates cannot reduce
that mass. Thus $\beta_2(\mu)=1$: the reverse inequality follows
because these are subsets of a probability space. Soundness forces
$C\ge1$ for such a law. At every remaining law the mandatory gate
is false by the first assertion, forbidding acceptance with $C<1$.
All accepted block lower endpoints $-\log_2C$ are consequently
at most zero, proving the cofinality failure. $\square$

**Convention 10.3 (scope of the rejected mechanism).** This conclusion
is not a characterization of the existing recursive, range-separation,
joint, scaffold, stability or conditional-owner certificate rules.
Those rules are not defined to impose (SCP.36). In particular the
positive all-size verifier obligation of Definition 6.1 does not
require a small relative error for each individual hard template.
Theorems 3.3 and 4.2 compare all-size suprema additively, and
Proposition 5.1 remains valid after weight optimization. None is
contradicted by (SCP.35).

The rejected gate asks for a vanishing normalized relative error
uniform in both template and length. It fails even with nonempty
hard solutions, a vanishing fraction $1/(6N)$ of violated targets,
a tree incidence graph, positive uniform soft tables and a
two-valued actual boundary. A bound on the boundary alphabet or on
defect density alone cannot supply this premise. No obstruction to
global recoloring, lawful recuts, a comparison between different
templates, all-boundary-sector summation, unrestricted effective
caps or computability is inferred. Nor does this depth-two gate
obstruction rule out another original-rate method using other depths.

## 11. Paid realization on the full original source family

**Theorem 11.1 (an actual full-family acquired code).** Fix any public
index, let $N=2^j$, $j\ge0$, and put $H_{\rm sc}=j+1$,
$D=H_{\rm sc}+2$. In the right subtree use a public perfect binary
scaffold of height $H_{\rm sc}$, placing the $2N$ ordered blocks at
its frontier words $a_1,\ldots,a_{2N}$. The actual original roots
are $Ra_i$. Let $\widehat B_N\subseteq S_D$ be the resulting
canonical right subtrees for $B_N$. There is a deterministic
source-blind preparation and a jointly correct reader on every
$t\in\mathcal F_D$ whose complete attained alphabet is exactly

$$
|S_D|-2^N+1.
\tag{SCP.38}
$$

Preparation makes $2^D-1$ charged Reads on every source, at maximum
address length $D$, submitting $(D-1)2^D+1$ letters. Each late
target uses zero Reads or one actual original-root Read of length
at most $H_{\rm sc}+1$, before every supplied count. This is a
deliberately nonoptimal construction, with no new optimized memory
bound asserted.

Proof. Every inserted block has height at most two. The scaffold
therefore gives actual trees of right-subtree height at most $D$,
and ordered parsing embeds the $2^N$ distinct tuples injectively
in $S_D$. Install a finite public assignment merging precisely
$\widehat B_N$ into one name and assigning a distinct name to every
other canonical state. This assignment is generated from explicit
finite trees and contains no acquired source data.

On the unknown actual $t=\langle\alpha,v\rangle$, before the
request, Read every literal $Rq$, $q\in W_D$, including absent
replies, in a fixed public order. These paid replies determine the
credited canonical completion $\pi_D(v)$. At depth $D-1$ a branch
is completed by $C_0$; all earlier constructors and leaves are
retained. [FMR, Lemma 2.2][FMR] preserves every requested full
factor and every boundary reply, including variable shapes. Export
only the fixed-width public name of $\pi_D(v)$. Every canonical
state is an actual possible right subtree and is fixed by $\pi_D$,
so every stated name is attained. Merging exactly $2^N$ canonical
states gives (SCP.38).

At a singleton name every requested factor is installed and no
late Read is needed. At the merged name, targets strictly above
the frontier have constant branch factor. Every remaining target
has the form $p=Ra_iq$, $q\in W_2$, because
$|p|\le D=1+H_{\rm sc}+1$. Use the unpinned prescriptions
(SCP.28)–(SCP.29), with its final own-root prescription, which
are valid on $B_N$. A selector target queries the actual root
of its $T_i$. A $Y_i$ target queries its own root for its root
factor, $T_i$'s root for its left factor, the next $Y$ root for
its right factor if $i<N$, and its own root for the final right
factor. A target known constant on the named subset may instead
use zero Reads. Each chosen query is one literal $Ra_l$ fixed
by the name, $D$ and $p$ before its reply and any count. Its
length is $H_{\rm sc}+1$.

The original occurrences are actually present in every source in
the merged inverse-image fiber. The exact presence premise of
`original_present_transport` in [NativeDepthPatterns][SCP-Depth]
therefore gives

$$
r_{\rho^kt}(Ra_iq)
 =r_{\rho^k(t|_{Ra_i})}(q)\qquad(k\ge0).
\tag{SCP.39}
$$

This subtree notation identifies an actual occurrence mathematically;
every executed query is an original-root literal. Canonicalization
preserves the queried root reply and requested factor on the whole
inverse-image fiber, so the installed decoder recovers
$\Gamma_p(t)$. The credited temporal predictor then answers
$r_{\rho^kt}(p)$ for every authentic subsequently supplied $k$,
with no further Reads. In particular initially absent suffixes
remain among the targets. No boundary selector or supplied count
is used to choose the query.

The scan contains $2^D-1$ literals and its submitted length is
$\sum_{\ell=0}^{D-1}(\ell+1)2^\ell=(D-1)2^D+1$.
It terminates on every source, independently of the later target.
Use public allocation, a fixed scan schedule and padded finite
membership computation. Under the declared paid handoff and
isolation services, all scanned arrays, selectors, buffers,
preparation control, allocation and timing distinctions beyond the
exported name are inaccessible at reader entry. The complete
attained alphabet is consequently the displayed name set.
These services are premises, not physical erasure deductions.
$\square$

This construction uses the credited FMR/RRN paid realization; its
additional content is the explicit fiber $B_N$ and its witnesses.
It replaces acquisition and does not preserve a rival preparer's
cost. The full source is always the original stationary
$t=\langle\alpha,v\rangle$. There is no acquired free reference,
extra readable root, subtree, equality, copying, reset, age,
navigation or identity port. The public scaffold is part of the
named slice, not a restriction on all original sources: all other
canonical states and all variable-shape inverse images are served
by the same preparation and reader.

Preparation work/control, temporary scan space, finite table
generation and installation, membership work, post-request
workspace, final predictor size, submitted literal resources,
authentic count representation, authentication, entry, source
continuity, handoff, isolation and physical time remain separate
resources. A fixed-width name needs
$\lceil\log_2(|S_D|-2^N+1)\rceil$ bits. No free total-efficiency
or physical mutual-recovery conclusion follows.

**Proposition 11.2 (ordinary request exposing an invalid promotion).**
If a row of the actual $B_N$ fiber is falsely treated as satisfying
the pinned final constant prescription, the legal request
$p=Ra_{2N}R$ and subsequent authentic count $k=1$ distinguish the
prescribed answer from the actual one.

Proof. The $Y_N$ block in that actual row is $f$, whereas the
pinned constant uses $h$. The request has length
$1+H_{\rm sc}+1=D$ and starts with $R$. The exact temporal
factors in (SCP.26) give

$$
\operatorname{Pred}(\Gamma_R(A),1)=\mathsf{absent},\qquad
\operatorname{Pred}(\Gamma_R(B),1)=\alpha.
\tag{SCP.40}
$$

Since $h,f$ are opposite leaves, the two answers differ. Presence
transport (SCP.39) identifies this with the original source request.
The code in Theorem 11.1 uses the correct unpinned witnesses;
this is a conditional test of an invalid promotion, not a failure
of that code or a claim about existing certificate rules. $\square$

## 12. Primary sources and finite exact readings

**Convention 12.1 (credited mathematics and transfer limits).** The
ordinary deductions in §§8–11 are repository-derived: the 54 public
families, their exact weighted sectors, the three relative lower
bounds, and the mandatory-gate consequence including support zeros.
Finite sum-product conditioning and weighted preimage counting are
mature methods. No worldwide originality claim is attached.

| Supplier | Exact use and boundary |
| --- | --- |
| [NCM, (NCM.14)–(NCM.16), Theorem 4.1][SCP-NCM] | The actual eleven-state factor table, local sets, credited law and value $\sigma_2=\log_2(25/17)$. The relative obstruction does not change that optimized value. |
| [RRN, Theorems 5.2 and 7.1][RRN], [CBN, §§2, 6–7][CBN] | Actual-owner guards, unique actual reconstruction, once-owned weights and paid scans. The explicit solution proof in Theorem 8.4 supplies the shared realization here. |
| [NPC, Definition 8.1][NPC], [COK, §9][SCP-COK], [GDB, §11][SCP-GDB] | The unchanged universal-cap and optimized-cofinality questions. Their obligations are not supplied by a relative gate or a finite tuple check. |
| [FMR, Lemma 2.2 and Theorems 2.3–2.5][FMR] | Paid canonical acquisition and all-variable-shape factor preservation, used with an explicitly assigned full-family code. |
| Vontobel, *Counting in Graph Covers: A Combinatorial Characterization of the Bethe Entropy Function*, [version 2, Theorems 25 and 30][SCP-Vontobel] | Rational local pseudo-marginals are realizable in some finite cover, and Bethe entropy describes the exponential average cover-preimage count. The cover may change the network and length; these statements do not give same-template weighted completion or an upper cap over every native network. |
| Ruozzi, *The Bethe Partition Function of Log-supermodular Graphical Models*, [Theorem 4.1 and Corollary 4.2][SCP-Ruozzi] | A binary log-supermodular factorization gives $Z(H)\le Z(G)^k$ for a $k$-cover and a Bethe lower bound on $Z(G)$. Neither log-supermodularity for arbitrary native joint tables nor the needed all-template upper direction is established here. |
| Brakensiek, Ciardo, Guruswami, Potechin and Zivny, *New Algorithms and Hardness Results for Robust Satisfiability of (Promise) CSPs*, [version 1, Theorems 1.2–1.3][SCP-PCSP] | The stated MAJ and PLUR promises give robust satisfaction guarantees. A fraction of weak constraints satisfied is a different target from exact weighted solution mass in the same native template. No native polymorphism or weighted-completion transfer is assumed. |

These checked primary hypotheses do not supply the missing unrestricted
native cofinal cap. This is a bounded transfer assessment, not a claim
that such a theorem does not exist. The finite-reader synthesis
criterion in [FCS, Theorem 6.1][SCP-FCS] instead constructs some
lawful code for its fixed finite installed reader using already
acquired terms and a different predecessor-row target. Its
Theorem 10.2 concerns verification of independently prescribed
acquired-term programs. Neither supplies an original all-length cap
or the bounded native preparer in Theorem 11.1; that preparer is
specified and paid directly above.

**Convention 12.2 (bounded exact checks).** The following are finite
exact in-memory readings, with rational arithmetic. No experimental
program or data is retained in this repository.

| Finite domain | Exact reading |
| --- | --- |
| All 54 indices, $N=1$, all $121$ actual pairs per index | $6,534$ pair/index tests: each pinned relation is the asserted singleton, each unpinned relation its asserted three rows, and each free row has one violation. |
| $b=C_0,h=A,u=b$, $N=1,2$, all $S_2^{2N}$ | Respectively $121$ and $14,641$ actual tuples; pinned counts $1,1$, unpinned counts $3,5$; hard masses $8/625$ and $64/390625$ at the credited law. |
| Same index, $N=1,2,4,6$, all displayed $B_N$ rows | Respectively $2,4,16,64$ one-defect rows at block distance $2N$, with exact mass ratios $16,256,65536,16777216$; graph counts $4N$ vertices and $4N-1$ edges, connected and seed incidence at most two. |
| Same index, $N=1,2$, $\varepsilon=1/10$ | Exhaustive actual-tuple defect sums and exhaustive $6^N$ seed sums satisfy all three bounds in (SCP.34). Kernel sums are $761/7500$ and $1023721/56250000$; floor sums are $301/1250$ and $124901/1562500$. |
| Support-zero law $\mu(A)=\mu(B)=1/4$, $\mu(C_0)=1/2$, zero elsewhere | With $h=A,u=A,N=2$, the exact sector ratio is $9=3^2$, as in (SCP.31)–(SCP.32). |
| Theorem 11.1 at $N=1,b=C_0,h=A,u=C_0$, all of $\mathcal F_3$ | All $1,446$ original variable-shape sources give $123$ canonical states and exactly $122$ complete attained names. All seven requests and authentic counts $0,\ldots,6$ agree with direct substitution/readout in $70,854$ comparisons. The explicit scan has seven Reads, maximum length three and seventeen letters. |

The all-$N$, all-law and all-count assertions rest on the proofs,
not extrapolation from these finite domains. These checks are not
Lean verification, independent review or an empirical convergence
claim.

## 13. The remaining joint relation

**Open problem 13.1 (avoid or pay the joint sector loss).** A proposed
same-template completion must control the joint conditional partition
ratio, not just the number of boundary values, small defect density,
local compatibility or tree incidence. In this explicit family its
exact extra cost is

$$
-\log_2P_N^0(s_N=h)=\log_2(1+R^N),
\tag{SCP.41}
$$

which is extensive in the number of original blocks. A global cap
may avoid this relative comparison, sum all boundary sectors, or
use a different full joint relation. Such a method still needs a
sound effective all-size bound retaining actual shared owners,
guards, support zeros and every whole-block potential once, together
with optimizer-cofinality for the unchanged $\sigma_d$ or a
uniform effective native length error. Neither obligation is
constructed or disproved here.

The original sharp $\lambda$, general exact $M_1(D)$, terminating
two-sided approximation and full minimal-relations/internal-observer/
mutual-recovery programme remain open. No numerical frontier update
is asserted. Under the paid services the operational recovery proved
here is only the requested full temporal factor from the complete
name, public request and at most one actual reply, followed by every
authentic-count readout. It does not recover an arbitrary whole
source, an unknown age, hidden history or physical space and time.

[SCP-COK]: https://github.com/the-omega-institute/trureturing/blob/91170b89dfe9dd7eadc64d14d86d2157ed14abdf/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONDITIONAL_OWNER_KERNELS.md
[SCP-GDB]: https://github.com/the-omega-institute/trureturing/blob/91170b89dfe9dd7eadc64d14d86d2157ed14abdf/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GLOBAL_DEPENDENCE_BOUNDARIES.md
[SCP-NCM]: https://github.com/the-omega-institute/trureturing/blob/91170b89dfe9dd7eadc64d14d86d2157ed14abdf/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CORRELATED_MEMORY_LOWER.md
[SCP-Depth]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[SCP-FCS]: https://github.com/the-omega-institute/trureturing/blob/91170b89dfe9dd7eadc64d14d86d2157ed14abdf/docs/develop/theory/FIB_NATIVE_FINITE_READER_CODE_SYNTHESIS.md
[SCP-Vontobel]: https://arxiv.org/html/1012.0065v2
[SCP-Ruozzi]: https://arxiv.org/html/1202.6035
[SCP-PCSP]: https://arxiv.org/html/2602.10368v1

## 追加锚（本行以下为增补区）
