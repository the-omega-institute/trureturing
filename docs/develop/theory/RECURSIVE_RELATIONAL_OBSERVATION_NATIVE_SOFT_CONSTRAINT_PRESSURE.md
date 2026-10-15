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
For positive uniform $\varepsilon$, every assignment in a nonempty
seed-domain network has strictly positive local tables; empty-domain
networks still have value zero.

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
Then

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
probabilities; positive rational $\varepsilon$ can be used in the
strictly positive models. A rational cap may always be rounded upward
after a semantic cap is established.

**Proof.** Approximate inside the finite support simplex. In the defect
carrier, every length-$n$ product mass gains at most
$(1+\delta)^n$. In the seed carriers, each baseline potential gains at
most $(1+\delta)$, and
$\Phi+\Psi\le(1+\delta)(\Phi+\Psi)$ because $\Psi$ is independent of
$\mu$. Take $n$th roots and the all-size supremum. $\square$

The bounds (SCP.19) are semantic all-size statements. Finite evaluation
at a chosen length is only a lower approximation to a soft pressure; it
does not provide a length cutoff or a cofinal upper certificate.

## 6. The positive-model obligation and the near-one boundary

**Definition 6.1 (remaining positive verifier obligation).** A positive
cap verifier at fixed $(d,L)$ is a total computable predicate

$$
V^\star(d,L,\mu,\varepsilon,C,\pi)
$$

on rational $\mu$, rational $\varepsilon>0$, positive rational $C$, and
a finite certificate string $\pi$. Soundness requires acceptance to
prove, for every $n$ and every network in the same owned-seed class,

$$
Z^\star_{\mathcal N}(\mu,\ldots,\mu)\le C^n,
\tag{SCP.21}
$$

with the selected carrier $\star\in\{\mathrm{ker},\mathrm{fl},\mathrm{def}\}$
and its exact hypotheses. For $\star=\mathrm{ker}$ or $\mathrm{fl}$ the
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

