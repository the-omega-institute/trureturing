# FIB-ATOM original-boundary finite-specimen access to native readout

This standalone source fixes the operational cut left open by [Continuation IV,
§§112--113](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md).
The source is still the full finite free ordered algebra, with its actual
substitution, INITIAL target, four-valued Read, history-dependent guard,
complete record and absorbing Stop.  The new input is a conditional quantum
installation of the already defined boundary value.  It is not a new source
algebra, a new equality oracle, or a derivation of quantum principles.

## 1. The operational quantum cut

### 1.1 The retained original contract

**Definition 1.1 (ambient source, authentic branch entry and complete native
service).** Let $\mathcal T$ be the entire free ordered algebra of Definition
113.1, with $\rho$, all occurrence addresses and the four replies
$\{\mathsf{alpha},\mathsf{beta},\mathsf{branch},\mathsf{absent}\}$ from
ActualTreeReadoutAcquisition.  The authentic branch-entry service has the
domain

$$
\mathcal B=\{\langle x,y\rangle:x,y\in\mathcal T\}\subseteq\mathcal T
$$

and retains the IV112 root record
$H_0=[(0,\varepsilon,\mathsf{branch})]$.  Thus, for $u\in\mathcal B$, a
source enters with the root branch record of the authentic entry.  The
singleton ambient sources $\alpha$ and $\beta$ remain in $\mathcal T$ with
their own leaf-root replies and no reached $L/R$ holes; they are not silently
treated as branch entries and are handled only in the explicitly qualified
singleton cases below.  For $u\in\mathcal B$, the full INITIAL target at
$Q=(L,R)$ is the required output of Definitions 112.1 and 112.2, not a
supplied source-dependent tag: it retains the two numbered holes, the
complete exterior and the partition of holes by equality of their original
subtrees.
An attempted
Apply has the common guard $G(\gamma,e,H)$ of Contract 112.1a, where $e$ is
the accepted epoch and $H$ is the complete chronological Read/status
history.  Acceptance replaces the source by $\rho u$; refusal leaves it
unchanged.  A Read is a real event, including repeats and absent addresses.
Stop is absorbing and executes no suffix.  These records, the guard, the
common apparatus and the reference are part of the service contract.

On this branch-entry domain, the complete native service means a finite
history-only operation word may perform every lawful Read and every
continuation required by this contract.
In particular, the epoch-zero root-first frontier of Definition 112.9 may
read every reached node and restore the exact finite ordered source before
any optional Apply.  The source itself, its phase, $W(u)$, a future specimen,
or a permission answer is never supplied as a free controller input.

### 1.2 Conditional boundary states

**Definition 1.2 (the finite-specimen input cut).** Reuse the Bernoulli
probability $M$ and the positive density

$$
f_u=\frac{d\nu_u}{dM}
$$

of Definition 113.3.  Conditionally install the complex Hilbert space
$\mathcal H_B=L^2(M;\mathbb C)$ and the normalized vector

$$
\psi_u(s)=\sqrt{f_u(s)},
\qquad \|\psi_u\|_2^2=\int f_u\,dM=1.
\tag{1.1}
$$

The principal input supplies exactly $m\ge1$ copies of

$$
\rho_u^{(m)}=|\psi_u\rangle\!\langle\psi_u|^{\otimes m}.
\tag{1.2}
$$

An exact classical $W$ register, a common entry record, apparatus and
reference $\tau$ may be supplied as additional tensor factors.  On a
same-scale comparison the $W$ register is the same state for every source,
and $\tau$ has no source dependence.  Every accessible source, archive,
memory, control or environment register is included in one finite-dimensional
side register $E$; its source-dependent state is denoted $\eta_u$.  Thus the
most general finite cut considered here is

$$
\widetilde\rho_u^{(m)}
=\rho_u^{(m)}\otimes\eta_u\otimes\tau.
\tag{1.3}
$$

The installation of $L^2(M)$, Born probabilities, complex amplitudes and
the preparation of (1.2) is an explicit conditional premise.  It is not a
consequence of the tree substitution, information conservation, the
relational spectrum or the original Read contract.  A classical exact
measure value is a mathematical object; a finite specimen of its square root
is a different input.  The source-step phase is not a complex phase.

**Lemma 1.3 (exact output requires orthogonal input supports).** Let
$\rho$ and $\sigma$ be density operators.  If one quantum instrument has
an outcome effect $0\le E\le I$ with

$$
\operatorname{tr}(E\rho)=1,
\qquad \operatorname{tr}(E\sigma)=0,
\tag{1.4}
$$

then $\operatorname{supp}(\rho)\perp\operatorname{supp}(\sigma)$.

Proof. Positivity gives
$\operatorname{tr}((I-E)\rho)=0$ and
$\operatorname{tr}(E\sigma)=0$.  Hence
$(I-E)^{1/2}\rho^{1/2}=0$ and $E^{1/2}\sigma^{1/2}=0$.
Therefore the support of $\rho$ is contained in the $1$-eigenspace of
$E$, while the support of $\sigma$ is contained in its $0$-eigenspace.
These eigenspaces are orthogonal.  A CPTP instrument followed by an exact
classical transcript is a special case of this effect argument. $\square$

## 2. An authentic equal-scale source family

### 2.1 The family inside the full domain

**Definition 2.1 (two ordered source constructors).** Put

$$
A=\langle\alpha,\beta\rangle,
\qquad B=\langle\beta,\alpha\rangle,
\qquad C_1=\alpha,
\qquad C_{n+1}=\langle C_n,\alpha\rangle,
\tag{2.1}
$$

and, for $n\ge1$,

$$
X_n=\langle C_n,A\rangle,
\quad Y_n=\langle C_n,B\rangle,
\quad U_n=\langle X_n,X_n\rangle,
\quad V_n=\langle X_n,Y_n\rangle.
\tag{2.2}
$$

These are actual members of the full branch domain of Definition 112.1.
They are not a replacement domain and do not add an equality query.

**Proposition 2.2 (composition, scale and native witness).** For every
$n\ge1$,

$$
a(U_n)=a(V_n)=2n+2,\qquad b(U_n)=b(V_n)=2,
\tag{2.3}
$$

and their total node count is

$$
S(U_n)=S(V_n)=4n+7.
\tag{2.4}
$$

Their common acquired scale is

$$
w_n=W(U_n)=W(V_n)=2n+2+2\varphi
    =2(n+\varphi^2),
\qquad \varphi=\frac{1+\sqrt5}{2}.
\tag{2.5}
$$

The INITIAL reached list at $Q=(L,R)$ and its exterior are the same for the
two sources, while the equality partition is

$$
\Pi(U_n)=\{\{1,2\}\},
\qquad
\Pi(V_n)=\{\{1\},\{2\}\}.
\tag{2.6}
$$

At epoch zero the genuine Read at address $RRL$ returns

$$
\operatorname{Read}_{U_n}(RRL)=\mathsf{alpha},
\qquad
\operatorname{Read}_{V_n}(RRL)=\mathsf{beta}.
\tag{2.7}
$$

Proof. $C_n$ has $n$ alpha leaves and $2n-1$ nodes.  Each of $A,B$ has
one alpha leaf, one beta leaf and three nodes.  The free ordered constructor
therefore gives (2.3)--(2.5), with $2(2n+3)+1=4n+7$ nodes.  The right
child of the root is $X_n$ in $U_n$ and $Y_n$ in $V_n$; the next right step
reaches $A$ or $B$, and the final left step reads alpha or beta.  The two
child subtrees are otherwise the same, giving (2.6). $\square$

### 2.2 What the square-root state retains

The density $f_u$ is the exact measure value of IV113, modulo
$M$-almost-everywhere equality.  It is already a merged cylinder function;
the unreduced leaf partition is not an additional input.  Equation (1.1)
retains precisely this merged value as one vector.  Appending $W$ restores
the scale-injective classical pair of Theorem 113.5 only when that exact
register is actually supplied.  It does not turn the finite specimens into
a classical function evaluator or provide a source-dependent partition tag.

## 3. Exact boundary geometry of the witness family

### 3.1 One exchanged ordered pair

**Lemma 3.1 (local square-root overlap).** Let $q$ be a fixed source
context and compare the two replacements $A$ and $B$ there, with all other
leaves unchanged and total common scale $w$.  On the two child cylinders of
$q$, the numerator values in (113.7) are

$$
\begin{array}{c|cc}
&[qL]&[qR]\\ \hline
A&\varphi^{s(q)+1}&\varphi^{s(q)+3}\\
B&\varphi^{s(q)+2}&\varphi^{s(q)+2}.
\end{array}
\tag{3.1}
$$

Their contribution to the Hellinger inner product
$\int\sqrt{f_Af_B}\,dM$ is $2\sqrt\varphi/w$, whereas the common scale
contribution is $\varphi^2/w$.  The deficit is therefore

$$
\delta/w,
\qquad
\delta=\varphi^2-2\sqrt\varphi=(\sqrt\varphi-1)^2>0.
\tag{3.2}
$$

Proof. The cylinder masses are $M([qL])=\varphi^{-s(q)-1}$ and
$M([qR])=\varphi^{-s(q)-2}$.  Multiplying each by the geometric mean of
the corresponding numerator values gives $\sqrt\varphi/w$ twice.  Every
unchanged cylinder contributes its common numerator divided by $w$; only
the exchanged pair has the deficit in (3.2). $\square$

**Theorem 3.2 (exact witness overlap).** For every $n\ge1$,

$$
\langle\psi_{U_n},\psi_{V_n}\rangle
  =1-\frac{\delta}{w_n},
\qquad
\|\psi_{U_n}-\psi_{V_n}\|_2^2
  =\frac{2\delta}{w_n}.
\tag{3.3}
$$

Proof. In (2.2) the sole changed ordered pair is the $A/B$ pair at the
common context $q=RR$.  Apply Lemma 3.1 with the common scale (2.5).
The vectors are positive real functions, so the inner product is the
Hellinger affinity and the squared distance is
$2-2\langle\psi_{U_n},\psi_{V_n}\rangle$. $\square$

### 3.2 A full source-family extension

**Corollary 3.3 (multiple fixed contexts).** Fix pairwise disjoint
ordered source contexts and replace $k$ of them by $A$ or $B$, leaving all
other leaves fixed with total scale $B_0$.  For
$\sigma,\tau\in\{A,B\}^k$, put $d=d_H(\sigma,\tau)$ and

$$
w=B_0+k\varphi^2.
\tag{3.4}
$$

Then all members have the same $W=w$, and

$$
\langle\psi_\sigma,\psi_\tau\rangle
=1-\frac{\delta\,d_H(\sigma,\tau)}{w}.
\tag{3.5}
$$

Proof. Each unchanged context contributes its common weight divided by
$w$, and each changed context replaces $\varphi^2/w$ by
$2\sqrt\varphi/w$.  Summing the $d$ deficits gives (3.5).  This is an
authentic finite source family in the original algebra; no unreduced leaf
partition is appended to the input. $\square$

## 4. Finite specimens versus deterministic Read

### 4.1 The strongest unrestricted binary benchmark

**Theorem 4.1 (exact finite-copy binary error).** Give $U_n$ and $V_n$
equal prior probability and allow an arbitrary joint POVM on the $m$ supplied
specimens (and the common $W$, apparatus and reference registers).  The exact
minimum average error is

$$
p_m(n)=\frac{1-\sqrt{1-(1-\delta/w_n)^{2m}}}{2}.
\tag{4.1}
$$

Proof. The overlap of the tensor powers is
$(1-\delta/w_n)^m$ by (3.3).  Let $\kappa$ be the common tensor factor
formed by the exact $W$ register, apparatus and reference, allowing the
reference $\tau$ to be mixed; $\kappa$ is a common density operator.  The
two inputs are
$\rho_{U_n}^{(m)}\otimes\kappa$ and $\rho_{V_n}^{(m)}\otimes\kappa$; since
$\operatorname{tr}\kappa=1$,

$$
\bigl\|(\rho_{U_n}^{(m)}-\rho_{V_n}^{(m)})\otimes\kappa\bigr\|_1
=\bigl\|\rho_{U_n}^{(m)}-\rho_{V_n}^{(m)}\bigr\|_1\,\|\kappa\|_1
=\bigl\|\rho_{U_n}^{(m)}-\rho_{V_n}^{(m)}\bigr\|_1.
$$

The equal-prior pure-state binary discrimination formula therefore gives
$p=(1-\sqrt{1-|\langle\psi,\phi\rangle|^{2}})/2$; this is the
Barnett--Croke result, [arXiv:0810.1970v1, §3.1, equation (12)](https://arxiv.org/html/0810.1970v1),
under its stated two-state and POVM assumptions.  Substitution yields
(4.1).  The displayed trace-norm identity shows that the common factor
leaves the Helstrom minimum unchanged even when $\tau$ is mixed. $\square$

This formula is used only for the bare cut with no source-dependent side
record, equivalently $\eta_{U_n}=\eta_{V_n}$.  A source-dependent record
changes the input overlap and is treated separately in §5.  The formula
does not assert that a native Read can implement the Helstrom effect, that
the copies can be prepared, or that a joint-control menu is available.

### 4.2 A quantitative nonuniformity law

**Corollary 4.2 (necessary copy count for a per-source error target).**
Let $0<\varepsilon<1/2$.  If a simulator's output on the promised pair
$\{U_n,V_n\}$ has Read error at most $\varepsilon$ for each source, then

$$
m\ge
\left\lceil
\frac{\log\!\bigl(1/[4\varepsilon(1-\varepsilon)]\bigr)}
{-2\log(1-\delta/w_n)}
\right\rceil.
\tag{4.2}
$$

For every finite $m$, $p_m(n)>0$.  For fixed $m$,

$$
\lim_{n\to\infty}p_m(n)=\frac12,
\qquad
\lim_{n\to\infty}\frac{m_{\min}(n,\varepsilon)}{w_n}
=\frac{\log\!\bigl(1/[4\varepsilon(1-\varepsilon)]\bigr)}{2\delta},
\tag{4.3}
$$

where $m_{\min}$ denotes the real-valued threshold in (4.2) before the
ceiling.

Proof. Per-source error at most $\varepsilon$ implies average error at most
$\varepsilon$, so (4.1) gives
$\sqrt{1-(1-\delta/w_n)^{2m}}\ge1-2\varepsilon$.  Squaring and rearranging
gives $(1-\delta/w_n)^{2m}\le4\varepsilon(1-\varepsilon)$, which is
(4.2).  Positivity of $\delta$ gives strict positive error at every finite
$m$.  The first limit follows from $w_n\to\infty$; the second uses
$-\log(1-x)\sim x$. $\square$

### 4.3 Native bill and the meaning of the obstruction

**Proposition 4.3 (the same promise is natively exact).** Under the
original source service, a Read at $RRL$ distinguishes the promised pair
with zero error, zero Applies and literal address length $3$.  If the retained
entry root is counted together with this post-entry event, the chronology has
two raw Read events and two distinct addresses; if only post-entry calls are
charged, it has one raw event and one fresh address.  These are the declared
cache scopes of (112.20a), not a new tariff.

The proposition compares an actual native event with a finite-specimen
quantum benchmark.  It does not claim that the quantum copies have a native
preparation cost, a source-dependent oracle, a reset, cloning, a backward
action, or a conversion from specimen number to the original bill.  It also
does not turn the binary promise into equality recovery on all of
$\mathcal T$: a two-source separation is weaker than a complete-domain
Read algorithm.

## 5. Exact complete service and the side-record capacity

### 5.1 The whole fixed-composition fiber

**Definition 5.1 (the unreduced fiber and an exact complete service).**
For integers $a,b\ge0$ with $\ell=a+b\ge1$, let

$$
D_{a,b}=\{u\in\mathcal T:a(u)=a,\ b(u)=b\}.
\tag{5.1}
$$

This is the entire ordered source fiber in the ambient algebra, including
every binary shape and every ordered leaf labeling.  When $\ell\ge2$, every
member is in $\mathcal B$, so the existing
GenealogicalFiberTransport result supplies

$$
K_{a,b}=|D_{a,b}|
=\operatorname{Catalan}_{\ell-1}\binom{\ell}{a}.
\tag{5.2}
$$

An exact complete service for a nondegenerate fiber ($\ell\ge2$) is one
common CPTP/instrument family that, from (1.3), returns every requested
original four-valued Read and continues with the same actual guard, Apply
rule, chronological records and absorbing Stop.  It must therefore support
the finite epoch-zero traversal that reads the root and every reached node.
The traversal's replies encode the ordered source uniquely; it is the same
paid acquisition supplier used in Theorem 112.10, not a free source index.
For $\ell=1$, the fibers are the singleton cases
$D_{1,0}=\{\alpha\}$ and $D_{0,1}=\{\beta\}$, with $K_{a,b}=1$; their
authentic entries are the leaf-root services just stated, and no $Q=(L,R)$
branch target is asserted for them.

### 5.2 Orthogonality forced by complete native reading

**Theorem 5.2 (source-dependent orthogonal side record is necessary).**
For a nondegenerate fiber $\ell\ge2$, assume the finite-specimen input on
$D_{a,b}$ has the form

$$
\widetilde\rho_u^{(m)}
=|\psi_u\rangle\!\langle\psi_u|^{\otimes m}
 \otimes\eta_u\otimes\tau,
\tag{5.3}
$$

where $\tau$ is source-independent and $E$ is a common finite-dimensional
side register containing every source-dependent accessible record.  If an
exact complete service exists, then

$$
\operatorname{supp}(\eta_u)\perp\operatorname{supp}(\eta_v)
\quad(u\ne v),
\qquad
\dim E\ge K_{a,b}.
\tag{5.4}
$$

Proof. The densities in (113.7) are strictly positive on every terminal
cylinder and those cylinders partition $\Omega$; hence

$$
\langle\psi_u,\psi_v\rangle=\int\sqrt{f_uf_v}\,dM>0
\quad\text{for all }u,v\in D_{a,b}.
\tag{5.5}
$$

Run the exact epoch-zero traversal. Its classical transcript is different
for every different ordered source because the four-valued address replies
recover every constructor and label.  By Lemma 1.3, the complete input
supports for two distinct sources must be orthogonal.  The support of (5.3)
is

$$
\operatorname{span}\{\psi_u^{\otimes m}\}\otimes
\operatorname{supp}(\eta_u)\otimes\operatorname{supp}(\tau).
\tag{5.6}
$$

The first factors for $u$ and $v$ have positive inner product by (5.5).
If the two side supports were not orthogonal, choose side vectors with a
nonzero inner product; their tensor products in (5.6) would then have a
nonzero inner product, contradicting exact output orthogonality.  Thus all
$K_{a,b}$ nonzero side supports are pairwise orthogonal, so their dimensions
sum to at least $K_{a,b}$ and $\dim E\ge K_{a,b}$.  The common factor $\tau$
cannot alter this conclusion. $\square$

**Corollary 5.3 (the no-side-record and degenerate cases).** If
$K_{a,b}>1$, the bare boundary specimens with only source-independent
apparatus ($\dim E=1$) cannot implement exact complete native reading,
regardless of the number of finite copies.  If $K_{a,b}=1$, the bound is
vacuous: these are exactly the singleton fibers $D_{1,0}=\{\alpha\}$ and
$D_{0,1}=\{\beta\}$, whose leaf-root reply already identifies the sole
source and which have no $L/R$ branch ambiguity.  Thus the blanket statement
that every fiber with $\ell\ge2$ fails at $d=1$ requires this $K_{a,b}>1$
qualification.  In the witness family, $K_{2n+2,2}>1$, so the qualification
is always active.

### 5.3 Conditional attainment and its price boundary

**Proposition 5.4 (mathematical attainment by an orthogonal label).**
Conditionally let $E=\mathbb C^{K_{a,b}}$ and choose an orthonormal basis
$\{|u\rangle:u\in D_{a,b}\}$.  Supplying

$$
\eta_u=|u\rangle\!\langle u|
\tag{5.7}
$$

attains the dimension bound mathematically: measure the label, restore the
ordered source description, and run the corresponding native
Read/Apply/guard/Stop contract (the branch-entry contract for $\ell\ge2$ and
the leaf-root contract for the singleton fibers).  This construction assumes
the label's preparation, storage,
protection and control and says nothing about their physical availability,
runtime, energy, clock conversion or total acquisition price.  It is a
full-history/orthogonal-source dilation, not a realization of the bare
boundary specimen cut.

## 6. Correspondence classification and remaining boundary

**Specification 6.1 (what this result establishes).** The square-root
encoding has the following precise status.

1. The exact classical pair $(\nu_u,W(u))$ remains an injective attained-image
   representation and can be evaluated after the original paid acquisition of
   $u$ described in Proposition 113.9.  The evaluation retains the complete
   INITIAL row, all four replies, guards, Apply statuses, chronological
   records and absorbing Stop.
2. On the supplied finite-specimen cut, the authentic family (2.2) has the
   exact nonzero overlaps (3.3).  Even the unrestricted joint POVM has the
   finite-copy error (4.1), and the fixed-$m$ error is nonuniform over this
   source family.  Therefore finite bare specimens cannot provide the exact
   native Read on that promise, with its original zero-error event and bill.
3. Exact complete reading on an entire nondegenerate fixed-composition fiber
   ($\ell\ge2$) requires a source-dependent orthogonal side record of
   dimension at least (5.2).  For the singleton fibers $D_{1,0}$ and
   $D_{0,1}$, $K_{a,b}=1$ and the bound is vacuous; their native leaf-root
   service has no $L/R$ branch target.  Supplying such a record changes the
   input cut; it does not prove that the bare boundary marginal is
   insufficient for every possible quantum model.
4. A coherent quantum instrument, a purification carrying the source, an
   exact equality register, or a full-history dilation must be stated as an
   additional source-bearing resource.  None is silently identified with the
   vector (1.1).  Born's rule, complex Hilbert structure, CPTP control and
   quantum preparation remain hypotheses.

The result is a boundary-access theorem for the original IV112--113 source
contract.  It neither derives quantum principles from substitution nor
completes the quantum-origin objective.  Binary promise discrimination,
complete equality recovery on the whole source domain, and recovery after an
orthogonal side-record installation are three different obligations.

### 6.1 Reused suppliers and bounded literature correspondence

The all-occurrence counting boundary, exact scale reconstruction, source-step
action and INITIAL/service contract are reused from Continuation IV,
Definitions 112.1--112.10 and 113.1--113.10.  The ordered-fiber count is the
existing D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean result;
the four-valued readout and paid traversal are owned by
D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean.  The exact
support implication is aligned with the existing pure-state effect result in
D5/S3/Quantum/PureState/PerfectEffectDiscriminationOrthogonality.lean; no
new Lean declaration is asserted here.  Barnett--Croke,
[arXiv:0810.1970v1, §3.1, equation (12)](https://arxiv.org/html/0810.1970v1),
is used only for the unrestricted two-state POVM benchmark.  The existing
Watrous library entries supply the standard density-operator/CPTP background.
None of these sources supplies a native specimen preparation, a free source
oracle, or the original physical permission and charge.

The positivity argument uses the actual finite terminal-cylinder density of
IV113, so it does not assume a uniform source family or replace the original
domain by the witnesses.  The finite-copy law is an exact conditional
benchmark, not a claim about a physical optimum.  Preparation, storage,
joint control, coherent phase reference, source-bearing purification, native
clock, actuator and all unpriced physical resources remain open premises.
The theorem also leaves open quantum models whose input includes additional
orthogonal source information; it only classifies the stated bare-boundary
cut and the explicitly bounded side-record extension.

## 追加锚（本行以下为增补区）
