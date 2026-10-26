# Recursive relational observation: the Gaussian adaptive record kernel

This continuation isolates one source-specific relation left open by the
Gaussian volume. The old $JM$ records, the common specimen and the actual
positive-width pointer service are kept together. The result is an
instrument-to-transcript correspondence for causal finite policies and for
their countable mathematical path extension, followed by a conservative
binary status floor. It is a record-law result for the changed post-$JM$
menu; it is not a four-view recovery theorem or a physical implementation.
This is a `generic-v1` reference volume; its text is append-only.

The source is [FIB shared Gaussian instruments and indexed record-law
fibres](FIB_SHARED_GAUSSIAN_RECORD_LAWS.md), especially §§24--27 and
§§30--34. Its old records, common probes, covariance, and pre-supplement
target are reused at their stated hypotheses. The categorical decision volume
§9 concerns independently prepared repetitions; it is a different resource
model and is not used as a same-specimen argument here.

## 1. The common specimen and the lawful continuation menu

**Definition 1.1 (pre-supplement target and old record).** Fix one allowed
$W\in\mathcal W$, one finite pointer width $\sigma\in(0,\infty)$, and put
$r=(4\sigma^2)^{-1}$. For $\boldsymbol\eta=(\eta_A,\eta_B)\in[0,\infty)^2$,
use the preparation and the three chronological operations

$$
\mathrm{read}_0,\ J,\ \mathrm{read}_1,\ M,\ \mathrm{read}_2
$$

from [FIB shared Gaussian instruments and indexed record-law fibres,
Definition 26.1](FIB_SHARED_GAUSSIAN_RECORD_LAWS.md). The retained old record
is $Z=(Z_0,Z_1,Z_2)$, including the labels of the fixed $J,M$ controls. The
state whose status is reported is exactly the record-averaged marginal

$$
\widetilde\rho_{AB;\boldsymbol\eta}^{W,\sigma}
 =\operatorname{Tr}_{\rm rest}
 (\mathcal D_2\circ\mathcal U_M\circ\mathcal D_1
 \circ\mathcal U_J\circ\mathcal D_0)
 (\widetilde\rho_{W;\boldsymbol\eta}),
\tag{1.1}
$$

before any supplementary coupling. Its status is

$$
\mathsf s_r(\boldsymbol\eta)=
\begin{cases}
\mathsf S,&F_r(\boldsymbol\eta)\ge0,\\
\mathsf E,&F_r(\boldsymbol\eta)<0,
\end{cases}
\qquad
F_r(\eta_A,\eta_B)=(\eta_A+64r-2)(\eta_B+r)-1.
\tag{1.2}
$$

Here $\mathsf S$ means separable and $\mathsf E$ means NPT-entangled for
(1.1). Equality belongs to $\mathsf S$, as in Proposition 27.1 of the source.
The supplements may disturb the specimen, but they do not change the target
time in (1.1).

**Definition 1.2 (same-specimen positive-width pointer service).** After the
old $JM$ prefix, a continuation step has a finite nonzero row
$c=(c_A,c_B)\in\mathbb R^2\setminus\{0\}$ and a width
$\tau\in(0,\infty)$. It supplies one fresh independent Gaussian pointer with
position variance $\tau^2$, couples it by

$$
m_c=c_Ap_A+c_Bp_B,
\qquad U_{c}=\exp(-i m_c\otimes\Pi_c),
\tag{1.3}
$$

and retains its position readout $Y$. Thus the pointer momentum variance is
$1/(4\tau^2)$. Each pointer is used once. The service has no reset, fresh
specimen, momentum-changing control, $q$-to-$p$ feedback, access to an old
conjugate probe, or preparation-side record of $\boldsymbol\eta$. The rows,
widths, settings, calibration or reference identity, readouts, controller
seed, stopping decision and final report are retained whenever they are
executed or supplied to the consumer.

**Definition 1.3 (causal policies and finite transcripts).** Let $\omega$ be
an independent common-law seed in a standard Borel probability space
$(\Omega_0,\lambda)$. A policy $\pi$ is a measurable causal map whose input at
step $n$ is

$$
h_{n-1}=(Z,\omega,(c_1,\tau_1,Y_1),\ldots,(c_{n-1},\tau_{n-1},Y_{n-1})).
$$

It either stops and emits a report in $\{\mathsf E,\mathsf S\}$, or selects
$(c_n(h_{n-1}),\tau_n(h_{n-1}))$ in the menu of Definition 1.2. The same
measurable map is used for every $W$ and every $\boldsymbol\eta$; $Z$ and the
previous retained values are inputs, not hidden parameter values. A finite
$N$-step transcript retains the first $N$ selected settings and outputs,
padding a stopped branch by a cemetery symbol $\dagger$. Policies that stop
earlier pay only their executed steps; a policy advertised with bound $N$
must still provision the corresponding finite menu.

Every measurable policy is an information relaxation containing any installed
finite controller. It does not assert that an arbitrary measurable map is
computable, calibrated, or physically implemented.

**Definition 1.4 (the common spectral variables).** In the deferred-pointer
dilation of source (30.4)--(30.6), write

$$
Z=u+Lq,
\qquad
p=(p_A,p_B)=H\pi-HL^{\mathsf T}\zeta,
\qquad
-HL^{\mathsf T}=\begin{pmatrix}0&1&-8\\0&-1&0\end{pmatrix}.
\tag{1.4}
$$

The output observables in (1.4) commute. Their joint Gaussian law
has $Z$ independent of $p$, with

$$
Z\sim G_W:=\mathcal N_3(L\mu(W),\Sigma_Z),
\qquad
p\sim\mathcal N_2(0,P_{\boldsymbol\eta}),
\tag{1.5}
$$

where

$$
P_{\boldsymbol\eta}=
\begin{pmatrix}
1+\eta_A+\eta_B+65r&-1/2-\eta_B-r\\
-1/2-\eta_B-r&1/2+\eta_B+r
\end{pmatrix},
\qquad
\Sigma_Z=LL^{\mathsf T}/2+\sigma^2I_3.
\tag{1.6}
$$

The variable $p$ is a spectral integration variable for the commuting
observable in the actual dilation. It is not an acquired momentum value and
(1.5) is not a joint classical assignment of the incompatible initial $q$
and $\pi$.

## 2. The finite actual-instrument correspondence

**Definition 2.1 (branch density and common base law).** For a chosen setting
$(c,\tau)$ define

$$
\varphi_{c,\tau}(y\mid x)
 =\frac1{\sqrt{2\pi\tau^2}}
   \exp\!\left(-\frac{(y-c^{\mathsf T}x)^2}{2\tau^2}\right).
\tag{2.1}
$$

For a finite policy, let $K_{\pi,N}((z,x,\omega),\cdot)$ be the recursively
generated kernel that keeps $z,\omega$, applies the measurable policy, and at
each continued step draws $y$ with density (2.1); after a stop it emits only
$\dagger$ and keeps the report. The common base law is

$$
B_{W,\boldsymbol\eta}^{\sigma}
 =G_W\otimes\mathcal N_2(0,P_{\boldsymbol\eta})\otimes\lambda.
\tag{2.2}
$$

The kernel is $W$- and $\boldsymbol\eta$-independent; these parameters enter
only through (2.2).

**Theorem 2.2 (actual finite adaptive record law).** For every fixed
$W\in\mathcal W$, $\sigma\in(0,\infty)$, finite causal policy $\pi$ and
$N\ge0$, the retained transcript law of the actual sequential instrument is

$$
\boxed{\quad
\mathsf{Law}_{W,\boldsymbol\eta}^{\pi,N}
 =B_{W,\boldsymbol\eta}^{\sigma}K_{\pi,N}.
\quad}
\tag{2.3}
$$

This is an equality of probability measures on the finite retained transcript
space. It includes the old $JM$ records, the selected settings and widths,
all selected pointer outputs, the stopping symbol and the report. It does not
factor the conditional quantum successor state through $p$.

**Proof.** The source dilation gives (1.4), the commutator cancellation
$[Z_i,p_j]=0$, and the product Gaussian law (1.5). For a selected pointer,
the actual Kraus density on its readout is

$$
M_{c,\tau}(y)=(2\pi\tau^2)^{-1/4}
 \exp\!\left(-\frac{(y-c^{\mathsf T}p)^2}{4\tau^2}\right).
\tag{2.4}
$$

The pointer coupling preserves $p$ and changes the system positions. For a
fixed realized history, every factor in the chronological product is a
bounded Borel function of the same commuting $p$. Therefore cyclicity of the
trace and the spectral theorem give, conditionally on the spectral value
$x$, the likelihood (2.1), even when the conditional quantum state is not a
function of $p$:

$$
\operatorname{tr}\!\left(M_{c,\tau}(y)\,\rho_h\,
 M_{c,\tau}(y)^*\right)
 =\int \varphi_{c,\tau}(y\mid x)\,\nu_h(dx),
\tag{2.5}
$$

and products of these factors give the joint branch likelihood. Here
$\rho_h$ is the actual normalized successor on that branch and $\nu_h$ is
its $p$ spectral measure; no normalizable momentum eigenstate is introduced.
Since later settings are measurable functions of earlier records, the
branch product is precisely the recursive transition kernel in
$K_{\pi,N}$. Induction on the executed steps proves (2.3), including the
absorbing stopped branches. The same argument with $N=0$ gives the old
record law. $\square$

The policy-dependent branch law is generally a mixture of word-specific
densities on selection regions. It is therefore not the single Gaussian law
of a word fixed independently of its outcomes. This retains the adaptive-word
restriction in Proposition 5.4 of the Gaussian source while supplying the
missing actual instrument bridge.

## 3. The countable mathematical transcript

**Definition 3.1 (padded path space).** Let $\mathcal H_n$ be the standard
Borel space of the first $n$ retained supplementary records, with $\dagger$
absorbing after a stop, and let

$$
\mathcal H_\infty=\varprojlim_n\mathcal H_n,
\qquad
\mathscr H_\infty=\sigma\!\left(\bigcup_{n\ge0}\mathscr H_n\right)
\tag{3.1}
$$

be its countable product sigma algebra. The event $T=\infty$ means that no
finite prefix contains a stop. It is a measurable path event; it is not a
finite acquired nonreturn flag.

**Theorem 3.2 (common countable path kernel).** For every measurable causal
policy $\pi$, there is a unique policy-specific Markov kernel

$$
K_{\pi,\infty}((z,x,\omega),\cdot)
$$

on $(\mathcal H_\infty,\mathscr H_\infty)$ whose $n$th cylinder marginal is
$K_{\pi,n}$. Consequently,

$$
\boxed{\quad
\mathsf{Law}_{W,\boldsymbol\eta}^{\pi,\infty}
 =B_{W,\boldsymbol\eta}^{\sigma}K_{\pi,\infty}.
\quad}
\tag{3.2}
$$

The path law is a consistent mathematical extension of the actual finite
instrument. It does not assert an infinite physical apparatus, infinite
memory, or a report returned at infinite time.

**Proof.** At every nonstopped history, (2.1) is a jointly measurable
probability kernel in $(x,c,\tau)$, and the policy is measurable. Add the
deterministic cemetery transition after a stop. The Ionescu--Tulcea
construction applied to these history kernels gives a probability measure on
the countable path space. Its cylinder marginals are the recursively defined
finite kernels, and the standard cylinder uniqueness property gives
uniqueness. Equation (2.3) for every finite prefix then identifies the actual
finite marginals; (3.2) is the single common path-kernel representation.
No joint counterfactual outcomes for incompatible future settings are used:
the kernel is constructed separately for the one policy that is run.
$\square$

**Proposition 3.3 (full-path equivalence, not a finite-prefix inference).**
For every finite $\boldsymbol\eta$, the matrix $P_{\boldsymbol\eta}$ is positive
definite. Hence all the base laws (2.2) are mutually absolutely continuous,
and the complete countable transcript laws (3.2) are mutually absolutely
continuous for one fixed policy $\pi$.

**Proof.** Use the independent coordinates

$$
U=p_A+p_B,\qquad B=p_B.
$$

From (1.6), $\operatorname{Cov}(U,B)=0$ and

$$
\operatorname{Var}(U)=\frac12+\eta_A+64r,\qquad
\operatorname{Var}(B)=\frac12+\eta_B+r.
\tag{3.3}
$$

Both variances are strictly positive, so $P_{\boldsymbol\eta}>0$. The Gaussian
densities in (1.5) are therefore mutually absolutely continuous, as are the
products with the common $G_W$ and $\lambda$. If $QK_{\pi,\infty}(A)=0$,
nonnegativity gives $K_{\pi,\infty}(u,A)=0$ for $Q$-almost every $u$;
$P\ll Q$ then gives $PK_{\pi,\infty}(A)=0$. Applying this in both directions
proves equivalence of the full path laws. The common countable kernel is the
reason this conclusion does not follow merely by collecting equivalence of
each finite prefix. $\square$

## 4. A read-count-independent status floor

**Definition 4.1 (the opposite-status pair).** Set $\sigma=2$, so
$r=1/16$, and use the same allowed $W$ and the same controller for

$$
\boldsymbol\eta_{\mathsf E}=(0,0),
\qquad
\boldsymbol\eta_{\mathsf S}=(0,7/16).
\tag{4.1}
$$

By (1.2), $F_{1/16}(\boldsymbol\eta_{\mathsf E})=-7/8$ and
$F_{1/16}(\boldsymbol\eta_{\mathsf S})=0$. Thus the pre-supplement target
(1.1) is respectively NPT-entangled and separable, with equality assigned to
the latter status. Their momentum covariance matrices are

$$
P_{\mathsf E}=\frac1{16}\begin{pmatrix}81&-9\\-9&9\end{pmatrix},
\qquad
P_{\mathsf S}=\begin{pmatrix}11/2&-1\\-1&1\end{pmatrix}.
\tag{4.2}
$$

The common old record $Z$ has the same law under both alternatives and is
independent of their respective $p$ variables.

**Lemma 4.2 (affinity and total variation bound).** With the probability total
variation convention $\operatorname{TV}(P,Q)=\sup_A|P(A)-Q(A)|$,

$$
\det P_{\mathsf E}=\frac{81}{32},\qquad
\det P_{\mathsf S}=\frac92,\qquad
\det\!\left(\frac{P_{\mathsf E}+P_{\mathsf S}}2\right)=\frac{225}{64},
$$

and the centered Gaussian affinity $A$ satisfies

$$
A^2=
\frac{\sqrt{\det P_{\mathsf E}\det P_{\mathsf S}}}
 {\det((P_{\mathsf E}+P_{\mathsf S})/2)}=\frac{24}{25}.
\tag{4.3}
$$

Consequently

$$
\operatorname{TV}(B_{W,\boldsymbol\eta_{\mathsf E}}^2,
                  B_{W,\boldsymbol\eta_{\mathsf S}}^2)\le\frac15,
\qquad
\operatorname{TV}(\mathsf{Law}_{\mathsf E}^{\pi,\infty},
                  \mathsf{Law}_{\mathsf S}^{\pi,\infty})\le\frac15.
\tag{4.4}
$$

**Proof.** Direct determinants give (4.3). Cauchy--Schwarz applied to the
square-root densities gives
$\operatorname{TV}\le\sqrt{1-A^2}=1/5$ for the two centered Gaussian
momentum laws. Tensoring with the common old-record and seed laws preserves
this total variation. For any measurable transcript event $A$, the function
$u\mapsto K_{\pi,\infty}(u,A)$ is measurable and takes values in $[0,1]$.
Integrating its level sets bounds the difference of its expectations by the
input probability total variation. This contraction and (3.2) give the second
bound. $\square$

**Theorem 4.3 (read-count-independent binary decision obstruction).** Let
$D:\mathcal H_\infty\to\{\mathsf E,\mathsf S\}$ be any measurable report
defined on every path, and write

$$
e_{\mathsf E}=\Pr_{\mathsf E}[D=\mathsf S],
\qquad
e_{\mathsf S}=\Pr_{\mathsf S}[D=\mathsf E].
$$

Then, for every measurable causal policy and every finite or countably
extended same-specimen read menu,

$$
\boxed{\quad
\frac{e_{\mathsf E}+e_{\mathsf S}}2\ge\frac25,
\qquad
\max\{e_{\mathsf E},e_{\mathsf S}\}\ge\frac25.
\quad}
\tag{4.5}
$$

The equal weights are a two-hypothesis testing comparison, not a prior over
preparations. The individual errors need not each be at least $2/5$, and the
constant is a conservative lower bound rather than an asserted sharp minimax
value.

**Proof.** Put $A=\{D=\mathsf S\}$. Then

$$
e_{\mathsf E}+e_{\mathsf S}
 =1-\Pr_{\mathsf S}(A)+\Pr_{\mathsf E}(A)
 \ge1-\operatorname{TV}(\mathsf{Law}_{\mathsf E}^{\pi,\infty},
                         \mathsf{Law}_{\mathsf S}^{\pi,\infty})
 \ge\frac45
$$

by (4.4). Divide by two and use that a maximum is at least an average. A
finite $N$-step report is a measurable function of the countable padded path,
so the same inequalities apply to every finite read count. $\square$

**Proposition 4.4 (return and abstention contract).** If a report may be
$\bot$ (abstention) or a run may have $T=\infty$, define wrong-only errors by
counting only the opposite finite status. No positive lower bound follows for
that loss: the always-$\bot$ rule has zero wrong-only error. If abstention and
nonreturn are counted as failure, set

$$
e_i^{\rm total}=\Pr_i[\text{the output is not the correct status}],
\qquad i\in\{\mathsf E,\mathsf S\}.
$$

Then the lower bound in (4.5) still holds with $e_i^{\rm total}$.

**Proof.** Let $A$ be the event that the report is $\mathsf S$. The total
error under $\mathsf E$ contains $A$, and the total error under $\mathsf S$
contains the complementary event that the report is not $\mathsf S$,
including $\mathsf E$, $\bot$ and nonreturn. Thus their sum is at least the
left side used in the proof of Theorem 4.3. The wrong-only assertion follows
from the always-abstain counterexample. The event $T=\infty$ remains a path
event in (3.1), not a finite value delivered by the observer. $\square$

## 5. Resources, continued use, and exact boundaries

For a finite bound $N$, one run uses one seventeen-mode specimen and the
original eight probe modes. The $JM$ prefix executes three original
probe-couplings and three retained old scalar records; five original probes
remain available. A continuation that executes $n\le N$ steps adds $n$ fresh
pointer modes, $n$ couplings and $n$ scalar readouts. It retains those values,
the selected rows and widths, the old records, calibration/reference data,
controller seed, stopping state and report. The pointer with width $\tau_j$
has momentum variance $1/(4\tau_j^2)$; arbitrarily narrow widths and large
coupling rows are therefore not free resource limits. A countable extension
uses a countable mathematical family of such steps and no finite total-memory
or finite total-energy claim.

The continued-use consumer is the internal status reporter for the target
(1.1): it reads the actually retained $JM$ history, chooses further lawful
positive-width pointers or stops, and emits the separable/NPT report. This is
an observer in the explicitly enlarged post-$JM$ model. It is not a native
call service, a preparation encoder, an entanglement-dependent permission
rule, or a replacement for the original fixed-$G_{gc}$ or original-$Q$
problem.

The family of preparations in (1.1) and the pointer service in Definition
1.2 are availability assumptions. The controller acquires only the retained
records and its lawful settings; it is given neither $\boldsymbol\eta$ nor
the spectral value $p$. Equation (2.3) is the derived bridge from that common
source and instrument to accessible records, rather than an inverse of an
unacquired population variance.

The correspondence proves only the accessible record law. The actual
post-pointer quantum successors remain the states generated by (2.4), and
future $q$-sensitive controls, quantum-state readout, parameter-dependent
couplings, fresh preparations, unknown-carrier acquisition, finite-bit
callable storage, or physical controller installation require separate
bridges. It does not identify $W$, reconstruct $\boldsymbol\eta$ from one
run, or make the target a property of a pure conditional branch.

The gain over the existing suppliers is precise. The Gaussian source already
has the fixed scalar and joint laws of §§30--32 and the finite independent-copy
equivalence of §33; it explicitly leaves all adaptive strategies outside that
statement. Equations (30.4)--(30.6) already supply the common commuting
spectral variables and their product Gaussian law. The present theorem uses
that dilation to derive the causal adaptive instrument-to-transcript
correspondence and its common countable path kernel, then applies the existing
affinity and testing inequalities to the explicit opposite-status pair. The
QND papers supply discrete pointer-basis and history-mixture methods, not
this continuous momentum-pointer correspondence. The categorical §9 volume
uses independent preparations and cannot replace the one-specimen resource
account here. NCR, PVC, PR57, PG and Atlas suppliers retain their own source,
rights and continued-use contracts; none supplies this Gaussian acquisition
edge, and this result does not transport their conclusions into the Gaussian
model.

No fresh-copy stopping theorem, generic finite-equivalence package, universal
$\alpha/\beta$ reduction, arbitrary-measurement impossibility, finite-bit
implementation, physical realization, total-cost optimum, or new Lean
certification is claimed. The four-expression space/time/boundary/memory
objective and the outstanding original fixed-model obligations remain open
at their stated scopes. All previous results and settlements stand unchanged
in their exact original scopes and statuses.

## 6. Sources and status

The exact common dilation, old-record covariance and supplementary scalar
coupling are [FIB shared Gaussian instruments and indexed record-law fibres,
§§24--30](FIB_SHARED_GAUSSIAN_RECORD_LAWS.md). The Gaussian separability
criterion and equality assignment are its §§26--28. The finite independent
copy limitation is its Proposition 33.1. Ionescu--Tulcea path construction,
common-kernel absolute continuity and total-variation contraction are mature
measure-theoretic suppliers, not new generic theorem packages here. At mathlib
revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, explicit source locators are
[IonescuTulcea/Traj.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean)
(`traj`, `traj_map_frestrictLe`, `eq_traj`) for the path construction and
[Composition/MeasureComp.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Kernel/Composition/MeasureComp.lean)
(`Measure.AbsolutelyContinuous.comp_right`) for common-kernel absolute
continuity. The convention note in
[TotalVariation/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Measure/TotalVariation/Defs.lean)
uses a `tvDist` twice the probability total variation of Lemma 4.2; the
contraction used here is explained directly in that lemma's proof.

The QND comparison sources are Bauer--Bernard,
arXiv:1106.4953v1/v2, and Bauer--Benoist--Bernard, arXiv:1206.6045v1. Their
discrete or method-mixture hypotheses are not silently identified with the
continuous spectral variables in (1.4).

This is a source-dependent theory application with ordinary proofs. It makes
no priority, empirical, physical, Lean, ingestion, or full-programme
completion claim.

## 追加锚（本行以下为增补区）
