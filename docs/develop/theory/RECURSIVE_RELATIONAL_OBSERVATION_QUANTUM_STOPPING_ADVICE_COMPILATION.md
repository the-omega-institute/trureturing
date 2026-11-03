# Recursive relational observation: effective finite advice for the original calibrated qutrit stopping interface

> The results below are ordinary conditional mathematical proofs, without a
> claim of Lean verification, physical installation or literature priority.
> Existing source statements retain their original hypotheses and boundaries.

## 1. The effective consumer and the source contract

[Predictive Waves VI, Definition 99.3](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_VI.md#99-全词经典表示标定及预测商的保留边界)
separates existence of stopping advice, supply of that advice, effective
production from computable inputs, and acquisition of an unknown model.
The result here supplies the third item on an explicit promised input domain.
It uses the stopping interface of VI Definition 95.1, rather than adding
stopping permission to the earlier fixed-terminal interface retroactively.
Its timetable remains independent of both the target and the preparation
parameter. Compiling the timetable and table precedes the sole preparation.

**Definition 1.1 (One original source).** Work over complex matrix spaces.
In the standard qutrit coordinates put

$$
\begin{gathered}
U=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\qquad
W=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix},\\
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\qquad
e=(1,1,-2)^{\mathsf T}/\sqrt6,\qquad
f=(1,-1,0)^{\mathsf T}/\sqrt2,\\
q=(\xi+e)/\sqrt2,\qquad E=qq^\dagger,\qquad
P_\xi=\xi\xi^\dagger,\\
0<d<1,\qquad \sin(2\theta)\ne0,\qquad
N\in U(3),\qquad [N,P_\xi]\ne0,\\
\psi=\sqrt d\,Uq+\mathrm i\sqrt{1-d}\,Uf,\qquad
\rho_0=\psi\psi^\dagger,\qquad
V_j=Ue^{\mathrm i\theta W}W^j\quad(j=0,1).
\end{gathered}
\tag{1.1}
$$

The sole installed preparation is $\rho_0$. The instrument $\mathsf J$ has
actual outcome branches $A_j(X)=V_jXV_j^\dagger/2$, including the output
label $j$. The already installed repeatable control $\mathsf N$ has map
$A_N(X)=NXN^\dagger$. The sole terminal is $(E,I_3-E)$, called exactly once
on each stopped path. These are the objects of [Predictive Waves V,
Definitions 54.1 and 91.1 and Proposition 91.3](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_V.md).
No inverse, selectable instrument outcome, additional preparation, reset,
environment port, variable angle or independent lottery is supplied.

For a chronological word $w=b_1\cdots b_t$ over $\{0,1,N\}$, the leftmost
letter acts first. Define

$$
U_w=U_{b_t}\cdots U_{b_1},\qquad
U_0=V_0,\quad U_1=V_1,\quad U_N=N,\qquad
A_w=2^{-k(w)}\operatorname{Ad}_{U_w},
\tag{1.2}
$$

where $k(w)$ counts outcome letters. In particular, every actual next
$\mathsf J$ label has conditional probability $1/2$, at every surviving
history and every mathematical input density matrix. This follows from
$V_j^\dagger V_j=I_3$, not from an external choice of labels.

**Definition 1.2 (Finite names and their promises).** A name of a real
number $x$ is a finite program which, on every natural-number input $n$,
halts with a rational $a(n)$ satisfying $|a(n)-x|\le2^{-n}$. A name of a
complex matrix supplies such programs for its real and imaginary entries.
Inputs are names $a_\theta,a_N$ of the particular installed $\theta,N$,
a name $a_P$ of a particular rank-one orthogonal projection $P\in M_3$,
and a positive rational accuracy $\varepsilon$. Totality, the error
bounds, the conditions in (1.1), and $P=P^\dagger=P^2$ with
$\operatorname{Tr}P=1$ are promises. The codes must describe the same
source, coordinate alignment and target throughout this run. There is no
algorithmic test of all these promises in the conclusion.

No name of $d$ or $\rho_0$ is required. The names are supplied calibrated
information, not observations obtained from fair labels. Producing,
authenticating and binding them to hardware are separate tasks. The
finite arithmetic certificates below are conditional on the soundness of
the input enclosures; they do not authenticate that binding or certify the
global correctness of an arbitrary program.

**Definition 1.3 (Stopping authority and initialization).** A finite
classical controller may retain a finite action string in
$\{\mathsf J,\mathsf N\}^T$, its checkpoints and a stop bit for each
checkpoint label prefix. Until stopping it executes the next prescribed
action, without changing the positions of $\mathsf N$ in response to
outcomes. A stop bit calls the original terminal and ends the run. The
last checkpoint is forced to stop. This is exactly the extra classical
authority declared in VI Definition 95.1.

The names are evaluated and the whole controller is constructed, stored
and initialized before the sole preparation is invoked. Its finite
classical storage and permission to implement this stopping interface are
explicit resources. After preparation, table lookup and record updates
select among these already permitted decisions; they do not evaluate
names or run the compilation search. No quantum wait, idle or identity
action is added. As in the source stopping model, the theorem concerns
discrete calls and their intervening classical decisions. A laboratory
claim would additionally need a timing and uncontrolled-evolution model
for those decisions. In particular, the construction never presumes
holding an acquired unknown specimen while an unbounded classical search
finishes. It does not provide a native service port or physical controller
installation. The target name is available before preparation as well.
A task first disclosed after an irrevocable specimen arrival, without
this permitted prelude, is outside the initialization theorem; no
holding permission for that different task is inferred.

## 2. Effective arithmetic and a target-independent projective sweep

Write $\|X\|_F=(\sum_{a,b}|X_{ab}|^2)^{1/2}$ for the Frobenius norm and
$\|X\|_{\rm op}$ for the operator norm. We use
$\|X\|_{\rm op}\le\|X\|_F$, unitary invariance of both norms, and
$\|P-Q\|_F\le\sqrt2<2$ for rank-one orthogonal projections.

**Lemma 2.1 (Finite upper bounds from names).** From the promised model
names, a finite word $w$, a named target $P$, and any positive rational
$\eta$, one can compute a rational $u(w,P,\eta)$ such that

$$
0\le u(w,P,\eta)-\|U_w^\dagger EU_w-P\|_F\le\eta.
\tag{2.1}
$$

The same procedure applies when the target is an exactly given rational
matrix. It produces a finite rational interval derivation from finitely
many name responses and their promised error bounds. A strict inequality
between the norm and a positive rational threshold is therefore
semidecidable; equality need not be decided.

**Proof.** Since $W^2=I_3$,
$e^{\mathrm i\theta W}=\cos\theta I_3+\mathrm i\sin\theta W$.
A name response at precision zero gives a rational bound on $|\theta|$.
Taylor series with their factorial tail bounds on that bounded interval,
together with refinements of the name, give rational enclosures of sine
and cosine of any requested width. The fixed square roots in $q$ can be
enclosed by rational bisection. Matrix sums, products and adjoints are
finite arithmetic operations. For example, if each factor $G_i$ is
unitary and $\|G_i-\widetilde G_i\|_{\rm op}\le h$, the telescoping
product estimate is bounded by $t h(1+h)^{t-1}$ for a product of $t$
factors. Thus one can choose input precisions effectively for any
specified finite word, without assuming exact unitarity of rational
approximants. Entry enclosures, rational bounds on sums of their squares,
and square-root bisection give a norm interval of width at most $\eta$;
take its nonnegative rational upper endpoint. All intermediate error
inequalities can be retained as finite rational arithmetic. Refining
$\eta$ until an upper endpoint is below a threshold recognizes every
strict instance. This uses neither an equality oracle nor a system
measurement. ∎

**Lemma 2.2 (An explicit finite projective net).** For every positive
rational $\delta\le1/16$, one can produce a finite list of rational
rank-one projections $Q_1,\ldots,Q_M$ such that every complex qutrit
rank-one projection is at Frobenius distance strictly less than
$\delta/16$ from one of them. The list depends only on $\delta$.

**Proof.** Choose an integer $m>128/\delta$. Enumerate all nonzero
complex vectors whose six real coordinates are multiples of $1/m$ in
$[-1,1]$, and output $Q_z=zz^\dagger/(z^\dagger z)$. Each denominator is
a positive rational, so this is a finite effective list; duplicates do
not matter. For a unit vector $v$, round each real coordinate to the
nearest grid point. The resulting $z$ satisfies
$\|z-v\|\le\sqrt6/(2m)<2/m<1$, hence $z\ne0$. Put $u=z/\|z\|$.
The triangle inequality gives $\|u-v\|\le2\|z-v\|<4/m$.
Expanding $uu^\dagger-vv^\dagger$ into two rank-one terms gives
$\|uu^\dagger-vv^\dagger\|_F\le2\|u-v\|<8/m<\delta/16$.
The normalized vector need not be computed to output $Q_z$. ∎

**Lemma 2.3 (Effective positive-word sweep).** Given valid model names
and $\delta$ as above, there is a terminating search for a finite
reference word

$$
\omega=0v_1\cdots v_M,\qquad
S_0=V_0,\qquad S_j=U_{v_j}S_{j-1},\qquad
\|S_j^\dagger ES_j-Q_j\|_F<\delta/16,
\tag{2.2}
$$

with every $v_j$ a nonempty positive word over $\{0,1,N\}$. Consequently
$R_j=S_j^\dagger ES_j$ form a strict $\delta/8$ projective net. Neither
the search nor its checkpoints use $d$ or any eventual target $P$.

**Proof.** The positive-word conjugation density of [Predictive Waves V,
Theorem 95.1](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_V.md#95-任意一个混合控制把实际原生闭包扩到-pu3)
is the substantive source supplier. It applies to every angle and
control in (1.1), including $\langle\xi,N\xi\rangle=0$; it supplies no
installed inverses. For each already chosen prefix $S_{j-1}$, the
conjugates $S_{j-1}^\dagger U_v^\dagger EU_vS_{j-1}$ are dense in the
rank-one projections. Restricting to nonempty positive words preserves
density: the subfamily obtained by placing any one fixed letter before
arbitrary positive words is a fixed unitary conjugate of a dense orbit.
Thus (2.2) has a strict witness at each step.

Search finite stages of words and precisions. At stage $s$, examine all
nonempty words of length at most $s$ with a norm upper bound from Lemma
2.1 of accuracy $2^{-s}$. Each stage terminates on the input promises.
A strict witness is eventually examined finely enough that its upper
bound is below $\delta/16$. Retain the first certified witness in a
fixed ordering and proceed to the next $j$. Finiteness of the list
proves termination. The triangle inequality and Lemma 2.2 give the
strict $\delta/8$ net. The initial $0$ ensures at least one instrument
call in the reference word, and nonempty $v_j$ give strictly increasing
checkpoint positions. Reference labels here are mathematical search
data, not requests that $\mathsf J$ produce particular outcomes. ∎

## 3. The generated advice and its quantifiers

**Definition 3.1 (Two compilation stages).** Set

$$
\delta=\min\{\varepsilon/8,1/16\}.
\tag{3.1}
$$

The first algorithm $G(a_\theta,a_N,\varepsilon)$ performs Lemmas
2.2–2.3. Replace the $0,1$ letters of $\omega$ by $\mathsf J$, and its
$N$ letters by $\mathsf N$, obtaining a block $s_*$. Its length is $n$,
its instrument count is $k\ge1$, its control count is $r=n-k$, and its
$M$ checkpoints are the endpoints of the prefixes in (2.2). Choose by
an exact rational loop a positive integer $L$ with

$$
(1-2^{-k})^L<\delta.
\tag{3.2}
$$

Output the timetable $s=s_*^L$, its repeated checkpoints, $T=nL$,
$\omega$ and the finite sweep certificates. This algorithm has no
target input.

The second algorithm $H(a_\theta,a_N,a_P,\varepsilon,G\text{-output})$
enumerates every label prefix at every checkpoint of this timetable,
including those which its eventual stop table will make unreachable.
For the chronological word $w$ at that row, compute
$u_w=u(w,P,\delta/8)$ from (2.1). Its normal stop bit is

$$
\operatorname{hit}(w)=1\quad\Longleftrightarrow\quad u_w<\delta/2.
\tag{3.3}
$$

This is a decidable rational comparison, including when the exact norm
equals a threshold. At a checkpoint, a hit stops immediately. At the
last checkpoint, a hit takes priority; otherwise stop and mark timeout.
At every other row without a hit, continue the same timetable. The
finite table and its trimmed tree of reachable stopping leaves are
denoted by $\pi_P$ and $\Lambda_{\pi_P}$.

Along each actual block record whether any of its observed labels
differs from the corresponding reference label of $\omega$. In a final
partial block compare only labels which actually occurred. Keep these
mismatch bits, the timeout bit, every actual original label, the
executed $N$ positions and the stopping position. Mismatch never causes
postselection, restart, renormalization or a change of action.

**Theorem 3.2 (Effective finite advice on the calibrated source).** There
are fixed algorithms $G,H$, terminating on all the promised inputs of
Definitions 1.1–1.3, with the following order of quantifiers. For every
valid pair of model names and every rational $\varepsilon>0$, $G$
outputs one finite timetable and endpoint, independent of $d$, $P$ and
$a_P$. For every valid target name, $H$ then outputs a finite table for
that same timetable and a rational error certificate. For every
$0<d<1$, execution with that retained table on the source (1.1) is
lawful in the declared stopping interface and calls the original
terminal exactly once. It has

$$
\begin{gathered}
\alpha_\ell=2^{-k(w_\ell)}>0,\qquad
R_\ell=U_{w_\ell}^\dagger EU_{w_\ell},\qquad
F_{\pi_P}=\sum_{\ell\in\Lambda_{\pi_P}}\alpha_\ell R_\ell,\\
\sum_\ell\alpha_\ell=1,\qquad
\|F_{\pi_P}-P\|_{\rm op}<\varepsilon.
\end{gathered}
\tag{3.4}
$$

For every mathematical density matrix $\mu$, including the actual
$\rho_0$, set $E_1=E$, $E_0=I_3-E$, $P_1=P$, $P_0=I_3-P$. The complete
terminal-record law and its comparison law are

$$
\begin{aligned}
p_\mu(\ell,b)&=\alpha_\ell
 \operatorname{Tr}(E_bU_{w_\ell}\mu U_{w_\ell}^\dagger),\\
q_{P,\mu}(\ell,b)&=\alpha_\ell\operatorname{Tr}(P_b\mu),
\qquad b\in\{0,1\},\\
\sup_{\mu\succeq0,\,\operatorname{Tr}\mu=1}
\operatorname{TV}(p_\mu,q_{P,\mu})&<\varepsilon.
\end{aligned}
\tag{3.5}
$$

Both terminal cells are retained even if one has zero probability. The
leaf includes the full action and label record and all the markers in
Definition 3.1. No success conditioning is used. The comparison law is
a mathematical benchmark on that same archive, not an installed target
measurement. The uniformity over $\mu$ grants no additional preparation.

The algorithms operate on names. Different valid names for the same
matrix may yield different certified timetables; no canonical
name-independent selector is asserted. For each fixed naming, the
same timetable works for every target, as required by the existential
target-independent quantifiers of VI Theorem 96.1. Invalid names or
failed source promises are outside the termination claim.

**Proof.** The first search terminates by Lemma 2.3 and the rational
loop (3.2) terminates since $k\ge1$. The second stage evaluates only a
finite number of rows, so Lemma 2.1 proves its termination. Two
consequences of (2.1) and (3.3) are

$$
\begin{aligned}
\|U_w^\dagger EU_w-P\|_F<\delta/8
 &\ \Longrightarrow\ u_w<\delta/4<\delta/2,\\
\operatorname{hit}(w)=1
 &\ \Longrightarrow\ \|U_w^\dagger EU_w-P\|_F<\delta/2.
\end{aligned}
\tag{3.6}
$$

Condition on any actual surviving block-entry history, and let $U_a$
be its cumulative unitary. The net of Lemma 2.3 contains an $R_j$ with
$\|R_j-U_aPU_a^\dagger\|_F<\delta/8$. If the actual labels through
that reference checkpoint agree with $\omega$, the cumulative word
there has effect $U_a^\dagger R_jU_a$, at distance less than
$\delta/8$ from $P$. Hence the table stops there or at an earlier hit.
To express this without generating unobserved outcomes after a stop,
take the first hit along this reference path: matching its actually
needed prefix has conditional probability $2^{-k_j}\ge2^{-k}$.
This event is an actual stopped path. All other outcomes remain in
the tree. The argument applies at every surviving block entry,
although $U_a$ generally changes from one block to the next.

The conditional probability of surviving a block without a hit is
therefore at most $1-2^{-k}$. Iterating conditional probabilities gives
the timeout mass

$$
\tau=\sum_{\ell:\,t_\ell=1}\alpha_\ell
\le(1-2^{-k})^L<\delta.
\tag{3.7}
$$

This is neither a Haar-mixing estimate nor an assumption of independent
block states. It uses no reset, selected branch or independently drawn
$N$. Each $\mathsf J$ node divides its incoming mass into two equal
parts and each $\mathsf N$ node preserves it. A finite complete tree
with forced final stopping thus gives $\sum_\ell\alpha_\ell=1$.
Equation (1.2) gives (3.5)'s exact $p_\mu$ and its leaf marginal
$\sum_b p_\mu(\ell,b)=\alpha_\ell$. This is the complete-tree supplier
of VI Proposition 95.2, not a new normalization assumption.

Every non-timeout leaf has Frobenius error less than $\delta/2$.
For every timeout leaf the error is at most $\sqrt2<2$. Consequently

$$
D_F:=\sum_\ell\alpha_\ell\|R_\ell-P\|_F
\le (\delta/2)(1-\tau)+2\tau
<5\delta/2<\varepsilon.
\tag{3.8}
$$

The triangle inequality bounds $\|F_{\pi_P}-P\|_{\rm op}$ by $D_F$.
The two terminal differences for each leaf have equal absolute value,
since their effects sum to the identity. Hence

$$
\operatorname{TV}(p_\mu,q_{P,\mu})
=\sum_\ell\alpha_\ell
 |\operatorname{Tr}[(R_\ell-P)\mu]|
\le\sum_\ell\alpha_\ell\|R_\ell-P\|_{\rm op}\le D_F.
\tag{3.9}
$$

Mismatch and timeout fields are deterministic functions of the full
leaf. Keeping those fields alongside the leaf preserves (3.9), and
keeps their original, unconditioned masses. Every event formed from
the complete archive is subject to this total-variation bound. The
finite certificate is supplied by Proposition 4.1 below; its construction
does not alter the table. The retained-use claim follows from Proposition
5.1. Neither conclusion uses $d$ in compilation. ∎

## 4. A finite conditional error certificate

**Proposition 4.1 (Arithmetic certificate for the entire tree).** The
second compiler can also output a rational number $b$ and a finite
certificate, checkable by finite rational arithmetic from the supplied
input enclosures, such that

$$
D_F<b<3\delta<\varepsilon.
\tag{4.1}
$$

The certificate bounds the full law in (3.5) and the effect in (3.4).
It does not merely certify the successful branch.

**Proof.** Enumerate the finite reachable leaf set after filling the
table. For each leaf use Lemma 2.1 to compute a rational $v_\ell$ with
$0\le v_\ell-\|R_\ell-P\|_F\le\delta/8$. Define

$$
b=\sum_\ell 2^{-k(w_\ell)}v_\ell+\delta/8.
\tag{4.2}
$$

The weights are exact rationals whose sum is one. Therefore
$D_F+\delta/8\le b\le D_F+\delta/4<11\delta/4<3\delta$.
In particular $b<\varepsilon$ is itself a rational check. Retain the
finite input responses used for these norm bounds, the rational
enclosures of the fixed constants and trigonometric evaluations,
their finite error calculations, and the tree with its exact weights.
A checker verifies child structure, forced stopping, the weights,
the interval calculations and (4.2). Its inference from the norm upper
bounds to (3.4)–(3.5) is just (3.9) and the triangle inequality.
For a certificate of the table-generation rule itself, also retain
the finite row comparisons (3.3); these are decidable rational
inequalities. The sweep certificates certify the first stage's search
outputs. None is an infinite trace of the search.

Soundness is conditional: a finite response labelled as an enclosure
of an installed matrix must actually enclose that matrix. Finite
rational arithmetic cannot prove that an arbitrary naming program is
total or accurately describes physical controls. The finite certificate
can check the achieved error without reconstructing a density proof or
rerunning the search; the density theorem is what guarantees that the
compiler will find its first-stage outputs on every promised source. ∎

## 5. Retention, selection and lawful use in the same run

**Proposition 5.1 (From generated code to the actual stopped process).**
Under Definitions 1.1–1.3, the advice of Theorem 3.2 is realizable by a
finite initialized classical table controller. At every preterminal
classical or action cut its stored path and the quantum substate agree
with the corresponding node of the compiled tree. It uses no online
matrix-norm comparison, model oracle or target-outcome choice.

**Proof.** Serialize the finite expanded tree using action tags, child
indices, checkpoint stop bits and marker updates; retain $s$, its
checkpoints and reference labels with it. Allocate its storage and an
archive before preparation, write the generated data into that storage,
and initialize the pointer to the root. These are specified classical
state transitions in this declared ideal controller, with their costs
charged in §8. The advice has thereby been produced and retained, not
supplied as a further unexplained oracle. The supplied prerequisites are
the accurate names, finite memory and stopping authority.

At a continue node the action tag requests precisely the next letter
of $s$. For $\mathsf N$ follow its sole child and record that action.
For $\mathsf J$ read the actual returned label and follow exactly its
child; record that label and update the mismatch bit. At a checkpoint
read the already stored bit. A stop invokes the sole terminal, records
its actual bit, and terminates; the final non-hit also sets timeout.
There is no discard transition. Table fetch and archive writes alter
only the classical state in this discrete-call model, and do not
request a new quantum action.

Induction on executed actions now proves that at a history $w$ the
quantum substate for a mathematical input $\mu$ is exactly
$2^{-k(w)}U_w\mu U_w^\dagger$, and the pointer and archive encode
that same history. Intermediate classical steps preserve this
invariant. At terminal invocation the Born rule gives exactly (3.5).
All decisions are determined by fixed retained data and actual past
labels. The paths therefore have the same legal actions and
preterminal successors as the compiled tree, not just the same
terminal marginal. This proof is an interpreter realization in the
declared source interface. It does not supply a physical memory
device, a native call service, a bound on laboratory delay or the
unspecified quantum state after terminal measurement. ∎

The map from supplied names to advice is a one-way effective
construction. The table need not recover $\theta$, $N$, $P$ or their
names; different inputs can give the same finite table. Likewise a
finite actual archive does not determine the unused rows of the table.
No inverse or unknown-source calibration is inferred from either map.
Exact numerical probabilities for the actual preparation would also
require information about $d$ if $d$ is not computably supplied; the
compiler instead gives the uniform law bound for its entire allowed
range.

## 6. The original five-dimensional sector and the exact converse domain

**Proposition 6.1 (Both source-coordinate directions on the original sector).**
Let $H=\mathbb C^5$ and

$$
B=\big((e_0+e_3)/\sqrt2,\ (e_1+e_4)/\sqrt2,\ e_2\big),\qquad
\Pi=BB^\dagger,\qquad P_5=BEB^\dagger.
\tag{6.1}
$$

Use the original five-dimensional Kraus operators
$\widehat K_{\theta,j}$ of V (54.7) and the installed lift
$\widetilde N=BNB^\dagger+(I_5-\Pi)$ of VI (95.4). The maps

$$
\mathcal L(X)=BXB^\dagger,\qquad
\mathcal C(Y)=B^\dagger YB
\tag{6.2}
$$

are mutually inverse positive, trace-preserving coordinate maps between
$M_3$ and the supported sector $\{Y\in M_5:Y=\Pi Y\Pi\}$.
They preserve every compiled preterminal branch, its substate and
classical record in both directions. They also preserve both
probabilities of the single original terminal
$(P_5,I_5-P_5)$. The actual five-dimensional preparation is the original
$B\rho_0B^\dagger$ supplied by V Proposition 91.3, without an additional
preparation choice.

**Proof.** $B^\dagger B=I_3$ gives
$\mathcal C\mathcal L=\operatorname{id}$ and
$\mathcal L\mathcal C(Y)=\Pi Y\Pi=Y$ on the stated sector.
These formulas give positivity, trace preservation on that domain,
and the same identities for subnormalized matrices. The source's
intertwining identity is

$$
\widehat K_{\theta,j}B=BV_j/\sqrt2,\qquad
\widetilde N B=BN.
\tag{6.3}
$$

Thus $\mathcal L A_j(X)=\widehat K_{\theta,j}\mathcal L(X)
\widehat K_{\theta,j}^\dagger$ and
$\mathcal L A_N(X)=\widetilde N\mathcal L(X)\widetilde N^\dagger$.
Compressing gives the converse on every supported branch. In particular
all those branches stay in the sector. Induction gives the word
substate correspondence, with the same factor $2^{-k(w)}$.
The controller sees the same outcome labels, hence traverses the same
table and makes the same stopping decisions. Finally
$B^\dagger P_5B=E$ and
$B^\dagger(I_5-P_5)B=I_3-E$ give both terminal probabilities.
The comparison law in (3.5) transfers by the same trace identities.
No approximation is lost in either direction. ∎

Outside $Y=\Pi Y\Pi$, compression followed by lifting gives
$\Pi Y\Pi$, not $Y$. Thus the converse is not an inverse on arbitrary
five-dimensional inputs. Compression here is a coordinate map, not an
installed physical recovery command. The original terminal has supplied
effects and record probabilities; no particular postmeasurement
instrument was specified. Accordingly neither Proposition 6.1 nor the
total-variation bound asserts a postterminal-state inverse, an
instrument approximation, a diamond-norm bound or a new reference port.

## 7. Consumers in their supplied-input domains

**Corollary 7.1 (A computable original target with no preparation name).**
Choose the fixed computable target $P=P_\xi$. The generated advice is
independent of $d$, and on the actual original preparation it satisfies

$$
\left|\Pr_{\rho_0}^{\pi_{P_\xi}}(\text{terminal }1)-d/2\right|
<\varepsilon\qquad(0<d<1).
\tag{7.1}
$$

**Proof.** The entries of $P_\xi$ are rational. V (91.6) gives
$\operatorname{Tr}(P_\xi\rho_0)=d/2$. Apply (3.4) or sum the complete
law in (3.5). This is a bound on a Bernoulli probability, not an
estimator of $d$ from one terminal bit or a finite-sample certification
of the model. ∎

**Corollary 7.2 (One generated suffix on all original prefix histories).**
For a fixed valid target name, use the same compiled suffix after every
history of each of the original prefix contexts in VI Definition 93.1,
with a new suffix pointer at that context's end, ignoring its identity
and labels in all suffix decisions. Let
$r_i=A_{u_i}\rho_0$ and $m_i=\operatorname{Tr}r_i=2^{-k(u_i)}$ for its
nine specified prefix events. Their unnormalized suffix laws satisfy

$$
\begin{gathered}
p_i(\ell,b)=\alpha_\ell\operatorname{Tr}(E_bU_{w_\ell}r_iU_{w_\ell}^\dagger),
\qquad q_i(\ell,b)=\alpha_\ell\operatorname{Tr}(P_b r_i),\\
\sum_{\ell,b}p_i(\ell,b)=\sum_{\ell,b}q_i(\ell,b)=m_i,\\
\frac12\sum_{\ell,b}|p_i(\ell,b)-q_i(\ell,b)|<m_i\varepsilon,
\qquad |\operatorname{Tr}[(F_{\pi_P}-P)r_i]|<m_i\varepsilon.
\end{gathered}
\tag{7.2}
$$

**Proof.** Substitute the positive substate $r_i$ into (3.9); trace
scaling gives the bounds. Operationally the suffix also runs after
every other prefix history, and those histories remain in that
context's archive. The $u_i$ event retains its original probability
$m_i$. There is no preparation of $r_i/m_i$, selection of the prefix
event, or cross-context preparation lottery. This is the effective
advice application of VI Corollary 96.2. Proposition 6.1 transfers it
to the original supported five-dimensional source. ∎

The theorem does not produce the nine prefix words or a source-dependent
target merely because their existence has been proved. In particular,
the separating target $P_N$ of VI Theorem 92.1 can be used here only
when an accurate computable name for that target is separately given
or constructed with its own proof. Existence of a parameter-dependent
witness is not a naming algorithm. No such selection is needed for
Corollary 7.1 or for the effective-synthesis consumer in VI 99.3.

## 8. Resources of this same prepared and stopped run

**Proposition 8.1 (Finite instance bounds, with classical costs separate).**
For the generated instance above, every actual run makes at most $Lk$
instrument calls, at most $Lr$ calls to the same installed $N$, at most
$LM$ checkpoint lookups, and exactly one original terminal call. No
extra system call is used by the compiler or its certificate checker.
Compilation, retention and online classical work are finite per valid
instance but are additional resources.

**Proof.** Every actual path is a prefix of $s_*^L$, with early stopping
only. These give the quantum-call and checkpoint bounds immediately.
For an explicit finite storage bound let $k_t$ count the instrument
positions in the first $t$ actions of the nominal timetable. The full
untrimmed action tree has

$$
S=\sum_{t=0}^{T}2^{k_t}\le(T+1)2^{Lk}
\tag{8.1}
$$

nodes. All table rows and trimmed leaves are included in this finite
tree. A serialization with fixed-width child indices therefore uses
$O(S(1+\log(S+1)))$ bits for node tags, links and stop bits, in addition
to the timetable, reference word, markers and arithmetic certificate.
All rational certificate numerators and denominators have finite
actual bit lengths; their sum, rather than a constant-cost real
number convention, is charged to the advice size. An elementary
sequential tape interpreter suffices: a table fetch may scan the
whole serialized table. Random-access memory is not required to
claim finite implementation. Its bit steps and workspace are charged
as classical costs, and no efficiency bound is inferred from (8.1).

The actual archive contains at most $Lk$ outcome bits, at most $L$
mismatch bits, the timeout bit and terminal bit, with the executed
action positions, stop decisions, source/advice identifiers and
framing retained as well. One can allocate a finite bound before
preparation, since $T$, $S$ and the serialization are then known.
The quantum-call bounds do not include the bit cost of writing,
copying or reading that archive. Detailed deterministic controller
traces, if also retained, are functions of the same actual path and
fixed advice; their full size and writing cost must also be charged.

The first-stage word search and all precision refinements terminate
by Lemmas 2.1–2.3. The second-stage enumeration and certificate
generation have finitely many terminating evaluations. A universal
classical implementation therefore has a finite actual step count
and maximum workspace on every valid input. These include evaluation
of the supplied naming programs, rational arithmetic and construction
of the stored controller. They take place before preparation, and
are not counted as $\mathsf J$ or $\mathsf N$ calls. Preparation of
the naming inputs, their authentication, storage allocation and
loading are separate costs as well; their availability is an explicit
premise, not a zero-cost achievement of the quantum source. ∎

For clarity, the resource account is a vector for the same execution,
not a sum in which classical work is converted into free quantum calls.
With a fixed bit-machine implementation, write $C_G,C_H,C_{\rm check}$
for its actual pre-preparation step counts, $C_{\rm load}$ for writing
the retained controller, and $C_{\rm on}(w_\ell,b)$ for the actual
online lookup and archive work. A run is charged these counts, the
actual retained and peak working bit sizes, and the quantum counts

$$
\bigl(k(w_\ell),\ \#_N(w_\ell),\ 1\bigr)
\le\bigl(Lk,Lr,1\bigr)
\tag{8.2}
$$

coordinatewise. Name evaluations are included in $C_G+C_H+C_{\rm check}$,
wherever they are actually performed. If the finite certificate is
retained without being separately checked in that run, its generation
still costs work in $C_H$; no additional check is claimed. Input
production and physical binding costs must be added when describing a
larger process that supplies the names. They have no bound supplied by
this theorem. Deterministic additions to the online archive preserve
the complete-record bound because the full $(\ell,b)$ is still retained
and the added fields are functions of it and the fixed advice.

There is no efficiency, minimality or uniform total-resource claim over
all valid models and naming programs. In particular [VI Theorem
97.1](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_VI.md#97-混合调用上限与精确有限取得的两个边界)
still excludes a uniform finite $N$-call bound over the allowed
installations for fixed error below $2/5$. The present compiler permits
its timetable, advice size and run costs to depend on the named
installation. A finite program is not a constant-memory guarantee;
the finite allocation here is made only after the particular advice
has actually been constructed. If compilation is repeated for another
target, that is another classical cost; each subsequent quantum run
requires its declared preparation and terminal resources.

## 9. Supplier correspondence and the remaining common-process problem

**Source correspondence.** The source-specific increment is the
terminating production of a target-independent timetable and
target-dependent retained table from finite accurate names, with a
finite conditional certificate for the complete record law. Direct
reuse of VI Theorem 96.1 supplies existence, and VI 99.3 permits a
supplied finite table, but neither supplies that production algorithm.
The rational net, certified strict search and finite expanded-table
construction close precisely that missing implication. The stochastic
sweep and complete-tree argument are reused with rational margins,
not renamed as newly discovered control or probability principles.

| Supplier | Exact contribution and boundary |
| --- | --- |
| Predictive Waves V §§54, 91, 95; VI §§95–100 | Original source, sole preparation, positive-word projective density, stopping authority, complete leaf law, existence/supplied-advice result and the explicit VI 99.3 effective-synthesis gap. VI 97–100 retain their uniform-cost, ternary, calibration and common-implementation boundaries. |
| `D5/S3/Quantum/Measurement/OriginalSingleTerminalTernaryObstruction.lean`, with `Blueprint/D5/S3/Quantum/Measurement/OriginalSingleTerminalTernaryObstruction.scribe.cs` | `fixedStoppingTree` takes a checkpoint and stop function already supplied. `complete_original_single_terminal_ternary_obstruction` supplies the general complete-tree leaf identities, code-sector equality and ternary boundary. It does not synthesize the stop function from computable model/target names. |
| `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.lean`, with its same-named owning Scribe | `OriginalCodeRealization` and `original_code_service_simulation` require supplied original code and its realization equation in a native service domain. They do not install this quantum stopping interface, compute its table or transfer native rights and costs to it. |
| Predictive Waves VI §§101–106, 110–111 | Later record-retention/coherent extensions and the nonselective contraction consumer have their own additional interfaces. Their existence does not turn the present original terminal into a postmeasurement instrument or supply a model-to-advice compiler. None of those additional ports is assumed here. |
| Atomic Generation Acquisition III §16.3; Native Leaf Boundary Acquisition IV §117; Process Geometry §§1–2 | A common apparatus must preserve preparations, legal actions, actual returns and successors, plus rights when claimed. The code-sector intertwiner above is such an exact correspondence within one quantum source, not a map from native/path/continuous processes to that source. |

The comparison uses the public source at
`ff3ea7091bd514090f02823448ff9046ae8e331d`. It preserves the literal
historical comparison pins inside the suppliers. In particular VI
§100's comparison at `e30c151ba97e8290d5969cb9e29b6adc29090582` and
Process Geometry's opening comparison at
`e5f7c3993b8fb2af67764dda0955ee31e74921b7` are not assertions that
every linked document has the current revision's content. The
intervening public additions to the source and its relevant owners
do not supply the VI 99.3 compiler. This is a bounded comparison of
the named supplier and consumer, not a corpus-wide absence theorem.

**Literature correspondence.** The computability and gate-search
ingredients are mature. The following attributions distinguish their
domains from the source-specific application proved here.

| Source | Used content and scope |
| --- | --- |
| Halil-Shah–Oi, [arXiv:1401.8004v1, §II](https://arxiv.org/html/1401.8004v1) | Fixed programmes, stochastic gate products and target-error stopping already occur with the paper's actual ancilla preparation and coupling. They do not by themselves give this original qutrit's target-independent timetable, retained table or complete finite-timeout error certificate. |
| Dawson–Nielsen, [arXiv:quant-ph/0505030v2, Definition 1 and the Solovay–Kitaev algorithm](https://arxiv.org/html/quant-ph/0505030v2) | Constructive gate approximation for its finite selectable inverse-closed universal gate set. That library and its efficiency bounds are not the present uncontrolled $\mathsf J$ labels and single repeated $N$. |
| Bouland–Giurgică-Tiron, [arXiv:2112.02040v1, introduction](https://arxiv.org/html/2112.02040v1) | Inverse-free universal compilation is an established subject; absence of installed inverses is not a generic impossibility argument. Here the reference word is only a stochastic path witness. Lawful use still requires the finite fixed schedule and stopping tree proved above. No efficiency result from this paper is imported. |
| Pinned mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, [`Mathlib/Analysis/Matrix/Normed.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Matrix/Normed.lean) and [`Mathlib/Computability/Partrec.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/Partrec.lean) | Frobenius norm calculus and ordinary partial-recursive search/minimization are existing tools. They do not provide an installed-source representation or the source-specific advice-to-run proof. |

The classification of the application in §§2–8 is `repo-derived`:
it combines the exact source density and stopping suppliers with
effective arithmetic and verifies the missing generation, retention
and use bridge. No global novelty or priority assertion is made.
Its evidence consists of the stated conditional proofs and cited suppliers,
without a claim of formal verification or experimental validation.

**Remaining obligations.** The gain toward a common-process account is
bounded: finite accurate descriptions now produce an actually retained
finite controller whose original-source chronology and terminal record
law are proved together, including their exact original code-sector
representation. The target is not merely a symbol accompanied by an
existential stopping witness. This does not identify independently
meaningful space, time, boundary and memory views with mutually
recoverable observations of a native/quantum/continuous common
apparatus. An advice table is not an acquired geometry or a common
counterfactual outcome seed.

Unknown-source calibration and input authentication remain open
acquisition obligations. VI Proposition 99.2 still makes the
preterminal labels model-blind for a fixed table. Shared coherent
references, cross-process initialization and operation maps,
finite-noise certification, postterminal instruments and common
multi-outcome measurements require their own proofs. VI §98's
single-terminal ternary obstruction is unchanged. No unrestricted
four-view inverse, efficient synthesis, universal or minimal
alpha/beta generation, or physical installation follows. Every
fixed-$G_{\rm gc}$, original-$Q$, parked-consumer,
unchanged-initialization, original-terminal and final-no-Ready
obligation retains its original scope. The full common-process
programme is not completed by this effective calibrated leg.

## 追加锚（本行以下为增补区）
