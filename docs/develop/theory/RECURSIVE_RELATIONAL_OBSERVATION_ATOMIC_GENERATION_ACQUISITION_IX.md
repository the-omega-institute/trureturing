# Recursive relational observation: atomic generation and acquisition IX

## 170. The finite phase targets fail unchanged-prefix consistency

**Definition 170.1 (the original endpoints and a prefix experiment).**
Retain [VIII157.1–157.2](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_VIII.md#157-a-regular-actual-phase-orbit-with-a-uniform-interior-coherence):
$A_0=D=\operatorname{diag}(1,3)$, $A_1(t)=e^{it}X$, and both endpoints
$e_0$. For calculations also allow lengths $n=0,1,\ldots$, writing

$$
\begin{aligned}
\psi_{n,ab}(t)(w)&=e_a^{\mathsf T}A_{w_1}(t)\cdots A_{w_n}(t)e_b,
& a,b&\in\{0,1\},\\
T&=\begin{pmatrix}1&1\\1&9\end{pmatrix},
&a_n&=(T^n)_{00},\qquad b_n=(T^n)_{01},\\
\rho_n(t)&=|\psi_{n,00}(t)\rangle\langle\psi_{n,00}(t)|/a_n.
\end{aligned}
\tag{IX.1}
$$

For $n\ge5$ this is exactly VIII157's original full finite input, with
all physical exterior factors present. The shorter lengths are auxiliary
calculations, without any interior-regularity assertion. An unchanged-prefix
output family means densities $\sigma_n$ on the first $n$ actual acquired
factors satisfying $\operatorname{Tr}_{n+1}\sigma_{n+1}=\sigma_n$.
The old factors may have arbitrary retained references, but are neither
replaced nor operated on in this prefix comparison.

The prefix experiment reads the occupations of all these $n$ factors,
retains the entire word $z\in\{0,1\}^n$, and computes its parity. It
uses V25.1's actual occupation instrument at acquired endpoints. Parity
is a function of its delivered bits, rather than an additional observable
or an observation of a hidden Kraus label.

**Theorem 170.2 (exact adjacent-length obstruction).** Set

$$
u=4+\sqrt{17},\qquad \lambda=5+\sqrt{17}=1+u,
\qquad \mu=5-\sqrt{17},\qquad q=\mu/\lambda\in(0,1).
\tag{IX.2}
$$

For every real $t$ and every $n\ge1$, the half-trace distance is

$$
\begin{aligned}
d\bigl(\rho_n(t),\operatorname{Tr}_{n+1}\rho_{n+1}(t)\bigr)
 &=\delta_n=\frac{b_n}{a_{n+1}}\\
 &=\frac{u(1-q^n)}{1+u+(u^2-u)q^n}.
\end{aligned}
\tag{IX.3}
$$

The prefix occupation experiment attains this distance: its odd-parity
probabilities are respectively $0$ and $\delta_n$. The sequence
$\delta_n$ is strictly increasing, $\delta_1=1/2$, and
$\lim_n\delta_n=u/\lambda$. In particular, for every $n\ge5$,
$\delta_n\ge479/538$.

Consequently the original $\rho_n(t)$ cannot be the unchanged-prefix
bank of one growing source. More quantitatively, for every consistent
family $\sigma_n$ and $e_n=d(\sigma_n,\rho_n(t))$,

$$
e_n+e_{n+1}\ge\delta_n,\qquad
\sup_{n\ge5}e_n\ge\frac{u}{2\lambda}.
\tag{IX.4}
$$

Proof. A virtual index changes exactly at a physical one. Thus
$\psi_{n,00}$ has even support and $\psi_{n,01}$ has odd support;
both are nonzero for $n\ge1$. Summing their squared amplitudes gives
$\|\psi_{n,ab}\|^2=(T^n)_{ab}$. The last physical bit gives the exact
vector identity

$$
\psi_{n+1,00}
 =\psi_{n,00}\otimes|0\rangle
   +e^{it}\psi_{n,01}\otimes|1\rangle.
\tag{IX.5}
$$

After tracing that bit, the even block is
$(a_n/a_{n+1})\rho_n$, the odd block has trace $b_n/a_{n+1}$,
and $a_{n+1}=a_n+b_n$. Their supports are orthogonal. Subtracting
$\rho_n$ therefore gives trace norm $2b_n/a_{n+1}$. On the even
words the occupation law is the same law scaled by $a_n/a_{n+1}$,
so its total variation distance is also exactly $\delta_n$.

The eigenvectors $(1,u)^{\mathsf T}$ and $(-u,1)^{\mathsf T}$ of $T$
have eigenvalues $\lambda,\mu$, since $u^2=8u+1$. Hence

$$
a_n=\frac{\lambda^n+u^2\mu^n}{1+u^2},\qquad
b_n=\frac{u(\lambda^n-\mu^n)}{1+u^2}.
\tag{IX.6}
$$

Substitution proves (IX.3). Its right side is strictly decreasing as
a function of $q^n$, proving the claimed monotonicity and limit.
Direct integer recurrence gives $a_5=944$, $b_5=7664$ and $a_6=8608$,
so $\delta_5=479/538$. Finally, triangle inequality and contraction
under partial trace give (IX.4); taking the supremum and then the
limit in $\delta_n$ gives its second assertion. $\square$

**Proposition 170.3 (finite benchmark and the finite-horizon distinction).**
On a common acquired roster, comparing the first five factors of
$\rho_5(t)$ and $\rho_6(t)$ by the complete occupation instrument,
the equal-prior minimum error on that five-factor interface is
$59/1076$. This statement concerns that interface, with the sixth factor
unread; it is not an optimum for access to all six factors or to supplier
memory. A supplied pure target at each separately chosen finite horizon
does not imply a causal family of those targets.

Proof. Report the six-length alternative on odd parity and the five-length
alternative on even parity. The first alternative never has odd parity,
and the second has even probability $59/538$, giving error $59/1076$.
On each even word its probability under the second alternative is the
constant $59/538$ times its probability under the first. This is the
optimal classical decision; (IX.3) also makes it the binary quantum
optimum on the five-factor interface. A common unused vacuum slot may
back the sixth roster entry for the five-length alternative; neither
its readout nor a preparation label is needed by this consumer.
Every outcome word and its actual projected full-bank successor remains
present. The two alternatives are separately prepared finite inputs,
not successive states asserted to come from one run. $\square$

## 171. A separately commissioned source-owned preparation port

**Assumption 171.1 (phase, memory, work and repeated-use contract).**
Fix the same actual native source, preparation supplier and acquired
backing as in VIII161 and VIII166.1, at either authentic entrance of
V25.1. Its private preparation phase is a fixed real $t$ for the
continuation considered here. The finite targets remain (IX.1). Supply
the following additional source-owned port, beyond the existing native
syntax, ingress and number-preserving $P/B$ catalogue.

Acquire a distinct actual two-level preparation memory $M$, initially
$|0\rangle$, and retain its identity, ownership and state throughout
the run. It is not the native phase-reference qubit $r$, a source vertex,
an immutable sample, or a replacement source. The owner can couple $M$
to a named acquired physical qubit $Q$. On the full space $M\otimes Q$
the port has the unitary $U_t$ specified below, tensored with identity
on every untouched reference. A fresh emission uses a genuinely fresh
$Q$ in independent vacuum. Reuse of a dirty $Q$, if separately
authorized, uses the same full unitary, without the vacuum-input formula.

The port is driven by the original supplier's phase, with the same
phase convention as $A_1(t)=e^{it}X$. Its two blocks share that calibrated
phase. A public call names the acquired port, endpoints and an enabled
control slot; it does not contain $t$ and returns no private phase label.
The source retains its actual phase-bearing backing and preparation
memory. Mathematical conditioning on $t$ grants no read authority.
An actual readable timing, calibration, work or control channel belongs
to the complete record and cannot be removed by calling it private.
The parameter describes this supplier's fixed analog phase coupling;
the contract does not encode an arbitrary real $t$ into a finite
orthogonal program register or provide a universal programmable phase
processor from a finite unknown quantum token.

For each declared finite adaptive continuation, supply the real coupling,
work/energy source, phase standard and retention, control description,
calibration, fresh blanks, detector readiness, allocation, whole-bank
holds and progress. At fixed $t$ their complete calibrated joint action
on the addressed systems is $U_t$, including arbitrary correlations with
the retained bank and references; any additional resource output has
its true retained state. In this exact ideal contract the untouched
phase/work backing has a specified evolution depending on the executed
control history and $t$, independent of the quantum input to the port.
It can therefore be retained alongside that input without an unlisted
dephasing or information channel. This is a substantive externally
powered preparation hypothesis, not a construction of a finite closed
energy-conserving reservoir with this property.

More explicitly, write $E$ for this retained resource backing. For each
executed port slot $h$ supply its specified trace-preserving resource
map $\mathcal R_h^t$ on $E$. The complete slot map, with all its resource
outputs included, is $\operatorname{Ad}_{U_t}\otimes\mathcal R_h^t$,
up to the fixed factor ordering, and similarly for a partial pulse.
Its public record and actual resource charges are retained. It acts on
arbitrary reference extensions of its stated domain. This factorization
is part of the ideal joint calibration promise, not a consequence of
energy bookkeeping or equality of resource marginals.

Every later call has this same joint action at the same fixed $t$ and
on the actual current $M$. No fresh $M$, phase redraw, hidden reset,
unrecorded replenishment or input-dependent calibration is inserted.
All resource changes, their finite supplies and present authority are
accounted for at that call. This contract quantifies over each finite
commission; it does not posit a fixed finite resource store serving an
infinite execution. If phase drift or a phase update is admitted, its
actual source-owned transition must be included and the fixed-$t$
terminal identities below have their stated restricted domain.

The terminal service is the complete occupation instrument on this very
$M$, with outcomes $0,1$ and their actual projected successors, in the
separate apparatus namespace. Both outcomes finish their own backed
output and Return. A zero-probability branch stays subnormalized zero.
No outcome restores consumed authority or promises another call's
physical readiness.

**Definition 171.2 (full unitary and its calibrated partial pulse).** Put

$$
a=\lambda^{-1/2},\quad b=\sqrt{u/\lambda},\quad
c=3\lambda^{-1/2},\quad d=(u\lambda)^{-1/2}.
\tag{IX.7}
$$

In the displayed memory/output order define

$$
\begin{aligned}
U_t|00\rangle&=a|00\rangle+e^{it}b|11\rangle,&
U_t|11\rangle&=-e^{-it}b|00\rangle+a|11\rangle,\\
U_t|10\rangle&=c|10\rangle+e^{it}d|01\rangle,&
U_t|01\rangle&=-e^{-it}d|10\rangle+c|01\rangle.
\end{aligned}
\tag{IX.8}
$$

A calibrated pulse path $U_t(s)$, $0\le s\le1$, is specified by replacing
$(a,b)$ by $(\cos(s\arccos a),\sin(s\arccos a))$ and $(c,d)$ by
$(\cos(s\arccos c),\sin(s\arccos c))$ in these two blocks. Its
actual executed progress and any enabled pause are part of the supplied
control contract. Partial execution retains that partial unitary's
state and pending obligations. The exact real constants specify an ideal
port; they are not asserted to be finite signed-dyadic $P/B$ commands.

**Proposition 171.3 (the extra preparation resource is essential to this
port specification).** Formula (IX.8) is unitary on its full four-dimensional
input. It has no dependence on a future terminal horizon. Its vacuum-input
action cannot be inferred from number-preserving $P/B$ operations on
vacuum and classical native operations alone.

Proof. The identities $1+u=\lambda$ and $9+1/u=\lambda$ give
$a^2+b^2=c^2+d^2=1$. Each displayed two-dimensional block is unitary,
and the even and odd subspaces are orthogonal. The same argument applies
to $U_t(s)$. On $|00\rangle$ the output has a nonzero $|11\rangle$
component. V34's $P$ and $B$ preserve total occupation, with $B$
fixing $00,11$; their words preserve vacuum. Native growth adds vacuum
and holds old systems. Such operations cannot produce (IX.8) from vacuum.
An energy/reference resource and its coherent coupling must therefore
be supplied. Occupation charge in this argument is not asserted to equal
the physical holding Hamiltonian or native elapsed time. $\square$

## 172. A causal joint emitter for the exact core

**Theorem 172.1 (horizon-independent joint generation).** Under
Assumption 171.1, use the same $M$ and one fresh independent vacuum
factor per emission. With output before memory, the vacuum restriction is
the isometry

$$
\begin{aligned}
W_t|v\rangle&=\sum_{i=0}^1|i\rangle\otimes K_i(t)|v\rangle,\\
H&=\operatorname{diag}(1,u),\qquad
K_i(t)=\lambda^{-1/2}H^{1/2}A_i(t)H^{-1/2},\\
K_0&=\lambda^{-1/2}\begin{pmatrix}1&0\\0&3\end{pmatrix},\qquad
K_1(t)=\lambda^{-1/2}e^{it}
 \begin{pmatrix}0&1/\sqrt u\\\sqrt u&0\end{pmatrix}.
\end{aligned}
\tag{IX.9}
$$

Starting at $M=|0\rangle$, after $n$ uninterrupted emissions the actual
retained vector on the first $n$ factors and that original memory is

$$
|\Omega_n(t)\rangle
 =\lambda^{-n/2}\left(
 |\psi_{n,00}(t)\rangle\otimes|0\rangle_M
 +\sqrt u\,|\psi_{n,01}(t)\rangle\otimes|1\rangle_M\right).
\tag{IX.10}
$$

All other held systems and the specified source-owned resource outputs
remain alongside this vector with their true identities and correlations.
If their initial conditional state is $\eta_{ER}$, their actual state
at this uninterrupted cut is

$$
|c_n\rangle\langle c_n|\otimes
 |\Omega_n(t)\rangle\langle\Omega_n(t)|\otimes
 \left((\mathcal R_{n-1}^t\circ\cdots\circ\mathcal R_0^t)
       \otimes\mathrm{id}_R\right)(\eta_{ER}),
\tag{IX.10a}
$$

with the identity resource map at $n=0$ and the actual common classical
configuration $c_n$. Any other commissioned hold or resource step is
included in that composition. Pure initial $M$ and fresh vacuum inputs
justify this conditional factorization; averaging a common unknown phase
retains the resulting full mixture.
In particular the emitted-bank densities
$\tau_n=\operatorname{Tr}_M|\Omega_n\rangle\langle\Omega_n|$ satisfy
$\operatorname{Tr}_{n+1}\tau_{n+1}=\tau_n$. They differ from the
finite pure targets $\rho_n$.

Proof. Direct multiplication gives

$$
\sum_i A_i(t)^\dagger H A_i(t)=\lambda H,
\qquad \sum_i K_i(t)^\dagger K_i(t)=I.
\tag{IX.11}
$$

Thus (IX.9) is an isometry and is exactly (IX.8) on the blank input.
The chronological coefficient of output $w_1\cdots w_n$ and final
memory $j$ is

$$
\langle j|K_{w_n}\cdots K_{w_1}|0\rangle
 =\lambda^{-n/2}\sqrt{H_{jj}}\,
    e_j^{\mathsf T}A_{w_n}\cdots A_{w_1}e_0
 =\lambda^{-n/2}\sqrt{H_{jj}}\,\psi_{n,0j}(t)(w).
\tag{IX.12}
$$

The last equality uses the transpose symmetry of each $D$ and $e^{it}X$;
it neither reverses the acquired physical roster nor takes a complex
conjugate of the phase. Summing the two memory coefficients proves
(IX.10). Its norm is one either by isometry or by
$a_n+u b_n=\lambda^n$. Subsequent isometric operations act only on
the current memory and new blanks. After tracing these systems they
cannot change an old output marginal. This proves prefix consistency.
For $n\ge1$, tracing $M$ in (IX.10) has a positive odd-parity block,
whereas $\rho_n$ does not. $\square$

## 173. Both terminal outcomes and their continuing successors

**Theorem 173.1 (exact flagged finite target with all branches retained).**
At an uninterrupted, fixed-$t$, $n$-emission cut of Theorem 172.1, the
complete terminal output on the declared quantum factors is

$$
\sum_{j=0}^1 |h_{n,j}\rangle\langle h_{n,j}|
 \otimes\frac{H_{jj}}{\lambda^n}
 |\psi_{n,0j}(t)\rangle\langle\psi_{n,0j}(t)|
 \otimes|j\rangle\langle j|_M.
\tag{IX.13}
$$

Here $h_{n,j}$ includes the actual source, acquired roster, port and
preparation binding, control, resource and detector records, and completed
or pending delivery fields at the cut specified. Untouched backing and
references are retained as in Assumption 171.1; (IX.13) suppresses their
tensor factors only when that assumption supplies their conditional
independence. The branch probabilities at every $n\ge0$ are

$$
p_0(n)=\frac{a_n}{\lambda^n}
       =\frac{1+u^2q^n}{1+u^2},\qquad
p_1(n)=\frac{u b_n}{\lambda^n}
       =\frac{u^2(1-q^n)}{1+u^2}.
\tag{IX.14}
$$

For $n\ge5$, outcome zero returns exactly the original $\rho_n(t)$
on the same emitted physical factors and leaves the original $M$ in
$|0\rangle$. Outcome one returns the normalized odd-endpoint state
$|\psi_{n,01}\rangle\langle\psi_{n,01}|/b_n$ and leaves that same
$M$ in $|1\rangle$. It is not a missing outcome, reset instruction,
or certification that the next finite block will be $\rho_k(t)$.
Both probabilities are positive for $n\ge1$, and

$$
\inf_{n\ge5}p_0(n)=\frac1{1+u^2}>0.
\tag{IX.15}
$$

Proof. Apply both memory projectors to (IX.10), retaining their actual
classical labels. Orthogonality gives (IX.13), whose traces are (IX.14)
by (IX.6). The two traces sum to one, so no branch has been discarded.
Their normalized states and the infimum follow immediately. The only
zero branch in the stated range $n\ge0$ is outcome one at $n=0$;
it has no assigned normalized successor. $\square$

**Theorem 173.2 (the actual next block after a terminal readout).**
Suppose a positive terminal branch has left the memory in $|a\rangle$.
Hold its entire old output and records. With the same fixed-phase port,
fresh blanks and no intervening quantum operations, a further block of
$k$ emissions followed by the complete terminal read has subnormalized
new block/memory output in outcome $b$

$$
\frac{H_{bb}}{H_{aa}\lambda^k}
 |\psi_{k,ab}(t)\rangle\langle\psi_{k,ab}(t)|
 \otimes|b\rangle\langle b|_M.
\tag{IX.16}
$$

The conditional outcome probabilities, with row $b$ and column $a$, are

$$
\mathsf P_k=
\frac1{1+u^2}
\begin{pmatrix}
1+u^2q^k&1-q^k\\
u^2(1-q^k)&u^2+q^k
\end{pmatrix}.
\tag{IX.17}
$$

For any prescribed finite sequence of such block lengths
$k_1,\ldots,k_m$ and outcomes $a_1,\ldots,a_m$, with $a_0=0$,
the full joint outcome probability is
$\prod_{\ell=1}^m(\mathsf P_{k_\ell})_{a_\ell a_{\ell-1}}$.
At fixed $t$, the conditional retained block states are exactly the
successive normalized versions of (IX.16), with their complete records
and all old systems still present. For adaptively selected finite block
lengths the same product holds along the selected record path, with
those actual lengths, while any external random control law must also
be retained.

Proof. Replace the initial $e_0$ in (IX.12) by $e_a$. The coefficient
becomes $\lambda^{-k/2}\sqrt{H_{bb}/H_{aa}}\psi_{k,ab}(t)(w)$.
Its squared norm is
$H_{bb}(T^k)_{ab}/(H_{aa}\lambda^k)$. Diagonalizing $T$ as in
(IX.6), including $(T^k)_{11}=(u^2\lambda^k+\mu^k)/(1+u^2)$,
gives every entry of (IX.17). A rank-one memory read separates its
actual eigenstate from the old conditional bank. Applying the same
input-independent port on the fresh systems proves the asserted
conditional block state and the chain-rule product by induction.

In particular, the two probabilities for a later outcome zero are
$(1+u^2q^k)/(1+u^2)$ and $(1-q^k)/(1+u^2)$ according to the
previous outcome. They differ for every finite $k$. The run is not a
sequence of independent trials. Starting from $a=1$, a later outcome
zero produces $\psi_{k,10}$, with odd support, rather than the original
even target. Formula (IX.15) by itself supplies no expected expenditure,
independent retry law, deterministic success, or readiness of a new
physical call. Averaging over an unknown common $t$ retains a mixture
of these joint block states, not a product of separately averaged
blocks. $\square$

## 174. An operator-valued joint boundary with explicit updates

**Definition 174.1 (the retained boundary at an actual cut).** At a
finite actual native/apparatus record $h$, let $c_h$ contain the complete
classical configuration: authentic source/root binding and preparation,
native material and successful-event journal, actual source/acquisition
versions, immutable samples, acquired occurrence/port/reference roster,
current grants and locks, parser, control and detector latches, delivered
record prefix, unprinted suffix and the exact owed actions. Source phase
backing is retained with its actual ownership; a private parameter is
not inserted into the public record.

Let $\mathcal B_h$ be the tensor product of every retained quantum factor
other than the original $M$, including emitted old factors, unused
acquired factors, true physical exteriors, spent probes, references and
apparatus/resource systems. For a specified finite commission these are
finite interfaces; classical fixed parameters may be conditioned on.
Write the actual positive subnormalized joint state as

$$
\omega_h=\sum_{b,c=0}^1 O_{bc}^{h}\otimes|b\rangle\langle c|_M,
\qquad
\mathfrak B_h=(c_h,(O_{bc}^{h})_{b,c=0}^1).
\tag{IX.18}
$$

Its weight is $\sum_b\operatorname{Tr}O_{bb}^{h}$. This is a block
representation of the actual joint quantum state, not four classical
readouts, a tomography oracle or an entitlement to read private backing.
Before any intervention its source-specific entries are

$$
O_{bc}^{(n)}=
\lambda^{-n}\sqrt{H_{bb}H_{cc}}\,
 |\psi_{n,0b}(t)\rangle\langle\psi_{n,0c}(t)|,
\tag{IX.19}
$$

tensored with independent held backing only where its preparation
contract permits. A random fixed phase is described by the same actual
classical-quantum conditional kernel and its common phase distribution;
one does not average the blocks independently of their backing.

**Theorem 174.2 (source-specific joint boundary for finite adaptive
continuations).** Under V25–29, V36.1 and Assumption 171.1, the boundary
(IX.18) is sufficient to compose every declared finite adaptive tree of
the following operations on its actual acquired references: native
service and growth, full-qubit $P/B$ words and occupation instruments,
the commissioned full port and its supplied pending pulse cuts, fresh
emissions, and terminal memory reads. Any additional already supplied
instrument can be included on its actual full input domain. The
sufficiency includes the complete record and actual quantum/native
successor of every branch, with these explicit updates:

For a fresh emission into a vacuum $Q$, with $Q$ appended to
$\mathcal B_h$, first set

$$
\widetilde O_{jk}^{h'}=
\sum_{b,c=0}^1\sum_{i,l=0}^1
(K_i)_{jb}\overline{(K_l)_{kc}}\,
O_{bc}^{h}\otimes|i\rangle\langle l|_Q.
\tag{IX.20}
$$

and then apply the specified resource evolution
$O_{jk}^{h'}=(\mathcal R_h^t\otimes\mathrm{id})(\widetilde O_{jk}^{h'})$
on its actual resource factors. Identity factors and fixed permutations
in this notation leave every other bank/reference system present.

For an actual observed instrument outcome $z$ acting on retained factors
other than $M$, with hidden index $\gamma$,

$$
O_{bc}^{h,z}=\sum_\gamma L_{z\gamma}O_{bc}^{h}L_{z\gamma}^\dagger.
\tag{IX.21}
$$

For a full port operation on an existing possibly dirty $Q$, write
$U_t=\sum_{j,b}U_{jb}^{(Q)}\otimes|j\rangle\langle b|_M$, after
the fixed factor permutation. Its update is

$$
\widetilde O_{jk}^{h'}=\sum_{b,c=0}^1
 U_{jb}^{(Q)}O_{bc}^{h}(U_{kc}^{(Q)})^\dagger.
\tag{IX.22}
$$

Apply the same specified $\mathcal R_h^t$ to these blocks. The expression
uses the actual $U_t(s')U_t(s)^\dagger$ and its own resource map for an
executed partial pulse. A terminal memory outcome $a$ retains only
$O_{aa}^{h}$ in memory block $(a,a)$, records $a$, and retains
$|a\rangle_M$. Native growth uses the actual full-bank vacuum extension
$O_{bc}\mapsto V O_{bc}V^\dagger$ with its actual $c_h\mapsto c_{h'}$;
native holds and classical output steps keep the blocks unchanged.

Proof. Inserting (IX.18) into $(I\otimes W_t)\omega_h(I\otimes W_t)^\dagger$
and collecting memory matrix units gives (IX.20). The same multiplication
gives (IX.21)–(IX.22) and the memory-projector rule. Thus the off-diagonal
blocks, source-memory correlations and old/new correlations are retained
at every node, including after arbitrary earlier observed disturbances.
These are full input formulas; only the fresh-emission restriction uses
the separately certified independent vacuum.

Equation (IX.11), full unitarity, the specified trace-preserving resource
maps, complete occupation instruments and V36.1's full-space growth
each preserve the sum of branch traces.
Hidden Kraus indices are summed, whereas observed outcomes select the
next actual instruction. The finite instrument composition of V29.2
then gives the normalized full output

$$
\sum_{h\in\operatorname{Leaves}}|h\rangle\langle h|\otimes\omega_h,
\qquad \sum_h\operatorname{Tr}\omega_h=1.
\tag{IX.23}
$$

Pending cuts are leaves when selected: their actual partial map,
configuration and owed suffix are used, without substituting a completed
service. A finite tree has a finite union of its branch resources;
unused coordinates can be held in vacuum. This is a proof interface
for that finite tree, not a capacity restriction on later native growth.
Equality of the initial complete boundaries, source-owned port contracts
and external control inputs makes every update equal, hence all complete
future outputs equal. It does not say equality of just a bank marginal
or a classical record suffices.

This reuses the finite instrument supplier
[FiniteCausalScheduleProtocol.program_graph_correspondence](../../../D5/S3/Quantum/Dynamics/FiniteCausalScheduleProtocol.lean)
in precisely V29.2's finite-interface role. The new interface data here
are the original phase core, its actual $M$ and the explicit operators
(IX.19)–(IX.22). Neither a general behavior quotient nor its cardinal
minimality supplies these physical data. $\square$

## 175. A legal early read changes the flagged target

**Proposition 175.1 (an actual disturbed successor with unchanged terminal
probability).** Start at the preparation of Theorem 172.1, emit the
first factor, read its occupation with V25.1's actual detector, retain
the result, and continue emitting to a fixed $N\ge5$. Perform the
terminal memory read. Its outcome-zero probability is still $p_0(N)$,
but its conditional complete record/bank state is

$$
\sum_{z=0}^1|z\rangle\langle z|\otimes
 \Pi_z^{(1)}\rho_N(t)\Pi_z^{(1)},
\tag{IX.24}
$$

with $M=|0\rangle$ and all other retained outputs alongside it. Even
after forgetting $z$, this is the first-factor pinching of $\rho_N(t)$,
and is different from $\rho_N(t)$. Conditional on $z=1$ and terminal
zero, the first retained factor is certainly occupied. Both that branch
and the $z=0$ branch have positive probability.

Proof. The early projectors act on the already emitted factor and
commute with every subsequent $W_t$ on the memory and new blanks.
Apply each projector to (IX.10), then apply the terminal projector.
This gives the unnormalized branches
$\lambda^{-N}\Pi_z^{(1)}|\psi_{N,00}\rangle
\langle\psi_{N,00}|\Pi_z^{(1)}$. Their traces sum to
$a_N/\lambda^N$, proving (IX.24). The words $0^N$ and $110^{N-2}$
both have nonzero amplitude, so pinching removes a nonzero cross term.
The two joint branch probabilities are, explicitly,

$$
\Pr(z=0,M=0)=\frac{a_{N-1}}{\lambda^N},\qquad
\Pr(z=1,M=0)=\frac{b_{N-1}}{\lambda^N}.
\tag{IX.25}
$$

They are positive. On the second branch the unnormalized new suffix
is the actual $\psi_{N-1,10}$ of (IX.16), preceded by the measured
$|1\rangle$. In contrast the original target has first-factor-zero
probability $a_{N-1}/a_N>0$. This gives a permitted later occupation
consumer separating that disturbed branch from the original target.
$\square$

**Proposition 175.2 (terminal transport with the intervention retained).**
Consider a fixed finite record path with $N$ fresh emissions, no
intermediate operation on $M$, a fixed phase, and interventions only
on already emitted factors and held references. Include their actual
native vacuum extensions and roster identifications. Let $\mathcal J_h$
be the path's composed completely positive map on the terminal retained
bank/reference space, including its specified resource maps and lifting
each earlier operation by identity on factors not yet emitted. If the
old backing is initially $\eta_R$
independent of $M$, its terminal branch $a$ has state

$$
\frac{H_{aa}}{\lambda^N}
\mathcal J_h\left(
 |\psi_{N,0a}(t)\rangle\langle\psi_{N,0a}(t)|\otimes\eta_R
\right)\otimes|a\rangle\langle a|_M.
\tag{IX.26}
$$

This is a branchwise identity; its trace is the actual joint probability
of $h,a$. It does not replace that trace by (IX.14) or replace its
normalized state by the original target.

Proof. On a fixed observed path the earlier Kraus operators act on
disjoint factors from every later emission, even when the state is
entangled. Commute them past those emissions, without changing their
order relative to other interventions, and sum any hidden Kraus indices.
Native vacuum extension identifies the same actual acquired factors,
so V36.1 permits this reordering as an operator calculation. The
terminal projection then gives (IX.26) by (IX.10). A different observed
path may choose different operators, lengths and native successors;
it has its own $\mathcal J_h$, not a common postselected state. If
an intermediate memory read, dirty-input port call or phase update is
present, use (IX.20)–(IX.22) on the actual successor instead. $\square$

## 176. Mounting the emitter without changing authentic native service

**Theorem 176.1 (actual occurrence continuation and original projection).**
Under V25.1's actual commissioning, V27.2/V36.1's full-space service,
the source-owned port contract and sufficient finite resources/progress,
each finite adaptive continuation in Theorem 174.2 can use the same
actual native source on either authentic entrance. Its emissions occupy
an acquired ordered roster of genuine occurrence qubits. Both terminal
outcomes, all legal disturbed successors and every original finite
native continuation remain available with their actual domains and
current rights. Its projection to the original source process preserves
the entire original service, including genuine addressed $P/S/\operatorname{Next}$.

Proof. At returned native Ready, acquire the actual root and existing
source/component binding, saving borrowed cursors. For the finite
entrance retain its actual prehistory and preparation. For the bilateral
entrance traverse the real headers to selected roots, retaining their
individual empty or $P_\varepsilon$ preparations. Commission the actual
components by V25.2; an integer index is not cast into a reference.
Acquire the preparation-memory and port references separately with their
own grants. The port couples these real references, not an inferred
source edge.

For each needed fresh emission slot reuse V39.2's concrete finite native
growth: navigate to a real leaf, promote it if it is alpha, split the
resulting beta, and acquire the genuine fresh right child's descriptor.
Continue from that actual right child when more slots are needed.
Each such qubit is QNew vacuum, independent of the held old bank.
V36.1 preserves it through subsequent full-space holds and growth.
Retain the actual tuple $(F,c,x,q_x)$, first acquisition and current
versions, current role and retention/control rights. The order in this
paid roster is tensor-factor/emission order. It is not native ancestry,
native distance, successful-event count or physical elapsed time.

Invoke the port only through its acquired endpoints and enabled current
control. Fresh-vacuum calls give (IX.9), while authorized dirty-input
calls have (IX.8)'s actual full-space successor. Unused fresh slots,
spent measured factors, all old exterior systems, supplier backing and
the continuing $M$ remain in the bank. Following a terminal outcome,
continue with that outcome's memory and newly acquired slots. No old
bank, unknown state, source root or immutable record is reset or swapped
for another to enforce a target promise.

The classical phase relation is V27.2's relation on identical actual
native fields, tapes, preparations, grants and pending/output fields,
extended by the actual port state and records. Every original Receive
prefix and parser mark is retained. Navigate/Guard follows the same
logical links and birth facts; beta's marker is not traversed as an
addressable logical child. Tag reads the actual logical-address
constructor or absence, not a quantum label or roster position.
Promotion/split tests, original refusals, OutOfRange and BadFrame keep
their original operands and meanings. Missing authority or wrong phase
leaves the protected primitive unexecuted; an available grant-denial
transition keeps its distinct actual denial record.

Reserve/edit/maintain retains its actual target, recalled pair, reserved
references and unfinished native/tape/attachment writes. Its quantum
action is full-bank hold with the genuine fresh vacuum extension,
including on all disturbed states from (IX.21)–(IX.22). Only the
completed actual source/acquisition pair is published. FetchGrowth
uses the original journals. Next internally recalls its real historical
kind/address, follows that still-existing address, descends current
logical left children, and executes the actual guard-selected edit.
It creates no external Recall reply or extra ACK. Neither emission nor
an apparatus outcome substitutes a preferred edit or reorders native
history. The ordered $\alpha/\beta$ bracket syntax is unchanged.

Every added transaction starts in its disjoint apparatus namespace from
an enabled native Ready cut and saves the original continuation. At a
pending port pulse or detector operation, retain the actual partial
unitary/projector state, active references, progress/latch fields,
held dirty bank and owed control/output suffix. At a pending native
operation retain that operation's actual parser, traversal, edit or
output microstate. A complete terminal formula is not assigned to
either pending cut. Source-owned phase/work resources retain their
actual specified evolution and every observable output joins $h$.

Each completed original or extra answer has its own real backed word,
sealing, Print, End, local ACK, same-root Return and charged scratch
clearing. Hold the entire bank through those phases. Immutable samples,
source history, acquisition records and occupied retained quantum
systems are not scratch. The actual emitted prefix and unprinted
suffix remain until their corresponding obligations are discharged.
Return does not restore preparation/detector authority or clean a
disturbed memory. Requests for further native service retain their
original supplied material/progress premises, regardless of terminal
flag or prior quantum disturbance.

These cases verify the concrete extension of V27.2, rather than assuming
a source correspondence from equal probability laws. Induction over
the finite actual phase steps proves the original projection. The
quantum component at each step is exactly (IX.20)–(IX.22) or the
full-space native hold/extension, so the same induction identifies its
complete joint successor with (IX.23). All allocation, original growth,
source traversal, blank and memory preparation, controls, phase/work
resources, calibration, detectors, computation, records, duration and
holds have their separate costs. This is a finite constructive schedule,
without a total-cost minimum or an infinite-bank assumption. $\square$

**Proposition 176.2 (the flagged supplement retains the deterministic
native recovery).** AAII96.2/97.2 and IV16's positive recovery on the
supplemented returned actual native image remains in force: space
$(S_0,J)$, boundary $(B_0,J)$, successful generation word and retained
callable memory recover the same actual semantic source/history under
the full original $Q_g$, including Next. The extra port supplies the
joint physical continuation boundary (IX.18) for its declared finite
menu. It does not replace those deterministic full-input promises by
a conditional successful flag.

Proof. Theorem 176.1 preserves the actual native fields, journal, current
authority and entire service projection on both outcomes and on pending
or disturbed paths. The inverse routes in AAII97.2 and IV16 therefore
refer to that same retained native source/history. Extra port and
detector records and quantum states are additional fields; (IX.18)
retains them jointly with the native fields and (IX.20)–(IX.22) update
them on the actual path. Theorem 170.2 obstructs an unchanged-prefix
interpretation of the separate pure physical targets, not the existing
supplemented native inverse. Neither bare geometry nor the two-level
memory alone recovers the serial journal or the acquired quantum
record. $\square$

## 177. Suppliers, preparation hypotheses and recovery boundaries

**Definition 177.1 (scoped mathematical attribution).** The isometry
condition and sequential matrix-product expansion are mature intermediate
tools: Schön, Solano, Verstraete, Cirac and Wolf,
[*Sequential generation of entangled multi-qubit states*,
quant-ph/0501096v1, equations (1)–(5)](https://arxiv.org/html/quant-ph/0501096v1),
give the sequential isometry expansion and a finite-target SVD generation
recipe whose last ancilla decouples. That finite-horizon recipe does not
identify all finite endpoints as one unchanged-prefix source. Cirac,
Perez-Garcia, Schuch and Verstraete,
[*Matrix product states and projected entangled pair states: Concepts,
symmetries, theorems*, 2011.12127v2, §II.2.3 and §II.2.5,
Figure 9(a)](https://arxiv.org/html/2011.12127v2),
supply the positive transfer-fixed-point and canonical-gauge/circuit
interpretation used inside (IX.9)–(IX.12). These are
`literature-attested` suppliers, not new generic generation theorems or
physical preparation-port grants.

The exact orbit's prefix distance (IX.3), its finite occupation benchmark,
the explicit original-endpoint joint emitter and terminal/successor
formulas (IX.8)–(IX.17), and their acquired-source intervention
correspondence (IX.18)–(IX.26) are `repo-derived` calculations on
VIII157's specified core and V25–39's actual mounting. This attribution
asserts no literature priority. V29.2 supplies finite instrument
composition; VI54.1/54.2 require full-input branch identities and actual
returned outputs; VI67.2 supplies joint, reference-retaining error
accounting when the necessary certificates exist. VI68/69's classical
observation kernel does not identify its quantum outputs, and is not
extended to the new port without checking its complete maps.

Context Geometry §42 already treats joint sequential sources, passive
coherent reception, intervention failures and distinct retained-record
capacity. Joint-Kernel Minimal Predictive Core §§1–2 and Law Run Residual
§§1–2 distinguish complete-future law quotients from acquired one-run
records. Their predictive-state counterparts include
[PredictiveSufficiencyDescent](../../../D5/S3/ObserverMemory/RefinementDescent/PredictiveSufficiencyDescent.lean)
and the finite controlled-realization statement in
[ControlledBehaviorUniversality](../../../D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean).
No generic quotient, finite-state minimum or passive-receiver theorem
is reasserted here as the missing source port. Those suppliers' hypotheses
do not follow merely from the two-dimensional active memory in (IX.9).

**Definition 177.2 (exact recovery scope).** The source-specific mathematical
conclusions concern a fixed phase, the stated full ideal port contract,
its actual continuing memory and each finite declared adaptive
continuation with current rights, resources and progress. A flagged
terminal zero recovers the original finite target only on the
uninterrupted domain of Theorem 173.1. The joint boundary retains all
disturbed successors; it gives their finite future laws and states,
without inferring a native journal from a physical marginal or an
unknown phase from a finite record.

The active bond dimension is two. The retained bank, native source,
phase/work backing, quantum references, immutable samples, complete and
pending records, controller, counters, calibration and current rights
are additional memory/resources. The four operator blocks in (IX.18)
act on that growing bank, not on a fixed four-dimensional observer.
No minimality of the joint boundary or of total retained memory follows.

An installed physical realization of Assumption 171.1, finite-resource
accuracy and drift certificates for it, source-faithful acquisition of
its private phase/work standard, and an all-future sufficient compression
smaller than the retained joint boundary are separate obligations. With
only the already supplied number-preserving $P/B$ and native syntax,
this port has not been granted. With approximate apparatus, comparison
must bound the complete joint output at each executed cut as in V29.2
and VI67.2; a scalar success probability or a resource-marginal error
cannot replace that bound. No fixed-noise robustness, deterministic
preparation, finite expected cost, unlimited reference reuse, universal
clock, bare four-view recovery or completion of the enduring mutual
recovery objective is entailed by these finite conditional conclusions.

## 追加锚（本行以下为增补区）

## 178. A finite source-owned commission and its separate phase premise

**Definition 178.1 (finite resource interface).** Keep the actual source,
its phase $t$, $u,\lambda,H$, the continuing acquired memory $M$ and
all native fields of §§170–177. Fix integers $K\ge1$ and $L\ge2$.
Commission at most $K$ executed port increments along each path of a
specified finite adaptive tree. An increment includes an executed
partial pulse; it need not be a completed emission. Acquire a distinct
resource $B$ with basis $|r\rangle$, $0\le r\le R_B$, where

$$
R_B=2K+L-1,\qquad N_B=\sum_{r=0}^{R_B}r|r\rangle\langle r|.
\tag{IX.27}
$$

Here $B$ is a resource register, not the native boundary $B_0$, a new
source, an old occurrence qubit or the preparation memory $M$.
Resource retention, port coupling, resource readout and resource
preparation are four separately typed permissions on its actual binding.
Port permission alone does not permit arbitrary operations on $B$.
Every operation below acts by identity on arbitrary untouched references.
All spent controls, preparation backing and readable apparatus outputs
are retained with their actual identities. The full finite dynamics
will be defined even for dirty $M,Q,B$ and their correlations; only
particular accuracy and emission formulas need the calibration below.

**Assumption 178.2 (source-owned preparation and protected holds).** In the
same calibrated frame as VIII159, suppose the original supplier can
actually prepare, at fixed $t$, the acquired $B$ in

$$
\begin{aligned}
\vartheta&=\frac{\pi}{L+1},&
g_{K+j}&=\sqrt{\frac2{L+1}}\sin((j+1)\vartheta)
       \quad(0\le j<L),\\
g_r&=0\quad\text{otherwise},&
|g_t\rangle&=\sum_{r=0}^{R_B}g_r e^{irt}|r\rangle.
\end{aligned}
\tag{IX.28}
$$

At the entrance to the calibrated comparison, its conditional joint state
is $|g_t\rangle\langle g_t|_B\otimes\rho_{AR}$, where $A$ includes
$M$, all dirty port inputs, old banks, source backing and other apparatus,
and $R$ is an arbitrary untouched reference. The state $\rho_{AR}$ is
otherwise unrestricted. The uninterrupted fresh-emission calculation
additionally uses the original $M=|0\rangle$ and genuine independent
vacuum slots. An imperfect preparation is treated by one complete joint
initial bound in §182, not by asserting factorization from a resource
marginal. Conditioning on a common unknown $t$ is mathematical notation;
the actual experiment retains the common mixture and phase-bearing
backing, with its original access restrictions.

Supply the finite couplings of §179, controls and their actual partial
progress, retention and detector readiness. Between port increments the
protected hold on $B$ is identity in this frame, including any required
paid compensation. Other backing has the specified input-independent
joint resource evolution of Assumption 171.1, tensored with identity on
$B$; all its outputs remain. Thus no undeclared clock, phase drift,
resource measurement, leakage or source-dependent control label is
hidden in a hold. Accuracy of a nonideal hold is separately chargeable.
These are modeled same-source preparation/coupling/hold premises, not
claims of installed hardware or acquired permission. The finite quantum
state (IX.28) is not itself a native acquisition procedure.

The phase in (IX.28) supplies a first charge harmonic: lowering its
level once approximates multiplication by $e^{it}$. This is an extra
phase interface. The original even-support targets satisfy
$\rho_n(t+\pi)=\rho_n(t)$, whereas for $L\ge2$ the resource densities
in (IX.28) at $t$ and $t+\pi$ differ: adjacent occupied levels have a
nonzero coherence whose sign changes. A fixed channel supplied only
those identical finite target densities cannot produce both distinct
resource densities. This elementary obstruction does not apply to an
additionally accessed original supplier/phase backing; that extra access
is exactly what the preparation premise must supply. No first-harmonic
acquisition is inferred from VIII157–169's even-mode target laws.

## 179. A full dirty-input finite port with actual boundary successors

**Definition 179.1 (two rotations on finite charge sectors).** Put
$\theta_0=\arccos a$ and $\theta_1=\arccos c$, with $a,b,c,d$ as in
(IX.7). For every $1\le r\le R_B$, let $V(s)$ act on the ordered pairs

$$
\begin{aligned}
(&|00\rangle_{MQ}|r\rangle_B,
  |11\rangle_{MQ}|r-1\rangle_B),\\
(&|10\rangle_{MQ}|r\rangle_B,
  |01\rangle_{MQ}|r-1\rangle_B)
\end{aligned}
$$

by the matrices

$$
\begin{pmatrix}\cos(s\theta_j)&-\sin(s\theta_j)\\
                \sin(s\theta_j)&\cos(s\theta_j)\end{pmatrix},
\qquad j=0,1,
\tag{IX.29}
$$

respectively. It fixes the four unpaired vectors
$|00,0\rangle$, $|10,0\rangle$, $|11,R_B\rangle$ and
$|01,R_B\rangle$. These are actual boundary actions, not discarded
failure branches. The unitary has no classical parameter $t$; the phase
is in the source-owned resource state. A supplied pulse from progress
$s$ to $s'$ executes $V(s')V(s)^\dagger=V(s'-s)$, with the same
$M,Q,B$ and all pending obligations retained. Normally $0\le s\le
s'\le1$; signed increments $|s'-s|\le1$ may also be commissioned.
No completed gate is substituted at a pending cut.

**Theorem 179.2 (complete dynamics, conservation and finite guard).** The
maps (IX.29) are unitaries on the entire $M\otimes Q\otimes B$.
They form a one-parameter group and commute with

$$
C_{QB}=N_Q+N_B,\qquad N_Q=|1\rangle\langle1|_Q.
\tag{IX.30}
$$

No charge is assigned to the label of $M$ in this conservation statement.
For an arbitrary dirty-input joint state $\omega_{MQB\mathcal B R}$,
the executed successor is exactly

$$
(V(s'-s)\otimes I_{\mathcal B R})\omega
 (V(s'-s)^\dagger\otimes I_{\mathcal B R}),
\tag{IX.31}
$$

with its actual resource/control outputs alongside it. There is no
trace over $B$ in this definition. Starting with support (IX.28), any
path of at most $K$ increments, interleaved with operations acting on
factors other than $B$, has the same action as the shift formulas below;
none of its nontrivial rotations is truncated by a boundary.

Proof. The displayed pairs and four unpaired vectors partition an
orthonormal basis. Each pair has the same value $r$ of $N_Q+N_B$;
its rotation is unitary and additive in $s$. This proves all operator
claims, including on correlated inputs after tensoring with identity.
Every port increment moves resource support by at most one level in
either direction. Before increment $j\le K$, its support is contained
in $[K-j+1,K+L+j-2]\subseteq[1,R_B-1]$. An operation on other
factors, including an observed conditional operation, cannot introduce
new resource support. Hence the input to every such increment avoids
the four unpaired endpoints. The last output may reach an endpoint;
it is still retained. Outside this guard or calibration the full
finite unitary (IX.29), including its fixed endpoints, remains the
specified successor whenever its control is authorized and backed.
$\square$

For example, away from the endpoints the full completed action includes

$$
\begin{aligned}
|00,r\rangle&\mapsto a|00,r\rangle+b|11,r-1\rangle,\\
|11,r\rangle&\mapsto-b|00,r+1\rangle+a|11,r\rangle,\\
|10,r\rangle&\mapsto c|10,r\rangle+d|01,r-1\rangle,\\
|01,r\rangle&\mapsto-d|10,r+1\rangle+c|01,r\rangle.
\end{aligned}
\tag{IX.32}
$$

These are both IX blocks on their full input, including absorption from
a dirty occupied $Q$. A fresh-vacuum formula would omit half this
interface. Resource states and all memory off-diagonal blocks must be
propagated by (IX.31) on such inputs; a fresh-resource substitution after
a call is not its successor.

## 180. Exact source-specific resource shifts and both terminal returns

**Definition 180.1 (finite shifts and their overlaps).** Extend $g_r$ by
zero outside its displayed support. For $0\le k\le K$ define the
normalized vector on the actual finite resource

$$
|g_t;k\rangle=\sum_{r=0}^{R_B}g_{r+k}e^{irt}|r\rangle,
\qquad
G_m=\sum_{r\in\mathbb Z}g_r g_{r+m},\quad G_{-m}=G_m.
\tag{IX.33}
$$

The zero extension is notation, not an infinite physical reservoir.
These vectors obey $\langle g_t;l|g_t;k\rangle=G_{k-l}$.
They are the phase-corrected $k$-step lowered resources: the uncorrected
lowering sends $|g_t\rangle$ to $e^{ikt}|g_t;k\rangle$.
The sine profile gives

$$
G_0=1,\qquad G_1=\cos\vartheta,\qquad
G_2=1-\frac{2L}{L+1}\sin^2\vartheta<1,\qquad
G_m=0\ \text{for }|m|\ge L.
\tag{IX.34}
$$

Indeed the finite-chain recurrence
$g_{r-1}+g_{r+1}=2\cos\vartheta\,g_r$ on the $L$ occupied
coordinates gives $G_1$. Squaring that recurrence and summing gives
$4\cos^2\vartheta=2-4\sin^2\vartheta/(L+1)+2G_2$,
which proves the stated $G_2$. The other identities follow from
normalization, reality and support.

**Theorem 180.2 (joint IX emission and complete terminal law).** Under
Assumption 178.2, start with $M=|0\rangle$ and perform $n\le K$
uninterrupted completed fresh emissions. On the ordered emitted bank,
that same $M$ and $B$, the actual normalized vector is

$$
|\Xi_n(t)\rangle=\lambda^{-n/2}
 \sum_{j=0}^1\sum_{w\in\{0,1\}^n}
 \sqrt{H_{jj}}\,\psi_{n,0j}(t)(w)
 |w\rangle|j\rangle_M|g_t;|w|\rangle_B.
\tag{IX.35}
$$

All other backing is retained in its stipulated joint evolution; tensor
factorization with it is used only where Assumption 178.2 supplies it.
A common random $t$ is averaged jointly with that backing. The complete
terminal memory instrument has the two subnormalized vectors
$|\Xi_{n,j}\rangle=(I\otimes|j\rangle\langle j|_M\otimes I_B)
|\Xi_n\rangle$ and output

$$
\sum_{j=0}^1|h_{n,j}\rangle\langle h_{n,j}|
 \otimes|\Xi_{n,j}\rangle\langle\Xi_{n,j}|.
\tag{IX.36}
$$

The flag probabilities are exactly $p_j(n)$ of (IX.14). For $n\ge1$
both are positive. Conditional on $j$, tracing $B$ gives on the full
emitted bank the entries

$$
(\rho^{g}_{n,j}(t))_{w,v}
 =\frac{\psi_{n,0j}(t)(w)\overline{\psi_{n,0j}(t)(v)}}{Z_{n,j}}
 G_{|w|-|v|},\qquad
 Z_{n,0}=a_n,\quad Z_{n,1}=b_n.
\tag{IX.37}
$$

In particular terminal zero does not return the exact original pure
$\rho_n(t)$ for finite $L$: its nonzero $0^n,110^{n-2}$ coherence
is multiplied by $G_2<1$ when $n\ge2$. The original exact ideal-port
conclusion of §173 remains valid on its own premises.

Proof. On a vacuum slot, (IX.32) uses precisely $K_0(0)$ for output
zero and $K_1(0)$ followed by one lowering for output one. Each new
emission acts on the same $M$. Multiplying its chronological coefficients
as in (IX.12) gives
$\lambda^{-n/2}\sqrt{H_{jj}}\psi_{n,0j}(0)(w)$ and $|w|$
lowerings. Their phase $e^{it|w|}$ gives (IX.35), with the original
ordered physical roster unchanged. The finite guard justifies every
lowering. Each lowered vector has norm one, so orthogonality of the
word/memory basis gives branch squared norm $H_{jj}Z_{n,j}/\lambda^n$,
exactly (IX.14). Projecting the actual $M$, with both labels retained,
proves (IX.36). Tracing $B$ uses (IX.33), proving (IX.37).
No normalization is assigned to the zero flag at $n=0$. $\square$

**Proposition 180.3 (actual resource return and exact joint discrepancy).**
Define

$$
T(z)=\begin{pmatrix}1&z\\z&9\end{pmatrix},\qquad
q_{n,j}(k)=\frac{[z^k](T(z)^n)_{0j}}{Z_{n,j}}
\tag{IX.38}
$$

on each positive terminal branch. The $q_{n,j}$ are probability
mass functions, supported on $k\equiv j\pmod2$. The actual
conditional resource marginal and its comparison overlap are

$$
\begin{aligned}
\eta^{\mathrm{act}}_{n,j}
 &=\sum_{k=0}^n q_{n,j}(k)|g_t;k\rangle\langle g_t;k|,\\
A_{n,j}&=\sum_{k=0}^n q_{n,j}(k)G_k.
\end{aligned}
\tag{IX.39}
$$

Compare the entire terminal output with (IX.13) retaining the unchanged
comparison resource $|g_t\rangle$, the same labels and the same other
backing. Their exact joint half-trace distance is

$$
D^{\mathrm{term}}_{n,g}
 =\sum_{j:p_j(n)>0}p_j(n)\sqrt{1-A_{n,j}^2}.
\tag{IX.40}
$$

Thus unchanged flag probabilities do not certify the complete return.
For the port alone the resource charge loss is the emitted occupation:

$$
\begin{aligned}
\langle N_B\rangle_{\mathrm{in}}&=K+(L-1)/2,\\
\langle N_B\rangle_{\mathrm{out}}
 &=K+(L-1)/2-\mathbb E|w|,\\
\mathbb E|w|&=
 \left.\frac{d}{dz}\left[
 \lambda^{-n}(1,0)T(z)^n(1,u)^{\mathsf T}\right]\right|_{z=1}.
\end{aligned}
\tag{IX.41}
$$

Proof. For squared amplitudes every zero step contributes $1$ or $9$
and every flip contributes $z$, yielding (IX.38). Tracing the word in
(IX.35) proves the first line of (IX.39). The normalized joint branch
has inner product $A_{n,j}$ with its ideal branch tensored with
$|g_t\rangle$: each word contributes its own probability times
$\langle g_t|g_t;k\rangle=G_k$. Both joint branches are pure.
The pure-state half-trace formula and orthogonal flag blocks therefore
give (IX.40), not a distance computed just on the resource marginal.
Each $|g_t;k\rangle$ has charge mean $K+(L-1)/2-k$.
The generating function in (IX.41) sums both flag weights, equals one
at $z=1$, and its derivative is the occupation mean. This proves the
charge assertions independently of any physical Hamiltonian. $\square$

**Proposition 180.4 (successive flagged blocks retain one correlated
resource).** Consider successive positive block lengths
$n_1,\ldots,n_m$ with $N=\sum_\ell n_\ell\le K$, complete memory
reads between them, and no other intervention. Put $a_0=0$ and
$W=w^{(1)}\cdots w^{(m)}$. For a particular complete flag record
$a_1,\ldots,a_m$, the unnormalized joint vector is

$$
\lambda^{-N/2}\sqrt{H_{a_ma_m}}
 \sum_{w^{(1)},\ldots,w^{(m)}}
 \left[\prod_{\ell=1}^m
 \psi_{n_\ell,a_{\ell-1}a_\ell}(t)(w^{(\ell)})\right]
 |W\rangle|a_m\rangle_M|g_t;|W|\rangle_B.
\tag{IX.42}
$$

Its trace is the same product of entries of $\mathsf P_{n_\ell}$
as in (IX.17). Nevertheless the old and new blocks and $B$ do not
in general factor conditional on the flags, even at fixed $t$.
The terminal read separates the one-dimensional current $M$ from the
rest, but does not separate the rest from $B$. This formula also holds
along an adaptively chosen block-length path with its actual control
probability retained.

Proof. At every block, the endpoint factor is
$\lambda^{-n_\ell/2}\sqrt{H_{a_\ell a_\ell}/
H_{a_{\ell-1}a_{\ell-1}}}$, as in (IX.16). These factors telescope;
all resource lowerings add. Word orthogonality makes the norm squared
the product of the block norms. Cross-word entries instead contain
$G_{|W|-|W'|}$ after tracing $B$. They depend jointly on all blocks,
which supplies the claimed correlated successor rather than a new
independent resource for each flag. $\square$

## 181. A finite-resource effect in the complete VIII159 consumer

**Definition 181.1 (same acquired pair and complete disturbed returns).**
Take $5\le n\le K$ with actual exterior lengths $p,q\ge1$,
$p+2+q=n$. After (IX.36), use the existing complete VIII159 instrument
on precisely factors $p+1,p+2$ and its two separately supplied fresh
$|+\rangle$ probes, in the same calibrated frame. Both flags remain;
there are sixteen delivered four-bit outcomes for each flag and each
chosen setting $\beta=0,1$. For outcome $o=(o_1,o_2)$ let
$J_{\beta,o}=\Pi_oU_\beta$ be the literal operator of (VIII.115–116).
On all retained quantum factors the output, before its backed classical
delivery suffix is discharged, is exactly

$$
\sum_{j=0}^1\sum_{o_1,o_2\in\{00,01,10,11\}}
 |h_{j,\beta,o_1,o_2}\rangle\langle h_{j,\beta,o_1,o_2}|
 \otimes
 (J_{\beta,o}\otimes I)
 (|\Xi_{n,j}\rangle\langle\Xi_{n,j}|\otimes
   |++\rangle\langle++|\otimes\zeta)
 (J_{\beta,o}^\dagger\otimes I).
\tag{IX.43}
$$

Here $I$ includes $M,B$, every exterior factor and every untouched
reference; $\zeta$ denotes the other backing only where the stated
conditional independence holds. More generally apply the same operators
to the full joint state without inserting a tensor factorization.
Each $h$ includes actual preparations, source/root and acquisition
bindings, versions, controls, detector outcomes and complete or pending
output fields. Formula (IX.43) returns all disturbed inputs and probes,
all resources and their conditional correlations; it restores none.

**Theorem 181.2 (source-specific resource-dependent joint detector law).**
Put $(x,y)^{\mathsf T}=T^pe_0$ and
$(v_j,w_j)^{\mathsf T}=T^qe_j$. Define $Q_{2,j}(t)$ by the matrix
(VIII.109) with $(a,b,c,d)=(x,y,v_j,w_j)$ and denominator $Z_{n,j}$,
and set

$$
\kappa_j=\frac{xv_j+9yw_j}{Z_{n,j}},\qquad
\nu_j=\frac{3(xw_j+yv_j)}{Z_{n,j}}.
\tag{IX.44}
$$

Let $d^{(j)}_{ab}$ be its four diagonal entries. The actual conditional
pair density $Q^g_{2,j}(t)$ has these same diagonal entries and the same
$01,10$ coherence $\nu_j$; its $00,11$ entry is
$G_2\kappa_j e^{-2it}$. No other entries are introduced. For all
sixteen outcomes the unconditioned joint law is

$$
\Pr_g(j,o_1,o_2\mid\beta)
 =p_j(n)\operatorname{Tr}\left[
 Q^g_{2,j}(t)(E_{o_1}^{(\beta)}\otimes E_{o_2}^{(0)})\right],
\tag{IX.45}
$$

using exactly (VIII.99)'s four full-qubit effects. With $C=\cos1$,
$S=\sin1$, and

$$
D_j=\frac{(1-C)^2d^{(j)}_{00}
 +S^2(d^{(j)}_{01}+d^{(j)}_{10})
 +(1+C)^2d^{(j)}_{11}}{16},
$$

the selected event, as a statistic of the entire retained output, has

$$
\begin{aligned}
\Pr_g(j,10,10\mid\beta)
 &=p_j(n)\left[D_j+\frac{S^2\nu_j}{8}\cos\beta
       -\frac{S^2\kappa_jG_2}{8}\cos(\beta-2t)\right],\\
\Pr_g(j,10,10\mid\beta)-\Pr_{\mathrm{id}}(j,10,10\mid\beta)
 &=\frac{p_j(n)S^2\kappa_j}{8}(1-G_2)\cos(\beta-2t).
\end{aligned}
\tag{IX.46}
$$

In particular at $t=0$, $\beta=0$, the complete-output half-trace
distance from the ideal source port followed by this same consumer is
at least

$$
\frac{p_0(n)S^2\kappa_0}{8}
 \frac{2L}{L+1}\sin^2\frac{\pi}{L+1}
 \ \ge\ \frac{5S^2}{416(1+u^2)}
 \frac{2L}{L+1}\sin^2\frac{\pi}{L+1}>0.
\tag{IX.47}
$$

This is an unconditioned bound on a lawful event including its terminal
flag. It is a resource dependence of this IX source with the supplied
consumer, despite exactly unchanged terminal flag and occupation laws.
For this family of calibrated sine resources, achieving complete error
at most $\epsilon$ at that interface necessarily requires

$$
L+1\ge
 \sqrt{\frac{5S^2}{104(1+u^2)\epsilon}}.
\tag{IX.48}
$$

There is no universal minimum claim over other resources or couplings.

Proof. In a two-site marginal, the exterior bra and ket words agree.
Their occupation counts cancel from $|w|-|v|$ in (IX.37); the remaining
difference is that of the selected pair. The actual exterior sums are
$T^pe_0$ and $T^qe_j$, so the same original-endpoint contraction used
in VIII157 gives $Q_{2,j}(t)$. Only its charge-two entries acquire
$G_2$; the charge-zero entries are unchanged. This proves the pair
assertions on both terminal branches, with the full exterior still
present in (IX.43). Contracting the supplied effects proves (IX.45).
The $10,10$ contraction is VIII159's calculation with the actual
coherence $G_2\kappa_j$, proving (IX.46), including its sign.
Unitary $U_\beta$ and the sixteen exhaustive projectors make (IX.43)
trace preserving after summing both flags.

Here $y/x\ge1$ and $w_j/v_j\ge1$: for $q=1$ the latter ratio is
$1$ or $9$, and $r\mapsto(1+9r)/(1+r)$ preserves $r\ge1$.
The polynomial inequality in VIII157 therefore gives
$\kappa_j\ge5/52$ for both actual endpoint choices. Combine this
with $p_0(n)\ge1/(1+u^2)$ and (IX.34). Reading the event
$(j,o_1,o_2)=(0,10,10)$ is a channel from the complete retained
output, so its probability difference is a lower bound on that
output distance. This proves (IX.47) without selecting or renormalizing
a rare branch. Finally $\sin\vartheta\ge2/(L+1)$ and
$L/(L+1)\ge1/2$ imply $1-G_2\ge4/(L+1)^2$, giving (IX.48).
$\square$

The finite resource has $G_2<1$ but $G_2>0$ for $L\ge3$.
In that range the two ideal probability laws of this calibrated finite
model still identify $t\bmod\pi$ after division by the known $G_2$;
this is a statement about laws, with reduced signal, not exact inference
from finitely many samples. At $L=2$, $G_2=0$ and this pair consumer's
phase signal vanishes. Neither case supplies the extra first-harmonic
preparation of §178 from an original finite target.

## 182. Complete-output accuracy for a finite adaptive commission

**Definition 182.1 (protected comparison tree and separate errors).** A
protected tree has at most $K$ executed port increments on any path,
with increments $r_h=s'_h-s_h$, $|r_h|\le1$. Between them it may use
all original native services and their pending phases, arbitrary already
supplied full-domain instruments on the bank, both terminal outcomes,
dirty-input port calls, paid new inputs, $P/B$ words, occupation reads,
and adaptive choices depending on their full records. None of these
non-port primitives acts on $B$. They include the protected resource
hold and the stipulated joint evolution of other backing. Thus the
ideal comparison prefix, at fixed $t$, always retains $|g_t\rangle_B$
independent of its other quantum factors. Arbitrary operations on old
outputs are allowed; their source disturbances are not undone.

Use V25.1/V29.1's instrument-level occupation service: while its acquired
input is waiting, hold the entire joint bank; its actual measurement
transition applies the named projector, records the actual outcome and
latches that subnormalized successor. Subsequent pending output phases
hold that successor and the owed delivery. No outcome is used to choose
a request before it is delivered. A separately declared detector
coupling with additional intermediate quantum cuts must supply those
cuts' full maps and their own certificates; the completed projector
formula is not assigned to an unfinished coupling. Port waiting/paused
cuts instead retain (IX.31) at the actual executed progress and resume
by its next increment. Native pending phases use their unchanged
full-bank holds and genuine fresh extensions.

The finite reference implementation uses (IX.31). Its ideal comparison
uses $U_t(r_h)=U_t(s'_h)U_t(s_h)^\dagger$ on the same actual $M,Q$,
with identity on $B$, and the same other primitive maps, raw labels,
source fields and resource outputs. This unchanged $B$ is a comparison
state, not an assertion about the actual successor (IX.39).

For a physical implementation, let $e_{\mathrm{init}}$ bound the
initial complete joint half-trace discrepancy from the calibrated
entrance, uniformly over the promised $\rho_{AR}$ and untouched
extensions, with the same finite labels. It includes initial source
binding, ingress, $M$ and blank preparation where promised, (IX.28),
all initially provided probes, controls and backing. At each genuinely
additional approximate primitive $h$, supply a full-interface
reference-stable error $e_h$. A sufficient certificate is half the
diamond distance between its actual map and the specified finite
reference map, including all resource, detector, record and pending
outputs. The domain includes dirty inputs and the correlated $B$
that can actually reach it. Later reference preparations/ingress, holds,
rounding, couplings, native operations, detectors and delivery get their
own terms at their actual interfaces; none is inferred from a resource
marginal, population calibration or flag-success frequency. An exact
primitive has $e_h=0$.

**Theorem 182.2 (finite complete-output certificate).** For every such
finite adaptive tree, at a leaf set including any selected pending cuts,
and uniformly over arbitrary dirty system inputs and untouched reference
extensions allowed at its entrance,

$$
\begin{aligned}
d(\mathrm{Out}_{\mathrm{phys}},\mathrm{Out}_{\mathrm{id}})
 &\le \min\{1,\Delta\},\\
\Delta&=e_{\mathrm{init}}+
 \max_{\text{paths }p}\left[
 \sum_{h\in p}e_h+
 \delta_L\sum_{h\in p\cap\mathrm{port}}
          \sin(|r_h|\theta_0)\right],\\
\delta_L&=\sqrt{2(1-G_1)}
       =2\sin\frac{\pi}{2(L+1)}.
\end{aligned}
\tag{IX.49}
$$

The complete output includes $B$ and all its correlations, the same
continuing $M$, every old/dirty/new factor, all flags and detector
outcomes, all source and preparation backing, immutable records,
refusals, delivered prefixes and owed suffixes, Print/End/ACK/Return
fields and actual partial states. In particular the intrinsic resource
term is at most

$$
Kb\delta_L\le\frac{\pi bK}{L+1}.
\tag{IX.50}
$$

Thus for a reserved resource tolerance $\epsilon_{\mathrm{res}}>0$,
choosing $L\ge2$ with $L+1\ge\pi bK/\epsilon_{\mathrm{res}}$
gives an explicit finite resource certificate of dimension $2K+L$,
in addition to the separately certified initial and physical errors.
The maximum covers all paths, including zero ideal-mass paths.

Proof. On the initial calibrated resource, one lowering differs from
multiplication by $e^{it}$ with unchanged resource by norm
$\sqrt{2(1-G_1)}=\delta_L$; one raising differs from $e^{-it}$
by the same norm. In (IX.32)'s partial version the diagonal terms agree
with $U_t(r_h)$ exactly. Its four off-diagonal terms have differences
of these shifted vectors, with coefficients of magnitudes
$|\sin(r_h\theta_0)|$ or $|\sin(r_h\theta_1)|$. Each of the
four input basis vectors sends its difference to a different output
$MQ$ basis vector. Hence for every unit vector $|\chi\rangle_{MQ\mathcal D R}$,
including one entangled with an arbitrary remaining bank $\mathcal D$
and untouched reference $R$,

$$
\left\|V(r_h)(|\chi\rangle|g_t\rangle)
 -(U_t(r_h)|\chi\rangle)|g_t\rangle\right\|
 \le\delta_L\sin(|r_h|\theta_0).
\tag{IX.51}
$$

Here $0<\theta_1<\theta_0<\pi/2$ and $|r_h|\le1$.
Purification, the pure-state trace-distance inequality and partial trace
give the same bound for joint densities, including all resource output.
This is a bound on calibrated product resource inputs; it is not a
half-diamond comparison over arbitrary inputs of $B$.

Expand the difference of the physical and ideal tree maps by placing
an ideal prefix before the changed slot and the physical suffix after
it. At that slot insert the finite reference map: its difference from
the physical map costs $e_h$, and its difference from the ideal map
costs (IX.51). These costs are added at the same node before taking
path maxima. Only the ideal prefix needs the calibrated product
resource; it has it by Definition 182.1. The physical suffix is a
normalized complete operation on every allowed dirty/correlated input
and contracts the changed slot's joint trace error. No induction
hypothesis asserts that the actual $B$ is fresh, independent or equal
to $|g_t\rangle$ after an earlier call.

At an observed split, the positive child masses sum to the parent mass.
Backward induction therefore bounds the descendant budget by the
largest child budget. This is exactly VI67.2's complete-interface
composition argument, with (IX.51) inserted on the ideal prefixes.
It gives the maximum path sum and requires no division by a branch
weight. Adding the initial joint error once proves (IX.49).
Since $\sin(|r_h|\theta_0)\le\sin\theta_0=b$ and
$2\sin(\pi/(2(L+1)))\le\pi/(L+1)$, (IX.50) follows.
The argument is pointwise uniform in fixed $t$ and also bounds the
full common-phase mixture when the preparation/physical certificates
hold conditionally in that same kernel. $\square$

For example, if the finite reference's desired two rotation angles at
one executed increment are $r_h\theta_j$ and their implemented angles
are $\widetilde\alpha_j$, the operator difference of those block
rotations is at most $\max_j|\widetilde\alpha_j-r_h\theta_j|$.
It supplies a full-interface half-diamond term of that size, including
$B$ and dirty inputs. It does not certify the physical coupler, its
holds, detectors or unlisted output channels; their certificates remain
separate. Comparison labels keep the same actual command and catalog
records, as in VI67.2; a real command difference is not erased.

A subsequent common normalized operation contracts a bound already
established at a cut. A further ideal-port comparison incurs further
resource/physical terms and must meet its own domain. For a positive
record event with actual and ideal weights $p,q$, an unconditioned
bound $\Delta$ gives only the conservative normalized-state bound
$\min\{1,2\Delta/\min(p,q)\}$. A zero-weight branch has no normalized
state. In particular (IX.49) is not a normalized rare-terminal-branch
bound with the same constant. The exact finite model has the sharper
branch formulas (IX.37–40); a physical detector or preparation error
does not inherit their exact flag weights.

## 183. Extra resource access changes the accuracy domain, not reality

**Proposition 183.1 (a granted resource read destroys this calibration).**
Suppose, in addition to port/hold permission, a resource occupation read
is separately acquired and authorized before emissions. Its full
instrument is

$$
\omega\longmapsto\sum_{r=0}^{R_B}|h_r\rangle\langle h_r|
 \otimes (|r\rangle\langle r|_B\otimes I)\omega
         (|r\rangle\langle r|_B\otimes I).
\tag{IX.52}
$$

It is a legitimate extra successor, with every result and resource
retained. On (IX.28) it gives the recorded mixture
$\sum_r g_r^2|h_r\rangle\langle h_r|\otimes|r\rangle\langle r|$,
independent of $t$ on these factors. Now execute $n\le K$ fresh
emissions and both terminal outcomes using the same finite coupler.
All flag and occupation laws of §180 remain the same, but the bank's
cross-occupation coefficients after forgetting the resource read record
and tracing $B$ are zero. In particular the actual VIII159 laws are
(IX.45–46) with charge-two coefficient zero, rather than $G_2$.

Proof. Each recorded resource eigenstate has initial level $r\ge K$.
A word of weight $k$ leaves it at the actual level $r-k$, with no
source phase factor in (IX.32). Different $k$ give orthogonal returned
resource vectors for that same recorded $r$. Tracing $B$ removes all
cross-weight entries, even if the resource outcome is still retained;
summing $r$ changes neither this fact nor any word's diagonal weight.
This proves the complete readout consequence. $\square$

This additional permission preserves the full dynamics (IX.31), all
original native futures and the growing-bank boundary of §174 with $B$
included. It invalidates the protected-prefix premise of §182. The
small resource term (IX.51) must not be asserted for later calls on
this post-read input. One may instead compare through the actual
post-read state, or insert a separately justified mismatch/renewed
preparation cost at the broken interface. A common read after an already
certified cut still contracts that cut's bound; replacing later finite
calls by $U_t$ is the step that needs renewed calibration. No branch
of (IX.52), occupied resource, old output or owed service is deleted to
rescue an all-future accuracy claim.

More general separately authorized interventions on $B$, source-phase
updates and hold drift use their true complete maps on the joint state.
Their successors exist on their declared domains. They are covered by
the exact update interface, but have a small ideal-port certificate only
when the required product/phase premise is reestablished or an explicit
additional error is proved. Even when no such intervention occurs, a
fixed finite $B$ is not an unlimited guard: after the commissioned
increments its boundary actions remain (IX.29), not an infinite shift.
For fresh vacuum inputs total emitted occupation cannot exceed the
initial maximum resource level $K+L-1$. The ideal IX word $1^n$ has
positive weight at every finite $n$, so for $n>K+L-1$ this particular
finite realization cannot have the ideal word law. This is a statement
about this conserving finite implementation, not a universal resource
lower bound or a refusal of an original native request.

## 184. Native mounting, retained obligations and distinct resource costs

**Theorem 184.1 (same-source mounting with full finite resource updates).**
Under the actual commissioning/preparation/material/progress premises
of V25–39 and §178, mount $M,B$ and the finite coupler in the apparatus
namespace of §176 on either authentic entrance of the same actual
source. Acquire their actual bindings and separate permissions; obtain
emission slots through the original genuine growth/acquisition route.
Then all original native legal futures and deterministic supplemented
recovery remain valid. Each finite declared enlarged tree has the
complete actual successor obtained from (IX.31), its resource maps and
its complete instruments, whether protected calibration holds or not.
Only protected finite commissions with the separate certificates obtain
(IX.49); uninterrupted protected blank emissions obtain (IX.35–48).

Proof. Use the concrete correspondence of Theorem 176.1, retaining its
native and acquired identities, rather than constructing a new source
from the vector (IX.35). At the finite entrance keep its actual
prehistory/preparation; at the bilateral entrance traverse its real
headers and retain each selected root's empty or $P_\varepsilon$
preparation. Ordered $\alpha/\beta$ bracket parsing, genuine addressed
$P/S/\operatorname{Next}$ and Tag's actual constructor/absence test
are unchanged. Neither a resource level, terminal flag nor emission
roster index is a source vertex, journal entry, logical child or native
Tag. Immutable samples and successful-event history retain their
original meanings and acquired versions.

At each apparatus call, the actual cursor is at an enabled returned
Ready cut and the native continuation is saved. Reference acquisition,
current grants, endpoint versions, locks and permission refusals use
the same real source/component pair. In particular no density operator
creates a reference or authority. A dirty-input port call uses the full
(IX.31), and a partial pulse retains its actual progress, resource state,
held bank, pending controls and owed suffix. Pending native parser,
traversal, reservation, edit and tape/output states retain their actual
fields. Native holds/growth are full-bank identity/vacuum extension
also on these disturbed states, so their source transition is unchanged.

Every completed reply, resource read, detector result or terminal flag
has its own backed output, sealing, Print, End, local ACK and same-root
Return with charged scratch clearing. Partial delivery keeps its actual
delivered prefix and unprinted suffix. Return restores neither a spent
probe, $M$, $B$, preparation authority nor detector readiness. Old
occurrences, physical exteriors, source backing, immutable samples and
occupied/spent quantum outputs remain held; they are not scratch.
Missing control/phase/resource authority leaves the protected primitive
unexecuted with its actual denial or pending obligations. It does not
alter an original native guard or remove an original request.

The retained boundary is exactly (IX.18) with $B$ included among the
operators' bank factors. Replace the ideal-port multiplication (IX.22)
by the $MQB$ operator (IX.31), or its enabled partial increment;
apply every additional instrument to the factors it really addresses.
Matrix-unit expansion gives the four memory blocks of the actual
joint successor, with no resource marginal substituted. All branch
maps sum to trace preservation, including (IX.43) and (IX.52).
Induction over the actual finite phase steps therefore proves both the
unchanged native projection and the stated complete enlarged dynamics.
AAII96.2/97.2 and IV16 still recover the same actual source/history from
their supplemented views under full original $Q_g$. Their native inverse
does not require a terminal zero or a clean resource. The new joint
quantum boundary remains a growing bank, not a four-number readout or
a claimed minimal total memory. $\square$

**Definition 184.2 (separate cost and acquisition coordinates).** The
finite resource dimension is $2K+L$, its initially occupied width is
$L$, its maximum supported entrance charge is $K+L-1$, and its mean
is $K+(L-1)/2$. The $K$-level margins support both dirty-input
absorption and emission throughout the finite commission. These
capacity/coherence/guard coordinates differ from the mean charge
transferred in (IX.41), from control complexity, retained-bank size,
calibration precision and elapsed physical duration. No optimum for
these coordinates is claimed. Maintaining and later releasing all old
outputs has its own storage/control/return obligations.

Charge means and the word-dependent charge law are predictions, not
extra classical logs of coherent energy-transfer paths. A meter that
resolves a resource level or transfer must be included as an actual
instrument with its disturbed joint return. Its records cannot be
added to the unitary model without changing that model's calibration.

The conserved quantity is $N_B+N_Q$, with the memory label assigned
zero charge. Identifying it with physical bare energy requires the
additional Hamiltonian hypothesis
$H_B=\hbar\omega N_B$, $H_Q=\hbar\omega N_Q$ and degenerate
$H_M$, with the relevant coupling commuting with their sum. A physical
nondegenerate memory or different gaps requires a different resource
implementation and its own certificate. Even under that hypothesis,
control switching, compensation, preparation, detector operation,
source/native work and storage are additional costs; bare conservation
does not pay them. Native occupation, edit count and source traversal
time are not identified with this energy by notation.

The two fresh VIII159 probes and their whole common-frame preparation,
backing, retention and detector readiness are separate resources from
$B$. They are supplied for (IX.43), and their disturbed returns remain.
Using $B$ to prepare those probes would be an additional actual coupling,
with its own resource successor and error; their free independent
preparation could not then be assumed. Likewise preparation of
(IX.28), source-phase acquisition and phase-preserving holds are distinct
from the later conserving port. Neither finite signed-dyadic $P/B$
controls nor the original even-mode targets supply them for free.

## 185. Attribution and precise remaining scope of the finite port

The charge-shift lift is `literature-attested`: Åberg,
[*Catalytic Coherence*, 1304.1060v3, Appendix B.1–B.4,
(18), (23), Proposition 1; Appendix D.1–D.2,
(84)–(86)](https://arxiv.org/html/1304.1060v3), constructs the
charge-sector lift, shift-dependent reduced channels and explicit
boundary sectors. Chiribella, Yang and Renner,
[*Fundamental energy requirement of reversible quantum operations*,
1908.10884v3, (11)–(14) and Appendix D](https://arxiv.org/html/1908.10884v3),
use finite sine batteries and energy-sector implementations, with their
stated gate fidelity/error and Hamiltonian assumptions. The sine
profile and the generic telescoping principle are reused tools here,
not new mathematical discoveries or an instantiated optimal-energy
bound for this source.

Vaccaro, Croke and Barnett,
[*Is coherence catalytic?*, 1804.05154v1, §3 and Appendix B](https://arxiv.org/html/1804.05154v1),
show why repeated-use whole outputs and correlations must be retained;
unchanged single-system behavior is insufficient. Lostaglio and Müller,
[*Coherence and asymmetry cannot be broadcast*, 1812.08214v2,
Theorems 1–2](https://arxiv.org/html/1812.08214v2), treat finite
references under covariant operations and connected Lie symmetry groups.
No theorem here promotes an unchanged resource marginal to catalytic
return or applies a no-broadcasting claim beyond those symmetry
premises. Quantum Cut Atlas III18–22 and QUANTUM-REALITY286/373–378
already supply the repository's full-return, finite-reference and
pure-fidelity distinctions; AURIC Internal Energy Reference Orbital
Deflection Resource Handoff V85 §§6–10 separates charge/energy and
return requirements. VI67.2 supplies complete-output adaptive error
composition, including pending records; it is applied in (IX.49).

Li and Lipka-Bartosik,
[*The memory cost of sequential quantum state preparation*,
2611.14652v1, §III and Theorem 1](https://arxiv.org/html/2611.14652v1),
establish exact memory costs for pure-state preparation from energy
eigenstates under energy-preserving operations, allowing memory to
change, correlate or be consumed. Its exact pure-output energy-support
count is not instantiated by IX's correlated emitted bank/resource
return. No optimal sequential-memory count is imported from it here.
The existing D5 suppliers ComplexReferenceFrameTaxExact,
AllFutureStatisticsSufficiency and ControlledBehaviorUniversality retain
their stated finite exchange, all-iterate readout and controlled-quotient
domains; none supplies a physical source preparation, IX calibration or
a smaller all-future acquired boundary. No new compilation or extension
of those formal statements is asserted.

The `repo-derived` contribution is the joint instantiation on the
specific continuing IX memory: the full two-block finite source port,
its occupation-count/resource law (IX.35–42), both endpoint-specific
complete VIII159 laws and finite-resource signal (IX.43–48), and their
same-source finite adaptive comparison with the actual resource kept
(IX.49–52). The source endpoints, genuine native mounting and positive
supplemented recovery are the existing suppliers, not replaced
preparations. This is a bounded constructive result, with no global
originality claim.

Actual same-source resource/phase preparation, calibrated couplings,
protected holds and all additional physical error certificates remain
premises. The exact finite map exists on all dirty inputs and permitted
reference extensions; its small ideal-port error has the protected
finite domain stated in §182. Additional acquired resource access keeps
its true successor and can leave that domain, as §183 demonstrates.
No unlimited finite-resource service, bare geometry-to-history inverse,
unknown phase returned exactly from finite samples, universal total
memory minimum, recorder-independent logarithmic result or completion
of the enduring space/time/boundary/memory mutual-recovery goal follows.

## 追加锚（本行以下为增补区）

## 186. Occupation-preserving read interfaces for a serial port compiler

**Definition 186.1 (fixed read rails and retained compilation cuts).**
Keep §§178–184's actual source, resource, preparations, rights and
complete futures. Consider a proposed realization of the finite port
by a finite serial word of V34's literal full-qubit $P$ and $B$ gates.
The occurrence output $Q$ is its actual acquired qubit $q$. One fixed
acquired qubit $m$ reads the memory value: on the proposed memory code,
the occupation projector $n_m$ is the original memory projector
$|1\rangle\langle1|_M$. All other memory rails, resource encodings,
work qubits, preparation devices and leakage spaces remain actual
retained factors. A change of decoder does not change which acquired
qubit this occupation request addresses.

At every completed elementary gate cut the original port progress is
some retained $s_k\in[0,1]$, initially zero and finally one. Intermediate
classical work may hold the bank and append genuine independent vacuum
through native growth. The raw gate cursor, enabled entries, actual
bindings, executed progress, output prefix and owed suffix are retained.
An authorized interruption may read $m$ and $q$ at such a cut and then
resume the saved raw suffix. The corresponding original continuation
reads the memory and $Q$ at $s_k$ and owes $V(1-s_k)$ on their actual
postmeasurement joint state. The decoder may not postpone these reads
until a completed word, silently complete that word first, discard a
read result or replace the pending state by an endpoint state.

This is a specified compiler class, including the two-rail encoding
below. It is not an assertion that every encoding has a one-qubit memory
read. The theorem permits arbitrary extra acquired wires and arbitrary
initial states of the other factors, including correlations with
untouched references; it does not grant those states, wires or rights.
Between the tested gates the unobserved word has no extra quantum
primitive besides $P/B$, identity holds and independent vacuum extension.
A measuring or adaptive compiler is a different complete instrument,
with its own retained outcomes and correspondence obligation.

**Definition 186.2 (one charge-compatible endpoint encoding).** An
explicit member of this class uses two acquired memory qubits
$m_0,m$, the literal occurrence qubit $q$, and $R_B$ resource qubits.
Its mathematical isometry $E$ is

$$
\begin{aligned}
|0\rangle_M&\longmapsto |10\rangle_{m_0m},&
|1\rangle_M&\longmapsto |01\rangle_{m_0m},\\
|r\rangle_B&\longmapsto |1^r0^{R_B-r}\rangle,&
|z\rangle_Q&\longmapsto |z\rangle_q.
\end{aligned}
\tag{IX.53}
$$

Thus physical total occupation compresses to $I+N_Q+N_B$.
The unused computational vectors are retained leakage directions, not
removed outcomes. The initial memory excitation, encoded resource,
same-source first harmonic, preparation/ingress and any helper state
require their own paid acquisitions and complete preparation backing.
In particular (IX.53) neither prepares (IX.28) nor transports its
same-phase promise into this encoding. The obstruction below may be
tested conditional on that preparation being supplied exactly; it
therefore does not arise merely from starting all resource qubits in
vacuum.

## 187. A necessary intermediate mismatch in every finite serial word

**Theorem 187.1 (IX first-emission cut obstruction and quantitative
gate certificate).** Start a proposed compiler of Definition 186.1 with
$M=|0\rangle$, the actual fresh $Q=|0\rangle$, and the calibrated
resource (IX.28), with its separately supplied full preparation. Take
any purification including every backing factor and untouched reference.
For an unobserved word of $N\ge1$ elementary gates write $\rho_k$
for the complete state after gate $k$, and define full-space projectors

$$
F_{11}=n_m n_q,\qquad
F_{\ne}=n_m(I-n_q)+(I-n_m)n_q,\qquad
p_k=\operatorname{Tr}(F_{\ne}\rho_k).
\tag{IX.54}
$$

For the $k$th hopping gate let $\alpha_k$ be its actual angle. Let
$\mathcal I$ consist of those gates whose endpoint pair contains
exactly one of $m,q$, and put

$$
A=\sum_{k\in\mathcal I}|\sin\alpha_k|,\qquad
T=|\mathcal I|.
\tag{IX.55}
$$

If the complete endpoint state has half-trace error at most $\eta$
from the encoded $V(1)$ first-emission target, then

$$
\begin{aligned}
\sqrt{(b^2-\eta)_+}
 &\le\sum_{k\in\mathcal I}|\sin\alpha_k|\sqrt{p_{k-1}},\\
(b^2-\eta)_+
 &\le A^2\max_{0\le k<N}p_k
 \le T^2\max_{0\le k<N}p_k.
\end{aligned}
\tag{IX.56}
$$

Here $b^2=u/\lambda>0$ is the original IX coefficient and
$x_+=\max\{x,0\}$. An empty word has endpoint $F_{11}$ probability
zero and cannot have $\eta<b^2$. If at every
prefix the complete state has half-trace error at most $\epsilon$
from its assigned original partial state, with endpoint error also
at most $\epsilon$, necessarily

$$
\epsilon\ge\frac{b^2}{1+A^2}
              \ge\frac{b^2}{1+T^2}.
\tag{IX.57}
$$

Consequently no finite serial word in this class is an exact
correspondence at all its exposed cuts. The obstruction already uses
one lawful clean first-emission input, so a purported exact bridge on
the full dirty/reference domain fails too. The inequalities do not
assert a positive error floor uniform over words of unbounded length.

Proof. The guard in Theorem 179.2 makes the one-step lowering $D_-$
an isometry on the initial resource support. Its exact first partial
emission, before any intervention, is

$$
\cos(s\theta_0)|0\rangle_M|0\rangle_Q|g_t\rangle_B
 +\sin(s\theta_0)|1\rangle_M|1\rangle_QD_-|g_t\rangle_B.
\tag{IX.58}
$$

This has $F_{\ne}$ probability zero at every $s\in[0,1]$, and
$F_{11}$ probability $b^2$ at $s=1$. All other factors and their
true stipulated evolution remain alongside it. The same statements
hold in the full common-phase mixture. They require neither a readable
$t$ nor a resource read.

Purify the actual initial state and retain that purification through
all unitary gates and vacuum extensions. Write $\psi_k$ for this
unit vector and $a_k=\|F_{11}\psi_k\|$. The initial $a_0$ is zero.
A phase gate, a hop disjoint from $\{m,q\}$, or the hop between
$m$ and $q$ commutes with $F_{11}$ and preserves $a_k$. The last
case uses the full-qubit fact that $B_{mq}$ fixes $11$; its exchange
acts only within the mismatching $10,01$ subspace.

For a hop $G=B(\alpha_k)$ touching exactly one of $m,q$, put
$F_{00}=(I-n_m)(I-n_q)$. The untouched one of these two read rails
prevents a direct $00$-to-$11$ transition, whereas the literal hopping
matrix gives

$$
F_{11}GF_{00}=0,\qquad
\|F_{11}GF_{\ne}\|\le |\sin\alpha_k|,\qquad
\|F_{11}GF_{11}\|\le1.
\tag{IX.59}
$$

These are identities and bounds on the entire qubit space, including
all occupations of the other endpoint and all spectators. Resolving
the identity as $F_{00}+F_{\ne}+F_{11}$ therefore gives

$$
a_k\le a_{k-1}+|\sin\alpha_k|\sqrt{p_{k-1}}.
\tag{IX.60}
$$

Holds and independent vacuum extension commute with these projectors
and leave the same inequality unchanged. Summing proves the first
upper bound for $a_N$. The endpoint half-trace bound, tested with the
effect $F_{11}$, gives $a_N^2\ge b^2-\eta$. This proves (IX.56).
Every assigned original partial state has mismatch probability zero,
so the prefix error bounds imply $p_k\le\epsilon$. Also
$\eta\le\epsilon$. Hence $b^2\le\epsilon+A^2\epsilon$;
$A\le T$ proves (IX.57). Purification included arbitrary untouched
references throughout; no helper marginal or clean-helper assumption
was inserted. $\square$

The restriction is about intermediate states even when the endpoint
has no algebraic reachability obstruction. For (IX.53), the full-qubit
unitary

$$
W_s=EV(s)E^\dagger+I-EE^\dagger
\tag{IX.61}
$$

preserves physical total occupation. In each physical occupation sector
it is a direct sum of the determinant-one rotations (IX.29) and
identities, so its sector determinant is one. Marvian,
[*Restrictions on realizable unitary operations imposed by symmetry
and locality*, 2003.05524v3, Corollary 10](https://arxiv.org/html/2003.05524v3),
then supplies an endpoint word using arbitrary-pair $XX+YY$ and local
$Z$ rotations, provided those pairs are actually acquired. The native
$B$ is $\exp(i\alpha(XX+YY)/2)$, and local $Z$ differs from a native
$P$ rotation only by a global scalar; the resulting channel on the
whole bank and every reference has the required endpoint action.
This application includes dirty $M,Q,B$ within the entire encoded
domain and the four unpaired resource endpoints. It does not identify
that endpoint word's prefixes with $W_s$.

For an effectively specified $s$ and positive rational endpoint
tolerance, this endpoint consequence also permits a finite-command
search: enumerate finite signed-dyadic $P/B$ words on the acquired
finite bank and rational global phases, dovetailing these descriptions
with increasing enclosure precision. Accept only a strict Frobenius
norm upper bound below the requested tolerance, computed from outward
enclosures of the word's entries and those of $W_s$. The real-angle
endpoint word and continuity ensure eventual termination. The Frobenius
bound dominates operator norm and supplies
the same reference-stable half-trace endpoint bound, retaining all
physical outputs. Each tested word and its accepted enclosure are
finite; execution still needs its paid enabled catalog entries and
holds. The search supplies no gate-count optimum. In particular this
effective endpoint certificate leaves (IX.56–57) in force at that
word's actual elementary cuts.

## 188. A legal interrupted future retaining the complete IX181 consumer

**Theorem 188.1 (a retained mismatch event survives the original
consumer).** Take a commission with $K\ge6$ and suppose $\eta<b^2$
in Theorem 187.1. Then $A>0$, and there is a prefix $k_*$ of that
fixed unobserved word for which the
following original permitted finite future separates the proposed
compiler from the finite reference port by complete-output half-trace
distance at least

$$
\frac{b^2-\eta}{A^2}.
\tag{IX.62}
$$

Pause at that prefix and read the memory and the actual $Q$ occupation
in succession, with both delivered bits $z_M,z_Q$ retained. Resume the
actual owed suffix on the disturbed joint state. For any commissioned
$5\le n\le K-1$ continue with genuine fresh occurrence factors to a
bank of $n$, make the complete terminal memory read, and apply precisely
the complete VIII159 instrument used in §181 to factors $p+1,p+2$,
where $p,q_{\rm ext}\ge1$ and $p+2+q_{\rm ext}=n$. Supply its two
fresh common-frame probes and all actual detector readiness. Retain both
terminal flags, all sixteen four-bit outcomes for the chosen setting,
the early bits, and every disturbed quantum/resource/backing output.
Either chosen $\beta\in\{0,1\}$ may be used. No branch is discarded.

The finite reference continuation resumes by $V(1-s_{k_*})$, then
uses its ordinary later increments on the actual post-read state.
Neither reference nor proposed implementation restarts the first
emission. The early read generally changes later quantum laws, so the
uninterrupted formulas (IX.35–48) are not asserted for this continuation.
Its complete consumer is nevertheless exactly (IX.43)'s full-domain
instrument on the joint state that actually reaches it, as permitted
by §§174 and 182.

Proof. Choose a prefix maximizing $p_k$ in (IX.56). Its two successive
occupation instruments commute and have complete joint projectors
$F_{ab}$ on the read rails. Thus the actual probability of the recorded
event $z_M\ne z_Q$ is $p_{k_*}\ge(b^2-\eta)/A^2$. At the
reference cut (IX.58), the probability of that event is zero for every
assigned progress. The fine outcomes $00,11$ need not preserve the
coherence in (IX.58); their projected full joint successors, not its
unmeasured version, are used on resumption. Zero-probability outcomes
have no normalized successor.

Every following operation, including the saved raw suffix, native
holds/growth, later emissions, both terminal branches and all sixteen
consumer outcomes, is a normalized complete operation. It cannot
change the probability of an already delivered immutable early event.
Testing that event in the final full classical record proves (IX.62).
All resource correlations, memory-code leakage, unused rails, old
exteriors, spent probes and untouched references remain in the quantum
output; none must be measured or traced away to obtain the lower bound.
Counting the interrupted first call as two executed increments gives
at most $n+1\le K$ reference increments, so the original finite guard
still applies. $\square$

The finite family of tests, one at each of the word's $N$ prefixes,
is specified directly by the gate cursors. It requires no request for
$p_k$ or private $t$. The conclusion says that at least one member
separates; it supplies no source-dependent oracle choosing the largest
probability. An all-future correspondence must pass every member.

This consumer uses only the separately supplied memory read and the
ordinary occurrence occupation read already allowed between port
increments. It needs no measurement of $B$, no new opaque coupler and
no simultaneous parity detector. Its two detector results are distinct
backed answers. Their deliveries keep Print, End, local ACK and
same-root Return; an unfinished delivery keeps its actual prefix and
owed suffix before an outcome may select a next request.

Mounting this test uses the same actual root and acquired component
bindings of Theorem 184.1 at either authentic entrance, including the
finite prehistory or selected bilateral preparation. Additional qubits
are apparatus references or genuinely acquired occurrences, never
substitute source vertices. All original ordered $\alpha/\beta$ syntax,
addressed $P/S/\operatorname{Next}$, Tag, immutable samples, old
history, rights, refusals and pending native phases remain. Interposed
native service holds the full disturbed bank and appends only genuine
vacuum. The raw suffix and its real controls are still owed after a
pause. This is a conditional test on acquired controls and detector
rights, not a new native grant or a claim about an uninspected physical
device.

## 189. Attribution and the exact compiler boundary

The charge-compatible endpoint application above uses Marvian's
Corollary 10 with all sector determinants checked, rather than
inferring it from one-excitation controllability. Theorem 15 of the
same primary source assumes its equally spaced intrinsic system
Hamiltonians (167–168), the level-selective conserving couplings
(169)/(174), and an ancillary qubit initially in $|0\rangle$; (180)
returns that ancilla for every system input. The zero ancillary
preparation and those interactions are hypotheses. In particular its
general $d$-level interactions are not automatically native qubit
$P/B$ wires. Neither theorem gives the intermediate memory/resource
state, the returned ancilla at every cut, the fixed read-rail
correspondence or the owed suffix demanded here.

The `repo-derived` result is the explicit first-emission mismatch
inequality (IX.56–57) and its separating future (IX.62) in the complete
IX181 consumer. It remains valid with arbitrarily many retained
helpers and with endpoint reachability on the full encoded input;
it is additional to §171's vacuum-conservation observation and
§183's resource-read disturbance. The proof uses the literal native
full-qubit matrices and finite norm inequalities, not a claimed new
general controllability or quantum speed-limit theorem. This attribution
asserts no literature priority or Lean verification.

For fixed $T$ it gives a necessary quantitative error budget; increasing
$T$ leaves open arbitrarily accurate process approximation. A different
encoding whose logical memory read is nonlocal, an adaptive measured
compiler, or a separately acquired simultaneous interaction is outside
the serial fixed-read-rail class and needs its own complete proof.
An exact continuous partial-path implementation is not constructed.
No finite budget for a uniform joint/reference-stable approximation
under all original allowed interruptions and later instruments is
supplied. Such a construction must specify every actual cut's state,
progress, control labels, decoder/read implementation and owed suffix,
with errors on that original future domain; matching only (IX.61) is
insufficient. The source-owned resource/phase preparation, protected
holds, calibration, actual acquisition and readiness premises remain
separate. No total-memory or resource optimum follows, and the
bespoke finite coupler premise has been delimited for this compiler
class rather than removed.

## 追加锚（本行以下为增补区）
