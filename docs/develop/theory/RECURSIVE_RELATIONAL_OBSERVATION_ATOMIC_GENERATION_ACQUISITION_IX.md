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
