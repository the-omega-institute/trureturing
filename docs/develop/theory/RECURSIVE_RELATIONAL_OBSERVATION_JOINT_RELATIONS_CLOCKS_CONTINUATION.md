# Recursive relational observation: thermal joint sources and retained charge memory

> Append-only reference input for `generic-v1`. Incorporated text is immutable;
> corrections and extensions belong after the final append anchor. This volume
> contains ordinary mathematical proofs about declared finite apparatus. It
> carries no new Lean verification or literature-priority claim.

## 1. The source-specific boundary-to-memory problem

This continuation of [Joint Relations and Clocks](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_RELATIONS_CLOCKS.md)
connects its joint-source and branch-instrument contracts to the full mixed
thermal family of [Boundary Geometry VI, §§139–146](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VI.md).
Call the added apparatus **QSSR2**. The result is an attained relation between
that source, a complete local-charge instrument, retained quantum modes and
their subsequent legal use. The apparatus setting is known before preparation.
The construction does not infer a setting from an unknown native source.

Unless another revision is specified, references to these two source volumes mean their bodies at
`c79b949f81a95ec1174e4582d04ba2e22e589d8c`. Their earlier internal historical
pins retain their own identities. In particular, VI127.1's corrected native
source quantifiers govern the application; a stopped singleton birth is not
replaced by an arbitrary abstract birth or by the separate Gaussian
program-world model.

The supplier comparison with [VI147–156](https://github.com/the-omega-institute/trureturing/blob/3da21bf26eeb4f3dbbb1e2f416b8e80d44852767/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VI.md)
uses that volume at `3da21bf26eeb4f3dbbb1e2f416b8e80d44852767`.
Its inverse temperature $\beta$ is the $\theta$ used here, and its scalar
$\mu=|z|^2$ is our $z^2$, distinct from our joint phase law $\mu$.

The observation at issue is genuinely joint. A one-copy local-number readout
does not retain the coherence needed by the two-copy consumer. Two sources
can have identical one-copy density matrices after phase averaging and still
give different retained resources. The proof below identifies the precise
surviving phase character and the competing thermal noise, rather than
assuming that two prescribed marginals specify an available pair.

**Convention 1.1 (independent meanings and the task).** A boundary here is
the declared normalized modal partition $A\mid B$, represented below using
ordinary occupation tensors with explicit CAR signs. Memory means released,
addressable fermionic modes together with readable classical records, held
under a stated storage Hamiltonian. A later task means a finite actual word
of the controls and instruments in §5, with its reported outcomes and
disturbed successors. These notions are specified independently of a desired
inverse map. The source's occurrence geometry, its accepted epoch, inverse
temperature and a storage wait are different data. No physical spatial metric
or physical clock is recovered from the declared modal cut.

The result proves a source-to-memory operation and transport of this consumer
task. It does not recover the discarded spectators, erased inter-charge
coherences or an original unknown source from memory. It supplies one leg of
the four-expression programme, whose other recovery and native-realization
obligations remain open in §7.

## 2. Full thermal preparation and the joint reference contract

**Definition 2.1 (the fixed native-derived thermal inputs).** Stop the actual
singleton substitution $\beta\mapsto\langle\beta,\alpha\rangle$ after its first
accepted step. In coordinate order $(r,\ell,R)$ retain $G_0=[1]$, $K=I_2$,
the unchanged unit-edge form and the two residual settings

$$
L_\star=\begin{pmatrix}2&-1&-1\\-1&1&0\\-1&0&1\end{pmatrix},\quad
T=(1,1,1)^{\mathsf T},\quad
q_a=(1/6,1/6)^{\mathsf T},\quad q_b=(1/3,1/3)^{\mathsf T}.
\tag{QSSR.1}
$$

For $q=(u,v)$ put $\pi_q=(1-u-v,u,v)^{\mathsf T}$ and
$G_q=L_\star+\pi_q\pi_q^{\mathsf T}$. VI139–140 gives the positive principal
root $S_q$, the normalized unit vector $V_q=S_qT$, and

$$
H_q=S_q^{-1}L_\star S_q^{-1}=I-V_qV_q^*,\qquad
V_a=(10,7,7)^{\mathsf T}/\sqrt{198},\qquad V_b=T/\sqrt3.
\tag{QSSR.2}
$$

Complexify these normalized coordinates and declare
$A=\mathbb C e_\ell$, $B=\operatorname{span}(e_r,e_R)$, so
$p=|(V_q)_\ell|^2$ equals $49/198$ or $1/3$. This is exactly the cut of
VI140.4. It is added quantum-model data; principal-root mixing does not make
it a physical partition of raw occurrence coordinates.

For any finite inverse temperature $\theta\ge0$, write

$$
t=e^{-\theta}\in(0,1],\qquad
\rho_{q,\theta}=
\frac{e^{-\theta d\Gamma_-(H_q)}}{2(1+t)^2}
\quad\hbox{on }\mathcal F_-(\mathbb C^3),\qquad \dim\mathcal F_-=8.
\tag{QSSR.3}
$$

There is no particle-number conditioning, removed zero mode or chemical
potential. VI141 supplies this full state: its eigenmode occupations are
independent with probabilities $(1/2,t/(1+t),t/(1+t))$.

**Assumption 2.2 (actual producer and consumer resources).** For the chosen
known $q,\theta$, one producer releases two disjoint three-mode systems with
the joint state specified in Definition 2.4. Exact preparation at general
$\theta$ is a conditional input. Proposition 2.3 supplies one bounded
preparation at $\theta=\log7$ only. Neither premise supplies a cloning
channel for an unknown specimen. Preparation controls may cross the eventual
$A\mid B$ cut; they belong to the producer and are withdrawn on release.

The consumer has the following resources on these same released systems:
the two known B-local number-preserving alignments of VI142.3, permission
to discard each aligned spectator, four blank memory modes, four calibrated
local even mode transfers, one blank neutral qutrit at each party, the
controlled-count gates of §3, pointer readout and stable flag writing, and
the controls, readouts and isolation of §5. Each primitive is paid and
available as specified, rather than inferred from a commutation relation.
In particular, bilinear control alone is not asserted to synthesize the
controlled-count interaction with a neutral pointer. Ancillas supplied to
the consumer are local product resources, with no borrowed entanglement or
coherence between different particle numbers. Only acquired reports and
actually delivered classical inputs are available to its controller. Each
named primitive specifies its complete input-to-output map, including any
controlled evolution during that operation. No unspecified drift interval
is inserted between these maps. A sufficient order is preparation, B
alignment, spectator discard, transfer, storage isolation, controlled
counting and flag readout, followed by the legal consumer commands.

**Proposition 2.3 (a finite known-setting producer at $\log7$).** In the
declared exact-control model, seven independent fair bits per copy, three
blank source modes, three occupied reservoir modes and a known three-mode
rotation suffice to prepare the full $\rho_{q,\log7}$ for either setting.
Two independent sets of these bits and reservoirs, with a common calibrated
modal convention, prepare the base two-copy source. This is an upper
construction, not an elementary-gate or precision optimum.

Proof. Write $V_q=(\eta,\chi,\chi)^{\mathsf T}$ and set

$$
w_q=(-\sqrt2\chi,\eta/\sqrt2,\eta/\sqrt2)^{\mathsf T},\quad
d_q=(0,1,-1)^{\mathsf T}/\sqrt2,\quad M_q=[V_q,w_q,d_q].
\tag{QSSR.4}
$$

The identity $\eta^2+2\chi^2=1$ gives three unit, mutually orthogonal
columns. The last two are perpendicular to $V_q$, so
$H_q M_q=M_q\operatorname{diag}(0,1,1)$. Take independent bits
$C_0,\ldots,C_6$. Fill eigenmode zero when $C_0=1$, eigenmode one when
$C_1=C_2=C_3=1$, and eigenmode two when $C_4=C_5=C_6=1$. A conditional
swap from its occupied reservoir fills an empty source mode without changing
the combined particle number. Unused occupied reservoirs remain outside the
released source. Fixed-order reservoir/source transfers fix all ket phases;
these phases cannot affect the diagonal occupation mixture.

The three occupations $m_0,m_1,m_2$ are independent with probabilities
$(1/2,1/8,1/8)$. Their joint weight is

$$
\frac12\prod_{j=1}^2
  (1/8)^{m_j}(7/8)^{1-m_j}
=\frac{(1/7)^{m_1+m_2}}{2(1+1/7)^2}.
\tag{QSSR.5}
$$

Apply $\Gamma_-(M_q)$ to the source, then release it without the coin and
reservoir records. On every occupied exterior basis vector this rotation
maps the eigenmode ket to the corresponding eigenket of $d\Gamma_-(H_q)$.
Tracing the inaccessible records therefore gives (QSSR.3), including its
vacuum, one-, two- and three-particle components. This finite occupation
proof uses the usual second-quantization law and requires no infinite-Fock
limit. Independent occupation bits do not independently randomize modal
phases: the two $M_q$ controls use the same reference convention. The same
argument with probabilities $(1/2,t/(1+t),t/(1+t))$ is conditional algebra
at other temperatures; the seven-fair-bit implementation is asserted only
for the values in (QSSR.5). ∎

**Definition 2.4 (joint copies and their reference variation).** Use creation
order $(A,b,d)$ after each B alignment, where $b$ is parallel to the B part
of $V_q$ and $d$ is perpendicular. The actual applied alignment is
$I_A\otimes\Gamma(U_{B,q})^*$ with $U_{B,q}$ as in VI142.3. VI142.5–142.6
then gives, before discarding $d$,

$$
\sigma\otimes\tau,\quad \tau=\operatorname{diag}(1,t)/(1+t),\quad
\sigma=\begin{pmatrix}
a&0&0&0\\0&b&z&0\\0&z&c&0\\0&0&0&d
\end{pmatrix},
\tag{QSSR.6}
$$

in effective basis $(00,01,10,11)$, where the scalar $d$ below is distinct
from the spectator mode named $d$:

$$
\begin{aligned}
D&=2(1+t),& a&=1/D,& d&=t/D,\\
b&=[1-(1-t)p]/D,&
c&=[t+(1-t)p]/D,& z&=(1-t)\sqrt{p(1-p)}/D.
\end{aligned}
\tag{QSSR.7}
$$

The **base source** consists of two independent full Gibbs preparations in
this common chart. Its reduced input is the even copy product
$\sigma\otimes\sigma$ in copy order $(A_1,b_1,A_2,b_2)$.

For a stated reference variation, let $\mu$ be an actual joint probability
law on two phases, set $D_\phi=e^{i\phi n_A}$ and
$\sigma_\phi=D_\phi\sigma D_\phi^*$, and supply the conditional product
$\sigma_{\phi_1}\otimes\sigma_{\phi_2}$ before averaging with $\mu$.
Thus $(\sigma_\phi)_{10,01}=z e^{i\phi}$. Define

$$
\kappa=\int e^{i(\phi_1-\phi_2)}\,d\mu(\phi_1,\phi_2),
\qquad |\kappa|\le1.
\tag{QSSR.8}
$$

At the full three-mode level these are the same phase conjugations of
$\rho_{q,\theta}$; they commute with the B alignment. A phase-conjugated
state is thermal for the conjugated Hamiltonian. It is generally different
from the unmodified Gibbs density for fixed $H_q$ in a fixed chart. This
variation is therefore explicitly a different joint preparation/reference
contract, not a claim that all phases leave (QSSR.3) unchanged. The base
source has $\phi_1=\phi_2=0$, hence $\kappa=1$. The temperature domain of
both conditional constructions remains every finite $\theta\ge0$.

For either contract discard only the two B spectators and express the
remaining state in party order. Define the occupation identification

$$
R|i,j,k,l\rangle=(-1)^{jk}|i,k,j,l\rangle,
\qquad
\Omega=R\left(\int\sigma_{\phi_1}\otimes\sigma_{\phi_2}\,d\mu\right)R^*.
\tag{QSSR.9}
$$

Here party order is $(A_1,A_2,b_1,b_2)$; the base source is the point-mass
case. The minus sign is the CAR reordering sign, not a nonlocal gate
granted to the consumer. Spectator removal is valid also in the full
six-mode system: the spectators are diagonal in occupation, and each
effective copy commutes with its total number. Moving a spectator past a
copy introduces its occupation times that copy's parity, whose conjugation
leaves the even density unchanged. After this identification the spectator
factors trace to one. No measurement of an active particle sector occurred.

## 3. The attained instrument, including every charge outcome

Let $\mathcal H_{j,n}$ be the charge-$n$ subspace of the two modes at
party $j\in\{A,B\}$. Their dimensions are $(1,2,1)$ for $n=0,1,2$.
Write $\Pi^j_n$ for their projectors, $I_{j,1}$ for the identity on
$\mathcal H_{j,1}$, and $P^j_0=|00\rangle\langle00|$,
$P^j_2=|11\rangle\langle11|$. Put
$\Pi_{nm}=\Pi^A_n\otimes\Pi^B_m$.

**Theorem 3.1 (complete thermal charge-to-memory relation).** Assume
Definition 2.1, the actual joint contract of Definition 2.4 and the
resources of Assumption 2.2. For either $q$, every finite $\theta\ge0$
and every supplied $\mu$, local controlled counting and transfer into blank
memory attain the trace-one state

$$
F_{q,\theta,\mu}
=\sum_{n,m=0}^2 |n\rangle\langle n|_{F_A}
 \otimes |m\rangle\langle m|_{F_B}\otimes J B_{nm}J^*,
\qquad B_{nm}=\Pi_{nm}\Omega\Pi_{nm},
\tag{QSSR.10}
$$

where $J$ is the calibrated occupation transfer in §5. Flags are local:
the memory bipartition groups $F_A$ with A modes and $F_B$ with B modes.
The eight noncentral unnormalized blocks are

$$
\begin{array}{lll}
B_{00}=a^2P^A_0\otimes P^B_0,&
B_{01}=abP^A_0\otimes I_{B,1},&
B_{02}=b^2P^A_0\otimes P^B_2,\\
B_{10}=acI_{A,1}\otimes P^B_0,& &
B_{12}=bdI_{A,1}\otimes P^B_2,\\
B_{20}=c^2P^A_2\otimes P^B_0,&
B_{21}=cdP^A_2\otimes I_{B,1},&
B_{22}=d^2P^A_2\otimes P^B_2.
\end{array}
\tag{QSSR.11}
$$

In local charge-one bases $|0_L\rangle=|10\rangle$,
$|1_L\rangle=|01\rangle$, the remaining block is

$$
B_{11}=\begin{pmatrix}
ad&0&0&0\\
0&bc&-\kappa z^2&0\\
0&-\overline\kappa z^2&bc&0\\
0&0&0&ad
\end{pmatrix}.
\tag{QSSR.12}
$$

The initial outcome-probability table, with row $n$ and column $m$, is

$$
(w_{nm})=\begin{pmatrix}
a^2&2ab&b^2\\
2ac&2(ad+bc)&2bd\\
c^2&2cd&d^2
\end{pmatrix}.
\tag{QSSR.13}
$$

Every entry is positive for these two settings at every finite temperature
in the stated domain. Every outcome is reported and retained, with
conditional memory $JB_{nm}J^*/w_{nm}$. No success conditioning is part of
the trace-preserving conversion. The legal continuation on all these states
is specified and proved in Theorem 5.2.

Proof. At party $j$ take a neutral qutrit with blank $|0\rangle$, shift
$X_3|r\rangle=|r+1\bmod3\rangle$ and available interaction

$$
U_{\mathrm{count},j}=\sum_{n=0}^2\Pi^j_n\otimes X_3^n.
\tag{QSSR.14}
$$

Orthogonality and completeness of the $\Pi^j_n$ give both products with
the adjoint equal to identity. This gate commutes with local number and
with the storage Hamiltonian of §5. Applying it to a blank pointer and
reading the pointer basis gives exactly the Kraus operator $\Pi^j_n$ for
outcome $n$. Reading both pointers therefore produces $B_{nm}$, with the
displayed flag. The sum of branch traces is $\operatorname{Tr}\Omega=1$.
Pointer readout includes dephasing and stable writing of the classical
result; an unread coherent pointer is not silently used as a classical flag.

For the block computation, the diagonals of the copy state are $(a,b,c,d)$.
A single off-diagonal term interchanges $01$ and $10$ and changes A charge
by one. Pinching by total A and B charges removes such a term unless a
second copy makes the opposite interchange. The surviving pair lies only
in $\mathcal H_{A,1}\otimes\mathcal H_{B,1}$. Its upper central entry,
in the local bases of the statement, comes from row copy occupations
$(10,01)$ and column occupations $(01,10)$. Their copy-product matrix
element is $z^2 e^{i(\phi_1-\phi_2)}$. The row has reordering sign $+1$
and the column has sign $-1$ in (QSSR.9). Integrating gives
$-\kappa z^2$; the reverse entry is its conjugate. The outer central
diagonals arise from one double occupation and one vacuum, giving $ad$;
the middle ones give $bc$. This proves (QSSR.12). Multiplying the diagonal
weights for the other occupation possibilities gives (QSSR.11).

Taking traces gives (QSSR.13). Its sum is
$(a+b+c+d)^2=1$. Since $t>0$ and $0<p<1$, each of $a,b,c,d$ is strictly
positive, proving the all-outcome assertion even when $z=0$. The transfers
proved in §5 carry these complete branch states into blank memory and
commute with the charge instrument under the occupation identification.
Thus (QSSR.10) is an attained instrument output, not just a prescribed
family of normalized conditional matrices. ∎

Measuring both rail occupations and then forgetting which rail was occupied
would give the same charge probabilities but erase the central coherence.
It is a different instrument. The available controlled count (QSSR.14)
measures only the degenerate total charge; this distinction is essential to
the actual attained state.

## 4. Exact thermal noise and joint-phase conditions

**Theorem 4.1 (retained entanglement and all failure regimes).** For the
complete state of Theorem 3.1, set $r=|\kappa|z^2$. Its ordinary
occupation-tensor partial-transpose negativity, with local flags included,
is

$$
\mathcal N(F)=\frac{\|F^{T_B}\|_1-1}{2}
=\max(0,r-ad).
\tag{QSSR.15}
$$

The output is separable if and only if $r\le ad$, and is NPT otherwise.
Equivalently, its exact entanglement condition is

$$
|\kappa|(1-t)^2p(1-p)>t.
\tag{QSSR.16}
$$

For the base source, or any common phase with $\phi_1=\phi_2$ almost surely,
$\kappa=1$. Then $P=w_{11}=2(2ad+z^2)$ and the normalized central block is

$$
\frac{B_{11}}P=(1-s)\frac{I_4}{4}
 +s|\psi_-\rangle\langle\psi_-|,\quad
s=\frac{z^2}{2ad+z^2},\quad
|\psi_-\rangle=(|0_L1_L\rangle-|1_L0_L\rangle)/\sqrt2.
\tag{QSSR.17}
$$

Thus the base retained resource is entangled precisely on the VI144.2
ordinary NPT temperature domain, now within a locally fixed-charge usable
sector. At $\theta=\log7$, model $b$ has
$P=11/64$, $s=4/11$, $\mathcal N(F)=1/256$. Model $a$ has zero negativity
and is separable. With the phase variation, model $b$ at this temperature
is entangled exactly when $|\kappa|>7/8$.

Proof. Direct expansion of (QSSR.7) gives

$$
bc-ad=\frac{(1-t)^2p(1-p)}{D^2}=z^2.
\tag{QSSR.18}
$$

The eight blocks (QSSR.11) are separable products of positive local
matrices. A local diagonal unitary on the A charge-one space changes
$\kappa$ to $|\kappa|$ in (QSSR.12); this is a mathematical local change
of basis irrespective of whether its angle has been learned by a consumer.
The partial transpose of that block has two singleton eigenvalues $bc$
and a corner with eigenvalues $ad+r$ and $ad-r$. Therefore $r>ad$ gives
a negative eigenvalue, which no separable state can have: transposition
preserves positivity on each factor of a product-state decomposition.

For sufficiency of separability, no higher-dimensional PPT criterion is
needed. In the two logical qubits let

$$
W_{1/3}=\frac16\sum_{k\in\{x,y,z\}}\sum_{\epsilon=\pm1}
 |\epsilon k\rangle\langle\epsilon k|
 \otimes|-\epsilon k\rangle\langle-\epsilon k|.
\tag{QSSR.19}
$$

Expanding the Pauli eigenprojectors gives
$W_{1/3}=I_4/4-(X\otimes X+Y\otimes Y+Z\otimes Z)/12$.
Its diagonals are $(1,2,2,1)/6$ and its two central off-diagonals are
$-1/6$. If $r\le ad$, the phase-adjusted $B_{11}$ is

$$
6rW_{1/3}
 +\operatorname{diag}(ad-r,\ bc-2r,\ bc-2r,\ ad-r).
\tag{QSSR.20}
$$

Every displayed diagonal remainder is nonnegative: $ad\ge r$ and
$bc=ad+z^2$ with $z^2\ge r$. Each diagonal ray is a product ray.
Undoing the local phase proves separability, including equality. Local
orthogonal flags make the partial transpose a direct sum of unnormalized
block partial transposes. The only possible negative eigenvalue is $ad-r$,
so trace-norm additivity gives (QSSR.15) and (QSSR.16).

When $\kappa=1$, (QSSR.18) converts (QSSR.12) into (QSSR.17). Its partial
transpose has eigenvalues $(1-3s)/4$ and $(1+s)/4$ three times, consistently
with the unnormalized calculation. At $t=1/7$, model $b$ has

$$
a=7/16,\quad b=5/16,\quad c=3/16,\quad d=1/16,\quad
z=2\sqrt2/16,\quad ad=7/256,\quad z^2=8/256.
\tag{QSSR.21}
$$

This gives all asserted values and the phase threshold $7/8$. For model $a$,
$ad=7623/528^2$ and $z^2=7301/528^2$, so $z^2-ad=-322/528^2<0$;
all $|\kappa|\le1$ are separable. At $\theta=0$, $z=0$ and every output
is separable. For $\kappa=1$, division of (QSSR.16) by $t>0$ recovers
$4\sinh^2(\theta/2)p(1-p)>1$, with the two VI144.3 thresholds and their
separable equality cases unchanged. No zero-temperature endpoint was used. ∎

**Corollary 4.2 (identical one-copy marginals, different attained memory).**
Fix model $b$ and $\theta=\log7$. A common uniformly random phase
$\phi_1=\phi_2$ and independent uniformly random phases have identical
one-copy phase-averaged densities, including their spectators. The first
source attains negativity $1/256$; the second attains a separable output.

Proof. In either source each one-copy average removes the two entries
proportional to $z e^{\pm i\phi}$ and leaves the same diagonal. For the
common source (QSSR.8) is one; for the independent source the two phase
integrals factor and are zero. Apply Theorem 4.1. Thus no inference from
these marginals alone determines which retained resource is available.
This is a counterpair of actual joint preparation laws, not an obstruction
to all additional reference resources. ∎

A fixed relative phase offset gives $|\kappa|=1$; a known offset can be
corrected by a local rail phase. For independent but nonuniform phases,
$\kappa=\mathbb E(e^{i\phi_1})\overline{\mathbb E(e^{i\phi_2})}$, which
need not vanish. “Independent” alone is not interchangeable with “uniformly
dephased.” Conversely, an unknown $\arg\kappa$ is not supplied to a controller
by the entanglement criterion. A prescribed joint law or a separately paid
calibration is needed to implement its optimal phase adjustment.

## 5. Actual installation, storage and every legal finite continuation

**Definition 5.1 (released memory and command interface).** At party $j$
write its source modes as $s_{j1},s_{j2}$ and blank memory modes as
$m_{j1},m_{j2}$. Each allowed transfer is the second quantization of the
two-mode rotation $s_{ji}\mapsto m_{ji}$,
$m_{ji}\mapsto-s_{ji}$, with identity on other modes. It is generated by
an even local hopping bilinear. Choose source and memory creation orders
within parties as rail one then rail two, and A before B. The product of
the four transfers defines the occupation isometry $J$ from source Fock
space to memory Fock space. After conversion the source is evacuated,
decoupled and inaccessible; flags are stable classical records.

Isolation switches the retained modes to

$$
H_M=\varepsilon_A N_A+\varepsilon_B N_B
\tag{QSSR.22}
$$

with real fixed $\varepsilon_A,\varepsilon_B$, no residual couplings,
degenerate rails at each party, and identity dynamics on the classical
records. The switching and preservation are apparatus premises. They do
not follow from thermal stationarity for the original $d\Gamma_-(H_q)$.

On each party's entire two-mode Fock space define

$$
X_j=m_{j1}^\dagger m_{j2}+m_{j2}^\dagger m_{j1},\quad
Y_j=-i(m_{j1}^\dagger m_{j2}-m_{j2}^\dagger m_{j1}),\quad
Z_j=n_{j1}-n_{j2}.
\tag{QSSR.23}
$$

The declared commands are Stop; Wait$(h)$ for any supplied finite $h\ge0$;
an addressed finite local rotation generated by these $X_j,Y_j,Z_j$;
local occupation readout, optionally preceded by such a rotation; and
classical sending, receipt or copying of an available report. Readout has
the complete four-outcome occupation projectors
$Q^j_y=|y_1y_2\rangle\langle y_1y_2|$ for $y\in\{0,1\}^2$.
An optional rotation $U_j$ gives branch Kraus operator $Q^j_yU_j$; a
no-read rotation has its single Kraus operator $U_j$. Every read requires
a declared blank or reset readout apparatus and writes its actual result.
These instruments are additional explicit primitives, including their
disturbance, and are defined on charges zero and two as well as one.
The orthogonal occupation projectors sum to identity, so
$\sum_y(Q_yU_j)^*(Q_yU_j)=I$: every readout menu is complete and its sum
over outcomes is trace preserving. For a simultaneous product readout use
all pairs of local outcomes, with Kraus operators
$(Q^A_yU_A)\otimes(Q^B_vU_B)$ and both reports retained.

An admissible policy chooses the next command using only the party's own
available flags, acquired outcomes, controller inputs and received messages.
The policy and its control prices are fixed together with the interface.
If a controller uses both flags, they must have been transmitted to it.
There is no implicit joint selector or access to discarded producer coins.
All actually retained reports form its archive. A family of finite words
does not assert a uniform bound on this archive.

**Theorem 5.2 (branchwise installation and continued use).** The physical
transfers in Definition 5.1 install the whole state (QSSR.10), including
every charge outcome. That state, and every state reachable by the declared
commands, is stationary during every finite storage wait. For every finite
admissible adaptive command history, its probability, retained reports,
enabled next commands and unnormalized quantum successor agree with those
on the released post-instrument carrier under the fixed occupation transfer.
This comparison uses the same released charge storage dynamics on the
carrier. It asserts neither intertwining with the original thermal
Hamiltonian nor with native Read/Apply evolution.

Proof. For a source occupation word with blank memories, the one-particle
rotation of each transfer sends its occupied source creation operator to
the corresponding memory creation operator. Acting on the vacuum and
wedging in the fixed order gives

$$
U_{\mathrm{tr}}(|x\rangle_S\otimes|0000\rangle_M)
=|0000\rangle_S\otimes J|x\rangle_M
\quad\hbox{for every }x\in\{0,1\}^4.
\tag{QSSR.24}
$$

The disjoint hopping unitaries are even and commute, so the transfers at
A and B are local operations despite the CAR grading of individual fields.
The chosen one-particle phases and ordered wedge fix (QSSR.24) without an
occupation-dependent correction. Linearity proves the equality for every
matrix, including correlations with inaccessible external environments.
Tracing the evacuated source therefore leaves $JDJ^*$ on memory for any
source density $D$, rather than only for a favorable charge block.

For each charge projector, occupation projector and the source counterpart
of each bilinear in (QSSR.23), the same occupation calculation gives

$$
J\Pi^S_{nm}=\Pi^M_{nm}J,\qquad
JQ^S_y=Q^M_yJ,\qquad JO^S_j=O^M_jJ\quad(O=X,Y,Z).
\tag{QSSR.25}
$$

Exponentiating finite matrices gives the rotation equality. Hence counting
then transferring and transferring then counting give identical flagged
branches. This proves the attained transfer assertion in Theorem 3.1 and
the agreement of those two actual installation orders. It does not create
two simultaneously existing copies of the released unknown quantum state.

Each matrix (QSSR.23) acts as its named Pauli matrix on $(10,01)$ and
vanishes on $00,11$, directly by the CAR occupation action. All its
rotations and all $Q_y$ commute with the local charge projectors. Every
reachable state is therefore block diagonal in $(n,m)$. On such a block
(QSSR.22) is the scalar $\varepsilon_A n+\varepsilon_B m$, so conjugation
by $e^{-ihH_M}$ is the identity for every finite $h$. This proves storage
for the entire output and for all disturbed reachable states, including
the eight noncentral sectors. It would fail for an unspecified residual
rail splitting or coupling; those are excluded by the isolation premise.

For a finite history $\gamma$ denote its unnormalized successor by $D_\gamma$.
Its trace is the history probability. Starting with a recorded $(n,m)$,
$D_{nm}=B_{nm}$ and $D^M_{nm}=JB_{nm}J^*$. If the next command has branch
$y$ with Kraus operator $K_y$, define, without dividing,

$$
D_{\gamma y}=K_yD_\gamma K_y^*,\qquad
D^M_{\gamma y}=K^M_yD^M_\gamma(K^M_y)^*.
\tag{QSSR.26}
$$

Equations (QSSR.25) and the equal released storage dynamics give
$K^M_yJ=JK^S_y$. Thus $D^M_{\gamma y}=JD^S_{\gamma y}J^*$ and their
traces agree. At a zero-probability branch both matrices are zero; there
is no invented conditional state. At positive trace normalization gives
the corresponding actual conditional states. Commands and results are
appended to the same accessible archives, so both descriptions make the
same next policy choice. Classical transmissions update the recipient's
available reports only upon receipt and have the same specified successor
and price. Stop ends the same branch. Induction proves the assertion for
every finite history, retaining all readout outcomes and their disturbance.
No incompatible measurements are assumed to have simultaneous values. ∎

**Proposition 5.3 (a concrete legal use of the stored relation).** With the
base source define the all-outcome operator

$$
W=\frac{\Pi_{11}+X_A X_B+Y_A Y_B+Z_A Z_B}{4},
\qquad \operatorname{Tr}(WF)=ad-z^2.
\tag{QSSR.27}
$$

Tensor identities on flags are implicit. The operator is zero outside
$(1,1)$ and is a nonnegative-expectation entanglement witness on separable
states. Its component expectations are obtainable by legal product
settings after any finite storage wait. For a phase variation with a
supplied correcting angle, the rotated witness has expectation $ad-r$.

Proof. On the central block, $W=(I+X\otimes X+Y\otimes Y+Z\otimes Z)/4$.
For a product of logical qubit states with Bloch vectors $u,v$, its
expectation is $(1+u\cdot v)/4\ge0$. A separable state restricted by local
$\Pi_1$ projections remains a positive sum of products, so extending by
zero gives the all-outcome witness. From (QSSR.12), for the base source,

$$
\operatorname{Tr}(\Pi_{11}F)=2(ad+bc),\quad
\langle X_AX_B\rangle=\langle Y_AY_B\rangle=-2z^2,\quad
\langle Z_AZ_B\rangle=2(ad-bc)=-2z^2.
\tag{QSSR.28}
$$

Substitution yields (QSSR.27). At model $b$, $\log7$, it is $-1/256$.
Local rotations generated by (QSSR.23) rotate the charge-one occupation
difference into X or Y. Read the two occupations after the selected
rotation, assigning result zero at local charges zero or two and $\pm1$
at charge one. The product of the two actual reports estimates the
corresponding correlation; the flags supply $\Pi_{11}$. These are three
separate product settings on fresh preparations, not three undisturbed
uses of one stored pair. A fixed common programmed setting per run suffices;
if instead a party chooses it, the setting must actually be communicated.
Combining reports requires actual communication and retained records.

For known $\arg\kappa$, the charge-preserving A rail phase
$\operatorname{diag}(e^{-i\arg\kappa},1)$ in its logical space makes the
central coherence $-r$. The same calculation gives $ad-r$. Without this
calibration, (QSSR.27) yields $ad-\operatorname{Re}\kappa\,z^2$, not
automatically the modulus bound. Readout has the successor (QSSR.26) and
can consume entanglement. A single flag or witness result certifies no
unknown density; expectation estimation requires actual repeated sources.
No statistical confidence or optimized sample bound is asserted here. ∎

## 6. Same-run resources and the in-place alternative

**Proposition 6.1 (a sufficient preparation-to-retention account).** At
$\theta=\log7$ for the base source, a sufficient conversion run uses the
following macro-resources, on every charge outcome:

| Resource or operation | Sufficient count and condition |
| --- | --- |
| Full three-mode source preparations | 2, with the same known $q$ and modal convention |
| Fresh fair-bit preparations and reads | 14 of each; disjoint bits for the two copies |
| Initially blank source modes | 6 |
| Initially occupied reservoir modes | 6 available; at most 6 conditional fills |
| Coin logic | Four three-bit conjunctions and six occupation-controlled fill decisions |
| Known three-mode preparation rotations | 2 applications of $\Gamma_-(M_q)$ |
| B alignments and spectator discards | 2 of each, as in VI142.5 |
| Initially blank memory modes and local transfers | 4 of each |
| Blank neutral qutrits | 2 |
| Controlled-count gates | 2 |
| Pointer reads and flag writes | 2 of each, with local trit records |
| Release and storage isolation | Actual producer withdrawal and the specified switch to (QSSR.22) |
| Initial retained consumer material | Four fermionic modes and two trits |

Proof. Proposition 2.3 gives each full preparation and its environment.
Definition 2.4 removes exactly two spectator modes. Theorem 3.1 performs
both charge measurements without rejecting any outcome, and Theorem 5.2
transfers four active modes and preserves their full flagged state. These
operations precede any selection of a later consumer, so their bills are
paid on separable and noncentral branches as well as on entangled ones.
This establishes the displayed account on a common run. ∎

These are counts of declared exact primitives, not microscopic gate counts,
energy costs, work extraction, duration or optimal prices. Internal control
logic, exact calibration, occupied-reservoir supply, isolation and flag
stability are separately paid assumptions. A general $\mu$ additionally
requires its actual phase-producing mechanism; Proposition 2.3 claims no
finite exact sampling recipe for arbitrary $\mu$. Similarly, the fourteen
fair-bit account is not extended to arbitrary real $\theta$.

For a later realized word, add its actual number of rotations, occupation
instruments, blank/reset readout resources, writes and messages, and its
finite wait durations. Two directed trit transmissions suffice to exchange
the initial flags when both parties need both flags; they do not also pay
for later settings or outcomes. A central observer instead needs the
corresponding deliveries to its own readable store. The reported quantum
occupation outcomes, command labels and received messages enlarge the
classical archive with the actual finite history. Fixed-size quantum
retention does not bound arbitrary later record memory. Witness repetition
uses another complete paid preparation for each independently sampled run.

**Proposition 6.2 (in-place storage under its actual premise).** If the
released, aligned four effective modes themselves admit the isolation,
addressed controls, pointers and later access of Definition 5.1, then
retaining them in place attains the same instrument and consumer task
without four additional blank memory modes or four transfers.

Proof. Use those released modes as the retained bank, so $J$ is their
identity identification. Equations (QSSR.10)–(QSSR.28) apply directly;
their only use of transfers was the occupation intertwining already
provided by identity. The producer still withdraws, spectators are still
discarded, flags are still acquired and isolation is still required. ∎

This is a sufficient alternative conditional on real access and storage
capabilities at that location. It proves no total-price ordering between
different hardware locations. For the stated two-rail task, two local
modes give a two-dimensional charge-one space, whereas the single A mode
of VI145 has only one-dimensional local charge spaces and a separable
SSR representative. Local invariant product ancillas and local operations
cannot turn that representative into entanglement. Thus the base model $b$
construction exhibits a one-versus-two specimen benefit under the declared
ancillary contract. It does not prove two specimens, four transferred modes
or two qutrit pointers globally minimal over other reference resources,
encodings, tasks or instruments. Three distinguishable pointer outcomes are
used to report all three local charges faithfully, a requirement of this
complete instrument rather than an optimum for a binary herald alone.

## 7. Reused suppliers, exact delta and remaining obligations

VI149–150 and 152 already supply the base $\kappa=1$ CAR block, singlet
mixture, effective success probability, partial-transpose spectrum,
number-twirled negativity and thermal thresholds used in (QSSR.12),
(QSSR.15)–(QSSR.18) and (QSSR.21). VI147 and 154, together with Joint
Relations and Clocks §§2.1.6 and 2.2.6, supply the common-versus-independent
reference distinction and the joint-access distinction from a single-copy
twirl. Those results are reused, without independent new-content credit.

The `repo-derived` contribution relative to these suppliers is the
source-specific preparation-to-retained-use relation of Theorems 3.1,
4.1 and 5.2: for an arbitrary supplied joint phase law, the surviving
coherence is $-\kappa z^2$, its exact entanglement criterion is
$|\kappa|z^2>ad$, and the complete nine-outcome flagged instrument is
installed in isolated memory with every declared finite legal continuation.
Proposition 2.3 supplies the finite known-setting producer at $\log7$;
general-temperature preparation and arbitrary phase-law production remain
conditional inputs. Corollary 4.2 is the corresponding thermal-memory
instance of the existing common-versus-independent-source mechanism.
The explicit separable branches, transfers, storage, witness menu and
same-run resource account complete this conditional operational synthesis.
Generic activation, pinching, pointers, dual rails, storage and branch
induction are reused mechanisms.

| Supplier and evidence class | Exact correspondence and retained limit |
| --- | --- |
| VI127.1, 127.2, 128.3 and 139–146, `repo-derived` supplier | The actual stopped singleton birth, two interior metrics, principal-root normalization, full eight-dimensional Gibbs inputs, B-local factorization, ordinary PPT boundary and single-copy SSR limit. No physical quantum preparation or storage follows from the native metric transport. |
| VI147–150, 152 and 155–156 at the separately specified revision, `repo-derived` supplier | Same-setting full Gibbs copies with compatible references; (148.1)–(148.3) give the coefficients and $bc=ad+z^2$; (149.1), (149.4), (149.6), (150.1)–(150.5) and (152.1)–(152.4) give the base CAR block, singlet mixture, effective probability, PPT spectrum, total effective number-twirl negativity, thresholds and $\log7$ values. VI148.4 and 156[M] credit the mixed-state SSR method to Schuch–Verstraete–Cirac, quant-ph/0404079v1, §IV.D.1–2. These supply the $\kappa=1$ algebra here; the arbitrary joint phase law and complete preparation-to-retained-use interface are the extension. |
| VI151 and 153–154 at the separately specified revision, `repo-derived` supplier | VI151's spectator-inclusive common filter has probability $343/2048$ at model $b$, $\log7$; it differs from our aligned, spectator-discarded instrument with central probability $11/64$. VI153's total-parity twirl has additional even-sector coherence and a different total negativity; it is not (QSSR.15). VI154's source-versus-single-copy-twirl joint readout is credited; Corollary 4.2 specializes the reference distinction to the retained-memory task. |
| Joint Relations and Clocks §2.1.3–2.1.6, equations TM.120–132; §2.2.6, TM.152, `repo-derived` supplier | Explicit pointer resource contracts, branchwise rather than averaged descent, and common versus independently randomized sources. The local qutrit gate and the thermal branch calculation above instantiate these mechanisms; no unrestricted effect implementation is presumed. |
| `D5/S3/Quantum/FockSpace/FiniteOccupationPartitionFunctions.lean` and its owning Scribe, existing source | Its finite diagonal binary occupation sum is credited. Here the three eigenvalues are $(0,1,1)$; the finite exterior-basis proof supplies the exact preparation correspondence. Its bosonic cutoff statement is not substituted for a full bosonic Gibbs state with a zero mode. |
| `D5/S3/Quantum/Fibers/FiveModeTwoCopyPhase.lean` and its owning Scribe, existing source | `two_copy_bell_readout` concerns a different five-coordinate mixture, a specified real Bell effect, and probability $(1+(1-2q)^2)/4$. Its scalar parameter is not this residual vector $q$; it supplies neither the thermal producer nor our local charge instrument or retained task. |
| `D5/S3/Quantum/Fermionic/PhysicalSiteProducts.lean` and its owning Scribe, existing source | Physicality is parity commutation; actual site partial traces preserve it, and physical product states obey its inter-site cancellation theorem. Ordinary occupation notation here does not make odd B fields local or make a nonphysical product decomposition a free fermionic preparation. Our surviving block decompositions use fixed local charge states. |
| Recovery Geometry §§10–14, Process Geometry §§12,17,19 and Native Paid View Conversion §§1,6–10, existing ordinary suppliers | Acquired records, task-relative future response, installed paid calls, ownership and return retain their own premises. PVC's fixed-H entrance and added converter do not install quantum source, phase or memory primitives; no native compiler or four-view inverse is inferred from the present finite isometry. |
| Jan Dereziński, *qft-lectures*, §§5.7,5.9, Theorem 5.3, `literature-attested` | Second quantization and the Fock direct-sum/exponential law support the finite occupation model. The retrieved unversioned edition is the supplied source identity, without a historical byte-equivalence claim. Its printed odd-field typography is not used to remove CAR parity strings: the ordered creation-word argument above supplies all signs. [Primary PDF](https://www.fuw.edu.pl/~derezins/qft-lectures.pdf). |
| M., P., and R. Horodecki, *Separability of Mixed States: Necessary and Sufficient Conditions*, quant-ph/9605038v2, Theorem 3, PDF p.8, `literature-attested` | PPT sufficiency in $2\times2$ or $2\times3$ supports VI's effective two-qubit criterion. We use no arbitrary $2\times4$ PPT sufficiency; (QSSR.20) proves separability of our block and its flags directly. [Primary PDF](https://arxiv.org/pdf/quant-ph/9605038v2). |
| H. M. Wiseman and J. A. Vaccaro, quant-ph/0210002v2, equations (12)–(14), Table I, `literature-attested` | Pure fixed-total-number SSR resource context, including two-copy benefit. Its pure-state average is not a formula for our full mixed Gibbs state's negativity or an ebit yield. [Primary PDF](https://arxiv.org/pdf/quant-ph/0210002v2). |
| S. D. Bartlett, T. Rudolph and R. W. Spekkens, quant-ph/0610030v3, II.B, III.C.2–3, equations (2.9),(3.32),(3.33), `literature-attested` | Local number pinching, allowed dual-rail controls, two-copy pure-state activation and mixed-state local-twirl/register context are already established. Equation (3.33)'s maximization uses its stipulated freely controlled registers and LOCC resources; our explicit finite consumer and ordinary flagged negativity claim no such optimum. The fermionic application discussed in III.C.4 does not dispense with the CAR sign calculation. [Primary PDF](https://arxiv.org/pdf/quant-ph/0610030v3). |

These correspondences are limited to the stated immutable sources and
parameter maps; they assert neither exhaustive literature priority nor a
classification of other apparatus. The finite-matrix, exterior-word and
branch proofs establish conditional QSSR2 conclusions. Availability of
their exact preparations, phase controls, instruments, transfers and
isolation remains an explicit apparatus premise.

**Open obligations 7.1 (unchanged full programme).** An unknown native source
is not identified here: $q$ is a known preparation input, and an actual
charge flag occurs under both settings and throughout the thermal domain.
Original alpha/beta operations have not been shown to prepare, align,
transfer or isolate these fermionic modes or implement the neutral-pointer
interaction. Physical space, physical time and their independent recovery
from boundary or memory have not been constructed. The common realized
growing observer, all four independent view kernels, every claimed reverse
direction, route agreement and native dynamics compatibility remain to be
proved on their original domains. The original fixed-$G_{\rm gc}$,
original-Q, parked-consumer, unchanged-initialization and common-runtime
obligations and all earlier settlements are preserved. No conditional
finite apparatus closes those obligations or the sustained full objective.

## 追加锚（本行以下为增补区）
