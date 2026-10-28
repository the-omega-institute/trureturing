# FIB native three-copy real local programming

## 1. Original coordinates and the full spatial problem

**definition 1.1 (Actual sources and targets).**
Let $B=(0,1,2,3,13)$, let $f=(0\ 13)(1\ 3)$ with $f(2)=2$, and retain
the original local identifications

$$
V_Ae_j=|B_j\rangle_A,\qquad
V_Be_j=|f(B_j)\rangle_B,\qquad
Je_j=|B_j,f(B_j)\rangle,\qquad 0\le j\le4.
$$

All coefficient matrix units $E_{jk}$ refer to these ordered positions.
The two ordered coefficient pairs and four possible labels are

$$
\begin{aligned}
d_a&=(0,4),&d_b&=(1,3),\\
X_a&=i(E_{04}-E_{40}),&X_b&=i(E_{13}-E_{31}),\\
U_4&=\{X_a,-X_a,X_b,-X_b\}.
\end{aligned}
$$

For known $t,\eta\in[0,1]$, one unknown $X\in U_4$ is fixed. The program
is exactly three conditionally independent copies of the original state

$$
\rho_X=(1-\eta)J(I_5+tX)J^\dagger/5+\eta I_{25}/25.
\tag{1.1}
$$

The batch $\rho_X^{\otimes3}$ is initially independent of the entire data
and reference state. There is no prior distribution on $X$. The target,
on the entire complex matrix algebra, is

$$
\Phi_X(Y)=(1-\eta)(I_5+tX)\circ Y
                  +\eta\operatorname{tr}(Y)I_5/5,
\qquad Y\in M_5(\mathbb C).
\tag{1.2}
$$

Here $\circ$ is entrywise multiplication. The matrix $I_5+tX$ is positive
with diagonal one: on the active pair its eigenvalues are $1+t,1-t$,
and its other three eigenvalues are one. The Schur CP criterion and its
diagonal therefore make the Schur term a channel. The replacement term
is a channel, so (1.2) is CPTP, including the singular endpoints.
The source has all five matching and all twenty unmatched coordinates.

The normalized output-first Choi convention is

$$
\chi(N)=\frac15\sum_{j,k=0}^4N(E_{jk})\otimes E_{jk}.
$$

In this convention
$(V_A\otimes V_B)\chi(\Phi_X)(V_A\otimes V_B)^\dagger=\rho_X$.
This identity fixes coordinates and normalization; a programmable
implementation still requires a common channel on data and programs.
The source, target and identifications are those of
[Compound communication and calibration, C-116.1, C-121.1 and C-134.1](AURIC_FIB_ATOM_HIDDEN_RELATIONS_COMPOUND_COMMUNICATION_AND_CALIBRATION.md).

**definition 1.2 (BOTH-REAL LOCC and unhalved error).**
Alice holds the complex five-dimensional data $D$ and $A_1,A_2,A_3$;
Bob holds $B_1,B_2,B_3$ and the output with the fixed identification above.
An admissible processor $\mathcal P$ is label independent and is a
finite-round two-way LOCC channel whose every local Kraus matrix is real
in the original bases. Arbitrary finite real local ancillary states,
exact known real local controls, local measurements, discard/reset,
shared classical randomness and classical messages are allowed.
There is no common bound on round count or finite ancillary dimension
across competitors. Local mixed ancillary states are real density
matrices. They do not include additional shared entanglement.

Each processor must be complex linear, CP and TP on the entire joint
complex algebra, including off-promise programs and arbitrary correlations
among data and programs. Only its evaluated channel

$$
N_X(Y)=\mathcal P(Y\otimes\rho_X^{\otimes3})
$$

uses the promised independent batch. Every finite complex reference $R$
is untouched. Write

$$
E_3(t,\eta)=\inf_{\mathcal P}\max_{X\in U_4}
                         \|N_X-\Phi_X\|_\diamond.
\tag{1.3}
$$

The diamond norm is unhalved: it is the stabilized trace norm on all
complex inputs, equivalently the stabilized reference-state distance
for a difference of channels. The class in (1.3) allows data-first
interaction, adaptive quantum memory and arbitrary two-way histories.
It has no program-first, classical-record, first-hit, Schur-channel or
fixed-round restriction. No quantum wire, extra entangled state,
supplied imbit, sign label, physical conjugation or transpose, hidden
joint measurement across the cut, or postselection is allowed.
The original batch, local access, exact real calibration and classical
communication are mathematical premises of this optimization.

**definition 1.3 (Weights and a faithful pair decomposition).**
Use the following notation throughout this volume:

$$
\begin{aligned}
c&=(1-\eta)t,&u&=c/5,&s&=1-4\eta/5,\\
w&=s/5=(5-4\eta)/25,&n&=\eta/25,&h&=w+n=(5-3\eta)/25,\\
q&=2h,&r&=1-q=(15+6\eta)/25,&[x]_+&=\max\{x,0\}.
\end{aligned}
\tag{1.4}
$$

In particular,

$$
u=t(w-n),\quad 0\le u\le w,\quad w\ge n\ge0,\quad
5w+20n=1,\quad 3/5\le r\le21/25.
\tag{1.5}
$$

For either $d=(j,k)\in\{d_a,d_b\}$, a local bit means its prescribed
original pair: Alice uses $|B_j\rangle,|B_k\rangle$, and Bob uses
$|f(B_j)\rangle,|f(B_k)\rangle$. These are real local restrictions,
not a change of cut. On this local pair product put

$$
\begin{aligned}
A&=i(|00\rangle\langle11|-|11\rangle\langle00|),\\
P&=|00\rangle\langle00|+|11\rangle\langle11|,\\
Q&=|01\rangle\langle01|+|10\rangle\langle10|.
\end{aligned}
\tag{1.6}
$$

For the opposite labels on $d$, the actual full source is

$$
\rho_\pm=D\pm uA,\qquad D=wP+nQ+O.
\tag{1.7}
$$

The positive real diagonal $O$ is supported outside the entire
four-dimensional local pair product. It contains three other matching
coordinates of weight $w$ and eighteen unmatched coordinates of weight
$n$, so $\operatorname{tr}O=3w+18n=r$. The other two unmatched modes
are precisely $Q$. Thus (1.7) keeps all 25 modes. In particular a local
pair-product test accepts $P+Q$, with probability $q$, rather than $P$.

## 2. The bounded three-copy result

**theorem 2.1 (Full-class converse and actual simultaneous upper bound).**
For every known $t,\eta\in[0,1]$, define

$$
\begin{aligned}
B_3&=6u(1-2h+2h^2)-4u^3,\\
F_3&=2u(1+r+r^2),\\
M_3&=6ur+12u(w^2+n^2)-4u^3,\\
K_3&=\max\{F_3,M_3\}.
\end{aligned}
\tag{2.1}
$$

Then the original optimization (1.3) satisfies

$$
\boxed{[c-B_3]_+\ \le\ E_3(t,\eta)\ \le\ [c-K_3]_+.}
\tag{2.2}
$$

The lower bound quantifies over every processor in Definition 1.2.
For each fixed parameter pair, one complete finite-round real LOCC
processor, selected from two explicit protocols using only $t,\eta$,
has error exactly the upper endpoint for each of the four labels.
It is CP/TP on the entire complex joint algebra. The coefficients also
have the forms

$$
\begin{aligned}
B_3&=\frac{c(2550+540\eta+108\eta^2)-100c^3}{3125},\\
F_3&=\frac{c(2450+660\eta+72\eta^2)}{3125},\\
M_3&=\frac{c(2550+420\eta+204\eta^2)-100c^3}{3125}.
\end{aligned}
\tag{2.3}
$$

Proof. Section 3 proves the lower bound. Sections 4–7 give the complete
instruments and a parameter-only selection with the upper error.
The identities in (2.3) follow by substituting (1.4) into (2.1).
Section 8 proves the equality regions and the qualified interval width.
None of these statements asserts either endpoint to be the optimum
at general positive noise. The two-copy finite certificate is reused
as an intermediate ingredient; the additional content is its
three-copy use with the cubic contribution and the actual three-copy
local protocols. QED.

## 3. A converse for every original real LOCC processor

**theorem 3.1 (Uniform three-copy certificate bound).**
Every processor of Definition 1.2 has worst-label error at least
$[c-B_3]_+$. The same lower bound holds for limits of its induced
four-channel tuples in diamond norm.

Proof. Fix either active pair $d=(j,k)$. At Alice prepare the real local
data/reference vector

$$
|\Omega_d\rangle=
 (|0\rangle_R|e_j\rangle_D+|1\rangle_R|e_k\rangle_D)/\sqrt2.
\tag{3.1}
$$

Feed its data into an arbitrary admissible processor and keep $R$
untouched. This defines a CPTP real LOCC map $\mathcal F$ from all three
programs to $R$ at Alice and Bob's output. This deduction uses the
processor's whole-algebra validity. It is valid regardless of when the
original processor first interacts with data. The imaginary Hermitian
test

$$
W_d=i(|0,j\rangle\langle1,k|-|1,k\rangle\langle0,j|)
\tag{3.2}
$$

has operator norm one and target expectations $+c,-c$ on the two
opposite labels. It is a mathematical norm test, not a processor
operation. If the respective diamond errors are $\epsilon_+,\epsilon_-$,
put

$$
\Delta_3=\frac{\rho_+^{\otimes3}-\rho_-^{\otimes3}}2,
\qquad g=\operatorname{tr}[W_d\mathcal F(\Delta_3)].
$$

Trace-norm duality on (3.1) gives

$$
\frac{\epsilon_++\epsilon_-}{2}\ge c-g.
\tag{3.3}
$$

Indeed, if $f_\pm$ are the actual output expectations, then
$\epsilon_+\ge c-f_+$ and $\epsilon_-\ge c+f_-$, while
$g=(f_+-f_-)/2$. This accounts for the unhalved normalization.

We first establish the exact supplied two-pair interface needed to
bound $g$. This is the finite certificate of
[C-135.1](AURIC_FIB_ATOM_HIDDEN_RELATIONS_COMPOUND_COMMUNICATION_AND_CALIBRATION.md),
with its signs and support patterns made explicit here. Put

$$
C=A^{T_A}=i(|10\rangle\langle01|-|01\rangle\langle10|),
\qquad R_n=A\otimes Q+Q\otimes A.
\tag{3.4}
$$

For a CPTP real separable map $\mathcal G$ from two such pairs to a bit
$r_0$ at Alice and a bit $o$ at Bob, use the unnormalized Choi order
$(r_0,a_1,a_2,b_1,b_2,o)$:

$$
M_{r_0abo,\,sa'b'p}
 =[\mathcal G(|ab\rangle\langle a'b'|)]_{r_0o,sp}.
\tag{3.5}
$$

Then $M\ge0$ and $\operatorname{tr}_{r_0,o}M=I_{ab}$. Let $\Gamma$
transpose Alice's entire block $(r_0,a_1,a_2)$. A product real Kraus
matrix has a vectorized real factor on each side, and the corresponding
rank-one local projector is symmetric. Thus $M^\Gamma=M$.
For real LOCC, refine every local Kraus history and final discard;
each complete history has exactly such product real Kraus factors.
Arbitrary finite real ancillary states can be absorbed using real
spectral decompositions. Classical mixtures, or integrals of histories,
preserve this finite-dimensional linear identity. This proves its
necessity for the entire competitor class without a round or ancillary
size bound. It is used only as a converse condition.

On the output bits set $W=i(|00\rangle\langle11|-|11\rangle\langle00|)$,
and on the inputs set

$$
Z=Q\otimes Q+\tfrac12(A\otimes A+C\otimes C),
\qquad \operatorname{tr}Z=4,\qquad Z^{T_{a_1a_2}}=Z.
$$

A hat extends an input operator by identity on the output bits, with
the reordering in (3.5). Define

$$
H_{r_0abo,\,sa'b'p}=W_{r_0o,sp}(R_n)_{a'b',ab}.
\tag{3.6}
$$

Thus $\operatorname{tr}(MH)=\operatorname{tr}[W\mathcal G(R_n)]$;
in output/input tensor notation $H=W\otimes R_n^T=-W\otimes R_n$.
In the stated six-bit order take the supplied real vectors

$$
\begin{aligned}
v_1&=|000110\rangle-|011000\rangle,\\
v_2&=|000111\rangle-|011001\rangle-|101100\rangle-|110010\rangle,\\
v_3&=|001101\rangle+|010011\rangle+|100110\rangle-|111000\rangle,\\
v_4&=|001100\rangle+|010010\rangle,\\
v_5&=|101101\rangle+|110011\rangle,\\
v_6&=|100111\rangle-|111001\rangle,\qquad
S=\sum_{\ell=1}^6|v_\ell\rangle\langle v_\ell|\ge0.
\end{aligned}
\tag{3.7}
$$

Their sparse expansion gives the more explicit identity

$$
S=\widehat{Q\otimes Q+C\otimes C}-H^\Gamma.
\tag{3.8}
$$

Here is a complete support-pattern verification. Each support state
satisfies $b=\bar a$, the bitwise complement of $a$. For every fixed
output $(r_0,o)$, the four diagonal entries, one for each $a$, are one.
The within-output off-diagonals are $-1$ between $a=00,11$ and $+1$
between $a=01,10$, including their reverses. These are precisely the
entries of $C\otimes C$, since $C_{01,10}=-i$ and $C_{10,01}=i$.
The remaining entries connect output $01$ to $10$ with Alice strings
that differ in exactly one bit $\ell$. Their value is $-(-1)^{a_\ell}$.
To see that these are all the entries, the two four-term vectors in
(3.7) contain the output $01,10$ support states, and the other four
vectors each contain the two within-output support states for output
$00$ or $11$. Expanding these six projectors gives exactly the patterns
just listed and their Hermitian reverses, with no other nonzero entry.

Writing $C_{\rm out}=W^{T_{r_0}}$, one has

$$
-H^\Gamma=C_{\rm out}\otimes(C\otimes Q+Q\otimes C).
$$

On a listed output $01$-to-$10$ entry, $C_{\rm out}$ contributes $-i$.
The one flipped input bit contributes $-i$ for $a_\ell=0$ and $+i$
for $a_\ell=1$. Their product is exactly $-(-1)^{a_\ell}$.
This verifies (3.8), including all zero entries and signs. Transposing
Alice's block therefore gives

$$
\frac{S+S^\Gamma}{2}
   =\widehat Z-\frac{H+H^\Gamma}{2}.
\tag{3.9}
$$

Pair (3.9) with $M=M^\Gamma$. Self-adjointness of partial transpose
for the trace pairing and trace preservation yield

$$
\operatorname{tr}[W\mathcal G(R_n)]
 =\operatorname{tr}(M\widehat Z)-\operatorname{tr}(MS)
 =4-\operatorname{tr}(MS)\le4.
\tag{3.10}
$$

Only $M,S$ need to be positive; no positivity of $Z$ is asserted.
Every transpose in this argument is algebraic, never a physical gate.

We will also use (3.10) with a spectator $T\in\{P,Q,O\}$ in another
copy position. Each such $T$ is a nonnegative diagonal sum of original
real product projectors. If $z=\operatorname{tr}T>0$, locally preparing
$T/z$ with shared classical randomness before a full real LOCC map
gives (3.10) multiplied by $z$. If $z=0$, the term is zero. Copy
permutations are local real operations. Restricting each input to its
local pair is a real isometric restriction. For Bob's five-dimensional
output, the pair-identification Kraus matrix and the rows
$|0\rangle\langle e_\ell|$ for $\ell\notin\{j,k\}$ form a real CPTP
compression preserving the $W_d$ expectation. Thus these reductions
give exactly the interface of (3.10), without restricting the internals
of the original processor.

Return to three copies. The same-sign iid expansion is

$$
\Delta_3=u(A\otimes D\otimes D+D\otimes A\otimes D
                    +D\otimes D\otimes A)+u^3A\otimes A\otimes A.
\tag{3.11}
$$

The cubic term survives. The following decomposition is a linear
calculation on Hermitian operators; it does not give the processor a
choice of programs or access to a matching-sector measurement.

Terms with two $O$ factors have three placements and total contribution
to $g$ at most $6ur^2$: $\|A\|_1=2$ and $\|O\|_1=r$.
We use the standard contraction of Hermitian trace norm under a CPTP
map, followed by the norm-one test.

For each of the three placements with one $O$, the other two factors
are

$$
uw(A\otimes P+P\otimes A)+unR_n.
$$

On $P\otimes P$, the first bracket has eigenvalues $2,0,0,-2$ and
trace norm four. The spectator multiplies this bound by $r$.
Equation (3.10) bounds the second bracket by $4r$. Thus all one-$O$
terms contribute at most $12ur(w+n)=12urh$.

With no $O$ factor, first group the $P$-supported terms with the cubic:

$$
L=uw^2(A\otimes P\otimes P+P\otimes A\otimes P
                       +P\otimes P\otimes A)+u^3A\otimes A\otimes A.
$$

The three $A$ operators commute on $P^{\otimes3}$ and have joint
eigenvalues $\epsilon_1,\epsilon_2,\epsilon_3\in\{1,-1\}$.
The eigenvalue of $L$ is
$uw^2(\epsilon_1+\epsilon_2+\epsilon_3)+u^3\epsilon_1\epsilon_2\epsilon_3$.
The two all-equal words have magnitude $3uw^2+u^3$; the other six have
magnitude $uw^2-u^3\ge0$, because $u\le w$. Hence

$$
\|L\|_1=2(3uw^2+u^3)+6(uw^2-u^3)=12uw^2-4u^3.
\tag{3.12}
$$

Taking a separate triangle bound on the cubic would lose the negative
term in (3.12), including its endpoint cancellation when $u=w$.

The six terms with one $A$, one $P$ and one $Q$ group into three
placements of $R_n$ with spectator $P$. Since $\operatorname{tr}P=2$,
(3.10) bounds each group by eight, for total $24uwn$.
The three terms with one $A$ and two $Q$ factors are half the sum of
the three placements of $R_n$ with spectator $Q$: each $AQQ$ term
occurs twice in that sum. Since $\operatorname{tr}Q=2$, their total
contribution is at most $12un^2$.

Combining every group gives

$$
\begin{aligned}
g&\le6ur^2+12urh+12uw^2+24uwn+12un^2-4u^3\\
 &=6u(1-2h+2h^2)-4u^3=B_3,
\end{aligned}
\tag{3.13}
$$

where $r=1-2h$. Equation (3.3) and nonnegativity of error prove
$\max_X\epsilon_X\ge[c-B_3]_+$. This argument applies to either
actual active pair and every admissible processor, including those
that interact with data first and retain all programs adaptively.
At $u=0$ the same inequalities apply directly. The bound is uniform
over all finite round counts and finite ancillary dimensions, so
continuity gives the asserted extension to limits. QED.

## 4. Common real instruments and the exact reference norm

**definition 4.1 (Sector, membership and Bell instruments).**
Alice first pinches the data into the sectors $d_a,d_b,\{2\}$ with
their real original-coordinate projections and tells Bob the sector.
Both the target and every protocol below annihilate all cross-sector
matrix units. In sector $\{2\}$ Bob prepares output $2$ with probability
$s$ and each of the other four coordinates with probability $5n=\eta/5$;
all programs are discarded.

In a data pair $d=(j,k)$, each examined copy is tested by both parties
for membership in their prescribed local two-dimensional supports.
Each local instrument has the projector and its complement. The two
membership bits are communicated. Acceptance means both are inside;
all three other membership outcomes are failures and are retained
before the corresponding program is discarded. No matching versus
unmatched test within the accepted product is performed. The accepted
unnormalized state is

$$
\tau_v=\operatorname{diag}(w,n,n,w)
             +iv(|00\rangle\langle11|-|11\rangle\langle00|),
\qquad\operatorname{tr}\tau_v=q,
\tag{4.1}
$$

where $v=\sigma u$ for $X=\sigma X_d$ and $v=0$ on the other axis.
Its acceptance probability $q$ is label independent. These values
describe the actual branch, and are never source-dependent controls.

For a retained pair, Alice measures the data bit and her half in the
four real Bell vectors

$$
|\beta_V\rangle=(I_2\otimes V)(|00\rangle+|11\rangle)/\sqrt2.
$$

The complete correction table is

| Bell-vector matrix $V$ | Bob's correction |
| --- | --- |
| $I_2$ | $I_2$ |
| $Z_2=\operatorname{diag}(1,-1)$ | $Z_2$ |
| $X_2=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ | $R_2$ |
| $R_2=\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$ | $X_2$ |

All four outcomes are sent and corrected; every correction is real
orthogonal and independent of the source label. The actual pair
contraction, reused from C-137.1, is

$$
\mathcal T_{\tau_v}(Y)=
\begin{pmatrix}
2wY_{00}+2nY_{11}&2ivY_{01}\\
-2ivY_{10}&2nY_{00}+2wY_{11}
\end{pmatrix},\qquad
\operatorname{tr}\mathcal T_{\tau_v}(Y)=q\operatorname{tr}Y.
\tag{4.2}
$$

For completeness, the $I_2$ outcome contracts the resource entry
$(a,b),(a',b')$ with $Y_{aa'}/2$ and produces one quarter of (4.2).
The $Z_2$ outcome's off-diagonal signs cancel its correction. For $X_2$,
the swapped indices send the coherent entry to $-ivE_{10}$, and
$R_2E_{10}R_2^T=-E_{01}$ corrects this sign. For $R_2$, the Bell
vector already supplies that minus sign and $X_2$ corrects the swap.
In both cases the correction also restores the diagonal ordering.
Thus every corrected outcome is one quarter of (4.2), on
$E_{00},E_{11},E_{01},E_{10}$ separately. In particular the calculation
keeps both independent complex off-diagonal units.

The same fixed Bell instrument, when given

$$
\omega(a,b,z)=\operatorname{diag}(a,b,b,a)
                   +iz(|00\rangle\langle11|-|11\rangle\langle00|),
\tag{4.3}
$$

has stay population $2a$, partner population $2b$, and coherence
multiplier $2iz$ with its negative on the reverse unit. This follows
from the identical contraction with $w,n,v$ replaced by $a,b,z$.

**definition 4.2 (A normalized common failure action).**
Suppose a data-pair protocol has aggregate paid stay and partner weights
$\alpha,\beta$ satisfying

$$
0\le\alpha\le s,\qquad 0\le\beta\le5n,\qquad
z_0=1-\alpha-\beta>0.
\tag{4.4}
$$

In every total-failure history Alice measures her data coordinate
$\ell\in d$, sends it to Bob, and Bob prepares the distribution

$$
p_{v\mid\ell}=
\begin{cases}
(s-\alpha)/z_0,&v=\ell,\\
(5n-\beta)/z_0,&v\text{ is its partner in }d,\\
5n/z_0,&v\notin d.
\end{cases}
\tag{4.5}
$$

The probabilities are nonnegative. Their numerator sum is
$s+20n-\alpha-\beta=z_0$, so they sum to one. Success and failure
together give $s$ at the input coordinate and $5n$ at every other
coordinate. The failure action kills both pair off-diagonals.
These are fixed normalized probabilities used in every failure
history, including those with unpromised inputs; they are not divisions
by a history's actual probability. Real basis measurement, a classical
message and Bob's real diagonal preparation realize (4.5).

**definition 4.3 (The response action and its norm).**
For $0\le G\le c$ and $X=\sigma X_d$, let the response action have
the following full complex matrix-unit values:

$$
\begin{aligned}
E_{\ell\ell}&\longmapsto sE_{\ell\ell}
                          +5n\sum_{v\ne\ell}E_{vv}
                         &&(0\le\ell\le4),\\
E_{jk}&\longmapsto i\sigma G E_{jk},&
E_{kj}&\longmapsto-i\sigma G E_{kj}&& (d=(j,k)),
\end{aligned}
\tag{4.6}
$$

and let every other off-diagonal unit vanish. Its difference from the
target has exact diamond norm $c-G$, as in the response norm of
C-121.3. The following direct norm argument also fixes the reference
scope needed here. Compress any reference/input operator to the active
pair. Trace norm cannot increase under left and right multiplication
by this orthogonal projection. On the compressed block, off-diagonal
extraction is $(Y-Z_2YZ_2)/2$ and is a trace-norm contraction by the
triangle inequality and unitary invariance. Multiplication of the two
off-diagonal blocks by $i,-i$ is conjugation by
$\operatorname{diag}(i,1)$ and preserves trace norm. Tensor all these
identities with the arbitrary reference identity. The difference map
therefore has stabilized norm at most $c-G$. The balanced pure data
input $(|e_j\rangle+|e_k\rangle)/\sqrt2$ gives a Hermitian output
difference with eigenvalues $\pm(c-G)/2$, proving equality.
The complex unitary in this norm identity is a proof device, never a
processor gate. Sections 5–7 establish the response action through
actual complete instruments, independently of a Choi existence claim.

## 5. First-hit transmission with all diagonal budgets

**theorem 5.1 (A complete thinned first-hit protocol).**
For every $t,\eta\in[0,1]$ one finite real LOCC processor has the
response action (4.6) with $G_F=\min\{c,F_3\}$ and hence error
$[c-F_3]_+$ simultaneously on all four labels.

Proof. Use the data-sector instrument of Definition 4.1. In a pair
sector test copies in order until the first local pair-product
acceptance. Unused copies are discarded. Before any data Bell
measurement, Bell-use this hit with the label-independent real coin
probability

$$
L=1+r+r^2,\qquad a_F=\min\{1,5/(2L)\}.
\tag{5.1}
$$

If the coin rejects, use the total-failure action; if there is no hit,
also use that action. All membership and coin outcomes are included.
For the promised iid batch the three possible first-hit positions
contribute $(1+r+r^2)\mathcal T_{\tau_v}$ before the coin. Thus the
paid populations and active coefficient after the coin are

$$
\alpha_F=2a_FwL,\qquad\beta_F=2a_FnL,\qquad
G_F=2a_FuL=\min\{F_3,c\}.
\tag{5.2}
$$

Both diagonal budgets hold directly: $\alpha_F\le5w=s$ and
$\beta_F\le5n$. The total failure mass on the promised batch is

$$
z_F=1-a_FqL\ge r^3\ge27/125>0,
\qquad qL=1-r^3.
\tag{5.3}
$$

Consequently Definition 4.2 applies with
$(\alpha,\beta,z_0)=(\alpha_F,\beta_F,z_F)$, and fills every
target population, including the three outputs outside the data pair.
The only surviving coherence is $i\sigma G_F$ on the active pair;
on the inactive pair $v=0$ and the coefficient is zero. The singleton
and cross-sector actions were already fixed. This proves (4.6) on
all 25 complex matrix units, and Definition 4.3 gives the error.

The thinning is required for this construction. Omitting the coin
would demand $2L\le5$ from the stay budget, which fails at some allowed
noise values. In that region (5.1) reduces the paid populations and
joins the rejected hit to the specified normalized fallback. No
failure or unmatched mode is removed. Whole-algebra completeness is
proved together with the second protocol in Section 7. QED.

## 6. A distributed three-pair majority instrument

**theorem 6.1 (Real local relative-sign processing of actual hits).**
Given three accepted pair states $\tau_v^{\otimes3}$ from (4.1), the
following complete real local instrument produces, on retained pair 1,
the unnormalized state $\omega(a,b,v_P)$ of (4.3), where

$$
\begin{aligned}
a&=4w^3+12wn^2,&b&=12w^2n+4n^3,\\
v_P&=6v(w^2+n^2)-2v^3,&2a+2b&=q^3.
\end{aligned}
\tag{6.1}
$$

It uses only local real gates, complete local measurements and
classical messages. It retains a quantum pair carrying the unknown
conjugate sign.

Proof. Write $X_2,Z_2,R_2$ for the real matrices in Definition 4.1.
Retain pair 1. For each auxiliary pair $j=2,3$, Alice applies $X_2$
to her retained bit controlled by her auxiliary bit, while Bob applies
$R_2^T$ to his retained bit controlled by his auxiliary bit. They then
measure both auxiliary bits in the real $X_2$ basis and communicate
their outcomes. Let $t_j$ be the product of these two measured signs.
After both auxiliary pairs, Alice applies $Z_2$ to her retained bit
exactly when $t_2=t_3=-1$, and otherwise does nothing.

We verify this actual gate schedule using complex vectors only as
proof indices. Define

$$
|\psi_{e,\epsilon}\rangle=
 (|0,e\rangle-i\epsilon|1,1\mathbin\oplus e\rangle)/\sqrt2,
\qquad e\in\{0,1\},\quad\epsilon\in\{1,-1\},\quad
\lambda=\epsilon(-1)^e.
\tag{6.2}
$$

The spectral weights of $\tau_v$ are $w+\epsilon v$ at $e=0$ and
$n$ at $e=1$. No preparation or measurement of these vectors is used,
and neither $e$ nor $\lambda$ is a supplied record.

Consider retained indices $(e_1,\epsilon_1)$ and auxiliary indices
$(e_2,\epsilon_2)$. Write Alice's original bits as $x_1,x_2$; Bob's
are $x_1\mathbin\oplus e_1,x_2\mathbin\oplus e_2$. Since
$R_2^T|b\rangle=(-1)^b|b\mathbin\oplus1\rangle$, the retained bits
after the gates are

$$
y=x_1\mathbin\oplus x_2,\qquad
y\mathbin\oplus e_1\mathbin\oplus e_2,
$$

and the input amplitude
$(-i\epsilon_1)^{x_1}(-i\epsilon_2)^{x_2}/2$ is multiplied by
$(-1)^{(x_1\mathbin\oplus e_1)(x_2\mathbin\oplus e_2)}$.
For $x_2=0$ this becomes, up to the common factor
$(-1)^{e_1e_2}/2$, the retained amplitude
$[-i\epsilon_1(-1)^{e_2}]^y$. For $x_2=1$, the ratio to the
$x_2=0$ amplitude at the same $y$ is
$\epsilon_1\epsilon_2(-1)^{e_1+e_2}$, independent of $y$.
These two expressions verify all four amplitudes and give, up to a
global phase, the factorization

$$
|\psi_{e_1\oplus e_2,\,\epsilon_1(-1)^{e_2}}\rangle_1
\ \otimes\
\frac{|0,e_2\rangle+t_2|1,1\oplus e_2\rangle}{\sqrt2},
\qquad t_2=\lambda_1\lambda_2.
\tag{6.3}
$$

The auxiliary factor is an $X_2\otimes X_2$ eigenvector with eigenvalue
$t_2$, so the product of its measured signs is precisely $t_2$.
Both compatible individual outcomes are retained; the other outcomes
are still part of the complete projective measurement. The retained
$\lambda$ remains $\lambda_1$. Repeating with pair 3 gives
$t_3=\lambda_1\lambda_3$ and again preserves that retained value.
Applying $Z_2$ reverses its sign. The specified final correction thus
sets the retained $\lambda$ to

$$
m=\operatorname{maj}(\lambda_1,\lambda_2,\lambda_3)
 =\frac{\lambda_1+\lambda_2+\lambda_3
                  -\lambda_1\lambda_2\lambda_3}{2},
\tag{6.4}
$$

with retained parity $E=e_1\oplus e_2\oplus e_3$. The global conjugate
sign stays in this quantum pair; only relative signs have been read.

We next evaluate the unnormalized actual mixture. The one-copy total,
parity, sign and parity-times-sign moments are, respectively,

$$
\sum p=2h,\quad
\sum p(-1)^e=2(w-n),\quad
\sum p\lambda=2v,\quad
\sum p(-1)^e\lambda=2v.
\tag{6.5}
$$

Independence and (6.4) therefore give

$$
\begin{aligned}
\sum p_1p_2p_3 m&=12vh^2-4v^3,\\
\sum p_1p_2p_3(-1)^E m&=12v(w-n)^2-4v^3.
\end{aligned}
\tag{6.6}
$$

On even parity the retained $\epsilon=m$, while on odd parity it is
$-m$. The difference of the two eigenweights is twice the corresponding
imaginary coherence. Taking the sum and difference in (6.6) yields

$$
v_P=6v(w^2+n^2)-2v^3,\qquad v_Q=-12vwn.
\tag{6.7}
$$

The total even and odd masses are obtained by adding and subtracting
the cube of the parity moment from the cube of the total mass.
Dividing each by two for its two equal coordinate populations gives

$$
a=\frac{(2h)^3+[2(w-n)]^3}{4}=4w^3+12wn^2,
\quad
b=\frac{(2h)^3-[2(w-n)]^3}{4}=12w^2n+4n^3.
$$

Before a final randomization, the retained state has diagonals
$(a,b,b,a)$, even coherence $v_P$ and odd coherence
$iv_Q(|01\rangle\langle10|-|10\rangle\langle01|)$.

Use a shared fair real classical coin to select this schedule or its
mirror with the parties interchanged, including the party applying the
final $Z_2$. The actual input $\tau_v^{\otimes3}$ is invariant under
mathematical interchange of Alice and Bob. Hence the mirror's output
is the mathematical swap of the displayed output. This fixes its
diagonals and even coherence and reverses its odd coherence. Averaging
the two schedules cancels $v_Q$ exactly and gives (6.1).
This mirror is a second specified local schedule; it transfers no
quantum register and performs no physical swap across the cut.

Each controlled gate is real orthogonal on its full local two-bit
support. Each local $X_2$ measurement includes both projectors. The
conditional $Z_2$ and the mirror coin are real. All measured records
have their actions specified and are then discarded. These operations
form a complete instrument on arbitrary complex inputs; the iid
spectral calculation only evaluates it on the actual promised batch.
The output remains distributed, ready for the Bell instrument (4.2).
QED.

## 7. Majority budgets, global parameter selection and whole-algebra validity

**theorem 7.1 (A complete majority protocol in its proved budget region).**
For all $t\in[0,1]$ and $0\le\eta\le2/3$, a complete finite real LOCC
processor has response coefficient $M_3$ and error $c-M_3$.

Proof. Use Definition 4.1 and test all three copies for local
pair-product membership. If exactly one or two copies are accepted,
Bell-use the first accepted copy and discard every other program.
If all three are accepted, apply Theorem 6.1 and then Bell-use the
retained pair. If none is accepted, use Definition 4.2 with the
weights below.

On the actual independent batch, the exactly-one and exactly-two
acceptance branches contribute $3r^2\mathcal T_{\tau_v}$ and
$3qr\mathcal T_{\tau_v}$, respectively. For example their probabilities
are $3qr^2$ and $3q^2r$, while the selected state's Bell channel is
$\mathcal T_{\tau_v}/q$. Their sum is $3r\mathcal T_{\tau_v}$.
The all-accepted branch gives (6.1) as an unnormalized state of trace
$q^3$. Equation (4.3) now gives the aggregate paid weights

$$
\begin{aligned}
\alpha_M&=6wr+2a=w(6r+8w^2+24n^2),\\
\beta_M&=6nr+2b=n(6r+24w^2+8n^2),\\
\alpha_M+\beta_M&=6hr+8h^3=1-r^3.
\end{aligned}
\tag{7.1}
$$

On $v=\sigma u$, the active coefficient is $\sigma M_3$, since
$6vr+2v_P=6vr+12v(w^2+n^2)-4v^3$; at $v=0$ it vanishes.
The no-acceptance probability is $z_M=r^3>0$.

The diagonal budgets hold throughout $[0,2/3]$. Because $w\ge n$,
the coefficient multiplying $w$ in $\alpha_M$ is at most the coefficient
multiplying $n$ in $\beta_M$. The latter is

$$
6r+24w^2+8n^2=\frac{2850-60\eta+392\eta^2}{625}.
\tag{7.2}
$$

Its numerator is convex in $\eta$. On $[0,2/3]$ it is at most its
endpoint maximum, whose two values are $2850$ and $26858/9$, both
strictly less than $3125$. Thus $\alpha_M\le5w=s$ and
$\beta_M\le5n$. This argument includes $n=0$ directly, with
$\beta_M=0$, rather than dividing by $n$.
Use (4.5) with $(\alpha_M,\beta_M,r^3)$. All target populations
are then recovered and no off-diagonal failure contribution occurs.

It remains to check that the stated coefficient is below $c$ in this
region. Algebra from (2.1) gives $B_3-M_3=24uwn\ge0$.
For $c>0$, since $3/25\le h\le1/5$ here and $1-2h+2h^2$ decreases
on that interval,

$$
\frac{B_3}{c}
 =\frac65(1-2h+2h^2)-\frac{4c^2}{125}
 \le\frac{2958}{3125}<1.
\tag{7.3}
$$

Also $M_3\ge0$, directly from $u\le w$ in its defining formula.
Hence $0\le M_3<c$ when $c>0$. If $c=0$ then $M_3=0$.
The response action is (4.6) and its exact error is $c-M_3$.
QED.

**theorem 7.2 (One lawful parameter-selected processor on the whole square).**
For each known $t,\eta\in[0,1]$, choose the common target directly when
$c=0$. When $c>0$, choose Theorem 7.1 precisely if $M_3>F_3$;
otherwise choose Theorem 5.1. This gives one processor independent of
$X$, with coefficient $G=\min\{c,K_3\}$ and exact error
$[c-K_3]_+$ on each label. Every branch is CP/TP on the full complex
joint algebra.

Proof. The majority choice is always within its proved region. Indeed

$$
\begin{aligned}
M_3-F_3&=4u(w^2+n^2-4wn-u^2),\\
w^2+n^2-4wn&=\frac{25-60\eta+33\eta^2}{625}.
\end{aligned}
\tag{7.4}
$$

The numerator in the second line is convex. On $[2/3,1]$ its endpoint
values are $-1/3,-2$, so it is negative throughout. Thus $M_3>F_3$
implies $\eta<2/3$, where Theorem 7.1 applies and $M_3<c$.
In the other case Theorem 5.1 gives $\min(c,F_3)$. This proves the
coefficient and error formula. If $c=0$, measuring the original data
coordinate at Alice and communicating it to Bob, who prepares stay
probability $s$ and probability $5n$ at each other coordinate, gives
the common target exactly without using a program. No selection uses
the unknown label, sign, parity or spectral index.

For whole-algebra validity, the initial real data projections sum to
$I_5$. Every local membership test includes its complement, and every
failure record has a specified action. On accepted local supports,
bit identifications are real isometries. The majority gates extend
by identity outside their local supports to full real unitaries.
Every auxiliary measurement has both outcomes. Alice's four Bell
projectors are complete on the selected data/program pair product;
adding the 21 computational projectors outside that subspace completes
them on her full $5\times5$ register. Bob's corrections extend by
identity on his other three coordinates, followed by the fixed real
output identification. Discard has a complete computational-bra Kraus
family. Unused or rejected program halves are discarded this way.

Every coin is a finite real local preparation and measurement with
fixed nonnegative probabilities. Each fallback is Alice's complete
basis measurement, its classical message and Bob's normalized real
diagonal preparation (4.5). The singleton uses the same type of map.
These facts establish completeness on every input, without using
independence or dividing by any actual input-dependent probability.
Consequently their finite conditional compositions are real LOCC
and CP/TP even for correlated off-promise inputs. In particular this
is an actual implementation, rather than a Choi-feasible point.

Independence is used only for the evaluated weights in (5.2) and
(7.1). On the promised batch the five diagonal units have exactly
the first line of (4.6), the two active off-diagonal units have the
displayed opposite imaginary multipliers, the two inactive ones
vanish, and the sixteen cross-sector off-diagonal units vanish.
This checks all 25 complex matrix units. The resulting identities
are equalities of complex-linear maps and remain equal after tensoring
the identity of every finite complex reference. Definition 4.3 gives
the exact norm claimed. QED.

## 8. Interval width and the established equality regions

**theorem 8.1 (Qualified width of the certified interval).**
For every $t,\eta\in[0,1]$, let $\mathcal W$ denote the difference
between the upper and lower endpoints in (2.2). Then

$$
\begin{aligned}
B_3-F_3&=4u(h^2-u^2)\ge0,\\
B_3-M_3&=24uwn\ge0,\\
\mathcal W&=[c-K_3]_+-[c-B_3]_+,\\
0\le\mathcal W&\le
\min\{4u(h^2-u^2),24uwn\}.
\end{aligned}
\tag{8.1}
$$

More explicitly,

$$
\mathcal W=
\begin{cases}
0,&c\le K_3,\\
c-K_3,&K_3<c<B_3,\\
B_3-K_3,&B_3\le c.
\end{cases}
\tag{8.2}
$$

Thus the polynomial minimum in (8.1) equals the interval width when
$B_3\le c$. It is only an upper bound for that width in general.

Proof. Substitute $r=1-2h$ in (2.1) and subtract. The displayed
differences result, and $h\ge w\ge u$ makes both nonnegative.
Therefore $K_3\le B_3$ and
$B_3-K_3=\min\{B_3-F_3,B_3-M_3\}$.
The positive-part function is monotone and 1-Lipschitz, which proves
(8.1). Splitting at $c=K_3$ and $c=B_3$ proves (8.2), with consistent
values at the boundaries. This describes the certified interval;
it does not identify the location of the true optimum inside it.
QED.

**theorem 8.2 (All zero-white-noise values and sufficient exactness).**
For every $t\in[0,1]$,

$$
\boxed{E_3(t,0)=\frac{t(23+4t^2)}{125}.}
\tag{8.3}
$$

For all $t,\eta\in[0,1]$, $E_3=0$ when $c=0$. Moreover,

$$
\eta\ge\eta_F:=\frac{25\sqrt7-55}{12}
\quad\Longrightarrow\quad E_3(t,\eta)=0
\quad\text{for every }t\in[0,1].
\tag{8.4}
$$

The threshold in (8.4) is sufficient; no necessity assertion is made.

Proof. At $\eta=0$, $w=h=1/5$, $n=0$, $r=3/5$ and $u=t/5$.
Then

$$
B_3=M_3=\frac{102t-4t^3}{125},\qquad
F_3=\frac{98t}{125},\qquad
M_3-F_3=\frac{4t(1-t^2)}{125}\ge0.
\tag{8.5}
$$

The lower and upper bounds in (2.2) coincide at
$t-B_3=t(23+4t^2)/125$. The majority protocol is directly lawful:
its paid populations are $\alpha_M=98/125$, $\beta_M=0$ and its
failure mass is $27/125$. Its failure preparation stays at the
measured coordinate with probability one. Thus (8.3) includes $t=0$,
$t=1$ and zero source eigenvalues, with finite rounds and no limit.
At $t=1$ its error is $27/125$; for $0<t<1$, majority improves the
three-copy first-hit error by $4t(1-t^2)/125$.

At $c=0$ the common measure-and-prepare target in Theorem 7.2 proves
exactness. For the first-hit protocol, $G_F=c$ whenever

$$
1+r+r^2\ge5/2
\quad\Longleftrightarrow\quad
r\ge(\sqrt7-1)/2
\quad\Longleftrightarrow\quad\eta\ge\eta_F.
$$

At and above this threshold, (5.1) gives $\alpha_F=s$ and
$\beta_F=5n$. The normalized failure preparation supplies the three
other coordinates and the achieved coherence equals $c$. Its entire
channel is the target, including at the threshold. This proves (8.4)
without an assertion that these are all exactness parameters. QED.

**theorem 8.3 (An explicit positive-noise residual interval).**
If $c>0$ and $0<\eta<\eta_F$, the interval in (2.2) has strictly
positive width. In particular the bounds do not determine a general
positive-noise value or a necessary threshold for exactness. At
$t=1,\eta=1/2$ they give precisely

$$
\boxed{\frac{303}{6250}\le E_3(1,1/2)\le\frac{327}{6250},}
\qquad\mathcal W=\frac{12}{3125}.
\tag{8.6}
$$

Proof. Positive noise and $c>0$ imply $u,w,n>0$ and $h>u$.
Both coefficient differences in (8.1) are strictly positive, so
$K_3<B_3$. Below $\eta_F$, $F_3<c$. If majority is selected,
Theorem 7.1 gives $M_3<c$; if it is not selected, $K_3=F_3<c$.
Hence $K_3<c$ in every case and (8.2) gives positive width, even
where $B_3\ge c$ and the lower endpoint is zero. A zero lower endpoint
does not imply a zero optimum, and positive interval width does not
imply that the true optimum is positive.

At the stated rational point, the parameters are

$$
c=\tfrac12,\quad u=\tfrac1{10},\quad w=\tfrac3{25},\quad
n=\tfrac1{50},\quad h=\tfrac7{50},\quad r=\tfrac{18}{25}.
$$

Direct substitution in the symbolic formulas gives, in denominator
$6250$,

$$
c=\frac{3125}{6250},\quad B_3=\frac{2822}{6250},\quad
F_3=\frac{2798}{6250},\quad M_3=\frac{2786}{6250}.
$$

Thus first-hit is selected, yielding (8.6). Neither endpoint in
(8.6) has been identified as the exact optimum. The remaining
mathematical bridge would require a sharper full-class converse,
an improved actual local protocol, or an argument between them.
In particular separate saturation of terms in (3.13) would not prove
simultaneous saturation by one admissible processor. QED.

## 9. Comparison with the supplied joint and classical-record results

**theorem 9.1 (Bounded positive-noise joint/spatial separation).**
Let $e_3^{\rm joint}$ be the common unrestricted or real-joint
three-copy optimum supplied in C-130.4, with exactly the source,
target and complex reference convention of Definition 1.1. Then, for
$c>0$ and $0<\eta\le1/2$,

$$
E_3-e_3^{\rm joint}\ge
\frac{12c\eta(15+7\eta)}{3125}>0.
\tag{9.1}
$$

The comparison uses the supplied joint value at its visible scope.
It does not assert that its joint operations are original-cut LOCC.

Proof. The credited C-130.4 value is

$$
e_3^{\rm joint}=[c-D_3]_+,\qquad
D_3=\left\|\frac{\rho_+^{\otimes3}-\rho_-^{\otimes3}}2\right\|_1
    =6u(1-2w+2w^2)-4u^3.
\tag{9.2}
$$

We first evaluate its trace quantity without using a nested
general-copy formula. The two opposite sources commute, with
distinguished active eigenweights $w\pm u$ and a neutral complement
of mass $d_0=1-2w$. Decompose the tensor experiment by the number of
active factors. The one-active blocks have total norm $6ud_0^2$;
the two-active blocks have total norm $12uwd_0$, since each
$uw(A\otimes P+P\otimes A)$ has norm $4uw$; and the all-active
block has norm $12uw^2-4u^3$ by (3.12). These supports are
orthogonal, so their norms add, giving (9.2). The neutral complement
includes all unmatched modes and is not dropped.

The following specialization explains the quantitative scope of
the visibly supplied joint construction at three copies. The common
spectral outcomes are $a_+,a_-,b_+,b_-,o,\star$: the pair vectors
are $J(e_j-i\epsilon e_k)/\sqrt2$, the singleton is $Je_2$, and
$\star$ retains the entire rank-20 unmatched sector. For $X=\sigma X_a$
their probabilities are

$$
p_{a,\sigma}=(w+\sigma u,w-\sigma u,w,w,w,20n),
$$

while $p_{b,\sigma}$ interchanges the two $a$ entries with the two
$b$ entries. These follow directly from (1.1); grouping the unmatched
sector loses no trace distance because all its individual probabilities
are label independent. The resulting commuting words have signed counts
$h_d(z)=\operatorname{sgn}(n_{d+}-n_{d-})$, with ties zero, and
presence indicator $H_d(z)$ recording any outcome on pair $d$.
A present tie is distinct from absence. Put

$$
Z_0=(1-2w)^3>0,\qquad T_0=1-Z_0.
$$

Each pair has presence probability $T_0$ under every label. Swapping
the two active outcomes gives
$\mathbb E_{\sigma X_d}h_d=\sigma D_3$; swapping the inactive pair
fixes the source law and gives zero expectation there. The sign of
the opposite-word probability difference is the sign of the active
count, including $w=u$ by comparison of its nonzero supports.
The necessary first-occurrence budget follows directly here:

$$
D_3-\frac uw T_0=4u(w^2-u^2)\ge0.
\tag{9.3}
$$

For $D_3>0$, set

$$
a_0=\min\{1,c/D_3\},\quad Q_0=\max\{s,a_0\},\quad
q_0=(s-Q_0T_0)/Z_0,
\quad
q_d(z)=\begin{cases}Q_0,&H_d(z)=1,\\q_0,&H_d(z)=0.\end{cases}
\tag{9.4}
$$

If $Q_0=s$, its numerator is nonnegative immediately. If $Q_0=a_0>s$,
(9.3) and $c/s=u/w$ imply $a_0T_0\le s$. Also $Q_0\ge s$
implies $q_0\le s$. Hence
$0\le q_0\le s\le Q_0\le1$,
$a_0|h_d|\le q_d$ and $\mathbb E_Xq_d=s$.

For clarity, this is a specialization of the supplied joint protocol,
not a spatial upper bound. Its real joint sector instrument extracts
a qubit from either two-dimensional matching sector, and retains the
singleton and full unmatched outcomes. On extracted qubits use
$H=iR_2$, $P_\epsilon=(I+\epsilon H)/2$ and the real gate

$$
V=(I\otimes A_H)
  (I\otimes|0\rangle\langle0|+R_2^T\otimes|1\rangle\langle1|),
\qquad A_H=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}.
$$

It obeys
$V(H\otimes I)V^T=H\otimes I$ and
$V(I\otimes H)V^T=H\otimes Z_2$: the first follows from commutation
with $R_2$, and in the second the controlled gate sends $I\otimes H$
to $H\otimes X_2$ before $A_HX_2A_H^T=Z_2$.
Measuring the auxiliary qubit computationally therefore reads only
relative signs and retains the first sign in one qubit.
For an orbit $\{z,\bar z\}$ under global conjugation, choose the
representative whose first extracted sign is positive. The orbit
record and retained unnormalized qubit are

$$
\tau_{X,z}=\lambda_X(z)P_++\lambda_X(\bar z)P_-,
\qquad\lambda_X(z)=p_X^{\otimes3}(z).
\tag{9.5}
$$

All-neutral words retain their scalar weight without a qubit. The
joint sector tests, relative-sign gates and measurements are complete
on the full complex algebra. They are the visible C-130.1 instrument;
their use of matching sectors is not a local-test permission in
Definition 1.2.

On a data pair $d$, the supplied real joint response uses a three-way
coin of probabilities
$a_0|h_d|$, $q_d-a_0|h_d|$, $1-q_d$. The first branch couples the
data to the retained qubit by controlled $R_2$ or $R_2^T$ according
to the representative sign of $h_d$. Its coherence on an
unnormalized retained operator $\tau$ is
$ia_0h_d\operatorname{tr}(H\tau)$. The second branch measures and
keeps the data coordinate, and the third measures it and prepares
uniformly one of the other four coordinates. The mean stay weight
is $s$ and every wrong-coordinate weight is $(1-s)/4=5n$.
Summing (9.5) over orbits gives active coefficient
$a_0D_3=\min(c,D_3)$ and zero inactive coefficient. The no-pair
record uses only the last two branches with probabilities $q_0,1-q_0$;
present ties use $Q_0$ and also have zero first-branch weight.
The singleton uses the ordinary target diagonal preparation.
If $D_3=0$, then $u=c=0$ and the common target is used instead.
These complete real joint instruments give (9.2)'s upper error by
the norm identity of Definition 4.3.

Conversely every joint CPTP processor, when appended with any fixed
reference/data state, contracts the actual opposite-program difference.
Thus $\|N_+-N_-\|_\diamond\le2D_3$. The opposite targets have
distance $2c$, so the triangle inequality gives worst error at least
$[c-D_3]_+$. This verifies the relevant three-copy joint specialization
from the visible ingredients. The already supplied joint optimum,
its general-copy theorem and its literature provenance are not claimed
as new results here.

For the separation itself, $c>0$ and $\eta\le1/2$ imply
$3/25\le w\le1/5$. As in (7.3),

$$
\frac{D_3}{c}=\frac65(1-2w+2w^2)-\frac{4c^2}{125}
                 \le\frac{2958}{3125}<1.
\tag{9.6}
$$

Moreover,

$$
D_3-B_3=12un(1-2w-n)
        =\frac{12c\eta(15+7\eta)}{3125}\ge0.
\tag{9.7}
$$

Therefore both $D_3<c$ and $B_3<c$: the positive parts in the
two lower errors do not clip. Subtract the supplied joint value
$c-D_3$ from the spatial lower bound $c-B_3$ to obtain (9.1).
Strictness uses $c>0$ and $\eta>0$ in exactly the stated range.

At $t=1,\eta=1/2$, (9.2) gives $D_3=2933/6250$ and joint error
$192/6250$. Consequently (8.6) implies spatial excess at least
$111/6250$. This is a lower bound on the excess, not its exact value.
At zero white noise, $D_3=B_3=M_3$, so the spatial equality (8.3)
has the already supplied joint number. Its additional assertion is
original-cut real LOCC attainment and a converse for the entire
original real LOCC class. QED.

**theorem 9.2 (The three-copy protocols use quantum retention).**
For $c>0$, the processor in Theorem 7.2 has error strictly less than
the supplied program-first real-record, memory-free value $c$.
It therefore lies outside that smaller comparison class, although
it uses real local Kraus matrices throughout.

Proof. The comparison class in C-132.1 acts only on programs first,
retains a classical record with real effects $F_z$, and keeps no
quantum subsystem or correlation with the original program for later
data interaction. Any retained state is prepared from the record
alone. For a real effect $F_z^T=F_z$, while
$\rho_-^{\otimes3}=(\rho_+^{\otimes3})^T$. Thus

$$
\operatorname{tr}(F_z\rho_+^{\otimes3})
 =\operatorname{tr}(F_z\rho_-^{\otimes3}).
\tag{9.8}
$$

Adaptive real program-only Kraus histories have real symmetric
effects as well. Any later data channel chosen only from that record
has the same average for the opposite signs, even if complex later
channels are allowed. Their target distance is $2c$, forcing worst
error at least $c$; the common zero-program diagonal channel attains
$c$. This is the already supplied C-132.2 comparison, reused here at
three copies.

For $c>0$, $F_3=2u(1+r+r^2)>0$, so the selected coefficient
$\min(c,K_3)$ is positive. Theorem 7.2's error is consequently
strictly less than $c$. Its Bell step uses an actual retained
distributed pair; in the all-hit majority branch Theorem 6.1 keeps
the unknown global sign quantum while reading relative signs.
Equation (9.8) never applies as a memory-discarding restriction on
the full class of Definition 1.2. QED.

## 10. Mathematical suppliers and the remaining optimization

**definition 10.1 (Attribution and scope of the supplied mathematics).**
The original source, target and reference convention are reused from
[Compound communication and calibration](AURIC_FIB_ATOM_HIDDEN_RELATIONS_COMPOUND_COMMUNICATION_AND_CALIBRATION.md),
C-116 and C-121. That volume already supplies the real joint
relative-sign instrument and joint value in C-129–C-133, and the
two-copy BOTH-REAL spatial value

$$
E_2=\frac{c(45-12\eta)}{125},\qquad
e_2^{\rm joint}=\frac{c(45-16\eta)}{125},\qquad
E_2-e_2^{\rm joint}=\frac{4c\eta}{125}
$$

in C-134–C-138. Those results are prior inputs. In particular their
two-copy excess is distinct from (9.1). The finite six-vector
certificate and Bell table are credited to C-135 and C-137 and
are used as intermediate interfaces, with the necessary identities
spelled out in Sections 3 and 4. The joint value is cited there from
*FIB noisy source programming minimax*; only the visible statement
and the three-copy specialization explained in Section 9 are
consumed here. No additional assertion from an unseen nested supplier
is needed for the spatial bracket.

The Kraus/Choi criterion, Hermitian trace-norm contraction, trace
duality and diamond stabilization are standard finite-dimensional
channel tools, not new general theorems of this volume. The necessary
local-transpose Choi condition is the one attributed by C-138.2 to
Wu et al., *Communications Physics* 7, 171, Methods, Eqs. (37)–(39),
[DOI 10.1038/s42005-024-01649-y](https://doi.org/10.1038/s42005-024-01649-y).
Its sufficiency for LOCC is not assumed. The real-operation and
supplied-imbit framework is credited in C-133.2 to Wu et al. (2021)
and Wu et al. (2024), arXiv:2301.04782v1, Appendix A, (22)–(23).
A supplied imbit is a different premise from the actual mixed
programs here. These bibliographic attributions retain the visible
supplier's scope; no independent authentication of the primary
articles or nested literature is asserted.

The additional three-copy bracket, retained cubic converse,
distributed majority gate, thinning and population selection, and
their stated consequences are repo-derived ordinary finite-dimensional
mathematics. They are not a claim of worldwide priority or a new
generic norm, Choi, teleportation or resource-theory theorem.

**definition 10.2 (The unresolved positive-noise problem).**
The optimization remains (1.3), with all its original competitors
and all $t,\eta\in[0,1]$. Outside the established equality regions,
the results here specify only the interval (2.2). For $c>0$ and
$0<\eta<\eta_F$, its positive width is proved in Theorem 8.3.
Before positive-part clipping, the explicit majority coefficient
misses the converse coefficient by $24uwn$, while first-hit misses
it by $4u(h^2-u^2)$. Neither loss is proved unavoidable for arbitrary
adaptive real LOCC. Feasibility for a transpose-invariant Choi
relaxation or equality of separately bounded groups is not an actual
local implementation. The necessary exactness threshold and the
general positive-noise optimum therefore remain unresolved here,
including the rational case (8.6).

All channel identities concern one use with the actual initial
independent batch and exact stated controls. They supply neither
native preparation of that batch, exact physical calibration from
a finite code name, nor a physical-efficiency or acquisition-cost
bound. Reuse of classical settings is permitted; reuse of the same
three quantum copies does not establish independent channel uses.
Approximate sources or controls require their own error analysis.
These are ordinary mathematical proofs, with no formal or kernel
certification asserted.

## 追加锚（本行以下为增补区）
