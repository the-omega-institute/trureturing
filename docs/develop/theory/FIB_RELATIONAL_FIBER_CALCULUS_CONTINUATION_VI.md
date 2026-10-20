# FIB Relational Fiber Calculus · Continuation VI
## —Task-compatible memory and finite closed-loop certificates

> **Machine contract.** This is a generic-v1 theory reference volume. The
> definitions and results below are ordinary mathematical prose, not Lean
> declarations. They make no kernel-verification claim.

Continuation V requires a summary to factor legality, responses, successors,
resources, and controller updates. This continuation isolates the task layer
that remains after those requirements have been stated. A summary can preserve
the current target candidates and still erase the distinction needed to choose
the next action. The correct object is therefore a family of jointly
controllable history sets, followed by a finite controller and a termination
certificate.

## 60. Task-compatible history fibers

### Definition 60.1 (finite target-state contract)

Let \(Z\), \(S\), and \(O\) be finite target, complete device-state, and
response sets. An admissible action \(a\) has a domain \(D_a\subseteq S\), a
response map

$$
r_a:D_a\longrightarrow O,
$$

and a successor map \(T_a:D_a\longrightarrow S\). A nonempty candidate
relation is a set \(B\subseteq Z\times S\). An action is jointly legal on \(B\)
when every \((z,s)\in B\) has \(s\in D_a\). After response \(r\), define

$$
B_{a,r}=\{(z,T_a(s)):(z,s)\in B,\ r_a(s)=r\}.
$$

Empty responses are discarded. All fields that affect a later response,
permission, cost, or stop condition belong to \(S\); their inclusion in the
mathematical state does not grant the controller access to them.

### Definition 60.2 (finite acquisition layers)

Let \(\mathfrak B\) be the nonempty subsets of \(Z\times S\). Define

$$
\mathcal W_0=\{B\in\mathfrak B:|\operatorname{pr}_Z B|=1\},
$$

and recursively

$$
\mathcal W_{n+1}=\mathcal W_n\cup
\left\{B:
\begin{array}{l}
\text{some action is jointly legal on }B,\\
\text{and every nonempty }B_{a,r}\text{ belongs to }\mathcal W_n
\end{array}
\right\}.
$$

Write \(\mathcal W_{\mathrm{fin}}=\bigcup_n\mathcal W_n\).

### Theorem 60.3 (the least finite acquisition fixed point)

For every \(n\), \(B\in\mathcal W_n\) if and only if there is a deterministic
protocol that is correct on \(B\) and uses at most \(n\) actions in the worst
case. Consequently \(\mathcal W_{\mathrm{fin}}\) is the least set containing
\(\mathcal W_0\) and closed under the displayed action/all-response rule.

**Proof.** Induct on \(n\). At \(n=0\), a protocol can stop correctly exactly
when all candidates have the same target. Suppose the statement holds at \(n\).
For a newly admitted \(B\), choose the action in the definition. Every possible
nonempty response leaves a member of \(\mathcal W_n\), so attach the induction
protocol for that response. The converse follows by inspecting the first
action of any protocol of depth at most \(n+1\). The least-fixed-point claim is
the same induction expressed as closure. \(\square\)

### Definition 60.4 (control-compatible history family)

Let \(I\) be a finite set of already acquired history classes, with candidate
relations \(B_i\subseteq Z\times S\). For a budget \(n\), put

$$
\mathcal K_n=
\left\{J\subseteq I:
J=\varnothing\text{ or }\bigcup_{i\in J}B_i\in\mathcal W_n\right\}.
$$

An element of \(\mathcal K_n\) is a set of histories that may be forgotten
inside one memory value while retaining a common protocol of budget \(n\).

### Theorem 60.5 (memory fibers and the noncommuting quantifiers)

For a memory map \(m:I\to M\), the memory is safe for budget \(n\) exactly when

$$
\forall u\in m(I),\qquad
\bigcup_{i:m(i)=u}B_i\in\mathcal W_n.
$$

Moreover, \(\mathcal K_n\) is downward closed and

$$
\mathcal K_n\subseteq\mathcal K_{n+1}.
$$

It need not be closed under unions.

**Proof.** After the memory value \(u\) is retained, every history in its
fiber remains possible, so the correct current candidate relation is their
union. The same continuation must work for the union, proving necessity. If
the union belongs to \(\mathcal W_n\), choose its protocol, proving
sufficiency. Restricting a successful protocol to a smaller candidate set
preserves success, and allowing more actions preserves an old protocol. The
union statement is false in the example below. \(\square\)

Thus the relevant quantifiers are

$$
\forall i\ \exists\pi_i
\quad\text{versus}\quad
\exists\pi\ \forall i.
$$

The first does not imply the second. A task-compatible memory is therefore a
cover by members of \(\mathcal K_n\), not generally an equivalence quotient.

### Definition 60.6 (history-label number)

Assume each \(B_i\) is individually in \(\mathcal W_n\). Define

$$
\kappa_n^{\mathrm{hist}}
  =\min\left\{|{\mathcal P}|:
    {\mathcal P}\text{ is a partition of }I,\
    P\in\mathcal K_n\text{ for every }P\in{\mathcal P}\right\}.
$$

This is a static label count. It does not count an action phase, an output
register, or the memory needed to update a label after a response.

### Theorem 60.7 (static labels are only a controller lower bound)

If a deterministic finite controller has \(K\) states and succeeds within
budget \(n\), then

$$
\kappa_n^{\mathrm{hist}}\le K.
$$

The inequality can be strict.

**Proof.** Partition \(I\) by the controller's initial state. Histories in one
block use the same continuation, so their candidate-relation union lies in
\(\mathcal W_n\) by Theorem 60.5. The number of blocks is at most \(K\). The
strict example is given in Theorem 61.3. \(\square\)

## 61. A three-history obstruction

### Definition 61.1 (destructive calibrated reader)

The initial source is \((i,z)\) with \(i\in\{1,2,3\}\) and \(z\in\{0,1\}\). The
target is \(z\). The three actions have responses

| calibration class | \(a\) | \(b\) | \(c\) |
|---|---:|---:|---:|
| \(i=1\) | \(z\) | \(z\) | \(\star\) |
| \(i=2\) | \(\star\) | \(z\) | \(z\) |
| \(i=3\) | \(z\) | \(\star\) | \(z\) |

\(\star\) is independent of \(z\). Every action sends the reader to the same
terminal state \(s_\dagger\); later responses contain only \(\star\). Let

$$
B_i=\{(0,s_{i,0}),(1,s_{i,1})\}.
$$

The class labels may themselves be represented by any three distinct legal FIB
words. The example distinguishes retaining a history label from erasing it:
when a label is retained, the initialization map \(c\) may use that label;
when all three labels are erased, the initial candidate relation is their
union and \(c\) must be constant on the erased fiber.

For any nonempty candidate relation, write

$$
D(B)=\min\{n\in\mathbb N:B\in\mathcal W_n\},
$$

with \(D(B)=+\infty\) when the set on the right is empty.

### Theorem 61.2 (pairwise controllability without joint controllability)

For each \(i\), \(D(B_i)=1\), and every pair is one-step controllable:

$$
D(B_1\cup B_2)=D(B_1\cup B_3)=D(B_2\cup B_3)=1.
$$

But

$$
D(B_1\cup B_2\cup B_3)=+\infty.
$$

**Proof.** Use \(b\) on \(B_1\cup B_2\), \(a\) on \(B_1\cup B_3\), and \(c\) on
\(B_2\cup B_3\). The response is \(z\), so one action suffices and zero
actions cannot suffice because both targets remain possible.

For all three classes, any first action has a class on which it returns
\(\star\). That branch leaves both \((0,s_\dagger)\) and
\((1,s_\dagger)\), with identical future responses. No later protocol can
recover \(z\). \(\square\)

### Theorem 61.3 (two labels but four controller states)

For the reader in Definition 61.1, assuming the retained history class is
available to the initialization map \(c\), and any \(n\ge1\),

$$
\kappa_n^{\mathrm{hist}}=2,
\qquad K_{\min}(n)=4.
$$

There is no unique coarsest safe partition of the three histories.

**Proof.** One label would merge all three classes and is impossible by Theorem
61.2. Two labels suffice, for example
\(\{1,2\}\mid\{3\}\), so \(\kappa_n^{\mathrm{hist}}=2\). The partition
\(\{1,3\}\mid\{2\}\) is also safe. Any partition coarser than both merges all
three classes and is unsafe, so no common coarsest safe partition exists.

For the upper bound, use running states \(k_b,k_a\), with the retained initial
classes
\(\{1,2\}\) and \(\{3\}\) sent to them. Execute \(b\) or \(a\), respectively;
response \(0\) enters a halt state \(h_0\), and response \(1\) enters \(h_1\).
This is a four-state controller.

For the lower bound, at least two distinct halt states are needed for the two
possible outputs. No initial source can be a halt state because its target is
unknown. No single running state can serve all three classes, since every one
of \(a,b,c\) returns \(\star\) on one class. Thus at least two running states
are required, giving \(K\ge4\). \(\square\)

### Corollary 61.4 (FIB register cost)

If controller states receive independent fixed-length legal FIB names with no
adjacent \(11\), then four states require length three:

$$
F_{\ell+2}\ge4
\quad\Longleftrightarrow\quad
\ell\ge3.
$$

The names \(000,010,100,101\) realize the four states. This is a static state
capacity statement; rewriting a register, maintaining a program counter, and
paying the physical action cost remain separate contracts.

## 62. Closed-loop certificates

### Definition 62.1 (controller support and rank)

Fix finite sets \(I,Z,S,K,A,O\), initial candidate relations
\(B_i\subseteq Z\times S\), and a deterministic controller with initialization
\(c:I\to K\), action/output map

$$
u:K\longrightarrow A\sqcup\operatorname{Halt}(Z),
$$

and response update \(v:K\times O\to K\). If \(u(k)=a\in A\), \(k\) is a
running state; if \(u(k)=\operatorname{Halt}(\widehat z)\), it is a halt state.
A support \(C_k\subseteq Z\times S\) records the candidates compatible with
controller state \(k\). A rank is a map

$$
\rho:\{(z,s,k):(z,s)\in C_k\}\longrightarrow\mathbb N.
$$

### Theorem 62.2 (sound and complete finite closed-loop certificate)

Suppose \(B_i\subseteq C_{c(i)}\) for every \(i\in I\). Whenever
\(u(k)=a\in A\), the action is jointly legal on \(C_k\), every response
successor lies in the support selected by \(v\), and every non-halt successor
satisfies

$$
\rho(z,T_a(s),v(k,r_a(s)))<\rho(z,s,k).
$$

For every halt state \(k\), with \(u(k)=\operatorname{Halt}(\widehat z)\), every
\((z,s)\in C_k\)
satisfies

$$
z=\widehat z.
$$

Then the controller is legal, terminates, and returns the target correctly.
Conversely, for a finite
deterministic controller that succeeds and terminates on all allowed sources,
reachable supports and remaining execution lengths supply such \(C_k\) and
\(\rho\).

**Proof.** The support conditions give induction along every actual response
history. The rank cannot decrease indefinitely in \(\mathbb N\), so execution
terminates. The halt condition gives correctness. Conversely, take
the exact reachable support at each controller state and define the rank to be
the maximum remaining number of actions. Termination excludes a reachable
non-halt cycle, so this rank strictly decreases. \(\square\)

This is the execution layer missing from a static observation quotient. A
mathematical hidden coordinate may occur in \(C_k\) and \(\rho\) without being
an input available to the controller.

## 63. Relation to current FIB boundaries

There are two distinct uses of a retained summary. A **full-behavior
predictive quotient** requires, for every permitted action (including silent,
illegal, and undefined outcomes), summary-factorized legality, response,
successor, status, resource labels, stop behavior, and source-independent
memory update. This is the all-action factorization contract of
[Continuation IV](FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_IV.md), not a
controller synthesis result. A **task-specific controller certificate** is
relative to one chosen action at each reachable support: it requires only
joint legality there, response-indexed successor closure, the target equality
at halt, and a decreasing rank. Unchosen actions need not descend through the
summary, and a task certificate does not establish a universal behavioral
quotient.

The dynamic summary conditions in [Continuation V](FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_V.md)
remain necessary for the first contract. The present results add the task
condition for the second contract: one retained memory value must support a
common protocol for the union of all histories in that memory fiber.

The actual-word results on dev show the same boundary in another form. A
tree endpoint may have two parity lifts, so a vertex-only summary is adequate
only for vertex-valued targets. Adding parity uses two static supplement labels
when the endpoint is already available, but does not provide acquisition,
noise robustness, or a finite live controller. The affine calibration results
give the continuous analogue: two nonparallel normals can remain in one
control-stable complete-record fiber and force infinite risk.

These comparisons do not identify the actual-word source with the legal FIB
word language, nor do they turn metric or set-theoretic estimates into finite
acquisition. A typed source map preserving domains, responses, updates,
permissions, targets, and costs is still required.

## 追加锚（本行以下为增补区）

## 64. The exact \(p_J\) acquired-\(M\) child as an action-labelled support

Let \(\mathscr W_{H_4}^{\mathrm{comp}}\) denote the complete-world domain of
the common-parent source at the fixed parent \(H_4\). Here \(H_4\) is the
parent object, \(p_J\) is the exact algebraic parameter inherited from
Theorem 8.1, and \(u_M(W)\) is the sixth-\(M\) response function. For a
scalar response \(v\), put

$$
\mathcal C_v=\{W\in\mathscr W_{H_4}^{\mathrm{comp}}:
                 p(W)=p_J,\ u_M(W)=v\}.
$$

Thus \(v\) is a candidate sixth-\(M\) response label here; this definition
does not by itself assert that a live reader has acquired it. The complete
worlds and terminal maps are taken from
[FIB common-parent geometry, §§18--23](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md);
the source notation \(\mathcal F(H_4,M,p_J,M,v)\) is the same set.

For the two terminal actions \(a_J,a_M\), define the pre-contract
action/response relation

$$
\mathcal R_v\subseteq\{J,M\}\times
    \mathscr W_{H_4}^{\mathrm{comp}}\times\mathbb R
$$

by

$$
\mathcal R_v
 =\{(F,W,y):W\in\mathcal C_v,\ F\in\{J,M\},\ y=f_{MF}(W)\},
$$

where \(f_{MJ}\) and \(f_{MM}\) are respectively the final-\(J\) and final-\(M\)
response functions, \(f_{MF}=f_{MJ}\) for \(F=J\), and
\(f_{MF}=f_{MM}\) for \(F=M\). The guard \(L_1\) is the recursive guard from
the same source, not an additional response coordinate. The action \(a_F\)
carries response \(y\). This relation is not yet a
candidate relation \(B\subseteq Z\times S\) of Definition 60.1: it has no
declared target/state encoding. It supplies neither a successor map, an
action domain, a permission contract, nor a live acquisition step; those
fields must be added before this source-specific relation can enter
Definition 60.1 or Theorem 62.2.

The source-specific results give two exact boundaries. First, at the response
\(v_\star\) of Theorem 18.2, with the response enclosure and terminal
separation supplied by Theorem 19.1, Theorem 23.1 states

$$
\mathcal C_{v_\star}=\{A,B,C,D\},
\qquad f_{MJ}(A)=f_{MJ}(B),
\qquad f_{MM}\ \text{is injective on }\mathcal C_{v_\star},
$$

and hence \(\neg L_1(S,(H_4,M,p_J,M,v_\star))\) for every support \(S\) in
this child. The final-\(J\) pair is real, while no final-\(M\) collision pair
exists in this exact four-world support.

The current `dev` geometry also supplies an exact off-\(24\) collision in
the full complete-world domain: two distinct regular worlds realize the same
three-response tuple \((p_\ast,u_\ast,m_\ast)\), with
\(p_\ast\in(2,3)\) and unequal analytical ratios. This is a rational
contraction certificate for the response map, not a \(p_J\) result. The
analytical ratio is only a separating coordinate in that construction; it is
not an acquired response. Consequently, any global claim that collisions are
confined to the \(p=24\) mirror sector is false, while the exact-\(p_J\) joint
witness question is resolved below by global branch injectivity.

Second, Theorem 31.1 gives a finite necessary response reduction. If one
child contains both a distinct final-\(J\) collision pair and a distinct
final-\(M\) collision pair, then

$$
Q(p_J,v)=0\quad\text{or}\quad v=s_-(p_J)\quad\text{or}\quad v=s_+(p_J),
$$

so at most \(74937\) scalar responses can support that joint collision
pattern. This is a response/action-support restriction, not an acquisition
protocol and not a finite-controller construction.

The newer all-response geometry closes the exact-\(p_J\) witness question
that this finite reduction left open. Its global two-branch parametrization,
opposite-branch order, lower-branch order, and upper-branch joint-response
injectivity imply

$$
f_{MM}\!\restriction_{\mathcal C_v}\ \text{is injective}
\qquad\text{for every }v\in\mathbb R,
$$

where \(\mathcal C_v=\mathcal F(H_4,M,p_J,M,v)\). Consequently no exact
acquired-\(M\) child contains a distinct terminal-\(M\) collision pair, and
the unchanged same-child predicate requiring both a terminal-\(J\) pair and a
terminal-\(M\) pair is false. The earlier \(74937\)-response reduction is
still a valid necessary sieve, but it is no longer an open existence test at
\(p_J\). The theorem does not decide other fifth responses, ancestor
conditions, or arbitrary adaptive readers.

## 65. Response-collision strata and promotion to an executable obstruction

For the complete-world domain of the common-parent source, let

$$
\Psi_{M^3}(W)=(p(W),u_M(W),m_M(W))
$$

denote the three actual responses of the fixed \((M,M,M)\) continuation, and
put

$$
\Sigma_{\mathrm{resp}}
 =\{y:\exists W\ne W',\ \Psi_{M^3}(W)=\Psi_{M^3}(W')=y\}.
$$

The off-\(24\) construction now proves that
\(\Sigma_{\mathrm{resp}}\) contains a point with
\(p\in(2,3)\) and two worlds having unequal analytical ratios. The exact
\(p_J\) joint-witness set is a different stratum: Theorem 31.1 bounds only
the responses that can support both a final-\(J\) collision and a final-\(M\)
collision in one child at that fixed \(p_J\). The newer global branch argument
then excludes the final-\(M\) pair for every such child. Consequently,

$$
\Sigma_{\mathrm{resp}}\ne\varnothing
\quad\not\Rightarrow\quad
\text{a witness of (32.1) exists at }p_J.
$$

Nor does a response collision alone prove failure of finite recovery. To use
Theorem 15.4, a source-specific contract must still embed the two worlds as

$$
(g(W),s),\qquad(g(W'),s),\qquad g(W)\ne g(W'),
$$

with the same complete post-observation state \(s\), and prove that every
permitted continuation depends only on that state. If a later permitted action
has a different successor or response on the two worlds, the present
collision is only an observation-fiber collision and may be recoverable.
The exact-\(p_J\) geometry now supplies the exclusion side of this test for
the terminal-\(M\) pair, while the off-\(24\) collision remains a separate
response stratum. Acquisition, permission, successor, and finite-controller
data are still required before either stratum becomes an executable
obstruction or protocol.

## 66. Behaviour kernels and chronology fibres from the latest dev boundary

The current native joint-state result supplies a concrete instance of the
task-relative quotient used above. On its authentic finite-history domain,
the current-continuation kernel, the complete raw-state kernel, the extracted
key kernel, and the partial-time kernel coincide:

$$
z\equiv_{\mathrm{now}}w
\iff
\mathcal K(z)=\mathcal K(w)
\iff
X^+(z)=X^+(w)
\iff
T_{\mathrm{cut}}(z)=T_{\mathrm{cut}}(w).
$$

This is a behaviour quotient: equal representatives have the same legal
trials, responses, guards, charges, successors, and finite future experiment
trees. It is not an exact-history quotient. For a captured key, write

$$
p=n-\kappa,\qquad q=m-1.
$$

The same current state has exactly

$$
L(\mathcal K)=\binom{p+q}{p}
$$

lawful owner-order chronologies. If \(p,q>0\), this number is greater than
one, so no function of the current raw state alone can recover the executed
total chronology. The post-capture cross-owner order is therefore
chronology-only memory for the continuation task, while the capture frontier
\(\kappa\) remains behaviour-bearing memory.

The distinction is operational. Two histories obtained from the same Armed cut can have the same visible
input and row counts but different capture ranks; a later lawful acquisition
and public return separates them. Dropping the captured read boundary
therefore breaks a future-use task even when it preserves the present target
candidate set. Conversely, retaining the owner chains and the capture bracket
is sufficient for the stated partial-time task on the authentic image; it does
not install a universal chronology logger or a decoder for fabricated keys.

## 67. Joint recovery is not the sum of local fibre optima

The latest finite quantum application gives a complementary composition
result. For its fixed six-record horizon-three partition, arbitrary
system-only terminal channels have exact error

$$
\varepsilon_{\mathcal P}
 =\frac{793-88\sqrt{13}}{1508},
$$

which is strictly below the mass-weighted sum \(11/32\) of the two separate
binary optima. A common input and projector certify the lower bound while a
single balanced family of channels attains it. The improvement comes from a
joint witness, not from adding independently optimal recordwise decoders.

The same fixed partition has a legal peak-six online realization at horizon
three. The latest finite recovery continuation now extends this comparison to
all complete six-cell partitions and independent seed mixtures: under its
declared encoded-qutrit, system-only, horizon-three contract, the global
peak-six optimum is the exact value \(E^*\) stated in Section 70. Thus the
finite horizon-three threshold is global over the allowed partitions and
controllers, although it does not determine the unbounded joint memory law,
physical register cost or arbitrary horizons. In particular, six terminal
cells and eight raw histories both still require three bits under a
fixed-length binary register, but that bit count does not determine the
diamond-error threshold.

These results sharpen the promotion rule of Section 65:

$$
\text{response collision}
\;\to\;
\text{acquired continuation collision}
\;\to\;
\text{finite-controller obstruction}
$$

are three different claims. The first is now witnessed off \(24\); the second
requires typed acquisition and successor data; the third additionally needs a
finite-history or trap argument. None follows from the preceding one by
relabeling the response.

## 68. Actual-word pair energy improves the recovery boundary without closing it

The latest actual-word geometry supplies a joint, same-law estimate for the
collision mass \(E_n(r)\), where the pair is drawn from the same fair ordered
FIB word process. Put

$$
\kappa=1-\gamma/2,
\qquad
\widehat\xi=-\log\kappa,
\qquad
R_L=\kappa^{2\lfloor(L-1)/2\rfloor}
\quad(L\ge1),
$$

with \(R_0=1\). For \(0\le m\le n\), \(0<r\le1/4\), and the strict actual-word
separation condition \(4r<\Delta_m\), the supplied estimate is

$$
E_n(r)
\le16\bigl(r^3+2^{-m}R_{n-m}\bigr).
$$

The two terms have different meanings. The \(r^3\) term is local volume, while
\(2^{-m}R_{n-m}\) is the remaining same-history mass after a real prefix of
length \(m\). The estimate uses one joint ordered process, so it cannot be
replaced by combining two separately attainable projection bounds.

The mechanism behind the improvement is chronological and algebraic. The
actual forward operator has the exact factorization

$$
P^L=U^LQ_{L-1}\cdots Q_1Q_0,
$$

and the spectral-gap estimate controls every three-projection block
\(Q_{j+2}Q_{j+1}Q_j\) on the componentwise-zero subspace by
\(\kappa=1-\gamma/2\). Consecutive blocks share their endpoint projection;
the identity \(Q_{2j}^2=Q_{2j}\) therefore joins them in the actual time order.
This gives \(\lfloor(L-1)/2\rfloor\) effective contractions from \(L\) actual
letters, rather than a product of independently selected left and right
bounds. The shared endpoint is the precise reason the estimate is a statement
about one realizable history law.

For radii \(r_n=\exp(-an+o(n))\), this yields the lower exponent

$$
\widehat b(a)=
\begin{cases}
\min\{3a,\ a+\widehat\xi(1-a/\log2)\},&0<a<\log2,\\
\log2,&a\ge\log2.
\end{cases}
$$

It strictly improves the previous full-envelope exponent on its former
unmatched interval, while the target exponent \(\min\{3a,\log2\}\) is matched
only on the enlarged range \(0<a\le\widehat a\) and \(a\ge\log2\) when
\(\gamma<1\), where

$$
\widehat a=\frac{\widehat\xi}{2+\widehat\xi/\log2}.
$$

The newest finite \(S^3\) calculation in the actual-word volume gives a
nonzero mean-zero test vector with Rayleigh quotient \(3/8\). Hence the
already supplied positivity of the same spectral-gap constant now has the
additional certified direction

$$
0<\gamma=\gamma_{22}\le\frac38<1,
\qquad
\kappa\ge\frac{13}{16},
\qquad
\widehat\xi\le\log\frac{16}{13}.
$$

Consequently the universally justified matching threshold is bounded by

$$
\widehat a\le
a_*:=
\frac{\log(16/13)}{2+\log(16/13)/\log2}
\approx0.09029525.
$$

This changes the status of the former \(\gamma=1\) branch: it is incompatible
with the new finite test vector, so it must no longer be presented as a live
route to closing the full exponent. The interval \(a_*<a<\log2\) remains a
gap in the present envelope, but the gap is unresolved rather than a
counterexample to the target.

The remaining interval \(\widehat a<a<\log2\) is still open. Consequently,
the all-\(a,c\) critical pair-energy statement,
the sharp finite-\(n,\varepsilon\) law, and the global minimum controller-memory
law remain open.

This result changes the quantitative boundary of the FIB programme without
changing the logical promotion rule of Section 65. A better joint collision
bound can improve a recovery rate; it does not by itself provide an acquired
response collision, a common post-observation state, or a finite-controller
obstruction. Geometry, acquisition, and control remain separate fibres of the
same analysis.

## 69. Spent-trigger fibres and paid promotion to an executable controller

The latest LAB continuation supplies an actual-image instance of the
task-compatible memory problem. It is useful because the hidden distinction is
not an arbitrary bit appended to a source: it is the order of two already
consumed growth triggers in one legal history. The source, selected word and
service rights are shared; only the selector state may differ.

Let \(\mathcal H(t)\) be the complete set of legal successful-event words for
one attained source \(t\), and let \(\nu\) be the selected word produced by the
two-state selector \(F_n\). For the left-trigger subword \(\nu_L\) and the set
of sufficiently deep right events \(H_R^n(t)\), the actual-history fibre is

$$
\Phi_n(t,\nu)=
\begin{cases}
\{1\},&\nu_L\ne\varepsilon,\\
\{0\},&\nu_L=\varepsilon\text{ and }\operatorname{set}(\nu)\ne H_R^n(t),\\
\{0,1\},&\nu_L=\varepsilon\text{ and }\operatorname{set}(\nu)=H_R^n(t).
\end{cases}
$$

This formula is quantified over the actual image of one initialized service.
It does not treat an arbitrary source, seed or record tuple as a legal witness.
The last case is a genuine history fibre: two different trigger orders produce
the same current source and the same nonempty selected word, while leaving
different selector controls.

The two controls cannot be merged merely because their present source and
record agree. They are persistently future-distinguishable. After both
triggers are spent, split a deepest \(\beta\)-leaf down to depth at least \(n\).
The high-control run selects the new event and the low-control run does not;
FetchSelected or NextSelected then returns different complete replies and
successors. Thus this is a behaviour-fibre obstruction in the sense of
Sections 60--62, not only a forgotten-history distinction.

The four-state absorbing latch in the same LAB continuation makes a second
boundary explicit. A selected-word observation can itself be coarser than the
control state: on the empty selected-word stratum, two absorbing states have
the same current word but different future replies. Conversely, the two-state
selector and the latch can produce different selected-word observations on the
same source-history family. Therefore “the selected record” is not a universal
substitute for the controller state; the observation contract must name the
selector and its update law.

The ambiguity also has an exact same-run acquisition cost. Let \(D\) be the
greatest current logical leaf depth and set

$$
g=\max\{1,n-D+1\}.
$$

After the paid stationary prepass, every deterministic finite-return requester
that must return a self-sufficient predictor for both controls satisfies

$$
G_{\mathrm{inc}}\ge g,\qquad R_{\mathrm{inc}}\ge g+1,
$$

where \(G_{\mathrm{inc}}\) counts successful growth events and
\(R_{\mathrm{inc}}\) counts all completed requests. The bound is attained by
splitting a deepest \(\beta\)-leaf \(g\) times and then fetching the next
selected record. The first \(g-1\) growths have identical complete replies in
both runs; the final growth creates the first new selected discrepancy, and the
extra fetch exposes it. This is a coupled-transcript lower bound and an
actual same-run upper bound, not a static information-count estimate.

Consequently the abstract acquisition layers acquire a concrete promotion
map:

$$
\text{actual history fibre}
\xrightarrow[\text{paid probes}]{(g,g+1)}
\text{identified control}
\xrightarrow{\text{ranked predictor}}
\text{finite closed-loop continuation}.
$$

The returned description remains task-relative. It predicts and executes
future requests from the reached source, selected word, public selector code
and live rights; it does not restore the old cut, install a reset or recover
the complete unselected chronology. In particular, making the residual
control known is a homing operation, not a solution of the old static equality
problem. This supplies the missing acquisition and permission data required
before a response collision can be promoted to an executable obstruction or
protocol.

The result sharpens the controller hierarchy of this volume:

$$
\begin{aligned}
\text{semantic fibre}&:\text{ which histories share the current record},\\
\text{behaviour fibre}&:\text{ which histories share every legal future},\\
\text{task fibre}&:\text{ which histories admit one common protocol},\\
\text{execution certificate}&:\text{ which protocol has legal updates and a decreasing rank}.
\end{aligned}
$$

The LAB theorem closes the acquisition-to-execution bridge for its declared
actual-image contract. It does not establish a universal finite controller,
state-minimality, total-cost optimality, unknown-seed acquisition or recovery
of all unselected chronology.

## 70. Exact finite horizon-three memory threshold

The newest approximate-online recovery volume closes a different part of the
controller problem: a finite, fully specified quantum contract with an encoded
qutrit input, three acquired labels, peak classical width at most six,
system-only terminal CPTP decoders, an input-independent shared seed, and no
intermediate quantum feedback or reference access. Let \(W_3(\varepsilon)\)
denote the least peak width if it exists under that contract. Put

$$
\tau=\frac{3\sqrt3}{8},\qquad
c=\frac{\sqrt{13}}4,\qquad
r=\sqrt{1+\tau},
$$

$$
E^*
=1-\left[
\frac{r-c}{r-1+\sqrt2(1-c)}
\right]^2.
$$

The complete partition reduction, common tester and matching online channel
give

$$
\varepsilon_{\mathrm{op}}(6,3)=E^*,
$$

and, in the stated range \(0<\varepsilon<1/4\),

$$
\varepsilon\ge E^*
\Longleftrightarrow
W_3(\varepsilon)\le6,
\qquad
0<\varepsilon<E^*
\Longrightarrow
W_3(\varepsilon)\ge7.
$$

This is a global finite result: the lower certificate covers all 266 complete
partitions after convexifying independent seed programs, while the upper
certificate is an actually legal online protocol. It therefore upgrades the
fixed-partition witness of Section 67 to a statement about the entire
declared peak-six controller class. The proof also shows why terminal alphabet
size alone is insufficient: online feasibility depends on the complete
prefix transition layers and on the joint Choi geometry of all collision
cells.

The threshold is task- and contract-relative. It does not determine the full
width curve \(W_3\), any horizon-uniform \(W_n\) law, the critical pair-energy
limit, physical implementation cost, or Lean/kernel certification. It also
does not turn an averaged-channel optimum into a single seed that succeeds on
every history. The finite result belongs after the acquisition and
branch-complete conditions above; it cannot be used as a universal memory
bound for other FIB contracts.

## 71. Finite geometric fibres and the promotion boundary

The newest common-parent geometry gives a sharper separation between a finite
semantic fibre and an executable observation protocol. Write

$$
\mathcal F_{p,v}=\mathcal F(H_4,M,p,M,v),\qquad
\mathcal F^{\mathrm{reg}}_{p,v}
 =\{W\in\mathcal F_{p,v}:\Lambda(W)\ne0\}.
$$

For every real \(p\) in the certified interval \(\mathcal P\), and every
real \(v\), the all-response elimination gives

$$
|\mathcal F_{p,v}|\le49,
\qquad
|\mathcal F^{\mathrm{reg}}_{p,v}|\le18.
$$

The first number comes from the nonzero resultant and affine Bézout after the
zero-safe singular lift is included. The second allocates the fixed
resultant multiplicity with the exceptional base factors removed. At the
original exact \(p_J\), the distinct regular terminal \(M\) collision locus
is also globally finite:

$$
|\mathcal T_M^{\mathrm{ord}}|\le4802,
\qquad
|\mathcal T_M^{\mathrm{un}}|\le2401,
$$

where the pairs range over all real acquired responses. These are bounds on
the complete mathematical world model; they do not say that a reader has
acquired \(v\), or that a controller can enumerate the worlds.

The same geometry now settles the exact \(p_J\) child question. Its global
two-branch parametrization and branch-order certificates imply

$$
f_{MM}\!\restriction_{\mathcal F_{p_J,v}}\text{ is injective}
\qquad(v\in\mathbb R).
$$

Thus no exact acquired \(M\) child contains two different worlds with the
same terminal \(M\) response. In particular, a child cannot contain both the
terminal \(J\) collision pair and the terminal \(M\) collision pair required
by the earlier \(L_1/L_2\) predicate. This is
an actual exclusion of that exact geometric predicate, not merely a finite
candidate list.

There is nevertheless a nontrivial observation fibre. At the exact \(p_J\),
there exist two distinct regular worlds with the same acquired response

$$
u_M(W_0)=u_M(W_1)=v_{\mathrm{loc}},
\qquad
\frac{15145}{100}<v_{\mathrm{loc}}<\frac{15147}{100},
$$

while \(f_{MM}(W_0)\ne f_{MM}(W_1)\). The current response therefore leaves
two candidates, but one permitted terminal \(M\) read separates them. This is
the concrete pattern

$$
\text{nontrivial observation fibre}
\;+
\text{injective future readout}
\;\Longrightarrow\;
\text{recoverable task fibre}.
$$

The promotion rule is now precise:

$$
\text{finite geometric fibre}
\not\Rightarrow
\text{finite acquisition},
\qquad
\text{response collision}
\not\Rightarrow
\text{irrecoverability}.
$$

To turn the injective terminal read into a controller theorem, the source
contract must still declare that \(v\) has actually been acquired, that the
terminal \(M\) action is legal, that its response is recorded, and that its cost and
successor update are available. Under those clauses, the child-specific
target \(f_{MM}\) has a one-step recovery certificate; without them, the
geometry remains a semantic result only.

The latest quantum recovery volume supplies a parallel quantitative result.
For the fixed six-cell horizon-three partition, the exact terminal-channel
optimum is

$$
\varepsilon_{\mathcal P}
 =\frac{793-88\sqrt{13}}{1508}
 <\frac{11}{32},
$$

where \(11/32\) is the sum of the two separate ambiguous-record optima.
The strict improvement comes from a common tester and a joint decoder family;
it cannot be obtained by adding recordwise minima. The global peak-six online
threshold \(E^*\) of Section 70 is a separate optimization over the whole
declared contract and satisfies

$$
\varepsilon_{\mathrm{op}}(6,3)=E^*
\le\varepsilon_{\mathcal P}.
$$

Both statements are contract-relative and ordinary mathematical results. They
do not provide a universal \(W_n\) law, a physical register cost, or Lean/
kernel certification.

## 72. Finite transducers as an execution-layer realization

The latest `dev` volume [Predictive Thermodynamic Finite Transducers](PREDICTIVE_THERMODYNAMIC_FINITE_TRANSDUCERS.md)
supplies a concrete instance of the execution layer that Sections 60--62 leave
abstract. Its source decoder is total: a valid raw word is mapped to its
physical query, while a malformed word is mapped to a declared dummy query and
also records an actual error prefix. The two cases are therefore not inferred
from equality of the final output.

For a raw source word of length \(L\), the declared preprocessor has a total
clock

$$
b(L)=(4L+20)L+13,
$$

and the paid one-query protocol has an explicit total edge bound

$$
16L^2+50L+71.
$$

The response itself is read, pushed, reversed and handed to the postprocessor
by actual transitions. The finite control labels, all writable stack contents,
the query phase and the error-cleanup phase therefore form the controller
state; none of these fields can be erased merely because the final numerical
answer is unchanged. Arbitrary bad-input stack contents are explicitly cleaned
to a terminal configuration, which is a concrete cleanup-and-clock witness for
the failure branches in the closed-loop certificate of Section 62. The actual
transition bound supplies the decreasing execution budget; it is not a claim
that the thermal volume has already proved the abstract controller-minimality
problem.

This gives the following precise bridge:

$$
\text{semantic source fibre}
\longrightarrow
\text{finite transducer state plus actual response}
\longrightarrow
\text{clean terminal certificate}.
$$

It demonstrates how a FIB protocol can carry syntax, permissions, response
phase, failure state and real transition cost in one executable history. It does
not supply a universal finite controller for the geometric fibres above: the
physical response port, the explicit variable universe and the declared dummy
query are part of its contract. Nor does it turn a finite semantic fibre into
an acquired parameter, or establish efficient physical Gibbs preparation.

The new dev result therefore strengthens the theory's execution boundary rather
than closing its recovery boundary. The required order remains

$$
\text{acquire the needed observation}
\longrightarrow
\text{choose a legal action}
\longrightarrow
\text{execute the finite transducer}
\longrightarrow
\text{verify termination and output}.
$$

Skipping the first two arrows would again confuse a mathematical response
table with a protocol that an observer can actually run.

## 七十三、目标保持、任务控制与审计的不同合同

**约定 73.1（任务与有限模型）。** 设 $\mathcal H^+$ 是声明的实际历史域，$z:\mathcal H^+\to Z$ 是在比较切面指定的目标，$s:\mathcal H^+\to S$ 是完整当前状态。会影响后续合法性、响应、successor、资源或停止条件的隐藏字段属于状态；列入数学状态不等于授予读取权限。本节调用 §§60–62 时，保留其有限 $Z,S,A,O$ 合同，且 $O$ 只含控制器实际可取得的响应。若实际装置的原始状态无限，须另给有限抽象：目标、所用动作的共同合法域、取得的响应、后继和停止判据沿抽象交换；需要保留的资源标签也须沿抽象下降。没有这种对应时，不将有限模型定理直接用于整个无限装置。

令有限摘要 $m:\mathcal H^+\to M$ 只使用合同允许取得并保留的资料。对 $u\in m(\mathcal H^+)$，定义非空候选关系

$$
B_u=\{(z(h),s(h)):h\in\mathcal H^+,\ m(h)=u\}\subseteq Z\times S.
$$

这里 $B_u\in\mathcal W_n$ 才是定义 60.2 中有类型的判断。定理 60.3、60.5 给出：允许在知道 $u$ 后选择一个至多 $n$ 步的协议时，摘要对该预算安全，当且仅当每个 $B_u\in\mathcal W_n$。协议内部仍只能按实际取得的响应分支。若存在 $\bar z:M\to Z$ 使 $z=\bar z\circ m$，则每个 $B_u\in\mathcal W_0$；这种**目标保持**是零步特例，不是普通可继续取得任务的必要条件。

一个选定的有限控制器还须满足 §62 的初始支持覆盖、所选动作在支持上的共同合法性、每个实际响应的后继支持闭合、source-independent controller update、halt 目标相等和自然数 rank 严格下降。未选择的动作无需在该摘要上具有相同响应。相反，full-behaviour predictive quotient 要求所有声明动作的合法/禁止/未定义状态、响应、raw successor、资源、停止与更新同时因子化。后者的充分键不自动给出前者的最小控制器；$\mathcal W_n$ 对候选并集不封闭，也不保证一般任务安全分割有唯一最粗商。

**定义 73.2（raw 审计与公开投影）。** 对一个动作 $a$，将其 lawful task-domain status 与 physical execution status 分别记入 $\operatorname{RawAct}(h,a)$，并保留实际发生的功能标签、released output、receipt、完整 successor 和声明的未来行费用。未执行的 disabled/unauthorized trial 为 `none`，无 receipt，状态不变。物理上 enabled 的 noncanonical Supply 可以在 lawful task map 中未定义，却已经执行一个 IN successor；其 latch/control、mirror 和 receipt 不因 task-domain status 未定义而消失。只在确无物理执行时才使用未执行标记。

可将当前原始状态及这些带类型的行记录记为 $\operatorname{Aud}(h)$。一个声明的当前公开值 $\operatorname{Pub}(h)=\pi_{\rm pub}(\operatorname{Aud}(h))$ 只投影合同实际公开的字段。已 released 而未保留的整个旧 OUT stream 不因此成为当前状态的一部分；控制器也不能按未取得的完整 successor 序列分支。若任务另行要求旧 stream、累计费用或历史全状态序列，它们是额外历史观察，须单独声明取得与保留。审计等价蕴含这种已声明的公开投影相等，逆向一般不成立。

**约定 73.3（native 供应与其边界）。** 以下各节的仓内供应引用均固定于 [源版本](https://github.com/the-omega-institute/trureturing/tree/033c1b370f2447aa20e191a6a3da609aba697e50)。其中 [Native acquired input, the unfinished-request frontier, and actual replay](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACQUIRED_INPUT_FRONTIER_AND_REPLAY.md) 简称 native。其 §§11.1–11.5 在固定 $A^+$ 的整个 lawful reached domain $\Omega^+$ 上给出

$$
K(h)=\bigl(\operatorname{code}(u),I(h),n(h),\kappa(h),m_C(h)\bigr),
\qquad
h\equiv_{\rm now}h'
\ \Longleftrightarrow\ K(h)=K(h')
\ \Longleftrightarrow\ X^+(h)=X^+(h').
$$

$u$ 是实际安装的 seed/source code，$I$ 是实际 IN 已消费的有序输入，$n$ 是绝对 P receipt 数，$\kappa$ 是 Capture 的实际 P 切点，$m_C=N_C-c_F(u)$ 是固定 startup 后 C 的已执行行数；未 Capture 时为 $(\kappa,m_C)=(\bot,0)$。$\equiv_{\rm now}$ 比较从当前切面开始的 partial finite-experiment maps，包括其域与完整 raw successor。native Theorems 11.9、11.11 和 Proposition 11.12 已供应该 kernel 及实际更新，不在这里重证。

完整 successor 是其反向 kernel 所用的数学审计数据，不是免费公开读口。该键也不是已经由 C 取得的 package。它不提供 public-output-only rigidity、独立自然视图的逆、历史累计结构费用的因子化或全域有限控制器最小性。raw noncanonical Supply 的物理边仍存在，但其后续不再属于 $\Omega^+$；不能用一个统一 $\bot_{\rm undefined}$ 覆盖整个物理记录。

## 七十四、取得前沿、当前重放与不可逆的全序损失

**定义 74.1（取得切面与因子关系）。** 实际取得前沿保留已经消费的有序输入、尚未 WR 的 latch 材料、请求阶段、owner、权限、pending event 和实际计数器。它按

$$
\text{acquire}\to\text{latch}\to\text{write}\to\text{request complete}
\to\text{seal}\to\text{deliver}
$$

区分不同切面。bit 一旦由 IN 消费，即使尚未 WR，也不能在 replay 中再次作为未来输入索取。对两个观察 $f,g$，只有在实际域上存在 $q$ 使 $f=q\circ g$，才称 $f$ 由 $g$ 因子化；等价义务是 $f$ 在每个 $g$-纤维上恒定。因此 acquired frontier、replay key、当前公开值与 exact chronology 不是未经证明就嵌套的集合链。

**命题 74.2（chronology 的确定域与排除域）。** 在 native §11 的 captured key 上令

$$
p=n-\kappa,\qquad q=m_C-1,
\qquad L(K)=\binom{p+q}{p}.
$$

完整 endpoint 纤维有恰好 $L(K)$ 条实际 P/C 全序。Armed 纤维为单点；captured 纤维恰在 $p=0$ 或 $q=0$ 时为单点。在这些单点纤维上，normal evaluation 恢复实际 chronology。若 $p,q>0$，任何只依赖当前 endpoint 的函数都不能恢复实际执行全序。即使同时给出当前 $S_{\rm now},B_{\rm now},M_C$，或者从同一 endpoint 继续执行相同的未来选择且不加入先前保留的记录，结论仍然如此。

**证明。** native Theorem 11.16 已确定纤维：固定 startup、Capture 前 P 链及 Capture 后两条 owner 链，只剩这两条链的 shuffle。其枚举、实际合法性、相同完整 endpoint 和单点条件均由该定理供应。$L(K)>1$ 时两条不同全序具有相同函数输入，却要求不同答案，故不存在所述逆。相同 endpoint 上相同未来选择给出相同后续，是同一状态转移语义的直接归纳。∎

native Theorem 11.15 给出的 $T_{\rm cut}$ 保留两条 owner 链及实际 Capture bracket，它与 $K,X^+,S_{\rm now}$ 的 actual-image recovery routes 相容；选取其任意线性扩展只得到一个相容历史。按 native Corollary 11.17，若增加 supplement $Z$ 后要求精确全序，则 $Z$ 必须在同一 endpoint 纤维上区分全部 $L(K)$ 个历史，故固定二进制宽度满足 $2^b\ge L(K)$。这是历史补充记录的必要标签数，不构造在线 logger，也不给出物理 port 或总代价下界。过去累计结构 tariff 是否下降到 endpoint 还需 native (AIF.40) 的逐交换费用等式；当前 successor 的未来费用相同不替代该条件。

**约定 74.3（不同 $A_R$ 的 pre-Pin historical inverse）。** native §12 的 $A_R$ 增加 disjoint scaffold、十五槽构造、atomic two-meter Pin、受限 cursor/read grants、canonical code/seed loader 和实际进入的 startup。令 $\mathcal D_R$ 为所有实际 reached、R 仍 Armed 的 pre-Pin 状态，允许旧 P/C 处于各个声明阶段。令 $\pi$ 为保持旧身份的投影，$K_R(x)=K(\pi(x))$。native (AIF.46)、Theorems 12.21、12.23 供应

$$
\mathcal L_RK_R=\operatorname{id}_{\mathcal D_R},\qquad
K_R\mathcal L_R=\operatorname{id}_{K_R(\mathcal D_R)}.
$$

其中 target $x$ 是实际 Pin 的**前驱状态**。在每个已调用程序的 pointwise R-progress、足够 backing 和声明权限下，程序逐 bit demand 已达到的输入，实际取得、seal、copy、print、ACK 并返回该历史记录；每次有限调用终止，不提供统一 scheduling-delay、elapsed-time 或总资源上界。Pin 离开 $\mathcal D_R$，不是 Armed key 的域内更新。打印历史 token/permission/grant 不恢复 live capability。

这一 actual-image inverse 包含目标时刻的 R 初始化材料，却不反演后来的 R acquisition/maintenance 状态，不恢复 current-at-return 的整个联合状态，也不是 unchanged $A^+$ 的全域 collector。固定 R startup 的插入点不分开旧的非单点 shuffle 纤维，因此它不推翻命题 74.2。没有 supplement 的全域 endpoint-only exact chronology 已被排除；可继续研究的是另外声明的历史记录合同及其取得成本。

## 七十五、付费 current gcd 口上的一源算术取得

**约定 75.1（实际端口与两个目标）。** 本节只使用 [Arithmetic acquisition and behavior return §9](RECURSIVE_RELATIONAL_OBSERVATION_ARITHMETIC_ACQUISITION_RETURN.md) 的独立 pair apparatus。公开 $H\ge1$，唯一实际 source $u=(a,b)^{\mathsf T}\in\mathbb N^2$，包括零坐标，入口为 $v_0$。只有

$$
R(u)=Mu,\quad G(u)=u+\alpha,\quad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
\alpha=\binom10,\quad q=(2,3),\qquad
\operatorname{Read}_H(u)=\gcd(qu,H)
$$

是 source 服务；read 是明确供应的、付费无损**当前**读口，$\gcd(0,H)=H$。执行串行且绑定唯一，没有 reset、clone、saved entry source、物理 inverse、坐标读或额外 source-dependent reply。隐藏 source 大小、service tariff 和 backing 不是控制器判别口。每个声称的有限运行有足够有限 backing、合法绑定/权限和服务完成；这不假定一个固定有限容量覆盖所有无界入口或未来长度。

安装的两个寄存器分别为

$$
e=v_0\bmod H\quad\text{（immutable entry）},\qquad
c=u_*\bmod H\quad\text{（mutable reached state）}.
$$

$c$ 随同一实际绑定的后续 $R/G$ acknowledgement 同步更新；$e$ 不变。二者均不是未取得的源坐标或原 source 的恢复。

**约定 75.2（Theorem 9.3 供应的同运行向量）。** 按资源顺序 $(N_{\rm read},N_G,N_R)$，精确 endpoint 和已执行计数为

$$
H=1:\quad (0,0,0),\qquad u_*=v_0;
$$

$$
H>1\text{ 奇}:\quad(2H,2H,1),\qquad
u_*=Mv_0+HM\alpha+H\alpha;
$$

$$
H\text{ 偶},\quad L=H/2:\quad
(H+r+\chi,\ H+\chi,\ r+1+\chi),\qquad
r\in\{0,1,2\},\quad\chi\in\{0,1\},
$$

$$
u_*=
\begin{cases}
M^{r+1}v_0+L(M\alpha+\alpha),&\chi=0,\\
M^{r+2}v_0+L(M^2\alpha+\alpha)+M\alpha,&\chi=1.
\end{cases}
$$

$r$ 是入口 paid parity search 实际执行的 replacement 数，$\chi$ 是第一 scan 后在 $Mw$ 的 paid parity test 是否要求实际 $G,R$ correction。偶数分支始终只有**两个完成的 $L$-scans**，各含最后一次 read 之后的 closing $G$。第一次从 $M^rv_0$ 开始；第二次从 $Mw$（$\chi=0$）或 $M^2w+M\alpha$（$\chi=1$）开始，其中 $w=M^rv_0+L\alpha$。$Mw$ 的奇数回复是中间付费测试，不是已完成的另一 scan。仅在同一 binding、同一 scan start、未发生 source update 时，已付费的回复才可复用为 scan 的第零项。上述调度、两个取得寄存器及向量的证明均引用 supplier Theorem 9.3 的 (AQBRP.5)–(AQBRP.17)，不另立不同调度。

实际末端数量为

$$
qu_*=
\begin{cases}
2a+3b,&H=1,\\
3a+5b+5H,&H>1\text{ 奇},\\
qM^{r+1+\chi}v_0+(5+2\chi)H/2+3\chi,&H\text{ 偶}.
\end{cases}
$$

supplier (AQBRP.8)–(AQBRP.9) 保证每个实际 acquisition prefix 的数量不超过末端；偶数时 $qu_*\le13a+21b+7H/2+3$。这保留未知入口的依赖，并不把数量变成可读参数。偶数计数上界为 $N_{\rm read}\le H+3,N_G\le H+1,N_R\le4$。

**定义 75.3（分开的资源与继续使用）。** 对实际 pre-call sources $u_i$ 和分别供应的 tariffs $\rho_H,\gamma,\tau$，source-service work 为

$$
W_{\rm svc}=
\sum_{i\in\mathcal I_{\rm read}}\rho_H(u_i)
+\sum_{i\in\mathcal I_G}\gamma(u_i)
+\sum_{i\in\mathcal I_R}\tau(u_i).
$$

另外计入 local bit work、tape reads/writes、installed code/data、source storage/retention、backing、binding/rights、acknowledgement 和 output/installation。supplier 的 $O(H\log(H+1))$ acquisition tape 与 $O(\log(H+1))$ modular working space 是充分 local bounds，不控制 source backing 或 source services 对未知入口的依赖，也不覆盖任意未来 trace 保留。

同一 source 的继续使用由 supplier (AQBRP.22)–(AQBRP.23) 供应：

$$
\operatorname{Out}_H(c)=\gcd(2c_1+3c_2,H),\qquad
\delta_R(c)=Mc,\qquad\delta_G(c)=c+\alpha.
$$

真实 source action 完成后再 local commit，才开放下一个 callable cut。这里取得的是改变 endpoint 后的 arithmetic quotient；相同 residue 的源可有不同整数 composition、树顺序/括号、chronology、handle、权限与 service bill。固定数量的 primitive replacements 不等于固定总费用，所列点也不是 minimum、reset 策略的支配比较或物理 gcd 口实现。

## 七十六、终端 sharp-task 签名及其最粗纤维

**定义 76.1（全 qutrit 的 flagged instrument 与可见信息）。** 固定有限 $n\ge0$ 和实角 $\theta$，取 [Environment record memory §26](AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md) 的整个 $H_q=\mathbb C^3$：

$$
U_0=(23),\quad W=(12),\quad a=U_0e^{i\theta W},\quad b=aW,
\qquad Q_h=V_{h_n}\cdots V_{h_1},\quad (V_0,V_1)=(a,b).
$$

$h_1$ 最先作用，$Q_\varnothing=I_3$。实际 fresh measured instrument 的每步 outcome 在所有 qutrit 输入上条件公平，因此 $p_h=2^{-n}$。以下终端判据也允许同一 word matrices 上另行声明的任意 input-independent full-support law $p_h>0$，不声称公平 apparatus 产生其他律。

设 $t(m\mid h)$ 为 input-independent stochastic kernel，$M$ 为有限终端 alphabet。其**实际传给解码器的量子—经典系统**为

$$
\mathcal F_t(X)=\sum_{m\in M}|m\rangle\langle m|\otimes
 \sum_h p_ht(m\mid h)Q_hXQ_h^\dagger.
$$

解码器只能获得该 qutrit 与完整 counted view $m$，并知道固定的 $\theta,n,p,t$、预先指定的有限 projection family $\mathscr E=(E_1,\ldots,E_k)$（$k\ge1$）及固定控制描述。没有其他未计入的 history-dependent clock、archive、program selection 或 seed，没有 input-dependent side information、reference access、postselection 或较小输入 code。丢弃的 private randomness 已平均进 $t$；可见且 history-dependent 的随机变量计入 $m$。允许每个 $m$ 选一个 qutrit CPTP map $\mathcal D_m$，但同一个 $\mathcal D_m$ 必须同时服务全部 $E_j$。目标是在所有 density matrices 上使 averaged corrected channel

$$
\mathcal T=\sum_m w_m\mathcal D_m\mathcal N_m,
\quad w_m=\sum_hp_ht(m\mid h),\quad
H_m=\{h:p_ht(m\mid h)>0\},\quad
\mathcal N_m=\sum_{h\in H_m}\frac{p_ht(m\mid h)}{w_m}
                  \operatorname{Ad}_{Q_h}
$$

满足 $\mathcal T^\dagger(E_j)=E_j$；只定义 $w_m>0$ 的条件分支。这里的 dagger 是 trace adjoint。目标是同时恢复这些 sharp Born probabilities，不是将不同未知输入或不同任务的最优 decoder 拼接。

**定理 76.2（正支持任务签名判据）。** 定义 finite-horizon task signature

$$
\sigma_{\mathscr E}(h)=
 (Q_hE_1Q_h^\dagger,\ldots,Q_hE_kQ_h^\dagger).
$$

定义 76.1 的 exact common decoding 存在，当且仅当对每个 $w_m>0$，$\sigma_{\mathscr E}$ 在 $H_m$ 上恒定。等价地，对所有 $h,g\in H_m$ 和所有 $j$，

$$
[E_j,Q_h^\dagger Q_g]=0.
$$

若 $\mathcal A_{\mathscr E}$ 是 $I_3,E_1,\ldots,E_k$ 生成的 complex unital star algebra，等价条件也写成

$$
\mathcal A_{\mathscr E}\subseteq
\bigcap_{m:w_m>0}\{Q_h^\dagger Q_g:h,g\in H_m\}'.
$$

**证明。** 若 exact decoding 存在，对每个 $j$ 写 $F_{m,j}=\mathcal D_m^\dagger(E_j)$，它是 effect，且

$$
E_j=\sum_{h,m}p_ht(m\mid h)Q_h^\dagger F_{m,j}Q_h.
$$

projection 是 effect interval 的极点。具体地，对 $x\in\ker E_j$，右侧各非负二次型之和为零，故每个正权项 annihilate $x$；对 $x\in\operatorname{ran}E_j$，同样将该论证用于补 effect。于是每个正权 effect 都恰等于 $E_j$。因此

$$
F_{m,j}=Q_hE_jQ_h^\dagger\qquad(h\in H_m),
$$

同一 $m$ 的签名必恒定。这一步也说明只要求 averaged exactness 不能让不同正权分支互相抵消错误。

反之，为每个非空 $H_m$ 选一个 $h_m\in H_m$，使用单一 unitary decoder $\mathcal D_m=\operatorname{Ad}_{Q_{h_m}^\dagger}$。签名相等给出

$$
Q_h^\dagger Q_{h_m}E_jQ_{h_m}^\dagger Q_h=E_j
\qquad(h\in H_m,\ 1\le j\le k).
$$

故同一 $\mathcal D_m$ 对全部任务精确，求和仍精确。签名相等与 displayed commutators 等价；与生成元交换等价于与其生成的 star algebra 交换，得到最后的写法。∎

这是对本 word instrument 的 terminal fibres 的直接组合证明。[Bény–Kempf–Kribs, *Quantum Error Correction of Observables*, Definition 8、Theorem 9、Corollary 10](https://arxiv.org/html/0705.1574v1) 已供应一般 observable-algebra correction 判据；这里其 code projection 是 $I_3$，Kraus products 为 $\sqrt{p_ht(m\mid h)p_gt(m\mid g)}\,Q_h^\dagger Q_g$。本定理不另立一般 observable-correction 定理，也不将 qutrit spectator projection 当作输入 code。

**推论 76.3（最粗 deterministic terminal partition 与正 alphabet）。** 令

$$
h\sim_{\mathscr E}g\quad\Longleftrightarrow\quad
\sigma_{\mathscr E}(h)=\sigma_{\mathscr E}(g),\qquad
N_{n,\theta}(\mathscr E)=|\sigma_{\mathscr E}(\{0,1\}^n)|.
$$

在定义 76.1 的 terminal contract 下，所有安全 deterministic partitions 恰为该 signature partition 的 refinements；所以它是唯一最粗者。即使允许 stochastic summaries 和任意 qutrit CPTP decoders，最小 positive terminal alphabet 也恰为 $N_{n,\theta}(\mathscr E)$。

**证明。** deterministic 情形直接应用定理 76.2。stochastic 情形中，每条正概率历史至少给一个终端值正质量；不同 signatures 的 histories 不能给同一终端值正质量。因此每个 signature class 必须占用一个不同的 positive value，给出下界。存储 signature class 并按定理 76.2 选 inverse 达到该数。若另有明确不计费的 independent shared seed，条件于该 seed；有限 histories 的共同满测集上同一论证仍成立，故不能降低 conditional alphabet 下界。∎

此唯一最粗商属于终端 exact sharp-task 合同；它不与 §73 的一般动态任务分割相混。对实际下一标签 $j$，signature 的数学更新是将每个成员同时以 $V_j$ 共轭，故其相等性保持。在线实现还须实际取得这些标签并供应相应控制、更新表与时钟；终端 alphabet 定理不优化这些资源，也不产生整个任务控制器或 apparatus minimum。

**命题 76.4（$\theta=0,n\ge3$ 的三个不同终端任务）。** 令 $\xi=(1,1,1)^{\mathsf T}/\sqrt3$，$P=|\xi\rangle\langle\xi|$，并用标准坐标基 $\epsilon_1,\epsilon_2,\epsilon_3$。取三种预先指定任务：$(P)$；$(|\epsilon_1\rangle\langle\epsilon_1|)$；以及下列 finite tomographic projection family

$$
\mathscr E_{\rm full}=
\left(\ |\epsilon_i\rangle\langle\epsilon_i|\ (1\le i\le3),\quad
\frac{|\epsilon_i+\epsilon_j\rangle\langle\epsilon_i+\epsilon_j|}{2},\quad
\frac{|\epsilon_i+\mathrm i\epsilon_j\rangle\langle\epsilon_i+\mathrm i\epsilon_j|}{2}
\ (1\le i<j\le3)\ \right).
$$

其最小 terminal alphabets 依次为 $1,3,6$。若把一个 terminal label 单独编码为固定长度、禁止子串 $11$ 的 binary word，且不混入 horizon/phase/其他资源，则最短长度依次为 $0,2,4$。

**证明。** Environment §§4–5 的 Theorems 4.1、5.1 已供应 actual chronological words 在 $n\ge3$ 恰遍历 $S_3$，且 permutation matrices 的 projective equality 就是 equality。全部 words 固定 $P$，给出一个 signature；坐标 rank-one projection 的 orbit 有三个成员。$\mathscr E_{\rm full}$ 的 Hermitian real span 为全部 Hermitian $M_3$，因为它给出各 diagonal、off-diagonal real part 和 imaginary part；所以同时保留其 Born probabilities 等价于 full-state channel identity。相同 full signatures 要求两 word matrices 之比与全部 $M_3$ 交换，即相差 scalar；此处恰有六类。推论 76.3 给出三个 alphabets，包括 stochastic 情形。禁止 $11$ 的长度 $\ell$ words 数为 $F_{\ell+2}$（$F_0=0,F_1=1$），由按首位 $0$ 或 $10$ 分类的递推得到；长度 $0,1,2,3,4$ 分别有 $1,2,3,5,8$ 个。于是三个最短长度为 $0,2,4$。∎

Environment Theorem 4.1 对 full projective-word statistic 另供应 clock/table 条件下的 online realization，§5 还供应 homogeneous six-value register；这些是独立的 supplier 结论。上述单个 forbidden-$11$ code 长度不计 paid label acquisitions、fresh environments、calibration、clock、tables、inverse controls 或动态编码更新，不能据此推论整个任务控制器的最小成本。

**约定 76.5（完全擦除的供应边界）。** 当 $M$ 只有一个值时，Environment Theorem 26.2、Corollary 26.3 对所有 full-support input-independent laws 供应唯一最大 common-correctable algebra

$$
\mathcal C_{n,p}=
\begin{cases}
M_3,&n=0,\\
\{W\}'\cong M_2\oplus\mathbb C,&n=1,\\
\mathbb CP\oplus\mathbb C(I_3-P),&n\ge2.
\end{cases}
$$

共同 decoder 可分别取 $\operatorname{id}_3,\operatorname{Ad}_{a^\dagger},\operatorname{id}_3$。所以 $n\ge2$ 完全擦除后 exact sharp projections 恰为 $0,I_3,P,I_3-P$。Proposition 26.4 已说明 positive support 在 $0^n,e_1,e_2$ 上足够维持这一上界，删去所需支持则可扩大 correctable algebra；此处 $e_i$ 是第 $i$ chronological bit 为一的历史。一般支持分类和一般 correction 原理均引用 supplier；定理 76.2 使用的是每个 summary 的实际正支持。

## 七十七、公平擦除后的方向依赖误差

**定义 77.1（量化任务与记号）。** 本节严格使用 [Environment §27](AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md) 的实际 fair law $2^{-n}$，完全擦除历史且不保留 summary。令

$$
\Delta_W(X)=\tfrac12(X+WXW),\quad
F=\operatorname{Ad}_{U_0}\circ\Delta_W,\qquad\mathcal N_n=F^n.
$$

actual angle family 的 averaged channel 在每个 $\theta$ 都是该 $F$，但单独 word matrices 未被替换。对固定 unit vector $v$ 与 $E=|v\rangle\langle v|$，任务为

$$
\eta_n(E)=\min_{\mathcal D\ {\rm CPTP}}
\sup_{\rho\in\mathsf D(\mathbb C^3)}
\left|\operatorname{Tr}(E\mathcal D F^n(\rho))-\operatorname{Tr}(E\rho)\right|.
$$

所有 qutrit inputs 均在 supremum 中，decoder 只按固定 $E,n$ 选择，没有历史、reference access、较小 input code、intermediate correction 或 postselection。此处是 Born-probability error，不是 diamond distance。

取 ordered orthonormal basis

$$
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\quad
 e_q=(1,1,-2)^{\mathsf T}/\sqrt6,\quad
 f_q=(1,-1,0)^{\mathsf T}/\sqrt2,
$$

并记

$$
p=|\langle\xi,v\rangle|^2,\quad
q=|\langle e_q,v\rangle|^2,\quad
r=|\langle f_q,v\rangle|^2,\quad p+q+r=1.
$$

这些是 task populations，不是 history law，也不是 §75 的 entry register。对有限 $n\ge1$，置

$$
s=(-1/2)^{n-1},\quad\tau=|s|>0,\quad
\alpha=(1+s)/2,\quad\beta=(1-s)/2,\quad k=\sqrt{r(1-r)}.
$$

**约定 77.2（供应的 effect image 与边界值）。** Environment (27.4)–(27.7)、Proposition 27.2 已给出整个 effect optimization

$$
\eta_n(E)=\min_{0\le B\le I_3}\|(F^n)^\dagger(B)-E\|_{\rm op},
$$

及所有可达 $C=(F^n)^\dagger(B)$：

$$
C=G_s(K)=
\begin{pmatrix}
x&sz&0\\s\overline z&\alpha y+\beta d&0\\
0&0&\beta y+\alpha d
\end{pmatrix},\qquad
K=\begin{pmatrix}x&z&0\\\overline z&y&0\\0&0&d\end{pmatrix},
\qquad 0\le K_2\le I_2,\quad 0\le d\le1.
$$

这里 $K_2$ 为左上 $2\times2$ block。对应实际 output effect 是 $B=U_0KU_0^\dagger$；可用 $\mathcal D_B(X)=\operatorname{Tr}(BX)E+\operatorname{Tr}((I_3-B)X)(I_3-E)/2$ 实现该单任务 decoder。supplier 同时供应 matching lower certificates，且以 diagonal-unitary invariance 将 complex phases 归约，误差只依赖 $(p,r)$。

具体地，Theorems 27.3–27.5 供应 $\eta_0(E)=0$、$\eta_1(E)=k$、$\eta_n(E)\ge k$，以及两个边界的 exact values。$p=0$ 时对每个有限 $n\ge1$，

$$
\eta_n(E)=\tfrac12\sqrt{4qr+(|q-r|-\tau)_+^2}.
$$

$q=0,n\ge2$ 时，令 $a_\tau=(1+\tau)/2,b_\tau=(1-\tau)/2$，并定义

$$
h_\tau(w)=
\begin{cases}
b_\tau w/a_\tau,&0\le w\le a_\tau,\\
(a_\tau w-\tau)/b_\tau,&a_\tau\le w\le1.
\end{cases}
$$

则

$$
\eta_n(E)=
\begin{cases}
k,&h_\tau(r)\le k,\\
\displaystyle\frac{b_\tau(\tau-a_\tau r)+a_\tau\sqrt{\tau^2p+b_\tau^2r^2}}{\tau},
 &h_\tau(r)>k.
\end{cases}
$$

这些式子的优化与 attainability 引用 supplier，不另复证。$n=1$ 使用 $k$，不在 $b_\tau=0$ 时代入后一式；$n=0$ 也不代入 $s$。

**推论 77.3（同一 spectator population 不决定误差）。** 在同一实际 fair instrument、同一 finite horizon，取 $v=e_q$ 和 $v=(e_q+f_q)/\sqrt2$。二者均有 $p=0$，但误差分别为 $(1-\tau)/2$ 和 $1/2$；在 $n=3$ 恰为 $3/8$ 与 $1/2$。

**证明。** 将 $(q,r)=(1,0)$ 与 $(1/2,1/2)$ 代入已引用的 $p=0$ 边界值。这也是 supplier Corollary 27.6 的两个 actual tasks；差为 $\tau/2>0$。∎

因而仅保留 task 的 spectator population $p$ 会合并不同的 quantitative answers，必须保留相对于 erased $W$ sectors 的方向。反之 $r$ 单独在 $n\ge2$ 也不够：$v=\xi$ 与 $v=e_q$ 都有 $r=0$，但误差为零与 $(1-\tau)/2$。

**定义 77.4（定量残余的精确范围）。** Environment Theorem 27.7 的 scalar feasibility criterion (27.24) 已完全判定 $0<r<1$ 时何时达到 floor $k$；Proposition 27.9 的 (27.27)–(27.28) 给出其余误差的有限维 coupled feasibility。尚缺的是 $n\ge2$ 时 $r=0,pq>0$，以及 interior $p,q,r>0$ 且不在 floor region 内的 analytic/piecewise 或足够显式 fixed-degree algebraic optimum、attaining effect 和 matching lower certificate。rank-two tasks 由 supplier Proposition 27.8 的 $\eta_n(I_3-E)=\eta_n(E)$ 归约。

这些 numerical values 不转移到任意 full-support correlated laws；§76 的 exact support criterion 则有那一较宽适用域。有限任务族的 approximate common objective 必须直接最小化同一 $\mathcal D$ 下的最大任务误差。分别最优化每个 $E_j$ 的值不能拼成一个共同 decoder；§76 的 exact common construction 不给出这种 approximate conclusion。

## 七十八、实际压缩的快速率障碍与仍开放的临界目标

**约定 78.1（同一完整复空间）。** [Actual pair energy §30](AURIC_FIB_ACTUAL_PAIR_ENERGY_OVERLAPPING_PROJECTIONS.md) 保持原 $\theta=\pi/6$ actual matrices

$$
A=\tfrac14\begin{pmatrix}\sqrt3-i&3+i\sqrt3\\3-i\sqrt3&-\sqrt3-i\end{pmatrix},
\quad J=\operatorname{diag}(-1,1),\quad
C=JA^{-1}JA,\quad D=AC,
$$

并在 $K_{\rm grp}=\{g\in U(2):\det g=\pm1\}$ 的 $L^2(K_{\rm grp};\mathbb C)$ 上取其 §20 的 translation convention $T_g$，

$$
Q=(I+T_J)/2,\quad\mathcal H_J=\operatorname{ran}Q,\quad
\mathsf S=(T_C+T_{C^{-1}})/2,\quad
\mathsf B=(T_D\mathsf S)|_{\mathcal H_J},\quad
E_C=(I+T_C+T_C^2)/3.
$$

$D^3=iI$ 在完整群中保持；不能将其当作三阶矩阵或删除其他中心扇区。令 $\Pi$ 是任意有限个完整 Peter–Weyl 左正则等型分量的投影，$\mathcal H_{J,\Pi}=\mathcal H_J\cap\ker\Pi$，$B_\Pi=\mathsf B|_{\mathcal H_{J,\Pi}}$。它是约化子空间。

**约定 78.2（供应的实际下界和被排除的窗口）。** supplier Theorem 30.3、Corollaries 30.4–30.5 供应，对每个有限整数 $r\ge1$、每个上述 finite $\Pi$，

$$
\|B_\Pi^r\|^2\ge(1+r/2)2^{-r}>2^{-r}.
$$

这里是原完整复空间中的实际子表示见证，不是离散正则模型的范数替代。令 $E=E_C|_{\mathcal H_{J,\Pi}}$，同一实际缺陷给出

$$
G_r=\sum_{j=0}^{r-1}(B_\Pi^\dagger)^j(I-E)B_\Pi^j
 =\tfrac43\bigl[I-(B_\Pi^r)^\dagger B_\Pi^r\bigr].
$$

因此若 $G_r\ge cI$、$a_r=1-3c/4$，必有

$$
a_r\ge(1+r/2)2^{-r},\qquad
c\le\tfrac43\bigl[1-(1+r/2)2^{-r}\bigr]
 <\tfrac43(1-2^{-r}).
$$

被排除的是 supplier (24.4) 的 exact fast-window requirement $a_r\le2^{-r}$，对每个 finite window 都被排除，即使 $r$ 和 finite removal 依 horizon 改选。较弱正耗散常数是否存在未由此判定；增长窗口允许 subexponential excess 的路线也未被排除。相应统一供应若写成

$$
\|B_\Pi^{n-1}\|^2\le2^{-n}s_n\quad(n\ge1),
$$

则必要 $s_n\ge n+1$，但并未证明这个 prefactor 足够，也没有反驳 $\log s_n=o(n)$。全部供应证明见 §30，不在此重复其矩或自旋 certificates。

**定义 78.3（原目标的保留量词）。** 原 finite upper-frequency target 仍为

$$
L_n=\left\lfloor2^{n/3}/4\right\rfloor,\quad
\rho_\ell(g)=(\det g)^\ell\operatorname{Sym}^{2\ell}(g),\quad
Q_\ell=(I+\rho_\ell(J))/2,\quad M_\ell=\rho_\ell(A)Q_\ell,
$$

$$
\mathcal S_n=\sum_{\ell=0}^{L_n}(2\ell+1)\|M_\ell^n\|_{\rm HS}^2,
\qquad \log\mathcal S_n=o(n).
$$

finite removal 后的无限尾空间与仅保留 $\ell\le L_n$ 的窗口不同。§30 的下界先固定 $r$ 再取充分大自旋；其方便的充分见证阈值在 $r=n-1$ 时为 $\ell\ge2^{10n-8}$，不能据此将见证放入 $L_n$。这个充分阈值也不排除窗口内另有见证。故快速率障碍既不证明也不反驳 $\mathcal S_n$ 的原目标。

令 $g_0=A,g_1=AJ$，并保留原 actual chronological products

$$
G_h=g_{h_n}\cdots g_{h_1},\quad
F_h=e^{-in\pi/6}G_h,\qquad
E_n(r)=4^{-n}\sum_{h,g\in\{0,1\}^n}
\mathbf 1_{\{\|F_h-F_g\|_F\le r\}}.
$$

这里 $\|\cdot\|_F$ 是未归一化 Frobenius norm。按 supplier §§19、23、30.8，仍需原 actual fair ordered pair quantity $Q_n^{\rm pair}=2^nE_n(2^{-n/3})$ 的 subexponential upper bound；它与该 finite-cutoff target、原分辨地址碰撞熵 $H_{\rm col}(Z_n)=n-o(n)$ 的接口保持不变。$E_n$ 保留闭有序 pairs、diagonal histories、actual multiplicities 和共同时间相位。在另外供应的 same-controller recovery necessity (7.3) 下，仅有条件界

$$
\varepsilon_n=2^{-2n/3}/36,\qquad
W_n^{\rm peak}(\varepsilon_n)\ge\frac{2^n}{4Q_n^{\rm pair}},\qquad
\log_2W_n^{\rm peak}(\varepsilon_n)\ge n-\log_2Q_n^{\rm pair}-2.
$$

$W_n^{\rm peak}$ 是该 supplier 完整 causal controller 的 peak width，与 §60 的 acquisition layer $\mathcal W_n$ 不同；误差是原 full-$H$、reference-inaccessible、平均不减半 diamond norm。缺少 $Q_n^{\rm pair}$ 的目标上界就不能得到 $n-o(n)$ memory conclusion。该 full-state approximate programme 不由 §76 的有限 exact sharp alphabets 或 §77 的单任务 probability errors 结算。

## 七十九、strict-real 同基底见证与一次取得的局部应用

**定义 79.1（完整 legal-world collision）。** [Strict-real joint-incidence support §§1–2](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md) 在本节局部取 $J=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$、$M=\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$，保持原 acquired word $J,M,J,M,M,M$、clocks $0,\ldots,7$ 与

$$
H_4=(0,J,24,M,147/5,J,24,M,18),\qquad
C(p,v)=\mathcal F(H_4,M,p,M,v),\quad p\ne24.
$$

此处用 $P_{\rm par}$ 区别于 qutrit spectator projection，whole world 为

$$
W=(P_{\rm par}(r,b),g,d),\qquad
P_{\rm par}(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},
\quad 0<r<1,\quad b>0.
$$

$g$ 是每个 world 内同一个 nonzero real polynomial、$\deg g\le3$，$d\in\mathbb R$。以 $A_0=I_2,A_i=E_iA_{i-1}$ 累积该历史已执行的字母，clock $i$ 的读数为 $d+g(i)\operatorname{tr}(A_iP_{\rm par})$；各原读数必须按其真实 clock 已发生。允许较低 degree、sampled/repeated roots、zero drift、singular source 与 unbounded positive off-diagonal，不能靠 regular chart 排除它们。clock seven 的 $J/M$ 是两个 counterfactual alternatives，不是在同一 run 顺次多读两次。

在同一 acquired $(p,v)$，$D_J$ 表示 $C(p,v)$ 中有一对 distinct legal worlds 的 terminal-$J$ responses 相等，$D_M$ 类似。$D_J\cap D_M$ 要求两个 collision pairs 共用同一 child；两 pairs 可以重叠，但每对内部必须 distinct。同一个 resultant index zero、complex root 或违反 strict guards 的 rational label 不是该见证。

**命题 79.2（一个 transverse algebraic intersection 不产生双 collision）。** supplier Theorem 2.2 的 actual acquired off-$24$ base $(p^*,v^*)$ 有 transverse、locally isolated common regular terminal-index zero，却不在 $D_J\cap D_M$。其原完整 child 有恰好三个 legal worlds，两个 terminal maps 各自 injective。

**证明。** 直接使用该定理的 complete three-world enumeration 与 strict-real lifting。构成 common index zero 的共同代数 label 违反 $b>0,0<r<1$；它不是实际 world。定理对整个 child（包括其 zero-safe branches）的穷尽性与两响应的 injectivity，排除了另一组合法 collision pairs。无需重现其 rational boxes、resultants 或 interval certificates。∎

**命题 79.3（在已取得 child 上的单次任务证书）。** 固定命题 79.2 的同一 actual base，令 $z$ 是其三个 legal worlds 的 branch label。若合同允许原 clock-seven $M$，实际取得其 paid response 并保留，且 source-independent 规则可判别 supplier 的三个不交 response intervals，则该 branch-label task 有一次动作的有限证书。这里没有新增 source port 或追加 counterfactual $J$。

**证明。** 固定 base 的三个候选 world 给出三个 pre-read complete states，加入这一次合法 $M$ 的实际 successor、response class 和 halt labels 就构成一个有限局部模型。其抽象只忘记与这一个任务无关的 fields；合法性和各实际 successor 逐候选保留，判别规则使用三个固定的 rational intervals，不依赖隐藏 world 选择动作。由 supplier injectivity，每个非空 response class 只有一个 $z$，故其 successor candidate relation 在 $\mathcal W_0$；读前的 union 在 $\mathcal W_1$。以读前/读后 rank $1/0$、实际 response update 和正确 halt label 得到 §62 的 chosen-action certificate。若计费用，其 actual branch cost 作为另行已声明的标签保留；三个固定候选上的标签仍只有有限多个。∎

这个应用取得的是固定 child 的 branch label；它不安装对任意 real $(p,v)$ 的 world enumerator，不假定有限 semantic candidates 已被读取，也不供应全局最小控制器。用于原任务时，已取得 $(p,v)$、exact read permission、response retention、source-independent 判别和 successor/cost 合同都是必要前提。反过来，一处 algebraic false lift 不排除其他 children 的合法 collisions。

**定义 79.4（未结算的 joint incidence）。** supplier §5.2 保留所有 $p\ne24,v$ 上 $D_J\cap D_M$ 的 real guarded decision：regular common components 与 isolated points 必须做 whole-world strict-real lifting；exceptional $E_0=0$ strata 还须 zero-safe reconstruction。每对内部 distinctness、每 label 的同一完整 $g$、singular sources、zero drift、repeated roots 和无界正 off-diagonal 均须保留。即使找到一处 positive child，也仍有同一 $p$ 的 sixth-$J$、fifth-$J$、common-parent 与 ancestor obligations，不能直接推出 $H_4$ 的 $L_3$、root $L_7$ 或 eight-versus-nine 结论。

## 八十、任务纤维的综合边界

**命题 80.1（任务充分性不等于统一行为或历史逆）。** 对上述声明的 source contracts，可分别使用 finite chosen-action certificate、current raw continuation kernel、terminal sharp-task signature 和 same-law quantitative estimates，但替换合同的任一步都须保留目标、支持、权限、更新及所数资源。具体有：native 的 current kernel 允许忘掉不影响 future behaviour 的 post-Capture chronology；算术 reached register 允许预测改变 endpoint 后的 quotient；sharp signature 允许合并对全部指定 projections 有同一像的 terminal histories；strict-real 的合法三-world child 允许一次声明读取得到 branch label。任何一个充分表示都不单独确定其他合同的 minimum 或逆。

**证明。** native 的反例和 singleton domain 是命题 74.2；算术使用约定 75.1–75.2 的两个不同 target times 与 supplier 的同步更新；terminal conclusion 是定理 76.2 和推论 76.3；局部取得是命题 79.3。它们分别使用不同的 source domain、可见信息与 target。要迁移一个协议，必须有保持这些数据的映射；仅由表示的存在不能补出缺失的读取或更新。命题 74.2 的两条实际历史还直接否定跨到 endpoint-only exact chronology 的迁移。∎

**定义 80.2（残余问题的范围）。** 仍待研究的是：unchanged native $A^+$ 的 whole-current joint-key acquisition 与各独立自然视图的 reverse kernels；$A_R$ 的完整 maintenance domain 和 current-at-return joint recovery；额外 chronology supplement 的实际取得与资源，而不是已被排除的全域 endpoint-only chronology inverse；给定动态任务与取得合同下的 controller optimum；§77.4 指定的 general quantitative sharp tasks 及共同 approximate decoder；§78.3 的原 subexponential/cutoff/collision-entropy 与 causal-memory goals；以及 §79.4 的 global strict-real joint incidence 和 ancestor obligations。

这里的承重组合是 prescribed-task signature 的 positive-support/terminal-partition 结论及固定 actual child 的 chosen-action 应用。一般 observable correction、native kernels 与历史逆、算术 parity acquisition、quantitative boundary optima、pair-energy obstruction 和 strict-real certificates 均按所引 supplier 的原范围使用。这些是普通论文数学与有条件 apparatus 定义，不提供新的物理服务实现、Lean kernel 认证或文献优先权结论，也不结算无界 horizon 的完整研究目标。

## 追加锚（本行以下为增补区）

## 81. 实际终端单任务的局部与联合误差几何

**定义 81.1（固定的输入、仪器与终端权限）。** 本节及 §§82–83 延续定义 77.1，令 $e=e_q,f=f_q$，使用同一 ordered basis $(\xi,e,f)$、$P=|\xi\rangle\langle\xi|$ 与 actual fair independent chronological channel $\mathcal N_n=F^n$。每个实际历史仍按 $V_{h_n}\cdots V_{h_1}$ 执行；擦除后平均为 $F^n$ 不改变历史顺序。令

$$
E(q)=|v_q\rangle\langle v_q|,\qquad
v_q=\sqrt{1-q}\,\xi+\sqrt q\,e,\qquad 0\le q\le1,
\qquad \eta_n(q)=\eta_n(E(q)).
$$

这里 $q$ 是任务方向，history law 始终为 $2^{-n}$。decoder 是按任务与 horizon 预先选择、与未知输入无关的一个 terminal complex qutrit CPTP map。误差在全部 $\rho\in\mathsf D(\mathbb C^3)$ 上取 supremum，等于 recovered effect 与 target 的 Hermitian operator-norm distance。没有 history/reference access、较小 input code、intermediate correction、postselection 或额外 summary。

本节唯一使用的 effect interface 是 [Environment §27，Proposition 27.2 与 (27.4)–(27.7)][F81ENV27]，即约定 77.2 的整个 complex interval $C=G_s(K_2\oplus d)$，$0\le K_2\le I_2,0\le d\le1$，不是仅挑选一个 real ansatz。有限 $n\ge1$ 时记

$$
s=(-1/2)^{n-1},\quad t=|s|=2^{1-n},\quad
\alpha=(1+s)/2,\quad\beta=(1-s)/2.
$$

每个所构造的 effect 都经 supplier 的 $B=U_0(K_2\oplus d)U_0^\dagger$ 与 (27.5) 实现一个该模型允许的 CPTP decoder；该接口的证明不再重复。一个任务的 effect right inverse 不供应多个任务的共同 decoder。

**定理 81.2（先固定 horizon 的尖锐一阶律）。** 对每个固定整数 $n\ge2$，

$$
\eta_n(q)=(t^{-2}-1)q+o_n(q)
          =(4^{n-1}-1)q+o_n(q),\qquad q\downarrow0.
$$

更具体地，设 $h=\sqrt{q(1-q)}$、$A=t^{-2}-1$。对 $0\le q\le1$ 有

$$
\eta_n(q)\ge\max\{0,L_t(q)\},\qquad
L_t(q)=h+\frac{t^2}{2}-\frac t2\sqrt{t^2+4(h+q)}.
$$

对 $0<q<t^2$ 有

$$
\eta_n(q)\le Aq+
\frac{Aq^{3/2}}{\sqrt{1-q}+\sqrt{1-q/t^2}}.
$$

**证明。** 对任意 complex feasible $K_2=\left(\begin{smallmatrix}x&z\\\overline z&y\end{smallmatrix}\right)$ 与 $d$，令 $\epsilon=\|G_s(K)-E(q)\|_{\rm op}$。矩阵元界及 $I_2-K_2\ge0$ 给出

$$
x\ge1-q-\epsilon,\quad |sz-h|\le\epsilon,\quad
|z|^2\le(1-x)(1-y)\le q+\epsilon.
$$

故 $(h-\epsilon)_+^2\le t^2(q+\epsilon)$。当 $\epsilon\ge h$，所需下界立即成立；当 $\epsilon<h$，解二次不等式得 $\epsilon\ge L_t(q)$，因为其另一根大于 $h$。这覆盖全部 complex effects。将小根有理化，

$$
L_t(q)=\frac{q(1-q-t^2)}
 {h+t^2/2+(t/2)\sqrt{t^2+4(h+q)}}.
$$

对上界取 $d=0$ 与 rank-one projection $K_2=uu^\dagger$，其中

$$
u=\begin{pmatrix}\sqrt{1-q/t^2}\\ \operatorname{sgn}(s)\sqrt{q/t^2}\end{pmatrix}.
$$

残余对角为 $(-Aq,(\alpha/t^2-1)q,\beta q/t^2)$，仅有的 off-diagonal residual 的模为

$$
w=h-\sqrt{q(1-q/t^2)}
 =\frac{Aq^{3/2}}{\sqrt{1-q}+\sqrt{1-q/t^2}}.
$$

实际 $n\ge2$ 满足 $-1/2\le s\le1/4$，从而
$\alpha-t^2=(1-s)(1+2s)/2\ge0$；三个对角绝对值均不超过 $Aq$。三角不等式得上界。固定 $t>0$ 后，$L_t(q)/q\to A$ 且 $w/q\to0$，故两界夹出结论。∎

**命题 81.3（trace balance 会删去更好的实际 effects）。** 在 $n=2$ 令 $\ell=(y+3d)/4$，并把 $x+\ell=1$ 强加于 supplier 的 feasible effects；记该受限最优值为 $\eta_{\rm tb}(q)$。对每个 $0<q\le1/10000$，

$$
\eta_2(q)\le\frac{199}{66}q<\frac{10}{3}q<\eta_{\rm tb}(q),
\qquad \eta_{\rm tb}(q)-\eta_2(q)>\frac7{22}q.
$$

**证明。** 取 $d=0$，

$$
K_2=\begin{pmatrix}
1-4q&-2\sqrt{q(1-4q)}\\
-2\sqrt{q(1-4q)}&4q
\end{pmatrix}.
$$

它是 rank-one projection。$G_{-1/2}(K)-E(q)$ 为
$\left(\begin{smallmatrix}-3q&-w\\-w&0\end{smallmatrix}\right)\oplus3q$，其中

$$
w=\frac{3q\sqrt q}{\sqrt{1-q}+\sqrt{1-4q}}<\frac q{66}.
$$

最后一步用 $\sqrt q\le1/100$ 且分母两项均大于 $99/100$。故 unrestricted error 小于 $199q/66$。

反之对任何满足 trace balance 的 complex effect，positivity 给出

$$
|z|^2\le\min\{(1-\ell)y,\ell(1-y)\}\le\min(y,\ell).
$$

$f$ residual 为 $c=(3y+d)/4=(2y+\ell)/3\ge\min(y,\ell)$。若其误差不超过 $\delta=10q/3$，则 $c\le\delta$，且
$h\le\delta+|z|/2\le\delta+\sqrt\delta/2$。除以 $\sqrt q$ 得

$$
\sqrt{1-q}\le\frac{10}{3}\sqrt q+\sqrt{5/6}
 \le\frac1{30}+\frac{11}{12}=\frac{19}{20},
$$

与 $\sqrt{1-q}>99/100$ 矛盾。受限 effect set 非空（含 $I_3/2$）且 compact，故最小值严格大于 $\delta$。系数差为 $7/22$。∎

**定理 81.4（$n=2$ 的 admissible small-$q$ exact branch）。** 对每个实数 $0<q\le1/1000$，多项式

$$
\mathscr P_q(R)=16q(1-q)(5R^2-8)^2
 -(R^2-1)(4-R^2)(3R-4+20q)^2
$$

在下列 admissible domain 中恰有一根：

$$
1<R\le21/20,\qquad
0\le d(R,q)\le y(R)/3,\qquad
y=\frac{(R-1)(2-R)}{6R},\quad
d=\frac{24q-R(R-1)(2-R)}{2(5R^2-8)}.
$$

在此根上，令

$$
\vartheta=\frac{R^2-1}{3},\quad
\gamma=\sqrt{\vartheta(1-\vartheta)},\quad
w=\frac\gamma{2R},\quad
Q_\vartheta=\begin{pmatrix}1-\vartheta&\gamma\\\gamma&\vartheta\end{pmatrix},
\quad K_2=\begin{pmatrix}1-y&-w\\-w&y\end{pmatrix},\quad
\eta=\frac{3y+d}{4}.
$$

则 $K_2$ 是 rank-one orthogonal projection，$0<d<y/3$，且

$$
\eta_2(q)=\eta,\qquad
G_{-1/2}(K_2\oplus d)-E(q)
 =[-\eta Q_\vartheta+d(I_2-Q_\vartheta)]\oplus\eta.
$$

这是全部 complex effects 上唯一的 reduced optimizer $K_2\oplus d$；不声称 decoder 唯一。其 residual spectrum 为 $(-\eta,d,\eta)$，$\xi,e$ block trace 为 $-3(y-d)/4<0$。当 $q\downarrow0$，

$$
y=4q-84q^2+O(q^3),\qquad d=108q^2+O(q^3),\qquad
\eta_2(q)=3q-36q^2+O(q^3).
$$

**证明。** 先让 $R\in[1,21/20]$，将 $d$ 作为变量，定义

$$
\widetilde E(R,d)=G_{-1/2}(K_2\oplus d)_{\xi,e}
       -dI_2+\left(\frac{3y+d}{4}+d\right)Q_\vartheta.
$$

直接展开发现 $w^2=y(1-y)$、$\operatorname{Tr}\widetilde E=1$，并且

$$
\begin{aligned}
Q(R,d)&=\widetilde E_{ee}
 =\frac{R(R-1)(2-R)}{24}+\frac{5R^2-8}{12}d,\\
H(R,d)&=\widetilde E_{\xi e}=\frac{\gamma(3-R+10d)}8,\\
16\det\widetilde E&=C_R+B_Rd-A_Rd^2,\\
A_R&=5R^2-4,\quad B_R=3R^3+R^2-4R-4,\quad
C_R=(R-1)^2(4-R^2)/4.
\end{aligned}
$$

当 $R>1$，$A_R,C_R>0$，故 determinant 恰有一个正根

$$
d_R=\frac{B_R+\sqrt{B_R^2+4A_RC_R}}{2A_R},
$$

它连续延伸到 $d_1=0$。整个区间上 $\vartheta\le41/1200$、$y\le\vartheta/4$；在 $d=y/3$ 有

$$
Q=\frac{y(1+7\vartheta)}6,\qquad
H-w/2=\frac{7\gamma(2-R)(R-1)}{36R}\ge0.
$$

于是

$$
\det\widetilde E\le Q-w^2/4
 =\frac{y(-1+14\vartheta+3y)}{12}<0,
\qquad14\vartheta+3y\le2419/4800<1.
$$

$d=0$ 时 determinant 为 $C_R/16>0$，所以 $0<d_R<y/3$。
$\widetilde E(R,d_R)$ trace 一、determinant 零且 off-diagonal 正，故恰为 $E(Q(R,d_R))$ 的 $\xi,e$ block。函数 $Q(R,d_R)$ 连续，起点为零，且

$$
Q(R,d_R)=\frac{y-d_R}{4}+\frac{3y+5d_R}{4}\vartheta>y/6,
\qquad Q(21/20,d_{21/20})>19/15120>1/1000.
$$

中间值定理给出每个声明的 $q$，无需假设 monotonicity。构造立即给出 residual identity，且 $\eta>d$，所以其 norm 为 $\eta$。

为对全部 complex effects 给出 lower certificate，取

$$
Y=\frac{Q_\vartheta\oplus(-3\vartheta)}{R^2},\qquad \|Y\|_1=1.
$$

对任意 competing $K'_2\oplus d'$，$d'$ 的 pairing 系数消去，并有

$$
\operatorname{Tr}(YG_{-1/2}(K'))=\operatorname{Tr}(M_RK'_2),\qquad
M_R=\frac1{R^2}\begin{pmatrix}1-\vartheta&-\gamma/2\\-\gamma/2&-2\vartheta\end{pmatrix}
 =m_+K_2+m_-(I_2-K_2),
$$

其中 $m_+=(2-R)(R+1)/(2R^2)>0$，$m_-=(1-R)(R+2)/(2R^2)<0$。在 $M_R$ eigenbasis 中，effect 的对角元在 $[0,1]$，所以此 pairing 不超过 $m_+$；等号迫使两个对角元为 $1,0$，positivity 再迫使 complex off-diagonal 为零。因此 support maximizer 唯一为 $K_2$。由标准 trace/operator-norm duality，

$$
\|E(q)-G_{-1/2}(K')\|_{\rm op}
 \ge\operatorname{Tr}(YE(q))-m_+=\eta.
$$

构造的 residual 达到等号。任何 optimizer 都必须有 $K'_2=K_2$；又因 $Y$ 的正 $Q_\vartheta$ 权和负 $f$ 权均非零，norm 等号迫使 $f$ residual 等于 $\eta$，即 $(3y+d')/4=\eta$，所以 $d'=d$。这是弱对偶与 equality case 的直接证明，不需要假设 strong duality。

由 $Q(R,d)=q$ 解得陈述中的 $d(R,q)$，分母在区间上满足 $5R^2-8\le-199/80<0$。代入得

$$
H(R,d(R,q))=\frac{3\gamma(3R-4+20q)}{4(5R^2-8)},\qquad
16(5R^2-8)^2[q(1-q)-H^2]=\mathscr P_q(R).
$$

整个 rectangle 上 $3R-4+20q\le-83/100<0$，故 $H>0$，平方没有混入反号 target。每个 admissible root 都重建同一 $E(q)$ 并取得上述证书；reduced optimizer 唯一且 $y'(R)=(2/R^2-1)/6>0$，故 admissible root 唯一。不排除 domain 之外的其他实根。

最后令 $h_R=R-1$。在 $(R,d)=(1,0)$，determinant polynomial 对 $d$ 的导数为 $-4$。解析隐函数及逆函数定理给出

$$
d_R=3h_R^2/16+13h_R^3/64+O(h_R^4),\quad
q=h_R/24-3h_R^2/64+O(h_R^3),\quad
h_R=24q+648q^2+O(q^3),
$$

代回得三个 expansions。每个构造均由定义 81.1 的 supplier decoder 实现；也可将 (27.5) 的 prepared states 取为 $E(q)$ 与 $|f\rangle\langle f|$。在 $q=0$ 连续取 $R=1,y=w=d=\eta=0$ 达到零，但本定理不在该端点声称 optimizer 唯一。∎

**定理 81.5（单任务的 joint cubic profile）。** 令 $t_n=2^{1-n}$。对每个固定 $\kappa\ge0$，在 $q_n=\kappa t_n^4\le1$ 的最终整数尾段上，两个 parity subsequences 均满足

$$
\frac{\eta_n(q_n)}{t_n^2}\longrightarrow
\mathcal L(\kappa)=\min_{z\ge0}\sqrt{z^4+(z-\sqrt\kappa)^2}
 =z_\kappa^2\sqrt{1+4z_\kappa^2},\qquad
2z_\kappa^3+z_\kappa=\sqrt\kappa.
$$

对固定 $K\ge0$、$n\ge2$ 且 $Kt_n^2\le1$，还有 compact-$\kappa$ bound

$$
\sup_{0\le\kappa\le K}
\left|\frac{\eta_n(\kappa t_n^4)}{t_n^2}-\mathcal L(\kappa)\right|
 \le(K+2K^{3/2})t_n^2.
$$

**证明。** 写 $t=t_n$、$a=\sqrt\kappa$。对任意 feasible complex $K_2=\left(\begin{smallmatrix}x&w\\\overline w&y\end{smallmatrix}\right)$，置 $A_0=(1-x)/t^2$、$Z=\operatorname{sgn}(s)w/t$。由 $I-K_2\ge0$ 得 $|Z|^2\le A_0(1-y)\le A_0$。scaled residual 的第一列是

$$
(-A_0+\kappa t^2,\ \overline Z-a\sqrt{1-\kappa t^4},\ 0)^{\mathsf T}.
$$

矩阵 norm 至少为列 norm，所以其不小于
$\sqrt{A_0^2+|Z-a|^2}-\delta_n\ge\mathcal L(\kappa)-\delta_n$，其中

$$
\delta_n=\sqrt{\kappa^2t^4+\kappa(1-\sqrt{1-\kappa t^4})^2}.
$$

这里用 $|Z-a|\ge||Z|-a|$，没有限制 complex optimizer。

对上界，任取 $z\ge0$ 且 $u=z^2t^2\le1$，令

$$
K_2=\begin{pmatrix}1-u&\operatorname{sgn}(s)zt\sqrt{1-u}\\
\operatorname{sgn}(s)zt\sqrt{1-u}&u\end{pmatrix},\qquad d=u.
$$

这是 rank-one block 加合法 scalar effect。scaled residual 对角为
$(-z^2+\kappa t^2,z^2-\kappa t^2,z^2)$，off-diagonal 为
$z\sqrt{1-z^2t^2}-a\sqrt{1-\kappa t^4}$。其 norm 趋向 $\sqrt{z^4+(z-a)^2}$，并经 supplier 的一个单任务 decoder 达到。函数 $z^4+(z-a)^2$ 的二阶导数为 $12z^2+2>0$，所以唯一非负 minimizer 满足所列 cubic；在根上 $a-z=2z^3$，得 $\mathcal L$ 的闭式。

为得 quantitative bound，$z_\kappa\le\sqrt\kappa$，故当 $Kt^2\le1$ 时所有这些 upper effects 都 feasible。用 $1-\sqrt{1-v}\le v$，lower perturbation 不超过 $(K+K^{3/2})t^2$；upper diagonal perturbation 不超过 $Kt^2$，off-diagonal perturbation 不超过
$z_\kappa^3t^2+\kappa^{3/2}t^4\le2K^{3/2}t^2$。两侧取较大常数即得结论。$\kappa=0$ 时全部值恰为零。∎

**约定 81.6（适用域与中间工具）。** 定理 81.2 先固定 $n$；不能把随 $n$ 增长的 $t^{-2}$ 系数直接代入 joint scale。定理 81.5 有独立的 moving-horizon proof，且 compact bound 不统一于无界 $\kappa$。定理 81.4 只解 $n=2,0<q\le1/1000$；它没有给出更大 $q$、其他 active sets、$n\ge3$ 的 finite-$q$ root rule 或 interior $p,q,r>0$ 的一般 optimum。

承重推导使用标准 convex support duality、Hermitian norm duality、解析隐函数定理与 supplier 的 observable-correction interface；一般 simultaneous observable correction 的先例为 [Bény–Kempf–Kribs 的现有文献条目](../../../Library/Quantum/benykempfkribs2007observables.md)。这些成熟中间工具不承担本节具体 branch、admissible interval 或 joint constants 的数值结论。

## 82. 同一个 CPTP decoder 的耦合约束

**定义 82.1（共同终端目标）。** 在定义 81.1 的同一 source 与权限下，令

$$
\begin{aligned}
L_{n,\mathcal D}(A)&=\|(F^n)^\dagger\mathcal D^\dagger(A)-A\|_{\rm op},\\
c_n(q)&=\min_{\mathcal D\ {\rm CPTP}}
       \max\{L_{n,\mathcal D}(P),L_{n,\mathcal D}(E(q))\}.
\end{aligned}
$$

两个 losses 必须来自同一个 complex CPTP map，不要求 exact preservation of $P$。有限维 Choi set $\{J\ge0:\operatorname{Tr}_{\rm out}J=I_3\}$ compact、convex、非空，且目标连续，故此 minimum 及下文的 finite common minima 均达到。这是标准 Choi/Kraus representation 的应用，见 [Watrous，Theorems 2.22、2.26 与 Corollary 2.27 的现有条目](../../../Library/Quantum/watrous2018theory.md)。

**定理 82.2（fixed-horizon common law）。** 对每个固定整数 $n\ge2$，

$$
c_n(q)=\frac{1-t}{2}\sqrt q+O_n(q),\qquad q\downarrow0.
$$

$n=1$ 时 $c_1(q)=0$ 对所有 $q\in[0,1]$ 成立。特别在 $n=2$，对全部 $q\in[0,1]$ 有

$$
\frac{\sqrt q}{2}\left(\sqrt{1-q}-\frac12\right)
 \le c_2(q)\le\frac{\sqrt q}{4}+\frac{13q}{4},
\qquad c_2(q)=\frac{\sqrt q}{4}+O(q).
$$

后一个 lower bound 在 $q\ge3/4$ 时不提供正信息。

**证明。** 对 Hermitian $X$，unital positive maps 保持 order interval $[-\|X\|I,\|X\|I]$，所以 contract operator norm。由 supplier 的 linear $G_s$ formula，

$$
\left|\big((F^n)^\dagger\mathcal D^\dagger(X)\big)_{\xi e}\right|
 \le t\|X\|_{\rm op}.
$$

令 $H_q=E(q)-P$，则 $H_q^2=q(P+|e\rangle\langle e|)$，所以 $\|H_q\|_{\rm op}=\sqrt q$。写两个 residuals 为 $R_P,R_E$，由同一 map 的线性性，

$$
2\max(\|R_P\|,\|R_E\|)
 \ge|(R_E-R_P)_{\xi e}|
 \ge\sqrt{q(1-q)}-t\sqrt q.
$$

这给出所有 complex decoders 的 lower bound。

对 fixed-$n$ upper bound，令 $\theta_q=\arcsin\sqrt q$、$\sigma=\operatorname{sgn}(s)$、$b=(1-t)/(2s)$、$\phi=b\theta_q$，在 $(\xi,e)$ plane 取

$$
V=\begin{pmatrix}\cos\phi&-\sigma\sin\phi\\
\sin\phi&\sigma\cos\phi\end{pmatrix}\oplus1,
\qquad \mathcal D=\operatorname{Ad}_{V^\dagger U_0^\dagger}.
$$

这是两个任务共用的一个 unitary CPTP decoder。其 adjoint 为 $\operatorname{Ad}_{U_0V}$，因此 supplier 中的 $K$ 分别为 $VPV^\dagger$ 与 $VE(q)V^\dagger$；它们均与 $W$ 交换，且 $d=0$。两个 rank-one directions 的角度为 $\gamma_P=b\theta_q$ 与 $\gamma_E=(b+\sigma)\theta_q$。恢复后的 $\xi e$ entry 是 $s\sin\gamma\cos\gamma$，对角为 $(\cos^2\gamma,\alpha\sin^2\gamma,\beta\sin^2\gamma)$。由于

$$
s\gamma_P=\frac{1-t}{2}\theta_q,\qquad
s\gamma_E-\theta_q=-\frac{1-t}{2}\theta_q,
$$

且 $|\sin\gamma|\le|\gamma|$、$|\sin\gamma\cos\gamma-\gamma|\le2|\gamma|^3/3$，两个全 qutrit residual norms 分别不超过

$$
\begin{aligned}
&\frac{1-t}{2}\theta_q+b^2\theta_q^2+\frac{2t|b|^3}{3}\theta_q^3,\\
&\frac{1-t}{2}\theta_q+[1+(b+\sigma)^2]\theta_q^2
 +\frac23[t|b+\sigma|^3+1]\theta_q^3.
\end{aligned}
$$

固定 $n$ 后这些常数有限，$\theta_q=\sqrt q+O(q^{3/2})$，得 matching upper asymptotic。$n=1$ 时取 $V=I$；两个 tasks 与 $W$ 交换，$\mathcal D=\operatorname{Ad}_{U_0^\dagger}$ 同时精确恢复它们。

在 $n=2$ 可给出上述全区间 sandwich。此时 $V$ 的 $2\times2$ block 为
$\left(\begin{smallmatrix}\cos a&\sin a\\\sin a&-\cos a\end{smallmatrix}\right)$，$a=-\theta_q/2$。置 $k=\sqrt{1-q}$，

$$
y_0=\frac{q}{2(1+k)},\qquad
y_3=\frac{q(1+2k)^2}{2(1+k)}\le\frac94q.
$$

同一个 decoder 的两个 residuals 恰为

$$
R_P=\begin{pmatrix}-y_0&\sqrt q/4&0\\\sqrt q/4&y_0/4&0\\0&0&3y_0/4\end{pmatrix},\quad
R_E=\begin{pmatrix}q-y_3&b_q&0\\b_q&y_3/4-q&0\\0&0&3y_3/4\end{pmatrix},
\quad b_q=-\sqrt q\,[1/4+k(1-k)].
$$

$9q/4-y_3=q(1-k)(8k+7)/[4(1+k)]\ge0$，且 $k(1-k)\le q$。因此 $\|R_P\|\le\sqrt q/4+q/2$，$\|R_E\|\le\sqrt q/4+q^{3/2}+9q/4\le\sqrt q/4+13q/4$。lower bound 由前式置 $t=1/2$ 得到。∎

**命题 82.3（附加 exact-$P$ 条件的不同障碍）。** 若 $n\ge2$ 且同一个 decoder 满足 $(F^n)^\dagger\mathcal D^\dagger(P)=P$，则

$$
L_{n,\mathcal D}(E(q))\ge(1-t)\sqrt{q(1-q)}.
$$

这不是定义 82.1 的 minimax lower bound。

**证明。** 令 $\Psi=\operatorname{Ad}_{U_0^\dagger}\circ\mathcal D^\dagger$，$B=\Psi(P)$。由 $G_s(\Delta_W B)=P$，$x=1$，且因 $\alpha,\beta>0$，$y=d=0$。$0\le B\le I$ 的零对角及单位对角迫使相应 off-diagonals 全为零，故 $B=P$。unital CP map 将 projection $P$ 映为 projection $P$ 时，$P$ 属于其 multiplicative domain：$\Psi(PX)=P\Psi(X)$、$\Psi(XP)=\Psi(X)P$。这一标准 CP equality case 也可由 Stinespring isometry $V_\Psi$ 直接看出：
$P\otimes I$ 与 $V_\Psi$ 的 intertwining 来自两侧 complementary projection 的零 norm。

于是 $\Psi(P)$ 与 $\Psi(|e\rangle\langle e|)$ 都不贡献 $\xi e$ entry。对 $X=|\xi\rangle\langle e|+|e\rangle\langle\xi|$，$\|X\|=1$，norm contraction 给出 $|\Psi(X)_{\xi e}|\le1$。因此 recovered $E(q)$ 的该 entry 的模至多 $th$，其 target entry 是 $h=\sqrt{q(1-q)}$，得结论。∎

在 $n=2$，这个 conditional bound 的 leading coefficient 为 $1/2$，而定理 82.2 的 unconstrained common coefficient 为 $1/4$；后者允许 $P$ 有正误差。两者均不确定一般 finite-$q$ common optimum。

**定理 82.4（same-decoder joint profile 与 $\kappa=2$ 分支）。** 对固定 $\kappa\ge0$，$a=\sqrt\kappa$，在 $q_n=\kappa t_n^4\le1$ 的最终尾段上，

$$
\frac{c_n(q_n)}{t_n^2}\longrightarrow\mathcal H(\kappa)
 =\min_{z\ge0}\sqrt{z^4+\max\{z^2,(z-a)^2\}}.
$$

两个 parity subsequences 具有同一 limit，唯一 scalar minimizer 为
$z_* =\min\{a/2,z_\kappa\}$，且

$$
\mathcal H(\kappa)=
\begin{cases}
\dfrac{\sqrt\kappa}{2}\sqrt{1+\kappa/4},&0\le\kappa\le2,\\
\mathcal L(\kappa),&\kappa\ge2.
\end{cases}
$$

特别 $\mathcal H(0)=0$，$\mathcal H(2)=\sqrt3/2$。第二分支仅是 leading-profile equality，不是 finite-$n$ simultaneous individual optimality。

**证明。** $a=0$ 时 $E=P$，identity decoder 精确恢复，故以下设 $a>0$。用 identity decoder 与 norm contraction 得
$c_n(q)\le2\|E(q)-P\|=2at^2$。取达到 minimum 的同一个 $\mathcal D$，记 $\epsilon=c_n(q)$、$\Psi=\operatorname{Ad}_{U_0^\dagger}\circ\mathcal D^\dagger$、$B=\Psi(P)$。$P$ loss 不超过 $\epsilon$ 意味着

$$
1-B_{\xi\xi}\le\epsilon,\qquad B_{ee}+B_{ff}\le2\epsilon.
$$

对各 basis vector $i$，$\omega_i(X)=\langle i|\Psi(X)|i\rangle$ 是 positive unital functional。令 $A=|\xi\rangle\langle e|$、$P_e=|e\rangle\langle e|$。其 Cauchy–Schwarz inequality 及 $P+P_e\le I$ 给出

$$
|\Psi(A)_{ii}|^2\le\omega_i(P)\omega_i(P_e)
 \le B_{ii}(1-B_{ii})\le2\epsilon.
$$

因此 $\Psi(H_q)$ 的每个 diagonal 绝对值不超过
$q+2h\sqrt{2\epsilon}$。$G_s$ 仅 convexly 混合 $e,f$ diagonals，保留的 off-diagonal 由 norm contraction 不超过 $t\sqrt q$。对于这个同一个 map，

$$
\begin{aligned}
\Delta&=(F^n)^\dagger\mathcal D^\dagger(H_q),\\
\|\Delta\|&\le q+2h\sqrt{2\epsilon}+t\sqrt q
 \le a^2t^4+(4a^{3/2}+a)t^3=o(t^2).
\end{aligned}
$$

所以 $C_E=C_P+\Delta=C_P+o(t^2)$；这一步不是两个独立 effects 的拼合。

写 $\Delta_W B=\left(\begin{smallmatrix}x&w\\\overline w&y\end{smallmatrix}\right)\oplus d$，置 $A_0=(1-x)/t^2$、$Z=\operatorname{sgn}(s)w/t$，则 $|Z|^2\le A_0$。两个 scaled residuals 的第一列分别为
$(-A_0,\overline Z,0)^{\mathsf T}$ 与
$(-A_0,\overline Z-a,0)^{\mathsf T}$ 加上 norm 不超过

$$
\delta_n=\|\Delta\|/t^2+a^2t^2+a(1-\sqrt{1-a^2t^4})\longrightarrow0
$$

的扰动。故

$$
\frac\epsilon{t^2}\ge
\sqrt{A_0^2+\max\{|Z|^2,|Z-a|^2\}}-\delta_n
 \ge\mathcal H(\kappa)-\delta_n.
$$

此界对 chosen minimizers uniform，未假设它们收敛，亦未限制 complex phases。

为实现 matching upper，给定 $z\ge0$，取定理 81.5 的 $K_2$ 与 $d=u=z^2t^2$，令 $B=U_0KU_0^\dagger$，但现在固定 prepared states 为 $P$ 与 $(I-P)/2$：

$$
\mathcal D_B(X)=\operatorname{Tr}(BX)P
       +\operatorname{Tr}((I-B)X)(I-P)/2.
$$

这是供两个 tasks 共用的一个 CPTP decoder。其 adjoint 同时满足

$$
\mathcal D_B^\dagger(P)=B,\qquad
\mathcal D_B^\dagger(E(q))=(1-3q/2)B+(q/2)I.
$$

于是 $C_E=(1-3q/2)C_P+(q/2)I$，$\|C_E-C_P\|\le q$，两个 scaled residuals 分别趋向

$$
\begin{pmatrix}-z^2&z\\z&z^2\end{pmatrix}\oplus z^2,
\qquad
\begin{pmatrix}-z^2&z-a\\z-a&z^2\end{pmatrix}\oplus z^2.
$$

取两者 norm 的最大值并置 $z=z_*$ 即给 matching limsup。

最后在 $z\ge a/2$ 上 squared objective 为严格递增的 $z^4+z^2$；在 $[0,a/2]$ 上为严格凸的 $z^4+(z-a)^2$。故唯一 minimizer 是 $\min(a/2,z_\kappa)$。条件 $z_\kappa\ge a/2$ 等价于 $a^2\le2$；在 $a^2=2$ 两式均为 $\sqrt3/2$。∎

**约定 82.5（不交换量词）。** 定理 82.2 的 constants 含 $1/s$，不统一于 $n$；定理 82.4 另由 same-map CP coupling 证明。该 joint theorem 只固定 $\kappa$，不声称 compact-$\kappa$ remainder 与定理 81.5 相同。所给 decoders 是模型内明确的 unitary 或 measure-and-prepare channels；这些数学 realizations 不证明外部装置已提供其操作，也不计算量子存储维数、online controller memory 或 paid physical ports。

## 83. 共同 decoder 的任务纤维与有限不相容见证

**定理 83.1（phase family 的 optimal-image separation）。** 固定 $n=2$、$0<q\le1/1000$，令

$$
E_\varphi(q)=|\sqrt{1-q}\,\xi+e^{i\varphi}\sqrt q\,e\rangle
 \langle\sqrt{1-q}\,\xi+e^{i\varphi}\sqrt q\,e|,
\qquad \varphi\in\mathbb R/(2\pi\mathbb Z).
$$

它们的 individual optima 均为定理 81.4 的 $\eta$。每个任务的 optimal recovered image 唯一为

$$
C_\varphi=Z_\varphi G_{-1/2}(K_0)Z_\varphi^\dagger,\quad
Z_\varphi=\operatorname{diag}(1,e^{i\varphi},1),\quad
K_0=\begin{pmatrix}1-y&-w\\-w&y\end{pmatrix}\oplus d,
\quad (C_\varphi)_{\xi e}=\frac w2e^{-i\varphi}.
$$

任意两个不同 phases 没有一个共同 CPTP decoder 同时达到这两个 individual optima。因此对 $N\ge1$ 个不同 phases，若一个已供应的 deterministic task label 仅用于从固定 terminal decoder dictionary 选一个 decoder，并要求每个任务恰达到 individual optimum，则最少恰需 $N$ 个 labels。

**证明。** $G_s$ 与 $Z_\varphi$ 的 conjugation 交换，后者保持整个 effect interval；这是 supplier Proposition 27.2 的 attainable-set invariance，并非 $F$ 的 covariance。故定理 81.4 的 optimum、optimizer 与 dual certificate 都逐 phase conjugate，给出所列 unique image。令 $B_\varphi=U_0Z_\varphi K_0Z_\varphi^\dagger U_0^\dagger$，以 $E_\varphi$ 与 $|f\rangle\langle f|$ 为 prepared states 的 supplier map 达到该 optimum。

令 $h=\sqrt{q(1-q)}$。定理 81.4 的 residual identity 给出

$$
h=w/2+(\eta+d)\gamma=\gamma(3-R+10d)/8,
\qquad \frac wh=\frac4{R(3-R+10d)}.
$$

由 $\vartheta\le41/1200$、$y\le\vartheta/4$、$d<y/3$，

$$
0<R(3-R+10d)<\frac{21}{20}\left(2+\frac{41}{1440}\right)
 =\frac{20447}{9600}<4,
\qquad w/h>1.
$$

对不同 $\varphi,\psi$，置 $a_{\varphi\psi}=|e^{-i\varphi}-e^{-i\psi}|>0$。$H=E_\varphi-E_\psi$ 的 eigenvalues 为 $ha_{\varphi\psi},-ha_{\varphi\psi},0$，故 $\|H\|=ha_{\varphi\psi}$。任何同一个 CPTP decoder 满足

$$
\left|\big((F^2)^\dagger\mathcal D^\dagger(H)\big)_{\xi e}\right|
 \le\frac12\|\mathcal D^\dagger(H)\|
 \le\frac12ha_{\varphi\psi}.
$$

若它对两个 tasks 都 individually optimal，unique image 与线性性却要求该 entry 的模为 $wa_{\varphi\psi}/2$，矛盾。因此每个 dictionary label fibre 至多含一个 phase；逐任务使用上面的 attaining map 则 $N$ labels 足够。这里没有 decoder uniqueness 结论。∎

**推论 83.2（固定 finite catalogue 的正 slack margin）。** 对定理 83.1 中固定 $q$ 与固定 $N\ge2$ 个不同 phases，存在 $\delta_*>0$，使得只要 $0\le\delta<\delta_*$，要求每个任务的 error 不超过 $\eta+\delta$ 仍恰需 $N$ 个 dictionary labels。

**证明。** 对每一 pair 定义

$$
\delta_{ij}=\min_{\mathcal D\ {\rm CPTP}}
 \max\{L_{2,\mathcal D}(E_{\varphi_i})-\eta,
         L_{2,\mathcal D}(E_{\varphi_j})-\eta\}.
$$

两个 terms 均非负；compact Choi set 上 minimum 达到。若 $\delta_{ij}=0$，同一 minimizer 就违反定理 83.1，故 $\delta_{ij}>0$。有限个 pairs 的 minimum $\delta_*$ 为正。若某 label 含两个 tasks 且都达到阈值 $\eta+\delta$，则 $\delta_{ij}\le\delta<\delta_*$，矛盾。individual optimal maps 给出 matching sufficiency。∎

$\delta_*$ 依赖整个 finite catalogue 与 $q$；此证明不给出 uniform phase-separation-free margin、$q\downarrow0$ margin 或一般 positive-slack capacity。$q=0$ 时所有 phases 是同一 $P$，一个 decoder 达到零。若另外规定 labels 用长度 $\ell$、禁止相邻 $11$ 的 data words 编码，前置固定 seam $0$ 不计入 $\ell$ 且无其他端点条件，则仅该静态编码的可用 word 数为 $F_{\ell+2}$，故条件为 $F_{\ell+2}\ge N$。这是 §76 的同一 Fibonacci counting，未计任务取得或在线更新。

**定义 83.3（实际 common image 中的 feasible task fibres）。** 对一个固定 finite $n\ge1$，令 $T_n=(F^n)^\dagger$ 作用于 real Hermitian space $\mathcal H_3$。给定 finite task catalogue $A_1,\ldots,A_N\in\mathcal H_3$ 与各阈值 $\epsilon_i\ge0$，定义

$$
\mathscr K=\left\{J\subseteq\{1,\ldots,N\}:\quad
 \exists\mathcal D\ {\rm CPTP},\quad
 \|T_n\mathcal D^\dagger(A_i)-A_i\|_{\rm op}\le\epsilon_i
 \text{ for every }i\in J\right\}.
$$

$\varnothing\in\mathscr K$，且该 family 向下封闭。其 source 仍为全部 qutrit densities，decoder 仍按固定 tasks 与 horizon 选择；对 Hermitian $A_i$，loss 是 absolute expectation error，只有当 $A_i$ 为 effect 时才是 event-probability error。定义中一个 fibre 只享有一个共同 map。

**定理 83.4（实际 rank-five image 的 bounded incompatibility）。** 在定义 83.3 下，令

$$
S=\operatorname{span}_{\mathbb R}\{I_3,A_1,\ldots,A_N\},\qquad
m=\dim_{\mathbb R}S-1\le8.
$$

每个不属于 $\mathscr K$ 的 finite task set 都含一个不属于 $\mathscr K$ 的非空 subset，其大小不超过 $5m+1\le41$。因此整个 catalogue feasible 当且仅当其每个大小至多 $5m+1$ 的 subset feasible，后者允许对不同 subsets 选择不同 decoders，但始终使用原来同一个 $S,T_n,A_i,\epsilon_i$。

对 fixed-$q$ phase family，单独的 $E_\varphi(q)$ 可取 $m\le3$，得到 $16$；若再加入 $P$，可取 $m\le4$，得到 $21$。这些是上界，不声称 sharp。

**证明。** supplier 的整个 Hermitian linear image 由五个 real coordinates
$(x,y,d,\operatorname{Re}z,\operatorname{Im}z)$ 给出。$\Delta_W\operatorname{Ad}_{U_0^\dagger}$ onto $\mathcal H_2\oplus\mathbb R$，而 $G_s$ 在这些 coordinates 上的 determinant 是

$$
(\alpha^2-\beta^2)s^2=s^3\ne0.
$$

故每个 fixed finite $n\ge1$ 都有 $\operatorname{rank}_{\mathbb R}T_n=5$，包括全部 complex off-diagonal degrees of freedom。

现将同一 Choi set 线性映到

$$
\Omega_S=\{(T_n\circ\mathcal D^\dagger)|_S:\mathcal D\ {\rm CPTP}\}.
$$

这是非空 compact convex set；每点按定义有一个 realizing decoder。其所在 affine space 是从 $S$ 到 $\operatorname{ran}T_n$ 的 real-linear maps，且 $I_3$ 的值固定为 $I_3$，维数至多 $5m$。每个 task 切出其中的 convex compact subset

$$
\Omega_i=\{L\in\Omega_S:\|L(A_i)-A_i\|_{\rm op}\le\epsilon_i\}.
$$

在这个同一个 affine space 使用经典 finite Helly theorem：空的 full intersection 必有至多 dimension 加一项的空 subintersection。该中间定理见 [Weisstein, “Helly's Theorem”](https://mathworld.wolfram.com/HellysTheorem.html)，其 finite real-convex statement 亦见 [Mathlib 的固定源表述][F83HELLY]。不重新证明 Helly，也不把它当作新的 quantum theorem。这里的新增对应在于从实际 $F^n$ 的 rank-five entire image 得到维数并只在 $\Omega_S$ 中求交；不假定任意 ambient linear map 都可实现。更精确地，$\dim\operatorname{aff}\Omega_S+1$ 也给出上界。

最后 $E_\varphi(q)$ 均在 $\operatorname{span}_{\mathbb R}(D_q,X,Y)$ 中，其中

$$
D_q=\operatorname{diag}(1-q,q,0),\quad
X=|\xi\rangle\langle e|+|e\rangle\langle\xi|,\quad
Y=i(|\xi\rangle\langle e|-|e\rangle\langle\xi|).
$$

加入 $I_3$ 给 $m\le3$，再加 $P$ 给 $m\le4$。当 $0<q<1$ 且 phases 含 $0,\pi,\pi/2$ 时这两个维数分别达到 $3,4$；short 或 degenerate catalogues 可更小。$m=0$ 时所有 tasks 为 scalar identities，loss 恒为零；empty list 亦总 feasible。∎

**命题 83.5（decoder-choice hypergraph 与 pairwise 的边界）。** 将定义 83.3 的 inclusion-minimal infeasible subsets 作为 forbidden hyperedges。一个 deterministic task label selecting one fixed decoder per label 满足全部阈值，当且仅当没有 forbidden edge 是 monochromatic。对实际 $F^n$，每条 edge 的大小至多 $5m+1$。singleton edge 意味着任何 labeling 都失败；空 catalogue 约定使用零 labels。

**证明。** 若每个 label fibre feasible，就可分别选择一个其 realizing decoder，且它不能含 forbidden edge。反之，一个 infeasible fibre 因 finite 而含 minimal infeasible subset，故若不存在 monochromatic edge 则每个 fibre feasible。edge-size bound 是定理 83.4。∎

这个 finite task hypergraph 不可一般替换为 pairwise graph。例如，另取 qutrit replacement noise $\mathcal N(\rho)=\operatorname{Tr}(\rho)|0\rangle\langle0|$，三任务为互相正交 coordinate projections $P_1,P_2,P_3$，阈值均为 $1/2$。任意 decoder 的 recovered input effects 是 $p_iI$，其中 $p_i=\operatorname{Tr}(P_i\sigma)$，$\sigma=\mathcal D(|0\rangle\langle0|)$；loss 是 $\max(p_i,1-p_i)$，individual optimum 为 $1/2$。任意 pair 由 preparation decoder 输出 $(P_i+P_j)/2$ 达到，但 triple 要求三个 $p_i=1/2$，违反 $\sum p_i=1$。这是另一个固定 channel 的反例，不声称实际 $F^n$ 存在同样 triple。

**约定 83.6（凸性与资源范围）。** Helly 作用于固定 noise 下同一个 effective common-CPTP image。若 encoder 也变化，composition 的 bilinearity 不自动给出该 convex image；discrete controllers 或非凸 resource restrictions 同样不能直接套用。bounded witness size 不给出 efficient enumeration、arbitrary-real decidability、统一 label 数上界或 memory dimension。定理 83.1 的 zero-slack phase catalogue 有更强的 pairwise obstruction；定理 83.4 则适用于一般方向与 thresholds。两者均只刻画已供应 tasks 的 static decoder choice，不推导 online controller minimum、quantum capacity 或物理资源 minimum。

## 84. 供应合同的对应与仍缺的桥梁

**定义 84.1（各命题的 owning supplier）。** §§73–80 保留其原 source contract；本批次只按下表使用明确的固定来源。一个来源更新不改变另一个来源的对象、权限或误差度量。

| 来源与固定版本 | 在本批次供应的中间结论 | 不转移的条件 |
| --- | --- | --- |
| [Environment §27][F81ENV27]，`033c1b370f2447aa20e191a6a3da609aba697e50` | actual all-angle fair chronological channel、whole-qutrit task、entire complex effect image 与单 effect right inverse | 不是 arbitrary law 或多任务 common right inverse |
| [Purity §§87–91][F84PA87]，`29400a844a8c71ee6134aeec1d34ec0103084b4e` | normalized Choi spectra、finite NPT、EB limit、frame norms 与 full-table injectivity | scalar norms 的承诺模型不能替换为所有 states/channels |
| [Purity §92][F84PA92] 与 [Environment §28][F84ENV28]，`054965ffe9988c98e97c1fbdc4d6edc125acde96` | separable same-scalar partners 与同一 fixed-$P$ task 的 exact optimum separation | 每 horizon 各有 partner，不是同一 partner semigroup、共同 decoder 或实际历史 |
| [RRO carrier §§9、11][F84RRO]，`8d00be1638132bbcf0ef888fa0901cacb583ca45` | actual unassisted delayed joint encoding 的 exact capacity 与 endpoint half-trace necessity | normalized live-state error、晚选 wait/execute 和全部 usable information 的 factorization 必须保留 |
| [Strict-real §§7–10][F84STRICT]，`3350fc26dcbaf210d8ab035c7e25ab99c76e8447` | both-endpoint tail、whole-child singleton neighbourhood、actual mixed-$M$ child 与 finite exceptional-meeting outer set | 不把 complex candidates、别的 child 或 counterfactual alternative 当作实际 acquired world |

**命题 84.2（scalar fibre 不决定扩域后的 fixed-task answer）。** 对 finite $n\ge3$ 及 $n=\infty$，令 $\tau=2^{1-n}$，在 infinity 取 $\tau=0$。采用 [Purity Theorem 92.2][F84PA92] 的 normalized Choi partner $\sigma_n$ 及其 EB channel $\Psi_n$。它与实际 normalized Choi state $\omega_n$ 的两个 marginals 均为 $I_3/3$；对每一组独立 local SIC choices 与每一组 independent complete local MUB choices，二者对应 table norms 同时相等：

$$
\|\mathbf P\|_*=(5+3\tau)/36,\qquad
\|\mathbf Q\|_*=5/3+\tau.
$$

SIC 使用 effects $\Pi_i/3$，MUB 使用 literal projectors；不添加 basis-sampling factor。对同一 fixed task $P_0=P=|\xi\rangle\langle\xi|$，全部 input densities 上、分别允许一个 input-independent terminal CPTP decoder 的 optima 却为

$$
\eta_{P_0}(F^n)=0,\qquad
\eta_{P_0}(\Psi_n)=\frac{2(1-3\tau)}{7-3\tau}>0.
$$

因此在包含这两类 channels 的 comparison domain 上，任何仅使用上述 marginals 与 scalar norms 的函数都不能决定该 task optimum。

**证明。** scalar equality、separable partner 与 channel correspondence 直接使用 Purity Theorem 92.2；exact unrestricted task values、attaining decoder 和 lower certificate 直接使用 Environment Theorem 28.2，不在此重建。两个 channels 在同一 retained scalar fibre 内，但该 task answer 不同，所以 answer 不能通过此 observation map factor。把相同读数代入任意 nonlinear postprocessing 仍相同，故后处理亦不能补回区别。∎

有限 $n\ge3$ 时 $\omega_n$ 是 NPT 而 $\sigma_n$ separable；infinity 时二者 channels 都是 EB，仍有 gap $2/7$（$n=3$ 时为 $2/25$）。这个任务差异因而也不等同于 EB/non-EB 二分。在 promised actual family 上，$\|\mathbf Q\|_*-5/3=\tau$ 仍恢复参数；反例使用的是 enlarged domain，未否定该受限辨识。固定同一 local frames 的 full tables 仍 informationally complete，故会区分 partners；二者 output on $P_0$ 已不同。

量词严格为 $\forall n\in\{3,4,\ldots,\infty\}\ \exists\Psi_n$，各 channel/task/horizon 有各自允许的 decoder。这里没有一个 channel 其 powers 同时等于全部 $\Psi_n$ 的结论，没有一个 decoder 同时实现全部 optima 的结论，也没有 partners 与 actual FIB histories 相同的结论。frame identities、entanglement bounds、product-state construction 的成熟先例与适用规范均沿 Purity §§89、92 所引文献，不把供应证书重复计作本批新的 witness。

**约定 84.3（delayed joint retention 的实际 necessity）。** [RRO Definition 9.2 与 Theorem 9.3][F84RRO] 使用其实际 double-wall source、known height $1/8$、所有未知 normalized live inputs $\rho_{\beta,m}$，先实际收到 command $j\in\{1,\ldots,N\}$，再 joint encoding、retention，之后才收到 wait/execute bit $b$。其 unassisted CPTP restrictions 与两个 fixed common endpoint decoders 为

$$
\mathcal E_j:M_3\to\mathcal B,\qquad
\mathcal B=\bigoplus_\alpha M_{d_\alpha},\qquad
\mathcal D_b:\mathcal B\to M_3,
\qquad
U_j=\operatorname{diag}(e^{-iC_j/4},e^{iC_j/4},1),\quad C_j=j/(N+1).
$$

$U_j$ 的 basis 是该来源的 $(U_+,U_-,e_2)$，不是本批的 $(\xi,e,f)$。两 endpoint identities 是
$\mathcal D_0\mathcal E_j(\rho_{\beta,m})=\rho_{\beta,m}$ 与
$\mathcal D_1\mathcal E_j(\rho_{\beta,m})=U_j\rho_{\beta,m}U_j^\dagger$。
所有 retention 后可用信息必须通过 $\mathcal B$；不存在 encoder 另行读取的 history-correlated helper、accessible archive、specimen bypass、surviving command dial 或 assisting receiver share。输入独立 ancillas 归入 maps，真正 spectator reference 不可访问。仅把一个 archive 列入资源账不证明输入具有 $\mathcal E_j(\rho_{\beta,m})$ 这一 unassisted form。

该来源的 exact necessary-and-sufficient condition 为

$$
N\le\sum_\alpha\lfloor d_\alpha/3\rfloor.
$$

这是其原 delayed task 的 theorem，不是 §83 的 label count。RRO §11 的 approximation 则要求在原 endpoint 对全部 $j,b,\beta,m$ uniform：

$$
\sup_{j,b,\beta,m}\frac12
\|\mathcal D_b\mathcal E_j(\rho_{\beta,m})
       -U_j^b\rho_{\beta,m}(U_j^b)^\dagger\|_1\le\epsilon.
$$

这是 normalized-live endpoint half-trace metric，包含每个 encoding outcome；没有 postselection、abort 或额外失败。若 $N\ge2$，令

$$
\begin{gathered}
\kappa_R=(2-\sqrt2)/8,\quad r_\epsilon=\sqrt{\epsilon/\kappa_R},\quad
u_\epsilon=2r_\epsilon+r_\epsilon^2,\\
s_N=\sqrt{1-\left(\frac{1+2\cos(1/[4(N+1)])}{3}\right)^2},\qquad
D=\sum_\alpha d_\alpha.
\end{gathered}
$$

RRO Theorem 11.2 供应 necessity

$$
D\ge\frac{9N}{(\sqrt3+u_\epsilon)^2
 +(N-1)u_\epsilon^2(1+2/s_N)^2}.
$$

此处 $D$ 不是 $\sum d_\alpha^2$。该界不是 sufficient 或 optimal approximate capacity，不决定给定 blocks 的可行性；即使 $\epsilon=0$，$D\ge3N$ 也不能替代 exact sum-of-floors condition。该来源还明确允许 positive-error command supports overlap。

terminal projection-probability loss 仅限制指定 effects，不能反推此 uniform half-trace premise；static supplied labels 亦没有 joint retention factorization。若 execute 在 encoding 前就不可撤回地选定，原 late wait option 已改变，也不是该 theorem 的任务。supplier 的 complete-continuation extension 还要求同一实际 joint endpoint ports、law、reference、archives、clocks、permissions 与 selection/update kernel，不能从 specimen marginal 近似直接推出。

**命题 84.4（最新 mixed child 的 chosen-$J$ 局部证书）。** 保持定义 79.1 的实际 $H_4$、strict-real guards、chronological clocks 与 complete worlds。在 [Strict-real Theorem 8.2][F84STRICT] 的同一个 acquired sixth-$M$ base $(p^*,v^*)$，以该 entire child 三个 legal worlds 的 identity 为 target $z$。假设原 clock-seven $J$ 已获许可，实际 paid response 被保留，并且存在已供应的 source-independent discriminator，把三个 terminal-$J$ values 分配到三个不交 intervals。则该 fixed child 的 branch-label task 有一次 chosen-$J$ 的 $\mathcal W_1$ certificate。相反，在没有额外区分输入的同一 read-and-halt task 中，只选一次 terminal $M$ 不能恢复全部三个 labels。

**证明。** Theorem 8.2 已穷尽该 entire child：恰有三个 legal complete worlds，其唯一 unordered terminal-$M$ collision pair 是一个 singular endpoint 与一个 ordinary endpoint，且 terminal $J$ 在整个 child 上 injective。无需重新隔离或 lift 其 algebraic roots。

将这三个 pre-read complete states、原合法 $J$ 的 actual successors、三种 response classes 和正确 halt labels 组成有限模型。其 chosen action、read permission 与 successor fields 来自同一原合同；discriminator 只用已供应 intervals，不查询隐藏 world。每个非空 response class 只剩一个 $z$，所以读后 candidate relation 在 $\mathcal W_0$，读前 relation 在 $\mathcal W_1$。保留实际 branch costs 为各自标签，取 rank $1/0$，就得到 §62 的 finite chosen-action certificate。这个有限关系抽象使用 abstract interpretation 的保守性思想（Cousot–Cousot，DOI [10.1145/512950.512973](https://doi.org/10.1145/512950.512973)）；抽象本身不授予读取或动作权限。

若只选原 terminal $M$ 然后 halt，该 actual collision pair 给出同一个 response，却有两个不同 target labels，因此 source-independent halt rule 不能同时正确。这个失败只针对所述 chosen action 与 read-and-halt task，不是所有后续协议的不可能性。∎

**约定 84.5（strict-real support reductions 的准确残余）。** 同一 [Strict-real §§7–10][F84STRICT] 的 Theorem 7.3 给出一个 finite $B_*>0$，同时约束每个 terminal-$J/M$ collision pair 的两个 endpoints：$b(W),b(W')<B_*$。Theorem 7.4 另给出 $q_\infty=(-216/5,-225)$ 附近的 whole-child empty-or-singleton neighbourhood，且 sufficiently large-$b$ acquired worlds 的 entire sixth-$M$ child 是 singleton。这里没有 explicit numerical bound，也没有把仅一个 endpoint 的 tail 估计当成整个 child 的分类。

Theorem 8.4 的 singular-endpoint-$M$ bases 构成 finite nonempty set。更宽的 Theorem 9.10 只要求整个 same child 与 exceptional set $E(p,v)$ 相交，即使 exceptional world 不在所选两 pairs 中，也将同时有 actual distinct $J$ pair 和 actual distinct $M$ pair 的 base 放入明确的 finite complex outer set

$$
\begin{aligned}
Z_E={}&V_{\mathbb C}(Q_{10},E_0N_J,E_0N_M)\\
 &\cup V_{\mathbb C}(S_4,E_0N_J,E_0N_M)\\
 &\cup V_{\mathbb C}(Q_{24},e_{24}n_{24,J},e_{24}n_{24,M}).
\end{aligned}
$$

所有 symbols 按该来源 Definitions 9.1、9.6–9.7 与 Theorem 9.10；$E(p,v)$ 是 strict-real exceptional worlds，不是 quantum task $E(q)$。这个 containment 只给 necessary outer candidates；没有任何 candidate 由此被 isolation、strict-real lifting 或分类。两 pairs 必须在同一 actual acquired child，各自内部 distinct，允许重叠；其共同 responses 无需相同。Theorem 8.2 的 mixed-$M$ witness 因 whole-child $J$ injective，尤其不是 actual joint-$J/M$ witness。

remaining noncompact limits 包括 $b\to0$、$r\to0,1$、无界 $r(1-r)/b$、finite-source singularities 和 denominator/ramification limits；children avoiding $E$ 亦不在上述 finite-image reduction 中。即使排除 $Z_E$ 的全部 legal candidates，也只结算 exceptional-meeting sector。actual joint child、same-$p$ sixth-$J$、fifth-$J$、common parent 与 ancestor obligations 均保留；没有 $H_4$ $L_3$、root $L_7$ 或 eight-versus-nine 结论。

**定义 84.6（本批实际缩小的缺口与原目标）。** §77.4 的 $r=0,pq>0$ 缺口现在在定理 81.4 的 bounded $n=2$ interval 有 exact branch，在定理 81.2、81.5 的不同 limit contracts 有 sharp laws；其余 finite-$q$ regimes、interior outside supplier floor region 与一般 attaining certificates 仍缺。§§82–83 增加 prescribed-task common-decoder laws、optimal-image incompatibility 与有限 feasibility witnesses，没有给出一般 finite-$q$ common optimum、所有 horizons 共用 decoder 或动态 controller optimum。

定义 80.2 的 native current joint-key acquisition、reverse kernels、$A_R$ maintenance/current-at-return recovery、实际 chronology supplement acquisition 与资源问题继续保留。§78.3 的原 actual subexponential pair-energy/cutoff/collision-entropy targets 和有条件 causal-memory programme，不由 terminal task errors 结算；原 fast-window obstruction 也未被削弱。§79.4 及约定 84.5 的 global strict-real incidence 与 ancestors 仍需各自 source guards 下的 actual witnesses 或 exhaustive exclusions。

这些任务关系的综合使用 mature convex support duality、CP positivity、norm contraction、Helly convex intersection 与保守有限抽象作为中间工具。所列既有 sources 供应其已证明内容，本批的承重推导限于实际终端 task geometry、same-decoder coupling 和有限 task-fibre consequences；没有 worldwide priority、物理实现或形式内核认证结论。任何迁移仍须逐项保留 source、chronology、permissions、input-independent laws、target time、task、metric 和所数资源，不能由 static alphabets 或充分 full-behaviour keys 推出 task-controller minimum。

[F81ENV27]: https://github.com/the-omega-institute/trureturing/blob/033c1b370f2447aa20e191a6a3da609aba697e50/docs/develop/theory/AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md#27-quantitative-sharp-tasks-after-fair-chronological-history-erasure
[F83HELLY]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Convex/Radon.lean#L86
[F84PA87]: https://github.com/the-omega-institute/trureturing/blob/29400a844a8c71ee6134aeec1d34ec0103084b4e/docs/develop/theory/AURIC_FIB_ACTUAL_WORD_PURITY_ARITHMETIC.md#87-exact-choi-spectra-of-the-actual-erased-history-qutrit
[F84PA92]: https://github.com/the-omega-institute/trureturing/blob/054965ffe9988c98e97c1fbdc4d6edc125acde96/docs/develop/theory/AURIC_FIB_ACTUAL_WORD_PURITY_ARITHMETIC.md#92-separable-partners-in-the-scalar-observation-fibers-of-the-actual-choi-sequence
[F84ENV28]: https://github.com/the-omega-institute/trureturing/blob/054965ffe9988c98e97c1fbdc4d6edc125acde96/docs/develop/theory/AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md#28-same-scalar-observations-and-different-exact-invariant-task-optima
[F84RRO]: https://github.com/the-omega-institute/trureturing/blob/8d00be1638132bbcf0ef888fa0901cacb583ca45/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_QUANTUM_CARRIER_MINIMUM.md#9-delayed-waitexecute-capacity-for-arbitrary-joint-encoders
[F84STRICT]: https://github.com/the-omega-institute/trureturing/blob/3350fc26dcbaf210d8ab035c7e25ab99c76e8447/docs/develop/theory/FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md#7-the-source-at-infinity-and-bounded-collision-endpoints

## 追加锚（本行以下为增补区）

## 85. 两个邻近任务的局部 exact common branch

**约定 85.1（同一实际信道与同一个终端 map）。** 本节使用定义 81.1、82.1 的整个 complex qutrit 合同：$F=\operatorname{Ad}_{U_0}\circ\Delta_W$，$\mathcal N=F^2$，actual words 的先后仍为 $V_{h_2}V_{h_1}$，history law 为 input-independent fair law。ordered basis 是 $(\xi,e,f)$，$P=|\xi\rangle\langle\xi|$，$E(q)=|\sqrt{1-q}\,\xi+\sqrt q\,e\rangle\langle\sqrt{1-q}\,\xi+\sqrt q\,e|$。比较类为所有与未知输入无关、只作用于终端 qutrit 的 complex CPTP maps $\mathcal D:M_3(\mathbb C)\to M_3(\mathbb C)$，同一个 map 同时服务 $P,E(q)$。对 $A=P,E(q)$，记

$$
L_{\mathcal D}(A)=\|\mathcal N^\dagger\mathcal D^\dagger(A)-A\|_{\rm op},
\qquad c_2(q)=\min_{\mathcal D\ {\rm CPTP}}
                   \max\{L_{\mathcal D}(P),L_{\mathcal D}(E(q))\}.
$$

此 loss 等于全部 qutrit density matrices 上的 worst-case absolute Born-probability error。decoder 可知道两个 tasks、$q$ 和固定 horizon $2$，不能读取 history、reference、额外 summary 或未知输入，不作 code restriction、intermediate correction 或 postselection。这里不加 exact-$P$ 条件；命题 82.3 的条件问题仍是另一个问题。

唯一 noise interface 仍是 [Environment §27][F81ENV27] 的整个 complex effect image。在本 horizon，若 $B$ 是任意 Hermitian output effect，置 $K_2=(U_0^\dagger B U_0)_{\xi,e}$、$d=(U_0^\dagger B U_0)_{ff}$，则

$$
\mathcal N^\dagger(B)=G_{-1/2}(K_2\oplus d)
 =\begin{pmatrix}
x&-z/2&0\\
-\overline z/2&(y+3d)/4&0\\
0&0&(3y+d)/4
\end{pmatrix},\qquad
K_2=\begin{pmatrix}x&z\\\overline z&y\end{pmatrix}.
\tag{85.1}
$$

这只是供应公式的 $n=2$ specialization；下界保留全部 complex degrees of freedom。多个任务对应的 effects 必须来自一个 $\mathcal D^\dagger$，不能分别在此 interval 中选取。

**定理 85.2（局部 analytic common optimum）。** 存在 $\theta_*>0$，令 $q_* =\sin^2\theta_*>0$，使对每个 $0<q<q_*$，置 $\theta=\arcsin\sqrt q$，方程

$$
3\sin(4a-2\theta)=4\sin(2a-2\theta)
\tag{85.2}
$$

在 $(a,\theta)=(0,0)$ 附近的唯一 analytic branch $a=a(\theta)$ 满足 $a/\theta\to-1/2$，且

$$
c_2(q)=c_*(q)
 =\frac12\sqrt{\sin^2a\,(1+3\sin^2a)}.
\tag{85.3}
$$

一个共同 attaining decoder 可用两个 Kraus operators 写成

$$
\begin{gathered}
\Pi=P+|e\rangle\langle e|,\qquad
V_a=\begin{pmatrix}\cos a&\sin a&0\\
                     \sin a&-\cos a&0\\0&0&1\end{pmatrix},\\
L_0=V_a^\dagger\Pi U_0^\dagger,\qquad
L_1=V_a^\dagger|e\rangle\langle f|U_0^\dagger,\qquad
\mathcal D_a(X)=L_0XL_0^\dagger+L_1XL_1^\dagger.
\end{gathered}
\tag{85.4}
$$

它在整个 $M_3(\mathbb C)$ 上为 CPTP，而不是两个 single-effect realizations。该 branch 的 expansions 为

$$
\begin{aligned}
a(\theta)&=-\theta/2-(7/2)\theta^3+O(\theta^5),\\
a(\arcsin\sqrt q)&=-\sqrt q/2-(43/12)q^{3/2}+O(q^{5/2}),\\
c_2(q)&=\sqrt q/4+(15/8)q^{3/2}+O(q^{5/2}).
\end{aligned}
\tag{85.5}
$$

特别，$q$ 项的系数恰为零。本定理只给正邻域的存在性，不给 $q_*$ 的数值，也不把它等同于单任务定理 81.4 的 interval。

**证明。** 先构造同一个 primal map，再给对全部 complex competitors 的 lower certificate。

由 $V_a$ unitary、$\Pi^2=\Pi$，

$$
L_0^\dagger L_0+L_1^\dagger L_1
 =U_0(\Pi+|f\rangle\langle f|)U_0^\dagger=I_3.
$$

故 (85.4) trace preserving；Kraus form 给 complete positivity。对 $A=P,E(q)$，令 $A_2$ 是其 $\xi,e$ block，$V=V_a|_{\operatorname{ran}\Pi}$。其 adjoint 同时给出

$$
U_0^\dagger\mathcal D_a^\dagger(A)U_0
  =K_A\oplus y_A,\qquad K_A=VA_2V^\dagger,\qquad
 y_A=(K_A)_{ee}.
\tag{85.6}
$$

这里 $y_P=\sin^2a$、$y_E=\sin^2(a-\theta)$。代入 (85.1)，两个 full residuals 为

$$
R_A=\begin{pmatrix}\delta_A&b_A\\b_A&-\delta_A\end{pmatrix}\oplus y_A,
\quad
\begin{array}{ll}
\delta_P=-\sin^2a,& b_P=-\sin(2a)/4,\\
\delta_E=q-\sin^2(a-\theta),&
 b_E=-\sin(2a-2\theta)/4-\sin\theta\cos\theta.
\end{array}
\tag{85.7}
$$

记

$$
p(a)=\sqrt{\delta_P^2+b_P^2}
 =\tfrac12\sqrt{\sin^2a(1+3\sin^2a)},\qquad
e(a,\theta)=\sqrt{\delta_E^2+b_E^2}.
$$

$p\ge y_P$，所以两个 losses 分别为 $p$ 与 $\max\{e,y_E\}$。直接展开平方差得到

$$
e^2-p^2=\frac{\sin(2\theta)}{16}
        [3\sin(4a-2\theta)-4\sin(2a-2\theta)].
\tag{85.8}
$$

方括号在原点对 $a$ 的偏导为 $4$，对 $\theta$ 的偏导为 $2$。解析隐函数定理给出唯一局部 branch，导数为 $-1/2$。方程在 $(a,\theta)\mapsto(-a,-\theta)$ 下变号，唯一性给出 $a$ 是 odd analytic function。将 $a=-\theta/2+c\theta^3+O(\theta^5)$ 代回 (85.2)，三次项为 $(4c+14)\theta^3$，故 $c=-7/2$。在正的充分小 $\theta$ 上，$p=e=c_*>0$，且

$$
y_E=9q/4+O(q^2)<\sqrt q/4+O(q^{3/2})=c_*.
$$

所以 (85.4) 确实达到共同值 $c_*$。还须排除所有其他 complex CPTP maps，而不只比较这条 real construction。

对任意 competitor 令 $\Phi=\mathcal D^\dagger$，把 $M_2$ 元素嵌为 $X\oplus0$，定义

$$
T(X)=\left[\Pi\Delta_W\bigl(U_0^\dagger\Phi(X\oplus0)U_0\bigr)
                    \Pi\right]_{\xi,e}.
\tag{85.9}
$$

embedding、$\Phi$、conjugation、dephasing 与 compression 都是 CP，故 $T$ 是 CP；又因 $\Phi(I_3)=I_3$、$0\le\Pi\le I_3$，$T(I_2)\le I_2$。这个 subunital relaxation 包含每个实际 competitor。取 input-first Choi convention

$$
J_T=\sum_{i,j=1}^2|i\rangle\langle j|\otimes T(|i\rangle\langle j|),
\qquad J_T\ge0,\qquad
\operatorname{Tr}_{\rm input}J_T=T(I_2)\le I_2.
\tag{85.10}
$$

以下所有 trace pairings 是 usual complex-matrix trace。对 $A=P,E(q)$，在所构造 branch 上定义 Hermitian witnesses

$$
H_A=\begin{pmatrix}\delta_A/c_*&b_A/(2c_*)\\b_A/(2c_*)&0\end{pmatrix},
\qquad
M_A=\begin{pmatrix}\delta_A/c_*&-b_A/(4c_*)\\-b_A/(4c_*)&0\end{pmatrix}.
\tag{85.11}
$$

$H_A$ 的两个 eigenvalues 异号，其 trace norm 为
$\sqrt{\delta_A^2+b_A^2}/c_*=1$，且
$\operatorname{Tr}((H_A\oplus0)R_A)=c_*$。由 (85.1)，对任意 competitor 的 residual $R'_A$，

$$
L_{\mathcal D}(A)\ge
\operatorname{Tr}((H_A\oplus0)R'_A)
 =\operatorname{Tr}(M_AT(A_2))-\operatorname{Tr}(H_AA_2).
\tag{85.12}
$$

$H_A$ 的 $ee$ entry 为零，所以这一 pairing 不含 competitor 的 $ff$ scalar，也未对其 complex off-diagonal 加 real restriction。

在 $a=a(\theta)$ 处取偏导，$p'=\partial_a p$，$e_a=\partial_a e$。令

$$
\begin{gathered}
\lambda=\frac{e_a}{e_a-p'},\qquad
C=\lambda P_2^{\mathsf T}\otimes M_P
       +(1-\lambda)E_2^{\mathsf T}\otimes M_E,\\
Y=-\lambda M_PK_P-(1-\lambda)M_EK_E,\qquad
Z=C+I_2\otimes Y,\\
\beta=\lambda\operatorname{Tr}(H_PP_2)
               +(1-\lambda)\operatorname{Tr}(H_EE_2).
\end{gathered}
\tag{85.13}
$$

这里 transpose 是 input-first Choi pairing 所需的 ordinary transpose；$P_2,E_2$ 是两个 fixed input tasks，不是另选的 effects。因 $p'\to-1/2$、$e_a\to1/2$，缩小正邻域后 $0<\lambda<1$，且 $\lambda\to1/2$。定义给出 exact stationarity

$$
\lambda p'+(1-\lambda)e_a=0.
\tag{85.14}
$$

这一 scalar identity 同时保证 $Y$ Hermitian。具体地，令
$J_0=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$，则
$\partial_aK_A=[J_0,K_A]$，且由 (85.7)、(85.11)，

$$
\operatorname{Tr}(M_P\partial_aK_P)=p',\qquad
\operatorname{Tr}(M_E\partial_aK_E)=e_a.
$$

real $2\times2$ skew-symmetric space 是 $J_0$ 的一维 span，因此 (85.14) 迫使
$\lambda[M_P,K_P]+(1-\lambda)[M_E,K_E]=0$，即 $Y=Y^\dagger$。

对 input-first vectorization $\operatorname{vec}(V)=\sum_i|i\rangle\otimes V|i\rangle$，定义 (85.13) 还给出 exact kernel 与 value identities：

$$
Z\operatorname{vec}(V)=0,\qquad -\operatorname{Tr}Y-\beta=c_*.
\tag{85.15}
$$

第一式可直接用
$(A^{\mathsf T}\otimes M)\operatorname{vec}(V)=\operatorname{vec}(MVA)$ 验证：由 $K_A=VA_2V^\dagger$，两项之和为
$\operatorname{vec}((\lambda M_PK_P+(1-\lambda)M_EK_E+Y)V)=0$。第二式来自 (85.12) 在共同 primal map 上对每项均为等号，即
$\operatorname{Tr}(M_AK_A)-\operatorname{Tr}(H_AA_2)=c_*$，再取 weighted sum。

为证明 exact dual feasibility，而非只给形式 stationarity，写 $t=\sqrt q\downarrow0$。由 (85.7) 与 branch expansion，

$$
\begin{gathered}
\delta_P=-t^2/4+O(t^4),\qquad
\delta_E=-5t^2/4+O(t^4),\\
b_P=t/4+O(t^3),\qquad b_E=-t/4+O(t^3),\qquad
\lambda=1/2+O(t^2).
\end{gathered}
$$

将这些式子及 $K_P=VP_2V^\dagger$、$K_E=VE_2V^\dagger$ 代入 (85.13)，得到

$$
\frac{Y}{t}\longrightarrow\frac18
 \begin{pmatrix}25&0\\0&1\end{pmatrix},\qquad
\frac{Z}{t}\longrightarrow\frac18
 \begin{pmatrix}
1&0&0&1\\
0&1&1&0\\
0&1&25&0\\
1&0&0&1
\end{pmatrix}=:Z_0.
\tag{85.16}
$$

这里的四维基顺序为 input-output pairs $(\xi\xi,\xi e,e\xi,ee)$。$Z_0$ 的 eigenvalues 恰为

$$
0,\quad\frac14,\quad
\frac{13-\sqrt{145}}8,\quad\frac{13+\sqrt{145}}8.
$$

后三个严格为正，kernel 恰为 $\operatorname{span}(1,0,0,-1)$，即 limiting $\operatorname{vec}(V)$。由于 (85.15) 对每个正 $t$ 都是 exact kernel，不能因连续扰动生成负的小 kernel eigenvalue：在连续选取的 $\operatorname{vec}(V(t))^\perp$ orthonormal frame 中，$Z/t$ 的 restriction 连续趋于 strictly positive restriction of $Z_0$。故缩小邻域后 $Z\ge0$；同时 (85.16) 的第一个 positive-definite limit 给出 $Y\ge0$。这是 exact kernel 加 positive complement 的论证，没有以数值 positivity 替代之。

最后对任意 complex competitor 的 $J_T$，由 (85.12)、$0<\lambda<1$、(85.10) 及 $Y,Z\ge0$，

$$
\begin{aligned}
\max_A L_{\mathcal D}(A)
&\ge \lambda\operatorname{Tr}((H_P\oplus0)R'_P)
          +(1-\lambda)\operatorname{Tr}((H_E\oplus0)R'_E)\\
&=\operatorname{Tr}(CJ_T)-\beta\\
&\ge-\operatorname{Tr}(Y T(I_2))-\beta\\
&\ge-\operatorname{Tr}Y-\beta=c_*.
\end{aligned}
\tag{85.17}
$$

这是 CP/subunital Choi cone 上的 weak-duality bound，适用于包含实际 competitor 的整个 relaxation；不要求 strong duality，也不把 independently attainable effects 当成共同 map。与 (85.4) 的全 qutrit realization 合并即证 (85.3)。所有局部条件只有有限多个，故可共同选取一个 $0<\theta_*<\pi/2$。

在正邻域 $\sin a<0$，可写
$c_*=-\tfrac12\sin a\sqrt{1+3\sin^2a}$。代入 odd analytic $a(\theta)$ 得
$c_*=\theta/4+(11/6)\theta^3+O(\theta^5)$；再用 $\theta=\sqrt q+q^{3/2}/6+O(q^{5/2})$ 得 (85.5)。odd expansion 也直接排除 $q$ 项。∎

**命题 85.3（独立的 finite-range fallback）。** 不论定理 85.2 的 existential interval 取多小，对每个 $0<q\le1/1000$，$t=\sqrt q$、$k=\sqrt{1-q}$，都有

$$
\frac{t(k-1/2)}2\le c_2(q)\le\frac t4+4t^3.
\tag{85.18}
$$

**证明。** 下界是定理 82.2 的全 complex common-map bound。对上界仍使用 (85.4)，但固定 $a=-\theta/2$，不要求满足 (85.2)。由 (85.7)，

$$
y_P=\frac{q}{2(1+k)},\quad b_P=t/4,\qquad
y_E=\frac{q(1+2k)^2}{2(1+k)},\quad
b_E=-t[1/4+k(1-k)].
$$

这里 $y_P\le q/2$、$q\le y_E\le9q/4$，所以 $|\delta_E|\le5q/4$；又 $k(1-k)=qk/(1+k)\le q/2$，故 $t/4\le|b_E|\le t/4+t^3/2$。用 $\sqrt{b^2+v^2}\le|b|+v^2/(2|b|)$，

$$
p\le t/4+t^3/2,\qquad
 e\le t/4+(29/8)t^3.
$$

$f$ spectator residual 为 $y_E\le9t^2/4\le t/4$，因为 $t\le1/\sqrt{1000}<1/9$；$y_P\le p$。故 full residuals 的最大值不超过 $t/4+4t^3$。∎

(85.18) 的显式 interval 属于这组较弱 inequalities；它不为 (85.2) 的 exact optimum 指定数值 endpoint。一般 finite-$q$ 的 common optimum、可能的 branch changes 与 spectator activation 仍未确定。

## 86. 固定正方向的 certificate stability 与 phase dictionary

**定义 86.1（已供应静态 labels 的 continuum task）。** 固定一个实数 $0<q\le1/1000$，固定 horizon $n=2$，使用约定 85.1 的同一 actual channel、fair chronology、全部 complex qutrit inputs 与终端权限。任务为定理 83.1 的整个 phase circle $E_\varphi(q)$，$\varphi\in\mathbb R/(2\pi\mathbb Z)$。对每个 fixed terminal CPTP map，令

$$
L_{\mathcal D}(\varphi)
 =\|\mathcal N^\dagger\mathcal D^\dagger(E_\varphi(q))-E_\varphi(q)\|_{\rm op}.
$$

给定 $\delta\ge0$，$M_q(\delta)$ 是能够满足

$$
\forall\varphi\ \exists j\in\{1,\ldots,M\},\qquad
L_{\mathcal D_j}(\varphi)\le\eta_2(q)+\delta
\tag{86.1}
$$

的最小正整数 $M$；不存在有限 dictionary 时取 $+\infty$。每个 $\mathcal D_j$ 必须是一个在整个 $M_3(\mathbb C)$ 上定义、与未知输入无关的 fixed CPTP map。一个已供应的 deterministic static task label 只能选择 $j$，不能在同一 label 内继续按 phase 调整 map；该 label 不携带额外 history 或输入资料。既不要求 selection fibres 连续或可测，也不供应取得 phase 的操作。这里比较的是 projection-probability error，非 whole-identity recovery 的 reference-sensitive channel error。

以下参数全部直接取自定理 81.4 的唯一 admissible root $R=R(q)$ 及其 $y,d,\vartheta,\gamma,w,\eta$，其中 $\eta=\eta_2(q)$。为显式给出 constants，记

$$
\begin{gathered}
y=\frac{(R-1)(2-R)}{6R},\qquad
 d=\frac{24q-R(R-1)(2-R)}{2(5R^2-8)},\qquad
\vartheta=\frac{R^2-1}{3},\quad
\gamma=\sqrt{\vartheta(1-\vartheta)},\\
w=\frac\gamma{2R},\qquad \eta=\frac{3y+d}{4},\qquad
h=\sqrt{q(1-q)},\\
m_+=\frac{(2-R)(R+1)}{2R^2},\qquad
\mu=\frac{(R-1)(R+2)}{2R^2},\\
A_q=\mu(w-h)^2,\qquad
B_q=\frac{h^2}{\eta+d}+\frac h2+h^2.
\end{gathered}
\tag{86.2}
$$

定理 81.4 与 83.1 已给出 $0<d<y/3$、$\eta>d$、$w^2=y(1-y)$ 与 $w>h$，故 $A_q,B_q>0$。admissible-root existence、uniqueness、attainment 与这些 strict inequalities 均复用原证明。

**命题 86.2（从单任务 certificate 到任意共同 map 的定量约束）。** 对定义 86.1 的每个 complex qutrit CPTP map，令

$$
\mathcal T_{\mathcal D}(X)
  =(U_0^\dagger\mathcal D^\dagger(X)U_0)_{\xi,e},\qquad
K_\varphi=\mathcal T_{\mathcal D}(E_\varphi),\qquad
\mathsf P_\varphi=\begin{pmatrix}
1-y&-we^{-i\varphi}\\-we^{i\varphi}&y
\end{pmatrix}.
$$

则对每个 $\varphi$，

$$
L_{\mathcal D}(\varphi)\le\eta+\delta
 \quad\Longrightarrow\quad
\|K_\varphi-\mathsf P_\varphi\|_{\rm op}\le\sqrt{\delta/\mu}.
\tag{86.3}
$$

而对任意 $\varphi,\psi$，不加近似最优假设也有

$$
\max\{L_{\mathcal D}(\varphi),L_{\mathcal D}(\psi)\}-\eta
 \ge\frac{A_q}{4}|e^{i\varphi}-e^{i\psi}|^2.
\tag{86.4}
$$

**证明。** $\mathcal T_{\mathcal D}:M_3\to M_2$ 是 unital CP compression，故 $K_\varphi$ 是任意可能的 complex effect。这里 domain 为 $M_3$，所以它 unital；(85.9) 另将 domain 限制为 $M_2$ 的 corner，才得到 subunital map。两种接口均从一个实际 $\mathcal D$ 取得。

令 $Z_\varphi^{(2)}=\operatorname{diag}(1,e^{i\varphi})$，
$Q_\varphi=Z_\varphi^{(2)}Q_\vartheta Z_\varphi^{(2)\dagger}$，其中 $Q_\vartheta$ 是定理 81.4 的 certificate projection。复用该定理与定理 83.1 的 conjugated witness，

$$
Y_\varphi=\frac{Q_\varphi\oplus(-3\vartheta)}{R^2},\qquad
\|Y_\varphi\|_1=1,
\qquad
M_\varphi=m_+\mathsf P_\varphi-\mu(I_2-\mathsf P_\varphi).
$$

(85.1) 中的 competitor scalar $d'$ 在此 pairing 中消去，故

$$
\operatorname{Tr}\bigl(Y_\varphi\mathcal N^\dagger
                         \mathcal D^\dagger(E_\varphi)\bigr)
   =\operatorname{Tr}(M_\varphi K_\varphi),\qquad
\operatorname{Tr}(Y_\varphi E_\varphi)-m_+=\eta.
\tag{86.5}
$$

由 trace/operator-norm support duality，

$$
L_{\mathcal D}(\varphi)\ge\eta+g_\varphi,\qquad
 g_\varphi=m_+-\operatorname{Tr}(M_\varphi K_\varphi).
$$

令 $a_\varphi=\operatorname{Tr}(\mathsf P_\varphi(I-K_\varphi))$、
$b_\varphi=\operatorname{Tr}((I-\mathsf P_\varphi)K_\varphi)$。两者非负，且

$$
g_\varphi=m_+a_\varphi+\mu b_\varphi
 \ge\mu(a_\varphi+b_\varphi),\qquad
m_+-\mu=\frac{2-R^2}{R^2}>0.
$$

因为 $K_\varphi^2\le K_\varphi$，

$$
\|K_\varphi-\mathsf P_\varphi\|_{\rm HS}^2
 =\operatorname{Tr}(K_\varphi^2)+1
                  -2\operatorname{Tr}(\mathsf P_\varphi K_\varphi)
 \le a_\varphi+b_\varphi.
$$

若 loss 不超过 $\eta+\delta$，则 $g_\varphi\le\delta$，再用 operator norm 不超过 Hilbert–Schmidt norm 得 (86.3)。这是 reduced-image stability，不声称 decoder 本身唯一或接近某个唯一 map。

对同一个 map 的两个 tasks，置 $r=|e^{i\varphi}-e^{i\psi}|$。positive unital maps 在 Hermitian operator norm 下 contract，故

$$
\|K_\varphi-K_\psi\|\le\|E_\varphi-E_\psi\|=hr,
\qquad
\|\mathsf P_\varphi-\mathsf P_\psi\|=wr.
$$

两个 individual optima 均为 $\eta$，所以
$\epsilon=\max\{L_{\mathcal D}(\varphi),L_{\mathcal D}(\psi)\}-\eta\ge0$。用 (86.3) 的 $\delta=\epsilon$ 与三角不等式，

$$
(w-h)r\le2\sqrt{\epsilon/\mu}.
$$

平方即得 (86.4)。此处 $K_\varphi,K_\psi$ 一直来自同一个 $\mathcal T_{\mathcal D}$，未以两个独立可达 effects 代替 commonness。∎

**命题 86.3（一个全 qutrit CPTP map 的 quadratic phase neighbourhood）。** 对每个 center $\alpha\in\mathbb R/(2\pi\mathbb Z)$，令 $Z_\alpha=\operatorname{diag}(1,e^{i\alpha},1)$，

$$
\begin{aligned}
B_\alpha&=U_0Z_\alpha(\mathsf P_0\oplus d)Z_\alpha^\dagger U_0^\dagger,\\
\mathcal D_\alpha(X)&=\operatorname{Tr}(B_\alpha X)E_\alpha
       +\operatorname{Tr}((I_3-B_\alpha)X)|f\rangle\langle f|.
\end{aligned}
\tag{86.6}
$$

这是一个 fixed input-independent terminal complex qutrit CPTP map，满足对所有 phases $\varphi$ 的 global bound

$$
L_{\mathcal D_\alpha}(\varphi)
 \le\eta+B_q|e^{i\varphi}-e^{i\alpha}|^2.
\tag{86.7}
$$

在 $\varphi=\alpha$ 时它达到 exact individual optimum $\eta$。

**证明。** $0\le B_\alpha\le I_3$，两个 prepared states 都 trace one。input-first Choi matrix 为

$$
B_\alpha^{\mathsf T}\otimes E_\alpha
 +(I_3-B_\alpha)^{\mathsf T}\otimes|f\rangle\langle f|\ge0,
$$

output partial trace 是 $I_3$，故这是真正的 whole-qutrit CPTP realization。令 $u=\varphi-\alpha$、$r(u)=|1-e^{iu}|$，因为 $f$ 与全部 $E_\varphi$ 正交，

$$
\mathcal D_\alpha^\dagger(E_\varphi)=a(u)B_\alpha,\qquad
 a(u)=\operatorname{Tr}(E_\varphi E_\alpha)=1-h^2r(u)^2.
$$

由 (85.1) 及已供应的 phase conjugation，

$$
\mathcal N^\dagger(B_\alpha)=Z_\alpha C_0Z_\alpha^\dagger,
\qquad
C_0=\begin{pmatrix}
1-y&w/2&0\\w/2&(y+3d)/4&0\\0&0&\eta
\end{pmatrix},\qquad 0\le C_0\le I_3.
\tag{86.8}
$$

只对这些明确的 effect images 使用 conjugation；未假定实际 $F$ phase covariant。由 unitary invariance，

$$
L_{\mathcal D_\alpha}(\varphi)=\|a(u)C_0-E_u\|,\qquad
 C_0-E_0=H_0\oplus\eta,\qquad
 H_0=-\eta Q_\vartheta+d(I_2-Q_\vartheta).
$$

这是定理 81.4 已供应的 residual identity，不重证其 optimizer。令 $\sigma_x,\sigma_y$ 为 usual Pauli matrices；$H_0$ real symmetric，eigenvalues 为 $-\eta,d$，且

$$
E_0-E_u=[h(1-\cos u)\sigma_x-h\sin u\,\sigma_y]\oplus0.
$$

$H_0$ 的 traceless real part 与 $\sigma_y$ anticommute。因此

$$
\begin{aligned}
\|H_0-h\sin u\,\sigma_y\|
 &=\frac{\eta-d}{2}
       +\sqrt{\frac{(\eta+d)^2}{4}+h^2\sin^2u}\\
 &\le\eta+\frac{h^2\sin^2u}{\eta+d}.
\end{aligned}
$$

第一行至少为 $\eta$，也控制了 full residual 中的 spectator scalar $\eta$。剩余 cosine perturbation 的 norm 为 $h(1-\cos u)=hr(u)^2/2$，scaling perturbation 的 norm 不超过 $h^2r(u)^2$，因为 $\|C_0\|\le1$。最后用 $\sin^2u\le r(u)^2$，三角不等式给出 (86.7)。当 $u=0$，residual 的 norm 恰为 $\eta$。∎

**定理 86.4（fixed-$q$ positive-slack dictionary law）。** 对每个固定 $0<q\le1/1000$，在 $0<\delta\le A_q/4$ 上有

$$
\left\lceil\frac{\pi}{\arcsin\sqrt{\delta/A_q}}\right\rceil-1
 \le M_q(\delta)
 \le\left\lceil\pi\sqrt{B_q/\delta}\right\rceil.
\tag{86.9}
$$

右侧对每个 $\delta>0$ 均成立。特别，

$$
\begin{gathered}
M_q(\delta)=\Theta_q(\delta^{-1/2})\quad(\delta\downarrow0),\\
\pi\sqrt{A_q}\le
\liminf_{\delta\downarrow0}\sqrt\delta\,M_q(\delta)
\le\limsup_{\delta\downarrow0}\sqrt\delta\,M_q(\delta)
\le\pi\sqrt{B_q}.
\end{gathered}
\tag{86.10}
$$

对固定的 $N\ge2$ 个不同 phases，令
$r_{\min}=\min_{i\ne j}|e^{i\varphi_i}-e^{i\varphi_j}|>0$。若

$$
0\le\delta<A_qr_{\min}^2/4,
\tag{86.11}
$$

则该 finite catalogue 恰需 $N$ 个 dictionary labels。对于整个 circle，$M_q(0)=+\infty$；在另一个端点 $q=0$，所有 phases 都是 $P$，一个 decoder 足够。

**证明。** 对 upper bound，取 $M$ 个等间隔 centers 并使用命题 86.3 的 actual maps。每个 phase 到某 center 的 circular distance 至多 $\pi/M$，所以其 chord 至多 $\pi/M$，由 (86.7) 达到 excess 不超过 $B_q\pi^2/M^2$。取 $M=\lceil\pi\sqrt{B_q/\delta}\rceil$ 即得 finite dictionary。这一 construction 给出每个 label 的完整 CPTP map，而非仅给一个希望实现的 effect。

反过来，任意满足阈值的 $M$-map dictionary 在 $M+1$ 个等间隔 phases 中，至少有两个 phases 可以选择同一个 successful map。无论 selection fibres 有何形状，所选两 phases 的 chord 至少为 $2\sin(\pi/(M+1))$。由对 arbitrary common map 的 (86.4)，

$$
\delta\ge A_q\sin^2\frac{\pi}{M+1}.
$$

$M\ge1$ 使 $0<\pi/(M+1)\le\pi/2$；当 $0<\delta\le A_q/4$，反正弦的 monotonicity 给出 (86.9) 的 integer lower bound。再用 $\arcsin x/x\to1$ 与 ceiling error 有界，得到 (86.10)。这是在实际 common-map constraint 上应用有限 pigeonhole 与 circle covering；不要求 fibres regular、compact 或 measurable。

对于 finite catalogue，(86.4) 与 (86.11) 排除同一个 label 含两个 tasks；逐 task 使用 (86.6) 的中心 decoder 则 $N$ labels 足够。zero-slack circle 的结论也可直接使用定理 83.1 的 pairwise optimal-image obstruction；$q=0$ 时使用保持 $P$ 的 decoder。∎

定理 86.4 将推论 83.2 的 qualitative finite-catalogue margin 量化，并给出 continuum positive-slack compression。$q$ 必须先固定：$A_q,B_q$ 及 lower-bound interval 均依赖 $q$，没有 uniform joint-$(q,\delta)$ conclusion，也没有 exact finite-$\delta$ count 或 sharp leading coefficient。命题 86.2 的 stability 是 reduced image 的约束；实际 attaining maps 的 existence 不蕴含 decoder uniqueness。

## 87. Phase 精度的静态 FIB register consequence

**推论 87.1（独立固定长度 names 的精度代价）。** 固定定义 86.1 的一个 $0<q\le1/1000$。假设 static dictionary label 仅用一个独立的长度 $\ell\ge0$ binary data word 命名，word 内禁止相邻 $11$，前置 seam 固定为 $0$ 且在这 $\ell$ 位之外，不加其他末端约束。每个 name 只索引一个已供应的 fixed whole-qutrit CPTP decoder，不能附带未计入的 phase access 或 name-dependent continuous program parameter。则对 $\delta>0$，存在达到全部 phase tasks 阈值 $\eta_2(q)+\delta$ 的这种 static naming，当且仅当

$$
F_{\ell+2}\ge M_q(\delta),\qquad F_0=0,\quad F_1=1.
\tag{87.1}
$$

因此最短这种 data length $\ell_q(\delta)$ 满足

$$
\ell_q(\delta)=\frac{\log(1/\delta)}{2\log\phi}+O_q(1),
\qquad\phi=\frac{1+\sqrt5}{2},\qquad\delta\downarrow0.
\tag{87.2}
$$

同一 naming contract 对定理 86.4 的 fixed finite catalogue，在 (86.11) 下的精确 capacity condition 是 $F_{\ell+2}\ge N$。

**证明。** §76.4 与推论 83.2 已供应此独立 fixed-length no-$11$ contract 的 word count $F_{\ell+2}$，此处不另立 counting theorem。若 naming 实现阈值，distinct names 使用的 fixed maps 数不超过 $F_{\ell+2}$，由定义 86.1 不小于 $M_q(\delta)$。反之，(86.9) 说明 $\delta>0$ 有 finite dictionary，故最小 positive integer $M_q(\delta)$ 确实由某 dictionary 实现；若 (87.1) 成立，将这些 maps 分配到不同 legal names 即足够。没有结尾限制，且前置 seam 为 $0$，因此不会删除已计入的 words。

标准 Fibonacci formula

$$
F_{\ell+2}=\frac{\phi^{\ell+2}-(-\phi^{-1})^{\ell+2}}{\sqrt5}
$$

给出 $F_{\ell+2}=\Theta(\phi^\ell)$。对最短 $\ell$ 使用 $F_{\ell+2}\ge M$ 及前一长度的失败条件，得
$\ell=(\log M)/\log\phi+O(1)$。将定理 86.4 的 fixed-$q$ relation
$\log M_q(\delta)=\tfrac12\log(1/\delta)+O_q(1)$ 代入即得 (87.2)。finite catalogue 则使用其恰为 $N$ 的 label count。∎

这一推论把同一 actual quantum task 的 positive-slack phase resolution 翻译成声明的 FIB static-address length。precision 放宽使一个 fixed map 可以服务一段 tasks；zero-slack 时 circle 不存在 finite dictionary，fixed finite catalogue 则每个 phase 仍须独立 label。它只计算 names 的静态容量，不计算 decoder descriptions、phase acquisition、online updates、program counter、量子 program/storage dimension、paid read ports 或物理费用。即使 names 可编码，也没有构造实际取得 phase、更新 register 或执行 decoder 的装置；这些仍需原来源的权限与付费实现合同。

**约定 87.2（承重来源与未解范围）。** §§85–86 的 actual effect image 固定使用 [Environment §27][F81ENV27] 的原 pin；单任务 admissible branch、residual 与 phase-image separation 使用本卷定理 81.4、83.1，不重建其 owning proofs。§85 新增的 common local certificate 在 CP/subunital Choi relaxation 中比较所有 complex maps，并以一个全 qutrit Kraus map 达到；§86 新增的 quantitative stability、共同 map separation 与 quadratic actual decoder neighbourhood 共同支撑 fixed-$q$ dictionary law。§87.1 是该 law 在独立 no-$11$ naming contract 下的应用，而不是另一个一般 classical coding theorem。

trace/operator-norm support duality、CP positivity、Kraus/Choi representation、positive-unital norm contraction、analytic implicit functions 和 circle packing/covering 均为成熟中间工具；量子 map 的规范沿 §82.1 所引 [Watrous 条目](../../../Library/Quantum/watrous2018theory.md)，observable correction 的对应沿 §81.6 所引 [Bény–Kempf–Kribs 条目](../../../Library/Quantum/benykempfkribs2007observables.md)。这些 standard results 本身不供应 (85.2)、$15/8$ 系数或 (86.2) 的 model-specific constants。这里的内容是相对于上述供应结果的组合推导，不作 worldwide novelty 或文献优先权主张。

定理 85.2 不确定局部 branch 外的 finite-$q$ common optimum，(85.18) 不扩大 exact interval。定理 86.4 不交换 $q\downarrow0$ 与 $\delta\downarrow0$，不推广到其他 horizons、其他 task directions 或另一种 input-dependent law。静态 task labels 的上述结论也不供应 erased-history causal control。

定义 80.2 与 84.6 的 native acquisition、reverse kernels、maintenance/current-at-return recovery、chronology supplement 与资源、general quantitative tasks、动态 controller optimum 继续保留。§78.3 的 actual subexponential pair-energy、finite cutoff、collision entropy 及其有条件 causal-memory programme，和 §79.4、84.5 的 strict-real global joint incidence、same-child lifting 与 ancestor obligations，均未由这两个固定 horizon 的论文结论结算。这些 fixed-horizon 结论不结算原无界 horizon 目标。

## 追加锚（本行以下为增补区）

## 88. 双参数范围内的非负 certificate slack

**定义 88.1（固定实际仪器与静态 dictionary 的量词）。** 本节至 §90 使用定义 81.1、86.1 的同一合同。标准坐标中 $U_0=(23)$、$W=(12)$，

$$
\Delta_W(X)=\frac{X+WXW}{2},\qquad
F=\operatorname{Ad}_{U_0}\circ\Delta_W,\qquad \mathcal N=F^2.
$$

这是 actual words $V_{h_2}V_{h_1}$ 在 input-independent fair law $1/4$ 下的平均；先后次序不改变。使用固定 ordered basis

$$
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\quad
 e=(1,1,-2)^{\mathsf T}/\sqrt6,\quad
 f=(1,-1,0)^{\mathsf T}/\sqrt2.
$$

对每个实数 $0<q\le1/1000$，任务是全部

$$
E_\varphi(q)=|v_\varphi\rangle\langle v_\varphi|,\quad
v_\varphi=\sqrt{1-q}\,\xi+e^{i\varphi}\sqrt q\,e,
\quad \varphi\in\mathbb R/(2\pi\mathbb Z),\quad
h=\sqrt{q(1-q)}.
$$

对一个与未知输入无关的 terminal complex qutrit CPTP map $\mathcal D:M_3(\mathbb C)\to M_3(\mathbb C)$，误差仍为

$$
\begin{aligned}
L_{\mathcal D}(\varphi)
 &=\|\mathcal N^\dagger\mathcal D^\dagger(E_\varphi)-E_\varphi\|_{\rm op}\\
 &=\sup_{\rho\in\mathsf D(\mathbb C^3)}
  |\operatorname{Tr}(E_\varphi\mathcal D\mathcal N(\rho))
                 -\operatorname{Tr}(E_\varphi\rho)|.
\end{aligned}
\tag{88.1}
$$

输入包括全部 complex qutrit densities。decoder 没有 history、reference access、额外 summary、较小 input code、intermediate correction 或 postselection。这里是 projection 的 absolute Born-probability error，不是 reference-sensitive whole-channel error。

令 $\eta=\eta_2(q)$ 为定理 81.4、83.1 已供应的 individual optimum，$M_q(\delta)$ 严格沿用定义 86.1：$\delta\ge0$ 时，它是能够使每个 $\varphi$ 都选择一个 $\mathcal D_j$ 达到 $L_{\mathcal D_j}(\varphi)\le\eta+\delta$ 的最小正整数 dictionary size，不存在有限 dictionary 时取 $+\infty$。每个 entry 是一个 whole complex qutrit CPTP map；一个 static label 只能选 entry，不能在 label 内再按 phase 调整 map。selector fibres 不必连续、连通或可测。量词为每个 $(q,\delta)$ 可另选一个 dictionary，不要求一套 dictionary 同时服务所有参数，也没有供应取得 phase 的操作。

下文直接采用定理 81.4 的唯一 admissible root $R=R(q)$、其 reduced optimum 和定理 83.1 的 phase certificate，不重复 root existence、uniqueness 或 individual optimality 的证明。具体参数为

$$
\begin{gathered}
1<R\le21/20,\qquad
 y=\frac{(R-1)(2-R)}{6R},\qquad
 d=\frac{24q-R(R-1)(2-R)}{2(5R^2-8)},\qquad 0<d<y/3,\\
\vartheta=\frac{R^2-1}{3},\qquad
\gamma=\sqrt{\vartheta(1-\vartheta)},\qquad
w=\frac\gamma{2R},\qquad \eta=\frac{3y+d}{4}>d,\\
m_+=\frac{(2-R)(R+1)}{2R^2},\qquad
\mu=\frac{(R-1)(R+2)}{2R^2}>0.
\end{gathered}
\tag{88.2}
$$

记 $Z_\varphi^{(2)}=\operatorname{diag}(1,e^{i\varphi})$，以及既有 rank-one projections 和 normalized dual witness

$$
\begin{gathered}
\mathsf P_\varphi=
 \begin{pmatrix}1-y&-we^{-i\varphi}\\-we^{i\varphi}&y\end{pmatrix},\qquad
Q_\vartheta=\begin{pmatrix}1-\vartheta&\gamma\\\gamma&\vartheta\end{pmatrix},\qquad
Q_\varphi=Z_\varphi^{(2)}Q_\vartheta Z_\varphi^{(2)\dagger},\\
Y_\varphi=\frac{Q_\varphi\oplus(-3\vartheta)}{R^2},\qquad
\|Y_\varphi\|_1=1,\qquad
M_\varphi=m_+\mathsf P_\varphi-\mu(I_2-\mathsf P_\varphi).
\end{gathered}
\tag{88.3}
$$

**引理 88.2（绝对参数界）。** 在定义 88.1 的整个正 $q$ interval 上，

$$
\begin{gathered}
3q\le y\le\frac{480}{119}q,\qquad
m_+\ge\frac12,\qquad \mu\ge18q,\qquad
2q\le\eta\le4q,\\
\frac34\sqrt q\le h,\qquad
\frac74h\le w\le2h\le3\sqrt q,\qquad
w-h\ge\frac12\sqrt q.
\end{gathered}
\tag{88.4}
$$

这些是 exact interval estimates，不使用 $q\downarrow0$ expansion。

**证明。** 从原 root interval 与原 identities 得

$$
\vartheta\le\frac{41}{1200},\qquad
\frac y\vartheta=\frac{2-R}{2R(R+1)}\le\frac14,
\qquad y\le\frac{R-1}{6}\le\frac1{120},
\qquad \frac wh=\frac4{R(3-R+10d)}.
$$

$R(3-R)-2=(R-1)(2-R)\ge0$，且 $d<y/3\le\vartheta/12$，所以

$$
2\le R(3-R+10d)
 \le\frac{21}{20}\left(2+\frac{41}{1440}\right)
 =\frac{20447}{9600}<\frac{16}{7}.
$$

这给 $7h/4\le w\le2h$。用原 identity $w^2=y(1-y)$，

$$
\begin{aligned}
y&\ge w^2\ge\frac{49}{16}q(1-q)
 \ge\frac{49}{16}\frac{999}{1000}q\ge3q,\\
y&=\frac{w^2}{1-y}\le4q\frac{120}{119}.
\end{aligned}
$$

另有 $m_+\ge380/441\ge1/2$。将 $\mu$ 写为

$$
\mu=\frac{3y(R+2)}{R(2-R)}\ge9y\ge27q\ge18q;
$$

其中第一步不等式等价于 $(R+2)-3R(2-R)=(3R-2)(R-1)\ge0$。又

$$
\eta\ge\frac34y\ge\frac94q\ge2q,\qquad
\eta<\frac56y\le\frac{400}{119}q<4q.
$$

最后 $1-q\ge999/1000\ge9/16$ 给 $h\ge3\sqrt q/4$；因此
$w-h\ge3h/4\ge9\sqrt q/16\ge\sqrt q/2$。∎

**命题 88.3（一个任意 complex map 的完整非负 slack）。** 对定义 88.1 的任一 $\mathcal D$，始终保留同一个 unital CP compression

$$
\mathcal T(X)=(U_0^\dagger\mathcal D^\dagger(X)U_0)_{\xi,e},\qquad
K_\varphi=\mathcal T(E_\varphi),\qquad
z_\varphi=(U_0^\dagger\mathcal D^\dagger(E_\varphi)U_0)_{ff}.
$$

有 $0\le K_\varphi\le I_2$、$0\le z_\varphi\le1$。将 actual residual 写成

$$
\begin{gathered}
\mathcal R_\varphi=\mathcal N^\dagger\mathcal D^\dagger(E_\varphi)-E_\varphi
       =H_\varphi\oplus r_\varphi^{(f)},\qquad
\ell_\varphi=\|\mathcal R_\varphi\|=L_{\mathcal D}(\varphi),\\
(H_\varphi)_{12}=-\frac{(K_\varphi)_{12}}2-he^{-i\varphi},\qquad
r_\varphi^{(f)}=\frac{3(K_\varphi)_{22}+z_\varphi}{4}.
\end{gathered}
\tag{88.5}
$$

令

$$
\begin{aligned}
a_\varphi&=\operatorname{Tr}(\mathsf P_\varphi(I_2-K_\varphi)),&
b_\varphi&=\operatorname{Tr}((I_2-\mathsf P_\varphi)K_\varphi),\\
g_\varphi&=m_+a_\varphi+\mu b_\varphi,&
s_\varphi&=\ell_\varphi+\operatorname{Tr}(Q_\varphi H_\varphi).
\end{aligned}
$$

则有 exact identity

$$
\ell_\varphi-\eta
 =m_+a_\varphi+\mu b_\varphi
  +\frac{s_\varphi+3\vartheta(\ell_\varphi-r_\varphi^{(f)})}{R^2}.
\tag{88.6}
$$

右侧每项非负。因此，若 $\ell_\varphi\le\eta+\delta$，$\delta\ge0$，则

$$
a_\varphi\le\delta/m_+,\qquad
b_\varphi\le\delta/\mu,\qquad
s_\varphi\le R^2\delta.
\tag{88.7}
$$

**证明。** 复用 [Environment §27][F81ENV27] 在本卷 (85.1) 的 actual adjoint formula，

$$
\mathcal N^\dagger\mathcal D^\dagger(E_\varphi)=
\begin{pmatrix}
(K_\varphi)_{11}&-(K_\varphi)_{12}/2&0\\
-(K_\varphi)_{21}/2&((K_\varphi)_{22}+3z_\varphi)/4&0\\
0&0&(3(K_\varphi)_{22}+z_\varphi)/4
\end{pmatrix}.
$$

该式包括 $\mathcal D^\dagger(E_\varphi)$ 的任意 complex cross entries，并不要求它本身 block diagonal。它给 (88.5)、$0\le r_\varphi^{(f)}\le\ell_\varphi$ 与 $H_\varphi+\ell_\varphi I_2\ge0$。两个 effects 的 positivity 给 $a_\varphi,b_\varphi\ge0$，而最后一个 PSD 条件给 $s_\varphi\ge0$。

原 certificate 的配对式 (86.5) 消去 $z_\varphi$，恰给

$$
-\operatorname{Tr}(Y_\varphi\mathcal R_\varphi)
 =\operatorname{Tr}(Y_\varphi E_\varphi)
       -\operatorname{Tr}(M_\varphi K_\varphi)
 =\eta+g_\varphi.
$$

左侧另一方面等于

$$
\frac{\ell_\varphi-s_\varphi+3\vartheta r_\varphi^{(f)}}{R^2}.
$$

用 $R^2=1+3\vartheta$ 重排即得 (88.6)。它保留了 dual inequality 后面的所有非负 slack，(88.7) 随即成立。∎

## 89. 同一个 complex decoder 的相位跨度

**命题 89.1（quadrature 与 radial 约束）。** 在定义 88.1、命题 88.3 的同一 map 下，若 $L_{\mathcal D}(\varphi)\le\eta+\delta$，$\delta\ge0$，则

$$
\begin{aligned}
|\operatorname{Im}(e^{i\varphi}(K_\varphi)_{12})|&\le V,\qquad
 V=2R\sqrt{2(\eta+\delta)\delta},\\
|\operatorname{Re}(e^{i\varphi}(K_\varphi)_{12})+w|&\le U,\qquad
 U=\sqrt{\delta/m_+}+w\delta(1/m_++1/\mu).
\end{aligned}
\tag{89.1}
$$

这里的 complex competitors 不限于 real effects。

**证明。** 先以 $Z_\varphi^{(2)\dagger}$ conjugate 两维 block，$Q_\varphi$ 变成 real projection $Q_\vartheta$，$K$ 的 off-diagonal 变成 $e^{i\varphi}(K_\varphi)_{12}$。再以 real orthogonal matrix diagonalize $Q_\vartheta$。positive matrix $H_\varphi+\ell_\varphi I_2$ 在该 eigenbasis 中，一个 diagonal entry 是 $s_\varphi$，另一个在 $[0,2\ell_\varphi]$ 内。其 principal determinant 非负，故 off-diagonal 的平方模不超过 $2\ell_\varphi s_\varphi$。

对任一两维 Hermitian matrix，off-diagonal 的 imaginary part 对应 real skew matrix 的一个标量系数；real orthogonal conjugation 只将此系数乘 $\det O\in\{1,-1\}$。所以其绝对值保持。相位旋转后的 $H$ entry 的 imaginary part 是 $-\operatorname{Im}(e^{i\varphi}(K_\varphi)_{12})/2$，因为 target off-diagonal $h$ 为实数。用 (88.7) 得

$$
|\operatorname{Im}(e^{i\varphi}(K_\varphi)_{12})|
 \le2\sqrt{2\ell_\varphi s_\varphi}
 \le2R\sqrt{2(\eta+\delta)\delta}.
$$

再在相位旋转后的 $\mathsf P_\varphi$ 的 real orthonormal eigenbasis 中写

$$
\widetilde K_\varphi=
 \begin{pmatrix}1-a_\varphi&c_\varphi\\
 \overline{c_\varphi}&b_\varphi\end{pmatrix}.
$$

由 $I_2-\widetilde K_\varphi\ge0$，
$|c_\varphi|^2\le a_\varphi(1-b_\varphi)\le a_\varphi$。选第一 eigenvector 为 $(\sqrt{1-y},-\sqrt y)^{\mathsf T}$，第二为 $(\sqrt y,\sqrt{1-y})^{\mathsf T}$，变回原 coordinates 得

$$
\operatorname{Re}(e^{i\varphi}(K_\varphi)_{12})+w
 =w(a_\varphi+b_\varphi)+(1-2y)\operatorname{Re}c_\varphi.
$$

$|1-2y|\le1$，故 (88.7) 给 radial bound。这里先控制完整 $|c_\varphi|$，没有以实数假设排除 imaginary direction。∎

**命题 89.2（同 map 的 midpoint contraction）。** 若定义 88.1 中同一个 $\mathcal D$ 在两个 phases $\varphi,\psi$ 的 losses 都不超过 $\eta+\delta$，令 $r=|e^{i\varphi}-e^{i\psi}|$，则

$$
(w-h-U)r\le2V.
\tag{89.2}
$$

**证明。** 取 short-arc representatives $\varphi=m+t$、$\psi=m-t$，必要时互换两者，使 $0\le t\le\pi/2$；此时 $r=2\sin t$。由命题 89.1 写

$$
e^{i\varphi}(K_\varphi)_{12}=-w+A_\varphi+iB_\varphi,
\qquad |A_\varphi|\le U,\quad |B_\varphi|\le V,
$$

并对 $\psi$ 同样写。直接取 midpoint quadrature，

$$
\begin{aligned}
\operatorname{Im}\bigl(e^{im}(K_\varphi-K_\psi)_{12}\bigr)
 &=(2w-A_\varphi-A_\psi)\sin t
       +(B_\varphi-B_\psi)\cos t,\\
|(K_\varphi-K_\psi)_{12}|&\ge(w-U)r-2V.
\end{aligned}
$$

另一方面，$\mathcal T$ 是同一个 positive unital map。在 Hermitian $X$ 的 order interval $-\|X\|I\le X\le\|X\|I$ 上作用，得到 $\|\mathcal T(X)\|\le\|X\|$。而

$$
K_\varphi-K_\psi=\mathcal T(E_\varphi-E_\psi),\qquad
\|E_\varphi-E_\psi\|=hr.
$$

于是 $|(K_\varphi-K_\psi)_{12}|\le hr$，合并得 (89.2)。整个比较中的两个 $K$ 一直由一个 $\mathcal T$ 产生；独立 single-effect attainability 不能替代这一步。∎

**定理 89.3（fine 与 coarse slack 的统一跨度界）。** 对定义 88.1 的每个 $0<q\le1/1000$、每个 $\delta>0$ 以及每个成功于 $\varphi,\psi$ 的同一个 arbitrary complex CPTP map，有

$$
\begin{aligned}
0<\delta\le q/16&\quad\Longrightarrow\quad r\le96\sqrt\delta,\\
\delta\ge q/16&\quad\Longrightarrow\quad r\le512\delta/\sqrt q,\\
r&\le512\max\{\sqrt\delta,\delta/\sqrt q\}.
\end{aligned}
\tag{89.3}
$$

因此不作成功假设时，任意同一个 $\mathcal D$ 也满足

$$
\max\{L_{\mathcal D}(\varphi),L_{\mathcal D}(\psi)\}-\eta
 \ge2^{-18}\min\{r^2,\sqrt q\,r\}.
\tag{89.4}
$$

**证明。** 若 $0<\delta\le q/16$，由 (88.4)，

$$
\begin{aligned}
U&\le\sqrt{2\delta}+6\sqrt q\,\delta
                      +\frac{\delta}{6\sqrt q}\\
 &\le\left(\frac{17}{48}+\frac{3}{8000}+\frac1{96}\right)\sqrt q
 \le\frac38\sqrt q,\\
V&\le\frac{21}{10}\sqrt{\frac{65}{8}q\delta}
 \le6\sqrt{q\delta}.
\end{aligned}
$$

第一行用了 $1/m_+\le2$、$1/\mu\le1/(18q)$、$w\le3\sqrt q$。第二行用 $\sqrt{1/8}\le17/48$、$6\delta\le3/8000$。最后一个 bound 由 $(21/10)^2(65/8)=28665/800\le36$ 给出。因此 $w-h-U\ge\sqrt q/8$，(89.2) 给 $r\le96\sqrt\delta$。

若 $\delta\ge q/16$，直接用 actual residual (88.5) 的 off-diagonal：

$$
|(K_\varphi)_{12}+2he^{-i\varphi}|\le2(\eta+\delta).
$$

在 $\psi$ 处同样成立。两式相减，再用同一个 $\mathcal T$ 的 contraction，得到

$$
2hr\le|(K_\varphi-K_\psi)_{12}|+4(\eta+\delta)
 \le hr+4(\eta+\delta).
$$

$\eta\le4q\le64\delta$、$h\ge3\sqrt q/4$ 给

$$
r\le\frac{4(\eta+\delta)}h
 \le\frac{1040}{3}\frac\delta{\sqrt q}
 \le512\frac\delta{\sqrt q}.
$$

两个 ranges 覆盖全部 $\delta>0$，故给 (89.3) 的最后一行；这些是 continuum inequalities，没有抽样步骤。

为得 (89.4)，令其左侧为 $\Delta\ge0$，非负性由 individual optimum 供应。若 $\Delta>0$，将 (89.3) 用于 $\delta=\Delta$，得到

$$
\Delta\ge\min\{r^2/512^2,\sqrt q\,r/512\}
 \ge2^{-18}\min\{r^2,\sqrt q\,r\}.
$$

若 $\Delta=0$，(88.7)、(89.1) 给 $U=V=0$，而 $w>h$，(89.2) 强迫 $r=0$，同一结论成立。∎

## 90. Uniform dictionary 与静态 FIB 名字长度

**命题 90.1（实际 whole-CPTP center maps 的统一 upper bounds）。** 在定义 88.1 的合同下，对每个 center $\alpha$ 使用命题 86.3 的既有 map

$$
\begin{aligned}
Z_\alpha&=\operatorname{diag}(1,e^{i\alpha},1),\\
B_\alpha&=U_0Z_\alpha(\mathsf P_0\oplus d)Z_\alpha^\dagger U_0^\dagger,\\
\mathcal D_\alpha(X)&=\operatorname{Tr}(B_\alpha X)E_\alpha
 +\operatorname{Tr}((I_3-B_\alpha)X)|f\rangle\langle f|.
\end{aligned}
\tag{90.1}
$$

对 $u=\varphi-\alpha$、$r(u)=|1-e^{iu}|$，它满足整个 circle 上的 bound

$$
0\le L_{\mathcal D_\alpha}(\varphi)-\eta
 \le\min\{r(u)^2,\ 2\sqrt q\,r(u)\}.
\tag{90.2}
$$

**证明。** 这里的 $\mathsf P_0,d,E_\alpha,f,U_0$ 与命题 86.3 完全相同：$B_\alpha$ 是 effect，(90.1) 是其已证明的 input-independent measure-and-prepare whole-qutrit CPTP realization，不是一个仅对单 effect 的形式选择。复用该命题的 actual identities

$$
\begin{gathered}
a(u)=\operatorname{Tr}(E_\varphi E_\alpha)=1-h^2r(u)^2,\qquad
\mathcal D_\alpha^\dagger(E_\varphi)=a(u)B_\alpha,\\
\mathcal N^\dagger(B_\alpha)=Z_\alpha C_0Z_\alpha^\dagger,\qquad
C_0=\begin{pmatrix}
1-y&w/2&0\\w/2&(y+3d)/4&0\\0&0&\eta
\end{pmatrix},\quad 0\le C_0\le I_3,\\
L_{\mathcal D_\alpha}(\varphi)=\|a(u)C_0-E_u\|,\qquad
\|C_0-E_0\|=\eta.
\end{gathered}
\tag{90.3}
$$

这些是明确 images 的 conjugation，不假设实际 channel $F$ phase covariant。原 quadratic proof (86.7) 在全部 $u$ 上给

$$
L_{\mathcal D_\alpha}(\varphi)-\eta\le B_qr(u)^2,
\qquad B_q=\frac{h^2}{\eta+d}+\frac h2+h^2.
$$

它使用原 real center residual $[-\eta Q_\vartheta+d(I_2-Q_\vartheta)]\oplus\eta$ 的 imaginary Pauli perturbation；该 upper construction 不限制 lower bound 中的 complex competitors。现在 (88.4) 与 $\sqrt q\le1/20$ 给出绝对 bound

$$
B_q\le\frac12+\frac1{40}+\frac1{1000}
 =\frac{263}{500}<1.
$$

另由 (90.3) 的三角不等式、$\|E_u-E_0\|=hr(u)$，

$$
\begin{aligned}
L_{\mathcal D_\alpha}(\varphi)-\eta
 &\le hr(u)+h^2r(u)^2\\
 &\le(\sqrt q+2q)r(u)\le2\sqrt q\,r(u),
\end{aligned}
$$

其中用了 $r(u)\le2$ 和 $2\sqrt q\le1$。两种 estimates 作用于同一个 actual map，给 (90.2)；非负性仍是 individual optimum。∎

**定理 90.2（双参数 uniform static-dictionary law）。** 对定义 88.1 中每个实数 $0<q\le1/1000$ 与每个实数 $\delta>0$，令

$$
x(q,\delta)=\min\{\delta^{-1/2},\sqrt q/\delta\}.
$$

则

$$
\boxed{\quad
\frac{1+x(q,\delta)}{257}\le M_q(\delta)
 \le1+2\pi x(q,\delta).
\quad}
\tag{90.4}
$$

因此 $M_q(\delta)=\Theta(1+x(q,\delta))$，比较常数同时独立于 $q,\delta$。这一统一结论补充定理 86.4 的 fixed-$q$ law，不改变其 $A_q,B_q$ 或 lower-$\delta$ interval。

**证明。** 对任意正整数 $M$，取 $M$ 个等间隔 centers 和 (90.1) 的 maps。每个 phase 距某 center 的 short-arc distance 至多 $\pi/M$，其 chord 也至多 $\pi/M$。命题 90.1 分别给出两个可行 finite dictionary sizes

$$
\left\lceil\frac\pi{\sqrt\delta}\right\rceil,
\qquad
\left\lceil\frac{2\pi\sqrt q}{\delta}\right\rceil.
$$

两者对所有正参数都是正整数；取较小者，

$$
M_q(\delta)
 \le\min\left\{\left\lceil\frac\pi{\sqrt\delta}\right\rceil,
         \left\lceil\frac{2\pi\sqrt q}{\delta}\right\rceil\right\}
 \le1+2\pi x(q,\delta).
$$

特别，每个正 $\delta$ 都有 finite dictionary。

反向，取任一成功的 $M\ge1$ map dictionary。在 $M+1$ 个等间隔 phases 中为每个 phase 选择一个 successful entry；有限 pigeonhole 给两个 phases 共用一个 entry。它们的 chord 至少为

$$
2\sin\frac\pi{M+1}\ge\frac4{M+1}.
$$

这里 $\pi/(M+1)\in(0,\pi/2]$，concavity 给 $\sin t\ge2t/\pi$。在所共用的同一个 map 上使用 (89.3)，

$$
\frac4{M+1}
 \le512\max\{\sqrt\delta,\delta/\sqrt q\}
 =\frac{512}{x(q,\delta)}.
$$

所以 $x\le128(M+1)$，从而

$$
1+x\le128M+129\le257M.
$$

该下界对任一成功 dictionary 成立，也对其最小正整数 size 成立。只用有限 packing 与选择，不要求 selector fibres 的任何 regularity。∎

**推论 90.3（同一 static naming contract 下的 uniform FIB 长度）。** 仍对每个 $0<q\le1/1000$、$\delta>0$，仅允许 §87.1 的独立 fixed-length binary data names：长度 $\ell\ge0$，word 内禁止相邻 $11$，preceding seam 为固定 $0$ 且不计入这 $\ell$ 位，无额外末端约束。每个 name 只索引一个已供应的 fixed whole complex qutrit CPTP map，不附带 phase access 或未计入的 continuous program。令 $\ell_q(\delta)$ 为达到定义 88.1 全 circle 阈值的最短该类长度。则 exact capacity condition 仍为

$$
F_{\ell+2}\ge M_q(\delta),
\tag{90.5}
$$

并有

$$
\ell_q(\delta)
 =\frac{\log(1+x(q,\delta))}{\log\phi}+O(1),
\qquad \phi=\frac{1+\sqrt5}{2},
\tag{90.6}
$$

其中 remainder 的绝对 bound 独立于 $q,\delta$。更具体，

$$
-\frac{\log514}{\log\phi}
 \le \ell_q(\delta)-\frac{\log(1+x(q,\delta))}{\log\phi}
 \le1+\frac{\log(2\pi)}{\log\phi}.
\tag{90.7}
$$

**证明。** (90.5) 直接应用推论 87.1 的同一 word count 与 naming equivalence；没有另设 counting 或 classical coding theorem。令 $M=M_q(\delta)$。既有 Fibonacci formula 给粗界
$\phi^\ell\le F_{\ell+2}\le2\phi^\ell$，$\ell\ge0$，因而

$$
\frac{\log M-\log2}{\log\phi}
 \le\ell_q(\delta)
 \le\left\lceil\frac{\log M}{\log\phi}\right\rceil.
$$

下界来自必要容量，上界来自选取显示的整数长度。将 (90.4) 的

$$
\log(1+x)-\log257\le\log M
 \le\log(1+x)+\log(2\pi)
$$

代入即得 (90.7)，故 (90.6) 的 $O(1)$ 绝对一致。$M=1$ 时 empty data word 合法，最短长度就是 $0$，同样包含在这些 bounds 中。∎

**约定 90.4（大 slack、零端点与资源范围）。** (90.4) 的 $1+x$ 保留 one-name range。由 (90.3) 也有明确 sufficient condition

$$
\delta\ge2h+4h^2\quad\Longrightarrow\quad
M_q(\delta)=1,\qquad\ell_q(\delta)=0.
$$

这里没有 exact one-label threshold 或 sharp constants 结论。正参数中两项 $\delta^{-1/2}$、$\sqrt q/\delta$ 在 $\delta=q$ 交会，只表示字典阶数的两个尺度，不把这个交点解释为 exact threshold。每个固定正 $q$ 的 $\delta\downarrow0$ 尾段回到 $\delta^{-1/2}$，而 (90.4) 对联合变化的正参数也保持绝对 constants；这不要求跨参数共用一个 dictionary。

端点必须另述：$q=0$ 时全部 tasks 合为同一个 $P$，原 preserving decoder 给 $M_0(\delta)=1$、$\ell_0(\delta)=0$，$\delta\ge0$。对每个 $0<q\le1/1000$，$\delta=0$ 时定理 83.1，或 (89.2) 的 zero-slack case，使每个 label 至多服务一个 phase，因此整个 circle 没有 finite dictionary 或有限 naming length。含 $1/\mu$、$1/\sqrt q$ 的正参数证明不延伸到 $q=0$。

(90.5)–(90.7) 只翻译已供应 static task labels 的精度与名字容量。它们不计 map descriptions、phase acquisition、online updates、program counter、quantum program/storage dimension、paid read ports 或 physical cost，也不由 names 的存在推断这些资源的 minimum。一个 name 选定的是一个完整 map；若同一 name 另获未计入的连续 phase 参数，已经不再是这里的 dictionary 合同。

## 91. 实际共同实现的 K42 迁移障碍

**定义 91.1（来源侧的固定相容模式）。** 使用 [Scale readout 定义 26.1、26.5 与定理 26.6][F91SCALE26] 的原全域合同：$\mathcal T$ 是全部非空有限自由有序满二叉 $\alpha/\beta$ 树，$\mathcal I_3=\rho^3(\mathcal T)$；原始查询是同一不变来源在任意有限左右地址的 leaf-label、branch 或 absent 报告，费用只数缓存后的不同付费地址。策略必须在整个 $\mathcal T$ 上正确判定 $\mathbf1_{\{T\in\mathcal I_3\}}$ 且有限终止，接受保留完整带标签叶证书；固定评价原型不提供免费 source reports 或正例承诺。

在该固定确定性策略空间 $\mathfrak D_3$ 中，$\mathcal O(P)$ 是实际正来源 $P$ 上达到 individual leaf cost $n_P$ 的策略集合。随机版本 $\mathcal O_{\mathrm u}(P)$ 使用 supplier 分别固定的均匀种子空间 $([0,1],\mathcal L,\operatorname{Leb})$，策略保留 input-independent seed law、同种子重放、逐来源几乎处处正确与有限终止，以及非负扩展费用可测；其目标是每个来源分别达到期望 $n_P$。一个 joint subset 中必须共用一个全域策略，随机情形也共用同一 seed law。

取 supplier 定理 26.6 的 $m=42$ 实例，得到两两不同的 $P_i=\rho^3(Q_i)$，$i\in[42]$，其共同构造组成和叶数为

$$
\begin{gathered}
T=42\cdot41=1722,\qquad M=41^2=1681,\\
c(Q_i)=(3403,1681)^{\mathsf T},\qquad
c(P_i)=(6765,11849)^{\mathsf T},\qquad n_{P_i}=18614.
\end{gathered}
\tag{91.1}
$$

这些数值只是原构造的参数代入，不是最小规模。其已供应的完整相容结论为

$$
\begin{aligned}
\bigcap_{i\in J}\mathcal O(P_i)\ne\varnothing
 &\quad\Longleftrightarrow\quad J\subsetneq[42],\\
\bigcap_{i\in J}\mathcal O_{\mathrm u}(P_i)\ne\varnothing
 &\quad\Longleftrightarrow\quad J\subsetneq[42]
 \qquad(J\subseteq[42]).
\end{aligned}
\tag{91.2}
$$

空交取各自原固定策略空间。因此两种来源侧的 hereditary compatibility family 都恰为 $K_{42}=2^{[42]}\setminus\{[42]\}$。这里直接使用原实际树构造、全域策略和固定种子证明，不重建任意 hereditary family 的 realization。

**定义 91.2（目标侧的 exact pattern assignment）。** 另固定一个 finite integer $n\ge1$，在定义 81.1 的实际 fair chronological $F^n$ 上使用全部 complex qutrit density inputs 与原 terminal CPTP permissions。给定 $42$ 个 fixed Hermitian tasks $A_i\in\mathcal H_3$ 和 fixed weak thresholds $\epsilon_i\ge0$，令

$$
\mathscr K_{\mathrm{qt}}=
 \left\{J\subseteq[42]:\quad
 \exists\mathcal D:M_3\to M_3\ {\rm CPTP},\quad
 \|(F^n)^\dagger\mathcal D^\dagger(A_i)-A_i\|_{\rm op}
       \le\epsilon_i\ \text{for all }i\in J\right\}.
\tag{91.3}
$$

loss 是所有 qutrit densities 上的 worst-case absolute expectation error；只有 $A_i$ 为 projection/effect 时才作 event-probability 解释。同一个 $J$ 内只允许一个共同 map。不同 subsets 可以选择不同 maps，但 $n,F^n$、全部 inputs、terminal permissions、整个 catalogue 和 thresholds 均固定不变；没有 history/reference access、额外 summary、smaller code、intermediate correction 或 postselection。exact pattern assignment 的要求是逐 subset 的等价

$$
J\in\mathscr K_{\mathrm{qt}}
 \quad\Longleftrightarrow\quad J\subsetneq[42]
 \qquad(J\subseteq[42]).
\tag{91.4}
$$

这里的 exact 指 feasibility pattern 完全相同，不要求 $\epsilon_i=0$，也不要求它等于某 task 的 individual optimum。

**命题 91.3（K42 不存在这种固定实际 qutrit assignment）。** 对定义 91.1 的实际 same-composition $\rho^3$ 族，不存在定义 91.2 所允许的 $n,A_i,\epsilon_i$ 实现 (91.4)。这同时排除精确保留 (91.2) 两个分别固定策略空间中的任一相容模式。

**证明。** 这正是本卷定理 83.4 与 [Scale 定理 26.6][F91SCALE26] 的 bounded application。参数对应为：来源侧指标 $i\in[42]$ 对应一个目标侧 fixed task/threshold pair $(A_i,\epsilon_i)$；两侧都检验同一个指标 subset $J$ 的一个共同 realization 是否存在。只对应这个交模式，不把 tree strategy 识别为 qutrit decoder。

对目标 catalogue 置

$$
S=\operatorname{span}_{\mathbb R}\{I_3,A_1,\ldots,A_{42}\},\qquad
 d_{\rm task}=\dim_{\mathbb R}S-1\le8.
$$

定理 83.4 的 $m$ 在此为 $d_{\rm task}$，不是 task 数 $42$，也不是 (88.2) 的 scalar $d$。该定理对这个 fixed actual finite positive horizon 的同一个 compact convex image

$$
\Omega_S=
 \{((F^n)^\dagger\circ\mathcal D^\dagger)|_S:
                    \mathcal D\ {\rm CPTP}\}
$$

给出 $\dim\operatorname{aff}\Omega_S\le5d_{\rm task}\le40$，且任何 infeasible catalogue 都有大小至多 $5d_{\rm task}+1\le41$ 的非空 infeasible subset。其 rank-five 与 finite Helly 证明已在 §83.4 给出，这里不重复，也不把所有 ambient linear maps 当作可实现 maps。

假设 (91.4)。full set $[42]$ 必 infeasible，故原 theorem 在同一个 $\Omega_S$ 中给某个 nonempty infeasible $J$，$|J|\le41$。但此 $J$ 是 proper subset，(91.2)、(91.4) 要求它 feasible，矛盾。∎

**约定 91.4（交模式的范围与尚缺目标）。** 这个结论不排除较小的 actual common-decoder incompatibility。它只说明来源侧已实现的一个 size-$42$ minimal infeasible edge 不能通过 (91.3) 的固定合同完整迁移；bounded witness size 也不等于 dictionary label 数的统一上界。Scale 定理供应的是实际相容模式，不供应目标 matrices 或 thresholds；上述反证没有建立两个模型等价，也不宣称任意物理实现不可能。若换成 subset-dependent channels、horizons、input codes、task catalogues 或 thresholds，或给每个 task 独立 decoder，就失去此处的同一个 $\Omega_S$，不能把当前反证转用于那些问题。没有从 tree leaves、strategy costs 或兼容复形推出 controller states、online memory、quantum storage、physical ports 或 channel capacity 的数值。

§§88–90 的统一性来自同一个 actual $F^2$ 的 certificate slack、complex quadrature、same-map contraction 与实际 center maps；§91 只组合两个既有 supplier。trace/operator-norm convex support duality、CP/PSD positivity、positive-unital norm contraction、finite Helly 和 circle packing/covering 都是成熟中间工具，沿 §83.4、87.2 的固定文献对应使用。这里保留的是这些工具与原模型参数的具体组合及适用边界，不作 worldwide novelty 或文献优先权主张。

上述静态结果不扩大定理 85.2 只存在正 $q_*$ 的 exact common branch，也不把其 finite fallback interval 变成 exact interval。一般 finite-$q$ common optima、其他 task directions、其他 horizons 以及跨 horizons 的共同 decoder 仍未由 (90.4) 给出。原 whole-current acquisition、chronology supplement 与 actual paid-resource 合同、general quantitative tasks、动态 controller optimum，§78.3 的 actual subexponential pair-energy、finite cutoff、collision entropy 及有条件 causal-memory programme，以及 §79.4、84.5 的 strict-real global joint incidence、same-child lifting 与 ancestor obligations 均保留；fixed-horizon static labels 与一个有限交模式障碍不结算这些无界目标。

[F91SCALE26]: https://github.com/the-omega-institute/trureturing/blob/77e6b52ce93d57d5dc918ac16456e97edc3e1a13/docs/develop/theory/FIB_SCALE_READOUT_PERMISSION_GEOMETRY.md#26-同组成实际三步像的有限遗传相容模式与无统一-helly-阶数

## 追加锚（本行以下为增补区）

## 92. Finite phase-circle common minimax at the actual horizon

**Definition 92.1 (The finite phase-circle contract).** Fix a finite integer
$n\ge2$ and $0<q\le10^{-3}$. In the ordered actual basis
$(|0\rangle,|1\rangle,|2\rangle)=(\xi,e,f)$, put

$$
s=s_n=(-1/2)^{n-1},\qquad t=|s|=2^{1-n},\qquad
c=\sqrt{q(1-q)},
$$

and let

$$
|v_\varphi\rangle=\sqrt{1-q}\,|0\rangle
       +e^{i\varphi}\sqrt q\,|1\rangle,\qquad
E_\varphi=|v_\varphi\rangle\langle v_\varphi|.
\tag{92.1}
$$

The actual fair chronological channel is
$F^n=\operatorname{Ad}_{U_0}\circ\Phi_s$, with

$$
\Phi_s(X)=
\begin{pmatrix}
 x_{00}&s x_{01}&0\\
 s x_{10}&\frac{1+s}{2}x_{11}+\frac{1-s}{2}x_{22}&0\\
 0&0&\frac{1-s}{2}x_{11}+\frac{1+s}{2}x_{22}
\end{pmatrix}.
\tag{92.2}
$$

A terminal decoder is one input-independent whole complex qutrit CPTP map
$D$. By the actual-channel correspondence, write
$D=\mathcal R\circ\operatorname{Ad}_{U_0^\dagger}$ and optimize over whole
complex CPTP maps $\mathcal R:M_3(\mathbb C)\to M_3(\mathbb C)$. The loss is

$$
e_{\mathcal R}(\varphi)=
 \left\|\Phi_s^\dagger\mathcal R^\dagger(E_\varphi)-E_\varphi
 \right\|_{\rm op}.
\tag{92.3}
$$

By the effect interface, (92.3) is the supremum of the absolute Born-
probability error over every complex qutrit density input. There is no
reference, history, summary, smaller input code, postselection or
intermediate correction. Define

$$
\begin{aligned}
\eta_{(q,n)}&=\min_{\mathcal R\ {\rm CPTP}}e_{\mathcal R}(0),\\
\varepsilon_{\circ}(q,n)&=\min_{\mathcal R\ {\rm CPTP}}
             \sup_{\varphi\in\mathbb R/(2\pi\mathbb Z)}e_{\mathcal R}(\varphi),\\
\Delta_1(q,n)&=\varepsilon_{\circ}(q,n)-\eta_{(q,n)}.
\end{aligned}
\tag{92.4}
$$

The notation $\varepsilon_{\circ}$ is specific to this whole phase circle.
It is not the two-task $c_2(q)$ of §85 and is not the half-diamond
whole-channel quantity of the actual recovery source.

Let $U_\theta=P_0+e^{i\theta}P_1+P_2$ and write
$\mathcal G_\theta=\operatorname{Ad}_{U_\theta}$. The channel is covariant:
$\Phi_s\mathcal G_\theta=\mathcal G_\theta\Phi_s$, and
$E_\varphi=\mathcal G_\varphi(E_0)$.

**Lemma 92.2 (Arbitrary complex lower bound by phase twirling).** For every
whole complex CPTP map $\mathcal R$,

$$
\sup_\varphi e_{\mathcal R}(\varphi)
 \ge (1-t)c.
\tag{92.5}
$$

*Proof.* Haar-twirl the map over the phase circle,

$$
\overline{\mathcal R}=
 \frac1{2\pi}\int_0^{2\pi}
 \mathcal G_\theta\circ\mathcal R\circ\mathcal G_{-\theta}\,d\theta.
\tag{92.6}
$$

This is again CPTP. Covariance of $\Phi_s$, unitary invariance of the
operator norm and convexity give

$$
\sup_\varphi e_{\overline{\mathcal R}}(\varphi)
 \le \sup_\varphi e_{\mathcal R}(\varphi).
\tag{92.7}
$$

It is therefore enough to consider a covariant map. Put
$D_0=(1-q)P_0+qP_1$ and
$C=\overline{\mathcal R}^{\dagger}(|0\rangle\langle1|)$. The operator
$\overline{\mathcal R}^{\dagger}(D_0)$ has charge zero and hence has zero
$01$ entry. The operator $C$ has charge $-1$, so it is a linear combination
of $|0\rangle\langle1|$ and $|2\rangle\langle1|$. The adjoint of (92.2)
multiplies its $01$ entry by $s$ and kills its $21$ entry. Thus the $01$
entry of
$\Phi_s^\dagger\overline{\mathcal R}^{\dagger}(E_\varphi)-E_\varphi$
is

$$
c\,e^{-i\varphi}(sC_{01}-1).
\tag{92.8}
$$

The adjoint of a CPTP map is unital completely positive, so it contracts
operator norm and $|C_{01}|\le\|C\|_{\rm op}\le1$. Consequently
$|sC_{01}-1|\ge1-|s|=1-t$. An operator norm dominates the modulus of
any matrix entry, proving (92.5). $\square$

**Lemma 92.3 (Whole-map upper certificate and spectator).** Let
$\sigma=\operatorname{sgn}(s)$ and define

$$
K_0=P_0+\sigma P_1,\qquad K_1=|1\rangle\langle2|,\qquad
\mathcal R_\sigma(X)=K_0XK_0^\dagger+K_1XK_1^\dagger.
\tag{92.9}
$$

Then $\mathcal R_\sigma$ is CPTP and, for every $\varphi$,

$$
e_{\mathcal R_\sigma}(\varphi)=(1-t)c.
\tag{92.10}
$$

*Proof.* The two adjoint Kraus products sum to $P_0+P_1+P_2$. Directly,

$$
\mathcal R_\sigma^\dagger(E_\varphi)=
 (1-q)P_0+qP_1+qP_2
 +\sigma c\bigl(e^{-i\varphi}|0\rangle\langle1|
                 +e^{i\varphi}|1\rangle\langle0|\bigr).
\tag{92.11}
$$

Applying $\Phi_s^\dagger$ changes the off-diagonal coefficient to
$s\sigma c=tc$ and leaves all three displayed diagonal entries fixed. The
residual is therefore the direct sum of a $2\times2$ off-diagonal block
with eigenvalues $\pm(1-t)c$ and the spectator entry $q$. Since
$t\le1/2$ and $q\le10^{-3}$,

$$
q<\tfrac12\sqrt{q(1-q)}\le(1-t)c.
\tag{92.12}
$$

Hence the spectator does not dominate, and (92.10) follows. The actual
whole-qutrit decoder is
$D_\sigma=\mathcal R_\sigma\circ\operatorname{Ad}_{U_0^\dagger}$,
whose Kraus operators are $K_0U_0^\dagger,K_1U_0^\dagger$. $\square$

**Theorem 92.4 (Finite phase-circle common minimax).** For every finite
$n\ge2$ and $0<q\le10^{-3}$,

$$
\boxed{\displaystyle
\varepsilon_{\circ}(q,n)=\bigl(1-2^{1-n}\bigr)\sqrt{q(1-q)}.}
\tag{92.13}
$$

*Proof.* Lemma 92.2 gives the lower bound for every arbitrary complex
whole-map competitor, and Lemma 92.3 attains it with one map for all
phases. $\square$

**Proposition 92.5 (Strict phasewise individual gap).** In the same range,

$$
0<\Delta_1(q,n),\qquad
\eta_{(q,n)}<\varepsilon_{\circ}(q,n).
\tag{92.14}
$$

*Proof.* Use $\sigma=\operatorname{sgn}(s)$. For $0<r<1-q$, set

$$
z_r=\sqrt{(1-q-r)(q+r)},\qquad
A_r=
\begin{pmatrix}
 1-q-r&\sigma z_r&0\\
 \sigma z_r&q+r&0\\
 0&0&q+r
\end{pmatrix}.
\tag{92.15}
$$

The $01$ block is a rank-one projection and its $22$ entry is in $(0,1)$;
therefore $0\le A_r\le I$. Prepare the actual task state $E_0$ on the
$A_r$ outcome and the orthogonal state $P_2$ on its complement:

$$
\mathcal R_{A_r}(X)=\operatorname{Tr}(A_rX)E_0
 +\operatorname{Tr}((I-A_r)X)P_2
\tag{92.16}
$$

This is a whole-qutrit CPTP map. Explicitly, with
$a=q+r$,
$|w_r\rangle=\sqrt{1-a}|0\rangle+\sigma\sqrt a|1\rangle$ and
$|u_r\rangle=\sigma\sqrt a|0\rangle-\sqrt{1-a}|1\rangle$,
a Kraus family is

$$
L_0=|v_0\rangle\langle w_r|,\quad
L_1=\sqrt a\,|v_0\rangle\langle2|,\quad
L_2=|2\rangle\langle u_r|,\quad
L_3=\sqrt{1-a}\,P_2.
$$

The first two adjoint products sum to $A_r$, the last two to $I-A_r$,
and all four to $I_3$. Its adjoint on any matrix $B$ is

$$
\mathcal R_{A_r}^\dagger(B)
 =\operatorname{Tr}(E_0B)A_r
  +\operatorname{Tr}(P_2B)(I-A_r).
$$

Since $E_0^2=E_0$, $\operatorname{Tr}E_0=1$ and $E_0P_2=0$, this gives
$\mathcal R_{A_r}^\dagger(E_0)=A_r$. The actual terminal decoder is
$D_{A_r}=\mathcal R_{A_r}\circ\operatorname{Ad}_{U_0^\dagger}$, with
Kraus operators $L_jU_0^\dagger$. Applying (92.2) in the adjoint direction
leaves the equal $11,22$ entries of $A_r$ fixed and sends its $01$ entry
to $s\sigma z_r=tz_r$. Thus its full phase-zero residual is

$$
\Phi_s^\dagger\mathcal R_{A_r}^\dagger(E_0)-E_0=
\begin{pmatrix}
-r&tz_r-c&0\\
tz_r-c&r&0\\
0&0&q+r
\end{pmatrix}
$$

with eigenvalues $\pm\sqrt{r^2+(c-tz_r)^2}$ and $q+r$. Hence

$$
e_{\mathcal R_{A_r}}(0)=\max\left\{
 \sqrt{r^2+(c-tz_r)^2},\ q+r\right\}.
\tag{92.17}
$$

At $r=0$ the first term is $(1-t)c$ and the second is strictly smaller
by (92.12). Moreover

$$
z'_0=\frac{1-2q}{2c}>0,
$$

and the derivative at zero of the square of the first term in (92.17)
is $-2t(1-t)c z'_0=-t(1-t)(1-2q)<0$. For each fixed $(q,n)$ in the
declared range, $0<t\le1/2$ and $1-2q>0$. The derivative and continuity
therefore give an $r>0$ with $r<1-q$ and $q+r<(1-t)c$ for which both
terms in (92.17) are strictly smaller than $(1-t)c$. This proves
$\eta_{(q,n)}<\varepsilon_{\circ}(q,n)$ at every finite $n\ge2$;
no choice of $r$ uniform in $n$ is needed. Phase covariance gives
$e_{\mathcal G_\varphi\circ\mathcal R\circ\mathcal G_{-\varphi}}(\varphi)
=e_{\mathcal R}(0)$, so the individual minimum is the same
$\eta_{(q,n)}$ at every phase. It is attained by compactness of the
finite-dimensional Choi set, and $\Delta_1>0$. $\square$

**Corollary 92.6 (Exact one-label excess threshold and positive slack).**
For a tolerance $\delta\ge0$, a one-label dictionary of fixed whole maps satisfies

$$
 e_{\mathcal R}(\varphi)\le\eta_{(q,n)}+\delta
 \quad\text{for every }\varphi
\tag{92.18}
$$

if and only if $\delta\ge\Delta_1(q,n)$. The threshold is exact even
though $\eta_{(q,n)}$ is generally not explicitly evaluated for $n\ge3$.

For every $\delta>0$ there is a finite positive-slack dictionary. If
$\mathcal R_0$ attains $\eta_{(q,n)}$ at phase zero, rotate it by
$\mathcal R_\theta=\mathcal G_\theta\circ\mathcal R_0\circ\mathcal G_{-\theta}$.
Then $e_{\mathcal R_\theta}(\theta)=\eta_{(q,n)}$. Since
$\Phi_s^\dagger\circ\mathcal R_\theta^\dagger$ is unital completely
positive and therefore contracts Hermitian operator norm,

$$
 e_{\mathcal R_\theta}(\varphi)
 \le \eta_{(q,n)}+4c\left|
 \sin\frac{\varphi-\theta}{2}\right|.
\tag{92.19}
$$

Indeed $\|E_\varphi-E_\theta\|_{\rm op}=2c|\sin((\varphi-\theta)/2)|$.
An equally spaced $M$-point phase grid is consequently sufficient when

$$
M\ge\frac{\pi}{2\arcsin(\min\{1,\delta/(4c)\})},
\qquad
M_0:=\max\left\{1,\left\lceil\frac{2\pi c}{\delta}\right\rceil\right\}
\tag{92.20}
$$

Taking $M=M_0$ is one convenient sufficient integer choice. Transporting every rotated
map by $D_\theta=\mathcal R_\theta\circ\operatorname{Ad}_{U_0^\dagger}$
gives whole actual terminal CPTP maps. This is only an upper certificate:
it gives no sharp multi-label rate, and it does not prove that finite
zero-excess dictionaries are infinite for any $n\ge3$. The known $n=2$
zero-slack obstruction and the unresolved $n\ge3$ question retain their
separate scopes.

## 93. The actual $s=0$ restricted-circle endpoint

**Definition 93.1 (Limiting restricted phase family).** Let
$0\le q\le1/2$, $h=\sqrt{q(1-q)}$, and use the same effects $E_\varphi$
from (92.1). At the actual limiting channel,

$$
\mathcal N_\infty=\Phi_0,\qquad
\Phi_0(X)=x_{00}P_0+\frac{x_{11}+x_{22}}2(P_1+P_2).
\tag{93.1}
$$

This is the $s=0$ limiting channel. It is not the empty-horizon identity
$\mathcal N_0$.

**Lemma 93.2 (All-complex lower bound at the endpoint).** For every whole
complex CPTP decoder $D$ and every phase $\varphi$,

$$
\left\|\Phi_0^\dagger D^\dagger(E_\varphi)-E_\varphi\right\|_{\rm op}
\ge h.
\tag{93.2}
$$

*Proof.* For $K=D^\dagger(E_\varphi)$, the adjoint of (93.1) is

$$
\Phi_0^\dagger(K)=\operatorname{diag}
 \left(K_{00},\frac{K_{11}+K_{22}}2,
                    \frac{K_{11}+K_{22}}2\right).
\tag{93.3}
$$

Thus the recovered effect has zero $01$ entry, even when the competing
CPTP map and its effect are fully complex. The residual has $01$ entry
$-h e^{-i\varphi}$, and compression to the unit vectors $|0\rangle$ and
$|1\rangle$ gives the lower bound in (93.2). $\square$

**Theorem 93.3 (Common individual optimum at $s=0$).** Define

$$
D_*(X)=\operatorname{Tr}(P_0X)P_0
       +\operatorname{Tr}((I-P_0)X)P_1.
\tag{93.4}
$$

Then $D_*$ is one whole-qutrit CPTP map, independent of $q$ and
$\varphi$, and for every $0\le q\le1/2$ and every phase,

$$
\min_{D\ {\rm CPTP}}
 \left\|\Phi_0^\dagger D^\dagger(E_\varphi)-E_\varphi\right\|_{\rm op}
 =\left\|\Phi_0^\dagger D_*^\dagger(E_\varphi)-E_\varphi\right\|_{\rm op}
 =h.
\tag{93.5}
$$

In particular the same map attains every individual minimum and
$\min_D\sup_\varphi e_D(\varphi)=h$.

*Proof.* Kraus operators for (93.4) are
$P_0,|1\rangle\langle1|,|1\rangle\langle2|$, whose adjoint products
sum to $I_3$. Their adjoint sends

$$
D_*^\dagger(E_\varphi)=(1-q)P_0+q(P_1+P_2).
\tag{93.6}
$$

The endpoint adjoint fixes this diagonal operator. The full residual is

$$
H_\varphi=
\begin{pmatrix}
0&-h e^{-i\varphi}&0\\
-h e^{i\varphi}&0&0\\
0&0&q
\end{pmatrix},
\tag{93.7}
$$

whose eigenvalues are $-h,h,q$. Since $0\le q\le1/2$ implies $q\le h$,
its norm is $h$. The lower bound (93.2) proves optimality for every
phase, and the same calculation includes both endpoints: at $q=0$ the
residual is zero, while at $q=1/2$ its spectrum is
$\{-1/2,1/2,1/2\}$. $\square$

**Corollary 93.4 (Restricted common-optimum horizon set).** Fix
$0<q\le10^{-3}$ and consider the same restricted $0/1$ phase family at
actual horizons $n\in\{0,1,2,\ldots,\infty\}$. A single whole terminal
CPTP decoder attains the individual minimum for every phase exactly at

$$
\boxed{\{0,1,\infty\}.}
\tag{93.8}
$$

*Proof.* At $n=0$ the identity decoder is exact. At $n=1$,
Proposition 103.2 of the owning actual-channel source supplies
$D=\operatorname{Ad}_{U_0^\dagger}$. Here $\Phi_1=\Delta_W$ fixes each
$E_\varphi$, which is supported on $\operatorname{span}\{|0\rangle,|1\rangle\}$,
so this decoder has zero loss for the whole phase family. For each
finite $n\ge2$, Proposition 92.5 gives the same individual minimum
$\eta_{(q,n)}$ at every phase and
$\eta_{(q,n)}<\varepsilon_{\circ}(q,n)$. A map attaining all those minima
would have supremum loss $\eta_{(q,n)}$, contradicting Theorem 92.4.
Theorem 93.3 supplies $D_*$ at the limiting channel.
The all-rank-one obstruction at the limit has a different task family:
it contains $P_0,P_2$ and the $0/2$ task $Q$, not the fixed-population
$0/1$ circle. Therefore that obstruction does not remove $\infty$ from
(93.8). At $q=0$ all phases coincide with $P_0$; this degenerate case is
separate and the identity already attains the task exactly at every
actual horizon, including the limit. $\square$

The statement (93.8) is a restricted task-family result. It does not
extend to all rank-one tasks, to arbitrary phase directions, or to
whole-channel inversion. For $0<q\le1/2$, the endpoint task error $h$ is
positive. The normalized unit vectors
$|\psi_\pm\rangle=(|0\rangle\pm e^{i\varphi}|1\rangle)/\sqrt2$
give density inputs $\rho_\pm=|\psi_\pm\rangle\langle\psi_\pm|$ with

$$
\Phi_0(\rho_+)=\Phi_0(\rho_-)
 =\tfrac12P_0+\tfrac14(P_1+P_2),\qquad
\operatorname{Tr}(E_\varphi\rho_\pm)=\tfrac12\pm h.
$$

The probabilities are distinct, with opposite deviations from $1/2$.
Thus even this common optimum is not recovery of the input state.

## 94. Same-channel task error and full-state testing

At the same actual limiting channel, keep the decoder permissions of
§93 and distinguish two input tests. The no-reference full-state quantity
of the owning terminal source is

$$
\mu_\infty=\min_{D\ {\rm CPTP}}
 \max_{\rho\in\mathsf D(\mathbb C^3)}
 \frac12\|D\Phi_0(\rho)-\rho\|_1=\frac23,
\tag{94.1}
$$

whereas the stabilized half-diamond quantity, whose reference is
untouched and available only in the input test, is

$$
\delta_\infty=\min_{D\ {\rm CPTP}}
 \frac12\|D\Phi_0-\operatorname{id}\|_\diamond=\frac45.
\tag{94.2}
$$

These are supplied by the exact no-reference and stabilized terminal
results from the full-state source at revision
88e708c6e499168a6bf79cabb6bd08d4e62fb6fb (§§105--111). The reference is never a decoder input.
In particular $\mu_\infty\le\delta_\infty$ and the exact gap is
$\delta_\infty-\mu_\infty=2/15$. No finite no-reference value for
$n\ge2$ is thereby supplied; those finite minimax problems remain open
where the owning source leaves them open.

The phase-optimal map $D_*$ makes the distinction concrete. Since
$\Phi_0(P_2)=(P_1+P_2)/2$ and $D_*$ sends the lower subspace to $P_1$,

$$
D_*\Phi_0(P_2)=P_1,\qquad
\frac12\|P_1-P_2\|_1=1.
\tag{94.3}
$$

Thus a single map can be optimal for every member of the restricted
phase family while performing badly on a full-state probe. Equation
(94.3) is only an explicit distinction for the supplied map; it is not a
new full-state minimax theorem and does not duplicate the proof of
(94.1) or (94.2).

## 95. Positive slack, static names and remaining boundaries

For finite $n\ge2$ define $M_{q,n}(\delta)$ to be the least number of
supplied fixed whole-qutrit CPTP maps whose labels cover the phase circle
with loss at most $\eta_{(q,n)}+\delta$. Corollary 92.6 gives, for every
$\delta>0$,

$$
M_{q,n}(\delta)\le
\max\left\{1,\left\lceil\frac{2\pi\sqrt{q(1-q)}}{\delta}\right\rceil\right\}.
\tag{95.1}
$$

If labels are independent fixed-length binary data words of length $\ell$,
with no adjacent $11$, a preceding seam fixed to $0$ outside the data and
no extra end condition, then the existing word-count supplier gives the
exact static capacity condition

$$
F_{\ell+2}\ge M_{q,n}(\delta),\qquad F_0=0,\quad F_1=1.
\tag{95.2}
$$

The proof is the same finite assignment used by the existing naming
result: a successful naming uses at most $F_{\ell+2}$ fixed maps, while
any dictionary of that cardinality can be assigned distinct legal names.
Combining (95.1) and (95.2) gives a concrete sufficient static length by
choosing the least $\ell$ with

$$
F_{\ell+2}\ge
\max\left\{1,\left\lceil\frac{2\pi\sqrt{q(1-q)}}{\delta}\right\rceil\right\}.
\tag{95.3}
$$

This is a positive-slack upper certificate. It does not assert a sharp
multi-label rate, a uniform lower bound, or a finite zero-slack dictionary
for $n\ge3$. At $s=0$, and also at $n=0,1$ for this phase family, one
static name suffices even at zero excess by Theorem 93.3 and the owning
first-horizon proposition. For $n=2$ the existing zero-slack obstruction
remains; for $n\ge3$ the question whether a finite zero-excess dictionary
exists is unresolved by the present theorem.

A name in (95.2) selects a pre-supplied fixed whole CPTP map. The count
therefore measures only the declared independent static data words. It
does not provide phase acquisition, an online controller, a program
counter, quantum storage, a paid port, or a physical-cost minimum. The
same actual-channel contract continues to quantify over all complex
qutrit density inputs and one common map per selected label.

The finite phase-circle theorem leaves the individual optima
$\eta_{(q,n)}$ generally unevaluated for $n\ge3$, the finite no-reference
full-state minima and minimizers unresolved, and all sharp multi-label
rates beyond the displayed upper certificate open. The endpoint result
also leaves other task directions, finite-to-limit interchange and
whole-channel recovery outside its scope. The standing unbounded
subexponential, cutoff, entropy, strict-real joint-incidence,
ancestor-lifting, dynamic-controller and physical-resource programmes
remain unchanged.

The arguments use only the actual channel and first-horizon suppliers,
finite-dimensional Choi compactness, Haar symmetry, complete positivity,
convexity and unital operator-norm contraction. These are mature
intermediates; the model-specific constants and endpoint certificates are
proved above. The results make no worldwide novelty claim. The two supplier pins used for the correspondence are the actual-channel
and first-horizon source at revision 37142002ed7d67cdfc47940a899f4dc818f42cf3
(§§93 and 103--104) and the no-reference and stabilized full-state source
at revision 88e708c6e499168a6bf79cabb6bd08d4e62fb6fb (§§105--111, including
the exact stabilized values).

## 追加锚（本行以下为增补区）
