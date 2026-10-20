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

## 七十三、取得前沿、重放纤维与历史时序纤维

最新 dev 的 [Native acquired input, the unfinished-request frontier, and actual replay](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACQUIRED_INPUT_FRONTIER_AND_REPLAY.md)
把上一节的“控制记忆”再分成三个不同问题：什么已经被实际取得，当前请求做到哪一步，以及从当前材料还能否唯一重放后续行动。三者都可以写成纤维，但它们不是同一个观察器。

### 定义 73.1：取得前沿

设 \(h\) 是一条实际执行到原子操作切点的有限历史。记：

$$
I(h)=\text{外部输入已经实际被 IN 消费的有序词},
$$

$$
\lambda(h)=\text{仍停留在输入 latch 中的已消费材料},
\qquad
\phi(h)=\text{请求、写入、响应、封存或交付阶段},
$$

并把权限、pending event、部分 frame、计数器、head、PC 和 owner 绑定一并记入

$$
\operatorname{AF}(h)=\bigl(I(h),\lambda(h),\phi(h),\operatorname{perm}(h),\operatorname{pending}(h),\operatorname{ctr}(h),\operatorname{owner}(h)\bigr).
$$

这里的 \(\operatorname{AF}\) 是**取得前沿**。若一个 bit 已被实际 IN 消费，即使它尚未 WR 到 tape，它已经属于 \(I(h)\) 和当前 latch 前沿；它不能在重放时被当作“未来输入”重新索取。

因此有严格的切面次序：

$$
\text{acquire}\;\to\;\text{latch}\;\to\;\text{write}\;\to\;\text{request complete}\;\to\;\text{seal}\;\to\;\text{deliver}.
$$

这些切面可以具有相同的最终数值，却具有不同的后继权限和不同的合法动作域。

### 定理 73.2：预测记忆必须同时分解读出和更新

设 \(m\) 是历史到记忆值的压缩，\(a\) 是允许动作。要使 \(m\) 成为下一步预测与控制的安全商，必须存在 \(\bar D_a,\bar r_a,\bar U_a\)，使得在实际历史域上：

$$
h\in D_a\iff m(h)\in\bar D_a,
$$

$$
r_a(h)=\bar r_a(m(h)),\qquad
m(h\cdot a)=\bar U_a(m(h),r_a(h)).
$$

只证明读出 \(r_a\) 可以由 \(m\) 计算，而没有证明合法域和更新也下降到 \(m\)，不能得到预测充分性。

证明是直接的：第一式保证同一记忆值不会把合法动作和非法动作混合；第二式保证同一记忆值给出相同响应；第三式保证响应之后仍落在同一个记忆系统中。反过来，若未来任务的 enabledness、response 或 successor 在同一 \(m\)-纤维上不同，则存在一对历史见证，说明该压缩不是安全控制商。

这把前一节的控制相容性判据推进了一步：

$$
\boxed{
\text{保存答案的读出}
\neq
\text{保存选择动作的记忆}
\neq
\text{保存更新后继续工作的记忆}.
}
$$

### 定义 73.3：取得键与重放键

在 dev 文档的 \(\Omega^+\) 合法历史域上，设 \(u\) 是实际安装的 source code，\(n\) 是 P owner 的实际 receipt 计数，\(I\) 是实际消费的 source-frame 输入，\(\kappa\) 是 Capture 读取的 P 切点，\(m\) 是 Capture 后 C owner 的实际进度；未 Capture 时取 \(\kappa=\bot,m=0\)。定义：

$$
K(h)=\bigl(\operatorname{code}(u),I(h),n(h),\kappa(h),m(h)\bigr).
$$

这不是一个免费安装的寄存器，而是从真实达到的 raw state 中提取的数学键。它只能在声明的实际历史像上使用。

### 定理 73.4：当前行动的精确重放纤维

在上述合法域上，dev 的精确 endpoint 纤维给出：

$$
X(h)=X(h')\iff K(h)=K(h').
$$

并且当前允许的有限实验映射相同，当且仅当这些键相同：

$$
h\equiv_{\mathrm{now}}h'\iff K(h)=K(h').
$$

所以 \(K\) 保留了当前动作所需的 source provenance、已消费输入、计数、Capture 读取切点和 C 进度；它不需要保存每一条过去的 P/C 交错历史。

### 证明

同一 \(K\) 时，固定 startup、实际输入前缀和 owner-local 进度确定正常重放代表；P 与 C 的后续行在 Capture 后满足完整 diamond，交换相邻的合法 owner 行不改变完整 endpoint。因此得到相同 raw state、同样的动作域、响应和 successor。

反向地，若当前实验映射相同，选择一个合法的下一 P 行。它的响应和完整 successor 相同，故 \(n\) 或 \(I\) 的更新相同；逐步取消这次更新得到前一键相同。Capture 的存在及其 \(\kappa\)，以及 C 的 \(m\)，由同样的 successor 递归恢复。于是 \(K(h)=K(h')\)。

这里的关键不是“保存一个摘要就能重放”，而是该摘要已经被证明同时决定合法域、响应和更新；没有这三个交换式，\((\operatorname{code}(u),I,n)\) 的短元组只是候选摘要。

### 定理 73.5：重放纤维不等于历史纤维

对一个已 Capture 的键，令

$$
p=n-\kappa,\qquad q=m-1.
$$

则同一 raw endpoint 的实际历史数为：

$$
L(K)=\binom{p+q}{p}=\binom{n-\kappa+m-1}{n-\kappa}.
$$

Armed 情形 \(m=0,\kappa=\bot\) 的纤维为单点；已 Capture 且 \(p,q>0\) 时，历史纤维通常含多个不同的 P/C 交错。

因此：

$$
\boxed{
\text{当前 continuation 可以被精确重放}
\quad\not\Rightarrow\quad
\text{完整过去 chronology 可以被恢复}.
}
$$

同一 endpoint、同一当前 storage、同一当前 boundary 和同一已取得 C backing，仍可能对应不同的总历史。若目标是 \(T_{\mathrm{exact}}\)，必须加入能够区分这些线性扩展的历史记录；若目标只是当前 continuation，则 \(K\) 已足够。

这解释了上一节中的“双不动点”为什么还不完整：

$$
\begin{aligned}
\nu\Psi&=\text{对允许动作保持不变的安全行为商},\\
\mu\Phi&=\text{有限目标的可取得域},\\
\operatorname{ReplayFib}&=\text{同一当前行动语义的最粗实际纤维},\\
\operatorname{ChronFib}&=\text{同一 endpoint 下仍未被恢复的历史线性扩展}.
\end{aligned}
$$

其中 \(\operatorname{ReplayFib}\) 可以安全合并历史，\(\operatorname{ChronFib}\) 则说明这种合并具体遗忘了什么。

## 七十四、取得前沿向可执行协议的提升

### 定义 74.1：FIB 取得—重放提升

设语义来源纤维由 \(\eta_{\mathrm{sem}}\) 给出，实际输入取得映射为 \(A\)，控制记忆为 \(m\)。称一个目标在该合同下被**可执行提升**，如果满足：

1. \(A\) 沿一条实际 owner 历史取得了目标所需的输入，而不是由数学模型事后填入；
2. \(m\) 对每个允许动作同时因子化合法域、响应和 successor；
3. \(m\) 的后继具有有限下降秩，或落入已知的有限取得层 \(\mathcal W_n\)；
4. 所有输入、封存、交付、重放和控制更新都计入实际成本。

这一定义把“语义纤维有限”与“观察者能执行”分开。

### 定理 74.2：有限语义纤维的提升判据

若 \(\eta_{\mathrm{sem}}\) 的目标纤维有限，但缺少第 74.1 条的实际取得或 successor 因子化条件，则不能推出存在有限协议。

若第 74.1 条全部成立，并且取得键 \(m_0\) 属于 \(\mathcal W_n\)，则从该实际历史开始可以提取一个至多 \(n\) 次语义操作的 FIB 控制协议；其控制状态至少保存 \(m\) 所区分的历史类，并沿每个实际响应更新到下一个键。

### 证明

前一方向由破坏性读出反例直接给出：潜在响应联合可以单射，而一次实际读出把不同目标压到同一终止状态，故没有有限协议。

后一方向先用实际取得映射把来源推进到 \(m_0\)，再用有限取得层的递归提取动作。读出、更新因子化保证每个动作在原合同中可执行，秩下降保证有限终止；FIB 无损编码只负责保存控制状态和证书，不增加隐藏观察能力。

### 定理 74.3：dev 的两 owner 采集桥是一个条件性提升

最新 dev 的 §12 在新增的、与原 apparatus 分离的 \(A_R\) 上，给出一个明确的提升实例：在每个实际到达的 pre-Pin Armed collector 状态，两个同时绑定的 meter endpoint、已取得的 source/code capsule、以及对已达到输入前缀的逐 bit demand，足以构造

$$
K_R(x)=K(\pi(x))
$$

并在真实付费 startup、word/effect interpreter、copy、seal、ACK 和调用 token 返回之后，得到完整状态重建

$$
\mathcal L_R(K_R(x))=x.
$$

这不是原 apparatus 的免费逆，也不是“两个 meter 数值就足够”。成立条件包括：新增 disjoint scaffold、实际 Pin、owner 权限、canonical code/seed loader、已有输入前缀的合法 demand、完整十五 slot successor、以及每个调用阶段的 progress 条件。

### 推论 74.4：采集边界可以小于完整快照，但不能小于实际控制边界

在 \(A_R\) 的声明域内，完整 raw snapshot 可以被压缩成两个 endpoint 绑定、source/code provenance、实际输入前缀、计数与 Capture 状态，再通过付费重放恢复；但删除其中任何一个会产生具体风险：

$$
\begin{array}{c|c}
\text{删除项}&\text{失去的性质}\\ \hline
\text{实际输入前缀}&\text{无法重放 source IN 的真实 successor}\\
\text{latch/partial-frame frontier}&\text{把已消费但未 WR 的 bit 错当成未来输入}\\
\text{Capture 切点}&\text{不同 meter root 的后续输出被错误合并}\\
\text{owner/permission}&\text{数学内容存在但当前调用未授权}\\
\text{完整 successor 更新}&\text{读出可算而控制器不能继续闭环}\\
\text{实际费用与进度}&\text{有限代码被误报为统一有限成本}
\end{array}
$$

因此，FIB 的最小充分边界现在应写成：

$$
\boxed{
\text{语义读出}
\subseteq
\text{取得前沿}
\subseteq
\text{当前重放键}
\subseteq
\text{完整历史记录}.
}
$$

每一步都是相对于任务的偏序：恢复当前动作时可以停在重放键，恢复完整 chronology 时必须继续保留历史 supplement。

## 七十五、结合最新 dev 后的剩余边界

现在可以把项目的新进展准确放回 FIB 理论：

1. Native acquired input 解决了“输入何时成为观察者已有信息”的接口问题：答案是实际 IN 的 acquired cut，而不是 WR、seal 或事后 replay 的时刻。
2. Exact joint endpoint fibres 解决了“什么可以被当前动作安全遗忘”的问题：在声明的 \(\Omega^+\) 域，\(K=(\operatorname{code}(u),I,n,\kappa,m)\) 是当前 continuation 的精确键。
3. Chronological ambiguity 解决了“精确重放是否等于精确历史恢复”的问题：不是；其剩余歧义由 \(\binom{n-\kappa+m-1}{n-\kappa}\) 明确计数。
4. Paid two-meter acquisition 解决了“语义键能否成为实际可调用记录”的一个条件实例：能，但需要新增 apparatus、真实输入、权限、loader、successor 和费用合同。
5. Growing \(\xi\) 的最新算术校准目前仍属于成本模型支线。只有建立其非线性 price 与 FIB 协议的实际动作/资源坐标映射后，才能把它纳入上述提升定理；当前不能把该校准当成 FIB 几何或控制记忆的新增闭合结果。

所以目前最强的统一结论是：

$$
\boxed{
\begin{gathered}
\text{有限语义纤维给出候选世界；}\\
\text{取得前沿给出观察者实际拥有的输入；}\\
\text{重放键给出当前可继续行动的最小充分边界；}\\
\text{历史纤维说明被压缩掉的 chronology；}\\
\text{付费采集桥把该键提升为可调用协议，但只在声明 apparatus 上成立。}
\end{gathered}
}
$$

仍然开放的不是“有没有更多符号可以编码”，而是更具体的合同问题：原固定 apparatus 是否存在同样的全域采集桥；任意 busy cut 是否有统一的 acquired-input frontier；完整 \(T_{\mathrm{exact}}\) 在不增加历史 supplement 时能否恢复；以及在给定误差、费用和控制状态预算下的全局最小控制器是什么。最新 dev 把这些问题的边界写得更细，但没有把条件性桥梁升级成这些全域结论。
