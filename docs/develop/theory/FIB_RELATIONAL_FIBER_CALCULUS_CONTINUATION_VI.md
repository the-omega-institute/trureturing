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
