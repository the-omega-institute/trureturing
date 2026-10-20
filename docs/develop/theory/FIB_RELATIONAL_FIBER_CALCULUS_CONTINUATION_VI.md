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
witness question below remains unchanged.

Second, Theorem 31.1 gives a finite necessary response reduction. If one
child contains both a distinct final-\(J\) collision pair and a distinct
final-\(M\) collision pair, then

$$
Q(p_J,v)=0\quad\text{or}\quad v=s_-(p_J)\quad\text{or}\quad v=s_+(p_J),
$$

so at most \(74937\) scalar responses can support that joint collision
pattern. This is a response/action-support restriction, not an acquisition
protocol and not a finite-controller construction.

The remaining joint witness system is the one in Definition 32.1 and its
equation (32.1): for
\(F\in\{J,M\}\) and \(a\in\{0,1\}\), choose legal reconstructed worlds
\(W_{Fa}\) with

$$
0<r_{Fa}<1,\quad b_{Fa}>0,\quad
\mathsf S_{p_J}(r_{Fa},b_{Fa})=0,\quad
p(W_{Fa})=p_J,\quad u_M(W_{Fa})=v,
$$

and require simultaneously

$$
f_{MJ}(W_{J0})=f_{MJ}(W_{J1}),\quad W_{J0}\ne W_{J1},\qquad
f_{MM}(W_{M0})=f_{MM}(W_{M1}),\quad W_{M0}\ne W_{M1}.
$$

Elimination roots may be extraneous; neither feasibility nor a common legal
child follows from the scalar projections. Existence of such a witness at
one of the at most \(74937\) responses, together with the inherited
sixth-\(J\) \(L_1\) child of Theorem 8.1, would establish the local fifth-\(M\)
\(L_2\) route through Theorem 17.1. Exclusion at every candidate would
exclude every sixth-\(M\) \(L_1\) at \(p_J\). Theorem 31.1 retains singular
and degree-drop cases in the necessary candidate reduction; their
realizability or exclusion remains open. Other fifth responses, terminal
components, replacement worlds, unrestricted adaptive readers, and the
native acquisition/controller bridge also remain open.

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
collision in one child at that fixed \(p_J\). Consequently,

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
Thus the correct research order is: stratify response collisions by the
parameter and terminal action, solve the exact-\(p_J\) joint witness or its
exclusion, and only then add the acquisition, permission, successor, and
finite-controller data needed for an executable obstruction or protocol.

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
three. This establishes an attainable finite protocol under its declared
permissions, but it does not determine the minimum over all partitions,
causal controllers, shared seeds, physical registers, or arbitrary horizons.
In particular, six terminal cells and eight raw histories both still require
three bits under a fixed-length binary register.

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
