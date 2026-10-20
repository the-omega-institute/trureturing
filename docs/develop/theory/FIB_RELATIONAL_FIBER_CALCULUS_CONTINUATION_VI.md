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

Let \(Z\) be a finite target set and \(S\) a finite complete device-state set.
An admissible action \(a\) has a domain \(D_a\subseteq S\), a response map

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
words; their names are not available to the controller after they are erased.

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

For the reader in Definition 61.1 and any \(n\ge1\),

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

For the upper bound, use running states \(k_b,k_a\), with initial classes
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

A deterministic controller has a finite state set \(K\), initialization
\(c:I\to K\), action/output map \(u\), and response update \(v\). A support
\(C_k\subseteq Z\times S\) records the candidates compatible with controller
state \(k\). A rank is a map

$$
\rho:\{(z,s,k):(z,s)\in C_k\}\longrightarrow\mathbb N.
$$

### Theorem 62.2 (sound and complete finite closed-loop certificate)

Suppose initial candidates lie in \(C_{c(i)}\). Every selected action is jointly
legal on its support, every response successor lies in the support selected by
\(v\), and every non-halt successor satisfies

$$
\rho(z,T_a(s),v(k,r_a(s)))<\rho(z,s,k).
$$

Every halt output is constant on its support. Then the controller is legal,
terminates, and returns the target correctly. Conversely, for a finite
deterministic controller that succeeds and terminates on all allowed sources,
reachable supports and remaining execution lengths supply such \(C_k\) and
\(\rho\).

**Proof.** The support conditions give induction along every actual response
history. The rank cannot decrease indefinitely in \(\mathbb N\), so execution
terminates. Constancy on a halt support gives correctness. Conversely, take
the exact reachable support at each controller state and define the rank to be
the maximum remaining number of actions. Termination excludes a reachable
non-halt cycle, so this rank strictly decreases. \(\square\)

This is the execution layer missing from a static observation quotient. A
mathematical hidden coordinate may occur in \(C_k\) and \(\rho\) without being
an input available to the controller.

## 63. Relation to current FIB boundaries

The dynamic summary conditions in [Continuation V](FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_V.md)
remain necessary: legality, full response, successor, resource labels, and
updates must factor through the retained summary. The present results add the
task condition that one retained memory value must support a common protocol
for the union of all histories in that memory fiber.

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
