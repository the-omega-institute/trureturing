# Native hidden-phase testing with paid original-root Reads

> **Source convention.** This is a `generic-v1` reference theory volume.
> Its numbered claims have their proofs in this source. Once published,
> existing source bytes remain fixed; additions and corrections belong in
> numbered sections after the terminal append anchor.

## 1. Scope, inherited premises and the testing question

**Convention 1.1 (ordinary proof and contribution).** This volume gives
ordinary finite mathematical proofs, without Lean-kernel verification.
It establishes an exact binary testing experiment for the actual native
family supplied by [OCC][OCC]. The new deductions relative to that entire
volume are the optimal risk at every paid Read budget, a full-native-tuple
simulation covering all adaptive literal-word policies, its attained
sufficient experiment, and the extension to independent whole sources
conditional on one common hypothesis. The native family, balanced block
law, alternative completion and merged export are credited inputs.
Bayes minimization, total variation, sufficiency, Blackwell comparison
and deferred revelation are mature methods used here with explicit
proofs. No claim of worldwide originality is made.

**Convention 1.2 (parameters and distinct budgets).** Throughout,
$m,d,\ell$ are integers with $m,d,\ell\ge2$, $\epsilon$ is rational
with $0<\epsilon<1$, $k$ is a nonnegative integer, and
$t=\min\{k,\ell\}$. A single hypothesis $\Theta\in\{P,Q\}$ has equal
prior probabilities. Conditional on it, one whole actual source is drawn
and remains stationary during preparation and testing. The quantity $k$
is a charged online Read budget. It is neither the owner-resampling
budget in OCC §5.3 nor a substitution count in a temporal prediction
problem. No substitution is performed on the source during testing.
The optional number $n$ of fresh whole sources is introduced in §8.

**Assumption 1.3 (precisely inherited mathematical interfaces).** The
native full temporal factors, their separation of canonical blocks,
the complete owned-seed/template representation with total guards and
unique actual lifts, and the full-family canonical preparation service
are those stated in OCC §§1.2–1.4, 2.1, 4.1–4.2 and 7.1–7.2.
The relevant source is
`docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_OWNER_COMPONENT_COMPLETION.md`
at revision `ce2fe4a685b5a195b8b0a380616daf0151f576cb`.
The explicit factors and gadget prescriptions needed below are restated
in §2, and their consequences for the entire native laws are proved
there and in §3. The nested suppliers cited by OCC for reconstruction,
lifting, temporal factors, canonicalization and paid preparation are
inherited premises; their underlying sources are not independently
verified here. In particular the testing laws below concern the exact
canonical scaffold support, rather than arbitrary noncanonical members
of a canonicalization inverse fiber.

**Assumption 1.4 (complete access and separately paid isolation).** The
sampled sources lie in the canonical merged fiber described in §4. The
complete accessible export before testing is its single constant name.
Public block ordering, scaffold, templates, weights, distributions and
installed tables are source-independent. Every other preparation
dependence is inaccessible by the declared, separately paid handoff
and access-isolation service. This includes scan transcripts, timing,
lengths, selectors, control, allocation, handles and buffers. Every
accessible surviving preparation field is a function of that complete
name and public data.

The only online source replies are charged Reads of finite literal
words from the original root, with alphabet
$\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$. There is no
source-identity, subtree, joint-read, free-navigation, reset, copying or
advice port. No authentic count later supplies source information.
Source acquisition, preparation, isolation, table generation and
installation, storage, computation, control, workspace, address letters,
randomness and physical time retain separate costs. Isolation is a
premise about accessibility, not a physical erasure construction.

**Definition 1.5 (legal policy and risk).** A legal policy terminates
with a decision $\widehat\Theta$ after at most $k$ charged Reads. Each
chosen finite word, stopping and decision depend only on public data,
previous replies and accessible internal state. A private random tape
independent of both $\Theta$ and the whole source may be allowed as a
separately declared and paid service. The attaining policies below are
deterministic. The transcript includes submitted words, replies,
stopping, accessible state and decision. Its equal-prior error is

$$
R(\pi)=\frac12\Pr_P(\widehat\Theta=Q)
       +\frac12\Pr_Q(\widehat\Theta=P),
\qquad R^*(k)=\inf_{\pi}R(\pi).
$$

There is no computation bound beyond the interface and Read budget.
Thus the converse also covers arbitrary source-independent private
computation and arbitrary finite word lengths.

## 2. The original native blocks and their full conditional laws

**Definition 2.1 (trees, factors and canonical states).** Write
$A=\alpha$, $B=\beta$ and $C_0=\langle A,A\rangle$. Pairing is
free and ordered. Put

$$
S_1=\{A,B,C_0\},\qquad
S_{d+1}=\{A,B\}\sqcup\{\langle u,v\rangle:u,v\in S_d\},
\qquad W_d=\{q\in\{L,R\}^*:|q|\le d-1\}.
$$

Write $\varnothing$ for the empty word. A Read reports the leaf label
or branch at its endpoint, and absent if traversal has already passed a
leaf. To specify the inherited native
factors explicitly, let $e(A)=0,e(B)=1$. If $q$ ends at an original
branch, $\Gamma_q(u)=(0,0)$. Otherwise write $q=av$, where $a$ is
the path to its first original leaf $z$. Then

$$
\Gamma_q(u)=
\begin{cases}
(2-e(z),1-e(z)),&v\text{ is empty},\\
(\#L(v)+2\#R(v)+2-e(z),\mathbf1_{\{v\text{ ends in }R\}}),
  &v\text{ is nonempty}.
\end{cases}
$$

The factor vector on $W_d$ separates $S_d$, as stipulated in
Assumption 1.3. In particular root factors distinguish a branch from
both leaves, and

$$
\Gamma_{\varnothing}(A)=(2,1),\quad
\Gamma_{\varnothing}(B)=(1,0),\quad
\Gamma_L(A)=(3,0),\quad\Gamma_L(B)=(2,0).
$$

**Definition 2.2 (the exact $11m$-block gadget).** Indices $i$ are
modulo $m$. Use Boolean variables $x_i,a_i,b_i$ and the two ordered
positive exact-one clauses

$$
(x_i,a_i,b_i),\qquad (x_{i+1},a_i,b_i)
\quad (i=1,\ldots,m).
$$

Boolean zero is the actual leaf $A$, and Boolean one is $B$. Each
of the $3m$ variables has its own original owner block. Each of the
$2m$ clauses has its own selector-owner block, with states
$u_0=A,u_1=B,u_2=C_0$ for selected positions $0,1,2$. Each of the
three positions of each clause has an original connector block. Hence
there are $3m+2m+6m=11m$ original blocks and $5m$ actual root-owned
seeds. A connector owns no seed.

All factors of a variable-owner block are those of its leaf seed. All
factors of a selector-owner block are those of $u_c$. A connector at
position $h$ of a clause with selector $c$ and variable leaf $v$ has

$$
z_{\varnothing}=\Gamma_{\varnothing}(v),\qquad
z_L=\Gamma_L(B\text{ if }c=h\text{, else }A),\qquad
z_R=\Gamma_R(v).
$$

For $d>2$, every additional connector factor is $\Gamma_q(v)$;
additional variable and selector factors also come from their same
actual leaf or $u_c$. Each occurrence refers to its original owner,
including the two distinct selector owners belonging to the two clauses
at an edge. Occurrences are not independent variables.

These are complete templates with attained-range total tables, not
Boolean restrictions supplied through another source port. The Boolean
root decoder fixes alpha and beta and sends branch and absent to the
root factor of $A$. The selector root decoder fixes the three displayed
states and sends absent to the root factor of $A$. Other off-domain
table entries can be filled with attained factors. A fixed-point Boolean
owner cannot have a branch root under its guard; a selector can have
exactly its three stated roots. The inherited representation identifies
these template solutions with their actual owned-seed lifts.

**Lemma 2.3 (complete actual support).** The gadget has one phase-one
tuple $g_1$ and $2^m$ phase-zero tuples $g_0(e)$, indexed by
$e=(e_1,\ldots,e_m)\in\{a,b\}^m$. In phase one all $x_i=1$
and all $a_i=b_i=0$. In phase zero all $x_i=0$, with
$(a_i,b_i)=(1,0)$ when $e_i=a$ and $(0,1)$ when $e_i=b$.
Each such Boolean assignment has exactly one actual native lift.
Every block in every lift is $A,B$ or $C_0$. The two selectors at
edge $i$ are both $A$ in phase one, both $B$ for phase-zero
choice $a$, and both $C_0$ for choice $b$. Every connector is its
incident variable leaf.

Proof. A Boolean owner is the leaf determined by its root seed: its
whole factor vector is that leaf's, and separation leaves no alternative
canonical block. The same argument makes a selector the indicated
$u_c$. At a connector, the root factor is one of the two nonbranch
leaf factors. Therefore its actual block is that variable leaf. The
left prescription agrees with this leaf exactly when its Boolean value
is $\mathbf1_{\{c=h\}}$, since $\Gamma_L(A)\ne\Gamma_L(B)$.
Its right and additional factors then agree as well. Applying this to
all three positions forces exactly the selected variable to be true.
Thus native compatibility is precisely the exact-one clause requirement, with no
remaining connector freedom. Conversely a satisfying assignment fills
all these actual blocks consistently and uniquely. Additional factors
for $d>2$ are factors of the very same blocks, so neither exclude these
lifts nor create others.

The two clause equations at edge $i$ are
$x_i+a_i+b_i=1$ and $x_{i+1}+a_i+b_i=1$. Subtraction gives
$x_i=x_{i+1}$; cycling gives one common $x$ value. Value one
forces both auxiliaries zero. Value zero allows exactly the two stated
choices at each edge, without any further condition between edges.
This remains valid at $m=2$, where every displayed clause still has
three distinct variables. The selectors and connectors therefore have
exactly the stated actual shapes. This proves both solution directions,
the count and uniqueness. $\square$

**Definition 2.4 (unchanged whole-block weights).** Set
$L_d=|S_d|+9$ and give the entire $S_d$ the positive rational law

$$
w(A)=5,\quad w(B)=3,\quad w(C_0)=4,\quad
w(u)=1\ (u\notin\{A,B,C_0\}),\qquad \mu_d=w/L_d.
$$

The sum is $|S_d|+9$ because the increases over unit weights are
$4,2,3$. On each gadget use the product of its $11m$ original
whole-block $\mu_d$ factors, each exactly once, including all
connectors. A phase, seed occurrence, mixture marker, scaffold position
or analytical cache receives no new weight factor.

**Lemma 2.5 (full native $K_0,K_1$ laws).** Both phases have original
unnormalized mass

$$
\tau_{m,d}=\frac{5^{8m}3^{3m}}{L_d^{11m}}.
$$

The full actual tuple conditional on phase one has law $K_1=\delta_{g_1}$.
Conditional on phase zero its law is

$$
K_0(g_0(e))=\prod_{i=1}^m\nu(e_i),\qquad
\nu(a)=\frac9{25},\quad\nu(b)=\frac{16}{25}.
$$

These are laws of all $11m$ actual blocks, including selectors and
connector shapes.

Proof. In either phase exactly $m$ variables are true and $2m$ are
false, so the variable owners contribute raw product $5^{2m}3^m$.
Each variable appears in two clauses and has two connectors equal to
its leaf, so connectors contribute $5^{4m}3^{2m}$. In phase one
all $2m$ selector blocks are $A$, adding $5^{2m}$. This gives
$5^{8m}3^{3m}$ and the denominator $L_d^{11m}$.

For phase zero, the selector pair at edge $i$ contributes $9$ for
choice $a$ and $16$ for choice $b$. Write $h(a)=9,h(b)=16$.
The weight of its entire unique lift is therefore

$$
L_d^{-11m}5^{6m}3^{3m}\prod_{i=1}^m h(e_i).
$$

Expanding the product of the $m$ two-term sums, its sum over all
edge choices is

$$
L_d^{-11m}5^{6m}3^{3m}(9+16)^m
  =L_d^{-11m}5^{8m}3^{3m}=\tau_{m,d}.
$$

Dividing each row by this phase sum gives the displayed $K_0$.
The factorization proves conditional edge independence for this precise
full-tuple law. It does not assert independent clause occurrences or
independence for arbitrary native relations. The other phase is a
singleton, proving its $K_1$ law. $\square$

## 3. Two hypotheses on the same entire actual relation

**Definition 3.1 (whole-source tuple laws).** Take $\ell$ disjoint
copies of Definition 2.2, retaining $N=11m\ell$ original blocks.
Let $G_j$ be the full tuple in copy $j$, $F_j\in\{0,1\}$ its
phase, and $W$ the unchanged product of all $N$ block factors.
Let $P=W/Z$ on the Cartesian product of the actual gadget relations.
Define a second law by its full phase law and full conditional law:

$$
q=(1-\epsilon)\frac{\delta_{0^\ell}+\delta_{1^\ell}}2
      +\epsilon\operatorname{Unif}(\{0,1\}^\ell),
\qquad Q_F=q,\qquad Q(\,\cdot\mid F)=P(\,\cdot\mid F).
$$

This last equality specifies the entire joint conditional law, rather
than only its individual marginals. $Q$ is the alternative completion
of OCC §5.3. It is not asserted to be the Gibbs law of the unchanged
$W$.

**Proposition 3.2 (common full conditional kernel and exact phase laws).**
The partition function is $Z=(2\tau_{m,d})^\ell$. Under $P$ the
phases are independent fair bits. For either hypothesis, for every
phase vector $f$ and compatible native tuple $g$,

$$
\Pr_\Theta(G_1=g_1,\ldots,G_\ell=g_\ell\mid F=f)
       =\prod_{j=1}^\ell K_{f_j}(g_j).
$$

Both laws are strictly positive on the same $(2^m+1)^\ell$ actual
tuples, and both give each entire gadget marginal $(K_0+K_1)/2$.

Proof. Disjointness gives a Cartesian product of actual relations and
a product of their original weights. Successive finite summation
therefore factors the partition sum into $\ell$ one-gadget sums.
Lemma 2.5 gives each sum $2\tau_{m,d}$ and each phase mass one
half after normalization. This proves the product law under $P$,
including its full conditional formula. Definition 3.1 transfers that
very full conditional to $Q$. Each $q(f)>0$ and all native
conditional weights on their respective supports are positive, proving
the support assertion. Every coordinate of $q$ is fair: both the
common-bit part and the uniform part have that marginal. Averaging
the full conditional formula over the other phases therefore gives
$(K_0+K_1)/2$ for each gadget under both laws. It does not make
$Q$'s different phases independent. $\square$

**Lemma 3.3 (analytical mixture representation).** $P$ is generated by
independent fair phases followed, given all phases, by independent
full tuple draws $K_{F_j}$. $Q$ has the following representation:
with probability $\epsilon$ use that independent-phase construction;
with probability $1-\epsilon$ choose one fair bit $B$, set all
phases to $B$, and independently draw the full tuples from $K_B$.

Proof. The first assertion is Proposition 3.2. In the second
construction the phase vector has exactly $q$; conditional on any
phase vector, both mixture components use the identical product native
kernel in Proposition 3.2. Summing the two component probabilities
therefore gives exactly Definition 3.1 on every actual tuple.
$\square$

The marker and bit used in this representation are latent mathematical
variables for one whole stationary source. They do not add a seed,
weight owner, operational randomization service or source-draw port.

## 4. Canonical sources and every finite original-root word

**Definition 4.1 (actual ordered scaffold).** Put

$$
H=\lceil\log_2N\rceil,\qquad K=2^H,\qquad D=H+d.
$$

At a public ordered frontier of a perfect height-$H$ binary scaffold,
place the $N$ original blocks and $K-N$ fixed $A$ padding blocks.
Let $u$ be the resulting right subtree and $T=\langle A,u\rangle$
the original source. A position $b$ has a public address
$a_b\in\{L,R\}^H$ within $u$. The source lies in
$\mathcal F_D=\{\langle A,v\rangle:\operatorname{ht}(v)\le D\}$,
and $u\in S_D$. Ordered pairing makes the scaffold map injective:
its ordered frontier subtrees recover the inserted tuple. Consequently
$P,Q$ on sources are the injective pushforwards of their tuple laws.
No scaffold constructor or padding block is a new random weight owner.

**Lemma 4.2 (all-word locality with complete native shapes).** Every
finite original-root word has either a public constant reply or a
reply that is a deterministic function of one full actual gadget tuple
$G_j$. The frontier position and hence that gadget label are determined
by the literal word and public ordering, independently of hidden values.
This holds for all word lengths, absent suffixes and repeated visits.

Proof. The empty word reports branch. The word $L$ reports alpha,
and every longer word beginning with $L$ reports absent. A word
beginning with $R$ with fewer than $H$ subsequent letters ends at a
fixed scaffold branch. Once $H$ letters after $R$ have been supplied,
they select one fixed frontier position $b$. Any remaining suffix
stays inside that one frontier block. Descending a tree cannot move
from that block into a sibling or another gadget.

For completeness, the entire possible local reply behavior is

$$
\begin{array}{c|ccc}
\text{block}&\text{empty suffix}&\text{suffix }L\text{ or }R
                                      &\text{suffix length }\ge2\\ \hline
A&\alpha&\mathsf{absent}&\mathsf{absent}\\
B&\beta&\mathsf{absent}&\mathsf{absent}\\
C_0&\mathsf{branch}&\alpha&\mathsf{absent}
\end{array}
$$

These cases cover every finite suffix. Lemma 2.3 says every original
block has one of these shapes; padding is fixed $A$. Hence a query
entering an original block is a deterministic function of its gadget's
full tuple, even if that particular function is constant. Queries to
the scaffold, left leaf and padding are public constants. This also
proves consistency of revisits, since they evaluate the same function
on the same stationary tuple. In particular a selector branch is not
silently replaced by a Boolean leaf. $\square$

**Proposition 4.3 (actual acquisition of fixed phases).** The phases
of any fixed $s$ distinct gadgets, $0\le s\le\ell$, can be acquired
with $s$ charged original-root Reads, each of length $H+1\le D$.

Proof. Fix an actual $x_1$-owner block in each chosen gadget, at
frontier position $b(j)$. Submit the literal word
$w_j=Ra_{b(j)}$ from the original root. Every prefix down to this
frontier is actually present by construction. The endpoint is its
actual owner block, $A$ in phase zero and $B$ in phase one by
Lemma 2.3. The alpha/beta reply therefore recovers $F_j$ exactly.
This is a present original-root word, without any subtree input or
artificial root. Its length is $H+1\le H+d=D$. The empty list
handles $s=0$. $\square$

## 5. Full-native simulation of every adaptive testing policy

**Definition 5.1 (the phase experiment).** Let $E_s$, $0\le s\le\ell$,
reveal the phases of $s$ fixed distinct public gadgets in fixed order.
At $s=0$ its sole outcome is the empty vector under both hypotheses.
For $s\ge1$ its two laws on $\{0,1\}^s$ are

$$
p_s=\operatorname{Unif}(\{0,1\}^s),\qquad
q_s=(1-\epsilon)\frac{\delta_{0^s}+\delta_{1^s}}2+\epsilon p_s.
$$

These follow by marginalization of the phase laws, without modifying
any conditional native tuple law.

**Theorem 5.2 (all-policy cached-full-tuple comparison).** For every
legal adaptive policy $\pi$ with at most $k$ Reads there is one
hypothesis-independent probability kernel $S_\pi$ from $E_t$ to its
complete transcript and decision such that

$$
\operatorname{Law}_P(\mathrm{transcript}_\pi)=p_tS_\pi,\qquad
\operatorname{Law}_Q(\mathrm{transcript}_\pi)=q_tS_\pi.
$$

Here $t=\min\{k,\ell\}$. In particular the kernel preserves all
within-gadget native nuisance, repeated-query consistency, adaptive
choice of gadget labels, arbitrary suffixes and stopping.

Proof. On input $Y=(Y_1,\ldots,Y_t)$, run the same policy with
its public inputs and, if allowed, its independent private random tape.
Maintain a dictionary indexed by touched gadget labels. Answer public
constant queries by Lemma 4.2. When a query first enters an uncached
original gadget $j$, let $r$ be its ordinal among first-touched
labels. Assign $F_j=Y_r$, draw once a complete actual tuple with
law $K_{Y_r}$, and cache that entire tuple. Answer this and every
later query to $j$ by its actual literal-word reply on the cached
tuple. Record all submitted words, replies, state, stopping and decision.
A query entering a gadget can be treated this way even if its own reply
happens to be constant. There is at most one new label per charged
Read, so at most $k$ new labels and at most $\ell$ in total.
Thus no more than $t$ input coordinates are needed. Ignore unused
coordinates.

All auxiliary draws use the known native $K$ laws and randomness
independent of the input. This defines a probability kernel depending
only on $Y$ and public data, without inspecting $\Theta$ or any
mixture marker. It remains to prove its exact law for adaptive label
selection; matching endpoint marginals alone would not suffice.

First consider the independent-phase construction of Lemma 3.3 and
condition on the policy's independent random tape. Enlarge the observed
history to include the full pair $(F_j,G_j)$ at each touched label.
Initially all untouched pairs are independent, each a fair phase
followed by its full $K$ tuple. Suppose that assertion holds at a
history. If the next query reaches a new label, that label is a
function of the history, since the actual policy uses only its observed
part. Selection has therefore not inspected an untouched pair.
Conditional on that history and the selected unused label, its pair
has the same fresh law and is independent of the remaining untouched
pairs. Revealing the entire selected pair preserves the assertion for
the other labels. Constants, repeats and stopping use only already
revealed data and preserve it as well. Induction proves that the
first-touch pairs have exactly the ordered independent-phase and
conditional-native draws used by the kernel.

Now consider the common-phase construction and additionally condition
on its common bit $B$. Every untouched phase equals $B$, and all
untouched tuples are independent $K_B$ tuples. The identical induction
applies: an adaptively selected unused label still has that fresh
conditional tuple law. Thus its first-touch sequence has precisely a
constant phase vector followed by independent $K_B$ tuple draws.

Under $P$, the input $Y$ has the independent fair phase law.
Under $Q$, its entire joint law is the mixture $q_t$ of the two
modes just considered. Average the modewise identities, and then the
independent policy tape if present, to obtain the two stated transcript
identities with the same $S_\pi$. Random stopping returns the same
history prefix and is included in the induction. Choices informed by
selector shapes or other native nuisance are functions of the enlarged
history and are covered.

In particular the $Q$ phases have not been replaced by independent
fair bits: their correlation is carried by the single input vector
$Y$. A touched edge, selector or gadget is never redrawn on a revisit.
This full-tuple cache is a mathematical probability kernel for experiment
comparison. It grants no operational randomness, copies, subtrees,
source draws or advice to the tester. $\square$

**Corollary 5.3 (attained optimal experiment and total variation bound).**
$E_t$ dominates every legal $k$-Read policy by a common probability
kernel and is itself acquired by legal Reads. Therefore the optimal
binary testing problem for that budget is exactly $E_t$. For any such
policy the total variation of its complete transcript laws is at most
$\operatorname{TV}(p_t,q_t)$, where

$$
\operatorname{TV}(p,q)=\sup_A|p(A)-q(A)|=\frac12\sum_y|p(y)-q(y)|.
$$

Proof. Proposition 4.3 acquires $E_t$ with $t\le k$ Reads.
Conversely any decision from a policy transcript, composed with
$S_\pi$, is a randomized decision from $E_t$ with the same two
errors. This proves equality of optimal risks. For the stronger
transcript bound, let $A$ be a transcript event. Its probability
difference is

$$
\sum_y(p_t(y)-q_t(y))S_\pi(A\mid y).
$$

Each kernel entry lies in $[0,1]$. The signed masses $p_t-q_t$
sum to zero, so their total positive mass equals their absolute total
negative mass. The event consisting of the positive-difference outcomes
attains that mass, and no event exceeds it; it equals both the event
supremum and half the absolute-mass sum defining total variation.
Weighting by numbers in $[0,1]$ bounds the displayed expression
between the negative and positive of that value. Taking the supremum
proves the bound. This is an attained comparison of experiment classes;
it does not say that each weaker individual policy can recover $E_t$.
$\square$

The same proof applies to any policy confined to at most $s$ distinct
gadgets, even with more local Reads: only $s$ phase coordinates are
needed. Thus arbitrarily detailed observation of one stationary gadget
has identical law under the two hypotheses, as also follows from
Proposition 3.2.

## 6. Exact risk, sufficient statistic and boundary cases

**Lemma 6.1 (finite Bayes identity).** For finite observation laws
$p,q$ and equal priors, the minimum error over all randomized decisions
is

$$
\frac12\sum_y\min\{p(y),q(y)\}
       =\frac{1-\operatorname{TV}(p,q)}2.
$$

A minimizing rule chooses $Q$ where $q(y)>p(y)$, chooses $P$
where $p(y)>q(y)$, and can break ties arbitrarily.

Proof. At outcome $y$, choosing $P$ contributes $q(y)/2$ to
the prior-averaged error, whereas choosing $Q$ contributes $p(y)/2$.
Randomization forms a convex combination of these contributions and
cannot beat their minimum. Sum the pointwise minima. Finally
$\min\{p,q\}=(p+q-|p-q|)/2$ pointwise, and both laws sum to
one, yielding the stated total variation identity. $\square$

**Proposition 6.2 (all-equal sufficiency).** For $t\ge2$, put

$$
A_t=\{0^t,1^t\},\quad C_t=\mathbf1_{A_t},\quad
c_t=2^{1-t},\quad b_t=1-\epsilon+\epsilon c_t,\quad
 a_t=\frac{b_t}{c_t}=\epsilon+(1-\epsilon)2^{t-1}.
$$

$C_t$ is sufficient for the binary experiment $E_t$. Its laws are
Bernoulli$(c_t)$ under $P$ and Bernoulli$(b_t)$ under $Q$.
The likelihood ratio $q_t/p_t$ is $a_t>1$ on $A_t$ and
$\epsilon<1$ outside it.

Proof. Every string has $p_t(y)=2^{-t}$. Its $q_t$ probability
is $(1-\epsilon)/2+\epsilon2^{-t}$ on the two constant strings,
and $\epsilon2^{-t}$ on the other $2^t-2$ strings. Division
proves the ratios, and summation gives the Bernoulli probabilities.
Both events have positive probability under both hypotheses since
$t\ge2$ and $0<\epsilon<1$. Under either law, conditional on
$C_t=1$, the vector is uniform on the two constant strings; conditional
on $C_t=0$, it is uniform on the nonconstant strings. These common
conditional laws define a hypothesis-independent reverse kernel from
$C_t$ to $Y$. Since $C_t$ is already a function of $Y$, it
loses no information for this binary pair. $\square$

**Theorem 6.3 (exact native testing curve).** Under Assumptions 1.3–1.4,
for every legal budget $k$ and $t=\min\{k,\ell\}$,

$$
R^*(k)=
\begin{cases}
\frac12,&t\le1,\\
\frac\epsilon2+(1-\epsilon)2^{-t},&2\le t\le\ell.
\end{cases}
$$

Equivalently $R^*(k)=\epsilon/2+(1-\epsilon)2^{-\max\{1,t\}}$.
The greatest attainable total variation of complete transcript laws is

$$
\operatorname{TV}^*(k)=
\begin{cases}
0,&t\le1,\\
(1-\epsilon)(1-2^{1-t}),&t\ge2.
\end{cases}
$$

Success probability above $1/2$, and error reduction below $1/2$,
each equal $\operatorname{TV}^*(k)/2$. The largest difference
between the $Q$- and $P$-probabilities of accepting $Q$ equals
$\operatorname{TV}^*(k)$ itself.

Proof. $E_0$ has the same empty outcome under both laws. At $t=1$
the common fair bit and an independent fair bit have the same law,
so $p_1=q_1$. Theorem 5.2 therefore makes every zero- or one-Read
transcript hypothesis-indistinguishable, and a fixed guess attains error
$1/2$ with no Reads.

For $t\ge2$, Corollary 5.3 reduces the entire native problem to
$E_t$. Proposition 6.2 and Lemma 6.1 choose $Q$ on $A_t$ and
$P$ otherwise. The conditional $P$-error is $c_t$, and the
conditional $Q$-error is $1-b_t=\epsilon(1-c_t)$. Consequently

$$
R^*(k)=\frac{c_t+\epsilon(1-c_t)}2
      =\frac\epsilon2+(1-\epsilon)2^{-t}.
$$

The positive mass of $q_t-p_t$ is concentrated on $A_t$, with
total $b_t-c_t=(1-\epsilon)(1-2^{1-t})$. This gives its total
variation. Proposition 4.3 makes the phase experiment an actual native
transcript, so the converse total variation bound is also attained.
The success and acceptance-difference conventions now follow from
Lemma 6.1 and the definition of total variation. Randomized decisions
cannot improve these values by its pointwise argument.

Every phase vector has an actual lift by Lemma 2.3, and both laws
are positive on the same native support by Proposition 3.2. Hence all
events and likelihoods used in this calculation are actual attainable
observations. The empty case was treated separately: $2^{1-t}$ is
not the all-equal event probability at $t=0$. $\square$

**Corollary 6.4 (strict improvements, exact worst-case budget and
saturation).** For $2\le u\le\ell$,

$$
R^*(u-1)-R^*(u)=(1-\epsilon)2^{-u}>0.
$$

Thus attaining the budget-$u$ optimum requires worst-case Read budget
at least $u$. For $k\ge\ell$ the optimum saturates at
$\epsilon/2+(1-\epsilon)2^{-\ell}>0$. Already two distinct
phase-root Reads give success advantage $(1-\epsilon)/4$.

Proof. Subtract the two values in Theorem 6.3, including its
$R^*(1)=1/2$ value when $u=2$. A policy with smaller worst-case
budget is bounded by the strictly larger preceding optimum. Conversely
the attaining list uses exactly $u$ Reads on its all-equal paths.
Such paths have positive probability under both laws. Once all $\ell$
phases are available, the entire native tuple has a common conditional
generation kernel under both hypotheses by Proposition 3.2. Acquiring
that entire tuple cannot improve testing beyond $E_\ell$, whose
phases its $x$ roots already reveal. This also proves saturation even
if arbitrary further Reads are allowed. Substitute $t=2$ for the
advantage assertion. $\square$

**Proposition 6.5 (descriptor recovery is a different task).** Exact
output of every actual phase on every source of the merged canonical
fiber requires at least $\ell$ Reads on each terminating deterministic
execution, and $\ell$ actual phase-root Reads suffice. This does not
impose a $\ell$-Read prerequisite on binary statistical advantage.

Proof. By Lemma 4.2 each queried word enters at most one gadget.
If an execution never enters gadget $j$, replace that gadget by any
valid opposite-phase native tuple and leave all other blocks fixed.
The merged name is unchanged. Every reply along the original execution
is unchanged, so induction gives the same next word, stopping and
output on the modified source. Its required full phase descriptor is
different, a contradiction. Thus each execution must enter all gadgets.
Proposition 4.3 attains that task with $\ell$ Reads. In contrast,
Theorem 6.3 gives positive statistical advantage from just two phases,
and even all phases leave nonzero hypothesis error. The descriptor
argument is not the statistical converse; that converse is Theorem 5.2.
$\square$

**Convention 6.6 (parameter boundaries).** The proofs apply at every
$m,d\ge2$, including the smallest gadget and canonical depth. Although
$m,d$ determine the native tuples, conditional nuisance and source
costs, their common conditional law removes them from the risk formula.
If $\ell=1$ is admitted, $P=Q$ and the risk is always $1/2$.
At the excluded endpoint $\epsilon=1$ the laws also coincide. At
the excluded endpoint $\epsilon=0$, for $t\ge1$ the one-source
risk is $2^{-t}$: under $P$, all phases can still agree. At $t=0$
it remains $1/2$. Endpoint statements follow directly from the phase
laws and the same pointwise Bayes argument; strict positivity and the
positive-event reverse kernels above were asserted only in the stated
open $\epsilon$ range.

**Example 6.7 (full native symbolic two-copy instance).** Take $m=2$,
any $d\ge2$, $\ell=2$ and $\epsilon=1/4$. For a gadget, order
the phase-zero native tuples as $aa,ab,ba,bb$ and put $g_1$ last.
Lemma 2.5 and the fair phase give its entire-tuple probabilities

$$
p=\frac1{1250}(81,144,144,256,625).
$$

For actual gadget rows $g,h$, the complete source tuple laws are

$$
P(g,h)=p(g)p(h),\qquad
Q(g,h)=
\begin{cases}
\frac74p(g)p(h),&F(g)=F(h),\\
\frac14p(g)p(h),&F(g)\ne F(h).
\end{cases}
$$

Indeed the phase law of $Q$, in order $00,01,10,11$, is
$(7/16,1/16,1/16,7/16)$; dividing by $P$'s phase probability
$1/4$ gives those multipliers, while the conditional native kernel
is unchanged. Two actual $x$-root Reads test phase equality. Their
$P$-error is $1/2$, their $Q$-error is $1/8$, and their
average error is $5/16$. Their total variation is $3/8$, with
success advantage $3/16$. Zero or one Read has risk $1/2$; further
Reads cannot improve $5/16$ for this two-gadget source. These are
symbolic consequences of the full native laws, without numerical
execution or enumeration.

## 7. Actual prices and the complete export alphabet

**Proposition 7.1 (attaining Read and literal-letter prices).** For
$k\le1$, an optimal fixed guess uses zero Reads and zero submitted
letters. For $k\ge2$, a fixed attaining list has $t$ Reads, each
of length $H+1$, and $t(H+1)$ submitted $L/R$ letters. It can
stop on its first mismatch, using $r$ Reads and $r(H+1)$ letters
on that path, $r\le t$, with worst-case $t$.

Proof. Query the $t$ actual $x$ roots of Proposition 4.3 and decode
alpha as zero and beta as one. Accept $Q$ exactly when all decoded
phases agree. Branch and absent cannot occur at those endpoints on
this support; assigning either any fixed fallback decision makes the
decoding table total. Once a mismatch occurs, completing the fixed list
cannot restore equality, so early decision $P$ preserves the test.
Lengths and letter counts follow by adding the initial $R$ and the
$H$ frontier letters for each submitted word. All-equal paths occur
under both laws and require the full list, making this a real worst-case
cost. Corollary 6.4 supplies Read optimality. No optimality claim for
expected cost or for a separate letter-budget problem is made. $\square$

Submitting a literal word is one charged Read, with its letters also
counted. Its prefixes are not free navigation operations. All addresses
and the alpha/beta and equality tables are public source-independent
data. The deterministic test needs no private randomness. If competitor
randomness is supplied and paid, Theorem 5.2 and Lemma 6.1 still give
the same optimum. Auxiliary random draws in its comparison kernel are
not resources of the implemented test.

**Proposition 7.2 (inherited full-family preparation and attained names).**
For the full-family preparation specified in OCC §7.1, the separate
preparation account is

$$
T_{\rm prep}=2^D-1,\qquad Q_{\max}\le D,\qquad
A_{\rm prep}=(D-1)2^D+1.
$$

The prescribed unrefined complete attained name alphabet on all
$\mathcal F_D$ has size

$$
|S_D|-(2^m+1)^\ell+1.
$$

Replacing the merged name by full phase-vector names instead gives
$|S_D|-(2^m+1)^\ell+2^\ell$, an addition of $2^\ell-1$ names.

Proof. The inherited preparer Reads all literal $Rq$ with
$|q|\le D-1$, including initially absent targets, to compute the
canonicalized right subtree and its complete name. Its claimed
correctness for every variable-shape source uses Assumption 1.3;
there is no free boundary array. There are
$\sum_{j=0}^{D-1}2^j=2^D-1$ words, with maximum length $D$.
The letter sum is

$$
\sum_{j=0}^{D-1}(j+1)2^j=(D-1)2^D+1.
$$

For completeness this identity is $1=1$ at $D=1$; increasing $D$
by one adds $(D+1)2^D$, transforming its right side to
$D2^{D+1}+1$, the required next value.

The scaffold map is injective and Lemma 2.3 gives exactly
$M=(2^m+1)^\ell$ canonical states in its image. Merge those
$M$ states into one name and give every other canonical state a
separate name. Every canonical state is attained as an actual right
subtree, so the entire attained alphabet has $|S_D|-M+1$ elements.
This count includes names outside the testing support; a fixed-width
encoding can have unused bit patterns without changing attained
cardinality. Every phase vector occurs, so replacing that one name by
its $2^\ell$ phase-vector refinements gives the other count. The
same already paid scan can compute that refinement. $\square$

**Convention 7.3 (resource separation and applicability).** Preparation
costs are distinct from the online budget $k$. If the scan is used,
its Reads are paid once; they are not also counted as new online phase
acquisition. Its complete transcript, temporary phase data and every
other inaccessible field must remain unavailable to the tester under
Assumption 1.4. Retaining a phase descriptor would change the accessible
experiment and its name count. For example, an already accessible full
phase vector permits the $E_\ell$ test with zero additional Reads;
this demonstrates why the constant-name and complete-isolation premises
are essential.

The public scaffold, block-order, membership, decoding and decision
tables need construction, installation, storage and lookup. Control,
computation, source acquisition, temporary storage, post-handoff
workspace and final decision storage retain separate accounts. Fixed
public addresses and finite tables establish mathematical availability;
no useful bound on their total construction or physical execution cost
is supplied. Access services are separately paid premises. The result
asserts exact online worst-case Read optimality with the displayed
literal lengths and letter costs, without a physical-efficiency claim.

## 8. Fresh whole sources under the same hypothesis

**Definition 8.1 (conditional independence and per-source budgets).**
For an integer $n\ge1$, draw $n$ whole sources independently
conditional on the same $\Theta$. Each obeys Definitions 2.2–4.1,
remains stationary, has the constant complete name and isolation of
Assumption 1.4, and has its own budget of at most $k$ online Reads.
The joint laws conditional on $\Theta=P$ and $\Theta=Q$ are
$P^{\otimes n}$ and $Q^{\otimes n}$. A global policy may choose
both its next source and its word from all observed histories and
independent private randomness, but must respect every per-source
budget. Under $Q$, different sources have independent mixture
markers and, in common mode, independent within-source common bits.
Sharing one marker or one bit across sources is a different joint law.
Conditional independence given $\Theta$ does not assert independence
after forgetting $\Theta$.

**Theorem 8.2 (comparison under global adaptive scheduling).** The
optimal experiment for every such global policy is
$E_t^{\otimes n}$, with independence conditional on the common
hypothesis. A single hypothesis-independent kernel simulates its
complete global transcript from these $n$ vectors, and fixed actual
phase-root Reads acquire that experiment.

Proof. Supply an array $Y_1,\ldots,Y_n$, independently drawn from
$p_t$ under $P$ or from $q_t$ under $Q$. Run the global policy
with one dictionary and one input-coordinate counter per source.
A constant query has its public reply. At a first touch of a gadget
in source $i$, consume the next unused coordinate of $Y_i$, draw
one full native $K$ tuple with that phase, and cache it in that
source's dictionary. Repeats use that full cached tuple. Every source
uses at most $\min\{k,\ell\}=t$ coordinates, even with arbitrary
switching and stopping. This is a kernel of the input array and
independent auxiliary variables, without using $\Theta$.

To verify its law, condition on all source mixture modes, all relevant
common bits and the independent policy tape. Under $P$ all sources
have independent mode. Under $Q$ these latent modes and bits are
independent across sources as specified in Definition 8.1. Enlarge the
history to include the full pair at every touched gadget. Initially,
in an independent-mode source, untouched pairs are independent fair
phase/$K$ pairs; in a common-mode source, untouched phases are its
fixed common bit and untouched tuples are independent corresponding
$K$ tuples. All unexposed data across sources are independent under
this conditioning. The choice of the next source and new label is a
function of the revealed history, so cannot inspect any unexposed pair.
Revealing that selected pair preserves the same assertions for all
remaining data. Constant queries, repeats, switches and termination
use only already revealed data. Induction therefore proves equality
with the array-driven cache process conditional on these latent
variables. Averaging them and the tape gives the desired transcript
identity under each product law with the same kernel.

This proof covers schedules informed by earlier nuisance replies and
hypothesis evidence; it does not assume a fixed order or replace a
source's correlated $Q$ phases by independent bits. Conversely,
Proposition 4.3 applied in each source acquires every $Y_i$ through
$t$ actual original-root Reads per source. Composition of decisions
with the common simulator and this attaining construction give equality
of the optimal testing problems. $\square$

**Theorem 8.3 (exact binomial Bayes risk and likelihood decision).** If
$t\le1$, the optimal error is $1/2$ for every $n$. If $t\ge2$,
put

$$
c=2^{1-t},\qquad b=1-\epsilon+\epsilon c,\qquad
 a=\frac bc=\epsilon+(1-\epsilon)2^{t-1}.
$$

Then the exact equal-prior error under per-source budget $k$ is

$$
R_{n,k}=\frac12\sum_{s=0}^n\binom ns
 \min\bigl\{c^s(1-c)^{n-s},\ b^s(1-b)^{n-s}\bigr\}.
$$

Acquire the phases, let $C_i$ indicate that source $i$'s $t$
phases are all equal, and set $S=\sum_i C_i$. An optimal rule
accepts $Q$ when $a^S\epsilon^{n-S}\ge1$, with arbitrary
choice on a tie, and accepts $P$ otherwise.

Proof. For $t\le1$ the two one-source phase laws are identical,
so their conditional products are identical. Theorem 8.2 transfers
this to every allowed global transcript, giving no information and
risk $1/2$.

For $t\ge2$, Proposition 6.2 makes each $C_i$ Bernoulli$(c)$
under $P$ and Bernoulli$(b)$ under $Q$. They are independent
conditional on the common hypothesis. Taking the product of its
one-source reverse kernels reconstructs all phase vectors from the
indicator vector using the same kernel under both hypotheses. Thus
that indicator vector is sufficient for the product experiment.
An indicator vector with $s$ ones has respective probabilities
$c^s(1-c)^{n-s}$ and $b^s(1-b)^{n-s}$. Both are positive,
since $0<c<b<1$. Its likelihood ratio is

$$
\left(\frac bc\right)^s
\left(\frac{1-b}{1-c}\right)^{n-s}
     =a^s\epsilon^{n-s},
$$

because $1-b=\epsilon(1-c)$. Lemma 6.1 proves the stated decision.
For a fixed count $s$ every indicator vector has the same probability
under either law. Conditional on the count it is therefore uniform
under both, giving a common reverse kernel from $S$. Hence the
count itself is sufficient. There are $\binom ns$ vectors with
that count; grouping their pointwise minimum-error contributions from
Lemma 6.1 gives exactly the displayed sum. Theorem 8.2 supplies the
full adaptive converse and actual attainment. The sum is a symbolic
finite Bayes identity. If $n=0$ is admitted,
there is no data and the risk is $1/2$. $\square$

**Proposition 8.4 (fresh-source prices and stationary-source reuse).**
For $t\ge2$, fixed acquisition for Theorem 8.3 pays for $n$
separately drawn, prepared and isolated actual sources, $nt$ online
Reads and $nt(H+1)$ submitted letters. When the inherited full scan
is used on each source, the separate total preparation price is
$n(2^D-1)$ Reads and $n[(D-1)2^D+1]$ submitted letters, with maximum
word length at most $D$. Early
mismatch stopping within a source can determine its $C_i$ with
fewer actual Reads without changing the rule. For $t\le1$, the
optimal fixed guess needs no online Reads.

Reusing one stationary source does not realize these product laws.
If instead that one source is allowed a total budget $nk$, its
optimum is Theorem 6.3 with $t$ replaced by $\min\{nk,\ell\}$.

Proof. Apply Proposition 7.1 separately to each fresh source and add
the actual words and letters. A mismatch already fixes that source's
indicator at zero, so early termination preserves all indicators and
the resulting count. Preparations and isolation are separate services
on separate actual sources; public common tables, control, workspace,
decision storage and any competitor randomness retain the accounts of
§7. The attaining test still needs no randomization.

On one stationary source, repeats return the same tuple's values,
not independent new native samples. All its data, regardless of how
one groups the invocations, belong to a single policy of total budget
$nk$. Theorem 5.2 gives its comparison with
$E_{\min\{nk,\ell\}}$, and actual root Reads attain the one-source
formula. In particular its risk saturates after $\ell$ distinct
phases. This distinguishes fresh source acquisition from repeated
access to one sample. $\square$

## 9. Attribution, relation to the supplied volume and limits

**Convention 9.1 (precise source and new-content boundary).** [OCC][OCC]
at `ce2fe4a685b5a195b8b0a380616daf0151f576cb` supplies the
source/action interface and credited factor representation in §§1–2,
the complete actual family and unique lifts in §§4.1–4.2, the
balanced native weights in §§5.1–5.2, the full-law completion $Q$
in §5.3, and the paid full-family names, phase refinement and descriptor
bound in §§7.1–7.2. Its §§3–6 concern conditional specifications,
owner barriers and completion deficits; §8 gives finite symbolic
instances; §9 states the remaining weighted-global-completion
obligation. Those results are inherited, rather than counted again as
new results of this volume.

The `repo-derived` additions here are Theorem 5.2's common full-native
simulation for all finite-word adaptive policies, the attained optimal
experiment in Corollary 5.3, the exact budget-dependent risk and
advantage in Theorem 6.3 with its sharp worst-case budgets, and the
globally scheduled fresh-source comparison and exact formula in
Theorems 8.2–8.3. The full native-law derivations and resource discussion
connect these deductions to the original experiment. This classification
is relative to the entire supplied OCC source and does not assert a
literature-wide priority claim. No external literature search or primary
paper verification is claimed. Bayes/TV identities, sufficient statistics,
Blackwell comparison and deferred revelation are mature mathematical
methods, and their needed finite arguments are given in full above.

**Convention 9.2 (limits of the proved experiment).** The conclusions
are conditional on the exact native templates, unchanged once-owned
weights, full common conditional law, canonical support, stationary
sampling and complete paid-access premises stated here. Equal local
marginals alone would not replace the full conditional product formula
of Proposition 3.2. A surviving preparation transcript, a phase-dependent
handle or another accessible source distinction would change the
experiment and defeat the specified constant-export hypothesis. A
source-update process or shared across-source mixture variable would
also require a different joint-law analysis. No physical source
generator, isolation implementation, useful total physical-efficiency
bound, native quantum preparation, general neural-network statement
or empirical machine-learning conclusion is provided.

The entropy and free-energy deficit of OCC §5.3 is a different
functional from Bayes risk. No entropy-to-total-variation estimate is
used here, and the alternative completion is not substituted for the
original Gibbs law in an identity requiring that law. The exact
likelihood and full-native experiment comparison are what yield the
risk. All proofs are ordinary written proofs; there is no kernel
verification or independent final certification claim.

**Open problem 9.3 (unchanged wider obligations).** These testing
results do not determine optimized $M_1(D)$, uniformly control the
all-size native component normalizers or cap extremum, supply an
optimizer-cofinal all-size verifier, establish a uniform effective
original length-error bridge, or determine sharp $\lambda$. The
remaining weighted-global-completion obligation of OCC §9.4 is not
resolved by this finite-family testing curve. Those broader questions
remain outside the present result.

[OCC]: https://github.com/the-omega-institute/trureturing/blob/ce2fe4a685b5a195b8b0a380616daf0151f576cb/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_OWNER_COMPONENT_COMPLETION.md

## 追加锚（本行以下为增补区）
