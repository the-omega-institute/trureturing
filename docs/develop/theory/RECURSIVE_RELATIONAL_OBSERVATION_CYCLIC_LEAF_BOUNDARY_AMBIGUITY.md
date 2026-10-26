# Recursive Relational Observation: Cyclic Leaf Boundary Ambiguity

## 1. A complete leaf interface on one actual source

This volume concerns a finite rational family with known order and an authenticated complete roster of leaves. It separates recovery of native coefficients and graph support from recovery of input/output behavior. Its second interface includes one additional, authentically bound interior scalar read. That installation is a different premise from the original leaf service.

**Definition 1.1 (native family).** Fix an integer $b\ge3$, put $N=b+4$, and use the ordered native vertex set

$$
V=(\ell_1,\ldots,\ell_b,c,d,e,f),
\qquad
\epsilon=\frac1{4N}.
\tag{CL.1}
$$

Write $e_v$ for a native coordinate vector. The rational symmetric matrix $A_0$ has zero diagonal and exactly the following undirected nonzero entries:

$$
(A_0)_{\ell_jc}=1\quad(1\le j\le b),\qquad
(A_0)_{cd}=1,\qquad
(A_0)_{de}=1,\qquad
(A_0)_{df}=2,\qquad
(A_0)_{ef}=1.
\tag{CL.2}
$$

Define

$$
\begin{aligned}
T_0&=\tfrac12 I+\epsilon A_0,\\
\mathcal P&=\{(C,S)\in\mathbb Q^2:
 C^2+S^2=1,\ 0\le S\le3/5,\ C\ge4/5\}.
\end{aligned}
\tag{CL.3}
$$

For $(C,S)\in\mathcal P$, let $Q=Q_{C,S}$ be the identity on the leaves, $c$ and $f$, with ordered $(d,e)$ block

$$
Q|_{d,e}=
\begin{pmatrix}C&-S\\S&C\end{pmatrix},
\qquad
T=T_{C,S}=QT_0Q^{\mathsf T}.
\tag{CL.4}
$$

A source has this fixed actual $T$ and native current field $x\in\mathbb Q^V$. Its actual entrance is $x=0$ on the entire field. The parameter is unknown to the observer. The native names describe coefficient positions in the promised family; they do not give read or input rights at those positions.

The family is infinite even for a fixed $b$: every rational $t\in[0,1/3]$ gives

$$
C=\frac{1-t^2}{1+t^2},\qquad S=\frac{2t}{1+t^2}.
\tag{CL.5}
$$

In particular the parameter encodings have no bound determined by $b$ alone.

**Definition 1.2 (old serial service).** The old menu acts on the same field and law throughout the run.

| Command | Actual successor field | Complete declared reply |
| --- | --- | --- |
| Reset | $0$ on all $N$ coordinates | a fixed acknowledgement |
| Add$(j,u)$, $1\le j\le b$, $u\in\mathbb Q$ | $x+u e_{\ell_j}$ | a fixed acknowledgement |
| Tick | $Tx$ | a fixed acknowledgement |
| Read$(j)$, $1\le j\le b$ | $x$ | the exact signed rational $x_{\ell_j}$ |
| Hold | $x$, with source advancement prevented during local processing | a fixed acknowledgement |

Acknowledgements can be typed by the command, but contain no source-dependent payload. Tick returns no scalar field value. Reads are nondestructive. Calls are serial and there is no unaccounted autonomous Tick between them. Inputs, stopping decisions and local calculation may depend on the acquired record and on supplied common external inputs.

**Assumption 1.3 (installation and access).** The known $b$, hence $N$, ordered complete-leaf roster, family promise, full-field zero calibration, fixed-law binding, exact rational units and serialization, serial exclusivity, Hold control, source handle, successful-call rights and storage backing are installed. The observer begins with common code and an empty acquired record. Any observer randomization has a common source-independent law. These data include no source-dependent coefficient, parameter, identifier, timing, allocation-length or work side channel. An opaque source handle binds the source; it is not a parameter-valued observation.

The installation must maintain this same source during acquisition, retention and later actual calls. Signed rational pulses are legal. Storage and input widths need not have a common finite cap. Physical conformance and the authentic implementation of these premises are **ASSUMED-UNVERIFIED**. The mathematical results are conditional on them.

**Definition 1.4 (enlarged service).** The enlarged model separately installs the authentic command

$$
\operatorname{Read}_e:\quad x\longmapsto x,
\qquad\text{reply }e_e^{\mathsf T}x=x_e.
\tag{CL.6}
$$

This is a read of the native $e$ coordinate, with its own binding, units, nondestructiveness, call right and backing. Its installation is present already at the zero entrance of this different model. There is no Add at $e$. The old service neither acquires nor installs this port. In particular, a read in a transported coordinate frame would be a different command from (CL.6).

## 2. Positive cyclic graphs with exactly the declared leaves

**Lemma 2.1 (the native entries).** Set $A=QA_0Q^{\mathsf T}$. Its only possibly nonzero diagonal entries are

$$
A_{dd}=-2CS,\qquad A_{ee}=2CS.
\tag{CL.7}
$$

Its undirected nonzero off-diagonal entries, apart from a possibly zero $ce$ entry, are

$$
\begin{aligned}
A_{\ell_jc}&=1,&
A_{cd}&=C,& A_{ce}&=S,\\
A_{de}&=C^2-S^2,&
A_{df}&=2C-S,& A_{ef}&=2S+C.
\end{aligned}
\tag{CL.8}
$$

All other off-diagonal entries vanish.

**Proof.** The leaves, $c$ and $f$ are fixed by $Q$. The old $c$-to-$(d,e)$ column is $(1,0)^{\mathsf T}$, which rotates to $(C,S)^{\mathsf T}$; the old $f$ column is $(2,1)^{\mathsf T}$, which rotates to $(2C-S,2S+C)^{\mathsf T}$. On the $(d,e)$ block the multiplication is

$$
\begin{pmatrix}C&-S\\S&C\end{pmatrix}
\begin{pmatrix}0&1\\1&0\end{pmatrix}
\begin{pmatrix}C&S\\-S&C\end{pmatrix}
=\begin{pmatrix}-2CS&C^2-S^2\\C^2-S^2&2CS\end{pmatrix}.
$$

These blocks exhaust the original nonzero entries, giving the claim. $\square$

**Theorem 2.2 (uniform admissibility and cycle ranks).** Every member of Definition 1.1 is rational and symmetric, and satisfies

$$
\tfrac14 I<T<\tfrac34 I.
\tag{CL.9}
$$

Thus $T$ and $I-T$ are positive definite. Its positive off-diagonal graph is connected, has no negative off-diagonal entries, and has exactly the leaves $\ell_1,\ldots,\ell_b$. At $S=0$ it has $b+4$ edges and cycle rank one; at $S>0$ it has $b+5$ edges and cycle rank two.

**Proof.** Rationality and symmetry follow from (CL.3)–(CL.4). The absolute row sums of $A_0$ are $1$ at a leaf, $b+1$ at $c$, $4$ at $d$, $2$ at $e$ and $3$ at $f$. Their maximum is $b+1$ because $b\ge3$. For an eigenvector of $A_0$, choose a coordinate of maximum absolute value; the eigenvalue equation at that coordinate gives $|\lambda|\le b+1$. Symmetry makes all eigenvalues real. Orthogonality of $Q$ preserves the spectrum, so every eigenvalue $\mu$ of $T$ obeys

$$
\frac14+\frac3{4N}
=\frac12-\frac{b+1}{4N}
\le\mu\le
\frac12+\frac{b+1}{4N}
=\frac34-\frac3{4N}.
\tag{CL.10}
$$

This proves the strict inequalities in (CL.9).

For the off-diagonal entries,

$$
C>0,\qquad
C^2-S^2=1-2S^2\ge7/25,\qquad
2C-S\ge1,\qquad 2S+C>0.
$$

The entry $ce$ is positive exactly when $S>0$. Multiplication by $\epsilon>0$ preserves these signs. Thus the graph always contains every leaf-to-$c$ edge, the edge $cd$, and the triangle $def$; the only additional edge is $ce$ when $S>0$. It is connected.

At $S=0$ the degrees of $c,d,e,f$ are respectively $b+1,3,2,2$. At $S>0$ they are $b+2,3,3,2$. Consequently none is a leaf and all declared leaves have degree one. Here the graph ignores diagonal entries: a diagonal coefficient is an onsite coefficient, not an extra loop edge. For a connected undirected graph the cycle rank is $|E|-|V|+1$. The counts above give one and two. $\square$

The word “cyclic” here means that the positive off-diagonal graph contains a cycle. It does not mean that any single leaf vector is a cyclic vector for $T$.

## 3. Joint reachability and joint observability without hidden modes

Put $B:\mathbb Q^b\to\mathbb Q^V$, $Bu=\sum_j u_j e_{\ell_j}$, and $H=B^{\mathsf T}$. Joint leaf reachability means

$$
\operatorname{span}_{\mathbb Q}\{T^k e_{\ell_j}:k\ge0,\ 1\le j\le b\}
=\mathbb Q^V.
\tag{CL.11}
$$

Joint leaf observability means that $HT^k v=0$ for every $k\ge0$ implies $v=0$. These are properties of the fixed system and its ports, not an assertion that the observer already knows the unknown native matrix.

**Theorem 3.1 (a five-level joint span).** For every member of the family,

$$
\begin{aligned}
\operatorname{span}_{\mathbb Q}\{T^k e_{\ell_j}:0\le k\le4,\ 1\le j\le b\}
&=\mathbb Q^V,\\
\bigcap_{k=0}^4\ker(HT^k)&=\{0\}.
\end{aligned}
\tag{CL.12}
$$

In particular there is no inaccessible or unobservable native subspace for the joint leaf interface.

**Proof.** First use $A_0$. The span of its leaf columns through the fourth power contains every $e_{\ell_j}$ and, by (CL.2),

$$
e_c=A_0e_{\ell_1},\qquad
e_d=A_0e_c-\sum_j e_{\ell_j}.
$$

It therefore contains

$$
v=A_0e_d-e_c=e_e+2e_f.
$$

Applying $A_0$ once more gives

$$
A_0v=5e_d+2e_e+e_f,
\qquad
w=A_0v-5e_d=2e_e+e_f.
$$

Here $e_c$ uses powers through one, $e_d$ through two, $v$ through three and $w$ through four. Finally,

$$
e_e=\frac{2w-v}{3},\qquad e_f=\frac{2v-w}{3}.
$$

Thus all native coordinate vectors belong to that span. Since $T_0=\tfrac12 I+\epsilon A_0$ with nonzero rational $\epsilon$, powers of $T_0$ and powers of $A_0$ through any fixed degree span the same polynomial columns. Conjugation and $Qe_{\ell_j}=e_{\ell_j}$ give

$$
T^k e_{\ell_j}=Q T_0^k e_{\ell_j}.
$$

The first equality of (CL.12) follows because $Q$ is invertible. If $HT^k v=0$ through $k=4$, symmetry gives

$$
0=e_{\ell_j}^{\mathsf T}T^k v
=(T^k e_{\ell_j})^{\mathsf T}v
$$

for every spanning column. Hence $v=0$, proving the second equality. $\square$

**Corollary 3.2 (actual finite-pulse meaning).** For a fixed member, every rational target field can be reached from zero using signed leaf Adds and four Ticks, with several Adds allowed between Ticks.

**Proof.** By (CL.12), write the target as $\sum_{k=0}^4T^k Bu_k$ with rational vectors $u_k$. Immediately before the first Tick add $Bu_4$, after that Tick add $Bu_3$, and continue, adding $Bu_0$ after the fourth Tick. Linearity gives exactly the displayed sum. Each $Bu_k$ is realized by its $b$ legal scalar Adds. This is a fixed-law existence construction; finding these amplitudes requires the law or equivalent information. It is not an unknown-source acquisition supplied to the observer. $\square$

The usual stacked-readout rank criterion is supplied by finite-dimensional linear systems theory. In the repository, [FiniteObservabilityEquivalence][FO] and its [owning Scribe][FOS] identify zero residual, full rank and positive Gram operator. The exact correspondence here is real state space $\mathbb R^V$, output space $\mathbb R^b$, update $T$, readout $H$, and horizon five, meaning exponents $0,\ldots,4$. The rational spanning calculation above verifies the family-specific premise. No new general rank criterion is asserted.

There is a repeated eigenvalue: every leaf-difference vector has eigenvalue $1/2$, on a subspace of dimension $b-1$. For any chosen leaf $\ell_j$, a difference of two other leaves is orthogonal to every $T^k e_{\ell_j}$. Such two other leaves exist because $b\ge3$. Thus a single leaf is not a cyclic input. Separate access to all leaf coordinates is precisely what makes (CL.12) possible.

## 4. Equality of the entire old adaptive service

**Definition 4.1 (complete records and boundary behavior).** A finite acquired record lists each actual command, its input and its complete reply, in order, including acknowledgements, Holds, Resets and stopping/output decisions. A common observer's accessible working memory is generated from this record, the common installed data and its common external inputs. The complete old boundary behavior at a field means the replies along every finite legal old command word. It is a semantic response profile; it is not an acquired response oracle or a retained journal.

**Theorem 4.2 (initialization-preserving service equivalence).** Fix $b$ and any two parameters $p=(C,S)$ and $p'=(C',S')$ in $\mathcal P$. Their entire old services from the actual zero entrance are equivalent. Every common adaptive policy has exactly the same acquired command/reply record, stopping behavior and observer outputs on both sources. With a common random tape the equality holds pointwise in the tape; consequently every defined randomized acquired-record law is the same.

**Proof.** Write $T_p=Q_pT_0Q_p^{\mathsf T}$ and set

$$
U=Q_{p'}Q_p^{\mathsf T}.
$$

Then

$$
UT_p=T_{p'}U,\qquad
Ue_{\ell_j}=e_{\ell_j},\qquad
e_{\ell_j}^{\mathsf T}U=e_{\ell_j}^{\mathsf T},\qquad U0=0.
\tag{CL.13}
$$

Couple native fields by $x'=Ux$. The initial fields satisfy this relation. Every old operation preserves it and its full reply:

- Reset gives the two zero fields and the same acknowledgement.
- Add$(j,u)$ gives $x'+u e_{\ell_j}=U(x+u e_{\ell_j})$ and the same acknowledgement.
- Tick gives $T_{p'}x'=UT_px$ and the same acknowledgement.
- Read$(j)$ gives $e_{\ell_j}^{\mathsf T}x'=e_{\ell_j}^{\mathsf T}x$ and changes neither field.
- Hold leaves the relation unchanged, prevents further advancement and gives the same acknowledgement.

The valid command and input domains in Definition 1.2 are parameter-independent. All supplied calibration and capability roles correspond, so there is no differing legality or successful-call output to omit.

Induct on the acquired record. Equal previous records, equal common external inputs and equal current observer memory make a common deterministic observer choose the same next command, rational pulse or stopping decision. The one-operation calculation gives the same next reply and corresponding next fields. The observer therefore writes the same next record and memory. The induction includes any finite number of local calculations between calls. If a policy never stops, every finite prefix still agrees.

For a randomized observer, fix its complete random tape and use the same tape on both sides. Its decisions then satisfy the deterministic argument. Thus the record maps are identical at every tape, including any termination/output coordinates. Pushing forward any common tape law gives equal record laws whenever these maps are measurable. The bad-source choice does not depend on the tape. $\square$

Equivalently, every multiport Markov matrix and transfer function of the old interface agree:

$$
HT_p^kB=HT_0^kB\quad(k\ge0),\qquad
H(zI-T_p)^{-1}B=H(zI-T_0)^{-1}B.
\tag{CL.14}
$$

The resolvent identity holds as a matrix of rational functions. These formulas follow directly from (CL.13); Theorem 4.2 additionally checks the authentic initial field, Reset, inputs, all replies and adaptive records. The actual sources can have different native fields, related by $U$ rather than equality.

This is the same mature distinction between native graph and realization coordinates used in [P, Counterexample 42.2][P] and [Process Geometry, §§17.2–17.4][PG]. The extra content here is that the fixed ports are the entire true leaf set for every member, with the same known order, positive links, connected cyclic graphs and full joint reachability/observability. Neither an unseen component nor an unobservable mode explains the equality.

## 5. Native topology and coefficient laws do not descend

A native graph is compared up to permutations fixing every declared leaf. A native coefficient law is the full symmetric $T$, including its diagonal coefficients, under the same equivalence. The distinction between unweighted support and coefficient law is material.

**Theorem 5.1 (two different failures of inverse).** For every $b\ge3$:

1. There is no uniform inverse from the old complete boundary behavior to the native unweighted topology on the whole family, even with $N$ and the exact complete-leaf roster supplied.
2. Within the subfamily $S>0$, the unweighted support is fixed, but distinct parameters give distinct coefficient laws even up to a leaf-fixing permutation. Thus there is no uniform native coefficient-law inverse on that fixed-support subfamily.

The same failures hold for every actually acquired old record and its further internal postprocessing.

**Proof.** At $S=0$ and $S=3/5$ the graphs have different edge counts by Theorem 2.2, and hence are not isomorphic even without fixing leaves. Their complete old behaviors coincide by Theorem 4.2. No function of that common value can return both topologies. An adaptive acquiring observer has the same records on the pair, so changing how it chooses or processes leaf observations cannot supply an inverse either.

For the second assertion, the two extreme diagonal entries of $T$ are

$$
\min_v T_{vv}=\frac12-2\epsilon CS,\qquad
\max_v T_{vv}=\frac12+2\epsilon CS,
\tag{CL.15}
$$

and all other diagonal entries are $1/2$. To see strict parameter separation without a differentiability assumption, let $0\le S_1<S_2\le3/5$ and put $r_i=S_i^2$. Then

$$
(C_2S_2)^2-(C_1S_1)^2
=(r_2-r_1)(1-r_1-r_2)>0,
\tag{CL.16}
$$

since $r_1+r_2\le18/25<1$. Both products are nonnegative, so $C_2S_2>C_1S_1$. Also $C$ is uniquely determined by $S$ because $C>0$ and $C^2=1-S^2$. A permutation preserves the multiset of diagonal entries, in particular its minimum and maximum. Therefore distinct parameters cannot give permutation-equivalent coefficient laws. For $S>0$, (CL.8) gives the same support for every member, and Theorem 4.2 again gives the same old complete behavior.

Any postprocessing of equal acquired records has equal values. This last observation does not impose a complexity bound on the observer: arbitrary finite computation and recursive relations among previously acquired data still start from the same data. $\square$

For randomized exact recovery, Theorem 4.2 gives the same output distribution on the two different topologies. It cannot assign probability one to the correct topology on both. This is a fixed pair, pointwise common-tape obstruction, rather than an inference from separate worst cases after fixing each random tape.

The obstruction is not that the order is unknown, nor that only some leaves were found. It is failure of the native target to be constant on a complete behavior fiber. Known-law observability in Theorem 3.1 and unknown-law native identification answer different questions.

## 6. One acquired interior scalar at the actual advanced cut

**Theorem 6.1 (attained family-relative acquisition).** In the enlarged service, perform on the actual zero field

$$
\operatorname{Add}(1,1),\quad
\operatorname{Tick},\quad
\operatorname{Tick},\quad
\operatorname{Read}_e.
\tag{CL.17}
$$

The acquired scalar is

$$
y=\epsilon^2S.
\tag{CL.18}
$$

This exact observation effectively determines $S,C$, the native law $T$ and the actual current field on this same source. No Reset or leaf Read is used.

**Proof.** Because $Q$ fixes $e_{\ell_1}$ and $e_c$,

$$
Te_{\ell_1}=\tfrac12 e_{\ell_1}+\epsilon e_c,\qquad
Te_c=\tfrac12 e_c+\epsilon\Bigl(\sum_j e_{\ell_j}+C e_d+S e_e\Bigr).
$$

After the two paid Ticks the actual field is therefore

$$
x_*=
\frac14 e_{\ell_1}+\epsilon e_c+
\epsilon^2\Bigl(\sum_j e_{\ell_j}+C e_d+S e_e\Bigr).
\tag{CL.19}
$$

The nondestructive native $e$ read gives (CL.18). Decode $S=y/\epsilon^2$ and take the unique positive $C$ satisfying $C^2=1-S^2$. This is an effective rational operation on the promised image, rather than a real-number oracle: if $S=p/q$ is reduced with $q>0$, compute the integer square root of $q^2-p^2$. It is an integer $r$ because $(qC)^2=q^2-p^2$ and a rational whose square is an integer has denominator one in reduced form. Finite integer square-root search returns it, and $C=r/q$. The promise ensures $C\ge4/5$, including $C=1$ when $S=0$.

Substitute the decoded values into (CL.4), or the complete entry list (CL.7)–(CL.8), to obtain the actual native law in its promised vertex correspondence. Formula (CL.19) gives the actual advanced field, not a field before the two Ticks. The read does not change it. The source has not been reset or replaced. $\square$

**Definition 6.2 (a retained predictor and its installation).** Immediately after (CL.17), issue one actual Hold and keep the source held while decoding and installing the record. This adds one fixed acknowledgement. Let

$$
z_*=T_0^2e_{\ell_1}
=\frac14e_{\ell_1}+\epsilon e_c+
\epsilon^2\Bigl(\sum_j e_{\ell_j}+e_d\Bigr).
\tag{CL.20}
$$

Retain the earned $(C,S)$, the common template $T_0$ and a current vector $z$, initialized as $z_*$. The predictor is a finite description of future responses in template coordinates. It stores no arbitrary command journal. Its native interpretation is $x=Qz$.

Here the family template, zero calibration, unit pulse and prescribed command schedule are supplied. The scalar $y$ is actually acquired. The pair $(C,S)$ is decoded from that scalar, while $z_*$ is computed from the public template and the actual known pulse/Tick sequence. Its native interpretation $Qz_*$ uses the earned parameter; no hidden native field value was initially supplied.

Keep separately the actual same-source handle, leaf and interior read rights, leaf input rights, Reset and Hold control, serial access and storage backing. None is encoded by the two rational parameters. Native law and field outputs can be produced as $QT_0Q^{\mathsf T}$ and $Qz$. A literal native coefficient list or redundant native field copy, if retained, is an additional store.

**Theorem 6.3 (complete finite common adaptive continuation).** From the actual cut of Definition 6.2, the retained predictor supports every finite common adaptive continuation using the installed enlarged menu, including arbitrary rational leaf Adds and later Resets. It predicts every declared reply and remains synchronized with the actual native field after every committed operation.

**Proof.** Use the following local rules.

| Command | Predictor successor | Predicted complete reply |
| --- | --- | --- |
| Reset | $z:=0$ | the command's fixed acknowledgement |
| Add$(j,u)$ | $z:=z+u e_{\ell_j}$ | the command's fixed acknowledgement |
| Tick | $z:=T_0z$ | the command's fixed acknowledgement |
| Read$(j)$ | $z$ | $z_{\ell_j}$ |
| Read$_e$ | $z$ | $S z_d+C z_e$ |
| Hold | $z$ | the command's fixed acknowledgement |

At installation (CL.19)–(CL.20) give $x_{\rm actual}=Qz_*$. If this invariant holds at a cut, Reset and Hold preserve it; Add preserves it since $Qe_{\ell_j}=e_{\ell_j}$. Tick preserves it because $TQ=QT_0$. The leaf read is correct because its row is fixed by $Q$. The native $e$ row of $Q$ is $(S,C)$ on $(d,e)$, which proves the displayed interior reply.

For an actual operation the source receives the actual call through its retained right; the observer computes and commits the corresponding predictor update before the next completed cut. Hold and serial exclusivity prevent an unrepresented source step. Induct on the continuation length. Equal earlier predicted and actual replies make a common adaptive policy select the same next command and input. The one-operation invariant then supplies both the next reply and the complete corresponding native successor. A common random tape is handled by the same pointwise induction. $\square$

The construction starts from the actual zero-entrance acquisition and its actual two-Tick field. It does not assert that $(C,S)$ reconstructs an arbitrary forgotten field, nor that a numerical predictor creates a missing authentic port. Local hypothetical forecasts use scratch copies of $z$; they do not execute calls on, reset or copy the actual source.

## 7. The two acquisition-coordinate lower bounds

**Theorem 7.1 (one informative added read and two total Ticks).** For uniform exact identification of the parameter, or of the native coefficient law, from the zero entrance in the enlarged family/menu:

1. At least one informative Read$_e$ is necessary; the old observations alone never suffice.
2. No policy that uses at most one total Tick on its identifying runs can succeed uniformly, even if it uses arbitrarily many legal Adds, Resets, Holds, leaf Reads and Read$_e$ calls.

The acquisition (CL.17) attains one informative added scalar read and two total Ticks simultaneously.

**Proof.** The first claim follows from Theorems 4.2 and 5.1. More explicitly, call a read informative at an acquired history if its possible reply is not constant on the parameters still compatible with that history and its actual command sequence. Until the first informative Read$_e$, every interior reply leaves that parameter fiber unchanged. Old commands and replies cannot split the initial fiber by Theorem 4.2. A finite terminal record with no informative added read is therefore still compatible with every initial parameter and cannot determine the native law. Randomness does not help: coupling the common tape leaves the same nonsingleton fiber and the same output law.

For the Tick lower bound, set

$$
L=\operatorname{span}\{e_{\ell_1},\ldots,e_{\ell_b}\}.
$$

Before a first Tick, every field reachable from zero is in $L$ and is parameter-independent: only Adds change it, Reset returns zero, and reads/Holds leave it unchanged. For any $v=\sum_j a_j e_{\ell_j}\in L$,

$$
Tv=\tfrac12v+\epsilon\Bigl(\sum_j a_j\Bigr)e_c,
\tag{CL.21}
$$

independently of $(C,S)$. After this sole Tick, subsequent Adds keep the field in $L+\mathbb Qe_c$; Reset can only return it to $L$. There is no second Tick to propagate the $c$ component into $d,e$. Hence every interior read is zero, all leaf values and acknowledgements are parameter-independent, and all actual fields are identical across parameters under a common adaptive policy. This argument includes Ticks before any pulse and Ticks whose effects are later reset.

Consequently no transcript using at most one Tick can identify a member of this nonsingleton family. The result is stronger at a proposed early terminal cut: if a common policy halts there with at most one Tick, every parameter has that same cut and terminal output. Pointwise common-tape coupling yields the same obstruction to uniform almost-sure randomized exact success. Finally, (CL.18) is nonconstant on $\mathcal P$ and decodes its parameter, so (CL.17) attains the two claimed coordinates. $\square$

These lower bounds concern identifying the unknown family member using the declared menu and zero entrance. They are not lower bounds for a different entrance, extra interior input, coefficient-reading instrument, arbitrary hardware design, elapsed duration, bit cost or total physical resource. A parameter-specific guessed answer is not uniform identification.

## 8. Space, time, boundary and retained memory at the earned cut

**Definition 8.1 (four independently exposed data).** Restrict this paragraph to the actual acquisition image (CL.17), followed by the Hold of Definition 6.2. All entries share the same common installation and promised native correspondence.

| View | Exposed data and their independent meaning |
| --- | --- |
| Space | The actual weighted native graph, its diagonal coefficients, and its present native field $x_*$ |
| Time | The ordered actual command/reply word Add$(1,1)$, Tick, Tick, Read$_e$, Hold, including its four acknowledgements and acquired scalar |
| Boundary | The leaf response $F_L(z)=H(zI-T)^{-1}B$ and the present authentic interior boundary value $y=x_e$ |
| Memory | The earned parameter pair and the current template-coordinate predictor $(C,S,z_*)$, with the rules in Theorem 6.3 |

The old Boundary would omit the extra scalar. Its leaf transfer $F_L$ is common to the family by (CL.14); it does not contain the missing parameter. In the enlarged Boundary, $F_L$ can be specified by the public formula $H(zI-T_0)^{-1}B$. Giving that common mathematical law is not an acquired table of source-dependent responses. The extra $y$ is the paid measurement, with the binding of Definition 1.4.

Space is a native snapshot, Time is an ordered event record, Boundary is a port law and current scalar, and Memory is a finite machine for predicting and updating. Only Time is an acquisition journal; the other views do not contain copies of that journal or any wall-clock duration.

**Proposition 8.2 (agreement on the actual acquisition image).** On this restricted image each view determines the same numerical $(T,x_*)$ and the other displayed numerical views. Every composition of these recovery routes agrees. Actual provenance and callable rights are retained installation data, not numerical outputs of a recovery map.

**Proof.** Time exposes its actually obtained scalar $y$, and Boundary exposes the same scalar. Theorem 6.1 decodes its unique $(C,S)$ and gives $T,x_*$. Space gives $y=(x_*)_e$, so the same argument applies there. Memory exposes $(C,S)$ and gives $x_*=Qz_*$.

Conversely these recovered values compute the specified native snapshot, the fixed public schedule with its one scalar and acknowledgements, its leaf transfer, and (CL.20)'s predictor state. Each route gives the unique parameter determined by (CL.18). All resulting expressions therefore agree. Reconstructing the numerical event word does not execute it or manufacture its observation provenance. The actual word, source binding and rights are already supplied by this one acquisition run. $\square$

This is a source-relative recovery condition with a paid acquisition bridge. The complete old boundary fails the Space inverse; the enlarged one succeeds on the specified actual image. The result does not give a variable-phase autonomous clock. Here the two source Ticks are part of a publicly specified preparation, and Time also retains their actual occurrence.

Nor does the continuation predictor invert arbitrary subsequent Time records. For example, from the earned cut the continuations Reset and Reset followed by Tick both end with the same law and zero field, the same predictor state and the same future response profile. Their actual words and Tick counts differ. An actually retained journal distinguishes them; a current snapshot does not. This preserves the chronology boundary of [P §42.1][P] and [NDR §6.2][NDR].

## 9. Resources coexisting on this same run

**Convention 9.1 (exact width and representation).** A rational is encoded by a reduced signed binary numerator and positive binary denominator with framing. Write $\lambda$ for the total bit length of the actual $C,S$ words and put

$$
W=1+\lambda+\lceil\log_2(N+1)\rceil.
\tag{CL.22}
$$

This is a bound parameter for the account, not advice given to the observer. At acquisition every coefficient in (CL.7)–(CL.8), every entry of $x_*$ and $z_*$, the acquired $y$, and the intermediate constant-degree rational expressions used to decode and form them have $O(W)$ bits. Integer square-root search uses $O(W)$-bit operands as well. There is no fixed precision bound over $\mathcal P$.

**Proposition 9.2 (one attained same-run account).** The following resource coordinates can be attained together for the protocol and predictor described above. They are upper accounts for an explicit representation, not a claim that every implementation has these costs.

| Coordinate | Acquisition and retained use |
| --- | --- |
| Actual source calls through installation | one leaf Add of the supplied unit, two Ticks, one Read$_e$, one Hold; zero Resets and zero leaf Reads |
| Complete received outputs | one exact rational $y$ and four fixed acknowledgements |
| Paid input and selection | pulse $1$, the selected roster entry $\ell_1$, command tags and framing; literal leaf selection uses $O(\log N)$ bits |
| Additional installation | one authentic native $e$-read port, its reference/units, right and backing; no interior input port |
| Source law store | a sparse native coefficient list with $N+2E\le3b+14$ nonzero entries, plus incidence/address data |
| Source current field and Tick scratch | $N$ exact field words and a separate $N$-word output vector for an out-of-place Tick |
| Observer fixed data | common code, the family/template, $b,N,\epsilon$, roster and command/port reference data |
| Observer source-dependent memory | earned $C,S$, current $N$-vector $z$, acquired $y$ and the fixed-size acquisition word |
| Observer scratch | a separate $N$-vector for its out-of-place Tick, integer/rational decoding work and output buffers |
| Optional extra retained outputs | any literal native law list or redundant $x=Qz$ copy, and any later full command/output journal |
| Continued service | every actual source call, predictor update, rational input/output word and storage at its current width is charged |

Here $E=b+4$ or $b+5$. Explicitly listing the source coefficients and the source/observer field and scratch vectors costs $O(NW)$ bits for each of these finitely many stores at installation. A literal roster in each party's own store and sparse address data contribute $O(N\log N)$ bits per copy. These counts coexist; the observer vector does not replace the source's field. A public compressed roster can use a different encoding, but cannot remove the actual installed leaf bindings. Handle, permissions, source-service implementation, reference and storage backing have separate installation charges; no numerical bit count here prices their physical realization.

**Proof.** The call/output counts follow directly from (CL.17) and the one Hold in Definition 6.2. The source is still at (CL.19). There is no implicit scalar read on either Tick. In a sparse row multiplication, initialize each output coordinate by its diagonal product and accumulate one term for every incident off-diagonal entry. Thus an arbitrary actual source Tick uses

$$
N+2E\le3b+14\quad\text{rational products},
\qquad
2E\le2b+10\quad\text{rational additions},
\tag{CL.23}
$$

and an $N$-word destination vector. Both of the two actual acquisition Ticks are charged on that source. The stored predictor template $T_0$ uses $E_0=b+4$, so a general later predictor Tick uses at most $3b+12$ products and $2b+8$ additions, with its own destination vector. The source and observer need their respective work even when their results are related.

Each rational expression for the law and acquisition field has bounded algebraic degree in $C,S,\epsilon$; reduced numerators and denominators therefore have $O(W)$ bits. For recovery, rational scaling yields $S$. If $S=p/q$, binary search for $r=\sqrt{q^2-p^2}$ uses $O(W)$ comparisons and squarings of $O(W)$-bit integers. Elementary integer multiplication, division and fraction reduction give a conservative polynomial bit cost, for example $O(W^4)$ for this constant-dimensional parameter decoding. This is not constant-time exact square root. Writing a literal native law and field requires $O(N)$ rational calculations and output words in addition. A uniform conservative installation allowance with schoolbook arithmetic is $O(NW^4)$ bit work and $O(NW)$ live arithmetic/output storage, in addition to the stated reference/capability stores. More compact template encoding can avoid duplicating every repeated coefficient, but is not needed for these simultaneous upper bounds. $\square$

**Convention 9.3 (later width-dependent work).** At a later cut, let $L$ bound the actual rational widths of the current source and predictor coordinates and the next supplied pulse. One source Tick and one predictor Tick use the linear arithmetic counts above, at operand and result widths bounded conservatively by $O(N(L+W+1))$. Indeed each result is a sum of at most $N$ products of a fixed coefficient and a current coordinate; a common denominator formed by multiplying the term denominators and summing numerators gives this bound. Products, additions, reductions and destination writes are all charged at those widths.

Each Add performs a source rational addition and a predictor rational addition. A leaf Read selects and serializes the actual leaf rational; Read$_e$ serializes the actual native value and its predictor calculation uses two rational products and one addition. Hold changes no field but is still an actual control call with acknowledgement. Reset zeroes both $N$-coordinate representations. Native output $Qz$ uses its two-coordinate rotation plus all literal output traffic. Hypothetical continuation calculations require their own scratch copy and traffic; a retained journal grows with its actual length.

There is no lifetime bounded-bit-memory conclusion. For example the predictor leaf-difference coordinate satisfies

$$
z_{\ell_1}-z_{\ell_2}\longmapsto
\tfrac12(z_{\ell_1}-z_{\ell_2})
$$

on every passive Tick. At the earned cut its value is $1/4$, so after $r$ further passive Ticks it is $2^{-(r+2)}$. At least one of those two exact rational coordinate words must have denominator bit length growing linearly in $r$: the denominator of their difference divides the product of their denominators. Arbitrarily wide rational pulse inputs give an additional independent source of width growth. The attained “one scalar” claim concerns a call coordinate, not one bit or a bounded-precision sensor.

## 10. Supplier correspondence and the remaining programme

**Convention 10.1 (fixed mathematical sources).** Repository suppliers in this section are read at public revision [39687802cb999fa97ebdbf17f226a541563cc351][PIN]. The source-relative contribution consists of the family algebra, the all-true-leaf and fixed-order obstruction, the fixed-support coefficient separation, and the paid interior-read recovery and lower bounds with their actual continuation cut. Generic rank, realization, coordinate-intertwining and finite-word principles are credited supplies.

| Supplier | Hypotheses, correspondence and subtraction |
| --- | --- |
| [P §§36–43, especially Counterexample 42.2][P] | P uses an unknown positive rational path, authentic unit-pulse entrance and a Tick returning the new root scalar. Its three-cell root-fixing orthogonal example already separates native graph from full endpoint behavior in connected minimal systems. Here $N$ is supplied, the actual entrance is zero, Tick returns only acknowledgement, the ports are exactly all leaves, and the graphs contain cycles. The matrix calculation strengthens that particular native-graph boundary; it does not extend P's unknown-path acquisition or change P's Tick. |
| [Process Geometry §§1–3 and 17.2–17.4][PG] | The declared process has one state type, legal rational-input commands, successors and full output labels as in Definition 1.2. Equation (CL.13) checks the actual port-preserving intertwining. Minimal realization similarity already belongs to these suppliers: their $A,B,H$ are our $T,B,B^{\mathsf T}$. An orthogonal coordinate map need not be a native permutation. The new graph family and paid symmetry-breaking read are the additional content. |
| [NDR §§1–2, 5–7][NDR] | Its original source is an immutable ordered labelled tree with four-valued address replies. Its leaf evidence sufficiency and discovery ratio use that address contract; leaf scalar dynamics here are different observations. Its separation of actual history, retained context, phase/lifetime charges and chronology is retained. No tree traversal bound is transferred to these cyclic graphs. |
| [Native Constructor Boundary Networks, Convention 2.3 and §§7–9][CBN] | Canonical native coordinates and finite-array inverses are mathematical descriptions, without installation of an extra read port. Theorem 6.1 explicitly pays for the actual measured scalar and assumes the distinct port. Constructor-pair/fiber counting results concern their original tree sources and do not prove this graph obstruction. |
| [Compatible Predictive Waves §§4–6 and 13][Wave] | Its unitary criterion requires a positive metric with $T^\dagger GT=G$, and its native five-mode Hamiltonian has its own flip graph, control menu and quantum input domain. Here $T$ has spectrum strictly inside $(0,1)$, so those unitary-wave hypotheses fail. The present contractive rational source is a separately specified model. No phase control, hidden-mode acquisition, quantum recovery or universal alpha/beta generation is inferred from it. |
| [FiniteObservabilityEquivalence, finite_observability_equivalence][FO], with [owning Scribe][FOS] | State $\mathbb R^N$, output $\mathbb R^b$, update $T$, readout $B^{\mathsf T}$ and horizon five give the stacked readout in (CL.12). Its Gram/rank equivalence is supplied; the explicit leaf-to-interior span verifies this family's full-rank premise. |
| [FiniteHoKalmanBlocks][HK], with [owning Scribe][HKS] | For a finite-sample realization statement use field $\mathbb Q$, $h=5$, input/output counts $m=p=b$ and reference dimension $r=N$, with Markov convention $H T^kB$ and samples $k=0,\ldots,9$. Choose $N$ independent columns from $[B,TB,\ldots,T^4B]$ using (CL.12), and choose the matching transposed observation rows. Symmetry makes the base minor their positive definite Gram matrix. Its finite_samples_exact_recovery uses that nonsingular minor and returns behavior in reachable coordinates. Neither the theorem nor finite_samples_order_lower_bound identifies native graph support. No Hankel dataset or minor is supplied or acquired in (CL.17). |
| [ControlledBehaviorUniversality][CW], with [owning Scribe][CWS] | Its private run_word_intertwines already proves finite-word transport from commuting total updates, without a finite-carrier hypothesis. With one command/input as a letter and realization $x\mapsto Ux$, (CL.13) is that premise; complete output equality is checked separately in Theorem 4.2. Its public finite-cardinality universal theorem requires finite carriers and is not applied to the infinite rational field. The Scribe's general actual-image discussion retains this distinction. |
| Pinned upstream [Mathlib Matrix.Adjugate][MA] | The repository manifest pins mathlib at 56a005855ea17e0b0958f73ec801ae140b0a1679. Its Matrix.adjugate_mul and Matrix.mul_adjugate supply ordinary finite matrix inversion when determinant is nonzero, as consumed in FiniteHoKalmanBlocks. This is coordinate linear algebra, without native binding or a new port. |
| Karl J. Åström and Richard M. Murray, [Feedback Systems: An Introduction for Scientists and Engineers][AM], Princeton University Press, §§6.1 and 7.1 | Equations (6.3) and (7.4), Theorems 6.1 and 7.1, supply the mature reachability/observability matrix perspective. Their displayed differential-equation system has $A=T$, input matrix $B$ and output matrix $H$ as an algebraic correspondence only. The finite rational pulse realization in Corollary 3.2 and discrete transpose argument in Theorem 3.1 establish this service's own operational statements; no continuous impulse instrument is imported. |
| R. E. Kalman, [Mathematical Description of Linear Dynamical Systems][K], Journal of the Society for Industrial and Applied Mathematics, Series A: Control 1(2), 152–192 | Mature realization theory is credited for the distinction between state coordinates and input/output behavior. The complete actual initialization/rights/menu and the native family separation are given explicitly here; the citation supplies no physical conformance premise or graph-identity theorem. |

The publicly available D5 declarations and their private helper above are mathematical suppliers in their stated scopes. The source-relative results here do not assert worldwide priority. The native realization correspondence is earned by (CL.18) and the promised class, not by an API name.

The original leaf-only native inverse remains impossible on this family; adding the port does not solve it under its old interface. The reserved all-leaf unknown-tree acquisition problem is also different: these graphs are cyclic, order is supplied, and the successful protocol uses an interior port. No result here determines a universal generator pair, reconstructs arbitrary entry chronology or forgotten state, derives all physical laws, or completes mutual recovery throughout the continuing four-expression programme. Those tasks require their own source, action, acquisition and realization bridges.

[PIN]: https://github.com/the-omega-institute/trureturing/tree/39687802cb999fa97ebdbf17f226a541563cc351
[P]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY_II.md
[PG]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md
[NDR]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DISCOVERY_AND_RETAINED_CONTEXT.md
[CBN]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md
[Wave]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/docs/develop/theory/AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md
[FO]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/D5/S3/Observer/Linear/FiniteObservabilityEquivalence.lean
[FOS]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/Blueprint/D5/S3/Observer/Linear/FiniteObservabilityEquivalence.scribe.cs
[HK]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.lean
[HKS]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/Blueprint/D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.scribe.cs
[CW]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean
[CWS]: https://github.com/the-omega-institute/trureturing/blob/39687802cb999fa97ebdbf17f226a541563cc351/Blueprint/D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.scribe.cs
[MA]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/Adjugate.lean
[AM]: https://www.cds.caltech.edu/~murray/books/AM08/pdf/am08-complete_22Feb09.pdf
[K]: https://doi.org/10.1137/0301010

## 追加锚（本行以下为增补区）
