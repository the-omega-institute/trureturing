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

## 11. Calibrated native multiplication on a resettable boundary source

**Definition 11.1 (the broad native quadratic boundary class).** Let $N\ge1$ and $1\le b\le N$ be known integers. One actual source has native vertex set $V$, $|V|=N$, distinct authentically ordered ports $\ell_1,\ldots,\ell_b$, and an unknown fixed matrix $T=T^{\mathsf T}\in\mathbb Q^{V\times V}$. Write $B=[e_{\ell_1}\ \cdots\ e_{\ell_b}]$. Assume

$$
\operatorname{span}_{\mathbb Q}\{T^ke_{\ell_j}:0\le k<N,\ 1\le j\le b\}
=\mathbb Q^V.
\tag{CM.1}
$$

The initial actual field is zero. The commands Reset, Add$(j,u)$ for $u\in\mathbb Q$, Tick, Read$(j)$ and Hold have exactly the numerical actions and complete replies in Definition 1.2, with this $T$ and these ports. There is no interior read. In addition, the provider installs

$$
\operatorname{Square}:x\longmapsto x\odot x,
\qquad (x\odot y)_v=x_vy_v,
\qquad\text{reply a fixed acknowledgement}.
\tag{CM.2}
$$

For the graph interpretation, the off-diagonal coefficients are nonnegative and the support $\{\{v,w\}:v\ne w,\ T_{vw}>0\}$ is connected. The diagonal is arbitrary rational. Call this graph class NQB. Its ports need not be leaves or exhaust the leaves. The algebraic acquisition below also holds without the connectedness and sign conditions; those conditions give its stated native weighted-graph meaning.

Call QLAB-Sq the subclass with $N\ge2$, $b\ge3$, and the ports exactly the exhaustive true-leaf set of that positive-support graph, where a leaf has off-diagonal degree one. Thus QLAB-Sq retains a stronger authentic roster promise. Neither class assumes invertibility of $T$, a simple spectrum, contraction, or a cyclic single port. For example, a connected source with every vertex a port belongs to NQB but need not belong to QLAB-Sq. No reconstruction of an unlisted vertex name is required: the native output is modulo permutations carrying each ordered port to its counterpart.

**Assumption 11.2 (one commissioned native operation and complete serial calls).** The source binding, exact order, authentic port roster, whole-field zero entrance and Reset, signed rational units and codec, current call rights, Hold control, exclusive serial access, fixed law and sufficient finite backing are supplied. The rank promise (CM.1) is a class condition, not advice containing a basis or coefficients. Square uses coefficient one in those same native units. Its provider traverses the actual $N$-cell registry, reads and squares each actual field value, writes the destination values and commits the whole successor under serial exclusion. The observer receives no interior registry references. Registry, arithmetic, old/destination storage, traversal, commit and the Square grant are real installation and execution resources.

A completed legal call has its complete input, reply, acknowledgement where applicable, framing, End and Return consumed before the next settled cut. Proper incomplete frames retain their actual pending bytes and cause no completed field edit. Malformed, wrong-type, disabled and out-of-roster calls have fixed typed refusal and identity-successor semantics depending only on the common frame and authority context. Legal domains and these refusal frames are field- and law-independent within this installation. No timing, allocation, capacity, source identifier or other metadata reveals a coefficient or field. Hold covers local calculations with no uncommanded advancement; the next explicit command can be issued through the same serial control. The theorem concerns completed finite sufficiently backed runs with these rights retained. It supplies no crash, revocation, busy-cut or physical conformance theorem. Physical realization of this installation is **ASSUMED-UNVERIFIED**.

Square is a new source operation. Squaring a decoder coordinate or a returned leaf number is not (CM.2). Reset, exact order and native calibrated units are likewise not derived from the older no-Reset material service or from alpha/beta generation.

## 12. Earning the product by actual boundary trials

**Definition 12.1 (two complete calibration schedules).** Use the fixed port order and increasing exponent order for every list and exact rational pivot. First, for each $j=1,\ldots,b$, actually Reset, Add$(j,1)$, then at epochs $k=0,\ldots,2N-1$ perform Hold and all $b$ Reads, with one actual Tick between consecutive epochs. Store the returned matrices

$$
M_k=B^{\mathsf T}T^kB\quad(0\le k<2N).
\tag{CM.3}
$$

From these data select the first $N$ independent columns in the ordered Krylov list, by the Gram procedure in Theorem 12.2. Denote their indices by $(k_i,j_i)$, $1\le i\le N$, and use the probe list $e_i$ followed by $e_i+e_j$, $i<j$, in lexicographic order. Its length is $q=N(N+1)/2$. Every probe starts with a real Reset on the same specimen.

The dense schedule, denoted $\sigma=\mathrm d$, prepares probe $z$ as follows. For $s=N-1,N-2,\ldots,0$, issue every port Add with operand

$$
u_{s,j}=\sum_{i:k_i=s,\,j_i=j}z_i,
\tag{CM.4}
$$

where $u_s=(u_{s,1},\ldots,u_{s,b})^{\mathsf T}$. Include literal zero operands, and issue a Tick after the stage if $s>0$. There are $bN$ Adds and $N-1$ Ticks. Then actually Square. At epochs $0,\ldots,N-1$ after that Square, perform Hold and all $b$ Reads, with one Tick between epochs. Repeat for every probe. There is no final Reset; the last observation Hold covers decoding and installation.

The selected-pulse schedule, denoted $\sigma=\mathrm s$, instead issues Add$(j_i,z_i)$ for every selected index with $k_i=s$, including zero operands, at each descending stage $s$. Ties follow the index order. It performs a Hold at the end of each of the $N$ preparation stages, including empty stages, and a Tick between stages. It uses exactly $N$ Adds. Square and its observation window are identical to the dense schedule. After all probes it actually performs Reset and Hold, installing the zero field. The two schedules share the moment trials but retain their different preparation Holds, pulse lists and final endpoints.

**Theorem 12.2 (actual acquisition of native multiplication).** For every source of Definition 11.1 under Assumption 11.2, either schedule finitely earns rational matrices $G,A,D,E$ and a bilinear table $\mu$ on $\mathbb Q^N$. There exists an invertible proof-coordinate matrix

$$
R=[T^{k_1}e_{\ell_{j_1}}\ \cdots\ T^{k_N}e_{\ell_{j_N}}]
\tag{CM.5}
$$

such that

$$
\begin{gathered}
G=R^{\mathsf T}R,\qquad A=R^{-1}TR,\qquad
D=R^{-1}B,\qquad E=B^{\mathsf T}R,\\
\mu(u,v)=R^{-1}((Ru)\odot(Rv))\quad(u,v\in\mathbb Q^N).
\end{gathered}
\tag{CM.6}
$$

The controller never receives $R$ or $T$. In the dense schedule it also earns the actual endpoint coordinate $z_*=A^{N-1}\mu(z_{\rm last},z_{\rm last})$. In the selected-pulse schedule the actual endpoint is zero. Both assertions include singular $T$.

**Proof.** The moment trials genuinely have fields $T^ke_{\ell_j}$ at their reads, because they start with Reset and their only intervening field changes are the declared Ticks. Symmetry gives the candidate Gram entries

$$
\langle T^re_{\ell_j},T^se_{\ell_h}\rangle=(M_{r+s})_{jh}
\quad(0\le r,s<N).
\tag{CM.7}
$$

Over $\mathbb R$, a list of rational vectors is independent exactly when its Gram determinant is positive. Independence over $\mathbb Q$ and over $\mathbb R$ agrees by the nonzero-minor criterion. Greedily test these rational Gram determinants and retain independent candidates. By (CM.1), exactly $N$ can be selected. Thus $R$ in (CM.5) exists and is invertible, although its native entries remain unknown to the controller.

The earned entries

$$
\begin{aligned}
G_{ih}&=(M_{k_i+k_h})_{j_i j_h},&
L_{ih}&=(M_{k_i+k_h+1})_{j_i j_h},\\
V_{ij}&=(M_{k_i})_{j_i j},&
E_{ji}&=(M_{k_i})_{j j_i}
\end{aligned}
\tag{CM.8}
$$

use only the measured range through $2N-1$. They are $R^{\mathsf T}R$, $R^{\mathsf T}TR$, $R^{\mathsf T}B$ and $B^{\mathsf T}R$. Compute $A=G^{-1}L$ and $D=G^{-1}V$. Since $G^{-1}R^{\mathsf T}=R^{-1}$, the first line of (CM.6) follows. This is the supplied finite Ho–Kalman calculation [finite_samples_exact_recovery][CMHK] and its [owning Scribe][CMHKS], with field $\mathbb Q$, horizon $h=N$, state dimension $r=N$, $m=p=b$, and matching selected row/column indices $(k_i,j_i)$. Its base and shifted minors are exactly $G,L$. Known matching order is an explicit premise; [finite_samples_order_lower_bound][CMHK] does not turn a finite minor into an unknown-order upper certificate. The real Gram interpretation agrees with [finite_observability_equivalence][CMFO] and its [owning Scribe][CMFOS] after extension of scalars; no rational inner-product-space instance is presumed.

For a probe $z$, each actual pulse at descending stage $s$ has exactly $s$ remaining Ticks before the end of preparation. The dense endpoint is

$$
\sum_{s=0}^{N-1}T^sBu_s
=\sum_{i=1}^Nz_iT^{k_i}e_{\ell_{j_i}}=Rz.
\tag{CM.9}
$$

The selected-pulse endpoint is the same sum with its $N$ separate pulses. This is an executable legal pulse word using learned indices and rational operands, rather than a supplied native basis-vector preparation. Holds and zero operands do not change (CM.9).

Let $w=(Rz)\odot(Rz)$ be the actual immediate Square successor. Its subsequent all-port window contains, at the selected positions, the scalar vector

$$
s_i(z)=e_{\ell_{j_i}}^{\mathsf T}T^{k_i}w,
\qquad s(z)=R^{\mathsf T}w.
\tag{CM.10}
$$

Thus compute $F(z)=G^{-1}s(z)=R^{-1}w$. This uses actually returned scalars; Square itself returns none. The full window also has the learned injective observation matrix

$$
\mathcal O=\begin{pmatrix}E\\EA\\\vdots\\EA^{N-1}\end{pmatrix}.
\tag{CM.11}
$$

Its selected rows form $G$, since $e_{\ell_{j_i}}^{\mathsf T}T^{k_i}R$ is row $i$ of $G$. Consequently any rational left inverse of $\mathcal O$ yields exactly the same $F(z)$ as (CM.10). These are two computations from one measured window, not two different acquisition results.

Every probe window ends at $T^{N-1}w$, whose response coordinate is $A^{N-1}F(z)$. It does not end at $Rz$ or at $w$. The last such coordinate gives the dense endpoint in the statement. The selected-pulse schedule's additional actual Reset makes its endpoint zero.

Finally put $\mu(e_i,e_i)=F(e_i)$ and, for $i<j$,

$$
\mu(e_i,e_j)=\mu(e_j,e_i)
=\tfrac12\bigl(F(e_i+e_j)-F(e_i)-F(e_j)\bigr),
\tag{CM.12}
$$

and extend bilinearly. Polarization of the actual native product proves the second line of (CM.6) for every rational $u,v$. Only the $q$ declared probes were performed. The controller obtains a finite table from them, not an oracle for unperformed experiments. Matrix inversion, rational pivots and the finite sums terminate on each promised input. $\square$

The uncovered operation-to-data bridge in this theorem is (CM.9)–(CM.12), including its actual advanced endpoint. The Gram realization and polarization identities are reused mathematics inside that bridge. Full rank failure would defeat this construction; it is not a proof that every nonlinear acquisition method fails outside (CM.1).

## 13. From the earned product to native vertices

**Theorem 13.1 (effective native axes and exact residual ambiguity).** The earned data of Theorem 12.2 effectively determine the whole native coefficient law and its positive-support graph up to an ordered-port-fixing permutation. No simple-spectrum premise on $T$ and no additional source call is needed. Two sources in the same class and common installation have equal complete calibration tables for a fixed schedule if and only if their laws are related by such a permutation. Here the table includes all measured moment and Square-window scalars; pulse choices are the deterministic functions of the moment table in Definition 12.1.

**Proof.** Use the classical diagonal-contraction method in [Anandkumar et al., Appendix D][CMTensor] on the acquired algebra: multiplication $L_z:v\mapsto\mu(z,v)$ satisfies

$$
R L_zR^{-1}=\operatorname{diag}(Rz).
\tag{CM.13}
$$

The rows $r_a$ of the unknown invertible $R$ are pairwise distinct. For $z(t)=(1,t,\ldots,t^{N-1})^{\mathsf T}$, every row difference $(r_a-r_c)z(t)$ is a nonzero polynomial of degree at most $N-1$. Their product is nonzero with degree at most

$$
d=\binom N2(N-1).
\tag{CM.14}
$$

A nonzero degree-at-most-$d$ polynomial cannot vanish at all integers $0,\ldots,d$. Thus one of these finitely many $t$ gives distinct diagonal entries in (CM.13). For $N=1$ the empty product is one and $d=0$. The controller forms each rational $L_{z(t)}$ and tests whether its characteristic polynomial is squarefree by the polynomial gcd with its derivative. By (CM.13), the successful test is exactly the distinct-entry condition and will occur.

All eigenvalues of that successful matrix are rational, because they are the actual rational coordinates of $Rz(t)$. They are found without an eigenvalue oracle: clear denominators in the characteristic polynomial, remove any zero-root factor, enumerate the finitely many signed numerator divisors of the remaining constant coefficient and positive denominator divisors of its leading coefficient, test, and divide out the found linear factors. This is the ordinary rational-root theorem, as supplied at the pinned upstream by [num_dvd_of_is_root and den_dvd_of_is_root][CMRoots]. The promised splitting and simple roots ensure that this finite calculation finds all $N$ roots, including zero when present. Solve their rational nullspaces and select a deterministic nonzero eigenvector $v_a$ on each eigenline. Equation (CM.13) implies $Rv_a=c_ae_{\pi(a)}$ for a nonzero rational $c_a$. Hence

$$
F(v_a)=\mu(v_a,v_a)=c_av_a.
\tag{CM.15}
$$

Take any nonzero coordinate of $v_a$, obtain $c_a$ by the ratio in (CM.15), and set $w_a=v_a/c_a$. Then $Rw_a=e_{\pi(a)}$. This normalization removes sign and scale; no unknown unit vector has been supplied. Order the eigenvalues increasingly, identify each port by the unique equality $D_j=w_a$, and reorder the columns with those $b$ port atoms first in their authentic order and the remaining atoms in eigenvalue order. Write $W=[w_1\ \cdots\ w_N]$. Then $RW=P$ is a permutation matrix and

$$
\widehat T=W^{-1}AW=P^{\mathsf T}TP,
\qquad \widehat B=W^{-1}D=P^{\mathsf T}B,
\qquad \widehat x=W^{-1}z=P^{\mathsf T}x.
\tag{CM.16}
$$

These recover every diagonal and off-diagonal coefficient, hence the weighted native graph, in a port-labelled representative. The anonymous remaining atoms are not raw native references. In particular $W^{\mathsf T}GW=I$, so the Gram-normalized and matrix-inverse conversions agree.

For completeness, consider equal tables on two sources, and let $R,R'$ be their proof matrices chosen by the same Gram pivots. Their $G,A,D,E,F$ and $\mu$ agree. Put $U=R'R^{-1}$. The learned identities give $UT=T'U$, $UB=B'$ and

$$
U(x\odot y)=(Ux)\odot(Uy)\quad(x,y\in\mathbb Q^N).
\tag{CM.17}
$$

This is the elementary rigidity of the finite function algebra. Each $Ue_v$ is a nonzero idempotent, so every one of its coordinates is zero or one. Distinct such columns have disjoint supports by (CM.17). There are $N$ disjoint nonempty supports in $N$ coordinates, forcing each to be a singleton. Thus $U$ is a permutation, and $UB=B'$ fixes the ordered port correspondence. Conversely a port-fixing permutation intertwines Reset, Add, Tick, Read, Hold and native Square, preserves zero, and preserves every deterministic trial and reply. It therefore gives equal full calibration tables. The full-interface rigidity principle is mature; [diagonal_interface_conjugacy][CMDiag] and its [owning Scribe][CMDiagS] concern a supplied diagonal-operator interface on complex finite-state transfer spaces. They supply neither (CM.9)–(CM.12) nor a general acquisition theorem for these weighted matrices. $\square$

The bounded integer search and atom normalization are a finite exact decoder of the earned table, not a polynomial bit-work or conditioning claim. Equal linear moments alone only give the orthogonal realization ambiguity of [minimal_symmetric_realization_uniqueness][CMMS] and its [owning Scribe][CMMSS]. In that supplier the state spaces are finite-dimensional real inner-product spaces, update is symmetric, input map is $B$, equality concerns every $B^{\mathsf T}T^kB$, and both reachable spans are full. Its private combination, Gram and kernel arguments establish that coordinate conclusion. The actual acquired multiplication is the extra premise that reduces it to (CM.17).

## 14. Retained nonlinear service and the two attained calibration bills

**Definition 14.1 (earned current memory).** Retain the learned $G,A,D,E,\mu$, selected indices, atom conversion $W$, common program/codec and authentic same-source callable context. Retain a current response vector $z$, initialized to the actual endpoint in Theorem 12.2. Complete calibration tapes may be retained for an explicitly exposed Time view, with their separate backing; they are not required as the predictor's state. Native snapshots are exported by (CM.16), charging any literal matrix/vector copies.

**Theorem 14.2 (complete synchronized actual continuation).** Either calibration installs exact prediction for every finite sufficiently backed common adaptive continuation of the entire menu of Assumption 11.2 on that same specimen, including Square, arbitrary rational boundary inputs, later Resets and the declared invalid/pending frames. At every settled cut the native invariant is $x_{\rm actual}=Rz$.

**Proof.** The local rules for complete legal calls are

| Call | Retained successor | Complete predicted reply |
| --- | --- | --- |
| Reset | $z:=0$ | its fixed ACK |
| Add$(j,u)$ | $z:=z+uD_j$ | its fixed ACK |
| Tick | $z:=Az$ | its fixed ACK |
| Square | $z:=\mu(z,z)$ | its fixed ACK |
| Read$(j)$ | $z$ | the literal rational $(Ez)_j$ |
| Hold | $z$ | its fixed ACK |

The initial invariant is Theorem 12.2. Reset, Add and Tick preserve it by (CM.6); Square preserves it by the product identity in that same equation; Read agrees by $E=B^{\mathsf T}R$; Hold preserves the field. For an actual call, forward its actual complete frame through the retained right, consume its whole actual reply and Return, and commit the displayed update before the next settled call. Fixed invalid-call/refusal frames have the same identity successor on both sides; proper incomplete frames retain their actual common pending bytes and have no completed update. Equal consumed histories and common external inputs select equal next calls and operands under a common adaptive controller. Induction proves every complete reply, pending-prefix correspondence and actual successor for a finite continuation. Fixing a common random tape gives the same pointwise argument. Hypothetical forecasts require scratch copies of the retained state and perform no source call. No arbitrary erased history is reconstructed. $\square$

**Proposition 14.3 (two simultaneous finite call vectors).** In the coordinate order $(\mathrm{Reset},\mathrm{Add},\mathrm{Tick},\mathrm{Square},\mathrm{Read},\mathrm{Hold})$, Definition 12.1 realizes respectively

$$
\begin{aligned}
\mathcal C_{\rm d}={}&\bigl(b+q,\ b+bNq,\ b(2N-1)+2q(N-1),\ q,\ 2Nb^2+bNq,\ 2Nb+Nq\bigr),\\
\mathcal C_{\rm s}={}&\bigl(b+q+1,\ b+Nq,\ b(2N-1)+2q(N-1),\ q,\ 2Nb^2+bNq,\ 2Nb+2Nq+1\bigr).
\end{aligned}
\tag{CM.18}
$$

The first endpoint is the actual final Square trial after its read window; the second is actual zero. These are attained whole vectors, not coordinatewise optima.

**Proof.** Each of $b$ impulse trials uses one Reset, one Add, $2N-1$ Ticks, $2Nb$ Reads and $2N$ Holds. Each of $q$ Square trials uses one Reset, one Square, $2(N-1)$ Ticks, $bN$ Reads and $N$ observation Holds. Its dense preparation has $bN$ Adds and no preparation Holds; its selected preparation has $N$ Adds and $N$ preparation Holds. The latter schedule alone adds a final Reset and Hold. Summing gives (CM.18), including literal zero input frames. Each non-Read call returns its own ACK, and every Read returns one whole rational. There is no implicit scalar on Tick or Square. $\square$

**Construction 14.4 (one actual selected use).** At either installed endpoint compute $u=(Ez)_1$ from the earned predictor and actually issue Add$(1,u)$, Square, Hold and Read$(1)$. The returned rational is $(2u)^2$. The entire actual field, rather than only its leaf, is updated, and Theorem 14.2 remains synchronized. This adds one of each displayed call and their complete input/output frames to the chosen vector. The authentic port choice and whole operand are submitted and paid; neither is an unknown-source selector oracle.

## 15. All-current four-view recovery at performed Report cuts

**Definition 15.1 (Report and its four independent exposures).** Fix either deterministic calibration schedule $\sigma$ of Definition 12.1 and the source-independent conventions used for its pivots and local decoder. Add the hypothesis $\det T\ne0$ in this section. This hypothesis is not used in §§12–14. After calibration and any finite actual intervening legal calls, begin at the actual current $x_0$ and perform Report: at relative epochs $0,\ldots,N-1$, actually Hold and Read all ports, with one Tick between epochs. The actual endpoint is

$$
x_*=T^{N-1}x_0.
\tag{CM.19}
$$

Retain its completed relative phase and same-source context. Let $K_\sigma(T)$ be the finite table of all actual moment and Square-window returns in calibration. It specifies a finite list of performed experiments, not an unrestricted response profile. Let

$$
g_T(x_*)=(B^{\mathsf T}T^kx_*)_{0\le k<N}
\tag{CM.20}
$$

be the current passive boundary germ. This germ is a paid computed export from the synchronized acquired predictor; it is available prediction and is not represented as a newly measured future word. If a new physical window is requested, it is a new Report with new costs and a new endpoint.

On actual completed runs, modulo port-fixing native permutations, expose:

| Expression | Exposed data and independent meaning |
| --- | --- |
| Space $\mathsf S$ | native weighted support, full coefficients $T$, and actual current native field $x_*$ |
| Time $\mathsf T_\sigma$ | the actual complete deterministic calibration word and the latest performed Report word, with all inputs, replies and relative Tick/Hold/return order |
| Boundary $\mathsf B_\sigma$ | the acquired finite first-/second-order experiment table $K_\sigma(T)$ and the present passive response germ $g_T(x_*)$ |
| Memory $\mathsf M_\sigma$ | the earned model/product/atom representation of Definition 14.1, its synchronized current vector and completed phase/callable context |

Time omits intervening arbitrary journals and unknown wall durations. Boundary contains only finite experimental responses and a present response germ. Memory is a finitely described predictor with rational state for future legal prediction. Its numerical state space and word widths are unbounded. Common context includes the schedule, port order, codecs, actual bindings/rights and the fact that these transactions occurred. It contains no law, field or source-dependent advice beyond data genuinely earned in the run. Provenance and authority are premises of this joint actual image and are not outputs of numerical inversion.

**Theorem 15.2 (mutual recovery, service kernel and route agreement).** On the actual Report image of Definition 15.1 every expression recovers the exposed numerical content of each other expression. Their kernels equal the complete current continuation-service kernel for the named menu in fixed authority context: native law and current field modulo port-fixing permutation. All ordered recovery routes agree. The result holds on the whole invertible NQB class and hence on its invertible QLAB-Sq subclass, at every rational current Report endpoint, with $\sigma$ retained.

**Proof.** Time contains the measured calibration, so §§12–13 recover the law and its response coordinates. Its latest Report contains the actual observation window at $x_0$. Selecting positions $(k_i,j_i)$ gives $R^{\mathsf T}x_0$; multiplying by $G^{-1}$ gives $z_0=R^{-1}x_0$. Advancing by the actually executed $N-1$ Ticks gives $z_*=A^{N-1}z_0$, hence $x_*$. Boundary's $K_\sigma(T)$ gives the same learned law, while its selected germ coordinates give $R^{\mathsf T}x_*$. The same solve recovers the current vector directly. Space supplies the native law/current field. Memory supplies them by (CM.16).

Conversely, from any representative $(T,x_*)$, calculate every numerical calibration response by its deterministic pulses, native Square and read windows. This regenerates $K_\sigma(T)$, all deterministic choices, and the numerical calibration word. It does not assert that recalculation is a measurement or that calibration has been physically repeated. Because $T$ is invertible, $x_0=T^{-(N-1)}x_*$ is unique and reproduces exactly the measured latest Report. Reapply the deterministic data decoder to obtain the unique retained response model and $z_*=R^{-1}x_*$. Forward evaluation gives (CM.20). Every encoding is therefore a deterministic function $\mathcal E_i^\sigma(T,x_*)$ and each proved decoder $\mathcal D_i^\sigma$ returns that same native pair on its actual image. Thus

$$
\mathcal D_i^\sigma\mathcal E_i^\sigma=\mathrm{id},\qquad
\mathcal E_i^\sigma\mathcal D_i^\sigma=\mathrm{id}
\text{ on its image},\qquad
(\mathcal E_k^\sigma\mathcal D_j^\sigma)
(\mathcal E_j^\sigma\mathcal D_i^\sigma)
=\mathcal E_k^\sigma\mathcal D_i^\sigma.
\tag{CM.21}
$$

Here native pairs are taken modulo the declared port-fixing permutations. All quantities computed from a different representative agree in that quotient; the deterministic moment/pivot/product arrays themselves are unchanged.

For the task kernel, a port-fixing permutation of equal native law/current field preserves every numerical action, reply and successor, including Square and all fixed invalid frames. Induction gives complete common adaptive service equality. Conversely, equal complete future service permits an actual Reset followed by the fixed calibration, so the two native laws must be related by Theorem 13.1's port-fixing permutation. This law correspondence is unique: any automorphism commuting with $T$ and fixing $B$ fixes every $T^kB$, hence is identity by (CM.1). After aligning the laws, compare the current states before that hypothetical Reset. The finite all-port linear observation window is injective by (CM.11), so equal service forces equal current fields. Thus the current pair is exactly the continuation kernel, rather than just a sufficient over-description.

Every rational target field is actually reachable from zero: if the target in the recovered native representative is $\widehat x_0$, compute $z=W\widehat x_0$ from the learned atom matrix and use the actual pulse word (CM.9). Its endpoint is $RW\widehat x_0=P\widehat x_0$, the target field in the actual native frame. The unknown proof matrix $R$ is not an input. The initial Reset and this pulse preparation are additional paid calls when required. Invertibility makes $x_*=T^{N-1}x_0$ range over all rational fields as well. The proof uses no combination of separate favorable source realizations. $\square$

**Proposition 15.3 (actual reporting dynamics and singular failure).** For a common actual menu call $c$ at a Report cut, let $U_c(T,x)$ and $r_c(T,x)$ be its native successor and complete reply. Execute that call and then a new actual Report. The new endpoint is

$$
\Phi_c(T,x)=\bigl(T,T^{N-1}U_c(T,x)\bigr).
\tag{CM.22}
$$

On the declared images the transported view dynamics $\mathcal E_i^\sigma\Phi_c\mathcal D_i^\sigma$ commute with all recovery routes and emit the same $r_c$. This is the call-plus-Report evolution, not the bare call. A bare call still has the exact predictor of Theorem 14.2; it does not supply a new measured Time record. Without invertibility, the historical inverse in Theorem 15.2 can fail even in QLAB-Sq, while acquisition and current prediction remain valid.

**Proof.** The actual call gives $U_c(T,x)$ and its complete reply; the subsequent $N-1$ real Ticks give (CM.22). The new actual read window, held completion and predictor updates supply precisely the new encodings. Substitution in (CM.21) proves each commuting square and equality of emitted replies. Each Report adds $bN$ Reads, $N-1$ Ticks and $N$ Holds, plus its record, solves, exports and full traffic; $c$ itself is also charged.

For the singular counterexample take the star with $b\ge3$ leaves and center $o$, $N=b+1$, and let $T$ be its unit zero-diagonal adjacency. All true leaves are ports. Leaf columns and $Te_{\ell_1}=e_o$ span all coordinates, so (CM.1) holds. The rational nonzero $\eta=e_{\ell_1}-e_{\ell_2}$ satisfies $T\eta=0$. Reports from $x_0=0$ and $x_0=\eta$ have different epoch-zero reads but the same endpoint zero because $N-1\ge1$. The law, current field, germ and current predictor coincide, while their latest performed Time records differ. Both entries are preparable by legal Adds after the same calibration. This disproves the unqualified current-to-prior-Report inverse on the singular class. Likewise Reset and Reset followed by Tick give identical present zero states but different arbitrary journals even for invertible $T$. No current-state chart recovers those journals. $\square$

## 16. Two complete one-Square calibrations on the entire cyclic family

**Definition 16.1 (the changed family menu).** Retain precisely the rational family $\mathcal P$, $b\ge3$, $N=b+4$, $\epsilon=1/(4N)$, $T=QT_0Q^{\mathsf T}$, native correspondence and actual zero entrance of Definition 1.1. Retain the original leaf service of Definition 1.2 and Assumption 1.3. Install native Square under Assumption 11.2, but do not install Read$_e$. Theorems 2.2 and 3.1 already give connected positive support, exactly these true leaves, invertibility and full joint rank. This is an infinite subclass of QLAB-Sq. The old full-service equivalence in Theorem 4.2 and the sufficient interior-port repair in §6 retain their respective original menus.

Write $\sigma=\mathrm n$ for the following natural pulse word:

$$
\operatorname{Add}(1,1);\ \operatorname{Tick};\ \operatorname{Tick};\
\operatorname{Square};\ \operatorname{Tick};\ \operatorname{Tick};\
\operatorname{Read}(1);\ \operatorname{Hold}.
\tag{CM.23}
$$

Write $\sigma=\mathrm p$ for the isolated-signal word, with $a_0=\epsilon^{-2}$:

$$
\begin{gathered}
\operatorname{Add}(1,a_0);\ \operatorname{Tick};\ \operatorname{Hold};\
\operatorname{Add}(1,-a_0);\ \operatorname{Tick};\ \operatorname{Hold};\\
\operatorname{Add}(1,a_0/4-1);\
\operatorname{Add}(2,-1);\cdots;\operatorname{Add}(b,-1);\ \operatorname{Hold};\\
\operatorname{Square};\ \operatorname{Tick};\ \operatorname{Tick};\
\operatorname{Read}(1);\ \operatorname{Hold}.
\end{gathered}
\tag{CM.24}
$$

Both act on the installed zero specimen without Reset. They are different full preparations, not two ways of labelling one endpoint.

**Theorem 16.2 (whole-family acquisition and the two actual endpoints).** Each word identifies every permitted rational $(C,S)$ and earns a full current nonlinear predictor on its actual endpoint. Set

$$
a=C^3+S^3,\qquad h=CS(S-C),\qquad r=\tfrac14+\epsilon^2.
\tag{CM.25}
$$

The respective actually acquired scalars and native endpoints are

$$
\begin{aligned}
y_{\rm n}&=r^3+(b-1)\epsilon^6+\epsilon^3+\epsilon^6a,&
w_{\rm n}&=T^2\bigl((T^2e_{\ell_1})\odot(T^2e_{\ell_1})\bigr),\\
y_{\rm p}&=\epsilon^2a,&
w_{\rm p}&=QT_0^2(ae_d+he_e).
\end{aligned}
\tag{CM.26}
$$

No other scalar read is used. In the call-coordinate order of (CM.18), the attained vectors are

$$
\mathcal C_{\rm n}=(0,1,4,1,1,1),\qquad
\mathcal C_{\rm p}=(0,b+2,4,1,1,4).
\tag{CM.27}
$$

They return respectively seven and $b+11$ fixed ACKs as well as their own whole scalar.

**Proof.** Formula (CL.19), already proved for this exact family, gives $v=T^2e_{\ell_1}$ with values $r$ at $\ell_1$, $\epsilon^2$ at other leaves, $\epsilon$ at $c$, $\epsilon^2C$ at $d$, $\epsilon^2S$ at $e$ and zero at $f$. After the real Square and two further real Ticks, symmetry yields

$$
y_{\rm n}=e_{\ell_1}^{\mathsf T}T^2(v\odot v)
=v^{\mathsf T}(v\odot v)=\sum_{u\in V}v_u^3,
\tag{CM.28}
$$

which gives the first line of (CM.26), including its actual four-Tick endpoint.

For (CM.24), the field before Square is exactly

$$
\epsilon^{-2}(T^2-T+I/4)e_{\ell_1}-\sum_{j=1}^be_{\ell_j}
=Qe_d=Ce_d+Se_e.
\tag{CM.29}
$$

Indeed the first two pulses followed by their two Ticks give $a_0(T^2-T)e_{\ell_1}$. The remaining Adds give the rest of the left side. Also $T-I/2=\epsilon QA_0Q^{\mathsf T}$, and $A_0^2e_{\ell_1}=\sum_je_{\ell_j}+e_d$, so cancellation proves the equality. This is an actually realized pulse polynomial; it assumes neither an interior actuator nor knowledge of $C,S$.

Native Square sends (CM.29) to $C^2e_d+S^2e_e$. Its template coordinates are

$$
Q^{\mathsf T}(C^2e_d+S^2e_e)=ae_d+he_e.
\tag{CM.30}
$$

Two actual Ticks therefore give $w_{\rm p}$ in (CM.26). The coefficient from $d$ to $\ell_1$ in $T_0^2$ is $\epsilon^2$ and the coefficient from $e$ to $\ell_1$ is zero, by the two-step edge list (CL.2). Hence its leaf read is exactly $y_{\rm p}=\epsilon^2a$.

Normalize the respective actual scalar by its own line of (CM.26) to obtain $a$. Put $p=C+S$. The promised arc gives $1\le p\le7/5$, $C-S\ge1/5$, and

$$
a=\frac{3p-p^3}{2},\qquad C-S=\sqrt{2-p^2}.
\tag{CM.31}
$$

For $1\le p_1<p_2\le7/5$,

$$
(p_2^3-3p_2)-(p_1^3-3p_1)
=(p_2-p_1)(p_2^2+p_1p_2+p_1^2-3)>0.
\tag{CM.32}
$$

Thus $p$ is the unique root in that interval of $p^3-3p+2a=0$. The root is rational by the source promise and finite rational-root enumeration finds it, including the repeated root at $a=1,p=1$. The nonnegative rational square root of $2-p^2$ is found by taking integer square roots of its reduced numerator and denominator; the promise says both are perfect squares. Return

$$
C=\tfrac12(p+\sqrt{2-p^2}),\qquad
S=\tfrac12(p-\sqrt{2-p^2}).
\tag{CM.33}
$$

This terminates exactly on the entire rational arc, including $S=0$. Substitution gives $T$ and the correct schedule-specific field in (CM.26). Initialize $z_\sigma=Q^{\mathsf T}w_\sigma$ and retain $x=Qz$. The linear update rules of Theorem 6.3 apply with only its original leaf reads, and native Square has the additional local rule

$$
z:=Q^{\mathsf T}\bigl((Qz)\odot(Qz)\bigr).
\tag{CM.34}
$$

It preserves the same actual invariant. Theorem 14.2's complete-call induction therefore supplies the full changed-menu predictor from this actual earned cut. Counting the literal words gives (CM.27) and their ACKs. $\square$

**Proposition 16.3 (necessary call coordinates and calibrated-operation boundary).** Uniform exact family identification in the menu of Definition 16.1 requires at least one Square and one successful scalar Read on every identifying path of an everywhere-correct deterministic finite protocol. The two words attain these coordinates simultaneously, without a Tick, bit, energy or total-resource optimality claim. Replacing native Square by a radial orthogonally equivariant nonlinearity or a transported-coordinate square need not break the old ambiguity. The scalar inverse is not uniformly Lipschitz at $S=0$.

**Proof.** On any identifying path without Square, the complete acquired history is an old-service path, so Theorem 4.2 gives that same history, stopping decision and output on every parameter. The native laws differ by Theorem 5.1, making uniform exact identification impossible on that path. On a path with no successful scalar Read, even with Squares, every obtained reply is a common ACK or fixed refusal. Induction on that history again makes the whole path and terminal answer independent of the parameter. The same pointwise argument applies to fixed common random tapes; for zero-error almost-sure termination on every rational family member, intersect the probability-one events over the countable rational family before applying it. The lower coordinates then hold almost surely for each entry.

For the radial gate $x\mapsto\|x\|_2^2x$, every orthogonal $U$ in (CL.13) commutes with the gate. Thus the same full-service coupling as Theorem 4.2 survives its addition. For the transported gate $\widetilde{\operatorname{Square}}_p(x)=Q((Q^{\mathsf T}x)\odot(Q^{\mathsf T}x))$, the actual pre-gate state in (CM.29) is mapped to $Qe_d$. Its later leaf read is $\epsilon^2$, independent of the parameter. At $C=4/5,S=3/5$, the genuine native read is $(91/125)\epsilon^2$. These are different operations in different coordinate ownership, not alternative implementations of (CM.2). This pair is a conformance discriminator for those specified gates, not global authentication of an unrestricted black box from finite tests.

Finally,

$$
1-a=S^2\left(\frac{1+C+C^2}{1+C}-S\right),\qquad
\frac{34}{45}S^2\le1-a\le\frac32S^2.
\tag{CM.35}
$$

For the bounds use $\frac{1+C+C^2}{1+C}=C+1/(1+C)$, increasing for $4/5\le C\le1$, its endpoint values $61/45,3/2$, and $0\le S\le3/5$. Rational arc parameters approach $S=0$ by (CL.5). Their parameter distance is at least $S$, whereas either scalar's distance from its $S=0$ value is a fixed positive multiple of $1-a=O(S^2)$. No uniform Lipschitz inverse exists there. A larger algebraic signal coefficient does not establish a noise or finite-resolution guarantee. $\square$

## 17. Cyclic acquired-image views and real selected use

**Definition 17.1 (two distinct calibration images).** Fix $b$, the family, authentic context and one schedule $\sigma\in\{\mathrm n,\mathrm p\}$ of Definition 16.1. Its common cut is after the final Read and Hold, with the full return consumed and the predictor installed at $w_\sigma$. On these actual runs expose:

| Expression | Exposed independent content |
| --- | --- |
| Space | the native weighted law $T$ and present field $w_\sigma$, modulo leaf-fixing permutations |
| Time | that schedule's actual complete ordered command/input/reply word, four Tick occurrences and completed held phase |
| Boundary | the original leaf transfer $B^{\mathsf T}(\zeta I-T)^{-1}B$ and the one actually returned current leaf-1 scalar $y_\sigma$ |
| Memory | the earned $(C,S,z_\sigma)$ predictor, rules including (CM.34), and genuine callable context |

Here $\zeta$ is a formal resolvent variable. The transfer is the public common template $B^{\mathsf T}(\zeta I-T_0)^{-1}B$ by (CL.14); it carries no hidden parameter advice and is not said to have been separately measured. Only Time retains the calibration word. Neither image contains arbitrary current fields or arbitrary previous histories.

**Proposition 17.2 (all numerical routes agree on each actual image).** On either fixed image in Definition 17.1, all four expressions mutually recover their displayed numerical content and have the same kernel as the complete current-service task restricted to that image. They are distinct images with distinct endpoints. Current callable use survives leaving an image; its historical inverse is not extended by that fact.

**Proof.** Time and Boundary give their actual $y_\sigma$. Theorem 16.2 recovers the unique $(C,S)$, native law and actual endpoint $w_\sigma$. Space gives the same scalar as $(w_\sigma)_{\ell_1}$ and uses the same decoder. Memory gives its earned parameter and $w_\sigma=Qz_\sigma$. Conversely those parameters compute the designated word's numerical inputs and replies, common transfer, present field and initialized predictor. Therefore every pairwise conversion factors through the same $(C,S)$; encoder/decoder round trips and all route compositions agree on that one image as in (CM.21). Actual occurrence, references, installed Square and call rights remain common premises, not regenerated numerical content.

Distinct parameters have distinct native coefficient laws even modulo leaf-fixing permutations by Theorem 5.1. Future actual Reset followed by the same finite Square calibration distinguishes them. Equal parameter/image point gives equal law/current field and complete service by the predictor induction. Thus the view and restricted continuation kernels agree. Nothing identifies $w_{\rm n}$ with $w_{\rm p}$. $\square$

**Construction 17.3 (paid nonlinear use on either earned endpoint).** Decode $S$, then actually issue Add$(1,S)$, Square, Hold and Read$(1)$ on that same specimen. The scalar returned is $(y_\sigma+S)^2$, and the complete native endpoint is

$$
(w_\sigma+Se_{\ell_1})\odot(w_\sigma+Se_{\ell_1}).
\tag{CM.36}
$$

This adds exactly one Add, one Square, one Hold and one Read, three ACKs and a scalar, plus the actual operand, selector, framing, arithmetic and storage. The parameter-derived operand is computed from the actual acquired scalar. Formula (CM.34) synchronizes the whole predictor. This successor need not remain on the calibration image. In particular the general inverse after arbitrary later calls is not Proposition 17.2: Reset and Reset;Tick already have equal current zero states and different words. If a new measured chart is wanted, the invertible family qualifies for Definition 15.1, but its actual Report and its own endpoint/cost must then be supplied. No performed measurement or chart dynamics is obtained by silently computing a forecast.

## 18. Same-source arithmetic, material and precision resources

**Convention 18.1 (literal width-dependent account).** Rational words use reduced signed binary numerators and positive denominators with framing. Every source coefficient, field, pulse, received scalar, local intermediate, table entry, root-search bound and output buffer is charged at its actual width. Let $L$ be a maximum of these widths on one specified finite run; this is an accounting variable after specifying that run, not free advice or a bound determined by $N$ alone. Installation pays its source law, zero/Reset provision, cell registry, port references and units, Square and serial-control implementation, genuine rights and backing. These costs coexist with the observer stores.

**Proposition 18.2 (a simultaneous literal implementation account).** The call vectors (CM.18) or, separately, (CM.27), can be realized with the following additional source and observer work and retained stores. They make no lifetime bit bound or total-resource minimality assertion.

| Resource | Account on the same chosen run |
| --- | --- |
| Source law and registry | one actual native $T$ store, up to $N^2$ rational words in a dense representation, native incidence/registry and authenticated port bindings |
| Source field and destination | $N$ current rational words and a distinct $N$-word destination buffer when an out-of-place update is used |
| Each source Tick | a dense implementation uses $N^2$ rational products, $N(N-1)$ additions and $N$ destination writes; zero coefficients may instead be handled by its explicitly chosen sparse representation |
| Each source Square | $N$ native rational products, source reads, $N$ destination writes and one whole-field serial commit |
| Each Reset/Add/Read | respectively $N$ zero writes, a genuine port addition, or source selection/serialization of the entire rational; every actual frame/ACK/End/Return remains charged |
| General acquired data | $2Nb^2$ moment rationals; selected indices; $G,A,D,E$ and solve scratch; up to $N^3$ stored product coefficients; $N^2$ atom/conversion entries and native export buffers |
| General current prediction | a separate $N$-vector and destination/scratch, plus actual local updates and full reply processing; these do not replace the source field or its work |
| Measured chronology | all retained calibration windows, actual pulse operands/indices, call tags and framing, plus any latest Report or later journal that is exposed or retained |
| Cyclic prediction | earned $C,S$, current $N$-vector in template coordinates, a separate destination vector and actual rotation/square arithmetic; any literal native-law copy is an extra store |
| All contexts | code, pivot/root/phase counters, parser and pending/input/output buffers, source/port references, current grants and storage backing at each owner |

For a concrete general observer representation, evaluate each $\mu(z,z)$ directly from its dense table. This uses at most $2N^3$ rational products and $N^3-N$ additions, with its own destination vector; each predictor Tick uses its own dense $A$ multiplication. This particular representation's bill accompanies either chosen source schedule. A conversion to native-atom predictor coordinates is possible but is a different explicit arithmetic representation, not a free substitution of favorable work coordinates.

**Proof.** Dense matrix-vector multiplication and direct expansion of the bilinear table give the stated arithmetic counts. The native Square count follows from its specified actual implementation, not from the number of opcodes. The schedules measured $2Nb^2$ impulse scalars and $bNq$ Square-window scalars. Retaining their literal Time, pulse inputs, the learned arrays and a streaming Gram-pivot implementation uses

$$
O(b^2N+bNq+N^3+Nb+N^2)
\tag{CM.37}
$$

rational data slots, in addition to framing, indices, references, code and any separate copies/exports. Gram entries can be evaluated from the moment table as required, retaining only the current selected minor rather than the entire $bN$-square candidate Gram. The selected-pulse schedule may omit dense pulse slots in its own retained word; (CM.37) is a simultaneous sufficient upper store, not a lower bound or optimized storage formula. A literal added Report retains its $bN$ scalar returns, held epoch/order data and solve scratch, and has the call increment in Proposition 15.3. Every local solve, rational reduction, characteristic-polynomial/gcd calculation, integer divisor search, nullspace solve, atom normalization and output formation is additional actual finite computation. Its algorithm and finite bounds in §13 terminate without any extra source samples. No polynomial bit-work estimate is asserted for those searches.

The two cyclic resource vectors have the same four Ticks, one Square and one Read, but different Adds/Holds and actual fields. Their observed coefficients on $a$ are $\epsilon^6$ and $\epsilon^2$, respectively. The second also pays pulses of size $\epsilon^{-2}$ and cancellation arithmetic. No noisy/quantized sensor contract was supplied, so these scales alone are not a simultaneous precision or conditioning advantage. In either case the source Square still performs $N$ products; later selected use in Construction 17.3 adds another $N$ products and all its other source/predictor work.

Fixed counts of rational slots do not bound their bits. The family contains parameters of unbounded rational width at fixed $b$ by (CL.5), and (CM.35) excludes a uniform inverse-conditioning claim. There is also actual lifetime growth without any extra input: on the isolated endpoint $0<y_{\rm p}=\epsilon^2a<1$ is a nonintegral reduced rational $m/n$, $n>1$. After $r$ additional Square calls without Ticks, the source leaf value is $m^{2^r}/n^{2^r}$ in lowest terms. Its denominator bit length grows as $2^r\log_2 n$. The synchronized predictor or literal native export must represent that growth too. Arbitrarily wide legal rational Adds provide a separate width cost. Thus finite code, finite per-instance termination and fixed dimension provide no bounded lifetime memory, precision, elapsed-time, energy or finite-shot theorem. $\square$

## 19. Exact suppliers and remaining common-apparatus boundaries

**Convention 19.1 (source-relative mathematical content).** The suppliers referenced by the new sections are fixed at [CMpin] and the stated pinned mathlib revision. Finite Ho–Kalman blocks, the real finite-observability criterion, minimal symmetric realization, finite function-algebra rigidity, rational-root extraction and simultaneous diagonalization are credited methods. The mathematical addition is their operational composition (CM.9)–(CM.12) from actual calibrated boundary calls, effective native-axis normalization, complete retained nonlinear use, the separately conditioned Report consumer, and the two complete cyclic-family acquisitions. This is repository-derived synthesis relative to those suppliers, not a worldwide priority claim or a new formal-certification claim.

The already public [Native Leaf Boundary Acquisition II, §§77–79][CMU45] supplies WLAB-ord unknown commissioned positive-tree law/current acquisition with an arbitrary initial field, a roster-derived order cap, free/forced response subtraction, no Reset or Square, ACK-only Tick and complete retained use, including its exact singular-history and current-boundary conditions. Its U5 supplies the $N-\operatorname{rank}M$ fresh-Read lower bound and paid attainment for a known integral adjacency's invertible contracting polynomial transfer under its complete entrance-information contract. Those conclusions are reused where their hypotheses fit; neither is reserved or reasserted as the present contribution. Here connected graphs may have cycles, the broad ports need not be true leaves, and the new native multiplication defeats the explicit whole linear-service collision of §§4–5. The earlier [native mask and fresh-only results, §§87–93][CMU123] retain their own known-unit-law/growth/entry-image and adaptive split-price contracts. They are sufficient acquisition/retention results in those contracts, without supplying this unknown weighted cyclic native frame.

On this cyclic family, §6 already earns $S$ by one actual interior Read$_e$ after two Ticks and installs a complete predictor. That is a sufficient alternative whenever its authentic interior read exists. The new leaf-only authority profile saves that port but commissions whole-field calibrated Square and extra activity. Numerical inverses do not install either right, and no total-cost ordering between these different installations is asserted.

**Boundary 19.2 (preserved consumers and absent bridges).** The native clocked recovery, paid conversion, original ordered-interface realization, Process Geometry and Structural Atlas consumers keep their exact preparations, acquired records, lawful operations, selectors, references, current rights and cost premises. Their distinct entrances are not identified with Definition 11.1. In particular [Atomic Generation Acquisition III, Boundary 16.2 and Open problem 16.3][CMCommon] still requires a common actual preparation/implementation preserving all original states and legal actions, complete outputs/refusals, pending/parsing behavior, successors, selectors, genuine references/grants, retained callable records and simultaneous resource costs. The fixed-$G_{\rm gc}$/original-$Q$, parked-consumer, unchanged-initialization, original terminal/final-no-Ready and erased-history obligations retain their exact scopes and settlements. None is solved by changing to Reset/Square or by numerical reencoding.

The current public [FIB mixed-clock §§19–20][CMMixed] concerns its strictly positive rank-one source, unknown polynomial gain/drift and countable fixed-linear gain-output contract; its critical-read exclusion does not cover this native Square class. The [coherent-reconstruction §35][CMCoherent] distinguishes a universal all-complex-input effect obstruction from a parameter-independent statistical test on its specified five-dimensional native menu; it supplies neither a Square installation nor finite-sample certain discrimination. The [original passive-pair stochastic-attainment result, §119][CMAttain] and [finite normalized diffusion sampler/consumer, §§20–23][CMDiffusion] retain their original sources, clocks, joint laws and consumers: stochastic attainment/equality of deterministic infimum and finite exact-real-input native approximation are available results, not absent capabilities. They do not provide bare-native causal acquisition of their exact-real samplers, finite-bit/shot or effective uniform-resource realization, or a joint apparatus with this rational field. No negative inference here relies on a corpus omission or a missing API name.

The four expressions have independent meanings only in the explicit acquired-image or invertible performed-Report domains above. Space means the native weighted coefficient graph/current field, not a derived physical spatial dimension; Time means a specified actual relative event window, not arbitrary history or wall duration; Boundary means the declared finite experiments/germ or the family transfer/current scalar; Memory means an earned synchronized predictor with real backing and rights. Claims outside those images require new injectivity and realization proofs. Alpha/beta remains a candidate foundation, not a proved universal minimum. A common native/path/quantum/continuous process, physical installation, robust precision and globally minimal resources remain unresolved. These bounded conditional results do not complete the sustained common internal-observer/four-expression objective.

[CMpin]: https://github.com/the-omega-institute/trureturing/tree/bc0d5339476df8b41d58d7cde040a82266a9f416
[CMHK]: https://github.com/the-omega-institute/trureturing/blob/bc0d5339476df8b41d58d7cde040a82266a9f416/D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.lean
[CMFO]: https://github.com/the-omega-institute/trureturing/blob/bc0d5339476df8b41d58d7cde040a82266a9f416/D5/S3/Observer/Linear/FiniteObservabilityEquivalence.lean
[CMHKS]: https://github.com/the-omega-institute/trureturing/blob/bc0d5339476df8b41d58d7cde040a82266a9f416/Blueprint/D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.scribe.cs
[CMFOS]: https://github.com/the-omega-institute/trureturing/blob/bc0d5339476df8b41d58d7cde040a82266a9f416/Blueprint/D5/S3/Observer/Linear/FiniteObservabilityEquivalence.scribe.cs
[CMMS]: https://github.com/the-omega-institute/trureturing/blob/bc0d5339476df8b41d58d7cde040a82266a9f416/D5/S3/Quantum/Measurements/MinimalSymmetricRealizationUniqueness.lean
[CMMSS]: https://github.com/the-omega-institute/trureturing/blob/bc0d5339476df8b41d58d7cde040a82266a9f416/Blueprint/D5/S3/Quantum/Measurements/MinimalSymmetricRealizationUniqueness.scribe.cs
[CMDiag]: https://github.com/the-omega-institute/trureturing/blob/bc0d5339476df8b41d58d7cde040a82266a9f416/D5/S3/Observer/Dynamics/DiagonalInterfaceConjugacy.lean
[CMDiagS]: https://github.com/the-omega-institute/trureturing/blob/bc0d5339476df8b41d58d7cde040a82266a9f416/Blueprint/D5/S3/Observer/Dynamics/DiagonalInterfaceConjugacy.scribe.cs
[CMTensor]: https://arxiv.org/html/1210.7559v4#A4
[CMRoots]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Polynomial/RationalRoot.lean
[CMU45]: https://github.com/the-omega-institute/trureturing/blob/bc0d5339476df8b41d58d7cde040a82266a9f416/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION_II.md
[CMU123]: https://github.com/the-omega-institute/trureturing/blob/bc0d5339476df8b41d58d7cde040a82266a9f416/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION_III.md
[CMCommon]: https://github.com/the-omega-institute/trureturing/blob/bc0d5339476df8b41d58d7cde040a82266a9f416/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_III.md
[CMMixed]: https://github.com/the-omega-institute/trureturing/blob/bc0d5339476df8b41d58d7cde040a82266a9f416/docs/develop/theory/FIB_CRITICAL_MIXED_GAIN_WORDS_AND_CLOCK_PENCIL_OBSTRUCTIONS.md
[CMCoherent]: https://github.com/the-omega-institute/trureturing/blob/bc0d5339476df8b41d58d7cde040a82266a9f416/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md
[CMAttain]: https://github.com/the-omega-institute/trureturing/blob/bc0d5339476df8b41d58d7cde040a82266a9f416/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md
[CMDiffusion]: https://github.com/the-omega-institute/trureturing/blob/bc0d5339476df8b41d58d7cde040a82266a9f416/docs/develop/theory/FIB_NATIVE_FREE_DIFFUSION_QUOTIENT_RIGIDITY.md

## 追加锚（本行以下为增补区）
