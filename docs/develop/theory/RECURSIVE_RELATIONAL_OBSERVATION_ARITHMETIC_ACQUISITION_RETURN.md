# Recursive relational observation: arithmetic acquisition and behavior return

## 1. One positive source, its ports and its entry task

**Definition 1.1 (the actual arithmetic process).** Fix an integer $H\ge2$, divisors $d_n\mid d_o\mid H$, and a finite indexed list $\mathcal A=(c_1,\ldots,c_s)$ of positive integer addends with $\gcd(H,c_1,\ldots,c_s)=d_n$. For the empty list the gcd is $H$. There is one opaque positive integer source $C$. The permitted source operations are

$$
\operatorname{Add}_i:C\longmapsto C+c_i\quad(1\le i\le s),
\qquad
\operatorname{Mul}_m:C\longmapsto mC\quad(m\in\mathbb Z_{>0}).
\tag{AQBR.1}
$$

Every finite word in these operations is legal, including the empty word. Each operation changes this same actual source. A residue is a mathematical description of its action, never a replacement source. The list entries name available positive blocks and their actual values, as in [FARG, Definition 100.1](FIBONACCI_ATOMIC_RELATION_GENERATION.md); a modularly equivalent translation is not an additional primitive. No subtraction, division of the source, reset, clone, preserved entry copy or other source handle is supplied.

There is an explicitly supplied, paid, nondestructive current port

$$
\operatorname{ReadF}(C)=F_H(C)=H/\gcd(C,H).
\tag{AQBR.2}
$$

Only a call actually made returns this value. The observer may compute $\gcd(C,H)=H/\operatorname{ReadF}(C)$ from that acquired answer. The port is an assumption of this process, not a construction from $\alpha,\beta$, a tree evaluator or a finer-summary encoder. Operations are total and expose no additional source-dependent reply, timing, size, failure or cost channel. Source service costs are charged separately in Definition 6.1 and are not extra observations.

The deterministic controller has lawful access to the source handle, the declared operation handles, the current ReadF port, finite public data, its genuinely acquired records, and writable local memory. It may run ordinary exact integer algorithms on these data, with their computation, installation, parameter handling and storage charged. During an acquisition procedure it controls the source exclusively; no unreported external operation occurs. Its program, initialization and every choice depend only on these accessible inputs. In particular, an unknown entry value cannot be built into its code or selector.

**Definition 1.2 (the supplied behavior code).** For $p^h\parallel H$, write $\nu_{p,h}(x)$ for the exponent of $p$ in $\gcd(x,p^h)$; thus the zero residue has depth $h$. For $0\le e\le h$, put $M=p^{h-e}$ and use the disjoint labels

$$
\eta_{p,h,e}(x)=
\begin{cases}
S(r,u),&r=\nu_{p,h}(x)<e,\quad u=(x/p^r)\bmod M,\\
D(z),&r\ge e,\quad z=(x/p^e)\bmod M.
\end{cases}
\tag{AQBR.3}
$$

The quotients are formed only in their indicated divisible cases. For $M=1$ the coordinate set, including its unit group, is a singleton. For $d\mid H$, let $\eta_{H,d}$ be the tuple of (AQBR.3) with $e=v_p(d)$, and abbreviate $\eta_o=\eta_{H,d_o}$ and $\eta_n=\eta_{H,d_n}$. In modular calculations $F_H$ denotes the periodic formula $H/\gcd(x,H)$ on integer representatives, including $F_H(0)=1$; this does not introduce an actual zero source.

These are the codes of [FARG, Theorems 100.2–100.6](FIBONACCI_ATOMIC_RELATION_GENERATION.md), which supply their representative independence, exact classification of all finite legal futures, positive-word realization and updates. In particular, equality of $\eta_n$ is exactly equality of every future $F_H$ under the original list $\mathcal A$ and all positive multipliers. The corresponding actual-library declaration is [`global_encoding_complete`](../../../D5/S3/Factorization/PrimePowers/GlobalAffineGcdBehavior.lean), with its [owning Scribe](../../../Blueprint/D5/S3/Factorization/PrimePowers/GlobalAffineGcdBehavior.scribe.cs). Its parameters are this $H$, this list $\mathcal A$ and these same positive sources; the local depths are the exponents of the actual gcd. [`affine_word_translation` and `affine_action_realization`](../../../D5/S3/Factorization/PrimePowers/AffineGcdBehavior.lean) supply the positive affine word correspondence. None of these declarations supplies the current port or an acquisition-and-return procedure. The results below are ordinary prose mathematics, without a new Lean certification.

**Definition 1.3 (entry knowledge and the three tasks).** At entry the controller is given a genuinely acquired value $s_o=\eta_o(C_0)$ for the actual positive entry source $C_0$. In the complete-fiber contract all its other initial accessible source information factors through $s_o$; the admitted entries are exactly

$$
E_{s_o}=\{C\ge1:\eta_o(C)=s_o\}.
\tag{AQBR.4}
$$

This initial acquisition is stipulated and has its own prior cost. It is not obtained free by the procedures below. A single controller for a supplied $s_o$ must succeed for every entry in (AQBR.4), rather than choosing a program after learning the unknown $C_0$.

Entry identification means outputting $\eta_n(C_0)$. Reached-state homing means installing an accurate current $\eta_n(C_*)$ at termination, allowing it to differ from the entry label. Acquisition-and-behavior-return requires both entry identification and

$$
\eta_n(C_*)=\eta_n(C_0),
\tag{AQBR.5}
$$

together with an installed callable current reader and updater for every finite subsequent legal word. Termination is required on every admitted entry. Return in (AQBR.5) concerns the task behavior, not equality of integers, source syntax, original records or elapsed time.

**Definition 1.4 (a genuinely narrowed alternative domain).** The archive-conditioned contract instead admits a nonempty $E\subseteq E_{s_o}$. The archived fact that $C_0\in E$ must already be genuinely obtained. All entries in this $E$ share the same accessible initial archive, code and public data. Thus no further initial accessible discriminator varies inside $E$. This is a different initial-knowledge contract from (AQBR.4).

For an effective construction a sufficient finite presentation of this domain is its exact residue support

$$
R_E=\{C\bmod H:C\in E\}\subseteq\{0,\ldots,H-1\}.
\tag{AQBR.6}
$$

An authentic supplied list or bitmap for (AQBR.6), or a terminating supplied algorithm producing it, is permitted and charged. Equivalently one may supply and charge a decoder on the actual projection image used in Theorem 2.1, with a valid domain guarantee. The existence of an abstract $E$, or of a semantic decoder, does not give an algorithm that extracts such a presentation from an arbitrary archive description. The source handle cannot be consulted while making this table. Full-fiber support in (AQBR.4) is computable by testing the public code on the $H$ residues; no archive narrowing is needed in that case.

## 2. The exact archive-conditioned acquisition-and-return boundary

**Theorem 2.1 (exact criterion on one old fiber).** Under Definitions 1.1–1.4 fix $E\subseteq E_{s_o}$ nonempty. For each $p^h\parallel H$ write

$$
e_o=v_p(d_o),\qquad e=v_p(d_n),\qquad
r_p=\nu_{p,h}(C)\quad(C\in E_{s_o}).
$$

The old code determines $r_p$, so it is constant on this entire old fiber. Partition the prime axes into

$$
B=\{p:r_p<e\},\qquad G=\{p:r_p\ge e\},\qquad
J=\prod_{p\in G}p^{h_p},\qquad
\pi(C)=(C\bmod p^{h_p})_{p\in G}.
\tag{AQBR.7}
$$

The empty projection has one value and $J=1$. By CRT, $\pi$ can equally be represented by $C\bmod J$.

There exists a deterministic acquisition-and-behavior-return controller on all entries of $E$ if and only if

$$
\boxed{\quad
\forall C,D\in E,\quad
\pi(C)=\pi(D)\ \Longrightarrow\ \eta_n(C)=\eta_n(D).
\quad}
\tag{AQBR.8}
$$

Here existence allows a fixed finite presentation appropriate to $E$, shared by all its alternatives. With the effective presentation of Definition 1.4, sufficiency is constructive and returns the stronger endpoint $C_*\equiv C_0\pmod H$ using only original positive additions and actual current reads. No effective claim is made from an unpresented semantic archive.

**Proof (the irreversible local constraint).** Fix $p\in B$ and an entry with depth $r=r_p<e$. Every allowed addend is divisible by $p^e$. At any current depth $t<e$, an addition leaves depth $t$ unchanged. A positive multiplication changes that depth to $\min(h,t+v_p(m))$. Once depth is at least $e$, every subsequent allowed operation leaves it at least $e$. Consequently depth can never fall back to $r$ after any multiplier divisible by $p$ has occurred. Since $\eta_n$ exposes this depth, a run satisfying (AQBR.5) cannot use a multiplier divisible by $p$ at any prefix. On every successful run, every multiplier is therefore a unit on every axis in $B$, and every current depth on these axes stays $r_p$.

This statement holds for the actual positive integers, including a multiplication that saturates the truncated depth. It does not assume that the rest of the state is invertible. Positivity and divisibility of the available addends are what prevent undoing the lost depth.

**Proof (necessity).** Let $C,D\in E$ have the same projection (AQBR.7). Run a claimed controller on these two fixed entries, with their identical accessible initialization. Induct through its local computations, operations and reads. Identical records and public inputs give identical choices. On $G$ the two current residues remain equal after every common operation. On $B$ a successful run can use only the prime-unit multipliers just proved necessary, so both current depths remain the same fixed $r_p$. Hence their complete current gcds, and therefore their entire ReadF answers, are equal at every call. Local records, choices and stopping decisions remain identical. Termination on one entry gives termination with the same output on the other. Correct entry identification forces $\eta_n(C)=\eta_n(D)$, which is (AQBR.8).

This induction also covers a strategy with an unbounded a priori number of calls, arbitrary local computation, and adaptive stopping: the successful finite history for either fixed entry is the same for the other. It never selects a new source between calls.

**Proof (sufficiency and the decoder).** Condition (AQBR.8) defines one value

$$
\Delta_E(z)=\eta_n(C)\quad\text{for any }C\in E\text{ with }\pi(C)=z
\tag{AQBR.9}
$$

on $\pi(E)$. To install it from (AQBR.6), enumerate that finite support, compute each public $\pi(x)$ and $\eta_n(x)$, and group equal projection keys. Condition (AQBR.8) is exactly agreement of the labels in each group. Store one representative residue per group and compute its label when called. This table has at most $H$ rows and is shared across all entries of $E$; it is not a table indexed by an inaccessible unknown-source label.

The actual procedure of Theorem 3.1 acquires $\pi(C_0)$ and returns the actual source modulo $H$. Applying (AQBR.9) gives the entry label and the same current label. The update installation of Theorem 5.1 gives continued use. These steps prove sufficiency. If only semantic $E$ is given, its residue support is still a finite set, so the argument proves finite nonuniform existence; producing that set from an arbitrary description is the separate presentation obligation of Definition 1.4. $\square$

## 3. Acquiring the observable residues without a reset

**Theorem 3.1 (original-addend sweep and modular return).** Put $d=d_n$ and $L=H/d$. There is a public finite word $W_d$ of original additions only whose actual integer increment is $S$ and whose length $\ell$ satisfies

$$
S\equiv d\pmod H,\qquad 1\le\ell\le L-1\quad(L>1).
\tag{AQBR.10}
$$

For $L=1$ use the empty word, $S=\ell=0$. On any admitted entry, the following single-source procedure acquires every coordinate in $\pi(C_0)$ and returns modulo $H$:

1. At each $t=0,\ldots,L-1$, call current ReadF once at the actual source $C_0+tS$ and retain its answer $a_t$.
2. After each of these calls, including the last, execute $W_d$ once on that source.
3. For every $p\in G$ with $e<h$, choose any acquired index $t_p$ for which $v_p(H/a_{t_p})=h$, and set $x_p=(-t_p d)\bmod p^h$. For $p\in G$ with $e=h$, set $x_p=0$.

All required indices exist, $x_p=C_0\bmod p^h$, and the endpoint is the actual integer

$$
C_*=C_0+LS\equiv C_0\pmod H.
\tag{AQBR.11}
$$

The procedure uses exactly $L$ paid reads, $L\ell$ original additions, and no source multiplications. When (AQBR.8) holds, these counts give upper bounds for attaining acquisition-and-return, not minima for reads or work; redundant reads and additions can be omitted in contracts where the initial data already determine the target.

**Proof (the finite original word).** Each $c_i$ is divisible by $d$. On the $L$-element cyclic group use the public directed edges

$$
z\longmapsto z+c_i/d\pmod L.
$$

Their nonnegative-word reachability from zero is the whole group. Indeed, in a finite group the inverse of any generator is a nonnegative number of repetitions of that generator. The generated subgroup is the whole group because $\gcd(L,c_1/d,\ldots,c_s/d)=1$. This is the finite positive translation argument of FARG100.2, applied to the actual normalized list. Breadth-first search from zero, stopping at residue one, supplies a path without repeated vertices, hence at most $L-1$ edges. Each edge is one indexed original addition. Its unnormalized sum is $S\equiv d\pmod H$, proving (AQBR.10). This search uses only public integers; it is not a query to $C_0$. For $L=1$ no search or edge is required, including when the library is empty.

**Proof (the actual read positions).** Addition of the same word $W_d$ increments the integer by exactly $S$. Induction in $t$ gives the claimed actual positions $C_0+tS$, not independently reset counterfactual positions. For $L>1$ the last extra execution is necessary for residue return: a procedure stopping at the last read has only made $L-1$ executions, and $d$ has additive order $L$ modulo $H$. Because $LS\equiv Ld=H\equiv0\pmod H$, the final execution closes the residue return. For $L=1$ both the word and the increment are empty.

**Proof (the acquired coordinates).** Fix $p\in G$ with $e<h$. Then $p^e\mid C_0$, $p^e\mid S$, and

$$
S/p^e\equiv d/p^e\pmod{p^{h-e}},
$$

which is a unit modulo $p^{h-e}$. Thus exactly one residue class $t\bmod p^{h-e}$ satisfies $C_0+tS\equiv0\pmod{p^h}$. The interval $0\le t<L$ contains this class, since $p^{h-e}\mid L$. Its actual ReadF answer has full depth $h$ on this axis, so such a $t_p$ is genuinely acquired. Every such index gives

$$
C_0\equiv-t_p S\equiv-t_p d\pmod{p^h}.
$$

For $e=h$ the hypothesis $r_p\ge e$ already says $C_0\equiv0\pmod{p^h}$; there is no modular inverse or additional coordinate to acquire. All coordinates come from the same read tape. CRT on the selected axes gives the actual $\pi(C_0)$, not a combination of independent optimizing sources. On $B$ every read has its fixed depth $r_p$, consistent with the obstruction in Theorem 2.1. $\square$

## 4. Complete old fibers and all-positive-source degeneracies

**Theorem 4.1 (exact complete-fiber test).** Retain Theorem 2.1 but take the complete fiber $E=E_{s_o}$. For $p^h\parallel H$ set

$$
m_p=\frac{\varphi(p^{h-e})}{\varphi(p^{h-e_o})},\qquad\varphi(1)=1.
\tag{AQBR.12}
$$

Then acquisition-and-behavior-return on this old fiber exists exactly when

$$
\boxed{\quad\text{for every }p\mid H\text{ with }r_p<e,\quad m_p=1.\quad}
\tag{AQBR.13}
$$

In particular, this is a criterion for an entry $C_0$ under its complete initial information fiber, not an assertion that a program chosen specifically for the unknown integer may hard-code its answer.

**Proof.** The local refinements and counts are supplied by [FARG, Sections 102.2–102.4](FIBONACCI_ATOMIC_RELATION_GENERATION.md). Here the relevant local fiber is the one with $r_p<e\le e_o$. Its old label is a low label at depth $r_p$.

If $e_o<h$, an old unit modulo $p^{h-e_o}$ has exactly $p^{e_o-e}$ unit lifts modulo $p^{h-e}$; this equals (AQBR.12). If $e_o=h$, the old unit modulus is one, and the number of possible new units is $\varphi(p^{h-e})$, again (AQBR.12). Every lift has a representative of exact depth $r_p$ and gives a distinct new low label. These arguments include $e=e_o$ and the singleton modulus-one unit class.

If all the indicated $m_p$ equal one, the old label determines the new label on every axis in $B$. The projection fixes full residues on $G$, so it fixes their new labels as well. This proves (AQBR.8).

Conversely, if $m_p>1$ for some $p\in B$, choose two of those local unit lifts with distinct new labels. Hold every other axis at one fixed representative of its old label, including all the full residues in $G$. CRT gives two residues modulo $H$ satisfying these simultaneous choices. Each has a positive integer representative, using $H$ for a zero residue if necessary. They lie in the same complete old fiber, have identical $\pi$, and have different $\eta_n$. Thus (AQBR.8) fails. This proves the exact equivalence rather than replacing it by the stronger sufficient condition $B=\varnothing$. $\square$

**Theorem 4.2 (one controller for every positive entry).** There is an acquisition-and-behavior-return controller for every $C_0\ge1$, receiving its acquired $\eta_o(C_0)$, if and only if on every prime axis

$$
\boxed{\quad e=0\quad\text{or}\quad e=e_o\quad\text{or}\quad
(p=2,\ e_o=h,\ e=h-1).\quad}
\tag{AQBR.14}
$$

**Proof.** The unit old fiber has $r_p=0$ on every axis, realized by the same source $1$. Whenever $e>0$, Theorem 4.1 therefore requires $m_p=1$. If $e_o<h$, (AQBR.12) is $p^{e_o-e}$, equal to one exactly when $e=e_o$. If $e_o=h$, it is $\varphi(p^{h-e})$, equal to one exactly when $h-e=0$, or when $p=2$ and $h-e=1$. These are precisely the alternatives in (AQBR.14), together with $e=0$, which has no low axes to obstruct return. A violating axis supplies the CRT witness in the proof of Theorem 4.1 on the old unit fiber, giving necessity.

Under (AQBR.14), every old fiber satisfies (AQBR.13). There are finitely many old labels, all computable on residues. A single public procedure takes the received label, constructs its full-fiber table, and runs Theorem 3.1 followed by Theorem 5.1. This gives sufficiency on all positive entries with a common finite algorithm. $\square$

**Proposition 4.3 (endpoints and a strict conditional example).** The tests include all of the following cases.

(a) If $d_n=d_o$, the old code already determines the new code on every entry; installing its known update program requires no new source operation or read. If $d_n=1$, every axis is in $G$, and the sweep acquires full residues modulo $H$. If the new library is empty, $d_n=d_o=H$, so the first case applies. The same zero-read shortcut applies when a nonempty library has all addends divisible by $H$.

(b) The saturated $2$-axis exception in (AQBR.14) is genuine. For $H=8,d_o=8,d_n=4$, the low new unit modulus is $2$ and has one unit; return is possible on every entry even though some entry depths are below the new translation depth. For $H=2$ all divisor pairs satisfy (AQBR.14). No inverse modulo one is required in any of these cases.

(c) For $H=8,d_o=8,d_n=2$ and actual library $\{2\}$, every odd entry has $r_2=0<e=1$ and $m_2=\varphi(4)/\varphi(1)=2$. Acquisition-and-return on the complete odd fiber is impossible. In contrast, on its genuinely known subdomain $E=\{C\ge1:C\equiv1\pmod4\}$ the new label is constant, so it is possible without a new read. Treating that narrower archive as free would change the initial contract.

(d) A narrower domain need not have a constant new label. Take $H=72,d_o=72,d_n=2$, actual library $\{2\}$, and

$$
E=\{C\ge1:C\equiv1\text{ or }11\pmod{72}\}.
\tag{AQBR.15}
$$

Both alternatives have the same old code, but different new labels. Only the $3$-axis is in $G$; it has full modulus $9$. Its entry residues $1$ and $2$ distinguish the two alternatives. Thus (AQBR.8) holds and the sweep with the genuine domain table acquires the differing $2$-axis label indirectly while returning modulo $72$. On the complete old fiber that return task is impossible.

**Proof.** For (a) use the definitions and $d_n\mid d_o\mid H$; the updater is the supplied FARG100.5 updater. For (b), $\varphi(2)=1$, and at a modulus-one coordinate there is only one label. For (c), an old odd label for $d_o=H$ records only depth zero; the new low coordinate is $C\bmod4$. Theorem 4.1 and then (AQBR.8) give the two assertions.

For (d), $72=2^3 3^2$. Since $d_o=H$, the old labels on both axes are depth zero. The new $2$-axis has $e=1$ and $r_2=0$, while the new $3$-axis has $e=0$, so $G$ is exactly the $3$-axis. Its two full projection residues are $1$ and $2$ modulo $9$. The new $2$-axis units are $1$ and $3$ modulo $4$. Thus the old label is shared, the new labels differ, and the projection separates them, proving (AQBR.8). The complete old unit fiber fails (AQBR.13) on the $2$-axis. $\square$

## 5. Successive acquired cuts and installed current use

**Theorem 5.1 (a returned label is a callable current state).** Suppose Theorem 2.1 succeeds, and retain its acquired output as an immutable entry label $b_{\rm entry}=\eta_n(C_0)$. Install a separate current register $b=\eta_n(C_*)$ with the supplied FARG100.5 updates. Then, for every finite subsequent legal word $w$, processing the actual source operations and the same supplied parameters in this updater gives

$$
b_w=\eta_n(w(C_*)),\qquad
\operatorname{Out}(b_w)=F_H(w(C_*)).
\tag{AQBR.16}
$$

Thus, using $b$ and public operation inputs, the controller may output the current task value without another source read. Both the current reader and the finite-word predictor are actual installed algorithms. A prediction for an unexecuted word is not an acquired observation of that word's effects.

**Proof.** Here are the exact local interfaces being installed. On an axis with new threshold $e$, modulus $M=p^{h-e}$, and $\nu_{p,h-e}(0)=h-e$, the reader is

$$
S(r,u)\mapsto r,\qquad D(z)\mapsto e+\nu_{p,h-e}(z).
\tag{AQBR.17}
$$

These exponents give the current gcd and then $F_H$. For the actual input $c_i=p^e\delta_i$, use

$$
D(z)\mapsto D(z+\delta_i),\qquad
S(r,u)\mapsto S(r,u+p^{e-r}\delta_i).
\tag{AQBR.18}
$$

For the actual positive input $m=p^av$, $p\nmid v$, use

$$
\begin{aligned}
D(z)&\mapsto D(mz),\\
S(r,u)&\mapsto
\begin{cases}
S(r+a,vu),&r+a<e,\\
D(p^{r+a-e}vu),&r+a\ge e.
\end{cases}
\end{aligned}
\tag{AQBR.19}
$$

Coordinates are reduced modulo $M$. As proved in FARG100.5, these are well defined and agree with the actual arithmetic, including saturation, $e=0$, $e=h$, and a scalar whose residue is zero. It is sufficient to handle the scalar's residue modulo $H$ in local computation, using positive representative $H$ for zero; reading and delivering the original parameter $m$ to the source is still charged. All library additions have the required divisibility by $p^e$.

At installation, (AQBR.11), (AQBR.9) and representative independence give $b=\eta_n(C_*)$. Each next actual operation and its local update commute by these supplied formulas. Induction on the word gives (AQBR.16). This is the concrete infinite-positive-source correspondence of FARG100 and `global_encoding_complete`, rather than an application of a finite-source universality theorem to an unproved infinite domain. The finite-carrier [`controlled_behavior_universal_property`](../../../D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean) supplies the general factorization perspective, not the acquisition or this domain bridge. $\square$

**Theorem 5.2 (what the actual successive read cuts certify).** Use Theorem 3.1 and retain the read tape. Just after the $j$th read, $1\le j\le L$, and before the following macro, the exact compatible entry residue set is

$$
K_j=\{x\in R_E:F_H(x+t d)=a_t\text{ for all }0\le t<j\}.
\tag{AQBR.20}
$$

It contains $C_0\bmod H$ and satisfies $K_{j+1}\subseteq K_j$. With only the retained initial data and these actual records, entry $\eta_n$ is identifiable at this cut exactly when $\eta_n(K_j)$ is a singleton. The exact possible current labels are

$$
\{\eta_n(x+(j-1)d):x\in K_j\}.
\tag{AQBR.21}
$$

At $j=L$, the projection $\pi$ is constant on $K_L$. Under (AQBR.8), the entry label is consequently a singleton; after the final macro the current label equals it. Earlier cuts need not have earned the final label or behavior return.

**Proof.** Each acquired answer is exactly the test displayed in (AQBR.20), since $S\equiv d\pmod H$. An entry in $E$ survives precisely when all its deterministic actual read replies match this prefix. Every residue in (AQBR.20) has an entry representative in $E$ and that representative realizes the entire observed prefix under the predetermined scan. Thus this set is exact, not merely an overapproximation. Appending the next equality gives inclusion. A singleton target image defines one output on this record; if two target values remain, two actual entries give identical records and different required outputs, ruling out a decoder on those inputs. The actual source after $j-1$ macro executions has precisely the residues in (AQBR.21).

For any $p\in G$ with $e<h$, the full tape contains a saturated index. Every surviving residue has to share that saturation, so its $p$-residue is $-t_p d$. Axes with $e=h$ are already fixed at zero. This proves constancy of $\pi$ on $K_L$, and (AQBR.8) gives the final assertion. No unqueried depth or resetting test has been used. $\square$

**Theorem 5.3 (actual staged refinements with intervening use).** Fix any finite chain

$$
d_0\mid H,\qquad d_{j+1}\mid d_j\quad(0\le j<q),
\tag{AQBR.22}
$$

with actual finite addition lists $\mathcal A_j$ of gcd parameter $d_j$ and all positive scalar multiplications. At stage $j$ only its declared current list is used; divisibility of parameters alone does not grant a primitive from another list. Assume the stage-zero current $\eta_{H,d_0}$ is genuinely acquired. At each next upgrade, let $E_j$ be the exact current alternative domain determined by the shared acquired archive, so that $\eta_{H,d_j}$ is constant on $E_j$ and its residue support is effectively presented. If (AQBR.8) holds for the pair $(d_j,d_{j+1})$ on this $E_j$, a fresh sweep using $\mathcal A_{j+1}$ acquires the finer entry label, returns modulo $H$ at that stage, and installs its current updater. This can be repeated through every such successful stage, with ordinary intervening legal operations on the same source.

**Proof.** Apply Theorems 2.1, 3.1 and 5.1 at the actual current entry of the next stage. Its final alternative residue support is $K_L$, because the final translation is zero modulo $H$. If a common recorded intervening word $w$ is then executed, the next current support is exactly

$$
\{w(x)\bmod H:x\in K_L\}.
\tag{AQBR.23}
$$

Every member is realized by a surviving actual entry, and every surviving entry maps into it. The installed updater computes the same next current coarse label from the acquired fine label and the known word, so that label is constant on (AQBR.23). Future adaptive choices cause no difficulty when their inputs are the shared installed state, supplied public inputs and acquired records: these are the same on every surviving alternative. If further paid replies are acquired, intersect with their actual reply constraints before taking the next image. These finite-support operations are effective and charged. Induction proves the assertion for any finite number of stages.

An old tape certifies its own entry and the operations actually performed since it; it is not a new read of the later source. A historical $\eta_{H,d_j}$ is not generally the later current label, and it does not alone justify a finer future upgrade. Each upgrade uses its new current support and the exact new criterion. If an unreported operation or a selector with additional private source input intervenes, this archive/update proof does not apply. The result supplies neither independent optimal supplements nor an optimal acquisition schedule. $\square$

## 6. Same-run resources and finite presentation

**Definition 6.1 (the separate resource coordinates).** Count a call to ReadF, an indexed original addition and a positive scalar multiplication separately. Also charge public setup computation, installed code/data, local bit computation, record writes, local workspace, operation-parameter input, source arithmetic/service work and source storage. For a source implementation with declared service prices $\rho_H(C)$ for the paid read and $\tau_i(C)$ for $\operatorname{Add}_i$, the sweep's exact source-service account is

$$
\sum_{t=0}^{L-1}\rho_H(C_0+tS)
+\sum_{t=0}^{L-1}\sum_{k=1}^{\ell}
\tau_{i_k}\!\left(C_0+tS+\sum_{v<k}c_{i_v}\right),
\qquad W_d=(i_1,\ldots,i_\ell).
\tag{AQBR.24}
$$

The call and primitive counts are not a claim that these services cost one bit operation. The port's implementation and price remain declared inputs. Production and installation of actual operation blocks, references and port hardware or service are separately supplied and charged; a list of their numeric values does not construct them. Indexed-call emission uses their installed handles. Service prices include the backend's actual parameter lookup/delivery and source arithmetic. In a binary integer implementation, source additions also pay for the actual operand lengths. No uniform bit bound independent of the unknown $C_0$ is asserted.

**Theorem 6.2 (one explicit finite local implementation and conservative bounds).** Suppose the support table (AQBR.6) is supplied as a finite list or bitmap. Let $b=\lceil\log_2(H+1)\rceil$, $\lambda=\lceil\log_2(s+2)\rceil$, $B_{\mathcal A}$ be the total binary length of the actual library values and delimiters, and $D_E$ the bit length of the supplied domain presentation. A deterministic binary implementation of the constructions above has finite public setup bounded by

$$
O\!\left(B_{\mathcal A}^{\,2}+D_E+H^2b^4+sL^2(b+\lambda)^2\right)
\tag{AQBR.25}
$$

bit operations. It can use installed data and peak local workspace bounded by

$$
O\!\left(B_{\mathcal A}+D_E+(H+L)(b+\lambda)+b^2\right)
\tag{AQBR.26}
$$

bits, including the complete sweep reply tape, the macro, its phase and the decoder table. Beyond setup, local sweep processing and output installation can be bounded by

$$
O\!\left((L+H)b^4+L\ell(b+\lambda)\right).
\tag{AQBR.27}
$$

These bounds exclude the separately charged source services (AQBR.24), the prior genuine acquisition of $s_o$, and production/authentication/delivery of the archive. If an algorithm produces the support table, add its actual setup work and storage to these bounds. They are conservative attainable upper bounds, without any cost-optimality claim.

**Proof.** Trial division factors the public $H$ using at most $H$ trial divisions on $O(b)$-bit integers. The depths, powers, code tests and projection keys on a residue can be computed using $O(b)$ such divisions and multiplications; allowing $O(b^4)$ bit work per residue covers these steps, coordinate encoding and CRT by ordinary school arithmetic. Reduce the supplied $c_i$ and form $c_i/d\bmod L$ by binary arithmetic, within the first term of (AQBR.25). Breadth-first search explores at most $L$ vertices and $sL$ edges. Store a predecessor and original-generator index for each reached vertex. Residues, comparisons, queue entries and indices use $O(b+\lambda)$ bits. Even sequentially scanning the at most $L$ stored vertex records for each edge and predecessor lookup is covered by the last term in (AQBR.25); no unit-cost random access or wide arithmetic is required. Following the predecessor chain gives the macro of length $\ell\le L-1$.

For the decoder enumerate at most $H$ supported residues. The pair of a projection key and one representative residue uses $O(b)$ bits: CRT encodes the selected full coordinates by one residue modulo $J\mid H$. Sequentially compare all pairs if necessary to check that equal keys have equal fine labels; this needs at most $H^2$ code comparisons and is covered by $H^2b^4$. Store just a key and representative per group. Labels may be calculated from their representative when called; inaccessible source coordinates are never read. Full old fibers can be generated by the same enumeration and public old-code tests.

During the sweep store the $L$ acquired answers, each at most $H$, their position and the macro phase. The index determines all completed source actions; the public word and phase determine each next original addend. Parse each answer, divide $H$ by it and extract truncated prime depths with the stated elementary arithmetic. One can find saturated indices by scanning the stored tape on each axis, then decode the projection, find its finite table row and compute the output code. The prime count is at most $b$, so (AQBR.27) covers the resulting divisions, table search, CRT, and label calculation. Emitting each macro index and maintaining its counters costs $O(b+\lambda)$ local bit work per primitive. Storing a fine-label tuple requires at most $O(b^2)$ bits with a simple tagged-coordinate encoding. This proves (AQBR.25)–(AQBR.27).

For $L>1$, $S>0$ and $S\le\ell\max_i c_i$, so the source at termination has value at most $C_0+L\ell\max_i c_i$. This is a bound in terms of the actual entry size, not a bound on it. For $L=1$ the source is unchanged and the zero-read shortcut in Proposition 4.3 is available. If a full raw source-operation log rather than the word/phase representation is required, add its actual $L\ell\lambda$ bits and write work; it is not included as a free duplicate archive. $\square$

**Proposition 6.3 (continued-use and staged costs).** For a supplied subsequent word, each occurrence of an original source operation is still paid as such. The installed updater requires no additional ReadF calls. It can process a scalar parameter of binary length $B_m$ by reading all its bits and reducing it modulo $H$, with $O(B_mb^2+b^4)$ conservative local bit work. Each indexed addition update and current output can be computed in $O(b^4+\lambda)$ local bit work. Parameter delivery to the actual source, its arithmetic, and retention of the parameter or historical word are additional accounts.

For the staged procedure of Theorem 5.3 the acquisition counts are, for its actual successful stages,

$$
\sum_j L_j\text{ paid reads},\qquad
\sum_j L_j\ell_j\text{ original additions},\qquad
0\text{ acquisition multiplications}.
\tag{AQBR.28}
$$

Add the actual intervening source operations, their inputs, all local setup/update work and retained archives. No bound uniform in the number of stages, future word length or scalar input lengths follows from the finite public controller.

**Proof.** Binary streaming modular reduction reads the entire supplied scalar. Use its residue in (AQBR.17)–(AQBR.19); extracting the necessary truncated factors and reducing the finite coordinates is bounded by the same school-arithmetic estimates as Theorem 6.2. The addition and output formulas use only known parameters and the acquired current label. Summing the actual counts from Theorem 3.1 over the finite stages gives (AQBR.28); no stage starts with a reset or another source. Historical tapes and arbitrarily many actual input parameters can grow without bound even though each fixed-$H$ procedure has finite code and bounded residue counters.

The return construction requires no new source generator: it uses original additions and the declared paid port, while the scalar operations remain available for subsequent tasks. If $\eta_n$ is nonconstant on a shared-initialization $E$, at least one paid source read is necessary for entry identification in this interface. Without a read, every local computation and choice has the same accessible input on all entries of $E$, so its terminating output is constant. This proves that the nonconstant acquisition cannot be charged as mere public setup; it does not make the sweep's larger read or work bound optimal. $\square$

## 7. Entry identification, homing and literal integer return

**Theorem 7.1 (entry identification without return is always attainable).** For every old label and every entry in its complete fiber, the entry label $\eta_n(C_0)$ can be acquired from the same source without reset if (AQBR.5) is dropped. Moreover an accurate reached-state current label can be installed. One construction uses at most one positive multiplication, $L$ paid reads and $L\ell$ original additions, with the same finite setup and additional local arithmetic charged.

**Proof.** Compute from the acquired old depths the public positive multiplier

$$
M_0=\prod_{p\in B}p^{e_p-r_p}.
\tag{AQBR.29}
$$

Execute it once, omitting the operation if $M_0=1$. The actual new source is $Y=M_0C_0$. Its old code is obtained by the supplied scalar update from the genuinely acquired entry code. Every axis now has depth at least its new $e_p$, so Theorem 3.1 applied to $Y$ acquires the full residue $Y\bmod H$ and ends at $Y+LS$. For $p\in G$, $M_0$ is a unit modulo $p^h$, so this acquired residue gives $C_0\bmod p^h$ by multiplying by its public inverse.

For $p\in B$, write $M_0=p^{e-r_p}v$ with $p\nmid v$. Since $C_0=p^{r_p}u$, the acquired quotient residue satisfies

$$
(Y/p^e)\bmod p^{h-e}=vu\bmod p^{h-e}.
\tag{AQBR.30}
$$

Its public unit inverse gives exactly the old entry's new unit coordinate $u\bmod p^{h-e}$. At modulus one there is only the unique coordinate and no inverse computation is needed. Together with the genuinely known depths this recovers every entry label. The full acquired reached-state residue independently installs its current code and updater. When $B\ne\varnothing$, the multiplied source has raised depths on those axes; the procedure does not satisfy behavior return there. The impossibility in Theorem 4.1 therefore excludes neither this identification procedure nor reached-state homing. $\square$

**Proposition 7.2 (homing alone and exact integer return).** Reached-state homing alone is possible on all positive sources with one multiplication by $H$ and zero reads: the reached residue is zero modulo $H$, whose current label is known. This is a change of the same source, not a reset to a known integer.

In contrast, under the one-old-fiber contract, entry identification together with literal equality $C_*=C_0$ on every entry of $E$ is possible exactly when $\eta_n$ is constant on $E$, with the constant effectively supplied or obtained from the presented support table. No strict positive source operation is then needed.

**Proof.** The first assertion follows from $HC\equiv0\pmod H$ and the supplied updater. For the second, every addition strictly increases a positive integer and every multiplication by $m>1$ strictly increases it. All subsequent legal operations are nondecreasing. Thus any literally returning run uses only reads, local computation and multiplications by one. Its ReadF answer is fixed by the common old label. All entries of $E$ consequently give identical accessible histories and outputs, so their required entry labels must be equal. Conversely a constant label from the authentic presentation can be installed with no source change. This exact-integer assertion is stronger than behavior return, and it does not claim recovery of any earlier raw history. $\square$

**Proposition 7.3 (a one-source separating example).** In the impossible odd-fiber case $H=8,d_o=8,d_n=2,\mathcal A=\{2\}$, multiplication by $2$ followed by the sweep identifies the entry unit $C_0\bmod4$ and installs the reached current state, yet no procedure identifies that unit and returns to its entry $\eta_n$ on the complete odd fiber. For $H=8,d_o=8,d_n=1,\mathcal A=\{1\}$, eight current reads and eight additions by one return the original residue and identify it, though they increase the integer by eight.

**Proof.** In the first case the multiplier sends $C_0$ to $2C_0$; acquired $2C_0\bmod8$ determines $C_0\bmod4$ by exact division of that residue by two. The resulting source has positive $2$-depth and cannot return to odd depth, while Theorem 4.1 excludes every other universally successful return controller. In the second case $L=8,W_d=\operatorname{Add}_1$, and a saturated ReadF answer occurs exactly at the offset $-C_0\bmod8$. The final eighth addition closes the residue cycle as in Theorem 3.1. $\square$

## 8. Common-process correspondence and the remaining recovery boundaries

**Definition 8.1 (the four process fields in this arithmetic model).** A complete actual configuration includes the positive current source, its one stable handle, the public modulus and operation list, the genuinely acquired old record, any genuine archive presentation, the program/phase and lawful access, and the actual paid reply tape and installed current register. Its histories are the ones generated from these initial data by (AQBR.1)–(AQBR.2), rather than a free product of possible marginal fields.

The spatial field here is the labeled finite residue incidence of that actual source under available translations, including its prime-axis projections. It specifies which translation positions coincide modulo $H$, independently of how long a word took. The temporal field is the ordered original action/read word and its separately accumulated service costs. The boundary field is the response to every finite legal continuation of the current source, classified by $\eta_n$. The memory field is the actual acquired read tape together with its old record, public decoding data and installed mutable current code. These meanings do not define the views as copies of one unrestricted history, and no physical interpretation of residue axes or operation counts is assumed.

This use of a common process and full access/selector conditions follows [Process Geometry, Definitions 19.1 and 19.6 and Theorem 19.7](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md). Its Sections 32–33 distinguish a task behavior kernel from endpoint incidence and cumulative path grades. Its Section 44 separately supplies and charges current numeric ports on a native tree; those are not the integer operations or ReadF assumption of Definition 1.1.

**Proposition 8.2 (the proved recovery routes and their limits).** In this process the newly acquired boundary-memory route is exactly Theorem 2.1: on a genuinely presented one-old-fiber domain the earned tape and public data recover the entry boundary with behavior return precisely under (AQBR.8). The direct route from the tape through its projection and decoder agrees with the output and installed-state route, and every subsequent current route commutes with the actual arithmetic as in (AQBR.16). In the complete-fiber contract this is exactly (AQBR.13), not an assumption of finer encoder access.

Neither the acquired boundary nor even a full current residue recovers the exact positive source, its literal history or cumulative original-operation count. For fixed public data, $C$ and $C+H$ are different positive sources with the same residue and all the same future task outputs. A closed positive sweep, or an extra multiplication by one, changes the temporal record without changing the residue endpoint or boundary. For any separately supplied time or cost grade the same witness obstructs recovery if the inserted word has nonzero grade; a grade identically zero is trivially recoverable. Thus these fields do not have unconditional mutual inverses in this model.

**Proof.** The first route agreement is (AQBR.9) applied to the saturation coordinates actually obtained in Theorem 3.1; Theorem 5.1 starts from that same value and proves every finite-word commuting equation. The two sources in the second assertion remain congruent after every common legal operation by (AQBR.1), and so have equal task outputs. The closed sweep satisfies (AQBR.11), while multiplication by one is a legal extra event preserving the integer itself and increasing the original-operation count by one. Their temporal records differ; any nonzero inserted additive grade differs as well. These are actual positive-source witnesses to the missing inverse directions. $\square$

**Definition 8.3 (supplier and literature scope).** The acquisition-and-return criterion (AQBR.8), its local arithmetic specialization (AQBR.13), the uniform criterion (AQBR.14), and their one-source attainment are `repo-derived` mathematics proved here. They use the known finite-group, valuation and CRT arguments within this specific source/access contract. FARG100 supplies the behavior classification, original-word closure and current updates. FARG102 supplies static refinement fiber counts and explicitly distinguishes those counts from source-free acquisition and online streams; no minimum-independent-supplement theorem is asserted here.

[FARG127.7](FIBONACCI_ATOMIC_RELATION_GENERATION.md) has a single progressing substitution copy only under its separately supplied nondestructive current port. It reproduces its increasing selected times, without returning the entry behavior. [FARG133.3–133.6](FIBONACCI_ATOMIC_RELATION_GENERATION.md) obtains scalar digits and a joint-query formula under its stated same-entry reset contract; its query minima are not minima for this no-reset arithmetic task. The scalar identification in Theorem 7.1 does not import those resets. [Nonlinear Recut Memory, Proposition 3.2](RECURSIVE_RELATIONAL_OBSERVATION_NONLINEAR_RECUT_MEMORY.md) and its rollback suppliers characterize recovery from actually retained records; they do not acquire a missing source label. These supplier boundaries remain in their original domains.

The following primary-source distinctions are `literature-attested`: Petra van den Bos and Frits Vaandrager, [*State Identification for Labeled Transition Systems with Inputs and Outputs*, arXiv:1907.11034v2, Section 1](https://arxiv.org/html/1907.11034v2), pose identification of the initialized state by inputs and observed outputs; Markus Theo Frohme, [*Active Automata Learning with Adaptive Distinguishing Sequences*, arXiv:1902.01139v1, Sections 6 and 8.1](https://arxiv.org/html/1902.01139v1), separates symbol queries from reset queries in its learning interface; Natalia Kushik and Nina Yevtushenko, [*Adaptive Homing is in P*, arXiv:1504.02444v1, Section 2](https://arxiv.org/html/1504.02444v1), define a homing test by uniqueness of the reached successor under each surviving trace. Those sources supply the identification/homing/reset distinctions, not (AQBR.8) or an arithmetic return theorem. Their finite-machine algorithmic statements do not imply complexity bounds for the unbounded positive source and services here. No worldwide originality claim is made.

The full four-expression problem still requires the missing inverse directions for independently meaningful views on its intended original processes, and a construction of whatever access ports are claimed there. Nothing here derives ReadF or old-boundary acquisition from $\alpha,\beta$, reconstructs original tree order or brackets, supplies an unknown-source Native/LAB reader, changes a fixed original task or initialization, or proves a universal reduction to this arithmetic apparatus. A finite acquisition-and-return theorem on this explicit interface does not complete that sustained problem.

## 追加锚（本行以下为增补区）

## 9. Direct continuous pair acquisition by parity and two graft scans

**Definition 9.1 (a distinct two-coordinate current-port apparatus).** Fix a public integer $H\ge1$. There is one opaque, exclusively controlled actual source $u\in\mathbb N^2$, initially $v_0=(a,b)$, with zero coordinates and $(0,0)$ admitted. Vectors are columns. The only source updates are the original Fibonacci replacement and alpha graft

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
\alpha=\binom10,\qquad q=(2,3),\qquad
R(u)=Mu,\qquad G(u)=u+\alpha.
\tag{AQBRP.1}
$$

Every occurrence acts forward on this very integer pair. It returns a fixed acknowledgement, with no numeric source field. An explicitly supplied, paid, nondestructive port returns the complete current value

$$
\operatorname{Read}_H(u)=\gcd(qu,H),\qquad \gcd(0,H)=H.
\tag{AQBRP.2}
$$

Calls are serial and complete before the next call; reads occur at the current operation boundary. The source binding remains the same, and there is no unreported writer. No reset, clone, saved entry source, physical inverse, subtraction, direct coordinate reader, arbitrary scalar multiplier or additional source observation is available. Timing, source size, backing capacity, service prices and failure channels are not accessible discriminators. In particular, a cost account below is not a further read port.

The installed controller initially has only public $H$, finite source-independent code and constants, bound handles for (AQBRP.1)–(AQBRP.2), lawful current rights, and writable backing. The opaque binding and rights convey no quantity or source-dependent selector advice. There is no acquired old scalar code, initial gcd, entry quantity, response table, history or clock. Local choices depend only on public inputs and replies already obtained on this run. Exact local binary arithmetic and record operations are permitted, with their installed code, storage and actual work charged. For each asserted finite run, sufficient finite backing for its actual source and controller is supplied, and every admitted primitive service and finite local computation completes. This is a per-run service/material premise, not a fixed finite capacity covering all unbounded entries or all future lengths. Rights retention, binding, service installation and backing provision are also charged. Declaring (AQBRP.2) is a conditional mathematical premise; its realization on a narrower Native, LAB or physical backend is not supplied by this declaration.

For a nonempty ordered tree with leaves $\alpha,\beta$, its composition fold counts the two leaf types. The original simultaneous substitution $\rho(\alpha)=\beta$, $\rho(\beta)=\langle\beta,\alpha\rangle$ and, for example, the fixed right graft $t\mapsto\langle t,\alpha\rangle$ induce (AQBRP.1), by [FARG, Sections 2–5 and 130.1](FIBONACCI_ATOMIC_RELATION_GENERATION.md). This fold is a source projection, not a syntax reader. The zero pair belongs to the arithmetic extension and is not the composition of a nonempty tree. All proofs below concern this pair interface, including its separate current gcd premise. They do not identify it with the positive scalar apparatus of Definition 1.1: the equal scalar quantities $q(3,0)=q(0,2)=6$ have replacement successors of quantities $9$ and $10$ respectively, as already observed in FARG5.1.

**Definition 9.2 (targets, independently meaningful fields and resource coordinates).** Write $A_H=\mathbb Z/H\mathbb Z$, including the singleton ring at $H=1$, and let $\bar u$ denote coordinatewise reduction of an actual source. Entry identification outputs the immutable label $e=\bar v_0$. Reached-state acquisition installs a separate mutable label $c=\bar u_*$ for the actual endpoint $u_*$. Callable use requires retention of its actual binding and lawful rights, together with installed local output, prediction and synchronized update procedures. It does not require the endpoint behavior to equal the entry behavior or the actual source to return to $v_0$.

At a fixed actual source cut, the spatial arithmetic field is $\mathcal S_H(u)=\bar u$: the two occurrence counts modulo $H$, retaining the distinction between atom types and forgetting order and brackets. Its prospective replacement-time field is the independently specified quantity progression

$$
\mathcal T_H(u)(k)=qM^ku\bmod H\quad(k\in\mathbb N).
\tag{AQBRP.3}
$$

This progression describes what repeated replacement does to quantity; it is not an input oracle or a clock. Actual temporal data instead consist of the chronological action/read events of the acquisition, their actual replies, and separately their service work. Service work can be an external mathematical account even when unobservable to the controller. Neither that chronology nor elapsed physical time is identified with (AQBRP.3).

The arithmetic boundary field is the complete controlled continuation behavior

$$
\mathcal B_H(u)(W)=\gcd\bigl(q\,W(u),H\bigr)
\quad\bigl(W\in\{R,G\}^{<\omega}\bigr),
\tag{AQBRP.4}
$$

with the empty word allowed and with successors given by prefixing an actual next action. Words here and below are written in chronological order. Each prefix is a possible current observation, but (AQBRP.4) does not supply its replies without calls. This full boundary has a different meaning from one current gcd answer. Memory is the actual acquired action/reply tape, acquired indices and branch records, immutable entry register, mutable current register, public code/control, and retained callable binding and rights. It contains no unobserved pre-entry history.

The primitive resource vector is $(N_{\rm read},N_G,N_R)$ on this same run. Physical source letters count individual occurrences of $R$ and $G$, even in a displayed power. Installed code, binding/rights, local computation, record reads/writes, parameter and acknowledgement handling, output/installation, backing, source services and source retention are additional coordinates. There is no unit-cost assumption for a global replacement.

**Theorem 9.3 (all-source direct acquisition, exact realized vectors and growth).** Under Definitions 9.1–9.2, one finite source-blind deterministic algorithm, uniform in public $H$, terminates on every $v_0=(a,b)\in\mathbb N^2$, earns $e=\bar v_0$, and installs $c=\bar u_*$ with actual continued callable use for every finite subsequent original $R/G$ continuation under the same service and synchronization premises.

For $H=1$ it uses vector $(0,0,0)$, leaves $u_*=v_0$, and installs the singleton predictor. For odd $H>1$ its vector and exact integer endpoint are

$$
(N_{\rm read},N_G,N_R)=(2H,2H,1),\qquad
u_*=Mv_0+H M\alpha+H\alpha,
\tag{AQBRP.5}
$$

For even $H$, put $L=H/2$. The actual observed branches determine $r\in\{0,1,2\}$ and $\chi\in\{0,1\}$, defined in the proof. Their exact vector and integer endpoint are

$$
(N_{\rm read},N_G,N_R)=(H+r+\chi,\ H+\chi,\ r+1+\chi),
\tag{AQBRP.6}
$$

$$
u_*=\begin{cases}
M^{r+1}v_0+L(M\alpha+\alpha),&\chi=0,\\
M^{r+2}v_0+L(M^2\alpha+\alpha)+M\alpha,&\chi=1,
\end{cases}
\tag{AQBRP.7}
$$

In particular the even bounds are $N_{\rm read}\le H+3$, $N_G\le H+1$ and $N_R\le4$, all for this one run. No assertion that every branch pair occurs at each $H$ is needed. The exact terminal quantities are

$$
qu_*=\begin{cases}
2a+3b,&H=1,\\
3a+5b+5H,&H>1\text{ odd},\\
qM^{r+1+\chi}v_0+(5+2\chi)H/2+3\chi,&H\text{ even}.
\end{cases}
\tag{AQBRP.8}
$$

Every actual acquisition prefix has quantity at most its terminal quantity. In the even case this gives the uniform bound

$$
qu\le qu_*\le13a+21b+\frac{7H}{2}+3
\quad\text{at every actual prefix }u.
\tag{AQBRP.9}
$$

A sufficient explicit retained acquisition tape uses $O(H\log(H+1))$ bits beyond public installed code and backend binding/rights representations; modular working registers use $O(\log(H+1))$ further bits. All their work and retention are paid. These local bounds do not bound source backing or source-service work independently of the unknown entry.

On the actual reached cut, acquired memory computes $\mathcal S_H$, $\mathcal T_H$ and $\mathcal B_H$, with agreeing recovery routes and action-compatible updates. On their actual mathematical images the three arithmetic fields determine one another. This uses the existing full-behavior quotient, not an extra response oracle. Whole-memory installation, ordered syntax, exact unbounded composition and actual chronology are not recovered by these arithmetic fields. The theorem specifies an attainable joint resource point; it asserts no continuous optimum or resource dominance over reset strategies.

**Proof (the paid scan used inside the construction).** For $H>1$ let $d=\gcd(2,H)$ and $L=H/d$. Suppose an actual scan starts at $x$ with $d\mid qx$. At each $j=0,\ldots,L-1$, read the current state and then execute one $G$, including after the final read. Induction gives the actual chronological read states and endpoint

$$
x+j\alpha,\qquad g_j=\gcd(qx+2j,H),\qquad
x_{\rm end}=x+L\alpha.
\tag{AQBRP.10}
$$

The congruence $2j\equiv-qx\pmod H$, divided by $d$, has exactly one solution modulo $L$, since $2/d$ is a unit modulo $L$. Thus exactly one of these $L$ paid replies equals $H$. Its acquired position $j_x$ gives $qx\equiv-2j_x\pmod H$. Also $2L$ is divisible by $H$, so this is the quantity residue at the scan endpoint as well. This is the positive-addend saturation argument of Theorem 3.1, specialized to the actual $+2$ quantity change of $G$, and is reused here. It is not a separately new scanning theorem.

A stored reply may supply the $j=0$ entry of this scan only if it was obtained at this exact start on the same binding and no $R$ or $G$ intervened. Local processing does not invalidate it. Such a reuse is one physical read with two local uses, never a second free observation or a reply transported across an update. All other scan positions are actually read. Even when saturation occurs early, this specified controller completes all $L$ read positions and all $L$ grafts. The closing graft cannot be omitted from its endpoint or costs.

**Proof (odd modulus).** For odd $H>1$, $d=1$ and $L=H$, so every start satisfies the scan condition. Scan from $v_0$ to $w=v_0+H\alpha$. Execute one $R$ and scan from $Mw$ to $u_*=Mw+H\alpha$. The acquired saturation indices give

$$
n=qw\bmod H=qv_0\bmod H,\qquad z=qMw\bmod H.
\tag{AQBRP.11}
$$

Use the already supplied unimodular quantity coordinates of FARG5.4 and FARG130.1,

$$
C=\begin{pmatrix}2&3\\3&5\end{pmatrix},\qquad
C^{-1}=\begin{pmatrix}5&-3\\-3&2\end{pmatrix},\qquad
\widehat w=C^{-1}\binom nz\in A_H^2.
\tag{AQBRP.12}
$$

Thus $\widehat w=\bar w$. Write the immutable entry register as $e=\widehat w-H\alpha=\bar v_0$ and the separate reached register as $c=M\widehat w+H\alpha=\bar u_*$. The displayed subtractions are local residue computations on earned operands. No source inverse occurs. Two complete scans and one replacement give (AQBRP.5), including its integer endpoint.

**Proof (even entry parity and the first scan).** Suppose $H$ is even. Read the actual entry. While the acquired reply is odd, execute one $R$ and read again. Let $r$ count these replacements. For even $H$, a gcd reply is even exactly when the actual quantity is even. The identity $M^2=M+I$ gives

$$
qM^{k+2}v_0=qM^{k+1}v_0+qM^kv_0.
\tag{AQBRP.13}
$$

If two consecutive quantities are odd, their next is even. Consequently $r\le2$, and this search earns an even reply at the actual state $x=M^rv_0$. It neither reads a coordinate nor receives an entry quantity. Reuse just that last reply as the first position of the $L$-step scan, then perform all its closing grafts. It ends at

$$
w=M^rv_0+L\alpha,
\qquad N=qw=qx+H\text{ is even},
\qquad n=N\bmod H=-2j_x\bmod H.
\tag{AQBRP.14}
$$

$N$ here is a proof variable for the actual integer, not a controller input. The first scan has acquired $n$ and made $L$ real grafts. Its coordinate displacement $L\alpha$ is retained in decoding, even though its quantity displacement $H$ vanishes modulo $H$.

**Proof (the second scan and the actual parity correction).** Execute $R$ on $w$ and read at $Mw$. Put $Z=qMw$ as a proof variable. If this paid reply is even, set $\chi=0$ and reuse it at position zero of the next $L$-step scan. This scan acquires $z=Z\bmod H$ and ends at $u_*=Mw+L\alpha$.

If that reply is odd, set $\chi=1$. Retain it as a paid parity test, then execute $G$ followed by $R$ on that very state. The successive actual states are $Mw$, $Mw+\alpha$, and

$$
y'=M(Mw+\alpha)=M^2w+M\alpha,\qquad
qy'=N+Z+3.
\tag{AQBRP.15}
$$

Here $M^2=M+I$ and $qM\alpha=3$ give the integer equality. Because $N$ is even and $Z$ is odd, $qy'$ is even. Thus a fresh $L$-step scan from $y'$ is enabled. Its first read is a new paid read: the odd reply at $Mw$ is not reused after $G,R$. If its acquired quantity residue is $t$, set

$$
z=t-n-3\pmod H=Z\bmod H.
\tag{AQBRP.16}
$$

The actual endpoint is $u_*=M^2w+M\alpha+L\alpha$. The scalar $+3$ in (AQBRP.15) is a consequence of two coupled original actions, not a new scalar primitive or an assumed realization bridge.

In both branches (AQBRP.12) now gives $\widehat w=\bar w$. The earned entry and reached registers are respectively

$$
e=M^{-r}(\widehat w-L\alpha),\qquad
c=\begin{cases}
M\widehat w+L\alpha,&\chi=0,\\
M^2\widehat w+M\alpha+L\alpha,&\chi=1.
\end{cases}
\tag{AQBRP.17}
$$

$M^{-1}=\begin{pmatrix}-1&1\\1&0\end{pmatrix}$ exists over every $A_H$, and $r\le2$. Its use in (AQBRP.17) is finite local arithmetic, not backward source movement. The first formula gives $e=\bar v_0$ by (AQBRP.14); the second gives $c=\bar u_*$ by the actual branch trajectories. Expanding those trajectories gives exactly (AQBRP.7).

This specifies every source-dependent choice: parity search uses acquired gcd parity, the correction uses the next acquired parity, and scan decoding uses acquired saturation positions. All other choices are public loops or local arithmetic. There is one deterministic program for all entries, not a family of selectors indexed by hidden coordinates. At $H=2$, $L=1$: each scan still has its one genuine read and its closing graft; (AQBRP.14)–(AQBRP.17) remain valid. At $v_0=(0,0)$ the initial even read is already saturated, which is legitimate and paid; saturation never asserts that the exact source is zero. For $H=1$, bypass both scans and install the unique labels, with constant predicted gcd $1$ and no source call.

**Proof (exact realized counts and source growth).** The odd branch has two scans of $H$ reads and $H$ grafts, with one intervening replacement. In the even branch the entry search has $r+1$ reads; the first scan adds $L-1$ reads; the replacement test adds one; and the second scan adds $L-1$ reads when $\chi=0$, or $L$ when $\chi=1$. Their sum is $2L+r+\chi$. There are $2L+\chi$ grafts and $r+1+\chi$ replacements. This proves (AQBRP.6) without moving a cached reply across a source action. The number of source letters, excluding reads, is $2H+1$ for odd $H>1$, and $H+r+1+2\chi$ for even $H$. The positive short-word reset compilers of [Canonical Window Compiler Geometry, Sections 1.1 and 1.4–1.8](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md) already supply a different attainable query/letter account under reset. This proof counts the displayed continuous schedule alone; it neither rederives their compiler nor transfers a reset minimum or another strategy's smaller read budget to this vector.

For even $H$ the two endpoint formulas yield, using $q\alpha=2$, $qM\alpha=3$, and $qM^2\alpha=5$,

$$
qu_* = qM^{r+1+\chi}v_0+(5+2\chi)L+3\chi.
\tag{AQBRP.18}
$$

For odd $H$, expansion of (AQBRP.5) yields $3a+5b+5H$. These are integer equalities, proving (AQBRP.8). On every nonnegative pair,

$$
q(Ru)-qu=u_1+2u_2\ge0,\qquad q(Gu)-qu=2.
\tag{AQBRP.19}
$$

Reads preserve the source. Thus every acquisition prefix is bounded by the terminal quantity. Finally $r+1+\chi\le4$ and

$$
q=(2,3),\quad qM=(3,5),\quad qM^2=(5,8),\quad
qM^3=(8,13),\quad qM^4=(13,21).
\tag{AQBRP.20}
$$

These rows increase coordinatewise. Since $a,b\ge0$, (AQBRP.18) gives $qu_*\le13a+21b+7L+3$, proving precisely (AQBRP.9). It also implies the weaker bound $13a+21b+13(H+1)$; no such larger allowance is needed for this construction. The inequalities bound the actual source size in terms of its unknown entry; they do not make the source size an accessible input.

**Proof (finite earned memory and complete service account).** Let $b_H=\lceil\log_2(H+1)\rceil$. Retain a chronological tape with one constant-size action tag per call and one $b_H$-bit field for each gcd reply, plus the fixed acknowledgements. Reuse is a local reference to an existing entry, not an extra reply. The exact counts just proved give $O(H)$ tape entries. The two saturation indices, loop/phase counters, $r,\chi$, residues $n,z,t$, immutable $e$ and mutable $c$ need $O(b_H)$ working bits. Sums and products in the decoder have fixed coefficients; intermediate residues and their reductions have $O(b_H)$ bits. Exact binary division with remainder, gcd, comparisons and these fixed-coefficient operations can use finitely many such registers and finite bit loops. No factorization of $H$, source coordinate or precomputed source-response table is needed. The tape uses $O(Hb_H)$ bits beyond installed code and backend references/rights; reading/writing it and every bit loop are charged. Public input delivery, installation of this uniform program, construction of its local record fields and output delivery are not free.

More precisely, let $\mathcal I_{\rm read},\mathcal I_G,\mathcal I_R$ be the actual call positions, and $u_i$ the actual pre-call source at position $i$. For separately supplied finite service tariffs $\rho_H,\gamma,\tau$, the source-service work on this run is exactly

$$
W_{\rm svc}=
\sum_{i\in\mathcal I_{\rm read}}\rho_H(u_i)
+\sum_{i\in\mathcal I_G}\gamma(u_i)
+\sum_{i\in\mathcal I_R}\tau(u_i).
\tag{AQBRP.21}
$$

To it add the actual local bit work, input/output and acknowledgement handling, installed program/data and service blocks, bindings/rights, backing provision, source storage/retention and retained records, in their declared resource coordinates. These tariffs price the actual implementation of the specified services, rather than adding observable numeric replies. A replacement of an entire represented tree is not thereby one local rewrite or one bit operation. Applying (AQBRP.9) to storage or workload requires a separately justified correspondence between quantity, representation and tariff. Sufficient finite backing for acquisition is part of Definition 9.1; additional backing for any chosen finite continuation is supplied and charged under the same condition. Indefinitely retaining future inputs or traces has no bound supplied by the acquisition-tape estimate. Thus finite code is not a bounded-memory claim for arbitrary future retention or unbounded source size.

**Proof (installed use, common-source recovery and its limits).** The reached-state task is homing in the sense of [Kushik and Yevtushenko, Section 2](https://arxiv.org/html/1504.02444v1): each surviving trace determines a unique reached task state. Entry identification is a separate assertion, as in the initialized-state test framework of [van den Bos and Vaandrager, Definitions 7–10](https://arxiv.org/html/1907.11034v2). These finite-machine distinctions are terminology here; the direct proof above establishes the actual infinite-source correspondence and costs. Really write the acquired $e,c$, tape and branch/scan records into the supplied local fields and retain the original binding and current rights. Install the following finite local reader and updater, reusing FARG130.1, FARG130.5 and FARG133.6:

$$
\operatorname{Out}_H(c)=\gcd(2c_1+3c_2,H),\qquad
\delta_R(c)=Mc,\qquad \delta_G(c)=c+\alpha.
\tag{AQBRP.22}
$$

The gcd uses any integer representatives of $c_1,c_2$ and is representative-independent. For an actual next requested action, the controller calls its retained source handle, consumes its completion acknowledgement, updates $c$ by the corresponding $\delta$, and exposes the next callable cut only after both have completed. Exclusive serial control prevents an observation between an actual update and this local commit. For a hypothetical finite word it instead evaluates these same updates on a scratch residue pair and returns the predicted outputs without changing the source. These are installed computations on earned registers, not declarations that a semantic inverse is already available.

The initial equalities $e=\bar v_0$, $c=\bar u_*$ were proved above. Congruence under each actual $R,G$ and induction over every finite subsequent word $V$ give

$$
c_V=\overline{V(u_*)},\qquad
\operatorname{Out}_H(c_V)=\mathcal B_H(u_*)(V).
\tag{AQBRP.23}
$$

The entry register stays immutable. No further source read is required by this synchronized predictor; all subsequent source actions, local updates, requested output work and retained future data are still paid. An external unreported update, revoked right or interrupted commit violates the stated synchronization/service premise.

Here are the exact recovery routes on this one acquired cut. The first two terms of (AQBRP.3) are $C\bar u$, so the existing inverse (AQBRP.12) gives $\mathcal T_H\mapsto\mathcal S_H$; the forward map is (AQBRP.3). By the existing FARG130.5 full original-alpha behavior quotient, $\mathcal B_H(u)=\mathcal B_H(u')$ exactly when $\bar u=\bar u'$, including $H=1$. Thus $\mathcal S_H\mapsto\mathcal B_H$ is (AQBRP.22) evaluated on words, and its inverse is well defined on the actual image. This inverse of a complete mathematical behavior is not a free behavior oracle in the acquisition interface. Computing both fields through the earned register yields exactly these maps, so $\mathcal T_H\mapsto\mathcal S_H\mapsto\mathcal B_H$ agrees with their direct common-source correspondence, and likewise in reverse. The theorem's acquisition supplies the missing finite earned payload, rather than assuming that inverse as initialization.

These routes commute with actual dynamics: replacement shifts the progression by one, grafting adds $qM^k\alpha$ to its $k$th term, and each boundary successor prefixes the same actual action to its continuation word. Equations (AQBRP.22)–(AQBRP.23) realize all of these updates on the same source. If $A$ is the recorded acquisition action word with reads omitted, its actual affine law is $A(v)=M^kv+t_A$, with $t_A$ computed from that known word. Hence forward transport gives $c=M^ke+t_A$ modulo $H$, and, retaining this action complement, local inverse transport gives $e=M^{-k}(c-t_A)$. This is the existing affine-word law of FARG130.2 applied to the newly acquired real history. It agrees with (AQBRP.11)–(AQBRP.17). It does not restore a callable entry source; the callable handle still refers to $u_*$.

The losses remain genuine. The distinct ordered trees $\langle\alpha,\beta\rangle$ and $\langle\beta,\alpha\rangle$ have the same composition, hence the same three arithmetic fields and all common arithmetic continuations; these fields cannot recover order, brackets or addresses. Even exact composition forgets brackets, while reduction further merges distinct actual pairs $v$ and $v+H\alpha$. Inserting the actual word $G^H$ changes the integer source and chronology but leaves its residue, prospective progression and arithmetic boundary unchanged. It adds $H$ source events; any separately priced nonzero grade of that insertion also differs. Therefore those arithmetic fields recover neither actual chronology nor such a grade or elapsed physical time. They also forget handle identity, installed code, record allocation and rights: two installations on equal residues can differ in these fields, which do not enter (AQBRP.3)–(AQBRP.4). Retained acquisition memory computes the arithmetic fields, but they do not reconstruct the whole memory installation. The tape earns only its actual post-entry records, not missing earlier history. This establishes the stated recovery domain and boundaries. $\square$

**Definition 9.4 (supplier subtraction and the conditional claim domain).** The load-bearing addition in Theorem 9.3 is the direct pair-source parity schedule, its common integer endpoints, exact cached-read counts and source-growth account. The saturation sweep is reused from Theorem 3.1; $C^{-1}$, $M^2=M+I$, affine word transport and the full original-graft behavior quotient are reused from FARG5 and FARG130–131 and their [`GraftAffineClosure.result`](../../../D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.lean) with its [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.scribe.cs). Sections 5–7 here supply the distinction between earned entry information, reached-state installation and behavior/literal return on the scalar interface. Their scalar multiplications and genuinely acquired old code are absent from Definition 9.1; they are not implicit steps of the pair construction.

[FARG127.7](FIBONACCI_ATOMIC_RELATION_GENERATION.md) already supplies single-copy increasing-time execution under a separate current gcd port for its pure-replacement future-class task. Its later prime-power supplier [`protocol_spec`](../../../D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.lean), including the internal `continuation_fiber` and `paid_first_layer` arguments and its [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.scribe.cs), preserves that pure-replacement target. It does not supply the complete original-$G/R$ composition target here. For example, multiplication of a pair by a unit modulo $H$ preserves every pure-replacement gcd, while it can change its composition residue. The full-alpha quotient used above is the stronger task distinction, not a new claim that continuous observation was absent.

[FARG133.1–133.6](FIBONACCI_ATOMIC_RELATION_GENERATION.md), [`terminal_gcd_acquisition_cost`](../../../D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost.lean), its internal `scalar_word_realization` and [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost.scribe.cs) retain exactly their same-entry-reset, terminal-only query theorem. The later [Canonical Window Compiler Geometry, Sections 1–2](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md) supplies shorter positive reset-query words, adjacent-direction decoding and its own prefix/control bounds. Those are available reset strategies, not a missing compiler to reprove. Neither their smaller read budgets nor another strategy's resource coordinate is paired with (AQBRP.6). The present linear scan may use more reads while making at most four replacements; no optimum, total-work comparison or global dominance follows.

The [Arithmetic Refinement Memory, Section 6](RECURSIVE_RELATIONAL_OBSERVATION_ARITHMETIC_REFINEMENT_MEMORY.md) direct initialization reader, [LAB Arithmetic Growth, Definitions 4.2 and 5.1](RECURSIVE_RELATIONAL_OBSERVATION_LAB_ARITHMETIC_GROWTH.md) paid field traversal, and [LAB Spent-Trigger Acquisition, Section 3](RECURSIVE_RELATIONAL_OBSERVATION_LAB_SPENT_TRIGGER_ACQUISITION.md) stationary prepass concern their own supplied access and actuators. Likewise [`NativeFullSourceProducer`](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean), [`NativePassiveServiceRealization`](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.lean) and [`ActualPureAcquisitionCompiler`](../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.lean), with their source-traversal, interpreter and cache helpers, acquire through stationary Native address replies. These stronger or different access contracts do not construct (AQBRP.2) or price its original global replacement. In particular the local LAB edits are not the simultaneous $R$ of (AQBRP.1).

The initialized-state/reached-state distinction is literature-attested in Petra van den Bos and Frits Vaandrager, [*State Identification for Labeled Transition Systems with Inputs and Outputs*, arXiv:1907.11034v2, Definitions 7–10 and Lemma 6](https://arxiv.org/html/1907.11034v2), and Natalia Kushik and Nina Yevtushenko, [*Adaptive Homing is in P*, arXiv:1504.02444v1, Section 2](https://arxiv.org/html/1504.02444v1). The latter defines homing by a singleton reached-successor set for each surviving trace on its known finite-machine contract. Markus Theo Frohme, [*Active Automata Learning with Adaptive Distinguishing Sequences*, arXiv:1902.01139v1, Section 8.1](https://arxiv.org/html/1902.01139v1), distinguishes dependent symbol queries from a separately available reset query. These are suppliers of terminology and interface distinctions; their finite-machine results do not supply this arithmetic parity policy, port implementation or unbounded-source service bound. Theorem 9.3 is a `repo-derived` source-specific synthesis with the direct finite proof above, without a literature-priority assertion.

The attained result is paid acquisition and installed continued use of the arithmetic quotient on the changed two-coordinate current-port apparatus. It leaves unchanged the scalar AQBR definitions and all fixed-model settlements, including the original FARG133 reset-query formula and every fixed original-task/initialization restriction. Recovering the lost syntax, actual temporal fields and whole installation, realizing any claimed narrower backend port, and establishing mutual recovery of independently meaningful space, time, boundary and memory on the full intended process remain outside this arithmetic theorem. No universal physical space/time claim, alpha/beta primitive-minimality claim or completion of that full four-expression objective is asserted.

## 追加锚（本行以下为增补区）

## 10. Sharp continuous acquisition with return of the original arithmetic behavior

**Definition 10.1 (the continuous return task and its read budget).** Keep precisely Definitions 9.1–9.2. In particular, the entry is any $v_0\in\mathbb N^2$, including zero, the public input is the integer $H\ge1$, the only actual updates are $R(u)=Mu$ and $G(u)=u+\alpha$, and every source reply other than a paid current gcd is a fixed acknowledgement. There is no initially acquired source label. A successful return policy terminates on every entry with an earned immutable $e=\bar v_0$, an installed mutable $c=\bar u_*$ at the same retained handle, and

$$
\mathcal B_H(u_*)(W)=\mathcal B_H(v_0)(W)
\quad\text{for every }W\in\{R,G\}^{<\omega}.
\tag{AQBRS.1}
$$

It must also retain the lawful, synchronized callable continuation of Definition 9.2. By the supplied full original-alpha quotient, FARG130.5, condition (AQBRS.1) is equivalent to $\bar u_*=\bar v_0$; it is stronger than merely knowing the entry label while leaving the handle at another behavior. A policy is one deterministic source-blind program using only the initial public inputs and its actual acquired replies. Its action counts and local work may depend on those replies. Termination is per entry; a finite worst read budget $J$ means $N_{\rm read}(v_0)\le J$ for every entry, without imposing a uniform bound on source size. Let $Q_{\rm ret}(H)$ be the least such $J$ when attainable. All other resource coordinates remain those of Definition 9.2 and are not minimized by this notation.

For $H>1$ define the public integers

$$
B(H)=\max_{p^h\parallel H}h(p-1),\qquad
L_H=\min\{l\ge1:M^l=I\text{ over }A_H\}.
\tag{AQBRS.2}
$$

For a finite chronological word $W=A_1\cdots A_m$, define its closing word by reversing the order of its letters and replacing each letter with the indicated positive repetition:

$$
W^{\rm cl}=C_H(A_m)\cdots C_H(A_1),\qquad
C_H(R)=R^{L_H-1},\qquad C_H(G)=G^{H-1}.
\tag{AQBRS.3}
$$

An exponent zero denotes an empty block. This notation specifies actual positive source letters, each separately executed and charged. It supplies no inverse-action handle. FARG130.2 and `GraftAffineClosure.result` supply the finite modular period, so $L_H$ exists. The closing notation concerns the residue action alone; its integer source trajectory is still forward.

**Theorem 10.2 (the sharp read budget on the original continuous apparatus).** For every integer $H\ge1$, the continuous return task of Definition 10.1 is attained by a single uniform finite algorithm on all $v_0\in\mathbb N^2$, and

$$
\boxed{\quad Q_{\rm ret}(1)=0,\qquad
Q_{\rm ret}(H)=2B(H)\quad(H>1).\quad}
\tag{AQBRS.4}
$$

The lower bound holds for the entire deterministic source-blind terminating competitor class of Definition 10.1, including policies that use arbitrary finite adaptive $R/G$ words between reads and arbitrary charged local computation. The attained run returns the same actual handle to its entry full original-$R/G$ arithmetic behavior and installs $e=c=\bar v_0$ there. It uses no reset, clone, saved entry source, source inverse, scalar multiplication, extra observation or free initial gcd. The optimized coordinate is paid reads only.

**Proof (public preparation and positive closing).** Reuse the modular invertibility in FARG130: $\det M=-1$, and $G$ is translation by $\alpha$ on $A_H^2$. Thus on residues $C_H(R)$ is the inverse permutation of $R$ and $C_H(G)$ is the inverse permutation of $G$. Reading (AQBRS.3) in its stated chronological order cancels the last letter first, and gives

$$
\overline{W^{\rm cl}(W(u))}=\bar u
\quad\text{for every actual }u\in\mathbb N^2.
\tag{AQBRS.5}
$$

This is a local equality of residue actions. Every letter in its actual realization still maps $\mathbb N^2$ into itself. No coordinate of the source is subtracted. If $r(W)$ and $g(W)$ count the two letters in $W$, the actual word $WW^{\rm cl}$ contains exactly $L_Hr(W)$ replacements and $Hg(W)$ grafts. This includes the letters executed before its observation.

All preparation uses finite integer input representations. Factor $H$ by trial division, compute the needed prime powers and CRT coefficients, and compute $L_H$ by multiplying the $2$-by-$2$ residue matrix until it first reaches $I$. These are computations on public binary integers. For an explicit termination bound, among the $H^4+1$ matrices $I,M,\ldots,M^{H^4}$ two coincide. Multiplying their equality locally by an inverse matrix yields a positive return exponent at most $H^4$. Consequently $1\le L_H\le H^4$, and the stated search terminates. The existing factorial period supplies another finite bound; no factorial-size word is required by this order search. Matrix inversion here is public local arithmetic, not a source operation.

**Proof (one actual run attaining the bound).** Reuse the complete reset policy and positive short words of [Fibonacci Canonical Window Compiler Geometry, Theorems 1.4–1.6](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md), with its own definitions

$$
K=\min\{k\ge1:F_{k+4}\ge H\},\qquad
\gamma=1+\left\lceil\frac{K+1}{2}\right\rceil,
\qquad F_0=0,\ F_1=1.
\tag{AQBRS.6}
$$

This supplier recovers $y_0=qM^Kv_0$ and $y_1=qM^{K+1}v_0$ modulo $H$. In each stage the prime-power digit policies share that stage's one direction; CRT combines their shifts into one $d\in A_H$. Its finite compiler gives an actual word $W(k,d)$, with exactly $k\in\{K,K+1\}$ replacements and at most $\gamma$ grafts, satisfying

$$
\gcd(qW(k,d)(u),H)=\gcd(qM^ku+d,H)
\quad\text{for every }u\in\mathbb N^2.
\tag{AQBRS.7}
$$

Use that supplier's choices and updates, without adding a new initial observation. Whenever it requests a word $W$, execute $W$ on the current actual source, make one paid current read there, retain the actual reply, and then execute all of $W^{\rm cl}$ before beginning another test or exposing the returned cut. The fixed acknowledgements are consumed throughout. Supply the retained gcd to the local reset-policy computation. Its next shift and word depend only on public inputs and preceding paid replies. In particular, the closing word depends on the known word and public $H,L_H$, not on an unknown source coordinate or a separately acquired entry code.

Initially the current residue is $\bar v_0$. If it has this residue before a test, congruence and (AQBRS.7) make the one acquired reply exactly the reply of that reset test on $v_0$. Equation (AQBRS.5) then restores the current residue to $\bar v_0$. Induction over the actual tests proves both assertions at every completed test. There is only one integer source trajectory: the input to the next word can be a much larger integer pair than $v_0$. Periodicity of gcd makes its residue sufficient for the next acquired answer.

The supplied policy completes each scalar stage in at most $B(H)$ paid tests. Its decoder is the existing inverse of $D_K=CM^K$, with $C$ from (AQBRP.12):

$$
e=D_K^{-1}\binom{y_0}{y_1}=\bar v_0.
\tag{AQBRS.8}
$$

Thus the same continuous run has at most $2B(H)$ reads. Finish the last closing word, really store this earned $e$, and store a separate mutable $c=e$. This is a returned current label by (AQBRS.5). FARG130.5 gives (AQBRS.1), and Theorem 10.3 supplies the retained callable interface. Every loop and word is finite; the per-run completion and backing premises in Definition 9.1 suffice for termination. This constructs one program, uniform in $H$, rather than selecting a program by the hidden entry. The supplier's attaining source $D_K\bar v_0=(-1,-1)$ also follows this same reply history and uses all $2B(H)$ reads; alternatively the universal lower bound below forces the constructed policy's worst budget to be attained.

**Proof (lower bound for arbitrary continuous policies).** Let a successful continuous policy have finite worst read budget $J$. Compare it with the exact reset-query class of FARG133.1, solely to obtain a lower bound. A local simulator keeps that policy's program state, its acquired replies and the cumulative chronological source-action word $A$, initially empty. It simulates local computations and fixed acknowledgements and appends each requested actual $R$ or $G$ to $A$. When the policy requests a paid current read, the simulator makes one reset-model terminal query with the entire word $A$, starting at the reset model's same unknown entry $v_0$. Previous reads were nondestructive, so its answer is exactly

$$
\gcd(qA(v_0),H),
\tag{AQBRS.9}
$$

the answer of this continuous run at this cut. Feed it to the simulated policy and continue. The word $A$ omits read events but includes every source letter previously executed, including any policy-specific restoration or other adaptive action. It is one finite positive word selected by accessible history. An empty $A$ is an allowed charged query. Reusing $A$ for a repeated read still costs another query.

Induction on acquired replies gives precisely the policy's actual local choices and replies for every $v_0$. There is no need to simulate unknown integer coordinates: neither the original controller nor its simulator can inspect them. All source services complete with fixed acknowledgements, and source-dependent time, capacity, cost or failure discrimination is excluded by Definition 9.1. Termination on each entry therefore gives a terminating reset-query policy with the identical earned entry output and exactly the same number of paid replies. Any operations after its final read are simulated before accepting that output; their acknowledgement contains no new information. The reset policy recovers $\bar v_0$ on all $\mathbb N^2$ and has worst budget at most $J$.

Apply [FARG133.5](FIBONACCI_ATOMIC_RELATION_GENERATION.md) or, with $H$ the same positive modulus, [`terminal_gcd_acquisition_cost`](../../../D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost.lean). Its `acquisitionBudgets` are exactly terminating deterministic history policies, with a finite worst number of charged terminal tests; its source, target, words and full gcd answers are those just constructed. Its least-budget conclusion gives $J\ge2B(H)$. This reuses that supplier's complete prime-axis lower bound, including arbitrary adaptive choices and full-depth replies. No new affine-valuation lower-bound proof or independent-axis worst-case assumption is needed. The comparison does not give the continuous source a reset service. It proves that even entry identification alone in the continuous competitor class cannot beat this bound, hence neither can identification with return and retained use.

For $H=1$ the residue carrier is a singleton and every gcd is $1$. Leave the source unchanged and install its unique label and continuation, using no source call. Nonnegativity of budgets proves minimality. All preceding arguments admit zero coordinates and the exact zero source. At $H=2$, the reused short-word policy uses $R$ and $RR$, and $L_H=3$; their positive closing blocks give nine actual replacements, zero grafts and two paid reads on this construction. The zero source stays zero in that case, but an observed saturated gcd still identifies only a residue, not the literal zero pair. $\square$

**Theorem 10.3 (earned entry memory and synchronized continuation at the returned cut).** Under Theorem 10.2, retain the actual source binding and rights, the acquired action/reply tape and public decoding data, the immutable $e$, and the separate mutable $c=e$ after the last completed closing word. There are installed finite procedures for current output, hypothetical finite-word prediction, and actual original-$R/G$ execution. For every finite actual continuation $V$, at each completed call boundary they satisfy

$$
c_V=\overline{V(u_*)},\qquad
\operatorname{Out}_H(c_V)=\mathcal B_H(u_*)(V)
=\mathcal B_H(v_0)(V).
\tag{AQBRS.10}
$$

They require no further paid source read. This conclusion is conditional on the same exclusive serialization, retained rights and sufficient per-run service/backing premises as Definition 9.1, including for the chosen continuation.

**Proof.** Install the already supplied residue reader and updates of FARG130.1, FARG133.6 and (AQBRP.22):

$$
\operatorname{Out}_H(c)=\gcd(2c_1+3c_2,H),\qquad
\delta_R(c)=Mc,\qquad \delta_G(c)=c+\alpha.
\tag{AQBRS.11}
$$

Stored residue representatives are finite accessible integers, so these are terminating exact local computations. Current output evaluates this formula on the retained $c$. For prediction, read the actual supplied finite word, copy $c$ to a scratch pair, apply its letters there and evaluate the same output at every requested prefix, including the empty prefix. The source is unchanged by prediction. Its results are computed predictions from an earned label, not newly acquired source replies.

For an actual single-letter execution, call that original action on the retained source handle, consume its completion acknowledgement, and then replace $c$ by the corresponding $\delta_R(c)$ or $\delta_G(c)$. Expose the next callable cut only after both steps have finished. Actual word execution repeats this interface; all its source calls and local updates are charged. The immutable entry register is not overwritten. The acquired cut has $c=\bar u_*=\bar v_0$. Each supplied local update commutes with its actual action, so induction on every finite $V$ proves the first equality in (AQBRS.10). The reader and behavior-return equality prove the other two. Applying the same induction to scratch evaluation proves its agreement with every possible actual continuation. There is no unreported intermediate observation between an actual source update and the local commit under exclusive serial control.

In particular these registers implement the recovery routes of Definition 9.2 on this actual returned cut. The first two replacement-time quantities are $C c$, the spatial field is $c$, and the complete arithmetic boundary is the reader (AQBRS.11) evaluated after words. Their existing inverse correspondences from FARG5.4 and FARG130.5 agree with these computations because all use this same $c$. Actual replacement shifts the prospective progression, and an actual graft adds $qM^k\alpha$ to its $k$th term; the same local updates realize both transformations. The acquired memory now computes those fields at an actual source of the entry behavior, rather than only storing an entry answer while the callable source remains elsewhere. At $H=1$ the identical procedures use the singleton pair and constant output $1$. An unreported source action, revoked right or interrupted commit is outside the stated synchronization premise. $\square$

## 11. Actual action counts, source growth and retained material

**Theorem 11.1 (one-run resource vector of the sharp construction).** Fix $H>1$ and one actual run of the construction in Theorem 10.2. Let $T_0,T_1$ be its numbers of paid tests in the two supplied scalar stages, let $Q=T_0+T_1$, and let $g_j$ be the number of graft letters in the actual short word selected at test $j$. Put $A=N_R+N_G$ for the total executed source letters, including all closing words. Then the exact vector for this run is

$$
\begin{aligned}
N_{\rm read}&=Q,\\
N_R&=L_H\bigl(KT_0+(K+1)T_1\bigr),\\
N_G&=H\sum_{j=1}^{Q}g_j.
\end{aligned}
\tag{AQBRS.12}
$$

Consequently this same construction has

$$
Q\le2B(H),\qquad
N_R\le L_H(2K+1)B(H),\qquad
N_G\le2H\gamma B(H).
\tag{AQBRS.13}
$$

Let $A_*$ be its actual chronological source-action word with reads omitted, and let $r_i$ be the number of replacements strictly after the $i$th graft occurrence in that word. Its exact integer endpoint and every-prefix quantity bound are

$$
u_*=M^{N_R}v_0+\sum_{i=1}^{N_G}M^{r_i}\alpha,
\qquad
qu\le qu_*\le2^{N_R}\bigl(qv_0+2N_G\bigr)
\quad\text{for every actual acquisition prefix }u.
\tag{AQBRS.14}
$$

The endpoint has residue $\bar v_0$ even though (AQBRS.14) can describe a much larger actual pair. The counts in (AQBRS.12) are not the counts of the reset supplier without its new closing words, nor those of the parity scans in Theorem 9.3.

**Proof.** For test $j$, its selected word has $k_j=K$ or $K+1$ replacements and $g_j$ grafts. Its closing word has $(L_H-1)k_j$ replacements and $(H-1)g_j$ grafts. There is exactly one paid read between the two words and none inside the closing word. Summing gives (AQBRS.12). The supplier gives $T_s\le B(H)$ and $g_j\le\gamma$, yielding (AQBRS.13) on this same run.

The endpoint formula is the existing affine-word law, specialized to the actual completed word $A_*$: each replacement acts on the entry and on all previous grafts, and a graft contributes one $\alpha$ followed by exactly its remaining replacements. Reads leave that trajectory unchanged. On a nonnegative pair $u=(a',b')$,

$$
qRu=3a'+5b'\le2qu,\quad qRu-qu=a'+2b'\ge0,
\qquad qGu=qu+2.
\tag{AQBRS.15}
$$

Thus quantity never decreases along any actual prefix. Each graft's contribution to final quantity is at most $2\cdot2^{N_R}$, and the entry contribution at most $2^{N_R}qv_0$, proving (AQBRS.14). All coordinates are nonnegative throughout. This bound depends explicitly on the unknown entry and does not give the controller that quantity as an input. $\square$

**Theorem 11.2 (finite local implementation and complete material account).** The construction of Theorem 10.2 admits the finite representation and local-work bounds below, from binary integer input $H>1$. Its source-service account is the same-run sum (AQBRS.16), in addition to the separately specified material and retention coordinates. The costs of Theorem 11.1 refer to its one executed trajectory. If $u_i$ is the actual pre-call source and $\rho_H,\tau,\gamma_{\rm svc}$ are the supplied finite tariffs of current read, replacement and graft, its source-service work is exactly

$$
W_{\rm svc}=
\sum_{i\in\mathcal I_{\rm read}}\rho_H(u_i)
+\sum_{i\in\mathcal I_R}\tau(u_i)
+\sum_{i\in\mathcal I_G}\gamma_{\rm svc}(u_i).
\tag{AQBRS.16}
$$

The call sets include the closing words. Add the actual local bit work, public input and output handling, acknowledgements, installed code/data, handle binding and rights, source/backing provision, source retention and retained records. The tariffs are an external resource account, not accessible source-dependent answers. A global replacement on a represented tree need not cost one rewrite or one bit operation.

**Proof.** An explicit finite local realization uses the binary input $H$; its factorization, CRT data, modular matrix order, digit-prefix and stage state; a buffer for the currently selected short word; a reverse traversal of that buffer for its closing word; and repetition counters. With $b=\lceil\log_2(H+1)\rceil$, there are $O(b)$ prime-axis and Fibonacci entries of $O(b)$ bits each. The order counter uses $O(b)$ bits since $L_H\le H^4$. Negative local residues are reduced to their nonnegative representatives. Trial division, repeated modular matrix multiplication, extended Euclid, modular arithmetic, and finite digit and word traversals give an effective algorithm from these exact integer representations. No exact comparison against arbitrary real names is involved.

One may retain an explicit chronological tape with one fixed-size action/acknowledgement tag for each source call and a $b$-bit field for each paid gcd. For this actual acquisition its tape and local workspace have the conservative bound

$$
O\bigl(A+Qb+b^2\bigr)\text{ bits},
\tag{AQBRS.17}
$$

beyond installed code, service/binding data and actual source storage. The word buffer is only $O(b)$ letters: this is the supplied short compiler's length bound. The tape is written as calls complete; it is not an assumed pre-entry archive. All writing and later retention are paid. If a different tape representation is required, charge that representation and its processing instead.

For example a sequential binary implementation using school arithmetic has a conservative local-work upper bound

$$
O\bigl(H^4b^3+(A+Q+1)b^5\bigr)
\tag{AQBRS.18}
$$

for public preparation, test choice/compilation, closing-loop control, tape writing, local decoding and residue output. Indeed, the order search has at most $H^4$ fixed-size modular matrix multiplications; trial division uses at most $H$ trials. Each uses $O(b)$-bit integers and fits the first allowance. The finite prime-axis tables, Euclidean and CRT calculations and short-word compilation per read fit $O(b^5)$ by sequential scans of $O(b)$ entries and ordinary binary arithmetic. Each emitted letter, acknowledgement and tape tag, including each repeated closing letter, fits the same allowance. Decoding and writing the two residue registers fit the last constant allowance. These deliberately loose bounds do not absorb source service or source storage. Installation and delivery of callable service blocks and authentic rights are additional supplied costs, not consequences of a local binary program.

For a separately supplied finite continuation $V$, actual execution adds exactly its own $\#R(V)$ and $\#G(V)$ source calls, their service tariffs at their actual later states, and local updates, input handling and requested outputs. The installed predictor adds zero paid reads. Hypothetical evaluation pays its own word input and local arithmetic/output but executes no source letter. Retaining further histories or results adds their actual writes and storage; there is no acquisition-only bound on an unbounded future tape. A binary pair implementation can translate (AQBRS.14) into a source-dependent operand-length bound. A tree or other backend must supply its own quantity-to-material correspondence and tariffs. Sufficient finite backing for each fixed run is a premise; neither finite code nor finite $Q$ supplies bounded backing over all unbounded entries or all future continuations. No total-work, action-count, workspace, storage or physical implementation optimum is asserted. $\square$

## 12. Supplier correspondence and the precise recovery boundary

**Definition 12.1 (source-relative mathematical contribution).** The new claim is the sharp continuous acquisition-and-return join (AQBRS.4), together with its actual closing trajectory, retained entry-behavior continuation and same-run account. Its hypotheses are exactly the pair apparatus of Definitions 9.1–9.2. Theorem 9.3 remains a different attained schedule with its own lower replacement count and its own endpoints; no smaller read count is substituted into that schedule's resource vector.

The following ingredients are reused in their stated domains. FARG130.1–130.5 and [`GraftAffineClosure.result`](../../../D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.lean), with its [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.scribe.cs), supply the complete-pair action, positive modular period, affine word law, consecutive-quantity inverse and full original-alpha behavior quotient. Its internal `period`, `wordAffine`, `castRun` and `residueAutonomous` arguments concern these same natural pairs, including zero; they do not themselves acquire an unknown entry or implement a source inverse. FARG133.1–133.6 and [`TerminalGcdAcquisitionCost.terminal_gcd_acquisition_cost`](../../../D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost.lean), with its [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost.scribe.cs), supply the exact reset-query budget. Its internal `scalar_word_realization`, `budget_equivalence`, `lower_axis` and `word_response` arguments already cover complete terminal replies and terminating adaptive history policies. They are not new lower-bound results here. The new lower-bound step is the correspondence (AQBRS.9) from every admitted continuous policy to that existing reset class.

[Fibonacci Canonical Window Compiler Geometry, Sections 1.4–1.8](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md) supplies the short positive test words, the common-direction CRT policy and $D_K^{-1}$ decoder. The parameter match is its same $H,M,\alpha,q$, actual domain $\mathbb N^2$, two consecutive directions $K,K+1$, and complete current gcd; only its reset execution is replaced by the positive closing schedule proved here. The supplier's short-word bounds are used for $W_j$, while (AQBRS.12) counts the new physical closing letters too. AQBR5.1 and AQBR9.3 supply the earned-entry/current distinction and installed-update pattern; (AQBRS.10) applies it at the newly attained returned cut. The proof does not reproduce their arithmetic classification, scalar digit proof, CRT theorem, compiler proof or affine-valuation lower bound as a new contribution. This is `repo-derived` synthesis in the continuous contract, without a global literature-priority claim.

The primary state-identification terminology is that of Petra van den Bos and Frits Vaandrager, [*State Identification for Labeled Transition Systems with Inputs and Outputs*, arXiv:1907.11034v2, PDF Section 4, Definitions 12–14, 17 and 20](https://arxiv.org/pdf/1907.11034v2): adaptive tests select inputs from preceding outputs and distinguish initial alternatives through their possible complete observations. Here the alternatives are exact arithmetic residues, the actual source remains infinite, and (AQBRS.5) supplies a source-specific behavior return between tests. The finite-machine terminology supplies neither this positive closing realization nor its sharp arithmetic read budget. The initialized-state versus reached-state distinction and the separately supplied reset-query interface retain the meanings stated in Definitions 1.3 and 9.2 and their cited primary sources.

**Definition 12.2 (what this return recovers).** The acquired registers support the entire arithmetic boundary of every finite original-$R/G$ continuation at a real returned source cut. They recover the spatial residue and prospective replacement-time field through the already supplied equivalences of Section 9. These statements concern one actual source, the paid replies of its one run, and actual installed continued use. They leave the complete original chronology, source syntax and whole memory installation outside the inverse.

For instance the positive word $G^H$ changes the integer source, adds $H$ actual source events and leaves the full arithmetic behavior unchanged. Equal residues of $v$ and $v+H\alpha$ remain equal after every common word, although the integer sources differ. Distinct ordered trees with the same composition remain indistinguishable by this arithmetic task. Acquired arithmetic fields also do not encode which local service blocks, records, handle identity and rights have been installed. These are the existing Section 9 separating examples, and they continue to apply after behavior return. In particular the word called closing is a modular restoration; it does not undo source growth, erase the executed chronology, recover a missing pre-entry archive or rewind physical time.

The paid current gcd port, authentic bindings/rights and sufficient actual backing remain supplied premises. Realizing them on a narrower Native/LAB or physical backend is a separate obligation. Original scalar and reset-model statements, fixed original-task/initialization restrictions, and their open outcomes retain their own exact scopes. Unrestricted mutual recovery of independently meaningful space, time, boundary and memory, a physical duration or metric interpretation, whole-memory inversion, and total-resource parsimony are not consequences of this arithmetic theorem.

## 追加锚（本行以下为增补区）

## 13. Unknown future precisions on one retained original source

**Assumption 13.1 (variable-modulus access and authentic cuts).** Retain the pair source, original $R/G$ actions, opaque binding, exclusive serialization, fixed acknowledgements, absent side channels and charged finite-run material premises of Definitions 9.1–9.2. Enlarge only the public read parameter: at a current cut the supplied port accepts any actually delivered positive binary integer $H$ and returns the paid value $\gcd(qu,H)$. This requires installation and lawful access for every modulus actually used, including moduli chosen by the controller. Access merely to the requested moduli does not imply this stronger menu. There is still one actual $v_0\in\mathbb N^2$ and one continuously updated source; no later request selects another original pair.

Requests $H_1,H_2,\ldots$ are revealed successively at completed callable cuts. A controller must finish the current acquisition before admitting another request or external action. Between requests, every chosen finite continuation is executed through the synchronized original-action interface of Theorem 10.3. There is no promised bound or advance description of later moduli or continuations. A request generator may depend on all already exposed requests, replies, outputs and actions. A source-dependent supplied parameter is additional information when comparing identification tasks; the benchmark below retains its source-blind fixed-modulus meaning.

The controller records each actual completed action and acknowledgement on this binding, including acquisition and closing letters, from entry onward. It also records every paid read with its modulus and its position in that action sequence. Let $A_t$ be the actual chronological action prefix through cut $t$, where $t$ counts completed source letters and $A_0$ is empty. Reads do not advance this index. A retained past-cut name consists of its genuine prefix position and binding association; a fabricated or counterfactual word is not an authentic past cut. Calling the record authentic assumes faithful recording under this exclusive service contract, not a cryptographic proof against a malicious recorder.

At request prefix $n$, set

$$
H^{[n]}=\operatorname{lcm}(H_1,\ldots,H_n),\qquad
m_n=\max_{1\le i\le n}B(H_i)=B(H^{[n]}),\qquad B(1)=0.
\tag{AQBRO.1}
$$

The last equality follows from prime exponents in an lcm. The comparison quantity is the existing one-shot fixed-modulus worst budget $Q_{\rm ret}(H^{[n]})=2m_n$. It is a benchmark for obtaining that joint residue from an initially unlabelled pair. It is not defined as the offline optimum among variable-modulus policies, and it does not include prices, payload lengths or actions.

**Definition 13.2 (a finite envelope for a read budget).** For an integer $b\ge1$ put

$$
E(b)=\prod_{\substack{p\text{ prime}\\p\le b+1}}
 p^{\lfloor b/(p-1)\rfloor},\qquad E(0)=1.
\tag{AQBRO.2}
$$

This is a public integer computed from $b$, independent of the hidden pair. The archive at envelope $E$ stores an immutable earned original label $e_E=v_0\bmod E$, a separate mutable current label $c_E=u\bmod E$, the actual action/reply record and cut names, and the installed procedures, binding and rights. The notation $\bmod E$ for a pair means coordinatewise reduction. Retaining an abstract label alone does not retain any of the other components.

**Theorem 13.3 (earned common-original transport across an upgrade).** Suppose the current actual cut is $s$, with recorded prefix $A_s$. Apply Theorem 10.2 at any newly chosen $E>1$ to the current actual pair $x=A_s(v_0)$, using the variable-modulus port of Assumption 13.1. Let $s'$ be the actual cut after its final closing word. This one acquisition has the following simultaneous consequences.

It earns a stage-entry label $d_E=x\bmod E$ and returns the actual source to $d_E$ modulo $E$, at cost at most $2B(E)$ paid reads. From the same earned label and the recorded prefix it computes $e_E=v_0\bmod E$. For every authentically recorded cut $t\le s'$, including cuts inside this acquisition, it computes $a_{E,t}=A_t(v_0)\bmod E$, and hence the entire arithmetic boundary and prospective replacement-time field at that actual past cut. It installs current $c_E=a_{E,s'}=d_E$ and synchronized continued use on this handle.

If an earlier archive used $D\mid E$, the new original and every common past-cut label reduce to their old values modulo $D$. At the completed upgrade, the current label modulo $D$ equals its value at the upgrade's start. None of these claims says that $c_E=e_E$ when earlier actions have intervened, or that a handle to a past integer source has been recovered.

**Proof.** Reuse the authentic affine-word supplier FARG130.2, equivalently the first word-law component of [`GraftAffineClosure.result`](../../../D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.lean), at graft $w=\alpha$. For a known chronological prefix, its coefficients can be computed without observing the source:

$$
A_t(v)=M^{k_t}v+z_t,\qquad
(k_0,z_0)=(0,0),\qquad
\begin{cases}
(k,z)\longmapsto(k+1,Mz)&\text{on }R,\\
(k,z)\longmapsto(k,z+\alpha)&\text{on }G.
\end{cases}
\tag{AQBRO.3}
$$

Here $z_t\in\mathbb N^2$ is a mathematical integer coefficient. An actual decoder may replay the stored word with $z_t$ reduced modulo the newly supplied $E$ at every step; it need not have stored an exact large $z_t$ beforehand. Since $\det M=-1$, the following are finite computations on acquired residues and public recorded letters:

$$
e_E=M^{-k_s}(d_E-z_s)\pmod E,
\qquad
a_{E,t}=M^{k_t}e_E+z_t\pmod E.
\tag{AQBRO.4}
$$

Theorem 10.2 applies to $x\in\mathbb N^2$ with precisely its original access contract. Its entry variable is now $x$, rather than $v_0$. It gives $d_E=\bar x$, actual modular return at $s'$, and no uncharged initial read. Substitution of $x=M^{k_s}v_0+z_s$ proves the first formula of (AQBRO.4) is $v_0\bmod E$. The second consequently labels every recorded prefix, including the actual letters subsequently written by this acquisition. Its value at $s'$ agrees with $d_E$ because this acquisition returns modulo $E$. Theorem 10.3 installs the callable current reader and updater there, using $c_E=d_E$. Local inverse matrix arithmetic in (AQBRO.4) never invokes a source inverse.

For each cut $t$ and each finite hypothetical continuation $V$, the installed past-cut procedure evaluates

$$
\mathcal S_E(A_t(v_0))=a_{E,t},\qquad
\mathcal T_E(A_t(v_0))(j)=qM^ja_{E,t},\qquad
\mathcal B_E(A_t(v_0))(V)=\gcd(qV(a_{E,t}),E).
\tag{AQBRO.5}
$$

In the last expression $V$ acts on residues; the gcd uses any integer representative. These are the existing Section 9 recovery maps applied to earned data. They are computations of a boundary indexed by an authentic past cut, not newly observed replies or actual execution from that cut. A hypothetical word appended to $A_t$ stays a prediction unless it really occurred.

Reduction modulo $D\mid E$ commutes with all integer affine operations. Both earned original labels are reductions of the same $v_0$, and both labels of a common past cut are reductions of $A_t(v_0)$. This proves archive compatibility without combining marginal observations from different source states. The completed acquisition acts as the identity modulo $E$ on its own entry, hence modulo $D$ too. During its private execution the physical source may leave that residue; those intermediate actual cuts are recorded and are not exposed as completed upgrade calls. All steps have finite exact binary realizations using replay, modular arithmetic and the already supplied fixed-modulus acquisition. $\square$

## 14. A uniform online archive with a constant cumulative read bound

**Theorem 14.1 (doubling envelopes, return and every finite request prefix).** Under Assumption 13.1 there is one deterministic program, uniform over all original pairs and successively revealed positive integer requests, which supplies the compatible archive of Definition 13.2 and the recovery of Theorem 13.3. It uses no future request or future continuation. If $C_n$ counts all paid source reads through completion of request $n$, then

$$
\begin{cases}
C_n=0,&m_n=0,\\[2mm]
C_n\le 4b_n-2<8m_n
       =4Q_{\rm ret}(H^{[n]}),&m_n\ge1,
\end{cases}
\qquad
b_n=2^{\lceil\log_2m_n\rceil}\quad(m_n\ge1).
\tag{AQBRO.6}
$$

The exponent in $b_n$ is computed by integer doubling, without a real-number oracle. At every completed request the installed envelope is $E(b_n)$ when $m_n>0$, and is $1$ otherwise. It answers every requested modulus and every divisor of that envelope at the current cut or any retained authentic past cut. Current output, finite-word prediction and synchronized further original actions require no additional source read at these covered moduli. Actual actions and all local processing remain charged.

The bound is pointwise for every completed finite request prefix, including when request choices depend on the accessible preceding history. It compares cumulative paid reads with the joint fixed-modulus benchmark; it asserts no optimal competitive ratio for the full variable-modulus problem.

**Proof (what the envelope supplies).** For each prime $p$, the exponent in $E(b)$ is $\lfloor b/(p-1)\rfloor$ when $p\le b+1$ and zero otherwise. Therefore

$$
H\mid E(b)\ \Longleftrightarrow\ B(H)\le b,
\qquad B(E(b))=b\quad(b\ge1),
\qquad E(b)\mid E(b')\quad(0\le b\le b').
\tag{AQBRO.7}
$$

For the first equivalence compare prime exponents. A positive exponent allowed by $B(H)\le b$ forces $p\le b+1$; each exponent is then at most $\lfloor b/(p-1)\rfloor$. The reverse implication uses the same inequalities. For equality $B(E(b))=b$, every axis has cost at most $b$, and the $2$-axis has exponent exactly $b$. Monotonicity follows by comparing floors. Thus $E(b)$ is the least common multiple of all positive $H$ with $B(H)\le b$. In particular a single earned label modulo this one integer covers every such request, rather than predicting which prime will be asked for next. This elementary divisibility calculation is an intermediate step for the acquisition construction.

**Proof (the actual online controller).** Start with envelope $1$, its singleton original/current labels, and an empty actual action record. On receiving $H$, factor that public integer by finite trial division to compute $B(H)$. If $H$ divides the installed envelope, use the earned residue registers and Theorem 10.3; do not read the source. Otherwise compute the least power of two $b\ge B(H)$, form the exact public integer $E(b)$, and execute Theorem 13.3 on the very current source. Finish every physical closing letter, record it, compute the new common-original label, install current use, and only then complete the request.

No intermediate skipped power of two is acquired. At a miss the new budget exceeds the old one; (AQBRO.7) shows that every previously requested modulus and every previous envelope divides the new envelope. Induction proves that at prefix $n$ this budget is exactly the least power of two covering $m_n$. The same induction with Theorem 13.3 proves original-label and past-cut compatibility, actual modular return at each upgrade, and correct synchronized current use between upgrades. This preserves one source and one archive even when intermediate continuations change its original behavior. An upgrade returns the behavior at that upgrade's entry; it does not undo those continuations.

**Proof (cumulative payment and nonanticipation).** Let $b_1'<\cdots<b_J'$ be the budgets actually acquired by prefix $n$. They are distinct nonnegative powers of two, with last term $b_n$. At each such stage Theorem 10.2 is executed at the actual modulus $E(b_j')$, and (AQBRO.7) gives at most $2b_j'$ genuine paid reads. Thus

$$
C_n=\sum_{j=1}^J Q_j
\le2\sum_{j=1}^J b_j'
\le2(1+2+\cdots+b_n)
=4b_n-2.
\tag{AQBRO.8}
$$

For $m_n\ge1$ the least covering power satisfies $m_n\le b_n<2m_n$, proving (AQBRO.6). If every request is one, no acquisition is made. Public preparation, action selection inside the fixed-modulus routine and subsequent register updates depend only on delivered integers, recorded letters and already acquired replies. The algorithm uses neither a future request nor a source-indexed choice of initial code.

The finite geometric payment inequality is the classical doubling argument in Chrobak–Kenyon–Noga–Young, [*Incremental Medians via Online Bidding*, Theorem 1(a) and Section 2](https://arxiv.org/html/cs/0504103v3). Here current requests reveal their budget, so the controller can skip unused bids; the displayed sum is an upper bound by that classical payment sequence. The source-specific content is that each actually paid envelope is acquired and returned on the same changing source and is transported to one original-cut archive. The bidding inequality alone supplies none of those correspondences. Its classical lower bounds do not prove an online lower bound in this apparatus. $\square$

**Proposition 14.2 (what an acquired precision archive leaves undecided).** At any finite completed request prefix the construction supplies arithmetic recovery only at covered moduli and authentically recorded cuts. The retained action word supplies the original-action chronology from entry, separately from its arithmetic labels. Arithmetic fields alone do not recover that word, elapsed time, literal integer source, tree syntax, bindings, rights or the rest of the memory installation. In the absence of additional source-dependent input, no finite archive certifies arbitrary finer original residues solely from its finite paid transcript.

If the acquired budgets are unbounded, their immutable original labels together determine the actual $v_0$ uniquely as a mathematical element of $\mathbb N^2$. This all-level injectivity does not provide a finite stopping certificate for exact unbounded-source recovery or a finite store for the entire stream.

**Proof.** Fix a completed run with finite action history and all moduli actually read. Their lcm $D$ is finite; in this construction they divide the last envelope. For any original pair $v$, the pair $v+D\alpha$ is a distinct nonnegative source with the same initial residues modulo every read modulus. Congruence and deterministic branch induction give the same paid replies, selected actions, stopping decisions and outputs for this fixed request history. The requests and continuations may be held fixed as an admissible history when making this comparison. Choose a prime $p\nmid D$. The two original pairs differ modulo $p$, so a finite transcript has not acquired all finer residues. The unknown-source service assumptions must hold for each compared finite run, as in Definition 9.1; inaccessible service prices cannot distinguish them.

The existing insertion $G^E$ preserves every arithmetic field modulo the installed $E$ and changes the literal integer source and action chronology. A separately nonzero path grade changes too. Thus chronology is available here because actual letters were recorded, not by inversion of an arithmetic boundary. Computation of a past-cut boundary never grants a saved source handle or physically executes its counterfactual continuations. The syntax and installation losses of Definition 12.2 still apply.

For unbounded budgets, every positive modulus divides a sufficiently late envelope by (AQBRO.7). If two natural pairs had equal original labels at all those levels, each coordinate difference would be divisible by unbounded integers $E(b)$, forcing that integer difference to be zero. Every finite completed run still admits the preceding distinct source $v+D\alpha$. Hence all-level injectivity does not justify finite termination for exact recovery without a separately supplied finite source bound or certificate. Nor does abstract compatibility alone assert realization by a natural pair; Theorem 15.3 gives a hard-branch counterexample. $\square$

## 15. Cumulative waste of a specified restarting policy

**Definition 15.1 (independent prime restarts).** Fix the following competing strategy solely for this section. On each successive distinct prime request $p_i$, start afresh the exact two-stage fixed-modulus controller used in Theorem 10.2, with the canonical-window directions $K_i,K_i+1$ for that prime. In each scalar stage test digits $0,1,\ldots,p_i-2$ in that order, as in Canonical Window Compiler Geometry, Theorem 1.6. Finish its actual positive closing word after every paid test. Ignore all earlier earned residues when choosing and stopping these tests. There are no interstage external source actions. The current source is nevertheless the actual endpoint of the preceding stage, not a reset or a new entry. This definition fixes a strategy; lower bounds below concern its wasted repeated acquisition.

Write

$$
D_i=\begin{pmatrix}qM^{K_i}\\qM^{K_i+1}\end{pmatrix},
\qquad
Z_i=D_i^{-1}\{-2,-1\}^2\subseteq(\mathbb Z/p_i\mathbb Z)^2
\quad(p_i\ge3).
\tag{AQBRO.9}
$$

The inverse is the existing unimodular consecutive-direction decoder. The four states in $Z_i$ are distinct. Each scalar $-2$ matches the last tested digit $p_i-2$; each scalar $-1$ is the inferred untested digit $p_i-1$. Both cost exactly $p_i-1$ reads under the specified test order. This uses complete gcd answers: the last matching answer is $p_i$, not a clipped failure bit.

**Theorem 15.2 (one actual source realizing every prescribed finite hard prefix).** For any finite distinct odd primes $p_1,\ldots,p_n$ and any recursively chosen $z_i\in Z_i$, there exists one original $v_0\in\mathbb N^2$ on which the restarting strategy enters stage $i$ at residue $z_i$ and uses exactly $2(p_i-1)$ paid reads there, for all $i\le n$ on its single continuous trajectory. The choice of $z_i$ may depend on the already prescribed finite action words of preceding stages. In particular

$$
C_n^{\rm restart}=2\sum_{i=1}^n(p_i-1),\qquad
Q_{\rm ret}\!\left(\prod_{i=1}^np_i\right)=2\max_{i\le n}(p_i-1).
\tag{AQBRO.10}
$$

These ratios are unbounded over finite prime lists and their actual common sources. For every $n$ there are $n$ distinct odd primes in a dyadic interval $(P,2P]$ for which the ratio in (AQBRO.10) exceeds $n/2$. The envelope policy of Theorem 14.1, on that same chosen original pair and request list, retains its bound (AQBRO.6) on its own actual trajectory.

**Proof (the common-source construction).** The scalar test count follows from Definition 15.1 and the actual reset-to-current-residue simulation of Theorem 10.2. Fix $z_i$ at the current stage. Running that finite controller on $z_i$ modulo $p_i$ determines all its replies and actual selected letters, including closing letters. Its hard path costs $2(p_i-1)$. Call the resulting chronological source word $S_i$. It is a definite public word once this prescribed branch is fixed. Let $A_{i-1}=S_1\cdots S_{i-1}$, with its affine coefficients from (AQBRO.3). Its reduction is bijective on $(\mathbb Z/p_i\mathbb Z)^2$, even though its integer action need not be onto $\mathbb N^2$. Prescribe the original congruence

$$
v_0\equiv M^{-k_{i-1}}(z_i-z_{i-1}^{\rm aff})\pmod{p_i},
\qquad
A_{i-1}(v)=M^{k_{i-1}}v+z_{i-1}^{\rm aff}.
\tag{AQBRO.11}
$$

The superscript distinguishes the accumulated affine offset from the chosen hard state $z_i$. All primes are distinct, so ordinary finite integer CRT gives a simultaneous nonnegative representative for each coordinate of $v_0$ modulo $\prod_i p_i$. This is one pair, chosen once. Induction in $i$ now shows that its actual entry to stage $i$ is $z_i$ modulo $p_i$, its genuine replies are precisely the prescribed branch replies, and its actual word is $S_i$. No earlier source is replaced when imposing a later congruence. This proves (AQBRO.10). It combines integer congruences of the same original pair after invertible affine transport, rather than unrelated rational floor reports.

**Proof (arbitrarily many comparable primes).** The elementary Euler argument supplies the required existence without a prime-asymptotic estimate. If $\sum_p1/p$ were finite, then

$$
\prod_{p\le x}(1-1/p)^{-1}
\le\exp\!\left(2\sum_{p\le x}1/p\right)
$$

would remain bounded, since $-\log(1-t)\le2t$ for $0\le t\le1/2$. Expansion of each finite geometric product contains $1/k$ for every $1\le k\le\lfloor x\rfloor$, by prime factorization. The harmonic sums are unbounded, a contradiction. If the numbers of primes in all dyadic intervals $(2^j,2^{j+1}]$ had a common finite bound $N$, their reciprocal sum would instead be bounded by a finite initial part plus $\sum_jN/2^j$, also a contradiction. Thus these counts are unbounded. For each $n$ choose such an interval containing $n$ odd primes, put $P=2^j$, and apply the already proved common-source construction. Then

$$
\frac{\sum_i(p_i-1)}{\max_i(p_i-1)}
\ge\frac{nP}{2P-1}>\frac n2.
\tag{AQBRO.12}
$$

This classical prime argument is an intermediate existence step; the source-specific assertion is the simultaneous actual execution in (AQBRO.11). The policy of Theorem 14.1 is correct on every natural pair and every list under the same variable-port premise, so it also applies to this chosen pair. The two strategies execute different actual words; no equality of endpoints or of their action, memory or service-work costs is asserted. $\square$

**Theorem 15.3 (finite hard realizations need not have an infinite natural source).** There is a sequence of distinct odd primes and recursively prescribed hard states for Definition 15.1 such that every finite prescribed prefix has a single natural-pair realization as in Theorem 15.2, while no $v_0\in\mathbb N^2$ realizes the entire infinite prescription. Equivalently its compatible residue prescriptions define a profinite thread outside the admitted natural-pair source image. Consequently this infinite adversarial thread is not an admissible single-source run, and it cannot prove an all-prefix lower bound on one actual natural pair.

**Proof.** Enumerate $\mathbb N^2$ as $w_1,w_2,\ldots$ by increasing coordinate sum, breaking ties by the first coordinate. Choose distinct odd primes, for example in increasing order. Given the previously prescribed words, compute $A_{i-1}(w_i)\bmod p_i$. The four-element set $Z_i$ contains a $z_i$ different from that residue; choose the lexicographically first such state in nonnegative representatives. Specify its hard branch and actual word $S_i$, and prescribe the original residue by (AQBRO.11). This rule uses only finite integer calculations at each index.

For each finite prefix, Theorem 15.2 gives a natural pair satisfying its congruences. The prescribed original residues are compatible under reduction along the finite products $P_n=\prod_{i\le n}p_i$, by CRT. They also extend to a thread in the usual full profinite pair ring by choosing arbitrary compatible $p_i$-adic lifts and coordinates at unlisted primes; this is a mathematical thread, not a newly supplied source service.

If one natural pair realized every prescribed stage, it would equal $w_j$ for some $j$. Its input to stage $j$ would be $A_{j-1}(w_j)\bmod p_j$, which was deliberately excluded when choosing $z_j$. This contradicts its required hard state. Hence no natural pair realizes the entire prescription, despite realizability of each finite prefix. The quantifiers in Theorem 15.2 are $\forall n\,\exists v_0^{(n)}$, and they have not been exchanged for $\exists v_0\,\forall n$. The construction supplies an explicit unrealizable infinite adversarial thread; it makes no claim that every infinite hard prescription is unrealizable. $\square$

## 16. The resource vector and supplier boundary of the online join

**Theorem 16.1 (the same construction's separate resource coordinates).** Fix a completed finite request prefix of Theorem 14.1, its $J$ actual upgrades and any intervening finite original-action continuations. Write $E_j=E(b_j')$, and use $K_j,\gamma_j,L_{E_j}$ from Definitions 10.1 and (AQBRS.6) at that actual modulus. If $T_{j,0},T_{j,1}$ are its actual scalar-stage test counts and $g_{j,l}$ the graft count in its $l$th short test word, then its acquisition coordinates are exactly

$$
\begin{aligned}
C_n&=\sum_{j=1}^J(T_{j,0}+T_{j,1}),\\
N_R^{\rm acq}&=\sum_{j=1}^J L_{E_j}
       \bigl(K_jT_{j,0}+(K_j+1)T_{j,1}\bigr),\\
N_G^{\rm acq}&=\sum_{j=1}^J E_j\sum_{l=1}^{T_{j,0}+T_{j,1}}g_{j,l},
\qquad T_{j,s}\le b_j',\quad g_{j,l}\le\gamma_j.
\end{aligned}
\tag{AQBRO.13}
$$

Add all actually requested continuation letters to their respective action counts. For total counts $N_R,N_G$, the exact endpoint and quantity bound are the affine-word formula and

$$
u_{\rm end}=M^{N_R}v_0+\sum_{l=1}^{N_G}M^{r_l}\alpha,
\qquad qu\le qu_{\rm end}\le2^{N_R}(qv_0+2N_G),
\tag{AQBRO.14}
$$

where $r_l$ counts replacements after that actual graft. The modulus and residue payload grow independently of the paid-read bound. In particular the following explicit finite bound holds, with $\mathsf h_b=\sum_{k=1}^b1/k$:

$$
\log_2E(b)
\le b\log_2(b+1)\mathsf h_b
\le b\log_2(b+1)(1+\log b)
\quad(b\ge1),
\tag{AQBRO.15}
$$

where the last logarithm is natural. No total-work, action, storage or source-retention ratio follows from (AQBRO.6).

**Proof.** Apply Theorem 11.1 to every actual upgrade, using $B(E_j)=b_j'$. Each is executed at its actual input pair, so its test and closing counts sum exactly as in (AQBRO.13). The endpoint formula and monotonic quantity bound of Theorem 11.1 apply to the concatenated actual action word, including intervening continuations. Nonnegative coordinates persist. The source can grow even though each upgrade closes modulo its own envelope.

For (AQBRO.15), take logarithms of (AQBRO.2), bound the floor by $b/(p-1)$ and $\log_2p$ by $\log_2(b+1)$, and bound the remaining sum over $p-1$ by the harmonic sum over $1,\ldots,b$. The elementary integral bound on that sum gives the last inequality, including $b=1$. This proves a finite bound on the public modulus representation, not a bound on the unknown actual source. Computing the product by enumeration and trial division and producing its binary representation are charged local work. There is no uniform constant bound on these parameter lengths as requests grow.

For a concrete finite record representation let $A=N_R+N_G$ count all completed source letters, let $Q_j=T_{j,0}+T_{j,1}$, let $\ell_j=\lceil\log_2(E_j+1)\rceil$, and let $I$ be the total binary length of the delivered request moduli and retained non-action input/output data. If $F$ past-cut names are retained, with their integer positions, a sufficient local storage bound beyond installed code and service/binding/rights representations is

$$
O\!\left(A+I+\sum_{j=1}^J(Q_j+1)\ell_j
       +F\log_2(A+2)+\max_j\ell_j^2+1\right)\text{ bits}.
\tag{AQBRO.16}
$$

Take the maximum over an empty set to be zero. A binary action tag per actual letter retains the authentic source word; every paid reply is stored with its stage and position, using a sequential merged call tape. Stage delimiters and the public envelope schedule identify the read moduli. Each gcd field fits $\ell_j$ bits. Immutable original and upgrade endpoint labels and public moduli fit the $(Q_j+1)\ell_j$ allowances. The current label uses the latest envelope. Explicit cut positions need the displayed $F$ allowance. The squared workspace allowance covers the existing fixed-modulus preparation of Theorem 11.2 and ordinary modular replay; optional retained outputs are included in $I$.

Theorem 11.2 supplies a finite local-work allowance for every upgrade at modulus $E_j$, and all its public preparation, word compilation and closing-loop control must be paid at that modulus. To transport a new label, replay the already retained $A_s$ at the new precision, reducing both the affine matrix and translation after each letter. Standard binary arithmetic gives a conservative additional $O((A_s+1)(\ell_j+\log_2(A_s+2))^3)$ bit-work bound, plus reading the word and writing the labels. Updating $M^{-k_s}$ letter by letter uses the fixed integer matrix $M^{-1}$, so no exact-real step or hidden original coordinate is involved. A past-cut evaluation replays its authentic prefix and then its supplied hypothetical word, paying for both lengths, modular arithmetic and requested output. Request factoring, envelope formation, future input/output and every tape write/retention are additional actual work. These bounds give finite procedures; they neither suppress repeated replay costs nor infer a computation ratio from the read ratio.

Finally, for actual pre-call states $u_i$ and the actual chosen read modulus $H_i^{\rm call}$, source-service work is exactly

$$
W_{\rm svc}=
 \sum_{i\in\mathcal I_{\rm read}}\rho_{H_i^{\rm call}}(u_i)
 +\sum_{i\in\mathcal I_R}\tau(u_i)
 +\sum_{i\in\mathcal I_G}\gamma_{\rm svc}(u_i).
\tag{AQBRO.17}
$$

All closing letters and subsequent genuine continuations belong to these call sets. Add actual source/backing provision, source storage, binding, rights retention, installed services, local record allocation and their retention costs separately. Finite backing and completion for every chosen finite run remain premises. Keeping finite code and constant read factor supplies neither finite capacity for an unbounded future archive nor lawful service after rights are revoked. $\square$

**Definition 16.2 (source-specific addition and exact suppliers).** The mathematical addition is the uniform common-original archive join of Theorems 13.3–14.1, with the specified restarting separation of Theorems 15.2–15.3 and the same-construction account of Theorem 16.1. Its domain is Assumption 13.1, including its explicitly stronger variable-modulus port menu. These are `repo-derived` conditional ordinary proofs; no new Lean verification or global literature-priority claim is attached to them.

Theorem 10.2 supplies each exact fixed-modulus acquisition-and-return and its positive closing realization. Theorem 10.3 supplies earned synchronized use. Theorems 11.1–11.2 supply the actual letter counts and finite local realization for each acquisition. The [Canonical Window Compiler Geometry, Theorems 1.4–1.6](FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md), supplies the two adjacent directions, short positive words, decoder and hard scalar digit histories. The correspondence in [FARG130–133](FIBONACCI_ATOMIC_RELATION_GENERATION.md) is their antecedent. None is reclassified as a new scalar acquisition, compiler, full-behavior quotient or fixed-modulus lower bound here.

In [`GraftAffineClosure.lean`](../../../D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.lean), the word-affine statement is a component of the public conjunction `D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.result`, quantified over positive $H$, natural graft $w$, words and all natural pairs. Its proof contains a scoped `have wordAffine`; there is no separate public declaration named `GraftAffineClosure.wordAffine`. The substitution $w=\alpha$ and actual recorded chronological word supplies (AQBRO.3); this is affine transport and local inversion on earned operands, not acquisition by a formal inverse map. The original natural pair, actual action history and earned residue are the three matched inputs of the new bridge.

In [`TerminalGcdAcquisitionCost.lean`](../../../D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost.lean), `D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost.costBound` is the maximum $h(p-1)$ over prime-power factors of its fixed argument $H$. The public `terminal_gcd_acquisition_cost (H : ℕ) (hH : 1 ≤ H)` identifies the least finite worst budget in `acquisitionBudgets H` as $0$ for $H=1$ and $2\,\mathrm{costBound}(H)$ otherwise. Its policies query terminal positive words with responses `terminalGcd H`, always at that same $H$. It does not permit a different modulus on each query and therefore supplies no lower bound for arbitrary variable-modulus online or offline policies. The constant four in (AQBRO.6) is an attained comparison to this fixed-modulus benchmark, not an optimality assertion.

Chrobak, Kenyon, Noga and Young, [*Incremental Medians via Online Bidding*, arXiv:cs/0504103v3, Theorem 1 and Section 2](https://arxiv.org/html/cs/0504103v3), attribute the deterministic four and randomized $e$ upper bounds in classical online bidding to folklore and give their proofs. Only the finite geometric payment step is used here. Their randomized proof samples a uniform real logarithmic phase; it is not a finite-random-bit implementation of this source interface, and no randomized strengthening is claimed here. Integer CRT, unimodular inversion, the harmonic/product prime argument and finite affine replay are known intermediate mathematics inside the source-specific proofs, not new standalone results.

The archive has acquired arithmetic data at recorded actual cuts and retained enough genuine action complement to transport those data. It has not constructed the paid gcd backend, supplied a Native/LAB or physical realization, recovered a callable past source, inverted source syntax or a memory installation, or derived a metric or physical clock. In particular its integer-pair congruences do not license CRT combination of separate rational floor reports in [Rooted Boundary History Recovery, Sections 24 and 29–30](RECURSIVE_RELATIONAL_OBSERVATION_ROOTED_BOUNDARY_HISTORY_RECOVERY.md); those sections have their own scale and legal-port contracts. Its finite-prefix and infinite-thread distinction remains consistent with [Effective Resolution, Sections 2.2.5–2.2.8](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_RESOLUTION.md), while Theorem 15.3 adds a hard-branch construction for this actual restarting strategy. The unrestricted four-expression recovery problem retains the missing physical, syntax, whole-memory and universal-resource bridges stated in Definition 12.2.

## 追加锚（本行以下为增补区）
