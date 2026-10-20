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
