# KBonacci endpoint-return costs across all proper narrow widths

## 1. Original reader, joint sources, and the cost contract

This volume gives ordinary mathematical proofs for a restricted family of immutable INITIAL targets. It is reference theory, without Lean compilation or kernel verification. The general objective remains the exact minimum worst-branch emitted-complete-block cost for every attainable INITIAL target and every original order and block width. The family below supplies a global parent-action comparison and a sharp calendar cost; it does not replace that objective.

**定义 1.1（Matched original reader）。** Fix integers $k\ge2$ and $1\le m<k$. Binary words are read from left to right in increasing weight position. A word is legal precisely when it avoids the consecutive subword $1^k$. The original integer weights and value are

$$
G_i=2^i\quad(0\le i<k),\qquad
G_i=\sum_{r=1}^{k}G_{i-r}\quad(i\ge k),\qquad
V_k(w)=\sum_{i<|w|}w_iG_i.
\tag{1.1}
$$

The legal endpoint output is $V_k(w)\bmod2$. Use the matched coefficient interface of [S2, Theorem 14.1]:

$$
T=k+1,\qquad c_i=G_i\bmod2
=\mathbf1_{\{0,T-1\}}(i\bmod T).
\tag{1.2}
$$

Extend $c_i$ periodically to integer indices. Put $g=\gcd(m,T)$, $p=T/g$, and $P=g\mathbb Z/T\mathbb Z$. A legal complete-block endpoint record is $(v,\theta,s)$, where $v\in\mathbb F_2$, $\theta\in P$ is the history length modulo $T$, and $0\le s<k$ is the terminal run of ones. There is also an independent absorbing rejection record $\bot$, whose output differs from both values in $\mathbb F_2$.

The literal bit transitions are

$$
\begin{aligned}
\delta_0(v,\theta,s)&=(v,\theta+1,0),\\
\delta_1(v,\theta,s)&=
\begin{cases}
(v\oplus c_\theta,\theta+1,s+1),&s+1<k,\\
\bot,&s+1=k,
\end{cases}\\
\delta_b(\bot)&=\bot.
\end{aligned}
\tag{1.3}
$$

Intermediate phases in (1.3) belong to $\mathbb Z/T\mathbb Z$. A complete action is exactly $m$ literal bits, executed in order; its endpoint again has phase in $P$. Only the completed action's value or rejection output is observed. Bit transitions define the action, rather than additional observations.

The two original alphabets are $\mathcal A_{\rm all}=\{0,1\}^m$ and the set $\mathcal A_{\rm loc}$ of internally legal $m$-bit words. In this volume $m<k$, so their literal word sets are equal. Cross-block rejection under (1.3) remains present in both. The prior contains all finite actual histories of these complete actions, including the empty history and rejected histories.

**约定 1.2（One joint history for each record）。** The joint-source supplier is [S1, Convention 1.3], also used in [S10, equation (1.7)] and [S15, equation (1.1)]. Here is its applicable construction. For $v\in\mathbb F_2$, $j\in P$, and $0\le s<k$, choose

$$
\ell\equiv0\pmod m,\qquad
\ell\equiv-j\pmod T,\qquad \ell\ge s+2,
\qquad d=\bigoplus_{i=\ell-s}^{\ell-1}c_i,
\tag{1.4}
$$

and take the actual word

$$
w=(v\oplus d)\,0^{\ell-s-1}1^s.
\tag{1.5}
$$

The congruences are compatible because $g\mid j$. Generalized CRT supplies a residue class modulo $\operatorname{lcm}(m,T)$, so arbitrarily large choices of $\ell$ exist. The first factor in (1.5) is one bit. At least one zero separates it from the terminal $s<k$ ones. Thus the word is legal, has length divisible by $m$, and splits into actual internally legal complete blocks. Its first bit contributes $v\oplus d$, its terminal run contributes $d$, and its record is simultaneously $(v,-j,s)$. Different records can use different history lengths; these lengths are not observed by the controller. Rejected histories are actual as well: a complete-block word of all ones with length at least $k$ reaches $\bot$.

Every source used below has this joint interpretation. No proof joins separately attainable value, phase, and tail marginals into a fictitious source.

**定义 1.3（Immutable labels and actual emitted-block fee）。** Let $f$ assign a label to every initial record. The initial value $v$, or the independent initial output $\bot$, is free. A controller subsequently chooses a complete block or stops using only its actual chronological archive of issued blocks and endpoint outputs. A stopping leaf returns $f(q_{\rm INITIAL})$, preserving that label through every destructive transition. Every emitted block costs one, including zero waits and blocks containing padding zeros. The fee is the maximum number of emitted blocks over all initial actual histories.

Write $C_{\rm ad}(f)$ for the least fee among correct adaptive controllers with a uniform finite bound. Write $C_{\rm pre}(f)$ for the least fee when all sources use prefixes of one fixed literal block stream, with endpoint-dependent stopping and decoding still allowed. An initially rejected source returns its separately specified label at fee zero. Both free-value fibres are included. Offline search time and controller memory are separate resources. There is no reset, copy, hidden initial clock, intermediate observation, or combination of different branches' outputs. These are the contracts of [S1, Sections 1–2]; its Proposition 2.3 supplies alphabet equivalence beyond the equal-alphabet range used here.

## 2. The endpoint threshold target and reused interfaces

**定义 2.1（Full-one endpoint target）。** Let $Y$ be a label set and choose $D,E,R,A,L_{\bot}\in Y$ subject only to $D\ne E$. In particular, $R$, $A$, and $L_{\bot}$ may coincide with either endpoint label, with each other, or with neither. Set

$$
H=k-m>0,\qquad j=-\theta_{\rm INITIAL}\pmod T.
$$

For both free initial values, define

$$
f(v,-j,s)=
\begin{cases}
R,&H\le s<k,\\
D,&0\le s<H,\ j=0,\\
E,&0\le s<H,\ j=m,\\
A,&0\le s<H,\ j\in P\setminus\{0,m\},
\end{cases}
\qquad f(\bot)=L_{\bot}.
\tag{2.1}
$$

Both $0$ and $m$ belong to $P$, and they are distinct because $0<m<T$. The outside phase set may be empty. The low-tail endpoint labels are immutable INITIAL labels; after a clearing zero their definition is not reevaluated on the new tail.

**接口 2.2（First-zero loss and literal responses, reused）。** If an $m$-bit block has its first zero after $a<m$ leading ones, an initial tail $s$ survives that prefix exactly when $s+a<k$. For two sources with the same initial value and phase which both survive, the zero makes their current records identical. They remain identical under every subsequent common action. This is the first-zero interface of [S1, Lemmas 4.2–4.3 and Theorem 5.2]; the bound $m<k$ ensures that no remaining internal run can reject a survivor in this one block.

For a successful block $x_0\cdots x_{m-1}$ at absolute block index $t$, its endpoint difference on INITIAL phase $j$ is the literal sum

$$
q_t(j)=\bigoplus_{i=0}^{m-1}x_i c_{-j+tm+i}.
\tag{2.2}
$$

Equivalently, its full phase response on the ordered path $[tm,tm+m]\pmod T$ has charges $x_0$, $x_{i-1}\oplus x_i$ at internal vertex $tm+i$, and $x_{m-1}$ at the right endpoint, and is zero elsewhere. The charges on the full path have even total parity. This is [S10, Interface 2.1; S15, equation (1.3)]. Restriction to the actual subgroup $P$ need not have even parity.

In particular, the root word $1^m$ rejects precisely the tails $s\ge H$. On success its response is

$$
q_0(j)=\mathbf1_{\{0,m\}}(j),
\tag{2.3}
$$

because the two contributions at each internal vertex cancel. A pulse consisting of one literal one at absolute position $i$ has response supported on $\{i,i+1\}\pmod T$. These response interfaces do not supply an optimum for (2.1); legality, acquired archives, and the global comparison of all root actions are proved next.

## 3. Exact all-gcd calendar fee and a common preset stream

**定理 3.1（Endpoint-return cost law）。** For every $k\ge2$, every $1\le m<k$, and every label choice in Definition 2.1, under each original literal alphabet,

$$
C_{\rm ad}(f)=C_{\rm pre}(f)
=N:=\left\lceil\frac{T}{m}\right\rceil
=\left\lceil\frac{k+1}{m}\right\rceil.
\tag{3.1}
$$

One attaining stream, common to both free values, is

$$
\begin{aligned}
B_0&=1^m,\\
B_t&=0^m &&(1\le t\le N-2),\\
B_{N-1}&=0^z1\,0^{m-z-1},
\qquad z=T-1-(N-1)m.
\end{aligned}
\tag{3.2}
$$

Thus exactly $N-2$ complete zero blocks occur between the root and the final pulse; this set is empty when $N=2$. Every wait and every padding position belongs to an emitted complete block.

**证明 3.1。** Fix either free value $v$. All records considered have actual joint histories by Convention 1.2.

First compare every possible root action. The controller cannot stop freely: low-tail sources at phases $0$ and $m$ have distinct labels $D,E$ and the same free value. At least one of those labels, denoted $L$, differs from $R$. At that endpoint phase choose the two initial tails $H-1$ and $H$. Their INITIAL labels are $L$ and $R$. If a proposed root contains a first zero after $a<m$ ones, both sources survive to that zero, since

$$
H+a\le k-m+(m-1)=k-1<k.
\tag{3.3}
$$

They have the same value and phase throughout that prefix, so the zero merges their current records. The rest of the block and every future continuation give them the same archive. No correct leaf can recover their different INITIAL labels. Hence every root containing a zero is excluded, regardless of the remaining bits or adaptive continuation. The only possible root is $1^m$. This argument needs no freshness condition on $R$ or $A$.

The forced root rejects exactly the high tails, all labelled $R$. All lower tails survive. By (2.3), its successful positive-difference archive contains exactly the INITIAL phases $0,m$ with all $0\le s<H$; their current value is $v\oplus1$ and their current tail is $s+m$. This archive retains both labels $D,E$.

Take specifically its two actual sources

$$
q_D=(v,0,H-1),\qquad q_E=(v,-m,H-1).
\tag{3.4}
$$

After the root they share the same endpoint output and the same current tail $k-1$. A correct controller cannot stop at their common archive. If its second block began with one, both would reject at that first bit and thereafter have the same absorbing output forever. Their labels are different, so the second block must begin with zero. This is a restriction on every correct adaptive controller on the positive archive, not an extra observation or a chosen normal form.

Now suppose a correct controller had worst fee $d<N$. With $d=0$ or $d=1$ the preceding common archive already gives a contradiction. For $2\le d<N$, we have

$$
dm\le (N-1)m<T,
\qquad dm-1\le T-2.
\tag{3.5}
$$

In the absolute positions $0,\ldots,T-2$, the source $q_D$ has nonzero coefficients only at position $0$; the source $q_E$ has them only at $m-1,m$. Their forced root has given each exactly one contribution. Position $m$, the next possible distinguishing position, is suppressed by the forced first zero of the second block. At every later position up to $dm-1$ both coefficients are zero. The clearing zero also makes their current tails equal, and any common later bits keep those tails equal. Thus every subsequent successful endpoint output is the same on the two sources; any rejection is common and absorbing as well.

Inductively, at every available endpoint the controller has the same acquired archive on $q_D,q_E$, chooses the same next block or stopping decision, and cannot return their two different INITIAL labels. This excludes all adaptive actions and all early stopping within fee $d$. It proves $C_{\rm ad}(f)\ge N$, and the preset class is a subclass, so $C_{\rm pre}(f)\ge C_{\rm ad}(f)\ge N$. The obstruction is the paid arrival at absolute position $T-1$, not merely the number of endpoint labels.

It remains to prove that (3.2) is an actual legal protocol and decodes the full original prior. Since $(N-1)m<T\le Nm$, its pulse offset satisfies $0\le z<m$. The root succeeds exactly when $s+m<k$, a strict seam condition. For these surviving low tails, the current tail can be as large as $k-1$.

If $N\ge3$, the next block is an emitted $0^m$. Its first zero clears every surviving tail safely; the remaining zero waits are safe, and the current tail before the last block is zero. The final word contains only one one, hence is safe even when $z=0$, since $1<k$.

If $N=2$, there is no intervening block. Here

$$
z=T-1-m=k-m=H\ge1.
\tag{3.6}
$$

The last block therefore begins with at least one zero and clears even the largest surviving tail before its isolated one. It is safe. All complete words in (3.2) are internally legal, and this reasoning checks every cross-block seam. No extra final clearing block is needed because decoding ends at that endpoint.

The root output $\bot$ returns $R$ at fee one. On a successful root, write $b_0=y_1\oplus y_0$. When $b_0=0$, the initial phase lies in $P\setminus\{0,m\}$, so return $A$ immediately at fee one. When $b_0=1$, the acquired archive has only phases $0,m$; continue along (3.2). All zero waits have difference zero and remain charged. The final pulse is at absolute position

$$
(N-1)m+z=T-1.
\tag{3.7}
$$

Its full-phase support is $\{T-1,0\}$. Since $m<k=T-1$, it gives final endpoint difference one on phase $0$ and zero on phase $m$. Return $D$ and $E$, respectively, using the actual difference $y_N\oplus y_{N-1}$. When $g=1$, the other charged phase $T-1$ was excluded on this same root-positive archive. When $g>1$, it is not an actual endpoint phase because $g\nmid T-1$. In either case the literal pulse, rather than an abstract singleton mask, performs the required query.

Every returned label is the original label in (2.1). Equalities among $A,R,L_{\bot},D,E$ do not alter any of these implications. An initially rejected source returns $L_{\bot}$ before any action. Both free values use the same stream and the same successive-difference decoder. Every actual low-tail endpoint source continues for exactly $N$ blocks, while all other legal sources stop after the root. Such endpoint sources exist by (1.4)–(1.5), so the displayed stream's worst fee is exactly $N$. This yields $C_{\rm pre}(f)\le N$ and completes both equalities. ∎

## 4. Boundaries, degeneracies, and the indispensable distinction

**边界 4.1（Width one and the near-critical edge）。** When $m=1$, the fee is $T=k+1$ and the actual stream is one one, $T-2$ paid zeros, and one one. For $k=m+1$ with $m\ge2$, the fee is two and the stream is $1^m\mid010^{m-2}$. The intersection $(k,m)=(2,1)$ instead has fee three and stream $1\mid0\mid1$. Thus the unqualified assertion “$k=m+1$ gives fee two” is false at this intersection; the formula (3.1) includes it.

For the explicit falsifier $(k,m)=(2,1)$, the low-tail sources at indices $0,1$ and tail zero have distinct labels. The root must be one; it gives the same successful value on both and leaves both with tail one. The second bit must be zero, and both outputs remain equal. No two-block adaptive tree can distinguish them, whereas the third bit one separates them. This remains true when $R=D$, $R=E$, or any outside or initial-bottom labels coincide.

**边界 4.2（Divisibility and nontrivial gcd）。** If $m\mid T$, then $N=T/m$, the final informative block index is $T/m-1$, and $z=m-1$. Its pulse is the last bit of that complete block. A possible final tail one is legal and requires no additional fee. The argument never assumes $g=1$ or uses phases outside $P$ as sources. Both indispensable phases $0,m$ are actual for every allowed gcd.

An empty outside branch occurs, for example, throughout $k=2m-1$, $m\ge2$. Then $T=2m$, $g=m$, $P=\{0,m\}$, and the exact fee is two. The outside label $A$ has no low-tail source, but the two low endpoint labels and the high-tail label remain defined as in (2.1). Arbitrary coincidences of the high label with an endpoint label still force the root by choosing the other endpoint.

**边界 4.3（Conditions cannot be dropped）。** The only required label inequality is $D\ne E$. If it is removed and $D=E=A=L$ while $R\ne L$, then $1^m$ alone distinguishes the high tails from every low tail, giving exact fee one. If all labels coincide, the fee is zero. These examples rule out extending (3.1) to coincident endpoint labels. Likewise $m=k$ would give $H=0$ and no low-tail sources at all, so the legal target would be constant $R$ and free. The proper-narrow hypothesis is part of the theorem's domain.

## 5. Suppliers, overlap, and literature scope

The coefficient period, joint-source realization, first-zero loss, literal response geometry, and finite adaptive-tree semantics are supplied interfaces. They are restated to fix their applicable hypotheses, not presented as new mathematical results. The derived result here is Theorem 3.1: the exact calendar fee for the full endpoint-threshold target, with a comparison against every root and adaptive continuation, arbitrary label coincidences, all gcds, and a single safe attaining stream.

| Immutable mathematical supplier | Applicable result and boundary |
| --- | --- |
| [S1: irreversible target acquisition](https://github.com/the-omega-institute/trureturing/blob/f64d9e5dc37301e04ffc33332c919dd56a81ed6f/docs/develop/theory/KBONACCI_IRREVERSIBLE_TARGET_ACQUISITION.md) | Sections 1–2 fix original matched records, the full joint prior, free INITIAL output, and complete-block fees. Convention 1.3 supplies (1.4)–(1.5); Proposition 2.3 gives alphabet equivalence; Lemmas 4.2–4.3 and Theorem 5.2 give first-zero loss and attainability. Theorem 5.2's general protocol bound is not an exact minimum for (2.1). |
| [S2: matched modular observer](https://github.com/the-omega-institute/trureturing/blob/73168b5b84a8ba1328b6fa51eb9d722f3d4a7daa/docs/develop/theory/KBONACCI_MINIMAL_MODULAR_OBSERVER.md) | Sections 13–14 concern the original $\Phi_k=X^k-\sum_{i<k}X^i$ and $V_k\bmod2$; Theorem 14.1 supplies the period $T=k+1$ and coefficients (1.2). Observer state counts and future-window counts are different resources from the emitted-block fee. |
| [S10: narrow query-window costs](https://github.com/the-omega-institute/trureturing/blob/84c05a76262b9b8c1a491c02afdee34e60535e9b/docs/develop/theory/KBONACCI_NARROW_QUERY_WINDOW_COST.md) | Interface 2.1 supplies literal masks and the separate full-one action. Theorem 4.1 assumes a tail-independent phase target and $g\ge2$; it cannot clear the mixed INITIAL tails of (2.1). Theorem 5.1 needs at least three labels among tail-zero indices $0\le j/g<m/g$; this family has at most two there, with its second indispensable endpoint at the excluded right boundary. That wait bound does not supply this optimum. |
| [S13: multilabel prefix and terminal costs](https://github.com/the-omega-institute/trureturing/blob/6850a89acdb12d4f17af57dacee2d67e0b514be4/docs/develop/theory/KBONACCI_MULTILABEL_PREFIX_AND_TERMINAL_COST.md) | The guarded phase laws have coprime phase targets independent of INITIAL tail. Theorem 8.4 concerns one additional block at an already acquired support and known current tail; reaching that support and tail must still be paid. It does not perform the global INITIAL parent comparison in Theorem 3.1. |
| [S15: joint response and seam costs](https://github.com/the-omega-institute/trureturing/blob/3541b57c0d31a89f11fb8b86c75b7b1555e49e6f/docs/develop/theory/KBONACCI_JOINT_RESPONSE_AND_SEAM_COST.md) | Equation (1.3) supplies literal path charges. Section 4 retains the original tails through full-one parents and checks first-zero merging. These composition interfaces are reused; a conditional child's optimum is not automatically a global INITIAL optimum or a common preset stream. |
| [S16: INITIAL calendar capacity](https://github.com/the-omega-institute/trureturing/blob/5c531690b4ee33e642757c8485297e94aba5d9a1/docs/develop/theory/KBONACCI_INITIAL_CALENDAR_CAPACITY.md) | Definition 1.5 and Theorem 2.1 concern tail-independent phase tables, full INITIAL tails, and $k=Qm$, $Q\ge2$. Their nonconstant root starts zero. Capacity over phase tables is not the cost of the mixed-tail endpoint target (2.1), whose root must be all ones. |
| [S17: forced-prefix parity costs](https://github.com/the-omega-institute/trureturing/blob/799d8549ae4d270122eb9a2a42024fdbbbe69459/docs/develop/theory/KBONACCI_FORCED_PREFIX_PARITY_COST.md) | Definition 2.1 assumes $3\le a<m$, $k=Qm$, $Q\ge2$, a nonconstant interior band, and a high label distinct from every low label. Its Theorem 2.2 forces root prefix $1^a0$. The full-block threshold $H=k-m$, different endpoint labels, and arbitrary high-label coincidences in (2.1) are outside those hypotheses. |
| [S18: full-block threshold costs](https://github.com/the-omega-institute/trureturing/blob/f65f9a766bc1380a37a465f99c9cab6090ed06ff/docs/develop/theory/KBONACCI_FULL_BLOCK_THRESHOLD_COST.md) | The base family has $Q\ge2$, $m\ge3$, $k=Qm$, a nonconstant interior table on $\{1,\ldots,m-1\}$, endpoint labels both equal to the outside label, and $R$ distinct from every low-tail label. Its Theorem 2.1 forces a full-one root and a subsequent zero on the root-zero archive. Here the different endpoint labels occupy the root-positive archive, $R$ may coincide with them, and neither width divisibility nor coprimality is assumed. |
| [S19: repeated-band prefix spectrum](https://github.com/the-omega-institute/trureturing/blob/bfc12f8722c6e1409b3eb4a58a6d48d87aa5b644/docs/develop/theory/KBONACCI_PREFIX_LABEL_SPECTRUM_COST.md) | Definition 1.2 and the exact prefix-spectrum law concern the same repeated interior band with $Q\ge2$, $m\ge3$, $k=Qm$ and fresh high label. They retain equal low-tail labels at $0,m$. The target (2.1) is not a specialization of that table. No unused provenance claim or finite producer check from that supplier is needed here. |

The current declaration comparison uses the immutable repository snapshot [0027a5558981ea193ed97f68f3207c5613c02461](https://github.com/the-omega-institute/trureturing/tree/0027a5558981ea193ed97f68f3207c5613c02461). In its `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/` family, `LiteralModel.joint_history_realization`, `EndpointCells.all_one_archive_exact`, `EndpointCells.first_zero_block_exact`, and `FirstZeroRecursion.first_zero_necessity`/`first_zero_sufficiency` supply the corresponding realization and loss interfaces. `KBonacciIrreversibleAcquisition.whole_first_zero_acquisition` supplies classification and a general bounded protocol. `NarrowWindowCost.narrow_window_cost` assumes $g\ge2$ and monochromatic windows for a tail-independent phase table; `OriginalNarrowCost.original_cost_lower` has the three-label first-window condition described above. `KBonacciActualEndpointOperators.actual_endpoint_operators` classifies actual tail operators and strict seams, rather than INITIAL-label calendar minima. Public statements and their internal proof helpers were examined in these named modules; no exact endpoint-target cost statement was found within this comparison. Reading their source is not a compilation claim.

The upstream comparison is pinned to mathlib commit [db584cd6d46c92f209a44c0f1c829460d327499d](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d), the dependency revision in this snapshot. Its `Mathlib/Computability/DFA.lean`, `Mathlib/Computability/Language.lean`, `Mathlib/Data/Nat/ModEq.lean`, and `Mathlib/Data/Nat/GCD/Basic.lean` provide deterministic word semantics and arithmetic interfaces, not this source-specific fee theorem. This is a targeted comparison of pinned upstream sources, not an exhaustive absence assertion about mathlib or other Lean libraries.

| Primary literature | Exact correspondence and limit |
| --- | --- |
| Edward F. Moore, *Gedanken-Experiments on Sequential Machines*, in *Automata Studies*, 1956, pp.129–153, [primary text](https://www.cs.cmu.edu/~cdm/resources/Moore1956-gedanken-experiments.pdf) | `literature-attested`: pp.129–130 define a simple experiment whose inputs may depend on prior outputs and whose conclusion depends on its outcome. The multiple experiment separately permits copies and is not used here. Page 131 describes irreversible information loss through an absorbing destroyed state. These supply experiment semantics, not the KBonacci calendar minimum. |
| Petra van den Bos and Frits Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2](https://arxiv.org/pdf/1907.11034v2), pp.10–12, Definitions 12, 14, 17, 20 and Figure 3 | `literature-attested`: finite acyclic tests, inputs compatible with every current candidate, disjoint completed observations, and adaptive distinguishing graphs. The complete deterministic endpoint machine here is a specialization: its input is a whole block and its output is the following endpoint, with a separate free initial reading. We require separation only of different INITIAL labels. The generic example of destructive first actions is reused as a principle; the all-action forced root and absolute-position obstruction in Proof 3.1 are proved for this reader. |
| Uraz Cengiz Türker, Robert M. Hierons, Mohammad Reza Mousavi and Khaled El-Fakih, *Efficient State Identification for Finite State Machine-Based Testing*, DOI [10.1109/TSE.2025.3604472](https://doi.org/10.1109/TSE.2025.3604472), [accepted manuscript](https://eprints.whiterose.ac.uk/id/eprint/230260/1/Ordered_Wset_Accepted.pdf), Definitions 11–15 and 18 | `literature-attested`: a state-identifying path applies a characterising word at a specified state; identification paths cover every state/word pair from the specified start. Definition 13 excludes additional transfer strings, Definition 14 requires pairwise shortest separating prefixes, Definition 15 combines these into an ordered characterising set, and Definition 18 bounds total transfer length. The accepted PDF has SHA256 `a20067072d7349615f42c05ad7b431de04389c035b81f2388d779230dc906c7a`. Transfer-free paths are present and are not described as reset-dependent. Their specified-start coverage and pairwise minimality do not establish the minimum worst branch for an unknown INITIAL label; no fee-preserving equivalence is asserted. |

Theorem 3.1 is `repo-derived`: its universal claim is carried by its ordinary proof. The comparison covers the named reader, narrow-mask, first-zero, repeated-band, deterministic-word, adaptive-test, and ordered-characterising-path sources. It gives neither exhaustive absence nor mathematical priority. No generic Bellman recurrence, source-encoding length, renamed supplier bound, or isolated finite table is presented as the new result.

## 6. Finite actual-transition and literal-tree checks

**数据 6.1（Integer sources and the emitted preset protocol）。** For every $2\le k\le18$ and every $1\le m<k$, all 153 parameter pairs were checked. Original integer weights (1.1) were generated directly and their parity compared with (1.2). For both free values, each actual phase in $P$, and every $0\le s<k$, one history (1.4)–(1.5) was constructed and evaluated as a literal integer-weight word. All 46,392 joint histories had the specified value, phase, and tail.

The preset protocol was executed on each history with actual early stopping after the root on rejection and outside phases. A separate integer sum and forbidden-run scanner were compared with the bitwise record transitions only at the actually emitted block endpoints: 63,764 comparisons. INITIAL labels were retained separately from the changing current records. All 37 equality partitions of $(D,E,R,A,L_{\bot})$ with $D\ne E$ were used, giving 1,716,504 legal-source/label cases and 2,359,268 actual paid blocks. Every label was correct and each low endpoint source paid exactly $N$. Actual rejected histories and absorption under either next bit were checked; their 5,661 parameter/label cases stopped freely with $L_{\bot}$.

The parameter range contains 17 width-one pairs, 40 pairs with $m\mid T$, 52 with nontrivial gcd, eight with empty outside support, 17 with $k=m+1$, and 113 with $m\nmid k$. The case $(2,1)$ gives the explicit two-block falsifier in Boundary 4.1. These counters overlap and are not disjoint classes.

**数据 6.2（All-action structural and cheaper-budget checks）。** For $2\le k\le9$ and all $1\le m<k$, every literal root containing a zero was tested on the same-phase actual tails $H-1,H$ at each endpoint, for both free values: 3,872 merging-pair checks. Every proposed second block beginning with one was tested on the two endpoint sources of INITIAL tail $H-1$ after the full-one root: 1,004 common-absorption checks. These action checks keep rejection independent of the two scalar values.

An independently implemented bounded literal-action-tree search used every $m$-bit word and every endpoint reply for $2\le k\le7$ and all $1\le m<k$, giving 21 parameter pairs. It retained an immutable label attached to each changing current record, allowed stopping only at a single-label node, and kept constant-output actions as paid transitions. Same-current-record collisions between different labels were rejected as irreversible. No root action, leading bit, waiting stream, query mask, or cost formula from Theorem 3.1 was imposed on the search.

The ten different legal-source equality patterns of $(D,E,R,A)$ were checked on both free values, for 420 cases; initial-bottom labels were separately free. Every budget from zero through $N$ was decided, giving 1,840 budget decisions and 10,157 cached bounded nodes. The first successful budget was $N$ in every case. The search-produced actual action trees were also executed source by source, with 12,040 source executions and 19,120 emitted blocks, returning all INITIAL labels correctly. There were no cheaper-budget falsifiers in this finite range. The two alphabets are the same literal set here, and their common cross-block seams were checked on every execution.

These are finite regression results. They do not prove an unbounded formula, certify another producer, or settle any target outside (2.1). The universal claim uses Proof 3.1. No finite result is used to infer an exhaustive literature gap, kernel truth, or independent approval.

## 7. Remaining exact-cost objective

**开放问题 7.1（All parameters and arbitrary attainable INITIAL targets）。** The full objective is still the exact minimum worst-branch actual emitted-complete-block fee for every attainable INITIAL record target, for every $k\ge2,m\ge1$, with the original matched scalar, all joint actual histories, endpoint-only archives, and independent absorbing rejection. Theorem 3.1 handles (2.1) for every proper narrow width and gcd. It does not determine costs for several different outside labels, arbitrary low-phase supports, multiple mixed-tail thresholds, longer full-one parent prefixes, general repeated reactivation, or the remaining non-narrow widths.

The useful bridge is a complete global parent obstruction even when the high-tail label coincides with a low label, followed by a lower bound that combines a destructive seam obligation with actual calendar silence. A continuation optimum on a favourable support cannot supply the full objective until every competing parent, every successful INITIAL-tail merging fibre, every absorbing rejection label, and every paid arrival are included. For arbitrary targets these obligations and a common attaining protocol remain to be solved. The unchanged broad objective therefore remains open.

## 追加锚（本行以下为增补区）
