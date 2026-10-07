# KBonacci INITIAL-target acquisition costs: spectrum, endpoint return, and two thresholds

This volume studies one resource: the minimum worst-branch number of actual emitted complete blocks needed to return a label of an immutable INITIAL record. It integrates the repeated-band spectrum and simultaneous endpoint refinement of [S19] with the proper-narrow endpoint-return law of [S20], then develops the two-threshold arbitrary-table frontier. Each result keeps its own hypotheses. A response mask is used only through its literal inverse and a strict seam check; independently optimal adaptive children are never presumed to form one preset stream.

This is ordinary mathematical reference theory. Its source interfaces and the two integrated results are credited reuse; the two-threshold classification is a deduction on those interfaces. The exact cost for every arbitrary attainable INITIAL target and every $k,m$ remains open.

Only results, constructions, mathematical boundaries, and source citations appear below.

## 1. One reader, one joint prior, and one fee

**定义 1.1（Original matched reader）。** Fix $k\ge2$ and a complete block width $m\ge1$. The original integer weights are

$$
G_i=2^i\quad(0\le i<k),\qquad
G_i=\sum_{h=1}^kG_{i-h}\quad(i\ge k),\qquad
V_k(w)=\sum_{i<|w|}w_iG_i.
$$

Bits are read in increasing weight position. Legal words avoid $1^k$. The matched mod-two coefficient interface [S2] (Theorem 14.1) is

$$
T=k+1,\qquad c_i=G_i\bmod2=\mathbf1_{\{0,T-1\}}(i\bmod T).
\tag{1.1}
$$

Extend $c_i$ periodically to integer indices. Put $g=\gcd(m,T)$, $p=T/g$, and $P=g\mathbb Z/T\mathbb Z$. At complete-block endpoints the successful record is $(v,\theta,s)$ with $v\in\mathbb F_2$, $\theta\in P$, and $0\le s<k$. There is a separate absorbing rejection record $\bot$; its output differs from both scalar values. Literal bit updates are

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
\tag{1.2}
$$

Intermediate phases in this definition are ambient residues modulo $T$. A complete action consists of exactly $m$ literal bits and returns an endpoint phase in $P$. Bit updates define the operation, without supplying intermediate observations. The prior includes all finite actual complete-block histories, including the empty and rejected histories.

The original alphabets are all $m$-bit words and the internally legal $m$-bit words. All proved fee laws here have $m<k$, so these alphabets have the same literal words; cross-block rejection is still checked. This does not replace the broader alphabet-equivalence interface [S1] (Proposition 2.3).

**约定 1.2（Joint actual sources）。** Write $j=-\theta_{\rm INITIAL}\pmod T$. For any $v\in\mathbb F_2$, $j\in P$, and $0\le s<k$, choose

$$
\ell\equiv0\pmod m,\qquad \ell\equiv-j\pmod T,\qquad \ell\ge s+2,
\qquad d=\bigoplus_{i=\ell-s}^{\ell-1}c_i.
$$

One legal history realizing the entire record simultaneously is

$$
w(v,j,s)=(v\oplus d)\,0^{\ell-s-1}1^s.
\tag{1.3}
$$

The first factor is one bit. Generalized CRT applies because $g\mid j$, and permits arbitrarily large $\ell$. A separating zero prevents the first bit from joining the terminal run $s<k$. The first bit contributes $v\oplus d$ and the terminal run contributes $d$, giving exactly $(v,-j,s)$. Its length is divisible by $m$, so it is one actual complete-block history under either alphabet when $m<k$. In the proper-narrow range used below, an all-one complete-block history of length at least $k$ realizes $\bot$. These are the joint witnesses of [S1] (Convention 1.3; S15, Section 1), rather than a product of separately reachable marginals. History lengths are unobserved and may differ; they are not part of the archive.

**定义 1.3（INITIAL labels and control costs）。** A target $f$ labels the initial record. The free initial reading reveals $v$ or $\bot$. Subsequent observations occur only at emitted complete-block endpoints. Every issued block costs one, including zero waits and padding blocks. A controller retains its own chronological issued-block/output archive and must return $f(q_{\rm INITIAL})$; it never reevaluates the target on the current record.

Let $C_{\rm ad}(f)$ be the least worst-branch fee of a correct adaptive controller with a uniform finite bound. Let $C_{\rm pre}(f)$ require all sources to follow prefixes of one fixed literal stream, while stopping and decoding may depend on their endpoint archive. Both free-value fibres count; initial $\bot$ returns its arbitrary independent label at fee zero. Thus $C_{\rm ad}\le C_{\rm pre}$. Offline search and controller memory are different resources. There is no reset, copied source, hidden initial clock, intermediate observation, or borrowed observation from another branch.

**接口 1.4（Literal charges and first-zero loss, reused）。** In the proper-narrow range, set $u_t=tm\pmod T$, where index $t=0$ is the first issued block, and retain the ordered path

$$
W_t=[u_t,u_t+m]\pmod T.
$$

A successful literal block $x_0\cdots x_{m-1}$ has endpoint difference

$$
q_t(j)=\bigoplus_{i=0}^{m-1}x_i c_{-j+tm+i}.
$$

Its path charges are

$$
\begin{aligned}
q_t(u_t)&=x_0,\\
q_t(u_t+i)&=x_{i-1}\oplus x_i\quad(1\le i<m),\\
q_t(u_t+m)&=x_{m-1},\\
q_t(j)&=0\quad(j\notin W_t).
\end{aligned}
\tag{1.4}
$$

The full path has even total charge. Conversely an even support $E\subseteq W_t$ gives the unique actual word

$$
\mathcal B_t(E)_i=\bigoplus_{h=0}^i\mathbf1_E(u_t+h),\qquad 0\le i<m.
\tag{1.5}
$$

More generally the same formula inverts any even binary charge assignment. The path is traversed in the indicated order, including a wrap. These interfaces are [S10] (Interface 2.1; S15, Section 1). Restriction to $P$ need not have even parity: nonactual vertices may supply compensation without becoming sources. Every use of (1.5) still requires a tail and seam proof.

If the first zero occurs after $b<m$ leading ones, a source survives that prefix precisely when $s+b<k$. Any two surviving sources with the same value and phase merge at that zero, because their tails are both cleared. Their different INITIAL labels cannot subsequently be recovered from a common archive. This is the first-zero interface [S1] (Lemmas 4.2–4.3 and Theorem 5.2). Because $m<k$, no internally later run in this block rejects a surviving source. In particular, $1^m$ rejects exactly $s\ge k-m$ and has successful charge support $\{0,m\}$.

## 2. Endpoint return across every proper narrow width

This chapter preserves [S20] (Definitions 1.1, 1.3, 2.1 and Theorem 3.1) in the common model. Only the endpoint inequality is required; freshness is not added.

**定义 2.1（Endpoint threshold target）。** For any $k\ge2$ and $1\le m<k$, put $b=k-m>0$. Choose labels $D,E,R,A,L_\bot$ subject solely to $D\ne E$. On both free-value fibres set

$$
f_{\rm end}(v,-j,s)=
\begin{cases}
R,&s\ge b,\\
D,&s<b,\ j=0,\\
E,&s<b,\ j=m,\\
A,&s<b,\ j\in P\setminus\{0,m\},
\end{cases}
\qquad f_{\rm end}(\bot)=L_\bot.
\tag{2.1}
$$

The two endpoint phases are actual and distinct. The outside support can be empty. Every other label coincidence, including a high label equal to an endpoint label, is permitted.

**定理 2.2（Credited endpoint-return law）。** Under Definition 2.1, for both original alphabets,

$$
C_{\rm ad}(f_{\rm end})=C_{\rm pre}(f_{\rm end})
=N=\left\lceil\frac{k+1}{m}\right\rceil.
\tag{2.2}
$$

A common attaining stream is

$$
B_0=1^m,\qquad B_t=0^m\ (1\le t\le N-2),\qquad
B_{N-1}=0^z1\,0^{m-z-1},\qquad z=k-(N-1)m.
\tag{2.3}
$$

Proof. Fix a free value. The low endpoint labels differ, so the root cannot stop. At least one of $D,E$ differs from $R$; choose that endpoint and its two actual initial tails $b-1,b$. A root containing a zero after $u<m$ ones lets both survive, since $b+u\le k-1$. It merges their records while their INITIAL labels differ. Thus every correct root, including one with arbitrary later adaptive continuation, must be $1^m$.

That root rejects the high tails and returns $R$. On success it puts precisely the phases $0,m$ in its positive-difference archive and all outside phases in its zero-difference archive. In the positive archive choose the sources $(v,0,b-1)$ and $(v,-m,b-1)$. Both now have tail $k-1$ and equal observed value $v\oplus1$. A second word beginning with one sends both to absorbing rejection, so every correct second word on this archive starts zero.

Suppose a correct adaptive controller stopped within a worst fee $d<N$. Beyond the root and up to absolute position $dm-1\le T-2$, the phase-zero source has nonzero coefficients only at position zero. The phase-$m$ source has them at positions $m-1,m$. The root contributed once to each, and the required second-block first zero suppresses position $m$. All later coefficients in that interval are zero for both. That clearing zero makes their current tails common; later rejection is also common. Their acquired archives therefore remain identical, inductively forcing the same actions and stopping decision on both sources. Distinct INITIAL labels cannot be returned. This rules out every adaptive controller of fee $d<N$, including arbitrary paid waits, and proves the lower bound $N$.

For the upper bound, $(N-1)m<T\le Nm$ gives $0\le z<m$. If $N\ge3$, the first paid zero wait clears every surviving root tail, and the final isolated one is safe from tail zero. If $N=2$, then $z=k-m=b\ge1$, so the last block itself starts zero and clears even tail $k-1$. All seams are strict; an isolated one cannot contain $1^k$. No extra final cleanup is needed.

The root-reject archive returns $R$ at fee one. Its successful zero-difference archive returns $A$ at fee one. Its positive archive continues through every charged wait. The final pulse is at absolute position $(N-1)m+z=T-1$ and has support $\{T-1,0\}$. Hence its last endpoint difference is one on phase zero and zero on phase $m$, returning $D,E$. If $g=1$, phase $T-1$ was excluded on this same positive archive; if $g>1$, it is not actual at all. Thus a literal pulse realizes the distinction. Both free values use successive differences of their own outputs. Actual low endpoint sources exist and pay exactly $N$, giving the stated worst fee. The arbitrary coincidences in (2.1) do not change these leaves. ∎

**边界 2.3（Width, divisibility, and equality）。** Width one costs $T$: the stream is one one, $T-2$ paid zeros, and one one. If $k=m+1$ and $m\ge2$, it costs two with stream $1^m\mid010^{m-2}$. At $(k,m)=(2,1)$ it instead costs three, with $1\mid0\mid1$. Here the two low endpoint sources at tail zero survive the first one with common tail one, must both take zero next, and are still indistinguishable until the third bit. This falsifies a fee-two claim at that intersection, even with high-label coincidences.

If $m\mid T$, the pulse offset is $m-1$; its final tail one is legal and does not require another block. Nontrivial gcd is allowed throughout. At $k=2m-1$, $m\ge2$, one has $P=\{0,m\}$ and no outside low source, yet the endpoint fee is two. The root is still forced even if $R$ equals an endpoint label, by using the other endpoint.

The hypothesis $D\ne E$ is indispensable. If $D=E=A=L$ and $R\ne L$, one full-one root costs exactly one; if all labels also equal $R$, the fee is zero. With $m=k$, there are no low tails and the legal target is constant $R$, so the proper-narrow condition is indispensable as well.

## 3. Repeated-band spectrum and simultaneous fresh endpoints

This chapter integrates [S19] (Definitions 1.1–1.2, 2.1 and Theorems 3.1, 4.1). The literal calendar and every code row are included because the common stream is part of the result.

**定义 3.1（Band labels and spectrum）。** Restrict to $Q\ge2$, $m\ge3$, $k=Qm$, and $T=Qm+1$. Then $g=1$ and all phases are actual. Set $I=\{1,\ldots,m-1\}$, take an arbitrary nonconstant table $\lambda:I\to Y$, an outside label $A$, and a fresh high label $R\notin\{A\}\cup\lambda[I]$. Band labels may repeat in arbitrary order, and $A$ may be a band label. Define

$$
f_{\rm band}(v,-j,s)=
\begin{cases}
R,&s\ge k-m,\\
\lambda(j),&s<k-m,\ j\in I,\\
A,&s<k-m,\ j\notin I,
\end{cases}
\qquad f_{\rm band}(\bot)=L_\bot.
\tag{3.1}
$$

For $1\le t\le m-1$, count distinct labels, not occurrences:

$$
n_t=\left|\lambda[\{1,\ldots,m-t\}]\right|,
\qquad
h=\min\{r\in\{1,\ldots,m-2\}:n_{r+1}\le2^r\},
$$
$$
e=\mathbf1_{\{n_h>2^h\ \text{or}\ (Q=2,\ m\text{ odd},\ h=1,\ A\notin\lambda[I])\}}.
\tag{3.2}
$$

The minimum exists because $n_{m-1}=1$. Also $n_h>2^{h-1}$: for $h>1$ this follows from minimality, and for $h=1$ from nonconstancy. If $n_h>2^h$, removal of one phase gives $n_h=2^h+1$ and $n_{h+1}=2^h$; the removed phase has a label absent from that shorter prefix.

**定理 3.2（Credited arbitrary repeated-band spectrum law）。** With exactly the hypotheses of Definition 3.1,

$$
C_{\rm ad}(f_{\rm band})=C_{\rm pre}(f_{\rm band})=hQ+1+e.
\tag{3.3}
$$

Proof. At any fixed value and phase, the actual tails $k-m-1,k-m$ have different labels. First-zero loss excludes every root containing a zero, so the root is $1^m$. It rejects the high band, has response support $\{0,m\}$, and places all of $I$ in its zero-difference child. Two distinct band labels at initial tail $k-m-1$ now have current tail $k-1$. A second word starting one would merge them in rejection, so the root-zero child must next issue a word starting zero. This makes the current tail common. Thereafter, within any acquired archive, current value and tail are common; a rejecting action merges the whole archive and supplies no useful extra leaf at a nonconstant node. Useful later observations are binary successful endpoint differences.

The calendar is

$$
W_{rQ+b}=[bm-r,(b+1)m-r]\pmod T,\qquad 0\le b<Q,
\tag{3.4}
$$

since $Qm\equiv-1\pmod T$. Restrict to actual sources at one free value, initial tail zero, and phases $K_h=\{1,\ldots,m-h\}$. Before total fee $hQ+1$, only indices $Q,2Q,\ldots,(h-1)Q$ can inform that prefix. Indeed a non-main index $rQ+b$ with $b\ge1$ and $r\le h-1$ has left endpoint at least $m-h+1$ and right endpoint at most $k-r<T$, so misses the prefix without a wrap. The root also misses it. Thus fee $hQ$ permits at most $h-1$ binary opportunities and $2^{h-1}$ distinct-label leaves, fewer than $n_h$. The next main index $hQ$ increases capacity to at most $2^h$; if $n_h>2^h$, another paid block is necessary. These counts concern sources on their own adaptive paths, without mixing branches or requiring equal labels to have equal codes.

For the remaining surcharge condition, $Q=2$, $m$ odd, $h=1$, and fresh outside $A$, the supplied first-tour boundary [S18] (Theorem 2.1) says at least one outside source remains on the band archive after two blocks. If the band already has more than two labels, the preceding capacity bound applies. Otherwise its two labels and fresh $A$ give three labels with common current value and tail, which one further binary endpoint cannot distinguish. Therefore the lower bound in every case is $hQ+1+e$.

For attainment define

$$
p_*=h-1+e,\qquad n=m-h-e,\qquad K=\{1,\ldots,n\},\qquad H_r=m-r\ (1\le r\le p_*).
\tag{3.5}
$$

The core is nonempty and has at most $2^h$ labels. Choose an injective code $c:\lambda[K]\to\{0,1\}^h$. Individual frontier phases $H_r$ may share labels with each other or the core; their distinct codes are allowed to decode to the same label.

First screen the outside phases using the actual [S18] scan. Let $Z_m$ be the alternating length-$m$ word starting zero and $O_m$ the one starting one. Issue root $1^m$. If $m$ is even, indices $1,\ldots,Q-1$ issue $Z_m$. If $m$ is odd and $Q\ge3$, index one uses $Z_m$ and the later first-tour indices use $O_m$. The continuing zero-difference root-zero archive is exactly $I$, and every scan-positive archive has label $A$ and stops. These charge supports can also be read directly from (1.4): even-width $Z_m$ covers each scan window except its left endpoint; odd-width $Z_m$ covers its interior, and subsequent $O_m$ covers its entire window. Together they exclude every actual outsider, including $k$.

The exceptional scan $Q=2$, $m$ odd, uses instead

$$
Z'_m=00(10)^{(m-3)/2}1.
\tag{3.6}
$$

Its support is $\{m+2,\ldots,2m\}$; hence the continuing archive is $I\cup\{z\}$ with $z=m+1$, and phases $0,m,k$ are excluded. The only extra source $z$ has label $A$. The first scan starts zero and safely clears every root survivor, including tail $k-1$. Subsequent alternating scans have tails at most one and strict seams.

If this exceptional scan has $p_*=0$, then $h=1,e=0$, the band has exactly two labels, and $A$ is one of them. Assign core code $c(A)=0$ and the other label code one. The extra source will correctly share $A$'s zero code.

For $1\le r\le h$, put $F_r=\{j\in K:c_r(\lambda(j))=1\}$. At the first main index $Q$, set

$$
L_1=F_1\cup\{0\}\cup
\begin{cases}
\{H_1\},&Q=2,\ m\text{ odd},\ p_*\ge1,\\
\varnothing,&\text{otherwise},
\end{cases}
\qquad
E_Q=L_1\cup
\begin{cases}
\{k\},&|L_1|\text{ odd},\\
\varnothing,&|L_1|\text{ even}.
\end{cases}
\tag{3.7}
$$

These vertices lie in $W_Q=[k,0,1,\ldots,m-1]$. Compensation at $k$ is valid on the continuing archive; its assigned charge only completes full-path parity. Phase zero is deliberately given response one. For $2\le r\le h$, use

$$
E_{rQ}=F_r\cup
\begin{cases}
\{0\},&|F_r|\text{ odd},\\
\varnothing,&|F_r|\text{ even}.
\end{cases}
\tag{3.8}
$$

The core lies in every main window $[-r,m-r]$ because $n\le m-h\le m-r$; phase zero is absent from the continuing root-zero archive and available for compensation. The left endpoint $-r$ is unselected. Emit the actual inverses (1.5), not abstract support combinations.

At each frontier index $rQ+1$, $1\le r\le p_*$, use

$$
E_{rQ+1}=
\begin{cases}
\{H_1,z\},&Q=2,\ m\text{ odd},\ r=1,\\
\{H_r,m\},&\text{otherwise}.
\end{cases}
\tag{3.9}
$$

Each is even and belongs to $[m-r,2m-r]$. Ordinary rows are the literal $1^r0^{m-r}$; phase $m$ was excluded by the root. The exceptional row is $110^{m-2}$ and selects both actual sources $H_1,z$, with no claim that $z$ is an absent donor. Every unmentioned index is an issued, paid $0^m$ wait.

The decoder retains the $h$ main coordinates and $p_*$ frontier coordinates in their actual chronological archive. A core label $y$ has code $(c(y),0^{p_*})$. An ordinary frontier phase $H_r$ has main code zero and frontier unit vector $r$, distinct from every core code and every other frontier phase. The core is strictly below all frontier windows, because its largest phase is $m-h-e$ and the smallest frontier endpoint is $m-p_*=m-h+1-e$. Other frontier phases receive prescribed zero at row $r$.

In the exceptional case with $p_*\ge1$, $z$ and $H_1$ share frontier coordinate one but have first main coordinates zero and one respectively by (3.7). Later main responses of both are zero: $H_1$ lies above the nonnegative right endpoints and $z$ lies between those right endpoints and the wrapped segment, whose least residue is $T-h\ge m+3$. Later frontier responses of both are prescribed zero. They therefore have distinct codes, neither sharing a core or another frontier code. Decode them to $A$ and $\lambda(H_1)$. This works with every allowed outside coincidence. If $p_*=0$, the special code convention already handles $z$. Every acquired code has a unique INITIAL label even when one label has several codes.

For seams, the first main word has charge one at its second path vertex zero, so either its first bit is zero or its second bit is zero. Its leading run is at most one and its terminal run at most $m-1$. Each later main starts zero. Ordinary frontier words have leading run $r\le p_*\le m-2$ and terminal run zero; the exceptional row has leading run two and terminal run zero. Every post-scan word contains zero. General adjacent leading/terminal runs sum to at most $2m-2<k=Qm$; specifically the exceptional leading two after a main tail is at most $m+1<2m\le k$. Zero waits safely clear tails. The scan-to-first-main seam is safe from tail at most one. No extra terminal clearing block is issued.

The last index is $hQ$ for $e=0$ or $hQ+1$ for $e=1$. Thus the stream pays at most $hQ+1+e$, including every intervening wait. Root rejection returns $R$; successful root-positive sources return $A$ at fee one; scan-positive sources return $A$ at that endpoint; remaining sources decode as above. Initial rejection stops free. The same stream and differences work for both free values. Combined with the adaptive lower bound, this proves (3.3). ∎

**定理 3.3（Credited simultaneous fresh-endpoint refinement）。** In Definition 3.1 choose $D,E$ distinct from one another and from $\{R,A\}\cup\lambda[I]$. Replace only the low-tail labels at $j=0,m$ by $D,E$ respectively, obtaining $f_{\rm band}^{D,E}$. Then

$$
C_{\rm ad}(f_{\rm band}^{D,E})=C_{\rm pre}(f_{\rm band}^{D,E})=hQ+1+e.
\tag{3.10}
$$

Proof. On the legal INITIAL-record fibres, coarsen $D,E$ to $A$ and fix every other legal label; freshness makes this label map well-defined. Keep the separately observed initial-bottom leaf at $L_\bot$, even if $L_\bot=D$ or $E$, rather than applying the legal-fibre map there. This recovers (3.1) on every initial record. Decoding any refined protocol according to its free initial reading therefore yields an unrefined one with the same actions and no greater fee, giving the lower bound. This argument alone supplies no preset upper bound.

For that upper bound use the very same stream (3.6)–(3.9) and its ordinary scan alternatives. The root-zero child contains neither endpoint and keeps the preceding decoder unchanged. The root-positive child is exactly $\{0,m\}$ with low tails and labels $D,E$. Its first scan begins zero, so it is safe even at tail $k-1$. At index one phase $m$ has zero response, and phase zero is outside the window. All later first-tour windows miss both. The endpoint child therefore reaches the first main index $Q$ without any distinguishing response. At that main word, (3.7) assigns response one at phase zero, while phase $m$ lies outside the window. The two labels are returned at total fee $Q+1$.

Phase zero is a real source on this child and is deliberately queried, not treated as absent. The compensation at $k$ is absent on both continuing children: the root excluded it from the endpoint child and the scan from the other child. Its possible first bit one is followed by zero, preserving safety. Later main compensation at zero is allowed because the endpoint child has already stopped. Thus one actual common stream serves both children.

If $Q=2$, $m$ odd, $h=1$, and $A$ is a band label, the no-frontier code convention still decodes $z$ while this same main word separates $D,E$. With fresh $A$, $e=1$ supplies the frontier row, and the endpoint child has already stopped. If $h\ge2$, that frontier row already exists and needs no extra tour. Every continuing branch follows one stream prefix; all paid waits and strict seams are those already checked. Both values and free initial rejection remain covered. ∎

**边界 3.4（Small widths, limiting spectra, and arrangement）。** At $m=3$, $h=1$. For $Q=2$ and fresh $A$, $e=1$, the core is $\{1\}$ and the frontier row separates $H_1=2$ from $z=4$. With $A$ a band label, $e=0$ and its zero code applies. For $Q\ge3$ the ordinary scan removes every outsider. At $h=m-2$, one still has $n=m-h-e\ge1$ and $p_*\le m-2$, so all windows, compensation vertices, and seams retain their stated domains.

For $m=12$ and any $Q\ge2$, the bands

$$
(B,B,B,C,C,C,L,L,L,U,V),\qquad
(U,V,B,B,B,C,C,C,L,L,L)
\tag{3.11}
$$

have the same label multiplicities $(3,3,3,1,1)$ but costs $2Q+1$ and $3Q+1$. The first has $n_2=4,n_3=3$ and $h=2,e=0$; the second has $n_2=n_3=5,n_4=4$ and $h=3,e=0$. These hold for every allowed $A$. In the second, the label $L$ appears in both the core and separately queried frontier phases, illustrating why equal labels need not have identical full codes.

Freshness in Theorem 3.3 is retained as a source hypothesis. Theorem 2.2 allows arbitrary other coincidences, but its constant outside table differs from this band spectrum. Neither theorem is silently extended by the other's label assumptions.

## 4. Two INITIAL tail thresholds and the forced parent

The new family retains the same reader and fee but changes the parameter relation and the whole low-phase table. It is not the repeated-band family of Chapter 3.

**定义 4.1（Two-threshold arbitrary table）。** Require

$$
m\ge3,\qquad 2\le r<m,\qquad T=m+r,\qquad k=m+r-1,
\qquad g=\gcd(m,r),\qquad P=g\mathbb Z/T\mathbb Z,
$$
$$
0\le a\le r-2,\qquad \lambda:P\to Y,\qquad C=\lambda(0),\quad D=\lambda(m).
\tag{4.1}
$$

Take $R_1\notin\lambda[P]$ and, if $a>0$, $R_2\notin\lambda[P]\cup\{R_1\}$. Define on both free-value fibres

$$
f_{\rm two}(v,-j,s)=
\begin{cases}
R_1,&s\ge r-1,\\
R_2,&r-1-a\le s<r-1\quad(a>0),\\
\lambda(j),&s<r-1-a,
\end{cases}
\qquad f_{\rm two}(\bot)=L_\bot.
\tag{4.2}
$$

The middle band is empty at $a=0$; the low band always contains tail zero. $L_\bot$ is arbitrary. The table and band are evaluated once on the INITIAL record. Put

$$
H=\{0,m\},\qquad Z=P\setminus H,\qquad
F=P\cap\{m-r+1,\ldots,m-1\}.
\tag{4.3}
$$

Endpoint labels may equal each other or any other low-phase label. Every specified source has the single-history witness (1.3).

**命题 4.2（All-action forced root and exact root archives）。** Every correct root on each free-value fibre is $U=1^m$. The root rejects precisely $s\ge r-1$, returning $R_1$. Every surviving record has

$$
(v\oplus\mathbf1_H(j),\ m-j,\ s+m),\qquad 0\le s\le r-2.
\tag{4.4}
$$

Its successful positive-difference archive has exactly the phases $H$ with all these initial tails; its zero-difference archive has exactly $Z$ with all these initial tails.

Proof. At any phase and fixed free value, take actual initial tails $s_{\rm hi}=r-1$ and $s_{\rm lo}=r-2-a$. Their labels are $R_1$ and $\lambda(j)$, which differ. A root first zero after $u<m$ ones is reached by both, since $(r-1)+u\le k-1$. They then merge and can never recover that distinction. Free stopping also fails on these two sources. Hence the only root is all ones. Its rejection criterion $s+m\ge k$ is exactly $s\ge r-1$, and its successful charge support is $H$ by (1.4). This proves both the current records and the full joint archive descriptions. ∎

**引理 4.3（All-action second-prefix necessity）。** If $a>0$, on either successful root archive every correct second action has first zero exactly after $a$ leading ones. If $a=0$, on the $Z$ archive with nonconstant $\lambda[Z]$, and on the $H$ archive with $C\ne D$, every correct second action starts zero.

Proof. For $a>0$, at the same phase take initial tails $s_M=r-1-a$ and $s_L=r-2-a$. Both occur on that phase's root-success archive. Their current tails are $k-a$ and $k-a-1$, and their INITIAL labels $R_2,\lambda(j)$ differ. A second first zero after $u<a$ ones merges them alive; one after $u>a$ ones, or no zero, sends both to common absorption. At $u=a$ precisely the middle source rejects and the low source survives to zero. No other prefix can occur in a correct controller, regardless of its remaining horizon.

For $a=0$, two different phase labels on either stated archive may be taken at initial tail $r-2$. Both now have tail $k-1$. A first bit one destroys both in the same absorbing state. Their unequal labels force a first zero. ∎

**命题 4.4（Actual omitted phases and prescribed charges）。** The second ordered path is

$$
W_1=[m,2m]\pmod T=[m,T-1]\cup[0,m-r].
\tag{4.5}
$$

Its actual complement is precisely $F$. A word with first zero after $a$ leading ones has, for $\varepsilon=\mathbf1_{\{a>0\}}$,

$$
q_1(m)=\varepsilon,
\qquad
q_1(m+i)=0\ (1\le i<a),\qquad
q_1(m+a)=1\quad(a>0).
\tag{4.6}
$$

All other path charges are free subject to full-path even parity. The prescribed charges matter as phase responses only at vertices in $P$.

Proof. The path description follows from $2m=T+(m-r)$. Formula (1.4) applied to $1^a0$ gives (4.6). Conversely these charges and the full-path parity yield exactly this literal prefix through (1.5); for $a=0$ it reads $q_1(m)=x_0=0$. Low sources have current tails at most $k-a-1$, so $a$ leading ones remain strictly below $k$ and the zero safely clears them. Middle sources have tails at least $k-a$ and reject during those leading ones. After the zero every survivor has a common tail determined solely by the suffix; its length is less than $m<k$, so no survivor rejects internally. A later word starting zero is safe at the next seam. ∎

## 5. Arbitrary-table depth-two frontier and global preset compatibility

**定理 5.1（Complete adaptive depth-two frontier）。** Suppose $\lambda[Z]$ is nonconstant. Then $C_{\rm ad}(f_{\rm two})\le2$ if and only if some orientation of distinct labels $A,B$ satisfies

$$
\lambda[Z]=\{A,B\},\qquad \lambda(j)=A\quad(j\in F),
\tag{5.1}
$$

and, when $a>0$,

$$
\lambda(j)=A\quad(j\in P\cap\{m+1,\ldots,m+a-1\}),
\qquad m+a\in P\ \Longrightarrow\ \lambda(m+a)=B.
\tag{5.2}
$$

If $F$ is empty, either orientation is allowed and must be tested against (5.2). Whenever the frontier holds, $C_{\rm ad}=2$. If both orientations fail, only $C_{\rm ad}\ge3$ and $C_{\rm pre}\ge3$ are concluded; the exact larger fees are not specified.

Proof. The root is forced by Proposition 4.2. On its $Z$ archive Lemma 4.3 forces second prefix $1^a0$, including $a=0$. Every low-tail source survives this prefix. Its second output is binary and differs from the common first endpoint by $q_1(j)$. Two-block completion therefore allows at most two low labels on $Z$; nonconstancy makes them exactly two. Let $A$ denote the zero-response label and $B$ the one-response label. Every phase in $F$ has response zero, as do the prescribed interior vertices in (4.6). The actual turn $m+a$ has response one. Thus (5.1)–(5.2) are necessary. A violation would leave differently labelled INITIAL sources with the same acquired endpoint archive. Preset control is a subclass, giving both failure lower bounds.

For sufficiency let $L=\{j\in Z:\lambda(j)=B\}$. On the second path set the prefix charges (4.6), assign $q_1(j)=\mathbf1_L(j)$ for every actual $j\in Z\cap W_1$, and set all unassigned charges except at zero to zero. The frontier guarantees consistency; $F$ needs no charge because its label is $A$. Finally choose

$$
q_1(0)=\bigoplus_{z\in W_1\setminus\{0\}}q_1(z).
\tag{5.3}
$$

This is an even full-path charge assignment. Its literal inverse supplies the $Z$ child's second block. Its middle band, if present, rejects to $R_2$; its low successful response returns $A$ or $B$ according to the actual second difference.

For the $H$ child, keep the same prescribed prefix and set

$$
q_1(0)=\varepsilon\oplus\mathbf1_{\{C\ne D\}},\qquad q_1(m)=\varepsilon.
\tag{5.4}
$$

Use vertex $d=m+a+1\le T-1$ for parity compensation, setting every other unassigned charge zero. It is in the path, outside $H$, and beyond the prescribed prefix, so it can be changed without altering either endpoint response or the literal first zero. If $C\ne D$ the two responses distinguish the endpoints; if $C=D$ either response returns their common label. The middle band rejects to $R_2$ here as well. Proposition 4.4 checks all seams and survival, and (1.5) explicitly constructs each actual word.

These two words are used on the two different root archives, as permitted for adaptive control. They are not combined into a preset stream. High sources returned $R_1$ at the root. The same difference decoder applies to both free values. Nonconstancy on $Z$ makes stopping after the root impossible, so the achieved adaptive fee two is exact. ∎

**定理 5.2（Exact common-stream surcharge）。** Under the frontier in Theorem 5.1, with $L=\{j\in Z:\lambda(j)=B\}$ in an admitted orientation,

$$
C_{\rm pre}(f_{\rm two})=2+
\mathbf1_{\{g=1,\ C\ne D,\ |L|\text{ even}\}}.
\tag{5.5}
$$

Noncoprime actual phase subgroups have no surcharge. In the coprime case the omitted set is nonempty and fixes the orientation, so the displayed parity cannot be evaded by exchanging label names.

Proof. Any two-block common stream starts with the forced root. Its second word must have the same prescribed prefix and must realize $q_1(j)=\mathbf1_L(j)$ on $Z$. The endpoint child uses this very word too; if $C\ne D$ it requires $q_1(0)\ne q_1(m)$.

If $g>1$, assign the required actual charges on $Z$ and the charges (5.4) on $H$. Keep all prescribed prefix charges, including nonactual ones. Use the residue of the absolute path vertex $d_*=2m-1$ as a parity donor. It is not actual because $d_*\equiv-1\pmod g$, and it lies strictly after the prefix because $a\le r-2<m-2$. It is not an endpoint or a previously prescribed vertex. Set all remaining unassigned charges zero and choose its charge to make the full path even. The inverse yields one actual second word that safely services both children. Its leaves are exactly those in the adaptive construction. The adaptive lower bound two proves optimality.

If $g=1$, every full-path vertex is actual. Here $r\ge2$ ensures $F\ne\varnothing$ by Proposition 6.1 below, fixing $A$ as its zero-response label. The total-charge identity reads

$$
q_1(0)\oplus\varepsilon\oplus(|L|\bmod2)=0.
\tag{5.6}
$$

Thus $q_1(0)=\varepsilon\oplus(|L|\bmod2)$, and its endpoint response differs from $q_1(m)=\varepsilon$ exactly when $|L|$ is odd. Equal endpoint labels need no separation, but unequal endpoint labels with even $|L|$ make every two-block common stream impossible. This is a sibling compatibility obstruction for one literal word, not a failure of either separately adapted child.

In this obstructed case use the $Z$ word from (5.3) as the common second block. The $Z$ successful archives and all middle-band rejection archives stop at the second endpoint. The remaining low $H$ archive has equal readings but distinct current phases; its states have not merged. The third ordered path is $W_2=[2m,3m]\pmod T$, with left endpoint $u_2=m-r\notin H$. It contains at least one $h_0\in H$: its complementary interval has only $r-1$ vertices and cannot contain both endpoints, whose shortest intervening arc has $r+1$ vertices. Select such an $h_0$ and a vertex

$$
e_0\in W_2\setminus\{u_2,0,m\}.
$$

This last set is nonempty since $m+1\ge4$. Give charge one to $h_0,e_0$ and zero elsewhere, including $u_2$ and the other endpoint if present. The even assignment inverts to a literal third word starting zero. It is safe from every surviving current tail, and its endpoint difference separates the two phases, returning $C,D$. This one common three-block stream has the required fee. All other cases already admit the common two-block word given by the charge identity or the nonactual donor. Both initial-value fibres and free initial rejection are covered. ∎

**推论 5.3（Constant outside table: credited overlap and direct interface completion）。** If $\lambda[Z]$ has one label, then

$$
C_{\rm ad}=C_{\rm pre}=
\begin{cases}
1,&a=0\text{ and }C=D,\\
2,&\text{otherwise}.
\end{cases}
\tag{5.7}
$$

Proof. The root cannot be omitted, by Proposition 4.2. At $a=0,C=D$ each root archive already has one label: $R_1$, the endpoint label, or the constant $Z$ label. If $a>0$, both successful archives still contain a middle and a low label; if $a=0,C\ne D$, the endpoint archive still contains two labels. These require a second block.

For $a=0,C\ne D$, Definition 2.1 applies and $T=m+r<2m$ gives exactly two blocks. For $a>0$, use the common prescribed prefix charges and the endpoint choice (5.4), compensating parity at $m+a+1$. The inverse is actual and safe. Its low $Z$ outputs may vary, but every such output returns the same constant label, so no constraint on their response bit is needed. Its middle sources reject to $R_2$, and its endpoint sources either return their common label or are separated by (5.4). Thus it is one correct common second word. This constant-table case and the endpoint specialization are supplier overlap; they are not asserted as a separate new arbitrary-table contribution. ∎

## 6. Attainability, subgroup edges, and sharp obstructions

**命题 6.1（Empty omitted set and smallest supports）。** For the two-threshold domain,

$$
F=\varnothing\quad\Longleftrightarrow\quad r=g,
\qquad |P|=(m+r)/g\ge3.
\tag{6.1}
$$

Proof. If $r=g$, the interval $m-g+1,\ldots,m-1$ contains no multiple of $g$. If $r>g$, divisibility gives $r\ge2g$, and the actual phase $m-g$ belongs to that interval, so $F$ is nonempty. Finally $m/g>r/g\ge1$ implies $m/g\ge2$, giving $|P|\ge3$. Hence $Z$ is always nonempty. If $|P|=3$, it is a singleton and the nonconstant frontier has no instances. ∎

**命题 6.2（Every two-threshold table remains attainable）。** Every table in Definition 4.1 has a uniformly finite actual controller, including tables outside the depth-two frontier.

Proof. After the forced root, issue the actual block $B_a=1^a0^{m-a}$. The high archive has already returned $R_1$; for $a>0$ the middle archive rejects in this block and returns $R_2$. Every low source survives and ends at tail zero. Its current phase is $\theta_{\rm INITIAL}+2m$.

Now use the supplied safe phase-recovery interface [S1] (Theorems 3.1, 5.2). For this $m\ge3$ domain it can be explicitly realized by repeating a single isolated-one probe $0^b1\,0^{m-b-1}$ for $p-1$ further paid blocks, where $b=1$ if $g=1$, and $b=g-1$ otherwise. One has $1\le b<m$. Each probe begins zero and contains one one, so every seam is safe. The interface says its chronological endpoint archive, with the current value as baseline, distinguishes the actual current phases in $P$. It relies on the fixed coefficient cycle and actual subgroup, not an unobserved clock. Subtract the known issued displacement $2m$ to recover the INITIAL phase, negate it to obtain $j$, and return $\lambda(j)$. The initial label remains unchanged through clearing. This common safe continuation pays its actual $p-1$ probes, giving the sufficient bound $p+1$ for this family, without an optimum claim outside the frontier. Both free values use their own difference baseline and initial $\bot$ stops free. ∎

**反例 6.3（Noncoprime empty-gap witness）。** Set

$$
m=6,\quad r=g=2,\quad T=8,\quad k=7,\quad P=\{0,2,4,6\},\quad a=0,
$$
$$
\lambda(2)=0,\quad\lambda(4)=1,\quad\lambda(0)=\lambda(6)=0.
\tag{6.2}
$$

Here $F=\varnothing$ but the exact adaptive and preset fee is two. A common stream is

$$
111111\mid000001.
\tag{6.3}
$$

Proof. The root rejects all initial tails at least one to $R_1$; the only low tail is zero. Its successful positive archive is $\{0,6\}$, both labelled zero; its zero archive is $\{2,4\}$. The second ordered path is $6,7,0,1,2,3,4$. Word $000001$ has charges one only at $3,4$, so its actual responses are zero at $2$ and one at $4$, and zero at both endpoints. Its first zero safely clears root tail six. Thus every leaf has its correct INITIAL label; nonconstancy on $Z$ excludes fee one. The nonactual vertex three supplies parity, demonstrating why a universal nonempty-$F$ requirement is false. ∎

**反例 6.4（Three low labels cannot fit depth two）。** At $m=3,r=2,a=0$, the actual set is $P=\mathbb Z/5\mathbb Z$ and $Z=\{1,2,4\}$. Give its three phases distinct low labels, choose any endpoint labels, and keep the required fresh $R_1$. The forced root places all three low labels in one archive; the next action must start zero and supplies only a binary endpoint. Hence neither adaptive nor common-preset control can complete in two blocks. Proposition 6.2 still makes the target attainable. This is a depth-two obstruction, not an exact larger-cost formula.

**边界 6.5（Bands, coincidences, and strictness）。** At $a=0$ no middle label is needed; at $a=r-2$ the low band consists exactly of initial tail zero. All forced-prefix and seam inequalities still hold. Empty internal sets in (5.2) impose no condition. A turn $m+a$ outside $P$ prescribes a literal charge but does not prescribe an actual label. At $r=g$, the omitted set is empty and orientations are checked explicitly; at $r>g$ it contains the actual phase $m-g$ and fixes the zero-response colour in an admitted table. The smallest actual support has three phases, leaving a singleton $Z$ handled by (5.7).

Any equality between $C,D$ or between them and either outside colour is permitted. The root separated $H$ from $Z$ before these later coincidences are used; labels equal across archives do not erase the archive. Initial $L_\bot$ may equal any legal label and stops freely on the distinct initial rejection reading. Rejection remains independent of the scalar value. All constructions work on both free-value fibres and both original literal alphabets in this proper-narrow range.

The freshness of $R_1$ and, when present, $R_2$ is used in the all-action mergers. Chapter 2's freedom to let its high label coincide with an endpoint does not extend these two-band premises. Theorems 5.1–5.2 specify exact fees only on their frontier; elsewhere their lower bound three and Proposition 6.2's finite sufficient bound are deliberately distinct.

## 7. Sources, reuse conditions, and literature boundary

**数学引文 7.1（Sealed integrated sources）。** The source for Chapter 3 is [S19], commit `bfc12f8722c6e1409b3eb4a58a6d48d87aa5b644`, SHA256 `d17ed037a3c0521c3a48e272dbd364c5a0f2e245cd01718e703fcefe89a2a0b6`. The source for Chapter 2 is [S20], commit `9d76ae7d0ff82788d133cb680d0792341e91ba69`, SHA256 `378313b5c4b2b8245253a71229b7334adfc4df4b358c378b16478ef686522c07`. These are ordinary supplied results, not new independent proofs or evidence of kernel verification. The present statement and construction preserve their substantive proofs while using one INITIAL-record convention.

| Source | Reused content and conditions |
| --- | --- |
| [S19] (Definitions 1.1–1.2, 2.1; Theorems 3.1, 4.1) | $k=Qm$, $Q\ge2$, $m\ge3$, arbitrary nonconstant repeated band, fresh high label and allowed outside coincidences; exact spectrum $hQ+1+e$. The endpoint refinement retains fresh distinct $D,E$ and the actual shared-stream proof with no extra fee. |
| [S20] (Definitions 1.1, 1.3, 2.1; Theorem 3.1) | Every $k\ge2$, $1\le m<k$, every gcd, constant outside low table, and only $D\ne E$. Its root obstruction, strict second zero, earliest informative absolute position, paid waits, isolated pulse, width-one exception, and label-coincidence domain appear in Chapter 2. |
| [S1] (Sections 1–2; Convention 1.3; Lemmas 4.2–4.3; Theorems 3.1, 5.2) | Original record and whole joint prior, INITIAL labels, actual fee, first-zero merger, both alphabets, and safe phase recovery. Its general finite bound is an attainability interface, not an optimum for arbitrary tables. |
| [S2] (Sections 13–14; Theorem 14.1) | Fixed original recurrence and $V_k\bmod2$ coefficient cycle with $T=k+1$. State counts, future-window counts, and emitted-block fees are different resources. |
| [S10], Interface 2.1; [S15], Sections 1–4 | Consecutive charge windows, actual inverse, current-tail safety, and joint archive composition. The noncoprime narrow-window law in S10 has tail-independent targets and window conditions, rather than the mixed-tail parent here. S15's separately optimized children do not prove global preset compatibility. |
| [S13] (Definition 1.3; Theorems 2.3, 8.4; [D11], response-code theory) | S13 supplies guarded phase-label costs and one-block certificates on an already acquired support. D11 is restricted to $g\ge2$, $3\le m<k$, and actual zero-cleared archives with common value and tail; its response-code conversion is not applied to the coprime two-threshold case. Acquiring a support, synchronizing its actual tail, and paying the arrival are additional obligations. No generic Bellman reformulation is offered as new cost mathematics. |
| [S16], Section 2; [S17], Definition 2.1; [S18], Theorem 2.1 and Convention 2.2 | Actual calendar, strict shorter-than-block forced-prefix family, full-one parent, compulsory second zero, and first-tour scans. S17's $a<m$ family does not specialize to the full-block parent. S18's binary, returning-frontier, injective-band, and binary fresh-endpoint cases are existing overlap. Its unused ancillary $10Q+1$ bound is not a premise. |

Theorem 2.2 is broader in width and label coincidences than the endpoint slice of Chapter 3, while Chapter 3 accommodates arbitrary repeated band spectra on its restricted divisible-order calendar. Their common subject is a forced mixed-tail INITIAL parent followed by paid phase opportunities. Chapter 5 adds a second INITIAL tail band, arbitrary subgroup-supported low tables, a complete depth-two frontier, and a compatibility calculation for the actual siblings. This organization does not identify the three domains or infer their maxima from one another.

The cited literal-execution and joint-history interfaces state actual block transitions and joint source realizations; the endpoint and first-zero interfaces state clearing, acquisition, and safe phase recovery on the actual subgroup. The associated first-zero criterion and bounded construction are used only as attainability interfaces. These source results do not assert any of the new cost formulas.

The supplied [D12] result gives exact adaptive cost on a whole INITIAL free-value fibre, rather than only an already acquired zero-cleared archive. Its parameters are $g\ge2$, $u\ge2$, $h\ge1$, $1\le\rho<u$, and $\gcd(u,\rho)=1$, with $p=hu+\rho$, $k=gp-1$, and $m=gu$; here $g=\gcd(m,k+1)$ is the actual phase gcd. For a phase-label table $\Lambda:\{0,\ldots,p-1\}\to Y$, set $n=\#\Lambda[\{0,\ldots,p-1\}]\ge3$ and $d=\lceil\log_2 n\rceil-1$. Every phase index whose label differs from $\Lambda(0)$ must satisfy $1\le j\le u-d\rho$. At a fixed free initial value $v$, the target must satisfy $f(v,-gj,s)=\Lambda(j)$ for every actual phase index $j$ and every $0\le s<k$: it is tail-independent on that entire INITIAL fibre. Under exactly these conditions, the fee is $hd+1$ actual emitted complete blocks for either original alphabet, with initial rejection returning its arbitrary label freely. The source theorem imposes no condition on the other free-value fibre. This guarded, tail-independent fee is supplied overlap; it does not give the mixed-tail two-threshold frontier of Theorem 5.1 or the sibling common-stream surcharge of Theorem 5.2, and no preset equality is inferred from its adaptive cost statement.

The pinned upstream comparison uses mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. Its `Mathlib/Computability/DFA.lean`, including `DFA.evalFrom`, append semantics, and the internal regular-language helper, supplies general deterministic word semantics. Those statements have no INITIAL-target, irreversible-tail, or paid-calendar minimum conclusion. This targeted comparison is not an exhaustive absence claim about upstream libraries.

**数学引文 7.2（Primary external literature）。** The following correspondences concern mature adjacent theory. The ordinary reader-specific proofs above carry the fee conclusions.

| Primary source | Exact use and limitation |
| --- | --- |
| Edward F. Moore, *Gedanken-Experiments on Sequential Machines*, *Automata Studies* (1956), pp.129–153, [primary text](https://www.cs.cmu.edu/~cdm/resources/Moore1956-gedanken-experiments.pdf), pp.129–131 | `literature-attested`: the simple experiment may choose inputs from prior outputs and draws conclusions about the state at the beginning; the multiple experiment separately allows copies. The destroyed-state example supplies irreversible-loss semantics. Only the single-source contract is used here; no multiple-copy or reset operation enters a protocol. |
| Petra van den Bos and Frits Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2](https://arxiv.org/pdf/1907.11034v2), pp.10–12, Definitions 12, 14, 17, 20 and Figure 3 | `literature-attested`: finite acyclic tests, inputs compatible with candidates, disjoint completed observations, adaptive distinguishing graphs, and destructive actions that merge previously distinguishable states. Here one input is a whole block and one reply its endpoint; only different INITIAL labels must be separated. These generic semantics do not supply a KBonacci mask or fee. |
| Anastasiya Chistopolskaya and Vladimir V. Podolskii, *Parity Decision Tree Complexity is Greater Than Granularity*, [arXiv:1810.08668v1](https://arxiv.org/pdf/1810.08668v1), introduction and Section 2.2 | `literature-attested`: parity trees query arbitrary input-coordinate subsets and charge depth. The elementary binary capacity principle is applicable. Arbitrary subset queries are unavailable here unless the ordered path, even full-path charge, prescribed first zero, and strict seam admit an actual literal inverse. A phase encoding alone supplies none of those operations. |
| Uraz Cengiz Türker, Robert M. Hierons, Mohammad Reza Mousavi, and Khaled El-Fakih, *Efficient State Identification for Finite State Machine-Based Testing*, [accepted manuscript](https://eprints.whiterose.ac.uk/id/eprint/230260/1/Ordered_Wset_Accepted.pdf), [DOI 10.1109/TSE.2025.3604472](https://doi.org/10.1109/TSE.2025.3604472), Definitions 11–15 and 18 | `literature-attested`: state-identifying paths start at specified states; identification paths cover all state/characterising-word pairs; Definition 13 removes extra transfer strings, Definition 14 requires pairwise shortest separating prefixes, Definition 15 combines these in an ordered characterising set, and Definition 18 bounds total transfer length. Transfer-free paths are present and are not uniformly reset-based. Their coverage and pairwise minimality do not equal an unknown INITIAL label's minimum worst-branch emitted-block fee. No fee-preserving equivalence is claimed. The accepted PDF has SHA256 `a20067072d7349615f42c05ad7b431de04389c035b81f2388d779230dc906c7a`. |

The named primary versions, fixed mathematical suppliers, and deterministic-word semantics are the comparison scope. Chapters 4–6 are deductions from the stated hypotheses. No exhaustive literature gap, mathematical priority, or originality claim is made. Generic identification results are reused with their actual contracts rather than rebuilt.

## 9. What remains open in the original objective

**开放问题 9.1（All parameters and arbitrary attainable INITIAL targets）。** The objective remains the exact minimum worst-branch actual emitted-complete-block fee for every attainable immutable INITIAL record target, for all original $k\ge2,m\ge1$, with the fixed matched value, full joint actual-history prior, chronological endpoint-only archives, independent absorbing rejection, and both original control alphabets.

The integrated results settle a constant-outside endpoint-threshold family for every proper narrow width; arbitrary repeated band spectra and their fresh endpoint refinement for $k=Qm$; and the complete two-threshold depth-two frontier for $k=m+r-1$ with the stated fresh rejection bands. They do not identify a universal all-target optimum. In the frontier-failing two-threshold family, attainability and a lower bound three are known here, while the exact larger fee remains open.

Further tail partitions, arbitrary low-phase supports, several outside labels beyond these tables, competing admissible parents, nonfresh rejection labels, nonmultiple calendars in general, repeated reactivation, and the remaining widths retain their original quantifiers and actual fee. The higher-$Q$ protected-spectrum route and paid-calendar batch route remain separate possible increments; neither is authored or discarded by this volume. Their protocols would still need joint realization, preservation of immutable labels, every charged arrival and wait, all competing parent comparisons, and global common-stream compatibility where claimed.

[S1]: https://raw.githubusercontent.com/the-omega-institute/trureturing/f64d9e5dc37301e04ffc33332c919dd56a81ed6f/docs/develop/theory/KBONACCI_IRREVERSIBLE_TARGET_ACQUISITION.md
[S2]: https://raw.githubusercontent.com/the-omega-institute/trureturing/73168b5b84a8ba1328b6fa51eb9d722f3d4a7daa/docs/develop/theory/KBONACCI_MINIMAL_MODULAR_OBSERVER.md
[S10]: https://raw.githubusercontent.com/the-omega-institute/trureturing/84c05a76262b9b8c1a491c02afdee34e60535e9b/docs/develop/theory/KBONACCI_NARROW_QUERY_WINDOW_COST.md
[S13]: https://raw.githubusercontent.com/the-omega-institute/trureturing/6850a89acdb12d4f17af57dacee2d67e0b514be4/docs/develop/theory/KBONACCI_MULTILABEL_PREFIX_AND_TERMINAL_COST.md
[S15]: https://raw.githubusercontent.com/the-omega-institute/trureturing/3541b57c0d31a89f11fb8b86c75b7b1555e49e6f/docs/develop/theory/KBONACCI_JOINT_RESPONSE_AND_SEAM_COST.md
[S16]: https://raw.githubusercontent.com/the-omega-institute/trureturing/5c531690b4ee33e642757c8485297e94aba5d9a1/docs/develop/theory/KBONACCI_INITIAL_CALENDAR_CAPACITY.md
[S17]: https://raw.githubusercontent.com/the-omega-institute/trureturing/799d8549ae4d270122eb9a2a42024fdbbbe69459/docs/develop/theory/KBONACCI_FORCED_PREFIX_PARITY_COST.md
[S18]: https://raw.githubusercontent.com/the-omega-institute/trureturing/f65f9a766bc1380a37a465f99c9cab6090ed06ff/docs/develop/theory/KBONACCI_FULL_BLOCK_THRESHOLD_COST.md
[D11]: https://raw.githubusercontent.com/the-omega-institute/trureturing/25a023d7f087268131a63ca799cb530a0b0796b7/docs/develop/theory/KBONACCI_RESPONSE_CODES_AND_ADAPTIVITY_BOUNDARIES.md
[S19]: https://raw.githubusercontent.com/the-omega-institute/trureturing/bfc12f8722c6e1409b3eb4a58a6d48d87aa5b644/docs/develop/theory/KBONACCI_PREFIX_LABEL_SPECTRUM_COST.md
[S20]: https://raw.githubusercontent.com/the-omega-institute/trureturing/9d76ae7d0ff82788d133cb680d0792341e91ba69/docs/develop/theory/KBONACCI_ENDPOINT_RETURN_COST.md
[D12]: https://github.com/the-omega-institute/trureturing/blob/9108f2ff2eff625c527c1226b56ff957ae62a28e/D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/RepeatedGuardrailCost.lean

## 追加锚（本行以下为增补区）

## 10. Guarded near-critical injective INITIAL tables

This chapter settles exact larger fees on a full mixed-tail INITIAL family. It uses the original joint prior and literal transitions of Chapter 1. Its high label may coincide with any low label; the freshness assumptions of Definition 4.1 are not imposed. The family has one INITIAL tail threshold and an injective table on the outside phases, rather than the arbitrary two-threshold table of Chapter 5.

**定义 10.1（Injective outside table and its guard）。** Fix

$$
m\ge3,\qquad 2\le r<m,\qquad T=m+r,\qquad k=T-1,
\qquad g=\gcd(m,r),\qquad u=m/g,\qquad \rho=r/g,
\qquad p=u+\rho.
\tag{10.1}
$$

Then $\gcd(u,\rho)=1$, $u>\rho\ge1$, and the actual phase set is $P=g\mathbb Z/T\mathbb Z$. Put

$$
H=\{0,m\},\qquad Z=P\setminus H,\qquad n=p-2\ge3,
\qquad d=\lceil\log_2 n\rceil,\qquad
u\ge(d-1)\rho+1.
\tag{10.2}
$$

Choose $\lambda:P\to Y$ injective on $Z$, and write $C=\lambda(0)$, $D=\lambda(m)$. The endpoint labels are arbitrary, including equality with each other or any outside label. Choose arbitrary labels $R,L_\bot$. On both free-value fibres define the entire target by

$$
f(v,-j,s)=
\begin{cases}
R,&s\ge r-1,\\
\lambda(j),&s<r-1,
\end{cases}
\quad j\in P,\quad 0\le s<k,
\qquad f(\bot)=L_\bot.
\tag{10.3}
$$

Thus low tails are all of $0,\ldots,r-2$, and high tails are all of $r-1,\ldots,k-1$. In particular this is not an INITIAL-tail-zero prior. Convention 1.2 supplies one whole actual history for each specified triple; all sources used below are instances of those joint witnesses. The arbitrary initial rejection label returns on the separate free rejection reading.

**引理 10.2（Global parent, immutable labels, and binary lower bound）。** Every correct controller for (10.3), on either free value and with any finite worst fee, starts with $1^m$. That parent rejects exactly the high tails. On its successful positive-difference archive the actual INITIAL phases are precisely $H$, and on its zero-difference archive they are precisely $Z$, in both cases with all low INITIAL tails. Consequently

$$
C_{\rm ad}(f)\ge1+d,\qquad C_{\rm pre}(f)\ge1+d.
\tag{10.4}
$$

The first post-parent block on the $Z$ archive must start zero. The same holds on the $H$ archive if $C\ne D$.

Proof. Since $n\ge3$ distinct outside labels occur, choose an actual phase $j\in Z$ with $\lambda(j)\ne R$. At this phase and one fixed free value, take INITIAL tails $r-2$ and $r-1$. Free stopping cannot return both labels. A root whose first zero follows $b<m$ leading ones lets both reach that zero, because $(r-1)+b\le m+r-2=k-1$. The zero merges their current records and their acquired archives, although their INITIAL labels differ. No later action can restore the distinction. Thus every correct root is $1^m$, without a freshness assumption on $R$.

That root rejects precisely $s+m\ge k$, or $s\ge r-1$. Its successful charge support is exactly $H$, by Interface 1.4. Each low source keeps its original label: the new record is $(v\oplus\mathbf1_H(j),-j+m,s+m)$, with its original $s$ still recorded only through the INITIAL target. The stated archive descriptions therefore follow from the full joint sources, not separately reachable coordinates.

For each $j\in Z$, select the actual source at INITIAL tail $r-2$. At the root these $n$ sources have common current value and tail $k-1$ and pairwise different INITIAL labels. A first post-parent bit one rejects them all without separating any label, so a correct second block starts zero. Afterwards their tail is common; within each acquired branch it remains common under every literal action. A later rejecting action therefore merges all remaining candidates of that branch and cannot resolve different labels. Successful observations are binary. A tree of at most $h$ further blocks has at most $2^h$ distinct-label leaves, even with early stopping and paid waits. Since $2^{d-1}<n$, at least $d$ post-parent blocks are necessary. This is an all-action lower bound from the INITIAL endpoint, including the forced parent's fee. The two endpoint sources at INITIAL tail $r-2$ give the same compulsory second zero on a nonconstant $H$ archive. ∎

## 11. Source-specific code lists on the guarded calendar

**引理 11.1（Disjoint forbidden bands and an unrestricted phase）。** Identify an actual phase $j=gi$ with $i\in\mathbb Z/p\mathbb Z$, and set $A=(\mathbb Z/p\mathbb Z)\setminus\{0,u\}$. For query indices $t=1,\ldots,d$ after the parent, let

$$
a_t=p-t\rho=u-(t-1)\rho,
\qquad
\mathcal W_t=[a_t,a_t+u]\pmod p,
\qquad
J_t=\{u-t\rho+1,\ldots,u-(t-1)\rho\}\pmod p.
\tag{11.1}
$$

The full physical path is $W_t=[tm,tm+m]\pmod T$, retaining all its nonactual vertices. Its actual vertices are $g\mathcal W_t$. Each $a_t$ is a positive representative, and

$$
(\mathbb Z/p\mathbb Z)\setminus(\mathcal W_t\setminus\{a_t\})=J_t.
\tag{11.2}
$$

The sets $J_1,\ldots,J_d$ are disjoint, each has $\rho$ vertices, and at least one phase of $A$ belongs to none of them. Thus the safe code list

$$
\mathcal L_i=\{z\in\mathbb F_2^d:z_t=0\text{ whenever }i\in J_t\},
\qquad i\in A,
\tag{11.3}
$$

is either the full cube or a single coordinate-zero half cube. There is at least one full-cube list.

Proof. The guard gives $a_d\ge1$ and $d\rho\le p-1$. Since $tm/g=tu\equiv-t\rho\pmod p$, the ordered actual path starts at $a_t$. Its last $u$ vertices, after deleting the first, have exactly the complementary band (11.2). All statements concern the circular order, even when the path or final band wraps. The bands concatenate the integer interval $u-d\rho+1,\ldots,u$, whose length is $d\rho<p$, so they are disjoint modulo $p$.

Write $L=u-(d-1)\rho\ge1$. Vertex $u$ is in $J_1$. If $L\ge2$, the number of phases of $A$ outside all bands is at least

$$
(p-2)-(d\rho-1)=L-1\ge1.
\tag{11.4}
$$

If $L=1$ and $\rho\ge2$, then $u=(d-1)\rho+1<d\rho$, so the concatenated interval also contains vertex zero. Exactly these two removed endpoint vertices belong to the bands. Hence there is exactly $p-d\rho=1$ outside phase outside all bands. The remaining possibility $L=\rho=1$ would give $u=d$ and $n=d-1$, contradicting $n>2^{d-1}$ for $d\ge2$. This proves the unrestricted list and the entire list description. ∎

**引理 11.2（Hall feasibility for the actual safe lists）。** There are pairwise distinct vectors $z_i\in\mathcal L_i$ for every $i\in A$.

Proof. Reuse the finite distinct-representative form of Hall's theorem, with index set $A$ and lists (11.3); its hypotheses are verified here for these specific lists. In the pinned upstream source [H11], this is `Finset.all_card_le_biUnion_card_iff_existsInjective'`. The finite theorem supplies the matching step, rather than a block-cost conclusion.

A subfamily containing a full-cube list has union size $2^d\ge n$, so satisfies Hall. Otherwise let $q$ be the number of distinct forbidden coordinates among its lists. If $q=0$, the subfamily is empty. If $q\ge1$, its union contains all vectors except those with one in each of these $q$ coordinates, and therefore has size

$$
2^d-2^{d-q}.
\tag{11.5}
$$

Each forbidden-coordinate group has at most $\rho$ sources, so a $q$-group subfamily has at most $q\rho$ sources. The guard and $n\le2^d$ imply $d\rho\le n+1\le2^d+1$.

For $d=2$ this gives $\rho\le2$, settling $q=1$ against the union size two. For $d\ge3$, the elementary inequality $2^d\ge3d-1$ gives

$$
(d-1)\rho\le\frac{(d-1)(2^d+1)}d\le2^d-2.
\tag{11.6}
$$

The sequence $(1-2^{-q})/q$ is decreasing for positive integers $q$: consecutive comparison reduces to $2^{q+1}\ge q+2$. For $1\le q\le d-1$, (11.6) consequently yields

$$
q\rho\le\frac q{d-1}(2^d-2)\le2^d-2^{d-q}.
\tag{11.7}
$$

This verifies every such subfamily. At $q=d$, its union has size $2^d-1$. The unrestricted phase of Lemma 11.1 is excluded from this subfamily, so its size is at most $n-1\le2^d-1$. All finite Hall inequalities hold. Applying the credited finite theorem gives the required distinct representatives. ∎

**引理 11.3（Slack changes the aggregate code）。** If $n<2^d$, the vectors in Lemma 11.2 can be chosen so that

$$
X=\bigoplus_{i\in A}z_i\ne0.
\tag{11.8}
$$

If $n=2^d$, every distinct assignment has $X=0$.

Proof. Begin with any matching. If its XOR is nonzero, retain it. Otherwise take the phase with full-cube list and replace its assigned vector $x$ by any unused cube vector $y$, which exists when $n<2^d$. This preserves every list condition and injectivity, and changes the aggregate from zero to $x\oplus y\ne0$. Under saturation the assigned vectors are the whole cube. Each coordinate then occurs as one exactly $2^{d-1}$ times, an even number since $d\ge2$, so the aggregate is zero. ∎

## 12. Literal protocols and the exact common-stream obstruction

**构造 12.1（Actual post-parent queries）。** Choose distinct codes from Lemma 11.2, using (11.8) in the nonsaturated case. For $t=1,\ldots,d$, prescribe the full physical path charges $q_t$ as follows. For every actual outside vertex $gi\in Z\cap W_t$, set

$$
q_t(gi)=z_i[t],\qquad q_t(ga_t)=0.
\tag{12.1}
$$

The two prescriptions agree by (11.3). All actual outside vertices not in $W_t$ have response zero and their corresponding code bit is zero. Let $X_t=\bigoplus_{i\in A}z_i[t]$.

When $g=1$, prescribe the endpoint charges by

$$
\begin{array}{c|cc}
 &q_t(0)&q_t(m)\\\hline
t=1&X_1&0\\
2\le t\le d&0&X_t.
\end{array}
\tag{12.2}
$$

A charge at an endpoint outside the path means zero there. Endpoint $m$ is in every one of these paths; zero is in the first path. For $t\ge2$ the left vertex $a_t$ lies strictly between zero and $m$, so none of the donor charges in (12.2) alters the prescribed left zero. Equation (12.2) makes the full-path sum even.

When $g>1$, set $q_1(0)=1$, $q_1(m)=0$, and set both endpoint charges to zero in all later rows when they are present. Every unassigned full-path vertex is zero except the nonactual donor

$$
b_t=ga_t+1\pmod T.
\tag{12.3}
$$

This donor is the second vertex of the full physical path and is not in $P$. Set its charge to the XOR of all other prescribed charges, making the full path even. Its nonactual status does not assert an independently reachable source or confer an unobserved output.

In both cases issue precisely the full literal inverse

$$
B_t(i)=\bigoplus_{h=0}^i q_t(tm+h\pmod T),\qquad 0\le i<m.
\tag{12.4}
$$

Each $B_t$ starts zero. By Interface 1.4 its actual endpoint differences are exactly the prescribed charges. That zero clears every surviving root tail, including $k-1$. All later queries start zero as well, so no cross-block run reaches $k$. Internally a word starting zero has run length at most $m-1<k$. Thus every query is an actual legal complete block under both alphabets, on every low INITIAL tail, not an algebraic combination of block masks. Every zero bit in (12.4) is emitted inside its charged block.

**命题 12.2（Adaptive attainment and compatible siblings）。** Construction 12.1 gives an adaptive protocol of worst fee $1+d$. It also gives one common preset stream of that fee whenever

$$
g>1\quad\text{or}\quad n<2^d\quad\text{or}\quad C=D.
\tag{12.5}
$$

Proof. Start with the forced parent $B_0=1^m$. Its rejection archive returns $R$ at fee one. Its successful $Z$ archive records its own successive differences during the $d$ actual queries and obtains precisely $z_{j/g}$. The distinct code identifies the INITIAL phase, so it returns $\lambda(j)$, without evaluating the target at the cleared current tail. Stopping may occur earlier when the code prefix already fixes that label; the full $d$ rows are a uniformly finite bound. Both free-value fibres have this same difference decoder. Initial rejection returns $L_\bot$ without issuing any block.

For adaptive control the $H$ archive stops at the parent if $C=D$. Otherwise it issues the single literal block

$$
0^{r-1}1\,0^{m-r}.
\tag{12.6}
$$

Its pulse is at absolute position $T-1$, with physical charge support $\{T-1,0\}$, so it has response one at INITIAL phase zero and zero at INITIAL phase $m$. Since $r-1\ge1$, its first zero safely clears every root survivor before the pulse, and the isolated one is legal. Thus it returns $C,D$ at fee two on this archive. These are actual alternate adaptive actions on separate root archives; no sibling observation is borrowed. The outside archive has the bound $1+d\ge3$, so the global adaptive bound is $1+d$.

For preset control use the one fixed literal stream $1^m\mid B_1\mid\cdots\mid B_d$ from Construction 12.1. If $g>1$, its first query already separates $H$ by $q_1(0)=1$, $q_1(m)=0$, independently of every outside code bit. If $C=D$, the endpoint archive stops before any query. In the remaining nonsaturated coprime case, (12.2) gives

$$
q_t(0)\oplus q_t(m)=X_t.
\tag{12.7}
$$

The nonzero vector $X$ guarantees a query where the endpoint responses differ. Their preceding common archive includes both INITIAL endpoints; at that differing query, the observed difference selects its correct label. Thus their actions are prefixes of the same actual stream that handles $Z$. This verifies global sibling compatibility, rather than inferring it from independently optimal children. Lemma 10.2 makes the attained adaptive bound exact and makes the preset bound exact under (12.5); in particular some actual outside source pays at least $d$ post-parent blocks even if others stop early. ∎

**引理 12.3（Saturated coprime sibling obstruction, for every action）。** If $g=1$, $n=2^d$, and $C\ne D$, no correct preset controller has worst fee at most $1+d$.

Proof. Any such stream must start with $1^m$. Select again the $n$ outside sources at INITIAL tail $r-2$. They have distinct labels and common root-success value and tail $k-1$. The first query must start zero. After it, all low INITIAL sources, including the two endpoints, have a common current tail independent of phase, free value, and former INITIAL tail.

A depth-$d$ binary tree can resolve exactly $2^d$ distinct labels only when all those sources reach successful leaves at depth $d$, one source per binary response vector. Indeed an early leaf would remove at least two of the $2^d$ depth-$d$ slots while resolving at most one label. A rejection at an unresolved common-tail node cannot split it. Hence no selected outside source stops early or rejects during these $d$ queries, and their successive-difference vectors comprise the whole cube $\mathbb F_2^d$.

The preset stream is common. Once the first query clears the tail, survival of every later block depends only on that common tail and the literal word. Since the outside sources all survive, both endpoint sources also survive every query. There is therefore no hidden selective rejection that could separate $C,D$. At each query the full physical path has even charge, and every physical vertex is actual because $g=1$. Extending the charges by zero outside the path yields the identity

$$
q_t(0)\oplus q_t(m)=\bigoplus_{j\in Z}q_t(j),\qquad 1\le t\le d.
\tag{12.8}
$$

In the complete outside code cube, the right side is zero at every coordinate, since $2^{d-1}$ is even. Thus the two endpoint sources have identical differences, and consequently identical acquired endpoint archives, throughout the stream. They could not have stopped on an earlier common archive with different labels and cannot stop correctly at the final one. This contradicts $C\ne D$. The argument allowed every literal query, every legal seam, and every archive-based early stopping rule; it did not assume the special safe lists or the construction's donor choice. ∎

**构造 12.4（One paid terminal block in the obstructed case）。** In the saturated coprime case with $C\ne D$, use Construction 12.1 for the first $d$ queries. Its outside sources have all stopped with their immutable labels by total fee $1+d$. Its endpoint responses remain equal by (12.7), but the endpoint phases have not merged. To finish, let

$$
t=d+1,\qquad a=tm\pmod T,\qquad W_t=[tm,tm+m]\pmod T.
\tag{12.9}
$$

Choose $h\in H\cap W_t$ and $e\in W_t\setminus\{a,0,m\}$. Assign charge one exactly at $h,e$ and zero at the other full-path vertices, then issue its complete inverse (1.5).

These choices always exist. For $n\ge3$, $d\le n-1$, so $d+1\le p-2$. Coprimality implies $a\notin H$: equality to zero would require $d+1\equiv0\pmod p$, and equality to $m$ would require $d\equiv0\pmod p$. Neither is possible. The complementary arc of $W_t$ has $r-1$ vertices. It cannot contain both zero and $m$, whose two cyclic separations have $r$ and $m>r$ edges. Hence the path contains at least one endpoint $h$, distinct from its left vertex. Finally $|W_t|=m+1\ge4$, so deleting its left vertex and both endpoints leaves a donor $e$.

The two charges have even parity and the left charge is zero, so the inverse starts zero. It safely clears the continuing endpoint sources' common tail and has no internal forbidden run. Its endpoint difference is one at $h$ and zero at the other endpoint, returning $C,D$. The donor is outside the continuing $H$ archive; using its literal charge does not combine histories or require a response from an already stopped outside source. This is one predetermined terminal block, charged in full. The total worst fee is $1+d+1$.

**定理 12.5（Exact guarded injective-table fees）。** For the entire parameter and label domain of Definition 10.1, under both original alphabets,

$$
\boxed{\displaystyle C_{\rm ad}(f)=1+d,\qquad
C_{\rm pre}(f)=1+d+\mathbf1_{\{g=1,\ n=2^d,\ C\ne D\}}.}
\tag{12.10}
$$

Proof. Lemma 10.2 gives the paid global-parent and binary lower bounds on both free-value fibres. Lemmas 11.1–11.3 verify the actual safe code lists; Construction 12.1 and Proposition 12.2 realize the adaptive bound and every compatible preset case with literal actions. Lemma 12.3 supplies the remaining all-stream lower bound, and Construction 12.4 attains it. Both fibres have identical fees because the protocols use their own successive endpoint differences and the sources exist on each fibre. The initial-bottom archive is independent and stops freely. None of these arguments requires freshness of $R$, $C$, $D$, or $L_\bot$ relative to the outside table. ∎

## 13. Sharp symbolic families and larger-fee examples

**推论 13.1（Every odd near-critical width at $r=2$）。** For every odd $m\ge3$, set $r=2$, $k=m+1$, and let $\lambda$ be injective on $Z=P\setminus\{0,m\}$. For the entire target (10.3), with arbitrary high, endpoint, and initial-bottom label coincidences,

$$
C_{\rm ad}(f)=C_{\rm pre}(f)=1+\lceil\log_2 m\rceil.
\tag{13.1}
$$

Proof. Here $g=1$, $n=m$, and $d=\lceil\log_2m\rceil\ge2$. Since $m$ is odd, $m\ge2^{d-1}+1$. The elementary inequality $2^{d-1}\ge2d-2$ for $d\ge2$ gives the guard $m\ge2d-1=(d-1)\rho+1$. An odd $m\ge3$ is not a power of two, so the nonsaturated case of Theorem 12.5 applies. ∎

**推论 13.2（Unbounded exact adaptive and preset fees with a terminal surcharge）。** For every odd integer $d\ge3$, take

$$
m=2^d-1,\qquad r=3,\qquad k=2^d+1.
\tag{13.2}
$$

For every injective $Z$ table and arbitrary high and initial-bottom labels, if $C\ne D$ then

$$
C_{\rm ad}(f)=d+1,\qquad C_{\rm pre}(f)=d+2.
\tag{13.3}
$$

If $C=D$, both fees instead equal $d+1$.

Proof. For odd $d$, $2^d-1\equiv1\pmod3$, so $g=1$ and $n=m+1=2^d$. The guard is $2^d-1\ge3d-2$, equivalently $2^d\ge3d-1$, valid for $d\ge3$. Thus Theorem 12.5 gives (13.3), with all low INITIAL tails $0,1$ and all high INITIAL tails $2,\ldots,k-1$ still included. The exact fees increase without bound; these are larger-fee laws rather than a depth-two table. ∎

**例 13.3（Smallest saturated member with literal streams）。** At $m=7,r=3,T=10,k=9$, one has $g=1$, $Z=\{1,2,3,4,5,6,8,9\}$, $n=8$, and $d=3$. Give these eight phases any distinct labels, keep $C\ne D$, and allow $R$ and either endpoint label to coincide with them. One feasible code table and its full common query words are

$$
\begin{array}{c|cccccccc}
j&1&2&3&4&5&6&8&9\\\hline
(z_1,z_2,z_3)&110&101&001&100&011&010&111&000
\end{array}
\tag{13.4}
$$

The guarded code stream and its terminal block can be chosen as

$$
1111111\mid0111011\mid0100111\mid0100111\mid0100000.
\tag{13.5}
$$

The root rejects precisely INITIAL tails at least two. The three middle words start zero and produce (13.4) on $Z$ through their own actual endpoint differences; their endpoint responses at zero and seven are equal. The final word, at absolute block index four, has even charge support $\{9,0\}$ on the ordered path $8,9,0,1,2,3,4,5$. Its first bit is zero and it separates the still-running endpoint phases. This is the preset optimum five. For adaptive control replace the endpoint archive's continuation by $0010000$, whose isolated one is at absolute position nine, and use the three code words only on the outside archive. That adaptive protocol has optimum four. Every successful low INITIAL source with tail zero or one survives the appropriate continuation. The displayed words are independent of label names and of the initial free value.

## 14. Reuse boundary and the original open objective

**数学引文 14.1（Exact prerequisites and uncovered deduction）。** The proof uses Chapter 1's matched coefficient cycle, whole-history realization, first-zero merger, even full-path charges, and literal inverse. Chapter 2's endpoint-return mechanism supplies the isolated pulse (12.6); its constant-outside fee is not asserted for an injective outside table. Chapters 4–6 supply the near-critical source model and depth-two boundaries with fresh rejection bands, whereas Definition 10.1 has only one threshold, permits a nonfresh high label, and has at least three different outside labels. The new exact fees therefore do not restate that depth-two frontier.

The finite Hall distinct-representative result is credited reuse through [H11]. Its actual use is finite index set $A$, finite binary cube, and lists (11.3); inequalities (11.5)–(11.7) verify the whole family of required unions. The list geometry, unrestricted source, code aggregate, literal sibling realization, and saturated all-stream lower bound are deductions for this reader. No new generic adaptive-testing or Hall theorem is claimed.

The response-code source [D11], Definitions 2.3, 3.1 and Theorems 2.2, 3.2–3.4, treats $g\ge2$ and an actually acquired common-value, common-tail archive. Its availability lists and simultaneous literal conversion are reusable background. Here the forced parent is paid from the full INITIAL prior, the outside support is the complement of two endpoints, and the zero-leading lists in Chapter 11 are a sufficient construction on a guarded near-critical calendar. For $g=1$, D11's noncoprime conversion does not apply; the even full-path coupling and the sibling obstruction are established directly. No necessity or exact-cost conclusion is inferred merely from these sufficient safe lists.

The supplied declaration [D12], `original_repeated_guardrail_cost`, requires $g\ge2$ and a target tail-independent on the entire specified free-value fibre. Its phase labels differing from the phase-zero label are restricted to $1,\ldots,u-R\rho$, where $R=\lceil\log_2 N\rceil-1$ and $N$ is that whole-fibre label count; its exact adaptive fee is $Rh+1$ in its stated parameterization. The target (10.3) depends on the INITIAL tail, is injective over the entire outside support, and includes coprime and preset cases. Those prerequisites are not substituted for one another. S17's shorter-than-block forced-prefix family and S19's repeated-band spectrum also have different supports and calendars; their binary capacity and paid-arrival reasoning are background, not this theorem's exact law.

The single-source identification contract of Moore's *Gedanken-Experiments on Sequential Machines* (pp.129–131), the compatible finite tests and adaptive distinguishing graphs of van den Bos and Vaandrager, and the binary-depth semantics in Chistopolskaya and Podolskii are mature adjacent theory as cited in Mathematical Citation 7.2. Their contracts do not provide arbitrary actual parity masks, reset/copy operations, or free phase waits. The accepted *Efficient State Identification for Finite State Machine-Based Testing* manuscript, Definitions 11–15 and 18, includes transfer-free paths and pairwise shortest separating prefixes, but optimizes state/characterising-word coverage and transfer length. That objective is not the unknown INITIAL label's worst-branch fee here. These literature comparisons supply semantics and boundaries; the reader-specific proofs above supply (12.10). The pinned finite-Hall source, these primary versions, and the named repository sources form the comparison scope, without an exhaustive absence or priority claim.

**开放问题 14.2（Unchanged all-parameter target）。** Theorem 12.5 settles one guarded near-critical injective family, including arbitrary high/endpoint label coincidences on the full joint INITIAL prior. It advances the exact larger-fee and global sibling-compatibility gaps in Open Problem 9.1. It does not settle the arbitrary repeated-label outside table without this guard, additional INITIAL tail partitions, competing feasible parents, other narrow calendars, or the general all-width attainable-target optimum. The original minimum worst-branch actual emitted-complete-block fee for every arbitrary attainable INITIAL target and all $k,m$ remains open. Offline code search, the number of label names, controller storage, and the emitted-block fee remain different resources.

[H11]: https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Combinatorics/Hall/Finite.lean

## 追加锚（本行以下为增补区）
## 15. Protected spectra with several INITIAL tail bands

**定义 15.1（Higher-tour protected INITIAL target）。** Use exactly the original reader, joint actual prior, two free-value fibres, independent initial rejection reading, and paid complete-block fee of Chapter 1. Fix

$$
Q\ge2,\qquad m\ge3,\qquad 2\le r<m,\qquad
T=Qm+r,\qquad k=T-1,\qquad g=\gcd(m,r),\qquad P=g\mathbb Z/T\mathbb Z.
\tag{15.1}
$$

Choose integers $d,a,J$ with

$$
1\le d\le Q,\qquad 0\le a<m,\qquad a>0\Longrightarrow d<Q,
\qquad H=k-dm-a>0,\qquad J\ge0.
\tag{15.2}
$$

Choose a set and a label table

$$
S\subseteq P\cap\bigl(\{1,\ldots,J\}\cup\{Qm+1,\ldots,T-1\}\bigr),
\qquad \eta:S\longrightarrow Y,
$$
$$
M=|\eta[S]|\ge2,\qquad L=\lceil\log_2 M\rceil,
\qquad A\in\eta[S],\qquad J+Lr\le m.
\tag{15.3}
$$

An interval with upper endpoint smaller than its lower endpoint is empty. Let $D,E,R_1,\ldots,R_d,L_\bot$, and, when $a>0$, $R_\star$, be arbitrary labels in $Y$. All coincidences among these labels and $\eta[S]$ are allowed. Put

$$
\lambda(j)=
\begin{cases}
D,&j=0,\\
E,&j=m,\\
\eta(j),&j\in S,\\
A,&\text{otherwise},
\end{cases}
\qquad j\in P.
\tag{15.4}
$$

The cases are disjoint: (15.3) implies $J\le m-r<m$, and the other protected interval lies above $Qm$. On both free-value fibres define the entire immutable INITIAL target by

$$
f(v,-j,s)=
\begin{cases}
R_t,&k-tm\le s<k-(t-1)m,\quad 1\le t\le d,\\
R_\star,&H\le s<k-dm,\quad a>0,\\
\lambda(j),&0\le s<H,
\end{cases}
\qquad f(\bot)=L_\bot.
\tag{15.5}
$$

Every triple in this definition has the single actual-history witness (1.3). In particular, all comparisons of different tails below concern jointly realized records, and not a product of separately attainable coordinates. The target is independent of the free value, but that value and its subsequent changes remain part of each source's own archive.

**引理 15.2（All-action staircase and paid protected-calendar lower bound）。** For every target (15.5), every correct controller on either free-value fibre has root $1^m$. Along the archive containing all protected low-tail sources, its first $d$ blocks are $1^m$. If $a>0$, its next block has first zero exactly after $a$ leading ones; if $a=0$, its next block starts zero. In particular,

$$
C_{\rm ad}(f)\ge LQ+1.
\tag{15.6}
$$

These conclusions allow early stopping on homogeneous other archives and all label coincidences in Definition 15.1.

Proof. Fix a free value. After $t<d$ blocks $1^m$, each protected phase has successful difference zero at every preceding endpoint, since the all-one charge support of block $b$ is $\{bm,(b+1)m\}$ for $0\le b<t$, and neither protected interval meets these vertices. All its low-tail sources remain present: $H-1+tm<k$. Their labels include the $M\ge2$ labels of $\eta[S]$, so this common archive cannot stop.

Choose a protected phase $j$ with $\eta(j)\ne R_{t+1}$. This is possible even if $R_{t+1}$ is a protected label. Compare the actual INITIAL tails

$$
s_{\rm low}=H-1,\qquad s_{\rm band}=k-(t+1)m
\tag{15.7}
$$

at this same phase and value. The second lies in band $t+1$, both survive the preceding $t$ all-one blocks, and both have the same acquired archive. Their current tails are $H-1+tm$ and $k-m$. If the next action has a first zero after $b<m$ leading ones, both reach that zero successfully, since $k-m+b\le k-1$. At the zero their entire current records merge. Their distinct INITIAL labels cannot be recovered by any subsequent action. Thus the next block must be $1^m$. This proves the assertion by induction, including its root case, and excludes every competing root or earlier zero on the protected archive without assuming fresh band labels.

When $a>0$, choose a protected phase with $\eta(j)\ne R_\star$ and compare INITIAL tails $H-1$ and $H$. After the $d$ compulsory blocks their current tails are $k-a-1$ and $k-a$. A first zero after $b<a$ ones merges both alive. If $b>a$, or if there is no zero, both reject before the next observed endpoint: their rejection times within that block are unobserved. Only $b=a$ can be correct. When $a=0$, take the protected low sources at INITIAL tail $H-1$. After the $d$ blocks all have tail $k-1$ and at least two different labels; a first bit one would send them to one rejection archive, so the next block starts zero.

For the cost lower bound, select one protected phase for each distinct label and, at each such phase, the actual source at INITIAL tail $H-1$. The selected sources have a common current tail before the first zero. After that zero the tail remains common within each acquired archive under every literal continuation. A rejecting action at a nonconstant selected archive destroys all its remaining labels together and cannot be correct. Successful observations supply at most two children. This remains true under adaptive actions; no observations from different branches are combined.

The actual calendar up to index $LQ$ follows from $Qm=T-r$:

$$
\begin{aligned}
W_{\ell Q}&=[-\ell r,m-\ell r]\pmod T,&&1\le\ell\le L,\\
W_{eQ+b}&=[bm-er,(b+1)m-er],&&0\le e<L,\quad 1\le b<Q.
\end{aligned}
\tag{15.8}
$$

Every main window $W_{\ell Q}$ contains all of $S$: its lower segment reaches at least $J$, and its upper segment starts at $T-\ell r\le Qm$. Every displayed non-main window misses $S$. Indeed, its left endpoint is at least $m-(L-1)r\ge J+r>J$, while its right endpoint is at most $Qm<T$; there is no wrap. The compulsory root also has zero response on $S$. Thus only indices $Q,2Q,\ldots$ can distinguish the selected protected labels. By total fee $LQ$, at most $L-1$ such indices have been emitted. At most $2^{L-1}<M$ distinct-label leaves are available, even with adaptive stopping and any paid waits. This proves (15.6). The induction and capacity argument apply separately on both actual free-value fibres. ∎

## 16. One literal stream attaining the protected-spectrum fee

**构造 16.1（Completed siblings and physical parity compensation）。** Choose an injective label code

$$
c:\eta[S]\longrightarrow\{0,1\}^L,\qquad c(A)=0^L,
\qquad F_\ell=\{j\in S:c_\ell(\eta(j))=1\},\quad 1\le\ell\le L.
\tag{16.1}
$$

The zero code is reserved for the default label, not for a presumed absent source. All actual low sources outside $S\cup\{0,m\}$ have that label.

The following complete-block stream is fixed in advance and ends at index $LQ$, hence has total length $LQ+1$ blocks. First issue $1^m$ at indices $0,\ldots,d-1$. If $a>0$, at index $d$ issue

$$
1^a0^{m-a}.
\tag{16.2}
$$

All remaining non-main indices are $0^m$, except for the special prescription below. This gives a single stream for both values; stopping and decoding use each source's own observed endpoint differences.

Call $d=1,a=0$ the endpoint-retaining case. In this case replace the non-main block at index $Q-1$ by

$$
0^{m-1}1.
\tag{16.3}
$$

Its full physical charge support is $\{Qm-1,Qm\}$. Both vertices are actual only if they belong to $P$; neither belongs to $S$ or $\{0,m\}$, and every actual low source there has label $A$. A positive response on the root-zero archive therefore returns $A$. This pulse is paid even when it detects no actual source.

At the main indices $\ell Q$, prescribe even full-path supports as follows. Outside the endpoint-retaining case, set

$$
E_\ell=F_\ell\cup
\begin{cases}
\{0\},&|F_\ell|\text{ odd},\\
\varnothing,&|F_\ell|\text{ even}.
\end{cases}
\tag{16.4}
$$

In the endpoint-retaining case, the first main support instead is

$$
E_1=F_1\cup\{0\}\cup
\begin{cases}
\{Qm\},&|F_1|\text{ even},\\
\varnothing,&|F_1|\text{ odd}.
\end{cases}
\tag{16.5}
$$

For its later main indices use (16.4). Issue the actual word $\mathcal B_{\ell Q}(E_\ell)$ given by the ordered literal inverse (1.5). The compensation vertex $0$ belongs to every main window, including when $Lr=m$ and it is the final path vertex. The extra vertex $Qm$ in (16.5) is the first vertex of $W_Q$. Equations (15.8) and (15.3) put every $F_\ell$ in its prescribed path. Thus every row is even on the full physical path and has a unique literal inverse; no algebraic span is used as an action.

**定理 16.2（Exact full mixed-tail protected-spectrum law）。** For every parameter, support, and label choice in Definition 15.1, under both original literal alphabets,

$$
\boxed{\displaystyle C_{\rm ad}(f)=C_{\rm pre}(f)=LQ+1.}
\tag{16.6}
$$

Construction 16.1 attains this cost on the entire joint actual INITIAL prior, including the initial rejection record, sparse protected supports, noncoprime phases, arbitrary label coincidences, a full $d=Q,a=0$ staircase, partial staircases, and equality $J+Lr=m$.

Proof. Lemma 15.2 supplies the all-action lower bound, so it remains to prove the stream, its seams, and its immutable leaf labels.

During its first $d$ all-one blocks, precisely the INITIAL tail band $t$ first rejects at index $t-1$, for $1\le t\le d$. Its leaf returns $R_t$, regardless of its preceding values. If $a>0$, precisely the remaining INITIAL tails $H\le s<k-dm$ first reject in (16.2), and their leaf returns $R_\star$. Every low INITIAL tail $s<H$ survives: its tail after the $d$ full-one blocks is at most $k-a-1$, so the $a$ subsequent leading ones, when present, reach at most $k-1$, after which zero clears it. The rest of (16.2) consists of zeros. These are labels of the INITIAL bands; the label $L_\bot$ is returned only from the separate free initial rejection reading.

Let

$$
B=d+\mathbf1_{\{a>0\}}
\tag{16.7}
$$

be the number of prefix blocks that complete this band separation. No successful source is decoded as a low source before these $B$ blocks have been paid. This prevents any unrejected band from borrowing a low label, even when band labels coincide with endpoint or protected labels. After these blocks every remaining source has INITIAL tail $s<H$ and its target depends only on $j$.

Write $\Delta_t$ for its observed successful endpoint difference at block $t$. The root has $\Delta_0=1$ exactly at $j=0,m$. If $d\ge2$, on this root-positive archive block one has $\Delta_1=0$ at $j=0$ and $\Delta_1=1$ at $j=m$, by the all-one support $\{m,2m\}$. If $d=1,a>0$, the same separation holds because (16.2) has support $\{m,m+a\}$. Thus, outside the endpoint-retaining case, the two endpoint sources can return their exact labels $D,E$ once all $B$ band-separating blocks have completed. They have stopped before any main query, since $B\le Q$. The main compensation at $0$ in (16.4) therefore affects no continuing low source on that completed endpoint archive.

Every other positive difference in these prefix blocks, on a root-zero archive, is supported at a multiple of $m$ or at $dm+a$ when $a>0$. None of those phases is protected. Their surviving low sources have label $A$, and can return it after block $B-1$. All protected sources have entirely zero prefix differences. Consequently, in the regular case, the continuing zero-prefix archive consists of all protected sources and some actual default-$A$ sources; the endpoints have already stopped.

In the endpoint-retaining case the only prefix block is the root, and the root-positive archive still contains $j=0,m$. The pulse (16.3) misses those endpoints and all of $S$. Any successful root-zero source with pulse difference one has label $A$ and stops there. In particular, every actual root-zero source at $Qm$ has stopped before the extra parity charge at that vertex in (16.5). At the first main block, (16.5) has response one at $0$ and zero at $m$, which is outside $W_Q$. On their root-positive archive this separates $D$ and $E$ exactly. Those sources now stop, so later compensation at $0$ is harmless on the same acquired archive. No observation from the default-$A$ pulse archive is used to decode an endpoint source or a protected source.

For every continuing root-zero source in either case, the main response at index $\ell Q$ equals $c_\ell(\eta(j))$ when $j\in S$, and zero otherwise. In (16.4), the only charged vertex outside $S$ is an already completed endpoint. In (16.5), the additional charged default vertex has already been screened by the paid pulse. Non-main zero blocks have zero successful difference, and the special pulse misses $S$. Thus after the $L$ main responses the decoder returns the label assigned to that code. The all-zero code returns $A$, both for protected occurrences of $A$ and for every continuing default source. Injectivity separates different protected labels, while repeated occurrences or coincidences with other leaf labels are allowed. These deductions use the chronological archive of the same original source throughout.

It remains to check literal legality at every seam. The all-one prefix has already been checked directly against each INITIAL tail. If $a>0$, its partial block ends at tail zero. If $a=0,d<Q$, the next block starts zero and clears every survivor; in the endpoint-retaining case it is either a zero wait or, at $Q=2$, the pulse (16.3), which also starts zero. The pulse ends at tail one. If $a=0,d=Q$, survivors can still have tail $k-1$ immediately before the first main query. Its left vertex is $Qm$, which is outside $S$ and different from $0$, and (16.4) prescribes zero there; hence its inverse starts zero and safely clears every survivor.

Every regular main word starts zero. For $1\le\ell\le L$ its first vertex $T-\ell r$ is at most $Qm$, above the low protected interval, different from $0$, and not in the upper protected interval. Thus it is uncharged in (16.4). After that first zero a length-$m$ block has no run reaching $k>2m$. In the endpoint-retaining first query its left vertex may be charged by (16.5), but the incoming tail is one and any leading run has length at most $m$; $1+m<k$ makes the seam strictly legal. The other main words start zero. Successive main indices are separated by $Q-1\ge1$ paid zero blocks. Any such wait clears the preceding tail, and any post-zero internal run is shorter than $k$. No additional rejection occurs after the INITIAL bands have been separated.

All issued words have length $m<k$, so all are internally legal and belong to both original alphabets. The seam argument checks their actual concatenation, not just their internal words. Neither sparse actual phase supports nor nonactual compensation possibilities are assumed: the supports above are explicit full-path supports, and any prescribed nonactual pulse charge simply supplies no source. All equality and extreme staircase cases satisfy the same inequalities. The construction never discards a paid zero block or the paid screening pulse. Its last main word is block index $LQ$, giving fee $LQ+1$. The same literal stream works on both values using their own differences, and initial $\bot$ stops freely with $L_\bot$. Hence $C_{\rm pre}\le LQ+1$, which with Lemma 15.2 proves (16.6). ∎

## 17. A sharp three-label boundary beyond the protected guard

**定义 17.1（Width-five boundary INITIAL family）。** For any $Q\ge2$, put

$$
m=5,\qquad r=2,\qquad T=5Q+2,\qquad k=5Q+1.
\tag{17.1}
$$

Here $g=1$ and every phase is actual. Choose pairwise distinct labels $A,B,C$, and arbitrary $D,E,R,L_\bot$; these latter labels may coincide with each other or with $A,B,C$. On both free-value fibres define

$$
f_5(v,-j,s)=
\begin{cases}
R,&s\ge k-5,\\
B,&s<k-5,\ j=1,\\
C,&s<k-5,\ j=3,\\
D,&s<k-5,\ j=0,\\
E,&s<k-5,\ j=5,\\
A,&\text{otherwise},
\end{cases}
\qquad f_5(\bot)=L_\bot.
\tag{17.2}
$$

All low-tail cases range over every $0\le s<k-5$. Their sources and the high-tail comparisons below have the joint witnesses (1.3).

**定理 17.2（Exact symbolic boundary fee for every tour count）。** For every target (17.2), under both original alphabets,

$$
\boxed{\displaystyle C_{\rm ad}(f_5)=C_{\rm pre}(f_5)=Q+2.}
\tag{17.3}
$$

Proof. On a fixed free-value fibre, choose one of the low labels $A,B,C$ different from $R$ and a phase carrying it. Compare INITIAL tails $k-6$ and $k-5$ at that phase. A root first zero after fewer than five ones merges them alive; their labels differ. Thus every correct root is $11111$, which rejects exactly the high band. This excludes every competing parent even with a nonfresh $R$.

Take the three actual low sources at phases $1,3,4$, INITIAL tail $k-6$, and the fixed free value. Their labels are $B,C,A$ and their root differences are all zero. Their current tails after the root are all $k-1$. The next action on this archive must start zero: a first one would reject all three into one archive. Until index $Q$, no block can split them. Indeed for $1\le t<Q$ its window is $[5t,5(t+1)]$ without wrap, and misses all of $1,3,4$. Every successful difference is zero; rejection cannot resolve their three different labels. Once zero clears their tails, these remain common within their acquired archive. At index $Q$ one successful complete-block observation gives at most two children, and a rejecting action would again merge all remaining labels. Therefore a worst fee of $Q+1$ cannot distinguish these three sources. Adaptive choices, homogeneous earlier leaves on other archives, and every paid wait are included in this lower bound. Hence $C_{\rm ad}(f_5)\ge Q+2$.

For attainment use the one common literal stream

$$
11111\ \mid\ \underbrace{00000\mid\cdots\mid00000}_{Q-1\ \text{paid blocks}}
\ \mid\ 00100\ \mid\ 11000.
\tag{17.4}
$$

The first word rejects exactly INITIAL tails $s\ge k-5$; return $R$ at that leaf. Every low source survives and the first paid zero wait safely clears even current tail $k-1$. All later waits are also paid. At index $Q$ the ordered path and the actual word $00100$ give

$$
W_Q=[5Q,5Q+1,0,1,2,3],\qquad E_Q=\{0,1\}.
\tag{17.5}
$$

At index $Q+1$ the actual word $11000$ gives

$$
W_{Q+1}=[3,4,5,6,7,8],\qquad E_{Q+1}=\{3,5\}.
\tag{17.6}
$$

These are literal charges from (1.4), not arbitrary parity queries. On the successful root-positive archive the only INITIAL phases are $0,5$. The first query has respective differences one and zero, returning $D,E$; these sources stop before the charge at $5$ in the last block. On the root-zero archive a first-query difference one occurs exactly at phase $1$, and returns $B$. Of the remaining sources, a last-query difference one occurs exactly at phase $3$, returning $C$; all others return $A$. The extra last-query charge at $5$ belongs to the already completed endpoint archive and does not supply an additional source to this decoder. Thus every low source returns its immutable INITIAL label, even if another completed label happens to coincide with it.

The zero waits end at tail zero; $00100$ starts and ends zero and is strictly legal. The last block has only two leading ones and ends zero, so it is also strictly legal for $k\ge11$. Each word has length $5<k$ and hence belongs to both original alphabets, and every actual cross-block seam has been checked. The same stream and differences work for either free value, while initial $\bot$ returns its independent label freely. Its fee is $1+(Q-1)+2=Q+2$, proving (17.3). ∎

**命题 17.3（Removing the protected guard changes the exact law）。** The extension of (16.6) to Definition 17.1 obtained by omitting only the guard $J+Lr\le m$ is false for every $Q\ge2$.

Proof. Represent (17.2) in the remaining notation of Definition 15.1 using $d=1,a=0$, $S=\{1,3,4\}$, $J=4$, and

$$
\eta(1)=B,\qquad\eta(3)=C,\qquad\eta(4)=A.
\tag{17.7}
$$

Then $M=3$, $L=2$, $A\in\eta[S]$, and every other requirement of (15.1)–(15.5) holds; only $J+Lr=8>5$ fails. The proposed extension would give $2Q+1$, whereas Theorem 17.2 gives $Q+2<2Q+1$. The missing calendar premise has a precise effect: phase $3$ is the right endpoint of $W_Q$ and the left endpoint of $W_{Q+1}$, so it can be queried again one paid block later. In the guarded proof all protected phases miss every non-main window through the required horizon. That statement is false here. The completed endpoint at phase $5$ supplies the compatible even last charge without contaminating the same continuing $C/A$ archive. This conclusion concerns only the family (17.2); it gives no exact formula for an arbitrary unguarded phase table. ∎

## 18. Source contracts and the unchanged general target

**数学引文 18.1（Exact reuse and the reader-specific deduction）。** Chapters 15–17 reuse Chapter 1's matched coefficient cycle, joint single-history realization, first-zero irreversible merger, ordered even-charge path, and literal inverse. These interfaces are credited there to the pinned [S1], [S2], [S10], and [S15]. The binary leaf-capacity principle is mature decision-tree theory; its reader-specific input is the paid calendar (15.8), not a newly supplied generic Bellman equation.

The supplied repeated-band theorem [S19], integrated as Theorem 3.2, has $k=Qm$, a fully populated first band with its frontier-removal spectrum, and a fresh high label. The forced-prefix families in [S17], including its returning-frontier example, likewise use $k=Qm$ and their particular bands. Neither fixes the calendar $T=Qm+r$, sparse two-sided protected support, several arbitrary nonfresh INITIAL tail bands, and shared physical compensation of Theorem 16.2. Theorem 2.2, credited to [S20], supplies endpoint-return reasoning but assumes its own constant-outside target and endpoint inequality; its exact fee is not transplanted to a protected spectrum. Theorems 5.1–5.2 concern a near-critical two-threshold depth-two table, and Theorem 12.5 concerns a near-critical injective outside table. Their hypotheses and fee origins are retained rather than identified with (15.5).

The pinned declaration [D12], `original_repeated_guardrail_cost` in `RepeatedGuardrailCost.lean`, is also reused only within its actual contract. It requires $g\ge2$, $m=gu$, $T=g(hu+\rho)$ with $\gcd(u,\rho)=1$, $\rho<u$, and at least three phase labels. With $N$ the whole-fibre phase-label count and $R=\lceil\log_2N\rceil-1$, its differing-from-phase-zero labels lie in $1,\ldots,u-R\rho$; the target is independent of every INITIAL tail on one specified free-value fibre. Its exact adaptive fee is $Rh+1$. It does not establish the mixed-tail target (15.5), a coprime case, or one common literal stream on all sibling archives. The ordinary proof here establishes these additional contracts rather than specializing that tail-independent assertion.

For external comparison, the primary versions in Mathematical Citation 7.2 remain the relevant mature background. Van den Bos and Vaandrager, [arXiv:1907.11034v2](https://arxiv.org/html/1907.11034v2), Definition 11 and Figure 3, treat adaptive distinguishing graphs and examples in which an input irreversibly merges initial states. Chistopolskaya and Podolskii, [arXiv:1810.08668v1](https://arxiv.org/html/1810.08668v1), introduction and Section 2.2, allow arbitrary coordinate-subset parity queries and charge tree depth. Such a query is not an available reader action without the actual window, ordered inverse, and seam proved here. The accepted *Efficient State Identification for Finite State Machine-Based Testing* [manuscript](https://eprints.whiterose.ac.uk/id/eprint/230260/1/Ordered_Wset_Accepted.pdf), Definitions 13–15 and 18, combines transfer-free state-identifying coverage, pairwise shortest separating prefixes, nonredundant ordered characterising sets, and transfer length. Those objectives do not equal one unknown INITIAL target's worst-branch complete-block fee. No fee-preserving equivalence, exhaustive absence, or mathematical priority is inferred from these comparisons.

**开放问题 18.2（All widths and arbitrary attainable INITIAL labels）。** Theorem 16.2 provides a higher-tour, repeated-label, multiple-tail symbolic family with an actual optimal common stream; Theorem 17.2 identifies one sharp unguarded boundary and its different exact fee. The general objective of Open Problem 9.1 remains unchanged: determine the exact minimum worst-branch number of actual emitted complete blocks for every arbitrary attainable immutable INITIAL target and all original $k\ge2,m\ge1$. Arbitrary unguarded tables, richer tail partitions beyond (15.5), competing feasible parents outside the proved families, and other narrow or wide calendars remain within that objective. Neither result replaces its quantifiers by a tail-only prior or by a generic decision-tree model. Offline code selection, controller memory, and all paid waits remain separate from one another and from the emitted-block fee.

## 追加锚（本行以下为增补区）

## 19. Arbitrary low-phase labels at the first endpoint return

**定义 19.1（Full INITIAL threshold table）。** Retain the reader, matched coefficient cycle, joint actual histories, two free-value fibres, independent absorbing rejection, literal alphabets, immutable INITIAL labels, and paid endpoint-only fee of Chapter 1. Fix

$$
Q\ge2,\qquad m\ge3,\qquad 2\le r<m,\qquad
T=Qm+r,\qquad k=T-1,\qquad g=\gcd(m,r),
$$
$$
P=g\mathbb Z/T\mathbb Z,\qquad b=k-m,\qquad N=Q+1.
\tag{19.1}
$$

Let $Y$ be any set and $\lambda:P\to Y$ any table with

$$
\lambda(0)=D\ne E=\lambda(m).
\tag{19.2}
$$

Choose arbitrary $R,L_\bot\in Y$, allowing every coincidence consistent with (19.2). The entire target, on both free-value fibres and every INITIAL tail, is

$$
f(v,-j,s)=
\begin{cases}
R,&b\le s<k,\\
\lambda(j),&0\le s<b,
\end{cases}
\qquad j\in P,\quad v\in\mathbb F_2,
\qquad f(\bot)=L_\bot.
\tag{19.3}
$$

The source at every displayed triple is the one whole history (1.3); no restriction to INITIAL tail zero is made. Independence of $v$ is a hypothesis of this family. Write

$$
H=\{0,m\},\qquad Z=P\setminus H.
$$

Block index zero is the paid root. The post-root indices are $1,\ldots,Q$ at total fee $N$. In representatives $0,\ldots,T-1$, their ordered windows are

$$
W_t=[tm,(t+1)m]\quad(1\le t<Q),
\qquad
W_Q=[Qm,Qm+1,\ldots,T-1,0,1,\ldots,m-r].
\tag{19.4}
$$

Their outside phases decompose into the frozen set, single-opportunity slots, and adjacent-window boundaries:

$$
F=P\cap\{m-r+1,\ldots,m-1\},
$$
$$
K_t=P\cap\{tm+1,\ldots,(t+1)m-1\}\quad(1\le t<Q),
$$
$$
K_Q=P\cap\bigl(\{Qm+1,\ldots,T-1\}\cup\{1,\ldots,m-r\}\bigr),
\qquad h_t=(t+1)m\quad(1\le t<Q).
\tag{19.5}
$$

Thus $Z$ is the disjoint union of $F$, all $K_t$, and $h_1,\ldots,h_{Q-1}$. A phase in $F$ has no post-root opportunity by fee $N$; a phase in $K_t$ has exactly the opportunity $t$; $h_t$ has exactly the two opportunities $t,t+1$. In particular the terminal slot includes the right endpoint $m-r$ of the wrapped path. This endpoint is not an adjacent-window boundary within this deadline. The frozen set can be empty. For $g=1$, it contains $r-1\ge1$ phases.

**定义 19.2（Explicit deadline arrays）。** A row $e_t$ prescribes charges on $P\cap W_t$, and is extended by zero on $P\setminus W_t$. Call the array $(e_1,\ldots,e_Q)$ literal-admissible when

$$
e_1(m)=0,
\qquad
\bigoplus_{j\in W_t}e_t(j)=0\quad(1\le t\le Q)\ \text{if }g=1.
\tag{19.6}
$$

When $g>1$ there is no parity restriction on the actual vertices. Indeed $tm+1\pmod T$ is a nonactual vertex of each window: assign its charge to compensate the parity of the prescribed actual charges and assign zero to other nonactual vertices. Formula (1.5) then gives a whole literal word realizing each row. For $g=1$ the row already has even full-path parity and (1.5) applies directly. In either case (19.6) makes the first bit of block one zero. This is actual path inversion, not a linear span of unavailable blocks.

For an admissible array define, using only its zero-difference continuation,

$$
U_1=Z,\qquad A_t=\{j\in U_t:e_t(j)=1\},\qquad
U_{t+1}=U_t\setminus A_t,
$$
$$
X_t=A_t\setminus\{h_t\}\quad(t<Q),\qquad X_Q=A_Q.
\tag{19.7}
$$

Say that the array has the retirement property if

$$
|\lambda[X_t]|\le1\quad(1\le t\le Q),\qquad
|\lambda[U_{Q+1}]|\le1.
\tag{19.8}
$$

Empty sets satisfy these inequalities. If $t<Q$, $h_t\in A_t$, and $X_t$ is nonempty with its unique label $L_t$, call $t$ a repair obligation exactly when $\lambda(h_t)\ne L_t$. The common-stream condition is

$$
e_Q(0)=1,
\qquad e_{t+1}(h_t)=1\quad\text{at every repair obligation }t<Q.
\tag{19.9}
$$

Labels may repeat arbitrarily, including at the $h_t$. Neither (19.7) nor (19.8) chooses a baseline in advance or presupposes an actual frozen phase. These conditions are finite mathematical existence tests on the actual charge rows. With a supplied finite table and decidable equality of its labels, the finitely many binary rows can be enumerated and the displayed comparisons performed. Without table access and label-equality access, no effective algorithm on an arbitrary abstract $Y$ is asserted. Such offline enumeration is not an emitted-block fee.

## 20. Complete adaptive and preset deadline classifications

**定理 20.1（Every arbitrary-table first-return deadline）。** For every parameter and table in Definition 19.1, under either original literal alphabet,

$$
C_{\rm ad}(f)\ge N,\qquad C_{\rm pre}(f)\ge N,
\tag{20.1}
$$
$$
C_{\rm ad}(f)=N
\quad\Longleftrightarrow\quad
\text{some literal-admissible array satisfies (19.8)},
\tag{20.2}
$$
$$
C_{\rm pre}(f)=N
\quad\Longleftrightarrow\quad
\text{some literal-admissible array satisfies (19.8) and (19.9)}.
\tag{20.3}
$$

These are separate existence statements: the preset array need not be the adaptive array first found. Failure of the respective test means only $C_{\rm ad}(f)>N$ or $C_{\rm pre}(f)>N$. It supplies no uniform next optimum and no unattainability conclusion.

Proof. First reuse the global first-zero comparison and endpoint-return obstruction of [S1, Lemmas 4.2–4.3] and [S20, Theorem 3.1], integrated in Theorem 2.2. Their lower-bound argument does not use the constant outside table of that theorem. At least one of $D,E$ differs from $R$. At that endpoint and a fixed free value, the actual INITIAL tails $b-1,b$ have different labels. Every root with a zero after $a<m$ leading ones lets both reach that zero, since $b+a\le k-1$, and merges them with the same acquired archive. No continuation can recover their different INITIAL labels. A free stopping root is likewise impossible. Thus every correct root among all $2^m$ words is $1^m$, even with nonfresh $R$ or further adaptive actions.

The root rejects exactly the high tails, which return $R$ at fee one. Every low tail survives; its root difference is one precisely at $H$. The two successful root archives are therefore the whole low-tail supports $H$ and $Z$, not marginal phase supports borrowed from another branch. On $H$, take the two actual low sources at INITIAL tail $b-1$. They have the same current value and current tail $k-1$. Every second block beginning one rejects both at its first bit, irreversibly merging distinct endpoint labels. Hence this block starts zero.

Before absolute emitted position $T-1$, the phase-zero source's only active position is zero, and the phase-$m$ source's only active positions are $m-1,m$. The root gives each one unit of difference; the compulsory zero at position $m$ suppresses the second source's next opportunity. For total fee $d<N$, the last emitted position is $dm-1<T-1$. The two endpoint archives therefore stay identical, with the same actions, stopping decisions and later rejection if any. This proves (20.1) for every adaptive tree, and thus for every preset stream. In the deadline $N$, the only later window permitting a nonzero charge on $H$ is $W_Q$, which contains zero and not $m$. Consequently every successful preset stream of fee $N$ must satisfy $e_Q(0)=1$.

On a nonconstant $Z$ archive, choose every phase at INITIAL tail $b-1$. All now have tail $k-1$ and the same root value. A second block beginning one would merge all of them in rejection, including two different labels. It must therefore start zero. If $\lambda[Z]$ is constant, stop this archive at the root; for a deadline array it may instead be extended formally by zero blocks. This covers the constant case without excluding any correct controller.

The clearing bit at absolute position $m$ has a useful stronger consequence. Up to fee $N$, there are only

$$
(Nm-1)-m=Qm-1<k
\tag{20.4}
$$

positions after it. Every later literal choice is safe, even if all those positions are ones. The clearing bit also makes the current tail common within each acquired archive, independently of the INITIAL tail. Thus there is no additional run or cross-block rejection shortcut after this point in the deadline. For $g>1$, compensation on a nonactual vertex affects the literal word but cannot introduce a nonexistent source. All words considered here are in both alphabets since $m<k$.

For adaptive necessity take the actions on the $Z$ archive's chronological zero-difference continuation. If it stops early, its labels are constant, so extend that leaf by actual zero blocks to index $Q$. These words give a literal-admissible array. At the positive child of index $t<Q$, the actual phase support is exactly $A_t$. By (19.4)–(19.5), the phases in $X_t$ have no further window opportunity before the deadline. Only $h_t$ can appear again, and only at index $t+1$. Two sources in $X_t$ follow identical subsequent outputs under any actions on this child, since their current values and tails are common and every future charge is zero. They must have the same INITIAL label. The same reasoning at $t=Q$ makes $\lambda[A_Q]$ constant, and the all-zero terminal archive makes $\lambda[U_{Q+1}]$ constant. This proves (19.8). It is a collapse forced by this reader's one-tour geometry, not a generic belief-tree recursion.

For adaptive sufficiency invert the array into literal words and issue them along the continuing zero-difference archive after the root. At a positive child $A_t$, if $X_t$ is empty, its sole possible phase is $h_t$, so return its label. If $X_t$ is nonempty with label $L_t$, and $h_t$ is absent or has that same label, return $L_t$ immediately. At a repair obligation issue, on this child alone, the next complete block

$$
10^{m-1}.
\tag{20.5}
$$

Its full-path support at index $t+1$ is $\{h_t,h_t+1\}$; the latter phase was never in $A_t$. It gives difference one on $h_t$ and zero on $X_t$. Return $\lambda(h_t)$ or $L_t$ accordingly. This is exactly one paid repair block, finishing at total fee $t+2\le Q+1=N$. It is safe by (20.4), including a seam whose preceding word ends in ones. At index $Q$, return the unique label of $A_Q$ or $U_{Q+1}$ on the respective nonempty child. All decoding refers to the acquired original labels.

The endpoint archive uses its own actual continuation: zero blocks at indices $1,\ldots,Q-1$, followed at index $Q$ by

$$
0^{r-1}1\,0^{m-r}.
\tag{20.6}
$$

The pulse is at absolute position $T-1$ with support $\{T-1,0\}$. On $H$ it selects only zero, so difference one returns $D$ and difference zero returns $E$. All waits are emitted and charged. The first wait clears tail $k-1$; the pulse is isolated, so every INITIAL low tail succeeds. The initial rejection reading returns $L_\bot$ freely. Both free values use their own successive endpoint differences, not another fibre's outputs. This realizes (20.2) with actual worst fee $N$, attained on the endpoint sources.

For preset necessity, the one stream supplies a single full array even on sources stopped early. It starts zero at index one because its $H$ archive still needs to continue. The safety bound (20.4) permits formal continuation of the whole low support through all $N$ blocks. The same retirement argument gives (19.8). At a repair obligation the sources in $X_t$ and $h_t$ share their acquired archive through index $t$ and have different labels. Only $h_t$ can have any further nonzero charge; its sole remaining opportunity is index $t+1$. Hence that same global row must have $e_{t+1}(h_t)=1$. Together with the endpoint constraint already proved, this is (19.9). Early stopping cannot remove an obligation at a nonconstant acquired archive.

For preset sufficiency, invert these very same rows on their full physical paths and use $1^m$ followed by the resulting $Q$ words as one fixed literal stream. The $Z$ decoder follows the cases in the adaptive construction. At a repair obligation it reads the next block of this common stream: (19.9) selects $h_t$, and all of $X_t$ is outside that next window, so the same two labels are separated. No word is substituted from a different branch. On $H$, the index-one first zero suppresses the charge at $m$, all intermediate windows miss both phases, and the final row selects zero by (19.9). The endpoint decoder therefore returns $D,E$ at fee $N$. Bound (20.4) simultaneously proves every seam safe on all continuing low sources. The high and initial rejection leaves are the ones already specified. This proves (20.3), including empty $X_t$, an empty zero-continuation support, empty $F$, repeated adjacent-boundary labels, all allowed coincidences, and both alphabets. ∎

The distinction between a deadline failure and unattainability is substantive. The supplied safe phase-recovery interface [S1, Theorem 3.1] applies after the paid parent and a paid zero-clearing block, since every successful same-phase merged fibre now has one INITIAL label. For example its safe pulse method can be used with blocks $0^{m-1}1$ for a complete $p=T/g$-step phase tour. On actual phases when $g>1$, the support $\{(t+1)m-1,(t+1)m\}$ restricts to the singleton $(t+1)m$, and these singletons traverse $P$. When $g=1$, the full $T$-step responses traverse a translated adjacent pair; two different phases cannot give identical full patterns, since an adjacent pair on a cycle of length $T\ge8$ has no nonzero translation stabilizer. Each block starts zero and has tail one, so its seams are strict. This is a reused finite-attainment construction with a total upper bound $p+2$, not a claimed optimum following a failed deadline test.

## 21. Arbitrary paid batches and the exact global-stream fee

**定义 21.1（Single-label batches with unrestricted coincidences）。** In Definition 19.1 choose a baseline $A\in Y$ and arbitrary subsets $O_t\subseteq K_t$ for $1\le t\le Q$, including empty and full sets. Each nonempty $O_t$ carries one label $B_t\ne A$. Different $B_t$ may coincide, and may equal $D,E,R,L_\bot$. Put

$$
\lambda(j)=B_t\quad(j\in O_t),\qquad
\lambda(j)=A\quad(j\in Z\setminus\bigcup_{t=1}^QO_t),
\qquad \lambda(0)=D\ne E=\lambda(m),
$$
$$
B=\sum_{t=1}^Q|O_t|.
\tag{21.1}
$$

The slots are disjoint; in particular every adjacent-window boundary $h_t$ has label $A$. This is a hypothesis about actual phases and INITIAL labels, not merely about the number of nonbaseline labels. The terminal slot $K_Q$ has both the high-end and wrapped low-end parts in (19.5).

**定理 21.2（Sharp all-gcd batch law）。** For every target in Definition 21.1,

$$
C_{\rm ad}(f)=N,
\qquad
C_{\rm pre}(f)=N+
\mathbf1_{\{g=1,\ O_t\ne\varnothing\ (1\le t\le Q),\ B\text{ even}\}}.
\tag{21.2}
$$

Proof. The lower bound $N$ is (20.1); it applies regardless of label coincidences. We first construct adaptive attainment and then compare the common streams, because parity of a proposed row alone does not establish preset optimality.

For $g=1$, take on the zero-continuation archive the following even supports:

$$
E_t=O_t\cup
\begin{cases}
\{h_t\},&|O_t|\text{ odd},\\
\varnothing,&|O_t|\text{ even},
\end{cases}
\quad(1\le t<Q),
$$
$$
E_Q=O_Q\cup
\begin{cases}
\{0\},&|O_Q|\text{ odd},\\
\varnothing,&|O_Q|\text{ even}.
\end{cases}
\tag{21.3}
$$

All left-boundary charges are zero, including the compulsory charge at $m$. Every selected strict-slot source has label $B_t$. The only additional selected actual source at a nonterminal index is $h_t$, with label $A$. If present alongside a nonempty $O_t$, it is separated by (20.5) on that positive child at the next paid endpoint. If $O_t$ is empty there is no selected boundary in (21.3). A left boundary previously removed from the continuing zero archive can have zero charge in the following scan word: the repair of its other actual child is an adaptive word, not a constraint on this word. At the final index, only $O_Q$ is selected inside $Z$. The final zero archive consists solely of baseline sources. Thus (21.3) has the retirement property and Theorem 20.1 supplies a legal adaptive controller of fee $N$, including its separately acquired endpoint sibling. This construction also covers empty terminal or earlier batches, and repeated $B_t$.

For $g>1$ prescribe actual charges exactly $O_t$ at indices $t<Q$, and $O_Q\cup\{0\}$ at index $Q$. Compensate an odd total on a nonactual vertex of that same window. This gives one literal common stream with first post-root bit zero. No actual adjacent boundary is selected. Each positive scan child returns $B_t$ immediately, the terminal zero child returns $A$, and the final row separates $D,E$ on the root-positive archive. Theorem 20.1 proves simultaneous literal validity and fee $N$. This argument does not require any frozen actual phase or a positive-size actual complement of a batch.

Now suppose $g=1$, every $O_t$ is nonempty, and a preset controller had fee $N$. Since $F$ contains an actual phase with label $A$ and has no post-root opportunity, its zero-difference archive fixes the terminal zero label to be $A$. Every $j\in O_t$ has its only opportunity at $t$, so its charge must be one: leaving it on the zero archive would permanently merge $B_t\ne A$ with that frozen phase. Any baseline phase in $K_t$ must have charge zero, since otherwise it shares the positive child with the nonempty $B_t$ core and has no later opportunity to separate. These assertions apply equally when $B_t$ equals a different batch label or an endpoint label.

Let $a_t=e_t(h_t)$ for $1\le t<Q$, and let $a_0=0$. At the next index the charge at the left boundary obeys

$$
e_{t+1}(h_t)=a_t.
\tag{21.4}
$$

If $a_t=1$, the root-zero archive's positive child contains the nonempty $B_t$ core and the boundary labelled $A$. The common stream must repair them at the boundary's sole remaining opportunity, forcing the next charge one. If $a_t=0$, that boundary is still on the zero-continuation archive; selecting it at the next index would join the nonempty $B_{t+1}$ core as a permanently silent different label, so the next charge must be zero. This proves both directions of (21.4) from actual leaf obligations, rather than choosing favourable parity orientations independently on different branches.

Full-path parity now gives

$$
a_{t-1}\oplus(|O_t|\bmod2)\oplus a_t=0
\quad(1\le t<Q).
\tag{21.5}
$$

On the terminal path, the charge at $Qm$ is $a_{Q-1}$ by the same argument, the actual terminal-slot charges are the indicator of $O_Q$, and the charge at zero is one for the unequal endpoint sibling. Hence

$$
a_{Q-1}\oplus(|O_Q|\bmod2)\oplus1=0.
\tag{21.6}
$$

Adding (21.5)–(21.6) in $\mathbb F_2$ cancels all boundaries and yields $B\bmod2=1$. Thus $B$ even excludes every preset stream of fee $N$, not just (21.3). The forced parent comparison and endpoint lower bound already excluded every cheaper fee.

To attain fee $N$ in all the remaining coprime cases, select sets $J_t$ as follows. If $B$ is odd, let $J_t=O_t$ for all $t$. If $B$ is even and some $O_h$ is empty, choose any $z\in K_h$ and put

$$
J_h=\{z\},\qquad J_t=O_t\quad(t\ne h).
\tag{21.7}
$$

Such a vertex exists: for $g=1$ each $K_t$, including $K_Q$, has $m-1\ge2$ vertices. It has label $A$. In both cases the total $\sum|J_t|$ is odd. Define

$$
a_0=0,\qquad a_t=\bigoplus_{i=1}^t(|J_i|\bmod2)\quad(1\le t<Q),
$$
$$
E_t=J_t\cup\{tm:a_{t-1}=1\}\cup\{(t+1)m:a_t=1\}
\quad(1\le t<Q),
$$
$$
E_Q=J_Q\cup\{Qm:a_{Q-1}=1\}\cup\{0\}.
\tag{21.8}
$$

The conditional singleton notation means the empty set when its condition fails. These supports have even full-path parity; their first row omits $m$, so every word is the literal inverse (1.5) and the first post-root bit is zero.

If the left charge at an index is one, that boundary was already selected by the previous right charge and is absent from this index's zero-continuation archive. If the previous right charge was zero, the boundary is still present and the present left charge is zero. Therefore the retired positive core is exactly $J_t$, whose label is $B_t$ for a nonempty original batch and $A$ for the compensation singleton. Every selected right boundary has label $A$. A positive core of label $B_t$ repairs that boundary using the next row's left charge one. A positive child containing only baseline sources returns $A$ immediately, with no repair obligation. The terminal positive core is again $J_Q$, and the terminal zero archive contains only baseline labels. The charge at zero is one on the very same final word, so the endpoint sibling returns $D,E$ correctly. Thus (21.8) satisfies the common-stream criterion (19.9) on all actual branches. Every paid scan, wait, and necessary repair is within fee $N$, with the strict safety bound (20.4). In particular an empty terminal batch can supply the compensation singleton just as an earlier empty batch can; it cannot be silently omitted from the criterion.

Finally suppose $g=1$, every batch is nonempty, and $B$ is even. Take $J_t=O_t$ and the cumulative $a_t$ just defined. Keep the nonterminal rows of (21.8), and replace its last row by

$$
E_Q=O_Q\cup\{Qm:a_{Q-1}=1\}.
\tag{21.9}
$$

Its full parity is even because the total $B$ is even. The same common-stream scan and repair decoder finishes every root-zero source by fee $N$. Only the root-positive endpoint sibling is unresolved: its final zero-phase charge is now zero. Append at index $Q+1$ the one literal block

$$
0^{r-1}1\,0^{m-r}.
\tag{21.10}
$$

Its starting residue is $(Q+1)m\equiv m-r\pmod T$; its isolated pulse has support $\{m-1,m\}$. On the still-live $H$ archive this selects exactly $m$, returning $E$ on difference one and $D$ on difference zero. The leading $r-1\ge1$ zeros clear any current tail before the pulse; the trailing $m-r\ge1$ zeros leave tail zero. There is no additional cleanup fee. The whole prefix through fee $N$ was safe by (20.4), and (21.10) is safe on the same histories. The outside sources may stop by fee $N$; the endpoint sources actually pay $N+1$. This is one fixed global stream and one paid final repair. Together with the all-action exclusion of $N$, it proves the exact surcharge in (21.2). ∎

The support of each word above is assigned on its own full physical path. A nonactual compensation vertex in the noncoprime case, an already removed boundary in (21.8), and a baseline-labelled compensation phase in an empty batch have different roles. Only the first is not a source. The latter two require the explicit acquired-archive and leaf arguments in the proof; they cannot be borrowed freely from another branch.

## 22. Complete-target obstructions and scope counterexamples

**命题 22.1（An empty terminal batch removes an even-total surcharge）。** Set $Q=2,m=3,r=2$, so $T=8,k=7,b=4,N=3$. On low tails let $\lambda(4)=\lambda(5)=B\ne A$, put $A$ at every other outside phase, and retain $\lambda(0)=D\ne E=\lambda(3)$. Give every high tail any label $R$ and initial rejection any label $L_\bot$. Then

$$
C_{\rm ad}(f)=C_{\rm pre}(f)=3.
\tag{22.1}
$$

Proof. Here $K_1=\{4,5\}$, $K_2=\{7,1\}$, $O_1=K_1$, and $O_2=\varnothing$, with total batch size two. The empty terminal slot is the missing hypothesis in an unqualified even-total surcharge. More explicitly the common stream

$$
111\mid010\mid001
\tag{22.2}
$$

has successive full charge supports $\{0,3\}$, $\{4,5\}$, $\{0,1\}$. Root rejection returns $R$. On the root-zero archive, the second difference selects exactly the $B$ phases; every other candidate there has label $A$, so both children stop by fee two. On the root-positive archive, the second word starts zero and gives no endpoint difference; the third selects zero and not three, returning $D,E$. The first bit of the second word clears every surviving INITIAL tail, and its isolated one and the final isolated one have strict seams. Initial $\bot$ is decoded separately for free. The endpoint lower bound (20.1) excludes every fee below three. This proves the full INITIAL target law, independently of the numerical parity observation. ∎

**命题 22.2（A genuine adaptive-three, preset-four target）。** At the same parameters, put $\lambda(4)=B\ne A$ and $\lambda(7)=C\ne A$, with all other outside phases labelled $A$. The labels $B,C$ may coincide with each other or any endpoint, high, or initial rejection label. With $D\ne E$,

$$
C_{\rm ad}(f)=3,\qquad C_{\rm pre}(f)=4.
\tag{22.3}
$$

Proof. The two nonempty batches are $O_1=\{4\}$ and $O_2=\{7\}$; Theorem 21.2 applies. An explicit adaptive controller starts with $111$. Its high-rejection archive returns $R$. On its endpoint archive issue $000\mid010$; the last support $\{7,0\}$ selects only zero among $\{0,3\}$ and returns $D,E$.

On the root-zero archive issue $011$, with support $\{4,6\}$. The positive child is $\{4,6\}$ with labels $B,A$; there issue $100$ at index two, whose support $\{6,7\}$ restricts to $\{6\}$. Difference zero returns $B$ and difference one returns $A$. The zero child is $\{1,2,5,7\}$; there issue $010$ with support $\{7,0\}$, returning $C$ on difference one and $A$ on difference zero. Each source follows only its own chronological actions, with no mixed-branch output. All these branches clear at the second block's first bit and end by fee three, so (20.4) proves every seam safe on every low INITIAL tail.

For a direct all-action preset exclusion at three, the frozen phase two has label $A$. The first post-root word must start zero; write its bits $0ab$. Since phase four's only opportunity is this word, it must have charge one, hence $a=1$. Phase five has label $A$ and no later opportunity; its charge must be zero, hence $a\oplus b=0$ and $b=1$. Thus phase six is selected with charge one. Its label $A$ differs from phase four's $B$, so the common final word must have charge one at six to repair that acquired positive child. On the zero child, phase seven must have charge one to separate $C$ from frozen $A$, and phase one must have charge zero because its baseline label cannot share the final positive child with $C$. The endpoint sibling requires charge one at zero. The last window is $[6,7,0,1]$; the four required charges are consequently $1,1,1,0$, of odd total, which no literal word realizes. This includes arbitrary common-stream early stopping: the cited nonconstant children cannot already stop. All fees below three are excluded by (20.1).

A common stream of fee four is

$$
111\mid000\mid010\mid001,
\tag{22.4}
$$

with post-root supports $\varnothing$, $\{7,0\}$, $\{3,4\}$. The third block distinguishes $C$ at seven from all other root-zero sources, and also distinguishes $D,E$ on the endpoint sibling. On the remaining root-zero archive the fourth block selects only phase four, returning $B$ versus $A$. Sources already identified stop at their own endpoints. The second word clears every low INITIAL tail, the last two pulses are isolated, and all intervening zeros are paid. Hence the upper bound four is actual and exact. ∎

**命题 22.3（One colour per strict slot is insufficient without the clearing-boundary condition）。** At the same parameters let $A,B,C,F$ be pairwise distinct, and set

$$
\lambda(4)=\lambda(5)=B,\qquad \lambda(1)=C,\qquad
\lambda(6)=F,\qquad \lambda(2)=\lambda(7)=A,
\qquad \lambda(0)=D\ne E=\lambda(3).
\tag{22.5}
$$

The endpoint labels and $R,L_\bot$ need satisfy no additional freshness conditions. Then

$$
C_{\rm ad}(f)=C_{\rm pre}(f)=4.
\tag{22.6}
$$

Proof. Each strict slot has only one nonbaseline label: $K_1$ carries $B$ and $K_2$ carries $C$ outside its baseline positions. But the adjacent boundary six carries a third nonbaseline label $F$.

To exclude adaptive fee three, use frozen phase two's label $A$. Both phases four and five have label $B\ne A$ and no opportunity after index one. They must both leave the zero archive at that index. Its word starts zero by the full-tail obstruction; in bits $0ab$ the charges at four, five, six are $a,a\oplus b,b$. Selecting both four and five therefore forces $a=1,b=0$, and charge zero at six. The positive child $\{4,5\}$ can stop with $B$, but the zero child contains the actual phases one, two, and six with respective labels $C,A,F$. There is only one complete endpoint left. It cannot distinguish these three labels: phase two has zero charge, while selecting both one and six puts the different labels $C,F$ in the same final positive child; failing to select either leaves that label with $A$. Later rejection cannot help, since after the compulsory clearing bit all choices up to fee three are safe by (20.4). Thus the adaptive deadline fails, excluding every adaptive or preset fee at most three.

The necessity of the clearing bit is visible in a false relaxed construction. The formal charges one at all four vertices $3,4,5,6$ would be the literal word $101$. They would select the right boundary six along with four and five, allowing a later phase-six repair on that child. But its first bit one rejects every root-zero source at INITIAL tail three, merging the different original labels. Thus it is not an available full-target action. The retirement criterion (19.8) together with (19.6) detects exactly this obstruction.

For attainment use the common stream

$$
111\mid001\mid101\mid100.
\tag{22.7}
$$

Its post-root supports are $\{5,6\}$, $\{6,7,0,1\}$, $\{1,2\}$. At the second block the root-zero positive archive is $\{5,6\}$; at the third it separates phase five's $B$ from phase six's $F$ and stops. The root-zero zero archive is $\{1,2,4,7\}$. At the third block its positive child is $\{1,7\}$ with labels $C,A$, and its zero child is $\{2,4\}$ with labels $A,B$. The fourth block selects phase one in the former child and phase two in the latter, giving the correct two decoders. On the endpoint sibling, the third block selects zero and not three, so $D,E$ are identified by fee three. Root rejection and initial rejection have their independent prescribed labels.

The second word begins zero, clearing even current tail six. It ends with one; the third word's leading one makes a run of length two before its zero. The third word again ends with one, and the fourth's leading one likewise makes a run of length two before clearing. These runs are strictly shorter than $k=7$, on every INITIAL low tail and both values. Thus the fourth block is a paid literal repair on the same sources, not an abstract extra binary query. The upper bound four and the adaptive lower bound four prove (22.6). ∎

**命题 22.4（An odd outside count can still require a preset surcharge）。** At $Q=2,m=3,r=2$, put $\lambda(4)=B$, $\lambda(6)=\lambda(7)=S$, and $A$ at the other outside phases, with $A,B,S$ pairwise distinct and $D\ne E$. Choose arbitrary $R,L_\bot$. Then

$$
C_{\rm ad}(f)=3,\qquad C_{\rm pre}(f)=4.
\tag{22.8}
$$

Proof. The following proof uses the actual complete target, independently of any assertion about this layout. The adaptive controller in Proposition 22.2 still works with these labels: root-zero word $011$ creates $\{4,6\}$ with labels $B,S$, repaired at index two by $100$; its zero child $\{1,2,5,7\}$ has labels $A,S$, separated by $010$. The endpoint archive uses $000\mid010$. All source and seam arguments are the same literal arguments already given, so the adaptive fee is at most three and (20.1) makes it exact.

For preset impossibility at three, the first post-root word $0ab$ must select four and not five, since their labels are $B,A$ and both retire there against frozen baseline two. Hence $a=b=1$ and six is also selected. Its different label $S$ forces a next-row charge one at six. Phase seven stays on the zero archive and carries $S\ne A$, forcing its final charge one; phase one's label $A$ forces its final charge zero. The endpoint sibling forces final charge one at zero. Again the last window would have charges $1,1,1,0$, impossible for an even literal path. The argument is independent of whether an already constant child stops early, and every cheaper fee was excluded by the endpoint lower bound.

One attaining common stream is

$$
111\mid000\mid100\mid001.
\tag{22.9}
$$

Its post-root supports are $\varnothing$, $\{6,7\}$, $\{3,4\}$. The third block identifies both $S$ phases on the root-zero archive; the last separates $B$ at four from its remaining baseline phases, and separates endpoint three from endpoint zero on the root-positive archive. The paid zero block clears every low INITIAL tail; the later pulses have strict seams and no extra cleanup. This proves the exact preset fee four.

There are three nonbaseline outside phases here, an odd number. This does not contradict Theorem 21.2: phase six is an adjacent-window boundary and that theorem requires its label to be $A$. Removing that hypothesis changes the simultaneous boundary-repair equations, even though the slot labels themselves are simple. ∎

The distinctness of $B,S$ is necessary for the separation in (22.8). If instead $B=S\ne A$, the common stream $111\mid011\mid010$ costs exactly three. Its post-root supports are $\{4,6\}$ and $\{7,0\}$: the first positive outside child has the single label $S$ and stops, the last word separates $S$ at seven from the remaining baseline phases, and that same word separates zero from three on the endpoint sibling. The first post-root bit clears every INITIAL low tail, and (20.4) proves safety. Bound (20.1) proves optimality. Thus an unqualified preset-four assertion for this layout would fail under that label coincidence.

## 23. Reuse contracts and the unchanged all-target objective

**数学引文 23.1（Source-specific addition and mature background）。** Theorem 20.1 reuses the joint-source and first-zero interfaces of [S1, Convention 1.3, Lemmas 4.2–4.3, Theorems 3.1 and 5.2], the fixed original matched cycle of [S2, Theorem 14.1], and the ordered charge/inverse interfaces of [S10, Interface 2.1; S15, Sections 1–4]. All parameters, values, phases, tails and chronological observations refer to those same original suppliers through Chapter 1. It does not replace the recurrence by another source-encoding or transfer problem.

The retired-colour scan, right-frontier repair, and first-zero safety arguments in [S13, Definition 1.3 and Theorems 2.3–3.2] are supplied overlap: they concern tail-independent phase tables, coprime pre-return deadlines and their prescribed baseline phase. [S13, Theorem 8.4] supplies the local actual-support terminal criterion; [S15, Theorem 3.3] supplies general whole-archive response/seam certificates. Those generic continuation certificates and scan mechanisms are reused, not offered again as new mathematics. The addition in (19.4)–(20.3) is the explicit all-gcd first-return classification of the full threshold INITIAL target: a forced mixed-tail parent, an unrestricted wrapped terminal table, possibly empty frozen set, arbitrary adjacent-boundary labels, and the exact one-stream compatibility constraints linking that same parent’s endpoint sibling. The classification collapses every off-spine live archive to one retired label and at most one returning boundary, with a complete single paid repair; it does not ask a generic Bellman recursion to stand in for these obligations.

The supplied endpoint law [S20], integrated as Theorem 2.2, provides the earliest informative fee and the all-action root comparison for its constant-outside family; its lower-bound proof is reused with the same two endpoint sources. Its constant-outside upper bound cannot be transplanted to arbitrary $\lambda$. The arbitrary repeated-band spectrum in [S19], integrated in Chapter 3, uses $k=Qm$, its protected band spectrum and its stated freshness conditions. It does not assert the unrestricted table deadline or the batch law (21.2) on $T=Qm+r$. The supplied unified chapters through 14 ([S22]) and through 18 ([S23]) give near-critical injective tables, protected higher-tour spectra with multiple INITIAL tail bands, and their sharp guard-removal boundary. Their code-list, protected-support and guard hypotheses are preserved; the batches of Definition 21.1 spread across the actual first-tour slots without those guards. The leaf-forced recurrence (21.4), the empty-slot compensation, the terminal endpoint obligation and the one extra paid endpoint pulse are the new cost obligations behind (21.2), not a renamed protected-spectrum bound.

The supplied `original_repeated_guardrail_cost` in [D12] (the local mathematical supplier also designated D14) requires $g\ge2$, $m=gu$, $T=g(hu+\rho)$, $\gcd(u,\rho)=1$, at least three phase labels, a guarded support, and a target independent of every INITIAL tail on its specified value fibre. It is not applied to (19.3), which gives a different high-tail label and preserves its INITIAL meaning after the paid parent. No preset cost or coprime assertion is borrowed from that tail-independent declaration.

For adjacent mature theory, van den Bos and Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2](https://arxiv.org/pdf/1907.11034v2), Definitions 12, 14, 17, 20 and Figure 3, supply finite adaptive testing and irreversible-merge semantics. Here an input is an entire literal block and a reply is only its completed endpoint; their general distinguishing graphs supply none of the window charges or paid deadline laws. Chistopolskaya and Podolskii, *Parity Decision Tree Complexity is Greater Than Granularity*, [arXiv:1810.08668v1](https://arxiv.org/pdf/1810.08668v1), Section 2.2, allow arbitrary coordinate-subset parity queries and charge tree depth. The binary-leaf and label-separation principles are mature background, but the physical even path and compulsory clearing bit in (19.6) cannot be dropped in favour of such unrestricted queries. Türker, Hierons, Mousavi and El-Fakih, *Efficient State Identification for Finite State Machine-Based Testing*, [accepted manuscript](https://eprints.whiterose.ac.uk/id/eprint/230260/1/Ordered_Wset_Accepted.pdf), Definitions 11–15 and 18, treat state-identifying coverage, transfer-free paths, pairwise shortest separating prefixes and total transfer length. These objectives are different from one unknown INITIAL target's minimum worst-branch emitted-complete-block fee, even though transfer-free paths are allowed. None is used as a fee-preserving reduction. These precise source comparisons make no exhaustive absence, priority or worldwide originality claim.

**开放问题 23.2（The original quantifiers remain）。** Theorem 20.1 determines exactly whether fee $N$ is attainable for every arbitrary low-phase table within (19.1)–(19.3); Theorem 21.2 gives actual optimal adaptive and preset protocols and symbolic fees for its arbitrary sparse/repeated batch subfamily. Propositions 22.1–22.4 show why its empty-slot and boundary-label hypotheses change the optimum. A failed arbitrary-table deadline retains its exact larger minimum as an open question here, except for an explicitly settled family or example. The reused phase-recovery bound establishes attainability separately and is not promoted to that larger minimum.

Open Problems 9.1 and 18.2 retain their original goal: the exact minimum worst-branch number of actual emitted complete blocks for every arbitrary attainable immutable INITIAL record target and all original $k\ge2,m\ge1$, with the fixed $V_k\bmod2$, actual subgroup phases, full joint actual-history prior, independent absorbing rejection, both original control alphabets, and endpoint-only chronological archives. Arbitrary richer INITIAL tail partitions, genuinely competing feasible parents outside the forced family, later tours and repeated reactivation of general phase tables, value-dependent targets, and the remaining widths are not settled by these first-return or batch laws. Every wait, padding block and branch repair remains part of the emitted fee; offline table access, equality tests, search time and controller memory remain different resources.

[S22]: https://raw.githubusercontent.com/the-omega-institute/trureturing/610262cfc623cded080f2343151926829a14112b/docs/develop/theory/KBONACCI_INITIAL_TARGET_COST_THEORY.md
[S23]: https://raw.githubusercontent.com/the-omega-institute/trureturing/c8c3e97d072491eca90472d5fe3aa258415bdc5c/docs/develop/theory/KBONACCI_INITIAL_TARGET_COST_THEORY.md

## 追加锚（本行以下为增补区）
## 24. A common-stream cut criterion for arbitrary INITIAL targets

This chapter uses every $k\ge2,m\ge1$ in the original reader (1.1)–(1.2). Initial value or rejection is free, later readings are complete-block endpoints, and every block actually issued before stopping is charged. The target is an arbitrary map on the full INITIAL record set. The statements include both original alphabets.

**定义 24.1（All-one response fibres）。** Put $T=k+1$, $g=\gcd(m,T)$, and $P=g\mathbb Z/T\mathbb Z$. For $\theta\in P$, define

$$
I_t(\theta)=\bigoplus_{i=tm}^{(t+1)m-1}c_{\theta+i}.
\tag{24.1}
$$

$$
S_t(\beta)=\{\theta\in P:(I_0(\theta),\ldots,I_{t-1}(\theta))=\beta\}.
\tag{24.2}
$$

where $t\ge0$, $\beta\in\mathbb F_2^t$, and $S_0(\varnothing)=P$. For sources still successful after $t$ all-one blocks, these are precisely the phase fibres of their chronological endpoint archive. The INITIAL tail range is $0\le s<k-tm$; neither the current tail nor current value replaces the INITIAL arguments of $f$. Write $\operatorname{Const}$ for image size at most one, including an empty set.

The full joint sources in [S1, Convention 1.3] apply also when $m\ge k$: the history (1.3) contains a separating zero and a terminal run $s<k$, has length divisible by $m$, and realizes value, phase and tail simultaneously. Every one of its complete blocks is internally legal. To realize absorption in that alphabet, follow an actual endpoint of tail $k-1$ by $10^{m-1}$; its first bit rejects across the seam. Thus wide blocks do not restrict the source quantifiers. History lengths remain unobserved.

**定理 24.2（Exact common-cut criterion）。** For arbitrary $f:Q\to Y$ on the full INITIAL record set, $C_{\rm pre}(f)<\infty$ if and only if there exists one integer $a\in\{0,\ldots,k-1\}$, written

$$
a=qm+r,\qquad q\ge0,\quad 0\le r<m,
\tag{24.3}
$$

such that all the following conditions hold for each $v\in\mathbb F_2$. For every $t<q$ and every $\beta\in\mathbb F_2^t$,

$$
\operatorname{Const}\{f(v,\theta,s):\theta\in S_t(\beta),\ k-(t+1)m\le s<k-tm\}.
\tag{24.4}
$$

With $h=k-qm$, for every $\beta\in\mathbb F_2^q$,

$$
\operatorname{Const}\{f(v,\theta,s):\theta\in S_q(\beta),\ h-r\le s<h\},
\tag{24.5}
$$

and, separately for every $\theta\in S_q(\beta)$,

$$
\operatorname{Const}\{f(v,\theta,s):0\le s<h-r\}.
\tag{24.6}
$$

The quantifier over $a$ precedes the value and archive quantifiers. The $r=0$ rejection band in (24.5) is empty. The independent label $f(\bot)$ is returned free. This criterion concerns existence of a finite preset stream, without asserting its optimal fee.

**证明。** Until its first zero, a literal stream consists of ones. A source survives $u$ such bits precisely when $s+u<k$. Before absorption, its endpoint value changes are the $I_t(\theta)$, independent of its old tail. Consequently a raw successful archive at depth $t$ has exactly the product in Definition 24.1. If this archive stopped earlier, its entire earlier candidate set had one target label; every raw subgroup obtained by hypothetically continuing that archive is a subset of that set and also has one label. Such hypothetical continuation is used only to inspect sets, never as an emitted action or a charge.

First suppose the common stream has its first zero after $a<k$ ones. In each preceding all-one block, the rejected INITIAL tails are $k-(t+1)m\le s<k-tm$. At its endpoint, rejection discards the phase and intermediate value, retaining only the previous successful archive. If the archive is live, correctness forces that whole rejected band to have one label; if it already stopped, the subset argument gives the same condition. This proves (24.4).

In the block containing the zero, the $r$ leading ones reject precisely $h-r\le s<h$, with previous phase archive $S_q(\beta)$. The same argument proves (24.5). All lower tails at any one fixed phase survive those leading ones and have identical intermediate values. The first zero merges their tails, hence their complete current records. Every remaining bit and later endpoint is common. Correctness therefore forces (24.6), whether this archive is live or previously stopped. This is the actual first-zero loss of [S1, Lemmas 4.2–4.3]; no tail marginals from different histories have been combined.

A finite correct stream need not emit a zero at all. If its first zero is at or beyond $k$, or if all sources stop before any zero, normalize the existence argument to $a=k-1$. Extend an already unused all-one prefix only as a set calculation. Conditions (24.4) hold as above. In the block crossing the $k$th one, every still-live candidate in $S_q(\beta)\times\{0,\ldots,h-1\}$ would reject to one endpoint archive, so that whole set must have one label. If it had already stopped, the same constancy follows from its stopping leaf. This stronger condition implies (24.5)–(24.6) at $a=k-1$. It establishes an eligible normalized cut, without asserting that a stopped source actually executes the inserted zero.

Conversely, given an eligible cut, issue the one common literal prefix

$$
(1^m)^q\mid1^r0^{m-r}.
\tag{24.7}
$$

Every rejection archive returns the common label in (24.4) or (24.5). Surviving sources finish with tail zero; (24.6) makes the target constant on each fixed INITIAL phase among those sources. Apply the safe preset phase-recovery protocol [S1, Theorem 3.1], using the newly observed value as its increment baseline. Its current phase lies in $P$; subtract the known issued displacement $(q+1)m$ to recover the INITIAL phase and return its label. The all-one blocks have $m<k$ whenever $q>0$, and the mixed block has $r<k$, so they are internally legal. The mixed block ends zero and all phase probes have the supplied safe seams. Stop any constant archive earlier. Each remaining source follows this same stream; all emitted prefix and recovery blocks are paid. This proves sufficiency for both alphabets. ∎

**推论 24.3（Charged constructive bound）。** Any cut satisfying Theorem 24.2 gives

$$
C_{\rm pre}(f)\le q+1+L(k,m),
\tag{24.8}
$$

where the supplied safe phase protocol [S1, Theorem 3.1] has

$$
L(k,m)=
\begin{cases}
0,&p=1,\\
p-1,&m\ge2,\ p>1,\\
2T,&m=1,\ T\text{ odd},\\
2T+1,&m=1,\ T\text{ even},
\end{cases}
\qquad p=T/g.
\tag{24.9}
$$

Proof. The construction (24.7) pays $q+1$ blocks and the stated recovery stream pays at most $L(k,m)$. Early stopping can reduce this fee. No optimality of the recovery bound or of the chosen cut is asserted. ∎

**定理 24.4（Sharp complete-threshold family）。** For any $k\ge2,m\ge1$, choose $1\le a_v\le k-1$ and $L_v\ne H_v$ for each $v\in\mathbb F_2$. Cross-value coincidences are unrestricted. On every actual phase set

$$
f(v,\theta,s)=
\begin{cases}
L_v,&s<k-a_v,\\
H_v,&s\ge k-a_v,
\end{cases}
\qquad f(\bot)\text{ arbitrary}.
\tag{24.10}
$$

Then

$$
C_{\rm ad}(f)=\max_v\left\lceil\frac{a_v}{m}\right\rceil.
\tag{24.11}
$$

Writing $a_{\min}=\min(a_0,a_1)$ and $a_{\max}=\max(a_0,a_1)$,

$$
C_{\rm pre}(f)=
\begin{cases}
\lceil a_{\max}/m\rceil,&a_0=a_1\text{ or }m\mid a_{\min},\\
+\infty,&\text{otherwise}.
\end{cases}
\tag{24.12}
$$

**证明。** Fix one free-value fibre and one actual phase. The two INITIAL tails $k-a_v-1$ and $k-a_v$ have different labels. Before $a_v$ leading ones they both survive with equal outputs; an earlier zero merges them alive. Thus fewer than $\lceil a_v/m\rceil$ blocks cannot distinguish them. The literal prefix of $a_v$ ones followed, if necessary, by zero padding to its complete-block boundary rejects exactly the high band and preserves exactly the low band. Every rejection leaf is $H_v$ and every successful leaf is $L_v$. This attains the bound, with the free initial value choosing the fibre and its own protocol.

If $m\nmid a_v$, that pair cannot stop before the block containing position $a_v$. A first zero before $a_v$ merges it alive; a first zero after $a_v$, including an all-one containing block, rejects both members within that block, since there is no endpoint between their consecutive rejection times $a_v$ and $a_v+1$. Therefore any finite correct stream on this unresolved fibre has its first zero exactly after $a_v$ ones. If $m\mid a_v$, the endpoint after $a_v$ ones already separates rejection from success and returns both labels, so this fibre stops there and places no constraint on later bits.

For unequal thresholds with non-boundary $a_{\min}$, its forced first zero at $a_{\min}$ clears both differently labelled sources of the larger-threshold pair before either rejects. Both had survived all previous endpoints with one common archive, so this loss is irreversible. Preset fee is infinite. When the thresholds agree, their common threshold word works. When $m\mid a_{\min}$, issue ones through $a_{\max}$, padding its containing block with zeros if needed. The smaller fibre stops at its earlier all-one endpoint; the larger fibre attains its own threshold fee. No continuation is charged to the stopped fibre. The larger pair gives the matching lower bound, proving (24.12). This includes wide blocks, $g=1$, $p=1$, and every other gcd. ∎

**命题 24.5（Unequal-offset obstruction and stopped-boundary case）。** At $k=9,m=4$, thresholds $a_0=1,a_1=2$ and the same $L\ne H$ on both fibres give $C_{\rm ad}=1$ and $C_{\rm pre}=+\infty$. At $k=4,m=2,a_0=a_1=2$, both fees are one and the complete word $11$ attains them without emitting a zero.

Proof. In the first case $1000$ and $1100$ are the adaptive threshold words, and the respective same-phase pairs of INITIAL tails $(7,8)$ and $(6,7)$ force incompatible first-zero positions in any common stream. In the second case $11$ rejects exactly INITIAL tails $2,3$ and preserves tails $0,1$; all phases return the appropriate threshold label at that endpoint. The lower-bound pairs in Theorem 24.4 exclude fee zero in both cases. ∎

## 25. Exact unit-width envelope for arbitrary two-value targets

Fix $m=1$, $k\ge2$, $T=k+1$. All phases are actual. Write the INITIAL phase as $-j$ with $0\le j\le k$. At absolute issued-bit position $t$, a successful one changes the value precisely for $j\in\{t,t+1\}\pmod T$; a zero changes no value and clears the tail. Each bit is one paid complete block. These are chronological endpoint comparisons on one actual source.

**定义 25.1（Unit target and constant prefixes）。** For arbitrary $f:Q\to Y$, put

$$
F_v(j,s)=f(v,-j,s),\qquad\lambda_v(j)=F_v(j,0),
\tag{25.1}
$$

and

$$
\ell_v(j)=\max\{h\in\{1,\ldots,k\}:F_v(j,s)=\lambda_v(j)\text{ for every }0\le s<h\}.
\tag{25.2}
$$

Thus $1\le\ell_v(j)\le k$. This definition uses INITIAL tails even after their destructive updates. Constancy means image size at most one; an empty eligible minimum is $+\infty$.

**定义 25.2（Phase expression, cleared suffix and root-archive expressions）。** For any table $\lambda:\{0,\ldots,k\}\to Y$, put

$$
J=\max\bigl(\{j\ge1:\lambda(j)\ne\lambda(0)\}\cup\{0\}\bigr),
\tag{25.3}
$$

and let the supplied phase-only cost expression [S11, Theorem 3.1] be

$$
\phi_k(\lambda)=
\begin{cases}
0,&J=0,\\
\max\bigl(J,2+\mathbf1_{\{\lambda(1)\ne\lambda(2)\}}\bigr),&k\ge3,\ J>0,\\
3,&k=2,\ J=1,\\
2,&k=2,\ J=2,\ \lambda(1)=\lambda(2),\\
4,&k=2,\ J=2,\ \lambda(1)\ne\lambda(2).
\end{cases}
\tag{25.4}
$$

For $2\le a\le k$ define the following expression on the suffix $\{a,\ldots,k\}$:

$$
d(a,\lambda)=
\begin{cases}
0,&\lambda\text{ constant on }\{a,\ldots,k\},\\
1,&\lambda(a)=\lambda(a+1)\text{ and }\lambda\text{ constant on }\{a+2,\ldots,k\},\\
\max(2,B-a),&\text{otherwise},
\end{cases}
\tag{25.5}
$$

where the second line is considered only after the first fails, and

$$
B=\max\{j\in\{a,\ldots,k-1\}:\lambda(j)\ne\lambda(j+1)\}.
\tag{25.6}
$$

The last case has a nonempty maximum. A singleton suffix uses the first line and never refers to $\lambda(k+1)$. The exact cleared-suffix interpretation of this expression is proved below, rather than taken as a supplied theorem.

For each $v$, define $H_v$ by the first applicable line:

$$
H_v=
\begin{cases}
1,&\operatorname{Const}\{F_v(j,s):j\in\{0,1\},\ 0\le s<k-1\},\\
k+1,&\ell_v(0),\ell_v(1)\ge k-1\text{ and }\lambda_v(0)\ne\lambda_v(1),\\
\max(2,k-\ell_v(0),k-\ell_v(1)),&k\ge3\text{ and }F_v(0,k-2)=F_v(1,k-2),\\
+\infty,&\text{otherwise}.
\end{cases}
\tag{25.7}
$$

A cutoff $\tau\in\{1,\ldots,k-1\}$ is $v$-eligible when

$$
\operatorname{Const}\{F_v(j,k-z-1):z+1\le j\le k\}
\quad\text{for every }1\le z<\tau,
\tag{25.8}
$$

and

$$
\ell_v(j)\ge k-\tau\quad\text{for every }j\ge\tau+1.
\tag{25.9}
$$

For such a cutoff set

$$
\begin{aligned}
L_v(\tau)&=
\begin{cases}
\tau,&\lambda_v|_{\{\tau+1,\ldots,k\}}\text{ constant},\\
\tau+1+d(\tau+1,\lambda_v),&\text{otherwise},
\end{cases}\\
M_v(\tau)&=\max\left(L_v(\tau),\ \max_{2\le j\le\tau}\max(j,k-\ell_v(j))\right).
\end{aligned}
\tag{25.10}
$$

The inner maximum is zero at $\tau=1$. All $H_v,L_v,M_v$ are total costs measured from the original root, not costs to concatenate.

**引理 25.2a（Actual cleared-suffix cost）。** Suppose an actual acquired unit archive has common current value, current tail zero, and exactly INITIAL phase candidates $j\in\{a,\ldots,k\}$, with $2\le a\le k$. The next paid bit is at absolute issued position $a$, and the immutable target on each phase is $\lambda(j)$. Its minimum additional adaptive fee equals $d(a,\lambda)$ in (25.5). One common all-one continuation attains that fee, so this is also its minimum preset continuation fee. Any multiplicities of actual histories with the same phase and label are allowed.

**证明。** A constant suffix stops free. Otherwise one bit can succeed only by issuing one at position $a$, which queries precisely $\{a,a+1\}$ against its complement. No source rejects from tail zero in this bit. Both sides have one label exactly in the second line of (25.5), so that line has exact fee one.

In every other nonconstant case fee is at least two. For any adjacent differing pair $j,j+1$ with $j\ge a+2$, their coefficients at every position from $a$ through $j-2$ are both zero. They start with the same tail, acquire the same outputs, and take identical actions on an adaptive common archive. Even a common rejection cannot separate them. Their first possible separation is position $j-1$, requiring $j-a$ additional bits. The same lower bound is trivial for $j=a$ or $a+1$. Applying it at the largest differing boundary $B$ gives $\max(2,B-a)$.

For attainment, take $n=\max(2,B-a)$ consecutive ones from absolute position $a$. Since a nonconstant suffix requires $a\le k-1$, one has $n\le\max(2,k-a-1)\le k-1$. Thus no run reaches $k$ and every seam is legal. Its first endpoint divides $\{a,a+1\}$ from the later suffix. The second endpoint distinguishes $a$ from $a+1$ and peels $a+2$ from the suffix. Each further endpoint peels the next phase. All phases through $a+n$ are therefore identified, and the remaining suffix is constant because it lies beyond $B$. When $a+n>k$, the pair is already the whole suffix and the second endpoint still distinguishes it; the last queried absolute position is at most $k$. Returning the INITIAL label on these actual archives attains the lower bound. This proves the adaptive and common-continuation equalities, without any new observations inside a block. ∎

**定理 25.3（Exact adaptive unit envelope）。** If $\ell_v(j)=k$ for every $j$, set $A_v=\phi_k(\lambda_v)$. Otherwise the fibre is mixed. If its top row

$$
\{F_v(j,k-1):0\le j\le k\}
\tag{25.11}
$$

is not constant, set $A_v=+\infty$. In the remaining mixed case set

$$
A_v=\max\left(H_v,\ \min_{\tau\text{ $v$-eligible}}M_v(\tau)\right).
\tag{25.12}
$$

Then, for every arbitrary label set and table,

$$
C_{\rm ad}(f)=\max(A_0,A_1).
\tag{25.13}
$$

**证明。** A phase-only fibre is exactly the domain of [S11, Theorem 3.1], including constants and the $k=2$ exceptions. Its attaining constructions are literal streams, and its lower bounds hold for adaptive trees. The initial free value chooses the fibre, so the two whole-root costs combine by a maximum.

In a mixed fibre, root zero merges all tails at each phase and destroys some required distinction. Thus root one is forced. It rejects the entire top row to one archive, making (25.11) necessary. Its two successful archives are exactly

$$
\begin{array}{c|c|c|c}
\text{archive}&\text{INITIAL phases}&\text{INITIAL tails}&\text{current value}\ \hline
\mathcal H&\{0,1\}&0\le s<k-1&v\oplus1\\
\mathcal M&\{2,\ldots,k\}&0\le s<k-1&v.
\end{array}
$$

Both have current tail $s+1$. The rejection archive returns its common INITIAL label and stops at depth one. The two successful archives are siblings: their total fees must be maximized, never added.

On $\mathcal H$, a constant target stops at depth one, giving the first line of (25.7). If each of its two phase rows has a constant surviving prefix but those labels differ, the second bit cannot be one: it would reject the INITIAL tail $k-2$ from both phases into one archive with different labels. A zero at absolute position one clears safely. At all later positions $2,\ldots,k-1$ both phases have zero coefficient; their cleared tails and values remain common. They cannot separate before the one at position $k$, whose endpoint has total depth $k+1$. The safe word $1\,0^{k-1}1$ attains that depth. This is the second line.

In every other unresolved $\mathcal H$ case, some surviving phase row is tail-dependent, so a second-bit zero is impossible. A second-bit one is possible exactly when $F_v(0,k-2)=F_v(1,k-2)$, since those are the two rejected sources. If equality fails both actions lose a required distinction, proving infinity. If equality holds and $k\ge3$, the successful second endpoint separates phases zero and one: only phase one flips there. Each is then a phase-known archive with INITIAL tail range $0\le s<k-2$.

More generally, on a phase-known archive reached by $j$ successful leading ones, remaining tails satisfy $0\le s<k-j$. Its exact total stopping depth is $\max(j,k-\ell_v(j'))$ for its known phase $j'$. To prove this, if the remaining prefix is constant it stops at depth $j$. Otherwise tails $\ell_v(j')-1$ and $\ell_v(j')$ have different labels, survive indistinguishably before absolute depth $k-\ell_v(j')$, and any earlier zero merges them. Consecutive ones through that depth reject the larger tail and then leave a constant surviving prefix. Each earlier rejection on this phase-known branch identifies exactly one INITIAL tail and returns its own label. No clearing zero is needed. Applying this at depth two to phases zero and one gives the third line of (25.7). At $k=2$ these surviving prefixes are singletons, so the first two lines already cover every finite $\mathcal H$ case. Thus $H_v$ is its exact total-root cost.

On $\mathcal M$, follow the still-unidentified suffix through leading ones. After total depth $z\ge1$, that archive has exactly phases $j\ge z+1$, tails $0\le s<k-z$, and current value $v$. A one at position $z$ rejects INITIAL tail $k-z-1$ from every one of those phases, requiring precisely the constancy in (25.8); its successful flip identifies phase $z+1$, while the other successful archive is the next suffix. All previously peeled phases are separate acquired siblings. At phase $j$'s identifying endpoint of depth $j$, its best total cost is $\max(j,k-\ell_v(j))$ by the phase-known calculation above.

The first zero on the unidentified suffix, if any, occurs after a total of $\tau$ ones, with $1\le\tau\le k-1$ in normalized form. It merges every surviving tail at each of its phases, so (25.9) is necessary. All earlier rejected strips require (25.8). If this suffix stops before its zero, its entire remaining table is constant and the same conditions hold for that stopping depth $\tau$. Continuing all ones to depth $k-1$ leaves only phase $k$ and tail zero, so no later cutoff is needed. Thus every finite controller yields an eligible $\tau$.

At an eligible cutoff, each remaining phase has surviving label $\lambda_v(j)$. A constant suffix stops at depth $\tau$; otherwise the zero at position $\tau$ is paid, and the resulting archive is exactly the cleared suffix of Lemma 25.2a with $a=\tau+1$. Its optimal further cost is $d(\tau+1,\lambda_v)$. This proves $L_v(\tau)$, including its absolute fee origin. Together with the identified-phase siblings it gives the necessary $M_v(\tau)$ lower bound on that choice of cutoff.

Conversely, choose a minimizing eligible cutoff. Issue ones on the unidentified suffix until that depth, retiring each rejected strip to its constant label. Each peeled phase independently follows its optimal phase-known all-one continuation and stops. At the chosen suffix either stop at its constant label, or issue its clearing zero followed by the safe all-one continuation in Lemma 25.2a. These are actual paths on separate acquired archives; all their depths are measured from the one original root. Their maximum is exactly $M_v(\tau)$. Independently run the attained $\mathcal H$ continuation on its sibling. Every emitted bit is charged; no source is copied and no labels are reevaluated after clearing. This attains (25.12) and (25.13), and failure of either archive condition proves unattainability. ∎

**定理 25.4（Exact preset unit envelope）。** Put

$$
\Lambda(j)=(\lambda_0(j),\lambda_1(j)).
\tag{25.14}
$$

If both fibres are phase-only, then

$$
C_{\rm pre}(f)=\phi_k(\Lambda).
\tag{25.15}
$$

If either fibre is mixed, first require the top row (25.11) to be constant separately on each value fibre. If this fails, preset fee is infinite. Otherwise a common cutoff $\tau\in\{1,\ldots,k-1\}$ is eligible exactly when (25.8) holds for both values and

$$
\begin{aligned}
\ell_v(j)&\ge k-\tau &&(v\in\mathbb F_2,\ 0\le j\le k),\\
F_v(0,k-2)&=F_v(1,k-2) &&(v\in\mathbb F_2,\ \tau\ge2).
\end{aligned}
\tag{25.16}
$$

In particular, the prefix condition covers phases zero and one and every phase peeled before the cutoff. For $\tau=1$ its cost is

$$
D(1)=\max\left(
\begin{cases}1,&\Lambda(0)=\Lambda(1),\\k+1,&\Lambda(0)\ne\Lambda(1),\end{cases}
\quad
\begin{cases}1,&\Lambda|_{\{2,\ldots,k\}}\text{ constant},\\2+d(2,\Lambda),&\text{otherwise}.
\end{cases}
\right).
\tag{25.17}
$$

For $\tau\ge2$ its cost is

$$
D(\tau)=
\begin{cases}
\tau,&\Lambda|_{\{\tau+1,\ldots,k\}}\text{ constant},\\
\tau+1+d(\tau+1,\Lambda),&\text{otherwise}.
\end{cases}
\tag{25.18}
$$

The exact preset fee is $\min_{\tau\text{ common-eligible}}D(\tau)$, including infinity for an empty eligible set. These are common-stream costs; no maximum of fibre-optimal preset costs is asserted.

**证明。** Under any one literal stream, the two free-value fibres have identical source partitions at each chronological depth: on successful sources their values differ by their initial-value offset, and rejection is common within the same tail/phase subset. Therefore one can test constancy separately on each fibre, equivalently use the ordered pair of INITIAL labels on each common source partition. This correspondence does not permit different actions on the fibres. If both targets are phase-only, the lower bound in [S11, Theorem 3.1] applies to the pair table, and its literal attaining stream works for both values. This proves (25.15).

If a fibre is mixed, the common root must be one. Hence root rejection forces a constant top row on each fibre, including any phase-only fibre accompanying it. Let $\tau$ be the number of leading ones before the stream's first zero. A successful source of fixed phase $j$ after those ones has INITIAL tails $0\le s<k-\tau$, all with identical previous archives on its value fibre. If they stopped earlier, their labels were already constant; otherwise the first zero merges them. Thus the first condition of (25.16) is necessary for every phase, even a phase already identified by its value archive.

For $\tau\ge2$, the second one rejects the phase-zero and phase-one sources at tail $k-2$ in one $\mathcal H$ archive; it also rejects the $\mathcal M$ strip at that tail. This gives the second condition of (25.16) and the $z=1$ case of (25.8). The later unresolved suffix rejections give all other cases of (25.8). For a source that stopped before these bits, these sets remain subsets of its constant stopping archive, so the same necessity holds without executing any continuation on it. If there is no useful first zero, at $k\ge3$ normalize to $\tau=k-1$: all-one successful signatures then identify every phase, and the remaining INITIAL tail is zero. At $k=2$, two consecutive ones reject both members of the unresolved $\mathcal H$ archive, so they could finish only if already constant at depth one, which admits $\tau=1$. A stream whose first zero is later gives no extra feasible case. Every finite preset controller therefore admits a common-eligible normalized cutoff.

At $\tau=1$, all surviving phase prefixes have length $k-1$ and are constant by (25.16). The $\mathcal H$ archive either has one pair label and stops at depth one, or its two phases have different pair labels. In the latter case the next one would merge differently labelled rejected sources; clearing zero is necessary, and no bit before absolute position $k$ can distinguish the two phases. Its exact total depth is $k+1$. The $\mathcal M$ archive either stops at depth one, or requires the paid zero at position one and the exact suffix cost $d(2,\Lambda)$. This proves the lower bound (25.17).

For simultaneous attainment at $\tau=1$, issue the common prefix $10$. If the endpoint pair is unresolved, continue ones at positions $2,\ldots,k$, stopping it at depth $k+1$. Its run has length $k-1$, hence is safe. Every nonconstant $\mathcal M$ suffix obtains the prefix of these same ones required by Lemma 25.2a and stops at depth $2+d(2,\Lambda)\le k+1$. If the endpoint pair is already constant, use only the suffix continuation needed for $\mathcal M$. When both archives are constant, stop all sources after the root one and emit no zero. Thus their worst actual fee is exactly the maximum in (25.17).

For $\tau\ge2$, after $\tau$ ones each successful phase $j\le\tau$ is identified and its surviving prefix has one label by (25.16). Those archives stop by depth $\tau$, including the two endpoint phases. Every earlier rejection was legal by the top-row condition, (25.8), and the endpoint equality. The still-unidentified suffix is constant phase by phase. If its pair labels are all equal, all sources stop by depth $\tau$; otherwise issue one zero at position $\tau$ and then the attained suffix stream of Lemma 25.2a. The all-one prefix and this zero have legal chronological seams, and the later run has length less than $k$. This attains (25.18).

For the matching cutoff lower bound, a nonconstant suffix cannot stop before its first zero; the first zero costs one and Lemma 25.2a forces its stated remaining depth. A constant suffix gives an apparent lower bound $\tau$ unless every source has already stopped at some smaller common depth $d$. In that event the raw all-one archives at depth $d$ are all constant on both fibres. All rejection-strip conditions up to $d$ hold, every phase prefix of length $k-d$ is constant, and the unresolved suffix pair label is constant. Thus $d$ is itself a common-eligible cutoff, with $D(d)=d$ (or $D(1)=1$). Such an unused later cut never lowers the minimum. Minimizing over eligible cuts gives the exact lower bound and attained common stream in every case, including all early-stopped archives. ∎

**推论 25.5（Sharp finite boundary and preset-infinite family）。** For $k\ge3$, every finite adaptive or preset cost above is at most $k+1$, and that bound is attained. On both value fibres choose $A\ne B$ and set $F_v(0,s)=A$, $F_v(1,s)=B$ for $s<k-1$, and every other entry $A$. Then both fees are $k+1$.

For every $k\ge3$, there is also a finite-adaptive, preset-infinite target. On both fibres put

$$
F_v(1,0)=B,\qquad F_v(k,s)=B\quad(0\le s<k-1),
\tag{25.19}
$$

and every other entry $A$, with $A\ne B$ and arbitrary $f(\bot)$. Exactly

$$
C_{\rm ad}=\begin{cases}4,&k=3,\\k-1,&k\ge4,\end{cases}
\qquad C_{\rm pre}=+\infty.
\tag{25.20}
$$

Proof. The phase-only expression is at most $k$ for $k\ge3$, and the endpoint expression is at most $k+1$. Every phase-known sibling costs at most $k-1$. A nonconstant cleared suffix has $\tau\le k-2$ and costs $\tau+1+\max(2,B-\tau-1)\le k+1$; its one-bit case is smaller. Thus every finite minimum has the asserted boundary. The first example has $H_v=k+1$ and a constant $\mathcal M$ archive; $1\,0^{k-1}1$ is a common attained stream.

For (25.19), $\ell_v(1)=1$, $\ell_v(k)=k-1$, and the endpoint equality at tail $k-2$ holds. Consequently $H_v=\max(2,k-1)$. Cutoff one is eligible on $\mathcal M$. Its suffix labels are $A$ at $2,\ldots,k-1$ and $B$ at $k$, so Lemma 25.2a gives total suffix cost four when $k=3$, three when $k=4$, and $k-1$ when $k\ge5$. Every $\tau\ge2$ fails (25.8) already at $z=1$, where phase $k$ has label $B$ and phase two label $A$. These are the adaptive lower bounds and actual attained sibling protocols. For a preset cut, phase one's prefix condition forces $\tau\ge k-1$, while that same $z=1$ strip excludes every $\tau\ge2$. Hence there is no common cut.

At $k=2$, mixed fibres have finite adaptive fee at most three, while the phase-only fee-four exception of (25.4) remains. A whole target with one fee-four phase-only fibre and another fee-one tail-dependent fibre therefore has adaptive fee four. Its preset fee is infinite if the phase-only fibre is nonconstant: the mixed fibre forces root one, whose top-row rejection destroys the phase-only distinction. ∎

**命题 25.6（Peeled-tail and endpoint obstructions）。** On both fibres at $k=4$, let $F_v(2,1)=B$ and every other entry be $A\ne B$. Then both exact fees are three, attained by $111$. At $k=3$, placing the sole $B$ at either $F_v(1,1)$ or $F_v(0,1)$ gives both fees infinite.

Proof. In the $k=4$ example the second successful one identifies phase two, but its INITIAL tails zero and one still have distinct labels and identical successful outputs. A zero among the first two bits merges them alive; $11$ leaves them unresolved. Thus every two-bit adaptive path on this pair fails. The third one rejects exactly its tail-one source; every other rejected source and surviving source has label $A$, while that identified-phase rejection has label $B$. This is an actual fee-three common stream. Equivalently (25.16) excludes cutoffs one and two, and cutoff three attains the fee. In the $k=3$ examples root zero loses the same-phase distinction, while root one leaves $\mathcal H$ unresolved. Its next zero merges that pair alive, and its next one merges the two phase-zero/phase-one sources of tail one with labels $A,B$ into absorption. Every legal next action destroys a required distinction, proving infinity without a finite-horizon inference. ∎

## 26. Source contracts and the remaining boundary

**数学引文 26.1（Source-specific reuse and deductions）。** The joint-source saturation, complete-block observation contract, INITIAL labels, first-zero loss and safe phase bound are [S1, Convention 1.3, Definition 2.1, Proposition 2.3, Lemmas 4.2–4.3, Theorems 3.1 and 5.2]. Theorem 24.2 adds one existential common cut across both free values and all archives; it normalizes already-stopped archives rather than requiring an executed first zero on them. Theorem 24.4 adds exact fee and literal compatibility for its complete threshold family at every width and gcd. No bound from a supplied phase protocol is represented as an optimum for an arbitrary target.

The phase-only unit expression (25.4), its adaptive lower bounds and its literal attaining streams are [S11, Theorem 3.1](https://raw.githubusercontent.com/the-omega-institute/trureturing/ef2fddd6bab3fe4b861b07e4c01577e942912ab8/docs/develop/theory/KBONACCI_COPRIME_PHASE_TARGET_COST.md). The new cleared-suffix law is Lemma 25.2a, with its own silent adjacent-pair lower bound and safe all-one attainment; its consumers are Theorems 25.3–25.4. Neither cited supplier is assigned this suffix law. The mixed-tail additions explicitly identify the two actual root archives, every peeled phase and rejection strip, all surviving INITIAL tail prefixes, and the chronological common-stream constraint. These are reader-specific ordinary deductions, rather than a new generic belief-game or a combination of separately optimal preset fibres. The source comparison is limited to the stated claims and the adjacent literature contracts in Mathematical citation 7.2; no absence or priority conclusion is asserted.

**定义 26.2（Remaining original objective）。** The unchanged general objective is the exact minimum worst-branch number of actual emitted complete blocks for every arbitrary attainable immutable INITIAL target at every $k\ge2,m\ge1$. The unit-width arbitrary-table adaptive and preset cases are settled by Theorems 25.3–25.4, with preset infinity retained. The all-width common-stream attainability criterion and complete-threshold exact family are Theorems 24.2 and 24.4. They do not supply the exact fee of an arbitrary target at $m\ge2$, nor a universal adaptive-to-preset conversion. Previously supplied finite deadlines remain restricted to their stated horizons. Every target outside the exact scopes retains its original source, output and fee obligations; no restricted increment replaces this objective.

## 追加锚（本行以下为增补区）

## 27. Positive offspring and the adaptive zero-difference spine

**定义 27.1（Chronological continuation and availability lists）。** Use the original matched reader, whole-history prior, immutable INITIAL labels, free initial reading, independent absorbing rejection and paid endpoint-only actions of [S24, Definitions 1.1–1.3 and Interface 1.4]. In this chapter assume $m\ge3$, $k\ge2m$, $T=k+1$, $g=\gcd(m,T)$ and $P=g\mathbb Z/T\mathbb Z$. A successful acquired archive at paid depth $b$ has already recorded a zero in its literal input. Its paid depth satisfies $b\ge1$, and the recorded zero lies in its own issued prefix, not in an unobserved source history. Its actual INITIAL phase support is $S\subseteq P$, with common current value, common current tail $\sigma<k$, and one well-defined immutable label $\lambda(j)$ for each $j\in S$. All witnesses share the entire chronological observed archive; they are continuations of their own actual initial histories, not separately assembled coordinates. If different INITIAL labels have merged at the same phase, such an archive is not successfully completable and is outside this definition.

Write $W_t=[tm,(t+1)m]\pmod T$ in the ordered physical-path convention of (1.4). For any actual support $A$ and chronological offset $b$, let

$$
\mathcal L_j(d;b)=\{z\in\mathbb F_2^d:\operatorname{supp}(z)\subseteq\{i<d:j\in W_{b+i}\}\}.
\tag{27.1}
$$

Define $K(A,\lambda;b)$ as the least $d$ admitting one $z_j\in\mathcal L_j(d;b)$ for every $j\in A$, such that different labels have different codes. Equal-label phases may have different codes. Empty and constant supports have $K=0$. These are the actual phase lists of [D11, Definitions 2.3 and 3.1], expressed in the physical $j$ indexing of Chapter 1. Their use below does not extend D11's noncoprime realization theorem to a coprime support without a separate literal proof.

**定理 27.2（The coprime one-hole extension）。** Suppose $g=1$. At every actually acquired archive of Definition 27.1 with $|A|\le m$ and $\sigma\le k-m$, for every $d\ge0$ there is an adaptive continuation of additional fee at most $d$ if and only if there is a preset continuation of that fee, if and only if codes as in (27.1) exist. Consequently

$$
D_{\rm ad}(A,\lambda;b,\sigma)
=D_{\rm pre}(A,\lambda;b,\sigma)=K(A,\lambda;b).
\tag{27.2}
$$

This includes every chronological offset, wrapped window, repeated label and window with only one missing physical phase.

Proof. The successful-path code extraction and early-stopping convention are those of [S15, Theorems 3.3–3.4]: at a nonconstant common-tail archive a rejecting action merges all candidates into the same absorbing output, so it cannot complete the target. On every actual successful path record the successive endpoint differences and pad with zero after its leaf. Unavailable physical phases give zero coordinates. Equal padded codes force the same observed prefix through the earlier stopping leaf, so different labels cannot have equal codes. Thus every adaptive protocol of depth at most $d$ supplies (27.1). This direction makes no independent-row assumption.

For sufficiency take such a code assignment and prescribe its $i$th row on $A\cap W_{b+i}$. A window has $m+1$ physical vertices. If it has at least two holes relative to the fixed $A$, [S15, Lemma 2.1] constructs a literal realization containing a zero. If it has exactly one hole, necessarily $|A|=m$ and $A\subset W_{b+i}$. Even full-path parity fixes the missing charge and gives a unique word by (1.5). If that word is $1^m$, complement coordinate $i$ of every code $z_j$, $j\in A$. Every phase of $A$ is available at this coordinate, so the new codes remain in their lists. Complementing a common coordinate is a bijection on code vectors and preserves every required separation. The new row differs from the all-one word's response on $A$, so its unique inverse is not $1^m$ and contains a zero. Apply this operation independently at each such row. The fixed support is the original $A$ throughout; no hole is borrowed from a different output child.

Every resulting word contains a zero. The first leading run is at most $m-1$, so its seam satisfies $\sigma+\alpha\le k-1$. Its terminal tail is at most $m-1$. Thereafter every seam has length at most $2m-2<k$. All prescribed code rows therefore occur on one literal stream, with every padding bit and every block emitted and paid. Its label decoder is well-defined by code separation. This proves all three conditions equivalent at every finite horizon. Finiteness follows from the safe paid phase-recovery stream in [S1, Theorem 3.1]; restriction of its phase-distinguishing codes to $A$ gives $K\le T-1$. Empty and constant archives stop freely. ∎

**定理 27.3（Geometry and tails of actual positive offspring）。** At any archive of Definition 27.1, issue an actual successful block at index $a$. Let $A$ be its positive-difference child. Every nonconstant such child has current tail at most $k-m$. Its actual phase count is at most $m$, except when $g=1$, $m$ is odd and $A=W_a$ has all $m+1$ physical vertices. In that exceptional case the emitted word is $101\cdots01$ and the child's current tail is one.

Proof. Every positive child is the intersection of the parent support with the actual charge support of one literal word, hence is contained in $P\cap W_a$. For $g>1$, this last set has $m/g+1\le m$ phases. For $g=1$ it has $m+1$ vertices. Selecting all of them requires full charge one on the entire path; its total charge is even precisely when $m$ is odd. Formula (1.5) then gives the unique alternating word starting and ending one, with a recorded internal zero and terminal tail one. If not all vertices are selected, the count is at most $m$.

If the issued word contains a zero, its terminal tail is at most $m-1\le k-m$. It remains to consider $1^m$, whose full charge support is just $\{am,(a+1)m\}$ modulo $T$. If the old tail is zero, the new tail is $m\le k-m$. If the old tail is positive, the preceding block ended in one, so its charge at the common endpoint $am$ was one. The present archive took one of that preceding block's two successful difference branches. If it took difference zero, $am$ is absent from its support. If it took difference one, its support is contained in $W_{a-1}$. Since $T\ge2m+1$, the vertex $(a+1)m$ is not in $W_{a-1}$: the two consecutive physical windows overlap only at $am$. Thus in either case the next positive child has at most one phase. Its one well-defined INITIAL label is constant. The existence of the preceding block is guaranteed by the already-recorded zero and the paid chronological archive; its last charge is an actual preceding response, not an invented extra observation. Therefore a nonconstant positive child of $1^m$ must have old tail zero, proving the tail claim. ∎

**定理 27.4（The acquired odd-width full-window exception）。** Suppose the exceptional child in Theorem 27.3 is acquired at depth $a+1$, so $g=1$, $m\ge3$ is odd, $A=W_a$, and its common tail is one. For every immutable phase-label table on this actual archive,

$$
D_{\rm ad}(A,\lambda;a+1,1)
=D_{\rm pre}(A,\lambda;a+1,1)=K(A,\lambda;a+1).
\tag{27.3}
$$

Proof. Successful-path extraction again gives $K\le D_{\rm ad}$. The safe phase-recovery stream of [S1, Theorem 3.1] gives separating availability codes of length $T-1$, so $K\le T-1$. It suffices to realize any separating code assignment of length $d\le T-1$ without increasing its length.

Rotate the physical coordinates for this proof so that $A=[0,m]$. Subsequent window starts are $nm\pmod T$, $1\le n\le d$. No such window is $A$, because $\gcd(m,T)=1$ and $n<T$. It therefore has at least one hole relative to $A$. Two length-$m+1$ consecutive arcs on a cycle of length at least $2m+1$ have an intersection of size $m$ only when their starts differ by $1$ or $-1$. To verify this assertion, write a different start as $u\in\{1,\ldots,T-1\}$. If $u\le m$, then $u+m\le2m<T$, so the intersection is $[u,m]$ of size $m+1-u$, equal to $m$ only for $u=1$. If $u>m$, the window misses $A$ unless it wraps; on wrapping its intersection is $[0,u+m-T]$ of size $u+m-T+1\le m$, equal to $m$ only for $u=T-1$. Thus these two adjacent starts are the only one-hole cases. Thus a one-hole window is $[1,m+1]$ or $[-1,m-1]$. In particular its hole is an endpoint. Consecutive chronological windows themselves share just one endpoint. Since $A$ has only one vertex outside a one-hole window, each of its adjacent chronological windows intersects $A$ in at most two vertices, and hence has at least two holes when $m\ge3$.

At a two-hole row use a zero-containing inverse supplied by [S15, Lemma 2.1]. At a one-hole row the inverse is unique. If it contains a zero, use it. If it is $1^m$, its response on $A$ selects exactly one phase $h$: the other physical endpoint of that window is its hole. Consequently this row's positive prefix uniquely identifies $h$ within the whole $A$. Set every later code coordinate of $h$ to zero and stop that actual phase at this endpoint. All code separations remain valid: $h$ differs from every other phase at this very coordinate, and the codes of other phases are unchanged. Repeat this operation in chronological order as necessary.

These all-one rows are isolated, because both neighbouring rows have at least two holes. Immediately before any such row, the tail is at most $m-1$, or is the initial tail one if this is the first row. Thus the all-one seam is at most $2m-1<k$. Immediately after such a row enforce first bit zero in the next literal word. If the one-hole window was $[1,m+1]$, the next window's leading vertex is $m+1$, outside $A$. If it was $[-1,m-1]$, that leading vertex is $m-1=h$, whose future code was just made zero. In both cases the leading charge can be zero; the next window has at least two holes, so there is another hole after its leading vertex to compensate parity. [S15, Proposition 2.2], or directly (1.5), therefore realizes the entire next row with first bit zero. It clears the possibly long tail created by the all-one row without adding a block. Its new tail is at most $m-1$.

Every other row follows a zero-containing word or is itself zero-containing; its seam is bounded by $2m-2<k$. The initial seam is at most $m<k$. All words belong to one preset stream on the original actual $A$, and all live sources are safe. The only suffix changes were on already uniquely identified phases, with permitted archive-dependent stopping; no response needed by another label was altered. Hence codes of length $K$ have actual fee $K$, giving the reverse inequality. This is a construction on this acquired full-window archive, not on arbitrary large supports or unrelated high tails. ∎

**定理 27.5（Only the zero-difference spine needs adaptive actions）。** At every archive of Definition 27.1, there is an optimal adaptive continuation whose actions can depend on new differences only until the first positive difference. Thereafter the continuation is one fixed literal stream on that acquired positive child, with archive-dependent stopping. Its exact additional fee is $K$ of that child's actual support and immutable labels at its actual chronological offset. Both original alphabets have this property.

Proof. The source-faithful safe phase-recovery construction [S1, Theorem 3.1] makes every archive in the definition finitely completable: one well-defined label is retained per phase, and the known paid displacement recovers INITIAL phase from current phase. Minimum worst fees are therefore attained integers; choose an optimal finite adaptive tree and stop every constant archive immediately. At any nonconstant node its next action must be successful, because the common tail makes rejection simultaneous and absorbing.

By Theorem 27.3 every nonconstant positive child has low current tail and at most $m$ phases, or is exactly the exceptional acquired archive. In the coprime small-support case use Theorem 27.2; in the exceptional case use Theorem 27.4. In the noncoprime case use [D11, Theorems 2.2 and 3.2–3.4] after the bijective rescaling $j\mapsto j/g$, $m\mapsto m/g$, $T\mapsto T/g$. Its high-tail deleted availability point does not apply here, since the actual child tail is at most $k-m<k-1$. Thus that supplier's code value is exactly (27.1). Its sparse literal realization is used only within $g\ge2$, $m\ge3$, $m<k$ and a common-tail acquired archive. Constant children instead have fee and $K$ zero.

Replace each subtree rooted at the first positive difference on the original zero-difference spine by its optimal preset stream. Its exact fee $K$ is no greater than the old subtree's worst fee, so the root's worst fee does not increase. Because the original tree was optimal, the new one is optimal. The choices remaining adaptive are exactly those on the chronological all-zero difference path. All preceding payments remain part of the total fee, and all later stream words are paid on the actual branches which emit them. Different first-positive children can require different streams; this establishes branchwise preset optimality and asserts no common global preset stream for all siblings. ∎

## 28. Whole-colour reactivation after the first-return deadline

**定义 28.1（Two colours in a guarded nonterminal strict slot）。** Retain all original source, target and fee conventions of Chapter 1. Let

$$
Q\ge2,\quad m\ge3,\quad 2\le r<m,\quad T=Qm+r,\quad k=T-1,\quad
 g=\gcd(m,r),\quad P=g\mathbb Z/T\mathbb Z,\quad N=Q+1.
\tag{28.1}
$$

Choose $1\le t<Q$ and disjoint nonempty actual sets

$$
U,V\subseteq P\cap[tm+g,(t+1)m-2g].
\tag{28.2}
$$

The interval has $m/g-2$ actual vertices, so these assumptions imply $m/g\ge4$. Let $A,B,C$ be pairwise distinct. Give low phases $0,m,U,V$ labels $D,E,B,C$, respectively, and every other actual low phase label $A$. Here $D,E,R,L_\bot$ are arbitrary, including $D=E$ and every coincidence with $A,B,C$. The complete target is

$$
f_3(v,-j,s)=
\begin{cases}
R,&k-m\le s<k,\\
D,&s<k-m,\ j=0,\\
E,&s<k-m,\ j=m,\\
B,&s<k-m,\ j\in U,\\
C,&s<k-m,\ j\in V,\\
A,&s<k-m,\ j\notin\{0,m\}\cup U\cup V,
\end{cases}
\qquad f_3(\bot)=L_\bot,
\tag{28.3}
$$

on both free-value fibres. Set

$$
M=\min(\max U,\max V),\qquad
L=\left\lceil\frac{T+M}{m}\right\rceil.
\tag{28.4}
$$

Maxima refer to the displayed ordinary representatives, not cyclic order.

**定理 28.2（Exact paid later-slot law）。** For every target in Definition 28.1 and both original alphabets,

$$
C_{\rm ad}(f_3)=C_{\rm pre}(f_3)=L\in\{N+t,N+t+1\}.
\tag{28.5}
$$

Proof. The full-source joint realizations are (1.3). A root containing a zero after $a<m$ ones merges, at each phase, the actual INITIAL tails $k-m-1,k-m$: both survive that zero, since $k-m+a<k$. At least one low phase has label different from $R$, because $A,B,C$ are distinct. At such a phase this merger loses a required label difference. A correct root is therefore $1^m$. It rejects precisely the high tails, which return $R$, and leaves actual low archives $H=\{0,m\}$ and $Z=P\setminus H$ as in [S24, Theorem 20.1]. This reasoning does not require $D\ne E$.

For an all-action lower bound choose the three actual phases

$$
u=\max U,\qquad v=\max V,\qquad z=(t+1)m-g.
\tag{28.6}
$$

They have pairwise different labels $B,C,A$ and $z>\nu,v\ge M$. Choose one common free value and INITIAL tail zero for these three whole-history sources. Their only opportunity before absolute emitted position $T+M-1$ is the first-tour block of index $t$. Indeed their first coefficient positions are $j-1,j$, both strictly inside that block; their next coefficient positions are $T+j-1,T+j$. The guard also keeps $z$ strictly inside the same block. Before index $t$ their outputs and tails are identical. Any rejecting action on their shared archive would merge all three distinct labels, so every action on this archive is successful. The index-$t$ endpoint has only two successful output values, hence puts two of these three differently labelled sources on the same chronological child. Their tails are common, and until a second opportunity every later successful response on this child is zero; a rejecting response is common and absorbing. They cannot separate by a total fee $d<L$, since $dm<T+M$ implies that every emitted position is less than $T+M-1$. A deterministic controller cannot return their different labels. This excludes every smaller-fee literal adaptive controller and therefore every smaller-fee preset stream. It uses actual sources and common histories, not the count of labels alone.

We construct one common attaining stream. Interchange the names of the two colour sets if necessary so that $\max U=M<\max V$. The corresponding labels are interchanged too. This is possible because the sets are disjoint and their maxima are different. Thus $U$ is the colour to reactivate, and $V$ is the whole colour retired on the first tour. Put

$$
h=(t+1)m,\qquad a=tm-r,\qquad c=(t+1)m-r,\qquad v_*=\max V.
\tag{28.7}
$$

All $a,c,h,v_*$ are actual phases. The first second-tour window meeting $U$ has block index $Q+t$, starts at the unwrapped residue $a$ and ends at $c$. The next has index $Q+t+1$ and ends at $c+m$. We have $a>0$, $\min U>a$, and $\max(U\cup V)\le h-2g<c+m$. Thus $L=N+t$ if $M\le c$, and $L=N+t+1$ if $M>c$.

All unspecified blocks in the construction are $0^m$ and are issued and paid whenever a source has not stopped. The root is $1^m$. At index $t$ use the even full physical charge set

$$
E_t=V\cup\bigl(\{h\}\text{ if }|V|\text{ is odd, otherwise }\varnothing\bigr),
\tag{28.8}
$$

inverted by (1.5). It starts zero because $V$ lies strictly inside the slot and the left endpoint is uncharged. If $|V|$ is even its terminal tail is zero. If $|V|$ is odd, the positive root-zero child is $V\cup\{h\}$, with labels $C,A$. At index $t+1$ include the pulse $10^{m-1}$ with charge support $\{h,h+1\}$. On this acquired child it selects only $h$, so both labels are returned at this paid endpoint. On the continuing zero archive $h$ is already absent and any actual $h+1$ has label $A$, hence any additional positive child is constant $A$. No phase of $U$ is touched. In the even case every phase of $V$ stops immediately at index $t$. Thus the whole colour $V$ has genuinely stopped before its second tour; its later charges may be used without adding it to a live acquired archive. Nonactual $h+1$, when $g>1$, is never a source.

For $t>1$, at index $Q$ use the endpoint pulse with support $\{T-1,0\}$, namely $0^{r-1}1\,0^{m-r}$. If $t=Q-1$ and $|V|$ is odd, also include the preceding paragraph's repair pulse in this same block: the two words are combined by bitwise XOR, which here means prescribing their symmetric-difference even charge supports and applying the single inverse (1.5). Their one positions are distinct. On $H$ this block selects only phase zero and returns $D,E$; if those labels coincide, $H$ may already have stopped at the root. On $Z$ all extra selected high-end phases have label $A$. At index $Q+t-1$ use the last-position pulse $0^{m-1}1$ with support $\{a-1,a\}$. Their actual members still live in the continuing $Z$ archive are low baseline phases to the left of $U,V$, with label $A$; if $a-1=m$, that endpoint has label $E$ and has already stopped on the $H$ sibling. Its positive $Z$ child is constant and stops. In particular phase $a$ has actually been removed from the zero continuation before index $Q+t$.

For $t=1$, the preparatory pulse and the endpoint return occupy the same index $Q$, so use instead the even support $\{0,a\}$ at that index. If $Q=2$ and $|V|$ is odd, add the repair support $\{Qm,Qm+1\}$ by symmetric difference in the same row. The ordered wrapped path places zero at local vertex $r$ and $a=m-r$ at its right endpoint. Without the optional first-position repair the inverse is $0^r1^{m-r}$. On $H$ it selects zero, hence returns $D,E$. On $Z$ it selects the baseline phase $a$; the optional repair adds only the already selected boundary $h=Qm$ and the baseline actual phase $Qm+1$. The same repair decoder separates $V$ from $h$, and every other positive $Z$ child here has label $A$. Thus $a$ is again genuinely absent from the continuing zero archive. This choice also covers $a=1$, where naively combining two isolated pulses would cancel the endpoint charge at zero.

It remains to query the whole returning colour $U$ on its actual second-tour windows. If $M\le c$, at index $Q+t$ prescribe the even support

$$
E=U\cup\bigl(\{a\}\text{ if }|U|\text{ is odd, otherwise }\varnothing\bigr).
\tag{28.9}
$$

The phase $a$ has already stopped with label $A$. On the live zero archive the positive child is exactly $U$, hence returns $B$, and the zero child contains only baseline labels $A$. All other low branches have already returned their respective immutable labels. This finishes at fee $N+t=L$, including the case $M=c$ at the window endpoint.

If $M>c$, put $U_-=U\cap[a,c]$ and $U_+=U\cap(c,c+m]$. The latter is nonempty. At index $Q+t$ start with $J=U_-\cup\{c\}$ and use the even support

$$
E_-=J\cup\bigl(\{a\}\text{ if }|J|\text{ is odd, otherwise }\varnothing\bigr).
\tag{28.10}
$$

On the continuing zero archive this selects $U_-$ and $c$. If $c\in U$, all selected live phases have label $B$. If $c\in V$, it has already stopped. Otherwise $c$ has label $A$ and, if $U_-$ is nonempty, this positive child needs one paid repair; if $U_-$ is empty it stops with $A$. In every case $c$ is absent from the continuing zero archive after this row. Because $v_*=\max V>M>c$ and $v_*<c+m$, the actual phase $v_*$ is available in the next window and has already stopped with colour $C$.

At index $Q+t+1$ start with $J'=U_+\cup\{c\}$ and use

$$
E_+=J'\cup\bigl(\{v_*\}\text{ if }|J'|\text{ is odd, otherwise }\varnothing\bigr).
\tag{28.11}
$$

The added $v_*$ is a genuinely completed phase of the first-tour colour, not an unavailable algebraic mask. On the zero-continuation archive the positive child is exactly $U_+$ and returns $B$, while its zero child returns $A$. On a pending positive child from (28.10), the phases of $U_-\setminus\{c\}$ are outside the new window and have difference zero; the baseline phase $c$ has difference one. That very same complete block therefore repairs this child and returns $B,A$ correctly. The already stopped phase $v_*$ and the removed phase $a$ supply no extra source to either decoder. This is one global literal stream, finishing at fee $N+t+1=L$.

Finally check every physical seam rather than extending the old deadline's safety bound. The first post-root block starts zero: if $t>1$ it is an issued zero block, and if $t=1$ it is (28.8), whose first bit is zero. Every low INITIAL tail, including $k-m-1$, is therefore cleared after the root. The scan word (28.8) contains a zero and has tail at most $m-1$. An immediately following repair has leading run one, or two if it coincides with the endpoint pulse and $r=2$, so the seam is at most $m+1<k$. Each other endpoint pulse starts zero and ends zero; the combined repair/endpoint block still ends zero because $m-r\ge1$. The later preparatory last-position pulse for $t>1$ follows zeros, has leading zero and tail one. For $t=1$ the preparatory endpoint row has terminal tail $a=m-r\le m-2$, including its optional isolated first-bit repair; its leading run is zero or one and is safe after the scan. Therefore the first returning row (28.9) or (28.10), even if it is all-one, has entering tail at most $m-2$ or one and total initial run at most $2m-2<k$.

In the two-window case (28.10) leaves tail at most $m$. The next row starts with charge one at $c$, but its first subsequent charged vertex is $\min U_+$: the compensation vertex $v_*$ lies strictly beyond $M$. Hence its leading one run is $\min U_+-c\le M-c\le r-2g$. Its seam is at most $m+r-2g\le2m-3<k$. The last physical endpoint $c+m$ is uncharged, so (28.11) ends zero. All intervening waits are literal zeros, and every internal run is shorter than $k$ because $m<k$. All branches are safe through their actual stopping point; no cleanup block is omitted. Initial $\bot$ returns $L_\bot$ freely and root rejection returns $R$ at fee one. Each free value decodes its own differences on this same stream. Arbitrary endpoint, high and bottom label coincidences do not change the acquired supports or any of these decoders. The lower bound and actual attainment prove (28.5). ∎

## 29. One literal stream across the two free-value fibres

**定义 29.1（Value join）。** For any original $k\ge2,m\ge1$ and record target $f$, set

$$
\Gamma(\theta,s)=\bigl(f(0,\theta,s),f(1,\theta,s)\bigr).
\tag{29.1}
$$

View $\Gamma$ as a target independent of the actual initial and current scalar value, on both free-value fibres. Give initial $\bot$ any separately prescribed pair label. Initial rejection is already freely distinguished and imposes no condition on the positive-fee stream.

**定理 29.2（Exact preset value-join law, including infinity）。** For either original alphabet, for every record target and all original parameters,

$$
C_{\rm pre}(f)=C_{\rm pre}(\Gamma).
\tag{29.2}
$$

Proof. A fixed literal stream has a value-independent phase/tail trajectory and rejection time. Before rejection, changing the INITIAL value bit complements every scalar endpoint output; after rejection both readings are $\bot$. This is the exact symmetry of the original bit updates [S1, Definition 1.2 and Convention 1.3; S24, (1.2)], valid also when $m\ge k$, when a block itself contains $1^k$, and for every allowed cross-block rejection. No intermediate reading is supplied by this symmetry.

Suppose a preset controller for $f$ has uniform fee bound $d$. Use its very same literal stream on an actual source. From the actual acquired endpoint archive and known initial value $v$, deterministically form the two scalar-output archives whose initial values are zero and one by complementing precisely the successful readings as necessary. Issued words, paid depths and $\bot$ entries are the same in both. Run the original stopping/decoding rule on each of these archives. When one rule stops, retain its label; continue the actual stream until the other stops. Both stopping times are at most $d$, because the same phase and INITIAL tail with either value have actual whole-history realizations and the original controller was correct on both. The output pair is (29.1).

This is a deterministic decoder applied to one actual chronological stream. It executes no second experiment, makes no source copy and imports no observation from another actual branch. The symmetry computes the other value's output string from the one already observed. Rejection cannot invalidate a label already decoded, and any rule still running sees the same prescribed absorbing suffix. The worst paid depth is the maximum of the two original stopping times, hence at most $d$. This proves $C_{\rm pre}(\Gamma)\le C_{\rm pre}(f)$ whenever the latter is finite.

Conversely use a preset controller for $\Gamma$, remember the free INITIAL value, and return that component of the acquired pair. The initial bottom branch returns its independent prescribed $f(\bot)$ freely. This uses the same stream and no greater fee, giving the reverse inequality at every finite bound. Therefore existence of a controller bounded by each $d$ is equivalent in the two directions, which proves equality in $\mathbb N\cup\{+\infty\}$. ∎

**定理 29.3（Unbounded finite preset excess from competing value fibres）。** Keep (28.1)–(28.2). Choose labels $A\ne B$ and $D\ne E$, with arbitrary cross coincidences, high label $R$ and initial bottom label. In free-value fibre zero put $B$ on low outside phases $U$ and $A$ on every other low outside phase. In free-value fibre one put $B$ on $V$ and $A$ elsewhere. In both fibres give low endpoints $0,m$ labels $D,E$ and high tails label $R$. Then

$$
C_{\rm ad}(f)=N,\qquad C_{\rm pre}(f)=L,
\qquad C_{\rm pre}(f)-C_{\rm ad}(f)\in\{t,t+1\}.
\tag{29.3}
$$

Proof. Each individual fibre is precisely [S24, Definition 21.1] with its sole nonempty batch in the nonterminal slot $t$. Since $Q\ge2$, another batch is empty. [S24, Theorem 21.2] therefore gives exact preset and adaptive fee $N$ in each fibre, under all gcds and all allowed label coincidences. The supplied free-value fibre convention [S1, (2.2) and Theorem 5.2; S24, Definition 1.3] lets the freely observed initial value select its own controller, so the full adaptive fee is the maximum $N$, with the same lower bound obtained in either fibre. This is reused fibre maximization, not a new adaptive solver.

The joined low outside labels are $(A,A)$ off $U\cup V$, $(B,A)$ on $U$ and $(A,B)$ on $V$. They are pairwise distinct. The joined endpoint labels are $(D,D),(E,E)$, the high label is $(R,R)$ and the bottom pair is independent. Thus $\Gamma$ is exactly a target in Definition 28.1. Theorem 28.2 and then Theorem 29.2 give its exact common-stream fee $L$ and the asserted difference.

For an explicit unbounded family fix $m=5,r=2$, take arbitrary $Q\ge2$, $t=Q-1$, $U=\{5t+1\}$ and $V=\{5t+2\}$. Here $g=1$, the guard holds, $M=5t+1$ and $L=N+t$. The excess is $Q-1$, which is unbounded. These finite costs apply to the complete original INITIAL target, with full tail ranges and free values, not to an isolated already acquired phase table. ∎

**定理 29.4（Disjoint feasible roots force infinite preset fee）。** For every $2\le m<k$ and $1\le\alpha<m$, choose two distinct tail labels in each fibre, with arbitrary coincidences between fibres. In fibre zero put one label on $s<k-\alpha$ and the other on $s\ge k-\alpha$; in fibre one put one label on $s<k-m$ and the other on $s\ge k-m$. Labels are constant over actual phases, and initial bottom has an arbitrary independent label. Then

$$
C_{\rm ad}(f)=1,\qquad C_{\rm pre}(f)=+\infty.
\tag{29.4}
$$

Proof. Both tail classes are nonempty whole-history sources by the original joint-source supplier (1.3), at every actual phase and each value. Neither fibre can stop at the free root. Fibre zero is acquired in one block by $1^\alpha0^{m-\alpha}$: rejection occurs exactly for $s\ge k-\alpha$, and every smaller tail reaches the zero and completes. Fibre one is acquired by $1^m$: it rejects exactly $s\ge k-m$. Since the free initial value selects the appropriate literal action, the adaptive fee is exactly one under both alphabets.

Every correct fibre-zero first word must contain its first zero exactly after $\alpha$ ones. To prove this against all words, suppose its first zero is after $a<m$ ones. If $a<\alpha$, the adjacent INITIAL tails $k-\alpha-1,k-\alpha$ both survive that zero, then merge at the same phase with identical observed archive and different required labels. If $a>\alpha$, those same tails both reject before that zero, becoming indistinguishable absorbing sources. If the word has no zero, it is $1^m$, and those same two tails both reject because $m>\alpha$. None of these mergers can be repaired at a later complete endpoint. Thus $a=\alpha$ is necessary; later bits do not change this root requirement.

Every correct fibre-one first word must be $1^m$. A zero after any $a<m$ ones lets the adjacent INITIAL tails $k-m-1,k-m$ both survive and merge. They again have different required labels. The feasible first-word sets of the two nonconstant fibres are therefore disjoint. A preset controller must emit the same first word in both, since both require a positive-fee action; archive-dependent stopping after that word cannot recover a difference already erased inside it. No correct common literal stream exists, irrespective of its proposed later horizon. Initial bottom stops for free and introduces no exception. This infinite preset boundary is a producer/control incompatibility, not a deficiency of a terminal decoder. ∎

## 30. Supplying statements and remaining quantifiers

**数学引文 30.1（Source-specific new bridges and exact reuse）。** The full original joint-source and fee contract is the immutable [S24, Chapter 1], with its direct credited suppliers [S1, Definition 1.2, Convention 1.3, Definition 2.1, Proposition 2.3, Theorem 3.1, Lemmas 4.2–4.3 and Theorem 5.2], [S2, Theorem 14.1] and [S10, Interface 2.1]. Whole-archive successful-path extraction, arbitrary-hole inverses and strict seam interfaces are [S15, Lemma 2.1, Proposition 2.2 and Theorems 2.3–3.4]. The noncoprime code conversion is [D11, Definitions 2.3 and 3.1 and Theorems 2.2 and 3.2–3.4], applied only at its actual hypotheses; the coprime one-hole and acquired full-window constructions are Theorems 27.2 and 27.4. The first-tour batch law used for the individual value fibres is exactly [S24, Theorem 21.2], including empty terminal batches. Theorem 28.2 supplies the later exact fee, with a new all-action three-source lower bound and an explicit one-stream second-tour realization. It does not extend the old first-tour retirement condition beyond its deadline. Availability lists retain one code per actual phase and allow distinct codes within one label class; no phase-count bound is substituted for this condition. These are ordinary source-specific deductions; no exhaustive literature priority assertion is made.

**定义 30.2（Unresolved original goal and retained boundaries）。** The original objective remains the exact minimum worst-branch emitted complete-block fee for every attainable immutable INITIAL target, for all $k\ge2,m\ge1$, with legal attainment under both alphabets. Theorem 27.5 restricts the adaptive decisions after a recorded first zero when $m\ge3,k\ge2m$; it does not select the best first-zero parent or identify one common stream across its siblings. Theorem 27.2 covers low-tail acquired supports of at most $m$ phases. Theorem 27.4 covers the stated chronological full-window offspring with tail one; arbitrary larger coprime supports and unrelated high-tail supports still require their actual seam conditions. Theorem 28.2 settles its guarded nonterminal two-colour family, including all label coincidences allowed in Definition 28.1, and does not give the optimum for arbitrary repeated batches, arbitrary multi-colour later slots, unguarded endpoints or every subsequent tour. Theorem 29.2 is universal for preset value joining but does not replace adaptive fibre maximization or resolve competing first-zero parents. The finite separation and infinite boundary in Theorems 29.3–29.4 retain preset infinity and leave the universal adaptive optimum unchanged as the goal. Widths $m=1,2$ and the region $k<2m$ are outside Theorem 27.5's continuation scope. The arbitrary $m=1$ adaptive and preset classification is already settled by Theorems 25.3–25.4, as retained in Definition 26.2, including preset infinity. For $m\ge2$, the remaining width-two and $k<2m$ cases, richer attainable INITIAL-tail partitions, and full joint global-stream compatibility outside the proved families remain within the unresolved original goal.

[S24]: https://raw.githubusercontent.com/the-omega-institute/trureturing/186832198cce5e1f2cf8c840689b087d1bbc0941/docs/develop/theory/KBONACCI_INITIAL_TARGET_COST_THEORY.md

## 追加锚（本行以下为增补区）
## 31. The full INITIAL common-cut response space in the noncoprime narrow region

**约定 31.1（Original sources, values and chronological indices）。** Throughout Chapters 31–35 assume

$$
3\le m<k,\qquad T=k+1,\qquad g=\gcd(m,T)\ge2,\qquad
P=g\mathbb Z/T\mathbb Z,\qquad p=T/g,\qquad D=\left\lfloor\frac{k-1}{m}\right\rfloor.
\tag{31.1}
$$

Use exactly the matched reader (1.1)–(1.2), the full joint actual-history prior of Convention 1.2, and the immutable INITIAL target and emitted-complete-block fee of Definition 1.3. Both original alphabets have all the same $m$-bit actions in (31.1), since $m<k$. A word's membership in either alphabet does not remove its cross-block rejection test. The initial scalar value is free; an initially rejected source is distinguished independently and returns $f(\bot)$ at fee zero.

Index the INITIAL phase by $j=-\theta\pmod T$, with $j\in P$. At paid block index $t$ put

$$
u_t=tm\pmod T,\qquad W_t=[u_t,u_t+m]\pmod T,\qquad
I_t(j)=\mathbf1_{\{u_t,u_t+m\}}(j).
\tag{31.2}
$$

The interval is the ordered physical path in Interface 1.4; its endpoints are distinct because $m<T$. For $\beta\in\mathbb F_2^t$ define

$$
S_t(\beta)=\{j\in P:(I_0(j),\ldots,I_{t-1}(j))=\beta\},\qquad h_t=k-tm.
\tag{31.3}
$$

For an arbitrary target $f$ on the complete INITIAL record set, use the full value join of Definition 29.1, in these coordinates:

$$
\Gamma(j,s)=\bigl(f(0,-j,s),f(1,-j,s)\bigr),\qquad
\Lambda(j)=\Gamma(j,0).
\tag{31.4}
$$

Constancy of a pair-valued map means constancy of both components separately. It does not require the two components to be equal, or identify an INITIAL label with a later scalar value. By Theorem 29.2, the preset fee for $f$ is the preset fee for this joined target, including infinity. This equality is credited reuse; adaptive value joining retains its separately supplied scope.

Every record used below is an actual joint source. In particular, for each $(v,j,s)$ use the single history (1.3): choose $\ell$ divisible by $m$, congruent to $-j$ modulo $T$, and at least $s+2$; its first bit and final $s$ ones give value $v$, its endpoint gives phase $-j$, and its separating zero gives precisely tail $s$. The same history provides all three coordinates. Subsequent arguments apply the one prescribed continuation to each such history. They do not assemble a value, phase and tail from separate realizations or condition on an unobserved history length.

**定义 31.2（Eligible common cuts and all-one stopping depths）。** Write $\operatorname{Const}$ for image size at most one, including the empty image. A cut $a=qm+r$ is eligible if $0\le a<k$, $0\le r<m$, and

$$
\begin{aligned}
&\operatorname{Const}\{\Gamma(j,s):j\in S_t(\beta),\ h_t-m\le s<h_t\}
&& (0\le t<q,\ \beta\in\mathbb F_2^t),\\
&\operatorname{Const}\{\Gamma(j,s):j\in S_q(\beta),\ h_q-r\le s<h_q\}
&& (\beta\in\mathbb F_2^q),\\
&\Gamma(j,s)=\Lambda(j)
&& (j\in P,\ 0\le s<k-a).
\end{aligned}
\tag{31.5}
$$

These are exactly the supplied common-cut conditions (24.4)–(24.6) applied to the supplied value join: (31.3) merely changes $\theta$ to $-j$, and the surviving interval contains $s=0$, which identifies its constant with $\Lambda(j)$. Thus (31.5) is not a replacement attainability criterion. In particular its quantifier chooses one $a$ before either free-value fibre or any archive. It permits $q=D$ and $r=0$; an empty rejection rectangle imposes no condition.

An all-one stopping depth is an integer $d\in\{0,\ldots,D\}$ such that

$$
\begin{aligned}
&\operatorname{Const}\{\Gamma(j,s):j\in S_t(\beta),\ h_t-m\le s<h_t\}
&& (0\le t<d,\ \beta\in\mathbb F_2^t),\\
&\operatorname{Const}\{\Gamma(j,s):j\in S_d(\beta),\ 0\le s<h_d\}
&& (\beta\in\mathbb F_2^d).
\end{aligned}
\tag{31.6}
$$

At $d=0$ the second condition says that $\Gamma$ is constant on all successful INITIAL records. The two scalar-value fibres of $f$ may still have different constant labels. Conditions (31.6) describe a stream stopped without issuing any first-zero block.

**定理 31.3（Exact simultaneous first-zero parent cube）。** Fix an eligible cut $a=qm+r$. In the parent block at index $q$, prescribe the empty initial run when $r=0$ and otherwise $r$ leading ones:

$$
B_0=\cdots=B_{r-1}=1,\qquad B_r=0.
\tag{31.7}
$$

For each actual local vertex $i\in\{0,g,2g,\ldots,m\}$, put

$$
A_0=\{0\},\qquad A_m=\{m-1\},\qquad
A_i=\{i-1,i\}\quad(0<i<m).
\tag{31.8}
$$

The possible successful parent-response rows are precisely zero outside $P\cap W_q$ and, at $j=u_q+i$, satisfy

$$
\xi_i\in
\begin{cases}
\left\{\displaystyle\bigoplus_{b\in A_i}B_b\right\},&A_i\subseteq\{0,\ldots,r\},\\
\mathbb F_2,&A_i\not\subseteq\{0,\ldots,r\}.
\end{cases}
\tag{31.9}
$$

Every combination in this product is realized by one and the same word satisfying (31.7). Its first zero is exactly at $r$; its successful sources are exactly the earlier all-one survivors with $s<k-a$; its final tail is at most $m-r-1\le m-1$. The rejected sources in that block are exactly $S_q(\beta)\times[h_q-r,h_q)$ in each earlier archive. These rejection and response data belong to the same parent word.

Proof. At every successful source, (1.4) gives the response at local vertex $i$ as the XOR of the bits indexed by $A_i$. Actual vertices have spacing $g\ge2$. Consequently the sets (31.8) are pairwise disjoint: consecutive internal pairs are separated or adjacent without sharing a bit, and neither endpoint singleton shares a bit with an internal pair. The two endpoint singletons are also disjoint, since $m\ge3$. If all bits of $A_i$ were prescribed in (31.7), its XOR is fixed. Otherwise choose one unprescribed bit in $A_i$, set the other unprescribed bits there to zero, and set the chosen bit to the desired response XOR the already prescribed bits. Different coordinates use disjoint unprescribed bits, so all choices coexist in one word. Set any other unprescribed bits to zero. This constructs every row in (31.9). Conversely (1.4) forces its fixed coordinates and its zero response outside the window. Ordered paths retain the same conclusion on a wrap; no vertex repeats because $m<T$.

Before $B_r=0$ the total emitted input consists of $a$ ones. Hence an INITIAL tail survives precisely when $s+a<k$. All higher tails still present at depth $q$ reject among the $r$ leading ones, without exposing their intermediate values. Every lower tail reaches the prescribed zero, resets, and completes the block safely: the remaining input has fewer than $m<k$ bits. The final tail is bounded by the length of that suffix. These facts establish the asserted joint threshold, response and tail information. ∎

The cube includes endpoint constraints. For example, when $r=m-1$ the right endpoint response is forced to zero; when $r=0$ the left endpoint response is forced to zero. A free charge assignment on all actual vertices would lose these restrictions and would not describe the INITIAL parent.

## 32. One lawful continuation across all values and archives

**引理 32.1（Simultaneous sparse rows after an arbitrary first-zero parent）。** In (31.1), suppose one parent satisfying (31.7) has just completed successfully. At every later chronological index $t>q$, prescribe an arbitrary row $x_t:P\to\mathbb F_2$ supported on $P\cap W_t$. Any finite sequence of these rows is realizable by one fixed literal continuation, simultaneously for every surviving earlier archive and both free INITIAL values. All its blocks succeed, and every prescribed zero or waiting block is emitted and paid.

Proof. This uses the noncoprime simultaneous-row construction [D11, Theorem 2.2]. Its literal word in the physical coordinates of Chapter 1 is

$$
\begin{aligned}
B_t(ig)&=x_t(u_t+ig) &&(0\le i<m/g),\\
B_t(m-1)&=x_t(u_t+m),\\
B_t(b)&=0 &&\text{at every other bit position }b.
\end{aligned}
\tag{32.1}
$$

All residues on the right are taken modulo $T$. For an actual phase $j$, a bit at $ig$ contributes only at $j=u_t+ig$: its coefficient index is a multiple of $g$, so it can hit $0$ modulo $T$ but cannot hit $-1$ modulo $T$. The bit at $m-1$ contributes only at $j=u_t+m$: its coefficient index is $-1$ modulo $g$, so it can hit $-1$ but cannot hit $0$. This verifies the entire actual row directly from (1.2), including its zero entries outside $W_t$. Nonactual physical vertices need no source or label; their charges supply the full-path parity automatically through this actual word.

The allowed one positions are $0,g,\ldots,m-g,m-1$. Position one is absent. If $g=2$, then $m$ is even and $m\ge4$; if $g\ge3$, position one is again absent and $m\ge3$. Thus the leading run is at most one. Only the final two allowed positions can be adjacent, and they are adjacent only when $g=2$; internal runs and terminal tails are at most two. The parameter region forces $k\ge5$: the only possibility with $k=4$ and $3\le m<k$ is $m=3$, whose gcd with five is one. After the parent, the old tail is at most $m-1\le k-2$. Therefore the first sparse word's leading seam has length at most $m<k$. Every later seam has length at most $2+1=3<k$. The internal runs are also shorter than $k$. All words are consequently safe for every parent's surviving source.

The proof never assumes that those sources have a common current value or a common observed archive. They have a common final tail from the same parent word, and their phases at chronological index $t$ are exactly $-j+tm$. Value affects neither safety nor the endpoint difference formula. Equation (32.1) therefore supplies one literal word for the union of all siblings, with their different scalar values retained. No branch selects a different word and no separately optimized sibling stream is flattened. An all-zero row gives the actual word $0^m$ and costs one if the source is still running. ∎

**引理 32.2（Successful global columns retain every stopping rule）。** Consider a correct preset controller for the joined target, with uniform fee at most $H$, whose common stream actually issues a first-zero block at index $q$, after $a=qm+r<k$ ones. Its parent satisfies (31.9), and $a$ satisfies (31.5). There is a matrix on every actual INITIAL phase,

$$
x_t(j),\qquad 0\le t<H,\quad j\in P,
\tag{32.2}
$$

whose rows at $t<q$ are $I_t$, whose row at $q$ is its actual parent response, and whose later rows vanish outside $P\cap W_t$, such that

$$
\Lambda(j)\ne\Lambda(j')\quad\Longrightarrow\quad
(x_0(j),\ldots,x_{H-1}(j))\ne(x_0(j'),\ldots,x_{H-1}(j')).
\tag{32.3}
$$

Here $H\ge q+1$. Rows may be inspected on already stopped sources as a set calculation, but no such calculation adds an emitted-block fee to those sources.

Proof. Apply the necessity proof of the supplied Theorem 24.2 at this actual first-zero location, through Theorem 29.2. Before the zero, each raw successful archive is $S_t(\beta)\times[0,h_t)$. Each preceding all-one block sends its rectangle $S_t(\beta)\times[h_t-m,h_t)$ to the same absorbing endpoint; the parent likewise sends $S_q(\beta)\times[h_q-r,h_q)$ to one absorbing endpoint. On a live archive, correctness forces the joined target to be constant on this rectangle, since absorption permits no later distinction. On an already stopped archive the rectangle is a subset of its homogeneous stopping leaf and is again constant. At every fixed phase, all tails $s<k-a$ survive the leading ones with identical observed histories and identical intermediate values. If they are still running, the first zero merges their full records; if already stopped, they shared that stopping archive. Either case forces their joined labels to agree with the label at $s=0$, namely $\Lambda(j)$. This establishes every part of (31.5) at the given $a$, including archives that do not execute the parent. The actual parent word has exactly (31.7), so Theorem 31.3 gives its row.

For the column argument take one actual source with INITIAL value zero and INITIAL tail zero at each $j\in P$, using (1.3). All these representatives could successfully traverse the whole literal prefix through the parent, because $a<k$ and the zero clears their tails. Some representatives can already have stopped; their hypothetical continuation is used only to define response coordinates. Their labels are $\Lambda(j)$ and their successful chronological differences before the parent are $I_t(j)$.

After the parent, all representatives have the same tail, independently of phase and scalar value. As long as the common suffix is successful, its literal response row is defined on the whole $P$ by (1.4) and is zero off $W_t$. If the common suffix first reaches a block that would reject, that rejection is simultaneous for every representative and for every still-running successful low-tail source. Within each prior observed archive, all still-running candidates would then give $\bot$ and have no future distinction. Correctness forces their joined INITIAL labels to be homogeneous already before this block. Stop each such archive there, and truncate this unused rejection and its suffix. The earlier stopping leaves remain unchanged. This gives a correct controller with no greater fee and a common successful suffix on all representatives. If fewer than $H$ rows remain, append zero response rows, represented by actual $0^m$ words in the formal extension.

If two representatives of different labels had equal whole columns, their initial free readings and their successful endpoint differences would coincide up to the earlier of their stopping times in this normalized controller. They would consequently have the same acquired archive there. A deterministic stopping/decoding rule must then stop both with the same label, a contradiction. This argument covers stopping before the parent, at the parent, and on any later row. The zero extension cannot remove an earlier difference. Hence (32.3) holds. It retains all earlier archive information in the columns themselves, without merging siblings or taking a maximum of their separate optima. ∎

The truncation in this lemma is used only after the first zero, when tails really are common. Before that zero, the different INITIAL tails make rejection partial, and the rejection rectangles in (31.5) are indispensable. A post-zero row replacement is not a replacement of the INITIAL parent's leading threshold.

## 33. The exact finite common-cut GLOBAL preset fee

**定义 33.1（A single joined chronological certificate）。** For an eligible cut $a=qm+r$, a depth $d\ge q+1$ is admitted by a common-cut certificate if one matrix

$$
(x_t(j))_{0\le t<d,\ j\in P}
\tag{33.1}
$$

has all of the following properties. Its rows for $t<q$ equal $I_t$. Its row at $q$ belongs to the actual first-zero cube (31.9), with zero entries off $W_q$. For every $t>q$, its entries are arbitrary on $P\cap W_t$ and zero outside. Its full columns separate different joined low-tail labels:

$$
\Lambda(j)\ne\Lambda(j')\quad\Longrightarrow\quad x_{<d}(j)\ne x_{<d}(j').
\tag{33.2}
$$

A same-label phase pair may have different columns. Every phase retains its own column, including one that is currently silent, previously identified, or later reactivated. Earlier all-one rows and the actual parent row are part of these columns, rather than an uncharged preliminary code. There is only one matrix for all successful archives and both INITIAL values.

Let $\mathcal A(f)$ be the set of all depths satisfying (31.6). Let $\mathcal Z(f)$ be the set of depths admitted by (33.1)–(33.2) for some eligible cut, restricted to

$$
q+1\le d\le D+p.
\tag{33.3}
$$

Both sets are finite. The target's table has finitely many entries; only their equality relations enter these conditions. No evaluation-time bound is implicit in the definition.

**定理 33.2（Exact arbitrary-INITIAL preset law in the noncoprime proper-narrow region）。** For every arbitrary immutable INITIAL target $f$, with the joint sources, free readings, independent bottom and actual emitted fees in Convention 31.1, under either original alphabet,

$$
\boxed{\displaystyle
C_{\rm pre}(f)=\min\bigl(\mathcal A(f)\cup\mathcal Z(f)\bigr),\qquad
\min\varnothing=+\infty.}
\tag{33.4}
$$

Every admitted depth constructs one lawful preset stream of at most that many actual emitted complete blocks. Every uniformly bounded stopping rule supplies an admitted depth no greater than its bound. In particular, any finite optimum is at most $D+p$. The law optimizes the first-zero location, every possible response of that same first-zero parent, and all subsequent chronological rows on one global stream. It asserts no equality between the arbitrary INITIAL adaptive and preset fees.

Proof. First construct the protocols supplied by each certificate. For $d\in\mathcal A(f)$ issue the all-one stream $(1^m)^d$. At depth $t+1$, a newly rejected source has prior successful archive $\beta$ and belongs exactly to the rectangle in the first line of (31.6). Its joined label is fixed, so return it immediately. At depth $d$, each still-successful archive is precisely $S_d(\beta)\times[0,h_d)$ and has a fixed joined label by the second line. All sources have now stopped. Any earlier homogeneous archive can stop as soon as it is homogeneous. Initial bottom remains its separate zero-fee branch. Each running source pays exactly its emitted prefix length, at most $d$; no first-zero word is appended to this stream.

For $d\in\mathcal Z(f)$ choose its eligible cut and matrix. Issue $q$ all-one blocks. Choose the one actual parent word constructed in Theorem 31.3 for the prescribed row at $q$. Then choose every later word by (32.1). Theorem 31.3 gives exactly the eligible partial rejection band at the parent, while Lemma 32.1 guarantees the simultaneous legal suffix on every surviving archive. Earlier rejections and the parent rejection return the joined labels of their homogeneous rectangles in (31.5), using the previous archive as well as the absorbing endpoint. Every final successful source has $s<k-a$, hence label $\Lambda(j)$ by (31.5), and has acquired the complete column $x_{<d}(j)$ from its actual chronological endpoint differences. Equation (33.2) makes decoding to that INITIAL label well-defined. Remembering the free INITIAL value returns the appropriate scalar component of the pair. This supplies $f$ itself with fee at most $d$ by the reused value-join law. Any homogeneous archive may stop earlier; such a source emits only its actual prefix. A row with no response is still a literal complete block and costs one on every source that reaches it. There are no free rotations, skipped windows, repairs or omitted padding payments.

For necessity, start with any correct preset controller of uniform fee $H$. By Theorem 29.2 its very same stream, with the supplied symmetry decoder, computes the joined target with bound at most $H$. Stop joined-homogeneous archives immediately. If the first zero is not actually reached on any running source, the executed common stream is all ones. If its next block would cross the $k$th emitted one, every remaining successful source would reject in that block. Each previous archive would therefore have to be joined-homogeneous before the block, because all its candidates would give the same absorbing output and could never separate afterwards. Stop there and omit that block. This puts the maximal actual stopping depth at some $d\le\min(H,D)$. The earlier newly rejected rectangles and the final surviving rectangles must be homogeneous: they are exact archive fibres of the full joint prior, or subsets of earlier homogeneous stopping leaves. Thus (31.6) holds and $d\in\mathcal A(f)$.

The same argument applies if the first zero in the written stream is at or beyond the $k$th emitted bit: any still-running source would already have been rejected before that zero and must be stopped before the crossing block. A correct controller in this case again supplies an all-one option. This is a stopping normalization, not an instruction to charge an unexecuted zero.

It remains to consider an actually reached first-zero block after $a<k$ ones. Its index is $q$ and necessarily $H\ge q+1$. Lemma 32.2 supplies an eligible cut and a matrix satisfying (33.1)–(33.2) at depth $H$. If $H\le D+p$, this is already an admitted depth. If $H>D+p$, use the finite bound proved next to replace its eligible-cut continuation by a certificate of depth at most $D+p\le H$.

For that bound, fix any eligible cut and choose any one parent row in its nonempty cube. At indices

$$
t=q+1,q+2,\ldots,q+p-1
\tag{33.5}
$$

query just the actual vertex $j_t=u_t+g\pmod T$. These $p-1$ vertices are distinct: after division by $g$, their indices are $t(m/g)+1$ modulo $p$, and $\gcd(m/g,p)=1$. Exactly one of the $p$ phases is omitted. Every queried phase has its own distinct unit suffix column; the omitted phase has the all-zero suffix column. Thus even the full INITIAL phase is identified, independently of the parent and earlier columns, and arbitrary $\Lambda$ is decoded. Each singleton row is realized by (32.1): a one at bit position $g$ if $m/g\ge2$, or at bit position $m-1$ if $m/g=1$, with all other bits actually zero. Lemma 32.1 proves the seams after any chosen parent. This pays $q+1$ prefix blocks and $p-1$ continuation blocks, for total

$$
q+1+(p-1)=q+p\le D+p.
\tag{33.6}
$$

This is the paid single-phase recovery bound supplied by [D11, Theorem 3.4], instantiated on the union of the parent archives; the new optimization uses it only to bound the exact global search horizon. Since $p\ge2$, there is no missing degenerate continuation case.

We have proved that every finite controller yields a member of $\mathcal A(f)\cup\mathcal Z(f)$ with no greater fee, and every member yields a correct controller with no greater fee. If the set is nonempty, its least member therefore equals the least possible integer worst-branch fee and its constructed stream attains it. If the set is empty, any hypothetical finite controller would contradict the necessity just established. This proves (33.4), including infinity. ∎

**注记 33.3（Supplied attainability and finite exactness）。** Failure of all candidates in (33.4) means infinite preset fee by Theorem 33.2. Finiteness is equivalent to common-cut eligibility (31.5), as already proved in the supplied Theorem 24.2. The certificate agrees with that supplied boundary: every eligible cut gives (33.5)–(33.6); an all-one stopping option gives a finite stream and hence an eligible normalized cut by Theorem 24.2, without executing an inserted zero. The new numerical optimum needs the independent all-one option and the global response columns in addition to eligibility.

Formula (33.4) is a finite exact certificate law. A closed general formula for its minimum and a polynomial-time bound are not supplied. Its variables specify the actual moving windows, the disjoint-bit parent cube, the full INITIAL value join and a proved simultaneous sparse literal inverse. Acquired-archive adaptive code equalities [D11, Theorems 3.2–3.4] and branchwise composition in Theorem 27.5 retain their supplied scopes.

## 34. Literal endpoints, early stopping and excluded compatibility

**例 34.1（A forced right endpoint and a stopped first-zero boundary）。** At $k=5,m=4$, one has $T=6$, $g=2$, $P=\{0,2,4\}$, $D=1$ and $p=3$. A parent whose first zero is at $r=3$ must be $1110$. At chronological index zero its responses on the three actual path vertices are

$$
(q(0),q(2),q(4))=(1,1\oplus1,0)=(1,0,0).
\tag{34.1}
$$

The right endpoint cannot be assigned one. At other indices the same calculation translates the vertices by $u_q$, with their order retained. This is a literal falsifier for any parent condition that independently chooses its rejection threshold and a free endpoint response.

At these same parameters take, in both INITIAL value fibres, two different labels $L,H$ with $L$ for $s=0$ and $H$ for $1\le s<5$, independently of phase. The original action $1111$ rejects exactly those tails at least one; its successful sources all have label $L$. Either kind of observed endpoint therefore decodes after one paid block, so $C_{\rm pre}=1$. Zero blocks cannot suffice because one free-value fibre contains both labels, with joint histories (1.3). The corresponding cut $a=4=1\cdot4+0$ is eligible, but a stream executing that first-zero parent would pay two blocks. The all-one option in (31.6) preserves the actual optimum one and charges no fictional second block. The label of an initially rejected source can equal $L$, equal $H$, or be different; its independent free observation changes neither argument.

**例 34.2（Both values, label coincidences and a paid wrapped row）。** At $k=5,m=4$, make the joined phase labels independent of INITIAL tail and give the three phases $0,2,4$ distinct pair labels $X,Y,Z$. These pairs can have coincident components, for example

$$
X=(A,A),\qquad Y=(A,B),\qquad Z=(B,A),\qquad A\ne B.
\tag{34.2}
$$

Thus one component alone need not distinguish all phases; the full join is retained. Fee zero is impossible, and fee one is impossible. Indeed any correct first word with a leading one rejects all sources with INITIAL tail $k-1=4$, from all three actual phases, to the same endpoint in one free-value fibre. In the pair-valued problem those three labels are different, so such a word cannot complete it. A first word starting zero avoids that rejection but offers only a binary successful endpoint in the joined phase problem, which cannot distinguish three pair labels in one block. This is equivalently the value-join one-block lower bound.

One common stream attaining fee two is

$$
0010\mid1000.
\tag{34.3}
$$

The first word starts zero and selects precisely actual phase $2$, by (1.4). The next window is the wrapped path $[4,8]\pmod6=(4,5,0,1,2)$. The second word selects actual phase $4$ through its first bit; the adjacent physical charge at $5$ is nonactual. The full columns of $0,2,4$ are respectively $00,10,01$. Their joined labels decode correctly. The first word ends zero, the second's leading run is one, and both internal runs are one, so every INITIAL tail survives the first reset and every subsequent seam is legal. A phase already identified at the first endpoint can stop there; the other phases actually emit and pay the second, wrapped block. Thus $C_{\rm pre}=2$ for (34.2), retaining the chronological window and the full two-component label. Separately the value-zero component is computed by $0001$ and the value-one component by $0010$, each at fee one: the former selects actual phase $4$ and the latter phase $2$. Both fibres are nonconstant, so their component minima are one. Their maximum one is strictly smaller than the one-stream joined optimum two. These component optima supply no common first word.

**例 34.3（A final cut and an infinite joined boundary）。** At $k=8,m=3$, $T=9$, $g=3$, $P=\{0,3,6\}$ and $D=2$. Give both value fibres label $L$ on INITIAL tail zero and a different label $H$ on all positive tails, independent of phase. The eligible final cut is $a=7=2\cdot3+1$, with the literal stream

$$
111\mid111\mid100.
\tag{34.4}
$$

Rejection bands at its successive endpoints are exactly $s\in[5,8)$, $s\in[2,5)$, and $s=1$; each returns $H$. INITIAL tail zero survives the first zero and returns $L$. This proves fee at most three, paying both all-one blocks and the final mixed block. For a smaller fee, a first zero after $a<7$ ones would merge, at every fixed phase, the still surviving tails zero and one with different INITIAL labels. Before such a zero, both have the same successful archive; any hypothetical earlier stop would already have to return both labels and is impossible. An all-one stream of at most two blocks also leaves both tails successful, with the same observations. Hence no controller restricted to a preset stream of two blocks can succeed, and $C_{\rm pre}=3$. This exhibits the endpoint $q=D$ and a nonempty final partial rejection band.

For any parameters (31.1), assign in value fibre zero two different labels at the threshold $s=k-1$ and in value fibre one two different labels at the threshold $s=k-m$, with unrestricted cross-component coincidences. The two adjacent tails around the first threshold force a correct first word in fibre zero to have its first zero after exactly one leading one: an earlier zero merges them successfully, while a later zero or no zero merges them by rejection. Around the second threshold, every zero inside the first word merges the adjacent differently labelled tails successfully, so fibre one requires $1^m$. Both fibres are nonconstant initially, hence both must execute the common first block. Their permissible first words are disjoint. Absorbing rejection or subsequent rows cannot repair either merger, so $C_{\rm pre}=+\infty$. This is the supplied competing-value obstruction of Theorem 29.4, here used to test the infinite case of (33.4), with the full pair labels and independently treated initial bottom. It is not a new adaptive or threshold-family law.

**数学反例 34.4（The width-two seam and the unchanged coprime joint archive）。** The sparse suffix realization in Lemma 32.1 depends on $m\ge3$. At $k=3,m=2$, $T=4$ and $g=2$, prescribe response one on both actual vertices of each of two successive windows. Each row forces word $11$, since the two actual endpoints directly prescribe its first and last bits. Their common concatenation is $1111$, which rejects on its third one even from tail zero. Hence independent row support conditions do not alone give legal width-two continuation. This example does not alter the INITIAL prior or confer a width-two exact law.

A separate global-compatibility falsifier is the supplied coprime archive [S15, Theorem 8.1] at $k=8,m=4$. Its actual support and immutable labels are exactly

$$
S=\{0,1,3,4,5,6,8\},\qquad
\lambda(0)=B,\quad\lambda(4)=C,\quad\lambda(8)=D,\qquad
\lambda(1)=\lambda(3)=\lambda(5)=\lambda(6)=A,
\tag{34.5}
$$

where $A,B,C,D$ are four distinct labels. The paid acquisition consists of nine complete blocks: block index four is $1111$ and all other blocks are $0000$, conditioned on the actual all-zero difference archive. Its one nonzero mask excludes precisely phases $7,2$; preceding zero blocks clear the INITIAL tails, the all-one block is safe from tail zero, and later zeros leave tail zero. Since $9m\equiv0\pmod9$, the acquired offset is the stated one. Every member of this seven-phase archive therefore has an actual jointly realized history and that exact shared continuation; its acquisition fee is already paid and is not folded into its additional fee.

The first extra word $1111$ separates $B,C$ from $A,D$. The former child is completed by $1000$, and the latter by $0001$, each with one further paid block and a legal seam. This gives additional adaptive fee two. A single common two-block stream, however, would need the four two-bit label codes $A=00,B=10,C=11,D=01$: actual $A$ phases occur exclusively in each of the two windows and force its code zero in both positions. The first window misses only phase $2$, and the second only phase $7$; each unique full-path completion for the required row is $1111$. Their joint seam reaches $k=8$, so all still-running sources reject in the second block. Both first children contain two different labels, hence neither may stop early. The source's single preset stream $0000\mid1111\mid1000$ attains additional fee three. Thus the supplied sibling fee maxima two cannot replace a simultaneous global stream, while the actual preset optimum is three. The seven phases and four labels in (34.5) are essential data. Here $g=1$, outside (31.1); the example supplies a boundary, not a counterexample to Theorem 33.2.

**约定 34.5（Finite literal regression evidence）。** Finite evaluation of the original updates (1.2) on the joint histories (1.3) agrees with the stated endpoint, wrap, final-cut, stopping and exclusion examples. Joint-source, response-cube and sparse-seam evaluations use parameter pairs $(k,m)=(5,3),(5,4),(7,4),(8,3),(9,4),(11,4),(11,6),(11,8),(14,6),(17,8)$, including every chronological residue of their finite phase cycles. Exact minima from actual fixed-word streams agree with the common-cut certificate on the evaluated target tables at $(5,3),(5,4),(7,4),(8,3),(9,4),(11,4),(11,6)$. These finite tables include coincident labels in both value components, eligible cuts at $0,1,m-1,m,k-1$, early stopping, paid waiting and infinite preset cases. The coprime boundary retains precisely the seven phases and four labels in (34.5). Source labels remain immutable after destructive transitions, and initial bottom has its separate free label. These evaluations are finite regression evidence only. They provide neither a universal proof by sampling nor a Lean/kernel certification; the universal iff, minimum and horizon claims are established by the ordinary proofs in Chapters 31–33.

## 35. Supplied results and the original all-parameter boundary

**数学引文 35.1（Exact reuse and the new global bridge）。** The source prior, matched coefficient and operation semantics are [S1, Definition 1.2, Convention 1.3, Definition 2.1 and Proposition 2.3], [S2, Theorem 14.1], and this volume's Chapter 1. The source-specific charge and inverse interface is [S10, Interface 2.1]; [S15, Section 1, Theorems 2.3–3.3 and Proposition 4.2] supplies the path-inversion, successful-code extraction and parent-composition analysis at its stated hypotheses. Noncoprime simultaneous continuation here uses D11 as specified below. First-zero irreversible loss is [S1, Lemmas 4.2–4.3 and Theorem 5.2]. The simultaneous noncoprime sparse rows, acquired response-code lists, their exact laws and their paid $p-1$ phase bound are [D11, Theorem 2.2, Definitions 2.3 and 3.1 and Theorems 3.2–3.4]. The full INITIAL common-cut attainability criterion and exact preset value join are [S25, Theorems 24.2 and 29.2], retained here as credited inputs. The adaptive composition and branchwise preset replacements [S25, Theorems 27.2–27.5] do not authorize a maximum of different sibling streams. The explicit coprime seven-phase compatibility boundary is [S15, Theorem 8.1], not a new counterexample family.

Theorem 31.3 supplies the actual jointly constrained first-zero response cube; Lemmas 32.1–32.2 connect it to simultaneous mixed-value global rows and the lower bound for arbitrary stopping; Theorem 33.2 minimizes these data with the independent all-one stopping option and the finite exact horizon. These are source-specific ordinary mathematical deductions. They retain the supplied source labels and operations, and make no exhaustive literature-priority assertion. The existing acquired adaptive laws, common-cut existence criterion and value-join equality are not redelivered as new outcomes.

**开放问题 35.2（The unchanged complete original objective）。** The original exact goal remains OPEN: determine the minimum worst-branch ACTUAL EMITTED COMPLETE-BLOCK fee for every arbitrary attainable immutable INITIAL target and all original $k\ge2,m\ge1$, separately for adaptive control and a single global preset stream under both alphabets. Theorem 33.2 covers every arbitrary INITIAL target, including preset infinity, in the whole noncoprime proper-narrow region $3\le m<k$, $\gcd(m,k+1)\ge2$. It covers $k<2m$ inside that region as well as the guarded smaller widths; no $k\ge2m$ restriction was used. It also optimizes all first-zero parent responses and every later reactivation there, rather than only the acquired-child fees.

General width two, arbitrary coprime proper-narrow global continuation, and the remaining critical and wide preset exact costs remain outside this new theorem. Adaptive results are retained only at their already supplied scopes; (33.4) introduces no full INITIAL adaptive-to-preset equality. The arbitrary unit-width adaptive and preset classification, including infinity, is already settled by Theorems 25.3–25.4 and is not reclassified as open. A closed general formula or polynomial evaluation bound for the global code minimum is not proved. These remaining obligations preserve the same joint prior, immutable labels, observations and fee; the restricted exact certificate is an increment to the original goal, not its all-width completion.

[S25]: https://raw.githubusercontent.com/the-omega-institute/trureturing/0b48df40f9ceea93e0b1e777381663cb67ae879b/docs/develop/theory/KBONACCI_INITIAL_TARGET_COST_THEORY.md

## 追加锚（本行以下为增补区）
## 36. A wide INITIAL common cut and the parity of one global stream

**定义 36.1（Wide source contract and joined phase cells）。** In Chapters 36–40 use the original reader (1.1)–(1.2), with $k\ge2$, $m\ge k$, $T=k+1$, $g=\gcd(m,T)$ and $P=g\mathbb Z/T\mathbb Z$. The two alphabets remain all literal $m$-bit words and the internally legal literal $m$-bit words. A block is observed only at its endpoint. INITIAL value or independent initial $\bot$ is free, and every subsequently emitted complete block costs one. The target $f$ is an arbitrary map on the full jointly attainable INITIAL record set, with arbitrary label coincidences. Put

$$
\Gamma(j,s)=\bigl(f(0,-j,s),f(1,-j,s)\bigr),\qquad
\Lambda(j)=\Gamma(j,0),\qquad j\in P,\quad 0\le s<k.
\tag{36.1}
$$

The pair is ordered: its components need not agree. By the credited Theorem 29.2, the preset cost of $f$ equals the preset cost of the target $\Gamma$, independent of the actual scalar value. This is a decoder symmetry on one actual stream, not permission to choose different streams for the two values.

The full source prior is unchanged at wide widths. For every $(v,j,s)$, choose the single history (1.3), with $\ell\equiv0\pmod m$, $\ell\equiv-j\pmod T$, and $\ell\ge s+2$. Its separating zero and terminal run $s<k$ make the whole history legal, hence each constituent block internally legal. It realizes all three coordinates together. Under the internally legal alphabet, absorption is realized by following such an endpoint with tail $k-1$ by $10^{m-1}$; rejection occurs at the first bit across the seam. No source history length is observed. These are the supplied wide joint-source witnesses in Definition 24.1.

Call $a\in\{0,\ldots,k-1\}$ a common eligible cut when

$$
\begin{aligned}
\Gamma(j,s)&=\Lambda(j)&& (j\in P,\ 0\le s<k-a),\\
\Gamma(j,s)&=\rho&& (j\in P,\ k-a\le s<k)
\end{aligned}
\tag{36.2}
$$

for one pair label $\rho$ when $a>0$. For $a=0$ the second line is empty. There is no freshness requirement on $\rho$, and $f(\bot)$ is independent of $\rho$. Since $a<k\le m$, the all-one block count before this cut is zero. Thus (36.2) is precisely the credited common-cut criterion of Theorem 24.2, specialized to this width and joined target. In particular, finite preset acquisition is equivalent to existence of one such common cut.

For a literal block $B$ at chronological paid index $t$, write $u_t=tm\pmod T$ and define its folded actual bits and arithmetic successful response by

$$
d_B(r)=\bigoplus_{\substack{0\le i<m\\i\equiv r\ (T)}}B_i,\qquad
q_t(j)=d_B(j-u_t)\oplus d_B(j-u_t-1).
\tag{36.3}
$$

Indeed $c_{u_t-j+i}=1$ exactly at $i\equiv j-u_t$ or $j-u_t-1\pmod T$. Formula (36.3) describes an endpoint difference on a successful source, even when the word is unsafe on some other source. It confers no intermediate observation. If $g=1$, summing over all actual phases gives

$$
\bigoplus_{j\in P}q_t(j)=0.
\tag{36.4}
$$

Every folded bit occurs twice. For $g\ge2$ this full-cycle identity imposes no parity condition on restriction to the actual subgroup $P$.

**定义 36.2（Separated phase codes with actual multiplicities）。** Let $D_g(\Lambda)$ be the least $d\ge0$ for which there are vectors $z_j\in\mathbb F_2^d$, one for every actual phase, with

$$
\Lambda(j)\ne\Lambda(j')\ \Longrightarrow\ z_j\ne z_{j'},
\qquad
\bigoplus_{j\in P}z_j=0\quad\text{if }g=1.
\tag{36.5}
$$

When $g\ge2$ only separation is required. Equal-label phases may have different vectors. The multiplicity in the XOR is the number of actual phases, not the number of labels and not a count of INITIAL tails. The single-label case has $D_g=0$. This definition is an algebraic constraint; legal literal attainment is supplied separately in Theorem 38.1. The optimum is a set-theoretic quantity on the finite record set. An effective construction may take its finite label partition or a finite label table with decidable equality as input; target comparison, offline search and controller memory are separate from emitted block fee.

**定理 36.3（Preset lower bound with early stopping and rejection）。** For either original alphabet, every correct preset controller with worst actual emitted fee $H$ satisfies

$$
H\ge D_g(\Lambda).
\tag{36.6}
$$

If $\Gamma$ is nonconstant on successful INITIAL records, also $H\ge1$. These bounds hold for arbitrary words, attempted rejection, archive-dependent stopping and coincident labels. They do not assume that stopped sources execute a common suffix.

Proof. Use the exact value join of Theorem 29.2 without increasing $H$. Restrict the joined controller to the actual joint sources $(0,-j,0)$ for $j\in P$. Under any one literal prefix their raw tails are identical, because the tail update depends on bits alone. Consequently their first rejecting block, if any, has an index $b$ independent of phase. Before that block all these sources, when continued as raw sources, succeed; their endpoint differences are exactly (36.3).

At an actually reached archive in block $b$, all still-running tail-zero candidates reject to the same absorbing output. That output and every later output contain no further distinction among those candidates. Correctness therefore forces their joined labels already to be constant in their preceding archive. A source previously stopped on that archive forces every source with the same preceding observations to have stopped there as well. Thus the restricted decoder can stop every such archive before block $b$, retaining its label. This normalization only shortens the stopping times of this subprior; it does not add a rejection branch, issue a block or charge an unused suffix. It need not be a controller for the other INITIAL tails, which are used separately in the positive-fee lower bound.

Let $q_t$ be the row (36.3) for $0\le t<\min(b,H)$, taking $b=+\infty$ if there is no raw rejection within the bound. Complete the matrix to $H$ rows with zero rows when $b<H$. The row for a fixed written word can be evaluated at phases that stopped earlier; this evaluation is an algebraic set calculation, not a further experiment on those sources. Every row has even total parity when $g=1$, by (36.4). Its columns therefore satisfy the XOR condition in (36.5).

If two columns coincide, the corresponding sources have identical differences up to the earlier normalized stopping time, hence identical endpoint observations on the same free-value fibre. A deterministic stopping rule cannot stop and decode one differently from the other on that common archive. Their joined INITIAL labels must agree. This proves separation, including labels that occur at several stopping leaves. Thus a code family of length $H$ exists, giving (36.6). Padding each individual stopped column by zero was not used: such padding could destroy the row parity. The calculation instead retains the response of each common written row on the full original phase set.

Finally, at fee zero one has only the free INITIAL value or bottom. The joined target is independent of that value, and the full joint successful prior contains every $(j,s)$. Zero fee is therefore possible exactly when $\Gamma$ is constant on those records. This proves the additional bound. Initial bottom remains its own free branch. ∎

## 37. Exact phase multiplicity corrections for a preset stream

**定理 37.1（Complete finite-vector multiplicity law）。** Let $n=|\Lambda[P]|$. For $n=1$, $D_g(\Lambda)=0$. For $n\ge2$, put

$$
h=\lceil\log_2 n\rceil,\qquad M=2^h,\qquad
r=\bigl|\{L\in\Lambda[P]:|\Lambda^{-1}(L)|\text{ is odd}\}\bigr|.
\tag{37.1}
$$

For $g\ge2$, $D_g(\Lambda)=h$. For $g=1$ and $h=1$,

$$
D_1(\Lambda)=h+\mathbf1_{\{r=2\}}.
\tag{37.2}
$$

For $g=1$ and $h\ge2$,

$$
D_1(\Lambda)=h+
\mathbf1_{\{(n=M\ \text{and}\ r\in\{2,M-2\})\ \text{or}\ T=n=M-2\}}.
\tag{37.3}
$$

Thus the optimum depends only on the actual phase-cell multiplicities at these wide query scopes. The equality $T=n$ in (37.3) refers to the original number of phases, since $g=1$; it means every label cell is a singleton.

Proof. Separation requires at least $n$ different vectors, hence $d\ge h$. Without parity, give every label one different vector of length $h$ and repeat it at its phases. This proves the noncoprime case. For the coprime case, write $t_L=|\Lambda^{-1}(L)|$.

We use the following existing subset-sum spectrum, with its exact domain made explicit. In the additive elementary abelian group $V=\mathbb F_2^e$, $e\ge2$, of order $N=2^e$, a subset of cardinality $b$ and sum zero exists for every $0\le b\le N$ except $b=2,N-2$. This is Bajnok–Edwards, *On two questions about restricted sumsets in finite abelian groups* [S27, Corollary 18], including zero as an allowed element; their Theorem 16 instead states the spectrum for $V\setminus\{0\}$. The empty set is added directly. The two excluded sizes also follow from distinctness and the zero sum of all of $V$. All uses below have $e\ge2$. This classical spectrum is credited mathematics inside the proof, not a new theorem of this volume.

First suppose $h\ge2$ and $r\notin\{2,M-2\}$. Choose $r$ distinct vectors in $\mathbb F_2^h$ whose XOR is zero, and assign them, one each, to the odd cells. Give each even cell a distinct unused vector. There are $M-r\ge n-r$ available vectors. Repeating a cell's assigned vector $t_L$ times contributes that vector if $t_L$ is odd and zero otherwise. Therefore the total XOR is zero, giving depth $h$.

Next suppose $r=2$ and $n<M$. Since $h\ge2$ implies $n\ge3$, some cell is even and has size at least two. Choose four distinct vectors of XOR zero, for example an affine two-dimensional plane. Give two to the two odd cells. Give the other two to the selected even cell, placing one phase at one vector and its other $t_L-1$ phases at the other vector. Both counts are odd. Every remaining even cell receives its own unused single vector. The total number of used vectors is $n+1\le M$, and its odd-multiplicity vectors are exactly the four chosen ones. This realizes (36.5). In particular a cell is allowed to occupy two different codes.

Now suppose $r=M-2$, $n<M$, and the preceding case has not already applied. Then $n=M-2$ or $M-1$. If $n=M-1$, there is exactly one even cell. Assign the $M-2$ odd cells one vector each and split that even cell between the remaining two vectors with odd counts. All of $\mathbb F_2^h$ then has odd multiplicity, so its total XOR is zero. If $n=M-2$ and $T>n$, all cells are odd and some cell has size at least three. Give each of the other $n-1$ cells a different single vector. Split the selected cell among the remaining three vectors, with phase counts $1,1,t_L-2$, all odd. Here exactly $n+2=M$ vectors are used, again with odd multiplicity throughout the whole vector space. These assignments are possible for the actual cells, because the selected cell has the required number of phases. They account for every unsaturated case outside $T=n=M-2$.

For the lower bounds in the excluded cases, if $n=M$ then every code vector is required by some label. No label can use a second vector: a vector shared by two labels violates separation, while giving two to one label leaves fewer than $M-1$ for the remaining labels. Thus each label has one vector and every vector is used. The total XOR is the sum of the $r$ distinct vectors assigned to odd cells. For $r=2$ this is nonzero. For $r=M-2$ it equals the sum of the two omitted vectors, also nonzero, since the sum of the whole space is zero. If $T=n=M-2$, every phase has a different label; its $M-2$ distinct vectors likewise have nonzero XOR. These arguments rule out length $h$, without assuming that codes are constant on labels in any unsaturated case.

Every excluded case attains length $h+1$. For $n=M$, $r=2$, select an even cell, which exists since $M\ge4$. Split it with odd counts between two vectors, use two further vectors for the two odd cells, and choose these four to have XOR zero. Fill the remaining even cells with distinct unused vectors. Only $n+1\le2M$ vectors are needed. For $n=M$, $r=M-2$, select an even cell and use the $M$ vectors of an $h$-dimensional subspace of $\mathbb F_2^{h+1}$: one for each odd cell and two for that even cell with odd counts. Their XOR is zero because $h\ge2$. The other even cells have enough distinct vectors outside this subspace and contribute zero. For $T=n=M-2$, the relation $h=\lceil\log_2 n\rceil$ forces $h\ge3$; in $\mathbb F_2^{h+1}$ the desired cardinality $M-2\ge6$ is neither two nor $2M-2$. The credited spectrum supplies $n$ distinct vectors of XOR zero, one per phase. This proves both attainment and optimality in (37.3).

It remains to handle $h=1$, where $n=2$ and the vector space is $\mathbb F_2$. Two labels require its two distinct vectors. If $r=0$, both cells contribute zero; if $r=1$, assign zero to the odd cell. These give depth one. If $r=2$, the XOR of the two distinct vectors is one, so depth one is impossible. Both cell sizes are odd. The full actual prior has $T\ge3$, and their sum is even, hence $T\ge4$ and one cell has size at least three. In $\mathbb F_2^2$ give that cell three distinct vectors with odd counts $1,1,t_L-2$ and give the other cell the remaining vector repeated its odd number of times. All four vectors then have odd multiplicity and XOR zero. Depth two is attained. This proves (37.2). ∎

**数学引文 37.2（Applicability of the classical spectrum）。** In [S27] the group rank is the code dimension, and the subset cardinality is the number of vectors assigned odd multiplicity; neither is the original reader order $k$ or block width $m$. Corollary 18 is applied only to the additive group $\mathbb F_2^e$ with $e\ge2$. It permits the zero vector and requires distinct elements within the subset. These are exactly the requirements in the proof of Theorem 37.1. The cases $e=1$, cardinality zero, and the multiplicities greater than one are handled explicitly there.

Kosters, *The subset sum problem for finite abelian groups* [S28, Theorem 2.3] gives an exact subset count for every finite abelian group. With group $\mathbb F_2^e$, order $N=2^e$, target zero and cardinality $b$, it specializes to

$$
N_e(b,0)=
\begin{cases}
N^{-1}\binom Nb,&b\text{ odd},\\[2mm]
N^{-1}\left[\binom Nb+(-1)^{b/2}(N-1)\binom{N/2}{b/2}\right],&b\text{ even}.
\end{cases}
\tag{37.4}
$$

Here the group exponent is two, its two-torsion is the whole group and $e(0)=2$ in Kosters' notation. Li–Wan, *On the subset sum problem over finite fields* [S29, Theorem 1.2] gives the same formula on taking the full finite field of order $N$, characteristic two, and target zero; its additive group is $\mathbb F_2^e$. The field multiplication has no role in this use. The support is the full field, not its nonzero part or a reader phase subgroup. Formula (37.4) is credited counting mathematics, not a count of legal source words. The proof of the reader law uses the spectrum [S27], so no additional positivity inference from (37.4) is required.

## 38. The exact wide preset fee and its literal common stream

**定理 38.1（Room-qualified arbitrary INITIAL preset law）。** Use Definition 36.1. If $\Gamma$ is constant on successful INITIAL records, then $C_{\rm pre}(f)=0$, independently of its initial bottom label. If there is no common eligible cut (36.2), then $C_{\rm pre}(f)=+\infty$. Otherwise, whenever at least one common eligible cut $a$ satisfies

$$
a+k+2\le m,
\tag{38.1}
$$

the exact minimum worst actual emitted complete-block fee, for both original alphabets, is

$$
C_{\rm pre}(f)=\max\{1,D_g(\Lambda)\}
\quad\text{if }\Gamma\text{ is nonconstant}.
\tag{38.2}
$$

Here $D_g$ is exactly (37.2)–(37.3) and the noncoprime value in Theorem 37.1. Every finite value asserted in (38.2) is attained by one fixed literal stream, common to all successful INITIAL sources and both free values, with archive-dependent stopping. If eligible cuts exist but none meets (38.1), this theorem makes no numerical finite-cost assertion from (38.2).

Proof. Zero fee and its necessity were proved in Theorem 36.3. The infinite criterion is the credited Theorem 24.2 with $a<k\le m$, applied through the credited value join. For a nonconstant target with a room-qualified cut, Theorem 36.3 supplies the lower bound $\max(1,D_g)$ for every correct preset controller, including controllers that try to use rejection or stop before part of the written stream. It remains to construct an attaining stream.

Let $d=\max(1,D_g(\Lambda))$. Choose the code assignment from Theorem 37.1 at length $D_g$; when that length is zero, use one all-zero coordinate. For each $0\le t<d$, prescribe the actual phase mask

$$
E_t=\{j\in P:(z_j)_t=1\}.
\tag{38.3}
$$

For $g=1$ every $E_t$ has even cardinality by (36.5). At $t=0$ prescribe the literal prefix $1^a0$. At each later $t$ prescribe first bit zero, so its prefix parameter is zero. The remainder of each row is the credited one-block construction of [S26, proof of Theorem 3.1], whose literal realization is given below in the coordinates of (36.3). It is used for one predetermined row at every global chronological index, not for a different row on each observed branch.

Write $a_t=a$ at $t=0$ and $a_t=0$ at $t>0$. Put ones at positions $0,\ldots,a_t-1$ and zero at position $a_t$. Let $A_t(j)$ be the arithmetic charge of these prescribed ones and let

$$
R_t(j)=\mathbf1_{E_t}(j)\oplus A_t(j),\qquad
J_t=\{a_t+1,\ldots,a_t+T\}.
\tag{38.4}
$$

The room condition is exactly $a_t+T\le m-1$, so $J_t$ is a set of actual positions within this same paid block, each residue modulo $T$ occurring once. The known displacement is $u_t=tm\pmod T$.

If $g\ge2$, select optional ones only at positions $i\in J_t$ with $i\equiv-1\pmod g$. Such a one has two ambient charge vertices, $u_t+i$ and $u_t+i+1$. The former is outside $P$, and the latter is its unique actual vertex. As $i$ varies through the $T$ consecutive positions in $J_t$, these latter vertices cover $P$ once each. Set the bit at that position equal to $R_t(u_t+i+1)$. All other suffix bits are zero. These pulses are spaced by $g\ge2$, so each suffix one is isolated. This gives exactly the residual row on the actual phases. The unobserved ambient vertices supply no source or information to a branch.

If $g=1$, both $E_t$ and the prefix charge have even cardinality, so $\bigoplus_{j\in P}R_t(j)=0$. Solve the cyclic equations

$$
x_r\oplus x_{r-1}=R_t(u_t+r),\qquad r\in\mathbb Z/T\mathbb Z.
\tag{38.5}
$$

Choose $x_0$, recurse through the other residues, and use the zero total XOR to verify the final equation. The two solutions complement one another. Select one with at most $\lfloor T/2\rfloor$ ones and put bit $x_{i\bmod T}$ at each actual $i\in J_t$. Equation (36.3) proves that these positions contribute exactly $R_t$. Also

$$
\lfloor T/2\rfloor=\lfloor(k+1)/2\rfloor<k.
\tag{38.6}
$$

Hence no suffix run reaches $k$; bounding the total number of suffix ones bounds every such run. This is a lawful representative of the response row, rather than an abstract span used as an operation.

In both cases all unspecified positions are actual zeros. The first block rejects exactly the INITIAL tails $s\ge k-a$, before its first zero; they all have joined label $\rho$ by (36.2), and can return it at this first endpoint. For $s<k-a$, the leading run is safe and the first zero clears the old tail. The prefix and suffix runs are separated by that zero, every internal suffix run is shorter than $k$, and padding adds only zeros. Thus all those sources succeed and the first observed difference is precisely $\mathbf1_{E_0}(j)$. Their immutable label is already $\Lambda(j)$ by (36.2).

Every subsequent block begins with zero. It clears the known terminal tail of the preceding literal block, even if that tail is nonzero; no seam can reject a surviving source. The same suffix argument proves internal legality. The selected words therefore belong to the internally legal alphabet as well as the unrestricted alphabet, and the complete literal concatenation is safe on every low-tail source. They implement (38.3) relative to INITIAL phase at their own chronological offsets. The controller never observes or reverses a hidden source clock.

A surviving source records the code $z_j$ as successive differences of its own successful scalar readings, remembering its free initial value. Distinct joined labels have distinct codes, so after at most $d$ endpoints its label is determined. Return the component selected by that remembered value. Any archive already homogeneous in joined labels may stop earlier. A high-tail rejection returns its constant pair's component at fee one; initial bottom returns $f(\bot)$ at fee zero.

There are exactly $d$ blocks in the global stream. All clearing zeros, prefix ones, compensating bits and suffix padding occupy positions in those same blocks. There is no separate wait, repair or final cleanup block. A stopped source emits only its own prefix. Thus the worst actual fee is at most $d$, matching the lower bound. The case $D_g=0$ but $\Gamma$ nonconstant uses the single zero-response threshold block and pays one; a coincident rejection label does not change the decoder or lower bound. ∎

**推论 38.2（Complete arbitrary-target wide preset spectrum）。** For every $k\ge2$ and $m\ge2k+1$, every arbitrary immutable INITIAL target under the full joint prior, and either original alphabet,

$$
C_{\rm pre}(f)=
\begin{cases}
0,&\Gamma\text{ constant on successful INITIAL records},\\
+\infty,&\text{no common eligible cut exists},\\
\max\{1,D_g(\Lambda)\},&\text{otherwise}.
\end{cases}
\tag{38.7}
$$

The finite value is the optimum actual emitted complete-block fee, with one literal attaining stream; it is not an upper bound or a fee for an already acquired phase archive.

Proof. Every eligible $0\le a<k$ satisfies $a+k+2\le(k-1)+k+2=2k+1\le m$. Apply Theorem 38.1. Constant $\Gamma$ admits cut zero, so the zero and infinite cases are disjoint. All sources, their initial tails and their independent bottom remain those of Definition 36.1. ∎

## 39. Full-source separations and necessary splitting inside a label

**命题 39.1（A two-row optimum that must split one label cell）。** Take $k=3$, $m=7$, $T=4$ and $g=1$. On both free-value fibres, for every INITIAL tail, give phases $j=0,1,2,3$ respectively the labels $A,B,C,C$, where $A,B,C$ are distinct. Give initial bottom any independent label. Then

$$
C_{\rm ad}(f)=C_{\rm pre}(f)=2.
\tag{39.1}
$$

One attaining preset stream is

$$
0010000\mid0011000.
\tag{39.2}
$$

A code assignment constant on each label cell cannot meet the full-phase XOR constraint at any dimension; thus within-label splitting is necessary here, not just a convenience of an optimal construction.

Proof. The target is phase-only and admits common cut zero. It has $n=3$, $h=2$, $M=4$, $r=2$, with an even cell of size two and a spare code. Theorem 37.1 therefore gives $D_1=2$, and Corollary 38.2 gives preset fee two. The credited adaptive wide law [S26, Theorem 3.1] gives adaptive fee two as well; alternatively three tail-zero labels cannot be distinguished by the single useful binary endpoint of one block.

Both words in (39.2) start zero, and their only runs of ones have lengths one and two, respectively, shorter than $k=3$. The first word has charge mask $\{2,3\}$ at offset zero. The second has charge mask $\{1,3\}$ at the known offset $7\equiv3\pmod4$. Hence the actual code columns are

$$
z_0=00,\qquad z_1=01,\qquad z_2=10,\qquad z_3=11.
\tag{39.3}
$$

Their XOR is zero, and the two codes for $C$ are different. Every INITIAL tail is cleared by the first zero, all subsequent seams are legal, and the two scalar values use their own differences. All emitted zeros are inside the two paid blocks.

If instead codes were constant on labels, let the codes of $A,B,C$ be $a,b,c$. Full-phase XOR would be $a\oplus b\oplus c\oplus c=a\oplus b$, nonzero since separation requires $a\ne b$. This excludes every such assignment regardless of code length. The actual sources for all four phases and all tails are the histories of Definition 36.1. ∎

**命题 39.2（Three infinite families of one-block preset excess）。** Let $h\ge2$ and $M=2^h$. Take a phase-only target, the same on both free values, whose label-cell sizes are either

$$
(1,1,\underbrace{2,\ldots,2}_{M-2}),\qquad T=2M-2,
\tag{39.4}
$$

or

$$
(\underbrace{1,\ldots,1}_{M-2},2,2),\qquad T=M+2.
\tag{39.5}
$$

At $k=T-1$, $m=2T-1$, both original alphabets have

$$
C_{\rm ad}(f)=h,\qquad C_{\rm pre}(f)=h+1.
\tag{39.6}
$$

For $h\ge3$, the same separation holds for $T=M-2$ with every phase given a distinct label, at the same $k=T-1$, $m=2T-1$. Each target is defined on every INITIAL tail; its bottom label is arbitrary.

Proof. Here $m=2k+1$ and $\gcd(m,T)=1$, so every phase is actual and all targets have common cut zero with sufficient room. Both (39.4) and (39.5) have $n=M$, and their odd-cell counts are respectively $2$ and $M-2$. These are the saturated exceptions of (37.3). The third family has $T=n=M-2$ and $\lceil\log_2 n\rceil=h$, its singleton exception. Corollary 38.2 gives preset fee $h+1$, with literal attainment from Theorem 38.1.

For every family $n\ge3$. The supplied adaptive wide law [S26, Theorem 3.1] gives fee $\lceil\log_2 n\rceil=h$ on each free-value fibre, hence overall fee $h$. Its branch-specific even extensions are used only in that adaptive protocol. They are not combined into one preset stream. All cell sizes sum to the displayed actual $T$, so these are complete-source targets, not known-source encodings. ∎

**命题 39.3（A finite common-stream penalty across free values）。** At $k=2$, $m=5$, $T=3$, $g=1$, take distinct scalar labels $A,B$. Independently of INITIAL tail, give the ordered pair $\Gamma$ at $j=0,1,2$ respectively

$$
(A,A),\quad(A,B),\quad(B,A).
\tag{39.7}
$$

Then $C_{\rm ad}(f)=1$ and $C_{\rm pre}(f)=2$ under both alphabets. One common preset stream is

$$
01000\mid00010.
\tag{39.8}
$$

Proof. Each scalar-value fibre has two phase cells of sizes two and one, so the credited adaptive wide law has no odd/odd exception and gives one paid block. Explicitly, on initial value zero use $00010$, whose first-index mask is $\{0,1\}$; on initial value one use $00100$, whose mask is $\{0,2\}$. These are the respective $A$ cells. Both words start zero and have a single one, so they clear every INITIAL tail and are legal. Both fibres are nonconstant, giving the one-block lower bound.

The joined target has three distinct labels, so at least two binary successful endpoints are required on the full tail-zero subprior. In (39.8) the first mask is $\{1,2\}$; at offset $5\equiv2\pmod3$ the second mask is $\{0,2\}$. Their columns are $01,10,11$ at $j=0,1,2$, have XOR zero and distinguish all three pairs. The words start zero and have only isolated ones, so every original INITIAL tail succeeds and all seams are legal. Decode the pair and return its free-value component. This attains fee two and includes every zero in the displayed blocks. ∎

**命题 39.4（Adaptive fee one with infinite wide preset fee）。** At the same $k=2,m=5$, choose labels $A\ne B$ and $C\ne D$, allowing arbitrary coincidences between the two pairs. In free-value fibre zero take the phase-only target $A$ at $j=0,2$ and $B$ at $j=1$, at both tails. In fibre one take $C$ at INITIAL tail zero and $D$ at INITIAL tail one, independent of phase. Then

$$
C_{\rm ad}(f)=1,\qquad C_{\rm pre}(f)=+\infty.
\tag{39.9}
$$

Proof. In fibre zero, word $00100$ has even mask $\{0,2\}$, starts zero and is legal, giving the required phase label in one block. In fibre one, word $10000$ rejects exactly INITIAL tail one across its first-bit seam, and its surviving tail-zero sources return $C$; its first endpoint returns $D$ on rejection. Both fibres are nonconstant, so one block is also necessary. Free INITIAL value selects these different actions adaptively, while initial bottom stops independently at zero fee.

Fibre zero is nonconstant and phase-only. It permits cut zero; every positive cut has a high band containing every phase and both labels, so no positive cut is eligible. Fibre one's distinct tail labels exclude cut zero and require cut one. Thus there is no common cut for the joined target. The credited common-cut criterion, or the infinite case of Theorem 38.1, gives infinite preset fee. Cross-component label coincidences do not remove either failed constancy condition. ∎

## 40. Source scope and the unchanged all-parameter objective

**数学引文 40.1（Credited inputs and reader-specific deductions）。** The complete INITIAL prior and operation/observation contract are those of Chapters 1 and 24; Theorem 24.2 supplies common-cut attainability and Theorem 29.2 supplies exact preset value joining. The literal response realization with a prescribed first-zero prefix and room $a+T+1\le m$ is [S26, proof of Theorem 3.1]. The same theorem supplies the wide adaptive fee used in Propositions 39.1–39.2. These are credited existing reader results. The elementary abelian zero-sum subset spectrum and counts are [S27, Theorem 16 and Corollary 18], [S28, Theorem 2.3] and [S29, Theorem 1.2], with their exact parameter correspondence in Mathematical citation 37.2. They are credited external mathematics, not new source-acquisition results.

Theorem 36.3 extracts the full-phase parity constraint from one preset stream while preserving actual stopping and attempted rejection. Theorem 37.1 solves its multiplicity constraint, including saturated codes and the necessary within-label splitting constructions. Theorem 38.1 connects that solution to one legal first-zero parent and every subsequent chronological row, and Corollary 38.2 supplies the complete arbitrary INITIAL preset fee at $m\ge2k+1$. Their literature status is `repo-derived`: ordinary reader-specific mathematical deductions on the credited interfaces. The external subset spectrum and counting formulas are `literature-attested` within the exact scopes in Mathematical citation 37.2. They are not obtained by taking the maximum of separately optimal sibling streams, counting arbitrary algebraic representatives as actions, or replacing an INITIAL record by a current image. No broad novelty or literature-priority claim is made.

**定义 40.2（Residual original objective and nontransferable boundaries）。** The original goal remains the exact minimum worst-branch ACTUAL EMITTED COMPLETE-BLOCK fee for every arbitrary attainable immutable INITIAL target at all original $k\ge2,m\ge1$, separately for adaptive control and one global preset stream, under both original alphabets. Corollary 38.2 settles its entire wide preset region $m\ge2k+1$, including zero and infinity. Theorem 38.1 also settles the finite optimum at $m\ge k$ when there is a common eligible cut with $a+k+2\le m$. The common-cut existence law retains its own all-parameter scope; an eligible cut without that room is not assigned (38.2) by this chapter. The already supplied wide adaptive law is not counted as a new outcome. The existing critical-width adaptive law in [S30, Theorem 4.1] also remains at its original scope; it does not identify one common preset stream for competing free-value fibres.

The arbitrary unit-width classification in Theorems 25.3–25.4 and the arbitrary noncoprime proper-narrow preset certificate in Theorem 33.2 remain supplied settled regions. General width-two chronological seams, arbitrary coprime proper-narrow common-stream compatibility, the remaining critical and insufficient-room preset fees, and the adaptive gaps outside the supplied exact scopes remain within the original objective. Their sources, labels, phases, alphabets and paid fee are unchanged.

The supplied $k=2,m=4$ target of [S26, Theorem 6.1] retains its original $\theta$-indexed cells, distinct labels $A,B,\star$, forced prefix $10$, and exact fee two; its only usable cut has $a+k+2=5>4$. Thus it continues to exclude dropping (38.1), even though its unrestricted parity-code depth is one. The supplied $k=8,m=4$ acquired archive of Mathematical counterexample 34.4 and [S15, Theorem 8.1] retains exactly the seven phases $\{0,1,3,4,5,6,8\}$, four labels, paid nine-block acquisition, additional adaptive fee two and additional preset fee three. Its incompatible $1111\mid1111$ seam is outside the wide realization hypothesis. Neither source is replaced by a smaller phase set, a different target, an unpaid acquisition or a changed fee.

The common-image plateau theorem in [D13] concerns raw exact-length images of known legal words under polynomial remainder maps. Its source, observation and resource are different from returning an unknown immutable INITIAL label after destructive complete-block experiments. Its saturation conclusion supplies neither a free phase query nor the cost (38.7). The latter depends on first-zero loss, joint-history sources, preset row parity, actual literal realization and chronological seams, as proved above.

These statements are ordinary proofs in the declared mathematical model. Finite evaluation of examples can only provide regression evidence for those evaluated instances. No finite enumeration replaces the universal proofs, and no Lean/kernel certification of Chapters 36–40 is asserted.

[S26]: https://raw.githubusercontent.com/the-omega-institute/trureturing/3fa4d2325f1e8bcf3f4f9813f83fdf4c1156fdd0/docs/develop/theory/KBONACCI_TARGET_ACQUISITION_COST.md
[S27]: https://arxiv.org/pdf/1607.05718v1
[S28]: https://arxiv.org/pdf/1112.6294v1
[S29]: https://arxiv.org/pdf/0708.2456v1
[S30]: KBONACCI_CRITICAL_WIDTH_TARGET_COST.md
[D13]: https://raw.githubusercontent.com/the-omega-institute/trureturing/9e834a13e0760767641dd65bbdcc92521589baf3/D5/S1/Words/AdmissibleWords/KBonacciActualCommonImagePlateau.lean

## 追加锚（本行以下为增补区）

## 41. Odd-order width two: actual endpoints and stopping before rejection

**约定 41.1（Full INITIAL sources and the two-endpoint calendar）。** Throughout Chapters 41–45 fix

$$
m=2,\qquad k=2p-1\ge3,\qquad p\ge2,\qquad T=2p,\qquad
 g=2,\qquad P=2\mathbb Z/(2p)\mathbb Z.
\tag{41.1}
$$

Use the original matched $V_k\bmod2$ reader (1.1)–(1.2), the full actual-history prior, and Definition 1.3's immutable INITIAL labels and actual emitted-complete-block fee. Write the INITIAL phase as $-2i$, where $i\in\mathbb Z/p\mathbb Z$, represented by $0,\ldots,p-1$. Every $v\in\mathbb F_2$ and every $0\le s<k$ is present at each such phase. Specifically, Convention 1.2 supplies one history (1.3) by taking $\ell\equiv0\pmod2$, $\ell\equiv-2i\pmod{2p}$ and $\ell\ge s+2$, with its first bit adjusted by the terminal run's coefficient sum. The separating zero, value adjustment and length congruence jointly realize $(v,-2i,s)$. No proof below substitutes a product of marginal realizations for that history. The history length is unobserved.

For any arbitrary target $f$ on these full INITIAL records, put

$$
\Gamma(i,s)=\bigl(f(0,-2i,s),f(1,-2i,s)\bigr),\qquad
\Lambda_i=\Gamma(i,0).
\tag{41.2}
$$

Theorem 29.2 supplies $C_{\rm pre}(f)=C_{\rm pre}(\Gamma)$, including infinity, through a decoder on one actual stream. We use that theorem, rather than run either value's separately optimal stream on the other value. Pair labels can have arbitrary component coincidences; only equality of the pairs is relevant to the preset calculation. Initial $\bot$ remains independently readable and returns its arbitrary label at fee zero. All four words $00,01,10,11$ belong to both original alphabets, since $2<k$; their cross-block seams still follow (1.2).

At chronological block index $t$, a successful literal word $xy$ has actual endpoint difference

$$
x_t(i)=x\mathbf1_{\{t\}}(i)\oplus y\mathbf1_{\{t+1\}}(i),
\qquad i,t\text{ taken modulo }p.
\tag{41.3}
$$

Indeed the coefficient of its first bit is $c_{-2i+2t}$, which is one exactly at $i=t$, and that of its second is $c_{-2i+2t+1}$, which is one exactly at $i=t+1$. The two vertices are distinct even at $p=2$. Both bits therefore directly prescribe the two actual endpoints. The ambient odd vertex in the physical path is not an INITIAL source. Equation (41.3) is an endpoint difference computed only after the whole block succeeds; it supplies no intermediate reading. Its literal inverse is exactly $(x_t(t),x_t(t+1))$.

**定义 41.2（Credited common cuts and all-one options in quotient coordinates）。** For $0\le t\le p-1$ put

$$
I_t(i)=\mathbf1_{\{t,t+1\}}(i),\qquad
S_t(\beta)=\{i:(I_0(i),\ldots,I_{t-1}(i))=\beta\},\qquad
h_t=k-2t.
\tag{41.4}
$$

Write $\operatorname{Const}$ for image size at most one, including empty images. A common eligible cut is $a=2q+r$ with $0\le a<k$ and $r\in\{0,1\}$, satisfying

$$
\begin{aligned}
&\operatorname{Const}\{\Gamma(i,s):i\in S_t(\beta),\ h_t-2\le s<h_t\}
&& (0\le t<q,\ \beta\in\mathbb F_2^t),\\
&\operatorname{Const}\{\Gamma(i,s):i\in S_q(\beta),\ h_q-r\le s<h_q\}
&& (\beta\in\mathbb F_2^q),\\
&\Gamma(i,s)=\Lambda_i
&& (0\le i<p,\ 0\le s<k-a).
\end{aligned}
\tag{41.5}
$$

These are exactly (24.4)–(24.6) on the value join, with $\theta=-2i$. The last interval contains $s=0$, so its constant is $\Lambda_i$. Cut zero is eligible exactly when $\Gamma$ is independent of INITIAL tail. Common-cut existence, including infinity, is supplied by Theorem 24.2; (41.5) is notation for that supplier, not a new existence criterion.

Let $\mathcal A$ consist of $d\in\{0,\ldots,p-1\}$ such that

$$
\begin{aligned}
&\operatorname{Const}\{\Gamma(i,s):i\in S_t(\beta),\ h_t-2\le s<h_t\}
&& (0\le t<d,\ \beta\in\mathbb F_2^t),\\
&\operatorname{Const}\{\Gamma(i,s):i\in S_d(\beta),\ 0\le s<h_d\}
&& (\beta\in\mathbb F_2^d).
\end{aligned}
\tag{41.6}
$$

These are the all-one stopping conditions (31.6), instantiated directly from their archive meaning at width two; the parameter restriction of Theorem 33.2 is not invoked. In particular $0\in\mathcal A$ exactly when the joined target is constant on all successful INITIAL records. Its two components need not equal each other or $f(\bot)$.

**定理 41.3（Identification before post-zero rejection and the two-phase normalization）。** In (41.1), consider one fixed literal stream with a first zero after $a<k$ leading ones. For $p\ge3$, before the first later block which would reject the common tail of its successful first-zero survivors, their completed endpoint-difference columns distinguish all $p$ actual INITIAL phases. This assertion concerns the completed prefix before the dangerous block. For an eligible cut, every still-running successful archive can therefore stop with its INITIAL joined label before that block.

For $p=2$, any finite matrix of the formal literal rows (41.3) can instead have each suffix word $11$ after the first-zero parent replaced by $00$. A raw rejected word does not supply an observed endpoint difference; these formal rows are used only to specify the normalized words. This preserves equality and inequality between every pair of full phase columns, preserves their prefix equality relations at each completed depth, and gives a safe suffix without increasing its written number of blocks. The all-one prefix and the first-zero parent are left intact.

**证明。** After the first zero, all surviving INITIAL tails at a fixed phase merge, and the final tail of its parent word is common across all surviving phases. Subsequently tail evolution depends only on the common literal stream. Any first post-zero rejection is thus simultaneous for all those raw surviving records. Let $n$ be the absolute bit position, counted from the first issued bit, where the run that first reaches $k=2p-1$ ones begins. This run is preceded by a zero, and begins after the stream's first zero.

First suppose $n=2h$. Its first $p-1$ whole words, at indices $h,\ldots,h+p-2$, are $11$ and complete successfully: they contain $2p-2<k$ ones after a clearing zero. The next block, at index $h+p-1$, would reject on its first bit. On the cyclically ordered vertices $v_j=h+j\pmod p$, the preceding $p-1$ rows are the path edges $\{v_0,v_1\},\ldots,\{v_{p-2},v_{p-1}\}$. With $e_0,\ldots,e_{p-2}$ the unit columns, the phase columns restricted to these actual completed rows are

$$
e_0,\quad e_0+e_1,\quad e_1+e_2,\quad\ldots,\quad
 e_{p-3}+e_{p-2},\quad e_{p-2}.
\tag{41.7}
$$

They are pairwise distinct for $p\ge3$: the end columns are different unit vectors, and each interior column has its own two adjacent nonzero coordinates. Arithmetic here is in $\mathbb F_2$. Keeping earlier rows cannot remove a distinction.

If $n=2h+1$, word $h$ is $01$. Its row is the singleton $\{v_1\}$, and the next $p-2$ successful words are $11$ on edges $\{v_1,v_2\},\ldots,\{v_{p-2},v_{p-1}\}$. The run at their final endpoint has length $1+2(p-2)=2p-3<k$. The next block is the first dangerous one. On these $p-1$ completed rows the columns are

$$
0,\quad e_0+e_1,\quad e_1+e_2,\quad\ldots,\quad
 e_{p-3}+e_{p-2},\quad e_{p-2},
\tag{41.8}
$$

where at $p=3$ this list is $0,e_0+e_1,e_1$. Again the columns are pairwise distinct. This case includes a zero in the first position of a block; the previous case includes a zero in the second position. These exhaust the possible alignment of the run. Each still-live source has actually paid for and observed all these rows; the argument supplies neither a midblock stop nor another source's archive.

At an eligible cut, (41.5) says that every surviving tail at phase $i$ has the one INITIAL label $\Lambda_i$. A live archive whose own completed columns now determine $i$ is therefore label-homogeneous. It can stop before the dangerous block. Earlier rejection archives were already homogeneous by the eligible rectangles and have their own labels; they are not folded into the successful phase calculation.

At $p=2$, (41.3) assigns word $11$ the constant response one on the whole actual phase set, and $00$ the constant response zero. Replacing the row adds one to that same coordinate of every phase column. All column comparisons, including comparisons of every prefix, are preserved. The decoder is defined from the new actual words and their actual outputs; it is not supplied an output of the old word. The parent ends with tail zero or one. Every following word is now $00,01$ or $10$, so its internal run is at most one and every seam has run at most two, strictly below $k=3$. The normalized suffix is safe and has exactly the same number of whole words.

This leaves Mathematical counterexample 34.4 intact. Starting at tail zero, the raw written words $11\mid11$ at $k=3,m=2$ still reject on their third one. The theorem asserts lawful execution through actual stopping, or the specified common-coordinate normalization after a first-zero parent; it does not assert raw legality of every written row sequence. ∎

## 42. A width-two chronological certificate for the complete INITIAL target

**定义 42.1（One common incidence matrix）。** For an eligible cut $a=2q+r$, a depth $q+1\le d\le p$ has a certificate when a matrix $x_t(i)$, $0\le t<d$, $0\le i<p$, satisfies all the following conditions. Rows $t<q$ are $I_t$. The parent row at $q$ is supported on $\{q,q+1\}\pmod p$ and is the actual row of

$$
B_q\in\{00,01\}\quad(r=0),\qquad B_q=10\quad(r=1).
\tag{42.1}
$$

Every later row is arbitrary on $\{t,t+1\}\pmod p$ and zero elsewhere. The whole columns separate different low labels:

$$
\Lambda_i\ne\Lambda_j\quad\Longrightarrow\quad
 (x_0(i),\ldots,x_{d-1}(i))\ne(x_0(j),\ldots,x_{d-1}(j)).
\tag{42.2}
$$

Equal labels may have different columns. Let $\mathcal Z$ be the set of admitted depths, over all common eligible cuts and their matrices. The matrix is on the whole actual phase set and has one literal word at each chronological index. It is not a family of separately optimized sibling streams. Its depth is an admitted horizon; a source already stopped need not issue every written word.

**定理 42.2（Objective-level incidence law and finite horizon）。** For every arbitrary full INITIAL target in (41.1), under both original alphabets,

$$
 C_{\rm pre}(f)=\min(\mathcal A\cup\mathcal Z),\qquad
 \min\varnothing=+\infty.
\tag{42.3}
$$

Every admitted depth gives one fixed literal stream with archive-dependent stopping and no greater actual fee. Every finite controller supplies an admitted depth no greater than its worst fee. In particular every finite preset fee is at most $p$. Theorem 44.2 will evaluate this certificate's minimum by a closed expression; the certificate is the stopping-and-seam bridge used in that evaluation.

**证明。** A depth in $\mathcal A$ is realized by $(11)^d$. A newly rejected source at block $t$ lies in precisely the rectangle in the first line of (41.6), with its own preceding archive $\beta$. Return that rectangle's joined label. At the last successful endpoint return the label of the rectangle in the second line. Earlier homogeneous archives can stop earlier, and bottom stops freely. This is the supplied all-one decoding argument, with every issued block paid.

For a matrix in $\mathcal Z$, issue $q$ words $11$, then its prescribed parent, then the literal inverses (41.3) of its later rows. Before and at the parent, (41.5) decodes every partial rejection using its preceding archive. All remaining sources have $s<k-a$ and label $\Lambda_i$. If $p\ge3$ and a later raw word would reject their common tail, Theorem 41.3 identifies every phase strictly before that word; all still-live archives stop there. If no such danger occurs before depth $d$, (42.2) decodes the successful archive at $d$. At $p=2$ apply Theorem 41.3's suffix normalization first; it preserves (42.2), and every resulting seam is safe. Initial values are handled simultaneously by Theorem 29.2, remembering the actual free value to return the appropriate component. A zero row costs one if it is reached. No hypothetical row is treated as an acquired observation.

We next give a uniform finite construction for every eligible cut, to justify the fixed horizon in Definition 42.1 independently of any controller's original bound. All following powers count whole words, and a zero exponent means no word. At $q=0$, use $(01)^{p-1}$ if $r=0$ and $(10)^{p-1}$ if $r=1$. Their actual rows select respectively phases $1,\ldots,p-1$ and $0,\ldots,p-2$. Each selected phase has a distinct unit column and the one omitted phase has the zero column. Thus all phases are identified by depth $p-1$.

For $q=1,r=0$, use

$$
 11\mid(01)^{p-1}.
\tag{42.4}
$$

The first row groups phases $0,1$. Later right-endpoint pulses select phases $2,\ldots,p-1$ and finally phase zero at the wrapped index $p-1$. Their full columns identify every phase by depth $p$, also when $p=2$ and the wrapped pulse is the parent itself. For $q=1,r=1$, necessarily $p\ge3$, use $11\mid(10)^{p-2}$. The parent selects phase one and splits the initial endpoint pair; subsequent left-endpoint pulses select $2,\ldots,p-2$. Phase $p-1$ is the unique zero column. All phases are identified by depth $p-1$.

For $2\le q\le p-2$, use

$$
 (11)^q\mid(r0)\mid(10)^{p-q-2},
\tag{42.5}
$$

where $r0$ denotes the actual word $00$ or $10$. The $q\ge2$ initial edge rows already distinguish $0,\ldots,q$ individually from each other and from the untouched suffix $q+1,\ldots,p-1$. Their columns are the distinct path columns of the form (41.7) on that shorter path; the untouched suffix has zero columns. Later left-endpoint pulses select $q+1,\ldots,p-2$, leaving only $p-1$ with the zero column. Total depth is $p-1$. If $q=p-1$, necessarily $r=0$. For $p\ge3$ the initial $p-1$ edge rows already identify all phases, and their surviving INITIAL tail range is just $s=0$. The eligible earlier rejection rectangles and these singleton survivor fibres show $p-1\in\mathcal A$, so the parent is not issued. The remaining $p=2,q=1,r=0$ case is (42.4).

Each first-zero word above has exactly its specified leading threshold. Higher INITIAL tails reject precisely in the eligible earlier or parent rectangles; lower tails reach its clearing zero. After it, $01$ or $10$ has at most one leading one, at most one trailing one, and seams at most two. All these seams are strict for $k\ge3$; the seam from the parent is also safe. Before the zero, an actually surviving tail has $s+a<k$ by definition. Thus the constructions are lawful on every actually running source, with no free wait or repair. They produce a member of $\mathcal A\cup\mathcal Z$ of depth at most $p$ for every eligible cut.

For necessity, let a correct preset controller have worst fee $H$, and apply the exact value-join decoder. Stop each joined-homogeneous archive as soon as it becomes homogeneous. If no running source reaches a zero, its execution uses only all-one blocks. A block crossing the $k$th emitted one rejects every still-successful candidate and gives no distinction within any previous archive; correctness requires each such archive to have one label already. Omit that block and stop before it. The maximal remaining depth $d$ is at most $\min(H,p-1)$, and the exact all-one rejection and survivor archives imply (41.6), also for raw subsets of archives stopped earlier. Thus $d\in\mathcal A$. The same normalization applies if the first written zero lies at or after the $k$th one.

Otherwise the actual first-zero block occurs after $a=2q+r<k$ ones and is reached by a running source. Theorem 24.2's necessity argument applied at this actual location proves (41.5), including subsets of earlier stopped leaves. Its literal parent is exactly (42.1). To extract columns, take actual INITIAL tail-zero, value-zero representatives at every phase, using Convention 41.1. They all could traverse the prefix through this zero successfully, though already stopped representatives are used only for the mathematical definition of a whole-phase row. After the parent their raw tails are common. Keep their literal successful rows until any first prospective common rejection. Such rejection cannot distinguish still-running candidates within one preceding archive: they would all become $\bot$ and stay there. Correctness forces that archive to be label-homogeneous before the rejecting block. Stop it there, remove the common rejecting suffix, and extend the entire remaining matrix by common zero rows if necessary. This is a proof-only extension on every phase; it neither pads individual stopped columns differently nor supplies a new acquired reading.

Two different $\Lambda$ labels cannot have equal full columns in this normalized matrix. Their two actual representatives would then have the same free reading and the same successful endpoint archive up to the earlier stopping time. A deterministic decoder would stop both there with the same label, a contradiction. This replay includes representatives stopped before the parent and those stopped later. Hence (42.2) holds. If $H\le p$, it gives a certificate at depth $H$; if $H>p$, the eligible-cut construction already proved gives a member of $\mathcal A\cup\mathcal Z$ with depth at most $p<H$.

Every finite controller therefore gives a candidate with no greater fee, and every candidate gives a controller with no greater fee. The least candidate equals the exact integer optimum; if there is no candidate, a finite controller would contradict necessity. This proves (42.3), zero and infinity included. ∎

## 43. The cleared chronological suffix consumed by the INITIAL envelope

**定义 43.1（Closed suffix expression）。** For $1\le L\le p$ use the fixed low labels $\Lambda_L,\ldots,\Lambda_{p-1}$; $L=p$ means the empty suffix. Define

$$
\Psi(L)=
\begin{cases}
0,&\operatorname{Const}\{\Lambda_i:L\le i<p\},\\
1,&\text{the suffix is nonconstant, }\operatorname{Const}\{\Lambda_i:L+2\le i<p\},
       \quad |\{\Lambda_i:L\le i<p\}|\le2,\\
\max\{2,B-L\},&\text{otherwise},
\end{cases}
\tag{43.1}
$$

In the last case

$$
 B=\max\{j:L\le j<p-1,\ \Lambda_j\ne\Lambda_{j+1}\}.
\tag{43.2}
$$

The nonconstant suffix has a differing adjacent pair, so this maximum exists. The one-block condition can equivalently be written as follows: if $\{L+2,\ldots,p-1\}$ is nonempty, its labels have one value $A$ and $|\{\Lambda_L,\Lambda_{L+1}\}\setminus\{A\}|\le1$; if it is empty, the two possible endpoint entries impose no extra condition. Thus empty, singleton and constant suffixes cost zero, and a nonconstant two-element suffix costs one. Both versions of the one-block condition include these cases.

**定理 43.2（Exact acquired suffix fee with its paid acquisition retained）。** Suppose an actually acquired archive has one common current value, current tail zero, exactly phase candidates $\{L,\ldots,p-1\}$, and next chronological block index $L$, where $1\le L\le p$. Its immutable labels are $\Lambda_i$. The minimum additional adaptive and preset fees both equal $\Psi(L)$. Empty archives need no action. This is an additional fee at the stated actual archive; it does not make its acquisition or its $L$ preceding blocks free. In Theorem 44.2 the archive will be realized by the original INITIAL sources of an odd first-zero parent.

**证明。** A constant label is returned without an action. For a nonconstant suffix, the first available block at index $L$ controls only phases $L,L+1$ independently by its two literal bits. Every phase in $\{L+2,\ldots,p-1\}$ has response zero. Tail zero makes every two-bit first word safe, since $2<k$.

One block suffices exactly when the zero-response outside set is label-homogeneous and all suffix labels can be assigned to at most two scalar responses. These are exactly the second line of (43.1). For attainment, if the outside set is nonempty let its label be the zero-response baseline and assign the two bits to mark the other label at the two endpoints. If the outside set is empty, choose either occurring label as that baseline. Every response fibre then has one label, and the literal word is $00,01,10$ or $11$ according to those assignments. A nonconstant suffix necessarily has at least two candidates, so this construction covers the possible two-element suffix; a singleton uses the zero-fee case. If the one-block condition fails, any adaptive or preset controller needs at least two additional blocks.

For the chronological lower bound, consider any differing adjacent labels at $j,j+1$ with $j\ge L+1$. Starting at absolute position $2L$, the two actual phases have no coefficient activity before position $2j-1$. Their current values and tails are equal. Up to that first possibly separating coefficient, any common input gives equal values and common tails; a rejection is common absorption and cannot distinguish their immutable labels. Equal acquired archives also force equal future adaptive choices and equal stopping decisions. Reaching position $2j-1$, the second bit of block $j-1$, requires at least $j-L$ additional complete blocks. No earlier endpoint can separate the pair. Thus the last differing boundary $B$ gives the lower bound $B-L$ when $B\ge L+1$; for $B=L$ that expression is zero and adds no restriction. Together with the failed one-block condition the lower bound is $\max\{2,B-L\}$.

For attainment in this last case put $d=\max\{2,B-L\}$ and issue exactly $d$ consecutive words $11$ starting at index $L$. Failure of the one-block condition implies at least three phases in the suffix. Since $B\le p-2$ and $L\ge1$,

$$
 d\le p-L-1,\qquad L+d\le p-1,\qquad 2d\le2p-4<k.
\tag{43.3}
$$

The bounds include the case $d=2$. There is no cyclic wrap in these rows. Their columns on $L,\ldots,L+d$ are

$$
e_0,\ e_0+e_1,\ldots,e_{d-2}+e_{d-1},\ e_{d-1},
\tag{43.4}
$$

which are distinct for $d\ge2$, while every later phase has the zero column. All those later phases have one label, because their indices are beyond the last differing boundary $B$. Hence every nonzero column decodes its own phase label and the zero column decodes the constant remaining suffix label. Within-label splitting is allowed and is not charged as a new label. Starting at tail zero, the run contains $2d<k$ ones, so every actual block and its final seam is safe. No cleanup block is appended. Early homogeneous archives can stop earlier but never change this one fixed continuation.

The lower bounds allowed arbitrary adaptive choices, and the upper bounds used one preset stream. Their equality therefore proves both additional optima. At an odd INITIAL cut the same-phase low tails that reached its clearing zero all have label $\Lambda_i$ by (41.5), and the tail-zero representatives in Convention 41.1 give the actual source pairs used in these lower bounds. That pullback, with the parent fee added, is made explicit next. ∎

## 44. Closed arbitrary-INITIAL preset fees at every odd order and width two

**定义 44.1（Numerical common-cut horizons）。** For the full table (41.2), define

$$
 J=\max\bigl(\{j:1\le j<p,\ \Lambda_j\ne\Lambda_0\}\cup\{0\}\bigr).
\tag{44.1}
$$

For every eligible $a=2q+r$ define its numerical horizon

$$
 E(a)=
\begin{cases}
 J,&a=0,\\
 q+1+\Psi(q+1),&r=1,\\
 p,&a=2\text{ and }\Lambda_0\ne\Lambda_1,\\
 \displaystyle\max\left(\{q+1\}\cup
       \{j:q+2\le j<p-1,\ \Lambda_j\ne\Lambda_{j+1}\}\right),
       &r=0,\ a>0,\text{ otherwise}.
\end{cases}
\tag{44.2}
$$

Empty boundary sets give $q+1$ in the last line. Using $q+1\le j<p-1$ instead of $q+2\le j<p-1$ in that line gives the same horizon: its only extra possible entry is $q+1$, already the mandatory parent lower bound. This equivalence does not change which cuts are eligible. At cut zero, (41.5) is a phase-only target, and [S10, Theorem 4.1 and Corollary 4.2] with $g=2,u=m/g=1$ already supplies the exact phase-only scan fee $J$. Theorem 29.2 applies it to the full value join. That supplied specialization is not a new fee law here.

**定理 44.2（Exact closed GLOBAL preset envelope for every full INITIAL table）。** In (41.1), for every arbitrary immutable INITIAL target, all tails, both free values and independent bottom included, under either original alphabet,

$$
\boxed{\displaystyle
 C_{\rm pre}(f)=
 \min\left(\mathcal A\ \cup\ \{E(a):a\text{ satisfies }(41.5)\}\right),
 \qquad \min\varnothing=+\infty.}
\tag{44.3}
$$

Every finite minimum is attained by one lawful fixed literal stream with archive-dependent stopping. The formula optimizes all common eligible cuts, permits equal labels on separately identified phases, and includes the option that no first-zero parent is ever emitted. Its quantifiers concern the complete original INITIAL target, not just a post-zero support. It asserts no arbitrary-target adaptive envelope.

**证明。** The objective-level bridge is Theorem 42.2. We evaluate its candidate horizons using the actual calendar and actual INITIAL sources, and also track the case where an admitted written parent is not reached. First record the all-one successful phase fibres before any wrap. At $q=0$ there is one full fibre. At $q=1$, phases $0,1$ have the same column one and every phase $2,\ldots,p-1$ has column zero. For $2\le q\le p-1$, phases $0,\ldots,q$ have individually distinct nonzero path columns of the form (43.4), and $q+1,\ldots,p-1$ have the zero column. These descriptions follow by listing which consecutive edges $\{t,t+1\}$ contain each actual phase. At $p=2,q=1$ the endpoint pair is the whole phase set and the outside fibre is empty. At $p\ge3,q=p-1$ every phase is individually identified.

For an odd cut $a=2q+1$, the parent is the one actual word $10$. It selects phase $q$ and ends with a clearing zero. If $q=0$, it identifies phase zero. If $q=1$, it separates the earlier endpoint collision $0,1$. If $q\ge2$, the selected phase was already individually identified. In every case the only possibly nonhomogeneous successful low-phase archive after this parent is exactly

$$
 \{q+1,\ldots,p-1\},\qquad
 \text{current tail }0,\qquad\text{next block index }q+1.
\tag{44.4}
$$

Its phases had zero differences on the all-one prefix and on this parent, and so have one common current value. All lower INITIAL tails at phase $i$ have label $\Lambda_i$ by (41.5). Decode the earlier successful singleton archives and all eligible rejection rectangles from their own acquired archives. For (44.4) apply Theorem 43.2's one fixed continuation, paying its $\Psi(q+1)$ blocks after the $q+1$ prefix-and-parent blocks. This attains fee at most $E(a)$ simultaneously on all successful siblings and both values. If $\Psi=1$ its word has at most two ones after the clearing zero. If $\Psi\ge2$, (43.3) gives a total run strictly shorter than $k$. Thus every actual seam is justified, including $p=2$, where the suffix has at most one phase and needs zero additional blocks.

For the matching lower bound on any correct stream with this actually reached odd parent, it already costs at least $q+1$. If the suffix labels are nonconstant, choose its actual INITIAL sources $(0,-2i,0)$ using Convention 41.1. They share their entire archive before and through the parent; they cannot stop earlier with different $\Lambda_i$ labels. At the parent's endpoint they actually realize precisely the current-value/tail situation (44.4). The all-action lower bound of Theorem 43.2 therefore applies to their actual continuation, not to an assumed freely acquired table. The worst fee is at least $q+1+\Psi(q+1)$. If the suffix is constant, $\Psi=0$ and the actually reached parent alone gives that bound. This lower bound allows either earlier stopping on other archives or arbitrary within-label phase splitting.

Next take an even cut $a=2q>0$. Its parent can be $00$ or $01$; their thresholds are the same but their response rows differ. Outside the exceptional endpoint collision, choose the actual parent $01$ and put $d=E(2q)$ from the last line of (44.2). Issue the single stream

$$
 (11)^q\mid(01)^{d-q}.
\tag{44.5}
$$

When $q\ge2$, the all-one prefix already identifies $0,\ldots,q$. The parent selects $q+1$, and later words select successive phases $q+2,\ldots,d$ at their first right-endpoint opportunity. They split the previously zero-column suffix into singleton columns. The untouched suffix $d+1,\ldots,p-1$ has one label, because $d$ is at least its last differing boundary. At $q=1,\Lambda_0=\Lambda_1$, the earlier pair has one label and may stop when its remaining tails have that label; it need not be split. The same right-endpoint scans and constant last suffix decode every other surviving low phase. The first zero clears the old surviving tails; each $01$ then starts zero and ends with tail one. Every actual seam is safe and every scan or zero-information word is paid.

At the final even cut $q=p-1$ with $p\ge3$, (44.5) writes one wrapped parent $01$, at total depth $p$. However the prefix has already identified every phase and has only INITIAL tail zero surviving. The earlier rejection rectangles are eligible and the final survivor labels are $\Lambda_i$, so $p-1\in\mathcal A$ and every source stops before that written parent. No nonexistent parent fee is charged. This is why $E(a)$ is an admitted horizon and the all-one alternative is retained separately in (44.3).

For every nonexceptional actually reached even parent, the fee is at least $q+1$. For any differing adjacent low labels at $j,j+1$ with $j\ge q+2$, take the actual INITIAL tail-zero, value-zero sources at these phases. Their all-one columns are both zero, and either legal even parent has zero response at both. After the parent's clearing zero they have equal current tails and values. Neither phase has coefficient activity before absolute position $2j-1$; they therefore share every actual acquired archive until at least block $j-1$, whose completed depth is $j$. A common rejection cannot distinguish them. They cannot stop with their unequal joined labels before depth $j$, regardless of the subsequent literal words. Taking all such differing boundaries and the reached-parent floor gives exactly the last line of (44.2). This lower bound applies to $00$ as well as $01$, so permitting $00$ cannot improve the envelope.

The remaining even case is $a=2,q=1,\Lambda_0\ne\Lambda_1$. The actual tail-zero, value-zero sources at phases $0,1$ both observe the first word $11$ with difference one. The next block's first bit must be the first zero, and suppresses phase one's active absolute position two. Their remaining coefficients are both zero through absolute position $2p-2$: phase zero's next coefficient is at $2p-1$, and phase one's next after the suppressed position is later still. Their tails become common at that zero. Every later common input before position $2p-1$ therefore gives equal outputs, or simultaneous absorbing rejection; neither source can stop correctly with its different joined label. Reaching the potentially separating endpoint requires fee at least $p$. For $p=2$, that position is already the parent's last bit. The global stream (42.4) attains $p$: each outsider $2,\ldots,p-1$ obtains its own right-endpoint pulse, and the last wrapped pulse selects phase zero against phase one. Earlier rejection labels use their eligible rectangles. Every post-root word begins zero, so all its actual seams are safe. No freshness of a low label relative to a high or outside label is assumed.

At cut zero the supplied phase-only fee $J$ gives both inequalities, with an attaining right-endpoint scan: at index $t<J$ use $01$ if $\Lambda_{t+1}\ne\Lambda_0$ and $00$ otherwise. Every actually running source pays for each word, including a zero word at an empty nonbaseline slot. Its first bit is zero, so it is safe for every INITIAL tail. At the first nonzero difference return that slot's label; after all zero differences return $\Lambda_0$. This is exactly [S10]'s supplied $g=2,u=1$ protocol on the join, not a new phase-only discovery.

We can now compare all actual controllers. Every all-one option has a correct stream of fee at most its depth by Theorem 42.2, and every eligible cut has just been given a correct common stream of fee at most $E(a)$. Conversely take any finite correct preset stream and join its decoder using Theorem 29.2. If all sources stop before its first zero, the all-one normalization in Theorem 42.2 supplies a member of $\mathcal A$ no larger than its fee, including omission of a wholly rejecting crossing block. If its first-zero parent is reached, its cut is eligible, it pays the parent, and the actual-source lower bounds just proved give worst fee at least $E(a)$. In particular a written but unissued parent is never used to impose the floor $q+1$; its smaller all-one option handles that execution. These cases exhaust the original common streams and preserve all earlier stopped and rejected archives. Taking the minimum proves (44.3). If the displayed set is empty, a hypothetical finite controller would supply a member by this same argument, proving infinity. The constructions at its least member attain the exact fee, since any smaller actual worst fee would contradict the reverse inequality. ∎

**定理 44.3（Sharp finite preset ceiling, credited endpoint attainment）。** In (41.1),

$$
 C_{\rm pre}(f)<\infty\quad\Longrightarrow\quad
 C_{\rm pre}(f)\le p=\frac{k+1}{2},\qquad
 \sup\{C_{\rm pre}(f):C_{\rm pre}(f)<\infty\}=p.
\tag{44.6}
$$

**证明。** Theorem 42.2 already supplies the uniform bound. In the closed envelope, all-one depths and $J$ are at most $p-1$. Odd cuts have $q\le p-2$; when their suffix fee is positive, (43.3) and the one-block case give $\Psi(q+1)\le p-q-2$, and when it is zero their horizon is simply $q+1\le p-1$. Thus every odd horizon is at most $p-1$. Nonexceptional even horizons are at most $p-1$ unless $q=p-1$; for that final cut at $p\ge3$, the all-one option $p-1$ replaces the unissued parent as proved above. The endpoint exception has horizon $p$, including the $p=2$ final even cut. For sharpness use the already supplied complete endpoint-threshold target of Definition 2.1 at $m=2,k=2p-1$. Theorem 2.2, equivalently [S20, Theorem 3.1], gives $C_{\rm ad}=C_{\rm pre}=\lceil(k+1)/2\rceil=p$. This supplied family certifies sharpness; its restricted exact law is not redelivered as new mathematics. ∎

**定理 44.4（The delayed endpoint pair with arbitrary full outside labels）。** In (41.1), suppose cut $a=2$ is eligible and $\Lambda_0\ne\Lambda_1$. The complete target may have arbitrary outside phase labels, arbitrary coincidences with high labels, and different component tables, subject only to (41.5) at this cut. Then

$$
 C_{\rm ad}(f)=C_{\rm pre}(f)=p.
\tag{44.7}
$$

**证明。** Eligibility says that all top two INITIAL tails $s\in\{k-2,k-1\}$ have one joined label $R$, over every phase, and all lower tails at phase $i$ have label $\Lambda_i$. Choose a free-value component $v$ in which the two endpoint low labels differ. At least one of these two labels differs from that component $R_v$. At that endpoint choose the two actual sources with INITIAL tails $k-3$ and $k-2$, common initial value $v$, and common phase. Any first word containing a zero has zero or one leading one; both sources survive its leading run and merge at that zero with the same archive but different required labels. Hence a correct adaptive root on this value fibre must be $11$, exactly as in the lower-bound mechanism of Theorem 2.2/[S20]. It cannot stop at the free reading because those actual labels differ.

Now choose the two endpoint sources at INITIAL tail $k-3$, with that same initial value $v$. Their $11$ output is the same successful value $v\oplus1$, and their current tails both equal $k-1$. Their different component labels forbid stopping. Any next word beginning one rejects both at its first bit, before a new observable endpoint, and makes them permanently indistinguishable. The next word on their shared archive must therefore start zero. That zero suppresses phase one's absolute coefficient at position two and makes their current tails common. Until absolute position $T-1=2p-1$, phase zero and phase one have no further unsuppressed coefficient difference. Induction on actual acquired endpoints forces identical future adaptive actions and stopping decisions before that position; common rejection gives no exception. They cannot return their unequal INITIAL labels at a total fee below $p$.

The preset stream (42.4) attains $p$ for the full target, not just these two sources, by Theorem 44.2's exceptional even-cut construction. It identifies all outside phases when their labels require it, decodes every high-tail rejection from the common high label, and works on both free values in one stream. Since $C_{\rm ad}\le C_{\rm pre}$, the lower and upper bounds give (44.7). The new scope here is the arbitrary complete outside and value tables; the endpoint obstruction itself is credited reuse. This family does not establish the adaptive optimum for an arbitrary mixed-tail table without the stated cut and endpoint inequality. ∎

## 45. Mathematical suppliers, experiment correspondence and residual scopes

**数学引文 45.1（Exact reuse and the width-two deductions）。** Chapters 41–44 retain the original matched reader, actual complete-block histories, endpoint-only observations and INITIAL labels of Chapters 1 and 24. The fixed supplier [S1, Definition 1.2, Convention 1.3, Definition 2.1, Proposition 2.3 and Lemmas 4.2–4.3] gives the corresponding original operations, joint history witnesses, alphabets and first-zero loss. Theorem 24.2 supplies the common eligible cut, and Theorem 29.2 supplies exact preset value joining, both at their original all-parameter scopes. Their uses in (41.5), the rejected rectangles and the one-stream decoder are credited reuse. [S10, Interface 2.1] gives literal path charges; its Theorem 4.1 and Corollary 4.2 at $g=2,u=1,p=(k+1)/2$ already settle all phase-only tables with fee $J$. Theorem 2.2/[S20, Theorem 3.1] supplies the restricted endpoint family's exact fee and the actual endpoint-return lower-bound mechanism.

Theorem 33.2 and its sparse simultaneous-row proof require $m\ge3$ and do not prove width-two realization. The wide results of Theorem 38.1 and Corollary 38.2 require their specified room or $m\ge2k+1$, and do not price this proper-narrow slice. Theorem 41.3 proves the missing stopping-aware chronological seam bridge; Theorem 42.2 uses it on the whole INITIAL target; Theorem 43.2 solves the particular live suffix; Theorem 44.2 evaluates the full common-cut minimum, with actual-source lower bounds and one fixed literal attainment. These statements and the arbitrary-outside extension in Theorem 44.4 are `repo-derived` ordinary mathematical deductions on the cited interfaces. No broad novelty or priority claim is made.

The mature experiment correspondence is Moore's *Gedanken-Experiments on Sequential Machines* [L41, pp.129–131]: a simple experiment sends either a fixed sequence or a sequence chosen from previous outputs to one machine and draws a conclusion about its beginning state; multiple copies are a separate experiment, and an absorbing destroyed state can prevent further learning. Here a single input symbol is an entire two-bit complete block, its output is that block's endpoint, and the conclusion is only the INITIAL target label. Van den Bos and Vaandrager's *State Identification for Labeled Transition Systems with Inputs and Outputs*, arXiv:1907.11034v2 [L42, Definitions 12, 14, 17 and 20, pp.10–12, Figure 3], supplies finite acyclic tests, inputs admitted for every current candidate and separation by disjoint completed observations, including an example where first actions merge candidates irreversibly. These semantic facts are `literature-attested`. Neither primary source supplies the reader-specific incidence, literal seams, closed expression (44.3) or $p$-block fee. A full-state distinguishing requirement is also stronger than separating just unequal $\Lambda$ labels. Copies, resets, intermediate observations and free transfer actions are not imported. Related distinguishing/checking-sequence search results without a proved operation, observation and fee correspondence supply no premise of (44.3); a bounded search non-hit implies neither novelty nor nonexistence.

The related original-source contracts remain separate. [FIB relational continuation, §42](https://github.com/the-omega-institute/trureturing/blob/9c5dbf0893d173600cf5a961c6b0a6090e9caa89/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md) concerns synchronized Hofstadter numerical readout and counts all automaton states. [Actual occurrence continuation, §52](https://github.com/the-omega-institute/trureturing/blob/9c5dbf0893d173600cf5a961c6b0a6090e9caa89/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md) uses ordered-tree occurrences, whole-source grafts and an additional propagation law on their actual seams. [Unit-context response transport, §71, especially Theorems 71.6 and 71.8](https://github.com/the-omega-institute/trureturing/blob/9c5dbf0893d173600cf5a961c6b0a6090e9caa89/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) preserves specified same-address responses and expressly separates them from nominal material and paid-cost equivalence. The source declarations [ActualDyadicAcquisitionTrace](https://github.com/the-omega-institute/trureturing/blob/9c5dbf0893d173600cf5a961c6b0a6090e9caa89/D5/S3/ConceptDynamics/Coding/ActualDyadicAcquisitionTrace.lean) and [ActualDyadicCausalPrefixRepairCapacity](https://github.com/the-omega-institute/trureturing/blob/9c5dbf0893d173600cf5a961c6b0a6090e9caa89/D5/S3/ConceptDynamics/Coding/ActualDyadicCausalPrefixRepairCapacity.lean) distinguish forward events from nondisturbing reads and bound the count of reads on their own sensor and source. They supply no destructive KBonacci tail, whole-block-only observation or unit-per-emitted-block correspondence. None is a cost-theorem premise here; the required KBonacci realization is proved directly in (41.3) and Theorems 41.3–44.2.

**定义 45.2（Unchanged original objective and exact remaining boundary）。** The original objective remains the exact minimum worst-branch ACTUAL EMITTED COMPLETE-BLOCK fee for every arbitrary attainable immutable INITIAL target, all original $k\ge2,m\ge1$, separately adaptive and one-global-stream preset, with both original alphabets, the full joint prior, free initial value or independent bottom, and all paid waits, padding, clearing and repair blocks. Theorem 44.2 settles the entire arbitrary-target preset slice $m=2,k\ge3$ odd, including zero and infinity; it does not replace the full objective by an acquired-support problem. Theorem 44.4 gives an adaptive equality only for its full stated endpoint family, and Theorem 43.2 gives an additional adaptive equality only at its specified actually acquired suffix.

Even-order width two has $g=1$ and retains its different physical-path parity and chronological seams. Arbitrary coprime proper-narrow common-stream compatibility, remaining critical and insufficient-room preset scopes, and arbitrary INITIAL adaptive gaps outside the supplied exact laws remain within the unchanged original goal. The supplied arbitrary unit-width laws, noncoprime $m\ge3$ certificate, wide and room-qualified preset laws, critical-width adaptive law and all other credited families retain their precise hypotheses; this append asserts no new resolution outside (41.1) or the stated conditional suffix and endpoint scopes. Mathematical counterexample 34.4's raw $11\mid11$ width-two seam and its separate seven-phase coprime acquired archive remain unchanged. Later written words after all relevant sources stop are not observations, and an archive may stop only at a completed endpoint it has actually acquired. No deferred alternative-region proposal is a proved result here. These are ordinary proofs in the declared model, without a Lean/kernel certification claim.

[L41]: https://www.cs.cmu.edu/~cdm/resources/Moore1956-gedanken-experiments.pdf
[L42]: https://arxiv.org/pdf/1907.11034v2

## 追加锚（本行以下为增补区）

## 46. Actual first parents at odd critical and strictly wide widths

**定义 46.1（Full INITIAL domain and the common cut）。** Fix $k\ge2$ and assume either

$$
m>k,\qquad\text{or}\qquad m=k\ge3\text{ with }k\text{ odd}.
\tag{46.1}
$$

Use the original integer weights, matched mod-two output, literal updates (1.1)–(1.2), endpoint-only observations and actual emitted complete-block fee of Definition 1.3. Set $T=k+1$, $g=\gcd(m,T)$ and $P=g\mathbb Z/T\mathbb Z$. The two control alphabets remain all literal $m$-bit words and the internally legal literal $m$-bit words; legality across their seams is still required. The prior is every actual finite complete-block history, and the target is any $f:Q\to Y$ on its entire INITIAL record set, for any set $Y$. A history target retains the necessary factorization $F=f\circ q$ through its INITIAL record, supplied by [S1, Proposition 2.2]; different labels within one record fibre cannot be acquired by these operations. Initial $\bot$ is independently observed and has its own arbitrary label, returned at fee zero. A preset controller issues prefixes of one fixed literal stream; its stopping and decoding use only its own chronological issued-block/output archive. It has no reset, source copy, hidden initial clock, intermediate observation or borrowed branch observation. Every reached complete block is paid, including waiting, padding, clearing and repair blocks.

The all-width joint realization is the one in Definition 36.1: for every $v\in\mathbb F_2$, $j\in P$ and $0\le s<k$, take the single history (1.3) with $\ell\equiv0\pmod m$, $\ell\equiv-j\pmod T$ and $\ell\ge s+2$. Its value, phase and tail are simultaneously $(v,-j,s)$. The entire history avoids $1^k$, so every constituent block belongs to both alphabets. An endpoint with tail $k-1$, followed by $10^{m-1}$, realizes absorbing rejection under the internally legal alphabet. No common hidden initial length is assumed or observed.

Use the ordered value join already proved in Theorem 29.2:

$$
\Gamma(j,s)=\bigl(f(0,-j,s),f(1,-j,s)\bigr),\qquad
\Lambda(j)=\Gamma(j,0).
\tag{46.2}
$$

Pair equality means equality of the two corresponding components; labels within or across components may coincide arbitrarily. A common eligible cut is an $a\in\{0,\ldots,k-1\}$ satisfying (36.2). Write $\mathcal A(\Gamma)$ for these cuts. This is the supplied all-width first-zero criterion of Theorem 24.2, with no preceding all-one complete block since $m\ge k$. The high band is empty at $a=0$; otherwise its joined label $\rho_a$ need not be fresh. Every target remains a label of the immutable INITIAL source.

**定义 46.2（The same-word parent response family）。** At a cut $a$, retain the actual literal parent set

$$
\mathcal B_a=\{B\in\{0,1\}^m:B\text{ avoids }1^k,\
 B_i=1\ (i<a),\ B_a=0\}.
\tag{46.3}
$$

Let $\tau(B)$ be its actual terminal run of ones. Its arithmetic root response and actual image are

$$
e_B(j)=\bigoplus_{i=0}^{m-1}B_i c_{i-j},\qquad
E_B=\{j\in P:e_B(j)=1\},\qquad
\mathcal R_a=\{E_B:B\in\mathcal B_a\}.
\tag{46.4}
$$

A successful source observes $e_B(j)$ as its first endpoint difference. Formula (46.4) does not turn a rejecting source's output into a binary difference. Both $E_B$ and $\tau(B)$ belong to this same parent, with its same first zero.

For use in the minimum below, the supplied literal image mechanisms [S10, Interface 2.1] and [CR46, Theorem 2.2] give the following descriptions. They are consumed parent interfaces, rather than separate cost results. At odd critical width $m=k$,

$$
\begin{aligned}
\mathcal R_0&=\{E\subseteq P:|E|\text{ even},\ 0\notin E\},\\
\mathcal R_a&=\{E\subseteq P:|E|\text{ even},\ \{0,a\}\subseteq E,\
 E\cap\{1,\ldots,a-1\}=\varnothing\}\quad(a>0).
\end{aligned}
\tag{46.5}
$$

Its actual unique word is $B_i=\bigoplus_{j=0}^i\mathbf1_E(j)$, $0\le i<k$. Empty and full masks are retained whenever (46.5) permits them.

For $m>k$ and $g=1$, put $L=m-a-1$, let $H_0=\varnothing$, $H_a=\{0,a\}$ for $a>0$, and let $V_a$ be the ordered consecutive vertices $[a+1,m]\pmod T$. Then

$$
\mathcal R_a=
\begin{cases}
\{H_a\mathbin\triangle F:F\subseteq V_a,\ |F|\text{ even}\},&L<k,\\
\{H_a\mathbin\triangle F:F\subseteq P,\ |F|\text{ even},\
 F\ne\{a+1,m\}\pmod T\},&L=k,\\
\{E\subseteq P:|E|\text{ even}\},&L\ge k+1.
\end{cases}
\tag{46.6}
$$

In the first line the path vertices are distinct. In the second line the excluded mask has the unique free inverse $1^k$. In the last line a full physical cycle fits in the free suffix. Since $g=1$, $m>k$ necessarily implies $m\ge k+2$.

For $m>k$ and $g\ge2$, define disjoint actual coordinate-position sets

$$
A_j=\{i:0\le i<m,\ i\equiv j\text{ or }j-1\pmod T\},\qquad j\in P.
\tag{46.7}
$$

A mask $E$ lies in $\mathcal R_a$ precisely when

$$
\mathbf1_E(j)=|A_j\cap[0,a-1]|\pmod2
\quad\text{at each }j\text{ with }A_j\cap[a+1,m-1]=\varnothing.
\tag{46.8}
$$

All other actual coordinates are independently free. These formulas retain repeated physical residue positions and the forced bit $B_a=0$. They grant no additional space to the first parent.

## 47. The exact continuation shared by both actual parent children

**定义 47.1（Actual multiplicities and aggregate types）。** Fix one $B\in\mathcal B_a$ with $a\in\mathcal A(\Gamma)$, already emitted as one paid block. Its successful phase children are $S_1=E_B$ and $S_0=P\setminus E_B$. On each child use its immutable joined labels $\Lambda$. For any $S\subseteq P$ put

$$
N(S)=|S|,\qquad n(S)=|\Lambda[S]|,\qquad
r(S)=|\{L\in\Lambda[S]:|S\cap\Lambda^{-1}(L)|\text{ odd}\}|.
\tag{47.1}
$$

These multiplicities count actual phases, not INITIAL tails, histories or label names. Define $\ell(0)=\ell(1)=0$ and $\ell(n)=\lceil\log_2 n\rceil$ for $n\ge2$, and put $h=\max\{\ell(n(S_0)),\ell(n(S_1))\}$.

For $d\ge0$ let $\Sigma_d(S)$ consist of the vectors

$$
\bigoplus_{j\in S}z_j,\qquad z_j\in\mathbb F_2^d,\qquad
\Lambda(j)\ne\Lambda(j')\Longrightarrow z_j\ne z_{j'}\quad(j,j'\in S).
\tag{47.2}
$$

A label may occupy several codes. Codes used by different labels in this same child must be disjoint; codes on different children may coincide. The aggregate is over one code per actual phase, with repetitions included. Write $V=\mathbb F_2^d$ and $V^\times=V\setminus\{0\}$.

**定理 47.2（Matching signatures, an exact suffix fee and one safe literal stream）。** After the actual parent of Definition 47.1, let $K(B,\Lambda)$ be the least worst additional emitted complete-block fee of a continuation common to both successful children, with stopping based on each source's own acquired archive. Both original alphabets have

$$
K(B,\Lambda)=
\begin{cases}
h,&g\ge2\text{ or }(g=1\text{ and }T\text{ odd}),\\
h+\chi,&g=1\text{ and }T\text{ even},
\end{cases}
\qquad
\chi=\mathbf1_{\{\Sigma_h(S_0)\cap\Sigma_h(S_1)=\varnothing\}}.
\tag{47.3}
$$

In particular $\chi=0$ when $h=0$. Its value is determined by the following closed aggregate table, which is used inside (47.3). Capacity failure $n(S)>2^d$ gives $\Sigma_d(S)=\varnothing$. An empty $S$ gives $\{0\}$, and at $d=0$ every capacity-admissible child gives $\{0\}$. If $N(S)$ is odd and capacity holds, $\Sigma_d(S)=V$. For nonempty even $N(S)$ at $d=1$,

$$
\Sigma_1(S)=
\begin{cases}
\mathbb F_2,&n(S)=1,\\
\{0\},&n(S)=2,\ r(S)=0,\\
\{1\},&n(S)=2,\ r(S)=2.
\end{cases}
\tag{47.4}
$$

For nonempty even $N(S)$, $d\ge2$, $M=2^d$ and $n(S)\le M$,

$$
\Sigma_d(S)=
\begin{cases}
\{0\},&n(S)=M,\ r(S)\in\{0,M\},\\
V^\times,&n(S)=M,\ r(S)\in\{2,M-2\},\\
V^\times,&n(S)<M,\ N(S)=n(S)\in\{2,M-2\},\\
V,&\text{otherwise}.
\end{cases}
\tag{47.5}
$$

Thus the even-cycle surcharge occurs exactly when one child's capacity-dimension spectrum is zero-only and the other's is nonzero-only. Every finite value in (47.3) is attained by one literal suffix at its actual chronological indices, from the actual incoming tail $\tau(B)$, with no separate clearing or repair block. This is an additional fee after an already paid parent; its acquisition is not free.

Proof. All successful INITIAL tails at a fixed phase merge at the parent's first zero. Their label is $\Lambda(j)$ by eligibility, and their terminal tail is $\tau(B)$. For every $j\in P$ an actual INITIAL tail-zero representative survives this parent. For a fixed free value, its root difference chooses $S_0$ or $S_1$, and each child's current value is common. Across both children the raw tails are common. This is a statement about the same issued parent applied to the joint sources of Definition 46.1.

First extract a necessary condition from an arbitrary correct common suffix of additional bound $d$. Apply the value join already supplied by Theorem 29.2. Continue the actual tail-zero phase representatives only as a raw set calculation when they have stopped. Their first later rejecting block, if one exists, is simultaneous across all phases, since legality depends only on this common tail and the common literal bits. Any live archive entering that block must already have a constant joined label: its members would all receive the same absorbing output, and no later output could recover a distinction. It can therefore stop before that block. An archive stopped earlier was already constant as well.

Retain each whole successful response row before that first raw rejection, and complete to $d$ rows by whole zero rows if necessary. For a written successful row its entries on phases that stopped earlier are evaluations of (36.3), not further observations or emitted actions. In particular this operation does not pad individual stopped columns independently. Within either fixed parent child, equal full suffix columns imply identical observed prefixes through the earlier stopping time, on one free-value fibre. The deterministic stopping rule then returns the same joined label. Unequal $\Lambda$ labels in that child therefore have unequal suffix codes. Binary capacity gives $d\ge h$.

When $g=1$, every retained literal row has full-phase XOR zero by (36.4). Hence its column vectors satisfy

$$
\bigoplus_{j\in S_0}z_j=\bigoplus_{j\in S_1}z_j.
\tag{47.6}
$$

The same equality holds for the added whole zero rows. Consequently a correct suffix of bound $d$ requires $\Sigma_d(S_0)\cap\Sigma_d(S_1)\ne\varnothing$. Attempted rejection and early stopping do not evade this necessary condition. For $g\ge2$ only the binary-capacity condition is needed.

We now evaluate the aggregates that this necessary condition actually uses. Capacity, the empty child and $d=0$ follow directly from (47.2). If $N(S)$ is odd, translating every assigned vector by $w\in V$ preserves separation and changes its aggregate by $w$. Any capacity-admissible assignment thus yields every element of $V$. For even $N(S)$ and $d=1$, a single label can contribute zero by repeating zero and one by using one at one phase and zero at every other phase. With two labels each must own one of the two vectors, so their even or odd multiplicities give exactly (47.4).

For $d\ge2$, use the credited Bajnok–Edwards subset spectrum [S27, Corollary 18], with precisely the hypotheses instantiated in Mathematical citation 37.2: distinct subsets of the full additive group $\mathbb F_2^d$, with zero allowed, have aggregate zero at every cardinality except $2,M-2$. The empty subset is direct. This existing spectrum is a step of the present continuation proof.

At saturation $n(S)=M$, each label must own exactly one vector and every vector is used. A second vector for one label would leave fewer than $M-1$ vectors for the other labels. The aggregate is therefore the sum of the $r(S)$ distinct odd-cell vectors. It is forced to zero at $r=0,M$; it cannot be zero at $r=2,M-2$. At every other $r$ the credited spectrum provides zero. For $0<r<M$ a nonzero sum also exists: if a selected $r$-subset sums to zero, exchange one selected vector with an unselected vector, changing its sum to their nonzero XOR. Invertible linear maps of $V$ preserve separation and act transitively on nonzero vectors. Whenever one nonzero aggregate occurs, every nonzero aggregate occurs. This proves the saturated lines of (47.5).

Below saturation, a nonzero aggregate always exists. If $r>0$, then $r<M$; choose one distinct vector per label, choosing an $r$-subset with nonzero sum for the odd cells by the same exchange argument. If $r=0$, choose one distinct vector per label, then change one phase of an even cell to one unused vector. That cell has at least two phases. Its contribution changes from zero to the nonzero XOR of the old and new vectors, while different labels still use disjoint codes. Again every nonzero aggregate follows by an invertible linear map.

For a zero aggregate below saturation, the one-vector-per-cell assignment works whenever $r\notin\{2,M-2\}$: give the odd cells a zero-sum $r$-subset and the even cells distinct unused vectors. The exceptional cardinalities are repaired by the actual multiplicities, as in the consumed constructions of Theorem 37.1, with the small-label case included here. If $r=2$ and an even cell exists, split that cell between two vectors with odd counts $1,t_L-1$. Choose those two vectors and the two odd-cell vectors to be four distinct elements of an affine two-dimensional plane, whose aggregate is zero. All other cells are even and receive distinct unused vectors. The total number used is $n+1\le M$. If no even cell exists, there are just two odd cells. Unless both are singletons, one has size at least three; split it between three vectors with odd counts $1,1,t_L-2$ and give the other cell the fourth plane vector. Their aggregate is zero. Two differently labelled singleton phases cannot have aggregate zero at any dimension.

If $r=M-2$ and $n<M$, then $n=M-2$ or $M-1$. In the latter case split its unique even cell between two unused vectors with odd counts; the odd-use vectors become the entire cube. In the former case all cells are odd. If $N>n$, a cell has size at least three; split it between three vectors with odd counts $1,1,t_L-2$, and give each other cell one distinct vector. Again the entire cube has odd multiplicity, with zero aggregate. If instead $N=n=M-2$, all phase codes are distinct; their sum is the sum of the two omitted vectors, which is nonzero. At $M=4$ the two exceptional cardinalities coincide, and the two-odd-cell construction already handles them. These cases exhaust all unsaturated zero failures and prove (47.5). Splitting a label uses its actual phases and never shares one code across different labels.

If $g=1$ and $T$ is odd, exactly one parent child has odd phase count. At dimension $h$ it can translate its codes to match the aggregate of the other child. Thus (47.6) can always be met at the capacity bound. If $T$ is even, both child sizes are even because $E_B$ has even cardinality. Their table gives an intersection at $h$ unless one spectrum is $\{0\}$ and the other $V^\times$. In that mismatch $h\ge1$.

One additional coordinate always repairs a mismatch. Put $M=2^h$ and evaluate at dimension $h+1$. Every nonempty child is now unsaturated, with at most $M$ labels in a cube of size $2M$. By (47.5), or its small cases, its spectrum contains every nonzero vector; the permanent two-singleton obstruction merely excludes zero. The other singleton obstruction would require $n=2M-2>M$, except at $M=2$, when it is the same two-singleton obstruction. Two nonempty children can thus match a nonzero aggregate. If one child is empty, the other has all $T\ge4$ actual phases. It is neither a two-singleton child nor a capacity-admissible $2M-2$-singleton child, so it admits zero in the larger cube. At $h=0$ both spectra were already $\{0\}$. This proves that the least algebraically possible suffix length is exactly (47.3).

It remains to realize these codes on one actual stream. When $g\ge2$, take arbitrary separated $h$-bit codes on each child. When $g=1$, choose codes with matching aggregates at the least length just proved. Matching two nonzero aggregates is possible by an invertible linear map on one child's codes. In either case denote the combined coordinate rows by $q_t:P\to\mathbb F_2$, at absolute paid indices $t=1,\ldots,K$. When $g=1$ every such row has even full-phase XOR. The same-label splitting allowed above is retained.

For strictly wide $m>k$, first consider $g\ge2$. At index $t$ let $u_t=tm\pmod T$. For each actual $j$, represent $j-u_t$ by $r\in\{0,g,\ldots,T-g\}$. Put an optional one at position $r-1$ if $r>0$, and at position $T-1$ if $r=0$, exactly when $q_t(j)=1$. Put zero at every other position. Since $m\ge T$, all these positions fit in the block. Each pulse selects only $j$ among actual phases: its other ambient vertex is outside $P$. The positions are at least one and are spaced by $g\ge2$, so the block starts zero and all its ones are isolated. This consumes the supplied sparse-row mechanism, including the singleton-phase case $m=T$.

For strictly wide $g=1$, one has $m\ge T+1$. Consume the zero-prefix case $a=0$ of [S26, proof of Theorem 3.1], retaining its room requirement $T+1\le m$. Put bit zero at position zero. In positions $1,\ldots,T$ realize $q_t$ by solving

$$
x_r\oplus x_{r-1}=q_t(u_t+r),\qquad r\in\mathbb Z/T\mathbb Z.
\tag{47.7}
$$

Even total charge makes this cyclic system consistent. Its two solutions complement one another; choose one with at most $\lfloor T/2\rfloor<k$ ones and place its residue bits in those $T$ actual positions. All remaining padding positions are zeros. Formula (36.3) gives exactly $q_t$. The free segment has fewer than $k$ ones in total, so it has no forbidden run. Its preceding zero separates it from every actual incoming tail. This reuse concerns subsequent rows only; it does not replace the already emitted first parent or enlarge that parent's free segment.

At odd critical $m=k$, use $T$ even and $u_t=tk\pmod T$. Replace each combined row by

$$
\widetilde q_t(j)=q_t(j)\oplus q_t(u_t)\quad(j\in P).
\tag{47.8}
$$

This complements the entire coordinate when necessary. Its full XOR stays zero because $T$ is even, and its value at the moving anchor $u_t$ is zero. It changes every code by the same coordinate translation, preserving all within-child equalities and inequalities. Both even-sized children's aggregates are unchanged. The actual critical inverse supplied by [CR46, Theorem 2.2] is

$$
B^{(t)}_i=\bigoplus_{r=0}^i\widetilde q_t(u_t+r),\qquad 0\le i<k.
\tag{47.9}
$$

It starts zero. Its remaining $k-1$ positions cannot contain $1^k$, and its first zero clears any incoming tail before a one is read. The omitted cyclic edge is exactly the zero boundary bit in the supplied critical inverse; even full-phase charge verifies its last response coordinate. Hence (47.9) realizes the transformed row at this actual chronological displacement.

Every construction gives the same word to every running source at a given index. Every word starts zero and is internally legal, so every seam from the actual parent's tail and every later tail is safe. No additional clearing action is inserted. At each reached endpoint a source records its own successive difference, selects its already acquired parent child and decodes its joined label from the separated suffix code. A homogeneous archive may stop earlier. No formal row entry on a stopped phase is used as an observation by another source. All padding, compensation and clearing bits are inside the counted complete blocks; each reached zero row is still paid. The suffix fee is at most the stated $K$, while the preceding necessity and capacity arguments rule out every smaller bound. Thus the upper and lower actual fees match. ∎

## 48. The full INITIAL first-parent minimum

**定理 48.1（Exact arbitrary-target GLOBAL preset envelope）。** For every $f$ in Definition 46.1, with all its actual INITIAL phases, values, tails and independent bottom, and either original alphabet,

$$
C_{\rm pre}(f)=
\begin{cases}
0,&\Gamma\text{ constant on successful INITIAL records},\\
+\infty,&\Gamma\text{ nonconstant and }\mathcal A(\Gamma)=\varnothing,\\
1+\displaystyle\min_{\substack{a\in\mathcal A(\Gamma)\\E\in\mathcal R_a}}
\bigl(h(E)+\chi(E)\bigr),&\text{otherwise}.
\end{cases}
\tag{48.1}
$$

Here $h(E)$ is the child-capacity quantity of Definition 47.1, and $\chi(E)=0$ when $g\ge2$ or $T$ is odd. When $g=1$ and $T$ is even, $\chi(E)$ is exactly the spectrum-intersection indicator in (47.3), evaluated by (47.4)–(47.5). The minimum retains the actual parent images (46.5)–(46.8), including empty/full masks, and evaluates the entire common continuation. Equivalently it is a minimum over the actual words $B\in\mathcal B_a$ of $1+K(B,\Lambda)$. Every finite value has an optimal one-global-stream literal protocol with archive-dependent stopping.

Proof. By Theorem 29.2 it suffices to acquire the joined target; this equality includes infinity and uses one stream on both free values. A constant joined target stops free. Conversely at fee zero the free scalar value cannot distinguish two different joined labels in the full joint successful prior. Thus the first case is exact.

Suppose $\Gamma$ is nonconstant. Every free-value archive for this joined target is initially unresolved. A first block containing $1^k$ internally rejects every successful source and cannot return two different joined labels; neither can the all-one word, since $m\ge k$. A correct first block therefore lies in $\mathcal B_a$ for some $0\le a<k$.

Its leading $a$ ones reject exactly the INITIAL tails $s\ge k-a$. Their entire first endpoint archive on a fixed free-value fibre is the same absorbing output; they must have one joined label $\rho_a$. Its zero merges all lower tails at each fixed phase. Those sources had the same free value and the same pre-zero increments, so their complete acquired archives and their records after the zero coincide. Different immutable labels could not subsequently be distinguished. As tail zero is among them, their label must be $\Lambda(j)$. These are exactly the eligible-cut conditions (36.2), with no additional freshness condition. This necessity uses actual same-history witnesses at each phase and each compared INITIAL tail. Hence no eligible cut implies infinite fee.

For an eligible parent, all lower tails at phase $j$ survive its remaining internally legal suffix and acquire the arithmetic response $e_B(j)$. Their common terminal tail is the same actual $\tau(B)$. The successful archives are precisely its actual children $E_B$ and $P\setminus E_B$, with their original $\Lambda$ labels. Every phase has a surviving tail-zero witness. Theorem 47.2 therefore supplies a lower bound of $1+K(B,\Lambda)$ on the total worst actual fee of every controller using this parent. High-tail rejection can stop at fee one, and the other children's early stopping was included in that theorem. Taking the minimum gives the lower inequality in (48.1).

For completeness, the displayed parent descriptions preserve literal attainability. At critical width this is exactly [CR46, Theorem 2.2]: its unique inverse, prescribed first-zero coordinates and actual terminal tail occur together. At strictly wide coprime width, the forced prefix $1^a0$ contributes $H_a$. The free $L$ bits occupy consecutive physical edges $a+1,\ldots,m-1$, with vertices $V_a$. The consumed [S10] path inverse realizes precisely every even charge on that path when $L<k$. At $L=k$ the same inverse is unique and the one excluded charge has inverse $1^k$; it would reject every surviving source. At $L\ge k+1$ use the first full $T$-edge cycle of the free suffix, choose a complementary solution with fewer than $k$ ones, and set every other free bit zero. The separator at position $a$ makes the prefix safe independently of that free segment. These are exactly (46.6), including the omitted literal representative.

At strictly wide noncoprime width, the sets $A_j$ are disjoint because actual phases are separated by $g\ge2$. The fixed prefix contributes the right side of (46.8). If no free position lies in $A_j$, that contribution is forced. Otherwise choose at most one free one in that set to achieve either desired parity, leaving its other free positions zero. These choices are independent across actual phases. They use at most $p=T/g<k$ suffix ones in total, so their free suffix contains no $1^k$; the prescribed first zero separates it from the leading run $a<k$. This realizes every mask in (46.8) and establishes its necessity as well. For each mask the chosen word is a member of $\mathcal B_a$, with its terminal tail read from that word. No response, rejection threshold or tail was borrowed from another representative.

Choose a minimizing eligible cut and actual parent word. On its first rejecting endpoint return the component of $\rho_a$ selected by the remembered INITIAL value. Otherwise use exactly the safe common suffix of Theorem 47.2, decoding the same component of $\Lambda(j)$ from the parent difference and the source's own subsequent differences. Initial bottom returns its independent $f(\bot)$ freely. This stream has at most $1+K$ actually emitted blocks on every source, all original labels preserved. The preceding lower bound makes its worst fee exact. The parent sets are finite and nonempty, since $1^a0^{m-a}$ is always a member, so every asserted finite minimum is attained.

In particular, a constrained first parent is never replaced by an unrestricted phase-code row. At the supplied $k=2,m=4$ example of [S26, Theorem 6.1], its only eligible cut is $a=1$. In INITIAL $j$ coordinates the low labels are $(A,B,A)$ and the common high label is fresh. Its actual parents $1000,1001,1010$ have masks $\{0,1\},\varnothing,\{1,2\}$ respectively. None gives a homogeneous one-block partition; the actual parent minimum has fee two, as that supplied theorem states. This instance is credited overlap, and the same parent restriction remains in (48.1) throughout the moderate-wide insufficient-room region. ∎

## 49. Sharp complete-source surcharges at odd critical width

**定理 49.1（A binary forced-parent surcharge at every odd order at least five）。** Let $k=m\ge5$ be odd and $1\le u\le(k-3)/2$. Choose $A\ne B$, any label $R$ and any independent bottom label. On both free-value fibres define the full INITIAL target by

$$
f(v,-j,s)=
\begin{cases}
A,&s=0,\ 0\le j\le2u,\\
B,&s=0,\ 2u<j\le k,\\
R,&1\le s<k.
\end{cases}
\tag{49.1}
$$

Allow $R=A$ or $R=B$. Then the supplied critical adaptive benchmark and the new GLOBAL preset fee satisfy

$$
C_{\rm ad}(f)=2,\qquad C_{\rm pre}(f)=3.
\tag{49.2}
$$

One optimal preset stream is the literal three-block word

$$
1^{k-1}0\ \bigm|\ 01\,0^{k-2}\ \bigm|\
000(10)^u0^{k-3-2u}.
\tag{49.3}
$$

Proof. Since both low labels occur, at some actual phase the label at INITIAL tail zero differs from $R$. Any $a<k-1$ leaves tails zero and one surviving together at that phase, so it is ineligible. The unique eligible cut is $a=k-1$, and its unique critical parent is $1^{k-1}0$, with actual mask $E=\{0,k-1\}$. Its endpoint child has two different singleton labels, with $\Sigma_1(E)=\{1\}$. The complementary child has $2u$ phases labelled $A$ and $k-1-2u$ labelled $B$, both positive even numbers, so its one-dimensional spectrum is $\{0\}$. Theorem 48.1 gives preset fee three and rules out every two-block common stream, including attempted rejection and early stopping.

The root rejects exactly positive INITIAL tails, returning their original $R$ at fee one. At paid index one, the isolated pulse at position one in the second word has actual mask $\{0,1\}$ because $u_1=k\equiv-1\pmod T$. It separates the two endpoint phases, and also identifies phase one as $A$ on the complementary child. These archives may stop at fee two. At index two, the pulses at positions $3,5,\ldots,2u+1$ in the third word give the disjoint pairs $\{1,2\},\{3,4\},\ldots,\{2u-1,2u\}$, hence mask $\{1,\ldots,2u\}$. On the remaining complementary archive this separates the remaining $A$ phases from every $B$ phase. Both suffix words begin zero and have isolated ones; all seams are safe. Their lengths are exactly $k$, and all zeros are paid within those blocks. This proves literal attainment with worst fee three.

For adaptive control, [CR46, Theorems 3.2 and 4.1] already give one additional block on each of these actual two-label children, from this same parent's tail zero. They give total fee two. The unique root leaves each child unresolved, so fee one is impossible. This is a comparison with the existing adaptive law, not a new arbitrary adaptive solver. The independent high and bottom labels, including their allowed coincidences, do not change either lower bound. ∎

**定理 49.2（Sharp odd-critical finite ceiling and an unbounded surcharge family）。** For every odd $k=m\ge3$, let

$$
b=k-1,\qquad h=\lceil\log_2 b\rceil,\qquad
H(k)=1+h+\mathbf1_{\{b\text{ a power of two and }b\ge4\}}.
\tag{49.4}
$$

Across arbitrary label sets and all full INITIAL targets with finite GLOBAL preset fee, the exact supremum of that fee is $H(k)$. It is attained by assigning a different label $y_j$ to each phase at INITIAL tail zero, the same on both free-value fibres, and one arbitrary common label $R$ to every positive INITIAL tail. Initial bottom retains any independent label. On this complete target,

$$
C_{\rm pre}(f)=H(k),\qquad C_{\rm ad}(f)=1+h,
\tag{49.5}
$$

where the adaptive value is the supplied [CR46, Theorem 4.1]. In particular $k=m=2^h+1$, $h\ge2$, has exact adaptive fee $h+1$ and exact preset fee $h+2$.

Proof. For any finite nonconstant target select one eligible cut. If $a>0$, the actual critical mask $E=\{0,a\}$ is permitted; if $a=0$, choose $E=\{1,2\}$. Thus one can always use an actual two-phase parent child and a complementary child of $b=k-1$ phases. Evaluate their spectra at dimension $h$, even if their actual label counts require fewer coordinates. A nonempty two-phase child always admits a nonzero aggregate at this dimension, whether its labels agree or differ.

If $k=3$, both children have two phases and their one-dimensional spectra meet at one. If $k>3$ and $b<2^h$, the larger child is unsaturated; (47.5) says that it admits every nonzero aggregate, even in its singleton exceptions. It can therefore match the two-phase child at length $h$. If $b=2^h\ge4$, length $h+1$ always matches by Theorem 47.2. This proves $C_{\rm pre}(f)\le H(k)$ for every finite target. Constant targets have fee zero and also obey this bound.

For the stated target, $\Lambda$ is injective, and at least one $y_j$ differs from $R$. As in Theorem 49.1, its only eligible cut is $a=k-1$, with unique parent mask $\{0,k-1\}$. Its two children have two and $b$ distinct singleton labels. Binary capacity forces at least $h$ further coordinates. At $k=3$ both aggregate spectra are nonzero-only at dimension one, so that length is possible. At $h\ge2$ the two-phase child is nonzero-only. When $b=2^h$, the complementary singleton child fills the whole cube and is zero-only; this forces the additional coordinate. When $b<2^h$, it admits a nonzero aggregate and there is no surcharge. Theorem 48.1 therefore gives exactly $H(k)$.

Here is an explicit code construction for one attaining literal stream. Let $d=H(k)-1$ and list the $b$ complementary phases in their ordinary increasing order. If $b=2^h\ge4$, assign them all vectors of an $h$-dimensional subspace of $\mathbb F_2^{h+1}$, replacing its zero vector by one vector $w$ outside that subspace. Their aggregate is the nonzero $w$. Otherwise choose $b$ distinct vectors in $\mathbb F_2^h$ with nonzero aggregate $w$. Such a subset exists for $b<2^h$: if a chosen subset has zero aggregate, exchange one of its vectors with an unused vector. For the remaining case $b=2,h=1$, use the entire one-dimensional cube, whose aggregate is one. Give the two endpoint phases the codes $0,w$. All labels are separated within their actual parent children, and the combined full-phase aggregate is zero. Apply the common coordinate normalization (47.8) at each actual paid index, then the literal inverse (47.9). Together with the unchanged root $1^{k-1}0$, these are exactly $H(k)$ safe complete blocks. The lower bound ensures that some source actually requires that worst fee; archives identified earlier can stop.

Finally, the existing critical adaptive law [CR46, Theorem 4.1] applies to the same unique parent and its actual terminal tail, with independently optimized children of two and $b$ distinct labels. It gives $1+h$. Its fresh-label special case is already [CR46, Theorem 6.1]; the use of Theorem 4.1 also permits $R=y_j$. This comparison changes neither the adaptive benchmark's source nor the preset controller's one-stream requirement. ∎

## 50. Remaining original quantifiers and consumed supplier boundaries

**定义 50.1（The residual complete-block cost problem）。** The original problem is still the exact minimum worst-branch number of ACTUAL EMITTED COMPLETE BLOCKS for every arbitrary attainable immutable INITIAL target at all $k\ge2,m\ge1$, separately adaptive and one-global-stream preset, under both original alphabets and the entire actual joint-history prior. The fixed matched reader, free initial value or independent absorbing rejection, endpoint-only observations, original label coincidences, stopping rules and payment for every wait, padding and repair block are unchanged.

Theorem 48.1 resolves the arbitrary-target GLOBAL preset part on every strictly wide width $m>k$ and every odd critical width $m=k\ge3$. Within that statement the room-qualified and $m\ge2k+1$ costs of Theorem 38.1 and Corollary 38.2 are credited existing numerical slices. The singleton-phase width $m=k+1$ is also credited reuse: Corollary 24.3 already bounds an eligible nonconstant target by one block, and the positive-fee necessity gives its exact fee one. The new first-parent minimum retains all insufficient-room roots, and Theorem 47.2 evaluates their genuinely shared continuation. The root images of [S10, Interface 2.1] and [CR46, Theorem 2.2], the zero-prefix wide rows of [S26, proof of Theorem 3.1], common-cut eligibility and value joining are used only with their stated source and literal-operation hypotheses. The classical finite-vector subset spectrum [S27, Corollary 18] is consumed inside the aggregate proof, as in Mathematical citation 37.2.

The odd-critical literal normalization uses even $T$. At even critical $k$, $T$ is odd and whole-phase complementation changes row parity, so (47.8) is not that missing literal bridge. At coprime proper-narrow widths a whole-phase complement generally creates charge outside the physical window. Those arbitrary preset scopes, including even-order width two and general coprime proper-narrow widths not already supplied, remain unresolved by (48.1). Arbitrary INITIAL adaptive costs outside existing supplier laws also remain part of the original problem. The comparisons (49.2) and (49.5) retain their stated full-source families and use the existing critical adaptive theorem; they assert no universal adaptive-to-preset equality.

The arbitrary unit-width laws of Theorems 25.3–25.4, the noncoprime proper-narrow preset law of Theorem 33.2 and the odd-order width-two preset law of Theorem 44.2 remain credited with their original scopes. An acquired-support fee is additional to its actual acquisition, and no source representation or calibration result supplies a reader fee without a proved source, operation, observation and resource correspondence. Formula (48.1) is a finite set-theoretic minimum for arbitrary $Y$; effective evaluation may use the finite target partition or a finite table with decidable label equality. It asserts no bound on offline search or memory.

[CR46]: https://raw.githubusercontent.com/the-omega-institute/trureturing/0e51d0ec80c86e888fcdde78982665a7c5c17c79/docs/develop/theory/KBONACCI_CRITICAL_WIDTH_TARGET_COST.md

## 追加锚（本行以下为增补区）
## 51. Paid prefix information and a coprime finite horizon

**定义 51.1（Full INITIAL tables on the proper-narrow coprime calendar）。** Fix the original reader and costs of Definitions 1.1–1.3, with

$$
2\le m<k,\qquad T=k+1,\qquad \gcd(m,T)=1,\qquad
P=\mathbb Z/T\mathbb Z,\qquad D=\left\lfloor\frac{k-1}{m}\right\rfloor.
\tag{51.1}
$$

Every INITIAL record $(v,-j,s)$, with $v\in\mathbb F_2$, $j\in P$ and $0\le s<k$, is represented by the single complete-block history (1.3). Coprimality makes its two length congruences compatible at every $j$. Its adjusted first bit, separating zero and terminal run jointly realize the specified value, phase and tail. The unknown length is not observed. Initial $\bot$ has its own arbitrary label and stops at its free reading. Since $m<k$, both original alphabets contain every $m$-bit word; rejection across a seam remains part of the original operation.

For arbitrary $f:Q\to Y$ use the ordered value join of Theorem 29.2 in INITIAL coordinates:

$$
\Gamma(j,s)=\bigl(f(0,-j,s),f(1,-j,s)\bigr),\qquad
\Lambda(j)=\Gamma(j,0).
\tag{51.2}
$$

Equality of ordered pairs requires equality in both components, without requiring the components to equal one another. Put

$$
I_t(j)=\mathbf1_{\{tm,(t+1)m\}\bmod T}(j),\qquad
S_t(\beta)=\{j:(I_0(j),\ldots,I_{t-1}(j))=\beta\},\qquad h_t=k-tm.
\tag{51.3}
$$

For $0\le a<k$ write $a=qm+r$, $0\le r<m$. Call $a$ eligible when the supplied common-cut conditions of Theorem 24.2 hold on the value join. Explicitly, for every indicated response string,

$$
\begin{aligned}
&\operatorname{Const}\{\Gamma(j,s):j\in S_t(\beta),\ h_t-m\le s<h_t\}
&& (0\le t<q),\\
&\operatorname{Const}\{\Gamma(j,s):j\in S_q(\beta),\ h_q-r\le s<h_q\},\\
&\Gamma(j,s)=\Lambda(j)
&& (j\in P,\ 0\le s<k-a).
\end{aligned}
\tag{51.4}
$$

Empty sets impose no condition. The common integer $a$ precedes all value and archive quantifiers. Theorems 24.2 and 29.2 supply eligibility and the exact preset value join, including infinity; they are used inside the paid constructions below. The single-source complete-observation experiment is the one in [S1, Definitions 1.2 and 2.1], consistent with Moore's simple experiments (*Gedanken-Experiments on Sequential Machines*, pp.129–131). Only actual complete endpoints and each source's own chronological archive enter the decoder.

**定理 51.2（Retaining the paid all-one chords）。** In (51.1), every eligible $a=qm+r$ admits a full-INITIAL preset protocol of worst actual fee at most $T$. More precisely, after $q$ all-one blocks one may retain any length-$m$ parent $B$ whose first zero follows exactly $r$ ones, and then issue

$$
E=01\,0^{m-2}
\quad\text{at every absolute block index }q+1,\ldots,T-1.
\tag{51.5}
$$

Every block in this schedule is paid when reached, including the parent. Consequently

$$
C_{\rm pre}(f)<\infty\quad\Longrightarrow\quad C_{\rm pre}(f)\le k+1.
\tag{51.6}
$$

The sufficient per-cut bound $q+T$ from Corollary 24.3 is replaced by $T$, and its uniform bound $D+T$ by $T$. These are comparisons of sufficient bounds, without an optimality or sharpness assertion for either construction.

**证明。** Interface 1.4 makes each successfully completed all-one block at index $t<q$ the actual charge edge

$$
H_t=\{tm,(t+1)m\}\pmod T,
\tag{51.7}
$$

and each successfully completed $E$ at index $t$ the actual edge

$$
F_t=\{tm+1,tm+2\}\pmod T.
\tag{51.8}
$$

The $T$ edges $F_0,\ldots,F_{T-1}$ are exactly the adjacent edges of the physical $T$-cycle, because multiplication by $m$ permutes the residues. Retain $H_0,\ldots,H_{q-1}$ and $F_{q+1},\ldots,F_{T-1}$, ignoring the paid parent's response for this separation argument. There are $T-1$ retained coordinates.

Since $qm\le T-2$, deleting $F_0,\ldots,F_q$ leaves the following $q+1$ path components of that cycle:

$$
\begin{aligned}
C_t&=\{tm+2,\ldots,(t+1)m+1\} &&(0\le t<q),\\
C_q&=\{qm+2,\ldots,T-1\}\cup\{0,1\}.
\end{aligned}
\tag{51.9}
$$

The first interval in $C_q$ is empty when $qm+2=T$. For $q=0$ this is just one spanning path. For $q>0$, $C_t$ has $m\ge2$ vertices when $t<q$, and $C_q$ has $T-qm\ge2$ vertices. Chord $H_0$ joins $C_q$ to $C_0$: zero lies in $C_q$, while $m$ lies in $C_0$. For $1\le t<q$, $tm$ lies in $C_{t-1}$ and $(t+1)m$ lies in $C_t$. Thus the $q$ already acquired chords join the components in one chain. None is an additional operation. The retained graph is connected and has $T-1$ edges, hence is a spanning tree.

Its incidence column at phase $j$ is exactly the list of that source's retained endpoint differences. These columns are distinct. Indeed, a zero column would be an isolated vertex. If distinct vertices had the same nonzero column, every edge incident to either would have to contain both, so they would constitute a component on just two vertices. Neither is possible in this connected tree on $T\ge5$ vertices. Adding the actual parent coordinate preserves separation.

It remains to realize these coordinates on the full INITIAL prior. An INITIAL tail $s<k-a$ survives all $a$ leading ones, since $s+a<k$, and reaches the parent's first zero. The remaining part of that parent has fewer than $m<k$ bits, so no later internal run rejects it. All these survivors have the same actual terminal tail of $B$, at most $m-r-1$. Every subsequent $E$ starts zero and contains only one one. It therefore safely clears that tail. When $m=2$, $E=01$ ends at tail one, and the next $E$ again starts zero. No final clearing block is required for stopping at a successful endpoint.

Each earlier rejection uses its own preceding successful archive $S_t(\beta)$ and the corresponding homogeneous band in (51.4). Parent rejection uses its own $S_q(\beta)$ and its homogeneous band. Neither supplies a binary parent charge. Those sources stop with the prescribed INITIAL pair label, and the remembered free value selects its component. A survivor retains its own earlier $q$ differences, takes its own actual parent endpoint as the baseline for the later differences, and decodes $j$ from the tree column. Its immutable label is $\Lambda(j)$ by (51.4). No other value fibre or stopped sibling is run or consulted; Theorem 29.2 is only the decoder symmetry of this one stream.

The number of issued blocks on a survivor kept to the last endpoint is

$$
q+1+(T-q-1)=T.
\tag{51.10}
$$

Such actual tail-zero sources exist at every phase by (1.3). Earlier homogeneous archives may stop sooner. Every reached word, including its zero padding, costs one. Thus the construction gives the claimed upper bound on all values, phases and tails. For a finite preset target, Theorem 24.2 supplies an eligible cut; independent initial rejection has already stopped for free. This proves (51.6). ∎

**定理 51.3（A block-boundary sharpening and every even-order width-two cut）。** In (51.1), if some eligible cut is $a=qm$, then $C_{\rm pre}(f)\le T-1=k$. For $m=2$ and every even $k=2p\ge4$, every eligible cut admits this bound, including cuts inside a block. Hence

$$
m=2,\ k\text{ even},\ C_{\rm pre}(f)<\infty
\quad\Longrightarrow\quad C_{\rm pre}(f)\le k.
\tag{51.11}
$$

At a boundary cut the sufficient $q+T$ bound is replaced by $T-1$, saving $q+1$ counted blocks. At even width two the supplied uniform $D+T=3p$ bound is replaced by $2p$. No sharp finite ceiling or individual minimum is asserted by these comparisons.

**证明。** At a boundary cut use $q$ blocks $1^m$ and then

$$
L=0^{m-1}1\quad\text{at indices }q,\ldots,T-2.
\tag{51.12}
$$

The first $L$ is the parent with leading run zero. Every subsequent $L$ starts zero, so every low INITIAL survivor safely reaches every endpoint; the terminal tail one is cleared by the next block. Earlier rejection bands are decoded as in Theorem 51.2.

The actual charge of $L$ at index $t$ is $\{(t+1)m-1,(t+1)m\}\pmod T$. The complete cycle of these edges is again the physical adjacent cycle. In (51.12) its deleted edges have right endpoints $0,m,\ldots,qm$. Since $qm\le T-2$, the resulting components, in ordinary representatives, are

$$
\{0,\ldots,m-1\},\ \{m,\ldots,2m-1\},\ldots,
\{(q-1)m,\ldots,qm-1\},\ \{qm,\ldots,T-1\}.
\tag{51.13}
$$

At $q=0$ only the last component occurs. The already paid chords (51.7) connect consecutive components. Thus the actual $q+(T-1-q)=T-1$ rows form a spanning tree and identify every INITIAL phase, by the incidence argument in Theorem 51.2.

Now let $m=2$, $k=2p$ and $T=2p+1$. An eligible cut is $a=2q+r$, $0\le q\le p-1$, $r\in\{0,1\}$. The case $r=0$ is (51.12). For $r=1$ use

$$
(11)^q\mid(10)^{T-1-q}.
\tag{51.14}
$$

Its first $10$ has exactly the required leading one, and every later $10$ starts from tail zero and ends at tail zero. All low survivors reach its first parent zero since $s+2q+1<k$. All later seams have a one-run of length one. The actual $10$ edges are $\{2t,2t+1\}\pmod T$, $q\le t\le T-2$.

For $q=0$ these are a spanning path, omitting just the cycle edge with left endpoint $2p-1$. For $q\ge1$ the omitted left endpoints are $0,2,\ldots,2q-2$ and $2p-1$. The components of the retained adjacent edges are

$$
\{2p,0\},\ \{1,2\},\ \{3,4\},\ldots,
\{2q-3,2q-2\},\ \{2q-1,\ldots,2p-1\}.
\tag{51.15}
$$

There are $q+1$ components; when $q=1$ the intermediate two-element sets are absent. The $q$ all-one chords $\{2t,2t+2\}$ connect them consecutively into a spanning tree. Its columns identify every phase. This uses the literal $10$ parent and its actual endpoint, rather than an abstract independent row. The same original rejection decoding and ordered value join finish the target at worst depth $T-1$. Both alphabets admit every displayed word. ∎

**定理 51.4（The separate adaptive finite horizon）。** Under (51.1), independently of preset finiteness,

$$
C_{\rm ad}(f)<\infty\quad\Longrightarrow\quad C_{\rm ad}(f)\le T.
\tag{51.16}
$$

For $m=2$ and even $k\ge4$, the right side can be replaced by $T-1=k$. These implications do not assert that finite adaptive cost implies finite preset cost.

**证明。** Apply [S1, Definition 5.1 and Theorem 5.2] to each free INITIAL value separately. Its full jointly attainable prior is supplied by (1.3); its target is the immutable record target $f$, its observations are complete endpoints, and its independent INITIAL bottom stops freely. Both original alphabets contain every $m$-bit word because $m<k$. Thus finite adaptive attainability supplies the source's finite recursive first-zero witness tree. No preset finiteness or ordered value join is assumed.

At a nonempty successful node before the first zero, let $q$ be the number of actually issued all-one blocks. Write $z_0=v,z_1,\ldots,z_q$ for this branch's own endpoint values and $\beta_t=z_{t+1}\oplus z_t$. By [S1, Lemma 4.2], the INITIAL candidates and their respective current records are exactly

$$
\begin{gathered}
\{(v,-j,s):j\in S_q(\beta),\ 0\le s<h_q\},\qquad h_q=k-qm>0,\\
(z_q,-j+qm,s+qm),\qquad
z_q=v\oplus\bigoplus_{t<q}\beta_t.
\end{gathered}
\tag{51.17}
$$

Every candidate has a whole actual history realization; the common current value is an observed value, and $q$ counts emitted blocks rather than an INITIAL clock. A homogeneous candidate set can stop at this node. Otherwise the witness tree either chooses another all-one block, with $h_q>m$ and a homogeneous INITIAL rejection band $h_q-m\le s<h_q$, or chooses a first-zero witness $0\le r<\min(m,h_q)$. In the recursive case the next observed difference selects the actual child support, and rejection stops with that node's common band label. In the first-zero case $C_v(q,-S_q(\beta),r)$, written in the $j=-\theta$ coordinates, says precisely

$$
\begin{aligned}
&\operatorname{Const}\{f(v,-j,s):j\in S_q(\beta),\ h_q-r\le s<h_q\},\\
&f(v,-j,s)=f(v,-j,0)
\qquad(j\in S_q(\beta),\ 0\le s<h_q-r).
\end{aligned}
\tag{51.18}
$$

The rejection set is empty when $r=0$. Each recursive step decreases $h_q$ by $m$, so $q\le D$ and $qm\le k-1=T-2$. The cumulative leading run $a=qm+r$ is strictly less than $k$. All these statements concern one actually acquired archive and its INITIAL candidates.

First construct the $T$ bound. Retain the witness parent $B_r=1^r0^{m-r}$ at index $q$. It rejects exactly the band in (51.18). Every other candidate has $s+qm+r<k$, reaches its first zero, and finishes at the actual record

$$
\left(z_q\oplus\bigoplus_{i=0}^{r-1}c_{-j+qm+i},\ -j+(q+1)m,\ 0\right).
\tag{51.19}
$$

The empty sum is zero. The rejection endpoint is decoded using this branch's band label. A successful endpoint has its own observed value as the new baseline. Now issue $E$ from (51.5) at indices $q+1,\ldots,T-1$. Every such word starts zero and has one isolated one, so the first is safe from the actual parent tail zero and each later seam is safe, including $m=2$, where the preceding $E$ has tail one. There is no further rejection on a surviving source.

The decoder uses the already acquired differences $\beta_0,\ldots,\beta_{q-1}$ and its own successive differences after the parent. For INITIAL phase $j$ these coordinates are exactly the incidence column of the retained $H_t$ and $F_t$ edges in the spanning tree (51.7)–(51.9). The parent's difference is not needed by this decoder, although its block is paid and its endpoint baseline is observed. That tree separates the whole $P$ for every permitted $q$, without a target eligibility hypothesis; restricting its columns to $S_q(\beta)$ preserves separation. The decoder therefore determines $j$ and returns $f(v,-j,0)$, which is the immutable label of every surviving INITIAL tail by (51.18). It never requests any coordinate from another archive. A surviving path emits $q$ prefix blocks, one parent and $T-q-1$ suffix blocks, for total $T$. Earlier homogeneous and rejection leaves stop at their actual completed endpoints. This proves (51.16).

For the sharper bound let $m=2$, $k=2p\ge4$, so $T=2p+1$, $q\le p-1$ and $r\in\{0,1\}$. Retain the same recursive all-one choices and their homogeneous rejection leaves up to the local first-zero node. At that node choose the following literal parent and continuation using its actual $r$.

If $r=0$, use $01$ as an alternative parent at index $q$, followed by $01$ at every index $q+1,\ldots,T-2$. The source's witness parent for $r=0$ is $00$, whose difference is zero and whose terminal tail is zero. The alternative $01$ first clears every candidate's current tail $s+2q<k$, then issues one safe bit. It rejects no candidate and has the actual endpoint record

$$
\left(z_q\oplus\mathbf1_{\{2q+1,2q+2\}\bmod T}(j),\ -j+2q+2,\ 1\right).
\tag{51.20}
$$

Indeed its difference is $c_{-j+2q+1}$. Thus the endpoint response and tail are those of $01$ itself. Condition (51.18) with $r=0$ makes $f$ constant on every fixed-phase INITIAL tail fibre $0\le s<h_q$, so the new parent's tail merge loses no required label distinction. Every subsequent $01$ starts zero, clears the actual tail one, and again ends with one isolated one; all its endpoints are safe. A surviving source can stop at the final tail-one endpoint without a clearing block.

For this new continuation the decoder retains its own prefix differences and observes the alternative parent's difference as well as every subsequent difference. These are exactly the edges

$$
H_t=\{2t,2t+2\}\pmod T\quad(0\le t<q),\qquad
L_t=\{2t+1,2t+2\}\pmod T\quad(q\le t\le T-2).
\tag{51.21}
$$

The $L_t$ form the physical adjacent cycle with the edges whose right endpoints are $0,2,\ldots,2q$ deleted. Its components are $\{0,1\},\{2,3\},\ldots,\{2q-2,2q-1\},\{2q,\ldots,2p\}$; for $q=0$ there is just the last component, the whole $P$. The already paid $H_t$ join consecutive components. Hence these actual $T-1$ rows form the spanning tree of (51.13), specialized to width two. Its distinct incidence columns identify every $j$, also after restriction to this branch's support. The decoder computes them from $z_q$ and the actual new parent endpoint; it then returns $f(v,-j,0)$ using (51.18). This continuation is defined from the new observations themselves, without identifying the $00$ and $01$ endpoint archives.

If $r=1$, use the source's witness parent $10$ at index $q$, followed by $10$ at every index $q+1,\ldots,T-2$. The parent rejects exactly $s=h_q-1$, with the common band label in (51.18). Each survivor satisfies $s+2q+1<k$, so its first bit is safe and the second bit clears its tail. Its actual endpoint record is

$$
\left(z_q\oplus\mathbf1_{\{2q,2q+1\}\bmod T}(j),\ -j+2q+2,\ 0\right).
\tag{51.22}
$$

Every later $10$ starts from tail zero and ends at tail zero. Its one-run has length one, so every reached suffix block is safe. The branch's own prefix differences and its actual parent and suffix differences are the $H_t$ and $\{2t,2t+1\}$ columns of (51.14)–(51.15). For $q=0$ the latter edges form a spanning path. For $q\ge1$ their components are those in (51.15), and the $H_t$ connect them consecutively. Again the result is a spanning tree on all $P$, with $T-1$ edges and distinct phase columns. Restricting to $S_q(\beta)$, the actual observed column determines $j$, and (51.18) supplies the survivor's INITIAL label $f(v,-j,0)$. Parent rejection uses only this branch's preceding archive and its homogeneous rejection band.

In either case there are exactly $T-1-q$ displayed blocks at indices $q,\ldots,T-2$, including the parent. Together with the $q$ actually emitted prefix blocks, every surviving path pays at most $T-1=k$. Each prior rejection or homogeneous leaf pays only its own reached blocks. The words $11$, $01$ and $10$ are available in both original alphabets, and every seam and terminal tail used above is literal. The finite witness tree selects cuts separately for different acquired archives and free values; after a selected parent, only that source's endpoints enter its decoder. Initial bottom retains its independent free label. No global eligible cut, sibling observation, free clearing action or implication to finite preset attainability is used. This proves the separate adaptive sharpening. ∎

## 52. The complete even-order width-two preset structural minimum

**定义 52.1（Joined INITIAL rejection rectangles and the no-zero option）。** Fix

$$
m=2,\qquad k=2p\ge4,\qquad T=2p+1,
\tag{52.1}
$$

and every arbitrary target $f:Q\to Y$ on the full prior of Definition 51.1. Use $\Gamma,\Lambda,I_t,S_t,h_t$ from (51.2)–(51.3), now with $I_t(j)=\mathbf1_{\{2t,2t+2\}\bmod T}(j)$ and $h_t=2p-2t$. All $T$ phases are actual. A common cut $a=2q+r<2p$, $r\in\{0,1\}$, is eligible exactly under (51.4).

Let $\mathcal A$ consist of the integers $0\le d\le p-1$ satisfying

$$
\begin{aligned}
&\operatorname{Const}\{\Gamma(j,s):j\in S_t(\beta),\ h_t-2\le s<h_t\}
&& (t<d,\ \beta\in\mathbb F_2^t),\\
&\operatorname{Const}\{\Gamma(j,s):j\in S_d(\beta),\ 0\le s<h_d\}
&& (\beta\in\mathbb F_2^d).
\end{aligned}
\tag{52.2}
$$

These are the rejection and final successful sets of an actual $d$-block all-one stream. In particular $d=0$ means that the joined target is constant on all successful INITIAL records; the bottom label is independent. This option retains stopping before an unissued zero, rather than charging a nominal parent.

**定义 52.2（Chronological literal graph and its two run exclusions）。** For an eligible cut $a=2q+r$ and an integer $q+1\le d\le k$, choose one sequence of actual two-bit words $B_0,\ldots,B_{d-1}$. Require

$$
B_t=11\ (t<q),\qquad
B_q\in\begin{cases}\{00,01\},&r=0,\\\{10\},&r=1.\end{cases}
\tag{52.3}
$$

At chronological index $t$ put $u_t=2t\pmod T$. The word's actual successful charge, from (1.4), gives the following graph row:

$$
\begin{array}{c|c}
B_t&\text{edge at index }t\\ \hline
00&\varnothing\\
10&\{u_t,u_t+1\}\\
01&\{u_t+1,u_t+2\}\\
11&\{u_t,u_t+2\}.
\end{array}
\tag{52.4}
$$

Let $G$ be the multigraph on all $P$ with one separately time-indexed edge for every nonempty row. Parallel edges retain their distinct chronological coordinates. An empty row retains its block index and its fee when reached. Require $\Lambda$ to be constant on the entire isolated-vertex set, and on the two vertices of each component of size two. Components of size at least three impose no further label condition.

Finally require the contiguous block suffix $B_q,\ldots,B_{d-1}$ to contain neither

$$
(11)^p,\qquad 01\mid(11)^{p-1}\mid10.
\tag{52.5}
$$

The parent $01$, if selected, is included as a possible start of the second pattern. The intentional INITIAL rejection threshold before its first zero is governed by eligibility, not by (52.5). Let $\mathcal Z$ be the set of depths $d$ admitted by these conditions over all eligible cuts and all their allowed parents. No phase column is padded separately after a stopping time; $G$ always comes from one whole written stream.

**定理 52.3（Full-INITIAL graphical minimum with a legal $k$ horizon）。** For every full target in (52.1), under either original alphabet,

$$
C_{\rm pre}(f)=\min(\mathcal A\cup\mathcal Z),\qquad \min\varnothing=+\infty.
\tag{52.6}
$$

This includes fee zero, preset infinity, arbitrary label coincidences, both value fibres, all INITIAL tails and independent bottom. It is an exact finite structural minimum, with chronological graph collisions and literal seams evaluated together. It is not a numerical closed formula for each arbitrary table or a sharpness assertion for the $k$ horizon.

**证明。** First identify the reader-specific column collisions. Each of the three physical vertices in (52.4) is actual and distinct, and the full even charge has the unique literal inverse $xy$ with charges $(x,x\oplus y,y)$. Thus the successful difference column at phase $j$ is exactly its edge-incidence column in $G$. The zero column consists of all isolated vertices. If two distinct vertices have the same nonzero column, every edge incident to either must contain both; their component has precisely those two vertices, possibly joined by several separately indexed edges. Conversely such a component gives equal columns to its endpoints. Every vertex in a component of size at least three therefore has a column distinct from every other vertex, including vertices in other components. It follows that full columns separate unequal $\Lambda$ labels exactly under the graph condition of Definition 52.2. Equal labels may have different columns.

Next identify all literal suffix failures. The zero-containing words $00,01,10$ have respectively leading/terminal one-runs $(0,0),(0,1),(1,0)$. Between successive zero-containing words, let $\ell$ intervening blocks be $11$. The run crossing them has length

$$
\rho_{\rm left}+2\ell+\alpha_{\rm right},\qquad
\rho_{\rm left},\alpha_{\rm right}\in\{0,1\}.
\tag{52.7}
$$

For a terminal stretch omit $\alpha_{\rm right}$. If $\ell\ge p$, the first pattern of (52.5) occurs and gives rejection. If $\ell\le p-2$, the run is at most $2p-2<k$. At $\ell=p-1$ it reaches $k$ precisely when both boundary contributions are one, namely when the left word is $01$ and the right word $10$. A terminal stretch with $\ell=p-1$ has length at most $2p-1$ and is safe. These cases also apply after the parent's actual first zero: its terminal tail is zero for $00,10$ and one for $01$. They exhaust all post-zero runs, and prove that (52.5) is exactly suffix safety. There is no block-internal observation in this argument. In particular, physical row parity alone does not replace either run exclusion.

For an actual obstruction to omitting the second exclusion, take $k=4,m=2$ and the full target $f(v,-j,s)=j$, with independent bottom label. The written stream $01\mid11\mid10$ has graph edges $\{1,2\},\{2,4\},\{4,0\}$, a four-vertex component and one isolated vertex, so all its formal incidence columns are distinct. Its actual INITIAL-tail-zero sources at $j=0$ and $j=3$ have the same two acquired differences $(0,0)$ and unequal labels. They cannot stop there. After $01\mid11$ their common tail is three; the first bit of $10$ reaches four and both acquire bottom at the next complete endpoint. The last formal graph row is therefore not a binary observation on these sources. Their whole histories are (1.3), and this failure is precisely $01\mid(11)^{p-1}\mid10$ at $p=2$.

For $d\in\mathcal A$, issue exactly $d$ words $11$. At every rejected endpoint return the constant label of its band in (52.2), from that source's preceding archive. At the last successful endpoint return the constant surviving rectangle label. Remember the free initial value to select its component, and stop initial bottom freely. This constructs a correct controller with worst fee at most $d$ and without any zero parent.

For $d\in\mathcal Z$, issue exactly its one specified stream. Its earlier and parent rejection rectangles are homogeneous by (51.4), so each rejected source decodes its INITIAL label from its own archive. All low sources $s<k-a$ survive the same parent zero and acquire its common terminal tail. Their immutable pair label is $\Lambda(j)$. Equation (52.7) proves that every later block is actually successful on all of them. Each survivor can therefore acquire the full incidence column and decode $\Lambda(j)$ under the graph condition. Its free initial value returns the corresponding component. Earlier homogeneous archives may stop sooner. Every empty row, wait or padded word still reached is one emitted complete block and is charged. This proves the sufficient direction of (52.6).

For necessity take a finite correct preset controller with worst fee $H$ and apply Theorem 29.2 to its same stream. Stop any joined-homogeneous archive immediately. If no running source reaches a zero, or a written first zero would follow at least $k$ ones, every remaining successful archive in the block crossing the $k$th one would be sent wholly to absorption. No later observation could distinguish its candidates. Correctness forces it already to be homogeneous before that block, so omit that block and its unused suffix. The maximal actual all-one depth is some $d\le\min(H,p-1)$. Raw rejected bands and final surviving rectangles are homogeneous: a raw subgroup of an earlier stopping leaf is a subset of its homogeneous candidate set. These are set calculations about INITIAL sources, without executing a stopped history. Hence $d\in\mathcal A$.

Otherwise the actually reached first zero follows $a=2q+r<k$ leading ones. Its own parent is exactly one of (52.3). The common-cut necessity proof of Theorem 24.2 supplies all (51.4), including raw subsets of earlier stopped leaves. Consider actual INITIAL-tail-zero representatives (1.3) at every phase on a fixed free-value fibre. They can all traverse the raw prefix and parent; all raw survivors then have the same tail. If a later written block would be the first common raw rejection, it sends every still-running successful archive wholly to bottom. Each such archive is already label-homogeneous by correctness. Stop it before that block and truncate the now unused rejecting suffix. If all actual sources stopped still earlier, truncate at their latest stopping endpoint. The retained written suffix is safe on every raw low-tail representative, including phases whose actual execution stopped earlier. Their later entries are design evaluations only; no actual output from a stopped source is acquired or borrowed.

Let its retained depth be $d$. It is at least $q+1$, since a running source reached that parent, and at most $H$. All original positive-tail sources either rejected by the parent or have the same raw post-parent tail as the low representatives. Thus this truncation omits no unresolved source. If two phases of unequal $\Lambda$ had the same full retained column, their actual low-tail sources would have the same successful endpoint archive through the earlier stopping time. A deterministic decoder would stop both there with the same pair label, a contradiction. The incidence calculation gives the graph condition, and actual suffix safety gives (52.5). These are whole rows on all phases, rather than individual zero extensions of stopped columns.

If $d\le k$, this is a member of $\mathcal Z$ no larger than $H$. If $d>k$, its eligible cut admits the lawful phase-identifying $k$-word stream of Theorem 51.3. That stream satisfies (52.3), has strictly safe suffix, and has distinct phase columns, so gives a member of $\mathcal Z$ at depth $k<d\le H$. Every finite correct controller therefore supplies a candidate no greater than its actual bound, while every candidate supplies a controller no greater than its depth. Their least values agree. If the union is empty, a finite controller would contradict necessity, proving infinity. If a minimum candidate's stream has all sources stop sooner, necessity supplies a no-larger candidate at that actual fee; thus no nominal unissued block is used to inflate the minimum.

The response/seam and stopping normalization in [S15, Theorem 3.3 and Proposition 4.2] is consumed at its stated $m\ge3$ scope as a source of the common-tail argument, not applied as a width-two fee theorem. Here the moving three-vertex geometry, the exact incidence collision classification and the two literal exclusions give its full original-source width-two replacement, and Theorem 51.3 supplies its smaller legal horizon. The odd-order width-two subgroup law of Theorem 44.2 has $g=2$ and is not a phase supplier for (52.1). ∎

## 53. An exact maximal-cut family on the original even-order source

**定义 53.1（All positive INITIAL tails and arbitrary two-value phase tables）。** In (52.1), choose arbitrary $R_0,R_1\in Y$ and arbitrary tables $\lambda_v:P\to Y$, $v\in\mathbb F_2$. With arbitrary coincidences, define the complete INITIAL target by

$$
f(v,-j,s)=
\begin{cases}
\lambda_v(j),&s=0,\\
R_v,&1\le s<k.
\end{cases}
\tag{53.1}
$$

Give initial bottom any independent label. There is no freshness, injectivity or value-independence hypothesis. Write

$$
\rho_0=2p,\qquad \rho_i=2i-1\ (1\le i<p),\qquad
b_v(i)=\lambda_v(\rho_i),\qquad b(i)=(b_0(i),b_1(i)).
\tag{53.2}
$$

For a table $c$ on $\{0,\ldots,p-1\}$ use the following expression inside this family's fee:

$$
\psi(c)=
\begin{cases}
0,&c\text{ is constant},\\
1,&c\text{ is nonconstant, }c|_{\{2,\ldots,p-1\}}\text{ is constant, and }|c[\{0,\ldots,p-1\}]|\le2,\\
\max\{2,B(c)\},&\text{otherwise},
\end{cases}
\tag{53.3}
$$

In the last case $B(c)=\max\{i:0\le i<p-1,\ c(i)\ne c(i+1)\}$. A nonconstant table has such a boundary. Constancy of the empty outside set is vacuous. The constant, one-block and path-column mechanism of Theorem 43.2 is consumed only after the actual even-order parent and suffix correspondence below; its odd-order source and acquired fee are not identified with the present INITIAL problem.

**定理 53.2（Closed adaptive and preset fees with the maximal cut paid）。** For the entire family (53.1), under either original alphabet, put

$$
F_v=
\begin{cases}
0,&\lambda_v(j)=R_v\text{ for all }j,\\
p+\psi(b_v),&\text{otherwise}.
\end{cases}
\tag{53.4}
$$

Then

$$
\begin{aligned}
C_{\rm ad}(f)&=\max\{F_0,F_1\},\\
C_{\rm pre}(f)&=
\begin{cases}
0,&(\lambda_0(j),\lambda_1(j))=(R_0,R_1)\text{ for all }j,\\
p+\psi(b),&\text{otherwise}.
\end{cases}
\end{aligned}
\tag{53.5}
$$

The parent fee $p$ is part of the original worst emitted fee, and all positive INITIAL tails are included. The equalities are restricted to (53.1), rather than asserted for arbitrary INITIAL tail partitions. With a common injective tail-zero table $\lambda_0=\lambda_1$, and arbitrary $R_0,R_1$, both exact fees are three at $k=4$, five at $k=6$, and $k-2$ at every even $k\ge8$.

**证明。** First fix one free value $v$ with $\lambda_v(j)\ne R_v$ at some phase $j$. Its two actual histories (1.3) with INITIAL tails zero and one have unequal labels and identical successful values for every common literal input before the first zero. A zero before $k-1$ emitted ones lets both survive and merges their current records. If no zero intervenes between the $(k-1)$st and $k$th ones, both reject in the same final two-bit block, and the one endpoint is bottom for both. No later observation separates either merged pair. They cannot stop while their archives agree. Every correct path carrying this pair must therefore have its first zero precisely after $k-1=2p-1$ ones, namely the literal prefix

$$
(11)^{p-1}\mid10.
\tag{53.6}
$$

It pays $p$ complete blocks. This is an all-action lower bound on that actual adaptive path. For a nonconstant joined target the same argument forces (53.6) on the preset stream. Constant fibres need no action and return $R_v$ for free.

Use (53.6) as a preset prefix on any nonconstant fibre, or on the joined table for preset control. Every positive INITIAL tail rejects in one of its $p$ blocks and returns its own $R_v$; the preceding archive is irrelevant to that label. Precisely INITIAL tail zero survives, reaches the final zero and ends at actual tail zero. The successful charge graph of the prefix is the path

$$
0\;--\;2\;--\;4\;--\;\cdots\;--\;(2p-2)\;--\;(2p-1).
\tag{53.7}
$$

It has $p\ge2$ edges and $p+1\ge3$ vertices. The incidence argument in Theorem 52.3 identifies each of these vertices by its distinct nonzero prefix column. Their successful archives are already homogeneous, since only INITIAL tail zero remains. They can actually stop at the parent endpoint with $\lambda_v(j)$. Exactly the $p$ isolated vertices of this graph remain on the all-zero successful archive:

$$
(\rho_0,\ldots,\rho_{p-1})=(2p,1,3,\ldots,2p-3).
\tag{53.8}
$$

They have current value $v$ and current tail zero, after the same paid parent, with their original labels $b_v(i)$.

At the next chronological indices $p+h$, $0\le h\le p-2$, the actual ordered windows are

$$
(\rho_h,\ 2h,\ \rho_{h+1})\pmod T.
\tag{53.9}
$$

For $h=0$ this is $(2p,0,1)$; for $h\ge1$ it is $(2h-1,2h,2h+1)$. The middle even phase belongs to the genuinely identified set (53.7). For a literal word $xy$, its two remaining endpoint charges are exactly $x,y$, and its middle charge is $x\oplus y$, all from the same actual block (1.4). This is the full even physical charge. The middle source has already stopped and provides no further observation. Thus the two-endpoint suffix mechanism in the proof of Theorem 43.2 has a lawful original-source realization here. The next block index is $p$, its ordered residual endpoints are $\rho_0,\rho_1$, and its acquisition has paid depth $p$; this is not a free substitution of an odd-order reader.

For completeness apply that mechanism with these actual indices and tails. A constant residual table stops at the parent. From tail zero every first two-bit word is safe. A nonconstant table can stop after one more block exactly when the untouched indices $i\ge2$, all with response zero, have one label and the entire residual has at most two labels. These are exactly the second line of (53.3). If the outside set is nonempty, choose its label as response-zero baseline and use the two literal bits to mark the other label at $\rho_0,\rho_1$; if it is empty, choose either occurring label. Each response class is homogeneous and this one actual word attains the fee. No more than two ones are emitted after the parent's clearing zero, so its seam is safe.

If the one-block condition fails, at least two further completed endpoints are necessary. For any differing adjacent labels at indices $i,i+1$ with $i\ge1$, their first possibly separating coefficient occurs at absolute bit position $2p+2i-1$, the second bit of suffix block $i-1$. Neither phase has any coefficient activity earlier in the suffix. Until that position their current values and tails are equal, so every actual adaptive archive, action and stopping decision on them is equal. A rejection would be common absorption and cannot identify unequal INITIAL labels. Reaching that position requires at least $i$ further complete blocks. Taking the last differing boundary, together with the failed one-block condition, gives the lower bound $\max\{2,B(c)\}$ for an arbitrary adaptive continuation.

For attainment in this last case put $d=\max\{2,B(c)\}$ and issue exactly $d$ words $11$ after (53.6). The failed one-block condition implies $p\ge3$. If $p=3$, $d=2=p-1$; if $p\ge4$, $d\le p-2$. In either case $d\le p-1$, so (53.9) covers every issued row and

$$
2d\le2p-2<k.
\tag{53.10}
$$

Every suffix endpoint is therefore successful on every residual source, and its final tail needs no clearing action for stopping. The columns on residual indices $0,\ldots,d$ are

$$
e_0,\ e_0+e_1,\ldots,e_{d-2}+e_{d-1},\ e_{d-1},
\tag{53.11}
$$

where $e_h$ denotes the unit vector at suffix coordinate $h$. They are pairwise distinct for $d\ge2$. Every later residual index has the zero column and one common label, because those indices are beyond the last differing boundary. Hence the written stream decodes the full residual table. Equal-label splitting is allowed. This proves the additional $\psi(c)$ fee and its actual literal attainment, within the paid correspondence (53.6)–(53.9).

To add that fee in an adaptive lower bound, a nonconstant $b_v$ has some entry different from $R_v$. Choose that residual phase's actual INITIAL tails zero and one. Before the parent all residual tail-zero sources are silent on the all-one rows, and share the successful archive of this unresolved pair. Any first zero before the final position would merge the pair, so its adaptive path must choose $11$ at every earlier block and $10$ as the parent. All residual tail-zero sources share those actions and outputs; none can stop separately while the pair makes the archive nonhomogeneous. They therefore actually reach the complete residual archive (53.8) at depth $p$. The suffix lower bound applies there to all adaptive choices and adds to the paid $p$ blocks. If $b_v$ is constant but the fibre is not constant, the same-phase pair at another phase already gives the lower bound $p$. The attaining stream (53.6) followed by the indicated suffix meets both cases. This proves $F_v$ on each fibre; the free initial value selects its own adaptive controller, giving their maximum.

For preset control apply exactly the same prefix and suffix argument to the ordered table $\lambda(j)=(\lambda_0(j),\lambda_1(j))$ with positive-tail label $(R_0,R_1)$. It has arbitrary pair coincidences and the same actual graph and suffix. Theorem 29.2 gives its exact original preset cost without a second experiment or an adaptive value join. Projecting the acquired pair label using the remembered free value returns $f$. This proves both equalities of (53.5), including the zero cases and all original source conditions. For the injective specialization, its residual table has $p$ distinct labels. Equation (53.3) gives additional fee one at $p=2$, two at $p=3$, and $p-2$ at $p\ge4$. Adding the actual parent fee $p$ gives the stated values. Arbitrary coincidence of $R_v$ with one phase label does not remove the unequal same-phase pair at another phase, so the lower bound remains valid. These family values do not assert sharpness of (51.11). ∎

**定理 53.3（Value dependence inside the maximal-cut family）。** For (53.1),

$$
0\le C_{\rm pre}(f)-C_{\rm ad}(f)\le1.
\tag{53.12}
$$

If at least one fibre is nonconstant, write $\alpha=\max\{\psi(b_0),\psi(b_1)\}$. Then the two exact fees are $p+\alpha$ and $p+\psi(b)$. Their difference is one precisely when both scalar residual tables have one-block fee, while their ordered-pair residual table has three distinct labels. This can occur at every $p\ge3$. It is a value-dependent comparison for this family, not a universal bound on preset excess.

**证明。** A constant full fibre has constant $b_v$ and $\psi(b_v)=0$. Thus (53.5) gives the displayed forms whenever some fibre is nonconstant. If $\alpha=0$, both residual components are constant and so is $b$. If $\alpha=1$, each scalar outside set $i\ge2$ is constant and each scalar residual has at most two labels. The pair outside is consequently constant. The pair residual has at most three labels, one at each of indices zero and one and a single outside label. For $p=2$ the outside is empty and there are at most two. It has fee one unless it has three distinct labels, when its last possible differing boundary is at most one and its fee is two. Three pair labels require both scalar tables to be nonconstant, since one constant component would leave at most two pair labels.

If $\alpha\ge2$, let $B_v$ be each nonconstant component's last differing boundary. A component with fee at most one has no differing boundary beyond index one. The pair's differing boundaries are exactly the union of those of its components. Therefore the pair also fails the one-block condition and

$$
\psi(b)=\max\{2,\max_{v:\,b_v\text{ nonconstant}}B(b_v)\}=\alpha.
\tag{53.13}
$$

This covers all cases and proves the characterization.

For actual attaining examples, choose $A\ne B$, put $R_0=R_1=A$, and put all non-residual tail-zero labels equal to $A$. On the residual order (53.8) let

$$
b_0=(A,B,A,A,\ldots,A),\qquad
b_1=(A,A,B,B,\ldots,B).
\tag{53.14}
$$

For every $p\ge3$ each component has additional fee one, but the pair has three labels and additional fee two. Both complete-source fibres have positive-tail label $A$. Their exact fees are $C_{\rm ad}=p+1$ and $C_{\rm pre}=p+2$. The common paid parent is (53.6). Value zero uses suffix $01$, marking only its $B$ endpoint; value one uses suffix $11$, marking its two $A$ endpoints relative to its outside label $B$. The preset pair uses $11\mid11$: residual indices zero, one and two have columns $(1,0),(1,1),(0,1)$ respectively, and every later index has column $(0,0)$ and the same pair label as index two. These words start at actual tail zero and contain at most four consecutive ones, strictly below $k=2p$ for $p\ge3$. Every reached block is paid. This proves attainability of the claimed one-block excess. ∎

## 54. Original cost quantifiers and the residual scopes

**定义 54.1（Exact structural scope and the remaining fee problem）。** The cost problem retains the fixed matched $V_k\bmod2$ reader, every jointly attainable complete-block history, immutable INITIAL labels, actual phases $g\mathbb Z/(k+1)\mathbb Z$, both free values and independent absorbing bottom. Only complete endpoints are observed; every actual wait, padding, clearing and repair block is paid. Adaptive and one-global-stream preset costs remain separate objectives for every original $k\ge2,m\ge1$.

Theorem 51.2 gives a sufficient $k+1$ preset ceiling on the full proper-narrow coprime slice (51.1). Theorem 51.3 sharpens it to $k$ at eligible boundary cuts and at every even-order width-two cut. Theorem 51.4 has its own adaptive finiteness premise and the discharged [S1, Theorem 5.2] interface. None of these sufficient ceilings is defined as a sharp supremum. Equation (52.6) is an exact structural minimum for every full INITIAL target at even order and width two; evaluating its minimum as a closed numerical function of each arbitrary table is a further problem. Equation (53.5) is a closed exact family law on all its positive-tail and value fibres; (53.12) is restricted to that family.

The exact individual fees for arbitrary INITIAL targets at coprime proper-narrow $m\ge3$, their sharp finite ceilings, arbitrary INITIAL adaptive fees outside the stated family and supplied exact laws, and the remaining original widths are unresolved by these statements. No seam-elimination premise at $k\ge4m$ is imposed: (52.5) remains an explicit requirement at every $p$. Finite adaptive attainability is not defined to be finite preset attainability, and the family equality cases do not impose an arbitrary-target adaptive equality.

The existing unit-width laws of Theorems 25.3–25.4, noncoprime proper-narrow $m\ge3$ law of Theorem 33.2, odd-order width-two law of Theorem 44.2, and wide and odd-critical laws of Theorem 48.1 retain their own parameter hypotheses. The original phase-only tables and their acquired-support mechanisms in [S11, Section 4], [S13, Definition 1.3 and Theorem 6.1] and [S15, Theorem 3.3] do not replace the mixed-tail parent in (53.6). Theorem 43.2 supplies the consumed two-endpoint suffix argument; (53.7)–(53.10) establish its actual even-order source, phase calendar, safe operation, INITIAL label and paid acquisition correspondence. A row evaluated on a stopped source is only a design coordinate, never an observed event or another branch's information.

Moore's single-machine simple experiments and van den Bos–Vaandrager's completed-observation tests (*State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2](https://arxiv.org/pdf/1907.11034v2), Definitions 12, 14, 17, 20 and Figure 3) supply experiment semantics and irreversible-merge boundaries. Their general testing statements supply neither the actual charge schedule (51.7)–(51.8), its paid horizon, the simultaneous graph/seam minimum, nor a transfer from independent child optima to a common preset stream. The remaining mathematical problem keeps those literal correspondence obligations.

## 追加锚（本行以下为增补区）

## 55. Actual positive offspring at even order and width two

**定义 55.1（Full source and the actual chronological coordinates）。** In Chapters 55–59 fix

$$
k=2p\ge4,\qquad m=2,\qquad T=2p+1,\qquad
P=\mathbb Z/T\mathbb Z,\qquad F_v(j,s)=f(v,-j,s).
\tag{55.1}
$$

The target $f:Q\to Y$ is arbitrary on the full INITIAL record set of Chapter 1. Every phase, every INITIAL tail $0\le s<k$, both free values, and independent initial bottom are retained. Initial bottom returns $f(\bot)$ freely. Since $2<k$, both original alphabets contain exactly $00,01,10,11$; cross-block rejection is still an actual operation. The fee counts complete emitted blocks, including waits and clearing words. A chronological index counts blocks issued by this controller, rather than an unobserved length of the initial history.

At index $t$, write $u=2t\pmod T$. Formula (1.4) gives the actual successful charge sets and tail updates:

$$
\begin{array}{c|c|c|c}
B&E_t(B)&\text{safety from common tail }\sigma&\text{new tail}\\ \hline
00&\varnothing&\text{always}&0\\
01&\{u+1,u+2\}&\text{always}&1\\
10&\{u,u+1\}&\sigma+1<k&0\\
11&\{u,u+2\}&\sigma+2<k&\sigma+2.
\end{array}
\tag{55.2}
$$

All vertices in a row are actual and distinct. Each row is the charge of its displayed literal word, with full physical charges $(x,x\oplus y,y)$ for $B=xy$. A rejected endpoint is bottom, not a binary charge.

A *recorded-zero archive* has paid depth $b\ge1$, has successfully observed every issued endpoint, and contains a zero in its own issued prefix. Its candidates have common observed current value and common current tail $\sigma<k$. Their INITIAL phase support is $S\subseteq P$. Assume one well-defined immutable label $\lambda(j)$ for each $j\in S$: all retained INITIAL tails and histories at that phase have that label. This last assumption is necessary for completion once those histories have merged. Every candidate shares this archive and is an actual continuation of its own original history. No condition is imposed on its original tail except the conditions that produced the archive. Denote its minimum worst-branch additional adaptive fee by $D_{\rm ad}(b,S,\sigma,\lambda)$, excluding the already-paid $b$ blocks; an empty archive has additional fee zero.

**引理 55.2（The tail of a nonconstant positive child）。** At a nonconstant recorded-zero archive, every action in a correct continuation is safe on all its candidates. Its positive-difference child is $A=S\cap E_b(B)$. If that child has unequal labels, then $|A|=2$. Its common tail is zero for $B=10$, one for $B=01$, and two for $B=11$. In the last case the old tail was necessarily zero.

**证明。** All candidates have the same tail and take the same word, so any rejection is simultaneous. It replaces the whole nonconstant archive by one absorbing output and cannot return different INITIAL labels. Thus the next word must be safe. Equation (55.2) gives the support and the first two asserted tails; a singleton or empty support is constant.

For $11$, suppose the old tail is positive. There is a preceding paid block, because a zero has already been recorded. That preceding word ended in one. Its physical window is $\{u-2,u-1,u\}$ and its charge at $u$ is one. If its observed difference was zero, the current support excludes $u$. If its observed difference was one, the current support lies inside that preceding window, which excludes $u+2$: the four residues $u-2,u-1,u,u+2$ are distinct for every odd $T\ge5$. In either case $S\cap\{u,u+2\}$ has at most one member. A nonconstant positive child of $11$ therefore has old tail zero, and new tail two. This argument uses the actual immediately preceding word and observation in the same archive. It does not obtain a missing phase from a sibling. ∎

**定理 55.3（Exact additional side prices）。** At the positive child of an actual safe action at a recorded-zero archive, the minimum additional adaptive fee is the following expression. It also applies to the successful positive child of a first-zero parent $00,01$ or $10$ whenever that parent has retained one well-defined INITIAL label per surviving phase:

$$
\delta(A,B)=
\begin{cases}
0,&\lambda|_A\text{ is constant},\\
p,&\lambda|_A\text{ is nonconstant and }B=10,\\
1,&\lambda|_A\text{ is nonconstant and }B\in\{01,11\}.
\end{cases}
\tag{55.3}
$$

Empty children have price zero and are not executed. Every nonconstant price is attained by one fixed literal continuation on that child's own archive, so it is also the minimum preset *continuation* fee there. For $11$ the recorded-zero and common-label hypotheses include Lemma 55.2; an unrelated abstract pair with arbitrary high tail is not covered.

**证明。** A constant child stops at the parent endpoint and returns its common INITIAL label. Otherwise it contains exactly the two phases of its row, which have the same current value after the positive response.

Write $t$ for the parent action's actual chronological index and $u=2t\pmod T$. For $10$ these phases are $u,u+1$, and the child's tail is zero. Their distinct coefficient positions modulo $T$ are $u-1$ and $u+1$; position $u$ is common. The latter distinct position was the zero second bit of the parent. After that parent, both phases have coefficient zero at every absolute bit position from $2t+2$ through $2t+T-2$. Their first possible new separation is at $2t+T-1=2t+2p$, the first bit of block $t+p$. Until that bit they have equal outputs and equal tails under any common actions; an adaptive controller must choose the same actions on both. Common rejection is irreversible and cannot complete unequal labels. Neither source can stop sooner. Hence at least $p$ further complete blocks are necessary, including all waits. Issue

$$
\underbrace{00\mid\cdots\mid00}_{p-1\text{ paid blocks}}\mid10
\quad\text{at indices }b+1,\ldots,b+p.
\tag{55.4}
$$

The last word has charge $\{u-1,u\}$ and marks exactly phase $u$ within this child. All preceding words keep tail zero; the final isolated one and its clearing zero are safe. Its actual endpoint returns the respective label. The fee is exactly $p$.

For $01$, the phases are $u+1,u+2$, at tail one. The next literal $10$ has charge $\{u+2,u+3\}$ and separates exactly the right member of this pair. Its leading one joins a run of two, strictly below $k$. For $11$, Lemma 55.2 gives phases $u,u+2$ at tail two; the same next $10$ marks only $u+2$ and joins a run of three, strictly below every $k\ge4$. The second bit clears the tail in both cases and is part of the paid block. Unequal labels cannot stop at their common parent archive, so one block is also a lower bound. Both continuations decode their own new endpoint difference. No final cleanup is required after a successful stop. ∎

## 56. Exact prices before the first recorded zero

**定义 56.1（The unzeroed rectangle）。** After $q$ successful words $11$, with no zero yet issued, put

$$
h_q=k-2q>0.
\tag{56.1}
$$

If the acquired phase support is $S$, the INITIAL candidates are exactly $\{(v,-j,s):j\in S,\ 0\le s<h_q\}$. Their current tails are $s+2q$, their current phases are $-j+2q$, and their current value is the common observed value. This is the actual rectangle of (51.17), supplied by [S1, Lemma 4.2], with the remembered *initial* value $v$ in $F_v$. In particular, a positive response does not replace $v$ by the current value in the target.

For a known phase $j$ on such an actually acquired archive, define, for $0\le n\le h_q/2-1$, the condition

$$
\mathcal R(j,q,n):\quad
F_v(j,\cdot)\text{ is constant on }[h_q-2i-2,h_q-2i)
\quad(0\le i<n).
\tag{56.2}
$$

Intervals here and below contain integer INITIAL tails. Define the explicit tail price

$$
\begin{aligned}
\eta_v(j,q)=\min\Bigl(&\{n:\mathcal R(j,q,n),\
 F_v(j,\cdot)\text{ constant on }[0,h_q-2n)\}\\
&\cup\{n+1:\mathcal R(j,q,n),\
 F_v(j,\cdot)\text{ constant on }[0,h_q-2n-1)\}\Bigr),
\end{aligned}
\tag{56.3}
$$

where $n$ in each set has the range just stated, and an empty minimum is $+\infty$. This is a finite comparison of the original tail table. The first set includes zero precisely for a constant remaining table.

**引理 56.2（Known-phase tail price, with all actions allowed）。** The exact additional adaptive fee on the archive of Definition 56.1 with $S=\{j\}$ is $\eta_v(j,q)$. Each finite value is attained using $n$ further $11$ words, followed either by immediate stopping or by one literal $10$. Every attained endpoint returns the INITIAL label; no phase-recovery operation is needed.

**证明。** Until a zero is issued, all surviving tails at this one phase have the same scalar outputs. A successful $11$ removes exactly the top two INITIAL tails of the current rectangle to one bottom endpoint, and leaves the lower rectangle. Its rejection pair must be homogeneous. After $n$ such words, these requirements are exactly (56.2).

If the lower rectangle is homogeneous, stopping there gives the first candidate in (56.3). Otherwise a word starting zero, either $00$ or $01$, merges every remaining INITIAL tail at the phase. Such a word cannot complete a nonconstant table. A first-zero $10$ rejects the one top tail $h_q-2n-1$ and merges all the lower tails. Its rejection label is automatically well-defined at a known phase; it is correct exactly when the lower interval in the second set is homogeneous. All its survivors have $s+2(q+n)+1<k$ and then take the actual clearing zero. This gives the second candidate and its lawful construction.

These cases also prove the lower bound for every adaptive controller. Before its first zero it can only issue $11$, and each rejected top pair has the condition in (56.2). It may instead stop with a homogeneous lower rectangle. If it reaches a first zero on a nonconstant rectangle, that word must be $10$ and its merged lower interval must be homogeneous. If an all-one word would absorb the whole remaining rectangle, correctness already makes that rectangle homogeneous, so stopping before it improves the fee. Thus a minimum uses at most $h_q/2-1$ further successful all-one words. Its stopping or first-zero event supplies exactly a candidate no greater than its paid fee in (56.3). Conversely the displayed construction realizes every candidate with no larger fee. At the least candidate, an earlier homogeneous stopping archive would give a smaller candidate, so the least fee is attained as an actual maximum, not a count of unused words. Empty rejection intervals are never decoded. ∎

**定义 56.3（The one genuine pre-zero phase pair）。** The positive successful child of the original root $11$ has phase support $\{0,2\}$, paid depth one, current value $v\oplus1$, and INITIAL tails $0\le s<h$, where $h=k-2$. Use the following four possible numbers, only when their accompanying conditions hold:

$$
\begin{array}{c|l}
\text{number}&\text{condition}\\ \hline
0&F_v\text{ constant on }\{0,2\}\times[0,h)\\
p&F_v(j,\cdot)\text{ constant on }[0,h)\text{ for }j=0,2\\
1&F_v\text{ constant on }\{0,2\}\times\{h-1\},\quad
 F_v(j,\cdot)\text{ constant on }[0,h-1)\text{ for }j=0,2\\
1+\max\{\eta_v(0,2),\eta_v(2,2)\}&h>2,\quad
 F_v\text{ constant on }\{0,2\}\times[h-2,h).
\end{array}
\tag{56.4}
$$

Let $\chi_v$ be their minimum, with $+\infty$ when there is no finite entry. The $q=2$ tail prices in the last row are used only when $h>2$, so $h_2=k-4>0$. There is no nonexistent height-zero singleton call at $k=4$.

**定理 56.4（Exact root-pair fee）。** The exact minimum additional adaptive fee on the actual root-pair archive of Definition 56.3 is $\chi_v$.

**证明。** If the whole rectangle is homogeneous it stops freely. Otherwise examine all four possible first words at chronological index one, where the physical window is $\{2,3,4\}$ modulo $T$.

A first $00$ or $01$ clears all tails. Neither charges either of phases zero and two: $00$ has no charge and $01$ has charge $\{3,4\}$. Completion therefore requires constancy of each phase's whole INITIAL tail fibre. If their two labels agree, the archive was already homogeneous. If they differ, both sources have coefficient zero after this parent through absolute position $k-1$; the first remaining distinguishing position is $k$, the first bit of block $p$. Common rejection cannot distinguish them. Counting the parent at index one, at least $p$ further blocks are necessary. The literal continuation

$$
(00)^{p-1}\mid10
\quad\text{at indices }1,\ldots,p
\tag{56.5}
$$

attains $p$: its first word clears all possible tails, its waits are paid, and its last charge $\{k,0\}$ marks only phase zero. This proves the second row of (56.4) whenever it is needed. It is the endpoint-return mechanism of Theorem 2.2 at $N=\lceil(k+1)/2\rceil=p+1$, with its already-paid root block removed; the present archive has exactly that supplier's low-tail pair.

A first $10$ rejects exactly INITIAL tail $h-1$ at both phases, at one common bottom endpoint. Its successful difference marks phase two and not phase zero. The two success archives therefore have known phases, but all their lower tails have already merged at that word's zero. Necessity and sufficiency are exactly the third row of (56.4), and successful and rejected sources stop after this one complete block.

A first $11$ rejects the top two INITIAL tails at both phases. If $h=2$, this absorbs the whole archive and cannot help a nonconstant target. If $h>2$, its successful difference marks phase two and not phase zero, leaving two known-phase rectangles at paid depth two. The common rejection band must be homogeneous. Lemma 56.2 gives the exact further prices of the two success archives, so the last row of (56.4) is both necessary and sufficient. Its rejection sources stop after the first of these additional blocks. These four actions and immediate stopping exhaust every adaptive first choice. Their exact lower bounds and literal constructions prove the minimum. The constant and unequal-label cases, including $p=2$, are included without a special unattainable operation. ∎

**引理 56.5（All other pre-zero positive children are singletons）。** On the chronological zero-difference path of $q$ successful all-one blocks from the root, the phase supports are

$$
U_0=P,\qquad U_q=P\setminus\{0,2,4,\ldots,2q\}
\quad(1\le q\le p-1).
\tag{56.6}
$$

The positive successful root child is $\{0,2\}$. At an all-one block of index $t$ with $1\le t\le p-2$, its positive child on this path is exactly $\{2t+2\}$, with INITIAL tails $[0,h_{t+1})$, and additional fee $\eta_v(2t+2,t+1)$. Its zero child is $U_{t+1}$. Rejection is the entire rectangle $U_t\times[h_t-2,h_t)$, with the single bottom endpoint.

**证明。** The charge of $11$ is $\{2t,2t+2\}$. At the root both vertices remain. A zero root response removes zero and two. Subsequently $2t$ was removed by the preceding zero response, whereas $2t+2$ has not appeared; no wrap occurs at the stated indices. Induction gives (56.6) and each singleton child. The rejection and surviving tail ranges follow by adding two ones to $s+2t$. Lemma 56.2 applies to the actually acquired singleton rectangle, with its own paid depth and original $v$. All these rectangles consist of jointly actual histories from (1.3). ∎

## 57. A priced literal spine after the recorded zero

**定义 57.1（One chronological spine and its actual maximum）。** Start at a recorded-zero archive $(b,S,\sigma,\lambda)$ of Definition 55.1. A priced spine is a finite sequence of literal words $B_b,\ldots,B_{L-1}$ with $L\ge b$. Set $S_b=S$, $\sigma_b=\sigma$ and, at each issued index $t$, require $S_t$ to be nonempty and $\lambda|_{S_t}$ nonconstant. Require the safety inequality in (55.2), and put

$$
A_t=S_t\cap E_t(B_t),\qquad
S_{t+1}=S_t\setminus E_t(B_t),\qquad
\sigma_{t+1}=\text{the literal new tail in (55.2)}.
\tag{57.1}
$$

Require $\lambda|_{S_L}$ to be constant; the empty set is constant. Each $A_t$ is the *first positive* child off this zero-difference spine, with its own acquired archive at paid depth $t+1$. Give it the explicit price (55.3). The certificate's absolute paid depth is

$$
\Pi=\max\left(\{L\}\cup
\{t+1+\delta(A_t,B_t):b\le t<L,\ A_t\ne\varnothing\}\right).
\tag{57.2}
$$

For an empty sequence $L=b$, a constant or empty support has $\Pi=b$ and additional price zero. An empty support is only a vacuous composition case, not an executed source. No positive child has an optimization variable or another decision tree: its continuation is the specified constant stop, paid return (55.4), or next-block $10$.

**定理 57.2（Exact spine reduction, including waits and seams）。** At every actual archive of Definition 55.1,

$$
D_{\rm ad}(b,S,\sigma,\lambda)
=\min_{\text{priced literal spines}}(\Pi-b).
\tag{57.3}
$$

Every minimum is attained by a lawful adaptive policy whose choices after the first positive response are a fixed literal stream on that child. For every nonempty starting archive, each certificate realizes exactly the worst actual depth $\Pi$. The zero path and its side streams need not agree after branching.

**证明。** Construct the policy by issuing the next written spine word when all differences acquired since this starting archive have been zero. Safety and (57.1) describe its actual success outputs and common tails. On its first positive response stop for a constant $A_t$; otherwise run the literal continuation of Theorem 55.3 and decode that child's own endpoints. On the terminal zero archive stop with its common label. The support and tail calculations hold inductively on every executed source. A common-tail rejection never occurs. The old zero and all new words belong to this same source's chronological archive.

For each nonempty $A_t$, actual candidates reach that child and its least price is attained, giving a branch of paid depth $t+1+\delta$. If $S_L$ is nonempty, candidates in it traverse every spine word and stop at depth $L$. If $S_L$ is empty and $L>b$, the last nonempty $S_{L-1}$ is wholly sent to the positive child, so some source still reaches and pays the last block at depth $L$. Hence (57.2) is the actual maximum. Zero-charge $00$ rows and every bit of the repair or return words are charged when reached; there is no nominal word counted after stopping.

Conversely, take any finite correct adaptive continuation, stopping a homogeneous archive immediately. At every nonconstant common-tail node its action must be safe by Lemma 55.2. Follow its zero-difference path until it stops or its support becomes empty, retaining those whole words and tails. At each positive child, Theorem 55.3 supplies an exact all-action lower bound for its further subtree. Replace that subtree by its fixed attaining continuation. Its new maximum does not exceed the old maximum. The retained zero path satisfies (57.1), and its terminal support is homogeneous or empty. This yields a priced spine with $\Pi-b$ no greater than the original continuation fee. Both inequalities prove (57.3).

For existence of a finite continuation, use $T-1$ successive $01$ blocks starting at index $b$. Every one starts zero and safely clears any incoming tail. Their actual charge edges $\{2t+1,2t+2\}\pmod T$ are all edges but one of the physical $T$-cycle, because multiplication by two permutes its residues. They form a spanning path. Its incidence columns are distinct on $T\ge5$ vertices: equal nonzero columns at distinct vertices would require a component on those two vertices, and a zero column would require an isolated vertex. Thus these own-archive differences identify $j$ and return $\lambda(j)$, also after restriction to $S$. This is the safe phase-recovery mechanism already supplied by [S1, Theorem 3.1] and the incidence argument of Theorem 52.3. An optimal finite fee is an attained nonnegative integer. The extraction and replacement just proved supply an attaining priced spine. No equality to a single GLOBAL-preset stream is inferred. ∎

## 58. The arbitrary INITIAL adaptive structural minimum

**定义 58.1（The pre-zero prefix price and admissibility）。** Fix a free initial value $v$. Choose $q\in\{0,\ldots,p-1\}$. The principal pre-zero path is $q$ words $11$, all with difference zero, so its actual supports are (56.6). Require, for every $0\le t<q$,

$$
\begin{gathered}
F_v\text{ nonconstant on }U_t\times[0,h_t),\\
F_v\text{ constant on }U_t\times[h_t-2,h_t).
\end{gathered}
\tag{58.1}
$$

The second condition decodes the one actual rejection endpoint of that word. Set

$$
\Delta_v(q)=\max\left(
\{q\}\cup\{1+\chi_v:q>0\}\cup
\{t+1+\eta_v(2t+2,t+1):1\le t<q\}
\right).
\tag{58.2}
$$

If any displayed price is infinite, this prefix is inadmissible. For $q=0$ the two extra sets are empty and $\Delta_v(0)=0$. The quantity is absolute depth from the original initial reading, not a sum of sibling fees. The $q$ term includes every pre-zero rejection depth $t+1\le q$.

There are two terminal choices on this principal path.

A **pre-zero stop** is allowed when $F_v$ is constant on $U_q\times[0,h_q)$. Its complete candidate fee is $\Delta_v(q)$. This includes $q=0$ and all successful-fibre zero-fee cases.

A **first-zero parent** is allowed only on a nonconstant $U_q\times[0,h_q)$. Choose $B_q\in\{00,01,10\}$, and put $r=0$ for $00,01$, $r=1$ for $10$. Require

$$
\begin{aligned}
&F_v\text{ constant on }U_q\times[h_q-r,h_q),\\
&F_v(j,s)=F_v(j,0)
\quad(j\in U_q,\ 0\le s<h_q-r).
\end{aligned}
\tag{58.3}
$$

For $r=0$ the first set is empty and imposes no label. Write $\lambda_v(j)=F_v(j,0)$ on $U_q$, and let

$$
A=U_q\cap E_q(B_q),\qquad Z=U_q\setminus E_q(B_q),\qquad b=q+1.
\tag{58.4}
$$

The successful parent has common tail $\rho=0$ for $00,10$, and $\rho=1$ for $01$. Assign $A$ its exact additional price $\delta(A,B_q)$ in (55.3). Choose one priced literal spine of Definition 57.1 from the actual zero child $(b,Z,\rho,\lambda_v|_Z)$, with absolute price $\Pi$. Its complete candidate fee is

$$
M=\max\{\Delta_v(q),\ q+1,\ q+1+\delta(A,B_q),\ \Pi\}.
\tag{58.5}
$$

If $A$ is empty, its term is just the already included $q+1$, without an execution. If $Z$ is empty, use its vacuous empty spine with $\Pi=q+1$. These conventions do not create observations on an empty source. A parent's bottom child, when nonempty, stops at depth $q+1$ with the common label of its rejected rectangle in the first line of (58.3).

Let $\mathcal C_v$ contain all pre-zero-stop and first-zero-parent candidate fees just defined that are at most $k$. In particular every chosen post-zero spine has $L\le k$, and every priced side completion also ends by $k$. This is a finite set specified by tail-table comparisons, $q$, and one sequence of at most $k-q-1$ literal words. It contains no off-spine adaptive optimization.

**定理 58.2（Full arbitrary-target law and an optimal literal policy）。** For every arbitrary immutable INITIAL target in (55.1), under both original alphabets,

$$
\boxed{\quad
C_{\rm ad}(f)=\max\left\{
\min\mathcal C_0,\ \min\mathcal C_1
\right\},\qquad \min\varnothing=+\infty.
\quad}
\tag{58.6}
$$

Every finite minimum has a lawful policy with exactly that maximum ACTUAL emitted-complete-block depth. The equality covers arbitrary tail partitions and labels, all $T$ phases, both values, early stops, intentional rejection, empty children, and infinity. It is a finite structural minimum, rather than a closed scalar evaluation or a sharp uniform ceiling.

**证明（literal upper bound）。** Select a finite candidate on one initial value fibre. On its principal pre-zero path issue the chosen $q$ words $11$ until a nonzero response or rejection occurs. The actual candidates, outputs and rejection bands are those of Definition 56.1 and Lemma 56.5. On a rejected endpoint return its homogeneous band label from (58.1) and stop. On the positive root endpoint use an attaining policy of Theorem 56.4, with the remembered initial $v$; on every later positive endpoint use the attaining known-phase tail policy of Lemma 56.2 at its actual index. Each such branch is an actual acquired rectangle, not an independently chosen initial source. Those subpolicies include their own further rejecting, stopping and clearing endpoints. If all $q$ differences are zero, arrive at $U_q\times[0,h_q)$ at paid depth $q$.

For a pre-zero stop, return its homogeneous label. The source set of this terminal rectangle is nonempty: $|U_q|=T-q-1\ge p+1$ for $q\ge1$, and $U_0=P$. Every INITIAL tail zero at its phases survives, and each preceding principal node was nonconstant by (58.1), so there is an actual source paying all $q$ blocks. Every nonempty side archive has its attained exact continuation price. Formula (58.2) is therefore the actual maximum, including any earlier reject leaf.

For a first-zero parent, the band $s\ge h_q-r$ is rejected before its zero, all at one bottom endpoint. All other sources satisfy $s+2q+r<k$, reach that zero, and finish the parent safely. There can be no further run of length $k$ in its at most two bits. For each surviving phase its INITIAL label is $F_v(j,0)$ by (58.3), so its merged tails lose no required distinction. Its endpoint difference, support and literal tail are exactly (58.4) and (55.2). On a positive endpoint use its constant stop or the prescribed optimal side stream; on a zero endpoint use the chosen priced spine and its prescribed side streams. Theorem 57.2 proves all their seam inequalities and decoding. At every point the current value used as a difference baseline is the source's own observed endpoint. No observation from any other branch is supplied.

Some actual source reaches the parent, because its preceding principal archive was nonconstant and has surviving tail-zero witnesses. All nonempty success children and, for $r=1$, its rejected band have such actual witnesses. The exact prices of Theorems 55.3, 56.4, Lemma 56.2 and Theorem 57.2 are attained on their corresponding archives. Consequently (58.5) is the exact maximum of the original execution depths. The parent, every $00$ wait, all pre-zero words and all padding, repair and clearing blocks are included. No word is charged to a source that already stopped. This constructs each candidate under both alphabets and proves the upper inequality in (58.6).

**证明（all-action lower bound and completeness）。** Take any finite correct controller on this initial value fibre and stop every homogeneous archive immediately. Before its first zero, every issued word must be $11$, and the acquired supports and tail rectangles have the form in Definition 56.1. Follow its zero-difference path. Every successful all-one step on this path has its rejected top-two rectangle homogeneous; otherwise different INITIAL labels enter the same bottom archive. When the step is the root, its positive successful child is precisely the archive priced by $\chi_v$. At each later step the positive child is the singleton of Lemma 56.5, priced by $\eta_v$. Their all-action lower bounds apply to the actual original subtrees, regardless of their later controls. Hence (58.1) holds and (58.2) is no greater than this controller's maximum on the prefix and its side branches.

The zero path can have at most $p-1$ successful $11$ words before its terminal choice. A next $11$ at $q=p-1$ would reject every remaining tail, so at a nonconstant archive it cannot occur in a correct controller. If the path stops before any zero, its rectangle is homogeneous and supplies the pre-zero-stop candidate. Otherwise its first zero is in exactly $00,01$ or $10$, with $r$ as in (58.3). The actual first-zero loss of [S1, Lemma 4.3] forces both conditions (58.3): its rejection band acquires one bottom archive, and each surviving same-phase tail fibre is merged before the next observation. Unequal labels in either merged set cannot be recovered by any future action. These are necessary conditions, not sufficient conditions substituted for the all-action test.

At a successful parent endpoint all retained tails are common and the per-phase INITIAL label is well-defined. The positive child's exact further lower bound is (55.3). Follow the zero child's actual zero-difference path and apply Theorem 57.2 to replace every first-positive subtree by its fixed optimal side stream. This produces a priced spine with absolute maximum no greater than the original subtree's maximum. Thus the controller supplies a complete candidate of cost no greater than its original maximum. The replacement is branchwise; it never changes another sibling's archive or requires their streams to coincide.

To justify the finite restriction $M\le k$, use the supplied adaptive horizon, Theorem 51.4, with $m=2$, even $k\ge4$, full joint source (1.3), free initial value, and the same target and alphabets. Its proof is fibrewise through [S1, Theorem 5.2]; it requires adaptive finiteness, without preset finiteness. Equivalently extend this one-fibre target by a constant target on the other value and an arbitrary bottom label and apply that horizon. Thus every finite optimum on this fibre is at most $k$. Extract the preceding candidate from an optimal controller of that bounded fee; it belongs to $\mathcal C_v$ and costs no more. Conversely every member of $\mathcal C_v$ has the actual controller of the upper-bound construction. Its least value therefore equals the finite optimum. If $\mathcal C_v$ is empty but a finite controller existed, the same horizon and extraction would supply a member, a contradiction. This proves the infinity case as well.

Finally the free initial value selects the independently defined optimal fibre policy, so the full adaptive fee is the maximum of the two fibre minima. No equality between their labels is required. Initial bottom is a distinct free observation and returns its independent target label at fee zero. If both successful fibres are constant, both sets contain zero and the total fee is zero even when their two constant labels and the bottom label are all different. If either fibre has no candidate, no uniform finite correct full controller exists. This proves (58.6) with every original source coordinate retained. ∎

**命题 58.3（Finite presentation and effective selection）。** With a decidable finite target presentation on the INITIAL records, (58.6) can be evaluated by finite enumeration, and a least candidate yields an effectively specified optimal policy. For an arbitrary label set without decidable equality, (58.6) remains a semantic minimum and existence theorem; it does not assert a general algorithm for arbitrary target expressions on histories.

**证明。** There are $2kT+1$ INITIAL records. A finite partition of these records, or a finite label table with decidable equality, decides every constancy and equality condition in (56.2)–(56.4), (58.1) and (58.3). The tail-price sets and root-pair choices are finite. Each $q$ has at most three parents; each chronological spine uses one of four words at each of at most $k-q-1$ indices, and its actual support and tail transitions are explicit. Compute its side prices and maximum, retaining only candidates at most $k$. Thus emptiness, the least fee, and its actual literal witnesses are decidable for this presentation. The stored initial value, issued-block count and own endpoint archive suffice to execute the selected policy. This proves no polynomial bound on enumeration time or memory, and gives no procedure deciding an unspecified infinite history target's factorization through INITIAL records. Without a decidable presentation, the finite comparisons are ordinary mathematical predicates, as in [S1, Note 5.3]. ∎

## 59. Source pullback, supplied overlap and the remaining objective

**命题 59.1（Full joint-source pullback of the structural policy）。** The policy of Theorem 58.2 is a policy on the original matched $V_k\bmod2$ reader and its whole actual-history prior, with exactly the fee in (58.6). Its phase rows and tail rectangles do not replace that reader by a known-source encoding, a marginal reachability model, or a machine with intermediate observations.

**证明。** Here $\gcd(2,T)=1$, so for every specified $(v,-j,s)$ the two congruences in (1.3) admit a complete-block history length $\ell$. That one legal word realizes its value, phase and tail together. Its adjusted first bit and terminal run supply $v$, its length supplies $-j$, and its separating zero keeps the run $s<k$ legal. Its two-bit pieces belong to either alphabet. Distinct phases or tails may use different unknown initial lengths; the controller reads none of those lengths. Independent initial bottom is also an actual history and remains distinct from either scalar value.

Starting from each such word, literal transitions are exactly (1.2). The issued displacement $2t$ gives the window $\{2t,2t+1,2t+2\}$ on the INITIAL index $j$, so (55.2) is the completed endpoint difference of the actual displayed action. Rejection bands follow the actual tail inequality before the first zero, while subsequent common-tail safety follows the same update. The induction proving the rectangles, supports and prices therefore holds for every actual representative, not just for one representative chosen to make a row reachable. Representatives of the same INITIAL record have the same deterministic future; the target is $f$ of that original record throughout. At a side branch the selected stream starts only after its own acquired endpoint, with the baseline and tail proved for that branch. The integer maxima count exactly the blocks emitted on these actual histories. This supplies the source, label, observation, operation and resource correspondence simultaneously. ∎

**数学引文 59.2（Exact reuse and the additional cost content）。** Chapter 1 and the pinned [S1, Definitions 1.2–2.1, Convention 1.3, Lemmas 4.2–4.3, Theorem 5.2 and Note 5.3] supply the original experiment, whole-history prior, pre-zero rectangles, irreversible tail merger, finite attainability interface and presentation boundary. [S2, Theorem 14.1] supplies the matched coefficient period; [S10, Interface 2.1] supplies the literal path charges and inverse. These interfaces are credited, not new reader definitions or new attainability theorems. The supplied adaptive horizon of Theorem 51.4 is used solely to bound the structural search. Theorem 52.3 remains the distinct exact GLOBAL-preset minimum, and Theorems 53.2–53.3 retain their maximal-cut family scope.

The recorded-zero geometric argument of Theorem 27.3 and its spine idea in Theorem 27.5 concern $m\ge3$. Lemma 55.2 proves the width-two instance directly on the original preceding window. Theorem 55.3 then evaluates its actual side prices, rather than substituting a generic availability-code minimum. [S11, Theorem 4.1](https://raw.githubusercontent.com/the-omega-institute/trureturing/ef2fddd6bab3fe4b861b07e4c01577e942912ab8/docs/develop/theory/KBONACCI_COPRIME_PHASE_TARGET_COST.md) already gives the even-order width-two *binary phase-only* scan/repair law, with its literal next-block $10$ on a positive $01$ child. That pulse is credited reuse within Theorem 55.3. The $p$ option in (56.4) reuses Theorem 2.2's acquired endpoint-return pair, while its other options and tail-dependent minimum retain their own hypotheses. The $10$ return price, the general $11$ child condition, the pre-zero prices (56.3)–(56.4), and their arbitrary-tail integration in (58.6) are the reader-specific ordinary cost deductions here. Lemma 25.2a and Theorem 43.2 price different acquired suffixes; neither is asserted to supply an arbitrary pre-zero tail table or the root pair of Definition 56.3. The reduction has one chronological word spine and explicit side prices, rather than an optimization over unknown off-spine adaptive trees.

For the classical comparison, van den Bos and Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2](https://arxiv.org/html/1907.11034v2), Definitions 8–11 and Figure 3, define completed leaf observations, compatible tests and adaptive distinguishing graphs, and show that first actions may irreversibly merge initially different states. Those are the appropriate experiment and lower-bound semantics. They provide neither the physical three-vertex charge rows, the paid $p$ return, nor the INITIAL tail-band prices proved here. The single-source comparison with Moore and the reset/transfer and parity-query boundaries in Mathematical Citation 7.2 remain at their stated scopes. No exhaustive literature absence, originality, independent-prior or model-diversity claim accompanies these ordinary deductions.

**定义 59.3（Exact scope and the original all-parameter boundary）。** Equation (58.6) resolves the exact adaptive *structural minimum* for every arbitrary INITIAL target at even $k\ge4,m=2$. It includes semantic infinity and constructs an optimal lawful policy whenever the fee is finite. A numerical closed form for every table and a sharp supremum over finite target fees are separate questions; the supplied bound $k$ is used as a sufficient horizon, without a sharpness claim. Theorem 57.2 allows all later phases and cyclic returns, rather than a first-tour, phase-only or maximal-cut restriction.

The original objective still asks for exact minimum worst-branch actual emitted-complete-block fee for every attainable immutable INITIAL target at all $k\ge2,m\ge1$, separately for adaptive and one-global-stream preset control. The GLOBAL-preset law is still (52.6) on this slice, with its own joined-value conditions and simultaneous seams. Branchwise optimal streams in (58.6) are not flattened into one common stream. The exact unit-width results, odd-order width-two preset result, noncoprime proper-narrow preset result, wide and critical results, finite horizons and scoped families remain supplied at their own hypotheses. Regions outside those results and the present slice retain their stated open boundaries. These are ordinary mathematical proofs; source integrity checks and finite regression calculations do not substitute for them or assert a Lean/kernel status.

## 追加锚（本行以下为增补区）

## 60. Arbitrary-tail prices on the actual unzeroed archives

**定义 60.1（The coprime guarded domain and original tail tables）。** In Chapters 60–64 fix the original reader, whole actual-history prior, costs and alphabets of Chapter 1, with

$$
m\ge3,\qquad k\ge2m,\qquad T=k+1,\qquad
\gcd(m,T)=1,\qquad P=\mathbb Z/T\mathbb Z,\qquad
D=\left\lfloor\frac{k-1}{m}\right\rfloor.
\tag{60.1}
$$

The target $f:Q\to Y$ is arbitrary, and $F_v(j,s)=f(v,-j,s)$ always uses the remembered INITIAL value $v$. All integer intervals below contain INITIAL tails, and all phases are reduced modulo $T$ only where indicated. Constancy on an empty set is true; a minimum of an empty set is $+\infty$. Independent initial bottom returns its own label freely. Since $m<k$, both original alphabets contain all $2^m$ literal words, with the same cross-block rejection rule.

At a successful archive after $q$ emitted all-one blocks and no issued zero, put $h_q=k-qm>0$. For its own observed difference string $\beta$, the phase support is

$$
S=\{j\in P:\mathbf1_{\{tm,(t+1)m\}}(j)=\beta_t\ (0\le t<q)\}.
\tag{60.2}
$$

The INITIAL candidates are exactly $S\times[0,h_q)$ on the fixed free-value fibre. Their current records are $(z_q,-j+qm,s+qm)$, where $z_q=v\oplus\bigoplus_{t<q}\beta_t$. These are the supplied actual rectangles of [S1, Lemma 4.2] and (51.17), not a prior chosen independently at the current endpoint.

For a known phase $j$ at such an archive, and $0\le n\le\lfloor(h_q-1)/m\rfloor$, put $H=h_q-nm$ and require

$$
\mathcal R_v(j,q,n):\quad
F_v(j,\cdot)\text{ constant on }[h_q-(i+1)m,h_q-im)
\quad(0\le i<n).
\tag{60.3}
$$

Define the finite tail-table price

$$
\begin{aligned}
\eta_v(j,q)=\min\Bigl(&\{n:\mathcal R_v(j,q,n),\ F_v(j,\cdot)\text{ constant on }[0,H)\}\\
&\cup\{n+1:\mathcal R_v(j,q,n),\ \exists r\in\{1,\ldots,\min(m-1,H-1)\},\\
&\hspace{24mm}F_v(j,\cdot)\text{ constant on }[H-r,H),\quad
 F_v(j,\cdot)\text{ constant on }[0,H-r)\}\Bigr).
\end{aligned}
\tag{60.4}
$$

The range of $n$ is the one just stated in both sets. An empty range of $r$ contributes no second-set candidate. All comparisons concern the actual original tail table; there is no continuation-cost variable in (60.4).

**引理 60.2（Exact known-phase price under every action）。** On every actually acquired unzeroed rectangle (60.2) with $S=\{j\}$, its minimum additional adaptive fee is $\eta_v(j,q)$, including infinity. Every finite least value is attained by $n$ further all-one blocks, followed either by stopping or by the one complete word $1^r0^{m-r}$ specified in (60.4).

**证明。** Before its first issued zero, a controller can only choose $1^m$. Successful scalar increments at this known phase are independent of the original tail. The $i$th such word sends the top $m$ remaining tails to one bottom endpoint and leaves the lower interval. The rejected band must therefore have one INITIAL label. After $n$ successful words these requirements are exactly (60.3), and the remaining tails are $[0,H)$.

If that lower interval is homogeneous, stopping realizes the first set. Otherwise a first-zero word with leading run $r$ has the same scalar response on every successful tail and merges all of them at its zero. For $r=0$ it merges the whole nonconstant interval, so it cannot complete the target. For $r\ge H$ it rejects the whole interval, with the same failure. The only possible range is $1\le r\le\min(m-1,H-1)$. Its rejection band and its merged surviving interval must separately be homogeneous; these are exactly the second-set conditions. Any remaining bits after its first zero cannot recover a merged distinction, and there is no additional phase uncertainty. Thus every successful and rejecting source can stop at this next completed endpoint.

Conversely issue the $n$ all-one words, decoding each reached homogeneous rejection band, and then use the stated stop or $1^r0^{m-r}$. Every survivor has $s+(q+n)m+r<k$ before that zero, and the rest of the word is zero. No uncharged clearing operation is required. An actual tail-zero source survives all $n$ words and, in the second case, the parent, so the displayed number is an actual maximum of emitted blocks.

These cases exhaust all actions in any finite correct controller. An all-one word with remaining height at most $m$ rejects the entire archive, so it cannot help a nonconstant table. Hence its successful all-one prefix has $n\le\lfloor(h_q-1)/m\rfloor$, and its first stopping or first-zero event supplies a candidate no greater than its paid fee. The constructions give the converse inequality. If no finite candidate exists, a finite controller would supply one by the same argument. This proves the infinity case as well. ∎

**定义 60.3（The actual root pair and its finite price）。** The successful positive child of the original root $1^m$ has $S=\{0,m\}$, paid depth one, current value $v\oplus1$, and original tails $[0,h)$, where $h=k-m\ge m$. Set

$$
R=\left\lceil\frac{T}{m}\right\rceil-1
=\left\lfloor\frac{k}{m}\right\rfloor.
\tag{60.5}
$$

Let $\chi_v$ be the least finite entry in the following list, or infinity if none is finite:

$$
\begin{array}{c|l}
\text{additional fee}&\text{condition}\\ \hline
0&F_v\text{ constant on }\{0,m\}\times[0,h)\\
R&F_v(j,\cdot)\text{ constant on }[0,h)\text{ for each }j=0,m\\
1&\exists r\in\{1,\ldots,m-1\}:\quad
 F_v\text{ constant on }\{0,m\}\times[h-r,h),\quad
 F_v(j,\cdot)\text{ constant on }[0,h-r)\text{ for each }j=0,m\\
1+\max\{\eta_v(0,2),\eta_v(m,2)\}
&h>m,\quad F_v\text{ constant on }\{0,m\}\times[h-m,h).
\end{array}
\tag{60.6}
$$

Only the last row calls height $h_2=k-2m$, and only under $h>m$. In particular no height-zero singleton is called at $k=2m$.

**定理 60.4（The pre-zero root-pair connection）。** The minimum additional adaptive fee on the actual archive of Definition 60.3 is exactly $\chi_v$, under either original alphabet. Every finite least value has a literal attaining policy, and the lower bound considers every next word.

**证明。** The next physical window is $W_1=[m,2m]$. Since $T\ge2m+1$, phase zero is outside it, and phase $m$ is its leading vertex. For every next word $B$, their successful charges are therefore zero and $B_0$, respectively.

A homogeneous whole rectangle stops. For a first-zero word starting zero, both charges are zero. Every remaining tail survives and the word merges each phase's entire tail fibre. Completion thus requires the second row's separate constancies. If the two labels agree, the whole archive was homogeneous already. If they differ, a next first bit one would send their two original tails $h-1$ to the same bottom output, so every correct next word starts zero. That zero suppresses absolute position $m$, a distinguishing coefficient of phase $m$. Between it and absolute position $k-1$, both phases have coefficient zero: phase zero's next coefficient one is at $k$, whereas phase $m$ has no further one in this interval. After the first clearing zero their tails are common. Before position $k$, any common successful actions give identical archives, and common rejection cannot resolve unequal labels. A completed block before that position therefore cannot suffice. The lower bound, measured from the already-paid root, is $R$.

To attain it, write $N=R+1$ and $z=k-Rm$, so $0\le z<m$. At absolute indices $1,\ldots,R-1$ issue $0^m$, and at index $R$ issue $0^z1\,0^{m-z-1}$. Here $R\ge2$, so the first paid zero block clears every possible incoming tail, including $k-1$. The final isolated pulse is safe and has charge $\{k,0\}$ modulo $T$, marking phase zero and not phase $m$. It decodes the two phase labels. All $R$ additional blocks, including waits and pulse padding, are emitted on an actual surviving source. This is the credited endpoint-return mechanism of Theorem 2.2 on its acquired low-tail pair; no constant-outside hypothesis is needed for this already acquired archive.

For a first-zero word starting one, let its leading run be $r\in\{1,\ldots,m-1\}$. Since $h\ge m$, there are survivors. The top $r$ original tails at both phases enter one bottom archive, requiring the third row's common band label. Its zero merges every lower tail separately at each phase, requiring that row's two lower-fibre constancies. The successful charges zero and one distinguish the phases at this same endpoint. Thus the conditions are necessary and sufficient, and $1^r0^{m-r}$ realizes fee one. All its suffix zeros are inside this paid action.

The only word without a zero is $1^m$. If $h=m$, it rejects the whole nonconstant rectangle and cannot be used. If $h>m$, its one rejection endpoint contains exactly the common top-$m$ band in the last row. Its two successful responses separate the phases into actual known-phase rectangles at paid depth two, with original tails $[0,k-2m)$. Lemma 60.2 supplies their exact additional prices. A correct next-step subtree has fee at least one plus their maximum; emitting this word and their respective optimal tail policies attains that maximum. These branches use the remembered original $v$, not their new scalar values in $F_v$.

Stopping, starting zero, starting one with a later zero, and the all-one word exhaust all first choices, including choices in arbitrary adaptive subtrees. A nonconstant root-pair archive cannot stop for free. Each possible first choice supplies one of the listed candidates no greater than its actual fee, while the stated constructions attain the least candidate. Their minimum is consequently exact, and an empty list precludes a finite controller. ∎

**引理 60.5（The one pair and the later singleton departures）。** Along the successful zero-difference path of all-one words from the original root, the actual phase supports are

$$
U_0=P,\qquad U_q=P\setminus\{0,m,2m,\ldots,qm\}
\quad(1\le q\le D).
\tag{60.7}
$$

At index zero the positive successful child is the pair priced by $\chi_v$. At index $1\le t<D$, its positive child on this path is the singleton $j=(t+1)m$, at paid depth $t+1$ and original height $h_{t+1}$, priced by $\eta_v((t+1)m,t+1)$. Its rejection archive is the whole rectangle $U_t\times[h_t-m,h_t)$.

**证明。** The actual all-one charge is $\{tm,(t+1)m\}$. At the root both endpoints are present. A zero root response removes both. At each later index the leading endpoint $tm$ was already removed, while $(t+1)m$ has not been removed. No wrap or repetition occurs because every indicated endpoint is at most $Dm\le k-1<T$. Induction gives the supports and singleton departures. The height and rejection statements follow from adding $m$ to each actual tail $s+tm$. Every displayed phase and tail is a joint actual source by (1.3), and the observed prefix is exactly its own successful all-one archive. ∎

## 61. Actual first-zero arrivals and a fully priced recorded-zero spine

The $K$ used below is the supplied availability-code minimum of Definition 27.1, on physical INITIAL indices and actual chronological offset:

$$
K(A,\lambda;b)=\min\left\{d\in\{0,\ldots,T-1\}:\begin{array}{l}
\exists z_j\in\mathbb F_2^d\ (j\in A),\quad z_j[i]=0\text{ if }j\notin W_{b+i},\\
\lambda(j)\ne\lambda(l)\Longrightarrow z_j\ne z_l
\end{array}\right\}.
\tag{61.1}
$$

It is zero for empty or homogeneous supports. On every support used below its finite range is justified by the safe phase-recovery stream of [S1, Theorem 3.1]. This is a finite code-assignment predicate, not an unknown adaptive continuation fee. The coprime literal constructions of Theorems 27.2 and 27.4 are supplied results; D11's noncoprime realization is not used here.

**引理 61.1（Checking the first-zero positive-child interface）。** At an actual pre-zero rectangle $U\times[0,h)$ at depth $q$, issue a word $B$ containing its first zero after $r<m$ leading ones, with terminal run $\rho$. A correct continuation from a nonconstant rectangle necessarily has $r<h$, and

$$
\begin{aligned}
&F_v\text{ constant on }U\times[h-r,h),\\
&F_v(j,s)=F_v(j,0)\qquad(j\in U,\ 0\le s<h-r).
\end{aligned}
\tag{61.2}
$$

Put $b=q+1$, $\lambda(j)=F_v(j,0)$, and let $E_q(B)$ be the charge support from (1.4). Its actual positive child is $A=U\cap E_q(B)$, with common tail $\rho$ and INITIAL tails $[0,h-r)$ at every retained phase. Under (61.2), its additional adaptive and child-local preset fees both equal $K(A,\lambda;b)$. Its zero child $Z=U\setminus E_q(B)$ is an actual archive of Definition 27.1. These assertions also hold when $q=0$.

**证明。** Literal tail updates reject exactly $s\ge h-r$ before the parent's first zero. If $r\ge h$, all candidates enter one absorbing archive, which cannot complete a nonconstant rectangle. For $r<h$, each fixed-phase surviving fibre merges at that zero before the next permitted observation. Thus the two conditions (61.2) are forced by irreversible equality of records and archives, as in [S1, Lemma 4.3; S15, Definition 4.1 and Proposition 4.2]. They are not consequences of mere legality of $B$ or attainability of the original target. The remaining bits have length less than $m<k$ after a zero and cannot reject. Every surviving original history ends at $(z_q\oplus e,-j+bm,\rho)$ in its own difference-$e$ child. The label at that child is well-defined precisely because the corresponding surviving fibres are constant.

For the positive child, $A\subseteq W_q$ and $\rho\le m-1\le k-m$. If $|A|\le m$, it now meets every hypothesis of Definition 27.1 and Theorem 27.2: its own issued parent supplies the recorded zero, its depth is $b\ge1$, all candidates share the acquired archive and current value and tail, the original label is $\lambda$, and its actual offset is $b$. The supplied one-hole construction therefore gives the claimed exact price.

The remaining possibility is $A=W_q$, with all $m+1$ physical vertices. Even full-path charge forces $m$ odd. Inverse (1.5) forces $B=101\cdots01$, hence $\rho=1$. In fact this first-zero case has $q=0$: for $q\ge1$ the preceding all-one difference either excludes $qm$ from $U$, or confines $U$ to its two charge endpoints, so $U$ cannot contain $W_q$. The parent did not previously record a zero, so Theorem 27.3's parent hypothesis is not asserted. Instead the supplied proof of Theorem 27.4 applies through its actual construction data: support $W_q$, offset $q+1$, and tail one. Here is the complete check of that transfer. Successful-path code extraction, padded by zeros after a homogeneous leaf, gives $K$ as a lower bound; equal padded codes at unequal labels would force identical actions and stopping through the earlier leaf. Safe phase recovery gives $K\le T-1$. Relative to the physical start $qm$, its next $d\le T-1$ windows start at $nm\pmod T$, $1\le n\le d$, and none equals $W_q$ by coprimality. The only one-hole windows relative to $W_q$ start at $1$ or $-1$ in these proof coordinates, as checked in Theorem 27.4; their chronological neighbours have at least two holes because consecutive windows share only one vertex and $m\ge3$.

On a two-hole row the supplied component inverse produces a word containing zero. On a one-hole row the inverse is unique. If it is all ones, its response on $W_q$ marks one phase $h_*$ alone. Set that phase's later code coordinates to zero and stop it at this identifying endpoint; unequal-label separations remain valid. Such all-one rows are isolated. They follow a tail at most $m-1$, or the initial tail one, giving a seam at most $2m-1<k$. Their following row can start zero: after the start-$1$ window its leading vertex is outside $W_q$; after the start-$(-1)$ window it is the just identified phase whose later code is zero. In either case that following window has another hole for even-charge compensation, so (1.5) realizes the whole prescribed row with its leading zero. It clears the long tail inside the already-counted next block. All other seams are at most $2m-2<k$, and the initial seam is at most $m<k$. A last all-one word needs no clearing after a stop. These are exactly the supplied literal code changes and inverses, on the fixed actual $A$; no holes or responses are borrowed from a sibling. They construct one stream of length $K$ on this first-zero child and prove the reverse inequality. Rotation was only notation in this proof, with no physical phase change or free wait.

For either size case, a least nonconstant code price is an attained actual maximum: if all sources could stop earlier, successful-path extraction would give a shorter separating code. Constant and empty children have price zero, and empty children are never executed. The zero child has the same recorded parent zero, depth, common tail and surviving-fibre labels, so it meets Definition 27.1 irrespective of its size. This proves the entire arrival interface. ∎

**定义 61.2（A literal spine with numerical side prices）。** Start at an actual recorded-zero archive $(b,S,\sigma,\lambda)$ of Definition 27.1. Choose a finite sequence of whole words $B_b,\ldots,B_{L-1}$, $L\ge b$. Set $S_b=S$, $\sigma_b=\sigma$. At every issued index $t$, require $S_t$ nonempty and $\lambda|_{S_t}$ nonconstant. Let $\alpha(B)$ be the leading run, taking value $m$ for the all-one word, and $\rho(B)$ its terminal run. Require

$$
\begin{aligned}
&\sigma_t+\alpha(B_t)<k,\qquad
A_t=S_t\cap E_t(B_t),\qquad S_{t+1}=S_t\setminus E_t(B_t),\\
&\sigma_{t+1}=\begin{cases}
\rho(B_t),&B_t\text{ contains zero},\\
\sigma_t+m,&B_t=1^m.
\end{cases}
\end{aligned}
\tag{61.3}
$$

Require $\lambda|_{S_L}$ constant, with empty support allowed. The absolute price of this certificate is

$$
\Pi=\max\left(\{L\}\cup
\{t+1+K(A_t,\lambda|_{A_t};t+1):b\le t<L,\ A_t\ne\varnothing\}\right).
\tag{61.4}
$$

An empty sequence at a homogeneous or empty support has $\Pi=b$. The certificate contains one chronological zero-difference path. Every side price is the finite predicate (61.1), with its own actual offset; it contains no adaptive subtree or continuation oracle.

**命题 61.3（Exact charged spine certificate, consuming the supplied offspring laws）。** On every actual archive just specified,

$$
D_{\rm ad}(b,S,\sigma,\lambda)
=\min_{\text{certificates of Definition 61.2}}(\Pi-b).
\tag{61.5}
$$

For nonempty starting support, each certificate has a lawful attaining policy with worst actual absolute depth exactly $\Pi$.

**证明。** At a nonconstant common-tail archive a rejecting word rejects every candidate. Its absorbing endpoint cannot resolve different INITIAL labels, so every correct next action is safe. Induction with (1.4) and the literal tail update proves that (61.3) gives the exact acquired zero child and its actual positive sibling. The recorded zero remains in this same issued history. Each retained phase continues an actual original witness; its INITIAL label is unchanged.

For each nonconstant positive sibling, Theorem 27.3 gives tail at most $k-m$ and at most $m$ phases, or precisely the odd-width full window at tail one. In its all-one case, the proof uses the actual immediately preceding endpoint: a positive incoming tail means its preceding word ended one. A preceding zero difference excludes the common endpoint; a preceding positive difference confines the support to the preceding window, which excludes the new far endpoint because $T\ge2m+1$. Thus a nonconstant two-endpoint all-one child must have incoming tail zero. There is a preceding block because the archive already recorded an issued zero. All supplier hypotheses are therefore actual, including the tail bound, and Theorems 27.2 and 27.4 give exactly (61.1), with their literal optimal streams. Homogeneous siblings stop. This is reuse of those acquired-child laws, not a new fee assertion about unrelated supports or high tails.

Execute the written spine until its first positive difference, then run that sibling's supplied least-code construction and decode its own endpoints. On the final zero support return its homogeneous label. All actions are complete paid words; (61.3) checks their strict seams. Every nonempty $A_t$ has an actual source reaching it and an attaining continuation. If $S_L$ is nonempty, an actual source traverses all $L-b$ spine words. If it is empty and $L>b$, the last nonempty $S_{L-1}$ went entirely to the last positive child, so a source still pays that last word. Hence (61.4), including waits, padding and clearing inside the side words, is the exact maximum. The empty-sequence case is immediate.

Conversely stop homogeneous archives immediately in any finite correct continuation and retain its own zero-difference path. Its words are safe as just proved. Every first-positive subtree has the supplied all-action lower bound $K$ on that actual child. Replacing it by its fixed attaining stream yields a certificate whose maximum is no greater than the original controller's maximum. This establishes both inequalities in (61.5). Finiteness and attainment use $T-1$ successive $01\,0^{m-2}$ words from the starting offset. Their leading zero makes every seam safe. Over $T$ chronological positions each phase's endpoint-difference cycle has exactly two ones; equality of its first $T-1$ entries forces equality of the last by that integer count, and then equality of the phases by the period $T$ and coprimality. This is the supplied safe phase-recovery construction. Restricting it to $S$ decodes every label. A finite minimum over integer fees is attained, and the preceding replacement produces an attaining certificate. Different siblings may use different streams; (61.5) is an adaptive statement. ∎

## 62. The arbitrary INITIAL adaptive structural minimum

**定义 62.1（A fully priced candidate from the free INITIAL reading）。** Fix $v$. Choose $q\in\{0,\ldots,D\}$. Along the principal path of $q$ successful zero-difference all-one words, require for every $0\le t<q$

$$
F_v\text{ nonconstant on }U_t\times[0,h_t),\qquad
F_v\text{ constant on }U_t\times[h_t-m,h_t).
\tag{62.1}
$$

Put

$$
\Delta_v(q)=\max\left(
\{q\}\cup\{1+\chi_v:q>0\}\cup
\{t+1+\eta_v((t+1)m,t+1):1\le t<q\}
\right).
\tag{62.2}
$$

For $q=0$ the extra sets are empty and $\Delta_v(0)=0$. Infinite side price excludes the candidate. This is a maximum of absolute branch depths, not a sum of sibling costs. The $q$ term already includes all prior rejection depths.

A **pre-zero stop** is allowed if $F_v$ is constant on $U_q\times[0,h_q)$. Its candidate fee is $\Delta_v(q)$.

Otherwise choose any whole word $B_q$ containing zero, with leading run $r<h_q$, and require (61.2) on $U=U_q$, $h=h_q$. Put

$$
\lambda_v(j)=F_v(j,0),\quad A=U_q\cap E_q(B_q),\quad
Z=U_q\setminus E_q(B_q),\quad b=q+1,\quad\rho=\rho(B_q).
\tag{62.3}
$$

Choose a certificate of Definition 61.2 from its actual zero child $(b,Z,\rho,\lambda_v|_Z)$, with price $\Pi$. Its complete **first-zero candidate** fee is

$$
M=\max\{\Delta_v(q),\ b,\ b+K(A,\lambda_v|_A;b),\ \Pi\}.
\tag{62.4}
$$

For empty $Z$ use the empty certificate with $\Pi=b$. Empty $A$ has $K=0$ and is not run. A nonempty parent rejection band returns its common original label at depth $b$; an empty band supplies no observed branch.

Let $\mathcal C_v$ contain all these candidate fees at most $T$. Thus all chosen spines have $L\le T$, and every priced side completion ends by $T$. This is a finite specification: tail-table comparisons, the bounded pre-zero index, one actual first-zero word, one sequence of at most $T-b$ literal words, and the finite availability assignments (61.1).

**定理 62.2（Complete adaptive law on the guarded coprime slice）。** For every arbitrary immutable INITIAL record target $f:Q\to Y$ under (60.1), for both original alphabets,

$$
\boxed{\displaystyle
C_{\rm ad}(f)=\max\left\{\min\mathcal C_0,\min\mathcal C_1\right\},
\qquad\min\varnothing=+\infty.}
\tag{62.5}
$$

Every finite minimum has a lawful policy attaining exactly this worst ACTUAL emitted-complete-block fee. The equality includes arbitrary tail partitions, labels, all original phases and both values, independent initial bottom, early stops and impossible targets. It is an exact reader-specific finite structural minimum, without a scalar closed-form or efficient-enumeration claim.

**证明（literal attainment）。** Select a finite candidate on one initial value fibre. Issue the selected $q$ all-one words while the observed differences remain zero. At every rejection stop with the band label of (62.1). On the positive root endpoint use the least entry's literal policy from Theorem 60.4. On a later positive endpoint use Lemma 60.2 at its actual singleton phase and paid depth. Lemma 60.5 proves that these are the actual archives and original-tail rectangles reached by those words. These policies include their own rejecting and successful endpoints and every further word; their exact prices give (62.2).

If the candidate is a pre-zero stop, the terminal rectangle has its stated homogeneous label. The phase set $U_q$ is nonempty: for $q\ge1$ its size is $T-q-1$, and $q\le D<T-1$. Every original tail-zero witness at these phases survives the all-one prefix. Thus a source really reaches depth $q$, while the side minima are also attained on nonempty actual archives. The maximum $\Delta_v(q)$ is exactly the worst emitted depth.

For a first-zero candidate, issue its actual $B_q$. The surviving original tails satisfy $s+qm+r<k$, reach its first zero, and then finish safely with common terminal tail $\rho$. Its own successful endpoint difference is exactly (1.4); no rejection is treated as a binary charge. Conditions (61.2) preserve all original labels on both the rejected band and the merged successful fibres. Lemma 61.1 verifies the positive child's hypotheses and supplies its least-code literal stream. Proposition 61.3 supplies the selected zero-child spine and each of its priced side streams. Decode only the source's observed endpoints and return the surviving fibre's INITIAL label. All phase movements, even on a wrap or return, are the actual displacements $tm$ of these issued words.

The parent is reached on a nonconstant nonempty rectangle, and $r<h_q$ leaves actual tail-zero survivors. Every nonempty success child and every nonempty rejected band has actual witnesses reaching its endpoint. The previous side prices and all the selected child prices have attained actual maxima. Together with the paid parent, their maximum is precisely (62.4). The $0^m$ waits, inverse-word padding, isolated-pulse waits and any seam-clearing bits inside the supplied code constructions all belong to issued paid blocks. No cleanup is added after a lawful stop and no word is counted on a source already stopped. This constructs every candidate under either original alphabet.

**证明（all-action lower bound and completeness）。** Take any finite correct controller on this free-value fibre and stop every homogeneous archive immediately. Before its first issued zero, every word is $1^m$. Follow its successful zero-difference path. The exact rectangles and supports are (60.2) and (60.7). At every such word the entire rejected top-$m$ rectangle shares one bottom archive, so it must be homogeneous. Its principal archive is nonconstant while it continues. The positive root child has the all-action lower bound $\chi_v$; every later positive child has the all-action lower bound $\eta_v$ at the actual offset of Lemma 60.5. Consequently (62.1) holds and $\Delta_v(q)$ does not exceed the original maximum on the retained prefix and its departing branches.

No nonconstant successful path can issue more than $D$ all-one words. At $q=D$ the next one rejects all remaining tails because $0<h_D\le m$, and cannot complete a nonconstant archive. The retained zero path must therefore stop on a homogeneous rectangle or choose an actual first-zero parent at some $q\le D$. In the stopping case it supplies a pre-zero-stop candidate. In the other case its leading run must be below $h_q$, and the two label-preservation conditions (61.2) are necessary by the actual merger proof, not postulated from target attainability. All possible literal first-zero words remain among the choices of Definition 62.1.

After this parent its positive child's exact lower bound is $K$ by Lemma 61.1, including the alternating full-window case. From its actual zero child follow the original controller's zero-difference path. Proposition 61.3 replaces every first-positive subtree by its literal least-code continuation and gives a certificate of price no greater than the original subtree's absolute maximum. Replace the pre-zero side branches as well by the exact policies of Lemma 60.2 and Theorem 60.4. Their all-action lower bounds ensure that the resulting complete candidate costs no more than the original controller. No replacement changes a sibling's original archive or asks it to share another sibling's stream.

It remains to justify the finite cutoff in $\mathcal C_v$. The supplied adaptive horizon, Theorem 51.4, applies: (60.1) implies $2\le m<k$, coprimality, the full joint prior (1.3), the same endpoint-only observation and alphabet contract, and the same immutable record target. Its hypothesis is adaptive finiteness alone. For a single fibre, extend its given table by a constant target on the other free-value fibre and any independent bottom label. A finite policy on the original fibre and immediate stops on the others give adaptive finiteness of that extension. Theorem 51.4 then bounds this fibre's finite optimum by $T$. An optimal finite controller exists because its possible finite worst fees are nonnegative integers. Extract the preceding candidate from an optimal controller of fee at most $T$; all its priced branch depths and its spine length are at most $T$, so it belongs to $\mathcal C_v$.

Thus a nonempty candidate set supplies a controller, and a finite controller supplies a member with fee no greater than its optimum; the two inequalities give equality on this fibre. If the set is empty but a finite controller existed, the same horizon and extraction would produce a member, a contradiction. This proves infinity, without changing a target or relying on preset finiteness.

Finally the free initial scalar value selects its own optimal fibre policy. The two minima combine by their maximum, with no equality required between their labels. Independent initial bottom returns its own label for free. If both successful fibres are homogeneous, each contains the zero candidate even when their labels and the bottom label are all different. If either candidate set is empty, no finite correct full controller exists. This proves (62.5). ∎

## 63. Effective selection, source-faithful examples and limitations

**命题 63.1（Finite evaluation and literal control data）。** For a decidable finite partition of the $2kT+1$ INITIAL records, (62.5) is effectively evaluable and a least candidate supplies an optimal literal adaptive policy. For an arbitrary label set it remains a semantic minimum and existence result, without assuming decidable label equality.

**证明。** Every constancy in (60.3), (60.4), (60.6), (61.2) and (62.1) is a comparison in the given finite partition. For (61.1) enumerate $d\le T-1$ and each phase's binary vectors with their prescribed unavailable zeros, allowing different codes for equal labels. These are finite lists, not adaptive trees. For each $q\le D$ enumerate the $2^m-1$ possible first-zero parents, checking their actual leading run and both label conditions. Enumerate the single spine up to absolute index $T$, computing its physical charge support by (1.4), safety and actual tail by (61.3), and side prices by (61.1). Keep the finite fees at most $T$ and select a least one, or detect emptiness.

The witnesses in (60.4) and (60.6) give all pre-zero side words. For each least code assignment, the row inversion, one-hole coordinate complement and isolated all-one repair in the supplied Chapter 27 constructions give its whole literal child stream, including its valid stopping decoder. The chosen spine retains its displayed whole words. At execution the remembered initial value, actual block count and source's own chronological endpoint archive select these stored words and labels. No adaptive cost oracle is invoked online or offline. No polynomial search bound is asserted. Without decidable label equality these same finite conditions still define the mathematical minimum, as in [S1, Note 5.3]. ∎

**例 63.2（A tail-dependent root pair actually completed by one more word）。** Let $m\ge3$ be odd and $k=2m+1$, so $\gcd(m,k+1)=1$. Choose labels $A,B,C,R$ with $A\ne B$ and $A\ne R$. On each free-value fibre put, for $j=0,m$, the label $A$ or $B$, respectively, when $s<m$, and label $R$ when $s\ge m$. At every other phase put $C$ when $s<m+1$ and $R$ when $s\ge m+1$. Give initial bottom any label. This full target has exact adaptive fee two.

Indeed, at phase zero the original tails $m-1$ and $m$ have unequal labels and both survive every root first-zero word: its leading run is at most $m-1$, so $m+(m-1)<k$. Such a word merges them; stopping also fails. Thus the root is $1^m$. It rejects exactly $s\ge m+1$, all with label $R$. Its positive child is the actual pair $\{0,m\}$ of height $m+1$, with the top single tail $m$ labelled $R$ and each lower fibre labelled $A$ or $B$. The third row of (60.6), with $r=1$, is realized by the next complete word $10^{m-1}$: its bottom endpoint returns $R$, and its two successful responses separate phases zero and $m$, returning $A,B$. The root's successful zero child has only label $C$ and stops at fee one. An actual pair source pays two blocks, and unequal labels on the pair rule out fee one. This example uses the new pre-zero tail connection; it does not restrict the arbitrary-target quantifier in (62.5).

**边界 63.3（Legal actions that lose the original target）。** The label checks in (61.2) remain essential even for a target attainable by another policy. For the supplied obstruction at $k=6,m=3$, a target with label zero for $s<3$ and one for $s\ge3$ is acquired by root $111$. The legal alternative root $101$ keeps original tails two and three alive at phase zero, gives both positive difference one, and puts both at the identical current record with tail one. Their original labels differ, so that child has infinite additional fee, rather than a finite phase-table $K$ price. Conditions (61.2) exclude this parent. The obstruction is credited to the first-zero merger interface; it is not an exception to (62.5) or a replacement of the INITIAL label by the label at tail zero.

## 64. Consumed sources and the original remaining quantifiers

**数学引文 64.1（Overlap and the added cost connection）。** The immutable integrated source through Chapter 59 supplies the original experiment, the full joint witnesses (1.3), the path charges and inverse, the endpoint-return mechanism, the acquired-price constructions of Chapter 27, and the sufficient adaptive horizon of Chapter 51. The fixed [S1, Definitions 1.2–2.1, Convention 1.3, Lemmas 4.2–4.3, Theorems 3.1 and 5.2, Note 5.3] supplies the INITIAL and first-zero semantics and attainability interface. [S2, Theorem 14.1] supplies the matched coefficients. [S10, Interface 2.1] and [S15, Sections 1–4] supply literal physical responses, component inversion, strict seams and actual-parent correspondence. These are ordinary supplied mathematics, and their definitions and hypotheses are instantiated above rather than replaced by an abstract game. D11's Definitions 2.3 and 3.1 provide the list convention, while its $g\ge2$ realization theorem remains outside the coprime domain used here.

The acquired-small-support and full-window streams, their phase-recovery bound and their zero-spine replacement are credited reuse of Theorems 27.2–27.5. Lemma 61.1 verifies their first-zero arrival hypotheses, including the actual full-window geometry without claiming an already-zeroed parent. The added cost content is the arbitrary-tail price (60.4), the exhaustive root-pair minimum (60.6), their exact pre-zero departures, and the all-action, finite and impossible composition (62.5). Chapters 51 and 54 supplied a sufficient horizon and left this individual adaptive-fee connection open. Chapters 55–59 supply a different width-two law, whose $m=2$ clauses are not asserted as proofs for $m\ge3$.

The single-source INITIAL-identification and irreversible-merger comparisons with Moore and van den Bos–Vaandrager in Mathematical Citation 7.2 retain their stated scope. They supply neither these physical tail bands nor the root-pair price. No exhaustive literature-absence, originality, independent-prior or model-diversity claim is made.

**范围 64.2（Exact scope and unresolved objectives）。** Equation (62.5) resolves the exact adaptive structural minimum for every arbitrary immutable INITIAL record target on $m\ge3$, $k\ge2m$, $\gcd(m,k+1)=1$, including finite and impossible cases under both original alphabets. The full-history pullback is literal: every specified original $(v,-j,s)$ has the single legal complete-block witness (1.3), the operations thereafter are (1.2), its windows use its actual issued count, and its decoder consumes only its own endpoints. Unknown initial history lengths, original tails and INITIAL values are never replaced by a favourable phase convention or a terminal-state label. Every reached whole block is paid.

The original all-parameter objective remains broader. In particular this result does not cover the coprime strip $m<k<2m$, does not replace the supplied width-one, width-two, noncoprime, wide or critical results, and does not give the exact GLOBAL-preset fee on this slice. The minimum chooses different continuations on different actual children and on the two free-value fibres. A single GLOBAL preset stream must independently satisfy their simultaneous literal rows, seams, rejection and stopping contracts; taking the maximum of their separately optimal continuation prices does not prove that compatibility. The original remaining parameter regions and this GLOBAL compatibility remain unresolved here. A scalar closed form for every label table and a sharp supremum of finite fees are also separate from the finite structural minimum. All statements in these chapters are ordinary mathematical proofs, with no Lean/kernel, build, axiom-closure or novelty certification.

## 追加锚（本行以下为增补区）

## 65. The zero/one-block boundary of actual critical-narrow positive children

**定义 65.1（Actual common-tail child and its two continuation prices）。** Retain the original weights, matched scalar, joint actual-history prior, immutable INITIAL record target $f:Q\to Y$, free initial scalar or independent bottom, endpoint-only observations, and complete-block fee of Chapter 1. In Chapters 65–67 assume

$$
3\le m<k<2m,\qquad T=k+1,\qquad \gcd(m,T)=1,\qquad h=k-m.
\tag{65.1}
$$

Thus $P=\mathbb Z/T\mathbb Z$ and $1\le h\le m-2$: the omitted endpoint $h=m-1$ would give $T=2m$ and nontrivial gcd. Both original alphabets contain exactly the same $2^m$ words, while cross-block rejection remains an actual operation.

Fix either free INITIAL value and any actual chronological archive whose emitted block $B$ at absolute issued index $a\ge0$ has a successful positive-difference child. Write $b=a+1$ and retain that child's entire acquired archive, support $A$ of INITIAL indices $j=-\theta_{\rm INITIAL}$, common current value, and common actual tail $\sigma<k$. Require that the retained INITIAL label is one well-defined function $\lambda:A\to Y$: every surviving INITIAL record at a given $j$ has that same label. All candidates are original histories sharing this very archive. The parent may have mixed tails and may be the first issued-zero parent; no earlier recorded zero, low inherited tail, tail-independent full target, distinct labels at distinct phases, or condition on another child or value fibre is required. Well-defined $\lambda$ is a substantive hypothesis, not a consequence of the parent's legality. The first-zero merger conditions of [S1, Lemma 4.3 and Theorem 5.2; S15, Definition 4.1 and Proposition 4.2] must still hold whenever this child is used in a correct full INITIAL controller.

Use the actual ordered windows $W_t=[tm,(t+1)m]\pmod T$ of Interface 1.4. Positivity gives $A\subseteq W_a$ and charge one on every $j\in A$. At the child, the current phase is $-j+bm\pmod T$. Let $D_{\rm ad}$ be its minimum additional worst-branch fee over adaptive continuations. Let $D_{\rm child\text{-}pre}$ restrict the continuation to a single preset literal stream selected for this particular acquired child, with stopping and decoding based on its own endpoints. It has no GLOBAL compatibility requirement with siblings or the other free-value fibre. Every further emitted block, including uninformative clearing and waits, is paid; a homogeneous archive may stop at its current endpoint. Empty supports have fee zero as vacuous composition entries. Label equality is semantic; effective selection requires a finite partition presentation or decidable equality, as in [S1, Note 5.3].

Define the one-coordinate availability condition and the exceptional family by

$$
\mathsf Q_1:\quad |\lambda[A]|\le2\quad\text{and}\quad
\lambda\text{ is constant on }A\setminus W_b,
\tag{65.2}
$$

with empty-set constancy true, and

$$
\begin{aligned}
\mathsf E:\quad &k=m+1,\quad m\text{ odd},\quad A=W_a,\\
&H=\{bm,(b+1)m\}\pmod T,\quad
\exists L\ne M:\quad
\lambda(j)=\begin{cases}L,&j\in H,\\M,&j\in A\setminus H.\end{cases}
\end{aligned}
\tag{65.3}
$$

Here $H\subset A$ has two vertices. The path inverse and strict seam criterion used below are the credited interfaces (1.4)–(1.5), [S10, Interface 2.1] and [S15, Definitions 1.1 and 2.1]. The general residual one-block safe-cut certificate is [S13, Theorem 8.4]; its arbitrary-support condition is not itself the positive-child classification below. The constructions of Chapter 27 and the fee laws of Chapters 60–64 require $k\ge2m$ and are not continuation laws under (65.1).

**定理 65.2（Exhaustive shallow boundary and exact paid exception）。** For every actual child of Definition 65.1, under both original alphabets,

$$
D_{\rm ad}=D_{\rm child\text{-}pre}=0
\quad\Longleftrightarrow\quad
A=\varnothing\ \text{or}\ \lambda\text{ is constant}.
\tag{65.4}
$$

For nonconstant $\lambda$,

$$
D_{\rm ad}\le1
\quad\Longleftrightarrow\quad
D_{\rm child\text{-}pre}\le1
\quad\Longleftrightarrow\quad
\mathsf Q_1\ \text{and not}\ \mathsf E,
\tag{65.5}
$$

and these prices are exactly one. In $\mathsf E$ the actual parent is forced to be $101\cdots01$, its child tail is $\sigma=1$, and

$$
D_{\rm ad}=D_{\rm child\text{-}pre}=2,
\qquad\text{attained from index }b\text{ by }0^m\mid110^{m-2}.
\tag{65.6}
$$

For every other nonconstant case failing (65.5), each continuation price is between two and $T-1$, inclusive. No equality of the two prices at general higher depths is asserted.

**证明（necessity and the separating row）。** At fee zero there is no further observation: all candidates have the same acquired archive, so a correct stop exists precisely for a constant INITIAL label. This gives (65.4), including the empty convention.

At a common-tail child every fixed next word either succeeds on all candidates or rejects all of them: since $m<k$, rejection depends only on $\sigma$ and the word's leading run. Rejection creates one absorbing archive and cannot finish a nonconstant target, at this endpoint or after later actions. A successful endpoint has only the binary difference $q$; outside $W_b$ it is zero by (1.4). Thus any one-block completion forces $\mathsf Q_1$. Adaptive and child-preset depth one have the same single next word.

For nonconstant $\mathsf Q_1$ there are exactly two labels. If $A\setminus W_b$ is nonempty, prescribe $q=0$ to its common label and $q=1$ to the other label. If it is empty either label orientation is allowed. A one-block completion exists exactly when such a separating row has a safe literal realization. These binary-row constraints also occur in the credited safe-cut interface; here they follow from the preceding common-tail argument without assuming an earlier issued zero. The remaining proof exhausts them using the actual positive parent.

**证明（zero-containing parents and the only unsafe row）。** Put $u=am\pmod T$ solely as a coordinate translation of this archive, so $W_a=u+\{0,\ldots,m\}$ and the next path starts at $u+m$. No emitted block, phase displacement or observation is supplied by this notation. Local vertices $1,\ldots,h$ of $W_b$ are outside $W_a$, hence outside $A$.

Write the next word's bits as $x_0,\ldots,x_{m-1}$, and pin $x_{-1}=x_m=0$. At local vertex $i$ its charge equation is $x_{i-1}\oplus x_i=q_i$. A missing vertex deletes this equation. Between two deleted equations the bit component has a freely chosen orientation; a component reaching a pinned endpoint has its orientation fixed. These are the supplied signed-path components [S15, Definition 2.1], applied to the holes of this same $A$.

Suppose first that $B$ contains a zero. Its child's actual tail is $\sigma=\rho(B)\le m-1$, irrespective of mixed tails before $B$. If $h\ge2$, missing vertices 1 and 2 isolate $x_1$ as a free component. Set $x_1=0$. All remaining prescribed charges can be solved component by component: no observed equation joins the two pinned endpoints, and no observed equation joins this free bit across either deleted edge. The resulting word has leading run at most one. Its seam obeys $\sigma+\alpha\le m<k$, so it safely realizes every prescribed separating row.

Let $h=1$. Vertex 1 is always missing. If vertex 0 is also missing, set $x_0=0$ and use the missing vertex 1 to compensate full-path parity; the inverse then solves all other prescribed charges. Otherwise, if any additional vertex is missing, choose the first such vertex $j>1$. The component $x_1,\ldots,x_{j-1}$ is free between the deleted equations 1 and $j$; orient it with $x_1=0$, and solve the other components. Again the leading run is at most one and the same strict safe seam holds.

The only remaining hole pattern has exactly the single missing local vertex 1. Here $T=m+2$, and the actual two windows satisfy

$$
W_b\setminus W_a=\{u+m+1\},\qquad
W_a\setminus W_b=\{u+m-1\}.
\tag{65.7}
$$

Consequently $A$ contains all of $W_a\cap W_b$ and, since $A\subseteq W_a$, is either that intersection or all of $W_a$. In the intersection case all phases of $A$ are available. Choose the label orientation giving charge zero at the leading vertex of $W_b$. The single hole fixes the remaining full-path parity, giving the unique inverse with $x_0=0$, safe from every inherited tail.

If $A=W_a$, the parent charges one at all $m+1$ vertices. Its even full-path charge forces $m$ odd, and (1.5) forces $B=101\cdots01$, with $\sigma=1$. The outside phase $u+m-1$ fixes the zero-label orientation. For that row the one-hole inverse is unique. Every inverse containing zero has $\alpha\le m-1$, hence $1+\alpha\le m<k$. The only unsafe inverse can therefore be $1^m$: its actual leading seam is $1+m=k$.

The charge of this all-one inverse on $A$ is one exactly at

$$
H=\{u+m,u+2m\}=\{u+m,u+m-2\}\pmod{m+2}.
\tag{65.8}
$$

It separates the labels exactly when one label class is $H$ and the other is $A\setminus H$, namely $\mathsf E$. Conversely that label table forces this unique unsafe row: the unavailable phase $u+m-1$ belongs to the complementary class and fixes its response to zero. This exhausts every $\mathsf Q_1$ obstruction for zero-containing parents, with arbitrary repeated labels and every absolute offset retained.

**证明（all-one parents, the paid repair and finite bounds）。** The remaining parent is $B=1^m$, whose positive support is contained in $\{u,u+m\}$. A nonconstant child therefore contains both endpoints with different labels. Its common current tail may exceed $m-1$; no low-tail assertion is used. At the next actual index emit

$$
0^{h+1}1\,0^{m-h-2}.
\tag{65.9}
$$

This is a complete $m$-bit word because $h\le m-2$. Its isolated one at local position $h+1$ has physical charge $\{u,u+1\}$, selecting exactly $u$ from the child's two endpoints. It begins zero, so it is safe from every $\sigma<k$. This proves that no all-one-parent child adds another exception. Together with the preceding cases, it establishes all one-block attainments in (65.5).

In $\mathsf E$, any successful separating one-block action must realize the forced row and hence must be $1^m$, which rejects every candidate from the actual tail one. Every other successful word fails to separate the two labels; every rejecting word merges them. Thus no one-block adaptive action works, an all-action lower bound of two rather than a failure of one chosen protocol.

For attainment, issue the whole paid word $0^m$ at index $b$. Its difference is zero on all candidates and its actual tail becomes zero; it does not identify either label. At index $b+1$, the path starts at $u+2m=u+m-2\pmod{m+2}$. The whole word $110^{m-2}$ has charge exactly $\{u+m-2,u+m\}=H$. Its leading run two is strictly below $k=m+1$ from tail zero, and its terminal tail is zero. Its endpoint difference returns $L$ on one and $M$ on zero. Both complete blocks, including the uninformative clearing block, are emitted and paid. This proves (65.6).

Finally apply the supplied safe phase-recovery stream of [S1, Theorem 3.1], starting at this actual offset: repeat $010^{m-2}$ for $T-1$ complete blocks. Every word begins zero, so every candidate is safe. Its $T$ chronological samples traverse the matched coefficient cycle by coprimality. Equality of two phases' first $T-1$ differences forces the last differences equal by the common integer total of two ones; equality of the whole shifted cycle then forces equal phases by its exact period $T$ [S2, Theorem 14.1]. Recovering the current phase and subtracting the known paid displacement gives INITIAL $j$ and hence $\lambda(j)$. This is credited reuse of a finite upper bound, not a new phase-recovery theorem. Failure of (65.5) and (65.4) gives the lower bound two; the safe stream gives each upper bound $T-1$. It supplies no further equality between adaptive and child-preset minima. ∎

## 66. A full INITIAL consumer of the paid obstruction

**定理 66.1（An attained infinite family with a strict availability surcharge）。** For every odd $m\ge3$, put $k=m+1$ and $T=m+2$, so $\gcd(m,T)=1$. Choose pairwise distinct labels $L,M,C,R$. On both free-value fibres define the entire INITIAL target by

$$
f_m(v,-j,s)=
\begin{cases}
R,&s=m,\\
L,&s<m,\ j\in\{m-2,m\},\\
M,&s<m,\ j\in\{0,\ldots,m\}\setminus\{m-2,m\},\\
C,&s<m,\ j=m+1,
\end{cases}
\qquad f_m(\bot)=L_\bot,
\tag{66.1}
$$

where $L_\bot$ is arbitrary and independent. The actual root $101\cdots01$ has positive child $A=W_0$ with tail one and the exceptional table $\mathsf E$. This child's additional adaptive and child-preset fees are exactly two, although its availability-code minimum $K(A,\lambda;1)$ of Definition 27.1 is one. That definition is used solely as a combinatorial code predicate; Chapter 27's guarded fee laws are not applied. The single literal stream

$$
101\cdots01\mid0^m\mid110^{m-2}
\tag{66.2}
$$

is a GLOBAL preset controller for the full target, shared by both free-value fibres, with actual worst fee three. Consequently $C_{\rm ad}(f_m)\le C_{\rm pre}(f_m)\le3$. No full-target lower bound three for every odd $m$ is included in this statement.

**证明。** The alternating root has leading run one, so it rejects exactly INITIAL tail $s=m$, labelled $R$. Every surviving fixed-phase INITIAL fibre $s=0,\ldots,m-1$ has one label in (66.1), so its actual first-zero merger preserves that label. The rejected band is also homogeneous. These are the actual INITIAL-fibre conditions from [S1, Lemma 4.3; S15, Proposition 4.2], not merely an internal legality check.

The root's full path charge is one on $W_0=\{0,\ldots,m\}$. Its positive child therefore has exactly that support, common tail one, and $L$ class $\{m-2,m\}=\{m,2m\}\pmod T$. The zero child is phase $m+1$, labelled $C$, and stops at its first endpoint. Rejection stops there with $R$. The positive child is $\mathsf E$, so Theorem 65.2 gives the exact additional fee two and the last two words of (66.2).

For its availability predicate the next window is $W_1$, and its only unavailable phase in $A$ is $m-1$, of label $M$. Assign the one-bit code one to $L$ and zero to $M$. The $L$ phases are both available; all unavailable entries are zero; different labels have different codes. Thus $K\le1$, and nonconstancy gives $K\ne0$. The strict surcharge $D_{\rm ad}=D_{\rm child\text{-}pre}=K+1=2$ is attained on an actual child of this full INITIAL target, rather than on an unrelated support or an unacquired favourable tail.

All source records used here have the single joint history (1.3): for the desired $(v,-j,s)$ choose $\ell\equiv0\pmod m$, $\ell\equiv-j\pmod T$, $\ell\ge s+2$ and $d=\bigoplus_{i=\ell-s}^{\ell-1}c_i$, and use $(v\oplus d)0^{\ell-s-1}1^s$. Coprimality supplies such $\ell$. This one legal word has exactly the prescribed value, phase and actual tail together and splits into complete source blocks under either alphabet. Appending (66.2) to that word gives precisely the root rejection or its own successful difference archive just calculated. INITIAL labels never change with the tail updates. An all-one complete-block history of length at least $k$ separately realizes initial bottom, which is freely observed and stops with $L_\bot$.

The root rejects only its stated band; the surviving root seam satisfies $s+1\le m<k$. The clearing word begins zero. The final word begins with two ones from tail zero, below $k=m+1$, and all later bits are zero. Only the positive child continues beyond the first endpoint. On it both labels occur on actual histories and require the third endpoint; those histories emit all three paid words, including the clearing block. On the final difference one return $L$, and on zero return $M$. Successive endpoint differences of each source's own outputs implement the same decoder on both INITIAL values. This proves the GLOBAL attainment and its actual maximum three, without a general minimization claim for the entire infinite family. ∎

## 67. A sharp whole-INITIAL adaptive and GLOBAL witness

**定理 67.1（The consumed $k=4,m=3$ full-source optimum）。** Take $k=4,m=3,T=5$ and pairwise distinct $A,B,C,R$. On both free-value fibres put

$$
f(v,-j,s)=
\begin{cases}
R,&s=3,\\
A,&s=0,1,2,\ j=1,3,\\
B,&s=0,1,2,\ j=0,2,\\
C,&s=0,1,2,\ j=4,
\end{cases}
\qquad f(\bot)=L_\bot,
\tag{67.1}
$$

with arbitrary independent $L_\bot$. Under either original alphabet the exact minimum whole-target fees are

$$
\boxed{C_{\rm ad}(f)=C_{\rm pre}(f)=3.}
\tag{67.2}
$$

The GLOBAL stream is $101\mid000\mid110$, with endpoint stopping; the lower bound excludes every depth-two adaptive controller on either free-value fibre.

**证明（all-action INITIAL lower bound）。** Fix either free initial value $v$. The target on its complete INITIAL fibre is nonconstant, so a fee-zero stop is impossible. The joint sources in (1.3), used in Theorem 66.1, realize every record compared below on one original history with the specified value, phase and tail.

Any root beginning zero merges, at each fixed phase, the actual INITIAL tails two and three. Both survive that zero and the remaining at most two bits; their current records and all acquired endpoint outputs are identical, while their INITIAL labels are the phase label $A$, $B$ or $C$ and the distinct $R$. Deterministic future actions and stops then remain identical. Such a root cannot occur in any correct controller, regardless of its later depth.

Any root with at least two leading ones, including $111$, sends both a tail-two source and a tail-three source at a fixed phase to absorbing rejection. Their labels are again distinct. Their rejection times within the block are unobserved, and the endpoint is the same bottom, so later actions cannot repair the loss. These roots also cannot occur in any correct controller. The only remaining length-three roots are $100$ and $101$. This exhausts all eight literal actions in both alphabets, without a favourable-root restriction.

After $100$, rejection identifies $R$. Its successful charge support is $\{0,1\}$, so its zero-difference child contains precisely phases $2,3,4$, with labels $B,A,C$ and common current tail zero. It is nonconstant and cannot stop at that endpoint. Any next word either rejects this whole common-tail child or gives at most two successful scalar endpoints. Neither possibility separates its three distinct INITIAL labels in one more block. Thus this root cannot support a correct controller of worst fee at most two.

After $101$, rejection identifies $R$, its zero-difference child identifies $C$, and its positive child has phases $0,1,2,3$ with labels $B,A,B,A$ and actual tail one. This is the $m=3$ exception of Theorem 65.2. Explicitly its next ordered window is $3,4,0,1$. Unavailable phase two has label $B$ and forces response zero for $B$; hence a separating word must have charges one at phase three, zero at phase zero, and one at phase one. The literal path equations are

$$
x_0=1,\qquad x_1\oplus x_2=0,\qquad x_2=1.
\tag{67.3}
$$

They force $x_0=x_1=x_2=1$; the missing phase four supplies no alternative word. This forced $111$ rejects every candidate because its seam is $1+3=4=k$. Every other word either fails the required label split or rejects uniformly. Therefore this root also cannot support fee two.

Every root and its relevant next action has been included. The argument holds separately for each free INITIAL value; using different adaptive policies on the two fibres does not avoid either lower bound. It uses actual shared archives and absorbing rejection, rather than a lower bound on only the displayed stream. Thus $C_{\rm ad}(f)\ge3$, and $C_{\rm pre}(f)\ge3$ because a GLOBAL preset controller is an adaptive controller.

**证明（one GLOBAL stream and lawful stopping）。** Apply Theorem 66.1 with $m=3$, $L=A$ and $M=B$. It supplies the full INITIAL target (67.1), the same literal stream $101\mid000\mid110$ on both free values, and its jointly realized source histories. At the first endpoint return $R$ on bottom and $C$ on zero difference. Only the positive child continues; its tail one is cleared by the whole paid $000$, whose difference is zero. The third actual window starts at $2m=1\pmod5$. The word $110$ has charge $\{1,3\}$, so its difference one returns $A$ and difference zero returns $B$.

Each surviving root seam has $s+1\le3<4$; clearing starts zero; the final leading run two starts from tail zero and is below four. The last endpoint is legal, so no subsequent cleanup is issued or charged. Both $A$ and $B$ histories exist and emit all three complete words. Already stopped $R$, $C$ and initial-bottom histories emit no later words. This gives a correct one-GLOBAL-stream preset controller of worst actual fee three. Combined with the all-action adaptive lower bound it proves (67.2). ∎

**定义 67.2（Quantified boundary of these conclusions）。** Theorem 65.2 is universal over actual common-tail positive children and their arbitrary well-defined INITIAL label tables under (65.1). It does not supply a continuation law for mixed-tail children, zero-difference children, arbitrary unrelated acquired supports, or exact higher-depth prices. Theorem 66.1 supplies actual full INITIAL consumers and a common-stream upper bound three; Theorem 67.1 alone adds its whole-target matching lower bound. Neither statement identifies an optimum for every full INITIAL target in the critical-narrow sector or a common optimal GLOBAL stream across arbitrary siblings and both free-value fibres. The full original objective of Definition 1.3 and Open Problem 9.1, over every attainable immutable INITIAL target and every original $k\ge2,m\ge1$, remains distinct from these restricted exact conclusions. The supplied guarded results retain their own hypotheses. Mathematical source reuse is that of Definition 65.1 and the corresponding proof steps; the single-trajectory identification conventions in Mathematical Citation 7.2 supply no additional reader-specific fee formula.

## 追加锚（本行以下为增补区）

