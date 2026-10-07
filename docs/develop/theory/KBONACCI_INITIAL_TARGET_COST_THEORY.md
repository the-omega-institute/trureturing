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
