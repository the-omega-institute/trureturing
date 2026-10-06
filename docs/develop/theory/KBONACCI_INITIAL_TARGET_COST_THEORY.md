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

