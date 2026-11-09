# KBonacci two-omission positive children: same-budget preset continuation

## 93. Actual children, immutable labels and the chronological two-omission geometry

**定义 93.1（The guarded original reader）。** Retain the original integer-weight matched reader and joint complete-history source convention of [IC, Chapter 1], with

$$
m\ge3,\qquad k=m+2,\qquad T=k+1=m+3,\qquad \gcd(m,T)=1.
\tag{93.1}
$$

The guard is equivalently $3\nmid m$; in particular $m\ne3$ and hence $m\ge4$. The initial record space is

$$
Q=\bigl(\mathbb F_2\times\mathbb Z/T\mathbb Z\times\{0,\ldots,k-1\}\bigr)
\sqcup\{\bot\}.
\tag{93.2}
$$

Fix a finite nonempty label set $Y$ and any immutable INITIAL target $f:Q\to Y$. Each successful triple is supported by its own jointly realizing complete legal history, whose length is hidden. All such histories are retained, rather than replacing their joint law by a product of marginal possibilities. The free INITIAL observation is the scalar $v\in\mathbb F_2$ or the separate absorbing output $\bot$. The label $f(\bot)$ is arbitrary and independent of all successful-record labels.

For clarity, the matched coefficient and literal updates are exactly those of [IC, Definition 1.1]:

$$
c_\theta=\mathbf1_{\{0,T-1\}}(\theta),\qquad
\begin{aligned}
0:\ (v,\theta,s)&\longmapsto(v,\theta+1,0),\\
1:\ (v,\theta,s)&\longmapsto
\begin{cases}
(v\oplus c_\theta,\theta+1,s+1),&s+1<k,\\
\bot,&s+1=k.
\end{cases}
\end{aligned}
\tag{93.3}
$$

Bottom is absorbing under either bit. A complete action emits $m$ bits and observes only its final scalar or bottom. The two original alphabets are

$$
\mathcal A_{\rm all}=\{0,1\}^m,\qquad
\mathcal A_{\rm loc}=\{B\in\{0,1\}^m:B\text{ avoids }1^k\text{ internally}\}.
\tag{93.4}
$$

They contain the same words here because $m<k$. This equality does not remove rejection across successive words. Each issued complete word costs one, including waits, clearing, padding, duplicates and a rejecting word with its entire emitted suffix. Only the controller's own chronological complete endpoints are available; there is no reset, copy, intermediate observation, free clock or borrowed sibling archive.

**定义 93.2（A retained actual positive child）。** Fix either successful free INITIAL value and one actual chronological archive. Let $B^{\rm par}$ be its actually issued parent word at absolute index $a\ge0$, and let $H$ be its successful positive-difference child in the sense of [IC, Definition 65.1]. Thus $H$ consists of all original histories sharing this very acquired archive, including the same issued words and observed endpoints through index $a$. Write

$$
A=\{-\theta_{\rm INITIAL}(w):w\in H\}\subseteq\mathbb Z/T\mathbb Z.
\tag{93.5}
$$

The current scalar $v_H$ and the true current tail $\tau<k$ are common to all histories in $H$. Require a well-defined immutable phase-label law

$$
f(q_{\rm INITIAL}(w))=\lambda(j)
\quad\text{for every }w\in H,\quad j=-\theta_{\rm INITIAL}(w)\in A.
\tag{93.6}
$$

Different phases may have the same label. Every retained history at a fixed phase must have that phase's label; neither a representative history nor a new label of the evolved record replaces (93.6).

At absolute issued index $t$ the ordered physical charge window is $[tm,(t+1)m]\pmod T$. Positivity of the parent means that its charge is one on every phase in $A$, so

$$
A\subseteq\{j:q_{a,B^{\rm par}}(j)=1\}\subseteq[am,(a+1)m]\pmod T.
\tag{93.7}
$$

This includes arbitrary placements of $A$ inside the actual positive support. The parent can contain the first issued zero, can have mixed incoming tails, or can follow an earlier archive with no recorded zero. If it is all ones, its common outgoing tail is still its true inherited tail, not an imposed low tail. No parity, density, number of labels or earlier-zero hypothesis is added to this child contract. The prior and earlier archive are those of [IC, Chapter 1 and Definition 65.1], with the true-tail interface of [FP, Definition 90.1].

**定义 93.3（Two kinds of additional-budget existence）。** For a finite integer $d\ge0$, let $\mathsf{Ad}(H,d)$ mean that there exists a correct adaptive continuation on $H$ with worst additional emitted-block fee at most $d$. Its next complete word may depend on its own acquired endpoint archive, and its stopping and decoding use that same archive. Let $\mathsf{Pre}(H,d)$ impose the further restriction that all histories in this particular $H$ follow prefixes of one literal suffix selected once for $H$; stopping and decoding may still depend on the endpoints acquired along those prefixes.

Correctness returns the original label (93.6) for every history in $H$. Empty children may stop vacuously, and homogeneous children may stop at the acquired endpoint. The entire earlier prefix remains paid; it is excluded only from this additional fee. A suffix chosen for another positive child or another free-value fibre need not agree with this suffix. An initially observed bottom returns its independent label without issuing a word.

For notation in the proof, translate phase indices by $u=am$ and write the translated label map again as $\lambda$. This changes no history, phase, issued index or action. The parent window becomes $W_0=\{0,\ldots,m\}$, while suffix slot $i$ is still the actual issued index $a+i$, and

$$
\begin{aligned}
W_i&=[im,im+m]\pmod T=[-3i,-3i+m]\pmod T,\\
M_i&=(\mathbb Z/T\mathbb Z)\setminus W_i
     =\{-3i-2,-3i-1\}\pmod T,\qquad i\ge1.
\end{aligned}
\tag{93.8}
$$

The support now denoted by $A$ lies in $W_0$. A further translation used to describe two adjacent windows below is also notation only. The chronology in (93.8) is the two-omission identity of [FP, (84.3)]; its use here does not impose the whole-target label tables or the $m\ge7$ restriction of that chapter.

## 94. Same-budget existence by minimum-one-count seam normalization

**定理 94.1（Every actual two-omission positive child, at every finite budget）。** For every guarded reader (93.1), every finite nonempty $Y$, every immutable INITIAL target $f:Q\to Y$, either original alphabet, either free successful INITIAL value, every actual child $H$ of Definition 93.2, and every finite integer $d\ge0$,

$$
\boxed{\mathsf{Ad}(H,d)\quad\Longleftrightarrow\quad\mathsf{Pre}(H,d).}
\tag{94.1}
$$

The suffix in $\mathsf{Pre}(H,d)$ is selected for this acquired child and its entire retained history set. The assertion concerns existence at the same budget. It imposes neither unchanged realization of an arbitrary prescribed row list nor one common GLOBAL stream across different children or free-value fibres.

**证明（zero fee and the all-one parent）。** If $A$ is empty or $\lambda$ is constant, stop at the acquired endpoint. Both existence assertions hold at every $d\ge0$. Conversely a nonconstant child cannot finish at additional fee zero: every retained history has the same acquired archive and no new observation is made.

Suppose $B^{\rm par}=1^m$. The credited charge derivative [IC, Interface 1.4] gives positive support only at the two endpoints of the parent window. In the translated coordinates a nonconstant child therefore has $A=\{0,m\}$ and different labels at those two phases. At the next actual slot emit

$$
0001\,0^{m-4}.
\tag{94.2}
$$

It has exactly $m$ bits. Its isolated one is at local bit position $3$ in the path starting at $m$, so its charge support is $\{0,1\}\pmod T$. It selects phase $0$ and not phase $m$. The leading zero makes it successful from every true incoming tail $\tau<k$, and its completed endpoint distinguishes the two labels. This is the $k-m=2$ instance of the all-one-parent completion in [IC, Theorem 65.2, (65.9)]. It costs one complete block and needs no observation between its bits.

No replacement of the parent's true outgoing tail has been made. If its incoming tail was $s$, success of $1^m$ gives outgoing tail $s+m$, as in [FP, Definition 90.1]; the word (94.2) works from that very tail. Thus for this nonconstant case both assertions in (94.1) hold precisely when $d\ge1$.

It remains to treat a zero-containing parent. Its successful execution clears every incoming tail at its first zero, so its true outgoing tail is

$$
\sigma=\rho(B^{\rm par})\le m-1.
\tag{94.3}
$$

Here $\rho$ denotes the literal trailing one-run length. This transfer is valid even for mixed tails before the parent and when that zero was the first issued zero. In the rest of the proof the child is nonconstant and satisfies (94.3).

**证明（the availability device and extraction from arbitrary adaptive actions）。** A length-$h$ availability code is a function

$$
C:A\longrightarrow\mathbb F_2^h
\quad\text{such that}\quad
\begin{cases}
C_i(j)=0&\text{if }j\notin W_i,\\
C(j)\ne C(j')&\text{if }\lambda(j)\ne\lambda(j'),
\end{cases}
\qquad 1\le i\le h.
\tag{94.4}
$$

Codes at equally labelled phases may differ. Write $K$ for the least such length; the short-horizon argument below proves that it is finite. This is the combinatorial availability definition in [IC, Definition 27.1], used without the $k\ge2m$ physical-realization hypotheses of that chapter.

Suppose a correct adaptive continuation has worst additional fee at most $d$. Stop any homogeneous node immediately. At each remaining node the current tail is common: it was common at $H$, and a fixed successful word transfers equal tails to equal tails. Since $m<k$, rejection depends only on that tail and the word's leading run. Hence any rejection at this node would be uniform. It would put every remaining label into the same absorbing endpoint archive and could never resolve a nonconstant node. All continuing words are therefore successful.

For each $j\in A$, record its successive scalar differences under this adaptive continuation, padding zeros after its own stopping endpoint to length $d$. All histories at that phase follow the same continuation: their current scalar, phase and tail at $H$ coincide, and the subsequent operations are deterministic. At relative depth $i$ their action, although archive-dependent, is a word at the actual index $a+i$. Its charge vanishes outside $W_i$, so the padded code satisfies the first clause of (94.4).

If two padded vectors agree, follow the two histories until the earlier of their stops. Equal earlier differences and the common scalar at $H$ give equal own endpoint archives inductively, and therefore the same adaptive actions. At that earlier stop the stopping rule and returned label are identical. Unequal immutable labels are consequently impossible. The second clause of (94.4) follows, and

$$
K\le d.
\tag{94.5}
$$

This is successful-path extraction with endpoint stopping and zero padding, as in [IC, Theorem 27.2, extraction direction; FP, proof of Theorem 91.4]. It requires no assumption that independently chosen rows can already be executed together. Every word of the original adaptive continuation, including an uninformative word, was counted in $d$.

**证明（a short horizon and every indexed Hall inequality）。** Since $3\nmid T$, write

$$
R=
\begin{cases}
r,&T=3r+1,\\
r+1,&T=3r+2.
\end{cases}
\tag{94.6}
$$

In both cases $R\ge2$ and $R<T$. The omitted sets $M_i\cap W_0$, $1\le i\le R$, are disjoint; their last member has one vertex and their earlier members have two. The following literal residue equations verify all these assertions and the position of the earlier pairs. For $T=3r+1$,

$$
\begin{aligned}
M_i&=\{3(r-i)-1,\,3(r-i)\}\subset W_0&& (1\le i<r),\\
M_r&=\{m+2,0\},\qquad M_r\cap W_0=\{0\}.
\end{aligned}
\tag{94.7}
$$

For $T=3r+2$,

$$
\begin{aligned}
M_i&=\{3(r-i),\,3(r-i)+1\}\subset W_0&& (1\le i\le r),\\
M_{r+1}&=\{m,m+1\},\qquad M_{r+1}\cap W_0=\{m\}.
\end{aligned}
\tag{94.8}
$$

In particular the total number of restricted phases of $W_0$ is $2R-1$. A phase belongs to at most one omitted pair in this horizon.

Index lists by the actual phases $j\in A$, not by the labels. Its allowed length-$R$ list is

$$
L_j=\{z\in\mathbb F_2^R:z_i=0\text{ whenever }j\in M_i\}.
\tag{94.9}
$$

Each $L_j$ is either the full cube or one coordinate-zero half cube. There are at most two phase indices of each restricted type, and at most $2R-1$ restricted phase indices altogether.

First assume $R\ge3$. The elementary bounds needed here are

$$
|A|\le m+1\le3R-1\le2^R,\qquad
2^{R-1}\ge2,\qquad 3\cdot2^{R-2}\ge2R-1.
\tag{94.10}
$$

The two exponential inequalities start at $R=3$, where $3R-1=8$ and $3\cdot2^{R-2}=6\ge5$. Increasing $R$ by one doubles their left-hand sides while increasing the corresponding linear expressions by $3$ and $2$, respectively, so they persist. The bound on $m+1$ follows directly from the two cases of (94.6).

For every finite set $S\subseteq A$ of phase indices, check the Hall inequality as follows. If $S$ is empty, both cardinalities are zero. If it contains a full-list phase, its list union is the full cube, whose size $2^R$ is at least $|A|$, hence at least $|S|$. If it is nonempty and has just one restricted type, then $|S|\le2$ and its union has size $2^{R-1}$. If it has at least two restricted types and no full list, two different coordinate-zero half cubes already have union size

$$
2^{R-1}+2^{R-1}-2^{R-2}=3\cdot2^{R-2}.
\tag{94.11}
$$

This is at least $2R-1$, and every index in $S$ is one of those at most $2R-1$ restricted phases. Additional types only enlarge the union. Thus every subfamily, including repeated equal lists belonging to different phase indices, satisfies the required inequality.

The only possibility $R=2$ under (93.1) is $m=4$, $T=7$. Here $W_0$ has five vertices. The parent's full path charge has even cardinality by the credited derivative, so its charge-one support has at most four vertices. Since this is an actual positive child,

$$
|A|\le4.
\tag{94.12}
$$

The omitted intersections are $\{2,3\}$ and $\{0\}$. There are at most three restricted phase indices in total and at most two of either type. A subfamily containing a full list has union size $4\ge|A|$. A nonempty subfamily of one restricted type has at most two indices and union size two. A subfamily of both restricted types has at most three indices and union size three. The empty inequality again holds. This proves all Hall inequalities also at this exceptional horizon.

Apply the finite indexed-list Hall theorem [H, declaration $\texttt{Finset.all\_card\_le\_biUnion\_card\_iff\_existsInjective'}$] to (94.9). Its finite index set is $A$ and its finite universe is the binary $R$-cube, which has decidable equality. The verified union inequalities give distinct representatives for all phase indices. They are a phase-injective availability code and therefore separate unequal labels even when labels repeat. Consequently

$$
1\le K\le R.
\tag{94.13}
$$

The lower bound uses the nonconstancy assumed in this part of the proof. Hall is used exactly as an existing finite selection theorem; the horizon and its actual-phase list bounds have just been proved for this child.

**证明（formal separating lists and a finite minimum）。** Put $h=K$. Choose a length-$h$ code in (94.4). For $1\le i\le h$, the actual window $W_i$ differs from $W_0$: equality of these proper consecutive arcs would give $im=0\pmod T$, contrary to coprimality and $1\le i\le R<T$. Two different arcs of the same length cannot contain one another, so $W_i\setminus W_0$ is nonempty. In particular $W_i$ has a vertex outside $A$.

Prescribe full charge $C_i(j)$ at the vertices $j\in A\cap W_i$. Set other charges to zero except at one chosen vertex of $W_i\setminus A$, where the value is selected to make the full charge even. The credited even-row inverse [IC, (1.5); FP, (84.5)] supplies one literal word in that window. On $A\setminus W_i$ its charge is zero, just as (94.4) requires.

This establishes nonemptiness of the finite class $\mathcal F_h$ of all $h$-word lists whose formal charge vectors separate every pair of unequal labels on $A$. Here “formal” means the arithmetic charge of a word, whether or not a concatenation would be safe to execute. No safety constraint is imposed in $\mathcal F_h$. Its finiteness follows from the finite set of width-$m$ words at each of its $h$ fixed actual slots.

Choose a member $(B_1,\ldots,B_h)$ minimizing the total literal one-count

$$
\mathcal N(B_1,\ldots,B_h)
=\sum_{i=1}^h\sum_{\ell=0}^{m-1}(B_i)_\ell.
\tag{94.14}
$$

Every summand is a literal bit, interpreted as $0$ or $1$ in the integer sum. This is a minimum over the formal separating class, not over lists already assumed physically executable. The next arguments establish safety for this minimizing member.

The charge identities used throughout these modifications are the existing derivative and unique inverse: in a window starting at $v$, a word $x_0,\ldots,x_{m-1}$ has charges $x_0$ at $v$, $x_{\ell-1}\oplus x_\ell$ at $v+\ell$ for $1\le\ell<m$, and $x_{m-1}$ at $v+m$. They vanish outside that window. In particular, toggling one literal bit toggles exactly the charges at the two vertices joined by its literal edge. These are [IC, Interface 1.4] and the mathematical declarations $\texttt{WindowChargeInverse.increment\_derivative}$ and $\texttt{WindowChargeInverse.short\_window\_charge\_inverse}$ in [D].

**证明（the exterior edge and the first actual seam）。** The vertices $m+1,m+2$ are outside $W_0$, hence outside $A$. For every slot $i<R$, (94.7)–(94.8) put both omitted vertices inside $W_0$. Thus the literal edge

$$
(m+1,m+2)
\tag{94.15}
$$

is present in that slot's ordered window. It joins two exterior vertices, so toggling its bit changes no charge on $A$. Were that bit one in a minimizing list, changing it to zero would preserve every formal code on $A$ and strictly lower (94.14). It is therefore zero.

At the first suffix slot the window starts at $m$. The edge (94.15) is its bit at local position $1$, so

$$
(B_1)_1=0,\qquad \alpha(B_1)\le1.
\tag{94.16}
$$

This also applies if $h=1$, because $R\ge2$. More generally every predecessor $B_i$ of another suffix word has $i<h\le R$ and hence $i<R$; it contains this exterior-edge zero. From the true child tail (94.3), the incoming seam of the first word obeys

$$
\sigma+\alpha(B_1)\le m<m+2=k.
\tag{94.17}
$$

Nothing has been emitted to establish (94.15)–(94.17). They describe literal bits already selected in the minimizing list.

**证明（the decreasing shear when a predecessor has at least three terminal ones）。** Consider adjacent words $P=B_i$ and $Q=B_{i+1}$ in this minimizing member. The predecessor contains zero. Set

$$
r=\rho(P)\le m-1,\qquad \alpha=\alpha(Q).
\tag{94.18}
$$

Suppose, towards a contradiction, that their literal seam is unsafe:

$$
r+\alpha\ge m+2.
\tag{94.19}
$$

Since $\alpha\le m$, we have $r\ge2$; since $r\le m-1$, we have $\alpha\ge3$. Translate coordinates by the start of $P$ solely to display these adjacent windows. Their ordered paths are

$$
W_P=[0,1,\ldots,m],\qquad
W_Q=[m,m+1,m+2,0,1,\ldots,m-3].
\tag{94.20}
$$

Write $p_0,\ldots,p_{m-1}$ for $P$'s bits. First let $r\ge3$. Its final $r$ bits are one, so its charges at $m-2,m-1$ vanish. Those are exactly the two vertices of $W_P$ absent from $W_Q$. Therefore its entire even full charge row $q_P$ is supported on $W_Q$, and the full row $q_Q\oplus q_P$ is a legitimate even row in $Q$'s actual window.

The inverse of $q_P$ in that destination window is the literal toggle word $D$ given by

$$
D_\ell=
\begin{cases}
1,&0\le\ell\le2,\\
1\oplus p_{\ell-3},&3\le\ell<m.
\end{cases}
\tag{94.21}
$$

Indeed, the first charge encountered in (94.20) is $q_P(m)=1$ and the next two charges are zero. Subsequent cumulative sums are $1\oplus p_0,1\oplus p_1,\ldots,1\oplus p_{m-4}$ by the original derivative. At the destination endpoint $m-3$, its last bit agrees with $q_P(m-3)$ because $p_{m-3}=1$. Thus (94.21) also satisfies the terminal charge equation, not only the internal equations.

Replace $Q$ by $Q'=Q\oplus D$. Its full charge is $q_Q\oplus q_P$. On every phase in $A$, the two affected code coordinates change by

$$
(C_i,C_{i+1})\longmapsto(C_i,C_{i+1}\oplus C_i).
\tag{94.22}
$$

This is an invertible binary coordinate shear; applying it twice is the identity. All unequal-label separations are preserved on the entire $A$, regardless of its placement and repeated labels.

Because $p_t=1$ for $t\ge m-r$, (94.21) gives

$$
D_\ell=0\quad\text{for }\ell\ge m-r+3,\qquad
\alpha\ge m+2-r.
\tag{94.23}
$$

Hence at most one nonzero toggle lies outside the leading $\alpha$ one-bits of $Q$. The first three toggles lie inside that run and remove three ones. Every other toggle inside it also removes a one; the possible single toggle outside it adds at most one. Therefore

$$
|Q'|_1-|Q|_1\le-3+1=-2.
\tag{94.24}
$$

The modified list is still in $\mathcal F_h$ by (94.22), but has smaller total one-count. Other seams of the modified list need not remain safe, since safety was never a condition defining $\mathcal F_h$. This contradicts the minimum.

**证明（the other decreasing shear, when the terminal run is two）。** The remaining case of (94.19) is $r=2$. It forces $\alpha=m$ and therefore $Q=1^m$. Its full charge row has exactly the two endpoints

$$
\operatorname{supp}(q_Q)=\{m,m-3\},
\tag{94.25}
$$

both in $P$'s actual window. Add this row to $P$'s row, leaving $Q$ fixed. The inverse of (94.25) in $W_P$ toggles just the last three bits:

$$
E_\ell=
\begin{cases}
0,&0\le\ell<m-3,\\
1,&m-3\le\ell<m.
\end{cases}
\tag{94.26}
$$

Here $m\ge4$, so all displayed indices are literal positions of the width-$m$ word. Since $P$ has trailing run exactly two, its last three bits are $011$. The replacement $P'=P\oplus E$ changes them to $100$ and gives

$$
|P'|_1-|P|_1=-1.
\tag{94.27}
$$

Its row is $q_P\oplus q_Q$. The affected code coordinates now undergo the other invertible shear

$$
(C_i,C_{i+1})\longmapsto(C_i\oplus C_{i+1},C_{i+1}).
\tag{94.28}
$$

Thus this modified list also lies in the same formal separating class and strictly decreases (94.14), again a contradiction. The two cases exhaust (94.19). Every adjacent seam of the original minimizing member consequently satisfies

$$
\rho(B_i)+\alpha(B_{i+1})<m+2=k,\qquad 1\le i<h.
\tag{94.29}
$$

This is the seam-normalization relation needed here: one formal separating list of the minimum availability length has a representative with all the required strict seams. It was obtained by minimizing over formal lists and using the two different supported row additions. It is not an assertion that a prescribed code or its rows survive these modifications unchanged.

**证明（actual strict-seam induction and the budget conclusion）。** Start from every actual history in the original child, with its common scalar and true incoming tail $\sigma$. Equation (94.17) and $m<k$ make the first complete word successful. If $h>1$, that word contains zero, so its true outgoing tail is exactly its literal trailing run. Inductively, before $B_{i+1}$ the predecessor $B_i$ has completed successfully and contains zero, because $i<h\le R$. Its true outgoing tail is therefore $\rho(B_i)$, and (94.29) makes $B_{i+1}$ successful. This uses the true-tail transfer in [FP, Definition 90.1], also expressed by $\texttt{InternalZeroSafety.internal\_zero\_execution}$ in [Z]. The transfer for a zero-containing word is invoked only after its incoming seam has been checked.

The last word can be all ones. Its incoming seam has already been verified; its true outgoing tail is then its incoming tail plus $m$, with no substitution of the literal value $m$. No further action is required, so no clearing or final cleanup is inserted or left unpaid. Each word is in both original alphabets.

All actual sources now produce the formal charge vector of their own phase as the successive completed scalar differences. Those vectors separate unequal values of $\lambda$ by membership in $\mathcal F_h$. They therefore decode the immutable INITIAL label (93.6), even when distinct vectors represent the same label. The controller can issue the entire selected list and stop at its final endpoint; optional earlier homogeneous stops only shorten actual prefixes.

This is one child-preset suffix of exactly $h=K$ paid complete words, issued at the actual indices $a+1,\ldots,a+h$. There were no additional waits, clearing, displacement or padding actions. In particular, whenever $\mathsf{Ad}(H,d)$ holds, (94.5) yields $h\le d$ and hence $\mathsf{Pre}(H,d)$. All original histories sharing $H$ were covered simultaneously, and the earlier paid prefix was preserved.

Conversely a child-preset continuation is an adaptive continuation whose word choices ignore the new endpoint values. Thus $\mathsf{Pre}(H,d)$ implies $\mathsf{Ad}(H,d)$. Together with the empty, homogeneous and all-one-parent cases, this proves (94.1) for every finite $d$.

The argument is local to a child of Definition 93.2. The indexed Hall theorem, the literal derivative and inverse, adaptive extraction, the high-tail two-endpoint completion and the true-tail transfer have been used in their stated domains. The minimum-one-count argument (94.14)–(94.29) supplies the additional safe representative at $k=m+2$. The full-positive $k=m+1$ results [FP, Chapters 73 and 92], the exterior-edge realization for $k\ge m+3$ [FP, Definition 91.1 and Theorem 91.4], and the fixed whole-target families [FP, Chapters 84–85] retain their respective hypotheses; none is a substitute for that argument.

No claim here identifies a sharp full-target fee, supplies GLOBAL compatibility across unrelated archives, realizes every availability row list unchanged, or extends (94.1) to arbitrary $k$. The finite availability minimum was an internal proof device for selecting this child's suffix. The result leaves the all-parameter whole-INITIAL objective of [IC, Definition 1.3 and Open Problem 9.1] in its original scope. $\square$

The mathematical citations attached to Definitions 93.1–93.3 and Theorem 94.1 use the two owning manuscripts and the derivative and tail declarations at repository revision $1f74e23eefcba4f6df990efe1ed5578554655e64$. The indexed Hall supplier is at mathlib revision $db584cd6d46c92f209a44c0f1c829460d327499d$. The charge and tail declarations are cited as the existing mathematical interfaces, with their short-word and incoming-safety hypotheses; their conditional suffix interfaces do not by themselves prove (94.29).

[IC]: https://github.com/the-omega-institute/trureturing/blob/1f74e23eefcba4f6df990efe1ed5578554655e64/docs/develop/theory/KBONACCI_INITIAL_TARGET_COST_THEORY.md
[FP]: https://github.com/the-omega-institute/trureturing/blob/1f74e23eefcba4f6df990efe1ed5578554655e64/docs/develop/theory/KBONACCI_FULL_POSITIVE_WINDOW_LOGARITHMIC_PRICE.md
[H]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Combinatorics/Hall/Finite.lean
[D]: https://github.com/the-omega-institute/trureturing/blob/1f74e23eefcba4f6df990efe1ed5578554655e64/D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.lean
[Z]: https://github.com/the-omega-institute/trureturing/blob/1f74e23eefcba4f6df990efe1ed5578554655e64/D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InternalZeroSafety.lean

## 追加锚（本行以下为增补区）
