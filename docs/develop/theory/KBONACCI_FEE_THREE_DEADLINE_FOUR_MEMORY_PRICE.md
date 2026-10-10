# KBonacci fee-three targets at the four-block memory deadline

This volume determines the complete stationary GLOBAL control-memory minimum when a target of [the original owner][OWN] (Definition 3.1) has optimal GLOBAL block fee three and is allowed four blocks. The target, source prior, observations, literal actions and memory convention are those of that owner. The new mathematical content is an exhaustion of four-word-row competitors at this slack deadline. The original bounds, physical interfaces and attaining controllers are reused.

## 1. The complete source and control contract

**Definition 1.1 (Parameters and immutable target).** Assume

$$
3\le m<k\le2m-2,\qquad T=k+1,\quad
 g=\gcd(m,T),\quad P=g\mathbb Z/T\mathbb Z,
$$
$$
h=k-m,\qquad a=2m\pmod T=m-h-1,\qquad
J=P\setminus\{0,m\},\qquad W_t=[tm,(t+1)m]\pmod T.
$$

The brackets denote the ordered full physical path, including its endpoints. Put $H=J\setminus W_1$ and $O=J\setminus W_2$. Take literal label tables $\lambda_0,\lambda_1:J\to Y$, each with exactly two labels, such that

$$
\Lambda(j)=(\lambda_0(j),\lambda_1(j)),\qquad
|\Lambda[J]|=3,\qquad \Lambda\text{ is constant on }H,
\qquad |\Lambda[O]|\le2.
\tag{1.1}
$$

Constancy on an empty set is allowed. Distinct labels $R,C$ are fresh from both lower-table images. The initial-bottom label $L_\bot$ is arbitrary, including every equality with an existing output. On the whole original source set

$$
Q=\{\bot\}\sqcup\{(v,-j,s):v\in\mathbb F_2,\ j\in P,\ 0\le s<k\}
$$

retain precisely the target

$$
f(v,-j,s)=
\begin{cases}
R,&s\ge h,\\
C,&s<h,\ j\in\{0,m\},\\
\lambda_v(j),&s<h,\ j\in J,
\end{cases}
\qquad f(\bot)=L_\bot.
\tag{1.2}
$$

Write

$$
U_Y=\lambda_0[J]\cup\lambda_1[J],\quad r=|U_Y|\in\{2,3,4\},
\qquad N=|f(Q)|=r+2+\mathbf1_{\{L_\bot\notin U_Y\cup\{R,C\}\}}.
\tag{1.3}
$$

No equality pattern between the two lower tables is excluded. In particular $r$ is not the number of joined classes.

**Source bridge 1.2 (Whole histories and total literal updates).** These are jointly actual records, not a product of marginal reachability sets. The credited supplier [IC, Chapter 1] uses

$$
G_i=2^i\ (i<k),\qquad G_i=\sum_{b=1}^kG_{i-b}\ (i\ge k),
\qquad c_i=G_i\bmod2=\mathbf1_{\{0,T-1\}}(i\bmod T).
$$

For every displayed $v,j,s$, choose an integer $\ell$ with

$$
\ell\equiv0\pmod m,\qquad \ell\equiv-j\pmod T,\qquad \ell\ge s+2,
\qquad d=\bigoplus_{i=\ell-s}^{\ell-1}c_i.
$$

Then $(v\oplus d)0^{\ell-s-1}1^s$ is one legal complete-block history with value $v$, phase $-j$ and tail $s$. Generalized CRT applies because $g\mid j$. An all-one complete-block history of length at least $k$ realizes bottom. History length is not observed or supplied to the controller. Thus (1.2) factors the target through the entire original INITIAL record and assigns every original source its immutable label.

For a successful current record, the original total bit updates are

$$
\delta_0(v,\theta,s)=(v,\theta+1,0),\qquad
\delta_1(v,\theta,s)=
\begin{cases}(v\oplus c_\theta,\theta+1,s+1),&s+1<k,\\
\bot,&s+1=k,
\end{cases}
\qquad \delta_b(\bot)=\bot.
\tag{1.4}
$$

A word means these updates composed for all its $m$ bits. Only its completed endpoint is read. Both original alphabets are retained: all $m$-bit words and internally legal $m$-bit words coincide here because $m<k$. Cross-block rejection remains part of (1.4). Every issued block costs one, including waits and blocks that reject before the endpoint.

**Definition 1.3 (Complete stationary GLOBAL memory).** The controller is exactly

$$
c:\{0,1,\bot\}\to K,\qquad
u:K\to\{0,1\}^m\sqcup\operatorname{Halt}(f(Q)),\qquad
V:K\times\{0,1,\bot\}\to K.
\tag{1.5}
$$

A word row emits its installed whole word, then applies its fixed update $V$ to the raw endpoint. A Halt row returns its installed literal label. GLOBAL requires every actual emitted sequence to be a prefix of one fixed installed stream. Stopping can depend on responses; the next emitted word cannot depend on them. All retained values, endpoint baselines, stages, stops and outputs belong to $K$. Phase, tail, source index, immutable target and proof rank are unavailable inputs. There is no external archive, clock, counter, reset, copy, runtime target tag or decoder.

Let $K_{\min}^{\rm GLOBAL}(4;f)$ be the minimum $|K|$ among complete controllers correct on all $Q$ within four issued blocks. Distinct output labels require distinct Halt rows. Equal-labelled terminal rows can be merged. Thus a certificate with $e$ word rows and exactly one Halt per actual label has $N+e$ states.

**Reused bounds 1.4.** [OWN, Lemma 5.3] is horizon-independent and gives at least four word rows. [OWN, Theorem 6.1, (6.2)–(6.5)] supplies five word rows within three blocks on precisely (1.1). Consequently

$$
N+4\le K_{\min}^{\rm GLOBAL}(4;f)\le N+5.
\tag{1.6}
$$

[OWN, Theorem 3.2] supplies $C_{\rm ad}(f)=2$ and $C_{\rm pre}(f)=3$. Block-fee value joining is not a memory-preserving transformation and is not used to infer a complete state minimum.

## 2. The three physical conditions

**Definition 2.1 (Same-word charges).** For an even full ambient support $E\subseteq W_t$, retain the credited inverse

$$
\mathcal B_t(E)_b=\bigoplus_{z=0}^b\mathbf1_E(tm+z),\qquad 0\le b<m.
\tag{2.1}
$$

Full ambient parity is required; restriction to the actual subgroup need not be even. If $B=\mathcal B_1(E)$, set $q(j)=\mathbf1_E(j)$, extended by zero outside $E$. Repeating this same literal word gives

$$
q_2^B(j)=q(j-m),\qquad q_3^B(j)=q(j-2m).
\tag{2.2}
$$

The first bit is $q(m)$ and the last bit is $q(a)$. Write $\tau(B)$ for its terminal one-run and $\alpha(D)$ for a word's leading one-run, including $\alpha(1^m)=m$. For the zero-leading first query, $m\notin E$, so $B_0=0$ and

$$
\tau(B)=m-1-\max\left\{b\in\{0,\ldots,m-1\}:
\bigoplus_{z=0}^b\mathbf1_E(m+z)=0\right\}.
$$

The maximum is defined because it includes $b=0$. This first zero clears every incoming successful tail, so every successful arrival after $B$ has this same terminal tail. An arbitrary literal word $D$ following this first query is safe exactly when $\tau(B)+\alpha(D)<k$. Later internal runs have length less than $k$. If $D=1^m$, its successful arrival tail is $\tau(B)+m$; if $D$ contains zero, its successful arrival tail is its own terminal one-run $\tau(D)$.

For $r=2$, fix a notation-only bijection $\kappa:U_Y\to\mathbb F_2$, and put $b_v=\kappa\lambda_v$. All targets and outputs remain the literal labels of (1.2). Let $M_i$ be the unique whole $\lambda_i$ class on which $\lambda_{1-i}$ is nonconstant. Three occupied corners of a binary rectangle give this unique class and make the other component constant on its complement.

The following are exactly the original physical predicates, with no controller existential hidden in their definitions.

**Condition $\mathsf A$ ([OWN, (9.2)]).** For some $i,\eta\in\mathbb F_2$ and even $E\subseteq W_1$ with $m\notin E$,

$$
q(j)=b_i(j)\oplus\eta\quad(j\in J),\qquad
q(j-m)=1\oplus b_0(j)\oplus b_1(j)\quad(j\in M_i).
\tag{2.3}
$$

Equivalently, a whole $\lambda_i$ class $A$ misses $H$ and satisfies

$$
M_i\cap(A+m)=\{j\in M_i:\lambda_i(j)=\lambda_{1-i}(j)\}.
\tag{2.4}
$$

Its even completion uses the excluded donor zero. That donor cannot affect the shifted tests, since $j-m\ne0$ on $J$.

**Condition $\mathsf B$ ([OWN, (9.3)–(9.4)]).** There are distinct literal labels $L,L'$, bits $e,\delta$, and even full supports $E\subseteq W_1$, $F\subseteq W_2$, with $m\notin E$, such that

$$
\Lambda[J]=\{(L,L),(L',L),(L,L')\},\qquad
\mu(j)=\mathbf1_{\{\Lambda(j)\ne(L,L)\}},
$$
$$
\lambda_{e\oplus\mathbf1_E(j)}(j)=L\quad(j\in J),\qquad
\mathbf1_F(j)=\mu(j)\oplus\delta\quad(j\in J),
\qquad \tau(\mathcal B_1(E))+\alpha(\mathcal B_2(F))<k.
\tag{2.5}
$$

Safe all-one final words are included.

**Condition $\mathsf R$ ([OWN, (11.2)]).** There are $v\in\mathbb F_2$, $w=1-v$, a zero-leading literal $B$, a bijection $G:\mathbb F_2\to U_Y$ and a literal label $z$ such that, with $I=\{j\in J:q_1^B(j)=1\}$ and $U=J\setminus I$,

$$
\lambda_w(j)=G(w\oplus q_1^B(j))\quad(j\in J),\qquad
\lambda_v(j)=z\quad(j\in U),
$$
$$
j'=j-2m\in J,\qquad \lambda_v(j)=\lambda_w(j')\quad(j\in I).
\tag{2.6}
$$

Only the original-fee-four restriction on the sufficient application of this predicate is removed. None of its word, label, translation or source requirements is removed. A failure of any sufficient predicate alone gives no exclusion.

**Theorem 2.2 (Exact slack-deadline classification).** For every target of Definition 1.1, under either original alphabet,

$$
\boxed{
K_{\min}^{\rm GLOBAL}(4;f)=
\begin{cases}
N+4,&r=2\text{ and }(\mathsf A\lor\mathsf B\lor\mathsf R),\\
N+5,&\text{otherwise}.
\end{cases}}
\tag{2.7}
$$

In particular $r=3$ and $r=4$ always have $N+5$ states. Every bottom-label case is governed by (1.3). Sections 3–5 prove necessity over arbitrary four-word-row controllers; Section 6 supplies the complete attainments by applicable reuse.

## 3. Facts used in the four-row exhaustion

**Lemma 3.1 (Actual supports, calendar and useful exits).** In any correct four-row competitor, every initial root installs $L=1^m$, and every mandatory root-zero successor installs the same zero-leading word $B$. Roots and those queries are disjoint rows. Put $q=q_1^B$, $p=q(0)$ and $c=3m\pmod T$. Then

$$
q(m)=0,\qquad q_2^B(a)=0,\qquad q_2^B(m)=p.
\tag{3.1}
$$

The index-two charge of $L$ is $\rho=\mathbf1_{\{a,c\}}$. In particular $\rho(0)=\rho(m)=0$. The actual subgroup has at least five vertices, because $|J|\ge3$; $a,c,-m,-2m$ are actual nonendpoint vertices wherever used below.

Proof. Root forcing and zero-leading query forcing are the irreversible first-zero and maximal surviving-tail arguments of [OWN, Theorems 3.2 and 9.2]. They use actual original tails $0,h$ at the root and $h-1$ on every lower phase, not a favorable tail selection. The translation and all-one charge identities are the physical interface (2.1)–(2.2). The order of $m$ in $P$ is $|P|\ge5$, which gives the vertex distinctions. ∎

After the first $B$, every still-active successful source has the same literal tail $\tau(B)$. Some endpoint archive is still mixed: otherwise $L\mid B$ would acquire the full target in two blocks, contrary to the reused fee theorem. Thus the common next word $D$ must succeed; common-tail semantics then makes it succeed on all active successful sources. A word containing zero is safe on repetition after itself, since $\alpha(D)+\tau(D)\le m-1<k$. A safe $D=L$ rejects on repetition, since $\tau(B)+2m\ge k$. Both alternatives are admitted.

A root's bottom continuation must eventually return $R$, because an actual initial high-tail source has that same row and absorbing bottom successor. It may be shortened to its existing $H_R$ without changing successful-source behavior. A later $C$ or lower source therefore cannot reject at a root. Initial bottom may likewise initialize to its literal Halt. No analogous shortening of a delayed successful $C$ branch is assumed.

At a fixed row, identical current records have identical remaining deterministic executions. Different immutable labels on that same row/current-record pair are therefore impossible. This is the actual-union invariant of [FC, §§26–27]; the label is a proof coordinate, not an input. A spare row with a homogeneous entire actual union can be replaced by its existing Halt and removed. A correct controller with only three word rows would contradict the reused horizon-independent lower bound.

**Proof convention 3.2 (Fixed effective outputs).** When a raw branch has at most one useful final Halt label, its eventual literal return can be denoted by that label. This only abbreviates its fixed installed updates. In particular, a last root cannot return a lower label; a last zero-leading query with one scalar Halt can return only that Halt's label; a repeated zero-containing row with an emitting edge offers at most its other scalar Halt; and a repeated all-one row offers one uniform bottom return. These statements retain actual rejection and charged delays. They do not install an external decoder.

There are exactly four sharing shapes: distinct/shared initial roots crossed with distinct/shared mandatory first queries. The remaining rows can install arbitrary words. Their actual occurrences, rather than nominal program layers, determine the following cases.

## 4. Shared-root and shared-query competitors

**Lemma 4.1 (A shared root and shared query are impossible).** A deadline-four controller with four word rows cannot share both its root and its first query.

Proof. Name these rows $a_0,b$ and the two spares $x_0,x_1$. Each raw child of $b$ contains $C$ from an original phase-$m$ source, and one lower source at every $j\in J$. Both edges emit. A self-edge of $b$ repeats at the actual phase $a$, where $q_2^B(a)=0$, and leaves a last $b$ with no scalar Halt.

An edge back to the shared root is impossible as well. If its $L$ rejects the phase-$m$ $C$ source, the output is $R$. If safe, $\tau(B)<h$, and that source's arrival at the root has translated INITIAL phase $-m\in J$. The same value, phase and tail are an actual original lower source at that shared root. The immutable labels conflict.

Both children therefore use the spares. If they merge into one spare, after its safe word each raw child still has $C$ and lower sources: the two initial values occur at every relevant phase. Both edges emit, leaving only the other spare as a final decoder for at least three labels. On the common tail it offers at most two successful responses, or one uniform rejecting response.

If the children use distinct spares, both install the same $D$. For $D=L$, each spare's first scalar branch has one fixed eventual output, including any late repeated-$L$ rejection. Its first support consequently has at most two labels. Since it includes $C$, its lower part must be homogeneous. Two such lower parts make the join have at most two classes.

For zero-containing $D$, repetition is safe. Non-$R$ labels can only be scalar Halts of the spares. At least three such labels require a spare with two distinct scalar Halts; a final spare with two identical labels is removable by the homogeneous-union observation. Say $x_i$ has outputs $\{C,A\}$. Its first support has a lower $A$ source at every actual $j$, so $D$'s charge is constant on all $J$. All lower sources at the other spare therefore have the same first scalar response. They either return its sole additional lower label, or continue and can return only $A$ among the final spare's labels. A self-continuation can only return its own sole Halt. Thus that lower part is homogeneous too. Again there are at most two joined classes. ∎

**Lemma 4.2 (A shared root with distinct queries is impossible).** A deadline-four four-word-row controller cannot have a shared root and distinct first queries.

Proof. Write the rows $a_0,b_0,b_1,x$. At $b_y$ the first actual support has exactly

$$
T_y=\{C\}\cup\lambda_y[J].
$$

The $C$ sources have initial value $1-y$; the lower sources have initial value $y$. Original $C$ phases $m,0$ give raw first-query endpoints $y,y\oplus p$. Each $b_y$ therefore has at most one scalar Halt. Partition by the common index-two word $D$.

If $D\ne B,L$, only $x$ installs $D$, and $D$ contains zero. Each raw branch of its index-two occurrence has one fixed useful eventual label: a last query has at most one scalar Halt, a last shared root none, and a repeated $x$ is safe and has at most its remaining scalar Halt. Thus $x$ supplies a fixed binary map with image $F$. Each $T_y$ has three labels and must split into a homogeneous direct Halt $Z_y$ outside the same two-label set $F$, and a child containing $F$. If $C\in F$, phase $m$ puts $C$ in the charge-zero child, so the common charge-one class is exactly $\lambda_y^{-1}(Z_y)$ for both values; the complementary class has the same lower label in $F$. If $C\notin F$, both direct Halts are $C$, all lower phases have charge one, and the two values enter the same fixed decoder with complementary scalars. Either way the join has at most two classes.

Let $D=L$. An endpoint-phase $C$ source cannot enter the shared root: safety puts its tail below $h$, while translation by $-2m$ puts its current phase in $J$, conflicting with the actual original lower label at that root. The index-two occurrence of $x$ still has a fixed binary effective output map, including repeated-$L$ bottom returns. If $p=1$, both children of each query contain $C$; any direct Halt is $C$, and both lower labels together with $C$ must enter $x$, exceeding two labels. If $p=0$ and a phase-$m$ $C$ edge halts, then $q=1$ on all $J$. Neither query has a lower Halt, so all lower sources enter $x$; a delayed $C$ entry there would exceed its output capacity. With both $C$ edges stopped, the common decoder gives at most two joined pairs. Otherwise both phase-$m$ $C$ edges enter $x$. Their scalars remain complementary because $\rho(m)=0$, so both outputs of its effective map are $C$. No lower source can enter it. This forces $q=1$ on $J$ and sends the binary lower supports through the root, whose last queries have no lower Halts. This also fails.

It remains $D=B$. If a first-query raw response is absent on its mandatory support, then $q=0$ on all $P$. The first two repetitions give no phase information; each $T_y$ still has three labels and cannot finish in one last common-tail block. Therefore both raw query responses occur early. Any useful edge to $x$ forces its word to be $B$ already at index two. All three query rows install $B$, all their repetitions are safe, and roots supply no useful last exit.

A spare with two equal scalar Halts has a homogeneous union and is removable. If $x$ has at most one scalar Halt, output capacity requires $r=2$ and one distinct Halt label at each of the three query rows. Both initial queries must reach all three labels, so their unique emitting edges form a three-cycle. This cycle fails on the two actual $C$ endpoint phases. If its $C$-Halt row is $b_i$, that row's own $C$ sources must halt immediately, forcing $p=0$ and its stop bit $i$. The other query's phase-$m$ source cannot use that stop after two queries. If it reaches it after three, it requires $q(-m)=1$; the phase-zero source then takes the preceding non-$C$ Halt. If the $C$-Halt row is $x$, the nearer initial query's two endpoint sources force $p=0$ and $q(-m)=0$. The farther query's phase-$m$ source reaches that nearer query with the complementary, halting scalar. Thus no three-cycle works.

Hence $x$ is final with two distinct scalar labels $F$. First suppose $C\notin F$. Some query halts $C$, so $q$ is constant on $J$. If $q=0$ on $J$, both binary lower supports receive no phase distinction in either of the first two $B$ words and must use $x$ last, with complementary scalars: at most two joined pairs. If $q=1$ on $J$, then $q_2^B$ is zero at $a$ and one on $J\setminus\{a\}$. A $C$-Halt query cannot send its lower edge to itself, because the other phases return $C$. It cannot send it to another $C$-Halt query, because phase $a$ returns $C$. Sending it through a nonhalting other query forces both of that query's edges to $x$ to finish the lower sources, also sending its early $C$ source to lower Halts. Thus each $C$-Halt query sends its lower edge directly to $x$; its phase-zero $C$ source additionally forces $p=0$. If both queries halt $C$, complementary lower inputs again give only two joined pairs. If only $b_i$ halts $C$, the phase-$m$ $C$ edge of the other query can only self-return or enter $b_i$. With $p=0$ the self-edge repeats through the deadline; the cross-edge takes $b_i$'s lower edge into $x$ and returns a lower label. Both fail.

Finally let $F=\{C,A\}$. A different lower label must halt at a query. Such a Halt requires $p=0$ and nonconstant $q$; no query can then halt $C$. Each phase-$m$ $C$ edge must enter $x$ or cross to the other query, since a self-edge repeats at $q_2^B(m)=0$. Two direct entries to $x$ have complementary scalars and cannot both return its single $C$ output. With one cross-edge and one direct edge, the receiving query's other edge must also enter $x$ to finish the late $C$ source; its entire three-label first support then enters a two-Halt final row. With two cross-edges, both opposite edges must emit to finish those $C$ sources, leaving no query Halt for the lower label outside $F$. These cases exhaust every $D$, including waits and late all-one rejection. ∎

**Lemma 4.3 (Distinct roots with a shared query imply $\mathsf B$).** Every four-row competitor of this shape has $r=2$ and satisfies (2.5).

Proof. Write the rows $a_0,a_1,b,x$. Each raw child of $b$ contains one lower source at every $j$. A self-edge with the other edge a Halt can return only that one lower label; with the other edge emitting, phase $a$ repeats the self-edge at its second query and leaves a nonhalting last $b$.

If both children enter $x$, its safe first word has a fixed binary effective output map on the lower sources. A last $b$ has no Halt, a last root cannot return a lower label, a repeated zero-containing $x$ has at most its existing scalar Halt, and a repeated all-one $x$ adds only one uniform bottom return. Complementary value inputs give at most two joined pairs. If an emitting edge instead enters a root, its zero edge leaves a last $b$ without Halts. Its positive edge can finish a lower label only through $x$; that same edge sends an actual initial $C$ source to $x$ at index one, forcing $u(x)=B$. Such an early safe $C$ occurrence prevents two lower scalar Halts at $x$. Two root entries cannot supply both lower labels, and a simultaneous root and $x$ at index two would require $u(x)=L$, contradicting $u(x)=B$.

Thus $b$ has a homogeneous raw child $e$ with literal Halt $L$, and one continuing child $\beta=1-e$. Homogeneity gives

$$
\lambda_{e\oplus q(j)}(j)=L\quad(j\in J).
\tag{4.1}
$$

This requires $L$ common to both label sets. For $r=3$, the other child contains $L$ and both exclusive lower labels. It cannot finish: at $x$ its first response has at most two fixed useful eventual labels, and a root offers only the last $b$'s $L$ Halt and at most one other lower Halt at an early-$C$ row $x$. The same observation gives $r=2$, with exactly the literal star in (2.5). The continuing support contains one initial value at every $j$, has common scalar $\beta$, and target $L$ on the central class and $L'$ on the leaves.

If it enters $x$, each raw branch of the safe index-two word must already be homogeneous: the possible last rows just listed each offer a single useful lower label. Its full charge is therefore $\mu\oplus\delta$ for some orientation $\delta$, and its actual safe seam supplies (2.5).

If it enters root $a_i$, the middle word is $L$. A lower return through its positive edge requires $x$ last. Its mandatory early $C$ occurrence forces $u(x)=B$ and fixes the raw-$1-i$ scalar Halt there to $C$, using original phase $m$. If $\beta=i$, actual phase $c$ takes the root-positive edge and has $q_3^B(c)=q(m)=0$, incorrectly returning that $C$ Halt. Hence $\beta=1-i$. On $\rho=1$, the root-zero edge reaches $b$ last and can only return $L$; on $\rho=0$, the positive edge reaches $x$ and can only return its other lower Halt $L'$. Thus $\mu=1-\rho$ on all $J$. The same actual safe $L$ has charge $\mu\oplus1$ and satisfies (2.5). No early stopping assumption was made on the root-positive $C$ paths. ∎

## 5. Distinct roots and distinct queries

**Lemma 5.1 (Delayed root-positive $C$ cannot help in this shape).** With four rows $a_0,a_1,b_0,b_1$, all useful lower outputs are scalar Halts of the queries. In every viable allocation, query scalar Halts are lower labels, and every query emitting edge is exercised at its mandatory first occurrence. The root-positive $C$ edges must halt immediately.

Proof. Root-bottom returns $R$, and a root's direct other scalar Halt must return $C$. Zero-leading queries never reject. At least two different lower labels must therefore occupy query scalar Halts. If a query is final, its first nonconstant binary table uses both responses and both Halts are its lower labels; the common charge is nonconstant, so both responses of the other query also occur early. Without a final query, both queries require one different lower Halt. Their binary first supports force their other, emitting edges to occur early; an unused raw branch may be their lower Halt, but cannot be an extra emitting edge. Both allocations leave no query $C$ Halt.

GLOBAL makes all exercised emitting query edges lead to rows with one common word, either $B$ or $L$. If $B$, they stay among queries and never return $C$. If $L$, follow an actual phase-$m$ $C$ source from a delayed positive root edge. Its scalar $1-v$ is unchanged by $B$ and by the middle $L$, using $q(m)=\rho(m)=0$. At a root with initial value $1-v$ it takes the emitting zero edge; at root $a_v$ it takes that same delayed positive edge. The last query has no $C$ Halt. An unsafe root returns $R$. Thus the original positive edge cannot be delayed. ∎

**Lemma 5.2 (An early final query implies $\mathsf A$ or $\mathsf R$).** Suppose $b_i$ has two scalar Halts. Then $r=2$, and one of (2.3), (2.6) holds.

Proof. Its installed decoder is a bijection $G$ and

$$
\lambda_i(j)=G(i\oplus q(j)).
$$

For $w=1-i$, the other table is mixed exactly on $M_i$, a whole $q=d$ class; it is constant on the complement. Its mixed raw response is $\beta=w\oplus d$.

If its successor is $b_i$, the same $B$ is issued again. The same raw decoder on the early and late supports gives (2.3); its late mixed pair also forces the two lower-label sets to coincide.

If its successor is $b_w$, the other edge cannot halt, since then only that sole label could ever return on the mixed support. GLOBAL forces that other edge into $b_i$. Termination requires $q_2^B=1$ on $M_i$. Correct decoding of the homogeneous complementary class requires $q_2^B$ constant there. That constant cannot be one, by $q_2^B(a)=0$. Thus $q_2^B=\mathbf1_{M_i}$ on $J$. Index actual phases as $j=tm$, $2\le t\le n-1$, with $n=|P|$ and $Q_t=q(tm)$, $Q_1=0$. If $d=1$, the identity becomes $Q_{t-1}=Q_t$, forcing constant $q$ on $J$. If $d=0$, it becomes $Q_{t-1}=1-Q_t$; on $M_i$ the two-step predecessor $q_3^B$ is then zero. The last decoder is constant on the mixed class. Both alternatives contradict its two labels.

The remaining successor is a root. Lemma 5.1 makes its positive edge a direct $C$ Halt, so all mixed sources must use its zero edge. A last $b_w$ cannot separate them, leaving only root $a_i$ and last query $b_i$. The root charge $\rho$ is constant $1\oplus d$ on $M_i$. Both literal labels on that mixed class are decoded by $G$, so the two lower-label sets coincide and $r=2$.

For $d=1$, the whole one-charge class $I=M_i$ arrives with scalar $i$. Safety gives $\tau(B)<h$. At the reused root its current record is an actual original record at $j'=j-2m$, with tail $\tau(B)$. Equality of immutable labels there forces $j'\in J$ and $\lambda_w(j)=\lambda_i(j')$; fresh $C$ excludes the endpoint phases. Together with the constant complement these are exactly $\mathsf R$. The mixed pair decoded at $b_i$ gives $r=2$.

For $d=0$, $M_i\subseteq\{a,c\}$ and its nonconstancy gives $M_i=\{a,c\}$. Both vertices miss $H$. The late decoder gives

$$
\lambda_w(a)=G(i\oplus p),\qquad \lambda_w(c)=G(i),
$$

whereas $\lambda_i$ equals $G(i)$ on both. Nonconstancy forces $p=1$: the literal labels are unequal at $a$ and equal at $c$. Choose the alternative whole first-charge class $A=M_i$. Its shifted charge is zero at $a-m=m$ and one at $c-m=a$. Its excluded-zero even completion satisfies (2.4), hence $\mathsf A$. This is an existence extraction of an existing predicate, not a claim that the competing word had that alternative support. ∎

**Lemma 5.3 (The nominal two-query cycle is absorbed by $\mathsf A$).** If neither query is final, a correct four-row competitor has $r=2$ and satisfies (2.3).

Proof. Each query has one distinct lower Halt $L_v$ and one exercised emitting edge. A self-edge can only return that query's own Halt label, contrary to its nonconstant table. If both emitting edges lead to roots, Lemma 5.1 makes all continuing sources take root-zero edges and finish at queries with only one lower Halt. Both component tables are then functions of the same first charge, giving at most two joined classes. Thus both edges cross to the other query; the stream is $L\mid B\mid B\mid B$. This nominal cycle is retained.

Let $t_v$ be the raw Halt bit of $b_v$. If $t_0\ne t_1$, both components either halt first or cross together, and only the two off-diagonal pairs can return. Hence $t_0=t_1=t$. Fixed raw updates give exactly

$$
q_2^B(j)=1\Longrightarrow \Lambda(j)=(L_{q(j)\oplus t},L_{q(j)\oplus t}),
$$
$$
q_2^B(j)=0\Longrightarrow
\Lambda(j)=(L_0,L_1),\qquad q_3^B(j)=1.
\tag{5.1}
$$

The last equality is the actual termination requirement, not an assumed guard. Both diagonal pairs and the displayed off-diagonal pair occur.

Homogeneous nonempty $H$ cannot be the off-diagonal class. To prove this with the actual gcd, use reduced actual coordinates $u=m/g$, $n=T/g$ and $v=n-u$. Then

$$
H/g=\{u-v+1,\ldots,u-1\},\qquad
(H/g)+v=\{u+1,\ldots,n-1\}.
$$

An off-diagonal $H$ forces $q=0$ on both intervals. Translating the termination requirement in (5.1) says

$$
q(x)=0\Longrightarrow q(x+v)=1\qquad(x\notin\{0,v\}).
$$

Thus nonempty $H/g$ is contained in $\{v\}$. Its cardinality $v-1$ forces $v=2$, and $u-1=v$ forces $(u,n)=(3,5)$. The forced actual charges on $J/g=\{1,2,4\}$ are $(1,0,0)$, whose second charges are $(0,0,1)$. They give only one diagonal and the off-diagonal pair, contradicting three joined classes. Therefore $H$ is empty or has diagonal label $(L_t,L_t)$.

Choose $i=1-t$ and the whole class $A=M_i$, namely the other diagonal together with the off-diagonal. It misses $H$. For a diagonal point in $M_i$, $q(j-m)=1$, so its shifted actual argument belongs to $A$. For an off-diagonal point, $q(j-m)=0$ and $q(j-2m)=1$; its shifted argument is the opposite diagonal and lies outside $A$. At $j=a$ that argument is the excluded leading vertex $m$ and both the shifted class indicator and the required equality indicator are zero. No argument is the excluded donor zero. These are exactly (2.4). The existing even completion supplies $\mathsf A$ on the full physical path. This argument uses no acyclicity assumption on the control graph. ∎

**Proof of necessity in Theorem 2.2.** Lemmas 4.1–4.2 exclude both shared-root shapes. Lemma 4.3 extracts $r=2$ and $\mathsf B$ from distinct roots with a shared query. With distinct roots and queries, four lower Halt labels would make both queries final and acquire the target in two blocks. Three lower labels require an early final query, but Lemma 5.2 forces equal lower-label sets. The remaining binary allocations are an early final query or one different Halt per query, covered by Lemmas 5.2–5.3. Thus every four-word-row competitor has $r=2$ and $\mathsf A\lor\mathsf B\lor\mathsf R$. All arguments used actual original sources, fixed raw updates and actual words at their paid indices. Delayed homogeneous branches, zero-Halt queries, all-one success and late rejection, waits, root entry and nominal cycles have remained in the case partition. ∎

## 6. Complete matched attainments and their source unions

**Proposition 6.1 (Applicable reuse).** Conditions $\mathsf A$ and $\mathsf B$ use exactly [OWN, (9.8)–(9.13)], already complete by deadline three. The universal five-row fallback is exactly [OWN, (6.2)–(6.5)], also complete by deadline three. Their domains include every source of (1.2), not merely the continuing lower archive. The following declarations specify their application and the extension of $\mathsf R$.

In all certificates, put

$$
\mathcal R_v=\{(f(v,-j,s),(v,-j,s)):j\in P,\ 0\le s<k\},
$$
$$
\mathcal S_v=\{(\lambda_v(j),(v,-j+m,m+s)):j\in J,\ 0\le s<h\}.
\tag{6.1}
$$

Install one $H_y$ for each actual $y\in f(Q)$, with $u(H_y)=\operatorname{Halt}(y)$ and $V(H_y,o)=H_y$ for all raw responses. Initialize $c(\bot)=H_{L_\bot}$. Each word row's bottom update is $H_R$. Exact Halt supports are the initial-bottom pair when applicable and the union of all actual incoming images routed to that Halt. This is [OWN, (5.6)], applied to the actual word-row unions below.

For $\mathsf A$, take two roots $a_v$ and two query rows $d_v$. Initialize $c(v)=a_v$, install $L$ at the roots and $B=\mathcal B_1(E)$ at both queries, and set

$$
V(a_v,v)=d_v,\quad V(a_v,1-v)=H_C,
\qquad V(d_i,x)=H_{G_i(x)},
$$
$$
G_i(x)=\kappa^{-1}(x\oplus i\oplus\eta),\quad
\beta=(1-i)\oplus q(M_i),\quad
V(d_{1-i},\beta)=d_i,\quad V(d_{1-i},1-\beta)=H_z,
\tag{6.2}
$$

where $z$ is the other component's constant literal label outside $M_i$. Root supports are $\mathcal R_v$, the other query has $\mathcal S_{1-i}$, and

$$
\Gamma_{d_i}=\mathcal S_i\cup
\{(\lambda_{1-i}(j),(\beta,-j+2m,\tau(B))):j\in M_i\}.
$$

The same word and decoder act on both parts. Ranks $3,2,1,0$ on roots, continuing query, final query and Halts, and stream $L\mid B\mid B$, are the existing certificate.

For $\mathsf B$, use two roots, one shared query $d$ and one last row $x$. Both root-zero updates enter $d$; positive updates halt $C$. Install $B=\mathcal B_1(E)$ at $d$ and $D=\mathcal B_2(F)$ at $x$, with

$$
V(d,e)=H_L,\quad V(d,1-e)=x,
\qquad V(x,z)=H_{L_{z\oplus(1-e)\oplus\delta}},\quad L_0=L,\ L_1=L'.
\tag{6.3}
$$

Its query support is $\mathcal S_0\cup\mathcal S_1$, and its last support is

$$
\Gamma_x=\{(L_{\mu(j)},(1-e,-j+2m,\tau(B))):j\in J\}.
$$

The actual strict seam in (2.5), ranks $3,2,1,0$, and stream $L\mid B\mid D$ give the unchanged complete certificate. Both A/B certificates have exactly $N+4$ states.

For $\mathsf R$, use four rows $a_v,a_w,b_v,b_w$, with $c(x)=a_x$, both root words $L$, both query words the same $B$ in (2.6), and

$$
V(a_x,x)=b_x,\quad V(a_x,1-x)=H_C,\qquad
V(b_v,v)=H_z,\quad V(b_v,w)=a_w,\qquad
V(b_w,e)=H_{G(e)}.
\tag{6.4}
$$

These are precisely [OWN, (11.4)]. The exact unions are

$$
\Gamma_{a_v}=\mathcal R_v,\quad \Gamma_{b_v}=\mathcal S_v,
$$
$$
\Gamma_{a_w}=\mathcal R_w\cup
\{(\lambda_v(j),(w,-j+2m,0)):j\in I\},
$$
$$
\Gamma_{b_w}=\mathcal S_w\cup
\{(\lambda_v(j),(w,-j+3m,m)):j\in I\}.
\tag{6.5}
$$

Since $a\in J$, condition (2.6) excludes $a$ from $I$: its translated phase would be zero. The very same $B$ therefore ends zero. Every added root pair is already an original support pair at $j'=j-2m$, original tail zero and the same literal target; the added query pair is its actual root image. The first $B$ clears every surviving original root tail, including $k-1$; the middle $L$ is safe from tail zero; the last $B$ clears tail $m$. Ranks $4,3,2,1,0$ on $a_v,b_v,a_w,b_w$, Halts certify the single stream $L\mid B\mid L\mid B$. These support inclusions, seams and outputs use no hypothesis about three classes on $O$. Thus the original sufficient controller applies to the present slack domain with $N+4$ states.

For the $N+5$ branch, reuse the entire five-row certificate [OWN, Theorem 6.1]: roots $a_v$, first queries $b_v$ and last row $p_2$, with (6.2)–(6.4) of that owner. Its first query isolates a leaf of the three-corner rectangle; its reverse orientation is retained when that leaf is the homogeneous $H$ class. The displayed second word includes the original first-interior charge adjustment, so its actual seam is safe even in that reverse orientation. Supports are $\mathcal R_v,\mathcal S_v$, the owner's (6.5), and its exact Halt images (5.6); ranks are $3,2,1,0$. All executions are prefixes of its installed three-block stream. No extra fourth block is needed. This is a direct application of the complete existing attainment, not a new five-row mechanism.

These certificates meet [FC, Theorem 27.2] on their actual immutable-target/current-record unions. They do not read those supports or ranks at runtime. The horizon-independent lower bound matches all four-row attainments; the exhaustion matches the five-row fallback on its complement. This proves Theorem 2.2. ∎

## 7. A strict deadline-slack consumer at every scale

**Corollary 7.1.** For every integer $q\ge1$, set

$$
m=5q,\quad k=7q-1,\quad T=7q,\quad g=q,
\quad J=\{q,2q,3q,4q,6q\},\quad H=\{4q\},\quad O=\{2q\},
$$
$$
\lambda_0(j)=\mathbf1_{\{2q\}}(j),\qquad
\lambda_1(j)=\mathbf1_{\{2q,6q\}}(j).
\tag{7.1}
$$

Use these literal labels $0,1$, fresh $R,C$ and arbitrary bottom in the entire target (1.2). Then

$$
C_{\rm ad}(f)=2,\quad C_{\rm pre}(f)=3,
\qquad K_{\min}^{\rm GLOBAL}(3;f)=N+5,
\quad K_{\min}^{\rm GLOBAL}(4;f)=N+4.
\tag{7.2}
$$

Proof. Both diagonal pairs occur, so $\mathsf B$ fails. Homogeneous $H$ fixes the orientation in $\mathsf A$. For component zero, phase $q\in M_0$ needs shifted charge one, but $q-m=3q$ has charge zero. For component one, phase $2q\in M_1$ needs shifted charge one, but $2q-m=4q$ lies in $H$. The reused [OWN, Theorem 9.2] therefore gives the deadline-three lower value $N+5$.

Condition $\mathsf R$ holds with $v=0,w=1$, $z=0$,

$$
B=0^q1^{3q}0^q,\quad I=\{2q,6q\},\qquad G(0)=1,\quad G(1)=0.
$$

Translation by $-2m$ sends $2q,6q$ to $6q,3q$, with matching literal labels $1,0$. The complete raw table is

| Row | Word | Endpoint 0 | Endpoint 1 | Bottom |
| --- | --- | --- | --- | --- |
| $a_0$ | $1^{5q}$ | $b_0$ | $H_C$ | $H_R$ |
| $a_1$ | $1^{5q}$ | $H_C$ | $b_1$ | $H_R$ |
| $b_0$ | $B$ | $H_0$ | $a_1$ | $H_R$ |
| $b_1$ | $B$ | $H_1$ | $H_0$ | $H_R$ |

Initialization, all Halt self-updates, exact unions and ranks are (6.4)–(6.5). Every one of the $98q-13$ jointly actual INITIAL records, including bottom, is included. Some sources issue all four blocks; the common optimal fee remains three because a different controller attains it. Complete states drop from nine to eight when bottom uses an existing output, and from ten to nine when its label is fresh. The dictionary has two words and $10q$ expanded bits; the four-block prefix has $20q$ bits. Those lengths are not complete-state counts. ∎

## 8. Source scope and resource conventions

**Convention 8.1 (Scope and cited premises).** The target and control contract is [OWN, Definitions 3.1/5.1], with all its original hypotheses. Its Sections 12.2/16.3 exclude this fee-three slack domain. Its original deadline-three results and original-fee-four deadline-four results retain their stated domains; no three-class-on-$O$ necessity is transferred here. Theorem 2.2 concerns precisely the complete Definition 3.1 fee-three targets at deadline four. Tail-dependent tables, nonhomogeneous $H$, other class counts or extensions, other parameter regions and the arbitrary-target/all-$k,m$ FIB objective remain outside it.

[IC, Chapter 1] supplies the original integer reader, total updates, whole-history witnesses and full physical inverse. [S10, Interface 2.1 and Lemma 3.2] supplies actual same-word seams and common-tail all-success/all-rejection semantics. [FC, Definitions 26.1–27.1 and Theorems 27.2–27.3] supplies complete Moore control and exact union-support/remaining-execution certificates.

The charged literal inverse, irreversible mergers, horizon-independent four-row lower bound, complete five-row attainment, A/B attainments and root-reentry mechanism are credited reuse in Theorem 2.2. Its source-local four-row necessity at the slack deadline is proved in Sections 3–5, including the endpoint-$C$ exclusions, shared-query extraction, zero-Halt self-query obstruction and actual-subgroup absorption of the nominal cycle. Corollary 7.1 consumes that distinction.

**Convention 8.2 (Resources and effectivity).** The result is a semantic minimum for arbitrary literal label sets. Effective selection requires a finite target-partition presentation or decidable equality on the finite tables. Conditions A and R can be tested through whole actual classes and label comparisons; condition B can be decided by enumerating full even ambient supports, retaining the physical inverse and actual seam. Such finite exhaustive selection is an offline procedure, not an emitted-block operation or a claim of efficient bit complexity. Costs of integer arithmetic, input representation and label equality remain separate.

The successful apparatus part has $2|P|k$ actual INITIAL records. A complete controller has the stated word rows and all $N$ Halt rows; the program position, initial-value distinction, baseline, stop and output are included there. Stored word-dictionary bits, expanded-stream bits, descriptor bits, installation/search work and physical bit work are distinct coordinates. The theorem bounds four issued blocks, each of exactly $m$ physical updates; an early rejection still charges the whole issued block. It supplies no reset, copy, archive, free delay, phase read or extra operation. Proof unions and pair-dependent ranks certify executions and are not runtime storage.

[OWN]: https://github.com/the-omega-institute/trureturing/blob/19af731fc2f1922307812d1050d1e88c2f7fd671/docs/develop/theory/KBONACCI_THREE_CLASS_ROOT_ZERO_COMPATIBILITY_PRICE.md
[IC]: https://github.com/the-omega-institute/trureturing/blob/78532fbc37b92a9d781eb2c9652a49ef6ce41986/docs/develop/theory/KBONACCI_INITIAL_TARGET_COST_THEORY.md
[S10]: https://github.com/the-omega-institute/trureturing/blob/84c05a76262b9b8c1a491c02afdee34e60535e9b/docs/develop/theory/KBONACCI_NARROW_QUERY_WINDOW_COST.md
[FC]: https://github.com/the-omega-institute/trureturing/blob/06aa305f75d2e8f0f38ccc4c763391e8caa15e6b/docs/develop/theory/FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md

## 追加锚（本行以下为增补区）
