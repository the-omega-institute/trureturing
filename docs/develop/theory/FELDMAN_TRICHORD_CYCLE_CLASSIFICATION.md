# 1. Classification of semitone-trichord cycles

## 1.1. Definition: the two existence predicates

Fix an integer $n\ge 6$, put $m=n-3$, and use the additive group $\mathbb Z/n\mathbb Z$. For $2\le k\le n-2$, write $T_k$ for the transposition class of $\{0,1,k\}$. An actual cycle is a cyclic word $c:\mathbb Z/m\mathbb Z\to\mathbb Z/n\mathbb Z$ whose windows

$$
W_i=\{c_i,c_{i+1},c_{i+2}\}
$$

are three-element sets, with exactly one window in each class $T_k$. All subscripts are cyclic. Transposition classes are not identified under inversion. Repeated pitches at different positions are permitted.

The cycle is scalar if its unique $T_2$ window, as an ordered triple, is $a+(0,1,2)$ or $a+(2,1,0)$ for some $a$. Let $C_n$ denote existence of an actual cycle and $S_n$ existence of an actual scalar cycle.

The classes in this definition are distinct. Indeed, the cyclic clockwise gap word of $\{0,1,k\}$ is $(1,k-1,n-k)$, considered up to cyclic rotation. When $k\ge3$ there is exactly one gap equal to $1$, so equality with another such gap word fixes its position and then fixes $k$. At $k=2$ there are two gaps equal to $1$; no other allowed $k$ has that property. A transposition preserves the cyclic gap word, proving the assertion.

## 1.2. Cited mathematical inputs

We use the following results of Feldman [F1, F2] as intermediate inputs:

1. An actual zigzag cycle exists at $n=9$ [F2, `exists_zigzag_nine`; also a consequence of F1, Theorem 8.3]. Here zigzag means that the unique chromatic window is not scalar. In particular, $C_9$ holds.
2. There are no actual cycles at $n=6,7,11$ [F2, `six_no_cycle`, `seven_no_cycle`, `eleven_no_cycle`].
3. There is no actual scalar cycle at $n=9$ [F2, `nine_no_scalar`].

The constructions below prove scalar existence for every other $n$. They do not require a scalar counting formula or any assertion that balance alone gives an actual cycle.

# 2. Edge plans and their realization

## 2.1. Definition: the six edges of a class

An ordered window with steps $(a,b)$ has pitches $(x,x+a,x+a+b)$. The six forms of $T_k$, in the notation of [F1, Section 5], are

| Form | Edge $a\to b$ |
| --- | --- |
| I | $1\to k-1$ |
| II | $k\to1-k$ |
| III | $-1\to k$ |
| IV | $k-1\to-k$ |
| V | $-k\to1$ |
| VI | $1-k\to-1$ |

For completeness, starting at $0$ the resulting pitch sets are respectively

$$
\{0,1,k\},\quad\{0,k,1\},\quad\{0,-1,k-1\},\quad
\{0,k-1,-1\},\quad\{0,-k,1-k\},\quad\{0,1-k,-k\}.
$$

The third and fourth become $\{0,1,k\}$ after adding $1$; the fifth and sixth do so after adding $k$. Thus each form realizes the stated class. Every set has three elements for the allowed $k$.

A plan chooses one form for each class. Its directed multigraph has the nonzero step residues as vertices and the chosen forms as edges, retaining the class as an edge label. Only vertices incident to an edge matter for connectivity. Its drift is the sum of its edge tails in $\mathbb Z/n\mathbb Z$.

## 2.2. Lemma: actual realization

Suppose a plan is balanced at every vertex, its active undirected support is connected, and its drift is zero. Then it gives an actual cycle. If its class-two edge is $1\to1$, the cycle is scalar.

**Proof.** We recall the Eulerian argument underlying [F1, Theorem 5.2]. Starting at an active vertex, follow unused outgoing edges until no continuation is possible. Balance forces this trail to end at its starting vertex: stopping elsewhere would leave that terminal vertex with more used incoming than used outgoing edges, hence at least one unused outgoing edge. If any edges remain, connectivity supplies an unused edge incident to a vertex already visited by the closed trail. The unused graph is balanced, so there is an unused outgoing edge there. Construct another closed trail and splice it into the first. Each splice uses additional edges, so finiteness produces a closed Eulerian trail through all edges.

Let its ordered edges be $e_0,\ldots,e_{m-1}$ and let $d_i$ be the tail of $e_i$. The head of $e_i$ is $d_{i+1}$, including the cyclic boundary. Define $c_0=0$ and

$$
c_i=\sum_{h=0}^{i-1}d_h\pmod n\qquad(1\le i\le m).
$$

Zero drift gives $c_m=c_0$. Extending cyclically, the ordered steps of window $i$ are $(d_i,d_{i+1})$, precisely the chosen form at edge $e_i$. Consequently every window has three distinct entries and realizes its assigned class. There is one edge for each class, and the classes are distinct by Section 1.1, so the windows realize every class exactly once. The class-two loop $1\to1$ gives the ordered triple $a+(0,1,2)$. This is its unique chromatic window. No distinctness between pitches at different positions has been imposed. $\square$

# 3. A subset-sum interval

## 3.1. Lemma: sums of distinct odd integers

Let $q\ge r\ge1$ be integers. The sums of $r$ distinct members of

$$
5,7,\ldots,2q+3
$$

are exactly the integers of parity $r$ in

$$
[r(r+4),\ r(2q+4-r)].
$$

**Proof.** Write the selected members as $2i_1+3,\ldots,2i_r+3$, where $1\le i_1<\cdots<i_r\le q$. The least and greatest sums follow by taking the first or last $r$ indices. To obtain all intermediate values with the correct parity, it suffices to show that $\sum i_h$ takes every integer between its endpoints.

Write $i_h=h+y_h$, where $0\le y_1\le\cdots\le y_r\le q-r$. For any integer $t$ with $0\le t\le r(q-r)$, write $t=ar+b$, $0\le b<r$. Take $r-b$ of the $y_h$ equal to $a$ and the final $b$ equal to $a+1$. These values satisfy the bounds: if $a=q-r$, then necessarily $b=0$. Their sum is $t$. The resulting indices are strictly increasing. Therefore the desired index sums, and hence all the claimed odd-member sums, occur. $\square$

## 3.2. Corollary: enough residues

For $q\ge8$, subset sums of $\{5,7,\ldots,2q+3\}$ contain every integer in

$$
[32,6q+3].
$$

Consequently they represent every residue modulo $2q+4$ when $q\ge8$, and every residue modulo $2q+7$ when $q\ge9$.

**Proof.** Taking $r=3$ in Lemma 3.1 gives all odd integers from $21$ to $6q+3$. Taking $r=4$ gives all even integers from $32$ to $8q$. Since $8q\ge6q+3$, these supply every integer in the stated interval. Its number of integers is $6q-28$. The inequalities

$$
6q-28\ge2q+4\quad(q\ge8),\qquad
6q-28\ge2q+7\quad(q\ge9)
$$

show that it contains at least one complete consecutive block of residues for the respective modulus. $\square$

# 4. Circuits for paired classes

## 4.1. Definition: four elementary pairs

For a level $j$, pair the low class $T_j$ with the high class $T_{n+1-j}$. The following choices are directed two-edge circuits. All residues in their descriptions are taken modulo $n$.

| Pair | Low form, high form | Circuit edges | Integer sum of tails |
| --- | --- | --- | --- |
| $A_j$ | I, V | $1\to j-1\to1$ | $j$ |
| $B_j$ | V, I | $1\to-j\to1$ | $1-j$ |
| $C_j$ | III, VI | $-1\to j\to-1$ | $j-1$ |
| $D_j$ | VI, III | $-1\to-(j-1)\to-1$ | $-j$ |

These identities follow by substituting $k=j$ and $k=n+1-j$ into the six forms. For example, the high-class V edge has tail $-(n+1-j)=j-1$ modulo $n$, and the high-class III edge is $-1\to n+1-j=-(j-1)$. The other entries follow by the displayed formulas in Section 2.1. Integer sums here use the displayed signed lifts; their reductions are the actual drifts.

## 4.2. Definition: a bridge across two levels

At consecutive levels $j,j+1$, choose

$$
(\mathrm{III},\mathrm{I})\text{ at }j,
\qquad
(\mathrm{VI},\mathrm{V})\text{ at }j+1.
$$

The four edges are

$$
-1\to j,\qquad1\to-j,\qquad-j\to-1,\qquad j\to1.
$$

They form the directed circuit

$$
1\to-j\to-1\to j\to1
$$

and their integer tail sum is $1-j-1+j=0$. Denote this four-edge circuit by $X_j$. In the instances below its four vertices are distinct. It connects both semitone vertices $1,-1$.

# 5. All even temperaments from twenty onward

## 5.1. Theorem: even scalar construction

For every even integer $n\ge20$, an actual scalar cycle exists.

**Proof.** Write $n=2L$ and $q=L-2\ge8$. The class-two loop $1\to1$ and the class pairs at levels $j=3,\ldots,L$ partition all classes: the low classes are $3,\ldots,L$, and their high partners are $L+1,\ldots,2L-2$.

For each level choose $A_j$ or $B_j$. Every chosen pair is a two-edge circuit containing $1$. Thus, together with the chromatic loop, the plan is balanced and has connected active support. This also holds at $j=L$, where $-L=L$ modulo $2L$: the formulas still give the indicated two-edge circuits.

If every pair is $B_j$, the total integer tail sum is

$$
\Sigma_0=1+\sum_{j=3}^L(1-j)
=2-\frac{L(L-1)}2.
$$

Changing $B_j$ to $A_j$ adds $2j-1$. The available changes are exactly

$$
5,7,\ldots,2L-1=2q+3.
$$

By Corollary 3.2, a subset of these changes has sum congruent to $-\Sigma_0$ modulo $2q+4=2L=n$. Make precisely those changes. The resulting balanced, connected plan has zero drift and chromatic loop $1\to1$. Lemma 2.2 gives the actual scalar cycle. $\square$

# 6. All odd temperaments from twenty-five onward

## 6.1. Theorem: odd scalar construction

For every odd integer $n\ge25$, an actual scalar cycle exists.

**Proof.** Write $n=2L+1$ and $q=L-3\ge9$. Besides the chromatic class, the paired levels $j=3,\ldots,L$ cover all classes except the singleton $T_{L+1}$.

Choose $A_j$ or $B_j$ for $3\le j<L$ and require $B_L$ at level $L$. At the singleton choose form II. Since $L+1=-L$ modulo $2L+1$, this is the loop

$$
-L\to-L.
$$

All paired circuits contain $1$, and $B_L$ contains $-L$. Thus the singleton loop is attached to their common component. The full plan is balanced and has connected active support.

Starting with all pairs $B_j$, including $B_L$, its integer tail sum is

$$
\Sigma_0=1-L+\sum_{j=3}^L(1-j)
=2-\frac{L(L+1)}2.
$$

The optional changes at levels $3,\ldots,L-1$ add the distinct numbers

$$
5,7,\ldots,2L-3=2q+3.
$$

Corollary 3.2 represents every residue modulo $2q+7=2L+1=n$ by a subset of these changes. Choose the residue $-\Sigma_0$. This gives zero drift while preserving balance, connectivity, and the chromatic loop. Apply Lemma 2.2. $\square$

# 7. The remaining positive temperaments

## 7.1. Lemma: small plans of the same form

Actual scalar cycles exist at

$$
8,12,14,15,17,18,19,21,23.
$$

**Proof.** Use the plans of Sections 5 and 6, with the following choices. The chromatic edge is always $1\to1$. The set $J$ lists the levels where $A_j$ replaces $B_j$; every other level uses $B_j$. For odd $n$, use the singleton loop $-L\to-L$ and retain $B_L$.

| $n$ | $L$ | $J$ | Total integer tail sum |
| --- | --- | --- | --- |
| $8$ | $4$ | $\{3,4\}$ | $-4+5+7=8$ |
| $12$ | $6$ | $\{3,5,6\}$ | $-13+5+9+11=12$ |
| $14$ | $7$ | $\{3\}$ | $-19+5=-14$ |
| $15$ | $7$ | $\{6\}$ | $-26+11=-15$ |
| $17$ | $8$ | $\varnothing$ | $-34$ |
| $18$ | $9$ | $\{3,6\}$ | $-34+5+11=-18$ |
| $19$ | $9$ | $\{3\}$ | $-43+5=-38$ |
| $21$ | $10$ | $\{6\}$ | $-53+11=-42$ |
| $23$ | $11$ | $\{3,7\}$ | $-64+5+13=-46$ |

Each displayed sum is divisible by its $n$. Balance and connected active support follow exactly from the circuits in Sections 5 and 6, independently of their lower bounds on $n$. In every odd row the listed levels lie below $L$, as required for attachment of the singleton loop. Lemma 2.2 completes each construction. $\square$

## 7.2. Lemma: three additional plans

Actual scalar cycles exist at $n=10,13,16$.

**Proof.** In all three cases choose the chromatic loop $1\to1$.

For $n=10$, the paired levels are $3,4,5$. Choose

$$
B_3,\quad D_4,\quad D_5.
$$

Their active support, including the chromatic loop, is connected because it contains the chain

$$
1\longleftrightarrow-3\longleftrightarrow-1\longleftrightarrow-4,
$$

and these are all its vertices. Every edge belongs to one of the two-edge circuits, so balance holds. The total integer tail sum is

$$
1+(1-3)-4-5=-10.
$$

For $n=13$, the paired levels are $3,4,5,6$ and the singleton is $T_7$. Choose

$$
D_3,\quad X_4\text{ on levels }4,5,\quad B_6,
$$

and form II at the singleton, namely the loop $-6\to-6$. The bridge $X_4$ joins $1$ and $-1$; $D_3$ attaches at $-1$; $B_6$ attaches at $1$ and contains $-6$, to which the singleton loop attaches. Thus the active support is connected, and each of its pieces is a directed circuit or a loop. Its total integer tail sum is

$$
1-3+0+(1-6)-6=-13.
$$

For $n=16$, the paired levels are $3,4,5,6,7,8$. Choose

$$
X_3\text{ on levels }3,4,\quad A_5,\quad B_6,\quad A_7,\quad D_8.
$$

The bridge joins $1,-1$; each other piece is a two-edge circuit attached to one of these vertices. Hence the active support is connected and the plan is balanced. Its total integer tail sum is

$$
1+0+5+(1-6)+7-8=0.
$$

In each case the displayed level pieces use every class exactly once, as specified by the even or odd class partition. Every total sum is zero modulo its respective $n$. Lemma 2.2 therefore gives an actual scalar cycle in each case. $\square$

# 8. The exhaustive classifications

## 8.1. Theorem: scalar cycles

For every integer $n\ge6$,

$$
S_n\quad\Longleftrightarrow\quad n\notin\{6,7,9,11\}.
$$

**Proof.** The exclusions at $6,7,11$ follow from the cited nonexistence of actual cycles; the scalar exclusion at $9$ is the cited result `nine_no_scalar` [F2]. For the converse, every even $n\ge20$ is covered by Theorem 5.1 and every odd $n\ge25$ by Theorem 6.1. The remaining allowed integers are precisely

$$
8,10,12,13,14,15,16,17,18,19,21,23.
$$

They are covered by Lemmas 7.1 and 7.2. Thus every allowed $n$ has an actual cycle with the required scalar presentation at its unique chromatic window. $\square$

## 8.2. Theorem: actual cycles

For every integer $n\ge6$,

$$
C_n\quad\Longleftrightarrow\quad n\notin\{6,7,11\}.
$$

**Proof.** Nonexistence at $6,7,11$ is the cited result of [F2]. For every other $n$ except $9$, Theorem 8.1 gives a scalar cycle, which is an actual cycle by definition. At $n=9$, Feldman's existence theorem `exists_zigzag_nine` [F2] gives an actual cycle. This covers every integer $n\ge6$. $\square$

# 9. Sources and scope of reuse

[F1] David Victor Feldman, *The Missing Zigzag: Cycles of Semitone Trichords and a Conservation Law in Equal Temperament*, arXiv:2609.26114v1, [canonical article](https://arxiv.org/html/2609.26114v1). Definitions 4.1 and 5.1 specify the actual cycles and plans; Theorem 5.2 gives their Eulerian realization; Theorem 8.3 classifies actual zigzag cycles. Section 11 records finite scalar positives but does not give the uniform scalar construction. Paper license: CC BY 4.0.

[F2] DavidVFeldman, *missing-zigzag-new*, [immutable source revision 5da74e8b5a1b19ff724a5c16b3b162c67bf172dd](https://github.com/DavidVFeldman/missing-zigzag-new/tree/5da74e8b5a1b19ff724a5c16b3b162c67bf172dd), `Mzp.lean`: `exists_zigzag_nine`, `six_no_cycle`, `seven_no_cycle`, `eleven_no_cycle`, and `nine_no_scalar`; accompanying `docs/STATUS.md` and `Audit.lean` describe the proof boundaries. Lean source license: Apache-2.0. The finite exclusion theorems concern actual cyclic pitch words, including zero drift; the scalar theorem fixes the chromatic presentation. They are used here as attributed intermediate results.

The scalar construction and subset-sum argument above supply the uniform existence implication. The six forms, Eulerian correspondence, zigzag classification and finite exclusions are Feldman's results. No balance-only counting result is used to infer either classification.

## 追加锚（本行以下为增补区）
