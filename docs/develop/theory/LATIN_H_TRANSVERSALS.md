# Three explicit transversals of the Ghafari–Wanless H family

## 1. The square and its transversal obstruction

**Definition 1.1 (coordinates and transversals).** Let $k\ge9$ be an
integer and put $n=4k$. Rows, columns and symbols belong to
$\mathbb Z_n$, represented by $0,\ldots,n-1$. A transversal is a set
of $n$ entries containing each row, column and symbol exactly once.
An entry is pinned if it belongs to every transversal and at least one
transversal exists. All coordinate expressions below are reduced modulo
$n$; inequalities and interval endpoints are ordinary integers.

**Definition 1.2 (the source square).** Define
$H_n[a,b]=a+b+\delta(a,b)\pmod n$, where the first applicable line in
the following table gives $\delta$. The branch tests use the standard
representatives of $a,b$. This is equation (7) of Afsane Ghafari and
Ian M. Wanless, *Latin Squares whose transversals intersect in unusual
ways*, arXiv:2607.17547v1, §3, DOI
[10.48550/arXiv.2607.17547](https://doi.org/10.48550/arXiv.2607.17547),
hereafter [GW].

| $\delta(a,b)$ | Condition, in priority order |
| --- | --- |
| $4$ | $a\in\{0,5,10\},\ b\equiv1\pmod4,\ b-4a/5\ne1$ |
| $3$ | $(a,b)\in\{(1,1),(6,5),(11,9)\}$ |
| $1$ | $a\in\{0,5,10\},\ 1\le b-4a/5\le4$ |
| $-1$ | $a\in\{1,6,11\},\ 2\le b-4(a-1)/5\le4$ |
| $-4$ | $a\in\{4,9,14\},\ b\equiv1\pmod4$ |
| $2$ | $15\le a<n-21,\ a\equiv3\pmod4,\ b\equiv0\pmod2$ |
| $-2$ | $15\le a<n-21,\ a\equiv1\pmod4,\ b\equiv0\pmod2$ |
| $0$ | Otherwise |

Write
$$
d_0=(1,1,5),\qquad d_1=(6,5,14),\qquad d_2=(11,9,23),
\qquad D=\{d_0,d_1,d_2\}.
$$
For an entry $(a,b,c)$, let $\Delta(a,b,c)$ be the integer congruent
to $c-a-b$ in $(-n/2,n/2]$. Since $n\ge36$, the displayed
$\delta(a,b)$ is exactly $\Delta(a,b,H_n[a,b])$.

**Assumption 1.3 (HLatinness, cited source theorem).** For the parameters
in Definition 1.1, the array in Definition 1.2 is Latin. This is the
Latinness assertion accompanying equation (7) in [GW]; it is used as a
literature premise here.

**Lemma 1.4 (the source obstruction and maximum supports).** Every
transversal of $H_n$ contains at least two members of $D$. Hence any
two transversals intersect. If a transversal omits $d_j$, where
$j\in\{0,1,2\}$, then its columns satisfy the following supports;
the right-hand column is its $\Delta$-value in that row.

| Row | Allowed columns $b$ | $\Delta$ |
| --- | --- | --- |
| $5h,\ h=0,1,2$ | $b\equiv1\pmod4,\ b\ne4h+1$ | $4$ |
| $1+5h,\ h\in\{0,1,2\}\setminus\{j\}$ | $b=4h+1$ | $3$ |
| $1+5j$ | $b\notin\{4j+1,4j+2,4j+3,4j+4\}$ | $0$ |
| $4,9,14$ | $b\not\equiv1\pmod4$ | $0$ |
| $15+4t,\ 0\le t<k-9$ | $b$ even | $2$ |
| $17+4t,\ 0\le t<k-9$ | $b$ odd | $0$ |
| All remaining rows | Any $b$ | $0$ |

Proof. This is the row-bound argument of [GW, Lemmas 5 and 8], with its
equality case made explicit. For any transversal $T$, summing the row,
column and symbol permutations gives
$$
\sum_{e\in T}\Delta(e)\equiv
-\sum_{a=0}^{n-1}a\equiv2k\pmod{4k}.
$$
The sum of row minima in Definition 1.2 is
$3(-1-4)-2(k-9)=-2k+3$. If at most one member of $D$ is selected,
the row maxima sum to at most $3\cdot4+3+2(k-9)=2k-3$.
There is no integer congruent to $2k$ modulo $4k$ between those
bounds. Every transversal therefore contains at least two members of
the three-element set $D$, proving pairwise intersection.

If $d_j$ is omitted, the other two members of $D$ must be selected.
The corresponding maximum sum is $3\cdot4+2\cdot3+2(k-9)=2k$.
The only admissible value between $-2k+3$ and $2k$ is $2k$.
Every row must attain its maximum, since the sum of its nonnegative
deficits is zero. Reading the equality cases from Definition 1.2 gives
exactly the support table. In particular the omitted distinguished row
must avoid its four exceptional columns, not merely its member of $D$.
$\square$

## 2. Three explicit formulas

**Definition 2.1 (bulk and caps).** Put $m=k-9$ and
$(s_0,s_1,s_2)=(0,-4,0)$. For $j=0,1,2$, define column and symbol
functions $\pi_j,\sigma_j:\mathbb Z_n\to\mathbb Z_n$ as follows.
For $0\le t<m$, the four bulk rows are $a=15+4t+r$, with
$r=0,1,2,3$, and their values are
$$
\begin{array}{c|cc}
r&\pi_j(15+4t+r)&\sigma_j(15+4t+r)\\ \hline
0&12+s_j-2t&29+s_j+2t\\
1&2k+10+s_j-2t&2k+26+s_j+2t\\
2&-1+s_j-2t&16+s_j+2t\\
3&2k+1+s_j-2t&2k+19+s_j+2t
\end{array}
$$
The other 36 rows, called the cap rows, are $0,\ldots,14$ and
$n-21,\ldots,n-1$. Their columns are the following literal formulas.
The superscripts E and O mean even and odd $k$, respectively.

| $a$ | $\pi_0^{\mathrm E}$ | $\pi_0^{\mathrm O}$ | $\pi_1^{\mathrm E}$ | $\pi_1^{\mathrm O}$ | $\pi_2^{\mathrm E}$ | $\pi_2^{\mathrm O}$ |
| --- | --- | --- | --- | --- | --- | --- |
| $0$ | $13$ | $17$ | $5$ | $5$ | $9$ | $9$ |
| $1$ | $18$ | $18$ | $1$ | $1$ | $1$ | $1$ |
| $2$ | $3$ | $11$ | $13$ | $2k+7$ | $7$ | $19$ |
| $3$ | $2k+9$ | $7$ | $3$ | $3$ | $16$ | $16$ |
| $4$ | $2k+16$ | $2k+16$ | $2k+12$ | $2k+12$ | $2k+16$ | $7$ |
| $5$ | $2k+5$ | $2k+3$ | $2k+1$ | $2k-1$ | $2k+5$ | $2k+3$ |
| $6$ | $5$ | $5$ | $11$ | $11$ | $5$ | $5$ |
| $7$ | $2k+3$ | $2k+7$ | $14$ | $14$ | $18$ | $18$ |
| $8$ | $2k+14$ | $2k+14$ | $2k+10$ | $7$ | $2k+14$ | $2k+14$ |
| $9$ | $16$ | $16$ | $10$ | $10$ | $14$ | $14$ |
| $10$ | $1$ | $1$ | $-3$ | $-3$ | $13$ | $13$ |
| $11$ | $9$ | $9$ | $9$ | $9$ | $2k+7$ | $2k+9$ |
| $12$ | $2k+12$ | $2k+12$ | $2k+8$ | $2k+8$ | $2k+12$ | $2k+12$ |
| $13$ | $14$ | $14$ | $2k-1$ | $2k+1$ | $2k+3$ | $2k+5$ |
| $14$ | $7$ | $3$ | $-1$ | $-1$ | $3$ | $3$ |
| $n-21$ | $22$ | $22$ | $18$ | $18$ | $22$ | $22$ |
| $n-20$ | $2k+24$ | $28$ | $2k+18$ | $2k+26$ | $2k+24$ | $28$ |
| $n-19$ | $26$ | $24$ | $20$ | $20$ | $26$ | $26$ |
| $n-18$ | $2k+26$ | $2k+24$ | $22$ | $22$ | $2k+26$ | $2k+20$ |
| $n-17$ | $28$ | $26$ | $2k+26$ | $24$ | $2k+30$ | $2k+28$ |
| $n-16$ | $2k+22$ | $2k+26$ | $2k+20$ | $2k+14$ | $24$ | $2k+16$ |
| $n-15$ | $24$ | $2k+30$ | $2k+11$ | $2k+11$ | $2k+15$ | $2k+13$ |
| $n-14$ | $2k+30$ | $2k+18$ | $24$ | $13$ | $2k+20$ | $2k+30$ |
| $n-13$ | $2k+15$ | $20$ | $2k+7$ | $16$ | $2k+28$ | $2k+26$ |
| $n-12$ | $20$ | $15$ | $15$ | $2k+16$ | $2k+22$ | $24$ |
| $n-11$ | $2k+11$ | $2k+9$ | $2k+22$ | $2k+5$ | $2k+9$ | $2k+15$ |
| $n-10$ | $2k+28$ | $2k+28$ | $2k+24$ | $2k+20$ | $20$ | $20$ |
| $n-9$ | $2k+7$ | $2k+11$ | $16$ | $2k+22$ | $2k+11$ | $2k+24$ |
| $n-8$ | $11$ | $19$ | $7$ | $2k+10$ | $11$ | $11$ |
| $n-7$ | $17$ | $2k+15$ | $2k+13$ | $2k+18$ | $28$ | $2k+17$ |
| $n-6$ | $19$ | $2k+22$ | $2k+14$ | $2k+24$ | $17$ | $15$ |
| $n-5$ | $2k+20$ | $2k+5$ | $2k+5$ | $15$ | $2k+17$ | $2k+22$ |
| $n-4$ | $2k+17$ | $2k+17$ | $12$ | $12$ | $19$ | $2k+18$ |
| $n-3$ | $15$ | $2k+20$ | $2k+16$ | $2k+3$ | $15$ | $2k+11$ |
| $n-2$ | $2k+13$ | $2k+13$ | $2k+9$ | $2k+9$ | $2k+13$ | $17$ |
| $n-1$ | $2k+18$ | $13$ | $2k+3$ | $2k+13$ | $2k+18$ | $2k+7$ |

On these cap rows put
$$
\varepsilon_j(a)=
\begin{cases}
4,&a\in\{0,5,10\},\\
3,&a=1+5h,\quad h\in\{0,1,2\}\setminus\{j\},\\
0,&\text{otherwise},
\end{cases}
\qquad
\sigma_j(a)=a+\pi_j(a)+\varepsilon_j(a)\pmod n.
$$
In particular $\sigma_j(n-\ell)=\pi_j(n-\ell)-\ell$ for
$1\le\ell\le21$. Finally set
$T_j=\{(a,\pi_j(a),\sigma_j(a)):a\in\mathbb Z_n\}$.

## 3. Source values and coordinate partitions

**Lemma 3.1 (source compatibility).** For every $k\ge9$, every
$j\in\{0,1,2\}$, and every row $a$,
$\sigma_j(a)=H_n[a,\pi_j(a)]$. All chosen columns satisfy the
corresponding support in Lemma 1.4, and $T_j\cap D=D\setminus\{d_j\}$.

Proof. The head, bulk and tail rows are disjoint and exhaust the row
set: the bulk is $15,\ldots,n-22$, with $4(k-9)$ rows, and the tail
starts at $n-21\ge15$. When $k=9$, the bulk is empty and the tail
starts at 15.

In bulk class $r=0$ the column is even and the source increment is
$2$. In class $r=2$ the column is odd and the increment is $0$.
The rows in classes $r=1,3$ are unmodified. Thus the four increments
are $(2,0,0,0)$; adding row and column gives exactly the four symbol
formulas in Definition 2.1. The shift $-4$ preserves these guards;
no symmetry of the entire square is required. Every tail row is outside
the modified head and bulk ranges, so its increment is zero.

For the head rows $0,5,10$, the three profiles use respectively
$$
\begin{array}{c|ccc}
j&\pi_j(0)&\pi_j(5)\ (k\text{ even};\ k\text{ odd})&\pi_j(10)\\ \hline
0&13\ (k\text{ even}),\ 17\ (k\text{ odd})&2k+5;\ 2k+3&1\\
1&5&2k+1;\ 2k-1&-3\\
2&9&2k+5;\ 2k+3&13
\end{array}
$$
Each is $1\pmod4$, and differs from the exceptional column $1,5,9$
in its respective row. Here $-3$ has standard representative $n-3>9$.
All three source increments are therefore $4$.

In the distinguished rows $1,6,11$, profile $j$ retains the literal
columns of the other two entries of $D$, giving increment $3$.
The omitted rows use respectively $18$, $11$, and $2k+7$ for even
$k$ or $2k+9$ for odd $k$. These avoid respectively
$\{1,2,3,4\}$, $\{5,6,7,8\}$, and $\{9,10,11,12\}$, giving
increment $0$. In rows $4,9$, the head table uses even columns,
except for $\pi_2(4)=7$ when $k$ is odd. In row 14 it uses $7$
or $3$ for $j=0$, $-1\equiv n-1$ for $j=1$, and $3$ for
$j=2$. None is $1\pmod4$. All other head rows are unmodified.

These head guards concern standard representatives: all the displayed
nonnegative head columns are at most $\max(19,2k+16)<4k$ and are
nonnegative for $k\ge9$. The two negative head columns $-3,-1$
have representatives $n-3,n-1$. The prescribed cap increment
$\varepsilon_j$ consequently equals the actual source increment in
every row, proving the identity and the asserted distinguished entries.
$\square$

**Lemma 3.2 (uniform coordinate partitions).** Each $\pi_j$ and
$\sigma_j$ in Definition 2.1 is a permutation of $\mathbb Z_n$.

Proof. For an even coordinate $x$, take its half-index $x/2$ modulo
$2k$; for an odd coordinate take $(x-1)/2$ modulo $2k$. First use
shift $s=0$. Write $C_r,S_r$ for the bulk column and symbol images
of class $r$. Their half-index images, together with their complements,
are the following consecutive interval partitions. Each interval includes
both endpoints, and $[u,u-1]$ is empty.

| Coordinate parity | First cap block | First bulk block | Second cap block | Second bulk block |
| --- | --- | --- | --- | --- |
| Even columns | $[7,14]$ | $C_1:[15,k+5]$ | $[k+6,k+15]$ | $C_0:[k+16,2k+6]$ |
| Odd columns | $[0,9]$ | $C_3:[10,k]$ | $[k+1,k+8]$ | $C_2:[k+9,2k-1]$ |
| Even symbols | $[4,7]$ | $S_2:[8,k-2]$ | $[k-1,k+12]$ | $S_1:[k+13,2k+3]$ |
| Odd symbols | $[0,13]$ | $S_0:[14,k+4]$ | $[k+5,k+8]$ | $S_3:[k+9,2k-1]$ |

For example, the raw half-indices of $C_0$ are $6-t$, with image
$[16-k,6]$; adding $2k$ gives the displayed $[k+16,2k+6]$.
Those of $C_2$ are $-1-t$, with image $[9-k,-1]$; adding $2k$
gives $[k+9,2k-1]$. The other column half-indices are $k+5-t$ and
$k-t$. The symbol half-indices for classes $0,1,2,3$ are respectively
$14+t,k+13+t,8+t,k+9+t$, giving the four displayed symbol blocks.

Each line is a consecutive block of length $2k$. Its two bulk blocks
each have length $k-9$; its cap block lengths are respectively
$(8,10),(10,8),(4,14),(14,4)$. Reduction modulo $2k$ is bijective
on each whole block, so all cross-class disjointness follows. Each bulk
parametrization is injective, since its half-index has step $1$ or
$-1$ and $k-9<2k$. At $k=9$, both bulk intervals in every line
are empty and the two cap intervals still concatenate without overlap.

Write $[u,v]_2=\{u,u+2,\ldots,v\}$, reduced modulo $4k$. The unused
columns and symbols of this bulk are therefore the disjoint unions
$$
\begin{aligned}
C={}&[14,28]_2\ \cup[2k+12,2k+30]_2
       \ \cup[1,19]_2\ \cup[2k+3,2k+17]_2,\\
S={}&[8,14]_2\ \cup[2k-2,2k+24]_2
       \ \cup[1,27]_2\ \cup[2k+11,2k+17]_2.
\end{aligned}
$$
Both sets have 36 elements. For shift $s=-4$, every bulk coordinate
is translated by $-4$, and every half-index by $-2$. Thus subtracting
$2$ from every endpoint in the partition table proves the corresponding
partitions, with complements $C-4,S-4$. This translation argument
concerns coordinate sets only; Lemma 3.1 already supplies the source
identity for that shift.

For completeness, the cap multiset identities can be read directly as
identities of affine expressions, before reduction of their values.
Represent (qk+b) by the pair $(q,b)$, reducing $q$ modulo $4$
after adding a tail row. The cap column table, in each of its six
columns, lists once each precisely the following pairs:
$$
\begin{split}
\mathcal C_s={}&\{(0,14+s+2u):0\le u<8\}
 \cup\{(2,12+s+2u):0\le u<10\}\\
 &\cup\{(0,1+s+2u):0\le u<10\}
 \cup\{(2,3+s+2u):0\le u<8\},
\end{split}
$$
where $s=s_j$ for both parities. Substitution into the cap symbol
rule lists once each precisely
$$
\begin{split}
\mathcal S_s={}&\{(0,8+s+2u):0\le u<4\}
 \cup\{(2,-2+s+2u):0\le u<14\}\\
 &\cup\{(0,1+s+2u):0\le u<14\}
 \cup\{(2,11+s+2u):0\le u<4\}.
\end{split}
$$
These equalities involve only the fixed cap table and integer addition:
add $a+\varepsilon_j(a)$ for a head row, or subtract (ell) for
row $n-\ell$. For example, the $j=1$ even cap at row $n-17$
has column $2k+26$ and symbol $2k+9$, and its row 10 has column
$-3$ and symbol $11$. They give pairs $(2,9)$ and $(0,11)$
in $\mathcal S_{-4}$.

The pair sets represent exactly $C+s,S+s$. The interval partitions
show that their residues are distinct for every $k\ge9$, even when
some displayed expressions are negative or exceed $4k-1$. Thus each
cap fills exactly the unused columns and symbols of its own bulk, with
no repetitions. Both coordinate functions are permutations. $\square$

## 4. Exact intersection and the H-family theorem

**Lemma 4.1 (exact common entry).** For every $k\ge9$,
$T_0\cap T_1=\{d_2\}$ and $T_0\cap T_1\cap T_2=\varnothing$.

Proof. Two entries in this square coincide if and only if their row and
column coincide. In every bulk row, $\pi_0(a)-\pi_1(a)=4$, which is
nonzero modulo $4k$. For the cap rows, the complete differences from
Definition 2.1 are as follows.

| Row $a$ | $\pi_0(a)-\pi_1(a)$, even $k$ | $\pi_0(a)-\pi_1(a)$, odd $k$ |
| --- | --- | --- |
| $0$ | $8$ | $12$ |
| $1$ | $17$ | $17$ |
| $2$ | $-10$ | $-2k+4$ |
| $3$ | $2k+6$ | $4$ |
| $4$ | $4$ | $4$ |
| $5$ | $4$ | $4$ |
| $6$ | $-6$ | $-6$ |
| $7$ | $2k-11$ | $2k-7$ |
| $8$ | $4$ | $2k+7$ |
| $9$ | $6$ | $6$ |
| $10$ | $4$ | $4$ |
| $11$ | $0$ | $0$ |
| $12$ | $4$ | $4$ |
| $13$ | $-2k+15$ | $-2k+13$ |
| $14$ | $8$ | $4$ |
| $n-21$ | $4$ | $4$ |
| $n-20$ | $6$ | $-2k+2$ |
| $n-19$ | $6$ | $4$ |
| $n-18$ | $2k+4$ | $2k+2$ |
| $n-17$ | $-2k+2$ | $2$ |
| $n-16$ | $2$ | $12$ |
| $n-15$ | $-2k+13$ | $19$ |
| $n-14$ | $2k+6$ | $2k+5$ |
| $n-13$ | $8$ | $4$ |
| $n-12$ | $5$ | $-2k-1$ |
| $n-11$ | $-11$ | $4$ |
| $n-10$ | $4$ | $8$ |
| $n-9$ | $2k-9$ | $-11$ |
| $n-8$ | $4$ | $-2k+9$ |
| $n-7$ | $-2k+4$ | $-3$ |
| $n-6$ | $-2k+5$ | $-2$ |
| $n-5$ | $15$ | $2k-10$ |
| $n-4$ | $2k+5$ | $2k+5$ |
| $n-3$ | $-2k-1$ | $17$ |
| $n-2$ | $4$ | $4$ |
| $n-1$ | $15$ | $-2k$ |

Only row 11 has zero difference. Every nonzero constant has absolute
value at most 19. Every nonconstant difference has form $\pm2k+b$
with $|b|\le15$, so
$$
0<2k-15\le |\pm2k+b|\le2k+15<4k\qquad(k\ge9).
$$
The constants likewise have absolute value strictly between $0$ and
$4k$. None can vanish modulo $4k$. The common entry in row 11 is
$(11,9,23)=d_2$, by Lemma 3.1. Finally $\pi_2(11)-9$ is $2k-2$
for even $k$ and $2k$ for odd $k$, strictly between $0$ and $4k$.
Thus $T_2$ avoids $d_2$, proving the empty triple intersection.
The bounds also cover $k=9$, when there are no bulk rows. $\square$

**Theorem 4.2 (three transversals and no pinned entry).** For every
integer $k\ge9$, assuming the cited HLatinness assertion 1.3, the
square $H_{4k}$ of [GW, equation (7)] has the three explicit transversals
$T_0,T_1,T_2$ of Definition 2.1, satisfying
$$
T_j\cap D=D\setminus\{d_j\}\quad(j=0,1,2),\qquad
T_0\cap T_1=\{d_2\},\qquad T_0\cap T_1\cap T_2=\varnothing.
$$
Every two transversals of $H_{4k}$ intersect, but $H_{4k}$ has no
pinned entry.

Proof. Lemmas 3.1 and 3.2 give one actual source entry in every row,
column and symbol for each $T_j$, hence three transversals. Lemma 4.1
gives the stated intersections. The intersection over all transversals
is contained in their empty triple intersection, so no entry is pinned.
Lemma 1.4 gives pairwise intersection for all transversals of the square.
$\square$

**Conjecture 4.3 (the larger question, [GW, Conjecture 3]).** For every
even integer $n\ge28$, there exists a Latin square of order $n$
having no two disjoint transversals and no pinned entry. Theorem 4.2
concerns only $n=4k\ge36$; it does not establish this all-even
assertion. The uniform no-pinned-entry problem for the source family
$G_{4k+2}$ and the existence question at order 30 lie outside its
conclusion. The finite cases $n=28$ and even $32\le n\le10000$,
including the H-family cases $9\le k\le2500$, are already established
in [GW, Theorem 6 and §3].

## 追加锚（本行以下为增补区）
