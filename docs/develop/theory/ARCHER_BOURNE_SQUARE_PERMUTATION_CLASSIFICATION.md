# Indecomposable permutations avoiding 312 and 54321 with 132-avoiding square

This volume is reference input; nothing in it is kernel-verified. Its text is append-only: corrections and additions belong after the final append anchor.

## 1. Scope

Let $a_n$ be the number of permutations $\pi$ of $\{1,\dots,n\}$ that avoid $312$ and $54321$ and whose square $\pi\circ\pi$ avoids $132$, and let $b_n$ be the number of those that are indecomposable. This volume classifies the indecomposable ones completely: for $n\ge9$ there are exactly $\lfloor n/2\rfloor+4$ of them, falling into seven explicit families, and the values for $n\le8$ are determined by the same arguments. With the decomposition of $a$ through $b$ obtained earlier in this project, this gives a rational generating function for $a_n$ and a linear recurrence of order seven valid for $n\ge12$.

## 2. Notation and cited facts

**Cited facts.** (a) K. Archer and N. Bourne, *Pattern avoidance in compositions and powers of permutations*, arXiv:2505.05218v3; published in Discrete Math. Theor. Comput. Sci. 28:1 (Permutation Patterns 2025), DOI 10.46298/dmtcs.17199. In the Introduction a permutation $\pi$ is said to avoid the chain $(\sigma:\tau)$ when $\pi$ avoids $\sigma$ and $\pi^2$ avoids $\tau$, sets of patterns being allowed on either side. Section 5, *Further directions and open questions*, conjectures that $a_n:=a_n(312,54321:132)$ satisfies $a_n=a_{n-1}+a_{n-2}+a_{n-3}+a_{n-4}+n-1$ for $n\ge6$, and proves nothing about this sequence. (b) Obtained earlier in this project and used here only as a cited step: with $b_n$ as in Definition 2.2 and $c_n$ the number of compositions of $n$ into parts of size at most four ($c_0=1$), one has $a_n=\sum_{k=1}^{n}b_k\,c_{n-k}$ for $n\ge1$; equivalently $A(x)=B(x)\,C(x)$ with $A(x)=\sum_{n\ge1}a_nx^n$, $B(x)=\sum_{n\ge1}b_nx^n$ and $C(x)=1/(1-x-x^2-x^3-x^4)$. In the same work the conjecture of (a) was shown to fail at $n=11$ and $n=12$.

**Convention 2.1 (Words and squares).** A permutation $\pi$ of $[n]=\{1,\dots,n\}$ is written as the word $\pi(1)\,\pi(2)\cdots\pi(n)$. For a value $v$ write $\mathrm{pos}(v)=\pi^{-1}(v)$. Throughout, $q=\pi\circ\pi$, so $q(i)=\pi(\pi(i))$. A word of distinct integers contains a pattern $\sigma\in S_k$ when some $k$ of its entries, read left to right, are in the same relative order as $\sigma$; otherwise it avoids $\sigma$. A sequence of positions or entries is read left to right; "right of position $i$" means at a position larger than $i$. Stance: repo-derived (notation fixed in this volume).

**Definition 2.2 (Admissible, indecomposable, $a_n$, $b_n$).** A permutation $\pi$ of $[n]$ is admissible if $\pi$ avoids $312$ and $54321$ and $q=\pi^2$ avoids $132$. It is indecomposable if there is no $k$ with $1\le k<n$ and $\pi(\{1,\dots,k\})=\{1,\dots,k\}$. Let $a_n$ be the number of admissible permutations of $[n]$ and $b_n$ the number of admissible indecomposable ones. Stance: literature-attested for $a_n$ (cited fact (a)); repo-derived for $b_n$ (cited fact (b)).

**Definition 2.3 (The seven families).** For the values of $n$ indicated, define permutations of $[n]$ as follows; inside parentheses an adjacent pair is listed, and "$\cdots$" continues the evident pattern.

- $I_n$ for $n\ge2$: $\pi(t)=t+1$ for $1\le t\le n-1$ and $\pi(n)=1$, that is $2\,3\cdots n\,1$.
- $J_n$ for $n\ge5$: $2\,4\,3\,5\,6\cdots n\,1$.
- $K_{n,j}$ for $n\ge6$ and $0\le j\le\lfloor(n-6)/2\rfloor$: $\pi(1)=2$, $\pi(2)=5$, $\pi(3)=4$, $\pi(2i+2)=2i+5$ and $\pi(2i+3)=2i+4$ for $1\le i\le j$, $\pi(2j+4)=3$, $\pi(t)=t+1$ for $2j+5\le t\le n-1$, $\pi(n)=1$; that is $2\,5\,4\,(7\,6)(9\,8)\cdots(2j{+}5\;\,2j{+}4)\,3\,(2j{+}6)\cdots n\,1$.
- $A_n$ for $n\ge6$: $4\,3\,5\,6\cdots n\,2\,1$, that is $\pi(t)=t+2$ for $3\le t\le n-2$.
- $B_n$ for odd $n\ge7$: $4\,3\,5\,(7\,6)(9\,8)\cdots(n\;\,n{-}1)\,2\,1$, that is $\pi(3)=5$, $\pi(2i)=2i+3$ and $\pi(2i+1)=2i+2$ for $2\le i\le(n-3)/2$, $\pi(n-1)=2$, $\pi(n)=1$.
- $B_n$ for even $n\ge8$: $4\,3\,5\,(7\,6)(9\,8)\cdots(n{-}1\;\,n{-}2)\,2\,n\,1$, that is $\pi(3)=5$, $\pi(2i)=2i+3$ and $\pi(2i+1)=2i+2$ for $2\le i\le(n-4)/2$, $\pi(n-2)=2$, $\pi(n-1)=n$, $\pi(n)=1$.
- $C_n$ for even $n\ge4$: $4\,3\,(6\,5)(8\,7)\cdots(n\;\,n{-}1)\,2\,1$, that is $\pi(2i+1)=2i+4$ and $\pi(2i+2)=2i+3$ for $1\le i\le(n-4)/2$, $\pi(n-1)=2$, $\pi(n)=1$.
- $C_n$ for odd $n\ge5$: $4\,3\,(6\,5)(8\,7)\cdots(n{-}1\;\,n{-}2)\,2\,n\,1$, that is $\pi(2i+1)=2i+4$ and $\pi(2i+2)=2i+3$ for $1\le i\le(n-5)/2$, $\pi(n-2)=2$, $\pi(n-1)=n$, $\pi(n)=1$.
- $D_n$ for $n\ge9$: $4\,3\,6\,7\,5\,8\,9\cdots n\,2\,1$, that is $\pi(3)=6$, $\pi(4)=7$, $\pi(5)=5$, $\pi(t)=t+2$ for $6\le t\le n-2$.

In all families with first entry $4$, $\pi(1)=4$ and $\pi(2)=3$. Thus $C_4=4\,3\,2\,1$, $C_5=4\,3\,2\,5\,1$ and $K_{n,0}=2\,5\,4\,3\,6\cdots n\,1$. Stance: repo-derived (constructions fixed in this volume).

## 3. Reading rules and the shape of an indecomposable member

**Lemma 3.1 (Reading rules).** Let $w$ be a word of distinct integers and $\pi$ a permutation.

(a) $w$ avoids $312$ if and only if, for every position $i$, the entries right of $i$ that are smaller than $w(i)$ appear in decreasing order.

(b) $w$ avoids $132$ if and only if, for every position $i$, the entries right of $i$ that are larger than $w(i)$ appear in increasing order.

(c) If $\pi$ avoids $312$ and $z<w$ are values with $\mathrm{pos}(z)<\mathrm{pos}(w)$, then every entry left of $\mathrm{pos}(z)$ is smaller than $w$.

(d) $w$ avoids both $312$ and $54321$ if and only if, for every position $i$, the entries right of $i$ that are smaller than $w(i)$ form a decreasing word of length at most three.

Stance: repo-derived (elementary reformulations of the definitions).

**Proof.** (a) An occurrence of $312$ is an entry $c$ followed by entries $a<b<c$ in the order $a,b$, that is, an increasing pair among the later entries smaller than $c$. (b) An occurrence of $132$ is an entry $a$ followed by entries $c>b>a$ in the order $c,b$, that is, a decreasing pair among the later entries larger than $a$. (c) An entry $x>w$ left of $\mathrm{pos}(z)$ would give the occurrence $x,z,w$ of $312$. (d) By (a), avoidance of $312$ means that these words decrease; an occurrence of $54321$ starting at position $i$ is a decreasing word of length four among them, and conversely such a word together with $w(i)$ is an occurrence of $54321$. ∎

**Lemma 3.2 (Shape).** Let $n\ge2$ and let $\pi$ be an admissible indecomposable permutation of $[n]$, with $m=\pi(1)$ and $p=\mathrm{pos}(n)$. Then:

(a) $\pi(n)=1$;

(b) $2\le m\le4$, and the values $2,\dots,m-1$ appear right of position $1$ in decreasing order;

(c) $q(p)=1$, $q(n)=m$, $q(p+1)<q(p+2)<\cdots<q(n)$, and $p\ge n-m+1$; in particular $n$ lies in one of the last four positions, and $p=n-1$ when $m=2$;

(d) the entries $\pi(p+1),\dots,\pi(n)$ decrease.

Stance: suspected-novel (see §9).

**Proof.** (a) Write $\pi=\sigma\,1\,\tau$. Every entry of $\sigma$ is smaller than every entry of $\tau$, for otherwise an entry $c$ of $\sigma$ and a smaller entry $b$ of $\tau$ give the occurrence $c,1,b$ of $312$. If $\tau$ were nonempty, then with $k$ the length of $\sigma1$ the first $k$ positions would carry exactly $\{1,\dots,k\}$ with $k<n$, contradicting indecomposability. So $\tau$ is empty. (b) $m\ne1$ by (a) and $n\ge2$. By Lemma 3.1(a) the values $2,\dots,m-1$ appear after $m$ in decreasing order, and $1$ comes last; with $m$ in front this is a decreasing subsequence of length $m$, so $m\le4$ because $\pi$ avoids $54321$. (c) $q(p)=\pi(n)=1$ and $q(n)=\pi(1)=m$. Lemma 3.1(b) at the entry $1$ of $q$ shows that $q(p+1),\dots,q(n)$ increase. These are $n-p$ distinct values in $\{2,\dots,m\}$, so $n-p\le m-1$. If $m=2$ then $p\ge n-1$ and $p\ne n$ by (a). (d) Every entry right of $n$ is smaller than $n$; apply Lemma 3.1(a). ∎

Conversely, every permutation ending in $1$ is indecomposable, since no proper initial segment of positions contains the value $1$.

**Lemma 3.3 (A word avoiding 312 and 321 before its least entry).** Let $u$ be a word of distinct integers that avoids $312$ and $321$, and let $\ell$ be its least entry. Then the entries of $u$ before $\ell$ increase, and each of them is smaller than every entry after $\ell$. Stance: repo-derived (elementary).

**Proof.** Two entries $x>y$ before $\ell$ would give the occurrence $x,y,\ell$ of $321$. An entry $x$ before $\ell$ and an entry $y$ after $\ell$ with $y<x$ would give the occurrence $x,\ell,y$ of $312$. ∎

## 4. First entry two

**Proposition 4.1 (First entry two).** Let $n\ge4$. The admissible indecomposable permutations of $[n]$ with $\pi(1)=2$ are exactly $I_n$; $J_n$ when $n\ge5$; and $K_{n,j}$ for $0\le j\le\lfloor(n-6)/2\rfloor$ when $n\ge6$. Their number is $1$ for $n=4$ and $\lfloor n/2\rfloor$ for $n\ge5$. Stance: suspected-novel (see §9).

**Proof.** Let $\pi$ be admissible and indecomposable with $\pi(1)=2$. By Lemma 3.2, $\pi(n)=1$ and $\pi(n-1)=n$, so $q(n-1)=1$, $q(n)=2$, and $q(1)=\pi(2)=:g$. The positions $2,\dots,n-2$ of $q$ carry the values $\{3,\dots,n\}\setminus\{g\}$. By Lemma 3.1(b) at position $1$ of $q$:

(L) the entries of $q$ in positions $2,\dots,n-2$ that exceed $g$ appear in increasing order.

Since $n\ge4$, position $2$ is not $n-1$, so $3\le g\le n-1$. By Lemma 3.1(a) the values $3,\dots,g-1$ appear after $g$ in decreasing order, and $1$ comes last; together with $g$ this is a decreasing subsequence of length $g-1$, so $g\le5$.

Case $g=3$. Then $g$ is the least of the values $3,\dots,n$ carried by positions $1,\dots,n-2$ of $q$, so by (L) $q(i)=i+2$ for $1\le i\le n-2$. Suppose $\pi(k)=k+1$ for all $k\le i$, where $1\le i\le n-3$; then $q(i)=\pi(i+1)$, so $\pi(i+1)=i+2$. By induction $\pi(t)=t+1$ for $t\le n-2$, and $\pi=I_n$.

Case $g=4$ (so $n\ge5$). Let $b=\mathrm{pos}(3)\ge3$ and $x=\pi^{-1}(b)$, so $q(x)=3$ and $2\le x\le n-2$. By (L) the other positions $2,\dots,n-2$ list $5,\dots,n$ increasingly: $q(i)=i+3$ for $2\le i<x$ and $q(i)=i+2$ for $x<i\le n-2$. If $x>b$, then $b\ge4$ (as $x\ne b$ forces $b\ne3$) and Lemma 3.1(c) with $z=3$, $w=b$ shows that the $b-1$ positions left of $b$ carry values smaller than $b$ and different from $1$, $3$ and $b$, of which there are only $b-3$; impossible. If $x=2$, then $b=\pi(2)=4$, so $\pi(4)=3$, and $q(3)=5$ because $3>x$ and $3\le n-2$. Put $c=\pi(3)$, so $\pi(c)=5$; then $c\notin\{1,2,3,4\}$, and $c\ne5$ since $\pi(3)=c$ and $\pi(c)=5$ would give two positions with value $5$. So $c\ge6$, and $c,3,5$ at positions $3<4<c$ is an occurrence of $312$; impossible. If $x\ge4$ with $x<b$, then $q(2)=5$ gives $\pi(4)=5$, and $q(3)=6$ gives $\pi(c)=6$ for $c=\pi(3)$. Here $c\notin\{2,4,5\}$, $c\ne3$ (else $b=3<x$), and $c\ne6$ (else $\pi(3)=\pi(6)=6$); so $c\ge7$ and $c,5,6$ at positions $3<4<c$ is an occurrence of $312$; impossible. The remaining possibility is $x=3$, that is $q(3)=3$, together with $q(2)=5$ and $q(i)=i+2$ for $4\le i\le n-2$. Then $\pi(4)=5$, and if $\pi(i)=i+1$ for some $4\le i\le n-3$, then $\pi(i+1)=q(i)=i+2$; so $\pi(t)=t+1$ for $4\le t\le n-1$, the remaining value $3$ sits at position $3$, and $\pi=J_n$.

Case $g=5$ (so $n\ge6$). Let $a=\mathrm{pos}(4)$ and $b=\mathrm{pos}(3)$; by Lemma 3.1(a), $3\le a<b\le n-2$. Put $x=\pi^{-1}(a)$ and $y=\pi^{-1}(b)$, so $q(x)=4$, $q(y)=3$, and $x,y\in\{2,\dots,n-2\}$. By (L) the positions $2,\dots,n-2$ other than $x,y$ list $6,\dots,n$ increasingly. Moreover:

(M) if $y<x$ then $x=y+1$, since an entry at a position strictly between $y$ and $x$ is at least $6$ and would form the occurrence $3,q(i),4$ of $132$.

Step 1: $a=3$. Suppose not, and let $c=\pi(3)$. Then $c\notin\{1,2,3,4,5\}$ ($c=3$ would put $3$ before $4$), so $c\ge6$. By Lemma 3.1(a) applied at position $3$, the values $6,\dots,c-1$ cannot appear after the smaller entry $4$, so they occupy positions in $\{4,\dots,a-1\}$.

If $3\notin\{x,y\}$, then $q(3)\ge6$; since position $3$ is the first or the second of the positions listing $6,7,\dots$, we have $q(3)\in\{6,7\}$, and $q(3)=7$ forces $q(2)=6$. Now $\pi(c)=q(3)$. If $c=6$, then $\pi(6)\ne6$, so $\pi(6)=7$, hence $q(2)=6$, that is $\pi(5)=6=\pi(3)$; impossible. If $c\ge7$, then $\pi(c)\in\{6,7\}$ lies in $\{6,\dots,c-1\}$, so $c\le a-1$, and $c,\pi(c),4,3,1$ at positions $3<c<a<b<n$ is an occurrence of $54321$; impossible.

If $3\in\{x,y\}$, then $c\in\{a,b\}$. If $c=a$, then $x=3$ and $a\ge6$. The case $y=2$ would mean $\pi(2)=b$, that is $b=5$, which is impossible as $b>a\ge6$; hence position $2$ lists $6$, and $\pi(5)=q(2)=6$. If $a=6$ this gives $\pi(5)=\pi(3)=6$; if $a\ge7$ then $a,6,4,3,1$ at positions $3<5<a<b<n$ is an occurrence of $54321$. If $c=b$, then $y=3$ and $b\ge6$. If $b\ge7$, the value $6$ lies at a position in $\{4,\dots,a-1\}$ and $b,6,4,3,1$ is an occurrence of $54321$. If $b=6$, then $a\in\{4,5\}$ and $\pi(6)=3$. The case $x=2$ would mean $\pi(2)=a$, that is $a=5$; then positions $4,\dots,n-2$ list $6,7,\dots$, so $q(4)=6$, that is $\pi(\pi(4))=6$ and $\pi(4)=\mathrm{pos}(6)=3$, which repeats the value $3=\pi(6)$. So $x\ge4$, and by (M) $x=4$, that is $\pi(4)=a$; as $\pi(2)=5$, this forces $a=4$. Then position $2$ lists $6$, so $\pi(5)=6=\pi(3)$; impossible.

Step 2: the family $K_{n,j}$. Now $\pi(3)=4$, so $x=\pi^{-1}(3)=b$, and $y=\pi^{-1}(b)$.

If $b=4$, then $y=3$, $x=4$, so positions $2$ and $5,\dots,n-2$ list $6,\dots,n$: $\pi(5)=q(2)=6$ and $q(i)=i+2$ for $5\le i\le n-2$. If $\pi(i)=i+1$ for some $5\le i\le n-3$, then $\pi(i+1)=q(i)=i+2$; so $\pi(t)=t+1$ for $5\le t\le n-1$ and $\pi=K_{n,0}$.

If $b=5$, then $q(2)=\pi(5)=3$, so $y=2<x=5$, contradicting (M).

Let $b\ge6$. If $y>b$, Lemma 3.1(c) with $z=3$, $w=b$ shows that the $b-1$ positions left of $b$ carry values smaller than $b$ and different from $1$, $3$, $b$, of which there are $b-3$; impossible. So $y<b=x$, and $y\notin\{2,3\}$ because $\pi(2)=5$ and $\pi(3)=4$ differ from $b$. By (M), $y=b-1$, that is $\pi(b-1)=b$. Hence the listing gives

$$
q(i)=i+4\quad(2\le i\le b-2),\qquad q(b-1)=3,\qquad q(b)=4,\qquad q(i)=i+2\quad(b+1\le i\le n-2).
$$

Claim: for every even $k$ with $2\le k\le b-1$ we have $\pi(k)=k+3$ and $\pi(k+1)=k+2$. For $k=2$ this is $\pi(2)=5$, $\pi(3)=4$. If it holds for an even $k$ with $k+2\le b-1$, then $k+1\le b-2$, so $q(k+1)=\pi(\pi(k+1))=\pi(k+2)$ equals $k+5$, and $q(k)=\pi(\pi(k))=\pi(k+3)$ equals $k+4$; this is the claim for $k+2$. If $b$ is odd, the claim for $k=b-1$ gives $\pi(b-1)=b+2$, contradicting $\pi(b-1)=b$. So $b$ is even, $b=2j+4$ with $j\ge1$, and the claim gives $\pi(2i+2)=2i+5$, $\pi(2i+3)=2i+4$ for $1\le i\le j$. Further $q(b-2)=\pi(\pi(b-2))=\pi(b+1)$ equals $b+2$, and if $\pi(i)=i+1$ for some $b+1\le i\le n-3$, then $\pi(i+1)=q(i)=i+2$; so $\pi(t)=t+1$ for $b+1\le t\le n-1$. Since $b\le n-2$, $j\le\lfloor(n-6)/2\rfloor$, and $\pi=K_{n,j}$.

Admissibility. Each listed permutation ends in $1$, hence is indecomposable. For $I_n$, $q=3\,4\cdots n\,1\,2$. For $J_n$, $q=4\,5\,3\,6\,7\cdots n\,1\,2$. For $K_{n,j}$, direct substitution of Definition 2.3 gives

$$
q(1)=5,\qquad q(i)=i+4\ (2\le i\le 2j+2),\qquad q(2j+3)=3,\qquad q(2j+4)=4,\qquad q(i)=i+2\ (2j+5\le i\le n-2),
$$

with $q(n-1)=1$ and $q(n)=2$; that is $q=5\,6\cdots(2j{+}6)\,3\,4\,(2j{+}7)\cdots n\,1\,2$. In each of the three squares, the entries larger than any given entry and to its right increase, so $q$ avoids $132$ by Lemma 3.1(b). For the permutations themselves we list, for each entry, the later entries smaller than it. In $I_n$ every entry is followed only by the smaller entry $1$. In $J_n$ these words are $3\,1$ for the entry $4$ and $1$ for every other entry except the final one. In $K_{n,j}$ they are $4\,3\,1$ for the entry $5$; $3\,1$ for the entry $4$; $2i{+}4\;\,3\,1$ for the first entry $2i+5$ of an adjacent pair; $3\,1$ for its second entry $2i+4$; and $1$ for the entries $2$, $3$ and $t\ge2j+6$. Each of these words decreases and has length at most three, so $I_n$, $J_n$, $K_{n,j}$ avoid $312$ and $54321$ by Lemma 3.1(d).

Counting: for $n\ge6$ the count is $2+\lfloor(n-6)/2\rfloor+1=\lfloor n/2\rfloor$, for $n=5$ it is $2$, and for $n=4$ it is $1$. ∎

## 5. First entry three

**Proposition 5.1 (First entry three).** For $n\ge5$ no admissible indecomposable permutation of $[n]$ has $\pi(1)=3$. Stance: suspected-novel (see §9).

**Proof.** Let $\pi$ be one, with $p=\mathrm{pos}(n)$ and $t=\mathrm{pos}(2)$. By Lemma 3.2, $\pi(n)=1$, $q(n)=3$ and $p\in\{n-2,n-1\}$.

If $p=n-1$, then $q(n-1)=1$. Let $q(i_2)=2$; then $i_2<n-1$. By Lemma 3.1(b) at $i_2$, the entries right of $i_2$ that exceed $2$ increase, and the last of them is $q(n)=3$; so no entry at a position strictly between $i_2$ and $n-1$ exists, and $i_2=n-2$. Thus $\pi(\pi(n-2))=2$, that is $\pi(n-2)=t$. As $t\le n-2$ and $t=n-2$ would give $\pi(n-2)=n-2$ with $\pi(t)=2$, that is $n=4$, we have $t\le n-3$. As a value, $t\notin\{1,2,3\}$: $t=2$ would give $\pi(2)=2$ and $\pi(n-2)=2$ at two positions, and $\pi(1)=3$. So $t\ge4$, the value $2$ sits at position $t$, and the value $t$ at the later position $n-2$. Lemma 3.1(c) shows that the $t-1$ positions left of $t$ carry values smaller than $t$ and different from $1$ and $2$, of which there are $t-3$; impossible.

If $p=n-2$, then $q(n-2)=1$ and $q(n-1)<q(n)=3$, so $q(n-1)=2$. Put $v=\pi(n-1)$, so $\pi(v)=2$. Here $v\ne2$ (else $q(n-1)=\pi(2)=2$, putting $2$ at two positions), $v\ne3=\pi(1)$, and $v\notin\{1,n\}$; so $v\ge4$, and the value $2$ sits at position $v\le n-3$ while the value $v$ sits at position $n-1$. Lemma 3.1(c) again shows that the $v-1$ positions left of $v$ carry values in $\{3,\dots,v-1\}$, of which there are $v-3$; impossible. ∎

## 6. First entry four

**Lemma 6.1 (The tail of the square).** Let $n\ge4$ and let $\pi$ be admissible and indecomposable with $\pi(1)=4$. Then $q(n-3),\dots,q(n)$ is a permutation of $\{1,2,3,4\}$ with $q(n)=4$, and consequently

$$
\{\pi(n-3),\pi(n-2),\pi(n-1)\}=\{n,\ \mathrm{pos}(2),\ \mathrm{pos}(3)\}.
$$

Stance: suspected-novel (see §9).

**Proof.** $q(n)=\pi(1)=4$. For $k\in\{1,2,3\}$ let $p_k$ be the position of $k$ in $q$. By Lemma 3.1(b) the entries right of $p_k$ that exceed $k$ increase, and the last of them is $q(n)=4$; so they all lie in $\{k+1,\dots,4\}$. Entries right of $p_k$ smaller than $k$ lie in $\{1,2\}$. Hence every entry right of $P=\min(p_1,p_2,p_3)$ is at most $4$; together with $q(P)\le3$ this shows that positions $P,\dots,n$ carry exactly $\{1,2,3,4\}$, so $P=n-3$. Finally $q(i)=1$ iff $\pi(i)=n$, $q(i)=2$ iff $\pi(i)=\mathrm{pos}(2)$, and $q(i)=3$ iff $\pi(i)=\mathrm{pos}(3)$, because $\pi(n)=1$. ∎

**Lemma 6.2 (Second entry and tail types).** Let $n\ge5$ and let $\pi$ be admissible and indecomposable with $\pi(1)=4$. Then $\pi(2)=3$, and $(\pi(n-3),\pi(n-2),\pi(n-1))$ is one of

$$
T_1=(n,\ n-1,\ 2),\qquad T_2=(n-1,\ n,\ 2),\qquad T_3=(n-2,\ 2,\ n).
$$

Stance: suspected-novel (see §9).

**Proof.** Put $s_3=\mathrm{pos}(3)$ and $s_2=\mathrm{pos}(2)$. By Lemma 3.2(b), $2\le s_3<s_2\le n-1$. By Lemma 6.1 the values $s_3$ and $s_2$ lie at positions in $\{n-3,n-2,n-1\}$.

The second entry. Suppose $s_3\ge4$. If the value $s_3$ lies right of position $s_3$, Lemma 3.1(c) with $z=3$, $w=s_3$ shows that the $s_3-1$ positions left of $s_3$ carry values in $\{4,\dots,s_3-1\}$ (the values $1,2,3$ lie at $n$, $s_2>s_3$ and $s_3$), of which there are $s_3-4$; impossible. If it lies left of $s_3$, then $s_3>n-3$, so $s_3=n-2$, $s_2=n-1$, and the value $n-2$ lies at position $n-3$; then $\pi(n-2)=3$ and $\pi(n-1)=2$, so $\{\pi(n-3),\pi(n-2),\pi(n-1)\}=\{n-2,3,2\}$, which by Lemma 6.1 must equal $\{n,n-1,n-2\}$; impossible for $n\ge5$. Suppose $s_3=3$, that is $\pi(3)=3$. By Lemma 6.1, $q(3)=3$ lies in the last four positions, so $n\le6$. Put $v=\pi(2)\ge5$. By Lemma 3.1(a) at position $2$, the values $5,\dots,v-1$ cannot follow the smaller entry $3$, and they cannot occupy positions $1,2$; so $v=5$, and $q(2)=\pi(5)$. For $n=5$ this gives $q(2)=\pi(5)=1$ and $q(3)=3$ inside the tail $q(2),\dots,q(5)$ with $q(5)=4$, so $q(4)=2$ and $1,3,2$ is an occurrence of $132$. For $n=6$ the entries $q(1),q(2)$ are $5,6$ in some order; $q(2)=\pi(5)\ne5$ because $\pi(2)=5$, so $\pi(5)=6$ and $q(1)=\pi(4)=5=\pi(2)$; impossible. Hence $s_3=2$, that is $\pi(2)=3$.

The tail. As $s_2\ge3$, if the value $s_2$ lay right of position $s_2$, Lemma 3.1(c) with $z=2$, $w=s_2$ would leave the $s_2-1$ positions left of $s_2$ with values in $\{3,\dots,s_2-1\}$, of which there are $s_2-3$; impossible. So the value $s_2$ lies left of position $s_2$ and at a position at least $n-3$, whence $s_2\in\{n-2,n-1\}$. By Lemma 6.1 the last three positions before $n$ carry $\{n,s_2,2\}$. If $s_2=n-1$, then $\pi(n-1)=2$ and positions $n-3,n-2$ carry $n$ and $n-1$: this is $T_1$ or $T_2$. If $s_2=n-2$, then $\pi(n-2)=2$, the value $n-2$ lies left of $n-2$ and at least at $n-3$, so $\pi(n-3)=n-2$, and $\pi(n-1)=n$: this is $T_3$. ∎

**Lemma 6.3 (The middle).** Let $n\ge7$ and $\pi$ be as in Lemma 6.2. Call $M=\pi(3)\,\pi(4)\cdots\pi(n-4)$ the middle. Its set of values is $V=\{5,\dots,n-2\}$ for $T_1,T_2$ and $V=\{5,\dots,n-3\}\cup\{n-1\}$ for $T_3$. The middle avoids $312$ and $321$, and for $T_3$ its last entry is $\pi(n-4)=n-1$. Stance: suspected-novel (see §9).

**Proof.** The value sets follow from $\pi(1)=4$, $\pi(2)=3$, $\pi(n)=1$ and the tail type. A $321$ in $M$ followed by $2$ and $1$, which lie right of position $n-4$, would be a $54321$ in $\pi$. In $T_3$ every entry of $M$ other than $n-1$ is smaller than $n-2$; if such an entry $e$ lay after $n-1$ in $M$, then $n-1,e,n-2$ would be an occurrence of $312$, as $n-2$ sits at position $n-3$. ∎

**Proposition 6.4 (First entry four, $n\ge8$).** Let $n\ge8$. The admissible indecomposable permutations of $[n]$ with $\pi(1)=4$ are exactly $A_n$, $B_n$, $C_n$, and in addition $D_n$ when $n\ge9$. Stance: suspected-novel (see §9).

**Proof.** Let $\pi$ be one. Since $n\ge8$, $5\in V$; let $w=\mathrm{pos}(5)$, so $3\le w\le n-4$, and $w\le n-5$ for $T_3$ by Lemma 6.3. By Lemmas 6.3 and 3.3, the entries of $M$ before $5$ increase and are the $w-3$ least values of $V\setminus\{5\}$, which are $6,\dots,w+2$ (all of them lie in $V$ because $w+2\le n-2$, and $w+2\le n-3$ for $T_3$). Hence

$$
\pi(i)=i+3\quad(3\le i\le w-1),\qquad \pi(w)=5.
$$

The values of $q$ in positions $1,\dots,n-4$ are $5,\dots,n$ (Lemma 6.1), and $q(i)=5$ exactly for $i=\pi^{-1}(w)$. By Lemma 3.1(b) at this position, all later entries among positions $1,\dots,n-4$ increase.

Case $w=4$. Then $\pi(3)=6$, $\pi(4)=5$, and $q(1)=\pi(4)=5$, so $q(i)=i+4$ for $1\le i\le n-4$. Claim: for odd $k\ge3$ with $k+1\le n-2$, $\pi(k)=k+3$ and $\pi(k+1)=k+2$. This holds for $k=3$. If it holds for an odd $k$ with $k+1\le n-4$, then $q(k)=\pi(k+3)=k+4$ and $q(k+1)=\pi(k+2)=k+5$, which is the claim for $k+2$. For even $n$ the claim with $k+1=n-2$ gives $\pi(n-3)=n$, $\pi(n-2)=n-1$, so the type is $T_1$ and $\pi=C_n$. For odd $n$ it gives $\pi(n-4)=n-1$ and $\pi(n-3)=n-2$, so the type is $T_3$ and $\pi=C_n$.

Case $w=3$. Then $\pi(3)=5$ and $q(2)=\pi(\pi(2))=\pi(3)=5$, so $q(3),\dots,q(n-4)$ increase. Put $h=q(1)=\pi(4)\ge6$. If $h=6$, then $q(i)=i+4$ for $3\le i\le n-4$; if $\pi(i)=i+2$ for some $3\le i\le n-4$, then $\pi(i+2)=q(i)=i+4$; from $\pi(3)=5$, $\pi(4)=6$ this gives $\pi(t)=t+2$ for $3\le t\le n-2$, the type is $T_2$, and $\pi=A_n$. If $h\ge7$, then $q(3)=6$, so $\pi(5)=6$; by Lemma 3.1(a) at position $4$ the values $7,\dots,h-1$ cannot follow the entry $6$ at position $5$, and positions $1,\dots,4$ carry $4,3,5,h$; hence $h=7$ and $q(i)=i+4$ for $4\le i\le n-4$. Claim: for even $k\ge4$ with $k+1\le n-2$, $\pi(k)=k+3$ and $\pi(k+1)=k+2$. This holds for $k=4$. If it holds for an even $k$ with $k+1\le n-4$, then $q(k)=\pi(k+3)=k+4$ and $q(k+1)=\pi(k+2)=k+5$, the claim for $k+2$. For odd $n$, the claim with $k+1=n-2$ gives $\pi(n-3)=n$, $\pi(n-2)=n-1$, type $T_1$, and $\pi=B_n$. For even $n$ it gives $\pi(n-4)=n-1$, $\pi(n-3)=n-2$, type $T_3$, and $\pi=B_n$.

Case $w=5$ (so $n\ge9$). Then $\pi(3)=6$, $\pi(4)=7$, $\pi(5)=5$, so $q(5)=5$, $q(1)=7$, $q(2)=6$. By Lemma 3.1(b) at position $2$, the entries of $q$ in positions $3,\dots,n-4$ that exceed $6$ increase; these are all of them except $q(5)=5$, and their values are $8,\dots,n$. So $q(3)=\pi(6)=8$, $q(4)=\pi(7)=9$ and $q(i)=i+4$ for $6\le i\le n-4$. If $\pi(i)=i+2$ for some $6\le i\le n-4$, then $\pi(i+2)=q(i)=i+4$; hence $\pi(t)=t+2$ for $6\le t\le n-2$, the type is $T_2$, and $\pi=D_n$.

Case $w\ge6$. Then $\pi(3)=6$, $\pi(4)=7$, $\pi(5)=8$, so $q(1)=7$, $q(2)=6$, and $q(w)=\pi(\pi(w))=\pi(5)=8$. If $w\ge7$, then $q(3)=\pi(6)=9$, and $6,9,8$ at positions $2<3<w$ is an occurrence of $132$. If $w=6$, then $n\ge10$; the values $1,\dots,8$ occupy positions $1,\dots,6$, $\mathrm{pos}(2)\ge n-2$ and $n$, so $\pi(7)\ge9$ and $q(4)=\pi(7)\ge9$, and $6,q(4),8$ at positions $2<4<6$ is an occurrence of $132$. Both are impossible.

Admissibility. Each of $A_n,B_n,C_n,D_n$ ends in $1$. Substituting Definition 2.3, their squares are

$$
\begin{aligned}
A_n&:\ 6\,5\,7\,8\cdots n\,2\,1\,3\,4, \\
B_n&:\ 7\,5\,6\,8\,9\cdots n\,1\,2\,3\,4\ \ (n\text{ odd}),\qquad 7\,5\,6\,8\,9\cdots n\,2\,3\,1\,4\ \ (n\text{ even}), \\
C_n&:\ 5\,6\cdots n\,1\,2\,3\,4\ \ (n\text{ even}),\qquad 5\,6\cdots n\,2\,3\,1\,4\ \ (n\text{ odd}), \\
D_n&:\ 7\,6\,8\,9\,5\,10\,11\cdots n\,2\,1\,3\,4.
\end{aligned}
$$

In each square, the first $n-4$ entries are the values $5,\dots,n$ and are followed by a block of $1,2,3,4$ ending in $4$; the larger entries right of any entry increase (in the head one checks $6\,5\,7\cdots$, $7\,5\,6\,8\cdots$, $5\,6\cdots$ and $7\,6\,8\,9\,5\,10\cdots$ directly, and the tail blocks $2134$, $1234$, $2314$ have this property), so each square avoids $132$ by Lemma 3.1(b). For the permutations themselves we list, for each entry, the later entries smaller than it. In all four families the entry $4$ is followed by the smaller entries $3\,2\,1$, the entry $3$ by $2\,1$, and the entry $2$ by $1$. For the entry $n$ in a final segment $2\,n\,1$ the word is $1$. Every other entry $e$ lies strictly between the entries $3$ and $2$, and its word is: in $A_n$, $2\,1$; in $B_n$ and $C_n$, $f\,2\,1$ when $e$ is the first entry of an adjacent pair whose second entry is $f$, and $2\,1$ otherwise; in $D_n$, $5\,2\,1$ for $e\in\{6,7\}$ and $2\,1$ otherwise. Each of these words decreases and has length at most three, so $A_n$, $B_n$, $C_n$, $D_n$ avoid $312$ and $54321$ by Lemma 3.1(d). ∎

**Proposition 6.5 (First entry four, small sizes).** For $n=4,5,6,7$, the admissible indecomposable permutations of $[n]$ with $\pi(1)=4$ are exactly $C_4$; $C_5$; $A_6$ and $C_6$; and $A_7$, $B_7$, $C_7$, respectively. Stance: suspected-novel (see §9).

**Proof.** For $n=4$, Lemma 3.2(b) forces $\pi=4\,3\,2\,1=C_4$, and $q$ is the identity. Let $5\le n\le7$; by Lemma 6.2, $\pi(1)=4$, $\pi(2)=3$, $\pi(n)=1$, and positions $n-3,n-2,n-1$ follow $T_1$, $T_2$ or $T_3$. For $n=5$, position $n-3=2$ carries $3=n-2$, which excludes $T_1$ and $T_2$; $T_3$ gives $4\,3\,2\,5\,1=C_5$. For $n=6$ no position lies between $2$ and $n-3$; $T_1$ gives $C_6$, $T_2$ gives $A_6$, and $T_3$ would put $n-2=4$ at position $3$. For $n=7$ only position $3$ lies between, and it carries the unique value of $V$ (Lemma 6.3): $5$ for $T_1$ and $T_2$, giving $B_7$ and $A_7$, and $6$ for $T_3$, giving $C_7$. All of these are admissible by the admissibility part of the proof of Proposition 6.4, whose computations of squares, of $312$ and of $54321$ hold verbatim for $A_n$ with $n\ge6$, $B_n$ with $n\ge7$ and $C_n$ with $n\ge4$. ∎

## 7. Classification, counts and the generating function

**Theorem 7.1 (Classification for $n\ge9$).** Let $n\ge9$. An indecomposable permutation $\pi$ of $[n]$ avoids $312$ and $54321$ and has $\pi^2$ avoiding $132$ if and only if $\pi$ is one of

- $I_n=2\,3\cdots n\,1$;
- $J_n=2\,4\,3\,5\cdots n\,1$;
- $K_{n,j}=2\,5\,4\,(7\,6)\cdots(2j{+}5\;\,2j{+}4)\,3\,(2j{+}6)\cdots n\,1$ for $0\le j\le\lfloor(n-6)/2\rfloor$;
- $A_n=4\,3\,5\,6\cdots n\,2\,1$;
- $D_n=4\,3\,6\,7\,5\,8\cdots n\,2\,1$;
- for odd $n$: $B_n=4\,3\,5\,(7\,6)(9\,8)\cdots(n\;\,n{-}1)\,2\,1$ and $C_n=4\,3\,(6\,5)(8\,7)\cdots(n{-}1\;\,n{-}2)\,2\,n\,1$;
- for even $n$: $B_n=4\,3\,5\,(7\,6)(9\,8)\cdots(n{-}1\;\,n{-}2)\,2\,n\,1$ and $C_n=4\,3\,(6\,5)(8\,7)\cdots(n\;\,n{-}1)\,2\,1$.

Stance: suspected-novel (see §9).

**Proof.** By Lemma 3.2(b), $\pi(1)\in\{2,3,4\}$. Proposition 4.1 gives the members with $\pi(1)=2$, Proposition 5.1 excludes $\pi(1)=3$, and Proposition 6.4 gives the members with $\pi(1)=4$; all listed permutations are admissible and indecomposable by the admissibility parts of these proofs. ∎

**Theorem 7.2 (The numbers $b_n$).** $b_1=1$, $b_2=1$, $b_3=2$, $b_4=3$, $b_5=3$, $b_6=5$, $b_7=6$, $b_8=7$, and

$$
b_n=\left\lfloor\frac n2\right\rfloor+4\qquad(n\ge9).
$$

Stance: suspected-novel (see §9).

**Proof.** For $n\ge9$, the families of Theorem 7.1 are pairwise distinct (they differ in the first two entries, or in the position of $3$ within the family $K_{n,j}$), and their number is $\lfloor n/2\rfloor+4$ by Proposition 4.1. For $5\le n\le8$, Propositions 4.1, 5.1, 6.4 and 6.5 give $\lfloor n/2\rfloor$ members with first entry $2$ and $1,2,3,3$ members with first entry $4$, that is $3,5,6,7$. For $n=1$ the only permutation qualifies. For $n\ge2$, $\pi(n)=1$ by Lemma 3.2(a). For $n=2$ only $2\,1$ remains, and its square is the identity. For $n=3$ the candidates are $2\,3\,1$ and $3\,2\,1$, with squares $3\,1\,2$ and $1\,2\,3$; both qualify. For $n=4$, Lemma 3.2(b) and the avoidance of $312$ leave $2\,3\,4\,1$, $2\,4\,3\,1$, $3\,2\,4\,1$, $3\,4\,2\,1$ and $4\,3\,2\,1$, with squares $3\,4\,1\,2$, $4\,1\,3\,2$, $4\,2\,1\,3$, $2\,1\,4\,3$ and $1\,2\,3\,4$; the second and fourth contain $132$ (as $1\,3\,2$ and $1\,4\,3$), so $b_4=3$. ∎

**Remark 7.3 (The conjectured recurrence).** By cited fact (b), $a_n=a_{n-1}+a_{n-2}+a_{n-3}+a_{n-4}+b_n$ for $n\ge5$, so the recurrence of cited fact (a) holds at a given $n\ge6$ exactly when $b_n=n-1$. Theorem 7.2 gives $b_n=n-1$ for $6\le n\le10$ and $b_n=\lfloor n/2\rfloor+4<n-1$ for every $n\ge11$, so the conjectured recurrence holds for $6\le n\le10$ and fails for every $n\ge11$. Stance: the failure at $n=11$ and $n=12$ and the reduction to $b_n=n-1$ are repo-derived (cited fact (b)); the failure for every $n\ge13$ is suspected-novel (see §9).

**Corollary 7.4 (Generating functions and recurrence).** With $A(x)=\sum_{n\ge1}a_nx^n$ and $B(x)=\sum_{n\ge1}b_nx^n$,

$$
B(x)=\frac{x+x^4-x^5+x^6+x^7-x^8-x^{11}}{(1-x)(1-x^2)},\qquad
A(x)=\frac{x+x^4-x^5+x^6+x^7-x^8-x^{11}}{(1-x)(1-x^2)(1-x-x^2-x^3-x^4)},
$$

and for every $n\ge12$

$$
a_n=2a_{n-1}+a_{n-2}-2a_{n-3}-a_{n-5}+a_{n-7}.
$$

Stance: suspected-novel (see §9); the passage from $B$ to $A$ uses cited fact (b).

**Proof.** Put $b_0=0$ and $e_n=b_n-b_{n-1}-b_{n-2}+b_{n-3}$, with $b_k=0$ for $k<0$; then $(1-x)(1-x^2)B(x)=(1-x-x^2+x^3)B(x)=\sum_{n\ge0}e_nx^n$. For $n\ge12$ all four indices are at least $9$, and with $f(k)=\lfloor k/2\rfloor$

$$
e_n=\bigl(f(n)-f(n-2)\bigr)-\bigl(f(n-1)-f(n-3)\bigr)=1-1=0 .
$$

For $0\le n\le11$, Theorem 7.2 gives $b_0,\dots,b_{11}=0,1,1,2,3,3,5,6,7,8,9,9$, and the definition of $e_n$ gives $e_1=1$, $e_4=1$, $e_5=-1$, $e_6=1$, $e_7=1$, $e_8=-1$, $e_{11}=-1$, and $e_n=0$ for the other $n\le11$ (for instance $e_9=8-7-6+5=0$ and $e_{11}=9-9-8+7=-1$). This is the stated form of $B(x)$, and cited fact (b) gives $A(x)=B(x)/(1-x-x^2-x^3-x^4)$. Expanding,

$$
(1-x)(1-x^2)(1-x-x^2-x^3-x^4)=1-2x-x^2+2x^3+x^5-x^7,
$$

so $A(x)\,(1-2x-x^2+2x^3+x^5-x^7)$ is a polynomial of degree $11$. Comparing the coefficients of $x^n$ for $n\ge12$, with $a_k=0$ for $k\le0$, gives the recurrence. ∎

## 8. Boundaries and open questions

**Remark 8.1 (What is not claimed).** This volume makes no statement about the chains $(312,k\cdots21:\sigma)$ for other $k$ or other patterns $\sigma$, and none about permutations whose square avoids a pattern other than $132$. The recurrence of Corollary 7.4 is asserted only for $n\ge12$. The decomposition of cited fact (b) and the failure of the conjectured recurrence at $n=11$ and $n=12$ were obtained earlier in this project and are not claimed here. Stance: repo-derived.

**Open question 8.2 (Other chains).** Archer and Bourne ask, in Section 5 of the paper in cited fact (a), for the enumeration of $a_n(312,k\cdots21:\sigma)$ beyond the cases they settle. For $k=5$ and $\sigma=132$ this volume reduces the question to the classification above; the analogous classification of the indecomposable members for $k\ge6$, where the first entry of an indecomposable member may be as large as $k-1$ by the argument of Lemma 3.2(b), is open. Stance: repo-derived (question posed in this volume).

## 9. Sources and literature status

| Source | Exact scope and use |
| --- | --- |
| K. Archer, N. Bourne, *Pattern avoidance in compositions and powers of permutations*, arXiv:2505.05218v3, Introduction and Section 5; Discrete Math. Theor. Comput. Sci. 28:1 (Permutation Patterns 2025), DOI 10.46298/dmtcs.17199 | `literature-attested`: the chain notation, the definition of $a_n(312,54321:132)$ and the wording of the conjectured recurrence for $n\ge6$ (cited fact (a)); the paper proves nothing about this sequence. |
| R. Simion, F. W. Schmidt, *Restricted permutations*, European J. Combin. 6 (1985) 383–406 | `literature-attested`: enumeration of the permutations avoiding each set of patterns of length three, among them the pair $312,321$ whose local structure appears in Lemma 3.3. Lemma 3.3 is proved here in full and does not depend on this source. |
| — | `repo-derived`: Convention 2.1, Definitions 2.2 (for $b_n$) and 2.3, Lemmas 3.1 and 3.3, Remark 8.1, Open question 8.2; the decomposition $A=B\,C$ and the failure of the conjectured recurrence at $n=11,12$ (cited fact (b), obtained earlier in this project and used as cited steps, not load-bearing items of this volume). |
| — | `suspected-novel`: Lemma 3.2, Propositions 4.1, 5.1, 6.4, 6.5, Lemmas 6.1, 6.2, 6.3, Theorems 7.1, 7.2, Remark 7.3 for $n\ge13$, Corollary 7.4. Searched: the full text of arXiv:2505.05218v3; the arXiv and DMTCS listings returned by searches for the title and identifier; the OEIS for the terms $1,2,5,11,22,45,89,174,338,655,1265$ of $a_n$, which returned no match; web searches combining Archer, Bourne, chain avoidance, square of a permutation, $312$, $54321$ and $132$. No statement of these results was found in the searched scope; this establishes no worldwide priority. |

<!-- 追加区自下一行的「追加锚」开始。每批增补写在锚之后,并以一行新的、逐字相同的追加锚结尾。 -->

## 追加锚（本行以下为增补区）
