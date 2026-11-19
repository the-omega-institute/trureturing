# Three-Sector Circulant Construction

This is mathematical reference input, authored by Codex (AI) on 2026-09-29
from Dalfó, Fiol, and Reyes, *A note on three-quarters circulant digraphs*,
*Utilitas Mathematica* 128 (2026), section 2, Conjecture 2.4,
[arXiv:2609.33718v1](https://arxiv.org/html/2609.33718v1), and the supplied
generic construction note. The source conjecture supplies the parameters and
three-sector distance; the arguments below supply the claimed deductions.
Only Lean declarations and their axiom closure carry formal truth in this
repository. The numbered statements below are formalization targets, not
independent certificates.

For an integer $k\ge 1$, put $c=k+4$, $q=k-1$, $d=k+2$, and
$N=qc+d=k^2+4k-2$. In $\mathbb Z/N\mathbb Z$ put $a=1$ and $b=-c$.
The three source sectors consist of $ma+nb$, $-ma+nb$, and $ma-nb$ for
nonnegative integers $m,n$ with $m+n\le r$; repetitions are permitted.

## theorem 1.1: Exact integer lattice

For every integer $k\ge1$, let $u=(k+2,1-k)$ and $v=(2,k)$ in $\mathbb Z^2$.
Their determinant is $N$, and the kernel of
$(x,y)\mapsto x-cy\pmod N$ is exactly $\mathbb Zu+\mathbb Zv$.

The integer values of $x-cy$ on $u$ and $v$ are $N$ and $-N$.
Conversely, if $x-cy=Nt$ for an integer $t$, then

$$
(x,y)=(y+kt)u+(y+(k-1)t)v.
$$

Expansion gives both coordinates, so the two inclusions and determinant
follow without an index theorem.

## theorem 1.2: Coverage by the three source sectors

For every integer $k\ge1$ and every residue $z\in\mathbb Z/N\mathbb Z$,
some nonnegative $m,n$ with $m+n\le k$ represent $z$ in one of the three
source sectors.

Choose the representative $0\le w<N$ and write $w=nc+r$ with
$n=\lfloor w/c\rfloor$ and $0\le r<c$. Since $0<d<c$ and $N=qc+d$,
$n\le q$. If $r\le k-n$, choose $m=r$; then $w=m-nb=m+nc$.
Otherwise put $j=q-n$. For $r\le d$, set $m=d-r$. The inequality
$r>k-n$ gives $m\le n+1$, while $w=N-jc-m$ is the sector
$-ma+jb$ modulo $N$. For $r>d$, set $m=r-d$. Since $r<c=d+2$,
$m\le1\le n+1$, and $w=N-jc+m$ is the sector $ma+jb$ modulo $N$.
In either case $m+j\le(n+1)+(q-n)=k$.

## theorem 1.3: Exact-radius witness

For every integer $k\ge1$, residue $k$ has no representation in any of
the three source sectors with $m+n\le k-1$.

Put $H=m+nc$ and suppose $m+n\le q=k-1$. Since $c>0$,
$H\le(m+n)c\le qc$, so $0<k+H<N=qc+k+2$. If $ma-nb=m+nc$
represented $k$, both natural representatives would be below $N$ and
$H=k$. For $n=0$ this requires $m=k>q$; for $n>0$ it gives
$H\ge c>k$. If $ma+nb=m-nc$ represented $k$, the two representatives
$k+nc$ and $m$ would be below $N$ and equal, contrary to $m\le q<k$.
If $-ma+nb=-H$ represented $k$, then $k+H$ would be a positive multiple
of $N$ strictly below $N$. All three cases are impossible.

## theorem 1.4: Degree-two range

For every integer $k\ge2$, the residues $a=1$ and $b=-c$ in
$\mathbb Z/N\mathbb Z$ are nonzero and distinct. Consequently the set
$\{z+a,z+b\}$ has cardinality two for every vertex $z$.

Here $q=k-1\ge1$ and $N=qc+d>k+5>c>1$. A zero $a$ would force
$N\mid1$; a zero $b$ would force $N\mid c$; equality $a=b$ would force
$N\mid(k+5)$. Each divisibility contradicts the displayed strict bound.

At $k=1$, $N=3$ and $b=-5=1=a$ modulo $3$, so the set of outgoing
neighbors has cardinality one. This does not affect the preceding sector
coverage, exact-radius witness, or lattice equality. It does contradict the
paper's degree-two graph convention when that convention is imposed on the
literal $k\ge1$ quantifier.

## 2. Source boundary

Section 2 of the paper defines arcs as a set of ordered pairs, constructs
$CD(N,a,b)$ from the generating set $\{a,b\}$, and repeats degree two as
property P1. Its three-sector distance is a separate rule for path lengths.
The paper's distinct $k=1$ example $TQ(5,1,2)$ is not the $N=3$ instance
specified in Conjecture 2.4. The finite generator assertion above starts at
$k=2$; the first three theorem statements retain $k=1$.

## 追加锚（本行以下为增补区）
