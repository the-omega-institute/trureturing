# The exact finite-exponent boundary for all-word Schatten comparison

## 1. The quantified assertion

For a finite dimension $d$, let $\mathcal H_d=\mathbb C^d$.  If
$A_0,A_1,B_0,B_1$ are positive semidefinite operators on $\mathcal H_d$,
write

$$
\Pi_s(A)=A_{s_1}A_{s_2}\cdots A_{s_\ell},
\qquad
\Pi_s(B)=B_{s_1}B_{s_2}\cdots B_{s_\ell}
$$

for an ordered binary word $s=(s_1,\ldots,s_\ell)$, and put
$\Pi_\varnothing=I_d$.  Eigenvalue multisets always include multiplicity.
For a real $p\geq1$, define $U(p)$ to be the following statement, with all
the displayed quantifiers retained:

> for every finite $d$ and every positive semidefinite quadruple
> $A_0,A_1,B_0,B_1$ on $\mathcal H_d$ satisfying
> $\lambda(A_i)=\lambda(B_i)$ for $i=0,1$, if, for every finite ordered
> binary word $s$, the number $\operatorname{tr}\Pi_s(A)$ is real and
> nonnegative and
> $$
> \operatorname{tr}\Pi_s(A)\geq\left|\operatorname{tr}\Pi_s(B)\right|,
> $$
> imply
> $$
> \lVert B_0+B_1\rVert_p\leq\lVert A_0+A_1\rVert_p,
> $$
> where $\lVert R\rVert_p=(\operatorname{tr}|R|^p)^{1/p}$ and
> $|R|=(R^*R)^{1/2}$.

The convention and the question are those of Alhejji--Knill, *Towards a
Resolution of the Spin Alignment Problem*, Section VI, concluding item 1:
their $\lambda$ is the eigenvalue list with multiplicity and their Schatten
norm is the unnormalised finite-dimensional norm just displayed.  Thus the
empty word, arbitrary finite dimension, and the full all-word quantifier are
part of $U(p)$.

**Theorem 1.1 (exact boundary).**  For every real $p\geq1$,

$$
U(p)\quad\Longleftrightarrow\quad p\in\mathbb Z_{>0}.
$$

The failure of the noninteger direction is witnessed, for every integer
$k\geq1$, by one
commuting positive definite quadruple in dimension $2^{k+1}$ which has equal
sum power traces at orders $1,\ldots,k+1$ and reverses the norm inequality at
every $p\in(k,k+1)$.

*Proof.*  For the positive-integer direction, we reuse the ordered-word
expansion argument in
[the Alhejji--Knill problem dossier](../../../Problems/alhejji-knill-2024-fractional-schatten-alignment.md),
Triage, “A weaker conclusion survives.”  The related argument in
Alhejji--Knill, Theorem IV.7, proves integer-order spin alignment within
their tensor-product family using Corollary IV.6; the dossier gives the
general all-word implication used here.  Let $k\in\mathbb Z_{>0}$ and take
any quadruple in the assertion $U(k)$.  Put $C=A_0+A_1$ and $D=B_0+B_1$.
The sums are positive
semidefinite.  Expanding the noncommutative product gives

$$
\operatorname{tr}(C^k)=\sum_{s\in\{0,1\}^k}\operatorname{tr}\Pi_s(A),
\qquad
\operatorname{tr}(D^k)=\sum_{s\in\{0,1\}^k}\operatorname{tr}\Pi_s(B).
$$

The second sum is real and nonnegative because $D^k$ is positive
semidefinite.  Taking real parts term by term and using
$|z|\geq\operatorname{Re}z$ gives

$$
\operatorname{tr}(D^k)
\leq\sum_s|\operatorname{tr}\Pi_s(B)|
\leq\sum_s\operatorname{tr}\Pi_s(A)
=\operatorname{tr}(C^k).
$$

For a positive semidefinite operator, $\lVert C\rVert_k^k=\operatorname{tr}(C^k)$.
The map $x\mapsto x^{1/k}$ is increasing on $[0,\infty)$, so
$\lVert D\rVert_k\leq\lVert C\rVert_k$, proving $U(k)$.

The quadruples in Sections 2 and 3 disprove $U(p)$ on every open interval
$(k,k+1)$, and every noninteger $p\geq1$ lies in exactly one such interval.
$\square$

## 2. A parity-split construction

The following notation is used for $k\geq2$.  Set

$$
r=k+2,\qquad q=r-1=k+1,\qquad N=2^q,
\qquad \tau=r+2,
$$

and let

$$
E_r=\{j\in\{0,\ldots,r\}:j\equiv r\pmod 2\}.
$$

For $j\in E_r$, take $\binom rj$ coordinate labels.  Of these labels,
$\binom qj$ are marked $\varepsilon=0$ and $\binom q{j-1}$ are marked
$\varepsilon=1$; binomial coefficients outside $0\leq a\leq q$ are zero.
Pascal's identity shows that the total number of labels is

$$
\sum_{j\in E_r}\binom rj=2^{r-1}=N.
$$

Let

$$
c=\frac{\tau+r/2-1}{2},\qquad u=\tau-c=\frac r4+\frac32.
$$

On the $N$ labels define diagonal real matrices by

$$
\begin{aligned}
(A_0)_{j,\varepsilon}&=(B_0)_{j,\varepsilon}=\tau+j-c-\varepsilon,\\
(A_1)_{j,\varepsilon}&=c+\varepsilon,\\
(B_1)_{j,\varepsilon}&=c+1-\varepsilon.
\end{aligned}
\tag{2.1}
$$

All entries are strictly positive: $c>0$ and $u>0$, while
$\tau+j-c-\varepsilon=u+j-\varepsilon\geq u-1>0$.  Hence this is a
commuting positive definite quadruple.

We use the forward difference

$$
\Delta^m f(x)=\sum_{a=0}^m(-1)^{m-a}\binom ma f(x+a).
\tag{2.2}
$$

The parity split in (2.1) gives, for every integer $m\geq0$,

$$
\begin{aligned}
&\sum_{j\in E_r}\binom q{j-1}(u+j-1)^m
-\sum_{j\in E_r}\binom qj(u+j)^m\\
&\hspace{35mm}=\Delta^q(x\mapsto x^m)(u).
\end{aligned}
\tag{2.3}
$$

Indeed, in the first sum put $a=j-1$.  The indices in that sum have the
parity of $q$, whereas those in the second have the opposite parity, and
$(-1)^{q-a}$ is respectively $+1$ and $-1$.  The standard finite-difference
calculus gives

$$
\Delta^q(x\mapsto x^m)(u)\geq0\quad(u\geq0,m\in\mathbb Z_{\geq0}).
\tag{2.4}
$$

For completeness, if $m<q$ the difference is zero; if $m\geq q$, repeated
use of the fundamental theorem of calculus gives

$$
\Delta^q f(u)=\int_{[0,1]^q}f^{(q)}(u+t_1+\cdots+t_q)\,dt_1\cdots dt_q,
$$

and $f^{(q)}(x)=m!/(m-q)!\,x^{m-q}\geq0$.

**Theorem 2.1 (all words and the higher interval).**  The quadruple (2.1)
has equal individual spectra, satisfies the all-ordered-word hypotheses of
$U(p)$, and its sum power traces obey

$$
\operatorname{tr}(A_0+A_1)^\ell
=\operatorname{tr}(B_0+B_1)^\ell
\qquad(\ell=1,\ldots,q),
\tag{2.5}
$$

while, simultaneously for every real $p\in(q-1,q)=(k,k+1)$,

$$
\lVert A_0+A_1\rVert_p<\lVert B_0+B_1\rVert_p.
\tag{2.6}
$$

*Proof.*  The equality $A_0=B_0$ gives the first individual spectral
identity.  The entries of $A_1$ are $c$ and $c+1$ with equal multiplicity:
the two multiplicities are $\sum_{j\in E_r}\binom qj$ and
$\sum_{j\in E_r}\binom q{j-1}$, both $2^{q-1}$.  The matrix $B_1$ interchanges
these two values, so $\lambda(A_1)=\lambda(B_1)$.

For a word with $m$ zeroes and $n$ ones, diagonality makes its trace depend
only on $(m,n)$.  If $n=0$, the two traces are equal because $A_0=B_0$.
If $n>0$, the entries carrying the value $c$ in the $A_1$ trace and the
value $c+1$ in the $B_1$ trace cancel in the difference, and (2.3) yields

$$
\operatorname{tr}\Pi_s(A)-\operatorname{tr}\Pi_s(B)
=\big((c+1)^n-c^n\big)\Delta^q(x\mapsto x^m)(u)\geq0.
\tag{2.7}
$$

Both traces are nonnegative real numbers.  Thus every finite ordered word,
including the empty word, satisfies the required inequality.

The $A$-sum has value $\tau+j$ on the $\binom rj$ labels with index $j$.
For the $B$-sum, the $\varepsilon=0$ labels have value $\tau+j+1$ and the
$\varepsilon=1$ labels have value $\tau+j-1$.  Reindexing by $a=j+1$ and
$a=j-1$ and applying Pascal's identity gives the opposite parity class:

$$
\begin{aligned}
P_A(p)&:=\operatorname{tr}(A_0+A_1)^p
=\sum_{j\in E_r}\binom rj(\tau+j)^p,\\
P_B(p)&:=\operatorname{tr}(B_0+B_1)^p
=\sum_{j\notin E_r}\binom rj(\tau+j)^p.
\end{aligned}
\tag{2.8}
$$

Consequently

$$
P_A(p)-P_B(p)=\Delta^r(x\mapsto x^p)(\tau).
\tag{2.9}
$$

For an integer $\ell=1,\ldots,q=r-1$, the right side is the $r$th
difference of a polynomial of degree $\ell$, hence is zero, proving (2.5).
For $p\in(q-1,q)$ and $x>0$,

$$
\frac{d^r}{dx^r}x^p=p(p-1)\cdots(p-r+1)x^{p-r}<0,
$$

because exactly the last factor $p-(r-1)$ is negative.  The repeated-integral
identity therefore makes the right side of (2.9) strictly negative.  The
diagonal positive-matrix norm identity
$\lVert\operatorname{diag}(d_i)\rVert_p=(\sum_i d_i^p)^{1/p}$ and the
strict increase of $x\mapsto x^{1/p}$ prove (2.6). $\square$

## 3. The first interval and normalization

For $k=1$, use the supplied dimension-four diagonal quadruple after adding
the identity to every member:

$$
\begin{aligned}
A_0=B_0&=\operatorname{diag}(1,2,2,3),\\
A_1&=\operatorname{diag}(2,1,2,3),\\
B_1&=\operatorname{diag}(1,2,3,2).
\end{aligned}
\tag{3.1}
$$

The unshifted quadruple is the diagonal witness
$\operatorname{diag}(0,1,1,2)$,
$\operatorname{diag}(1,0,1,2)$,
$\operatorname{diag}(0,1,2,1)$, with $B_0=A_0$; adding $I$ to all four
matrices preserves every word inequality by expanding each shifted word into
words of the unshifted quadruple.  It also makes all entries positive.
The individual spectra remain equal, and the sum spectra are

$$
\{3,3,4,6\}\quad\text{and}\quad\{2,4,5,5\}.
$$

Their power-sum difference is

$$
2\cdot3^p+6^p-2^p-2\cdot5^p
=\Delta^2(x\mapsto x^p)(4)-\Delta^2(x\mapsto x^p)(2).
\tag{3.2}
$$

The second derivative of $x^p$ is strictly decreasing for $1<p<2$; the
double-integral formula for $\Delta^2$ makes (3.2) strictly negative on that
whole interval.  At $p=1,2$ it is zero.  Thus (3.1) supplies the required
$k=1$ instance, including equality at orders $1$ and $2$.

The quadruples in (3.1) and (2.1) have a common trace on all four members.
For (3.1) that trace is $8$.  For (2.1),

$$
\operatorname{tr}A_1=\operatorname{tr}B_1=(c+\tfrac12)N,
$$

and

$$
\operatorname{tr}A_0=\tau N+\frac r2N-cN-\frac12N
=(c+\tfrac12)N,
$$

with the same value for $B_0$.  Multiplying all four matrices by the common
positive scalar

$$
\gamma=\frac1{\operatorname{tr}A_0}
$$

makes every trace equal to one.  A word of length $\ell$ is multiplied by
$\gamma^\ell$, so all word inequalities and spectral equalities survive;
each sum is multiplied by $\gamma$, so the strict reversal (2.6) survives as
well.  This proves the normalized form of every instance.

The parity split in (2.3), the diagonal Schatten identity, and the scalar
finite-difference argument are the reusable parity, diagonal, calculus, and
word interfaces already represented by the repository's
`ParityConditionedMoments`, `NonintegerForwardDifferenceSignal`,
`DiagonalSingularValues`, `Holder`, and `WordHankelRealization` sources.  The
dimension-four line (3.1) is the shifted supplied witness; the new content is
the jointly realized family (2.1) for all higher intervals and the resulting
exact boundary in Theorem 1.1.

## References

- M. A. Alhejji and E. Knill, *Towards a Resolution of the Spin Alignment
  Problem*, Commun. Math. Phys. 405 (2024), 119,
  DOI [10.1007/s00220-024-04980-1](https://doi.org/10.1007/s00220-024-04980-1),
  arXiv [2307.06894v3](https://arxiv.org/abs/2307.06894v3), Section VI,
  concluding item 1.
- The supplied dimension-four all-word witness and its finite-dimensional
  Schatten convention: `D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation`.
- The source statement with the spectrum-with-multiplicity and finite Schatten
  conventions: `Problems/alhejji-knill-2024-fractional-schatten-alignment.md`.

## 4. Further deductions

The preceding construction is a uniform jointly realized inference for finite
Schatten exponents.  It makes no assertion about $p=\infty$, minimum
dimension, fixed-dimension optimality, tensor-product spin families, strong
alignment, entropy, or the status of any external conjecture.

## 追加锚（本行以下为增补区）
