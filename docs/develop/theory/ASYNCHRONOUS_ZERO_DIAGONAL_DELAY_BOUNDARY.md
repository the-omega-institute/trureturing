# Zero-diagonal asynchronous iteration: exact radius and stability boundary

## 1. Block model and signed family

**Definition 1.1 (Constant-delay history operator).** Let $\ell\ge1$, let
$n_1,\ldots,n_\ell$ be positive integers, and put
$E=\bigoplus_{i=1}^{\ell}\mathbb R^{n_i}$. For a real block matrix
$M=(M_{ij})$ on $E$ and a constant array
$\delta\in\mathbb Z_{\ge0}^{\ell\times\ell}$ with $\delta_{ii}=0$, choose
an integer $K\ge\max_{i,j}\delta_{ij}$. The history operator
$B_{\delta,K}$ on $E^{K+1}$, with slot zero newest, is

$$
\begin{aligned}
(B_{\delta,K}y)_{0,i}
  &=\sum_{j=1}^{\ell}M_{ij}y_{\delta_{ji},j},\\
(B_{\delta,K}y)_{s,i}&=y_{s-1,i}\qquad(1\le s\le K).
\end{aligned}
\tag{1.1}
$$

Thus $x_i(t+1)=\sum_jM_{ij}x_j(t-\delta_{ji})$ for $t\ge0$,
with arbitrary prescribed real history $x(-K),\ldots,x(0)$.
Convergence means $x(t)\longrightarrow0$ for every such history.
The spectrum and spectral radius are taken after complexification;
$\rho(T)=\max\{|z|:z\in\operatorname{spec}_{\mathbb C}(T)\}$.
A positive remote-delay array has $\delta_{ij}\ge1$ whenever $i\ne j$.
The larger class of nonnegative remote-delay arrays permits zero there.

This is the recurrence and history convention of Ortiz Marrero and Young,
“Price of Asynchrony,” in Aksoy et al., *Seven open problems in applied
combinatorics*, [arXiv:2303.11464v1, source
`Sections/ratfish.tex`, Problem Statement and Lemmas `L:spectra`,
`L:uniform`](https://arxiv.org/src/2303.11464v1).
In the existing block-coordinate definition
[`Vtx`](../../../D5/S3/Combinatorics/Graph/MultipartiteCHS/Defs.lean),
$E$ has coordinates $(i,a)$ with $1\le i\le\ell$ and
$1\le a\le n_i$, corresponding to the zero-based pair
$(i-1,a-1)$ in `Vtx`; (1.1) is the same entry rule as
[`asyncMatrix`](../../../D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.lean).
The parameter correspondence is $\ell\leftrightarrow\ell$,
$n_i\leftrightarrow n(i-1)$, $K\leftrightarrow k$, and source-to-destination
delay $j\to i\leftrightarrow\delta_{ji}$, with history coordinates
$(s,(i,a))$.

**Assumption 1.2 (Parameter domain).** Throughout Sections 1–3 and 5,
$\lambda,c$ are real numbers satisfying

$$
0<\lambda<1,\qquad c\ge\lambda^2,\qquad d=c-\lambda^2\ge0.
\tag{1.2}
$$

**Definition 1.3 (Three scalar blocks).** With three blocks of size one,
set

$$
M=\begin{pmatrix}
0&1&1\\
c&0&0\\
-d&0&0
\end{pmatrix},\qquad
\delta_* =\begin{pmatrix}
0&1&2\\
1&0&1\\
2&1&0
\end{pmatrix},\qquad B=B_{\delta_*,2}.
\tag{1.3}
$$

All diagonal blocks of $M$ vanish. The delay array is symmetric,
independent of both parameters, and has strictly positive remote
entries with maximum two. Delays on zero matrix entries have no effect
on the recurrence. In particular,

$$
\begin{aligned}
x_1(t+1)&=x_2(t-1)+x_3(t-2),\\
x_2(t+1)&=c\,x_1(t-1),\\
x_3(t+1)&=-d\,x_1(t-2).
\end{aligned}
\tag{1.4}
$$

The zero-diagonal restriction is the block-Jacobi restriction discussed
in the Experimental Results of the cited v1 section. The unrestricted
power-bound and subunit-bound alternatives already have the two-scalar-block
counterexample in
[`AsynchronousIterationSpectralRadiusRefutation.result`](../../../D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.lean)
and its [problem statement and zero-diagonal residual](../../../Problems/aksoy-et-al-2023-asynchronous-iteration-spectral-radius-refutation.md).
That matrix has nonzero diagonal entries; the family (1.3) imposes the
additional zero-diagonal constraint.

## 2. Exact delayed spectrum, radius range and power threshold

**Theorem 2.1 (Exact family spectrum and endpoints).** Under (1.2),

$$
\operatorname{spec}(M)=\{0,\lambda,-\lambda\},\qquad
\rho(M)=\lambda,
\tag{2.1}
$$

and $M$ is diagonalizable over $\mathbb R$. There is exactly one
positive real number $r$ satisfying

$$
r^6=c\,r^2+d.
\tag{2.2}
$$

For the nine-dimensional history operator in (1.3),

$$
\det(zI_9-B)=z^3(z^6-cz^2+d),\qquad \rho(B)=r.
\tag{2.3}
$$

Consequently,

$$
\begin{aligned}
\rho(B)<1&\iff c<\frac{1+\lambda^2}{2},\\
\rho(B)=1&\iff c=\frac{1+\lambda^2}{2},\\
\rho(B)>1&\iff c>\frac{1+\lambda^2}{2}.
\end{aligned}
\tag{2.4}
$$

If $c>\lambda^2$, the only eigenvalues of modulus $r$ are $ir$ and
$-ir$, each of algebraic multiplicity one. At the boundary in (2.4)
they are $i$ and $-i$. At $c=\lambda^2$, instead,
$r=\sqrt\lambda$ and the peripheral eigenvalues are the four simple
values $r,-r,ir,-ir$. Enlarging the history from two preceding iterates
to any $K\ge2$ only adds zero eigenvalues, with multiplicity $3(K-2)$.

**Proof.** Expanding the determinant along the first row gives

$$
\det(zI_3-M)=z\bigl(z^2-c+d\bigr)
           =z(z-\lambda)(z+\lambda).
$$

The three roots are distinct. More explicitly, $(0,1,-1)^{\mathsf T}$
is a zero eigenvector, and, for $s\in\{\lambda,-\lambda\}$,
$(s,c,-d)^{\mathsf T}$ is an eigenvector with eigenvalue $s$:
its image is $(c-d,cs,-ds)^{\mathsf T}$ and $s^2=c-d$.
Eigenvectors for distinct eigenvalues are linearly independent,
so they form a real eigenbasis and prove (2.1).

In the order $(x(t),x(t-1),x(t-2))$, (1.4) gives

$$
B=\begin{pmatrix}0&P&Q\\I_3&0&0\\0&I_3&0\end{pmatrix},\qquad
P=\begin{pmatrix}0&1&0\\c&0&0\\0&0&0\end{pmatrix},\qquad
Q=\begin{pmatrix}0&0&1\\0&0&0\\-d&0&0\end{pmatrix}.
\tag{2.5}
$$

For $z\ne0$, eliminate the last two block rows in $zI_9-B$.
Their diagonal block determinant is $z^6$, and the Schur complement is
$zI_3-z^{-1}P-z^{-2}Q$. Hence

$$
\begin{aligned}
\det(zI_9-B)
 &=z^6\det\begin{pmatrix}
 z&-z^{-1}&-z^{-2}\\
 -cz^{-1}&z&0\\
 dz^{-2}&0&z
 \end{pmatrix}\\
 &=z^6\bigl(z^3-cz^{-1}+dz^{-3}\bigr)
  =z^3(z^6-cz^2+d).
\end{aligned}
\tag{2.6}
$$

Both sides are polynomials, so agreement for every nonzero $z$ proves
the identity also at zero. This includes the zero eigenvalues rather
than dividing them out of the spectral assertion.

For $s>0$ put $g(s)=s^4-c-d/s^2$. It is continuous and strictly
increasing: $g'(s)=4s^3+2d/s^3>0$. Its limit at infinity is positive
infinity; its limit at zero is $-\infty$ when $d>0$ and $-c<0$ when
$d=0$. Here $c\ge\lambda^2>0$. The intermediate value theorem and
strict increase give exactly one positive root $r$. Multiplication
by $r^2$ gives (2.2). For every positive $s$,

$$
s\le r\iff s^6-cs^2-d\le0,
\tag{2.7}
$$

and the strict and equality versions follow from the same strict increase.

If $z\ne0$ is a root of the sextic in (2.6), then

$$
|z|^6=|cz^2-d|\le c|z|^2+d,
$$

so (2.7) implies $|z|\le r$. On the other hand, (2.2) gives
$(ir)^6-c(ir)^2+d=-r^6+cr^2+d=0$. Thus $ir$ and $-ir$ are
eigenvalues, and every eigenvalue, including zero, has modulus at most
$r$. This proves the exact radius assertion. Since
$g(1)=1-c-d=1-2c+\lambda^2$, comparison with the unique zero of $g$
proves all three cases of (2.4).

Suppose $d>0$ and $|z|=r$ for a sextic root. Equality is necessary in
the triangle inequality above. One can express it without a phase
convention by squaring:

$$
(c|z|^2+d)^2-|cz^2-d|^2
 =2cd\bigl(|z|^2+\operatorname{Re}(z^2)\bigr).
$$

As $c,d>0$, equality forces $\operatorname{Re}(z^2)=-|z|^2$.
The complex number $z^2$ has modulus $|z|^2$, so it must equal the
negative real number $-r^2$. Hence $z=ir$ or $z=-ir$.
For $p(z)=z^6-cz^2+d$,

$$
p'(\pm ir)=2(\pm ir)(3r^4-c)\ne0,
$$

because (2.2) gives $r^4=c+d/r^2\ge c>0$.
The factor $z^3$ is nonzero there, proving algebraic simplicity.
The boundary value $c=(1+\lambda^2)/2$ has
$d=(1-\lambda^2)/2>0$, so this conclusion applies at the boundary.
If $d=0$, then $c=\lambda^2$ and (2.6) becomes
$z^5(z^4-c)$. Its four nonzero roots are exactly the four listed values,
all simple, with modulus $c^{1/4}=\sqrt\lambda$.

Finally, split an enlarged history into slots $0,1,2$ and the remaining
slots. No remaining slot enters the new update or any of the first
three slots. The enlarged matrix is therefore
$\begin{pmatrix}B&0\\E&N\end{pmatrix}$, where $N$ is a nilpotent shift
on $3(K-2)$ coordinates. Its characteristic polynomial is
$z^{3(K-2)}\det(zI_9-B)$. This is the exact zero-eigenvalue qualification
of the history-length invariance used in the cited Lemma `L:spectra`.
$\square$

**Corollary 2.2 (Every prescribed radius and absence of a finite bound).**
For each fixed $0<\lambda<1$, the family (1.3), with $c\ge\lambda^2$,
attains each delayed radius $R\in[\sqrt\lambda,\infty)$ exactly once.
The required parameter is

$$
c=\frac{R^6+\lambda^2}{R^2+1},\qquad d=c-\lambda^2.
\tag{2.8}
$$

In particular, for this single symmetric delay array with maximum two,
the delayed radii are unbounded at every fixed synchronous radius
$\lambda$. No finite real upper bound depending only on $\lambda$ and
$k$ can hold for all zero-diagonal block matrices and positive remote
delays bounded by $k$, even at $k=2$.

**Proof.** Replacing $d$ by $c-\lambda^2$ in (2.2) yields
$r^6=c(r^2+1)-\lambda^2$, which forces (2.8) if $r=R$.
For any $R\ge\sqrt\lambda$,

$$
c-\lambda^2
 =\frac{R^2(R^4-\lambda^2)}{R^2+1}\ge0.
$$

Thus (2.8) satisfies the full parameter domain, and substitution gives
$R^6=cR^2+d$. The uniqueness in Theorem 2.1 makes its delayed radius
exactly $R$. Conversely, any family radius satisfies
$r^4=c+d/r^2\ge\lambda^2$, and hence $r\ge\sqrt\lambda$.
The forced formula (2.8) proves uniqueness of its parameter. Given any
finite proposed bound $F(\lambda,2)$, choose a real
$R>\max\{\sqrt\lambda,F(\lambda,2)\}$ and apply (2.8). The matrix and
the unchanged array (1.3) violate that bound. $\square$

**Proposition 2.3 (Exact original power-bound threshold).** In the same
parameter domain, the power bound of the cited v1 Open Problem for the
array (1.3), namely $\rho(B)\le\lambda^{1/3}$, holds exactly when

$$
c\le\frac{2\lambda^2}{1+\lambda^{2/3}}.
\tag{2.9}
$$

Equality of the two radii holds exactly at equality in (2.9); reversing
the strict inequality reverses the strict radius comparison.

**Proof.** Set $s=\lambda^{1/3}>0$. The sign comparison (2.7), with
its strict and equality forms, reduces the radius comparison to

$$
s^6-cs^2-d
 =2\lambda^2-c(1+\lambda^{2/3}).
$$

Its coefficient $1+\lambda^{2/3}$ is positive. This proves all the
comparisons, including equality. The cutoff lies inside the allowed
domain because $1+\lambda^{2/3}<2$, so it exceeds $\lambda^2$.
$\square$

## 3. Convergence for every constant bounded delay array

**Theorem 3.1 (Sharp delay-robust boundary for the family).** Under
(1.2), the following conditions are equivalent:

1. $2c-\lambda^2<1$.
2. For every integer $K\ge0$ and every constant nonnegative array
   $\delta$ with zero local delays and $\max\delta\le K$, (1.1)
   converges to zero for every real initial history.
3. For the fixed array $\delta_*$, (1.4) converges to zero for every
   real initial history.

Moreover, for each fixed bound $K\ge2$, condition 1 is also equivalent
to convergence for every such array bounded by $K$, and to convergence
for every positive remote-delay array bounded by $K$.
At $2c-\lambda^2=1$ the array $\delta_*$ has a nondecaying real
periodic history. At $2c-\lambda^2>1$ it has a real history with an
exponentially growing subsequence. The necessity statement with a
fixed bound is asserted only for $K\ge2$.

**Proof.** Write $W=|M|$ entrywise and $S=c+d=2c-\lambda^2$.
The same three-by-three determinant expansion gives
$\det(zI-W)=z(z^2-S)$, so $\rho(W)=\sqrt S$.
The absolute-matrix contraction criterion is a classical intermediate:
see Bertsekas and Tsitsiklis, *Some Aspects of Parallel and Distributed
Iterative Algorithms—A Survey*, Automatica 27(1), 3–21,
[author-hosted text, §6.1, equations (6.1)–(6.2) and example (a),
p. 14](https://web.mit.edu/dimitrib/www/Some_Aspects_DB.pdf).
The [existing problem's sufficient-condition argument](../../../Problems/aksoy-et-al-2023-asynchronous-iteration-spectral-radius-refutation.md)
also gives its weighted-history form. For the present family its entire
sufficiency argument, including $d=0$, can be made explicit as follows.

If $S<1$, choose $q$ with $\sqrt S<q<1$, and put

$$
\varepsilon=\frac{q^2-S}{4q}>0,\qquad
w=\left(1,\frac cq+\varepsilon,\frac dq+\varepsilon\right)^{\mathsf T}.
$$

Every entry of $w$ is positive. Its first absolute row sum is
$w_2+w_3=(S+q^2)/(2q)<q$, while
$c\le q w_2$ and $d\le q w_3$. Thus $Ww\le q w$ coordinatewise.
For any of the arrays and bounds in condition 2, let
$\eta=q^{1/(K+1)}\in(0,1)$ and use the norm

$$
\|y\|_*=\max_{0\le s\le K,\,1\le i\le3}
           \frac{\eta^s|y_{s,i}|}{w_i}.
\tag{3.1}
$$

For each newest coordinate, (1.1) and $0\le\delta_{ji}\le K$ give

$$
\begin{aligned}
\frac{|(B_{\delta,K}y)_{0,i}|}{w_i}
 &\le\sum_j\frac{|M_{ij}|w_j}{w_i}\eta^{-\delta_{ji}}\|y\|_*\\
 &\le q\eta^{-K}\|y\|_*=\eta\|y\|_*.
\end{aligned}
$$

Every shifted coordinate has weighted size at most
$\eta\|y\|_*$ as well. Therefore
$\|B_{\delta,K}^t y\|_*\le\eta^t\|y\|_*$, which tends to zero.
This proves condition 2 and sufficiency for each fixed bound; the rate
here depends on that bound. Condition 2 implies condition 3 by taking
$K=2$ and $\delta=\delta_*$.

For the converse, if $S\ge1$, Theorem 2.1 gives a radius $r\ge1$
and a nonzero eigenvalue $z=ir$. An explicit nonzero vector in its
newest slot is

$$
u_z=(1,cz^{-2},-dz^{-3})^{\mathsf T}.
\tag{3.2}
$$

Indeed, the second and third equations for
$(u_z,z^{-1}u_z,z^{-2}u_z)$ to be a $z$-eigenvector of (2.5) hold
by its definition. The first reduces to
$z=cz^{-3}-dz^{-5}$, exactly $z^6-cz^2+d=0$.
For every integer $t$, set

$$
x(t)=\operatorname{Re}(z^t u_z).
\tag{3.3}
$$

Because (1.4) has real coefficients, this is a real solution for all
$t$, so its values at $-2,-1,0$ form an allowed history. Its first
coordinate satisfies $x_1(2m)=(-1)^m r^{2m}$ for $m\ge0$.
It does not tend to zero. If $S=1$, then $r=1$, and (3.3) is
periodic with period four. If $S>1$, the displayed subsequence grows
exponentially in magnitude. This contradicts condition 3, proving
necessity including equality.

For a fixed $K\ge2$, the same array $\delta_*$ is allowed even when
all remote delays are required to be positive. Extending (3.3) back
to $-K$ gives a legal longer initial history and the same failure.
Together with sufficiency, this proves both fixed-bound equivalences.
The uniform positive-delay class at bound one has the different radius
law in Theorem 4.1; it cannot be used for this necessity implication.
$\square$

## 4. Minimality with positive remote delays

**Theorem 4.1 (Minimal block count and positive delay bound).** Among
real zero-diagonal block matrices with spectral radius
$\lambda\in(0,1)$ and constant strictly positive remote delays,
three blocks and maximum delay two are simultaneously sufficient and
minimal for a delayed spectral radius at least one. More precisely:

1. For arbitrary positive integers $m,n$, arbitrary real rectangular
   matrices $U\in\mathbb R^{m\times n}$,
   $V\in\mathbb R^{n\times m}$, and
   $M_0=\begin{pmatrix}0&U\\V&0\end{pmatrix}$ with
   $\rho(M_0)=\lambda\in(0,1)$, let the remote delays from the second
   block to the first and from the first to the second be respectively
   integers $1\le a,b\le k$. For any history length at least
   $\max\{a,b\}$,

   $$
   \rho(M_0^{(\delta)})
    =\lambda^{2/(a+b+2)}
    \le\lambda^{1/(k+1)}<1.
   \tag{4.1}
   $$

2. For any finite positive number of positive-sized blocks and any
   real zero-diagonal block matrix $N$ with $\rho(N)=\lambda\in(0,1)$,
   if every remote delay is a positive integer at most one, then
   $\rho(N^{(\delta)})=\sqrt\lambda<1$.
3. The family (1.3) has three scalar coordinates and attains radius
   one at $c=(1+\lambda^2)/2$, and arbitrarily large radii as in (2.8),
   with maximum positive remote delay two.

The minimality assertion uses the strictly positive remote-delay
convention. It makes no assertion for the convention permitting zero
remote delays at maximum one.

**Proof.** For part 1, work over $\mathbb C$ and put $L=a+b+2$.
A nonzero eigenvalue $z$ of the history operator has an eigenvector
whose newest slot is $(u,v)\ne0$ and whose slot $s$ is
$z^{-s}(u,v)$, by the shift equations. Its update equations are

$$
zu=z^{-a}Uv,\qquad zv=z^{-b}Vu.
\tag{4.2}
$$

If $u=0$, the second equation forces $v=0$, a contradiction.
Eliminating $v$ gives

$$
z^L u=UVu.
\tag{4.3}
$$

Conversely, for any nonzero eigenvalue $\mu$ of $UV$, choose a
nonzero $u$ with $UVu=\mu u$. Every complex root $z$ of $z^L=\mu$
is nonzero; setting $v=z^{-(b+1)}Vu$ verifies both equations (4.2).
Their history vector is nonzero because $u\ne0$. Thus the nonzero
spectrum of the delayed operator consists exactly of all $L$th roots
of the nonzero spectrum of $UV$.

For completeness, the rectangular block dimensions do not change the
radius identification used here. If $UVu=\mu u$ with $\mu\ne0$,
then $Vu\ne0$ and $VU(Vu)=\mu Vu$. Reversing $U,V$ proves that
$UV$ and $VU$ have exactly the same nonzero eigenvalues as sets.
Also $M_0^2=\operatorname{diag}(UV,VU)$. The elementary polynomial
spectral-mapping identity for squaring gives
$\rho(M_0)^2=\max\{\rho(UV),\rho(VU)\}$. Equivalently, over
$\mathbb C$ the factorization
$M_0^2-z^2I=(M_0-zI)(M_0+zI)$ shows that $z^2$ is a spectral
value of $M_0^2$ exactly when $z$ or $-z$ is a spectral value of
$M_0$. Since $\lambda>0$, both rectangular products consequently
have radius $\lambda^2>0$. Equation (4.3) and its converse now yield
$\rho(M_0^{(\delta)})=(\lambda^2)^{1/L}$.
As $L\le2k+2$, we have $2/L\ge1/(k+1)$, and powers of a number
in $(0,1)$ decrease as the exponent increases. This proves (4.1).
Any additional zero eigenvalues have no effect on this positive radius.

For part 2, all remote delays equal one, and the diagonal blocks
contribute nothing. Thus $x(t+1)=Nx(t-1)$. This is precisely the
uniform-contributing-delay case of Ortiz Marrero and Young's cited
Lemma `L:uniform`, used here as a classical intermediate. With one
preceding slot its history matrix is

$$
C=\begin{pmatrix}0&N\\I&0\end{pmatrix},\qquad
C^2=\operatorname{diag}(N,N).
$$

The same spectral-mapping argument gives $\rho(C)^2=\rho(N)=\lambda$.
For a longer history, the decomposition into the first two slots and
the unused older slots has a nilpotent lower diagonal block exactly
as in the last paragraph of Theorem 2.1. Hence the radius remains
$\sqrt\lambda$.

Part 3 follows from Theorem 2.1 and Corollary 2.2. A single zero-diagonal
block is the zero matrix and cannot have positive radius $\lambda$.
Part 1 rules out two blocks of any positive dimensions, and part 2
rules out a maximum positive remote delay one with any number of
blocks. Three scalar blocks have total dimension three; total
dimension less than three permits at most two positive-sized blocks.
Thus (1.3) attains both minima, including the minimum scalar dimension,
under exactly the stated convention. $\square$

## 5. Jacobi sign conventions

**Proposition 5.1 (Two exact system correspondences).** Under (1.2),
let $H=I_3+M$ and $A=I_3-M$. The positive off-diagonal convention
printed in the cited v1 Experimental Results,
$H_{ii}^{-1}H_{ij}$ for $i\ne j$ with zero diagonal blocks,
produces exactly the iteration matrix $M$ from $H$. The ordinary
Jacobi error iteration for the system $Ax=b$ also has iteration
matrix $M$. Both $H$ and $A$ are diagonalizable over $\mathbb R$,
with the real positive eigenvalues

$$
\{1,1-\lambda,1+\lambda\}.
\tag{5.1}
$$

Neither is symmetric; in particular, neither is a symmetric positive
definite matrix.

**Proof.** Every diagonal entry of $M$ is zero, so $H_{ii}=A_{ii}=1$.
For $i\ne j$, $H_{ii}^{-1}H_{ij}=M_{ij}$, verifying the source's
printed positive convention with all blocks scalar. For ordinary
Jacobi, write $D=\operatorname{diag}(A)=I_3$. Subtracting the exact
solution from $Dx(t+1)=(D-A)x(t)+b$ gives the error matrix
$I_3-D^{-1}A=M$. This uses $A=I_3-M$, rather than silently applying
the positive convention to the ordinary error iteration.
For any eigenvector of $M$ with eigenvalue $s$, $I_3\pm M$ has that
same eigenvector with eigenvalue $1\pm s$. The real eigenbasis from
Theorem 2.1 proves (5.1) and diagonalizability. The inequalities
$0<\lambda<1$ make all three values positive. Nevertheless,
$H_{13}=1$ and $H_{31}=-d\le0$, so $H$ is not symmetric;
$A_{13}=-1$ and $A_{31}=d\ge0$ give the same conclusion for $A$.
Positive real eigenvalues therefore supply no symmetry or symmetric
positive definiteness in this family. $\square$

## 追加锚（本行以下为增补区）
