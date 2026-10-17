# Legal-prefix lattice rigidity and interior normal forms

Legal cumulative $M/J$ histories admit an exact arithmetic description. On the whole fixed-polar-sign rank-one prefix class, their kernel levels are primitive integer lattice lines. When all four entries of the kernel generator are nonzero, the last two prefix transitions have an exhaustive necessary-and-sufficient normal form, subject to explicit first-endpoint and rank filters. In this entire subcase, a final legal multiplier preserves the kernel level exactly when its matrix is the identity. These structural results do not imply positive multiplicity or global recovery.

## 1. Actual sources, recorded indices, and prefix kernels

**Definition 1.1 (actual model and legal history).** Set
$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
U=JM=\begin{pmatrix}1&1\\0&1\end{pmatrix},\qquad
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix}.
$$
A predetermined legal history has $A_0=I$ and $A_{i+1}=W_iA_i$, where each $W_i$ is a fixed finite forward word in $M,J$, possibly empty. Products act on the left and execute from right to left. Thus chronological $(M,J)$ implements $U$, and chronological $(J,M)$ implements $L$. The five scalar readings below have indices exactly $0,1,2,3,4$. Every scalar read advances this index, including a read after an empty word; unread atoms do not advance it.

The effective source and observations are
$$
S=\begin{pmatrix}p&q\\r&s\end{pmatrix},\qquad
p,q,r,s>0,\qquad ps=qr,
$$
$$
z_i=(1+ik)\operatorname{tr}(A_iS)+\delta,
\qquad k\in\mathbb R,\qquad D(\tau)=\delta\quad(\tau\in\mathbb R).
\tag{1.1}
$$
The target is the whole $(S,k,D)$. Sampled zero and negative gains are included. In original gain parameters, $S=\alpha R$, $k=\beta/\alpha$, with $\alpha>0$ and arbitrary real $\beta$.

**Proposition 1.2 (actual realization and exact representation fibres).** Every source in (1.1) is realized by
$$
\alpha=1,\qquad \beta=k,\qquad R=S,\qquad
f_+=\binom p r,\qquad \ell_+=(1,q/p).
\tag{1.2}
$$
The row is unchanged throughout its run, and every recorded and unread column on any legal history is positive. For a fixed effective target, its original gain/relation representations are exactly
$$
R=S/u,\qquad \alpha=u>0,\qquad \beta=uk,\qquad D\text{ unchanged}.
\tag{1.3}
$$
For fixed $R$, its positive factorizations differ exactly by $f_+'=\mu f_+$ and $\ell_+'=\ell_+/\mu$, with $\mu>0$.

**Proof.** The identity $s=qr/p$ gives $f_+\ell_+=S$. If $A=(\begin{smallmatrix}h&t\\g&e\end{smallmatrix})$, then
$$
\ell_+Af_+=hp+tr+gq+es=\operatorname{tr}(AS).
$$
The identities $M(x,y)^{\mathsf T}=(y,x+y)^{\mathsf T}$ and $J(x,y)^{\mathsf T}=(y,x)^{\mathsf T}$ preserve strict positivity for $x,y>0$, proving the assertion through every unread atom. Necessity of (1.3) follows from $S=\alpha R$ and $k=\beta/\alpha$; substitution proves sufficiency. If $R=f\ell=f'\ell'$ with positive factors, equality of the first columns gives $f'=\mu f$ for a positive scalar, and equality of the other column gives $\ell'=\ell/\mu$. These are representation freedoms, not identifications of different effective targets. Different candidate runs may have different fixed positive rows. ∎

**Definition 1.3 (auxiliary operators and the class $\mathscr G$).** On full real $2\times2$ matrices put
$$
\mathsf B_{\rm pre}X=
\bigl(\operatorname{tr}(A_iX)-\operatorname{tr}X\bigr)_{i=1}^3,
$$
$$
\mathsf BX=\bigl(\operatorname{tr}(A_iX)-\operatorname{tr}X\bigr)_{i=1}^4,
\qquad
\mathsf CX=\bigl(i\operatorname{tr}(A_iX)\bigr)_{i=1}^4,
\qquad \mathsf T_k=\mathsf B+k\mathsf C.
\tag{1.4}
$$
The determinant polar is
$$
\mathfrak b(X,Y)=\det(X+Y)-\det X-\det Y.
$$
For $X=(\begin{smallmatrix}p&q\\r&s\end{smallmatrix})$ and $Y=(\begin{smallmatrix}P&Q\\R&T\end{smallmatrix})$, expansion gives
$$
\mathfrak b(X,Y)=sP+pT-rQ-qR,
\qquad
\det(X+vY)=\det X+v\mathfrak b(X,Y)+v^2\det Y.
\tag{1.5}
$$
In particular the polar is symmetric bilinear.

The class $\mathscr G$ consists of legal prefixes $I,A_1,A_2,A_3$ for which $\ker\mathsf B_{\rm pre}=\mathbb RN$, where $N\ne0$ has rank one and $\mathfrak b(S,N)$ has one strict fixed sign on every strictly positive rank-one $S$. Orient $N$ so that this sign is positive. Thus $\operatorname{rank}\mathsf B_{\rm pre}=3$. The kernel matrices and signed columns used below are auxiliary proof objects; they are not actual positive sources or additional acquisitions.

## 2. The exact legal monoid and cumulative criterion

**Theorem 2.1 (legal matrix monoid).** The finite $M/J$ word matrices, including $I$, are exactly the nonnegative integral $2\times2$ matrices of determinant $+1$ or $-1$.

**Proof.** Products of $M,J$ have the stated properties. Conversely let
$$
H=\begin{pmatrix}h&t\\g&e\end{pmatrix}
$$
be nonnegative integral with $|\det H|=1$. Its rows are nonzero. When the first row dominates the second componentwise, subtract the second from the first. This is left multiplication by $U^{-1}$ and leaves a nonnegative integral unimodular matrix. When the second dominates the first, use $L^{-1}$ instead. Each subtraction strictly reduces the nonnegative integer sum of all entries, since the subtracted row is nonzero. The resulting rows cannot include a zero row because the determinant remains nonzero.

If the rows are incomparable, first suppose $h>g$ and $t<e$. Write $h=g+\eta$ and $e=t+\theta$, with positive integers $\eta,\theta$. Then
$$
\det H=g\theta+\eta t+\eta\theta.
$$
Absolute determinant one forces $g=t=0$ and $\eta=\theta=1$, so $H=I$. The other incomparable case becomes this one after exchanging the rows, and gives $H=J$. Repeated subtraction must therefore terminate at $I$ or $J$. Reversing the reductions expresses the original matrix using $U,L,J$, and $U=JM$, $L=MJ$ are forward legal words. This is a finite decreasing-integer proof, with no inverse acquisition. ∎

**Corollary 2.2 (exact cumulative continuation).** For two legal endpoint matrices $A,B$, the endpoint $B$ can follow $A$ by a legal left word if and only if $BA^{-1}$ is entrywise nonnegative.

**Proof.** Any such multiplier equals $BA^{-1}$, so nonnegativity is necessary. Conversely $A^{-1}$ is integral and unimodular. Hence $BA^{-1}$ is integral with determinant $\pm1$, and nonnegativity permits Theorem 2.1 to supply a forward word. The inverse here identifies that word algebraically; only the word is executed. Separate legality of $A$ and $B$ does not replace this cumulative condition. ∎

## 3. Primitive signed lattice levels on the whole class

**Lemma 3.1 (signs and positive trace).** Every positively oriented kernel generator in Definition 1.3 has
$$
n_{11},n_{22}\ge0,\qquad n_{12},n_{21}\le0,
\qquad \operatorname{tr}N>0.
\tag{3.1}
$$
The prefix trace map
$$
\mathcal L_{\rm pre}X=
\bigl(\operatorname{tr}(A_iX)\bigr)_{i=0}^3
\tag{3.2}
$$
is invertible on the four-dimensional full matrix space.

**Proof.** On the positive rank-one matrix $(\begin{smallmatrix}uv&u\\v&1\end{smallmatrix})$, $u,v>0$, the polar is
$$
n_{11}+n_{22}uv-n_{12}v-n_{21}u>0.
$$
Take $u=v$ to zero to obtain $n_{11}\ge0$. Take $u=v$ to infinity and divide by $u^2$ to obtain $n_{22}\ge0$. Take $(u,v)=(T^{-2},T)$ and divide by $T$ as $T$ tends to infinity to obtain $n_{12}\le0$; $(u,v)=(T,T^{-2})$ gives $n_{21}\le0$.

If the trace were zero, both diagonal entries would vanish. Rank one would force at least one off-diagonal entry to vanish. Then nonzero $N$ would be a negative multiple of $E_{12}$ or $E_{21}$. Its prefix level equations would force, respectively, the lower-left or upper-right entry of every endpoint to vanish. A triangular nonnegative integral unimodular matrix has diagonal product one, hence both diagonal entries one. The three endpoint differences would lie in a one-dimensional off-diagonal span, contradicting rank three. Thus the trace is positive. Finally, $\mathcal L_{\rm pre}X=0$ implies $X=vN$ by the prefix kernel condition; its zero initial trace forces $v=0$. This proves invertibility. ∎

**Theorem 3.2 (whole-class primitive representation, with converse).** Every prefix in $\mathscr G$ has its positively oriented kernel line generated by
$$
N=f\ell,\qquad f=\binom a{-b},\qquad \ell=(c,-d),
\qquad a,b,c,d\in\mathbb Z_{\ge0},
$$
$$
\gcd(a,b)=\gcd(c,d)=1,\qquad t=ac+bd>0.
\tag{3.3}
$$
Every recorded prefix endpoint satisfies
$$
A_if=f+m_i r_0,\qquad r_0=\binom d c,\qquad m_i\in\mathbb Z,
\qquad m_0=0.
\tag{3.4}
$$
Conversely, suppose a nonnegative integral unimodular cumulative prefix starts at $I$, satisfies (3.3)–(3.4), and has $\operatorname{rank}\mathsf B_{\rm pre}=3$. It belongs to $\mathscr G$ with kernel line $\mathbb R(f\ell)$. Cumulative legality can equivalently be imposed by Corollary 2.2 at each step.

**Proof.** The integer coefficient matrix of $\mathsf B_{\rm pre}$ has rank three and therefore has a nonzero rational kernel vector, for example its signed $3\times3$ minors. Scale to an integer kernel matrix and orient its polar positively. It has rank one and the signs in Lemma 3.1.

Its column line has a primitive integer generator $f=(a,-b)^{\mathsf T}$ with $a,b\ge0$: use the first column if nonzero, or the negative of the second otherwise, then divide by the gcd. Every integer column on this line is an integer multiple of $f$. Indeed Bezout coefficients for $a,b$ recover that multiplier as an integer. The sign pattern makes the first column multiplier nonnegative and the second nonpositive. Divide the two multiplier magnitudes by their common positive gcd to obtain $(c,-d)$ with nonnegative coprime $c,d$. Thus the integer matrix is a positive scalar multiple of $f\ell$. Lemma 3.1 gives $t=\operatorname{tr}(f\ell)=ac+bd>0$.

For every endpoint, its kernel equation is
$$
\operatorname{tr}(A_if\ell)=\ell A_if=\ell f=t.
$$
The integer solutions to $cX-dY=t$ are exactly
$$
(X,Y)=(a,-b)+m(d,c),\qquad m\in\mathbb Z.
$$
For $c,d>0$ this follows from coprimality after subtracting the initial solution. If $c=0$, then $d=1$ and only $Y=-b$ is fixed; if $d=0$, then $c=1$ and only $X=a$ is fixed. These give the same formula. This proves (3.4) on the whole class, including zero-entry kernels.

Conversely, (3.4) and $\ell r_0=0$ give $\mathsf B_{\rm pre}(f\ell)=0$. The rank condition makes this the entire kernel line. The matrix is nonzero rank one and
$$
\mathfrak b(S,f\ell)=bd\,p+bc\,q+ad\,r+ac\,s>0
\tag{3.5}
$$
on every positive source: its coefficients are nonnegative and $ac+bd>0$. Corollary 2.2 and Theorem 2.1 realize each retained cumulative transition by a forward word. This proves the converse without inferring realizability from lattice equations alone. ∎

## 4. Interior phase and integer transition rigidity

In this section and the normal form below, $d$ denotes a lattice coordinate, not the degree of a drift polynomial.

**Theorem 4.1 (phase rigidity for four nonzero kernel entries).** Suppose a prefix in $\mathscr G$ has all four kernel entries nonzero. In (3.3) this is exactly $a,b,c,d>0$. After conjugating the entire history by $J$ if necessary, its three noninitial signed images are strictly positive and
$$
A_if=f+m_ir_0,\qquad 1\le m_1<m_2<m_3.
\tag{4.1}
$$
Every mixed-sign recorded image satisfying its kernel level comes from the identity endpoint; no nonidentity invariant endpoint occurs in the mixed phase.

**Proof.** Follow $f=(a,-b)^{\mathsf T}$ through its actual sequence of unread atoms as an auxiliary signed vector. While its signs remain mixed, its positive magnitude is at most $a$ and its negative magnitude is at most $b$. The atom $J$ swaps their positions. The atom $M$ keeps one coordinate and replaces the other by the sum: if that sum retains a mixed sign pattern, the affected sign magnitude has decreased by the opposite magnitude. If the sum is zero or has the other sign, the vector enters a closed same-sign orthant. Both closed same-sign orthants are preserved by subsequent $M,J$ atoms.

At a recorded mixed image $v$ with $\ell v=t>0$, the orientation $(-,+)$ is impossible because $c,d>0$. In the other orientation write $v=(A,-B)^{\mathsf T}$, with $0<A\le a$, $0<B\le b$. Its level equation is $cA+dB=ca+db$, forcing $A=a$, $B=b$.

A nonnegative integral unimodular matrix fixing $f$ must be $I$. To prove this, write it as $(\begin{smallmatrix}h&u\\g&e\end{smallmatrix})$. The fixed-vector equations give
$$
a(h-1)=bu,\qquad b(e-1)=ag.
$$
Coprimality yields $h=1+bv$, $u=av$, $g=bw$, $e=1+aw$ for nonnegative integers $v,w$. Its determinant is $1+bv+aw$, so absolute determinant one gives $v=w=0$. Thus every invariant mixed endpoint is $I$.

Rank three excludes $I$ and repeated matrices among $A_1,A_2,A_3$, since their three differences are independent. Each $A_if$ is primitive because $A_i$ is integral unimodular. A boundary same-sign image would therefore be a signed coordinate unit. Its level would be one of $c,-c,d,-d$, whereas
$$
t=ac+bd\ge c+d>\max(c,d).
$$
This is impossible. All three noninitial images are strictly in one same-sign orthant, and they cannot switch between those orthants along the history.

If that orthant is negative, put
$$
A_i'=JA_iJ,\qquad f'=-Jf=\binom b{-a},\qquad
\ell'=-\ell J=(d,-c).
\tag{4.2}
$$
Then $A_i'f'=-JA_if$ is positive, $f'\ell'=JNJ$, and $W_i'=JW_iJ$ is a legal forward word. This includes empty multipliers, whose conjugates have matrix $JJ=I$. This is a correspondence of histories, with the same recorded indices.

In the positive branch, the second coordinate of (3.4) gives $m_i\ge1$. Along positive columns, $J$ preserves the coordinate sum and every $M$ strictly increases it. The coordinate sum on the level line increases strictly with $m$. If successive $m_i$ were equal, a realizing transition could contain no $M$ and would have matrix $I$ or $J$. The latter could fix this primitive positive column only at $(1,1)^{\mathsf T}$, whose level $c-d$ is smaller than $t$. The former repeats the endpoint. Both are excluded. This proves the strict inequalities in (4.1). ∎

**Lemma 4.2 (integer transition inequalities).** Let $v=(x,y)^{\mathsf T}$ and $r_0=(d,c)^{\mathsf T}$ be primitive positive integer columns with
$$
\det(v,r_0)=t>0.
$$
Suppose a legal matrix $W$ sends $v$ to $v'=v+jr_0$, with integer $j\ge1$. Write $\epsilon=\det W$. Then an integer $\lambda\ge1$ satisfies
$$
Wr_0=\epsilon r_0+\lambda v'.
\tag{4.3}
$$
Its lower-left entry implies
$$
\lambda\le\frac{jc^2}{y(y+jc)}\quad(\epsilon=+1),\qquad
\lambda\le c\left(\frac1y+\frac1{y+jc}\right)\quad(\epsilon=-1).
\tag{4.4}
$$
Consequently a determinant-$+1$ transition requires $y<c$, and no such transition of either sign exists when $y\ge2c$.

**Proof.** Taking determinants with $v'$ gives
$$
\det(v',Wr_0)=\epsilon t=\det(v',\epsilon r_0).
$$
Thus $Wr_0-\epsilon r_0$ is parallel to $v'$. The vector $v'$ is primitive, since $W$ is integral unimodular, so its integer parallel vector has an integer multiplier $\lambda$. If $\epsilon=-1$, $Wr_0+r_0$ is strictly positive, giving $\lambda\ge1$. If $\epsilon=+1$, a realizing word for $W$ must contain $M$, because the coordinate sum increases from $v$ to $v'$. The same word increases the sum of the strictly positive $r_0$. Hence $Wr_0-r_0=\lambda v'$ has positive sum, again giving $\lambda\ge1$.

The dual rows of the basis $[v,r_0]$ are $(c,-d)/t$ and $(-y,x)/t$. Therefore
$$
W=\frac{v'(c,-d)}t+
\frac{(\epsilon r_0+\lambda v')(-y,x)}t.
\tag{4.5}
$$
Writing $y'=y+jc$, its lower-left entry is
$$
\frac{c(y'-\epsilon y)-\lambda yy'}t.
$$
Nonnegativity gives (4.4). In the positive-determinant case, $y\ge c$ makes that upper bound at most $j/(j+1)<1$. In the negative-determinant case, $y\ge2c$ makes it at most $1/2+1/3<1$. These contradict the integer lower bound for $\lambda$. ∎

## 5. An exhaustive realizable interior normal form

**Theorem 5.1 (necessary and sufficient parameters).** Up to the conjugation (4.2), every prefix in $\mathscr G$ whose kernel has four nonzero entries has the following form, and every choice passing the stated filters gives such a prefix.

Choose integers and a sign satisfying
$$
x>d\ge1,\qquad \gcd(x,d)=1,\qquad m,n\ge1,\qquad
\sigma\in\{+1,-1\},\qquad a=x-md\ge1.
\tag{5.1}
$$
Define
$$
Q=1+nd,\qquad h=n(x+d)+\sigma,\qquad
c=x+hd,\qquad b=mc-d,
\tag{5.2}
$$
and require $\gcd(a,b)=1$. These formulas give $b,c,h>0$ and $Q\ge2$. Put
$$
f=\binom a{-b},\qquad \ell=(c,-d),\qquad
r_0=\binom d c,\qquad t=ac+bd=cx-d^2>0.
$$
Choose a nonnegative integral unimodular $A_1$ satisfying
$$
A_1f=\binom x d.
\tag{5.3}
$$
Then the next two multiplier matrices are exactly
$$
K=\begin{pmatrix}1&1\\Q&Q+\sigma\end{pmatrix},\qquad
H=\begin{pmatrix}0&1\\1&h\end{pmatrix},\qquad
A_2=KA_1,\qquad A_3=HA_2.
\tag{5.4}
$$
The remaining filter is
$$
\operatorname{rank}\mathsf B_{\rm pre}=3.
\tag{5.5}
$$
The first-endpoint condition (5.3), its nonnegative-integral requirement, and (5.5) are part of the necessary-and-sufficient statement. They are not automatic consequences of (5.1)–(5.2).

**Proof of necessity.** Work in the positive branch of Theorem 4.1 and write
$$
v_1=(x,y)^{\mathsf T},\qquad
v_2=v_1+jr_0,\qquad v_3=v_2+hr_0,\qquad j,h\ge1.
$$
Here $x>d$, because the first coordinate of $v_1=f+m_1r_0$ is $a+m_1d$. The input second coordinate $y+jc$ of the last transition exceeds $c$. Lemma 4.2 forces that transition to have determinant $-1$ and input second coordinate below $2c$. Thus $j=1$ and $0<y<c$.

For that last transition, (4.4) bounds its positive integer $\lambda$ by
$$
c\left(\frac1{y+c}+\frac1{y+(1+h)c}\right)<\frac32,
$$
so $\lambda=1$. Formula (4.5), now with input $v_2$, gives the last matrix's upper-left entry as
$$
\frac{dc-xy-hdy}{t},\qquad t=cx-dy.
\tag{5.6}
$$
The difference between its denominator and numerator is
$$
c(x-d)+xy+(h-1)dy>0.
$$
Since the entry is a nonnegative integer, it is zero. Determinant $-1$ then forces both off-diagonal entries to be one. Write the matrix as $(\begin{smallmatrix}0&1\\1&e\end{smallmatrix})$. The first coordinate of $Wr_0=-r_0+v_3$ gives $(v_3)_1=c+d$, while the first coordinate of $Wv_2=v_3$ gives $(v_3)_1=y+c$. Hence $y=d$. The identity $(v_3)_1=x+(1+h)d$ gives $c=x+hd$, and the second coordinate of $Wr_0=-r_0+v_3$ gives $e=h$. This proves the form of $H$. Primitiveness of $v_1=(x,d)^{\mathsf T}$ gives $\gcd(x,d)=1$.

For the preceding transition, its first-coordinate equation is
$$
K_{11}x+K_{12}d=x+d.
$$
Since $x>d$, $K_{11}$ is zero or one. If zero, unimodularity and nonnegativity force $K_{12}=K_{21}=1$, contradicting the displayed equation. Thus $K_{11}=K_{12}=1$. With $Q=K_{21}$ and $\sigma=\det K$, its remaining entry is $Q+\sigma$, and its second-coordinate equation is
$$
Q(x+d)=c+(1-\sigma)d.
\tag{5.7}
$$
Here $Q\ge1$. If $Q=1$ and $\sigma=-1$, (5.7) gives $c=x-d$, contrary to $c>x$. If $Q=1$ and $\sigma=+1$, it gives $c=x+d$, $h=1$, $K=M^2$ and $H=M$. But
$$
M^3=2M^2-I
$$
would imply $A_3=2A_2-A_1$ and therefore rank at most two for the three prefix differences. Hence $Q\ge2$.

Substitute $c=x+hd$ into (5.7). It becomes
$$
(Q-1)x=(h+1-\sigma-Q)d.
$$
Coprimality gives $d\mid Q-1$. Write $Q=1+nd$, with $n\ge1$; rearrangement gives $h=n(x+d)+\sigma$. Finally $v_1=f+m_1r_0$ yields $a=x-m_1d$ and $b=m_1c-d$. Set $m=m_1\ge1$. The original primitive $f$ gives $\gcd(a,b)=1$, and the original prefix supplies $A_1$ and the rank-three filter. This proves every necessary condition using the two transitions of the same cumulative history. ∎

**Proof of sufficiency and forward realization.** From (5.1)–(5.2), $h>0$, $c>x>d$, $b>0$, and $\gcd(c,d)=\gcd(x,d)=1$. Also
$$
ac+bd=(x-md)c+(mc-d)d=cx-d^2>0.
$$
Theorem 2.1 supplies a legal word for every admitted $A_1$. The following are explicit forward word matrices for the next transitions:
$$
K=L^QU\quad(\sigma=+1),\qquad
K=L^{Q-1}UJ\quad(\sigma=-1),\qquad
H=L^hJ.
\tag{5.8}
$$
All exponents are nonnegative; replace $L,U$ by $MJ,JM$ to obtain literal $M/J$ words. Execute the word for $A_1$, then the displayed words for $K,H$, reading only at their endpoints. Equation (5.7) follows from the parameter definitions, and multiplication gives
$$
A_1f=\binom x d=f+mr_0,
$$
$$
A_2f=\binom{x+d}{c+d}=f+(m+1)r_0,
$$
$$
A_3f=\binom{c+d}{d+(h+1)c}=f+(m+1+h)r_0.
\tag{5.9}
$$
All have the same $\ell$ level $t$. Thus $N=f\ell$ annihilates every prefix difference. The retained rank test makes its line the entire kernel. Formula (3.5), now with all coefficients positive, gives the strict fixed polar sign. This constructs a member of $\mathscr G$ on a single legal cumulative history, proving sufficiency. Proposition 1.2 realizes every actual positive source on these very words, with unchanged row and positive unread columns. The signed vectors in (5.9) are algebraic coordinates, not replacements for those sources. The conjugate correspondence of Theorem 4.1 restores the negative branch without extra reads or operations. ∎

**Theorem 5.2 (exact arithmetic first-endpoint filter).** For parameters (5.1)–(5.2), all possible first endpoints in (5.3) are exactly the matrices obtained by choosing $\epsilon\in\{+1,-1\}$ and $g\in\mathbb Z$ and setting
$$
(A_1)_{11}=\frac{cx+\epsilon bd+gbx}{t},\qquad
(A_1)_{12}=\frac{-dx+\epsilon ad+gax}{t},
$$
$$
(A_1)_{21}=\frac{cd+\epsilon bc+gbd}{t},\qquad
(A_1)_{22}=\frac{-d^2+\epsilon ac+gad}{t},
\tag{5.10}
$$
subject to all four entries being nonnegative integers. Their determinant is $\epsilon$. The rank test (5.5) is still required after forming $A_2,A_3$. For each admitted parameter tuple before the rank test, the first-endpoint arithmetic conditions have solutions, even strictly positive ones; this does not assert the rank test for those solutions.

**Proof.** The dual rows of $[f,r_0]$ are $\ell/t$ and $(b,a)/t$. If $A_1f=v_1=(x,d)^{\mathsf T}$ and $\det A_1=\epsilon$, then
$$
\det(v_1,A_1r_0)=\epsilon t=\det(v_1,\epsilon r_0).
$$
Primitiveness of $v_1$ makes $A_1r_0-\epsilon r_0=gv_1$ for an integer $g$. Consequently
$$
A_1=\frac{v_1\ell}t+
\frac{(\epsilon r_0+gv_1)(b,a)}t,
\tag{5.11}
$$
which expands to (5.10). Conversely this expression maps $f$ to $v_1$ and $r_0$ to $\epsilon r_0+gv_1$. Its determinant is
$$
\frac{\det(v_1,\epsilon r_0+gv_1)}{\det(f,r_0)}=\epsilon,
$$
since both $\det(v_1,r_0)$ and $\det(f,r_0)$ equal $t$. Thus nonnegative integral entries give precisely the desired legal first endpoint.

To prove existence of arithmetic solutions, extend each primitive column $f,v_1$ to an integer unimodular basis. Choose their basis determinants to be $1$ and $\epsilon$, respectively. The map between these bases is an integral determinant-$\epsilon$ matrix taking $f$ to $v_1$, and hence has an integer parameter $g_0$ in (5.11). Replacing $g_0$ by $g_0+Lt$ adds the positive integral matrix $L v_1(b,a)$. A sufficiently large positive integer $L$ makes every entry positive. This proves arithmetic nonemptiness, while leaving (5.5) as an explicit separate filter. ∎

**Proposition 5.3 (nonvacuity with the rank filter).** The normal form contains an actual legal prefix with four nonzero kernel entries and rank-three prefix differences.

**Proof.** Choose
$$
x=2,\quad d=1,\quad m=n=1,\quad \sigma=+1.
$$
Then $Q=2$, $h=4$, $c=6$, $a=1$, $b=5$, $t=11$. Taking $\epsilon=+1$, $g=6$ in (5.10) gives
$$
A_1=\begin{pmatrix}7&1\\6&1\end{pmatrix}=UL^6,
\qquad K=L^2U,\qquad H=L^4J,
$$
$$
A_2=\begin{pmatrix}13&2\\32&5\end{pmatrix},\qquad
A_3=\begin{pmatrix}32&5\\141&22\end{pmatrix}.
\tag{5.12}
$$
These follow from multiplying the displayed forward matrices. In source-entry order $(p,q,r,s)$, the prefix difference rows are
$$
(6,6,1,0),\qquad(12,32,2,4),\qquad(31,141,5,21).
$$
Their first-three-column minor is $-20$: subtract twice the first row from the second and five times the first from the third, obtaining rows $(0,20,0)$ and $(1,111,0)$ in those columns; expansion in the third column gives $-20$. Thus the rank is three. The kernel generator and its polar are
$$
N=\begin{pmatrix}6&-1\\-30&5\end{pmatrix},\qquad
\operatorname{tr}N=11,\qquad
\mathfrak b(S,N)=5p+30q+r+6s>0.
$$
This proves nonvacuity of all filters together. It is a structural witness, not a collision witness. ∎

## 6. Final-level rigidity throughout the interior subcase

**Theorem 6.1 (identity-only final level).** For every prefix in Theorem 5.1, including its conjugate branch, and every legal final multiplier matrix $W$,
$$
\operatorname{tr}(WA_3N)=\operatorname{tr}N
\quad\Longleftrightarrow\quad W=I.
\tag{6.1}
$$
Consequently the full zero-slope quotient $\mathsf B$ has rank three exactly when the final multiplier matrix is $I$, and is invertible for every other final multiplier.

**Proof.** First use the positive normal form. By (5.9),
$$
v_3=A_3f=\binom{c+d}{d+(h+1)c},\qquad (v_3)_2>2c.
$$
If the level is preserved, $Wv_3$ is a positive primitive integer vector with $\ell Wv_3=t$. The lattice equation gives $Wv_3=v_3+jr_0$ for an integer $j$. The coordinate sum cannot decrease along a positive column under a legal word, so $j\ge0$.

If $j=0$, a realizing word can contain no $M$. Its matrix is $I$ or $J$. The coordinates of $v_3$ differ by $hc>0$, so $J$ does not fix it. Hence $W=I$. If $j\ge1$, Lemma 4.2 forbids the transition because its input second coordinate exceeds $2c$. Conversely $W=I$ plainly preserves the level. This proves (6.1) on the positive branch.

For completeness, conjugation by $J$ sends every endpoint to $JA_iJ$, every multiplier to $JW_iJ$, and $N$ to $JNJ$. It preserves the level because
$$
\operatorname{tr}\bigl((JWJ)(JA_3J)(JNJ)\bigr)
=\operatorname{tr}(WA_3N).
$$
It preserves rank and has $JWJ=I$ exactly when $W=I$. Theorem 2.1 or the explicit concatenation by $J$ proves legality of every conjugate multiplier. Thus the negative branch has exactly the same assertion and final-word quantifier.

The first three rows of $\mathsf B$ have kernel $\mathbb RN$. Its last row removes that line exactly when
$$
\operatorname{tr}(A_4N)-\operatorname{tr}N\ne0,
\qquad A_4=WA_3.
$$
By (6.1), this happens precisely for $W\ne I$. The full rank is then four; for $W=I$ it is exactly three. ∎

Identity in Theorem 6.1 means the multiplier matrix. A nonempty literal word such as $JJ$ also has matrix $I$. The theorem covers it with the identity branch. Inverses in the monoid proof, signed vectors in the classification, and conjugations in the correspondence are proof devices. They add no inverse, conjugation, reset, copy, alternative-history combination, or extra read to an actual acquisition.

## 7. Exact fibres and the distinction from positive multiplicity

**Proposition 7.1 (whole-drift quotient equivalence).** For a fixed legal five-read history, two actual runs have identical complete data if and only if
$$
\mathsf T_{k_0}S_0=\mathsf T_{k_1}S_1,
\qquad \delta_1-\delta_0=\operatorname{tr}(S_0-S_1).
\tag{7.1}
$$
For arbitrary proposed data $z$, put $y=(z_i-z_0)_{i=1}^4$. Its entire actual fibre is exactly
$$
\left\{(S,k,D):\ S>0\text{ entrywise},\ \det S=0,\
\mathsf T_kS=y,\ D(\tau)=z_0-\operatorname{tr}S\text{ for all }\tau\right\}.
\tag{7.2}
$$

**Proof.** At index zero the gain is one and the signal is $\operatorname{tr}S+\delta$. Subtracting this initial reading from every other gives $\mathsf T_kS=y$. This proves necessity of both assertions. Conversely, attach the single entire constant $\delta=z_0-\operatorname{tr}S$. For every $i=1,2,3,4$,
$$
(1+ik)\operatorname{tr}(A_iS)+\delta
=(\mathsf T_kS)_i+z_0=z_i,
$$
and the initial equation holds by construction. At a gain zero this equation enforces $z_i=\delta$; it is not discarded. Proposition 1.2 realizes every retained source on the same actual words. Taking $D_0=0$ and $D_1=\operatorname{tr}(S_0-S_1)$ gives the whole drifts for any quotient collision. ∎

**Proposition 7.2 (credited all-slope rank and zero-slope uniqueness).** For every prefix in $\mathscr G$ and every legal final word, $\operatorname{rank}\mathsf T_k\ge3$ for all real $k$, $\mathsf T_{-1/4}$ is invertible, and each actual fibre has at most one target at the common slope $k=0$.

**Proof.** Use the invertible coordinates $f_i=\operatorname{tr}(A_iX)$, $0\le i\le3$, of Lemma 3.1. The first three rows are $(1+ik)f_i-f_0$, $i=1,2,3$. At most one of their three gains vanishes. If none does, the separate $f_i$ coefficients prove independence. If one does, its row is $-f_0$, independent of the other two rows with separate nonzero $f_i$ coefficients. At $k=-1/4$, the last row is also exactly $-f_0$, whereas the first three gains are $3/4,1/2,1/4$. A kernel vector must have all four $f_i=0$, proving invertibility.

At zero slope, an invertible $\mathsf B$ gives linear uniqueness. If it is singular, its kernel is $\mathbb RN$, since the first three rows have rank three. Any other auxiliary solution through an actual $S$ is $S+vN$. Since $\det S=\det N=0$, equation (1.5) gives
$$
\det(S+vN)=v\mathfrak b(S,N).
$$
The coefficient is strictly positive, so rank-one solutions require $v=0$. The initial equation then fixes $D$. This is common-slope-zero uniqueness only. ∎

In particular, the identity branch of Theorem 6.1 does not obtain a collision merely from singular $\mathsf B$, and the nonidentity branch does not obtain recovery merely from invertible $\mathsf B$. Cross-slope positive intersections in (7.2) remain a separate question.

## 8. Attribution and complete dependency correspondence

The original sharp fixed-path recovery programme supplies the actual strictly positive common-source model, the whole target, arbitrary real slopes, counted initial read, and cumulative finite forward-word contract. The supplied companion is titled *Prefix kernels and finite collisions for shared affine gain*. Its numbered results have the following precise roles.

| Credited companion result | Role and retained scope |
|---|---|
| Definition 1.1 and Proposition 1.2; equations (19.1)–(19.6) | Actual realization, exact representation fibres, determinant polar, and whole-constant-drift quotient; their needed forms are proved in Sections 1 and 7 here |
| Lemma 14.1 and Lemma 19.2 | Prefix trace invertibility and all-slope rank/erasure facts on the whole $\mathscr G$; their needed forms are proved in Lemma 3.1 and Proposition 7.2 here |
| Proposition 21.1 | Common-slope-zero uniqueness, proved in Proposition 7.2 here; no cross-slope uniqueness conclusion |
| Theorem 20.1 and Corollary 20.2, with complete proofs in companion Section 20 | Exhaustive regular/singular actual-fibre decomposition for every datum and final word on $\mathscr G$; a fibre is finite with size at most fourteen or contains a nontrivial continuous arc. These are existing results, not new structural contributions here |
| Proposition 17.1 and Theorem 22.1, with complete proofs in companion Sections 17 and 22 | A strict one-sign erased-gain method boundary and a compatible finite nonlocal collision for the exact specified history; that single history is already excluded as recovering. Neither result is a universal collision theorem |
| Theorems 8.1 and 8.2, with complete proofs and inverse/image criterion in companion Section 8 | The retained all-degree lower bound, positive-degree sharp construction, and six-read constant-drift restriction |

In the read-bound notation of that companion, $d$ now denotes the declared drift degree. The credited conclusions are exactly
$$
C_{\mathrm{fix}}(d)=d+5\quad(d\ge1),\qquad
5\le C_{\mathrm{fix}}(0)\le6.
\tag{8.1}
$$
The companion's Theorem 8.1 proves the fixed-history lower bound on the actual target chart by a maximal-rank argument. Its Theorem 8.2 supplies the terminal-repetition legal history, interpolation, exact midpoint injectivity, and cubic inverse with positivity, degree, and original-equation filters. Its degree-zero upper bound uses the degree-one six-read restriction, rather than invalid degree-zero terminal interpolation. These complete supplied proofs are the dependencies for (8.1); no sharper read bound follows from the structural normal form.

The supplied auxiliary result titled *Cumulative legal-prefix rigidity for kernels with four nonzero entries; the universal actual-positive multiplicity bridge remains unproved* supplies the following mathematical content.

| Auxiliary result | Complete result here |
|---|---|
| A: nonnegative integral unimodular monoid and cumulative continuation | Theorem 2.1 and Corollary 2.2 |
| B: primitive signed lattice representation on the whole class | Theorem 3.2, including its converse and zero-coordinate cases |
| C: interior signed-phase rigidity | Theorem 4.1, including the conjugate branch and strict parameter order |
| D: integer transition inequalities | Lemma 4.2 |
| E: exhaustive interior normal form, arithmetic first endpoint, forward realizability, and nonvacuity | Theorems 5.1–5.2 and Proposition 5.3, with the nonnegative-integral and rank-three filters retained |
| F: identity-only final-level preservation | Theorem 6.1 on the entire four-nonzero-entry subcase and its conjugate |

The proofs of these auxiliary results and all their internal mathematical prerequisites are present above. The companion's fibre theorem, isolated nonlocal collision, and read bounds are credited existing results. Supplier attribution is not an independent-review, formal-certification, external-priority, or missing-literature assertion. No nested reference is required to prove the new structural statements.

## 9. Exact remaining positive-intersection obligation

For every legal prefix in the whole class $\mathscr G$ and every legal final word $W$, the universal obstruction still requires finite actual matrices and real slopes satisfying
$$
\begin{gathered}
S_j>0\text{ entrywise},\qquad \det S_j=0,\qquad k_j\in\mathbb R,\\
(S_0,k_0)\ne(S_1,k_1),\qquad
\mathsf T_{k_0}S_0=\mathsf T_{k_1}S_1.
\end{gathered}
\tag{9.1}
$$
This quantifier asks for some colliding datum for each complete history. It does not ask for multiplicity at every datum or every slope. Proposition 7.1 then determines one whole drift per run and checks all five original equations.

Within the four-nonzero-entry subcase, Theorem 5.1 replaces arbitrary cumulative endpoints by exactly the admissible parameter tuples and first endpoints passing (5.10) and (5.5). The missing assertion is still (9.1) for every such tuple, every admitted first endpoint, and every legal final word, on both conjugate branches. Theorem 6.1 resolves precisely which final words preserve the kernel level. It supplies no second positive source for those histories. In the companion's exhaustive fibre description, the missing positive intersection would have to produce two positive regular candidates, a positive regular and positive singular candidate, two positive singular candidates, or a positive arc for some datum. A degree bound, failed sign test, or invertible zero-slope quotient does not force any such alternative.

For kernels with at least one zero entry, Theorem 3.2 still applies. Theorems 4.1, 5.1, and 6.1 do not classify those boundary geometries. They remain in the whole-class obligation (9.1), except where a separate supplied collision theorem applies with its literal hypotheses. The already supplied exact nonlocal collision remains excluded as a recovering history; other final words are not excluded merely by that witness.

The alternative constant-drift completion would be a legal predetermined five-read history with global uniqueness for every actual target, a global inverse, and a necessary-and-sufficient actual-source image criterion at every real slope. No such history or uniqueness theorem is established here. The original unrestricted programme also includes prefix geometries outside $\mathscr G$. Its five-versus-six alternative and full all-history objective remain unresolved; (8.1) is unchanged.

Every structural realization uses the original forward words, the actual reading clock, and the actual positive-source factorization. These are ordinary exact textual mathematical results. They assert no adaptive-path lower bound, empirical or general-neural-network conclusion, Lean/kernel certification, unrestricted atom optimum, resource, bit, time, stability or physical acquisition-cost bound, external priority, or absence of other literature.

## 追加锚（本行以下为增补区）

## 10. A positive rational retraction on the whole prefix class

All statements in Sections 10–13 apply to every prefix in $\mathscr G$, including kernels with zero entries. Retain the actual model (1.1), the predetermined forward cumulative words, and the reading indices $0,1,2,3,4$. An entrywise positive auxiliary matrix need not have rank one or be invertible. Only its rank-one representative is an actual source.

**Definition 10.1 (kernel coordinates and positive domains).** Use the primitive representative of Theorem 3.2 and put
$$
f_K=\binom a{-b},\qquad \ell_K=(c,-d),\qquad N=f_K\ell_K,
\qquad r_K=\binom d c=r_0,\qquad l_K=(b,a),
$$
$$
a,b,c,d\ge0,\qquad \gcd(a,b)=\gcd(c,d)=1,\qquad
 t=ac+bd>0,
$$
$$
P=[f_K,r_K]=\begin{pmatrix}a&d\\-b&c\end{pmatrix},\qquad
P^{-1}=\frac1t\begin{pmatrix}c&-d\\b&a\end{pmatrix}.
\tag{10.1}
$$
Here $\ell_K$ is the signed kernel row and $l_K$ is its nonnegative left-null row; they are different rows. The kernel vectors are auxiliary, whereas the positive factors of Proposition 1.2 realize actual sources. Define
$$
\mathcal P=\{X\in\mathbb R^{2\times2}:X_{ij}>0\},\qquad
\mathcal A=\{S\in\mathcal P:\det S=0\},
$$
$$
h(X)=l_KXr_K=\mathfrak b(X,N).
\tag{10.2}
$$
For $X=(\begin{smallmatrix}p&q\\r&s\end{smallmatrix})$, the last equality follows from
$$
h(X)=bd\,p+bc\,q+ad\,r+ac\,s.
$$
Both $r_K$ and $l_K$ are nonzero and nonnegative. Thus $Xr_K$ and $l_KX$ are strictly positive for $X\in\mathcal P$, and $h(X)>0$. Direct multiplication also gives
$$
Nr_K=0,\qquad l_KN=0,\qquad
P^{-1}NP=tE_{11},\qquad l_KP=(0,t).
\tag{10.3}
$$

**Theorem 10.2 (positive retraction, determinant correction, and unique representative).** For $X\in\mathcal P$ define
$$
\rho_N(X)=\frac{(Xr_K)(l_KX)}{h(X)}.
\tag{10.4}
$$
Then $\rho_N(X)\in\mathcal A$ and
$$
(Xr_K)(l_KX)=h(X)X-(\det X)N,
\qquad
\rho_N(X)=X-\frac{\det X}{h(X)}N.
\tag{10.5}
$$
The first identity holds for every real full matrix $X$. For positive $X$, $\rho_N(X)$ is the unique determinant-zero matrix on the entire real affine line $X+\mathbb RN$. In particular,
$$
\mathsf B_{\rm pre}\rho_N(X)=\mathsf B_{\rm pre}X,
\qquad
\mathsf B_{\rm pre}(\mathcal A)=\mathsf B_{\rm pre}(\mathcal P).
\tag{10.6}
$$
The map is real analytic on $\mathcal P$, homogeneous of degree one under positive scalars, idempotent, and fixes every actual source. Every positive point on one prefix quotient fibre has the same retraction.

**Proof.** To prove the matrix identity without an invertibility or positivity restriction on $X$, write
$$
Y=P^{-1}XP=\begin{pmatrix}w&\xi\\\nu&\zeta\end{pmatrix}.
$$
Equations (10.1)–(10.3) give $h(X)=t\zeta$, $\det X=\det Y$, $Xr_K=P(\xi,\zeta)^{\mathsf T}$ and $l_KX=t(\nu,\zeta)P^{-1}$. Conjugating the two sides of the first identity in (10.5) by $P^{-1},P$ reduces them respectively to
$$
t\begin{pmatrix}\xi\nu&\xi\zeta\\\zeta\nu&\zeta^2\end{pmatrix}
\quad\hbox{and}\quad
 t\left[\zeta\begin{pmatrix}w&\xi\\\nu&\zeta\end{pmatrix}
 -(w\zeta-\xi\nu)E_{11}\right].
$$
They are identical entry by entry. For $X\in\mathcal P$, (10.4) is a positive outer product divided by $h(X)>0$, hence is strictly positive and has rank one. Division of the proved identity gives its determinant correction formula.

Since $\det N=0$, (1.5) gives, for every real $u$,
$$
\det(X+uN)=\det X+u h(X).
\tag{10.7}
$$
Its coefficient is strictly positive. It has exactly one zero, $u=-\det X/h(X)$, proving uniqueness on the entire affine line. Since $\ker\mathsf B_{\rm pre}=\mathbb RN$, this proves both assertions in (10.6), with the reverse image inclusion also following from $\mathcal A\subset\mathcal P$. If two positive matrices have the same prefix quotient, their lines $X+\mathbb RN$ coincide, so their unique determinant-zero representatives coincide.

The rational formula (10.4) has a strictly positive denominator throughout the open set $\mathcal P$, proving real analyticity. Its numerator and denominator have degrees two and one under positive scalar multiplication, proving homogeneity. For $S\in\mathcal A$, (10.5) gives $\rho_N(S)=S$. Since every output lies in $\mathcal A$, applying the map twice changes nothing. All actual representatives have Proposition 1.2's positive fixed-row realization on the original words. No full auxiliary matrix is asserted to be an acquired rank-two source. ∎

## 11. The exact open convex prefix cone and its inverse

**Theorem 11.1 (five strict inequalities, including zero-component kernels).** Define the linear map
$$
H(\xi,\nu,\zeta)=P\begin{pmatrix}0&\xi\\\nu&\zeta\end{pmatrix}P^{-1},
\qquad
V(\xi,\nu,\zeta)=\mathsf B_{\rm pre}H(\xi,\nu,\zeta).
\tag{11.1}
$$
Then $V:\mathbb R^3\to\mathbb R^3$ is an isomorphism. Let
$$
\begin{split}
\mathcal K=\{(\xi,\nu,\zeta):\;&\zeta>0,\\
&a\xi+d\zeta>0,\quad c\zeta-b\xi>0,\\
&c\nu+b\zeta>0,\quad a\zeta-d\nu>0\}.
\end{split}
\tag{11.2}
$$
The exact prefix quotient image at slope zero is
$$
\mathsf B_{\rm pre}(\mathcal A)
=\mathsf B_{\rm pre}(\mathcal P)=V(\mathcal K).
\tag{11.3}
$$
For a proposed prefix quotient $y_{\rm pre}$, compute $(\xi,\nu,\zeta)=V^{-1}y_{\rm pre}$. It is realizable by an actual source if and only if all five strict inequalities in (11.2) hold. When they hold, the unique actual source is
$$
S_*(\xi,\nu,\zeta)
=P\begin{pmatrix}\xi\nu/\zeta&\xi\\\nu&\zeta\end{pmatrix}P^{-1}
=\frac1{t\zeta}
\binom{a\xi+d\zeta}{c\zeta-b\xi}
(c\nu+b\zeta,\ a\zeta-d\nu).
\tag{11.4}
$$
Both $\mathcal K$ and $V(\mathcal K)$ are nonempty, open, convex cones of dimension three, described by finitely many strict homogeneous linear inequalities. This is the strict-inequality meaning of an open polyhedral cone; boundary points with equality are not included.

**Proof.** In the coordinates $Y=P^{-1}XP$, the kernel of $\mathsf B_{\rm pre}$ is $\mathbb RE_{11}$ by (10.3). If $V(\xi,\nu,\zeta)=0$, the matrix with upper-left entry zero in (11.1) lies in that line, so $\xi=\nu=\zeta=0$. Equal dimensions make $V$ an isomorphism.

For $X\in\mathcal P$, write $Y=(\begin{smallmatrix}w&\xi\\\nu&\zeta\end{smallmatrix})$. The formulas used in Theorem 10.2 give
$$
\zeta=\frac{h(X)}t>0,
\qquad Xr_K=\binom{a\xi+d\zeta}{c\zeta-b\xi},
$$
$$
l_KX=(c\nu+b\zeta,\ a\zeta-d\nu).
\tag{11.5}
$$
Both vectors are strictly positive. Thus these three coordinates lie in $\mathcal K$, and the $w$ coordinate has no effect on the prefix quotient. This proves $\mathsf B_{\rm pre}(\mathcal P)\subset V(\mathcal K)$.

Conversely take $(\xi,\nu,\zeta)\in\mathcal K$. Formula (11.4) is a strictly positive outer product divided by $t\zeta>0$, so it is actual. To check its first expression and quotient, put $u=\xi/\zeta$, $v=\nu/\zeta$. Then
$$
S_* =\zeta\,[P(u,1)^{\mathsf T}]\,[(v,1)P^{-1}].
$$
Its conjugate by $P$ is exactly $(\begin{smallmatrix}\xi\nu/\zeta&\xi\\\nu&\zeta\end{smallmatrix})$, and its difference from $H$ lies in $\mathbb RN$. Its quotient is therefore $V(\xi,\nu,\zeta)$. This proves the opposite inclusion and actual realization. A determinant-zero matrix with these coordinates must satisfy $w\zeta=\xi\nu$. Since $\zeta>0$, its upper-left coordinate is uniquely the one in (11.4), which also proves the stated inverse directly.

There is no division by $a,b,c,d$ in either the test or the inverse. If $a=0$, primitivity and $t>0$ give $b=1,d>0$; if $b=0$, they give $a=1,c>0$. Likewise $c=0$ gives $d=1,b>0$, and $d=0$ gives $c=1,a>0$. Every such case, including simultaneous permitted zeros, still has nonzero $r_K,l_K$, positive $t\zeta$, and the same two strictly positive factors in (11.4). This verifies the zero-component cases without an implicit interior assumption.

Finally, each condition in (11.2) is a strict linear homogeneous inequality. Their intersection is open and convex and is closed under positive scalar multiplication. It is nonempty: any strictly positive matrix gives a point in it by (11.5). Being nonempty and open in $\mathbb R^3$, it has dimension three. The isomorphism $V$ preserves these properties and transports the five inequalities. Nothing in this argument replaces strict positivity by nonnegativity or adds the cone's boundary. ∎

## 12. Positive interpolation and the full zero-slope data test

**Corollary 12.1 (actual interpolation of prefix quotients).** For $S_0,S_1\in\mathcal A$ and $0\le\theta\le1$, set $X_\theta=(1-\theta)S_0+\theta S_1$. Then
$$
S_\theta=\rho_N(X_\theta)
=X_\theta-
\frac{\theta(1-\theta)\mathfrak b(S_0,S_1)}
{(1-\theta)\mathfrak b(S_0,N)+\theta\mathfrak b(S_1,N)}N
\tag{12.1}
$$
is an actual source, with $S_\theta=S_j$ at $\theta=j$ for $j=0,1$, and
$$
\mathsf B_{\rm pre}S_\theta
=(1-\theta)\mathsf B_{\rm pre}S_0
+\theta\mathsf B_{\rm pre}S_1.
\tag{12.2}
$$

**Proof.** Every entry of $X_\theta$ is strictly positive, including at both endpoints. Bilinearity of the determinant polar and $\det S_j=0$ give
$$
\det X_\theta=\theta(1-\theta)\mathfrak b(S_0,S_1),
$$
while linearity of $h$ gives the denominator in (12.1). Both endpoint values of $h$ are positive, so its convex combination is positive on the whole closed parameter interval. Theorem 10.2 gives (12.1), actual positivity, the endpoints and (12.2). Each source has its own positive factors of Proposition 1.2 and one unchanged row during its run on the same fixed history. This interpolates mathematical targets and their prefix quotients; it does not combine unexecuted histories into one acquisition. ∎

**Proposition 12.2 (necessary and sufficient full five-read test at $k=0$).** Fix any legal final word, set $A_4=WA_3$, and write
$$
t_4=\operatorname{tr}(A_4N),\qquad
b_4(X)=\operatorname{tr}(A_4X)-\operatorname{tr}X.
$$
For proposed data $\mathbf z=(z_0,\ldots,z_4)$, put $y_i=z_i-z_0$. First compute
$$
(\xi,\nu,\zeta)=V^{-1}(y_1,y_2,y_3)^{\mathsf T}.
$$
There is an actual target at slope zero if and only if (11.2) holds and
$$
y_4=b_4(H(\xi,\nu,\zeta))
+\frac{\xi\nu}{t\zeta}(t_4-t).
\tag{12.3}
$$
If so, it is uniquely
$$
S=S_*(\xi,\nu,\zeta),\qquad k=0,\qquad
D(\tau)=z_0-\operatorname{tr}S\quad(\tau\in\mathbb R).
\tag{12.4}
$$
If $t_4=t$, the full zero-slope quotient image is the linear image
$$
\widehat V(\mathcal K),\qquad
\widehat V=\mathsf B\circ H.
\tag{12.5}
$$
It is an open convex cone relative to the three-dimensional range of the injective linear map $\widehat V$. If $t_4\ne t$, the final condition (12.3) is still required; prefix feasibility alone is insufficient. On the whole $\mathscr G$, $\mathsf B$ has rank three when $t_4=t$ and is invertible when $t_4\ne t$.

**Proof.** Formula (10.3) gives $PE_{11}P^{-1}=N/t$, so (11.4) gives
$$
S_*=H(\xi,\nu,\zeta)+\frac{\xi\nu}{t\zeta}N.
$$
Applying $b_4$ proves exactly (12.3), since $b_4(N)=t_4-t$. Every actual solution of the first three zero-slope quotient equations is uniquely $S_*$ by Theorem 11.1; hence (12.3) is necessary and sufficient for the remaining quotient equation. With (12.4), the initial reading holds and each remaining original equation is
$$
\operatorname{tr}(A_iS)+D(i)=(\mathsf BS)_i+z_0=z_i
\quad(i=1,2,3,4).
$$
This proves both directions, uniqueness and the single whole drift, with actual realization supplied by Proposition 1.2.

The kernel of the first three rows of $\mathsf B$ is $\mathbb RN$. Its last row vanishes on this line exactly when $t_4=t$. This proves both rank assertions. In that case $\mathsf BN=0$, so the full quotient of $S_*$ equals $\widehat V(\xi,\nu,\zeta)$. Its first three coordinates are $V(\xi,\nu,\zeta)$, proving injectivity of $\widehat V$ and the relative dimension and openness in (12.5). If $t_4\ne t$, correction along $N$ changes the last quotient coordinate by precisely the nonzero coefficient in (12.3). There is no basis for dropping that coordinate or declaring the full image to be the linear cone (12.5). ∎

## 13. The exact correction obstruction at distinct slopes

**Theorem 13.1 (necessary and sufficient preservation of an auxiliary distinct-slope equality).** For any prefix in $\mathscr G$ and any legal final word, suppose that $X_0,X_1\in\mathcal P$ and finite real slopes $k_0\ne k_1$ satisfy
$$
\mathsf T_{k_0}X_0=\mathsf T_{k_1}X_1.
\tag{13.1}
$$
Define
$$
\eta_j=\frac{\det X_j}{h(X_j)},\qquad S_j=\rho_N(X_j)=X_j-\eta_jN.
$$
Then
$$
\mathsf T_{k_0}S_0=\mathsf T_{k_1}S_1
\quad\Longleftrightarrow\quad
\begin{cases}
\eta_0k_0=\eta_1k_1,\\
(t_4-t)(\eta_0-\eta_1)=0.
\end{cases}
\tag{13.2}
$$
If $t_4\ne t$, this is equivalent to $\eta_0=\eta_1=0$, or equivalently $\det X_0=\det X_1=0$. Thus this correction preserves (13.1) exactly when both positive auxiliary matrices were already actual rank-one sources. If $t_4=t$, the exact condition is solely $\eta_0k_0=\eta_1k_1$. These assertions concern this construction, and do not assert impossibility of actual collisions.

**Proof.** The prefix kernel equations give $\operatorname{tr}(A_iN)=t$ for $i=0,1,2,3$. Consequently
$$
\mathsf BN=(0,0,0,t_4-t)^{\mathsf T},\qquad
\mathsf CN=(t,2t,3t,4t_4)^{\mathsf T},
$$
$$
\mathsf T_kN=(kt,2kt,3kt,(t_4-t)+4kt_4)^{\mathsf T}.
\tag{13.3}
$$
Using (13.1), equality of the corrected quotients is equivalent to
$$
\eta_0\mathsf T_{k_0}N=\eta_1\mathsf T_{k_1}N.
\tag{13.4}
$$
Its first coordinate, with $t>0$, gives $\eta_0k_0=\eta_1k_1$. The next two coordinates repeat it. The last is
$$
(t_4-t)(\eta_0-\eta_1)+4t_4(\eta_0k_0-\eta_1k_1)=0,
$$
which, after the first condition, is exactly the second condition in (13.2). Conversely the two scalar conditions make every coordinate in (13.4) equal. This proves necessity and sufficiency without dividing by either slope or any sampled gain.

If $t_4\ne t$, the second condition gives $\eta_0=\eta_1$. The first then gives $\eta_0(k_0-k_1)=0$; the distinct-slope hypothesis forces both coefficients to be zero. Their denominators are positive, so this is exactly determinant zero for both matrices. Conversely determinant zero makes both corrections vanish. One can also see the separation directly: the minor formed from the first and fourth coordinates of the two vectors in (13.3) is
$$
t(t_4-t)(k_0-k_1),
$$
nonzero under exactly these two hypotheses.

If $t_4=t$, (13.3) instead becomes $kt(1,2,3,4)^{\mathsf T}$. Thus precisely the first scalar condition remains. For example, when $k_0=0$ and $k_1\ne0$, it requires $\eta_1=0$ and imposes no further condition on $\eta_0$ beyond the already assumed auxiliary equality and positivity. The reversed case is symmetric. This reconciles the level-preserving branch, including identity multipliers, without extending the two-zero-coefficient conclusion to it. Negative slopes and sampled gain erasures obey the same undivided identities.

Every corrected $S_j$ is actual by Theorem 10.2. If (13.2) holds, put
$$
\Delta=\operatorname{tr}(S_0-S_1),\qquad
D_0(\tau)=0,\qquad D_1(\tau)=\Delta\quad(\tau\in\mathbb R).
$$
At index zero, $\operatorname{tr}S_0=\operatorname{tr}S_1+\Delta$. At every $i=1,2,3,4$, (13.2) says exactly
$$
(1+ik_0)\operatorname{tr}(A_iS_0)
=(1+ik_1)\operatorname{tr}(A_iS_1)+\Delta.
\tag{13.5}
$$
These are all five original equations after adding the respective whole drifts, including an erased equation if a gain is zero. Proposition 1.2 supplies one fixed positive row in each run and positive columns through every unread atom of the same prescribed words. Distinct slopes ensure distinct targets. No existence of the auxiliary equality (13.1) is supplied by this preservation test. ∎

The step from equal correction coefficients to zero correction coefficients uses $k_0\ne k_1$. This hypothesis belongs to Theorem 13.1, not to the universal multiplicity question. Neither that step nor the theorem proves uniqueness at a common nonzero slope.

## 14. Interior final words and exact conjugate correspondence

**Corollary 14.1 (every nonidentity final multiplier in the interior normal form).** Take any admissible parameter tuple and first endpoint of Theorems 5.1–5.2, retaining all nonnegative-integral, primitive and rank-three filters, or its conjugate branch. For every legal final multiplier matrix $W\ne I$, a positive auxiliary equality (13.1) at distinct slopes survives the correction (10.4) if and only if both auxiliary matrices are already rank one. For $W=I$, the exact test is instead $\eta_0k_0=\eta_1k_1$.

**Proof.** Theorem 6.1 gives $t_4=t$ exactly when $W=I$ on the entire four-nonzero-entry subcase, including its conjugate. Apply the two respective branches of Theorem 13.1. This uses the full normal form with its first-endpoint and rank filters, rather than an arbitrary formally chosen lattice tuple. Identity is the multiplier matrix: a nonempty literal word such as $JJ$ belongs to the identity branch. For zero-component kernels Theorem 13.1 still holds, but Theorem 6.1 supplies no identity-only classification. ∎

**Proposition 14.2 (coordinate and realization correspondence under $J$).** For a conjugated history $A_i'=JA_iJ$, take $X'=JXJ$ and
$$
f_K'=-Jf_K,\qquad \ell_K'=-\ell_KJ,\qquad
(a',b',c',d')=(b,a,d,c).
$$
Then
$$
N'=JNJ,\quad r_K'=Jr_K,\quad l_K'=l_KJ,\quad t'=t,
\quad h'(X')=h(X),\quad
\rho_{N'}(X')=J\rho_N(X)J.
\tag{14.1}
$$
In the cone coordinates, $(\xi',\nu',\zeta')=(-\xi,-\nu,\zeta)$; the five inequalities and inverse in Section 11 correspond exactly.

**Proof.** The displayed parameter substitution gives the identities for $N',r_K',l_K',t'$. Substitution into (10.4) gives the identities for $h'$ and $\rho_{N'}$. If $E=\operatorname{diag}(-1,1)$, then $P'=JPE$, so
$$
(P')^{-1}X'P'=E(P^{-1}XP)E.
$$
The off-diagonal coordinates change sign and the lower-right coordinate is unchanged. In (11.5) the positive column becomes its $J$ permutation and the positive row becomes its $J$ permutation, proving exact equivalence of all inequalities and their inverses. Every transition $JW_iJ$ is a legal word, with an empty multiplier represented by $JJ$. For actual sources, the positive factors transfer as $f_+'=Jf_+$ and $\ell_+'=\ell_+J$, and trace cyclicity preserves all original signals. The slopes, whole drifts and recorded indices are unchanged. This is a correspondence between histories and their actual realizations, with no conjugation or inverse acquisition added to a run. ∎

## 15. Attribution, parameters, and dependency scope

The supplied positive-retraction proposal, titled *Positive rank-one retraction and convex prefix image on all G; an exact obstruction to repairing lifted distinct-slope collisions*, supplies the retraction, five-inequality cone, interpolation and correction-obstruction content developed with complete proofs in Sections 10–14. The earlier structural results and read bounds retain their attribution in Section 8. The dependencies and parameter identifications are as follows.

| Supplied result or notation | Correspondence and exact use here |
|---|---|
| Original sharp fixed-path recovery programme | The actual positive common-source model, arbitrary real slope, whole target, counted initial read and cumulative finite forward-word contract in Sections 1 and 9 remain unchanged |
| Current normal-form volume, Theorem 3.2 | Its $f,\ell,r_0,N$ are $f_K,\ell_K,r_K,N$ in (10.1); this primitive representation applies on all $\mathscr G$ and supplies $t>0$ and the kernel line |
| Current volume, Theorems 5.1–5.2 and 6.1 | Only Corollary 14.1 needs the exhaustive interior normal form and identity-only final-level theorem; all stated parameter, first-endpoint and rank filters remain in force |
| Positive-retraction proposal, additional theorem 1 and its interpolation corollary | Theorem 10.2 and Corollary 12.1, including actual positivity, determinant correction, unique representative and fixed actual sources |
| Positive-retraction proposal, additional theorem 2 | Theorem 11.1 and Proposition 12.2; its coordinates $(x,y,z)$ are $(\xi,\nu,\zeta)$ here, and its linear map $V$ is (11.1) |
| Positive-retraction proposal, additional theorem 3 | Theorem 13.1 and Corollary 14.1; the zero-correction conclusion requires distinct slopes and a nonpreserved final kernel level |
| Companion, Definition 19.1, Lemma 19.2, Theorem 20.1 and Corollary 20.2 | The same $\mathscr G$, all-slope rank facts, exhaustive regular/singular actual fibres and finite-or-arc alternative used to state the residual; these are credited existing results |
| Companion, Proposition 21.1 and current Proposition 7.2 | Common-slope-zero uniqueness, consistent with the exact zero-slope inverse here; no common-nonzero-slope uniqueness premise |
| Companion, Theorem 22.1 | The already excluded exact history ending at $(\begin{smallmatrix}2&3\\7&10\end{smallmatrix})$ with final multiplier $MJM$, not a new witness or an unresolved recovering candidate |
| Companion, Theorems 8.1–8.2 | Complete support for the credited bounds (8.1); neither prefix convexity nor the correction obstruction changes them |

The supplier's interior transition entry called $q$ is the normal form's $Q=1+nd$, distinct from a source entry $q$. Its first-endpoint determinant sign and integer parameter are $\epsilon,g$ in (5.10). The kernel coordinate $d$ is unrelated to the declared drift degree. The function $h(X)$ in (10.2) is unrelated to the integer $h$ in (5.2). No integer normal-form condition is imposed on an actual positive source or an auxiliary $X$.

If a trace-one kernel convention is used, $\overline N=N/t$. Then $\mathfrak b(X,\overline N)=h(X)/t$, the correction coefficient becomes $\overline\eta=t\eta$, and $\overline t_4=t_4/t$. Thus $\overline\eta\,\overline N=\eta N$ and both scalar conditions in (13.2) are unchanged in meaning. The primitive convention used here never silently normalizes $t$ to one.

The all-class retraction and cone results use only the primitive signed kernel and its positive trace, not the interior classification. The last-word corollary uses exactly that classification's four-nonzero-entry scope. Linear inverses, signed vectors, conjugations and positive full matrices are proof devices. Every retained actual source has the positive factorization and representation fibres of Proposition 1.2, with its original gain parameters $R=S/u$, $\alpha=u>0$, $\beta=uk$, and unchanged $D$. Attribution is not independent approval, formal certification, external priority or a missing-literature claim.

## 16. The unchanged all-slope completion and the construction's boundary

The universal actual-multiplicity obligation throughout $\mathscr G$ remains
$$
\begin{gathered}
\text{for every legal prefix in }\mathscr G\text{ and every legal final word }W,
\quad A_4=WA_3,\\
\text{there exist }S_0,S_1\in\mathcal A,\quad k_0,k_1\in\mathbb R,\\
(S_0,k_0)\ne(S_1,k_1),\qquad
\mathsf T_{k_0}S_0=\mathsf T_{k_1}S_1.
\end{gathered}
\tag{16.1}
$$
It asks for some colliding datum for each complete history, with one entire constant drift per run supplied by Proposition 7.1. Existing sufficient collision results apply where their literal hypotheses hold. The remaining unproved cases of (16.1) include all still-uncovered admitted interior tuples and first endpoints, both conjugate branches, and zero-component kernel geometries with arbitrary final words. The quantifier includes identity matrices, nonempty words with identity matrix, and empty words.

In particular (16.1) retains the possibility $k_0=k_1$ with $S_0\ne S_1$. In the interior nonidentity-final case, Theorem 6.1 makes $\mathsf B=\mathsf T_0$ invertible. This gives uniqueness at the common slope zero only. It does not prove invertibility of $\mathsf T_k$ at every other real slope, or uniqueness of positive rank-one sources at every singular member. At any common slope, a nonsingular $\mathsf T_k$ gives linear uniqueness; a singular $\mathsf T_k$ requires its own actual-source intersection analysis. Proposition 7.2 gives rank at least three at all slopes and invertibility at $-1/4$, not invertibility at all slopes. Therefore the residual cannot be narrowed to $k_0\ne k_1$ by invertibility of $\mathsf B$. The distinct-slope hypothesis of the correction theorem has no such global implication.

The new convexification is exact for the zero-slope prefix quotient: every positive full representative has one unique actual representative. For $t_4\ne t$, Proposition 12.2 keeps the final zero-slope condition, and Theorem 13.1 shows that correction of a positive auxiliary distinct-slope equality preserves the full collision only when both matrices already have rank one. For $t_4=t$, the exact test is instead $\eta_0k_0=\eta_1k_1$; it is a test on an already given equality, not an existence proof. Thus neither branch supplies an actual pair for every remaining history. This limits the stated retraction construction and does not prohibit collisions obtained by other means, including equal nonzero slopes.

In the companion's exhaustive fibre description, a proof of the remaining multiplicity statement must force some datum with two positive regular candidates, a positive regular and a positive singular candidate, two distinct positive singular candidates, or a positive arc. The finite bound of fourteen, the finite-or-arc alternative, convex prefix feasibility, local rank information and fixed-slope-zero uniqueness do not force one of those events. The already proved isolated collision ending at $(\begin{smallmatrix}2&3\\7&10\end{smallmatrix})$ remains credited as excluded; it proves no assertion about arbitrary other final words after that prefix.

The alternative completion remains one legal predetermined five-read history with global uniqueness for every actual target, a whole-target inverse and a necessary-and-sufficient actual-source image criterion for every real slope, including erased and negative gains. The zero-slope inverse (12.4) does not provide that alternative. Prefixes outside $\mathscr G$ remain in the unrestricted original programme. With $d$ now the declared drift degree, the credited bounds remain exactly
$$
C_{\mathrm{fix}}(d)=d+5\quad(d\ge1),\qquad
5\le C_{\mathrm{fix}}(0)\le6.
\tag{16.2}
$$
No universal actual-multiplicity theorem, globally recovering five-read history, or sharper read bound is established by Sections 10–16.

All results use strictly positive actual rank-one common sources, one fixed positive row per run, positive columns through every unread atom, predetermined forward cumulative $M/J$ words, the original reading clock and one entire constant drift per run. Strict cone boundaries are excluded. These are ordinary exact symbolic textual mathematics, with no adaptive-path lower bound, unrestricted atom optimum, empirical or general-neural-network claim, Lean/kernel certification, resource, bit, time, stability or physical acquisition-cost conclusion, external priority or absent-literature assertion.

## 追加锚（本行以下为增补区）
