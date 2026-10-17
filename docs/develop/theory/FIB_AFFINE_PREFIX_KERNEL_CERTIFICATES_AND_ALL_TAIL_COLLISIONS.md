# Prefix kernels and finite collisions for shared affine gain

Three sufficient prefix certificates obstruct uniform recovery from five readings with constant additive drift. The first fixes three transfer coordinates while the fourth endpoint of the prefix still has lower-right entry one; it covers every final word that leaves that stratum. The second uses a positive tangent section of an indefinite prefix kernel after the fourth endpoint has already left the stratum; it covers every final word, including the empty word. The third begins with the recorded permutation pattern $I,J,L$, permits an otherwise arbitrary legal fourth endpoint satisfying an explicit entry criterion, and covers every final word. A proved entry cone for the third certificate includes an arbitrary interior legal word. The hypotheses and continuation quantifiers of the three classes are distinct.

All three mechanisms produce finite collisions of actual strictly positive rank-one sources, with one whole constant drift and one unchanged positive row in each run. They preserve the exact target $(S,k,D)$ and the actual recorded clock. Complete support for the credited positive-degree equality is included. The unrestricted constant-drift optimum remains
$$
5\le C_{\mathrm{fix}}(0)\le6.
$$

## 1. Model, legal histories, and representation fibres

**Definition 1.1 (actual common-source model).** Put
$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
U=JM=\begin{pmatrix}1&1\\0&1\end{pmatrix},\qquad
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix}.
$$
A legal predetermined history has $A_0=I$ and $A_{i+1}=W_iA_i$, where each $W_i$ is a fixed finite word in $M,J$, possibly empty. Products act on the left and execute from right to left. Thus chronological $(M,J)$ implements $U$, and $(J,M)$ implements $L$. A scalar read advances the recorded index by one, including a read after an empty word. An unread atom does not advance that index.

The effective source, observations, and recovery target are
$$
S=\begin{pmatrix}p&q\\r&s\end{pmatrix},\qquad
p,q,r,s>0,\qquad ps=qr,
$$
$$
z_i=(1+ki)\operatorname{tr}(A_iS)+D(i),\qquad
k\in\mathbb R,\qquad \deg D\le d,
\tag{1.1}
$$
$$
\text{target }(S,k,D).
$$
Here the known upper degree is $d\ge0$, including smaller actual degrees and the zero polynomial. In original parameters $S=\alpha R$, $k=\beta/\alpha$, $\alpha>0$, $\beta\in\mathbb R$. Each run has a single positive rank-one relation $R$ and one fixed positive row. The constant-drift results below take $d=0$, write $D(\tau)=\delta$, and use exactly the indices $0,1,2,3,4$. The domain includes sampled gain zeros and negative gains.

There is no reset, source copy, inverse acquisition, adaptive word choice, combination of unexecuted histories, independent lifted source, or additional acquisition clock.

**Proposition 1.2 (actual realization and exact fibres).** Every source in Definition 1.1 is realized by
$$
\alpha=1,\qquad \beta=k,\qquad R=S,\qquad
f=\binom p r,\qquad \ell=(1,q/p).
\tag{1.2}
$$
All recorded and unread columns on every legal history are positive, and $\ell$ remains fixed. For a fixed effective target, all original relation/gain representations are exactly
$$
R=S/b,\qquad \alpha=b>0,\qquad \beta=bk,\qquad D\text{ fixed}.
\tag{1.3}
$$
For fixed $R=f\ell$, all positive factorizations are exactly $f'=\mu f$, $\ell'=\ell/\mu$, $\mu>0$.

**Proof.** Rank one gives $s=qr/p$, so $f\ell=S$. If $A=(\begin{smallmatrix}a&b\\c&e\end{smallmatrix})$, then
$$
\ell Af=\operatorname{tr}(AS)=ap+br+cq+es.
\tag{1.4}
$$
The identities
$$
M\binom{x}{y}=\binom{y}{x+y},\qquad
J\binom{x}{y}=\binom{y}{x}\qquad(x,y>0)
$$
prove positivity atom by atom, including inside unread words. Necessity of (1.3) follows from $S=\alpha R$ and $k=\beta/\alpha$; substitution proves sufficiency. For the factorization assertion, equality of first columns gives $f'=\mu f$ for a positive scalar, and equality of second columns determines the remaining row component. Different candidate runs may have different fixed rows. These representation freedoms do not identify different effective targets. ∎

Every legal word matrix is nonnegative integral with determinant $\pm1$. In particular its trace pairing with an entrywise positive matrix is positive.

## 2. Quotient operators and finite collision bridges

For a fixed five-read history, define on auxiliary real $2\times2$ matrices
$$
\mathcal L(X)_i=\operatorname{tr}(A_iX),\qquad
(\mathcal I v)_i=iv_i,\qquad
\mathcal Qv=(v_i-v_0)_{i=1}^4,
$$
$$
\mathsf B=\mathcal Q\mathcal L,\qquad
\mathsf C=\mathcal Q\mathcal I\mathcal L,\qquad
\mathsf T_k=\mathsf B+k\mathsf C.
\tag{2.1}
$$
The kernel of $\mathcal Q$ is exactly the constant five-vectors. Consequently
$$
\mathsf T_{k_0}S_0=\mathsf T_{k_1}S_1
\tag{2.2}
$$
means that the difference of the two undrifted observation vectors is constant. Its initial value is $\operatorname{tr}(S_0-S_1)$, since $A_0=I$ and the initial gain is one. Thus the whole polynomials
$$
D_0(\tau)=0,\qquad D_1(\tau)=\operatorname{tr}(S_0-S_1)
\tag{2.3}
$$
make all five original readings agree. This quotient removes exactly one whole constant drift.

Use determinant polarization
$$
\mathfrak b(X,Y)=\det(X+Y)-\det X-\det Y.
$$
For $S=(\begin{smallmatrix}p&q\\r&s\end{smallmatrix})$ and
$Y=(\begin{smallmatrix}P&Q\\R&T\end{smallmatrix})$,
$$
\mathfrak b(S,Y)=sP+pT-rQ-qR,
$$
$$
\det(S+\epsilon Y)=\det S+\epsilon\mathfrak b(S,Y)+\epsilon^2\det Y.
\tag{2.4}
$$
Expansion of the two $2\times2$ determinants proves both identities; in particular $\mathfrak b$ is symmetric bilinear.

**Lemma 2.1 (one-erasure obstruction).** If deletion of some noninitial endpoint $j\in\{1,2,3,4\}$ leaves a matrix span of dimension at most three, there are distinct positive rank-one sources with identical five observations at the common slope $k=-1/j$ and common drift zero. Uniform five-read recovery therefore requires four independent survivors after every noninitial deletion.

**Proof.** The survivors include $I$. Choose $A,B$ such that $I,A,B$ span them, repeating $I$ if necessary. There is a nonzero trace-zero annihilator
$$
X=\begin{pmatrix}a&b\\c&-a\end{pmatrix}
$$
of $A,B$: these impose only two homogeneous equations on three variables. For $A=(\begin{smallmatrix}u&v\\w&x\end{smallmatrix})$ the equation is
$$
(u-x)a+wb+vc=0.
$$
If $a\ne0$ or $bc<0$, the coefficients $a,-b,-c,-a$ contain both strict signs. Otherwise $a=0$, $bc\ge0$, and changing the sign of $X$ makes $b,c\ge0$, not both zero. Nonnegativity forces the appropriate off-diagonal entry of each selected matrix to vanish. A triangular nonnegative integral unimodular matrix has diagonal entries one, since their nonnegative integral product is one. Hence $\operatorname{diag}(1,-1)$ also annihilates $I,A,B$ and all survivors. Replace $X$ by it. We have obtained a nonzero annihilator $X=(\begin{smallmatrix}a&b\\c&e\end{smallmatrix})$ with both strict signs among $a,-b,-c,e$.

For $x,y>0$, put
$$
E(x,y)=\begin{pmatrix}xy&x\\y&1\end{pmatrix},\qquad
h(x,y)=exy+a-cx-by.
$$
This polynomial takes both signs. Its values at $(t,t)$ tend to $a$ as $t\downarrow0$; its values at $(T,T)/T^2$ tend to $e$; and its values at $(T,T^{-2})/T$ and $(T^{-2},T)/T$ tend to $-c,-b$ as $T\to\infty$. Each strictly signed coefficient therefore gives a finite positive point of that sign. Join two such points by a positive straight segment. Let $m>0$ be a lower bound on all entries of $E$ along this compact segment, let $h_-<0<h_+$ be its endpoint values, and put $\Delta=\det X$. Choose a finite
$$
\rho>\max\left\{\frac{\max_{a,b}|X_{ab}|}{m},
\frac{|\Delta|}{\min(-h_-,h_+)}\right\}.
$$
The intermediate value theorem gives a segment point with $h=-\Delta/\rho$. At that point $S_0=\rho E$ and $S_1=S_0+X$ are strictly positive and
$$
\det S_0=0,\qquad \det S_1=\rho h+\Delta=0.
$$
They are distinct positive rank-one sources. Their survivor traces agree. At the missing index the common gain is zero, and all five observations therefore agree with drift zero. Proposition 1.2 realizes both sources on exactly the prescribed words, with positive unread states and a fixed row in each run. ∎

**Lemma 2.2 (finite transfer collision).** Suppose $\mathsf T_a$ is invertible and put $\mathsf H=\mathsf T_a^{-1}\mathsf C$. If $\mathfrak b(S,\mathsf H S)$ takes both strict signs on positive rank-one sources, there are collisions with slopes $a,a+\epsilon$ for every sufficiently small $\epsilon>0$, using the whole drifts (2.3). The sources are distinct. At $a=0$ every sampled gain in these collisions is positive.

**Proof.** Choose signed sources $S^+,S^-$ and their positive factors $f^\pm,\ell^\pm$ from (1.2). Define
$$
f(\theta)=(1-\theta)f^++\theta f^-,\qquad
\ell(\theta)=(1-\theta)\ell^++\theta\ell^-,
\qquad S(\theta)=f(\theta)\ell(\theta),\quad 0\le\theta\le1.
$$
This is an actual positive rank-one path of degree at most two. If $m_f,m_\ell$ are the minima of the entries of the two endpoint columns and rows, then every source entry is at least $m=m_fm_\ell>0$. Write
$$
S(\theta)=V_0+\theta V_1+\theta^2V_2,\qquad
K=1+\max_{a,b}\sum_{j=0}^2|(\mathsf H V_j)_{ab}|.
$$
Here $V_0=f^+\ell^+$, $V_1=(f^--f^+)\ell^++f^+(\ell^--\ell^+)$, and $V_2=(f^--f^+)(\ell^--\ell^+)$. Thus all entries of $\mathsf H S(\theta)$ have magnitude less than $K$, and its determinant has magnitude at most $2K^2$. Let
$$
\eta=\min\{\mathfrak b(S^+,\mathsf H S^+),-\mathfrak b(S^-,\mathsf H S^-)\}>0.
$$
For any
$$
0<\epsilon<\min\{m/(2K),\eta/(4K^2)\},
\tag{2.5}
$$
the polynomial
$$
h_\epsilon(\theta)=\mathfrak b(S(\theta),\mathsf H S(\theta))
+\epsilon\det(\mathsf H S(\theta))
$$
has opposite strict endpoint signs. It has degree at most four, is nonzero, and has a root in $(0,1)$. A nonzero polynomial has finitely many distinct roots, by successive division by root factors. Its smallest root in that interval is therefore an exact finite algebraic choice $\theta_\epsilon$.

Set $S_1=S(\theta_\epsilon)$ and $S_0=S_1+\epsilon\mathsf H S_1$. Every entry of $S_0$ exceeds $m/2$. Equation (2.4) makes $\det S_0=0$, so both sources are positive rank one. Moreover
$$
\mathsf T_a S_0=\mathsf T_a S_1+\epsilon\mathsf C S_1
=\mathsf T_{a+\epsilon}S_1.
$$
Equation (2.3) now proves equality of all five original readings, including the initial one. The sources differ: the four coordinates $i\operatorname{tr}(A_iS_1)$ of $\mathsf C S_1$ are strictly positive, so $\mathsf H S_1$ cannot vanish. The slopes differ as well.

Every source has Proposition 1.2's original realization, not an independent lifted realization. Any additional positive upper bound can be imposed on $\epsilon$. If $a=0$, the gains are one and $1+\epsilon i>0$. More generally $|a|<1/16$ and $\epsilon<1/16$ ensure $1+ki>0$ for both slopes at $i\le4$. ∎

The matrices and linear maps in this section are proof devices. They do not supply extra observations or sources.

## 3. A diagonal-one prefix coefficient certificate

**Theorem 3.1 (three fixed transfer coordinates).** Fix any legal prefix $A_0=I,A_1,A_2,A_3$ whose lower-right entries are one. Write
$$
A_i=\begin{pmatrix}a_i&b_i\\c_i&1\end{pmatrix}\quad(1\le i\le3),
$$
and form
$$
V=\begin{pmatrix}
a_1-1&c_1&b_1\\
a_2-1&c_2&b_2\\
a_3-1&c_3&b_3
\end{pmatrix},\qquad
F=\begin{pmatrix}
a_1&c_1&b_1&1\\
2a_2&2c_2&2b_2&2\\
3a_3&3c_3&3b_3&3
\end{pmatrix}.
$$
Assume $\det V\ne0$ and put $K=V^{-1}F$. Label the output rows of $K$ by $P,Q,R$ and its input columns by $p,q,r,s$. Suppose
$$
K_{Q,r}=0,\qquad
\gamma=K_{P,r}-K_{Q,s}>0,\qquad
K_{R,q}>0\ \text{or}\ K_{P,s}<0.
\tag{3.1}
$$
Then every legal fifth endpoint $A_4=WA_3$ with $(A_4)_{22}\ne1$ has a finite actual-source collision. The sources and slopes are distinct, the slopes can be $0,\epsilon$ for arbitrarily small $\epsilon>0$, the drifts are (2.3), and every sampled gain is positive.

**Proof.** In source-entry order $(p,q,r,s)$, the first three rows of $\mathsf B$ are $[V,0]$, while the last $s$ coefficient is $(A_4)_{22}-1$. Hence
$$
\det\mathsf B=((A_4)_{22}-1)\det V\ne0.
\tag{3.2}
$$
Put $\mathsf H=\mathsf B^{-1}\mathsf C$. If
$\mathsf H X=(\begin{smallmatrix}P&Q\\R&T\end{smallmatrix})$, its first three equations give
$$
V(P,Q,R)^{\mathsf T}=F(p,q,r,s)^{\mathsf T}.
$$
Thus $P,Q,R$ are fixed by the prefix alone. Only $T$ depends on the final endpoint.

Consider the actual positive rank-one source
$$
S_+(t)=\begin{pmatrix}t^2&t^3\\1&t\end{pmatrix},\qquad t>0.
$$
In $\mathfrak b(S_+(t),\mathsf H S_+(t))$, the constant coefficient is $-K_{Q,r}=0$. The coefficient of $t$ is $K_{P,r}-K_{Q,s}=\gamma$: it comes from $sP-rQ$, while $pT$ and $-qR$ have order at least two. Thus this polynomial is
$$
\gamma t+\sum_{j=2}^6a_jt^j.
\tag{3.3}
$$
If $K_{R,q}>0$, take
$$
S_-(t)=\begin{pmatrix}t&1\\t^2&t\end{pmatrix}.
$$
Its limiting value at $t=0$ is $E_{12}$, and the constant coefficient of its transfer form is $-K_{R,q}<0$. If instead $K_{P,s}<0$, take
$$
S_-(t)=\begin{pmatrix}t^2&t\\t&1\end{pmatrix};
$$
its constant coefficient is $\mathfrak b(E_{22},\mathsf H E_{22})=K_{P,s}<0$. Both displayed sources have positive entries and zero determinant for every $t>0$. Write the chosen negative polynomial as
$$
-\zeta+\sum_{j=1}^4d_jt^j,\qquad \zeta>0.
$$
All degree bounds follow from linearity of $\mathsf H$ and bilinearity of $\mathfrak b$.

For explicit finite strict signs, put $A=\sum_{j=2}^6|a_j|$, $E=\sum_{j=1}^4|d_j|$, and choose
$$
t=\min\{1/2,\gamma/[4(1+A)],\zeta/[4(1+E)]\}>0.
$$
Then (3.3) is at least $\gamma t-At^2\ge3\gamma t/4>0$, and the negative polynomial is at most $-\zeta+Et\le-3\zeta/4<0$. No assumption on the fourth row of $\mathsf H$ entered either sign choice. Boundary matrices served only to identify coefficients; all signed sources are strictly positive.

Apply Lemma 2.2 with $a=0$, imposing also $\epsilon<1/8$. Its polynomial path, root choice, positivity bound, determinant identity, constant drifts, and Proposition 1.2 give the claimed finite collisions on the entire actual history. The sources may depend on the fixed final word: the quantifier is that each history has a collision, not that one source pair works for all histories. ∎

## 4. Uniform coverage while the prefix stays diagonal-one

Put
$$
P_c=\begin{pmatrix}c&1\\c-1&1\end{pmatrix},\qquad
N_c(v)=\begin{pmatrix}cv-1&v\\c&1\end{pmatrix}.
$$

**Theorem 4.1 (all non-upper-shear tails).** For all integers
$$
n\ge1,\qquad c\ge n+1,\qquad v\ge3,
\tag{4.1}
$$
the prefix
$$
I,\quad L^n,\quad P_c,\quad N_c(v)
\tag{4.2}
$$
satisfies Theorem 3.1's coefficient conditions. Every legal final multiplier whose matrix is not $U^b$, $b\ge0$, therefore has the finite collision of Theorem 3.1.

**Proof.** One legal implementation has successive prefix multipliers
$$
L^n,\qquad UL^{c-1-n},\qquad U^{v-1}J.
\tag{4.3}
$$
All exponents are nonnegative,
$$
(UL^{c-1-n})L^n=UL^{c-1}=P_c,\qquad
U^{v-1}JP_c=N_c(v).
$$
Replacing $L,U$ by $MJ,JM$ gives finite literal words, without interior reads. Any other legal implementation with the same endpoints is covered as well.

For (4.2), the rows of $V$ are
$$
(0,n,0),\qquad(c-1,c-1,1),\qquad(cv-2,c,v),
$$
and expansion along its first row gives $\det V=n(v-2)>0$. Set $d_*=v-2$ and $z=v-c(v-1)$. The prefix transfer equations give
$$
Q=q+(p+s)/n,
$$
$$
P=\frac{(cv-3-z/n)p+(v-cd_*)q+vr+(3-2v-z/n)s}{d_*},
\tag{4.4}
$$
$$
R=2cp+2(c-1)q+2r+2s-(c-1)(P+Q).
$$
Indeed the first equation is $nQ=p+nq+s$. Subtracting $v$ times the second prefix equation from the third yields
$$
d_*P+zQ=(cv-3)p+[3c-2v(c-1)]q+vr+(3-2v)s.
$$
Substitution of $Q$ proves (4.4), and the second equation gives $R$.

Consequently
$$
K_{Q,r}=0,\qquad
K_{P,r}-K_{Q,s}=\frac v{v-2}-\frac1n>0,
$$
$$
K_{R,q}=(c-1)\left(c+1-\frac v{v-2}\right).
\tag{4.5}
$$
Since $c\ge2$ and $v/(v-2)\le3$, the last quantity is positive except possibly $c=2,v=3$. The parameter constraints force $n=1$ there. For precisely $(n,c,v)=(1,2,3)$, $z=-1$, $d_*=1$, and
$$
K_{P,s}=(3-2v-z/n)/d_*=-2<0.
$$
Thus the alternative negative clause covers the exceptional boundary exactly.

It remains to identify all final words in the theorem. Write their multiplier matrix as
$$
W=\begin{pmatrix}h&b\\g&e\end{pmatrix}.
$$
It is nonnegative integral and unimodular, and
$$
(WN_c(v))_{22}=gv+e.
$$
If $g>0$, this is at least $v>1$. If $g=0$, unimodularity forces $h=e=1$, so $W=U^b$ and this entry is one. Thus the entry differs from one exactly for the asserted non-upper-shear matrices. Literal words with cancellations are classified by their resulting matrix. Equation (3.2) and Theorem 3.1 apply to every such final word, regardless of length. ∎

Both diagonal sequences vary in these covered histories: $(A_2)_{11}=c>1$, while $(A_4)_{22}>1$ and the first four lower-right entries are one. The upper-shear final branch stays in the lower-right-one stratum and is outside this theorem's diagonal-exit hypothesis.

**Proposition 4.2 (regular infinite witness).** Fix $n=3,c=6,v=3$ and take the final multiplier $W=U^mM$ for any integer $m\ge3$. The endpoints are
$$
I,\quad \begin{pmatrix}1&0\\3&1\end{pmatrix},\quad
\begin{pmatrix}6&1\\5&1\end{pmatrix},\quad
\begin{pmatrix}17&3\\6&1\end{pmatrix},\quad
\begin{pmatrix}6+23m&1+4m\\23&4\end{pmatrix}.
\tag{4.6}
$$
Deletion of any endpoint leaves four independent matrices, and $\mathsf B$ is invertible. Nevertheless Theorem 4.1 gives finite collisions.

**Proof.** Multiplication by $M$ first gives $(\begin{smallmatrix}6&1\\23&4\end{smallmatrix})$, then $U^m$ gives (4.6), proving legality. The first four matrices are independent because their three nonconstant trace coefficient rows have determinant $n(v-2)=3$. The unique five-matrix dependence, up to scale, has coefficients
$$
(m,\ 9-7m,\ 15m-30,\ 9-9m,\ 3).
$$
Its four entry sums are
$$
m+(9-7m)+6(15m-30)+17(9-9m)+3(6+23m)=0,
$$
$$
(15m-30)+3(9-9m)+3(1+4m)=0,
$$
$$
3(9-7m)+5(15m-30)+6(9-9m)+69=0,
$$
$$
m+(9-7m)+(15m-30)+(9-9m)+12=0.
$$
All five coefficients are nonzero for $m\ge3$. Any dependence among four survivors would extend to one with a zero coefficient, contradicting uniqueness. Finally $\det\mathsf B=(4-1)\det V=9\ne0$. This family therefore passes every deletion-span test of Lemma 2.1. Its upper-right final entry $1+4m$ also shows that its final multiplier is not a lower-shear tail preserving the preceding upper row. The witness establishes coverage beyond those narrower exclusions; the uniform theorem is the substantive assertion. ∎

## 5. An indefinite prefix-kernel tangent certificate

The next mechanism leaves the lower-right-one stratum within the prefix and treats singular final quotients as well.

**Theorem 5.1 (indefinite prefix kernel, every final word).** Fix any legal prefix
$$
A_0=I,\qquad A_1=L^n,\qquad A_2=P_c,\qquad
A_3=\begin{pmatrix}a&b\\x&e\end{pmatrix},
$$
where $n\ge1$, $c\ge n+1$ are integers and $e>1$. Set
$$
C=c-1,\qquad E=e-1,\qquad
\lambda=\frac{a-1-bC}{E},
\qquad \lambda>0,
$$
$$
A=2c-C/n,\qquad B_*=2-C/n,
$$
$$
\xi=\frac{3a-x/n-bA}{E},\qquad
\psi=\frac{2x-bC}{E},\qquad
\omega=\lambda/C,
$$
$$
\gamma=\frac bE-\frac{1+\lambda}{n},\qquad
\Lambda=\xi+\psi\omega-\omega(A+C\omega).
\tag{5.1}
$$
If $\gamma\Lambda<0$, then every legal fifth multiplier $W$, including the empty word, gives a finite actual-target collision on all five original readings. If $\mathsf B$ is invertible, the sources and slopes differ, with slopes $0,\epsilon$ for every sufficiently small $\epsilon>0$. If $\mathsf B$ is singular, the sources differ and both slopes can be zero. Every sampled gain is positive in both branches.

**Proof.** The first three rows of $\mathsf B$, in order $(p,q,r,s)$, are
$$
(0,n,0,0),\qquad(C,C,1,0),\qquad(a-1,x,b,E).
\tag{5.2}
$$
They are independent: the first has a nonzero $q$ entry, the second a nonzero $r$ entry, and the third a nonzero $s$ entry. Their kernel is exactly $\mathbb RN$, where
$$
N=\begin{pmatrix}1&0\\-C&-\lambda\end{pmatrix},\qquad
\det N=-\lambda<0.
\tag{5.3}
$$
Their products with its entry vector are $0$, $C-C$, and $a-1-bC-E\lambda=0$. This indefinite kernel depends only on the first four recorded endpoints.

Define a partial transfer map on arbitrary full matrices by
$$
G X=\begin{pmatrix}0&Q\\R_*&T_*\end{pmatrix},
$$
$$
Q=q+(p+s)/n,\qquad
R_*=Ap+Cq+2r+B_*s,
$$
$$
T_*=\frac{3(ap+xq+br+es)-xQ-bR_*}{E}.
\tag{5.4}
$$
The first three equations $\mathsf B(GX)=\mathsf C X$ hold, because they are precisely
$$
nQ=p+nq+s,\qquad
CQ+R_*=2(cp+Cq+r+s),
$$
$$
xQ+bR_*+ET_*=3(ap+xq+br+es).
$$
If $\mathsf B$ is invertible and $\mathsf H=\mathsf B^{-1}\mathsf C$, then $(\mathsf H-G)X$ lies in $\mathbb RN$ for every $X$. Only the scalar functional multiplying $N$ can depend on the final endpoint. Hence
$$
\mathfrak b(S,N)=0\quad\Longrightarrow\quad
\mathfrak b(S,\mathsf H S)=\mathfrak b(S,GS).
\tag{5.5}
$$

For $u>0$ use the positive rank-one curve
$$
Z(u)=\begin{pmatrix}u+Cu^2&\lambda u^2\\1+Cu&\lambda u\end{pmatrix}
=\binom u1(1+Cu,\lambda u).
\tag{5.6}
$$
It satisfies
$$
\mathfrak b(Z(u),N)=\lambda u-\lambda(u+Cu^2)+C\lambda u^2=0.
$$
Write $Z(u)=Z_0+uZ_1+u^2Z_2$, where
$$
Z_0=\begin{pmatrix}0&0\\1&0\end{pmatrix},\quad
Z_1=\begin{pmatrix}1&0\\C&\lambda\end{pmatrix},\quad
Z_2=\begin{pmatrix}C&\lambda\\0&0\end{pmatrix}.
$$
The polynomial $J_*(u)=\mathfrak b(Z(u),GZ(u))$ has degree at most four and zero constant coefficient, since $Q(Z_0)=0$. Moreover
$$
GZ_0=\begin{pmatrix}0&0\\2&b/E\end{pmatrix}.
$$
Thus its coefficient of $u$ is
$$
\mathfrak b(Z_1,GZ_0)+\mathfrak b(Z_0,GZ_1)
=b/E-(1+\lambda)/n=\gamma.
$$
For its leading coefficient,
$$
R_*(Z_2)=C(A+\lambda),\qquad
T_*(Z_2)=C\xi+\lambda\psi.
$$
Consequently
$$
\mathfrak b(Z_2,GZ_2)
=C(C\xi+\lambda\psi)-\lambda C(A+\lambda)
=C^2\Lambda.
$$
We have proved the exact identity
$$
J_*(u)=\gamma u+j_2u^2+j_3u^3+C^2\Lambda u^4.
\tag{5.7}
$$
The coefficient matrices with zero entries only identify this polynomial; every $Z(u)$ used as a source has $u>0$ and strictly positive entries.

Here are finite strict sign choices. Put
$$
A_* = |j_2|+|j_3|+C^2|\Lambda|,\qquad
u_-=\min\{1/2,|\gamma|/[4(1+A_*)]\},
$$
$$
u_+=2+\frac{|\gamma|+|j_2|+|j_3|+1}{C^2|\Lambda|}.
\tag{5.8}
$$
Then $0<u_-<1<u_+$. At $u_-$ the higher terms have total magnitude at most $A_*u_-^2<|\gamma|u_-/4$. At $u_+$ the lower terms have total magnitude at most
$(|\gamma|+|j_2|+|j_3|)u_+^3<C^2|\Lambda|u_+^4$.
The signs of $J_*(u_-)$ and $J_*(u_+)$ are therefore the opposite strict signs of $\gamma$ and $\Lambda$.

First suppose $\mathsf B$ is singular. Its first three rows have rank three, so its kernel is exactly $\mathbb RN$ and $\mathsf BN=0$. Define
$$
S_1=\begin{pmatrix}C/\lambda+1&1\\2C+2\lambda&2\lambda\end{pmatrix},
\qquad
S_0=\begin{pmatrix}C/\lambda+2&1\\C+2\lambda&\lambda\end{pmatrix}.
\tag{5.9}
$$
They are positive, $S_0-S_1=N$, and their determinants vanish because
$$
(C/\lambda+1)2\lambda=2C+2\lambda,\qquad
(C/\lambda+2)\lambda=C+2\lambda.
$$
Their quotient signals agree at slope zero. Their undrifted signals differ by the same constant $\operatorname{tr}N=1-\lambda$ at all five indices, so $D_0(\tau)=0$ and $D_1(\tau)=1-\lambda$ give a collision. If $\lambda=1$, the drifts coincide and the sources still differ. This branch needs no further sign argument.

Now suppose $\mathsf B$ is invertible. Equation (5.5) makes $J_*(u)$ the transfer form $\mathfrak b(Z(u),\mathsf HZ(u))$ on the entire positive interval $[u_-,u_+]$. One could apply Lemma 2.2 directly. A finite construction staying on this tangent curve is as follows. Let
$$
\eta=\min\{|J_*(u_-)|,|J_*(u_+)|\}>0,\qquad
m=\min_{a,b} Z(u_-)_{ab}>0.
$$
All entries of $Z(u)$ are nondecreasing for $u>0$, so $m$ bounds them below on the interval. With $Y_j=\mathsf H Z_j$, set
$$
K=1+\max_{a,b}\bigl(|(Y_0)_{ab}|+
u_+|(Y_1)_{ab}|+u_+^2|(Y_2)_{ab}|\bigr).
$$
Then $|\det(\mathsf HZ(u))|\le2K^2$ there. Choose any
$$
0<\epsilon<\min\{m/(2K),\eta/(4K^2),1/8\}.
\tag{5.10}
$$
The nonzero polynomial $J_*(u)+\epsilon\det(\mathsf H Z(u))$ has degree at most four and opposite strict endpoint signs. Its smallest root $u_\epsilon$ in $(u_-,u_+)$ exists and is a finite algebraic choice. Put
$$
S_1=Z(u_\epsilon),\qquad S_0=S_1+\epsilon\mathsf H S_1.
$$
Every entry of $S_0$ exceeds $m/2$, and (2.4) gives $\det S_0=0$. Also
$$
\mathsf T_0S_0=\mathsf B S_1+\epsilon\mathsf C S_1
=\mathsf T_\epsilon S_1.
$$
The sources differ because $\mathsf C S_1$ is strictly positive. With slopes $0,\epsilon$ and drifts (2.3), all five original observations agree, including index zero, and every sampled gain is positive. An arbitrary additional positive upper bound on $\epsilon$ is allowed.

Finally, both (5.9) and the nonsingular sources have the original positive factors of Proposition 1.2. All unread atoms of the fixed prefix and the arbitrary final word preserve their columns, while their respective rows remain unchanged. The singular and nonsingular branches exhaust all final endpoints. ∎

This theorem does not require a final diagonal exit or a nonsingular final quotient. Its invariant is the tangent condition $\mathfrak b(S,N)=0$, rather than three fixed output entries of a full transfer map.

## 6. Uniform coverage after an earlier diagonal exit

**Theorem 6.1 (every tail after $L^nN_c(v)$).** For all integers
$$
n\ge1,\qquad c\ge n+2,\qquad v\ge3,
\tag{6.1}
$$
every legal history with prefix
$$
I,\qquad L^n,\qquad P_c,\qquad L^nN_c(v)
\tag{6.2}
$$
and every legal fifth multiplier, including the empty word, satisfies Theorem 5.1 and has its finite actual-target collision.

**Proof.** Successive prefix multipliers can be
$$
L^n,\qquad UL^{c-1-n},\qquad L^nU^{v-1}J.
$$
The identities in (4.3) verify the first two endpoints and $U^{v-1}JP_c=N_c(v)$ verifies the last. These are finite literal words with no interior reads. The fourth endpoint is
$$
A_3=\begin{pmatrix}cv-1&v\\c+n(cv-1)&1+nv\end{pmatrix}.
\tag{6.3}
$$
Thus its lower-right entry has already changed within the first four reads. Its earlier upper-left entry $c$ also differs from one.

Set $d_*=v-2>0$ and $C=c-1$. In Theorem 5.1's notation,
$$
a=cv-1,\quad b=v,\quad x=c+n(cv-1),\quad E=nv,
$$
$$
\lambda=d_* /(nv)>0,\qquad
\gamma=-d_* /(n^2v)<0.
\tag{6.4}
$$
Indeed $a-1-bC=d_*$ and $b/E=1/n$. Put $z=vC-x$. Direct substitution into (5.1) gives
$$
\xi=\frac{cv-3+z/n}{nv},\qquad
\psi=\frac{2x-vC}{nv},
$$
$$
\Lambda=
\frac{c(v-1)-2n-2-d_*[cd_*+2(n-1)]/(vC)}{n^2v}.
\tag{6.5}
$$
For a complete simplification, multiplying the defining expression for $\Lambda$ by $nv$ gives
$$
nv\Lambda=cv-3+\frac{z+d_*}{n}
+\frac{d_*[2x-vC-d_*-2cnv]}{nvC}.
$$
Here
$$
2x-vC-d_*-2cnv=-cd_*+2(1-n),\qquad
z+d_*=cv(1-n)-c+n-2.
$$
Substituting these two identities gives (6.5).

To prove its numerator positive, let
$$
E_*=c(v-1)-2n-2-\frac{d_*[cd_*+2(n-1)]}{vC}.
$$
The parameter constraints imply $C\ge2$, $2n+2\le2c-2$, and
$cd_*+2(n-1)<cv$. Therefore
$$
E_*>c(v-3)+2-\frac{c(v-2)}C
=c(v-3)(1-1/C)+1-1/C>0.
$$
This includes $v=3$ and $n=1$. Thus $\Lambda>0$ and $\gamma\Lambda<0$ for every stated parameter. Theorem 5.1 applies to every final word; its singular branch removes any exceptional final-word condition. ∎

The prefix (6.2) satisfies neither Theorem 3.1's lower-right-one prefix hypothesis nor its upper-left-one mirror hypothesis. The parameter range (6.1) is the range proved here. No extension to $c=n+1$ is asserted by this uniform sign estimate.

**Proposition 6.2 (regular infinite witness with an early exit).** For $n=1,c=3,v=3$ and every integer $m\ge1$, take final multiplier $U^m$. The endpoints are
$$
I,\quad \begin{pmatrix}1&0\\1&1\end{pmatrix},\quad
\begin{pmatrix}3&1\\2&1\end{pmatrix},\quad
\begin{pmatrix}8&3\\11&4\end{pmatrix},\quad
\begin{pmatrix}8+11m&3+4m\\11&4\end{pmatrix}.
\tag{6.6}
$$
Deletion of any endpoint leaves four independent matrices, and $\mathsf B$ is invertible. Theorem 6.1 still gives a collision.

**Proof.** Legality follows from Theorem 6.1 and multiplication by $U^m$. The first three quotient rows have kernel $\mathbb RN$ with
$$
N=\begin{pmatrix}1&0\\-2&-1/3\end{pmatrix},\qquad \operatorname{tr}N=2/3.
$$
Any annihilator of all first-four trace functionals lies in this line and has trace zero, so it vanishes. Thus the first four matrices are independent.

Their unique five-matrix dependence has coefficients
$$
(4m,\ m,\ -17m,\ 3m-2,\ 2).
$$
Its four entry sums are
$$
4m+m-51m+8(3m-2)+2(8+11m)=0,
$$
$$
-17m+3(3m-2)+2(3+4m)=0,
$$
$$
m-34m+11(3m-2)+22=0,
$$
$$
4m+m-17m+4(3m-2)+8=0.
$$
Every coefficient is nonzero for integer $m\ge1$, so uniqueness excludes dependence among any four survivors. To check the quotient as well, the difference between its last and third rows is $(11m,0,4m,0)$; its product with the entry vector of $N$ is $3m\ne0$. Hence the last row removes the first-three-row kernel and $\mathsf B$ is invertible. This supplies a regular subclass whose collisions are not consequences of the one-erasure test. ∎

## 7. Mirrored certificates without extra acquisition

**Theorem 7.1 (exact conjugate correspondence).** Each of Theorems 3.1, 4.1, 5.1, and 6.1 has a mirror obtained by conjugating its endpoints by $J$. The mirrored statements retain the same recorded indices and all final-word quantifiers.

**Proof.** For an original history define $A'_i=JA_iJ$. Its transitions are $W'_i=JW_iJ$, legal finite words obtained by concatenating $J$, a word for $W_i$, and $J$. For an empty word this is $JJ=I$. Thus the primed history starts at $I$ and has the same number of reads and the same indices. Conjugation exchanges diagonal entries, exchanges off-diagonal entries, and preserves linear independence.

Apply the appropriate theorem to the primed history and its complete constructed sources $S'_j$, slopes, and entire constant drifts. Transfer back by
$$
S_j=JS'_jJ,\qquad f_j=Jf'_j,\qquad \ell_j=\ell'_jJ.
$$
These factors are positive, their product is $S_j$, and cyclicity of trace gives
$$
\operatorname{tr}(A_iS_j)=\operatorname{tr}((JA_iJ)S'_j)
$$
at every original index. Slopes and drifts are unchanged, so all original readings agree. The row is fixed in each original run and every original unread atom preserves its positive column. No conjugation is acquired or added to the original history: this is an algebraic correspondence between realizations.

In particular Theorem 3.1's mirror assumes first-four upper-left entries one and a final upper-left exit. The mirror of Theorem 4.1 covers all conjugate final multiplier matrices except $L^b$. The mirror of Theorem 6.1 covers every legal final word, including empty words, after the conjugate early-exit prefix. Conjugating the singular construction in (5.9) proves the mirrored singular branch as well. ∎

## 8. Credited read bounds with complete support

Let $C_{\mathrm{fix}}(d)$ be the minimum uniform number of exact reads over all legal predetermined histories recovering the whole target in (1.1).

**Theorem 8.1 (all-degree fixed-history lower bound).** For every $d\ge0$,
$$
C_{\mathrm{fix}}(d)\ge d+5.
$$

**Proof.** Use the injective open actual-target chart
$$
(p,q,r,k,\delta_0,\ldots,\delta_d)
\in(0,\infty)^3\times\mathbb R^{d+2},
$$
$$
S=\begin{pmatrix}p&q\\r&qr/p\end{pmatrix},\qquad
D(\tau)=\sum_{h=0}^d\delta_h\tau^h.
$$
It has dimension $N=d+5$, and Proposition 1.2 realizes every chart point. For any fixed $m$-read endpoint list its observation map $F$ is smooth:
$$
F_i=(1+ki)\bigl((A_i)_{11}p+(A_i)_{12}r+
(A_i)_{21}q+(A_i)_{22}qr/p\bigr)+
\sum_{h=0}^d\delta_hi^h.
$$
Suppose $m<N$, and let $\rho\le m<N$ be the largest attained derivative rank. If $\rho=0$, integration along line segments in a small convex chart ball makes $F$ constant there. Otherwise choose a nonzero $\rho$-minor. It remains nonzero on a neighborhood, where maximality makes the rank exactly $\rho$. Reorder coordinates and outputs so this minor comes first. The implicit function theorem makes the level set of the first $\rho$ outputs a smooth graph over a small connected open ball of dimension $N-\rho>0$. The differential of every remaining output lies in the span of the first $\rho$ differentials, and therefore vanishes on every tangent vector of the graph. Integrating along graph paths makes all outputs constant. Distinct graph points give distinct actual targets with identical complete data.

A fixed protocol with earlier stopping can be padded along its predetermined continuation, using empty words where needed. Equal complete padded data include equal prefixes and stopping decisions. This proves the fixed-history lower bound; it is not an adaptive-word lower bound. ∎

**Theorem 8.2 (terminal repetition and the six-read restriction).** For every $d\ge1$, the following legal $d+5$-read history recovers the whole target for every real slope:
$$
A_0=I,\quad A_1=L^2,\quad
A_2=Q_0=\begin{pmatrix}6&1\\5&1\end{pmatrix},\quad
A_3=T_0=\begin{pmatrix}11&2\\6&1\end{pmatrix},
$$
$$
A_i=B_0=\begin{pmatrix}17&3\\6&1\end{pmatrix}
\quad(4\le i\le d+4).
\tag{8.1}
$$
It uses seventeen literal atoms, independently of $d$. Consequently
$$
C_{\mathrm{fix}}(d)=d+5\quad(d\ge1),\qquad
5\le C_{\mathrm{fix}}(0)\le6.
\tag{8.2}
$$

**Proof.** The nonempty successive multipliers are $L^2,UL^3,UJ,U$. Their chronological atom blocks are
$$
(J,M,J,M),\quad
(J,M,J,M,J,M,M,J),\quad
(J,M,J),\quad(M,J),
$$
of lengths $4,8,3,2$, totaling seventeen. Multiplication gives
$$
Q_0=UL^5=(UL^3)L^2,\qquad T_0=UJQ_0,\qquad B_0=UT_0.
$$
There are $d$ final empty transitions and no interior reads in those atom blocks. Proposition 1.2 proves actual realization throughout.

Set $a_*=p+s$ and
$$
\chi=16p+6q+3r,\qquad t=6p+r,\qquad w=q-p.
$$
Their inverse is
$$
p=(\chi-3t-6w)/4,\quad
q=(\chi-3t-2w)/4,\quad
r=(11t+18w-3\chi)/2,\quad s=qr/p.
\tag{8.3}
$$
For example the first two numerators are $4p,4q$, and substitution in $t-6p$ gives $r$. At fixed $\chi$, positivity of $p,q,r$ defines a convex intersection of three open half-planes in $(t,w)$.

Trace expansion gives
$$
\operatorname{tr}(B_0S)=a_*+\chi,
$$
$$
\operatorname{tr}((B_0-I)S)=\chi,\qquad
\operatorname{tr}((B_0-L^2)S)=(\chi+3t+2w)/2,
$$
$$
\operatorname{tr}((B_0-Q_0)S)=2t+w,\qquad
\operatorname{tr}((B_0-T_0)S)=t.
\tag{8.4}
$$
The single polynomial
$$
P(\tau)=D(\tau)+(a_*+\chi)(1+k\tau)
$$
has degree at most $d$ because $d\ge1$. The final $d+1$ readings determine it:
$$
P(\tau)=\sum_{j=4}^{d+4}z_j
\prod_{\substack{4\le h\le d+4\\h\ne j}}\frac{\tau-h}{j-h}.
\tag{8.5}
$$
The denominators are fixed nonzero integers. This polynomial has the prescribed values; uniqueness follows because a nonzero degree-at-most-$d$ polynomial cannot have $d+1$ distinct roots. Sampled gain zeros remain interpolation data.

From the complete data form
$$
\chi=P(0)-z_0,\qquad W_*=2(P(1)-z_1)-\chi,\qquad
Y=P(2)-z_2,\quad Z=P(3)-z_3.
$$
Equations (8.4) give the undivided reduced map
$$
(W_*,Y,Z)=F_\chi(t,w,k)
=\bigl((1+k)(3t+2w)+k\chi,\ (1+2k)(2t+w),\ (1+3k)t\bigr).
\tag{8.6}
$$
At fixed $\chi$, with $g_j=1+jk$, its derivative is
$$
DF_\chi=
\begin{pmatrix}
3g_1&2g_1&3t+2w+\chi\\
2g_2&g_2&2(2t+w)\\
g_3&0&3t
\end{pmatrix}.
$$
Expansion gives
$$
\mathcal J=\det DF_\chi
=-(3t+2w+\chi)g_2g_3+4(2t+w)g_1g_3-3tg_1g_2
$$
$$
=(2t+2w-\chi)+(8t+6w-5\chi)k-6\chi k^2.
$$
Substituting $\chi,t,w$ gives
$$
-\mathcal J=p(96k^2+38k+6)+q(36k^2+24k+4)+r(18k^2+7k+1)
$$
$$
=p\bigl[96(k+19/96)^2+215/96\bigr]
+4q(3k+1)^2+r\bigl[18(k+7/36)^2+23/72\bigr]>0.
\tag{8.7}
$$
The strictly positive $p,r$ terms handle every real $k$, including $k=-1/3$.

Local nonsingularity alone is not the uniqueness argument. For $y=(t,w)$ and two points at fixed $\chi$, the exact identity
$$
k_0y_0-k_1y_1=\bar k(y_0-y_1)+\bar y(k_0-k_1)
$$
implies
$$
F_\chi(y_0,k_0)-F_\chi(y_1,k_1)
=DF_\chi(\bar y,\bar k)(t_0-t_1,w_0-w_1,k_0-k_1)^{\mathsf T}.
\tag{8.8}
$$
The midpoint has positive $p,q,r$ by (8.3), and its fourth entry is reconstructed as $qr/p$. Equation (8.7) makes the midpoint derivative invertible. Equal reduced outputs force equal $t,w,k$. Equal complete data already give the same $P,\chi$, hence the same $S$, and then the same entire polynomial
$$
D(\tau)=P(\tau)-(p+s+\chi)(1+k\tau).
\tag{8.9}
$$
This proves global uniqueness, including all gain-zero and negative-gain cases.

For completeness an exact finite inverse and image criterion are explicit. Interpolate $P$, form $\chi,W_*,Y,Z$, and require $\chi>0$. Consider the distinct real roots of
$$
H(k)=-(W_*-\chi k)(1+2k)(1+3k)
+2Y(1+k)(1+3k)-Z(1+k)(1+2k).
\tag{8.10}
$$
Its leading coefficient is $6\chi>0$, so it is a nonzero cubic with at most three distinct real roots; it has a real root by its opposite end limits and continuity. Repeated roots are considered once. For each root solve
$$
\begin{pmatrix}3g_1&2g_1\\2g_2&g_2\\g_3&0\end{pmatrix}
\binom t w=\begin{pmatrix}W_*-\chi k\\Y\\Z\end{pmatrix}.
\tag{8.11}
$$
At most one of $g_1,g_2,g_3$ vanishes. The unweighted row-pair determinants are $-1,-2,-1$, so every surviving pair is independent. The augmented determinant of (8.11) is exactly (8.10), enforcing all rows, including a zero-gain row's zero right-hand side. Explicitly define only the available values
$$
V_1=(W_*-\chi k)/g_1,\qquad V_2=Y/g_2,\qquad V_3=Z/g_3.
$$
Rows $2,3$ give $(t,w)=(V_3,V_2-2V_3)$; rows $1,3$ give $(V_3,(V_1-3V_3)/2)$; rows $1,2$ give $(2V_2-V_1,2V_1-3V_2)$.

Reconstruct by (8.3), require $p,q,r>0$, put $s=qr/p$, form (8.9), require the declared degree, and check every original equation (1.1) at every recorded index. Actual data supply a passing candidate. Conversely every passing candidate has Proposition 1.2's actual realization on exactly the legal words above, and the checked equations give all proposed readings. Equation (8.8) excludes two passing targets. This proves necessity and sufficiency of the finite common-image criterion as well as recovery. No compulsory division by a gain or a leading drift coefficient occurs.

The lower bound in Theorem 8.1 now proves the positive-degree equality. To obtain the constant-drift upper bound, use (8.1) with declared upper degree one: its endpoints are $I,L^2,Q_0,T_0,B_0,B_0$, at indices $0,\ldots,5$. The two terminal readings determine the affine $P$. The same inverse recovers the true whole $D$; for constant-drift image membership explicitly require (8.9) to be constant and check all six equations. Its restriction is globally injective on that submodel. The lower bound at $d=0$ is five. This proves (8.2). The terminal interpolation proof itself requires $d\ge1$; substituting degree zero into (8.5) would not be valid. ∎

The seventeen-atom number is a directly exhibited upper construction. No shortest-word or unrestricted atom optimum is asserted. These read bounds and the positive-degree equality are credited existing results; the prefix certificates do not improve those read counts.

## 9. A permutation-first arbitrary-endpoint certificate

**Theorem 9.1 (arbitrary fourth endpoint after $I,J,L$).** Consider any legal prefix
$$
A_0=I,\qquad A_1=J,\qquad A_2=L,\qquad
A_3=\begin{pmatrix}a&b\\x&e\end{pmatrix}.
$$
Define
$$
E=b+e-1,\qquad F=a+b-1,\qquad
\lambda=F/E,\qquad c_*=\lambda-1,
$$
and assume
$$
E>0,\qquad\lambda>1,\qquad
\Delta=F(x-3)+E(a-2x+2)>0.
\tag{9.1}
$$
Then every legal final endpoint $A_4=WA_3$, where $W$ is any predetermined finite $M/J$ word including the empty word, has a finite collision of distinct effective sources on all five original readings. If $\mathsf B$ is invertible, the slopes can be $0,\epsilon$ for every sufficiently small $\epsilon>0$, and both sources and slopes differ. If $\mathsf B$ is singular, both slopes can be zero and the sources differ. Every sampled gain is positive in both branches. Each run has one entire constant drift.

The first two transitions can be $J$ and $M$, since $MJ=L$. The endpoint $A_3$ must be a legal left continuation of $L$; no additional factorization, diagonal pattern, word-length bound, or survivor-span hypothesis is imposed. All legal implementations of these recorded endpoints are covered.

**Proof.** Use Section 2's quotient operators at the actual indices $0,1,2,3,4$. In entry order $(p,q,r,s)$, the first three rows of $\mathsf B$ are
$$
(-1,1,1,-1),\qquad(0,1,0,0),\qquad(a-1,x,b,e-1).
\tag{9.2}
$$
A vector in their kernel has $q=0$ and $r=p+s$. The last equation becomes $Fp+Es=0$. Thus these three rows have rank three and their kernel is exactly $\mathbb RN$, where
$$
N=\begin{pmatrix}1&0\\-c_*&-\lambda\end{pmatrix},\qquad
\det N=-\lambda<0.
\tag{9.3}
$$
This line depends only on the first four recorded endpoints.

For an arbitrary auxiliary full matrix $X=(\begin{smallmatrix}p&q\\r&s\end{smallmatrix})$, put
$$
Q=2(p+q+s),\qquad V_*=r-q-2p-2s,
$$
$$
T=\frac{(3a+2b-2x)p+(x+b)q+2br+(3e+2b-2x)s}{E},
\qquad R_*=T+V_*,
$$
$$
GX=\begin{pmatrix}0&Q\\R_*&T\end{pmatrix}.
\tag{9.4}
$$
The first three equations $\mathsf B(GX)=\mathsf C X$ are
$$
Q+R_*-T=q+r,\qquad Q=2(p+q+s),
$$
$$
xQ+bR_*+(e-1)T=3(ap+xq+br+es).
\tag{9.5}
$$
The first two follow by substitution. For the third, the left side is $xQ+bV_*+ET$, and expansion of
$$
ET=3(ap+xq+br+es)-xQ-bV_*
$$
is precisely (9.4). Hence all three equations hold on every full matrix. If $\mathsf B$ is invertible, $\mathsf H=\mathsf B^{-1}\mathsf C$ satisfies the same three equations, so $(\mathsf H-G)X$ is a scalar multiple of $N$ for every $X$. Only that scalar functional can depend on the final endpoint.

For $u>0$ consider the positive rank-one tangent section
$$
Z(u)=\begin{pmatrix}u+c_*u^2&\lambda u^2\\1+c_*u&\lambda u\end{pmatrix}
=\binom u1(1+c_*u,\lambda u).
\tag{9.6}
$$
Since $c_*,\lambda>0$, every entry is strictly positive. Direct substitution gives
$$
\mathfrak b(Z(u),N)=\lambda u-\lambda(u+c_*u^2)+c_*\lambda u^2=0.
$$
Consequently, whenever $\mathsf H$ exists,
$$
\mathfrak b(Z(u),\mathsf HZ(u))=\mathfrak b(Z(u),GZ(u)).
\tag{9.7}
$$
The final endpoint's contribution vanishes on this entire positive section, not merely at a limiting matrix.

Here is the complete sign calculation. Write
$$
Z(u)=Z_0+uZ_1+u^2Z_2,
$$
$$
Z_0=\begin{pmatrix}0&0\\1&0\end{pmatrix},\qquad
Z_1=\begin{pmatrix}1&0\\c_*&\lambda\end{pmatrix},\qquad
Z_2=\begin{pmatrix}c_*&\lambda\\0&0\end{pmatrix}.
$$
Let $J_*(u)=\mathfrak b(Z(u),GZ(u))$. This polynomial has degree at most four and zero constant term, since $Q(Z_0)=0$. Formula (9.4) gives
$$
GZ_0=\begin{pmatrix}0&0\\1+2b/E&2b/E\end{pmatrix}.
$$
Thus its linear coefficient is
$$
\gamma=\mathfrak b(Z_1,GZ_0)+\mathfrak b(Z_0,GZ_1)
=\frac{2b}{E}-2(1+\lambda)
=-\frac{2(a+b+e-2)}E<0.
\tag{9.8}
$$
Indeed $E$ is a positive integer, so $b+e\ge2$; and $\lambda>1$ is equivalent to $a>e$, so $a\ge1$. Hence $a+b+e-2>0$.

For the coefficient of $u^4$, put $A_*=3a+2b-2x$ and $B_*=x+b$. At $Z_2$,
$$
T_2=(A_*c_*+B_*\lambda)/E,\qquad R_2=T_2-\lambda-2c_*.
$$
Therefore
$$
\mathfrak b(Z_2,GZ_2)=c_*T_2-\lambda R_2
=-T_2+\lambda^2+2\lambda c_*.
$$
Multiplying by $E^2$ and using $\lambda=F/E$, $c_*=(F-E)/E$, gives
$$
F^2+2F(F-E)-A_*(F-E)-B_*F
=F(3F-A_*-B_*)+E(A_*-2F).
$$
The brackets are $x-3$ and $a-2x+2$. Thus this coefficient is
$$
\ell_* =\Delta/E^2>0.
$$
In particular the exact polynomial is
$$
J_*(u)=\gamma u+j_2u^2+j_3u^3+\ell_*u^4,
\qquad\gamma<0<\ell_*.
\tag{9.9}
$$
The remaining coefficients are fully specified, if desired without collecting monomials, by
$$
j_2=\mathfrak b(Z_0,GZ_2)+\mathfrak b(Z_1,GZ_1)+\mathfrak b(Z_2,GZ_0),
$$
$$
j_3=\mathfrak b(Z_1,GZ_2)+\mathfrak b(Z_2,GZ_1).
$$
The matrices with zero entries in this coefficient calculation are proof devices. Every source used in the collision has $u>0$.

To obtain finite strictly signed sources, set
$$
A_{\mathrm{bd}}=|j_2|+|j_3|+\ell_*,\qquad
u_-=\min\{1/2,|\gamma|/[4(1+A_{\mathrm{bd}})]\},
$$
$$
u_+=2+\frac{|\gamma|+|j_2|+|j_3|+1}{\ell_*}.
\tag{9.10}
$$
Then $0<u_-<1<u_+$. At $u_-$ the last three terms have total magnitude at most $A_{\mathrm{bd}}u_-^2<|\gamma|u_-/4$, so $J_*(u_-)<0$. At $u_+$ the first three terms have total magnitude at most $(|\gamma|+|j_2|+|j_3|)u_+^3<\ell_*u_+^4$, so $J_*(u_+)>0$. Both are actual positive rank-one sources.

If $\mathsf B$ is singular, (9.2)'s rank implies $\ker\mathsf B=\mathbb RN$. Define
$$
S_1=\begin{pmatrix}c_*/\lambda+1&1\\2c_*+2\lambda&2\lambda\end{pmatrix},\qquad
S_0=\begin{pmatrix}c_*/\lambda+2&1\\c_*+2\lambda&\lambda\end{pmatrix}.
\tag{9.11}
$$
All entries are positive, $S_0-S_1=N$, and
$$
(c_*/\lambda+1)2\lambda=2c_*+2\lambda,\qquad
(c_*/\lambda+2)\lambda=c_*+2\lambda
$$
prove that both determinants vanish. They are distinct. The equation $\mathsf BN=0$ says their unweighted signal difference is the same constant $\operatorname{tr}N=1-\lambda$ at every original index, including zero. Take slopes $k_0=k_1=0$ and whole constant drifts $D_0(\tau)=0$, $D_1(\tau)=1-\lambda$. Then all five observations agree, and all gains are one. This includes every singular final endpoint, whether or not its word is empty.

If $\mathsf B$ is invertible, put $\mathsf H=\mathsf B^{-1}\mathsf C$ and
$$
\eta=\min\{-J_*(u_-),J_*(u_+)\}>0,\qquad
m=\min_{a,b}Z(u_-)_{ab}>0.
$$
All entries of $Z(u)$ are nondecreasing for $u>0$, so $m$ bounds them below on $[u_-,u_+]$. Set $Y_j=\mathsf HZ_j$ and
$$
K=1+\max_{a,b}\bigl(|(Y_0)_{ab}|+u_+|(Y_1)_{ab}|+u_+^2|(Y_2)_{ab}|\bigr).
$$
Every entry of $\mathsf HZ(u)$ has magnitude less than $K$, and $|\det(\mathsf HZ(u))|\le2K^2$ throughout the interval. For any
$$
0<\epsilon<\min\{m/(2K),\eta/(4K^2),1/8\},
\tag{9.12}
$$
the polynomial
$$
f_\epsilon(u)=J_*(u)+\epsilon\det(\mathsf HZ(u))
$$
has degree at most four and opposite strict endpoint signs. The correction at each endpoint has magnitude less than $\eta/2$. The intermediate value theorem gives a root in $(u_-,u_+)$. Opposite signs make the polynomial nonzero, and successive division by root factors makes its distinct-root set finite. Its smallest root in that interval, denoted $u_\epsilon$, is an exact finite algebraic choice.

Set
$$
S_1=Z(u_\epsilon),\qquad S_0=S_1+\epsilon\mathsf H S_1.
\tag{9.13}
$$
Every entry of $S_0$ exceeds $m/2$. Equations (2.4), (9.7), and the root identity give
$$
\det S_0=\epsilon\bigl[J_*(u_\epsilon)+\epsilon\det(\mathsf HZ(u_\epsilon))\bigr]=0.
$$
Thus both sources are positive rank one. They are distinct because every coordinate $i\operatorname{tr}(A_iS_1)$ of $\mathsf C S_1$ is positive; $\mathsf B\mathsf H S_1=\mathsf C S_1$ therefore forbids $\mathsf H S_1=0$.

Choose $k_0=0$, $k_1=\epsilon$ and the entire constant polynomials
$$
D_0(\tau)=0,\qquad D_1(\tau)=\operatorname{tr}(S_0-S_1).
$$
The exact identity
$$
\mathsf T_0S_0=\mathsf B S_1+\epsilon\mathsf C S_1=\mathsf T_\epsilon S_1
$$
means, at each original $i=1,2,3,4$,
$$
\operatorname{tr}(A_iS_0)-(1+\epsilon i)\operatorname{tr}(A_iS_1)
=\operatorname{tr}(S_0-S_1).
$$
At $i=0$ this is the definition of the right side. Adding $D_1$ to the second run proves equality of all five readings. Both sources and slopes differ; all gains are strictly positive. An arbitrary further positive upper bound can be imposed on $\epsilon$. No gain is divided out.

Finally Proposition 1.2 realizes every source in (9.11) or (9.13) as $\alpha_j=1$, $\beta_j=k_j$, $R_j=S_j$, with a positive column $(p_j,r_j)^{\mathsf T}$ and a single unchanged row $(1,q_j/p_j)$. All unread columns on the originally prescribed words are positive. The singular and nonsingular branches exhaust every final endpoint. A collision in this positive-gain subdomain obstructs uniform recovery on the full arbitrary-real-slope domain. ∎

## 10. A whole entry cone and unrestricted interior words

**Theorem 10.1 (legal entry-cone coverage).** Every legal prefix $I,J,L,A_3$, with
$$
A_3=\begin{pmatrix}a&b\\x&e\end{pmatrix},\qquad x\ge3,\quad a\ge2x,
\tag{10.1}
$$
satisfies Theorem 9.1. Every legal final word, including the empty word, therefore has its finite actual-source collision. There is no additional diagonal, survivor-span, word-length, or clock-determinant hypothesis.

**Proof.** Because $A_3$ is a legal left continuation of $L$, its multiplier has a nonnegative integral unimodular matrix $W_2=(\begin{smallmatrix}h&t\\g&f\end{smallmatrix})$, and
$$
A_3=W_2L=\begin{pmatrix}h+t&t\\g+f&f\end{pmatrix}.
$$
In particular $x\ge e$. From (10.1), $a\ge6$ and $a>e$. If $e=0$, the absolute determinant of $A_3$ is $bx=1$, contrary to $x\ge3$. If $b=0$, its determinant gives $ae=1$, contrary to $a\ge6$. Hence $b,e\ge1$ and $E=b+e-1\ge1$. Also $a>e$ gives $F>E$, so $\lambda>1$. Finally
$$
F(x-3)\ge0,\qquad E(a-2x+2)\ge2E>0.
$$
Thus $\Delta>0$ and every hypothesis (9.1) holds. The complete singular and nonsingular constructions of Theorem 9.1 apply to every final word. ∎

**Corollary 10.2 (arbitrary interior legal word).** For any legal multiplier matrix $V$, including the empty word's matrix, any integers $c\ge3$, $m\ge2$, and any legal final multiplier $W$, the history with endpoints
$$
I,\qquad J,\qquad L,\qquad A_3=U^mVU L^c,\qquad A_4=WA_3
\tag{10.2}
$$
has the collision of Theorem 9.1.

**Proof.** Successive transitions can be $J$, $M$, $U^mVU L^{c-1}$, and $W$. All are predetermined finite words, since $U=JM$ and $L=MJ$, and none requires an interior read. Write $V=(\begin{smallmatrix}H&B\\G&F_*\end{smallmatrix})$. Each row is nonzero and nonnegative integral. Since
$$
UL^c=\begin{pmatrix}c+1&1\\c&1\end{pmatrix}
$$
is entrywise positive, so is $VUL^c=(\begin{smallmatrix}a_0&b_0\\x&e\end{smallmatrix})$. Its bottom entries satisfy
$$
x=c(G+F_*)+G\ge c\ge3,\qquad e=G+F_*\ge1.
$$
Left multiplication by $U^m$ preserves these bottom entries and makes $a=a_0+mx>2x$. Theorem 10.1 applies. Proposition 1.2 verifies the fixed row and positive unread columns on these exact words. Both word parameters $V,W$ are unrestricted and predetermined. Theorem 10.1 also covers legal cone endpoints without a selected factorization (10.2). ∎

**Proposition 10.3 (regular infinite witness).** For every integer $h\ge4$, the legal endpoints
$$
I,\qquad J,\qquad L,\qquad
A_3=\begin{pmatrix}7&2\\3&1\end{pmatrix},\qquad
A_4=\begin{pmatrix}7&2\\3+7h&1+2h\end{pmatrix}
\tag{10.3}
$$
have four independent survivors after deletion of any endpoint and an invertible $\mathsf B$, yet Theorem 10.1 supplies a finite collision.

**Proof.** The third endpoint transition after $L$ can be $U^2L^2$, since $A_3=U^2L^3$; the final multiplier is $L^h$. Along with the initial $J,M$ transitions, this proves legality at precisely indices $0,1,2,3,4$. The entry cone holds because $x=3$ and $a=7\ge6$.

The first four endpoint matrices are independent. In a relation among $I,J,L,A_3$, subtraction of the lower-right entry equation from the upper-left makes six times the $A_3$ coefficient zero. The upper-right equation then kills the $J$ coefficient, the lower-left kills the $L$ coefficient, and a diagonal equation kills the $I$ coefficient. The unique dependence on all five matrices, up to scale, has coefficients
$$
(15h,\ -2h,\ -22h,\ h-3,\ 3).
\tag{10.4}
$$
The four corresponding entry sums are
$$
15h-22h+7(h-3)+21=0,\qquad -2h+2(h-3)+6=0,
$$
$$
-2h-22h+3(h-3)+3(3+7h)=0,
$$
$$
15h-22h+(h-3)+3(1+2h)=0.
$$
All five coefficients are nonzero for $h\ge4$. Any four-matrix dependence would extend to a five-matrix dependence with a zero coefficient, contradicting uniqueness. Thus even deletion of the initial endpoint leaves independent survivors.

Here $E=2$, $F=8$, $\lambda=4$, and $c_*=3$, so
$$
N=\begin{pmatrix}1&0\\-3&-4\end{pmatrix}.
$$
The final quotient row on $N$ is
$$
\operatorname{tr}(A_4N)-\operatorname{tr}N
=\bigl[7-6-4(1+2h)\bigr]-(1-4)=-8h\ne0.
$$
It removes (9.2)'s one-dimensional kernel, proving $\mathsf B$ invertible. Theorem 9.1's nonsingular finite construction applies, with different sources and slopes, a whole constant drift per run, and the original positive factors. This witness shows coverage beyond Lemma 2.1's erasure failure. The entire cone theorem, rather than this witness, is the uniform assertion. ∎

## 11. The permutation-first mirror

**Theorem 11.1 (mirrored endpoint criterion and cone).** Conjugation by $J$ gives an exact mirror of Theorem 9.1 and every result of Section 10, with the same final-word quantifiers. In particular every legal prefix
$$
I,\qquad J,\qquad U,\qquad A_3=\begin{pmatrix}a&b\\x&e\end{pmatrix}
$$
with $b\ge3$ and $e\ge2b$, followed by every legal final word including the empty word, has a finite actual-source collision.

Explicitly the mirrored general criterion is
$$
\widetilde E=x+a-1>0,\qquad
\widetilde F=e+x-1,\qquad \widetilde\lambda=\widetilde F/\widetilde E>1,
$$
$$
\widetilde\Delta=\widetilde F(b-3)+\widetilde E(e-2b+2)>0.
\tag{11.1}
$$
The mirrored unrestricted-interior-word family has fourth endpoint $L^m\widetilde V L U^c$, where $\widetilde V$ is any legal word matrix, $c\ge3$, $m\ge2$.

**Proof.** Conjugation preserves $I,J$ and exchanges $L,U$. For $A_3=(\begin{smallmatrix}a&b\\x&e\end{smallmatrix})$ its conjugate is $(\begin{smallmatrix}e&x\\b&a\end{smallmatrix})$. Substitution into (9.1) gives exactly (11.1), while substitution into (10.1) gives $b\ge3,e\ge2b$. Each multiplier becomes $JW_iJ$, a legal finite word; an empty multiplier becomes $JJ=I$. Thus all actual recorded indices are unchanged. Conjugation of (10.2) gives the stated family because $JVJ$ ranges over all legal word matrices whenever $V$ does.

For either branch, take the full collision $S'_j,k_j,D_j$ of the conjugated history and set
$$
S_j=JS'_jJ,\qquad f_j=Jf'_j,\qquad\ell_j=\ell'_jJ.
$$
All factors are positive and $f_j\ell_j=S_j$. The row remains fixed within each original run. At every original index,
$$
\operatorname{tr}(A_iS_j)=\operatorname{tr}((JA_iJ)S'_j),
$$
so the same slopes and whole drifts give identical original observations. Proposition 1.2 proves positivity during every original unread atom. Invertibility and singularity are preserved by the invertible source-coordinate conjugation, so the singular same-slope construction and nonsingular distinct-slope construction both transfer. Conjugation also preserves independence of endpoint matrices, giving the mirrored regular witness. No conjugation acquisition is added to the original path. ∎

## 12. Credits and dependency boundaries

The original common-source recovery programme supplies the effective target, positive-scale representation fibre, counted initial read, arbitrary real affine-gain slope, and fixed finite-word history contract. The supplied *Shared affine gain and zero-crossing recovery* supplies that model and the actual-chart maximal-rank lower-bound method reproduced in Theorem 8.1. Its calibration-prefix results retain their restricted scope and are not premises of the prefix certificates.

The supplied *Terminal repetition and recorded-clock obstructions with affine gain* supplies the terminal-repetition construction, the determinant and exact-midpoint argument, the cubic common-image inverse, the all-degree lower-bound support, and the constant-drift six-read restriction reproduced in Section 8. It credits *Sharp positive-degree recovery and six-read stability with affine gain* for the established positive-degree equality and the source-coordinate, determinant, midpoint, and cubic methods. It credits *Seventeen literal atoms suffice at the sharp d+5 read count for every positive drift degree* for the degree-independent atom construction. Every premise used for the stated bounds is proved in Section 8. Additional atom-count comparisons and stability results in those sources are not asserted here without their separate proofs.

The one-erasure positive-secant construction and the quotient/sign-transfer bridge are reused from the terminal-repetition and obstruction text and its credited collision interfaces. Lemmas 2.1 and 2.2 prove the exact forms used here. That text's recorded-clock determinant obstructions concern specified constant-diagonal strata. They are not used here as sufficient recovery tests or an unrestricted classification.

The complete supplied two-mechanism staged companion, *Prefix kernels and finite collisions for shared affine gain*, supplies the full statements, proofs, credits, and support retained in Sections 1–8. Its two prefix mechanisms have the following attributions, alongside the third proposal.

| Supplied mechanism | Results retained here | Exact final-word scope |
|---|---|---|
| *A prefix certificate forces finite actual-source collisions independently of the final legal word* | Theorem 3.1, Theorem 4.1, Proposition 4.2, and their mirrors | Any final lower-right exit after a certified lower-right-one prefix; concretely every non-$U^b$ multiplier after (4.2), with $n\ge1,c\ge n+1,v\ge3$ |
| *An indefinite prefix-kernel certificate excludes every final continuation after earlier diagonal variation* | Theorem 5.1, Theorem 6.1, Proposition 6.2, and their mirrors | Every legal final word, including empty, under the stated kernel/sign criterion; concretely (6.2) with $n\ge1,c\ge n+2,v\ge3$ |
| *Every final continuation collides after a permutation-first prefix with an arbitrary fourth endpoint in a proved entry cone* | Theorem 9.1, Theorem 10.1, Corollary 10.2, Proposition 10.3, and Theorem 11.1 | Every legal final word, including empty, after any legal $I,J,L,A_3$ satisfying (9.1); in particular the whole cone (10.1) and its unrestricted-interior-word class, with exact conjugate statements |

The first mechanism uses earlier special-tail prefix equations verified in (4.4), with boundary coefficients independent of the final transfer row. The second supplies the positive tangent section of an indefinite prefix kernel and its explicit singular branch. Their regular infinite witnesses demonstrate coverage beyond erasure-span failure. The third reuses that quotient and tangent-section method with a different recorded initial pattern, a different prefix calculation, and the sign invariant $\Delta$. Sections 9–11 prove all its coefficient identities, finite signs, singular and nonsingular collision bridges, cone and interior-word quantifiers, witness, and mirror directly.

The third class has $A_1=J$, whose two diagonal entries are zero. The concrete classes (4.2), (6.2) have $A_1=L^n$ with both diagonal entries one, and their mirrors have $A_1=U^n$ with both diagonal entries one. Thus neither prior concrete prefix class literally contains the third class. The abstract Theorem 5.1 also fixes $A_1=L^n$; Theorem 3.1 requires a diagonal-one prefix. Constant-diagonal strata also fail at this third class's $A_1$. This scope comparison concerns the stated hypotheses, not an exhaustive proof of disjointness from every other collision argument.

No unprovided classification, external source, or nested supplier reference is a premise of these proofs. Supplier titles and credits convey mathematical attribution, without independent approval, external priority, or formal-certification force.

## 13. Exact residual and limits

These three certificates give sufficient collision conditions. A failure of their signs or prefix hypotheses establishes neither recovery nor impossibility by another mechanism. The first theorem leaves its concrete upper-shear final branch outside its final-diagonal-exit hypothesis. The second covers every tail after its certified early-exit prefixes, but does not establish its kernel form or opposite-sign condition for arbitrary first-four endpoints. Its uniform family is proved for $c\ge n+2$, and does not decide $c=n+1$ merely by that family estimate. The general certificate can still be checked with its own literal hypotheses.

The third theorem covers every legal fourth endpoint after $I,J,L$ satisfying $E>0,\lambda>1,\Delta>0$, and every legal final word. Its cone $x\ge3,a\ge2x$ is sufficient, not necessary for the general criterion. Its arbitrary interior word $V$ and final word $W$ in (10.2) are independently unrestricted predetermined words on the same actual history. It does not show that every fourth endpoint after $I,J,L$ satisfies that criterion or lies in the cone. Its mirror has the same limitations. Failed criteria and failed cone inequalities are not recovery certificates.

After the one-erasure obstruction and these sufficient classes are accounted for, the remaining universal obligation still includes arbitrary first-four recorded endpoint patterns, other ways of leaving both diagonal-one strata, other prefix-kernel geometries, and failed coefficient or tangent-section signs, except where a separate theorem applies with its own literal hypotheses. The cone result enlarges the excluded set; it does not exhaust that set's complement or classify all five-read histories.

A complete resolution of the constant-drift question still requires either a legal predetermined five-read history with a global inverse and a complete actual common-source image criterion for the entire $(S,k,D)$ at every real slope, including erased and negative gains, or finite actual-target collisions at all original readings for every remaining legal five-read history. Neither is established here. Thus
$$
5\le C_{\mathrm{fix}}(0)\le6
$$
remains the available interval. The original all-degree sharp recovery programme retains the whole target and its representation fibres. The credited equality $C_{\mathrm{fix}}(d)=d+5$ for $d\ge1$ does not settle the constant-degree case or classify all optimal histories.

Every collision here uses finite exact-real algebra and continuity, actual strictly positive rank-one sources, one entire constant drift in each run, original consecutive reading indices $0,1,2,3,4$, positive unread columns, and one unchanged positive row per run. Every matrix operation belongs to the same prescribed cumulative finite-word history. Positive-gain collisions obstruct uniform recovery on the larger arbitrary-real-slope domain. Finite algebraic root choices specify exact existence without asserting bit complexity, running time, numerical stability, or physical acquisition cost.

The conclusions do not establish adaptive-path lower bounds, unrestricted atom optima, off-image noise decoding, general neural-network performance, empirical or Lean/kernel certification, worldwide originality, or absence of other literature.

## 追加锚（本行以下为增补区）

<a id="erased-final-gain-model"></a>
## 14. An erased-final-gain mechanism and its actual-source domain

Sections 1–13 give three sufficient prefix mechanisms. The additional mechanism below uses a rank-one prefix kernel whose determinant polar has one strict sign. Its positive tangent section is empty. Instead it uses exact transfer at a sampled gain zero, two coefficient signs at different boundary rays, and a finite determinant correction between actual positive sources. Section 16 proves the coefficient conditions on an entire four-parameter legal family, for every final word. Section 17 proves a strict-one-sign diagnostic delimiting this particular transfer-sign method.

For these additional collision results the drift is constant. Retain precisely
$$
S=\begin{pmatrix}p&q\\r&s\end{pmatrix},\qquad
p,q,r,s>0,\qquad ps=qr,\qquad k\in\mathbb R,
$$
$$
z_i=(1+ki)\operatorname{tr}(A_iS)+\delta,\qquad
D(\tau)=\delta\quad\text{for every real }\tau,\qquad i=0,1,2,3,4.
\tag{14.1}
$$
The target remains the whole triple $(S,k,D)$. Here $A_0=I$ and $A_{i+1}=W_iA_i$, with each $W_i$ a predetermined finite word in the same $M,J$ as in Definition 1.1, including the empty word. Multiplication acts on the left and executes from right to left. Only scalar reads advance the index; all intermediate atoms in a word are unread. Sampled zero and negative gains remain in the domain.

**Actual realization and fibres.** For every source in (14.1), take
$$
\alpha=1,\qquad \beta=k,\qquad R=S,\qquad
f=\binom{p}{r},\qquad \ell=(1,q/p).
\tag{14.2}
$$
Then $f\ell=S$ because $s=qr/p$. For $A=(\begin{smallmatrix}a&b\\c&e\end{smallmatrix})$,
$$
\ell Af=ap+br+cq+es=\operatorname{tr}(AS).
$$
The row $\ell$ is fixed throughout this run. The identities
$$
M\binom{x}{y}=\binom{y}{x+y},\qquad
J\binom{x}{y}=\binom{y}{x}\qquad(x,y>0)
$$
show, atom by atom, that every recorded and unread column is positive on every prescribed word. Different candidate runs may have different fixed rows.

For a fixed effective target, its original gain/relation representations are exactly $R=S/t$, $\alpha=t>0$, $\beta=tk$, with $D$ unchanged: necessity follows from $S=\alpha R$ and $k=\beta/\alpha$, and substitution proves sufficiency. If $R=f\ell=f'\ell'$ are two positive factorizations, equality of their first columns gives $f'=\mu f$ for $\mu>0$; equality of the other column then gives $\ell'=\ell/\mu$. These are representation fibres only. Distinct $S$ or distinct $k$ give distinct effective targets.

On the four-dimensional auxiliary space of real $2\times2$ matrices put
$$
\mathsf B X=\bigl(\operatorname{tr}(A_iX)-\operatorname{tr}X\bigr)_{i=1}^4,
\qquad
\mathsf C X=\bigl(i\operatorname{tr}(A_iX)\bigr)_{i=1}^4,
\qquad \mathsf T_k=\mathsf B+k\mathsf C.
\tag{14.3}
$$
Subtracting the initial reading proves the exact equivalence
$$
\text{equal five data}\quad\Longleftrightarrow\quad
\mathsf T_{k_0}S_0=\mathsf T_{k_1}S_1,
\qquad \delta_1-\delta_0=\operatorname{tr}(S_0-S_1).
\tag{14.4}
$$
Indeed the initial equality is exactly the second equation; after subtracting it, each remaining equality is exactly one coordinate of the first. Conversely adding that initial equality to the four quotient equations recovers every original reading. Thus the quotient removes exactly one entire constant polynomial, with no independent per-reading offsets.

Write
$$
\mathfrak b(X,Y)=\det(X+Y)-\det X-\det Y.
$$
Expanding two-by-two determinants gives the symmetric bilinear form and the exact finite identity
$$
\mathfrak b\left(\begin{pmatrix}p&q\\r&s\end{pmatrix},
\begin{pmatrix}P&Q\\R&T\end{pmatrix}\right)=sP+pT-rQ-qR,
$$
$$
\det(X+tY)=\det X+t\mathfrak b(X,Y)+t^2\det Y.
\tag{14.5}
$$
All operators and boundary matrices below are proof devices on this auxiliary space. They are neither acquired inverse operations nor additional sources.

<a id="fixed-polar-prefix-invertibility"></a>
**Lemma 14.1 (prefix trace invertibility from strict fixed polar sign).** Let a legal prefix $I,A_1,A_2,A_3$ satisfy
$$
\ker\mathsf B_{\rm pre}=\mathbb RN,\qquad
\mathsf B_{\rm pre}X=
\bigl(\operatorname{tr}(A_iX)-\operatorname{tr}X\bigr)_{i=1}^3,
\tag{14.6}
$$
where $N\ne0$ has rank one and $\mathfrak b(S,N)$ has one strict fixed sign on every strictly positive rank-one $S$. Orient $N$ so that this sign is positive. Then $\operatorname{tr}N>0$, and
$$
\mathcal L_{\rm pre}X=
\bigl(\operatorname{tr}(A_iX)\bigr)_{i=0}^3
\tag{14.7}
$$
is invertible.

**Proof.** Write $N=(\begin{smallmatrix}n_{11}&n_{12}\\n_{21}&n_{22}\end{smallmatrix})$. Its polar on the actual positive rank-one sources $(\begin{smallmatrix}uv&u\\v&1\end{smallmatrix})$, $u,v>0$, is
$$
n_{11}+n_{22}uv-n_{12}v-n_{21}u>0.
\tag{14.8}
$$
Taking $u=v\downarrow0$ gives $n_{11}\ge0$. Taking $u=v\to\infty$ and dividing by $u^2$ gives $n_{22}\ge0$. Taking $(u,v)=(T^{-2},T)$ and dividing by $T$ gives $n_{12}\le0$ as $T\to\infty$; using $(u,v)=(T,T^{-2})$ gives $n_{21}\le0$.

If $\operatorname{tr}N=0$, both diagonal entries vanish. Since $\det N=0$, at least one off-diagonal entry also vanishes. Nonzeroness then makes $N$ a negative nonzero multiple of $E_{12}$ or $E_{21}$, where $E_{ab}$ is the matrix unit. Equation (14.6) forces the corresponding trace-paired off-diagonal entry of every $A_i$ to vanish. Every legal endpoint is nonnegative integral with determinant $\pm1$. A triangular such endpoint has diagonal product one, hence both diagonal entries one. All four endpoints would therefore lie in $\operatorname{span}\{I,E_{12}\}$ or $\operatorname{span}\{I,E_{21}\}$, making $\operatorname{rank}\mathsf B_{\rm pre}\le1$. This contradicts (14.6), whose kernel dimension one makes that rank three. Hence $\operatorname{tr}N>0$.

If $\mathcal L_{\rm pre}Y=0$, all three prefix differences vanish, so $Y=tN$. Its initial trace is zero, and $\operatorname{tr}N>0$ forces $t=0$. The four-dimensional map (14.7) is injective, hence invertible. One may normalize $\operatorname{tr}N=1$, in which case $\mathcal L_{\rm pre}N=(1,1,1,1)^{\mathsf T}$. ∎

<a id="erased-final-gain-certificate"></a>
## 15. A prefix-only coefficient certificate at the erased final gain

**Theorem 15.1 (four prefix tests, every final word).** Assume Lemma 14.1's prefix hypotheses, and define
$$
\mathbf d=(1,4/3,2,4)^{\mathsf T},\qquad
\mathsf P=\mathcal L_{\rm pre}^{-1}
\operatorname{diag}(\mathbf d)\mathcal L_{\rm pre},\qquad
X_\star=\mathcal L_{\rm pre}^{-1}\mathbf d.
\tag{15.1}
$$
Suppose the following four prefix-only coefficient tests hold:
$$
(X_\star)_{21}\ge0,\qquad (X_\star)_{12}\le0,
\qquad
(\mathsf P E_{12})_{21}<0,\qquad
(\mathsf P E_{21})_{12}>0.
\tag{15.2}
$$
For every predetermined finite legal final word $W$, including the empty word, set $A_4=WA_3$. Then there is $\epsilon_0>0$ such that every $0<\epsilon<\epsilon_0$ gives a finite collision of distinct strictly positive rank-one effective sources, at slopes
$$
k_0=-1/4,\qquad k_1=-1/4+\epsilon,
\tag{15.3}
$$
with one entire constant drift per run and with all five original observations equal. The first run has its final gain zero, and the second has all five sampled gains strictly positive. The threshold may depend on the fixed final word; no single threshold or source pair for all words is asserted.

**Proof: exact transfer including the erased reading.** Put $k_\circ=-1/4$. The fourth row of $\mathsf T_{k_\circ}Y$ is $-\operatorname{tr}Y$. If $\mathsf T_{k_\circ}Y=0$, then $\operatorname{tr}Y=0$, and its first three rows give
$$
(1-i/4)\operatorname{tr}(A_iY)=0\qquad(i=1,2,3).
$$
These three gains are nonzero, so $\mathcal L_{\rm pre}Y=0$. Lemma 14.1 gives $Y=0$. Thus $\mathsf T_{k_\circ}$ is invertible for every final word, even when $\mathsf B$ is singular. Set
$$
\mathsf H=\mathsf T_{k_\circ}^{-1}\mathsf C,
\qquad f_i=\operatorname{tr}(A_iS).
$$
The fourth row of $\mathsf T_{k_\circ}\mathsf H S=\mathsf C S$ gives
$$
\operatorname{tr}(\mathsf H S)=-4f_4.
\tag{15.4}
$$
For $i=0,1,2,3$, let $d_i=(1-i/4)^{-1}$, the entries of $\mathbf d$. The other three rows, together with (15.4) at $i=0$, give
$$
\operatorname{tr}(A_i\mathsf H S)
=i d_i f_i-4d_i f_4
=4(d_i-1)f_i-4d_i f_4.
$$
Here $id_i=4(d_i-1)$. Applying the exact prefix inverse yields
$$
\boxed{\ \mathsf H S=4\bigl(\mathsf P S-S-f_4X_\star\bigr).\ }
\tag{15.5}
$$
This identity holds on every auxiliary full matrix, with no determinant restriction. In the normalization of Lemma 14.1, $X_\star=\mathsf P N$ also follows directly from (15.1). No inverse or determinant condition on the final multiplier was used.

**Proof: opposite signs at finite actual sources.** Let $F(S)=\mathfrak b(S,\mathsf H S)$. On rank-one $S$, (14.5) gives $\mathfrak b(S,S)=2\det S=0$, so (15.5) implies
$$
F(S)/4=\mathfrak b(S,\mathsf P S)
-\operatorname{tr}(A_4S)\mathfrak b(S,X_\star).
\tag{15.6}
$$
Write $b_4=(A_4)_{12}\ge0$ and $c_4=(A_4)_{21}\ge0$. Substitution of the auxiliary boundary matrices into this identity gives exactly
$$
F(E_{12})/4=-(\mathsf P E_{12})_{21}
+c_4(X_\star)_{21}>0,
$$
$$
F(E_{21})/4=-(\mathsf P E_{21})_{12}
+b_4(X_\star)_{12}<0.
\tag{15.7}
$$
The strict terms in (15.2) keep these inequalities strict even if either final off-diagonal entry is zero.

Replace these boundary matrices by the actual positive rank-one sources
$$
S_+(t)=\begin{pmatrix}t&1\\t^2&t\end{pmatrix}
=\binom{1}{t}(t,1),\qquad
S_-(t)=\begin{pmatrix}t&t^2\\1&t\end{pmatrix}
=\binom{t}{1}(1,t),\qquad t>0.
\tag{15.8}
$$
Since $\mathsf H$ is linear, each $F(S_\pm(t))$ is a polynomial of degree at most four. Write
$$
F(S_\pm(t))=c_\pm+\sum_{j=1}^4a_{\pm,j}t^j,
\qquad c_+=F(E_{12})>0>c_-=F(E_{21}).
$$
Let $A_\pm=\sum_{j=1}^4|a_{\pm,j}|$ and choose the finite positive values
$$
t_\pm=\min\{1/2,\ |c_\pm|/[4(1+A_\pm)]\}.
\tag{15.9}
$$
For $0<t\le1$, the nonconstant terms have magnitude at most $A_\pm t$. At (15.9) this is strictly less than $|c_\pm|/4$. Hence $S^+=S_+(t_+)$ and $S^-=S_-(t_-)$ have the required opposite strict signs. Their entries and factors are strictly positive; the boundary matrices have not been used as sources.

**Proof: finite determinant-corrected sources.** Take the positive factors $S^\pm=f^\pm\ell^\pm$ displayed in (15.8), and interpolate the factors:
$$
f(\theta)=(1-\theta)f^++\theta f^-,\qquad
\ell(\theta)=(1-\theta)\ell^++\theta\ell^-,\qquad
S(\theta)=f(\theta)\ell(\theta),\quad0\le\theta\le1.
$$
All these sources are positive rank one. Let $m_f$ and $m_\ell$ be the smallest entries among the two endpoint columns and among the two endpoint rows, respectively. Every entry of $S(\theta)$ is at least $m=m_fm_\ell>0$. Write
$$
S(\theta)=V_0+\theta V_1+\theta^2V_2,
$$
$$
V_0=f^+\ell^+,\quad
V_1=(f^--f^+)\ell^++f^+(\ell^--\ell^+),\quad
V_2=(f^--f^+)(\ell^--\ell^+),
$$
and set
$$
K=1+\max_{a,b}\sum_{j=0}^2|(\mathsf HV_j)_{ab}|,
\qquad \eta=\min\{F(S^+),-F(S^-)\}>0.
$$
Then every entry of $\mathsf HS(\theta)$ has magnitude less than $K$, and its determinant has magnitude at most $2K^2$. Choose any
$$
0<\epsilon<\min\{m/(2K),\ \eta/(4K^2),\ 1/4\}.
\tag{15.10}
$$
Any further prescribed positive upper bound may be imposed. The polynomial
$$
g_\epsilon(\theta)=F(S(\theta))+
\epsilon\det(\mathsf HS(\theta))
$$
has degree at most four. Its correction at either endpoint has magnitude less than $\eta/2$, so its endpoint signs are opposite and strict. The intermediate value theorem gives a zero in $(0,1)$. The polynomial is nonzero because of those signs; successive division by distinct root factors bounds its number of roots by four. Its smallest root in that interval, $\theta_\epsilon$, is therefore an exact finite root choice. Put
$$
S_1=S(\theta_\epsilon),\qquad
S_0=S_1+\epsilon\mathsf H S_1.
\tag{15.11}
$$
Every entry of $S_0$ is greater than $m/2$. The exact determinant identity (14.5) gives
$$
\det S_0=\epsilon\bigl[F(S_1)+
\epsilon\det(\mathsf H S_1)\bigr]=0.
$$
Thus $S_0,S_1$ are finite strictly positive rank-one matrices, not merely tangent vectors or limiting boundary matrices. Their exact quotient equality is
$$
\mathsf T_{k_\circ}S_0
=\mathsf T_{k_\circ}S_1+\epsilon\mathsf C S_1
=\mathsf T_{k_\circ+\epsilon}S_1.
\tag{15.12}
$$

**Proof: all five original equations and whole drifts.** Define
$$
\Delta=\operatorname{tr}(S_0-S_1)
=\epsilon\operatorname{tr}(\mathsf HS_1)
=-4\epsilon\operatorname{tr}(A_4S_1)<0,
\qquad D_0(\tau)=0,\quad D_1(\tau)=\Delta
\quad(\tau\in\mathbb R).
\tag{15.13}
$$
The strict inequality holds because every legal endpoint is a nonzero nonnegative matrix and $S_1$ is entrywise positive. In particular $S_0\ne S_1$. Equation (15.12) and the initial trace identity give the following five original equalities, with their actual recorded gains:
$$
\begin{aligned}
\operatorname{tr}S_0
&=\operatorname{tr}S_1+\Delta,\\
\tfrac34\operatorname{tr}(A_1S_0)
&=(\tfrac34+\epsilon)\operatorname{tr}(A_1S_1)+\Delta,\\
\tfrac12\operatorname{tr}(A_2S_0)
&=(\tfrac12+2\epsilon)\operatorname{tr}(A_2S_1)+\Delta,\\
\tfrac14\operatorname{tr}(A_3S_0)
&=(\tfrac14+3\epsilon)\operatorname{tr}(A_3S_1)+\Delta,\\
0&=4\epsilon\operatorname{tr}(A_4S_1)+\Delta.
\end{aligned}
\tag{15.14}
$$
The last equality also follows directly from (15.13); it checks the erased final reading rather than discarding it. The first gains are $1,3/4,1/2,1/4,0$; the second are $1,3/4+\epsilon,1/2+2\epsilon,1/4+3\epsilon,4\epsilon$. The slopes differ, and (15.13) shows the sources and whole drifts differ as well. These targets are not representation fibres.

Finally realize each source by (14.2), with $k_j$ its specified slope. Each run uses one unchanged positive row, and every unread atom on the original predetermined words preserves its positive column. No word is chosen in response to data. This proves the theorem on the full actual-source model. The collisions at these admissible slopes obstruct uniform recovery on the arbitrary-real-slope domain; no assertion of collisions at every slope is needed. ∎

The theorem assumes no invertibility of the zero-slope quotient $\mathsf B$, no survivor-span condition, and no final-word length bound. Prefix geometry ensures the particular pencil member $\mathsf T_{-1/4}$ is invertible for all final words; other pencil members may be singular. The only reciprocal gains used in (15.1) are the four fixed nonzero gains at indices $0,1,2,3$. No unknown or zero gain is divided out.

<a id="erased-gain-four-parameter-family"></a>
## 16. Complete four-parameter legal coverage

**Theorem 16.1 (every final word after a rank-one fixed-sign prefix family).** For all positive integers $h,u,b$, all integers $a\ge2h+1$, and every predetermined finite legal word $W$, including empty, the endpoints
$$
A_0=I,\qquad A_1=L^hU^u,\qquad
A_2=L^{h+a}U^u,\qquad
A_3=U^bL^{h+a}U^u,\qquad A_4=WA_3
\tag{16.1}
$$
have the finite actual-target collisions of Theorem 15.1. All four coefficient tests hold uniformly throughout the stated parameter range, with no remaining test on $W$.

**Proof: legal words and exact prefix inverse.** Put $c=h+a$. Since $U=JM$ and $L=MJ$, successive prefix multipliers can be $L^hU^u$, $L^a$, $U^b$. Chronologically the first block is $u$ repetitions of $(M,J)$ followed by $h$ repetitions of $(J,M)$; the next is $a$ repetitions of $(J,M)$; the next is $b$ repetitions of $(M,J)$. The final block is exactly $W$. These are finite forward words, with no reads inside their blocks. Empty $W$ still supplies the distinct scalar read at index four. Direct multiplication gives
$$
A_1=\begin{pmatrix}1&u\\h&1+hu\end{pmatrix},\quad
A_2=\begin{pmatrix}1&u\\c&1+cu\end{pmatrix},\quad
A_3=\begin{pmatrix}1+bc&u+b(1+cu)\\c&1+cu\end{pmatrix}.
\tag{16.2}
$$
For an arbitrary auxiliary full matrix $X=(\begin{smallmatrix}p&q\\r&s\end{smallmatrix})$, introduce $x=p+s$ and $y=q+us$. Its four prefix traces are
$$
f_0=x,\qquad f_1=x+hy+ur,\qquad
f_2=x+cy+ur,\qquad
f_3=f_2+b\bigl[cp+(1+cu)r\bigr].
\tag{16.3}
$$
They have the exact linear inverse
$$
\begin{aligned}
x&=f_0,& y&=(f_2-f_1)/a,&
r&=(f_1-x-hy)/u,\\
p&=\bigl((f_3-f_2)/b-(1+cu)r\bigr)/c,&
s&=x-p,&q&=y-us.
\end{aligned}
\tag{16.4}
$$
Each divisor is a fixed positive integer. The first two differences in (16.3), when all three prefix differences vanish, give $ay=0$ and $ur=0$. The third gives $bcp=0$. Therefore
$$
\ker\mathsf B_{\rm pre}=\mathbb RN,\qquad
N=\begin{pmatrix}0&-u\\0&1\end{pmatrix}.
\tag{16.5}
$$
Conversely this $N$ makes all three differences zero, so the kernel assertion is exact. This nonzero $N$ has rank one, trace one, and
$$
\mathfrak b(S,N)=p+ur>0
\tag{16.6}
$$
on every actual positive source. Thus the family has precisely the required strict fixed-polar-sign geometry. In particular there is no positive source with $\mathfrak b(S,N)=0$.

**Proof: the first two coefficient tests.** Apply (16.4) to $\mathbf d=(1,4/3,2,4)^{\mathsf T}$. Define
$$
Y_\star=\frac2{3a},\qquad
R_\star=\frac{a-2h}{3au},\qquad
P_\star=\frac{2/b-(1+cu)R_\star}{c},\qquad
Q_\star=Y_\star-u+uP_\star.
$$
The result is
$$
X_\star=\begin{pmatrix}P_\star&Q_\star\\
R_\star&1-P_\star\end{pmatrix}.
\tag{16.7}
$$
The parameter restrictions give $a\ge3$, $c=h+a\ge4$, and $R_\star>0$. Hence
$$
P_\star<\frac2{bc}\le\frac12,\qquad
Y_\star\le\frac29,
$$
$$
Q_\star<\frac29-\frac u2\le-\frac5{18}<0.
\tag{16.8}
$$
Thus $(X_\star)_{21}>0$ and $(X_\star)_{12}<0$, stronger than the first two required weak inequalities. No lower bound on $P_\star$ is needed.

**Proof: the last two coefficient tests.** The prefix trace vector of $E_{12}$ is $(0,h,c,c)^{\mathsf T}$. After multiplication by $\operatorname{diag}(\mathbf d)$ it is $(0,4h/3,2c,4c)^{\mathsf T}$. Formula (16.4) then gives
$$
y=\frac{2c-4h/3}{a}=2+\frac{2h}{3a},\qquad
(\mathsf P E_{12})_{21}
=\frac{4h/3-hy}{u}
=-\frac{2hc}{3au}<0.
\tag{16.9}
$$
The prefix trace vector of $E_{21}$ is $(0,u,u,u+b(1+cu))^{\mathsf T}$. Its scaled vector is $(0,4u/3,2u,4u+4b(1+cu))^{\mathsf T}$. Its inverse has
$$
x=0,\qquad y=\frac{2u}{3a}>0,\qquad
r=\rho=\frac43-\frac{2h}{3a},
$$
$$
p=\frac{2u}{bc}+\frac{(1+cu)(4-\rho)}c>0,
\qquad 4-\rho=\frac{8a+2h}{3a}>0.
$$
Since $s=-p$, its remaining off-diagonal entry is
$$
(\mathsf P E_{21})_{12}=y+up>0.
\tag{16.10}
$$
Equations (16.8)–(16.10) prove all four tests for every allowed tuple, independently of the final word. The complete finite construction, all five equations, entire drifts, and original positive realizations now follow from Theorem 15.1. The final word is fixed before constructing the sources; the construction may depend on it. ∎

Both diagonals vary during this prefix: $(A_1)_{22}=1+hu>1$ and $(A_3)_{11}=1+bc>1$. Hence neither the lower-right-one hypothesis of Theorem 3.1 nor its upper-left-one mirror holds throughout the prefix. The concrete earlier families and Theorem 5.1 start with $L^n$ or, in their mirrors, $U^n$, whereas (16.2) has both off-diagonal entries positive and trace $2+hu>2$. The permutation-first mechanism starts with $J$, which also differs from (16.2). These are comparisons with the literal earlier hypotheses, not an exhaustive classification of other possible collision proofs.

<a id="strict-one-sign-method-boundary"></a>
## 17. A strict-one-sign diagnostic for the erased-gain method

**Proposition 17.1 (full survivor spans with a strictly negative erased-gain transfer form).** There is a legal five-read history with a rank-one strict-fixed-polar-sign prefix, invertible $\mathsf B$, and four independent survivors after deletion of any endpoint, for which
$$
\mathfrak b\bigl(S,\mathsf T_{-1/4}^{-1}\mathsf C S\bigr)<0
\tag{17.1}
$$
on every strictly positive rank-one actual source. Thus opposite transfer-form signs at this fixed erased-final-gain slope are not a universal consequence of those geometric and span conditions.

**Proof: legal history and prefix geometry.** Take
$$
A_0=I,\quad
A_1=M^2=\begin{pmatrix}1&1\\1&2\end{pmatrix},\quad
A_2=LM^2=\begin{pmatrix}1&1\\2&3\end{pmatrix},\quad
A_3=ULM^2=\begin{pmatrix}3&4\\2&3\end{pmatrix}.
$$
The predetermined final multiplier is
$$
W=MJM=L^2J=\begin{pmatrix}0&1\\1&2\end{pmatrix},\qquad
A_4=WA_3=\begin{pmatrix}2&3\\7&10\end{pmatrix}.
\tag{17.2}
$$
The chronological blocks are $(M,M)$, $(J,M)$, $(M,J)$, and $(M,J,M)$, with readings only at the displayed endpoints. They are finite forward words with actual indices $0,1,2,3,4$.

The three trace-free endpoint triples $(a-e,b,c)$ of $A_1,A_2,A_3$ are
$$
(-1,1,1),\quad(-2,1,2),\quad(0,4,2).
$$
Their determinant is $6+4-8=2\ne0$. This proves independence of the first four matrices: applying the linear projection $(\begin{smallmatrix}a&b\\c&e\end{smallmatrix})\mapsto(a-e,b,c)$ kills $I$ and makes the other three independent. The first three rows of $\mathsf B$ in entry order $(p,q,r,s)$ are
$$
(0,1,1,1),\qquad(0,2,1,2),\qquad(2,2,4,2).
\tag{17.3}
$$
Their first two equations give $q=-s$ and $r=0$; the third gives $p=0$. Hence their kernel is precisely
$$
\mathbb RN,\qquad N=\begin{pmatrix}0&-1\\0&1\end{pmatrix},
\qquad\mathfrak b(S,N)=p+r>0.
\tag{17.4}
$$
The last quotient row on $N$ is $(10-7)-1=2\ne0$, so $\mathsf B$ is invertible. Lemma 14.1 also makes $\mathsf T_{-1/4}$ invertible.

**Proof: every deletion leaves full span.** The five matrices satisfy
$$
3I-4A_1-6A_2+A_3+2A_4=0.
\tag{17.5}
$$
The four entry checks, in row order, are
$$
3-4-6+3+4=0,\qquad -4-6+4+6=0,
$$
$$
-4-12+2+14=0,\qquad 3-8-18+3+20=0.
$$
Since the first four matrices are independent, the space of five-matrix relations has dimension one. Every coefficient in (17.5) is nonzero. A dependence among any four survivors would extend to a relation with a zero coefficient, contradicting that one-dimensional relation space. This includes deletion of the initial endpoint as well as all four possible noninitial erasures.

**Proof: exact inverse and transfer coefficients.** For this prefix the four trace values are
$$
f_0=p+s,\quad f_1=p+q+r+2s,\quad
f_2=p+2q+r+3s,\quad f_3=3p+2q+4r+3s.
$$
Their linear inverse on arbitrary full matrices is
$$
x=f_0,\quad y=f_2-f_1,\quad r=f_1-x-y,
\quad p=(f_3-f_2-3r)/2,\quad s=x-p,\quad q=y-s.
\tag{17.6}
$$
Indeed $x=p+s$ and $y=q+s$, and direct substitution recovers $r,p,s,q$ in that order. Applying (17.6) to $\mathbf d$ gives
$$
X_\star=\begin{pmatrix}3/2&7/6\\-1/3&-1/2\end{pmatrix}.
\tag{17.7}
$$
Applying it instead to $(f_0,4f_1/3,2f_2,4f_3)$ gives all entries of $\mathsf P S$:
$$
\begin{aligned}
(\mathsf P S)_{11}&=(11p+8q+12r+11s)/2,\\
(\mathsf P S)_{12}&=(31p+40q+40r+47s)/6,\\
(\mathsf P S)_{21}&=(-p-4q+2r-5s)/3,\\
(\mathsf P S)_{22}&=-(9p+8q+12r+9s)/2.
\end{aligned}
\tag{17.8}
$$
For example the scaled inverse first gives $y=(2p+8q+2r+10s)/3$ and $r=(-p-4q+2r-5s)/3$; its $p$ equation then gives the first line of (17.8), and $s=x-p$, $q=y-s$ give the other entries. Thus (17.8) is a direct prefix inversion, without a numerical or lifted-source step. In particular $(\mathsf P E_{12})_{21}=-4/3$ and $(\mathsf P E_{21})_{12}=20/3$, but both weak inequalities on $X_\star$ in (15.2) fail. This prefix is (16.1) with $h=u=a=b=1$, outside $a\ge2h+1$.

**Proof: strict sign on the entire actual source domain.** Put $\mathsf H=\mathsf T_{-1/4}^{-1}\mathsf C$ and $F(S)=\mathfrak b(S,\mathsf H S)$. Equations (17.2) and (17.7) give
$$
f_4=2p+7q+3r+10s,\qquad
6\mathfrak b(S,X_\star)=-3p+2q-7r+9s.
\tag{17.9}
$$
Using (17.8) in the determinant polar, before any rank-one simplification, gives
$$
\begin{aligned}
6\mathfrak b(S,\mathsf P S)={}&-27p^2+8q^2-40r^2+33s^2\\
&-22pq-67pr+6ps-44qr+34qs-11rs.
\end{aligned}
\tag{17.10}
$$
Multiplication of the two expressions in (17.9) gives
$$
\begin{aligned}
6f_4\mathfrak b(S,X_\star)={}&-6p^2+14q^2-21r^2+90s^2\\
&-17pq-23pr-12ps-43qr+83qs-43rs.
\end{aligned}
\tag{17.11}
$$
For rank-one $S$, subtracting (17.11) from (17.10) in the exact transfer identity (15.6) yields
$$
\begin{aligned}
6F(S)/4={}&-21p^2-6q^2-19r^2-57s^2\\
&-5pq-44pr+18ps-qr-49qs+32rs.
\end{aligned}
$$
Now use exactly the actual constraint $ps=qr$. The $18ps-qr$ term becomes $17qr$. Completing squares proves the identity
$$
\boxed{\quad F(S)=-\frac23\left[
21p^2+5pq+44pr+49qs
+6\left(q-\frac{17r}{12}\right)^2
+\frac{167}{24}\left(r-\frac{384s}{167}\right)^2
+\frac{3375}{167}s^2\right].\quad}
\tag{17.12}
$$
For an explicit check, the first square contributes $6q^2-17qr+(289/24)r^2$. The second contributes $(167/24)r^2-32rs+(6144/167)s^2$. Their $r^2$ coefficients sum to $19$, and adding the last square makes the $s^2$ coefficient $(6144+3375)/167=57$. This recovers the displayed polynomial after $ps=qr$. Every bracket term in (17.12) is nonnegative on the actual domain, and $21p^2>0$. Therefore $F(S)<0$ for every strictly positive rank-one source, proving (17.1). All such sources have the fixed-row, positive-unread-state realization (14.2) on the exact words (17.2). ∎

This diagnostic proves only a method boundary. Even with strict fixed prefix polar sign, invertible $\mathsf B$, and all survivor spans full, the two-strict-sign hypothesis for transfer at $k=-1/4$ can fail everywhere. It does not prove that the history recovers the target. It does not exclude collisions at other slopes, nonlocal transfers, equal-slope constructions, or other finite actual-source mechanisms. Its recovery status is not determined by (17.12). In particular neither a failed coefficient test nor a transfer form with one strict sign is a recovery certificate.

<a id="erased-gain-credits-and-residual"></a>
## 18. Mathematical attribution, exact residual, and limits

The unchanged original recovery programme supplies the whole effective target, the counted initial read, arbitrary real affine-gain slopes, positive-scale fibres, and predetermined finite-word contract. The delivered companion source supplies the three mechanisms and all proofs retained in Sections 1–13, including the complete lower and upper support in Section 8. The following additional mathematical inputs are credited by their results rather than by any purported assessment or hidden dependency.

| Mathematical input result | Direct content here | Scope retained |
|---|---|---|
| Erased-final-gain prefix proposal | Lemma 14.1 and Theorem 15.1, including the exact transfer identity, four coefficient tests, actual positive approximants, finite determinant correction, all five equations, and entire drifts | Certified strict-fixed-polar-sign rank-one prefixes; every final word; no exhaustive geometric-class assertion |
| Four-parameter legal family in that proposal | Theorem 16.1, with all endpoint, kernel, inverse, parameter, and coefficient calculations | Every $h,u,b\ge1$, every $a\ge2h+1$, every predetermined final word including empty |
| Full-class audit's strict-one-sign diagnostic | Proposition 17.1, with the exact legal final word, full survivor spans, operator entries, polynomial expansion, and square completion | A limitation of the fixed erased-gain two-sign method only |
| Constant-drift quotient and finite transfer interface already in the companion and proposals | Equations (14.3)–(14.5) and the complete finite proof in Theorem 15.1 | Actual common sources and one entire drift per run; no tangent-only or independently lifted substitute |

Every mathematical premise used for the additional certificate, family, and diagnostic has been derived directly in Sections 14–17. Section 8 contains the retained complete proof of the credited bounds
$$
C_{\mathrm{fix}}(d)=d+5\quad(d\ge1),\qquad
5\le C_{\mathrm{fix}}(0)\le6.
\tag{18.1}
$$
Those read bounds are existing results. The new covered family does not improve the read count. The proposal's separate auxiliary determinant observation is not used. Neither historical nested sources nor supplier confidence, purported review, or hosted checks are premises of any proof here. These are ordinary conditional textual mathematics under the stated model, without an external priority or originality assertion.

To state the remaining geometric obligation precisely, let $\mathscr G$ be all legal first-four prefixes whose three difference rows have a kernel line generated by a nonzero rank-one matrix with one strict fixed determinant-polar sign on every positive rank-one actual source. Lemma 14.1 and the invertibility of $\mathsf T_{-1/4}$ hold throughout $\mathscr G$. Theorem 15.1 proves collisions only where (15.2) holds; Theorem 16.1 verifies those tests on the whole declared four-parameter family. No assertion is made that these inequalities exhaust $\mathscr G$.

For prefixes in $\mathscr G$ failing those tests, the unproved universal obstruction would still require, for every such prefix and every legal final word, finite positive rank-one sources and real slopes satisfying
$$
(S_0,k_0)\ne(S_1,k_1),\qquad
(\mathsf B+k_0\mathsf C)S_0=(\mathsf B+k_1\mathsf C)S_1.
\tag{18.2}
$$
Their entire drifts would then be fixed by (14.4). Equation (18.2) states the missing theorem, not a proof of it. Proposition 17.1 prevents replacing that obligation by a universal claim of opposite transfer signs at $-1/4$. It does not refute (18.2). The full strict-fixed-polar-sign rank-one class remains unresolved, as do the other residual prefix geometries in Section 13 unless another theorem applies with its literal hypotheses.

The unrestricted constant-drift question still requires either finite actual-target collisions for every remaining predetermined legal five-read history, or an explicitly legal five-read history with a global inverse and a necessary-and-sufficient actual-source image criterion for the entire $(S,k,D)$ at every real slope. Neither completion is established here. The global five-versus-six alternative in (18.1) remains open. The bounded appended delivery does not complete the unchanged global research programme.

All additional collisions use the actual indices $0,1,2,3,4$, a single fixed positive row in each run, positive columns at every unread atom, predetermined finite forward cumulative words, distinct effective targets, and one whole constant drift in each run. The erased gain is checked rather than normalized away. Arbitrary zero and negative gains remain part of the model even though the constructed counterexamples use the particular admissible slopes (15.3). No reset, copy, inverse acquisition, adaptive path, or combination of unexecuted alternatives occurs. The finite exact-real constructions assert no bit, time, stability, physical acquisition cost, adaptive lower bound, unrestricted atom optimum, empirical or general neural-network result, Lean/kernel certification, or worldwide originality.

<a id="global-actual-fibre-domain"></a>
## 19. Global pencil geometry on the fixed-polar-sign prefix class

The results below describe the entire actual fibre over every proposed five-read vector for every prefix in the class $\mathscr G$ of Section 18 and every legal final word. They also give a finite positive-gain collision for the exact history of Proposition 17.1. The negative erased-gain transfer form in that proposition remains valid and coexists with this collision at other slopes. The exact Section 17 history is consequently excluded as a recovering candidate. Section 23 states the current residual; Sections 14–18 retain their prior conditional statements and proofs.

Retain the matrices $M,J,U,L$ of Definition 1.1. Fix legal cumulative endpoints
$$
A_0=I,\qquad A_{i+1}=W_iA_i\quad(0\le i\le3),
$$
where each $W_i$ is a predetermined finite $M/J$ word, including the empty word. The final multiplier is arbitrary subject to that contract. The actual model is
$$
S=\begin{pmatrix}p&q\\r&s\end{pmatrix},\qquad
p,q,r,s>0,\qquad ps=qr,\qquad k\in\mathbb R,
$$
$$
z_i=(1+ik)\operatorname{tr}(A_iS)+\delta\quad(i=0,1,2,3,4),
\qquad D(\tau)=\delta\quad(\tau\in\mathbb R).
\tag{19.1}
$$
The target is the whole $(S,k,D)$. A read after an empty word still advances the reading index. Unread atoms do not advance it. All zero and negative gains remain admissible.

For clarity, every positive determinant-zero matrix here is an actual source, with the complete realization
$$
\alpha=1,\qquad \beta=k,\qquad R=S,
\qquad f=\binom p r,\qquad \ell=(1,q/p).
\tag{19.2}
$$
Indeed $s=qr/p$ gives $f\ell=S$, and for $A=(\begin{smallmatrix}a&b\\c&e\end{smallmatrix})$,
$$
\ell Af=ap+br+cq+es=\operatorname{tr}(AS).
$$
The column is positive throughout every recorded and unread atom because
$$
M\binom{x}{y}=\binom{y}{x+y},\qquad
J\binom{x}{y}=\binom{y}{x}\qquad(x,y>0).
$$
The row $\ell$ is fixed for that entire run. A different candidate run may have its own fixed positive row. The only gain/relation representations of a fixed effective target are $R=S/b$, $\alpha=b>0$, $\beta=bk$, with $D$ unchanged: these follow necessarily from $S=\alpha R$, $k=\beta/\alpha$, and substitution proves sufficiency. For a fixed relation, equality of first columns in two positive factorizations forces $f'=\mu f$, $\mu>0$, and equality of second columns then forces $\ell'=\ell/\mu$. These freedoms do not identify different effective targets.

On auxiliary full real matrices define
$$
\mathsf B X=\bigl(\operatorname{tr}(A_iX)-\operatorname{tr}X\bigr)_{i=1}^4,
\qquad
\mathsf C X=\bigl(i\operatorname{tr}(A_iX)\bigr)_{i=1}^4,
\qquad \mathsf T_k=\mathsf B+k\mathsf C.
\tag{19.3}
$$
For arbitrary proposed data $z=(z_0,\ldots,z_4)\in\mathbb R^5$ put
$$
y=(z_i-z_0)_{i=1}^4.
$$
Subtracting the initial equation of (19.1), and then restoring it, proves both directions of
$$
(S,k,D)\text{ realizes }z
\quad\Longleftrightarrow\quad
\mathsf T_kS=y,\quad
S>0\text{ entrywise},\quad\det S=0,\quad
D(\tau)=z_0-\operatorname{tr}S\text{ for every }\tau.
\tag{19.4}
$$
Strict positivity makes such a determinant-zero matrix nonzero rank one. In particular two runs collide exactly when
$$
\mathsf T_{k_0}S_0=\mathsf T_{k_1}S_1,
\qquad \delta_1-\delta_0=\operatorname{tr}(S_0-S_1).
\tag{19.5}
$$
There is one entire drift per run, rather than independently adjustable offsets at different indices.

Use the determinant polar
$$
\mathfrak b(X,Y)=\det(X+Y)-\det X-\det Y.
$$
For $X=(\begin{smallmatrix}p&q\\r&s\end{smallmatrix})$ and $Y=(\begin{smallmatrix}P&Q\\R&T\end{smallmatrix})$, direct expansion gives
$$
\mathfrak b(X,Y)=sP+pT-rQ-qR,
\qquad
\det(X+uY)=\det X+u\mathfrak b(X,Y)+u^2\det Y.
\tag{19.6}
$$
In particular the polar is symmetric bilinear. Auxiliary linear inverses used below are proof devices, never additional acquisitions.

**Definition 19.1 (the quantified prefix class).** The class $\mathscr G$ consists of all legal prefixes $I,A_1,A_2,A_3$ for which
$$
\mathsf B_{\rm pre}X=
\bigl(\operatorname{tr}(A_iX)-\operatorname{tr}X\bigr)_{i=1}^3
$$
has kernel exactly $\mathbb RN$, with $N\ne0$ of rank one, and $\mathfrak b(S,N)$ has one strict fixed sign on every strictly positive rank-one $S$. This is the same class as in Section 18; it imposes no coefficient tests from (15.2).

<a id="global-pencil-rank-and-erasure"></a>
**Lemma 19.2 (all-slope rank and a nonsingular erased-gain member).** For every prefix in $\mathscr G$ and every legal final word, the prefix trace map
$$
\mathcal L_{\rm pre}X=
\bigl(\operatorname{tr}(A_iX)\bigr)_{i=0}^3
$$
is invertible, $\operatorname{rank}\mathsf T_k\ge3$ for every real $k$, and $\mathsf T_{-1/4}$ is invertible. Thus every singular member of the full pencil has rank exactly three.

**Proof.** Orient $N=(\begin{smallmatrix}n_{11}&n_{12}\\n_{21}&n_{22}\end{smallmatrix})$ so that its polar is strictly positive. On the positive rank-one matrices $(\begin{smallmatrix}uv&u\\v&1\end{smallmatrix})$, it is
$$
n_{11}+n_{22}uv-n_{12}v-n_{21}u>0\qquad(u,v>0).
$$
Taking $u=v$ to zero and then to infinity, dividing by $u^2$ in the latter limit, gives $n_{11},n_{22}\ge0$. Taking $(u,v)=(T^{-2},T)$, dividing by $T$ and taking $T$ to infinity gives $n_{12}\le0$; the choice $(T,T^{-2})$ gives $n_{21}\le0$.

If $\operatorname{tr}N=0$, its diagonal entries vanish. Its zero determinant then forces at least one off-diagonal entry to vanish. Nonzeroness makes it a negative multiple of $E_{12}$ or $E_{21}$. The prefix equations force the trace-paired off-diagonal entry of every $A_i$ to vanish. Each endpoint is nonnegative integral and unimodular, since it is a product of $M,J$. A triangular such endpoint has diagonal product one, hence both diagonal entries one. All four prefix matrices would lie in the same two-dimensional span of $I$ and one off-diagonal matrix unit. Their three difference rows could not have rank three, contradicting the one-dimensional kernel of $\mathsf B_{\rm pre}$. Therefore $\operatorname{tr}N>0$.

Normalize $\operatorname{tr}N=1$. If $\mathcal L_{\rm pre}X=0$, then $\mathsf B_{\rm pre}X=0$, so $X=tN$; its zero initial trace gives $t=0$. The four-dimensional trace map is thus invertible. Also $\mathcal L_{\rm pre}N=(1,1,1,1)^{\mathsf T}$.

In its invertible coordinates $f_i=\operatorname{tr}(A_iX)$, $0\le i\le3$, the first three rows of $\mathsf T_k$ are
$$
g_if_i-f_0,\qquad g_i=1+ik,\qquad i=1,2,3.
\tag{19.7}
$$
At most one of these three gains vanishes. If none vanishes, the separate nonzero $f_i$ coefficients prove independence. If $g_j=0$, its row is $-f_0$; the other two rows have separate nonzero $f_i$ coefficients and are independent of it. This proves rank at least three at every real $k$.

At $k=-1/4$, the last row is $-f_0$, independently of $A_4$, and the first three gains are $3/4,1/2,1/4$. A vector in the kernel therefore has $f_0=0$ and then $f_1=f_2=f_3=0$. Prefix trace invertibility makes that vector zero. Hence $\mathsf T_{-1/4}$ is invertible for every final word, including empty. A singular four-dimensional member now has rank exactly three. ∎

<a id="global-exact-actual-fibre-theorem"></a>
## 20. An exhaustive actual-fibre theorem and the finite-or-arc alternative

**Theorem 20.1 (global actual fibres for every datum and final word).** Fix any prefix in $\mathscr G$, any legal final word, and any proposed $z\in\mathbb R^5$. Represent $\mathsf T_t$ as a $4\times4$ matrix in source-entry order $(p,q,r,s)$, and define
$$
\Pi(t)=\det\mathsf T_t,\qquad
m_y(t)=\operatorname{adj}(\mathsf T_t)y,
\qquad
\mathcal M_y(t)=\operatorname{reshape}_{2\times2}m_y(t),
\qquad Q_y(t)=\det\mathcal M_y(t).
\tag{20.1}
$$
Here the reshape puts the four coordinates into $(p,q,r,s)$ order. The polynomial $\Pi$ is nonzero of degree at most four, each entry of $\mathcal M_y$ has degree at most three, and $Q_y$ is either the zero polynomial or has degree at most six.

The entire actual fibre of $z$ consists exactly of the following candidates, with one entire drift attached to each source.

1. **Regular slopes.** For every real $t$ with $\Pi(t)\ne0$, retain
   $$
   S(t)=\mathcal M_y(t)/\Pi(t),\qquad k=t,
   \qquad D_t(\tau)=z_0-\operatorname{tr}S(t)\quad(\tau\in\mathbb R)
   \tag{20.2}
   $$
   if and only if $Q_y(t)=0$ and all four entries of $S(t)$ are strictly positive. If $Q_y$ is nonzero, only its distinct real roots can pass. If $Q_y\equiv0$, the same strict inequalities are applied at every real slope outside the roots of $\Pi$.
2. **Singular slopes.** For each distinct real root $t$ of $\Pi$, discard it if $\mathsf T_tX=y$ is inconsistent. Otherwise choose a particular full matrix $X_t$ and a nonzero generator $K_t$ of $\ker\mathsf T_t$. Form
   $$
   q_t(u)=\det X_t+u\mathfrak b(X_t,K_t)+u^2\det K_t.
   \tag{20.3}
   $$
   Retain exactly the matrices $S=X_t+uK_t$ satisfying $q_t(u)=0$ and all four strict entry inequalities, with
   $$
   k=t,\qquad D(\tau)=z_0-\operatorname{tr}(X_t+uK_t)
   \quad(\tau\in\mathbb R).
   \tag{20.4}
   $$
   A nonzero $q_t$ contributes at most its two distinct real roots, including the linear and constant cases. If $q_t\equiv0$, all real $u$ are considered subject to strict positivity.

This is a necessary-and-sufficient actual image criterion: the datum is in the image precisely when at least one candidate survives. It applies to every real slope, including all gain erasures and negative gains.

**Proof of polynomial claims and regular candidates.** Each entry of $\mathsf T_t$ has degree at most one, so determinant expansion gives $\deg\Pi\le4$. Lemma 19.2 gives $\Pi(-1/4)\ne0$, so this polynomial is not identically zero and has at most four distinct real roots. Each adjugate entry is a signed determinant of a $3\times3$ submatrix and has degree at most three. Multiplication by the fixed vector $y$ preserves that bound. Expanding the two-by-two determinant gives the stated degree bound for nonzero $Q_y$, without excluding the identically-zero case.

For $\Pi(t)\ne0$, the cofactor identity
$$
\mathsf T_t\operatorname{adj}(\mathsf T_t)=\Pi(t)I
$$
gives the unique auxiliary solution $S=\mathcal M_y(t)/\Pi(t)$ of $\mathsf T_tS=y$. Its determinant is
$$
\det S=Q_y(t)/\Pi(t)^2.
$$
Consequently determinant zero and strict entry positivity are exactly the regular retention conditions. This division is by a known nonsingular pencil determinant at the candidate slope, not by a sampled gain.

**Proof of all singular branches and strict positivity handling.** At every root $t$ of $\Pi$, Lemma 19.2 gives rank three. If the system is consistent, its entire auxiliary solution set is exactly the affine line $X_t+\mathbb RK_t$; if inconsistent, it supplies no source. Formula (19.6) makes its determinant exactly (20.3). A nonzero polynomial of degree at most two has at most two distinct real roots, with a nonzero constant having none. Repeated roots are included only once. If all three coefficients vanish, the determinant is zero for every $u$, rather than just at selected roots.

The positivity set on this line is exactly
$$
I_t=\bigcap_{a,b\in\{1,2\}}
\{u\in\mathbb R:(X_t)_{ab}+u(K_t)_{ab}>0\}.
\tag{20.5}
$$
Each factor is an open half-line, all of $\mathbb R$, or empty, according to its coefficients. The intersection is an open interval, possibly unbounded, all of $\mathbb R$, or empty. No zero entry at a boundary is retained. In the nonzero-polynomial branch retain exactly its real roots in $I_t$; in the identically-zero branch retain all of $I_t$. Changing $X_t$ to another particular solution or rescaling $K_t$ only reparametrizes this same affine line and does not change the retained sources. Thus all singular cases, including zero determinant polynomials and empty positive intersections, are covered without division by a gain or by $\Pi(t)$.

**Proof of both directions and all five original equations.** An actual target producing $z$ satisfies $\mathsf T_kS=y$ by (19.4). If $\Pi(k)\ne0$, uniqueness of the auxiliary solution puts it in (20.2), where determinant zero is exactly $Q_y(k)=0$. If $\Pi(k)=0$, consistency and rank three put it on exactly the line above, and determinant zero is exactly $q_k(u)=0$. Positivity passes in either case, and the initial reading fixes its whole drift as displayed. No actual target is omitted.

Conversely, every retained candidate is a strictly positive determinant-zero matrix, hence rank one, and satisfies $\mathsf T_kS=y$. Set $\delta=z_0-\operatorname{tr}S$, a single constant for the whole run. Its original equations are explicitly
$$
\begin{aligned}
\operatorname{tr}S+\delta&=z_0,\\
(1+k)\operatorname{tr}(A_1S)+\delta
&=(\mathsf T_kS)_1+z_0=z_1,\\
(1+2k)\operatorname{tr}(A_2S)+\delta
&=(\mathsf T_kS)_2+z_0=z_2,\\
(1+3k)\operatorname{tr}(A_3S)+\delta
&=(\mathsf T_kS)_3+z_0=z_3,\\
(1+4k)\operatorname{tr}(A_4S)+\delta
&=(\mathsf T_kS)_4+z_0=z_4.
\end{aligned}
\tag{20.6}
$$
If $1+jk=0$, the quotient equation is $y_j=-\operatorname{tr}S$, so (20.6) enforces $z_j=\delta$ at that erased reading. Such an equation has been checked, not discarded. Negative gains need no separate normalization. Realization (19.2) supplies one common actual source, one fixed positive row, and positive columns through every unread atom of the same prescribed history. This proves sufficiency and necessity on the actual model. ∎

<a id="global-finite-or-arc-dichotomy"></a>
**Corollary 20.2 (finite multiplicity at most fourteen, or a continuous arc).** Every fibre in Theorem 20.1 is either finite with at most fourteen actual targets or contains a nontrivial continuous arc of distinct actual targets. The empty fibre is included in the finite alternative. Fourteen is an upper bound, not a claimed sharp optimum.

**Proof.** A nonzero degree-at-most-$m$ polynomial has at most $m$ distinct real roots: divide successively by the distinct root factors; a product of more than $m$ such factors cannot divide it. If $Q_y\ne0$, at most six regular slopes pass, each with exactly one auxiliary source and a uniquely attached drift. There are at most four singular slopes. At a consistent singular slope with nonzero $q_t$, at most two values of $u$ pass, so this part contributes at most eight targets.

At a consistent singular slope with $q_t\equiv0$, an empty $I_t$ contributes none. If $u_0\in I_t$, strict positivity gives an open interval about $u_0$ contained in $I_t$. For an explicit neighborhood, put
$$
m=\min_{a,b}(X_t+u_0K_t)_{ab}>0,
\qquad L=1+\max_{a,b}|(K_t)_{ab}|.
$$
For $|u-u_0|<m/(2L)$, every entry remains greater than $m/2$. All such matrices have determinant zero. Since $K_t\ne0$, different $u$ give different sources. Equations (20.4) give a continuous attached whole drift at the same slope. Restricting to this interval yields a continuous injective arc of distinct actual targets with identical data. Therefore when $Q_y\ne0$, absence of such an arc leaves at most $6+4\cdot2=14$ targets.

Now suppose $Q_y\equiv0$. If a positive regular candidate exists at $t_0$, then $\Pi(t_0)\ne0$. Continuity gives an interval about $t_0$ on which $\Pi$ stays nonzero and all four entries of the rational matrix $\mathcal M_y(t)/\Pi(t)$ stay strictly positive. Its determinant is identically zero there, so every parameter value passes Theorem 20.1. The map
$$
t\longmapsto\bigl(S(t),t,D_t\bigr)
$$
is continuous; the slope coordinate makes it injective even if some sources coincide. It supplies a nontrivial continuous arc. If $Q_y\equiv0$ but there is no positive regular point, the regular branch contributes nothing. Only the singular branches remain. A singular zero polynomial with a positive point supplies the arc just proved; otherwise at most eight targets survive the nonzero singular polynomials. This includes the case where none survive. These cases exhaust all data and rule out an unclassified infinite discrete fibre. An arc contains infinitely many targets, so the finite and arc alternatives are exclusive. ∎

A complete fibre description and a finite multiplicity bound are not a globally recovering inverse or a uniqueness theorem. They do not establish that a history ever has two passing targets, or that some history always has at most one.

<a id="fixed-sign-prefix-zero-slope-uniqueness"></a>
## 21. Equal-slope uniqueness at zero

**Proposition 21.1 (limited fixed-slope uniqueness).** For every prefix in $\mathscr G$, every legal final word, and every proposed datum, there is at most one actual target in its fibre with $k=0$.

**Proof.** If $\mathsf B=\mathsf T_0$ is invertible, its quotient equation has at most one auxiliary solution. If it is singular, its first three rows have rank three and kernel $\mathbb RN$, so its full kernel is exactly $\mathbb RN$. Starting from an actual solution $S$, every other auxiliary solution is $S+tN$. Since $\det S=\det N=0$, (19.6) gives
$$
\det(S+tN)=t\mathfrak b(S,N).
$$
With the orientation of Lemma 19.2, the coefficient is strictly positive for this actual $S$. Hence determinant zero forces $t=0$. Once $S$ is fixed, the initial equation fixes the entire constant drift. If there is no actual solution there is no target to compare. This proves the at-most-one statement. ∎

This proposition is only at the common slope zero. It gives neither uniqueness between different slopes nor uniqueness at other singular pencil members. In particular it permits the distinct-slope collision below.

<a id="section17-finite-positive-gain-nonlocal-collision"></a>
## 22. A finite positive-gain collision for the exact Section 17 history

**Theorem 22.1 (nonlocal collision with slopes zero and one).** The exact history of Proposition 17.1, with final multiplier $W=MJM$ and final endpoint $A_4=(\begin{smallmatrix}2&3\\7&10\end{smallmatrix})$, has a finite collision of distinct strictly positive rank-one sources and distinct slopes $k_0=0$, $k_1=1$. Both lists of sampled gains are strictly positive. Each run has one entire constant drift, one fixed positive row, and positive columns throughout the same prescribed words.

**Proof of the exact history and its quotient.** The endpoints and successive chronological blocks are
$$
\begin{gathered}
A_0=I,\qquad
A_1=M^2=\begin{pmatrix}1&1\\1&2\end{pmatrix},\qquad
A_2=LM^2=\begin{pmatrix}1&1\\2&3\end{pmatrix},\\
A_3=ULM^2=\begin{pmatrix}3&4\\2&3\end{pmatrix},\qquad
W=MJM=L^2J=\begin{pmatrix}0&1\\1&2\end{pmatrix},\qquad
A_4=WA_3=\begin{pmatrix}2&3\\7&10\end{pmatrix},
\end{gathered}
\tag{22.1}
$$
$$
(M,M),\qquad(J,M),\qquad(M,J),\qquad(M,J,M).
$$
There are no reads inside those finite blocks. The readings are exactly $0,1,2,3,4$, and all blocks are fixed before either run.

The quotient matrix $\mathsf B$, in entry order $(p,q,r,s)$, has rows
$$
(0,1,1,1),\quad(0,2,1,2),\quad
(2,2,4,2),\quad(1,7,3,9).
\tag{22.2}
$$
The first three homogeneous equations give $q=-s$, $r=0$, $p=0$. Their kernel is therefore $\mathbb RN$ with
$$
N=\begin{pmatrix}0&-1\\0&1\end{pmatrix},\qquad
\mathfrak b(S,N)=p+r>0.
$$
The last row on $N$ is two, so $\mathsf B$ is invertible, and this is a member of $\mathscr G$.

The first four endpoint matrices are independent: the triples $(a-e,b,c)$ of $A_1,A_2,A_3$ are $(-1,1,1)$, $(-2,1,2)$, $(0,4,2)$, with determinant $6+4-8=2$. Projecting a relation among the first four matrices to those triples kills $I$ and hence all three other coefficients; the coefficient of $I$ then vanishes. The relation
$$
3I-4A_1-6A_2+A_3+2A_4=0
$$
has entry sums $3-4-6+3+4=0$, $-4-6+4+6=0$, $-4-12+2+14=0$, and $3-8-18+3+20=0$. It is the unique relation up to scale because the first four are independent. All five coefficients are nonzero, so deletion of any endpoint leaves four independent survivors. This collision is not a deletion-span failure.

**Proof of the finite transfer identity.** For an arbitrary full source matrix $S=(\begin{smallmatrix}p&q\\r&s\end{smallmatrix})$, define
$$
\mathsf H_0S=\begin{pmatrix}P&Q\\R&T\end{pmatrix},
$$
$$
\begin{aligned}
P&=\tfrac72p+4q+5r+\tfrac92s,\\
Q&=\tfrac94p-\tfrac32q+r-\tfrac{11}4s,\\
R&=-2q-2s,\\
T&=-\tfrac54p+\tfrac92q+\tfrac{27}4s.
\end{aligned}
\tag{22.3}
$$
Its useful combined entry is $Q+T=p+3q+r+4s$. The four traces are
$$
f_1=p+q+r+2s,\quad f_2=p+2q+r+3s,
\quad f_3=3p+2q+4r+3s,\quad f_4=2p+7q+3r+10s.
$$
The four rows of (22.2) applied to $\mathsf H_0S$ give
$$
\begin{aligned}
Q+R+T&=p+q+r+2s=f_1,\\
2Q+R+2T&=2p+4q+2r+6s=2f_2,\\
2P+2Q+4R+2T&=9p+6q+12r+9s=3f_3,\\
P+7Q+3R+9T&=8p+28q+12r+40s=4f_4.
\end{aligned}
\tag{22.4}
$$
Thus $\mathsf B\mathsf H_0=\mathsf C$ on every full matrix. Invertibility of $\mathsf B$ proves exactly $\mathsf H_0=\mathsf B^{-1}\mathsf C$, and consequently
$$
\mathsf B(S+\mathsf H_0S)=(\mathsf B+\mathsf C)S=\mathsf T_1S.
\tag{22.5}
$$
This is a finite transfer identity, with no infinitesimal approximation or small-parameter requirement.

**Proof of finite rank-one sources and strict positivity.** Let $v$ be the unique positive real root of
$$
2915v^2-1742v-2784=0.
\tag{22.6}
$$
Define
$$
S_1=\begin{pmatrix}1&1/10\\v&v/10\end{pmatrix},
\qquad
S_0=\begin{pmatrix}
49/10+(109/20)v&11/5+(29/40)v\\
(4v-1)/5&-4/5+(31/40)v
\end{pmatrix}.
\tag{22.7}
$$
Substituting $p=1$, $q=1/10$, $r=v$, $s=v/10$ into (22.3) gives
$$
\mathsf H_0S_1=
\begin{pmatrix}
39/10+(109/20)v&21/10+(29/40)v\\
-(v+1)/5&-4/5+(27/40)v
\end{pmatrix},
$$
so $S_0=S_1+\mathsf H_0S_1$ exactly. The determinant of $S_1$ is zero. Expanding that of $S_0$ gives
$$
\det S_0=-\frac{87}{25}-\frac{871}{400}v+\frac{583}{160}v^2
=\frac{2915v^2-1742v-2784}{800}.
\tag{22.8}
$$
For the coefficient check, the constant is $(49/10)(-4/5)-(11/5)(-1/5)=-87/25$. The linear coefficient is
$$
\frac{1519}{400}-\frac{109}{25}-\frac{44}{25}+\frac{29}{200}
=-\frac{871}{400},
$$
and the quadratic coefficient is $3379/800-29/50=583/160$.

At $v_*=32/31$, the lower-right entry of $S_0$ is zero, while its two upper entries are strictly positive and its lower-left entry is positive because $v_*>1/4$. Its determinant is therefore strictly negative there. The quadratic (22.8) has positive leading coefficient and tends to positive infinity as $v$ tends to positive infinity. Continuity supplies a finite root larger than $32/31$. The polynomial (22.6) has positive leading coefficient and negative constant, and its discriminant is $1742^2+4\cdot2915\cdot2784>0$. Its two real roots have negative product, so exactly one is positive. Hence the chosen root satisfies
$$
v>32/31>0.
\tag{22.9}
$$
This proves existence, uniqueness, finiteness, and the required strict bound for the exact root choice. Every entry of $S_1$ is positive. The two upper entries of $S_0$ are positive, its lower-left is positive by $v>1/4$, and its lower-right is positive by $v>32/31$. Equations (22.6)–(22.8) make both sources determinant zero, hence nonzero rank one. They are distinct since
$$
(S_0)_{21}-(S_1)_{21}=-(v+1)/5<0.
$$
No boundary source or limiting source is used.

**Proof of one whole drift and all five original readings.** Take
$$
k_0=0,\qquad k_1=1,\qquad
D_0(\tau)=0,\qquad D_1(\tau)=\Delta\quad(\tau\in\mathbb R),
$$
$$
\Delta=\operatorname{tr}(S_0-S_1)=\frac{31}{10}+\frac{49}{8}v.
\tag{22.10}
$$
Indeed the trace of $\mathsf H_0S_1$ is $39/10-4/5+(109/20+27/40)v=31/10+(49/8)v$. Equations (22.5) and (22.7) give $\mathsf T_0S_0=\mathsf T_1S_1$. Its four coordinates, together with the initial trace identity, are precisely the five original equalities
$$
\begin{aligned}
\operatorname{tr}S_0&=\operatorname{tr}S_1+\Delta,\\
\operatorname{tr}(A_1S_0)&=2\operatorname{tr}(A_1S_1)+\Delta,\\
\operatorname{tr}(A_2S_0)&=3\operatorname{tr}(A_2S_1)+\Delta,\\
\operatorname{tr}(A_3S_0)&=4\operatorname{tr}(A_3S_1)+\Delta,\\
\operatorname{tr}(A_4S_0)&=5\operatorname{tr}(A_4S_1)+\Delta.
\end{aligned}
\tag{22.11}
$$
Thus both runs have identical complete data with the displayed whole drifts. Their sampled gains are, respectively,
$$
(1,1,1,1,1),\qquad(1,2,3,4,5).
$$
Both are strictly positive. Their sources, slopes, and drifts differ, so the targets are not merely two representations of one effective target.

For explicit original common-source realizations one may take
$$
f_1=\binom1v,\qquad \ell_1=(1,1/10),
$$
$$
f_0=\binom{49/10+(109/20)v}{(4v-1)/5},\qquad
\ell_0=\left(1,\frac{11/5+(29/40)v}{49/10+(109/20)v}\right),
\qquad \alpha_j=1,\quad\beta_j=k_j,\quad R_j=S_j.
\tag{22.12}
$$
The determinant-zero identities give $f_j\ell_j=S_j$. Both factors are positive. Each row remains unchanged throughout its run. The $M,J$ positivity identities from Section 19 prove positive columns at every unread atom of the very same blocks in (22.1). Inverting $\mathsf B$ was only an algebraic proof device. No inverse operation, reset, copy, alternate history, additional read, or adaptive choice is acquired. ∎

<a id="one-sign-barrier-coexists-with-nonlocal-collision"></a>
**Compatibility with Proposition 17.1.** That proposition concerns the separate fixed slope $a=-1/4$ and $\mathsf H_a=\mathsf T_a^{-1}\mathsf C$. Its exact identity on positive rank-one $S$ is
$$
\mathfrak b(S,\mathsf H_aS)=-\frac23\left[
21p^2+5pq+44pr+49qs
+6\left(q-\frac{17r}{12}\right)^2
+\frac{167}{24}\left(r-\frac{384s}{167}\right)^2
+\frac{3375}{167}s^2\right]<0.
\tag{22.13}
$$
Its proof in Section 17 remains intact. Algebraically the square terms contribute $6q^2-17qr+(289/24)r^2$, $(167/24)r^2-32rs+(6144/167)s^2$, and $(3375/167)s^2$; the $r^2$ and $s^2$ coefficients become $19$ and $57$. Together with $ps=qr$ these give exactly the transfer polynomial (17.12), and $21p^2>0$ gives strict negativity. This says that opposite transfer signs at the single erased-final-gain slope are unavailable for this history. It places no prohibition on the finite transfer $\mathsf B^{-1}\mathsf C$ between slopes zero and one. Thus (22.13) and Theorem 22.1 coexist.

The conclusion of Theorem 22.1 is for exactly $A_4=(\begin{smallmatrix}2&3\\7&10\end{smallmatrix})$, $W=MJM$. It excludes this history as a globally recovering five-read history. It does not prove collision for every final word after the same prefix and does not address the different endpoint $(\begin{smallmatrix}5&7\\7&10\end{smallmatrix})$. The prior equation (17.12) alone still has its original method-only implication; the exclusion now follows from the separate finite witness (22.7)–(22.12).

<a id="global-fibres-attribution-and-current-residual"></a>
## 23. Attribution and the updated exact residual

The complete companion supplies the actual-source model, representation fibres, quotient interface, determinant polar, the three earlier certificate classes, the erased-final-gain coefficient mechanism, the four-parameter family, and the strict-one-sign diagnostic retained in Sections 1–18. All their original proofs and conditional scopes remain part of this text. The supplied *Global actual-source fibre decomposition and a finite nonlocal collision across the strict-one-sign barrier; the full quantified completion remains open* supplies the global pencil analysis and the finite distinct-slope witness developed in Sections 19–22. The unchanged original programme supplies the whole target, arbitrary real slopes, counted initial read, and predetermined cumulative finite-word contract.

| Supplied mathematical content | Results here | Exact scope |
|---|---|---|
| Fixed-polar-sign prefix trace invertibility, already in the companion | Lemma 19.2, with its full proof | Every prefix in $\mathscr G$; no coefficient-test hypothesis |
| Global pencil rank, adjugate and singular-line fibre analysis | Lemma 19.2, Theorem 20.1, Corollary 20.2 | Every prefix in $\mathscr G$, every legal final word including empty, every proposed five-read vector, all real slopes |
| Equal-slope zero uniqueness | Proposition 21.1 | A common slope of zero only, for every history just quantified |
| Finite nonlocal barrier collision | Theorem 22.1 | Exactly the Section 17 history with final multiplier $MJM$ and endpoint $(\begin{smallmatrix}2&3\\7&10\end{smallmatrix})$, slopes zero and one |
| Strictly negative erased-gain form | Proposition 17.1 and (22.13) | A boundary of the two-sign method at $-1/4$; compatible with Theorem 22.1 |

Every premise used for the appended results is proved in the complete text. Supplier attribution conveys no independent approval or formal certification. The supplier's abstention concerns the full quantified completion: the global fibre theorem and the isolated collision are substantive bounded results and do not constitute that completion. No nested source, supplier confidence, opaque log reference, or unprovided classification is a premise.

Theorem 20.1 replaces a local transfer test by an exhaustive actual-fibre description throughout $\mathscr G$, but it does not prove multiplicity or singleton fibres uniformly. To exclude every remaining history in this class, the still-missing statement is
$$
\begin{gathered}
\text{for every legal prefix in }\mathscr G
\text{ and every legal final word, there exist }y,S_0,S_1,k_0,k_1\\
S_j>0\text{ entrywise},\quad \det S_j=0,\quad
(S_0,k_0)\ne(S_1,k_1),\qquad
\mathsf T_{k_0}S_0=\mathsf T_{k_1}S_1=y.
\end{gathered}
\tag{23.1}
$$
Whole drifts would then be fixed by (19.5). In the exhaustive description, this requires some datum with two passing regular candidates, a regular and a singular candidate, two distinct retained points on singular branches, or a positive arc. No proof makes one of these occur for every remaining history. Theorem 15.1 still covers only its literal coefficient conditions, Theorem 16.1 still covers its declared family, and Theorem 22.1 additionally disposes of the exact Section 17 history. Other final words after that prefix and the remaining full class are unresolved unless an earlier theorem applies with its actual hypotheses. In particular the new current residual does not include the already excluded exact Section 17 history as a candidate for recovery.

Alternatively, constant-drift completion would require one legal predetermined five-read history with at most one actual target for every datum, a global inverse, and a necessary-and-sufficient actual-source image criterion for the whole target at all real slopes. The general fibre description supplies the image criterion for histories in $\mathscr G$, but supplies no such global uniqueness theorem. The exact Section 17 history cannot serve as that recovering history because of (22.11). Equal-slope uniqueness at zero, invertibility at $-1/4$, or a strictly signed transfer form at that single slope cannot replace the missing global uniqueness or multiplicity argument.

Other residual prefix geometries from Section 13 remain in the original unrestricted programme. The retained bounds, credited with complete support in Section 8, are still
$$
C_{\mathrm{fix}}(d)=d+5\quad(d\ge1),\qquad
5\le C_{\mathrm{fix}}(0)\le6.
\tag{23.2}
$$
Neither the upper bound of fourteen on finite fibre size nor the finite pair improves these read bounds or resolves the five-versus-six alternative. The bounded integration does not complete the original all-history or through-2027 research objective.

All appended conclusions concern the actual strictly positive rank-one common-source model, one fixed positive row per run, positive columns through all unread atoms, the exact indices $0,1,2,3,4$, predetermined cumulative finite left words, and one whole constant drift per run. No independently lifted source or representation-fibre ambiguity is substituted. The arguments are ordinary unexecuted symbolic textual mathematics. They assert no adaptive lower bound, unrestricted atom optimum, bit or precision bound, time bound, stability result, physical acquisition cost, empirical or general neural-network conclusion, Lean/kernel certification, missing-literature claim, or worldwide originality.
