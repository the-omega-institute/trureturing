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
