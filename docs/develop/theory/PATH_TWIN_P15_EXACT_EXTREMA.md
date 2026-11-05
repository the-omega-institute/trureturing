# Exact return infimum and twin transfer supremum for the path with 15 vertices

Haobo Ma and Wenlin Zhang

## Theorem 1 (Ma–Zhang)

Let $A$ be the adjacency matrix of the path on $1,\ldots,15$ with vertex $16$ joined to vertex $2$, and let $U(t)=e^{itA}$. Then
$$
 C(15):=\inf_{t>0}|U(t)_{1,1}|=\frac{143}{480},\qquad
 \sup_{t>0}|U(t)_{16,1}|^2=\frac{113569}{230400}.
$$
The infimum is attained in the closure of the positive-time phase orbit. No assertion of attainment at a finite time is needed.


## Proof: spectral formula and complete integer relations
Write $n=15$, $\alpha_k=(2k+1)\pi/(2n)$ for $0\leq k<n$, and
$$
 v_k=\bigl(\tfrac12,\cos\alpha_k,\cos(2\alpha_k),\ldots,
                    \cos((n-1)\alpha_k),\tfrac12\bigr)^T.
$$
The cosine recurrence and $\cos(n\alpha_k)=0$ show $Av_k=2\cos\alpha_k\,v_k$. Also $A(e_1-e_{16})=0$. For $1\leq j<n$, the finite cosine-sum identity gives
$$
\sum_{k=0}^{n-1}\cos(j\alpha_k)
=\frac{\sin(j\pi)}{2\sin(j\pi/(2n))}=0,
$$
where the denominator is nonzero. Thus
$$
 e_1=\tfrac12(e_1-e_{16})+\frac1n\sum_{k=0}^{n-1}v_k.
$$
Applying $e^{itA}$ and pairing the opposite nonzero eigenvalues gives
$$
 f(t):=U(t)_{1,1}=\frac8{15}+\frac1{15}\sum_{m\in M}\cos(t\lambda_m),
 \quad M=\{1,3,5,7,9,11,13\},\quad
 \lambda_m=2\cos\frac{m\pi}{30}.
\tag{1}
$$
In particular $f(t)\geq1/15>0$; its absolute value may be removed. This is the twin-path graph of Monterde's Example 18 [1].

In the order $M$, the full integer relation lattice is
$$
 \mathcal L=\{c\in\mathbb{Z}^7:c\cdot\lambda=0\}
 =\operatorname{span}_{\mathbb{Z}}\left\{
 \begin{pmatrix}1\\0\\0\\0\\-1\\-1\\0\end{pmatrix},
 \begin{pmatrix}0\\1\\0\\-1\\0\\0\\-1\end{pmatrix},
 \begin{pmatrix}0\\0\\1\\1\\-1\\-2\\-1\end{pmatrix}\right\}.
\tag{2}
$$
Here is an exact proof, including saturation over $\mathbb{Z}$. Let $z=e^{i\pi/30}$, so $z$ is a primitive $60$th root and
$$
 \Phi_{60}(X)=X^{16}+X^{14}-X^{10}-X^8-X^6+X^2+1.
$$
Reduction of $X^m+X^{60-m}$ modulo $\Phi_{60}$ verifies the three displayed relations. The four frequencies $\lambda_1,\lambda_3,\lambda_5,\lambda_7$ are independent over $\mathbb{Q}$: after multiplication by $z^7$, a nonzero relation would be a nonzero polynomial of degree at most $14$ vanishing at $z$, below $\deg\Phi_{60}=16$. Its exponents $7\pm m$ are distinct. Thus the rational relation space has dimension three. The rows in (2) have the identity matrix in the first three columns. Every rational relation is their unique rational combination; if its coordinates are integral, its first three coordinates force the combination coefficients to be integral. This proves the full lattice claim.

The continuous Kronecker theorem [2] describes the phase-orbit closure as
$$
 H=\{\theta\in(\mathbb{R}/2\pi\mathbb{Z})^7:c\cdot\theta=0\pmod{2\pi}\ (c\in\mathcal L)\}.
$$
This version concerns the real-time flow, so the annihilator is $c\cdot\lambda=0$, not a discrete-time congruence. Positive times have the same closure as all real times: for each $s>0$, compactness gives positive integers $n_j\to\infty$ with $n_js\lambda\to0$ in the torus, by the pigeonhole principle applied to the multiples of $s\lambda$. Hence $(n_j-1)s\lambda\to-s\lambda$ through nonnegative times; zero is also a limit of positive times. The positive-time closure therefore contains every real-time phase, and the reverse inclusion is immediate. By (2), every point of $H$ has the following parameterization by arbitrary real $a,b,c,d$:
$$
 (\theta_1,\theta_3,\theta_5,\theta_7,\theta_9,\theta_{11},\theta_{13})
 =(a+b,\ c+d,\ a+2b-c+d,\ c,\ a,\ b,\ d).
\tag{3}
$$
Therefore $15C(15)=8+\min_H S$, where $S=\sum_{m\in M}\cos\theta_m$.

## Proof: exact elimination of two phases
Put $w=c-d$ and $y=(c+d)/2$. Then
$$
 S=\cos b+2\cos y\cos(w/2)+\cos(2y)
       +\operatorname{Re}\{e^{ia}Z\},\qquad
 Z=1+e^{ib}+e^{i(2b-w)}.
$$
For each fixed $b,w$, the variables $y$ and $a$ are independent. Completing a square in $\cos y$ gives
$$
 \min_y\{2\cos y\cos(w/2)+\cos(2y)\}
       =-1-\tfrac12\cos^2(w/2),
 \quad \cos y=-\tfrac12\cos(w/2),
$$
and $\min_a\operatorname{Re}(e^{ia}Z)=-|Z|$. Thus both eliminated minima are attained.

Take $b=2t$, $x=\cos^2t$, $u=\cos w$, $v=\sin w$. The remaining minimum is exactly
$$
 \min_{0\leq x\leq1,\ u^2+v^2=1}F(x,u,v),\qquad
 F=2x-\frac94-\frac u4-r,
 \quad r=\sqrt{1+4x+B(x)u+D(x)v},
\tag{4}
$$
where
$$
 B(x)=4x(4x-3),\qquad D(x)=4\sqrt{x(1-x)}(4x-1),\qquad
 B^2+D^2=16x.
\tag{5}
$$
To justify equality of the domains, choose $t=\arccos\sqrt{x}\in[0,\pi/2]$. Direct expansion of $|Z|^2=1+4\cos^2t+4\cos t\cos(3t-w)$ gives (4). Other choices of $t$ with the same $x$ change at most the sign of the sine coefficient; $v\mapsto-v$ absorbs that sign. All circle points $(u,v)$ occur, and $a,y$ can always be chosen as above. In particular $0\leq r\leq3$.

## Proof: global stationary-point certificate
The compact domain in (4) has a minimum. We first include every boundary or nondifferentiable case. At $x=0$, $r=1$ and $F=-13/4-u/4\geq-7/2$. At $x=1$, $r=\sqrt{5+4u}$ and
$$
 F=-\tfrac14-\tfrac u4-\sqrt{5+4u}\geq-\tfrac72,
$$
since the expression decreases for $-1\leq u\leq1$. If $r=0$, then $F\geq-5/2$. Hence any smaller minimum has $0<x<1$ and $r>0$, where the function is smooth in $x$ and the circle angle $w$; the point $x=1/4$, at which $D=0$, is included in this smooth region.

At an interior stationary point, differentiating with respect to $w$ gives
$$
 (B+r/2)v=Du.
$$
Consequently a signed real $k$ satisfies
$$
 B+r/2=ku,\qquad D=kv.
\tag{6}
$$
The number $k$ cannot vanish. In the interior $D=0$ only at $x=1/4$, where $B=-2$ and $r^2=2-2u\leq4$; $B+r/2=0$ would instead force $r=4$. No sign assumption on $k$ is used.

The derivative with respect to $x$ is $4(r-1)=B'u+D'v$. Since $BB'+DD'=8$, equation (6) yields
$$
 4(r-1)k=8+\tfrac r2 B'=8+16rx-6r.
\tag{7}
$$
If $r=1$, this forces $x=-1/8$, impossible. Therefore set
$$
 K=\frac{8+16rx-6r}{4(r-1)}=k.
$$
The norm equation in (4) and the square of (6) now imply the polynomial equations
$$
\begin{aligned}
 E&=2(r-1)\{K(r^2-1-4x)-16x-rB/2\}=0,\\
 G&=4(r-1)^2\{K^2-16x-rB-r^2/4\}=0.
\end{aligned}
$$
Their expanded forms, making the certificate independently reproducible, are
$$
\begin{aligned}
 E={}&-16r(r+1)x^2+(8r^3+12r^2-40r+16)x\\
    &\hspace{23mm}-3r^3+4r^2+3r-4,\\
 G={}&-64r(r^2-3r+1)x^2+(48r^3-208r^2+240r-64)x\\
    &\hspace{23mm}-r^4+2r^3+8r^2-24r+16.
\end{aligned}
$$
For quadratics $E=ax^2+bx+c$, $G=dx^2+ex+f$, the elementary resultant formula is $(af-cd)^2-(ae-bd)(bf-ce)$. Substitution and factorization give
$$
 \operatorname{Res}_x(E,G)
 =256r^4(r-4)^2(r-2)(r-1)^2
          (r^2+2r-4)(16r^2-63r+56).
\tag{8}
$$
Every stationary point must annul this polynomial; allowing extra roots from elimination can only enlarge the candidate set. Since $0<r\leq3$ and $r\ne1$, the only candidates come from the following three rows. The accompanying linear equations are forced by $E=G=0$ and the factor in that row:
$$
\begin{array}{c|c|c}
 \text{factor} & \text{forced equation} & \text{consequence}\\ \hline
 r-2 &4x-1=0 & K=1,\ u=-1,\ F=-7/2\\
 r^2+2r-4 &r+4x-1=0 & r>0\Rightarrow x<0\\
 16r^2-63r+56 &-4r+8x+5=0 & K=2(r-1),\ u=1/8,\ F=-113/32
\end{array}
$$
These forced equations can be checked by polynomial division or by the three exact Gröbner bases (variable order $x,r$)
$$
\begin{aligned}
 \langle E,G,r-2\rangle&=\langle4x-1,r-2\rangle,\\
 \langle E,G,r^2+2r-4\rangle&=\langle r+4x-1,r^2+2r-4\rangle,\\
 \langle E,G,16r^2-63r+56\rangle&=\langle-4r+8x+5,16r^2-63r+56\rangle.
\end{aligned}
$$
The brackets denote ideals over $\mathbb{Q}[x,r]$; scalar normalizations of their generators do not matter.

All root selections are exact. The two roots of $r^2+2r-4$ lie respectively in $(-4,-3)$ and $(1,5/4)$, so neither gives admissible $r,x$. The two roots of $16r^2-63r+56$ lie in $(1355/1000,1356/1000)$ and $(2581/1000,2582/1000)$, respectively. Sturm's theorem gives exactly one root in each interval and no other real roots. Both branches give the same objective value. Comparing the rational values $-113/32<-7/2<-5/2$ proves the global lower bound $F\geq-113/32$ once attainment is supplied.

## Proof: an exact attaining phase point
Define
$$
 x_* =\frac{23-\sqrt{385}}{64},\qquad
 r_* =2x_*+\frac54=\frac{63-\sqrt{385}}{32},\qquad
 k_*=2(r_*-1),\qquad
 u_* =\frac18,\quad v_*=-\frac{3\sqrt7}{8}.
$$
The root $x_*$ of $q(x)=256x^2-184x+9$ is isolated in $(52/1000,53/1000)$. In particular $0<x_*<1/4$, $k_*>0$, and $D(x_*)<0$. For general $x$, writing $r=2x+5/4$ and $k=2(r-1)$ gives the exact identities
$$
\begin{aligned}
 B+r/2-k/8&=q(x)/16,\\
 D^2-63k^2/64&=-(256x^2-200x+7)q(x)/256,\\
 r^2-(1+4x+k-r/16)&=q(x)/64.
\end{aligned}
$$
At $x_*$ the first two identities and the signs give $B+r_*/2=k_*/8$ and $D=k_*v_*$. Thus
$$
 1+4x_*+B(x_*)u_*+D(x_*)v_*
   =1+4x_*+k_*-r_*/16=r_*^2.
$$
Set, explicitly,
$$
\begin{aligned}
 b&=2\arccos\sqrt{x_*},& w&=-\arccos(1/8),\\
 Z&=1+e^{ib}+e^{i(2b-w)},& a&=\pi-\arg Z,\\
 y&=\arccos\bigl(-\tfrac12\cos(w/2)\bigr),&
 c&=y+w/2,\qquad d=y-w/2.
\end{aligned}
$$
These are well defined: $|Z|=r_*>0$ and the argument of the last arccosine lies in $[-1/2,1/2]$. Use these $a,b,c,d$ in (3). They obey every integer relation; hence this is a phase point in the positive-time orbit closure $H$. The choices of $a$ and $y$ attain the two eliminated minima, and
$$
 S=F=2x_*-\frac94-\frac1{32}-r_*=-\frac{113}{32}.
$$
The spectral formula (1) proves $C(15)=(8-113/32)/15=143/480$.

## Proof: transfer probability
The antisymmetric vector $e_1-e_{16}$ has eigenvalue zero, so $U(t)_{16,1}=f(t)-1$. The convex cosine formula gives $C(15)\leq f(t)\leq1$. Taking the supremum, using the orbit-closure minimizer above, proves
$$
 \sup_{t>0}|U(t)_{16,1}|^2
   =(1-C(15))^2=(337/480)^2=113569/230400.
$$
This is a supremal transfer probability below one.


## References

[1] H. Monterde, *New results in vertex sedentariness*, arXiv:2401.00362v1 (31 December 2023), Definition 1 and Example 18. <https://arxiv.org/abs/2401.00362v1>. Published in *Discrete Mathematics* 349(4) (2026), 114959, DOI: [10.1016/j.disc.2025.114959](https://doi.org/10.1016/j.disc.2025.114959). The graph, adjacency convention, lower bound $1/n$ and sharp $n=5$ case are from Example 18; Theorem 1 gives the exact $n=15$ extrema.

[2] A. L. Onishchik, “Kronecker theorem”, *Encyclopedia of Mathematics*, revision 47528 (5 June 2020), simultaneous approximation criterion and torus subgroup closure formulation. <https://encyclopediaofmath.org/index.php?title=Kronecker_theorem&oldid=47528>. See also the repository's [source note](../../../Library/Fourier/onishchik2020kronecker.md). For the real-time flow the integer characters that vanish are precisely those with $c\cdot\lambda=0$; requiring $tc\cdot\lambda\in2\pi\mathbb Z$ for every real $t$ is equivalent to this equality.
