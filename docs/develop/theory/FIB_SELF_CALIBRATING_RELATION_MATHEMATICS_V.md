# FIB 自校准关系数学 V

## 1. 完整目标、共同第五纤维与原时钟

**定义 1.1（采集域与历史）。** Let $\mathcal W_3$ consist of the triples $W=(P,g,\delta)$ such that $P$ is a strictly entrywise positive real $2\times2$ matrix, $\det P=0$, $\operatorname{tr}P=1$, $0\ne g\in\mathbb R[t]$, $\deg g\le3$, and $\delta\in\mathbb R$. Set

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
A_0=I,\quad A_i=E_iA_{i-1},\quad E_i\in\{M,J\}.
$$

The reading at original clock $i$ is $g(i)\operatorname{tr}(A_iP)+\delta$. The initial reading counts, and every single atom is followed immediately by its reading. Eight readings therefore use clocks $0,\ldots,7$ on one trajectory. Resetting, copying, skipping readings, unread compound actions, empty-action readings, renumbering clocks and additional observation ports are excluded. Actions, stopping and the returned complete target $(P,g,\delta)$ may depend arbitrarily and deterministically on the actual history. All gain signs, lower degrees, sampled roots, repeated roots and real constant drifts are allowed.

For a literal history $H$, write $\mathcal F(H)$ for all its compatible complete targets. Use the failure recursion of [II, Definition 56.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md):

$$
\begin{aligned}
L_0(K,H)&\Longleftrightarrow |K|\ge2,\\
L_s(K,H)&\Longleftrightarrow |K|\ge2\ \land\
\bigwedge_{E\in\{M,J\}}\exists z\in\mathbb R:
L_{s-1}(K\cap\mathcal F(H,E,z),(H,E,z)).
\end{aligned}                                                    \tag{1.1}
$$

This recursion includes every early stop. Its negation gives recovery of the whole known candidate set within the stated remaining horizon. Counterfactual responses are functions of fixed targets used to define a strategy or prove a collision; they are not acquired readings.

An unnormalized positive rank-one $R$ and nonzero polynomial $H$ represent exactly

$$
\left(\frac R{\operatorname{tr}R},\ (\operatorname{tr}R)H,\ \delta\right),
\qquad z_i=H(i)\operatorname{tr}(A_iR)+\delta.                      \tag{1.2}
$$

The normalizing factor is positive, so signs, roots and degrees are preserved.

**定义 1.2（指定 MMJM 纤维）。** Fix one real $Y$ and the entire history

$$
H_4(Y)=(0,M,1,M,23/7,J,331/35,M,Y),\qquad
D=MJM^2=\begin{pmatrix}1&1\\2&3\end{pmatrix}.
$$

The joint fiber $\mathcal F(Y;m,j)$ consists of the targets in $\mathcal F(H_4(Y))$ whose fifth-$M$ and fifth-$J$ predictions are respectively $m,j$. The non-diagonal hypothesis is $k=m-j\ne0$. Membership in this joint fiber is a promise on the same fixed targets.

The chart of [II, Definitions 69.1–69.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md) is

$$
\begin{gathered}
\eta=(DP)_{22}>0,\quad R=P/\eta,\quad H=\eta g,\\
DR=\begin{pmatrix}xy&x\\y&1\end{pmatrix},\qquad
R=\begin{pmatrix}(3x-1)y&3x-1\\(1-2x)y&1-2x\end{pmatrix},
\qquad \frac13<x<\frac12,\quad y>0.
\end{gathered}                                                     \tag{1.3}
$$

These inequalities are equivalent to strict positivity of the displayed rank-one $R$. Put $p=xy,s=x+y$. The five trace factors along the parent are

$$
(T_0,T_1,T_2,T_3,T_4)
=(3p+1-2x-y,\ s-2p,\ p+1-x,\ s-p,\ p+1),                        \tag{1.4}
$$

all strictly positive. The joint fifth conditions are exactly

$$
H(5)=k,\qquad \delta=j-ks.                                      \tag{1.5}
$$

Thus $(x,y)$ determines the complete target within this joint fiber: it determines $R,\delta$, and the parent readings at $0,1,2,3$ determine $H$ by cubic interpolation using the positive $T_i$. The clock-four equation is still required.

Write $w=H(6)/k$, $r=H(7)/k$. After subtracting $j$ and dividing by $k$, the four sixth responses and their two final responses, in final-$M$, final-$J$ order, are

| Chronological fifth/sixth node | Sixth response | Final response pair |
| --- | --- | --- |
| $a=JJ$ | $w(p+1)-s$ | $(r(s+1)-s,rs-s)$ |
| $b=JM$ | $w(p+x+1)-s$ | $(r(p+2x+y+1)-s,r(p+s)-s)$ |
| $c=MJ$ | $w(p+y+1)-s$ | $(r(s+2)-s,r(s+1)-s)$ |
| $d=MM$ | $w(p+s+2)-s$ | $(r(p+2s+3)-s,r(p+x+2y+1)-s)$ |

Equality of these normalized responses is equivalent to actual equality for either sign of $k$. A bad pair at a sixth node means equality of its sixth reading and of both possible final readings for that same pair.

## 2. 稀疏三目标与共同祖先的不相容性

**定理 2.1（共同第五条件下的稀疏祖先排除）。** There are no three legal fixed targets in the chart (1.3) with common fifth predictions $m,j$, $k\ne0$, satisfying all the following conditions:

$$
\begin{gathered}
r_1=r_2=1,\qquad r_3\ne1,\qquad a_1=a_2,\quad c_1=c_2,\\
\{1,3\}\text{ is bad at }d,\qquad
\{2,3\}\text{ is bad at }b,                                  \tag{2.1}\\
z_1(W_1)=z_1(W_2),\quad z_3(W_1)=z_3(W_2),\quad
z_4(W_1)=z_4(W_2)
\quad\text{along the original word }MMJM.
\end{gathered}
$$

The three common ancestor values in the last line need not be $1,331/35,Y$. The sixth sample of target $3$ is unrestricted, including zero.

Proof. Put $x=x_3,y=y_3,e=r_3-1$. Differences of the final responses at $d$ and $b$ give

$$
x_1+2=(1+e)(x+2),\qquad x_2+1=(1+e)(x+1).
$$

Their final-$J$ equalities then give

$$
\begin{aligned}
x_1&=x+e(x+2),& y_1&=y+\frac{e(x+1)}{x_1+1},\\
x_2&=x+e(x+1),& y_2&=y+\frac{ex}{x_2}.                         \tag{2.2}
\end{aligned}
$$

The first difference also implies $14/15<1+e<15/14$. Consequently

$$
-1/15<e<1/14,\qquad e\ne0.
$$

Define the following polynomials in $x,e,y$:

$$
\begin{gathered}
B=x+e(x+1)=x_2,\quad C=x+1+e(x+2)=x_1+1,\quad G=BC,\quad U=G+e,\\
L_1=Cy+e(x+1)=Cy_1,\quad L_2=By+ex=By_2,\quad L=L_1L_2,\quad Z=L-e,\\
A_1=(x+2)C+x+1,\quad A_2=(x+1)B+x,\\
Q_1=L_1+C+1,\quad R_2=L_2+B+1,\\
Q_3=(x+1)y+x+2,\quad R_3=xy+x+1.                              \tag{2.3}
\end{gathered}
$$

Source legality gives $B>1/3,C>4/3,L_1,L_2>0$, $G>4/9$ and $U>17/45$. Exact subtraction in (2.2) gives

$$
y_1-y_2=\frac{e^2}{G},\qquad s_1-s_2=\frac{eU}{G}.             \tag{2.4}
$$

Common $a,c$ imply $w_1y_1=w_2y_2=n$ and

$$
n\left(e-\frac{e^2}{L}\right)=\frac{eU}{G}.
$$

The stratum $Z=0$ would give $0=eU/G$, which is impossible. On every remaining stratum,

$$
n=\frac{UL}{GZ},\qquad
w_1=\frac{UL_2}{BZ},\qquad w_2=\frac{UL_1}{CZ}.                \tag{2.5}
$$

This establishes nonvanishing of $w_1,w_2$ without assuming their signs. The selected sixth collisions are

$$
w_1Q_1-w_3Q_3=eA_1/C,\qquad
w_2R_2-w_3R_3=eA_2/B.
$$

Eliminating $w_3$ and multiplying by the already nonzero $GZ$ gives $E=0$, where

$$
E=U(CL_2Q_1R_3-BL_1R_2Q_3)
-eZ(BA_1R_3-CA_2Q_3).                                        \tag{2.6}
$$

For the sign analysis set

$$
\begin{gathered}
\rho=1+e,\quad v=x(x+1),\quad W=\rho v-e,\\
V=1+2\rho(x+1),\qquad N=1+\rho(x+1)(x+2),\\
F=(L+G)(Wy-eV)-e\rho vZ.
\end{gathered}
$$

Expansion of the factors in (2.3) yields the two polynomial identities

$$
E=eF,\qquad
F=Z(Wy-eN)+U(Wy-eV).                                         \tag{2.7}
$$

These identities use no ancestor values. Since $e\ne0$, (2.6) requires $F=0$.

If $e<0$, then $Z=L-e>0$, $W=\rho v-e>0$, and $N,V>0$, since $\rho>14/15$. Both summands in the second identity (2.7) are strictly positive. Thus $F>0$, a contradiction.

Suppose $e>0$. On the containing rectangle $1/3\le x\le1/2$, $0\le e\le1/14$,

$$
W=v-e(1-v)\ge\frac49-\frac5{126}=\frac{17}{42}>0.
$$

The first formula for $F$ and $F=0$ give

$$
Wy=e\left(V+\rho v\frac{Z}{L+G}\right)<e(V+\rho v)=eN,         \tag{2.8}
$$

because $L+G>0$, $Z<L+G$ and $\rho v>0$. This inequality holds for both signs of the nonzero $Z$.

For completeness the bound for $N/W$ is uniform. The identity $N=W+\rho(2x+3)$ gives

$$
\frac{\partial}{\partial x}\frac NW
=-\frac{\rho[\rho(2x^2+6x+3)+2e]}{W^2}<0.
$$

For fixed $x$ in this rectangle, $N$ increases with $e$ and $W$ decreases with $e$, while both remain positive. Hence (2.8) implies

$$
0<\frac ye<\frac NW\le
\frac{N(1/3,1/14)}{W(1/3,1/14)}
=\frac{182}{17}<11.                                          \tag{2.9}
$$

It remains to use the actual ancestor collisions. For $i=1,2$, put $K_i=H_i/k$. Every polynomial of degree at most three with $K_i(5)=K_i(7)=1$, $K_i(6)=w_i$ is exactly

$$
K_i(t)=1+(1-w_i)q(t)+\alpha_i c(t),\quad
q(t)=(t-5)(t-7),\quad c(t)=(t-5)(t-6)(t-7),                  \tag{2.10}
$$

with $\alpha_i\in\mathbb R$. Indeed the first two terms have the three prescribed samples, and their difference from $K_i$ is divisible by $c$. This includes every possible degree drop.

At original clocks $t=1,3,4$, the numerators $n_{1t}=CT_{1t}$, $n_{2t}=BT_{2t}$ of the source traces are

$$
\begin{array}{c|cc}
t&n_{1t}&n_{2t}\\ \hline
1&C(C-1)+(3-2C)L_1&B^2+(1-2B)L_2\\
3&C(C-1)+(2-C)L_1&B^2+(1-B)L_2\\
4&(C-1)L_1+C&BL_2+B.
\end{array}                                                     \tag{2.11}
$$

Let $(q_1,q_3,q_4)=(24,8,3)$ and $(c_1,c_3,c_4)=(-120,-24,-6)$. Define

$$
\begin{aligned}
V_t={}&(1+q_t)Z(Bn_{1t}-Cn_{2t})
-q_tU(L_2n_{1t}-L_1n_{2t})-eUZ,\\
\Delta(x,e,y)={}&
\det\begin{pmatrix}
c_1n_{11}&c_1n_{21}&V_1\\
c_3n_{13}&c_3n_{23}&V_3\\
c_4n_{14}&c_4n_{24}&V_4
\end{pmatrix}.                                                \tag{2.12}
\end{aligned}
$$

The common ancestor reading at $t$ is equivalent to

$$
K_1(t)T_{1t}-K_2(t)T_{2t}=s_1-s_2=eU/G.
$$

Substituting (2.5), (2.10), and multiplying by $GZ$, gives

$$
V_t+c_tZ(Bn_{1t}\alpha_1-Cn_{2t}\alpha_2)=0.                  \tag{2.13}
$$

Thus the third column of (2.12) is a fixed linear combination of the first two, so $\Delta=0$. No minor or interpolation coefficient has been divided out.

The exact coefficient certificate in Definition 3.1 gives

$$
\Delta(x,e,ez)=144e^3\Phi(x,e,z),\qquad
\Phi(x,e,z)>0
\quad\left(\frac13\le x\le\frac12,\ 0\le e\le\frac1{14},\ 0\le z\le11\right).
                                                                  \tag{2.14}
$$

By (2.9), $z=y/e$ is in this box. Hence $\Delta(x,e,y)>0$, contradicting (2.13). The two signs of $e$ and the separately excluded $Z=0$ stratum exhaust the possibilities. All divisions have used positive source coordinates, $k\ne0$, $e\ne0$ or the proved $Z\ne0$; no division by $w_3$, an ancestor gain, a leading gain coefficient, or a minor occurs. ∎

## 3. 祖先行列式的完整有限正系数证书

**定义 3.1（四盒 Bernstein 证书）。** Use exactly the integer polynomial factors (2.3), (2.11), (2.12). Expansion gives a polynomial $\Phi$ characterized by

$$
\Delta(x,e,ez)=144e^3\Phi(x,e,z),\qquad
\deg_{x,e,z}\Phi\le(6,10,5).                                  \tag{3.1}
$$

The identity specifies its polynomial extension at $e=0$; it is an exact polynomial division. Its expanded polynomial has $281$ nonzero monomials.

For $\ell=1,2,3,4$, use the following endpoints:

| $\ell$ | $e_\ell^-$ | $e_\ell^+$ | $z_\ell^-$ | $z_\ell^+$ |
| --- | --- | --- | --- | --- |
| 1 | $0$ | $1/28$ | $0$ | $11/2$ |
| 2 | $0$ | $1/28$ | $11/2$ | $11$ |
| 3 | $1/28$ | $1/14$ | $0$ | $11/2$ |
| 4 | $1/28$ | $1/14$ | $11/2$ | $11$ |

Define every rational coefficient by finite coefficient extraction and finite sums:

$$
\begin{aligned}
q^\ell_{abc}
&=[X^aE^bZ_0^c]\,
\Phi\left(\frac13+\frac X6,
e_\ell^-+(e_\ell^+-e_\ell^-)E,
z_\ell^-+(z_\ell^+-z_\ell^-)Z_0\right),\\
\beta^\ell_{ijk}
&=\sum_{a=0}^i\sum_{b=0}^j\sum_{c=0}^k
q^\ell_{abc}
\frac{\binom ia}{\binom6a}
\frac{\binom jb}{\binom{10}b}
\frac{\binom kc}{\binom5c},
\quad 0\le i\le6,\quad0\le j\le10,\quad0\le k\le5.             \tag{3.2}
\end{aligned}
$$

Here coefficient extraction has its usual polynomial meaning; missing monomials have coefficient zero. Thus no auxiliary coefficient file is part of the definition. For an explicit multiplication rule, $[x^ae^by^c](PQ)$ is the sum of $[x^{a'}e^{b'}y^{c'}]P\,[x^{a-a'}e^{b-b'}y^{c-c'}]Q$ over $0\le(a',b',c')\le(a,b,c)$. Together with the displayed determinant this reduces (3.1)–(3.2) to rational additions and multiplications.

The following matrices give all $1848$ integer lower bounds

$$
n^\ell_{ijk}=\lfloor2\beta^\ell_{ijk}\rfloor>0.                 \tag{3.3}
$$

Each matrix is indexed by increasing row $i=0,\ldots,6$ and column $j=0,\ldots,10$; the indicated $k$ is fixed. Formula (3.2) and these complete matrices give the exact comparisons $2\beta^\ell_{ijk}\ge n^\ell_{ijk}\ge1$.

$$
\left(n^{1}_{ij0}\right)_{i,j}=\begin{pmatrix}
7&7&7&7&7&8&8&8&8&8&8\\
8&8&9&9&9&9&9&10&10&10&10\\
10&10&10&11&11&11&11&12&12&12&12\\
12&13&13&13&13&14&14&14&14&14&15\\
15&15&16&16&16&16&17&17&17&17&17\\
18&18&19&19&19&20&20&20&20&21&21\\
22&22&23&23&23&24&24&24&24&25&25
\end{pmatrix}.
$$

$$
\left(n^{1}_{ij1}\right)_{i,j}=\begin{pmatrix}
10&10&10&10&11&11&11&11&12&12&12\\
12&12&13&13&13&14&14&14&14&15&15\\
15&16&16&16&17&17&17&18&18&18&18\\
19&20&20&20&21&21&21&22&22&22&22\\
24&24&25&25&26&26&26&27&27&27&28\\
30&30&31&31&32&32&32&33&33&33&34\\
37&37&38&38&39&39&40&40&41&41&41
\end{pmatrix}.
$$

$$
\left(n^{1}_{ij2}\right)_{i,j}=\begin{pmatrix}
13&13&13&13&13&14&14&14&14&14&13\\
16&16&17&17&17&17&17&17&17&17&17\\
21&21&21&21&21&21&21&21&21&21&21\\
26&26&27&27&27&27&27&27&27&26&26\\
33&33&33&33&33&33&33&33&33&33&32\\
41&42&42&42&42&42&41&41&41&40&40\\
52&52&52&52&52&52&51&51&50&50&49
\end{pmatrix}.
$$

$$
\left(n^{1}_{ij3}\right)_{i,j}=\begin{pmatrix}
16&16&16&16&16&15&15&15&14&14&13\\
20&20&20&20&20&20&19&19&18&18&17\\
26&26&26&25&25&25&24&24&23&22&21\\
33&33&33&32&32&31&30&29&29&27&26\\
42&41&41&41&40&39&38&37&36&34&33\\
53&52&52&51&50&49&47&46&44&43&41\\
67&66&65&64&62&61&59&57&55&53&50
\end{pmatrix}.
$$

$$
\left(n^{1}_{ij4}\right)_{i,j}=\begin{pmatrix}
19&19&18&18&17&17&16&15&14&13&12\\
24&24&23&23&22&21&20&19&18&17&16\\
31&31&30&29&28&27&26&24&23&21&20\\
40&39&38&37&35&34&32&31&29&27&25\\
51&50&48&47&45&43&41&38&36&33&31\\
64&63&61&59&56&54&51&48&45&42&39\\
81&79&77&74&71&67&64&60&56&52&48
\end{pmatrix}.
$$

$$
\left(n^{1}_{ij5}\right)_{i,j}=\begin{pmatrix}
22&21&21&20&19&17&16&15&14&12&11\\
28&27&26&25&24&22&21&19&17&16&14\\
37&35&34&32&30&28&26&24&22&20&18\\
47&45&43&41&38&36&33&30&28&25&22\\
60&57&55&52&48&45&42&38&35&31&28\\
76&73&69&65&61&57&52&48&44&39&35\\
96&92&87&82&77&71&66&60&54&49&44
\end{pmatrix}.
$$

$$
\left(n^{2}_{ij0}\right)_{i,j}=\begin{pmatrix}
22&21&21&20&19&17&16&15&14&12&11\\
28&27&26&25&24&22&21&19&17&16&14\\
37&35&34&32&30&28&26&24&22&20&18\\
47&45&43&41&38&36&33&30&28&25&22\\
60&57&55&52&48&45&42&38&35&31&28\\
76&73&69&65&61&57&52&48&44&39&35\\
96&92&87&82&77&71&66&60&54&49&44
\end{pmatrix}.
$$

$$
\left(n^{2}_{ij1}\right)_{i,j}=\begin{pmatrix}
25&24&23&21&20&18&16&15&13&11&10\\
32&31&29&27&25&23&21&19&17&14&12\\
42&40&37&35&32&30&27&24&21&18&16\\
54&51&48&45&41&37&34&30&27&23&20\\
69&65&61&57&52&47&43&38&33&29&25\\
87&83&77&72&66&60&54&48&42&37&32\\
111&105&98&90&83&75&68&60&53&46&40
\end{pmatrix}.
$$

$$
\left(n^{2}_{ij2}\right)_{i,j}=\begin{pmatrix}
28&27&25&23&21&18&16&14&12&10&8\\
36&34&32&29&26&24&21&18&15&12&10\\
47&44&41&37&34&30&26&23&19&16&13\\
61&57&52&48&43&38&33&29&24&20&17\\
78&72&67&61&54&48&42&36&31&26&21\\
99&92&85&77&69&61&53&46&39&32&27\\
126&117&107&97&87&77&67&57&49&41&34
\end{pmatrix}.
$$

$$
\left(n^{2}_{ij3}\right)_{i,j}=\begin{pmatrix}
31&29&26&24&21&18&15&13&10&8&6\\
41&37&34&31&27&23&20&16&13&10&8\\
52&48&44&39&34&30&25&21&17&13&11\\
67&62&56&50&44&38&32&26&21&17&14\\
87&79&72&64&56&48&40&33&27&22&18\\
111&101&91&81&70&60&51&42&34&28&23\\
141&128&115&102&89&76&64&53&43&35&29
\end{pmatrix}.
$$

$$
\left(n^{2}_{ij4}\right)_{i,j}=\begin{pmatrix}
34&31&28&25&21&18&14&11&9&7&5\\
45&41&36&32&27&22&18&14&11&9&7\\
58&52&46&40&34&29&23&18&14&11&9\\
74&67&59&52&44&37&30&24&19&15&12\\
95&86&76&66&56&46&38&30&24&19&16\\
122&110&97&84&71&59&48&38&30&24&21\\
156&139&123&106&89&74&60&48&38&31&27
\end{pmatrix}.
$$

$$
\left(n^{2}_{ij5}\right)_{i,j}=\begin{pmatrix}
37&33&29&25&21&17&13&10&7&6&5\\
49&43&38&32&27&21&17&13&10&8&7\\
63&56&49&41&34&27&21&16&13&10&9\\
81&72&62&53&43&35&27&21&16&13&12\\
104&92&80&67&55&44&35&27&21&17&16\\
134&118&101&85&70&56&44&34&27&22&21\\
171&150&129&108&89&71&55&43&34&29&27
\end{pmatrix}.
$$

$$
\left(n^{3}_{ij0}\right)_{i,j}=\begin{pmatrix}
8&9&9&9&9&9&9&9&9&10&10\\
10&10&10&11&11&11&11&11&11&11&11\\
12&12&13&13&13&13&13&13&13&13&13\\
15&15&15&15&15&15&16&16&16&16&16\\
17&18&18&18&18&18&18&18&19&19&19\\
21&21&21&21&22&22&22&22&22&22&22\\
25&25&25&25&25&26&26&26&26&26&26
\end{pmatrix}.
$$

$$
\left(n^{3}_{ij1}\right)_{i,j}=\begin{pmatrix}
12&12&12&12&13&13&13&13&13&13&13\\
15&15&15&15&16&16&16&16&16&16&16\\
18&18&19&19&19&19&19&19&19&19&19\\
22&23&23&23&23&23&23&24&24&24&24\\
28&28&28&28&28&29&29&29&29&29&29\\
34&34&34&34&35&35&35&35&35&35&35\\
41&42&42&42&42&42&42&43&43&43&42
\end{pmatrix}.
$$

$$
\left(n^{3}_{ij2}\right)_{i,j}=\begin{pmatrix}
13&13&13&13&13&12&12&12&11&11&10\\
17&17&16&16&16&15&15&15&14&13&13\\
21&21&20&20&20&19&19&18&17&16&15\\
26&26&25&25&24&24&23&22&21&20&19\\
32&32&31&31&30&29&28&27&26&25&23\\
40&39&38&38&37&36&35&33&32&30&29\\
49&48&47&46&45&44&42&41&39&37&35
\end{pmatrix}.
$$

$$
\left(n^{3}_{ij3}\right)_{i,j}=\begin{pmatrix}
13&13&12&12&11&10&9&8&7&6&5\\
17&16&15&14&13&12&11&10&9&7&6\\
21&20&19&18&17&15&14&12&11&9&8\\
26&25&24&22&21&19&17&16&14&12&10\\
33&31&30&28&26&24&22&19&17&15&12\\
41&39&37&34&32&29&27&24&21&18&15\\
50&48&45&43&40&36&33&30&26&23&19
\end{pmatrix}.
$$

$$
\left(n^{3}_{ij4}\right)_{i,j}=\begin{pmatrix}
12&11&10&9&8&7&6&5&4&3&2\\
16&14&13&12&10&9&7&6&5&3&2\\
20&18&16&15&13&11&9&8&6&5&3\\
25&23&21&18&16&14&12&10&8&6&5\\
31&28&26&23&20&18&15&13&10&8&7\\
39&35&32&29&25&22&19&16&13&11&9\\
48&44&40&36&32&28&24&20&17&14&12
\end{pmatrix}.
$$

$$
\left(n^{3}_{ij5}\right)_{i,j}=\begin{pmatrix}
11&10&8&7&6&5&4&3&2&2&2\\
14&12&11&9&8&6&5&4&4&3&3\\
18&16&14&12&10&8&7&6&5&5&4\\
22&20&17&15&12&11&9&8&7&6&6\\
28&25&22&19&16&14&12&10&9&9&9\\
35&31&27&24&20&17&15&13&12&12&12\\
44&39&34&30&26&22&19&17&16&16&16
\end{pmatrix}.
$$

$$
\left(n^{4}_{ij0}\right)_{i,j}=\begin{pmatrix}
11&10&8&7&6&5&4&3&2&2&2\\
14&12&11&9&8&6&5&4&4&3&3\\
18&16&14&12&10&8&7&6&5&5&4\\
22&20&17&15&12&11&9&8&7&6&6\\
28&25&22&19&16&14&12&10&9&9&9\\
35&31&27&24&20&17&15&13&12&12&12\\
44&39&34&30&26&22&19&17&16&16&16
\end{pmatrix}.
$$

$$
\left(n^{4}_{ij1}\right)_{i,j}=\begin{pmatrix}
10&8&6&5&4&3&2&1&1&2&2\\
12&10&8&7&5&4&3&2&2&3&4\\
16&13&11&9&7&5&4&4&4&4&6\\
20&17&14&11&9&7&6&5&5&6&8\\
25&21&18&14&12&9&8&8&8&9&11\\
32&27&22&18&15&13&11&10&11&12&15\\
40&34&28&23&19&17&15&14&15&17&20
\end{pmatrix}.
$$

$$
\left(n^{4}_{ij2}\right)_{i,j}=\begin{pmatrix}
8&6&4&3&2&1&1&2&3&4&6\\
10&8&6&4&3&2&2&3&4&6&9\\
13&10&8&6&4&4&4&4&6&8&12\\
17&13&10&8&6&5&5&6&8&12&15\\
21&17&13&10&8&7&8&9&12&16&20\\
27&22&17&14&11&10&11&13&16&21&27\\
34&28&22&18&15&14&15&17&21&27&35
\end{pmatrix}.
$$

$$
\left(n^{4}_{ij3}\right)_{i,j}=\begin{pmatrix}
6&4&3&2&2&2&3&5&8&11&14\\
8&6&4&3&3&4&5&7&10&14&19\\
11&8&6&5&5&5&7&10&14&19&24\\
14&11&8&7&6&7&10&13&18&24&31\\
18&14&11&9&9&10&13&18&24&31&39\\
23&18&14&12&12&14&18&24&31&40&49\\
29&23&19&17&17&19&24&31&40&50&62
\end{pmatrix}.
$$

$$
\left(n^{4}_{ij4}\right)_{i,j}=\begin{pmatrix}
5&4&3&3&4&6&8&12&15&20&24\\
7&5&5&5&6&8&11&15&20&25&30\\
9&7&6&7&8&11&15&20&26&32&37\\
12&10&9&9&11&14&20&26&33&40&46\\
16&13&12&12&15&19&25&33&42&50&57\\
21&17&15&16&20&25&33&42&52&62&70\\
27&22&20&22&26&33&42&54&66&77&86
\end{pmatrix}.
$$

$$
\left(n^{4}_{ij5}\right)_{i,j}=\begin{pmatrix}
5&4&4&6&8&10&14&17&20&22&22\\
7&6&6&8&10&14&18&22&26&27&26\\
9&8&9&10&14&18&23&28&32&33&30\\
12&11&11&14&18&23&29&35&39&40&35\\
16&14&15&18&23&30&37&44&48&49&41\\
21&19&20&24&30&38&47&55&60&58&47\\
27&25&26&31&39&49&59&68&73&70&54
\end{pmatrix}.
$$

For additional exact bounds, the minima of the coefficients in the four boxes are respectively

$$
\frac{2560}{729},\quad
\frac{69582848975}{25092716544},\quad
\frac{9108519137}{8538493824},\quad
\frac{2710955983953911}{2950903465574400}.                       \tag{3.4}
$$

The positivity consequence uses only the finite comparisons (3.2)–(3.3). To see this directly, write $B_{i,n}(u)=\binom niu^i(1-u)^{n-i}$. The binomial identity

$$
u^a=\sum_{i=a}^n\frac{\binom ia}{\binom na}B_{i,n}(u)
$$

follows on factoring out $u^a$ and expanding $(u+(1-u))^{n-a}$. Applying this identity in the three coordinates gives exactly (3.2) as the tensor Bernstein expansion of the polynomial on each box. For coordinates in $[0,1]$, these basis products are nonnegative and sum to one. Every coefficient is at least $1/2$ by (3.3), so $\Phi\ge1/2>0$ throughout all four boxes. They cover the rectangle in (2.14), including their boundaries. This proves the sign needed in Theorem 2.1 by finite exact rational comparisons, with the polynomial, index ranges and every lower-bound entry specified.

## 4. 共同第五条件下的整个已知三目标策略

**推论 4.1（条件三目标恢复）。** Let $K$ be any explicitly known set of at most three distinct targets in one entire $\mathcal F(Y;m,j)$, $m\ne j$. One deterministic strategy recovers every target of $K$ with at most three further readings, at original clocks $5,6,7$, hence at most eight total readings.

Proof. For exactly three targets, suppose $L_3$. [II, Theorem 73.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md), with precisely this non-diagonal common-fifth hypothesis, supplies labels with $r_1=r_2=1$, $r_3\ne1$, $\delta_1\ne\delta_2$, $a_1=a_2$, $c_1=c_2$. [IV, Theorem 7.1 and Corollary 7.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md) exclude constant $b$ or $d$ and supply the sparse mixed bad pairs in (2.1). In particular each nonconstant sixth response has actual fibers of size at most two. The pair $\{1,2\}$ cannot be bad at $b$ or $d$, since at $r=1$ the final pairs

$$
b:(p+x+1,p),\qquad d:(p+s+3,p+y+1)
$$

determine $x,y$ and the complete target. The same mixed pair cannot be bad at both nodes: its terminal differences would give $x_i+1=r_3(x_3+1)$ and $x_i+2=r_3(x_3+2)$, forcing $r_3=1$. Thus the two selected mixed pairs can indeed be labeled as in (2.1). All three targets realize the same ancestor readings, so Theorem 2.1 is a contradiction. This argument also covers a constant $a$ or a constant $c$. The separate mixed-sixth-root exclusion of IV, Theorem 8.1 is consistent with it but is not needed: Theorem 2.1 already allows $H_3(6)=0$.

For two distinct targets, II, Theorem 53.2 and Corollary 53.3 give recovery after fifth $J$ within the remaining two readings. A singleton can stop immediately.

To define one whole-$K$ policy, at each node declare zero remaining readings successful exactly for a set of size at most one. With $s>0$ remaining, a nonsingleton node is successful exactly when some next atom has successful remaining subtrees at every reachable actual response. Choose the first qualifying atom in the fixed order $M,J$, execute it once, read, and recurse on the actual child. The preceding nonfailure statements ensure success at the root; induction on $s$ proves correct recovery on every target of $K$. Predictions from the known finite set merely define this finite decision tree. Every executed atom is individually read, and a singleton child stops. ∎

**开放问题 4.2（不受限三目标的共同第五桥梁）。** The implication

$$
\begin{gathered}
|K|=3,\quad K\subseteq\mathcal F(H_4(Y)),\quad L_3(K,H_4(Y))\\
\Longrightarrow\quad
\exists m\ne j:\ K\subseteq\mathcal F(Y;m,j)
\end{gathered}
$$

is an additional unresolved assertion. Corollary 4.1 assumes its right-hand fiber membership; it does not establish this implication. On the diagonal joint fiber $m=j$, all gains have $g(5)=0$, and the separate whole-root-five strategy of II, Theorem 58.1 applies. Neither fact forces an unrestricted triple into any common joint fifth fiber.

## 5. JMMJ 同历史的整个基线漂移根七类

**定义 5.1（两个互补父历史）。** Fix $D_0\in\mathbb R$, $\lambda\ne0$ and $0<\varepsilon<1/6$. Set

$$
\begin{aligned}
H_J^-&=(D_0,J,D_0+24\lambda,M,D_0+48\lambda,M,D_0+312\lambda/5),\\
H_{MJ}^-&=(D_0-21\lambda,M,D_0,J,D_0+5\lambda(1+\varepsilon),M,D_0),\\
H_J(Y)&=(H_J^-,J,Y),\qquad
H_{MJ}(Y)=(H_{MJ}^-,M,Y).
\end{aligned}                                                     \tag{5.1}
$$

These retain exactly the preceding literal histories of [IV, Theorems 2.1 and 3.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md), with complementary fourth atoms. Define the whole promised classes

$$
C_J(Y)=\mathcal F(H_J(Y))\cap\{\delta=D_0,g(7)=0\},\qquad
C_{MJ}(Y)=\mathcal F(H_{MJ}(Y))\cap\{\delta=D_0,g(7)=0\}.        \tag{5.2}
$$

The baseline $D_0$ in the history is not presumed to equal an unrestricted target's drift.

**定理 5.2（JMMJ 根类的七总读逆）。** For every $Y$, the fixed fifth and sixth atoms $M,M$ recover every target in $C_J(Y)$ by original clock six, with seven total readings. Equivalently, fourth $J$, fifth $M$, sixth $M$ recover the entire $\delta=D_0,g(7)=0$ class compatible with $H_J^-$, without a gain-ray promise.

Proof. The initial read and drift promise give $g(0)=0$. Together with $g(7)=0$, write

$$
g(t)=t(t-7)(a+bt).
$$

The cumulative matrices at clocks $1,2,3$ are $J,L_0,J+L_0$, where $L_0=MJ$. Their readings force

$$
\operatorname{tr}(JP)=\frac{-4\lambda}{a+b},\quad
\operatorname{tr}(L_0P)=\frac{-24\lambda}{5(a+2b)},\quad
\operatorname{tr}((J+L_0)P)=\frac{-26\lambda}{5(a+3b)}.          \tag{5.3}
$$

All three denominators are nonzero, since the corresponding readings differ from $D_0$ and the traces are positive. Positivity also makes $a+b,a+2b,a+3b$ have the same sign. The sum relation among the three traces gives

$$
20(a+2b)(a+3b)+24(a+b)(a+3b)-26(a+b)(a+2b)
=2(a+5b)(9a+14b)=0.
$$

If $b=0$, this would force $a=0$, which is forbidden. The factor $9a+14b=0$ would give opposite signs for $a+b=-5b/9$ and $a+2b=4b/9$, which is impossible. Thus $a=-5b$, $b=\kappa\ne0$ and

$$
g(t)=\kappa h(t),\quad h(t)=t(t-5)(t-7),\quad
\kappa/\lambda=1/\operatorname{tr}(JP)>0.                       \tag{5.4}
$$

This derives the gain ray from the whole promised class. Put $R=(\kappa/\lambda)P$. Then $R$ is positive rank one,

$$
\operatorname{tr}(JR)=1,\quad \operatorname{tr}(L_0R)=8/5,
\qquad (P,g,\delta)=(R/\operatorname{tr}R,\lambda(\operatorname{tr}R)h,D_0).
$$

At clocks $4,5,6$ along the actual complementary suffix $J,M,M$, the cumulative matrices are

$$
C_0=J(J+L_0)=\begin{pmatrix}2&1\\1&1\end{pmatrix},\quad
MC_0=\begin{pmatrix}1&1\\3&2\end{pmatrix},\quad
M^2C_0=\begin{pmatrix}3&2\\4&3\end{pmatrix}.
$$

The gain samples are $\lambda h(4)=12\lambda$, $\lambda h(5)=0$, $\lambda h(6)=-6\lambda$ in this representative. The mandatory fifth reading is therefore $D_0$. From the actual fourth and sixth readings form

$$
u=\frac{Y-D_0}{12\lambda},\qquad
v=-\frac{z_6-D_0}{6\lambda}.
$$

Solving the four linear trace equations gives the explicit inverse

$$
R=\begin{pmatrix}
u-v+21/5&34/5-v\\v-29/5&2v-u-47/5
\end{pmatrix},\qquad \operatorname{tr}R=v-26/5.                \tag{5.5}
$$

Indeed substitution into the traces against $J,L_0,C_0,M^2C_0$ gives $1,8/5,u,v$. Strict positivity and rank one are exactly

$$
\begin{gathered}
29/5<v<34/5,\qquad v-21/5<u<2v-47/5,\\
(u-v+21/5)(2v-u-47/5)-(34/5-v)(v-29/5)=0.                     \tag{5.6}
\end{gathered}
$$

Conversely every $(u,v)$ satisfying (5.6) yields a legal target with the entire promised preceding history and fourth read $D_0+12\lambda u$. Thus these equations describe the whole class, rather than selected examples. An actual input guarantees them, and $\operatorname{tr}R>0$ makes normalization lawful. No unknown gain sample is used as a divisor. ∎

**命题 5.3（同一互补父历史的非空二目标纤维）。** The class $C_J(D_0+1632\lambda/55)$ contains distinct targets represented by

$$
R_1=\frac1{55}\begin{pmatrix}12&19\\36&57\end{pmatrix},\qquad
R_3=\frac1{55}\begin{pmatrix}28&35\\20&25\end{pmatrix},
\qquad G=\lambda h,\quad \delta=D_0.
$$

Proof. Both positive matrices have determinant zero, with traces $69/55,53/55$, and satisfy the two trace constraints in the proof of Theorem 5.2. Their $C_0$ traces are both $136/55$. Their $M^2C_0$ traces are $71/11,339/55$, so after the same mandatory fifth-$M$ read $D_0$, their sixth-$M$ reads are respectively $D_0-426\lambda/11$ and $D_0-2034\lambda/55$. The difference is $-96\lambda/55\ne0$. All readings belong to this same complementary history. ∎

## 6. MJMM 同历史的整个基线漂移根七类

**定理 6.1（MJMM 根类的六总读逆）。** For every $Y$, a single fifth atom $J$ recovers every target in $C_{MJ}(Y)$ by original clock five, with six total readings. Fourth $M$ followed by fifth $J$ therefore recovers the entire $\delta=D_0,g(7)=0$ class compatible with $H_{MJ}^-$.

Proof. The clock-one and clock-three readings equal the promised drift. Their positive traces force $g(1)=g(3)=0$. Together with $g(7)=0$ and the nonzero degree-at-most-three condition this gives

$$
g(t)=\kappa(t-1)(t-3)(t-7).
$$

The initial read $D_0-21\lambda$ and $\operatorname{tr}P=1$ give $\kappa=\lambda$. No alternative lower-degree gain can occur in this promised class.

At clock two the cumulative matrix is $U_0=JM=(\begin{smallmatrix}1&1\\0&1\end{smallmatrix})$, and $g(2)=5\lambda$. Thus $\operatorname{tr}(U_0P)=1+\varepsilon$, equivalently $P_{21}=\varepsilon$. Strict positivity, rank one and trace one now give the complete parametrization

$$
P(d)=\begin{pmatrix}1-d&d(1-d)/\varepsilon\\\varepsilon&d\end{pmatrix},
\qquad 0<d<1.                                                  \tag{6.1}
$$

Every such $d$ conversely gives the whole preceding history with this gain and drift. Put

$$
f_2(d)=d(1-d)/\varepsilon+\varepsilon+2d.
$$

The actual complementary fourth and fifth matrices are

$$
A_4=M^2U_0=\begin{pmatrix}1&2\\1&3\end{pmatrix},\qquad
A_5=JA_4=\begin{pmatrix}1&3\\1&2\end{pmatrix}.
$$

Their traces are respectively $1+\varepsilon+f_2(d)$ and $1+2\varepsilon+f_2(d)-d$, while $g(4)=-9\lambda$, $g(5)=-16\lambda$. Hence the actual readings determine

$$
q=-\frac{Y-D_0}{9\lambda}-1-\varepsilon=f_2(d),\qquad
v=-\frac{z_5-D_0}{16\lambda},\qquad
d=1+2\varepsilon+q-v.                                        \tag{6.2}
$$

Return (6.1), the forced gain and drift $D_0$. The denominators are known and nonzero. The full possible fourth-coordinate range is

$$
\varepsilon<q\le\frac1{4\varepsilon}+1+2\varepsilon,            \tag{6.3}
$$

since the concave quadratic $f_2$ has its maximum at $d=1/2+\varepsilon\in(0,1)$, tends to $\varepsilon$ at $d=0$, and tends to $\varepsilon+2$ at $d=1$. The upper endpoint is included. For two distinct parameters,

$$
f_2(d)=f_2(d')\ \Longleftrightarrow\ d+d'=1+2\varepsilon.
$$

Their fifth readings then differ by $16\lambda(d-d')$. In particular the inverse covers both branches of any actual fourth fiber, including its vertex, with no division by a discriminant or by a gain sample. ∎

**命题 6.2（字面 MJMM 二目标消费者）。** At $\varepsilon=1/12$, $\lambda=1$, $D_0=0$, the two parameters $d=1/2,2/3$ realize the same entire history

$$
(-21,M,0,J,65/12,M,0,M,-93/2).
$$

Proof. Their $f_2$ values are both $49/12$, so (6.2) gives the shared fourth read $-93/2$. Their actual fifth-$J$ reads are respectively $-76,-220/3$, which differ. Their sources (6.1) are strictly positive, rank one, trace one, and their common gain is $(t-1)(t-3)(t-7)$. Thus the separation occurs in the actual complementary history, with its original baseline and clocks. ∎

## 7. 实际第五子纤维的非基线替代条件

**定理 7.1（小实际子纤维恢复与必要替代）。** At $H_J(Y)$ choose fifth $M$, and at $H_{MJ}(Y)$ choose fifth $J$. For a known family $K$ in either parent, let $K_z$ denote its entire actual response fiber under that specified fifth action.

If every member of $K$ has drift $D_0$ and every $K_z$ has at most two targets, then one deterministic strategy recovers all of $K$ with at most three additional readings. The family itself may be finite or infinite, and its actual fifth and sixth values may vary.

For an unrestricted family $K$ at either parent with $L_3$, at least one actual fiber $K_z$ has $L_2$, and one of the following holds for that same fiber:

1. It contains at least three distinct targets.
2. It consists of two distinct targets with one common drift $d_*\ne D_0$, both with $g(7)=0$, sharing both possible sixth readings.

Proof. First consider any two distinct targets after one actual five-atom history, with last cumulative matrix $Q$. If the pair has $L_2$, its sixth readings coincide under each atom, and its four terminal readings coincide under each chronological sixth/seventh suffix. Otherwise a separating sixth atom or separating length-two suffix recovers the pair.

The rank-one reconstruction of [II, Theorem 53.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md) applies here to the four terminal functions, independently of that theorem's special MMJM root-six exclusion. For clarity set $X=g(7)QP=(\begin{smallmatrix}a&b\\c&d\end{smallmatrix})$. The terminal readings are

$$
\begin{aligned}
r_{MM}&=a+b+c+2d+\delta,&r_{MJ}&=a+c+d+\delta,\\
r_{JM}&=a+b+d+\delta,&r_{JJ}&=a+d+\delta.
\end{aligned}                                                     \tag{7.1}
$$

They determine $b=r_{JM}-r_{JJ}$, $c=r_{MJ}-r_{JJ}$ and $d=r_{MM}-r_{JM}-r_{MJ}+r_{JJ}$. Since $Q$ is invertible, nonnegative and has no zero row, $QP$ is strictly positive rank one. If $d\ne0$, then $a=bc/d$ and $\delta=r_{JJ}-a-d$. If $d=0$, positivity forces $g(7)=0$ and $X=0$, so all four readings equal $\delta$. Thus the four terminal functions determine $X,\delta$ in both strata.

If the common $X$ of the two targets is nonzero, invertibility of $Q$ and trace normalization determine the same $P$ and $g(7)$. With the same drift, the shared ancestor readings at the four distinct original clocks $0,1,2,3$ then determine the same entire gain polynomial, since every source trace is positive. This contradicts distinctness. Therefore an $L_2$ pair at either parent has common drift and two clock-seven roots.

If that drift were $D_0$, both targets would lie in the corresponding whole class (5.2). At $H_J(Y)$ they already share fifth $M$ and, by $L_2$, also sixth $M$; Theorem 5.2 would return the same complete target. At $H_{MJ}(Y)$ their common fifth $J$ and Theorem 6.1 already return the same complete target. Both are contradictions. Thus no distinct baseline-drift pair in an actual specified fifth fiber has $L_2$.

For the recovery assertion, execute the specified fifth atom and read $z$. Stop at a singleton $K_z$. If $K_z$ has two targets, choose the lexicographically first length-two suffix whose sixth or seventh reading separates them; it exists because the pair is not $L_2$. Execute its sixth atom and read; stop if separated, otherwise execute its seventh atom and read. This is one policy on the whole known family, with choices determined by the actual fifth history and its entire remaining fiber. The finite choice among four suffixes requires no regularity assumption on the response-to-action function.

Finally $L_3(K,H)$ requires an $L_2$ actual child for the specified fifth action. It has at least two targets. If it has exactly two, the preceding reconstruction gives the common drift and roots, and the whole-class inverses exclude drift $D_0$. Otherwise it has at least three. All ancestors and both sixth equalities in the two-target case refer to this same fixed pair. ∎

**推论 7.2（非恒定第五三目标与前一层消费者）。** An $L_3$ triple at either complementary parent whose specified fifth response is nonconstant must have a two-target child as in alternative 2 of Theorem 7.1. In particular, a triple entirely at drift $D_0$ can have $L_3$ there only if its specified fifth response is constant.

At $H_J^-$ take fourth $J$, then fifth $M$; at $H_{MJ}^-$ take fourth $M$, then fifth $J$. Any known family at drift $D_0$ whose resulting entire histories through clock five each have at most two targets is recoverable by clock seven, with at most eight total readings.

Proof. A nonconstant response on three targets has actual fibers of size at most two, so the losing child in Theorem 7.1 must use alternative 2. For the preceding-history assertion, the actual fourth read first selects $Y$; apply the whole-family policy of Theorem 7.1 at that parent. This produces a single strategy depending only on actual reads and the known family, for every possible $Y$ and fifth response. ∎

**定义 7.3（剩余同对的全部第六零层）。** In alternative 2 put

$$
QP_i=t_i\begin{pmatrix}x_iy_i&x_i\\y_i&1\end{pmatrix},\quad
t_i>0,\quad x_i,y_i>0,\quad c_i=g_i(6)t_i.
$$

Equality of both sixth readings is exactly $c_1=c_2=c$ and $c(x_1+y_1-x_2-y_2)=0$. When $c=0$, both sixth gains vanish and no sum constraint follows. When $c\ne0$, the sums agree and distinctness forces $x_1\ne x_2$, $y_1\ne y_2$, with

$$
(x_1-x_2)(y_1-y_2)=-(x_1-x_2)^2<0.
$$

Indeed equal coordinates would make the normalized sources equal, and the common drift and first four ancestor reads would make the gains equal. Both signs of $c$ remain possible. These equations are necessary conditions together with the entire fixed ancestor and actual fifth history; they do not assert existence of the pair.

## 8. 适用对应与未定数学问题

**约定 8.1（数学接口）。** The chart, failure recursion and known-domain target normalization are those of II. Theorem 2.1 adds the incompatibility of the simultaneous sparse sixth/terminal equations with the same worlds' cubic ancestor equations. Its known-three-target consumer uses II, Theorem 73.1 and IV, Theorem 7.1 only within their common non-diagonal joint fifth fiber. The whole-class inverses in Theorems 5.2 and 6.1 concern the separate literal histories (5.1), and Theorem 7.1 partitions by one actual fifth action rather than a joint fifth promise.

The positive normalization in (1.2) removes exactly $(R,H)\mapsto(cR,H/c)$ for $c>0$ and retains additive drift. This is the specified-orbit notion of identifiability in Li–Lee–Bresler, *A Unified Framework for Identifiability Analysis in Bilinear Inverse Problems with Applications to Subspace and Sparsity Models*, [Definition 2.7 and Theorem 2.8](https://arxiv.org/html/1501.06120v1). The concrete class inverses above check uniqueness over every compatible target of their promised domains; no bilinear sample threshold is used.

Whole-set adaptive discrimination is also the relevant distinction in van den Bos–Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [Theorem 6.1](https://arxiv.org/html/1907.11034v2). That theorem assumes a suspension automaton with mutually incompatible distinct states and injective splits. Those hypotheses are not imposed on the continuous calibration domain here. The policies in Corollary 4.1 and Theorem 7.1 follow directly from (1.1) and the actual fibers, with every individual read counted.

Polynomial interpolation, rank-one completion and the Bernstein convex-combination identity are tools used inside these applications. The tensor certificate (3.1)–(3.3) proves a sign for the particular ancestor determinant, including both denominator signs retained in Theorem 2.1. It gives no numerical-infeasibility assertion for a different polynomial system. The promised-factor inverse in [III, Theorem 4.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_III.md) keeps its separate known gain-space domain. The fixed-linear-palette obstruction of IV, Theorem 10.2 keeps its specified architecture; nonlinear or data-dependent inversion remains outside it.

**开放问题 8.2（不受限局部与原根）。** The unrestricted joint-fifth bridge of Open Problem 4.2, realizable larger families with variable actual fifth and sixth responses, and feasibility of the full sixteen-slot local system of IV, Theorem 9.2 remain unresolved. The common-fifth sparse exclusion does not supply an inverse on every unrestricted $\mathcal F(H_4(Y))$ or a target-cardinality bound for unrestricted losing families. The exceptional two-target secant system of IV, Theorem 6.1 is not decided by excluding its sparse third-target completion.

At the exact complementary histories (5.1), nonbaseline-drift bad pairs and actual fifth losing fibers with at least three targets remain to be realized or excluded. The necessary alternatives of Theorem 7.1 are not sufficiency conditions. The data of an unrestricted target do not by these results certify $\delta=D_0$ and $g(7)=0$. Thus the two whole promised-class inverses do not recover the unrestricted complementary fibers. The complementary fifth-$M$ subtree at the separate $JMJM$ history of IV, Proposition 3.3, and the earlier initial-$J$, initial-$MJ$ and other root alternatives also remain separate.

The original full question is still whether $n_{\rm det}(3,0)\ge9$ or a lawful full-domain decoder with at most eight total readings exists. The root slot system of IV, Theorem 9.3 has no feasibility determination here. All lower degrees, signed gains, sampled and repeated roots, constant drifts, deterministic nonregular policies and early stops remain in that full question.

## 追加锚（本行以下为增补区）

## 9. JMMJ 的完整实际父纤维与仿射对应

**定义 9.1（归一父历史与实际子集）。** In the domain $\mathcal W_3$ of Definition 1.1, write a normalized target as $W=(P,f,d)$ and put

$$
\begin{gathered}
H_p(y)=(0,J,24,M,48,M,312/5,J,y),\qquad
\mathcal P_y=\mathcal F(H_p(y)),\\
\mathcal F_y^E(z)=\mathcal F((H_p(y),E,z)),
\qquad E\in\{M,J\},\quad y,z\in\mathbb R.
\end{gathered}                                                     \tag{9.1}
$$

Thus $H_p(y)$ is precisely $H_J(Y)$ of Definition 5.1 at $D_0=0$, $\lambda=1$, $Y=y$. No drift, gain ray or root condition is imposed on $\mathcal P_y$ or its actual response subsets. Sources are strictly entrywise positive real rank-one trace-one matrices; symmetry is not assumed. Gains range over all nonzero real polynomials of degree at most three, with every sign, degree drop, repeated root and sampled root allowed, and $d$ is any real number.

The clocks, actions, stopping rules and complete target are those of Definition 1.1. In particular, each chosen atomic action is immediately read on the same unresettable, uncopyable history at its original clock. A response formula for an unchosen action is a function of a fixed target, not an additional observation.

**引理 9.2（两种增益符号的仿射输运）。** For $D_0\in\mathbb R$ and $\lambda\in\mathbb R\setminus\{0\}$, define

$$
\Phi_{D_0,\lambda}(P,f,d)=(P,\lambda f,D_0+\lambda d).
                                                                  \tag{9.2}
$$

This is a bijection of $\mathcal W_3$. On every fixed action word, it maps each normalized reading $z_i$ to $D_0+\lambda z_i$. Consequently it maps $\mathcal P_y$ bijectively onto $\mathcal F(H_J(Y))$ for $Y=D_0+\lambda y$, with exactly the parameters $D_0,\lambda$ in (5.1). It preserves complete-target distinction, actual response fibers, every failure predicate $L_s$, and recoverability by deterministic policies with early stopping and the same number of readings. These assertions hold for both signs of $\lambda$.

Proof. The inverse is $(P,g,\delta)\mapsto(P,g/\lambda,(\delta-D_0)/\lambda)$. Source positivity, rank and trace are unchanged; multiplication of a nonzero polynomial by $\lambda\ne0$ preserves its degree and roots. At every original clock,

$$
(\lambda f(i))\operatorname{tr}(A_iP)+D_0+\lambda d
=D_0+\lambda\bigl(f(i)\operatorname{tr}(A_iP)+d\bigr).
$$

Since this affine map on readings is injective, corresponding actual children are bijective. Induction in (1.1) proves preservation of $L_s$: cardinalities are preserved at $s=0$, and the possible next response values are related bijectively at each induction step. To transport a policy, apply the inverse affine map to each acquired reading before making the original policy's next action, stop or output decision, and apply $\Phi_{D_0,\lambda}$ to its returned target. The inverse construction transports policies back. No comparison of ordered readings or sign of $\lambda$ is used. ∎

**引理 9.3（同历史单调性与二目标判据）。** Let $H$ be one literal history and $K\subseteq K'\subseteq\mathcal F(H)$, with no cardinality restriction. For every nonnegative integer $s$,

$$
L_s(K,H)\ \Longrightarrow\ L_s(K',H).                            \tag{9.3}
$$

For a two-target set after clock five, $L_2$ holds exactly when the same pair has equal readings under both sixth actions and under all four chronological sixth/seventh suffixes. For a two-target set after clock six, $L_1$ holds exactly when both possible final readings agree on the pair.

Proof. For $s=0$, inclusion preserves the existence of two distinct targets. If the assertion holds for $s-1$, each losing actual child of $K$ is contained in the corresponding actual child of $K'$; apply the induction hypothesis there and then (1.1). For a two-target set, a child has at least two targets precisely when both remain in that child. Applying this observation once gives the $L_1$ criterion and twice gives the $L_2$ criterion. A deterministic early stop cannot return different complete targets on an identical history, so it does not remove either obstruction. ∎

## 10. 不预设增益射线的全部第五 J 二目标必要性

**定理 10.1（第五 J 的二目标完全刻画）。** Let $y,\xi\in\mathbb R$ and let $W_1,W_2$ be distinct complete targets in $\mathcal F_y^J(\xi)$. Put

$$
t=\frac5{96}(y-12),\qquad
Q_t(\ell)=\left(t^2-\frac38\right)\ell^2+
                  \left(\frac{11}8-3t\right)\ell+1.              \tag{10.1}
$$

Then

$$
L_2(\{W_1,W_2\},(H_p(y),J,\xi))                                \tag{10.2}
$$

holds if and only if $\xi=0$ and there exist two distinct real roots $\ell_1,\ell_2$ of $Q_t$ such that

$$
\begin{gathered}
1<\ell_i<\frac83,\qquad 0<t\ell_i-1<1,\\
W_i=W_{\ell_i}=(P_{\ell_i},f_{\ell_i},0),\\
P_\ell=\begin{pmatrix}
t\ell-1&\ell-1\\
1-3\ell/8&2-t\ell
\end{pmatrix},\qquad
f_\ell(T)=\frac8{5\ell}\,T(T-5)(T-7).
\end{gathered}                                                     \tag{10.3}
$$

In particular, baseline drift and the gain ray are consequences of (10.2), not promises on the starting pair. This statement classifies two-target $L_2$ sets; it does not classify larger losing families or pairs required to collide only after one already specified sixth action.

Proof. The actual cumulative matrices at clocks one through five, with fifth action $J$, are

$$
J,\quad L_0=MJ,\quad Q=J+L_0=
\begin{pmatrix}1&1\\2&1\end{pmatrix},\quad
C_0=JQ=\begin{pmatrix}2&1\\1&1\end{pmatrix},\quad Q.
                                                                  \tag{10.4}
$$

By Lemma 9.3, (10.2) gives equality of all four terminal response functions of this same pair. Apply the terminal reconstruction subargument of Theorem 7.1, specifically (7.1), at the actual fifth matrix $Q$. Its hypotheses hold: $\det Q=-1$, $Q$ is nonnegative with no zero row, and each $QP_i$ is strictly positive rank one. That subargument determines the same matrix $X=f_i(7)QP_i$ and the same drift $d$ from the four response functions, including its zero-entry stratum. If $X\ne0$, invertibility and trace normalization give the same $P_i$ and $f_i(7)$; the common ancestor readings at clocks $0,1,2,3$ then give the same entire polynomial $f_i$, since their source trace factors are positive. This contradicts distinctness. Hence

$$
d_1=d_2=d,\qquad f_1(7)=f_2(7)=0.                              \tag{10.5}
$$

Only the terminal subargument is being applied here; the later fifth-$M$ baseline exclusion in Theorem 7.1 concerns a different actual child.

For each of these same two targets write

$$
\begin{gathered}
P_i=\begin{pmatrix}r_i&u_i\\v_i&1-r_i\end{pmatrix},\quad
\jmath_i=u_i+v_i>0,\quad \ell_i=1+u_i>1,\quad
a_i=\jmath_i+\ell_i>0,\\
q_i=\jmath_i/a_i\in(0,1),\quad h_i=a_if_i,\quad
\alpha_i=(1+r_i+\jmath_i)/a_i>0.
\end{gathered}                                                     \tag{10.6}
$$

The trace factors at clocks $0,\ldots,5$ in (10.4) are

$$
1,\quad \jmath_i,\quad \ell_i,\quad a_i,\quad
1+r_i+\jmath_i,\quad a_i.
$$

Use the common constants

$$
\begin{gathered}
A=312/5-d,\quad B=\xi-d,\quad C=24-d,\quad D=48-d,\\
K=15A-5B,\qquad L=-5A+15B,\qquad N=9A+9B.
\end{gathered}                                                     \tag{10.7}
$$

The parent and actual fifth equations imply

$$
h_i(3)=A,\quad h_i(5)=B,\quad h_i(7)=0,\quad
q_ih_i(1)=C,\quad (1-q_i)h_i(2)=D.                              \tag{10.8}
$$

Polynomial interpolation at the four distinct clocks $1,3,5,7$, valid for every degree at most three, gives

$$
\begin{aligned}
16h_i(2)&=5C/q_i+K,\\
16h_i(4)&=-C/q_i+N,\\
16h_i(6)&=C/q_i+L.
\end{aligned}                                                     \tag{10.9}
$$

For example, the coefficient rows of the interpolant at $2,4,6$, relative to its values at $1,3,5,7$, are respectively $(5,15,-5,1)/16$, $(-1,9,9,-1)/16$, $(1,-5,15,5)/16$. Thus each $q_i$ satisfies

$$
(1-q_i)(5C+Kq_i)=16Dq_i.                                      \tag{10.10}
$$

Let $w_J,w_M$ be the pair's common actual sixth responses after the fifth $J$. The actual fourth and sixth equations are

$$
y-d=\alpha_i h_i(4),\quad
w_J-d=\alpha_i h_i(6),\quad
w_M-d=(2-q_i)h_i(6),                                         \tag{10.11}
$$

because $\operatorname{tr}(MQP_i)=\jmath_i+2\ell_i=(2-q_i)a_i$.

We first prove $q_1=q_2$. If $C=0$, then $d=24$ and $D=24$; division of (10.10) only by $q_i>0$ gives $K(1-q_i)=384$. This has at most one solution, including the case $K=0$, when it has none. Suppose instead that $C\ne0$ and $q_1\ne q_2$. They are roots of

$$
-Kq^2+(K-5C-16D)q+5C=0.
$$

The constant term is nonzero, so two distinct roots require $K\ne0$ and give $q_1q_2=-5C/K$. Equality of the sixth-$M$ responses in (10.11), using (10.9), gives

$$
(q_2-q_1)(2C+Lq_1q_2)=0,\qquad L=\frac{2K}{5}.                 \tag{10.12}
$$

The first two common responses in (10.11), and $\alpha_1\alpha_2>0$, also imply

$$
h_1(4)h_2(6)-h_2(4)h_1(6)=0.
$$

After multiplication by $256q_1q_2$, (10.9) makes this equation

$$
C(N+L)(q_1-q_2)=0,\qquad N+L=0.                              \tag{10.13}
$$

No gain sample or response is divided out in either cancellation. Equations (10.12)–(10.13) say $-11A+17B=0$ and $A+6B=0$, whence $A=B=0$, contradicting $K\ne0$. This proves $q_1=q_2=q$. The four values at $1,3,5,7$ now agree, so $h_1=h_2=h$ as polynomials.

Suppose $d\ne0$. The initial read gives $h(0)=-a_id$, so $a_1=a_2=a$. Consequently $\jmath_i=qa$ and $\ell_i=(1-q)a$ agree. If either $h(4)$ or $h(6)$ is nonzero, its common response in (10.11) fixes $\alpha_i$, hence $r_i$; then $u_i=\ell_i-1$, $v_i=\jmath_i-u_i$ and $f_i=h/a$ agree as well. This again contradicts distinctness.

The remaining nonzero-drift case has $h(4)=h(6)=0$. Since also $f_i(7)=0$, a nonzero polynomial of degree at most three must have exactly the form

$$
f_i(T)=\frac d{168}(T-4)(T-6)(T-7),                            \tag{10.14}
$$

where its initial value $f_i(0)=-d$ fixes the coefficient. The parent readings at $1,2,3$ then require, for either source,

$$
\jmath=\frac{28(d-24)}{15d},\qquad
\ell=\frac{21(d-48)}{5d},\qquad
a=\frac{14(d-312/5)}d.
$$

The identity $a=\jmath+\ell$ gives $d=1344/17$, and therefore $\jmath=13/10$, $\ell=33/20$, $u=v=13/20$. But rank one and trace one require

$$
uv=r(1-r)\le\frac14,\qquad
\frac{169}{400}>\frac14,
$$

a contradiction even for one legal source. The three distinct roots in (10.14) also exclude a lower-degree exception. Thus $d=0$ is necessary.

Now each target lies in the whole promised class $C_J(y)$ of (5.2), with exactly $D_0=0$, $\lambda=1$, baseline drift and the already proved seventh root. Apply the gain-ray conclusion (5.4) of Theorem 5.2. It gives $f_i(T)=\kappa_i T(T-5)(T-7)$, with $\kappa_i>0$, and the trace constraints there give

$$
\kappa_i\jmath_i=1,\qquad \kappa_i\ell_i=8/5.
$$

Hence $\jmath_i=5\ell_i/8$, $\kappa_i=8/(5\ell_i)$ and $\xi=0$. The common fourth reading is

$$
y=\frac{96}{5\ell_i}(1+r_i+\jmath_i)
  =12+\frac{96}{5}\frac{1+r_i}{\ell_i}.
$$

Thus $r_i=t\ell_i-1$ with the common $t$ in (10.1), and the source is exactly (10.3). Its determinant is $-Q_t(\ell_i)$. Its four entries are strictly positive exactly when $1<\ell_i<8/3$ and $0<t\ell_i-1<1$. Equality of the two $\ell_i$ would now give equality of the complete targets, so the roots are distinct.

Conversely, take any two distinct roots satisfying these strict inequalities. Formula (10.3) gives positive trace-one sources with determinant zero, and nonzero degree-three gains. Their trace factors along the entire original parent are

$$
1,\quad 5\ell/8,\quad \ell,\quad 13\ell/8,\quad
(t+5/8)\ell.
$$

Multiplying by the gain samples at clocks $0,1,2,3,4$ gives exactly $0,24,48,312/5,y$. After fifth $J$ the reading is $0$; sixth $J$ reads $-y/2$ and sixth $M$ reads $-126/5$ on both targets. Every seventh reading is $0$, since both gains vanish at $7$. Lemma 9.3 proves (10.2). The sixth gain samples are $-48/(5\ell)\ne0$. All zero-sample and degree-drop cases were retained in (10.8)–(10.13) before the final form was deduced; no leading gain coefficient or unknown gain sample was used as a divisor. ∎

## 11. 两个尖锐合法窗口与同一配对的全部实际响应

**定理 11.1（严格正源的精确窗口）。** The polynomial $Q_t$ in (10.1) has two distinct roots satisfying (10.3) exactly when

$$
t\in\left(\frac34,\frac{31}{40}\right)
       \ \cup\ \left(\frac78,1\right).
                                                                  \tag{11.1}
$$

Equivalently, an actual fifth-$J$ two-target $L_2$ set exists at $H_p(y)$ exactly when

$$
y\in\mathcal I:=
\left(\frac{132}5,\frac{672}{25}\right)
\ \cup\
\left(\frac{144}5,\frac{156}5\right).                            \tag{11.2}
$$

At the four excluded endpoints, the roots and their failure mechanisms are

$$
\begin{array}{c|c|c}
t&\text{roots of }Q_t&\text{obstruction to a distinct legal pair}\\ \hline
3/4&2,\ 8/3&\ell=8/3\text{ has zero source entries}\\
31/40&40/19\text{ (double)}&\text{only one target}\\
7/8&8/5\text{ (double)}&\text{only one target}\\
1&1,\ 8/5&\ell=1\text{ has zero source entries}.
\end{array}                                                       \tag{11.3}
$$

Proof. Two distinct legal roots are positive. Since $Q_t$ has constant coefficient $1$, it is not identically zero, and a degree drop leaves at most one root. Thus its leading coefficient $a_t=t^2-3/8$ is nonzero. The positive product of the roots gives $a_t>0$. Legality also gives $0<t<2$, and puts both roots strictly between $1/t$ and $2/t$. An upward quadratic is positive strictly outside its two roots, so

$$
Q_t(1/t)=-\frac{(8t-3)(t-1)}{8t^2}>0,\qquad
Q_t(2/t)=-\frac{(4t-3)(t-2)}{4t^2}>0.                          \tag{11.4}
$$

With $0<t<2$, the second inequality implies $t>3/4$; the first then implies $t<1$. Its discriminant is

$$
\Delta_t=\left(\frac{11}8-3t\right)^2
          -4\left(t^2-\frac38\right)
        =5\left(t-\frac{31}{40}\right)\left(t-\frac78\right).
                                                                  \tag{11.5}
$$

Two distinct real roots require $\Delta_t>0$, giving exactly (11.1).

Conversely, let $t$ lie in (11.1). Then $a_t>0$, both endpoint values in (11.4) are positive, and $\Delta_t>0$. The vertex

$$
\ell_*=\frac{24t-11}{16t^2-6}
$$

lies strictly between $1/t$ and $2/t$: after multiplication by the positive $t(16t^2-6)$, the two inequalities have respective numerators

$$
8t^2-11t+6>0,\qquad 8t^2+11t-12>0.
$$

The first quadratic has discriminant $-71$ and positive leading coefficient. The second has value $3/4$ at $t=3/4$ and positive derivative for $t>3/4$. Since $Q_t(\ell_*)=-\Delta_t/(4a_t)<0$, there is a root on each side of this vertex inside $(1/t,2/t)$. These are its two roots. Moreover

$$
1<1/t<\ell<2/t<8/3,
$$

so all the strict source conditions hold. The affine relation $y=12+96t/5$ gives (11.2). Direct factorization at the endpoints gives (11.3); the two double roots are legal but each yields only one complete target. This also covers the discriminant-zero and leading-coefficient-zero possibilities. Theorem 10.1 supplies both directions of the asserted existence criterion. ∎

**定义 11.2（绑定的同父二目标族）。** For every $y\in\mathcal I$, set $t=5(y-12)/96$ and define the one family

$$
\begin{aligned}
\mathcal R_t&=\{\ell\in\mathbb R:
Q_t(\ell)=0,\ 1<\ell<8/3,\ 0<t\ell-1<1\},\\
\mathcal A_y&=\{W_\ell:\ell\in\mathcal R_t\},
\end{aligned}                                                     \tag{11.6}
$$

where $W_\ell$ is exactly the complete target (10.3). By Theorems 10.1 and 11.1, $\mathcal A_y$ has exactly two elements, both in the same entire literal parent $\mathcal P_y$. The symbol $\mathcal A_y$ always denotes this set, including when it is retained in a fifth-$M$ or sixth-action response child.

**命题 11.3（同一族的实际分支与非父层失败）。** Fix $y\in\mathcal I$ and the family $\mathcal A_y$ of (11.6). For each $W_\ell\in\mathcal A_y$, its predictions at original clocks $5,6,7$ are as follows; the last column holds for either final atom:

$$
\begin{array}{c|c|c|c|c}
E_5&E_6&z_5&z_6&z_7\\ \hline
J&J&0&-y/2&0\\
J&M&0&-126/5&0\\
M&J&0&48/5-y&0\\
M&M&0&-156/5-48/(5\ell)&0.
\end{array}                                                       \tag{11.7}
$$

In particular,

$$
\begin{gathered}
L_2(\mathcal A_y,(H_p(y),J,0)),\\
\mathcal A_y\subseteq
\mathcal F((H_p(y),M,0,J,48/5-y)),\\
L_1(\mathcal A_y,(H_p(y),M,0,J,48/5-y)),\\
\neg L_2(\mathcal A_y,(H_p(y),M,0)),\qquad
\neg L_3(\mathcal A_y,H_p(y)).
\end{gathered}                                                     \tag{11.8}
$$

Proof. The first two rows were computed in Theorem 10.1. For fifth $M$, the cumulative matrix is $MC_0$, and $f_\ell(5)=0$ gives the same fifth read $0$. The two sixth trace factors are

$$
\operatorname{tr}(JMC_0P_\ell)=(2t+1/4)\ell,\qquad
\operatorname{tr}(M^2C_0P_\ell)=1+13\ell/4.
$$

Multiplying by $f_\ell(6)=-48/(5\ell)$ and using $y=12+96t/5$ gives the last two sixth responses. The gain vanishes at $7$ for every final action. Lemma 9.3 proves the positive failure assertions. The last sixth response is injective in $\ell>0$, so fifth $M$, sixth $M$ separate the pair by clock six. This proves both negations in (11.8); it is the restriction of the existing whole-class inverse of Theorem 5.2 to this pair, not an inverse on $\mathcal P_y$.

For the existing representatives in Proposition 5.3, the normalized parameters are $y=1632/55$, $t=81/88$ and $\ell=88/69,88/53$. They are instances of (11.6), with exactly the same $M,M$ separation as that proposition. ∎

## 12. 强制实际动作与任意基数的同父粘合

**定理 12.1（全纤维成功解码的必要动作）。** Let $y\in\mathcal I$. Any deterministic decoder that recovers every complete target of the whole unrestricted fiber $\mathcal P_y$ by original clock seven must choose fifth $M$. After its actual fifth-$M$ response $0$, it must choose sixth $M$. The same sixth-action necessity holds for any decoder required to recover the whole fiber $\mathcal F_y^M(0)$ with at most two further readings. These are necessary conditions on a successful decoder; existence of such a decoder is not a hypothesis-free conclusion.

Proof. The parent contains both elements of $\mathcal A_y$, so an immediate stop cannot recover all of it. Fifth $J$ has the actual response-$0$ child containing this same pair with $L_2$, by (11.8) and monotonicity (9.3). That child cannot be recovered within clocks $6,7$, including by a history-dependent sixth action and early stops. Therefore a successful parent decoder must choose fifth $M$. Its actual response-$0$ fiber contains the same two targets, so it cannot stop there. Sixth $J$ has the actual response-$(48/5-y)$ child containing $\mathcal A_y$ with $L_1$; no final choice or early stop recovers that child. Thus the necessary sixth action is $M$. Separation of $\mathcal A_y$ under that action proves only recovery of this pair, as stated in Proposition 11.3. ∎

**定理 12.2（同父粘合与整个父纤维的条件等价）。** Fix one $y\in\mathcal I$. For every $z\in\mathbb R$ and every family $\mathcal B\subseteq\mathcal F_y^M(z)$ of arbitrary cardinality, if

$$
L_2(\mathcal B,(H_p(y),M,z)),
$$

then the family $\mathcal U=\mathcal A_y\cup\mathcal B$ consists of fixed legal targets in $\mathcal P_y$ and satisfies

$$
L_3(\mathcal U,H_p(y)).                                        \tag{12.1}
$$

More generally, for every $\mathcal A_y\subseteq K\subseteq\mathcal P_y$,

$$
\begin{aligned}
L_3(K,H_p(y))
\quad\Longleftrightarrow\quad
\exists z\in\mathbb R:\quad
L_2(K\cap\mathcal F_y^M(z),(H_p(y),M,z)).
\end{aligned}                                                     \tag{12.2}
$$

In particular (12.2) holds for $K=\mathcal P_y$. No finiteness, common drift, common gain ray, common response under the other fifth action, or two-target losing subset is required of $\mathcal B$.

Proof. All targets in $\mathcal B$ share the entire literal $H_p(y)$ by its assumed actual-child membership; those in $\mathcal A_y$ share that identical history by (11.6). Thus their union uses one and the same $y$ and never changes any target. Its fifth-$J$ response-$0$ child contains $\mathcal A_y$ with $L_2$, and its fifth-$M$ response-$z$ child contains $\mathcal B$ with $L_2$. Lemma 9.3 gives the same failure predicates on the corresponding union children. Applying (1.1) proves (12.1). The two fifth response values need not coincide.

For (12.2), the forward implication is the fifth-$M$ clause of (1.1). Conversely, the stated fifth-$M$ child supplies that clause, and the fifth-$J$ response-$0$ child of $K$ contains $\mathcal A_y$, supplying the other clause by (11.8) and (9.3). This proves the equivalence without extracting a pair or triple from an arbitrary losing family. ∎

**定理 12.3（实际 M0 子纤维的精细第六 M 消费者）。** Fix one $y\in\mathcal I$ and put

$$
H_{M0}=(H_p(y),M,0),\qquad \beta_y=48/5-y.
$$

For every family $\mathcal A_y\subseteq K_0\subseteq\mathcal F_y^M(0)$ of arbitrary cardinality,

$$
\begin{aligned}
L_2(K_0,H_{M0})
\quad\Longleftrightarrow\quad
\exists v\in\mathbb R:\quad
L_1\bigl(K_0\cap\mathcal F((H_{M0},M,v)),(H_{M0},M,v)\bigr).
\end{aligned}                                                     \tag{12.3}
$$

Consequently, for any real $v$ and any family

$$
\mathcal T\subseteq\mathcal F((H_p(y),M,0,M,v)),\qquad
L_1(\mathcal T,(H_p(y),M,0,M,v)),
                                                                  \tag{12.4}
$$

the explicitly bound union $\mathcal U_0=\mathcal A_y\cup\mathcal T$ satisfies

$$
L_2(\mathcal U_0,H_{M0}),\qquad L_3(\mathcal U_0,H_p(y)).          \tag{12.5}
$$

The $L_1$ hypothesis in (12.4) concerns both final actions on that same $\mathcal T$; their witnessing collision pairs may differ. It does not require $v=\beta_y$, and no cardinality or drift promise is imposed on $\mathcal T$.

Proof. The same defined family $\mathcal A_y$ lies in the actual sixth-$J$ response-$\beta_y$ child of $H_{M0}$ and has $L_1$ there, by (11.8). Thus every $K_0$ as stated already has the sixth-$J$ clause needed in (1.1). Its sixth-$M$ clause is exactly the right-hand side of (12.3). This proves both directions.

For (12.4), all elements of $\mathcal U_0$ share the entire same $H_{M0}$. Its sixth-$J$ response-$\beta_y$ child contains $\mathcal A_y$ with $L_1$, and its sixth-$M$ response-$v$ child contains $\mathcal T$ with $L_1$. Monotonicity and (1.1) give the first assertion in (12.5). At the original parent, the fifth-$M$ response-$0$ child is $\mathcal U_0$ and therefore has $L_2$; the fifth-$J$ response-$0$ child contains $\mathcal A_y$ with $L_2$. Applying (1.1) again gives the second assertion. Every inclusion uses the same fixed targets and the same literal $y$. The existential response in the $L_1$ definition can be chosen separately for each final action; hence the proof does not assume one common terminal collision pair inside $\mathcal T$. ∎

**推论 12.4（原参数下的两个窗口与实际动作）。** Let $D_0\in\mathbb R$, $\lambda\ne0$, $Y\in\mathbb R$ and $y=(Y-D_0)/\lambda$. At the literal parent $H_J(Y)$ of (5.1), a two-target $L_2$ set in an actual fifth-$J$ child exists exactly for $y\in\mathcal I$. Every such pair is the image under $\Phi_{D_0,\lambda}$ of the pair (11.6), has drift $D_0$, and has actual fifth-$J$ response $D_0$. On these normalized windows, every successful whole-parent decoder by clock seven must choose fifth $M$ and, after actual response $D_0$, sixth $M$.

All same-parent inclusions, arbitrary-cardinality gluing implications and conditional equivalences of Theorems 12.2–12.3 transport by $\Phi_{D_0,\lambda}$. In the finer consumer the actual fifth response is $D_0$, the sixth-$J$ response is

$$
D_0+\lambda\beta_y=2D_0+\frac{48\lambda}{5}-Y,
$$

and an arbitrary normalized sixth-$M$ response $v$ becomes $D_0+\lambda v$.

Proof. Apply the bijection of Lemma 9.2 to Theorems 10.1, 11.1 and 12.1–12.3 and to each of their actual history arguments. The two windows are imposed on $y=(Y-D_0)/\lambda$, so negative $\lambda$ requires no assumption about the order of physical $Y$ endpoints. Every transported family shares the entire corresponding $H_J(Y)$; the displayed sixth response follows by substitution. These conditional implications do not supply a family satisfying the fifth-$M$ $L_2$ premise or the finer sixth-$M$ $L_1$ premise. ∎

## 追加锚（本行以下为增补区）
## 13. 同一 JMMJMM 历史的联合实现方程

**定义 13.1（三个固定目标的有理参数）。** Work in the complete-target domain $\mathcal W_3$ and the original-clock history convention of Definitions 1.1 and 9.1. For $\alpha,\beta>0$ and $d\in\mathbb R$, put

$$
\begin{gathered}
h=1+\alpha\beta,\qquad
P(\alpha,\beta)=\frac1h
\begin{pmatrix}1&\beta\\\alpha&\alpha\beta\end{pmatrix},\\
a=\frac1h,\qquad j=\frac{\alpha+\beta}{h},\qquad
\ell=1+\frac\beta h,\qquad
\tau=(1,j,\ell,j+\ell),\qquad b=(0,24,48,312/5),\\
q_i=\frac{b_i-d}{\tau_i}\quad(0\le i\le3),\qquad
f(T)=\sum_{i=0}^3q_i
\prod_{\substack{0\le m\le3\\m\ne i}}\frac{T-m}{i-m}.
\end{gathered}                                                     \tag{13.1}
$$

There is one polynomial $f$ for this target throughout all continuations. Denote its later samples by

$$
\begin{pmatrix}f_4\\f_5\\f_6\\f_7\end{pmatrix}=
\begin{pmatrix}
-1&4&-6&4\\
-4&15&-20&10\\
-10&36&-45&20\\
-20&70&-84&35
\end{pmatrix}
\begin{pmatrix}q_0\\q_1\\q_2\\q_3\end{pmatrix}.                 \tag{13.2}
$$

Define the trace factors and response functions

$$
\begin{gathered}
A=1+a+j,\qquad B=j+2\ell-a,\\
Y=d+f_4A,\qquad Z=d+f_5B,\qquad V=d+f_6(A+B),\\
R=d+f_7(2A+j),\qquad S=d+f_7(A+2B).
\end{gathered}                                                     \tag{13.3}
$$

For $x=(\alpha_1,\beta_1,d_1,\alpha_2,\beta_2,d_2,
\alpha_3,\beta_3,d_3)$, attach subscript $i$ to these functions evaluated on its $i$th coordinate triple. The jointly constrained map is

$$
F(x)=
\begin{pmatrix}
Z_1\\ Z_2\\ Z_3\\
Y_1-Y_2\\ Y_1-Y_3\\
V_1-V_2\\ V_1-V_3\\
R_1-R_2\\ S_1-S_3
\end{pmatrix}.                                                    \tag{13.4}
$$

In particular, the two terminal equalities concern the pairs $\{1,2\}$ and $\{1,3\}$ within the same three targets. All equations in (13.4), including the ancestor equalities, are simultaneous.

## 14. 联合零点的完整有理盒证书

**定义 14.1（中心、矩阵与区间运算）。** Let $\rho=10^{-8}$ and set

$$
x_0=\frac1{10^{15}}
\begin{pmatrix}
648261282725604\\
1661406963929015\\
2963341227084761\\
267996473307519\\
1637499998610191\\
4652954721959948\\
576125340775968\\
10453577045282132\\
15807600936593863
\end{pmatrix},\qquad
X=\{x\in\mathbb R^9:\|x-x_0\|_\infty\le\rho\}.                \tag{14.1}
$$

Use the rational matrix

$$
C=\frac1{10^6}
\begin{pmatrix}
1023801&217453&-1001127&168959&-262908&78207&-721314&-16353&132738\\
391102&-378813&-8273&-294334&-2173&-136240&-5961&28487&1097\\
864656&-1063712&44044&-826493&11566&-382564&31734&79992&-5840\\
147048&-359545&162474&-20132&42668&-386529&117063&165543&-21542\\
-65905&-1886&53887&5189&14152&33283&38826&-18326&-7145\\
718648&4820697&-4559578&63606&-1197400&4024327&-3285186&-1551509&604549\\
24068&-20689&-480&-16075&6305&-7441&-14419&1556&4154\\
-858169&-695624&1582086&-540493&945650&-250181&935725&52312&-180525\\
1329025&2475184&-3103628&1923192&-2606045&890200&-1860321&-186137&311185
\end{pmatrix}.                                                    \tag{14.2}
$$

Every interval endpoint below is rational. For $U=[u_-,u_+]$ and $V=[v_-,v_+]$, the operations are

$$
\begin{aligned}
U+V&=[u_-+v_-,u_++v_+],&
-U&=[-u_+,-u_-],\\
UV&=\bigl[\min_{\epsilon,\eta\in\{-,+\}}u_\epsilon v_\eta,
          \max_{\epsilon,\eta\in\{-,+\}}u_\epsilon v_\eta\bigr],&
V^{-1}&=[1/v_+,1/v_-]\quad(0\notin V),\\
U/V&=UV^{-1},&
\operatorname{mag}(U)&=\max(|u_-|,|u_+|).
\end{aligned}                                                     \tag{14.3}
$$

Real constants are singleton intervals, subtraction is addition of the negative, and squares are products of the interval with itself. Evaluate (13.1)–(13.4) with the displayed parentheses, starting from $[x_{0i}-\rho,x_{0i}+\rho]$. In particular $\ell=1+\beta/h$, rather than an algebraically expanded expression. Linear combinations use the displayed terms; (13.2) uses its four columns in order.

Here is an explicit derivative specification for the interval matrix $[DF](X)$. Gradients are row vectors in coordinate order $(\alpha,\beta,d)$; put $e_d=(0,0,1)$. Use

$$
\begin{gathered}
Da=\frac{(-\beta,-\alpha,0)}{h^2},\qquad
Dj=\frac{(1-\beta^2,1-\alpha^2,0)}{h^2},\qquad
D\ell=\frac{(-\beta^2,1,0)}{h^2},\\
D\tau=(0,Dj,D\ell,Dj+D\ell),\\
Dq_i=-\frac{(b_i-d)D\tau_i}{\tau_i^2}
      -\frac{e_d}{\tau_i}\quad(0\le i\le3),\\
Df_s=\sum_{i=0}^3w_{si}Dq_i\quad(4\le s\le7),
\end{gathered}                                                     \tag{14.4}
$$

where $w_{si}$ are the entries of (13.2). For each response in (13.3), use

$$
D(d+f_sT)=e_d+T Df_s+f_sDT,\qquad
(s,T)=(4,A),(5,B),(6,A+B),(7,2A+j),(7,A+2B),                    \tag{14.5}
$$

with $DA=Da+Dj$ and $DB=Dj+2D\ell-Da$. Assemble the nine rows according to (13.4); a response has zero derivatives in the other two targets' coordinates. The notation $[DF](X)$ means precisely evaluation of (14.4)–(14.5) by (14.3), without algebraic substitution for the displayed gradients. Define

$$
\mathcal D_{ij}=[\delta_{ij},\delta_{ij}]
                  -\sum_{k=1}^9 C_{ik}[DF]_{kj}(X),
\qquad m_i=\sum_{j=1}^9\operatorname{mag}(\mathcal D_{ij}),      \tag{14.6}
$$

where $\delta_{ij}$ is the Kronecker symbol. Thus (13.1)–(14.6) specify the entire finite rational certificate.

**定理 14.2（精确联合零点与投影）。** The map $F$ has exactly one zero $x_*$ in $X$. It is defined without a rounded equality by

$$
x^{(0)}=x_0,\qquad
x^{(n+1)}=x^{(n)}-CF(x^{(n)}),\qquad
x_*=\lim_{n\to\infty}x^{(n)}.                                  \tag{14.7}
$$

All these iterates lie in $X$, and

$$
\|x_*-x_0\|_\infty<\frac{40}{39}\,10^{-14}<2\cdot10^{-14}.
                                                                  \tag{14.8}
$$

For $y_*=Y_1(x_*)$ and $v_*=V_1(x_*)$,

$$
\frac{29286821}{10^6}<y_*<\frac{29286822}{10^6},\qquad
-\frac{45328099}{10^6}<v_*<-\frac{45328097}{10^6}.               \tag{14.9}
$$

Proof. All $\alpha_i,\beta_i$ are strictly positive throughout $X$. Therefore $h_i,j_i,\ell_i,j_i+\ell_i$ and their squared denominators in (14.4) are positive; their interval lower endpoints under (14.3) are positive as well. Product and quotient differentiation of (13.1) gives exactly (14.4), and (14.5) is the product rule for (13.3). Thus $F$ is continuously differentiable on a neighborhood of $X$, and every actual derivative matrix $DF(x)$ is enclosed by $[DF](X)$.

The endpoint operations (14.3) give the following finite comparisons:

$$
\|CF(x_0)\|_\infty<\frac{37711955}{10^{23}}<10^{-14},            \tag{14.10}
$$

and, for each row, $m_i<n_i/10^{12}<c_i/10^6$, with all nine entries specified here:

$$
\begin{array}{c|r|r}
i&n_i&c_i\\ \hline
1&2619848233&2620\\
2&654912347&655\\
3&1903547437&1904\\
4&2007031636&2008\\
5&571807883&572\\
6&19941425792&19942\\
7&151118857&152\\
8&3726043872&3727\\
9&7932801408&7933
\end{array}                                                       \tag{14.11}
$$

These inequalities follow by rational endpoint addition, multiplication, reciprocal and comparison from the integers in (14.1)–(14.2) and formulas (13.1)–(14.6). In particular they concern the whole box $X$. Since $19942/10^6<1/40$, they imply

$$
\sup_{x\in X}\|I-CDF(x)\|_\infty<\frac1{40}.                   \tag{14.12}
$$

Put $G(x)=x-CF(x)$. Integration of its derivative along the segment between two points of the convex box $X$ gives Lipschitz constant $1/40$. Also, for every $x\in X$,

$$
\begin{aligned}
\|G(x)-x_0\|_\infty
&\le\|G(x)-G(x_0)\|_\infty+\|CF(x_0)\|_\infty\\
&<\frac1{40}\,10^{-8}+10^{-14}<10^{-8}.
\end{aligned}                                                     \tag{14.13}
$$

Thus $G$ is a self-map and a contraction of the complete closed box $X$. The Banach contraction principle applies: the iterates (14.7) converge to its unique fixed point. The geometric-series error estimate is

$$
\|x_*-x_0\|_\infty
\le\sum_{n=0}^\infty(1/40)^n\|CF(x_0)\|_\infty
<\frac{40}{39}\,10^{-14}.
$$

At $x_0$, (14.12) makes $CDF(x_0)$ invertible, as is seen from the convergent series for $(I-(I-CDF(x_0)))^{-1}$. Since these are square matrices, $C$ is nonsingular. Hence $CF(x_*)=0$ is equivalent to $F(x_*)=0$. Every zero of $F$ in $X$ is a fixed point of $G$, proving the asserted uniqueness within $X$.

For completeness the projections and terminal separations use the same endpoint rules, on $X'=\{x:\|x-x_0\|_\infty\le2\cdot10^{-14}\}$ or on $X$ as indicated:

$$
\begin{array}{c|c|c}
\text{function}&\text{box}&\text{strict containing interval}\\ \hline
Y_1&X'&(29286821500/10^9,\ 29286821501/10^9)\\
V_1&X'&(-45328098035/10^9,\ -45328098033/10^9)\\
R_1,\ R_2&X&(-22,-21)\\
R_3&X&(-10,-9)\\
S_1,\ S_3&X&(-41,-40)\\
S_2&X&(-42,-41).
\end{array}                                                       \tag{14.14}
$$

Each entry follows by substituting the coordinate endpoints in (13.1)–(13.3) with (14.3); no equality of responses is inferred from these containing intervals. Estimate (14.8) places $x_*$ in $X'$, so the first two rows imply (14.9). The equalities themselves are the exact equations $F(x_*)=0$. ∎

## 15. 一个精确父历史的五目标失败族

**定理 15.1（三目标实际子历史与五目标同父障碍）。** Use the exact limit $x_*$ of Theorem 14.2, and let

$$
\begin{gathered}
W_i=(P(\alpha_{i*},\beta_{i*}),f_i,d_{i*})\quad(1\le i\le3),
\qquad \mathcal T=\{W_1,W_2,W_3\},\\
y_*=Y_1(x_*),\qquad v_*=V_1(x_*),\qquad
\mathcal K=\mathcal A_{y_*}\cup\mathcal T,
\end{gathered}                                                     \tag{15.1}
$$

where each $f_i$ is the single polynomial (13.1) at that coordinate triple, and $\mathcal A_{y_*}$ is exactly the already bound family (11.6), with complete targets (10.3). Then $y_*\in(144/5,156/5)$, all five elements of $\mathcal K$ are distinct legal complete targets, and

$$
\begin{gathered}
\mathcal K\subseteq\mathcal F((H_p(y_*),M,0)),\qquad
|\mathcal K|=5,\\
\mathcal T\subseteq\mathcal F((H_p(y_*),M,0,M,v_*)),\qquad
L_1(\mathcal T,(H_p(y_*),M,0,M,v_*)),\\
L_2(\mathcal K,(H_p(y_*),M,0)),\qquad
L_3(\mathcal K,H_p(y_*)).
\end{gathered}                                                     \tag{15.2}
$$

In the displayed $L_1$ child, the final-$J$ collision pair is exactly $\{W_1,W_2\}$, and the final-$M$ collision pair is exactly $\{W_1,W_3\}$. In particular (15.2) obstructs every deterministic policy recovering this known five-target family from the stated parent within the remaining three original-clock readings, including policies with early stopping.

Proof. The source in (13.1) has four strictly positive entries, trace one and determinant zero. Its rank is therefore one, with no symmetry requirement. The exact cumulative matrices along clocks $0,\ldots,6$ for the literal word $JMMJMM$ are

$$
I,\quad J,\quad
\begin{pmatrix}1&0\\1&1\end{pmatrix},\quad
\begin{pmatrix}1&1\\2&1\end{pmatrix},\quad
\begin{pmatrix}2&1\\1&1\end{pmatrix},\quad
\begin{pmatrix}1&1\\3&2\end{pmatrix},\quad
\begin{pmatrix}3&2\\4&3\end{pmatrix}.                           \tag{15.3}
$$

Their traces against $P(\alpha,\beta)$ are respectively

$$
1,\quad j,\quad\ell,\quad j+\ell,\quad A,\quad B,\quad A+B.
                                                                  \tag{15.4}
$$

The two possible final matrices are, in final-$J$ and final-$M$ order,

$$
\begin{pmatrix}4&3\\3&2\end{pmatrix},\qquad
\begin{pmatrix}4&3\\7&5\end{pmatrix},
$$

with trace factors $2A+j$ and $A+2B$. Thus the response functions (13.3) are the actual fourth-$J$, fifth-$M$, sixth-$M$ and two final responses of the same fixed target. There is no change of source or gain between them.

Lagrange interpolation at original clocks $0,1,2,3$ gives (13.2); multiplying $q_i$ by the first four traces in (15.4) and adding the same drift gives exactly the readings $0,24,48,312/5$. Every $f_i$ has degree at most three and is nonzero: if it were zero, these four readings would all be its constant drift. The coordinate box gives

$$
d_{1*}\in(2,3),\qquad d_{2*}\in(4,5),\qquad d_{3*}\in(15,16),
                                                                  \tag{15.5}
$$

so the three complete targets are distinct. The single simultaneous equality $F(x_*)=0$ now gives

$$
\begin{gathered}
Y_1=Y_2=Y_3=y_*,\qquad Z_1=Z_2=Z_3=0,\\
V_1=V_2=V_3=v_*,\qquad R_1=R_2,\qquad S_1=S_3.
\end{gathered}                                                     \tag{15.6}
$$

Consequently all three worlds realize the entire history

$$
(0,J,24,M,48,M,312/5,J,y_*,M,0,M,v_*).
                                                                  \tag{15.7}
$$

The last four rows of (14.14) separate $R_3$ from $R_1=R_2$ and $S_2$ from $S_1=S_3$. For final $J$, the actual response $R_1$ retains exactly the two distinct targets $W_1,W_2$ in $\mathcal T$; for final $M$, response $S_1$ retains exactly $W_1,W_3$. Each child has $L_0$. This proves the $L_1$ assertion by the actual recursion (1.1), with different terminal collision pairs on this same $\mathcal T$.

For the complementary two worlds, (14.9) places $y_*$ in the second window of Theorem 11.1. To specify the roots more narrowly, put $t_*=5(y_*-12)/96$. Then $9/10<t_*<901/1000$. Direct endpoint operations on $t\in[9/10,901/1000]$ give the following containing intervals for the quadratic (10.1):

$$
\begin{array}{c|c}
\ell&\text{interval containing }Q_t(\ell)\\ \hline
4/3&[2666666/10^9,\ 9868445/10^9]\\
3/2&[-13250000/10^9,\ -4697750/10^9]\\
8/5&[-11200000/10^9,\ -1789440/10^9]\\
9/5&[19000000/10^9,\ 30235240/10^9].
\end{array}                                                       \tag{15.8}
$$

The positive leading coefficient and the two sign changes isolate one root $\ell_-$ in $(4/3,3/2)$ and the other $\ell_+$ in $(8/5,9/5)$. These are precisely the two roots used by $\mathcal A_{y_*}$ in (11.6). On both root intervals, $1<\ell<8/3$ and $0<t_*\ell-1<1$; hence the sources (10.3) are strictly positive, trace one and rank one. Their gains $8T(T-5)(T-7)/(5\ell)$ are nonzero cubics, and their drifts are zero. Their different $\ell$ values give different sources, and (15.5) separates both complete targets from $\mathcal T$. Thus $|\mathcal K|=5$.

Theorem 10.1 and Proposition 11.3 give these two worlds' whole parent history $H_p(y_*)$ and their following actual responses:

$$
\begin{array}{c|c|c|c|c}
E_5&E_6&z_5&z_6&z_7\text{ for either final atom}\\ \hline
J&J&0&-y_*/2&0\\
J&M&0&-126/5&0\\
M&J&0&48/5-y_*&0\\
M&M&0&-156/5-48/(5\ell)&0.
\end{array}                                                       \tag{15.9}
$$

This uses exactly the same $y_*$ as (15.7). After fifth $M$, all five worlds have the actual response $0$. In this child, sixth $J$ has the response $48/5-y_*$ retaining $\mathcal A_{y_*}$ with $L_1$, whereas sixth $M$ has response $v_*$ retaining $\mathcal T$ with $L_1$. The pair alone has different sixth-$M$ responses, as is also explicit in (15.9); it is the jointly realized triple that supplies this second sixth-action clause. Lemma 9.3 and (1.1), or equivalently the finer gluing implication of Theorem 12.3, give $L_2(\mathcal K,(H_p(y_*),M,0))$.

At the parent, fifth $J$ has a response-$0$ child containing the same $\mathcal A_{y_*}$ with $L_2$, and fifth $M$ has the response-$0$ child $\mathcal K$ with the just established $L_2$. Applying (1.1) gives $L_3(\mathcal K,H_p(y_*))$. All inclusions concern fixed complete targets and their entire literal histories. Arbitrary discontinuous deterministic choices and early stopping are covered by that recursion. ∎

**推论 15.2（两种符号的输运与原根边界）。** For every $D_0\in\mathbb R$ and $\lambda\ne0$, set $Y_*=D_0+\lambda y_*$. The transported family $\Phi_{D_0,\lambda}(\mathcal K)$ has exactly five distinct complete targets at the parent $H_J(Y_*)$ of (5.1), and

$$
\begin{gathered}
L_1\bigl(\Phi_{D_0,\lambda}(\mathcal T),
(H_J(Y_*),M,D_0,M,D_0+\lambda v_*)\bigr),\\
L_2\bigl(\Phi_{D_0,\lambda}(\mathcal K),(H_J(Y_*),M,D_0)\bigr),\\
L_3\bigl(\Phi_{D_0,\lambda}(\mathcal K),H_J(Y_*)\bigr).
\end{gathered}                                                     \tag{15.10}
$$

The three failure predicates in (15.10) also hold on the respective whole compatible fibers by inclusion. They concern this one exact normalized $y_*$ and its affine images. An original-root lower bound additionally requires losing actual children for both actions throughout the necessary earlier histories, with one consistent realization along each selected path. A policy beginning at the original root need not reach $H_p(y_*)$ or any of these transported parents. Thus (15.2)–(15.10) do not settle the unrestricted eight-reading question of Open Problem 8.2, provide a nine-reading upper bound, or classify other $y$ values or all fifth-$M$ fibers.

Proof. Apply the bijection in Lemma 9.2 to each fixed target, each full history and each selected actual response in Theorem 15.1. Its inverse preserves target distinction and the recursion for either sign of $\lambda$; in particular the sixth-$J$ response after fifth $M$ is $D_0+\lambda(48/5-y_*)$, and the triple's sixth-$M$ response is $D_0+\lambda v_*$. The whole-fiber implications follow from Lemma 9.3. These applications start at the displayed parents and supply no losing children at earlier nodes, which is the remaining hypothesis needed for a conclusion at the original root. ∎

## 追加锚（本行以下为增补区）

## 16. 同一 JMM 祖先上的严格正圆锥曲线伴随点

**定义 16.1（共同射线类与固定五目标的记号）。** Retain the complete-target domain, original clocks, acquisition rules and failure recursion of Definition 1.1. Put

$$
\begin{gathered}
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix},\qquad
h(T)=T(T-5)(T-7),\\
H_2=(0,J,24,M,48),\qquad
H_3=(H_2,M,312/5),\qquad H_M=(H_3,M,252/5),\\
\mathscr R=\left\{R\in\mathbb R^{2\times2}:
R_{ij}>0,\ \operatorname{rank}R=1,\
\operatorname{tr}(JR)=1,\
\operatorname{tr}(LR)=8/5\right\},\\
\mathcal C=\left\{W(R)=
\left(\frac R{\operatorname{tr}R},(\operatorname{tr}R)h,0\right):
R\in\mathscr R\right\}.
\end{gathered}                                                     \tag{16.1}
$$

Thus $\mathcal C$ contains every source satisfying the two trace constraints, rather than a selected finite subset. Equivalently, writing $s=\operatorname{tr}R$ and $a=R_{11}$ gives

$$
\begin{gathered}
R(a,s)=
\begin{pmatrix}
a&8/5-s\\s-3/5&s-a
\end{pmatrix},\qquad
C(a,s)=a^2-as-s^2+\frac{11}5s-\frac{24}{25},\\
\mathscr R=
\left\{R(a,s):\frac35<s<\frac85,\quad 0<a<s,\quad C(a,s)=0\right\},
\qquad W(a,s)=\left(\frac{R(a,s)}s,sh,0\right).
\end{gathered}                                                     \tag{16.2}
$$

Indeed, the first trace constraint fixes the sum of the off-diagonal entries to $1$, and the second fixes $R_{11}+R_{12}+R_{22}=8/5$. These give exactly the entries in (16.2). Their determinant is $-C(a,s)$; positivity excludes rank zero and is equivalent to the displayed strict inequalities. The complete target determines $R$: the coefficient multiplying the fixed polynomial $h$ gives $\operatorname{tr}R$, and its normalized source then gives $R$. Hence $R\mapsto W(R)$ is injective.

Use exactly $x_*,y_*,\mathcal T$ and $\mathcal K$ of Theorems 14.2 and 15.1, and write

$$
\mathcal K_5=\mathcal K=\{U_-,U_+\}\cup\mathcal T,\qquad
U_\pm=W_{\ell_\pm}\in\mathcal A_{y_*},\qquad
\ell_-<\ell_+.
                                                                  \tag{16.3}
$$

The notation $W_{\ell}$ refers to (10.3), with $t=5(y_*-12)/96$. In particular $x_*$ is the limit (14.7), not a rounded solution of a new system, and $y_*=Y_1(x_*)$ is the same number used throughout Section 15. Every member of $\mathcal C$ is a complete legal target. Conversely, among worlds with the known promise $d=0$ and $g=\kappa h$, $\kappa\ne0$, compatibility with $H_2$ forces

$$
\kappa\operatorname{tr}(JP)=1,\qquad
\kappa\operatorname{tr}(LP)=8/5.
                                                                  \tag{16.4}
$$

Since $\operatorname{tr}(JP)>0$, one has $\kappa>0$; setting $R=\kappa P$ recovers precisely (16.1). This converse uses the stated gain and drift promise.

**定理 16.2（固定精确点的合法不同伴随世界）。** Set

$$
\begin{gathered}
t=\frac{5(y_*-12)}{96},\qquad q=\frac85t,\qquad
s_0=\frac8{5\ell_-},\qquad a_0=q-s_0,\\
a_1=\frac{66}5-13a_0-8s_0,\qquad
s_1=21a_0+13s_0-\frac{99}5,\qquad
B_{\rm new}=W(a_1,s_1).
\end{gathered}                                                     \tag{16.5}
$$

Then $B_{\rm new}$ is a legal complete target in $\mathcal C$ distinct from every member of $\mathcal K_5$. The affine map in (16.5) preserves $C(a,s)$ and $3a+2s$ and is an involution. At this particular point,

$$
\begin{gathered}
0.2810<a_1<0.2813,\qquad 1.1581<s_1<1.1585,\qquad
0.002<a_1-a_0<0.0025,\\
29.27<12(1+a_1+s_1)<29.28<y_*.
\end{gathered}                                                     \tag{16.6}
$$

Every terminating decimal in this section and the sections below denotes its exact rational value.

Proof. Multiplying the source $P_\ell$ of (10.3) by $s=8/(5\ell)$ gives $R(q-s,s)$, with $q=8t/5$. Direct substitution gives

$$
C(q-s,s)=s^2Q_t(\ell),\qquad s=\frac8{5\ell}.
                                                                  \tag{16.7}
$$

Thus $W(a_0,s_0)=U_-$ as a complete target, including its gain and drift.

For the root exchange, put $k=3a+2s$ and substitute $s=(k-3a)/2$. Then

$$
4C\left(a,\frac{k-3a}{2}\right)
=a^2+\left(4k-\frac{66}5\right)a
-k^2+\frac{22}5k-\frac{96}{25}.
                                                                  \tag{16.8}
$$

The replacement $a'=66/5-4k-a$ preserves this quadratic, and $s'=(k-3a')/2$ gives

$$
(a',s')=\left(\frac{66}5-13a-8s,\ 
21a+13s-\frac{99}5\right).
                                                                  \tag{16.9}
$$

It preserves $k$, applying it twice returns $(a,s)$, and (16.8) proves preservation of $C$ even at a tangency. Positivity and distinction for the point in (16.5) require separate bounds.

The projection (14.9) confines $y_*$ to $(29.286821,29.286822)$. On the closed interval with these endpoints, using $t=5(y-12)/96$ in the exact quadratic (10.1) gives

$$
\begin{array}{c|c}
\ell&\text{strict containing interval for }Q_t(\ell)\\ \hline
1.37728&(0.0000007397,\ 0.0000011329)\\
1.37730&(-0.0000017816,\ -0.0000013884)\\
1.6666&(-0.0000083124,\ -0.0000077913)\\
1.6667&(0.0000042928,\ 0.0000048139).
\end{array}                                                       \tag{16.10}
$$

These are rational endpoint comparisons under (14.3). For example each row encloses
$(t^2-3/8)\ell^2+(11/8-3t)\ell+1$ with the same fixed rational $\ell$ in that row. The leading coefficient is positive, and the signs locate its two roots as

$$
1.37728<\ell_-<1.37730,\qquad
1.6666<\ell_+<1.6667.
                                                                  \tag{16.11}
$$

There are no additional roots, and both intervals satisfy $1<\ell<8/3$ and $0<t\ell-1<1$ as in Theorem 11.1.

To bound (16.5), first retain the relation $a_0=q-s_0$ by using the equivalent formulas

$$
\begin{aligned}
a_1&=\frac{66}5-13q+5s_0,&
s_1&=21q-8s_0-\frac{99}5,\\
a_1-a_0&=\frac{66}5-14q+6s_0,&
a_1+s_1&=8q-3s_0-\frac{33}5.
\end{aligned}                                                     \tag{16.12}
$$

Substitution of (16.11) and (14.9), with reciprocal endpoints reversed for $s_0=8/(5\ell_-)$, yields the strict rational enclosures

$$
\begin{array}{c|c}
\text{quantity}&\text{containing interval}\\ \hline
a_1&(0.281075338,\ 0.281160770)\\
s_1&(1.158256452,\ 1.158393158)\\
a_1-a_0&(0.002200006,\ 0.002302390).
\end{array}                                                       \tag{16.13}
$$

The wider bounds in (16.6) follow. In particular, the four entries of $R(a_1,s_1)$ have the strict lower bounds

$$
a_1>0.2810,\quad \frac85-s_1>0.4415,\quad
s_1-\frac35>0.5581,\quad s_1-a_1>0.8768.
                                                                  \tag{16.14}
$$

Equations (16.7)–(16.9) give determinant zero; positivity gives rank one and positive trace $s_1$. Consequently $R(a_1,s_1)/s_1$ has trace one, $s_1h$ is a nonzero cubic, and $B_{\rm new}$ is legal.

Writing $q_1=a_1+s_1$, preservation of $3a+2s$ gives

$$
q_1-q=-\frac{a_1-a_0}{2}<0.
                                                                  \tag{16.15}
$$

Both old $U$ worlds have $a+s=q$ and fourth-$J$ reading $12(1+q)=y_*$. The new world's fourth-$J$ reading is $12(1+q_1)$: the fourth cumulative matrix is $I+JL$, whose trace against $R(a,s)$ is $1+a+s$. Equations (16.12)–(16.13) give the last line of (16.6), distinguishing the new world from both $U$ worlds. Its drift is zero, whereas (15.5) gives strictly positive drifts for all members of $\mathcal T$, so it differs from those three as well.

The root exchange used in (16.8) is Vieta's quadratic identity. Line-intersection involutions have established broader treatments, for example van der Kamp–McLaren–Quispel, *Generalised Manin transformations and QRT maps*, [Journal of Computational Dynamics 8, 183–211](https://doi.org/10.3934/jcd.2021009). Here a single conic and the single linear response $3a+2s$ suffice; no pencil, integrability or measure-preservation conclusion is used. The concrete positive point (16.5) and its history consumers below are the specific content of this construction. ∎

## 17. 三个完整参数盒的实际联合响应

**定义 17.1（两条实际延续的响应函数）。** Let $\mathcal B_i\subset\mathbb R^3$ be the projection of $X$ in (14.1) onto its $i$th triple $(\alpha_i,\beta_i,d_i)$, for $i=1,2,3$. Thus each coordinate interval has radius exactly $10^{-8}$ about the corresponding rational coordinate of $x_0$, without imposing $F=0$. For $\theta=(\alpha,\beta,d)\in\mathcal B_i$, use exactly the source, traces, samples and single interpolating gain of (13.1)–(13.2), and write $W(\theta)=(P(\alpha,\beta),f,d)$. Define

$$
\begin{aligned}
\sigma(\theta)&=d+q_3(a+j),\\
\zeta(\theta)&=d+f_4(2\ell-1),\\
\mu(\theta)&=d+f_4(j+2\ell).
\end{aligned}                                                     \tag{17.1}
$$

Here $a=1/(1+\alpha\beta)$ is the scalar from (13.1), distinct from the conic coordinate $R_{11}$ of (16.2). For any real pair $(\sigma,z)$ set

$$
\begin{gathered}
\widehat A=\frac{\sigma}{24}-1,\qquad
\widehat B=\frac z{12}-\frac85,\qquad
\widehat C=1-\widehat B,\qquad
\widehat D=\frac85-\widehat A-\widehat B,\\
\widehat R(\sigma,z)=
\begin{pmatrix}\widehat A&\widehat B\\\widehat C&\widehat D\end{pmatrix},
\qquad
\Delta(\sigma,z)=\widehat A\widehat D-\widehat B\widehat C.
\end{gathered}                                                     \tag{17.2}
$$

**定理 17.2（整盒合法性、分离与联合排除）。** Every $\theta\in\mathcal B_i$ gives a legal complete target realizing all of $H_3$. Its actual third-$J$ response at $H_2$ is $\sigma(\theta)$, its next fourth-$M$ response along that continuation is $\zeta(\theta)$, and its fourth-$M$ response at $H_3$ is $\mu(\theta)$. Throughout each entire box,

$$
\begin{array}{c|c|c|c|c}
i&\sigma(\mathcal B_i)&\zeta(\mathcal B_i)&
\mu(\mathcal B_i)&d(\mathcal B_i)\\ \hline
1&(35.488,35.489)&(29.350,29.352)&(50.787,50.789)&(2,3)\\
2&(38.332,38.333)&(31.381,31.383)&(50.345,50.347)&(4,5)\\
3&(35.469,35.471)&(35.566,35.569)&(48.338,48.341)&(15,16).
\end{array}                                                       \tag{17.3}
$$

For the same joint response pair $(\sigma(\theta),\zeta(\theta))$, the strict exclusion bounds are

$$
\begin{array}{c|c}
i&\text{quantity evaluated on }\mathcal B_i\\ \hline
1&0.001486462<\Delta<0.001488988\\
2&-0.015170242<\widehat C<-0.015168132<-15/1000\\
3&-0.363958637<\widehat C<-0.363957400<-36/100.
\end{array}                                                       \tag{17.4}
$$

In particular the first row gives $1/1000<\Delta<2/1000$ on the whole first box.

Proof. The boxes have $\alpha,\beta>0$. The matrix (13.1) is therefore strictly entrywise positive, has trace one and determinant zero, and has rank one. Its positive traces at clocks $0,1,2,3$ are $(1,j,\ell,j+\ell)$. The polynomial (13.1) interpolates the four prescribed gain values there, so these readings, with the same drift $d$, are $0,24,48,312/5$. Those readings are unequal, hence the polynomial cannot be zero. This proves legality throughout the boxes without using $F=0$.

At $H_2$ the cumulative matrix is $L$. Choosing third $J$ and then fourth $M$ gives

$$
JL=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
MJL=\begin{pmatrix}1&0\\2&1\end{pmatrix}.
                                                                  \tag{17.5}
$$

Their traces against $P(\alpha,\beta)$ are $a+j$ and $2\ell-1$. The gain values at the actual clocks are $q_3$ and $f_4$, giving $\sigma$ and $\zeta$. On the other continuation, third $M$ followed by fourth $M$ has fourth matrix

$$
D=J+2L=\begin{pmatrix}2&1\\3&2\end{pmatrix},
                                                                  \tag{17.6}
$$

with trace $j+2\ell$, giving $\mu$. These are alternative response functions of the same fixed world. Acquiring $\sigma,\zeta$ uses just the chosen $J,M$ continuation; it does not acquire $\mu$.

For completeness, all bounds (17.3)–(17.4) follow from rational endpoint operations (14.3) on the three coordinate intervals in each $\mathcal B_i$. The expressions to substitute are

$$
\begin{gathered}
H=1+\alpha\beta,\quad
a=H^{-1},\quad j=(\alpha+\beta)/H,\quad \ell=1+\beta/H,\\
q_0=-d,\quad q_1=(24-d)/j,\quad
q_2=(48-d)/\ell,\quad
q_3=(312/5-d)/(j+\ell),\\
f_4=-q_0+4q_1-6q_2+4q_3,\\
\sigma=d+q_3(a+j),\quad
\zeta=d+f_4(2\ell-1),\quad
\mu=d+f_4(j+2\ell).
\end{gathered}                                                     \tag{17.7}
$$

All reciprocal denominators have strictly positive interval lower endpoints. Substitute the resulting rational intervals for $\sigma,\zeta$ into (17.2), before rounding them outward to (17.3). The comparisons with the rational endpoints in (17.4) are strict. Thus (17.4) encloses the compositions $\Delta\circ(\sigma,\zeta)$ and $\widehat C\circ(\sigma,\zeta)$ on the original parameter boxes; it is not inferred from the coarser printed marginal intervals alone. In particular these are bounds for every point of the radius-$10^{-8}$ boxes, rather than only for $x_*$ or a finite sample. ∎

## 18. 六目标的实际 H3 障碍与更早 J 分支

**定理 18.1（六目标 L4 与固定 K5 的一次最少增补）。** Define the single fixed family

$$
\mathcal K_6=\mathcal K_5\cup\{B_{\rm new}\},\qquad
\mathcal C_3=\{U_-,U_+,B_{\rm new}\}.
                                                                  \tag{18.1}
$$

It has exactly six distinct complete legal targets and satisfies

$$
\begin{gathered}
\mathcal K_6\subseteq\mathcal F(H_3),\qquad
L_3(\mathcal C_3,H_M),\qquad L_4(\mathcal K_6,H_3),\\
\neg L_4(\mathcal K_5,H_3).
\end{gathered}                                                     \tag{18.2}
$$

Consequently, among extensions of this fixed $\mathcal K_5$ by additional legal worlds at $H_3$, the minimum number of added worlds needed for $L_4$ is exactly one. This is a relative augmentation minimum, with $\mathcal K_5$ fixed.

Proof. Distinction and legality follow from Theorems 15.1 and 16.2. For every conic world (16.2), the cumulative matrices along $JMM$ are

$$
I,\quad J,\quad L,\quad J+L,
                                                                  \tag{18.3}
$$

and the values of the one fixed polynomial $h$ at clocks $0,\ldots,7$ are

$$
(0,24,30,24,12,0,-6,0).
                                                                  \tag{18.4}
$$

The two trace constraints therefore give exactly the entire ancestor history $H_3$. The fourth-$M$ matrix is $D$ of (17.6), with trace $21/5$ against $R$, so every conic world reads $252/5$ there. The fifth reading is zero for either action, and the seventh reading is zero for either action after any preceding choices.

After that fourth $M$, the complete sixth-response table, with fifth and sixth actions in chronological order, is

$$
\begin{array}{c|c|c|c|c}
E_5&E_6&A_6&z_6&z_7\text{ for either }E_7\\ \hline
M&M&\begin{pmatrix}5&3\\8&5\end{pmatrix}&-66&0\\
M&J&\begin{pmatrix}5&3\\3&2\end{pmatrix}
&-6(3+2s+3a)&0\\
J&M&\begin{pmatrix}2&1\\5&3\end{pmatrix}
&-6(37/5-s-a)&0\\
J&J&D&-126/5&0.
\end{array}                                                       \tag{18.5}
$$

Each matrix is $E_6E_5D$, and multiplying its trace against $R(a,s)$ by $h(6)=-6$ gives the displayed response. All fifth readings in this table are zero. The trace calculations use the same $R$ that gave (18.3), so the ancestor and descendant equalities hold jointly.

For fifth $M$, the actual response $0$ retains $\mathcal C_3$. Sixth $M$ then retains all three at $-66$, whereas sixth $J$ retains the distinct pair $\{U_-,B_{\rm new}\}$ because (16.9) preserves $3a+2s$. Each selected sixth child has at least two complete targets and both final readings equal zero. Lemma 9.3 gives $L_1$ in each selected sixth child, and (1.1) gives $L_2$ after fifth $M$.

For fifth $J$, the actual response is again $0$ on $\mathcal C_3$. Sixth $J$ retains all three at $-126/5$, whereas sixth $M$ retains $\{U_-,U_+\}$ because both have $a+s=q$. Again both final actions read zero on each retained pair. This gives $L_2$ after fifth $J$, and hence $L_3(\mathcal C_3,H_M)$. The two mixed-action rows use different collision pairs, within this one fixed three-target family.

At $H_3$, fourth $J$ with actual response $y_*$ retains exactly $\mathcal K_5$ in $\mathcal K_6$: Theorem 15.1 gives its common response and $L_3$, while (16.6) excludes $B_{\rm new}$. Fourth $M$ with actual response $252/5$ retains exactly $\mathcal C_3$: the three $\mu$ intervals in (17.3) exclude every $W_i$. Both actions therefore have an actual $L_3$ child of the same $\mathcal K_6$, proving $L_4$ by (1.1). Every selected node has at least two distinct complete targets, which includes the impossibility of a successful early stop.

To prove the relative minimum, consider one policy on the entire known $\mathcal K_5$ at $H_3$. Choose fourth $M$. By (17.3), each of its three $W_i$ responses is distinct from the other two and from $252/5$, so those children are singletons and permit immediate return of the corresponding whole target. In the response-$252/5$ child exactly $\{U_-,U_+\}$ remain. Choose fifth $M$, read $0$, and then sixth $J$. On this pair, (18.5) becomes

$$
z_6=-6(3+3q-s).
                                                                  \tag{18.6}
$$

The two $s=8/(5\ell_\pm)$ values are different, and this response is injective in $s$. The policy returns the complete target by original clock six, with at most three additional readings from $H_3$. Thus $\mathcal K_5$ cannot have $L_4$ there. Zero additions fail and the one addition in (18.1) succeeds, proving the stated minimum. No comparison with other possible initial supports is part of that minimum.

The abstract response-fiber recursion is (1.1), from [II, Definition 56.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md), and its monotonicity and same-parent uses are Lemma 9.3 and Theorems 12.2–12.3. The $J$ arm here is exactly the existing five-target construction of Section 15. The additional content is the strictly positive companion furnishing the concrete other arm at their earlier common ancestor. ∎

**定理 18.2（第三 J 的分离、条件强制与精确未决支臂）。** At $H_2$, one actual third-$J$ reading identifies every complete target of the known family $\mathcal K_6$. In particular,

$$
\neg L_1(\mathcal K_6,H_2),\qquad
\neg L_5(\mathcal K_6,H_2).
                                                                  \tag{18.7}
$$

For the whole unrestricted fiber $\mathcal F_2=\mathcal F(H_2)$, however, the exact reduction is

$$
\begin{aligned}
L_5(\mathcal F_2,H_2)
\quad\Longleftrightarrow\quad
\exists z\in\mathbb R:\ 
L_4\bigl(\mathcal F((H_2,J,z)),(H_2,J,z)\bigr).
\end{aligned}                                                     \tag{18.8}
$$

Every deterministic policy that succeeds on all of $\mathcal F_2$ within eight total readings must choose third $J$ at this reached history. For every $D_0\in\mathbb R$ and $\lambda\ne0$, the corresponding assertion holds at

$$
(D_0,J,D_0+24\lambda,M,D_0+48\lambda).
                                                                  \tag{18.9}
$$

Proof. The actual third-$J$ matrix is $JL$ of (17.5). For a conic world its response is $24(1+a)$, and for a member of $\mathcal T$ it is

$$
\sigma_i=d_{i*}
+(312/5-d_{i*})
\frac{1+\alpha_{i*}+\beta_{i*}}
{1+\alpha_{i*}+2\beta_{i*}+\alpha_{i*}\beta_{i*}}.
                                                                  \tag{18.10}
$$

The two conic-root intervals (16.11), the correlated companion bounds (16.12), and (17.3) give the pairwise disjoint strict intervals

$$
\begin{array}{c|c}
\text{world}&\text{third-}J\text{ response at }H_2\\ \hline
U_-&(30.69,30.70)\\
B_{\rm new}&(30.74,30.76)\\
W_3&(35.469,35.471)\\
W_1&(35.488,35.489)\\
U_+&(35.53,35.54)\\
W_2&(38.332,38.333).
\end{array}                                                       \tag{18.11}
$$

Thus the acquired response singles out a target in this known six-element family. The same policy also fits every larger remaining horizon, proving (18.7).

In contrast, $\mathcal F_2$ contains the six distinct targets, so it cannot be decoded by stopping at $H_2$. If a policy chooses third $M$, its actual response $312/5$ can leave all of $\mathcal K_6$ at $H_3$. By Theorem 18.1 and same-history monotonicity, this entire third-$M$ child has $L_4$. At original clock three there are exactly four remaining reads through clock seven, so that choice cannot guarantee success on $\mathcal F_2$ with eight total readings.

The cardinality and third-$M$ clauses of the defining recursion for $L_5(\mathcal F_2,H_2)$ are therefore supplied by this concrete construction. Its only remaining clause is exactly the third-$J$ alternative on the right of (18.8). This proves both directions of that equivalence. Lemma 9.2 transports it and the action necessity for either sign of $\lambda$ in (18.9); the obstructing third-$M$ response becomes $D_0+312\lambda/5$. Equivalently, at $(a,J,b,M,2b-a)$ with $b\ne a$, take $D_0=a$ and $\lambda=(b-a)/24$.

The existence assertion on the right of (18.8) remains unresolved. Formula (18.11) shows that $\mathcal K_6$ cannot supply it. The necessity of third $J$ is conditional on reaching (18.9) and on requiring success for its entire fiber; there is no claim that a root policy must reach that history. The case $b=a$ is outside the nonzero-scale transport.

For clarity, along this particular ancestor chain a sufficient route to the original-root lower bound would require all three further existence assertions

$$
\begin{gathered}
\exists z_3:\quad
L_4\bigl(\mathcal F((H_2,J,z_3)),(H_2,J,z_3)\bigr),\\
H_1=(0,J,24),\qquad
\exists z_2:\quad
L_5\bigl(\mathcal F((H_1,J,z_2)),(H_1,J,z_2)\bigr),\\
\exists z_1:\quad
L_6\bigl(\mathcal F((0,M,z_1)),(0,M,z_1)\bigr).
\end{gathered}                                                     \tag{18.12}
$$

If the first held, (18.8) would give $L_5$ at $H_2$. With the second, the actual second-$M$ response $48$ and second-$J$ response $z_2$ would give $L_6$ at $H_1$. With the third, the actual first-$J$ response $24$ and first-$M$ response $z_1$ would give $L_7$ at the initial history $(0)$. None of the three assertions in (18.12) is established here, and this chain is not asserted to be necessary for every possible root proof.

In the terminology of Open Problem 8.2 and [IV, Theorem 9.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md), the unrestricted root eight-versus-at-least-nine question remains unresolved. Neither a root lower bound nor an unrestricted eight-read decoder nor a nine-read upper bound follows from this reached-history obstruction. ∎

## 19. 整个已知无限类的恰两读完整目标逆

**定理 19.1（整条正源曲线并三目标的精确逆与最少读数）。** Let

$$
\mathcal E=\mathcal C\cup\mathcal T,
                                                                  \tag{19.1}
$$

with $\mathcal C$ the entire class (16.1) and $\mathcal T$ exactly the three fixed targets of (15.1). At $H_2$, the minimum remaining deterministic reading count on this known class is exactly two. One policy takes third $J$, immediately reads $\sigma$, takes fourth $M$, immediately reads $z$, and recovers the whole target by original clock four.

More generally, for every selection $\theta_i\in\mathcal B_i$, $i=1,2,3$, the same minimum and an inverse of the same form hold for the known class

$$
\mathcal E_{\theta_1,\theta_2,\theta_3}
=\mathcal C\cup\{W(\theta_1),W(\theta_2),W(\theta_3)\}.
                                                                  \tag{19.2}
$$

The selected triples are part of the known class; they are not additional unknown continuously varying parameters promised only to lie in the boxes. All of these classes contain the entire infinite $\mathcal C$.

Proof. For $R\in\mathscr R$ write

$$
R=\begin{pmatrix}A_0&B_0\\C_0&D_0'\end{pmatrix},\qquad
C_0=1-B_0,\qquad D_0'=\frac85-A_0-B_0.
                                                                  \tag{19.3}
$$

The two actual cumulative matrices are exactly (17.5), and $h(3)=24$, $h(4)=12$. Thus

$$
\sigma=24(1+A_0),\qquad z=12(8/5+B_0).
                                                                  \tag{19.4}
$$

Both multipliers are nonzero known rational numbers. Consequently (17.2) reconstructs the entire $R$, and hence the entire target

$$
\left(\frac{\widehat R}{\operatorname{tr}\widehat R},
(\operatorname{tr}\widehat R)h,\ 0\right).
                                                                  \tag{19.5}
$$

In the conic coordinates this is equivalently

$$
a=\frac{\sigma}{24}-1,\qquad
s=\frac{16}5-\frac z{12},\qquad W=W(a,s).
                                                                  \tag{19.6}
$$

This proves injectivity of the two-read response on every member of $\mathcal C$, including every legal branch of the conic. For example the pairs $\mathcal A_y$ for all $y$ in the open windows (11.2) belong to $\mathcal C$, and different $y$ give different fourth-$J$ responses. Thus $\mathcal C$ is indeed infinite.

Its exact joint response image can be expressed without a parametrization: a real pair $(\sigma,z)$ arises from $\mathcal C$ if and only if all four entries of $\widehat R(\sigma,z)$ are strictly positive and $\Delta(\sigma,z)=0$. For the reverse implication, these conditions give a positive rank-one matrix whose two trace constraints in (16.1) hold by (17.2); (19.4) then gives exactly the prescribed pair. Its trace is positive, so (19.5) is legal. The determinant condition has the explicit polynomial form

$$
5(\sigma-24)(504-5\sigma-10z)
-4(5z-96)(156-5z)
=14400\,\Delta(\sigma,z)=0.
                                                                  \tag{19.7}
$$

This is a relation on the two responses of the same world. It retains strict source positivity, as required in addition to the polynomial equality.

Theorem 17.2 now separates the entire joint image of $\mathcal C$ from each extra world's response pair, uniformly for every allowed point of each box. On the first box, $\Delta>1/1000$ contradicts (19.7). On the second and third boxes, respectively $\widehat C<-15/1000$ and $\widehat C<-36/100$ contradict strict positivity of the reconstructed source. The three $\sigma$ intervals in (17.3) are pairwise disjoint, so the three selected extra worlds also have different joint responses. These exclusions concern the entire specified parameter boxes and the entire conic class, not separate marginal comparisons or finitely many conic targets.

For any fixed known selection in (19.2), denote its extra worlds' exact joint response pairs by
$(\sigma_i,\zeta_i)=(\sigma(\theta_i),\zeta(\theta_i))$. A complete policy on every reachable history of this known class is therefore

$$
\operatorname{Decode}(\sigma,z)=
\begin{cases}
W(\theta_i),&
(\sigma,z)=(\sigma_i,\zeta_i)\text{ for some }i,\\[2pt]
\displaystyle
\left(\frac{\widehat R(\sigma,z)}
{\operatorname{tr}\widehat R(\sigma,z)},
\bigl(\operatorname{tr}\widehat R(\sigma,z)\bigr)h,0\right),&
\text{otherwise}.
\end{cases}                                                       \tag{19.8}
$$

On reachable pairs the two cases are exclusive, the first index is unique, and the second case is guaranteed to have a legal positive rank-one reconstruction. Thus (19.8) is total on the known class. It may be extended arbitrarily on unreachable histories. The deterministic-policy model of Definition 1.1 requires no regularity or computability beyond dependence on the acquired history, so exact equality with these known response pairs is an allowed decision rule. For $\mathcal E$, the exact triples are those selected by the single inherited $x_*$ of Theorem 14.2, and (19.8) gives the asserted inverse without replacing them by decimal approximations.

Only the actual third-$J$ and fourth-$M$ responses are acquired. The already acquired readings at clocks $0,1,2$ remain $0,24,48$, and the gain samples used by the inverse are those at original clocks three and four. No response along the unchosen third-$M$ continuation, no reset and no independent experiment is used. Early singleton stops may be added but are unnecessary for the two-read upper bound.

To prove the matching lower bound, consider the two matrices

$$
R^{(1)}=
\begin{pmatrix}2/5&3/5\\2/5&3/5\end{pmatrix},\qquad
R^{(2)}=
\begin{pmatrix}2/5&4/5\\1/5&2/5\end{pmatrix}.
                                                                  \tag{19.9}
$$

Both have strictly positive entries, determinant zero, and satisfy $\operatorname{tr}(JR)=1$, $\operatorname{tr}(LR)=8/5$. They define distinct complete targets in $\mathcal C$ by injectivity in Definition 16.1; in particular their traces are $1$ and $4/5$. If the one chosen action at $H_2$ is third $M$, both read $312/5$, as does all of $\mathcal C$. If it is third $J$, both have $A_0=2/5$ and by (19.4) both read

$$
\sigma=24(1+2/5)=168/5.
                                                                  \tag{19.10}
$$

A deterministic policy sees the same literal $H_2$ on these two worlds, so it must choose the same action or the same immediate stop there. Stopping cannot distinguish them, and either possible single read leaves this collision. One remaining read is therefore insufficient even on $\mathcal C$. This proves the exact minimum two for every class (19.2), including (19.1), and includes all deterministic early stops.

In particular $\neg L_2(\mathcal E,H_2)$ and hence $\neg L_5(\mathcal E,H_2)$: after third $J$, every reachable response child is recovered by one fourth-$M$ read. Since $\mathcal K_6\subseteq\mathcal E$, closing the six-world support under all of $\mathcal C$ still does not realize the missing $JMJ$ alternative in (18.8). Membership in $\mathcal E$ is prior knowledge for this inverse. Neither $H_2$ nor the pair $(\sigma,z)$ certifies that membership for an unrestricted world in $\mathcal W_3$; the inverse therefore makes no claim of recovery on $\mathcal F(H_2)$.

The mathematical dependencies are precisely the positive normalization (1.2), the entire conic class (16.1), the actual-word traces (17.5), and the whole-box joint exclusions (17.4). The exact three-world definition and its existence are reused from (13.1), (14.7) and (15.1); no new nine-variable existence assertion is needed. The known gain-space inverse of [III, Theorem 4.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_III.md), the complementary-parent inverses of Theorems 5.2 and 6.1, and the unrestricted systems of [IV, Theorems 9.2–9.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md) retain their own domains. None is identified with the earlier actual history and promised class of this theorem.

For the literature correspondence, the scaling orbit in Li–Lee–Bresler, [Definition 2.7 and Theorem 2.8](https://arxiv.org/html/1501.06120v1), explains why positive trace normalization removes source/gain scale while leaving drift in the target. It supplies no prescribed-word reading threshold here. Whole-set discrimination in van den Bos–Vaandrager, [Theorem 6.1](https://arxiv.org/html/1907.11034v2), has finite suspension-automaton and injective-split hypotheses; those hypotheses are not transferred to this continuous class. Likewise the generic-linear-map quantifier in Breiding–Gesmundo–Michałek–Vannieuwenhoven, *Algebraic compressed sensing*, [Answer 9](https://arxiv.org/html/2108.13208v2), does not apply to the fixed $M/J$ words and their gain-weighted original-clock observations. Vieta exchange, interpolation, trace normalization, interval inclusion and the failure recursion are the reused methods. The concrete companion, its common-history six-world consumer, and this entire-known-class inverse with its joint exclusions are repo-derived calculations; no external priority assertion is made. The unrestricted root question remains the one stated in Open Problem 8.2. ∎

## 追加锚（本行以下为增补区）

## 20. JMJ 实际第四子历史的全部二目标分类

**定义 20.1（不受限 JMJ 父纤维与源坐标）。** Retain the complete-target domain $\mathcal W_3$, original clocks and immediate atomic readings of Definition 1.1. With the same $H_2$ as in Definition 16.1, put

$$
\begin{gathered}
H_z=(H_2,J,z)=(0,J,24,M,48,J,z),\qquad
\mathcal G_z=\mathcal F(H_z),\qquad z\in\mathbb R,\\
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix},\qquad
N=JL=\begin{pmatrix}1&1\\1&0\end{pmatrix}.
\end{gathered}                                                     \tag{20.1}
$$

Here $H_z$ ends at original clock three. Write the normalized source and its three trace coordinates as

$$
P=\begin{pmatrix}r&b\\c&1-r\end{pmatrix},\qquad
0<r<1,\quad b>0,\quad c=\frac{r(1-r)}b>0,\qquad
j=b+c,\quad \ell=1+b,\quad T=r+j.                              \tag{20.2}
$$

These coordinates cover every strictly positive rank-one trace-one source, without symmetry. Given $(r,b,d)$ with these strict inequalities and arbitrary $d\in\mathbb R$, let $g$ be the unique polynomial of degree at most three with

$$
(g(0),g(1),g(2),g(3))=
\left(-d,\frac{24-d}j,\frac{48-d}\ell,\frac{z-d}T\right).
                                                                  \tag{20.3}
$$

This is a bijective parametrization of $\mathcal G_z$: its source and drift recover $(r,b,d)$, and interpolation gives exactly the four original readings. The polynomial is nonzero because those readings are not all equal. Thus arbitrary signs, lower degrees, sampled zeros, repeated roots and drifts remain in this chart.

The following table records actual cumulative matrices and traces; each fifth row is conditional on its indicated fourth action:

$$
\begin{array}{c|c|c}
\text{clock and actions}&A_i&\operatorname{tr}(A_iP)\\ \hline
0&I&1\\
1:J&J&j\\
2:JM&L&\ell\\
3:JMJ&N&T\\
4:JMJJ&L&\ell\\
4:JMJM&L^2=2L-I&2\ell-1\\
5:JMJJJ&N&T\\
5:JMJJM&ML=J+L&j+\ell\\
5:JMJMJ&JL^2&2T-j\\
5:JMJMM&ML^2&T+2\ell-1.
\end{array}                                                       \tag{20.4}
$$

These are alternative response functions of one fixed complete target. Only the chosen action and its immediate reading are acquired.

**定理 20.2（第四 J 的唯一无序失败对与第四 M 的全域二目标排除）。** Set

$$
\mathcal I_{JMJ}=\left(\frac{144}5,\frac{216}5\right),\qquad
\psi(t)=t(t-6)(t-7).
                                                                  \tag{20.5}
$$

For every $z\in\mathcal I_{JMJ}$ define

$$
\begin{gathered}
a=\frac z{36}-\frac45,\qquad
q_a(B)=B^2-\left(a+\frac45\right)B+\frac65a-a^2,\\
\Delta_a=5a^2-\frac{16}5a+\frac{16}{25},\qquad
B_\pm=\frac{a+4/5\ \pm\sqrt{\Delta_a}}2,\\
R_B=\begin{pmatrix}a&B\\4/5-B&6/5-a-B\end{pmatrix},\qquad
s_B=\operatorname{tr}R_B=\frac65-B,\\
W_B=\left(\frac{R_B}{s_B},s_B\psi,0\right),\qquad
\mathcal B_z=\{W_{B_-},W_{B_+}\}.
\end{gathered}                                                     \tag{20.6}
$$

The notation $\mathcal B_z$ concerns JMJ; it is separate from the JMMJ family $\mathcal A_y$ of Definition 11.2. For all real $z,v$ and every pair $K$ of distinct complete targets in $\mathcal F((H_z,J,v))$,

$$
L_3(K,(H_z,J,v))
\quad\Longleftrightarrow\quad
z\in\mathcal I_{JMJ},\quad v=\frac{144}5,\quad K=\mathcal B_z.
                                                                  \tag{20.7}
$$

For all real $z,v$, no pair of distinct targets in $\mathcal F((H_z,M,v))$ has $L_3$. Both statements begin with the unrestricted chart (20.2)–(20.3); the zero drift and cubic ray in (20.6) are forced conclusions. The theorem classifies two-target sets only.

Proof. We first obtain consequences shared by both fourth actions. For two targets, the recursion (1.1) says that $L_s$ holds exactly when their readings agree on every continuation prefix of length at most $s$: at each level a child with two targets must retain the same pair. This follows by induction on $s$, and includes every early stop. Inclusion monotonicity is already Lemma 9.3; it is not a principle extracting a losing pair from a larger family.

Use the terminal reconstruction inside Theorem 7.1, with the terminal clock specified here. If $Q$ is an invertible nonnegative cumulative matrix with no zero row, then $QP$ is strictly positive rank one. For

$$
X=g(n)QP=\begin{pmatrix}\alpha&\beta\\\gamma&\epsilon\end{pmatrix},
$$

the four terminal response functions for chronological two-action suffixes $MM,MJ,JM,JJ$ at clock $n$ are

$$
\begin{aligned}
\alpha+\beta+\gamma+2\epsilon+d,&\qquad
\alpha+\gamma+\epsilon+d,\\
\alpha+\beta+\epsilon+d,&\qquad
\alpha+\epsilon+d.
\end{aligned}                                                     \tag{20.8}
$$

Their differences recover $\beta,\gamma,\epsilon$. If $\epsilon\ne0$, rank one gives $\alpha=\beta\gamma/\epsilon$ and then $d$. If $\epsilon=0$, positivity of $(QP)_{22}$ forces $g(n)=0$, so $X=0$ and the common terminal value is $d$. Thus the four functions determine $X,d$, including negative and zero gains. For a common nonzero $X$, the trace of $Q^{-1}X=g(n)P$ recovers $g(n)$, then $P$. Shared readings at clocks $0,1,2,3$ and their positive trace factors then recover the same entire $g$ by (20.3).

Suppose a distinct pair has $L_3$ after its fourth action, whose matrix is $A_4=L$ or $L^2$. Equality of all four clock-six readings applies (20.8) with $Q=A_4,n=6$. A nonzero reconstructed $X$ would make the complete targets equal, so both sixth gains are zero and the drifts agree. Fixing fifth $J$ and applying (20.8) to the four clock-seven readings, with $Q=JA_4,n=7$, likewise forces both seventh gains to vanish. Consequently, for one common real $d$,

$$
\begin{gathered}
g_i(t)=(t-6)(t-7)\left(\beta_i t-\frac d{42}\right),\\
\begin{array}{c|ccccc}
t&1&2&3&4&5\\ \hline
g_i(t)&30\beta_i-5d/7&40\beta_i-10d/21&
36\beta_i-2d/7&24\beta_i-d/7&10\beta_i-d/21.
\end{array}
\end{gathered}                                                     \tag{20.9}
$$

No leading coefficient was presumed nonzero. This normal form includes quadratic gains and repeated sixth or seventh roots before further constraints are imposed.

The two $\beta_i$ must differ. Otherwise the common nonzero gain cannot vanish at both $2,4$, since it already vanishes at $6,7$. A nonzero sample at $2$ fixes $\ell$ through the shared ancestor; a nonzero sample at $4$ fixes it through either actual fourth trace in (20.4). If $g(5)\ne0$, the two common fifth responses in that table then fix $T,j$. If $g(5)=0$, the three roots $5,6,7$ force the samples at $1,2,3$ to be nonzero, so the ancestors already fix $j,\ell,T$. In either case (20.2) gives the same source and hence the same complete target, a contradiction. Thus $\beta_1\ne\beta_2$. Moreover

$$
d\notin\{24,48,z\},\qquad g_i(1)g_i(2)g_i(3)\ne0.             \tag{20.10}
$$

Indeed equality of $d$ with one of these readings would, by its positive trace, force both gains to vanish at that early clock. Its affine expression in (20.9) would force $\beta_1=\beta_2$.

For fourth $J$, the equal clock-two and clock-four responses imply

$$
0=g_1(2)g_2(4)-g_2(2)g_1(4)
  =\frac{40d}7(\beta_1-\beta_2).
                                                                  \tag{20.11}
$$

This cancellation uses only $\ell_i>0$, without division by either gain sample. Hence $d=0$. The clock-one reading then gives $\beta_i>0$. Put $R_i=\beta_iP_i$. The same original ancestor readings give

$$
\operatorname{tr}(JR_i)=\frac45,\qquad
\operatorname{tr}(LR_i)=\frac65,\qquad
\operatorname{tr}(NR_i)=\frac z{36}.
                                                                  \tag{20.12}
$$

Solving these linear equations yields exactly $R_B$ in (20.6), with $a=z/36-4/5$. Its determinant is $q_a(B)$. Distinct complete targets require distinct roots. Strict positivity gives $a>0$ and both roots in $(0,4/5)$, so

$$
q_a(4/5)=a(2/5-a)>0,
$$

which forces $0<a<2/5$, equivalently $z\in\mathcal I_{JMJ}$.

Conversely, for $0<a<2/5$ the discriminant satisfies

$$
\Delta_a=5\left(a-\frac8{25}\right)^2+\frac{16}{125}>0.
                                                                  \tag{20.13}
$$

Both endpoint values $q_a(0)=a(6/5-a)$ and $q_a(4/5)=a(2/5-a)$ are positive. The vertex $(a+4/5)/2$ lies in $(0,4/5)$ and has negative value $-\Delta_a/4$. Thus exactly two distinct roots lie inside that interval. Also $6/5-a-B>0$ there. Every entry of $R_B$ is strictly positive, its determinant is zero, and $s_B>0$, proving legality of both worlds. At $a=0$ the first diagonal entry is zero; at $a=2/5$ a root lies at $B=4/5$ and has zero entries. These endpoints do not yield a distinct strictly positive pair.

For each of these same worlds the complete response table is

$$
\begin{array}{c|c}
\text{actual prefix or next action}&\text{readings or response}\\ \hline
JMJJ&(0,24,48,z,144/5)\\
\text{fifth }J&5z/18\\
\text{fifth }M&20\\
\text{clock }6\text{ after either fifth action}&0\\
\text{clock }7\text{ after any fifth/sixth actions}&0.
\end{array}                                                       \tag{20.14}
$$

Here $\psi(0),\ldots,\psi(7)=(0,30,40,36,24,10,0,0)$; the fifth traces against $R_B$ are $a+4/5$ and $2$. In particular the actual fifth-$M$ matrix after fourth $J$ is $ML=J+L$, as in (20.4). These equalities prove $L_3$ at the stated fourth-$J$ child, and force its response $144/5$. The two roots exhaust every possible distinct pair, proving both directions of (20.7).

It remains to exclude fourth $M$. Suppose it had a distinct $L_3$ pair. Use (20.9)–(20.10) and put

$$
\begin{gathered}
x_i=g_i(2),\quad D=48-d,\quad C_1=24-d,\quad C_3=z-d,\quad
\pi=x_1x_2,\\
g_i(1)=\frac34x_i-\frac{5d}{14},\quad
g_i(3)=\frac9{10}x_i+\frac d7,\quad
g_i(4)=\frac35x_i+\frac d7,\quad
g_i(5)=\frac14x_i+\frac d{14}.
\end{gathered}                                                     \tag{20.15}
$$

Then $x_1\ne x_2$, $\ell_i=D/x_i>0$ and $\pi>0$. The case $D=0$ would force $x_1=x_2=0$ and has already been excluded. Equality of the actual fourth-$M$ reading gives

$$
\begin{aligned}
0&=\frac1{x_1-x_2}\left[
\left(\frac35x_1+\frac d7\right)\left(\frac{2D}{x_1}-1\right)
-\left(\frac35x_2+\frac d7\right)\left(\frac{2D}{x_2}-1\right)
\right]\\
&=-\frac35-\frac{2dD}{7\pi},\qquad
\pi=-\frac{10dD}{21}>0.
\end{aligned}                                                     \tag{20.16}
$$

Hence $d<0$ or $d>48$, so $dC_1<0$. On the other hand, $j_i=C_1/g_i(1)>0$ forces

$$
T_1=g_1(1)g_2(1)>0,\qquad T_3=g_1(3)g_2(3)\ne0.
$$

For affine numerator and denominator, the divided difference of $(px+q)/(ux+v)$ is $(pv-uq)/[(ux_1+v)(ux_2+v)]$. Applying it to (20.15), the divided differences of $g(5)/g(3)$, $g(5)/g(1)$ and $g(5)/x$ are respectively

$$
-\frac d{35T_3},\qquad -\frac d{7T_1},\qquad -\frac d{14\pi}.
                                                                  \tag{20.17}
$$

The two fifth trace factors after fourth $M$ are $T_i+2\ell_i-1$ and $2T_i-j_i$, where $T_i=C_3/g_i(3)$. Equality of fifth $M$, then of fifth $J$, gives respectively

$$
\begin{aligned}
0&=-\frac{dC_3}{35T_3}-\frac{dD}{7\pi}-\frac14,\\
0&=-\frac{2dC_3}{35T_3}+\frac{dC_1}{7T_1}.
\end{aligned}                                                     \tag{20.18}
$$

Substituting (20.16) in the first yields $dC_3/(35T_3)=1/20$. The second then yields $T_1=10dC_1/7<0$, contradicting $T_1>0$. Every divided denominator was proved nonzero in (20.10), (20.15)–(20.16). Neither $g(4)$ nor $g(5)$, a discriminant, a leading gain coefficient or an unproved minor was divided out. This proves the unrestricted fourth-$M$ pair exclusion. ∎

**例 20.3（同一有理对的全部实际后继）。** At $z_0=936/25$, (20.6) has $a=6/25$ and roots $B=8/25,18/25$. The two complete worlds are

$$
\begin{aligned}
W_1&=\left(\frac1{11}\begin{pmatrix}3&4\\6&8\end{pmatrix},
\frac{22}{25}\psi,0\right),\\
W_2&=\left(\frac16\begin{pmatrix}3&9\\1&3\end{pmatrix},
\frac{12}{25}\psi,0\right).
\end{aligned}                                                     \tag{20.19}
$$

Their positive unnormalized sources are $\frac1{25}(\begin{smallmatrix}6&8\\12&16\end{smallmatrix})$ and $\frac1{25}(\begin{smallmatrix}6&18\\2&6\end{smallmatrix})$, both of determinant zero. Both actual JMJJM reading arrays are

$$
(0,24,48,936/25,144/5,20).
                                                                  \tag{20.20}
$$

Fifth $J$ instead reads $52/5$ on both. Every sixth and seventh response is zero under every intervening choice, verifying all eight length-three suffixes of this same pair after fourth $J$. Their alternative fourth-$M$ responses are $912/25,1152/25$, respectively, since in general that response is $144/5+24B$. Thus this pair has $L_3$ after fourth $J$ and is separated by fourth $M$ at $H_{z_0}$; it is not an $L_4$ family at that parent.

## 21. 任意基数族的第四动作条件与完整联合第四图

**定理 21.1（同父条件等价、支持下界与三目标必要性）。** For every $z\in\mathcal I_{JMJ}$ and every family

$$
\mathcal B_z\subseteq K\subseteq\mathcal G_z
$$

of arbitrary cardinality,

$$
\begin{aligned}
L_4(K,H_z)\quad\Longleftrightarrow\quad
\exists v\in\mathbb R:\quad
L_3\bigl(K\cap\mathcal F((H_z,M,v)),(H_z,M,v)\bigr).
\end{aligned}                                                     \tag{21.1}
$$

In particular this is an equivalence for the whole unrestricted $\mathcal G_z$. Every fourth-$M$ $L_3$ child, for any real $z$, contains at least three distinct targets. An $L_4$ family containing $\mathcal B_z$ has at least four distinct targets. For any real $z$ and any $K\subseteq\mathcal G_z$ with $|K|\le3$,

$$
L_4(K,H_z)\ \Longrightarrow\
|K|=3\text{ and both fourth response functions are constant on }K.
                                                                  \tag{21.2}
$$

Any deterministic decoder succeeding on the whole $\mathcal G_z$ by clock seven, for $z\in\mathcal I_{JMJ}$, must choose fourth $M$ at this reached history.

Proof. The forward implication in (21.1) is the fourth-$M$ clause of (1.1). The fourth-$J$ response-$144/5$ child contains the same fixed $\mathcal B_z$ with $L_3$, by Theorem 20.2. Lemma 9.3 therefore supplies the fourth-$J$ clause for $K$, so the displayed fourth-$M$ clause also suffices. Equivalently, any fixed $\mathcal D\subseteq\mathcal F((H_z,M,v))$ with $L_3$ can be joined to $\mathcal B_z$ at this same $z$ to give $L_4$; this does not assert the existence of such a $\mathcal D$.

A losing fourth-$M$ child cannot be a singleton by (1.1), or a pair by Theorem 20.2. Its cardinality is therefore at least three. The two members of $\mathcal B_z$ have different fourth-$M$ predictions $144/5+24B_\pm$. Such a child contains at most one of them, and its union with $\mathcal B_z$ contains at least four distinct targets. This proves the support lower bound, including for infinite $K$.

If $|K|\le3$ and $L_4$ holds, its losing fourth-$M$ child must be all three targets, so that response is constant. A losing fourth-$J$ child of size two would have to be $\mathcal B_z$ by Theorem 20.2, contradicting constancy of fourth $M$. Therefore its fourth-$J$ losing child also contains all three, proving (21.2). This argument makes no assertion that an arbitrary larger losing family has a losing pair.

Finally a decoder cannot stop on a parent containing the two distinct worlds $\mathcal B_z$, and choosing fourth $J$ leaves their $L_3$ response child with only three reads left. Thus any successful whole-parent decoder must choose fourth $M$. Existence of that decoder is not proved by this necessary action. ∎

**定理 21.2（所有联合第四响应的充要图，包括相等响应）。** Fix arbitrary real $z,U,V$, denoting common fourth-$J$ and fourth-$M$ predictions by $U,V$. Put $C=2U-V$. All worlds in $\mathcal G_z$ with these two predictions are exactly the following filtered interpolants (20.3).

If $U\ne V$, choose $0<r<1$ and $d\in\mathbb R$ with

$$
C-d\ne0,\qquad b=\frac{V-U}{C-d}>0,
\qquad c=\frac{r(1-r)}b,\quad j=b+c,\quad \ell=1+b,\quad T=r+j,
                                                                  \tag{21.3}
$$

and impose the single remaining equation

$$
C-2d=\frac{4(24-d)}j-\frac{6(48-d)}\ell+\frac{4(z-d)}T.
                                                                  \tag{21.4}
$$

If $U=V$, set $d=U$, choose any $0<r<1,b>0$, define $c,j,\ell,T$ as above, and impose

$$
0=U+\frac{4(24-U)}j-\frac{6(48-U)}\ell+\frac{4(z-U)}T.
                                                                  \tag{21.5}
$$

The equal-response stratum has exactly $g(4)=0,d=U=V$. In the unequal-response stratum $g(4)=C-d$ has the sign of $V-U$; hence all its drifts satisfy $d<C$ for $V>U$, and $d>C$ for $V<U$.

Proof. For every one of the same worlds, the actual fourth matrices in (20.4) give

$$
\begin{gathered}
U=d+\ell g(4),\qquad V=d+(2\ell-1)g(4),\\
C=d+g(4),\qquad V-U=b\,g(4),\\
g(4)=d+\frac{4(24-d)}j-\frac{6(48-d)}\ell+\frac{4(z-d)}T.
\end{gathered}                                                     \tag{21.6}
$$

The last identity is interpolation of the same polynomial (20.3), using the coefficient row $(-1,4,-6,4)$ at clock four. If $U\ne V$, $b>0$ forces $g(4)\ne0$, so (21.3) and (21.4) follow. Conversely these conditions give $g(4)=C-d$ and $b g(4)=V-U$. Substitution in the first line of (21.6) recovers exactly $U,V$. If $U=V$, positivity of $b$ forces $g(4)=0$ and $d=U$; the last line is exactly (21.5), and its converse is immediate by the same substitution. All source traces divided by here are positive. The interpolant is nonzero and reproduces all ancestors by Definition 20.1. Thus this is the complete joint fiber, including its zero-fourth-gain stratum. Membership in it supplies neither $L_4$ nor existence of a three-target losing family. ∎

The affine bijection of Lemma 9.2 transports (20.7), (21.1)–(21.6), and all actual responses for either sign of its nonzero scale. In particular at $(a_0,J,b_0,M,2b_0-a_0,J,c_0)$ with $b_0\ne a_0$, the normalized window is

$$
\frac65<\frac{c_0-a_0}{b_0-a_0}<\frac95.
                                                                  \tag{21.7}
$$

The fourth-$J$ witness response is $a_0+(144/5)(b_0-a_0)/24$. The case $b_0=a_0$ is outside this bijection. Transport preserves a reached history and its entire compatible fiber; it does not force a root policy to reach that history.

## 22. 指定 JMJJJJJ 八读的整个兼容世界集

**定理 22.1（含全部零层的充要生成式）。** Fix any real data

$$
\mathbf z=(0,24,48,z,u,w,x,y)
                                                                  \tag{22.1}
$$

at original clocks $0,\ldots,7$ for the prescribed seven-action word $JMJJJJJ$. Its cumulative matrices are

$$
(I,J,L,N,L,N,L,N).
                                                                  \tag{22.2}
$$

No action or reading is omitted. Define data quantities

$$
D_E=48+2u-3x,\qquad D_O=3z-2w-y,\qquad C_*=48+6u+x.
                                                                  \tag{22.3}
$$

The following construction gives exactly all compatible complete worlds. All displayed equalities and strict filters apply; a branch whose conditions fail contributes no world. Identical output triples are counted once. This is a solution-set parametrization and permits multiple compatible worlds.

First select the possible positive trace ratio $\rho=T/\ell$:

$$
\mathscr P(\mathbf z)=
\begin{cases}
\{D_O/D_E\}\cap(0,\infty),&D_E\ne0,\\
\varnothing,&D_E=0,\ D_O\ne0,\\
(0,\infty),&D_E=D_O=0.
\end{cases}                                                       \tag{22.4}
$$

For every selected $\rho$, use its appropriate branch below.

For $\rho=1$, let $Y\in\mathbb R[t]$, $\deg Y\le3$, interpolate

$$
(Y(2),Y(3),Y(4),Y(5))=(48,z,u,w).
$$

Require $Y(6)=x$, $Y(7)=y$, and set

$$
\ell=\frac{Y(1)-Y(0)}{24},\qquad 1<\ell<2.
                                                                  \tag{22.5}
$$

When these filters hold, this stratum contributes its one world

$$
P=\begin{pmatrix}\ell-1&\ell-1\\2-\ell&2-\ell\end{pmatrix},
\qquad d=\frac{Y(0)}{1-\ell},\qquad g=\frac{Y-d}{\ell}.
                                                                  \tag{22.6}
$$

For $\rho\ne1$, define the drift and interpolant

$$
\begin{gathered}
d=\frac{\rho C_*-4(z+w)}{8(\rho-1)},\\
(h(2),h(3),h(4),h(5))=
\left(48-d,\frac{z-d}\rho,u-d,\frac{w-d}\rho\right),
\qquad \deg h\le3,\\
h_0=h(0)=480+15u-25d-\frac{20z+4w-24d}\rho,\\
h_1=h(1)=192+4u-8d-\frac{6z+w-7d}\rho.
\end{gathered}                                                     \tag{22.7}
$$

There are exactly three reconstruction cases.

1. If $d\ne0$ and $h_1\ne0$, set

$$
\ell=-\frac{h_0}d,\quad j=\frac{\ell(24-d)}{h_1},\quad
r=\rho\ell-j,\quad b=\ell-1,\quad c=j-b.
                                                                  \tag{22.8}
$$

Require

$$
\ell>1,\quad j>0,\quad 0<r<1,\quad c>0,\quad
(\ell-1)c=r(1-r).
                                                                  \tag{22.9}
$$

Exactly when these filters hold, output the single world

$$
\left(\begin{pmatrix}r&\ell-1\\c&1-r\end{pmatrix},\frac h\ell,d\right).
                                                                  \tag{22.10}
$$

In particular $d=24,h_1\ne0$ fails $j>0$ and contributes no world.

2. If $d=0$, require $h_0=0$ and $h_1>0$. Set

$$
k=\frac{24}{h_1}>0,\qquad \gamma=\rho-k,
$$

and take every real root of

$$
(\gamma^2+k-1)\ell^2+(2-\rho)\ell-1=0.
                                                                  \tag{22.11}
$$

Keep exactly those roots satisfying

$$
\ell>1,\qquad 0<\gamma\ell<1,\qquad 1+(k-1)\ell>0.
                                                                  \tag{22.12}
$$

Each retained root gives

$$
P=\begin{pmatrix}
\gamma\ell&\ell-1\\1+(k-1)\ell&1-\gamma\ell
\end{pmatrix},\qquad g=h/\ell,\qquad d=0.
                                                                  \tag{22.13}
$$

3. If $d\ne0$ and $h_1=0$, require $d=24$ and

$$
\ell=-h_0/24>1.
$$

Take every real root $r$ of

$$
r^2-\ell r+(\ell-1)(\rho\ell-\ell+1)=0,
                                                                  \tag{22.14}
$$

keeping exactly those with

$$
0<r<1,\qquad c=\rho\ell-r-\ell+1>0.
                                                                  \tag{22.15}
$$

Each gives $P=(\begin{smallmatrix}r&\ell-1\\c&1-r\end{smallmatrix})$, $g=h/\ell$, $d=24$.

The inverse equations retain their full degree and root strata. For (22.11), write $A_2=\gamma^2+k-1$ and $A_1=2-\rho$. If $A_2\ne0$, use discriminant $A_1^2+4A_2$: negative gives no real roots, zero gives one repeated root, and positive gives two distinct real roots, each still subject to (22.12). If $A_2=0,A_1\ne0$, the sole candidate is $\ell=1/A_1$. If $A_2=A_1=0$, the equation is $-1=0$ and has no roots; it is never an identically zero equation. Equation (22.14) is monic, with discriminant

$$
\ell^2-4(\ell-1)(\rho\ell-\ell+1).
                                                                  \tag{22.16}
$$

Its negative, zero and positive signs give zero, one and two real candidates before the strict filters. A boundary root with a zero source entry is rejected; a repeated legal root yields one world. This root convention also covers empty legal-root sets when real roots exist but all fail positivity.

Proof. For any compatible world put $h=\ell g$. At even clocks $2,4,6$ the readings are $h(t)+d$; at odd clocks $3,5,7$ they are $\rho h(t)+d$. Thus the six successive values of $h$ at $2,\ldots,7$ must be

$$
48-d,\quad (z-d)/\rho,\quad u-d,\quad (w-d)/\rho,
\quad x-d,\quad (y-d)/\rho.
                                                                  \tag{22.17}
$$

A polynomial of degree at most three on these six successive nodes is characterized by its two vanishing fourth differences. Multiplying the first by $\rho$ and leaving the second in its denominator-cleared form gives

$$
\begin{aligned}
0&=\rho C_*-4(z+w)-8d(\rho-1),\\
0&=z+6w+y-4\rho(u+x)+8d(\rho-1).
\end{aligned}                                                     \tag{22.18}
$$

Their sum is $\rho D_E-D_O$. Therefore (22.4) is necessary. Conversely, for $\rho\ne1$, the selected ratio and drift formula make both equations (22.18) hold. Interpolation at $2,3,4,5$ then gives the required $h(6)=x-d$ from the first difference, and $h(7)=(y-d)/\rho$ from the second. The extrapolation coefficient rows at $0,1$, on those four nodes, are $(10,-20,15,-4)$ and $(4,-6,4,-1)$; they give exactly $h_0,h_1$ in (22.7). There is no leading-degree assumption on this interpolant.

The still unaccounted-for initial and first readings, and the definition of the trace ratio, are exactly

$$
h_0=-\ell d,\qquad jh_1=\ell(24-d),\qquad r+j=\rho\ell.
                                                                  \tag{22.19}
$$

If $dh_1\ne0$, these identities force (22.8); (22.9) is precisely strict positivity, trace one and determinant zero for its source. If $d=0$, (22.19) forces $h_0=0,h_1>0$, $j=k\ell$ and $r=\gamma\ell$. Substitution in $bc=r(1-r)$ gives (22.11), while the four strictly positive source entries are exactly (22.12). If $d\ne0,h_1=0$, the first-clock equation forces $d=24$; the initial equation fixes $\ell$, and $j=\rho\ell-r$ gives (22.14) and (22.15). This proves that the three cases exhaust all denominators, including $d=0,h_1=0$, which cannot satisfy the first-clock equation.

For $\rho=1$, $T=\ell$ implies $r+c=1$. Rank one gives $(r-b)(1-r)=0$, so strict positivity forces $b=r$, $c=1-r$, $j=1$, $\ell=1+r\in(1,2)$. All readings at clocks $2,\ldots,7$ are samples of $Y=\ell g+d$. Its initial and first equations are

$$
Y(0)=(1-\ell)d,\qquad Y(1)-Y(0)=24\ell.
                                                                  \tag{22.20}
$$

These force (22.5)–(22.6), as well as both later consistency checks. Conversely those checks and (22.20) recover all eight readings, including the first two, for the positive source in (22.6). No division by $\rho-1$ is used in this branch.

Finally every output in the $\rho\ne1$ branches has all four entries positive, trace one and determinant zero, hence rank one. Equations (22.19) give the initial and first readings; (22.17)–(22.18) give the other six. Thus the same entire polynomial $g=h/\ell$ works throughout the full word. In either ratio branch $g$ cannot be zero, since that would make the initial and first readings both equal the same $d$, contradicting $0\ne24$. This proves sufficiency as well as necessity. The only divisors used are positive source traces or the quantities explicitly separated as nonzero. ∎

Constant, linear, quadratic and cubic gains are all retained by degree-at-most-three interpolation. A zero sampled gain is not an illegal source and need not be removed; neither its sample nor a gain leading coefficient or discriminant is inverted. Repeated gain roots are also allowed. The tests $d=0$, $h_1=0$ and $\rho=1$ separate reconstruction equations, not a restriction to generic gains. In particular no nonzero-fourth, fifth, sixth or seventh-gain promise is hidden in Theorem 22.1.

## 23. 增益超平面、正则纤维及两类尖锐碰撞区域

**定理 23.1（正则纤维基数与退化层的全部比值）。** For a gain

$$
g(t)=a_0+a_1t+a_2t^2+a_3t^3,\qquad
\mathcal E(g)=a_1+9a_2+64a_3,
$$

every world compatible with (22.1) satisfies

$$
D_E=-8\ell\mathcal E(g),\qquad D_O=-8T\mathcal E(g).
                                                                  \tag{23.1}
$$

If $D_E\ne0$, the whole compatible eight-read fiber has at most two worlds. Its ratio $\rho=D_O/D_E$ is fixed. At $\rho=1$ it has at most one world. At $\rho\ne1$ it can have two only at the common drift $d=0$ or $d=24$, in the respective quadratic branches of Theorem 22.1. All other drifts give at most one world.

If $D_E=0,D_O\ne0$, the fiber is empty. If $D_E=D_O=0$, all compatible gains satisfy $\mathcal E(g)=0$, and the construction (22.4)–(22.16) must retain every $\rho>0$. This includes $\rho=1$, both exceptional drifts and every other drift, with all their zero and lower-degree intersections. There is no finite-cardinality assertion for this degenerate fiber and no assertion that different positive ratios cannot give the same data.

At the JMJ ancestors, the gain hyperplane has the equivalent positive-trace equation

$$
7d+\frac{25(24-d)}j-\frac{31(48-d)}\ell+\frac{13(z-d)}T=0,
                                                                  \tag{23.2}
$$

or, clearing only positive denominators,

$$
7dj\ell T+25(24-d)\ell T-31(48-d)jT+13(z-d)j\ell=0.
                                                                  \tag{23.3}
$$

These equations supplement the full-data conditions and source filters; they do not replace them.

Proof. Evaluating the monomials $1,t,t^2,t^3$ at the actual even clocks gives

$$
g(2)+2g(4)-3g(6)=-8\mathcal E(g).
$$

The odd clocks give $3g(3)-2g(5)-g(7)=-8\mathcal E(g)$. The drift cancels in both combinations, proving (23.1). Also direct interpolation on $0,1,2,3$ gives

$$
2\mathcal E(g)=-7g(0)+25g(1)-31g(2)+13g(3).
                                                                  \tag{23.4}
$$

Substitution of (20.3) proves (23.2)–(23.3). Since $\ell,T>0$, the zero-data alternatives follow. In the regular case $D_E\ne0$, Theorem 22.1 fixes the ratio, then either the unique $\rho=1$ candidate or the common $d,h$ for $\rho\ne1$. Only its two displayed non-identically-zero quadratic equations can contribute more than one world. At $d=24$, the $h_1\ne0$ branch fails $j>0$, so two worlds there necessarily have $h_1=0$ and share $\ell,g$. At $d=0$ they share $h=\ell g$. This proves the cardinality and drift claims. When both data quantities vanish, the necessary ratio equation is $0=0$, and the complete construction, with its remaining filters, is still over all positive ratios. ∎

**定理 23.2（正则零漂移碰撞的精确区域）。** In the regular stratum $D_E\ne0$, a two-world fiber at $d=0$ is equivalent to the zero-drift consistency conditions in Theorem 22.1 together with the following strict chamber. Put

$$
q=\frac{24}{h(1)},\qquad a=\rho-q,\qquad
\mathscr D=\rho^2-4a(1-a).
$$

The exact inequalities for two distinct legal worlds are

$$
0<\rho<1,\qquad 0<a<\rho/2,\qquad \mathscr D>0.
                                                                  \tag{23.5}
$$

Their explicit forms are

$$
\begin{gathered}
\sigma_\pm=1-\frac\rho2\ \pm\frac{\sqrt{\mathscr D}}2,\qquad
R_\sigma=\begin{pmatrix}a&1-\sigma\\q-1+\sigma&\sigma-a\end{pmatrix},\\
W_\sigma=\left(R_\sigma/\sigma,\sigma h,0\right).
\end{gathered}                                                     \tag{23.6}
$$

Equivalently, choose $\rho,a$ satisfying (23.5), put $q=\rho-a$, choose $z\in\mathbb R$, and interpolate the one polynomial $h$ from

$$
h(0)=0,\qquad h(1)=24/q,\qquad h(2)=48,\qquad h(3)=z/\rho,
                                                                  \tag{23.7}
$$

retaining $\mathcal E(h)\ne0$. The two worlds (23.6) give exactly a regular two-world fiber for their induced full word, with even readings $h(t)$ and odd readings $\rho h(t)$ at clocks $2,\ldots,7$. Each source has its second column strictly larger entrywise than its first.

Proof. In the zero-drift branch, $q=j/\ell>0$ and $a=r/\ell>0$. Set $\sigma=1/\ell$ and $R=P/\ell$. Its entries are exactly those in (23.6), with trace $\sigma$. Its determinant is

$$
F(\sigma)=\sigma^2+(\rho-2)\sigma+1-q-a^2.
                                                                  \tag{23.8}
$$

The exact legal interval is

$$
\max(0,1-q,a)<\sigma<1,
                                                                  \tag{23.9}
$$

and

$$
F(a)=(a-1)(\rho-1),\quad
F(1-q)=a(1-\rho),\quad F(1)=a(1-a).
                                                                  \tag{23.10}
$$

If two roots are legal, then $a<1$ and $F(a)>0$, forcing $\rho<1$; positivity already gives $\rho>0$. Now $1-q=1-\rho+a>a>0$, so it is the lower endpoint in (23.9). The vertex $1-\rho/2$ must lie above it, which is exactly $a<\rho/2$. The discriminant must be strictly positive and equals $\mathscr D$. These are all the inequalities in (23.5).

Conversely (23.5) puts the vertex strictly between $1-q$ and $1$, both endpoint values in (23.10) are positive, and the vertex value is $-\mathscr D/4<0$. Thus both distinct roots (23.6) lie in the legal interval. This proves sharpness and full positivity. Since $(R_\sigma)_{22}-(R_\sigma)_{21}=1-\rho>0$, positivity and rank one give the same strict column inequality in the first row. All original-clock readings follow by substitution of (23.7); regularity is $D_E=-8\mathcal E(h)\ne0$. Theorem 22.1 proves that these two roots exhaust the compatible fiber. Equality at a chamber boundary either fails the strict endpoint/vertex criterion or makes the roots coincide. It cannot supply two distinct legal worlds; the full filters still decide any remaining single root. ∎

**定理 23.3（正则漂移二十四碰撞的精确区域）。** In the regular stratum, a two-world fiber at drift $24$ is equivalent to the drift-$24$ consistency conditions in Theorem 22.1 together with

$$
1<\ell<2,\qquad
\ell<T<(\ell-1)+\frac{\ell^2}{4(\ell-1)}.
                                                                  \tag{23.11}
$$

Here $T=\rho\ell$ is common. Let $r_-<r_+$ be the two roots of

$$
Q(r)=r^2-\ell r+(\ell-1)(T-\ell+1).
                                                                  \tag{23.12}
$$

The two sources and their common gain are

$$
\begin{gathered}
P_r=\begin{pmatrix}r&\ell-1\\T-r-\ell+1&1-r\end{pmatrix},\\
g(0)=-24,\qquad g(1)=0,\qquad g(2)=24/\ell,\qquad
g(3)=(z-24)/T,\qquad \deg g\le3,
\end{gathered}                                                     \tag{23.13}
$$

with $\mathcal E(g)\ne0$. Conversely any $\ell,T,z$ satisfying these conditions gives exactly two compatible worlds for the induced eight-read word, at drift $24$. Here $\rho=T/\ell>1$, and each source's first column strictly dominates its second entrywise.

Proof. The reconstruction in (22.14) gives precisely (23.12). Two roots in $(0,1)$ have sum $\ell$, forcing $1<\ell<2$. The endpoint value

$$
Q(1)=(\ell-1)(T-\ell)>0
$$

forces $T>\ell$. The discriminant is positive exactly when $T<(\ell-1)+\ell^2/[4(\ell-1)]$. Conversely those bounds give a vertex $\ell/2\in(0,1)$ with negative value, while $Q(0),Q(1)>0$. Thus both distinct roots lie strictly in $(0,1)$. For each root the remaining entry is positive because

$$
T-r-\ell+1=\frac{r(1-r)}{\ell-1}>0.
$$

They therefore pass every source filter. The common gain (23.13) and equal traces $\ell,T$ give the full common word; its clock-one reading is $24$ despite the different $j=T-r$, since $g(1)=0$. Regularity and exhaustiveness follow from Theorems 22.1 and 23.1. Finally $r_++r_-=\ell$ and both roots below $1$ imply $r_\pm>\ell-1$; rank one gives the strict column dominance in the second row as well. At either non-strict $T$ boundary a root reaches a zero-entry boundary or the roots coincide. These cases cannot give a distinct legal pair, although a repeated legal root remains one world in Theorem 22.1. ∎

The chambers (23.5) and (23.11) concern regular data and the common interpolants specified above. Their inequalities alone are not consistency tests for arbitrary eight numbers; the full-data equations of Theorem 22.1 remain necessary. In the degenerate gain hyperplane, neither chamber nor the regular two-world bound removes the other ratios retained in (22.4).

## 24. 实际末次 M、完整词例与任意族的碰撞叶条件

**命题 24.1（同一时钟六历史的末次动作）。** At the clock-six prefix $JMJJJJ$, the matrix is $L$. The final-$J$ matrix is $N$, and the final-$M$ matrix is

$$
ML=J+L=\begin{pmatrix}1&1\\2&1\end{pmatrix}.
                                                                  \tag{24.1}
$$

For a regular zero-drift pair (23.6), final $M$ has the same reading on both worlds,

$$
z_7^M=h(7)(q+1),
                                                                  \tag{24.2}
$$

including $h(7)=0$. For a regular drift-$24$ pair (23.13),

$$
z_7^M(r)=24+g(7)(T-r+\ell),\qquad
z_7^M(r_+)-z_7^M(r_-)=-g(7)(r_+-r_-).
                                                                  \tag{24.3}
$$

Thus it splits that pair exactly when $g(7)\ne0$. If $g(7)=0$, both final actions read $24$ on this pair. In particular the zero-seventh-gain stratum is retained, rather than inferred away from regularity.

If a known family at this same clock-six history has $L_1$ and contains a regular drift-$24$ final-$J$ collision pair with $g(7)\ne0$, it must contain a target outside that pair. These assertions concern the indicated reached prefix, with no change of clock or gain.

Proof. The final-$M$ trace is $j+\ell$. In (23.6), $j=q\ell$ and $g=h/\ell$, giving (24.2). In (23.13), $j=T-r$ and the gain is common, giving (24.3). Both pairs already share their final-$J$ reading by construction. If the final-$M$ difference is nonzero, any losing final-$M$ child needs two distinct targets and contains at most one member of this pair, so it needs an outside target. If that difference is zero, the same pair survives both final choices and has $L_1$ at this clock-six history. This does not assert failure at an earlier node. ∎

**例 24.2（两个正则碰撞的全部八读）。** A zero-drift pair from (23.5) is

$$
\begin{gathered}
P_1=\begin{pmatrix}1/8&1/4\\7/16&7/8\end{pmatrix},\qquad
P_2=\begin{pmatrix}2/11&9/11\\2/11&9/11\end{pmatrix},\\
h(t)=\frac{24}{11}t(29-9t),\qquad
g_1=\frac45h,\quad g_2=\frac{11}{20}h,\quad d_1=d_2=0.
\end{gathered}                                                     \tag{24.4}
$$

The two positive trace-one sources have determinant zero. Their $\ell$ values are $5/4,20/11$, with common $q=11/20$, $\rho=13/20$, $a=1/10$. Their full JMJJJJJ arrays are both

$$
(0,24,48,468/55,-672/11,-1248/11,-3600/11,-18564/55).
                                                                  \tag{24.5}
$$

Here $D_E=9984/11\ne0$. On the same clock-six prefix, final $M$ instead reads $-44268/55$ on both, by (24.2).

A drift-$24$ pair from (23.11) is

$$
\begin{gathered}
P_+=\begin{pmatrix}7/10&1/5\\21/20&3/10\end{pmatrix},\qquad
P_-=\begin{pmatrix}1/2&1/5\\5/4&1/2\end{pmatrix},\\
g(t)=2(t-1)(12-t),\qquad d=24.
\end{gathered}                                                     \tag{24.6}
$$

Both sources are positive rank-one trace-one, with common $\ell=6/5$, $T=39/20$, $\rho=13/8$ and roots $r_+=7/10,r_-=1/2$ of (23.12). Their full JMJJJJJ arrays are both

$$
(0,24,48,471/5,408/5,666/5,96,141).
                                                                  \tag{24.7}
$$

Here $D_E=-384/5\ne0$. Actual final $M$ at the common clock-six prefix reads $171,183$, respectively. Their difference is $-12=-60(1/5)$, as (24.3) predicts. Each example uses one fixed source, one entire quadratic gain and one drift through every ancestor and descendant. A collision of this prescribed word is not a certificate of $L_4$ at $H_z$.

**定理 24.3（任意基数 L4 族的全 J 叶约束）。** Let $z\in\mathbb R$ and $K\subseteq\mathcal G_z$ have arbitrary cardinality. If $L_4(K,H_z)$, there exist actual successive responses $u,w,x,y$ along four further $J$ actions for which

$$
\left|K\cap\mathcal F((H_z,J,u,J,w,J,x,J,y))\right|\ge2.
                                                                  \tag{24.8}
$$

For that one full eight-read history, either $D_E=D_O=0$ and every compatible gain obeys (23.2)–(23.4), with the full positive-ratio construction of Theorem 22.1, or $D_E\ne0$ and its entire compatible fiber is exactly one of the two-world types (23.5) or (23.11). In the regular case $\rho=1$, or $d\notin\{0,24\}$, cannot support this leaf. The final-$M$ consequences of Proposition 24.1 apply at its same clock-six prefix.

Proof. Specify $J$ in the universal action clause of (1.1), successively four times. The corresponding actual children have $L_3,L_2,L_1,L_0$ on one nested sequence of literal histories, yielding (24.8). Only now, at this terminal leaf, may two targets be selected. Theorems 22.1 and 23.1 apply to its full compatible fiber. In the regular case that fiber has at most two worlds, so the two targets exhaust it and Theorems 23.2–23.3 give exactly its chamber. In the degenerate case both data combinations vanish and the full generator remains over every $\rho>0$. No cardinality bound is added there. This argument extracts a pair only at $L_0$, and does not assert that the pair had $L_3$ or $L_4$ at an earlier node. ∎

**约定 24.4（复用、文献对应与未决范围）。** The underlying complete-target domain and failure recursion are Definition 1.1; terminal rank-one reconstruction is the argument (7.1); inclusion monotonicity and affine transport are Lemmas 9.3 and 9.2. They are used within the concrete new JMJ classifications, not renamed as additional method theorems. The new mathematical content is the sharp unrestricted pair window and other-action exclusion, their whole-family and joint-fourth constraints, the complete prescribed-word solution set with all singular filters, and the two sharp regular collision chambers with actual final-$M$ behavior.

Interpolation, fourth differences, rank-one completion, quadratic root exchange and strict positive-real filtering are standard tools. The literature correspondences in Conventions 8.1 and Theorem 19.1 continue to apply: Li–Lee–Bresler, [Definition 2.7 and Theorem 2.8](https://arxiv.org/html/1501.06120v1), concern whole-fiber identifiability modulo a specified scaling orbit; here positive trace normalization removes that scale, while drift stays in the complete target. Van den Bos–Vaandrager, [Theorem 6.1](https://arxiv.org/html/1907.11034v2), has suspension-automaton, incompatible-state and injective-split hypotheses, which are not established for this continuous domain. Breiding–Gesmundo–Michałek–Vannieuwenhoven, [Answer 9](https://arxiv.org/html/2108.13208v2), treats generic linear maps, not these fixed original-clock words. The conic-involution analogy in Theorem 16.2 does not import pencil invariance or integrability. All concrete conditions used here are proved directly above; these applications carry no external priority or literature-completeness claim.

For $z\in\mathcal I_{JMJ}$, the unresolved other-action obligation in (21.1) is an actual fourth-$M$ $L_3$ family of at least three fixed complete targets sharing the entire same $H_z$, or a proof resolving all such children. Constructing such a family and joining it to $\mathcal B_z$ would supply an actual JMJ $L_4$ obstruction; it is not supplied here. For example $z=936/25$ gives the explicit J arm (20.19), but no common fourth-$M$ losing family is asserted there. A candidate $L_4$ family of exactly three worlds must have both fourth predictions constant and obey Theorem 21.2. That necessary joint chart is not its existence proof. Outside $\mathcal I_{JMJ}$ the J-arm pair disappears, while larger losing families remain undecided.

Theorem 22.1 enumerates every compatible world for one prescribed word, including nonunique and degenerate fibers. It does not provide a unique decoder on that word or on the whole unrestricted JMJ branch. Likewise the necessary action at a reached $H_z$ does not make that history inevitable for a policy starting at the original root. The earlier JJ and initial-M obligations in (18.12), the other unresolved local systems and bridges in Open Problems 4.2 and 8.2, and their original-root quantifiers remain unchanged. No actual JMJ $L_4$ family, unrestricted whole-branch inverse, unrestricted eight-read lower bound, nine-read upper bound or resolution of the original root question is established by Sections 20–24.

## 追加锚（本行以下为增补区）

## 25. 非平坦第一 J 历史的实际 JJ 五层障碍

**定理 25.1（第二 J 的不受限五层失败纤维）。** In the original complete-target domain $\mathcal W_3$ of Definition 1.1, put

$$
H^{JJ}=(0,J,24,J,192/5).
                                                                  \tag{25.1}
$$

There is a finite family $K\subseteq\mathcal F(H^{JJ})$ satisfying

$$
L_5(K,H^{JJ}),\qquad
L_5\bigl(\mathcal F(H^{JJ}),H^{JJ}\bigr).
                                                                  \tag{25.2}
$$

The five remaining reads are at original clocks $3,4,5,6,7$. The family is specified below by two distinct complete targets at each of the $32$ terminal words beginning $JJ$, with a single simultaneous assignment of all their shared ancestor responses. Repetition of a target at different terminal words is allowed. The ambient fiber retains all sources, gains and drifts of Definition 1.1; the choices made for these witnesses are not promises on a decoder's domain.

Proof. We first specify every complete world, and then compute its entire assigned history. Words are chronological: for $w=E_1\cdots E_7$, the cumulative matrix is $A_w=E_7\cdots E_1$.

For the terminal words beginning $JJJ$, use the two unit-$J$-signature source lines in [positive-trace/singular-source, Theorem 9.2](FIB_ORIGINAL_ROOT_POSITIVE_TRACE_GUARDS_AND_SINGULAR_SOURCES.md). Write

$$
P_*=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad
R_0=\begin{pmatrix}-1&-1\\1&1\end{pmatrix},\qquad
L_0=\begin{pmatrix}-1&1\\-1&1\end{pmatrix}.
                                                                  \tag{25.3}
$$

Both $P_*+uR_0$ and $P_*+uL_0$, for $|u|<1/2$, are strictly positive rank-one trace-one sources with $\operatorname{tr}(JP)=1$. Indeed, the first has equal columns, the second equal rows, and their diagonal entries sum to one. The two lines meet only at $P_*$.

For each such $w$ set

$$
\alpha_w=\operatorname{tr}(A_wR_0),\qquad
\beta_w=\operatorname{tr}(A_wL_0),\qquad
c_w=4(1+|\alpha_w|+|\beta_w|),
$$

and fix its two sources by

$$
(Q_{w,0},Q_{w,1})=
\begin{cases}
(P_*-R_0/4,\ P_*+R_0/4),&\alpha_w=0,\\
(P_*-L_0/4,\ P_*+L_0/4),&\alpha_w\ne0,\ \beta_w=0,\\
(P_*+(\beta_w/c_w)R_0,\ P_*+(\alpha_w/c_w)L_0),
  &\alpha_w\beta_w\ne0.
\end{cases}                                                       \tag{25.4}
$$

These sources are legal and distinct. In the last case both parameters are nonzero and have absolute value less than $1/4$, so the two sources lie away from the sole intersection of their lines. The first two cases use opposite nonzero parameters on one line. Trace linearity gives, in every case,

$$
\operatorname{tr}(A_wQ_{w,0})=\operatorname{tr}(A_wQ_{w,1}).
                                                                  \tag{25.5}
$$

For the last case the two increments from $\operatorname{tr}(A_wP_*)$ are both $\alpha_w\beta_w/c_w$; for the first two cases the relevant increment is zero.

For the other terminal words use two fixed transpose pairs:

$$
\begin{gathered}
P_{A,0}=\frac1{768}
\begin{pmatrix}
607&372+\sqrt{40657}\\
372-\sqrt{40657}&161
\end{pmatrix},
\qquad P_{A,1}=P_{A,0}^{\mathsf T},\\
P_{B,0}=
\begin{pmatrix}
9/10&(44+\sqrt{1207})/90\\
(44-\sqrt{1207})/90&1/10
\end{pmatrix},
\qquad P_{B,1}=P_{B,0}^{\mathsf T}.
\end{gathered}                                                     \tag{25.6}
$$

For the $A$ pair, $372^2-40657=97727=607\cdot161$ and $607+161=768$. For the $B$ pair, $44^2-1207=729$ and $729/90^2=9/100$. Thus all four sources have determinant zero and trace one. The square roots are strictly between zero and their respective off-diagonal centers, so all entries are positive and each transpose pair consists of different sources.

The three entire gains and constant drifts are

$$
\begin{array}{c|c|c}
X&h_X(t)&d_X\\ \hline
C&\dfrac25(t-4)(t-5)(t-6)&48\\
A&\dfrac{32}{125}(t-5)(t-6)(t-7)&1344/25\\
B&\dfrac3{10}(t-4)(t-6)(t-7)&252/5.
\end{array}                                                       \tag{25.7}
$$

Each gain is a nonzero cubic. For every seven-letter word beginning $JJ$ and $e\in\{0,1\}$, assign the fixed complete world

$$
W_{w,e}=
\begin{cases}
(Q_{w,e},h_C,d_C),&w\text{ begins }JJJ,\\
(P_{A,e},h_A,d_A),&w\text{ begins }JJMM,\\
(P_{B,e},h_B,d_B),&w\text{ begins }JJMJ.
\end{cases}                                                       \tag{25.8}
$$

These three disjoint cases exhaust all such words: after $JJ$, the third action is $J$, or it is $M$ and the fourth action is $M$ or $J$. There are respectively $32,16,16$ labelled slots, counting $e$. Every slot is a legal complete target, and the two slots at each terminal word have different sources, hence different complete targets. All sources, gains and drifts in (25.8) are fixed before any responses are considered.

The samples of the same gains (25.7), at the original clocks, are

$$
\begin{array}{c|rrrrrrrr}
i&0&1&2&3&4&5&6&7\\ \hline
h_C(i)&-48&-24&-48/5&-12/5&0&0&0&12/5\\
h_A(i)&-1344/25&-768/25&-384/25&-768/125&-192/125&0&0&0\\
h_B(i)&-252/5&-27&-12&-18/5&0&3/5&0&0.
\end{array}                                                       \tag{25.9}
$$

Every source has initial trace one. At clocks one and two along $JJ$, the cumulative matrices are $J,I$. Their $J$ traces are respectively $1,31/32,44/45$ for the $C,A,B$ sources. Substitution in (25.9) with the corresponding drift gives, for every slot,

$$
(z_0,z_1,z_2)=(0,24,192/5).
                                                                  \tag{25.10}
$$

For a word beginning $JJJ$, the clock-three matrix is $J$, so its response is $48-12/5=228/5$. Clocks four through six read $48$ for every descendant action sequence, because $h_C$ vanishes there. At the terminal word $w$, the two responses are equal by (25.5), with their common value $48+(12/5)\operatorname{tr}(A_wQ_{w,0})$. In particular, the choice of the terminal pair does not change any of its ancestor readings.

For both the $A$ and $B$ pairs the third action is $M$, and the clock-three matrix is $M$, since the first two $J$ actions have returned the cumulative matrix to $I$. Their trace factors are

$$
\begin{aligned}
\operatorname{tr}(MP_{A,e})&=\frac{31}{32}+\frac{161}{768}
                           =\frac{905}{768},\\
\operatorname{tr}(MP_{B,e})&=\frac{44}{45}+\frac1{10}
                           =\frac{97}{90}.
\end{aligned}                                                     \tag{25.11}
$$

Consequently both pairs give the same third response:

$$
\frac{1344}{25}-\frac{768}{125}\frac{905}{768}
=\frac{1163}{25}
=\frac{252}{5}-\frac{18}{5}\frac{97}{90}.
                                                                  \tag{25.12}
$$

This equality joins the two fourth-action arms at their entire common $JJM$ history.

In the $JJMM$ arm the clock-four matrix is $M^2=I+M$, with trace $1673/768$ on both $A$ sources. The fourth response is therefore

$$
\frac{1344}{25}-\frac{192}{125}\frac{1673}{768}
=\frac{25207}{500}.
                                                                  \tag{25.13}
$$

All three remaining gain samples vanish, so every fifth, sixth and seventh action reads $1344/25$ on this fixed pair.

In the $JJMJ$ arm the clock-four matrix is $JM$, and $h_B(4)=0$, so its response is $252/5$. For fifth $J$ the cumulative matrix is $J(JM)=M$; for fifth $M$ it is

$$
MJM=\begin{pmatrix}0&1\\1&2\end{pmatrix}.
$$

Their traces on either $B$ source are $97/90$ and $44/45+2/10=53/45$. Thus the two possible fifth responses are respectively

$$
\frac{252}{5}+\frac35\frac{97}{90}=\frac{7657}{150},
\qquad
\frac{252}{5}+\frac35\frac{53}{45}=\frac{3833}{75}.
                                                                  \tag{25.14}
$$

The sixth and seventh responses are $252/5$ for every continuation, since both clocks are roots of $h_B$. These calculations use chronological left multiplication throughout; all zero-gain positions still execute their chosen atom and acquire its immediate reading.

To make the simultaneous ancestor assignment explicit, let $v$ be a chronological prefix of length $k\ge3$ beginning $JJ$. The common response $z_v$ of every slot descending from $v$ is exactly the following:

$$
\begin{array}{c|c|c}
k&v&z_v\\ \hline
3&JJJ&228/5\\
4,5,6&JJJ\cdots&48\\
7&w\text{ beginning }JJJ&
  48+(12/5)\operatorname{tr}(A_wQ_{w,0})\\ \hline
3&JJM&1163/25\\
4&JJMM&25207/500\\
5,6,7&JJMM\cdots&1344/25\\ \hline
4&JJMJ&252/5\\
5&JJMJJ&7657/150\\
5&JJMJM&3833/75\\
6,7&JJMJ\cdots&252/5.
\end{array}                                                       \tag{25.15}
$$

Together with (25.10), this supplies a single literal history $H_v$ for each selected prefix. The table is a consequence of the fixed complete worlds (25.8), including every ancestor equation, rather than a collection of independently fitted terminal collisions.

For each prefix $v$ beginning $JJ$, with $2\le k=|v|\le7$, let

$$
K_v=\{W_{w,e}:v\text{ is a prefix of }w,\ e\in\{0,1\}\}.
                                                                  \tag{25.16}
$$

Then $K_v\subseteq\mathcal F(H_v)$. Every $K_v$ contains a distinct terminal pair, so $|K_v|\ge2$, even if some worlds at different leaves coincide. At a terminal word $w$, (25.5) or the root calculations show that the two distinct worlds realize the entire same $H_w$, giving $L_0(K_w,H_w)$.

Induct backwards from $k=7$. For $k<7$ and either action $E\in\{M,J\}$,

$$
K_{vE}\subseteq K_v\cap\mathcal F(H_v,E,z_{vE}),
\qquad H_{vE}=(H_v,E,z_{vE}).
                                                                  \tag{25.17}
$$

If $L_{6-k}(K_{vE},H_{vE})$ holds, inclusion monotonicity, Lemma 9.3, gives it on the full indicated response intersection of $K_v$. The two action clauses and $|K_v|\ge2$ give $L_{7-k}(K_v,H_v)$ by (1.1). This proves the induction, including both actions at every remaining node and every early stop. At $v=JJ$ it yields $L_5(K_{JJ},H^{JJ})$. Taking $K=K_{JJ}$ and applying Lemma 9.3 once more proves (25.2) on the entire unrestricted fiber. ∎

**推论 25.2（非平坦第一 J 的条件动作与充分链消费）。** For every $a,b\in\mathbb R$ with $b\ne a$, put

$$
c=a+\frac85(b-a),\qquad H^{JJ}_{a,b}=(a,J,b,J,c).
                                                                  \tag{25.18}
$$

Then $L_5(\mathcal F(H^{JJ}_{a,b}),H^{JJ}_{a,b})$. Every deterministic complete-target decoder that succeeds on the whole original domain within eight total readings must, if it reaches $(a,J,b)$ with $b\ne a$, continue with $M$.

In particular Theorem 25.1 supplies the second existential of (18.12), with $z_2=192/5$. If the first and third existentials of that sufficient chain also hold, then $L_7(\mathcal F((0)),(0))$ holds at the original initial history.

Proof. Apply Lemma 9.2 with $D_0=a$ and $\lambda=(b-a)/24\ne0$ to Theorem 25.1. Its second-$J$ response becomes

$$
a+\lambda\frac{192}{5}=a+\frac85(b-a)=c.
$$

The map is a bijection of the original domain, for either sign of $\lambda$, and carries whole compatible fibers and their $L_5$ predicates to the displayed history.

The reached first-$J$ history contains at least the two distinct targets of any transported terminal pair, so stopping there cannot succeed on its entire fiber. Choosing second $J$ has the actual response $c$ whose child has $L_5$. Three total reads have then been acquired, at clocks $0,1,2$, leaving exactly the five reads $3,\ldots,7$. Hence this action cannot guarantee complete-target recovery within eight total reads. The remaining legal action is $M$. This is a conditional action requirement, not a recovery assertion for that action.

For the sufficient-chain assertion, retain the literal histories $H_1=(0,J,24)$ and $H_2=(H_1,M,48)$ in (18.12). If its first existential holds, Theorem 18.2 gives $L_5(\mathcal F(H_2),H_2)$. Theorem 25.1 gives the other second-action $L_5$ child at the same $H_1$. Recursion (1.1) therefore gives $L_6(\mathcal F(H_1),H_1)$, with the stopping guard supplied by either child. If the initial-$M$ existential in (18.12) holds as well, it and this first-$J$ child give $L_7$ at $(0)$ by the same recursion. No assumption about inevitability of $H_1$ is used. ∎

**约定 25.3（来源对应与保留的原问题）。** The mathematical content of Theorem 25.1 is the joint legal realization (25.8)–(25.15) of the actual $JJ$ five-read obstruction. Its domain and target normalization are Definition 1.1 and [II, Definition 51.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md), originating in [the original volume, Sections 39 and 44](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md). Its finite-history recursion and inclusion step consume [II, Definition 56.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md) and Lemma 9.3. The unit-signature lines are supplied by positive-trace/singular-source Theorem 9.2; the source signatures and $J^2,M^2$ identities agree with [J-signature, Definition 2.1 and Proposition 2.2](FIB_ORIGINAL_ROOT_J_SIGNATURE_COUPLING_AND_HISTORY_FIBER_DECODER.md). The affine response correspondence is Lemma 9.2. These suppliers are used inside the construction and its policy consumer.

The original volume's Theorem 44.2 gives $n_{\rm det}(3,0)\ge8$, with a seven-total-read obstruction. [II, Lemma 49.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md) joins transpose and diagonal-flip arms at a $JJ$ history for quadratic gain and affine drift, again through clock six. Those results supply shared-history and source-difference methods; neither provides the clock-seven, constant-drift $L_5$ relation at (25.1). The present proof adds the simultaneous third-$M$ response matching and the terminal-pair family below third $J$ needed for that relation.

The literature-supplied correspondences remain those of Convention 24.4. Li–Lee–Bresler, [Definition 2.7 and Theorem 2.8](https://arxiv.org/html/1501.06120v1), concern identifiability modulo a specified transformation group; the two sources at each leaf here are already distinct after trace normalization. Van den Bos–Vaandrager, [Theorem 6.1](https://arxiv.org/html/1907.11034v2), assumes a suspension automaton with mutually incompatible distinct states and injective splits. Krieg–Novak–Ullrich, [Proposition 10 and its proof](https://arxiv.org/html/2406.07108v2), give a Bernstein-number error bound for a bounded linear target between Banach spaces and arbitrary input subsets; a concrete bound here would require the corresponding linear model and a suitable contained-ball estimate. The present proof invokes neither the automaton theorem nor the numerical width bound. Elementary trace linearity, source positivity, polynomial evaluation and finite-history induction are standard tools. The specific joint worlds and their $JJ$ consumer are repo-derived ordinary mathematics; no global originality, priority or exhaustive literature claim is made.

The second existential in (18.12), left unresolved in Convention 24.4, is supplied by (25.1)–(25.2). The first, actual $JMJ$ $L_4$ existential and the third, initial-$M$ $L_6$ existential remain open. The construction covers the $64$ labelled terminal slots whose words begin $JJ$; it supplies no worlds for the other $192$ slots in [IV, Theorem 13.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md), nor a full source tuple satisfying that theorem's common-kernel guards. The other local systems and bridges in Open Problems 4.2 and 8.2 retain their stated boundaries.

The nonflat condition $b\ne a$ is required for Corollary 25.2's transport. Neither it nor the source and gain choices in (25.8) restrict the original decoder domain, which still includes all gain signs, degree drops, sampled and repeated roots, arbitrary constant drifts and all strictly positive rank-one trace-one sources. The conditional choice of $M$ at a reached first-$J$ history does not assert that a root policy reaches such a history, or that its $M$ continuation succeeds. The sufficient chain (18.12) is not asserted necessary for every possible root proof. Original-root completion, the full-domain exclusion of eight-total-read decoders and a nine-read upper bound remain unresolved.

## 追加锚（本行以下为增补区）

## 26. Perron 时钟三根类的八读完整逆与初始 M 障碍排除

**定义 26.1（Perron 时钟三根类与实际八读）。** 沿用定义 1.1 的完整世界域 $\mathcal W_3$、矩阵 $M,J$、完整目标和字面历史纤维，以及 [II，定义 51.1、56.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md) 的原时钟与含早停递归。置

$$
\varphi=\frac{1+\sqrt5}{2},\qquad
\psi=-\frac1\varphi=1-\varphi,\qquad
N=1+\varphi^2,\qquad
O=\frac1{\sqrt N}
\begin{pmatrix}1&\varphi\\ \varphi&-1\end{pmatrix}.
\tag{26.1}
$$

定义子类

$$
\begin{aligned}
\mathcal R&=\{R\subseteq\{0,1,\ldots,7\}:|R|=3\},&
p_R(t)&=\prod_{r\in R}(t-r),\\
\mathcal C
&=\{(P,g,d)\in\mathcal W_3:
\operatorname{tr}(MP)=\varphi,\ 
g=c\,p_R,\ R\in\mathcal R,\ c\in\mathbb R\setminus\{0\},\
d\in\mathbb R\}.
\end{aligned}
\tag{26.2}
$$

这里 $R$ 含三个不同的原时钟，$\mathcal R$ 的全部 $\binom83=56$ 个成员均在定义内；$c$ 可取任意非零实数，$d$ 可取任意实数。每个固定世界在整条轨迹上始终使用同一个 $P$、同一个整个多项式 $g$ 和同一个 $d$。实际读数为

$$
A_0=I,\qquad A_i=E_iA_{i-1},\qquad
y_i=d+c\,p_R(i)\operatorname{tr}(A_iP).
\tag{26.3}
$$

初读计数；每个原子 $E_i\in\{M,J\}$ 后立即读取。原时钟为 $0,\ldots,7$，包括增益为零的时钟；不重置、不复制、不跳读、不作空动作读取，也不增加观测口。

$\mathcal C$ 是明确的承诺子类，不替换 $\mathcal W_3$。完整域仍容许所有严格正秩一迹一源、任意符号的非零三次及以下增益、次数下降、重根、非采样根和任意实常漂移。

**定理 26.2（两分路八读完整恢复及任意初始 M 支撑族的排除）。** 对 $\mathcal C$ 中每个完整目标，先在时钟一、二各作一次 $M$，取得 $y_0,y_1,y_2$，置

$$
a=y_1-y_0,\qquad b=y_2-y_0.
\tag{26.4}
$$

若 $a=b=0$，实际七动作词取 $MMJJJMM$；否则取 $MMJMMMM$。每条分路都在时钟七的立即读数后返回完整目标 $(P,g,d)$。漂移由下述实际前三读唯一确定：

$$
\begin{gathered}
a=0\ \Longrightarrow\ d=y_0,\\
a\ne0:\qquad \rho=b/a=x+y\varphi,\quad x,y\in\mathbb Q,\\
d=
\begin{cases}
y_0,&x=0,\\[2pt]
y_0+\displaystyle\frac{a}
 {1-\varphi(1+y-x)/x},&x\ne0.
\end{cases}
\end{gathered}
\tag{26.5}
$$

其中 $(x,y)$ 可由以下固定有限代数表与 $\rho$ 的精确相等比较取得：

$$
\mathscr T=
\left\{(x_R,y_R)\in\mathbb Q^2:
x_R+y_R\varphi=
\frac{\varphi^2p_R(2)-p_R(0)}
     {\varphi p_R(1)-p_R(0)},\
R\in\mathcal R,\
\varphi p_R(1)-p_R(0)\ne0\right\}.
\tag{26.6}
$$

表中同一个比值只对应一个有理坐标对，不要求从任意实数判定其是否属于 $\mathbb Q(\varphi)$。式 (26.5) 的所有实际除法、下述增益与源的逆均有非零分母。特别地，源双线的交点和任意接近严格正域边界的源都在恢复范围内；返回的是完整规范目标，不是进一步的商类。

同时，对任意 $a_0,a_1\in\mathbb R$，令 $H_1=(a_0,M,a_1)$。则

$$
\forall K\subseteq\mathcal C\cap\mathcal F(H_1),\qquad
\neg L_6(K,H_1).
\tag{26.7}
$$

因而在 (18.12) 的原初读 $a_0=0$ 上，任何支持其初始 $M$ 六层失败断言的候选族都必须含有 $\mathcal C$ 以外的完整世界；此结论对任意基数的候选族成立。

证明。$\varphi>1$、$N>0$，故式 (26.1) 的归一化分母均非零。先确定式 (26.2) 中整个源切片，而不预选其中一条直线。由 $\varphi^2=\varphi+1$、$\varphi\psi=-1$，直接相乘得

$$
O^{\mathsf T}O=I,\qquad
O^{\mathsf T}MO=
\begin{pmatrix}\varphi&0\\0&\psi\end{pmatrix},\qquad
O^{\mathsf T}JO=\frac1{\sqrt5}
\begin{pmatrix}2&1\\1&-2\end{pmatrix}.
\tag{26.8}
$$

写 $P'=O^{\mathsf T}PO$。迹一与 $M$ 迹条件给

$$
P'_{11}+P'_{22}=1,\qquad
\varphi P'_{11}+\psi P'_{22}=\varphi.
$$

因为 $\varphi-\psi=\sqrt5\ne0$，必有 $P'_{11}=1$、$P'_{22}=0$。于是

$$
P'=\begin{pmatrix}1&\alpha\\ \beta&0\end{pmatrix},
\qquad
\det P'=-\alpha\beta=0.
\tag{26.9}
$$

秩一恰要求 $\alpha\beta=0$，因为左上项已经非零。若 $\beta=0$，变回原坐标得到

$$
P_R(s)=
\begin{pmatrix}
s&(1-s)/\varphi\\
\varphi s&1-s
\end{pmatrix},
\qquad
\alpha=\sqrt5\,s-\frac1\varphi.
\tag{26.10}
$$

若 $\alpha=0$，则得到 $P_L(s)=P_R(s)^{\mathsf T}$，且
$\beta=\sqrt5\,s-1/\varphi$。两种情形中严格逐项正都恰等价于 $0<s<1$，也恰等价于非固定谱坐标位于 $(-1/\varphi,\varphi)$。反之，这些区间中的每个矩阵均严格正、秩一、迹一且 $M$ 迹为 $\varphi$，故两条开线段穷尽整个合法源切片。两条谱坐标轴同时成立恰要求 $\alpha=\beta=0$，故两条源线段只在

$$
s_*=\frac1N=\frac{5-\sqrt5}{10},\qquad
\alpha=\beta=0,\qquad
P_*=\frac{uu^{\mathsf T}}N,\quad
u=\begin{pmatrix}1\\ \varphi\end{pmatrix}
\tag{26.11}
$$

相交。在 $s=0,1$ 有条目为零，故端点不属于严格正域。式 (26.9) 还对每个非负整数 $i$ 给出

$$
\operatorname{tr}(M^iP)=\varphi^i.
\tag{26.12}
$$

这一恒等式适用于两条直线及其交点。

接着只用实际前三读恢复漂移。暂记 $p=p_R$，并置
$\Delta=d-y_0=-c\,p(0)$。由 (26.12)，

$$
a=c\bigl(\varphi p(1)-p(0)\bigr),\qquad
b=c\bigl(\varphi^2p(2)-p(0)\bigr).
\tag{26.13}
$$

若 $a=0$，因 $c\ne0$，有 $\varphi p(1)=p(0)$。两个多项式取值都是整数，$\varphi$ 无理，故 $p(0)=p(1)=0$。因此 $d=y_0$；且此时 $b=0$ 当且仅当 $p(2)=0$。由于 $R$ 恰有三个不同元素，

$$
a=b=0\quad\Longleftrightarrow\quad R=\{0,1,2\}.
\tag{26.14}
$$

这也处理了 $a=0,b\ne0$ 的全部根集合，而未倒取 $a$。

现设 $a\ne0$。式 (26.13) 使 $\rho=b/a$ 属于 (26.6) 的表。$\mathbb Q(\varphi)$ 中每个元素唯一写成 $x+y\varphi$，所以该坐标对唯一。若 $0\in R$，则 $p(0)=0$，而 $a\ne0$ 使 $p(1)\ne0$；于是

$$
\rho=\varphi\,\frac{p(2)}{p(1)},\qquad x=0,\qquad\Delta=0.
\tag{26.15}
$$

若 $0\notin R$，定义有理数

$$
A=\frac{p(1)}{p(0)},\qquad B=\frac{p(2)}{p(0)}.
\tag{26.16}
$$

当 $1\in R$ 时 $A=0$，而 $B\le0$：根 $1$ 对该比值贡献 $-1$，其余根属于 $\{2,\ldots,7\}$，各贡献非负因子。若 $1\notin R$，按递增顺序写 $R=\{r_1,r_2,r_3\}$，则
$2\le r_1\le5$、$r_1<r_2\le6$、$r_2<r_3\le7$。因 $1-1/r$、$1-2/r$ 在 $r\ge2$ 上递增且非负，

$$
0<A=\prod_{r\in R}\left(1-\frac1r\right)
 \le\frac45\frac56\frac67=\frac47,\qquad
0\le B=\prod_{r\in R}\left(1-\frac2r\right)
 \le\frac35\frac46\frac57=\frac27.
\tag{26.17}
$$

两种情况均给 $A+B<1$。将

$$
(x+y\varphi)(\varphi A-1)=(\varphi+1)B-1
$$

中的常数和 $\varphi$ 系数分别比较，得到

$$
B=1-x+yA=(x+y)A-y,\qquad xA=1+y-x.
\tag{26.18}
$$

若 $x=0$，后一式强制 $y=-1$，前一式即 $B=1-A$，与 $A+B<1$ 矛盾。因此 $0\notin R$ 时 $x\ne0$，并且

$$
A=\frac{1+y-x}{x},\qquad
a=\Delta(1-\varphi A),\qquad
\Delta=\frac{a}{1-\varphi A}.
\tag{26.19}
$$

$1-\varphi A\ne0$，因为 $A$ 有理而 $1/\varphi$ 无理。式 (26.15)、(26.19) 证明 (26.5) 的完整分支和全部分母条件。任意 $d$ 已从差分中消去，任意非零实尺度 $c$ 已从比值中消去；没有正尺度或零漂移假设。

表 (26.6) 是有限集合，由 $\mathcal R$ 逐项用 $\varphi^2=\varphi+1$ 的域算术确定。真实的 $a\ne0$ 历史必命中其中一个比值；重复比值的有理坐标必相同。故式 (26.5) 仅使用有限多个已指定代数实数的精确相等比较。动作分路同样只检验实际等式 $y_1=y_2=y_0$。这属于定义 1.1 和 II 定义 51.1 所容许的集合意义下的精确确定性策略，不包含由任意可计算实数表示判定相等、有限精度恢复或数值稳定性的断言；在 $\mathcal C$ 不可达的历史上可任意延拓。

现在恢复根与增益。严格迹正性采用[正迹与奇异源，引理 3.1](FIB_ORIGINAL_ROOT_POSITIVE_TRACE_GUARDS_AND_SINGULAR_SOURCES.md)：每个实际 $A_i$ 均非负可逆，每行有正项，故 $A_iP$ 严格正且 $\operatorname{tr}(A_iP)>0$。因此，不论 $c$ 的符号如何，

$$
y_i=d\quad\Longleftrightarrow\quad p_R(i)=0
\quad\Longleftrightarrow\quad i\in R.
\tag{26.20}
$$

在漂移确定后，八个实际读数恰给

$$
R=\{i\in\{0,\ldots,7\}:y_i=d\}.
\tag{26.21}
$$

这里没有用未选动作的响应，也没有将零增益时钟删除。

先看非例外分路 $MMJMMMM$。由 (26.14)，$\{0,1,2\}$ 不全包含于 $R$，故可取其中不属于 $R$ 的最小指标 $j$。实际矩阵为 $A_j=M^j$，从而

$$
c=\frac{y_j-d}{\varphi^j p_R(j)},\qquad g(t)=c\,p_R(t).
\tag{26.22}
$$

分母非零，因为 $\varphi>0$ 且 $j\notin R$；分子也非零，由 (26.20) 得 $c\ne0$。这恢复整个多项式，而非只恢复若干样本。

为恢复源，在同一证明内写出所需的两个谱方程。对 $k\ge0$，由 (26.8)、(26.9) 直接相乘，

$$
\begin{aligned}
T_k(P)&=\operatorname{tr}(M^kJM^2P)\\
&=\frac{2\varphi^{k+2}}{\sqrt5}
 +U_k\alpha+V_k\beta,\\
U_k&=\frac{\varphi^2\psi^k}{\sqrt5},\qquad
V_k=\frac{\psi^2\varphi^k}{\sqrt5}.
\end{aligned}
\tag{26.23}
$$

对不同的 $k<\ell$，两个系数行的行列式是

$$
D_{k\ell}
=U_kV_\ell-U_\ell V_k
=\frac{\varphi^2\psi^2}{5}
 \bigl(\psi^k\varphi^\ell-\psi^\ell\varphi^k\bigr)\ne0.
\tag{26.24}
$$

确实，括号等于
$\varphi^{k+\ell}((\psi/\varphi)^k-(\psi/\varphi)^\ell)$；
$0<|\psi/\varphi|=\varphi^{-2}<1$，所以不同非负整数次幂不相同，且其余因子均非零。

非例外分路的每个 $i\ge3$ 有实际矩阵 $A_i=M^{i-3}JM^2$。五个时钟 $3,\ldots,7$ 至少有两个不在三元素集合 $R$ 内。取其中最小的两个 $i<j$，令 $k=i-3$、$\ell=j-3$，用真实非零增益取得

$$
t_k=\frac{y_i-d}{c\,p_R(i)}=T_k(P),\qquad
t_\ell=\frac{y_j-d}{c\,p_R(j)}=T_\ell(P),\qquad
q_h=t_h-\frac{2\varphi^{h+2}}{\sqrt5}\quad(h=k,\ell).
\tag{26.25}
$$

所有分母已由 $c\ne0$ 和 $i,j\notin R$ 保证非零。完整源的显式逆为

$$
\alpha=\frac{q_kV_\ell-q_\ell V_k}{D_{k\ell}},\qquad
\beta=\frac{U_kq_\ell-U_\ell q_k}{D_{k\ell}},\qquad
P=O\begin{pmatrix}1&\alpha\\ \beta&0\end{pmatrix}O^{\mathsf T}.
\tag{26.26}
$$

式 (26.24) 使该逆唯一。真实源的两个谱坐标满足同一方程组，故恢复者就是原源，自动满足 $\alpha\beta=0$ 和全部严格正性条件。在交点处两者均为零；无需选择源直线标签，也无遗漏交点的除法。

最后看例外分路。式 (26.14) 已给

$$
R=\{0,1,2\},\qquad d=y_0,\qquad
g(t)=c\,t(t-1)(t-2).
\tag{26.27}
$$

在 $MMJJJMM$ 上，原时钟三至七的实际矩阵依次为

$$
A_3=JM^2,\qquad A_4=M^2,\qquad A_5=JM^2,\qquad
A_6=MJM^2,\qquad A_7=M^2JM^2.
\tag{26.28}
$$

时钟四的回返用的是 $J^2=I$。由 (26.12)，

$$
c=\frac{y_4-d}{24\varphi^2}\ne0,\qquad
t_0=\frac{y_3-d}{6c}=T_0(P),\qquad
t_1=\frac{y_6-d}{120c}=T_1(P).
\tag{26.29}
$$

$24\varphi^2$、$6c$、$120c$ 均非零。此处 $t_0,t_1$ 的下标是式 (26.23) 的谱指数，所用实际读数仍为原时钟三、六。取 $k=0,\ell=1$，由 (26.24)–(26.26) 恢复 $\alpha,\beta,P$；(26.27)–(26.29) 同时恢复整个 $g$ 和 $d$。时钟五、七及所有零增益时钟的动作和读数均保留。至此两分路在全部 $56$ 个根集合、任意非零实 $c$、任意实 $d$ 和整个源切片上，都使实际完整记录唯一确定 $(P,g,d)$。

为证明 (26.7)，固定一个字面 $H_1=(a_0,M,a_1)$ 和一个预先给定的 $K\subseteq\mathcal C\cap\mathcal F(H_1)$。从已经取得的时钟一历史开始，上述策略先在时钟二作 $M$，再依 (26.4) 选择分路，恰用原时钟二至七的六次剩余读数。假设 $L_6(K,H_1)$ 成立。递归 (1.1) 对策略实际所选的每个下一动作都给一个响应子历史，使剩余失败层数下降一。依此六次，得到同一实际完整记录 $H_7$ 和嵌套子集

$$
K=K_1\supseteq K_2\supseteq\cdots\supseteq K_7,\qquad
K_{i+1}=K_i\cap\mathcal F(H_{i+1}),\qquad
L_0(K_7,H_7).
\tag{26.30}
$$

所以 $K_7$ 至少含两个不同完整目标。它们都属于最初固定的 $K$，实现同一整条实际记录，且因策略确定性而走同一条分路。这与已证的 $\mathcal C$ 上记录唯一恢复矛盾，故 (26.7) 成立。此论证不限制 $K$ 的基数，不要求不同终端词采用同一碰撞对，也不从较深失败族抽取保持原层数的一对目标。所有子集都来自同一个最初固定的世界族；没有在取得动作后改变源、增益或漂移。早停条款仍由 (1.1) 的基数守卫保留，所用反策略只选择其合法的完整六读余程。

取 $a_0=0$ 即得到 (18.12) 的真实消费：若某个 $a_1$ 和某个 $K\subseteq\mathcal F((0,M,a_1))$ 满足 $L_6(K,(0,M,a_1))$，则必有 $W\in K\setminus\mathcal C$。等价地，该族必须含有一个 $M$ 迹不等于 $\varphi$ 的源，或一个不能写成 (26.2) 所给三原时钟异根形式的增益。这只是离开 $\mathcal C$ 的必要条件，不是这样的完整原域支撑族的构造；一般 Perron 源配任意三次及以下增益、少于三个不同采样根、重根或非采样根的情形并未被此排除。

这里完整目标与历史的来源是定义 1.1 及 II 定义 51.1，失败族的来源是 II 定义 56.1，严格迹正性是正迹与奇异源引理 3.1；同源纯 $M$ 迹关系与该卷 §§4–5 的关系一致。谱分解、有限二次数域算术和二元线性方程求逆是证明内的标准工具。两分路的完整逆及其对 (18.12) 初始 $M$ 接口的消费是这些关系上的仓内受限综合推导（repo-derived），不含外部原创性或文献优先权断言。

剩余的完整域问题包括 (18.12) 的实际 $JMJ$ 四层失败存在断言、初始 $M$ 六层失败存在断言，以及原根八读与至少九读之分。第 25 章给出的第二 $J$ 五层失败仍供应 (18.12) 的第二个存在断言。定理的八读恢复范围仅为 $\mathcal C$；完整域的八读恢复、原根 $L_7$ 和九读上界均不由此推出。∎

## 追加锚（本行以下为增补区）

## 27. 原七读历史的完整纤维、末 J 单射与末步失败排除

**定义 27.1（固定原历史与候选坐标）。** 使用定义 1.1 的整个 $\mathcal W_3$，令 $\varphi=(1+\sqrt5)/2$、$f_{012}(z)=z(z-1)(z-2)$，固定字面历史

$$
H_6=(0,M,0,M,0,J,6,M,24\varphi,M,60\varphi^2,M,120\varphi^3).
\tag{27.1}
$$

这里已有七读，原时钟为 $0,\ldots,6$，实际六动作词为 $MMJMMM$；余下的一读仍在原时钟七。$\mathcal F(H_6)$ 对全部严格正秩一迹一源、全部非零三次及以下整个增益和全部实常漂移取纤维，不预设增益的根、符号、实际次数或源的 $M$ 迹。源既不要求对称，也不排除对称。

记 $B=JM^2$、$C=MB$。对 $u,n>0$ 及实数 $k,d$，定义候选源和整个插值多项式

$$
\begin{aligned}
r&=-1-3u+(1+k)n,&
b&=-3-4u+(1+2k)n,&
c&=1+2u-kn,\\
Q(u,k,n)&=\begin{pmatrix}r&b\\c&1-r\end{pmatrix},\\
L_i(z)&=\prod_{\substack{0\le j\le3\\j\ne i}}\frac{z-j}{i-j}
\quad(0\le i\le3),\\
\Gamma_{u,n,d}(z)
&=-dL_0(z)-\frac d uL_1(z)-\frac d{1+u}L_2(z)
  +\frac{6-d}{n}L_3(z).
\end{aligned}
\tag{27.2}
$$

$Q$ 在定义阶段不承诺严格正性或秩一；这些合法性仍须证明。再记以下整系数多项式：

$$
\begin{aligned}
U(u)&=u(u+1),\\
H(u)&=143u^2+97u-446,\\
N(u)&=2u^2+85u-42,\\
T(u)&=50u^4+157u^3-261u^2-518u+600,\\
F(u)&=1250u^9-10100u^8-50548u^7+87387u^6\\
&\quad+304653u^5-292493u^4-610657u^3\\
&\quad+462754u^2+231600u-90000.
\end{aligned}
\tag{27.3}
$$

**定理 27.2（完整原域的纤维穷尽）。** 历史 (27.1) 的整个兼容纤维恰为不交并

$$
\begin{aligned}
\mathcal F(H_6)
&=\{W(t):0<t<1/\varphi\}\ \sqcup\ \{W_*\},\\
P(t)&=\begin{pmatrix}
1-\varphi t&\varphi-\varphi^2t\\
t&\varphi t
\end{pmatrix},
\qquad n(t)=\varphi^2-\frac t\varphi,\\
W(t)&=\left(P(t),\frac{f_{012}}{n(t)},0\right).
\end{aligned}
\tag{27.4}
$$

唯一非零漂移世界 $W_*=(P_*,g_*,d_*)$ 由以下数据确定。$u_*$ 是 $F$ 在下列有理开区间内的唯一根：

$$
\frac{1714372989806711221366727852543}{10^{30}}
<u_*<
\frac{1714372989806711221366727852544}{10^{30}}.
\tag{27.5}
$$

定义

$$
\begin{aligned}
k_*&=\frac{N(u_*)}{H(u_*)},&
n_*&=\frac{U(u_*)H(u_*)}{T(u_*)},\\
A_4(u)&=1-\frac4u+\frac6{u+1},&
S_*&=1-4k_*+n_*k_*A_4(u_*),\\
d_*&=\frac{24(\varphi-k_*)}{S_*},&
P_*&=Q(u_*,k_*,n_*),\qquad
g_*=\Gamma_{u_*,n_*,d_*}.
\end{aligned}
\tag{27.6}
$$

这里全部分母非零，$n_*,S_*,d_*>0$，$P_*$ 严格逐项正、秩恰为一、迹一，$g_*$ 为同一个非零且次数至多三的多项式。分类包括实际次数下降、所有采样零和全部消元除数退化情形。

证明。首先固定全部实际累计矩阵及迹坐标。按原时钟左乘，

$$
\begin{aligned}
(A_0,A_1,A_2,A_3,A_4,A_5,A_6)
=\biggl(&I,\
\begin{pmatrix}0&1\\1&1\end{pmatrix},\
\begin{pmatrix}1&1\\1&2\end{pmatrix},\
\begin{pmatrix}1&2\\1&1\end{pmatrix},\\
&\begin{pmatrix}1&1\\2&3\end{pmatrix},\
\begin{pmatrix}2&3\\3&4\end{pmatrix},\
\begin{pmatrix}3&4\\5&7\end{pmatrix}\biggr).
\end{aligned}
\tag{27.7}
$$

对任意兼容世界 $W=(P,g,d)$，置

$$
u=\operatorname{tr}(MP),\qquad
n=\operatorname{tr}(BP),\qquad
k=\frac{\operatorname{tr}(CP)}n.
\tag{27.8}
$$

[正迹与奇异源，引理 3.1](FIB_ORIGINAL_ROOT_POSITIVE_TRACE_GUARDS_AND_SINGULAR_SOURCES.md) 给 $u,n,k>0$。直接复用 [II，式 (52.5)](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md) 的四迹逆，取其 $v=n,w=kn$，即得 $P=Q(u,k,n)$。相应七个迹恰为

$$
(t_0,t_1,t_2,t_3,t_4,t_5,t_6)
=(1,u,1+u,n,kn,(1+k)n,(1+2k)n).
\tag{27.9}
$$

时钟零至三因此强制

$$
(g(0),g(1),g(2),g(3))
=\left(-d,-\frac d u,-\frac d{1+u},\frac{6-d}n\right).
\tag{27.10}
$$

次数至多三使整个 $g$ 恰等于 $\Gamma_{u,n,d}$；这没有先要求任何采样为根，也没有倒取某个增益值或 $6-d$。整个增益在后续原时钟的值为

$$
\begin{aligned}
g(4)&=\frac{24}n+d\left(A_4-\frac4n\right),
&A_4&=1-\frac4u+\frac6{u+1},\\
g(5)&=\frac{60}n+d\left(A_5-\frac{10}n\right),
&A_5&=4-\frac{15}u+\frac{20}{u+1},\\
g(6)&=\frac{120}n+d\left(A_6-\frac{20}n\right),
&A_6&=10-\frac{36}u+\frac{45}{u+1},\\
g(7)&=\frac{210}n+d\left(A_7-\frac{35}n\right),
&A_7&=20-\frac{70}u+\frac{84}{u+1}.
\end{aligned}
\tag{27.11}
$$

这些是四节点插值的恒等式，适用于低于三次的实际次数和每个单独的零样本。

先处理 $d=0$。由 (27.10) 及 $g\ne0$，必有 $g=\lambda f_{012}$，且时钟三给 $\lambda n=1$。时钟四随即给 $\operatorname{tr}(CP)=\varphi n$。将严格正秩一源写成 $P=xy^{\mathsf T}$，其中 $x,y$ 均逐项正，令 $q=(-\varphi,1)^{\mathsf T}$。利用

$$
M-\varphi I=-\frac{qq^{\mathsf T}}\varphi
$$

可将这条迹等式写成

$$
0=y^{\mathsf T}(M-\varphi I)Bx
=-\frac{(y^{\mathsf T}q)(q^{\mathsf T}Bx)}\varphi.
\tag{27.12}
$$

若 $q^{\mathsf T}Bx=0$，因 $Bx$ 逐项正，必有 $Bx=a(1,\varphi)^{\mathsf T}$、$a>0$。但

$$
B^{-1}(1,\varphi)^{\mathsf T}
=(\sqrt5,1-\varphi)^{\mathsf T}
$$

有一正一负两项，与 $x>0$ 矛盾。因此 $y^{\mathsf T}q=0$，即 $y$ 正比例于 $(1,\varphi)^{\mathsf T}$。迹一归一化给出且只给出 (27.4) 的 $P(t)$，严格正性恰等价于 $0<t<1/\varphi$。反向这些矩阵的迹为一、行列式为零且逐项正，故秩恰为一。其 $B$ 迹为 $n(t)$，并有

$$
n(t)>\varphi^2-\varphi^{-2}=\sqrt5>0.
\tag{27.13}
$$

同一个 Perron 行向量关系 $y^{\mathsf T}M=\varphi y^{\mathsf T}$ 给时钟三至六的迹依次为 $n,\varphi n,\varphi^2n,\varphi^3n$。代入同一个增益 $f_{012}/n$，全部七读恰为 (27.1)。这证明零漂移分支的必要性与充分性。

再处理 $d\ne0$，此时仍不假设 $\varphi-k$ 非零。令

$$
\begin{aligned}
D_4&=1-4k+nkA_4,\\
D_5&=-9-10k+n(1+k)A_5,\\
D_6&=-19-40k+n(1+2k)A_6.
\end{aligned}
\tag{27.14}
$$

由 (27.9)、(27.11)、$\varphi^2=\varphi+1$、$\varphi^3=2\varphi+1$，最后三条祖先读数恰等价于

$$
dD_4=24(\varphi-k),\qquad
dD_5=60(\varphi-k),\qquad
dD_6=240(\varphi-k).
\tag{27.15}
$$

因此只除以已知非零的 $d$，取 $2D_5-5D_4=0$ 与 $D_6-10D_4=0$，再乘正数 $U=u(u+1)$，得到两个未倒取系数的方程

$$
\begin{aligned}
n(ka+b_0)&=23U,&
a&=3u^2+3u-10,& b_0&=8u^2+18u-30,\\
n(ka_2+b_2)&=29U,&
a_2&=10u^2+8u-32,& b_2&=10u^2+19u-36.
\end{aligned}
\tag{27.16}
$$

因为 $29a-23a_2=-H$、$29b_0-23b_2=N$，用 $n>0$ 消去右端即得 $kH=N$。下列整数 Bézout 恒等式排除了 $H=0$：

$$
(-23922u-1026913)H+(1710423u+1891519)N=378559400.
\tag{27.17}
$$

事实上 $H=0$ 会同时迫使 $N=0$。另外

$$
Na+Hb_0=23T
$$

使 (27.16) 的第一行等价地给出 $nT=UH$。若 $T=0$，则 $U>0$ 迫使 $H=0$，仍矛盾。所以对每个非零漂移兼容世界，都可以且只能取

$$
k=N/H,\qquad n=UH/T,\qquad H\ne0,\quad T\ne0.
\tag{27.18}
$$

至此既没有除以 $\varphi-k$，也没有除以 $S=D_4$；特别没有丢掉 $\varphi=k$ 或 $S=0$ 的可能世界。

将 (27.18) 代入四迹逆，行列式恒等式为

$$
\det Q\left(u,\frac NH,\frac{UH}T\right)
=-\frac{2(u+2)F(u)}{T(u)^2}.
\tag{27.19}
$$

由于 $u>0$，合法世界必有 $F(u)=0$。下面给出正根的完整有理隔离证书。

取 $p_0=F,p_1=F'$，随后递归取 $-\operatorname{rem}(p_{i-1},p_i)$ 的整系数本原代表 $p_{i+1}$：只除以正的有理内容，保留符号，直至常数。各项次数依次为 $9,8,\ldots,0$；$p_2,\ldots,p_9$ 的降幂系数如下：

| 多项式 | 降幂系数 |
| --- | --- |
| $p_2$ | $[39068200,12488647,-380100744,21355095,1060721294,-358779408,-603832616,135466800]$ |
| $p_3$ | $[131093321186031,182665363437328,-762154347077937,-738509300620194,1467163334504080,252000523478040,-316112154642000]$ |
| $p_4$ | $[1330199456950819579981690,34338584906949244388913,-5449002775683134797328976,-501070754118064003647581,6037657410945186600243468,-482929882076420812976400]$ |
| $p_5$ | $[23657775820249948605168911314498421,-4661675680585610022278761059442262,-96749854979897547230346800498610837,52937108709440950094017295522142796,25845658005587155609425103062769200]$ |
| $p_6$ | $[-62426852638930414243998357942209677630654,2866036270452238798176255269374632654874567,-4961147535481470757976329795983389194934704,1020792576908426649080711772291270941062200]$ |
| $p_7$ | $[-2655621602314215978187985991284772673381046616401,4763036662623485433203200165215888868113441522448,-986510091402490717122186303603294280536031919976]$ |
| $p_8$ | $[-3322462763978503298502235095715255974572554615616495,4602347423424584341314741743503036844420074038983282]$ |
| $p_9$ | $[-1]$ |

常数末项非零还给 $\gcd(F,F')=1$。记 $V(x)$ 为该十项符号列的变号数。在零及正无穷处分别为

$$
\begin{array}{c|c|c}
x&(\operatorname{sgn}p_0,\ldots,\operatorname{sgn}p_9)&V(x)\\ \hline
0&-++--++-+-&6\\
+\infty&++++++----&1
\end{array}
\tag{27.20}
$$

所有下表小数均为精确有理数，而非近似根；在各端点没有链项为零：

| 根序号 | 有理隔离区间 $(a,b)$ | 左端符号 | 右端符号 | $(V(a),V(b))$ |
| --- | --- | --- | --- | --- |
| $1$ | $(0.2906469363,0.2906469364)$ | $-+--++-++-$ | $++--++-++-$ | $(6,5)$ |
| $2$ | $(1.1607389214,1.1607389215)$ | $+--++--++-$ | $---++--++-$ | $(5,4)$ |
| $3$ | $(1.5714248897,1.5714248898)$ | $-++---+---$ | $+++---+---$ | $(4,3)$ |
| $4$ | $(1.7143729898,1.7143729899)$ | $+--++++---$ | $---++++---$ | $(3,2)$ |
| $5$ | $(11.0119189149,11.0119189150)$ | $-++++++---$ | $+++++++---$ | $(2,1)$ |

上述符号可完全在整数上取得：若 $p_i(u)=\sum_{j=0}^{m_i}a_{ij}u^{m_i-j}$、$x=A/B$、$B>0$，其符号就是整数 $\sum_j a_{ij}A^{m_i-j}B^j$ 的符号；正无穷处取首项符号。因 $V(0)-V(+\infty)=5$，Sturm 定理给恰好五个正根。表内五次下降已用尽这五根，故不存在表外正根，也没有未列的重正根。

为对每个整隔离区间筛选源，而非只在近似零点筛选，四迹逆在 (27.18) 上还有如下有理重建：

$$
\begin{aligned}
r(u)&=-\frac{150u^5+376u^4-953u^3-1509u^2+1770u+600}{T},\\
b(u)&=-\frac{200u^5+631u^4-987u^3-2592u^2+1376u+1800}{T},\\
c(u)&=\frac{2(u+2)(50u^4+81u^3-388u^2+106u+150)}{T},\\
S(u)&=\frac{4(1759u^6+5563u^5-12509u^4-34373u^3
              +41706u^2+55584u-60432)}{HT}.
\end{aligned}
\tag{27.21}
$$

在前表五个完整闭区间上，$r$ 分别属于

$$
\begin{array}{c|c}
1&[-2.239454163,-2.239454161]\\
2&[7.799384124,7.799384193]\\
3&[5.624523347,5.624523373]\\
4&[0.793478109,0.793478115]\\
5&[-31.253821933,-31.253821930].
\end{array}
\tag{27.22}
$$

这些包含按以下有理区间规则直接得到：多项式用降幂 Horner 求值，先分别求分子、分母，再作区间除法；加减取相应端点，乘法取四个端点积的最小值与最大值，除法只在整个分母区间不含零时取倒数相乘。对 (27.22) 用 (27.21) 的 $r$ 分子和 $T$；这五个分母区间都不含零。根一、二、三、五的整个区间均违反 $0<r<1$。这些源的排除不依赖 $S$ 或 $\varphi-k$ 的值，因而也涵盖在这些根上可能出现的 $S$ 退化情形。

第四隔离区间内，(27.5) 的两个端点仍有变号数 $(3,2)$，故其中恰有同一根 $u_*$。用精确平方有

$$
2.236067977499789696409173668731
<\sqrt5<
2.236067977499789696409173668732.
\tag{27.23}
$$

将 (27.5) 的闭区间及 (27.23) 的闭区间代入同一套有理区间规则，(27.21) 与 (27.6) 给

$$
\begin{array}{c|c}
r_*&[0.793478112862,0.793478112863]\\
b_*&[0.117896354139,0.117896354140]\\
c_*&[1.389954748528,1.389954748529]\\
1-r_*&[0.206521887137,0.206521887138]\\
S_*&[0.547287915333,0.547287915334]\\
d_*&[36.766818175916,36.766818175917].
\end{array}
\tag{27.24}
$$

同一区间求值还给 $H(u_*),T(u_*),n_*>0$。因此第四根的全部源条目严格正，且 $S_*>0$；此时才允许按 (27.6) 倒取 $S_*$。这是唯一可能合法的根，故没有尚未处理的合法 $S=0$ 情形；$\varphi=k$ 也已被 $d_*>0$ 与 $S_*>0$ 排除，未在消元时预先删除。

最后验证充分性。由 $F(u_*)=0$ 及 (27.19)，$P_*$ 行列式恰为零，迹恒为一，所以秩恰为一。$g_*=\Gamma_{u_*,n_*,d_*}$ 是一个整个多项式，且 $g_*(0)=-d_*<0$，故非零。原时钟零至三的等式由插值逐项给出。在有理函数域中将 (27.18) 代入 (27.14)，恒有

$$
D_5=\frac52S,\qquad D_6=10S,\qquad S=D_4.
\tag{27.25}
$$

这些恒等式不要求仅在数值根处成立。因 $d_*S_*=24(\varphi-k_*)$，(27.25) 给出 (27.15) 的全部三条等式，从而时钟四、五、六也恰好实现 (27.1)。相等由代数恒等式给出，区间包含只承担根的隔离、合法性和分母守卫。反过来，任意非零漂移兼容世界已被迫具有同一个 $u_*,k_*,n_*$，同一个 $d_*$，并由四迹逆与整个插值确定同一个 $P_*,g_*$。这证明存在、唯一性和穷尽性。零漂移与非零漂移两部分因完整目标的漂移坐标不同而不交。∎

**定理 27.3（末 J 在整个纤维上的单射与完整逆）。** 从同一个 $H_6$ 作最后一次 $J$，记实际原时钟七的响应为 $Z_J(W)$。它在整个 $\mathcal F(H_6)$ 上单射。零漂移部分的响应为

$$
Z_J(W(t))
=\frac{210(5+3\varphi-4t/\varphi)}{\varphi^2-t/\varphi},
\tag{27.26}
$$

恰取遍开区间

$$
I_J=(735+21\sqrt5,\ 1260-210\sqrt5)\subset(781,791).
\tag{27.27}
$$

额外世界的响应满足

$$
Z_J(W_*)\in
[1459.482174590103,\ 1459.482174590104]\subset(1459,1460).
\tag{27.28}
$$

故每个可达实际末 $J$ 响应子纤维恰为单点。取得的响应 $z\in I_J$ 时，完整目标为 (27.4)，其中

$$
t=\frac{\varphi\bigl(210(5+3\varphi)-z\varphi^2\bigr)}{840-z};
\tag{27.29}
$$

其余可达响应只能来自 $W_*$，返回 (27.5)–(27.6) 的完整目标。

证明。真实末 $J$ 累计矩阵是

$$
JA_6=\begin{pmatrix}5&7\\3&4\end{pmatrix},
\qquad
\operatorname{tr}(JA_6P)=4+r+3b+7c.
\tag{27.30}
$$

将 $P(t)$ 和同一个 $g(7)=210/n(t)$ 代入，得到 (27.26)。直接求导为

$$
\frac{d}{dt}Z_J(W(t))
=-\frac{210}{\varphi^2n(t)^2}<0.
\tag{27.31}
$$

因此在整个合法开参数区间上严格单调，而非只分离预选的有限源。两端极限分别为

$$
\lim_{t\uparrow1/\varphi}Z_J(W(t))=735+21\sqrt5,\qquad
\lim_{t\downarrow0}Z_J(W(t))=1260-210\sqrt5.
\tag{27.32}
$$

两端不属于源域；连续性、严格单调性及 $n(t)>0$ 给出精确开像 (27.27)。其中下端大于 $781$ 由 $5\cdot21^2>46^2$ 得到，上端小于 $791$ 由 $5\cdot210^2>469^2$ 得到。

对于 $W_*$，仍用同一个整个插值的原时钟七值：

$$
Z_J(W_*)=
d_*+\left(\frac{210}{n_*}
+d_*\left(A_7(u_*)-\frac{35}{n_*}\right)\right)
(4+r_*+3b_*+7c_*).
\tag{27.33}
$$

以 (27.5)、(27.23) 的有理闭区间对 (27.33) 求值即给 (27.28)：源、$S$ 按 (27.21) 的有理分子分母分别用 Horner 求值，$n=UH/T,k=N/H$；$A_7=(20u^2+34u-70)/U$，其余按已述区间四则规则组合。$U,H,T,S,n$ 的分母及除数区间均排除零。这也给出与整个 $I_J$ 的严格分离。结合定理 27.2 的穷尽性，末 $J$ 既分开每两个零漂移目标，也分开 $W_*$ 与每个零漂移目标。

从 (27.26) 解出 $t$ 即为 (27.29)，且在其响应像上 $840-z>49>0$，所以逆式无退化分母。$t$ 决定 $P(t),n(t)$ 和整个 $g=f_{012}/n(t)$，而非仅确定若干增益样本。$W_*$ 则由有理隔离的唯一代数根及 (27.6) 确定。本逆是在定义 1.1 所许的精确实响应与确定性历史策略意义下成立，不增加有限精度、数值稳定性或可计算实数相等判定的结论。∎

**推论 27.4（真实末 M 连续碰撞与任意子族的末步失败排除）。** 末 $M$ 的一个实际响应子纤维包含全部连续零漂移族：

$$
\{W(t):0<t<1/\varphi\}
\subseteq\mathcal F(H_6,M,210\varphi^4).
\tag{27.34}
$$

但对整个原域纤维及其任意子集均有

$$
\neg L_1(\mathcal F(H_6),H_6),\qquad
\forall K\subseteq\mathcal F(H_6),\quad \neg L_1(K,H_6).
\tag{27.35}
$$

因此，在这一个固定原历史上增补任何兼容源、任何常漂移或任何整个三次及以下增益，均不能把它补成一个 $L_1$ 节点。

证明。真实末 $M$ 累计矩阵为

$$
MA_6=\begin{pmatrix}5&7\\8&11\end{pmatrix}=M^4B.
\tag{27.36}
$$

对全部 $W(t)$，Perron 行关系给 $\operatorname{tr}(MA_6P(t))=\varphi^4n(t)$。每个世界固定的整个增益在七处为 $210/n(t)$，漂移为零，所以实际响应均为 $210\varphi^4$。特别地，预先固定

$$
t_1=\frac1{4\varphi},\qquad t_2=\frac1{2\varphi}
\tag{27.37}
$$

给两个不同合法完整目标。它们在 $H_6$ 的全部七个祖先读数及该末 $M$ 读数上一致，确实构成非单点实际子纤维；这不是一个忽略祖先约束的形式碰撞。

另一方面，定理 27.3 对每个实数 $z$ 给

$$
\left|K\cap\mathcal F(H_6,J,z)\right|\le1
\qquad\text{对所有 }K\subseteq\mathcal F(H_6).
\tag{27.38}
$$

而原递归 (1.1) 的 $L_1(K,H_6)$ 要求对两个允许动作各有一个实际响应子族满足 $L_0$，即至少两个不同完整目标。末 $J$ 的存在响应条款已被 (27.38) 排除，故 (27.35) 对任意基数的 $K$ 成立，末 $M$ 的连续碰撞不能补回该条款。纤维本身含有 (27.37) 的不同目标，故在 $H_6$ 立即停止不能恢复整个纤维；再作合法末 $J$ 则能在原时钟七恢复。早停语义与两动作的共同目标域均未改变。

所有目标的源、一个整个增益及常漂移都在各自整条轨迹中固定。零漂移族在时钟零、一、二的增益为零；初读照常计数，时钟一、二的两个 $M$ 及其立即读数仍实际执行，(27.7) 的后续矩阵未删除这些动作。两个末动作的互择响应只用于证明策略与碰撞，不在一条轨迹上额外获取。此消费者直接作用于整个真实纤维，无须从较深失败族抽取碰撞对。∎

**约定 27.5（供应关系与原问题边界）。** 定义 1.1 及 [II，定义 51.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md) 供应原完整世界、正尺度规范和原时钟合同；II 式 (52.5) 供应四迹坐标逆；[正迹与奇异源，引理 3.1](FIB_ORIGINAL_ROOT_POSITIVE_TRACE_GUARDS_AND_SINGULAR_SOURCES.md) 供应严格迹正性；II 定义 56.1 供应已含早停的失败递归。这些是证明中直接复用的前置。Sturm 根计数、Lagrange 插值、有限有理区间算术、迹线性和二阶行列式均为成熟中间工具，不作为新增成果单列。本节的 repo-derived 普通数学内容是将同一 (27.1) 的原历史、全部源约束、整个增益与漂移联合穷尽，及其整个纤维末 $J$ 单射对 (1.1) 的排除消费者；不含外部原创性、文献优先权或 Lean 内核核验主张。

这里的零漂移族满足 $\operatorname{tr}(MP(t))=\varphi$，且增益根恰为 $\{0,1,2\}$，故包含于第 26 章的承诺类 $\mathcal C$。但 $u_*>1.714>\varphi$，所以 $W_*\notin\mathcal C$；定理 27.2 与 27.3 还覆盖这个合法非零漂移世界。第 26 章的两分路八读完整逆及其对任意 $\mathcal C$ 支撑族的初始 $M$ 排除仍按原范围成立，不能被解释为已经穷尽 (27.1) 的原域纤维。原卷推论 44.3 给出的特定旧 $MM$ 对沿 $MMJMMMM$ 延长失败，只约束那一对；(27.35) 则排除了在本节这一个固定 $H_6$ 上任意补世界的末步修复路线。

第 25 章已供应 (18.12) 的第二 $J$ 五层失败存在断言；其非平坦第一 $J$ 历史的条件动作结论保留。[三次图，第 51 章](FIB_MMJ_FULL_VARIABLE_CUBIC_CHART_AND_COLLISION_COMPATIBILITY.md) 已供应另一个字面父 $H_4^*=(0,J,24,M,48,J,z^*,M,Y^*)$ 的 $L_3$，也保留该原范围。它们与本节的 $MMJMMM$ 父不是同一个字面历史，不能仅按层数互相替代或拼接。

式 (27.35) 不供应更早祖先的相反动作失败世界，不证明任意原根策略必须到达 $H_6$，也不构造初始 $M$ 的 $L_6$。在 (18.12) 的既有充分链上，实际 $JMJ$ 的 $L_4$ 存在断言与初始 $M$ 的 $L_6$ 存在断言仍待其各自联合兼容世界。原完整域的八读恢复或八读排除、原根 $L_7$、八读与至少九读之分及九读上界均未由本节解决。

## 追加锚（本行以下为增补区）

## 28. 参数七读纤维的接合与末步失败的精确区域

**定义 28.1（同动作词的参数历史）。** 保持定义 1.1 的整个 $\mathcal W_3$、完整目标及原时钟合同。对每个 $\theta\in\mathbb R$，固定

$$
H_\theta=(0,M,0,M,0,J,6,M,24\theta,M,60(1+\theta),M,120(1+2\theta)).
\tag{28.1}
$$

已有读数仍在原时钟 $0,\ldots,6$，动作词仍为 $MMJMMM$。$\theta$ 是实际历史的参数，不是对源、增益或漂移另加的承诺。沿用 (27.2) 的 $Q,\Gamma$、(27.3) 的 $U,H,N,T,F$ 和 (27.5)–(27.6) 的固定 $u_*,k_*,n_*,S_*,P_*$。这里 $P_*$ 的定义不含 $\varphi$。置

$$
\begin{aligned}
D_\theta&=\{q:1/2<q<1,\ q<\theta<1+1/q\},\\
s(q)&=\frac{1-q}{2q-1},\qquad
v_\theta(q)=\frac{\theta-q}{1+q-\theta q},\\
P_\theta(q)&=\frac1{1+s(q)v_\theta(q)}
\begin{pmatrix}1&v_\theta(q)\\s(q)&s(q)v_\theta(q)\end{pmatrix},\\
n_\theta(q)&=\operatorname{tr}(BP_\theta(q)),\qquad B=JM^2,\\
\mathcal Z_\theta&=\left\{\left(P_\theta(q),\frac{f_{012}}{n_\theta(q)},0\right):q\in D_\theta\right\},\\
d_\theta&=\frac{24(\theta-k_*)}{S_*},\qquad
\mathsf E_\theta=(P_*,\Gamma_{u_*,n_*,d_\theta},d_\theta).
\end{aligned}
\tag{28.2}
$$

**定理 28.2（全部实参数的完整纤维）。** 对每个实数 $\theta$，

$$
\mathcal F(H_\theta)=\mathcal Z_\theta\cup\{\mathsf E_\theta\}.
\tag{28.3}
$$

$\mathsf E_\theta$ 对全部实参数均为合法完整世界。两个部分相交当且仅当 $\theta=k_*$，此时交集恰为 $\{\mathsf E_{k_*}\}$，不产生两个不同目标。零漂移部分非空当且仅当 $1/2<\theta<3$；其参数域准确为

$$
D_\theta=
\begin{cases}
(1/2,\theta),&1/2<\theta<1,\\
(1/2,1),&1\le\theta\le2,\\
(1/2,1/(\theta-1)),&2<\theta<3,\\
\varnothing,&\text{其余情形}.
\end{cases}
\tag{28.4}
$$

特别地，$\theta\le1/2$ 或 $\theta\ge3$ 时整个纤维恰为单点，而非空集。

证明。全部累计矩阵直接复用 (27.7)。对任意兼容世界，严格迹正性仍给 $u,n,k>0$，四迹逆和整个插值仍为 (27.8)–(27.11)。若 $d=0$，前三个零读数和正迹迫使 $g(0)=g(1)=g(2)=0$；同一个非零且次数至多三的多项式因而为 $\lambda f_{012}$。时钟三给 $\lambda=1/n$，时钟四给 $k=\theta$，时钟五、六随 $M^2=M+I$ 自动成立。

每个严格正秩一迹一源唯一写成

$$
P=\frac1{1+sv}\begin{pmatrix}1&v\\s&sv\end{pmatrix},\qquad s,v>0.
\tag{28.5}
$$

事实上 $s=P_{21}/P_{11}$、$v=P_{12}/P_{11}$，秩一及迹一给出余下分量。其两迹为

$$
n=\frac{1+2s+v+sv}{1+sv},\qquad
kn=\frac{1+s+2v+3sv}{1+sv}.
\tag{28.6}
$$

令 $q=(1+s)/(1+2s)$，则 $1/2<q<1$。方程 $k=\theta$ 恰为

$$
v(1+q-\theta q)=\theta-q.
\tag{28.7}
$$

若右端非正，则 $\theta\le q<1$，左端括号严格正，不可能有 $v>0$。若左端括号非正，则 $\theta\ge1+1/q>2$，右端严格正，也不可能。故正源恰要求 $q<\theta<1+1/q$，给出 (28.2)。这些条件使全部显示分母严格正，$n_\theta(q)>0$。它们对 $q$ 求交即为 (28.4)，没有删除等号处的额外合法源。反向代入 (28.6) 和 $g=f_{012}/n$，全部七读恰为 (28.1)。这穷尽零漂移部分。

若 $d\ne0$，用 (27.14) 的同一个 $D_4,D_5,D_6$，后三条祖先约束准确变为

$$
dD_4=24(\theta-k),\qquad
dD_5=60(\theta-k),\qquad
dD_6=240(\theta-k).
\tag{28.8}
$$

仅除以已知非零的 $d$，仍得 $2D_5-5D_4=0$、$D_6-10D_4=0$。于是 (27.16)–(27.19) 的消元方程、Bézout 除数守卫和秩一九次式完全不含 $\theta$，其正源筛选也不含 $\theta$。直接复用该处全部正根隔离与合法性证明，唯一可能的源坐标仍为 $u_*,k_*,n_*$。原证明先排除 $H=0,T=0$，再筛出该严格正源；没有在此之前倒取 $\theta-k$ 或 $D_4$，所以同样覆盖 (28.8) 的退化情形。最后 $D_4=S_*>0$ 迫使 $d=d_\theta$，故非零漂移世界只能为 $\mathsf E_\theta$，且此时 $\theta\ne k_*$。

反向，对固定源 $P_*$，已有消元恒等式给 $D_5=5S_*/2$、$D_6=10S_*$。因此 (28.8) 对 $d_\theta$ 逐项成立，四节点插值供应全部早期读数，得到所有实 $\theta$ 的 $\mathsf E_\theta$。若 $d_\theta\ne0$，其 $g(0)=-d_\theta\ne0$；若 $d_\theta=0$，其 $g(3)=6/n_*>0$。所以整个增益在任何参数处都不成为零多项式，低次退化仍允许。

两个部分相交必有 $d_\theta=0$，故 $\theta=k_*$。反过来，此时 $\Gamma_{u_*,n_*,0}=f_{012}/n_*$，而 $P_*$ 严格正且其两迹比为 $k_*$，由刚证的零漂移穷尽性知 $\mathsf E_{k_*}\in\mathcal Z_{k_*}$。因此这里是一个世界的接合，不能作为碰撞。∎

**定理 28.3（零漂移响应的折返与固定源响应）。** 从同一个 $H_\theta$ 在原时钟七作末 $E\in\{M,J\}$，记响应为 $Z_E$。对 $q\in D_\theta$，

$$
\begin{aligned}
Z_M\!\left(P_\theta(q),f_{012}/n_\theta(q),0\right)&=210(2+3\theta),\\
\frac1{210}Z_J\!\left(P_\theta(q),f_{012}/n_\theta(q),0\right)
&=j_\theta(q)
=\frac{2+4q+q^2+\theta(1-3q^2)}{1+q-q^2}.
\end{aligned}
\tag{28.9}
$$

末 $J$ 在 $\mathcal Z_\theta$ 上非单射，当且仅当

$$
13/8<\theta<5/3.
\tag{28.10}
$$

令 $V_* =\operatorname{tr}(JA_6P_*)$，其中 $A_6$ 为 (27.7) 的固定末累计矩阵。定义常数

$$
\begin{aligned}
\beta&=\frac{24\left[1+(A_7(u_*)-35/n_*)V_*\right]}{210S_*},\\
\alpha&=\frac{V_*}{n_*}-\beta k_*,\qquad
A_7(u)=20-70/u+84/(u+1).
\end{aligned}
\tag{28.11}
$$

则对全部实 $\theta$，

$$
Z_J(\mathsf E_\theta)/210=\alpha+\beta\theta,
\qquad
\frac{903}{1000}<\alpha<\frac{904}{1000},\quad
\frac{3737}{1000}<\beta<\frac{3738}{1000}.
\tag{28.12}
$$

证明。由 $M^4=2I+3M$、$\operatorname{tr}(BP)=n$、$\operatorname{tr}(MBP)=\theta n$ 和 $g(7)=210/n$，得末 $M$ 恒值。末 $J$ 的矩阵与四迹表达式仍为 (27.30)。代入 (28.2)，约去严格正的公因子，得到 $j_\theta$，没有在来源层增加任何读数。

置 $D(q)=1+q-q^2>0$。直接求导有

$$
\begin{aligned}
j_\theta'(q)&=\frac{5q^2+6q+2-\theta(3q^2+4q+1)}{D(q)^2},\\
h(q)&=\frac{5q^2+6q+2}{3q^2+4q+1},\qquad
h'(q)=-\frac{2D(q)}{(3q^2+4q+1)^2}<0,\\
h(1/2)&=5/3,\qquad h(1)=13/8.
\end{aligned}
\tag{28.13}
$$

因此 $\theta\le13/8$ 时 $j_\theta$ 在 $(1/2,1)$ 上严格递增，$\theta\ge5/3$ 时严格递减；在两个等号处，导数仅可能在未包含的端点为零。限制到任何 $D_\theta$ 仍为单射。若 (28.10) 成立，(28.4) 给整个 $D_\theta=(1/2,1)$；唯一临界点满足 $h(q)=\theta$，两侧导数先正后负。因此有严格内部极大值，两侧像存在非空开交集，给两个不同 $q$ 的同读。由 (28.5) 的唯一性，它们确为不同完整目标，得准确条件 (28.10)。

对固定源世界，(27.11) 的整个增益在七处给

$$
Z_J(\mathsf E_\theta)
=\frac{210V_*}{n_*}
+d_\theta\left[1+(A_7(u_*)-35/n_*)V_*\right],
\tag{28.14}
$$

所以响应是 (28.12) 的仿射式。其有理界可直接由 (27.5) 的闭区间端点和 (27.6) 取得：以 Horner 方式对 $H,N,T$ 求区间，取 $k=N/H,n=UH/T$，再按 (27.2) 取 $r,b,c$、$V_*=4+r+3b+7c$，最后依 (28.11) 作有理四则运算。全部除数区间排除零。所得闭区间严格包含于 (28.12) 的显示开区间；同一运算给 $3/4<k_*<4/5$。这些界只定位固定代数常数，没有另选或拟合来源。∎

**定理 28.4（完整纤维的末步失败相图）。** 定义两个精确代数阈值

$$
a_\circ=\frac{17/5-\alpha}{\beta-1/5},\qquad
b_\circ=\frac{7-\alpha}{\beta+2}.
\tag{28.15}
$$

它们满足

$$
\frac7{10}<a_\circ<\frac{18}{25}<\frac34<k_*<\frac45<1
<\frac{21}{20}<b_\circ<\frac{27}{25}<\frac{13}{8}.
\tag{28.16}
$$

对全部实参数，原含早停递归的精确判据为

$$
L_1(\mathcal F(H_\theta),H_\theta)
\quad\Longleftrightarrow\quad
\theta\in\bigl((a_\circ,b_\circ)\setminus\{k_*\}\bigr)
\ \cup\ (13/8,5/3).
\tag{28.17}
$$

证明。(28.12) 与 $3/4<k_*<4/5$ 用正分母的有理比较给 (28.16)。两个碰撞机制须分别核对。其一是 (28.10) 的零漂移内部折返。其二只能来自 $\mathsf E_\theta$ 与 $\mathcal Z_\theta$ 的交叉响应，因为 (28.3) 已穷尽整个纤维。

对所有 $1/2<q<1$，有

$$
\partial_\theta j_\theta(q)-\frac15
=-\frac{(2q-1)(7q+4)}{5D(q)}<0.
\tag{28.18}
$$

故 $\alpha+\beta\theta-j_\theta(q)$ 对 $\theta$ 严格递增，斜率大于 $\beta-1/5>0$。在 $\theta=a_\circ$，因 $a_\circ<13/8$，$j_{a_\circ}$ 严格递增且

$$
\alpha+\beta a_\circ
=j_{a_\circ}(1/2)=17/5+a_\circ/5
<j_{a_\circ}(q).
\tag{28.19}
$$

于是 $\theta\le a_\circ$ 时，固定源响应严格小于所有 $q\in(1/2,1)$ 的零漂移响应。在 $\theta=b_\circ$，同理

$$
\alpha+\beta b_\circ=j_{b_\circ}(1)=7-2b_\circ
>j_{b_\circ}(q),
\tag{28.20}
$$

所以 $\theta\ge b_\circ$ 时，固定源响应严格大于所有这样的零漂移响应。这些比较在完整区间 $(1/2,1)$ 上成立，因而也适用于参数变化后的合法子域，不把不同 $D_\theta$ 误作同一个来源集合。

剩下 $a_\circ<\theta<b_\circ$。此时 $j_\theta$ 严格递增。若 $\theta<1$，实际域是 $(1/2,\theta)$，两端响应为

$$
j_\theta(1/2)=17/5+\theta/5,\qquad
j_\theta(\theta)=2+3\theta.
\tag{28.21}
$$

固定源响应大于前者，由 $\theta>a_\circ$ 得到；它小于后者，因为 $\beta>3$、$\alpha+\beta<5$，故

$$
\alpha+\beta\theta-(2+3\theta)
<\alpha+\beta-5<0.
\tag{28.22}
$$

若 $1\le\theta<b_\circ$，实际域是 $(1/2,1)$，下端仍为 (28.21) 第一式，上端为 $7-2\theta$。前者小于固定源响应当且仅当 $\theta>a_\circ$，后者大于它当且仅当 $\theta<b_\circ$。连续性和严格单调性遂给唯一 $q\in D_\theta$，使 $j_\theta(q)=\alpha+\beta\theta$。因此交叉同读准确发生在 $(a_\circ,b_\circ)$，但它是不同目标的碰撞还须 $\theta\ne k_*$。在 $k_*$ 处，定理 28.2 说明两分支是同一个世界，而本区间内零漂移响应单射，不能重复计数。

若零漂移部分非空，它含连续多个不同目标；(28.9) 使末 $M$ 的一个实际响应子纤维始终非单点。因此 (1.1) 的 $L_1$ 在这里恰等价于末 $J$ 非单射，以上两种且仅有的碰撞机制给 (28.17)。若零漂移部分为空，整个纤维为单点，$L_1$ 的非单点及早停守卫直接失败。$a_\circ,b_\circ$ 的交点落在未包含的来源端点；$13/8,5/3$ 的临界点也落在未包含的 $q$ 端点，故四个阈值均须按显示的开区间处理。∎

**命题 28.5（有理实际见证及同父下一层的准确缺口）。** 置 $\theta_0=33/20$，定义两个固定完整世界

$$
\begin{aligned}
P_0&=\frac1{271}\begin{pmatrix}61&105\\122&210\end{pmatrix},
&g_0&=\frac{271}{620}f_{012},&d_0&=0,\\
P_1&=\frac1{267}\begin{pmatrix}77&133\\110&190\end{pmatrix},
&g_1&=\frac{267}{620}f_{012},&d_1&=0.
\end{aligned}
\tag{28.23}
$$

它们严格合法且不同，共同七读及两个互择末响应分别为

$$
\begin{aligned}
(y_0,\ldots,y_6)&=(0,0,0,6,198/5,159,516),\\
Z_M(W_0)=Z_M(W_1)&=2919/2,\\
Z_J(W_0)=Z_J(W_1)&=24297/31.
\end{aligned}
\tag{28.24}
$$

令同一个六读父历史为

$$
H^-=(0,M,0,M,0,J,6,M,198/5,M,159).
\tag{28.25}
$$

则

$$
\begin{aligned}
&L_1(\mathcal F(H^-,M,516),(H^-,M,516)),\\
&L_2(\mathcal F(H^-),H^-)
\ \Longleftrightarrow\
&\hspace{12mm}\exists z\in\mathbb R:\
L_1(\mathcal F(H^-,J,z),(H^-,J,z)).
\end{aligned}
\tag{28.26}
$$

证明。两个显示矩阵的全部元素严格正；两条对角线之和分别为 $271/271$、$267/267$，两条乘积相等，故迹一、秩一。它们的 $P_{21}/P_{11}$ 分别为 $2$、$10/7$，所以目标不同。其 $B$ 迹分别为 $620/271$、$620/267$，$MB$ 迹比分别都为 $33/20$。同一个三根多项式与 (27.7) 的各实际矩阵相乘即给全部祖先及末响应 (28.24)；这里两个末动作的同读使用同一对世界，比 (1.1) 所需量词更强，并未把两个互择结果当作一条轨迹共同取得的记录。

这两个世界属于 $\mathcal F(H^-,M,516)$，且在每个末动作都有共同响应，直接供应 (28.26) 第一式。故六读父的非单点守卫和 $M$ 分支条款都已满足；将 (1.1) 的 $L_2$ 展开，唯一余下条款正是 (28.26) 第二式的右端。这是同一字面父、原时钟六的 $J$ 动作及其原时钟七后续，不允许替换为别的父历史上的 $L_1$。

这些源的 $M$ 迹分别为 $437/271$、$433/267$，均为有理数，不等于 $\varphi$。因此它们在第 26 章 Perron 三根承诺类之外；但离开该类只满足那里的必要条件，不能把当前一个 $L_1$ 自动提升为初始 $M$ 的 $L_6$。∎

**约定 28.6（供应关系与原域边界）。** 完整域、原时钟与含早停失败递归由定义 1.1 供应；四迹逆、严格正迹和全部固定源消元、根隔离及除数守卫分别按第 27 章所引前置与 (27.16)–(27.24) 复用。有限插值、单变量单调性和有理区间运算是证明内的成熟工具，不另列为新增结果。本章的仓内综合增量（repo-derived）是参数历史的整个纤维接合、两类末 $J$ 碰撞的精确区域及其实际失败消费者，不申领外部原创性或文献优先权。

$\theta=\varphi$ 时 (28.1) 就是 (27.1)。因 $b_\circ<\varphi<13/8$，(28.17) 与第 27 章的末 $J$ 单射一致；它没有被新历史的失败所推翻。参数变化改变的是实际历史，不是在固定历史中无条件增加来源。命题 28.5 供应 (28.26) 的 $M$ 支臂，未供应其 $J$ 支臂，也未证明任何原根策略必须到达这个父。第 25 章的第二 $J$ 五层失败及三次图第 51 章在其各自父历史上的结论继续按原范围成立。(18.12) 的实际 $JMJ$ 四层失败、初始 $M$ 六层失败和完整原域的八读／九读判别，仍分别需要原来的共同祖先兼容条件。

## 追加锚（本行以下为增补区）

## 29. 六读父纤维的完整来源曲线与固定 JM 恢复

**定义 29.1（父历史的三迹坐标）。** 保持定义 1.1 的全部来源、整个增益、常漂移和原时钟，固定 (28.25) 的同一个 $H^-$。置 $B=JM^2$，并对来源定义

$$
\begin{gathered}
u=\operatorname{tr}(MP),\quad n=\operatorname{tr}(BP),\quad
a=\operatorname{tr}(MBP),\qquad h=u(u+1),\quad \ell=u^2+3u-4,\\
R=33n-20a,\qquad
\Delta=nh+an\ell-4ah,\\
A=3u^2+3u-10,\quad B_1=8u^2+18u-30,\quad
\Phi=Aa+B_1n-23h,\\
D=a^2-na-n^2+(4u+2)n-2(u+1)a-u^2+u+1,\\
P(u,n,a)=
\begin{pmatrix}
n+a-3u-1&n+2a-4u-3\\
1+2u-a&2+3u-n-a
\end{pmatrix}.
\end{gathered}                                                   \tag{29.1}
$$

字母 $B_1$ 是标量多项式，与累计矩阵 $B$ 区分。记 $\mathcal C$ 为满足

$$
\begin{gathered}
u,n,a>0,\quad D=0,\quad
0<n+a-3u-1<1,\\
n+2a-4u-3>0,\quad 1+2u-a>0,\quad
\Delta\ne0,\quad R\Phi=0
\end{gathered}                                                   \tag{29.2}
$$

的三元组。对这样的三元组，令 $d=6hR/(5\Delta)$，并令 $g$ 为在 $0,1,2,3$ 分别取值

$$
-d,\qquad -d/u,\qquad -d/(1+u),\qquad (6-d)/n
\tag{29.3}
$$

的至多三次插值多项式。

**定理 29.2（整个父纤维的坐标双射）。** 定义 29.1 给出 $\mathcal C$ 与 $\mathcal F(H^-)$ 的双射。若第六动作是 $J$，记其读数为 $z$，随后原时钟七作 $M$ 的读数为 $m$。置

$$
\begin{gathered}
K=5a\ell-28h,\quad V=10u^2+19u-36,\quad X=20u^2+34u-70,\\
N_d=6hR,\quad G_6=6(20K+RV),\quad G_7=6(35K+RX).
\end{gathered}                                                   \tag{29.4}
$$

则完整响应为

$$
z=\frac{N_d+(1+2n)G_6}{5\Delta},\qquad
m=\frac{N_d+(u+2a)G_7}{5\Delta}.
\tag{29.5}
$$

证明。四个迹 $1,u,n,a$ 的线性逆给出 (29.1)，且该显示矩阵的行列式恰为 $D$。沿真实动作词 $MMJMMJM$，从时钟零起的迹依次为

$$
1,\ u,\ 1+u,\ n,\ a,\ n+a,\ 1+2n,\ u+2a.
\tag{29.6}
$$

严格正源使这些迹为正。前三个零读数和时钟三的读数六给 (29.3)，不要求增益恰为三次，也不删除前三次动作。

插值在四处的值是 $24/n+d(\ell/h-4/n)$，故时钟四的约束等价于

$$
d\Delta=6hR/5.                                                  \tag{29.7}
$$

先证明它没有遗漏 $\Delta=0$ 的来源。若 $\Delta=0$，(29.7) 迫使 $R=0$。把任意正秩一迹一源唯一写成

$$
P_s=\frac1{1+sv}\begin{pmatrix}1&v\\s&sv\end{pmatrix},\qquad s,v>0,
$$

则 $a/n=33/20$ 准确给 $v=(13+46s)/(7+27s)$。于是

$$
u=\frac{13+66s+73s^2}{7+40s+46s^2}\in(1,2),\qquad
n=\frac{20(1+5s+5s^2)}{7+40s+46s^2}<20/7.
\tag{29.8}
$$

从而 $0<\ell/h<1$，且

$$
\frac{\Delta}{nh}=1+\frac{33}{20}\frac{n\ell}{h}-\frac{33}{5}
<1+\frac{33}{7}-\frac{33}{5}=-\frac{31}{35},
$$

矛盾。故实际父纤维总有 $\Delta\ne0$，(29.7) 给出显示的 $d$。将其代入同一个插值，时钟五读数减去 $159$ 恰为 $3R\Phi/(5\Delta)$。这给 (29.2) 的最后一个方程。反向，(29.2) 保证正秩一迹一源；(29.3)、(29.7) 和该残差等式供应全部六个祖先读数。若 $g$ 是零多项式，时钟零迫使 $d=0$，而时钟三读数六不可能成立，故 $g\ne0$。四节点插值唯一，因此双射恢复的是整个 $g$ 和 $d$，不只是有限样本。

同一插值在六、七处分别为 $G_6/(5\Delta),G_7/(5\Delta)$。结合 (29.6) 的最后两迹即得 (29.5)。∎

**定理 29.3（正来源的两条代数曲线与唯一极点）。** 在 $\Phi=0$ 的严格正来源上，必有 $u>3/2$。定义

$$
\begin{aligned}
c_2(u)&=79u^4+348u^3-221u^2-1290u+1100,\\
c_1(u)&=84u^5-143u^4-1578u^3-401u^2+1950u+800,\\
c_0(u)&=-9u^6-147u^5+193u^4+1131u^3+1100u^2+500u+100,\\
F(u,n)&=c_2(u)n^2+c_1(u)n+c_0(u),\\
\mathcal Q(u)&=1100u^6+1684u^5-9243u^4-11138u^3
+20249u^2+15560u+2000,\\
n_\pm(u)&=\frac{-c_1(u)\pm A(u)\sqrt{\mathcal Q(u)}}{2c_2(u)},\qquad
a_\pm(u)=\frac{23h-B_1n_\pm(u)}{A(u)}.
\end{aligned}                                                   \tag{29.9}
$$

对 $u>3/2$，这些分母为正，且 $\mathcal Q(u)>0$。以下四个方程各有唯一的 $u>3/2$ 实根，分别记为 $\alpha_0,\beta_0,\gamma_0,\eta_0$：

$$
\begin{array}{c|c|c}
\text{根}&\text{方程}&\text{有理隔离区间}\\ \hline
\alpha_0&19u^3+27u^2-72u-40=0&(1649/1000,1650/1000)\\
\beta_0&7u^2-8u-10=0&(1896/1000,1897/1000)\\
\gamma_0&19u^3+14u^2-105u+10=0&(1953/1000,1954/1000)\\
\eta_0&7u^3+2u^2-35u-5=0&(2170/1000,2171/1000).
\end{array}                                                     \tag{29.10}
$$

全部严格正的 $D=\Phi=0$ 来源恰为

$$
\begin{aligned}
\mathcal S_-&=\{(u,n_-(u),a_-(u)): \beta_0<u<\eta_0\},\\
\mathcal S_+&=\{(u,n_+(u),a_+(u)): \alpha_0<u<\gamma_0\}.
\end{aligned}                                                   \tag{29.11}
$$

$\Delta$ 在 $\mathcal S_-$ 上不为零，在 $\mathcal S_+$ 上恰有一个零点，其 $u$ 坐标 $\sigma$ 满足

$$
18383242777/10^{10}<\sigma<18383242778/10^{10}.
\tag{29.12}
$$

证明。写 $P=\left(\begin{smallmatrix}p&b\\c&1-p\end{smallmatrix}\right)$，则 $u=b+c+1-p>0$，且 $n=1+b+2c<1+2u$、$a=1+2u-c<1+2u$。当 $u\le1$ 时，$A,B_1<0$，故 $\Phi<0$。在 $1<u\le3/2$ 上，若 $B_1\le0$ 则同样如此；若 $B_1>0,A\le0$，则

$$
\Phi<B_1(1+2u)-23h=16u^3+21u^2-65u-30<0.
$$

若 $A>0$，则 $B_1>0$，且

$$
\Phi<(A+B_1)(1+2u)-23h=22u^3+30u^2-82u-40<0.
$$

这两个三次式在 $[1,3/2]$ 上导数为正，而右端值分别为 $-105/4,-85/4$。因此 $u>3/2$，尤其 $A>0$；没有除以未排除的 $A=0$ 截面。解 $\Phi=0$ 并代入 $D$，恰得

$$
A^2D\!\left(u,n,\frac{23h-B_1n}{A}\right)=F(u,n),\qquad
\operatorname{disc}_nF=A^2\mathcal Q.
\tag{29.13}
$$

Sturm 实根计数给 $\mathcal Q$ 在 $(0,\infty)$ 无根，$c_2$ 在 $(3/2,\infty)$ 无根；其变号数对分别为 $(2,2)$、$(0,0)$。由 $\mathcal Q(0)>0,c_2(3/2)>0$，两条显示根在整个 $u>3/2$ 上相异、光滑。

为穷尽正性边界，在 $a=(23h-B_1n)/A$ 中令 $p=n+a-3u-1,b=n+2a-4u-3,c=1+2u-a$。分别对 $F$ 与 $Ap,A(p-1),Ab,Ac$ 消去 $n$，所得非零常数因子外的结果为

$$
\begin{array}{c|l}
p&2A^2(7u^3+2u^2-35u-5)(19u^3+14u^2-105u+10)\\
p-1&2(u+2)A^2(7u^2-8u-10)(19u^3+27u^2-72u-40)\\
b&-A^2(19u^3+14u^2-105u+10)(19u^3+27u^2-72u-40)\\
c&-4(u+2)A^2(7u^2-8u-10)(7u^3+2u^2-35u-5).
\end{array}                                                     \tag{29.14}
$$

每个 (29.10) 多项式在 $(3/2,\infty)$ 的 Sturm 变号数对均为 $(1,0)$，在其显示隔离区间也为 $(1,0)$。故正性只能在这四处改变。相邻区间取 $8/5,17/10,19/10,2,3$ 检查，分别得到以下符号；表中三元组按 $(p,b,c)$ 排列。

$$
\begin{array}{c|c|c}
u\text{ 区间}&n_-\text{ 分支}&n_+\text{ 分支}\\ \hline
(3/2,\alpha_0)&(p>1,b>0,c<0)&(p>1,b<0,c>0)\\
(\alpha_0,\beta_0)&(p>1,b>0,c<0)&(0<p<1,b>0,c>0)\\
(\beta_0,\gamma_0)&(0<p<1,b>0,c>0)&(0<p<1,b>0,c>0)\\
(\gamma_0,\eta_0)&(0<p<1,b>0,c>0)&(p<0,b<0,c>0)\\
(\eta_0,\infty)&(p<0,b>0,c<0)&(p<0,b<0,c>0).
\end{array}                                                     \tag{29.15}
$$

相异光滑根与 (29.14) 保证符号在各区间内不变。这里 $p,b,c$ 对 $n$ 的系数分别为 $-5\ell/A,(A-2B_1)/A,B_1/A$，在 $u>3/2$ 都不为零。因此两个相异根不能同时达到同一个边界；结合四个边界根互异，$\beta_0$ 处的 $n_+$ 来源及 $\gamma_0$ 处的 $n_-$ 来源仍严格正。严格正性只排除自身分支的端点，给出完整的开区间 (29.11)，没有遗漏不接边界的额外分支。

以下给出同时用于本定理和下一定理的实根证书约定。把 (29.5) 中 $a$ 换成 $(23h-B_1n)/A$，所得有理函数记为 $z(u,n),m(u,n)$。对有理函数 $e(u,n)$，先取约分分子，对 $F$ 在 $\mathbb Q(u)[n]$ 中取余，再清去系数分母和整数公因子，得到 $r_e(u,n)$。令

$$
E_e(u)=\operatorname{sqfree}\operatorname{Res}_n(F,r_e),
\tag{29.16}
$$

并从此无平方因子多项式中剔除与 $Ac_2$ 的公因子。这里的消元只用于 $A,c_2\ne0$ 的范围，故不删除该范围内的实际零点。记 $V_e(x)$ 为从 $E_e,E_e'$ 开始、每步取负余式的 Sturm 序列在 $x$ 处去零后的变号数。置

$$
e_m=m_uF_n-m_nF_u.
$$

由 (29.1)、(29.5)、(29.9)、(29.16) 的有理运算得到下表；$\Delta$ 在表中也先作同一个 $a$ 代换。

$$
\begin{array}{c|r|c|c}
e&\deg E_e&(l,r)&(V_e(l),V_e(r))\\ \hline
\Delta&16&(8/5,11/5)&(4,3)\\
\Delta&16&(1838/1000,1839/1000)&(4,3)\\
z-282&16&(8/5,11/5)&(5,4)\\
z-282&16&(1995/1000,1996/1000)&(5,4)\\
z-400&16&(8/5,11/5)&(5,5)\\
m-700&16&(1838/1000,1954/1000)&(3,3)\\
m-800&16&(1896/1000,2171/1000)&(2,2)\\
e_m&34&(3/2,11/5)&(13,13).
\end{array}                                                     \tag{29.17}
$$

所有端点均不是相应多项式的根。表中的 $\Delta$ 唯一根还位于 (29.12) 的窄区间；$z-282$ 的唯一根 $\rho$ 位于

$$
19954703303/10^{10}<\rho<19954703304/10^{10}.
\tag{29.18}
$$

这两个窄区间的相应变号数对仍分别是 $(4,3)$、$(5,4)$。这些是由显示多项式及余式定义完全确定的有理符号证书，不使用浮点根作为计数依据。

在 (29.12) 的整个闭包上，代入 $n_-$ 并作有理区间运算给 $-14<\Delta<-13$。因此消元式的该唯一零点只能在 $n_+$ 上；由 (29.10) 它落在 $\alpha_0<u<\gamma_0$，且 (29.13) 的两个根均为实根。于是 $\mathcal S_+$ 恰有这一极点，$\mathcal S_-$ 没有极点。∎

**定理 29.4（分支内严格单调与分支间响应分离）。** 将 $\mathcal S_+$ 按 $u<\sigma$、$u>\sigma$ 分为 $\mathcal S_+^{<},\mathcal S_+^{>}$。在以下三个连通来源区间上，$m$ 都对 $u$ 严格递增；其联合响应满足

$$
\begin{array}{c|c}
\text{来源}&\text{响应约束}\\ \hline
\mathcal S_-&z<282,\quad m>800\\
\mathcal S_+^{<}&z>400\\
\mathcal S_+^{>}&z<282,\quad m<700.
\end{array}                                                     \tag{29.19}
$$

证明。在各区间上，$F_n\ne0$，且 $A,c_2,\Delta$ 均不为零。隐式求导给

$$
\frac{dm}{du}=\frac{m_uF_n-m_nF_u}{F_n}=\frac{e_m}{F_n}.
\tag{29.20}
$$

所有合法 $u$ 都在 $(3/2,11/5)$ 内。(29.17) 最后一行排除导数零点，故导数在每个区间内符号不变。在 $\mathcal S_-,\mathcal S_+^{<},\mathcal S_+^{>}$ 上分别取 $u=2,17/10,19/10$，严格有理包围给

$$
\begin{array}{c|c|c|c}
\text{来源及 }u&z&m&dm/du\\ \hline
\mathcal S_-,\ 2&(277,278)&(920,921)&(1092,1094)\\
\mathcal S_+^{<},\ 17/10&(458,459)&(754,755)&(2774,2775)\\
\mathcal S_+^{>},\ 19/10&(237,238)&(417,418)&(7107,7109).
\end{array}                                                     \tag{29.21}
$$

于是三个区间内均严格递增。式 (29.17) 的 $m-800$ 行与 $m-700$ 行分别覆盖整个 $\mathcal S_-$ 和 $\mathcal S_+^{>}$ 的 $u$ 区间，故结合 (29.21) 得这两支的 $m$ 界。$z-400$ 行覆盖全部合法来源，结合 $u=17/10$ 得 $\mathcal S_+^{<}$ 的 $z>400$。$\mathcal S_+^{>}$ 的 $u<\gamma_0<1954/1000$，不包含 $z-282$ 唯一候选根 $\rho$，故 (29.21) 给其 $z<282$。

对 $\mathcal S_-$，唯一须另查的候选根是 (29.18) 的 $\rho$。在该整个闭包上，代入 $n_-$ 的有理区间运算给 $277<z<279$，故实际 $z-282$ 不为零。其消元根属于另一个代数根，而非这个合法分支。于是 $\mathcal S_-$ 全区间上也没有 $z=282$，由 (29.21) 得 $z<282$。这里没有把消元根自动认作合法来源。

上述根式包围可全部用有理数完成：在显示的 $u$ 区间中对 $A,c_i,\mathcal Q$ 作 Horner 运算；对正的 $\mathcal Q$ 取分母 $10^{30}$、由有理数平方比较确定的上下平方根界；依 (29.9)、(29.1)、(29.5)、(29.20) 逐项组合。所有除数区间排除零。这个规则同时给出 (29.15) 的样本符号和 (29.21) 的严格包围。∎

**定理 29.5（单次 J 仍有实际非零漂移碰撞）。** 存在两个不同的 $H^-$ 兼容世界，其漂移都非零，第六动作 $J$ 的实际读数同为 $270$。两者分别属于 $\mathcal S_+^{>}$ 和 $\mathcal S_-$，但它们的后续 $M$ 读数不同。

证明。分别在 $n_+$ 分支的 $u\in[1940/1000,1941/1000]$、$n_-$ 分支的 $u\in[2057/1000,2058/1000]$ 上使用 (29.5)。两段严格包含于各自合法区间，且不含极点。有理平方根包围分别给

$$
\begin{array}{c|c|c}
\text{分支}&z(\text{左端})&z(\text{右端})\\ \hline
n_+&(269,270)&(270,271)\\
n_-&(270,271)&(269,270).
\end{array}                                                     \tag{29.22}
$$

连续性分别供应一个 $z=270$ 的实际来源。这两段的 $R$ 分别严格为正、严格为负；$h>0,\Delta\ne0$ 使 $d=6hR/(5\Delta)\ne0$。定理 29.2 供应各自唯一的整个增益和常漂移，因此它们满足全部同一祖先约束。由 (29.19)，前者 $m<700$，后者 $m>800$，故确为不同完整目标，且随后 $M$ 将它们区分。这个碰撞不供应同一 $J$ 子纤维的末 $M$ 失败。∎

**定理 29.6（整个父纤维的固定 JM 八读恢复）。** 在 $\mathcal F(H^-)$ 上，原时钟六、七固定执行 $J,M$ 所得的联合读数 $(z,m)$ 为单射。因此

$$
\begin{gathered}
\forall z\in\mathbb R,\qquad
\neg L_1(\mathcal F(H^-,J,z),(H^-,J,z)),\\
\forall K\subseteq\mathcal F(H^-),\qquad \neg L_2(K,H^-).
\end{gathered}                                                   \tag{29.23}
$$

证明。先看 $R=0$ 分支。定理 29.2 给 $d=0$，且来源恰为 (29.8) 的 $P_s$。整个增益为 $f_{012}/n(s)$，第六 $J$ 响应为

$$
z_0(s)=240+\frac{120}{n(s)},\qquad
n'(s)=-\frac{100+440s+600s^2}{(7+40s+46s^2)^2}<0.
\tag{29.24}
$$

因此 $z_0$ 严格递增，准确像为 $(282,1476/5)$，单独这个读数就恢复该分支的完整世界。

其余世界必须满足 $\Phi=0$，由定理 29.3 恰落在三个去极点来源区间中。定理 29.4 的 $z$ 界使它们全部与零漂移分支分离，也把 $\mathcal S_+^{<}$ 与另外两支分离。$\mathcal S_-$ 和 $\mathcal S_+^{>}$ 再由 $m>800$、$m<700$ 分离。每个区间内部的 $m$ 严格递增，故联合响应在其内部单射。定理 29.2 将唯一来源坐标提升为唯一完整 $(P,g,d)$，得到整个纤维的单射。此论证也说明两个方程分支在兼容世界域内没有被重复计数的交点。

固定第六 $J$ 响应后，第七 $M$ 在整个剩余纤维上单射，因此没有任何实际 $m$ 子纤维含两个不同完整目标。原递归 (1.1) 的 $L_1$ 所需末 $M$ 条款随之失败，给 (29.23) 第一行。对子集 $K$ 同样成立；原 $L_2$ 的第六 $J$ 存在条款因此失败，给第二行。早停不会补回这个缺失条款。

恢复可按响应区间选定分支，再使用 (29.24) 或严格单调的 $m$ 的像上逆，最后调用 (29.9)、(29.1)、(29.3)。它是定义 1.1 的精确实响应合同中的确定性恢复；不增加有限精度、稳定性或实数比较算法的结论。初读和每个原子后的读数照常计数，没有重置、复制、跳读或反事实结果合并。∎

**约定 29.7（供应关系与原根边界）。** 这里的全部源域、完整目标及含早停递归直接由定义 1.1 供应；(28.25) 供应同一个实际父历史，(28.23)–(28.26) 的 $M$ 分支失败继续成立。定理 29.6 将 (28.26) 右端的 $J$ 分支存在断言判为假，因此该固定父不能供应两层失败。四迹逆、有限插值、Sturm 实根计数和有理区间算术均作为成熟中间工具使用，不另列为新增成果。承重的仓内综合内容是整个父纤维的正来源分支穷尽、实际响应分离及固定 $JM$ 恢复，不申领外部文献优先权。

定理 29.5 说明单次 $J$ 的非零漂移来源投影确实非单射；这与两次联合响应恢复并不冲突。定理 28.4 的七读末步失败相图也不被否定：先在原时钟五选择 $M$ 或 $J$，会到达不同的实际历史。当前固定 $H^-$ 的八读恢复，不证明原根所有历史均可八读恢复，不构造原根初始 $M$ 的六层失败，也不排除其他父历史的两层失败。实际 $JMJ$ 四层失败、原根八读与至少九读之分及九读上界仍保留各自的共同祖先证明义务。

## 追加锚（本行以下为增补区）

## 30. 整段参数父族的完整坐标与固定 JJ 恢复

**定义 30.1（同参数的六读父族）。** 保留定义 1.1 的整个来源域、完整目标和原时钟。对

$$
\theta\in I=[13/8,5/3],\qquad
H^-_\theta=(0,M,0,M,0,J,6,M,24\theta,M,60(1+\theta)),
\tag{30.1}
$$

使用 (29.1) 的 $u,n,a,h,\ell,A,B_1,\Delta,D,\Phi$ 及显示源矩阵，置

$$
\begin{gathered}
r=\theta n-a,\quad K_\theta=5a\ell+(5-20\theta)h,\\
V=10u^2+19u-36,\quad X=20u^2+34u-70,\quad C_\theta=210(1+\theta),\\
L=4(n+a)X-35a\ell-171h.
\end{gathered}                                                   \tag{30.2}
$$

这里 $r$ 是标量残差，不是源矩阵的分量。$\mathcal S_-,\mathcal S_+$、端点 $\alpha_0,\beta_0,\gamma_0,\eta_0$ 及极点 $\sigma$ 全部沿用定理 29.3，因其定义没有 $\theta$。

**定理 30.2（整个参数父纤维与无退化除数）。** 对每个 $\theta\in I$，$\mathcal F(H^-_\theta)$ 与满足

$$
P(u,n,a)>0\text{ 逐项},\qquad D=0,\qquad \Delta\ne0,\qquad r\Phi=0
\tag{30.3}
$$

的三元组一一对应。原始父方程没有 $\Delta=0$ 的解；其余完整目标由

$$
d=\frac{24hr}{\Delta},\qquad
(g(0),g(1),g(2),g(3))
=(-d,-d/u,-d/(1+u),(6-d)/n)
\tag{30.4}
$$

的唯一至多三次插值恢复。第六、七动作固定为 $J,J$ 时，实际新读数为

$$
\begin{gathered}
g_6=\frac{24(K_\theta+rV)}{\Delta},\qquad
g_7=\frac{42K_\theta+24rX}{\Delta},\\
z=d+(1+2n)g_6,\qquad j=d+(n+a)g_7,\\
\boxed{\quad j-C_\theta=\frac{6rL}{\Delta}.\quad}
\end{gathered}                                                   \tag{30.5}
$$

证明。前三个零读数与时钟三的六给出 (30.4) 的插值节点。保持前三次实际动作，时钟四的方程准确为 $d\Delta=24hr$；若 $\Delta\ne0$，时钟五的读数残差为 $12r\Phi/\Delta$。这与 (29.7) 的推导相同，只保留自由参数而不代入 $33/20$。

先处理不能预先删除的 $\Delta=0$ 截面。第四方程迫使 $r=0$。任意正秩一迹一源唯一写成

$$
P_s=\frac1{1+sv}\begin{pmatrix}1&v\\s&sv\end{pmatrix},\qquad s,v>0.
$$

条件 $a=\theta n$ 等价于

$$
\begin{gathered}
v=\frac{(\theta-1)+(2\theta-1)s}{(2-\theta)+(3-\theta)s},\quad
D_s=(2-\theta)+2s+(2\theta-1)s^2,\\
n(s)=\frac{1+5s+5s^2}{D_s},\\
u-1=\frac{(3-\theta)s^2+(2\theta-2)s+2\theta-3}{D_s}>0,\\
2-u=\frac{(3\theta-4)s^2+(4-2\theta)s+5-3\theta}{D_s}>0,\\
3-n=\frac{(6\theta-8)s^2+s+5-3\theta}{D_s}>0.
\end{gathered}                                                   \tag{30.6}
$$

全部分母为正；各分子系数非负，并有严格正项，端点 $\theta=5/3$ 也不例外。故 $1<u<2,n<3$，从而 $0<\ell/h<1$，且

$$
\frac{\Delta}{nh}=1+\theta\frac{n\ell}{h}-4\theta
<1-\theta<0.                                                   \tag{30.7}
$$

这与 $\Delta=0$ 矛盾。于是第四方程可除，第五方程等价于 (30.3)。反向，同一插值供应六个祖先读数；时钟零和时钟三的不同读数排除 $g=0$。唯一插值确定整个 $g$，不只是采样值。沿 $MMJMMJJ$ 的最后两迹为 $1+2n,n+a$，直接插值给 $g_6,g_7$。将 (30.2) 展开，$\Delta(j-C_\theta)-6rL$ 恒为零，最后一个恒等式不额外要求 $\Phi=0$。∎

**定理 30.3（完整来源曲线上的统一响应分离）。** 对所有 $\theta\in I$，函数 $j$ 在 $\mathcal S_-,\mathcal S_+^{<},\mathcal S_+^{>}$ 各自随 $u$ 严格递增。在这些来源上，

$$
\begin{array}{c|c}
\text{来源范围}&\text{统一约束}\\ \hline
\mathcal S_-&L>0,\quad\Delta<0,\quad z<300\\
\mathcal S_+^{<}&L>0,\quad\Delta>0,\quad a/n<3/2,\quad z>400,\quad j>C_\theta\\
\mathcal S_+^{>}&L>0,\quad\Delta<0,\quad a/n<3/2,\quad z<279,\quad j<C_\theta\\
\mathcal S_-\text{ 且 }j<C_\theta&u<48/25,\quad z>279.
\end{array}                                                     \tag{30.8}
$$

证明。两条曲线、正性范围与唯一极点复用定理 29.3。全部端点和极点独立于参数。在 $\Phi=0$ 上作 (29.13) 的 $a$ 代换，对 (30.5) 的 $z,j$ 采用 (29.16) 的消元约定；仍记其 Sturm 变号数为 $V_e$。令

$$
e_j=j_uF_n-j_nF_u,\qquad \frac{dj}{du}=\frac{e_j}{F_n}.
\tag{30.9}
$$

所用有理符号证书如下；有限小数均表示精确有理端点。

$$
\begin{array}{c|c|r|c|c}
\theta&e&\deg E_e&(l,r)&(V_e(l),V_e(r))\\ \hline
\text{无关}&L&10&(1.6,2.2)&(2,2)\\
\text{无关}&a-3n/2&6&(1.6,2.2)&(1,1)\\
\text{无关}&a-5n/3&6&(1.92,2.171)&(1,1)\\
13/8&e_j&34&(1.649,2.171)&(15,13)\\
13/8&e_j&34&(1.71435952234,1.71435952235)&(15,14)\\
13/8&e_j&34&(2.15222927621,2.15222927622)&(14,13)\\
5/3&e_j&34&(1.649,2.171)&(16,15)\\
5/3&e_j&34&(2.15503296651,2.15503296652)&(16,15)\\
13/8&z-300&16&(1.6,2.2)&(5,5)\\
5/3&z-300&16&(1.6,2.2)&(4,4)\\
13/8,5/3&z-400&16&(1.6,2.2)&(5,5)\\
13/8,5/3&z-279&16&(1.838,1.954)&(5,5)\\
13/8,5/3&z-279&16&(1.896,1.920)&(5,5).
\end{array}                                                     \tag{30.10}
$$

无关行没有 $\theta$；逗号行表示两个参数分别具有同一变号数对。全部端点非根。所有实际来源都在 $(1.649,2.171)$ 中，故表中 $e_j$ 的三个窄区间穷尽两端参数的候选导数零点。不能直接把这些消元根认作合法分支的零点：在三个窄区间整个闭包上，唯一合法的分支及其导数严格包围分别为

$$
\begin{array}{c|c|c}
\theta&\text{对应合法分支}&dj/du\\ \hline
13/8,\ u\approx1.71435952234&n_+&(1605,1606)\\
13/8,\ u\approx2.15222927621&n_-&(270,271)\\
5/3,\ u\approx2.15503296651&n_-&(281,282).
\end{array}                                                     \tag{30.11}
$$

另一根式分支在相应整个小区间不满足源正性，由 (29.10)—(29.11) 即知。因此这些候选根都没有给合法来源的导数零点。根式包围使用定理 29.4 末段的同一有理平方比较规则，分母均排除零。每个来源区间上的样本包围为

$$
\begin{array}{c|c|c|c|c}
\theta&\text{来源及 }u&z&j&dj/du\\ \hline
13/8&\mathcal S_+^{<},1.7&(453,454)&(681,682)&(1398,1399)\\
13/8&\mathcal S_+^{>},1.9&(239,240)&(303,304)&(4832,4833)\\
13/8&\mathcal S_-,2&(276,277)&(589,590)&(382,383)\\
5/3&\mathcal S_+^{<},1.7&(461,462)&(696,697)&(1482,1483)\\
5/3&\mathcal S_+^{>},1.9&(235,236)&(284,285)&(5207,5209)\\
5/3&\mathcal S_-,2&(278,279)&(590,591)&(405,406).
\end{array}                                                     \tag{30.12}
$$

连续性、无合法导数零点及这些正样本给两个端点参数的严格递增。响应公式对 $\theta$ 仿射，来源曲线不随参数改变，故沿曲线的导数也对 $\theta$ 仿射；端点导数的凸组合给整个闭参数区间的严格递增。

由 (30.10) 的首行，$L$ 在两条曲线上无零点；在 $\mathcal S_+^{<}$ 的 $u=1.7$ 处 $67<L<68$，在 $\mathcal S_-$ 的 $u=2$ 处 $281<L<282$。$L$ 本身在 $\sigma$ 处仍连续，故正号覆盖整个 $\mathcal S_+$。$a-3n/2$ 同样无零点，$u=1.7$ 的 $n_+$ 分支给 $-4<a-3n/2<-3$，于是整个 $\mathcal S_+$ 有 $a/n<3/2$。$\Delta$ 的唯一零点及正负样本给 (30.8) 的符号。因 $\theta\ge13/8>3/2$，$\mathcal S_+$ 上 $r>0$，(30.5) 随之给两侧的 $j-C_\theta$ 符号。

表中 $z-300,z-400$ 在两端参数均无候选零点，样本 (30.12) 给整个 $\mathcal S_-$ 的 $z<300$ 和整个 $\mathcal S_+^{<}$ 的 $z>400$。$z-279$ 的第一条区间覆盖 $\mathcal S_+^{>}$，$u=1.9$ 的样本给该支 $z<279$。对 $\mathcal S_-$ 的短段 $\beta_0<u<1.92$，第二条区间无根，且 $u=1.91$ 时两个端点参数的 $z$ 分别在 $(280,281)$、$(281,282)$，故短段有 $z>279$。这些严格响应界也由参数仿射性延伸到整个 $I$。

最后，$\mathcal S_-$ 上 $j<C_\theta$ 与 $L>0,\Delta<0$ 强制 $r>0$，所以 $a/n<\theta\le5/3$。但是 (30.10) 的 $a-5n/3$ 行在 $1.92<u<\eta_0$ 无零点，而 $u=2$ 的样本给 $0<a-5n/3<1$。因此该区域不容 $r>0$；在 $u=1.92$ 也不为零且同号。必有 $u<1.92$，再用短段响应界完成 (30.8)。∎

**定理 30.4（整个参数父族的固定 JJ 八读恢复）。** 对所有 $\theta\in[13/8,5/3]$，固定执行第六、七动作 $J,J$ 的联合响应 $(z,j)$ 在整个 $\mathcal F(H^-_\theta)$ 上单射。因此

$$
\begin{gathered}
\forall z\in\mathbb R,\quad
\neg L_1(\mathcal F(H^-_\theta,J,z),(H^-_\theta,J,z)),\\
\forall K\subseteq\mathcal F(H^-_\theta),\quad
\neg L_2(K,H^-_\theta).
\end{gathered}                                                   \tag{30.13}
$$

证明。先看 $r=0$。定理 30.2 给 $d=0$，整个 $g=f_{012}/n(s)$；在 (30.6) 的坐标中

$$
z_0(s)=240+\frac{120}{n(s)},\quad j_0=C_\theta,\quad
n'(s)=\frac{(8-5\theta)+(22-14\theta)s+(15-10\theta)s^2}{D_s^2}<0.
\tag{30.14}
$$

所以 $z_0$ 严格递增，准确像为 $(480-120\theta,216+48\theta)$，在零漂移分支单独恢复完整世界。

其余来源位于定理 29.3 的三段曲线上，每段内部 $j$ 严格递增。$\mathcal S_-$ 与 $\mathcal S_+^{<}$ 由 $z<300$ 和 $z>400$ 分离；$\mathcal S_+^{<}$ 与 $\mathcal S_+^{>}$ 由 $j>C_\theta$ 和 $j<C_\theta$ 分离。比较 $\mathcal S_-$ 与 $\mathcal S_+^{>}$，若前者 $j\ge C_\theta$，两者的 $j$ 不同；若前者 $j<C_\theta$，(30.8) 给它 $z>279$，后者却 $z<279$。因此三段的联合响应彼此分离。

若曲线上某世界与零漂移世界有相同 $z,j$，则 $j=C_\theta$，由 $L>0,\Delta\ne0$ 及 (30.5) 得 $r=0$，它本身已在零漂移分支中；再由同一个 $z$ 的单射性，两者是同一完整世界。曲线与零漂移方程的交点只计作同一来源，不能把分支接合重复计成碰撞。以上证明联合响应对全部合法坐标单射，定理 30.2 再恢复整个 $(P,g,d)$。

固定第六 $J$ 的实际响应后，第七 $J$ 在其整个子纤维上单射，故原 $L_1$ 要求的末 $J$ 非单点子纤维不存在。对子集仍然成立，于是任何 $L_2$ 所需的第六 $J$ 存在条款都失败，给 (30.13)。这个证明无需要求两种末动作共用一个碰撞对，也不改变含早停递归。恢复只用一条真实 $JJ$ 接续，不同时汇集互择动作的反事实读数。∎

**约定 30.5（参数族排除的消费者与边界）。** 当 $13/8<\theta<5/3$，定理 28.4 供应第六 $M$ 的指定七读子历史的 $L_1$，该结论保持原范围；定理 30.4 同时排除同一个六读父的全部第六 $J$ 子历史的 $L_1$。因而沿这整族父历史加入更多兼容源、漂移或整个至多三次增益，都不能补成 $L_2$。在 $\theta=33/20$ 处，定理 29.6 的固定 $JM$ 与这里的固定 $JJ$ 都是合法八读恢复，并不互相替代或冲突。

来源正性分类与极点穷尽直接消费定理 29.3；四迹逆、有限插值、Sturm 计数、根式有理包围及仿射函数的端点控制均为成熟工具。这里的 repo-derived 增量是闭参数区间上的完整父纤维、跨分支统一分离及其原失败递归消费者，不申领这些工具或外部文献优先权。

本章的恢复仍是原精确实响应合同中的像上逆；没有推出有限精度、稳定性或实数比较算法。整族父被排除，不等于所有初始 $M$ 历史被排除，也不证明原根的八读策略存在。实际 $JMJ$ 的 $L_4$、原根初始 $M$ 的 $L_6$、原根八读与至少九读之分及九读上界，仍保留各自的共同祖先和完整策略义务。∎

## 追加锚（本行以下为增补区）

## 31. 低参数父族的无除数坐标与全部已知碰撞相的接续排除

**定义 31.1（低参数的同父问题）。** 保留定义1.1的完整世界、原时钟和失败递归，令

$$
I_-=[7/10,27/25],\qquad
H^-_\theta=(0,M,0,M,0,J,6,M,24\theta,M,60(1+\theta)).
\tag{31.1}
$$

沿用(29.1)的源矩阵 $P(u,n,a)$、$D,h,\ell,\Delta,\Phi$，及(30.2)的 $r,K_\theta,V,X,L,C_\theta$。第六、七动作固定为 $J,J$，实际读数记 $z,j$。合法来源仍为整个严格正秩一迹一域，不把第30章的 $1<u<2,n<3$ 移用于本区间。

**定理 31.2（无除数父坐标与零漂移的保留）。** 对每个 $\theta\in I_-$，整个 $\mathcal F(H^-_\theta)$ 与下列四元组一一对应：

$$
P(u,n,a)>0\text{ 逐项},\quad D=0,\quad
d\Delta=24h(\theta n-a),\quad d\Phi=0.
\tag{31.2}
$$

其完整增益是(30.4)四个节点的唯一至多三次插值。全部父世界满足

$$
\boxed{\quad j-C_\theta=\frac{dL}{4h}.\quad}
\tag{31.3}
$$

非零漂移世界必有 $\Phi=0,\Delta\ne0$，故可用(30.4)—(30.5)恢复；零漂移世界则由 $a=\theta n,g=f_{012}/n$ 描述，不要求 $\Delta\ne0$。

证明。正来源给 $u,n,h>0$。令 $\Gamma$ 为四节点插值，设 $E=d\Delta-24h(\theta n-a)$；在原时钟四、五的读数残差分别为

$$
a\Gamma(4)+d-24\theta=\frac{E}{nh},\qquad
(n+a)\Gamma(5)+d-60(1+\theta)=\frac{5E}{2nh}+\frac{d\Phi}{2h}.
\tag{31.4}
$$

这是有限插值的恒等式，故必要且充分地给(31.2)，没有先除 $\Delta$。四迹逆保留全部来源；时钟零、三的不同读数排除零多项式，所以确为完整世界的双射。另由

$$
\Gamma(7)=\frac{210}{n}+d\left(\frac Xh-\frac{35}{n}\right),\quad
j-C_\theta-\frac{dL}{4h}=\frac{35E}{4nh}
\tag{31.5}
$$

得到(31.3)，包括 $\Delta=0$ 的来源。

若 $d\ne0$，则 $\Phi=0$。定理29.3已穷尽全部正 $\Phi$ 来源及唯一 $\Delta$ 零点 $(\sigma,n_+(\sigma),a_+(\sigma))$。将(29.12)代入(29.9)，按定理29.4的有理根式包围规则得到

$$
1.1049<\frac{a_+(\sigma)}{n_+(\sigma)}<1.105.
\tag{31.6}
$$

若 $\Delta=0$，(31.2)还迫 $\theta=a/n$，与 $\theta\le1.08$ 矛盾。因此非零漂移部分可除。若 $d=0$，同式只迫 $r=0$，不能额外删除 $\Delta=0$ 的零漂移来源；节点插值此时就是 $f_{012}/n$。∎

**定理 31.3（低参数三段来源的统一分离）。** 对每个 $\theta\in I_-$，在定理29.3的三段正来源曲线上，$z$ 随 $u$ 严格递减，并且

$$
\begin{array}{c|c}
\mathcal S_+^{<}&j<530\\
\mathcal S_-&j>540,\quad z<270\\
\mathcal S_+^{>}&j>540,\quad z>280.
\end{array}
\tag{31.7}
$$

证明。在 $\Phi=0,\Delta\ne0$ 上采用(30.5)的 $z,j$，令 $e_z=z_uF_n-z_nF_u$，沿曲线有 $dz/du=e_z/F_n$。用(29.16)的同一个消元及 Sturm 约定，有限小数均作精确有理数，得到

$$
\begin{array}{c|c|r|c|c}
\theta&e&\deg E_e&(l,r)&(V_e(l),V_e(r))\\ \hline
7/10&e_z&34&(1.649,2.171)&(13,12)\\
7/10&e_z&34&(2.13702290115,2.13702290116)&(13,12)\\
27/25&e_z&34&(1.649,2.171)&(12,11)\\
27/25&e_z&34&(2.08731133528,2.08731133529)&(12,11)\\
7/10&j-530&16&(1.649,1.839)&(6,6)\\
27/25&j-530&16&(1.649,1.839)&(5,5)\\
7/10&j-540&16&(1.838,2.171)&(6,6)\\
27/25&j-540&16&(1.838,2.171)&(4,4)\\
7/10,27/25&z-270&16&(1.896,2.171)&(5,5)\\
7/10&z-280&16&(1.838,1.954)&(6,6)\\
27/25&z-280&16&(1.838,1.954)&(5,5).
\end{array}
\tag{31.8}
$$

所有端点非根。两个窄区间分别穷尽对应端参数的候选导数零点；它们都在 $\gamma_0<u<\eta_0$，唯一合法分支为 $n_-$。在整个闭区间的有理根式包围分别给

$$
-214<dz/du<-213\quad(\theta=7/10),\qquad
-203<dz/du<-202\quad(\theta=27/25).
\tag{31.9}
$$

另一根式分支的 $P_{11}<0$。所以消元根没有产生合法导数零点。各段上的符号样本为

$$
\begin{array}{c|c|c|c|c}
\theta&\text{来源及 }u&z&j&dz/du\\ \hline
7/10&\mathcal S_+^{<},1.7&(261,262)&(350,351)&(-510,-509)\\
7/10&\mathcal S_+^{>},1.9&(338,339)&(732,733)&(-1450,-1448)\\
7/10&\mathcal S_-,2&(233,234)&(565,566)&(-215,-214)\\
27/25&\mathcal S_+^{<},1.7&(340,341)&(486,487)&(-287,-286)\\
27/25&\mathcal S_+^{>},1.9&(298,299)&(556,557)&(-268,-267)\\
27/25&\mathcal S_-,2&(251,252)&(575,576)&(-168,-167).
\end{array}
\tag{31.10}
$$

连续性与无合法导数零点给两端参数的严格递减。其余无根区间分别覆盖所需连通来源段，样本给(31.7)。来源曲线及 $\Delta$ 独立于 $\theta$，响应及沿曲线导数对 $\theta$ 仿射；对端点函数值与导数取凸组合，遂给整个闭参数区间的严格不等式。不对消元根数作参数插值。∎

**定理 31.4（低参数完整恢复与两碰撞相的同父排除）。** 对每个 $\theta\in I_-$，固定原时钟六、七执行 $J,J$ 的联合响应 $(z,j)$ 在整个 $\mathcal F(H^-_\theta)$ 上单射。因此

$$
\forall K\subseteq\mathcal F(H^-_\theta),\qquad \neg L_2(K,H^-_\theta).
\tag{31.11}
$$

证明。非零漂移来源只落在定理31.3的三段上；每段内 $z$ 单射，$j<530$ 与 $j>540$ 分开第一段和其余两段，$z<270$ 与 $z>280$ 再分开后两段。同一来源的 $d$ 及整个 $g$ 由31.2唯一确定。

零漂移来源唯一写成(30.6)的 $P_s$，只保留 $s>0,v(s)>0$。在 $I_-$，$v(s)$ 的分母严格正，故合法 $s$ 域是一个开区间：$\theta<1$ 时为 $s>(1-\theta)/(2\theta-1)$，$\theta\ge1$ 时为 $s>0$。同式的 $D_s>0$，且

$$
n'(s)=\frac{(8-5\theta)+(22-14\theta)s+(15-10\theta)s^2}{D_s^2}>0.
\tag{31.12}
$$

三个分子系数均严格正，故 $z_0=240+120/n(s)$ 严格递减，$j_0=C_\theta$，在零漂移部分单射。若非零漂移世界与它同读，则(31.3)迫 $dL=0$；定理30.3的 $L>0$ 只依赖同一正 $\Phi$ 来源曲线，与参数无关，故矛盾。零漂移源即使满足 $\Phi=0$ 也只算同一个世界，没有把两份坐标描述重复计成碰撞。这证明全纤维单射。固定第六 $J$ 的任意实际响应后，第七 $J$ 都恢复其整个子纤维，所以该子纤维不支持 $L_1$；对子集仍然如此，得(31.11)。

结合定理28.4的全部参数相图与定理30.4，进一步有

$$
L_1(\mathcal F(H_\theta),H_\theta)
\ \Longrightarrow\
\neg L_2(\mathcal F(H^-_\theta),H^-_\theta)
\quad(\theta\in\mathbb R).
\tag{31.13}
$$

因为相图中的低参数相包含于 $I_-$，高参数相包含于 $[13/8,5/3]$。这排除用任一已知指定末 $M$ 碰撞相补成其同父两层失败；不声称其余参数下所有其他 $M$ 响应都已检查，更不把这一模板推广为原根初始 $M$ 的全部历史分类。实际 $JMJ$ 的 $L_4$、初始 $M$ 的 $L_6$、原根八读／九读判别及九读上界仍需各自完整策略与共同祖先证明。恢复采用原精确实响应合同，不增加有限精度、稳定性或实数比较算法结论。

31.2直接消费29.3的全部正来源及唯一极点；31.3消费其消元约定和30.3的参数无关正性；有限插值、Sturm实根计数、有理根式包围和仿射端点控制均沿用29—30章所列成熟工具。新增承重是低参数完整父纤维的接合、统一单射及两种碰撞机制在同父递归中的共同排除，属本仓综合推导（repo-derived），不申领外部工具或文献优先权。∎

## 追加锚（本行以下为增补区）
