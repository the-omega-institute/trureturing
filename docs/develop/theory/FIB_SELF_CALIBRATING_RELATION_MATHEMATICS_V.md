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
