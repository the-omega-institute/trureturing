# 平方 Zeckendorf 奇偶序列的反馈寄存器下界与多项式猜想反例

**定义 1（规范坐标、Lucas 数与平方抽样）。** 记 $\mathbb N_0=\{0,1,2,\ldots\}$，并定义

$$
F_0=0,\quad F_1=1,\quad F_{r+2}=F_{r+1}+F_r,
\qquad
L_0=2,\quad L_1=1,\quad L_{r+2}=L_{r+1}+L_r.
$$

一个有限集合 $D\subseteq\{2,3,\ldots\}$ 称为规范支撑，当且仅当它不含两个相邻整数。对每个 $x\in\mathbb N_0$，以 $Z(x)$ 表示满足

$$
x=\sum_{r\in Z(x)}F_r
$$

的唯一规范支撑，令 $s_Z(x)=|Z(x)|$。特别地，$Z(0)=\varnothing$，$s_Z(0)=0$，$Z(1)=\{2\}$。本文的二元序列从样本下标零开始：

$$
S(n)=s_Z(n^2)\bmod 2,\qquad n\in\mathbb N_0.
$$

这里仅允许下标至少为二的权重，因而单位权重是 $F_2=1$，下一权重是 $F_3=2$。这与 Jamet–Popoli–Stoll 的 Definition 5 中以 $F_{j+2}$ 为权重的坐标完全相同；该文的 $\varepsilon_j(x)$ 等于这里的 $\mathbf1_{\{j+2\in Z(x)\}}$。[Jamet–Popoli–Stoll, *Maximum order complexity of the sum of digits function in Zeckendorf base and polynomial subsequences*, Definition 5, Cryptography and Communications **13** (2021), 791–814, DOI: [10.1007/s12095-021-00507-w](https://doi.org/10.1007/s12095-021-00507-w)。]

规范表示的存在唯一性是通常的 Zeckendorf 定理；以下基本论证也固定本文所需的边界。令 $B_r$ 是规范支撑包含于 $\{2,\ldots,r\}$ 时的最大权重和，并约定 $B_1=0$。有 $B_2=1$，且对 $r\ge3$，按是否含有 $r$ 分解得到

$$
B_r=\max\{B_{r-1},F_r+B_{r-2}\}=F_{r+1}-1,
$$

最后一个等号由 $B_1=F_2-1$、$B_2=F_3-1$ 归纳得到。对 $x>0$，取最大的 $r\ge2$ 使 $F_r\le x$，则

$$
0\le x-F_r<F_{r+1}-F_r=F_{r-1}.
$$

对 $x$ 作强归纳，余数已有规范表示；若余数非零，其支撑中每个下标都至多为 $r-2$，所以加上 $r$ 仍然规范。余数为零时直接取 $\{r\}$。这证明存在性。若两种表示不同，取消共同的较大下标，并取最大的相异下标 $r$；含有 $r$ 的一侧至少为 $F_r$，另一侧至多为 $B_{r-1}=F_r-1$，矛盾。存在唯一性亦见 [Zeckendorf, *Représentation des nombres naturels par une somme de nombres de Fibonacci ou de nombres de Lucas*, Bulletin de la Société Royale des Sciences de Liège **41** (1972), 179–182]；同一规范坐标在仓内对应 [WDigits 的 `wdigits_isCanonical`、`decode_wdigits`、`wdigits_unique`](https://github.com/the-omega-institute/trureturing/blob/8b9b65f4a2eb01e267a4704da33fd01b022ffaa7/D5/S0/Conventions/WDigits.lean)。

**定义 2（原始反馈多项式复杂度）。** 设 $T=(T(n))_{n\ge0}$ 是取值于 $\{0,1\}=\mathbb F_2$ 的序列，$N\ge2$ 是整数。如果 $(T(0),\ldots,T(N-2))$ 非常值，定义 $M(T,N)$ 为满足下列条件的最小正整数 $m$：存在

$$
f\in\mathbb F_2[X_1,\ldots,X_m]
$$

使得对每一个整数起点 $a$ 都有

$$
T(a+m)=f\bigl(T(a),\ldots,T(a+m-1)\bigr),
\qquad 0\le a\le N-m-1.
\tag{2.1}
$$

该最小值存在：取 $m=N-1$ 以及常值多项式 $f=T(N-1)$ 即可。若存在 $b\in\{0,1\}$ 使 $T(0)=\cdots=T(N-2)=b$，则分别定义

$$
M(T,N)=
\begin{cases}
0,&T(N-1)=b,\\
N-1,&T(N-1)\ne b.
\end{cases}
\tag{2.2}
$$

这保留了两个常值前缀分支，以及所有合法起点上的同一个反馈多项式。[Jamet–Popoli–Stoll, Definition 1；[arXiv:2106.09959v1](https://arxiv.org/abs/2106.09959v1), Definition 1，与上述出版社版本 Definition 1。]

**定义 3（完整多项式猜想的量词）。** 令 $\mathcal A$ 是所有满足下列条件的多项式组成的集合：$P\in\mathbb Z[X]$ 为首一多项式，$d=\deg P\ge2$，且 $P(\mathbb N_0)\subseteq\mathbb N_0$。记

$$
S_{Z,P}(n)=s_Z(P(n))\bmod2,\qquad n\ge0.
$$

以 $\mathcal C$ 表示命题

$$
\begin{aligned}
\forall P\in\mathcal A\quad
&\exists c_P>0\ \exists C_P>0\ \exists N_P\in\mathbb N,\quad N_P\ge2,\\
&\forall N\in\mathbb N,\quad
N\ge N_P\ \Longrightarrow\quad
c_P N^{1/(2\deg P)}\le M(S_{Z,P},N)\le C_P N^{1/(2\deg P)}.
\end{aligned}
\tag{3.1}
$$

这是 Jamet–Popoli–Stoll 的原预印本 Conjecture 3、出版社版本 Conjecture 3.3，在该文 §1.3 所固定的首一、整系数及非负取值范围内的陈述；指数、常数对 $P$ 的依赖与“每个充分大的 $N$”均保持原义。[上述文献，§1.3、Theorem 1.2、§3.2、Conjecture 3.3；预印本中的已知下界编号为 Theorem 2。]

**引理 4（平方抽样的长相同块）。** 对每个偶整数 $\lambda\ge14$，令

$$
s=\lambda-10,\qquad R=F_s,\qquad k=3\lambda+2.
$$

则对每个整数 $0\le n<R$，都有整数等式

$$
s_Z\bigl((L_k+n)^2\bigr)=s_Z\bigl((L_{k+2}+n)^2\bigr).
\tag{4.1}
$$

证明。以下使用的 Lucas 乘积与非干扰加法是既有工具，分别见 [Stoll, *Extremal orders of the Zeckendorf sum of digits of powers*, [arXiv:1009.5360v1](https://arxiv.org/abs/1009.5360v1), Lemmas 2.2–2.3] 及 [Jamet–Popoli–Stoll, §1.2 式 (1)、Lemma 3]。这里给出所需的统一支撑估计和移位论证，使倍数随 $\lambda$ 增长时仍有明确的适用范围。

置

$$
\varphi=\frac{1+\sqrt5}{2},\qquad
\rho=\varphi^{-1},\qquad \psi=-\rho.
$$

有 $0<\rho<1$，$\rho+\rho^2=1$，$\varphi+\rho=\sqrt5$。通常的 Binet 恒等式为

$$
F_j=\frac{\varphi^j-\psi^j}{\sqrt5},\qquad
L_j=\varphi^j+\psi^j.
\tag{4.2}
$$

两式的右侧均满足相应递推和初值，所以由递推归纳即得 (4.2)。特别地，对 $j\ge2$，

$$
L_j=F_{j-1}+F_{j+1},\qquad
\rho F_j=F_{j-1}-\psi^j,\qquad
F_{j+2}=\varphi^2F_j+\psi^j.
\tag{4.3}
$$

对自然数 $x$ 定义其规范坐标误差及移低一位的整数

$$
E(x)=\sum_{j\in Z(x)}\psi^j,
\qquad
A_x=\sum_{j\in Z(x)}F_{j-1}\in\mathbb Z.
$$

这里 $E$ 是规范支撑上的坐标和，并非把整数 $x$ 作域共轭得到的函数；不对它假设可加性。由 (4.3)，

$$
E(x)=A_x-\rho x.
\tag{4.4}
$$

将偶、奇下标分别与完整几何级数比较，有限支撑给出严格不等式

$$
-\rho^2
=-\frac{\rho^3}{1-\rho^2}
<E(x)
<\frac{\rho^2}{1-\rho^2}
=\rho.
\tag{4.5}
$$

事实上，正项至多是所有偶下标 $2,4,\ldots$ 对应的项，负项的绝对值至多是所有奇下标 $3,5,\ldots$ 对应的项；有限性使两侧均严格。区间 $(-\rho^2,\rho)$ 长度恰为一。

更一般地，若 $x=\sum_{j\ge2}c_jF_j$，其中 $c_j\in\mathbb Z$ 且只有有限多个非零项，令 $e=\sum_jc_j\psi^j$。再次使用 (4.3) 得到

$$
e+\rho x=\sum_jc_jF_{j-1}\in\mathbb Z.
$$

因此 $e-E(x)$ 是整数。若 $e$ 也属于 $(-\rho^2,\rho)$，则 $-1<e-E(x)<1$，从而

$$
e=E(x).
\tag{4.6}
$$

若 $x>0$，记 $r=\min Z(x)$。把 $E(x)$ 乘以 $(-1)^r$ 后，首项为 $\rho^r$。与首项异号的下标只能从 $r+3$ 开始，因为 $r+1$ 被规范性禁止。全部异号项的绝对值严格小于

$$
\sum_{a\ge0}\rho^{r+3+2a}
=\frac{\rho^{r+3}}{1-\rho^2}
=\rho^{r+2}.
$$

同号项均非负，故

$$
(-1)^rE(x)>\rho^r-\rho^{r+2}=\rho^{r+1}>0,
\qquad
|E(x)|>\rho^{r+1}.
\tag{4.7}
$$

(4.4)–(4.5) 的坐标方法对应仓内 [ZeckendorfBeattyBridge 的 `conjugate_error_bounds`、`sum_fib_mul_inv_golden` 及其局部辅助引理](https://github.com/the-omega-institute/trureturing/blob/8b9b65f4a2eb01e267a4704da33fd01b022ffaa7/D5/S1/Words/ZeckendorfBeattyBridge.lean)；单位区间识别误差与 (4.7) 的最小下标估计也见 [ZeckendorfCarryBarrier 的 `same_error`、`least_large` 局部论证](https://github.com/the-omega-institute/trureturing/blob/8b9b65f4a2eb01e267a4704da33fd01b022ffaa7/D5/S1/Digit/ZeckendorfCarryBarrier.lean)。同一有符号坐标亦见 [Fibonacci Canonical Window Compiler Geometry，定义 17.5、定理 17.6](https://github.com/the-omega-institute/trureturing/blob/8b9b65f4a2eb01e267a4704da33fd01b022ffaa7/docs/develop/theory/FIBONACCI_CANONICAL_WINDOW_COMPILER_GEOMETRY.md)，其 $\alpha=\rho$、$s(x)=-E(x)$。这些是这里使用的中间坐标事实。

现在设 $u,t$ 均为偶整数，$t\ge2$，$u-t\ge3$，且 $m$ 是满足 $0<m<F_t$ 的整数。表示

$$
mL_u=m(F_{u-1}+F_{u+1})
$$

的原始坐标误差为

$$
e=m(\psi^{u-1}+\psi^{u+1})
=-m\rho^u(\rho^{-1}+\rho)
=-\sqrt5\,m\rho^u.
$$

由于 $t$ 为偶数，(4.2) 给出

$$
\sqrt5\,m<\sqrt5 F_t=\varphi^t-\rho^t<\varphi^t,
\qquad
|e|<\rho^{u-t}\le\rho^3<\rho^2.
\tag{4.8}
$$

又因 $e<0$，有 $e\in(-\rho^2,\rho)$。由 (4.6)，

$$
E(mL_u)=-\sqrt5\,m\rho^u.
\tag{4.9}
$$

若 $r=\min Z(mL_u)$，则 (4.7)–(4.8) 给出

$$
\rho^{r+1}<|E(mL_u)|<\rho^{u-t}.
$$

因为 $0<\rho<1$，必有 $r+1>u-t$，即 $r\ge u-t$。另一方面，由 (4.2) 直接相乘，利用 $u,t$ 均为偶数，得到熟知的乘积恒等式

$$
\begin{aligned}
\sqrt5 F_tL_u
&=(\varphi^t-\rho^t)(\varphi^u+\rho^u)\\
&=\varphi^{u+t}-\rho^{u+t}
 -(\varphi^{u-t}-\rho^{u-t}),\\
F_tL_u&=F_{u+t}-F_{u-t}.
\end{aligned}
$$

因此

$$
mL_u<F_tL_u<F_{u+t}.
$$

规范支撑的每个权重均为正；若其中有下标至少为 $u+t$ 的项，其值就至少为 $F_{u+t}$。所以

$$
Z(mL_u)\subseteq\{u-t,u-t+1,\ldots,u+t-1\}.
\tag{4.10}
$$

将 $Z(mL_u)$ 的每个下标增加二，所得集合仍然规范，且由 (4.3) 和 (4.9)，其权重和为

$$
\begin{aligned}
\sum_{j\in Z(mL_u)}F_{j+2}
&=\varphi^2mL_u+E(mL_u)\\
&=m\bigl(\varphi^2L_u-\sqrt5\,\rho^u\bigr)\\
&=mL_{u+2}.
\end{aligned}
\tag{4.11}
$$

最后一步使用 $u$ 为偶数和 $\varphi^2-\sqrt5=\rho^2$，代入 (4.2) 即可。规范表示唯一，故

$$
Z(mL_{u+2})=\{j+2:j\in Z(mL_u)\},\qquad
s_Z(mL_{u+2})=s_Z(mL_u).
\tag{4.12}
$$

$m=0$ 时两边支撑均为空，(4.10)–(4.12) 也成立。规范下标平移所保持的正是定义 1 的同一对象，亦对应 [GoldenDesubstitutionZeckendorf 的 `shifted_wdigits_isCanonical` 与 `golden_subst_start_wdigits`](https://github.com/the-omega-institute/trureturing/blob/8b9b65f4a2eb01e267a4704da33fd01b022ffaa7/D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf.lean)。这里通过 (4.11) 另外识别了实际平移后的整数为 $mL_{u+2}$。

回到本引理，令 $t=s+2=\lambda-8$。对 $0\le n<F_s$，置

$$
m=2n,\qquad q=n^2+2.
$$

因为 $s\ge4$，有 $F_s\ge2$，并且

$$
m<2F_s<F_{s+2}=F_t.
\tag{4.13}
$$

其中 $F_{s+2}=2F_s+F_{s-1}>2F_s$。同样，

$$
q\le(F_s-1)^2+2\le F_s^2<F_sL_s=F_{2s}.
\tag{4.14}
$$

中间的弱不等式等价于 $3\le2F_s$；严格不等式使用 $L_s=F_s+2F_{s-1}>F_s$。最后的等式直接由 (4.2) 得到：$F_sL_s=(\varphi^{2s}-\psi^{2s})/\sqrt5=F_{2s}$。因此

$$
Z(q)\subseteq\{2,\ldots,2s-1\}.
\tag{4.15}
$$

$k,t$ 都为偶数，且 $k-t=2\lambda+10\ge3$，所以 (4.10)–(4.12) 适用于 $u=k$。又由 (4.3)，

$$
Z(L_{2k})=\{2k-1,2k+1\},\qquad
Z(L_{2k+4})=\{2k+3,2k+5\}.
\tag{4.16}
$$

这两种表示本身规范。三个支撑组的范围为

$$
\begin{array}{c|c|c|c}
&Z(q)&\text{中间组}&\text{最高组}\\ \hline
u=k&[2,2s-1]&[k-t,k+t-1]&\{2k-1,2k+1\}\\
u=k+2&[2,2s-1]&[k+2-t,k+2+t-1]&\{2k+3,2k+5\}.
\end{array}
\tag{4.17}
$$

这里区间均表示整数下标范围，空的中间支撑允许出现。对于第一行，相邻两组最近可能下标的差分别至少为

$$
(k-t)-(2s-1)=31,
\qquad
(2k-1)-(k+t-1)=k-t=2\lambda+10.
$$

第二行对应的差分别为 $33$ 和 $2\lambda+12$。它们均至少为二，所以每行的三个规范支撑的并仍然规范，且不需任何进位。由规范唯一性，并集的基数就是总和的位数和。这正是所引非干扰加法在此处的直接含义。

最后，由 (4.2)，对偶数 $u$ 有 $L_u^2=L_{2u}+2$。取 $u=k$ 或 $k+2$，得到

$$
(n+L_u)^2=(n^2+2)+2nL_u+L_{2u}=q+mL_u+L_{2u}.
$$

应用 (4.17) 的分离以及 (4.12)，

$$
\begin{aligned}
s_Z((n+L_k)^2)
&=s_Z(q)+s_Z(mL_k)+2\\
&=s_Z(q)+s_Z(mL_{k+2})+2\\
&=s_Z((n+L_{k+2})^2).
\end{aligned}
$$

这证明 (4.1)，包括 $n=0$。$\square$

**引理 5（同一对平移的显式异奇偶位置）。** 对每个偶整数 $\lambda\ge14$，有

$$
s_Z\bigl((L_\lambda+L_{3\lambda+2})^2\bigr)=9,
\qquad
s_Z\bigl((L_\lambda+L_{3\lambda+4})^2\bigr)=10.
\tag{5.1}
$$

证明。所需的既有 Lucas 恒等式为

$$
L_aL_b=L_{a+b}+(-1)^bL_{a-b}\quad(a\ge b\ge0),
\qquad
L_a^2=L_{2a}+2(-1)^a,
\tag{5.2}
$$

其中 $a=b$ 时用 $L_0=2$。两式均由 (4.2) 相乘得到；在第一式中，两个交叉项为 $(-1)^b(\varphi^{a-b}+\psi^{a-b})$。参见 [Stoll, arXiv:1009.5360v1, Lemma 2.2；Jamet–Popoli–Stoll, Lemma 3]。另有

$$
2L_j=F_{j+3}+F_{j-3}\quad(j\ge3),
\qquad
2F_j=F_{j+1}+F_{j-2}\quad(j\ge2).
\tag{5.3}
$$

第一式也用于 [Stoll, §4, 式 (17) 前的恒等式]。为直接核对它，由 Fibonacci 递推，$F_{j+3}=2F_{j+1}+F_j$，$F_{j-3}=2F_{j-1}-F_j$，相加即得 $2(F_{j-1}+F_{j+1})=2L_j$。第二式是 $F_{j+1}=F_j+F_{j-1}$ 与 $F_{j-1}=F_j-F_{j-2}$ 的合并。

置 $B=2\lambda$。对发生干扰的最低 Lucas 组，(5.3) 给出如下完整化简：

$$
\begin{aligned}
L_B+2L_{B+2}
&=F_{B-1}+F_{B+1}+F_{B+5}+F_{B-1}\\
&=F_{B+5}+F_{B+1}+F_B+F_{B-3}\\
&=F_{B+5}+F_{B+2}+F_{B-3},\\[2mm]
L_B+2L_{B+4}
&=F_{B-1}+F_{B+1}+F_{B+7}+F_{B+1}\\
&=F_{B+7}+F_{B-1}+F_{B+2}+F_{B-1}\\
&=F_{B+7}+F_{B+2}+F_B+F_{B-3}.
\end{aligned}
\tag{5.4}
$$

第一种支撑按升序为 $B-3,B+2,B+5$，间隔为五、三；第二种为 $B-3,B,B+2,B+7$，间隔为三、二、五。因为 $\lambda\ge14$，所有下标至少为二。两者都是规范表示，分别有三项和四项。

对 $c\in\{2,4\}$，所有 $\lambda$、$3\lambda+c$ 都是偶数。用 (5.2) 展开两个平方和一个乘积，得到整数等式

$$
\begin{aligned}
(L_\lambda+L_{3\lambda+c})^2
&=(L_{2\lambda}+2)+(L_{6\lambda+2c}+2)
  +2(L_{4\lambda+c}+L_{2\lambda+c})\\
&=4+(L_{2\lambda}+2L_{2\lambda+c})
  +2L_{4\lambda+c}+L_{6\lambda+2c}.
\end{aligned}
\tag{5.5}
$$

按照 (5.4) 及 (5.3)，右侧四组的规范支撑依次为

$$
\begin{aligned}
Z(4)&=\{2,4\},\\
Z(L_{2\lambda}+2L_{2\lambda+2})
 &=\{2\lambda-3,2\lambda+2,2\lambda+5\},\\
Z(L_{2\lambda}+2L_{2\lambda+4})
 &=\{2\lambda-3,2\lambda,2\lambda+2,2\lambda+7\},\\
Z(2L_{4\lambda+c})&=\{4\lambda+c-3,4\lambda+c+3\},\\
Z(L_{6\lambda+2c})&=\{6\lambda+2c-1,6\lambda+2c+1\}.
\end{aligned}
\tag{5.6}
$$

其中 $4=F_2+F_4$。对于固定的 $c$，第二组取相应的一行。每个组内部已经规范；相邻组之间的最近下标差分别为

$$
2\lambda-7,\qquad
2\lambda-6,\qquad
2\lambda+c-4.
\tag{5.7}
$$

三者均至少为二。故 (5.5) 确是四组规范支撑的无交叠并，没有遗漏的进位或约简。由定义 1 的唯一性，$c=2$ 时总位数和为 $2+3+2+2=9$，$c=4$ 时为 $2+4+2+2=10$，即 (5.1)。$\square$

**定理 6（原始反馈寄存器的平方下界）。** 令 $S(n)=s_Z(n^2)\bmod2$，复杂度严格采用定义 2。对每个偶整数 $\lambda\ge14$，置

$$
N_\lambda=L_{3\lambda+4}+L_\lambda+1.
$$

则

$$
M(S,N_\lambda)\ge F_{\lambda-10}+1.
\tag{6.1}
$$

证明。记

$$
i=L_{3\lambda+2},\qquad
j=L_{3\lambda+4},\qquad R=F_{\lambda-10}.
$$

$i<j$，而引理 4 给出

$$
S(i+n)=S(j+n),\qquad 0\le n<R.
\tag{6.2}
$$

引理 5 则给出

$$
S(i+L_\lambda)=1,\qquad S(j+L_\lambda)=0.
\tag{6.3}
$$

因此有限非空集合

$$
\{n\in\mathbb N_0: n\le L_\lambda,\ S(i+n)\ne S(j+n)\}
$$

有最小元 $h$。由 (6.2)–(6.3)，

$$
R\le h\le L_\lambda,\qquad
S(i+n)=S(j+n)\ (0\le n<h),\qquad
S(i+h)\ne S(j+h).
\tag{6.4}
$$

全部涉及的样本下标都在前缀 $0,\ldots,N_\lambda-1$ 内，因为

$$
i+h<j+h\le j+L_\lambda=N_\lambda-1.
\tag{6.5}
$$

下面直接使用反馈定义。这是 Jansen 的“相同块、不同后继”方法在当前索引上的应用；该方法见 [Jamet–Popoli–Stoll, Lemma 1，所引 Jansen Proposition 3.1]。

设有正整数 $m\le h$ 及一个多项式 $f\in\mathbb F_2[X_1,\ldots,X_m]$ 满足 (2.1)，取 $N=N_\lambda$。两个起点

$$
a=i+h-m,\qquad b=j+h-m
$$

都非负；由 (6.5)，

$$
a\le N_\lambda-m-1,\qquad b\le N_\lambda-m-1.
\tag{6.6}
$$

故这两个起点都是 (2.1) 所要求的合法起点。对每个 $0\le r<m$，有 $0\le h-m+r<h$，所以 (6.4) 蕴含

$$
T_r:=S(a+r)=S(i+h-m+r)=S(j+h-m+r)=S(b+r).
$$

把同一个多项式用于这两个相同的长度 $m$ 输入块，得到

$$
S(i+h)=f(T_0,\ldots,T_{m-1})=S(j+h),
$$

与 (6.4) 矛盾。因此任何满足反馈条件的正阶数都严格大于 $h$。

最后必须核对常值前缀分支。由定义 1，$S(0)=0$，$S(1)=1$；又 $N_\lambda\ge3$，故 $(S(0),\ldots,S(N_\lambda-2))$ 非常值，(2.2) 的两个分支均不适用。定义 2 的最小正阶数因而满足

$$
M(S,N_\lambda)>h\ge R.
$$

各量为整数，遂得 (6.1)。这里的输入是平方抽样序列自身的连续历史位，结论直接针对 (2.1) 的反馈多项式。$\square$

**推论 7（完整原多项式猜想的否定）。** 多项式 $P(X)=X^2$ 属于定义 3 的 $\mathcal A$，但满足

$$
\forall C>0\ \forall H\in\mathbb N\ \exists N\in\mathbb N,
\qquad N\ge\max\{2,H\},\qquad M(S_{Z,P},N)>CN^{1/4}.
\tag{7.1}
$$

因此定义 3 的命题 $\mathcal C$ 为假，即 Jamet–Popoli–Stoll 的 Conjecture 3 / published Conjecture 3.3 在原始定义及其完整多项式范围内不成立。

证明。$X^2$ 的系数为整数、首项系数为一、次数为二，且对每个 $n\in\mathbb N_0$，$n^2\in\mathbb N_0$，故它满足全部多项式条件。又 $S_{Z,X^2}=S$，无需任何平移或重新编号。

为把定理 6 转为 (7.1)，先给出不依赖渐近省略项的估计。由 $\varphi^2=\varphi+1$，从 $F_2=1$ 和 $F_3=2>\varphi$ 归纳得到

$$
F_r\ge\varphi^{r-2}\qquad(r\ge2).
\tag{7.2}
$$

确切地说，若相邻两项满足此界，则

$$
F_{r+2}=F_{r+1}+F_r
\ge\varphi^{r-1}+\varphi^{r-2}
=\varphi^r.
$$

对正偶数 $r$，由 (4.2)，

$$
\varphi^r<L_r=\varphi^r+\rho^r\le2\varphi^r.
\tag{7.3}
$$

所以对所有偶整数 $\lambda\ge14$，

$$
\varphi^{3\lambda+4}<N_\lambda
\le2\varphi^{3\lambda+4}+2\varphi^\lambda+1
\le5\varphi^{3\lambda+4}.
\tag{7.4}
$$

将 (7.2)、(7.4) 与定理 6 合并，得到

$$
\frac{M(S,N_\lambda)}{N_\lambda^{1/4}}
\ge\frac{F_{\lambda-10}+1}{N_\lambda^{1/4}}
>\frac{\varphi^{\lambda-12}}
 {5^{1/4}\varphi^{(3\lambda+4)/4}}
=5^{-1/4}\varphi^{\lambda/4-13}.
\tag{7.5}
$$

因为 $\varphi>1$，(7.4) 的左侧及 (7.5) 的右侧，在偶整数 $\lambda$ 趋向无穷时都趋向无穷。给定任意 $C>0$ 和任意阈值 $H\in\mathbb N$，可取同一个充分大的偶整数 $\lambda\ge14$，同时使 $N_\lambda\ge\max\{2,H\}$ 且 (7.5) 的右侧大于 $C$。令 $N=N_\lambda$ 即得 (7.1)。

若 $\mathcal C$ 成立，将 (3.1) 用于 $P=X^2$ 就会给出某个 $C_P>0$ 及阈值 $N_P$，使所有 $N\ge N_P$ 满足 $M(S,N)\le C_PN^{1/4}$。在 (7.1) 中取 $C=C_P$、$H=N_P$，即得矛盾。这否定的是每个充分大 $N$ 上的统一上界，不要求每个大 $N$ 都是反例。原文 Theorem 1.2 已证明的 $N^{1/(2d)}$ 下界与此相容；本反例不推出平方序列的匹配上界，也不判定其他多项式的精确增长阶。$\square$

## 追加锚（本行以下为增补区）
