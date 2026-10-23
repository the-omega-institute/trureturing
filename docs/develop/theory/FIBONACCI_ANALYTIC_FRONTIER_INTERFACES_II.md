# Fibonacci 解析前沿接口续卷

> 本卷是参考输入，不承担数学真值；正文未经 Lean kernel 验证。采用 `generic-v1` 消化语法，既有字节保留，修订与增补写在末尾追加锚之后。章节编号承接 [前卷](FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md)。

## 480. 完整 Robin 加权尾量的直接高斯定位

本节直接消费前卷 §479 的同尺度高斯零点选择，以及 §477 的实际 lcm 比较。完整积分显式公式、零点倒数和、[Révész 所用 Cassel 幂和步骤](../../../Library/Zeros/revesz1988oscillation.md)、[完整 Mertens 恒等式](../../../Library/Analytic/lay2015mertenssignchanges.md)和[无条件积分收敛输入](../../../Library/Weil/johnstonyang2022pnt.md)均为已有工具。新增承重部分是原始加权尾量的伴随核及其完整非振荡均值估计，文献状态为 `repo-derived`，不主张文献优先权。

**命题 480.1（原加权尾量与有界实际整数）。** 设实际非平凡零点 $\rho_0=\beta+i\gamma$ 满足 $\beta>1/2$、$\gamma>0$，令

$$
\delta=\beta-\tfrac12,\qquad D=\gamma+10,\qquad
m_0=100D^2\delta^{-2},\qquad m_1=500D^4\delta^{-2},\qquad X=e^{28m_1}.
\tag{480.1}
$$

对完整 Chebyshev 尾量

$$
I_\psi(t)=\int_t^\infty(\psi(s)-s)
\frac{1+\log s}{s^2\log^2s}\,ds
$$

存在实数 $A\in[e^{4m_0},X]$ 满足 $I_\psi(A)<-4/\sqrt A$。因此实际整数 $N=\operatorname{lcm}(1,\ldots,\lfloor A\rfloor)$ 满足

$$
5040<N\le\exp(X\log X),\qquad
\frac{\sigma(N)}N>e^{\gamma_E}\log\log N.
\tag{480.2}
$$

证明。以下零点多重集完整保留重数。直接复用 §479 的记号与估计，写

$$
a_\rho=\frac1{\rho(1-\rho)},\quad H(y)=\sum_\rho a_\rho e^{\rho y},\quad
U(y)=\mathcal U(e^y),\quad c=\log(2\pi),\quad
V(y)=\sum_{j\ge1}\frac{e^{-2jy}}{2j(2j+1)}.
$$

已知 $H=U-c+V$（$y>0$），$|H(y)|\le2e^{\max(y,0)}$，且对 $\rho=b+i\eta$ 有

$$
0<b<1,\quad |\eta|>10,\quad
\sum_\rho\eta^{-2}<2,\quad \sum_\rho|a_\rho|<2,\quad
N_{\rm both}(T)\le2T^2.
\tag{480.3}
$$

已有的整数幂和选择供应同一个 $m\in[m_0,m_1]$，使

$$
E_\gamma(m)=\sum_\rho e^{m(\rho-i\gamma)^2+16m(\rho-i\gamma)},\qquad
\Re E_\gamma(m)\ge\tfrac12e^{am},\qquad a=\beta^2+16\beta.
\tag{480.4}
$$

这里不重新选择零点或丢弃远端零点。以下所有核与均值均使用这个 $m$。

令 $r(y)=(y+1)/y^2$、$q(y)=1/r(y)=y^2/(y+1)$，并令 $R(y)=-e^yI_\psi(e^y)$（$y\ge1$）。前卷的 $Q$ 满足 $U(y)=-e^yQ(e^y)$。由 $I_\psi'=r(\log t)Q'$ 得到

$$
U'-U=q(R'-R),\qquad
H''-H'=\bigl[q(R'-R)\bigr]'+V''-V',\qquad
V''-V'=\frac1{e^{2y}-1}.
\tag{480.5}
$$

第一式几乎处处成立，第二式按分布理解，保留每个素数幂跳变。

**完整加权谱与绝对主控。** 经典 Laplace 身份 $r(y)=\int_0^\infty(1+h)e^{-hy}\,dh$ 在这里仅作中间工具。对完整 $U$ 分部积分，有

$$
R(y)=r(y)U(y)+e^y\int_y^\infty r'(z)e^{-z}U(z)\,dz.
$$

无穷端由上述无条件收敛输入支付。将绝对收敛的 $H$ 代入，并使用 $r'\le0$：每个零点在第二项中的绝对贡献之和至多 $e^y r(y)\sum|a_\rho|$。因此这里可以交换零点和与积分，而无需逐项使用未平滑的条件收敛显式公式。应用 Laplace 身份后，每项的代数因子是

$$
a_\rho\left(1-\frac{h}{1+h-\rho}\right)
=\frac1{\rho(1+h-\rho)}.
$$

从而有精确表示

$$
\begin{aligned}
R(y)&=\int_0^\infty(1+h)L_h(y)\,dh+S(y),\\
L_h(y)&=\sum_\rho\frac{e^{(\rho-h)y}}{\rho(1+h-\rho)},\\
S(y)&=\int_y^\infty e^{y-z}
\left[c+\tfrac12\log(1-e^{-2z})\right]r(z)\,dz.
\end{aligned}
\tag{480.6}
$$

两分母的模均至少为 $|\eta|$，所以 (480.3) 也直接给出该表示的绝对可和性。对 $y\ge1$，有 $|S(y)|\le3r(y)\le6$，以及

$$
|R(y)|\le2e^yr(y)+3r(y)\le10e^y.
\tag{480.7}
$$

**伴随核与有限下端。** 令 $M=16m$，并写

$$
g(y)=\frac{e^{-(y-M)^2/(4m)}}{\sqrt{4\pi m}},\qquad
u=\frac{y-M}{2m},\qquad \phi(y)=e^{-i\gamma y}g(y).
$$

定义

$$
\begin{aligned}
k_R&=-q\phi''-(q'+q)\phi',\qquad K_R=\Re k_R,\\
v_R(y)&=3(y+1)(u^2+\gamma^2+1)g(y)\quad(y\ge1).
\end{aligned}
$$

由 $0<q\le y$、$0<q'\le1$、$\phi'=-(u+i\gamma)\phi$ 及 $m\ge1$，有 $|K_R|\le v_R$。零点高斯积分给出 $E_\gamma(m)=-\int_{\mathbb R}H(\phi''+\phi')$；将 (480.5) 用于 $[1,\infty)$，两次分部积分得到

$$
E_\gamma(m)=\int_1^\infty R(y)k_R(y)\,dy+\mathcal E_m,
\tag{480.8}
$$

其中完整误差为

$$
\begin{aligned}
\mathcal E_m={}&-\int_{-\infty}^1H(\phi''+\phi')
-\int_1^\infty(V''-V')\phi\\
&+[H(1)-q(1)R(1)]\phi'(1)
 +[-c+V(1)-V'(1)]\phi(1).
\end{aligned}
\tag{480.9}
$$

所有无穷端因高斯衰减消失；$y=1$ 不是素数幂事件。由 $|H(1)|<6$、$|R(1)|<30$、$q(1)=1/2$、$|\phi'(1)|\le D$ 及 $|-c+V(1)-V'(1)|\le4$，并用

$$
|\phi''+\phi'|\le2(u^2+\gamma^2+1)g,\qquad
\int_{\mathbb R}2(u^2+\gamma^2+1)g\le2D^2,
$$

得到 $|\mathcal E_m|\le12D^2+21D+5<20D^2$。不能将 (480.9) 当作零边界。

**支付非振荡均值。** 对 (480.6) 的 $h\ge2$ 部分，绝对值至多

$$
2e^{-y}\left(\frac3y+\frac1{y^2}\right)\le8\qquad(y\ge1).
$$

对 $0\le h\le2$，将 $L_h$ 延到实轴再支付补出的 $y<1$ 部分。写 $z=\rho-h$，完整高斯矩为

$$
\int_{\mathbb R}(y+1)(u^2+\gamma^2+1)g(y)e^{zy}\,dy
=\left[(M+2mz+1)\left(z^2+\gamma^2+1+\frac1{2m}\right)+2z\right]e^{mz^2+Mz}.
\tag{480.10}
$$

这里 $-2<\Re z<1$，故指数实部至多 $17m-m\eta^2$。乘上系数 $1/[\rho(1+h-\rho)]$ 后，方括号的模至多 $20mD^2(|\eta|+1)$。按 $|\eta|\in[10+j,11+j)$ 分箱，由 (480.3) 得

$$
\sum_\rho(|\eta|+1)e^{-m\eta^2}
\le2\sum_{j\ge0}(11+j)^2(12+j)e^{-m(10+j)^2}
\le10000e^{-100m}.
$$

因此完整实轴的 $0\le h\le2$ 均值，包含 $v_R$ 的因子 $3$ 与 $\int_0^2(1+h)dh=4$，其模至多 $2.4\cdot10^6mD^2e^{-83m}$。逐零点交换的绝对主控来自 (480.3)、有界 $h$ 与高斯衰减；式 (480.10) 在此给出抵消后的均值，而非用零点谱的绝对积分冒充该均值。

以下列出补出的半轴及其余部分的全部成本。在整条实轴临时使用 $\widetilde v=3(y+1)(u^2+\gamma^2+1)g$，它在 $y< -1$ 可为负；估计使用 $|\widetilde v|$。高斯二、四阶矩给出 $\int|\widetilde v|\le100mD^2$。当 $0\le y\le1$ 时 $|L_h(y)|\le6$，其成本至多 $2400mD^2$。当 $y<0$ 时 $|L_h(y)|\le2e^{-2y}$；以 $e^{-2y}g$ 倾斜，均值成为 $12m$，总因子为 $e^{-28m}$，得到成本至多 $384mD^2e^{-28m}$。例如令倾斜后的中心变量为 $Z$，则

$$
|y+1|\le14m+Z^2/2,\qquad
u^2+\gamma^2+1\le D^2+Z^2/(2m^2),
$$

方差 $2m$ 下的矩为 $\mathbb EZ^2=2m$、$\mathbb EZ^4=12m^2$，故相应绝对多项式矩至多 $48mD^2$，其中已经包含 $v_R$ 的系数 $3$。其余 $h\ge2$ 与 $S$ 分别至多贡献 $800mD^2$、$600mD^2$。合计得到

$$
\left|\int_1^\infty R(y)v_R(y)\,dy\right|\le3\cdot10^6mD^2.
\tag{480.11}
$$

**有符号估计与实际整数。** 反设在 $J=[4m,28m]$ 上 $R(y)\le4e^{y/2}$。因 $K_R+v_R\ge0$，(480.8) 给出

$$
\Re E_\gamma(m)\le8\int_J e^{y/2}v_R
+\left|\int_1^\infty Rv_R\right|
+2\int_{[1,\infty)\setminus J}|R|v_R+|\mathcal E_m|.
\tag{480.12}
$$

第一项以 $e^{y/2}g$ 倾斜为均值 $17m$、方差 $2m$ 的高斯，支付因子 $e^{33m/4}$。令中心变量为 $Z$，使用 $|y+1|\le19m+Z^2/2$ 与 $u^2+\gamma^2+1\le D^2+Z^2/(2m^2)$，其多项式绝对矩（已含系数 $3$）至多 $60mD^2+66\le100mD^2$，所以

$$
\int_J e^{y/2}v_R\le100mD^2e^{33m/4}.
$$

区间外用 (480.7)，再以 $e^yg$ 倾斜为均值 $18m$ 的高斯。此时 $|Z|\ge10m$；将高斯指数平分，支付 $e^{-25m/2}$，剩下方差 $4m$。用 $y+1\le20m+Z^2/2$、$u^2+\gamma^2+1\le D^2+Z^2/(2m^2)$，其多项式矩（已含系数 $3$）至多 $66mD^2+156$。连同倾斜因子 $e^{17m}$、(480.7) 的 $10$ 与密度比 $\sqrt2$，得

$$
\int_{[1,\infty)\setminus J}|R|v_R\le1000mD^2e^{9m/2}.
$$

将这些估计及 (480.11) 代回 (480.12)，得到

$$
\Re E_\gamma(m)\le4\cdot10^6mD^2e^{33m/4}.
$$

但 $a-33/4=17\delta+\delta^2$，且由 $D>20$、$0<\delta<1/2$、$m_0\le m\le m_1$，

$$
\log(8\cdot10^6mD^2)
\le\log(4\cdot10^9D^6\delta^{-2})
<23+6D+2/\delta\le D^2/\delta<17\delta m.
$$

这与 (480.4) 矛盾。因此某个 $y\in J$ 满足 $R(y)>4e^{y/2}$，即 $A=e^y$ 满足所述严格负尾界。前卷 (477.4) 直接给出

$$
\log\frac{e^{\gamma_E}\log\log D_A}{\sigma(D_A)/D_A}
\le I_\psi(A)+\frac4{\sqrt A}<0.
$$

又 $A>10000$、$D_A\ge\lfloor A\rfloor$ 及 $\log D_A=\psi(A)\le A\log A\le X\log X$，故得到 (480.2)。证毕。

本命题消费原始 $I_\psi$，保留全部未来积分、素数幂、平凡零点修正和下端边界。前卷 §479 经 §478 使用的截止是 $\exp(4(28m_1+20)^2)$；这里直接使用 $X=e^{28m_1}$，免去该对数截止的二次扩大。两份实际整数上界均为双指数，不将此改进称为减少一层指数。这里没有构造实际离线零点、无条件负尾峰或 Robin 反例，也没有证明 RH 或对每个 $n>5040$ 的严格 Robin。

## 追加锚（本行以下为增补区）

## 481. 原前向价格核的临界零点响应与统一下界障碍

这里继续使用 [QG3、QG7、QG9 与 CW3–CW5](../../../Library/ArithSums/nicolas2025comparison.md) 的实际前向积分，不更换为素数单层、固定相对区间或另一种平滑。它们的整数后继、完整库存和终端凹性成本均直接复用。本节证明这一原核的 Mellin 接口，并区分全实中心下界与实际被选来源上的下界。

令

$$
\begin{gathered}
E(x)=\psi(x)-x,\qquad H_x=x^{4/5},\qquad B_x=x+H_x,\\
\lambda(x)=\frac1{x\log x},\qquad
w(x)=-\lambda'(x)=\frac{1+\log x}{x^2\log^2x},\qquad
\rho_x(u)=\frac{w(x+u)}{w(x)}.
\end{gathered}
$$

定义同一归一化前向响应

$$
\begin{aligned}
\mathcal T(x)
&=\frac{\sqrt x}{H_x^2}
\int_0^{H_x}[E(x+u)-E(x)]\rho_x(u)\,du\\
&=\frac{T_\psi(x,x^{4/5})}{x^{11/10}}.
\end{aligned}
\tag{481.1}
$$

原 QG7 的有限恒等式给出

$$
\mathcal T(x)=\frac{\sqrt x}{w(x)H_x^2}
\int_{(x,B_x]}[\lambda(t)-\lambda(B_x)]\,dE(t),
\qquad dE=\sum_{n\ge1}\Lambda(n)\delta_n-dt.
\tag{481.2}
$$

初端原子排除，终端原子的权重为零；每个参考素数幂仍带完整的 $\log p$ 权重。

**命题 481.1（原核的 Mellin 留数）。** 假设 RH，并使用其经典 von Koch 界 $E(t)=O(\sqrt t\log^2t)$。对任意固定 $x_0\ge3$，最初在 $\Re s>1/2$ 定义

$$
\mathcal F(s)=\int_{x_0}^\infty\mathcal T(x)x^{-s-1}\,dx.
$$

则存在在 $\Re s>-1/5$ 全纯的 $R_{x_0}(s)$，使

$$
\mathcal F(s)
=-\frac12\frac{\zeta'}{\zeta}(s+1/2)
-\frac1{2(s-1/2)}+R_{x_0}(s).
\tag{481.3}
$$

右边在 $s=1/2$ 的奇点可去。它在 $\Re s>0$ 全纯，并在 $s=0$ 全纯。每个重数为 $m$ 的非平凡零点 $1/2+i\gamma$ 在 $s=i\gamma$ 给出留数 $-m/2$。

证明。最初在 $\Re s>1/2$ 对 (481.2) 作绝对 Fubini 交换，所得伴随核为

$$
q_s(t)=\int_{\substack{x\ge x_0\\x<t\le x+x^{4/5}}}
\frac{x^{-s-1/2}[\lambda(t)-\lambda(x+x^{4/5})]}
 {w(x)x^{8/5}}\,dx.
\tag{481.4}
$$

写 $a=4/5$。在 $t\ge x_0+x_0^a$ 时，以 $t=x+zx^a$ 定义 $x=x(t,z)$，其中 $0\le z\le1$。这个正解唯一，且

$$
D=1+azx^{a-1},\qquad x_t=D^{-1},\qquad x_z=-x^aD^{-1}.
$$

于是 (481.4) 恰为

$$
q_s(t)=\int_0^1 x(t,z)^{-s-1/2}
\frac{\displaystyle\int_z^1w(x+ux^a)/w(x)\,du}
 {1+azx^{a-1}}\,dz.
\tag{481.5}
$$

令 $\epsilon_t=t^{-1/5}$。对 $s$ 的每个固定紧集 $K\subset\mathbb C$，一致地有

$$
\begin{gathered}
q_s(t)=\tfrac12t^{-s-1/2}+r_s(t),\\
|r_s(t)|\le C_Kt^{-\Re s-1/2}\epsilon_t,\qquad
|\partial_t r_s(t)|\le C_Kt^{-\Re s-3/2}\epsilon_t.
\end{gathered}
\tag{481.6}
$$

确切系数来自 $\int_0^1(1-z)\,dz=1/2$。为核对余项与其导数，使用 $x/t=1+O(\epsilon_t)$、$D=1+O(\epsilon_t)$ 以及

$$
(\log w)'(x)=-\frac2x+rac1{x(1+\log x)}-rac2{x\log x},
\qquad (\log w)''(x)=O(x^{-2}).
$$

由此 $w(x+ux^a)/w(x)=1+O(\epsilon_t)$；沿 $t$ 对这个相关比值求导为 $O(\epsilon_t/t)$，同时 $\partial_t(x/t)=O(\epsilon_t/t)$、$\partial_t(x^{a-1})=O(\epsilon_t/t)$。代入 (481.5)，先抽出 $t^{-s-1/2}$ 再求导，给出 (481.6)；不是对未减主项的导数误报较小阶。

RH 下，对 $\int r_s\,dE$ 作分部积分，其无穷端边界为

$$
O_K(t^{-\Re s-1/5}\log^2t),
$$

导数积分在 $\Re s>-1/5$ 的每个紧集上一致绝对收敛。因此余项全纯。核在有限区间 $[x_0,x_0+x_0^a]$ 的修正，以及移除 $[1,x_0]$，只产生整函数项。主项最初满足

$$
\frac12\int_1^\infty t^{-s-1/2}\,dE(t)
=-\frac12\frac{\zeta'}{\zeta}(s+1/2)-\frac1{2(s-1/2)},
$$

得 (481.3)。$\zeta$ 在 $1$ 的极点使两个显式项的奇点相消；实区间 $(0,1)$ 无零点，故 $s=0$ 正则。其余临界零点的对数导数留数为 $m$，给出所示 $-m/2$。这里没有先假设原积分在整个 $\Re s>0$ 收敛；直接的 RH 点值界只先保证其在 $\Re s>1/5$ 绝对收敛。证毕。

**命题 481.2（RH 下统一单侧预算的必要系数）。** 在命题 481.1 的前提下，若有限常数 $\kappa$ 满足 $\mathcal T(x)\ge-\kappa$ 对所有充分大的实数 $x$ 成立，则对每个非平凡零点的重数 $m$ 都有

$$
\kappa\ge\frac m2.
\qquad\text{特别地，}\quad
\liminf_{x\to\infty}\mathcal T(x)\le-\frac12.
\tag{481.7}
$$

证明。增大 $x_0$，使 $g(y)=\mathcal T(e^y)+\kappa\ge0$ 对 $y\ge\log x_0$ 成立。RH 点值界给 $g(y)=O(e^{y/5}(1+y^2))+O(1)$，故其收敛横坐标至多为 $1/5$。其变换最初为

$$
G(s)=\mathcal F(s)+\frac{\kappa x_0^{-s}}s.
$$

由 (481.3)，它能跨过每个正实点全纯延拓。直接使用 [FIB 原卷定理 92.3](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 已明列的 Landau 非负 Laplace 变换定理，收敛横坐标不能为正。因此对每个 $\sigma>0$，实际的非负积分均收敛。该积分与延拓表达式在右半平面由恒等定理一致，故

$$
|G(\sigma+i\gamma)|\le G(\sigma).
$$

由 $\mathcal F$ 在零点的留数和在 $0$ 的正则性，

$$
\lim_{\sigma\downarrow0}\sigma G(\sigma)=\kappa,
\qquad
\lim_{\sigma\downarrow0}\sigma G(\sigma+i\gamma)=-\frac m2.
$$

取极限给 $m/2\le\kappa$。非平凡零点存在，且不在实轴，故 $m\ge1$ 给出 (481.7)。不需要零点简单性、零点纵坐标的线性无关性或数值零点输入。证毕。

**推论 481.3（全实中心版 QGP 不成立）。** 复用 [S5 的 RH 失败时的无界实际正则 GA1/GA2 来源](../../../Library/Arith/caveney2012sacaga.md) 及上述完整 $Q$ 供应。令 $c_Q=(\sqrt2-1)/4$。对每个固定 $\kappa<c_Q$ 和每个有限 $T$，存在实数 $x\ge T$ 使

$$
T_\psi(x,x^{4/5})<-\kappa x^{11/10}.
\tag{481.8}
$$

证明。若 RH 成立，(481.7) 与 $c_Q<1/2$ 直接给出。若 RH 失败，S5 给出无界的同一实际正则来源 $N=N_A^{\rm str}$、$A=\log N$。原 QG9 和该整数的 GA2 比较保留实际终端成本，给出

$$
w(A)[T_\psi(A,A^{4/5})+S_Q(A,A^{4/5})]
\le-C_{B_A}(K(B_A))\le0.
$$

完整供应 $S_Q(A,A^{4/5})/A^{11/10}\to c_Q$ 因来源无界而越过每个共同的未知有限起点，遂得 $\mathcal T(A)\le-c_Q+o(1)<-\kappa$。这里直接消费既有来源与恒等式，不重建其选择或删除／插入桥。证毕。

**范围与文献归属。** von Koch 的 RH 误差界、$-\zeta'/\zeta$ 的 Dirichlet 级数、非平凡零点及 Landau 非负变换原理是经典输入。原前向消费者、完整 $Q$ 漂移和 S5 来源各按上述既有条目归属。本节的 `repo-derived` 内容是 (481.4)–(481.6) 对同一移动价格核的运输，以及它对全实中心下界的限制；不主张一般振荡理论的原创性或最优系数。它是纸面解析推导，未作 Lean 核验。

(481.8) 否定的是一个比原 QGP 更强的统一供应，并不是 Robin 反例。RH 分支中的坏中心不自动属于被选整数族；它也不提供任何好中心落在该族的结论。原任务仍须在同一实际来源、完整约数响应、所有素数幂和实际终端成本下取得独立的有符号估计。RH 与每个 $n>5040$ 的严格 Robin 不等式仍未证明。

## 追加锚（本行以下为增补区）

## 482. 固定高估值部分的平均 Type-I 与全部小标记留数

**约定与解析假设。** 沿用前卷 §460、[H1–H5、G7](../../../Library/Analytic/faveri2026fixedorder.md#a-prime-labelled-residue-cut-for-the-original-unsplit-convolution) 的 Eisenstein 理想、固定坏素集合 $S$、原始 primary 与 ray 约定。写 $q_a=Na$，$a^{\ge2}=\prod_{v_p(a)\ge2}p^{v_p(a)}$；单位的该乘积为单位。元素频率按原固定 unit 与 ray sectors 读取，不将元素重数另算为理想重数。

本节的解析输入是 [averaged Type-I 原稿 v1](https://rstation.ai/api/v1/papers/riemann_hypothesis_8/versions/1/download) §5 的固定形式变换、Lemma 3 的固定 cusp 系数平方和、(5.9) 的核界、(6.3) 的完整四项筛，以及 H4 的原始 primitive/full 密度关系。它们在此作为条件，不由本节另行认证。固定形式、固定有限过滤和 level $M$ 均按 H2–H5 保持；所有外模数避开 $S$，$M$ 只支撑在 $S$ 上。对每个固定 cusp $k$，所需平方和是

$$
\sum_{0<q_n\le H}|t_k(n/M)|^2\ll_{f,M,\varepsilon}H^{1+\varepsilon}\qquad(H\ge1),
\tag{482.1}
$$

而 $\mathcal H\mathcal W$ 保留小参数奇性 $x^{-1/12-\varepsilon}$ 及任意大参数衰减，连同有限阶 Euler 导数界。系数 $t$ 对应 cusp 常数指数 $5/6$；非零常数产生的 progression 主项指数为 $11/12$。负 orientation 同时共轭整个族。

本节直接复用已有的有限 Gauss 恒等式、密度展开、主项 Möbius 估计和实际 Gram 界。新增 `repo-derived` 推导是：不把固定高估值乘子当成增长的自动形式 level，而在原固定 cusp 上重新组织全 Gauss 变换，再消费于 §460 的同一不拆分卷积。Dunn 的 [Metaplectic cusp forms and the large sieve, v4，(1.13)、§9、(9.26)](https://arxiv.org/html/2403.13151v4) 提供 cubic cusp 与平方自由外变量的先例；上述 sextic 原稿的 Proposition 4 与 Theorem 1 也限定平方自由外变量。这里不把这些已知结果另立为定理，也不主张文献优先权。

**引理 482.1（固定高估值部分的统一平均）。** 取一个指定的 good sixth-power-free 理想 $T$。设 $\alpha_a$ 支撑在 $q_a\asymp A$、$a$ good sixth-power-free、$a^{\ge2}\mid T^{\ge2}$，并有 $1\le A\le C_0X$。对固定光滑紧支撑 $\mathcal W$，有

$$
\begin{aligned}
\sum_a\alpha_a\sum_{a\mid n}t(n)\mathcal W(q_n/X)
={}&C_fX^{11/12}\widehat{\mathcal W}(11/12)
       \sum_a\frac{\alpha_a}{q_a}\\
&+O_\varepsilon\left((XAq_T)^\varepsilon
 X^{5/12}A^{1/6}\|\alpha\|_2\right).
\end{aligned}
\tag{482.2}
$$

隐常数依赖原固定形式、level、$C_0$、$\varepsilon$ 及有限阶 profile seminorms，不依赖 $T$。对 H4 的固定有限族及固定过滤 $\phi$，相同条件给出

$$
\begin{aligned}
&\sum_a\alpha_a\sum_{a\mid n}
 \phi(n)\rho_{\mathrm{prim},\tau;S}(n)\mathcal W(q_n/X)\\
&\quad=C_{\tau,Q,\phi}Z_SX^{5/6}\widehat{\mathcal W}(5/6)
       \sum_a\frac{\alpha_av(\operatorname{rad}a)}{q_a}
 +O_\varepsilon\left((XAq_T)^\varepsilon
 X^{1/3}A^{1/6}\|\alpha\|_2\right).
\end{aligned}
\tag{482.3}
$$

这里 $Z_S,v$ 与 H5 相同；$T$ 可以随尺度变化，费用已显式保留为 $q_T^\varepsilon$，不声称对所有高估值部分同时求和仍无费用。

证明。对原稿 §5 的有限 cusp 计算，不对 $r\mid a$ 使用平方自由的 $g(1,r)\overline{\chi_r(n)}$ 分解，而保持完整 $g(-n,r)$。矩阵恒等式、$f\circ\sigma_r$ 仅依赖 $r\bmod M$ 的结论、原 CRT 相位和 Mellin 核均不使用平方自由性。非单位 sixth-power-free $r$ 的局部指数在 $1,\ldots,5$，故 $\chi_r$ 在单位上非主；只有 $r=1$ 保留 cusp 常数。因此 progression 主项仍为原 $C_f/q_a$，完整对偶项为

$$
\frac X{q_a}\sum_{r\mid a}\frac{\chi_r(M)}{q_r}
 \sum_{n\ne0}t_{[r]}(n/M)e(-n\bar r/M)g(-n,r)
 \mathcal H\mathcal W\left(\frac{q_{n/M}X}{q_r^2}\right).
\tag{482.4}
$$

对非平方自由 $r$ 的局部加性求和，正是 H5 已用的完整 Gauss 版本。为进行平均，写

$$
r=se,\quad s=r^{\ge2},\quad e\text{ squarefree},\quad(s,e)=1,
\qquad S_1=q_s,\quad F=q_{\operatorname{rad}s},\quad
c=s/\operatorname{rad}s,\quad C=q_c=S_1/F.
\tag{482.5}
$$

固定 $s$，令 $q_e\asymp R$。字符 $\xi_s=\prod_{p^j\parallel s}\chi_p^j$ 在 $\operatorname{rad}s$ 上 primitive，因为每个 $2\le j\le5$ 的局部字符非主。加性正交及 CRT 给出

$$
\begin{gathered}
g(n,s)=0\quad(c\nmid n),\qquad
g(cm,s)=C\tau(\xi_s)\overline{\xi_s(m)},\qquad |\tau(\xi_s)|=\sqrt F,\\
g(-cm,se)=C\sqrt{Fq_e}\,\omega_{s,e}
       \overline{\xi_s(m)}\,\overline{\chi_e(m)},
       \qquad |\omega_{s,e}|=1.
\end{gathered}
\tag{482.6}
$$

字符保留自然零延拓，包括 $(m,\operatorname{rad}s)>1$ 时的零值。单位因子 $\omega_{s,e}$ 与 $m$ 无关；例如可取

$$
\omega_{s,e}=\chi_s(e)\chi_e(s)
 \frac{\tau(\xi_s)}{\sqrt F}\frac{g(1,e)}{\sqrt{q_e}}
 \overline{\xi_s(-1)}\,\overline{\chi_e(-c)}.
$$

单位 $s,e$ 的相应因子按 $1$ 解释。原相位 $e(-cm\overline{se}/M)$ 只需按 $e\bmod M$ 分成固定有限 sectors。固定 $s$ 与该 sector 后，cusp 系数是同一有限族的一个成员，不引入模 $s$ 的自动形式或扭曲平方和假设。

将所有模一因子吸收到外系数，定义

$$
\Psi_e=(Fq_e)^{-1/2}\omega'_{s,e}
       \sum_{\substack{q_a\asymp A\\se\mid a}}\frac{\alpha_a}{q_a}.
$$

每个 $se$ 的倍数至多 $O(A/(S_1R))$ 个。Cauchy 不等式及每个 $a$ 的除数界给出

$$
\sum_{q_e\asymp R}|\Psi_e|^2
\ll_\varepsilon(Aq_T)^\varepsilon
 A^{-1}S_1^{-1}F^{-1}R^{-2}\|\alpha\|_2^2.
\tag{482.7}
$$

频率块 $q_m\asymp H$ 上，对原固定 cusp 使用 (482.1)，只扩大频率集合：

$$
\sum_{q_m\asymp H}|t_{[se]}(cm/M)\xi_s(m)|^2
\ll_\varepsilon(CH)^{1+\varepsilon}.
\tag{482.8}
$$

这里不对稀疏子序列假设额外消去。由 (482.4) 的核参数，$m$ 的实际对偶长度是

$$
J\asymp_M\frac{S_1FR^2}{X},
\tag{482.9}
$$

不是 $S_1^2R^2/X$。对剩余平方自由 $e$ 列使用原完整 unrestricted-frequency 筛

$$
\Delta_6(H,R)\ll_\varepsilon(HR)^\varepsilon
 \left(H+H^{1/6}R+H^{5/6}R^{1/3}+H^{1/3}R^{5/6}\right).
\tag{482.10}
$$

当 $1\le H\le J$ 时，$S_1R\ll A\le C_0X$ 蕴含 $H/R\ll F$。将四项分别除以 $H^{1/6}R$，得到

$$
H^{5/6}/R,\quad1,\quad(H/R)^{2/3},\quad(H/R)^{1/6}.
$$

因 $R\ge1$，它们均为 $O(F^{5/6})$。故 $\Delta_6(H,R)\ll(HR)^\varepsilon F^{5/6}H^{1/6}R$。将 (482.7)、(482.8) 和该筛界相乘，并作原共同光滑核的 Mellin 分离，块贡献至多

$$
(XAq_T)^\varepsilon X A^{-1/2}F^{-7/12}R^{-1/2}
 H^{7/12}(J/H)^{1/12+\varepsilon}\|\alpha\|_2.
\tag{482.11}
$$

固定 $s,R$ 后选择内部损失 $0<\varepsilon<1/4$，小频率块留下正的 $H$ 幂，故由 $H\asymp J$ 控制。若 $J\ge1$、$H>J$，(482.10) 的各项关于 $H$ 的幂至多 $1$，所以该筛不超过临界筛界乘 $(H/J)^{1+\varepsilon}$；统一固定大参数衰减阶 $B=4$ 即可求和。若 $J<1$，原非零频率间隙给 $H\gg_M1$，用 $\Delta_6(H,R)\ll(HR)^\varepsilon HR$ 和同一 $B=4$，整条尾部不超过

$$
(XAq_T)^\varepsilon X A^{-1/2}F^{-1}R^{-1/2}J^B\|\alpha\|_2,
$$

它被 (482.11) 的临界表达式控制，因 $F\ge1$、$J<1$、$B>7/12$。固定 $M$ 的比较常数并入隐常数。这些分离始终使用每个块的一个共同变换，不在 $e$ 间选择不同的 profile。

在 $H\asymp J$ 的界中代入 (482.9)，全部 $F$ 幂抵消，得到

$$
\begin{aligned}
X A^{-1/2}F^{-7/12}R^{-1/2}J^{7/12}\|\alpha\|_2
&\ll X^{5/12}A^{-1/2}S_1^{7/12}R^{2/3}\|\alpha\|_2\\
&\ll X^{5/12}A^{1/6}S_1^{-1/12}\|\alpha\|_2.
\end{aligned}
\tag{482.12}
$$

$R$ dyads 的正幂和由 $R\ll A/S_1$ 控制。每个可能的 $s$ 都整除 $T$，数量至多 $\tau(T)$，故其和只支付 $q_T^\varepsilon$。这证明 (482.2)。

为恢复原 primitive 密度，按原稿 §7 使用 $w_S=1*h_S$，其中 $h_S(p)=-1/(q_p+1)$、$h_S(p^j)=0$（$j\ge2$）。对其平方自由除数写 $d=eg$，$e\mid\operatorname{rad}a$、$(g,a)=1$；则 $[a,d]=ag$，故即使 $a$ 非平方自由仍有精确展开

$$
\sum_{a\mid n}w_S(n)t(n)\mathcal W(q_n/X)
=w_S(a)\sum_{\substack{g\ {\rm squarefree}\\(g,aS)=1}}h_S(g)
 \sum_{ag\mid n}t(n)\mathcal W(q_n/X).
\tag{482.13}
$$

在 $q_g\asymp G$ 上聚合到 $a'=ag$ 的系数 $\beta$，除数 Cauchy 与理想计数给

$$
\|\beta\|_2^2\ll_\varepsilon(AG)^\varepsilon G^{-1}\|\alpha\|_2^2.
$$

$a'$ 的高估值部分未改变，且有贡献时 $AG\ll X$。由 (482.2)，该块误差为 $\ll(XAq_T)^\varepsilon X^{5/12}A^{1/6}G^{-1/3}\|\alpha\|_2$，其 dyadic 和收敛。主项延到全部 $g$ 的尾部至多 $X^{-1/12+\varepsilon}A^{1/2}\|\alpha\|_2$，被目标误差吸收；主项 Euler 因子为

$$
w_S(a)\sum_{(g,a)=1}\frac{h_S(g)}{q_g}
=Z_Sv(\operatorname{rad}a).
$$

最后使用 H4 的 $t(n)=q_n^{1/12}\rho_{\mathrm{full},\tau;S}(n)$，把 profile 换为 $x^{-1/12}\mathcal W(x)$ 并乘 $X^{-1/12}$，得到 (482.3)。固定过滤在 H4 密度关系之后施加，保留 H2–H5 的同一个有限族。证毕。

**定理 482.2（原卷积的全部小标记留数）。** 采用 §460 的同一个原向量、实际行、实际 Gram 和留数矩阵：

$$
b(h)=\omega_j(h)\sum_{dn=h}\mu(d)V(q_d/D)W(q_n/N),\qquad K=DN,
\quad\mathcal L_L=\{R\text{ good sixth-power-free}:q_R\le L\}.
\tag{482.14}
$$

$h,n$ 均不限重数，不要求 $(d,n)=1$。设 $2L\le D$、$L\le C_1N$，并保留 $L\le U^{1/3-\bar\varkappa}$、固定 $0<\bar\varkappa<1/3$ 的实际 G7 范围。除上述解析假设外，保留 §460 的 $B_0=7/8$ 原固定字符 inverse-$L$ 输入和同一共同成本包络 $\mathcal C$；包络覆盖固定有限族、所需 profile、共同 Mellin 分离及 reciprocal-strip 成本的实际有限乘积和，不随标签重新选择。则

$$
Q_{\rho,L}(b)\ll_\varepsilon\mathcal C^2(UKL)^\varepsilon U^{1/3}
 \left(K^{5/3}D^{-1/4}L^{2/3}
       +K^{2/3}D^{4/3}L^2\right).
\tag{482.15}
$$

证明。保留 (460.4) 的同一个 coherent $T_R$，并按 (460.10) 写

$$
g=(d,\operatorname{rad}R),\quad d=ge,\quad(e,R)=1,\quad
R_5=\prod_{v_p(R)=5}p,\quad c=(g,R_5),\quad T_g=Rg/c^6.
\tag{482.16}
$$

原 Möbius support 保证所有 $g,e$ squarefree。$Rd=c^6T_ge$，$T_g$ sixth-power-free 且 $(T_g,c)=1$。直接使用 (460.6) 的精确密度展开。对每个 $k\mid c$，实际固定乘子是 $T=T_gk$，变化模数是 $a=T_gke$；$e\mapsto a$ 单射，其长度、内和尺度与外系数范数分别为

$$
A_{g,k}=\frac{q_RDq_k}{q_c^6},\qquad
X_g=\frac{q_RK}{q_c^6},\qquad
\|\alpha\|_2\ll_\varepsilon\mathcal C(D/q_g)^{1/2+\varepsilon}.
\tag{482.17}
$$

这里 $a^{\ge2}\mid T^{\ge2}$，$A_{g,k}/X_g=q_k/N\le L/N$，所以引理 482.1 的范围成立。原非空 annuli 保证 $D/q_g\gg1$，且 $q_c^5\le q_R\le L$ 蕴含 $X_g\ge K/L^{1/5}\ge1$。固定端点只改变光滑分割的常数。$q_T\le q_R^2$，可并入共同次幂损失。

所有原有限 masks 仍在配对中：模原固定 $B$ 的函数沿 $h\equiv R^{-1}c^6m\pmod B$ 拉回，$R,c$ 均为该模的单位，所以只置换同一有限函数族。共同 Mellin 分离保留 $q_m/X_g=(q_d/D)(q_n/N)$，不生成标签依赖的新 profile。

含密度系数 $w_S(c)/q_k$ 的实际分支误差由 (482.3) 给出：

$$
\begin{aligned}
\frac{w_S(c)}{q_k}X_g^{1/3}A_{g,k}^{1/6}(D/q_g)^{1/2}
=w_S(c)K^{1/3}D^{2/3}q_R^{1/2}
 q_g^{-1/2}q_c^{-3}q_k^{-5/6}.
\end{aligned}
\tag{482.18}
$$

全部 $g,k$ 的和由局部乘积控制：

$$
\begin{aligned}
&\sum_{g\mid\operatorname{rad}R}
 w_S((g,R_5))q_g^{-1/2}q_{(g,R_5)}^{-3}
 \sum_{k\mid(g,R_5)}q_k^{-5/6}\\
&\quad=\prod_{\substack{p\mid R\\v_p(R)<5}}(1+q_p^{-1/2})
 \prod_{p\mid R_5}\left[1+w_S(p)q_p^{-7/2}(1+q_p^{-5/6})\right]
 \ll_\varepsilon q_R^\varepsilon.
\end{aligned}
\tag{482.19}
$$

因此没有额外的外长度或导子正幂。主项只复用 (460.8)、(460.11) 和 (460.12) 的第一项，保留必要的六次幂 $q_c$ 增益；得到

$$
|T_R|\ll_\varepsilon\mathcal C(Kq_R)^\varepsilon
 \left(K^{5/6}D^{-1/8}q_R^{-1/6}q_{R_5}^{1/8}
       +K^{1/3}D^{2/3}q_R^{1/2}\right).
\tag{482.20}
$$

先完成同一原 $h$ 的求和，再取标签平方和。由实际定义有 $Q_{\rho,L}\le U^{1/3}|\widehat\Omega(2/3)|^2\|G_L^{-1}\|\sum_R|T_R|^2$；G7 的统一 inverse Gram 成本与原 $\widehat\Omega(2/3)$ 成本的乘积，均与 (482.20) 的成本共同归入所定义的同一包络。第一项直接使用 (460.13) 的 $\sum_Rq_R^{-1/3}q_{R_5}^{1/4}\ll L^{2/3}$，第二项使用理想计数 $\sum_{q_R\le L}q_R\ll L^2$，即得 (482.15)。这没有假设不同标签正交。证毕。

**推论 482.3（平衡尺度及尚存的完整投影成本）。** 在同一条件下，取 $U\asymp K$、$D=N=\sqrt K$、$L=K^\ell$，其中固定 $0<\ell<1/6$ 且 G7 范围成立，则

$$
Q_{\rho,L}(b)\ll_\varepsilon\mathcal C^2K^\varepsilon
 \left(K^{15/8+2\ell/3}+K^{5/3+2\ell}\right).
\tag{482.21}
$$

记 $\eta_\ell=\min\{1/8-2\ell/3,\ 1/3-2\ell\}>0$。若共同成本满足 $\mathcal C=K^{o(1)}$，则 $Q_{\rho,L}(b)\ll K^{2-\eta_\ell+\varepsilon+o(1)}=o(K^2)$，其中最终 $\varepsilon<\eta_\ell$。若另使用 §460 所引 primitive-mean v2 的同一个 unrestricted adjoint，则完整投影仍只有

$$
\|P_LAb\|_2^2\ll_\varepsilon\mathcal C^2(UKL)^\varepsilon
 \left\{U^{1/3}\left(K^{5/3}D^{-1/4}L^{2/3}
       +K^{2/3}D^{4/3}L^2\right)+K^2L^{3/2}\right\}.
\tag{482.22}
$$

证明。前式直接代入 (482.15)，两个幂次均严格小于 $2$。后式复用 (460.14)–(460.15) 的同一个 $A^*V_L=\mathsf W_L+E_L$；本节不改变 $\|E_L\|_{\mathrm{HS}}^2\ll(UKL)^\varepsilon KL^{3/2}$，也不改变原 $\|b\|_2^2\ll\mathcal C^2K^{1+\varepsilon}$，故残留 $K^2L^{3/2}$。证毕。

(482.15) 加强 (460.3) 的留数项；对相同平衡尺度，(482.22) 将 (460.16) 的投影预算从 $K^{2+5\ell/3+\varepsilon}$ 改为 $K^{2+3\ell/2+\varepsilon}$。它仍不提供 $o(K^2)$ 的完整投影，更不提供同一完整补空间的估计。引理的固定形式条件、共同成本合同和实际 Gram 范围不可删除；其他长度、高度及 signed Robin restoration 不由上述估计推出。所有结果均为在明列解析输入下的纸面推导，未作 Lean 核验；RH 与每个 $n>5040$ 的严格 Robin 不等式仍未证明。

## 追加锚（本行以下为增补区）
