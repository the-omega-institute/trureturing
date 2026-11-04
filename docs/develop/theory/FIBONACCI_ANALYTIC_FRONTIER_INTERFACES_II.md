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

## 483. 六阶主字符块与全部小标记的原分子连续项

**约定与解析假设。** 保留 §482 的固定 Eisenstein 算术、原有限 masks、primary/ray sectors 和 level $M$，以及 [I1–I6](../../../Library/Analytic/faveri2026fixedorder.md#an-unchanged-numerator-term-in-the-primitive-continuous-adjoint) 的实际 full-series cusp 族。固定 $u=1+\eta+it$，其中 $0<\eta<1/12$ 满足 I3 的谱避让条件。I4 的统一平方和指数为 $1+\eta$；I5 的核在零附近为 $x^{-\eta/2-\varepsilon}$，在无穷远任意阶衰减，各有限阶 Euler 导数及 Mellin 分离具有多项式 $t$ 成本。这些解析输入在此作为前提，所有形式与 level 保持固定。

本节使用 [Type-I 原稿 v1](https://rstation.ai/api/v1/papers/riemann_hypothesis_8/versions/1/download) §§5–7 的固定形式变换与除数聚合，以及 [primitive-mean 原稿 v2](https://rstation.ai/api/v1/papers/riemann_hypothesis_10/versions/2/download) §§3、7 的完整局部反演和实际伴随公式。前者 Proposition 4 限定平方自由外模数，§482 限定外模数指数至多五；后者 Corollary 5 给通用连续余项均方，不给下述原系数消费。I9 和前卷 §457 的对应消费限定素标记。本节的 `repo-derived` 承重推导是估值六的主字符块及全部小标记的原分子连续项；已知筛法、Gauss 恒等式和反演公式只作输入，不另立为新结果，也不主张文献优先权。

**引理 483.1（含六阶主字符块的平均 full-series 估计）。** 取指定 good seventh-power-free 理想 $T$。设 $\alpha_a$ 支撑在 $q_a\asymp A$、$a$ good seventh-power-free、$a^{\ge2}\mid T^{\ge2}$，并有 $1\le A\le C_0X$。令 $\phi$ 为原固定 numerator mask，$\mathcal W$ 为固定光滑 annular profile，$\varphi(r)=|(\mathcal O/r)^\times|$。写

$$
\mathcal Q_6(a)=\{c\text{ squarefree}:c^6\mid a\}.
\tag{483.1}
$$

令 $C_{{\rm in},[r]}(u),C_{{\rm out},[r]}(u)$ 为该实际过滤形式在 $\sigma_r$ 的两项 cusp 常数经 I5 原 Mellin/Fourier 归一化所得的有限族。定义

$$
\begin{aligned}
\mathfrak M_a(X)=\frac1{q_a}\sum_{c\in\mathcal Q_6(a)}\varphi(c^6)
\big[&C_{{\rm in},[c^6]}(u)q_c^{-6u}X\widehat{\mathcal W}(1)\\
&+C_{{\rm out},[c^6]}(u)q_c^{6u-12}
 X^{2-u}\widehat{\mathcal W}(2-u)\big].
\end{aligned}
\tag{483.2}
$$

则

$$
\left|\sum_a\alpha_a\left(\sum_{a\mid n}\phi(n)
D_{\nu;S}(n,u)\mathcal W(q_n/X)-\mathfrak M_a(X)\right)\right|
\ll_\varepsilon(XAq_T)^\varepsilon(1+|t|)^B
 X^{5/12-\eta}A^{1/6+\eta}\|\alpha\|_2.
\tag{483.3}
$$

再令 $\mathcal v_u,z_u,Z_u,v_u$ 为 I1、I6 的原 Euler 因子；特别地 $\mathcal v_u=1*z_u$，而 $v_u$ 是主项局部因子，二者不混同。将内和乘 $\mathcal v_u(n)$ 后，主项变为 $Z_uv_u(\operatorname{rad}a)\mathfrak M_a(X)$，误差满足

$$
\left|\sum_a\alpha_a\left(\sum_{a\mid n}\phi(n)\mathcal v_u(n)
D_{\nu;S}(n,u)\mathcal W(q_n/X)
-Z_uv_u(\operatorname{rad}a)\mathfrak M_a(X)\right)\right|
\ll_\varepsilon(XAq_T)^\varepsilon(1+|t|)^B
 X^{5/12}A^{1/6}\|\alpha\|_2.
\tag{483.4}
$$

隐常数只依赖固定族、$\eta,\varepsilon,C_0$ 和有限阶 profile seminorms，不依赖 $T$；$q_T^\varepsilon$ 的显式费用不可删除。

证明。原稿 (5.1)–(5.3) 的矩阵、multiplier 与固定 cusp 族计算不使用模数平方自由性；保持完整 Gauss 和即可使用 §482 的 progression 变换。若 $r\mid a$，其单位字符主当且仅当各局部估值皆为六，即 $r=c^6$。在 cusp 常数指数 $\beta$ 上，有限单位和给出乘在原 $\beta$-cusp 常数前的运输因子

$$
\frac{\varphi(r)q_r^{-\beta}}{q_a}y^{-\beta}.
\tag{483.5}
$$

取 $\beta=u,2-u$，原归一化 Fourier 主项指数 $(1+\beta)/2$ 在去除 $q_n^{(u-1)/2}$ 后分别成为 $1,2-u$，因而恰得 (483.2)。大高度的两项常数仍按 I5 扣除，其 Gamma 抵消极点不新增主项。尤其不能把 $r=c^6\ne1$ 的小高度常数抹去，也不使用离开留数点的六次幂周期性。

为估计完整非恒定项，将每个 $r\mid a$ 唯一写为

$$
r=sb^6e,\quad v_p(s)\in\{2,3,4,5\},\quad
b,e\text{ squarefree},\quad(s,b)=(s,e)=(b,e)=1.
\tag{483.6}
$$

固定 $s,b$ 与有限 ray sector，写 $S_1=q_s$、$F=q_{\operatorname{rad}s}$、$B_1=q_b$、$q_e\asymp R$。非主的 $s$ 部分直接复用 (482.5)–(482.6)。主字符部分是原有限 Gauss/Ramanujan 恒等式

$$
\begin{gathered}
g(n,b^6)=0\quad(b^5\nmid n),\qquad
g(b^5m,b^6)=B_1^5c_b(m),\\
c_b(m)=\sum_{k\mid b}\mu(b/k)q_k\,\mathbf1_{k\mid m}.
\end{gathered}
\tag{483.7}
$$

因此逐个 $k\mid b$ 重编号 $n=(s/\operatorname{rad}s)b^5km$。相位与单位字符保留在系数中；progression 前因子为 $Xq_k/(q_a\sqrt F B_1\sqrt{q_e})$。将 $q_k$ 单独留在外面，其聚合外系数 $\Psi$ 的平方范数满足

$$
\|\Psi\|_2^2\ll_\varepsilon(Aq_T)^\varepsilon
 A^{-1}S_1^{-1}F^{-1}B_1^{-8}R^{-2}\|\alpha\|_2^2.
\tag{483.8}
$$

这是原除数 Cauchy：固定 $sb^6e$ 的倍数至多 $O(A/(S_1B_1^6R))$，前因子平方再贡献 $A^{-2}F^{-1}B_1^{-2}R^{-1}$。所有分支仍只读取同一原系数。

对 $q_m\asymp H$ 的频率块，不假设子序列具有新的均方消去；I4 直接给

$$
\sum_{q_m\asymp H}
|t_{u,[r]}((s/\operatorname{rad}s)b^5km/M)|^2
\ll (1+|t|)^B[(S_1/F)B_1^5q_kH]^{1+\eta+\varepsilon}.
\tag{483.9}
$$

此 $m$ 坐标的实际对偶尺度是

$$
J=\frac{S_1FB_1^7R^2}{q_kX}.
\tag{483.10}
$$

因为 $S_1B_1^6R\ll A\ll X$，在 $H\le J$ 时有 $H/R\ll FB_1/q_k$。原完整四项筛由此蕴含

$$
\Delta_6(H,R)\ll_\varepsilon(HR)^\varepsilon
 (FB_1/q_k)^{5/6}H^{1/6}R.
\tag{483.11}
$$

共同 smooth Mellin 分离、(483.8)–(483.11) 与核奇性给出的块费用，在 $H\asymp J$ 为

$$
(XAq_T)^\varepsilon(1+|t|)^B
 X^{5/12-\eta/2}A^{-1/2}S_1^{7/12+\eta}
 B_1^{3+6\eta}q_k^{1/2}R^{2/3+\eta}\|\alpha\|_2.
\tag{483.12}
$$

在 $H\le J$ 上，核奇性扣除后剩余 $H$ 幂为 $7/12-\varepsilon>0$，故 dyadic 和由临界块控制。$H>J$ 使用完整四项筛，额外损失至多为固定多项式，选择核衰减阶四即可求和。若 $J<1$，固定非零频率间隙与 $\Delta_6(H,R)\ll(HR)^\varepsilon HR$ 给出的尾部相对于 (483.12) 多出至多

$$
(q_k/(FB_1))^{5/12}J^{4-7/12-\eta/2},
\tag{483.13}
$$

其有界，因为 $q_k\le B_1$、$F\ge1$、$0<\eta<1/12$。固定 $M$ 的比较常数并入隐常数；全部分离使用块内共同 profile，不允许按 $e$ 选择另一个变换。

去除原 Fourier 归一化贡献 $X^{-\eta/2}$；再用 $R\ll A/(S_1B_1^6)$，(483.12) 变为

$$
(XAq_T)^\varepsilon(1+|t|)^B
 X^{5/12-\eta}A^{1/6+\eta}
 S_1^{-1/12}B_1^{-1}q_k^{1/2}\|\alpha\|_2.
\tag{483.14}
$$

这里 $F$ 与全部 $B_1^{6\eta}$ 均已抵消，且
$B_1^{-1}\sum_{k\mid b}q_k^{1/2}\ll_\varepsilon B_1^{-1/2+\varepsilon}$。所有可能 $s,b$ 来自指定 $T$，其数量只支付 $q_T^\varepsilon$。$R$ dyads 的正幂和由同一上端控制。这证明 (483.3)。

为加上原 Euler 密度，按 I1、I6 写平方自由密度除数为 $eg$，$e\mid\operatorname{rad}a$、$(g,a)=1$。精确展开为

$$
\sum_{a\mid n}\phi(n)\mathcal v_u(n)D(n,u)\mathcal W(q_n/X)
=\mathcal v_u(a)\sum_{\substack{g\text{ squarefree}\\(g,aS)=1}}z_u(g)
 \sum_{ag\mid n}\phi(n)D(n,u)\mathcal W(q_n/X).
\tag{483.15}
$$

$ag$ 的高估值部分及六阶主除数与 $a$ 相同。$q_g\asymp G$ 时，I6 的聚合系数范数为
$\ll(AG)^\varepsilon G^{-1/2-6\eta}\|\alpha\|_2$；(483.3) 给 $G^{-1/3-5\eta+\varepsilon}$ 的可求和误差。非空支持满足 $AG\ll X$，且 $(A/X)^\eta\ll1$，因此得到 (483.4) 的误差。

在 (483.2) 中，入射主和的绝对大小至多为除数费用，出射主和至多为除数费用乘 $A^\eta$。因 $A\ll X$，全部主项每个 $\alpha_a/q_a$ 的系数为 $O(X)$，连同原有限族的多项式 $t$ 费用。将 $g$ 主项延到无穷的尾部至多

$$
(XAq_T)^\varepsilon(1+|t|)^B
 A^{1/2}(A/X)^{6\eta}\|\alpha\|_2,
\tag{483.16}
$$

被 (483.4) 吸收。主项 Euler 乘积正是
$\mathcal v_u(a)\prod_{p\nmid aS}(1+z_u(p)/q_p)
=Z_uv_u(\operatorname{rad}a)$，证毕。

**定理 483.2（原卷积全部小标记的原分子连续项）。** 保留 (482.14) 的同一个原始 $b(h)$、全部标记 $R\in\mathcal L_L$（包括单位）、实际 $G_L$ 与 G7 范围。令

$$
C_R^0(t)=\sum_hb(h)\overline{\mathcal v_u(Rh)
D_{\nu_{[h]};S}(Rh,u)}.
\tag{483.17}
$$

在 primitive-mean 原稿 §7 的同一个实际 Mellin 伴随中，由 I2 精确分解 $E_L^*b=e_L^0+e_L^{\rm ref}$，其中 $e_L^0$ 积分 (483.17)，$e_L^{\rm ref}$ 保存每个非空反射选择。假设 $2L\le D$，并保留原固定字符 $B_0=7/8$ 的 inverse-$L$ 输入。令共同成本包络 $\mathcal C$ 覆盖原有限族、所需 smooth/Mellin seminorms、多项式 $t$ 积分、reciprocal-strip 与 G7 inverse-Gram 成本的实际有限乘积和。则

$$
|C_R^0(t)|\ll_\varepsilon\mathcal C(Kq_R)^\varepsilon(1+|t|)^B
 \left(KD^{-1/8}+K^{5/12}D^{2/3}q_R^{7/12}\right),
\tag{483.18}
$$

$$
Q_{E0,L}:=(e_L^0)^*G_L^{-1}e_L^0
\ll_\varepsilon\mathcal C^2(UKL)^\varepsilon U^{2\eta}
 \left(K^2D^{-1/4}L+K^{5/6}D^{4/3}L^{13/6}\right).
\tag{483.19}
$$

证明。对每个原 Möbius 变量写

$$
g=(d,\operatorname{rad}R),\quad d=ge,\quad(e,R)=1,
\qquad R_5=\prod_{v_p(R)=5}p.
\tag{483.20}
$$

直接把 (483.4) 用于实际外模数 $a=Rge$；不删除 $Rh$ 的六次幂。参数精确为

$$
T=Rg,\qquad A=q_RD,\qquad X=q_RK,\qquad
\|\alpha\|_2\ll_\varepsilon\mathcal C(D/q_g)^{1/2+\varepsilon}.
\tag{483.21}
$$

$a$ 的局部指数至多六，$a^{\ge2}=(Rg)^{\ge2}$，$q_T\le q_R^2$，$A/X=1/N$；原非空 annuli 及 $2L\le D$ 保证长度条件。原 fixed masks 沿 $h\equiv R^{-1}m\pmod B$ 拉回，只置换同一有限族。共同 Mellin 分离仍读取 $q_m/X=(q_d/D)(q_n/N)$，不额外选择依赖标签的任意 profile。于是误差为

$$
\mathcal C(Kq_R)^\varepsilon(1+|t|)^B
 K^{5/12}D^{2/3}q_R^{7/12}
 \sum_{g\mid\operatorname{rad}R}q_g^{-1/2},
\tag{483.22}
$$

最后的和只支付 $q_R^\varepsilon$。

主项的 $c$ 恰好遍历 $c\mid(g,R_5)$，与变化的 $e$ 无关；$\operatorname{rad}a=\operatorname{rad}R\,e$。故 (483.2) 的原有限 cusp 常数和 ray 相位可在每个 $g,c$ 分支固定后，直接复用 I7 的 $\mu(e)v_u(e)\xi(e)/q_e$ smooth inverse-$L$ 估计。局部因子的正常收敛域、所选 $B_0$ 和字符有限族均不改变。入射常数前的大小满足 $\varphi(c^6)q_c^{-6\Re u}\le q_c^{-6\eta}$，出射部分满足 $\varphi(c^6)q_c^{6\Re u-12}\le q_c^{6\eta}$。相应主项上界分别为

$$
\begin{aligned}
&\mathcal C(Kq_R)^\varepsilon(1+|t|)^B KD^{-1/8}
 \sum_{g\mid\operatorname{rad}R}q_g^{-7/8}
 \sum_{c\mid(g,R_5)}q_c^{-6\eta},\\
&\mathcal C(Kq_R)^\varepsilon(1+|t|)^B K^{1-\eta}q_R^{-\eta}D^{-1/8}
 \sum_{g\mid\operatorname{rad}R}q_g^{-7/8}
 \sum_{c\mid(g,R_5)}q_c^{6\eta}.
\end{aligned}
\tag{483.23}
$$

两和均为 $O_\varepsilon(q_R^\varepsilon)$：出射一项在 $p\mid R_5$ 的局部因子是
$1+q_p^{-7/8}+q_p^{-7/8+6\eta}$，而 $6\eta<1/2<7/8$。这证明 (483.18)，没有用不同分支的分别最优值替代原来的联合系数。

最后在原实际伴随中乘 $U^\eta$，对原快速衰减 row Mellin profile 积分，再用同一 G7 和
$\sum_{q_R\le L}1\ll L$、$\sum_{q_R\le L}q_R^{7/6}\ll L^{13/6}$。先完成每个原 $h$ 的 coherent 求和后才取标签平方和，得到 (483.19)，不假设标签正交。证毕。

**推论 483.3（平衡尺度的连续原分子预算）。** 在定理 483.2 的条件下，取 $U\asymp K$、$D=N=\sqrt K$、$L=K^\ell$，其中固定 $0<\ell<1/8$ 且实际 G7 范围成立。定义

$$
\zeta_{\ell,\eta}
=\min\{1/8-\ell,\ 1/2-13\ell/6\}-2\eta.
\tag{483.24}
$$

可选足够小且满足 I3 的固定 $\eta>0$ 使 $\zeta_{\ell,\eta}>0$。若共同成本为 $\mathcal C=K^{o(1)}$，则

$$
Q_{E0,L}\ll_\varepsilon\mathcal C^2K^\varepsilon
 \left(K^{15/8+\ell+2\eta}+K^{3/2+13\ell/6+2\eta}\right)
=o(K^2)
\tag{483.25}
$$

其中最终 $\varepsilon<\zeta_{\ell,\eta}$。另保留 §482 的解析输入，并将两处成本纳入同一共同包络后，与 (482.21) 联合可在同一实际投影中控制 $w_L+e_L^0$，其中 $w_L=\mathsf W_L^*b$；完整向量仍为

$$
\|P_LAb\|_2^2
=\|G_L^{-1/2}(w_L+e_L^0+e_L^{\rm ref})\|_2^2.
\tag{483.26}
$$

证明。(483.25) 直接代入 (483.19)；I3 允许的固定 $\eta$ 任意接近零。留数与连续项采用相同 $b,G_L$，其和用平方范数三角不等式控制。(483.26) 是原精确伴随分解。该分解未给 $e_L^{\rm ref}$ 的新上界，也未给完整正交补的上界；不同长度、高度、signed Robin restoration、全部 $n>5040$ 的严格 Robin 不等式和 RH 均不由上述估计推出。证毕。

## 追加锚（本行以下为增补区）

## 484. 全部小标记的反射主项与完整投影预算

**约定与解析假设。** 保留 §482–483 的原卷积 $b(h)$、全部 good sixth-power-free 标记 $q_R\le L$（包括单位）、实际 $G_L$ 与原 row Mellin profile。采用前卷假设 454.2 的解析输入，以及 [I1–I16、I14a、H1–H8、G7](../../../Library/Analytic/faveri2026fixedorder.md#an-unchanged-numerator-term-in-the-primitive-continuous-adjoint) 和 [PR1–PR10、SH6](../../../Library/Analytic/openai2026quasirh.md#joint-control-of-all-powerful-prime-reflection-choices) 的精确有限变换、原固定字符 $B_0=7/8$ zero-free/reciprocal-strip 输入及移动删因子合同。固定 $u=1+\eta+it$，$0<\eta<1/48$ 满足同一固定 cusp 的谱避让条件。特别地，$B_0=7/8$ 是保留的解析前提，不在此宣告为无条件定理。

本节直接复用前卷 (456.5)–(456.11) 的完整 Gauss 平方支撑与 finite Euler split、(457.4)–(457.7) 的保留谱幂次正均方，以及 [Type-I 原稿 v1](https://rstation.ai/api/v1/papers/riemann_hypothesis_8/versions/1/download) §§5–7、[primitive-mean 原稿 v2](https://rstation.ai/api/v1/papers/riemann_hypothesis_10/versions/2/download) §§3–7 的实际原始 series 和局部反演。新增 `repo-derived` 推导是带固定标记乘子的多 mark 主项消费及其全部小标记原系数预算；不对上述筛、Gauss、反演、正均方或 inverse-$L$ 输入另作新结果或文献优先权断言。

**引理 484.1（固定乘子的多 mark 主项消费）。** 取 PR4 的互素平方自由低反射块 $P_i$，其真实总估值为 $j_i\in\{1,2,3,4\}$。写

$$
s_i=4-j_i,\quad b_i=5-j_i,\quad k_i=j_i+1,\qquad
Z=\prod_iP_i,\quad \Pi=\prod_iP_i^{s_i},\quad
V=q_\Pi,\quad R_0=\prod_iP_i^{b_i}.
\tag{484.1}
$$

允许没有低 mark，此时上述乘积均为单位。固定 seventh-power-free $P$，$(P,Z)=1$。原剩余外变量 $a_0$ 平方自由并避开 $PZ$；所有变量仍避开原固定坏素。取 $m$ 的真实 annular 尺度 $Y$、原完整 reflected scalar 与 character mark、原 numerator masks，full numerator 为 $P\Pi m$，并在 $a_0\mid m$ 上求和。反射 scalar 和 mark 保持 PR1、PR4 的实际顺序、相位、共轭与 ray 运输，不独立选择系数。

令 $\mathfrak P_{P,a_0}(Y)$ 为这份 unweighted pairing 的完整小高度主项。存在原固定有限 cusp 族的实际系数 $A_{{\rm in},[R_0c^6]}(u)$、$A_{{\rm out},[R_0c^6]}(u)$，包含该支的原单位相位，使

$$
\begin{aligned}
\mathfrak P_{P,a_0}(Y)=\frac1{q_{a_0}}
\sum_{\substack{c\ {\rm sf}\\c^6\mid P}}\varphi(c^6)
\big[&q_c^{-6u}A_{{\rm in},[R_0c^6]}(u)Y\widehat{\mathcal W}(1)\\
&+q_P^{1-u}q_c^{6u-12}A_{{\rm out},[R_0c^6]}(u)
Y^{2-u}\widehat{\mathcal W}(2-u)\big].
\end{aligned}
\tag{484.2}
$$

这些系数与 $a_0$ 无关，并满足

$$
\begin{aligned}
|A_{{\rm in},[R_0c^6]}(u)|&\ll(1+|t|)^B\prod_iq_{P_i}^{-1-6\eta},\\
|A_{{\rm out},[R_0c^6]}(u)|&\ll(1+|t|)^B\prod_iq_{P_i}^{-1-j_i\eta}.
\end{aligned}
\tag{484.3}
$$

完整 unweighted 非恒定项的误差为

$$
\ll_\varepsilon(Yq_Pq_{a_0}q_Z)^\varepsilon(1+|t|)^B
q_P^{1/2}Y^{-\eta}q_{a_0}^{1/2+\eta}
\prod_iq_{P_i}^{3-j_i/2-j_i\eta}.
\tag{484.4}
$$

插入原有限 Euler 密度及冻结分母后，主项为
$F_T(u)Z_u^T v_u(a_0)\mathfrak P_{P,a_0}(Y)$；其中 $T$ 是原冻结／删除素支持的平方自由乘积，包含 $PZ$ 的支持及该支全部已选支持（包括高六层支），$a_0$ 避开 $T$。$F_T$ 是每个冻结分母只计一次的实际乘积，$Z_u^T$ 如 SH6 前的原 Euler 乘积。它们与 $a_0$ 无关且在固定 $\eta$ 下一致有界。(484.2) 右侧括号连同 $c$-和是不含 $q_{a_0}^{-1}$ 的 principal sum；$\mathfrak P_{P,a_0}$ 已含该分母，完成主项不再乘第二份。全部误差和 finite polar tails 满足

$$
\operatorname{Err}_{P,\mathrm{wt}}
\ll_\varepsilon(Yq_Pq_{a_0}q_Zq_T)^\varepsilon(1+|t|)^B
q_P^{1/2}Y^{5/12+\eta}
\prod_iq_{P_i}^{(26-5j_i)/12+12\eta}.
\tag{484.5}
$$

若 $a_0=d_0$ 为原 Möbius 外变量，保持原固定有限字符和 normalized smooth profiles，则两份完成主项均可使用同一 $D_0^{-1/8}$ 位移；不需要将其绝对值先估成 $Y/q_p$。

证明。原 full Fourier 尺度是 $X=q_PVY$，外模数为 $a=Pa_0$。PR4 的完整有限变换不要求 $r\mid a$ 平方自由。零频单位字符主当且仅当 $r=c^6$；因 $a_0$ 平方自由且 $(a_0,P)=1$，这恰为 $c^6\mid P$。此时

$$
\chi_{P_i}(c^6)^{-k_i}=1.
\tag{484.6}
$$

PR4 的 mark Ramanujan 常数与原 $\gamma_{k_i}\tau_i$ 相位配对仍精确成立。按 I11 的原 normalization 恢复 $m$ 坐标后，incoming 的 $q_P$ 抵消，outgoing 留下 $q_P^{1-u}$，给出 (484.2)–(484.3)。Cusp 分量仅依赖 $R_0c^6\bmod\mathfrak M$；剩余固定 $P$ 相位留在系数中。原大高度常数仍按同一变换扣除，Gamma 抵消的极点不新增主项。

对非零频率直接使用 (456.5)–(456.7) 的完整 imprimitive Gauss 平方界。它允许 $a$ 在 $P$ 处估值六，且 $(P,\Pi)=1$ 使原双频支撑计数不变。原计算中的 $X^{-\eta}q_a^{1/2+\eta}$ 现在恰贡献额外 $q_P^{1/2}$，得到 (484.4)。固定非零频率间隙、原核奇性及大参数任意阶衰减仍支付全部 dyads；不按外变量选择不同 profile，不把 $t(\Pi n)$ 的平方质量假设为密度分布。

原密度只在允许的 $g$ 上展开，保留冻结分母。$g$ 避开全部 $T$；$\operatorname{lcm}(a_0,g)$ 仍平方自由，故六阶主除数和 (484.2) 的常数不改变。取 $q_g\le G$，原误差为 (484.4) 乘 $G^{1/2-5\eta+\varepsilon}$。Full-$D$ convexity 的大 $g$ 尾部不超过

$$
(Yq_Pq_{a_0}q_Zq_T)^\varepsilon(1+|t|)^B
\frac{q_P^{1/4-\eta/2}Y^{5/4-\eta/2}}{q_{a_0}G^{1+6\eta}}
\prod_iq_{P_i}^{1/2-j_i/4-(3+j_i/2)\eta}.
\tag{484.7}
$$

Incoming 的 $c$ 和只有除数费用；outgoing 也如此，因为
$q_P^{-\eta}q_c^{6\eta}\le1$。因此两份 finite polar tails 至多为次幂及多项式高度成本乘
$Y(q_{a_0}q_Z)^{-1}G^{-1-6\eta}$。取原分裂点

$$
G=Y^{5/6}q_{a_0}^{-1}\prod_iq_{P_i}^{-5/3+j_i/6}.
\tag{484.8}
$$

若 $G\ge1$，(456.10)–(456.11) 的同一指数计算适用；$q_P^{1/4-\eta/2}\le q_P^{1/2}$，故得到 (484.5)。若 $G<1$，则
$q_{a_0}>Y^{5/6}\prod_iq_{P_i}^{-5/3+j_i/6}$；直接计数整个原支给出

$$
q_P^{1/4-\eta/2}Y^{5/12-\eta/2}
\prod_iq_{P_i}^{(26-5j_i)/12-(3+j_i/2)\eta},
\tag{484.9}
$$

完整 polar main 则至多为
$Y^{1/6}\prod_iq_{P_i}^{2/3-j_i/6}$，均被 (484.5) 控制。非空 $m$-annulus 保证 $Y$ 有固定正下界，故 bounded subunit 支撑同样成立。

付清上述尾项后才完成 Euler 主项，得到所述 $F_T Z_u^T v_u(a_0)$。在 $a_0=d_0$ 的原系数和中，(484.6) 保证没有增长的 $d_0$-字符；实际算术权是

$$
\frac{\mu(d_0)v_u(d_0)\xi(d_0)}{q_{d_0}},
\qquad(d_0,T)=1,
\tag{484.10}
$$

其中 $\xi$ 仅遍历原固定有限族。两个 polar 泛函只增加共同 normalized smooth/Mellin profiles。直接使用 I7 的 $B_0=7/8$ 位移及 SH6 的删除因子次幂费用，即得 $D_0^{-1/8}$。所有复相位在这之前保留在实际 signed pairing 中。证毕。

**定理 484.2（全部小标记的完整连续反射向量）。** 在上述条件下，以 I2 的同一固定反演顺序定义 $e_L^{\rm ref}$，包含全部非空第二选择，令
$Q_{{\rm ref},L}=(e_L^{\rm ref})^*G_L^{-1}e_L^{\rm ref}$。记 $T_1,T_2,T_3>1$ 为原 valuation-one、two、three 非标签反射乘积的共同截断阈值。一次选定共同成本包络 $\mathcal C$，覆盖原有限族、所需 profiles、核、Mellin、高度、inverse-$L$ 与 G7 成本的实际有限乘积和；不随标记或分支重选。则

$$
\begin{aligned}
Q_{{\rm ref},L}\ll_\varepsilon{}&\mathcal C^2(UKL)^\varepsilon U^{2\eta}L^{12}
\big[K^2D^{-1/4}\\
&+K^{5/6+2\eta}D^2T_1^{14/3+22\eta}
 T_2^{3+20\eta}T_3^{4/3+18\eta}\\
&+K^2(T_2^{-2}+T_3^{-9/2})+K^{2-4\eta}\\
&+K^{2-\eta}T_1^{-1/2-6\eta}+K^2T_1^{-1-4\eta}\big].
\end{aligned}
\tag{484.11}
$$

证明。先固定一个真实标记 $R$。对每个 $p\mid R$ 记 $t_p=v_p(R)\in\{1,\ldots,5\}$，按原 $j=v_p(Rh)$ 分为 $t_p\le j\le5$ 和 $j\ge6$，并分原 Möbius 变量在 $p$ 处的估值 $0$ 或 $1$。低支精确采用
$e=0,\ldots,\min(1,j-t_p)$、$d=p^ed_0$、$n=p^{j-t_p-e}n_0$，其中 $p\nmid d_0n_0$；故原 $h$ 提取 $p^{j-t_p}$。$j\le4$ 的第二选择成为 PR4 的同一低 mark，raw numerator 为 $p^{4-j}m$，其 $p\nmid n_0$ 仍由原 mark 的自然零延拓执行；$j=5$ 没有第二选择。高支精确写 $h=p^{6-t_p}m$，$m$ 不限重数，第一选择保留 $D(p^6m,u)$，第二选择保留原 $-q_p^{6-6u}D(m,u)$。不约化离开留数点的 raw 估值。

对低第一选择，仅在原 $n_0$ 中使用
$\mathbf1_{p\nmid n_0}=1-\mathbf1_{p\mid n_0}$；$d_0$ 已避开 $p$。第二项令 $n_0=pn_1$，同步改变原 profile、原 $h$、full numerator、mask 和全部混合相位。该项不再声称单独是原低估值来源，但两项之差精确等于原单位限制；原 $\mu(d)$ 及原符号不变。新的 $h$ 提取指数至多为 $6-t_p$，numerator 指数至多为六。

由此得到至多 $64^{\omega(R)}\ll_\varepsilon q_R^\varepsilon$ 份精确有限 sector。各份具有标签提取 $J_R$、未反射标签乘子 $P$ 和低标签 marks；写

$$
H_R=P\prod_{i\text{ 为标签低 mark}}P_i^{4-j_i},\qquad
q_{J_R}\le q_R^5,\quad q_P\le q_R^6,\quad q_{H_R}\le q_R^6.
\tag{484.12}
$$

$P$ 与所有低 marks 互素；$H_R$ 还包含选中标签的强制 numerator 因子，不能在正均方中将它误写成 $P$。标签 branch scalar 的模至多为一，连同原统一有界分母；所有标签相位和固定 $216$ 个 ray 分量均保留。Frozen denominators 与原 Euler 展开遵守每素因子只计一次的 SH5–SH6。

其余所选素因子避开 $R$。令 $C=A_1$ 为其中原 valuation-one 的乘积，$A_2,A_3,A_4,B$ 为原 valuation $2,3,4,\ge6$ 的乘积；写
$x_j=q_{A_j}$、$z=q_B$、$W=x_2^2x_3^3x_4^4z^6$、$H_0=A_2^2A_3$。原变量仍按 PR3、(454.14) 提取 $E_j\mid A_j$、$F\mid B$，其余外变量 $d_0$ 避开全部选中支持和 $R$；没有附加 $(d_0,n_0)=1$。实际剩余尺度是

$$
Y=\frac{K}{q_{J_R}q_CW},\qquad
D_0=\frac{D}{q_{E_R}(\prod_{j=1}^4q_{E_j})q_F},
\quad E_R\mid\operatorname{rad}R,
\tag{484.13}
$$

各 sector 保留自身非空 annuli。此时引理 484.1 的 $T$ 冻结 $\operatorname{rad}R$ 及全部已选非标签支持（含 $B$），再并入原固定坏素；Euler 变量 $g$ 避开全部 $T$。标签有限容斥只在 $J_R$、$P$ 和原 profile 中增加已说明的因子。

在 $q_C\le T_1,x_2\le T_2,x_3\le T_3$ 上使用引理 484.1。标签低 mark 的误差费用至多为 $q_R^{7/4+12\eta}$，而 $q_P^{1/2}\le q_R^3$，故可共同上界为 $q_R^5$。非标签的原变量误差质量与 (456.13) 相同，其指数依次为 $4/3+11\eta,1/2+10\eta,-1/3+9\eta,-7/6+8\eta,-5/2-6\eta$。后两类绝对可和，前三区域按共同阈值求和，得到

$$
\begin{aligned}
|C_{R,\rm small}(t)|\ll_\varepsilon{}&\mathcal C(Kq_R)^\varepsilon(1+|t|)^Bq_R^5
\big[KD^{-1/8}\\
&+K^{5/12+\eta}D
T_1^{7/3+11\eta}T_2^{3/2+10\eta}T_3^{2/3+9\eta}\big].
\end{aligned}
\tag{484.14}
$$

第一项在同一 signed pairing 中使用 (484.10)，没有以反射部分的大小代替整个 $R$。具体地，incoming 的非标签质量为
$\prod_{j=1}^4x_j^{-j-1-6\eta}z^{-6-6\eta}$，outgoing 为 $\prod_{j=1}^4x_j^{-j-1}z^{-6}$；连 $E_j,F$ 的 $1/8$ 次幂损失仍绝对可和。标签 $E_R$ 的损失至多为 $q_R^{1/8}$，已被 $q_R^5$ 覆盖；$J_R\ge1$ 的缩短只改善上述上界。有限极点尾项先由 (484.5) 支付，之后才使用完成主项。

对 $q_C>T_1$，直接复用 (457.4)–(457.7)，以实际 multiplier $H_RH_0$、尺度 (484.13)、系数侧权重 $d(m)^{1/2}$ 和正均方侧倒权重作同一 Cauchy。这里 $d(m)$ 是平方部分的 norm。因 $6\eta<1/2$，原平方部分和仍收敛。逐 $R$ 使用该正均方，不合并标签，因此无需素标记专属的 $d(pm)$ 一致估计。将真实 $q_{H_R}^{1/2-\eta}\le q_R^3$ 保留，原 powerful 质量仍为 (457.9) 后的同一可和质量；得到逐标签的平方 pairing 上界

$$
\mathcal C^2(Kq_R)^\varepsilon(1+|t|)^Bq_R^3
\big[K^{2-4\eta}+K^{2-\eta}T_1^{-1/2-6\eta}
 +K^2T_1^{-1-4\eta}\big].
\tag{484.15}
$$

对 $q_C\le T_1$ 且 $x_2>T_2$ 或 $x_3>T_3$，使用 (454.11) 的同一粗正均方，multiplier 仍为 $H_RH_0$。$C$ dyads 只支付次幂；原质量尾和给出逐标签平方费用

$$
\mathcal C^2(Kq_R)^\varepsilon(1+|t|)^Bq_R^3K^2
(T_2^{-2}+T_3^{-9/2}).
\tag{484.16}
$$

标签乘子不与这些非标签块共享素支持，不能把它们当成新增自由块再求和。全部原系数、mask 和同时选择始终在原 pairing 中，仅在这些正范数中放松支持。无非空反射的部分直接复用 §483，不加入反射向量。

所有实际 label sectors 先在同一向量范数中用除数 Cauchy 汇总。理想计数给 $\sum_{q_R\le L}q_R^{10}\ll L^{11}$、$\sum_{q_R\le L}q_R^3\ll L^4$。分配内部小幂后，统一保守付 $L^{12}$，再恢复原实际 Mellin 的 $U^{2\eta}$ 与同一 G7，即得 (484.11)。证毕。

**推论 484.3（指定平衡扇区的全部小标记完整投影）。** 在同一条件和实际 G7 范围下，取

$$
U\asymp K,\quad D=N=\sqrt K,\quad L=K^\ell,
\quad 0<\ell<10^{-6},\qquad 7\ell<\eta<8\ell,
\tag{484.17}
$$

其中固定 $\eta$ 满足原谱避让条件，并取
$T_1=K^{1/100}$、$T_2=K^{1/500}$、$T_3=K^{1/1000}$。若全部所需共同成本为 $\mathcal C=K^{o(1)}$，则对每个最终 $\varepsilon>0$，先分配内部小幂后，

$$
Q_{{\rm ref},L}\ll_\varepsilon\mathcal C^2K^{2-\ell+\varepsilon},
\qquad
\|P_LAb\|_2^2\ll_\varepsilon\mathcal C^2K^{2-\ell+\varepsilon}
=o(K^2)
\tag{484.18}
$$

其中最后取 $\varepsilon<\ell/2$，$P_L$ 是同一全部小标记的实际行投影。

证明。(484.11) 临界项恢复 Mellin 后的裕度为 $2\eta-12\ell>2\ell$。其余各项的裕度依次为

$$
\begin{gathered}
\tfrac18-2\eta-12\ell,\\
\tfrac16-4\eta-12\ell
-\tfrac{14/3+22\eta}{100}-\tfrac{3+20\eta}{500}
-\tfrac{4/3+18\eta}{1000},\\
\tfrac2{500}-2\eta-12\ell,\quad
\tfrac9{2000}-2\eta-12\ell,\\
\tfrac{1/2+6\eta}{100}-\eta-12\ell,\qquad
\tfrac{1+4\eta}{100}-2\eta-12\ell.
\end{gathered}
\tag{484.19}
$$

在 (484.17) 的整个范围内，它们均大于 $2\ell$；例如第二个大于 $11/100$，最小的 powerful-tail 裕度大于 $39/10000$。保留 $\ell$ 作为共同节省即可分配内部小幂。原固定商空间的离散谱允许在非空区间 $(7\ell,8\ell)$ 内选择合法固定 $\eta$。

另保留 §482 的留数输入及 §483 的连续原分子输入，将所有成本纳入同一包络。它们在本尺度和同一 $\eta$ 下有更大的正裕度。由同一精确分解

$$
\|P_LAb\|_2^2
=\|G_L^{-1/2}(w_L+e_L^0+e_L^{\rm ref})\|_2^2
\tag{484.20}
$$

使用有限和平方范数界，得到 (484.18)。完整补空间仍是同一个未被上述估计控制的 $\|(I-P_L)Ab\|_2^2$；其他长度、高度、原 growing-height allowance、F4 transfer 和 signed Robin restoration 也未由本推论供应。RH 与全部 $n>5040$ 的严格 Robin 不等式仍未由此推出。证毕。

## 追加锚（本行以下为增补区）

## 485. 原前向价格核的无条件双侧振荡下界

沿用 §481 的 $E,H_x,\lambda,w,\rho_x$ 与 (481.1) 的 $\mathcal T$。本节把命题 481.1 的误差输入由 von Koch 界放宽为任意幂界，从而去掉命题 481.2 对 RH 的依赖，并对全实中心的 $\mathcal T$ 给出无条件的单侧振荡常数 $1/2$。推论 481.3 中的常数 $c_Q=(\sqrt2-1)/4$ 由此提高为 $1/2$，且证明不经 S5 来源、GA1/GA2 来源或完整 $Q$ 供应。

记
$$
\Theta=\sup\{\Re\rho:\ \zeta(\rho)=0,\ 0<\Re\rho<1\}.
$$
经典输入如下：零点上确界的误差估计
$$
\forall\varepsilon>0\ \exists C_\varepsilon:\quad |E(t)|\le C_\varepsilon t^{\Theta+\varepsilon}\qquad(t\ge2),
\tag{485.1}
$$
非平凡零点的存在性，$\zeta$ 在实区间 $(0,1)$ 与 $(1,\infty)$ 无零点，以及 [Widder, The Laplace Transform, Ch. II, Thm 5b](../../../Library/Fourier/widder1941laplace.md)：若 $g\ge0$ 在 $[y_0,\infty)$ 上局部可积，其 Laplace 变换的收敛横坐标 $c_g$ 有限，则 $c_g$ 是该变换的奇点。

**命题 485.1（幂误差下的 Mellin 留数）。** 设 $\alpha\ge0$，且存在 $C,t_0$ 使 $|E(t)|\le Ct^\alpha$ 对 $t\ge t_0$ 成立。对固定 $x_0\ge3$，令 $\mathcal F(s)=\int_{x_0}^\infty\mathcal T(x)x^{-s-1}\,dx$，它在 $\Re s>\max(1/2,\alpha-3/10)$ 绝对收敛。则存在在
$$
D_\alpha=\{s:\Re s>\alpha-7/10\}
$$
上全纯的 $R_{x_0,\alpha}$，使在上述收敛半平面内
$$
\mathcal F(s)=-\frac12\frac{\zeta'}{\zeta}(s+1/2)-\frac1{2(s-1/2)}+R_{x_0,\alpha}(s),
\tag{485.2}
$$
并且 $|\mathcal T(x)|\ll x^{\alpha-3/10}$。

证明。$\mathcal T$ 由 (481.2) 的有限有符号价格式给出，故为 Borel 可测且局部有界。积分区间长为 $x^{4/5}$，前因子为 $x^{1/2}/x^{8/5}$，得点值界 $|\mathcal T(x)|\ll x^{\alpha-3/10}$；因此 $\mathcal F$ 在 $\Re s>\alpha-3/10$ 绝对收敛。在 $\Re s>\max(1/2,\alpha-3/10)$ 作 (481.4) 的绝对 Fubini 交换，伴随核满足 (481.6)，其中余项对每个紧集 $K\subset\mathbb C$ 一致地有
$$
|r_s(t)|\le C_Kt^{-\Re s-7/10},\qquad |\partial_tr_s(t)|\le C_Kt^{-\Re s-17/10}.
$$
在 $(A,B]$ 上作 Stieltjes 分部积分：
$$
\int_{(A,B]}r_s\,dE=r_s(B)E(B)-r_s(A)E(A)-\int_A^BE(t)\,\partial_tr_s(t)\,dt.
$$
边界项为 $O(B^{\alpha-\Re s-7/10})$，导数积分的被积函数为 $O(t^{\alpha-\Re s-17/10})$；二者在 $\Re s>\alpha-7/10$ 的每个紧集上一致地分别趋于零与绝对收敛，故余项部分在 $D_\alpha$ 全纯。主项与有限区间修正同命题 481.1 的证明，给出 (485.2)。证毕。

**定理 485.2（无条件下侧振荡）。** 无条件地，
$$
\liminf_{x\to\infty}\mathcal T(x)\le-\frac12.
\tag{485.3}
$$
若 RH 不成立，则 $\liminf_{x\to\infty}\mathcal T(x)=-\infty$。

证明。设有限常数 $\kappa$ 与 $x_0$ 使 $\mathcal T(x)\ge-\kappa$ 对 $x\ge x_0$ 成立。令 $g(y)=\mathcal T(e^y)+\kappa\ge0$，$y_0=\log x_0$，
$$
G(s)=\int_{y_0}^\infty g(y)e^{-sy}\,dy=\mathcal F(s)+\frac{\kappa x_0^{-s}}s,
$$
后一等式在两边均绝对收敛处成立。$g$ 局部有界可测，且由命题 485.1 的点值界，$c_g<+\infty$（可能为 $-\infty$）。

先设 RH 不成立，于是 $\Theta>1/2$。由上确界的定义，取零点 $\rho=\beta+i\gamma$，重数为 $m\ge1$，使 $\beta>\max(1/2,\Theta-1/5)$；再取 $0<\varepsilon<\beta-\Theta+1/5$，令 $\alpha=\Theta+\varepsilon$，由 (485.1) 适用命题 485.1。记 $b=\max(0,\alpha-7/10)$ 与 $\sigma_\rho=\beta-1/2$，则 $\sigma_\rho>b$。

$G$ 沿实射线 $(b,\infty)$ 全纯：对实数 $s>b\ge0$，$s+1/2\in(1/2,\infty)$，其中 $\zeta$ 无零点；$s=1/2$ 处 $\zeta$ 在 $1$ 的极点与 $-1/(2(s-1/2))$ 相消；$\kappa x_0^{-s}/s$ 在 $s>0$ 全纯。若 $c_g>b$，则 $c_g$ 有限且为 $G$ 的正则点，与 Landau–Widder 定理矛盾；故 $c_g\le b$。于是对每个 $\sigma>b$，原积分收敛，且由恒等定理它与 (485.2) 给出的延拓在 $\Re s>b$ 上一致。由 $g\ge0$，
$$
|G(\sigma+i\tau)|\le G(\sigma)\qquad(\sigma>b,\ \tau\in\mathbb R).
\tag{485.4}
$$
在 $\sigma_\rho+i\gamma$，$-\frac12\zeta'/\zeta(s+1/2)$ 有留数 $-m/2$，其余项正则；在实点 $\sigma_\rho$，$G$ 正则。于是
$$
\lim_{\sigma\downarrow\sigma_\rho}(\sigma-\sigma_\rho)G(\sigma+i\gamma)=-\frac m2,\qquad
\lim_{\sigma\downarrow\sigma_\rho}(\sigma-\sigma_\rho)G(\sigma)=0,
$$
与 (485.4) 矛盾。故对任何有限 $\kappa$ 都不存在最终下界，即 $\liminf\mathcal T=-\infty$。

再设 RH 成立。取 $\alpha=1/2+\varepsilon$，$0<\varepsilon<1/5$，则 $b=0$，同上得 $c_g\le0$ 与 (485.4) 对 $\sigma>0$ 成立。取任一非平凡零点 $1/2+i\gamma$，重数 $m\ge1$，$\gamma\ne0$。$\mathcal F$ 在 $0$ 正则，故
$$
\lim_{\sigma\downarrow0}\sigma G(\sigma)=\kappa,\qquad
\lim_{\sigma\downarrow0}\sigma G(\sigma+i\gamma)=-\frac m2,
$$
由 (485.4) 得 $m/2\le\kappa$，从而 $\kappa\ge1/2$。合并两种情形得 (485.3)。证毕。

**定理 485.3（上侧对应）。** 若 RH 成立，则 $\limsup_{x\to\infty}\mathcal T(x)\ge1/2$；若 RH 不成立，则 $\limsup_{x\to\infty}\mathcal T(x)=+\infty$。

证明。设 $\mathcal T(x)\le K$ 对 $x\ge x_0$ 成立，令 $h(y)=K-\mathcal T(e^y)\ge0$，其变换为 $Kx_0^{-s}/s-\mathcal F(s)$。它在零点对应处的留数为 $+m/2$，在 $0$ 处（RH 情形）的主部为 $K/s$。将定理 485.2 证明中的 $g,G$ 换为 $h$ 及其变换，逐字重复，得 RH 下 $K\ge m/2\ge1/2$，非 RH 下矛盾。证毕。

**推论 485.4（推论 481.3 的加强）。** 对每个固定 $\kappa<1/2$ 与每个有限 $T$，存在实数 $x\ge T$ 使
$$
T_\psi(x,x^{4/5})<-\kappa x^{11/10}.
$$
证明。由 (481.1) 的归一化与定理 485.2 直接得出。证毕。

**范围与文献归属。** (485.1)、$\zeta$ 的实轴无零点、非平凡零点存在与 Landau–Widder 定理是经典输入；单个极点迫使 $m/2$ 的机制是标准的 Landau 型论证。本节的 `repo-derived` 内容是命题 485.1 对同一移动价格核的幂误差推广，以及定理 485.2–485.3 对全实中心函数 $\mathcal T$ 的无条件常数 $1/2$。单极点方法所能给出的普适常数即为 $1/2$；更强的结论需要聚合无穷多个零点的贡献。在 RH 下 $\liminf\mathcal T=-\infty$ 是否成立，以及有限双侧预算 $|\mathcal T|\le K$ 在 RH 下是否被排除，仍未决：它们需要该核的逐点零点和公式、带重数的零点计数、正 Fejér 核局部化、联立逼近与一致尾部估计。本节结论只关于全实中心函数，不推出 §481 所述被选整数来源上的下界，也不推出 RH 或每个 $n>5040$ 的严格 Robin 不等式。

## 追加锚（本行以下为增补区）

## 486. 原前向价格核的无条件双侧无界性

沿用 §481 与 §485 的记号。定理 485.2–485.3 在 RH 不成立时给出 $\liminf\mathcal T=-\infty$ 与 $\limsup\mathcal T=+\infty$，在 RH 下只给出 $\liminf\mathcal T\le-1/2\le1/2\le\limsup\mathcal T$。本节在 RH 下也得到两侧无界，于是两侧无界无条件成立。工具是正测度的 Laplace 变换在虚轴上的边界极限满足的有限 Gram 正性。下侧只用到零点有无穷多个；上侧还要用到零点计数的增长与 $0$ 附近的无零点间隙。

经典输入除 §485 所列各项外，还有 Riemann–von Mangoldt 公式
$$
N(T,2T)=\frac T{2\pi}\Bigl(\log\frac T{2\pi}+2\log2-1\Bigr)+O(\log T),
\tag{486.1}
$$
其中 $N(T_1,T_2)$ 是纵坐标落在 $(T_1,T_2]$ 中的非平凡零点个数（计重数）。下文只用它推出的 $N(T,2T)/T\to\infty$。

下面两个命题共用以下前提：$\mu$ 是 $\mathbb R$ 上的正 Borel 测度，对每个 $\sigma>0$ 有 $\int e^{-\sigma y}\,d\mu(y)<\infty$；记 $G(s)=\int e^{-sy}\,d\mu(y)$（$\Re s>0$），并在极限存在处记
$$
L(t)=\lim_{\sigma\downarrow0}\sigma\,G(\sigma+it).
$$

**命题 486.1（同号边界项的预算）。** 设 $c>0$，$t_1,\dots,t_n$ 两两不同且非零。设 $L$ 在点组 $\{0,t_1,\dots,t_n\}$ 的全部两两差处存在，在其中每个非零点有 $\Re L\le0$，并且对每个 $j$ 有 $\Re L(t_j)\le-c$。则
$$
n\,c^2\le4\,L(0)^2.
\tag{486.2}
$$

证明。(a) 设 $s_0,\dots,s_n$ 为实数，$L$ 在全部差 $s_j-s_k$ 处存在，$a_0,\dots,a_n\in\mathbb C$。对 $\sigma>0$，
$$
0\le\int\Bigl|\sum_ja_je^{-is_jy}\Bigr|^2\sigma e^{-\sigma y}\,d\mu(y)
=\sum_{j,k}a_j\overline{a_k}\,\sigma G\bigl(\sigma+i(s_j-s_k)\bigr).
$$
被积函数有界乘以可积函数，和是有限和。令 $\sigma\downarrow0$ 得
$$
\sum_{j,k}a_j\overline{a_k}\,L(s_j-s_k)\ \text{为非负实数}.
\tag{486.3}
$$
由 $\mu$ 为实测度，$G(\sigma-it)=\overline{G(\sigma+it)}$，故 $L(-t)=\overline{L(t)}$；又 $\sigma G(\sigma)\ge0$，故 $L(0)\ge0$。

(b) 在点组 $s_0=0$、$s_j=t_j$ 上取 $a_0=s\ge0$，$a_1=\dots=a_n=1$。(486.3) 的实部为
$$
s^2L(0)+s\sum_j\Re\bigl(L(t_j)+L(-t_j)\bigr)+nL(0)+\sum_{j\ne k}\Re L(t_j-t_k)\ge0 .
$$
各 $\Re L(-t_j)$ 与 $\Re L(t_j-t_k)$（$j\ne k$）都不大于零，故 $s^2L(0)-snc+nL(0)\ge0$ 对每个 $s\ge0$ 成立。若 $L(0)=0$，则 $-snc\ge0$ 对每个 $s>0$ 成立，故 $n=0$，(486.2) 成立；否则取 $s=nc/(2L(0))$ 得 (486.2)。证毕。

**命题 486.2（间隙内的二次预算）。** 设 $\delta>0$，$t_1,\dots,t_n$ 两两不同且落在一个长度小于 $\delta$ 的区间内。设 $L$ 在点组 $\{0,t_1,\dots,t_n\}$ 的全部两两差处存在，并且其中满足 $0<|t|<\delta$ 的点处 $L(t)=0$。则
$$
\sum_{j=1}^n|L(t_j)|^2\le L(0)^2.
\tag{486.4}
$$

证明。对 $j\ne k$ 有 $0<|t_j-t_k|<\delta$，故 $L(t_j-t_k)=0$。在点组 $0,t_1,\dots,t_n$ 上对命题 486.1 证明的 (a) 步取 $a_0=L(0)$，$a_j=-\overline{L(t_j)}$。由共轭关系，(486.3) 化为
$$
L(0)^3-2L(0)\sum_j|L(t_j)|^2+L(0)\sum_j|L(t_j)|^2\ge0 .
$$
若 $L(0)>0$ 即得 (486.4)；若 $L(0)=0$，改取 $a_0=s>0$ 与 $a_j=-\overline{L(t_j)}$，得 $-2s\sum_j|L(t_j)|^2\ge0$，(486.4) 仍成立。证毕。

**定理 486.3（RH 下的双侧无界性）。** 设 RH 与 (485.1) 成立。

1. 若 $\mathcal T(x)\ge-\kappa$ 对充分大的 $x$ 成立，则对非平凡零点的每个有限集 $Z$ 有 $|Z|\le16\kappa^2$。因此 $\liminf_{x\to\infty}\mathcal T(x)=-\infty$。
2. 再设 (486.1)。若 $\mathcal T(x)\le K$ 对充分大的 $x$ 成立，则存在 $\delta>0$，使每个长度小于 $\delta$ 的区间内零点重数之和不超过 $4K^2$。这与 (486.1) 矛盾，因此 $\limsup_{x\to\infty}\mathcal T(x)=+\infty$。

证明。(1) 取 $\mu$ 为 $(\mathcal T(x)+\kappa)\,dx/x$ 在 $(x_0,\infty)$ 上的测度经 $\log$ 的前推，它是正测度，且 $G(s)=\mathcal F(s)+\kappa x_0^{-s}/s$。如定理 485.2 证明的 RH 分支，取 $\alpha=1/2+\varepsilon$（$0<\varepsilon<1/5$）。命题 485.1 的余项在包含闭虚轴的半平面 $\Re s>\alpha-7/10$ 上全纯；由 Landau–Widder 定理，对每个 $\sigma>0$ 积分收敛，且 $G$ 在 $\Re s>0$ 上与延拓一致。逐点计算 $L$：$L(0)=\kappa$，因为 $\mathcal F$ 在 $0$ 正则；若 $1/2+it$ 是重数 $m$ 的零点，则 $L(t)=-m/2$；其余 $t\ne0$ 处 $\zeta(1/2+it)\ne0$，延拓在 $it$ 邻近全纯，故 $L(t)=0$。RH 下 $Z$ 中零点的纵坐标两两不同且非零（$\zeta(1/2)\ne0$）。以 $c=1/2$ 应用命题 486.1，得 $|Z|\le16\kappa^2$。非平凡零点有无穷多个，故不存在这样的 $\kappa$。

(2) 对 $K-\mathcal T$ 作同样构造，$G(s)=Kx_0^{-s}/s-\mathcal F(s)$。此时 $L(0)=K$，重数 $m$ 的零点处 $L(t)=+m/2$，其余 $t\ne0$ 处 $L(t)=0$。由 $\zeta(1/2)\ne0$ 与连续性，存在 $\delta>0$ 使 $\zeta(1/2+it)\ne0$ 对 $0<|t|<\delta$ 成立；于是 $L$ 在 $0<|t|<\delta$ 上为零。对长度小于 $\delta$ 的区间内的零点应用命题 486.2，得 $\sum m^2/4\le K^2$，从而 $\sum m\le\sum m^2\le4K^2$。用 $\lceil 2T/\delta\rceil$ 个长度不超过 $\delta/2$ 的区间覆盖 $(T,2T]$，得 $N(T,2T)\le4K^2(2T/\delta+1)$，与 (486.1) 给出的 $N(T,2T)/T\to\infty$ 矛盾。证毕。

**定理 486.4（无条件双侧无界性）。** 设 (485.1) 成立，则 $\liminf_{x\to\infty}\mathcal T(x)=-\infty$。再设 (486.1)，则 $\limsup_{x\to\infty}\mathcal T(x)=+\infty$。等价地，对每个实数 $\kappa$ 与每个有限 $X$，存在 $x\ge X$ 使 $T_\psi(x,x^{4/5})<-\kappa x^{11/10}$；在 (486.1) 下也存在 $x\ge X$ 使 $T_\psi(x,x^{4/5})>\kappa x^{11/10}$。

证明。RH 成立时由定理 486.3 得出；RH 不成立时由定理 485.2 与 485.3 得出，此时不需要 (486.1)。等价形式由 (481.1) 的归一化给出。证毕。

推论 485.4 中对每个 $\kappa<1/2$ 成立的结论，由此推广到每个实数 $\kappa$。

**注 486.5（两侧所需输入的差别）。** 下侧用到的只是边界极限的符号与零点的无穷性。上侧仅凭正定性与零点的无穷性不够。假如零点纵坐标恰为 $\{\pm nc:n\ge1\}$ 且都是单零点，则 $L=(K-\tfrac12)\mathbf 1_{\{0\}}+\tfrac12\mathbf 1_{c\mathbb Z}$ 在 $K\ge1/2$ 时是 $c\mathbb Z$ 上的正定函数，与有界上界相容。因此仅凭正定性与零点的无穷性推不出上侧；本节的证明用零点计数的超线性增长 (486.1) 补足。

**范围与文献归属。** 以下各项是经典输入：
- (485.1)、(486.1) 与 Landau–Widder 定理；
- $\zeta(1/2)\ne0$；
- 正核配合 Landau 正性来约束边界留数，属于 Ingham 振荡方法。

本节的 `repo-derived` 内容如下：
- 命题 486.1–486.2 的两个预算不等式，其中 (a) 步把有限和的 Gram 正性带到边界极限。
- 把上侧化归为短区间零点重数的有界性：用 $0$ 附近的无零点间隙消去交叉项。
- 定理 486.3–486.4 对全实中心函数 $\mathcal T$ 的双侧无界性。

本节结论只关于全实中心函数，不推出 §481 所述被选整数来源上的下界，也不推出 RH 或每个 $n>5040$ 的严格 Robin 不等式。

## 追加锚（本行以下为增补区）
