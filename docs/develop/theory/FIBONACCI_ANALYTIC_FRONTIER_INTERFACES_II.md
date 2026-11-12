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

## 487. RH 下原前向价格核的 $\log\log x$ 双侧振荡

沿用 §481 的 $E,H_x,\lambda,w,\rho_x$、(481.1) 的 $\mathcal T$ 与命题 481.1 的 $\mathcal F,R_{x_0}$。§486 证明了 $\mathcal T$ 双侧无界；本节在 RH 下给出显式速率。全节假设 RH，零点记为 $1/2\pm i\gamma$（$\gamma>0$），$m_\gamma$ 为重数，不同纵坐标只列一次，并令 $N(T)=\sum_{0<\gamma\le T}m_\gamma$。

取 $y_0=\log x_0$，令 $f(y)=\mathcal T(e^y)$（$y\ge y_0$），$f(y)=0$（$0\le y<y_0$）。则在 $\Re s>1/2$ 有 $\int_0^\infty f(y)e^{-sy}\,dy=\mathcal F(s)$，且由 von Koch 界，$f(y)=O(e^{y/5}y^2)$。

经典输入如下，均只作为假设使用：

$$
N(T)\sim\frac1{2\pi}T\log T,
\tag{487.1}
$$

以及 RH 下 $\xi(z)=\tfrac12z(z-1)\pi^{-z/2}\Gamma(z/2)\zeta(z)$ 的对称 Hadamard 展开

$$
\frac{\xi'}{\xi}\Bigl(\frac12+s\Bigr)=\sum_{\gamma>0}m_\gamma\Bigl(\frac1{s-i\gamma}+\frac1{s+i\gamma}\Bigr),
\tag{487.2}
$$

级数按 $\pm\gamma$ 配对，在避开极点的紧集上绝对一致收敛。

**命题 487.1（余项的多项式增长）。** 对每个 $0<\delta<1/5$，存在 $C_\delta$，使

$$
|R_{x_0}(\sigma+i\tau)|\le C_\delta(1+|\tau|)^2\qquad\Bigl(-\frac15+\delta\le\sigma\le1,\ \tau\in\mathbb R\Bigr).
\tag{487.3}
$$

证明。取 (481.4) 的伴随核 $q_s$ 与命题 481.1 证明中的换元 $t=x+zx^a$（$a=4/5$），写 $L(t,z)=\log(x(t,z)/t)$，并令

$$
A(t,z)=D^{-1}\int_z^1\frac{w(x+ux^a)}{w(x)}\,du,\qquad q_s(t)=\int_0^1x^{-s-1/2}A(t,z)\,dz .
$$

记 $h_w=(\log w)'$。由 $h_w=O(1/x)$、$h_w'=O(1/x^2)$ 与 $D=1+azx^{a-1}$，得 $L_t=\frac{(1-a)zx^a}{txD}$，并且 $\partial_t\frac{w(x+ux^a)}{w(x)}=\frac{w(x+ux^a)}{w(x)}D^{-1}\bigl[(1+aux^{a-1})h_w(x+ux^a)-h_w(x)\bigr]$，其中方括号为 $O(x^{a-2})$。由此 $L=O(t^{-1/5})$、$L_t=O(t^{-6/5})$、$A=(1-z)+O(t^{-1/5})$、$A_t=O(t^{-6/5})$，且这些界关于 $z\in[0,1]$ 一致。令 $p_s=e^{-(s+1/2)L}$。当 $-1/5\le\Re s\le1$ 时 $L$ 为实数，故 $|p_s|\ll1$，$|p_s-1|\ll(1+|s|)t^{-1/5}$，$|\partial_tp_s|\ll(1+|s|)t^{-6/5}$。于是

$$
q_s(t)=\tfrac12t^{-s-1/2}+r_s(t),\qquad
|r_s(t)|\ll(1+|s|)t^{-\sigma-7/10},\qquad
|r_s'(t)|\ll(1+|s|)^2t^{-\sigma-17/10}.
$$

主项 $\tfrac12t^{-s-1/2}$ 给出 (481.3) 的 $\zeta'/\zeta$ 项与 $-1/(2(s-1/2))$，余项 $R_{x_0}$ 由 $r_s$ 生成。固定充分大的 $T_*$（位于 §481 证明中初始修正区间之外），把有限区间部分合并为整函数 $H_0$，分部积分得

$$
R_{x_0}(s)=H_0(s)-E(T_*)r_s(T_*)-\int_{T_*}^\infty E(t)r_s'(t)\,dt .
$$

$H_0$ 在固定实部条带上关于 $\tau$ 有界，端点项为 $O(1+|\tau|)$。由 $|E(t)|\ll t^{1/2}\log^2t$，当 $\sigma\ge-1/5+\delta$ 时积分项至多为 $(1+|\tau|)^2\int_{T_*}^\infty t^{-1-\delta}\log^2t\,dt\ll_\delta(1+|\tau|)^2$。证毕。

**引理 487.2（定量边界公式）。** 采用 $\widehat g(t)=\int_{\mathbb R}g(v)e^{-itv}\,dv$。对 $b>0$ 令 $K_b(v)=\dfrac{1-\cos bv}{\pi bv^2}$（$K_b(0)=b/(2\pi)$），对 $U>2b$ 令 $H_{b,U}(v)=K_b(v)(1-\cos Uv)$。二者非负、积分为 $1$，$H_{b,U}\le2K_b$，且（Fejér 核的 Fourier 对；乘以 $\cos Uv$ 对应频移）

$$
\widehat K_b(t)=\phi_b(t):=\Bigl(1-\frac{|t|}b\Bigr)_+,\qquad
\widehat H_{b,U}(t)=\phi_b(t)-\tfrac12\phi_b(t-U)-\tfrac12\phi_b(t+U).
\tag{487.4}
$$

设 $\kappa,C\ge0$，且 $f(u)\le\kappa\log(e+u)+C$ 对所有 $u\ge0$ 成立，或 $f(u)\ge-\kappa\log(e+u)-C$ 对所有 $u\ge0$ 成立。设 $g=K_b$ 或 $g=H_{b,U}$，$\operatorname{supp}\widehat g\subset[-M,M]$，$M\ge1$。则对 $y\ge1$，$\int_0^\infty f(u)g(y-u)\,du$ 绝对收敛，且

$$
\int_0^\infty f(u)g(y-u)\,du=-\sum_{0<\gamma\le2M}m_\gamma\widehat g(\gamma)\cos(\gamma y)
+O\Bigl(\frac{(1+b)M^2}y+\frac{N(2M)}{by}\Bigr),
\tag{487.5}
$$

其中隐含常数与 $b,U,M,y$ 无关。

证明。由 (481.3) 与 (487.2)，并用 $-\zeta'/\zeta(z)=-\xi'/\xi(z)+1/z+1/(z-1)-\tfrac12\log\pi+\tfrac12\Gamma'/\Gamma(z/2)$，

$$
\mathcal F(s)=-\frac12\sum_{\gamma>0}m_\gamma\Bigl(\frac1{s-i\gamma}+\frac1{s+i\gamma}\Bigr)+J(s),\qquad
J(s)=R_{x_0}(s)+\frac1{2(s+1/2)}-\frac14\log\pi+\frac14\frac{\Gamma'}{\Gamma}\Bigl(\frac{s+1/2}2\Bigr).
$$

$s=1/2$ 处的两项主部互相抵消，$J$ 在 $\Re s>-1/5$ 全纯。令 $G_M(s)=\mathcal F(s)+\tfrac12\sum_{0<\gamma\le2M}m_\gamma\bigl(\frac1{s-i\gamma}+\frac1{s+i\gamma}\bigr)$。由 (487.1) 分部求和得 $\sum_{\gamma>2M}m_\gamma\gamma^{-2}\ll\log(2+M)/M$，配对项为 $2s/(s^2+\gamma^2)=O(|s|/\gamma^2)$，故在 $|\Im s|\le M+1/4$、$|\Re s|\le1/10$ 上，未减去部分为 $O(\log(2+M))$。结合命题 487.1、Cauchy 导数估计与 $\Gamma'/\Gamma$ 的条带估计，

$$
\sup_{|t|\le M}\bigl(|G_M(it)|+|G_M'(it)|\bigr)\ll M^2 .
\tag{487.6}
$$

令 $a(u)=\kappa\log(e+u)+C$，$h=a\mp f\ge0$（符号按所设单侧界选取）。$h$ 的 Laplace 变换为 $a$ 的变换与 $\mp\mathcal F$ 之和；RH 下前者与后者沿正实轴均全纯（$s=1/2$ 处已相消），故由 Landau 关于非负函数 Laplace 变换的定理，$\int_0^\infty h(u)e^{-\sigma u}\,du<\infty$ 对每个 $\sigma>0$ 成立；由 $|f|\le h+a$，$f$ 的 Laplace 积分也对每个 $\sigma>0$ 绝对收敛。

令 $p_M(u)=-\sum_{0<\gamma\le2M}m_\gamma\cos\gamma u$，其 Laplace 变换恰为 $G_M-\mathcal F$ 的相反数。对 $\sigma>0$ 由绝对 Fubini，

$$
\int_0^\infty\bigl(f(u)-p_M(u)\bigr)e^{-\sigma u}g(y-u)\,du=\frac1{2\pi}\int_{\mathbb R}\widehat g(t)G_M(\sigma+it)e^{ity}\,dt .
$$

右边被积函数在 $[-M,M]$ 上关于 $\sigma\in[0,1/10]$ 一致有界，故 $\sigma\downarrow0$ 时收敛。$p_M$ 有界，由控制收敛取极限；对 $h(u)e^{-\sigma u}g(y-u)\ge0$ 用单调收敛，得 $h*g<\infty$，进而 $f*g$ 绝对收敛且上式在 $\sigma=0$ 成立。$p_M*g$ 在全实轴上等于 $-\sum m_\gamma\widehat g(\gamma)\cos\gamma y$；改为 $[0,\infty)$ 的误差至多 $N(2M)\int_y^\infty g\ll N(2M)/(by)$，因为两类核均满足 $g(v)\ll1/(bv^2)$。最后，$\widehat g$ 连续、分段线性、支撑在 $[-M,M]$，$\|\widehat g\|_1\ll b$，$\|\widehat g'\|_1\ll1$，对正则部分分部积分一次并用 (487.6)，得 $O((1+b)M^2/y)$。证毕。

**定理 487.3（RH 下的 $\log\log x$ 双侧振荡）。** 设 RH、(487.1) 与 (487.2)。则存在常数 $c>0$，使

$$
\liminf_{x\to\infty}\frac{\mathcal T(x)}{\log\log x}\le-c,\qquad
\limsup_{x\to\infty}\frac{\mathcal T(x)}{\log\log x}\ge c .
\tag{487.7}
$$

等价地，存在 $c>0$，使 $T_\psi(x,x^{4/5})\le-cx^{11/10}\log\log x$ 与 $T_\psi(x,x^{4/5})\ge cx^{11/10}\log\log x$ 各对任意大的 $x$ 成立。

证明。在 $y=\log x$ 上证明 $f(y)=\Omega_\pm(\log y)$。固定 $Q=8$，$c_Q=\cos(\pi/4)>0$，并取 $L=M^5$。证明用到两个经典事实。其一（Dirichlet 同时逼近，抽屉原理）：给定实数 $\lambda_1,\dots,\lambda_d$ 与 $L\ge1$，存在 $y\in[L,LQ^d]$ 使 $\cos(\lambda_jy)\ge c_Q$ 对所有 $j$ 成立。其二：由 $\log(e+u)\le\log(e+y)+\log(1+|u-y|)$、$K_M(v)=MK_1(Mv)$、$\int K_1(v)\log(1+|v|)\,dv<\infty$ 与 $H_{b,U}\le2K_b$，存在 $C_0$ 使 $\int_0^\infty g(y-u)\log(e+u)\,du\le\log(e+y)+C_0$ 对 $g=K_M$（$M\ge1$）与 $g=H_{b,U}$（$b$ 固定）一致成立。

负侧。设 $W_-(M)=\sum_{0<\gamma<M}m_\gamma(1-\gamma/M)$。由 (487.1)，$W_-(M)=\frac1M\int_0^MN(t)\,dt\sim\frac1{4\pi}M\log M$，$N(M)\sim2W_-(M)$。对 $0<\gamma<M$ 的不同纵坐标（个数 $d\le N(M)$）应用 Dirichlet 同时逼近，得 $y\in[M^5,M^5Q^{N(M)}]$ 使 $\cos\gamma y\ge c_Q$，从而 $\log(e+y)\le C_1W_-(M)$。反设 $f(u)\ge-\kappa\log(e+u)$ 对充分大的 $u$ 成立；由局部有界性加一个常数后对所有 $u\ge0$ 成立。取 $g=K_M$（$\widehat g=\phi_M$），由 (487.5)，

$$
\int_0^\infty f(u)K_M(y-u)\,du\le-c_QW_-(M)+o(1),
$$

而对数包络的平均给出该积分 $\ge-\kappa(C_1W_-(M)+C_0)-O(1)$。取 $\kappa<c_Q/(2C_1)$ 并令 $M\to\infty$，矛盾。

正侧。先选频带。由 $\zeta(1/2)\ne0$ 与连续性，取 $b>0$ 使 $(0,b]$ 中没有零点纵坐标。令 $n(U)=\sum_{|\gamma-U|<b}m_\gamma$，$W_+(U)=\sum_\gamma m_\gamma(1-|\gamma-U|/b)_+$。由 (487.1) 与有限和积分交换，$\int_T^{2T}n\sim\frac{2b}{2\pi}T\log T$，$A_T:=\int_T^{2T}W_+\sim\frac b{2\pi}T\log T$，端点修正以 $T$ 与 $2T$ 附近定宽邻域的零点质量为界，为 $o(T\log T)$。故充分大时 $\int_T^{2T}n\le3A_T$。在 $\{n>12W_+\}$ 上 $\int W_+\le\frac1{12}\int n\le A_T/4$；在 $\{W_+<A_T/(4T)\}$ 上 $\int W_+\le A_T/4$；两集合之外承载至少 $A_T/2$ 的质量。于是对充分大的 $T$ 存在 $U\in[T,2T]$ 使

$$
n(U)\le12W_+(U),\qquad W_+(U)\ge c_b\log T,
\tag{487.8}
$$

其中 $c_b>0$ 只依赖 $b$。对这样的 $U$ 令 $M=U+b$。由 (487.4)，中央频带 $(0,b]$ 无零点，$\widehat H_{b,U}(\gamma)=-\tfrac12\phi_b(\gamma-U)$ 对 $\gamma>2b$ 成立，故 (487.5) 的主和为 $\tfrac12\sum_{|\gamma-U|<b}m_\gamma\phi_b(\gamma-U)\cos\gamma y$。只对 $|\gamma-U|<b$ 的不同纵坐标同步，得 $y\in[M^5,M^5Q^{n(U)}]$，由 (487.8)，$\log(e+y)\le5\log M+n(U)\log Q+O(1)\le C_2W_+(U)$。反设 $f(u)\le\kappa\log(e+u)$ 最终成立，则

$$
\tfrac12c_QW_+(U)+o(1)\le\int_0^\infty f(u)H_{b,U}(y-u)\,du\le\kappa(C_2W_+(U)+C_0)+O(1),
$$

取 $\kappa<c_Q/(4C_2)$，令 $T\to\infty$，矛盾。

两侧所得 $y$ 均可任意大，且两处误差项因 $y\ge M^5$ 而为 $o(1)$。由 $y=\log x$ 得 (487.7)。证毕。

**注 487.4（与 $\psi(x)-x$ 的比较与未决部分）。** $\psi(x)-x$ 的显式公式带权重 $1/\rho$，同一方法只给出 Littlewood 的 $\sqrt x\log\log\log x$；$\mathcal F$ 在 $i\gamma$ 处的留数恒为 $-m_\gamma/2$，不随 $\gamma$ 衰减，零点质量 $N(M)\asymp M\log M$ 直接成为振幅，故得到 $\log\log x$。定理 487.3 只给出 $\log\log x$ 的下界，不主张其为真实阶，也不给出匹配的上界。§486 的正性论证需要整个尾部为正测度：$[X,Y]$ 上的有限窗口正性只产生紧支撑测度，其 Laplace 变换为整函数，看不到边界留数；因此显式的 $Y(X,\kappa)$ 需要额外的有效尾部输入，本节不处理。

**范围与文献归属。** 经典输入：
- RH、(487.1)、(487.2)、von Koch 界；
- Landau 关于非负函数 Laplace 变换的定理；
- Fejér 核的 Fourier 对；
- Dirichlet 同时逼近。

带边界极点的正性振荡方法属于 Ingham [Two conjectures in the theory of numbers, Amer. J. Math. 64 (1942)] 的框架。Diamond–Pintz [Oscillation of Mertens' product formula, J. Théor. Nombres Bordeaux 21 (2009)] 的 Lemma 5.1 在单侧对数包络下给出固定截断的同类论证。Kaczorowski–Wiertelak [Ω-estimates for a class of arithmetic error terms, Math. Proc. Cambridge Philos. Soc. 142 (2007)] 给出上半平面调和函数边界值型误差项的一般 Ω 方法；本节不主张该定理对本核的任何应用。Goldston–Yıldırım [Higher correlations of divisor sums related to primes II: variations of the error term in the prime number theorem, Proc. London Math. Soc. 95 (2007)] 的定理 3 在 Dirichlet $L$ 函数的 GRH 下，对 $(\log N)^{14}\ll h\ll N^{1/7-\varepsilon}$ 给出 $\psi(n+h)-\psi(n)-h=\Omega_\pm(\sqrt{h\log N})$；de la Bretèche–Fiorilli [Math. Ann. 381 (2021)] 给出平滑短区间计数的矩下界。二者的对象、区间长度范围或所得符号与本核不同。

本节的 `repo-derived` 内容：
- 命题 487.1 对原核余项的显式多项式增长；
- 引理 487.2 对本核的定量边界公式（截断随 $M$ 增长、误差显式）；
- 定理 487.3 对全实中心函数 $\mathcal T$ 的双侧 $\log\log x$ 振荡。

本节结论只关于全实中心函数，不推出 §481 所述被选整数来源上的下界，也不推出 RH 或每个 $n>5040$ 的严格 Robin 不等式。

## 追加锚（本行以下为增补区）

## 488. RH 下原前向价格核的幂次均方下界

沿用 §481 的 $E,H_x,w,\rho_x$、(481.1) 的 $\mathcal T$，以及 §487 的记号：全节假设 RH，零点记为 $1/2\pm i\gamma$（$\gamma>0$），$m_\gamma$ 为重数，不同纵坐标只列一次；$N(T)=\sum_{0<\gamma\le T}m_\gamma$。令 $f(y)=\mathcal T(e^y)$（$y>\log3$），$f(y)=0$（$y\le\log3$）。§487 给出 $\mathcal T=\Omega_\pm(\log\log x)$；本节给出 $|\mathcal T|$ 的一个幂次下界。

经典输入如下，均只作为假设使用：von Koch 界 $E(x)=O(\sqrt x\log^2x)$；配对 Hadamard 展开 (487.2)；Riemann–von Mangoldt 公式给出的局部零点计数

$$
N(T+1)-N(T)\ll\log(2+T);
\tag{488.1}
$$

以及 Montgomery 函数

$$
F(\alpha,T)=\frac{2\pi}{T\log T}\sum_{0<\gamma,\gamma'\le T}m_\gamma m_{\gamma'}T^{i\alpha(\gamma-\gamma')}\frac4{4+(\gamma-\gamma')^2}
$$

的平均下界

$$
\liminf_{T\to\infty}\int_{17}^{19}F(\alpha,T)\,d\alpha\ge\frac23 .
\tag{488.2}
$$

(488.2) 是 Carneiro–Chandee–Chirre–Milinovich [On Montgomery's pair correlation conjecture: a tale of three integrals, J. Reine Angew. Math. (2022)] Theorem 9 在 $b=17$、$\ell=2$ 时的结论，只假设 RH；该文指出 $\ell\le2$ 的下界情形源自 Goldston–Gonek [A note on the number of primes in short intervals, Proc. Amer. Math. Soc. 108 (1990)]。

**引理 488.1（高斯边界公式）。** 令 $q_M(v)=\dfrac{M}{\sqrt{2\pi}}e^{-M^2v^2/2}$，$A_M(y)=\int_0^\infty f(u)q_M(y-u)\,du$，$G_M(y)=\sum_{\gamma>0}m_\gamma e^{-\gamma^2/(2M^2)}\cos(\gamma y)$。则对 $M,y\ge1$，

$$
A_M(y)=-G_M(y)+O\bigl(M^3e^{-y/6}\bigr),
\tag{488.3}
$$

隐含常数与 $M,y$ 无关。

证明。由 von Koch 界、$0<\rho_x(u)\le1$ 与 $H_x\le x$，$|f(y)|\ll e^{y/5}(1+y)^2$。由命题 481.1、(487.2) 与 $\xi'/\xi$ 和 $\zeta'/\zeta$ 的关系，在 $\Re s>1/2$ 上

$$
\mathcal F(s):=\int_0^\infty f(y)e^{-sy}\,dy=-\sum_{\gamma>0}m_\gamma\frac{s}{s^2+\gamma^2}+J(s),
$$

其中 $J(s)=R(s)+\frac1{2(s+1/2)}-\frac14\log\pi+\frac14\frac{\Gamma'}{\Gamma}\bigl(\frac{s+1/2}2\bigr)$ 在 $\Re s>-1/5$ 全纯；由命题 487.1（取 $\delta=1/30$）与 digamma 的条带估计（其自变量实部至少 $1/6$），$|J(\sigma+it)|\ll(1+|t|)^2$ 于 $-1/6\le\sigma\le3/4$。取 $c=3/4$，高斯反演 $q_M(v)=\frac1{2\pi i}\int_{(c)}e^{sv+s^2/(2M^2)}\,ds$ 与绝对 Fubini 给出 $A_M(y)=\frac1{2\pi i}\int_{(c)}\mathcal F(s)e^{sy+s^2/(2M^2)}\,ds$。$J$ 的部分移到 $\Re s=-1/6$：被积函数全纯，水平边上高斯衰减压过多项式增长，所得积分至多 $Ce^{-y/6}\int(1+|t|)^2e^{-t^2/(2M^2)}dt\ll M^3e^{-y/6}$。配对极点部分逐项反演：令 $S_2=\sum_{\gamma>0}m_\gamma\gamma^{-2}$，由 (488.1) 它有限。在 $s=c+it$ 上按 $\gamma=2|s|$ 分开：低频配对项以 $2/c$ 为界，个数受 $N(2|s|)\le4|s|^2S_2$ 控制；高频部分为 $O(|s|S_2)$。故每个有限配对部分和受 $C(1+|t|)^2$ 控制，乘以高斯因子后可积，由控制收敛可逐项交换。单项给出 $\int_0^\infty\cos(\gamma u)q_M(y-u)\,du=e^{-\gamma^2/(2M^2)}\cos(\gamma y)-B_\gamma(y)$，其中半直线修正 $B_\gamma(y)=\int_0^\infty\cos(\gamma v)q_M(y+v)\,dv$；两次分部积分并用 $q_M''(w)\ge0$（$w\ge y\ge1$，$M\ge1$）得 $|B_\gamma(y)|\le2M^2yq_M(y)/\gamma^2$，故 $\sum_\gamma m_\gamma|B_\gamma(y)|\ll M^3e^{-y/6}$。合并即得 (488.3)。证毕。

**引理 488.2（零点和的窗口均方）。** 令 $L=\log M$，$C_M(y)=\sum_{0<\gamma\le M}m_\gamma\cos(\gamma y)$，$J=[16L,20L]$。则对充分大的 $M$，

$$
\int_J C_M(y)^2\,dy\gg ML^2 .
\tag{488.4}
$$

证明。令 $S_M(y)=\sum_{0<\gamma\le M}m_\gamma e^{i\gamma y}$，$h(v)=e^{-2|v|}$，则 $\int h=1$，$\int h(v)e^{itv}dv=4/(4+t^2)$。展开有限和得

$$
(h*|S_M|^2)(y)=\frac{ML}{2\pi}F\Bigl(\frac yL,M\Bigr),
$$

故由 (488.2)，$\int_{17L}^{19L}(h*|S_M|^2)\,dy=\frac{ML^2}{2\pi}\int_{17}^{19}F(\alpha,M)\,d\alpha\gg ML^2$。由 $C_M^2=\frac12|S_M|^2+\frac12\Re(S_M^2)$，交叉项 $h*\Re(S_M^2)$ 的绝对值至多 $\sum_{\gamma,\gamma'\le M}m_\gamma m_{\gamma'}\frac4{4+(\gamma+\gamma')^2}$；按 $\max(\gamma,\gamma')$ 的二进尺度 $2^j$ 分组，每组贡献 $O(2^{-2j}N(2^{j+1})^2)=O((j+1)^2)$，总和为 $O(L^3)$，在长为 $2L$ 的区间上积分损失 $O(L^4)$。于是 $\int_{17L}^{19L}(h*C_M^2)\,dy\gg ML^2$。对 $y\in[17L,19L]$ 与 $z\notin J$，$|y-z|\ge L$，且 $\|C_M\|_\infty\le N(M)\ll ML$，故 $z\notin J$ 的贡献总计 $O(N(M)^2\cdot L\cdot e^{-2L})=O(L^3)$；$z\in J$ 的贡献至多 $\int_JC_M^2$（$h$ 的质量为 $1$）。由此得 (488.4)。证毕。

**定理 488.3（宽窗口幂次均方下界）。** 设 RH、von Koch 界、(487.2)、(488.1) 与 (488.2)。则存在 $c>0$ 与 $M_0$，使对 $M\ge M_0$

$$
\int_{e^{-2}M^{16}}^{e^2M^{20}}\mathcal T(x)^2\,\frac{dx}x\ge cM(\log M)^2 .
\tag{488.5}
$$

因而存在 $c_1>0$，使 $|\mathcal T(x)|\ge c_1x^{1/40}\sqrt{\log x}$ 对任意大的 $x$ 成立；等价地，$|T_\psi(x,x^{4/5})|\ge c_1x^{9/8}\sqrt{\log x}$ 对任意大的 $x$ 成立。

证明。**第一步：从硬截断到高斯权。** 取 $\Delta=M^{1/4}$ 与偶的光滑截断 $\chi_M$：$0\le\chi_M\le1$，$|t|\le M$ 时 $\chi_M=1$，$|t|\ge M+\Delta$ 时 $\chi_M=0$，过渡带上 $|\chi_M^{(r)}|\ll_r\Delta^{-r}$。令 $b_M(t)=e^{t^2/(2M^2)}\chi_M(t)$，$k_M(v)=\frac1{2\pi}\int b_M(t)e^{itv}\,dt$。则 $\|b_M\|_\infty\le e^2$；由 Leibniz 公式，$\|b_M^{(5)}\|_1\ll\Delta^{-4}+M^{-4}\ll M^{-1}$，五次分部积分给出 $\int_{|v|\ge1}|k_M|\ll M^{-1}$。又 $k_M*G_M=\sum_\gamma m_\gamma\chi_M(\gamma)\cos(\gamma y)$，它与 $C_M$ 只在过渡带不同；由 (488.1)，$N(M+\Delta)-N(M)\ll\Delta L$，故 $\|k_M*G_M-C_M\|_\infty\ll M^{1/4}L$。令 $J^+=[16L-1,20L+1]$，$g_M=G_M\mathbf 1_{J^+}$。由 $\|G_M\|_\infty\ll ML$ 与 $k_M$ 的尾部界，在 $J$ 上 $|k_M*g_M-k_M*G_M|\ll L$。结合 (488.4)，

$$
\|k_M*g_M\|_{L^2(J)}\ge c\sqrt ML-O(M^{1/4}L^{3/2})-O(L^{3/2})\gg\sqrt ML .
$$

由 Plancherel，$\|k_M*g_M\|_2\le\|b_M\|_\infty\|g_M\|_2\le e^2\|g_M\|_2$，故 $\|G_M\|_{L^2(J^+)}\gg\sqrt ML$。

**第二步：回到 $f$。** 在 $J^+$ 上 (488.3) 的误差为 $O(M^3e^{-(16L-1)/6})=O(M^{1/3})$，其 $L^2(J^+)$ 范数为 $o(\sqrt ML)$，故 $\|A_M\|_{L^2(J^+)}\gg\sqrt ML$。令 $J^{++}=[16L-2,20L+2]$，$f_M=f\mathbf 1_{J^{++}}$。对 $y\in J^+$，$u\notin J^{++}$ 时 $|u-y|\ge1$，由 $|f(u)|\ll e^{u/5}(1+u)^2$ 与高斯衰减，$|A_M(y)-(q_M*f_M)(y)|\ll M^4L^2e^{-M^2/8}$，在所需尺度上可忽略。由 $q_M\ge0$、$\|q_M\|_1=1$ 与 Young 不等式，$\|q_M*f_M\|_2\le\|f_M\|_2$。于是 $\int_{J^{++}}f^2\gg ML^2$，换元 $x=e^y$ 即得 (488.5)。

**第三步：取点。** $J^{++}$ 的长度为 $4L+4$，故存在 $u\in J^{++}$ 使 $f(u)^2\gg ML^2/(4L+4)\gg ML$。令 $x=e^u$，则 $e^{-2}M^{16}\le x\le e^2M^{20}$，$x^{1/40}\sqrt{\log x}\le e^{1/20}M^{1/2}\sqrt{20L+2}\ll\sqrt{ML}\ll|\mathcal T(x)|$；$M\to\infty$ 时这些 $x$ 任意大。最后由 $T_\psi(x,x^{4/5})=x^{11/10}\mathcal T(x)$ 与 $\frac{11}{10}+\frac1{40}=\frac98$ 得最后一式。证毕。

**命题 488.4（二倍区间均方上界）。** 设 RH，并设短区间均方估计 $\int_X^{2X}|E((1+\theta)x)-E(x)|^2dx\ll\theta X^2\log^2(2/\theta)$（$0<\theta\le1$；Saffari–Vaughan，见 Chan [More precise pair correlation of zeros and primes in short intervals, J. London Math. Soc. 68 (2003)] 式 (2)）。则

$$
\int_X^{2X}\mathcal T(x)^2\,\frac{dx}x\ll X^{1/5}(\log X)^2 .
\tag{488.6}
$$

证明。令 $D(x,\theta)=E((1+\theta)x)-E(x)$。换元 $u=\theta x$ 并由 $0<\rho_x(u)\le1$ 与 Cauchy–Schwarz，

$$
\frac{\mathcal T(x)^2}x\le\frac x{H_x^3}\int_0^{x^{-1/5}}D(x,\theta)^2\,d\theta .
$$

在 $[X,2X]$ 上积分，交换次序并代入 Selberg 型估计，右边至多 $\ll X^{-7/5}\int_0^{X^{-1/5}}\theta X^2\log^2(2/\theta)\,d\theta\ll X^{1/5}(\log X)^2$。证毕。

**范围说明。** 定理 488.3 把 §487 的 $\log\log x$ 提升为 $|\mathcal T|$ 的幂次下界 $x^{1/40}\sqrt{\log x}$；命题 488.4 说明在二倍区间上 $\mathcal T$ 的均方至多 $X^{1/5}(\log X)^2$，即二次平均意义下的量级不超过 $x^{1/10}\log x$。以下仍未决：二倍区间上的下界 $\int_X^{2X}\mathcal T^2dx/x\gg X^{1/5}\log X$（Chan 前引文讨论的是普通短区间方差渐近与强对相关的等价，不直接涉及本核的加权下界）；带符号的幂次 $\Omega_\pm$——均方只控制 $|\mathcal T|$，而 §487 的 Dirichlet 同步只保证 $\log y$ 量级；以及 §481 所述被选整数来源上的下界。

**范围与文献归属。** 经典输入：RH、von Koch 界、(487.2)、(488.1)、(488.2)、Saffari–Vaughan 短区间均方上界；高斯反演、Plancherel 与 Young 不等式。(488.2) 及其 $\ell\le2$ 情形的来源见上文；de la Bretèche–Fiorilli [Math. Ann. 381 (2021)] 的平滑短区间矩下界要求偶的内层平滑与非负 Fourier 变换，不能直接用于本核的单侧、随 $x$ 变化的权。本节的 `repo-derived` 内容：引理 488.1 对本核的高斯边界公式（含半直线修正与余项移线）；引理 488.2 由 (488.2) 推出的零点余弦和窗口均方下界；定理 488.3 把该下界运输到 $\mathcal T$ 的幂次均方下界与 $\Omega(x^{1/40}\sqrt{\log x})$；命题 488.4 对本核的二倍区间均方上界。本节结论只关于全实中心函数，不推出 §481 所述被选整数来源上的下界，也不推出 RH 或每个 $n>5040$ 的严格 Robin 不等式。

## 追加锚（本行以下为增补区）

## 489. 原前向价格核的二倍区间均方渐近

沿用 §481 的 $E,H_x,w,\rho_x$ 与 (481.1) 的 $\mathcal T$，其中 $H_x=x^{4/5}$。记

$$
D_u(x)=E(x+u)-E(x),\qquad B_h(x)=\int_0^hD_u(x)\,du,\qquad P_h(x)=\frac{B_h(x)}{h^2},\qquad V(Y,h)=\int_1^YD_h(x)^2\,dx .
$$

本节只使用以下三项作为假设。von Koch 界：$E(x)\ll\sqrt x\log^2x$。命题 488.4 的短区间均方上界：存在 $C,X_0$，使对 $X\ge X_0$、$0<\theta\le1$，

$$
\int_X^{2X}\bigl(E((1+\theta)x)-E(x)\bigr)^2\,dx\le C\theta X^2\log^2(2/\theta).
\tag{489.1}
$$

以及在 $h\asymp Y^{4/5}$ 附近一致的普通短区间方差渐近：

$$
\sup_{Y^{3/4}\le h\le Y^{7/8}}\left|\frac{V(Y,h)}{Yh\log(Y/h)}-1\right|\longrightarrow0\qquad(Y\to\infty).
\tag{489.2}
$$

在 RH 下，(489.2) 由 Montgomery 强对相关猜想推出：Goldston–Montgomery [Pair correlation of zeros and primes in short intervals, Progr. Math. 70 (1987)] 证明了普通方差渐近与强对相关的等价；见 Goldston [Notes on pair correlation of zeros and prime numbers, arXiv:math/0412313] §9 定理 7 与式 (9.3)，那里的渐近对相对长度 $h/Y\in[Y^{-B_2},Y^{-B_1}]$（$0<B_1\le B_2<1$ 固定）一致成立，取 $B_1=1/8$、$B_2=1/4$ 即给出 (489.2)。指数 $3/4$、$7/8$ 可换为任意 $4/5\mp\eta$（$0<\eta<1/5$）。(489.2) 是本节额外采用的一致方差渐近假设；(488.2) 在 RH 下已知，它是固定 $\alpha$ 区间 $[17,19]$ 上的平均下界，而二倍 $x$ 区间对应的 $\alpha$ 区间长度为 $\log2/\log T$，故 (488.2) 不能替代这里所需的局部渐近信息。

**引理 489.1（去掉价格权）。** 令 $\mathcal T_0(x)=\sqrt x\,P_{H_x}(x)$。则 $\mathcal T(x)-\mathcal T_0(x)=O(\log^2x)$。

证明。对 $x\ge3$，$(\log w)'(x)=-\frac2x+\frac1{x(1+\log x)}-\frac2{x\log x}$，其中 $0<-x(\log w)'(x)=2+\frac2{\log x}-\frac1{1+\log x}<4$。令 $A_x(u)=-\int_x^{x+u}(\log w)'(v)\,dv$，则 $\rho_x(u)=e^{-A_x(u)}$ 且 $0\le A_x(u)\le4\log(1+u/x)\le4u/x$，故 $0\le1-\rho_x(u)\le A_x(u)\le4u/x$（$0\le u\le H_x$）。由 von Koch 界，$|D_u(x)|\ll\sqrt x\log^2x$。于是 $|\mathcal T-\mathcal T_0|\ll\frac{\sqrt x}{H_x^2}\int_0^{H_x}\sqrt x\log^2x\cdot\frac{4u}x\,du\ll\log^2x$。证毕。

由此 $\|\mathcal T-\mathcal T_0\|_{L^2([X,2X],dx/x)}=O(\log^2X)$，且 $\int_X^{2X}\mathcal T_0^2\,dx/x=\int_X^{2X}P_{H_x}(x)^2\,dx$。

以下引理 489.2–489.3 是经典方差转移方法（由普通方差经极化得协方差，再作三角平均）在本节长度尺度上的实现。

**引理 489.2（固定长度的协方差）。** 固定 $1\le a<b\le2$、$c>0$，令 $h=cX^{4/5}$、$\ell_X=\log(X/h)$。对固定 $s,t\in[0,1]$，

$$
\frac1{Xh\ell_X}\int_{aX}^{bX}D_{sh}(x)D_{th}(x)\,dx\longrightarrow(b-a)\min(s,t).
$$

证明。对固定的正倍数 $q$ 与 $k=qh$，所需端点均为 $Y=dX+O(h)$（$d\in[1,2]$），故 $k/Y^{3/4}\asymp X^{1/20}\to\infty$、$k/Y^{7/8}\asymp X^{-3/40}\to0$，$k$ 最终落在 (489.2) 的范围内，且每个端点处的误差 $o(Yk\log(Y/k))$ 都是 $o(Xh\ell_X)$。对固定 $s>0$，$\int_{aX}^{bX}D_{sh}^2=V(bX,sh)-V(aX,sh)=(b-a)Xsh\ell_X+o(Xh\ell_X)$，因为固定倍数的 $X^{4/5}$ 最终落在 (489.2) 的范围内，且 $\log(aX/(sh))=\ell_X+O(1)$。设 $s>t>0$。由恒等式 $D_{sh}(x)-D_{th}(x)=D_{(s-t)h}(x+th)$，$\int_{aX}^{bX}(D_{sh}-D_{th})^2=V(bX+th,(s-t)h)-V(aX+th,(s-t)h)=(b-a)X(s-t)h\ell_X+o(Xh\ell_X)$。极化恒等式 $2D_{sh}D_{th}=D_{sh}^2+D_{th}^2-(D_{sh}-D_{th})^2$ 给出极限 $\frac{b-a}2(s+t-|s-t|)=(b-a)\min(s,t)$。$s=t$ 或 $st=0$ 的情形直接成立。证毕。

**引理 489.3（固定长度的三角平均）。** 在引理 489.2 的记号下，

$$
\int_{aX}^{bX}P_h(x)^2\,dx\sim\frac{(b-a)X}{3h}\log(X/h).
$$

证明。令 $U=X^{31/40}$，最终 $U<h$。由 Cauchy–Schwarz 与换元 $u=x\theta$，再用 (489.1)，

$$
\int_X^{2X}B_U(x)^2\,dx\le2UX\int_0^{U/X}\!\!\int_X^{2X}\bigl(E((1+\theta)x)-E(x)\bigr)^2\,dx\,d\theta\ll UX^3\int_0^{U/X}\theta\log^2(2/\theta)\,d\theta\ll XU^3\log^2X,
$$

它与 $Xh^3\ell_X$ 之比为 $O(X^{-3/40}\log X)\to0$。对 $u\in[U,h]$，(489.2) 给出 $\int_{aX}^{bX}D_u^2\ll Xu\log X$；故当 $sh,th\ge U$ 时，协方差除以 $Xh\ell_X$ 后受 $C\sqrt{st}$ 控制。在 $[0,1]^2$ 上对 $\mathbf 1_{\{s,t\ge U/h\}}$ 加权的协方差用引理 489.2 与控制收敛，得

$$
\frac1{Xh^3\ell_X}\int_{aX}^{bX}\Bigl(\int_U^hD_u(x)\,du\Bigr)^2dx\longrightarrow(b-a)\int_0^1\!\!\int_0^1\min(s,t)\,ds\,dt=\frac{b-a}3 .
$$

由 $L^2$ 三角不等式补回 $[0,U]$ 段，得 $\int_{aX}^{bX}B_h^2\sim\frac{b-a}3Xh^3\ell_X$；除以 $h^4$ 即得结论。证毕。

**引理 489.4（移动长度）。** 令 $S_X=X^{1/5}\log X$。则

$$
\int_X^{2X}P_{H_x}(x)^2\,dx\sim\frac{2^{1/5}-1}3\,S_X .
$$

证明。固定正整数 $n$，令 $\eta=1/n$、$a_j=1+j\eta$、$I_j=[a_jX,a_{j+1}X]$、$h_j=(a_jX)^{4/5}$，并在 $I_j$ 上令 $P^{(n)}_X=P_{h_j}$。由引理 489.3（取 $c=a_j^{4/5}$，$\ell_X\sim\frac15\log X$），

$$
\frac{\|P^{(n)}_X\|_{L^2[X,2X]}^2}{S_X}\longrightarrow C_n=\frac1{15n}\sum_{j=0}^{n-1}a_j^{-4/5}.
$$

令 $H_0=X^{4/5}$、$\delta_j=(a_{j+1}^{4/5}-a_j^{4/5})H_0\le\frac45\eta H_0$；在 $I_j$ 上 $h_j\le H_x\le h_j+\delta_j$，且有分解

$$
P_{H_x}(x)-P_{h_j}(x)=\bigl(H_x^{-2}-h_j^{-2}\bigr)B_{h_j}(x)+H_x^{-2}\int_{h_j}^{H_x}D_u(x)\,du .
$$

第一项的 $L^2$ 范数至多 $C\eta\|P^{(n)}_X\|_2$。对第二项，由 Cauchy–Schwarz，$\int_{I_j}\bigl|\int_{h_j}^{H_x}D_u\,du\bigr|^2dx\le\delta_j\int_{h_j}^{h_j+\delta_j}\int_{I_j}D_u^2\,dx\,du$；再由 $\int_{I_j}D_u^2\le V(2X,u)\ll XH_0\log X$（$u\asymp H_0$），它在 $I_j$ 上的平方范数为 $O(H_0^{-4}\cdot\eta H_0\cdot\eta H_0\cdot XH_0\log X)=O(\eta^2S_X)$；对 $n$ 个格子求和得 $O(\eta S_X)$。故 $\limsup_{X\to\infty}\|P_{H_\cdot}-P^{(n)}_X\|_2/\sqrt{S_X}\ll n^{-1/2}$，常数与 $n$ 无关。又 $C_n\le\frac1{15}$ 且 $C_n\to C:=\frac1{15}\int_1^2v^{-4/5}\,dv=\frac{2^{1/5}-1}3$。令 $A_X=\|P_{H_\cdot}\|_2/\sqrt{S_X}$，由反三角不等式，对每个固定 $n$，$\limsup_{X\to\infty}|A_X-\sqrt{C_n}|\le Kn^{-1/2}$，$K$ 与 $n$ 无关；于是 $\limsup_{X\to\infty}|A_X-\sqrt C|\le Kn^{-1/2}+|\sqrt{C_n}-\sqrt C|$，令 $n\to\infty$ 得 $A_X\to\sqrt C$。证毕。

**定理 489.5（二倍区间均方渐近）。** 设 von Koch 界、(489.1) 与 (489.2)。则

$$
\lim_{X\to\infty}\frac1{X^{1/5}\log X}\int_X^{2X}\mathcal T(x)^2\,\frac{dx}x=\frac{2^{1/5}-1}3 .
\tag{489.3}
$$

因而对每个 $0<c<1/\sqrt{15}$，所有充分大的 $X$ 都有 $x\in[X,2X]$ 使

$$
|\mathcal T(x)|\ge c\,x^{1/10}\sqrt{\log x}.
\tag{489.4}
$$

证明。由引理 489.1，在 $L^2([X,2X],dx/x)$ 中 $\mathcal T$ 与 $\mathcal T_0$ 相差 $O(\log^2X)=o(\sqrt{S_X})$；再由引理 489.4 得 (489.3)。又 $W_X=\int_X^{2X}x^{1/5}\log x\,\frac{dx}x\sim5(2^{1/5}-1)X^{1/5}\log X$，故 $\int_X^{2X}\mathcal T^2\,dx/x\,\big/\,W_X\to1/15$。固定 $c<1/\sqrt{15}$，取 $X_0(c)$ 使 $X\ge X_0(c)$ 时该比值大于 $c^2$。若某个 $X\ge X_0(c)$ 的 $[X,2X]$ 上处处 $|\mathcal T(x)|<cx^{1/10}\sqrt{\log x}$，则 $\mathcal T(x)^2<c^2x^{1/5}\log x$，该比值至多 $c^2$，矛盾。证毕。

**范围说明。** 定理 489.5 给出 $\mathcal T$ 在每个充分大二倍区间上的均方渐近与精确主项常数，把 §488 的宽窗口下界 $x^{1/40}\sqrt{\log x}$ 提到自然尺度 $x^{1/10}\sqrt{\log x}$，并与命题 488.4 的上界在 $X^{1/5}$ 的幂次上相符；代价是额外假设 (489.2)，它在 RH 下由强对相关推出。(489.3) 只控制 $|\mathcal T|$，不给出带符号的幂次 $\Omega_\pm$；也不涉及 §481 所述被选整数来源上的下界。

**范围与文献归属。** 经典输入：von Koch 界；Saffari–Vaughan 短区间均方上界 (489.1)（见 Chan [More precise pair correlation of zeros and primes in short intervals, J. London Math. Soc. 68 (2003)] 式 (2)）；Goldston–Montgomery 的方差—对相关等价给出的 (489.2)。引理 489.2–489.3 所用的极化与三角平均是经典的方差转移方法。本节的 `repo-derived` 内容：引理 489.1 对原价格权的去除；引理 489.3–489.4 中对移动长度 $H_x=x^{4/5}$ 的转移，包括小长度截断与先 $X$ 后 $n$ 的双重极限；定理 489.5 对原核的渐近式 (489.3)、常数 $(2^{1/5}-1)/3$ 与逐二倍区间的取点结论 (489.4)。

## 追加锚（本行以下为增补区）

## 490. 一般指数与 $L^1$ 观测剖面的移动价格核均方定律

沿用 §481 的 $w,\rho_x$。本节令 $E:[1,\infty)\to\mathbb R$ 为局部有界的 Borel 可测函数；算术应用取 $E=\psi-\mathrm{id}$。固定 $0<\theta<1$ 与实值 $g\in L^1(0,1)$（取 Borel 代表元），令 $H_x=x^\theta$，并记

$$
D_u(x)=E(x+u)-E(x),\qquad V(Y,h)=\int_1^YD_h(x)^2\,dx,
$$

$$
F_{h,g}(x)=\int_0^1g(s)D_{sh}(x)\,ds,\qquad P_{h,g}(x)=\frac1{h^2}\int_0^hg(u/h)D_u(x)\,du=\frac{F_{h,g}(x)}h .
$$

**移动剖面核**为

$$
\mathcal T_{\theta,g}(x)=\frac{\sqrt x}{H_x^2}\int_0^{H_x}g(u/H_x)\,D_u(x)\,\rho_x(u)\,du .
\tag{490.1}
$$

取 $\theta=4/5$、$g\equiv1$ 时，$\mathcal T_{4/5,1}$ 就是 (481.1) 的 $\mathcal T$，$P_{h,1}$ 就是 §489 的 $P_h$。令

$$
G_g(r)=\int_r^1g(s)\,ds,\qquad Q(g)=\int_0^1\!\!\int_0^1g(s)g(t)\min(s,t)\,ds\,dt,\qquad S_X=X^{1-\theta}\log X .
$$

本节唯一的数论型假设是指数带上一致的普通方差渐近：对某对 $0<\alpha<\theta<\beta<1$，

$$
\sup_{Y^\alpha\le h\le Y^\beta}\left|\frac{V(Y,h)}{Yh\log(Y/h)}-1\right|\longrightarrow0\qquad(Y\to\infty).
\tag{490.2}
$$

对 $E=\psi-\mathrm{id}$，在 RH 下 (490.2) 由 Montgomery 强对相关猜想推出。Goldston [Notes on pair correlation of zeros and prime numbers, arXiv:math/0412313] §9 定理 7（p.18）对比例窗参数 $\delta$ 给出 (9.1) 的一致渐近，一致范围为 $\delta\in[Y^{-B_2},Y^{-B_1}]$（$0<B_1\le B_2<1$ 固定）；其后经 Saffari–Vaughan 转移得到加法窗的方差律 (9.3)（p.19），在 $h/Y\in[Y^{-B_2},Y^{-B_1}]$ 上一致。取 $B_1=1-\beta$、$B_2=1-\alpha$ 即得 (490.2)。因此对算术情形，任意 $0<\alpha<\theta<\beta<1$ 都可用；(489.2) 是 $\alpha=3/4$、$\beta=7/8$ 的情形。

**引理 490.1（较短增量与移动增量的一致界）。** 设 (490.2)，令 $h_0=X^\theta$。

(i) 对固定 $c>0$ 与 $h=cX^\theta$，存在常数 $C$，使对所有充分大的 $X$ 与所有 $0\le u\le h$，

$$
\int_X^{2X}D_u(x)^2\,dx\le C\,Xh\log(X/h).
$$

(ii) 存在常数 $C$，使对所有充分大的 $X$，

$$
\sup_{0\le s\le1}\int_X^{2X}D_{sx^\theta}(x)^2\,dx\le C\,Xh_0\log X .
$$

证明。(i) 由恒等式 $D_u(x)=D_{h+u}(x)-D_h(x+u)$，

$$
\int_X^{2X}D_u^2\le2\int_X^{2X}D_{h+u}^2+2\int_{X+u}^{2X+u}D_h^2\le2V(3X,h+u)+2V(3X,h).
$$

对 $v\in[h,2h]$ 一致地有 $v/(3X)^\alpha\ge c3^{-\alpha}X^{\theta-\alpha}\to\infty$、$v/(3X)^\beta\le2c3^{-\beta}X^{\theta-\beta}\to0$，且 $\log(3X/v)=\log(X/h)+O(1)$；故 (490.2) 的同一个 $X$ 门槛对全部 $u\in[0,h]$ 适用，两项都 $\ll Xh\log(X/h)$。

(ii) 令 $L_s(x)=sx^\theta$、$\phi_s(x)=x+L_s(x)$。在 $[X,2X]$ 上 $0\le L_s\le2^\theta h_0<2h_0$、$\phi_s'(x)=1+s\theta x^{\theta-1}\ge1$，且对充分大的 $X$，$\phi_s([X,2X])\subset[X,3X]$，门槛与 $s$ 无关。对每个 $v\in[3h_0,4h_0]$，有恒等式 $D_{L_s(x)}(x)=D_v(x)-D_{v-L_s(x)}(\phi_s(x))$，且 $v-L_s(x)\in[h_0,4h_0]$。平方后对 $v\in[3h_0,4h_0]$ 取平均，再对 $x$ 积分。第一部分至多 $\frac2{h_0}\int_{3h_0}^{4h_0}V(3X,v)\,dv\ll Xh_0\log X$。第二部分中，内层令 $w=v-L_s(x)$ 并把积分区间放大到 $[h_0,4h_0]$（被积函数非负），再由 Tonelli 及换元 $y=\phi_s(x)$（逆映射导数不超过 $1$）：

$$
\int_X^{2X}\!\!\int_{3h_0}^{4h_0}D_{v-L_s(x)}(\phi_s(x))^2\,dv\,dx\le\int_{h_0}^{4h_0}\!\!\int_X^{3X}D_w(y)^2\,dy\,dw\le\int_{h_0}^{4h_0}V(3X,w)\,dw\ll Xh_0^2\log X .
$$

除以 $h_0$ 即得 (ii)。证毕。

**引理 490.2（固定长度的剖面均方）。** 设 (490.2)。固定 $1\le a<b\le2$、$c>0$，令 $h=cX^\theta$、$\ell_X=\log(X/h)$。则

$$
\frac1{Xh\ell_X}\int_{aX}^{bX}F_{h,g}(x)^2\,dx\longrightarrow(b-a)\,Q(g),
\qquad\text{即}\qquad
\int_{aX}^{bX}P_{h,g}(x)^2\,dx=(b-a)Q(g)\frac Xh\log\frac Xh+o\!\Bigl(\frac Xh\log\frac Xh\Bigr).
$$

证明。令 $K_X(s,t)=\frac1{Xh\ell_X}\int_{aX}^{bX}D_{sh}(x)D_{th}(x)\,dx$。在包含全部 $x+sh$ 的紧区间上 $|D_{sh}(x)|\le2B$，故未归一化的三重绝对积分至多 $4B^2(b-a)X\|g\|_1^2$，Fubini 给出

$$
\frac1{Xh\ell_X}\int_{aX}^{bX}F_{h,g}^2\,dx=\int_0^1\!\!\int_0^1g(s)g(t)K_X(s,t)\,ds\,dt .
$$

对固定 $s,t\in[0,1]$，$K_X(s,t)\to(b-a)\min(s,t)$：这是由普通方差经极化恢复两点相关的经典计算（见 Leung [Joint distribution of primes in multiple short intervals, Adv. Math. 490 (2026), 110847] 附注 2.3），其证明与引理 489.2 逐字相同，只需核对所用长度落在 (490.2) 的指数带内。所需端点为 $Y=dX+O(h)$（$d\in[1,2]$ 固定），所需长度为 $qh$（$q\in\{s,t,|s-t|\}$ 为正的固定数），故 $qh/Y^\alpha\asymp X^{\theta-\alpha}\to\infty$、$qh/Y^\beta\asymp X^{\theta-\beta}\to0$，且 $\log(Y/(qh))=\ell_X+O(1)$；$s=t$ 或 $st=0$ 的情形无需长度 $|s-t|h$。另一方面，由引理 490.1(i) 与 Cauchy–Schwarz，存在 $C$ 使对充分大的 $X$，$\sup_{s,t\in[0,1]}|K_X(s,t)|\le C$。于是被积函数受 $C|g(s)g(t)|$ 控制，后者在单位正方形上可积；由控制收敛定理得极限 $(b-a)\iint g(s)g(t)\min(s,t)=(b-a)Q(g)$。证毕。

**引理 490.3（移动算子的一致界）。** 设 (490.2)。存在常数 $C$（只依赖 $\theta$ 与 (490.2)），使对所有 $g\in L^1(0,1)$ 与所有充分大的 $X$（门槛与 $g$ 无关），

$$
\Bigl\|P_{H_\cdot,g}\Bigr\|_{L^2[X,2X]}\le C\,\|g\|_1\sqrt{S_X},
\qquad P_{H_\cdot,g}(x):=P_{H_x,g}(x)=\frac1{x^\theta}\int_0^1g(s)D_{sx^\theta}(x)\,ds .
$$

证明。由 Minkowski 不等式与引理 490.1(ii)，$\|P_{H_\cdot,g}\|_2\le X^{-\theta}\int_0^1|g(s)|\,\|D_{sx^\theta}(x)\|_{L^2[X,2X]}\,ds\le X^{-\theta}\|g\|_1\sqrt{CX^{1+\theta}\log X}=\sqrt C\,\|g\|_1\sqrt{S_X}$。证毕。

**引理 490.4（移动长度的剖面均方）。** 设 (490.2)。则

$$
\frac1{S_X}\int_X^{2X}P_{H_x,g}(x)^2\,dx\longrightarrow Q(g)\bigl(2^{1-\theta}-1\bigr).
$$

证明。先设 $g$ 为 Lipschitz 函数，记 $M=\|g\|_\infty$、$L=\mathrm{Lip}(g)$。固定正整数 $n$，令 $\eta=1/n$、$a_j=1+j\eta$、$I_j=[a_jX,a_{j+1}X]$、$h_j=(a_jX)^\theta$，并在 $I_j$ 上令 $P^{(n)}_X=P_{h_j,g}$。由引理 490.2（取 $c=a_j^\theta$；$X/h_j=a_j^{-\theta}X^{1-\theta}$，$\log(X/h_j)=(1-\theta)\log X-\theta\log a_j$），

$$
\frac{\|P^{(n)}_X\|_{L^2[X,2X]}^2}{S_X}\longrightarrow C_n=\frac{(1-\theta)Q(g)}n\sum_{j=0}^{n-1}a_j^{-\theta}.
$$

在 $I_j$ 上 $h_j\le H_x\le h_j+d_j$，$d_j=(a_{j+1}^\theta-a_j^\theta)X^\theta\le\theta\eta h_0$，并有分解

$$
P_{H_x,g}(x)-P_{h_j,g}(x)=\int_0^{h_j}\Bigl[H_x^{-2}g(u/H_x)-h_j^{-2}g(u/h_j)\Bigr]D_u(x)\,du+H_x^{-2}\int_{h_j}^{H_x}g(u/H_x)D_u(x)\,du .
$$

对 $0\le u\le h_j$，由 $|H^{-2}-h^{-2}|\le2d/h^3$ 与 $|H^{-1}-h^{-1}|\le d/h^2$，方括号的绝对值至多 $(2M+L)d_j/h_j^3$。全部比值 $h_j/h_0$ 与全部尾部长度与 $h_0$ 之比都落在固定紧区间 $[1,2^\theta]$ 内，故下面引理 490.1 与 (490.2) 的常数及 $X$ 门槛可对全部 $j$ 与全部 $n$ 一致选取。由 Minkowski 不等式与引理 490.1(i)，第一项在 $I_j$ 上的平方范数至多 $(2M+L)^2d_j^2h_j^{-6}\bigl(h_j\sqrt{CXh_j\log X}\bigr)^2\ll_g\eta^2S_X$。对第二项，由 Cauchy–Schwarz，

$$
\int_{I_j}\Bigl|H_x^{-2}\int_{h_j}^{H_x}g(u/H_x)D_u(x)\,du\Bigr|^2dx\le M^2h_j^{-4}d_j\int_{h_j}^{h_j+d_j}\int_{I_j}D_u(x)^2\,dx\,du\ll_g\eta^2S_X ,
$$

这里对 $u\in[h_j,h_j+d_j]$ 用了 $\int_{I_j}D_u^2\le V(2X,u)\ll Xh_0\log X$。对 $n$ 个不相交格子求和得 $O_g(\eta S_X)$，故

$$
\limsup_{X\to\infty}\frac{\|P_{H_\cdot,g}-P^{(n)}_X\|_2}{\sqrt{S_X}}\le K_gn^{-1/2},
$$

$K_g$ 与 $n$ 无关。又 $a\mapsto a^{-\theta}$ 在 $[1,2]$ 上递减，上下矩形和相差 $(1-2^{-\theta})/n$，故 $C_n\to(1-\theta)Q(g)\int_1^2v^{-\theta}\,dv=Q(g)(2^{1-\theta}-1)$。令 $A_X=\|P_{H_\cdot,g}\|_2/\sqrt{S_X}$，由反三角不等式，对每个固定 $n$ 有 $\limsup_X|A_X-\sqrt{C_n}|\le K_gn^{-1/2}$；令 $n\to\infty$ 得 Lipschitz 情形。

一般 $g\in L^1(0,1)$。由 $\min(s,t)=\int_0^1\mathbf 1_{\{r\le s\}}\mathbf 1_{\{r\le t\}}\,dr$ 及 $\iint|g(s)g(t)|\min(s,t)\le\|g\|_1^2$，Fubini 给出 $Q(g)=\int_0^1G_g(r)^2\,dr=\|G_g\|_{L^2(0,1)}^2$；于是对 $f,g\in L^1(0,1)$，$|\sqrt{Q(g)}-\sqrt{Q(f)}|\le\|G_{g-f}\|_{L^2(0,1)}\le\sup_r|G_{g-f}(r)|\le\|g-f\|_1$。Lipschitz 函数在 $L^1(0,1)$ 中稠密，取 Lipschitz 的 $g_m$ 使 $\|g_m-g\|_1\to0$。由 $P_{H_x,g}-P_{H_x,g_m}=P_{H_x,g-g_m}$ 与引理 490.3，$\|P_{H_\cdot,g}-P_{H_\cdot,g_m}\|_2\le C\|g-g_m\|_1\sqrt{S_X}$ 对充分大的 $X$ 一致成立；又 $\sqrt{Q(g_m)}\to\sqrt{Q(g)}$。在反三角不等式中先令 $X\to\infty$、再令 $m\to\infty$ 即得。证毕。

**引理 490.5（去掉价格权）。** 设 (490.2)。则在 $L^2([X,2X],dx/x)$ 中 $\|\mathcal T_{\theta,g}-\sqrt x\,P_{H_x,g}\|=o(\sqrt{S_X})$。若再设 von Koch 界 $E(x)\ll\sqrt x\log^2x$，则逐点地 $\mathcal T_{\theta,g}(x)-\sqrt x\,P_{H_x,g}(x)=O\bigl(\log^2x\int_0^1s|g(s)|\,ds\bigr)$。

证明。由引理 489.1 的证明，$0\le1-\rho_x(u)\le4u/x$（$x\ge3$，$0\le u\le H_x$）。于是

$$
\Bigl|\frac{\mathcal T_{\theta,g}(x)}{\sqrt x}-P_{H_x,g}(x)\Bigr|\le\frac1{x^\theta}\int_0^1|g(s)|\,|D_{sx^\theta}(x)|\,\frac{4sx^\theta}x\,ds=\frac4x\int_0^1s|g(s)|\,|D_{sx^\theta}(x)|\,ds .
$$

由 Minkowski 不等式与引理 490.1(ii)，其 $L^2[X,2X]$ 范数 $\ll X^{-1}\|sg\|_1\sqrt{X^{1+\theta}\log X}$，与 $\sqrt{S_X}$ 之比为 $O(X^{\theta-1})\to0$。又 $\int_X^{2X}(\mathcal T_{\theta,g}-\sqrt xP_{H_x,g})^2\,dx/x=\int_X^{2X}(\mathcal T_{\theta,g}/\sqrt x-P_{H_x,g})^2\,dx$，得第一结论。逐点结论：von Koch 界给出 $|D_u(x)|\ll\sqrt x\log^2x$（$0\le u\le H_x\le x$），代入上式。证毕。

**定理 490.6（移动剖面均方定律）。** 设 $E$ 局部有界 Borel 可测，$0<\alpha<\theta<\beta<1$，(490.2) 成立，$g\in L^1(0,1)$ 实值。则

$$
\lim_{X\to\infty}\frac1{X^{1-\theta}\log X}\int_X^{2X}\mathcal T_{\theta,g}(x)^2\,\frac{dx}x=Q(g)\bigl(2^{1-\theta}-1\bigr).
\tag{490.3}
$$

若 $g$ 不几乎处处为零，则对每个 $0<c<\sqrt{(1-\theta)Q(g)}$，存在 $X_0$，使每个 $X\ge X_0$ 的 $[X,2X]$ 中满足

$$
|\mathcal T_{\theta,g}(x)|>c\,x^{(1-\theta)/2}\sqrt{\log x}
\tag{490.4}
$$

的 $x$ 构成正测度集。

证明。$\int_X^{2X}(\sqrt xP_{H_x,g})^2\,dx/x=\int_X^{2X}P_{H_x,g}^2\,dx$；由引理 490.4、490.5 与反三角不等式得 (490.3)。若 $g$ 不几乎处处为零，则 $Q(g)>0$：由引理 490.4 证明中的恒等式 $Q(g)=\|G_g\|_2^2$，若 $Q(g)=0$，则绝对连续函数 $G_g$ 几乎处处为零，由连续性处处为零，而 $G_g'=-g$ 几乎处处，故 $g=0$ 几乎处处。令 $W_X=\int_X^{2X}x^{1-\theta}\log x\,\frac{dx}x$；换元 $x=Xv$ 得 $W_X=X^{1-\theta}\bigl[\log X\int_1^2v^{-\theta}dv+\int_1^2v^{-\theta}\log v\,dv\bigr]\sim\frac{2^{1-\theta}-1}{1-\theta}X^{1-\theta}\log X$。故 $\int_X^{2X}\mathcal T_{\theta,g}^2\,\frac{dx}x\big/W_X\to(1-\theta)Q(g)>0$。固定 $c$ 后取 $X_0$ 使 $X\ge X_0$ 时该比值大于 $c^2$。若 (490.4) 在 $[X,2X]$ 上只在零测集上成立，则几乎处处 $\mathcal T_{\theta,g}(x)^2\le c^2x^{1-\theta}\log x$，比值至多 $c^2$，矛盾。证毕。

**推论 490.7（§489 假设的精简）。** 取 $\theta=4/5$、$g\equiv1$、$\alpha=3/4$、$\beta=7/8$：$Q(1)=\int_0^1(1-r)^2dr=\frac13$，(490.3) 成为 (489.3)，阈值 $\sqrt{(1-\theta)Q(1)}=1/\sqrt{15}$ 与 (489.4) 相同。因此定理 489.5 的结论只需 (489.2) 与 $E$ 的局部有界可测性；§489 的证明所用的 von Koch 界与 (489.1) 分别只服务于引理 489.1 的逐点误差与 §489 的小长度截断。

**附注 490.8（二阶 Brownian 结构）。** 引理 490.2 的证明说明：在 (490.2) 下，关于概率测度 $dx/((b-a)X)$ 在 $[aX,bX]$ 上平均，归一化增量 $s\mapsto D_{sh}(x)/\sqrt{h\log(X/h)}$ 的二阶矩核趋于 $\min(s,t)$，即标准 Brownian 运动的协方差；素数计数的 Brownian（Hurst 指数 $1/2$）预期见 Gorodetsky–Matomäki–Radziwiłł–Rodgers [On the variance of squarefree integers in short intervals and arithmetic progressions, Geom. Funct. Anal. 31 (2021), 111–149] §1.2，$x^\theta$ 窗中方差的 $1-\theta$ 因子见 Montgomery–Soundararajan [Primes in short intervals, Comm. Math. Phys. 252 (2004), 589–617] p.8。若再设 von Koch 界，则 $\int_{aX}^{bX}D_{sh}(x)\,dx=\int_{bX}^{bX+sh}E-\int_{aX}^{aX+sh}E=O(h\sqrt X\log^2X)$，归一化均值为 $O\bigl(\sqrt{h/X}\log^{3/2}X\bigr)=o(1)$，故中心化协方差有同一极限。对 $E=\psi-\mathrm{id}$，$E$ 在紧区间上有界变差，$D_{sh}(x)=\int_{(x,x+sh]}dE(t)$，绝对 Fubini 给出

$$
F_{h,g}(x)=\int_{(x,x+h]}G_g\Bigl(\frac{t-x}h\Bigr)\,dE(t),
$$

其中连续部分为 $-\int_x^{x+h}G_g((t-x)/h)\,dt=-h\int_0^1s\,g(s)\,ds$，与 $F_{h,g}(x)=\int_0^1g(s)\bigl(\psi(x+sh)-\psi(x)-sh\bigr)ds$ 的漂移项一致；于是 $Q(g)=\|G_g\|_{L^2(0,1)}^2$ 是这一短窗线性统计在该协方差下的二次能量。本节只用到二阶结构；高阶混合矩、有限维高斯分布与紧性都不在本节结论之内，本节不给出随机过程意义下的收敛。

**范围。** 比例窗与加法窗之间的方差转移另见 Bui–Keating–Smith [On the variance of sums of arithmetic functions over primes in short intervals and pair correlation for $L$-functions in the Selberg class, J. London Math. Soc. 94 (2016), 161–185] 定理 $C_1,C_2,D_1,D_2$，那里的定量结论要求幂次节省的误差。Leung 前引文定理 10.1 的移动窗结论在 RH、LI 与 QLI 下对对数取样 $x=e^u$ 成立，并要求 $\log(1/\delta)=o(\log U)$，不覆盖这里固定 $\theta<1$ 的普通二倍区间取样。定理 490.6 只控制 $|\mathcal T_{\theta,g}|$，不给出带符号的幂次 $\Omega_\pm$。

## 追加锚（本行以下为增补区）

## 491. 不同指数的移动剖面核的渐近正交

沿用 §490 的 $E,D_u,V,\rho_x,\mathcal T_{\theta,g}$ 与 (490.2)。固定 $0<a<b<1$、实值 $g_1,g_2\in L^1(0,1)$，令

$$
h=X^a,\qquad k=X^b,\qquad A_X=(X\log X)^{1/2},\qquad N_X=X^{1-(a+b)/2}\log X,
$$

$$
f_s(x)=D_{sx^a}(x),\qquad z_t(x)=D_{tx^b}(x)\qquad(s,t\in[0,1]).
$$

由 (490.1)，$\mathcal T_{\theta,g}(x)=x^{1/2-\theta}\int_0^1g(s)D_{sx^\theta}(x)\rho_x(sx^\theta)\,ds$；由定理 490.6，$\|\mathcal T_{a,g_1}\|_{L^2([X,2X],dx/x)}\|\mathcal T_{b,g_2}\|_{L^2([X,2X],dx/x)}\asymp N_X$（$g_1,g_2$ 非零时）。

下面只用 (490.2) 推出的**上界**。称尺度 $R=R(X)$ 满足**可比长度上界**，若对每组固定的 $0<c_1\le c_2$ 与 $C\ge1$，对充分大的 $X$，

$$
V(CX,u)\ll XR\log X\qquad(c_1R\le u\le c_2R).
\tag{491.1}
$$

若 (490.2) 在某个包含 $\rho$ 的开指数带上成立，则 $R=X^\rho$ 满足 (491.1)。全部范数取在 $[X,2X]$ 的固定放大区间（例如 $[X/2,4X]$）上；下面所有平移都是 $O(k)=o(X)$，故放大区间足够；所有常数对 $s,t\in[0,1]$ 与 $[X,2X]$ 的子区间一致。

**引理 491.1（两端移动的增量）。** 设尺度 $R$ 满足 (491.1)。设 $p,q$ 是工作区间上递增的 $C^1$ 映射，导数有固定正下界，像落在固定放大区间内，且 $0\le q(x)-p(x)\le C_0R$。则 $\|E\circ q-E\circ p\|_2\ll A_X\sqrt R$。特别地（取 $p(x)=x$、$q(x)=x+u$），$\sup_{0\le u\le C_0R}\|D_u\|_2\ll A_X\sqrt R$。

证明。令 $\delta=q-p$。对 $v\in[(C_0+1)R,(C_0+2)R]$ 有恒等式 $E(q(x))-E(p(x))=D_v(p(x))-D_{v-\delta(x)}(q(x))$，因为 $q+(v-\delta)=p+v$。平方后用 $(u-v)^2\le2u^2+2v^2$ 并对 $v$ 取平均。第一项经换元 $y=p(x)$（逆映射导数有界）至多 $\frac2R\int_{(C_0+1)R}^{(C_0+2)R}V(CX,v)\,dv\ll XR\log X$。第二项中先令 $w=v-\delta(x)$ 并把 $w$ 的范围放大到 $[R,(C_0+2)R]$（被积函数非负），再由 Tonelli 与换元 $y=q(x)$ 得同一界。证毕。

当 $p(x)=x$、$q(x)=x+u$ 时，这正是引理 490.1(i) 所用的恒等式 $D_u(x)=D_{R+u}(x)-D_R(x+u)$ 的移动形式。

**引理 491.2（移动短增量的平均）。** 设 $h$ 与 $M$ 满足 (491.1)，$h\ll M=o(X)$，令 $\mathscr A_Mu(x)=\frac1M\int_0^Mu(x+r)\,dr$。则对 $s\in[0,1]$ 一致地，

$$
\|\mathscr A_Mf_s\|_2\ll\frac hM\,A_X\sqrt M .
$$

证明。令 $L(x)=sx^a$、$\phi(x)=x+L(x)$、$\xi=\phi^{-1}$、$q=\xi'$。在放大区间上 $L\ll h$、$0\le L'\ll h/X$、$|q-1|\ll h/X$。固定 $x$，令 $P=\phi(x)$、$Q=\phi(x+M)$、$Q_0=x+M+L(x)$、$\delta=Q-Q_0$，则 $0\le\delta\ll hM/X$。由 $\int_0^ME(\phi(x+r))\,dr=\int_P^QE(y)q(y)\,dy$，得恒等式

$$
M\,\mathscr A_Mf_s(x)=\int_0^{L(x)}D_M(x+r)\,dr+\int_P^Q(q(y)-1)\bigl(E(y)-E(x)\bigr)\,dy+\int_{Q_0}^Q\bigl(E(y)-E(x)\bigr)\,dy ,
$$

其中减去 $E(x)$ 合法，因为 $\int_P^Q(q-1)\,dy+\delta=M-(M+\delta)+\delta=0$。第一项由 Minkowski 不等式与 (491.1) 的 $L^2$ 范数为 $O(hA_X\sqrt M)$。第二项中令 $y=x+u$，$u$ 的范围放大到 $[0,CM]$，由引理 491.1，其范数为 $O\bigl(\frac{hM}XA_X\sqrt M\bigr)$。第三项中令 $y=Q_0(x)+v$，插入示性函数 $\mathbf 1_{v\le\delta(x)}$ 并对 $0\le v\le ChM/X$ 积分；对每个固定的 $v$，端点映射 $x$ 与 $x+M+L(x)+v$ 满足引理 491.1 的条件，故由 Minkowski 不等式得同一界。除以 $M$ 并用 $M=o(X)$。证毕。

**引理 491.3（四尺度分离）。** 设 $h,M,T,k$ 都满足 (491.1)，$h\ll M\ll T\ll k$。则对每个区间 $I\subset[X,2X]$ 与 $s,t\in[0,1]$，

$$
\Bigl|\int_If_s(x)z_t(x)\,dx\Bigr|\ll A_X^2\sqrt{hk}\Bigl(\sqrt{\frac hM}+\sqrt{\frac MT}+\sqrt{\frac Tk}\Bigr).
$$

证明。由引理 491.1，$\|f_s\|_2\ll A_X\sqrt h$、$\|z_t\|_2\ll A_X\sqrt k$。令 $\psi(x)=x+tx^b$。对 $0\le r\le R$（$R=M$ 或 $T$），$z_t(x+r)-z_t(x)=\bigl[E(\psi(x+r))-E(\psi(x))\bigr]-D_r(x)$；前一项的端点映射之差为 $O(R)$，由引理 491.1，

$$
\|z_t(\cdot+r)-z_t\|_2\ll A_X\sqrt R .
\tag{491.2}
$$

对长度至多 $M$ 的区间 $J$，把 $z_t(x)^2\le2z_t(x+r)^2+2|z_t(x+r)-z_t(x)|^2$ 对 $r\in[0,T]$ 取平均再在 $J$ 上积分，由 Fubini 与 (491.2)，

$$
\int_Jz_t^2\ll\frac MT\|z_t\|_2^2+A_X^2T\ll A_X^2\Bigl(\frac{Mk}T+T\Bigr).
\tag{491.3}
$$

现在比较 $\int_If_sz_t$ 与 $\int_I(\mathscr A_Mf_s)z_t$。后者由引理 491.2 至多 $\frac hMA_X\sqrt M\cdot A_X\sqrt k=A_X^2\sqrt{hk}\sqrt{h/M}$。对每个 $r\le M$，$\int_If_s(x+r)z_t(x)\,dx$ 经平移变为 $I+r$ 上 $f_s(y)z_t(y-r)$ 的积分；在 $I\cap(I+r)$ 上，与 $\int f_sz_t$ 之差由 (491.2) 与 Cauchy–Schwarz 至多 $A_X\sqrt h\cdot A_X\sqrt M\le A_X^2\sqrt{hk}\sqrt{M/T}\sqrt{T/k}$；其余是长度至多 $M$ 的端点条，由 Cauchy–Schwarz 与 (491.3) 至多 $A_X\sqrt h\cdot A_X\sqrt{Mk/T+T}=A_X^2\sqrt{hk}\sqrt{M/T+T/k}$。对 $r$ 取平均，并用 $\sqrt{M/k}=\sqrt{M/T}\sqrt{T/k}\le\sqrt{M/T}+\sqrt{T/k}$ 吸收重叠项，即得。$|I|<M$ 时同样成立。证毕。

**引理 491.4（移动差的转移）。** 令 $\phi(x)=x+sx^a$，$I\subset[X,2X]$。对放大区间上的 $u\in L^2$ 与 $v\in C^1$，

$$
\Bigl|\int_I\bigl[u(\phi(x))-u(x)\bigr]v(x)\,dx\Bigr|\ll h\|u\|_2\|v'\|_2+\frac hX\|u\|_2\|v\|_2+\|v\|_\infty\int_{J}|u| ,
$$

其中 $J$ 是总长 $O(h)$ 的端点条；末项至多 $Ch\|u\|_\infty\|v\|_\infty$，也至多 $C\sqrt h\|u\|_2\|v\|_\infty$。又对 $u\in C^1$，$\|u\circ\phi-u\|_2\ll h\|u'\|_2$；对长映射 $\psi(x)=x+tx^b$（$1\le\psi'\le2$），$\|u\circ\psi-u\|_2\ll\|u\|_2$、$\|(u\circ\psi-u)'\|_2\ll\|u'\|_2$。

证明。对第一项作换元 $y=\phi(x)$。在 $I\cap\phi(I)$ 上令 $\xi=\phi^{-1}$、$q=\xi'$，被积函数之差为 $u(y)\bigl\{v(\xi(y))-v(y)+(q(y)-1)v(\xi(y))\bigr\}$，其中 $0\le y-\xi(y)\ll h$、$|q-1|\ll h/X$，且 $|v(\xi(y))-v(y)|\le\int_{y-Ch}^y|v'|$；由 Fubini 与 Cauchy–Schwarz，后者的 $L^2$ 范数至多 $Ch\|v'\|_2$。$I\triangle\phi(I)$ 的测度为 $O(h)$，给出端点项。其余估计直接由同样的换元得到。证毕。

**二重平均与二进分解。** 设 (490.2) 在一个指数带 $0<\alpha<a<b<\beta<1$ 上成立。令 $Z_R=\mathscr A_R^2E$、$B_R=Z_R-Z_{2R}$、$r_h=E-Z_h$。则 $Z_R\in C^1$ 且

$$
Z_R'=\frac1R\,\mathscr A_RD_RE ,
\qquad
B_R=-\tfrac12\mathscr A_R^2D_RE-\tfrac14\mathscr A_R^2D_{2R}E .
\tag{491.4}
$$

前者因为 $\mathscr A_RE$ 局部绝对连续且导数为 $D_RE/R$，再作一次平均；后者由 $\mathscr A_{2R}=\frac12(I+T_R)\mathscr A_R$（$T_Ru=u(\cdot+R)$）展开 $Z_{2R}=\frac14(Z_R+2T_RZ_R+T_{2R}Z_R)$ 得到。由 (490.2) 得 $\|D_u\|_2\ll A_X\sqrt u$（$h\le u\le8k$）与 $\sup_{0\le u\le2h}\|D_u\|_2\ll A_X\sqrt h$（引理 491.1）。于是对 $h\le R\le2k$，由 (491.4)、Minkowski 不等式，以及 $|\mathscr A_Ru(x)|\le R^{-1/2}\|u\|_2$：

$$
\|B_R\|_2\ll A_X\sqrt R,\quad\|B_R'\|_2\ll\frac{A_X}{\sqrt R},\quad\|B_R\|_\infty\ll A_X,\quad\|Z_R'\|_2\ll\frac{A_X}{\sqrt R},\quad\|Z_R'\|_\infty\ll\frac{A_X}R ;
\tag{491.5}
$$

又 $r_h$ 是长度至多 $2h$ 的增量的平均，故 $\|r_h\|_2\ll A_X\sqrt h$。取 $N$ 使 $K=2^Nh\in[k,2k)$，则 $N\ll1+\log(k/h)$ 且 $Z_h=Z_K+\sum_{j=0}^{N-1}B_{2^jh}$。

**引理 491.5（共同指数带上的一致协方差界）。** 设 (490.2) 在 $0<\alpha<a<b<\beta<1$ 上成立。则对每个区间 $I\subset[X,2X]$ 与 $s,t\in[0,1]$，

$$
\Bigl|\int_If_s(x)z_t(x)\,dx\Bigr|\ll Xh\log X\,\bigl(1+\log(k/h)\bigr)^2 .
$$

证明。记 $U_au=u\circ\phi-u$、$U_bu=u\circ\psi-u$，则 $f_s=U_aE$、$z_t=U_bE$，$E=Z_h+r_h$。(i) $|\langle U_aE,U_br_h\rangle_I|\le\|f_s\|_2\|U_br_h\|_2\ll A_X^2h$。(ii) 令 $v=U_bZ_h$；由 (491.5) 与引理 491.4，$\|v'\|_2\ll A_X/\sqrt h$、$\|v\|_2\le\|z_t\|_2+\|U_br_h\|_2\ll A_X\sqrt k$，且 $\|v\|_\infty\le\sum_j\|U_bB_{2^jh}\|_\infty+k\|Z_K'\|_\infty\ll A_X(N+1)$。由引理 491.4（$u=r_h$，末项取 $L^2$ 形式），$|\langle U_ar_h,v\rangle_I|\ll A_X^2h(N+1)$，因为 $\frac hX\|r_h\|_2\|v\|_2\ll A_X^2h\sqrt{hk}/X\le A_X^2h$。(iii) 余下 $\langle U_aZ_h,U_bZ_h\rangle_I$，按二进分解展开两个因子。第一因子为 $Z_K$ 时，$\|U_aZ_K\|_2\ll h\|Z_K'\|_2\ll A_Xh/\sqrt k$，乘以 $\|U_bZ_h\|_2\ll A_X\sqrt k$ 得 $A_X^2h$。第一因子为 $B_R$、第二因子为 $Z_K$ 时，由引理 491.4（末项取上确界形式）与 $\|U_bZ_K\|_2\ll A_X\sqrt k$、$\|(U_bZ_K)'\|_2\ll A_X/\sqrt k$、$\|U_bZ_K\|_\infty\ll A_X$，得 $O(A_X^2h)$。两个因子为 $B_R,B_S$ 时：若 $S\le R$，$\|U_aB_R\|_2\|U_bB_S\|_2\ll\frac{A_Xh}{\sqrt R}A_X\sqrt S\le A_X^2h$；若 $S>R$，由引理 491.4，界为 $A_X^2h\bigl(\sqrt{R/S}+\sqrt{RS}/X+1\bigr)\ll A_X^2h$。共 $(N+1)^2$ 对，合计 $O\bigl(A_X^2h(N+1)^2\bigr)$。证毕。

**定理 491.6（跨指数渐近正交）。** 设 $E$ 局部有界 Borel 可测，$0<a<b<1$，$g_1,g_2\in L^1(0,1)$ 实值。

(i) **两条指数带。** 设 (490.2) 分别在 $0<\alpha_1<a<\beta_1<1$ 与 $0<\alpha_2<b<\beta_2<1$ 上成立。任取固定的 $a<\mu<\nu<\min(\beta_1,b)$，令 $\eta_0=\frac12\min\{\mu-a,\nu-\mu,b-\nu\}$。则

$$
\Bigl|\int_X^{2X}\mathcal T_{a,g_1}(x)\mathcal T_{b,g_2}(x)\,\frac{dx}x\Bigr|\ll\|g_1\|_1\|g_2\|_1\,N_X\,X^{-\eta_0}.
\tag{491.6}
$$

(ii) **共同指数带。** 设 (490.2) 在 $0<\alpha<a<b<\beta<1$ 上成立。则

$$
\Bigl|\int_X^{2X}\mathcal T_{a,g_1}(x)\mathcal T_{b,g_2}(x)\,\frac{dx}x\Bigr|\ll\|g_1\|_1\|g_2\|_1\,X^{1-b}\log X\,\bigl(1+(b-a)\log X\bigr)^2 ,
\tag{491.7}
$$

即相对于 $N_X$ 为 $O\bigl(\|g_1\|_1\|g_2\|_1X^{-(b-a)/2}(\log X)^2\bigr)$。

两处常数只依赖 $E$、指数带与 $a,b$，对剖面的依赖只经 $\|g_1\|_1\|g_2\|_1$。

证明。令 $r_{\theta,s}(x)=\rho_x(sx^\theta)$、$W_{s,t}(x)=x^{-a-b}r_{a,s}(x)r_{b,t}(x)$，则

$$
\int_X^{2X}\mathcal T_{a,g_1}\mathcal T_{b,g_2}\frac{dx}x=\int_0^1\!\!\int_0^1g_1(s)g_2(t)\int_X^{2X}W_{s,t}(x)f_s(x)z_t(x)\,dx\,ds\,dt ;
$$

对固定的 $X$，所用 $E$ 的值都在一个紧区间内，局部有界性给出对 $|g_1(s)g_2(t)|\,ds\,dt\,dx$ 的绝对可积性，Fubini 成立。令 $\ell=\log w$。由 §481 的显式公式，$\ell'(x)=O(x^{-1})$、$\ell''(x)=O(x^{-2})$；由 $\frac d{dx}\log r_{\theta,s}=\ell'(x+sx^\theta)(1+s\theta x^{\theta-1})-\ell'(x)$，对 $s\in[0,1]$ 一致地 $r_{\theta,s}=O(1)$、$r_{\theta,s}'=O(X^{\theta-2})$（$X\le x\le2X$）。于是 $|W_{s,t}(2X)|+\int_X^{2X}|W_{s,t}'|\ll X^{-a-b}$。令 $F_{s,t}(y)=\int_X^yf_sz_t$；分部积分给出

$$
\Bigl|\int_X^{2X}W_{s,t}f_sz_t\,dx\Bigr|\le\sup_{y\in[X,2X]}|F_{s,t}(y)|\Bigl(|W_{s,t}(2X)|+\int_X^{2X}|W_{s,t}'|\Bigr).
$$

(i) 取 $M=X^\mu$、$T=X^\nu$。尺度 $h,M,T$ 落在第一条带内，$k$ 落在第二条带内，故都满足 (491.1)。由引理 491.3，$\sup_y|F_{s,t}(y)|\ll A_X^2\sqrt{hk}\,X^{-\eta_0}$，乘以 $X^{-a-b}$ 得 $N_XX^{-\eta_0}$，再对 $|g_1(s)g_2(t)|$ 积分。(ii) 由引理 491.5，$\sup_y|F_{s,t}(y)|\ll Xh\log X(1+\log(k/h))^2$，乘以 $X^{-a-b}$ 得 $X^{1-b}\log X(1+(b-a)\log X)^2$。证毕。

**推论 491.7（多尺度归一化）。** 设 $0<\theta_1<\dots<\theta_m<1$，$m$ 固定，(490.2) 在包含每个 $\theta_j$ 的开指数带上成立，$g_j\in L^1(0,1)$ 实值，$c_j\in\mathbb R$。则

$$
\int_X^{2X}\Bigl(\sum_{j=1}^mc_j\frac{\mathcal T_{\theta_j,g_j}(x)}{\sqrt{X^{1-\theta_j}\log X}}\Bigr)^2\frac{dx}x\longrightarrow\sum_{j=1}^mc_j^2\bigl(2^{1-\theta_j}-1\bigr)Q(g_j).
$$

证明。展开有限平方：对角项由定理 490.6 收敛；非对角项由定理 491.6(i) 趋于零。证毕。

**范围。** 由普通方差经极化恢复两点相关，见 Leung [Joint distribution of primes in multiple short intervals, Adv. Math. 490 (2026), 110847, doi:10.1016/j.aim.2026.110847] 附注 2.3；该文命题 2.2 给出等长、互不相交的比例短区间的协方差，定理 10.1 的移动窗结论在 RH、LI 与 QLI 下对对数取样成立，要求 $\log(1/\delta)=o(\log U)$。增量关系 $D_k-D_h=D_{k-h}(\cdot+h)$ 也出现在 Bui–Keating–Smith [On the variance of sums of arithmetic functions over primes in short intervals and pair correlation for $L$-functions in the Selberg class, J. London Math. Soc. 94 (2016), 161–185, doi:10.1112/jlms/jdw030] §5.3 定理 $C_1$ 的证明中，那里用于长度 $H_1<H_2<2H_1$ 之间的方差转移。Montgomery–Soundararajan [Primes in short intervals, Comm. Math. Phys. 252 (2004), 589–617, doi:10.1007/s00220-004-1222-4] 处理单一长度的矩，Goldston–Yıldırım [Canad. J. Math. 50 (1998), 563–580] 处理单一长度在算术级数中的方差，Coppola–Laporta [Afrika Mat. 29 (2018), 1245–1263] 处理固定位移的相关；这些文献都不处理两个幂次分离长度 $x^a,x^b$（$a<b$）的增量之间的协方差。直接对 $\int D_hD_k$ 作极化只给出 $O(Xh\log X)+O(\varepsilon_XXk\log X)$，其中 $\varepsilon_X\to0$ 是 (490.2) 的一致误差；当 $k/h\to\infty$ 时，归一化后的第二项不必趋于零。定理 491.6 的证明采用引理 491.1–491.5 的平均与二进分解，仅依赖 (490.2) 推出的上界 (491.1)。定理 491.6 与推论 491.7 只涉及二阶量，不给出渐近独立、高斯性或随机过程意义下的收敛，也不给出带符号的幂次 $\Omega_\pm$。

## 追加锚（本行以下为增补区）

## 492. 共同指数带交叉界的近最优性：保持方差的端点对数尖峰

沿用 §490 的 $w,\rho_x$。对局部有界 Borel 可测的 $E:[1,\infty)\to\mathbb R$，记 $D^E_u(x)=E(x+u)-E(x)$、$V_E(Y,u)=\int_1^Y(D^E_u)^2$，

$$
\mathcal T^E_{\theta,1}(x)=x^{1/2-\theta}\int_0^1D^E_{sx^\theta}(x)\,\rho_x(sx^\theta)\,ds .
$$

固定 $0<\alpha<a<b<\beta<1$。本节的假设恰为 (490.2) 在共同指数带上的形式：

$$
\sup_{Y^\alpha\le u\le Y^\beta}\left|\frac{V_E(Y,u)}{Yu\log(Y/u)}-1\right|\longrightarrow0 .
\tag{492.1}
$$

令 $C_E(X)=\int_X^{2X}\mathcal T^E_{a,1}(x)\mathcal T^E_{b,1}(x)\,\frac{dx}x$ 与 $R_b(X)=X^{1-b}(\log X)^3/\log\log X$（$X>e$）。由定理 491.6(ii)，(492.1) 蕴含 $C_E(X)=O\bigl(X^{1-b}(\log X)^3\bigr)$。

**引理 492.1（截断对数的平移能量）。** 对 $0<h<k$，令 $\ell_{h,k}(y)=\log\bigl(\min\{k,\max\{h,|y|\}\}/k\bigr)$。存在绝对常数 $C$，使对所有 $0<h<k$ 与 $u>0$，

$$
\int_{\mathbb R}\bigl|\ell_{h,k}(y+u)-\ell_{h,k}(y)\bigr|^2\,dy\le Cu .
$$

证明。$v\mapsto\min\{\log k,\max\{\log h,v\}\}$ 是 $1$-Lipschitz 的，故除 $y\in\{0,-u\}$ 外 $|\ell_{h,k}(y+u)-\ell_{h,k}(y)|\le|\log|y+u|-\log|y||$。换元 $y=uz$，右端的平方积分为 $u\int_{\mathbb R}(\log|z+1|-\log|z|)^2\,dz$；该积分有限，因为 $\log^2|z|$ 在 $0$、$-1$ 附近局部可积，而 $|z|\ge2$ 时被积函数为 $O(z^{-2})$。证毕。

此界与尖峰深度 $\log(k/h)$ 无关。

**引理 492.2（保持方差的全局扰动）。** 令 $X_n=10^n$、$h_n=X_n^a$、$k_n=X_n^b$、$A_n^2=X_n\log X_n/\log\log X_n$，取 $n_0$ 使 $n\ge n_0$ 时 $k_n\le X_n/10$，并令

$$
F(x)=\sum_{n\ge n_0}A_n\,\ell_{h_n,k_n}(x-X_n).
\tag{492.2}
$$

则 $F$ 连续、局部有界；当 $Y\to\infty$ 时，对 $0<u\le Y^\beta$ 一致地 $V_F(Y,u)\ll Yu\log Y/\log\log Y$；并且 $F(x)\ll\sqrt x\,(\log x)^{3/2}/\sqrt{\log\log x}$。

证明。第 $n$ 项的支撑为 $[X_n-k_n,X_n+k_n]$，诸支撑两两不交且趋于无穷，故和局部有限，$F$ 连续。充分大时 $Y+u\le2Y$；第 $n$ 项的支撑含于 $[0.9X_n,1.1X_n]$；若它对某个 $x\in[1,Y]$ 的 $F(x)$ 或 $F(x+u)$ 有贡献，则 $0.9X_n\le2Y$，于是 $X_n\le\frac{20}9Y<3Y$。由引理 492.1 与 $L^2$ 三角不等式，$\|D^F_u\|_{L^2[1,Y]}\le\sqrt{Cu}\sum_{X_n\le3Y}A_n$；令 $m=\max\{n:X_n\le3Y\}$，则 $0.3Y<X_m\le3Y$；因 $A_{n+1}/A_n\to\sqrt{10}>2$，充分大时 $\sum_{n_0\le n\le m}A_n\ll A_m$，故 $\sum_{X_n\le3Y}A_n\ll\sqrt{Y\log Y/\log\log Y}$。平方即得方差界。最后，在第 $n$ 项的支撑上 $x\asymp X_n$ 且 $|F(x)|\le A_n\log(k_n/h_n)=(b-a)\sqrt{X_n}(\log X_n)^{3/2}/\sqrt{\log\log X_n}$。证毕。

由于在带内 $\log(Y/u)\ge(1-\beta)\log Y$，引理 492.2 给出 $\sup_{Y^\alpha\le u\le Y^\beta}V_F(Y,u)/(Yu\log(Y/u))\ll1/\log\log Y$。若 $E_0$ 满足 (492.1)，记 $M(Y,u)=Yu\log(Y/u)$、$\varepsilon_0(Y)=\sup_{Y^\alpha\le u\le Y^\beta}|V_{E_0}(Y,u)/M(Y,u)-1|$，则 $\varepsilon_0(Y)\to0$，且 $V_{E_0}/M$ 在带内最终一致有界。由 Cauchy–Schwarz，$|V_{E_0\pm F}-V_{E_0}|\le2\sqrt{V_{E_0}V_F}+V_F$，故

$$
\sup_{Y^\alpha\le u\le Y^\beta}\frac{|V_{E_0\pm F}(Y,u)-V_{E_0}(Y,u)|}{M(Y,u)}\ll(\log\log Y)^{-1/2},\qquad\sup_{Y^\alpha\le u\le Y^\beta}\Bigl|\frac{V_{E_0\pm F}(Y,u)}{M(Y,u)}-1\Bigr|\le\varepsilon_0(Y)+O\bigl((\log\log Y)^{-1/2}\bigr),
$$

于是 $E_0+F$ 与 $E_0-F$ 也满足 (492.1)。

**引理 492.3（单个尖峰的交叉能量）。** 记 $\ell=\ell_{h,k}$、$L=\log(k/h)$，对 $y\ge0$、$q>0$ 令 $B_q(y)=\int_0^1\bigl(\ell(y+sq)-\ell(y)\bigr)\,ds$。当 $k\ge2h$ 时，

$$
\int_0^kB_h(y)B_k(y)\,dy=\frac h4L^2+O(hL),
$$

其中隐含常数绝对。

证明。在 $[0,\infty)$ 上 $\ell$ 递增，故 $B_q\ge0$。在 $0\le y<h$ 上，$0\le B_h\le\log2$、$0\le B_k\le L$，贡献为 $O(hL)$。对 $h\le y\le k$，令 $c=y/k$，直接积分得

$$
B_k(y)=\log\frac ky-1+c\Bigl(1+\log\frac ky\Bigr),\qquad 0\le B_k(y)\le\log\frac ky .
$$

对 $h\le y\le k-h$，$B_h(y)=\int_0^1\log(1+sh/y)\,ds=\frac h{2y}+O(h^2/y^2)$；误差项的贡献至多 $O\bigl(h^2\int_h^k\log(k/y)\,y^{-2}\,dy\bigr)=O(hL)$。在 $[k-h,k]$ 上两个 $B$ 都是 $O(h/k)$，贡献为 $O(h^3/k^2)$；把近似主项 $\frac h{2y}B_k(y)$ 的积分延伸到这一段，代价同样是 $O(h^3/k^2)$。于是 $\int_0^kB_hB_k=\frac h2\int_h^kB_k(y)\,\frac{dy}y+O(hL)$；令 $v=\log(k/y)$，

$$
\int_h^k\frac{B_k(y)}y\,dy=\int_0^L\bigl(v-1+e^{-v}(1+v)\bigr)\,dv=\frac{L^2}2-L+2-(L+2)e^{-L}.
$$

代入即得。证毕。

**引理 492.4（原移动长度与原价格权下的尖峰交叉项）。** 对引理 492.2 的 $F$，

$$
C_F(X_n)=\Bigl(\frac{(b-a)^2}4+o(1)\Bigr)\,R_b(X_n)\qquad(n\to\infty).
$$

证明。固定 $X=X_n$，记 $h=h_n$、$k=k_n$、$A=A_n$。对 $x\in[X,2X]$ 及长度至多 $2k$ 的前向增量，只有第 $n$ 个尖峰出现，且 $x\ge X+k$ 时两个前向增量都为零（$\ell$ 在 $[k,\infty)$ 上为零）。令 $y=x-X\ge0$，则 $\int_0^1D^F_{sq}(x)\,ds=A\,B_q(y)$。在 $0\le y\le2k$ 上，$x^a/h=1+O(k/X)$、$x^b/k=1+O(k/X)$、$x^{-a-b}=X^{-a-b}(1+O(k/X))$。对 $y\ge h$，$\ell$ 在 $[h,k]$ 上为 $\log(t/k)$（导数 $1/t$ 递减），在 $k$ 处导数降为零并此后保持常数，故 $f_y(t)=\ell(y+t)-\ell(y)$ 在 $[0,\infty)$ 上递增、凹且 $f_y(0)=0$；于是 $r\le q$ 时 $f_y(sr)\le f_y(sq)\le\frac qrf_y(sr)$，对 $s$ 积分得 $B_r(y)\le B_q(y)\le\frac qrB_r(y)$；这把移动长度 $x^a,x^b$ 换成 $h,k$，相对误差为 $O(k/X)$。在 $0\le y<h$ 上，充分大时 $x^a\le2h$，$B_{x^a}(y)\le\log3$、$B_{x^b}(y)\le L$，贡献为 $O(hL)$。对价格权，由引理 489.1 的证明 $1-4u/x\le\rho_x(u)\le1$；这里 $u\le2k$ 且两个前向增量非负，所以价格权在相对误差 $O(k/X)$ 内被夹住。由引理 492.3，

$$
C_F(X)=A^2X^{-a-b}\Bigl[\frac h4L^2+O(hL)+O\Bigl(\frac kXhL^2\Bigr)\Bigr],
$$

而 $A^2X^{-a-b}\cdot\frac h4L^2=\frac{(b-a)^2}4\,X^{1-b}(\log X)^3/\log\log X$。证毕。

**定理 492.5（共同指数带交叉界的近最优性）。** 设 $E_0:[1,\infty)\to\mathbb R$ 局部有界、Borel 可测，满足 (492.1)。令 $F$ 为 (492.2)。则：

(i) $E_0$、$E_0+F$、$E_0-F$ 都满足 (492.1)；

(ii) $F(x)\ll\sqrt x\,(\log x)^{3/2}/\sqrt{\log\log x}$；特别地，若 $E_0(x)=O(\sqrt x\log^2x)$，则 $E_0\pm F$ 也满足 $O(\sqrt x\log^2x)$；

(iii) 存在固定的 $\varepsilon_*\in\{-1,0,1\}$，使 $E_*=E_0+\varepsilon_*F$ 满足

$$
\limsup_{X\to\infty}\frac{|C_{E_*}(X)|}{R_b(X)}\ge\frac{(b-a)^2}8 ;
\tag{492.3}
$$

从而对每个固定 $\eta>0$，$C_{E_*}(X)\ne O\bigl(X^{1-b}(\log X)^{3-\eta}\bigr)$。

证明。(i)、(ii) 见引理 492.2 后的论证。映射 $E\mapsto\mathcal T^E_{\theta,1}$ 是线性的。令 $B_X(E,E')=\int_X^{2X}\mathcal T^E_{a,1}\mathcal T^{E'}_{b,1}\,\frac{dx}x$，它是双线性的（不必对称），$C_E(X)=B_X(E,E)$，且 $C_{E_0\pm F}=C_{E_0}\pm B_X(E_0,F)\pm B_X(F,E_0)+C_F$；两式相加得 $C_{E_0+F}+C_{E_0-F}-2C_{E_0}=2C_F$；因而 $\max\{|C_{E_0+F}(X)|,|C_{E_0-F}(X)|,|C_{E_0}(X)|\}\ge\frac12|C_F(X)|$。对序列 $X_n$ 应用有限集合上的抽屉原理，三者中有一个固定的函数在无穷多个 $n$ 上取到这个最大值。由引理 492.4 得 (492.3)。最后，$R_b(X)/\bigl(X^{1-b}(\log X)^{3-\eta}\bigr)=(\log X)^\eta/\log\log X\to\infty$。证毕。

**推论 492.6。** 任给满足 (492.1) 的局部有界可测 $E_0$，$E_0,E_0\pm F$ 中有一个函数满足 (492.1)，而其交叉项不满足 $O\bigl(X^{1-b}(\log X)^{3-\eta}\bigr)$（任意固定 $\eta>0$），也不满足 $O(X^{1-b}\log X)$；若 $E_0$ 另满足 $E_0(x)=O(\sqrt x\log^2x)$，该函数也满足此界。因此在 (492.1) 的接口下，定理 491.6(ii) 的上界 $X^{1-b}(\log X)^3$ 中 $X$ 的幂次不能普遍改进，总对数幂 $3$ 不能降低任何固定正数，形如 $C_E(X)\sim c(a,b)\,X^{1-b}\log X$ 的交叉主项定律不能由 (492.1) 单独推出。

**范围。** 定理 492.5 是关于抽象接口 (492.1) 的锐性结论，构造的 $E_*$ 一般不是 $\psi-\mathrm{id}$；它不给出算术情形 $E=\psi-\mathrm{id}$ 的交叉项下界，也不排除 $o\bigl(X^{1-b}(\log X)^3\bigr)$ 形式的非幂次改进。证明中的截断、Cauchy–Schwarz、凹性与二次恒等式都是标准工具，本节的新内容是三者的组合：保持整条指数带方差的扰动、端点尖峰的 $h\log^2(k/h)$ 交叉能量，以及它向原移动价格核的运输；由普通方差恢复协方差的极化方法见 Leung [Joint distribution of primes in multiple short intervals, Adv. Math. 490 (2026), 110847, doi:10.1016/j.aim.2026.110847] 附注 2.3。要对 $\psi-\mathrm{id}$ 得到交叉项主项，需要 (492.1) 之外能排除端点集中的信息，例如关于零点或素数分布的更细输入。

## 追加锚（本行以下为增补区）

## 493. 第四矩驱动的双侧正比例振荡

沿用 §490 的 $E,D_u,V,w,\rho_x,\mathcal T_{\theta,g},Q(g)$ 与 (490.2)。固定 $0<\alpha<\theta<\beta<1$。除 (490.2) 外，本节使用第四矩上界：存在常数 $C_4$，使对所有充分大的 $Y$，

$$
\sup_{Y^\alpha\le u\le Y^\beta}\frac{\int_1^Y|D_u(x)|^4\,dx}{Yu^2\log^2(Y/u)}\le C_4 .
\tag{493.1}
$$

由 Cauchy–Schwarz，$\int_1^YD_u^4\ge\frac1YV(Y,u)^2$，故在 (490.2) 下 (493.1) 只能在 $C_4\ge1$ 时成立。令 $h=X^\theta$、$f_s(x)=D_{sx^\theta}(x)$、$S_X=X^{1-\theta}\log X$，并在 $[X,2X]$ 上取概率测度 $d\mu_X=dx/(x\log2)$ 与 $Z_X=\mathcal T_{\theta,g}/\sqrt{S_X}$。

**引理 493.1（移动增量与 $L^1$ 剖面的第四矩）。** 设 (493.1)。则存在 $C$（只依赖 $\theta$ 与指数带），使对所有充分大的 $X$，

$$
\sup_{0\le s\le1}\int_X^{2X}|f_s(x)|^4\,dx\le C\,C_4\,X h^2\log^2X ,
\qquad
\int_X^{2X}|\mathcal T_{\theta,g}(x)|^4\,\frac{dx}x\le C\,C_4\,\|g\|_1^4\,S_X^2 .
$$

证明。令 $L_s(x)=sx^\theta$、$\phi_s(x)=x+L_s(x)$；在 $[X,2X]$ 上 $0\le L_s<2h$、$\phi_s'\ge1$。对 $v\in[3h,4h]$ 有恒等式 $f_s(x)=D_v(x)-D_{v-L_s(x)}(\phi_s(x))$（两个增量终点同为 $x+v$），故 $|f_s(x)|^4\le8\bigl(|D_v(x)|^4+|D_{v-L_s(x)}(\phi_s(x))|^4\bigr)$；对 $v\in[3h,4h]$ 取平均后对 $x$ 积分。第一部分：$v\asymp X^\theta$ 最终落在 $Y=3X$ 的指数带内，由 (493.1) 得 $\int_1^{3X}|D_v|^4\ll C_4Xh^2\log^2X$。第二部分作联合换元 $(x,v)\mapsto(y,w)=(\phi_s(x),\,v-L_s(x))$，其 Jacobian 为 $\phi_s'(x)\ge1$，像含于 $[X,3X]\times[h,4h]$；由 Tonelli，$\int_X^{2X}\!\int_{3h}^{4h}|D_{v-L_s(x)}(\phi_s(x))|^4\,dv\,dx\le\int_h^{4h}\!\int_1^{3X}|D_w(y)|^4\,dy\,dw\ll C_4Xh^3\log^2X$。两部分除以 $h$ 即得第一式，对 $s$ 一致。

对第二式，令 $G=\|g\|_1>0$，$F_g(x)=\int_0^1g(s)f_s(x)\rho_x(sx^\theta)\,ds$。由 $0<\rho\le1$ 与关于概率测度 $|g(s)|ds/G$ 的 Jensen 不等式，$|F_g(x)|^4\le G^3\int_0^1|g(s)|\,|f_s(x)|^4\,ds$；对 $x$ 积分并用第一式得 $\int_X^{2X}|F_g|^4\ll C_4G^4Xh^2\log^2X$。又 $\mathcal T_{\theta,g}=x^{1/2-\theta}F_g$，故 $\int_X^{2X}|\mathcal T_{\theta,g}|^4\,dx/x\ll X^{1-4\theta}\int_X^{2X}|F_g|^4\ll C_4G^4S_X^2$。证毕。

**引理 493.2（移动价格核的一阶均值消失）。** 设 (490.2)，取固定 $\theta<\nu<\beta$。则对每个实值 $g\in L^1(0,1)$，

$$
\int_X^{2X}\mathcal T_{\theta,g}(x)\,\frac{dx}x\ll\|g\|_1\sqrt{\log X}\,\bigl(X^{(1-\nu)/2}+X^{(\nu-\theta)/2}\bigr)=o\bigl(\sqrt{S_X}\bigr).
$$

证明。令 $M=X^\nu$、$\mathscr A_Mf(x)=\frac1M\int_0^Mf(x+r)\,dr$。由引理 491.2，$\|\mathscr A_Mf_s\|_{L^2[X,2X]}\ll\frac hM\sqrt{X\log X}\sqrt M$；由引理 491.1，$\|f_s\|_2\ll\sqrt{X\log X}\sqrt h$；两者对 $s\in[0,1]$ 一致。令 $P_s(t)=\int_X^tf_s$（$X\le t\le2X$）。由 Fubini，$\int_X^t\mathscr A_Mf_s=\frac1M\int_0^M\int_{X+r}^{t+r}f_s$，它与 $P_s(t)$ 只相差长度至多 $M$ 的两个端点条；故由 Cauchy–Schwarz，

$$
|P_s(t)|\le\sqrt X\,\|\mathscr A_Mf_s\|_2+2\sqrt M\,\|f_s\|_2\ll\sqrt{\log X}\,\Bigl(\frac{X\,h}{\sqrt M}+\sqrt{XhM}\Bigr),
$$

对 $t$ 与 $s$ 一致。令 $q_s(x)=x^{-1/2-\theta}\rho_x(sx^\theta)$。由 §481 的显式 $w$，$(\log w)'=O(x^{-1})$、$(\log w)''=O(x^{-2})$，从而（与定理 491.6 的证明相同）对 $s\in[0,1]$ 一致地 $q_s=O(X^{-1/2-\theta})$、$q_s'=O(X^{-3/2-\theta})$，故 $|q_s(2X)|+\int_X^{2X}|q_s'|\ll X^{-1/2-\theta}$。分部积分给出 $\bigl|\int_X^{2X}q_sf_s\bigr|\le\sup_t|P_s(t)|\bigl(|q_s(2X)|+\int_X^{2X}|q_s'|\bigr)\ll\sqrt{\log X}\bigl(X^{(1-\nu)/2}+X^{(\nu-\theta)/2}\bigr)$。由于 $\int_X^{2X}\mathcal T_{\theta,g}\,\frac{dx}x=\int_0^1g(s)\int_X^{2X}q_sf_s\,dx\,ds$（$E$ 局部有界，Fubini 成立），得第一式；除以 $\sqrt{S_X}$ 为 $O\bigl(X^{-(\nu-\theta)/2}+X^{-(1-\nu)/2}\bigr)=o(1)$。证毕。

**定理 493.3（双侧正比例振荡）。** 设 $E$ 局部有界 Borel 可测，(490.2) 与 (493.1) 在指数带 $\alpha<\theta<\beta$ 上成立，$g\in L^1(0,1)$ 实值且不几乎处处为零。令 $v=\frac12(2^{1-\theta}-1)Q(g)$，$K$ 为引理 493.1 给出的 $\sup_X\mathbb E_{\mu_X}Z_X^4$ 的上界（$K\ll C_4\|g\|_1^4$），

$$
K_1=8\Bigl(K+\frac{v^2}4\Bigr),\qquad \Lambda=\frac{(v/2)^{3/2}}{\sqrt{K_1}},\qquad c=\frac\Lambda8,\qquad \delta=\frac{\Lambda^2}{16\sqrt{K_1}} .
$$

则对所有充分大的 $X$，

$$
\mu_X\Bigl\{\mathcal T_{\theta,g}>c\sqrt{S_X}\Bigr\}\ge\delta,\qquad \mu_X\Bigl\{\mathcal T_{\theta,g}<-c\sqrt{S_X}\Bigr\}\ge\delta .
\tag{493.2}
$$

证明。由定理 490.6，$\mathbb EZ_X^2\to Q(g)(2^{1-\theta}-1)/\log2>2v$，且该定理的证明给出 $Q(g)>0$；故充分大时 $\mathbb E Z_X^2\ge v>0$（$\mathbb E=\mathbb E_{\mu_X}$）；由引理 493.1，$\mathbb EZ_X^4\le K$；由引理 493.2，$\varepsilon_X=|\mathbb EZ_X|\to0$，故充分大时 $\varepsilon_X\le\min\{\sqrt{v/2},\Lambda/8\}$。以下是经典的 Paley–Zygmund 型论证。令 $W=Z_X-\mathbb EZ_X$，则 $\mathbb EW=0$，$\mathbb EW^2\ge v-\varepsilon_X^2\ge v/2$，$\mathbb EW^4\le8(\mathbb EZ_X^4+\varepsilon_X^4)\le K_1$。由插值不等式 $\mathbb EW^2\le(\mathbb E|W|)^{2/3}(\mathbb EW^4)^{1/3}$，$\mathbb E|W|\ge\Lambda$；又 $\mathbb EW=0$ 给出 $\mathbb EW_+=\mathbb EW_-=\frac12\mathbb E|W|\ge\Lambda/2$。取 $a=\Lambda/4$，由 $\mathbb EW_+\le a+(\mathbb EW_+^2)^{1/2}\mu_X(W>a)^{1/2}$ 与 $\mathbb EW_+^2\le\mathbb EW^2\le\sqrt{K_1}$，得 $\mu_X(W>\Lambda/4)\ge\delta$；同理 $\mu_X(W<-\Lambda/4)\ge\delta$。最后 $|\mathbb EZ_X|\le\Lambda/8$，故 $W>\Lambda/4\Rightarrow Z_X>c$、$W<-\Lambda/4\Rightarrow Z_X<-c$。证毕。

**推论 493.4（条件算术形式）。** 记 $M_K(N;H)=\sum_{n\le N}(\psi(n+H)-\psi(n)-H)^K$。设 Montgomery–Soundararajan [Primes in short intervals, Comm. Math. Phys. 252 (2004), 589–617] 猜想 1 在 $K=2,4$ 时成立：对固定 $\varepsilon>0$，$M_K(N;H)=(\mu_K+o(1))\,N\,(H\log(N/H))^{K/2}$（$\mu_2=1$、$\mu_4=3$）对 $(\log N)^{1+\varepsilon}\le H\le N^{1-\varepsilon}$ 一致成立。则对 $E=\psi-\mathrm{id}$、任意 $0<\alpha<\theta<\beta<1$ 与任意不几乎处处为零的实值 $g\in L^1(0,1)$，(493.2) 成立。

证明。给定 $\alpha,\beta$ 后取 $0<\varepsilon<\min\{\alpha,1-\beta\}$（猜想中的 $H$ 为正整数），则 $Y^\alpha-1\le H\le Y^\beta$ 最终落在猜想的范围内。对 $1\le x\le Y$、$u\in[Y^\alpha,Y^\beta]$，令 $n=\lfloor x\rfloor$、$H=\lfloor u\rfloor$；左端点相差不到 $1$，右端点相差不到 $2$，故 $D_u(x)-D_H(n)$ 是区间长度至多 $2$ 上的 $\psi$ 增量与 $O(1)$ 线性项之差，$|D_u(x)-D_H(n)|\ll\log(3Y)$。于是 $\int_1^Y|D_u|^4\le8\sum_{n\le Y}|D_H(n)|^4+O(Y\log^4Y)$，由 $K=4$ 的情形得 (493.1)（粗略不等式 $|a+b|^4\le8(|a|^4+|b|^4)$ 使任意固定 $C_4>8\mu_4=24$ 均可；$Y\log^4Y=o(YH^2\log^2(Y/H))$ 因 $H\ge Y^\alpha$）。同一桥接在 $L^2$ 中给出 $\bigl|\sqrt{V(Y,u)}-\sqrt{\sum_{n\le Y}D_H(n)^2}\bigr|\ll\sqrt Y\log Y=o\bigl(\sqrt{YH\log(Y/H)}\bigr)$，再由 $K=2$ 的情形与 $H\log(Y/H)\sim u\log(Y/u)$ 得 (490.2)。$E=\psi-\mathrm{id}$ 局部有界可测。由定理 493.3 得结论。证毕。

**推论 493.5（原前向价格核）。** 在推论 493.4 的假设下，取 $\theta=4/5$、$g\equiv1$（$Q(1)=1/3$）：存在 $c,\delta>0$，使对所有充分大的 $X$，$[X,2X]$ 中 $\mathcal T(x)>cx^{1/10}\sqrt{\log x}$ 的点集与 $\mathcal T(x)<-cx^{1/10}\sqrt{\log x}$ 的点集的 $dx/x$ 测度都至少 $\delta$（由 $dx/x=(\log2)\,d\mu_X$，将定理 493.3 的 $\delta$ 换为 $\delta\log2$）。换算到 (481.1) 的价格量即 $T_\psi(x,x^{4/5})=x^{11/10}\mathcal T(x)$，两侧各在每个充分大二倍区间中占正比例，特别地 $T_\psi(x,x^{4/5})=\Omega_\pm\bigl(x^{6/5}\sqrt{\log x}\bigr)$。

证明。$\mathcal T_{4/5,1}=\mathcal T$；在 $[X,2X]$ 上 $\log X\le\log x\le\log X+\log2$、$x^{1/10}\le2^{1/10}X^{1/10}$，减小 $c$ 即把阈值 $c\sqrt{S_X}$ 换成 $cx^{1/10}\sqrt{\log x}$。证毕。

**范围。** 推论 493.4–493.5 以 Montgomery–Soundararajan 猜想 1 的 $K=2,4$ 情形为条件；该文定理 3 另以强相关估计 (20) 为条件；对 $K=4$ 的长度范围至多为 $H\le N^{1/4}$，不覆盖推论 493.5 所需的 $H\asymp N^{4/5}$。Goldston–Yıldırım [Higher correlations of divisor sums related to primes II: variations of the error term in the prime number theorem, Proc. London Math. Soc. 95 (2007), 199–247] 定理 3 在 GRH 下对 $\log^{14}N\ll h\ll N^{1/7-\varepsilon}$ 的固定长度 $h$ 给出两个符号的存在性；Kaczorowski–Pintz [Oscillatory properties of arithmetical functions. I, Acta Math. Hungar. 48 (1986), 173–185；II, 49 (1987), 441–453] 研究算术函数余项的振荡与变号，不给出这里每个充分大二倍区间中的正比例结论。对固定长度，由足够强的 Montgomery–Soundararajan 矩渐近推出两侧正比例是第二、第四矩配合 Paley–Zygmund 论证的直接推论；本节的区别在于移动长度 $sx^\theta$、任意实值 $L^1$ 剖面与原价格权，并且只用第四矩上界 (493.1) 与方差渐近 (490.2)，给出每个充分大二倍区间中两侧的统一正比例。de la Bretèche–Fiorilli [On a conjecture of Montgomery and Soundararajan, Math. Ann. 381 (2021), 575–591] 给出加权偶矩下界，不提供这里所需的第四矩上界 (493.1)。定理 493.3 不给出渐近正态性或随机过程意义下的收敛。

## 追加锚（本行以下为增补区）

## 494. 固定二倍区间归一化下的矩传递与正超额峰度

沿用 §490 的 $E,D_u,\rho_x,\mathcal T_{\theta,g},Q(g),S_X$ 与 §493 的概率测度 $d\mu_X=dx/(x\log2)$（$[X,2X]$ 上）及 $Z_X=\mathcal T_{\theta,g}/\sqrt{S_X}$。固定 $0<\theta<1$，令

$$
\kappa=1-\theta,\qquad r=\frac\kappa2,\qquad U_X(x)=\frac xX,\qquad
B_X(s,x)=\frac{D_{sx^\theta}(x)}{\sqrt{x^\theta\log x}}\quad(0\le s\le1,\ X\le x\le2X).
$$

由 $E$ 的 Borel 可测性，$(s,x)\mapsto B_X(s,x)$ 联合 Borel 可测。对整数 $k\ge1$，记 $c_k=\int_1^2u^{kr}\frac{du}{u\log2}=\dfrac{2^{kr}-1}{kr\log2}$。

**$k$ 阶矩接口。** 称 $E$ 满足 $(\mathrm M_k)$，若

(a) 存在 $C_k$，使对充分大的 $X$，$\sup_{0\le s\le1}\mathbb E_{\mu_X}|B_X(s)|^k\le C_k$；

(b) 对每个 $\mathbf s=(s_1,\dots,s_k)\in[0,1]^k$，极限

$$
M_k(\mathbf s)=\lim_{X\to\infty}\mathbb E_{\mu_X}\Bigl[U_X^{kr}\prod_{j=1}^kB_X(s_j)\Bigr]
\tag{494.1}
$$

存在。

$M_k$ 作为可测函数的逐点极限是可测的；由 (a) 与 Hölder 不等式，$\bigl|\mathbb E_{\mu_X}[U_X^{kr}\prod_jB_X(s_j)]\bigr|\le2^{kr}\prod_j(\mathbb E|B_X(s_j)|^k)^{1/k}\le2^{kr}C_k$，故 $|M_k|\le2^{kr}C_k$。

**定理 494.1（矩传递）。** 设 $E$ 局部有界 Borel 可测且满足 $(\mathrm M_k)$，$g\in L^1(0,1)$ 实值。则

$$
\lim_{X\to\infty}\mathbb E_{\mu_X}Z_X^k=\int_{[0,1]^k}\Bigl(\prod_{j=1}^kg(s_j)\Bigr)M_k(\mathbf s)\,d\mathbf s .
\tag{494.2}
$$

证明。由 (490.1)，

$$
Z_X(x)=U_X(x)^r\,L_X(x)\int_0^1g(s)B_X(s,x)\rho_x(sx^\theta)\,ds,\qquad L_X(x)=\sqrt{\frac{\log x}{\log X}} .
$$

在 $[X,2X]$ 上 $1\le L_X\le\sqrt{1+\log2/\log X}$；由 §481 的显式 $w$，$1-4u/x\le\rho_x(u)\le1$（$0\le u\le x^\theta$，$x$ 充分大），故 $\eta_X=\sup_{x,s}\bigl|L_X(x)\rho_x(sx^\theta)-1\bigr|\to0$。展开 $k$ 次方并对 $(s_1,\dots,s_k)$ 用 Fubini，

$$
\mathbb E_{\mu_X}Z_X^k=\int_{[0,1]^k}\Bigl(\prod_jg(s_j)\Bigr)\,\mathbb E_{\mu_X}\Bigl[U_X^{kr}\prod_j\bigl(L_X\rho_x(s_jx^\theta)\bigr)B_X(s_j)\Bigr]d\mathbf s ,
$$

Fubini 的合法性由 $\int_{[0,1]^k}\prod_j|g(s_j)|\,\mathbb E_{\mu_X}\bigl[U_X^{kr}\prod_j|L_X\rho_x(s_jx^\theta)|\,|B_X(s_j)|\bigr]d\mathbf s\le2^{kr}(1+\eta_X)^kC_k\|g\|_1^k<\infty$ 给出（Hölder 不等式同上）。把每个因子 $L_X\rho_x(s_jx^\theta)$ 换成 $1$ 的误差逐点至多 $\bigl((1+\eta_X)^k-1\bigr)U_X^{kr}\prod_j|B_X(s_j)|$，积分后至多 $\bigl((1+\eta_X)^k-1\bigr)2^{kr}C_k\|g\|_1^k\to0$。余下 $\int\prod_jg(s_j)\,\mathbb E_{\mu_X}[U_X^{kr}\prod_jB_X(s_j)]\,d\mathbf s$：被积函数逐点收敛到 $\prod_jg(s_j)M_k(\mathbf s)$，且受可积函数 $2^{kr}C_k\prod_j|g(s_j)|$ 控制；由控制收敛定理得 (494.2)。证毕。

**Brownian 接口。** 对偶数 $k=2m$，令 $\mathcal P_k$ 为 $\{1,\dots,k\}$ 的全部完美配对（共 $(k-1)!!$ 个），并令

$$
W_k(\mathbf s)=\sum_{\pi\in\mathcal P_k}\ \prod_{\{i,j\}\in\pi}\min(s_i,s_j),\qquad W_k=0\ (k\ \text{奇}).
$$

由 Isserlis（Wick）公式，$W_k(\mathbf s)=\mathbb E\prod_jB(s_j)$，$B$ 为标准 Brownian 运动。称 $E$ 满足 Brownian 型 $(\mathrm M_k)$，若 $(\mathrm M_k)$ 成立且 $M_k=c_k\kappa^{k/2}W_k$。

**定理 494.2（固定二倍区间归一化的正超额峰度）。** 设 $E$ 局部有界 Borel 可测，(490.2) 与 (493.1) 在指数带 $\alpha<\theta<\beta$ 上成立，且对每个 $\mathbf s\in[0,1]^4$，

$$
\lim_{X\to\infty}\mathbb E_{\mu_X}\Bigl[U_X^{2\kappa}\prod_{j=1}^4B_X(s_j)\Bigr]=c_4\kappa^2\,W_4(\mathbf s),\qquad c_4=\frac{2^{2\kappa}-1}{2\kappa\log2} .
\tag{494.3}
$$

则对每个实值 $g\in L^1(0,1)$，

$$
\lim_{X\to\infty}\mathbb E_{\mu_X}Z_X^2=\frac{(2^\kappa-1)\,Q(g)}{\log2},\qquad
\lim_{X\to\infty}\mathbb E_{\mu_X}Z_X^4=\frac{3\kappa\,(2^{2\kappa}-1)\,Q(g)^2}{2\log2} .
\tag{494.4}
$$

若 $g$ 不几乎处处为零，令 $a=\kappa\log2$，则

$$
\frac{\lim_X\mathbb E_{\mu_X}Z_X^4}{\bigl(\lim_X\mathbb E_{\mu_X}Z_X^2\bigr)^2}=3\cdot\frac a2\coth\frac a2>3 .
\tag{494.5}
$$

证明。第一式是定理 490.6 除以 $\log2$。对第二式验证 $(\mathrm M_4)$：(b) 即 (494.3)；(a) 由引理 493.1 的第一式得到——在 $[X,2X]$ 上 $x^\theta\log x\ge X^\theta\log X$，故

$$
\mathbb E_{\mu_X}|B_X(s)|^4\le\frac{1}{\log2}\cdot\frac{1}{X\,(X^\theta\log X)^2}\int_X^{2X}|D_{sx^\theta}(x)|^4\,dx\ll C_4 ,
$$

对 $s\in[0,1]$ 一致。由定理 494.1（$k=4$），$\lim\mathbb E Z_X^4=c_4\kappa^2\int_{[0,1]^4}\prod_jg(s_j)W_4(\mathbf s)\,d\mathbf s$。对 $W_4$ 的每个配对 $\pi$，由 $0\le\min\le1$ 与 $g\in L^1$ 得绝对可积性，再由 Fubini，$\int\prod_jg(s_j)\prod_{\{i,j\}\in\pi}\min(s_i,s_j)\,d\mathbf s=Q(g)^2$；三个配对给出 $3Q(g)^2$（这是 Isserlis 公式对 $\int_0^1g(s)B(s)\,ds$ 的计算），即 (494.4) 第二式。若 $g$ 不几乎处处为零，则 $Q(g)>0$（定理 490.6 的证明），比值为

$$
\frac{3\kappa(2^{2\kappa}-1)\log2}{2(2^\kappa-1)^2}=\frac{3a\,(e^a+1)}{2(e^a-1)}=3\cdot\frac a2\coth\frac a2 ,
$$

而 $y\coth y>1$（$y>0$）等价于 $\tanh y<y$。证毕。

若 $g$ 不几乎处处为零，(494.5) 说明 (494.3) 下 $Z_X$ 的二阶、四阶矩极限不是任何中心高斯分布的矩：中心高斯变量的四阶矩恰为二阶矩平方的 $3$ 倍。超额峰度 $3\bigl(\frac a2\coth\frac a2-1\bigr)$ 只依赖 $\theta$，与剖面 $g$ 无关；它是尺度混合的一般机制的显式值：对独立的标准高斯 $N$ 与满足 $\mathbb E\sigma^4<\infty$ 的非常数正尺度 $\sigma$，$\mathbb E(\sigma N)^4/(\mathbb E(\sigma N)^2)^2-3=3\operatorname{Var}(\sigma^2)/(\mathbb E\sigma^2)^2>0$（Andrews–Mallows [Scale mixtures of normal distributions, J. Roy. Statist. Soc. B 36 (1974), 99–102]），这里尺度为 $U^r$。由关于概率测度 $|g(s)|ds/\|g\|_1$ 的 Jensen 不等式，$\sup_{X\ge X_0}\mathbb E_{\mu_X}|Z_X|^4\le\sup_{X\ge X_0}2^{4r}(1+\eta_X)^4C_4\|g\|_1^4<\infty$（$C_4$ 为 $k=4$ 时 (a) 的常数），故 $\mathbb E[Z_X^2\mathbf 1_{\{Z_X^2>R\}}]\le\mathbb EZ_X^4/R$，$\{Z_X^2\}_{X\ge X_0}$ 一致可积（$X_0$ 充分大），任何分布极限的二阶矩等于 (494.4) 的第一式；若再有 $Z_X^4$ 的一致可积性，即可由上述矩比较排除高斯分布极限。推论 494.3 在完整接口下给出极限分布。

**推论 494.3（尺度混合极限）。** 设对每个 $k\ge1$，Brownian 型 $(\mathrm M_k)$ 成立。令 $U$ 在 $[1,2]$ 上有密度 $1/(u\log2)$，$G\sim N(0,\kappa Q(g))$ 与 $U$ 独立。则对每个 $k$，$\mathbb E_{\mu_X}Z_X^k\to\mathbb E\,(U^rG)^k$；$Z_X$ 依分布收敛到 $U^rG$，其特征函数为

$$
\lim_{X\to\infty}\mathbb E_{\mu_X}e^{itZ_X}=\frac1{\log2}\int_1^2\exp\Bigl(-\frac{t^2\kappa Q(g)}2\,u^{\kappa}\Bigr)\frac{du}u ;
\tag{494.6}
$$

若 $g$ 不几乎处处为零，则 $\mu_X\{Z_X>0\}\to\frac12$，$\mu_X\{Z_X<0\}\to\frac12$。

证明。偶数 $k$ 时，与定理 494.2 的证明相同，对 $W_k$ 的每个配对用 Fubini 得 $Q(g)^{k/2}$，配对数为 $(k-1)!!$（Isserlis 公式），故由定理 494.1，$\lim\mathbb E Z_X^k=c_k\kappa^{k/2}(k-1)!!\,Q(g)^{k/2}=\mathbb E U^{kr}\cdot\mathbb E G^k=\mathbb E(U^rG)^k$；奇数阶两边都为 $0$。在 $U$ 上取条件期望，$\mathbb Ee^{tU^rG}=\mathbb E\exp\bigl(\frac{t^2\kappa Q(g)}2U^{2r}\bigr)\le\exp\bigl(\frac{t^2\kappa Q(g)}22^{2r}\bigr)$，故 $U^rG$ 的分布由矩唯一确定。对任意 $X_n\to\infty$，由矩方法（Billingsley, Probability and Measure, 3rd ed., Theorem 30.2）得 $Z_{X_n}$ 依分布收敛到 $U^rG$，从而 $Z_X$ 依分布收敛。(494.6) 由在 $U$ 上取条件期望得到。若 $Q(g)>0$，$U^rG$ 关于 $0$ 对称且 $\mathbb P(U^rG=0)=0$，故 $(0,\infty)$ 与 $(-\infty,0)$ 都是极限分布的连续集，其概率都是 $\frac12$，由 portmanteau 定理得结论。证毕。

**范围。** 定理 494.1、494.2 与推论 494.3 是抽象接口上的结论；对 $E=\psi-\mathrm{id}$，(494.3) 与推论 494.3 所需的 Brownian 型接口都未被证明。Montgomery–Soundararajan [Primes in short intervals, Comm. Math. Phys. 252 (2004), 589–617] 猜想 1 关于固定加法长度 $H=H(N)$、$n\le N$ 变动时的单长度矩，不直接提供 (494.3)：后者涉及四个不同移动长度 $s_jx^\theta$ 的混合矩及其与宏观位置 $U_X$ 的渐近独立性。Leung [Joint distribution of primes in multiple short intervals, Adv. Math. 490 (2026), 110847] 在 RH 与 LI 下研究比例长度 $\delta x$ 的多个不交区间，采用对数取样 $\frac1{\log X}\int_2^X(\cdots)\frac{dx}x$，得到 $\delta\to0$ 时的高斯近似；其单个移动区间的结果另设 QLI，取 $\log x$ 在 $[U,2U]$ 上均匀分布、$\delta=o(1)$ 且 $\log(1/\delta)=o(\log U)$（该文定理 10.1）。两者的取样都不是本节 $[X,2X]$ 上的 $dx/(x\log2)$，长度也不是幂次 $x^\theta$，且都不处理移动价格核。本节的新内容限于：带宏观权 $U_X^{kr}$ 的矩传递对任意实值 $L^1$ 剖面与原价格权成立，以及由此得到的显式常数 (494.4)–(494.6)；尺度混合本身是经典机制。矩方法、Isserlis 公式与 Hölder、Fubini、控制收敛都是标准工具。

## 追加锚（本行以下为增补区）

## 495. 不同指数的联合矩：交叉核的消失与平方的正相关

沿用 §494 的 $\mu_X,U_X,c_k$ 与记号。固定 $0<\theta_1<\theta_2<1$、实值 $g_1,g_2\in L^1(0,1)$，令 $\kappa_i=1-\theta_i$、$r_i=\kappa_i/2$、$Q_i=Q(g_i)$，

$$
B_{i,X}(s,x)=\frac{D_{sx^{\theta_i}}(x)}{\sqrt{x^{\theta_i}\log x}},\qquad
Z_{i,X}=\frac{\mathcal T_{\theta_i,g_i}}{\sqrt{X^{1-\theta_i}\log X}}\qquad(i=1,2).
$$

对整数 $p,q\ge0$、$k=p+q\ge1$，令 $i_\ell=1$（$\ell\le p$）、$i_\ell=2$（$\ell>p$），$\gamma_{p,q}=pr_1+qr_2$，$c_{p,q}=\int_1^2u^{\gamma_{p,q}}\frac{du}{u\log2}$。

**联合矩接口。** 称 $E$ 满足 $(\mathrm J_{p,q})$，若

(a) 存在 $C$，使对充分大的 $X$，$\sup_{i=1,2}\sup_{0\le s\le1}\mathbb E_{\mu_X}|B_{i,X}(s)|^k\le C$；

(b) 对每个 $\mathbf s\in[0,1]^k$，极限

$$
M_{p,q}(\mathbf s)=\lim_{X\to\infty}\mathbb E_{\mu_X}\Bigl[U_X^{\gamma_{p,q}}\prod_{\ell=1}^kB_{i_\ell,X}(s_\ell)\Bigr]
\tag{495.1}
$$

存在。

与 §494 相同，$M_{p,q}$ 可测且 $|M_{p,q}|\le2^{\gamma_{p,q}}C$。$q=0$ 时 $(\mathrm J_{p,0})$ 蕴含 $\theta=\theta_1$ 的 $(\mathrm M_p)$，二者的极限核相同（(a) 对两个指数都要求矩界，故 $(\mathrm J_{p,0})$ 更强）。

**引理 495.1（联合矩传递）。** 设 $E$ 局部有界 Borel 可测且满足 $(\mathrm J_{p,q})$。则

$$
\lim_{X\to\infty}\mathbb E_{\mu_X}\bigl[Z_{1,X}^pZ_{2,X}^q\bigr]=\int_{[0,1]^k}\Bigl(\prod_{\ell=1}^kg_{i_\ell}(s_\ell)\Bigr)M_{p,q}(\mathbf s)\,d\mathbf s .
\tag{495.2}
$$

证明。对每个因子用定理 494.1 证明中的表示 $Z_{i,X}=U_X^{r_i}L_X\int_0^1g_i(s)B_{i,X}(s)\rho_x(sx^{\theta_i})\,ds$，宏观因子之积为 $U_X^{\gamma_{p,q}}$。令 $\eta_X=\max_{i=1,2}\sup_{x,s}|L_X(x)\rho_x(sx^{\theta_i})-1|$；由 $1\le L_X\le\sqrt{1+\log2/\log X}$ 与 $1-4u/x\le\rho_x(u)\le1$，$\eta_X=O\bigl((\log X)^{-1}+X^{\theta_2-1}\bigr)\to0$。其余各步——Fubini 的合法性（广义 Hölder 不等式给出 $\mathbb E_{\mu_X}[U_X^{\gamma_{p,q}}\prod_\ell|B_{i_\ell,X}(s_\ell)|]\le2^{\gamma_{p,q}}C$）、把价格因子换成 $1$ 的误差 $((1+\eta_X)^k-1)2^{\gamma_{p,q}}C\prod_\ell\|g_{i_\ell}\|_1$、控制收敛——与定理 494.1 的证明逐行相同。证毕。

**定理 495.2（交叉二阶核的消失）。** 设 $E$ 局部有界 Borel 可测，(490.2) 分别在 $0<\alpha_1<\theta_1<\beta_1<1$ 与 $0<\alpha_2<\theta_2<\beta_2<1$ 上成立，且 $(\mathrm J_{1,1})$(b) 成立。则

$$
\int_0^1\!\!\int_0^1g_1(s)g_2(t)\,M_{1,1}(s,t)\,ds\,dt=0\qquad(\text{对一切实值 }g_1,g_2\in L^1(0,1)),
\tag{495.3}
$$

从而 $M_{1,1}=0$ 在 $[0,1]^2$ 上几乎处处成立。

证明。先验证 $(\mathrm J_{1,1})$(a)：$R=X^{\theta_i}$ 满足 (491.1)，由引理 491.1（取 $p(x)=x$、$q(x)=x+sx^{\theta_i}$），对 $i=1,2$ 与 $s\in[0,1]$ 一致地 $\int_X^{2X}D_{sx^{\theta_i}}(x)^2\,dx\ll X^{1+\theta_i}\log X$，而在 $[X,2X]$ 上 $x^{\theta_i}\log x\ge X^{\theta_i}\log X$、$1/x\le1/X$，故 $\mathbb E_{\mu_X}|B_{i,X}(s)|^2\ll1$。由引理 495.1，$\mathbb E_{\mu_X}[Z_{1,X}Z_{2,X}]$ 收敛到 (495.3) 左边。另一方面

$$
\mathbb E_{\mu_X}[Z_{1,X}Z_{2,X}]=\frac1{\log2}\cdot\frac1{N_X}\int_X^{2X}\mathcal T_{\theta_1,g_1}\mathcal T_{\theta_2,g_2}\frac{dx}x,\qquad N_X=X^{1-(\theta_1+\theta_2)/2}\log X ,
$$

由定理 491.6(i)（取 $a=\theta_1$、$b=\theta_2$，并取 $\mu,\nu$ 为 $\theta_1$ 到 $\min(\beta_1,\theta_2)$ 之间的三等分点）它是 $O(X^{-\eta_0})\to0$。这给出 (495.3)。取 $g_1,g_2$ 为区间的示性函数，$M_{1,1}$ 在每个矩形 $[a_1,b_1]\times[a_2,b_2]\subset[0,1]^2$ 上的积分为零；$M_{1,1}$ 有界可测，故有限带号测度 $M_{1,1}\,ds\,dt$ 在生成 $[0,1]^2$ 的 Borel $\sigma$-代数的矩形 $\pi$-系上为零，由 Dynkin $\pi$-$\lambda$ 定理它为零测度，即 $M_{1,1}=0$ 几乎处处。证毕。

因此在 (490.2) 下，两个不同指数的 Brownian 型联合接口中，交叉协方差核只能是零：不同指数的局部增量过程在宏观加权下渐近不相关这一事实不是附加假设，而是 §491 的推论。

**Brownian 型联合四阶接口。** 设 $C:[0,1]^2\to\mathbb R$ 有界可测，称 $E$ 满足以 $C$ 为交叉核的 $(\mathrm W_{2,2})$，若 $(\mathrm J_{1,1})$(b) 以 $M_{1,1}=c_{1,1}C$ 成立，且 $(\mathrm J_{2,2})$(b) 以

$$
M_{2,2}(s_1,s_2,t_1,t_2)=c_{2,2}\Bigl[\kappa_1\kappa_2\min(s_1,s_2)\min(t_1,t_2)+C(s_1,t_1)C(s_2,t_2)+C(s_1,t_2)C(s_2,t_1)\Bigr]
\tag{495.4}
$$

成立（变量顺序 $(s_1,s_2)$ 对应 $\theta_1$，$(t_1,t_2)$ 对应 $\theta_2$）。这是二维 Gauss 过程 $(\sqrt{\kappa_1}B^{(1)},\sqrt{\kappa_2}B^{(2)})$ 在交叉协方差为 $C$ 时的四阶 Isserlis 公式乘以宏观因子 $c_{2,2}$。

**定理 495.3（不同指数的平方正相关）。** 设 $E$ 局部有界 Borel 可测，(490.2) 与 (493.1) 分别在包含 $\theta_1$ 与 $\theta_2$ 的指数带上成立，且 $E$ 满足以某个有界可测 $C$ 为交叉核的 $(\mathrm W_{2,2})$。则

$$
\lim_{X\to\infty}\mathbb E_{\mu_X}[Z_{1,X}Z_{2,X}]=0,\qquad
\lim_{X\to\infty}\mathbb E_{\mu_X}[Z_{1,X}^2Z_{2,X}^2]=c_{2,2}\,\kappa_1\kappa_2\,Q_1Q_2 ,
\tag{495.5}
$$

其中 $c_{2,2}=\dfrac{2^{\kappa_1+\kappa_2}-1}{(\kappa_1+\kappa_2)\log2}$；并且

$$
\lim_{X\to\infty}\Bigl(\mathbb E_{\mu_X}[Z_{1,X}^2Z_{2,X}^2]-\mathbb E_{\mu_X}Z_{1,X}^2\,\mathbb E_{\mu_X}Z_{2,X}^2\Bigr)=\kappa_1\kappa_2\,Q_1Q_2\,\bigl(c_{2,2}-c_{2,0}\,c_{0,2}\bigr),
\tag{495.6}
$$

其中 $c_{2,0}=\frac{2^{\kappa_1}-1}{\kappa_1\log2}$、$c_{0,2}=\frac{2^{\kappa_2}-1}{\kappa_2\log2}$，且 $c_{2,2}>c_{2,0}c_{0,2}$。特别地，若 $g_1,g_2$ 都不几乎处处为零，则 (495.6) 的极限严格为正。

证明。第一式由定理 495.2 的证明得到。对第二式验证 $(\mathrm J_{2,2})$(a)：由引理 493.1 的第一式（对两条指数带分别使用），与定理 494.2 的证明相同，$\sup_{i,s}\mathbb E_{\mu_X}|B_{i,X}(s)|^4\ll\max(C_4^{(1)},C_4^{(2)})$。由引理 495.1，$\lim\mathbb E[Z_{1,X}^2Z_{2,X}^2]=\int\prod g\cdot M_{2,2}$。对 (495.4) 的三项分别用 Fubini：第一项给出 $\kappa_1\kappa_2Q_1Q_2$；后两项各为 $\bigl(\iint g_1(s)g_2(t)C(s,t)\,ds\,dt\bigr)^2$。由 $(\mathrm J_{1,1})$(b) 与定理 495.2，$c_{1,1}\iint g_1g_2C=\iint g_1g_2M_{1,1}=0$，而 $c_{1,1}>0$，故后两项为零，得 (495.5) 第二式；可积性由 $C$ 有界与 $g_i\in L^1$ 给出。由定理 490.6，$\lim\mathbb EZ_{i,X}^2=\frac{(2^{\kappa_i}-1)Q_i}{\log2}=c_{2,0}\kappa_1Q_1$（$i=1$）与 $c_{0,2}\kappa_2Q_2$（$i=2$），得 (495.6)。最后，令 $U$ 在 $[1,2]$ 上有密度 $1/(u\log2)$，$U'$ 为其独立复制，$f(u)=u^{\kappa_1}$、$h(u)=u^{\kappa_2}$ 都严格递增，则

$$
c_{2,2}-c_{2,0}c_{0,2}=\mathbb E[f(U)h(U)]-\mathbb Ef(U)\,\mathbb Eh(U)=\tfrac12\,\mathbb E\bigl[(f(U)-f(U'))(h(U)-h(U'))\bigr]>0 ,
$$

因为被积函数在 $U\ne U'$ 时严格为正，而 $\mathbb P(U\ne U')=1$（Chebyshev 积分不等式的严格形式；该不等式见 Hardy–Littlewood–Pólya, Inequalities, Cambridge 1934, 定理 236）。若 $g_i$ 都不几乎处处为零，则 $Q_1,Q_2>0$（定理 490.6 的证明）。证毕。

若 $g_1,g_2$ 都不几乎处处为零，则在 $(\mathrm W_{2,2})$ 与 (490.2)、(493.1) 下，两个不同指数的归一化核渐近不相关，而它们的平方渐近正相关：$Z_{1,X},Z_{2,X}$ 的二阶、四阶联合矩极限不可能是两个独立随机变量的联合矩。正相关来自两者共享的宏观尺度 $U_X=x/X$，其大小 $\kappa_1\kappa_2Q_1Q_2(c_{2,2}-c_{2,0}c_{0,2})$ 只经 $\theta_1,\theta_2$ 依赖宏观取样。

**推论 495.4（符号的渐近独立）。** 设 (490.2) 分别在包含 $\theta_1$、$\theta_2$ 的指数带上成立，且对一切 $p,q\ge0$（$p+q\ge1$），$(\mathrm J_{p,q})$ 成立，其极限为二维 Brownian 型：$M_{p,q}=c_{p,q}\sum_{\pi}\prod_{\{a,b\}\in\pi}C_{i_ai_b}(s_a,s_b)$（对 $\{1,\dots,k\}$ 的全部完美配对 $\pi$ 求和，$k$ 奇时为零），其中 $C_{11}=\kappa_1\min$、$C_{22}=\kappa_2\min$、$C_{12}(s,t)=C_{21}(t,s)=C(s,t)$ 有界可测。若 $g_1,g_2$ 都不几乎处处为零，令 $U$ 如上，$G_i\sim N(0,\kappa_iQ_i)$，$U,G_1,G_2$ 相互独立。则 $(Z_{1,X},Z_{2,X})$ 依分布收敛到 $(U^{r_1}G_1,U^{r_2}G_2)$，且四个符号象限的 $\mu_X$-测度都趋于 $\frac14$：

$$
\lim_{X\to\infty}\mu_X\{\varepsilon_1Z_{1,X}>0,\ \varepsilon_2Z_{2,X}>0\}=\frac14\qquad(\varepsilon_1,\varepsilon_2\in\{\pm1\}).
\tag{495.7}
$$

证明。由 $(\mathrm J_{1,1})$ 与定理 495.2，$\iint g_1g_2C=0$。由引理 495.1，$\lim\mathbb E[Z_{1,X}^pZ_{2,X}^q]=c_{p,q}\sum_\pi\prod_{\{a,b\}\in\pi}\iint g_{i_a}g_{i_b}C_{i_ai_b}$（Fubini 把每个配对的积分分解为各对的积分之积）；含交叉对的配对贡献为零，余下为 $c_{p,q}(p-1)!!\,(\kappa_1Q_1)^{p/2}(q-1)!!\,(\kappa_2Q_2)^{q/2}$（$p,q$ 都为偶数，约定 $(-1)!!=1$），否则为 $0$。这正是 $\mathbb E\,U^{\gamma_{p,q}}\,\mathbb EG_1^p\,\mathbb EG_2^q=\mathbb E[(U^{r_1}G_1)^p(U^{r_2}G_2)^q]$。对实数 $a,b$，在 $U$ 上取条件，$aU^{r_1}G_1+bU^{r_2}G_2$ 是方差至多 $2^{2\max(r_1,r_2)}(a^2\kappa_1Q_1+b^2\kappa_2Q_2)$ 的中心高斯变量，故其矩生成函数处处有限，分布由矩确定。由一维矩方法（Billingsley, Probability and Measure, 3rd ed., Theorem 30.2）与 Cramér–Wold 定理（同书 Theorem 29.4），沿任意 $X_n\to\infty$ 依分布收敛。由于 $U>0$，$\operatorname{sgn}(U^{r_i}G_i)=\operatorname{sgn}G_i$；$G_1,G_2$ 独立、对称且无原子，故每个开象限的极限概率为 $\frac14$，坐标轴的极限概率为零，开象限是极限分布的连续集，由 portmanteau 定理得 (495.7)。证毕。

**命题 495.5（联合信息的必要性）。** 存在取值于 $\mathbb R^2$ 的随机向量 $V=(V_1,V_2)$，使 $\mathbb EV_i=0$、$\mathbb EV_i^2=\mathbb EV_i^4=\frac12$（$i=1,2$）、$\mathbb EV_1V_2=0$，而四个开象限的概率都为零。因此两个坐标各自的有界四阶矩与零协方差不足以推出 (495.7) 型的象限结论；推论 495.4 用的是全部联合矩。

证明。令 $V$ 等概率地取值于 $(1,0),(-1,0),(0,1),(0,-1)$。则 $V_1$ 以概率 $\frac14$ 取 $\pm1$、以概率 $\frac12$ 取 $0$，故 $\mathbb EV_1=0$、$\mathbb EV_1^2=\mathbb EV_1^4=\frac12$；$V_2$ 同理。每个取值都有一个坐标为零，故 $V_1V_2=0$，$\mathbb EV_1V_2=0$，且每个取值都落在坐标轴上，四个开象限的概率都为零。证毕。

**范围。** 引理 495.1、定理 495.2–495.3 与推论 495.4 是抽象接口上的结论；对 $E=\psi-\mathrm{id}$，(493.1)、$(\mathrm W_{2,2})$ 与推论 495.4 的全阶接口都未被证明。Montgomery–Soundararajan [Primes in short intervals, Comm. Math. Phys. 252 (2004), 589–617] 在其强 Hardy–Littlewood 型相关误差假设下推出单一长度的矩（其更一般的矩渐近为该文猜想 1），不涉及不同指数的移动长度 $sx^{\theta_1},tx^{\theta_2}$ 的混合矩及其与宏观位置的联合；Leung [Joint distribution of primes in multiple short intervals, Adv. Math. 490 (2026), 110847] 在 RH 与 LI 下处理比例长度的多个不交区间并采用对数取样。本节的新内容是：定理 495.2 由 §491 推出交叉二阶核必须几乎处处为零，以及定理 495.3 给出的显式正相关常数 $\kappa_1\kappa_2Q_1Q_2(c_{2,2}-c_{2,0}c_{0,2})$。矩方法、Cramér–Wold 定理、Isserlis 公式、Chebyshev 积分不等式与 $\pi$-$\lambda$ 定理都是标准工具。

## 追加锚（本行以下为增补区）

## 496. 方差带推出带宏观权的二阶接口

沿用 §490 的 $E,D_v,V$ 与 §494 的 $\mu_X,U_X,B_X,\kappa$。本节 $E$ 局部有界 Borel 可测，(490.2) 在 $0<\alpha<\theta<\beta<1$ 上成立。令 $h=X^\theta$、$\mathscr N_X=Xh\log X$、$\|f\|_{X,2}^2=\mathscr N_X^{-1}\int_X^{2X}|f|^2$，以及

$$
\varepsilon_X=\sup_{\substack{X/2\le Y\le4X\\Y^\alpha\le v\le Y^\beta}}\left|\frac{V(Y,v)}{Yv\log(Y/v)}-1\right| ,
\tag{496.1}
$$

由 (490.2)，$\varepsilon_X\to0$；本节不假设任何收敛速度。

**引理 496.1（局部方差与移动端点）。** (i) 设 $X\ge4$，$J=[A,B]\subset[X/2,4X]$，$R>0$ 满足

$$
(4X)^\alpha\le R,\qquad 4R\le(X/2)^\beta .
\tag{496.2}
$$

则对所有 $v\in[R,4R]$，$\int_A^BD_v(y)^2\,dy\le v\log X\,\bigl(3(B-A)+16\varepsilon_XX\bigr)$。

(ii) 设 $I$ 为紧区间，$p,q\in C^1(I)$，$p',q'\ge m>0$，$p(I),q(I)\subset J$，$|q-p|\le R$，且对某个 $C\ge0$，$\int_JD_v^2\le Cv$（$R\le v\le4R$）。则 $\int_I|E(q(x))-E(p(x))|^2\,dx\le20CR/m$。

(iii) 在 (i) 及 (ii) 关于 $I,p,q,m$ 的条件下，$\int_I|E(q)-E(p)|^2\le\frac{20R}m\log X\,\bigl(3|J|+16\varepsilon_XX\bigr)$。

证明。(i) 由 (496.2)，对 $Y\in[X/2,4X]$ 与 $v\in[R,4R]$ 有 $Y^\alpha\le v\le Y^\beta$。于是 $\int_A^BD_v^2=V(B,v)-V(A,v)\le v\bigl(B\log\frac Bv-A\log\frac Av\bigr)+\varepsilon_Xv\bigl(B\log\frac Bv+A\log\frac Av\bigr)$。函数 $y\mapsto y\log(y/v)$ 的导数 $\log(y/v)+1\le\log(4X)+1\le3\log X$，故第一项至多 $3v(B-A)\log X$；又 $A+B\le8X$、$0<\log(A/v),\log(B/v)\le\log(4X)\le2\log X$，故第二项至多 $16\varepsilon_XXv\log X$。

(ii) 令 $\delta=q-p$。对 $v\in[2R,3R]$ 有恒等式 $E(q(x))-E(p(x))=D_v(p(x))-D_{v-\delta(x)}(q(x))$（两个增量的终点都是 $p(x)+v$），且 $v-\delta(x)\in[R,4R]$。平方、用 $|a-b|^2\le2a^2+2b^2$、对 $v\in[2R,3R]$ 取平均并对 $x\in I$ 积分：第一项换元 $y=p(x)$，逆 Jacobian 至多 $1/m$；第二项对固定 $x$ 作平移 $w=v-\delta(x)$，把范围放大到 $[R,4R]$，再由 Tonelli 与换元 $y=q(x)$。得

$$
\int_I|E(q)-E(p)|^2\le\frac2{mR}\Bigl(\int_{2R}^{3R}\!\!\int_JD_v^2+\int_R^{4R}\!\!\int_JD_w^2\Bigr)\le\frac{2C}{mR}\Bigl(\frac52+\frac{15}2\Bigr)R^2=\frac{20CR}m .
$$

局部有界性使所有积分有限，Borel 可测性使换序合法。(iii) 把 (i) 代入 (ii)。证毕。

(iii) 保留了因子 $|J|$，而不是把它放大成 $X$；下面把 $[X,2X]$ 分成 $n$ 块时，正是这一点使冻结误差为 $O(1/n)$。

**引理 496.2（宏观变长的冻结）。** 固定 $M\ge1$、$L\ge0$。设 $a\in C^1([1,2])$，$0\le a\le M$，$|a'|\le L$，令 $f_{a,X}(x)=D_{h\,a(x/X)}(x)$。对正整数 $n$，令 $u_j=1+j/n$、$I_j=[u_jX,u_{j+1}X]$，在 $I_j$ 上令 $F_{a,n,X}(x)=D_{h\,a(u_j)}(x)$。若 $Mh\le X$、$Lh/X\le\frac12$，且 $R=(1+L)h/n$ 满足 (496.2)，则

$$
\|f_{a,X}-F_{a,n,X}\|_{X,2}^2\le120(1+L)\Bigl(\frac1n+\frac{Mh}X\Bigr)+640(1+L)\varepsilon_X .
\tag{496.3}
$$

特别地，对每个固定 $n$，$\limsup_X\sup_a\|f_{a,X}-F_{a,n,X}\|_{X,2}^2\le120(1+L)/n$（上确界取遍满足条件的 $a$），且对充分大的 $X$，$\|f_{a,X}\|_{X,2}^2\le880M$。

证明。在 $I_j$ 上取 $p(x)=x+h\,a(u_j)$、$q(x)=x+h\,a(x/X)$，则 $f_{a,X}-F_{a,n,X}=E(q)-E(p)$，$p'=1$，$q'\ge\frac12$，$|q-p|\le Lh/n\le R$，两像都含于 $J_j=[u_jX,u_{j+1}X+Mh]\subset[X/2,4X]$，$|J_j|=X/n+Mh$。由引理 496.1(iii)（$m=\frac12$），$\int_{I_j}|f_{a,X}-F_{a,n,X}|^2\le40R\log X\,(3X/n+3Mh+16\varepsilon_XX)$。对 $j$ 求和并除以 $\mathscr N_X$ 得 (496.3)。对固定 $n$，$R=ch$（$c=(1+L)/n$）满足 $R/(4X)^\alpha=c4^{-\alpha}X^{\theta-\alpha}\to\infty$、$4R/(X/2)^\beta=4c2^\beta X^{\theta-\beta}\to0$，故 (496.2) 与其余条件最终成立（$R=Mh$ 同理），门槛只依赖 $E,\alpha,\theta,\beta,M,L,n$。最后在整个 $[X,2X]$ 上取 $p(x)=x$、$q(x)=x+h\,a(x/X)$、$R=Mh$、$J=[X,2X+Mh]$；对充分大的 $X$，$\varepsilon_X\le1$，由引理 496.1(iii)，$\|f_{a,X}\|_{X,2}^2\le40M(3(1+Mh/X)+16\varepsilon_X)\le880M$。证毕。

**定理 496.3（宏观变长的带权协方差）。** 设 $a,b\in C^1([1,2])$ 非负，$w\in C([1,2])$ 实值。则

$$
\frac1{X^{1+\theta}\log X}\int_X^{2X}w(x/X)\,D_{X^\theta a(x/X)}(x)\,D_{X^\theta b(x/X)}(x)\,dx\longrightarrow\kappa\int_1^2w(u)\min\bigl(a(u),b(u)\bigr)\,du .
\tag{496.4}
$$

证明。第一步（固定长度）。固定 $1\le u<v\le2$、$q>0$、$e\ge0$。端点 $Y_X=dX+eh$（$d\in\{u,v\}$）满足 $qh/Y_X^\alpha\to\infty$、$qh/Y_X^\beta\to0$ 与 $\log(Y_X/(qh))/\log X\to\kappa$，故由 (490.2)，$V(dX+eh,qh)/\mathscr N_X\to dq\kappa$，从而 $\mathscr N_X^{-1}\int_{uX+eh}^{vX+eh}D_{qh}^2\to\kappa q(v-u)$。对 $0<c\le d$，由 $D_{dh}(x)-D_{ch}(x)=D_{(d-c)h}(x+ch)$ 得极化恒等式 $2D_{ch}D_{dh}=D_{ch}^2+D_{dh}^2-D_{(d-c)h}(\cdot+ch)^2$（由方差经极化恢复两点相关，见 Leung [Joint distribution of primes in multiple short intervals, Adv. Math. 490 (2026), 110847] 附注 2.3）；第三项的积分区间为 $[uX+ch,vX+ch]$，用上式处理，得

$$
\mathscr N_X^{-1}\int_{uX}^{vX}D_{ch}D_{dh}\longrightarrow\kappa(v-u)\min(c,d) ;
\tag{496.5}
$$

$c=d$ 时第三项为零，$cd=0$ 时乘积为零。

第二步（分块）。取共同的 $M\ge1$、$L\ge0$ 使 $0\le a,b\le M$、$|a'|,|b'|\le L$，沿用引理 496.2 的分块，令 $w_n=w(u_j)$（$u_j\le u<u_{j+1}$）。由 (496.5)，对固定 $n$，$\mathscr N_X^{-1}\int_X^{2X}w_n(x/X)F_{a,n,X}F_{b,n,X}\to q_n=\frac\kappa n\sum_jw(u_j)\min(a(u_j),b(u_j))$，且 $\|F_{a,n,X}\|_{X,2}^2\to\frac\kappa n\sum_ja(u_j)\le M$。

第三步（误差）。由 $wf_af_b-w_nF_aF_b=(w-w_n)f_af_b+w_n\bigl((f_a-F_a)f_b+F_a(f_b-F_b)\bigr)$、Cauchy–Schwarz 与引理 496.2，记 $\omega_w$ 为 $w$ 的连续模、$d_n=\sqrt{120(1+L)/n}$，

$$
\limsup_X\Bigl|\mathscr N_X^{-1}\int_X^{2X}w(x/X)f_af_b-q_n\Bigr|\le880M\,\omega_w(1/n)+\|w\|_\infty\bigl(\sqrt{880M}+\sqrt M\bigr)d_n .
$$

又 $\min(a,b)$ 的 Lipschitz 常数至多 $L$，故 $|q_n-\kappa\int_1^2w\min(a,b)|\le\kappa(M\omega_w(1/n)+L\|w\|_\infty/n)$。先令 $X\to\infty$，再令 $n\to\infty$。证毕。

**推论 496.4（二阶 Brownian 接口）。** 对每个实值 $\phi\in C([1,2])$，

$$
\sup_{s,t\in[0,1]}\Bigl|\mathbb E_{\mu_X}\bigl[\phi(U_X)B_X(s)B_X(t)\bigr]-\kappa\min(s,t)\int_1^2\phi(u)\frac{du}{u\log2}\Bigr|\longrightarrow0 ,
\tag{496.6}
$$

且对充分大的 $X$，$\sup_{s\in[0,1]}\mathbb E_{\mu_X}|B_X(s)|^2\le1760/\log2$。

证明。在 $[X,2X]$ 上 $x^\theta\log x\cdot x=X^{1+\theta}\log X\cdot u^{1+\theta}(1+\log u/\log X)$（$u=x/X$），故

$$
\mathbb E_{\mu_X}\bigl[\phi(U_X)B_X(s)B_X(t)\bigr]=\frac1{\log2}\cdot\frac1{\mathscr N_X}\int_X^{2X}w_X(x/X)D_{sx^\theta}(x)D_{tx^\theta}(x)\,dx,\qquad w_X(u)=\frac{\phi(u)u^{-1-\theta}\log X}{\log X+\log u},
$$

且 $\|w_X-w\|_\infty\le\|\phi\|_\infty\log2/\log X$，$w(u)=\phi(u)u^{-1-\theta}$。由引理 496.2 的一致界（$a(u)=su^\theta$ 满足 $0\le a\le2$、$|a'|\le1$），把 $w_X$ 换成 $w$ 的误差至多 $1760\|\phi\|_\infty/\log X$，对 $s,t$ 一致。由定理 496.3（$a(u)=su^\theta$、$b(u)=tu^\theta$，$\min(a,b)=u^\theta\min(s,t)$）得 (496.6) 的逐点形式；二阶矩界由 $x^{1+\theta}\log x\ge X^{1+\theta}\log X$ 与同一一致界得到。对一致性，固定 $0<\delta\le1$，对 $|s-t|\le\delta$ 在引理 496.1(iii) 中取 $p(x)=x+sx^\theta$、$q(x)=x+tx^\theta$、$R=2\delta h$、$m=1$、$J=[X,2X+2h]$，门槛与 $s,t$ 无关，得 $\limsup_X\sup_{|s-t|\le\delta}\|B_X(s)-B_X(t)\|_{L^2(\mu_X)}^2\le120\delta/\log2$。由 Cauchy–Schwarz，$K_X(s,t)=\mathbb E_{\mu_X}[\phi(U_X)B_X(s)B_X(t)]$ 满足 $\limsup_X\sup_{|s-s'|,|t-t'|\le\delta}|K_X(s,t)-K_X(s',t')|\le\frac{2\|\phi\|_\infty}{\log2}\sqrt{1760\cdot120\,\delta}$；在 $[0,1]^2$ 的有限 $\delta$-网上逐点收敛是一致的，极限核在 $\delta$ 尺度上的变化至多 $2\kappa\|\phi\|_\infty\delta$，令 $\delta\downarrow0$。证毕。

**推论 496.5（一、二阶接口由 (490.2) 推出）。** (a) $(\mathrm M_2)$ 成立，$M_2(s,t)=c_2\kappa\min(s,t)=\frac{2^\kappa-1}{\log2}\min(s,t)$。

(b) 对每个实值 $\phi\in C([1,2])$，$\sup_{s\in[0,1]}|\mathbb E_{\mu_X}[\phi(U_X)B_X(s)]|\to0$；特别地 $(\mathrm M_1)$ 以 $M_1=0$ 成立。

(c) 设 $0<\theta_1<\theta_2<1$，(490.2) 分别在包含 $\theta_1$、$\theta_2$ 的指数带上成立，$B_{i,X}$ 如 §495。则对每个实值 $\phi\in C([1,2])$，$\sup_{s,t\in[0,1]}|\mathbb E_{\mu_X}[\phi(U_X)B_{1,X}(s)B_{2,X}(t)]|\to0$；特别地 $(\mathrm J_{1,1})$ 成立且 $M_{1,1}\equiv0$。

证明。(a) 取 $\phi(u)=u^\kappa$，由推论 496.4，二阶矩界给出 (a) 部分，极限核连续。(b) 取 $\theta<\nu<\beta$、$M=X^\nu$、$f_s(x)=D_{sx^\theta}(x)$、$P_s(y)=\int_X^yf_s$。引理 493.2 的证明给出 $\sup_{s,y}|P_s(y)|\ll\sqrt{\log X}\bigl(Xh/\sqrt M+\sqrt{XhM}\bigr)$，故 $\sup_{s,y}|P_s(y)|/(X\sqrt{h\log X})\ll X^{-(\nu-\theta)/2}+X^{-(1-\nu)/2}\to0$。$\mathbb E_{\mu_X}[\phi(U_X)B_X(s)]=\frac1{\log2}\int_X^{2X}\phi(x/X)\,\varpi(x)f_s(x)\,dx$，其中 $\varpi(x)=x^{-1-\theta/2}(\log x)^{-1/2}$ 在 $[X,2X]$ 上单调、$\varpi\le X^{-1-\theta/2}(\log X)^{-1/2}$。若 $\phi$ 是 $n$ 块阶梯函数，逐块分部积分（$\varpi$ 递减，故每块 $[a,b]$ 上 $\varpi(a)+\varpi(b)+\int_a^b|\varpi'|=2\varpi(a)\le2\varpi(X)$）给出至多 $\frac{2n}{\log2}\|\phi\|_\infty\sup_{s,y}|P_s(y)|\,X^{-1-\theta/2}(\log X)^{-1/2}\to0$；一般连续 $\phi$ 用阶梯函数 $\phi_n$ 一致逼近，误差由 $|\mathbb E[(\phi-\phi_n)(U_X)B_X(s)]|\le\|\phi-\phi_n\|_\infty(\mathbb EB_X(s)^2)^{1/2}$ 与推论 496.4 的二阶矩界控制。(c) 取 $\theta_1<\mu<\nu<\min(\beta_1,\theta_2)$、$\eta_0=\frac12\min(\mu-\theta_1,\nu-\mu,\theta_2-\nu)$。由引理 491.3（$h=X^{\theta_1}$、$k=X^{\theta_2}$），对每个区间 $I\subset[X,2X]$ 与 $s,t\in[0,1]$ 一致地 $|\int_ID_{sx^{\theta_1}}D_{tx^{\theta_2}}|\ll X^{1+(\theta_1+\theta_2)/2}\log X\cdot X^{-\eta_0}$。与推论 496.4 同样写出权 $w_X(u)=\phi(u)u^{-1-(\theta_1+\theta_2)/2}\log X/(\log X+\log u)$；对 $n$ 块阶梯权，上界逐块给出至多 $Cn\|w\|_\infty X^{-\eta_0}$（相对于自然尺度 $X^{1+(\theta_1+\theta_2)/2}\log X$）；连续权的逼近误差由两个指数的二阶矩界与 Cauchy–Schwarz 控制，至多 $C'\omega_w(1/n)$。先令 $X\to\infty$ 再令 $n\to\infty$。证毕。

因此，在相应的 (490.2) 下，§494–§495 各接口中总阶数为一和二的部分都是定理：$M_1=0$、$M_{2,0}=c_{2,0}\kappa_1\min$、$M_{0,2}=c_{0,2}\kappa_2\min$、$M_{1,1}\equiv0$（这加强了定理 495.2 的几乎处处结论），所需的一、二阶矩界也已给出。总阶数三及更高的绝对矩界与相应混合矩极限仍需额外假设，包括 Brownian 型接口所要求的奇阶极限为零；四阶情形还涉及 (493.1) 型上界及四阶混合矩极限。

**范围。** 本节以 (490.2) 为条件，不涉及素数余项 $E=\psi-\mathrm{id}$ 的算术证明。固定长度方差到比例长度或移动长度的转移已有先例：Goldston [Notes on pair correlation of zeros and prime numbers, arXiv:math/0412313] §9 用 Saffari–Vaughan 论证讨论比例窗与加法窗方差的定性等价；Bui–Keating–Smith [On the variance of sums of arithmetic functions over primes in short intervals and pair correlation for $L$-functions in the Selberg class, J. London Math. Soc. 94 (2016), 161–185] 的定理 $C_1$、$D_1$ 在固定加法窗与比例窗之间转移方差；Chan [Higher moments of primes in short intervals I, arXiv:math/0409530v2 (2004)] 定理 3.1、4.1 在 RH 与定量矩假设下转移固定长度与比例长度的偶矩，方法可追溯到 Saffari–Vaughan。极化恢复两点相关是已知工具（Leung 2026 附注 2.3）。本节在上述转移方法下给出：只用定性的一致 $o(1)$ 假设 (490.2)、对局部有界 Borel $E$ 的局部移动端点估计（引理 496.1(iii)，保留区间长度 $|J|$）与冻结误差 (496.3)，由此对一般宏观变长 $X^\theta a(x/X)$ 与连续宏观权得到带权协方差 (496.4)，以及对时间参数一致的二阶接口 (496.6) 和推论 496.5 对 §494–§495 接口的削减。

## 追加锚（本行以下为增补区）

## 497. 固定尺度四阶矩到移动长度的传递

沿用 §494 的 $\mu_X,U_X,B_X,\kappa,r,c_k$ 与 §496 的 $h=X^\theta$、$\varepsilon_X$ 记号；$E$ 局部有界 Borel 可测，$0<\alpha<\theta<\beta<1$。令 $d\nu(u)=du/(u\log2)$（$1\le u\le2$），

$$
\widetilde B_X(c,x)=\frac{D_{ch}(x)}{\sqrt{h\log X}}\qquad(c\ge0,\ X\le x\le2X),
$$

$W_3\equiv0$，$W_4(c_1,c_2,c_3,c_4)=\kappa^2\bigl[\min(c_1,c_2)\min(c_3,c_4)+\min(c_1,c_3)\min(c_2,c_4)+\min(c_1,c_4)\min(c_2,c_3)\bigr]$。

**局部四阶能量假设 $(\mathrm L_4)$。** 存在 $C_4$ 与 $\varepsilon'_X\to0$，使对充分大的 $X$、一切 $X/2\le A\le B\le4X$ 与 $(4X)^\alpha\le v\le(X/2)^\beta$，

$$
\int_A^B|D_v(y)|^4\,dy\le C_4\,v^2(\log X)^2\bigl(B-A+\varepsilon'_XX\bigr).
\tag{497.1}
$$

**固定尺度假设 $(\mathrm F_k)$（$k=3,4$）。** 对每个 $M>0$、$\mathbf c\in[0,M]^k$ 与 $1\le u<v\le2$，

$$
\lim_{X\to\infty}\mathbb E_{\mu_X}\Bigl[\mathbf 1_{[u,v]}(U_X)\prod_{j=1}^k\widetilde B_X(c_j)\Bigr]=\nu([u,v])\,W_k(\mathbf c).
\tag{497.2}
$$

$(\mathrm F_4)$ 是固定长度 $c_1h,\dots,c_4h$ 的联合四阶矩的 Wick 渐近，带有宏观位置的区间权，是下面证明直接使用的形式；$(\mathrm F_3)$ 是相应三阶混合矩的消失。单一长度的四阶矩渐近不决定 $(\mathrm F_4)$：边际矩不决定混合矩。

**引理 497.1（$L^4$ 移动端点估计）。** 设 $(\mathrm L_4)$，$R$ 满足 (496.2)，$I$ 为紧区间，$p,q\in C^1(I)$，$p',q'\ge m>0$，$p(I),q(I)\subset J\subset[X/2,4X]$，$|q-p|\le R$。则

$$
\int_I|E(q(x))-E(p(x))|^4\,dx\le\frac{656}{3}\cdot\frac{C_4}m\,R^2(\log X)^2\bigl(|J|+\varepsilon'_XX\bigr).
\tag{497.3}
$$

证明。令 $\delta=q-p$。对 $v\in[2R,3R]$，$E(q)-E(p)=D_v(p)-D_{v-\delta}(q)$ 且 $v-\delta\in[R,4R]$。由 $|a-b|^4\le8(|a|^4+|b|^4)$，对 $v\in[2R,3R]$ 取平均并对 $x\in I$ 积分；与引理 496.1(ii) 的证明相同地换元与使用 Tonelli，得

$$
\int_I|E(q)-E(p)|^4\le\frac8{mR}\Bigl(\int_{2R}^{3R}\!\!\int_J|D_v|^4+\int_R^{4R}\!\!\int_J|D_w|^4\Bigr)\le\frac{8C_4}{mR}(\log X)^2\bigl(|J|+\varepsilon'_XX\bigr)\Bigl(\int_{2R}^{3R}v^2dv+\int_R^{4R}v^2dv\Bigr),
$$

而 $\int_{2R}^{3R}v^2+\int_R^{4R}v^2=\bigl(\frac{19}3+21\bigr)R^3=\frac{82}3R^3$。证毕。

**引理 497.2（四阶冻结与一致矩界）。** 设 $(\mathrm L_4)$。固定 $M\ge1$、$L\ge0$。

(i) 对 $a\in C^1([1,2])$，$0\le a\le M$，$|a'|\le L$，令 $f_{a,X}(x)=D_{h\,a(x/X)}(x)$。则对充分大的 $X$（门槛只依赖 $E,\alpha,\theta,\beta,M,L$），$\mathbb E_{\mu_X}\bigl|f_{a,X}/\sqrt{h\log X}\bigr|^4\le K_M:=1312\,C_4M^2/\log2$；特别地 $\sup_{0\le c\le M}\mathbb E_{\mu_X}|\widetilde B_X(c)|^4\le K_M$。

(ii) 沿用引理 496.2 的分块 $u_j=1+j/n$、$I_j=[u_jX,u_{j+1}X]$ 与冻结函数 $F_{a,n,X}=D_{h\,a(u_j)}$（$x\in I_j$）。则对每个固定 $n$，

$$
\limsup_{X\to\infty}\ \sup_a\ \mathbb E_{\mu_X}\Bigl|\frac{f_{a,X}-F_{a,n,X}}{\sqrt{h\log X}}\Bigr|^4\le\frac{1312\,C_4(1+L)^2}{3\,n^2\log2} .
\tag{497.4}
$$

证明。在 $[X,2X]$ 上 $d\mu_X\le dx/(X\log2)$。(i) 取 $p(x)=x$、$q(x)=x+h\,a(x/X)$、$R=Mh$、$m=\frac12$、$J=[X,2X+Mh]$（对充分大的 $X$，$q'\ge\frac12$、$Mh\le X$、$\varepsilon'_X\le1$，且 $R$ 满足 (496.2)），由引理 497.1，$\int_X^{2X}|f_{a,X}|^4\le\frac{1312}3C_4M^2h^2(\log X)^2\cdot3X$，除以 $X\log2\cdot h^2(\log X)^2$ 即得。$c$ 为常数时取 $a\equiv c$。(ii) 在 $I_j$ 上取 $p(x)=x+h\,a(u_j)$、$q(x)=x+h\,a(x/X)$、$R=(1+L)h/n$、$m=\frac12$、$J_j=[u_jX,u_{j+1}X+Mh]$，与引理 496.2 的证明相同，条件对充分大的 $X$ 成立。由引理 497.1，$\int_{I_j}|f-F|^4\le\frac{1312}3C_4R^2(\log X)^2(X/n+Mh+\varepsilon'_XX)$。对 $j$ 求和并除以 $X\log2\cdot h^2(\log X)^2$，得 $\frac{1312C_4(1+L)^2}{3n^2\log2}\bigl(1+nMh/X+n\varepsilon'_X\bigr)$，对固定 $n$ 令 $X\to\infty$。证毕。

冻结误差为 $O(n^{-2})$，因为引理 497.1 保留了区间长度 $|J|$。

**定理 497.3（四阶以内的移动长度传递）。** 设 $(\mathrm L_4)$，$k\in\{3,4\}$，$(\mathrm F_k)$ 成立。设 $b_1,\dots,b_k\in C^1([1,2])$，$0\le b_j\le M$，$|b_j'|\le L$，$w\in C([1,2])$ 实值。则

$$
\lim_{X\to\infty}\mathbb E_{\mu_X}\Bigl[w(U_X)\prod_{j=1}^k\frac{D_{h\,b_j(U_X)}(x)}{\sqrt{h\log X}}\Bigr]=\int_1^2w(u)\,W_k\bigl(b_1(u),\dots,b_k(u)\bigr)\,d\nu(u).
\tag{497.5}
$$

证明。令 $A_j=f_{b_j,X}/\sqrt{h\log X}$、$G_j=F_{b_j,n,X}/\sqrt{h\log X}$。由引理 497.2(i)，$\|A_j\|_{L^4(\mu_X)}\le K_M^{1/4}$；对 $G_j$，在每块上对 $p(x)=x$、$q(x)=x+h\,b_j(u_\ell)$、$R=Mh$、$m=\frac12$、$J_\ell=[u_\ell X,u_{\ell+1}X+Mh]$ 用引理 497.1，得 $\mathbb E_{\mu_X}|G_j|^4\le\frac{1312C_4M^2}{3\log2}(1+nMh/X+n\varepsilon'_X)\le K_M$（对固定 $n$ 与充分大的 $X$）。又$\limsup_X\|A_j-G_j\|_{L^4(\mu_X)}\le\bigl(\frac{1312C_4(1+L)^2}{3\log2}\bigr)^{1/4}n^{-1/2}$。由望远镜恒等式 $\prod_jA_j-\prod_jG_j=\sum_i(A_i-G_i)\prod_{j<i}A_j\prod_{j>i}G_j$ 与关于概率测度 $\mu_X$ 的 Hölder 不等式（$k$ 个 $L^k$ 因子，且 $\|\cdot\|_{L^k}\le\|\cdot\|_{L^4}$），$\limsup_X\|\prod_jA_j-\prod_jG_j\|_{L^1(\mu_X)}\le C'n^{-1/2}$，$C'$ 只依赖 $C_4,K_M,L,k$；乘以 $\|w\|_\infty$ 即控制 $\mathbb E[w(U_X)(\prod_jA_j-\prod_jG_j)]$。令 $w_n=w(u_j)$（$u_j\le u<u_{j+1}$），则 $|\mathbb E[(w-w_n)(U_X)\prod_jG_j]|\le\omega_w(1/n)K_M^{k/4}$。在每块上 $G_j=\widetilde B_X(b_j(u_j))$，由 $(\mathrm F_k)$（区间 $[u_j,u_{j+1}]$），

$$
\mathbb E_{\mu_X}\Bigl[w_n(U_X)\prod_jG_j\Bigr]=\sum_{j'}w(u_{j'})\,\mathbb E_{\mu_X}\Bigl[\mathbf 1_{[u_{j'},u_{j'+1}]}(U_X)\prod_j\widetilde B_X\bigl(b_j(u_{j'})\bigr)\Bigr]\longrightarrow\sum_{j'}w(u_{j'})\,\nu([u_{j'},u_{j'+1}])\,W_k\bigl(\mathbf b(u_{j'})\bigr)
$$

（块的公共端点是 $\mu_X$-零集）。$W_k\circ\mathbf b$ 在 $[1,2]$ 上连续，右边是 $\int_1^2w\,W_k(\mathbf b)\,d\nu$ 的 Riemann 和。先令 $X\to\infty$，再令 $n\to\infty$。证毕。

**推论 497.4（§494 的三、四阶接口）。** 设 $(\mathrm L_4)$。

(a) 若 $(\mathrm F_4)$ 成立，则 (494.3) 成立：对每个 $\mathbf s\in[0,1]^4$，$\mathbb E_{\mu_X}[U_X^{2\kappa}\prod_jB_X(s_j)]\to c_4\kappa^2\sum_\pi\prod_{\{i,j\}\in\pi}\min(s_i,s_j)$；且 $\sup_{s\in[0,1]}\mathbb E_{\mu_X}|B_X(s)|^4$ 对充分大的 $X$ 有界，故 $(\mathrm M_4)$ 以这一 Brownian 核成立。

(b) 若 $(\mathrm F_3)$ 成立，则 $(\mathrm M_3)$ 以 $M_3\equiv0$ 成立。

证明。在 $[X,2X]$ 上，$B_X(s,x)=\lambda_X(x)\,u^{-\theta/2}\,D_{h\,su^\theta}(x)/\sqrt{h\log X}$，其中 $u=x/X$、$\lambda_X(x)=\sqrt{\log X/\log x}$，$\sup_{[X,2X]}|\lambda_X^k-1|\to0$。取 $b_j(u)=s_ju^\theta$（$0\le b_j\le2$、$|b_j'|\le1$）。由引理 497.2(i)，$\mathbb E|B_X(s)|^4\le K_2$，并且把 $\prod_j\lambda_X$ 换成 $1$ 的误差至多 $\sup|\lambda_X^k-1|\cdot2^{kr}K_2^{k/4}\to0$。对 $k=4$，由定理 497.3（$w(u)=u^{2\kappa}u^{-2\theta}$），极限为 $\int_1^2u^{2\kappa-2\theta}W_4(s_1u^\theta,\dots,s_4u^\theta)\,d\nu=\kappa^2\sum_\pi\prod\min(s_i,s_j)\int_1^2u^{2\kappa}\,d\nu=c_4\kappa^2\sum_\pi\prod\min(s_i,s_j)$，因为 $W_4$ 关于其变量二次齐次。对 $k=3$，取 $w(u)=u^{3r-3\theta/2}$，由 $W_3\equiv0$ 得极限为零，且 $\sup_s\mathbb E|B_X(s)|^3\le K_2^{3/4}$，这给出 $(\mathrm M_3)$ 的 (a) 部分。证毕。

**引理 497.5（由固定长度四阶渐近推出 (493.1) 与 $(\mathrm L_4)$）。** 设存在常数 $\mathsf B$，使在 $Y^\alpha\le v\le Y^\beta$ 上一致地

$$
\int_1^Y|D_v(x)|^4\,dx=3v^2\int_1^Y\Bigl(\log\frac yv+\mathsf B\Bigr)^2dy+o\Bigl(Yv^2\log^2\frac Yv\Bigr)\qquad(Y\to\infty).
\tag{497.6}
$$

则 (493.1) 与 $(\mathrm L_4)$ 都成立。（在所述误差精度下，把 $\mathsf B$ 换成任何其他常数只改变 $O(Yv^2\log(Y/v))$，(497.6) 保留常规的次项形式，并不确定 $\mathsf B$。）

证明。由 $\log(Y/v)\ge(1-\beta)\log Y\to\infty$ 与 $\int_1^Y\log^2(y/v)\,dy=v\int_{1/v}^{Y/v}\log^2t\,dt\le Y(\log^2(Y/v)+2)+2v$，主项为 $O(Yv^2\log^2(Y/v))$，给出 (493.1)。对 $X/2\le A\le B\le4X$、$(4X)^\alpha\le v\le(X/2)^\beta$，$v$ 对 $Y=A$ 与 $Y=B$ 都在带内；两式相减，主项 $3v^2\int_A^B(\log(y/v)+\mathsf B)^2dy\le3v^2(B-A)(2\log X+|\mathsf B|)^2\le13v^2(\log X)^2(B-A)$（$X$ 充分大），误差为 $o(Xv^2\log^2X)$。证毕。

于是，在 (490.2)、(497.6) 与 $(\mathrm F_4)$ 下，定理 494.2 的全部假设成立，其结论成立：二、四阶矩极限，以及 $g$ 不几乎处处为零时的超额峰度 $3(\frac a2\coth\frac a2-1)$；§494 中依赖移动长度与宏观权的四阶接口被约化为固定长度的陈述 (497.6) 与 $(\mathrm F_4)$。$(\mathrm F_3)$ 另给出三阶接口。

**范围。** (497.6)、$(\mathrm F_3)$、$(\mathrm F_4)$ 对 $E=\psi-\mathrm{id}$ 未被证明。Montgomery–Soundararajan [Primes in short intervals, Comm. Math. Phys. 252 (2004), 589–617] 猜想 1（$K=4$）是单一长度 $H$ 的四阶矩渐近，与 (497.6) 同型，但不给出不同长度 $c_jh$ 的联合矩 $(\mathrm F_4)$；其定理 3 在强 Hardy–Littlewood 型相关误差假设下对 $\log N\le H\le N^{1/K}$ 给出带显式误差的公式，相对渐近在 $N^\eta\le H\le N^{1/K-\delta}$ 一类内部范围上成立。Chan [Higher moments of primes in short intervals I, arXiv:math/0409530v2 (2004)] 定理 3.1、4.1 在 RH 与定量矩假设下，于相应的内部参数范围上转移单一固定长度与比例长度的偶矩；Leung [Joint distribution of primes in multiple short intervals, Adv. Math. 490 (2026), 110847] 处理不交区间。本节在 §496 的端点与冻结方法下给出：$L^4$ 端点估计 (497.3)、$O(n^{-2})$ 的四阶冻结误差 (497.4)、带宏观区间权的固定尺度混合矩到移动长度的传递（定理 497.3），以及由此对 §494 三、四阶接口的约化。Isserlis 配对结构、Hölder 不等式与 Riemann 和逼近都是标准工具。

## 追加锚（本行以下为增补区）

## 498. 强 Hardy–Littlewood 假设下重叠短区间的三、四阶矩

本节对 $E=\psi-\mathrm{id}$ 证明：在四点以内的 Montgomery–Soundararajan 型强 Hardy–Littlewood 误差假设下，对 $0<\theta<\frac14$，§497 的 $(\mathrm F_3)$、$(\mathrm F_4)$、(497.6) 与 (490.2) 都成立。

**记号。** $\Lambda_0=\Lambda-1$。对有限整数集 $\mathcal D$，$\mathfrak S(\mathcal D)=\prod_p\frac{1-\nu_p(\mathcal D)/p}{(1-1/p)^{|\mathcal D|}}$（$\nu_p$ 为 $\mathcal D$ 模 $p$ 的剩余类个数，$\mathfrak S(\varnothing)=1$），$\mathfrak S_0(\mathcal D)=\sum_{\mathcal J\subseteq\mathcal D}(-1)^{|\mathcal D|-|\mathcal J|}\mathfrak S(\mathcal J)$；$\mathfrak S_0(\{d\})=0$。固定 $0<\alpha<\beta<\frac14$。

**假设 $\mathrm{HL}_4(\beta)$。** 对每个 $\varepsilon>0$ 与 $M\ge1$，存在 $A_{\varepsilon,M}$ 与 $N_{\varepsilon,M}$，使对 $N\ge N_{\varepsilon,M}$、$1\le r\le4$、互异整数 $1\le d_1,\dots,d_r\le MN^\beta$ 与 $0\le y\le3N$，

$$
\Bigl|\sum_{n\le y}\prod_{j=1}^r\Lambda(n+d_j)-y\,\mathfrak S(\{d_1,\dots,d_r\})\Bigr|\le A_{\varepsilon,M}N^{1/2+\varepsilon}.
\tag{498.1}
$$

这是 Montgomery–Soundararajan [Primes in short intervals, Comm. Math. Phys. 252 (2004), 589–617] 定理 3 的相关误差假设在 $k\le4$、位移至多 $MN^\beta$ 时的形式。

对区间 $I=(a,b]\subseteq[0,M]$ 与 $H\ge1$，令 $\Delta_{H,I}(x)=\psi(x+bH)-\psi(x+aH)-(b-a)H$，$Z_{N,H}(I;x)=\Delta_{H,I}(x)/\sqrt{H\log N}$，$\kappa_{N,H}=\log(N/H)/\log N$，$\sigma(I,J)=|I\cap J|$，$\mathcal W_4(I_1,\dots,I_4)=\sigma(I_1,I_2)\sigma(I_3,I_4)+\sigma(I_1,I_3)\sigma(I_2,I_4)+\sigma(I_1,I_4)\sigma(I_2,I_3)$。对实值有界变差函数 $w$（在 $[1,2]$ 外延拓为零），$\|w\|_{\mathrm{BV}}=\|w\|_\infty+\operatorname{Var}_{\mathbb R}w$，$\langle w\rangle=\int_1^2w$。

**定理 498.1（带宏观权的重叠区间矩）。** 设 $\mathrm{HL}_4(\beta)$，$M\ge1$ 固定。则当 $N\to\infty$ 时，

$$
\frac1N\int_N^{2N}w(x/N)\prod_{j=1}^3Z_{N,H}(I_j;x)\,dx=o(1),
\tag{498.2}
$$

$$
\frac1N\int_N^{2N}w(x/N)\prod_{j=1}^4Z_{N,H}(I_j;x)\,dx=\langle w\rangle\,\kappa_{N,H}^2\,\mathcal W_4(I_1,\dots,I_4)+o(1),
\tag{498.3}
$$

余项关于 $N^\alpha\le H\le N^\beta$、$I_j\subseteq[0,M]$（含空区间与任意重叠）与 $\|w\|_{\mathrm{BV}}\le1$ 一致。

取 $\alpha<\theta<\beta$、$N=X$、$H=X^\theta$、$I_j=(0,c_j]$ 与 $w(t)=\mathbf 1_{[u,v]}(t)/(t\log2)$（$\langle w\rangle=\nu([u,v])$，$\|w\|_{\mathrm{BV}}\le3/\log2$），由于 $Z_{X,h}((0,c];x)=\widetilde B_X(c,x)$、$\kappa_{X,h}=1-\theta=\kappa$、$\sigma((0,c_i],(0,c_j])=\min(c_i,c_j)$，定理 498.1 给出 §497 的 $(\mathrm F_3)$ 与 $(\mathrm F_4)$。

**引理 498.2（二次关系下的四阶配对缺陷）。** 设 $S$ 为有限集，$\mathcal A$ 为交换实代数，$\ell:\mathcal A\to\mathbb R$ 线性，$\ell(1)=1$，且对 $d\in S$，$\ell(Y_d)=0$、$Y_d^2=aY_d+b$。对 $f_1,\dots,f_4:S\to\mathbb R$，令 $f_A=\prod_{i\in A}f_i$、$T_A=\sum_{d\in S}f_A(d)$、$V_k(f_1,\dots,f_k)=\ell\bigl(\prod_{i\le k}\sum_df_i(d)Y_d\bigr)$，以及有序互异指标和 $R_k(g_1,\dots,g_k)=\sum_{d_1,\dots,d_k\in S\text{ 两两不同}}\prod_jg_j(d_j)\,\ell(Y_{d_1}\cdots Y_{d_k})$。则

$$
V_2(f_i,f_j)=R_2(f_i,f_j)+bT_{ij},\qquad
V_3=R_3+a\sum_{\{i,j\}}R_2(f_{ij},f_k)+abT_{123},
\tag{498.4}
$$

$$
\begin{aligned}
V_4-\sum_\pi\prod_{\{i,j\}\in\pi}V_2(f_i,f_j)={}&R_4-\sum_\pi\prod_{\{i,j\}\in\pi}R_2(f_i,f_j)+a\sum_{\{i,j\}}R_3(f_{ij},f_k,f_l)+a^2\sum_{\pi=\{ij,kl\}}R_2(f_{ij},f_{kl})\\
&+(a^2-2b)\sum_lR_2(f_{[4]\setminus\{l\}},f_l)+(a^2b-2b^2)T_{1234},
\end{aligned}
\tag{498.5}
$$

其中 $\pi$ 遍历三个完美配对，三个非平凡和分别有 $6,3,4$ 项。

证明。由二次关系，$Y_d^3=(a^2+b)Y_d+ab$、$Y_d^4=(a^3+2ab)Y_d+(a^2b+b^2)$。展开 $V_k$ 并按指标相等关系分类。二、三阶式立即得到。四阶的五种重数类型贡献为：$1{+}1{+}1{+}1$ 给 $R_4$；重复对 $ij$ 的 $2{+}1{+}1$ 给 $aR_3(f_{ij},f_k,f_l)+b\bigl[T_{ij}R_2(f_k,f_l)-R_2(f_{ijk},f_l)-R_2(f_{ijl},f_k)\bigr]$（两个减项来自重复指标不得等于其余两个指标）；配对 $ij\mid kl$ 的 $2{+}2$ 给 $a^2R_2(f_{ij},f_{kl})+b^2(T_{ij}T_{kl}-T_{1234})$；单点 $l$ 的 $3{+}1$ 给 $(a^2+b)R_2(f_{[4]\setminus\{l\}},f_l)$；$4$ 给 $(a^2b+b^2)T_{1234}$。六个 $2{+}1{+}1$ 类型中，每个 $R_2(f_{[4]\setminus\{l\}},f_l)$ 恰被减去三次，合并系数为 $(a^2+b)-3b=a^2-2b$；三个 $2{+}2$ 类型给 $T_{1234}$ 贡献 $-3b^2$，合并系数为 $a^2b-2b^2$。最后把二阶式代入 $\sum_\pi\prod V_2$，项 $b\sum T_{ij}R_2(f_k,f_l)$ 与 $b^2\sum_\pi T_{ij}T_{kl}$ 恰好抵消，得 (498.5)。证毕。

**引理 498.3（区间权的中心化奇异级数平均）。** 对区间 $I_j\subseteq[0,M]$，令 $R_k(H;I_1,\dots,I_k)=\sum\mathfrak S_0(\{d_1,\dots,d_k\})$，求和取遍两两不同、$d_j/H\in I_j$ 的正整数 $d_j$。则关于区间端点一致地，

$$
R_2(H;I,J)=-H\log H\,|I\cap J|+O_M(H),\qquad R_3=o_M\bigl((H\log H)^{3/2}\bigr),
\tag{498.6}
$$

$$
R_4(H;I_1,\dots,I_4)=\sum_\pi\prod_{\{i,j\}\in\pi}R_2(H;I_i,I_j)+o_M(H^2\log^2H)=H^2\log^2H\,\mathcal W_4(I_1,\dots,I_4)+o_M(H^2\log^2H).
\tag{498.7}
$$

证明。(a) 二阶。令 $K(d,e)=\mathfrak S(\{d,e\})-1=\mathfrak S_0(\{d,e\})$（$d\ne e$）、$K(d,d)=0$，$A(m)=\sum_{1\le d,e\le m}K(d,e)$。由 Montgomery–Soundararajan 2004 定理 2 与 (16)，$A(m)=-m\log m+O(m)$。$K$ 平移不变，故对前缀区间有 $\sum_{d\le m,\,e\le n}K(d,e)=\frac12\bigl(A(m)+A(n)-A(|m-n|)\bigr)$；当 $0\le m,n\le MH$ 时它等于 $-\min(m,n)\log H+O_M(H)$。区间示性函数是两个前缀示性函数之差，展开得 (498.6) 第一式。

(b) 有限筛。令 $Y_0=((M+5)H)^{10}$、$Q=\prod_{p\le Y_0}p$、$P=Q/\varphi(Q)\ll_M\log H$。在模 $Q$ 均匀的 $a$ 上令 $Y_d(a)=P\mathbf 1_{(a+d,Q)=1}-1$，则 $\mathbb EY_d=0$、$Y_d^2=(P-2)Y_d+(P-1)$，且由中国剩余定理，对互异位移 $\mathbb E\prod_{d\in\mathcal D}Y_d=\mathfrak S_{0,Q}(\mathcal D)$（Euler 积只取 $p\mid Q$）。位移直径至多 $(M+4)H$、$|\mathcal D|\le4$ 时，每个 $p>Y_0$ 看到 $|\mathcal D|$ 个不同剩余类，故 $\mathfrak S(\mathcal D)=\mathfrak S_Q(\mathcal D)(1+O(Y_0^{-1}))$；又 $0\le\mathfrak S_Q\le P^{|\mathcal D|}$，由容斥 $|\mathfrak S_0-\mathfrak S_{0,Q}|\ll_M(\log H)^4/Y_0$，对至多 $O_M(H^4)$ 个位移组求和后可忽略。

(c) 有限筛的光滑权配对与区间恢复。令 $X_I=\sum_{d/H\in I}Y_d$、$A_H=\sqrt{H\log H}$。Montgomery–Soundararajan 2004 定理 1（(15)）给出：含 $K$ 个整数点的区间满足 $V_2(Q;K)\ll_MK\log H$、$V_4(Q;K)=3V_2(Q;K)^2+O(K^{2-1/28}P^{18})$；当 $K\ge H^{1/4}/\sqrt{\log H}$ 时误差除以 $K^2\log^2H$ 为 $O(K^{-1/28}(\log H)^{16})=o(1)$，当 $K$ 更小时用 $\|X_I\|_4\le KP$。合并得 $\|X_I\|_{L^4}\le C_MA_H\sqrt{|I|}+O_M(H^{1/4}\sqrt{\log H})$，对全部相关区间一致；故端点相差至多 $\delta$ 的两个区间满足 $\|X_I-X_J\|_4/A_H\le2C_M\sqrt\delta+o(1)$。Kuperberg [Sums of singular series along arithmetic progressions and with smooth weights, arXiv:2301.06095] 定理 1.3 对固定的光滑权 $f_j\in C_c^\infty((0,\infty))$ 给出有限筛矩的配对公式：$\mathbb E\prod_{j\le k}X_{f_j}=\sum_\pi\prod\mathbb E[X_{f_i}X_{f_j}]+O_{\mathbf f}(H^{k/2-1/(7k)}P^{2^k+k/2})$（奇数阶配对和为空；该定理允许任意无平方因子模，包括这里的 $Q$）。它与上面的有限筛变量的对应由 Ramanujan 展开 $P\mathbf 1_{(a,Q)=1}=\sum_{q\mid Q}\frac{\mu(q)}{\varphi(q)}c_q(a)$ 与模 $Q$ 的特征正交性给出。由 $P\ll_M\log H$，对固定光滑权，三阶矩为 $o(A_H^3)$、四阶 Wick 缺陷为 $o(A_H^4)$。用支撑在 $(0,\infty)$ 内的平移光滑化 $f_{I,\delta}$（例如 $\mathbf 1_{I+r}$ 对 $\delta\le r\le3\delta$ 的光滑平均）逼近区间示性函数，由 $\mathbf 1_{(a+r,b+r]}-\mathbf 1_{(a,b]}=\mathbf 1_{(b,b+r]}-\mathbf 1_{(a,a+r]}$ 与 Minkowski 不等式，误差在 $L^4$ 中至多 $2C_M\sqrt{3\delta}A_H+o(A_H)$；乘积的望远镜展开与 Hölder 不等式把误差传到三、四阶矩与四阶 Wick 缺陷。为得到端点一致性，先把任意区间移到有限 $\delta$-网格上，再对有限组网格区间使用配对公式；先令 $H\to\infty$ 再令 $\delta\downarrow0$。得有限筛的 $\mathbb E\prod_{j\le3}X_{I_j}=o_M(A_H^3)$ 与 $\mathbb E\prod_{j\le4}X_{I_j}-\sum_\pi\prod\mathbb E[X_{I_i}X_{I_j}]=o_M(A_H^4)$，对端点一致。

(d) 去掉重合指标。对有限筛代数用引理 498.2（$a=P-2$、$b=P-1$，区间示性函数之积仍是区间示性函数）。由 (a) 与 (b)，所有出现的二阶互异指标和为 $O_M(H\log H)$，$T$ 型和为 $O_M(H)$。三阶式中 $R_3$ 以外的项为 $O_M(H\log^2H)=o((H\log H)^{3/2})$；四阶式中 $R_4-\sum_\pi\prod R_2$ 以外的项为 $o_M(H^2\log^2H)$（$aR_3$ 项由三阶结论控制，$a^2R_2$ 与 $(a^2-2b)R_2$ 项为 $O_M(H\log^3H)$，末项为 $O_M(H\log^3H)$）。结合 (c) 与 (b) 换回完整奇异级数，得 (498.6)–(498.7)。证毕。

令 $\eta_M(H)\to0$ 为单调不增函数，同时控制 (498.6)–(498.7) 中归一化后的 $o$ 项。

**引理 498.4（带 BV 权的算术传递）。** 设 $\mathrm{HL}_4(\beta)$，$H$ 为整数，$N^\alpha\le H\le N^\beta$，$S_I(n)=\sum_{d/H\in I}\Lambda_0(n+d)$。对 $k=3,4$ 与 $s\in\mathbb R$，令 $\Phi_k(s;\mathbf I)$ 为按引理 498.2 展开 $\prod_{j\le k}\sum_{d/H\in I_j}Y_d$ 的形式值：不同指标之积赋值 $\mathfrak S_0$，重复指标按 $Y_d^2=(s-2)Y_d+(s-1)$ 化简。则

$$
\sum_{N<n\le2N}w(n/N)\prod_{j=1}^kS_{I_j}(n)=\int_N^{2N}w(x/N)\,\Phi_k(\log x;\mathbf I)\,dx+O\bigl(\|w\|_{\mathrm{BV}}N^{1/2+\varepsilon}H^k\bigr),
\tag{498.8}
$$

常数依赖 $\alpha,\beta,M,\varepsilon$ 与 (498.1) 的常数，关于区间端点一致。

证明。令 $m=n+d$、$\lambda=\log n$。若 $\Lambda(m)\in\{0,\log m\}$，则 $Y=\Lambda(m)-1$ 满足 $Y^2=(z-2)Y+(z-1)$（$z=\log m$），从而 $Y^r=a_r(z)Y+b_r(z)$，其中 $a_r(z)=((z-1)^r-(-1)^r)/z$、$b_r=a_r+(-1)^r$ 为多项式。把 $z$ 换成 $\lambda$ 的误差为 $O_r((H/N)(\log N)^{r-1})$。真素数幂 $p^e$（$e\ge2$）在 $[1,3N]$ 中至多 $O(\sqrt N\log N)$ 个；在真素数幂处使用上述二次化简产生的误差只在化简某个重复指标时出现。把 $k$ 个指标按相等关系分成 $j$ 个不同位移，相应 $\log n$ 系数多项式的次数至多 $k-j$，展开中心化乘积只出现至多 $j\le4$ 个不同位移的相关。对 (498.1) 作分部求和（$w(x/N)p(\log x)$ 的上确界与变差 $\ll\|w\|_{\mathrm{BV}}(\log N)^{k-j}$），相关误差总计 $\ll\|w\|_{\mathrm{BV}}N^{1/2+\varepsilon}\sum_{j\le k}H^j(\log N)^{k-j}$；真素数幂误差 $\ll\|w\|_\infty\sqrt NH^{k-1}(\log N)^{k+1}$；对数替换误差 $\ll\|w\|_\infty H^k(\log N)^{k-1}$。由 $H\ge N^\alpha$，这些都被 (498.8) 的误差控制。证毕。

**定理 498.1 的证明。** 令 $L=\log N$、$T_{ij}=\#\{d:d/H\in I_i\cap I_j\}=H\sigma(I_i,I_j)+O(1)$。由引理 498.3，对 $s\in[L,L+\log2]$，$R_2(I_i,I_j)+(s-1)T_{ij}=H(s-\log H)\sigma(I_i,I_j)+O_M(H)$。由引理 498.2 的三阶式，$|\Phi_3(s;\mathbf I)|\le C_M[\eta_M(H)(HL)^{3/2}+HL^2]$；由四阶式（重合类型的全部项保留在误差中），$\Phi_4(s;\mathbf I)=\sum_\pi\prod[R_2+(s-1)T]+O_M(\eta_M(H)H^2L^2+HL^3)$，代入上式并用 $HL^3=O_\alpha(H^2L)$，

$$
\Phi_4(s;\mathbf I)=H^2(s-\log H)^2\,\mathcal W_4(\mathbf I)+O_{\alpha,M}\bigl(\eta_M(H)H^2L^2+H^2L\bigr).
$$

不同位移的二阶主项为 $-H\log H\,\sigma$，重合位移补回 $H\log n\,\sigma$，四阶配对使用的方差是 $H\log(n/H)$。由引理 498.4，离散三阶矩除以 $N(HL)^{3/2}$ 后至多 $C\|w\|_{\mathrm{BV}}[\eta_M(H)+\sqrt{L/H}+N^{-1/2+\varepsilon}H^{3/2}L^{-3/2}]$；离散四阶矩的归一化误差至多 $C\|w\|_{\mathrm{BV}}[\eta_M(H)+1/L+N^{-1/2+\varepsilon}H^2L^{-2}]$，这里用到 $x\in[N,2N]$ 上 $(\log(x/H)/L)^2=\kappa_{N,H}^2+O(1/L)$。取 $0<\varepsilon<\frac12-2\beta$，则 $N^{-1/2+\varepsilon}H^2\le N^{-1/2+\varepsilon+2\beta}\to0$；这是本方法的界 $\beta<\frac14$。

连续取样：若 $x=n+t$（$0\le t<1$），每个端点至多跨过一个整数，$|\Delta_{H,I}(x)-S_I(n)|\le2\log(4N)+2$，归一化后的 $L^4$ 误差为 $O_M(\sqrt{\log N/H})$；四个相同区间与 $w=1$ 的离散四阶式给出一致 $L^4$ 界，乘积的望远镜展开与 Hölder 不等式允许把离散增量换成连续增量。宏观权的单元误差满足 $\sum_n\int_n^{n+1}|w(x/N)-w(n/N)|\,dx\le\operatorname{Var}w$，结合粗界 $|Z_{N,H}|\ll_M\sqrt{H\log N}$，$k$ 阶乘积的权替换误差至多 $O_M(\|w\|_{\mathrm{BV}}(H\log N)^{k/2}/N)\to0$。实数 $H$ 换成 $\lfloor H\rfloor$ 只使物理端点 $x+aH$、$x+bH$ 移动 $O_M(1)$，增量变化 $O_M(\log N)$，同样处理。证毕。

**推论 498.5（单长度接口）。** 设 $\mathrm{HL}_4(\beta)$。则 (490.2) 在 $\alpha<\theta<\beta$ 的带上成立，且对 $\mathsf B=1-\gamma-\log(2\pi)$（Montgomery–Soundararajan 2004 定理 3 的次项常数），使在 $Y^\alpha\le v\le Y^\beta$ 上一致地 (497.6) 成立。因此对 $\alpha<\theta<\beta<\frac14$，

$$
\mathrm{HL}_4(\beta)\ \Longrightarrow\ (490.2),\ (497.6),\ (\mathrm L_4),\ (\mathrm F_3),\ (\mathrm F_4),
\tag{498.9}
$$

从而定理 494.2 的结论在 $\mathrm{HL}_4(\beta)$ 下对 $E=\psi-\mathrm{id}$ 与 $\alpha<\theta<\beta<\frac14$ 成立。

证明。Montgomery–Soundararajan 2004 定理 3 在其相关误差假设 (20) 下，对整数长度 $\log Y\le K\le Y^{1/k}$ 给出 $\sum_{n\le Y}D_K(n)^k$（$k=2,4$）带显式误差的渐近；$k=4$ 时主项为 $3K^2\int_1^Y(\log(y/K)+\mathsf B)^2dy$，误差除以 $YK^2\log^2(Y/K)$ 后在 $Y^\alpha\le K\le Y^\beta$ 上一致趋于零（$\beta<\frac14$）。取 $K=\lfloor v\rfloor$；连续取样的替换 $|D_v(x)-D_K(\lfloor x\rfloor)|\ll\log Y$ 由 Hölder 不等式与四阶上界控制，主项中 $K$ 换成 $v$ 的误差为 $O(Yv\log^2Y)$。得 (497.6)；$k=2$ 同理给出 (490.2)。$(\mathrm L_4)$ 由引理 497.5 得到，$(\mathrm F_3)$、$(\mathrm F_4)$ 由定理 498.1 得到；再由推论 497.4 与引理 497.5，定理 494.2 的假设全部成立。证毕。

**推论 498.6（均方误差即足够）。** 定理 498.1 中的 $\mathrm{HL}_4(\beta)$ 可换成：对每个 $\varepsilon>0$、$M\ge1$、$1\le r\le4$，一致地对 $1\le K\le MN^\beta$、$N\le y\le2N$，

$$
\sum_{\substack{1\le d_1,\dots,d_r\le K\\ \text{两两不同}}}|E_r(y;\mathbf d)|^2\le C_{\varepsilon,M}N^{1+2\varepsilon}K^r ,
\tag{498.10}
$$

其中 $E_r(y;\mathbf d)$ 为 (498.1) 左边的相关误差。

证明。在含 $j$ 个不同位移的重合类型中，中心化展开的一项使用其中 $r$ 个相关位移，其余位移的求和至多给出 $K^{j-r}$。由 Cauchy–Schwarz，$K^{j-r}\sum_{\mathbf d_r}|E_r|\le K^{j-r}K^{r/2}(\sum|E_r|^2)^{1/2}\le C^{1/2}N^{1/2+\varepsilon}K^j$，这正是引理 498.4 所需的误差；分部求和只用 $N\le y\le2N$。其余不变。证毕。

**范围。** 本节的算术结论以 $\mathrm{HL}_4(\beta)$（或 (498.10)）为条件，且只覆盖 $0<\theta<\frac14$，不覆盖 §481 的 $\theta=4/5$；它供应三、四阶接口，不给出全阶联合中心极限。外部输入为：Montgomery–Soundararajan 2004 的定理 1（有限筛矩，(15)）、定理 2 与 (16)（二阶中心化奇异级数平均）、定理 3（单长度矩）；Kuperberg arXiv:2301.06095 定理 1.3（光滑权有限筛矩的配对公式）。Gallagher [On the distribution of primes in short intervals, Mathematika 23 (1976), 4–9] 处理对数长度的 Poisson 统计；Chan [A note on primes in short intervals, Int. J. Number Theory 2 (2006), 105–110] 把逐位移误差弱化为均方误差，推论 498.6 是同一机制在重叠区间混合矩上的形式；Leung [Joint distribution of primes in multiple short intervals, Adv. Math. 490 (2026), 110847] 在 RH 与 LI 下处理比例长度区间与对数取样；Leung [Pseudorandomness of primes at large scales, arXiv:2407.05380] 定理 2.1 在 HL 下给出对数长度（Poisson 区域）的混合矩；de la Bretèche [arXiv:2410.02480] 给出更精细的标量三阶矩分析。不交区间的联合矩经细分与可加性即可延伸到重叠区间，故重叠本身不是区别所在。本节在这些结果之上给出：多项式长度、端点一致的锐截断区间、宏观有界变差权与固定二倍区间连续取样下的三、四阶混合矩（引理 498.3 与定理 498.1），引理 498.2 是证明中所用的显式代数记账；由此在 $\alpha<\theta<\beta<\frac14$ 上推出 $(\mathrm F_3)$、$(\mathrm F_4)$ 与定理 494.2 的结论。
## 499. 逐阶均方相关下的算术传递与三分之一次幂以下的三阶矩

沿用 §498 的 $\Lambda_0,S_I,\Delta_{H,I},Z_{N,H},\sigma$ 与 $\|w\|_{\mathrm{BV}}$。本节把阶数与长度上界分别指定，不沿用 §498 开头的 $\beta<1/4$ 约定。为区分相关误差假设与奇异级数平均，允许 $\mathcal S$ 为有限正整数集上的实函数，满足 $\mathcal S(\varnothing)=1$、$\mathcal S(\{d\})=1$；记

$$
\mathcal S_0(D)=\sum_{J\subseteq D}(-1)^{|D|-|J|}\mathcal S(J),\qquad
E_r^{\mathcal S}(y;\mathbf d)=\sum_{1\le n\le y}\prod_{i=1}^r\Lambda(n+d_i)-y\mathcal S(\{d_1,\ldots,d_r\}).
$$

取 $\mathcal S=\mathfrak S$ 即为 §498 的奇异级数及相关误差。

**逐阶均方假设 $\mathrm{MS}_q(\beta;\mathcal S)$。** 固定整数 $q\ge1$。对每个 $\varepsilon>0$ 与 $M\ge1$，存在 $C_{\varepsilon,M}>0$ 与 $N_0$，使对所有实数 $N\ge N_0$、整数 $1\le r\le q$、整数 $1\le K\le MN^\beta$ 及实数 $N\le y\le2N$，

$$
\sum_{\substack{1\le d_1,\ldots,d_r\le K\\d_1,\ldots,d_r\text{ 两两不同}}}
 |E_r^{\mathcal S}(y;\mathbf d)|^2
 \le C_{\varepsilon,M}N^{1+2\varepsilon}K^r .
\tag{499.1}
$$

常数可以依赖固定的 $q,\beta,\mathcal S$，不依赖 $r,K,y$。省略 $\mathcal S$ 时取 $\mathcal S=\mathfrak S$；$\mathrm{MS}_4(\beta)$ 正是 (498.10)，$\mathrm{MS}_3(\beta)$ 只要求其中 $r\le3$ 的部分。

**定理 499.1（每个有限阶的带权算术传递）。** 设 $q\ge1$、$0<\alpha<\beta<1$、$\mathrm{MS}_q(\beta;\mathcal S)$，并固定 $M\ge1$。对整数 $H\ge1$ 与 $I_j=(a_j,b_j]\subseteq[0,M]$（允许 $a_j=b_j$），把 (498.8) 中的形式值延伸到任意 $1\le k\le q$：展开 $\prod_{j=1}^k\sum_{d/H\in I_j}Y_d$，以 $Y_d^2=(s-2)Y_d+(s-1)$ 化简各个幂，再将互异指标的乘积 $\prod_{d\in J}Y_d$ 赋值为 $\mathcal S_0(J)$。所得值记为 $\Phi_k^{\mathcal S}(s;\mathbf I)$。则对每个 $\varepsilon>0$，当 $N\to\infty$ 时，

$$
\sum_{N<n\le2N}w(n/N)\prod_{j=1}^kS_{I_j}(n)
 =\int_N^{2N}w(x/N)\Phi_k^{\mathcal S}(\log x;\mathbf I)\,dx
 +O_{q,\alpha,\beta,M,\varepsilon,\mathcal S}
 \bigl(\|w\|_{\mathrm{BV}}N^{1/2+\varepsilon}H^k\bigr),
\tag{499.2}
$$

其中 $w:\mathbb R\to\mathbb R$ 有界变差、在 $[1,2]$ 外为零；常数及充分大的 $N$ 的门槛关于整数 $N^\alpha\le H\le N^\beta$、全部 $1\le k\le q$、区间端点与 $w$ 一致。特别地，$\mathcal S=\mathfrak S$ 时，这就是 (498.8) 对每个 $1\le k\le q$ 的形式。

**证明。** 先对任意幂次建立二次化简。令 $a_0=0,b_0=1$，递推定义多项式

$$
a_{r+1}(z)=(z-2)a_r(z)+b_r(z),\qquad b_{r+1}(z)=(z-1)a_r(z).
$$

若 $Y^2=(z-2)Y+(z-1)$，归纳给出 $Y^r=a_r(z)Y+b_r(z)$。对 $r\ge1$，两多项式次数均至多 $r-1$；若 $\|p\|_1$ 表示系数绝对值之和，则递推与 $a_1=1,b_1=0$ 给出

$$
\|a_r\|_1+\|b_r\|_1\le5^{r-1},\qquad
|a_r(z)|+|b_r(z)|\le5^{r-1}(1+|z|)^{r-1}.
\tag{499.3}
$$

因此对含 $j$ 个不同位移的 $k$ 元组，化简后的系数多项式次数至多 $k-j$，且 $k\le q$ 时所有系数来自一个固定有限族。这给出了任意有限阶所需的系数控制。

令 $P=\{1,\ldots,K\}$。固定 $R\subseteq P$、$|R|=r\le k$；值域包含 $R$ 的 $k$ 元组至多有 $k^rK^{k-r}$ 个：为 $R$ 的各元素各选一个出现位置，所选位置必不同，共至多 $k^r$ 种，其余 $k-r$ 个坐标各有 $K$ 种选择。此界对区间盒的任意子族仍成立。另一方面，(499.1) 与 Cauchy–Schwarz 给出

$$
\sum_{\substack{R\subseteq P\\|R|=r}}|E_r^{\mathcal S}(y;R)|
 \le K^{r/2}\left(\sum_{\substack{1\le d_1,\ldots,d_r\le K\\\text{两两不同}}}
 |E_r^{\mathcal S}(y;\mathbf d)|^2\right)^{1/2}
 \ll N^{1/2+\varepsilon/2}K^r,
\tag{499.4}
$$

这里在 (499.1) 中使用 $\varepsilon/2$，无序集上的误差与其任一排序相同。先对中心化乘积作容斥，再按实际使用的 $r$ 个相关位移求和；乘以上面的 $k^rK^{k-r}$，各阶误差总和为 $O_q(N^{1/2+\varepsilon/2}K^k)$。空集项的误差是 $\lfloor y\rfloor-y$，绝对值至多 $1$，也满足所需总界。对每个系数多项式 $p$ 作 BV 分部求和，权 $w(x/N)p(\log x)$ 的上确界加变差为 $O_q(\|w\|_{\mathrm{BV}}(1+\log N)^{m_q})$，其中 $m_q$ 固定。分部求和只使用 $N\le y\le2N$，并不要求更大截断范围上的均方假设。取 $K=\lfloor MH\rfloor\asymp_M H$，再用 $(1+\log N)^{m_q}=O_{q,\varepsilon}(N^{\varepsilon/2})$，得到二次化简值与形式积分之间的 (499.2) 型误差。

最后核对实际算术乘积与二次化简值。固定一个值 $e\in P$，当 $k\ge2$ 时，$e$ 出现至少两次的元组数至多 $k^2K^{k-2}$：选择两个不同位置并把它们都固定为 $e$，再任取其余坐标；$k=1$ 时此类元组为空。只有这些重复指标需要使用二次关系。除真素数幂外，$Y=\Lambda(n+e)-1$ 在 $z=\log(n+e)$ 处满足该关系；真素数幂在 $[1,3N]$ 中有 $O(\sqrt N\log N)$ 个。结合重复值计数，与引理 498.4 同样得到真素数幂例外误差

$$
O_{q,M}\bigl(\|w\|_\infty\sqrt N H^{k-1}(\log N)^{k+1}\bigr).
$$

又 $MH\le N$ 最终成立；把各个 $\log(n+e)$ 换为 $\log n$，利用多项式导数界得到误差 $O_{q,M}(\|w\|_\infty H^k(\log N)^{k-1})$。以更小的正指数使用均方假设并吸收固定对数幂，两项均受 (499.2) 的误差控制。证毕。

**引理 499.2（三阶乘积的二阶控制替换）。** 设 $f_i,g_i:\mathbb R\to\mathbb R$（$i=1,2,3$）在 $[1,2]$ 上属于 $L^2$，并且两个三重乘积 $\prod_{i=1}^3f_i$、$\prod_{i=1}^3g_i$ 分别在 $[1,2]$ 上可积。设 $K,e,B\in\mathbb R$，$e\ge0$、$B\ge0$，且对每个 $i$，

$$
\int_1^2|f_i(t)|^2\,dt\le K,\qquad
\int_1^2|g_i(t)|^2\,dt\le K,\qquad
|f_i(t)-g_i(t)|\le e\quad(1\le t\le2).
\tag{499.5}
$$

若 $w$ 在 $[1,2]$ 上可积，且对每个 $t\in[1,2]$ 有 $|w(t)|\le B$，则

$$
\left|\int_1^2w(t)\prod_{i=1}^3f_i(t)\,dt
      -\int_1^2w(t)\prod_{i=1}^3g_i(t)\,dt\right|\le6BeK .
\tag{499.6}
$$

这里只要求两个三重乘积可积，不要求其三阶矩上界或各因子的四阶矩上界；$K\ge0$ 已由平方积分条件推出。

**证明。** 望远镜恒等式为

$$
f_1f_2f_3-g_1g_2g_3
 =(f_1-g_1)f_2f_3+g_1(f_2-g_2)f_3+g_1g_2(f_3-g_3).
$$

由 $|uv|\le(|u|^2+|v|^2)/2$（二项的 Cauchy–Schwarz 不等式）及 (499.5)，逐点有

$$
|f_1f_2f_3-g_1g_2g_3|
 \le e\bigl(|f_2f_3|+|g_1f_3|+|g_1g_2|\bigr)
 \le e\sum_{i=1}^3\bigl(|f_i|^2+|g_i|^2\bigr).
$$

各平方可积，两个三重乘积也分别可积；乘以有界可积权后，积分之差可以写成差的积分。取绝对值，以 $|w|\le B$ 控制，再对上式积分，六个平方积分各至多 $K$，即得 (499.6)。证毕。

**定理 499.3（三分之一次幂以下的三阶混合矩）。** 设 $0<\alpha<\beta<1/3$、$\mathrm{MS}_3(\beta;\mathcal S)$，并保留定理 498.1 所用的区间奇异级数输入：将引理 498.3 中的 $\mathfrak S_0$ 换成 $\mathcal S_0$ 后，(498.6)–(498.7) 关于全部区间端点一致成立。确切地，对每个 $M\ge1$，二阶式的误差对所有实数 $H\ge1$ 至多 $C_MH$；存在非负、在 $[2,\infty)$ 上单调不增且趋于零的 $\eta_M(H)$，使 $H\ge2$ 时三阶式的绝对值至多 $\eta_M(H)(H\log H)^{3/2}$，四阶式相对配对和及相对 $H^2\log^2H\,\mathcal W_4$ 的两个误差各至多 $\eta_M(H)H^2\log^2H$。则对每个 $M\ge1$、$\delta>0$，存在 $N_0$，使所有实数 $N\ge N_0$、实数 $N^\alpha\le H\le N^\beta$、$B\ge0$、$\|w\|_{\mathrm{BV}}\le B$ 及 $I_1,I_2,I_3\subseteq[0,M]$ 都满足

$$
\left|\frac1N\int_N^{2N}w(x/N)\prod_{j=1}^3 Z_{N,H}(I_j;x)\,dx\right|\le B\delta .
\tag{499.7}
$$

这里 $w$ 实值且在 $[1,2]$ 外为零；区间允许为空或任意重叠。结论先对整数 $H$ 成立，并延伸至上述全部实数 $H$。特别地，对 $\mathcal S=\mathfrak S$，(498.2) 在 $0<\alpha<\beta<1/3$ 上成立，余项关于长度、端点及 $\|w\|_{\mathrm{BV}}\le1$ 一致。上述奇异级数平均是保留的外部输入，并非由 $\mathrm{MS}_3$ 推出；它包括四阶奇异级数配对估计，但不要求四阶算术相关的均方假设。

**证明。** 令 $L=\log N$。先设 $H$ 为整数。用引理 498.2 的三阶恒等式与所假设的二、三阶奇异级数估计，对 $L\le s\le L+\log2$ 一致地有

$$
|\Phi_3^{\mathcal S}(s;\mathbf I)|
 \ll_M \eta_M(H)(HL)^{3/2}+HL^2.
$$

定理 499.1 取 $q=3,k=3$，将离散矩除以 $N(HL)^{3/2}$ 后得到

$$
\left|\frac{\sum_{N<n\le2N}w(n/N)\prod_{j=1}^3S_{I_j}(n)}{N(HL)^{3/2}}\right|
 \ll\|w\|_{\mathrm{BV}}\left[\eta_M(H)+\sqrt{L/H}
       +N^{-1/2+\varepsilon}H^{3/2}L^{-3/2}\right].
\tag{499.8}
$$

选择 $0<\varepsilon<1/2-3\beta/2$，则最后一项至多 $N^{-1/2+\varepsilon+3\beta/2}L^{-3/2}\to0$；前两项由 $H\ge N^\alpha$ 也一致趋零。三阶算术误差要求的是 $\beta<1/3$。

为作连续取样，仅需一致二阶界。定理 499.1 取 $k=2$，配合二阶奇异级数估计，给出归一化离散增量的均方界；其算术误差为 $O(N^{-1/2+\varepsilon}H/L)$，在上述 $\varepsilon$ 的选择下趋零。单元端点误差以粗界 $O_M(HL/N)$ 控制，也趋零。因此对 $1\le t\le2$，令

$$
f_j(t)=Z_{N,H}(I_j;Nt),\qquad
g_j(t)=\frac{S_{I_j}(\lfloor Nt\rfloor)}{\sqrt{HL}},
$$

有 $\int_1^2|g_j|^2\le C_M$。每个物理端点从 $\lfloor Nt\rfloor$ 移到 $Nt$ 时跨过的整数数目有绝对上界，连同中心化长度的取整误差给出

$$
\sup_{1\le t\le2}|f_j(t)-g_j(t)|
 \ll_M\sqrt{L/H}=:e_{N,H}\longrightarrow0.
$$

由 $|f_j|^2\le2|g_j|^2+2e_{N,H}^2$，$f_j$ 的平方积分也一致有界。对每个固定 $N,H$，这些函数在紧区间上有界可测，故两个三重乘积分别可积；这不提供也不需要一致四阶矩界。应用引理 499.2，连续矩与单元常值矩相差 $O_M(Be_{N,H})=o(B)$。

把单元上的 $w(t)$ 换成 $w(n/N)$，BV 变差控制所有单元的权误差总和；用粗界 $|g_j|\ll_M\sqrt{HL}$，连同二倍区间两端的不完整单元，归一化误差至多 $O_M(B(HL)^{3/2}/N)=o(B)$。结合 (499.8) 得整数长度的 (499.7)。整个三阶连续替换只用了平方积分上界，无须借助四阶矩及其 $\beta<1/4$ 的长度限制。

对实数 $H$，令 $J=\lfloor H\rfloor$、$I'_j=(Ha_j/J,Hb_j/J]$。充分大时 $J\ge N^{\alpha/2}$、$J\le N^\beta$、$I'_j\subseteq[0,2M]$，且物理区间完全相同，故

$$
Z_{N,H}(I_j;x)=\sqrt{J/H}\,Z_{N,J}(I'_j;x).
$$

用指数带 $(\alpha/2,\beta)$、窗口 $2M$ 的整数长度结论，乘以 $(J/H)^{3/2}\le1$，即得实数长度结论。证毕。

**推论 499.4（固定尺度三阶接口）。** 取 $\mathcal S=\mathfrak S$，设 $0<\theta<\beta<1/3$、$\mathrm{MS}_3(\beta)$，并保留定理 499.3 的区间奇异级数输入。则对 $E=\psi-\mathrm{id}$，§497 的 $(\mathrm F_3)$ 成立：对每个 $M>0$、$c_1,c_2,c_3\in[0,M]$ 与 $1\le u<v\le2$，

$$
\lim_{X\to\infty}\mathbb E_{\mu_X}\left[\mathbf1_{[u,v]}(U_X)
             \prod_{j=1}^3\widetilde B_X(c_j)\right]=0,
\qquad d\mu_X(x)=\frac{dx}{x\log2},\quad U_X(x)=x/X.
\tag{499.9}
$$

**证明。** 在定理 499.3 中取 $N=X$、$H=X^\theta$、$\alpha=\theta/2$、窗口 $\max\{1,M\}$、$I_j=(0,c_j]$，并取 $w(t)=\mathbf1_{[u,v]}(t)/(t\log2)$。该权的 BV 范数至多 $3/\log2$，且 $Z_{X,X^\theta}((0,c_j];x)=\widetilde B_X(c_j,x)$。换元 $t=x/X$，(499.7) 的积分恰为 (499.9) 的期望；令 $\delta\downarrow0$ 即得结论。证毕。

**范围。** Montgomery–Soundararajan [Primes in short intervals, Comm. Math. Phys. 252 (2004), 589–617, doi:10.1007/s00220-004-1222-4] 定理 3 在逐位移相关误差假设下，对 $\log N\le H\le N^{1/k}$ 给出单一区间的 $k$ 阶矩及显式误差；Chan [A note on primes in short intervals, Int. J. Number Theory 2 (2006), 105–110, doi:10.1142/S1793042106000437] 将该单一区间论证的逐位移误差弱化为均方误差。二次化简、重复指标分类与 Cauchy–Schwarz 属于这些方法的共同机制。本节在此基础上给出任意固定有限阶、锐截断区间端点一致、宏观 BV 权下的形式算术传递，以及只用二阶矩控制连续替换的三阶混合矩与固定尺度接口；不将单一区间的先例或均方弱化本身作为新结论。区间奇异级数输入沿用引理 498.3，其文献前置仍包括 Montgomery–Soundararajan 的有限筛矩与二阶奇异级数平均，以及 Kuperberg [Sums of singular series along arithmetic progressions and with smooth weights, arXiv:2301.06095] 定理 1.3；这些输入没有由相关误差假设消去。任意阶的形式算术传递不等于任意阶的高斯矩渐近，本节不主张全阶高斯极限或随机过程收敛；四阶矩结论仍使用 $\mathrm{MS}_4(\beta)$ 与 $\beta<1/4$，三阶的改进不扩大四阶结论，也不覆盖 $\theta=4/5$。

## 追加锚（本行以下为增补区）

## 500. 二次关系下任意有限阶的配对缺陷传播与低阶障碍

**定义 500.1（互异指标矩、配对多项式与部分配对）。** 固定整数 $k\ge2$，令 $K=\{1,\ldots,k\}$。设 $D$ 有限，$\mathcal A$ 为交换含幺实代数，$\ell:\mathcal A\to\mathbb R$ 为实线性泛函，且

$$
\ell(1)=1,\qquad \ell(Y_d)=0,\qquad Y_d^2=aY_d+b1\quad(d\in D).
$$

不要求 $\ell$ 正性或 $Y_d$ 独立。给定 $f_i:D\to\mathbb R$，$|f_i(d)|\le1$；对非空 $B\subseteq K$，令 $f_B=\prod_{i\in B}f_i$、$T_B=\sum_{d\in D}f_B(d)$。定义有序互异指标和

$$
R_r(g_1,\ldots,g_r)=
\sum_{\substack{d_1,\ldots,d_r\in D\\d_1,\ldots,d_r\text{ 两两不同}}}
\left(\prod_{j=1}^rg_j(d_j)\right)\ell\left(\prod_{j=1}^rY_{d_j}\right),\qquad R_0=1.
$$

对 $U\subseteq K$，记

$$
R_U=R_{|U|}((f_i)_{i\in U}),\qquad
V_U=\ell\left(\prod_{i\in U}\sum_{d\in D}f_i(d)Y_d\right),\qquad V_k=V_K.
$$

交换性与重编号使 $R_U$ 不依赖 $U$ 的排序，且 $R_\varnothing=V_\varnothing=1$。对对称数组 $c=(c_{ij})$，令

$$
\mathcal W_U(c)=\sum_{\pi\in\mathcal P_2(U)}\prod_{\{i,j\}\in\pi}c_{ij},\qquad
\mathcal W_U^R=\mathcal W_U((R_{\{i,j\}})),\qquad
\mathcal W_U^V=\mathcal W_U((V_{\{i,j\}})),\qquad
\Delta_U=R_U-\mathcal W_U^R.
\tag{500.1}
$$

这里 $\mathcal P_2(U)$ 是 $U$ 的完美配对集；空集的配对多项式为 $1$，奇数大小时为 $0$。因此 $|U|=0,1,2$ 时 $\Delta_U=0$。$K$ 的部分配对 $P$ 是互不相交的二元子集组成的集合，记

$$
U(P)=K\setminus\bigcup_{e\in P}e,\qquad T_P=\prod_{e\in P}T_e,\qquad T_\varnothing=1.
$$

**定理 500.2（有限任意阶缺陷恒等式）。** 在定义 500.1 的条件下，设 $C\ge1$、$H\ge L\ge1$，且

$$
|D|\le CH,\qquad |a|,|b|\le CL,\qquad
|R_r(f_{B_1},\ldots,f_{B_r})|\le C(HL)^{r/2}
\tag{500.2}
$$

对全部 $2\le r\le k-1$ 与两两不交的非空 $B_1,\ldots,B_r\subseteq K$ 成立。则存在 $E_k$，使

$$
\begin{aligned}
V_k&=\sum_{P\text{ 部分配对}}b^{|P|}T_PR_{U(P)}+E_k,\\
V_k-\mathcal W_K^V&=\sum_{P\text{ 部分配对}}b^{|P|}T_P\Delta_{U(P)}+E_k,\\
|E_k|&\le\mathfrak C_{k,C}(HL)^{k/2}\left(\sqrt{L/H}+H^{-1}\right),\qquad
\mathfrak C_{k,C}=2^kk^kk!(C+1)^{k+1}.
\end{aligned}
\tag{500.3}
$$

这里不要求 $R_k$ 的大小上界；顶阶项在两条恒等式中分别原样保留为 $R_K$ 与 $\Delta_K$。

**证明。** 令 $s=\sqrt{HL}$、$\rho=\sqrt{L/H}$。先递推定义

$$
(u_0,v_0)=(0,1),\qquad (u_{m+1},v_{m+1})=(au_m+v_m,bu_m).
$$

由二次关系归纳，$Y_d^m=u_mY_d+v_m1$，其中 $u_1=1,v_1=0,u_2=a,v_2=b$。对 $m\ge1$，

$$
|u_m|,|v_m|\le(C+1)^{m-1}L^{m-1}.
\tag{500.4}
$$

事实上，递推中 $|au_m+v_m|\le(CL+1)(C+1)^{m-1}L^{m-1}\le(C+1)^mL^m$，$|bu_m|$ 也满足同一上界。

令 $\Pi(K)$ 为集合分割集。按指标相等关系展开 $V_k$：固定 $\sigma\in\Pi(K)$，并令 $\mathcal B\subseteq\sigma$ 为选取 $u_{|B|}Y_d$ 的保留块，其余块选取 $v_{|B|}1$。记 $t=|\sigma|$、$r=|\mathcal B|$、$q=t-r$，则

$$
\begin{aligned}
c(\sigma,\mathcal B)&=\prod_{B\in\mathcal B}u_{|B|}\prod_{B\in\sigma\setminus\mathcal B}v_{|B|},\\
J(\sigma,\mathcal B)&=\sum_{\phi:\sigma\hookrightarrow D}
\prod_{B\in\sigma}f_B(\phi(B))\,
\ell\left(\prod_{B\in\mathcal B}Y_{\phi(B)}\right),\\
V_k&=\sum_{\sigma\in\Pi(K)}\sum_{\mathcal B\subseteq\sigma}
c(\sigma,\mathcal B)J(\sigma,\mathcal B).
\end{aligned}
\tag{500.5}
$$

若未保留块中有单点，系数因 $v_1=0$ 消失；若 $r=1$，则由中心化 $J=0$。

为使用有符号的 $R_r$ 上界，不能把相关值的绝对值移入求和。对块集 $\sigma$ 的分割 $\tau$ 定义

$$
\mu(\tau)=\prod_{A\in\tau}(-1)^{|A|-1}(|A|-1)!,\qquad
F_A=f_{\cup_{B\in A}B}.
$$

称 $\tau$ 容许，如果每个 $A\in\tau$ 至多含一个保留块。则有精确容斥式

$$
J(\sigma,\mathcal B)=\sum_{\tau\text{ 容许}}\mu(\tau)
\prod_{\substack{A\in\tau\\A\cap\mathcal B=\varnothing}}T_{\cup_{B\in A}B}\,
R_r((F_A)_{A\cap\mathcal B\ne\varnothing}).
\tag{500.6}
$$

证明此式时，先只要求保留块的指标两两不同，再插入分割格容斥

$$
\mathbf1_{\phi\text{ 单射}}=
\sum_{\tau\in\Pi(\sigma)}\mu(\tau)
\mathbf1_{\phi\text{ 在 }\tau\text{ 的各块上常值}}.
\tag{500.7}
$$

在一个大小为 $j$ 的相等类上，右侧的系数和等于 $j$ 元置换的符号和：将置换按循环分割归类，每个循环块贡献 $(-1)^{|A|-1}(|A|-1)!$。$j=1$ 时该和为 $1$，$j\ge2$ 时以一个固定换位配对而为 $0$，故 (500.7) 成立。同一循环分类还给出 $\sum_{\tau\in\Pi(\sigma)}|\mu(\tau)|=t!$。合并两个保留块的分割与已施加的互异要求冲突，因而贡献为零；其余分割中，无保留块的分量给出 $T$，有保留块的分量给出 $R_r$ 的一个权。这就证明 (500.6)。这些权的标签集合仍非空且两两不交，故确实属于 (500.2) 的适用族。

令 $e=t-|\tau|$。容许的 $\tau$ 恰有 $q-e$ 个不含保留块的分量，故 $0\le e\le q$。利用 $|T_B|\le CH$、$R_0=1$、$R_1=0$ 及 (500.2)，除 $r=k$ 的顶阶项外，有

$$
\begin{aligned}
|J(\sigma,\mathcal B)|&\le t!C^{q+1}H^qs^r,\\
\left|J(\sigma,\mathcal B)-\prod_{B\notin\mathcal B}T_B\,
R_r((f_B)_{B\in\mathcal B})\right|&\le t!C^qH^{q-1}s^r\quad(q\ge1).
\end{aligned}
\tag{500.8}
$$

第二式去掉离散分割，其余 $e\ge1$，故 $C^{q-e+1}\le C^q$ 且 $H^{q-e}\le H^{q-1}$；$q=0$ 时没有其余容许分割，差恰为零。$r=k$ 只能是全部单点且全部保留，此时 $J=R_K$，无需估计。

对未因单点系数消失的构型定义分级

$$
\delta=\sum_{B\in\mathcal B}(|B|-1)+
\sum_{B\notin\mathcal B}(|B|-2)=k-2q-r=k-2t+r\ge0.
\tag{500.9}
$$

由 (500.4)，$|c(\sigma,\mathcal B)|\le(C+1)^{k-t}L^{k-t}$。与 (500.8) 合并，并用 $k-t+q+1=k-r+1\le k+1$，得到除顶阶项外

$$
\begin{aligned}
|cJ|&\le k!(C+1)^{k+1}H^qL^{k-t}s^r\\
&=k!(C+1)^{k+1}(HL)^{k/2}(L/H)^{\delta/2}.
\end{aligned}
\tag{500.10}
$$

更精细地，(500.6) 中单个 $\tau$ 项乘上 $c$ 后的绝对值至多

$$
|\mu(\tau)|(C+1)^{k+1}(HL)^{k/2}(L/H)^{\delta/2}H^{-e}.
$$

$\delta=0$ 当且仅当所有保留块为单点、所有未保留块为二元块。因此这些构型恰由部分配对 $P$ 参数化，系数为 $b^{|P|}$；离散分割的贡献为 $b^{|P|}T_PR_{U(P)}$。$P=\varnothing$ 的顶阶项精确保留；其余构型用 (500.8) 去掉碰撞，其误差各至多 $k!(C+1)^{k+1}s^k/H$。$r=1$ 的构型与对应主项同时为零。所有 $\delta\ge1$ 的非零构型由 $\rho\le1$ 与 (500.10) 各至多 $k!(C+1)^{k+1}s^k\rho$。

分割总数至多 $k^k$：把每个标签映到其所在块的最小标签即得到单射编码；每个分割的保留块选择至多 $2^k$。分别累加上述两类误差，得到 (500.3) 的第一式与所列常数。

最后，由二次关系与中心化，$V_{\{i,j\}}=R_{\{i,j\}}+bT_{\{i,j\}}$。逐对展开完美配对的乘积，给出

$$
\mathcal W_K^V=\sum_{P\text{ 部分配对}}b^{|P|}T_P\mathcal W_{U(P)}^R.
\tag{500.11}
$$

这里“完美配对及其中选出的若干对”等价于“部分配对及余下标签的完美配对”，没有额外排序或阶乘因子；奇数 $k$ 时两边同时为零。相减即得第二条恒等式。

在 $k=2,3,4$，(500.5)–(500.11) 的精确展开分别还原 (498.4)–(498.5)。具体地，$E_2=0$；$E_3=a\sum_{\{i,j\}}R_2(f_{ij},f_\ell)+abT_{123}$；$E_4$ 恰为 (498.5) 右侧除顶阶缺陷之外的四项。四阶的较低同偶缺陷只有 $\Delta_2,\Delta_0$，它们恒为零，这正是 §498 只需顶阶配对假设的代数原因。证毕。

**推论 500.3（渐近配对传递）。** 固定 $k,C$，考虑满足定理 500.2 的一列数据，设 $L/H\to0$，并对全部 $U\subseteq K$ 满足

$$
3\le|U|\le k,\qquad |U|\equiv k\pmod2
$$

者，有 $\Delta_U=o((HL)^{|U|/2})$。则

$$
V_k=\mathcal W_K^V+o((HL)^{k/2}).
\tag{500.12}
$$

奇数 $k$ 时即 $V_k=o((HL)^{k/2})$。这些附加假设只涉及原权的子元组，不要求合并权的配对渐近；合并权只需 (500.2) 的大小界。

**证明。** $L\ge1$ 与 $L/H\to0$ 已蕴含 $H\to\infty$。由 $|bT_e|\le C^2HL$ 与 (500.3)，

$$
\frac{|V_k-\mathcal W_K^V|}{(HL)^{k/2}}
\le\sum_P C^{2|P|}\frac{|\Delta_{U(P)}|}{(HL)^{|U(P)|/2}}
+\mathfrak C_{k,C}(\sqrt{L/H}+H^{-1}).
$$

$|U(P)|\le2$ 时缺陷恒为零，其余均在假设之内，部分配对仅有有限个，故右侧趋零。具体地，若这些归一化缺陷均至多 $\varepsilon$，第一项至多 $Q_{k,C}\varepsilon$，其中

$$
Q_{k,C}=\sum_{p=0}^{\lfloor k/2\rfloor}\frac{k!}{2^pp!(k-2p)!}C^{2p}.
$$

各低阶缺陷分别消失是充分条件；在本推论的尺度极限和大小界下，必要且充分的是 (500.3) 中整个加权缺陷和除以 $(HL)^{k/2}$ 后趋零，允许不同项抵消。证毕。

**命题 500.4（五阶顶阶条件不足）。** 即使 $\ell$ 为概率期望，全部低阶有界权互异指标和满足 (500.2)，且 $R_5$ 对所有有界权恒为零，仍可能有 $V_5\ne o((HL)^{5/2})$。

**证明。** 先给出两组反例共用的构造。令 $H=n$、$L=\log n$、$D=\{1,\ldots,n\}$。取固定的有限值实随机变量 $Z$，$\mathbb EZ=0$。对充分大的整数 $n\ge\|Z\|_\infty^2$，给定 $Z$ 后独立选取符号 $\varepsilon_d\in\{-1,1\}$，概率为

$$
\mathbb P(\varepsilon_d=1\mid Z)=\frac{1+Z/\sqrt n}{2},\qquad
\mathbb E(\varepsilon_d\mid Z)=Z/\sqrt n.
$$

取有限概率空间上的实函数代数，$\ell=\mathbb E$，$Y_d=\sqrt L\,\varepsilon_d$。于是 $\ell(1)=1$、$\ell(Y_d)=0$、$Y_d^2=L$，即 $a=0,b=L$。令 $m_j=\mathbb EZ^j$、$m_0=1$。对两两不同的 $d_1,\ldots,d_j$，条件独立性给出

$$
\ell(Y_{d_1}\cdots Y_{d_j})=(L/n)^{j/2}m_j,\qquad
|R_j(g_1,\ldots,g_j)|\le|m_j|(nL)^{j/2}\quad(|g_i|\le1).
\tag{500.13}
$$

因此任一固定有限阶均可取一个与 $n$ 无关的 $C\ge1$，满足全部大小条件。

现在指定

$$
\mathbb P(Z=-2)=8/22,\qquad \mathbb P(Z=1)=13/22,\qquad
\mathbb P(Z=3)=1/22.
$$

概率和为 $1$，且逐项计算

$$
\begin{aligned}
m_1&=(-16+13+3)/22=0,\\
m_2&=(32+13+9)/22=27/11,\\
m_3&=(-64+13+27)/22=-12/11,\\
m_4&=(128+13+81)/22=111/11,\\
m_5&=(-256+13+243)/22=0.
\end{aligned}
$$

由 (500.13)，$R_5=0$ 对所有权恒成立。取全部 $f_i=1$，令 $S_n=\sum_d\varepsilon_d$、$(n)_t=n(n-1)\cdots(n-t+1)$。对一个有 $t$ 块、其中 $o$ 块大小为奇数的相等模式，先条件于 $Z$ 再取期望，所得期望为 $m_on^{-o/2}$，其指标赋值数为 $(n)_t$。若大小 $j$ 的块有 $c_j$ 个，该模式的分割数为

$$
\frac{k!}{\prod_j(j!)^{c_j}c_j!}.
\tag{500.14}
$$

五阶模式 $1^5$ 因 $m_5=0$ 消失；$2^2+1,3+2,4+1,5$ 均因 $m_1=0$ 消失。仅余 $2+1^3$ 与 $3+1^2$，重数分别为 $\binom52=10$、$\binom53=10$，两者都有三个奇块。因此

$$
\mathbb ES_n^5=10m_3n^{-3/2}\bigl((n)_4+(n)_3\bigr),\qquad
\frac{V_5}{(nL)^{5/2}}=\frac{\mathbb ES_n^5}{n^{5/2}}
\longrightarrow10m_3=-120/11\ne0.
\tag{500.15}
$$

相应的三阶缺陷 $\Delta_3=R_3$ 除以 $(nL)^{3/2}$ 趋于 $m_3$，故它未被顶阶条件消去。证毕。

**命题 500.5（六阶顶阶配对条件不足）。** 在同一概率代数构造中，可以使全部低阶大小界成立，并对所有有界权一致地有 $\Delta_K=O((HL)^3/H)$（$|K|=6$），而对全部 $f_i=1$ 有

$$
\frac{V_6-15V_2^3}{(nL)^3}\longrightarrow15(\sqrt{15}-3)\ne0.
\tag{500.16}
$$

**证明。** 沿用命题 500.4 的构造，改取 $c=15^{1/4}$，

$$
\mathbb P(Z=c)=\mathbb P(Z=-c)=\frac1{2\sqrt{15}},\qquad
\mathbb P(Z=0)=1-\frac1{\sqrt{15}}.
$$

对称性给出全部奇矩为零；偶矩为 $m_{2j}=c^{2j}/\sqrt{15}$（$j\ge1$），故 $m_2=1,m_4=\sqrt{15},m_6=15$。由 (500.13)，全部低阶大小界仍成立。

为验证顶阶条件对权一致，记 $A_i=\sum_df_i(d)$。非互异元组包含在 $\binom j2$ 个两坐标相等的集合的并中，故对全部 $|f_i|\le1$，

$$
\left|\sum_{d_1,\ldots,d_j\text{ 两两不同}}\prod_if_i(d_i)-\prod_iA_i\right|
\le\binom j2n^{j-1}.
$$

于是 $R_6=15(L/n)^3\prod_{i=1}^6A_i+O(L^3n^2)$。每个二阶和为 $(L/n)(A_iA_j-T_{ij})$；三因子乘积中非主项的绝对值总和至多 $7n^5$，乘上 $(L/n)^3$ 后为 $O(L^3n^2)$。六标签的完美配对数是 $6!/(2^33!)=15$，因此 $\mathcal W_K^R$ 有同一主项，$\Delta_K=O(L^3n^2)=O((nL)^3/n)$，常数不依赖权。

下面取全部 $f_i=1$。二阶的不同指标相关为 $m_2/n=1/n$，对角相关为 $1$，故

$$
V_2=L\left(n+\frac{n(n-1)}n\right)=L(2n-1).
$$

用 (500.14) 列出六阶全部相等模式；$t$ 为块数，$o$ 为奇块数，每一行贡献为“重数 $\times(n)_t m_on^{-o/2}$”。

| 模式 | 重数 | $t$ | $o$ |
| --- | ---: | ---: | ---: |
| $1^6$ | $1$ | $6$ | $6$ |
| $2+1^4$ | $15$ | $5$ | $4$ |
| $2^2+1^2$ | $45$ | $4$ | $2$ |
| $2^3$ | $15$ | $3$ | $0$ |
| $3+1^3$ | $20$ | $4$ | $4$ |
| $3+2+1$ | $60$ | $3$ | $2$ |
| $3^2$ | $10$ | $2$ | $2$ |
| $4+1^2$ | $15$ | $3$ | $2$ |
| $4+2$ | $15$ | $2$ | $0$ |
| $5+1$ | $6$ | $2$ | $2$ |
| $6$ | $1$ | $1$ | $0$ |

特别地，前四行的重数分别为 $1$、$\binom62=15$、$6!/((2!)^2\,2!\,2!)=45$、$6!/((2!)^3\,3!)=15$，且 $t-o/2=3$。其余各行 $t-o/2\le2$，因而总贡献为 $O(n^2)$。完整公式是

$$
\begin{aligned}
\mathbb ES_n^6={}&m_6n^{-3}(n)_6
+m_4n^{-2}\bigl(15(n)_5+20(n)_4\bigr)\\
&+m_2n^{-1}\bigl(45(n)_4+75(n)_3+16(n)_2\bigr)
+15(n)_3+15(n)_2+n.
\end{aligned}
\tag{500.17}
$$

由于 $V_6=L^3\mathbb ES_n^6$，得到

$$
\frac{V_6}{(nL)^3}\longrightarrow m_6+15m_4+45m_2+15
=75+15\sqrt{15},\qquad
\frac{15V_2^3}{(nL)^3}=15(2-1/n)^3\longrightarrow120.
$$

相减即得 (500.16)。同时，对任意四个标签及全部单位权，$\Delta_U/(nL)^2\to\sqrt{15}-3$；在 (500.3) 中，恰有十五个只含一对的部分配对把这个四阶缺陷传到六阶，且 $bT_e=nL$。这与上面的非零极限一致。证毕。

**注记 500.6（低阶接口与假设边界）。** 五、六阶反例说明 §498 的结论不能直接推广为任意固定阶的“仅顶阶”传递；它们不声称每个低阶假设分别都是必要条件。

**范围。** 按相等模式展开有限和、集合分割计数与分割格 Möbius 容斥是标准组合事实；循环与集合分割的计数约定参见 [NIST DLMF §26.8](https://dlmf.nist.gov/26.8)，上述证明已直接给出所需容斥系数与恒等式。本节的本仓推导（repo-derived）是适配二次关系和有符号互异指标界的分级 $\delta$、定量的部分配对缺陷传播恒等式，以及揭示顶阶条件不足的两组反例与矩计算；不主张这些标准组合机制的原创性，也不作历史首创主张。它本身不提供任意阶算术相关或奇异级数估计。

## 追加锚（本行以下为增补区）

## 501. 二次关系下 Wick 渐近与低阶缺陷的等价反演

本节沿用定义 500.1 的记号，并把定理 500.2 的正向传播反过来：在同一组大小界下，全部子组的配对缺陷消失与全部子组的 Wick 渐近完全等价，且两个方向都有显式常数。

**定义 501.1（子组的归一化缺陷与 Wick 偏差）。** 在定理 500.2 的条件下，令 $s=\sqrt{HL}$、$\eta=\sqrt{L/H}+H^{-1}$。对 $U\subseteq K$，令

$$
\delta(U)=\frac{|\Delta_U|}{s^{|U|}},\qquad
\omega(U)=\frac{|V_U-\mathcal W_U^V|}{s^{|U|}},\qquad
\Omega(U)=\max_{\substack{U'\subseteq U\\|U'|\ge3}}\omega(U'),
$$

其中空最大值记为 $0$。对整数 $m\ge0$、$0\le p\le m/2$，令 $N_{m,p}=\dfrac{m!}{2^pp!(m-2p)!}$，即 $m$ 元集合上恰含 $p$ 个二元组的部分配对个数。再令

$$
Q_{m,C}=\sum_{p=0}^{\lfloor m/2\rfloor}N_{m,p}C^{2p},\qquad
A_0=A_1=A_2=0,\qquad
A_m=1+\sum_{p=1}^{\lfloor m/2\rfloor}N_{m,p}C^{2p}A_{m-2p}\quad(m\ge3),
$$

并记 $M_{k,C}=\max_{3\le j\le k}\mathfrak C_{j,C}$，其中 $\mathfrak C_{j,C}$ 为定理 500.2 中阶数 $j$ 的误差常数。

**引理 501.2（配对权的大小）。** 在定理 500.2 的条件下，对任意 $U\subseteq K$ 及 $U$ 上大小为 $p$ 的部分配对 $P$，有 $|b|^p|T_P|\le C^{2p}s^{2p}$。

**证明。** 对二元组 $e=\{i,j\}$，$|f_e|\le1$，故 $|T_e|\le|D|\le CH$；又 $|b|\le CL$，所以 $|bT_e|\le C^2HL=C^2s^2$。对 $P$ 的 $p$ 个二元组相乘即得。证毕。

**定理 501.3（定量双向反演）。** 在定理 500.2 的条件下，对每个 $U\subseteq K$，

$$
\omega(U)\le Q_{|U|,C}\max_{U'\subseteq U}\delta(U')+\mathfrak C_{|U|,C}\,\eta\quad(|U|\ge2),
\tag{501.1}
$$

$$
\delta(U)\le A_{|U|}\bigl(\Omega(U)+M_{k,C}\,\eta\bigr).
\tag{501.2}
$$

**证明。** 先说明定理 500.2 可用于每个子组。对 $U\subseteq K$，$|U|\ge2$，把标签集换成 $U$、权重换成 $(f_i)_{i\in U}$。条件 (500.2) 对 $2\le r\le|U|-1$ 与 $U$ 中两两不交的非空子集成立，因为这些子集也是 $K$ 中两两不交的非空子集；其余条件不涉及标签。于是

$$
V_U-\mathcal W_U^V=\sum_{P\text{ 为 }U\text{ 的部分配对}}b^{|P|}T_P\Delta_{U(P)}+E_U,\qquad
|E_U|\le\mathfrak C_{|U|,C}\,s^{|U|}\eta,
\tag{501.3}
$$

其中 $U(P)=U\setminus\bigcup_{e\in P}e$，$|U(P)|=|U|-2|P|$。

(501.1)：对 (501.3) 取绝对值，用引理 501.2 并除以 $s^{|U|}$，得

$$
\omega(U)\le\sum_{P}C^{2|P|}\delta(U(P))+\mathfrak C_{|U|,C}\,\eta .
$$

每个 $\delta(U(P))$ 不超过 $\max_{U'\subseteq U}\delta(U')$，且大小为 $p$ 的部分配对恰有 $N_{|U|,p}$ 个，即得 (501.1)。

(501.2)：对 $|U|$ 作强归纳。$|U|\le2$ 时 $\Delta_U=0$，结论成立。设 $|U|=m\ge3$，且结论对所有更小的子组成立。在 (501.3) 中，空配对 $P=\varnothing$ 的贡献恰为 $\Delta_U$，故

$$
\Delta_U=\bigl(V_U-\mathcal W_U^V\bigr)-E_U-\sum_{P\ne\varnothing}b^{|P|}T_P\Delta_{U(P)} .
$$

除以 $s^m$ 并用引理 501.2，

$$
\delta(U)\le\omega(U)+\mathfrak C_{m,C}\,\eta+\sum_{p=1}^{\lfloor m/2\rfloor}\ \sum_{|P|=p}C^{2p}\delta(U(P)).
$$

由于 $m\ge3$，$\omega(U)\le\Omega(U)$；又 $\mathfrak C_{m,C}\le M_{k,C}$。对 $P\ne\varnothing$，$U(P)\subsetneq U$，归纳假设给出 $\delta(U(P))\le A_{m-2p}(\Omega(U(P))+M_{k,C}\eta)$，而 $\Omega(U(P))\le\Omega(U)$。合并得

$$
\delta(U)\le\Bigl(1+\sum_{p=1}^{\lfloor m/2\rfloor}N_{m,p}C^{2p}A_{m-2p}\Bigr)\bigl(\Omega(U)+M_{k,C}\eta\bigr)
=A_m\bigl(\Omega(U)+M_{k,C}\eta\bigr).
$$

归纳完成。证毕。

**推论 501.4（逐权重的渐近等价）。** 固定 $k$、$C$ 及一列满足定理 500.2 条件且 $L/H\to0$ 的数据，权重组 $f_1,\ldots,f_k$ 随下标任意选取但始终满足 $|f_i|\le1$。则以下两条等价：

1. 对全部 $U\subseteq K$，$|U|\ge3$，有 $\Delta_U=o\bigl((HL)^{|U|/2}\bigr)$；
2. 对全部 $U\subseteq K$，$|U|\ge3$，有 $V_U=\mathcal W_U^V+o\bigl((HL)^{|U|/2}\bigr)$。

**证明。** $L\ge1$ 与 $L/H\to0$ 给出 $H\to\infty$，从而 $\eta\to0$。由 (501.1)，条件 1 推出条件 2：$|U'|\le2$ 时 $\delta(U')=0$，其余 $\delta(U')\to0$，而子集只有有限个。由 (501.2)，条件 2 推出条件 1：$\Omega(U)$ 是有限个趋零量的最大值。证毕。

**注记 501.5（与 §500 反例的关系）。** 推论 501.4 说明，在二次关系与 (500.2) 的大小界下，获得全部子组 Wick 渐近所需的算术输入，恰为全部子组的互异指标配对缺陷消失，代数层面不再有其他障碍。命题 500.4、500.5 说明这一条件族不能缩减为只含顶阶的条件。本节不主张族中每一条单独都是必要条件。(501.2) 中出现的低阶缺陷 $\Delta_{U(P)}$ 只作用于原权重的子组，合并权只出现在 $T_e$ 与大小界中，这是反演能够闭合的原因。前几项常数为 $A_3=A_4=1$、$A_5=1+10C^2$、$A_6=1+15C^2$、$A_7=1+21C^2+315C^4$。

**范围。** 部分配对计数与三角递推是标准组合事实。本节的本仓推导（repo-derived）是：在二次关系与有符号互异指标大小界下，对定理 500.2 的逐子组定量反演 (501.2) 及显式递推常数。本节不主张一般 Wick 公式或矩方法的原创性。本节本身不提供任何素数模型的缺陷估计；这类估计仍须由算术输入（Hardy–Littlewood 型相关及奇异级数平均）给出。

## 追加锚（本行以下为增补区）

## 502. 有界变差位置权下全部有限阶的奇异级数配对与条件 Wick 定理

本节把引理 498.3 推广到全部有限阶，并把定理 498.1 推广为全部阶数 $\le k$ 的条件 Wick 定理。低阶缺陷不再逐阶显式记账，改用定理 500.2 与 §501 的定量反演。本节同时说明：单独的有界性不足以保证配对，所需权重类是位置有界变差类。

**定义 502.1（离散位置权与形式奇异级数矩）。** 固定 $M\ge1$、$B\ge0$。对 $H\ge1$，令 $D_H=\{1,\ldots,\lfloor MH\rfloor\}$，对 $f:D_H\to\mathbb R$ 令 $\operatorname{Var}_d(f)=\sum_{1\le d<\lfloor MH\rfloor}|f(d+1)-f(d)|$，并令

$$
\mathcal F_{H,M,B}=\{f:D_H\to\mathbb R:\ \|f\|_\infty\le1,\ \operatorname{Var}_d(f)\le B\}.
\tag{502.1}
$$

权重可随 $H$ 变化；区间示性函数 $\mathbf 1_{d/H\in I}$（$I\subseteq[0,M]$）属于 $B=2$ 的情形。对 $f_1,\ldots,f_k:D_H\to\mathbb R$ 与 $U\subseteq[k]$，沿用 §500 的记号，以 $\ell(Y_{d_1}\cdots Y_{d_r})=\mathfrak S_0(\{d_1,\ldots,d_r\})$（两两不同）作赋值，记

$$
R_U^{\mathfrak S}=\sum_{\substack{(d_i)_{i\in U}\\d_i\text{ 两两不同}}}\prod_{i\in U}f_i(d_i)\,\mathfrak S_0(\{d_i:i\in U\}),\qquad
\Delta_U^{\mathfrak S}=R_U^{\mathfrak S}-\mathcal W_U\bigl((R_{\{i,j\}}^{\mathfrak S})\bigr).
$$

**引理 502.2（乘积的变差）。** 若 $\|f_i\|_\infty\le1$，则 $\operatorname{Var}_d(\prod_{i\in A}f_i)\le\sum_{i\in A}\operatorname{Var}_d(f_i)$。特别地，$f_i\in\mathcal F_{H,M,B}$ 时，$\prod_{i\in A}f_i\in\mathcal F_{H,M,|A|B}$。

**证明。** 对相邻位置作乘积的望远镜展开，每项中其余因子的绝对值至多 $1$，求和即得。证毕。

**引理 502.3（前缀分解）。** 令 $K=\lfloor MH\rfloor$。每个 $f:D_H\to\mathbb R$ 满足

$$
f=f(K)\mathbf 1_{[1,K]}+\sum_{1\le m<K}\bigl(f(m)-f(m+1)\bigr)\mathbf 1_{[1,m]},
\tag{502.2}
$$

系数绝对值之和至多 $\|f\|_\infty+\operatorname{Var}_d(f)$。

**证明。** 在每个 $d\le K$ 处，右边望远镜求和为 $f(d)$。证毕。

$V_U$、$R_U$ 及配对多项式 $\mathcal W_U$ 对每个标签的权都是线性的（每个标签在一个完美配对中恰出现一次），故由引理 502.3，对 $\mathcal F_{H,M,B}$ 的一致估计可归结为对前缀区间权的一致估计，只多出因子 $(1+B)^{|U|}$。

**定理 502.4（全部有限阶的奇异级数配对，对位置有界变差权一致）。** 固定 $k\ge3$、$M\ge1$、$B\ge0$。存在 $\eta_{k,M,B}(H)\to0$，使对全部 $f_1,\ldots,f_k\in\mathcal F_{H,M,B}$ 与 $U\subseteq[k]$、$3\le|U|\le k$，

$$
|\Delta_U^{\mathfrak S}|\le\eta_{k,M,B}(H)\,(H\log H)^{|U|/2}.
\tag{502.3}
$$

此外，一致地

$$
R_{\{1,2\}}^{\mathfrak S}=-\log H\sum_{d\in D_H}f_1(d)f_2(d)+O_{M,B}(H),
\tag{502.4}
$$

且对 $2\le r\le k$ 与 $[k]$ 中两两不交的非空标签块 $B_1,\ldots,B_r$，

$$
R_r^{\mathfrak S}(f_{B_1},\ldots,f_{B_r})=O_{k,M,B}\bigl((H\log H)^{r/2}\bigr).
\tag{502.5}
$$

**证明。** (a) 二阶。引理 498.3(a) 对前缀区间给出 $-\min(m,n)\log H+O_M(H)$；由引理 502.3 得 (502.4)。

(b) 有限筛。取 $Y_0=((M+5)H)^{k+2}$、$Q=\prod_{p\le Y_0}p$、$P=Q/\varphi(Q)\ll_{k,M}\log H$，在模 $Q$ 均匀的 $a$ 上令 $Y_d(a)=P\mathbf 1_{(a+d,Q)=1}-1$。如引理 498.3(b)，$\mathbb EY_d=0$、$Y_d^2=(P-2)Y_d+(P-1)$、$\mathbb E\prod_{d\in\mathcal D}Y_d=\mathfrak S_{0,Q}(\mathcal D)$，且 $|\mathcal D|\le k$、直径 $O_M(H)$ 时 $|\mathfrak S_0(\mathcal D)-\mathfrak S_{0,Q}(\mathcal D)|\ll_{k,M}P^k/Y_0$。对至多 $O_M(H^k)$ 个位移组求和，换回完整奇异级数的误差为 $O(H^kP^k/Y_0)=o(1)$。以下记有限筛的相应量为 $V^Q,R^Q,\Delta^Q$。

(c) 统一的偶矩界。固定偶数 $q\ge k$，令 $X_g=\sum_dg(d)Y_d$、$A_H=\sqrt{H\log H}$。Montgomery–Soundararajan 2004 定理 1（(15)）给出 $V_q(Q;K)=\mu_qV_2(Q;K)^{q/2}+O_q(K^{q/2-1/(7q)}P^{2^q+q/2})$，且 $V_2(Q;K)\ll_MK\log H$。如引理 498.3(c) 区分 $K\ge H^{1/4}$ 与 $K<H^{1/4}$（后者用 $\|X_I\|_q\le KP$），得 $\|X_I\|_{L^q}\le C_{k,M}A_H\sqrt{|I|}+o(A_H)$，关于区间端点一致。由引理 502.3 与 Minkowski，对 $g\in\mathcal F_{H,M,kB}$ 有 $\|X_g\|_{L^q}\ll_{k,M,B}A_H$；Hölder 给出 $|V_r^Q(g_1,\ldots,g_r)|\ll A_H^r$（$r\le k$）。

(d) 区间权的配对。Kuperberg [arXiv:2301.06095] 定理 1.3 对固定 $f_j\in C_c^\infty((0,\infty))$ 与无平方因子模给出 $\mathbb E\prod_{j\le r}X_{f_j}=\sum_\pi\prod\mathbb E[X_{f_i}X_{f_j}]+O_{\mathbf f}(H^{r/2-1/(7r)}P^{2^r+r/2})$。如引理 498.3(c) 以支撑在 $(0,\infty)$ 内的平移光滑化逼近区间示性函数，用 (c) 的 $L^q$ 界、乘积望远镜展开与 Hölder 传递误差，先把端点移到有限 $\delta$-网格，令 $H\to\infty$ 再令 $\delta\downarrow0$，得

$$
V_U^Q-\mathcal W_U\bigl((V_{\{i,j\}}^Q)\bigr)=o_{k,M}(A_H^{|U|})\qquad(|U|\le k),
\tag{502.6}
$$

关于全部区间端点一致；由引理 502.3 与多重线性，对 $\mathcal F_{H,M,B}$ 一致。

(e) 合并权的大小界。对 $r$ 归纳证明：对全部 $g_1,\ldots,g_r\in\mathcal F_{H,M,kB}$，$R_r^Q(g_1,\ldots,g_r)=O(A_H^r)$。$r\le2$ 时由 (a)、(b) 成立。设对所有较小阶成立。有限筛模型满足定义 500.1，取定理 500.2 中的 $(H,L)$ 为 $(H,\log H)$：$|D_H|\le MH$，$|P-2|,|P-1|\ll\log H$，且由归纳假设与引理 502.2，(500.2) 对阶数 $<r$ 成立。定理 500.2 第一式中空配对给出 $R_r^Q$，非空部分配对项由引理 501.2 与归纳假设为 $O(A_H^r)$，误差项为 $O(A_H^r(\sqrt{\log H/H}+H^{-1}))$；再由 (c)，$R_r^Q=O(A_H^r)$。

(f) 反演。由 (e)，有限筛模型对 $\mathcal F_{H,M,B}$ 中的权满足定理 500.2 的全部条件，常数只依赖 $k,M,B$。由 (502.6)，定义 501.1 中的 $\Omega(U)$ 一致趋于零，且 $\eta=\sqrt{\log H/H}+H^{-1}\to0$。由 (501.2)，$\Delta_U^Q=o(A_H^{|U|})$ 一致成立。最后由 (b) 换回 $\mathfrak S$，得 (502.3)；(502.5) 由 (e) 与 (b) 得到。证毕。

**命题 502.5（有界权下三阶缺陷可以不消失）。** 存在满足 $|f_i|\le1$ 的位置权，使形式奇异级数模型（$\ell_s$ 以 $\mathfrak S_0$ 赋值，$a=s-2$、$b=s-1$，$s\in[L,L+\log2]$）满足定理 500.2 在 $k=3$ 时的全部条件，而

$$
\frac{\Delta_{\{1,2,3\}}^{\mathfrak S}}{(HL)^{3/2}}\longrightarrow-\frac1{32}.
\tag{502.7}
$$

因此定理 502.4 中的有界变差条件不能删去。

**证明。** 取 $M=1$、$H$ 为 $3$ 的倍数，$g(d)=\cos(2\pi d/3)$，即 $3\mid d$ 时为 $1$，否则为 $-\frac12$，故 $\sum_{d\le H}g(d)=0$。沿用 (b) 的有限筛，写 $Q=3Q'$、$P'=Q'/\varphi(Q')=\frac23P$，并令 $Y'_d(a)=P'\mathbf 1_{(a+d,Q')=1}-1$。由中国剩余定理，条件于 $a\equiv c\pmod3$ 时 $a\bmod Q'$ 均匀。若 $d\equiv-c\pmod3$，则 $Y_d=-1$；否则 $Y_d=\frac32Y'_d+\frac12$。由 $\sum_{r\not\equiv-c}g(r)=-g(-c)$，

$$
X_g=\sum_{d\le H}g(d)Y_d=-\frac H2\,g(-c)+E_c,\qquad
E_c=\frac32\sum_{r\not\equiv-c\ (3)}g(r)\sum_{\substack{d\le H\\d\equiv r\ (3)}}Y'_d .
\tag{502.8}
$$

写 $d=3m+r$；因 $3$ 在模 $Q'$ 下可逆，内层和是模 $Q'$ 的有限筛在长度 $H/3$ 的区间上的中心化和，其平移参数在模 $Q'$ 上均匀。由 Montgomery–Soundararajan 2004 定理 1，$\|E_c\|_{L^4}\ll\sqrt{H\log H}$，且 $\mathbb E[E_c\mid c]=0$。于是

$$
\mathbb E[X_g^3\mid c]=-\frac{H^3}{8}g(-c)^3+O(H^2\log H)+O\bigl((H\log H)^{3/2}\bigr),
$$

而 $\frac13\sum_{c\bmod3}g(c)^3=\frac14$，故 $V_3^Q(g,g,g)=-H^3/32+o(H^3)$。含重合指标的三元组只有 $O(H^2)$ 个，且 $|Y_d|\le P$，故 $R_3^Q(g,g,g)=-H^3/32+o(H^3)$；由 (b) 的 Euler 尾估计，$R_3^{\mathfrak S}(g,g,g)=-H^3/32+o(H^3)$。

令 $L\le H$、$L/H\to0$，取 $f_1=f_2=f_3=c_Hg$，$c_H=\sqrt{L/H}\le1$。奇数阶配对和为空，故 $\Delta_{\{1,2,3\}}^{\mathfrak S}/(HL)^{3/2}=c_H^3R_3^{\mathfrak S}(g,g,g)/(HL)^{3/2}\to-1/32$。核对 $k=3$ 时的 (500.2)：对不交非空 $B_1,B_2$，$t=|B_1|+|B_2|\ge2$，由 $\mathfrak S\ge0$ 与 Montgomery–Soundararajan 2004 的 (16)，$\sum_{d\ne e\le H}|\mathfrak S_0(\{d,e\})|\le\sum_{d\ne e}(\mathfrak S(\{d,e\})+1)=O(H^2)$，故 $|R_2^{\mathfrak S}(f_{B_1},f_{B_2})|\le c_H^tO(H^2)\le c_H^2O(H^2)=O(HL)$；又 $|D_H|=H$，$|a|,|b|=O(L)$。证毕。

由推论 501.4，这组权在 $k=3$ 上也不满足 Wick 渐近。$g$ 的变差为 $\asymp H$，不属于任何固定的 $\mathcal F_{H,M,B}$。

**定理 502.6（有界变差权的条件 Wick 定理）。** 固定 $k\ge3$、$M\ge1$、$B\ge0$、$0<\alpha<\beta<1/k$，设 $\mathrm{MS}_k(\beta)$。对 $f\in\mathcal F_{H,M,B}$ 令 $S_f(n)=\sum_{d\in D_H}f(d)\Lambda_0(n+d)$，$L=\log N$，$\Gamma_{ij}=\frac1H\sum_{d\in D_H}f_i(d)f_j(d)$。则对每个 $U\subseteq[k]$，

$$
\frac1{N(HL)^{|U|/2}}\sum_{N<n\le2N}w(n/N)\prod_{i\in U}S_{f_i}(n)
=\langle w\rangle\,\mathcal W_U\bigl(\kappa_{N,H}\Gamma\bigr)+o(1),
\tag{502.9}
$$

余项关于整数 $N^\alpha\le H\le N^\beta$、$f_i\in\mathcal F_{H,M,B}$ 与 $\|w\|_{\mathrm{BV}}\le1$ 一致。

**证明。** 定理 499.1 对区间权给出算术传递 (499.2)；其形式值 $\Phi^{\mathfrak S}$ 与左边都对每个标签的权线性，由引理 502.3，(499.2) 对 $\mathcal F_{H,M,B}$ 成立，常数多出因子 $(1+B)^{|U|}$。归一化后误差为 $O(N^{-1/2+\varepsilon}H^{|U|/2}L^{-|U|/2})$；取 $0<\varepsilon<(1-k\beta)/2$，它对全部 $|U|\le k$ 趋零。

对 $s\in[L,L+\log2]$，形式模型 $\ell_s$ 满足定义 500.1，$a=s-2$、$b=s-1=O(L)$，$|D_H|\le MH$。由 (502.5)，合并权满足 (500.2)，其中 $(H\log H)^{r/2}\le(HL)^{r/2}$；由 (502.3)，$\Delta_U^{\mathfrak S}=o((HL)^{|U|/2})$。由 (501.1)，

$$
\Phi_U^{\mathfrak S}(s;\mathbf f)=\mathcal W_U\bigl(R_{\{i,j\}}^{\mathfrak S}+(s-1)T_{ij}\bigr)+o\bigl((HL)^{|U|/2}\bigr),
$$

一致成立。由 (502.4)，$R_{\{i,j\}}^{\mathfrak S}+(s-1)T_{ij}=(s-\log H)H\Gamma_{ij}+O_{M,B}(H)$，除以 $HL$ 后为 $\kappa_{N,H}\Gamma_{ij}+O_{M,B}(L^{-1})$。配对多项式的有限乘积展开把这一误差传为 $o(1)$。对 $x$ 积分即得 (502.9)。证毕。

取区间权 $f_i=\mathbf 1_{d/H\in I_i}$，$\Gamma_{ij}=\sigma(I_i,I_j)+O(H^{-1})$。对实数 $x$ 的连续取样，按 §499 中连续替换的论证（每个单位单元内端点只跨越有界个整数；奇数阶用 $r-1$ 阶偶矩界，偶数阶用 $r$ 阶偶矩界，均由 (502.9) 给出），得

$$
\frac1N\int_N^{2N}w(x/N)\prod_{i\in U}Z_{N,H}(I_i;x)\,dx=\langle w\rangle\,\mathcal W_U\bigl(\kappa_{N,H}(\sigma(I_i,I_j))\bigr)+o(1),
\tag{502.10}
$$

关于 $N^\alpha\le H\le N^\beta$（实数）、$I_i\subseteq[0,M]$ 与 $\|w\|_{\mathrm{BV}}\le1$ 一致。$k=4$ 时这就是 (498.2)–(498.3)。

**推论 502.7（共同尺度上的条件 Gaussian 极限）。** 设对每个 $q\ge1$ 存在 $\beta_q>0$ 使 $\mathrm{MS}_q(\beta_q)$ 成立，且 $H/\log N\to\infty$、$\log H/\log N\to0$。固定 $m$，设 $f_{1,N},\ldots,f_{m,N}\in\mathcal F_{H,M,B}$ 且 $\Gamma_{ij}\to\Gamma^\ast_{ij}$。当 $n$ 在 $(N,2N]$ 的整数上均匀取样时，

$$
\Bigl(\frac{S_{f_{1,N}}(n)}{\sqrt{H\log N}},\ldots,\frac{S_{f_{m,N}}(n)}{\sqrt{H\log N}}\Bigr)\Longrightarrow\mathcal N_m(0,\Gamma^\ast).
\tag{502.11}
$$

**证明。** 固定矩阶 $r$。因 $H=N^{o(1)}$，最终 $H\le N^{\beta'}$，其中 $\beta'<\min(\beta_r,1/r)$；又 $L/H\to0$、$\kappa_{N,H}\to1$。定理 502.6（取 $k=r$、$w=\mathbf 1_{[1,2]}$）的证明在此尺度下给出全部 $r$ 阶混合矩趋于 $\mathcal N_m(0,\Gamma^\ast)$ 的相应矩；定理 499.1 的证明只用到 $MH\le N$ 与把对数幂吸收进 $N^{\varepsilon}$，不用下界 $H\ge N^\alpha$；定理 502.4 只需 $H\to\infty$。故这里只需该证明中的各误差趋零。对固定 $t\in\mathbb R^m$，$\sum_it_if_{i,N}$ 仍属于固定的有界变差类。Gaussian 矩满足 Carleman 条件，矩方法与 Cramér–Wold 定理给出 (502.11)。证毕。

**范围。** 外部输入为：Montgomery–Soundararajan [Primes in short intervals, Comm. Math. Phys. 252 (2004), 589–617] 定理 1（(15)）与定理 2、(16)；Kuperberg [arXiv:2301.06095] 定理 1.3。Montgomery–Soundararajan 定理 3 与推论 1 在逐位移相关误差假设下给出单一区间的各阶矩与相同共同尺度上的标量 Gaussian 极限；推论 502.7 的标量、单区间情形即该推论，Chan [Int. J. Number Theory 2 (2006)] 的均方弱化见 §499。本节的本仓推导（repo-derived）是：对全部有限阶、区间端点与整个离散有界变差权球一致的奇异级数配对 (502.3)，其中低阶缺陷由定理 500.2 与 §501 的反演一并处理；有界变差权下全部阶数 $\le k$ 的条件 Wick 定理 (502.9)–(502.10)，把定理 498.1 从 $k\le4$、$\beta<1/4$ 推广到一般 $k$、$\beta<1/k$；有界权下的三阶反例 (502.7)；以及有界变差权向量的 Gaussian 极限 (502.11)。$\beta<1/k$ 来自把相关误差对全部位移聚合后与 Gaussian 尺度比较：归一化误差为 $N^{(k\beta-1)/2+\varepsilon}$；奇异级数配对本身没有这一限制。本节不覆盖 $\theta=4/5$，不推出 RH，也不主张文献优先权。

## 追加锚（本行以下为增补区）
