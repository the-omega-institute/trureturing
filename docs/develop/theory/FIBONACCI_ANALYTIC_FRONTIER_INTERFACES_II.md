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
