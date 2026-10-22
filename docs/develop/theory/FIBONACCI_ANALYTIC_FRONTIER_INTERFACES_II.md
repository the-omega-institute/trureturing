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
