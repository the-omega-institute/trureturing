# Fibonacci 原子关系生成：Robin 素数前缀续卷

**符号与引用。** 本卷延续 [原卷](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的章节编号。
本卷所引 §428、§433、§438、§439 与 §440 均指原卷对应条目；
本卷 §441 定义完整素数前缀、统一插入时钟与补偿积分。

## 441. 完整素数前缀的三尺度唯一交点与阻尼常数匹配

**定义与范围。** 本节回到完整的实际素数前缀。令 \(z\ge2\) 为素数，
\(p\) 为严格大于 \(z\) 的最小素数，统一使用插入时钟 \(L=\log p\)。定义

\[
E_z(s)=\prod_{q\le z}(1-q^{-s}),\qquad
C_z=E_z(1)^{-1},\qquad
F_z(v)=C_zE_z(1+v/L),
\]

\[
s_z=\frac1L\sum_{q\le z}\frac{\log q}{q-1},\qquad
H_z(v)=F_z(v)(1-e^{-v})-v,
\]

\[
R_z(v)=F_z(v)\frac{1-e^{-v}}v\quad(v>0),\qquad
J_z(\sigma)=\int_0^\infty e^{-\sigma v}\frac{H_z(v)}{v^2}\,dv
\quad(\sigma>0).
\tag{PX.1}
\]

所有素数乘积与和均包含 \(q\le z\) 的全部素数。与 §440 的单素数基底
不同，此处 \(z\) 之后恰好只插入 \(p\)。若

\[
I_z(\sigma)=\int_0^\infty e^{-\sigma v}
 \frac{F_z(v)-1-s_zv}{v^2}\,dv,
\]

插入后的 \(I_p\) 也使用同一个 \(L\)，则逐点精确补偿给

\[
F_p(v)=F_z(v)\frac{p-e^{-v}}{p-1},\qquad
s_p=s_z+\frac1{p-1},\qquad
I_p(\sigma)-I_z(\sigma)=\frac{J_z(\sigma)}{p-1}.
\tag{PX.2}
\]

本节只研究这一完整首积分及其零点，不将它等同于 §433 的全部阶乘密度
或 §428 的完整 Robin 配对。记 Euler 常数为 \(\gamma_E\)，并令

\[
C=e^{\gamma_E}>1,\qquad
\Phi(v)=\exp(\operatorname{Ein}(v)),\qquad
\operatorname{Ein}(v)=\int_0^v\frac{1-e^{-t}}t\,dt.
\tag{PX.3}
\]

**定理 441.1（真实前缀的最终唯一交点）。** 存在 \(z_0\)，使每个素数
\(z\ge z_0\) 的 \(H_z\) 恰有一个正零点 \(r_z\)，且

\[
H_z(v)>0\quad(0<v<r_z),\qquad
H_z(v)<0\quad(v>r_z).
\tag{PX.4}
\]

相应的 \(J_z\) 恰有一个正零点 \(\sigma_z\)，并且

\[
J_z(\sigma)<0\quad(0<\sigma<\sigma_z),\qquad
J_z(\sigma)>0\quad(\sigma>\sigma_z).
\tag{PX.5}
\]

若 \(u_*\) 是方程 \(u\zeta(1+u)=C\) 的唯一正解，则
\(r_z/L\to u_*\)。这里所有极限均沿实际素数 \(z\to\infty\) 取得。

**证明：时钟运输与整个近区。** 置 \(\theta=\log z/L\)。Bertrand 定理给
\(p\le2z\)，所以 \(\theta\to1\) 且
\(0\le1-\theta\le\log2/L\)。令
\(r(v)=(1-e^{-v})/v\)，连续补成 \(r(0)=1\)。对 \(v>0\)，

\[
0\le r(v)-\theta r(\theta v)
=\frac{e^{-\theta v}-e^{-v}}v\le1-\theta.
\]

将（SC.4）的原时钟斜率乘 \(\theta\)，再积分，得到某个固定 \(B>0\)
对全部 \(v\ge0\) 满足

\[
\left|\frac{F_z'(v)}{F_z(v)}-r(v)\right|\le\frac BL,
\qquad
|\log F_z(v)-\log\Phi(v)|\le\frac{Bv}L,
\qquad \Phi(v)\le e(1+v).
\tag{PX.6}
\]

可以取 \(B=D+\log2\)，其中 \(D\) 为（SC.3）的固定预算。特别地
\(s_z\to1\)。定义 \(g(v)=\log(\Phi(v)r(v))\)，并补成 \(g(0)=0\)。
由原始轮廓微分恒等式，

\[
(\Phi r)'=\Phi(r^2-j),\qquad
r(v)^2-j(v)=\frac{e^{-v}(v-1+e^{-v})}{v^2}>0.
\]

零端展开给 \(g'(0+)=1/2\)，故 \(g\) 在正轴严格增加，且对任意固定
\(V>0\)，连续补成后的 \(g(v)/v\) 在 \([0,V]\) 有严格正的最小值
\(m\)。取 \(\varepsilon>0\) 使 \(B\varepsilon<g(V)\)。当
\(L>B/m\) 且 \(\varepsilon L\ge V\) 时，（PX.6）给

\[
\log R_z(v)\ge g(v)-Bv/L>0\qquad(0<v\le\varepsilon L).
\tag{PX.7}
\]

其中 \(0<v\le V\) 用 \(g(v)\ge mv\)，\(V\le v\le\varepsilon L\)
用 \(g(v)\ge g(V)\)。这支付了整个随 \(L\) 扩张的近区，包括任意小的
正 \(v\)，并非只支付固定 \(v\) 的点态极限。

**证明：宏观比率的严格斜率。** 对 \(u>0\)，置 \(Q(u)=u\zeta(1+u)\)。
先在本证明内部使用经典 Gamma 与 zeta 积分表示

\[
Q(u)=\int_0^\infty\psi(t)\rho_u(t)\,dt,
\qquad
\psi(t)=\frac{t}{1-e^{-t}},\qquad
\rho_u(t)=\frac{t^{u-1}e^{-t}}{\Gamma(u)}.
\tag{PX.8}
\]

\(\rho_u\) 的总质量为一，一阶矩为 \(u\)。由指数函数的基本不等式，
\(1\le\psi(t)\le1+t\) 且 \(\psi(t)\ge t\)，故

\[
1\le Q(u)\le1+u,\qquad Q(u)\ge u.
\tag{PX.9}
\]

更强的斜率支付可只用一个积分。令 \(\chi(t)=\psi(t)-t/2\)。对 \(t>0\)，

\[
\chi'(t)=\frac{e^{-t}(\sinh t-t)}{(1-e^{-t})^2}>0.
\]

若 \(0<a<b\)，密度比
\(\rho_b(t)/\rho_a(t)=[\Gamma(a)/\Gamma(b)]t^{b-a}\) 严格增加，从零
趋于无穷，故恰在一个 \(t_0>0\) 等于一。总质量相同允许扣去常数
\(\chi(t_0)\)，得到

\[
\begin{aligned}
Q(b)-Q(a)-\frac{b-a}{2}
&=\int_0^\infty[\chi(t)-\chi(t_0)]
 [\rho_b(t)-\rho_a(t)]\,dt>0.
\end{aligned}
\tag{PX.10}
\]

积分绝对收敛，因为 \(0\le\chi(t)\le1+t/2\)，而两个密度的质量与
一阶矩均有限。被积函数对 \(t\ne t_0\) 严格为正；取一个避开
\(t_0\) 的正长度紧区间即可支付严格正性。由 \(\zeta\) 在实轴
\(s>1\) 的经典可微性，（PX.10）给 \(Q'(u)\ge1/2\)。这里没有从严格
割线不等式直接推出严格导数不等式。结合（PX.9），\(Q\) 连续严格增加，
零端极限为一，远端趋于无穷，故 \(u_*\) 存在且唯一。

准确的宏观对象是

\[
\mathcal R_z(u):=R_z(Lu)
=\frac{C_z}L\,\frac{E_z(1+u)(1-p^{-u})}{u}.
\tag{PX.11}
\]

经典第三 Mertens 定理与 \(\theta\to1\) 给 \(C_z/L\to C\)。在每个
固定 \([\varepsilon,M]\subset(0,\infty)\)，Euler 乘积及其一阶导数
一致趋于 \(1/\zeta(1+u)\) 及相应导数：对数导数的素数尾由收敛级数
\(\sum_{n\ge2}\log n/n^{1+\varepsilon}\) 控制，未求导的尾同样绝对收敛。
另外 \(p^{-u}\to0\) 一致成立，且
\(|(p^{-u})'|\le Lp^{-\varepsilon}\to0\)。因此

\[
\mathcal R_z\longrightarrow \mathcal R:=C/Q
\quad\text{在每个固定 }[\varepsilon,M]\text{ 上一致连同一阶导数收敛}.
\]

由（PX.9）–（PX.10），在整段区间上都有统一严格界

\[
\mathcal R'(u)=-\frac{CQ'(u)}{Q(u)^2}
\le-\frac{C}{2(1+M)^2}<0.
\tag{PX.12}
\]

因此充分大 \(z\) 的 \(\mathcal R_z\) 在整段 \([\varepsilon,M]\)
严格递减，不必再将宏观区间切为根邻域与其余符号区。

**证明：完整远尾与分子唯一性。** 对 \(v\ge0\)，有限 Euler 乘积给
\(1\le F_z(v)\le C_z\)。选固定 \(M>C\)，并增大 \(z_0\) 使
\(C_z/L<M\)，则

\[
R_z(v)<C_z/v<1\qquad(v\ge ML).
\tag{PX.13}
\]

在边界第二个不等式仍严格成立。缩小上述 \(\varepsilon\) 使
\(\varepsilon<u_*\)，增大 \(M\) 使 \(M>u_*\)。由（PX.7）、
（PX.12）和（PX.13），\(R_z\) 从近区的严格大于一，经过整段宏观
严格递减，进入整个远尾的严格小于一。连续性给唯一交点。因
\(H_z(v)=v(R_z(v)-1)\)，得到（PX.4）。宏观一致收敛及
\(\mathcal R(u_*)=1\) 的严格交点还给 \(r_z/L\to u_*\)。

**证明：完整积分的唯一阻尼。** 每个固定前缀有
\(H_z(0)=H_z'(0)=0\)、\(H_z''(0)=2s_z-1\)；局部二阶界支付零端，
有限乘积上界与正阻尼支付整个远尾，故 \(J_z(\sigma)\) 绝对收敛并在
\(\sigma>0\) 连续。更具体地，有限支持给全部 \(v\ge0\) 上
\(0\le k_z(v):=F_z'(v)/F_z(v)\le s_z\)、
\(0\le T_z(v):=-k_z'(v)\le2s_z\)，因此
\(|H_z''(v)|\le C_z(s_z^2+4s_z+1)\)。两次积分给一个固定前缀的
全轴二阶预算。它同样支付（PX.2）两侧的字面补偿积分。替换
\(t=\sigma v\) 并用该二阶全轴界作主导函数给
\(\sigma J_z(\sigma)\to s_z-1/2>0\) 当 \(\sigma\to\infty\)。另一方面，
将 \(-v\) 的尾保留为 \(-\int_1^\infty e^{-\sigma v}\,dv/v\)，其余两项
在 \(\sigma\downarrow0\) 有有限极限，所以 \(J_z(\sigma)\to-\infty\)。
最后对 \(\sigma_2>\sigma_1>0\)，全部积分均已支付且

\[
J_z(\sigma_2)-e^{-(\sigma_2-\sigma_1)r_z}J_z(\sigma_1)
=\int_0^\infty e^{-\sigma_1v}
 [e^{-(\sigma_2-\sigma_1)v}-e^{-(\sigma_2-\sigma_1)r_z}]
 \frac{H_z(v)}{v^2}\,dv>0.
\]

两侧区间的括号与 \(H_z\) 同号，正长度区间支付严格性。于是
\(e^{\sigma r_z}J_z(\sigma)\) 严格递增；与两端符号及连续性合并，得到
（PX.5）。证毕。

**定理 441.2（两尺度常数与实际阻尼匹配）。** 定义

\[
A=\int_0^1\frac{\Phi(v)(1-e^{-v})-v}{v^2}\,dv
 +\int_1^\infty\left[\frac{\Phi(v)(1-e^{-v})}{v^2}-\frac Cv\right]dv,
\]

\[
Z_0=\int_0^1\frac{1/Q(u)-1}{u}\,du,
\qquad Z_1=\int_1^\infty\frac{du}{u^2\zeta(1+u)},
\qquad B_*=A+C(Z_0+Z_1).
\tag{PX.14}
\]

这些积分均绝对收敛。对真实前缀令

\[
\mathcal B_z=\int_0^1\frac{H_z(v)}{v^2}\,dv
 +\int_1^\infty\frac{F_z(v)(1-e^{-v})}{v^2}\,dv.
\]

则

\[
\mathcal B_z=C\log L+B_*+o(1),\qquad
J_z(tL^{-C})\longrightarrow\log t+\gamma_E+B_*.
\tag{PX.15}
\]

第二个极限在每个固定 \(0<a\le t\le b<\infty\) 上一致成立。因此
定理 441.1 中的实际唯一阻尼满足

\[
\sigma_zL^C\longrightarrow e^{-\gamma_E-B_*}.
\tag{PX.16}
\]

**证明：两个端点的付款。** 零端补偿支付 \(A\) 的第一积分。经典恒等式
\(\operatorname{Ein}(v)=\log v+\gamma_E+E_1(v)\)，其中
\(E_1(v)=\int_v^\infty e^{-t}\,dt/t\le e^{-v}/v\)，给
\(\Phi(v)=Cv\exp(E_1(v))\)，故 \(A\) 的远尾指数可积。
由（PX.9），\(|(1/Q(u)-1)/u|\le1\)，而 \(Z_1\) 的被积函数不超过
\(u^{-2}\)，故其两个端点均已支付。每个固定 \(z\) 的
\(\mathcal B_z\) 由零端二阶界及有限乘积上界绝对收敛。

**证明：先固定切点比例，再消去比例。** 固定 \(0<\varepsilon<1\)，
先令 \(z\to\infty\)，使 \(\varepsilon L\ge1\)。将
\(\mathcal B_z\) 在 \(v=\varepsilon L\) 分为近部与完整宏观尾。
由（PX.6），在 \(0<v\le\varepsilon L\) 有

\[
|F_z(v)-\Phi(v)|\le\Phi(v)e^{B\varepsilon}Bv/L.
\]

在 \((0,1]\) 中额外因子 \(1-e^{-v}\le v\) 支付零端，近部差为
\(O(1/L)\)。在 \([1,\varepsilon L]\) 使用 \(\Phi(v)\le e(1+v)\)，
可取与 \(z,\varepsilon\) 无关的固定 \(K\)，使总近部差不超过

\[
K/L+Ke^{B\varepsilon}
 \left[\varepsilon+\frac{\log(\varepsilon L)}L\right].
\tag{PX.17}
\]

\(A\) 的定义及其尾收敛给对应的 \(\Phi\) 近部等于
\(A+C\log(\varepsilon L)+o_z(1)\)。整个宏观尾的精确换元是

\[
\int_{\varepsilon L}^\infty\frac{F_z(v)(1-e^{-v})}{v^2}\,dv
=\frac{C_z}L\int_\varepsilon^\infty
 \frac{E_z(1+u)(1-p^{-u})}{u^2}\,du
\longrightarrow C\int_\varepsilon^\infty\frac{du}{u^2\zeta(1+u)}.
\tag{PX.18}
\]

对这个固定 \(\varepsilon\)，\(C_z/L\) 最终有界且
\(0\le E_z(1+u)(1-p^{-u})\le1\)，故共同主导函数为常数乘
\(u^{-2}\)，支付整个尾。又精确地有

\[
\log\varepsilon+\int_\varepsilon^\infty\frac{du}{u^2\zeta(1+u)}
=Z_0+Z_1-\int_0^\varepsilon\frac{1/Q(u)-1}{u}\,du.
\]

结合（PX.17）–（PX.18）及末积分的绝对值不超过 \(\varepsilon\)，得

\[
\limsup_{z\to\infty}|\mathcal B_z-C\log L-B_*|
\le K\varepsilon e^{B\varepsilon}+C\varepsilon.
\]

最后才令 \(\varepsilon\downarrow0\)，即得（PX.15）的第一式。
整个推导只用 \(C_z/L\to C\)，没有使用更强的
\((C_z/L-C)\log L\to0\) 或随 \(z\) 移动的切点比例。

**证明：联合阻尼的完整尾。** （PX.6）给最终有界的 \(s_z\)；
（SC.5）的有限支持曲率证明在新时钟下同样适用，因为
\(0<\log q/L<1\)。由 \(F_z'=F_zk_z\)、
\(F_z''=F_z(k_z^2-T_z)\)、\(0\le k_z\le s_z\) 及
\(0\le T_z\le2s_z\)，存在与 \(z\) 无关的 \(K_0\)，使最终所有
\(0\le v\le1\) 满足 \(|H_z(v)|\le K_0v^2\)。故此区间的阻尼差
不超过常数乘 \(\sigma\)。正尾在 \(0<\sigma\le1\) 满足

\[
\begin{aligned}
0&\le\int_1^\infty(1-e^{-\sigma v})
 \frac{F_z(v)(1-e^{-v})}{v^2}\,dv\\
&\le C_z\int_1^\infty\frac{\min(\sigma v,1)}{v^2}\,dv
=C_z\sigma[1+\log(1/\sigma)].
\end{aligned}
\tag{PX.19}
\]

负线性尾保持为 \(-E_1(\sigma)=\log\sigma+\gamma_E+O(\sigma)\)。于是

\[
|J_z(\sigma)-\log\sigma-\gamma_E-\mathcal B_z|
\le K_1\sigma+C_z\sigma[1+\log(1/\sigma)]
\tag{PX.20}
\]

有固定最终预算 \(K_1\)。取 \(\sigma=tL^{-C}\)，在每个正 \(t\) 紧区间
上误差一致为 \(O(L^{-C}+L^{1-C}\log L)=o(1)\)，因为 \(C_z=O(L)\)
且 \(C>1\)。与常数匹配合并得（PX.15）的第二式。最后在
\(t_*=e^{-\gamma_E-B_*}\) 两侧任取正的固定 \(t_-<t_*<t_+\)，一致极限
给相反符号；由实际阻尼唯一性，
\(t_-<\sigma_zL^C<t_+\) 最终成立。令两侧趋于 \(t_*\)，即得（PX.16）。
证毕。

**推论 441.3（两种递归尺度的联系与边界）。** 对充分大的完整实际前缀，
分子交点发生在 \(v\sim u_*\log p\)，而首积分的阻尼交点发生在
\(\sigma\sim e^{-\gamma_E-B_*}(\log p)^{-e^{\gamma_E}}\)。两种尺度由同一
Euler 幅度常数 \(e^{\gamma_E}\) 联系，但不互为简单倒数。

**证明。** 直接由定理 441.1 与（PX.16）。分子在宏观尺度由
\(C/Q(u)\) 的交点控制；积分还累计近区的对数储备
\(C\log L\)，与准确负线性尾 \(\log\sigma\) 匹配后产生幂次 \(C\)。
两项付款来自同一 \(F_z\)，不能把一个固定前缀的零阻尼极限直接代入
同时增长的前缀。该联系只描述（PX.2）的完整首项；完整同筛 Robin 配对
在更新粗糙前缀和所有整数纤维后仍是同一个 \(I_\psi\)，其临界符号仍需
共同的有符号估计。上述结果未决定 RH 或 5040 之后的 Robin 不等式。证毕。

**来源。** 完整前缀的三尺度交点与常数匹配为本仓推导（`repo-derived`）。
Bertrand、第一与第三 Mertens、绝对收敛 Euler 乘积为经典供应；本节使用
§438 的全轴原始轮廓误差和曲率界。Gamma 质量及一阶矩、密度比单交点
比较为标准积分与随机序方法，（PX.8）的经典积分表示参见
[NIST DLMF 25.5.1](https://dlmf.nist.gov/25.5.E1)，Gamma 积分参见
[NIST DLMF 5.9.1](https://dlmf.nist.gov/5.9.E1)。这些经典步骤只在新的
前缀交点证明内部承担供应，不作为单独的新定理。
