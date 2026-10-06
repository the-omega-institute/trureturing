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


## 442. 完整素数前缀的五个阻尼区域与宏观肩部函数

**对象与常数。** 沿用 §441 的完整实际素数前缀：\(z\ge2\) 为素数，
\(p\) 为严格大于 \(z\) 的最小素数，两侧统一使用 \(L=\log p\)。仍令

\[
E_z(s)=\prod_{q\le z}(1-q^{-s}),\qquad C_z=E_z(1)^{-1},\qquad
F_z(v)=C_zE_z(1+v/L),
\]

\[
H_z(v)=F_z(v)(1-e^{-v})-v,\qquad
J_z(\sigma)=\int_0^\infty e^{-\sigma v}\frac{H_z(v)}{v^2}\,dv.
\]

乘积包含全部 \(q\le z\) 的素数，\(\sigma>0\) 时积分绝对收敛。
保持 \(C=e^{\gamma_E}>1\)、\(\Phi(v)=\exp(\operatorname{Ein}(v))\)
以及 \(Q(u)=u\zeta(1+u)\)。常数 \(A,Z_0,Z_1,B_*\) 均为（PX.14）
中的原常数，特别地

\[
Z_0=\int_0^1\frac{1/Q(u)-1}{u}\,du,\qquad
Z_1=\int_1^\infty\frac{du}{u^2\zeta(1+u)},\qquad
B_*=A+C(Z_0+Z_1).
\]

以下全部前缀极限均沿实际素数 \(z\to\infty\) 取得。参数
\(\alpha>0\) 固定，\(t\) 位于固定的正紧区间 \([a,b]\subset(0,\infty)\)。
各前缀极限式中的 \(o(1)\) 均在该 \(t\) 区间上一致成立。

**定理 442.1（全部幂次阻尼的常数级展开）。** 定义宏观肩部函数

\[
K(t)=A-(C-1)(\log t+\gamma_E)
 +C\int_0^\infty e^{-tu}\frac{1/Q(u)-1}{u}\,du,
\qquad t>0.
\tag{FD.1}
\]

该积分对每个 \(t>0\) 绝对收敛，\(K\) 在正轴连续。完整首积分满足

\[
J_z(tL^{-\alpha})=
\begin{cases}
(C-1)\alpha\log L+A-(C-1)(\log t+\gamma_E)+o(1),
 &0<\alpha<1,\\[2mm]
(C-1)\log L+K(t)+o(1),&\alpha=1,\\[2mm]
(C-\alpha)\log L+\log t+\gamma_E+B_*+o(1),&\alpha>1.
\end{cases}
\tag{FD.2}
\]

**证明：极限轮廓的完整积分。** 置
\(H_\Phi(v)=\Phi(v)(1-e^{-v})-v\)，并定义固定残差

\[
\mathfrak a(v)=
\begin{cases}
H_\Phi(v)/v^2,&0<v\le1,\\[1mm]
\Phi(v)(1-e^{-v})/v^2-C/v,&v>1.
\end{cases}
\]

\(\Phi(0)=1\)、\(\Phi'(0)=1\) 给
\(H_\Phi(0)=H_\Phi'(0)=0\)，其二阶连续性使第一段在零端有界。
在远端使用 §441 内的经典指数积分恒等式

\[
\Phi(v)=Cv\exp(E_1(v)),\qquad
E_1(v)=\int_v^\infty\frac{e^{-w}}w\,dw\le\frac{e^{-v}}v.
\]

因此 \(v\ge1\) 时
\(\mathfrak a(v)=C[\exp(E_1(v))(1-e^{-v})-1]/v\) 的绝对值
不超过固定常数乘 \(e^{-v}/v\)。这支付两个端点，且
\(\int_0^\infty\mathfrak a(v)\,dv=A\)。几乎处处精确地有

\[
\frac{H_\Phi(v)}{v^2}
=\mathfrak a(v)+(C-1)\frac{\mathbf1_{(1,\infty)}(v)}v.
\]

从而对每个正阻尼

\[
J_\Phi(\sigma):=\int_0^\infty e^{-\sigma v}
 \frac{H_\Phi(v)}{v^2}\,dv
=\int_0^\infty e^{-\sigma v}\mathfrak a(v)\,dv+(C-1)E_1(\sigma).
\tag{FD.3}
\]

这里 \(\int_1^\infty e^{-\sigma v}\,dv/v=E_1(\sigma)\)。经典恒等式
\(E_1(\sigma)=-\log\sigma-\gamma_E+\operatorname{Ein}(\sigma)\)
以及 \(0\le\operatorname{Ein}(\sigma)\le\sigma\)，结合固定可积残差的
支配收敛，给

\[
J_\Phi(\sigma)=A-(C-1)(\log\sigma+\gamma_E)+o(1)
\qquad(\sigma\downarrow0).
\tag{FD.4}
\]

所需的一致性也直接由同一残差支付。对任意固定 \(\alpha>0\)，

\[
\sup_{t\in[a,b]}
\left|\int_0^\infty(e^{-tL^{-\alpha}v}-1)\mathfrak a(v)\,dv\right|
\le\int_0^\infty(1-e^{-bL^{-\alpha}v})|\mathfrak a(v)|\,dv\longrightarrow0.
\]

指数积分的误差一致不超过 \(bL^{-\alpha}\)。因此（FD.4）可在这些
随 \(L\) 收缩的阻尼区间上一致使用，无须给残差积分附加收敛速率。

**证明：\(0<\alpha<1\) 的完整全轴误差。** §441 的原时钟运输给固定
\(B>0\)，使全部 \(v\ge0\) 满足
\(|\log F_z(v)-\log\Phi(v)|\le Bv/L\) 及 \(\Phi(v)\le e(1+v)\)。
由 \(|e^x-1|\le e^{|x|}|x|\)，得到

\[
|F_z(v)-\Phi(v)|\le\Phi(v)e^{Bv/L}\frac{Bv}L.
\]

两个补偿分子具有相同的 \(-v\)，其差恰为
\((F_z-\Phi)(1-e^{-v})\)。当 \(\sigma>B/L\) 时，完整差积分满足

\[
\begin{aligned}
|J_z(\sigma)-J_\Phi(\sigma)|
&\le\frac{eB}L\int_0^\infty e^{-(\sigma-B/L)v}
 \frac{(1+v)(1-e^{-v})}{v}\,dv\\
&\le\frac{2eB}{L(\sigma-B/L)}.
\end{aligned}
\tag{FD.5}
\]

第二步在 \(0<v\le1\) 使用 \(1-e^{-v}\le v\)，在 \(v\ge1\) 使用
\(1-e^{-v}\le1\)，因而全轴上的剩余因子不超过二。正的指数衰减支付
整个无限尾。固定 \(0<\alpha<1\) 后，最终
\(B/L\le aL^{-\alpha}/2\)，所以对所有 \(t\in[a,b]\)，
\(\sigma=tL^{-\alpha}\) 满足 \(\sigma-B/L\ge\sigma/2\)。于是（FD.5）
一致不超过 \((4eB/a)L^{\alpha-1}=o(1)\)。与（FD.4）合并即得
（FD.2）的第一式。

**证明：\(\alpha=1\) 的完整宏观修正。** 精确换元 \(v=Lu\) 给

\[
J_z(t/L)-J_\Phi(t/L)=\int_0^\infty e^{-tu}d_z(u)\,du,
\qquad
d_z(u)=\frac{[F_z(Lu)-\Phi(Lu)](1-e^{-Lu})}{Lu^2}.
\tag{FD.6}
\]

在每个固定 \(u>0\)，§441 中由第三 Mertens 定理所得的
\(C_z/L\to C\)，以及绝对收敛的经典 Euler 乘积，给

\[
\frac{F_z(Lu)}L\longrightarrow\frac{C}{\zeta(1+u)},\qquad
\frac{\Phi(Lu)}L\longrightarrow Cu,\qquad 1-e^{-Lu}\longrightarrow1.
\]

故

\[
d_z(u)\longrightarrow d_\infty(u)
=C\frac{1/Q(u)-1}{u}.
\]

为支付整个零端，在 \(0<u\le1\) 使用全轴对数误差，得到

\[
|d_z(u)|\le eB e^{Bu}\frac{1+Lu}{Lu}(1-e^{-Lu})
\le2eB e^B.
\tag{FD.7}
\]

最后一步正是（FD.5）中对任意正实数成立的因子界，故也覆盖
\(u\ll1/L\)，并不要求 \(Lu\ge1\)。由 §441 的
\(1\le Q(u)\le1+u\)，还有 \(|d_\infty(u)|\le C\)。

在 \(u\ge1\)，取固定 \(C_0\) 使最终 \(C_z/L\le C_0\) 及 \(L\ge1\)。
有限完整乘积的上界 \(F_z\le C_z\) 和 \(\Phi(Lu)\le e(1+Lu)\) 给

\[
|d_z(u)|\le\frac{C_0+e(u+1/L)}{u^2}
\le\frac{C_0+e(u+1)}{u^2},\qquad
|d_\infty(u)|\le\frac Cu.
\]

因此 \(e^{-au}|d_z(u)-d_\infty(u)|\) 在 \((0,1]\) 有固定常数界，
在 \([1,\infty)\) 由固定常数乘
\(e^{-au}(1+u)/u^2\) 控制，两段合为一个固定可积主导函数。普通
支配收敛给

\[
\begin{aligned}
\sup_{t\in[a,b]}\left|\int_0^\infty
 e^{-tu}[d_z(u)-d_\infty(u)]\,du\right|
&\le\int_0^\infty e^{-au}|d_z(u)-d_\infty(u)|\,du\\
&\longrightarrow0.
\end{aligned}
\tag{FD.8}
\]

此处只用了每个固定 \(u>0\) 的 Euler 收敛；零端由（FD.7）直接支付。
与（FD.4）在 \(\sigma=t/L\) 的一致展开合并，得到（FD.1）和
（FD.2）的第二式。

为了同时确认 \(K\) 的定义，令 \(\beta(u)=(1/Q(u)-1)/u\)。上述
\(Q\) 界给

\[
\beta(u)\le0,\qquad |\beta(u)|\le1\quad(u>0),\qquad
|\beta(u)|\le1/u\quad(u>0).
\]

用第一个绝对值界支付 \((0,1]\)，第二个支付指数阻尼下的
\([1,\infty)\)，得到（FD.1）的绝对收敛。在每个正 \(t\) 紧区间上，
同样的 \(e^{-au}\) 主导函数支付连续性。

**证明：\(\alpha>1\) 的完整联合阻尼尾。** 使用 §441 已得的统一局部
预算：最终存在固定 \(K_0\)，使 \(0\le v\le1\) 上
\(|H_z(v)|\le K_0v^2\)。令 \(\mathcal B_z\) 为（PX.15）中的原常数。
扣除它并保留全部负线性尾，精确地有

\[
\begin{aligned}
J_z(\sigma)-\mathcal B_z
={}&\int_0^1(e^{-\sigma v}-1)\frac{H_z(v)}{v^2}\,dv\\
&+\int_1^\infty(e^{-\sigma v}-1)
 \frac{F_z(v)(1-e^{-v})}{v^2}\,dv-E_1(\sigma).
\end{aligned}
\]

第一积分的绝对值不超过 \(K_0\sigma/2\)。对 \(0<\sigma\le1\)，第二
积分的绝对值不超过

\[
C_z\int_1^\infty\frac{\min(\sigma v,1)}{v^2}\,dv
=C_z\sigma[1+\log(1/\sigma)].
\]

这一步包含 \(v\ge1/\sigma\) 的全部尾。结合
\(-E_1(\sigma)=\log\sigma+\gamma_E+O(\sigma)\)，得到固定最终预算
\(K_1\) 下的全轴界

\[
|J_z(\sigma)-\log\sigma-\gamma_E-\mathcal B_z|
\le K_1\sigma+C_z\sigma[1+\log(1/\sigma)].
\tag{FD.9}
\]

当 \(\sigma=tL^{-\alpha}\)、固定 \(\alpha>1\) 时，\(C_z=O(L)\)
使右侧在 \(t\in[a,b]\) 上一致为
\(O_{a,b,\alpha}(L^{-\alpha}+L^{1-\alpha}\log L)=o(1)\)。使用 §441
通过先固定切点比例再令比例趋零而得到的
\(\mathcal B_z=C\log L+B_*+o(1)\)，再代入
\(\log\sigma=\log t-\alpha\log L\)，即得（FD.2）的第三式。
这只消耗原有 \(C_z/L\to C\) 与已匹配常数，不要求加强 Mertens
误差的速率。定理得证。

**定理 442.2（肩部两端的常数连接）。** 同一个完整肩部函数满足

\[
K(t)=A-(C-1)(\log t+\gamma_E)+O(1/t)
\qquad(t\to\infty),
\tag{FD.10}
\]

\[
K(t)=\log t+\gamma_E+B_*+o(1)
\qquad(t\downarrow0).
\tag{FD.11}
\]

**证明。** 因 \(|\beta(u)|\le1\)，有
\(|\int_0^\infty e^{-tu}\beta(u)\,du|\le1/t\)，直接给（FD.10）。
在零端将同一个完整积分精确分为

\[
\int_0^\infty e^{-tu}\beta(u)\,du
=\int_0^1e^{-tu}\beta(u)\,du
 +\int_1^\infty\frac{e^{-tu}}{u^2\zeta(1+u)}\,du-E_1(t).
\]

第一项由 \(|\beta|\le1\) 支配收敛到 \(Z_0\)。第二项由
\(\zeta(1+u)\ge1\) 及可积的 \(u^{-2}\) 支配收敛到 \(Z_1\)。最后
一项保持为完整的负指数积分。因此

\[
\int_0^\infty e^{-tu}\beta(u)\,du
=Z_0+Z_1+\log t+\gamma_E+o(1).
\]

代入（FD.1），\(\log t+\gamma_E\) 的系数为
\(-(C-1)+C=1\)，其余常数为 \(A+C(Z_0+Z_1)=B_*\)，即得
（FD.11）。证毕。

这两式描述先取宏观极限后，固定函数 \(K\) 的两个端点；它们本身
不提供 \(t=t_z\to0\) 或 \(t_z\to\infty\) 时的联合前缀极限。
（FD.2）中相应的幂次参数通道已分别由全轴误差（FD.5）和完整联合
尾界（FD.9）直接支付。

**推论 442.3（五个阻尼区域与精确符号边界）。** 对每个固定
\(\alpha>0\)，在每个固定正 \(t\) 紧区间上一致有

\[
\frac{J_z(tL^{-\alpha})}{\log L}\longrightarrow f(\alpha),\qquad
f(\alpha)=
\begin{cases}
(C-1)\alpha,&0<\alpha\le1,\\
C-\alpha,&\alpha\ge1.
\end{cases}
\tag{FD.12}
\]

令 \(t_*=e^{-\gamma_E-B_*}\)。完整 \(J_z\) 的五个区域为

| 固定阻尼指数 | \(J_z(tL^{-\alpha})\) 的行为 |
|---|---|
| \(0<\alpha<1\) | 以系数 \((C-1)\alpha\) 正向发散，常数项为 \(A-(C-1)(\log t+\gamma_E)\)。 |
| \(\alpha=1\) | 以系数 \(C-1\) 正向发散，有限修正为完整肩部 \(K(t)\)。 |
| \(1<\alpha<C\) | 以系数 \(C-\alpha\) 正向发散，常数项为 \(\log t+\gamma_E+B_*\)。 |
| \(\alpha=C\) | 趋于 \(\log(t/t_*)\)；\(t<t_*\) 时最终为负，\(t>t_*\) 时最终为正。 |
| \(\alpha>C\) | 以系数 \(C-\alpha\) 负向发散，常数项为 \(\log t+\gamma_E+B_*\)。 |

在 \(\alpha=C\)、\(t=t_*\) 时，只得到
\(J_z(t_*L^{-C})\to0\)；该零极限没有给出有限前缀的最终符号，
也没有断言 \(t_*L^{-C}\) 恰为每个前缀的阻尼零点。临界区域的非零
符号在与 \(t_*\) 分离的固定正 \(t\) 紧集上一致成立。

**证明。** 将（FD.2）除以 \(\log L\to\infty\)。连续的 \(K\) 在
\([a,b]\) 上有界，\(\log t\) 也一致有界，故（FD.12）及其一致性
成立。在 \(\alpha=1\)，两段系数同为 \(C-1>0\)，斜率由
\(C-1\) 变为 \(-1\)。唯一的零系数位于 \(\alpha=C\)。
（FD.2）的临界常数为 \(\log(t/t_*)\)，从而给上述非零符号；
当此常数为零时，余下 \(o(1)\) 的符号没有被这些估计确定。

若同时使用定理 441.1 已建立的实际唯一阻尼零点及其两侧严格符号，
则在任意固定 \(0<t_-<t_*<t_+\) 上，临界极限给
\(J_z(t_-L^{-C})<0<J_z(t_+L^{-C})\) 最终成立。因此
\(t_-<\sigma_zL^C<t_+\)，两侧固定括号趋于 \(t_*\) 后仍得
\(\sigma_zL^C\to t_*\)。此根结论消耗实际唯一交点，五区展开本身
并不替代该交点证明。证毕。

宏观折点 \(\alpha=1\) 对应完整积分开始感受到 \(v\) 与 \(L\)
同阶的实际前缀轮廓；符号阈值 \(\alpha=C\) 则由正的有限前缀
储备 \(C\log L\) 与精确负线性尾 \(\log\sigma\) 匹配而来。
\(K(t)\) 通过一个支付两端的完整实际到极限轮廓差积分，将
常数 \(A\) 与 \(B_*\) 连接。这五区只使用固定 \(\alpha\) 与固定
正 \(t\) 紧区间的均匀性，未给出同时移动 \(\alpha_z\) 的断点
邻域展开。

由（PX.2），\(I_p(\sigma)-I_z(\sigma)=J_z(\sigma)/(p-1)\)，故上述
\(J_z\) 符号也是完整首项插入差的符号。完整 Robin 配对还包含原
第一块、全部阶乘密度项、实际 Möbius 与粗糙前缀权重及全部互补整数
纤维；其临界符号仍需要这些项共同的有符号估计。本节结论的对象
始终是同一时钟下的完整首补偿积分。

**来源。** 完整实际前缀的五区展开及肩部常数连接为本仓推导
（`repo-derived`）。本节消耗 §441 的真实前缀误差、经典 Mertens
与 Euler 乘积供应及已匹配常数；指数积分恒等式、支配收敛与
Laplace 换元均为经典分析工具。


## 443. 宏观阻尼响应的指数平均与对数严格凹性

**对象。** 沿用 §441–§442 的完整前缀、统一时钟、比率与肩部函数
\(L=\log p\)、\(R_z(v)=F_z(v)(1-e^{-v})/v\)、\(C=e^{\gamma_E}>1\)、
\(Q(u)=u\zeta(1+u)\) 及 \(K(t)\)。以下所有积分均在整个正轴上取得。
§441 已给出 \(Q\) 在正轴连续、严格增加，且
\(1\le Q(u)\le1+u\)、\(Q(u)\ge u\)。这些界还给
\(Q(0+)=1\) 和 \(Q(+\infty)=+\infty\)。

**定理 443.1（完整肩部响应与严格凹性）。** 定义

\[
h(t)=\int_0^\infty\frac{e^{-x}}{Q(x/t)}\,dx\qquad(t>0).
\tag{MR.1}
\]

则 \(K\) 在正轴连续可微，而且

\[
K'(t)=\frac1t-C\int_0^\infty\frac{e^{-tu}}{Q(u)}\,du,
\qquad tK'(t)=1-Ch(t).
\tag{MR.2}
\]

函数 \(h\) 连续、严格增加，取值在 \((0,1)\)，并满足

\[
h(0+)=0,\qquad h(+\infty)=1.
\tag{MR.3}
\]

因此 \(G(y)=K(e^y)\) 在整个实轴严格凹。存在唯一 \(t_0>0\) 满足
\(Ch(t_0)=1\)，且

\[
K'(t)>0\quad(0<t<t_0),\qquad
K'(t_0)=0,\qquad K'(t)<0\quad(t>t_0).
\tag{MR.4}
\]

该 \(t_0\) 是 \(K\) 的唯一全局最大点。

**证明。** 写 \(\beta(u)=(1/Q(u)-1)/u\)。在任意固定正紧区间
\([a,b]\)，§442 给出了 \(e^{-tu}\beta(u)\) 的完整可积主导函数。
其关于 \(t\) 的导函数为
\(-e^{-tu}(1/Q(u)-1)\)，绝对值不超过 \(e^{-au}\)。这同时支付零端
和整个无限尾，故经典积分下求导和支配收敛给

\[
K'(t)=-\frac{C-1}t-C\int_0^\infty e^{-tu}(1/Q(u)-1)\,du.
\]

使用 \(\int_0^\infty e^{-tu}\,du=1/t\) 即得（MR.2）的第一式；
精确换元 \(x=tu\) 给第二式。导函数的连续性由同一指数主导支付。

对每个 \(x>0\)，\(e^{-x}/Q(x/t)\) 随 \(t\) 严格增加，且被
\(e^{-x}\) 主导。因 \(Q\) 连续，完整支配收敛给 \(h\) 连续。
任意 \(0<t_1<t_2\) 的两个被积函数之差在整个正轴严格为正，
所以其积分差严格为正。严格增加的 \(Q\) 及 \(Q(u/2)\ge1\) 还给
\(Q(u)>1\)，因而 \(0<h(t)<\int_0^\infty e^{-x}\,dx=1\)。
当 \(t\downarrow0\)，对每个 \(x>0\) 有 \(Q(x/t)\to\infty\)；
当 \(t\to\infty\)，有 \(Q(x/t)\to1\)。两个极限均以
\(e^{-x}\) 为共同主导，故得到（MR.3）。

链式法则给 \(G'(y)=1-Ch(e^y)\)，它连续、严格减少，从
\(1\) 趋于 \(1-C<0\)。连续严格减少的导函数给整个实轴上的严格
凹性。介值定理和严格单调性给唯一 \(h(t_0)=1/C\)；（MR.2）给
（MR.4）。因此 \(K\) 在 \((0,t_0)\) 严格增加、在 \((t_0,\infty)\)
严格减少。证毕。

**推论 443.2（肩部零点的完整条件分类）。** \(K\) 两端均趋于
\(-\infty\)，且最多有两个正零点。若 \(K(t_0)>0\)，恰有两个正
零点；若 \(K(t_0)=0\)，仅有 \(t_0\) 一个零点；若 \(K(t_0)<0\)，
没有正零点。

**证明。** §442 的两端展开给

\[
K(t)=\log t+\gamma_E+B_*+o(1)\quad(t\downarrow0),
\]

\[
K(t)=A-(C-1)(\log t+\gamma_E)+O(1/t)\quad(t\to\infty).
\]

因为 \(C>1\)，两端均趋于 \(-\infty\)。在最大点两侧使用连续性、
严格单调性和介值定理，即得三种情况。本推论没有预设 \(K(t_0)\)
的符号。证毕。

**定理 443.3（实际前缀的完整宏观导数极限）。** 对每个固定完整
前缀，\(t\mapsto J_z(t/L)\) 在正轴连续可微，且精确地有

\[
\frac{d}{dt}J_z(t/L)=\frac1t-
 \int_0^\infty e^{-tu}R_z(Lu)\,du.
\tag{MR.5}
\]

沿实际素数 \(z\to\infty\)，对任意固定
\(0<a\le t\le b<\infty\)，

\[
\sup_{t\in[a,b]}
\left|\frac{d}{dt}J_z(t/L)-K'(t)\right|\longrightarrow0.
\tag{MR.6}
\]

结合 §442，这给 \(J_z(t/L)-(C-1)\log L\) 在每个正紧区间上
向 \(K(t)\) 的函数和一阶导数一致收敛。

**证明：固定前缀下的全轴求导。** 先在原补偿积分内作精确换元，
得到

\[
J_z(t/L)=\int_0^\infty e^{-tu}\frac{R_z(Lu)-1}{u}\,du.
\]

这是已支付零端与无限尾的完整积分，不分别积分零端发散的两个项。
对固定前缀，\(0<R_z(v)\le C_z\)，因为 \(F_z(v)\le C_z\) 且
\((1-e^{-v})/v\le1\)。在任意 \(t\) 的正紧邻域上，关于 \(t\)
的导函数绝对值不超过 \((C_z+1)e^{-au}\)，它在整个正轴可积。
完整积分下求导给
\(-\int_0^\infty e^{-tu}(R_z(Lu)-1)\,du\)。这时两项各自均可积，
才将它们分开，并使用指数积分 \(1/t\)，得到（MR.5）。同一主导
支付导函数连续性。

**证明：联合增长的完整主导。** 对每个固定 \(u>0\)，§441 的
真实宏观极限给
\(R_z(Lu)\to C/Q(u)\)。令 \(B\) 为（PX.6）中的固定预算。
对全部 \(0<u\le1\)，全轴对数误差和 \(\Phi(v)\le e(1+v)\) 给

\[
R_z(Lu)\le e^{Bu}\Phi(Lu)\frac{1-e^{-Lu}}{Lu}
\le2e e^B.
\tag{MR.7}
\]

最后一步同时覆盖任意小的 \(Lu\)。对 \(u\ge1\)，由
\(C_z/L\to C\) 取固定最终预算 \(C_0\)，则

\[
R_z(Lu)\le\frac{C_z/L}{u}\le\frac{C_0}{u}.
\tag{MR.8}
\]

又 \(C/Q(u)\le C\)，所以
\(e^{-au}|R_z(Lu)-C/Q(u)|\) 在 \((0,1]\) 有固定常数主导，
在 \([1,\infty)\) 有 \(e^{-au}(C_0/u+C)\) 主导。两段合成一个
固定的完整可积主导函数，支配收敛给

\[
\begin{aligned}
\sup_{t\in[a,b]}
\left|\int_0^\infty e^{-tu}[R_z(Lu)-C/Q(u)]\,du\right|
&\le\int_0^\infty e^{-au}|R_z(Lu)-C/Q(u)|\,du\\
&\longrightarrow0.
\end{aligned}
\]

将（MR.2）与（MR.5）比较，即得（MR.6）。证毕。

**范围与来源。** 本节的实际前缀宏观导数极限是本仓从 §441–§442
原对象推出的结论（`repo-derived`）；肩部形状是经典 Laplace 单调
机制在同一 \(K\) 上的应用。具体地，若 \(\mathcal L\) 表示正轴
Laplace 变换，则 \(h(t)=\mathcal L(1/Q)(t)/\mathcal L1(t)\)。
这一比率的单调性对应 Yang–Tian 的 Laplace 比率单调规则：
《Monotonicity rules for the ratio of two Laplace transforms with applications》，
J. Math. Anal. Appl. 470(2) (2019), 821–845，
[DOI: 10.1016/j.jmaa.2018.10.034](https://doi.org/10.1016/j.jmaa.2018.10.034)。
本节用（MR.1）的严格逐点比较直接支付严格性；Laplace 参数求导的
经典公式参见 [NIST DLMF 1.14.23](https://dlmf.nist.gov/1.14.E23)。
支配收敛、导函数判凹性和介值定理均为经典分析供应。
这里的最大点是首积分在宏观阻尼尺度上的有限修正最大点。
实际阻尼零点仍位于 §441 的 \(L^{-C}\) 尺度；本节没有将其移到
\(L^{-1}\) 尺度，也没有断言有限前缀导数在全轴上的唯一零点。
完整 Robin 配对中其余有符号项的联合临界估计仍待证明。
