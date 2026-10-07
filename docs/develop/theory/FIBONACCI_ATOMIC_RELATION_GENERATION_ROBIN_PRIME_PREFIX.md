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

## 444. 原始轮廓的曲率与完整肩部的严格负储备

**对象。** 保持 §441–§443 的原常数与原完整积分。仍令
\(C=e^{\gamma_E}\)、\(\Phi(v)=\exp(\operatorname{Ein}(v))\)、
\(Q(u)=u\zeta(1+u)\)，并使用（PX.14）中的原常数 \(A\)。肩部为

\[
K(t)=A-(C-1)(\log t+\gamma_E)
 +C\int_0^\infty e^{-tu}\frac{1/Q(u)-1}{u}\,du,
\qquad t>0.
\]

实际前缀仍包含全部 \(q\le z\) 的素数；\(p\) 是严格大于素数
\(z\) 的最小素数，\(L=\log p\)，\(J_z\) 是 §441 中同一时钟下的
完整首补偿积分。以下新增符号

\[
\delta=\frac{2\log2-1}{6}
\]

是一个固定正数。

**定理 444.1（全轴曲率与原轮廓常数）。** \(\Phi\) 在零点光滑延拓，
满足

\[
\Phi'(0)=1,\qquad \Phi''(0)=1/2,
\qquad 0<\Phi''(v)<1/2\quad(v>0).
\tag{NS.1}
\]

其二阶导数在整个正轴严格递减，且原常数满足

\[
A<1/2.
\tag{NS.2}
\]

**证明：零端与曲率代数。** 令 \(r(v)=(1-e^{-v})/v\)，在零点补成
\(r(0)=1\)。有限区间上的经典表示

\[
r(v)=\int_0^1e^{-sv}\,ds
\]

给同一函数的光滑延拓，且 \(r'(0)=-1/2\)。因
\(\Phi'=\Phi r\) 及 \(\Phi(0)=1\)，得到（NS.1）的两项零端值。
对 \(v>0\)，准确地有

\[
\Phi''(v)=\Phi(v)e^{-v}\frac{v-1+e^{-v}}{v^2}.
\tag{NS.3}
\]

\(v-1+e^{-v}\) 从零开始，其导数 \(1-e^{-v}\) 在正轴严格为正，
故（NS.3）严格为正。对其正值取对数并求导，得到

\[
\begin{aligned}
(\log\Phi'')'(v)
&=\frac{1-e^{-v}}v-1
 +\frac{1-e^{-v}}{v-1+e^{-v}}-\frac2v\\
&=\frac{D(v)}{v(v-1+e^{-v})},\\
D(v)&=1+v-v^2-3ve^{-v}-e^{-2v}.
\end{aligned}
\tag{NS.4}
\]

置 \(T(v)=-e^{2v}D(v)=(v^2-v-1)e^{2v}+3ve^v+1\)。连续导数为

\[
\begin{aligned}
T'(v)&=(2v^2-3)e^{2v}+3(v+1)e^v,\\
T''(v)&=(4v^2+4v-6)e^{2v}+3(v+2)e^v,\\
T'''(v)&=(8v^2+16v-8)e^{2v}+3(v+3)e^v,\\
T''''(v)&=(16v^2+48v)e^{2v}+3(v+4)e^v.
\end{aligned}
\]

\(T(0)=T'(0)=T''(0)=0\)、\(T'''(0)=1\)，且 \(T''''(v)>0\) 对
全部 \(v\ge0\) 成立。从零点连续积分给
\(T'''(v)>1\)、\(T''(v)>v\)、\(T'(v)>v^2/2\)，最后
\(T(v)>v^3/6>0\)。于是 \(D(v)<0\)；（NS.4）的分母正，故
\(\Phi''\) 在整个正轴严格递减。由零点连续性及正性，得到
\(0<\Phi''(v)<1/2\)。

**证明：原常数的完整两段积分。** 原定义中的
\(\Phi(v)(1-e^{-v})=v\Phi'(v)\) 直接给

\[
A=\int_0^1\frac{\Phi'(v)-1}{v}\,dv
 +\int_1^\infty\frac{\Phi'(v)-C}{v}\,dv.
\tag{NS.5}
\]

这保持了两段原积分及整个无限尾。由（NS.1），对每个 \(v>0\)，

\[
0<\Phi'(v)-1=\int_0^v\Phi''(w)\,dw<v/2.
\]

近段被积函数在零端连续补成 \(1/2\)，且在正轴严格小于
\(1/2\)。其与常数 \(1/2\) 的差在任意内部正长度紧区间上有
严格正的积分，故近段积分严格小于 \(1/2\)。

使用 §441 中的经典指数积分恒等式，

\[
\Phi(v)=Cv\exp(E_1(v)),\qquad
\Phi'(v)=C\exp(E_1(v))(1-e^{-v}),\qquad
0<E_1(v)\le e^{-v}/v,
\]

得到 \(\Phi'(v)\to C\)。又 \(\Phi''>0\) 使 \(\Phi'\) 严格增加，
因此每个有限 \(v\) 均有 \(\Phi'(v)<C\)，远段被积函数严格为负。
其绝对收敛也直接支付：对 \(v\ge1\)，取固定
\(M=\exp(e^{-1})\)，由 \(e^y-1\le e^y y\) 得

\[
|\Phi'(v)-C|
\le C[\exp(E_1(v))-1+\exp(E_1(v))e^{-v}]
\le CM e^{-v}(1+1/v)\le2CM e^{-v}.
\]

除以 \(v\) 后仍可积。远段在 \([1,2]\) 上连续严格为负，而其余
尾也非正，故完整远段积分严格为负。与已支付的近段合并得到
（NS.2）。证毕。

**定理 444.2（完整肩部的统一严格负界）。** 对所有 \(t>0\)，

\[
K(t)\le A-\Lambda(C-1)<-\delta
=\frac{1-2\log2}{6}<0,
\qquad
\Lambda(k)=k\left[1+\log\frac{1+k}{2k}\right]\quad(k>0).
\tag{NS.6}
\]

因此 \(\sup_{t>0}K(t)<-\delta\)。

**证明：真实斜率与完整比较积分。** §441 通过经典 Gamma 质量、
一阶矩及密度比单交点比较支付了
\(Q(b)-Q(a)>(b-a)/2\)（\(0<a<b\)）。保持原归一化
\(Q(0+)=1\)，固定 \(u>0\) 并令 \(a\downarrow0\)，得到
非严格的极限界

\[
Q(u)\ge1+u/2,\qquad
\frac{1/Q(u)-1}{u}\le-\frac1{u+2}.
\tag{NS.7}
\]

所有分母正；这里没有将严格割线不等式在端点极限中仍宣称为严格。
对任意 \(t>0\)，原肩部积分和比较积分均在整个正轴绝对收敛。
积分比较及完整换元 \(w=t(u+2)\) 给

\[
\begin{aligned}
K(t)&\le A-(C-1)(\log t+\gamma_E)
 -C\int_0^\infty\frac{e^{-tu}}{u+2}\,du\\
&=A-(C-1)(\log t+\gamma_E)-Ce^{2t}E_1(2t).
\end{aligned}
\tag{NS.8}
\]

指数积分的下限为 \(2t\)，上限仍为无穷。

**证明：比较函数的两端与全局最小值。** 写 \(k=C-1>0\)，定义

\[
H(x)=e^xE_1(x),\qquad
\mathcal G(x)=k(\log(x/2)+\gamma_E)+CH(x)\quad(x>0).
\]

（NS.8）即 \(K(t)\le A-\mathcal G(2t)\)。经典指数积分的基本
微积分公式给 \(H'(x)=H(x)-1/x\)，从而导数中的边际系数准确取消为

\[
\mathcal G'(x)=\frac kx+C\left[H(x)-\frac1x\right]
=CH(x)-\frac1x,
\tag{NS.9}
\]

因为 \(k-C=-1\)。

在零端，\(E_1(x)=-\log x-\gamma_E+O(x)\)，所以
\(H(x)=-\log x-\gamma_E+o(1)\)，其中使用
\(x|\log x|\to0\)。于是

\[
\mathcal G(x)=-\log x-\gamma_E-k\log2+o(1)
\longrightarrow+\infty\qquad(x\downarrow0).
\]

在远端，正的 \(H\) 已给
\(\mathcal G(x)\ge k(\log(x/2)+\gamma_E)\to+\infty\)。两端均趋
正无穷的连续函数因而在某个内部点 \(x_0>0\) 取得全局最小值。
（NS.9）给 \(CH(x_0)=1/x_0\)，故

\[
\min_{x>0}\mathcal G(x)
=k(\log(x_0/2)+\gamma_E)+1/x_0.
\]

函数 \(x\mapsto k(\log(x/2)+\gamma_E)+1/x\) 的导数为
\((kx-1)/x^2\)，在 \(x=1/k\) 取得其全局最小值。因此

\[
\min_{x>0}\mathcal G(x)
\ge k[1+\gamma_E-\log(2k)]
=k\left[1+\log\frac{1+k}{2k}\right]=\Lambda(k).
\tag{NS.10}
\]

最后一步保持原 Euler 幅度关系 \(\gamma_E=\log C=\log(1+k)\)。
该全局下界不需要定位 \(x_0\)。

**证明：Euler 常数的经典调和序列界。** 记
\(H_n=\sum_{j=1}^n1/j\)，并用经典下调和序列
\(\gamma_n^-=H_n-\log(n+1)\)。它趋于 \(\gamma_E\)，且

\[
\gamma_{n+1}^--\gamma_n^-
=\frac1{n+1}-\log\left(1+\frac1{n+1}\right)>0.
\]

所以 \(\gamma_E\ge\gamma_1^-=1-\log2\)。再由指数函数的正项
级数 \(e>1+1+1/2+1/6=8/3\)，得到

\[
C=e^{\gamma_E}\ge e/2>4/3,\qquad k>1/3.
\tag{NS.11}
\]

对 \(k>0\)，令 \(r=k/(1+k)\in(0,1)\)。经典对数界
\(\log y\le y-1\) 给

\[
\Lambda'(k)=r-\log(2r)\ge1-r>0.
\]

故

\[
\Lambda(C-1)>\Lambda(1/3)=\frac{1+\log2}{3}
=\frac12+\delta.
\tag{NS.12}
\]

严格积分比较 \(\log2=\int_1^2dw/w>1/2\) 同时支付 \(\delta>0\)。
结合 \(A<1/2\)、（NS.8）与（NS.10），得到（NS.6）。同一上界
\(A-\Lambda(C-1)\) 对所有 \(t>0\) 成立，故其上确界也严格小于
\(-\delta\)。证毕。

**推论 444.3（负最大值分支与实际宏观负修正）。** 推论 443.2
对原实际 \(K\) 落在负最大值分支：其唯一全局最大点 \(t_0\)
满足 \(K(t_0)<-\delta\)，且 \(K\) 没有正零点。对任意固定
\([a,b]\subset(0,\infty)\)，沿实际素数 \(z\to\infty\)，最终对所有
\(t\in[a,b]\) 有

\[
J_z(t/L)-(C-1)\log L<-\delta/2.
\tag{NS.13}
\]

**证明。** 定理 443.1 已支付唯一全局最大点；（NS.6）给该点的
严格负值，故推论 443.2 的负最大值分支适用。§442 的完整宏观
极限在每个固定正 \(t\) 紧区间上一致成立，因此最终

\[
\sup_{t\in[a,b]}
|J_z(t/L)-(C-1)\log L-K(t)|<\delta/2.
\]

与 \(K(t)<-\delta\) 合并即得（NS.13）。证毕。

这里支付的是完整首补偿积分的有限宏观修正：\(J_z(t/L)\) 的正
主项仍为 \((C-1)\log L\)。固定紧区间结论没有给移动
\(t_z\to0\) 或 \(t_z\to\infty\) 的联合均匀性，也没有由此判断
\(\alpha=C,t=t_*\) 时 \(J_z(t_*L^{-C})\to0\) 的有限前缀符号。
完整 Robin 配对中的其余阶乘密度、实际粗糙前缀权重、整数纤维
及互补尾仍需共同的有符号估计。本节将经典指数积分与调和序列界
绑定到原 \(A,Q,K\)，确定的是该原肩部的严格负储备。

**来源。** 原常数 \(A\) 的曲率控制、同一肩部的全轴统一负界及
实际宏观负修正为本仓推导（`repo-derived`）。本节消耗 §441–§443
的原对象与估计；指数积分恒等式、调和序列的 Euler 常数界、
对数与指数的基本不等式及连续函数的全局极小值判据为经典供应。

## 445. 临界阻尼的带符号余项与实际零点偏移

**对象与结论范围。** 沿用 §§441–444 的完整实际素数前缀。令 \(z\ge2\)
为素数，\(p\) 为严格大于 \(z\) 的最小素数，统一使用
\(L=\log p\)、\(\ell=\log z\)。定义仍为

\[
E_z(s)=\prod_{q\le z}(1-q^{-s}),\qquad C_z=E_z(1)^{-1},\qquad
F_z(v)=C_zE_z(1+v/L),
\]

\[
H_z(v)=F_z(v)(1-e^{-v})-v,\qquad
J_z(\sigma)=\int_0^\infty e^{-\sigma v}\frac{H_z(v)}{v^2}\,dv.
\]

乘积包含全部 \(q\le z\) 的素数。本节保留原常数
\(C=e^{\gamma_E}\)、\(\Phi=e^{\operatorname{Ein}}\)、
\(Q(u)=u\zeta(1+u)\)、\(A,Z_0,Z_1,B_*\)，并记

\[
\beta(u)=\frac{1/Q(u)-1}{u},\qquad
t_*=\exp(-\gamma_E-B_*),\qquad
\epsilon_L=L^{1-C}\log L.
\tag{CS.1}
\]

全部前缀极限沿实际素数 \(z\to\infty\) 取得。以下一致性均指
\(t\) 位于任意固定的正紧区间 \([a,b]\subset(0,\infty)\)。

**定理 445.1（原完整积分的首个带符号修正）。** 有

\[
\boxed{
J_z(tL^{-C})=\log(t/t_*)-C(C-1)t\,\epsilon_L
+O(L^{1-C}),
}
\tag{CS.2}
\]

且余项在上述 \(t\) 区间上一致。因此原先常数级极限为零的临界点满足

\[
\boxed{
\frac{J_z(t_*L^{-C})}{L^{1-C}\log L}
\longrightarrow-C(C-1)t_*<0.
}
\tag{CS.3}
\]

特别地，原完整首积分在该临界阻尼处最终严格为负。

**定理 445.2（实际阻尼零点的首个偏移）。** 令
\(\sigma_z\) 为 §441 的唯一实际阻尼零点，\(t_z=\sigma_zL^C\)。则

\[
\boxed{
\frac{t_z/t_*-1}{L^{1-C}\log L}\longrightarrow C(C-1)t_*,
\qquad
t_z-t_*\sim C(C-1)t_*^2L^{1-C}\log L.
}
\tag{CS.4}
\]

等价地，

\[
\boxed{
\sigma_z=t_*L^{-C}
+C(C-1)t_*^2L^{1-2C}\log L
+o(L^{1-2C}\log L).
}
\tag{CS.5}
\]

因此 \(\sigma_z>t_*L^{-C}\) 最终成立。

**证明：所需常数区间。** 本节只需 \(1<C<2\)，可完全由经典积分比较
支付。下端比较给 \(\gamma_E\ge1-\log2>0\)。另一方面，\(1/x\) 严格凸，
故对每个整数 \(n\ge2\)，

\[
\frac1n<\int_{n-1/2}^{n+1/2}\frac{dx}{x}.
\]

求和后令上端趋于无穷，得到 \(\gamma_E\le1-\log(3/2)\)。指数级数中
\(n!\ge2^{n-1}\) 对 \(n\ge2\) 成立，并在 \(n=3\) 严格，故 \(e<3\)。
于是

\[
1<C\le\frac{2e}{3}<2.
\tag{CS.6}
\]

特别地，\(\epsilon_L\to0\)，并且
\(\log L/L=o(L^{1-C})\)。

**证明：临界余项的精确恒等式。** 定义

\[
\mathcal B_z=\int_0^1\frac{H_z(v)}{v^2}\,dv+
\int_1^\infty\frac{F_z(v)(1-e^{-v})}{v^2}\,dv,\qquad
\Delta_z=\mathcal B_z-C\log L-B_*,
\]

\[
\mathcal L_z(\sigma)=\int_0^1(e^{-\sigma v}-1)\frac{H_z(v)}{v^2}\,dv,
\qquad
\mathcal D_z(\sigma)=\int_1^\infty
(1-e^{-\sigma v})\frac{F_z(v)(1-e^{-v})}{v^2}\,dv\ge0.
\tag{CS.7}
\]

§441 的统一局部预算给固定 \(K_0\)，使最终所有前缀在
\(0\le v\le1\) 上满足 \(|H_z(v)|\le K_0v^2\)；远端用
\(F_z\le C_z\)。因此这些积分均绝对收敛。直接在原完整积分的 \(v=1\)
处分割，得到

\[
J_z(\sigma)=\mathcal B_z+\mathcal L_z(\sigma)
-\mathcal D_z(\sigma)-E_1(\sigma).
\]

经典指数积分恒等式
\(E_1(\sigma)=-\log\sigma-\gamma_E+\operatorname{Ein}(\sigma)\)
与原 \(t_*\) 给出精确式

\[
\boxed{
J_z(tL^{-C})=\log(t/t_*)+\Delta_z+\mathcal L_z(tL^{-C})
-\mathcal D_z(tL^{-C})-\operatorname{Ein}(tL^{-C}).
}
\tag{CS.8}
\]

而 \(1-e^{-\sigma v}\le\sigma v\) 给

\[
|\mathcal L_z(\sigma)|\le K_0\sigma/2,\qquad
0\le\operatorname{Ein}(\sigma)\le\sigma.
\tag{CS.9}
\]

**证明：Mertens 归一化、Euler 尾与时钟尾的精确分离。** 对
\(1\le V<L\)，置 \(\varepsilon=V/L\)，定义

\[
N_z(V)=\int_0^V
\frac{[F_z(v)-\Phi(v)](1-e^{-v})}{v^2}\,dv,
\]

\[
a_\infty(V)=\int_V^\infty
\left[\frac{\Phi(v)(1-e^{-v})}{v^2}-\frac Cv\right]\,dv,
\qquad
W(\varepsilon)=\int_\varepsilon^\infty
\frac{du}{u^2\zeta(1+u)},
\]

\[
T_z^E(\varepsilon)=\int_\varepsilon^\infty
\frac{E_z(1+u)-1/\zeta(1+u)}{u^2}\,du\ge0,
\qquad
T_z^p(\varepsilon)=\int_\varepsilon^\infty
\frac{p^{-u}E_z(1+u)}{u^2}\,du\ge0,
\]

\[
\eta_z=\frac{C_z}{L}-C.
\tag{CS.10}
\]

\(\mathcal B_z\) 的近段恰为
\(A+C\log V-a_\infty(V)+N_z(V)\)；远段在 \(v=Lu\) 后恰为

\[
\frac{C_z}{L}[W(\varepsilon)+T_z^E(\varepsilon)-T_z^p(\varepsilon)].
\]

利用 \(1/(u^2\zeta(1+u))=1/u+\beta(u)\)，有

\[
\log\varepsilon+W(\varepsilon)
=Z_0+Z_1-\int_0^\varepsilon\beta(u)\,du.
\]

于是得到全量、带符号的恒等式

\[
\boxed{
\Delta_z=N_z(V)-a_\infty(V)-C\int_0^\varepsilon\beta(u)\,du
+\eta_zW(\varepsilon)
+\frac{C_z}{L}[T_z^E(\varepsilon)-T_z^p(\varepsilon)].
}
\tag{CS.11}
\]

这里 \(W\) 是归一化误差的真实权重；遗漏素数的 Euler 尾为正，
下一素数时钟尾以负号进入。本证明不预设 \(\Delta_z\) 的符号。

**证明：归一化只需既有的弱经典速率。** 复用（CP.7）所用的
[经典 Mertens 供应](../../../Library/notes/pntplus2026mertens.md)。
经典第三 Mertens 的对数误差给

\[
E_3(x)=\sum_{q\le x}\log(1-1/q)+\log\log x+\gamma_E,
\qquad |E_3(x)|\le K/\log x\quad(x\ge2).
\]

这一弱误差采用 Goldmakher 的经典 Mertens 论证；下文也从第一 Mertens
预算与既有第三常数直接推导。Diamond–Pintz 的文献引文确认经典第三
公式，其振荡定理不作为这里误差速率的来源。准确归一化为

\[
\eta_z=C\left[\frac{\ell}{L}e^{-E_3(z)}-1\right].
\tag{CS.12}
\]

因此 \(C_z=C\ell+O(1)\)。Bertrand 给
\(0<L-\ell\le\log2\)，从而

\[
\boxed{C_z=CL+O(1),\qquad \eta_z=O(1/L).}
\tag{CS.13}
\]

也可从同一第一 Mertens 预算直接推出所需速率。写

\[
S(x)=\sum_{q\le x}\frac{\log q}{q-1}=\log x+e(x),
\qquad |e(x)|\le D_S,
\]

其中 \(D_S\) 已由（CP.7）的
\(\left|\sum_{q\le x}\log q/q-\log x\right|\le\log4+4\)
及收敛分母修正
\(\sum_{n\ge2}\log n/[n(n-1)]\) 支付。
令 \(U(x)=\sum_{q\le x}1/(q-1)\)。保留 \(q=2\) 原子的 Abel 恒等式给

\[
\begin{aligned}
U(x)
&=\frac{S(x)}{\log x}+\int_2^x\frac{S(t)}{t\log^2t}\,dt\\
&=\log\log x+U_\infty+\frac{e(x)}{\log x}
-\int_x^\infty\frac{e(t)}{t\log^2t}\,dt.
\end{aligned}
\]

后两项绝对值之和不超过 \(2D_S/\log x\)。对素数 \(q\)，定义

\[
d(q)=-\log(1-1/q)-\frac1{q-1}
=-\sum_{k\ge2}(1-1/k)q^{-k},\qquad |d(q)|\le2/q^2.
\]

故 \(\sum_{q>z}|d(q)|\le2/z\)，而既有定性第三 Mertens 常数识别
\(U_\infty+\sum_qd(q)=\gamma_E\)。于是精确地

\[
\log C_z=\log\ell+\gamma_E+\frac{e(z)}{\ell}
-\int_z^\infty\frac{e(t)}{t\log^2t}\,dt-\sum_{q>z}d(q).
\tag{CS.14}
\]

这再次给出 \(O(1/\ell)\) 的对数归一化误差，并证明（CS.13）；
没有引入有效 PNT 或 RH 前提。

**证明：整个移动分割点的预算。** （PX.6）的全轴误差给

\[
|F_z(v)-\Phi(v)|
\le e(1+v)\frac{Bv}{L}e^{Bv/L}.
\]

因 \((1+v)(1-e^{-v})/v\le2\)，对全部 \(1\le V<L\) 有

\[
|N_z(V)|\le2eB e^{BV/L}V/L.
\tag{CS.15}
\]

由 \(\Phi(v)=Cv\,e^{E_1(v)}\) 和 \(E_1(v)\le e^{-v}/v\)，有固定常数
\(K_a\) 使

\[
|a_\infty(V)|\le K_a e^{-V}/V\qquad(V\ge1).
\]

又由（PX.9），\(-1\le\beta\le0\)，且

\[
W(\varepsilon)\le\log(1/\varepsilon)+1,\qquad
\left|\int_0^\varepsilon\beta(u)\,du\right|\le\varepsilon.
\tag{CS.16}
\]

对每个 \(u>0\)，收敛 Euler 乘积与整数尾积分给

\[
0\le E_z(1+u)-1/\zeta(1+u)
\le\sum_{q>z}q^{-1-u}
\le\sum_{n=z+1}^\infty n^{-1-u}
\le z^{-u}/u.
\]

故整个 Euler 尾和整个时钟尾分别满足

\[
T_z^E(\varepsilon)\le
\frac{e^{-\ell\varepsilon}}{\ell\varepsilon^3},
\qquad
T_z^p(\varepsilon)\le
\frac{e^{-L\varepsilon}}{L\varepsilon^2}.
\tag{CS.17}
\]

取 \(V=4\log L\)、\(\varepsilon=4\log L/L\)。最终 \(1\le V<L\)，且
必须保留 Bertrand 的完整时钟预算：

\[
e^{-\ell\varepsilon}
=L^{-4}\exp(4(L-\ell)\log L/L)=O(L^{-4}).
\]

因此（CS.15）–（CS.17）给

\[
\begin{aligned}
N_z(V)&=O(\log L/L),&
a_\infty(V)&=O(L^{-4}/\log L),\\
\int_0^\varepsilon\beta(u)\,du&=O(\log L/L),&
\eta_zW(\varepsilon)&=O(\log L/L),\\
T_z^E(\varepsilon)&=O(L^{-2}/\log^3L),&
T_z^p(\varepsilon)&=O(L^{-3}/\log^2L).
\end{aligned}
\]

\(C_z/L\) 有界，代入精确式（CS.11）得到

\[
\boxed{\Delta_z=O(\log L/L).}
\tag{CS.18}
\]

**证明：完整阻尼损失。** 置
\(\lambda=\sigma L\)、\(g_z(u)=E_z(1+u)(1-p^{-u})\)。
从（CS.7）对完整损失作变量替换，有

\[
\mathcal D_z(\sigma)=\frac{C_z}{L}
\int_{1/L}^\infty(1-e^{-\lambda u})\frac{g_z(u)}{u^2}\,du.
\tag{CS.19}
\]

在整个 \(1/L\le u\le1\) 上，§441 的全近区包络
\(R_z(Lu)\le2e\,e^B\) 与最终 \(C_z/L\ge C/2\) 给固定 \(M\)，使

\[
\frac{g_z(u)}u=\frac{L}{C_z}R_z(Lu)\le M.
\]

于是完整近段满足

\[
0\le\int_{1/L}^1(1-e^{-\lambda u})\frac{g_z(u)}{u^2}\,du
\le M\lambda.
\tag{CS.20}
\]

在整个 \(u\ge1\) 上，有限乘积不等式给

\[
\begin{aligned}
0\le1-g_z(u)
&\le\sum_{n\ge2}n^{-1-u}+p^{-u}\\
&\le2^{-u}(1/2+1/u)+2^{-u}
\le(5/2)2^{-u}.
\end{aligned}
\]

因此将这一完整远段的 \(g_z\) 替为 \(1\) 所需的误差不超过

\[
\frac52\lambda\int_1^\infty\frac{2^{-u}}u\,du=O(\lambda).
\tag{CS.21}
\]

剩下的模型积分精确为

\[
\begin{aligned}
\int_1^\infty\frac{1-e^{-\lambda u}}{u^2}\,du
&=1-e^{-\lambda}+\lambda E_1(\lambda)\\
&=\lambda[\log(1/\lambda)+1-\gamma_E]+O(\lambda^2).
\end{aligned}
\tag{CS.22}
\]

因此对最终所有前缀与 \(0<\lambda\le1\)，一致有

\[
\mathcal D_z(\sigma)
=C_z\sigma[\log(1/(\sigma L))+O(1)].
\tag{CS.23}
\]

对 \(\sigma=tL^{-C}\)，有
\(\lambda=tL^{1-C}\to0\) 在正紧区间上一致成立。使用（CS.13），得到

\[
\boxed{
\mathcal D_z(tL^{-C})=C(C-1)tL^{1-C}\log L+O(L^{1-C}).
}
\tag{CS.24}
\]

这里 \(\log(1/(\sigma L))=(C-1)\log L-\log t\)；
完整 \(v<L\) 区域只有 \(O(\sigma L)\) 的损失。故主修正系数为
\(C(C-1)\)。

**证明：临界符号与实际零点。** （CS.6）给

\[
\frac{\log L/L}{L^{1-C}}\to0,\qquad
\frac{L^{-C}}{L^{1-C}}\to0.
\]

把（CS.9）、（CS.18）、（CS.24）代回原完整恒等式（CS.8），即得
一致展开（CS.2）。取 \(t=t_*\)，再除以
\(\epsilon_L=L^{1-C}\log L\)，得到（CS.3）。

§441 已证 \(t_z\to t_*\)，故最终 \(t_z\) 位于某个固定正紧区间内。
一致展开允许直接代入实际零点，得到

\[
\log(t_z/t_*)=C(C-1)t_z\epsilon_L+o(\epsilon_L).
\]

右侧为 \(O(\epsilon_L)\)，先得 \(t_z/t_*-1=O(\epsilon_L)\)；
再用 \(\log(1+x)=x+O(x^2)\) 与 \(t_z\to t_*\)，便得（CS.4）。
乘回 \(L^{-C}\) 得（CS.5）。这里无需新增 \(J_z\) 的导数速率。

最后，同一时钟下的精确插入恒等式（PX.2）仍给

\[
I_p(t_*L^{-C})-I_z(t_*L^{-C})
=\frac{J_z(t_*L^{-C})}{p-1}<0
\]

最终成立。本节的符号属于这个原完整首补偿积分；它不直接给出完整
Robin 配对的全局符号。证毕。

**来源。** Bertrand、第一与第三 Mertens、实轴收敛 Euler 乘积及指数积分
和初等积分界为经典供应，Mertens 的来源归属沿用上述文献记录。原
\(\Delta_z\) 的精确有符号分解、全轴余项排序、临界负首修正与实际根位移
为本仓推导（repo-derived），由同一原完整积分及 §§441–444 的预算得出。

## 446. 临界阻尼常数项与同一 ζ 轮廓的对数矩

**对象与范围。** 沿用 §§441–445 的完整实际素数前缀。令 \(z\ge2\)
为素数，\(p\) 为严格大于 \(z\) 的最小素数，统一使用 \(L=\log p\)。
仍令

\[
E_z(s)=\prod_{q\le z}(1-q^{-s}),\qquad C_z=E_z(1)^{-1},\qquad
F_z(v)=C_zE_z(1+v/L),
\]

\[
H_z(v)=F_z(v)(1-e^{-v})-v,\qquad
J_z(\sigma)=\int_0^\infty e^{-\sigma v}\frac{H_z(v)}{v^2}\,dv.
\]

乘积包含全部 \(q\le z\) 的素数。保持原常数
\(C=e^{\gamma_E}\)、\(Q(u)=u\zeta(1+u)\)、\(A,Z_0,Z_1,B_*\)，
以及 \(t_*=\exp(-\gamma_E-B_*)\)。记 \(h_L=L^{1-C}\)。全部前缀
极限沿实际素数 \(z\to\infty\) 取得；以下一致性均指 \(t\) 位于任意
固定正紧区间 \([a,b]\subset(0,\infty)\)。

定义同一宏观轮廓的另一种表示和一个固定常数：

\[
g(u)=\frac1{\zeta(1+u)}=\frac{u}{Q(u)}\quad(u>0),
\qquad
d_*=1-\gamma_E+\int_0^1\frac{du}{Q(u)}
+\int_1^\infty\frac{g(u)-1}{u}\,du.
\tag{CM.1}
\]

这两个积分均绝对收敛。近端由（PX.9）的 \(Q\ge1\) 支付；在整个
\(u\ge1\) 上，经典 Dirichlet 级数与整数尾积分给

\[
0\le1-g(u)\le\zeta(1+u)-1
\le2^{-u}(1/2+1/u)\le\frac32\,2^{-u}.
\]

因此远端绝对值由 \((3/2)2^{-u}/u\) 支配。

**定理 446.1（完整阻尼损失的常数项）。** 沿用（CS.7）的完整正损失
\(\mathcal D_z\)，有

\[
\boxed{
\sup_{t\in[a,b]}
\left|\frac{\mathcal D_z(tL^{-C})}{C_ztL^{-C}}
-\big[(C-1)\log L-\log t+d_*\big]\right|\longrightarrow0.
}
\tag{CM.2}
\]

**定理 446.2（原完整积分与实际零点的常数级修正）。** 在上述紧区间
上一致有

\[
\boxed{
J_z(tL^{-C})=\log(t/t_*)
-CtL^{1-C}\big[(C-1)\log L-\log t+d_*\big]+o(L^{1-C}).
}
\tag{CM.3}
\]

令 \(\sigma_z\) 为 §441 的唯一实际阻尼零点，\(t_z=\sigma_zL^C\)。则

\[
\boxed{
t_z=t_*+Ct_*^2L^{1-C}\big[(C-1)\log L-\log t_*+d_*\big]
+o(L^{1-C}),
}
\tag{CM.4}
\]

\[
\boxed{
\begin{aligned}
\sigma_z={}&t_*L^{-C}
+C(C-1)t_*^2L^{1-2C}\log L\\
&+Ct_*^2(d_*-\log t_*)L^{1-2C}+o(L^{1-2C}).
\end{aligned}
}
\tag{CM.5}
\]

**证明：整个移动近段和完整远尾。** 置
\(\sigma=tL^{-C}\)、\(\lambda=\sigma L=th_L\)，并沿用
\(g_z(u)=E_z(1+u)(1-p^{-u})\)。定义

\[
w_\lambda(u)=\frac{1-e^{-\lambda u}}{\lambda u}
=\int_0^1e^{-s\lambda u}\,ds.
\]

于是 \(0<w_\lambda\le1\)，且 \(w_\lambda\) 随 \(\lambda\) 递减。
对原完整损失使用（CS.19），精确得到

\[
\frac{\mathcal D_z(\sigma)}{C_z\sigma}
=\int_{1/L}^\infty w_\lambda(u)\frac{g_z(u)}u\,du.
\tag{CM.6}
\]

在整个移动区间 \(1/L\le u\le1\) 上，§441 的原全近区包络和
（CS.13）的最终 \(C_z/L\ge C/2\) 给固定 \(M\)，使

\[
0\le\frac{g_z(u)}u=\frac{L}{C_z}R_z(Lu)\le M.
\]

将这份近段被积函数在 \(0<u<1/L\) 上补为零，便在固定区间
\((0,1)\) 上得到同一个可积主导 \(M\)。对每个固定 \(u>0\)，
实轴绝对收敛 Euler 乘积和 \(p^{-u}\to0\) 给
\(g_z(u)\to g(u)\)。近段的零延拓因此在 \(L^1(0,1)\) 中收敛到
\(g(u)/u=1/Q(u)\)。

在整个 \(u\ge1\) 上，§445 已付的有限乘积界给

\[
0\le1-g_z(u)\le\frac52\,2^{-u}.
\]

结合原 \(g\) 的远端界，差
\([(g_z-1)-(g-1)]/u\) 的绝对值由 \(4\cdot2^{-u}/u\) 支付。
支配收敛于是同时给出两个完整的绝对差极限：

\[
\begin{aligned}
\int_0^1\left|
\boldsymbol 1_{[1/L,1]}(u)\frac{g_z(u)}u-\frac1{Q(u)}
\right|du&\longrightarrow0,\\
\int_1^\infty\frac{|g_z(u)-g(u)|}{u}\,du&\longrightarrow0.
\end{aligned}
\tag{CM.7}
\]

这里的零延拓保留（CM.6）的原近段，整个远尾也未被截去。

**证明：模型常数与一致性。** 经典指数积分模型满足

\[
\begin{aligned}
\frac1\lambda\int_1^\infty\frac{1-e^{-\lambda u}}{u^2}\,du
&=\frac{1-e^{-\lambda}}\lambda+E_1(\lambda)\\
&=\log(1/\lambda)+1-\gamma_E+O(\lambda).
\end{aligned}
\tag{CM.8}
\]

从（CM.6）减去这一完整模型，精确剩下

\[
\int_{1/L}^1w_\lambda(u)\frac{g_z(u)}u\,du
+\int_1^\infty w_\lambda(u)\frac{g_z(u)-1}u\,du.
\]

先用 \(w_\lambda\le1\) 和（CM.7）替换为极限轮廓，误差不超过两项
与 \(t\) 无关的绝对差积分。再移除极限轮廓上的 \(w_\lambda\)，对
\(t\in[a,b]\) 有

\[
\sup_{t\in[a,b]}|w_{th_L}(u)-1|
\le1-w_{bh_L}(u)\longrightarrow0.
\]

近段主导为 \(1/Q\le1\)，远段主导为 \((3/2)2^{-u}/u\)，所以第二步
误差也一致趋于零。（CM.8）的模型余量一致为 \(O(bh_L)\)。因
\(C>1\)，\(h_L\to0\)，合并得到（CM.2）。这一极限只需上述全段
支配收敛，无需新增 Euler 尾收敛速率。

**证明：原归一化和局部项的排序。** 沿用 §445 的同一精确恒等式
（CS.8）：

\[
J_z(tL^{-C})=\log(t/t_*)+\Delta_z+\mathcal L_z(tL^{-C})
-\mathcal D_z(tL^{-C})-\operatorname{Ein}(tL^{-C}).
\]

已付（CS.13）给 \(C_z=CL+O(1)\)，所以在固定正 \(t\) 紧区间上

\[
C_ztL^{-C}=Cth_L+O(h_L/L).
\]

归一化误差乘上（CM.2）中的 \(O(\log L)\) 括号，只产生
\(O(h_L\log L/L)=o(h_L)\)。已付（CS.18）与（CS.9）分别给

\[
\Delta_z=O(\log L/L)=o(h_L),\qquad
\mathcal L_z(tL^{-C})-\operatorname{Ein}(tL^{-C})
=O(L^{-C})=o(h_L).
\tag{CM.9}
\]

第一项使用已证 \(C<2\)，因为
\((\log L/L)/h_L=L^{C-2}\log L\to0\)；第二项使用
\(L^{-C}/h_L=1/L\)。把（CM.2）代入原完整恒等式即得（CM.3）。
这里保留 §445 已付的移动 Euler 尾和归一化预算，没有用定性收敛替代
这些原误差的速率。

**证明：实际根的常数级残量。** §441 已证 \(t_z\to t_*\)，所以实际根
最终落在某个固定正紧区间。§445 的首位移同时给
\(t_z-t_*=O(h_L\log L)\)。由（CM.3）的一致性可以直接代入实际根，
得到

\[
\log(t_z/t_*)
=Ct_zh_L\big[(C-1)\log L-\log t_z+d_*\big]+o(h_L).
\]

左侧对 \(t_z-t_*\) 线性化的误差为
\(O(h_L^2\log^2L)\)。右侧括号乘 \(t_z\) 的函数，在固定正紧区间上
关于 \(t_z\) 的导数为 \(O(\log L)\)，所以把右侧 \(t_z\) 替为
\(t_*\)，再乘 \(h_L\)，误差同为 \(O(h_L^2\log^2L)\)。由于 \(C>1\)，

\[
h_L^2\log^2L=o(h_L).
\]

因此左侧为 \((t_z-t_*)/t_*+o(h_L)\)，右侧可以使用原 \(t_*\)，即得
（CM.4）。乘回 \(L^{-C}\) 并拆开对数项得到（CM.5）。这一根展开
不需要新增 \(J_z\) 的导数估计。证毕。

**定理 446.3（同一宏观轮廓的绝对对数矩）。** 将（CM.1）的 \(g\)
在非正半轴补成零，则 \(g\) 是连续分布函数，在 \(u>0\) 上有严格
正密度 \(g'(u)\)，且

\[
\int_0^\infty g'(u)\,du=1,\qquad
\int_0^\infty g'(u)|\log u|\,du<\infty.
\tag{CM.10}
\]

其对数矩精确给出

\[
\boxed{
d_*=1-\gamma_E-\int_0^\infty g'(u)\log u\,du,
\qquad
d_*-\log t_*=1+B_*-\int_0^\infty g'(u)\log u\,du.
}
\tag{CM.11}
\]

**证明：密度与两个边界。** 经典 Dirichlet 级数在任意正 \(u\)
紧区间上可逐项求导。若其下端为 \(a>0\)，导数级数绝对值由
\(\sum_{n\ge2}(\log n)n^{-1-a}<\infty\) 一致支配；该级数的收敛由
整数尾积分支付。因此

\[
g'(u)=\frac{\sum_{n\ge2}(\log n)n^{-1-u}}{\zeta(1+u)^2}>0.
\]

又 \(0<g(u)=u/Q(u)\le u\)，故 \(g(0+)=0\)；（CM.1）后的指数尾界
给 \(g(\infty)=1\)。这支付连续分布函数的两个端点。基本微积分给
\(\int_\varepsilon^R g'=g(R)-g(\varepsilon)\)，令
\(\varepsilon\downarrow0\)、\(R\to\infty\)，由非负性得到总密度为一。

对 \(0<\varepsilon<1<R\)，分别积分分部，得到

\[
\begin{aligned}
\int_\varepsilon^1(-\log u)g'(u)\,du
&=g(\varepsilon)\log\varepsilon
+\int_\varepsilon^1\frac{g(u)}u\,du,\\
\int_1^R(\log u)g'(u)\,du
&=[g(R)-1]\log R
+\int_1^R\frac{1-g(u)}u\,du.
\end{aligned}
\tag{CM.12}
\]

两个边界项分别满足
\(|g(\varepsilon)\log\varepsilon|\le\varepsilon|\log\varepsilon|\to0\)
和 \(|[g(R)-1]\log R|\le(3/2)2^{-R}\log R\to0\)。两份右侧积分
均已由（CM.1）的近端和远端主导支付。非负被积函数的极限于是给

\[
\int_0^1(-\log u)g'(u)\,du=\int_0^1\frac{du}{Q(u)},\qquad
\int_1^\infty(\log u)g'(u)\,du
=\int_1^\infty\frac{1-g(u)}u\,du.
\]

这同时证明（CM.10）的绝对对数可积性。相减并代入原 \(d_*\) 定义，
得到（CM.11）的第一式；再用原 \(\log t_*=-\gamma_E-B_*\)，得到
第二式。证毕。

（CM.11）把（CM.5）的常数级系数写成
\(Ct_*^2[1+B_*-\int_0^\infty g'(u)\log u\,du]\)。§441 的宏观交点
由 \(C/Q(u)\) 控制；本节的下一常数由同一轮廓
\(g(u)=u/Q(u)\) 的完整对数矩控制。点态交点与全域矩是这份实际
前缀轮廓的两种不同读出，原 \(J_z\) 和时钟始终相同。

本节结论属于（PX.2）的完整首补偿积分及其阻尼零点。完整 Robin
配对在更新粗糙前缀和所有整数纤维后仍需共同的有符号估计；上述
对数矩表示没有支付该估计。

**来源。** 实轴绝对收敛 Euler 乘积、经典 ζ Dirichlet 级数及其局部
一致逐项微分、指数积分模型、支配收敛和积分分部为经典供应；ζ 级数
参见 [NIST DLMF 25.2.1](https://dlmf.nist.gov/25.2.E1)。Mertens
归一化、移动近段和 Euler 尾预算均沿用 §445。完整损失的常数级一致
匹配、实际阻尼零点的常数级残量，以及同一宏观轮廓的对数矩表示为
本仓推导（repo-derived）。

## 447. 完整指数平均中的额外统一肩部储备

**对象与条件。** 保留 §441–§446 的同一个实际素数前缀、原字面轮廓
\(\Phi\)、原完整两段常数 \(A\)、原归一化
\(Q(u)=u\zeta(1+u)\)，以及原完整肩部

\[
K(t)=A-(C-1)(\log t+\gamma_E)
 +C\int_0^\infty e^{-tu}\frac{1/Q(u)-1}{u}\,du,
\qquad C=e^{\gamma_E},\quad t>0.
\]

令 \(k=C-1>0\)，保持 §444 的

\[
\Lambda(k)=k\left[1+\log\frac{1+k}{2k}\right],
\qquad \delta=\frac{2\log2-1}{6}>0.
\]

下面所有指数积分都保留完整无穷尾。定义

\[
E_1(x)=\int_x^\infty\frac{e^{-y}}y\,dy,
\quad H(x)=e^xE_1(x),
\quad
G(x)=k(\log(x/2)+\gamma_E)+CH(x),\qquad x>0.
\]

§444 已证明 \(A<1/2\)、\(k>1/3\)、
\(\Lambda(k)>1/2+\delta\)，以及对全部 \(t>0\) 的原比较
\(K(t)\le A-G(2t)\)。本节先给同一 \(G\ge\Lambda\) 的替代证明，
随后证明一个显式正的额外储备，因而严格加强原统一负界。

**引理 447.1（完整指数平均恒等式）。** 令

\[
h(y)=k(\log(y/2)+\gamma_E)+\frac1y,\qquad y>0.
\]

则对每个 \(x>0\)，完整地有

\[
G(x)=e^x\int_x^\infty e^{-y}h(y)\,dy
 =\int_0^\infty e^{-v}h(x+v)\,dv,
\qquad
e^x\int_x^\infty e^{-y}\,dy=1.
\tag{EA.1}
\]

**完整可积性。** 固定 \(x>0\)。原 Gamma 积分供应给
\(\int_0^\infty e^{-y}|\log y|\,dy<\infty\)，而
\(e^{-y}/y\le e^{-y}/x\) 对全部 \(y>x\) 成立。
因此

\[
e^{-y}|h(y)|
\le k e^{-y}|\log y|
 +k(|\log2|+|\gamma_E|)e^{-y}+\frac{e^{-y}}y
\]

在整个 \((x,\infty)\) 上可积。这也支付下文的全部完整平均和
常数差积分；没有从一个积分值等式反推可积性。

**恒等式证明。** 原完整有限／无限 FTC 给

\[
\int_x^\infty e^{-y}\log y\,dy
 =e^{-x}\log x+E_1(x),\qquad
\int_x^\infty e^{-y}\,dy=e^{-x}.
\]

代入 \(h\)，利用准确的 \(k+1=C\)，得到

\[
\begin{aligned}
e^x\int_x^\infty e^{-y}h(y)\,dy
 &=k(\log(x/2)+\gamma_E)+(k+1)e^xE_1(x)\\
 &=G(x).
\end{aligned}
\]

完整平移 \(y=x+v\) 给（EA.1）的第二式。权重质量由完整指数尾
精确计算为一。这里无须寻找 \(G\) 的全局极小点。证毕。

**引理 447.2（唯一等号层之外的对数差）。** 对 \(r>0\) 令

\[
f(r)=\log r+\frac1r-1.
\]

则 \(f(r)\ge0\)，等号恰在 \(r=1\)。对任意 \(a>1\) 和
\(r\ge a\)，还有 \(f(r)\ge f(a)>0\)。原 Euler 幅度关系
\(\gamma_E=\log C=\log(1+k)\) 给准确恒等式

\[
h(y)-\Lambda(k)=k f(ky)\ge0,\qquad y>0.
\tag{EA.2}
\]

**证明。** 经典严格对数切线界等价于
\(\log r\ge1-1/r\)，在 \(r\ne1\) 时严格。
若 \(r\ge a>1\)，将同一非严格界应用于 \(r/a\)，得到

\[
\begin{aligned}
f(r)-f(a)
 &=\log(r/a)+\frac1r-\frac1a\\
 &\ge1-\frac ar+\frac1r-\frac1a
 =(a-1)\left(\frac1a-\frac1r\right)\ge0.
\end{aligned}
\]

（EA.2）由 \(\log(ky)=\log k+\log y\) 与原 \(C=1+k\)
直接展开；不改变归一化常数。证毕。

（EA.1）与（EA.2）已立即给 \(G(x)\ge\Lambda(k)\)。这是
§444 同一比较函数下界的完整平均证明。进一步，非退化的完整指数
权重不能仅支撑于单一等号层 \(ky=1\)，因此可以支付显式正储备。

**定理 447.3（完整平均的显式额外储备）。** 对任意 \(a>1\)，定义

\[
m_a(k)=k e^{-a/k}\left(\log a+\frac1a-1\right)>0.
\]

则对所有 \(x>0\)，同一个固定常数满足

\[
G(x)\ge\Lambda(k)+m_a(k).
\tag{EA.3}
\]

**证明。** 由完整单位质量平均和（EA.2），

\[
G(x)-\Lambda(k)
 =e^x\int_x^\infty e^{-y}k f(ky)\,dy.
\]

整个被积函数非负。在完整尾 \(y>x+a/k\) 上，
\(ky>kx+a>a\)，所以 \(f(ky)\ge f(a)>0\)。保留该完整尾、
以非负性支付其余部分，准确地得到

\[
\begin{aligned}
G(x)-\Lambda(k)
 &\ge e^x k f(a)\int_{x+a/k}^\infty e^{-y}\,dy\\
 &=k f(a)e^{-a/k}=m_a(k).
\end{aligned}
\]

所取尾的权重质量恰为 \(e^{-a/k}\)，独立于 \(x\)。此处是在完整
积分上比较两个可积核，保留的也是整个无穷尾；没有将有限截断称为
完整平均。证毕。

**推论 447.4（原完整肩部的严格加强）。** 取 \(a=2\)，记

\[
m(k)=k e^{-2/k}(\log2-1/2)=3k\delta e^{-2/k}>0.
\]

则对所有 \(t>0\)，

\[
K(t)\le A-\Lambda(k)-m(k)
 <-\delta(1+e^{-6})< -\delta<0,
\qquad
\sup_{t>0}K(t)<-\delta(1+e^{-6}).
\tag{EA.4}
\]

**证明。** 原 \(K(t)\le A-G(2t)\) 与（EA.3）直接给第一个
非严格界。由于原 \(k>1/3\)，有 \(2/k<6\)，因此

\[
m(k)=3k\delta e^{-2/k}>\delta e^{-6}.
\]

再由原 \(A<1/2\)、\(\Lambda(k)>1/2+\delta\)，得到
\(A-\Lambda(k)-m(k)<-\delta(1+e^{-6})\)。同一个固定上界
\(A-\Lambda(k)-m(k)\) 严格低于目标，故上确界也严格低于目标。
不是从各点严格界未经统一储备便推出严格上确界。证毕。

**完整平均的递推关系。** 同一个（EA.1）对任意 \(s>0\) 还给

\[
G(x)=\int_0^s e^{-v}h(x+v)\,dv+e^{-s}G(x+s).
\tag{EA.5}
\]

这是完整平均在平移下的精确递推；迭代保持同一无穷尾。
等价的正轴微分关系是 \(G'(x)=G(x)-h(x)\)，即 §444 中准确的
\(G'(x)=CH(x)-1/x\)。额外储备来自等号层之外的固定正质量，
不是由递推形式本身推断出符号。此处的平均、平移与递推有准确的
数学关系，无须赋予不同 RH 等价判据一个未定义的群结构。

**结论范围。** （EA.1）–（EA.2）为已得 \(G\ge\Lambda\) 的
替代证明；（EA.3）–（EA.4）给明确的严格加强。它们保持原
\(A,C,Q,K\)，只加强完整首补偿积分的宏观肩部储备。没有因此支付
完整 Robin 配对中其他权重、整数纤维或互补尾，也没有给出 RH 的
证明、实际移动价格带的联合均匀估计或临界阻尼根的新精细项。

**来源。** 完整指数积分、Gamma 对数核可积性、对数切线不等式与
指数尾质量都是经典供应；本节不将这些中间供应独立主张为原创。
将完整指数平均及其等号层之外的正质量绑定到同一原肩部，得到
（EA.3）–（EA.4）的统一额外储备，为本仓推导（`repo-derived`）。

## 448. 实际素数极值、Fibonacci 概率读出与正 Laplace 原子的失效边界

**对象。** 保持 §§441–446 的原完整素数前缀、下一素数时钟
\(L=\log p\) 以及完整 \(J_z\) 和损失 \(\mathcal D_z\)。本节使用

\[
g(u)=\frac1{\zeta(1+u)},\qquad
g_z(u)=E_z(1+u)(1-p^{-u})\quad(u>0).
\]

同时回到 §§384–385 的同一实际 Fibonacci 原子来源：

\[
0<q=\varphi_{\rm gold}^{-2}<2/5,\qquad
\beta_d=\log(1-(-q)^d),\qquad
\mathcal B(s)=\sum_{d\ge1}\beta_dd^{-s},\qquad e=\mu*\beta.
\]

这里 \(\varphi_{\rm gold}=(1+\sqrt5)/2\)，不与原轮廓
\(\Phi=\exp(\operatorname{Ein})\) 混用。记 \(b=\beta_1=\log(1+q)>0\)，并定义

\[
\mathsf F(u)=\frac{\mathcal B(1+u)}{b\,\zeta(1+u)}
=\frac1b\sum_{n\ge1}\frac{e_n}{n^{1+u}}\quad(u>0).
\tag{PM.1}
\]

最后一个级数在每个 \(u>0\) 绝对收敛，来源正是（385.5）的原
\(e_n\)，包括已校正的 \(e_1=b\)。

**定理 448.1（同一 Euler 乘积的真实极值实现）。** 存在相互独立的随机
变量 \(B_r,T_r\)，由全部素数 \(r\) 编号，满足

\[
\mathbb P(B_r=1)=1/r,\qquad
\mathbb P(T_r>u)=e^{-u\log r},\qquad X_r=B_rT_r.
\]

令

\[
U=\sup_rX_r,\qquad
M_z=\max\!\left(\max_{r\le z}X_r,T_p\right).
\]

则 \(0<U<\infty\) 几乎处处，且原两个轮廓精确为

\[
\boxed{\mathbb P(U\le u)=g(u),\qquad
\mathbb P(M_z\le u)=g_z(u)\quad(u>0).}
\tag{PM.2}
\]

\(U\) 的最大值几乎处处由唯一素数取得。在这个实现中，
有限实际前缀的下一素数时钟 \(T_p\) 没有 Bernoulli 稀释。

**证明。** 对每个素数，
\(\mathbb P(X_r\le u)=1-r^{-1-u}\)。有限乘积与递减事件的概率连续性
给

\[
\mathbb P(U\le u)=\prod_r(1-r^{-1-u})=\zeta(1+u)^{-1}.
\]

经典实轴 Euler 乘积在 \(u>0\) 绝对收敛。由 \(g(0+)=0\)、
\(g(\infty)=1\)，得到 \(0<U<\infty\) 几乎处处。对每个固定有理数
\(a>0\)，\(\sum_r\mathbb P(X_r>a)=\sum_rr^{-1-a}<\infty\)；
因此几乎处处只有有限多个 \(X_r>a\)。在全部正有理 \(a\) 上同时取这项
结论，当 \(U>0\) 时即可从某个有限集合取得最大值。两个不同素数的正值
连续且独立，故其相等的概率为零；可数对的并集仍为零。有限
\(r\le z\) 与独立 \(T_p\) 的分布函数乘积给 \(g_z\)。证毕。

进一步，唯一获胜素数的联合密度为

\[
\mathbb P(U\in du,\ r\text{ 获胜})
=g(u)\frac{\log r}{r^{1+u}-1}\,du,
\]

故

\[
g'(u)=\sum_r g(u)\frac{\log r}{r^{1+u}-1}>0.
\tag{PM.3}
\]

局部逐项微分由 \(\sum_{n\ge2}(\log n)n^{-1-a}<\infty\) 支付；
非负积分交换给全部获胜素数的质量和为一。这种素数标记实现保留全部素数，
不只保留自身为 Fibonacci 项的素数。

**定理 448.2（原有限损失的精确对数矩与带方向余量）。** 令
\(Y_z=\max(M_z,1/L)\)、\(\lambda=\sigma L\)，其中最终 \(L>1\)。则对全部
\(\sigma>0\) 精确有

\[
\boxed{
\frac{\mathcal D_z(\sigma)}{C_z\sigma}
=\log(1/\lambda)+1-\gamma_E-\mathbb E\log Y_z+r_z(\lambda),
}
\tag{PM.4}
\]

\[
\boxed{0\le r_z(\lambda)\le\frac{\lambda}{2}\mathbb EY_z.}
\tag{PM.5}
\]

沿实际前缀，\(\mathbb EY_z\) 一致有界，且
\(\mathbb E\log Y_z\to\mathbb E\log U\)。因此 §446 的原常数正是
\(d_*=1-\gamma_E-\mathbb E\log U\)。

**证明。** 对完整损失（CS.19）使用非负 Tonelli，得到

\[
\frac{\mathcal D_z(\sigma)}{C_z\sigma}
=\mathbb E K_\lambda(Y_z),\qquad
K_\lambda(y)=\int_y^\infty\frac{1-e^{-\lambda u}}{\lambda u^2}\,du
=\frac{1-e^{-\lambda y}}{\lambda y}+E_1(\lambda y).
\tag{PM.6}
\]

这里 \(Y_z\) 的分布函数在 \(u<1/L\) 为零，在 \(u\ge1/L\) 为
\(g_z(u)\)，包括 \(1/L\) 处的原子，所以该期望保留原移动近段。
指数积分恒等式给

\[
K_\lambda(y)=\log(1/\lambda)+1-\gamma_E-\log y+\mathsf R(\lambda y),
\]

\[
\mathsf R(a)=\operatorname{Ein}(a)+\frac{1-e^{-a}}a-1,\qquad
\mathsf R(0)=0,\qquad
\mathsf R'(a)=\frac{a-1+e^{-a}}{a^2}.
\]

由于
\(a-1+e^{-a}=\int_0^a(1-e^{-t})dt\)，有
\(0\le\mathsf R'(a)\le1/2\)，从而
\(0\le\mathsf R(a)\le a/2\)。取期望即得（PM.4）–（PM.5）。

整个 \(u\ge1\) 上的原预算
\(1-g_z(u)\le(5/2)2^{-u}\) 给

\[
\mathbb EY_z\le1+\frac52\int_1^\infty2^{-u}\,du<\infty
\tag{PM.7}
\]

且常数不依赖最终 \(z\)。对数矩在有限前缀中存在，因为
\(Y_z\ge1/L>0\) 且上述远尾可积。精确积分分部给

\[
\mathbb E\log Y_z
=-\int_{1/L}^1\frac{g_z(u)}u\,du
+\int_1^\infty\frac{1-g_z(u)}u\,du.
\]

将近段在 \(u<1/L\) 补零，§446 已付的全近区包络给固定主导 \(M\)；
远段主导为 \((5/2)2^{-u}/u\)。固定 \(u>0\) 时 \(g_z(u)\to g(u)\)，
所以支配收敛给

\[
\mathbb E\log Y_z\longrightarrow
-\int_0^1\frac{g(u)}u\,du+\int_1^\infty\frac{1-g(u)}u\,du
=\mathbb E\log U.
\tag{PM.8}
\]

所有近段、整个远尾与两个矩边界均在极限前支付。证毕。

**定理 448.3（实际 Fibonacci 带权来源也是极值分布）。** 对全部实数
\(s\ge0\)，有

\[
0<\mathcal B(s)<b,\qquad
\mathcal B'(s)\ge
\frac{187}{1323}\,q^2(\log2)\,2^{-s}>0.
\tag{PM.9}
\]

因此 \(\mathsf F\) 在非正半轴补零后是连续分布函数，正半轴有严格正密度
\(f_{\rm Fib}=\mathsf F'\)。存在与 \(U\) 独立的非负随机变量 \(V\)，满足

\[
\mathbb P(V\le u)=\mathcal B(1+u)/b\quad(u\ge0),
\]

从而 \(W=\max(U,V)\) 的分布函数精确为 \(\mathsf F\)。
\(V\) 在零点有质量 \(\mathcal B(1)/b\)，而 \(W\) 无零点原子。并且

\[
\boxed{
\mathbb E\log W-\mathbb E\log U
=\int_0^\infty \frac{g(u)}u
\left[1-\frac{\mathcal B(1+u)}b\right]du>0.
}
\tag{PM.10}
\]

**证明：实际带权乘子的非负实轴单调性。** \(\beta_d\) 的指数尾已付全部固定
阶逐项微分。偶数 \(d\) 的 \(\beta_d\) 为负，奇数 \(d\) 的
\(\beta_d\) 为正，且

\[
-\beta_2\ge q^2,\qquad \beta_d\le q^d\quad(d\text{ 为奇数}).
\]

因 \(d\ge3\) 时 \((\log d)/d\le(\log3)/3\)，对 \(s\ge0\)，

\[
\begin{aligned}
\mathcal B'(s)
&\ge2^{-s}\left[q^2\log2-\sum_{\substack{d\ge3\\d\ {\rm odd}}}q^d\log d\right],\\
\sum_{\substack{d\ge3\\d\ {\rm odd}}}q^d\log d
&\le\frac{\log3}{3}\frac{q^3(3-q^2)}{(1-q^2)^2}.
\end{aligned}
\]

函数 \(q(3-q^2)/(1-q^2)^2\) 的导数为
\((3+6q^2-q^4)/(1-q^2)^3>0\)，故在 \(0<q<2/5\) 递增。
又 \(3^5<2^8\) 给 \(\log3/\log2<8/5\)，所以最后尾项与
\(q^2\log2\) 的比不超过

\[
\frac8{15}\frac{710}{441}=\frac{1136}{1323}<1.
\]

这支付（PM.9）的导数界。正性也可直接由

\[
\mathcal B(s)\ge\log(1+q)-\sum_{j\ge1}|\beta_{2j}|
\ge\frac{q}{1+q}-\frac{q^2}{(1-q^2)^2}>0
\]

得到；最后比较使用
\((1-q^2)^2>q(1+q)\)，在 \(q\le2/5\) 上由
\(441/625>14/25\) 支付。由于 \(\mathcal B(s)\to b\)，严格递增又给
\(\mathcal B(s)<b\)。此外，令
\(S_{\beta,\ge2}=\sum_{d\ge2}|\beta_d|<\infty\)，有

\[
0<b-\mathcal B(s)\le S_{\beta,\ge2}\,2^{-s}.
\tag{PM.11}
\]

于是 \(\mathcal B(1+u)/b\) 是带零点原子的非负变量分布函数。
独立极值的乘积分布给（PM.1）的原 \(\mathsf F\)，其导数正性来自
\(\mathcal B,\mathcal B',g,g'>0\)。又 \(0<\mathsf F<g\le u\) 在近端成立，
远端 \(1-\mathsf F\) 由固定常数乘 \(2^{-u}\) 支付，所以
\(\mathbb E|\log W|<\infty\)。两个绝对对数矩相减得到（PM.10），
近端主导为一，远端由（PM.11）支付。其被积函数在全部 \(u>0\)
严格为正。证毕。

**定理 448.4（原 signed 来源的完整对数矩）。** 以下级数均按自然前缀
\(n\le N\) 取极限。对每个实数 \(r>-1\)，有

\[
\boxed{
\sum_{n\ge2}\frac{\mu(n)}{n(\log n)^r}
=-\frac{\mathbb EU^r}{\Gamma(1+r)}<0,\qquad
\sum_{n\ge2}\frac{e_n}{n(\log n)^r}
=-\frac{b\,\mathbb EW^r}{\Gamma(1+r)}<0.
}
\tag{PM.12}
\]

在零阶对 \(r\) 微分，得到

\[
\boxed{
\begin{aligned}
\mathbb E\log U&=-\gamma_E+
\sum_{n\ge2}\frac{\mu(n)\log\log n}{n},\\
\mathbb E\log W&=-\gamma_E+
\frac1b\sum_{n\ge2}\frac{e_n\log\log n}{n},\\
d_*&=1-\sum_{n\ge2}\frac{\mu(n)\log\log n}{n}.
\end{aligned}}
\tag{PM.13}
\]

因此（PM.10）是同一实际 Fibonacci 与 Möbius 系数的严格完整比较，而非
有限素原子的数值巧合。

**证明：条件矩、共同解析域与自然截止。** 复用 §424 的无条件定量
Mertens 供应及 §414 的实际 Fibonacci 转移；扩大有限头后，
\(|M(N)|,|H_{\rm raw}(N)|\) 分别不超过固定常数乘
\(N/(1+\log N)^4\)。对 \(a=\mu\) 或 \(a=e\)，Abel 求和因此使

\[
S_a(r)=\sum_{n\ge2}a_n/[n(\log n)^r]
\]

在 \(\Re r>-3\) 局部一致收敛并全纯。删去 \(n=1\) 只改变固定常数。
具体地，原部分和乘末项趋零；
导数权重与部分和的乘积由常数倍

\[
\frac{1}{x(\log x)^{4+\Re r}}
\left(1+\frac{1+|r|}{\log x}\right)
\]

支配。每个紧域的下端 \(\Re r>-3\) 支付尾积分；对 \(r\) 求导只增加
有限次 \(\log\log x\)，仍可积。这里没有对条件级数作无偿无限重排。

\(U,W\) 的分布函数在近端均不超过 \(u\)，远端生存函数均为指数小量，
故其矩函数 \(\mathbb EU^r,\mathbb EW^r\) 在 \(\Re r>-1\) 全纯。
近端负矩由积分分部
\(\int_0^1u^{-a}dF(u)\le1+a\int_0^1u^{-a}du\)（\(0<a<1\)）
支付；紧域上的对数导数由稍扩大的同一指数区间支配。

先在实数 \(r>1\) 使用尾积分矩公式。由于 \(|e_n|\) 有界，
\(\sum_{n\ge2}|a_n|/[n(\log n)^r]<\infty\)，可以绝对交换，从
\(1-F(u)=-a_1^{-1}\sum_{n\ge2}a_nn^{-1-u}\) 得

\[
\mathbb EX^r=-\frac{\Gamma(1+r)}{a_1}S_a(r),
\]

其中 \((X,a_1)=(U,1)\) 或 \((W,b)\)。
在共同半平面 \(\Re r>-1\) 使用解析恒等定理，得到（PM.12）。
\(S_a(0)=-a_1\)、\(\Gamma'(1)=-\gamma_E\) 及局部一致逐项求导给
（PM.13）。证毕。

**定理 448.5（同一正概率密度不能成为正 Laplace 原子）。** 记
\(f_\mu=g'\)、\(f_{\rm Fib}=\mathsf F'\)，并令

\[
u_m=\frac{m}{\log6}-1\quad(m\text{ 为充分大的正整数}).
\]

原实际来源满足两个严格负的高阶导数极限：

\[
\boxed{
\begin{aligned}
\frac{(-1)^{m-1}f_\mu^{(m-1)}(u_m)}
     {(\log6)^m e^{-m}}&\longrightarrow-1,\\
\frac{(-1)^{m-1}f_{\rm Fib}^{(m-1)}(u_m)}
     {(\log6)^m e^{-m}}&\longrightarrow
-\frac{\log(1+q+q^2)}b<0.
\end{aligned}}
\tag{PM.14}
\]

因此这两个严格正密度均不完全单调，均不存在在全部 \(u>0\) 上有效的
正测度表示 \(f(u)=\int_{[0,\infty)}e^{-ut}\,d\nu(t)\)。

**证明：实际复合原子的局部化与整个无穷尾。** 在固定 \(u>0\) 的紧区间上，
两个绝对 Dirichlet 级数可作任意固定阶微分。对
\(a=\mu\) 或 \(a=e\)，其密度为

\[
f_a(u)=-\frac1{a_1}\sum_{n\ge2}
a_n\frac{\log n}{n}e^{-u\log n}.
\]

代入 \(u_m\)，精确得到

\[
\frac{(-1)^{m-1}f_a^{(m-1)}(u_m)}
     {(\log6)^m e^{-m}}
=-\frac1{a_1}\sum_{n\ge2}a_n\rho_n^m,\qquad
\rho_n=\frac{\log n}{\log6}
\exp\!\left(1-\frac{\log n}{\log6}\right).
\tag{PM.15}
\]

\(x e^{1-x}\le1\)，且仅在 \(x=1\) 等号成立，所以 \(\rho_6=1\)，
其余全部 \(\rho_n<1\)。选择一个固定整数 \(m_0>\log6\)。那么

\[
\sum_{n\ge2}\rho_n^{m_0}
=\frac{e^{m_0}}{(\log6)^{m_0}}
\sum_{n\ge2}\frac{(\log n)^{m_0}}{n^{m_0/\log6}}<\infty.
\tag{PM.16}
\]

该完整整数尾由指数 \(m_0/\log6>1\) 的积分检验支付。
\(\mu\) 与 \(e\) 的系数均有界；对全部 \(m\ge m_0\)，
\(|a_n|\rho_n^m\) 被同一个可求和主导支付。因此计数测度上的支配收敛
给 \(\sum a_n\rho_n^m\to a_6\)，没有只比较有限个竞争项。

真实 Möbius 原子为 \(\mu(6)=1\)。对实际 Fibonacci 原子，有限卷积恰给

\[
\begin{aligned}
e_6&=\beta_6-\beta_3-\beta_2+\beta_1\\
&=\log\frac{(1-q^6)(1+q)}{(1+q^3)(1-q^2)}
=\log(1+q+q^2)>0.
\end{aligned}
\tag{PM.17}
\]

这证明（PM.14）。若存在所述正 Laplace 测度，任意固定 \(u>0\) 和
整数 \(k\ge0\) 都有
\((-1)^kf^{(k)}(u)=\int t^ke^{-ut}d\nu(t)\ge0\)；
微分由 \(t^ke^{-ut}\le C_{k,u}e^{-ut/2}\) 支付。它与（PM.14）
矛盾。证毕。

**原 Robin 来源中的精确边界。** 正极值分布与正密度是原来源在
实数 \(1+u>1\) 上的概率读出；（PM.14）直接排除了把同一密度改写为
正 Laplace 原子的做法。其复域来源仍是

\[
\mathsf F(u)=\frac{\mathcal B(1+u)}{b\,\zeta(1+u)}.
\]

由（385.4）的既有无零乘子，任意非平凡 ζ 零点 \(\rho\) 的重数为 \(h\)
时，这一来源在 \(u=\rho-1\) 的极点阶仍恰为 \(h\)，其密度的极点阶为
\(h+1\)。极值实现没有消去这些实际算术极点。

原完整 Robin 尾项仍保留（424.6）的全部商纤维，

\[
I_\psi(x)=\sum_{n\ge1}M(n)J_x^\eta(n),\qquad
I_\psi(x)=\int_x^\infty[\psi(t)-t]\frac{1+\log t}{t^2\log^2t}\,dt.
\]

这不是（PM.6）的正损失期望。（PM.4）只给同一有限 \(J_z\) 内
\(\mathcal D_z\) 的精确读出；（PM.12）–（PM.13）只给上述已支付
自然截止的对数权矩。它们没有估计原 \(I_\psi\) 的完整有符号临界余量，
也没有把 \(|H_{\rm raw}(N)|\) 的已付对数界提升到平方根尺度。

**来源。** 实轴 Euler 乘积、可数独立乘积、概率连续性、Borel–Cantelli、
非负 Tonelli、指数积分和 Gamma 矩、Abel 求和及解析恒等定理为经典
供应；Dirichlet 与 Gamma 接口参见
[NIST DLMF 25.2.1](https://dlmf.nist.gov/25.2.E1) 和
[NIST DLMF 5.9.1](https://dlmf.nist.gov/5.9.E1)。
Mertens 的定量供应复用 §424 引用的
[Ng 作者稿 p. 5](https://www.cs.uleth.ca/~nathanng/RESEARCH/mobius2b.pdf)，
实际 Fibonacci 系数、无零乘子及对数转移复用 §§384–385、414。
Euler 乘积的极值解释和倒数 ζ 的非完全单调性不作全局原创性断言；
原有限阻尼的精确对数矩及带方向余量、同一实际 Fibonacci 概率读出、
其完整 signed 对数矩比较与由 \(e_6\) 支付的正 Laplace 原子失效边界
为本仓推导（repo-derived）。

## 449. Fibonacci 概率对数导数与原 Robin 临界尾的精确运输

**原对象与记号。** 本节保持原自然数 von Mangoldt 函数和原实数截断
\(x>1\)：

\[
\Lambda(n)=
\begin{cases}
\log r,&n=r^j,\ r\text{ 为素数},\ j\ge1,\\
0,&\text{其余情形},
\end{cases}
\qquad
\psi(t)=\sum_{n\le t}\Lambda(n),
\]

\[
w(t)=\frac{1+\log t}{t^2\log^2t},\qquad
I_\psi(x)=\int_x^\infty[\psi(t)-t]w(t)\,dt.
\tag{HT.1}
\]

\(\psi\) 与 \(I_\psi\) 的全部整数和及完整无穷尾均保留；原绝对存在性
复用 §424。仍取 §§384–385 的同一实际 Fibonacci 来源

\[
q=\varphi_{\rm gold}^{-2}\in(0,2/5),\quad
\beta_d=\log(1-(-q)^d),\quad
b=\beta_1=\log(1+q),\quad
\mathcal B(s)=\sum_{d\ge1}\beta_dd^{-s},\quad e=\mu*\beta.
\]

这里 \(\gamma=(\gamma_d)_{d\ge1}=\beta^{-1}\) 专指正整数上的
Dirichlet 卷积逆，不是 Euler 常数 \(\gamma_E\)。卷积单位记为
\(\varepsilon_1=1,\varepsilon_n=0\)（\(n>1\)）。复用（384.5）的正间隙

\[
\delta=b-\sum_{d\ge2}|\beta_d|
\ge\delta_0:=\frac{94q}{2205}>0.
\tag{HT.2}
\]

保持 §448 的同一概率分布函数

\[
g(u)=\zeta(1+u)^{-1},\qquad
\mathsf F(u)=\frac{\mathcal B(1+u)}{b\,\zeta(1+u)}.
\]

定义实际乘子的算术对数导数系数、累积和及其规范读出：

\[
c=-\,(\beta\cdot\log)*\gamma,\qquad
(\beta\cdot\log)_d=\beta_d\log d,\qquad
C_\beta(t)=\sum_{n\le t}c_n,
\]

\[
\psi_{\mathsf F}(t)=\psi(t)+C_\beta(t),\qquad
I_{\mathsf F}(x)=\int_x^\infty[\psi_{\mathsf F}(t)-t]w(t)\,dt.
\tag{HT.3}
\]

\(\psi_{\mathsf F}\) 是原实际 \(\mathsf F\) 的对数导数所确定的读出；
它不重新定义（HT.1）的原 \(\psi\)。

**定理 449.1（同一概率来源的完整算术身份）。** 有

\[
\boxed{
\frac{\mathsf F'(u)}{\mathsf F(u)}
=-\frac{\zeta'}{\zeta}(1+u)
+\frac{\mathcal B'}{\mathcal B}(1+u)
=\sum_{n\ge1}\frac{\Lambda(n)+c_n}{n^{1+u}},
\qquad u>0.
}
\tag{HT.4}
\]

令

\[
T_0=\frac{q^2(2-q)}{(1-q)^3},\qquad
U_0=\frac{q^2(4-3q+q^2)}{(1-q)^4},\qquad
M_0=\frac{T_0}{\delta_0},
\]

\[
\alpha=\min\!\left\{1,\frac{\delta_0}{2U_0}\right\}>0,\qquad
M_\alpha=\frac{2U_0}{\delta_0}.
\tag{HT.5}
\]

则全部实际系数的无穷预算满足

\[
\boxed{
\sum_{n\ge1}|\gamma_n|\le\frac1\delta\le\frac1{\delta_0},\quad
\sum_{n\ge1}|\gamma_n|n^\alpha\le\frac2{\delta_0},\quad
\sum_{n\ge1}|c_n|\le M_0,\quad
\sum_{n\ge1}|c_n|n^\alpha\le M_\alpha.
}
\tag{HT.6}
\]

此外，在整个 \(\Re s\ge-\alpha\) 上，绝对收敛身份为

\[
\boxed{
\sum_{n\ge1}\gamma_nn^{-s}=\frac1{\mathcal B(s)},\qquad
\sum_{n\ge1}c_nn^{-s}=\frac{\mathcal B'(s)}{\mathcal B(s)}.
}
\tag{HT.7}
\]

**证明：有符号逆与全系数预算。** 写 \(\beta=b\varepsilon+a\)，其中
\(a_1=0\)，\(\|a\|_1=b-\delta<b\)。正整数 Dirichlet 卷积的绝对范数
满足 \(\|h*k\|_1\le\|h\|_1\|k\|_1\)，因为完整非负双和可按乘积分组。
因此实际逆有绝对收敛 Neumann 展开

\[
\gamma=b^{-1}\sum_{j\ge0}(-a/b)^{*j},
\qquad
\|\gamma\|_1\le\frac1\delta.
\tag{HT.8}
\]

每个固定整数系数只用有限多阶非单位卷积，故该逆也是既有有限递推定义
的同一个 \(\gamma\)。

指数尾 \(|\beta_d|\le q^d/(1-q)\) 与 \(\log d\le d\) 给完整预算

\[
\sum_{d\ge2}|\beta_d|\log d\le T_0,\qquad
\sum_{d\ge2}|\beta_d|d\log d\le U_0.
\tag{HT.9}
\]

右侧分别由完整几何级数的 \(\sum_{d\ge2}dq^d\) 和
\(\sum_{d\ge2}d^2q^d\) 得出，没有截去后续系数。

对 \(0<\alpha\le1\)，有
\(d^\alpha-1=\int_0^\alpha d^v\log d\,dv\le\alpha d\log d\)。
因此

\[
\sum_{d\ge2}|\beta_d|d^\alpha
\le b-\delta+\alpha U_0\le b-\delta_0/2.
\]

权 \(n^\alpha\) 满足 \((mn)^\alpha=m^\alpha n^\alpha\)，故同一
Neumann 展开在这个完整加权范数中收敛，给
\(\sum|\gamma_n|n^\alpha\le2/\delta_0\)。卷积定义（HT.3）与（HT.9）
随后给 \(c\) 的两条完整预算（HT.6）。

若 \(\Re s\ge-\alpha\)，则 \(|n^{-s}|\le n^\alpha\)；
上述全部 Dirichlet 级数及卷积双和均绝对收敛。在同一域中，
\(|\mathcal B(s)-b|\le b-\delta_0/2<b\)，所以 \(\mathcal B(s)\ne0\)。
卷积身份与逐项微分给（HT.7）。当 \(s=1+u>1\) 时，经典
von Mangoldt Dirichlet 级数给
\(-\zeta'/\zeta(s)=\sum\Lambda(n)n^{-s}\)。对原 \(\mathsf F\)
取对数导数即得（HT.4）。证毕。

**定理 449.2（完整原尾的显式补偿与单侧方向）。** 定义

\[
\kappa=\sum_{n\ge1}c_n=\frac{\mathcal B'(0)}{\mathcal B(0)},\qquad
\kappa_0=\frac{187}{1323}\frac{q^2\log2}{b}>0.
\tag{HT.10}
\]

则 \(\kappa\ge\kappa_0\)，且对每个原实数 \(x>1\) 精确有

\[
I_{\mathsf F}(x)-I_\psi(x)=
\int_x^\infty C_\beta(t)w(t)\,dt,
\qquad
|I_{\mathsf F}(x)-I_\psi(x)|\le\frac{M_0}{x\log x},
\tag{HT.11}
\]

\[
\boxed{
\left|I_{\mathsf F}(x)-I_\psi(x)
-\frac{\kappa}{x\log x}\right|
\le\frac{M_\alpha x^{-\alpha}}{x\log x}.
}
\tag{HT.12}
\]

特别地，令

\[
X_\beta=\max\!\left\{
e,\left(\frac{2M_\alpha}{\kappa_0}\right)^{1/\alpha}
\right\}<\infty.
\]

则对全部 \(x\ge X_\beta\)，有可量化单侧预算

\[
\boxed{
I_\psi(x)\le I_{\mathsf F}(x)-\frac{\kappa_0}{2x\log x},
\qquad
I_{\mathsf F}(x)-I_\psi(x)
=\frac{\kappa}{x\log x}
+O\!\left(\frac{x^{-1-\alpha}}{\log x}\right)>0.
}
\tag{HT.13}
\]

**证明：完整实际尾的运输。** （HT.7）在 \(s=0\) 的绝对收敛给
\(\sum c_n=\mathcal B'(0)/\mathcal B(0)\)。§448 的非负实轴结论给

\[
0<\mathcal B(0)<b,\qquad
\mathcal B'(0)\ge\frac{187}{1323}q^2\log2,
\]

所以 \(\kappa\ge\kappa_0>0\)。对每个 \(t\ge1\)，整个未保留补集满足

\[
|C_\beta(t)|\le M_0,\qquad
|\kappa-C_\beta(t)|
\le\sum_{n>t}|c_n|
\le M_\alpha t^{-\alpha}.
\tag{HT.14}
\]

这里最后一步直接消费完整加权无穷尾，没有把有限源估计当成全尾界。

原 \(I_\psi\) 已绝对存在，而 \(C_\beta\) 有界，故 \(I_{\mathsf F}\)
也绝对存在。原权重精确满足

\[
w(t)=-\left(\frac1{t\log t}\right)',\qquad
\int_x^\infty w(t)\,dt=\frac1{x\log x}.
\tag{HT.15}
\]

对（HT.3）中的两个完整积分作差，得到（HT.11）的身份和绝对界；
对（HT.14）的尾差在整个 \(t\ge x\) 上积分，并用
\(t^{-\alpha}\le x^{-\alpha}\)，得到（HT.12）。
当 \(x\ge X_\beta\) 时，
\(M_\alpha x^{-\alpha}\le\kappa_0/2\)，于是（HT.13）成立。证毕。

**定理 449.3（临界有符号部分保持原样）。** 在原归一化下，令

\[
Z_\psi(x)=\sqrt{x}\log x\,I_\psi(x),\qquad
Z_{\mathsf F}(x)=\sqrt{x}\log x\,I_{\mathsf F}(x).
\]

则

\[
\boxed{
Z_{\mathsf F}(x)-Z_\psi(x)
=\frac{\kappa}{\sqrt{x}}
+O(M_\alpha x^{-1/2-\alpha})\longrightarrow0.
}
\tag{HT.16}
\]

因此两个完整尾的上极限、下极限及绝对值上极限相同，允许扩展实数值。
特别地，

\[
I_\psi(x)=O\!\left(\frac1{\sqrt{x}\log x}\right)
\quad\Longleftrightarrow\quad
I_{\mathsf F}(x)=O\!\left(\frac1{\sqrt{x}\log x}\right).
\tag{HT.17}
\]

**证明。** 乘（HT.12）以 \(\sqrt{x}\log x\) 得（HT.16）；
趋零差保留上述全部上、下极限，且（HT.11）给
\(|Z_{\mathsf F}-Z_\psi|\le M_0/\sqrt{x}\)，从而得到（HT.17）。
这是在同一完整原尾上的精确运输；并未证明两边任一临界界实际成立。
证毕。

**定理 449.4（概率正对数导数仍有真实负算术事件）。** 虽然 §448 给
\(\mathsf F'/\mathsf F>0\) 在全部 \(u>0\) 上成立，但（HT.4）的原
算术系数在复合指标六处严格为负：

\[
\boxed{
c_6=\frac{\log6}{b^2}
\left(\beta_2\beta_3-b\beta_6\right)<0,\qquad
\Lambda(6)+c_6=c_6<0.
}
\tag{HT.18}
\]

因此其自然累积读出 \(\psi_{\mathsf F}\) 在 \(t=6\) 向下跳跃。

**证明：原精确系数与全部参数区间。** 有限 Dirichlet 逆递推给

\[
\gamma_1=1/b,\qquad
\gamma_2=-\beta_2/b^2,\qquad
\gamma_3=-\beta_3/b^2.
\]

在原 \(c=-(\beta\cdot\log)*\gamma\) 的 \(n=6\) 系数中保留全部四个约数：
\(d=1\) 项因 \(\log1=0\) 消失，其余三项给

\[
c_6=-\frac{\beta_6\log6}{b}
+\frac{\beta_2\beta_3(\log2+\log3)}{b^2},
\]

即（HT.18）的精确公式。这里
\(\beta_2,\beta_6<0\)、\(\beta_3,b>0\)，且经典对数积分界给

\[
|\beta_2|\beta_3\ge\frac{q^5}{1+q^3},\qquad
b|\beta_6|\le\frac{q^7}{1-q^6}.
\]

对全部 \(0<q<2/5\)，
\(q^2+q^5+q^6<3q^2<12/25<1\)，故
\(1-q^6>q^2(1+q^3)\)。于是
\(|\beta_2|\beta_3>b|\beta_6|\)，证明 \(c_6<0\)。
六不是素数幂，所以 \(\Lambda(6)=0\)。证毕。

**概率递归与实际逆的准确关系。** 非负变量的分布函数在点态乘法下闭合，
对应独立变量取最大值；该运算可结合、交换，单位为零点质量一的分布。
但本节的非平凡 Fibonacci 因子满足
\(0<\mathcal B(1+u)/b<1\)，其点态倒数 \(b/\mathcal B(1+u)>1\)
不是概率分布函数。概率乘法并不带这个逆。

同一实际 \(\beta\) 在绝对 Dirichlet 卷积代数中则有（HT.8）的
\(\gamma\) 逆。这个逆保留符号：例如
\(\gamma_3=-\beta_3/b^2<0\)。因而可逆的算术运输与概率最大值递归有
明确不同的载体；（HT.11）–（HT.17）支付前者的完整成本，
概率读出的单调性没有消除这个有符号逆。

**推论 449.5（递归次数在原临界尺度上的准确成本）。** 对整数 \(m\ge0\)，
取同一极值递归的分布函数

\[
\mathsf F_m(u)=g(u)\left[\frac{\mathcal B(1+u)}b\right]^m.
\]

其对数导数的规范算术读出为
\(\psi_m(t)=\psi(t)+mC_\beta(t)\)。记相应完整尾为 \(I_m(x)\)。
则对每个 \(x>1\) 和整数 \(m\ge0\)，精确有

\[
I_m(x)-I_\psi(x)=m[I_{\mathsf F}(x)-I_\psi(x)],
\]

\[
\boxed{
\sqrt{x}\log x\,[I_m(x)-I_\psi(x)]
=\frac{m}{\sqrt{x}}
\left[\kappa+\epsilon_\beta(x)\right],
\qquad
|\epsilon_\beta(x)|\le M_\alpha x^{-\alpha}.
}
\tag{HT.19}
\]

若 \(m=m(x)\) 变化，每个 \(x\) 先固定该整数，在整个积分尾 \(t\ge x\)
上使用同一个 \(m(x)\)。于是 \(m=o(\sqrt{x})\) 时临界差趋零；
若 \(m/\sqrt{x}\to a<\infty\)，临界差趋于 \(a\kappa\)；
若 \(m/\sqrt{x}\to\infty\)，临界差趋于 \(+\infty\)。

**证明。** 取同一 CDF 乘积的对数导数，新增项精确为
\(m\mathcal B'/\mathcal B\)，所以自然整数系数新增 \(mc_n\)。
全部尾积分由固定 \(m\) 的（HT.6）支付。完整线性身份与（HT.12）
给（HT.19），三种极限随即成立。证毕。

增长到平方根次数的概率递归可以产生临界量级的新增读出，但原
\(I_\psi\) 必须扣回（HT.19）的同一完整补偿。因此该新增量不成为
原 Robin 余量的免费储备。

**剩余边界与来源。** 原目标仍是（HT.1）及（424.6）的全量配对

\[
I_\psi(x)=\sum_{n\ge1}M(n)J_x^\eta(n),
\]

包括原首块与所有整数纤维。（HT.13）给实际、显式、单侧且低于临界
尺度的补偿；（HT.16）证明未控的临界有符号部分在这个规范概率读出中
保持相同。由（HT.7），新增 \(\mathcal B'/\mathcal B\) 在
\(\Re s>-\alpha\) 解析，所以原 \(-\zeta'/\zeta\) 的非平凡零点极点
及其留数仍保留。此处不排除其他概率方法，但本节的单调读出和迭代本身
没有估计共同的原临界部分，也没有得到全局 Robin 符号或 RH。

完整 von Mangoldt Dirichlet 级数、绝对卷积与带权 Neumann 求逆、
几何级数、对数积分界及完整积分权重为经典供应。带权逆的来源沿用
§388 所引 Glöckner–Lucht，
[Weighted inversion of general Dirichlet series](https://arxiv.org/abs/1112.0749)；
本节的 \(\alpha\) 和全部预算仅用（384.5）的解析间隙及完整指数尾，
不依赖 §388 的定向数值前提。原实际 \(\beta,e,\gamma\) 的归属沿用
§§384–385；概率正性沿用 §448。把同一实际 Fibonacci 概率对数导数
接回原 \(I_\psi\)，得到完整带方向补偿、临界等价、真实 \(c_6<0\)
与变化递归次数的精确临界成本，为本仓推导（repo-derived）。

## 450. 原始轮廓的曲率概率、完整超额期望与对数矩

**对象与既有供应。** 保持 §§441–448 的同一原始轮廓和原完整两段常数：

\[
\operatorname{Ein}(v)=\int_0^v\frac{1-e^{-w}}w\,dw,
\qquad \Phi(v)=\exp(\operatorname{Ein}(v)),
\qquad C=e^{\gamma_E},\qquad k=C-1>0,
\]

\[
A=\int_0^1\frac{\Phi'(v)-1}{v}\,dv
 +\int_1^\infty\frac{\Phi'(v)-C}{v}\,dv.
\tag{CVP.1}
\]

零端使用原有限区间表示
\(r(v)=\int_0^1e^{-sv}\,ds\)、\(\Phi'=\Phi r\)、\(\Phi(0)=1\)。
§444 已证明 \(\Phi''(0)=1/2\)、\(0<\Phi''(v)<1/2\) 于全部
\(v>0\)，且 \(\Phi''\) 在非负轴严格递减；原 \(A<1/2\) 也已支付。
Euler 常数的经典界 \(\gamma_E>1/2\) 保证 \(k>0\)，可直接复用
Mathlib 的 `Real.one_half_lt_eulerMascheroniConstant`。

本节新增的是同一 \(\Phi\) 的曲率概率解释、原 \(A\) 的负对数矩、
严格 Jensen 下界与二阶完全单调障碍。§433（SL.21）、§434 已有的
经典 Dickman Laplace 身份在本节末尾复用，不另列为新变换。

**引理 450.1（全部端点预算）。** 写 \(B(v)=\Phi''(v)\)，令
\(M=\exp(e^{-1})\)。原指数积分身份在每个 \(v>0\) 给

\[
E_1(v)=\int_v^\infty\frac{e^{-w}}w\,dw,
\quad 0<E_1(v)\le e^{-v}/v,
\quad \Phi(v)=Cv\exp(E_1(v)),
\]

\[
\Phi'(v)=C\exp(E_1(v))(1-e^{-v}),
\quad
B(v)=C\exp(E_1(v))e^{-v}\left(1-\frac{1-e^{-v}}v\right).
\tag{CVP.2}
\]

对 \(v\ge1\)，整段尾有显式界

\[
\begin{aligned}
0<B(v)&\le CM e^{-v},\\
|\Phi'(v)-C|&\le CM e^{-v}(1+1/v)\le2CM e^{-v},\\
0<\Phi(v)-Cv&\le CM e^{-v},\\
v\Phi'(v)-\Phi(v)&=-Cv\exp(E_1(v))e^{-v}.
\end{aligned}
\tag{CVP.3}
\]

在近端，\(0\le\Phi'(v)-1\le v/2\) 对 \(0\le v\le1\) 成立。
因此 \(B\)、\(vB\)、\(|\log v|B\) 在整个正轴可积，且以下边界
全部成立：

\[
\begin{gathered}
\Phi'(0)=1,\quad\Phi(0)=1,\quad
\Phi'(v)\longrightarrow C,\quad\Phi(v)-Cv\longrightarrow0,\\
v(\Phi'(v)-C)\longrightarrow0,\quad
\log v\,(\Phi'(v)-C)\longrightarrow0,\quad
v\Phi'(v)-\Phi(v)\longrightarrow0\qquad(v\to\infty),\\
\log v\,(\Phi'(v)-1)\longrightarrow0\qquad(v\downarrow0).
\end{gathered}
\tag{CVP.4}
\]

**证明。** （CVP.2）的末式是 §444（NS.3）代入同一 Euler 归一化；
其中 \(0<(1-e^{-v})/v<1\)。当 \(v\ge1\)，有
\(0<E_1(v)\le e^{-1}\)，从而 \(\exp(E_1(v))\le M\)。再用
\(e^y-1\le e^y y\)（\(y\ge0\)），得到（CVP.3）的前三行；第四行
由（CVP.2）准确相减得到，未分别取两个发散项的极限。

近端由 \(\Phi'(v)-1=\int_0^vB(w)\,dw\) 和 \(B\le1/2\) 得界。
\(\int_0^1|\log v|\,dv=1\) 支付近端对数可积性；远端以
\(\log v\le v\) 和 \(CM e^{-v}\) 支付。\(vB\) 的近端有界、
远端由 \(CMve^{-v}\) 支付。（CVP.3）与
\(v|\log v|\to0\)、\(ve^{-v}\to0\)、\(e^{-v}\log v\to0\) 给
（CVP.4）。原（CVP.1）的近段有界，远段被 \(2CM e^{-v}/v\) 主导，
所以两段均绝对收敛。证毕。

**定理 450.2（真实曲率概率与原轮廓的超额期望）。** 存在正随机变量
\(V\)，其严格正的密度、分布函数与生存函数为

\[
f_V(v)=\frac{B(v)}k\quad(v>0),\qquad
\mathbb P(V\le v)=\frac{\Phi'(v)-1}k,\qquad
\mathbb P(V>v)=\frac{C-\Phi'(v)}k\quad(v\ge0).
\tag{CVP.5}
\]

它满足完整质量和一阶矩身份

\[
\int_0^\infty B(v)\,dv=k,\qquad
\int_0^\infty vB(v)\,dv=1,\qquad
\mathbb EV=\frac1k.
\tag{CVP.6}
\]

而同一原 \(\Phi\) 对每个 \(v\ge0\) 精确满足

\[
\boxed{
\begin{aligned}
\Phi(v)&=1+v+k\,\mathbb E[(v-V)_+]\\
       &=Cv+k\,\mathbb E[(V-v)_+]\\
       &=v+k\,\mathbb E[\max(v,V)].
\end{aligned}}
\tag{CVP.7}
\]

所有期望使用同一 \(V\)，其无穷尾均保留。

**证明：质量与一阶矩。** 引理450.1已给可积性。在有限区间上使用
FTC，然后以（CVP.4）取极限：

\[
\int_0^R B(v)\,dv=\Phi'(R)-1\longrightarrow C-1=k,
\]

\[
\int_0^R vB(v)\,dv
=R\Phi'(R)-\Phi(R)+1\longrightarrow1.
\]

因此 \(B/k\) 确实定义 \((0,\infty)\) 上的概率密度。（CVP.5）由
其从零积分得到；\(B>0\) 保证任意正长度的正轴区间有严格正质量，
所以这不是点质量，且没有零点原子。

**证明：完整超额表示。** 对固定 \(v\ge0\)，\((w-v)_+B(w)\)
由 \(wB(w)\) 主导，故完整尾绝对收敛。有限区间分部积分给

\[
\int_v^R(w-v)B(w)\,dw
=(R-v)\Phi'(R)-\Phi(R)+\Phi(v).
\]

准确地写成

\[
v\Phi'(R)-Cv\longrightarrow0,\qquad
R\Phi'(R)-\Phi(R)\longrightarrow0,
\]

便得到
\(\int_v^\infty(w-v)B(w)\,dw=\Phi(v)-Cv\)。这给（CVP.7）第二行。
有限区间的两次 FTC 则给
\(\Phi(v)=1+v+\int_0^v(v-w)B(w)\,dw\)，即第一行。
最后用 \(\max(v,V)=v+(V-v)_+\) 和 \(C=1+k\) 得第三行。证毕。

**定理 450.3（原 \(A\) 的完整负对数矩与严格下界）。** 同一随机变量
满足 \(\mathbb E|\log V|<\infty\)，且

\[
\boxed{\quad A=-\int_0^\infty\log v\,B(v)\,dv
                =-k\,\mathbb E\log V.\quad}
\tag{CVP.8}
\]

因此原常数有严格两侧界

\[
\boxed{\qquad k\log k<A<\frac12.\qquad}
\tag{CVP.9}
\]

**证明：完整分部及边界。** 引理450.1已先支付绝对可积性。
对 \(0<\varepsilon<1<R\)，仅在有限区间分部积分，得

\[
\begin{aligned}
\int_\varepsilon^1\frac{\Phi'(v)-1}{v}\,dv
&=-\log\varepsilon\,[\Phi'(\varepsilon)-1]
  -\int_\varepsilon^1\log v\,B(v)\,dv,\\
\int_1^R\frac{\Phi'(v)-C}{v}\,dv
&=\log R\,[\Phi'(R)-C]
  -\int_1^R\log v\,B(v)\,dv.
\end{aligned}
\]

两个截断边界由（CVP.4）趋于零，完整积分由绝对可积性收敛，故得到
（CVP.8），没有无偿的形式分部。

写 \(m=\mathbb EV=1/k\)。严格对数切线不等式给

\[
\log v\le\log m+\frac{v-m}m,
\qquad\text{等号当且仅当 }v=m.
\]

各项期望均有限；由于 \(V\) 有全正轴严格正的密度，切线差在任意
避开 \(m\) 的正长度紧区间上有严格正积分。因此
\(\mathbb E\log V<\log\mathbb EV=-\log k\)，乘以 \(-k<0\) 得
\(A>k\log k\)。上界直接复用 §444 的原 \(A<1/2\)。证毕。

**推论 450.4（同一对象的 Mellin 域与非完全单调性）。** 曲率概率的矩函数

\[
\mathcal M_V(r)=\mathbb E V^r
=\frac1k\int_0^\infty v^rB(v)\,dv
\quad(\Re r>-1)
\]

在此半平面全纯，且

\[
\mathcal M_V(0)=1,\quad\mathcal M_V(1)=1/k,\quad
\mathcal M_V'(0)=-A/k.
\tag{CVP.10}
\]

尽管 \(f_V\) 严格为正、严格递减，它不是正半轴上的完全单调函数，
也不存在对全部 \(v>0\) 成立的正 Laplace 测度表示
\(f_V(v)=\int_{[0,\infty)}e^{-vt}\,d\nu(t)\)。

**证明：矩函数的整个积分。** 对半平面中的任意紧域，取
\(-1<a\le\Re r\le b\)。在 \(0<v\le1\) 上，第 \(j\) 阶参数导数由
\(v^a|\log v|^j/(2k)\) 支配；在 \(v\ge1\) 上由
\(CMv^b(\log v)^je^{-v}/k\) 支配，两者都可积。这支付任意固定阶
求导与全纯性。（CVP.6）、（CVP.8）给（CVP.10）。

**证明：二阶符号障碍。** 指数幂级数在任意有界的 \(v\) 区间与
\(0\le s\le1\) 上一致绝对收敛，有限积分因此给
\(r(v)=\sum_{n\ge0}(-1)^nv^n/(n+1)!\)。再在有限区间积分得
\(\operatorname{Ein}(v)=\sum_{n\ge1}(-1)^{n-1}v^n/(n\,n!)\)。
这些幂级数保证 \(\Phi\) 在零点解析，准确展开为

\[
\begin{aligned}
\operatorname{Ein}(v)&=v-\frac{v^2}4+\frac{v^3}{18}-\frac{v^4}{96}
 +O(v^5),\\
\Phi(v)&=1+v+\frac{v^2}4-\frac{v^3}{36}-\frac{v^4}{144}+O(v^5).
\end{aligned}
\tag{CVP.11}
\]

第四项系数可逐项独立核对：

\[
-\frac1{96}+\frac1{18}+\frac1{32}-\frac18+\frac1{24}
=-\frac1{144}.
\]

因而 \(\Phi'''(0)=\Phi''''(0)=-1/6\)。以 \(B/k\) 光滑延拓密度至零点后，特别

\[
f_V''(0)=\frac{\Phi''''(0)}k=-\frac1{6k}<0.
\tag{CVP.12}
\]

由解析连续性，存在 \(\eta>0\)，使每个 \(0<v<\eta\) 都满足
\(f_V''(v)<0\)。完全单调性要求正轴上每阶交替导数非负，二阶条件
已在这个真正的正区间失败；零点本身不被拿来代替正轴违反点。

若存在上述正 Laplace 表示，对任何固定 \(v>0\)，在 \(3v/4\le s\le5v/4\) 的邻域上，
\(t^2e^{-st}\le K_v e^{-(v/2)t}\)，右侧对 \(\nu\) 可积，因为该
表示在 \(v/2>0\) 有有限值。这支付局部两次微分，故
\(f_V''(v)=\int t^2e^{-vt}\,d\nu(t)\ge0\)，与（CVP.12）后的正区间
矛盾。证毕。

**定理 450.5（复用 Dickman 变换后的同对象方差关系）。** 取 §433、§434
已有的经典 Dickman 函数 \(\rho_D\)，满足
\(\widehat\rho_D(v)=C/\Phi(v)\)。归一密度
\(\rho_D(y)/C\) 定义随机变量 \(Y\)，故其 Laplace 变换为

\[
\ell(v)=\mathbb E e^{-vY}=\frac1{\Phi(v)}\qquad(v>0).
\tag{CVP.13}
\]

对任意 \(v>0\)，用 \(e^{-vY}/\ell(v)\) 倾斜这同一概率律，记
倾斜期望和方差为 \(\mathbb E_v\)、\(\operatorname{Var}_v\)。则

\[
\boxed{\quad
\Phi''(v)=\Phi(v)
\left[(\mathbb E_vY)^2-\operatorname{Var}_v(Y)\right]>0,
\qquad
\operatorname{Var}_v(Y)<(\mathbb E_vY)^2.
\quad}
\tag{CVP.14}
\]

**证明。** 经典身份在 \(v\downarrow0\) 的单调收敛给
\(\int_0^\infty\rho_D(y)\,dy=C\)，所以归一密度确实有质量一。
对任意固定正 \(v\) 的紧邻域，\(y^je^{-vy}\) 由固定常数乘
\(e^{-(v/2)y}\) 支配，右侧对 Dickman 律可积。这支付前两阶
Laplace 求导及倾斜矩的完整无穷尾。
写 \(a=-\ell'/\ell=\mathbb E_vY\)、
\(b=\ell''/\ell=\mathbb E_vY^2\)，准确求倒数的二阶导数得

\[
\Phi''=2(\ell')^2/\ell^3-\ell''/\ell^2
=\Phi(2a^2-b)=\Phi(a^2-\operatorname{Var}_v(Y)).
\]

原 \(\Phi''>0\) 和 \(\Phi>0\) 给（CVP.14）。证毕。

**关系与成果边界。** 原 \(\Phi\) 同时具有两个合法概率读出：
它是经典 Dickman Laplace 变换的倒数，也是曲率律 \(V\) 的完整超额
期望。（CVP.8）把先前需要分开正近段和负尾段的原 \(A\) 合成为这个
同一曲率律的负对数矩。§448 的素数极值律 \(U\)、Fibonacci 律
\(W\) 与这里的 \(V\) 都有共同的矩半平面 \(\Re r>-1\)，且三者的
严格正密度均不能作为正 Laplace 原子；这指出了概率正性和有符号
谱表示之间的共同限制。这里未断言它们具有同一分布、同一随机实现
或保号变换。

本节为完整纸面证明；不声称新增 Lean 核验。新组合与显式二阶障碍
为本仓推导（`repo-derived`），未作全局原创性断言。原曲率性质、
Euler 归一化、\(A<1/2\) 和 Dickman 身份均复用既有来源；FTC、
绝对可积分部、严格 Jensen 与支配求导为经典供应。它没有支付完整
Robin 配对中其余阶乘密度、实际粗糙前缀、整数纤维及有符号互补尾，
也没有由此证明 Robin 不等式或 RH。

## 451. 同一原始完整肩项的半 Gamma 负储备

This section strictly strengthens §447 for the same literal objects. Set
\[
 C=e^\gamma,\qquad k=C-1,\qquad
 \delta=\frac{2\log2-1}{6}>0,
\]
and retain the original complete two-piece constant \(A<1/2\),
\[
 Q(u)=u\Re\zeta(1+u),\qquad
 K(t)=A-k(\log t+\gamma)
 +C\int_{u>0}e^{-tu}\frac{1/Q(u)-1}{u}\,du\quad(t>0).
\]
No new shoulder, finite truncation, or assumed infinite bound is introduced.
The suppliers for complete integrability and the literal comparison are
exactly those in §447.

### The existing complete average and its positive tail mass

For \(x>0\), let
\[
 E_1(x)=\int_{y>x}\frac{e^{-y}}y\,dy,\qquad
 G(x)=k(\log(x/2)+\gamma)+Ce^x E_1(x).
\]
The actual \(Q(u)\ge1+u/2\) gives
\((1/Q(u)-1)/u\le-1/(u+2)\); the complete affine substitution
\(y=t(u+2)\) therefore gives \(K(t)\le A-G(2t)\).
The full logarithmic FTC identity and \(C=1+k\) give the unit-mass average
\[
 G(x)=e^x\int_{y>x}e^{-y}
 \left[k(\log(y/2)+\gamma)+\frac1y\right]dy.
\]
All integrals above are over their full specified domains and are absolutely
integrable. Let
\[
 \Lambda(k)=k\left[1+\log\frac{1+k}{2k}\right],\qquad
 m(k)=ke^{-2/k}(\log2-1/2)=3k\delta e^{-2/k}.
\]
The scalar gap equals \(k[\log(ky)+1/(ky)-1]\ge0\).
For \(y>x+2/k\), its value is at least \(k(\log2-1/2)\),
and that part of the normalized complete average has mass \(e^{-2/k}\).
Consequently, for every \(x>0\),
\[
 G(x)\ge\Lambda(k)+m(k),\qquad
 K(t)\le R:=A-\Lambda(k)-m(k).
\]
The number \(R\) is independent of \(t\).

### The half-gamma simplification

The already available strict classical bound \(\gamma>1/2\) and the
exponential tangent inequality \(e^\gamma\ge1+\gamma\) yield
\[
 k=e^\gamma-1\ge\gamma>1/2.
\]
Put \(z=(1+k)/(2k)>0\). The logarithmic tangent is used in its lower-bound
direction, \(\log z\ge1-1/z\), so
\[
 \Lambda(k)\ge k\left(2-\frac{2k}{1+k}\right)
 =\frac{2k}{1+k}>\frac23.
\]
This estimate requires neither the location of a minimum of \(G\) nor
monotonicity or differentiation of \(\Lambda\).
Because \(k>1/2\), one also has \(2/k<4\), hence
\[
 m(k)=3k\delta e^{-2/k}
 >\frac32\delta e^{-4}.
\]
The positivity of \(\delta\) follows from the strict logarithmic tangent
at \(1/2\), giving \(\log2>1/2\).

### A strict supremum paid by a common barrier

Combining the strict bound on the original \(A\) with the two strict
constant reserves gives
\[
 R=A-\Lambda(k)-m(k)
 <-\frac16-\frac32\delta e^{-4}.
\]
The set \(\{K(t):t>0\}\) is nonempty (take \(t=1\)) and every member is
bounded above by the same \(R\). Thus the conditional complete supremum
satisfies
\[
 \boxed{\sup_{t>0}K(t)\le R
 <-\frac16-\frac32\delta e^{-4}.}
\]
This is a genuine strict supremum estimate; pointwise strictness alone is
not substituted for a uniform barrier.

It strictly improves §447. The strict upper tangent \(\log2<1\) gives
\(0<\delta<1/6\), and
\((3/2)\delta e^{-4}>\delta e^{-6}\). Therefore
\[
 -\frac16-\frac32\delta e^{-4}
 <-\delta(1+e^{-6}),
\]
recovering its advertised bound with strictly more reserve.

This is a bound for the same original complete shoulder. The full Robin
pairing and the remaining signed tail still require their own proofs; this
section does not claim RH or an unproved bound for that tail.

Provenance: §447 complete exponential-average construction; original
\(A<1/2\) from PrimePrefixOriginalA; classical Euler-constant and exponential
bounds from Mathlib; lower logarithmic tangent from Mathlib. The
half-gamma substitution and stronger displayed reserve are the repo-derived
simplification of that existing construction.

This is a complete paper proof. It reports no new Lean acceptance.

## 452. Fibonacci 极值递归在临界增长空间中的精确范数与指数逆成本

**原对象与既有供应。** 保持 §§384–385、414、448–449 的同一实际来源
\[
q=\varphi_{\rm gold}^{-2}\in(0,2/5),\quad
\beta_d=\log(1-(-q)^d),\quad b=\beta_1=\log(1+q),\quad
\mathcal B(s)=\sum_{d\ge1}\beta_dd^{-s},\quad \gamma=\beta^{-1},
\]
\[
\delta_\beta=b-\sum_{d\ge2}|\beta_d|>0,\qquad
\sum_{d\ge1}|\gamma_d|\le1/\delta_\beta.
\tag{IC.1}
\]
这里 \(\gamma\) 是 Dirichlet 卷积逆，不是 Euler 常数；
\(\delta_\beta\) 不与 §451 的肩项常数混用。卷积单位为
\(\varepsilon_1=1,\varepsilon_n=0\)（\(n>1\)）。§448 给全部实数 \(s\ge0\) 上
\[
0<\mathcal B(s)<b,\quad
\mathcal B'(s)\ge c_*q^2(\log2)2^{-s},\quad
c_*=\frac{187}{1323},\quad
\mathcal B(s)\longrightarrow b\quad(s\to\infty).
\tag{IC.2}
\]
以下不假定原 Mertens 函数的临界界，也不假定 RH。

**同一最大值递归的算术读出。** 令
\[
a=\beta/b,\quad \eta=b\gamma,\quad
a_m=a^{*m},\quad \eta_m=\eta^{*m}\quad(m\in\mathbb Z_{\ge0}),
\qquad a_0=\eta_0=\varepsilon.
\tag{IC.3}
\]
则 \(a_m*\eta_m=\varepsilon\)。§448 的非负变量 \(V\) 有分布函数
\(h(u)=\mathcal B(1+u)/b\)（\(u\ge0\)）；与原素数极值 \(U\) 独立的
\(m\) 份 \(V\) 给
\[
\mathsf F_m(u)=\mathbb P(\max(U,V_1,\ldots,V_m)\le u)
=\frac{\mathcal B(1+u)^m}{b^m\zeta(1+u)}\quad(u>0).
\tag{IC.4}
\]
这确实是点态 CDF 乘法的交换幺半群递归。其同一算术系数是
\(e^{(m)}=\mu*a_m\)。对整数 \(N\ge1\)，置
\[
M(N)=\sum_{n\le N}\mu(n),\qquad H_m(N)=\sum_{n\le N}e^{(m)}_n,
\qquad M(0)=H_m(0)=0.
\]
因此 \(H_0=M\)，\(H_1=H_{\rm raw}/b\)。在 \(\Re s>1\) 上的全部
Dirichlet 级数身份绝对收敛，因为 \(a_m\in\ell^1\)、\(|\mu(n)|\le1\)；
（IC.4）的系数绑定不依赖条件级数重排。

**临界增长空间。** 固定一个整数 \(j\ge0\)，标量域取 \(\mathbb R\) 或 \(\mathbb C\)。
序列与算术核使用同一标量域。令 \(\mathcal X_j\) 为满足
\(f(0)=0\) 且下列范数有限的序列空间：
\[
W_j(N)=\sqrt N(1+\log N)^j,\qquad
\|f\|_{\mathcal X_j}=\sup_{N\ge1}\frac{|f(N)|}{W_j(N)}.
\tag{IC.5}
\]
对算术核 \(v=(v_d)_{d\ge1}\)，定义
\[
(T_vf)(N)=\sum_{1\le d\le N}v_df(\lfloor N/d\rfloor),\quad N\ge1,
\qquad (T_vf)(0)=0,\qquad
\|v\|_{1,1/2}=\sum_{d\ge1}|v_d|d^{-1/2}.
\tag{IC.6}
\]
所有正商至少为一。有限约数分组给
\(H_m=T_{a_m}M\)、\(M=T_{\eta_m}H_m\)，不要求实际 \(M,H_m\)
已经属于 \(\mathcal X_j\)。

**引理 452.1（全部整数纤维的精确算子成本）。** 若 \(\|v\|_{1,1/2}<\infty\)，则
\[
\boxed{\ \|T_v\|_{\mathcal X_j\to\mathcal X_j}
=\sum_{d\ge1}|v_d|d^{-1/2}.\ }
\tag{IC.7}
\]
**证明。** 对 \(d\le N\)，令 \(n=\lfloor N/d\rfloor\)。由
\(1\le n\le N/d\)、\(j\ge0\)，有 \(W_j(n)/W_j(N)\le d^{-1/2}\)。
完整正尾预算因而给
\(\|T_vf\|_{\mathcal X_j}\le\|v\|_{1,1/2}\|f\|_{\mathcal X_j}\)。

反向固定整数 \(D\ge1\)，取整数 \(N>D(D+1)\)。因为
\(N/d-N/(d+1)=N/[d(d+1)]>1\) 对 \(1\le d\le D\) 成立，
前 \(D\) 个正商 \(n_d=\lfloor N/d\rfloor\) 严格互异，而全部 \(d>D\)
的商都严格低于 \(n_D\)。定义 \(f_N\) 仅在这些 \(D\) 个商上非零：
当 \(v_d\ne0\) 时取
\(f_N(n_d)=\overline{v_d}W_j(n_d)/|v_d|\)，当 \(v_d=0\) 时取零；
其余处及零点取零。实核只需取 \(\operatorname{sign}(v_d)W_j(n_d)\)。
则 \(\|f_N\|_{\mathcal X_j}\le1\)，且无后续商混入，
\[
\|T_v\|_{\mathcal X_j\to\mathcal X_j}
\ge\frac{|(T_vf_N)(N)|}{W_j(N)}
=\sum_{d\le D}|v_d|\frac{W_j(\lfloor N/d\rfloor)}{W_j(N)}.
\]
先令 \(N\to\infty\)，每个固定 \(d\) 的比值趋于 \(d^{-1/2}\)；
再令 \(D\to\infty\)，完整非负级数收敛，得到反向界。这里是对
operator norm 的有限支撑测试，测试输入随 \(N,D\) 变化，
不是指定的实际 \(M\)。证毕。

**定理 452.2（同一递归的统一临界逆成本）。** 对每个固定整数 \(j\ge0\)、
每个整数 \(m\ge0\)，\(T_{a_m}\) 和 \(T_{\eta_m}\) 是互逆有界算子，且
\[
\boxed{
\left(\frac b{\mathcal B(1/2)}\right)^m
\le\|T_{\eta_m}\|_{\mathcal X_j\to\mathcal X_j}
=\|\eta_m\|_{1,1/2}
\le\left(\frac b{\delta_\beta}\right)^m.
}
\tag{IC.8}
\]
其中
\[
\lambda:=\log\frac b{\mathcal B(1/2)}
\ge\lambda_0:=\frac{187q^2}{1323b\sqrt2}>0.
\tag{IC.9}
\]
这是整个增长空间上的最坏成本；不声称未知的实际 \(M\) 或 \(H_m\)
必然取得该下界。

**证明：有界性与真实逆。** 完整正双和按乘积分组，且
\((dk)^{-1/2}=d^{-1/2}k^{-1/2}\)，故
\(\|v*w\|_{1,1/2}\le\|v\|_{1,1/2}\|w\|_{1,1/2}\)。于是
\[
\|\eta_m\|_{1,1/2}
\le\|b\gamma\|_{1,1/2}^{\,m}\le(b/\delta_\beta)^m<\infty.
\]
\(a_m\) 也有完整有限范数。每个 \(N\) 上的双和是有限和，
\(\lfloor\lfloor N/d\rfloor/k\rfloor=\lfloor N/(dk)\rfloor\)，所以
\(T_vT_w=T_{v*w}\)。结合 \(a_m*\eta_m=\varepsilon\) 和（IC.7）
即得真实互逆、范数等式及完整上界。

**证明：正临界测试与完整尾 DCT。** 取同一个正序列
\(f_j(0)=0\)、\(f_j(N)=W_j(N)\)（\(N\ge1\)），其范数恰为一。
固定 \(m\)。令
\[
R_{N,d}=
\begin{cases}
W_j(\lfloor N/d\rfloor)/W_j(N),&d\le N,\\
0,&d>N.
\end{cases}
\]
对每个固定 \(d\)，\(R_{N,d}\to d^{-1/2}\)，并且对全部 \(N,d\) 有
\(0\le R_{N,d}\le d^{-1/2}\)。在整个计数测度上，
\[
|\eta_{m,d}R_{N,d}|\le|\eta_{m,d}|d^{-1/2},\qquad
\sum_{d\ge1}|\eta_{m,d}|d^{-1/2}<\infty.
\]
因此完整支配收敛与绝对收敛的 Dirichlet 卷积乘法给
\[
\frac{(T_{\eta_m}f_j)(N)}{W_j(N)}
\longrightarrow\sum_{d\ge1}\eta_{m,d}d^{-1/2}
=\left(\frac b{\mathcal B(1/2)}\right)^m.
\tag{IC.10}
\]
最后的身份复用同一 \(\gamma\) 的完整逆级数。全部 \(d>N\) 的补集
保留在共同可求和主导中，未把有限头当完整尾。范数至少为这个正极限，
给（IC.8）左界。本证明对每个 \(m\) 分别成立；应用于 \(m=m(x)\)
时使用已证明的全称界，不偷换成 \(m,N\) 的未经支付联合 DCT。

**证明：\(\lambda\) 的完整积分下界。** 对有限 \(R>1/2\)，（IC.2）给
\[
\mathcal B(R)-\mathcal B(1/2)
\ge c_*q^2(\log2)\int_{1/2}^{R}2^{-s}ds
=c_*q^2(2^{-1/2}-2^{-R}).
\]
令 \(R\to\infty\)，由 \(\mathcal B(R)\to b\) 得
\(b-\mathcal B(1/2)\ge c_*q^2/\sqrt2\)。令
\(z=(b-\mathcal B(1/2))/b\in(0,1)\)，由 \(-\log(1-z)\ge z\)
得到（IC.9）。积分端点准确为 **\(1/2\) 到 \(\infty\)**，
没有把 \(\mathcal B(1)\) 当作 \(b\)。证毕。

**命题 452.3（同一逆的具体非保号事件）。** 对每个 \(m\ge1\)，素指标三处
\[
\eta_{m,3}=m\eta_3=-m\beta_3/b<0.
\tag{IC.11}
\]
**证明。** 因为 \(\gamma_1=1/b\)、\(\gamma_3=-\beta_3/b^2\)，素数三的 \(m\) 重
卷积中恰有一个因子取三，其余全取一。取非负输入
\(f(N)=\mathbf1_{N=3}\)、\(f(0)=0\)。它属于每个 \(\mathcal X_j\)，
而 \(1\le d\le9\) 时 \(\lfloor9/d\rfloor=3\) 仅在 \(d=3\) 成立，故
\[
(T_{\eta_m}f)(9)=\eta_{m,3}<0.
\tag{IC.12}
\]
所以反向算术运输不保持非负序列锥。独立最大值的正 CDF 并不使
同一个 Dirichlet 逆成为保号概率操作。证毕。

**推论 452.4（原 RH 临界归一化下的准确成本冲突）。** §449 保持
\[
I_\psi(x)=\int_x^\infty[\psi(t)-t]
\frac{1+\log t}{t^2\log^2t}\,dt,\qquad
Z_\psi(x)=\sqrt x\log x\,I_\psi(x).
\]
同一 \(\mathsf F_m\) 的对数导数读出给 \(I_m,Z_m\)，并已证明
\[
Z_m(x)-Z_\psi(x)=\frac m{\sqrt x}
[\kappa+\epsilon_\beta(x)],\qquad
\kappa>0,\quad|\epsilon_\beta(x)|\le M_\alpha x^{-\alpha}.
\tag{IC.13}
\]
当 \(m=m(x)\) 时，每个 \(x\) 先固定该整数，在全部 \(t\ge x\) 的
原完整尾上使用同一个 \(m(x)\)。若固定 \(K>0,r\ge0\) 使充分大 \(x\) 上
\[
\|T_{\eta_{m(x)}}\|_{\mathcal X_j\to\mathcal X_j}\le Kx^r,
\tag{IC.14}
\]
**证明。** （IC.8）和正 \(\lambda\) 强迫
\[
m(x)\le\frac{\log K+r\log x}{\lambda}=O(\log x),\qquad
Z_{m(x)}(x)-Z_\psi(x)\longrightarrow0.
\tag{IC.15}
\]
这是**假定统一 operator cost 至多多项式时的必要条件**。反过来，
若 \(m(x)/\sqrt x\to a_*\) 且 **\(a_*>0\)**，那么新增临界补偿趋于
\(a_*\kappa>0\)，同时
\[
\|T_{\eta_{m(x)}}\|_{\mathcal X_j\to\mathcal X_j}
\ge\exp(\lambda m(x))
=\exp[(a_*\lambda+o(1))\sqrt x],
\tag{IC.16}
\]
超过任意固定幂 \(x^r\)。两者是同一 max 因子、同一迭代次数在
对数导数读出和完整逆运输中的不同真实成本。原 \(I_\psi\) 仍须扣回
（IC.13）的同一完整补偿；本节没有给该尾新增免费储备。证毕。

**范围与来源。** \(\mathcal B(1/2)/b\) 是算术乘子在实数 \(s=1/2\) 的值，
不能当作 \(u=-1/2\) 的概率 CDF；§448 的概率律在负轴补零。本节也没有
将正实概率密度改写成正 Laplace 测度。算子最坏成本下界不证明实际
\(M,H_m,I_\psi\) 发散，不否定可能利用实际符号抵消的其他估计，
不推出 RH 或其否定。

绝对 Dirichlet 卷积 Banach 代数与 Neumann 逆预算参照
Glöckner–Lucht，*Weighted inversion of general Dirichlet series*，
[arXiv:1112.0749v2](https://arxiv.org/abs/1112.0749v2)。
实际 \(\beta,\gamma\) 复用 §§384–385；整数商复合身份复用 §414；
概率单调性复用 §448；原临界补偿复用 §449。新增承重是全部整数
纤维的精确临界算子范数、重复逆的显式指数下界、具体非保号输入及
多项式统一成本与平方根递归深度的定量冲突，为本仓推导（repo-derived），
不作全局原创性断言。

## 453. 实际奇数 Möbius 二倍配对的原尾素数面板与必需联合补偿

本单元检验 §419 所提示的二幂消去，在 §424 的**原始实际阶乘配对**中能否单独取得 Robin 临界收益。结论是一个实际输入的局部障碍：精确配对后的真实素数面板仍有严格负的 \(1/\log^2x\) 主项；同一完整补集必须反向补偿它。这里不把面板贡献当成全尾下界，也不声称 RH 的反例或一般数学不可能性。

新增承重内容是：实际奇数 Möbius 源的有限截止、条件级数末项付款，以及固定二倍配对在 \(p\asymp x\) 上的原尾素数面板主项。移动尺度的核误差直接消费 §425.5，不重证其完整 β 纤维预算。以下为解析推导；原临界有符号估计仍未解决。

### 453.1 原字面对象与既有供应

固定真实 Möbius 函数 \(\mu\)，\(M(n)=\sum_{r=1}^n\mu(r)\)。对于全部 \(y>0\)，保持

\[
\eta(y)=\log(\lfloor y\rfloor!)-y\log y+y.
\]

\(\eta\) 是这个固定函数，不随 \(x\)、素数面板或截止改变。对于实数 \(x>1,s>0\) 和正整数 \(n\)，保持 §424.1 的字面定义

\[
w(t)=\frac{1+\log t}{t^2\log^2t},\qquad
P_x^\eta(s)=\int_x^\infty\eta(t/s)w(t)\,dt,
\qquad J_x^\eta(n)=P_x^\eta(n)-P_x^\eta(n+1).
\tag{DP.1}
\]

同一个完整目标是

\[
I_\psi(x)=\int_x^\infty[\psi(t)-t]w(t)\,dt,
\qquad Z_\psi(x)=\sqrt x\log x\,I_\psi(x).
\tag{DP.2}
\]

下列既有供应直接复用，并保留其证据范围。

* §§422、424：存在固定有限 \(C_M\)，对全部 \(n\ge1\) 有
  \( |M(n)|\le C_M n/(1+\log n)^4\)。§424.5 已支付积分前绝对预算，故
  \(I_\psi(x)=\sum_{n\ge1}M(n)J_x^\eta(n)\) 绝对收敛，包含原首块及全部整数纤维。它没有支付未阻尼的 Möbius 原子绝对和。
* §425.5：对于固定 \(U\ge0\)，既有有限常数 \(\mathsf C_\beta(U),\mathsf L_\beta(U)\) 满足

  \[
  \left|n^2\log x\,J_x^\eta(n)
  -\left[\frac{\log^2(n/x)}2+\gamma_1\right]\right|
  \le\frac{\mathsf C_\beta(U)}{\log x}
  +\frac{\mathsf L_\beta(U)}n
  \quad(x\ge e,\ x\le n\le e^Ux).
  \tag{DP.3}
  \]

  这些是 §425.3 对全部无界 β 来源的完整常数，不能换成逐个固定来源的极限。
* §429.2–3：\( |\eta(y)|\le1+\log y\) 对 \(y\ge1\) 成立。若 \(s>x\ge e\)，\(\ell=\log x\)、\(v=\log(s/x)\)，则

  \[
  -\frac{d}{ds}P_x^\eta(s)=\frac{G_{\eta,x}(\log s)}{s^2},\qquad
  |\ell G_{\eta,x}(\ell+v)|\le v^2/2+v+12.
  \tag{DP.4}
  \]

  该导数来自同一完整阶乘核，不用点值包络代替跳跃差分。
* \(\gamma_1\) 使用原约定 \(\zeta(1+z)=z^{-1}+\gamma_E-\gamma_1z+O(z^2)\)。下一小节用纯解析证明 \(\gamma_1>-167/1600>-1/8\)，面板正性据此付款。既有 `robin-kernel-diagonal.json` 的向外下端点为

  \[
  g_-=-3656579760393884564419850453066548425766419045455786552735\cdot2^{-195}.
  \]

  该保存区间及精确比较 \(g_->-1/8\) 只作交叉参考，不是下文的证明前提，也不是 Lean 定理。来源是既有 FLINT `acb.stieltjes(1)` 区间，源说明还核对 deflated ζ 的一次系数约定；两接口不是独立数值算法的声明。
* 仓内 `Library/Weil/johnstonyang2022pnt.md` 记录 Johnston–Yang arXiv:2204.01980v2，Theorem 1.1、(1.3)、印刷 p.2：对全部 \(t\ge2\)，

  \[
  |\psi(t)-t|\le9.39t(\log t)^{1.515}e^{-0.8274\sqrt{\log t}}.
  \tag{DP.5}
  \]

  这是包含全部素幂的无条件既有供应。下文的 PNT 求和和粗于临界的尾预算都是它的经典后果，没有把有限验零输入升级成全局 RH。

### 453.2 \(\gamma_1\) 的纯解析下界及符号约定

先付清 Stieltjes 极限与原 Laurent 约定的联系。对 \(\Re z>0\)，经典 Dirichlet 级数与积分给

\[
\zeta(1+z)-z^{-1}
=\sum_{n\ge1}\left[n^{-1-z}-\int_n^{n+1}t^{-1-z}dt\right].
\tag{DG.1}
\]

在 \(|z|\le1/4\) 上，每个差值由关于 \(t\) 的一阶导数控制，其项及关于 \(z\) 的一阶导数共同有 \(O((1+\log n)n^{-7/4})\) 的可和包络。因此差值级数在此盘正常收敛并可逐项微分；它解析延拓（DG.1）的左侧到零点。原 Laurent 约定给其零点导数为 \(-\gamma_1\)，所以

\[
\gamma_1=\lim_{N\to\infty}
\left[\sum_{n=1}^N\frac{\log n}{n}-\frac{\log^2N}{2}\right].
\tag{DG.2}
\]

实际逐项微分先产生 \(\log^2(N+1)/2\)；由于 \(\tfrac12[\log^2(N+1)-\log^2N]\to0\)，上式的端点替换已经支付。

令 \(f(t)=\log t/t\)、\(L=\log2\)。对于整数 \(N\ge3\)，复合梯形和为

\[
T_{2,N}=\frac{f(2)}2+\sum_{n=3}^{N-1}f(n)+\frac{f(N)}2.
\]

两次有限分部积分给保留端点的 Peano 核恒等式

\[
T_{2,N}-\int_2^Nf(t)dt
=\frac12\sum_{n=2}^{N-1}
\int_n^{n+1}(t-n)(n+1-t)f''(t)dt.
\tag{DG.3}
\]

该单元核在整个单位区间不超过 \(1/8\)，故

\[
\left|T_{2,N}-\int_2^Nf(t)dt\right|
\le\frac18\int_2^N|f''(t)|dt.
\]

这里 \(f'(t)=(1-\log t)/t^2\)、\(f''(t)=(2\log t-3)/t^3\)。\(f''\) 在 \(2<t<e^{3/2}\) 为负，在 \(t>e^{3/2}\) 为正；\(f'(e^{3/2})=-1/(2e^3)\)，而 \(f'(t)\to0\)。因此完整绝对曲率质量精确为

\[
\int_2^\infty|f''(t)|dt=\frac{1-L}{4}+e^{-3}.
\tag{DG.4}
\]

再用
\(\sum_{n=1}^Nf(n)=T_{2,N}+f(2)/2+f(N)/2\)、
\(\int_2^Nf=(\log^2N-L^2)/2\)、
\(f(N)\to0\)，从（DG.2）–（DG.4）得到

\[
\gamma_1\ge\frac L4-\frac{L^2}{2}
-\frac{1-L}{32}-\frac1{8e^3}.
\tag{DG.5}
\]

严格凸函数 \(1/t\) 的中点积分比较给 \(L>2/3\)。正项 Taylor 级数给

\[
e^{7/10}>1+\frac7{10}+\frac{49}{200}+\frac{343}{6000}
=\frac{12013}{6000}>2,
\]

所以 \(L<7/10\)；同样 \(e>2\)。逐项用这些严格界，即得完全有理的解析下界

\[
\boxed{\displaystyle
\gamma_1>
\frac16-\frac{49}{200}-\frac1{96}-\frac1{64}
=-\frac{167}{1600}>-\frac18.}
\tag{DG.6}
\]

这个证明支付无限端点和原符号约定，不需数值 Stieltjes 区间。

### 453.3 奇数前缀与固定 \(x\) 的截止末项

定义 \(O(y)=\sum_{1\le m\le y,\ m\text{ 奇}}\mu(m)\)（\(y\ge0\)，空和为零）。实际恒等式 \(\mu(2m)=-\mu(m)\) 对奇数 \(m\) 成立，而 \(4\mid r\) 时 \(\mu(r)=0\)。因此

\[
M(n)=O(n)-O(n/2)
=\sum_{n/2<m\le n,\ m\text{ 奇}}\mu(m).
\tag{DP.6}
\]

递归展开并在正指标终止，给 \(y\ge1\) 的有限恒等式

\[
O(y)=\sum_{\substack{a\ge0\\2^a\le y}}M(\lfloor y/2^a\rfloor).
\tag{DP.7}
\]

这不消费零指标的 Mertens 估计。若 \(y\ge4\)，令 \(a_0=\lfloor\tfrac12\log_2y\rfloor\)。对于 \(a\le a_0\)，

\[
\lfloor y/2^a\rfloor\ge\frac{\sqrt y}{2},\qquad
1+\log\lfloor y/2^a\rfloor\ge\tfrac12\log y,
\]

第二式使用 \(1>\log2\)。用既有 Mertens 供应及几何和，得到

\[
\sum_{a\le a_0}|M(\lfloor y/2^a\rfloor)|
\le\frac{32C_My}{\log^4y}.
\]

余下部分用 \( |M(k)|\le k\)，其总量不超过

\[
\sum_{a>a_0}y/2^a=y/2^{a_0}<2\sqrt y.
\]

因为 \(\log^4y/\sqrt y\to0\)，并可用 \( |O(y)|\le y\) 吸收有限头，故存在有限常数 \(C_O\) 使

\[
|O(y)|\le C_O\frac{y}{(1+\log y)^4}\qquad(y\ge1).
\tag{DP.8}
\]

还要独立控制 \(P_x^\eta\) 的原子截止。固定 \(x\ge e\)，写 \(\ell=\log x\)、\(r=\log s\)。对于 \(s\ge x\)，低商 \(x\le t\le s\) 上有 \(\eta(t/s)=(t/s)[1-\log(t/s)]\)，从而直接积分得

\[
\begin{aligned}
P_{x,\mathrm{low}}^\eta(s)
&=\frac1s\int_\ell^r\left[\frac{1+r}{u^2}+\frac r u-1\right]du\\
&=\frac1s\left[r\log r+
  (\ell^{-1}-\log\ell-1)r+
  (\ell^{-1}+\ell-1)-r^{-1}\right].
\end{aligned}
\tag{DP.9}
\]

高商 \(t\ge s\) 换元 \(t=sy\)，由 \(\int_1^\infty(1+\log y)y^{-2}dy=2\) 给

\[
|P_{x,\mathrm{high}}^\eta(s)|
\le\frac2s(r^{-1}+r^{-2}).
\tag{DP.10}
\]

所以（DP.4）、（DP.9）–（DP.10）共同支付

\[
|P_x^\eta(s)|=O_x\!\left(\frac{(1+\log s)^2}s\right),\qquad
|(P_x^\eta)'(s)|=O_x\!\left(\frac{(1+\log s)^2}{s^2}\right)
\quad(s>x).
\tag{DP.11}
\]

常数允许依赖这个固定 \(x\)；此处没有增长 \(x\) 的统一截止账。

### 453.4 精确有限配对及条件极限

定义真实二倍配对核

\[
\mathscr D_x(m)=P_x^\eta(m)-P_x^\eta(2m)
=\sum_{n=m}^{2m-1}J_x^\eta(n)\qquad(m\ge1).
\tag{DP.12}
\]

对每个整数 \(N\ge1\)，令 \(S_N(x)=\sum_{n=1}^NM(n)J_x^\eta(n)\)。在有限集合中使用（DP.6）及望远镜，精确得到

\[
\boxed{\displaystyle
S_N(x)=\sum_{m\le N,\ m\text{ 奇}}\mu(m)
\left[P_x^\eta(m)-P_x^\eta(\min\{2m,N+1\})\right].}
\tag{DP.13}
\]

触发条件是 \(m\le n<2m\)；一个完整奇源纤维恰为 \(m\le n\le2m-1\)。这包括原单位源 \(m=1\)，其核 \(\mathscr D_x(1)=J_x^\eta(1)\) 保留 §424.7 的原首块补偿。

令 \(T_N(x)=\sum_{m\le N,\ m\text{ 奇}}\mu(m)\mathscr D_x(m)\)，则

\[
E_N(x):=S_N(x)-T_N(x)
=\sum_{N/2<m\le N,\ m\text{ 奇}}\mu(m)
\left[P_x^\eta(2m)-P_x^\eta(N+1)\right].
\tag{DP.14}
\]

若 \(2m=N+1\)，括号精确为零，所以该写法对奇偶 \(N\) 都成立。取固定 \(x\)，随后令 \(N\to\infty\)。对 \(N>2x\)，在 \([N/2,N]\) 上置

\[
B_N(t)=O(t)-O(N/2),\qquad
F_N(t)=P_x^\eta(2t)-P_x^\eta(N+1).
\]

（DP.8）给 \(\sup|B_N(t)|=O(N/\log^4N)\)；（DP.11）给

\[
|F_N(N)|+\int_{N/2}^N|F_N'(t)|dt
=O_x(\log^2N/N).
\]

有限 Abel 求和保留全部端点：

\[
E_N(x)=B_N(N)F_N(N)-\int_{N/2}^NB_N(t)F_N'(t)dt
=O_x(\log^{-2}N)\longrightarrow0.
\tag{DP.15}
\]

§424 的绝对 Mertens 配对使 \(S_N(x)\to I_\psi(x)\)，故得到付清截止末项后的原子身份

\[
\boxed{\displaystyle
I_\psi(x)=\lim_{N\to\infty}
\sum_{m\le N,\ m\text{ 奇}}\mu(m)\mathscr D_x(m).}
\tag{DP.16}
\]

这个极限按所写奇源自然截止定义。它没有从 §424 的绝对累计配对推出原子绝对交换。事实上（DP.9）–（DP.10）还给固定 \(x\) 下

\[
\mathscr D_x(m)\sim\frac{\log m\log\log m}{2m}\qquad(m\to\infty).
\]

在真实奇素数 \(p\) 上 \( |\mu(p)|=1\)，因此该原子绝对和发散：充分大的素数项至少为 \(\log p/(4p)\)，而既有第一 Mertens 供应 \(\sum_{p\le Y}\log p/p=\log Y+O(1)\) 发散。这里的条件截止付款不可删除，也不能将全部素数与合数另作未经支付的无限分拆。

### 453.5 \(p\asymp x\) 的共同二倍核估计

保持 \(x\ge e\)、\(\ell=\log x\)。令

\[
q_\eta(v)=\tfrac12\log^2v+\gamma_1,\quad
C_*=\mathsf C_\beta(\log8),\quad L_*=\mathsf L_\beta(\log8),
\quad D_* =\log8+\log^28+2|\gamma_1|.
\]

对每个整数 \(2x<m\le4x\)，纤维 \(m\le n\le2m-1\) 的全部行满足 \(2<n/x<8\)。因此（DP.3）用**同一个** \(U=\log8\)，求和并用 \(\sum_{n=m}^{2m-1}n^{-2}\le m^{-1}\)、\(\sum n^{-3}\le m^{-2}\)，得到

\[
\left|\mathscr D_x(m)-\frac1\ell
\sum_{n=m}^{2m-1}\frac{q_\eta(n/x)}{n^2}\right|
\le\frac{C_*}{m\ell^2}+\frac{L_*}{m^2\ell}.
\tag{DP.17}
\]

函数 \(f_x(s)=q_\eta(s/x)/s^2\) 在 \([m,2m]\) 上满足

\[
f_x'(s)=\frac{\log(s/x)-\log^2(s/x)-2\gamma_1}{s^3},
\qquad |f_x'(s)|\le D_*/s^3.
\]

逐个完整单位区间积分，故

\[
\left|\sum_{n=m}^{2m-1}f_x(n)-\int_m^{2m}f_x(s)ds\right|
\le\frac{D_*}{2m^2}.
\]

定义固定紧区间轮廓

\[
k_2(u)=\int_u^{2u}\frac{q_\eta(v)}{v^2}dv\qquad(2\le u\le4).
\tag{DP.18}
\]

换元 \(s=xv\)，得到显式共同误差

\[
\boxed{\displaystyle
\left|x\ell\,\mathscr D_x(m)-k_2(m/x)\right|
\le\frac{C_*}{2\ell}+\frac{L_*+D_*/2}{4x}
\quad(2x<m\le4x).}
\tag{DP.19}
\]

此界同时适用于面板内全部真实素数，且保留原 \(2m\) 端点。没有将固定 \(x\) 渐近冒充联合 \(x,m\) 渐近。

令 \(L=\log2\)。由 \(L=\int_1^2dt/t>1/2\) 及已支付的 \(\gamma_1>-1/8\)，

\[
q_0:=\tfrac12L^2+\gamma_1>0,\qquad
k_2(u)\ge q_0\int_u^{2u}v^{-2}dv
=q_0/(2u)\ge q_0/8.
\tag{DP.20}
\]

当（DP.19）的共同误差小于 \(q_0/16\) 时，所有面板核都严格为正，并有 \(\mathscr D_x(m)>q_0/(16x\ell)\)。该共同阈值存在；本篇不提供其数值。

### 453.6 真实素数面板的严格主项

对于同一实数 \(x\)，令

\[
\mathcal P_x=\{p\text{ 素数}:2x<p\le4x\},\qquad
\mathcal A_x=\sum_{p\in\mathcal P_x}\mathscr D_x(p),\qquad
\Pi_x=\sum_{p\in\mathcal P_x}\mu(p)\mathscr D_x(p)=-\mathcal A_x.
\tag{DP.21}
\]

因为 \(x\ge e\)，面板中每个素数均为奇数，真实系数精确为 \(\mu(p)=-1\)。对于任何 \(N\ge\lceil8x\rceil\)，这些素数源都已经在（DP.13）中触发完整纤维，因为 \(2p-1\le N\)。\(2x\) 的严格下端和 \(4x\) 的闭上端不被改变。

经典 PNT 在全部 \(u\in[2,4]\) 上共同给

\[
F_x(u):=\frac\ell x[\pi(ux)-\pi(2x)]\longrightarrow u-2.
\tag{DP.22}
\]

这也可直接由（DP.5）导出：素幂余项 \(\psi(t)-\vartheta(t)=O(\sqrt t\log^2t)\) 给 \(\vartheta(t)=t+o(t)\)，再对 \(\vartheta\) 有限 Abel 求和得到 \(\pi(t)\sim t/\log t\)。共同性来自 \(ux\ge2x\to\infty\) 及 \(\ell/\log(ux)\to1\) 于固定紧区间共同成立；未调用短区间 PNT。

对 \(k_2\) 有限 Abel 求和，保留 \(F_x(2)=0\)，得到

\[
\frac\ell x\sum_{p\in\mathcal P_x}k_2(p/x)
=k_2(4)F_x(4)-\int_2^4F_x(u)k_2'(u)du
\longrightarrow C_{\rm pair}:=\int_2^4k_2(u)du>0.
\tag{DP.23}
\]

PNT 还给 \(\#\mathcal P_x=O(x/\ell)\)。因此（DP.19）在整个面板求和的核误差为 \(O(\ell^{-3})+O((x\ell^2)^{-1})=O(\ell^{-3})\)，从而

\[
\boxed{\displaystyle
\mathcal A_x=\frac{C_{\rm pair}}{\log^2x}+o(\log^{-2}x),\qquad
\Pi_x=-\frac{C_{\rm pair}}{\log^2x}+o(\log^{-2}x).}
\tag{DP.24}
\]

常数具有完全指定的正积分和闭式。积分原函数给

\[
k_2(u)=\frac1{2u}\left[1+\gamma_1-L-\frac{L^2}2
+(1-L)\log u+\frac{\log^2u}2\right],
\]

故

\[
\boxed{\displaystyle
C_{\rm pair}=\int_2^4\int_u^{2u}
\frac{\tfrac12\log^2v+\gamma_1}{v^2}\,dv\,du
=\frac{(1+\gamma_1)L}{2}+\frac{L^2}{4}-\frac{5L^3}{12}>0.}
\tag{DP.25}
\]

正性由（DP.20）证明，不依赖闭式小数求值。

### 453.7 保留完整来源的反向补偿与精确缺口

定义同一奇源截止的完整补集

\[
\mathscr C_x=\lim_{N\to\infty}
\sum_{\substack{m\le N,\ m\text{ 奇}\\m\notin\mathcal P_x}}
\mu(m)\mathscr D_x(m).
\tag{DP.26}
\]

这是删除一个有限面板后的自然截止极限；（DP.16）证明它存在。它保留单位源、全部其余奇素数、所有合数源、\(m<x\)、面板两侧和全部远尾，以及每份奇源中的完整偶倍配对。通过（DP.13）–（DP.15），这些来源恢复同一个原 Mertens 配对，故没有遗失原首块或 β 运输补偿。精确身份是

\[
\boxed{I_\psi(x)=\Pi_x+\mathscr C_x=\mathscr C_x-\mathcal A_x.}
\tag{DP.27}
\]

（DP.5）使存在有限 \(C_4\) 满足 \( |\psi(t)-t|\le C_4t/\log^4t\) 对全部 \(t\ge2\) 成立，因为 \(u^{5.515}e^{-0.8274\sqrt u}\) 在 \(u\ge\log2\) 上有界。直接在原核积分给

\[
|I_\psi(x)|\le C_4\left[\frac1{4\ell^4}+\frac1{5\ell^5}\right].
\tag{DP.28}
\]

所以该同源补集已有必需反向主项

\[
\boxed{\displaystyle
\mathscr C_x=\mathcal A_x+O(\log^{-4}x)
=\frac{C_{\rm pair}}{\log^2x}+o(\log^{-2}x).}
\tag{DP.29}
\]

这里先使用同一个完整身份取差，没有对补集逐项取 \(x\to\infty\) 的极限；也没有把其来源换成另一优化值。两份实际量在临界归一化下分别为

\[
\sqrt x\log x\,\Pi_x\sim-C_{\rm pair}\frac{\sqrt x}{\log x}\to-\infty,
\qquad
\sqrt x\log x\,\mathscr C_x\sim C_{\rm pair}\frac{\sqrt x}{\log x}\to+\infty.
\tag{DP.30}
\]

因此，二倍配对已经发生，却没有单独把这个实际面板降至 Robin 临界尺度。完整补集确实产生反向抵消；（DP.28）的对数预算仍不支付它们差值的临界预算。面板负项不构成 \(I_\psi\) 的负下界。

若原目标要求某个固定 \(B\ge0\) 的一侧临界下界，缺失的同源联合条件须对**精确面板值**写成

\[
\boxed{\displaystyle
\mathscr C_x\ge\mathcal A_x-\frac B{\sqrt x\log x}
\quad\text{对全部充分大实数 }x.}
\tag{DP.31}
\]

这是（DP.27）下原下界的字面要求，不是新 RH 判据或已证结论。如果选用更强的绝对临界预算，则需要

\[
|\mathscr C_x-\mathcal A_x|\le B/(\sqrt x\log x).
\tag{DP.32}
\]

（DP.24）的 \(o(\log^{-2}x)\) 或共同核账中的 \(O(\log^{-3}x)\) 都不能直接替代（DP.31）中的精确 \(\mathcal A_x\)：它们没有临界误差预算。与面板 \(C_{\rm pair}/\log^2x\) 相比，临界缺额的允许比例只有 \(O(\log x/\sqrt x)\)；一侧目标允许更大的正向补偿，不要求两侧相等。也不能把（DP.15）的固定 \(x\) 末项界用于未经支付的联合截止 \(N=N(x)\)。

### 453.8 来源、非重复范围及证据边界

§419 是实际 Fibonacci \(e_n\) 的逐二幂链终端；§421、§423 是 \(H_{\rm raw}\) 的素核／固定复杂度层主项。本单元处理原 \(I_\psi\) 中真实普通 Möbius 的固定二倍配对，并在 \(p\asymp x\) 上计算完整相邻纤维的面板。§§429、435 已给其他增长 Euler 过滤器的实际窗口及反向补集；这里没有重发其结果或声称“补集补偿”这个原则的新颖性。§452 的输入空间算子成本也没有被当成真实 Möbius 达到最坏情况的证据。

直接复用范围：§§422、424、425.3–5、429.2–3；既有第一 Mertens 供应；Johnston–Yang v2 的上述无条件 Chebyshev 误差供应。新增推导为（DP.13）–（DP.16）的实际有限截止与 Abel 付款、（DP.17）–（DP.25）的同一二倍纤维面板及显式常数，以及以精确面板保留全部补集的（DP.27）–（DP.31）。不作全球原创性声明。

（DG.1）–（DG.6）给出本节使用的解析下界、正常收敛及原约定联系。Stieltjes 经典约定仍沿用既有源说明及 DLMF §25.2.4；梯形误差、有限分部积分与正常收敛只是经典中间工具。保存的 FLINT 向外区间只作交叉参考，没有作为解析下界前提或 Lean 定理。

本次读取的源快照 SHA-256：

* `docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md`：`eb0bcb3fad6aaded820f8e6d3c8cb07008068c694a7747ac369cd1f5ad96acda`。
* `docs/reports/fib-robin-boundary/robin-kernel-diagonal.json`：`29834f084f6b7be486efd5c1516093e4b6c2a12e690c46d01e94e31c472e963d`。
* `docs/reports/fib-robin-boundary/robin-kernel-diagonal.md`：`1f8347eda47d65d874dbda10c053fc1ee743ac040b99470350b3b279c33f45c7`。
* `Library/Weil/johnstonyang2022pnt.md`：`adb7c7bc038556fe195dc977121a4fe9a34d804e0578c81964b4e8c3a2a779d8`。

这些源与经典供给的归属保持原记录。本节是纸面证明；原临界有符号估计、其常数和全范围仍未解决。

## 454. 真实素数面板在有界二倍逆运输后的有限截止符号翻转

同一个真实 Möbius 素数面板在原配对中有严格负主项；将它改写成奇数前缀配对，再只取 \(N=\lceil8x\rceil\) 以前的部分，主项却严格为正。完整逆运输保留原符号，有限截止留下一个精确边界块。这个边界仍是 \(1/\log^2x\) 量级，必须与正前段共同保留。

本节的承重结论是这个实际面板的截止符号翻转及其完整边界。二倍逆范数直接复用 §452，原奇数 Möbius 完整配对及积分前预算直接复用 §427 的 \(P=2\) 情形；这些复用接口不另作新成果。原 Robin 临界有符号界仍未解决。

### 454.1 同一实际对象与两个配对

保持 §§424、453 的字面定义
\[
\eta(y)=\log(\lfloor y\rfloor!)-y\log y+y,\qquad
w(t)=\frac{1+\log t}{t^2\log^2t},
\]
\[
P_x^\eta(s)=\int_x^\infty\eta(t/s)w(t)dt,\qquad
J_x^\eta(n)=P_x^\eta(n)-P_x^\eta(n+1),\qquad
\mathscr D_x(m)=P_x^\eta(m)-P_x^\eta(2m).
\tag{BC.1}
\]
这里 \(\eta\) 固定，\(x\ge e\) 为同一实数源；全部整数索引均为正。令
\[
\ell=\log x,\quad L=\log2,\quad
\mathcal P_x=\{p\text{ 素数}:2x<p\le4x\},\quad Q_x^\mathrm{p}=\#\mathcal P_x,
\]
\[
\mathcal A_x=\sum_{p\in\mathcal P_x}\mathscr D_x(p),\qquad
\Pi_x=-\mathcal A_x.
\tag{BC.2}
\]
上端闭、下端严格，面板中的每个素数均为奇数且 \(\mu(p)=-1\)。\(Q_x^\mathrm{p}\) 是素数数目，不是此前的核积分范数 \(Q_x\)。

对 \(n\ge0\)，定义面板的真实奇数前缀及完整 Möbius 前缀分量
\[
\mathcal U_x(n)=\sum_{\substack{p\in\mathcal P_x\\p\le n}}\mu(p)
=-\#\{p\in\mathcal P_x:p\le n\},
\qquad
\mathcal V_x(n)=\mathcal U_x(n)-\mathcal U_x(\lfloor n/2\rfloor).
\tag{BC.3}
\]
两列在零处为零；\(\mathcal U_x(n)=0\) 当 \(n\le2x\)，而
\(\mathcal U_x(n)=-Q_x^\mathrm{p}\) 当 \(n\ge4x\)。
实际 \(\mu(2p)=-\mu(p)=1\) 给
\[
\mathcal V_x(n)=-\#\{p\in\mathcal P_x:p\le n<2p\}.
\tag{BC.4}
\]
所以 \(\mathcal V_x\) 支撑于 \(n<8x\)。有限面板及完整整数纤维求和直接给
\[
\sum_{n\ge1}\mathcal V_x(n)J_x^\eta(n)
=-\sum_{p\in\mathcal P_x}\sum_{n=p}^{2p-1}J_x^\eta(n)
=-\mathcal A_x=\Pi_x.
\tag{BC.5}
\]
这正是 §453 的实际面板，不是另选符号或测试输入。

### 454.2 已付款的逆运输、对偶空间与全来源

在 \(f(0)=0\) 的序列上，保持
\[
(T_2f)(n)=f(\lfloor n/2\rfloor),\qquad
(B_2k)(n)=k(2n)+k(2n+1).
\]
对于固定整数 \(j\ge0\)，§452 的
\(W_j(n)=\sqrt n(1+\log n)^j\)、
\(\mathcal X_j=\ell^\infty(W_j^{-1})\)
与自然配对的前对偶
\[
\mathcal Y_j=\left\{k:\ \|k\|_{\mathcal Y_j}
=\sum_{n\ge1}W_j(n)|k(n)|<\infty\right\}
\]
满足 \(\mathcal X_j=(\mathcal Y_j)^*\)。\(\mathcal Y_j\) 不被宣称为 \(\mathcal X_j\) 的整个 Banach 对偶。
完整商纤维给
\(\langle T_2f,k\rangle=\langle f,B_2k\rangle\)；
\(r=1\) 的零商乘 \(f(0)=0\)，其余纤维恰为 \(r=2n,2n+1\)。
§452 的精确系数范数直接给
\[
\|T_2\|=\|B_2\|=2^{-1/2},\qquad
G=(I-T_2)^{-1}=\sum_{a\ge0}T_{2^a},\qquad
\|G\|=2+\sqrt2.
\tag{BC.6}
\]
算术系数是 \(g_d=\mathbf1_{d=2^a,\ a\ge0}\)，其完整临界系数和为
\(\sum_a2^{-a/2}=2+\sqrt2\)；每个整数输入点的逆和因零商而局部终止。
相应前对偶逆 \(\sum_aB_2^a\) 在算子范数中收敛，范数相同。
这是加权 Dirichlet 卷积单位群的既有算子表示及经典 Neumann 逆应用。

定义原核的完整前对偶变换
\[
\mathcal L_x(n)=(I-B_2)J_x^\eta(n)
=J_x^\eta(n)-J_x^\eta(2n)-J_x^\eta(2n+1)
=\mathscr D_x(n)-\mathscr D_x(n+1).
\tag{BC.7}
\]
§424.12 的完整积分范数界给
\(Q_x^\eta(n)\le C'_x(1+\log n)^2/n^2\)，故每个固定 \(x\) 与 \(j\) 上
\[
\sum_{n\ge1}W_j(n)Q_x^\eta(n)<\infty,\qquad
J_x^\eta,\mathcal L_x\in\mathcal Y_j.
\tag{BC.8}
\]
因为 \(\mathcal U_x\) 有界，面板配对还具有直接的积分前绝对账：
\[
\sum_{n\ge1}|\mathcal U_x(n)|
\int_x^\infty|\eta_2(t/n)-\eta_2(t/(n+1))|w(t)dt
\le Q_x^\mathrm{p}\sum_{n\ge1}
[Q_x^\eta(n)+Q_x^\eta(2n)+Q_x^\eta(2n+1)]<\infty,
\tag{BC.9}
\]
其中固定 \(\eta_2(y)=\eta(y)-\eta(y/2)\)。因此（BC.5）的完整前对偶运输绝对合法：
\[
\boxed{\sum_{n\ge1}\mathcal U_x(n)\mathcal L_x(n)
=\sum_{n\ge1}\mathcal V_x(n)J_x^\eta(n)
=-\mathcal A_x.}
\tag{BC.10}
\]

对全实际来源 \(O(n)=\sum_{m\le n,\ m\text{ 奇}}\mu(m)\)，已有 §427（GP.1）–（GP.3）取固定 \(P=2\) 正好给
\[
I_\psi(x)=\sum_{n\ge1}O(n)\mathcal L_x(n),\qquad
\sum_n|O(n)|Q_x^{\eta_2}(n)<\infty.
\tag{BC.11}
\]
这里 \(O(1)=1\)、\(\theta_{2,1}=\beta_1\)，原首块补偿及全部纤维均保留。
这份完整实际预算来自无条件 \(O(n)=O(n/(1+\log n)^4)\) 和固定过滤器账，未假设全实际 \(M,O\in\mathcal X_j\)。RH 的全部 \(N^{1/2+\varepsilon}\) 供应不能被当成某个固定平方根对数范数的免费输入。

### 454.3 截止不交换及精确边界

对整数 \(N\ge\lceil8x\rceil\)，令 \(P_{\le N}f=f\,\mathbf1_{n\le N}\)。实际常值前缀给逐点恒等式
\[
\boxed{(I-T_2)(P_{\le N}\mathcal U_x)-\mathcal V_x
=Q_x^\mathrm{p}\mathbf1_{N<n\le2N+1}.}
\tag{BC.12}
\]
当 \(n\le N\)，两者恰相同；当 \(N<n\le2N+1\)，正商满足
\(4x\le\lfloor n/2\rfloor\le N\)，故右侧恰为
\(-\mathcal U_x(\lfloor n/2\rfloor)=Q_x^\mathrm{p}\)；
当 \(n>2N+1\)，两份截止读出为零，而 \(\mathcal V_x(n)=0\)。
这保留奇端点 \(2N+1\)，没有用连续区间代替真实整数商。

记同一面板的有限前段及全尾为
\[
\mathscr H_x(N)=\sum_{n=1}^N\mathcal U_x(n)\mathcal L_x(n),\qquad
\mathscr T_x(N)=\sum_{n>N}\mathcal U_x(n)\mathcal L_x(n).
\]
对（BC.12）配对并在有限边界块中望远镜，得到
\[
\boxed{\mathscr H_x(N)
=-\mathcal A_x+Q_x^\mathrm{p}
[P_x^\eta(N+1)-P_x^\eta(2N+2)]
=-\mathcal A_x+Q_x^\mathrm{p}\mathscr D_x(N+1).}
\tag{BC.13}
\]
§453（DP.11）已给固定 \(x\) 的 \(P_x^\eta(s)\to0\)。
因此由（BC.7）及（BC.8）的绝对收敛，
\[
\boxed{\mathscr T_x(N)=-Q_x^\mathrm{p}\mathscr D_x(N+1),\qquad
\mathscr H_x(N)+\mathscr T_x(N)=-\mathcal A_x.}
\tag{BC.14}
\]
等价地，每个面板素数 \(p\) 在 \(\mathcal U_x\) 中留下完整阶跃，
\(\sum_{n\ge p}\mathcal L_x(n)=\mathscr D_x(p)\)。
原有限支撑被变成常值前缀的无限尾；上述完整边界支付后总配对仍相同。

### 454.4 原核的共同边界主项及解析符号

取同一真实截止 \(N_x=\lceil8x\rceil\)。令
\[
q_\eta(v)=\tfrac12\log^2v+\gamma_1,\qquad
k_2(u)=\int_u^{2u}\frac{q_\eta(v)}{v^2}dv.
\]
§453（DP.17）–（DP.19）的证明直接消费 §425.5。在这里对全部
\(8x\le m\le9x\) 使用同一个 \(U=\log18\)，给
\[
\left|x\ell\mathscr D_x(m)-k_2(m/x)\right|
\le\frac{\mathsf C_\beta(\log18)}{8\ell}
+\frac{\mathsf L_\beta(\log18)+D_{18}/2}{64x},
\quad D_{18}=\log18+\log^218+2|\gamma_1|.
\tag{BC.15}
\]
付款步骤仍是对 \(m\le n\le2m-1\) 的完整共同误差求和，
再用 \( |[q_\eta(s/x)/s^2]'|\le D_{18}/s^3\) 支付单位纤维到积分的端点误差。
这覆盖 \(m=N_x+1\)，其 \(m/x\to8\)，所以
\[
x\ell\mathscr D_x(N_x+1)\longrightarrow
k_2(8)=\frac{1+\gamma_1+2L+L^2}{16}>0.
\tag{BC.16}
\]
正性已由 §453 的解析 \(\gamma_1>-1/8\) 及 \(L>1/2\) 付款。
既有 PNT 给 \(\ell Q_x^\mathrm{p}/x\to2\)。故定义
\[
C_{\rm tail}=2k_2(8)=\frac{1+\gamma_1+2L+L^2}{8},
\qquad
C_{\rm pair}=\frac{(1+\gamma_1)L}{2}+\frac{L^2}{4}-\frac{5L^3}{12}>0,
\tag{BC.17}
\]
则（BC.13）–（BC.16）和 §453（DP.24）共同给
\[
\ell^2\mathscr T_x(N_x)\to-C_{\rm tail},\qquad
\ell^2\mathscr H_x(N_x)\to C_{\rm head}:=C_{\rm tail}-C_{\rm pair}.
\tag{BC.18}
\]

还须证明 \(C_{\rm head}>0\)，不能用近似数值判断符号。
§453（DG.3）–（DG.5）的同一**绝对**梯形余项也给反向界
\[
\gamma_1\le L/4-L^2/2+(1-L)/32+1/(8e^3)
<7/40-2/9+1/96+1/64=-61/2880<0.
\tag{BC.19}
\]
这里严格界 \(2/3<L<7/10\)、\(e>2\) 均已在 §453 解析证明。
由（BC.17）直接展开，
\[
C_{\rm head}=(1+\gamma_1)(1/8-L/2)
+L/4-L^2/8+5L^3/12.
\]
因为 \(1/8-L/2<0\)、\(1+\gamma_1<1\)，所以
\[
\boxed{C_{\rm head}>
1/8-L/4-L^2/8+5L^3/12
>1/8-7/40-49/800+10/81
=791/64800>0.}
\tag{BC.20}
\]
因此对于全部充分大实数 \(x\)，同一个实际面板满足
\[
\boxed{\mathscr H_x(\lceil8x\rceil)>0,\qquad
\mathscr T_x(\lceil8x\rceil)<0,\qquad
\mathscr H_x(\lceil8x\rceil)+\mathscr T_x(\lceil8x\rceil)
=-\mathcal A_x<0.}
\tag{BC.21}
\]
负尾的主项严格大于正前段的主项，差值恰是原 \(C_{\rm pair}\)。
共同边界用了（BC.15），没有将固定 \(x\) 的尾趋零界用于增长 \(N_x,x\)。

### 454.5 与临界预算、完整来源及既有递归的关联

每个固定 \(x\) 的面板 \(\mathcal U_x,\mathcal V_x\) 确实属于全部固定 \(\mathcal X_j\)，但它们的共同 \(x\)-范数并不有界。令 \(n_x=\lfloor4x\rfloor\)，有
\(\mathcal U_x(n_x)=\mathcal V_x(n_x)=-Q_x^\mathrm{p}\)；
非零项的下端均大于 \(2x\)。因此由单调 \(W_j\) 和 PNT，
\[
\|\mathcal U_x\|_{\mathcal X_j}
\asymp_j\|\mathcal V_x\|_{\mathcal X_j}
\asymp_j\frac{\sqrt x}{\ell^{j+1}}
\quad(x\to\infty,\ j\text{ 先固定}).
\tag{BC.22}
\]
§395 的可测核定理在 \(\eta\) 上给
\(M_{1/2}(\eta)=\int_0^\infty|\eta(y)|y^{-3/2}dy\le12\)，因此
\(\|J_x^\eta\|_{\mathcal Y_0}\le144/(\sqrt x\log x)\) 对 \(x\ge e\) 成立。
这里 \(M_{1/2}(\eta)\) 是核的 Mellin 绝对矩，绝非实际 Mertens 平方根范数。
对 \(j>0\)，本节只用（BC.8）的固定 \(x,j\) 完整前对偶成员性；不把 \(j=0\) 的共同临界常数推广到带对数权空间。

所以（BC.6）的有界逆与实际 \(1/\ell^2\) 面板响应相容。
本操作将二倍尺度深度作几何求和；§452 的同 β 最大值递归则反复施加卷积逆幂。
二者的真实系数不同，算子恢复成本不提供实际联合相位预算。
完整变换保留总配对，截止与变换不交换时，已经付款的逆范数也不能替代（BC.14）的真实边界。

保持 §453 的同源全补集 \(\mathscr C_x\)，原目标仍精确为
\[
I_\psi(x)=\mathscr C_x-\mathcal A_x
=\mathscr C_x+\mathscr H_x(N_x)+\mathscr T_x(N_x).
\tag{BC.23}
\]
一侧临界下界仍须控制精确 \(\mathscr C_x\ge\mathcal A_x-B/(\sqrt x\log x)\)。
（BC.18）的任一非零主项归一化后都为 \(\sqrt x/\log x\) 量级；
省去负尾会改变这个实际面板的符号，却不构成原完整 \(I_\psi\) 的正性证明。
原单位、原首块补偿和全部窗外来源均由（BC.11）、（BC.23）保留。

**来源与范围。** 先检索并复用 §§395、424、425、427、452、453；固定 \(P=2\) 配对及临界逆范数早已覆盖，未将它们包装成新结论。新承重是（BC.12）–（BC.21）的真实面板截止边界、共同主项及严格符号翻转。解析 \(\gamma_1\) 上界与前段正性估计沿用 §453 已付清的 Laurent 约定、梯形绝对误差和有理对数界。Dirichlet 卷积 Banach 代数沿用 Library/ArithSums/glocknerlucht2011weightedinversion.md 的 Glöckner–Lucht arXiv:1112.0749v2 归属；PNT 沿用 §453 的 Johnston–Yang v2。没有新 RH 判据或全局原创性声明。

本节为解析推导；复用本卷 §§452–453，原有符号临界估计仍未解决。

## 455. 同一真实奇 Möbius 面板的联合临界截止补偿

沿用 §§453–454 的真实核和精确截止边界，同时考虑增长的实数尺度与整数截止。以下估计给出同一面板截止补偿在原 Robin 临界归一化下的共同误差。

### 455.1. 对象、精确边界及来源合同

对实数 \(x\ge e\)，记 \(\ell=\log x\)、\(L=\log2\)，沿用

\[
\eta(y)=\log(\lfloor y\rfloor!)-y\log y+y,
\qquad w(t)=\frac{1+\log t}{t^2\log^2t},
\]
\[
P_x^\eta(s)=\int_x^\infty\eta(t/s)w(t)\,dt,
\quad J_x^\eta(n)=P_x^\eta(n)-P_x^\eta(n+1),
\quad \mathscr D_x(s)=P_x^\eta(s)-P_x^\eta(2s).
\tag{CC.1}
\]

这里 \(s\) 可以为正实数；整数 \(m\) 时有精确完整纤维

\[
\mathscr D_x(m)=\sum_{n=m}^{2m-1}J_x^\eta(n).
\tag{CC.2}
\]

取同一个真实素数面板

\[
\mathcal P_x=\{p\text{ prime}:2x<p\le4x\},\qquad
Q_x^{\mathrm p}=\#\mathcal P_x,\qquad
\mathcal A_x=\sum_{p\in\mathcal P_x}\mathscr D_x(p).
\tag{CC.3}
\]

其真实奇源系数为 \(\mu(p)=-1\)。设

\[
\mathcal U_x(n)=-\#\{p\in\mathcal P_x:p\le n\},\quad
\mathcal L_x(n)=J_x^\eta(n)-J_x^\eta(2n)-J_x^\eta(2n+1),
\]
\[
\mathscr H_x(N)=\sum_{n=1}^N\mathcal U_x(n)\mathcal L_x(n),\qquad
\mathscr E_x(N)=Q_x^{\mathrm p}\mathscr D_x(N+1).
\tag{CC.4}
\]

§454（BC.13）–（BC.14）已经证明，对每个整数 \(N\ge\lceil8x\rceil\)，

\[
\boxed{\mathscr H_x(N)=-\mathcal A_x+\mathscr E_x(N),\qquad
\sum_{n>N}\mathcal U_x(n)\mathcal L_x(n)=-\mathscr E_x(N).}
\tag{CC.5}
\]

补偿项的端点始终是 **\(N+1\) 和 \(2N+2\)**。这一精确身份不是本稿的新结论；下文支付同时增长的 \(x,N\) 下的大小，而不使用固定 \(x\) 的尾趋零来代替共同精度。

使用以下已证明结果与文献：

1. §453（DP.9）–（DP.10）的精确低商积分与完整高商绝对预算；其高商界来自 §429.2 的经典阶乘夹逼，保留实际 \(\eta\)。
2. §454（BC.13）–（BC.14）的同一个真实整数截止与奇端点。
3. Johnston–Yang, *Some explicit estimates for the error term in the prime number theorem*, arXiv:2204.01980v2，2022-04-20 修订版，Theorem 1.1、式（1.3）、印刷页 2。其所有素幂误差为
   \[
   |\psi(t)-t|\le9.39t(\log t)^{1.515}e^{-0.8274\sqrt{\log t}}\quad(t\ge2).
   \tag{CC.6}
   \]
   所需计数误差由该素幂界与有限 Abel 求和导出。

### 455.2. 全高商联合核估计

定义

\[
F(a)=(1+a)\log(1+a)-a=\int_0^a\log(1+t)\,dt\quad(a\ge0).
\tag{CC.7}
\]

因此 \(F(0)=0\)、\(F'(a)=\log(1+a)\)，且 \(F(a)>0\) 对每个 \(a>0\) 成立。

**引理 455.1（共同误差，含完整高商）。** 固定 \(0<\alpha\le\beta<\infty\)。对全部 \(x\ge e\) 及 \(s\ge x\)，若

\[
a=\frac{\log(s/x)}\ell\in[\alpha,\beta],
\]

则有同一个显式常数

\[
K_\beta=\frac32\beta+\frac{15}2+
\frac L2\left[1+\log(1+\beta+L)\right]
\tag{CC.8}
\]

使得

\[
\boxed{\left|s\mathscr D_x(s)-\frac\ell2F(a)\right|\le K_\beta.}
\tag{CC.9}
\]

**证明。** 令 \(r=\log s=\ell(1+a)\)。§453（DP.9）的低商积分为

\[
sP_{x,\mathrm{low}}^\eta(s)
=r\log r+(\ell^{-1}-\log\ell-1)r
+(\ell^{-1}+\ell-1)-r^{-1}.
\]

代入 \(r=\ell(1+a)\) 并逐项整理，精确得到

\[
sP_{x,\mathrm{low}}^\eta(s)=\ell F(a)+a+\ell^{-1}-r^{-1}.
\tag{CC.10}
\]

高商使用同一 \(\eta\) 的全部区间 \(t\ge s\)。由

\[
|\eta(y)|\le1+\log y\quad(y\ge1),\qquad
\int_1^\infty(1+\log y)y^{-2}\,dy=2,
\]

及 \(u^{-1}+u^{-2}\) 在 \(u>0\) 上递减，换元 \(t=sy\) 给

\[
\left|sP_{x,\mathrm{high}}^\eta(s)\right|
\le2(r^{-1}+r^{-2}).
\tag{CC.11}
\]

写 \(sP_x^\eta(s)=\ell F(a)+R_x(s)\)。因为 \(\ell\ge1\)、\(r\ge\ell\)，且 \(0\le\ell^{-1}-r^{-1}\le\ell^{-1}\)，（CC.10）–（CC.11）给

\[
|R_x(s)|\le a+\ell^{-1}+2r^{-1}+2r^{-2}\le a+5.
\tag{CC.12}
\]

在 \(2s\) 上参数恰为 \(a+L/\ell\)，故

\[
s\mathscr D_x(s)
=\ell F(a)-\frac\ell2F(a+L/\ell)+R_x(s)-\frac12R_x(2s).
\tag{CC.13}
\]

由 \(F'=\log(1+a)\) 的单调性，

\[
0\le\ell[F(a+L/\ell)-F(a)]
\le L\log(1+\beta+L).
\]

（CC.12）在两个端点给 \( |R_x(s)|\le\beta+5\)、

\[
|R_x(2s)|\le\beta+L+5.
\]

代入（CC.13）并取绝对值即得（CC.8）–（CC.9）。该估计同时支付了完整 \(s\) 到 \(2s\) 的纤维与全部高商，常数不依赖 \(x,s\)。证毕。

### 455.3. 真实面板计数的误差供应

**引理 455.2。** 当实数 \(x\to\infty\) 时，

\[
Q_x^{\mathrm p}=\frac{2x}\ell+O\!\left(\frac{x}{\ell^2}\right).
\tag{CC.14}
\]

**证明。** （CC.6）与 \(u^{3.515}e^{-0.8274\sqrt u}\to0\) 给

\[
\psi(t)=t+O(t/\log^2t).
\]

对素幂余项用有限层求和与 \(\vartheta(y)\le y\log y\)，得到

\[
0\le\psi(t)-\vartheta(t)
=\sum_{k=2}^{\lfloor\log_2t\rfloor}\vartheta(t^{1/k})
\ll\sqrt t\log^2t=o(t/\log^2t).
\]

所以 \(\vartheta(t)=t+O(t/\log^2t)\)，并有全部 \(t\ge2\) 上的 \(\vartheta(t)\ll t\)。包含素数 2 的精确有限 Abel 求和为

\[
\pi(t)=\frac{\vartheta(t)}{\log t}
+\int_2^t\frac{\vartheta(u)}{u\log^2u}\,du.
\tag{CC.15}
\]

积分由 \(\vartheta(u)\ll u\) 及在 \(\sqrt t\) 分段，界为 \(O(t/\log^2t)\)。故

\[
\pi(t)=\frac{t}{\log t}+O(t/\log^2t).
\]

在精确端点相减，

\[
Q_x^{\mathrm p}=\pi(4x)-\pi(2x)
=\frac{4x}{\ell+2L}-\frac{2x}{\ell+L}+O(x/\ell^2)
=\frac{2x}\ell+O(x/\ell^2).
\]

这证明（CC.14）。普通无误差 PNT 的 \(\sim\) 本身没有被用来声称这个 \(O\) 率。证毕。

### 455.4. 锐的共同临界截止律

**定理 455.3（联合面板补偿）。** 固定 \(0<\alpha\le\beta<\infty\)。令 \(N=N(x)\) 为整数、\(N\ge\lceil8x\rceil\)，写

\[
m=N+1,\qquad a_x=\frac{\log(m/x)}\ell\in[\alpha,\beta].
\tag{CC.16}
\]

则对该范围的全部 \(N,x\) 共同有

\[
\boxed{\mathscr E_x(N)=\frac{x}{N+1}
\left[F(a_x)+O_{\alpha,\beta}(\ell^{-1})\right].}
\tag{CC.17}
\]

进而

\[
\boxed{\sqrt x\ell\,\mathscr E_x(N)
=\frac{x^{3/2}\ell}{N+1}
\left[F(a_x)+O_{\alpha,\beta}(\ell^{-1})\right].}
\tag{CC.18}
\]

**证明。** 引理 455.1 给

\[
\mathscr D_x(m)=\frac\ell{2m}
\left[F(a_x)+\varepsilon_{x,m}\right],\qquad
|\varepsilon_{x,m}|\le2K_\beta/\ell.
\]

引理 455.2 可写为 \(Q_x^{\mathrm p}=(2x/\ell)(1+\delta_x)\)，其中

\[
|\delta_x|\le C_{\mathrm p}/\ell\qquad(x\ge X_{\mathrm p})
\]

的有限常数与阈值不依赖 \(N\)。乘积中 \(2\) 与 \(1/2\) 精确相消。因 \(F(a_x)\le F(\beta)\)，（CC.17）的共同误差常数可取

\[
C_{\alpha,\beta}=C_{\mathrm p}F(\beta)+2K_\beta(1+C_{\mathrm p})
\]

对 \(x\ge\max(e,X_{\mathrm p})\) 使用。乘以 \(\sqrt x\ell\) 得（CC.18）。证毕。

**推论 455.4（在该共同范围内的充要截止尺度）。** 仍假设（CC.16）。则补偿项最终严格为正，并有

\[
\boxed{\sqrt x\ell\,\mathscr E_x(N(x))\longrightarrow0
\quad\Longleftrightarrow\quad
\frac{N(x)+1}{x^{3/2}\ell}\longrightarrow\infty.}
\tag{CC.19}
\]

**证明。** 因 \(F(\alpha)>0\)，对全部充分大 \(x\)，（CC.18）中的中括号介于

\[
\frac12F(\alpha)\quad\text{与}\quad F(\beta)+\frac12F(\alpha)
\]

之间。因此它与 \(x^{3/2}\ell/(N+1)\) 具有两个固定正比较常数。（CC.19）及最终正性随即成立。充要条件只在明确的固定正紧区间合同下主张；没有扩张为任意无约束的 \(N(x)\)。证毕。

**推论 455.5（非零临界补偿常数）。** 对每个固定 \(\lambda>0\)，取

\[
N_\lambda(x)=\left\lceil\lambda x^{3/2}\log x\right\rceil.
\tag{CC.20}
\]

则 \(N_\lambda(x)\ge\lceil8x\rceil\) 最终成立，并且

\[
\boxed{\sqrt x\log x\,\mathscr E_x(N_\lambda(x))
=\frac{F(1/2)}\lambda+
O_\lambda\!\left(\frac{1+\log\log x}{\log x}\right)
\longrightarrow\frac{\tfrac32\log(3/2)-\tfrac12}\lambda>0.}
\tag{CC.21}
\]

**证明。** \(m=N_\lambda+1=\lambda x^{3/2}\ell+O(1)\)，其中整数误差位于 \([1,2)\)。所以

\[
a_x=\frac12+\frac{\log\ell+\log\lambda}{\ell}
+O_\lambda\!\left(\frac1{x^{3/2}\ell^2}\right),
\qquad
\frac{x^{3/2}\ell}m=\frac1\lambda+
O_\lambda\!\left(\frac1{x^{3/2}\ell}\right).
\]

于是 \(a_x\) 最终位于例如 \([1/4,3/4]\)，而 \(F'\) 在此及其固定邻域有界。将以上式代入（CC.18）即得误差与极限。正性来自（CC.7）。证毕。

**推论 455.6（固定幂及对数调整的全部临界情形）。** 固定 \(\lambda>0\)、\(\rho>1\)、\(b\in\mathbb R\)，令

\[
N_{\lambda,\rho,b}(x)=\lceil\lambda x^\rho\ell^b\rceil.
\]

则该截止最终满足 \(N_{\lambda,\rho,b}\ge\lceil8x\rceil\)，且共同付款后的定量式为

\[
\boxed{\sqrt x\ell\,\mathscr E_x(N_{\lambda,\rho,b}(x))
=\frac1\lambda x^{3/2-\rho}\ell^{1-b}
\left[F(\rho-1)+
O_{\lambda,\rho,b}\!\left(\frac{1+\log\ell}{\ell}\right)\right].}
\tag{CC.22a}
\]

由此恰有以下固定参数分类：

| 固定参数范围 | \(\sqrt x\ell\,\mathscr E_x(N_{\lambda,\rho,b}(x))\) 的极限 |
| --- | --- |
| \(1<\rho<3/2\)，任意固定 \(b\) | \(+\infty\) |
| \(\rho=3/2,\ b<1\) | \(+\infty\) |
| \(\rho=3/2,\ b=1\) | \(F(1/2)/\lambda>0\) |
| \(\rho=3/2,\ b>1\) | \(0\) |
| \(\rho>3/2\)，任意固定 \(b\) | \(0\) |

特别地，\(\lambda=1,b=0\) 的固定纯幂截止 \(N_\rho(x)=\lceil x^\rho\rceil\) 满足

\[
\mathscr E_x(N_\rho(x))\sim F(\rho-1)x^{1-\rho},\qquad
\sqrt x\ell\,\mathscr E_x(N_\rho(x))
\sim F(\rho-1)x^{3/2-\rho}\ell.
\tag{CC.22}
\]

故临界归一化补偿在 \(1<\rho<3/2\) 时趋于 \(+\infty\)，在 \(\rho=3/2\) 时仍按正倍数 \(\log x\) 发散，而在 \(\rho>3/2\) 时趋于零。

**证明。** 对每组固定参数，

\[
m=\lambda x^\rho\ell^b+O(1),\quad
a_x=\rho-1+\frac{b\log\ell+\log\lambda}{\ell}
+O_{\lambda,\rho,b}(x^{-\rho}\ell^{-b-1}).
\]

因 \(\rho>1\)，整数误差趋于相对零，且 \(a_x\to\rho-1>0\)。可取固定正紧区间，使（CC.18）的误差共同成立；\(F'\) 在其固定邻域有界，给

\[
F(a_x)=F(\rho-1)+O_{\lambda,\rho,b}((1+\log\ell)/\ell).
\]

同时

\[
\frac{x^{3/2}\ell}{m}
=\frac1\lambda x^{3/2-\rho}\ell^{1-b}
\bigl[1+O_{\lambda,\rho,b}(x^{-\rho}\ell^{-b})\bigr].
\]

最后这个相对整数误差对固定 \(\rho,b\) 是 \(o(\ell^{-1})\)，故（CC.18）给（CC.22a）。因 \(F(\rho-1)>0\)，幂 \(x^{3/2-\rho}\) 压过任意固定对数幂；在 \(\rho=3/2\) 时由 \(\ell^{1-b}\) 的极限得到表中三种情形。（CC.22）是其特例。证毕。

### 455.5. 精确校正观测量与完整实际缺口

面板校正读数

\[
\widehat{\mathscr H}_x(N)=\mathscr H_x(N)-\mathscr E_x(N)=-\mathcal A_x
\tag{CC.23}
\]

在全部 \(N\ge\lceil8x\rceil\) 精确保持原面板值。这里保留 **精确 \(\mathcal A_x\)**，不将其 \(C_{\rm pair}/\ell^2+o(\ell^{-2})\) 渐近替换进临界公式。§454 的 \(N\asymp x\) 正前段及负全尾已经表明补偿不能在该尺度省略；（CC.21）进一步证明，即使采用 \(x^{3/2}\log x\) 的截止，省略后仍有非零原临界误差。

为明确完整来源，复用 §453（DP.26）–（DP.27）的自然奇源补集

\[
\mathscr C_x=\lim_{R\to\infty}
\sum_{\substack{m\le R,\ m\text{ odd}\\m\notin\mathcal P_x}}
\mu(m)\mathscr D_x(m),\qquad
I_\psi(x)=\mathscr C_x-\mathcal A_x.
\tag{CC.24}
\]

这一已有极限保留单位 \(m=1\)、全部其余奇素数、合数、面板两侧及完整远尾；每份奇源包含完整偶倍纤维。它恢复 §424 的同一实际 Mertens 配对，原单位首块与原 \(\beta_d=\log(1-(-q)^d)\)、\(q=(3-\sqrt5)/2\) 的全部纤维及运输补偿均来自已有完整合同。上文估计使用全部高商的实际 \(\eta\)，没有新增任何 \(\beta\) 截断。

因此含完整补集的精确观测量为

\[
\boxed{\mathscr C_x+\widehat{\mathscr H}_x(N)
=\mathscr C_x+\mathscr H_x(N)-\mathscr E_x(N)=I_\psi(x).}
\tag{CC.25}
\]

如果省略唯一显示的面板截止校正，则同一完整来源读数变成

\[
\mathscr C_x+\mathscr H_x(N)=I_\psi(x)+\mathscr E_x(N).
\tag{CC.26}
\]

故在（CC.20）的截止上，这个错误读数与目标之间的临界归一化差精确趋于 \(F(1/2)/\lambda>0\)。这不是关于真实完整 \(I_\psi(x)\) 符号的推断，而是同一来源上可量化的观测偏差。

原一侧目标所需的剩余供应仍然是：存在固定 \(B\ge0\)，对全部充分大实数 \(x\)，

\[
\boxed{\mathscr C_x\ge\mathcal A_x-\frac B{\sqrt x\log x}.}
\tag{CC.27}
\]

（CC.27）与 \(\sqrt x\log x\,I_\psi(x)\ge-B\) 精确等价。既有无条件 \(\mathscr C_x=\mathcal A_x+O(\ell^{-4})\) 不支付该精度；本稿的有限面板截止律也不提供完整实际 \(M/O\) 的平方根对数范数或全部来源的临界抵消。若进一步把 \(\mathscr C_x\) 改为有限实际补集，必须另外控制那个**同一来源**的完整截断余项，不能用本稿的面板补偿代替。

### 455.6. 全实际 \(O\) 的有限来源读数及精确剩余供应

前节的 \(\mathscr C_x\) 是完整补集。若要求一个有限来源读数，须使用实际

\[
O(n)=\sum_{\substack{m\le n\\m\text{ odd}}}\mu(m),\qquad O(0)=0,
\quad \mathscr F_x(N)=\sum_{n=1}^NO(n)\mathcal L_x(n),
\]

并置

\[
\mathscr C_{x,N}=
\sum_{\substack{m\le N,\ m\text{ odd}\\m\notin\mathcal P_x}}
\mu(m)\mathscr D_x(m).
\]

对同一整数 \(N\ge\lceil8x\rceil\)，有限 Abel 求和与
\(\mathcal L_x(n)=\mathscr D_x(n)-\mathscr D_x(n+1)\) 给

\[
\boxed{\mathscr F_x(N)+O(N)\mathscr D_x(N+1)
=\sum_{\substack{m\le N\\m\text{ odd}}}\mu(m)\mathscr D_x(m)
=\mathscr C_{x,N}-\mathcal A_x.}
\tag{CC.28}
\]

证明只用
\(O(n)-O(n-1)=\mu(n)\mathbf1_{n\text{ odd}}\)，包括 \(n=1\)，以及全部面板素数已满足 \(p\le N\)。这里校正的是**全实际 \(O(N)\)** 的截止边界；它不是面板的 \(-Q_x^{\mathrm p}\)，因而不能将（CC.19）–（CC.22a）的面板大小直接移植到这个全实际边界。

定义同一自然奇源截止的剩余量

\[
\mathscr R_x(N)=\mathscr C_x-\mathscr C_{x,N}
=\lim_{R\to\infty}
\sum_{\substack{N<m\le R\\m\text{ odd}}}\mu(m)\mathscr D_x(m).
\tag{CC.29}
\]

这个固定 \(x,N\) 的极限存在性直接来自 §453（DP.16）；没有推导任何增长 \(x,N\) 的共同临界误差。把（CC.28）补全得到精确完整读数

\[
\boxed{\mathscr F_x(N)+O(N)\mathscr D_x(N+1)+\mathscr R_x(N)
=\mathscr C_x-\mathcal A_x=I_\psi(x).}
\tag{CC.30}
\]

因此有限来源版本的原目标仍精确要求

\[
\mathscr C_{x,N}+\mathscr R_x(N)
\ge\mathcal A_x-\frac B{\sqrt x\log x}
\tag{CC.31}
\]

对全部充分大实数 \(x\) 成立，且 \(N=N(x)\) 为所选同一截止。支付（CC.31）需要同源完整剩余 \(\mathscr R_x(N)\) 的联合抵消；固定 \(x\) 的收敛及本稿的有限面板截止律都不提供这一供应。完整观测量（CC.30）保留单位、每份已触发来源的全部纤维、全部剩余来源及精确 \(\mathcal A_x\)。

联合面板估计（CC.17）与全实际来源的有限校正身份（CC.30）作用于不同系数：前者控制面板大小，后者保留实际奇前缀与全部剩余来源。原临界下界仍要求（CC.31）的同源剩余估计。
