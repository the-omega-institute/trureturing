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
