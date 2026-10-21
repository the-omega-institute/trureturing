# FIB 分析前沿接口

本卷记录与 FIB ATOM、Robin 判据和现有 sextic transport 直接相交的外部解析输入。它只记录接口、假设和未闭合义务，不重复仓内已有的 CA/SA 归约、Robin 判据或 signed packet 推导。

## 追加锚（本行以下为增补区）

## 441. de Faveri 固定阶字符大筛的非重复接口

截至 2026 年 10 月 10 日，定向检索得到 Alexandre de Faveri 的 [*Optimal large sieve for fixed order characters](../../../Library/Analytic/faveri2026fixedorder.md)，arXiv:2610.04045v1。仓内已有章节已经覆盖 CA/SA 归约、Lagarias/Nicolas 判据、有限 Robin 证书、平滑正性和 Möbius 有符号障碍；这份来源提供的是一个不同的解析输入，因此这里只记录它是否能接到当前尚未闭合的完整 signed joint correlation，不重写那些已有路线。

该文 Theorem 1.1 对含 $n$ 次单位根的数域中的 $n$ 阶 Hecke 字符，在 $n$ 次幂自由理想参数和内变量上给出

$$
\Theta_n(A,B)
\ll_{\varepsilon}
(AB)^\varepsilon
\left(A+B+A^{1-1/n}B^{2/n}+A^{2/n}B^{1-1/n}\right).
$$

在 Eisenstein 域和 $n=6$ 时，形式上覆盖当前 sextic 字符背景。活动载体

$$
a=A_1R_2^2R_3^3R_4^4R_5^5
$$

若五个 radical 确实是同一实际分解中的互素平方自由理想，则 $a$ 的每个素理想指数至多为5，因而满足该定理的 sixth-power-free 参数条件。冻结 $R_2,R_3,R_4,R_5$、只对 $A_1$ 应用大筛，结合已有列质量后产生四个形式尺度

$$
R^2,\qquad A_1R,\qquad A_1^{5/6}R^{4/3},\qquad A_1^{1/3}R^{11/6}.
$$

沿用当前载体预算，四项的最坏源指数为

$$
\max\left\{\frac5{12},\frac49,\frac{19}{36},\frac49\right\}
=\frac{19}{36}<\frac23.
$$

这只说明一个可能的幂次供应商；它还没有成为完整估计。必须先完成以下同源桥接：

1. 用 sextic reciprocity 把项目的 $\chi_p(a)$ 逐项转成该文的 $\chi_a(p)$，并保留有限 ray 相位、共轭方向、单位因子和所有零延拓；
2. 把原始固定因子和移动 mask 纳入实际行参数，再证明其 sixth-power-free 分解，而不是把 radical 的乘积误当成混合幂参数；
3. 证明 Möbius 系数、共同 smooth profile、有限 mask 与行权重可以在该 $L^2$ 大筛中固定或分解，且不支付未登记的多项式损失；
4. 在完整 parent pair 或完整 signed restoration 上使用该估计，保留所有 secondary-$L$ partners、tails 和 common kernels；
5. 对冻结的其余四个载体在同一实际实现上求和，不能把分别可达的五个最优值拼成一个共同构型。

因此，$19/36$ 是条件性的 source-interface 计算，不是新的 Robin 定理，更不是 RH 证明。若上述五项中任一项不能闭合，应把失败记录为该接口的边界，转而寻找能切开同一 source fiber 的新关系；继续重做 CA 支撑线、Robin 等价式或已有有限枚举不会推进当前缺口。

## 追加锚（本行以下为增补区）

## 442. Liu v1 的 quasi-RH 零自由半平面改进与 FIB 接口

2026 年 10 月 8 日提交的 Baiying Liu 预印本 v1 [*Slightly improved zero-free half-planes for the quasi-Riemann hypothesis*](../../../Library/Analytic/liu2026quasirh.md)，arXiv:2610.12234v1，给出仓内 OpenAI 7/8 路线的第一阶段参数改进。其 Theorem 21.1 对 $\mathbb Q(\sqrt{-3})$ 上全部有限阶 Hecke $L$ 函数以及全部 Dirichlet $L$ 函数给出

$$
\beta_*\le B_{\mathrm{new}}
=\frac{1507-2\sqrt{921}}{1653}
=0.874957069799\ldots,
$$

允许 $s=1$ 的主极点且不包含边界。论文先给出 $B_r=34999/40000$ 的有理改进，再同时调节 cubic-theta 论证的长度差与选中素数总长，得到上述代数值；它沿用 OpenAI 7/8 证明的零检测、矩估计、轮廓和 Dirichlet 转移，不是新的 Robin 判据。

这项结果对当前 FIB 路线的直接含义是：可以把严格无零输入从 $\Re s>7/8$ 候选地推进到 $\Re s>B_{\mathrm{new}}$，但必须一起运输 $b,\ell,l_x,l_y,h$、正槽矩容量、主项与非主项的端点不等式以及外部轮廓高度。现有 [OpenAI 来源卡](../../../Library/Analytic/openai2026quasirh.md) 中的 $7/8$ 估计带有固定参数合同，不能只把常数文字替换成 $B_{\mathrm{new}}$。

即使该外部预印本的 Lean 形式化经过独立迁移，$B_{\mathrm{new}}>1/2$ 仍不会提供临界线结论；它也没有给普通整数 Möbius 的平方根消去、完整 signed Robin 尾项或 FIB 来源到约数和的保真映射。因此它改善的是零自由辅助输入，不闭合 Robin/RH 的核心联合预算。仓内未重复 OpenAI 7/8 的推导，只记录这个参数优化及其迁移义务。

## 443. Liu v1 界对现有 FIB packet 门槛的精确影响

把新界与仓内已有的 packet 预算放在同一坐标中，得到

$$
\frac78-B_{\mathrm{new}}
=0.0000429302008312599816599930411207758482\ldots.
$$

现有无槽低端估计要求

$$
\beta>\frac23+\frac{5a}{6}.
$$

取当前固定示例 $a=1/10$，门槛为 $3/4$；因此 $B_{\mathrm{new}}$ 与原 $7/8$ 都位于同一可用侧，微小改善没有改变这条估计的适用分区。现有正槽容量路线的联合门槛为

$$
\frac{19}{64}+\frac{11}{16}=\frac{63}{64}=0.984375,
$$

严格高于 $B_{\mathrm{new}}$，所以新零自由界不能解锁该路线。临界线读数仍留下无槽缺口 $(1+5a)/6$；这是一份当前低端上界的未支付预算，不是对真实消去的反例。

因此，Liu 的参数优化在本项目中应当作为可运输的外部零自由输入保存；它没有给出新的 FIB packet 余量，也不改变完整 signed Robin 尾项仍未闭合的状态。继续重复 CA 支撑线、7/8 证明或有限 Robin 检查不会消费这个缺口；需要的是新的同一来源联合估计或能降低上述 packet 门槛的真实解析输入。

## 追加锚（本行以下为增补区）

## 444. 规范 FIB 窗口上的低素因子数筛适用范围

**定义 444.1（同一实际窗口）。** 使用 $F_0=0,F_1=1$ 的 Fibonacci 数列，令

$$
I_r=\left[\left\lceil\frac{F_r}{10}\right\rceil,
\left\lfloor\frac{F_r}{5}\right\rfloor\right]\cap\mathbb Z,
\qquad N_{r,g}=1+F_rg.
$$

$\omega(n)$ 表示正整数 $n$ 的不同素因子数。旧卷 §258.6 的低 $\omega$ Robin 筛只适用于满足该筛上界的实际 $N_{r,g}$。

**命题 444.2（窗口联合族不满足固定的 $\omega$ 截断）。** 对每个整数 $k\ge1$，有无穷多个素数指标 $r$ 及 $g\in I_r$，满足 $N_{r,g}>5040$ 与 $\omega(N_{r,g})\ge k$。

**证明。** 选取 $k$ 个互异且大于5的素数 $q_1,\ldots,q_k$，令 $Q=\prod_iq_i$。直接使用经典 Fibonacci 进入秩判据

$$
q_i\mid F_r\quad\Longleftrightarrow\quad z(q_i)\mid r;
$$

其来源与适用条件见 [Lengyel, Section 3, Theorem A](../../../Library/Factorization/lengyel1995fibonacciorder.md)。$F_1=F_2=1$ 给 $z(q_i)>1$。若 $r$ 为大于全部 $z(q_i)$ 的素数，则 $z(q_i)\nmid r$，故每个 $q_i$ 都不整除 $F_r$。

由经典中国剩余定理，存在唯一的模 $Q$ 剩余类 $g_r$，使 $F_rg_r\equiv-1\pmod{q_i}$ 对全部 $i$ 成立。这里只复用 CRT，不另立固定模数仿射族的无界性定理。对连续整数窗口，有

$$
|I_r|=\left\lfloor\frac{F_r}{5}\right\rfloor
-\left\lceil\frac{F_r}{10}\right\rceil+1
\ge\frac{F_r}{10}-1.
$$

因此 $F_r\ge10(Q+1)$ 时，该窗口含至少 $Q$ 个连续整数，必含某个 $g\equiv g_r\pmod Q$。对这个同一实际 $g$，全部 $q_i$ 都整除 $N_{r,g}$，于是 $\omega(N_{r,g})\ge k$。Fibonacci 数沿素数指标趋于无穷，故上述两个有限阈值对所有充分大的素数 $r$ 同时成立；再增加一个有限阈值即可保证 $N_{r,g}>5040$。素数指标有无穷多个，结论成立。$\square$

这里的窗口应用是本仓综合推导（`repo-derived`）；CRT 和 Fibonacci 进入秩判据是已知工具。结论没有判断这些高 $\omega$ 点的 Robin 符号，也没有否定对每个实际整数成立的 Robin 不等式。它只排除以固定低素因子数筛覆盖全部规范窗口的充分条件；同一实际候选的 CA/SA 来源保持或完整有符号余量仍需独立估计。

## 追加锚（本行以下为增补区）

## 445. Liu v2 的迭代边界更新

Liu 的 [v2](../../../Library/Analytic/liu2026quasirh.md) 将最终边界从一次代数优化的

$$
B_{\mathrm{alg}}=\frac{1507-2\sqrt{921}}{1653}
=0.874957069799168740\ldots
$$

推进到迭代极限

$$
B_{\mathrm{new}}=\frac{18\xi_{\mathrm{new}}+7}{18\xi_{\mathrm{new}}+9}
=0.874957019420098946\ldots,
$$

其中 $\xi_{\mathrm{new}}\in(0.38858,0.38859)$ 是

$$
1188\xi^3-2160\xi^2+171\xi+190=0
$$

在该区间内的唯一根。v2 的新内容是把无权第四矩的可用范围推进到
$13/18\le\kappa\le1$，再以 $\kappa=2B_{\mathrm{new}}-1$ 迭代长度参数；它不是只替换旧常数。

相对原 $7/8$，可用侧的数值余量变为

$$
\frac78-B_{\mathrm{new}}
=0.000042980579901054\ldots,
$$

比 v1 的 $0.000042930200831260\ldots$ 增加

$$
5.0379069794\times10^{-8}.
$$

这仍不改变仓内 packet 的适用分区：已有无槽门槛 $3/4$ 与正槽联合门槛 $63/64$ 都不因这一级微小改进而跨过边界。因而 v2 应更新外部零自由输入的版本和常数，但不产生新的同一来源 signed Robin 估计；继续重复 v1 的零检测推导不会推进当前缺口。

## 446. Ye 短条带零密度与 FIB 相位接口

Yangbo Ye 的 [*Zero density in short strips and short-interval bounds toward Hypothesis S*](../../../Library/Zeros/ye2026shortstripdensity.md)，arXiv:2610.15989v1，给出一个不同于仓内 Guth--Maynard 全局大值输入的短条带接口。其 Theorem 1.2 对 $2/3\le a\le1$ 的 zeta 零点计数给出

$$
N_\zeta(\sigma;T,T+T^a)
\ll_{a,\varepsilon}T^{aB(\sigma)+\varepsilon},
$$

其中在 $7/10\le\sigma\le4/5$ 的分支为

$$
B(\sigma)=\frac{15(1-\sigma)}{3+5\sigma}.
$$

Theorem 1.3 进一步对

$$
\sum_n\Lambda(n)e(\alpha n^\beta)\,\varphi((n-K)/K^\delta)
$$

给出带显式频率 $m^{-1/2}$ 代价的平滑幂节省，zeta 应用的最小长度阈值为 $\delta>2/3$。

这条输入目前不能接到 FIB Robin 主线：仓内五窗相位是黄金递归／双嵌入读出，尚无保持系数、平滑权重和同一实际 $N_*$ 的映射到 $e(\alpha n^\beta)$ 的定理；而短条带零密度本身也不提供全部 prime powers 的 signed Robin 余项。因此它是可运输的外部解析供应商和明确的接口缺口，不是新的 Robin 估计或 RH 证明。继续重做已有短区间素数计数不会消费这一缺口，必须先建立 FIB 相位到该振荡和的同源桥。

## 447. Sang 对 $7/8$ 零自由边界的进一步改进

Hejian Sang 的 [*Refining the $7/8$ zero-free half-plane for Hecke and Dirichlet $L$-functions*](../../../Library/Zeros/sang2026seveneighths.md)，arXiv:2610.15291v1（2026 年 10 月 11 日），是 Liu v2 之后尚未记录的同族新输入。它假设最近 $7/8$ 结果的解析输入，对 $\mathbb Q(\sqrt{-3})$ 上有限阶 Hecke $L$ 函数及其 Dirichlet 转移给出

$$
B_{\mathrm{Sang}}=\frac{8748867}{10000000}=0.8748867.
$$

相对 $7/8$ 的可用侧余量为

$$
\frac78-B_{\mathrm{Sang}}=0.0001133,
$$

比仓内 Liu v2 的 $0.874957019420098946\ldots$ 再低约
$0.000070319420098946$。摘要所述改进来自放宽直接估计并对反射分子使用放大的第一矩，仍以既有第四矩输入为前提；它不是临界线结论。

这条更小的零自由边界不能直接替换现有 FIB packet 的 $7/8$ 参数。若要运输，必须同时重算长度参数、矩范围、反射项、轮廓高度和每个端点不等式；即使运输成功，当前 packet 的无槽缺口、同一实际候选的完整 signed Robin 预算以及 FIB 地址到约数和的保真映射仍未支付。因此这里记录的是一个新外部参数供应商，不重复 Liu 或 OpenAI 的零检测推导，也不把它当作 Robin 不等式或 RH 的证据。

对当前无槽门槛

$$
\beta>\frac23+\frac{5a}{6},
$$

可以直接反解其允许的最大短区间指数：

$$
a<\frac65\left(\beta-\frac23\right).
$$

因此 Sang 的边界给出

$$
a<0.24986404,
$$

而 Liu v2 给出约 $a<0.2499484233$，原始 $7/8$ 给出 $a<1/4$。现有示例 $a=1/10$ 离三者都很远；这项改进没有打开新的 packet 分区，只精确量化了尚未支付的参数余量。

## 448. Tenenbaum--Wang 的大 friable 成分计数

Gérald Tenenbaum 与 Xiangyu Wang 的 [*On integers whose friable component is large*](../../../Library/Scale/tenenbaumwang2026largefriablecomponent.md)，arXiv:2609.37507v2（2026 年 10 月 11 日），给出一个与当前稀疏候选计数相邻、但量词不同的最新输入。令 $n_y$ 为 $n$ 的最大 $y$-光滑因子，

$$
\Theta(x,y,z)=\#\{n\le x:n_y>z\},
\qquad \nu=\frac{\log z}{\log y}.
$$

其定理 1 在

$$
\max\{2,\log z\}\le y\le z\le x/2
$$

上一致给出

$$
\Theta(x,y,z)
=x\exp\!\left(-\nu\log\!\bigl(\nu\log(3\nu)\bigr)+O(\nu)\right).
$$

这条估计可以直接接到当前的同一候选。对

$$
N=uv=1+F_rg,
\qquad v\mid C,
\qquad Cu\equiv v\pmod {F_r},
\qquad E=\log(uv),
$$

令 $g_0=\gcd(N,C)=C/v$。若 $C$ 的所有素因子不超过 $y$，则 $g_0$ 是 $N$ 的 $y$-光滑因子，因此

$$
N_y\ge g_0=\frac Cv,
\qquad E\le L\Longrightarrow N_y\ge Ce^{-L}.
$$

所以在

$$
\max\{2,\log(Ce^{-L})\}\le y\le Ce^{-L}\le x/2
$$

等参数条件成立时，原始窗口内的同一候选满足

$$
\#\{N\text{ in the window}:E\le L\}
\le
\min\left\{\tau(C),\Theta\left(x,y,Ce^{-L}\right)\right\}.
$$

左侧仍保留移动 Fibonacci 同余；这里没有把不同候选分别优化后拼接。这是本来源对当前稀疏层的真实新增接口。

它仍只控制候选数量，不估计同一 $N$ 的完整 prime-power 权重、$D^*(a)$ 或 signed Robin tail $H_a$。因此它缩小了异常集合的计数问题，但没有关闭 Robin 的联合预算，也不构成 Robin 不等式或 RH 证明。

### 448.1 现有尺度下的条件性比较

这条来源不能直接替换 (TC.11)。若另有一个尚未证明的同源桥同时给出

$$
\log C=a+O\!\left(\frac a{\log a}\right),
\qquad N_y\ge C e^{-L},
\qquad L=O(a^{3/4}),
$$

并且 $C e^{-L}\le X_+/2$，可以形式上取 $y\asymp a$、$z=C e^{-L}$。此时

$$
 \nu=\frac{\log z}{\log y}
 =\frac{a-L+O(a/\log a)}{\log a},
$$

从而

$$
 \nu\log\!\bigl(\nu\log(3\nu)\bigr)
 =a-L+O\!\left(\frac a{\log a}\right).
$$

在 $\log X_+=a+O(1)$ 的同一附加尺度下，Tenenbaum--Wang 的人口界至多给出

$$
\log\Theta(X_+,y,z)=O\!\left(\frac a{\log a}\right),
$$

与当前精确同余计数的

$$
\log\tau(C)=O\!\left(\frac a{\log a}\right)
$$

同阶。这里的三项附加条件尚未由 FIB/CA 接口证明；即使它们都成立，也只说明人口层没有新的渐近量级，仍未支付同一候选的 signed Robin tail。要取得实质推进，必须得到常数级改进并保留同余，或直接建立联合有符号估计。

## 449. Fibonacci 尺度采样的零相位接口

当前 FIB 几何真正能接到 Robin 显式公式的地方，是尺度采样，而不是把组成层的四相标签直接当成零点谱。取固定 $c>0$，使用 $F_0=0,F_1=1$ 的 Fibonacci 数列，并令

$$
x_r=cF_r.
$$

这里的 $x_r$ 是把 FIB 长度直接送入显式公式的解析采样尺度；实际候选的 Robin 时钟是 $A=\log(1+F_rg)$。当 $g$ 随窗口变化时，二者没有自动相等，必须另证 $g$ 的范围和同一来源桥。

特别地，在标准同尺度窗口

$$
F_r/10\le g\le F_r/5,
$$

有

$$
\log(1+F_rg)=2r\log\varphi+O(1),
\qquad
\log\log(1+F_rg)=\log r+O(1).
$$

所以若显式公式的变量取实际 Robin 时钟 $x=A$，其零项在该窗口上的相位是 $\gamma\log r+O(1)$，而不是 $\gamma r\log\varphi+O(1)$。只有把 $x$ 本身选成与 $F_r$ 成比例的外部解析尺度时，下面的线性黄金相位才直接出现。这个区别是 FIB 地址到 Robin 时钟桥接中的实质义务。

由

$$
F_r=\frac{\varphi^r-\psi^r}{\sqrt5},
\qquad \psi=-\varphi^{-1},
$$

得到

$$
\log x_r=r\log\varphi+\log\frac c{\sqrt5}+O(\varphi^{-2r}).
$$

因此，对固定的非平凡零点 $\rho=\beta+i\gamma$，有

$$
x_r^{\rho-1}
=\left(\frac c{\sqrt5}\right)^{\rho-1}
  \varphi^{r(\rho-1)}
  \left(1+O_\rho(\varphi^{-2r})\right).
$$

它的幅度和相位分别满足

$$
\left|x_r^{\rho-1}\right|
\asymp_{c,\rho}x_r^{\beta-1},
\qquad
\arg x_r^{\rho-1}
=\gamma r\log\varphi+O_{c,\rho}(1).
$$

Polak 的 signed-tail 分解以及 Broadbent--Fiori--Kadiri--Ng--Wilk 的显式公式都包含

$$
\frac{\log x+1}{\log^2x}
\sum_\rho\frac{x^{\rho-1}}{\rho(\rho-1)}
$$

这一零项。故在 Fibonacci 尺度上，单个固定零的首项系数具有

$$
\text{幅度}\asymp
\frac{x_r^{\beta-1}}{\log x_r},
\qquad
\text{相位步长}\approx\gamma\log\varphi.
$$

这给出一个精确的尺度比较：选定 CA 源所需的充分条件是

$$
I_\psi(A)\ge-
\frac{D_{\rm lb}(A)}{\sqrt A\log A},
$$

而若存在 $\beta>1/2$ 的零，单个零的未抵消幅度相对于 $A^{-1/2}/\log A$ 多出因子 $A^{\beta-1/2}$。这只是显式公式中的单零尺度分析；其余零、积分项和共轭配对可能发生相消，所以它不能单独排除离线零，也不能单独证明 Robin。

同样，组成层的四相操作

$$
C=MJ,
\qquad
C:(x_+,x_-)\longmapsto(\varphi x_-,\psi x_+)
$$

交换的是黄金双嵌入的扩张与收缩通道。它没有把实数尺度 $x_r$ 变成四个复尺度，也没有已证的映射

$$
C^k\longmapsto e^{ik\pi/2}
$$

作用于 $x^{\rho-1}$ 的零点相位。因此，四相闭包不能直接替代对
$e^{i\gamma r\log\varphi}$ 的相位平均。

要把这条接口推进成 RH 证明，至少还需一个同一实际来源上的桥接定理，满足以下之一：

1. 证明 FIB/CA 选定尺度上的完整零和具有可控的正性或无抵消下界；
2. 证明该尺度序列的相位平均保留全部零重数、积分项和 prime-power 修正，并给出 $A^{-1/2}/\log A$ 级的余项；
3. 直接给出选定实际候选的 signed $I_\psi(A)$ 下界。

当前文献和仓内接口均未提供这些条件。这个尺度采样关系因此是可复用的解析接口，不是 RH 证明或新的零点估计。

## 450. 全局 PNT 误差可以支付 theta 前提，但支付不了平方根级 signed 预算

上一节的缺口还可以与
`D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation` 的实际前提逐项对照。
令

$$
L=\log A,
\qquad
w(L)=\frac{L^{3/5}}{(\log L)^{1/5}}.
$$

Fiori--Jaskari 的全局估计，在固定紧比例区间

$$
0.99A\le t\le1.98A
$$

上取任意略小于其指数常数的 $d>0$ 后，给出一个充分大的起点以后的一致形式

$$
|\psi(t)-t|\le C A e^{-d w(L)}.
$$

这里把比例区间的常数吸收到 $C$ 和较小的 $d$ 中；这一步只是在已有
Fiori--Jaskari 估计上作紧比例区间的单调化，不是新的 PNT 供应。
由于

$$
0\le\psi(t)-\vartheta(t)
 =\sum_{k\ge2}\vartheta(t^{1/k})
 \ll\sqrt t\log t,
$$

且 $w(L)=o(L)$，同一范围内也有

$$
|\vartheta(t)-t|\le C' A e^{-d' w(L)}
$$

对某个 $0<d'<d$ 成立。于是可取

$$
\varepsilon_A=e^{-d'w(L)/2},
\qquad
H_A=2C'Ae^{-d'w(L)/2}.
$$

对任意 $u<v$ 满足

$$
0.99A\le u<v\le1.98A,
\qquad v-u\ge H_A,
$$

有

$$
\begin{aligned}
\vartheta(v)-\vartheta(u)
&\ge(v-u)-2C'Ae^{-d'w(L)}\\
&\ge(1-\varepsilon_A)(v-u).
\end{aligned}
$$

因此，Fiori--Jaskari 确实可以在未知但有限的起点以后供应

$$
\operatorname{ThetaIncrementLower}(0.99A,H_A,\varepsilon_A).
$$

这澄清了一个此前容易混淆的事实：`ThetaIncrementLower` 本身不是当前的真正障碍，
而是可以由全局 PNT 误差支付的中间接口。

若固定 $c=1+\delta$，其中 $0<\delta\le1/100$，则

$$
\operatorname{bandVolume}(A,c)\asymp\frac{\delta^2}{L},
$$

而 $H_A/(\delta A)\to0$，所以 `shortAllowance` 的实际尺度为

$$
O\left(\frac{e^{-d'w(L)}}{L}\right),
$$

并且

$$
\varepsilon_A\operatorname{bandVolume}(A,c)
=O\left(\frac{e^{-d'w(L)/2}}{L}\right).
$$

代入已有的有限补偿定理，得到的确是“几乎全部 band volume 都由实际
$\Lambda$ 原子支付”的渐近补偿。这一结论保留了 prime powers 和右闭端点，
所以比只用普通素数人口计数更强；但它仍只控制该有限 centered kernel。

它不能支付当前 Robin 比较所要求的平方根级 signed 余项。所需尺度为

$$
\frac1{\sqrt A\log A},
$$

而上述供应器能给出的统一误差尺度至多落在

$$
\frac{e^{-d'w(L)}}{\log A}.
$$

两者的上界比为

$$
\sqrt A\,e^{-d'w(L)}\longrightarrow\infty,
$$

因为 $w(L)=o(L)$。这是“可支付的 theta 前提”和“不可支付的 signed Robin
预算”之间的严格尺度分界：前者已由现有文献覆盖，后者仍需要同一实际
FIB/CA 来源上的平方根级有符号估计。

所以继续改进普通 PNT 或重复建立 `ThetaIncrementLower` 不会推进 RH 主线。
下一项真正新增的结果必须是以下之一：把该 centered kernel 证明地映射到
原始 $I_\psi(\log N)$ 并取得平方根级下界，或者直接对同一实际候选给出

$$
I_\psi(\log N)\ge-
\frac{D_{\rm lb}(\log N)}{\sqrt{\log N}\log\log N}.
$$

本节是接口尺度分析，不是 RH 或 Robin 的新证明。

## 451. centered 补偿核是膨胀差分，不是 $I_\psi$ 本身

还需要把有限补偿定理的核与 Robin 比较中使用的 signed tail 区分开。
令

$$
E(t)=\psi(t)-t,
\qquad
k(t)=\frac{1+\log t}{t^2(\log t)^2},
\qquad
I_\psi(A)=\int_A^\infty E(t)k(t)\,dt.
$$

取 $c>1$。在没有端点跳跃的开区间上，已有定义直接给出

$$
\frac{d}{dt}\left[c^{-1}\operatorname{maxKernel}(A,t/c)\right]
=-\frac{1+\log(t/c)}{t^2(\log(t/c))^2},
$$

以及

$$
\frac{d}{dt}\operatorname{maxKernel}(A,t)=-k(t),
$$

$$
\frac{d}{dt}\frac1{t(\log t)^2}
=-\frac{\log t+2}{t^2(\log t)^3}.
$$

因此，对 `finiteResponse` 作 Stieltjes 分部积分时，在把已经单独记录的
$A$ 处跳跃、右端 $R$ 项和 `smoothBoundary` 分开以后，centered 核的未抵消
高分支贡献恰为（这里保留 dilation 定义中的 $c^{-1}$ 归一化）

$$
\boxed{
\frac1c\int_A^\infty E(cs)k(s)\,ds
-I_\psi(A)
-(c-1)J_2(A),
}
$$

其中

$$
J_2(A)=
\int_A^\infty E(t)\frac{\log t+2}{t^2(\log t)^3}\,dt.
$$

第一项来自 $t=cs$ 的换元：在 $t>cA$ 上，膨胀核的导数是

$$
-\frac{1+\log(t/c)}{t^2(\log(t/c))^2},
$$

而 $dt=c\,ds$ 与 dilation 前的 $c^{-1}$ 恰好留下前式中的 $1/c$。
因此换元后被积的误差仍变成 $E(cs)$，并没有只改变积分下限。更明确地，若

$$
D_c(A):=\frac1c\int_A^\infty E(cs)k(s)\,ds-I_\psi(A),
$$

则对 $c>1$ 有保留端点的精确分解

$$
\boxed{
D_c(A)
=-\int_A^{cA}E(t)k(t)\,dt
+\int_{cA}^\infty E(t)
\left[
\frac{1+\log(t/c)}{t^2(\log(t/c))^2}
-k(t)
\right]dt.
}
$$

所以一般没有

$$
\frac1c\int_A^\infty E(cs)k(s)\,ds=I_\psi(cA).
$$

这不是记号差异，而是来源不同：右边只改变积分下限，左边改变了同一实际
误差函数的取值。有限 $R$ 时的右端项和 $A$ 处跳跃必须与
`finite_signed_response_identity` 保留的 `smoothBoundary` 一起记账；把它们
删掉会改变原命题。

于是已有 `ThetaIncrementLower` 接口最多能控制上述膨胀差分的一个有限版本，
而 Nicolas/Broadbent--Fiori--Kadiri--Ng--Wilk 的 signed 公式控制的是
$I_\psi(A)$。从前者得到后者至少还需要一个同源的 dilation-correlation 估计，
同时控制上述区间端点项、权重差、$J_2(A)$ 和全部端点项，并达到

$$
O\left(\frac1{\sqrt A\log A}\right)
$$

的尺度。普通 PNT 误差、FIB 地址重编码或单独的零点计数都不提供这条映射。

因此，补偿定理目前应被定位为一个独立的 centered-kernel 结果；它不能被
重命名为 Robin signed-tail 定理，也不能用它已经支付的 band volume 冒充
$I_\psi(A)$ 的符号。

## 452. Fibonacci--Lucas 特殊值抵消仍不提供 Robin 桥

Payam Danesh 的 [*Cancellation profiles of Fibonacci-Lucas zeta sums*](../../../Library/Analytic/danesh2026fiblucaszeta.md)，
arXiv:2609.33564v1，研究有限 Fibonacci/Lucas 加权和中的负整数 zeta
特殊值抵消。该文给出归一化绝对项的有限指数展开、总变差极限分布，及
Fibonacci/Lucas 情形在偶次数至少 26 时的最大项位置为 8；它还量化求和
条件数的阶。

这条结果与当前缺口的对象不同。它没有 Euler 乘积、\(\Lambda\)、\(\mu\)、
\(\psi\) 或 \(\sigma(N)/N\)，也没有把 Fibonacci 地址映射到同一个实际
Robin 候选。因此其有限特殊值抵消不能替代

$$
I_\psi(\log N)\quad\text{或同一候选上的有符号 Robin 余量估计}.
$$

它的直接研究价值是排除一条看似相近但对象不相容的路线：有限
Fibonacci--Lucas zeta 和的条件数抵消，不等于普通 Möbius 的平方根抵消。
继续重做这类特殊值展开不会缩小 FIB 到 Robin 的联合系数桥缺口。

## 453. 相对误差包络下的 dilation 差额上界

上一节的精确分解还可以给出一个不依赖零点展开的量级结论。令

$$
L=\log A,
\qquad a=\log c,
\qquad c>1,
$$

并假设在整个 $[A,\infty)$ 上有同一个相对误差包络

$$
|E(t)|\le\eta_A t.
$$

### 命题 453.1（dilation 差额的包络）

若 $L>0$，则由上一节对 $D_c(A)$ 的精确分解直接得到

$$
\boxed{
|D_c(A)|
\le
2\eta_A a\left(\frac1L+\frac1{L^2}\right).
}
\tag{453.1}
$$

**证明。** 记

$$
G(u)=\frac{1+u}{u^2},
\qquad
k(t)=\frac{G(\log t)}{t^2}.
$$

端点项满足

$$
\begin{aligned}
\int_A^{cA}|E(t)|k(t)\,dt
&\le\eta_A\int_L^{L+a}\frac{1+u}{u^2}\,du\\
&\le\eta_Aa\left(\frac1L+\frac1{L^2}\right).
\end{aligned}
$$

尾部权重差使用

$$
|G'(u)|=\frac{u+2}{u^3}.
$$

在 $t\ge cA$ 时令 $u=\log(t/c)\ge L$。平均值定理与
$dt/t=du$ 给出

$$
\begin{aligned}
&\int_{cA}^{\infty}|E(t)|
\left|\frac{1+\log(t/c)}{t^2(\log(t/c))^2}-k(t)\right|dt\\
&\quad\le
\eta_Aa\int_L^\infty\frac{u+2}{u^3}\,du
=\eta_Aa\left(\frac1L+\frac1{L^2}\right).
\end{aligned}
$$

两项相加即得（453.1）。证毕。

这个上界把“端点改变”和“尾部改变权重”分开支付。若某个全尾部 PNT
供应器能够给出如下现有零自由区同形的包络

$$
\eta_A\le C\exp\!\left(-d\frac{L^{3/5}}{(\log L)^{1/5}}\right),
$$

其中 $C,d>0$ 与 $A$ 无关，则固定 $c>1$ 时（453.1）至多给出

$$
|D_c(A)|
\ll_c
\frac{\exp(-dL^{3/5}(\log L)^{-1/5})}{L}.
$$

与当前 Robin 比较所需的

$$
\frac1{\sqrt A\,L}
$$

相比，其包络比为

$$
\sqrt A\exp\!\left(-d\frac{L^{3/5}}{(\log L)^{1/5}}\right),
$$

并且趋于无穷，因为 $L^{3/5}(\log L)^{-1/5}=o(L)$。这不是“不存在更强
估计”的证明；它证明的是：现有这类全局相对 PNT 误差，经过精确 dilation
分解后，仍不能支付平方根级 signed Robin 预算。要继续推进，必须改善同一实际
来源上的相关性估计，而不是再次加强相对误差包络的文字形式。

## 454. 原系数一重数反射的临界带定位

**定义 454.1（共同来源与分区）。** 沿用 [PR1–PR10](../../../Library/Analytic/openai2026quasirh.md#joint-control-of-all-powerful-prime-reflection-choices) 的原卷积、局部反演、Mellin pairing 及实际 inverse Gram $G_P^{-1}$。所有变量取原 Eisenstein 理想参数，$q_A$ 表示 norm；$p$ 是原标记素理想，$Q=q_p\asymp L$，$\mathscr S$ 是固定坏素集合。令 $C=A_1\ne1$ 为其他素因子中原 valuation $1$ 且选择第二分支者的平方自由乘积。其余选中乘积为 $A_2,A_3,A_4,B_0$；它们分别对应原 valuation $2,3,4,\ge6$，互素并避开 $p\mathscr S$。记

$$
x=q_C,\quad x_j=q_{A_j},\quad z=q_{B_0},\quad
W=x_2^2x_3^3x_4^4z^6,\qquad H_0=A_2^2A_3.
$$

原 $h$、full-series numerator 与剩余乘积长度分别为

$$
\begin{array}{c|c|c|c}
p\text{ 分支}&h&\text{numerator}&M_p\\ \hline
\text{第一支}&CA_2^2A_3^3A_4^4B_0^6m&pH_0C^3m&K/W\\
\text{低第二支 }j=1,2,3,4&p^{j-1}CA_2^2A_3^3A_4^4B_0^6m&p^{4-j}H_0C^3m&K/(Q^{j-1}W)\\
\text{高第二支}&p^5CA_2^2A_3^3A_4^4B_0^6m&H_0C^3m&K/(Q^5W).
\end{array}
\tag{454.1}
$$

这里 $(m,CA_2A_3A_4)=1$；仅低第二支另有 $p\nmid m$。$m$ 在 $B_0$ 处不受限，第一支与高第二支在 $p$ 处也不受限。原 valuation $5$ 没有第二支。取 $H=p^tH_0$，三种 $t$ 依次为 $1,4-j,0$。在 $x\asymp X$ 上，$m$ 的长度为 $Y=M_p/X$。

每个实际模式保留原 $b(h)$、外部共轭、Gauss 相位、当前 ray 字符、分母、mask 与 section indicator。只在正均方上扩大支撑。固定的共同包络 $\mathcal N$ 控制原 divisor-bound、profiles、Mellin、cusp、full-series mean 与 reciprocal-$L$ 成本，满足 $|b(h)|\ll K^\varepsilon\mathcal N$；不按行、选中乘积或模式重选系数或包络。

给定 $R_i=K^{a_i}>1$，对全部行与原 profiles 使用同一组阈值，把 $C\ne1$ 的实际模式分为

$$
\begin{aligned}
\mathrm P={}&\{x_2>R_2\}\cup\{x_2\le R_2,\ x_3>R_3\},\\
\mathrm S={}&\{x_2\le R_2,\ x_3\le R_3,\ 1<x\le R_1\},\\
\mathrm O={}&\{x_2\le R_2,\ x_3\le R_3,\ x>R_1,\
x^2/M_p\notin[R_1^{-4},R_1^4]\},\\
\mathrm T={}&\{x_2\le R_2,\ x_3\le R_3,\ x>R_1,\
R_1^{-4}\le x^2/M_p\le R_1^4\}.
\end{aligned}
\tag{454.2}
$$

端点按所写的弱不等号分配；原 annular 常数只改变估计常数。令 $e^{\rm paid}$ 是原 Mellin 下 $\mathrm P,\mathrm S,\mathrm O$ 三族与既有 $C=1$ powerful 族之和，$Q_{\rm paid}=(e^{\rm paid})^*G_P^{-1}e^{\rm paid}$。

**假设 454.2（解析输入）。** 使用 [primitive-mean 源稿 v2](https://rstation.ai/api/v1/papers/riemann_hypothesis_10/versions/2/download) 的 full $D_\nu$ 向量及其 Lemma 2 证明（4.7）—（4.9）、Proposition 3 证明（5.3）—（5.6）；使用 [I1–I16、I14a、H1–H8 与 G7](../../../Library/Analytic/faveri2026fixedorder.md#an-unchanged-numerator-term-in-the-primitive-continuous-adjoint)，以及 PR1–PR10、VF1–VF10、SH1–SH11 的精确有限变换与统一成本合同。$u=1+\eta+it$ 的固定 $\eta>0$ 满足这些输入的 spectral avoidance 条件。已知筛法、局部反演与固定字符位移在下面只作为中间输入；承重结论是它们对同一个原始系数族的联合应用，不对这些输入另立新定理或主张文献原创性。

**定理 454.3（同源补集的共同二次型界）。** 在假设 454.2 下，令

$$
U\asymp K,\qquad K^{1/2}\le D\le K^{1/2}L^{1/6-\delta},
\qquad 0<\delta<1/6,\qquad L=K^\ell,
\qquad 0<\ell<\frac3{530-36\delta}.
$$

取

$$
\begin{aligned}
r&=\frac16-\left(\frac{41}6-2\delta\right)\ell,\\
c&=\frac{18r-407\ell}{305}
=\frac{3-(530-36\delta)\ell}{305}>0,\\
a_1&=2c+3\ell,\qquad a_2=(c+\ell)/2,\qquad
a_3=2(c+\ell)/9,
\end{aligned}
\tag{454.3}
$$

并选择同一个 spectral 允许的固定

$$
0<\eta<\min\left\{
\frac{1/8-\ell}{32},\frac\ell8,
\frac{c}{2(4+24\ell+22a_1+20a_2+18a_3)}\right\}.
\tag{454.4}
$$

则对每个最终 $\varepsilon>0$，内部小幂先作分配后有

$$
Q_{\rm paid}\ll K^{2-\zeta+\varepsilon}\mathcal N^2,
\qquad
\zeta=\min\{(1/8-\ell)/2,\ell/2,c/2\}>0.
\tag{454.5}
$$

对有界的共同成本及充分小的 $\varepsilon$，H8 的 $w$ 与 $e^{\rm paid}$ 在同一个实际 inverse Gram 下的总二次型为 $o(K^2)$。这里 $\zeta$ 只属于 correction vector；$w$ 使用 H8 自己的节省，不赋予它同一个数值指数。原 valuation $1$ 反射族中尚未估计的部分准确为 $\mathrm T$，仍允许所有合法 $p$ 分支及其他同时选中乘积。结论不包含整个 projection/complement、其他原长度与高度、原 growing-height allowance、F4 transfer 或 signed Robin restoration 的界。

证明。先保留源筛估计在化为体积界以前的 minimum。对 $M=AB$、$T_0=\sqrt M B$，置

$$
\mathcal B(A,T)=\min\{\Psi_6(A,T),(A/B)(B+T)\}.
$$

源稿（4.7）—（4.9）给出的 completed smoothed mean 带外部因子 $1/B$，其界为 subpowers 乘 $\mathcal B(A,T)$。两种选择关于 $T$ 的各列指数至多为 $1$，所以在 $T=k_\eta\sqrt{q_H}T_0(1+|t|)^5$ 时，费用至多为

$$
(q_HM)^\varepsilon q_H^{1/2}(1+|t|)^6\mathcal B(A,T_0).
$$

源稿（5.4）将同一个 $(H,A,B)$ 的有限向量均方返回自身。以正数 $\mathcal B(A,T_0)$ 归一化 height supremum，再按（5.5）选择同一个固定 $k_\eta$，即用其（2.5）的先验有限性完成原吸收步骤。有限 ray 向量、完成化卷积及单调缩短都沿用（4.3）的同一估计。结合已有 Proposition 3 的体积界，在本证明中得到

$$
\frac1B\sum_{\substack{q_a\asymp A,\ q_b\asymp B\\ab\ {\rm sf},\ (ab,H)=1}}
|D_\nu(Hab^3,u)|^2
\ll(q_HM)^\varepsilon q_H^{1/2}(1+|t|)^6M f(M,B),
\tag{454.6}
$$

其中

$$
f(M,B)=\min\left\{1,\
B^{-1}+\frac B{\sqrt M}+B^{-1/2}+M^{-1/4}B^{1/2},\
B^{-1}+\frac{\sqrt M}B\right\}.
\tag{454.7}
$$

这是对同一个正均方的三个上界，没有组合不同的优化系数。内含 fixed-$\eta$ 常数与小幂损失。

先估计 $\mathrm O$。固定实际 powerful 乘积与一个 $p$-sector，把不受平方自由限制的 $m$ 写成

$$
m=a\Delta^2,\quad a\ {\rm sf},\quad
e=\gcd(a,\operatorname{rad}(H\Delta)),\quad a=ea_0,
\quad d=q_\Delta,\quad v=q_e,\quad s=d\sqrt v.
$$

实际互素条件保证 $a_0C$ 平方自由且 $(a_0C,H\Delta^2e)=1$。在（454.6）中取 multiplier $H\Delta^2e$、$A\asymp Y/(d^2v)$、$B\asymp X$，因而 $M'=M_p/s^2$。PR7 的固定扩大处理非空有界 subunit annuli；空支撑为零。包含 $C^{-1/2}$ scalar 的原系数 $\ell^2$ 范数至多为

$$
K^\varepsilon\mathcal N\sqrt{Y/(d^2v)}
\prod_{j=2}^4x_j^{-1/2}.
$$

Cauchy 与（454.6）给出固定 $(\Delta,e,X)$ 的 pairing 界

$$
\begin{aligned}
|\operatorname{pair}_{\Delta,e,X}|
\ll{}&K^\varepsilon(1+|t|)^J\mathcal N
M_pq_H^{1/4}\prod_{j=2}^4x_j^{-1/2}\\
&\times d^{-3/2}v^{-3/4}\sqrt{f(M_p/s^2,X)},
\end{aligned}
\tag{454.8}
$$

暂未乘低-$p$ 的 $Q^{-1/2}$ scalar；第一支与高第二支的 scalar 模至多为 $1$。所有原复相位在 pairing 内保留，到正范数处才取模。

若 $s>R_1$，使用 $f\le1$ 与

$$
d^{-3/2}v^{-3/4}=s^{-1/3}d^{-7/6}v^{-7/12}.
$$

$e$ 的除数和仅支付 $(q_Hd)^\theta$，取内部 $\theta<1/12$，则 $\Delta$ 的剩余和收敛，整个尾部给出 $R_1^{-1/3}$。若 $s\le R_1$，在 $\mathrm O$ 下侧有 $X/\sqrt{M_p}<R_1^{-2}$ 及 $X\gg R_1$，故 $X/\sqrt{M'}\ll R_1^{-1}$，（454.7）第二选择的每项至多为常数乘 $R_1^{-1/2}$。在上侧 $X/\sqrt{M_p}>R_1^2$，第三选择至多为常数乘 $R_1^{-1}$。所以小-$s$ 部分一致满足 $\sqrt f\ll R_1^{-1/4}$；其 $d^{-3/2}v^{-3/4}$ 和也收敛至允许的小幂。

代回原参数并汇总 $C$ dyads，得到

$$
|C_{p,\mathrm O}(t)|\ll(KL)^\varepsilon(1+|t|)^J\mathcal N
KQ^{1/4}R_1^{-1/4}
x_2^{-2}x_3^{-13/4}x_4^{-9/2}z^{-6}.
\tag{454.9}
$$

三种 $p$-sector 的实际 $Q$ 因子依次为 $Q^{1/4}$、$Q^{3/2-5j/4}\le Q^{1/4}$、$Q^{-5}$。其余 powerful 质量绝对可和。依赖 $p$-sector 的不平衡限制始终留在实际 signed tuple 中，使用（454.8）的统一正范数界，不把此限制充当未被证明的 structured-coefficient multiplier。最后对原标记取正和，原 Mellin 与 G7 给出

$$
Q_{\mathrm O}\ll(UKL)^\varepsilon\mathcal N^2U^{2\eta}
K^2L^{3/2}R_1^{-1/2}.
\tag{454.10}
$$

再估计 $\mathrm P$，这里需要联合处理标记与 $C$。在（454.6）中只用 $f\le1$，沿上述 $m=a\Delta^2$ 分解，对 $(\Delta,e)$ 费用求和，得到本证明内部的供应式

$$
\sum_{\substack{q_C\asymp X,\ C\ {\rm sf}\\(C,H)=1}}
\sum_{\substack{q_m\asymp Y\\(m,C)=1}}
|D_\nu(HC^3m,u)|^2
\ll(q_HXY)^\varepsilon q_H^{1/2}X^2Y(1+|t|)^6.
\tag{454.11}
$$

固定 $(\Delta,e)$ 的费用为 $q_H^{1/2}X^2Y/(d\sqrt v)$；$e$ 的除数和为小幂，$\Delta$ 的调和和为对数。实际 ray 由固定 $216$ 个分量的最大值处理；只在正均方中扩大原 mask 支撑。

第一 $p$ 支的系数平方质量至多为 $K^\varepsilon\mathcal N^2Y\prod_{j=2}^4x_j^{-1}$。在正 $D$ 平方和中合并 $n=pm$，其表示重数是除数界，实际仍有 $(C,n)=1$。对（454.11）取 multiplier $H_0$、$n$ 长度 $LY$，得到

$$
\sum_{p\asymp L}|C_{p,X}^{\rm first}(t)|^2
\ll(KL)^\varepsilon(1+|t|)^J\mathcal N^2K^2L
x_2^{-4}x_3^{-13/2}x_4^{-9}z^{-12}.
\tag{454.12}
$$

低-$p$ 的 $j=1$ 支有 numerator $H_0(pC)^3m$；其系数平方质量多一个 $Q^{-1}$。在正均方中合并平方自由 $b=pC$，长度 $LX$，表示重数仍为除数界。（454.11）的费用为 $q_{H_0}^{1/2}(LX)^2Y$，也给出（454.12）的 $K^2L$。各原字符相位只在这之前的系数范数中估计，不从原 signed pairing 中删除。

对低-$p$ 的 $j=2,3,4$，按自身 $Y/Q^{j-1}$ 长度、$Q^{-1/2}$ scalar 和 multiplier $p^{4-j}H_0$ 使用（454.11），再求标记和。平方 pairing 的标记幂为 $L^{4-5j/2}$，依次为 $L^{-1},L^{-7/2},L^{-6}$。高第二支的长度为 $Y/Q^5$，标记幂为 $L^{-9}$。这些均至多为 $L$。用范数三角不等式汇总同一原系数的 powerful 乘积，其共同质量为 $x_2^{-2}x_3^{-13/4}x_4^{-9/2}z^{-6}$。在 $\mathrm P$ 中该质量的尾和给出 $R_2^{-1}+R_3^{-9/4}$；$C$ dyads 只支付对数。因此

$$
Q_{\mathrm P}\ll(UKL)^\varepsilon\mathcal N^2U^{2\eta}K^2L
(R_2^{-2}+R_3^{-9/2}).
\tag{454.13}
$$

对小区域 $\mathrm S$，在 PR1–PR6 的同一有限 multi-mark 计算中加入 $A_1=C$，取

$$
k_1=2,\qquad s_1=3,\qquad b_1=4.
$$

同类型 CRT 是 $\gamma_2(C)$；与类型 $l$ 的交换指数为 $6(1-l)$、$(2-4)k_l$，故仍为平凡值。PR2 的当前字符改为 $\nu_j=\nu_0\prod_{i<j,\ i\ge1}\epsilon_{A_i,i}$，$r_j=p^tm\prod_{1\le i<j}A_i^{s_i}\prod_{i>j}A_i^i$，原完整标量的乘积范围改为 $j=1,\ldots,4$。包括 $C$ 的混合相位均保留。PR4 的 mark 现在为

$$
R_0=C^4A_2^3A_3^2A_4,
\qquad
\psi(w)=\prod_{j=1}^4\mathbf1_{A_j^{4-j}\mid w}
\chi_{A_j}(w/A_j^{4-j})^{-(j+1)},
\tag{454.14}
$$

低-$p$ 时再加入原 $p^{5-j_p}$ mark。抽到 mark 外的单位因子准确为

$$
\Xi=\prod_{1\le j<i\le4}\chi_{A_j}(A_i)^{-k_j(i-s_i)},
$$

低-$p$ 时另乘 $\prod_{j=1}^4\chi_p(A_j)^{-k_p(j-s_j)}$。PR4 中的 $\mathcal K$、$\tau_i$、所有 Ramanujan 中心与零值也按这一完整块集合取值。每个 $k_j+b_j=6$，故 $r=1$ 主项无残留增长字符 $\chi_C(d_0)$；$p^2e_0$ 的 imprimitive sector 仍使用完整 Gauss 和与 I4/H5 的 gcd-Cauchy。

PR3 同时提取 $E_1\mid C$，即

$$
d=(\prod_{j=1}^4E_j)Fd_0,\qquad
n=\prod_{j=1}^4(A_j^j/E_j)(B_0^6/F)n_0,
$$

$$
D'=D/(\prod_{j=1}^4q_{E_j}q_F),\qquad K'=K/(xW),
$$

保留全部原 Möbius 符号、互素排除和 section。原有限 $g$ split 与两个 polar tails 同时保留；新增 weighted error 因子为 $x^{11/4+12\eta}$。代回 $K',D'$ 后，它的原变量质量为 $x^{7/3+11\eta}$，故 $x\le R_1$ 的截断和至多为 $R_1^{10/3+11\eta+\varepsilon}$。主项质量为 $x^{-2}$，连原除数权仍可和。没有增长 $\chi_C(d_0)$，所以原固定字符 Möbius 位移与 SH6 的移动删因子界继续适用。所有非空 subunit 支撑仍按自身 sector 扩大。由此

$$
\begin{aligned}
|C_{p,\mathrm S}(t)|\ll{}&(KL)^\varepsilon(1+|t|)^J\mathcal N
\bigl[KD^{-1/8}+K/Q\\
&+K^{5/12+\eta}DQ^{11/4+12\eta}
R_1^{10/3+11\eta}R_2^{13/6+10\eta}R_3^{1+9\eta}\bigr].
\end{aligned}
\tag{454.15}
$$

将（454.10）、（454.13）、（454.15）配入同一个原 Mellin 与实际 $G_P^{-1}$。固定有限和的交叉项用范数三角不等式支付。加上既有 $C=1$ 族以后，总 correction 的界含有 PR9 的前四项

$$
K^2D^{-1/4}L+K^{5/6}D^{4/3}L^{13/6}
+K^{5/6+2\eta}D^2L^{-1/6+2\eta}+K^2/L,
$$

以及新增的三份费用

$$
\begin{aligned}
&K^{5/6+2\eta}D^2L^{13/2+24\eta}
R_1^{20/3+22\eta}R_2^{13/3+20\eta}R_3^{2+18\eta},\\
&K^2L(R_2^{-2}+R_3^{-9/2}),\\
&K^2L^{3/2}R_1^{-1/2},
\end{aligned}
\tag{454.16}
$$

同乘 $(UKL)^\varepsilon\mathcal N^2U^{2\eta}$。这里 $C=1$ 的已证 PR10 可直接调用；等价地，它也可用上述同一多标记计算的小区域及（454.11）在 $C=1$ 的联合标记尾部界处理。三阈值不按行或 profile 分别最优化。

（454.3）给出同一组参数的四个准确裕度

$$
r-\frac{20}3a_1-\frac{13}3a_2-2a_3
=2a_2-\ell=\frac92a_3-\ell
=\frac{a_1}2-\frac{3\ell}2=c.
\tag{454.17}
$$

新增小区域的 $\eta$ 损失为 $(4+24\ell+22a_1+20a_2+18a_3)\eta<c/2$；各尾部损失为 $2\eta<c/2$。（454.4）也蕴含原 SH、VF 和 PR10 的限制；既有 powerful 族在本较小区间的节省至少容许（454.5）的 $\zeta$。PR9 前四项保留的裕度分别由同一个 $(1/8-\ell)/2$、$\ell/2$ 及原 SH 约束支付，故得（454.5）。H8 对 $w$ 另给正裕度；实际 Gram 范数的三角不等式于是给出所述 $o(K^2)$。定义 454.1 的四族互斥且穷尽 $C\ne1$ 的原模式，所以剩余部分恰为 $\mathrm T$。证毕。

## 追加锚（本行以下为增补区）

## 455. 临界反射族的共轭公共因子细分

**定义 455.1（共轭公共部分）。** 对定义 454.1 中实际选中的平方自由好理想 $C$，令

$$
I(C)=\gcd(C,\overline C),\qquad J(C)=C/I(C),\qquad v=q_{I(C)}.
$$

保留原生成元的 primary 约定和全部相位；$I(C)$ 表示理想。令 $e^{\rm rat}_{>R}$ 为原 Mellin 向量中满足 $C\in\mathrm T$ 且 $v>R\ge1$ 的全部模式之和，并记

$$
Q^{\rm rat}_{>R}=(e^{\rm rat}_{>R})^*G_P^{-1}e^{\rm rat}_{>R}.
$$

**定理 455.2（稀疏公共部分在原二次型中的消费）。** 在假设 454.2 及其同一共同成本包络 $\mathcal N$ 下，

$$
Q^{\rm rat}_{>R}\ll(UKL)^\varepsilon\mathcal N^2U^{2\eta}
K^2LR^{-1/2}.
\tag{455.1}
$$

在定理 454.3 的原参数区间、原 $\eta$ 和原阈值下，取 $R=R_1$，则把 $e^{\rm rat}_{>R_1}$ 加入原 $e^{\rm paid}$ 后仍满足（454.5）的同一个 $\zeta$ 界。H8 的 $w$ 与这个扩大后的 correction vector 的实际总二次型仍为 $o(K^2)$，其中 $w$ 保留自己的节省。原一重数反射族中准确剩下

$$
\mathrm T_{\rm rat}=\{\text{定义 454.1 的 }\mathrm T\text{ 模式}:q_{\gcd(C,\overline C)}\le R_1\}.
\tag{455.2}
$$

在该剩余族中，$J(C)$ 必须含有非单位的未配对分裂素理想部分。此结论只细分同一个原系数族；不包含整个 projection/complement、其他原长度与高度、原 growing-height allowance、F4 transfer 或 signed Robin restoration 的估计。

证明。先使用 Eisenstein 理想的既有分裂分类。避开 $6$ 后，有理素数 $l$ 在该域中或保持为范数 $l^2$ 的惰性素理想 $(l)$，或分裂为两个范数为 $l$ 的共轭素理想。因为 $C$ 作为理想平方自由，$I(C)$ 在惰性素处保留该素理想，在分裂素处恰好保留被同时选中的共轭对。因此唯一地有

$$
I(C)=(r),\qquad r\in\mathbb N\text{ 平方自由},\quad(r,6)=1,
\qquad v=r^2,
$$

$$
C=IJ,\qquad (I,J)=1,\qquad\gcd(J,\overline J)=1.
\tag{455.3}
$$

$J$ 只含分裂素理想，且不同时含同一有理素数上的两个共轭素因子。分解不改变任何原 numerator valuation；不把有理素性与 Eisenstein 素性等同。

固定实际 $I,A_2,A_3,A_4,B_0$，在 $q_J\asymp X$ 上令 $Y=M_p/(vX)$。完整 numerator 是 $HI^3J^3m$，$H$ 与 $M_p$ 仍按（454.1）逐个 $p$-sector 取值。原 scalar 的模至多为 $v^{-1/2}X^{-1/2}\prod_{j=2}^4x_j^{-1/2}$，低-$p$ 支另有 $Q^{-1/2}$。原 $b(h)$、$\gamma_2(IJ)$、混合字符、当前有限 ray、分母、mask、section、共同 profiles 及 $\mathrm T$ 限制始终留在 signed pairing 内；这里只使用平方自由实际支撑上的 $|\gamma_2(IJ)|=1$，不需要重新分解其 CRT 相位。

在已消费的（454.11）中取同一个 multiplier $HI^3$，得到本证明的正均方输入

$$
\sum_{\substack{q_J\asymp X,\ J\ {\rm sf}\\(J,HI)=1}}
\sum_{\substack{q_m\asymp Y\\(m,J)=1}}
|D_\nu(HI^3J^3m,u)|^2
\ll(q_HvXY)^\varepsilon q_H^{1/2}v^{3/2}X^2Y(1+|t|)^6.
\tag{455.4}
$$

这里 $m$ 不限平方自由，其全部平方部分沿用（454.11）的分解。固定 $216$ 个 ray 分量统一处理。只有在正范数中才放松 $\gcd(J,\overline J)=1$、原 $\mathrm T$ band 及其余互素条件；不把这些限制塞入需要独立列系数的 structured estimate。非空有界 subunit annuli 按原固定扩大处理，空支撑为零。

第一 $p$ 支在一个 $J$ dyad 上的原系数平方质量至多为

$$
K^\varepsilon\mathcal N^2(Y/v)\prod_{j=2}^4x_j^{-1}.
$$

在正 $D$ 平方和中合并 $n=pm$，保持实际 $(J,n)=1$，其表示重数为除数界。对（455.4）取 multiplier $H_0I^3$、$n$ 长度 $LY$，由 Cauchy 得

$$
\sum_{p\asymp L}|C_{p,I,X}^{\rm first}(t)|^2
\ll(KL)^\varepsilon(1+|t|)^A\mathcal N^2
K^2Lv^{-3/2}x_2^{-4}x_3^{-13/2}x_4^{-9}z^{-12}.
\tag{455.5}
$$

其 $v$ 幂准确来自 $(Y/v)v^{3/2}X^2LY=v^{1/2}L(XY)^2$ 与 $XY=K/(vW)$。低-$p$ 的 $j=1$ 支在正均方中合并平方自由 $b=pJ$，长度 $LX$；系数平方质量为 $\mathcal N^2Y/(vL)$，均方费用为 $q_{H_0}^{1/2}v^{3/2}(LX)^2Y$，同样给出（455.5）。$p$ 与 $J$ 在实际支撑上互素，即使 $J$ 含 $\overline p$ 也不损坏理想平方自由条件；$I$ 避开 $p$。

低-$p$ 的 $j=2,3,4$ 使用自身原长度 $Y=K/(Q^{j-1}vWX)$ 和 multiplier $p^{4-j}H_0I^3$。scalar 平方、multiplier、长度平方与标记数的 $L$ 幂合计为

$$
L\cdot L^{-1}\cdot L^{(4-j)/2}\cdot L^{-2(j-1)}
=L^{4-5j/2},
$$

分别为 $L^{-1},L^{-7/2},L^{-6}$。高第二支的长度为 $K/(Q^5vWX)$，其标记幂为 $L^{-9}$。它们均被（455.5）的 $L$ 控制，且全部保留同一个 $v^{-3/2}$。原 valuation $5$ 没有第二支。

先对实际有限 signed 模式形成 pairing，再取上述正范数。对 $J$ dyads 支付对数，并对其他实际选中乘积使用范数三角不等式；其共同质量 $x_2^{-2}x_3^{-13/4}x_4^{-9/2}z^{-6}$ 绝对可和。因此

$$
\left\|(C_{p,I,\mathrm T}(t))_p\right\|_2
\ll(KL)^\varepsilon(1+|t|)^A\mathcal N KL^{1/2}v^{-3/4}.
\tag{455.6}
$$

实际 $\mathrm T$ 限制只减少先前使用的系数平方质量和正均方支撑，不改变此式的适用性。

最后，公共理想 $I$ 的范数为 $r^2$，故对任意充分小的内部 $\epsilon>0$ 有

$$
\sum_{\substack{I=(r),\ r\ {\rm sf}\\q_I>R}}q_I^{-3/4+\epsilon}
\le\sum_{r>\sqrt R}r^{-3/2+2\epsilon}
\ll R^{-1/4+\epsilon}.
\tag{455.7}
$$

在（455.6）中先对原有限 $I$ 求范数和，再仅将这个正 majorant 扩为（455.7），恢复同一个原 Mellin 和 G7 的实际 inverse Gram，得到（455.1）。所有内部小幂在最终 $\varepsilon$ 以前分配；实际 $q_I\ll K$，没有新的独立多项式成本。

取 $R=R_1=K^{a_1}$，原（454.3）给出

$$
\frac{a_1}2-\ell=c+\ell/2>c.
$$

原（454.4）保证 $U^{2\eta}$ 的损失 $2\eta<c/2$，因此（455.1）被原 $K^{2-\zeta+\varepsilon}\mathcal N^2$ 吸收。对同一个 $G_P^{-1}$ 使用范数三角不等式，与（454.5）及 H8 合并即得所述总界。剩余族正是（455.2）；若其中 $J=1$，则 $C=I$ 且 $q_C\le R_1$，与 $\mathrm T$ 的 $q_C>R_1$ 矛盾。因此所有仅由惰性素理想和完整共轭对构成的一重数选择均在已控制的并集中；未配对分裂核心的进一步消去仍是额外估计义务。证毕。

## 追加锚（本行以下为增补区）

## 456. 精确双频支撑对原系数反射预算的改进

**定理 456.1（完整有限 Euler 分裂下的支撑节省）。** 使用假设 454.2 的解析输入、定义 454.1 的实际原系数族以及同一个共同成本包络 $\mathcal N$。以下是这些输入的 `repo-derived` 联合应用；Ramanujan 支撑、格点计数和 Cauchy 不等式只作为证明中的既有工具，不另作原创性断言。

令

$$
U\asymp K,\quad K^{1/2}\le D\le K^{1/2}L^{1/6-\delta},
\quad 0<\delta<1/6,\quad L=K^\ell,
\quad 0<\ell<\frac9{1114-108\delta},
$$

$$
\begin{aligned}
c&=\frac{9-(1114-108\delta)\ell}{655}>0,\\
a_1&=2c+3\ell,\quad a_2=(c+\ell)/2,
\quad a_3=2(c+\ell)/9,\quad R_i=K^{a_i}.
\end{aligned}
\tag{456.1}
$$

选同一个满足原 spectral avoidance 的固定

$$
0<\eta<\min\left\{
\frac{1/8-\ell}{32},\frac\ell8,
\frac{c}{2(4+24\ell+22a_1+20a_2+18a_3)}\right\}.
\tag{456.2}
$$

用这组共同阈值重新定义（454.2）的 $\mathrm P,\mathrm S,\mathrm O,\mathrm T$，并令 $e^{\rm paid+rat}$ 包含其 $\mathrm P,\mathrm S,\mathrm O$、全部 $C=1$ powerful 选择，以及 $\mathrm T$ 内所有 $q_{\gcd(C,\bar C)}>R_1$ 的实际模式。则

$$
(e^{\rm paid+rat})^*G_P^{-1}e^{\rm paid+rat}
\ll K^{2-\zeta+\varepsilon}\mathcal N^2,
\qquad
\zeta=\min\{(1/8-\ell)/2,\ell/2,c/2\}>0.
\tag{456.3}
$$

这里内部小幂在最终 $\varepsilon>0$ 以前分配。对有界共同成本和充分小的 $\varepsilon$，加入 H8 的 $w$ 后，同一实际 inverse Gram 下的总二次型仍为 $o(K^2)$；$w$ 沿用 H8 自己的节省，不指定为 $\zeta$。尚未控制的原一重数反射族准确为

$$
\mathrm T_{\rm rat}=
\{\mathrm T,\ q_{\gcd(C,\bar C)}\le R_1\},
\tag{456.4}
$$

其未配对分裂核心非单位。结论不包含该剩余族、整个 projection/complement、其他原长度与高度、原 growing-height allowance、F4 transfer 或 signed Robin restoration。

证明。复用 [PR4 的完整多标记变换](../../../Library/Analytic/openai2026quasirh.md#joint-control-of-all-powerful-prime-reflection-choices) 与 [I4、I10–I13 的固定 cusp 估计和有限 Euler 分裂](../../../Library/Analytic/faveri2026fixedorder.md#an-unchanged-numerator-term-in-the-primitive-continuous-adjoint)。加入（454.14）的 $C=A_1$ 块。对每个非单位块 $P_i$，写其原 valuation 为 $j_i\in\{1,2,3,4\}$，并取

$$
s_i=4-j_i,\quad b_i=5-j_i,\quad k_i=j_i+1,
\quad R_0=\prod_iP_i^{b_i},\quad
\Pi=\prod_iP_i^{s_i},\quad
V=q_\Pi,\quad B=\prod_iq_{P_i}.
$$

低-$p$ 支再加入其真实 $j_p$ 块；第一支和高支没有额外 $p$ mark。各块互素，且与外模数 $a$ 及固定观察模数 $\mathfrak M$ 互素。所有原混合字符、Gauss 相位、有限 ray 置换、分母、零 mask 和外部共轭保留在原式中。

记完整有限变换系数为 $\mathcal A_r(n)$，$r\mid a$。PR4 的 $c_{R_0}(n)$ 在 $\Pi\nmid n$ 时为零。由完整 imprimitive Gauss 界和 $|\tau_i|=\sqrt{q_{P_i}}$，有

$$
|\mathcal A_r(n)|^2
\le Bq_rq_{\gcd(n,r)}\mathbf1_{\Pi\mid n}.
\tag{456.5}
$$

它也适用于第一 $p$ 支外模数 $a=p^2e_0$；此处没有把 imprimitive $r$-Gauss 和换成平方自由点态界。

在 $q_{n/\mathfrak M}\asymp H$ 的真实 Fourier dyad 上，$\Pi d\mid n\ne0$ 的格点数至多为固定常数乘 $H/(Vq_d)$；非空性已经迫使 $Vq_d\ll_{\mathfrak M}H$。因此

$$
\begin{aligned}
\sum_{q_{n/\mathfrak M}\asymp H}|\mathcal A_r(n)|^2
&\le Bq_r\sum_{d\mid r}q_d
\#\{n:\Pi d\mid n,\ q_{n/\mathfrak M}\asymp H\}\\
&\ll(q_rH)^\varepsilon Bq_rH/V.
\end{aligned}
\tag{456.6}
$$

这里使用 $q_{\gcd(n,r)}\le\sum_{d\mid\gcd(n,r)}q_d$。固定分母和非空 fractional-lattice gap 包含在常数中；空 dyad 贡献为零。

对同一个完整 marked cusp 系数，I4 只提供总平方和 $\ll(1+|t|)^JH^{1+\eta+\varepsilon}$。与（456.6）作 Cauchy 得

$$
\sum_{q_{n/\mathfrak M}\asymp H}
|\mathcal A_r(n)t_{[R_0r]}(n/\mathfrak M)|
\ll(q_rH)^\varepsilon(1+|t|)^J
B^{1/2}q_r^{1/2}V^{-1/2}H^{1+\eta/2}.
\tag{456.7}
$$

节省来自有限变换系数的平方质量，不假设 $t$ 的平方质量在 $\Pi$ 倍数上按密度分布；也不将 $t(\Pi m)$ 替换为 $t(m)$，或借用 residue theta 的周期性。

原 Fourier 长度是 $X=VY$，$R=R_0r$ 的 dual scale 是 $K_R=q_R^2/X$。把（456.7）放回原 smooth inversion，各 dyad 都得到共同的 $V^{-1/2}$ 因子。低于固定分母所决定的最小非零频率尺度的 dyad 为空；其余情形，包括 $K_R<V$，均逐 dyad 使用（456.7）及原核界求和，得到同一个正 majorant。去掉原 Fourier normalization 并乘实际 reflected scalars，unweighted error 改为

$$
(Yq_a\prod_iq_{P_i})^\varepsilon(1+|t|)^J
Y^{-\eta}q_a^{1/2+\eta}
\prod_iq_{P_i}^{3-j_i/2-j_i\eta}.
\tag{456.8}
$$

它是原 unweighted error 乘 $\prod_iq_{P_i}^{-(4-j_i)/2}$；完整 cusp 系数与有限 ray 族没有改变。

继续保留原有限 $\sum_{g\mid m}z_u(g)$。在同一个实际 sector 上于 $G$ 分裂后，小-$g$ 误差为（456.8）乘 $G^{1/2-5\eta}$；large-$g$ 的原 full-$D$ convexity 尾部仍为

$$
(Yq_a\prod_iq_{P_i})^\varepsilon(1+|t|)^J
\frac{Y^{5/4-\eta/2}}{q_aG^{1+6\eta}}
\prod_iq_{P_i}^{1/2-j_i/4-(3+j_i/2)\eta}.
\tag{456.9}
$$

两个 finite polar tails 仍有界为 $Y(q_a\prod_iq_{P_i})^{-1}G^{-1-6\eta}$，不提前换成无限主项乘积。现在取

$$
G=Y^{5/6}q_a^{-1}\prod_iq_{P_i}^{-5/3+j_i/6}.
\tag{456.10}
$$

若 $G\ge1$，小-$g$ 与 large-$g$ 的 $Y$ 指数分别为 $5/12-31\eta/6$、$5/12-11\eta/2$；每块的 $\eta$ 系数分别为 $25/3-11j_i/6$、$7-3j_i/2$，均至多为 $13/2$。实际支撑上 $q_a\ll Y$，故 $q_a^{6\eta}$ 可由 $Y^{6\eta}$ 支付，得到完整 weighted error

$$
\operatorname{Err}_{\rm wt}
\ll(Yq_a\prod_iq_{P_i})^\varepsilon(1+|t|)^J
Y^{5/12+\eta}
\prod_iq_{P_i}^{(26-5j_i)/12+12\eta}.
\tag{456.11}
$$

finite polar tail 的无 $\eta$ 上界为 $Y^{1/6}\prod_iq_{P_i}^{2/3-j_i/6}$；与（456.11）的指数差分别是 $1/4$、$(6-j_i)/4>0$，所以同次 split 已支付它。若 $G<1$，$q_a$ 大于（456.10）的分子，直接计数（456.9）在 $G=1$ 的整个原支与两个 polar terms，给出同一个界。有界非空 subunit annuli 沿用原固定扩大，不产生新多项式成本。

四类块的 weighted mark 指数由 $11/4,2,5/4,1/2$ 分别降为

$$
7/4,\qquad4/3,\qquad11/12,\qquad1/2.
\tag{456.12}
$$

代回 PR3 与（454.14）的原 $E_j,F,d_0,n_0$ 分解，保持每个 Möbius 符号与相位。两个主项及原固定字符位移不变。误差的原变量质量现在为

$$
\frac{x^{4/3+11\eta}x_2^{1/2+10\eta}
 x_3^{-1/3+9\eta}x_4^{-7/6+8\eta}z^{-5/2-6\eta}}
{(\prod_jq_{E_j})q_F}.
$$

$x_4,z$ 的和连原除数损失收敛；$x,x_2,x_3$ 的截断计数与原 divisor sums 给出

$$
\begin{aligned}
|C_{p,\rm small}(t)|\ll{}&(KL)^\varepsilon(1+|t|)^J\mathcal N
\bigl[KD^{-1/8}+K/Q\\
&+K^{5/12+\eta}DQ^{7/4+12\eta}
R_1^{7/3+11\eta}R_2^{3/2+10\eta}R_3^{2/3+9\eta}\bigr].
\end{aligned}
\tag{456.13}
$$

这里低-$p$ 的 $j_p=1,2,3,4$ 在按各自长度缩短后，误差的无 $\eta$ 标记幂依次为 $7/4,11/12,1/12,-3/4$。第一支在 numerator 长度 $QK'$、外模数 $pd_0$ 或 $p^2e_0$ 上应用无 $p$-mark 的（456.11），与 VF9 同样的原 sector 计数给出 $D'Q^{5/12+\eta}$；（456.6）已包含完整 imprimitive overlap。高支按 I14a 的全部 $j\ge6$ 恒等式缩为 $K'/Q^5$，没有低-$p$ mark，且原 $Q^{-6\eta}$ 和两个 $e$-sector 计数有利。它们均由（456.13）的 $Q$ 幂控制；valuation $5$ 没有第二支。$C=1$ 时，small 部分取 $x=1$，powerful tails 仍使用（454.11）—（454.13）；无标记分量继续使用 I9。

将（456.13）、不变的（454.10）、（454.13）以及 PR9 的前四项放入同一个原 Mellin 与实际 inverse Gram。新的 small-error 费用是

$$
(UKL)^\varepsilon\mathcal N^2U^{2\eta}
K^{5/6+2\eta}D^2L^{9/2+24\eta}
R_1^{14/3+22\eta}R_2^{3+20\eta}R_3^{4/3+18\eta}.
\tag{456.14}
$$

其余三阈值费用仍是 $K^2L(R_2^{-2}+R_3^{-9/2})$ 与 $K^2L^{3/2}R_1^{-1/2}$。这一步复用的是（454.10）—（454.16）的 constituent proofs，不在定理 454.3 的旧 $\ell$ 范围以外直接调用其结论。原复系数只在正范数处取模，所有交叉项由同一范数的三角不等式支付。

（456.1）的四个无 $\eta$ 裕度准确为

$$
\begin{aligned}
a_1/2-3\ell/2&=c,&2a_2-\ell&=c,\\
(9/2)a_3-\ell&=c,&
\frac16-\left(\frac{29}6-2\delta\right)\ell
-\frac{14}3a_1-3a_2-\frac43a_3&=c.
\end{aligned}
\tag{456.15}
$$

（456.14）的 $\eta$ 损失至多是 $(4+24\ell+22a_1+20a_2+18a_3)\eta<c/2$。不变项在所用 $\ell<1/9$ 范围内仍有原正裕度，I9 的裕度由（456.2）支付。由此得到 $\mathrm P,\mathrm S,\mathrm O$ 与全部 $C=1$ 的（456.3）。

最后对同一新阈值 $R_1$ 复用（455.1）的证明。其额外费用为 $(UKL)^\varepsilon\mathcal N^2U^{2\eta}K^2LR_1^{-1/2}$，无损失裕度 $a_1/2-\ell=c+\ell/2>c$，仍被同一 $\zeta$ 吸收。于是（456.3）包含全部所述模式，剩余恰为（456.4）；未配对核心非单位的结论沿用定理 455.2 的同一论证。

新共同 $\ell$ 区间严格包含原 $0<\ell<3/(530-36\delta)$：两个端点交叉相乘后的正差为 $1428$。该扩大来自（456.6）—（456.11）的完整误差估计，未假设剩余临界带已经消去。证毕。

## 追加锚（本行以下为增补区）

## 457. 保留谱幂次与平方部分权重的完整素标记预算

**定理 457.1（指定平衡扇区的完整 primitive continuous 向量）。** 使用假设 454.2 的解析输入、原始 Möbius/plain 卷积 $b$、I2 的精确 primitive adjoint 以及实际 $G_P$。这些输入的解析条件在以下共同 $\eta$ 上成立；不调用定理 454.3、455.2、456.1 的旧充分预算条件。以下是原解析输入的 `repo-derived` 联合应用，不对中间的 Cauchy、平方部分计数或吸收方法另作原创性断言。

令

$$
U\asymp K,\quad L=K^\ell,\quad 0<\ell<1/1000,
\quad K^{1/2}\le D\le K^{1/2}L^{1/6-\delta},
\quad 0<\delta<1/6.
$$

取（456.1）的 $c,a_1,a_2,a_3,R_i$，并选择满足原固定 cusp spectral avoidance 的同一个固定

$$
\ell/2-\ell^2/2<\eta<\ell/2+\ell^2/2.
\tag{457.1}
$$

该开区间非空，固定商空间在 $1$ 以下的离散谱保证可选到所需 $\eta$。令 $e=E_P^*b$ 为原 adjoint 的完整 continuous 向量，包含 unchanged-numerator 项及精确有限反演的全部反射选择；令 $w=W_P^*b$ 为原 residue 向量。则对任意最终 $\varepsilon>0$，先分配内部小幂以后，

$$
e^*G_P^{-1}e
\ll\mathcal N^2K^{2-\ell^2/4+\varepsilon}.
\tag{457.2}
$$

$\mathcal N$ 是一次固定的原 profiles、finite cusp、Mellin、reciprocal-$L$ 与解析输入的共同成本包络，不按行、素标记或分支重选。对有界共同成本及充分小的 $\varepsilon$，H8 与（457.2）给出

$$
(w+e)^*G_P^{-1}(w+e)=o(K^2).
\tag{457.3}
$$

这里 H8 的 $w$ 保留自己的正节省，不赋予它指数 $\ell^2/4$。结论控制此平衡扇区中的完整指定素标记相干投影；它不控制正交补、全部标记、其他原长度与高度、原 growing-height allowance、F4 的不同列二次型或 signed Robin restoration。

证明。先在 [primitive-mean 源稿 v2](https://rstation.ai/api/v1/papers/riemann_hypothesis_10/versions/2/download) 的 Lemma 2、Proposition 3 证明内保留列平方范数的谱幂次。记 $h$ 为 good multiplier、$H=q_h$、$M=AB$、$Y_0=\sqrt M B$，仍用（454.7）的 $f$。在本证明中需要

$$
\frac1B\sum_{\substack{a\asymp A,b\asymp B\\ab\ {\rm sf},\ (ab,h)=1}}
|D_\nu(hab^3,1+\eta+it)|^2
\ll(HM)^\varepsilon(1+|t|)^6
\left[A+H^{1/2-\eta}Y_0^{-2\eta}M f(M,B)\right].
\tag{457.4}
$$

令 $q_n\asymp\Lambda$ 表示列 dyad；源稿（4.7）的列平方范数带 $\Lambda^{-2\eta}$。两个筛选择的共同常数项为 $A$，非恒定列幂次为 $1,1/3,5/6$，都大于 $2\eta$。保留这个因子作 dyadic 求和，常数项给出 $O_\eta(A)$，非恒定项给出它们在 smoothing length $Y$ 上的值乘 $Y^{-2\eta}$。源稿已支付的 $e,f,w$ 提取费用及缩短的指数截断不增加该界。

完成化的 $d$ 卷积也保持此结论：以 $q_d^{-1-6\eta}$ 作 Cauchy 权重，列幂次 $\beta\ge1/3$ 对应的 $d$ 和为 $\sum_dq_d^{-1-6\beta+6\eta}$，常数项对应 $\sum_dq_d^{-1-6\eta}$，均收敛。取源稿相同的

$$
Y=k_\eta\sqrt H Y_0(1+|t|)^5.
$$

每个非恒定列幂次至多为 $1$，所以它的费用至多是 $H^{1/2-\eta}Y_0^{-2\eta}$ 乘（454.7）以前的同一 sieve minimum，另含 $(1+|t|)^6$。以 $A$ 加这份正量归一化源稿（5.3）—（5.6）的 height supremum，反射项的吸收系数仍为固定常数乘 $k_\eta^{-4\eta}$。初始有限性沿用源稿（2.5）；同一 pole-cancelling kernel 消去可能的 theta pole。选择固定 $k_\eta$ 完成同一有限向量的吸收，最后除以有界的 $\zeta_S(6u-5)$，得到（457.4）。常数可依赖固定 $\eta$，不将其视为 $K$ 的幂；没有用 residue 周期性或新的标量 functional equation。

对 ideal $n$，记 $\Delta(n)$ 为满足 $n/\Delta(n)^2$ 平方自由的平方部分，$d(n)=q_{\Delta(n)}$。取 $\vartheta=1/2$，则 $6\eta<\vartheta<1$。对任意 prime ideal $p$ 及真实 annular 长度 $Y$，有

$$
\sum_{m\asymp Y}d(pm)^\vartheta\ll_\vartheta Y,
\qquad \sum_{m\asymp Y}d(m)^\vartheta\ll_\vartheta Y.
\tag{457.5}
$$

第一式用 $d(pm)^\vartheta\le\sum_{\Delta^2\mid pm}q_\Delta^\vartheta$。非空时的理想计数至多为 $Y/q_{\Delta^2/(\Delta^2,p)}$；$p$ 处 Euler 因子为

$$
1+\sum_{k\ge1}Q^{1+k(\vartheta-2)}
=1+\frac{Q^{\vartheta-1}}{1-Q^{\vartheta-2}},\qquad Q=q_p,
$$

一致有界，其余因子由 $\zeta_K(2-\vartheta)$ 控制。第二式是同一计数去掉特殊 $p$ 因子。非空有界 subunit annuli 沿用原固定扩大。

在正的 $D(hC^3n,u)$ 平方和中，$C\asymp X$ 平方自由、$n\asymp Z$ 不限平方自由。按原互素条件写

$$
n=a\Delta^2,\quad e=\gcd(a,\operatorname{rad}(h\Delta)),
\quad a=ea_0,\quad d=q_\Delta,\quad v=q_e,\quad s=d\sqrt v.
$$

对 multiplier $h\Delta^2e$、$A\asymp Z/(d^2v)$、$B\asymp X$ 使用（457.4）。在 $\Delta,e$ 求和以前，对角费用为 $XZ/(d^2v)$，第二份费用为

$$
H^{1/2-\eta}X^{2-3\eta}Z^{1-\eta}
 d^{-1}v^{-1/2}f(XZ/s^2,X).
\tag{457.6}
$$

$d,v$ 的谱幂次在 multiplier 与缩短之间恰好抵消。在这个正平方和上再乘 $d^{-\vartheta}$，而将反向权重放到原 pairing 的系数侧。需要的 elementary maximum 是

$$
B^{-6\eta}f(M,B)
\ll M^{-3\eta}+B^{-1/2-6\eta}.
\tag{457.7}
$$

当 $B\le\sqrt M$，对（454.7）的第二选择逐项估计；其中 $B/\sqrt M$ 与 $M^{-1/4}B^{1/2}$ 乘 $B^{-6\eta}$ 后因 $\eta<1/12$ 在 $B=\sqrt M$ 取得上界，另外两项由右侧第二项支付。当 $B\ge\sqrt M$，使用第三选择 $B^{-1}+\sqrt M/B$。在（457.6）中应用（457.7）引入 $s^{6\eta}$，因此 $\Delta$ 和的指数为 $-1-\vartheta+6\eta<-1$；$e$ 的因子 $v^{-1/2+3\eta}$ 只需除数界。该权重使原先可能为调和的平方部分求和收敛。

现在固定实际 $A_2,A_3,A_4,B_0$，仍取 $W=x_2^2x_3^3x_4^4z^6$、$H_0=A_2^2A_3$。对 $C\asymp X>R_1$，原反射标量的模保留为

$$
X^{-1/2-2\eta}\mathcal P_\eta,
\qquad
\mathcal P_\eta=
\prod_{j=2}^4x_j^{-1/2-(j+1)\eta}z^{-6\eta}.
\tag{457.8}
$$

低-$p$ 的 $j$ 支另有 $Q^{-1/2-(j+1)\eta}$，高支另有 $Q^{-6\eta}$。原 $b(h)$、全部 Gauss／混合字符相位、分母、mask 及外部共轭保持在实际 signed pairing 中，只有在正 Cauchy 范数处才使用其模。分母在固定 $\eta$ 下一致有界。

第一 $p$ 支的 $Y=K/(XW)$，numerator 是 $H_0C^3pm$。逐 $p$ 对 $(C,m)$ 作加权 Cauchy：系数侧用 $d(pm)^\vartheta$，$D$ 侧用其倒数。由（457.5），原系数平方质量至多为 $K^\varepsilon\mathcal N^2YX^{-4\eta}\mathcal P_\eta^2$。随后只在正 $D$ 平方和中合并 $n=pm$，表示重数为除数界，倒权重只依赖 $n$，实际 $(C,n)=1$；对 $Z=LY$ 使用（457.6）—（457.7）。有限 ray 分量统一处理，原 $p$-dependent 限制仅在这些正量中放松。

低-$p$ 的 $j=1$ 支使用另一种合并：系数侧权重为 $d(m)^\vartheta$，平方质量至多为 $K^\varepsilon\mathcal N^2YL^{-1-4\eta}X^{-4\eta}\mathcal P_\eta^2$；正平方和中合并平方自由 $b=pC\asymp LX$，保持表示重数和实际 $(b,m)=1$，再对 $B=LX,Z=Y$ 使用同一估计。两种合并分别证明其权重独立性，不把原系数替换成独立的优化向量。

汇总 $C$ dyads、全部实际 powerful 乘积并作同一范数的三角不等式以后，两支共有的标记向量平方费用至多为

$$
\begin{aligned}
&(KL)^\varepsilon(1+|t|)^J\mathcal N^2
\bigl[K^{2-4\eta}L^{1-4\eta}\\
&\hspace{20mm}+K^{2-\eta}L^{1-\eta}R_1^{-1/2-6\eta}
+K^2LR_1^{-1-4\eta}\bigr].
\end{aligned}
\tag{457.9}
$$

第一支在应用（457.7）以前的第二份费用为

$$
q_{H_0}^{1/2-\eta}(K/W)^{2-\eta}L^{1-\eta}X^{-6\eta}\mathcal P_\eta^2
\sum_{\Delta,e}d^{-1-\vartheta}v^{-1/2}
 f((LK/W)/s^2,X).
$$

低-$p$ 的 $j=1$ 支取 $B=LX$，用 $X^{-6\eta}=L^{6\eta}B^{-6\eta}$，其首项相同，第二项的 $L$ 幂为 $1/2-7\eta$、对角项的 $L$ 幂为 $-4\eta$，均由（457.9）控制。

原 powerful 乘积确实已求和：首项的平方权重为

$$
q_{H_0}^{1/2-\eta}W^{-2+4\eta}\mathcal P_\eta^2
=x_2^{-4}x_3^{-13/2+3\eta}x_4^{-9+6\eta}z^{-12+12\eta}.
$$

其平方根绝对可和；第二项的平方权重为 $x_2^{-4-6\eta}x_3^{-13/2-6\eta}x_4^{-9-6\eta}z^{-12-6\eta}$，对角项更强。实际有限和先作范数三角不等式，之后才扩大正 majorant，内部小幂保留可和性。

低-$p$ 的 $j=2,3,4$ 不合并标记；逐 $p$ 使用其自身 multiplier $p^{4-j}H_0$、长度 $K/(Q^{j-1}XW)$ 与（457.8）的实际 scalar。标记求和后的首项 $L$ 幂分别为 $-1-4\eta,-7/2-\eta,-6+2\eta$；第二项为 $4-5j/2-7\eta$，对角项为 $2-2j-2(j+1)\eta$，均由（457.9）控制。原全部 $j\ge6$ 高支使用 I14a 的同一个精确恒等式，三份 $L$ 幂为 $-9+8\eta,-9-7\eta,-9-12\eta$；valuation $5$ 没有第二支。因此（457.9）包含所有 $C>R_1$ 的模式，不限于原 $\mathrm T$ 或 $\mathrm T_{\rm rat}$，并保留任意 $m$ 平方部分和所有同时选中乘积。

对 $C\le R_1$，用（456.5）—（456.14）的完整有限变换及 Euler split；在 $x_2>R_2$ 或 $x_3>R_3$ 的 powerful 尾部继续用（454.13）的正界。这里要在 small box 中保留 [I11 的两个精确 cusp 标量](../../../Library/Analytic/faveri2026fixedorder.md#an-unchanged-numerator-term-in-the-primitive-continuous-adjoint)，而不把二者都放大成 $K/Q$。

低-$p$ 的 $j$ 支 incoming 标量为 $O(Q^{-1-6\eta})$，outgoing 标量为 $O(Q^{-1-j\eta})$，对应泛函大小分别为 $Y$、$Y^{1-\eta}$。代入 $Y=K/(Q^{j-1}xW)$，incoming 原变量质量由

$$
KQ^{-j-6\eta}\prod_{i=1}^4x_i^{-i-1-6\eta}z^{-6-6\eta}
$$

控制，outgoing 质量由 $K^{1-\eta}Q^{-j-\eta}\prod_{i=1}^4x_i^{-i-1}z^{-6}$ 控制；其中 $x_1=x$。两个 selected-ideal 和连原 $E_i,F$ 的除数损失都收敛。有限 Euler 密度仍用 I11 的 $\sum_g|z_u(g)|/q_{\operatorname{lcm}(d_0,g)}\ll q_{d_0}^{-1}$；两个 finite polar tails 已由（456.10）—（456.11）支付。于是 low-$p$ 主项共同由

$$
KQ^{-1-6\eta}+K^{1-\eta}Q^{-1-\eta}
\tag{457.10}
$$

控制。没有宣告任何 pole 为零。第一支与高支保留原固定字符 Möbius 位移 $KD^{-1/8}$ 及原移动删因子成本。全部原系数、相位和有限主项都在原卷积分解内处理。

恢复同一个原 Mellin 与实际 G7 后，原先合并成 $U^{2\eta}K^2/L$ 的 small-box polar 费用改为

$$
U^{2\eta}
\left[K^2L^{-1-12\eta}+K^{2-2\eta}L^{-1-2\eta}\right].
\tag{457.11}
$$

其余费用仍是（456.14）的误差、$K^2L(R_2^{-2}+R_3^{-9/2})$，以及 PR9／I9 的前三项。对无 mark 的第一支直接使用 I9；这属于包含单位 $C$ 的 small box，不另加一份 signed 副本。这样 $C>R_1$、$C\le R_1$ 的 powerful 尾部及其余 small box 恰好覆盖完整 continuous 向量。

最后核对同一个参数预算。当前范围有

$$
c>1/100,\quad c<1/70,\quad
 a_1<1/30,\quad a_2<1/120,\quad a_3<1/250,
$$

且 $\eta<1/1900<(1/8-\ell)/32$，

$$
4+24\ell+22a_1+20a_2+18a_3<5,
\qquad(4+24\ell+22a_1+20a_2+18a_3)\eta<c/2.
$$

因此 small-box 误差和 powerful 尾部仍有至少 $c/2$ 的节省。这里改变的是原定理的充分预算选择，不改变解析输入的 $\eta<1/12$ 或 spectral avoidance；H8 不要求 $\eta<\ell/8$。I9 的前三项继续满足其已验证裕度。

将真实外因子 $U^{2\eta}$ 乘回（457.9）、（457.11），临界首项和 incoming polar 的裕度分别为

$$
\begin{aligned}
r_{\rm crit}&=2\eta-(1-4\eta)\ell
>\ell^2(1-2\ell)>\ell^2/2,\\
r_{\rm in}&=(1+12\eta)\ell-2\eta>5\ell^2.
\end{aligned}
\tag{457.12}
$$

outgoing polar 的裕度为 $(1+2\eta)\ell>\ell$。（457.9）第二项的裕度至少为 $c+\ell/2-\eta>c-\ell^2/2>c/2$，对角项的裕度大于 $c$。其余费用保留上述固定正裕度。将全部内部小幂分配在这些同源裕度以内，原 Mellin 高度由同一 $\mathcal N$ 支付，得到（457.2）。在同一实际 inverse Gram 范数中与 H8 的 $w$ 使用三角不等式，即得（457.3）。证毕。

## 追加锚（本行以下为增补区）

## 458. Möbius 自卷积与无槽四矩的完整原系数预算

**定理 458.1（同一原卷积的完整行能量）。** 沿用 [H1 的固定物理表示及原零掩码](../../../Library/Analytic/faveri2026fixedorder.md#a-prime-labelled-residue-cut-for-the-original-unsplit-convolution)，工作于 F4 之前。以下是 `repo-derived` 的联合应用，解析前提为 de Faveri [Theorem 1.1](https://arxiv.org/abs/2610.04045v1)、原稿 `lem:plain` 的无槽情形及其既有 smooth-calculus/Sobolev 合同。[Xu–Sang v2，Theorem 2.2（2.5）及（6.3）](https://arxiv.org/html/2610.17675v2)也明确陈述所用无槽 plain 四矩；该文只允许粗素数卷积的 Proposition 7.2 不用作原 Möbius/plain 系数的供应。通用筛法、Cauchy 和除数估计仅是本条证明的既有工具，不分别列作新结果。本条没有本仓解析 Lean 认证或文献优先权断言。

固定原 Eisenstein 理想变量、坏素集合 $S$、有限 ray 数据、annular profiles 及其有限多项式高度合同。令 $q_a=Na$，$K=DN$，各长度在原解析输入允许的固定幂范围内。取原非负行权 $\Omega$，保留 $q_z\asymp U$ 的 good sixth-power-free 行，令

$$
\begin{aligned}
b(h)&=\omega(h)\sum_{dn=h}\mu(d)V(q_d/D)W(q_n/N),\\
(Ab)(z)&=\sqrt{\Omega(q_z/U)}\sum_h b(h)\chi_h(z),
\qquad Q(b)=\|Ab\|_2^2,\\
\Psi_6(U,X)&=U+X+U^{5/6}X^{1/3}+U^{1/3}X^{5/6}.
\end{aligned}
\tag{458.1}
$$

$h$ 不限平方自由或 sixth-power-free，不附加 $(d,n)=1$。$\omega$ 包含 H1 的全部固定相位、section 与有限过滤，$\chi$ 保持其原非单位零值。负 orientation 整体共轭，不在非单位处取倒数。固定有限 Fourier 分解以及必要的有限行分区，均按 H1 的固定 ray 合同执行。

每个 Fourier 分量及所需 profile 导数的 Möbius、plain 四矩成本，分别写成第四根因子 $C_{M,\xi}$、$C_{S,\xi}$；把 $\Omega$ 的固定有界权纳入这些因子。一次选择共同乘积包络

$$
\mathcal C\ge
\max\left\{1,\sum_\xi|c_\xi|C_{M,\xi}C_{S,\xi}\right\},
\tag{458.2}
$$

并支付原有限分区、smooth seminorm 与 Mellin/Sobolev 费用。这里的 $\mathcal C$ 控制两种第四根成本的乘积；不能把两个独立四矩成本各自改名为 $\mathcal C$，再漏掉乘积。它不按行、标签或范数重新选择，原 growing-height allowance 也不重新分配。

对任意最终 $\varepsilon>0$，先分配内部除数及 dyadic 小幂，有

$$
Q(b)\ll_\varepsilon
(UK)^\varepsilon\mathcal C^2 K
\sqrt{U\Psi_6(U,D^2)}.
\tag{458.3}
$$

因此对同一个行 Hilbert 空间中的任意实际正交投影 $P$，特别是定理 457.1 的实际素标记投影，

$$
\|(I-P)Ab\|_2^2
\le Q(b)
\ll_\varepsilon(UK)^\varepsilon\mathcal C^2 K
\sqrt{U\Psi_6(U,D^2)}.
\tag{458.4}
$$

这是完整原能量的上界，再由投影收缩控制补空间；没有从小投影推断完整范数小。既有的 $K\Psi_6(U,K)$ 原卷积界仍可与（458.3）取最小值，不作为新增结果重述。

证明。在每个固定有限分量上，精确写 $\omega(h)=\sum_\xi c_\xi\xi(h)$，包括原固定非单位处的零。对该分量令

$$
\begin{aligned}
\psi_z(a)&=\xi(a)\chi_a(z),\\
M_\xi(z)&=D^{-1/2}\sum_d\mu(d)V(q_d/D)\psi_z(d),\\
S_\xi(z)&=N^{-1/2}\sum_n W(q_n/N)\psi_z(n).
\end{aligned}
\tag{458.5}
$$

乘法性包含 collision zeros，故 $Ab_\xi=\sqrt\Omega K^{1/2}M_\xi S_\xi$。两因子在同一实际行上，使用同一字符、共同固定 mask 与原 profiles；没有独立优化两个系数向量。原 fixed-ray 族的 conductor 支持于固定 $S$ 数据；good 非单位 sixth-power-free 行至少有一个 $S$ 外素因子的 valuation 在 $1,\ldots,5$，所以 inducing character 非主。原有限例外按既有分解另计，不能删去 principal 极点；annular 大 $U$ 的当前 good 行不含单位。

展开 $M_\xi(z)^2$，而不是 $|M_\xi(z)|^2$：

$$
\begin{aligned}
M_\xi(z)^2&=\sum_a g_\xi(a)\chi_a(z),\\
g_\xi(a)&=D^{-1}\xi(a)
\sum_{d_1d_2=a}\mu(d_1)\mu(d_2)
 V(q_{d_1}/D)V(q_{d_2}/D).
\end{aligned}
\tag{458.6}
$$

每个非零 $\mu(d_i)$ 强迫 $d_i$ 平方自由，故 $v_p(a)\le2$，即 $a$ cube-free，从而 sixth-power-free；允许 $d_1,d_2$ 共享素因子。$q_a\asymp D^2$，除数界及理想计数给出

$$
\sum_a|g_\xi(a)|^2\ll_\varepsilon C_{M,\xi}^4D^\varepsilon.
$$

因此直接在真实的 cube-free 列支撑上使用 Theorem 1.1，经既有有限 ray-family 修正，得到

$$
\sum_z\Omega(q_z/U)|M_\xi(z)|^4
\ll_\varepsilon(UD)^\varepsilon C_{M,\xi}^4\Psi_6(U,D^2).
\tag{458.7}
$$

这里不需要不限列的第六次幂提取；添加 $U(D^2)^{1/6}$ 费用会丢掉实际 $\mu*\mu$ 支撑。原 $h=dn$ 仍不限重数，受限的是证明内平方多项式的新列 $a=d_1d_2$。

在相同非主 inducing 行上，无槽 plain product 估计取两个相同的 $N$，给出

$$
\sum_z\Omega(q_z/U)|S_\xi(z)|^4
\ll_\varepsilon(UK)^\varepsilon C_{S,\xi}^4U.
\tag{458.8}
$$

固定有限 ray twist 不增加 growing radical 费用；共同原零掩码仍在两个 plain 因子中。该输入不以新的无零区为前提，也不将 prime-only 结论迁移到任意卷积。

对同一批行使用带 $\Omega$ 的 Cauchy，得到

$$
\|Ab_\xi\|_2^2
\le K
\left(\sum_z\Omega|M_\xi|^4\right)^{1/2}
\left(\sum_z\Omega|S_\xi|^4\right)^{1/2}.
\tag{458.9}
$$

代入（458.7）—（458.8），再在同一个行范数中对原有限 Fourier 分量作三角不等式，使用（458.2），即得（458.3）。只在正范数处放大，全部原符号、相位、重叠素因子和零值已经由（458.5）精确保留。

上述筛应用先固定 row-independent profiles。原允许的有限维 smooth 参数选择，沿既有 Sobolev 论证对有限 profile 导数作同一估计；乘积导数产生有限个（458.6）型系数，仍有相同 cube-free 支撑与除数范数。实际行向量及其统一范数据此控制，所有高度费用留在同一次 $\mathcal C$ 中。与定理 457.1 合用时，必须取同一个实际原向量及共同 profile/height 合同，不能把分别取得的参数选择合并成一个实现。最后正交投影收缩给出（458.4）。证毕。

当 $D\le U^{1/4}$，四个筛项均为 $O(U)$，所以完整原能量及其实际补空间满足

$$
Q(b),\ \|(I-P)Ab\|_2^2
\ll_\varepsilon(UK)^\varepsilon\mathcal C^2 UK.
\tag{458.10}
$$

在 $U\asymp K$ 写 $D=K^d$、$N=K^{1-d}$，$0\le d\le1$，则（458.3）的幂次为

$$
J(d)=
\begin{cases}
2,&0\le d\le1/4,\\
23/12+d/3,&1/4\le d\le1/2,\\
5/3+5d/6,&1/2\le d\le1.
\end{cases}
\tag{458.11}
$$

特别地，$D=N=\sqrt K$ 时完整原矩及补空间为 $O(\mathcal C^2K^{25/12+\varepsilon})$，较既有通用原卷积公式的 $K^{13/6+\varepsilon}$ 改进 $1/12$。在定理 457.1 的同一扇区 $\sqrt K\le D\le\sqrt K L^{1/6-\delta}$、$L=K^\ell$，得到

$$
Q(b),\ \|(I-P)Ab\|_2^2
\ll_\varepsilon\mathcal C^2
K^{25/12+(5/36-5\delta/6)\ell+\varepsilon}.
\tag{458.12}
$$

把 $\mathcal C$ 一次扩大到也控制定理 457.1 的共同包络，在同一实际向量、该定理的有界共同成本及充分小 $\varepsilon$ 合同下，其投影是 $o(K^2)$，但（458.12）仍比 $K^2$ 高 $1/12+(5/36-5\delta/6)\ell$。该差额是本上界的预算缺口，不是实际补空间的下界；（458.10）在 $U\asymp K$ 也只有 $K^{2+\varepsilon}$，没有严格节省。其他原长度、高度、growing-height allowance、F4 的不同列二次型及 signed Robin restoration 仍需对应估计。本条不证明 RH 或全部 $n>5040$ 的严格 Robin 不等式。

## 追加锚（本行以下为增补区）
