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

## 459. 缓冲零点分箱下的完整原卷积联合估计

**定理 459.1（保留原逆因子的分箱联合预算）。** 沿用定理 458.1 的原 $b(h)$、行算子 $A$、$Q(b)=\|Ab\|_2^2$、固定有限 Fourier 表示、共同零掩码及 good sixth-power-free 非单位行。以下为 `repo-derived` 的完整原系数联合应用；承重解析输入是原稿 `lem:logarithmic-control`、`lem:deleted-euler-factors`、无槽 `lem:plain`，以及原 buffered-bin／detector-count 合同。后两份合同在 [Xu–Sang v2，Theorem 2.2、Lemma 6.2 及 Proposition 6.3](https://arxiv.org/html/2610.17675v2)有明确陈述。原逆矩、分箱计数、复分析和 Cauchy 均直接复用，不分别作为新增结果。本条不把只有 $\mu$ 系数的逆二矩套到 $\mu*\mu$ 上，也不使用该文 prime-only 的 Proposition 7.2。

固定 $U\asymp K$、$D=N=\sqrt K$。Profiles 支撑于原固定 annuli，并有下文所需有限阶有界 seminorms；norm-twist 高度固定。也允许实际 seminorm 和高度成本为 $U^{o(1)}$ 的 polylog 参数，但不据此认证原来更大的 growing-height allowance。原有限实参数或 smooth 选择只在同一固定 profile/height 合同下恢复。共同有限字符族 $\mathcal X_z$ 包含原 H1 的每一个 Fourier presentation；它不随 $U$ 扩张。

对每个 Fourier 分量，记 $C_{M,\xi}$ 为下文原逆多项式逐行界的 profile 成本，$C_{S,\xi}$ 为原 plain 四矩成本的第四根，选择一次共同乘积包络

$$
\mathcal C\ge\max\left\{1,
\sum_\xi|c_\xi|C_{M,\xi}C_{S,\xi}\right\}.
\tag{459.1}
$$

原有限行分区、行权及所需的有限分离／Sobolev 费用都包含在其中，不按行、分箱或标签重新分配。令

$$
\kappa_{\mathrm{joint}}=\frac{49-10\sqrt6}{12}.
\tag{459.2}
$$

则对任意最终 $\varepsilon>0$，在所列解析输入下，完整原行能量及任意实际正交投影 $P$ 的补空间满足

$$
\begin{aligned}
Q(b)&\ll_\varepsilon\mathcal C^2
 K^{\kappa_{\mathrm{joint}}+\varepsilon},\\
\|(I-P)Ab\|_2^2&\le Q(b).
\end{aligned}
\tag{459.3}
$$

在同一有界或相应次幂成本口径下，这把定理 458.1 在该平衡点的上界幂次再降低

$$
\frac{25}{12}-\kappa_{\mathrm{joint}}
=\frac{5\sqrt6-12}{6}>0.
\tag{459.4}
$$

若改取定理 457.1 的同一扇区 $L=K^\ell$、$\sqrt K\le D\le\sqrt K L^{1/6-\delta_{457}}$、$N=K/D$，仍在本条明确的 profile/height 范围，则完整原能量和补空间满足

$$
Q(b),\ \|(I-P)Ab\|_2^2
\ll_\varepsilon\mathcal C^2
K^{\kappa_{\mathrm{joint}}+(1/6-\delta_{457})\ell+\varepsilon}.
\tag{459.5}
$$

证明。先固定一个原 Fourier 分量，使用（458.5）的同一个 $\psi_z$、$M_\xi$、$S_\xi$。乘法性包含零值，所以 $Ab_\xi=\sqrt\Omega K^{1/2}M_\xi S_\xi$，原 $h=dn$ 不限重数，也没有增加 $(d,n)=1$。下述各项属于同一实际行和同一个原向量。

取原 floor $a_0=51/100$，选小的固定分箱宽度 $e>0$，再使用原有的高度顺序选 $H_1=U^\tau$。令 $M_j(z)$ 是 $\mathcal X_z$ 中所有 primitive inducing $L$-函数在 $|\Im\rho|\le3jH_1$、$\Re\rho\ge a_0$ 的最大零点实部，并与 $a_0$ 取最大值。原共同分箱给出有限个 $\mathcal B_{i,a}$，满足

$$
a\le M_i(z)<a+e,\qquad M_{i+1}(z)<a+2e.
\tag{459.6}
$$

每个 $\xi$ 都包含在这份共同最大值中。Floor 行有 $O(U)$ 个；其余行由原计数合同满足

$$
\#\mathcal B_{i,a}\ll_\varepsilon U^{\mathcal R(a)+\varepsilon},
\qquad
\mathcal R(a)=
\begin{cases}
(31-32a)/(21-12a),&a_0<a\le11/12,\\
2(1-a),&11/12\le a\le1.
\end{cases}
\tag{459.7}
$$

此计数保留全部 good sixth-power-free 行，含字符阶数严格整除六的行；不是素行或仅平方自由行的计数。固定有限 ray 与原 masks 按同一算术数据合同处理，不将移动 ray 群并入固定常数。

关键是逐行控制原逆因子。固定 $z\in\mathcal B_{i,a}$，在绝对收敛线使用其原完整逆级数：

$$
M_\xi(z)=\frac{D^{-1/2}}{2\pi i}
\int_{(2)}\frac{D^s\widehat V(s)}
 {L_{\mathrm{orig}}(s,\psi_z)}\,ds.
\tag{459.8}
$$

$L_{\mathrm{orig}}$ 包含原删因子，故这里的系数正是原 $\mu(d)\psi_z(d)$。不在移线前去掉原零掩码。原 fixed-$S$ 字符不能消去 good 非单位行在 $S$ 外 valuation $1,\ldots,5$ 的非平凡局部字符，因而这些行非主；principal 来源不在当前行族中，既有例外处理中的贡献仍按其原合同保留。

截断在 $H=H_1/4$，只把该有限线段移至 $\Re s=a+8e$。先运输原固定 norm twist，再应用（459.6）的缓冲：以 $2+it$ 为中心、半径 $2-a-2e$ 的所需圆盘无零。原 logarithmic-control 在较小圆盘上给出的正是 $|L|+|1/L|\ll U^\varepsilon$，不只是 $L'/L$ 的对数界。Conductor 与完整删除 radical 的 norm 均为 $O(U)$，原 deleted-euler-factors 同时控制这些因子及其倒数，所以原完整 $1/L_{\mathrm{orig}}$ 在实际有限矩形中也是次幂有界。固定／polylog 高度在足够大 $U$ 时处于这份缓冲内部。

高度与导数的次序保留原合同：先固定分箱损失、内部 moment 及参数 Sobolev 的有限阶，再选足够小的 $\tau$ 支付其固定多项式高度费用；最后选外部 Mellin-tail 阶数 $J$。对原限定的 $D\le U^{O(1)}$，令 $J$ 足够大，使绝对线上的尾部和有限水平 joins 均为 $O(U^{-10})$。提高这份外部阶数只提高 $V$ 所需的有限 seminorm，不重新提高已经支付的内部高度指数。固定 norm twists 先平移到 $L$ 的高度参数，不能对其导数反复收取新的 growing-height 费用。移线后不把新纵线延伸到无缓冲的无限高度。

因此，对同一个原分量和实际行，

$$
|M_\xi(z)|^2
\ll_\varepsilon U^\varepsilon C_{M,\xi}^2
 D^{2a-1+16e}+O(U^{-10}).
\tag{459.9}
$$

有限单位或有界大小的原例外使用既有分解；annular 大 $U$ 的当前 good 非单位行不包含它们。这里没有先证一个新逆四矩，也没有把 witness 下界当成逐行上界。

在同一个分箱中，只对 plain 因子使用带原 $\Omega$ 的 Cauchy。原无槽四矩对当前真实 $N$ 与固定 $\xi$ 给出

$$
\begin{aligned}
\sum_{z\in\mathcal B_{i,a}}\Omega|M_\xi S_\xi|^2
&\ll U^\varepsilon C_{M,\xi}^2D^{2a-1+16e}
 \left(\#\mathcal B_{i,a}\sum_{z\in\mathcal B_{i,a}}
 \Omega|S_\xi|^4\right)^{1/2}\\
&\ll U^\varepsilon(C_{M,\xi}C_{S,\xi})^2
 D^{2a-1+16e}U^{(1+\mathcal R(a))/2}.
\end{aligned}
\tag{459.10}
$$

$\Omega$ 的固定有界质量已纳入成本。Tail 的正贡献由原多项式大小及 $O(U^{-10})$ 支付。Floor 使用相同论证和 $\#\mathcal B_{i,a_0}=O(U)$。然后在同一个行范数中恢复全部有限 Fourier 分量、分箱及原行分区，使用（459.1）；没有把分别可达的系数或不同来源的最优值合并。

在精确平衡点，先令 $e$ 和内部小幂适配最终 $\varepsilon$，再乘回原 $K$。写 $\delta=2a-1$，上方分箱的 raw 能量幂次为

$$
\frac32+\frac12\{R(\delta)+\delta\},
\qquad
R(\delta)=
\begin{cases}
(15-16\delta)/(15-6\delta),&1/50<\delta\le5/6,\\
1-\delta,&5/6\le\delta\le1.
\end{cases}
\tag{459.11}
$$

第一段 $R(\delta)=8/3-25/(15-6\delta)$，故 $R(\delta)+\delta$ 的导数是 $1-150/(15-6\delta)^2$。它在

$$
\delta_*=(15-5\sqrt6)/6,
\qquad R(\delta_*)+\delta_*=(31-10\sqrt6)/6
\tag{459.12}
$$

取得最大值；$\delta_*\in(1/50,5/6)$。第二段之和恒为 $1$；floor 的 raw 幂次为 $201/100<\kappa_{\mathrm{joint}}$。有限分箱总数不随 $U$ 增加，因此（459.11）—（459.12）给出（459.3）的完整能量界。实际正交投影是收缩，遂同时控制其补空间。

在（459.5）的扇区，写 $D=\sqrt K K^\theta$，$0\le\theta\le(1/6-\delta_{457})\ell$，仍取实际 $N=K/D$。原 plain 四矩在该真实长度范围内统一成立。因为 $0\le2a-1\le1$，（459.10）相对于平衡点额外至多支付 $K^\theta$；floor 额外只有 $K^{\theta/50}$，同样被所列幂次覆盖。由此得到（459.5），没有重新优化一个独立系数向量。证毕。

当前上界的平衡点差额仍是

$$
\kappa_{\mathrm{joint}}-2
=\frac{25-10\sqrt6}{12}>0.
\tag{459.13}
$$

它是本估计距离目标 $K^2$ 的幂次差额，不是实际补空间的下界。只有在定理 457.1 的有界共同成本、充分小损失、同一实际向量及共同 profile/height 合同都满足时，才可同时保留其指定素标记投影的 $o(K^2)$ 结论；（459.3）并未将补空间降到 $K^2$ 以下。其他原长度和高度、原 growing-height allowance、F4 的不同列二次型以及 signed Robin restoration 仍需对应估计。本条没有新增零密度、RH 或全部 $n>5040$ 的严格 Robin 结论，也没有本仓解析 Lean 认证或文献优先权断言。

相近的既有 mollified second-moment 方法仍按其范围复用。[David–de Faveri–Dunn–Stucky v3，§1.2 的（1.8）、（1.26）—（1.27）](https://arxiv.org/html/2410.03048v3)处理平方自由三次字符的 central $L$-值及其 mollifier；其 power-saving asymptotic 使用 $M\ll X^{1/6-\delta}$。它不直接给出本条六次字符原 annular $\mu$／plain 向量在 $D=N\asymp\sqrt U$ 时的完整联合界，不能把不同阶数、central-value 来源及长度条件删去。这里新增的是上述原向量的完整组合消费，所用分箱、次幂逆界及 plain 四矩本身都是既有输入。

## 追加锚（本行以下为增补区）

## 460. 全部六次幂自由标记的原卷积投影预算

**定理 460.1（保留六次幂重叠的共同投影）。** 沿用 [G7、H1—H5](../../../Library/Analytic/faveri2026fixedorder.md#actual-gauss-compression-on-all-original-column-packets) 的实际 Gauss 行族、固定坏素集合 $S$、乘法 primary 约定、全部有限 ray sections、相位及零掩码。取原不拆分列向量

$$
b(h)=\omega_j(h)\sum_{dn=h}\mu(d)V(q_d/D)W(q_n/N),
\qquad K=DN,
\tag{460.1}
$$

其中 $h$ 不限重数，也不要求 $(d,n)=1$。负 orientation 同时共轭整个族。令 $D,N\ge1$、$L\ge1$、$2L\le D$，并固定 $0<\bar\varkappa<1/3$ 使 $L\le U^{1/3-\bar\varkappa}$。精确定义 $\mathcal L_L=\{R:R\text{ good、sixth-power-free},\ q_R\le L\}$；$V_L$ 的列为 G7 的实际 $v_R$，$G_L=V_L^*V_L$，$P_L=V_LG_L^{-1}V_L^*$。行算子 $A$ 保留原 good sixth-power-free 行和全部列；$v_R$ 在非平方自由行上为零。

定义实际极点矩阵和二次型

$$
\begin{aligned}
\mathsf W_L(h,R)&=U^{1/6}\widehat\Omega(2/3)
 \rho_{\mathrm{prim},\nu_{[h]};S}(hR),\\
Q_{\rho,L}(b)&=(\mathsf W_L^*b)^*G_L^{-1}(\mathsf W_L^*b).
\end{aligned}
\tag{460.2}
$$

假设 H5 的固定形式输入、H6 的同一 $B_0=7/8$ 固定字符 inverse-$L$ 输入以及 [primitive-mean 原稿 v2，§7、Corollary 5](https://rstation.ai/api/v1/papers/riemann_hypothesis_10/versions/2/download) 的输入成立。共同包络 $\mathcal N\ge1$ 包含这些固定有限族的常数、所需有限阶 profile seminorms、原固定 twists、共同 Mellin 分离变换及 reciprocal-strip 成本，并覆盖实际推导中这些费用的有限乘积和，不按标签或除数重新选择。则对充分大的原尺度和任意最终 $\varepsilon>0$，

$$
\begin{aligned}
Q_{\rho,L}(b)\ll_\varepsilon{}&
\mathcal N^2(UKL)^\varepsilon U^{1/3}
\left(K^{5/3}D^{-1/4}L^{2/3}
      +K^{2/3}D^2L^{5/3}\right),\\
\|P_LAb\|_2^2\ll_\varepsilon{}&
\mathcal N^2(UKL)^\varepsilon
\left\{U^{1/3}
\left(K^{5/3}D^{-1/4}L^{2/3}
      +K^{2/3}D^2L^{5/3}\right)+K^2L^{3/2}\right\}.
\end{aligned}
\tag{460.3}
$$

这是一条 `repo-derived` 的原系数组合估计。H5、极点留数的六次幂周期律、primitive density、共同 Gram 条件与原 unrestricted adjoint 直接复用；不将它们另立为新结果。新增消费覆盖全部 $\mathcal L_L$，包括 $v_p(R)=5$ 且 $p\mid d$ 的分支。

证明。对每个 $R$ 定义原 coherent 配对

$$
T_R=\sum_h b(h)
 \overline{\rho_{\mathrm{prim},\nu_{[h]};S}(Rh)}.
\tag{460.4}
$$

在 H2 中把 $p^{-1}\bmod B$ 换成 $R^{-1}\bmod B$，所有 original masks 仍包含于固定函数 $\phi_{R,j,\tau}$。$R$ 与固定 $B$ 互素，故这仍只置换同一个固定有限函数族，没有 growing conductor。对 $m=Rdn$ 使用 H3 的完全相同原配对及共同 Mellin 分离。其总 norm 尺度为 $Y=q_RK$；分离后外变量只有原 $d$ 的 smooth profile，内部是 $R d\mid m$ 的 H5 型和。原有限因子若需要 character 分解，仍属于 H6 的同一固定族。

先处理 H5 不能直接覆盖的六次幂指数。以下只在极点留数上使用 [averaged Type-I 原稿 v1，（2.6）、（3.3）](https://rstation.ai/api/v1/papers/riemann_hypothesis_8/versions/1/download) 及 H4 的固定额外排除版本：

$$
\rho_{\mathrm{full},\tau;S}(c^6m)
=\rho_{\mathrm{full},\tau;S}(m),\qquad
\rho_{\mathrm{prim},\tau;S}(m)=w_S(m)
 \rho_{\mathrm{full},\tau;S}(m),\qquad
w_S(m)=\prod_{p\mid m}\frac{q_p}{q_p+1}.
\tag{460.5}
$$

对 good squarefree $c$，两式直接给出精确有限密度展开

$$
\rho_{\mathrm{prim},\tau;S}(c^6m)
=w_S(c)\sum_{k\mid c}\frac{\mathbf1_{k\mid m}}{q_k}
 \rho_{\mathrm{prim},\tau;S}(m).
\tag{460.6}
$$

确实，每个 $p\mid c$ 的乘子在 $p\nmid m$ 时为 $q_p/(q_p+1)$，在 $p\mid m$ 时为 $1$。这里没有对离开极点的 primitive 或 full series 使用周期律，也没有删去 principal sixth-power 项。

若 $a=a_0c^6$，其中 $a_0$ sixth-power-free、$c$ squarefree 且 $(a_0,c)=1$，置 $Y'=Y/q_c^6$、$\phi_c(m)=\phi(c^6m)$。由（460.6），原 progression 和恰为

$$
w_S(c)\sum_{k\mid c}\frac1{q_k}
\sum_{a_0k\mid m}\phi_c(m)\rho_{\mathrm{prim},\tau;S}(m)
 \mathcal W(q_m/Y').
\tag{460.7}
$$

每一个 $a_0k$ 仍 sixth-power-free，可直接应用 H5；$\phi_c$ 仍只属于固定模 $B$ 上的有限函数族。记 H5 的主项常数为 $C_{\tau,Q,\phi_c}$，保留它对 $c\bmod B$ 的依赖。因 $v$ 在平方自由理想上乘法，且

$$
\frac{q_p}{q_p+1}\left(1+\frac{v(p)}{q_p^2}\right)=v(p),
\qquad
w_S(c)\sum_{k\mid c}\frac1{q_k}=1,
\tag{460.8}
$$

（460.7）的主项与误差分别是

$$
\begin{aligned}
&C_{\tau,Q,\phi_c}Z_S Y^{5/6}\widehat{\mathcal W}(5/6)
 \frac{q_c\,v(\operatorname{rad}a)}{q_a},\\
&O_\varepsilon\left((Yq_a)^\varepsilon
 Y^{1/3}q_c^{-2}\right).
\end{aligned}
\tag{460.9}
$$

此处 $Y'\ge1$ 的条件在下述应用中成立。与把 $a$ 当成 sixth-power-free 的错误代入相比，主项保留了必要的 $q_c$ 增益。

现在按同一个原 Möbius 变量分解

$$
\begin{aligned}
g&=(d,\operatorname{rad}R),&d&=ge,&(e,R)&=1,\\
R_5&=\prod_{v_p(R)=5}p,&c&=(g,R_5),&
a_0&=(Rg/c^6)e.
\end{aligned}
\tag{460.10}
$$

Möbius support 保证 $g,e$ 平方自由且互素。$Rd=a_0c^6$，$a_0$ 的每个指数至多为5，且 $(a_0,c)=1$，所以（460.9）包含每一个重叠。由 $q_c^5\le q_R\le L$ 及 $K\ge D\ge2L$，有 $Y'=q_RK/q_c^6\ge K/L^{1/5}\ge1$。不约化原 $h$ 的估值，也不改变其列掩码。

固定 $R,g$ 后，主项常数及 $c$ 都与 $e$ 无关。只对实际 $e\asymp D/q_g$ 的 Möbius 和使用 H6 原固定字符输入：

$$
\sum_{(e,RS)=1}\frac{\mu(e)v(e)\xi(e)}{q_e}
 V_*(q_e/(D/q_g))
\ll\mathcal N(D/q_g)^{-1/8+\varepsilon}q_R^\varepsilon.
\tag{460.11}
$$

新增的算术删除只是原固定字符 Euler product 中 $p\mid R$ 的因子，其正向及倒数在 $B_0+\varepsilon$ 线上均为 $q_R^\varepsilon$ 成本；不把它当作 changing ray level。所需 $v(p)=1+O(q_p^{-1})$ 的 Euler 修正与 H6 相同。共同 Mellin 分离后仍使用这份同一包络。

（460.9）的误差在每个 $g$ 分支至多有 $O(D/q_g)$ 个 $e$。因此完整 coherent 和满足

$$
\begin{aligned}
|T_R|\ll{}&\mathcal N(Kq_R)^\varepsilon\left\{
K^{5/6}D^{-1/8}q_R^{-1/6}
 \sum_{g\mid\operatorname{rad}R}\frac{q_{(g,R_5)}}{q_g^{7/8}}
 +K^{1/3}Dq_R^{1/3}
 \sum_{g\mid\operatorname{rad}R}
  \frac1{q_gq_{(g,R_5)}^2}\right\}\\
\ll{}&\mathcal N(Kq_R)^\varepsilon
\left(K^{5/6}D^{-1/8}q_R^{-1/6}q_{R_5}^{1/8}
      +K^{1/3}Dq_R^{1/3}\right).
\end{aligned}
\tag{460.12}
$$

最后一步逐素使用 $1+q_p^{-7/8}$，而 $p\mid R_5$ 时使用 $1+q_p^{1/8}$；剩余有限除数乘积由次幂界支付。六次幂主项的增益没有在除数和中被丢弃。

在平方之前已对原 $h$ 作 coherent 求和。随后只需正标签和。写 $R=R_0s^5$，$s=R_5$，放宽互素及 fifth-power-free 限制以取得上界。固定域的理想计数给出

$$
\begin{aligned}
\sum_{R\in\mathcal L_L}q_R^{-1/3}q_{R_5}^{1/4}
&\le\sum_{q_s^5\le L}q_s^{-5/3+1/4}
       \sum_{q_{R_0}\le L/q_s^5}q_{R_0}^{-1/3}\\
&\ll L^{2/3}\sum_s q_s^{-19/4}\ll L^{2/3},\\
\sum_{R\in\mathcal L_L}q_R^{2/3}&\ll L^{5/3}.
\end{aligned}
\tag{460.13}
$$

G7 供给同一个实际 $G_L^{-1}$ 的范数界；将（460.12）平方，使用（460.13）及 $\mathsf W_L$ 的 $U^{1/6}$ 因子，得到（460.3）的第一式。没有将不同标签视为正交，也没有用 upper sieve bound 代替 Gram 下界。

对于第二式，直接用 primitive-mean v2 的 unrestricted-column Corollary 5：

$$
A^*V_L=\mathsf W_L+E_L,\qquad
\|E_L\|_{\mathrm{HS}}^2
\ll(UKL)^\varepsilon K\sum_{q_R\le L}q_R^{1/2}
\ll(UKL)^\varepsilon KL^{3/2}.
\tag{460.14}
$$

非平方自由行上的 $v_R$ 为零，故原较大行空间的 adjoint 与该原稿 §7 完全相同；这里不从 G9 的平方自由列范围外推。原列向量的除数界给出 $\|b\|_2^2\ll\mathcal N^2K^{1+\varepsilon}$。因此

$$
\begin{aligned}
\|P_LAb\|_2^2
&=\|G_L^{-1/2}(\mathsf W_L+E_L)^*b\|_2^2\\
&\le2Q_{\rho,L}(b)
 +2\|G_L^{-1}\|\,\|E_L\|_{\mathrm{HS}}^2\|b\|_2^2,
\end{aligned}
\tag{460.15}
$$

从而得到第二式。全部原列和标签均在同一实际向量上，既没有先取逐列绝对值的 residue majorant，也没有把独立可达的向量最优值拼接。证毕。

**推论 460.2（平衡点与完整能量的严格比较）。** 在定理 460.1 的同一条件和有界共同成本下，取 $U\asymp K$、$D=N=\sqrt K$、$L=K^\ell$。若固定 $\ell>0$ 满足共同 Gram 范围，则

$$
\begin{aligned}
Q_{\rho,L}(b)&\ll_\varepsilon\mathcal N^2K^\varepsilon
 (K^{15/8}L^{2/3}+K^2L^{5/3}),\\
\|P_LAb\|_2^2&\ll_\varepsilon
 \mathcal N^2K^{2+5\ell/3+\varepsilon}.
\end{aligned}
\tag{460.16}
$$

若同时满足定理 459.1，使用一次共同包络 $\mathcal H\ge\max\{\mathcal N,\mathcal C\}$。当

$$
0<\ell<\frac{25-10\sqrt6}{20},
\tag{460.17}
$$

当前全部标记投影的幂次上界严格小于从（459.3）直接得到的 $\kappa_{\mathrm{joint}}$；差额为

$$
\kappa_{\mathrm{joint}}-(2+5\ell/3)
=\frac{25-10\sqrt6}{12}-\frac{5\ell}3>0.
\tag{460.18}
$$

最终 $\varepsilon$ 取小于这个正差额；所有组合成本由上述同一个 $\mathcal H$ 支付。改进的对象是由（459.3）整体能量直接继承的该投影界。

证明。把平衡尺度代入（460.3）；第一项的 $K$ 幂为 $1/3+5/3-1/8=15/8$，第二项为 $2$，余项为 $K^2L^{3/2}$。因 $K,L\ge1$，前者和余项都被 $K^2L^{5/3}$ 吸收，得到（460.16）。再直接比较（459.2）的幂次即得（460.18）。证毕。

在相同固定或 polylog 次幂成本合同下，（460.3）保留全部六次幂自由标签，但其 $2+5\ell/3$ 仍高于 $2$。既有定理 457.1 对指定素标签的更强结论不被替换。原恒等式

$$
\|Ab\|_2^2=\|P_LAb\|_2^2+\|(I-P_L)Ab\|_2^2
\tag{460.19}
$$

仍需对同一完整补空间给出更强上界；（459.3）对它的 $K^{\kappa_{\mathrm{joint}}+\varepsilon}$ 预算没有因本条而降低。其他原长度、高度、growing-height allowance、F4 的不同列二次型及 signed Robin restoration 也不由（460.3）推出。

## 追加锚（本行以下为增补区）

## 461. 算子尾部与短核心的更细标记切面

**定理 461.1（全部小标记的平方自由行 Gram）。** 使用 [G1–G7 的同一行空间、标记、零值、固定有限 ray 约定及对角矩阵](../../../Library/Analytic/faveri2026fixedorder.md#the-actual-gram-including-all-original-zeros)。标记恰好为所有 good sixth-power-free 理想 $q_R\le L$，不把同一理想的单位代表重复计入。假设 de Faveri [Theorem 1.1、Lemma 3.1、Lemma 6.1](https://arxiv.org/abs/2610.04045v1) 的解析输入成立。固定 $0<\kappa<1/2$。对任意 $\varepsilon>0$，在

$$
1\le L\le U^{1/2-\kappa}
$$

及充分大 $U$ 上，同一个实际 $G=V^*V$ 满足

$$
\|G-D_L\|
\ll_{\kappa,\varepsilon,\Omega,S}(UL)^\varepsilon U^{-1/2}L.
\tag{461.1}
$$

进而

$$
G>0,\qquad \|G\|+\|G^{-1}\|
\ll_{\kappa,\varepsilon,\Omega,S}(UL)^\varepsilon.
\tag{461.2}
$$

这里 $\Omega$ 是固定非零、非负、光滑 annular 行权；常数只使用其有限阶 seminorms 及 $C_\Omega^{-1}$。本条是所引大筛、完整字符 Poisson 与同一个实际 Gram 的联合应用，标为 `repo-derived`；不把通用 Poisson、理想计数或既有 G1–G7 另立为新结果。

证明。令 $q_a=Na$。原 Gauss 因子在 $G$ 中抵消。对任意标记系数向量 $c$，逐项展开平方自由行，得到精确有限式

$$
\langle Gc,c\rangle
=\frac1U\sum_a\mu(a)\sum_b
\Omega(q_a^2q_b/U)
\left|\sum_{R\in\mathcal R_L}c_R\overline{\chi_{a^2b}(R)}\right|^2.
\tag{461.3}
$$

$a,b$ 仍为 good 理想；$q_a\ll\sqrt U$。乘法性包括零值，故内层标记系数恰为 $c_R\overline{\chi_{a^2}(R)}$，其平方范数不超过 $\|c\|_2^2$。不增加 $(a,b)=1$ 或 $(a,R)=1$；原来为零的项继续为零。

先复用完整有限 Hecke 字符的光滑 Poisson 估计。设 $\xi$ 非主、primitive conductor 为 $\mathfrak f$，完整零延拓模数为 $\mathfrak q$，无限型平凡。对任意固定 $B>0$，de Faveri Lemma 3.1 及其变换的快速衰减给出

$$
\left|\sum_b\xi(b)\Omega(q_b/Y)\right|
\ll_{B,\epsilon_1,\Omega,S}
q_{\mathfrak f}^{1/2}q_{\mathfrak q}^{\epsilon_1}
\left(\frac{q_{\mathfrak q}}Y\right)^B.
\tag{461.4}
$$

这里只在 $Y/q_{\mathfrak q}$ 有固定正幂裕度时使用。具体地，primitive Poisson 的外因子为 $Y/\sqrt{q_{\mathfrak f}}$，dual scale 为 $q_{\mathfrak f}/Y$；取变换衰减阶数 $B+1>1$ 并用收敛的理想和，得到 $q_{\mathfrak f}^{1/2}(q_{\mathfrak f}/Y)^B$。对额外 zero-only primes 作有限 Möbius 展开，$b=dm$ 将尺度改为 $Y/q_d$，且 $q_{\mathfrak f}q_d\le q_{\mathfrak q}$；除数损失由 $q_{\mathfrak q}^{\epsilon_1}$ 支付。所有固定有限 primary/ray 分量均按 G6 的原约定处理。Lemma 3.1 对其允许的 profile 线性适配到 $\Omega$；不引入新的移动 ray 导子。

选小的固定 $\delta>0$，令

$$
A=U^{1/2-\delta}/L,\qquad 0<\delta<\kappa/2.
\tag{461.5}
$$

先在（461.3）中只取 $q_a\le A$。若 $R\ne T$，G6 已核对该比值是非主有限 Hecke 字符，并且其 primitive conductor 与保留 zero-only primes 的完整模数都为 $O_S(L^2)$。此时 $Y=U/q_a^2\ge L^2U^{2\delta}$。由（461.4），取足够大的固定 $B$，短 $a$ 段的全部非对角项在算子范数中为 $O(U^{-10})$：标记对用 $\|c\|_1^2\ll L\|c\|_2^2$，再支付 $O(A)$ 个 $a$。$B$ 只依赖固定损失和参数范围。

对角项直接复用 G5 的 principal 陈述。其截断主项为

$$
 d_R^{(A)}=
 \operatorname{Res}_{s=1}\zeta_F(s)
 \frac{\varphi_F(\mathfrak q_R)}{q_{\mathfrak q_R}}
 \left(\int_0^\infty\Omega(y)\,dy\right)
 \sum_{\substack{q_a\le A\\(a,SR)=1}}\frac{\mu(a)}{q_a^2},
\tag{461.6}
$$

其中 $\mathfrak q_R$ 的素支撑为 $SR$，使用 G3 相同的完整零掩码。Euler 乘积给出完整主项 $d_R$，且 $|d_R^{(A)}-d_R|\ll A^{-1}$ 一致成立。G5 的对角误差求和为 $O((UL)^{\epsilon_1}U^{-1/2})$。这一段保留全部对角密度，不由大筛上界推断下界。

现在估计 $q_a>A$ 的完整算子尾部。直接在正平方范数中使用 de Faveri Lemma 6.1 与 Theorem 1.1：对任意 good 标记向量 $u$ 及真实行尺度 $T$，

$$
\sum_b\Omega(q_b/T)
\left|\sum_{R\in\mathcal R_L}u_R\overline{\chi_b(R)}\right|^2
\ll(TL)^{\epsilon_1}\|u\|_2^2
\left(T+T^{1/6}L+T^{5/6}L^{1/3}+T^{1/3}L^{5/6}\right).
\tag{461.7}
$$

这里 $b$ 不限平方自由或 sixth-power-free。整体共轭及系数共轭将这一范数送到原筛族。Lemma 6.1 提供的量为 $\max_{1\le r\ll T^{1/6}}r\mathscr F_6(T/r^6,L)$，逐项取最大值正好给出（461.7）。分解 $b=b_0v^6$ 时 $\chi_{v^6}(R)$ 只是原系数中的 zero-only mask；每个 $v$ 的系数平方范数不增加。有限 reciprocity 分区沿用原筛族。非空有界 subunit 行尺度用固定 annular 扩大，不造成新的幂损失。

尾部的 $\mu(a)$ 可以取绝对值，因为此处只求同一个 Hermitian 尾算子的范数上界。对（461.7）代入 $T=U/q_a^2$，利用固定域理想计数，得到

$$
\begin{aligned}
\|G_{>A}\|\ll(UL)^{\epsilon_2}
\bigl(&A^{-1}+U^{-1/2}L\\
 &+U^{-1/6}L^{1/3}A^{-2/3}
 +U^{-1/2}L^{5/6}\bigr).
\end{aligned}
\tag{461.8}
$$

例如四项分别来自 $U\sum_{q_a>A}q_a^{-2}$、$U^{1/6}L\sum_{q_a\ll\sqrt U}q_a^{-1/3}$、$U^{5/6}L^{1/3}\sum_{q_a>A}q_a^{-5/3}$ 及 $U^{1/3}L^{5/6}\sum_{q_a\ll\sqrt U}q_a^{-2/3}$，最后共同除以 $U$。此处以整体正平方和控制尾部，不对每个标记对再作绝对行和。

将（461.5）代入，右边由 $(UL)^{\epsilon_2}U^{-1/2+\delta}L$ 控制。先选 $\delta$ 与全部内部损失以适配最终 $\varepsilon$，再选（461.4）的有限衰减阶数，短段、对角尾及（461.8）共同给出（461.1）。最后使用 G3 既有的 $d_R\gg_{\epsilon_3}L^{-\epsilon_3}$，在 $L\le U^{1/2-\kappa}$ 的固定裕度内分配内部小幂，使扰动严格小于最小对角的一半，即得（461.2）。证毕。

**推论 461.2（原始短核心包的较大标记投影）。** 沿用定理 461.1、原 F4 包 $b_{j;c,a,\vartheta}$、G8–G11 的同一原算子与 [primitive-mean v2，Corollary 5、§§7–8](https://rstation.ai/api/v1/papers/riemann_hypothesis_10/versions/2/download) 的解析输入。固定

$$
\frac13<\ell<\frac12,\qquad
0<\nu<1-\frac32\ell,\qquad
L=U^\ell,\qquad \alpha=1-\frac32\ell-\nu>0.
\tag{461.9}
$$

令 $P_L=VG^{-1}V^*$ 为同一个实际投影，$W_{U,X,L}$ 是原 adjoint 的完整 primitive residue 矩阵。对全部 $1\ll X\le U^\alpha$，有

$$
\|A_{U,X}^*P_LA_{U,X}
 -W_{U,X,L}G^{-1}W_{U,X,L}^*\|
\ll U^{1-\nu/2+\varepsilon}\mathcal N^2.
\tag{461.10}
$$

共同包络 $\mathcal N\ge1$ 一次包含原 profiles、固定有限 ray、实际 Mellin/Sobolev 及解析输入费用，不按核心或标记重选。它包含（461.4）为当前 $\kappa,\varepsilon$ 所需有限阶行权 seminorms 及 $C_\Omega^{-1}$；不据此扩张原有增长高度范围。具体地，若 $C_A,C_E,C_G,C_{G^{-1}}$ 分别为 G8、G9、（461.2）两项剥去所示小幂后的常数，取 $\mathcal N^2\ge C_A+C_E+C_{G^{-1}}(2\sqrt{C_AC_GC_E}+C_E)$；这些乘积也在同一包络内。原 F4 的正权 $w_{c,a,\vartheta}=q_c^{1/2+\eta}\tau(\operatorname{rad}c)$ 与完整实际系数均保留。仅对满足 $K_c=K/q_c\le U^\alpha$ 的实际包求和，得到

$$
\begin{aligned}
&\sum_{K_c\le U^\alpha}w_{c,a,\vartheta}
 \left|Q_{P_L}(b_{j;c,a,\vartheta})
       -Q_{\rho,L}(b_{j;c,a,\vartheta})\right|\\
&\hspace{15mm}\ll(UK)^\varepsilon\mathcal N^2
  UK\,U^{-\nu/2}\mathcal P^2.
\end{aligned}
\tag{461.11}
$$

和式包含原 $a\mid\operatorname{rad}c$ 与全部有限 $\vartheta$。在 $U\asymp K$、$\mathcal N^2\mathcal P^2$ 有界或至多 polylog 增长及 $0<\varepsilon<\nu/4$ 下，（461.11）除以 $K^2$ 为 $O(K^{2\varepsilon-\nu/2}\mathcal N^2\mathcal P^2)=o(1)$。其中 $L>U^{1/3}$ 的整个标记范围由（461.2）提供。本结论只估计这些短包中的投影与 residue 二次型之差；它没有分别给出 residue 二次型、长包或完整正交补的上界，也没有推出 signed Robin restoration。

证明。取固定 $\kappa<1/2-\ell$，应用（461.2）于原实际全部标记 Gram。Corollary 5 对所有 good $R$、$U,X\ge1$ 一致成立，不带 $L\le U^{1/3}$ 的前提。其误差列在同一标记集上给出

$$
\|E\|_{\rm HS}^2\ll(UXL)^\varepsilon\mathcal N^2XL^{3/2}
\ll U^{1-\nu+\varepsilon}\mathcal N^2.
\tag{461.12}
$$

因为 $\alpha<1/2$，原 G8 直接给出 $\|A_{U,X}\|^2\ll U^{1+\varepsilon}\mathcal N^2$。G10 的有限矩阵比较保留实际 $T=A^*V=W+E$、全部交叉标记及同一个 $G^{-1}$；其两项分别为 $U^{1-\nu/2+\varepsilon}\mathcal N^2$ 和 $U^{1-\nu+\varepsilon}\mathcal N^2$，给出（461.10）。

对每个原包乘 $\|b_{j;c,a,\vartheta}\|_2^2$。原零掩码 $(x,c)=1$ 与全部相位仍在这个实际向量中。复用 G11 的已付系数质量

$$
\sum_{c,a,\vartheta}w_{c,a,\vartheta}
 \|b_{j;c,a,\vartheta}\|_2^2
\ll K^{1+\varepsilon}\mathcal P^2.
$$

只在此正和内限制到短包，得到（461.11）。原 F4 的 $\eta$ 及全部内部除数损失依同一最终 $\varepsilon$ 分配，共同累计高度没有重新分配。证毕。

## 追加锚（本行以下为增补区）

## 462. 原卷积的大重复部分与完整交叉项

**定理 462.1（保留原列相位的完整尾部）。** 沿用（458.1）的原卷积 $b$、同一个行算子 $A$、good sixth-power-free 物理行及其固定有限 ray 表示。令

$$
\mathfrak x(h)=\prod_{v_{\mathfrak p}(h)=1}\mathfrak p,
\qquad
\mathfrak c(h)=\prod_{v_{\mathfrak p}(h)\ge2}
 \mathfrak p^{v_{\mathfrak p}(h)},
\qquad h=\mathfrak c(h)\mathfrak x(h).
$$

两因子互素，$\mathfrak c(h)$ 为 powerful 理想。对 $1\le X\le K$，在取行范数之前限制原列向量：

$$
b_{\le X}(h)=b(h)\mathbf1_{q_{\mathfrak x(h)}\le X}.
\tag{462.1}
$$

假设 de Faveri [Theorem 1.1](https://arxiv.org/abs/2610.04045v1) 的解析输入成立，沿用其到原有限物理表示的既有修正。令 $\mathcal P_b\ge1$ 控制原卷积及所需 profile 导数的除数型系数包络，$\mathcal P_A\ge1$ 控制加权筛的范数成本，$\mathcal P_F\ge1$ 控制固定有限修正及本条所需分离费用。一次取组合包络 $\mathcal P\ge\mathcal P_b\mathcal P_A\mathcal P_F$，不以三个成本的最大值代替乘积。则

$$
\|A b_{\le X}\|_2^2
\ll_\varepsilon (UK)^\varepsilon\mathcal P^2
 \Psi_6(U,K)\sqrt{KX}.
\tag{462.2}
$$

这里 $\Psi_6$ 为（458.1）的同一个四项筛界。负 orientation 整体共轭，原零值保持。$\mathcal P$ 不按重复部分或行重新选择；不扩张原有高度合同。本条是 `repo-derived` 的原系数消费，直接复用原稿 `prop:sextic-row-count` 证明中的 powerful 理想计数、原列的除数界及既有有限字符修正，不将这些结果另立为新定理。

**证明。** 按唯一分解 $h=a r^6$ 分组，其中 $a$ 为 sixth-power-free 理想，且不要求 $(a,r)=1$。固定 $r$ 后，提取 $a$ 在 $r$ 的素支撑上的完整部分：

$$
e=\prod_{\mathfrak p\mid r}\mathfrak p^{v_{\mathfrak p}(a)},
\quad e\mid\operatorname{rad}(r)^5,
\quad a=e c_0x,\quad(c_0x,r)=1.
\tag{462.3}
$$

其中 $c_0$ 为 powerful，$x$ 为平方自由且 $(c_0,x)=1$。由于 $r$ 的每个素因子在 $h$ 中的重数至少为六，恰有 $x=\mathfrak x(h)$；即使某素因子在 $a$ 中的重数为一，也不能把它从 $e$ 移入 $x$。这保留了全部 sixth-power 重合情况。

记 $Y\asymp K/q_r^6$ 为原 annulus 对 $q_a$ 的上界尺度。直接复用原稿的 $O(V^{1/2})$ powerful 理想计数及固定域理想计数，固定 $r$ 并按全部允许的 $e$ 求和，有

$$
\begin{aligned}
\#\{a\ {\rm sixth\ power\ free}:q_a\ll Y,\ q_{\mathfrak x(ar^6)}\le X\}
&\ll \sum_{e\mid\operatorname{rad}(r)^5}
 \sum_{q_x\le X}\left(\frac{Y}{q_eq_x}\right)^{1/2}\\
&\ll_\delta q_r^\delta\sqrt{YX}.
\end{aligned}
\tag{462.4}
$$

内和只含 $Y/(q_eq_x)\gg1$ 的非空范围；扩大为所示正和不会缩小上界。除数界支付 $e$ 的选择，部分求和给出 $\sum_{q_x\le X}q_x^{-1/2}\ll\sqrt X$。不在有符号和里移除互素条件。

原 $b(h)$ 及本条使用的每个有限阶 profile 导数均为 $\mathcal P_b K^\delta$ 的除数型上界，故固定 $r$ 的真实列向量满足

$$
\sum_{a\ {\rm sixth\ power\ free}}|b_{\le X}(ar^6)|^2
\ll_\delta \mathcal P_b^2 K^{2\delta}
 q_r^{-3+\delta}\sqrt{KX}.
\tag{462.5}
$$

原符号的精确零延拓给出

$$
\chi_{ar^6}^{\rm raw}(z)
=\chi_a^{\rm raw}(z)\mathbf1_{(r,z)=1}.
\tag{462.6}
$$

固定 $r$ 后先保留这个行限制；只在正行范数中扩大行集。既有固定有限 Kummer/ray 修正使 Theorem 1.1 可以用于同一个列向量，其实际列长为 $O(K/q_r^6)$。当该长度为有界 subunit 时作固定 annular 扩大。筛界的四项单调，因此由 $\Psi_6(U,K)$ 统一控制。Minkowski 在原行 Hilbert 空间中求和，得到

$$
\|A b_{\le X}\|_2
\ll (UK)^{\delta'}\mathcal P\,
 \Psi_6(U,K)^{1/2}(KX)^{1/4}
 \sum_r q_r^{-3/2+\delta/2}.
\tag{462.7}
$$

最后的理想级数在足够小 $\delta>0$ 下收敛。按最终 $\varepsilon$ 分配所有内部损失，并在有限物理表示之间使用原合同的有限范数不等式，得（462.2）。每次筛调用的系数均与行无关；原有 smooth/Sobolev 恢复仅在同一有限阶费用可支付的范围使用。证毕。

**定理 462.2（实际完整能量与补空间的剩余来源）。** 再采用定理 459.1 的全部解析输入、平衡长度 $U\asymp K$、$D=N=\sqrt K$ 及其同一固定或 polylog profile/height 合同。取

$$
b_{\rm tail}=b_{\le\sqrt K},\qquad
b_{\rm rem}=b-b_{\rm tail},\qquad
\zeta=\frac{5\sqrt6-12}{12}>0.
\tag{462.8}
$$

一次选择 $\mathcal H\ge\max\{\mathcal C,\mathcal P,1\}$，其中 $\mathcal C$ 为（459.1）的完整原卷积成本。对同一个行空间中的任意正交投影 $\Pi$，一致有

$$
\begin{aligned}
\|A b_{\rm tail}\|_2^2
 &\ll_\varepsilon\mathcal H^2 K^{23/12+\varepsilon},\\
\left|\|\Pi Ab\|_2^2
       -\|\Pi A b_{\rm rem}\|_2^2\right|
 &\ll_\varepsilon\mathcal H^2 K^{2-\zeta+\varepsilon}.
\end{aligned}
\tag{462.9}
$$

这同时适用于 $\Pi=I$、任意实际 $P$ 及 $I-P$。当 $\mathcal H=K^{o(1)}$ 时，完整原能量或同一补空间的 $o(K^2)$ 目标，分别等价于同一个 $b_{\rm rem}$ 的目标。余向量的每列满足 $q_{\mathfrak x(h)}>\sqrt K$，从而 $q_{\mathfrak c(h)}\ll\sqrt K$；在充分大 $K$ 时，原 annular 支撑使全部平方自由列仍保留。

**证明。** 在平衡点 $\Psi_6(U,K)\ll K^{7/6}$。将 $X=\sqrt K$ 代入（462.2），得第一式。记 $v=\Pi Ab$、$t=\Pi A b_{\rm tail}$，直接复用 Hilbert 范数恒等式及 Cauchy：

$$
\bigl|\|v\|^2-\|v-t\|^2\bigr|
\le2\|v\|\,\|t\|+\|t\|^2.
\tag{462.10}
$$

定理 459.1 仅用于完整原 $b$，不将其因子估计套在已失去卷积分解的 $b_{\rm rem}$ 上。由投影收缩性和（459.3），$\|v\|^2\le Q(b)\ll\mathcal C^2K^{\kappa_{\rm joint}+\varepsilon}$。因此完整交叉项的幂次为

$$
\frac12\left(\kappa_{\rm joint}+\frac{23}{12}\right)
=3-\frac{5\sqrt6}{12}=2-\zeta.
\tag{462.11}
$$

尾部平方项的幂次更小，故得第二式及所述等价。证毕。

（462.9）控制的是 F4 之前、保持全部原列相位的真实尾部及其与余向量的交叉项。它不提供 F4 中逐核心加权正和的同样节省，也不改变（461.11）各项的含义。$b_{\rm rem}$ 的完整估计、其他原长度和高度以及 signed Robin restoration 仍未支付；它不是完整 Robin 不等式或 RH 的证明。

## 追加锚（本行以下为增补区）

## 463. 三重以上重复部分与剩余原列

原列的乘法分解与 Minkowski 方法已有文献先例：[Blomer–Goldmakher–Louvel, *L-functions with n-th order twists*, §5, Corollary 1.6 的证明，（5.3）—（5.5）](https://arxiv.org/pdf/1112.1650v1)对原内变量使用 squarefree／squarefull 分解。本节复用这种范数方法与既有六次幂自由筛，保留完整三满部分截断和全部六次幂碰撞，再消费到原向量的完整交叉项；不将通常的满数计数或这些筛与范数方法认作本项目发明。

**定理 463.1（大三满部分的原列能量）。** 沿用定理 462.1 的原卷积、行算子、解析输入、固定有限表示及组合成本 $\mathcal P$。定义

$$
\mathfrak c_3(h)=\prod_{v_{\mathfrak p}(h)\ge3}
 \mathfrak p^{v_{\mathfrak p}(h)},\qquad
b_{3,\ge Y}(h)=b(h)\mathbf1_{q_{\mathfrak c_3(h)}\ge Y},
\qquad 1\le Y\le K.
\tag{463.1}
$$

$\mathfrak c_3(h)$ 收集原重数至少为三的完整素因子幂，允许重数四、五及更高的部分；它是三满理想，不限于整立方。则

$$
\|Ab_{3,\ge Y}\|_2^2
\ll_\varepsilon (UK)^\varepsilon\mathcal P^2
 \Psi_6(U,K)K Y^{-2/3}.
\tag{463.2}
$$

同一上界允许再乘一个与行无关、绝对值至多为一的列乘子。所有原字符零值及相位保持，组合成本仍按定理 462.1 的乘积合同承担。

**证明。** 直接复用既有六次幂移除 $h=ar^6$，其中 $a$ 为 sixth-power-free，允许 $a,r$ 相交。固定 $r$，仍提取

$$
e=\prod_{\mathfrak p\mid r}\mathfrak p^{v_{\mathfrak p}(a)},
\quad e\mid\operatorname{rad}(r)^5,
\quad a=ea_0,\quad(a_0,r)=1.
\tag{463.3}
$$

这时有精确恒等式

$$
\mathfrak c_3(ar^6)=r^6e\,\mathfrak c_3(a_0).
\tag{463.4}
$$

特别地，$e$ 在 $a$ 中重数一、二的素因子，在 $h$ 中也已属于三满部分。

所需计数只用通常的正 Euler 乘积与 Rankin 界。对 $0<\eta<1/6$，三满理想的级数

$$
\sum_{c\ {\rm three\ full}}q_c^{-1/3-\eta}
=\prod_{\mathfrak p\notin S}
 \left(1+\frac{q_{\mathfrak p}^{-1-3\eta}}
 {1-q_{\mathfrak p}^{-1/3-\eta}}\right)<\infty
\tag{463.5}
$$

绝对收敛。将 $a_0$ 分成其三满部分 $c$ 与剩余部分，只在正计数中扩大剩余理想及互素条件，得到对 $M,Z>0$ 的统一界

$$
\#\{a_0:q_{a_0}\le M,\ q_{\mathfrak c_3(a_0)}\ge Z\}
\ll_\eta M Z^{-2/3+\eta}.
\tag{463.6}
$$

这里 $Z<1$ 时同样成立：在 $q_c\ge Z$ 上使用
$q_c^{-1}\le Z^{-2/3+\eta}q_c^{-1/3-\eta}$，再复用固定域理想计数。空的短范围保留为零。

固定 $r,e$ 后，原 annulus 给出 $M\ll K/(q_r^6q_e)$，（463.4）给出 $Z=Y/(q_r^6q_e)$。故固定 $r$ 的实际列支撑数至多为

$$
\begin{aligned}
&\sum_{e\mid\operatorname{rad}(r)^5}
 \frac{K}{q_r^6q_e}
 \left(\frac{Y}{q_r^6q_e}\right)^{-2/3+\eta}\\
&\qquad\ll_{\eta,\delta}
 K Y^{-2/3+\eta}q_r^{-2-6\eta+\delta}.
\end{aligned}
\tag{463.7}
$$

最后一步用除数界处理全部 $e$，不遗漏 $a,r$ 的相交素因子。原卷积及所需有限阶 profile 导数的除数型包络于是给出

$$
\sum_a|b_{3,\ge Y}(ar^6)|^2
\ll_{\eta,\delta,\delta'}
 \mathcal P_b^2K^{1+2\delta'}
 Y^{-2/3+\eta}q_r^{-2-6\eta+\delta}.
\tag{463.8}
$$

保留（462.6）的精确行零值，固定 $r$ 后应用同一个六次幂自由筛，再在原行 Hilbert 空间使用 Minkowski。其求和因子为

$$
\sum_r q_r^{-1-3\eta+\delta/2}<\infty
\qquad(0<\delta<6\eta).
\tag{463.9}
$$

因此不需要把六次幂碰撞当作互不相干的列。先相对于最终 $\varepsilon$ 选择 $\eta,\delta'$ 及筛损失，再取 $0<\delta<6\eta$；由 $Y\le K$ 吸收 $Y^\eta$，得（463.2）。额外的有界列乘子不增加支撑计数或系数包络；同一证明适用。负 orientation、有限物理表示及 smooth/Sobolev 恢复沿用定理 462.1 的同一费用和累计高度合同。证毕。

**定理 463.2（合并尾部及完整交叉项）。** 再采用定理 459.1 的全部输入及定理 462.2 的平衡、固定或 polylog 成本合同。定义

$$
\begin{aligned}
b_{\rm tail}^{+}(h)
 &=b(h)\mathbf1_{\{q_{\mathfrak x(h)}\le\sqrt K\}
                 \,\cup\,\{q_{\mathfrak c_3(h)}\ge K^{1/3}\}},\\
b_{\rm rem}^{+}&=b-b_{\rm tail}^{+},\qquad
\zeta_3=\frac{30\sqrt6-73}{72}>0.
\end{aligned}
\tag{463.10}
$$

一次选择 $\mathcal H$ 同时控制原完整卷积及两条尾部估计的组合成本。对同一行空间中的任意正交投影 $\Pi$，有

$$
\begin{aligned}
\|Ab_{\rm tail}^{+}\|_2^2
 &\ll_\varepsilon\mathcal H^2K^{35/18+\varepsilon},\\
\left|\|\Pi Ab\|_2^2
       -\|\Pi Ab_{\rm rem}^{+}\|_2^2\right|
 &\ll_\varepsilon\mathcal H^2K^{2-\zeta_3+\varepsilon}.
\end{aligned}
\tag{463.11}
$$

**证明。** 平衡点的 $\Psi_6(U,K)\ll K^{7/6}$ 与 $Y=K^{1/3}$ 给出
$7/6+1-2/9=35/18$。将合并尾部写成（462.8）的旧尾部，加上
$b_{3,\ge K^{1/3}}\mathbf1_{q_{\mathfrak x(h)}>\sqrt K}$；两项在列支撑上不重叠。在行空间中使用三角不等式及两条实际尾部界，得第一式。这里没有从两个范数上界相减推断子向量的范数。

对第二式复用（462.10）。定理 459.1 只用于完整原 $b$，不用于已加列截断的余向量。交叉项幂次为

$$
\frac12\left(\frac{49-10\sqrt6}{12}+\frac{35}{18}\right)
=\frac{217-30\sqrt6}{72}=2-\zeta_3.
\tag{463.12}
$$

它大于尾部平方项的幂次，且 $30\sqrt6>73$。投影收缩性使估计对全部上述 $\Pi$ 一致。证毕。

当 $\mathcal H=K^{o(1)}$ 时，（463.11）把完整能量及同一投影、补空间的 $O_\varepsilon(K^{2+\varepsilon})$ 目标转移到同一个 $b_{\rm rem}^{+}$；更强的 $o(K^2)$ 目标也同样转移。新余向量的每个非零列同时满足

$$
q_{\mathfrak x(h)}>\sqrt K,\qquad
q_{\mathfrak c_3(h)}<K^{1/3}.
\tag{463.13}
$$

这是对 F4 之前真实原列及其完整干涉的附加源限制；三满部分较大的列不必满足旧的一重部分小截断。所有充分大规模的平方自由列仍保留。这里复用六次幂自由筛、通常的满数计数与 Hilbert 范数估计，所得为 `repo-derived` 的原系数应用，不声明新筛或文献优先权。完整余向量、F4 加权正和、其他原长度及高度、原固定指数的 signed Robin restoration 仍未支付；本条不证明 Robin 不等式或 RH。

## 追加锚（本行以下为增补区）

## 464. 短逆因子的平方自由投影与原长包预算

**定理 464.1（原 F4 长包中的三分之一次幂扇区）。** 在下列所引解析输入下，沿用 [F1–F4](../../../Library/Analytic/faveri2026fixedorder.md#a-weighted-powerful-part-majorant-for-all-original-columns) 的同一原系数、非负行权、good 非单位 sixth-power-free 物理行、固定有限 ray 数据及零延拓。令 $U\ge2$、$K=DN$、$a\mid\operatorname{rad}c$、$b=c/a$，并保留原有约定

$$
D_a=D/q_a,\qquad N_b=N/q_b,\qquad X=K_c=D_aN_b=K/q_c.
\tag{464.1}
$$

长度属于原输入允许的固定幂范围，包含其中更短的非空 annuli。Profiles 与 norm-twist 高度固定，或满足下述共同费用为次幂的 polylog 合同；不扩张原 growing-height allowance。把有限 Fourier 重构、原行分区、所需有限 profile 导数以及原 Möbius/plain 成本的乘积纳入一次共同包络 $\mathcal C\ge1$。此包络不按 $c,a$、投影展开的除子或物理行重选。对每个固定 $C_0>0$，当

$$
D_a\le C_0 U^{1/3}
\tag{464.2}
$$

时，原 F4 包的完整正能量满足

$$
\widetilde T^{\rm sf}_{j;c,a,\kappa}
\ll_{\varepsilon,C_0}\mathcal C^2(UK)^\varepsilon UX.
\tag{464.3}
$$

这里既不删除 $\mathbf1_{x\ {\rm sf}}$，也不删除 $(x,c)=1$；结论估计的是同一系数包的完整行范数，不是单个 pure-power 对偶项。对每个最终 $\varepsilon>0$，先按 F4 选择 $s=1/2+\eta$，再分配全部内部损失，得到原正 majorant 中的实际子和

$$
\begin{aligned}
M_{\le1/3}
&=Z_s|\mathcal T|\sum_{c\ {\rm powerful}}q_c^s\tau(\operatorname{rad}c)
\sum_{\substack{a\mid\operatorname{rad}c\\D_a\le C_0U^{1/3}}}
\sum_{\kappa\in\mathcal T}\widetilde T^{\rm sf}_{j;c,a,\kappa}\\
&\ll_{\varepsilon,C_0}\mathcal C^2(UK)^\varepsilon UK.
\end{aligned}
\tag{464.4}
$$

这是一项 `repo-derived` 的原系数联合应用。解析供应为原稿 [pinned source](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex) 的 `lem:logarithmic-control`、`lem:deleted-euler-factors`、无槽 `lem:plain`、`lem:buffered-bins` 至 `prop:detector-witness` 及实际行计数证明；逆矩、plain 四矩与计数优化亦见 [Xu–Sang v2，Lemma 6.1、Theorem 2.2、Proposition 6.3](https://arxiv.org/html/2610.17675v2)。平方自由 Möbius 展开、Euler 卷积、Minkowski 和 F4 临界 powerful-core 求和仅作为既有工具使用，不单列为新增结果。DDDS 的 C1 是另一 Gauss Dirichlet-series 恒等式，不作为这里的 plain moment 供应。

证明。先在一个原有限 Fourier 分量上记 $\psi_z(h)=\xi(h)\chi_h(z)$，包括其全部固定零值。定义未作平方自由投影的原乘积

$$
B(D_0,N_0;z)=\sum_{dn}\mu(d)V(q_d/D_0)W(q_n/N_0)\psi_z(dn).
\tag{464.5}
$$

第一步是在原逐行逆界和共同分箱计数中使用任意固定地板 $a_\eta=1/2+\eta$，其中 $\eta>0$ 随最终误差预先固定。此步骤复用定理 459.1 的证明，并在本条实际包中消费其短长度范围。原缓冲分箱只要求最大零点实部属于一个固定有界区间且随高度非减。原有限移线与删除因子控制在 $\Re s>1/2+\eta$ 仍适用，记 $M(D_0;z)=\sum_d\mu(d)V(q_d/D_0)\psi_z(d)$，给出归一化逆因子

$$
|D_0^{-1/2}M(D_0;z)|^2
\ll U^{\epsilon_1}C_M^2D_0^{\delta+16e}+O(U^{-10}),
\qquad \delta=2a-1.
\tag{464.6}
$$

非地板分箱的计数仍由原检测证明给出：先固定见证 dyadic 长度 $r,m$ 及 presentation，再计数，然后对它们求和。地板变化所需的唯一长度修正是
$2\delta(m-1/2)_+\ll\epsilon_0$；因 $\delta\ge2\eta$，先固定 $\eta$ 再令初步损失足够小，保留 $m\le1/2+O_\eta(\epsilon_0)$ 和 $r\ge t-1/2-O_\eta(\epsilon_0)$。原 Gamma 移线的余项至多为
$U^{-3+t(5/4-\Re\rho)+o(1)}H_1^2\le U^{-15/8+o(1)}H_1^2=o(1)$，仍取 $1\le t\le3/2$、$H_1\le U^{1/100}$。因此原优化不变，计数指数为

$$
R(\delta)=
\begin{cases}
(15-16\delta)/(15-6\delta),&2\eta<\delta\le5/6,\\
1-\delta,&5/6\le\delta\le1.
\end{cases}
\tag{464.7}
$$

没有断言计数所返回的检测见证本身满足短逆长度；本条需要短的是规定目标 (464.5) 中的 $D_0$。共同分箱控制同一有限字符族中的每一个目标分量，不将辅助见证替换成目标卷积。

复用无槽 plain 四矩及定理 459.1 的同一行 Cauchy，非地板包的 (464.5) 能量至多为
$\mathcal C^2(UK)^\epsilon D_0N_0D_0^\delta U^{(1+R(\delta))/2}$。
若 $D_0\le C_0U^{1/3}$，第一段的余幂为
$\delta\{1/3-5/(15-6\delta)\}\le0$，第二段为 $-\delta/6\le0$。地板仅多出 $D_0^{2\eta}\ll U^{2\eta/3}$，先选 $\eta$ 再分配误差便可吸收。高度顺序仍是先固定内部 moment、分箱和有限 Sobolev 阶，再选足够小的缓冲高度指数，最后选外部 Mellin-tail 阶；未增加任何新的高度预算。于是对原允许范围内的全部更短非空长度，统一有

$$
\|\sqrt\Omega B(D_0,N_0)\|_2
\ll_{\epsilon,C_0}\mathcal C(UK)^\epsilon\sqrt{UD_0N_0},
\qquad D_0\le C_0U^{1/3}.
\tag{464.8}
$$

第二步把实际包精确接回这些未投影乘积，不假设对列投影后的向量仍有 (464.8)。记

$$
B_{A,B}(D_0,N_0;z)=\sum_{dn}\mu(d)\mathbf1_{(d,A)=1}\mathbf1_{(n,B)=1}
 V(q_d/D_0)W(q_n/N_0)\psi_z(dn),
\tag{464.9}
$$

其中 $A,B$ 只用于零掩码。若 $\mathcal P(A)$ 表示素因子均在 $A$ 中的所有理想，则逐素因子的既有 Euler 卷积恒等式给出

$$
\mu(\cdot)\mathbf1_{(\cdot,A)=1}
=\mu*\mathbf1_{\mathcal P(A)},\qquad
\mathbf1_{(\cdot,B)=1}=\mathbf1*\bigl(\mu\mathbf1_{\cdot\mid\operatorname{rad}B}\bigr).
$$

因此精确地有

$$
B_{A,B}(D_0,N_0;z)=
\sum_{m\in\mathcal P(A)}\sum_{e\mid\operatorname{rad}B}
\mu(e)\psi_z(me)\,
 B(D_0/q_m,N_0/q_e;z).
\tag{464.10}
$$

由 profiles 的紧支撑，实际非空项有限。只在正行范数中使用 $|\psi_z(me)|\le1$，再用 (464.8) 及 Minkowski，得到

$$
\begin{aligned}
\|\sqrt\Omega B_{A,B}(D_0,N_0)\|_2
&\ll\mathcal C(UK)^\epsilon\sqrt{UD_0N_0}\,
\prod_{p\mid A}(1-q_p^{-1/2})^{-1}
\prod_{p\mid B}(1+q_p^{-1/2})\\
&\ll_{\theta}\mathcal C(UK)^\epsilon(q_Aq_B)^\theta\sqrt{UD_0N_0}
\end{aligned}
\tag{464.11}
$$

对每个固定 $\theta>0$ 均成立。最后一步是有限素因子乘积的通常次幂界；它不把移动模数常数当作固定常数。若某个缩短长度低于一，非空性仍把它从下方限制在原固定 annular 常数；按固定 annular enlargement 归入长度一并运输 profile，所需有限 seminorms 一致有界。更短空项为零。没有更换字符族或增加真正 conductor。

第三步保留实际 squarefree 投影。令 $P_c(z)$ 是固定 Fourier 分量的原 F3 包响应。使用
$\mathbf1_{dn\ {\rm sf}}=\sum_{r^2\mid dn}\mu(r)$。
每个非零 $\mu(r)$ 的 $r$ 平方自由；因 $d$ 也平方自由，令 $g=(d,r)$，则唯一地写成

$$
g\mid r,\qquad d=gd',\qquad n=(r^2/g)n',\qquad(d',r)=1.
$$

原 $(dn,c)=1$ 强迫 $(r,c)=1$、$(d'n',c)=1$，而 $\mu(d)=\mu(g)\mu(d')$。所以包含所有 collision zeros 的逐行恒等式是

$$
P_c(z)=
\sum_{\substack{r\ {\rm sf}\\(r,c)=1}}
\mu(r)\psi_z(r^2)
\sum_{g\mid r}\mu(g)
B_{cr,c}\left(D_a/q_g,\ N_bq_g/q_r^2;z\right).
\tag{464.12}
$$

每个乘积的总长度为 $X/q_r^2$，逆长度至多 $D_a$，并且非空性给出 $q_r\ll\sqrt X$。这保持原相同物理行和字符；$\psi_z(r^2)$ 仍仅在正行范数中由模长一上界放大。原有限类条件在 $h=r^2d'n'$ 下由同一有限 Fourier 分量精确运输，不加入新的 ray 群。

将 (464.11) 用于 $A=cr,B=c$，再在 (464.12) 的同一行空间使用 Minkowski，得到

$$
\begin{aligned}
\|\sqrt\Omega P_c\|_2
&\ll\mathcal C(UK)^\epsilon\sqrt{UX}\,
q_c^{2\theta}\sum_{q_r\ll\sqrt X}\frac{\tau(r)q_r^\theta}{q_r}\\
&\ll_{\theta}\mathcal C(UK)^\epsilon
q_c^{2\theta}X^\theta\sqrt{UX}.
\end{aligned}
\tag{464.13}
$$

这里直接以 Rankin 正上界
$\sum_{q_r\le C\sqrt X}\tau(r)q_r^{-1+\theta}
\le(C\sqrt X)^{2\theta}\zeta_F(1+\theta)^2$
支付全部 $r,g$，不假设投影正性或不同项正交。因 $q_c\le CK$、$X\ll K$，先分配 $\epsilon,\theta$ 再平方，恢复有限分量和同一 smooth 参数，便得 (464.3)。对原参数所需的有限次导数，乘法相位的运输至多再给出固定阶 $\log(2K)$ 因子，纳入同一最终小幂，不重新支付高度。此界包含包内全部交叉项。

最后按 F4 的同一正权求和。其数值部分由已拥有的临界 powerful-core 估计支付：

$$
K\sum_{\substack{c\ {\rm powerful}\\q_c\le CK}}
\tau(c)^2q_c^{-1/2+\eta}
\ll_{\eta,\delta}K^{1+\eta+\delta}.
\tag{464.14}
$$

选择 $\eta,\delta$ 以及前述全部内部损失适配一个最终 $\varepsilon$，得到 (464.4)。$Z_s$ 可依赖最终 $\varepsilon$，但不依赖 $U,K$。未删除一个独立固定的正 $\eta$，也没有更新 profiles 的共同成本。证毕。

**命题 464.2（与原未付长包的交集）。** 在 $U=K$、$D=N=\sqrt K$ 时，(464.2) 选择的是实际 $a$-分量 $q_a\ge C_0^{-1}K^{1/6}$，而非自由缩短原见证。因 $a^2\mid c$，这使 $X=K/q_c\le C_0^2K^{2/3}$。固定 $C_0=1$ 时，其中存在满足 $X>\sqrt U$ 的合法非零 F3 包；但此条件不覆盖该长度带内的所有包。

证明。此例固定 $C_0=1$。取足够大的 good 素理想 $p$，令 $P=q_p$，并取 $U=K=P^6$、$D=N=P^3$、$c=p^2$、$a=b=p$。则原分解给出的恰是

$$
D_a=N_b=P^2=U^{1/3},\qquad
X=P^4=U^{2/3}>\sqrt U.
\tag{464.15}
$$

先选原物理过滤后仍允许且权重非零的有限列类 $\kappa$。把 $c=p^2$ 的类运输到 $x$ 后，选择两个固定 ray 类，使它们的乘积是该允许的 $x$-类；由固定 ray 类中的素理想定理，可取避开 $pS$ 的不同素理想 $d',n'$，范数均处于 $P^2$ 的固定小相对区间。取原允许的非负 annular profiles 在两处为正。对 $x=d'n'$，只有两个单素因子 $d'$、$n'$ 落在这份逆 annulus；它们的 Möbius 值均为 $-1$。物理类过滤在 $x$ 处保留这项，乘法相位非零，故实际 F3 包的系数不为零；这一判断不只针对一个 Fourier 分量。这仅说明原允许系数族存在这样的非零包，不断言实际零点检测必定返回这份见证或这些 profiles。原列 $h=p^2d'n'$ 的一重部分为 $x$，满足 $q_x\asymp P^4$，因而对充分大 $P$ 有 $q_x>\sqrt K$；三满部分为一，故也不被定理 462–463 的旧尾部条件排除。证毕。

在该平衡点，使用相同投影展开但只消费已有 $D_a\le U^{1/4}$ 估计时，必有 $q_c\ge q_a^2\ge K^{1/2}$，因而只落在已经由 G8 与完整系数质量界支付的 $X\le\sqrt U$ 块。三分之一次幂范围的作用是加入 (464.15) 所在的原长包分量。它不保证检测实际选中这块，也不推断其余包很小。

F4 可以按同一个 $\eta$ 把上述子和与其补集相加。结合已付的 $X\le\sqrt U$ 子和后，沿此正 majorant 路线仍需估计

$$
X>\sqrt U,\qquad D_a>C_0U^{1/3}
\tag{464.16}
$$

的实际包和。这是充分的剩余估计要求，没有从原矩反推正 majorant 的逆向界。在平衡点，对固定 $C_0$ 及充分大 $K$，$c=a=1$ 的平方自由原列仍在补集中。所有更大的原高度费用及 signed Robin restoration 仍须分别处理；本条没有给出完整原矩上界、严格幂次节省、$o(UK)$、RH 或逐整数 Robin 结论。

## 追加锚（本行以下为增补区）

## 465. 短 plain 因子的高阶矩与原 F4 联合长度扇区

**定理 465.1（保留实际包的联合长度预算）。** 沿用定理 464.1 与 [F1–F4](../../../Library/Analytic/faveri2026fixedorder.md#a-weighted-powerful-part-majorant-for-all-original-columns) 的同一物理行、原系数、有限类、非负权、零延拓与解析输入。另复用 de Faveri [Theorem 1.1](https://arxiv.org/abs/2610.04045v1) 及既有固定有限 ray-family 接口。固定整数 $k\ge3$ 和常数 $C_D,C_N>0$，令

$$
d_k=\frac23\left(1-\frac1k\right),\qquad
D_a\le C_DU^{d_k},\qquad N_b\le C_NU^{1/(2k)}.
\tag{465.1}
$$

长度仍在原允许固定幂范围及其中更短的非空 annuli。Profiles 与 norm-twist 高度固定，或符合下面共同费用为次幂的 polylog 合同；不扩张原 growing-height allowance。令 $\mathcal A$ 是既有筛界的算子范数成本，$C_{M,\xi}$ 是（464.6）的原逆因子逐行成本，$P_{k,\xi}$ 控制 plain profile 及本证明所需有限阶导数。一次选择共同乘积包络

$$
\mathcal C_k\ge
\max\left\{1,\sum_\xi|c_\xi|
 C_{M,\xi}\mathcal A^{1/k}P_{k,\xi}\right\},
\tag{465.2}
$$

并纳入原有限行分区、有限 Fourier 重构及 smooth/Sobolev 费用。它不随物理行、$c,a$ 或掩码展开项重选。则在所列解析输入下，实际完整包满足

$$
\widetilde T^{\rm sf}_{j;c,a,\kappa}
\ll_{\varepsilon,k,C_D,C_N}
\mathcal C_k^2(UK)^\varepsilon UX,
\qquad X=D_aN_b=K/q_c.
\tag{465.3}
$$

沿 F4 的同一正权、同一 $s=1/2+\eta$ 求和，限制在（465.1）的实际 $a$-分量，得到

$$
\begin{aligned}
M_k={}&Z_s|\mathcal T|
 \sum_{c\ {\rm powerful}}q_c^s\tau(\operatorname{rad}c)
 \sum_{\substack{a\mid\operatorname{rad}c\\
 D_a\le C_DU^{d_k},\ N_b\le C_NU^{1/(2k)}}}
 \sum_{\kappa\in\mathcal T}\widetilde T^{\rm sf}_{j;c,a,\kappa}\\
&\ll_{\varepsilon,k,C_D,C_N}
 \mathcal C_k^2(UK)^\varepsilon UK.
\end{aligned}
\tag{465.4}
$$

每个最终 $\varepsilon>0$ 先固定 $k,C_D,C_N$，再选择 $\eta$、零点地板及全部内部损失。证明复用短 Dirichlet 多项式取幂、除数界、六次幂提取、Hölder 与第 464 节的精确投影运输，将其用于（465.1）的实际包及同权聚合。

证明。先固定原有限 Fourier 分量，记 $\psi_z(h)=\xi(h)\chi_h(z)$，包含原固定零值。对实际 plain 因子定义

$$
S_\xi(N_0;z)=N_0^{-1/2}
 \sum_n W(q_n/N_0)\psi_z(n).
$$

将 $S_\xi(N_0;z)^k$ 展开为

$$
S_\xi(N_0;z)^k
=N_0^{-k/2}\sum_h A_{N_0,k}(h)\psi_z(h),\qquad
A_{N_0,k}(h)=\sum_{n_1\cdots n_k=h}
 \prod_{i=1}^k W(q_{n_i}/N_0).
\tag{465.5}
$$

系数的支撑为 $q_h\asymp_k N_0^k$；除数界给出
$|A_{N_0,k}(h)|\ll_{k,\epsilon}P_{k,\xi}^kq_h^\epsilon$。
唯一写 $h=\ell^6h_0$，$h_0$ sixth-power-free，允许 $\ell,h_0$ 相交。固定 $\ell$ 后，理想计数及同一除数界给出

$$
\sum_{h_0\ {\rm sixth\ power\ free}}
 \left|N_0^{-k/2}A_{N_0,k}(\ell^6h_0)\right|^2
\ll_{k,\epsilon}P_{k,\xi}^{2k}N_0^\epsilon q_\ell^{-6}.
\tag{465.6}
$$

只对实际非空项使用该式。若 $Y_\ell=N_0^k/q_\ell^6$ 为 subunit，非空性给出固定正下界，按原固定 annular enlargement 归入长度一；更短项为零。$N_0$ 本身为有界 subunit 的非空情形亦作同样处理。

当 $N_0\le C_NU^{1/(2k)}$ 时，$Y_\ell\ll_{k,C_N}\sqrt U$。既有四项筛界满足 $\Psi_6(U,Y_\ell)\ll_{k,C_N}U$。原乘法性给出精确行因子 $\psi_z(\ell^6)$；只在正行范数中使用 $|\psi_z(\ell^6)|\le1$。对各 $\ell$ 应用同一个筛及固定有限族接口，再用 Minkowski 和 $\sum_\ell q_\ell^{-3}<\infty$，得到作为本条中间步骤的短矩界

$$
\sum_z\Omega(q_z/U)|S_\xi(N_0;z)|^{2k}
\ll_{k,\epsilon,C_N}
 \mathcal A^2P_{k,\xi}^{2k}(UN_0)^\epsilon U.
\tag{465.7}
$$

这不是在 $N_0\asymp\sqrt U$ 假定任意高矩；此处的长度限制是 $N_0\ll U^{1/(2k)}$。六次幂重叠由（465.6）的质量和 Minkowski 支付，不把相同行字符的列视为正交。

令 $M_\xi(D_0;z)$ 为归一化原 Möbius 因子。直接复用（464.6）—（464.7）的同一共同缓冲分箱，选固定地板 $1/2+\eta_0$。在非地板箱上记 $\delta=2a-1$，则逐行逆界与（465.7）、带原权的 Hölder 给出

$$
\begin{aligned}
\sum_{z\in\mathcal B_{i,a}}\Omega|M_\xi S_\xi|^2
&\ll (UK)^\epsilon
 (C_{M,\xi}\mathcal A^{1/k}P_{k,\xi})^2
 D_0^{\delta+16e}
 U^{1/k+(1-1/k)R(\delta)},\\
R(\delta)&=
\begin{cases}
(15-16\delta)/(15-6\delta),&2\eta_0<\delta\le5/6,\\
1-\delta,&5/6\le\delta\le1.
\end{cases}
\end{aligned}
\tag{465.8}
$$

原 $\Omega$ 有界，箱的加权质量由同一个实际行计数控制。若 $D_0\le C_DU^{d_k}$，忽略已预留的小损失后，相对 $U$ 的余幂精确为

$$
d_k\delta+\frac1k+
 \left(1-\frac1k\right)R(\delta)-1
=\begin{cases}
-\dfrac{4(1-1/k)\delta^2}{15-6\delta},&\delta\le5/6,\\
-\dfrac13(1-1/k)\delta,&\delta\ge5/6.
\end{cases}
\tag{465.9}
$$

两段均非正。地板箱用原 $O(U)$ 行计数，额外费用仅为
$D_0^{2\eta_0}\ll U^{2d_k\eta_0}$，先随最终 $\varepsilon$ 选择固定 $\eta_0>0$ 即可吸收。再令分箱宽度 $e$ 和内部损失足够小。高度顺序完全沿用第 464 节：先固定内部 moment、有限分箱与 Sobolev 阶，再选足够小的缓冲高度指数，最后选外部 Mellin-tail 阶。$k$ 固定，不取得随尺度增长的高度或矩阶。原逆尾部与多项式大小仍由既有合同支付。乘回 $D_0N_0$ 并恢复有限分量，便得未投影乘积的完整行范数

$$
\|\sqrt\Omega B(D_0,N_0)\|_2
\ll\mathcal C_k(UK)^\epsilon\sqrt{UD_0N_0}
\tag{465.10}
$$

在（465.1）的两个相应长度条件下同时成立。

现在直接复用（464.10）与（464.12），不另证零掩码或 squarefree projector 恒等式。在后者的实际展开中

$$
D_0=D_a/q_g\le D_a,\qquad
N_0=N_bq_g/q_r^2\le N_b,\qquad g\mid r.
\tag{465.11}
$$

故两个联合长度条件同时保留；再经（464.10）的 Euler 掩码卷积除以 $q_m,q_e$，长度只会进一步缩短。逐行标量、原 collision zeros、有限类运输、同一物理行与字符族均保持第 464 节的合同。使用（465.10）替代（464.8），原（464.11）—（464.13）的 Euler 次幂界、Minkowski 及 $r$ 的 norm-harmonic 正求和原样支付全部项，得到（465.3），含实际包内完整交叉项。对有限 profile 导数的取幂展开仍具相同除数包络；固定阶对数费用纳入最终小幂，不增加算术系数类或更新高度预算。最后按同一个 F4 的 $\eta$ 消费（464.14），给出（465.4）。证毕。

**命题 465.2（确实新增的原长包）。** 以下两份实例固定 $C_D=C_N=1$。在原平衡 $U=K$、$D=N=\sqrt U$ 中，（465.1）含有不满足 $D_a\ll U^{1/3}$ 且满足 $X>\sqrt U$ 的合法非零物理 F3 包。$k=3$ 与 $k=4$ 都提供这样的包；下列实例的三满部分均为一，故其原列也未被第 462–463 节的两个尾部条件删除。

证明。先取 $k=4$。令 $p$ 为范数 $P\to\infty$ 的 good 素理想，取

$$
U=K=P^5,\quad D=N=P^{5/2},\quad
c=p^2,\quad a=1,\quad b=p^2.
$$

则

$$
D_a=P^{5/2}=U^{1/2},\qquad
N_b=P^{1/2}=U^{1/10}\le U^{1/8},\qquad
X=P^3=U^{3/5}>\sqrt U.
\tag{465.12}
$$

因此它属于 $k=4$ 的新矩形，且对每个固定 $C_0$，充分大 $P$ 时不属于（464.2）。

再取 $k=3$。仍取 $q_p=P\to\infty$，并在一个固定 ray 类中选择不同 good 素理想 $v$，使 $Q=q_v\in[P^{5/2},(1+\vartheta)P^{5/2}]$，其中 $\vartheta>0$ 固定且小。取

$$
U=K=P^{18},\quad D=N=P^9,\quad
c=p^2v^2,\quad a=p,\quad b=pv^2.
$$

于是

$$
D_a=P^8=U^{4/9},\qquad
N_b=P^8/Q^2\asymp P^3\le U^{1/6},\qquad
X=P^{16}/Q^2\asymp P^{11}>\sqrt U.
\tag{465.13}
$$

这里同样越出（464.2），并且 $N_b/U^{1/8}\to\infty$，所以它还不在固定常数的 $k=4$ 矩形内。

两例的实际系数非零性按同一物理过滤检验。先取允许且原乘法权非零的有限列类，运输 $c$ 后，把所得 $x$-类分成两个固定 ray 素类。固定 ray 类中的素理想定理给出避开 $cS$ 的不同素理想 $d',n'$，范数分别位于 $D_a,N_b$ 的固定小相对区间。取原允许的非负 profiles 在两处为正。由于两例均有 $D_a/N_b\to\infty$，$x=d'n'$ 的约数中只有 $d'$ 落入逆 annulus，故内层 Möbius 卷积为负，乘以非零原权后完整 F3 系数非零；实际有限过滤保留 $x$，并非只在一个 Fourier summand 上非零。原列 $h=cx$ 的一重部分为 $x$，其范数分别为 $\asymp P^3$、$\asymp P^{11}$，对充分大 $P$ 都大于 $\sqrt K$；$c$ 只含平方且 $(x,c)=1$，故三满部分为一。这个存在性结论只使用原允许系数族，不给出包能量的正下界，也不断言原零点检测实际返回这些 profiles 或包。证毕。

因此，在同一个 F4 正 majorant 中，可以把第 464 节及已付 $X\le\sqrt U$ 子和之外、满足任一固定（465.1）的实际包加入已付部分。有限多个 $k$ 的并集可沿同一 $\eta$ 用相同正权求和，交集只计一次；共同费用取这些实际乘积费用的包络。新增范围是联合长度条件，不能仅凭 $D_a\le U^{d_k}$ 删除对 $N_b$ 的限制。

在平衡点 $c=a=1$ 时，$D_a=N_b=\sqrt U$，对每个固定 $k\ge3,C_N$ 和充分大 $U$ 仍不满足（465.1）。完整单位核心、其余原包、原更大高度费用与 signed Robin restoration 均未支付；（465.3）—（465.4）没有证明完整原矩、严格幂次节省、$o(UK)$、RH 或逐整数 Robin 不等式。

## 追加锚（本行以下为增补区）

## 466. 物理行的低阶切面与完整原能量

**定理 466.1（平方与立方物理行的完整预算）。** 沿用定理 458.1 的原行算子、原列系数、全部固定物理表示与零延拓。另使用 [de Faveri Theorem 1.1 的三阶情形及 Goldmakher–Louvel 的二阶筛界](../../../Library/Analytic/faveri2026fixedorder.md#separating-the-lower-order-character-blocks)，包括所引原稿 `eq:quadratic-large-sieve` 已核对的 primary、ramified conductor 与有限 ray 接口。它们分别为

$$
\Theta_3(A,B)\ll_\epsilon(AB)^\epsilon
 \{A+B+(AB)^{2/3}\},\qquad
\Xi_2(A,B)\ll_\epsilon(AB)^\epsilon(A+B).
\tag{466.1}
$$

三阶筛的两个索引均为 cubefree；二阶筛的两个索引均为 squarefree。本节直接使用这两份既有结果。

固定有限物理标签 $j$，把原行的 good 理想部分记为 $v$，其中每个素估值均在 $0,\ldots,5$。其单位与 $S$-部分已经按原约定记入 $j$，且 $q_v\asymp U$，只差固定标签导致的常数因子。定义两个原物理行子集

$$
\mathcal R_{3,j}=\{v=r^2:r\text{ good、cubefree、非单位}\},
\qquad
\mathcal R_{2,j}=\{v=r^3:r\text{ good、squarefree、非单位}\}.
\tag{466.2}
$$

子集仍保留原行选择及非负有界 norm 权。这里的下标指 $S$ 外的实际字符阶数；固定 $S$-twist 仍保留，不把它的导子删除。两子集在 good 非单位 sixth-power-free 行中不相交。

令 $K=DN$，$b(h)$ 是定理 458.1 的同一个完整原系数，也允许再乘与行无关、绝对值至多为一的列乘子；该乘子须对所用 smooth 参数固定，或乘后系数的全部所需参数导数仍满足同一共同包络。原有限 Fourier 表示及必要的有限 profile 导数满足同一个除数型包络，组合成本写作 $\mathcal C$；它包含实际 profile 包络与（466.1）算子成本的乘积、有限标签及 smooth/Sobolev 恢复。Profiles 与 norm-twist 高度固定，或满足该共同费用为次幂的 polylog 合同，不扩大原高度许可。

把完整行能量限制到（466.2），分别记为 $Q_{3,j}(b),Q_{2,j}(b)$。则在所列解析输入下

$$
\begin{aligned}
Q_{3,j}(b)&\ll_\varepsilon
 \mathcal C^2(UK)^\varepsilon K
 \{U^{1/2}+K+U^{1/3}K^{2/3}\},\\
Q_{2,j}(b)&\ll_\varepsilon
 \mathcal C^2(UK)^\varepsilon K\{U^{1/3}+K\}.
\end{aligned}
\tag{466.3}
$$

特别地，对每个固定 $C_0>0$，当 $K\le C_0U$ 时，两类完整原行能量的和为

$$
\sum_j\{Q_{3,j}(b)+Q_{2,j}(b)\}
\ll_{\varepsilon,C_0}\mathcal C^2(UK)^\varepsilon UK.
\tag{466.4}
$$

该式保留完整原 $h=dn$，不要求 $h$ 平方自由或 $d,n$ 互素，也不要求 $D$ 或 $N$ 单独变短。

证明。固定一个原 Fourier 分量和物理标签。若 $v=r^2$，原乘法性连同零值给出
$\chi_h^{(6),\rm raw}(r^2)=\chi_h^{(3),\rm raw}(r)$；若 $v=r^3$，得到相同意义的二阶字符。单位与 $S$-部分以及源字符族的修正只产生原固定有限 ray 数据中的列 twist。按同一有限分区把它们吸收入系数；负 orientation 先整体共轭。三阶的行尺度为 $R_3\asymp U^{1/2}$，二阶为 $R_2\asymp U^{1/3}$。物理元素与其 good 理想、单位及 $S$-标签之间的有限重数已纳入共同成本。没有把素估值减模，也没有删掉原非单位处的零值。

在三阶行上唯一提取原列的全部立方：$h=\ell^3h_0$，其中 $h_0$ cubefree，允许 $h_0,\ell$ 相交。精确字符因子为

$$
\chi_{\ell^3h_0}^{(3),\rm raw}(r)
=\chi_{h_0}^{(3),\rm raw}(r)\mathbf1_{(\ell,r)=1}.
\tag{466.5}
$$

原系数的除数界和理想计数给出，对每个实际非空 $\ell$，

$$
\sum_{h_0\ {\rm cubefree}}
 |b(\ell^3h_0)|^2
\ll_\epsilon\mathcal P^2 K^{1+\epsilon}q_\ell^{-3}.
\tag{466.6}
$$

固定 $\ell$ 时，保留（466.5）的行限制后，只在正行范数中扩大该行集。用（466.1），列长为 $O(K/q_\ell^3)$；其筛界由单调性统一控制为 $\Theta_3(R_3,CK)$。再在同一个原行 Hilbert 空间使用 Minkowski。理想级数 $\sum_\ell q_\ell^{-3/2}$ 收敛，于是得到（466.3）的第一式。

二阶行上同样唯一写 $h=\ell^2h_0$，$h_0$ squarefree，并保留精确零值

$$
\chi_{\ell^2h_0}^{(2),\rm raw}(r)
=\chi_{h_0}^{(2),\rm raw}(r)\mathbf1_{(\ell,r)=1},\qquad
\sum_{h_0\ {\rm sf}}|b(\ell^2h_0)|^2
\ll_\epsilon\mathcal P^2K^{1+\epsilon}q_\ell^{-2}.
\tag{466.7}
$$

在固定 $\ell$ 的正行范数上用二阶筛，再用 Minkowski。原 annulus 给出 $q_\ell\ll\sqrt K$，而固定域理想和满足
$\sum_{q_\ell\ll\sqrt K}q_\ell^{-1}\ll\log(2K)$。这份对数及其平方由最终小幂支付，得（466.3）的第二式。两种提取都只对实际非空项求和；有界 subunit annuli 归入原固定 annular enlargement，更短项为零。列乘子不改变支持计数或除数包络，因此同样适用。

最后，当 $K\le C_0U$ 时，$K\ll U$ 且 $U^{1/3}K^{2/3}\ll_{C_0}U$，其余括号项也为 $O_{C_0}(U)$。有限物理分区、Fourier 分量及原允许的有限 smooth 参数都按共同成本恢复，不给每类行追加独立高度预算。由此得到（466.4）。证毕。

**命题 466.2（同权 F4 子和与剩余物理行）。** 沿用 [F1–F4](../../../Library/Analytic/faveri2026fixedorder.md#a-weighted-powerful-part-majorant-for-all-original-columns) 的全部原系数及 $s=1/2+\eta$。当 $K\le C_0U$ 时，实际 F4 包在（466.2）两类物理行上的完整能量，沿同一个 F4 正权的总和满足

$$
Z_s|\mathcal T|\sum_{c\ {\rm powerful}}
 q_c^s\tau(\operatorname{rad}c)
 \sum_{a\mid\operatorname{rad}c}\sum_{\kappa\in\mathcal T}
 \widetilde T^{{\rm sf},\,{\rm proper}}_{j;c,a,\kappa}
\ll_{\varepsilon,C_0}\mathcal C^2(UK)^\varepsilon UK.
\tag{466.8}
$$

证明。每个实际包的原系数具有同一除数型包络，支撑长度为 $X=K/q_c\ll K$，其列 mask 与有限过滤仍与物理行无关。把（466.4）的 $K$ 换成 $X$，得到完整包的 $UX$ 上界；这里只在包实际非空时应用固定 annular 合同。然后直接使用（464.14）的同一个临界 powerful-core 求和，并按一个最终 $\varepsilon$ 选择同一个 $\eta$ 与全部内部损失，得到（466.8）。没有估计独立 signed pole，也没有把正范数界相减。证毕。

在原平衡 $U\asymp K$、$D=N=\sqrt K$ 中，该行切面包含全部 $c=a=1$ 的平方自由列系数在这些物理行上的完整能量。这不要求这些列属于第 464–465 节的短因子范围。该切面也不是列对 $h,k$ 的比值阶数选择：已知的 $H_{2,j},H_{3,j},H_{6,j}$ 是列对的分块，不能将其有符号拼接直接认作（466.2）的正行能量。

把其余 good 非单位 sixth-power-free 行记为 $\mathcal R_{6,j}$。它们在 $S$ 外的字符阶数恰为六，因为其素估值不全被二整除，也不全被三整除。这给出同一个原正能量的精确行分拆

$$
Q(b)=Q_{\rm exc}(b)+
 \sum_j\{Q_{3,j}(b)+Q_{2,j}(b)+Q_{6,j}(b)\}.
\tag{466.9}
$$

有限 $S$-例外保持原处理。在 $K\le C_0U$ 范围内，完整 $UK$ 正预算仍需估计 $Q_{6,j}$；（466.3）在 $K/U$ 无界时也不自动给出 $UK$ 预算。原更大高度费用、完整六阶行及 signed Robin restoration 仍是独立义务；这些结论不证明 RH 或逐整数 Robin 不等式。

## 追加锚（本行以下为增补区）

## 467. 导子敏感的 plain 因子与六阶物理行的重复幂切面

**定理 467.1（同一完整原卷积的物理余数核截断）。** 沿用定理 458.1 的原始卷积、完整零延拓、固定有限 Fourier 表示和物理行，取原平衡尺度 $K=U$、$D=N=\sqrt U$，$U\ge2$。复用[三次与二次大筛的既有族接口](../../../Library/Analytic/faveri2026fixedorder.md#separating-the-lower-order-character-blocks)，以及[原稿](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex) lem:hecke-strip-growth 证明中的 primitive Hecke 函数方程与 lem:plain 的 ordinary reflection。共同费用 $\mathcal C$ 一次控制这些输入、原 profiles 及所需有限阶导数、固定有限 ray/物理分区和 smooth/Sobolev 恢复的实际乘积。Profiles 与 norm-twist 高度固定，或使该共同费用满足原 polylog 合同；不扩大原高度范围。

固定物理标签 $j$，令 $v$ 为行的 good 非单位 sixth-power-free 理想部分。用其原始素估值唯一分解

$$
v=a_2r_2^2=a_3r_3^3,\qquad
 a_2\text{ squarefree},\quad r_2\text{ cubefree},\qquad
 a_3\text{ cubefree},\quad r_3\text{ squarefree}.
\tag{467.1}
$$

不要求 $a_m,r_m$ 互素；$a_2,a_3$ 分别保留原素估值模二、模三的余数。这里分解的是物理行，不是列 $h=dn$ 或列对的比值。对 $1\le A_2,A_3\le U$，把原完整正行能量限制到 $q_{a_2}\le A_2$ 或 $q_{a_3}\le A_3$，分别记为 $Q^{[2]}_{\le A_2}(b),Q^{[3]}_{\le A_3}(b)$，包括全部原有限标签。则在所列解析输入及共同费用条件下，对每个 $\varepsilon>0$，

$$
\begin{aligned}
Q^{[2]}_{\le A_2}(b)
&\ll_\varepsilon \mathcal C^2U^\varepsilon
 \left\{U^{3/2}A_2+U^{3/2}A_2^{3/2}
              +U^{5/3}A_2^{7/6}\right\},\\
Q^{[3]}_{\le A_3}(b)
&\ll_\varepsilon \mathcal C^2U^\varepsilon
 \left\{U^{7/6}A_3^{4/3}+U^{4/3}A_3^{5/3}\right\}.
\end{aligned}
\tag{467.2}
$$

因此，$A_2\le U^{2/7}$ 与 $A_3\le U^{2/5}$ 时，两份能量及其行并集的能量均为 $O_\varepsilon(\mathcal C^2U^{2+\varepsilon})$。更精确地，若 $0\le\nu_2\le2/7$、$0\le\nu_3\le2/5$，则

$$
\begin{aligned}
Q^{[2]}_{\le U^{2/7-\nu_2}}(b)
 &\ll_\varepsilon\mathcal C^2U^{2-7\nu_2/6+\varepsilon},\\
Q^{[3]}_{\le U^{2/5-\nu_3}}(b)
 &\ll_\varepsilon\mathcal C^2U^{2-5\nu_3/3+\varepsilon}.
\end{aligned}
\tag{467.3}
$$

对固定正的 $\nu_m$，若共同费用为次幂且最终 $\varepsilon$ 足够小，（467.3）给出严格低于 $U^2$ 的幂次预算；$\nu_m=0$ 仅给出体积预算。这是同一个完整原卷积在指定行上的上界，含其全部列和列间干涉；不允许用任意列乘子替换原系数后仍直接使用结论。

证明。固定一个原有限 Fourier 分量 $\xi$。记未归一化的原因子为

$$
\mathsf M_\xi(v)=\sum_d\mu(d)V(q_d/D)\xi(d)\chi_d^{\rm raw}(v),\qquad
\mathsf S_\xi(v)=\sum_nW(q_n/N)\xi(n)\chi_n^{\rm raw}(v).
\tag{467.4}
$$

原乘法性给出该完整原列多项式恰为 $\mathsf M_\xi(v)\mathsf S_\xi(v)$。两因子使用同一个字符、所有原零值和固定过滤；负 orientation 整体共轭。

首先按实际导子估计 plain 因子。设 $\mathfrak f_v$ 是 $\xi\chi^{\rm raw}_{(\cdot)}(v)$ 的 primitive inducing conductor，$F_v=q_{\mathfrak f_v}$。Good 素数处的行估值为 $1,\ldots,5$，故每个这样的素数均保留非平凡局部 Kummer 分歧；固定 $\xi$ 不能消去 $S$ 外的分歧。该字符非主。所有额外固定 $S$ 零值按原有限 Euler 因子保留，且

$$
F_v\ll_S q_{\operatorname{rad}v}\le q_{a_m}q_{r_m},\qquad m=2,3.
\tag{467.5}
$$

已有 primitive Hecke 函数方程及 entireness 给出所用普通平滑字符和界

$$
|\mathsf S_\xi(v)|\ll_\delta
 C_{\xi,\mathrm{ref}}F_v^{1/2+\delta},\qquad \delta>0.
\tag{467.6}
$$

具体地，在原 Mellin 公式中移到 $\Re s=-\delta$，不穿过极点；函数方程把 $L(-\delta+it)$ 控制为 $O_\delta(F_v^{1/2+\delta}(3+|t|)^{1+2\delta})$，而对偶 $L(1+\delta-it)$ 由绝对 Euler 收敛控制。$N^{-\delta}\le1$，原紧支撑 profile 的 Mellin 衰减支付积分。固定坏素的删除因子只改变固定常数。纯 norm twist 及所需有限 profile 导数按照同一函数方程与 gamma 商的多项式高度费用纳入 $C_{\xi,\mathrm{ref}}$；该费用不按行或 $a_m$ 重选。此处复用普通函数方程与平滑和方法，不将其另列为新定理。

在一个 $q_{a_2}\asymp A$ 的 dyadic 块上，$q_{r_2}\asymp R=(U/A)^{1/2}$。固定实际 $a_2$ 后，零延拓下的精确恒等式为

$$
\chi_d^{\rm raw}(a_2r_2^2)
 =\chi_d^{\rm raw}(a_2)\chi_d^{(3),\rm raw}(r_2).
\tag{467.7}
$$

把 $\xi(d)\chi_d^{\rm raw}(a_2)$ 留在原 Möbius 列系数中。它与行 $r_2$ 无关，模长至多一；移动 $a_2$ 的导子没有被当作筛常数。非零 $\mu(d)$ 已使列 $d$ squarefree，从而 cubefree。行 $r_2$ cubefree，原 row selector、$a_2,r_2$ 重叠及其零值保留；只在正行范数中扩大允许的 $r_2$。按第 466 节复用的固定有限族接口和三阶筛，

$$
\sum_{r_2}\Omega\left|\mathsf M_\xi(a_2r_2^2)\right|^2
 \ll_\delta C_{\xi,M}^2(UD)^\delta
 D\{R+D+(RD)^{2/3}\}.
\tag{467.8}
$$

（467.5）—（467.6）在同一块上给出 $|\mathsf S_\xi|^2\ll C_{\xi,\mathrm{ref}}^2(AR)^{1+\delta}$，重新命名内部 $\delta$。该块至多有 $O(A)$ 个 $a_2$，所以其完整原乘积能量为

$$
\ll_\delta\mathcal C^2U^\delta
 A^2RD\{R+D+(RD)^{2/3}\}
=\mathcal C^2U^\delta
 \{AUD+U^{1/2}A^{3/2}D^2+U^{5/6}A^{7/6}D^{5/3}\}.
\tag{467.9}
$$

这里利用 $A,R,D$ 都在固定多项式范围，将所有内部小幂统一纳入最终损失。再代入 $D=\sqrt U$，沿 $A\le A_2$ 的 dyadic 块正求和，得到（467.2）第一式。$a_2=1$ 单独作为长度一块处理。

同样，在 $q_{a_3}\asymp A$ 的块上，$R=(U/A)^{1/3}$，$r_3$ squarefree，且
$\chi_d^{\rm raw}(a_3r_3^3)=\chi_d^{\rm raw}(a_3)\chi_d^{(2),\rm raw}(r_3)$。保留原 Möbius 列的 squarefree 支撑，使用既有二阶筛与（467.6），得到同一原乘积块的能量

$$
\ll_\delta\mathcal C^2U^\delta A^2RD(R+D)
=\mathcal C^2U^\delta
 \{U^{2/3}A^{4/3}D+U^{1/3}A^{5/3}D^2\}.
\tag{467.10}
$$

代入 $D=\sqrt U$ 并正求和，给出第二式。所有原有限 Fourier 分量、物理标签及有限 smooth 参数用同一个实际乘积成本包络恢复。取内部损失小于所给最终 $\varepsilon$，便得（467.2）。代入两个阈值，并逐项比较幂次，得到（467.3）。行并集的能量不超过两份正能量之和，交集只计一次。证毕。

**命题 467.2（实际六阶行及精确剩余域）。** 第 467.1 节的物理行切面可包含 $S$ 外实际字符阶数为六的行。它与仅取 $a_2=1$ 或 $a_3=1$ 的平方、立方物理行不同；对平方自由的充分大物理行，两种截断均不成立。

证明。保留原有非零行权 $\Omega$ 及一个允许的固定物理标签 $j$。记其范数因子为 $s_j>0$，即物理行 $u$ 满足 $q_u=s_jq_v$。在原 $\Omega$ 的正支撑内固定 $t_0>0$，并取固定常数 $0<c_1<c_2<(s_j/t_0)^{2/3}$。取不同 good 素理想 $p,\ell$，令 $q_p=P\to\infty$，并在所需固定 ray 类中选取 $c_1P^2\le q_\ell\le c_2P^2$。固定 ray 类中的素理想定理提供这样的 $\ell$，且可避开 $pS$。令 $v=\ell p^3$、$U=s_jq_\ell P^3/t_0$，则原行权仍在同一点读取 $\Omega(q_u/U)=\Omega(t_0)>0$，没有更换原 annulus。其模三余数核为 $a_3=\ell$、$r_3=p$，且 $q_\ell\le(s_j/t_0)^{2/3}P^2$ 恰好推出 $q_{a_3}\le U^{2/5}$。该行有原素估值 $1,3$，因而 good 部分既非平方也非立方，其诱导字符在 $S$ 外的阶数为六。有限物理类、单位与 $S$-标签仍按原允许分区选择。此处只给出原允许行族中的实例，不断言检测器实际选中该行，也不给出其完整原系数响应的正下界。

若 $v$ squarefree，则 $a_2=a_3=v$，$q_v\asymp U$ 大于两个严格次线性阈值，故原平方自由物理行仍在余域。证毕。

令 $\mathcal V_{\rm cut}$ 为同一原行族中满足 $q_{a_2}\le U^{2/7}$ 或 $q_{a_3}\le U^{2/5}$ 的行并集，$\mathcal V_{\rm rem}$ 为其补集。完整原正能量具有精确分拆

$$
Q(b)=Q_{\rm exc}(b)+Q_{\mathcal V_{\rm cut}}(b)
                         +Q_{\mathcal V_{\rm rem}}(b).
\tag{467.11}
$$

本条支付 $\mathcal V_{\rm cut}$ 上的原始整向量能量；所有列内与列间干涉均留在该范数中。它不从整向量的界反推孤立 F4 包的界，因为 squarefree projector 后的系数不再直接具有（467.4）的原乘积。$\mathcal V_{\rm rem}$、其他原长度与更大高度费用、F4 的相应新运输及 signed Robin restoration 仍需独立估计；本节不证明 RH 或逐整数严格 Robin 不等式。

## 追加锚（本行以下为增补区）

## 468. 整体 plain 反射与更大的物理奇偶核切面

**定理 468.1（反射完整原因子后的奇偶核预算）。** 保持定理 467.1 的原完整卷积、物理行、有限 Fourier 表示、原零延拓及平衡尺度 $D=N=\sqrt U$、$K=U$。复用[三次大筛的既有族接口](../../../Library/Analytic/faveri2026fixedorder.md#separating-the-lower-order-character-blocks)、第 466 节的列立方提取，以及[原稿](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex) lem:plain 的 normalized ordinary reflection、`old-eq:2.1c`—`old-eq:2.1d` 和 smooth-calculus。令 $\mathcal C$ 包络这些输入、原 profiles 与反射 profiles 所需有限阶导数、原有限物理/ray/Fourier 分区及尺度 supremum 恢复的实际共同费用；所有 norm-twist 高度仍在原固定或 polylog 合同内，不扩大原高度范围。

仍用 $v=ar^2$，其中 $a$ squarefree、$r$ cubefree，允许重叠。对 $1\le A_*\le U$，令 $Q^{[2]}_{\le A_*}(b)$ 为同一个完整原正行能量在 $q_a\le A_*$ 上的限制。则在这些解析输入和共同费用条件下，对每个 $\varepsilon>0$，

$$
Q^{[2]}_{\le A_*}(b)
\ll_\varepsilon\mathcal C^2U^\varepsilon
\left\{U^{3/2}A_*^{1/2}
       +U^{3/2}A_*^{3/2}+U^{5/3}A_*\right\}.
\tag{468.1}
$$

因此，$A_*\le U^{1/3}$ 时，这份完整原能量为 $O_\varepsilon(\mathcal C^2U^{2+\varepsilon})$。若 $0\le\nu\le1/3$，则

$$
Q^{[2]}_{\le U^{1/3-\nu}}(b)
\ll_\varepsilon\mathcal C^2U^{2-\nu+\varepsilon}.
\tag{468.2}
$$

严格幂次节省要求固定 $\nu>0$、共同费用为次幂且最终 $\varepsilon$ 足够小。本结论只适用于所列原完整卷积，不对任意附加列乘子或 squarefree projector 后的孤立 F4 包作此断言。

证明。先固定原有限物理标签和一个乘法 Fourier 分量 $\xi$。以 $\psi_v^0(h)=\xi(h)\chi_h^{\rm raw}(v)$ 表示其同一个自然 Hecke 字符，原多项式是（467.4）的 $\mathsf M_\xi(v)\mathsf S_\xi(v)$。负 orientation 整体共轭。以下所有反射均在原允许物理行上进行，之后才扩大正行范数。

把 cubefree 理想 $r$ 唯一写成

$$
r=bc^2,\qquad b,c\text{ squarefree},\quad(b,c)=1.
$$

再令 $e_1=(a,b)$、$e_2=(a,c)$，写 $b=e_1b_0$、$c=e_2c_0$。于是 $e_1,e_2$ 是 $a$ 的互素约数，$a,b_0,c_0$ 两两互素，且

$$
v=ae_1^2e_2^4b_0^2c_0^4,\qquad
\operatorname{rad}v=ab_0c_0.
\tag{468.3}
$$

在 $q_a\asymp A$、$q_{c_0}\asymp C$ 的块上固定实际 $a,c_0,e_1,e_2$。令

$$
R=(U/A)^{1/2},\qquad E=q_{e_1}q_{e_2}^2\ge1,
\qquad B=R/(EC^2).
\tag{468.4}
$$

原行 annulus 给出 $q_{b_0}\asymp B$；实际非空块的 $B$ 可在固定 annular 常数内裁剪为至少一。每个 good 素处的原估值在 $1,\ldots,5$，故 primitive inducing character 的该局部分歧非平凡、导子指数恰为一；固定 $\xi$ 不能消去它。非单位 good 行对应非主字符。原固定 $S$ 的分歧与额外零值经原有限分区保留。因此其实际 primitive 导子范数和自然字符的 redundant radical 满足

$$
F_v\asymp_S q_aq_{b_0}q_{c_0}\asymp ACB=:F,
\qquad \mathfrak R_{0,v}\text{ 仅支持在固定 }S.
\tag{468.5}
$$

这里不把移动的 $a,c_0,b_0$ 导子视为筛常数。

使用 normalized 原因子 $\mathsf m_v=D^{-1/2}\mathsf M_\xi(v)$、$\mathsf s_v=N^{-1/2}\mathsf S_\xi(v)$。完整原能量是 $DN\sum_v\Omega|\mathsf m_v\mathsf s_v|^2=U\sum_v\Omega|\mathsf m_v\mathsf s_v|^2$。原稿 lem:plain 的精确反射把 $\mathsf s_v$ 写成模长一的 root number 乘以 normalized 共轭字符和。primitive 主尺度为 $C_v/N$，其中 $C_v=3F_v/(2\pi)^2$。保留自然零值时，其精确项为

$$
\mathsf s_v=\varepsilon_v
\sum_{\substack{d_0\mid\mathfrak R_{0,v}\\
                 \operatorname{rad}h_0\mid\mathfrak R_{0,v}}}
\frac{\mu(d_0)\psi_v^*(d_0)\overline{\psi_v^*(h_0)}}
 {\sqrt{q_{d_0}q_{h_0}}}\,
T_{\overline{\psi_v^0}}
 \left(\frac{C_vq_{d_0}}{Nq_{h_0}};W^\sharp\right).
\tag{468.6}
$$

这里 $\psi_v^*$ 为 primitive inducing character，$T$ 为所引原稿的 normalized plain 和。固定 $S$ 使上述 Euler 系数的绝对总质量一致有界；它们的相位可随行变化，但在正范数的三角不等式中只用其绝对值。保持 normalized 形式，避免把缩短尺度的归一化移入这份质量后丢失可和性。没有删去 good collision zeros，也没有将本来的零值补成一。

反射 profile 在零处有界，Euler 导数同样有界，在无穷处任意快衰减。直接复用所引原稿的 annular 分解：相对主尺度下方的 normalized 权为 $O(2^{-j/2})$，上方权任意快衰减。对任意固定小 $\xi_0>0$，上方超出 $U^{\xi_0}$ 的项以及主尺度小于 $U^{-\xi_0}$ 的项可用任意幂衰减和绝对计数控制。对保留的非空 annuli，原支持判据允许把有界 subunit 尺度裁剪到一。经原 smooth-calculus 的有限阶 Sobolev 尺度 supremum 恢复后，全部保留项具有共同、与移动 $b_0$ 无关的 annular profiles，尺度满足

$$
X=DY\ll F U^{O(\xi_0)}.
\tag{468.7}
$$

同一块上实际主尺度虽依赖行，但都在同一多项式尺度区间；supremum 由原有限阶 profile 导数和对数数量的单位盒支付，而非允许任意行依赖列系数。所有尾部和有限 Euler 质量均计入同一 $\mathcal C$。

在每个完整乘积的绝对值内共轭整个反射 plain 因子，原 Möbius 因子保持不变。于是它们重新使用同一个 $\psi_v^0$；root number 的模长为一，不留下未付的行相位。在每个反射项、annulus、恢复尺度和 profiles 均固定后，对应的完整 normalized 卷积多项式为

$$
\sum_h\beta_X(h)\psi_v^0(h),\qquad
\beta_X(h)=X^{-1/2}\sum_{dn=h}
\mu(d)V(q_d/D)\widetilde W(q_n/Y).
\tag{468.8}
$$

它含所有 $h=dn$、公因子与原零值；$\beta_X$ 与 $b_0$ 无关。有限 profile 导数具有同一除数包络。由（468.3），其字符恰为

$$
\psi_v^0(h)=\xi(h)
 \chi_h^{\rm raw}(ae_1^2e_2^4c_0^4)
 \chi_h^{(3),\rm raw}(b_0).
\tag{468.9}
$$

把前两个因子留在列系数中，模长至多一，不更改其原零值。其移动导子没有进入三次筛的常数。

现在对整个（468.8）使用第 466 节的列立方提取，而非对单独 Möbius 因子取界。写 $h=\ell^3h_1$，$h_1$ cubefree，允许 $h_1,\ell$ 重叠；原字符保留 $\mathbf1_{(\ell,b_0)=1}$。除数包络、$X$ 归一化及理想计数给出

$$
\sum_{h_1\ {\rm cubefree}}
|\beta_X(\ell^3h_1)|^2
\ll_\delta\mathcal P^2X^\delta q_\ell^{-3}.
\tag{468.10}
$$

仅在每个固定 $\ell$ 的正行范数内扩大 $b_0$ 的允许集；此时才解除原 $b_0$ 与固定标签的互素限制。未把（468.5）的实际导子恒等式宣称在新加入的行上成立。$b_0$ squarefree，因而 cubefree，三次筛两侧均满足其条件。复用 $\sum_\ell q_\ell^{-3/2}<\infty$ 的 Minkowski 求和和（466.1），得到固定 $a,c_0,e_1,e_2$ 上的完整原能量

$$
\ll_\delta\mathcal C^2U^{1+\delta}
 \{B+F+(BF)^{2/3}\}.
\tag{468.11}
$$

这里已先按最终损失选择 $\xi_0$，把（468.7）的扩大和所有内部小幂收入 $U^\delta$；反射与尺度 supremum 需要的固定有限导数也已同时计入。所引函数方程、三次筛与列幂提取均是复用的中间工具。

每个 $q_a\asymp A$ 的块有 $O(A)$ 个 $a$，每个 $q_{c_0}\asymp C$ 的块有 $O(C)$ 个 $c_0$；每个 $a$ 的 $(e_1,e_2)$ 选择只有除数型数量。由（468.4）—（468.5），乘以 $ACU$ 后的三项分别为

$$
\frac{U^{3/2}A^{1/2}}{EC},\qquad
\frac{U^{3/2}A^{3/2}}E,\qquad
\frac{U^{5/3}A}{E^{4/3}C}.
\tag{468.12}
$$

先用 $E\ge1$ 取统一上界，除数数量收入任意小幂。对实际非空 $C$ 的 dyadic 块求和：第一、三项的 $C^{-1}$ 可和，第二项只付对数；单位 $c_0$ 单独归入尺度一。再对 $A\le A_*$ 的 dyadic 块正求和，并恢复全部原有限分量及 smooth 参数，得到（468.1）。单位 $a$ 同样作为尺度一处理。代入 $A_*=U^{1/3-\nu}$，三项指数依次为 $5/3-\nu/2$、$2-3\nu/2$ 和 $2-\nu$；对 $0\le\nu\le1/3$，均不超过 $2-\nu$，得到（468.2）。证毕。

**命题 468.2（超出两个旧核截断的原六阶行）。** 在原非零行权及允许有限物理类下，（468.1）的 $q_a\le U^{1/3}$ 可包含同时不满足 $q_{a_2}\le U^{2/7}$ 和 $q_{a_3}\le U^{2/5}$ 的实际六阶物理行。

证明。保持原行权 $\Omega$ 和一个允许物理标签 $j$，令其范数因子为 $s_j>0$。固定 $t_0$ 在 $\Omega$ 的正支撑内，以及 $0<c_1<c_2<(s_j/t_0)^{1/2}$。在所需固定 ray 类中选取不同 good 素理想 $p,\ell$，使 $q_p=P\to\infty$、$c_1P\le q_\ell\le c_2P$；固定 ray 类中的素理想定理给出此选择，可避开 $S$。取

$$
v=\ell p^2,\qquad U=s_jq_\ell P^2/t_0.
\tag{468.13}
$$

原权仍为 $\Omega(q_u/U)=\Omega(t_0)>0$。其奇偶核 $a_2=\ell$ 满足 $q_\ell^2\le(s_j/t_0)P^2$，故 $q_{a_2}\le U^{1/3}$。又 $q_{a_2}\asymp U^{1/3}>U^{2/7}$，而 $a_3=v$、$q_{a_3}\asymp U>U^{2/5}$，均对充分大 $P$ 成立。原估值 $1,2$ 使 $S$ 外字符阶数恰为六。这里仅给出原允许行族中的实例，不断言检测器实际选中该行，也不给出其完整原能量的正下界。证毕。

因而，令 $\mathcal C_{468}=\mathcal C$，并令 $\mathcal C_{467,[3]}$ 为第 467 节模三支路实际使用的二阶筛、反射与其余共同费用包络。同一原正能量在 $q_{a_2}\le U^{1/3}$ 或 $q_{a_3}\le U^{2/5}$ 的行并集上满足 $O_\varepsilon((\mathcal C_{468}^2+\mathcal C_{467,[3]}^2)U^{2+\varepsilon})$，交集只计一次；若使用单一包络，须同时覆盖这两条支路。原平方自由的充分大物理行仍满足 $a_2=a_3=v$，属于剩余域。完整余域、其他长度或高度费用、F4 的对应新运输和 signed Robin restoration 仍需独立估计；本节不证明 RH 或逐整数严格 Robin 不等式。

## 追加锚（本行以下为增补区）

## 469. 原始素估值的联合切面与完整原能量

**定理 469.1（三次幂素估值方向的联合预算）。** 保持定理 467.1 的原始完整卷积、原非负行权、固定有限物理/ray/Fourier 表示和零延拓，取 $D=N=\sqrt U$、$K=U$、$U\ge2$。直接复用（467.5）—（467.6）的实际 primitive 导子及 plain 因子界和（466.1）的二次筛族接口。令 $\mathcal C_{\rm val}$ 一次包络该二次筛、原 plain 因子估计、profiles 所需有限阶导数、有限分量与 smooth/Sobolev 恢复的实际乘积费用。所有 norm-twist 高度仍满足原固定或 polylog 合同。

固定有限物理标签后，把 good 非单位 sixth-power-free 理想行唯一写成

$$
v=R_1R_2^2R_3^3R_4^4R_5^5,
\qquad R_i\text{ 两两互素且 squarefree}.
\tag{469.1}
$$

$R_i$ 只包含原素估值恰为 $i$ 的素理想，不是列 $h=dn$ 的幂次提取，也不把原行估值减模。定义同一物理行的读数

$$
\mathscr H_3(v)=\frac{q_{\operatorname{rad}v}^{2}}{q_{R_3}}.
\tag{469.2}
$$

对固定 $C_0\ge1$ 和 $1\le T\le C_0U$，令 $Q^{\langle3\rangle}_{\le T}(b)$ 为同一个完整原正行能量在 $\mathscr H_3(v)\le T$ 上的限制，包括全部原有限物理标签。则在所列解析输入及共同费用条件下，对每个 $\varepsilon>0$，

$$
Q^{\langle3\rangle}_{\le T}(b)
\ll_{\varepsilon,C_0}\mathcal C_{\rm val}^{2}
U^{1+\varepsilon}T.
\tag{469.3}
$$

特别地，$T=U$ 给出 $O_\varepsilon(\mathcal C_{\rm val}^{2}U^{2+\varepsilon})$ 的体积预算；对 $0\le\nu\le1$，取 $T=U^{1-\nu}$ 得

$$
Q^{\langle3\rangle}_{\le U^{1-\nu}}(b)
\ll_\varepsilon\mathcal C_{\rm val}^{2}U^{2-\nu+\varepsilon}.
\tag{469.4}
$$

固定 $\nu>0$、共同费用为次幂且最终 $\varepsilon$ 足够小时，后一式严格低于 $U^2$。这是原完整 $\mu*\mathrm{plain}$ 卷积的行子域估计；不允许在原系数上增加任意列乘子后直接使用，也不推断孤立 F4 包的相同预算。

证明。固定一个原乘法 Fourier 分量 $\xi$ 和物理标签。其完整原列多项式仍恰为（467.4）的两个未归一化原因子之积，即 $\mathsf M_\xi(v)\mathsf S_\xi(v)$。两个因子使用同一个自然字符、全部原零值和固定过滤；负 orientation 整体共轭。这里只沿用已有 plain 界和二次筛，不另立函数方程或筛定理。

把（469.1）的五个 norm 分到 $q_{R_i}\asymp X_i$ 的 dyadic 块。单位因子归入尺度一；非空 subunit 尺度只作原固定 annular enlargement。记

$$
F=\prod_{i=1}^5X_i,\qquad
G=\prod_{i\ne3}X_i=F/X_3.
\tag{469.5}
$$

原 annulus 给出 $\prod_iX_i^i\asymp U$，故 $X_3\ll U^{1/3}$。如果该块有原允许行满足（469.2）的截断，则

$$
F^2/X_3\ll T.
\tag{469.6}
$$

固定实际 $R_1,R_2,R_4,R_5$，只让原 $R_3$ 变化。其 good 素估值仍在 $1,\ldots,5$，且各 $R_i$ 在原允许行上互素，故（467.5）使用的非主 primitive inducing character 具有实际导子范数 $F_v\asymp_S q_{\operatorname{rad}v}\asymp F$。Good collision zeros 已在该字符中，额外 $S$ 零值按原固定 Euler 因子保留。（467.6）于是给出原允许行上的统一界

$$
|\mathsf S_\xi(v)|^2
\ll_\delta C_{\xi,\rm plain}^{2}F^{1+\delta}.
\tag{469.7}
$$

先在这些原允许行上取此界，再估计剩余 Möbius 因子的正范数；不把导子公式运输到新增的非互素行。对该因子，原零延拓下的精确式为

$$
\chi_d^{\rm raw}(v)
=\chi_d^{\rm raw}(R_1R_2^2R_4^4R_5^5)
 \chi_d^{(2),\rm raw}(R_3).
\tag{469.8}
$$

把 $\xi(d)\chi_d^{\rm raw}(R_1R_2^2R_4^4R_5^5)$ 留在原 Möbius 列系数中。它与变化的 $R_3$ 无关，模长至多一；其移动导子没有进入筛常数。列 $d$ 因 $\mu(d)$ 而 squarefree，行 $R_3$ 也 squarefree。保留所有原行限制、与固定四个因子的互素条件及零值后，只在该正范数中扩大行集。直接使用（466.1）的二次筛得到

$$
\sum_{R_3\ {\rm original}}\Omega
 |\mathsf M_\xi(v)|^2
\ll_\delta C_{\xi,2}^{2}(UD)^\delta
D(X_3+D).
\tag{469.9}
$$

这不是对原两因子分别选取一个最优实现，而是在同一原行上先用（469.7），再对同一 $\mathsf M_\xi$ 作正范数估计。固定的四个实际理想至多有 $O(G)$ 种；遗忘其互素限制只用于这份正计数。乘合（469.7）—（469.9）并吸收任意小幂，该块的完整原能量为

$$
\ll_\delta\mathcal C_{\rm val}^{2}U^\delta
\left\{DF^2+D^2F^2/X_3\right\}.
\tag{469.10}
$$

由 $D=\sqrt U$、（469.6）及 $X_3\ll U^{1/3}$，第一项为 $O(TU^{5/6})$，第二项为 $O(TU)$。五个原估值位置只有对数幂数量的非空 dyadic 块。选择内部损失小于最终 $\varepsilon$，对这些块正求和，再以同一实际乘积费用恢复全部原有限分量和所需有限 profile 导数，得到（469.3）。恢复导数时只用原乘积结构的有限阶 Leibniz 展开；不引入任意行依赖系数或额外高度预算。（469.4）由代入得到。证毕。

同一读数也给出按原素估值表达的联合区域：

$$
\frac{\mathscr H_3(v)}{q_v}
=\frac{q_{R_1}}{q_{R_3}^{2}q_{R_4}^{2}q_{R_5}^{3}}.
\tag{469.11}
$$

因此，原允许行中满足 $q_{R_1}\le q_{R_3}^{2}q_{R_4}^{2}q_{R_5}^{3}$ 的部分均有体积预算；这里取固定 $C_0$ 覆盖原 annulus 和有限物理标签的 $q_v/U$ 上界。此处每个 $R_i$ 必须来自同一个实际行，不能拼合不同对象上分别可达的 norm 值。

**命题 469.2（两个既有核截断之外的实际六阶行）。** 保持原非零行权及允许有限物理类，存在任意大的原允许行，满足 $\mathscr H_3(v)\le U^{21/22}$，却同时满足 $q_{a_2}>U^{1/3}$ 与 $q_{a_3}>U^{2/5}$，其中 $a_2,a_3$ 为（467.1）的原物理余数核。

证明。固定原行权 $\Omega$、一个允许物理标签 $j$ 及其范数因子 $s_j>0$，并在 $\Omega$ 的正支撑内固定 $t_0>0$。先取 good 素理想 $p$，$q_p=P\to\infty$；在所需固定 ray 类中，固定 ray 类的素理想定理提供不同 good 素理想 $r,\ell$，满足 $q_r\asymp P^2$、$q_\ell\asymp P^3$，可避开 $pS$。取

$$
v=\ell p^2r^3,\qquad U=s_jq_v/t_0\asymp P^{11}.
\tag{469.12}
$$

原行权仍在同一点取值 $\Omega(q_u/U)=\Omega(t_0)>0$。其五个原素估值因子为 $R_1=\ell$、$R_2=p$、$R_3=r$、$R_4=R_5=1$，故

$$
\mathscr H_3(v)=q_\ell^2q_p^2q_r\asymp P^{10}
 < U^{21/22}
\tag{469.13}
$$

对充分大的 $P$ 成立，因为 $11\cdot21/22=21/2>10$。另一方面，$a_2=\ell r$、$a_3=\ell p^2$，二者 norm 均为 $\asymp P^5$，分别严格大于 $U^{1/3}\asymp P^{11/3}$、$U^{2/5}\asymp P^{22/5}$。原素估值 $1,2,3$ 使 $S$ 外字符阶数恰为六。此处只给出原允许行族中的实例，不断言检测器实际选中该行，也不给出其完整原能量的正下界。证毕。

将（469.3）的行区域与第 468 节奇偶核区域、第 467 节模三核区域合并时，只能使用覆盖实际三条支路的共同费用包络，或保留它们三个平方费用之和，交集只计一次。原平方自由的充分大物理行仍满足 $R_1=v$、$R_3=1$，故 $\mathscr H_3(v)=q_v^2\asymp U^2$，仍在当前截断之外。其余原行、其他长度和高度费用、F4 的新运输及 signed Robin restoration 仍需独立估计；本节不证明 RH 或逐整数严格 Robin 不等式。

## 追加锚（本行以下为增补区）

## 470. 原始二、四估值的联合 cubefree 行切面

**定理 470.1（共同保留二、四估值的完整原能量）。** 保持第 469 节的同一个原始完整卷积、原非负行权、固定有限物理/ray/Fourier 表示、零延拓及平衡尺度 $D=N=\sqrt U$、$K=U$。直接复用第 468 节的实际 primitive 导子、完整 normalized plain 反射、有限 Euler 与 annular/supremum 恢复，以及（466.1）的两个索引均为 cubefree 的三次筛和（468.10）的列立方提取。共同包络 $\mathcal C_{24}$ 包含这些输入、profiles 的所需有限阶导数、原有限分量与 smooth/Sobolev 恢复的实际乘积费用。高度仍为原固定或相应次幂成本的 polylog 范围。

对同一个 good 非单位 sixth-power-free 物理行使用（469.1）的唯一分解，记 $x_i=q_{R_i}$，定义

$$
\begin{aligned}
f(v)&=q_{\operatorname{rad}v}=\prod_{i=1}^5x_i,\\
g(v)&=x_1x_3x_5,\qquad b(v)=x_2x_4^2,\\
\mathscr H_{24}(v)
&=g(v)\{b(v)+f(v)+(b(v)f(v))^{2/3}\}\\
&=f(v)x_4+\frac{f(v)^2}{x_2x_4}
 +f(v)^{5/3}\left(\frac{x_4}{x_2}\right)^{1/3}.
\end{aligned}
\tag{470.1}
$$

对固定 $C_0\ge1$ 和 $1\le T\le C_0U$，令 $Q^{\langle24\rangle}_{\le T}(b)$ 为完整原正能量在 $\mathscr H_{24}(v)\le T$ 上的限制，保留全部原有限物理标签。则在所列解析输入及共同费用条件下，对每个 $\varepsilon>0$，

$$
Q^{\langle24\rangle}_{\le T}(b)
\ll_{\varepsilon,C_0}\mathcal C_{24}^2U^{1+\varepsilon}T.
\tag{470.2}
$$

特别地，$T=U^{1-\nu}$、$0\le\nu\le1$ 给出 $O_\varepsilon(\mathcal C_{24}^2U^{2-\nu+\varepsilon})$；严格节省要求固定 $\nu>0$、共同费用为次幂且最终损失足够小。这是原始完整卷积的新行子域消费，不是任意列乘子或孤立 F4 包的估计。

证明。固定原有限物理标签、一个乘法 Fourier 分量及 $q_{R_i}\asymp X_i$ 的 dyadic 块。记

$$
F=\prod_iX_i,\qquad G=X_1X_3X_5,\qquad B=X_2X_4^2.
\tag{470.3}
$$

固定实际 $R_1,R_3,R_5$，共同保留

$$
r=R_2R_4^2.
\tag{470.4}
$$

它是 cubefree，范数为 $\asymp B$；$r$ 唯一确定 $R_2,R_4$，所以它们不再作为外部标签计数。原允许行上 $v=R_1R_3^3R_5^5r^2$，实际非主 primitive 导子范数为 $\asymp F$。只在这些原行上使用第 468 节的完整 normalized plain 反射及（468.6）—（468.8）的恢复。每个反射项、annulus、恢复尺度和 profiles 固定后，同一个 normalized 完整乘积写成列多项式，系数 $\beta_X(h)$ 与变化的 $r$ 无关，长度 $X\ll FU^{O(\xi_0)}$。这里同时把（468.6）的有限 Euler 质量、全部尾部与所需导数收入共同费用；没有把行依赖的实际主尺度直接变成行依赖列系数。

整个反射 plain 因子在绝对乘积内共轭后，原字符连同零值精确为

$$
\psi_v^0(h)=\xi(h)
 \chi_h^{\rm raw}(R_1R_3^3R_5^5)
 \chi_h^{(3),\rm raw}(r).
\tag{470.5}
$$

前两个因子与 $r$ 无关，留在列系数中且模长至多一；它们的移动导子没有进入筛常数。对整个列多项式直接复用（468.10）的 $h=\ell^3h_0$ 提取、全部 collision zeros、$q_\ell^{-3}$ 系数质量和可和的 Minkowski。只在每个固定 $\ell$ 的正行范数中，才把 $r$ 扩大为范数 $\asymp B$ 的 cubefree 行；不再要求新增行满足原分解的互素性或实际导子恒等式。原块中 $R_2,R_4$ 各自的 norm 限制也只在这一步放宽。两个筛索引都为 cubefree，因此（466.1）给出固定三个实际标签后的完整原能量

$$
\ll_\delta\mathcal C_{24}^2U^{1+\delta}
 \{B+F+(BF)^{2/3}\}.
\tag{470.6}
$$

若 $r$ 为单位，单独用列 Cauchy 支付括号中的 $F$ 项。反射中的全部实际非空 subunit annuli、固定有限导数及 $U^{O(\xi_0)}$ 扩大按第 468 节同一合同处理；先适配最终损失选 $\xi_0$，不增加原高度预算。

三个实际固定标签至多 $O(G)$ 个。因此整个块的正能量至多

$$
\mathcal C_{24}^2U^{1+\delta}
 G\{B+F+(BF)^{2/3}\}.
\tag{470.7}
$$

若块与 $\mathscr H_{24}\le T$ 相交，则括号乘积为 $O(T)$，因为所有 dyadic 因子与（470.1）的同一实际行读数只差固定常数。仅对这些块正求和；至多对数次幂个块和原有限分量由最终 $\varepsilon$ 支付，得到（470.2）。全部列内、列间及不同原分解的交叉项均保留在原完整范数中。证毕。

**推论 470.2（可比较的联合素估值区域）。** 在同一解析与共同费用合同下，原允许行中满足

$$
x_1\le x_2x_3x_4^3x_5^3
\tag{470.8}
$$

的部分具有 $O_\varepsilon(\mathcal C_{24}^2U^{2+\varepsilon})$ 的完整原能量。

证明。对同一实际行 $q_v=x_1x_2^2x_3^3x_4^4x_5^5$，（470.1）三项与 $q_v$ 的比值分别为

$$
\frac1{x_2x_3^2x_4^2x_5^4},\qquad
\frac{x_1}{x_2x_3x_4^3x_5^3},\qquad
\left(\frac{x_1}{x_2x_3^2x_4^3x_5^5}\right)^{2/3}.
\tag{470.9}
$$

$x_i\ge1$，所以（470.8）使三项均至多一。取固定 $C_0$ 支付 $3q_v/U$ 的原 annular 与物理标签常数，再用（470.2）。证毕。

**命题 470.3（超出全部既有物理截断的原六阶行）。** 固定原非零行权、允许标签 $j$ 与 $t_0$ 在其正支撑中。由同一固定 ray 类中的素理想定理，可选择不同 good 素理想 $\ell,p,r$，范数分别为 $\asymp P^7,\asymp P^2,\asymp P^2$，$P\to\infty$。令

$$
v=\ell p^2r^4,\qquad U=s_jq_v/t_0\asymp P^{19}.
\tag{470.10}
$$

原权仍为 $\Omega(t_0)>0$。其 $R_1=\ell,R_2=p,R_4=r,R_3=R_5=1$，故（470.1）三项分别为 $\asymp P^{13},\asymp P^{18},\asymp P^{55/3}$。因此对充分大 $P$，

$$
\mathscr H_{24}(v)\le U^{37/38}.
\tag{470.11}
$$

另一方面，原奇偶核、模三核及（469.2）的读数为

$$
q_{a_2}\asymp P^7>U^{1/3},\qquad
q_{a_3}\asymp P^{13}>U^{2/5},\qquad
\mathscr H_3(v)\asymp P^{22}>C_0U
\tag{470.12}
$$

对每个固定 $C_0$ 和充分大 $P$ 都成立。原估值 $1,2,4$ 使 $S$ 外字符阶数恰为六。这只给出原允许行中的实例，不断言零点检测器选择了这些行，也不提供能量的正下界。式（470.2）因而确实消费了第 467—469 节各截断之外的完整原行能量。

新的消费是共同保留 $R_2R_4^2$ 并对全部此类原行积分后的联合区域；三次筛、函数方程、列立方提取和通常理想计数本身均直接复用。充分大的原平方自由行仍有 $\mathscr H_{24}\asymp U^2$，不在此预算中。其他长度与高度、F4 的新运输、完整六阶余域和 signed Robin restoration 仍需独立估计；本节没有证明 RH 或逐整数严格 Robin 不等式，没有本仓解析 Lean 认证或文献优先权断言。

## 追加锚（本行以下为增补区）

## 471. 完整反射后的原始一估值行预算

**定理 471.1（平方自由一估值方向的完整原因子预算）。** 保持第 468—470 节的同一个完整原卷积、非负有界行权、固定有限物理/ray/Fourier 表示、原零延拓及平衡尺度 $D=N=\sqrt U$、$K=U$。直接复用[六阶大筛及其原族接口](../../../Library/Analytic/faveri2026fixedorder.md#the-large-sieve-statement)、该接口的完整列六次幂提取，以及第 468 节的实际 primitive 导子、完整 normalized plain 反射、有限 Euler 质量和 annular/supremum 恢复。令 $\mathcal C_1$ 包络所用解析输入、profiles 所需有限阶导数、全部原有限分量及 smooth/Sobolev 恢复的实际乘积费用。Norm-twist 高度仍限于原固定或相应次幂费用的 polylog 合同。

在（469.1）的同一实际物理分解中记 $x_i=q_{R_i}$，定义

$$
\begin{aligned}
a(v)&=x_1,\qquad g_1(v)=x_2x_3x_4x_5,\\
c_1(v)&=x_2^2x_3^3x_4^4x_5^5,\qquad f(v)=a(v)g_1(v),\\
\mathscr H_1(v)
&=g_1(v)\{a(v)+f(v)+a(v)^{5/6}f(v)^{1/3}
                         +a(v)^{1/3}f(v)^{5/6}\}\\
&=f(v)+a(v)g_1(v)^2
 +a(v)^{7/6}g_1(v)^{4/3}+a(v)^{7/6}g_1(v)^{11/6}.
\end{aligned}
\tag{471.1}
$$

这里 $q_v=a(v)c_1(v)\asymp U$。对固定 $C_0\ge1$、$1\le T\le C_0U$，令 $Q^{\langle1\rangle}_{\le T}(b)$ 为同一个完整原正能量在 $\mathscr H_1(v)\le T$ 上的限制，包括全部原有限物理标签。在所列解析输入及共同费用条件下，对每个 $\varepsilon>0$，

$$
Q^{\langle1\rangle}_{\le T}(b)
\ll_{\varepsilon,C_0}\mathcal C_1^2U^{1+\varepsilon}T.
\tag{471.2}
$$

因此 $T=U^{1-\nu}$、$0\le\nu\le1$ 给出 $O_\varepsilon(\mathcal C_1^2U^{2-\nu+\varepsilon})$；严格幂次节省须固定 $\nu>0$、共同费用次幂且最终损失足够小。此式不允许先给原系数增加任意列乘子，也不对孤立 F4 包宣称相同反射估计。

证明。固定原物理标签、一个 Fourier 分量 $\xi$ 及五个 norm 的 dyadic 块，记

$$
A\asymp x_1,\qquad G\asymp x_2x_3x_4x_5,
\qquad F=AG\asymp q_{\operatorname{rad}v}.
\tag{471.3}
$$

单位因子归入尺度一；实际非空 subunit annuli 按原固定 annular enlargement 处理。固定实际 $R_2,R_3,R_4,R_5$，只让原 squarefree $R_1$ 变化。先在原允许行上使用第 468 节的实际非主 primitive 导子 $F_v\asymp F$ 和（468.6）的完整 normalized plain 反射。固定每个反射项、annulus、恢复尺度及 profiles 后，（468.8）的同一个完整列多项式为

$$
\sum_h\beta_X(h)\psi_v^0(h),\qquad
\beta_X(h)=X^{-1/2}\sum_{dn=h}
 \mu(d)V(q_d/D)\widetilde W(q_n/Y),\qquad
X=DY\ll FU^{O(\xi_0)}.
\tag{471.4}
$$

这里整个反射 plain 因子在绝对乘积内共轭，原 Möbius 因子不变；root number 的模长为一。$\beta_X$ 与变化的 $R_1$ 无关。行依赖实际主尺度不是额外的行依赖系数，而由第 468 节同一有限阶尺度 supremum 恢复支付。有限 $S$ Euler 系数的绝对总质量、全部尾部、原 collision zeros 及所需导数均保留在共同合同中；只在原行上使用实际导子恒等式。

对每个固定项，字符连同零值恰好分解为

$$
\psi_v^0(h)=\xi(h)\chi_h^{\rm raw}(R_2^2R_3^3R_4^4R_5^5)
                         \chi_h^{\rm raw}(R_1).
\tag{471.5}
$$

前两个因子与 $R_1$ 无关，吸入列系数 $\gamma_X(h)$，模长至多一；不把它们的移动导子放入筛常数。负 orientation 先整体共轭。原族接口直接将最后一个字符识别为第 441 节六阶筛的同一族；不另作未付费用的 reciprocity 换向。

对完整列唯一写 $h=\ell^6h_0$，$h_0$ sixth-power-free，允许 $\ell,h_0$ 相交。复用原接口的精确零延拓和除数型质量界，得到

$$
\chi_{\ell^6h_0}^{\rm raw}(R_1)
 =\chi_{h_0}^{\rm raw}(R_1)\mathbf1_{(\ell,R_1)=1},
\qquad
\sum_{h_0\ {\rm sixth\ power\ free}}
 |\gamma_X(\ell^6h_0)|^2
 \ll_\delta\mathcal P^2X^\delta q_\ell^{-6}.
\tag{471.6}
$$

固定 $\ell$ 后，先保留行限制 $(\ell,R_1)=1$，再只在正范数中扩大 $R_1$ 的允许集，解除它与四个固定标签的互素条件。原 $R_1$ squarefree，因而 sixth-power-free，列 $h_0$ 也满足同一筛条件。此时才使用原族六阶筛

$$
\begin{aligned}
\Psi_6(A,X)&=A+X+A^{5/6}X^{1/3}+A^{1/3}X^{5/6},\\
\sum_{R_1}\left|\sum_{h_0}c_{h_0}\chi_{h_0}^{\rm raw}(R_1)\right|^2
&\ll_\delta(AX)^\delta\Psi_6(A,X)\sum_{h_0}|c_{h_0}|^2.
\end{aligned}
\tag{471.7}
$$

式（471.7）中行 $R_1$ 与列 $h_0$ 均按上述 sixth-power-free 条件取值，行 norm 尺度为 $A$、列 norm 至多为 $O(X)$；它是平方行范数界。列长为 $O(X/q_\ell^6)$，单调性允许用 $X$ 统一支配；Minkowski 的质量为 $q_\ell^{-3}$，其理想和收敛。若 $R_1=1$，单独用列 Cauchy 支付 $X$ 项，不把主字符误纳入非主字符函数方程。该原行的完整 $v$ 仍非单位，实际反射在此前已合法执行。由原归一化 $DN=U$，固定四个实际标签后的完整原能量至多

$$
\mathcal C_1^2U^{1+\delta}
 \{A+F+A^{5/6}F^{1/3}+A^{1/3}F^{5/6}\}.
\tag{471.8}
$$

先按最终损失选取 $\xi_0$，再吸收 $X\ll FU^{O(\xi_0)}$ 的扩大和内部小幂；反射、有限 Euler、profile 导数及原高度费用一起恢复，不能为不同因子另开高度预算。

四个固定理想的实际选择至多 $O(G)$；忽略其互素性只用于正计数。于是该块上界是（471.8）乘 $G$。若原块与 $\mathscr H_1\le T$ 相交，该乘积的括号费用为 $O(T)$，因为五个 dyadic norm 与同一实际行的（471.1）只差固定因子。只对这些块正求和，块数及原有限分量用最终小幂支付，得到（471.2）。所有原 $h=dn$、共同因子、不同分解和列间交叉项始终留在同一个完整范数中。证毕。

**推论 471.2（联合高估值所支付的一估值区域）。** 同一合同下，原允许行中满足

$$
x_1\le x_2x_3^7x_4^{13}x_5^{19}
\tag{471.9}
$$

的部分具有 $O_\varepsilon(\mathcal C_1^2U^{2+\varepsilon})$ 的完整原能量。

证明。记 $a=a(v)$、$g=g_1(v)$、$c=c_1(v)$。有 $c\ge g^2\ge g\ge1$，所以（471.1）的前两项均至多 $ac=q_v$，第三项不超过第四项。而

$$
\left(\frac{a^{7/6}g^{11/6}}{ac}\right)^6
 =\frac{ag^{11}}{c^6},\qquad
\frac{c^6}{g^{11}}=x_2x_3^7x_4^{13}x_5^{19}.
\tag{471.10}
$$

故（471.9）使 $\mathscr H_1(v)\le4q_v$。取固定 $C_0$ 支付原 annular/物理标签常数，再应用（471.2）。证毕。

**命题 471.3（全部既有物理截断之外的新原行）。** 保持原行权和允许有限标签 $j$。固定 $t_0$ 在 $\Omega$ 的正支撑中，在所需固定 ray 类中选取不同 good 素理想 $\ell,r$，范数为 $q_\ell\asymp P^5$、$q_r=P\to\infty$。同一 ray 类的素理想定理提供该选择，可避开固定 $S$。令

$$
v=\ell r^3,\qquad U=s_jq_v/t_0\asymp P^8.
\tag{471.11}
$$

原权仍为 $\Omega(t_0)>0$；此时 $R_1=\ell$、$R_3=r$，其他 $R_i=1$。（471.1）的四项分别为 $\asymp P^6,P^7,P^{43/6},P^{23/3}$，均严格小于 $U^{47/48}\asymp P^{47/6}$ 的幂次。因此充分大 $P$ 时

$$
\mathscr H_1(v)\le U^{47/48}.
\tag{471.12}
$$

但对每个固定 $C_0$，同一原行有

$$
q_{a_2}\asymp P^6>U^{1/3},\qquad
q_{a_3}\asymp P^5>U^{2/5},\qquad
\mathscr H_3(v)\asymp P^{11}>C_0U,\qquad
\mathscr H_{24}(v)\asymp P^{12}>C_0U.
\tag{471.13}
$$

故该完整原行族在第 467—470 节各已付截断之外。估值 $1,3$ 使 $S$ 外字符阶数恰为六；这里不声称检测器选择这些行，也不给出它们能量的正下界。

第 441 节已有的四个形式尺度恰为（471.1）乘 $a(v)$，重排后为 $f^2,af,a^{5/6}f^{4/3},a^{1/3}f^{11/6}$；它们及所用大筛、反射、六次幂提取不是新增结果。本节的消费是把实际导子上的完整反射、原列系数和四个固定实际标签的求和接合，支付（471.2）的原正能量区域。合并既有区域时须覆盖所有实际支路的共同费用，或保留其平方费用之和，交集只计一次。充分大的原平方自由行仍满足 $g_1=c_1=1$、$\mathscr H_1\asymp U^{7/6}$，未获 $U^2$ 体积预算。完整六阶余域、其他长度与高度、F4 的新运输及 signed Robin restoration 仍未解决；本节没有证明 RH 或逐整数严格 Robin 不等式，没有解析 Lean 认证或文献优先权断言。

## 追加锚（本行以下为增补区）

## 472. 实际逆／plain 长度比与原一估值行预算

**定理 472.1（原始长度耦合的完整一估值能量）。** 保持第 471 节的同一原物理行、原有限 Fourier／ray 分区、非负有界行权和完整 normalized Möbius／plain 因子。此处 $D$ 始终为 Möbius 长度，$N$ 始终为 plain 长度，$K=DN$。固定 $C>0$，允许 $1\le D,N\le U^C$，而不要求 $D=N$ 或 $K=U$。复用第 468 节实际 primitive 导子上的完整 normalized plain 反射、固定 $S$ Euler 质量、annular／尺度 supremum 恢复，以及[既有六阶大筛及其原族接口](../../../Library/Analytic/faveri2026fixedorder.md#the-large-sieve-statement)。原 norm-twist 高度固定，或满足这些实际有限阶恢复费用为次幂的同一 polylog 合同；不扩张原 growing-height allowance。

在（469.1）的同一实际互素平方自由分解中记

$$
\begin{aligned}
a(v)&=q_{R_1},& g(v)&=q_{R_2R_3R_4R_5},& f(v)&=a(v)g(v),\\
X_{D,N}(v)&=\max\{1,Df(v)/N\},\\
\mathscr H_{1;D,N}(v)
&=g(v)\{a(v)+X_{D,N}(v)
 +a(v)^{5/6}X_{D,N}(v)^{1/3}
 +a(v)^{1/3}X_{D,N}(v)^{5/6}\}.
\end{aligned}
\tag{472.1}
$$

令 $Q_{D,N;\le T}^{\langle1\rangle}(b)$ 为同一个完整原列向量在 $\mathscr H_{1;D,N}(v)\le T$ 的正行能量，仍包括全部实际 $h=dn$、共同因子、原零值、列间干涉及原有限物理标签。共同乘积包络 $\mathcal C_{472}$ 一次包含所用解析供应、有限 Fourier 重构、有限阶 profile 导数、完整 Euler 质量及 scale／Sobolev 恢复成本，不按行、估值块或长度选择重新配置。对固定 $C_0\ge1$、$1\le T\le C_0U$ 及每个最终 $\varepsilon>0$，在所列解析合同下有

$$
Q_{D,N;\le T}^{\langle1\rangle}(b)
\ll_{\varepsilon,C,C_0}
\mathcal C_{472}^2(UK)^\varepsilon KT.
\tag{472.2}
$$

因此同一原长度上的 $T=U^{1-\nu}$、固定 $0<\nu\le1$ 使该部分完整原能量为 $O(\mathcal C_{472}^2(UK)^\varepsilon KU^{1-\nu})$。幂次节省还要求共同费用次幂且最终损失小于该余量。原检测器返回的长度仍须满足其原限制，不能由（472.2）任意重选。

证明。固定实际原物理标签、Fourier 分量及五个 norm 的 dyadic 块，记 $A\asymp q_{R_1}$、$G\asymp q_{R_2R_3R_4R_5}$、$F=AG$。固定实际 $R_2,\ldots,R_5$，只让 $R_1$ 变化。先在这些原允许行上使用 $F_v\asymp F$ 的实际 primitive 导子和（468.6）的完整 normalized 反射。其 dual 主长度为 $F_v/N$，而不是 $F_v/D$。Normalized 形式中的 root number 模长为一，有限 $S$ Euler 系数仍有一致绝对总质量；不把 $D/N$ 或缩短尺度的平方根移入该质量。

直接使用第 468 节同一 annular 恢复。对预先固定的小 $\xi_0>0$，保留项的 dual 长度为 $Y\ll(F/N)U^{O(\xi_0)}$。若主尺度小于 $U^{-\xi_0}$，由反射 profile 在无穷处任意快衰减、原理想绝对计数及 $D,N\le U^C$，提高外部衰减阶数后，连同完整原乘积的总尾部可小于任意预定负幂。其余非空 subunit annuli 裁剪到一只增加 $U^{O(\xi_0)}$；故完整保留卷积长度满足

$$
X=DY\ll U^{O(\xi_0)}\max\{1,DF/N\}.
\tag{472.3}
$$

实际 $F_v$ 随 $R_1$ 变化的尺度仍用相同有限阶 profile 导数及对数数量的尺度盒恢复；每一个固定盒内的列系数与变化行无关。只在完整反射 plain 因子的绝对值内整体共轭，使其与原 Möbius 因子重新使用同一 $\psi_v^0$。于是固定项的完整 normalized 列恰为（471.4）的 $\beta_X$，此时保留真正的 $D,Y$，而原外因子始终是 $K=DN$，并未改成 $DY$。

复用（471.5）—（471.7）的原族分解和完整列六次幂提取。固定 $R_2,\ldots,R_5$ 后，剩余筛行仍为 squarefree $R_1$；列的 $h=\ell^6h_0$ 分解保留 $\mathbf1_{(\ell,R_1)=1}$，归一化列平方质量仍为 $O(X^\delta q_\ell^{-6})$。只在正行范数内扩大允许的 $R_1$，Minkowski 用同一收敛质量 $\sum_\ell q_\ell^{-3}$。固定四个实际标签后的完整原能量由

$$
\mathcal C_{472}^2(UK)^\delta K
 \Psi_6\bigl(A,\max\{1,DF/N\}\bigr),
\qquad
\Psi_6(A,X)=A+X+A^{5/6}X^{1/3}+A^{1/3}X^{5/6}
\tag{472.4}
$$

控制；$R_1=1$ 的单行用同一 $X$ 项支付，非主完整字符的反射已在扩大行集以前执行。有限标签的相位只作模长至多一的固定列 twist，不引入移动导子常数。

四个固定理想的实际选择至多 $O(G)$。相交于 $\mathscr H_{1;D,N}\le T$ 的 dyadic 块满足 $G\Psi_6(A,\max\{1,DF/N\})\ll T$，因为各 norm 与原实际行只差固定因子。对这些块正求和，先选择 $\xi_0$ 和内部损失以适配最终 $\varepsilon$，再恢复全部原有限分量与共同费用，得到（472.2）。这里只对同一原向量的实际行取正限制；没有给列添加任意乘子或对孤立 F4 包套用该反射。证毕。

**推论 472.2（允许的不平衡长度上的严格原行预算）。** 保持原非零行权及允许有限 ray 类。选 $t_0$ 在原 $\Omega$ 的正支撑内，在所需固定 ray 类中取不同 good 素理想 $\ell,r$，满足 $q_r=P\to\infty$、$q_\ell\asymp P^5$。该选择直接复用固定 ray 类素理想定理；不另证素数计数。令

$$
v=\ell r^5,\qquad U=s_jq_v/t_0\asymp P^{10},
\qquad D=U^{3/5},\quad N=U^{2/5},\quad K=U.
\tag{472.5}
$$

这是原长度限制 $r_{\rm length}\le t$、$r_{\rm length}+m\ge t$、$0\le m\le1/2$ 在 $t=1$ 下允许的 $(3/5,2/5)$；此处不声称检测器必选该长度或这些行。其实际 $a\asymp P^5$、$g=P$、$f\asymp P^6$、$X_{D,N}\asymp P^8$，所以（472.1）四项依次为

$$
P^6,\qquad P^9,\qquad P^{47/6},\qquad P^{28/3}.
\tag{472.6}
$$

因此这些实际原行最终满足 $\mathscr H_{1;D,N}\le U^{19/20}$，其所在（472.2）正截断具有 $O_\varepsilon(\mathcal C_{472}^2U^{39/20+\varepsilon})$ 的完整原能量。固定 dyadic 估值区域 $q_{R_1}\asymp U^{1/2}$、$q_{R_5}\asymp U^{1/10}$、$R_2=R_3=R_4=1$ 本身还满足 $\mathscr H_{1;D,N}\ll U^{14/15}$，故其完整能量为 $O_\varepsilon(\mathcal C_{472}^2U^{29/15+\varepsilon})$。

证明。代入（472.1）；最大幂次 $28/3$ 小于 $10\cdot19/20=19/2$。原物理权仍为 $\Omega(t_0)>0$，素估值 $1,5$ 使 $S$ 外实际阶数恰为六。Dyadic 区域的固定隐常数可放进 $T=C_1U^{14/15}$，充分大 $U$ 时仍在 $T\le C_0U$ 内；再用（472.2）。不从行权非零推断完整卷积响应非零，也不给出能量下界。证毕。

**命题 472.3（超出逐行 plain 预算的原不平衡扇区）。** 仍取同一原允许长度 $D=U^{3/5}$、$N=U^{2/5}$、$K=U$。在实际估值块

$$
q_{R_1}\asymp U^{6/11},\qquad q_{R_5}\asymp U^{1/11},
\qquad R_2=R_3=R_4=1
\tag{472.7}
$$

上，完整原能量满足

$$
Q_{D,N;(472.7)}(b)
\ll_\varepsilon\mathcal C_{472}^2U^{65/33+\varepsilon}.
\tag{472.8}
$$

该块包含任意大的原允许行 $v=\ell r^5$、$q_\ell\asymp P^6$、$q_r=P$、$U=s_jq_v/t_0\asymp P^{11}$。这些仍只表示原允许行和长度，未给出检测器选择或响应下界。

证明。固定 ray 类的素理想选择及原行权按推论 472.2 处理。此时 $A\asymp P^6$、$G=P$、$F\asymp P^7$、$X_{D,N}\asymp P^{46/5}$。实际（472.1）的四项为

$$
P^7,\qquad P^{51/5},\qquad P^{136/15},\qquad P^{32/3}.
\tag{472.9}
$$

最大幂次为 $32/3<11$。故整个（472.7）dyadic 区域有 $\mathscr H_{1;D,N}\ll U^{32/33}$，在（472.2）中取 $T=C_2U^{32/33}$ 并吸收最终损失，得到（472.8）。

为比较同一原长度和同一估值块上的分开估计，复用第 467 节的逐行反射 plain 上界与单 Möbius 因子的同一六阶筛。这里 $F/N\asymp P^{13/5}$，而 $\Psi_6(A,D)$ 的主项是 $A^{1/3}D^{5/6}\asymp P^{15/2}$，所以该指定分开预算为

$$
g\,\Psi_6(a,D)\frac fN\asymp P^{111/10}
\asymp U^{111/110}>U.
\tag{472.10}
$$

完整反射的行预算则为 $O(U^{32/33})$。因此所列分开估计未支付的该长度与行的联合区域，已由（472.8）控制。这仅比较两份具体上界预算，不是原能量下界，也不排除其他估计方法。证毕。

这份消费保留了原实际 $(D,N)$。第 471 节的 $D=N=\sqrt U$ 陈述不能用于（472.5）；平衡时（472.1）则恰好回到（471.1）。作为推论 472.2 的扇区上的预算比较，若只以单 Möbius 因子的大筛乘逐行反射 plain 上界，则 $g\Psi_6(a,D)\,f/N$ 的主项为 $P^{29/3}$，而（472.6）的完整反射给出 $P^{28/3}$。这些是上界预算的比较，不是实际能量的下界。六阶大筛、反射公式、六次幂提取及 norm 论证本身都是既有工具；本节仅为 `repo-derived` 的原系数非平衡长度应用，不声明新筛或文献优先权。

充分大的平方自由物理行仍有 $a=f\asymp U$、$g=1$；在原允许 $D/N\ge1$ 的上述长度上并未获得 $KU$ 体积预算。完整六阶余域、其他未付长度／高度、F4 的新运输及逐整数 signed Robin restoration 仍需独立估计。本节没有证明 RH 或全部 $n>5040$ 的严格 Robin 不等式，也没有解析 Lean 认证。

## 追加锚（本行以下为增补区）

## 473. 对全部 F4 掩码与投影稳定的物理行切面

**定理 473.1（原 F4 完整正和的稳定行预算）。** 沿用第 472 节的原物理行分解、实际 primitive 导子、完整 normalized Möbius／plain 反射、有限 Fourier／ray 数据、零延拓和同一解析费用合同，以及 [F1–F4](../../../Library/Analytic/faveri2026fixedorder.md#a-weighted-powerful-part-majorant-for-all-original-columns) 的实际原系数分解。原长度满足 $1\le D,N\le U^C$，$K=DN$；$D$ 始终是原 Möbius 长度。令

$$
\begin{aligned}
a(v)&=q_{R_1},&g(v)&=q_{R_2R_3R_4R_5},&f(v)&=a(v)g(v),\\
\mathscr H^{\rm sf}_1(v;D)&=g(v)\Psi_6(a(v),Df(v)),\\
\mathcal R_T&=\{v:\mathscr H^{\rm sf}_1(v;D)\le T\},
&1\le T&\le C_0U.
\end{aligned}
\tag{473.1}
$$

这里 $\Psi_6$ 是（472.4）的同一四项筛预算。对每个实际 $c$、$a_{\rm col}\mid\operatorname{rad}c$、$b=c/a_{\rm col}$，记 $D_a=D/q_{a_{\rm col}}$、$N_b=N/q_b$、$X=K/q_c=D_aN_b$。令 $\widetilde T^{\rm sf}_{j;c,a_{\rm col},\kappa;\mathcal R_T}$ 为 F4 的同一个完整包能量，仅将原非负行权乘以 $\mathbf1_{\mathcal R_T}$。特别地，保留 $x$ 平方自由、$(x,c)=1$、原有限类、全部零值和包内交叉项。定义完整正和

$$
M^{F4}_{\mathcal R_T}
=Z_s|\mathcal T|
\sum_{\substack{c\ {\rm powerful}\\q_c\le CK}}
q_c^s\tau(\operatorname{rad}c)
\sum_{a_{\rm col}\mid\operatorname{rad}c}\sum_{\kappa\in\mathcal T}
\widetilde T^{\rm sf}_{j;c,a_{\rm col},\kappa;\mathcal R_T}.
\tag{473.2}
$$

对每个最终 $\varepsilon>0$，按 F4 选择 $s=1/2+\eta$ 并分配内部损失。在所引解析合同下，同一共同包络 $\mathcal C\ge1$ 给出

$$
\begin{aligned}
\widetilde T^{\rm sf}_{j;c,a_{\rm col},\kappa;\mathcal R_T}
&\ll_{\varepsilon,C,C_0}\mathcal C^2(UK)^\varepsilon TX,\\
M^{F4}_{\mathcal R_T}
&\ll_{\varepsilon,C,C_0}\mathcal C^2(UK)^\varepsilon KT.
\end{aligned}
\tag{473.3}
$$

$\mathcal C$ 一次包含第 472 节的全部解析、完整 Euler、profile、尺度与 Sobolev 成本，以及第 464 节实际有限类恢复所需的费用，不按 $c,a_{\rm col}$、投影除子或物理行重新配置。高度仍固定，或满足原共同费用为次幂的 polylog 合同；没有扩张 growing-height allowance。结论覆盖（473.2）的全部实际包，包括 $c=a_{\rm col}=1$，不要求 $D_a\le U^{1/3}$ 或 $N_b$ 满足第 465 节的短长度条件。

证明。关键是让第 472 节的完整乘积估计对所有实际展开项使用同一物理行集，而不把它直接套到投影系数上。记 $B(D',N';v)$ 为（464.5）的未掩码原乘积。若一个展开项非空，则紧 annular 支撑使 $D',N'$ 均有固定正下界；低于一的长度按第 464 节的固定 annular enlargement 归入一，并运输 profiles。只要 $D'\ll D$，就有

$$
\max\{1,D'f(v)/N'\}\ll Df(v),\qquad
\mathscr H_{1;D',N'}(v)\ll\mathscr H^{\rm sf}_1(v;D).
\tag{473.4}
$$

使用 $D,f\ge1$ 和 $\Psi_6$ 的逐项单调性即可；enlargement 只改变固定常数及一致有界的有限 seminorms。每个非空项的长度仍在原固定幂范围内。因此（472.2）对同一个 $\mathcal R_T$ 给出原始未归一化范数界

$$
\|\sqrt{\Omega\mathbf1_{\mathcal R_T}}\,B(D',N')\|_2
\ll\mathcal C(UK)^\delta\sqrt{TD'N'}.
\tag{473.5}
$$

这里将 $T$ 乘固定常数，只是使用（472.2）中另一个固定 $C_0$。原始范数的外因子是 $D'N'$，不是反射后的卷积长度；annular tails、subunit clipping 和实际导子尺度恢复全部复用第 472 节的合同。对行集的进一步零限制可在此正范数内保留或扩大。

下面直接消费（464.9）—（464.12）的精确恒等式。对零掩码 $A,B$ 的每个非空 Euler 展开项，未掩码长度为 $D_0/q_m,N_0/q_e$，故逆长度不超过 $D_0$，乘积长度为 $D_0N_0/(q_mq_e)$。先在同一正行范数内处理 $\psi_v(me)$，再用（473.5）和同一 Euler 乘积质量，得到

$$
\begin{aligned}
\|\sqrt{\Omega\mathbf1_{\mathcal R_T}}\,B_{A,B}(D_0,N_0)\|_2
&\ll\mathcal C(UK)^\delta\sqrt{TD_0N_0}
\prod_{p\mid A}(1-q_p^{-1/2})^{-1}
\prod_{p\mid B}(1+q_p^{-1/2})\\
&\ll_\theta\mathcal C(UK)^\delta(q_Aq_B)^\theta\sqrt{TD_0N_0},
\qquad D_0\ll D.
\end{aligned}
\tag{473.6}
$$

该步骤没有在绝对 $L$ 值中删除因子，也没有把移动掩码改成固定 conductor 常数。

对实际平方自由 F3 包 $P_c$，（464.12）中的项具有

$$
D_0=D_a/q_g\le D,\qquad
N_0=N_bq_g/q_r^2,\qquad
D_0N_0=X/q_r^2,
\qquad g\mid r,\quad q_r\ll\sqrt X.
\tag{473.7}
$$

由于 $q_g\le q_r$，亦有 $N_0\le N_b\le N$。式（473.4）同时覆盖这些项和其后的全部 Euler 缩短项；不要求保持 $D_0/N_0\le D/N$。在（473.6）中取 $A=cr,B=c$，复用第 464 节的 Minkowski 与除数质量，得到

$$
\begin{aligned}
\|\sqrt{\Omega\mathbf1_{\mathcal R_T}}\,P_c\|_2
&\ll\mathcal C(UK)^\delta q_c^{2\theta}\sqrt{TX}
\sum_{q_r\ll\sqrt X}\tau(r)q_r^{-1+\theta}\\
&\ll_\theta\mathcal C(UK)^\delta q_c^{2\theta}X^\theta\sqrt{TX}.
\end{aligned}
\tag{473.8}
$$

有限 Fourier 类在 $h=r^2d'n'$ 下按原规则运输；所需有限次导数的固定阶对数损失纳入同一小幂。包内原有零值未被删去，所有交叉项由 Minkowski 控制，不声称不同展开项正交。选择 $\delta,\theta$ 再平方，便得（473.3）的第一式。

F4 的加权 Cauchy 在取平方范数以前即可使用行权 $\Omega\mathbf1_{\mathcal R_T}$，所以（473.2）仍是同一个原行限制的正 majorant。把（473.3）第一式代入，复用（464.14）及同一有限类数，数值总和为

$$
TK\sum_{\substack{c\ {\rm powerful}\\q_c\le CK}}
\tau(c)^2q_c^{-1/2+\eta}
\ll_{\eta,\delta'}TK^{1+\eta+\delta'}.
\tag{473.9}
$$

按一个最终 $\varepsilon$ 分配所有内部损失，得到第二式。这里直接估计整份正和，没有从原未投影能量的上界反推其各个正展开包。证毕。

**命题 473.2（含原长 unit-core 包的严格行扇区）。** 在原允许的平衡长度 $D=N=\sqrt U$、$K=U$ 上，考虑实际物理行扇区

$$
q_{R_1}\asymp U^{1/11},\qquad q_{R_5}\asymp U^{2/11},
\qquad R_2=R_3=R_4=1.
\tag{473.10}
$$

将（473.2）中的全部包均限制到该行扇区，则在定理 473.1 的解析合同下，其完整正和满足

$$
M^{F4}_{(473.10)}
\ll_\varepsilon\mathcal C^2U^{43/22+\varepsilon}.
\tag{473.11}
$$

共同费用次幂且最终损失小于 $1/22$ 时，该预算严格小于 $U^2$ 的幂次规模。这里约束的是物理行，未缩短或重选原列见证。

证明。复用固定 ray 类中的素理想定理，在所需允许类取不同 good 素理想 $\ell,r$，使 $q_\ell=P\to\infty$、$q_r\asymp P^2$。选 $t_0$ 在原 $\Omega$ 的正支撑内，并令 $v=\ell r^5$、$U=s_jq_v/t_0\asymp P^{11}$。实际估值为一、五，故 $S$ 外字符阶数恰为六，且原物理行权非零。此时

$$
a\asymp P,\qquad g\asymp P^2,\qquad f\asymp P^3,
\qquad Df\asymp P^{17/2}.
$$

式（473.1）的四项依次为

$$
P^3,\qquad P^{21/2},\qquad P^{17/3},\qquad P^{113/12}.
\tag{473.12}
$$

所以整个（473.10）区域有 $\mathscr H^{\rm sf}_1\ll U^{21/22}$。取 $T=C_1U^{21/22}$ 并使用（473.3），得到（473.11）。对充分大 $U$，该 $T$ 仍在原允许区间内。

这份正和包括 $c=a_{\rm col}=1$、$D_a=N_b=\sqrt U$、$X=U>\sqrt U$ 的原长包。它不满足第 464 节 $D_a\ll U^{1/3}$ 的条件，也不满足第 465 节任意固定 $k\ge3$ 的 $N_b\ll U^{1/(2k)}$ 条件；物理行 $v=\ell r^5$ 亦非纯平方或纯立方行。原允许系数族确有这样的非零 unit-core 包：在运输后的允许有限列类中，用同一固定 ray 类素理想定理选两个不同 good 素理想 $d',n'$，范数在 $\sqrt U$ 的固定小相对区间内，避开 $\ell rS$，并令原非负 annular profiles 在两处为正。对平方自由 $x=d'n'$，逆 annulus 内只有这两个单素因子，二者的 Möbius 值均为 $-1$，故实际 F3 系数非零。该论证只说明允许的原系数包非空，不推出实际行响应非零或检测器必选这些行与 profiles。

作为具体预算比较，同一 unit-core 包若仅使用固定 $R_5$ 后的直接六阶筛，则 $g\Psi_6(a,K)\asymp P^{13}>P^{11}\asymp U$。这份指定直接预算没有支付（473.10）的整份正和，而（473.11）支付了它；该比较不是能量下界，也不排除其他估计。证毕。

第 472 节已经估计过这些行的未投影原乘积；（473.3）增加的是对全部实际掩码、平方自由投影和 F4 正权求和均稳定的接口。反射公式、六阶大筛、Euler 恒等式、投影和 powerful-core 质量均按所引来源复用，本节是 `repo-derived` 的完整正和应用，不主张新筛或文献优先权。

对大平方自由物理行 $a=f\asymp U$、$g=1$，即使 $D=\sqrt U$，本节的稳定行预算仍有主项 $U^{19/12}>U$。因此（473.11）没有支付完整六阶余域。其余原长度／高度、全物理行估计及逐整数 signed Robin restoration 仍需独立处理；没有由此得到 RH 或全部 $n>5040$ 的严格 Robin 不等式，也没有解析 Lean 认证。

## 追加锚（本行以下为增补区）

## 474. 标准 Xi 导数滤波的完整 gamma 振幅运输

**定义 474.1（完成函数的归一化滤波平均）。** 取标准完成函数 $\Xi(t)=\xi(1/2+it)$ 及 Hardy 实函数 $Z(t)$，并令

$$
A(t)=\frac12\left(t^2+\frac14\right)\pi^{-1/4}
 \left|\Gamma\left(\frac14+\frac{it}{2}\right)\right|>0,
\qquad \Xi(t)=-A(t)Z(t),\quad t\in\mathbb R.
\tag{474.1}
$$

对标准普通导数 $\mathsf D=d/dt$，沿用经典广义 Laguerre 形式

$$
\mathcal L_p[f](t)=\sum_{j=0}^{2p}
 \frac{(-1)^{j+p}}{j!(2p-j)!}f^{(j)}(t)f^{(2p-j)}(t).
\tag{474.2}
$$

固定非负非零 $w\in C_c^\infty((0,1))$，记 $L=\log T$、$w_{X,H}(t)=w((t-X)/H)$。对实多项式 $P$ 定义

$$
\begin{aligned}
J_Z(P)&=\int_{\mathbb R}w_{X,H}(t)
 \mathcal L_p[Z](t)[P(\mathsf D/L)Z(t)]^2\,dt,\\
J_\Xi(P)&=\int_{\mathbb R}w_{X,H}(t)A(t)^{-4}
 \mathcal L_p[\Xi](t)[P(\mathsf D/L)\Xi(t)]^2\,dt.
\end{aligned}
\tag{474.3}
$$

这里 $\mathcal L_p$ 与 $P(\mathsf D/L)$ 均使用 $\Xi$ 的普通导数；没有以 $\mathsf D-A'/A$ 取代它们。因子 $A(t)^{-4}$ 是指定平均的一部分，不能省略。

**定理 474.2（全部系数方向上的完成振幅消费）。** 以下以 bramble_trace 的 [*Signs and uniform filtered positivity in fourth moments of Hardy's function*，v3，Theorems 9–10 及（29）—（50）](https://rstation.ai/api/v1/papers/riemann_hypothesis_36/versions/3/download)的解析估计为前提，直接复用其中的四移位矩、正核强制性和完整算术余项界。固定 $0<\delta<1/13$、$0<\varepsilon<1/4$ 及上述 $w$。令

$$
X\in[T,2T],\qquad T^{12/13+\delta}\le H\le T,
\qquad Q(x)=P\left(x-\frac{\pi}{4L}\right).
\tag{474.4}
$$

在下列任一范围内，对每个非零实多项式 $P$，当 $T$ 足够大时一致有

$$
J_\Xi(P)=(1+o(1))J_Z(Q)>0:
\quad
\begin{cases}
p\ge1\text{ 固定},& \deg P\le L^{1/4-\varepsilon},\\
p\ge1,&p+\deg P\le(1/4-\varepsilon)\log\log T.
\end{cases}
\tag{474.5}
$$

第一种范围的阈值允许依赖 $p$；第二种范围的阈值不按 $p$ 重选。两种范围均一致于 $X,H$ 及所有非零系数方向，允许系数随 $T$ 改变。该结果是 `repo-derived` 的标准完成函数应用；所引 Hardy 正性、经典 Laguerre 判据及 Stirling 估计本身均为已有输入。

证明。对 $t$ 位于原窗口支撑及 $|z-t|\le1$，将 $A$ 局部全纯延拓为

$$
A(z)=\frac12\left(z^2+\frac14\right)\pi^{-1/4}
 \left\{\Gamma\left(\frac14+\frac{iz}{2}\right)
        \Gamma\left(\frac14-\frac{iz}{2}\right)\right\}^{1/2},
\tag{474.6}
$$

取在实轴上为正的平方根分支。对充分大 $T$，这份局部支撑中没有 gamma 极点或多项式零点，故分支存在并满足（474.1）的解析延拓。经典解析 Stirling 给出 $A'/A=-\pi/4+O(T^{-1})$，并因而在固定 $|b|\le2$ 上一致有

$$
\frac{A(t+b/L)}{A(t)}
=e^{-\pi b/(4L)}\left\{1+O\left((TL)^{-1}\right)\right\}.
\tag{474.7}
$$

先在完整四移位乘积内使用此式。定义

$$
\begin{aligned}
F_Z(\mathbf b)&=\int w_{X,H}(t)\prod_{j=1}^4 Z(t+b_j/L)\,dt,\\
F_\Xi(\mathbf b)&=\int w_{X,H}(t)A(t)^{-4}
                      \prod_{j=1}^4\Xi(t+b_j/L)\,dt.
\end{aligned}
\tag{474.8}
$$

分母始终是未移位的 $A(t)^4$；对 $b_j$ 求导不会作用到分母，所以它保留了标准 $\Xi$ 导数。不能把该分母改成四个移位振幅而将结论变成形式恒等式。

复用原四移位矩的共轭匹配情形及 Hölder：在该固定微观复移位域内，$\int w_{X,H}|Z(t+b/L)|^4\ll_w HL^4+E$，其中

$$
E\ll_{w,\sigma}T^{3/4+\sigma}(T/H)^{9/4},
\qquad 0<\sigma<13\delta/4.
$$

该域与原文的固定移位域仅差坐标乘以 $i$，不扩张其半径。因此（474.7）给出全纯差额

$$
\begin{aligned}
F_\Xi(\mathbf b)
&=e^{\beta\sum_j b_j}F_Z(\mathbf b)+R_\Gamma(\mathbf b),
&\beta&=-\frac{\pi}{4L},\\
\sup_{|b_j|\le2}|R_\Gamma(\mathbf b)|
&\ll_w\frac{HL^4+E}{TL}.
\end{aligned}
\tag{474.9}
$$

这里不把快速增长的 $A^{-4}$ 当作原矩定理允许的缓变行权；约去振幅之后才对原 $Z$ 乘积使用四矩。

写 $P(x)=\sum_{r=0}^d c_rx^r$。使用普通导数的四槽泛函

$$
\mathscr D_{p,P}=
\frac{(-1)^p}{(2p)!}(\partial_{b_1}-\partial_{b_2})^{2p}
 P(\partial_{b_3})P(\partial_{b_4})\big|_{\mathbf b=0}.
\tag{474.10}
$$

它作用在（474.8）上分别得到 $L^{-2p}J_Z(P)$ 与 $L^{-2p}J_\Xi(P)$。第一对槽的差导数消去共同指数，第三、四槽则准确地将 $P$ 替成 $Q=P(\cdot+\beta)$。故

$$
J_\Xi(P)-J_Z(Q)=L^{2p}\mathscr D_{p,P}R_\Gamma.
\tag{474.11}
$$

在单位圆上作 Cauchy 估计，第一对槽的两个阶乘与（474.2）的分母抵消，留下 $2p+1$ 项；两份滤波各至多支付 $d!$。于是

$$
|J_\Xi(P)-J_Z(Q)|
\ll_w L^{2p}(2p+1)(d!)^2\|c\|_1^2\frac{HL^4+E}{TL}.
\tag{474.12}
$$

还须与同一系数方向的正主项比较，不能仅使用一个不定量的正性结论。复用所引论文（30）—（34）的核下界，记

$$
C=2+\sqrt5,\qquad
\kappa_p=\frac{6(1/2-1/\pi)}{\pi^2 4^p(2p)!}.
$$

对 $Q(x)=\sum q_rx^r$，其（45）、（47）在固定阶数范围及（49）—（50）在联合范围中，连同原算术位移

$$
\rho=\frac{\log(t/(2\pi))+2\kappa}{L}=1+O(L^{-1}),
\qquad \kappa=2\gamma-\frac{\zeta'(2)}{\zeta(2)},
$$

给出同一实际平均的下界

$$
J_Z(Q)\ge c_w HL^{2p+4}
\frac{\kappa_p e^{-C_1(p+d+1)/L}}
 {(d+2)^6 C^{2d}}\,\|q\|_1^2,
\tag{474.13}
$$

其中 $c_w>0$、$C_1$ 与系数方向无关。这里分别使用对应范围的原统一误差，未把固定 $p$ 常数用于增长 $p$。平移多项式及其逆平移给出
$\|c\|_1\le e^{|\beta|d}\|q\|_1$，所以（474.12）相对（474.13）至多为

$$
\frac{C_w(2p+1)(d!)^2(d+2)^6 C^{2d}}
 {\kappa_p TL}\,
 e^{C_2(p+d+1)/L}\left(1+\frac E{HL^4}\right).
\tag{474.14}
$$

窗口下界和 $\sigma<13\delta/4$ 使 $E/(HL^4)=o(1)$。其余分子的对数为 $O((p+d+1)\log(p+d+2))=o(\log T)$，在（474.5）的两种范围均成立。因此（474.14）一致趋于零，结合（474.13）即得结论。证毕。

式（474.5）控制的是带指定正振幅权的长窗口平均。它没有给出无 $A^{-4}$ 权的平均、个别高度的 Laguerre 符号，或允许滤波器在任意指定高度集中之定理。尤其不能在固定 $t$ 上令 $p$ 无限制增长：阈值及原窗口条件仍须同时满足。经典 Laguerre–Pólya／RH 判据所需的逐点、全阶条件没有由此获得；全整数 Robin 恢复也未建立。这里没有独立验证所引外部论文的完整证明，没有本仓解析 Lean 认证或文献优先权结论。

## 追加锚（本行以下为增补区）

## 475. 标准 Xi 线性导数观察器的分辨率下界

**定义 475.1（实际观察器的归一化质量）。** 沿用第 474 节的 $A,\Xi,Z,L=\log T$、固定非负非零 $w\in C_c^\infty((0,1))$ 及 $w_{X,H}(t)=w((t-X)/H)$。对非零实多项式 $P(x)=\sum_{r=0}^dc_rx^r$，定义

$$
Y_P(t)=A(t)^{-1}P(\mathsf D/L)\Xi(t),\qquad
N_P=\int_{\mathbb R}w_{X,H}(t)Y_P(t)^2\,dt.
\tag{475.1}
$$

在 $N_P>0$ 时，对可测集 $E\subset\mathbb R$ 记

$$
\mu_P(E)=N_P^{-1}\int_Ew_{X,H}(t)Y_P(t)^2\,dt.
\tag{475.2}
$$

它是第 474 节平均中实际出现的观察器质量：令 $F_p(t)=A(t)^{-2}\mathcal L_p[\Xi](t)$，则 $J_\Xi(P)=N_P\int F_p\,d\mu_P$。导数仍是 $\Xi$ 的普通导数，未用协变导数替换。

**定理 475.2（全部系数方向上的非集中界）。** 以第 474 节所引 bramble_trace v3 的定量四移位矩、正核强制性及完整余项估计为前提。固定 $0<\varepsilon_0<1/4$、$0<\delta<1/13$ 及上述 $w$。对每个 $\eta>0$，充分大 $T$ 上，一致于

$$
T\le X\le2T,\qquad T^{12/13+\delta}\le H\le T,
\qquad 0\le d\le L^{1/4-\varepsilon_0}
\tag{475.3}
$$

及所有非零实系数方向，均有 $N_P>0$，并对每个有限 Lebesgue 测度的可测集 $E$ 成立

$$
\boxed{
\mu_P(E)\ll_{\eta,\varepsilon_0,\delta,w}
\frac{|E|\,T^{13/21+\eta}}{HL^4}.
}
\tag{475.4}
$$

系数可随 $T,X,H$ 改变。常数不依赖 $P$ 或 $E$。相同结论也适用于将 $Y_P^2$ 换成任意非零有限正组合 $\sum_j a_jY_{P_j}^2$ 后的归一化质量，其中 $a_j\ge0$，每份 $P_j$ 满足同一次数限制；组合的项数与系数亦可改变。

证明。使用已有的 [Bourgain，*Decoupling, exponential sums and the Riemann zeta function*，arXiv:1408.5794v2，Theorem 5 及 §4](https://arxiv.org/abs/1408.5794v2) 的临界线估计 $|\zeta(1/2+it)|\ll_\nu t^{13/84+\nu}$。这份估计不是本节的新内容。标准函数方程、条带 Phragmén–Lindelöf 及 Hardy 相位的解析 Stirling，将它用于固定微观邻域后给出：对每个 $\nu>0$，

$$
\sup_{\substack{t\in[T,3T]\\|b|\le1}}
 |Z(t+b/L)|\ll_\nu T^{\theta+\nu},
\qquad \theta=13/84.
\tag{475.5}
$$

这里 $Z$ 取第 474 节所用的局部全纯延拓。条带插值在临界线右侧不增加幂次；左侧由函数方程至多增加 $T^{O(1/L)}=O(1)$，Hardy 相位在该微观圆盘上的模也有统一常数界。故没有将实轴估计未经接口直接用作复移位估计。

先控制同一实际观察器的分母。记 $Q(x)=P(x-\pi/(4L))$ 及 $C=2+\sqrt5$。所引来源 Theorem 9 允许 $p=0$；其（30）—（34）、（45）、（47）连同实际伸缩 $\rho=(\log(t/(2\pi))+2\kappa)/L=1+O(L^{-1})$，$\kappa=2\gamma-\zeta'(2)/\zeta(2)$，给出

$$
\int w_{X,H}Z^2[Q(\mathsf D/L)Z]^2
\ge c_w\frac{HL^4e^{-C_1(d+1)/L}}
 {(d+2)^6C^{2d}}\|q\|_1^2.
\tag{475.6}
$$

复用（474.9）的完整四移位振幅恒等式，只在第三、四槽施加 $P(\partial_{b_3})P(\partial_{b_4})$。第一、二槽不求导；其实际左边恰为

$$
M_P=\int w_{X,H}A^{-4}\Xi^2[P(\mathsf D/L)\Xi]^2
   =\int w_{X,H}Z^2Y_P^2.
\tag{475.7}
$$

对应误差至多

$$
\left|M_P-\int w_{X,H}Z^2[Q(\mathsf D/L)Z]^2\right|
\ll_w(d!)^2\|c\|_1^2\frac{HL^4+E_T}{TL},
\quad
E_T\ll_{w,\sigma}T^{3/4+\sigma}(T/H)^{9/4},
\quad 0<\sigma<13\delta/4.
\tag{475.8}
$$

这复用的是（474.9）的四槽估计及其 Cauchy 计算，未把只陈述于 $p\ge1$ 的（474.5）应用到范围之外。逆多项式平移给出 $\|q\|_1\ge e^{-\pi d/(4L)}\|c\|_1$。因此（475.8）相对（475.6）为 $o(1)$，一致于全部系数方向：其阶乘与系数损失的对数是 $O(d\log(d+2))=o(L)$，而余项有既定幂次节省。于是

$$
M_P\ge c_0\frac{HL^4e^{-C_2(d+1)/L}}
 {(d+2)^6C^{2d}}\|c\|_1^2>0.
\tag{475.9}
$$

由（475.5），$M_P\le\sup_{[T,3T]}|Z|^2N_P\ll_\nu T^{2\theta+2\nu}N_P$；这既证明 $N_P>0$，又支付了分母的统一下界。另一方面，在同一微观圆盘上，（474.7）给出 $|A(t+b/L)/A(t)|\ll1$。Cauchy 因而给出

$$
\sup_{t\in\operatorname{supp}w_{X,H}}|Y_P(t)|
\ll_\nu d!\|c\|_1T^{\theta+\nu}.
\tag{475.10}
$$

分子至多为 $\|w\|_\infty|E|$ 乘此上界的平方。与（475.9）及分母下界相除，得到

$$
\mu_P(E)\ll_{\nu,w}
\frac{|E|T^{4\theta+4\nu}}{HL^4}
 (d!)^2(d+2)^6C^{2d}e^{C_2(d+1)/L}.
\tag{475.11}
$$

最后一串因子在（475.3）中为 $T^{o(1)}$，且 $4\theta=13/21$。先取 $\nu=\eta/8$，再将该损失界为 $T^{\eta/2}$，即得（475.4）。有限正组合归一化后是各 $\mu_{P_j}$ 的凸组合，其权重正比于 $a_jN_{P_j}$，故同一个统一界仍成立。证毕。

**推论 475.3（原高度坐标上的实际分辨率限制）。** 在定理 475.2 的前提与范围内，若区间 $I$ 满足 $\mu_P(I)\ge c>0$，则

$$
|I|\gg_{c,\eta,\varepsilon_0,\delta,w}
 HL^4T^{-13/21-\eta}
 \ge L^4T^{83/273+\delta-\eta}.
\tag{475.12}
$$

特别地，对所有长度至多 $1/L$ 的区间及全部允许观察器，一致有

$$
\mu_P(I)\ll_{\eta,\varepsilon_0,\delta,w}
\frac{T^{-83/273-\delta+\eta}}{L^5}=o(1),
\qquad 0<\eta<83/273+\delta.
\tag{475.13}
$$

同样适用于定理中的有限正组合。

证明。重排（475.4），并用 $12/13-13/21=83/273$，即得两式。证毕。

该结果是 `repo-derived` 的指定观察器分辨率应用；Bourgain 的次凸界、经典 Cauchy 估计、源论文的正核与四矩及第 474 节的振幅运输均直接复用，不主张新的次凸估计、一般不确定性原理或文献优先权。它将“尚无集中定理”细化成了当前固定窗形和次数预算下的定量障碍：任意单个允许线性滤波器及其有限正组合，都不能将归一化观察质量集中到原高度坐标上的微观区间。该界没有排除改变窗长、次数预算或观察器类别后的集中，也没有断言所有平均正性论证都必须通过近似点质量恢复逐点符号。它仍以所引来源的解析估计为前提；逐点全阶 Laguerre 条件与逐整数 Robin 恢复尚未由此得到。

## 追加锚（本行以下为增补区）

## 476. 实际 Xi 观察器的无条件联合第二矩

**定理 476.1（增长次数下的完整 Gram 与分辨率）。** 沿用（475.1）—（475.2）的实际普通导数观察器 $Y_P,N_P,\mu_P$。固定非负非零 $w\in C_c^\infty((0,1))$、$0<\delta<1/2$ 和 $0<\varepsilon<1/4$。令 $L=\log T$，并要求

$$
T\le X\le2T,\qquad T^{1/2+\delta}\le H\le T,
\qquad d\le(1/4-\varepsilon)\frac{L}{\log L}.
\tag{476.1}
$$

对每份非零实多项式 $P(z)=\sum_{r=0}^dc_rz^r$，充分大 $T$ 上一致有

$$
N_P\gg_w\frac{HL}{(d+1)^2\,85^{2d}}\|c\|_1^2>0,
\qquad
\sup_{t\in\operatorname{supp}w_{X,H}}|Y_P(t)|
\ll T^{1/4}\|c\|_1.
\tag{476.2}
$$

因而，对每个有限 Lebesgue 测度的可测集 $E$ 及每个 $\eta>0$，

$$
\boxed{
\mu_P(E)\ll_w
 \frac{|E|\sqrt T(d+1)^2\,85^{2d}}{HL}
\ll_{\eta,\varepsilon,\delta,w}
 \frac{|E|T^{1/2+\eta}}{HL}.
}
\tag{476.3}
$$

每次积分内 $P$ 固定；其系数可以任意依赖 $T,X,H$，常数不依赖系数方向。阈值允许依赖 $\varepsilon,\delta,w$，第二个（476.3）还允许依赖 $\eta$。相同界适用于以任意非零有限正组合 $\sum_j a_jY_{P_j}^2$ 替换平方后所得的归一化质量，其中 $a_j\ge0$，每份多项式满足同一次数限制。特别地，当 $0<\eta<\delta$ 时，对全部长度至多 $1/L$ 的区间一致有

$$
\mu_P(I)\ll_{\eta,\varepsilon,\delta,w}
 T^{-\delta+\eta}L^{-2}=o(1).
\tag{476.4}
$$

这些结论不使用定理 475.2 的四移位矩前提。

证明。先将经典近似函数方程用于同一个实际观察器。所用两段公式直接复用 [Conrey，*The fourth moment of derivatives of the Riemann zeta-function*，Quart. J. Math. 39（1988），21–36，p.26，（31）](https://aimath.org/~kaur/publications/15.pdf) 所引的经典公式；下文不使用其固定求导阶数的余项。

对实 $t\in[T,3T]$，记 $N(t)=\lfloor\sqrt{t/(2\pi)}\rfloor$。在复圆盘 $|b|\le1$ 上，令 $z=t+b/L$、$s=1/2+iz$、$\tau=\Im s=t+\Re b/L$。选择固定实截断 $x=\sqrt{t/(2\pi)}$ 和 $y=\tau/(2\pi x)$。于是 $|y-x|=O((\sqrt T L)^{-1})$；将双侧截断都改为 $N(t)$ 至多改变一项，其大小为 $O(T^{-1/4})$。近似函数方程本身的误差同样是 $O(T^{-1/4})$，一致于当前紧实部带。在 Hardy 相位的局部解析分支中，函数方程给出 $\chi(1/2+iz)=e^{-2i\theta(z)}$，故

$$
\begin{aligned}
Z(t+b/L)={}&e^{i\theta(t+b/L)}
 \sum_{n\le N(t)}n^{-1/2-it-ib/L}\\
&+e^{-i\theta(t+b/L)}
 \sum_{n\le N(t)}n^{-1/2+it+ib/L}+R_t(b),
\qquad \sup_{|b|\le1}|R_t(b)|\ll T^{-1/4}.
\end{aligned}
\tag{476.5}
$$

$R_t$ 是解析左边与两份固定有限解析和之差，因而全纯；不需对变化的截断求导。微观圆盘上的 Hardy 相位因子均有统一模界。

复用（474.7）的解析振幅估计，并令

$$
\beta=-\frac{\pi}{4L},\qquad Q(z)=P(z+\beta),\qquad
x_n(t)=\frac{\theta'(t)-\log n}{L}.
\tag{476.6}
$$

经典解析 Stirling 还给出 $\theta'(t)=\frac12\log(t/(2\pi))+O(T^{-2})$、$\theta''(t)=1/(2t)+O(T^{-3})>0$ 及 $\theta(t+b/L)=\theta(t)+b\theta'(t)/L+O((TL^2)^{-1})$。在（476.5）中乘 $-A(t+b/L)/A(t)$ 后，两份和的线性化指数为 $b(\beta\pm ix_n(t))$。和的绝对值是 $O(T^{1/4})$，故振幅与相位线性化误差 $O(T^{-3/4}/L)$ 小于（476.5）的余项。对完整全纯余项使用单位圆盘的 Cauchy 估计，得到

$$
\begin{aligned}
Y_P(t)&=B_Q(t)+r_P(t),\\
B_Q(t)&=-2\Re\bigl(e^{i\theta(t)}D_Q(t)\bigr),\qquad
D_Q(t)=\sum_{n\le N(t)}n^{-1/2-it}Q(ix_n(t)),\\
|r_P(t)|&\ll d!T^{-1/4}\|c\|_1.
\end{aligned}
\tag{476.7}
$$

这里 $A(t)$ 始终未移位，因而左边恰是 $\Xi$ 的普通导数观察器。若 $q$ 为 $Q$ 的系数向量，二项式公式及逆平移给出

$$
e^{-|\beta|d}\|c\|_1\le\|q\|_1
\le e^{|\beta|d}\|c\|_1.
\tag{476.8}
$$

接着估计完整第二矩。恒等式

$$
B_Q^2=2|D_Q|^2+2\Re\bigl(e^{2i\theta}D_Q^2\bigr)
\tag{476.9}
$$

同时保留反向与同向相位。每对 $(m,n)$ 的积分仅从 $t\ge2\pi\max(m,n)^2$ 起算。实际出现的 $|x_n(t)|\le0.6$，从而 $|Q(ix_n)|\le\|q\|_1$、$|Q'(ix_n)|\le d\|q\|_1$，且 $x_n'=O((TL)^{-1})$。在这份截断区间上，含 $w_{X,H}$ 的复振幅之上确界加总变差至多

$$
\ll_w(mn)^{-1/2}\|q\|_1^2
 \left(1+\frac{dH}{TL}\right).
\tag{476.10}
$$

切入端点由上确界项支付，不对截断跳跃作微分。反向非对角相位的导数模为 $|\log(m/n)|$。同向非对角相位 $2\theta(t)-t\log(mn)$ 的导数单调，且截断条件保证

$$
2\theta'(t)-\log(mn)
\ge|\log(m/n)|+O(T^{-2})
\ge\tfrac12|\log(m/n)|.
\tag{476.11}
$$

经典带有界变差振幅的一阶导数积分估计因而控制两类非对角项。对 $N\ll\sqrt T$，使用 $m\ge n/2$ 与 $m<n/2$ 的划分求和，得到

$$
\sum_{\substack{m,n\le N\\m\ne n}}
 \frac1{\sqrt{mn}|\log(m/n)|}\ll N\log(2N).
$$

同向对角 $m=n$ 可以在切入端点附近驻相，但其二阶相位导数 $2\theta''\asymp T^{-1}$。经典二阶导数积分估计给出每项 $O_w(\sqrt T\|q\|_1^2/n)$，总和为 $O_w(\sqrt T L\|q\|_1^2)$。所以完整地有

$$
\int w_{X,H}B_Q^2
=2\int w_{X,H}\sum_{n\le N(t)}\frac{|Q(ix_n(t))|^2}{n}
 +O_w\bigl(\sqrt T L(1+d/L)\|q\|_1^2\bigr).
\tag{476.12}
$$

为控制最弱系数方向，只使用确实包含在原和中的频段 $T^{1/8}\le n\le T^{1/4}$。变量 $x=(\theta'(t)-\log u)/L$ 将其积分区间映为包含 $I=[9/32,11/32]$ 的区间，一致于 $t\in[T,3T]$。对 $u^{-1}|Q(i(\theta'(t)-\log u)/L)|^2$ 使用一阶求和积分比较，其端点和总变差为 $O(T^{-1/8}(1+d/L)\|q\|_1^2)$。因此

$$
\sum_{T^{1/8}\le n\le T^{1/4}}\frac{|Q(ix_n(t))|^2}{n}
\ge L\int_I|Q(ix)|^2\,dx
 -O\bigl(T^{-1/8}(1+d/L)\|q\|_1^2\bigr).
\tag{476.13}
$$

使用经典 Legendre 正交基 $e_k(x)=4\sqrt{2k+1}\,\mathrm P_k(32x-10)$。若 $b_k$ 为 $\mathrm P_k(32x-10)$ 的单项式系数绝对值和，其递推给出 $b_0=1,b_1=42$、$b_{k+1}\le84b_k+b_{k-1}$，因而 $b_k\le85^k$。将 $Q(ix)$ 展开为这份正交基并用 Cauchy–Schwarz，得到全部复系数方向上同样有效的界

$$
\|q\|_1\le4(d+1)85^d\|Q(i\,\cdot)\|_{L^2(I)}.
\tag{476.14}
$$

将（476.13）—（476.14）代入（476.12），其正主项至少为 $c_wHL\|q\|_1^2/((d+1)^2 85^{2d})$。求和积分误差及振荡误差相对此主项分别至多

$$
\begin{aligned}
&\ll_w T^{-1/8}(1+d/L)(d+1)^2 85^{2d}/L
 =T^{-1/8+o(1)},\\
&\ll_w\frac{\sqrt T}{H}(1+d/L)(d+1)^2 85^{2d}
 \le T^{-\delta+o(1)}.
\end{aligned}
\tag{476.15}
$$

这里 $d=O(L/\log L)$ 保证每份所列指数系数损失都是 $T^{o(1)}$。于是 $B_Q$ 的完整加权范数有同一主项下界。（476.7）的误差范数至多 $O_w(\sqrt H d!T^{-1/4}\|c\|_1)$；相对于该主项平方根，其比值由（476.8）控制为

$$
\ll_w d!T^{-1/4}\frac{(d+1)85^d}{\sqrt L}e^{O(d/L)}
\le T^{-\varepsilon+o(1)}.
\tag{476.16}
$$

最后一步使用 $\log(d!)\le d\log d\le(1/4-\varepsilon)L$；$d=0$ 时直接成立。加权 $L^2$ 三角不等式遂给出实际 $N_P$ 的（476.2）下界。

点态上直接使用（476.7）中的实际截断和，而不对分子使用阶乘界：$|D_Q|\le\|q\|_1\sum_{n\ll\sqrt T}n^{-1/2}\ll T^{1/4}\|q\|_1$，余项 $d!T^{-1/4}\|c\|_1\le T^{-\varepsilon}\|c\|_1$ 更小。这给出（476.2）的上界。分子至多为 $\|w\|_\infty|E|$ 乘该上界的平方，除以同一个实际 $N_P$ 即得（476.3）。正组合沿用定理 475.2 证明中的归一化凸组合关系，没有项数损失；（476.4）由（476.1）及（476.3）直接得到。证毕。

短窗口混合第二矩的先例包括 [Das–Pujahari，*Zeros of higher derivatives of Riemann zeta function*，arXiv:2104.10243v1，Theorem 5](https://arxiv.org/abs/2104.10243v1) 的带 Dirichlet 多项式权的 Hardy 混合导数渐近。本条所需的统一性同时覆盖增长次数、最弱系数方向、实际普通 $\Xi$ 导数归一化与相应质量比；不将既有混合矩公式本身作为新增结果。

本条是 `repo-derived` 的实际观察器联合消费；经典近似函数方程、解析 Stirling、Cauchy、振荡积分与 Legendre 正交性均为复用工具，不单独构成新增结果。该消费独立于第 475 节的四矩输入，控制的是指定归一化质量及次数、窗口预算。逐点全阶 Laguerre 条件和逐整数严格 Robin 估计仍需额外论证；这里没有最优分辨率或文献优先权主张。

## 追加锚（本行以下为增补区）

## 477. Mertens 累积峰值到实际 lcm Robin 反例的有限位置界

本节复用 Zhao 的线性 Mertens 误差定义与有效振荡引理，给出到实际整数的定量应用。来源是 [arXiv:2411.18903v2](https://arxiv.org/pdf/2411.18903v2)，定义见印刷第 1 页，§5 引理 10、式 (28) 见第 13—14 页；版本与适用边界由 [既有文献条目](../../../Library/Analytic/zhao2025mertensmeans.md) 保存。Zhao 的引理及经典 Mertens、Euler 乘积与切线不等式均为既有结果，不在此重证。下面的承重结论是累积峰值到有界实际 lcm 见证的仓内综合推导，文献状态为 `repo-derived`，不主张研究优先权。

沿用 $Z(n)=\sigma(n)/n$ 与完整 $I_\psi$。令

$$
\begin{aligned}
c_2&=\gamma_E-\sum_p\sum_{k\ge2}\frac1{kp^k},&
E_2(t)&=\sum_{p\le t}\frac1p-\log\log t-c_2,\\
\Delta_1(x)&=\int_2^xE_2(t)\,dt,&
D_x&=\operatorname{lcm}(1,\ldots,\lfloor x\rfloor),\qquad a=10000.
\end{aligned}
$$

**命题 477.1（累积峰值给出有界实际见证）。** 对每个实数 $x\ge a^2$，若

$$
\Delta_1(x)>12\sqrt x\log x,
\tag{477.1}
$$

则存在实数 $t\in[a,x]$，其实际整数 $N=D_t$ 满足

$$
5040<N\le\exp(x\log x),\qquad
Z(N)>e^{\gamma_E}\log\log N.
\tag{477.2}
$$

证明。对 $u\ge a$，设 $L=\log u$、$a_p=\lfloor\log u/\log p\rfloor$，保留有限完整 prime-power 和与两个非负量

$$
P(u)=\sum_{p^k\le u}\frac1{kp^k},\qquad
Q(u)=\sum_{p\le u}\sum_{k>a_p}\frac1{kp^k},\qquad
\mathcal L(u)=-\sum_{p\le u}\log(1-p^{-a_p-1}).
$$

经典完整 Mertens 账本及有限 Euler 乘积给出

$$
P(u)=\gamma_E+\log\log u+
\frac{\psi(u)-u}{u\log u}-I_\psi(u),\qquad
\log Z(D_u)=P(u)+Q(u)-\mathcal L(u).
\tag{477.3}
$$

这里 $\log D_u=\psi(u)$；所有上端采用 $\le$，包括 prime-power 端点。函数 $v\mapsto\log\log v$ 在 $v>1$ 上凹，而 $\psi(u)>1$，故其在 $u$ 处的切线给出

$$
\log\frac{e^{\gamma_E}\log\log D_u}{Z(D_u)}
\le I_\psi(u)+\mathcal L(u)-Q(u)
\le I_\psi(u)+\frac4{\sqrt u}.
\tag{477.4}
$$

最后一界保留实际指数：当 $p\le\sqrt u$ 时 $p^{-a_p-1}<1/u$；当 $p>\sqrt u$ 时 $a_p=1$。因 $p^{-a_p-1}\le1/4$，有

$$
\mathcal L(u)\le\frac43\left(
\frac1{\sqrt u}+\sum_{m>\sqrt u}\frac1{m^2}\right)
\le\frac43\left(\frac1{\sqrt u}+\frac1{\sqrt u-1}\right)
\le\frac4{\sqrt u}.
$$

反设 $[a,x]$ 上每个 $D_u$ 都满足 $Z(D_u)\le e^{\gamma_E}\log\log D_u$。由 (477.4)，整个实区间上有 $I_\psi(u)\ge-4/\sqrt u$。

记 $I_\theta$ 为将完整核中的 $\psi(v)-v$ 换成 $\theta(v)-v$ 所得积分，$H_2=I_\psi-I_\theta\ge0$。逐个保留高次 prime-power，并只用 $\theta(y)\le y\log y$，得到

$$
\psi(v)-\theta(v)
\le\frac{\sqrt v\log^2v}{\log2},\qquad
H_2(u)\le\frac{2\log u+6}{\log2\sqrt u}.
$$

由 $\log2>1/2$ 与 $\log a>8$，反设因此推出

$$
I_\theta(u)\ge-\frac{6\log u}{\sqrt u}
\qquad(a\le u\le x).
\tag{477.5}
$$

下一步使用 $E_2$ 的实际累积量，区别于既有文献条目中的 $E_1$ 累积量。令

$$
q(u)=\frac{u\log u}{1+\log u},\qquad
h(u)=\frac{\log u}{(1+\log u)^2}.
$$

经典 partial summation 在相同端点给出

$$
I_\theta(u)=\frac{\theta(u)-u}{u\log u}-E_2(u),\qquad
I_\theta'(u)=-\frac{(\theta(u)-u)(1+\log u)}{u^2\log^2u}
$$

（导数几乎处处成立）。因 $q'-1=-h$，积分后是有限区间上的精确等式

$$
\Delta_1(x)=C_a-q(x)I_\theta(x)
-\int_a^xh(u)I_\theta(u)\,du,
\qquad C_a=\Delta_1(a)+q(a)I_\theta(a).
\tag{477.6}
$$

没有丢弃任何未来积分：$I_\theta$ 本身仍是完整无限尾，(477.6) 对它在 $[a,x]$ 上积分。由 $0<\gamma_E<1$ 与 $\sum_p\sum_{k\ge2}1/(kp^k)\le\tfrac12\sum_{m\ge2}1/[m(m-1)]=1/2$，可得 $|c_2|<1$。再用 $\sum_{p\le u}1/p\le\log u$ 与 $|\log\log u|\le\log u$（$u\ge2$），有 $|E_2(u)|\le2\log u+1$。又 $q(a)\le a$、$I_\theta(a)\le2\log a+2$，故

$$
C_a\le a(4\log a+3)=:K_a.
$$

把 (477.5) 代入 (477.6)，用 $q(x)\le x$、$h(u)\le1/\log u$，得到

$$
\Delta_1(x)\le K_a+6\sqrt x\log x+12\sqrt x.
\tag{477.7}
$$

当 $x\ge a^2$ 时，$K_a<3\sqrt x\log x$ 且 $12\sqrt x\le2\sqrt x\log x$，所以右端小于 $12\sqrt x\log x$，与 (477.1) 矛盾。最后，$D_t\ge\lfloor t\rfloor\ge a>5040$，而

$$
\log D_t=\psi(t)
=\sum_{p\le t}a_p\log p\le t\log t\le x\log x,
$$

给出 (477.2)。证毕。

**推论 477.2（带原文高度条件的有效零点到整数上界）。** 取 $0<\varepsilon<\beta_0-1/2$。假设已给定实际零点 $\rho_0=\beta_0+i\gamma_0$，其中 $\beta_0<1$，并满足

$$
\gamma_0>\max\{2,C_1(\varepsilon)\},
$$

这里 $C_1,C_2$ 是 Zhao 引理 10 中可有效计算的常数，必要时增大到正值。定义

$$
Y=\max\left\{2\log a,\ \frac{16}{\varepsilon^2},
\frac2\varepsilon[\log24+(2+\varepsilon)\log\gamma_0],
[C_2(\varepsilon)+1]\log\gamma_0\right\},\qquad B=e^{(1+\varepsilon)Y}.
\tag{477.8}
$$

则存在实际整数 $N$ 严格违反 Robin，且

$$
5040<N\le\exp(B\log B).
\tag{477.9}
$$

证明。取 $X=e^Y>\gamma_0^{C_2(\varepsilon)}$。直接应用 Zhao 引理 10，存在 $x\in[X,X^{1+\varepsilon}]$ 满足

$$
\Delta_1(x)>\frac{x^{\beta_0}}{\gamma_0^{2+\varepsilon}\log x}.
$$

令 $y=\log x\ge Y$。因 $y\ge16/\varepsilon^2$，初等界 $\log y\le\sqrt y$ 给出 $y^2\le e^{\varepsilon y/2}$；(477.8) 因此保证

$$
\frac{x^\varepsilon}{(\log x)^2}
\ge e^{\varepsilon y/2}\ge24\gamma_0^{2+\varepsilon}.
$$

由 $\beta_0-1/2>\varepsilon$，该峰值大于 $12\sqrt x\log x$。命题 477.1 给出 $N\le\exp(x\log x)\le\exp(B\log B)$，证毕。

这里的上界有效依赖所引用的 $C_1,C_2$。原文只声明二者可有效计算，证明为对 Pintz 方法的改编提纲，未列二者数值或公式；本节未提取它们，也未给出数值截止。因而这不是只输入零点矩形便已实现的数值算法，也不适用于未满足原文高度条件的任意离线零点。命题 477.1 独立于该引理；推论在其前提下继承有效性。结论是实际 lcm 见证上界，不要求 CA 最优性、右端零点上确界、零点简单性或分离假设。不存在离线零点的证明、RH 与对每个 $n>5040$ 的严格 Robin 仍未给出。

本节是纸面数学应用；没有科学执行、数值扫描、Lean 编译或 kernel 认证。文献检索只承担既有来源与适用范围核对，不承担证明审查。有限峰值到整数的转换由上述推导承担。

## 追加锚（本行以下为增补区）

## 478. 完整 Mertens 累积峰值的显式有限 Robin 定位

本节复用第 477 节的实际 lcm 响应比较，以及 [Johnston–Yang，arXiv:2204.01980v2，定理 1.1、式 (1.3)](../../../Library/Weil/johnstonyang2022pnt.md) 的无条件完整 Chebyshev 误差界。经典 Mertens 分部求和恒等式由 [Lay，arXiv:1505.03589v1，Lemma 4 证明中的未编号身份，印刷第 6 页](../../../Library/Analytic/lay2015mertenssignchanges.md) 直接供应；它与正权积分、该素数定理估计均作为已有工具；下面保留远端边界并给出显式整数位置的综合命题记为 `repo-derived`，不主张文献优先权。

令 $\Lambda$ 为 von Mangoldt 函数，$\gamma_E$ 为 Euler 常数，并定义

$$
\begin{aligned}
\psi(t)&=\sum_{n\le t}\Lambda(n),&
Q(t)&=\int_t^\infty\frac{\psi(u)-u}{u^2}\,du,\\
r(t)&=\frac{1+\log t}{(\log t)^2},&
I(t)&=\int_t^\infty\frac{\psi(u)-u}{u^2}r(u)\,du,\\
\mathcal U(t)&=t\sum_{n\le t}\frac{\Lambda(n)}n-\psi(t)
-t\log t+(1+\gamma_E)t.
\end{aligned}
\tag{478.1}
$$

所有有限和包括上端点及全部素数幂。经典完整 Mertens 恒等式给出 $\mathcal U(t)=-tQ(t)$；因而 $\mathcal U(t)$ 的定义只需截止到 $t$ 的有限算术和与固定常数，不要求取得无限尾积分的数值。

**命题 478.1（完整素数幂累积峰值的有限见证）。** 对每个实数 $A\ge10000$，令

$$
L=\log A,\qquad B=\exp\!\left(4(L+20)^2\right).
$$

若

$$
\mathcal U(A)>
\sqrt A\left(\frac{4L^2}{1+L}+9\right),
\tag{478.2}
$$

则存在实数 $t\in[A,B]$，使实际整数 $N=\operatorname{lcm}(1,\ldots,\lfloor t\rfloor)$ 满足

$$
5040<N\le\exp(B\log B),\qquad
\frac{\sigma(N)}N>e^{\gamma_E}\log\log N.
\tag{478.3}
$$

证明。引用的完整 Chebyshev 界是对每个 $u\ge2$ 成立的

$$
|\psi(u)-u|\le
9.39u(\log u)^{1.515}e^{-0.8274\sqrt{\log u}}.
\tag{478.4}
$$

它保证本节全部无限积分的绝对收敛及下面使用的无穷端边界消失。直接套用 Lay 的上述完整 Mertens 恒等式，即有

$$
Q(t)=\frac{\psi(t)}t-\sum_{n\le t}\frac{\Lambda(n)}n
+\log t-1-\gamma_E=-\frac{\mathcal U(t)}t.
\tag{478.5}
$$

为保留更换核产生的远端项，写

$$
w(t)=\left(\frac1{r(t)}\right)'
=\frac{(\log t)(\log t+2)}{t(1+\log t)^2},
\qquad 0<w(t)<\frac1t.
$$

由 $I'=rQ'$（几乎处处），在任意有限区间 $[A,Y]$ 分部积分得到

$$
Q(A)=\frac{I(A)}{r(A)}
+\int_A^Yw(t)I(t)\,dt
+Q(Y)-\frac{I(Y)}{r(Y)}.
\tag{478.6}
$$

函数 $I,Q$ 在每个此类区间绝对连续，故该恒等式也适用于素数幂端点。令 $Y\to\infty$ 后，再在任意 $X>A$ 处拆开，远端边界的精确表达是

$$
\mathcal T(X):=Q(X)-\frac{I(X)}{r(X)}
=\int_X^\infty w(t)I(t)\,dt.
\tag{478.7}
$$

以下估计保留并支付 $\mathcal T(X)$。设 $b=\log X\ge1$。由 (478.4) 及 $w(t)\le1/t$，绝对值、Tonelli 与 $v=\log u$ 给出

$$
\begin{aligned}
|\mathcal T(X)|
&\le9.39\int_b^\infty
(v-b)(v^{-0.485}+v^{0.515})e^{-0.8274\sqrt v}\,dv\\
&\le18.78\int_b^\infty v^{1.515}e^{-0.8274\sqrt v}\,dv\\
&\le37.56\int_{\sqrt b}^\infty z^5e^{-4z/5}\,dz.
\end{aligned}
\tag{478.8}
$$

最后一步令 $v=z^2$，使用 $z^{4.03}\le z^5$（$z\ge1$）及 $0.8274>4/5$。对 $z_0\ge16$，经典有限分部积分公式及 $5!/(5-j)!\le5^j$ 给出

$$
\begin{aligned}
\int_{z_0}^\infty z^5e^{-4z/5}\,dz
&=e^{-4z_0/5}\sum_{j=0}^5
\frac{5!}{(5-j)!}\left(\frac54\right)^{j+1}z_0^{5-j}\\
&\le\frac52z_0^5e^{-4z_0/5}.
\end{aligned}
$$

这里的几何级数比为 $25/(4z_0)<1/2$。所以得到完全显式的远端界

$$
|\mathcal T(X)|\le100z_0^5e^{-4z_0/5},
\qquad z_0=\sqrt{\log X}\ge16.
\tag{478.9}
$$

对所选 $X=B$，有 $z_0=2(L+20)\ge40$。由 $\log40<4$、$\log200<6$ 及 $\log(1+L/20)\le L/20$，

$$
\begin{aligned}
\log\!\left(200\sqrt A\,z_0^5e^{-4z_0/5}\right)
&=\log200+\frac L2+5\log\!\left(40(1+L/20)\right)
-\frac85(L+20)\\
&< -6-\frac{17}{20}L<0.
\end{aligned}
$$

故

$$
|\mathcal T(B)|<\frac1{2\sqrt A}.
\tag{478.10}
$$

反设 $[A,B]$ 中没有任何 $\operatorname{lcm}(1,\ldots,\lfloor t\rfloor)$ 严格违反 Robin。第 477 节的完整 Euler 乘积比较 (477.4) 对每个这样的 $t$ 直接给出

$$
I(t)\ge-\frac4{\sqrt t}\qquad(A\le t\le B).
\tag{478.11}
$$

将此下界与 (478.10) 用于有限恒等式 (478.6)，再用 $w(t)\le1/t$，得到

$$
\begin{aligned}
Q(A)
&\ge-\frac4{\sqrt A\,r(A)}
-4\int_A^B\frac{dt}{t^{3/2}}-\frac1{2\sqrt A}\\
&\ge-\frac1{\sqrt A}\left(\frac4{r(A)}+\frac{17}2\right).
\end{aligned}
$$

这与 (478.2) 及 (478.5) 矛盾，因为 $4/r(A)=4L^2/(1+L)$。因而有实际 $t\in[A,B]$ 严格超界。沿用第 477 节的有限库存界，$N\ge\lfloor t\rfloor\ge10000>5040$，且 $\log N=\psi(t)\le t\log t\le B\log B$，即得 (478.3)。证毕。

**推论 478.2（普通素数 $E_1$ 累积量的有限消费）。** 沿用 [Zhao，arXiv:2411.18903v2，式 (14)](../../../Library/Analytic/zhao2025mertensmeans.md) 的

$$
\mathcal E_1=-\gamma_E-\sum_p\sum_{j\ge2}\frac{\log p}{p^j},
\quad E_1(t)=\sum_{p\le t}\frac{\log p}{p}-\log t-\mathcal E_1,
\quad F_1(A)=\int_2^AE_1(t)\,dt,
\quad c_1=2\log2-2+2\mathcal E_1.
$$

对 $A\ge10000$、$L=\log A$，若

$$
F_1(A)-c_1>\sqrt A\left[
\frac{4L^2}{1+L}+9+\frac{2L^2+8L+16}{\log2}\right],
\tag{478.12}
$$

则有同一个显式 $B=\exp(4(L+20)^2)$ 与 (478.3) 中的实际整数见证。

证明。直接使用该来源的恒等式 $Q_\theta(A)=(c_1-F_1(A))/A$。全部高次素数幂满足

$$
0\le\psi(u)-\theta(u)
\le\frac{\sqrt u(\log u)^2}{\log2}.
$$

因此保留它们的非负积分后是

$$
\begin{aligned}
0\le Q(A)-Q_\theta(A)
&\le\frac1{\log2}\int_A^\infty\frac{(\log u)^2}{u^{3/2}}\,du\\
&=\frac{2L^2+8L+16}{\sqrt A\log2}.
\end{aligned}
$$

由此，$\mathcal U(A)=-AQ(A)$ 大于 $\sqrt A(4L^2/(1+L)+9)$；应用命题 478.1，证毕。

第 477 节的输入是普通素数倒数误差 $E_2$ 在有限前缀上的累积峰值；命题 478.1 的输入是有限完整素数幂和 $\mathcal U(A)$，推论 478.2 则消费普通素数 $E_1$ 的累积峰值。新的远端位置 $B$ 由完整尾项 (478.7) 与无条件显式误差 (478.4) 决定，并未删除未来均值。它不要求 CA 最优性、零点高度门槛、零点简单性或零点分离，但也未断言任何实际 $A$ 满足其峰值前提。峰值前提的存在性及全范围严格 Robin 的估计不包含在上述条件结论中。

## 追加锚（本行以下为增补区）

## 479. 任意离线零点的正累积峰值与显式整数位置

本节复用第 478 节的完整 Mertens 量 $\mathcal U$ 与实际 lcm 消费命题；复用[完整积分显式公式与零点和](../../../Library/Analytic/polak2026finiterobinca.md#published-event-dynamics-and-the-unpaid-prime-state-work)，以及 [Révész 的 Cassel 幂和步骤及低高度零点事实](../../../Library/Analytic/revesz1988oscillation.md)。以下保留非振荡包络及全尾项的带符号应用记为 `repo-derived`；不主张文献优先权。

**命题 479.1（不另设零点高度门槛的有限正峰值）。** 设实际非平凡零点 $\rho_0=\beta+i\gamma$ 满足 $\beta>1/2$、$\gamma>0$，令

$$
\delta=\beta-\tfrac12,\quad D=\gamma+10,\quad
m_0=100D^2\delta^{-2},\quad m_1=500D^4\delta^{-2}.
$$

则存在实数 $A\in[e^{4m_0},e^{28m_1}]$ 使

$$
\mathcal U(A)>\sqrt A\,(4\log A+9).
\tag{479.1}
$$

从而，若 $B_0=\exp(4(28m_1+20)^2)$，存在实际整数 $5040<N\le\exp(B_0\log B_0)$ 严格违反 Robin。

证明。下列零点多重集均包括全部非平凡零点，不假设简单性、分离或存在最右零点。写 $\rho=b+i\eta$、$a_\rho=[\rho(1-\rho)]^{-1}$，定义

$$
H(y)=\sum_\rho a_\rho e^{\rho y}\quad(y\in\mathbb R),\qquad
\sum_\rho a_\rho=C=2+\gamma_E-\log(4\pi)<1.
$$

经典低高度结果给出 $|\eta|>10$。由 $0<b<1$，直接有 $\Re a_\rho\ge1/(2\eta^2)$，故

$$
\sum_\rho\eta^{-2}\le2C<2,\quad
\sum_\rho|a_\rho|<2,\quad
\#\{\rho:|\Im\rho|\le T\}\le2T^2,\quad
|H(y)|\le2e^{\max(y,0)}.
\tag{479.2}
$$

这里 $\Re a_\rho$ 的分母不超过 $2\eta^4$，分子至少为 $\eta^2$。所有级数在实紧集上一致绝对收敛，$H$ 由共轭对称性为实值。复用完整积分显式公式，对 $y>0$ 有

$$
H(y)=\mathcal U(e^y)-\log(2\pi)
+\sum_{j\ge1}\frac{e^{-2jy}}{2j(2j+1)}\le\mathcal U(e^y).
\tag{479.3}
$$

最后的级数小于 $1$，而 $\log(2\pi)>1$；不丢弃素数幂或平凡零点修正。

令 $a=\beta^2+16\beta$，把 $|\eta-\gamma|\le6$ 的 $n$ 个零点（计重数）变成复数

$$
z_\rho=\exp\!\left(m_0[(\rho-i\gamma)^2+16(\rho-i\gamma)-a]\right).
$$

其中至少一个为 $1$，且 $n\le2(\gamma+6)^2\le2D^2$。使用所引 Cassel 步骤的离散结论：去掉一个 $1$ 后把其余根连同共轭取成实系数多项式的根，存在整数 $1\le\nu\le2n+1$ 使 $\Re\sum z_\rho^\nu\ge1$。于是 $m=\nu m_0$ 满足 $m_0\le m\le m_1$，且相应有限和的实部至少为 $e^{am}$。

记完整高斯零点和

$$
E_\gamma(m)=\sum_\rho e^{m(\rho-i\gamma)^2+16m(\rho-i\gamma)}.
$$

对所遗漏的 $|\eta-\gamma|>6$，按整数距离 $k\ge6$ 分组，利用 (479.2) 及 $b^2+16b\le17$，得到

$$
\begin{aligned}
\left|\sum_{|\eta-\gamma|>6}e^{m(\rho-i\gamma)^2+16m(\rho-i\gamma)}\right|
&\le2D^2\sum_{j\ge0}(j+1)^2e^{m(17-(6+j)^2)}
\le4D^2e^{-19m},\\
\Re E_\gamma(m)&\ge\tfrac12e^{am}.
\end{aligned}
\tag{479.4}
$$

此处 $m\ge m_0\ge1$，并用 $\sum_{j\ge0}(j+1)^2r^j<2$（$0\le r\le1/10$）及 $e^{(a+19)m}>8D^2$。

现在支付带符号适配。取均值 $M=16m$、方差 $2m$ 的高斯密度，写

$$
g(y)=\frac{e^{-(y-M)^2/(4m)}}{\sqrt{4\pi m}},\quad
u=\frac{y-M}{2m},\quad P=(u+i\gamma)(u+i\gamma-1)-\frac1{2m},\quad
K(y)=-\Re(e^{-i\gamma y}P)g(y),\quad
v(y)=2(u^2+\gamma^2+1)g(y)\ge|K(y)|.
$$

对高斯核求两次 $M$ 导数，保持 $m$ 固定，然后在 $M=16m$ 取值。绝对可和性与高斯衰减允许逐项积分，由 $a_\rho\rho(\rho-1)=-1$ 得到精确等式

$$
\int_{\mathbb R}H(y)K(y)\,dy=\Re E_\gamma(m),\qquad
\int_{\mathbb R}H(y)v(y)\,dy
=2\sum_\rho a_\rho\left(\rho^2+\gamma^2+1+\frac1{2m}\right)e^{m\rho^2+16m\rho}.
\tag{479.5}
$$

包络对应的第二个积分没有被删去。用 $|\eta|>10$ 与 (479.2)，按 $|\eta|\in[k,k+1)$ 分组，有

$$
\sum_\rho e^{-m\eta^2}\le\sum_{k\ge10}2(k+1)^2e^{-mk^2}\le500e^{-100m},\qquad
\left|\int H v\right|\le1000D^2e^{-83m}.
\tag{479.6}
$$

后一式使用 $|a_\rho|(\gamma^2+1+1/(2m)+|\rho|^2)\le\gamma^2+3\le D^2$。

反设 (479.1) 在 $e^{4m}\le A\le e^{28m}$ 全部失败。由 (479.3)，在 $J=[4m,28m]$ 上 $H(y)\le b(y):=(4y+11)e^{y/2}$。因 $K+v\ge0$，保留整个实轴上的包络积分及区间外响应，得

$$
\Re E_\gamma(m)\le2\int_0^\infty b(y)v(y)\,dy
+\left|\int_{\mathbb R}H(y)v(y)\,dy\right|
+2\int_{\mathbb R\setminus J}|H(y)|v(y)\,dy.
\tag{479.7}
$$

下面的三个高斯估计给出全部常数。第一项以 $e^{y/2}g(y)$ 换成均值 $17m$、方差 $2m$ 的高斯，令 $z=y-17m$，使用 $4y+11\le81m+2z^2$（$y\ge0$）、$u^2\le1/2+z^2/(2m^2)$ 及二、四阶矩 $2m,12m^2$，得到

$$
\int_0^\infty bv\le2e^{33m/4}\bigl[85m(\gamma^2+2)+93\bigr]
\le300mD^2e^{33m/4}.
\tag{479.8}
$$

对 $y\ge0$ 的区间外部分用 $|H(y)|\le2e^y$。指数倾斜把均值移至 $18m$，令 $z=y-18m$，此部分满足 $|z|\ge10m$，且 $u^2+\gamma^2+1\le D^2+z^2/(2m^2)$。把高斯指数分为相等两半，支付 $e^{-25m/2}$ 并对方差 $4m$ 的高斯积分。对 $y<0$ 同样支付 $e^{-32m}$，得

$$
\int_{[0,\infty)\setminus J}|H|v\le12D^2e^{9m/2},\qquad
\int_{(-\infty,0)}|H|v\le8D^2e^{-32m}.
\tag{479.9}
$$

由 (479.6)—(479.9)，反设蕴含 $\Re E_\gamma(m)\le2000mD^2e^{33m/4}$。但

$$
\begin{aligned}
a-\tfrac{33}4&=17\delta+\delta^2,\\
\log(4000mD^2)&\le\log(2\cdot10^6D^6\delta^{-2})
<20+6D+2/\delta\le D^2/\delta
<17\delta m.
\end{aligned}
$$

这里 $D>20$、$0<\delta<1/2$、$m_0\le m\le m_1$，故与 (479.4) 矛盾。这证明 (479.1)。所得 $A>10000$，且 $4\log A+9>4(\log A)^2/(1+\log A)+9$。直接应用命题 478.1，并用 $\log A\le28m_1$，即得 $N$ 的上界。证毕。

本命题只以实际离线零点为条件，不给出该条件的实例或 RH 的判定；它给出的正峰值是完整 $\mathcal U$ 的峰值，不把某个余项的绝对值下界当成其正向下界，也不把截断参数 $B_0$ 当成整数 $N$ 的上界。

## 追加锚（本行以下为增补区）
