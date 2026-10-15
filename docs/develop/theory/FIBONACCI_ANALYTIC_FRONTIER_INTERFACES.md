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
