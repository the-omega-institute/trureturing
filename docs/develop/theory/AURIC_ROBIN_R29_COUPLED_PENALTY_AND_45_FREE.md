# Robin 的关系递归研究

R29：联动惩罚与45-free

共享约束 · 非零尾项 · 全域严格余量

研究记录 · 2026-11-08

由指定已发表输入推出：所有45-free 的 $n>5040$ 满足 Robin 不等式。\
相对所查已发表21-free基线，素因子指数上限由20提高到44。\
高位零点尾保持非零；共同余量大于 $3.2\times10^{-16}$。\
普通证明内部交叉核查通过；未声称外部审稿、优先权或完整RH。

## 目录

- [1. 本轮结论与证据等级](#section-1)
- [2. 怎样落实用已知无穷约掉未知无穷](#section-2)
- [3. 截至2026-11-08的前沿：需要分轴比较](#section-3)
- [4. 为什么旧方法确实卡在26，而新方法能跨过去](#section-4)
- [5. 新的关系：指数与大小共享一个预算](#section-5)
- [6. 无限零点尾怎样被压成可支付预算](#section-6)
- [7. 一条全局凸性关系完成闭合](#section-7)
- [8. 明确量化：好多少、好在哪里](#section-8)
- [9. 另一条已闭合结果：局部素数条件与联合缺陷](#section-9)
- [10. 与 trureturing 结合的准确范围](#section-10)
- [11. 为什么这里还不能取 t→∞](#section-11)
- [12. 核查、复算与交付范围](#section-12)
- [参考来源](#section-13)
- [附录 A：强制来源更正：零点计数常数](#section-14)
- [附录 B：统一指数与大小联动惩罚](#section-15)
- [附录 C：高零点配对与45-free完整闭合](#section-16)
- [附录 D：同一45-free结论的全局凸性收尾](#section-17)
- [附录 E：局部素数条件与联合缺陷](#section-18)
- [附录 F：旧27-free消费者的严格障碍](#section-19)
- [附录 G：冻结R28分析证明：须同时采用附录A修正](#section-20)
- [附录 H：冻结R28核分析与无穷和交换](#section-21)
- [附录 I：独立关系保持与严格余量模块](#section-22)

<a id="section-1"></a>

## 1. 本轮结论与证据等级

**本轮得到一个实质性的家族扩展：在列明的已发表输入下，给出并内部交叉核查了“所有45-free 的 n\>5040 满足 Robin 不等式”的普通证明。** 同时得到一个适用于其余指数任意大的局部条件：只要存在素数 p 满足 p^{ν_p(n)+1}≤80,000,000，Robin 即成立。

这里45-free 的含义是：没有任何素数的45次方整除 n，等价于每个素因子指数至多44。它不表示 n 没有45个素因子，也不表示“黎曼猜想证明了45%”。Robin 目标为

$$
\sigma(n)<e^\gamma n\log\log n\qquad(n>5040).
$$

全体整数上的这一不等式等价于黎曼猜想；限制整数族上的证明仍是局部进展。\[1\]

本轮采用三种明确等级：**P** 为已发表结果或官方状态；**M** 为公开论文稿或外部计算主张；**本轮普通证明** 为本文给出、经内部独立数学审查和数值证书检查的推导。后者尚未外部同行评审，也不是 Lean 内核认证，不能写成“新发表的世界纪录”。大型零点计算与有限 Robin 计算作为已发表输入导入，本轮没有重跑。

| 比较轴 | 已核读的命名基线 | 本轮结果 | 准确增量 |
|:---|:---|:---|:---|
| 全 t-free 家族 | Axler2023：21-free，P | 45-free，普通证明 | 指数上限20→44，增加24级 |
| 相对本项目上一轮 | R28：26-free，普通证明 | 45-free | 指数上限25→44，增加19级 |
| 单个2-adic限制 | ν<sub>2</sub>≤20，P | ν<sub>2</sub>≤25 | 增加5级；其他指数任意 |
| 单个3-adic限制 | ν<sub>3</sub>≤12，P | ν<sub>3</sub>≤15 | 增加3级；其他指数任意 |
| 单个5-adic限制 | ν<sub>5</sub>≤8，P | ν<sub>5</sub>≤10 | 增加2级；其他指数任意 |
| 单个7-adic限制 | ν<sub>7</sub>≤6，P | ν<sub>7</sub>≤8 | 增加2级；其他指数任意 |
| 缺失某个小素数 | p≤1,771,559 且 p$\nmid$n，P | p≤80,000,000 且 p$\nmid$n | 素数上限约45.16倍 |
| 完整 RH、零点高度和比例 | 各自现有结果 | 没有新结论 | 增量0 |
| 反例的渐近稀疏性 | 2025更正后的 x^{O(1/loglog x)}，P | 固定算术筛选 | 渐近计数增量0 |

这些比较只针对列出的同量词家族。没有证明其为全球文献中最强，也没有证明本文新集合与所有已知家族的并集之间恰好相差多少。\[2-5\]

<a id="section-2"></a>

## 2. 怎样落实“用已知无穷约掉未知无穷”

这条思路可以严格使用，但需要改变一句话的逻辑形式。关系存在不阻止量趋零：a_n=1/n、b_n=1/n<sup>2</sup> 都趋零，同时 b_n/a_n<sup>2</sup>=1。可保留的研究原则是：**原读出可以趋零；恰当的关系或归一化读出仍可能保留信息；误差也必须按同一个变换传递。**

本轮没有令任何未知无穷尾项等于零。实际使用了三种可证明的操作：Euler 乘积把无限素数因子封装成 ζ(t)；显式公式和 Stieltjes 积分把无限零点尾封装成非零预算；凸性把一整个连续区间的余量检验变成有限常数条件。闭合来自严格余量，而不是来自“还有一层关系”本身。

这一点也回答了“无尽深渊”的担忧：递归应当有停止条件。若新增变量没有保留新的实际约束、没有改善预算、没有扩大已证量词，就不计为推进。本轮新增的有效状态是素因子指数和整数大小的联动，不是一个新的抽象名称。

<a id="section-3"></a>

## 3. 截至2026-11-08的前沿：需要分轴比较

### 3.1 黎曼猜想

Clay 当前页面仍将完整 RH 标为未解决。\[6\] 有限高度、临界线比例、简单零点比例、零点密度属于不同问题，不能相加为一个“完成度”。

| 方向 | 本轮核读的结果 | 状态与边界 |
|:---|:---|:---|
| 严格有限验证 | Platt-Trudgian：高度3,000,175,332,800，最低12,363,153,437,138个非平凡零点位于临界线 | P；本文保守使用 H=3·10<sup>12</sup>；没有重跑 |
| 已发表临界线比例基线 | Pratt-Robles-Zaharescu-Zeindler：至少0.417293962；简单且在线至少0.407511457 | P；不能把它称为2026所有论文稿中的最大数值 |
| 2026普通论文稿 | Lamzouri v2：简单且在线比例至少3/2−cot(1/√2)/√2≈0.6725007 | M；明确主张无条件；本轮未完整重现其证明 |
| 更高的2026计算辅助论文稿 | Knausgård v1：简单且在线至少1669159/2478195≈0.67353820 | M；额外3个计算评价公理；未本地重建 |
| 已发表零点密度进展 | Guth-Maynard，Annals2026，给出 N(σ,T)≤T^{30(1−σ)/13+o(1)} 等结论 | P；不宣称对每个σ均为最佳界 |

这里有一项必须纠正的文献辨别：旧的67.25%左右简单零点结果有 RH 条件，但 Lamzouri2026 和 Alpöge-Furman2026 是新的无条件论文稿主张。不能把它们仅凭相似数值一起归为“有条件”。同样，“简单或在线”“简单且在线”“不同零点”三个比例也不能混写。\[7-10\]

R28 保留的 Murphy 有限窗口、QuasiRiemannTracker、Polak 更大有限 Robin 计算和 Bell 支撑下界仍按外部主张保存。它们未在本轮重建，未升级为已发表输入，也没有被用于45-free证明；审查清单保留其原有版本和限制。

### 3.2 Robin 已发表比较

Axler2023 的 Theorem1 给出21-free；Assani-Chester-Paschal2026 的 Theorem7 仍证明21-free。对26、27、38、45等明确用词和2026 t-free 文献的有界检索未找到另一篇可直接引用的更强已发表全家族定理，因此本报告使用“本次检索找到的最强已发表 t-free 比较基线为21”，不主张文献穷尽。\[2,11\]

有限全整数前缀采用 Morrill-Platt 的精确形式：

$$
5040<n\le N_{k_0}=x_0\#,
\quad x_0=29\,996\,208\,012\,611,
\quad k_0=999\,999\,476\,056.
$$

这里 x# 为所有不超过 x 的素数之积。应使用这个精确端点，而不能把论文里的简写十进制指数当成等值端点。\[1,2\]

Axler-Nicolas2023 的公开作者版本本轮已找到并核读。其 Theorem1.3 对 n≥exp(26,318,064,420) 给出更强的全整数正误差包络：

$$
\frac{\sigma(n)}n<e^\gamma\log\log n+
\frac{0.0094243e^\gamma}{(\log\log n)^2}
-\frac{2\sqrt2e^\gamma}{\sqrt{\log n}}
+\frac{4.143e^\gamma}{\sqrt{\log n}\log\log n}.
$$

因此，“保留负的平方根尺度修正”有明确已发表前例；本文不把这一思想命名为首次发现，也不把只适用于 t-free 的2.81·10<sup>-14</sup>比较写成超越所有全整数包络。\[12\]

另一条很强的已发表基线是 Luca-Pomerance-Solé2025 更正稿：Robin 反例数至多 x^{O(1/loglog x)}。它的渐近稀疏性强于任何固定整除条件带来的正密度容器，但稀疏仍不等于不存在。\[5\]

### 3.3 本轮处理的原文常数更正

Bellotti-Wong2025 对T≥e的新零点计数界为0.10076logT+0.24460loglogT+8.08344；其表1脚注同时把 HSW2022 的旧加法常数9.3675 更正为9.4925。\[13\] 本轮已补上这个更正。冻结的 R28 文件保留原貌，但必须与附录的来源补丁一起阅读：对本轮消费范围T≥H=3·10<sup>12</sup>，新常数仍给 N(T)≤TlogT 和 \| N(T)−A(T)\|\<2logT，故所有后续消费者预算不变。内部复算已使用更正常数。

<a id="section-4"></a>

## 4. 为什么旧方法确实卡在26，而新方法能跨过去

记

$$
R_t(N_k)=\frac{\prod_{p\le p_k}(1-p^{-t})/(1-p^{-1})}{\log\log N_k}.
$$

经典压缩给 σ(n)/(n loglogn)≤R_t(N_k)。上一轮证明了 t=26 足够，但它在分子端把指数推到 t−1，同时在分母端按最小的 primorial 大小计量。这两个极端不必由同一个整数同时实现。

本轮对这个怀疑给出严格诊断，而不只是上界失败：

$$
\log\frac{R_{27}(N_{k_0})}{e^\gamma}>2.4\cdot10^{-9}>0.
$$

更强地，对所有 prime endpoints x=p_k∈\[x0,5·10<sup>13</sup>\]，同一对数差大于3·10<sup>-11</sup>。证明使用 Rosser-Schoenfeld 的 ψ−θ\>0.98√x 下界，并保留全部负修正的上界。\[14\]

因此，在该端点，26确实是这个分离消费者所能支持的最大 t。继续只收紧同一个量的上界，不能把其真实正值变成负值。这个结论只说明辅助消费者受阻，绝不是一个27-free Robin反例。突破必须恢复丢掉的联系。

<a id="section-5"></a>

## 5. 新的关系：指数与大小共享一个预算

给定任意 t-free n≥N_k0，选 k 使 Nk≤n\<Nk+1。将实际素因子 q_i 按大小排列，对应到前 k 个素数 p_i；指数保持在原位置，不足处补 a_i=0。因为 q_i≥p_i，得到

$$
S_a=\sum_{p\le x}a_p\log p\le\log n,
\qquad\theta(x)\le\log n.
$$

补零很重要：缺失一个小素数也损失分子中的 Euler 因子，不能把那项当作已存在。max(θ,S_a) 很重要：压缩后的 S_a 可能比 θ 小，不能用它给分母一个虚假的大小。

于是保留共同约束后，定义联动惩罚

$$
\begin{aligned}
\mathcal P_t(x,\mathbf a)={}&
\sum_{p\le x}\log\frac{1-p^{-t}}{1-p^{-(a_p+1)}}\\
&+\log\log\max\{\theta(x),S_a\}-\log\log\theta(x).
\end{aligned}
$$

准确返回原整数的上界为

$$
\boxed{G(n)\le E_\theta(x)-\mathcal P_t(x,\mathbf a)
-\log\zeta(t)+\tau_t(x).}
$$

其中 τ_t=−Σ\_{p\>x}log(1−p<sup>-t</sup>)≥0，是完整保留的 Euler 尾。

本轮关键引理是对所有 x≥x0、所有 t≥9 和全部补零指数向量成立的统一下界：

$$
\boxed{\mathcal P_t(x,\mathbf a)\ge\frac{2.15}{\sqrt x\log x}.}
$$

证明中取 V=(1+10<sup>-5</sup>)x+3√x、λ=1/(VlogV)，将分母增量转成 λ 的指数成本。小素数 p≤(4/3)√x 至少支付 λlogp；大素数 p\>2√x 至少支付0.99/p<sup>2</sup>。中间部分非负。Abel求和与统一 θ 界使这两部分给出实际系数2.197548150916…，因而选2.15有保守余量。完整证明处理 a=0、a=1、a≥2 以及 S_a≤θ、θ\<S_a≤V、S_a\>V 的全部情形。

这正是本轮可称为“升维”的数学内容：把原先独立松弛的两个读出提升成同一个可行状态，随后利用它们不能同时达到各自最坏值的约束。无需假定黄金比例、物理三维性或余弦固定点能够约束素数分布。

<a id="section-6"></a>

## 6. 无限零点尾怎样被压成可支付预算

继承的准确相消关系为 Eθ=Q−Kθ−T<sub>2</sub>，且 Q≥0、T<sub>2</sub>≥0。对 Kθ 使用积分显式公式后，得到

$$
E_\theta\le Q+|Z|+
\frac{2.04}{\sqrt xL}+
\frac{4.5}{x^{2/3}L}+\frac{\log(2\pi)}{xL},\qquad L=\log x.
$$

低零点用已发表有限高度位置定理与 Hadamard恒等式，贡献至多 (L<sup>-1</sup>+L<sup>-2</sup>)·0.047/√x。

高零点先用更正后的计数界。与上一轮不同，本轮保留 Stieltjes 分部积分的负端点：

$$
\mathcal T_H=-2N(H)/H^2+4\int_H^\infty N(T)T^{-3}\,dT
<3\cdot10^{-12}.
$$

随后保留 β↔1−β 的函数方程配对：

$$
\sum_{|\Im\rho|>H}\frac{x^{\beta-1}}{(\Im\rho)^2}
\le\frac{1+x^{-1}}2\mathcal T_H
<1.501\cdot10^{-12}.
$$

没有假设 H 以上零点在线，也没有把未知尾项删去。得到

$$
|Z|\le(L^{-1}+L^{-2})
\left(0.047/\sqrt x+1.501\cdot10^{-12}\right).
$$

联动惩罚2.15/(√xL) 抵消了所有平方根尺度正项后，仍留有负系数

$$
-\frac{49\,819\,873}{1\,422\,900\,000}<-0.035.
$$

所以剩下的精确任务是估计

$$
Q+A(L^{-1}+L^{-2})-0.035e^{-L/2}/L,
\qquad A=1.501\cdot10^{-12}.
$$

<a id="section-7"></a>

## 7. 一条全局凸性关系完成闭合

本包保留了两条经核查的收尾。第一条用 Axler2024 θ界和六个有限区间，再接 L≥55 的解析尾；第二条只用既有 Morrill-Platt θ界，并以一个全局凸性不等式替代这些区间。\[15\] 两者得到相同的45-free结论和同一保守预算。

第二条更直接展示“用已知无限结论构造”的方式。对 logx0≤L≤55，二阶余项满足

$$
Q<\frac{L^3}{1000x}<\frac{0.0002}{\sqrt xL}.
$$

吸收 Q 后，可保守写成

$$
E_\theta-\mathcal P_t
<A(L^{-1}+L^{-2})-c\frac{e^{-L/2}}L,
\qquad c=0.034.
$$

取 R=2.81·10<sup>-14</sup>。两个准确的有理数比较给出

$$
2R(68/25)^{27}<c,
\qquad A\frac{32}{31}<56R.
$$

由 e\<68/25 和对全部实数成立的 e<sup>u</sup>≥1+u，

$$
c e^{-L/2}>2R e^{(54-L)/2}\ge R(56-L).
$$

因此对所有 L≥31，

$$
A(1+1/L)-c e^{-L/2}<RL.
$$

除以正的 L 后，就支付了完整连续区间。对 L≥55，已发表全局相对 θ 界直接给 Q\<10<sup>-21</sup>；剩余正项满足

$$
10^{-21}+A\frac{56}{3025}<R.
$$

这两段完整覆盖 x≥x0，从而

$$
\boxed{E_\theta(x)-\mathcal P_t(x,\mathbf a)<2.81\cdot10^{-14}.}
$$

最后，Euler级数与 log(1+u)\>u−u<sup>2</sup>/2 给出

$$
\log\zeta(45)>2^{-45}-2^{-91},
\qquad\tau_{45}\le2/(44\cdot10^{572}).
$$

严格余量为

$$
\boxed{2^{-45}-2^{-91}-2/(44\cdot10^{572})-2.81\cdot10^{-14} > 3.2\cdot10^{-16}.}
$$

这证明所有45-free n≥N_k0 的 G(n)\<0，再接已发表有限前缀，得到全体45-free n\>5040。共同的数值余量只声明在尾部成立，不为有限前缀另作未经计算的统一余量声明。

**预算图的文字说明（原稿未提供图片文件）：** 文中旧分离消费者的充分预算为 1.243668062349…×10⁻⁸，新联动消费者的充分预算为 2.81×10⁻¹⁴，并与 log ζ(t) 阈值比较；这两个预算对应不同的量。此处据正文列值说明，原图注保留如下。

*图 1：不同消费者的充分预算与 log ζ(t) 阈值。曲线和水平线是严格证明中数值的图示；图本身不承担证明。*

<a id="section-8"></a>

## 8. 明确量化：好多少、好在哪里

本轮新联动消费者的统一预算为2.81·10<sup>-14</sup>，上一轮分离消费者的 Eθ端点预算为1.243668062349…·10<sup>-8</sup>，数值相差约442,586倍。**两个量并不相同：新量为 Eθ−P_t，旧量为 Eθ。** 这量化的是保留共享约束后，充分判据的预算改善；不能写成“同一个 Eθ误差缩小442,586倍”。

同一整数族指标的改进更容易解释：已发表比较为21-free，本轮为45-free，允许素因子指数从20提高到44。上一轮26-free到本轮45-free增加19级。研究包中38-free是中间可独立复用的推论，最终结论取45。

t-free整数自然密度为1/ζ(t)。本轮数值为

$$
1/\zeta(21)=0.999999523067240677\ldots,
$$

$$
1/\zeta(45)=0.999999999999971578\ldots.
$$

二者密度差约4.769327309·10<sup>-7</sup>，即0.00004769327309个百分点；单看这两个族的补集，密度约缩小1.678058·10<sup>7</sup>倍。这个密度比较不是 RH完成度，也没有超过2025已有反例稀疏性结论。

本轮在完整 RH、已核验零点高度、临界线比例、零点密度指数、反例渐近稀疏性几个方向上的新增结论均为0。报告不把一个指标的进步转移成另一个指标的纪录。

<a id="section-9"></a>

## 9. 另一条已闭合结果：局部素数条件与联合缺陷

对 n\>N_k0 和素数 p≤x0，沿用经过区间认证的 R28统一端点界 Eθ(x)\<1.244·10<sup>-8</sup>，保留该实际素因子的有限指数缺陷。如果该素数缺失，需增加下一素数替补的支撑修正；这一步已经计入

$$
G(n)<1.244\cdot10^{-8}+\frac1{x_0-1}-p^{-\nu_p(n)-1}.
$$

因为前两项之和小于1/80,000,000，且 p^{ν_p(n)+1}≤80,000,000 自动保证 p≤x0，再用已发表有限前缀处理5040\<n≤N_k0，得到对所有 n\>5040 的结论

$$
\boxed{p^{\nu_p(n)+1}\le80\,000\,000\quad\Longrightarrow\quad G(n)<0.}
$$

从而，任意可能的 Robin反例必须满足

$$
\boxed{\operatorname{lcm}(1,2,\ldots,80\,000\,000)\mid n.}
$$

这是必要条件，不是说该最小公倍数的倍数是反例，也不是说它们每个素因子的指数都很大。

对 n\>N_k0，同时保留有限集合 P 中几个素数的缺陷，并要求 P 中每个素数都实际整除 n，可得到

$$
G(n)\le E_\theta(x)-\sum_{p\in P}[-\log(1-p^{-\nu_p(n)-1})].
$$

如果所选的2、3或5中有素数缺失，单素数推论已经处理；若都存在，则使用上式。加上有限前缀，对所有 n\>5040，ν<sub>2</sub>≤26 且 ν<sub>3</sub>≤16 足够，因为2<sup>-27</sup>+3<sup>-17</sup>\>1.244·10<sup>-8</sup>；另一例为 ν<sub>2</sub>≤26、ν<sub>3</sub>≤17、ν<sub>5</sub>≤11 三者同时成立。它们是联合条件，不能把“且”改为“或”。

<a id="section-10"></a>

## 10. 与 trureturing 结合的准确范围

本次固定审查提交为 `9a201d9cb6089d7ec36fd2c2cdffbbd9797a2ae5`。相对上一轮固定提交，它前进149次提交；对 D5与docs 完整子树的比较发现52个变动路径。Robin子树从227到236个文件，有20个变动、9个新增。20份选定快照的 Git blob 哈希均与树条目一致；未声称审查整个仓库的依赖或重新构建其 Lean证明。\[16\]

最有价值的对应是：原多项式零响应文档明确给出“四份分别优化的绝对预算仍有正底，而实际带符号关系可精确抵消”的模型。这与本轮恢复 Eθ−P_t、保留零点反射配对、保留 Stieltjes负端点相吻合。使用的是共同来源约束，不是任意把两项相减。

仓库的新二阶、四阶矩传递接口保留了方差或四阶矩渐近供应作为前提。它们能够传递某项已知误差关系，但本身没有证明实际素数误差满足该供应，也没有直接给全整数 Robin符号。FIB有限窗口精度安排也明确区分逐个有限窗口和无限记录结论。

因此，独立模块采用六步：**准确等式、同源相消、联动状态、已证无限供应、严格误差余量、返回原量词。** 原则“读出与误差也构成二元关系”落实为同一个归一化变换必须同时作用在信号和误差上。模块全文在后附独立章节和单独文件中。

<a id="section-11"></a>

## 11. 为什么这里还不能取 t→∞

每一个固定整数都是某个 t-free族的成员，但本轮只对 t≤45闭合了共同预算。不能把“任意固定 t最终有某个有效起点”与“所有整数已有共同覆盖”混同。logζ(t) 随 t趋无穷而趋零，固定正预算不能无限支付它。

现有证书在 L=55 的无限尾起点给约2.77871076·10<sup>-14</sup>，已经高于logζ(46)≈1.42108548·10<sup>-14</sup>。因此**这一份证书不证明46-free**；这不说明46-free为假。若继续推进，应针对高位零点带符号响应、实际误差的联合供应或更强全整数结构约束提出明确的新引理。

本轮完成的是一个停止得下来的研究单元：旧消费者障碍被证明，新共享约束被提出并核查，45-free与局部素数条件已闭合，剩余缺口有明确量词和误差目标。

<a id="section-12"></a>

## 12. 核查、复算与交付范围

正文结论由附录完整普通证明支持。核心联动推导经过另一套有理数常数重构；45-free的区间收尾经过独立320阶Taylor有理数重构，并以192位和240位 Arb球算术交叉计算；MP替代收尾使用独立有理数检查。原整数支撑压缩、补零、缺失素数替补、连续全域与无限尾覆盖都被逐条审查，而非仅运行脚本。

证明范围与数值检查范围分别记录。复算不意味着重新验证 Platt-Trudgian 的大型零点计算，也不意味着重新枚举 Morrill-Platt的巨大有限整数区间。外部预印本结论和仓库形式化报告没有用作数论承重输入。完整代码、证书、依赖修正、冻结来源、独立审查与文件散列均在复核包内。

<a id="section-13"></a>

## 参考来源

1.  Morrill-Platt, *Robin’s inequality for20-free integers*, Integers21(2021),A28. <https://math.colgate.edu/~integers/v28/v28.pdf>.

2.  Axler, *On Robin’s inequality*, Ramanujan J.61(2023),909-919. <https://doi.org/10.1007/s11139-022-00683-0>.

3.  Hertlein, *Robin’s inequality for new families of integers*, Integers18(2018),A71. <https://math.colgate.edu/~integers/s71/s71.pdf>.

4.  Vega, *Robin’s criterion on divisibility*, Ramanujan J.59(2022),745-755. <https://doi.org/10.1007/s11139-022-00574-4>.

5.  Luca-Pomerance-Solé, Corrigendum to A8, Integers25(2025), posted2025-06-02. <https://math.colgate.edu/~integers/z8/z8.errata.pdf>.

6.  Clay Mathematics Institute, RH official status, accessed2026-11-08. <https://www.claymath.org/millennium/riemann-hypothesis/>.

7.  Platt-Trudgian, BLMS53(2021),792-797. <https://doi.org/10.1112/blms.12460>; author version <https://arxiv.org/abs/2004.09765>.

8.  Pratt-Robles-Zaharescu-Zeindler, *More than five-twelfths of the zeros of ζ are on the critical line*, Res. Math. Sci.7(2020),2. <https://doi.org/10.1007/s40687-019-0199-8>.

9.  Lamzouri, arXiv2609.02882v2,2026-09-08. <https://arxiv.org/abs/2609.02882v2>; Knausgård, arXiv2610.08965v1,2026-10-06. <https://arxiv.org/abs/2610.08965v1>; Alpöge-Furman, arXiv2608.13637v2. <https://arxiv.org/abs/2608.13637v2>. These are treated as manuscripts in this report.

10. Guth-Maynard, *New large value estimates for Dirichlet polynomials*, Annals203(2026),623-675. <https://annals.math.princeton.edu/2026/203-2/p06>.

11. Assani-Chester-Paschal, Integers26(2026),A86. <https://math.colgate.edu/~integers/aa86/aa86.pdf>.

12. Axler-Nicolas, *Large values of n/φ(n) and σ(n)/n*, Acta Arith.209(2023),357-383. <https://doi.org/10.4064/aa220705-12-10>; public author copy <http://math.univ-lyon1.fr/homes-www/nicolas/colsansHR.pdf>.

13. Bellotti-Wong, with appendix byFiori, *Improved estimates for the argument and zero-counting function of the Riemann zeta-function*, Math.Comp., electronically published2025-11-14. <https://doi.org/10.1090/mcom/4133>; <https://arxiv.org/html/2412.15470v2>. Earlier HSW: J.NumberTheory235(2022),219-241, <https://doi.org/10.1016/j.jnt.2021.06.032>.

14. Rosser-Schoenfeld, *Approximate formulas for some functions of prime numbers*, IllinoisJ.Math.6(1962),64-94, Theorem14. <https://doi.org/10.1215/ijm/1255631807>.

15. Axler, *Effective estimates for some functions defined over primes*, Integers24(2024),A34. <https://math.colgate.edu/~integers/y34/y34.pdf>.

16. trureturing, fixed commit9a201d9cb6089d7ec36fd2c2cdffbbd9797a2ae5. <https://github.com/the-omega-institute/trureturing/tree/9a201d9cb6089d7ec36fd2c2cdffbbd9797a2ae5>. Selected path/read-range and hash manifests accompany this report.

<a id="section-14"></a>

## 附录 A：强制来源更正：零点计数常数

Date: 2026-11-08 UTC. This addendum accompanies every R29 import of the frozen R28 proof. It is part of the proof contract, not an optional bibliographical note.

### Corrected published constant

The original printed Hasanalizade-Shen-Wong2022 Corollary1.2 displayed the additive constant9.3675. Bellotti-Wong, *Improved estimates for the argument and zero-counting function of the Riemann zeta-function*, Math. Comp., DOI10.1090/mcom/4133 (electronically published2025-11-14), explicitly corrects that value to **9.4925** in Table1 and its footnote. The publicly available author version is <https://arxiv.org/html/2412.15470v2>.

Accordingly, throughout the inherited R28 source step T1 use the corrected theorem

$$
\left|N(T)-\frac{T}{2\pi}\log\frac{T}{2\pi e}\right|
\le0.1038\log T+0.2573\log\log T+9.4925,
\quad T\ge e.
\tag{C1}
$$

R28’s frozen file is kept byte-for-byte for provenance; its displayed9.3675 is superseded by C1. No later conclusion relies on the difference between the two decimal constants.

### Re-establish the exact consumed R28 bound

For H=3·10<sup>12</sup> and T≥H, log T\>10\>9.4925, loglog T≤log T and2π\>6. Thus C1 implies

$$
N(T)<\left(\frac T6+1.3611\right)\log T<T\log T.
\tag{C2}
$$

The coefficient1.3611 is0.1038+0.2573+1. It is exactly the coarse coefficient already used in R28. Consequently the R28 high-zero bound

$$
\sum_{|\Im\rho|>H}(\Im\rho)^{-2}
\le4(\log H+1)/H<4\cdot10^{-11}
$$

and every analytic endpoint/budget downstream of it remain valid. The R28 kernel and interchange proof uses no additive zero-count constant elsewhere. Therefore the frozen R28 ordinary theorem is valid when read with this explicit source correction.

### Re-establish the sharper R29 bound

For the same T≥H,

$$
0.1038\log T+0.2573\log\log T+9.4925
\le(0.1038+0.2573+0.94925)\log T
=1.31035\log T<2\log T.
\tag{C3}
$$

All R29 high-tail integrations use only \| N−A\|≤2log T. Hence the3·10<sup>-12</sup> raw tail,1.501·10<sup>-12</sup> symmetry-weighted tail,2.81·10<sup>-14</sup> composed Robin budget and45-free conclusion are unchanged. The exact rational checker has been updated to test C3 with9.4925, and the independent reviewer reruns it separately.

### Stronger current result, kept distinct

Bellotti-Wong Theorem1.1 proves, for every T≥e,

$$
|N(T)-A(T)|\le0.10076\log T+0.24460\log\log T+8.08344,
$$

as well as a different small-constant alternative. This stronger theorem also implies C1 and C3. It is not necessary to optimize those constants to close the present45-free proof. The source search therefore must not call HSW2022 the latest bound.

This correction improves source accuracy. It is not a new number-theoretic gain, a new large computation, or an erasure of the unknown high-zero tail.

<a id="section-15"></a>

## 附录 B：统一指数与大小联动惩罚

Date: 2026-11-08. Status: ordinary proof independently checked within this research run. All large computations remain explicitly imported published inputs. No claim of historical priority, external peer review, Lean certification, or full RH is made.

### J0. Domain, inherited analytic input, and goal

All logarithms are natural. Let

$$
x_0=29\,996\,208\,012\,611,\qquad k_0=999\,999\,476\,056,
\qquad p_{k_0}=x_0,\qquad N_k=\prod_{j\le k}p_j.
$$

Write

$$
\theta(x)=\sum_{p\le x}\log p,\quad f(u)=\log\log u\quad(u>1),
\quad M(x)=-\sum_{p\le x}\log(1-p^{-1}),
$$

$$
E_\theta(x)=M(x)-\gamma-f(\theta(x)),\qquad
s(x)=\frac1{\sqrt x\log x},\quad L=\log x.
$$

The inherited R28 analytic lemma, proved there from the named published inputs with no global RH assumption, is the following all-real-x bound for every x≥x0:

$$
\begin{aligned}
E_\theta(x)\le{}&q_0+
\left(\frac1L+\frac1{L^2}\right)
\left(\frac{0.047}{\sqrt x}+4\cdot10^{-11}\right)\\
&+\frac{2.04}{\sqrt xL}+\frac{4.5}{x^{2/3}L}
+\frac{\log(2\pi)}{xL},
\qquad q_0=\frac{31}{1800\cdot99999^2}.
\end{aligned}
\tag{J1}
$$

Its proof is the frozen R28 T0-T22 / I1-I13 material, using the rigorously verified finite RH height H=3·10<sup>12</sup>, an unconditional summable high-zero tail, the Rosser-Schoenfeld prime-power correction, and the exact same-source identity Eθ=Q−Kθ−T<sub>2</sub>. J1 is a proved lemma to be included or imported with that proof, not an assumption inferred from numerical sampling.

The published finite-prefix input is that Robin holds for every 5040\<n≤N_k0, as explicitly consolidated in Axler 2023 Lemma 3 from Morrill-Platt.

The new work below establishes a **joint exponent-size penalty** that is absent from the old R_t(N_k) consumer. It then proves, using J1 and the published prefix, that every 38-free integer n\>5040 satisfies Robin.

### J1. An elementary common theta supplier at the square-root scale

Morrill-Platt 2021 Lemmas 2-3 give

$$
|\theta(y)-y|\le\frac{\sqrt y\log^2y}{8\pi}
\quad(599\le y\le B),\qquad B=2.169\cdot10^{25},
$$

$$
|\theta(y)-y|\le1.405\cdot10^{-10}y
\quad(\log y\ge55).
$$

These ranges overlap because e<sup>55</sup>\<B. Since log<sup>2</sup>y/√y decreases when log y\>4, and at y=5,000,000 one has log y\<16, √y\>2200 and π\>3,

$$
\frac{\log^2y}{8\pi\sqrt y}
<\frac{256}{24\cdot2200}<\frac1{200}.
$$

Consequently the following **uniform** supplier holds on the whole infinite range:

$$
\boxed{\frac{199}{200}y\le\theta(y)\le\frac{201}{200}y
\quad\text{for every }y\ge5\,000\,000.}
\tag{J2}
$$

The stronger inherited R28 bound remains available at the original scale:

$$
\theta(x)\le(1+10^{-5})x\qquad(x\ge x_0).
\tag{J3}
$$

No new prime enumeration is required for J2.

### J2. Canonical-prime compression retains the actual size constraint

Fix a positive integer n≥N_k0, and select k by N_k≤n\<N\_{k+1}; thus k≥k0. Set x=p_k. Suppose n is t-free, where the integer t≥9. If its distinct prime factors are q<sub>1</sub>\<⋯\<q_m with respective exponents a<sub>1</sub>,…,a_m, then m≤k: otherwise n≥∏\_{i≤m}q_i≥N\_{k+1}, a contradiction. Also q_i≥p_i.

Pad the exponent vector to length k by setting a_i=0 for m\<i≤k. In particular,

$$
0\le a_i\le t-1,\qquad
S_a:=\sum_{i\le k}a_i\log p_i\le S:=\log n,
\qquad \theta(x)=\log N_k\le S.
\tag{J4}
$$

The function h_a(u)=1+u<sup>-1</sup>+⋯+u<sup>-a</sup> is decreasing for u\>1 (constant when a=0). Thus

$$
\frac{\sigma(n)}n
\le\prod_{i\le k}h_{a_i}(p_i).
$$

Because f is increasing on (1,∞), J4 gives the valid upper bound

$$
\begin{aligned}
G(n)&:=\log\frac{\sigma(n)}{e^\gamma n\log\log n}\\
&\le E_\theta(x)+\sum_{p\le x}\log(1-p^{-(a_p+1)})
-\{f(\max(\theta(x),S_a))-f(\theta(x))\}.
\end{aligned}
\tag{J5}
$$

Here a_p denotes the corresponding padded exponent. In particular, one must not replace max(θ,S_a) by S_a when S_a\<θ, and one must not discard the numerator factor for a padded zero exponent.

Define

$$
d_{t,a}(p)=\log\frac{1-p^{-t}}{1-p^{-(a+1)}}\ge0,
$$

$$
\mathcal P_t(x,\mathbf a)=
\sum_{p\le x}d_{t,a_p}(p)
+f(\max(\theta(x),S_a))-f(\theta(x)).
\tag{J6}
$$

With τ_t(x)=−Σ\_{p\>x}log(1−p<sup>-t</sup>)≥0, Euler’s product changes J5 into

$$
\boxed{G(n)\le E_\theta(x)-\log\zeta(t)+\tau_t(x)
-\mathcal P_t(x,\mathbf a).}
\tag{J7}
$$

The old separated bound drops P_t. The following lemma shows that the exponents cannot simultaneously saturate its numerator and denominator relaxations.

### J3. A finite tangent budget for all exponent configurations

Set

$$
V=(1+10^{-5})x+3\sqrt x,\qquad \lambda=\frac1{V\log V}.
\tag{J8}
$$

For all x≥x0, L≥31 and √x≥5,400,000. If

$$
v=1+10^{-5}+\frac3{5\,400\,000}
=\frac{1\,800\,019}{1\,800\,000},
$$

then, by log(1+u)≤u,

$$
1<\frac{V\log V}{xL}
\le v\left(1+\frac{v-1}{31}\right)<\frac{1000}{999}.
$$

Hence

$$
\boxed{\frac{999}{1000xL}<\lambda<\frac1{xL}.}
\tag{J9}
$$

If S_a≤V, then

$$
f(\max(\theta,S_a))-f(\theta)
\ge\lambda(S_a-\theta).
\tag{J10}
$$

For S_a≤θ the right side is nonpositive and the left side is zero. For θ\<S_a≤V, integrate f′(u)=1/(u log u)≥λ on \[θ,S_a\]. Therefore

$$
\mathcal P_t\ge\sum_{p\le x} b_a(p),\qquad
b_a(p)=d_{t,a}(p)+\lambda(a-1)\log p.
\tag{J11}
$$

If instead S_a\>V, J3 and J9 give

$$
\mathcal P_t\ge f(V)-f(\theta)
\ge\lambda(V-\theta)
\ge3\lambda\sqrt x > \frac{2997}{1000}s(x).
\tag{J12}
$$

Thus the remaining proof concerns only the finite-tangent case S_a≤V.

### J4. Three elementary pointwise cases, including padded zeros

The following bounds hold for every p≤x and every 0≤a≤t−1 with t≥9.

**Nonnegativity for all p.** If a≥1, then b_a≥0. If a=0, then

$$
d_{t,0}(p)=\log(1+p^{-1}+\cdots+p^{-(t-1)})
\ge\log(1+p^{-1})\ge\frac1{p+1}.
$$

Since V≥x+2≥p+2 and λ log p≤1/V,

$$
b_0(p)\ge\frac1{p+1}-\frac1V
\ge\frac1{(p+1)(p+2)}>0.
\tag{J13}
$$

**Small primes: p≤(4/3)√x.** In this range

$$
\boxed{b_a(p)\ge\lambda\log p.}
\tag{J14}
$$

For a≥2 this follows from d≥0. For a=0, x≥16 implies p+1≤x/2. Thus d<sub>0</sub>≥2/x≥2λ log p, proving J14. For a=1,

$$
d_{t,1}(p)=\int_{p^{-t}}^{p^{-2}}\frac{du}{1-u}
\ge p^{-2}-p^{-t}
\ge\frac{127}{128p^2}>\frac{99}{100p^2},
\tag{J15}
$$

because t≥9. Meanwhile log(4/3)\<3/10 and L≥31 imply

$$
\lambda\log p
\le\frac{1/2+3/(10\cdot31)}x
=\frac{79}{155x}
<\frac{891}{1600x}
\le\frac{99}{100p^2}.
$$

This proves the a=1 case.

**Large primes: 2√x\<p≤x.** In this range

$$
\boxed{b_a(p)\ge\frac{99}{100p^2}.}
\tag{J16}
$$

For a=1 use J15. For a≥2, J9 gives

$$
b_a(p)\ge\lambda\log p>
\frac{999}{2000x}>
\frac{99}{400x}>\frac{99}{100p^2}.
$$

For a=0, J13 applies. Since p\>2√x≥10,800,000\>300 and $(p+1)(p+2)\le(100/99)p^2$ for p≥300, J16 follows. No support monotonicity or superabundance hypothesis is used.

### J5. A lower bound for the reciprocal-square prime tail

For y≥5,000,000 and x≥y, finite Abel summation gives

$$
\sum_{y<p\le x}\frac1{p^2}
=\frac{\theta(x)}{x^2\log x}
-\frac{\theta(y)}{y^2\log y}
+\int_y^x\theta(u)\frac{2\log u+1}{u^3\log^2u}\,du.
\tag{J17}
$$

Apply J2 to the positive terms and to the negative endpoint term with their correct directions. Writing I(y,x)=∫\_y^x du/(u<sup>2</sup> log u), the result simplifies exactly to

$$
\sum_{y<p\le x}p^{-2}
\ge\frac{199}{200}I(y,x)-\frac1{100y\log y}.
$$

Integration by parts gives

$$
I(y,\infty)\ge\frac{1-1/\log y}{y\log y},
\qquad I(x,\infty)\le\frac1{x\log x}.
$$

Consequently

$$
\sum_{y<p\le x}p^{-2}
\ge\frac{\frac{197}{200}-\frac{199}{200\log y}}{y\log y}
-\frac{199}{200x\log x}.
\tag{J18}
$$

Choose y=2√x. Then log y=L/2+log 2, log 2\<7/10, and L≥31. Hence

$$
\frac{197}{200}-\frac{199}{200\log y}\ge\frac{5709}{6200},
\qquad \frac{L}{2\log y}\ge\frac{155}{162},
$$

and J18 becomes the useful all-x bound

$$
\boxed{\sum_{2\sqrt x<p\le x}p^{-2}
\ge\left(\frac{1903}{2160}
-\frac{199}{200\cdot5\,400\,000}\right)s(x).}
\tag{J19}
$$

This is an analytic prime-sum lower bound, not a numerical prime table.

### J6. Uniform coupling theorem

Combining the disjoint small-prime and large-prime ranges J14/J16, the nonnegativity outside them, J2 and J9, and then J19, gives in the case S_a≤V

$$
\begin{aligned}
\mathcal P_t
&\ge\lambda\theta\!\left(\frac43\sqrt x\right)
+\frac{99}{100}\sum_{2\sqrt x<p\le x}p^{-2}\\
&\ge\left[
\frac{999}{1000}\frac{199}{200}\frac43
+\frac{99}{100}
\left(\frac{1903}{2160}-\frac{199}{200\cdot5\,400\,000}\right)
\right]s(x)\\
&=\frac{26\,370\,577\,811}{12\,000\,000\,000}s(x) > \frac{43}{20}s(x).
\end{aligned}
\tag{J20}
$$

The other case S_a\>V has the stronger J12 bound. Therefore:

> **Uniform coupling theorem.** For every real x≥x0 that is a prime endpoint, every integer t≥9, and every vector 0≤a_p≤t−1 indexed by p≤x, with P_t defined by J6, one has
>
> $$
> \boxed{\mathcal P_t(x,\mathbf a)\ge\frac{43}{20\sqrt x\log x}.}
> \tag{J21}
> $$

The same analytic inequality in fact holds for arbitrary real x≥x0 with the same finite prime indexing; prime endpoints are the consumer needed in J5-J7. The fixed coefficient 43/20 is deliberately conservative and is not claimed sharp.

### J7. Cancellation of the square-root-scale budget

Substitute J21 into J1 and J7. The terms proportional to s(x), including a safe upper bound for the cube-root and elementary correction, have coefficient at most

$$
\begin{aligned}
C_*&=\frac{51}{25}
+\frac{47}{1000}\frac{32}{31}
+\frac9{2\cdot170}
+\frac2{5\,400\,000}
-\frac{43}{20}\\
&=-\frac{49\,819\,873}{1\,422\,900\,000}<0.
\end{aligned}
\tag{J22}
$$

Here x0\>170<sup>6</sup> ensures x^(1/6)\>170, and log(2π)\<2 was already certified in R28. In particular, the term 4.5/(x^(2/3)L) is at most (9/340)s(x).

Since C\_\*\<0, discarding the resulting negative term leaves the uniform residual

$$
\begin{aligned}
E_\theta(x)-\mathcal P_t(x,\mathbf a)
&\le q_0+4\cdot10^{-11}\left(\frac1L+\frac1{L^2}\right)\\
&\le \mathcal B
:=\frac{31}{1800\cdot99999^2}
+\frac4{10^{11}}\frac{32}{31^2}\\
&=\frac{206\,369\,293\,759}
{67\,568\,961\,100\,507\,031\,250\,000}\\
&=3.054202556881571\ldots\cdot10^{-12}.
\end{aligned}
\tag{J23}
$$

This bound is three orders of magnitude smaller than the old separated endpoint budget because the dominant prime-power contribution is consumed jointly with the exponent/size penalty. The infinite high-zero budget has not been set to zero.

### J8. A complete 38-free integer consumer

For t=38 and x≥x0, the positive Euler tail satisfies

$$
0\le\tau_{38}(x)
\le2\sum_{m>\lfloor x\rfloor}m^{-38}
\le\frac2{37\lfloor x\rfloor^{37}}
\le\frac2{37(10^{13})^{37}}.
\tag{J24}
$$

The first inequality uses −log(1−u)≤2u for 0≤u≤1/2. Euler’s series and log(1+u)\>u−u<sup>2</sup>/2 give

$$
\log\zeta(38)>2^{-38}-2^{-77}.
\tag{J25}
$$

An exact rational comparison, reproduced by `verify_coupled_38_free.py`, gives

$$
\boxed{
(2^{-38}-2^{-77})-\mathcal B
-\frac2{37(10^{13})^{37}} > 5.8\cdot10^{-13}>0.
}
\tag{J26}
$$

Its decimal value is 5.83776250203524…·10<sup>-13</sup>, only for display.

For every 38-free n≥N_k0, canonical-prime compression J4-J7 and J23-J26 therefore imply

$$
\log\frac{\sigma(n)}{e^\gamma n\log\log n}
<-5.8\cdot10^{-13}<0.
$$

The published finite-prefix theorem covers every remaining 5040\<n≤N_k0. The two ranges cover every 38-free n\>5040. Thus:

> **38-free corollary.** Subject to the explicitly cited published inputs and the inherited, fully proved R28 analytic lemma J1, every 38-free integer n\>5040 satisfies Robin’s inequality.

The strict quantitative margin above applies to the tail n≥N_k0; no such common margin is asserted for the imported finite prefix.

### J9. Scope and comparison

1.  Relative to the checked published 21-free comparator, this ordinary corollary allows prime exponents up to 37 rather than 20: +17 levels. Relative to R28’s 26-free consumer, the increase is +12 levels. This is a comparison of named t-free families, not a claim about the union of all previously known integer families.

2.  J23 retains the nonzero high-zero contribution. It does not prove an RH-equivalent critical-scale bound, nor full RH.

3.  The conservative residual B is already larger than log ζ(39), so **this exact numerical consumer** does not establish 39-free. A sharper legitimate Q supplier or high-zero tail could change that conclusion. The failure is not a counterexample to 39-free.

4.  The tangent budget and prime-sum argument are ordinary mathematical estimates with classical antecedents; no priority claim is made. A source audit must separately check whether this precise t-free corollary is already known.

5.  Zero exponents, S_a\<θ, all-x coverage, and original-integer reconstruction are essential parts of the proof. Omitting them would invalidate a claim about all t-free integers.

### Sources and exact dependencies

- T. Morrill and D. J. Platt, *Robin’s inequality for 20-free integers*, Integers 21 (2021), A28: Lemmas 1-3, Theorem 5 and Corollary 2. <https://math.colgate.edu/~integers/v28/v28.pdf>.

- C. Axler, *On Robin’s inequality*, Ramanujan Journal 61 (2023), 909-919: Lemma 3 for the exact published finite prefix; Theorem 1 is the published 21-free comparison. <https://link.springer.com/article/10.1007/s11139-022-00683-0>.

- R28 `proofs/finite_height_26_free.md`, frozen SHA256 `616331d41ce00fb5bc361610be8a242b5d87eca0c03c54463a8ec98b2c23b645`: analytic lemma T16 is J1. The full dependencies include Platt-Trudgian finite RH, Hasanalizade-Shen-Wong counting, Rosser-Schoenfeld prime-power bounds, and classical Hadamard / integrated explicit formulae. This is an internally checked ordinary proof, not an external published paper.

- R28 `proofs/psi1_kernel_interchange.md`, frozen SHA256 `13c385157e920434392a2b378c1c3f47edfa2a0b45cac2f24959a6424c30cdd5`: preserves the full zero-series interchange and signs used by J1.

<a id="section-16"></a>

## 附录 C：高零点配对与45-free完整闭合

Date: 2026-11-08 UTC. Status at writing: ordinary proof submitted for independent internal review. This text uses named published theorems, the two complete R28 analytic proofs, and the R29 uniform coupling proof. No global RH hypothesis, external unreviewed manuscript theorem, or experimental prime table is an input. It does not claim journal review, a Lean proof, historical priority, or a solution of full RH.

### S0. Exact import contract

Every logarithm is natural. Put

$$
x_0=29\,996\,208\,012\,611,\quad k_0=999\,999\,476\,056,
\quad p_{k_0}=x_0,\quad N_k=\prod_{j\le k}p_j,
\quad H=3\cdot10^{12},\quad L=\log x.
$$

Write $\theta(x)=\sum_{p\le x}\log p$, $\psi(x)=\sum_{p^m\le x}\log p$, and

$$
E_\theta(x)=-\sum_{p\le x}\log(1-p^{-1})-\gamma-\log\log\theta(x).
$$

The frozen R28 proofs supply the exact same-source identity and its explicit-formula consequence, for every real x≥x0:

$$
E_\theta=Q-K_\theta-T_2,
\quad Q=r(x)^2\int_0^1(1-s)w(x+sr(x))\,ds,
\tag{S1}
$$

where r=θ−x, w(u)=(log u+1)/(u<sup>2</sup>log<sup>2</sup>u), $K_\theta=\int_x^\infty r(u)w(u)\,du$ and $T_2=\sum_{p>x,m\ge2}(mp^m)^{-1}\ge0$. In particular,

$$
E_\theta(x)\le Q(x)+|Z(x)|+
\frac{2.04}{\sqrt xL}+\frac{4.5}{x^{2/3}L}
+\frac{\log(2\pi)}{xL}.
\tag{S2}
$$

Here Z=ΣρFρ(x)/ρ, $F_z(x)=\int_x^\infty u^zw(u)\,du$, with all nontrivial zeros counted with multiplicity. The full $\psi_1$ argument in the inherited kernel proof justifies the convergent weighted zero sum, endpoint terms and exchanges of integration. Its estimate is

$$
\left|\frac{F_\rho(x)}\rho\right|
\le x^{\beta-1}\left\{\frac1{|\rho(1-\rho)|L}
+\frac1{|1-\rho|^2L^2}\right\}.
\tag{S3}
$$

Platt-Trudgian’s published computation puts every zero with \| Imρ\|≤H on Reρ=1/2. The unconditional Hadamard identity, with each real paired summand positive, gives the low-zero bound

$$
|Z_{\le H}(x)|\le
\left(\frac1L+\frac1{L^2}\right)\frac{B_0}{\sqrt x},
\qquad B_0=2+\gamma-\log(4\pi)<0.047.
\tag{S4}
$$

No assertion about the real part of a zero above H has been made.

The frozen R29 coupling proof `coupled_38_free.md`, J4-J21, supplies for every t≥9, every t-free n≥N_k0, and k chosen by Nk≤n\<Nk+1 (x=pk),

$$
G(n):=\log\frac{\sigma(n)}{e^\gamma n\log\log n}
\le E_\theta(x)-\log\zeta(t)+\tau_t(x)-\mathcal P_t(x,\mathbf a),
\tag{S5}
$$

$$
\mathcal P_t(x,\mathbf a)\ge\frac{2.15}{\sqrt xL},
\qquad 0\le\tau_t(x)\le\frac2{(t-1)\lfloor x\rfloor^{t-1}}.
\tag{S6}
$$

The vector a uses canonical prime compression and padded zeros, and retains max(θ,Σa_p log p). Thus S5 applies to every such original integer, including missing primes; it is not restricted to superabundant or consecutive-support integers.

Finally, Morrill-Platt’s published finite prefix, in the exact form recorded by Axler 2023 Lemma 3, covers every integer 5040\<n≤N_k0. This is an imported published computation, not a computation rerun here.

### S1. Count the high zeros before discarding the boundary term

Let N(T) count, with multiplicity, zeros satisfying 0\<Imρ≤T, and set

$$
A(T)=\frac{T}{2\pi}\log\frac{T}{2\pi e}.
$$

Hasanalizade-Shen-Wong 2022 Corollary 1.2, with its additive constant corrected in Bellotti-Wong 2025 Table 1 and its footnote, gives for T≥e,

$$
|N(T)-A(T)|\le0.1038\log T+0.2573\log\log T+9.4925.
\tag{S7}
$$

For T≥H, log T\>10 and log log T≤log T. Hence its right side is less than 2log T. This is a deliberately weaker consequence of a published estimate; no assertion that S7 is the latest counting bound is needed. The original HSW printed constant9.3675 is not used. The mandatory companion `zero_count_source_correction.md` also patches the source quotation in the frozen R28 text: its consumed bound N(T)≤Tlog T and every later R28 constant remain valid with9.4925.

Since N(T)=O(Tlog T), Stieltjes integration gives the exact convergent identity

$$
\mathcal T_H:=\sum_{|\Im\rho|>H}\frac1{(\Im\rho)^2}
=-\frac{2N(H)}{H^2}+4\int_H^\infty\frac{N(T)}{T^3}\,dT.
\tag{S8}
$$

The endpoint count includes zeros at H, so S8 excludes them from the tail. Use the lower bound for N(H) and the upper bound for N(T) inside the integral. Elementary integration yields

$$
\boxed{\mathcal T_H\le
\frac{\log H-\log(2\pi)+1}{\pi H}
+\frac{8\log H+2}{H^2}<3\cdot10^{-12}.}
\tag{S9}
$$

For the strict numerical inequality, log H\<29, log(2π)\>1.8 and π\>3.14 give the rational upper bound

$$
\frac{28.2}{3.14H}+\frac{234}{H^2}<3\cdot10^{-12}.
$$

The logarithmic inequalities are checked by finite Taylor bounds in the companion certificate (and independently with Arb); π\>3.14 is an elementary classical bound. Keeping −2N(H)/H<sup>2</sup> in S8 is essential for this improvement over R28’s coarse 4·10<sup>-11</sup> budget.

### S2. Functional-equation symmetry halves the worst weighted tail

The multiset of nontrivial zeros is invariant under $\rho\mapsto1-\bar\rho$, including multiplicity and the absolute-height restriction. For x≥1 and 0≤β≤1, convexity in β gives

$$
x^{\beta-1}+x^{-\beta}\le1+x^{-1}.
\tag{S10}
$$

Consequently, by nonnegative absolute convergence,

$$
\begin{aligned}
\sum_{|\Im\rho|>H}\frac{x^{\beta-1}}{(\Im\rho)^2}
&=\frac12\sum_{|\Im\rho|>H}
\frac{x^{\beta-1}+x^{-\beta}}{(\Im\rho)^2}\\
&\le\frac{1+x^{-1}}2\mathcal T_H
<1.501\cdot10^{-12}\qquad(x\ge x_0).
\end{aligned}
\tag{S11}
$$

Both denominators in S3 are at least (Imρ)<sup>2</sup> in the needed sense: \| ρ(1−ρ)\|≥(Imρ)<sup>2</sup> and \|1−ρ\|<sup>2</sup>≥(Imρ)<sup>2</sup>. Combining S4 and S11,

$$
\boxed{|Z(x)|\le\left(\frac1L+\frac1{L^2}\right)
\left(\frac{0.047}{\sqrt x}+1.501\cdot10^{-12}\right).}
\tag{S12}
$$

The high-zero contribution has been bounded, not made zero. S10 uses the functional equation, not RH.

### S3. A sharper quadratic Taylor remainder

Put a=99999/100000 and ε=1/1000. The already proved uniform θ bound gives θ(x)≥ax for x≥x0, and −log a≤(1−a)/a\<ε. The positive function w is decreasing on (1,∞). Thus, if \| r(x)\|≤δ(x)x, S1 gives

$$
0\le Q(x)\le\frac{\delta(x)^2}{2a^2}
\frac{L-\varepsilon+1}{(L-\varepsilon)^2}.
\tag{S13}
$$

Indeed, the whole Taylor segment lies above ax, and the function (u+1)/u<sup>2</sup> decreases for u\>0.

Axler 2024, *Effective estimates for some functions defined over primes*, Proposition 1, gives the published all-x bound

$$
|\theta(x)-x|<\frac{0.024334\,x}{\log^3x}
\quad\text{for }x\ge1\,757\,126\,630\,797<x_0.
\tag{S14}
$$

Hence, for L≥log x0\>31,

$$
Q(x)\le q_A(L):=
\frac{0.024334^2}{2a^2L^6}
\frac{L-\varepsilon+1}{(L-\varepsilon)^2}.
\tag{S15}
$$

For L≥55, Morrill-Platt’s published global relative bound δ_B=1.405·10<sup>-10</sup> supplies an alternative that is substantially smaller near L=55

$$
Q(x)\le q_B(L):=
\frac{(1.405\cdot10^{-10})^2}{2a^2}
\frac{L-\varepsilon+1}{(L-\varepsilon)^2}.
\tag{S16}
$$

The two ranges cover everything needed. Both q_A and q_B are positive and decreasing on L≥31. Finite numerical obligations do not replace these all-real-variable monotonicity arguments.

### S4. Retain the signed coupling surplus

Since x0\>170<sup>6</sup>, √x0\>5,400,000, L\>31 and log(2π)\<2, S2, S6 and S12 give

$$
\begin{aligned}
E_\theta(x)-\mathcal P_t(x,\mathbf a)
\le{}&Q(x)+1.501\cdot10^{-12}\left(\frac1L+\frac1{L^2}\right)\\
&+\left[\frac{51}{25}+\frac{47}{1000}\frac{32}{31}
+\frac9{340}+\frac2{5\,400\,000}-\frac{43}{20}\right]
\frac1{\sqrt xL}.
\end{aligned}
$$

The bracket is exactly −49,819,873/1,422,900,000\<−0.035. Define

$$
h(L)=1.501\cdot10^{-12}(L^{-1}+L^{-2}),
\qquad g(L)=0.035\,e^{-L/2}/L.
$$

We have proved the signed bound

$$
\boxed{E_\theta(x)-\mathcal P_t(x,\mathbf a)
\le q_A(L)+h(L)-g(L)}
\quad(L\ge\log x_0),
\tag{S17}
$$

and q_A can be replaced by q_B when L≥55. Every function q_A,h,g decreases on L≥31, but their difference need not. The next step therefore does not assume that the signed difference is monotone.

### S5. Six finite intervals plus one analytic infinite tail

For any interval \[u,v\] contained in \[31,55\], separate monotonicity gives

$$
q_A(L)+h(L)-g(L)\le q_A(u)+h(u)-g(v).
\tag{S18}
$$

For L≥55, discard the negative term and use

$$
q_B(L)+h(L)-g(L)\le q_B(55)+h(55).
\tag{S19}
$$

The complete interval cover and resulting upper bounds are:

| L interval | Upper bound, displayed approximately |
|:-----------|:-------------------------------------|
| \[31,45\]  | −7.0501750053·10<sup>-14</sup>       |
| \[45,50\]  | 2.5185207524·10<sup>-14</sup>        |
| \[50,52\]  | 2.7568157005·10<sup>-14</sup>        |
| \[52,53\]  | 2.7667635490·10<sup>-14</sup>        |
| \[53,54\]  | 2.7893698904·10<sup>-14</sup>        |
| \[54,55\]  | 2.7810823298·10<sup>-14</sup>        |
| \[55,∞)    | 2.7787107621·10<sup>-14</sup>        |

These are rounded displays of exact rational upper bounds, not tests at sample points. To obtain the finite rational bound for g(v), for z=v/2 and N=256 use

$$
e^z\le U_N(z):=
\sum_{j=0}^{N}\frac{z^j}{j!}
+\frac{z^{N+1}}{(N+1)!}\frac1{1-z/(N+2)}.
\tag{S20}
$$

The tail ratio is bounded by z/(N+2)\<1. Thus g(v)≥0.035/\[vU_N(v/2)\]. Every comparison in the table and the uniform conclusion is a finite exact rational comparison. In particular,

$$
\boxed{E_\theta(x)-\mathcal P_t(x,\mathbf a)<2.81\cdot10^{-14}
\quad(x\ge x_0,\ t\ge9).}
\tag{S21}
$$

The companion `verify_45_free.py` records the exact fractions, rather than relying on printed decimals. Arb independently encloses the same calculations and the elementary transcendental constants.

### S6. Original-integer closure for 45-free numbers

Euler’s series and log(1+u)\>u−u<sup>2</sup>/2 give

$$
\log\zeta(45)>2^{-45}-2^{-91}.
$$

For x≥x0\>10<sup>13</sup>, S6 gives τ<sub>45</sub>(x)≤2/\[44(10<sup>13</sup>)<sup>44</sup>\]. A final exact rational comparison is

$$
\boxed{2^{-45}-2^{-91}
-\frac2{44\cdot10^{572}}-2.81\cdot10^{-14} > 3.2\cdot10^{-16}>0.}
\tag{S22}
$$

It follows from S5 that every 45-free n≥N_k0 has

$$
G(n)<-3.2\cdot10^{-16}<0.
$$

The imported published finite-prefix theorem covers every 5040\<n≤N_k0. Hence the two ranges establish the ordinary mathematical conclusion:

> **45-free theorem.** Every positive integer n\>5040 that is not divisible by the 45th power of any prime satisfies
>
> $$
> \sigma(n)<e^\gamma n\log\log n.
> $$

The quantitative common log margin above belongs to the tail n≥N_k0; it is not asserted for the published finite prefix. The ordinary proof uses the displayed identities, inequalities, and published inputs; the finite certificate verifies only its explicit arithmetic obligations.

### S7. Boundaries and comparison

- The named published t-free comparator located in the bounded source search is Axler’s 21-free theorem (2023), also reproved in Assani-Chester-Paschal 2026. The present ordinary proof permits exponents through 44 instead of 20: +24 levels. Relative to the internally checked R28 26-free theorem, the change is +19 levels. Neither is a percentage of RH proved or an established publication record.

- The new global bound 2.81·10<sup>-14</sup> is for **Eθ−P_t**, whereas R28’s 1.243668…·10<sup>-8</sup> bound was for **Eθ**. Their ratio describes improvement of this composed sufficient test, not an improvement of the same bare analytic remainder. The joint coupling must not be dropped from the interpretation.

- S19 at55 exceeds log ζ(46). Therefore this particular complete interval certificate does not establish46-free. No counterexample to46-free is asserted.

- The positive high-zero contribution remains. As t grows, log ζ(t)→0; the fixed45 certificate does not pass uniformly to all t and proves no full RH result.

- Axler-Nicolas2023 already contains a negative square-root correction in a published all-integer divisor envelope. The general idea of keeping exponent/size losses and correcting the main term has classical antecedents; this proof claims neither invention of that mechanism nor historical priority.

### Sources and frozen analytic dependencies

1.  Platt-Trudgian, *The Riemann hypothesis is true up to 3·10<sup>12</sup>*, Bulletin of the London Mathematical Society53(2021),792-797, DOI10.1112/blms.12460. Published finite height; not replayed.

2.  Hasanalizade-Shen-Wong, *Counting zeros of the Riemann zeta function*, Journal of Number Theory235(2022),219-241, Corollary1.2, DOI10.1016/j.jnt.2021.06.032. Author-hosted published text: <https://www-math.nsysu.edu.tw/~pjwong/stuff/CountingRiemannZeros.pdf>.

3.  Axler, *Effective estimates for some functions defined over primes*, Integers24(2024),A34, Proposition1: <https://math.colgate.edu/~integers/y34/y34.pdf>.

4.  Morrill-Platt, *Robin’s inequality for20-free integers*, Integers21(2021),A28, Lemmas1-3 and Corollary2: <https://math.colgate.edu/~integers/v28/v28.pdf>.

5.  Axler, *On Robin’s inequality*, Ramanujan Journal61(2023),909-919, Lemma3 and Theorem1, DOI10.1007/s11139-022-00683-0.

6.  R28 `finite_height_26_free.md`, SHA256 `616331d41ce00fb5bc361610be8a242b5d87eca0c03c54463a8ec98b2c23b645`, and `psi1_kernel_interchange.md`, SHA256 `13c385157e920434392a2b378c1c3f47edfa2a0b45cac2f24959a6424c30cdd5`: full analytic derivations included in the R29 package.

7.  R29 `coupled_38_free.md`, SHA256 `5c555eefbc0b863ba846505e88933174721f0b18e425906502a1890e41dd4267`: the uniform exponent-size penalty, arbitrary-integer transfer, and initial38-free consequence.

8.  Bellotti-Wong, with an appendix by Fiori, *Improved estimates for the argument and zero-counting function of the Riemann zeta-function*, Mathematics of Computation, electronically published2025-11-14, DOI10.1090/mcom/4133; author version <https://arxiv.org/html/2412.15470v2>, Theorem1.1 and Table1 footnote. This corrects the older HSW additive constant and also supplies a stronger counting estimate. Only the corrected coarse consequence is needed here.

<a id="section-17"></a>

## 附录 D：同一45-free结论的全局凸性收尾

Date: 2026-11-08 UTC. This is an alternative ordinary closing argument for the already derived 45-free theorem. It keeps the same headline residual bound $2.81\cdot10^{-14}$, the same prefix, and the same original-integer transfer. It neither asserts a new theorem beyond that conclusion nor optimizes any constant.

The purpose is to remove the dependency on Axler 2024 Proposition 1 from the curvature estimate and replace the six finite interval calculations by one global exponential tangent inequality. The published zero verification, counting theorem, Morrill–Platt bounds, and finite Robin prefix remain explicit inputs.

### A0. Exact shared input

Let $x\ge x_0=29\,996\,208\,012\,611$, $L=\log x>31$,

$$
s(x)=\frac1{\sqrt x L},\qquad
a=\frac{99999}{100000},\qquad
R=2.81\cdot10^{-14},\quad A=1.501\cdot10^{-12},\quad c=0.034.
$$

The R28 kernel and exact Taylor identity, the R29 coupling theorem, and the high-zero counting/pairing argument in S1–S2 of `joint_45_free.md` jointly give

$$
E_\theta(x)-\mathcal P_t(x,\mathbf a)
\le Q(x)+A\left(\frac1L+\frac1{L^2}\right)+C_*s(x),
\tag{A1}
$$

$$
C_*=-\frac{49\,819\,873}{1\,422\,900\,000}<-0.035,
\qquad t\ge9,
$$

where $Q=r^2\int_0^1(1-u)w(x+ur)\,du$, $r=\theta(x)-x$, and $w(v)=(\log v+1)/(v^2\log^2v)$. Those particular shared lemmas precede the Axler 2024 curvature input and do not depend on it. They retain the positive unknown high-zero contribution A.

The inherited R28 estimate gives $\theta(x)\ge ax$ on the full range. Morrill–Platt 2021 Lemmas 2–3 give

$$
|r(x)|\le\frac{\sqrt x L^2}{8\pi}
\quad(599\le x\le B),\qquad B=2.169\cdot10^{25},
\tag{A2}
$$

$$
|r(x)|\le\delta_B x,
\quad \delta_B=1.405\cdot10^{-10}
\quad(L\ge55).
\tag{A3}
$$

The ranges overlap because $e^{55}<B$. No new θ theorem or prime enumeration is used below.

### A1. Absorb curvature on the complete range up to L=55

Suppose $x\ge x_0$ and $L\le55$. Then A2 applies. The whole Taylor segment is at least ax, and w decreases. Also $-\log a<1$, so $\log(ax)>L-1$. Hence

$$
\begin{aligned}
Q(x)&\le\frac{r(x)^2}{2}w(ax)\\
&\le\frac{L^4}{128\pi^2a^2x}
\frac{L+1}{(L-1)^2}\\
&<\frac{L^3}{x}
\frac{L(L+1)}{1152a^2(L-1)^2}
<\frac{L^3}{1000x}.
\end{aligned}
\tag{A4}
$$

The last inequality holds for every L≥31: the function $L(L+1)/(L-1)^2$ decreases on L\>1, and the exact endpoint comparison is

$$
\frac{31\cdot32}{1152a^2\cdot30^2}<\frac1{1000}.
\tag{A5}
$$

Divide A4 by s(x). The function $L^4e^{-L/2}$ decreases for L\>8. The elementary bounds $e>27/10$ and $\sqrt e>8/5$ give the exact rational comparison

$$
e^{31/2}>(27/10)^{15}(8/5)>5\cdot31^4.
\tag{A6}
$$

Consequently

$$
\frac{Q(x)}{s(x)}<\frac{L^4e^{-L/2}}{1000}
\le\frac{31^4e^{-31/2}}{1000}<\frac1{5000}.
\tag{A7}
$$

Since the exact rational coefficient satisfies $`C_*+1/5000<-c`$, A1 becomes

$$
E_\theta-\mathcal P_t
< A(L^{-1}+L^{-2})-c\frac{e^{-L/2}}L
\qquad(\log x_0\le L\le55).
\tag{A8}
$$

This is an all-x absorption of the same-source quadratic remainder. It is not a small-error assertion based on a few endpoints.

### A2. One exponential tangent inequality replaces all finite boxes

Two exact rational comparisons are

$$
2R(68/25)^{27}<c,
\qquad A\frac{32}{31}<56R.
\tag{A9}
$$

The elementary series bound $e<68/25$ gives $c>2Re^{27}$. For every real L, the convexity inequality $e^u\ge1+u$ with $u=(54-L)/2$ therefore yields

$$
c e^{-L/2} > 2R e^{(54-L)/2}
\ge R(56-L).
\tag{A10}
$$

For L≥31,

$$
\begin{aligned}
L\left[A(L^{-1}+L^{-2})-c\frac{e^{-L/2}}L\right]
&=A(1+1/L)-c e^{-L/2}\\
&\le A\frac{32}{31}-c e^{-L/2}\\
&<56R-R(56-L)=RL.
\end{aligned}
\tag{A11}
$$

Division by L\>0 proves that the right side of A8 is strictly less than R, uniformly throughout its complete range. The argument does not assume monotonicity of a signed difference. It uses a single global convexity inequality instead of a finite interval cover.

### A3. Close the remaining infinite range with the global θ bound

For L≥55 use A3. Since $-\log a<(1-a)/a<1/1000$, put $\varepsilon=1/1000$. The Taylor segment bound gives

$$
Q(x)\le\frac{\delta_B^2}{2a^2}
\frac{L-\varepsilon+1}{(L-\varepsilon)^2}
\le\frac{\delta_B^2}{2a^2}
\frac{56-\varepsilon}{(55-\varepsilon)^2}
<10^{-21}.
\tag{A12}
$$

Discarding the negative $`C_*s`$ in A1 and using monotonicity of the positive high-zero term gives, on this entire infinite range,

$$
E_\theta-\mathcal P_t
<10^{-21}+A\frac{56}{3025}
<R.
\tag{A13}
$$

Together A11 and A13 prove precisely the existing headline bound

$$
\boxed{E_\theta(x)-\mathcal P_t(x,\mathbf a)
<2.81\cdot10^{-14}\qquad(x\ge x_0,\ t\ge9).}
\tag{A14}
$$

There is no uncovered boundary at L=55. The global θ supplier is used only in its published range.

### A4. The unchanged 45-free consumer

The audited canonical-prime compression gives

$$
\log\frac{\sigma(n)}{e^\gamma n\log\log n}
\le E_\theta-\mathcal P_{45}-\log\zeta(45)+\tau_{45}
$$

for every 45-free n≥N_k0. As before,

$$
\log\zeta(45)>2^{-45}-2^{-91},\qquad
\tau_{45}\le\frac2{44\cdot10^{572}},
$$

and the exact inequality

$$
2^{-45}-2^{-91}-\frac2{44\cdot10^{572}}-R > 3.2\cdot10^{-16}
\tag{A15}
$$

gives the same strict tail margin. The same published finite prefix fills 5040\<n≤N_k0. Thus this alternative closes the same 45-free result with the same headline constants and without using Axler 2024 Proposition 1.

### Finite certificate and remaining source obligations

`verify_mp_curvature_alternative.py` verifies A5, A6, A9, A12, A13, A15 and the elementary exponential brackets using exact rational arithmetic. For e it uses the lower series through degree 4 and an upper series through degree 6 with its geometric remainder. These arithmetic checks complement the derivative, convexity, and all-integer proofs; they do not replace them.

Sources retained:

- Morrill–Platt, *Robin’s inequality for 20-free integers*, *Integers* 21 (2021), A28, Lemmas 1–3 and the published finite prefix: <https://math.colgate.edu/~integers/v28/v28.pdf> .

- Axler 2023, Lemma 3, remains the cited precise formulation of that finite prefix; the removed source dependency is specifically **Axler 2024 Proposition 1**.

- The R28 kernel proof and R29 high-zero pairing lemma retain Platt–Trudgian’s finite-height verification, Hasanalizade–Shen–Wong’s zero count, Rosser–Schoenfeld’s prime-power estimate, and the standard integrated explicit formula and Hadamard identity.

- The R29 coupling theorem remains essential, including its padded-zero and max(θ,S_a) transfer to the original integer.

The alternative changes the curvature supplier and scalar closure only. It makes no stronger integer claim, no new large computation, no world-record claim, and no full RH claim.

<a id="section-18"></a>

## 附录 E：局部素数条件与联合缺陷

Date: 2026-11-08 UTC. Status: ordinary derivation from the frozen R28 analytic theorem and the named published finite prefix; submitted for independent internal review. No full RH or publication-priority claim is made. These statements concern all possible Robin counterexamples, not only the least one.

### L0. A uniform imported bound, with its numerical provenance

Let x0=29,996,208,012,611, k0=999,999,476,056, p_k0=x0 and Nk=∏\_{j≤k}p_j. As in the R28 proof, define

$$
M_k=\prod_{j\le k}(1-p_j^{-1})^{-1},
\qquad E_\theta(p_k)=\log M_k-\gamma-\log\log\theta(p_k).
$$

The R28 all-x spectral envelope is decreasing and at x0 is

$$
C_0=1.243668062349108\ldots\cdot10^{-8}<C:=1.244\cdot10^{-8}.
\tag{L1}
$$

The exact formula is recorded and reevaluated with certified Arb enclosures in `verify_45_free.py`. For reproducibility it is

$$
\begin{aligned}
C_0={}&\frac{31}{1800\cdot99999^2}
+\left(\frac1{\log x_0}+\frac1{\log^2x_0}\right)
\left(\frac{2+\gamma-\log(4\pi)}{\sqrt{x_0}}
+\frac{4(\log H+1)}H\right)\\
&+\frac{2.04}{\sqrt{x_0}\log x_0}
+\frac{4.5}{x_0^{2/3}\log x_0}
+\frac{\log(2\pi)}{x_0\log x_0},\qquad H=3\cdot10^{12}.
\end{aligned}
\tag{L2}
$$

Thus Eθ(x)≤C0\<C for all x≥x0. This uses the tighter certified endpoint, not the coarser R28 rational envelope1.26405…·10<sup>-8</sup>, which would not justify the round cutoff80,000,000 below.

### L1. Preserve one actual local factor

Suppose n\>N_k0 and select k by Nk≤n\<Nk+1. Its number of distinct prime factors is at most k, and log n≥θ(p_k). Fix a prime p≤x0 and put a=ν_p(n). If a≥1, the Euler factors give

$$
\frac{\sigma(n)}n
\le(1-p^{-a-1})\prod_{q\mid n}(1-q^{-1})^{-1}
\le(1-p^{-a-1})M_k.
\tag{L3}
$$

If a=0, the largest product of at most k Euler factors avoiding p uses the first k+1 primes with p removed. Because p≤x0≤p_k,

$$
\frac{\sigma(n)}n
\le M_k\frac{1-p^{-1}}{1-p_{k+1}^{-1}}.
\tag{L4}
$$

Consequently the following single bound holds in both cases (with an unnecessary but harmless correction when a≥1):

$$
G(n)\le E_\theta(p_k)+\log(1-p^{-a-1})
-\log(1-p_{k+1}^{-1}).
\tag{L5}
$$

Since −log(1-u)≤u/(1-u), the next prime p\_{k+1}\>x0, and −log(1-u)≥u,

$$
G(n)< C+\frac1{x_0-1}-p^{-a-1}.
\tag{L6}
$$

An exact rational comparison gives

$$
C+\frac1{x_0-1}<\frac1{80\,000\,000}.
\tag{L7}
$$

If p^{a+1}≤80,000,000, then p≤80,000,000\<x0, so all conditions apply and L6 is strictly negative. The published finite-prefix theorem covers every other integer5040\<n≤N_k0. We have therefore proved:

> **Local prime-power corollary.** If n\>5040 and there is a prime p such that
>
> $$
> p^{\nu_p(n)+1}\le80\,000\,000,
> $$
> then Robin’s inequality holds at n. All other prime exponents may be arbitrary.

An equivalent necessary restriction on every possible Robin counterexample is

$$
\boxed{\operatorname{lcm}(1,2,\ldots,80\,000\,000)\mid n.}
\tag{L8}
$$

Indeed, failure of the local sufficient condition forces ν_p(n)≥$\lfloor$log(80,000,000)/log p$\rfloor$ for every p≤80,000,000. These are exactly the exponents in that least common multiple. No decimal rounding of logarithms is needed to interpret L8.

Examples of sufficient conditions, any one of which is enough, are

| Prime                  | Sufficient exponent restriction |
|:-----------------------|:--------------------------------|
| 2                      | ν<sub>2</sub>(n)≤25             |
| 3                      | ν<sub>3</sub>(n)≤15             |
| 5                      | ν<sub>5</sub>(n)≤10             |
| 7                      | ν<sub>7</sub>(n)≤8              |
| 11 or13                | ν_p(n)≤6                        |
| 17 or19                | ν_p(n)≤5                        |
| any prime23≤p≤37       | ν_p(n)≤4                        |
| any prime41≤p≤89       | ν_p(n)≤3                        |
| any prime97≤p≤421      | ν_p(n)≤2                        |
| any prime p≤80,000,000 | p does not divide n             |

These examples are checked by integer powers. For example431<sup>3</sup>=80,062,991 exceeds the cutoff and is deliberately excluded from the displayed ν_p≤2 row.

### L2. Several local factors share one budget

If a finite set P of primes all divide n, L3 generalizes without any support correction:

$$
\boxed{G(n)\le E_\theta(p_k)-\sum_{p\in P}d_p(n),
\qquad d_p(n)=-\log(1-p^{-\nu_p(n)-1}).}
\tag{L9}
$$

Thus a potential counterexample must satisfy Σ\_{p∈P}d_p(n)≤C0 for every such set. For small primes whose absence is already excluded by L8, there is no hidden divisibility hypothesis.

For instance, the conjunction

$$
\nu_2(n)\le26\quad\text{and}\quad\nu_3(n)\le16
$$

is sufficient for Robin, because

$$
2^{-27}+3^{-17}=1.519\ldots\cdot10^{-8}>C.
\tag{L10}
$$

If either prime is missing, L8’s local corollary already proves Robin. If both divide n, L9 and −log(1-u)≥u prove it. Another sufficient conjunction is

$$
\nu_2(n)\le26,\quad\nu_3(n)\le17,\quad\nu_5(n)\le11,
$$

since 2<sup>-27</sup>+3<sup>-18</sup>+5<sup>-12</sup>\>C. These are intersections of upper-exponent conditions, not claims that each listed bound separately suffices. All other prime exponents remain unrestricted.

### L3. Scope of improvement

The named published comparisons are Axler2023 ν<sub>2</sub>≤20 and ν<sub>5</sub>≤8, Hertlein2018 ν<sub>3</sub>≤12 and ν<sub>7</sub>≤6, and Vega2022 absence of a prime≤1,771,559. Relative to these named all-integer families, the new sufficient caps add5,3,2,2 exponent levels for2,3,5,7, respectively; the missing-prime ceiling increases by the factor80,000,000/1,771,559≈45.16. A bounded current literature search is not a proof of worldwide priority.

These all-counterexample arithmetic restrictions are distinct from bounds for the least counterexample. They are also distinct from the45-free theorem: L8 does not say that every exponent is large, or that an integer divisible by this fixed lcm is a counterexample.

Luca-Pomerance-Solé’s published2025 corrigendum already gives an asymptotically much stronger rarity statement, \#exceptions≤x = x^{O(1/log log x)}. A fixed-divisor filter has no improvement over that asymptotic counting theorem. Its gain is explicit arithmetic exclusion.

### Reproducibility

`verify_45_free.py` certifies L1/L2 and the two example sums by Arb. `verify_local_filter.py` checks the rational slack in L7, the displayed integer powers, and the strict joint-defect inequalities. The ordinary support arguments L3-L5 and the lcm equivalence L8 are indispensable and are not established by running the scripts alone.

<a id="section-19"></a>

## 附录 F：旧27-free消费者的严格障碍

Date: 2026-11-08. This is an ordinary proof using the published inputs already audited in R28 and one additional published lower bound. It is a statement about an auxiliary upper-bound consumer, **not** a counterexample to Robin’s inequality or a proof that 27-free integers cannot be treated by another argument.

### Statement and inherited input

Write

$$
x_0=29\,996\,208\,012\,611,
\quad N_k=\prod_{j\le k}p_j,
\quad p_{k_0}=x_0,
$$

and, for an integer $t\ge2$, define

$$
R_t(N_k)=\frac{\prod_{j\le k}(1-p_j^{-t})/(1-p_j^{-1})}
{\log\log N_k}.
$$

Then the following strict inequalities hold:

1.  At the published finite-prefix endpoint,

    $$
    \log(R_{27}(N_{k_0})/e^\gamma)>2.4\cdot10^{-9}.
    $$

2.  For every prime endpoint $x=p_k\in[x_0,4\cdot10^{13}]$,

    $$
    \log(R_{27}(N_k)/e^\gamma)>9\cdot10^{-10}.
    $$

3.  For every prime endpoint $x=p_k\in[x_0,5\cdot10^{13}]$,

    $$
    \log(R_{27}(N_k)/e^\gamma)>3\cdot10^{-11}.
    $$

The imported R28 facts are the exact identities T15 and T18, the uniform spectral envelope T9, and nonnegativity of the local concavity remainder Q. The ordinary proofs of their analytic interchanges are in the frozen R28 files `proofs/finite_height_26_free.md` and `proofs/psi1_kernel_interchange.md`. No global RH assumption occurs in these facts. Their only zero-location input is the published finite verification through height $H=3\cdot10^{12}$.

The new published input is Rosser and Schoenfeld (1962), Theorem 14, equation (3.37):

$$
\psi(t)-\theta(t)>\frac{49}{50}\sqrt t\qquad(t\ge121).
\tag{O1}
$$

The original formula was visually checked on printed page 71, as well as in Johnston (2023), Lemma 2.3. This lower bound is unconditional and valid on the entire integration tail.

### Exact identity, with the signs retained

For $x\ge x_0$, let $L=\log x$,

$$
w(t)=\frac{\log t+1}{t^2\log^2t},\quad
D(x)=\int_x^\infty(\psi(t)-\theta(t))w(t)\,dt,
$$

$$
Z(x)=\sum_\rho\frac1\rho\int_x^\infty t^\rho w(t)\,dt,
\quad T_2(x)=\sum_{p>x}\sum_{j\ge2}\frac1{jp^j},
$$

$$
W(x)=-\frac12\int_x^\infty\log(1-t^{-2})w(t)\,dt\ge0.
$$

R28 gives the real identity

$$
E_\theta(x)=Q(x)+D(x)+Z(x)
+\frac{\log(2\pi)}{xL}-W(x)-T_2(x),
\tag{O2}
$$

where

$$
E_\theta(x)=-\sum_{p\le x}\log(1-p^{-1})
-\gamma-\log\log\theta(x),\qquad Q(x)\ge0.
$$

The zero sum is real by conjugation and absolute convergence. Consequently

$$
E_\theta(x)\ge D(x)-|Z(x)|-W(x)-T_2(x).
\tag{O3}
$$

In particular, neither negative correction is simply omitted when constructing this lower bound.

### Lower bound for the prime-power contribution

Let $J(x)=\int_x^\infty\sqrt t\,w(t)\,dt$. The R28 kernel identity, or one direct integration by parts, gives

$$
J(x)=\frac2{\sqrt xL}
-\int_x^\infty\frac{t^{-3/2}}{\log^2t}\,dt
\ge\frac2{\sqrt xL}\left(1-\frac1L\right).
\tag{O4}
$$

Since every point of the integration tail satisfies $t\ge x_0>121$, O1 implies

$$
D(x)>\frac{49}{50}\frac2{\sqrt xL}\left(1-\frac1L\right).
\tag{O5}
$$

For every $x\in[x_0,5\cdot10^{13}]$,

$$
31<L<32,\qquad\sqrt x>5\,400\,000.
\tag{O6}
$$

If also $\sqrt x<A$, O5 therefore yields the rational lower bound

$$
D(x)>D_A:=\frac{49}{50}\frac2{32A}\frac{30}{31}.
\tag{O7}
$$

We will use $A=5\,500\,000$ for $x=x_0$, $A=6\,400\,000$ through $4\cdot10^{13}$, and $A=7\,100\,000$ through $5\cdot10^{13}$.

### Uniform bounds for the three possible losses

The inherited R28 spectral envelope gives

$$
|Z(x)|<Z_0:=
\left(\frac1{31}+\frac1{31^2}\right)
\left(\frac{47}{1000\cdot5\,400\,000}+\frac4{10^{11}}\right).
\tag{O8}
$$

This uses the exact unconditional total zero mass $2+\gamma-\log(4\pi)<47/1000$, the published finite-height location theorem, and the absolute high-zero tail budget $4\cdot10^{-11}$. It does not assume that unknown high zeros lie on the critical line.

For $m=\lfloor x\rfloor\ge x_0$, the nonnegative prime-power tail has the elementary bound

$$
T_2(x)\le\sum_{n>m}\frac1{2n(n-1)}
=\frac1{2m}\le T_0:=\frac1{2x_0}.
\tag{O9}
$$

Here $1/j\le1/2$ for $j\ge2$; adding all integers only enlarges the prime sum. The telescoping identity keeps the whole infinite tail.

For the trivial-zero correction, $-\log(1-u)\le u/(1-u)$ and $\int_x^\infty w(t)\,dt=1/(x\log x)$ give

$$
W(x)\le\frac1{2(x^2-1)x\log x}
\le W_0:=\frac1{62(x_0^2-1)x_0}.
\tag{O10}
$$

Combining O3 and O7–O10 yields

$$
E_\theta(x)>D_A-Z_0-T_0-W_0.
\tag{O11}
$$

### Comparison with the exact Euler-product saving

A decreasing integral comparison gives

$$
\log\zeta(27)<\zeta(27)-1
<2^{-27}+\int_2^\infty t^{-27}\,dt
=\frac{14}{13\cdot2^{27}}=:V_{27}.
\tag{O12}
$$

For a prime endpoint $x=p_k$, the inherited exact Euler-product identity is

$$
\log\frac{R_{27}(N_k)}{e^\gamma}
=E_\theta(x)-\log\zeta(27)+\tau_{27}(x),
\quad
\tau_{27}(x)=-\sum_{p>x}\log(1-p^{-27})\ge0.
\tag{O13}
$$

It follows that

$$
\log(R_{27}(N_k)/e^\gamma)>G_A,
\quad G_A:=D_A-Z_0-T_0-W_0-V_{27}.
\tag{O14}
$$

All quantities in $G_A$ are rational. Exact integer arithmetic verifies:

| Endpoint range | A | G_A, decimal display only | Exact rational conclusion |
|:---|:---|:---|:---|
| $x=x_0$ | 5,500,000 | $2.4622537444\ldots\cdot10^{-9}$ | $G_A>24/10^{10}$ |
| $x_0\le x\le4\cdot10^{13}$ | 6,400,000 | $9.4672038663\ldots\cdot10^{-10}$ | $G_A>9/10^{10}$ |
| $x_0\le x\le5\cdot10^{13}$ | 7,100,000 | $3.3605609263\ldots\cdot10^{-11}$ | $G_A>3/10^{11}$ |

The accompanying `verify_primorial_obstruction.py` checks each strict rational inequality, the square bounds, and the logarithm brackets. For the latter it verifies $27/10<e<68/25$ using the exponential series, then checks $(68/25)^{31}<x_0$ and $5\cdot10^{13}<(27/10)^{32}$. Decimal output is only a readable rendering of exact fractions.

### What is and is not obstructed

At fixed $N_k$, $R_t(N_k)$ strictly increases with the integer $t$, because each $1-p^{-t}$ strictly increases. R28 establishes $R_{26}(N_{k_0})<e^\gamma$, whereas O14 proves $R_{27}(N_{k_0})>e^\gamma$. Thus **26 is the largest t admitted by this particular uncoupled primorial consumer at that particular endpoint**. Merely improving its upper estimate cannot make its exact value negative at t=27. The obstruction extends through the displayed finite band.

No conclusion follows that any 27-free integer violates Robin. The consumer maximizes prime-factor contributions while using the smallest possible primorial denominator. Those two choices need not be realizable together by the same integer. Retaining the connection between actual exponents and $\log n$, or using a larger verified prefix with sufficient analytic coverage, can escape this obstruction.

The leading difficulty is genuine: the positive $D$ term has size comparable to $1/(\sqrt x\log x)$. In contrast the retained negative prime-power tail is bounded here by $1/(2\lfloor x\rfloor)$, already much smaller throughout the displayed band. The exact lower bound certifies this scale comparison without requiring heuristic asymptotics or an assertion that all discarded terms are negligible.

### Sources and provenance

- J. B. Rosser and L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. 6 (1962), 64–94, Theorem 14, equation (3.37), printed page 71. DOI: <https://doi.org/10.1215/ijm/1255631807> . Original scan inspected: <https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf> .

- D. R. Johnston, *On the average value of π(t)−li(t)*, Canadian Mathematical Bulletin 66 (2023), 185–195, Lemma 2.3, equation (2.4), <https://arxiv.org/pdf/2201.06184> . This independently restates the same published lower bound; it is not a second independent theorem required by the proof.

- Frozen R28 `proofs/finite_height_26_free.md`: T9, T12, T15, T18. Frozen R28 `proofs/psi1_kernel_interchange.md`: I1–I13. These are prior ordinary proofs in this project, not externally published results. Their external dependencies remain explicit and were audited independently in R29.

This note makes no historical-priority claim. Its contribution to this research pass is a certified limitation of a specific earlier consumer, useful for choosing what must be coupled in the next proof.

<a id="section-20"></a>

## 附录 G：冻结R28分析证明：须同时采用附录A修正

日期：2026-11-08。作者角色：本轮 tail 工作席。性质：普通证明候选，依赖下列逐项明确的已发表定理；本文件本身不构成外部同行评审、完整 Lean 认证或历史优先性认定。

### T0 原命题与输入清单

一个正整数称为 t-free，是指没有任何素数 p 使 p^t 整除它。本节证明的消费者是：

> **定理 T。** 所有 26-free 整数 $n>5040$ 都满足 Robin 不等式 $\sigma(n)<e^\gamma n\log\log n$。

所有对数为自然对数。取

$$
x_0=29\,996\,208\,012\,611,\qquad H=3\cdot10^{12},\qquad
B=2.169\cdot10^{25},\qquad a=1-10^{-5}.
$$

这里 $\theta(x)=\sum_{p\le x}\log p$、$\psi(x)=\sum_{p^m\le x}\log p$，$\gamma$ 为 Euler 常数，$\rho$ 总是按重数计数的 Riemann ζ 函数非平凡零点。 所用外部输入如下；它们均不假设全高 RH。

1.  Platt-Trudgian 的严格有限高度验证：所有满足 0\<\| Im ρ\|≤H 的非平凡零点都在 Reρ=1/2。Morrill-Platt 2021 Lemma 1 明确采用此 H。

2.  Morrill-Platt 2021 Lemma 2：对 599≤x≤B，\| θ(x)−x\|≤√x log<sup>2</sup>x/(8π)。其 Lemma 3：对 logx≥55，\| θ(x)−x\|≤1.405·10^−10 x。

3.  Morrill-Platt 的有限整数验证，经 Axler 2023 Lemma 3 明确整理为：所有 5040\<n≤N\_{k0} 满足 Robin，其中 k0=999,999,476,056，p\_{k0}=x0，N_k=∏\_{j≤k}p_j。

4.  Rosser-Schoenfeld 1962 Theorem 14 的 Corollary (3.39)：对所有 $t>0$， $\psi(t)-\theta(t)<1.02\sqrt t+3t^{1/3}$。

5.  一个远弱于现有结果的显式零点计数界：N(T)≤T logT 对 T≥H。这里 N(T) 按重数计数 0\<Imρ≤T。它可直接由 Hasanalizade-Shen-Wong 2022 Corollary 1.2 推出，见 T1。

6.  经典 Hadamard 恒等式及积分显式公式。其应用只需要无条件的临界带 0\<Reρ\<1；详见本节 T2 和同轮 `psi1_kernel_interchange.md` 的完整交换证明。

本证明不依赖 Murphy、Knausgård、Polak、Bell、teal-sea 的公开候选结论。也不需要枚举 x0 以内的全部素数或重新计算 H 以内的全部零点；这些大型有限义务作为已发表定理输入保留。

### T1 把全部未知高零点压缩为一个正预算

Hasanalizade-Shen-Wong 的已发表界是，对 T≥e，

$$
\left|N(T)-\frac{T}{2\pi}\log\frac{T}{2\pi e}\right|
\le0.1038\log T+0.2573\log\log T+9.3675.
\tag{T1}
$$

对 T≥H，有 loglogT≤logT、9.3675\<logT、2π\>6，因此右侧与主项之和小于 $(T/6+1.3611)\log T<T\log T$。所以下面的极粗计数输入成立：

$$
N(T)\le T\log T\qquad(T\ge H).
\tag{T2}
$$

按 Stieltjes 分部积分，先在 H\<\| Imρ\|≤Y 截断再令 Y→∞，

$$
\begin{aligned}
\mathcal T_H
&:=\sum_{|\Im\rho|>H}\frac1{|\Im\rho|^2}
=2\int_{(H,\infty)}t^{-2}\,dN(t)\\
&=-\frac{2N(H)}{H^2}+4\int_H^\infty\frac{N(t)}{t^3}\,dt
\le\frac{4(\log H+1)}H
<4\cdot10^{-11}.
\end{aligned}
\tag{T3}
$$

最后用了 logH\<29。式中高零点不被假设在临界线上；原来的无穷集合被一个**非零** 的显式总预算控制。

### T2 保留复振荡的核估计与准确零点和

令 x\>1、L=logx，并设

$$
w(t)=\frac{\log t+1}{t^2\log^2t},\qquad
F_z(x)=\int_x^\infty t^z w(t)\,dt\quad(\Re z<1).
$$

若 z=β+iτ、λ=1−z，则

$$
F_z(x)=\frac{x^{z-1}}{(1-z)L}-\frac z{1-z}I_2(z;x),
\qquad
I_2(z;x)=x^{z-1}\int_0^\infty\frac{v e^{-Lv}}{\lambda+v}\,dv.
\tag{T4}
$$

第二个恒等式来自 t=xe^y 与 $(L+y)^{-2}=\int_0^\infty v e^{-(L+y)v}dv$。Reλ\>0 保证交换绝对可积；\| λ+v\|≥\| λ\| 给出

$$
\boxed{\left|\frac{F_z(x)}z\right|
\le x^{\beta -1}\left[
\frac1{|z(1-z)|L}+\frac1{|1-z|^2L^2}
\right],\qquad z\ne0.}
\tag{T5}
$$

这里没有隐含 1/(1−β) 损失。若先在原 t 积分中把振荡取绝对值，不能得到这个界。

记

$$
K_\psi(x)=\int_x^\infty(\psi(t)-t)w(t)\,dt,
\qquad Z(x)=\sum_\rho\frac{F_\rho(x)}\rho.
$$

准确恒等式为

$$
K_\psi(x)=-Z(x)-\frac{\log(2\pi)}{xL}
-\frac12\int_x^\infty\log(1-t^{-2})w(t)\,dt.
\tag{T6}
$$

最后一项为正。T6 可从绝对收敛的 $\psi_1$ 显式公式出发，在有限 \[x,Y\] 上先把每个零点的边界与积分合并，再由 T5 的可和 O_x(\| Imρ\|^−2) 包络令 Y→∞。完整证明在同轮 `psi1_kernel_interchange.md`，I5-I10；这避免直接对条件收敛的 ψ 零点和交换无穷积分。Ramaré 的作者勘误 Lemma 1.1 也确认了 T6 中 −log(2π) 的符号。

经典 Hadamard 恒等式为

$$
B_0:=\sum_\rho\frac1{\rho(1-\rho)}
=2+\gamma-\log(4\pi)<\frac{47}{1000}.
\tag{T7}
$$

此和绝对收敛。对每个非平凡零点 ρ=β+iτ，

$$
\Re\frac1{\rho(1-\rho)}
=\frac{\beta (1-\beta )+\tau ^2}{[\beta (1-\beta )+\tau ^2]^2+\tau ^2(1-2\beta )^2}>0.
\tag{T8}
$$

有限高度验证中的 $0<|\tau|$ 不会遗漏实零点：对 $0<s<1$，交错级数 $\eta(s)=\sum_{n\ge1}(-1)^{n-1}n^{-s}>0$，而 $1-2^{1-s}<0$，所以 $\zeta(s)=\eta(s)/(1-2^{1-s})<0$。 因此，虽然 H 以上的零点可能离线，已验证低零点的正实总质量仍不超过 B0。对低零点，\| ρ(1−ρ)\|=\|1−ρ\|<sup>2</sup>=1/4+τ<sup>2</sup>、x^(β−1)=x^−1/2；对高零点，x^(β−1)≤1、两个分母均至少 τ<sup>2</sup>。由 T3、T5-T8 得到

$$
\boxed{
|Z(x)|
\le\left(\frac1L+\frac1{L^2}\right)
\left(\frac{B_0}{\sqrt x}+\mathcal T_H\right)
<\left(\frac1L+\frac1{L^2}\right)
\left(\frac{0.047}{\sqrt x}+4\cdot10^{-11}\right).
}
\tag{T9}
$$

T9 对全部 x\>1 成立。它不是全高 RH 下的 O(1/(√x logx)) 界：未知高零点留下了 4·10^−11/L 的非临界尺度项。

### T3 素数幂修正与统一的局部曲率预算

定义

$$
K_\theta(x)=\int_x^\infty(\theta(t)-t)w(t)dt,
\quad D(x)=K_\psi(x)-K_\theta(x)
=\int_x^\infty(\psi(t)-\theta(t))w(t)dt.
$$

对实数 0\<α\<1，T4 给 $F_\alpha (x)\le x^{\alpha -1}/[(1-\alpha )L]$，因为 $I_2(\alpha;x)>0$。由已发表的 ψ−θ 界，

$$
\boxed{0\le D(x)\le\frac{2.04}{\sqrt xL}
+\frac{4.5}{x^{2/3}L}.}
\tag{T10}
$$

对全部 x≥x0，Morrill-Platt 的两个范围合起来给

$$
|\theta(x)-x|\le10^{-5}x.
\tag{T11}
$$

具体地，x0≤x≤B 时，L<sup>2</sup>/(8π√x) 随 x 递减（L\>4），在左端小于 $32^2/(8\cdot3\cdot5\cdot10^6)<10^{-5}$。x≥B 时 logx≥55，Lemma3 的 1.405·10^−10 预算更小。

现在令 f(t)=loglogt，r=θ−x，并保留准确局部误差

$$
Q(x)=f(x)+f'(x)r-f(\theta(x))
=r^2\int_0^1(1-s)w(x+sr)ds.
\tag{T12}
$$

w 正且递减，θ≥ax，且对 x≥x0 有 log(ax)\>30。故

$$
0\le Q(x)
\le\frac{10^{-10}x^2}{2}w(ax)
\le q_0:=\frac{31}{1800\cdot99999^2}
<2\cdot10^{-12}.
\tag{T13}
$$

这仅使用了极粗的统一相对误差界；没有依赖 R27 的 31.2433% 优化常数。

### T4 共同原对象上的单调上包络

定义原乘积偏差与非负的高幂尾

$$
M(x)=-\sum_{p\le x}\log(1-p^{-1}),\qquad
E_\theta(x)=M(x)-\gamma-\log\log\theta(x),\qquad
T_2(x)=\sum_{p>x}\sum_{j\ge2}\frac1{jp^j}.
$$

这里只使用 $x\ge x_0$，所以 $\theta(x)>1$，所有对数都有实数定义。$T_2$ 绝对收敛，因为 $\sum_{j\ge2}(jp^j)^{-1}\le1/[2p(p-1)]$。保留 R27 的准确恒等式

$$
E_\theta(x)=Q(x)-K_\theta(x)-T_2(x),\qquad T_2(x)\ge0.
\tag{T14}
$$

为使本节可独立使用，直接核对 T14：对 $x<y$ 作 Stieltjes 分部积分，素数端点取 $x<p\le y$，得

$$
\sum_{x<p\le y}\frac1p
=f(y)-f(x)+\frac{r(y)}{y\log y}-\frac{r(x)}{x\log x}
+\int_x^y r(t)w(t)dt.
$$

写 $M(x)=\sum_{p\le x}p^{-1}+\sum_{p\le x,j\ge2}(jp^j)^{-1}$，再令 $y\to\infty$。经典 Mertens 乘积极限给 $M(y)-\gamma-f(y)\to0$，T11 给 $r(y)/(y\log y)\to0$，而 T6、T10 已保证 $K_\theta=K_\psi-D$ 的广义积分存在。因此 $M(x)-\gamma-f(x)=r(x)/(x\log x)-K_\theta(x)-T_2(x)$；减去 $f(\theta(x))-f(x)$ 即得 T14。

将 Kθ=Kψ−D 和 T6 代入，得到

$$
E_\theta(x)=Q(x)+D(x)+Z(x)+\frac{\log(2\pi)}{xL}
+\frac12\int_x^\infty\log(1-t^{-2})w(t)dt-T_2(x).
\tag{T15}
$$

最后两项都非正，故 T9、T10、T13 给出全部 x≥x0 上的共同上包络

$$
\boxed{
E_\theta(x)\le\mathcal E(x):=
q_0+
\left(\frac1L+\frac1{L^2}\right)
\left(\frac{0.047}{\sqrt x}+4\cdot10^{-11}\right)
+\frac{2.04}{\sqrt xL}
+\frac{4.5}{x^{2/3}L}
+\frac{\log(2\pi)}{xL}.
}
\tag{T16}
$$

每个非常数项都是正的递减函数，所以 $\mathcal E$ 递减。这里必须将同源 Q 保留为二次量；把其两个组成项分别取绝对值会失去下文的余量。

为使最终端点检验不依赖长小数，使用以下粗界：

$$
L\ge31,\quad\sqrt x\ge5.4\cdot10^6,\quad
x^{2/3}\ge9\cdot10^8,\quad x\ge2.7\cdot10^{13},\quad
\log(2\pi)<2.
$$

于是，对每个 x≥x0，

$$
\begin{aligned}
E_\theta(x)&\le U:=q_0
+\frac{47}{1000}\frac{32/31}{5\,400\,000\cdot31}
+\frac4{10^{11}}\left(\frac1{31}+\frac1{31^2}\right)\\
&\qquad+\frac{2.04}{5\,400\,000\cdot31}
+\frac{4.5}{900\,000\,000\cdot31}
+\frac2{27\,000\,000\,000\,000\cdot31}\\
&=1.2640548402271685\ldots\cdot10^{-8}
<1.27\cdot10^{-8}.
\end{aligned}
\tag{T17}
$$

U 本身是准确有理数；显示小数只供阅读。

### T5 26-free 的有限消费者：原整数族得到覆盖

设 k≥k0、x=p_k，令

$$
\Psi_t(n)=n\prod_{p\mid n}\frac{1-p^{-t}}{1-p^{-1}},\qquad
R_t(n)=\frac{\Psi_t(n)}{n\log\log n}.
$$

Euler 乘积给出准确式

$$
\log\frac{R_t(N_k)}{e^\gamma}
=E_\theta(x)-\log\zeta(t)+\tau_t(x),\qquad
\tau_t(x)=-\sum_{p>x}\log(1-p^{-t})\ge0.
\tag{T18}
$$

对 x≥x0，令 $m=\lfloor x\rfloor\ge10^{13}$。由 −log(1−z)≤2z（0≤z≤1/2）及递减积分判别，

$$
0\le\tau_{26}(x)
\le2\sum_{n>m}n^{-26}
\le\frac2{25m^{25}}
\le8\cdot10^{-327}.
\tag{T19}
$$

而 ζ(26)\>1+2^−26，log(1+v)≥v−v<sup>2</sup>/2 给

$$
\log\zeta(26)>2^{-26}-2^{-53}>1.49\cdot10^{-8}.
\tag{T20}
$$

T17-T20 给出对**全部** k≥k0 的严格余量

$$
\boxed{
\log\frac{R_{26}(N_k)}{e^\gamma}
\le U+8\cdot10^{-327}-(2^{-26}-2^{-53})
<-2.2\cdot10^{-9}<0.
}
\tag{T21}
$$

剩下的原整数消费者是标准且可直接证明的：如果 n 是 t-free，则 σ(n)≤Ψ_t(n)。如果 N_k≤n\<N\_{k+1}，则 n 至多有 k 个不同素因子。函数 h_t(p)=1+p^−1+⋯+p^(−t+1) 随 p 递减且大于1，故 Ψ_t(n)/n≤∏\_{j≤k}h_t(p_j)，并且 loglogn≥loglogN_k\>0。于是

$$
\frac{\sigma(n)}{n\log\log n}\le R_t(N_k).
\tag{T22}
$$

当 n\>N\_{k0}，取上述 k≥k0，T21-T22 证明原 Robin 不等式。所有 5040\<n≤N\_{k0} 已由外部输入3覆盖，不再要求它们 t-free。两个范围无缝覆盖全部 26-free 整数 n\>5040，定理 T 得证。

### T6 实际增量、最优性与不能推论的事项

1.  若以上普通证明及全部输入被最终接受，结论把所核对的已发表 21-free 基线扩大为26-free，允许素因子指数上界从20增至25，增加五级。相对于未审25-free候选则增加一级。这里没有作历史穷尽性证明，不能先宣布公认世界纪录已变更。

2.  这里两个命名族（21-free 与26-free）的自然密度增量为准确式 1/ζ(26)−1/ζ(21)。它不是所有既有 Robin 文献结果取并集之后的新增整数密度，也不是 RH 的完成百分比。有限个 n≤5040 不影响密度。

3.  这个消费者不使用 Bell/Polak 公开稿提供更大的有限前缀，因而不继承那些未重放大型证书的义务。

4.  未知高零点尾 $\mathcal T_H$ 仍为正。乘以 √x logx 后，它可能增长；没有推出与 RH 等价的全高临界尺度 K 界。

5.  此包络在同一端点不能认证27-free，因为 ζ(27) 的固定间隔更小；这不构成27-free的反例或不可能性证明。

6.  本节的核、Hadamard恒等式、有限H与绝对可和尾的思想均有经典前身。Vanlalngaia2017及BFKNW2026亦有相关加权零点估计。新颖性最多暂定为本轮这一组输入的可消费组合及更强整数族，须继续进行文献与数学复核。

### 来源

- T. Morrill and D. J. Platt, *Robin’s inequality for 20-free integers*, Integers21(2021), A28. <https://math.colgate.edu/~integers/v28/v28.pdf> 。实际核读 Lemmas1-3、Theorem5、Corollary2及primorial reduction。

- C. Axler, *On Robin’s inequality*, Ramanujan Journal61(2023),909-919. <https://link.springer.com/article/10.1007/s11139-022-00683-0> 。使用Lemma3的准确全部整数前缀；Lemma4提供T18的既有形式。其21-free定理是比较基线，不作为26-free的新结论。

- J. B. Rosser and L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math.6(1962),64-94. DOI10.1215/ijm/1255631807；扫描 <https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf> 。使用Theorem14的Corollary(3.39)，并核对(3.38)及Theorem9。

- E. Hasanalizade, Q. Shen and P.-J. Wong, *Counting zeros of the Riemann zeta function*, J. Number Theory235(2022),219-241. DOI10.1016/j.jnt.2021.06.032；作者预印本 <https://arxiv.org/pdf/2107.06506> 。实际核读Corollary1.2及N(T)取重数/端点约定。这里只消费极粗的N(T)≤TlogT，不需要优化其常数。

- J.-L. Nicolas, *Small values of the Euler function and the Riemann hypothesis*, Acta Arith.155(2012),311-321. <https://arxiv.org/pdf/1202.0729> 。(1.3)为T7、Lemma2.2为T4前身；本节不把其RH条件结论导入全高。

- O. Ramaré, author corrigendum to *Explicit estimates for the summatory function of Λ(n)/n from the one of Λ(n)*, <https://ramare-olivier.github.io/Maths/Corrigendum-PsiTildeSimple-Acta-02.pdf> 。核对Lemma1.1的准确积分公式与log(2π)符号；不消费其小范围程序输出。

- 同轮 `research/r28/closure/psi1_kernel_interchange.md` 是T4-T9所需普通分析证明的独立重建；不是外部文献。

<a id="section-21"></a>

## 附录 H：冻结R28核分析与无穷和交换

日期：2026-11-08。普通分析证明；本节只证明无穷零点和的交换与核估计，不证明新的零点位置结论。

令

$$
w(t)=\frac{\log t+1}{t^2\log^2t},\qquad k(t)=-w'(t)>0,\quad
F_z(x)=\int_x^\infty t^z w(t)\,dt\quad(x>1,\ \Re z<1).
$$

所有幂使用实数 $\log t$。非平凡零点按重数列入，$0<\Re\rho<1$。

### I1 一个对整个临界带有效的复核界

对 $z=\beta+i\tau$、$\beta<1$，令 $L=\log x$、$\lambda=1-z$。有限分部积分并消去无穷边界，得

$$
F_z(x)=\frac{x^{z-1}}{(1-z)L}-\frac{z}{1-z}I_2(z;x),\qquad
I_2(z;x)=\int_x^\infty\frac{t^{z-2}}{\log^2t}\,dt.
\tag{I1}
$$

这里 $\Re\lambda>0$。写 $t=xe^y$，再使用 $(L+y)^{-2}=\int_0^\infty v e^{-(L+y)v}\,dv$，得到

$$
I_2(z;x)=x^{z-1}\int_0^\infty\frac{v e^{-Lv}}{\lambda+v}\,dv.
\tag{I2}
$$

双积分在交换前绝对可积：用 $\Re\lambda>0$，可估为 $\int_0^\infty v e^{-Lv}/(\Re\lambda+v)\,dv<\infty$。 又因为 $|\lambda+v|\ge|\lambda|$ 对所有 $v\ge0$ 成立，

$$
|I_2(z;x)|\le\frac{x^{\beta-1}}{|1-z|L^2}.
\tag{I3}
$$

故当 $z\ne0$ 时，

$$
\boxed{\left|\frac{F_z(x)}z\right|
\le x^{\beta-1}\left[
\frac1{|z(1-z)|\log x}+\frac1{|1-z|^2\log^2x}
\right].}
\tag{I4}
$$

这是保留复振荡后的界；不能把 $I_2$ 在原 t 积分中逐点取绝对值后仍声称得到 I3。

### I2 从 $\psi_1$ 推出准确的 Kψ 零点和

已知的无条件 integrated explicit formula 为

$$
\psi_1(t):=\int_1^t\psi(u)\,du
=\frac{t^2}{2}
-\sum_\rho\frac{t^{\rho+1}}{\rho(\rho+1)}
-t\log(2\pi)+C
-\sum_{m\ge1}\frac{t^{1-2m}}{2m(2m-1)},\qquad t>1,
\tag{I5}
$$

其中 $C=\zeta'(-1)/\zeta(-1)$。零点和绝对收敛，且在任意紧区间 $[x,Y]\subset(1,\infty)$ 上一致收敛：零点计数 $N(T)=O(T\log(T+2))$ 给 $\sum_\rho|\rho(\rho+1)|^{-1}<\infty$，而 $|t^{\rho+1}|\le\max(1,Y^2)$。平凡零点项也在该紧区间上一致绝对收敛。

设 $R_1(t)=\psi_1(t)-t^2/2$，则在有限区间

$$
\int_x^Y(\psi(t)-t)w(t)\,dt
=[R_1(t)w(t)]_x^Y+\int_x^Y R_1(t)k(t)\,dt.
\tag{I6}
$$

这一步用的是 $R_1$ 的局部绝对连续性，没有对不绝对收敛的 ψ 逐项零点公式直接积分。 把 I5 代入 I6，利用紧区间上一致收敛交换求和与积分。每个零点项的边界与积分合在一起准确为

$$
-\frac1\rho\int_x^Y t^\rho w(t)\,dt
=-\frac{F_\rho(x)-F_\rho(Y)}\rho.
\tag{I7}
$$

常数 C 贡献为零；其余光滑项可直接微分。因此

$$
\int_x^Y(\psi(t)-t)w(t)\,dt
=-\sum_\rho\frac{F_\rho(x)-F_\rho(Y)}\rho
-\log(2\pi)\int_x^Yw(t)\,dt
-\frac12\int_x^Y\log(1-t^{-2})w(t)\,dt.
\tag{I8}
$$

对每个固定零点，$F_\rho(Y)\to0$。由 I4，所有 $Y\ge x>1$ 都满足

$$
\left|\frac{F_\rho(Y)}\rho\right|
\le\frac1{|\rho(1-\rho)|\log x}
+\frac1{|1-\rho|^2\log^2x}.
\tag{I9}
$$

右边对全部零点可和，因为 $|\Im\rho|\to\infty$ 时每项是 $O_x(|\Im\rho|^{-2})$，且有限个低零点不等于 0 或 1。故对零点级数应用支配收敛，允许令 $Y\to\infty$。两个非零点项也绝对收敛。这已证明 Kψ 的广义积分存在，并给出

$$
\boxed{
K_\psi(x):=\int_x^\infty(\psi(t)-t)w(t)\,dt
=-\sum_\rho\frac{F_\rho(x)}\rho
-\frac{\log(2\pi)}{x\log x}
-\frac12\int_x^\infty\log(1-t^{-2})w(t)\,dt.
}
\tag{I10}
$$

经典定量 PNT 另可保证左侧绝对收敛；但 I5-I9 本身的交换不需要一项新的全高零点无零区估计。 最后一个项为正，所以可在求 Kψ 下界时删去。不得在上界中按同样方向删去。

### I3 低零点的无条件总质量上界

Hadamard 乘积的经典绝对收敛恒等式为

$$
B_0:=\sum_\rho\frac1{\rho(1-\rho)}=2+\gamma-\log(4\pi).
\tag{I11}
$$

为明确其无条件地位，令 $\xi(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)$。其 Hadamard 对数导数在 1 与 0 的差为绝对收敛和 $\sum_\rho[(1-\rho)^{-1}+\rho^{-1}]$。函数方程 $\xi(1-s)=\xi(s)$ 使此差等于 $-2\xi'(0)/\xi(0)$。由 $\zeta'(0)/\zeta(0)=\log(2\pi)$ 及 $\Gamma$ 在 0 的展开， $\xi'(0)/\xi(0)=-1-\gamma/2+\tfrac12\log(4\pi)$，即得 I11。推导没有把任何零点替换为 $1/2+i\tau$。 对任意非平凡零点 $\rho=\beta+i\tau$，

$$
\Re\frac1{\rho(1-\rho)}
=\frac{\beta(1-\beta)+\tau^2}
{[\beta(1-\beta)+\tau^2]^2+\tau^2(1-2\beta)^2}>0.
\tag{I12}
$$

若已知全部 $|\Im\rho|\le H$ 的零点都在临界线上，则这些项本身为正实数，且

$$
\sum_{|\Im\rho|\le H}\frac1{|\rho(1-\rho)|}
=\sum_{|\Im\rho|\le H}\frac1{|1-\rho|^2}
\le B_0.
\tag{I13}
$$

这是由无条件总和及每项的正实部推出的有限已验证部分上界；并未假设 H 以上的零点在临界线上。

有限高度验证通常写为 $0<|\Im\rho|\le H$。这里不会遗漏实零点：若实数 $0<s<1$，交错级数 $\eta(s)=\sum_{n\ge1}(-1)^{n-1}n^{-s}>0$，而 $1-2^{1-s}<0$，故 $\zeta(s)=\eta(s)/(1-2^{1-s})<0$。因此临界带内没有 $\Im\rho=0$ 的零点。

### 来源与范围

- Jean-Louis Nicolas, *Small values of the Euler function and the Riemann hypothesis*, Acta Arith.155(2012),311-321; <https://arxiv.org/pdf/1202.0729> ，定义 (1.3) 给 I11，Lemma2.2 给 I1 的前身。本节 I2-I4 逐式独立证明，不作首次发现声明。

- Daniel R. Johnston, *On the average value of π(t)−li(t)*, Canad. Math. Bull.66(2023),185-195; arXiv:2201.06184v2, <https://arxiv.org/pdf/2201.06184> ，Lemma2.6 的证明列出 I5；全文零点记号与取重数约定保留。本文不消费其显示数值和中间估计的舍入。

- Angel Kumchev, *The Distribution of Prime Numbers* (2005 graduate notes), <https://tigerweb.towson.edu/akumchev/distributionofprimesnotes.pdf> ，PDF p43 Exercise16 同样给出 I5。

这里的成果是合法的精确表示及可消费估计。任何具体 26-free 结论仍需有限前缀、θ 的统一界、H 的验证范围、N(T) 显式计数界及最终数值证书共同完成。

<a id="section-22"></a>

## 附录 I：独立关系保持与严格余量模块

版本：R29，2026-11-08。用途：将“保留关系、寻找下一层关系、用已知无限定理处理余项”的研究直觉，变成可以独立复用、核查和停止的普通数学模块。这里的闭合指证明接口闭合；不假设目标猜想已被证明。

**数论实例的固定记号。** 所有对数为自然对数；σ(n)为正因子和，γ为Euler常数，ζ为Riemann zeta函数。t-free 指任何素数的t次方均不整除n。令 p_k 为第k个素数，N_k为前k个素数之积，θ(x)=Σ\_{p≤x}logp，x0=29,996,208,012,611，k0=999,999,476,056，p_k0=x0，H=3·10<sup>12</sup>。N(T)按重数计数满足0\<Imρ≤T的非平凡零点。以下Robin实例的尾部取n≥N_k0，另用已发表有限前缀覆盖5040\<n≤N_k0；核心联动引理要求整数t≥9。

### 1. 可采用的核心命题

一个量趋于零，并不意味着所有与它相关的信息消失。关系信息可能在经过适当归一化的量中保留。但“只要有关系就不可能趋于零”不是数学定理。例如

$$
a_n=n^{-1},\qquad b_n=n^{-2},\qquad b_n/a_n^2=1.
$$

两个量都趋零，关系仍精确保留。实际需要研究的是：目标、归一化尺度与误差能否一起传递，并且能否重建原问题的符号或大小。

同样，“约掉无穷”应落实为已证明的等式、可和性、支配估计或统一界。不能把无穷当成一个普通非零实数进行约分。一个收敛尾项可以用有限参数控制，控制后的预算一般仍非零。

### 2. 模块输入与输出

模块的状态为

$$
\mathfrak R=(D,\ F,\ \omega,\ \mathcal S,\ \mathcal E,\ \Pi).
$$

| 槽位 | 必须记录的内容 | Robin 实例 |
|:---|:---|:---|
| D：定义域 | 对象、正性条件、全称量词 | n\>5040；t-free；x=p_k≥x0 |
| F：原目标 | 不等式的准确左减右形式 | G(n)=log\[σ(n)/(e^γ n loglog n)\] |
| ω：共享数据 | 不同读出来自同一对象的约束 | 素因子指数 a_p、S_a=Σa_p log p、θ(x) |
| S：已知供应 | 定理、来源、适用范围 | 有限 RH 高度、θ 界、零点计数、有限 Robin 前缀 |
| E：误差账本 | 符号、相关性、区间、尾项 | Q、Z、D、T<sub>2</sub>、τ_t；禁止独立重复支付 |
| Π：返回映射 | 如何从辅助结论回到原对象 | 任意素数支撑压缩、补零、max(θ,S_a)、前缀与尾部拼接 |

输出只取三种状态：

1.  **闭合**：严格余量经证明大于零，且 Π 覆盖完整原量词。

2.  **待证**：还缺一个明确命名、明确范围的供应定理或余量。

3.  **该接口受阻**：证明选定辅助量确实越过阈值；这不自动否定原猜想。

### 3. 六个允许的研究操作

#### 3.1 准确改写

先找等式，再做估计。乘法目标可以在严格正的定义域上取对数：

$$
\log\frac{\sigma(n)}n
=\sum_{p^a\parallel n}\left[-\log(1-p^{-1})+\log(1-p^{-a-1})\right].
$$

取对数是一种合法的关系变换，不是所有层次都必须使用的固定形式。下一层可以是泰勒余项、凸对偶、求和变换或积分核，只要保留其定义域与返回规则。

#### 3.2 同源相消

对共享误差 r=θ−x，先保留 Mertens 边界项与分母修正的准确联系：

$$
E_\theta=Q-K_\theta-T_2,
$$

$$
Q=r^2\int_0^1(1-s)w(x+sr)\,ds\ge0.
$$

一阶误差已经在等式层相消，随后才估计二阶 Q。若先分别取最坏绝对上界，可能破坏这份相消。

#### 3.3 联动扩展

发现松弛受阻时，加入丢失的实际约束。对任意 t-free 原整数，按顺序压缩素数支撑，并把不足的支撑位置补 a_p=0，保留

$$
S_a=\sum_{p\le x}a_p\log p,\qquad
\log n\ge\max\{\theta(x),S_a\}.
$$

定义

$$
\mathcal P_t=
\sum_{p\le x}\log\frac{1-p^{-t}}{1-p^{-a_p-1}}
+\log\log\max\{\theta(x),S_a\}-\log\log\theta(x).
$$

这给出

$$
G(n)\le E_\theta-\mathcal P_t-\log\zeta(t)+\tau_t.
$$

R29 已核查的普通推导对 x≥x0、整数 t≥9 和全部上述补零指数向量证明 P_t≥2.15/(√x log x)。它把提高分子所需的指数成本与提高分母的整数大小联系起来。

#### 3.4 无限量的有限预算

对有限高度 H 以下零点使用已发表位置定理。对所有未知高零点使用计数定理与 Stieltjes 积分：

$$
\sum_{|\Im\rho|>H}(\Im\rho)^{-2}
=-2N(H)/H^2+4\int_H^\infty N(T)T^{-3}\,dT.
$$

再保留函数方程的成对关系 β↔1−β：

$$
x^{\beta-1}+x^{-\beta}\le1+x^{-1}.
$$

无限集合被一项显式、非零预算控制。分部积分的负端点与对称配对都必须在放宽前保留。

#### 3.5 带误差归一化

若 Y=sR，s\>0，且观测为 Y+η，则归一化误差为 η/s。研究 R 时，必须同时证明 η/s 有界或小于目标余量。不能只把信号放大，而把误差留在旧尺度。

一般的商误差公式是

$$
\frac{a+\delta a}{b+\delta b}-\frac ab
=\frac{b\,\delta a-a\,\delta b}{b(b+\delta b)}.
$$

分子保留读出与误差的相关性；分母要求 b 与 b+δb 不为零。舍去共享来源，只给 \| δa\|+\| δb\|，可能过度放宽；没有误差控制，则归一化可能放大不确定性。

#### 3.6 严格余量与返回

闭合量定义为

$$
\mathcal M_t(x,\mathbf a)=
\log\zeta(t)-\tau_t(x)-[E_\theta(x)-\mathcal P_t(x,\mathbf a)].
$$

只有当 M_t\>0 对所需全域成立，且原整数返回映射完整，才能输出 G(n)\<0。证明每个固定有限窗口可处理，并不等于证明整个无限域已有统一余量。

### 4. 递归的停止规则

每一轮必须回答：哪个等式新保留了信息？哪个真实误差或供应被改善？结果新增了哪一个量词范围？

- 若只有变量或术语增加，余量与量词均未变，不计数学进展。

- 若更紧的上界仍不足，先检查是否只是估计松；必要时建立辅助量的下界。

- 若辅助量下界已超过阈值，递归应恢复被舍弃的共享约束，不能继续宣称同一个上界“还能变负”。

- 若闭合依赖一个实质上等价于 RH 的新供应，必须标明该供应待证，不能把它当定义。

- 若所有义务已闭合，停止该消费者的优化，把余下问题列成独立明确目标。

R29 给出实际例子：旧 R_27(N_k0) 的对数差严格大于2.4·10<sup>-9</sup>，说明旧分离消费者在该点确实受阻。保留 P_t 后，完整的45-free消费者得到正余量，而不是把旧辅助量的正值重新命名成零。

### 5. 与 trureturing 的对应

审查固定于提交 `9a201d9cb6089d7ec36fd2c2cdffbbd9797a2ae5`，没有修改远端仓库，也没有本地重建其 Lean 文件。引用与阅读范围记录在包内的仓库审查清单。

| 仓库概念或接口 | 本模块采用的数学要求 | 不自动获得的结论 |
|:---|:---|:---|
| 原多项式响应、四份独立预算的正底 | 先保留实际输出的符号和共同输入 | 任意数论余项已相消 |
| 同一记录、来源相对顺序 | 每次递归保留来源与返回映射 | 固定窗口结论可无限一致化 |
| 方差与四阶矩传递接口 | 接口声明必须列出供应前件 | 实际素数误差满足该前件 |
| 中心响应与共同强度 | 在指定分支、正质量上归一化 | 任意输入对自动可加或一般物理三维性 |
| FIB 有限窗口精度安排 | 区分逐个有限窗口与全局误差 | 无限记录的全变差或物理时间解释 |

仓库提供有用的接口纪律；数论定理仍由本文自己的等式、已发表供应和严格余量证明。量子态、面积或余弦固定点等直觉若进入该模块，需要先给出到 σ、ζ 或素数误差的明确、可证明映射。

### 6. R29 已闭合实例与开放边界

已闭合的普通证明实例：所有45-free n\>5040 满足 Robin；对所有 n\>5040，局部条件 p^{ν_p(n)+1}≤80,000,000 足够，两种明确的有限素数联合缺陷条件也足够。这里“已闭合”指所列普通证明与内部独立审查通过，不表示外部审稿或形式化内核认证完成。

完整 RH 仍开放。本次固定消费者不能对所有 t 给出统一的正 M_t，因为 log ζ(t)→0，而高零点预算仍正。未来需要改善的是实际高零点的带符号响应、可证明的联合矩供应或另一条全整数结构约束；这是一项具体数学义务，而不是要求无限增加关系层数。

### 7. 可复用执行合同

```text
输入：原目标 F、全称定义域 D、共享数据 ω、已证供应 S。
准确改写 F；列出全部误差和适用域。
保留共享约束后相消；仅对剩余部分取界。
若存在无限和或积分，提交一致收敛/可和性或显式尾预算。
若归一化，传输误差并记录非零条件和返回映射。
计算严格余量 M；验证连续全域及全部离散对象覆盖。
M>0：返回带量词的结论及依赖。
否则：返回缺失供应，或受阻辅助接口的准确下界。
```

**强制来源补丁：** 冻结 R28 文件中的 HSW 印刷常数9.3675 按 Bellotti-Wong2025 更正为9.4925。`zero_count_source_correction.md` 已重新证明全部被使用的粗界，后续预算不变。继承旧证明必须同时继承此补丁。
