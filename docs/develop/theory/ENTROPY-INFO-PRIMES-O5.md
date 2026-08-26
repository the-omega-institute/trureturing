# ENTROPY-INFO-PRIMES-O5:热层卷宗(审计版 r1)

**性质**:热层归档卷宗,供 data-only 归入 trureturing `docs/develop/theory/`;整编 2026-08-01~03 讨论弧(热力学=概率 / 加乘干涉 / 熵–素数–概率词典 / 退相干与退相关双词典 / 白化读法 / O-5 接口)。
**口径**:kernel 冻结为唯一真值;本卷通篇热层罗盘,逐条分型;**去形式化候选清单**见 §7,审计记录与待异模型审计清单见 §8。
**审计标记**:【检】= 本卷成文时检索亲核;【算】= 本卷作者亲手推算;【训】= 训练知识级,待第二模型/文献员复核。
**单模型产出(Claude Fable 5),待异模型审计,如实声明。**

---

## §1 Legendre 主账:热力学是概率的加法语气

**1.1** 平衡热力学 = 指数族概率论:对偶 = Legendre–Fenchel 共轭,间隙 = 相对熵,封零 = 平衡。Fenchel–Young 恒等式 ln Tr e^H = Tr(Hρ) + S(ρ) + D(ρ‖e^H/Z) 对一切 (H,ρ) 成立【算】(量子形属 loning Observer-quantum 母账,分账见 §9)。
**1.2** 一元论的准确形:实体唯概率;熵与自由能是**向概率提问的读数**,不是新存在者。对数之必然:机会相乘、账本相加,乘转加的换算函数唯一(Shannon 公理化)【训】。熵之词性:S = E[−ln p],量纲为对数概率——概率的指数(速率函数),非概率本身;自由能 = 概率的对数母函数;(累积量母函数, 速率函数) 这对在概率论内出厂即互为 Legendre 共轭(Gärtner–Ellis/Varadhan;Ellis、Touchette 2009 综述)【训】。
**1.3 ℕ 上的字面实例化**【算】:能量 E(n) = ln n,Gibbs 态 = zeta 分布 P_s(n) = n^{−s}/ζ(s)(约束 E[ln n] 下的最大熵分布);三本账:自由能 ln ζ(β);**内能 U = −ζ′/ζ = Σ Λ(n)n^{−β}**(整数气体内能即 von Mangoldt 级数,ψ(x) 为其积累形);熵 S = βU + ln ζ。
**1.4** 边界:本节全部住在平衡侧;概率时间对称,箭头须自创世条件另行进口(WM v0.11 线)。

## §2 加乘与干涉:素性的位置

**2.1** 量子记账两条:相继相乘、并列相加;干涉 = 加法换成复币种后的相消——波动性住在加法允许相消的那一刻,粒子性住在乘法可分解【训,教科书级】。
**2.2** ℕ 的两套结构:加法(计数)与乘法(素数 = 自由生成元);ζ 的两种写法之等号 = 唯一分解定理。显式公式的波粒读法:ψ 在素数幂处跳(粒子相),每个零点贡献一列波 x^{1/2}e^{iγ ln x}(频率相);对数/Mellin = 乘法群上的 Fourier【训】。
**2.3** 1/2 分账(协变检验,WM-R4 后继):(a) Berstel 深度之 1/2 = 进位速度倒数,随 k-bonacci 协变——与 ζ 族无关(前案已裁);(b) 临界线 1/2 与 √x 抵消之 1/2 由 von Koch 1901 焊接为同一常数(Θ 双向控制误差指数)【训】;(c) 对偶中点 1/2 进口自加法侧(Poisson 求和 → 函数方程,Riemann/Tate 线)【训】;(d) **RH = 两枚异出身 1/2(对偶中点 vs CLT 指数)的会师断言**——读法级冠语,骨架定理级(§3)。

## §3 熵–素数–概率词典(压缩;全文另卷 Entropy-Primes-Probability-Survey)

| 条目 | 内容 | 分型/审计 |
|---|---|---|
| Euler 积 = 独立性 | zeta 分布下 v_p 独立几何分布;唯一分解的概率化身 | 定理级【检:Lin–Hu, Bernoulli 2001;Golomb 1970】 |
| primon 气体 | ε_p = ln p;玻色 Z = ζ(β);费米 Z = ζ(β)/ζ(2β);μ = 费米宇称,Σμ(n)n^{−β} = 1/ζ = Witten 指标 | 定理级(词典为构造)【训:Julia 1990;Spector 1990】 |
| 极点 = 相变 | 态密度 e^E ⟹ S(E)=E ⟹ Hagedorn 于 β=1;Bost–Connes 1995:配分函数 ζ 之 C*-系统于 β=1 自发破缺,对称群 Gal(ℚ^ab/ℚ) | 定理级【训】 |
| 熵证 Chebyshev | 均匀整数不可压 + 分解次可加 ⟹ Σ_{p≤n}(ln p)/p ~ ln n | 定理级【检:Kontoyiannis arXiv:0710.4076;Billingsley 1973】 |
| 粒子数 CLT | Erdős–Kac 1940:(ω(n)−ln ln n)/√(ln ln n) → N(0,1) | 定理级【训】 |
| 短区间 Poisson | Gallagher 1976,依 Hardy–Littlewood | 条件级【训】 |
| 独立性汇率 | Mertens e^{−γ};Maier 1985 短区间失效;Granville 修正 | 定理级【训】 |
| RH ⟺ 硬币 | Littlewood 1912:RH ⟺ M(x)=O(x^{1/2+ε});Denjoy 1931 读法;Littlewood 1914 Ω 兜底 | 定理级+读法级【训】 |
| 零点对数气体 | Montgomery 1973 对关联;GUE = Coulomb 对数气体 β=2 Gibbs 测度(Dyson);素数近最大熵 vs 零点亚泊松刚性,显式公式为 Fourier 桥 | 定理/数值级;并置为读法【训】 |
| 热流形变 | de Bruijn 1950–Newman 1976 常数 Λ;RH ⟺ Λ≤0;Rodgers–Tao 2018/2020:Λ≥0;Polymath15:Λ≤0.22 | 定理级【训】 |
| Sarnak 熵分界 | μ ⟂ 一切零拓扑熵系统(猜想);Matomäki–Radziwiłł、Tao 对数二点等进展 | open【训】 |

## §4 稳定性双词典:退相干与退相关

**4.1 量子(趋衡端)。** 退相干退的是相位相干,机制是**建立**系统–环境相关:信息搬家非销毁;局部熵 = 环境已读而我未读之账(v0.9 机制现场);单向性依 DPI 三方结构(v0.10)。链条:**监视 → 筛选(熵稳定:einselection/可预测性筛,熵产率极小者当选指针态;Zurek–Habib–Paz 1993【训】)→ 誊抄(信息稳定:no-broadcasting——可广播 ⟺ 交换代数,Barnum et al. 1996【训】;量子达尔文冗余,Ollivier–Poulin–Zurek 2004、Blume-Kohout–Zurek【训】;普适定理化:Brandão–Piani–Horodecki 2015,量子 de Finetti/单配性证【训】)→ 客观性(多方独立核账一致 = D2 多面恒等之物理层)**。已冻锚(in-tree,零 sorry):`phase_damping_fixed_iff_diagonal`、`record_channel_fixed_iff_selected_blocks`(D5/S3/Quantum)——"稳定者 = 监视信道之 Fix"的 qubit 精确形;按 WM-R4 只指认不加冕。箭头脚注:退相干需初始未相关环境(空白纸带),再相干仅需阴谋级初始相关——信息稳定运行于创世拨付的负熵(v0.11/v0.12 Landauer–Albert 线)。
**4.2 视觉(编码端)。** 退相关 = 熵最大化的二阶投影:固定预算下不相关等方差最大化容量;自然图像 1/f² 强相关,中心-周边感受野 = 白化滤波(Atick–Redlich 1990/1992【检】);侧抑制 = 预测编码只传残差(Srinivasan–Laughlin–Dubs 1982【检】);实测:LGN 时域白化(Dan–Atick–Reid 1996, J. Neurosci. 16:3351【检】),直方图均衡逐点实现于蝇(Laughlin 1981【检】)。**枢纽:信息稳定与完全退相关对抗**——白化放大高频而高频信噪比最低;最优滤波随 SNR 滑动(亮带通/暗低通),真目标函数为 infomax(Linsker 1988【训】),退相关仅其无噪极限;Barlow 2001 自修订:冗余为纠错与结构之原料【训】;实测退相关是部分的(Pitkow–Meister 2012, Nat. Neurosci.【检】)。熵稳定由适应实现:增益控制/除法归一化钉住输出分布(Heeger 1992;Carandini–Heeger 2012【训】;适应性重标度最大化传输:Brenner–Bialek–de Ruyter 2000【检,连带】)。退相关 ≠ 独立:二阶花完剩非高斯性,稀疏编码/ICA 收割高阶(Olshausen–Field 1996;Bell–Sejnowski 1997【检,连带】)。
**4.3 符号反转之和解。** 量子词典"稳定者被复制",视觉词典"稳定者被丢弃"——载体(字母表/指针基)要稳,内容(消息/惊奇)要新;信源编码去冗余,信道编码靠冗余;两个"稳定"由冗余定价、符号相反,真实系统按噪声在其间取内点。JEPA 防塌缩正则(方差项=熵下限、协方差项=退相关、不变项=信息稳定;Barlow Twins 直以 Barlow 命名)为此词典之直系后代【训;读法级家谱】。

## §5 白化读法:边缘 = 素数,零交叉 = 零点

**5.1 视觉侧定理骨架。** 稳定像消失:影像钉死于视网膜则数秒内知觉消失(Ditchburn–Ginsborg 1952;Riggs et al. 1953【训】)——信道不动点不可见,所见唯偏离。白化残差 = 稀疏重尾之边缘结构(Field 1987【检,连带】);Marr–Hildreth 1980:边缘 = ∇²G 零交叉【训】;**Logan 1977(审计后精确形)**:一倍频程内带通、与自身 Hilbert 变换无公共零点(实单零除外)⟹ 零交叉**至乘常数**唯一确定信号;唯一性 ≠ 稳健可恢复(无鲁棒性保证),二维 Marr 猜想有 Meyer 反例【检;本卷勘误,见 §8】。相位一致性:边缘 = 诸频相位对齐之建设性干涉(Morrone–Burr【训】)。正交性原理:最优预测残差为白(Wiener/Kalman 新息)【训】。
**5.2 素数侧对榫复现(读法级)。** 显式公式 = 预测编码:光滑趋势(极点项)减除后,残差全由零点振荡模承载;素数幂 = 诸零点波相位对齐处;谱线峰落于 γ。**RH 之白化读法(读法级)**:RH = 素数通过白化检验——光滑项已是最优预测器,残差再无可榨结构,诸谱线同包络 x^{1/2};骨架定理级(von Koch 1901、Littlewood Ω、M(x) ⟺ RH)。鱼眼 = 惊奇落点(saliency = 中心-周边残差;Bayesian surprise = 先验后验 KL;Itti–Koch/Itti–Baldi【训】)。
**5.3 对榫总表(全部读法级,禁同构宣称)**:边缘 ↔ 素数;零交叉集/谱线 ↔ 非平凡零点;相位一致 ↔ 显式公式干涉;白化检验 ↔ RH;注意/鱼眼 ↔ 惊奇落点。结构对应仅落在"**趋势+残差**"分解与"信息聚于残差之零集/谱线"之定理形处;余皆读法级类比,不作同构宣称。

## §6 O-5 与 trureturing 整体接口

**6.1 气体身份【算】。** eulerGerm(s) = ∏_p Σ_v p^{−sβ(v)} = 能级被黄金-Sturmian 非调和化的 primon 气体:自由玻色模(能级 v·ln p ⟹ ζ 之 Euler 因子)换成能级 β(v)·ln p;β(v) = √5v + 1/φ − {(v+1)φ}(闭式亲算),初段黄金幂 0, φ², φ³, φ⁴(成立域 = {v : F(v+1)=v}),v≥4 起 √5-线性正身;涨落 {(v+1)φ} 由三隙定理管辖(AxiomDebt D5-T0019 兑现处)。结构常数对榫:横坐标 1/φ²、结构极点 1/φ³、结构线 1/(2φ²) = 横坐标之半 = 形变自对偶中线(详 O5-PRESTUDY-Anatomy)。
**6.2 三重接口。** (a) §2.3 之会师问题:函数域为已证实验室(Weil 1948,定理级),O-5 为自建第二实验室——形变对偶跨度,证对照系守其线;(b) §5 之趋势+残差:germ 指数自身即"√5 趋势 + Sturmian 残差"结构,对榫第三次出现(读法级);(c) §4 之稳定性:B14(Kripke lfp)、S3/Quantum 不动代数、einselection 同属"稳定者居 Fix"家族(WM-R4 纪律:指认不加冕)。
**6.3 全树关系。** 黄金算术梯(单位群/桥/分裂律/GoldenApparition:加乘接口样本——素之入账时刻由 mod 5 户籍裁定)+ S1 相位/词层(三距)+ Weil/Zeros/Analytic 栈(LiCausalTrichotomy 冠顶)(读法级)读为汇于 O-5;O-5 为 O-6(Weil 正性纪念碑)之对照实验;主人先验(2026-07-16 在案:预期离线零点)下,对照实验两侧结果各自经独立 Lean 验证方入账——本卷仅提出对照假设,不由本卷产真。

## §7 去形式化候选清单(全部〔Lean可关〕候选;每靶 PR 前 mathlib 检索留痕,铸币禁令适用,评测搭真活)

| # | 靶 | 检验面/依赖 | 估价 |
|---|---|---|---|
| F1 | zeta-Gibbs 三本账:ln ζ 为对数配分、U = −ζ′/ζ = Σ Λ n^{−s}、最大熵刻画 | mathlib `riemannZeta`、Euler 积、`ArithmeticFunction.vonMangoldt`、LSeries 对数导数关系(在库与否留痕);PMF 机器 | 周~月 |
| F2 | 素指数独立性:zeta 分布下 v_p 独立几何 | Euler 积 + PMF 独立性;F1 之后自然续靶 | 周级+ |
| F3 | 熵证 Chebyshev(Kontoyiannis 路线) | 有限 Shannon 熵与次可加性(mathlib 熵件现状留痕);纯有限组合 + 对数不等式 | 周~月 |
| F4 | qubit 可预测性筛玩具:对角态于相位阻尼下熵产极小 | 直接续已冻 `phase_damping_fixed_iff_diagonal`;真需求,引擎候选 | 周级 |
| F5 | 正交性原理有限维形:最优线性预测残差正交/白 | mathlib 内积空间正交投影现成;§5 骨架之可冻核 | 周级 |
| F6 | o5-a/o5-b(指数账/收敛层) | 见 O5-PRESTUDY;T0019 三隙耦合(一债两用) | 周级起 |

排序建议:F4/F5(便宜、各自锚定 §4/§5)→ F1→F2(主脊)→ F3 → F6 随 O-5 主线。F1–F3 若 mathlib 已有对应件,按铸币禁令如实降格为搬运/引用。

## §8 审计记录(r1)

**已检索亲核**:Kontoyiannis(arXiv:0710.4076,及 Rissanen 文集 2008);zeta 分布独立性(Lin–Hu 2001;Golomb 1970);Atick–Redlich 1990/1992;Dan–Atick–Reid 1996(J. Neurosci. 16(10):3351–62);Srinivasan–Laughlin–Dubs 1982;Laughlin 1981;Pitkow–Meister 2012(Nat. Neurosci.);Field 1987;Olshausen–Field 1996;Bell–Sejnowski 1997;Brenner–Bialek–de Ruyter 2000;Logan 1977(BSTJ 56(4):487–510,精确假设与"唯一性≠可恢复性"及 Meyer 反例注记)。
**本卷亲算**:Fenchel–Young 之 ℕ 实例、U = −ζ′/ζ、β(v) 闭式与 v=0..4 表、黄金幂成立域 {F(v+1)=v}、apparition 双支机制、Pell 基变换。
**本卷勘误**:对话中"Logan 1977 可完全重构"表述收紧为"至乘常数唯一确定;唯一性不含稳健恢复;二维 Marr 猜想有 Meyer 反例"(§5.1)。
**待异模型审计清单(高危点标注)**:①【训】级全部年份/期刊(尤:Zurek–Habib–Paz 1993 出处;Barnum et al. 1996 no-broadcasting 精确陈述范围;Brandão–Piani–Horodecki 2015 定理的碎片极限精确形;Morrone–Burr 年份;Ditchburn–Ginsborg 1952 vs Riggs 1953 归属;Bost–Connes KMS 相图细节;Gallagher 条件依赖形;GUE 数方差量级表述;Denjoy 1931 出处);②§3 表逐行复核;③§6.1 结构常数与 Hearts 声明再对榫;④F1 之 mathlib LSeries 对数导数在库性。审计通过前,本卷不得作为任何冻结 PR 之依据引用。
**审计员**:Claude Fable 5(单模型);第二席审计后此节追加 r2 记录,旧行不改。

## §9 边界与所有权

①通篇热层;读法级各条禁作同构宣称,升格唯经 §7 检验面。②量子 Fenchel–Young 原轮与 KMS/Tomita 线属 loning Observer-quantum 母账,本卷仅引其数学内容,不代登记(v0.5 排除先例,账各记各的)。③独立性词典带实测汇率(e^{−γ}、Maier),不得当恒等式用。④平衡侧一元论不含时间之箭(创世条件另账)。⑤本卷入 trureturing 须经作者 data-only 归流;版本纪律:追加新节新行,旧行不改。

---

## §10 增订：素数观察者 × 量子观察者统一（2026-08-26）

**性质。** 本节及其后续全部为追加式理论增订，不改写 §1–§9。本文严格区分【Lean锚】、【纸证】与【路线】：前者只指仓库中已有 machine-checked 声明；中者指本文给出有限维或代数层面的直接证明；后者指尚需统一 API 或额外分析依赖才能进入 Lean kernel 的桥。本文不把素数拟人化，也不声称素数本身具有意识，更不声称“素数产生量子力学”。

### 10.1 两套观察者的共同骨架

素数观察者首先是一族局部接口

$$
q_{p,k}:X\to O_{p,k},
$$

其中 $p$ 是横向素数方向，$k$ 是同一素数内部的纵向精度。加入动力学 $T:X\to X$ 后，完整轨迹读出为

$$
q_{p,k}(T^t x).
$$

量子观察者则以有限维 Hilbert 空间 $\mathcal H$、状态 $\rho$、效果 $E$、instrument 分支 $\mathcal I_a$ 与量子通道 $\Phi$ 为底层，最基本的概率读出为

$$
\rho\longmapsto \operatorname{Tr}(\rho E).
$$

二者的共同问题不是“观察者是谁”，而是：

$$
\boxed{
\text{给定读出与允许协议后，哪些状态差异被消去，哪些附加实验足以恢复它们？}
}
$$

经典素数线用 kernel／等价关系表示不可区分；有限维量子线用可见 Hermitian 空间的正交补表示不可见状态差。二者共享同一反序原则：

$$
\boxed{
\text{读出族越丰富}\Longrightarrow\text{不可区分关系越小}.
}
$$

---

## §11 确定性素数读出是交换量子子理论

设 $X$ 为有限状态集，$q_i:X\to O_i$ 为任意有限确定性观察接口，其中 $i$ 可具体取 $(p,k)$。构造

$$
\mathcal H_X=\mathbb C^X
$$

及计算基 $\{|x\rangle:x\in X\}$。对有效输出 $o$ 定义

$$
P_{o|i}
=\sum_{x:q_i(x)=o}|x\rangle\langle x|.
$$

### 定理 11.1【纸证】（确定性接口的 PVM 实现）

对每个固定 $i$，有效输出上的 $\{P_{o|i}\}_o$ 构成投影值测量，并且对 basis state

$$
\rho_x=|x\rangle\langle x|
$$

有

$$
\operatorname{Tr}(\rho_xP_{o|i})
=\mathbf 1_{\{q_i(x)=o\}}.
$$

故

$$
q_i(x)=q_i(y)
\iff
\rho_x,\rho_y
\text{ 对第 }i\text{ 个测量不可区分}.
$$

**证明。** 不同输出对应 $q_i$ 的不交纤维，因此投影彼此正交；全部有效纤维分割 $X$，故投影和为单位。对计算基态取 Born 配对立即得到指示函数。$\square$

所有 $P_{o|i}$ 在同一计算基中对角，所以

$$
[P_{o|i},P_{o'|j}]=0.
$$

因此存在严格嵌入

$$
\boxed{
\text{finite deterministic prime observer}
\hookrightarrow
\text{finite commutative quantum observer}.
}
$$

反向不成立：一般量子观察者可以使用不交换效果、相位基、顺序 instrument 以及跨因子纠缠相关。

---

## §12 CRT 把素数局部坐标升级为量子张量因子

令

$$
M=\prod_{p\mid M}p^{k_p}.
$$

CRT 给出集合等价

$$
\mathbb Z/M\mathbb Z
\simeq
\prod_{p\mid M}\mathbb Z/p^{k_p}\mathbb Z.
$$

因此标准基诱导 Hilbert 空间酉等价

$$
\boxed{
\mathcal H_M
=\ell^2(\mathbb Z/M\mathbb Z)
\simeq
\bigotimes_{p\mid M}\mathcal H_{p^{k_p}}.
}
$$

其基映射为

$$
|n\bmod M\rangle
\longmapsto
\bigotimes_{p\mid M}|n\bmod p^{k_p}\rangle.
$$

【Lean锚】`D5/S3/ObserverMemory/PrimePowerTensorTower.lean` 已经在完整矩阵代数层证明相应 prime-power tensor factorization：有限窗口矩阵代数规范等价于全部素数幂矩阵因子的有限张量积。

这使“不同素数”在有限窗口量子模型中获得严格含义：它们不只是任意传感器标签，还可以成为量子可观测代数的 prime-primary tensor factors。

但必须立即保留边界：

$$
\boxed{
\text{observable algebra factorizes}
\not\Rightarrow
\rho=\bigotimes_p\rho_p.
}
$$

张量分解只给出系统组成，不强迫状态独立。一般全局态可以含跨素数经典相关与量子纠缠。

---

## §13 CRT 层析的三个模型层

### 13.1 基标签层

若先验只允许计算基态

$$
|n\bmod M\rangle,
$$

全部 prime-power residues

$$
(n\bmod p^{k_p})_{p\mid M}
$$

由 CRT 唯一恢复 $n\bmod M$。因此 CRT 对离散 basis identity 信息完备。

### 13.2 对角概率层

若

$$
\rho=\sum_{n\bmod M}\mu(n)|n\rangle\langle n|,
$$

完整联合 residue tuple 的 law 可以恢复整个 $\mu$。但若只分别保留每个素数因子的边缘 law，则仍可能丢失跨素数经典相关。

所以

$$
\boxed{
\text{joint CRT transcript}
\neq
\text{collection of one-prime marginals}.
}
$$

### 13.3 任意量子态层

若 $\rho$ 允许非对角项，则计算基 residue 测量只依赖 $\rho_{nn}$。例如

$$
|\psi_\pm\rangle
=\frac{|x\rangle\pm|y\rangle}{\sqrt2}
$$

具有不同相对相位，但全部纯 residue 测量概率相同。

当 $\dim\mathcal H_M=M$ 时，计算基对角 Hermitian 空间维数为 $M$，完整 Hermitian 空间维数为 $M^2$，因此仅 residue 测量的不可见方向维数至少为

$$
\boxed{M^2-M.}
$$

故

$$
\boxed{
\text{CRT 是经典标签层析，通常不是完整量子层析。}
}
$$

---

## §14 量子素数局部—全局余量

设

$$
\mathcal H
=\bigotimes_{j=1}^{r}\mathcal H_j,
\qquad
\dim\mathcal H_j=d_j=p_j^{k_j},
\qquad
D=\prod_jd_j.
$$

定义全部单素数约化读出

$$
\mathcal R_{\mathrm{loc}}(\rho)
=(\rho_1,\ldots,\rho_r),
$$

其中

$$
\rho_j=\operatorname{Tr}_{\widehat j}\rho.
$$

定义量子局部—全局余量

$$
\operatorname{QLGRes}
=\{(\rho,\sigma):\rho\neq\sigma,\ \rho_j=\sigma_j\ \forall j\}.
$$

### 定理 14.1【纸证】（单素数边缘不决定全局态）

若至少两个因子的维数不小于 $2$，则

$$
\operatorname{QLGRes}\neq\varnothing.
$$

**证明。** 在两个二维子空间中取

$$
|\Phi^\pm\rangle
=\frac{|00\rangle\pm|11\rangle}{\sqrt2}.
$$

二者是不同的正交全局态，但任一单边约化态均为 $I/2$。其余因子固定在同一纯态即可。$\square$

所以

$$
\boxed{
\text{知道每个素数因子的完整局部量子态}
\not\Rightarrow
\text{知道完整全局量子态}.
}
$$

这给出了 `FORMAL_PRIME_OBSERVER_DYNAMICS.md` 中“局部—全局余量”概念的一个真正量子实例。

---

## §15 跨素数相关扇区的正交分解

对每个因子分解

$$
\operatorname{Herm}(\mathcal H_j)
=\mathbb RI_j\oplus\operatorname{Herm}_0(\mathcal H_j).
$$

于是全局 Hermitian 空间有正交直和

$$
\boxed{
\operatorname{Herm}(\mathcal H)
=\bigoplus_{S\subseteq\{1,\ldots,r\}}
\left(\bigotimes_{j\in S}\operatorname{Herm}_0(\mathcal H_j)\right),
}
$$

未属于 $S$ 的因子放置单位方向。

其物理解释为：

- $S=\varnothing$：单位方向；
- $|S|=1$：单素数局部方向；
- $|S|=2$：双素数相关方向；
- $|S|\ge3$：高阶跨素数相关方向。

### 定理 15.1【纸证】（单素数观察的不可见维数）

只允许全部单因子 Hermitian 测量时，可见空间维数为

$$
1+\sum_{j=1}^{r}(d_j^2-1).
$$

因此迹零全局状态差空间中的不可见维数为

$$
\boxed{
D^2-1-\sum_{j=1}^{r}(d_j^2-1).
}
$$

不可见空间恰由所有 $|S|\ge2$ 的相关扇区组成。

于是可以把量子局部—全局余量严格识别为：

$$
\boxed{
\text{cross-prime correlation sectors}.
}
$$

---

## §16 $m$-素数观察层级

定义

$$
V_{\le m}
=\bigoplus_{|S|\le m}V_S.
$$

其维数为

$$
\boxed{
\dim V_{\le m}
=\sum_{|S|\le m}\prod_{j\in S}(d_j^2-1).
}
$$

因此得到层级：

$$
V_{\le1}\subseteq V_{\le2}\subseteq\cdots\subseteq V_{\le r}
=\operatorname{Herm}(\mathcal H).
$$

对应残差

$$
N_{>m}
=V_{\le m}^{\perp}
=\bigoplus_{|S|>m}V_S.
$$

这为素数观察者增加一个此前缺失的轴：

$$
\boxed{
\text{prime correlation order}.
}
$$

完整量子素数观察索引不应只写 $(p,k,t)$，而应允许

$$
(S,\mathbf k,t,b,a),
$$

其中 $S$ 是素数子集，$\mathbf k$ 是各因子精度，$b$ 是测量上下文，$a$ 是结果标签。

---

## §17 时间动力学可以把相关余量运输到局部可见方向

设基础观察者只能测单素数效果 $E_p$，系统通过通道 $\Phi$ 演化。时刻 $t$ 的 Heisenberg 效果为

$$
E_{p,t}=(\Phi^*)^t(E_p).
$$

若

$$
\Phi=\bigotimes_p\Phi_p
$$

是完全局部的乘积通道，则

$$
\Phi^*(E_p\otimes I_{\widehat p})
=\Phi_p^*(E_p)\otimes I_{\widehat p}.
$$

所以局部效果的全部时间轨道仍停留在单素数扇区。

### 定理 17.1【纸证】（纯局部动力学的相关盲区）

若所有允许初始效果均位于 $V_{\le1}$ 且 $\Phi^*(V_{\le1})\subseteq V_{\le1}$，则无限时间观察闭包仍满足

$$
V_\infty\subseteq V_{\le1},
$$

从而所有 $|S|\ge2$ 相关扇区永久不可见。

反之，若 $\Phi$ 含跨素数耦合，局部效果的 Heisenberg 演化可以生成联合效果：

$$
E_p\mapsto E_{p,q}\mapsto E_{p,q,r}\mapsto\cdots.
$$

因此 prime-time tomography 中的 time 不只是“多观察几次”，还可能是：

$$
\boxed{
\text{把高阶相关方向运输进当前可见空间的动力学资源}.
}
$$

---

## §18 Hamiltonian 支持传播与素数交互图

若封闭系统由 Hamiltonian

$$
H=\sum_SH_S
$$

驱动，其中 $H_S$ 只作用在素数集合 $S$ 上，局部可观测量 $A_R$ 只支撑在 $R$ 上，则

$$
\operatorname{supp}[H_S,A_R]\subseteq S\cup R.
$$

Heisenberg 方程

$$
\frac{dA}{dt}=i[H,A]
$$

说明可观测支持沿 Hamiltonian 相互作用超图传播。

### 原理 18.1

若素数交互图分成若干不连通分量，并且可测效果全部起始于某一分量，则交换子闭包不能跨越没有 Hamiltonian 边连接的分量。

因此图连通性是局部效果扩散到全局相关空间的一个结构必要条件，但一般不是充分条件；充分性还依赖生成的 Lie 代数是否足够大。

可定义一步跨素数耦合缺陷

$$
\boxed{
\Delta_\Phi(E)
=\|(I-\Pi_{\mathrm{loc}})\Phi^*(E)\|_{\mathrm{HS}},
}
$$

其中 $\Pi_{\mathrm{loc}}$ 是到单素数可见空间的正交投影。

$\Delta_\Phi(E)=0$ 表示一步演化保持局部性；$\Delta_\Phi(E)>0$ 则表示局部问题已经生成跨素数相关分量。

---

## §19 量子 finite prime-time tomography

【Lean锚】`D5/S3/Observer/Refinement/FinitePrimeTimeTomography.lean` 已证明：对有限状态空间 $X$，若全部索引与全部时间联合可分离，则存在有限索引集 $J$ 与有限时间深度 $m$ 已经分离。该 Lean 文件明确使用一般 `Nat` 索引，并没有强制索引为算术素数。

有限维量子情形有一个更强的线性版本，因为量子态集合虽然连续无穷，但状态差空间

$$
\operatorname{Herm}_d^0
$$

只有

$$
d^2-1
$$

个实维度。

对 prime-precision 测量效果 $E_{p,k,a}$ 定义中心化 Heisenberg 效果

$$
\widetilde E_{p,k,a,t}
=(\Phi^*)^t(E_{p,k,a})
-\frac{\operatorname{Tr}((\Phi^*)^t(E_{p,k,a}))}{d}I.
$$

### 定理 19.1【纸证】（量子有限 prime-time 证书）

若

$$
\operatorname{span}_{\mathbb R}
\{\widetilde E_{p,k,a,t}:p,k,a,t\}
=\operatorname{Herm}_d^0,
$$

则存在至多

$$
\boxed{d^2-1}
$$

个具体 prime-precision-time 效果已经张成整个迹零 Hermitian 空间。

**证明。** 从任意生成集抽取有限基即可。$\square$

令这些基效果的索引为 $(p_j,k_j,a_j,t_j)$。取有限素数—精度设置集合 $J$ 包含全部 $(p_j,k_j,a_j)$，再取

$$
T=1+\max_jt_j.
$$

则窗口 $J\times\{0,\ldots,T-1\}$ 已经信息完备。

因此

$$
\boxed{
\text{all-prime/all-precision/all-time quantum completeness}
\Longrightarrow
\text{finite prime-precision-time certificate}.
}
$$

与有限集合 compactness 版本不同，这里不要求量子状态集合有限；只要求 Hilbert 空间有限维。

---

## §20 横向素数与纵向精度必须严格分型

不同素数之间形成横向张量方向：

$$
\mathcal H_{p^k}\otimes\mathcal H_{q^\ell},
\qquad p\neq q.
$$

它们可以支持独立局部效果、联合效果和跨素数纠缠。

同一素数内部则有粗化塔

$$
\mathbb Z/p^{k+1}\mathbb Z\to\mathbb Z/p^k\mathbb Z.
$$

结果空间形成逆系统，而效果代数通过拉回形成正向嵌入：

$$
\mathcal A_{p,k}\hookrightarrow\mathcal A_{p,k+1}.
$$

所以

$$
\boxed{
\text{不同精度不是彼此独立的张量因子}.
}
$$

把 $k$ 层全部当成独立量子子系统会重复计算同一 $p$-进信息。

这保持了素数观察者理论原有的几何：

$$
\boxed{
\begin{aligned}
\text{horizontal prime axis}&=\text{independent/fusable local directions},\\
\text{vertical precision axis}&=\text{nested refinement tower}.
\end{aligned}
}
$$

---

## §21 zeta-weighted prime-time Gram 几何

【Lean锚】`D5/S3/Analytic/PrimeProducts/PrimePrecisionEntropyContraction.lean` 已证明 canonical prime-exponent channel 在 $s>1$ 时具有精确几何残余熵收缩：若 $q_p=p^{-s}$，则第 $k$ 层未解析熵满足

$$
R_{p,k}=q_p^kH_p,
$$

并且

$$
\boxed{R_{p,k+1}=q_pR_{p,k}.}
$$

这为 prime-precision 预算提供了一个已有 machine-checked 的纵向几何权重。

令

$$
Z_s=\sum_{p\in\mathbb P}p^{-s},
\qquad s>1.
$$

定义归一化 prime-precision 权重

$$
\nu_s(p,k)
=\frac{(1-p^{-s})p^{-s(k+1)}}{Z_s},
\qquad k\ge0.
$$

因为

$$
\sum_{k\ge0}(1-p^{-s})p^{-s(k+1)}=p^{-s},
$$

故

$$
\sum_{p,k}\nu_s(p,k)=1.
$$

再取时间几何权重

$$
\mu_\beta(t)=(1-\beta)\beta^t,
\qquad 0<\beta<1.
$$

对中心化效果

$$
e_{p,k,t}
=(\Phi^*)^t(E_{p,k})
-\frac{\operatorname{Tr}((\Phi^*)^t(E_{p,k}))}{d}I,
$$

定义 zeta-weighted prime-time Gram operator

$$
\boxed{
W_{s,\beta}
=\sum_{p,k,t}\nu_s(p,k)\mu_\beta(t)
|e_{p,k,t}\rangle\langle e_{p,k,t}|.
}
$$

这里把 $\operatorname{Herm}_d^0$ 视为 Hilbert–Schmidt 实内积空间。

### 定理 21.1【纸证/有限截断直接，完整级数为路线】

对任意状态差 $D$，形式上有

$$
\langle D,W_{s,\beta}D\rangle_{\mathrm{HS}}
=\sum_{p,k,t}\nu_s(p,k)\mu_\beta(t)
|\operatorname{Tr}(De_{p,k,t})|^2.
$$

所有权重严格正时，若该级数定义良好，则

$$
\boxed{
\ker W_{s,\beta}
=\bigcap_{p,k,t}
\ker\bigl[D\mapsto\operatorname{Tr}(De_{p,k,t})\bigr].
}
$$

所以

$$
W_{s,\beta}>0
$$

恰表示 weighted family 无不可见方向。

三个参数具有分离意义：

$$
\begin{aligned}
s&:\text{横向素数预算偏置},\\
k&:\text{同一素数的纵向精度},\\
\beta&:\text{时间深度折扣}.
\end{aligned}
$$

不应把某个特殊 $s$ 或 $\beta$ 未经额外证明解释成物理相变。

---

## §22 Frobenius 素数观察器的量子后处理不可恢复定理

【Lean锚】`D5/S3/Factorization/Galois/GaloisPrimeObserver.lean` 定义带 ramification tag 的 Frobenius 观察器

$$
O_{\mathrm{Frob}}(p)
\in\operatorname{Option}(\operatorname{ConjClasses}G)
$$

并证明：若共轭类输出有限且 ramified primes 有限，则存在某个共轭类 $c$，其 unramified prime fiber 为无限集。该文件还用显式反例审计了两个假设的必要性。

现在设任意量子编码

$$
\eta:
\operatorname{Option}(\operatorname{ConjClasses}G)
\to\mathsf S(\mathcal H),
$$

再接任意量子通道或测量签名 $\Sigma$。若

$$
O_{\mathrm{Frob}}(p)=O_{\mathrm{Frob}}(q),
$$

则

$$
\eta(O_{\mathrm{Frob}}(p))
=\eta(O_{\mathrm{Frob}}(q)),
$$

故全部下游量子统计相同。

### 定理 22.1【纸证】（后处理不恢复上游 kernel）

对任意映射 $f$、$g$：

$$
\ker f\subseteq\ker(g\circ f).
$$

应用于

$$
f=O_{\mathrm{Frob}},
\qquad
g=\Sigma\circ\eta,
$$

得到

$$
\boxed{
\ker O_{\mathrm{Frob}}
\subseteq
\ker(\Sigma\circ\eta\circ O_{\mathrm{Frob}}).
}
$$

因此量子后处理不能恢复已经在 Frobenius 共轭类压缩阶段丢掉的素数身份。

要破除同一 Frobenius fiber，只能加入绕过原压缩的新平行信息，例如另一个扩张的 Frobenius 数据、更细的局部结构或独立的 prime register；不能只对已有有限标签做更复杂的量子电路。

---

## §23 Frobenius 身份信息率趋零

令 $P_N$ 在 $p\le N$ 的素数中均匀取值。其身份熵为

$$
H(P_N)=\log\pi(N).
$$

若某 Frobenius 观察器最多有固定有限的 $r$ 个输出，则

$$
H(O_{\mathrm{Frob}}(P_N))\le\log r.
$$

因此

$$
\boxed{
\frac{H(O_{\mathrm{Frob}}(P_N))}{H(P_N)}
\le
\frac{\log r}{\log\pi(N)}
\longrightarrow0.
}
$$

这比“存在无限 fiber”更定量：固定有限 alphabet 的局部 Galois 观察，在越来越大的素数身份集合上保留的相对身份信息率趋于零。

注意它衡量的是“素数身份”相对于该有限标签的压缩，不意味着 Frobenius 共轭类作为算术不变量本身“信息很少”；对某些目标任务，共轭类可能已经充分。

---

## §24 三环二次角色形成交换量子观察代数

【Lean锚】`D5/S3/PrimeForms/Splitting/QuadraticCharacterProfileRedundancy.lean` 已证明：在 $(\mathbb Z/60\mathbb Z)^\times$ 上，Gaussian、Eisenstein、Golden 三个二次分裂角色生成全部二次角色；所有二次角色在三环画像纤维上常值，而每个画像纤维恰有两个元素。

令三角色为

$$
\chi_2,\chi_3,\chi_5.
$$

它们生成交换函数代数

$$
\mathcal A_{\mathrm{quad}}
=\operatorname{Alg}\langle\chi_2,\chi_3,\chi_5\rangle.
$$

把单位类 $u$ 编码为 basis state $|u\rangle$ 后，这些角色对应彼此交换的对角量子可观测量。

因此若

$$
\operatorname{triRingImage}(u)
=\operatorname{triRingImage}(v),
$$

则对所有

$$
A\in\mathcal A_{\mathrm{quad}}
$$

都有

$$
\langle u|A|u\rangle
=\langle v|A|v\rangle.
$$

### 原理 24.1

再加入任何仍通过该二次角色代数因子化的观察量，都不能切开既有二元素纤维。

这与量子“对角数据不能通过后处理制造缺失相位”完全平行：要打破纤维，必须加入一个不通过原观察代数因子化的新方向。

---

## §25 Galois fiber product 与量子 marginal fiber

【Lean锚】`D5/S3/Factorization/Galois/GaloisFusion.lean` 已证明：两个 Galois 子扩张的联合 restriction 必落在它们对共同交域 restriction 的 group fiber product 中；在适当正规、生成与线性无交条件下还可得到更强的联合分解。

量子系统有一个结构相似但不能直接等同的映射：

$$
\mathsf S(\mathcal H_A\otimes\mathcal H_B)
\longrightarrow
\mathsf S(\mathcal H_A)\times\mathsf S(\mathcal H_B),
$$

$$
\rho_{AB}\longmapsto(\rho_A,\rho_B).
$$

该映射对任意局部状态对是满的，因为 $\alpha\otimes\beta$ 总是一个全局扩张；但它一般不单射，因为纠缠态可以共享相同局部约化态。

因此量子局部—全局理论必须严格分开：

$$
\boxed{
\begin{aligned}
\text{local compatibility}&,\\
\text{global existence}&,\\
\text{global uniqueness}&.
\end{aligned}
}
$$

即使局部代数相互独立、交集仅为标量、联合生成完整全局代数，也不能推出给定局部状态唯一决定全局相关结构。

---

## §26 平行融合与串行压缩的 kernel 法则

设两个观察接口

$$
q_1:X\to O_1,
\qquad
q_2:X\to O_2.
$$

平行联合为

$$
q_\vee(x)=(q_1(x),q_2(x)),
$$

则

$$
\boxed{
\ker q_\vee=\ker q_1\cap\ker q_2.
}
$$

量子可见空间版本为

$$
V_{\mathfrak O_1\vee\mathfrak O_2}
=V_{\mathfrak O_1}+V_{\mathfrak O_2},
$$

故

$$
N_{\mathfrak O_1\vee\mathfrak O_2}
=N_{\mathfrak O_1}\cap N_{\mathfrak O_2}.
$$

相反，串行后处理

$$
X\xrightarrow{q}O\xrightarrow{f}Y
$$

满足

$$
\boxed{
\ker q\subseteq\ker(f\circ q).
}
$$

所以：

$$
\boxed{
\text{parallel new experiment can refine knowledge; serial postprocessing cannot resurrect lost distinctions.}
}
$$

这一区分是量子技术与素数观察结合时最重要的设计纪律之一。

---

## §27 prime-power Weyl 观察器：从 residue 到 phase

对局部 prime-power Hilbert 空间

$$
\mathcal H_{p^k}
=\ell^2(\mathbb Z/p^k\mathbb Z),
$$

定义 clock 与 shift：

$$
Z|x\rangle=\omega^x|x\rangle,
\qquad
X|x\rangle=|x+1\rangle,
$$

其中

$$
\omega=e^{2\pi i/p^k}.
$$

它们满足 Weyl 关系

$$
\boxed{ZX=\omega XZ.}
$$

$Z$ 的谱投影读取 residue／位置；$X$ 或 Fourier 基读取相位／频率。二者共同生成完整局部矩阵代数。

因此真正局部信息完备的 quantum prime observer 不能只读取

$$
n\bmod p^k.
$$

它必须加入不与 residue algebra 同时对角的 phase-sensitive contexts。

可以形成三层：

$$
\boxed{
\begin{aligned}
\text{arithmetic prime observer}&=\text{residue/clock sector},\\
\text{local quantum prime observer}&=\text{clock+shift+instrument words},\\
\text{global quantum prime observer}&=\text{local sectors+cross-prime correlations}.
\end{aligned}
}
$$

---

## §28 自适应素数—量子实验设计

【Lean锚】`D5/S3/ConceptDynamics/ExperimentDesign/ThreeStateAdaptiveEarlyStopping.lean` 已给出一个有限三状态模型：固定两实验方案和自适应提前停止方案都保持零错误识别；后者 worst-case 深度仍为 $2$，但在给定先验下平均实验数严格下降。

将动作推广为 prime-quantum 实验：

$$
a=(p,k,b,t,\mathcal I),
$$

分别表示素数、精度、测量上下文、演化时间与 instrument。对候选隐藏状态或候选通道参数 $\theta$，历史 $h_t$ 产生 posterior

$$
\pi_t(\theta)=P(\theta\mid h_t).
$$

策略根据 belief 选择下一实验：

$$
a_t=\pi_{\mathrm{policy}}(\pi_t).
$$

任务相对停止条件可取

$$
\operatorname{BayesRisk}(\pi_t)\le\varepsilon
$$

或

$$
\max_\theta\pi_t(\theta)\ge1-\varepsilon.
$$

量子情形必须区分两类实验资源：

1. 每次独立重新制备同一初态，再选择不同 prime-time effect；
2. 对同一个量子样本顺序测量。

第二种情况下前一次测量改变后续状态，因此完整历史概率必须由 instrument words 计算，而不能把不同时间概率简单当作同一个未扰动态上的独立样本。

---

## §29 统一余量塔

把算术与量子两条线合并后，应区分至少四类 residual：

### 29.1 算术读出余量

$$
R_{\mathrm{arith}}
=\{(x,y):q_{p,k}(x)=q_{p,k}(y)\ \forall p,k\}.
$$

### 29.2 量子 effect 余量

$$
N_{\mathrm{quant}}
=V_{\mathfrak O}^{\perp}.
$$

### 29.3 跨素数相关余量

$$
N_{\mathrm{corr}}
=\bigoplus_{|S|\ge2}V_S
$$

或任务限制下尚未被读取的高阶相关扇区。

### 29.4 动态协议余量

$$
N_{\mathrm{seq}}
=\left(\operatorname{span}\{F_w:w\text{ allowed protocol}\}\right)^\perp.
$$

对真正并行独立加入的接口，总余量由 kernel 交或可见空间和来计算；对串行压缩则必须直接计算复合映射 kernel，不能机械写成交。

### 原理 29.1（typed residual discipline）

$$
\boxed{
\text{不同 residual 可以同名“不可见”，但属于不同 carrier，不能无类型地求交。}
}
$$

形式化时必须登记每个 residual 的 carrier、pairing 与 comparison map。

---

## §30 素数完成与动力完成一般不交换

令 $C_{\mathrm{prime}}$ 表示加入更多 prime/precision 观察方向，$C_\Phi$ 表示在动力学下闭合全部 Heisenberg 轨道。

若

$$
\Phi^*(\mathcal A_p)\subseteq\mathcal A_p
$$

对每个 prime factor 成立，则局部 prime decomposition 被动力保持，两种完成在适当共同 carrier 上可以交换。

但若 $\Phi$ 含跨素数耦合，则

$$
\Phi^*(\mathcal A_p)\not\subseteq\mathcal A_p.
$$

此时时间闭包生成联合相关效果；若每一步又投影回纯局部 prime algebra，就会把这些新信息删除。

因此一般不应假定

$$
\boxed{
C_\Phi C_{\mathrm{prime}}
=C_{\mathrm{prime}}C_\Phi.
}
$$

其失败量可以由前述

$$
\Delta_\Phi(E)
=\|(I-\Pi_{\mathrm{loc}})\Phi^*(E)\|_{\mathrm{HS}}
$$

或多步闭包的局部外分量来定量。

---

## §31 统一 prime-quantum observer 定义

一个有限维 prime-quantum observer 可以组织为

$$
\boxed{
\mathfrak O_{PQ}
=(\mathcal H,\mathcal P,\mathcal K,\mathcal X,
\{\mathcal I_{a|p,k,x}\},\Phi,\mathcal A_M),
}
$$

其中：

- $\mathcal H$：全局 Hilbert 空间；
- $\mathcal P$：允许的 prime 或 prime-primary 因子；
- $\mathcal K$：各 prime 的精度层；
- $\mathcal X$：测量上下文；
- $\mathcal I_{a|p,k,x}$：结果分支 instrument；
- $\Phi$：观察间隔动力学；
- $\mathcal A_M$：稳定记录代数。

对重复制备型 prime-time 实验，签名为

$$
\Sigma_{PQ}(\rho)
=\left(
\operatorname{Tr}\bigl(\rho(\Phi^*)^tE_{a|p,k,x}\bigr)
\right)_{p,k,x,a,t}.
$$

其可见 operator system 为

$$
V_{PQ}
=\operatorname{span}_{\mathbb R}
\left\{I,(\Phi^*)^tE_{a|p,k,x}\right\}.
$$

不可见状态差为

$$
N_{PQ}=V_{PQ}^{\perp}.
$$

故

$$
\boxed{
\rho\sim_{PQ}\sigma
\iff
\rho-\sigma\in N_{PQ}.
}
$$

当

$$
V_{PQ}=\operatorname{Herm}(\mathcal H)
$$

时，prime-quantum observer 对申报实验族信息完备。

---

## §32 关键统一定理清单

### PQO-1【纸证】 确定性素数观察的交换量子实现

每个有限确定性 $q_i:X\to O_i$ 可由计算基 PVM 精确实现，且 basis-state kernel 完全一致。

### PQO-2【Lean锚+纸桥】 prime-power 量子张量分解

CRT/`PrimePowerTensorTower` 给出有限窗口 full matrix algebra 的 prime-primary tensor factorization。

### PQO-3【纸证】 单素数约化非单射

至少两个非平凡 prime factors 时，

$$
\rho\mapsto(\rho_p)_p
$$

一般不单射；Bell-type phase witness 给出显式 residual。

### PQO-4【纸证】 相关扇区分解

单素数可见空间之外的余量精确由 $|S|\ge2$ 的跨素数 Hermitian sectors 构成。

### PQO-5【纸证】 纯局部动力学不能完成全局相关层析

若 Heisenberg 动力保持单素数 operator system，则无限时间闭包仍无法进入高阶相关扇区。

### PQO-6【纸证】 有限量子 prime-time 证书

有限维全部 prime/precision/time 完备时，至多 $d^2-1$ 个中心化效果已经构成完备证书。

### PQO-7【纸证/级数路线】 zeta-weighted Gram kernel

严格正的 prime-precision-time 权重下，Gram operator 的 kernel 等于全部加权效果 pairing kernel 的交。

### PQO-8【Lean锚+纸桥】 Frobenius quantum postprocessing no-recovery

Frobenius 观察的 kernel 被任何只依赖其输出的量子编码与后处理 kernel 包含；已有无限 fiber 不会由下游量子化消失。

### PQO-9【Lean锚+纸桥】 quadratic-profile commutative no-go

全部二次角色均通过已有三环画像因子化时，任何仅由这些角色生成的对角量子观察仍保留同一二元素纤维。

### PQO-10【路线】 active prime-quantum completion

在有限候选模型、可计算 instrument law 与实验成本下，以 posterior belief 为状态的自适应 prime-quantum 策略应形成相应 Bellman/停止问题。

---

## §33 建议 Lean 模块树

```text
D5/S3/Quantum/PrimeObserver/
  DeterministicPrimeObserverEmbedding.lean
  PrimeIndexedEffectFamily.lean
  PrimePrecisionEffectTower.lean
  PrimeTimeVisibleSpace.lean
  FiniteQuantumPrimeTimeTomography.lean
  ZetaWeightedPrimeTimeGramian.lean

D5/S3/Quantum/PrimeTensor/
  CRTBasisTensorEquiv.lean
  PrimeLocalMarginalMap.lean
  PrimeLocalGlobalResidual.lean
  CorrelationSectorDecomposition.lean
  PrimeCorrelationOrder.lean

D5/S3/Quantum/PrimeDynamics/
  ProductChannelPreservesPrimeSupport.lean
  InteractionSupportPropagation.lean
  PrimeDynamicsCompletionDefect.lean
  PrimeCompletionNoncommutation.lean

D5/S3/Quantum/GaloisObserver/
  FrobeniusClassQuantumEncoding.lean
  FrobeniusPostprocessingNoRecovery.lean
  QuadraticProfileCommutativeNoGo.lean
  GaloisQuantumRestrictionFiber.lean

D5/S3/Quantum/PrimeActive/
  PrimeInstrumentAction.lean
  PrimeBeliefUpdate.lean
  AdaptivePrimeEarlyStopping.lean
```

建议优先顺序：

```text
1. DeterministicPrimeObserverEmbedding
2. CRTBasisTensorEquiv
3. PrimeLocalGlobalResidual
4. CorrelationSectorDecomposition
5. ProductChannelPreservesPrimeSupport
6. FiniteQuantumPrimeTimeTomography
7. FrobeniusPostprocessingNoRecovery
8. ZetaWeightedPrimeTimeGramian
```

前六项主要依赖有限维线性代数、现有 CRT/observer API 和矩阵迹 pairing；第七项是纯 kernel factorization 加现有 Frobenius theorem；第八项才需要较多可数求和与正算子收敛基础设施。

---

## §34 追加严格非主张

1. 本增订不声称素数本身具有意识、主观体验或物理测量能力。
2. 本增订不声称素数产生量子力学，或量子力学可以还原为模素数运算。
3. 本增订不声称 CRT 的经典唯一恢复自动给出任意量子态层析。
4. 本增订不声称矩阵代数的 prime-power tensor factorization 自动推出量子态是乘积态。
5. 本增订不声称全部单素数约化态决定全局纠缠或跨素数相位。
6. 本增订不声称不同 prime factors 的统计输出在一般纠缠态上条件独立。
7. 本增订不声称同一素数的不同 $p$-进精度层是独立张量因子。
8. 本增订不声称时间重复本身能消除静态 kernel；只有动力学将不可见方向运输到可见效果时，时间才增加可辨识维度。
9. 本增订不声称 interaction graph 连通自动推出完整量子可观测性。
10. 本增订不声称 $d^2-1$ 个效果一定可以作为单个 POVM 的 $d^2-1$ 个结果；这里是中心化效果方向的线性证书。
11. 本增订不声称 `FinitePrimeTimeTomography` 当前 Lean 索引已经限制为 `Nat.Primes`。
12. 本增订不声称 zeta-weighted Gramian 的任意参数值具有已证明的物理相变意义。
13. 本增订不声称 `PrimePrecisionEntropyContraction` 的熵权重就是唯一或最优量子实验预算。
14. 本增订不声称量子编码能够恢复上游 Frobenius 共轭类观察已经丢失的素数身份。
15. 本增订不声称有限 Frobenius 输出对所有算术任务都低效；任务相对充分性必须单独判断。
16. 本增订不声称三环二次画像的两元素 fiber 能被任何仍经二次角色代数因子化的后处理切开。
17. 本增订不声称 Galois fiber product 与量子 marginal fiber 是同一范畴对象；这里只比较局部—全局约束结构。
18. 本增订不声称局部约化 map 的满射性蕴含唯一 global extension。
19. 本增订不声称自适应 prime-quantum policy 在任意损失和成本下都优于静态设计。
20. 本增订不声称顺序测量可以忽略 back-action；同一量子样本必须使用 instrument word 计算。
21. 本增订不声称所有本文纸面定理已有同名 Lean proof term。
22. 本增订不声称本理论证明 RH、Born 规则来源、波函数唯一解释或其他公开开放问题。

---

## §35 最终统一：素数坐标、量子相位与观察完成

经典素数观察者解决的是局部算术坐标问题：

$$
\boxed{
\text{global discrete label}
\longrightarrow
\text{prime/prime-power local coordinates}.
}
$$

有限 CRT 在合适模型上告诉我们：足够的局部 residue 坐标可以恢复一个离散基标签。

量子观察者进一步问：

$$
\boxed{
\text{这些坐标之外，振幅之间还有哪些相位、相关与纠缠方向？}
}
$$

prime-primary tensor factorization 使该问题变得精确：不同素数因子提供局部 subsystem；单素数读出只覆盖 $|S|=1$ 的局部扇区；跨素数量子相关位于 $|S|\ge2$ 的不可见扇区。非局部动力学可以通过 Heisenberg 演化把这些高阶方向运输到局部可测 effect；纯局部动力学则不能。

因此统一链为

$$
\boxed{
\begin{aligned}
\text{prime arithmetic coordinates}
&\to\text{commuting residue observables},\\
\text{CRT prime-primary decomposition}
&\to\text{quantum tensor factors},\\
\text{local quantum effects}
&\to\text{one-prime visible sectors},\\
\text{entanglement/correlation}
&\to\text{local-global residual},\\
\text{Heisenberg interaction dynamics}
&\to\text{residual transport},\\
\text{prime-precision-time family}
&\to\text{finite-dimensional tomography},\\
\text{weighted Gram geometry}
&\to\text{robustness and experiment allocation},\\
\text{adaptive instruments}
&\to\text{task-relative active completion}.
\end{aligned}
}
$$

最严格的最终表述不是

$$
\text{“素数就是量子观察者”},
$$

而是

$$
\boxed{
\text{素数观察者给出局部算术坐标与精度塔；}
\text{量子观察者揭示这些坐标之上仍存在的非交换相位、跨素数相关与协议可见性。}
}
$$

因此两套理论真正共享的本体不是“素数”或“量子”这两个词，而是同一个观察完成问题：

$$
\boxed{
\text{给定有限接口后，识别剩余不可见方向，加入最小新实验，直到目标商上的状态差被完全分离。}
}
$$
