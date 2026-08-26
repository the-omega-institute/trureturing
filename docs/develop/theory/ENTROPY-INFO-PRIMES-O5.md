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
**4.2 视觉(编码端)。** 退相关 = 熵最大化的二阶投影:固定预算下不相关等方差最大化容量;自然图像 1/f² 强相关,中心-周边感受野 = 白化滤波(Atick–Redlich 1990/1992【检】);侧抑制 = 预测编码只传残差(Srinivasan–Laughlin–Dubs 1982【检】);实测:LGN 时域白化(Dan–Atick–Reid 1996, J. Neurosci. 16:3351–62【检】),直方图均衡逐点实现于蝇(Laughlin 1981【检】)。**枢纽:信息稳定与完全退相关对抗**——白化放大高频而高频信噪比最低;最优滤波随 SNR 滑动(亮带通/暗低通),真目标函数为 infomax(Linsker 1988【训】),退相关仅其无噪极限;Barlow 2001 自修订:冗余为纠错与结构之原料【训】;实测退相关是部分的(Pitkow–Meister 2012, Nat. Neurosci.【检】)。熵稳定由适应实现:增益控制/除法归一化钉住输出分布(Heeger 1992;Carandini–Heeger 2012【训】;适应性重标度最大化传输:Brenner–Bialek–de Ruyter 2000【检,连带】)。退相关 ≠ 独立:二阶花完剩非高斯性,稀疏编码/ICA 收割高阶(Olshausen–Field 1996;Bell–Sejnowski 1997【检,连带】)。
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

**性质**：本节及其后续全部为追加式理论增订，不改写 §1–§9。与仓库既有 Lean 证明直接对应者标为【Lean锚】，本文给出严格纸面证明但尚无同名 proof term 者标为【纸证】，依赖未来统一 carrier/API 者标为【路线】。本增订不把素数拟人化，也不声称素数“产生”量子力学。

### 10.1 两套观察者理论的共同骨架

素数观察者的基础接口是

$$
q_{p,k}:X\to O_{p,k},
$$

其中 $p$ 为素数方向，$k$ 为同一素数内部的精度。加入动力学 $T$ 后，读出为

$$
q_{p,k}(T^t x).
$$

量子观察者的基础接口是

$$
\rho\mapsto \operatorname{Tr}(\rho E),
$$

或更完整地由 instrument 分支

$$
\mathcal I_a
$$

产生概率、状态改变和后续顺序实验。

二者共同的问题不是“谁是意识”，而是：

$$
\boxed{
\text{哪些状态差异会被给定读出族消去，哪些协议足以恢复它们？}
}
$$

经典素数线用等价关系／kernel 表示不可区分；有限维量子线用可见 Hermitian 空间的正交补表示不可见状态差。二者都服从同一反序规律：

$$
\boxed{
\text{readout 越丰富}\Longrightarrow\text{indistinguishability 越小}.
}
$$

---

## §11 确定性素数读出是交换量子子理论

设 $X$ 为有限状态集，$q_i:X\to O_i$ 为任意有限确定性观察接口，其中 $i$ 可专门取 $(p,k)$。构造

$$
\mathcal H_X=\mathbb C^X
$$

及计算基 $\{|x\rangle:x\in X\}$。对输出 $o$ 定义

$$
P_{o|i}=\sum_{x:q_i(x)=o}|x\rangle\langle x|.
$$

**定理 11.1【纸证】**：对每个固定 $i$，有效输出上的 $\{P_{o|i}\}$ 构成 PVM；且对 basis state $\rho_x=|x\rangle\langle x|$，

$$
\operatorname{Tr}(\rho_xP_{o|i})
=
\mathbf1_{\{q_i(x)=o\}}.
$$

所以

$$
q_i(x)=q_i(y)
\iff
\rho_x,\rho_y
\text{ 对第 }i\text{ 个量子测量不可区分}.
$$

证明只需观察：不同纤维对应不相交的计算基投影，全部有效纤维分割 $X$。

进一步，所有这些投影共同对角，因此

$$
[P_{o|i},P_{o'|j}]=0.
$$

于是得到严格嵌入：

$$
\boxed{
\text{finite deterministic prime observer}
\hookrightarrow
\text{finite commutative quantum observer}.
}
$$

反向不成立：一般量子观察者可以测相位、使用不交换效果、顺序 instrument 和跨因子纠缠相关。

---

## §12 CRT 把素数局部坐标升级为量子张量因子

令

$$
M=\prod_{p\mid M}p^{k_p}.
$$

CRT 给出

$$
\mathbb Z/M\mathbb Z
\simeq
\prod_{p\mid M}\mathbb Z/p^{k_p}\mathbb Z.
$$

因此标准基诱导 Hilbert 空间等价

$$
\mathcal H_M
=\ell^2(\mathbb Z/M\mathbb Z)
\simeq
\bigotimes_{p\mid M}\mathcal H_{p^{k_p}},
$$

其 basis map 为

$$
|n\bmod M\rangle
\mapsto
\bigotimes_{p\mid M}|n\bmod p^{k_p}\rangle.
$$

【Lean锚】`D5/S3/ObserverMemory/PrimePowerTensorTower.lean` 已证明更强的完整矩阵代数等价：

$$
\boxed{
M_{\mathbb Z/M\mathbb Z}(\mathbb C)
\simeq
\bigotimes_{p\mid M}
M_{\mathbb Z/p^{k_p}\mathbb Z}(\mathbb C).
}
$$

因此“不同素数”在有限窗口上不只是传感器标签；它们确实对应可观测代数的 prime-power tensor factors。

但必须同时写下禁令：

$$
\boxed{
\text{observable algebra factorizes}
\not\Rightarrow
\rho=\bigotimes_p\rho_p.
}
$$

CRT 分解 carrier，不自动强迫量子态独立。只有乘积态配乘积效果时，Born 概率才分解为各素数概率的乘积。

---

## §13 CRT 层析的三个不同模型层

**基标签层。** 若先验只允许 $|n\rangle$，全部 prime-power residues 由 CRT 唯一恢复 $n\bmod M$，所以 CRT 对离散 basis identity 完备。

**对角概率层。** 若

$$
\rho=\sum_n\mu(n)|n\rangle\langle n|,
$$

完整联合 residue tuple 的 law 可以恢复 $\mu$；但只知道每个 prime factor 的边缘 law 仍不足以恢复跨素数经典相关。

**任意量子态层。** 计算基 residue PVM 只读对角项 $\rho_{nn}$。例如

$$
|\psi_\pm\rangle
=
\frac{|x\rangle\pm|y\rangle}{\sqrt2}
$$

具有完全相同 residue 统计，却有不同相对相位。若总 Hilbert 维数为 $M$，对角 Hermitian 空间维数仅为 $M$，完整 Hermitian 空间维数为 $M^2$，故纯 residue 静态读出的线性不可见维数为

$$
\boxed{M^2-M.}
$$

所以：

$$
\boxed{
\text{CRT 完备性是模型相对命题：}
\text{basis label 完备不等于 quantum-state 完备。}
}
$$

---

## §14 跨素数量子局部—全局余量

设

$$
\mathcal H=\bigotimes_{j=1}^r\mathcal H_j,
\qquad d_j=\dim\mathcal H_j,
\qquad D=\prod_jd_j.
$$

定义全部单素数约化画像

$$
\mathcal R_{\rm loc}(\rho)
=(\rho_1,\ldots,\rho_r),
$$

其中 $\rho_j=\operatorname{Tr}_{\widehat j}\rho$。

定义

$$
\operatorname{QLGRes}
=
\{(\rho,\sigma):\rho\neq\sigma,\ \rho_j=\sigma_j\ \forall j\}.
$$

**定理 14.1【纸证】**：若至少有两个因子维数不小于 $2$，则 $\operatorname{QLGRes}\neq\varnothing$。取两个因子的 Bell 态

$$
|\Phi^\pm\rangle
=\frac{|00\rangle\pm|11\rangle}{\sqrt2}
$$

并把其它因子固定为同一纯态即可；两个全局态不同，但每个单因子约化态相同。

因此：

$$
\boxed{
\text{知道每个 prime factor 的完整 reduced state}
\not\Rightarrow
\text{知道 global quantum state}.
}
$$

这就是素数观察者“局部—全局余量”在量子理论中的严格实例。

---

## §15 相关扇区分解与 $m$-prime 观察层级

每个因子有 Hilbert–Schmidt 正交分解

$$
\operatorname{Herm}(\mathcal H_j)
=\mathbb RI_j\oplus\operatorname{Herm}_0(\mathcal H_j).
$$

张量展开得到

$$
\operatorname{Herm}(\mathcal H)
=\bigoplus_{S\subseteq[r]}V_S,
$$

其中

$$
V_S
=
\left(\bigotimes_{j\in S}\operatorname{Herm}_0(\mathcal H_j)\right)
\otimes
\left(\bigotimes_{j\notin S}\mathbb RI_j\right).
$$

把 $|S|$ 称为 prime-correlation order。只允许全部单 prime observables 时，可见空间为

$$
V_{\le1}=V_\varnothing\oplus\bigoplus_{|S|=1}V_S,
$$

其维数为

$$
1+\sum_j(d_j^2-1).
$$

所以迹零全局状态差空间中的不可见维数为

$$
\boxed{
D^2-1-\sum_j(d_j^2-1).
}
$$

它恰由所有 $|S|\ge2$ 的高阶相关扇区组成。

更一般定义

$$
V_{\le m}=\bigoplus_{|S|\le m}V_S,
$$

$$
N_{>m}=\bigoplus_{|S|>m}V_S.
$$

于是量子化后的 prime observer 比原来的 $(p,k,t)$ 三轴多出第四轴：

$$
\boxed{S=\text{prime subset / correlation order}.}
$$

增加更多单 prime 传感器不能替代真正的 multi-prime correlation effects。

---

## §16 时间何时能把高阶相关搬进局部读出

设初始可见空间为所有单素数局部 observables。若动力学为乘积通道

$$
\Phi=\bigotimes_j\Phi_j,
$$

则

$$
\Phi^*(A_j\otimes I_{\widehat j})
=\Phi_j^*(A_j)\otimes I_{\widehat j}.
$$

因此所有时间轨道仍留在单 prime 空间。结论是：

$$
\boxed{
\text{pure local dynamics + pure local readout}
\Longrightarrow
\text{cross-prime residual persists for all time}.
}
$$

反之，若 Hamiltonian 含跨素数相互作用，局部 observable 的 Heisenberg 轨道可生成联合方向。若 $H_S$ 只作用于素数集合 $S$，$A_R$ 只作用于 $R$，则

$$
\operatorname{supp}[H_S,A_R]\subseteq S\cup R.
$$

所以嵌套交换子沿 interaction hypergraph 传播 observable support。

这里 time 不是“多等一会就自动获得信息”，而是一个动力资源：只有动力学把原本不可见的高阶扇区耦合进可见扇区时，时间层析才真正细化观察商。

连通 interaction graph 仍只是必要结构之一，不足以单独保证 full observability；对称性、守恒量、简并和 Lie closure 都可能留下 residual。

---

## §17 有限维 quantum prime-time certificate

【Lean锚】`D5/S3/Observer/Refinement/FinitePrimeTimeTomography.lean` 已证明：有限状态 carrier 上，若全部 `Nat` 索引与全部时间联合分离，则存在有限索引集与有限时间窗口已经分离。该文件明确说明其索引并未强制为真实素数。

量子有限维情形有另一种更强的有限化机制。令真实算术索引

$$
i=(p,k,b,a)
$$

表示素数、精度、测量上下文和结果效果。定义中心化 Heisenberg 效果

$$
\widetilde E_{i,t}
=(\Phi^*)^t(E_i)
-\frac{\operatorname{Tr}((\Phi^*)^t(E_i))}{d}I.
$$

若

$$
\operatorname{span}\{\widetilde E_{i,t}:i,t\}
=\operatorname{Herm}_d^0,
$$

那么从该生成族抽取一个基即可得到至多

$$
\boxed{d^2-1}
$$

个具体 $(i,t)$ 形成完备证书。令 $J$ 为这些索引的有限集合、$T=1+\max t$，则 $J\times\{0,\ldots,T-1\}$ 已信息完备。

所以：

$$
\boxed{
\text{all-prime/all-precision/all-time quantum completeness}
\Longrightarrow
\text{finite experimental certificate}.
}
$$

这里状态集合仍连续无穷；有限化来自 $\dim\operatorname{Herm}_d^0=d^2-1$，不是来自状态数有限。

---

## §18 素数精度熵与 zeta-weighted Gram 几何

【Lean锚】`D5/S3/Analytic/PrimeProducts/PrimePrecisionEntropyContraction.lean` 已证明：对 $s>1$ 和素数 $p$，canonical prime-exponent geometric channel 在增加一层精度后，未解析尾部熵精确乘以

$$
p^{-s}.
$$

这是一条算术概率通道定理，不是量子退相干定律。

为了把横向素数、纵向精度和时间预算统一到量子观测几何，可定义：

$$
Z_s=\sum_pp^{-s},
$$

$$
\nu_s(p,k)
=\frac{(1-p^{-s})p^{-s(k+1)}}{Z_s},
\qquad k\ge0,
$$

则

$$
\sum_{p,k}\nu_s(p,k)=1.
$$

再取时间折扣

$$
\mu_\beta(t)=(1-\beta)\beta^t,
\qquad0<\beta<1.
$$

对中心化效果 $e_{p,k,t}$ 定义

$$
W_{s,\beta}
=\sum_{p,k,t}\nu_s(p,k)\mu_\beta(t)
|e_{p,k,t}\rangle\langle e_{p,k,t}|.
$$

在有限维且效果一致有界时级数收敛，并满足

$$
\langle D,W_{s,\beta}D\rangle
=\sum_{p,k,t}\nu_s(p,k)\mu_\beta(t)
|\operatorname{Tr}(De_{p,k,t})|^2.
$$

因为全部权重严格正，

$$
\boxed{
\ker W_{s,\beta}
=\bigcap_{p,k,t}
\ker[D\mapsto\operatorname{Tr}(De_{p,k,t})].
}
$$

于是 $W_{s,\beta}$ 正定恰好对应全部 prime-precision-time 效果完备；其最小特征值衡量该预算下最难看见的状态方向。

严格边界：$p^{-s}$ 在这里是与仓库精度熵结构相容的实验权重模型，不是量子理论强迫的物理常数；任何特殊 $s$ 值都不能未经额外定理解释成物理临界点。

---

## §19 Frobenius 量子后处理不可恢复定理

【Lean锚】`D5/S3/Factorization/Galois/GaloisPrimeObserver.lean` 定义未分歧素数的 Frobenius 共轭类观察，并证明：若共轭类输出有限、分歧素数有限，则至少一个 Frobenius class fiber 含无限多个素数；同时显式审计两个有限性假设不可无条件删除。

令

$$
O_{\rm Frob}(p)
\in\operatorname{Option}(\operatorname{ConjClasses}G)
$$

为该读出。再令任意量子编码

$$
\eta:O\to\mathsf S(\mathcal H)
$$

和任意后续量子观察签名

$$
\Sigma:\mathsf S(\mathcal H)\to Y.
$$

复合接口为

$$
Q=\Sigma\circ\eta\circ O_{\rm Frob}.
$$

**定理 19.1【纸证】**：

$$
\boxed{
\ker O_{\rm Frob}\subseteq\ker Q.
}
$$

证明只用函数复合：上游已经相等的两个输出，经任意编码与量子后处理后仍相等。

所以：

$$
\boxed{
\text{量子计算不能恢复已经被 Frobenius class map 删除的 prime identity。}
}
$$

要区分同一 class 中的不同素数，必须增加绕过该粗标签的新平行信息源，如另一个扩张、新局部系数、素数幂精度或直接依赖 $p$ 的 effect。

---

## §20 有限输出素数观察器的相对身份信息率趋零

令 $P_N$ 在 $\{p\le N:p\text{ prime}\}$ 上均匀分布。则

$$
H(P_N)=\log\pi(N).
$$

若某 prime observer 的输出 alphabet 大小固定为 $r<\infty$，则

$$
H(O(P_N))\le\log r.
$$

所以

$$
\boxed{
\frac{H(O(P_N))}{H(P_N)}
\le
\frac{\log r}{\log\pi(N)}
\to0.
}
$$

该结论比“存在无限 fiber”更定量，但它只讨论**素数身份信息率**，不否认有限 Frobenius 输出可能完整表达所研究扩张的分裂性质。

故必须区分：

$$
\boxed{
\text{property information}\neq\text{identity information}.
}
$$

---

## §21 三环二次角色是交换量子观察代数

【Lean锚】`D5/S3/PrimeForms/Splitting/QuadraticCharacterProfileRedundancy.lean` 已证明，在 $(\mathbb Z/60\mathbb Z)^\times$ 上，Gaussian、Eisenstein、Golden 三个分裂角色生成全部二次角色；任意二次角色都在三环画像 fiber 上常值，而每个 fiber 恰有两个单位类。

把单位类 $u$ 编码成 basis state $|u\rangle$，三个角色成为共同对角的量子可观测量。令 $\mathcal A_{\rm quad}$ 为它们生成的交换对角代数。

若 $u,v$ 有相同三环画像，则对所有

$$
A\in\mathcal A_{\rm quad}
$$

都有

$$
\langle u|A|u\rangle
=\langle v|A|v\rangle.
$$

所以再增加任何只由既有二次角色组合得到的经典或量子后处理，都不能破除那两个元素的 fiber。

这与量子相位缺失服从同一个数据处理原则：

$$
\boxed{
\text{下游计算能重组保留的信息，不能创造上游 quotient 已删除的坐标。}
}
$$

---

## §22 Galois fiber product 与 quantum marginal fiber

【Lean锚】`D5/S3/Factorization/Galois/GaloisFusion.lean` 已证明两个子扩张的联合限制必须满足共同交域上的 fiber-product 兼容约束，并在适当生成、正规与线性无交条件下给出更强限制分解。

量子复合系统有一个结构相似但唯一性性质不同的映射：

$$
R:\mathsf S(\mathcal H_A\otimes\mathcal H_B)
\to\mathsf S(\mathcal H_A)\times\mathsf S(\mathcal H_B),
$$

$$
R(\rho_{AB})=(\rho_A,\rho_B).
$$

它是满射，因为任意 $(\alpha,\beta)$ 至少由乘积态 $\alpha\otimes\beta$ 实现；但当两个因子均非平凡时，它不是单射，Bell states 提供显式 fiber。

所以 local-to-global 逻辑必须永久分成：

$$
\boxed{
\text{compatibility}\neq\text{existence}\neq\text{uniqueness}.
}
$$

Galois restriction 与 quantum marginal 不是同一对象；这里只统一它们“局部数据是否能够胶合及是否唯一”的问题形状。

---

## §23 平行融合与串行后处理的 kernel 方向相反

对两个平行接口

$$
q_1:X\to O_1,
\qquad q_2:X\to O_2,
$$

联合读出 $q=(q_1,q_2)$ 满足

$$
\boxed{
\ker q=\ker q_1\cap\ker q_2.
}
$$

量子线性版是

$$
V_{1\vee2}=V_1+V_2,
\qquad
N_{1\vee2}=N_1\cap N_2.
$$

反之，串行后处理

$$
X\xrightarrow qO\xrightarrow fY
$$

满足

$$
\boxed{
\ker q\subseteq\ker(f\circ q).
}
$$

所以“量子化”只有在提供新的**平行 effect directions、joint contexts 或 dynamical protocols**时才会提升 prime observer 能力；若只是把一个已压缩的 Frobenius/profile 标签送入量子电路，它仍只是串行后处理。

---

## §24 横向素数与纵向精度不可混成 tensor factors

不同素数在有限 CRT 窗口上是真正横向因子：

$$
\mathcal H_{p^kq^\ell}
\simeq\mathcal H_{p^k}\otimes\mathcal H_{q^\ell}.
$$

但同一素数内部是精度粗化塔：

$$
\cdots\to\mathbb Z/p^{k+1}\mathbb Z
\to\mathbb Z/p^k\mathbb Z\to\cdots.
$$

地址／状态侧形成逆系统，而 observable 通过拉回形成正向递增塔：

$$
\boxed{
\mathcal A_{p,k}\hookrightarrow\mathcal A_{p,k+1}.
}
$$

因此：

$$
\boxed{
\text{state/output precision tower is inverse,}
\quad
\text{effect tower is direct}.
}
$$

把 $k$ 与 $k+1$ 当成独立 tensor factors 会重复计数同一 $p$-进信息。

---

## §25 prime Weyl observer：residue 与 phase 的最小非交换扩展

固定 $N=p^k$，在

$$
\mathcal H_N=\ell^2(\mathbb Z/N\mathbb Z)
$$

上定义

$$
Z|x\rangle=\omega^x|x\rangle,
\qquad
X|x\rangle=|x+1\rangle,
\qquad
\omega=e^{2\pi i/N}.
$$

满足

$$
\boxed{ZX=\omega XZ.}
$$

$Z$ 的谱投影读取 residue／计算基地址；$X$ 在 Fourier 基中对角，能够读取单纯 residue statistics 看不到的相位方向。

只使用 $Z$ 的谱投影，静态可见 Hermitian 空间只是对角空间；$X,Z$ 则生成完整局部矩阵代数。

必须保留一条重要边界：

$$
\boxed{
\text{algebra-generated complete}
\not\Rightarrow
\text{one fixed POVM is informationally complete}.
}
$$

静态层析看 effect 的线性 span；顺序层析看允许 instrument words 的 word-effect span。

---

## §26 主动 prime–quantum 实验与停止

【Lean锚】`D5/S3/ConceptDynamics/ExperimentDesign/ThreeStateAdaptiveEarlyStopping.lean` 给出一个有限经典见证：固定方案总执行两次实验，而保持零错误识别的自适应树在给定先验下平均成本为

$$
1+2\varepsilon<2.
$$

这证明自适应提前停止可以降低某些 observer 模型的平均成本，但不自动证明量子优势。

完整 prime–quantum 实验动作至少应写成

$$
\boxed{
a_t=(p_t,k_t,b_t,\mathcal I_t,\tau_t),}
$$

其中依次选择 prime、precision、measurement basis/context、instrument 和演化时间。

若候选状态／模型为 $\theta$，历史后验为

$$
\pi_t(\theta)=P(\theta\mid h_t),
$$

则 policy 可以在 belief 上选择下一实验并决定停止。

必须区分 fresh-copy protocol 与 sequential single-system protocol：前者每次重新制备相同初态，适合 Heisenberg effect family 层析；后者对同一个量子样本连续作用，早期测量改变后续状态，必须使用 instrument words。

最重要的操作边界仍是：

$$
\boxed{
\text{adaptive choice of measurement setting}
\neq
\text{choice of Born outcome}.
}
$$

---

## §27 typed residual discipline

合并两套理论后至少存在四类不同 residual，不能把它们无类型转换地混成一个“隐藏信息”。

1. **算术 kernel**：
$$
R_{\rm arith}=\{(x,y):q_{p,k}(x)=q_{p,k}(y)\ \forall(p,k)\}.
$$
它是状态对上的关系。

2. **量子线性 residual**：
$$
N_{\rm quant}=V_\mathfrak O^\perp\subseteq\operatorname{Herm}_d^0.
$$
它是状态差向量子空间。

3. **correlation residual**：
$$
N_{\rm corr}=\bigoplus_{|S|>m}V_S.
$$
它按 multi-prime support 分层。

4. **sequential residual**：
$$
N_{\rm seq}=\left(\operatorname{span}\{F_w:w\text{ allowed}\}\right)^\perp.
$$
它依赖 instrument protocol language。

平行加入接口时，kernel 取交、可见空间取 span；串行管道时必须计算复合 kernel。该 typed discipline 是后续 Lean 化的必要前置，否则极易把 setoid、线性子空间、相关阶和协议等价混成同一类型。

---

## §28 prime completion 与 dynamics completion 一般不交换

令 $\mathcal A_{\rm loc}$ 为当前单 prime 可见空间，$\Pi_{\rm loc}$ 为 Hilbert–Schmidt 正交投影到该空间。

若

$$
\Phi^*(\mathcal A_{\rm loc})\subseteq\mathcal A_{\rm loc},
$$

则时间闭包不会生成新跨素数方向；在更强的逐 prime 不变条件下，先做 prime-local completion 再做 time closure 与分别 time closure 后联合具有相同生成空间。

若存在局部效果 $E$ 使

$$
\Phi^*(E)\notin\mathcal A_{\rm loc},
$$

则动力学把局部问题搬进了相关扇区。定义一步耦合缺陷

$$
\boxed{
\Delta_\Phi(E)
=\|(I-\Pi_{\rm loc})\Phi^*(E)\|_{\rm HS}.
}
$$

则 $\Delta_\Phi(E)=0$ 当且仅当该效果一步演化后仍完全局部。

该量只度量“local question 向 cross-prime observable sector 的泄漏”，不声称它是标准 entanglement measure，也不声称它直接度量因果强度。

---

## §29 统一 prime–quantum observer

定义有限维 prime–quantum observer

$$
\mathfrak{PQO}
=\left(
\mathcal H,
\{\mathcal H_{p^k}\},
\{\mathcal I_{a|p,k,b}\},
\Phi,
\mathcal W,
\Lambda
\right),
$$

其中 $\mathcal W$ 为允许顺序实验词语言，$\Lambda$ 为实际记录账本。对每个允许词 $w$ 定义 word effect $F_w$，并令

$$
V_{\mathfrak{PQO}}
=\operatorname{span}_{\mathbb R}\{I,F_w:w\in\mathcal W\},
$$

$$
N_{\mathfrak{PQO}}
=V_{\mathfrak{PQO}}^\perp.
$$

于是对任意状态

$$
\boxed{
\rho\sim_{\mathfrak{PQO}}\sigma
\iff
\rho-\sigma\in N_{\mathfrak{PQO}}.
}
$$

并且

$$
\boxed{
\mathfrak{PQO}\text{ 信息完备}
\iff
V_{\mathfrak{PQO}}=\operatorname{Herm}(\mathcal H).
}
$$

有限维完备时，中心化允许 word effects 中存在至多 $d^2-1$ 个构成有限完备证书。

由此得到层级：

$$
\text{deterministic prime observer}
\subset
\text{commutative quantum prime observer}
\subset
\text{local noncommutative prime observer}
\subseteq
\text{global prime–quantum observer}.
$$

是否严格取决于 carrier 非平凡性和实际允许的 effect/instrument 集。

---

## §30 本增订 Lean 锚点与建议形式化路线

本增订直接复用而不扩大解释范围的锚点包括：

- `D5/S3/Observer/Refinement/FinitePrimeTimeTomography.lean`：有限状态的有限 prime-time witness；
- `D5/S3/ObserverMemory/PrimePowerTensorTower.lean`：prime-power full-matrix tensor factorization；
- `D5/S3/Factorization/Galois/GaloisPrimeObserver.lean`：Frobenius observer 与 infinite fiber；
- `D5/S3/Factorization/Galois/GaloisFusion.lean`：Galois restriction fiber product；
- `D5/S3/Analytic/PrimeProducts/PrimePrecisionEntropyContraction.lean`：精度熵精确收缩；
- `D5/S3/PrimeForms/Splitting/QuadraticCharacterProfileRedundancy.lean`：三环二次角色冗余与两元素 fiber；
- `D5/S3/ConceptDynamics/ExperimentDesign/ThreeStateAdaptiveEarlyStopping.lean`：自适应提前停止平均成本优势；
- `D5/S3/Quantum/*` 与 `D5/S3/Observer/*` 中既有 Born、decoherence、tomography、conditioning、CHSH、observer metric 等锚点。

建议新增：

```text
D5/S3/Quantum/PrimeObserver/
  DeterministicPrimeObserverEmbedding.lean
  PrimeIndexedEffectFamily.lean
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

D5/S3/Quantum/GaloisObserver/
  FrobeniusPostprocessingNoRecovery.lean
  QuadraticProfileCommutativeNoGo.lean
```

优先闭合顺序：

$$
\boxed{
\text{deterministic embedding}
\to
\text{CRT tensor bridge}
\to
\text{local–global residual}
\to
\text{finite quantum prime-time theorem}
\to
\text{weighted Gram geometry}.
}
$$

---

## §31 严格非主张

①不声称素数产生量子力学，或素数本身具有意识。②不声称任意量子系统都天然具有唯一 prime-power 物理分解。③不声称矩阵代数 CRT 分解自动意味着状态乘积、统计独立或无纠缠。④不声称全部单 prime reduced states 唯一决定 global state。⑤不声称所有 cross-prime residual 都是 entanglement；经典相关也位于高阶扇区。⑥不声称增加更多单 prime observables 可以替代 multi-prime effects。⑦不声称时间演化必然增加可见性。⑧不声称 interaction graph 连通足以保证层析完备。⑨不声称现有 `FinitePrimeTimeTomography` 已直接证明本文量子有限证书；二者有限化机制不同。⑩不声称 zeta-weighted Gramian 是量子力学唯一自然权重。⑪不声称 $s$ 或 $\beta$ 特殊值构成物理临界点。⑫不声称 prime precision entropy contraction 是量子退相干定律。⑬不声称 Frobenius 量子编码恢复 class map 已删除的 prime identity。⑭不声称有限输出身份信息率趋零表示其算术性质信息无价值。⑮不声称 Galois fiber product 与 quantum marginal fiber 是同一数学对象。⑯不声称不同 $p$-进精度层是独立 tensor factors。⑰不声称 clock–shift 代数生成完整等价于固定 POVM 信息完备。⑱不声称自适应 prime–quantum protocol 自动优于所有静态方案。⑲不声称观察者能通过选择 instrument 来选择 Born outcome。⑳本文新增纸面定理在 proof term、依赖闭包与 admission 完成前不得标记为 Lean-closed。

---

## §32 最终收束：素数给坐标，量子给非交换可见性，动力学决定局部能否完成全局

本增订的最终统一式是：

$$
\boxed{
\begin{aligned}
\text{prime index}
&=\text{局部算术寻址},\\
\text{prime precision}
&=\text{同一局部坐标的纵向精化},\\
\text{CRT tensorization}
&=\text{有限窗口 observable carrier 的横向分解},\\
\text{quantum state}
&=\text{允许跨这些因子保存相位、相关与纠缠的全局对象},\\
\text{local effect}
&=\text{单 prime 可执行问题},\\
\text{correlation effect}
&=\text{multi-prime 联合问题},\\
\text{dynamics}
&=\text{把 observable support 在相关扇区之间运输的机制},\\
\text{completion}
&=\text{允许协议生成的 effect 闭包},\\
\text{residual}
&=\text{与该闭包正交、因此仍不可区分的状态差}.
\end{aligned}
}
$$

经典 CRT 的正确结论是：

$$
\boxed{
\text{局部素数坐标可以恢复一个离散 basis label。}
}
$$

量子 local–global residual 的新增结论是：

$$
\boxed{
\text{同样的局部坐标并不足以恢复振幅之间的相位、相关与纠缠。}
}
$$

所以 quantum observer theory 不是 prime observer theory 的替代，而是它在非交换和全局相关方向上的严格扩展。

另一方面，Frobenius 与 quadratic-profile 结果提供数据处理边界：

$$
\boxed{
\text{若算术接口已经把多个对象压成同一标签，}
\text{任何只依赖该标签的下游量子计算都不能恢复被删坐标。}
}
$$

真正减少余量的只能是新的平行信息：新 prime/precision、新扩张、新非交换测量上下文、新联合相关 effect，或能够把不可见相关搬运到可见方向的动力学。

因此完整 prime–quantum observer completion 的流程是：

$$
\boxed{
\text{choose arithmetic local coordinates}
\to
\text{close the quantum effect family}
\to
\text{add required correlation order}
\to
\text{propagate by allowed dynamics}
\to
\text{measure the remaining residual}
\to
\text{extract a finite certificate in finite dimension}.
}
$$

更短地：

$$
\boxed{
\text{局部坐标决定在哪里问，}
\text{量子上下文决定能够问什么，}
\text{动力学决定隐藏全局关系能否被搬到答案里，}
\text{completion 的终点由 residual 是否归零决定。}
}
$$
