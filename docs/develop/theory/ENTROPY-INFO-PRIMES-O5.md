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
