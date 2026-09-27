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

## §10 可恢复综合征的熵增加与相对可区分性

### 定义 10.1：显式可恢复量子记录

取有限非零逻辑空间$L=\mathbb C^d$和物理空间$H=\mathbb C^n$。给定有限非空指标集$I_{\mathrm{syn}}$上的矩阵$S_j:L\to H$，满足

$$
S_j^\dagger S_k=\delta_{jk}I_d.
$$

令$P=\sum_jS_jS_j^\dagger$，给定密度矩阵$\sigma$和固定逻辑密度态$\tau_0$，定义

$$
\mathcal E_\sigma(\rho)=\sum_{j,k}\sigma_{jk}S_j\rho S_k^\dagger,
\qquad
\mathcal D(X)=\sum_jS_j^\dagger XS_j+
\operatorname{tr}[(I-P)X]\tau_0.
\tag{10.1}
$$

采用有限von Neumann熵$S(\rho)=-\operatorname{tr}\rho\log\rho$，零本征值项按连续极限取零；相对熵为$D(\rho\|\tau)=\operatorname{tr}\rho(\log\rho-\log\tau)$，要求$\operatorname{supp}\rho\subseteq\operatorname{supp}\tau$，否则取$+\infty$。对数取自然底。这里的环境综合征态$\sigma$与未知逻辑输入无关。

### 定理 10.2：额外熵与完全恢复可以同时成立

式(10.1)的两个映射均为CPTP，$\mathcal D\mathcal E_\sigma=\mathrm{id}$，且

$$
\boxed{S(\mathcal E_\sigma(\rho))=S(\rho)+S(\sigma).}
\tag{10.2}
$$

对同一综合征态编码的任意逻辑态$\rho,\tau$，有

$$
\boxed{D(\mathcal E_\sigma(\rho)\|\mathcal E_\sigma(\tau))=D(\rho\|\tau).}
\tag{10.3}
$$

因此完整输出熵的严格增加，不能单独证明逻辑信息已不可恢复。本定理给本卷§4的信息搬移叙述一个有限、带明确访问权限的实现；它不把任意环境耦合都判成可恢复。

**证明。** 定义$J:L\otimes\mathbb C^{|I_{\mathrm{syn}}|}\to H$为$J(v\otimes|j\rangle)=S_jv$。正交关系给出$J^\dagger J=I$和$JJ^\dagger=P$，故$\mathcal E_\sigma(\rho)=J(\rho\otimes\sigma)J^\dagger$为CPTP。$\mathcal D$第一项的Kraus为$S_j^\dagger$，其Kraus平方和为$P$；第二项是正效果$I-P$后制备$\tau_0$，补足保迹条件。矩阵乘法给出

$$
\sum_iS_i^\dagger\mathcal E_\sigma(\rho)S_i
=\sum_i\sigma_{ii}\rho=\rho,
$$

且编码支持在$P$，所以补项为零。

设$\rho$与$\sigma$的本征值分别为$r_a,s_b$。编码的非零本征值为$r_as_b$，因此

$$
-\sum_{a,b}r_as_b\log(r_as_b)
=-\sum_ar_a\log r_a-\sum_bs_b\log s_b.
$$

得到(10.2)。在各自支持上，$\log(\rho\otimes\sigma)=\log\rho\otimes I+I\otimes\log\sigma$。相对熵中综合征对数项相消，迹的乘法性和等距性给出(10.3)；支持不包含时两侧同时为无穷。∎

此正规形的普遍可逆通道背景见Knill–Laflamme及Nayak–Sen。[QREC-KL][QREC-NS] 这里给出的熵计算不依赖原§1至§9中尚未核对的数论或物理类比。

### 定理 10.3：恢复器可由噪声数据显式计算

给定$\mathcal N(X)=\sum_aE_aXE_a^\dagger$且$\sum_aE_a^\dagger E_a=I_d$。计算

$$
Q=\mathcal N(I_d),\quad P=\operatorname{supp}Q,\quad
W=Q^{[-1/2]},\quad
c_{ab}=\operatorname{tr}(E_a^\dagger E_b)/d,
$$

其中$Q^{[-1/2]}$在正谱上取逆平方根、在零谱上取零。映射

$$
\boxed{\mathcal R_\mathcal N(X)=\sum_aE_a^\dagger WXWE_a+
\operatorname{tr}[(I-P)X]\tau_0}
\tag{10.4}
$$

总是CPTP，并且它精确反演$\mathcal N$，当且仅当存在任一CPTP逆，当且仅当

$$
E_a^\dagger E_b=c_{ab}I_d\quad\forall a,b.
\tag{10.5}
$$

**证明。** 支持部分的Kraus为$E_a^\dagger W$，其平方和$WQW=P$；补项补足$I-P$。若(10.5)成立，对Gram矩阵$c$酉对角化得到$F_j^\dagger F_k=\lambda_j\delta_{jk}I$。零权重时$F_j=0$；其余令$S_j=F_j/\sqrt{\lambda_j}$。于是$Q=\sum_j\lambda_jS_jS_j^\dagger$且$WF_j=S_j$，(10.4)精确变成(10.1)的恢复器。

反向，任一恢复Kraus$A_t$与原Kraus的复合必须表示恒等通道。该通道Choi矩阵秩一，所以$A_tE_a=z_{ta}I$。用$\sum_tA_t^\dagger A_t=I$得到$E_a^\dagger E_b=\sum_t\overline z_{ta}z_{tb}I$；取迹确定标量就是$c_{ab}$。∎

公式(10.4)属于已有transpose/Petz型恢复结构。[QREC-BK] 本定理不将数值近零残差等同于(10.5)的精确等式，也没有提供一般实数oracle的有限判等算法。

### 定理 10.4：删除环境访问权可以破坏全部未知态恢复

令逻辑为一个量子比特，先构造带公开错误标签的通道

$$
\mathcal M(\rho)=\tfrac12|0\rangle\langle0|\otimes\rho+
\tfrac12|1\rangle\langle1|\otimes Z\rho Z.
$$

保留标签时，按标签补偿$I$或$Z$并丢弃标签可精确恢复。删除标签后，通道为$\mathcal N(\rho)=(\rho+Z\rho Z)/2$，不存在任何CPTP左逆。

**证明。** 有标签的分支补偿直接给$\rho$。无标签通道把$|+\rangle\langle+|$与$|-\rangle\langle-|$都映成$I/2$，任何单值恢复映射都不能把相同输入变成两个不同输出。也可由其Kraus交叉项$Z/2$违反(10.5)得到结论。∎

### 定理 10.5：同一静态不可区分核不足以决定相干路径实验

$\operatorname{Ad}_I=\operatorname{Ad}_{-I}$，但它们作为具体酉实现接入受控路径后，产生的通道分别为$\operatorname{Ad}_{I\otimes I}$与$\operatorname{Ad}_{Z\otimes I}$，在控制输入$|+\rangle$上完全可区分。

**证明。** 酉的整体负号在$V\rho V^\dagger$中相消；在$|0\rangle\langle0|\otimes I+|1\rangle\langle1|\otimes V$中只改变第二条路径的相位，所以产生$|+\rangle$与$|-\rangle$。∎

因此核或“完整可恢复性”必须相对于明确的实验权限定义。给定相干实现、路径参考和相位数据时，可以构造对应实验；只有普通通道数据时，上述反例禁止唯一补出这些额外信息。[QREC-Control]

[QREC-KL]: https://doi.org/10.1103/PhysRevA.55.900 "E. Knill and R. Laflamme, Theory of quantum error-correcting codes, Physical Review A 55, 900 (1997)."
[QREC-NS]: https://arxiv.org/abs/quant-ph/0605041 "A. Nayak and P. Sen, Invertible Quantum Operations and Perfect Encryption of Quantum States, Quantum Information and Computation 7(1&2), 103–110 (2007), Theorem 2.1."
[QREC-BK]: https://arxiv.org/abs/quant-ph/0004088 "H. Barnum and E. Knill, Reversing quantum dynamics with near-optimal quantum and classical fidelity, Journal of Mathematical Physics 43, 2097–2106 (2002)."
[QREC-Control]: https://arxiv.org/abs/1309.7976 "M. Araújo, A. Feix, F. Costa and Č. Brukner, Quantum circuits cannot control unknown operations, New Journal of Physics 16, 093026 (2014)."

## §11 压缩仪器的正缺陷与忠实逻辑观测代数

### 定义 11.1：允许不同输入、输出框架的压缩

取有限维复 Hilbert 空间及等距框架 $U:L\to H$、$W:L'\to H'$，满足 $U^\dagger U=I_L$、$W^\dagger W=I_{L'}$。物理仪器的有限 Kraus 族为 $K_a:H\to H'$，并满足 $\sum_aK_a^\dagger K_a=I_H$。定义

$$
k_a=W^\dagger K_aU,\qquad R_a=(I_{H'}-WW^\dagger)K_aU.
\tag{11.1}
$$

这里 $R_a$ 是相对于输出框架的法向漏出，不是另行假设的噪声强度。分支均用未归一化矩阵描述，零概率分支不除以其概率。

### 定理 11.2：压缩保持归一性当且仅当所有分支零漏出

有精确等式

$$
\sum_a k_a^\dagger k_a+\sum_aR_a^\dagger R_a=I_L.
\tag{11.2}
$$

从而 $\sum_a k_a^\dagger k_a=I_L$ 当且仅当每个 $R_a=0$，也当且仅当 $K_aU=Wk_a$ 对所有 $a$ 成立。

**证明。** $Q=WW^\dagger$ 是正交投影。对任意矩阵 $B$，分解 $B=QB+(I-Q)B$ 的两项正交，故

$$
(W^\dagger B)^\dagger(W^\dagger B)
+[(I-Q)B]^\dagger[(I-Q)B]=B^\dagger B.
$$

代入 $B=K_aU$ 并求和即得(11.2)。若正 Gram 矩阵之和为零，对任意向量 $x$ 有 $\sum_a\|R_ax\|^2=0$；每一项非负，故所有 $R_a=0$。反向直接代入。最后 $R_a=K_aU-Wk_a$ 给出交织等价。∎

这个条件严于“原动力学有一个不变谱子空间”：仪器的每个 Kraus 算子也必须保持规定的输入、输出框架，才可不增加修复项地直接压缩。

### 定理 11.3：显式复位补全不等于逻辑恢复

若 $L'$ 非零，选单位基向量 $v\in L'$。对 $H'$ 的任意正交基 $e_b$，令

$$
T_{a,b}=|v\rangle\langle e_b|R_a.
$$

把每个 $k_a$ 与该分支的全部 $T_{a,b}$ 作为同一公开结果 $a$ 的 Kraus 算子，得到合法仪器

$$
\widehat{\mathcal I}_a(\rho)=k_a\rho k_a^\dagger+
\operatorname{tr}(R_a\rho R_a^\dagger)|v\rangle\langle v|.
\tag{11.3}
$$

其分支概率恰为 $\operatorname{tr}(K_aU\rho U^\dagger K_a^\dagger)$。

**证明。** 完备关系 $\sum_b|e_b\rangle\langle e_b|=I$ 给出 $\sum_bT_{a,b}^\dagger T_{a,b}=R_a^\dagger R_a$，也给出(11.3)中的复位项。由(11.2)全部 Kraus 平方和等于 $I_L$，所以总映射完全正且保迹。对单分支取迹并使用同一 Gram 分解，即得所述概率恒等式。∎

补全只保证通道合法并保留这些分支概率，不能据此推出保留所有逻辑相干性、与参考系统的纠缠或未来自适应实验。无漏出情形才直接得到交织。特别地，当输入、输出框架同为固定 $U$ 时，逐次使用 $K_aU=Uk_a$，任意有限矩阵词 $w=(a_1,\ldots,a_r)$ 均满足

$$
K_{a_1}\cdots K_{a_r}U=Uk_{a_1}\cdots k_{a_r},
$$

所以对应未归一化分支矩阵也由 $U$ 精确交织。空词取单位矩阵；此结论不需要对任何分支作非零概率假设。

### 定理 11.4：综合征编码保留的是带支持单位的忠实逻辑代数

沿用定义10.1的正交综合征族，定义

$$
\pi(A)=\sum_jS_jAS_j^\dagger,\qquad A\in\mathcal B(L).
\tag{11.4}
$$

则 $\pi$ 线性、保伴随、保乘法，且 $\pi(I_L)=P$。对任意综合征标签 $j$，

$$
\pi(A)S_j=S_jA,\qquad S_j^\dagger\pi(A)S_j=A.
\tag{11.5}
$$

因指标集非空，$\pi$ 单射。它作为 $P\mathcal B(H)P$ 中的表示以 $P$ 为单位；除非 $P=I_H$，不能称其为到整个 $\mathcal B(H)$ 的保单位表示。进一步，对任意矩阵 $\rho,\sigma$，包括非对角综合征矩阵，有

$$
\pi(A)\mathcal E_\sigma(\rho)=\mathcal E_\sigma(A\rho).
\tag{11.6}
$$

**证明。** 线性与伴随性质由有限和直接得到。乘法展开中 $S_i^\dagger S_j=\delta_{ij}I$ 消去全部交叉项，故 $\pi(A)\pi(B)=\pi(AB)$。同一关系得到(11.5)，其第二式给出左逆及单射性。对编码式逐项使用 $\pi(A)S_j=S_jA$，得到(11.6)。∎

在上述有限构造里，综合征可携带额外熵，同时逻辑算子的乘法和伴随关系均完整保留。这比单独追踪输出熵更精确：它明确规定哪些操作和哪些观测仍可从物理表示中恢复。此处不额外断言参数化支持向量丛有全局基，也不把一个点上的矩阵关系当成全局拓扑定理。

### 文献拓展：从全态恢复到可纠正观测量

Bény、Kempf 与 Kribs 的算子代数量子纠错以 Heisenberg 图像中的观测量代数为对象，允许保护量子与经典信息的混合结构，而不要求恢复整个物理态。[QREC-OA-PRL][QREC-OA-PRA] 定理11.4提供该视角下的一个显式有限矩阵实例；一般可纠正代数的充要条件属于文献中的更广结果，不能由本节这个正交综合征实例反向宣称已证明。

因而“保留目标所需的可区分性”应先指定目标观测代数及允许的仪器，而不是把所有物理自由度无区别地列为恢复目标。对仅保留经典结果概率的(11.3)与保持完整逻辑乘法结构的(11.4)，两者所解决的是不同的数学任务。

[QREC-OA-PRL]: https://doi.org/10.1103/PhysRevLett.98.100502 "C. Bény, A. Kempf and D. W. Kribs, Generalization of Quantum Error Correction via the Heisenberg Picture, Physical Review Letters 98, 100502 (2007); arXiv:quant-ph/0608071."
[QREC-OA-PRA]: https://doi.org/10.1103/PhysRevA.76.042303 "C. Bény, A. Kempf and D. W. Kribs, Quantum Error Correction of Observables, Physical Review A 76, 042303 (2007); arXiv:0705.1574."

## §12 从实际错误算子到恢复与逻辑运输

### 定义 12.1：允许零分支的谱恢复候选

取非零有限维复 Hilbert 空间 $L=\mathbb C^d$、$H=\mathbb C^n$，给定有限矩阵族 $E_a:L\to H$，定义完全正分支 $\mathcal N(X)=\sum_aE_aXE_a^\dagger$。本定义不要求该分支保迹。令

$$
Q=\sum_aE_aE_a^\dagger,\qquad
P=\mathbf 1_{(0,\infty)}(Q),\qquad
W=f(Q),\quad f(x)=\begin{cases}x^{-1/2},&x>0,\\0,&x=0.\end{cases}
\tag{12.1}
$$

谱函数作用于有限半正定矩阵；它们只由 $Q$ 决定，不依赖本征基的选择。固定逻辑单位基向量 $v$，定义

$$
\mathcal R_E(X)=\sum_aE_a^\dagger W X W E_a+
\operatorname{tr}[(I-P)X]|v\rangle\langle v|.
\tag{12.2}
$$

### 定理 12.2：谱归一化适用于所有完全正分支

定义12.1满足 $P=P^\dagger=P^2$、$W=W^\dagger$、$PQ=Q$、$WQW=P$ 及 $PE_a=E_a$。式(12.2)总是CPTP，包括全部 $E_a=0$ 的情形。

**证明。** 在 $Q$ 的非负本征值 $q$ 上，支撑函数满足 $p(q)^2=p(q)$、$p(q)q=q$，且 $f(q)qf(q)=p(q)$，故前四式成立。再令 $C=I-P$，则

$$
0=CQC=\sum_a(CE_a)(CE_a)^\dagger.
$$

每项半正定，故 $CE_a=0$。恢复的显式 Kraus 为 $E_a^\dagger W$ 与 $|v\rangle\langle b|(I-P)$，其中 $b$ 遍历物理正交基。其平方和分别为 $P$ 与 $I-P$，相加为 $I$。当 $Q=0$ 时 $P=W=0$，只剩复位通道；没有除以分支概率。∎

该归一化构造属于既有 transpose/Petz 恢复结构。[QREC-BK] 通道合法性本身没有给出 $\mathcal R_E\mathcal N=\mathrm{id}$；精确恢复仍需约束错误算子。

### 定理 12.3：恒等通道的正交换子缺陷迫使全部 Kraus 为标量

设有限矩阵族 $F_b\in M_d(\mathbb C)$ 满足

$$
\Phi(X):=\sum_bF_bXF_b^\dagger=X\quad\text{对所有 }X\in M_d(\mathbb C).
$$

则对每个 $b$ 存在 $z_b\in\mathbb C$，使 $F_b=z_bI$。固定任意逻辑基指标 $i_0$ 时，$z_b=(F_b)_{i_0i_0}$。

**证明。** 对任意 $X$ 直接展开得

$$
\sum_b[F_b,X][F_b,X]^\dagger
=\Phi(XX^\dagger)-\Phi(X)X^\dagger-X\Phi(X^\dagger)+X\Phi(I)X^\dagger=0.
\tag{12.3}
$$

正项不能相互抵消，故 $[F_b,X]=0$ 对全部 $X$ 成立。取 $X=e_{jj}$ 消去所有非对角矩阵元，再取 $X=e_{ij}$ 得各对角元相等。于是 $F_b=(F_b)_{i_0i_0}I$。∎

本命题的假设是作用在全部矩阵上的恒等映射。单独的 $\Phi(I)=I$ 不足：$\Phi(X)=ZXZ$ 保单位，但 $Z=\operatorname{diag}(1,-1)$ 与 Pauli $X$ 不交换。正缺陷与纠错的关系可置于完全正映射乘法域的文献背景中；幺通道与非幺通道的分类条件仍须分别保留。[QREC-MD]

### 定理 12.4：有限 Kraus 左逆的双向构造

设 $\sum_aE_a^\dagger E_a=I_d$。存在某个有限矩阵族 $A_b:H\to L$ 满足

$$
\sum_bA_b^\dagger A_b=I_n,\qquad
\sum_bA_b\left(\sum_aE_aXE_a^\dagger\right)A_b^\dagger=X
\quad\forall X
\tag{12.4}
$$

当且仅当

$$
E_a^\dagger E_c=\frac{\operatorname{tr}(E_a^\dagger E_c)}d I_d
\quad\forall a,c.
\tag{12.5}
$$

**证明：必要性。** 对实际复合 Kraus $F_{ba}=A_bE_a$ 用定理12.3，得 $A_bE_a=z_{ba}I$。由恢复归一性，

$$
E_a^\dagger E_c
=\sum_b(A_bE_a)^\dagger(A_bE_c)
=\left(\sum_b\overline{z_{ba}}z_{bc}\right)I_d.
$$

取迹确定标量即为(12.5)中的归一迹。这不需要预先假定复合 Kraus 的标量性。

**证明：充分性。** 写 $E_a^\dagger E_c=c_{ac}I_d$，固定逻辑单位基向量 $v$，令 $B$ 的第 $a$ 列为 $E_av$。则 $c=B^\dagger B\ge0$，且原通道保迹给出 $\operatorname{tr}c=1$。选酉矩阵 $V$ 使 $V^\dagger cV=\operatorname{diag}(\lambda_j)$，并令 $F_j=\sum_aV_{aj}E_a$。矩阵乘法给出

$$
F_j^\dagger F_k=\lambda_j\delta_{jk}I_d,\qquad
\sum_jF_jXF_j^\dagger=\sum_aE_aXE_a^\dagger.
$$

当 $\lambda_j=0$ 时，$F_j^\dagger F_j=0$ 迫使 $F_j=0$。仅对 $J=\{j:\lambda_j>0\}$ 定义 $S_j=F_j/\sqrt{\lambda_j}$。它们是正交综合征副本，$\sum_{j\in J}\lambda_j=1$。因此原通道成为定义10.1中 $\sigma=\operatorname{diag}(\lambda_j)_{j\in J}$ 的编码。使用定理10.2的支持内解码，并用定理11.3的显式复位补足支持外部分，得到(12.4)。所有矩阵族有限，零本征值算子被消去而没有参与除法。∎

本判据及综合征构造属于经典量子纠错和可逆量子操作理论。[QREC-KL][QREC-NS] 本命题直接在有限 Kraus 表示上量化。若起点改为仅用任意放大正性定义的抽象完全正映射，则需另用有限维 Kraus 表示定理连接两种表述。

### 定理 12.5：矩阵单位给出无需综合征基的实际解码

给定 $F_{ij}\in M_n(\mathbb C)$ 满足

$$
F_{ij}F_{kl}=\delta_{jk}F_{il},\qquad F_{ij}^\dagger=F_{ji},
\qquad P=\sum_iF_{ii},\qquad \pi(A)=\sum_{i,j}A_{ij}F_{ij}.
$$

固定逻辑指标 $v$，以矩阵元定义 $T_b(i,c)=F_{vi}(b,c)$。则 $P$ 为正交投影，$\pi$ 保乘法和伴随，且

$$
\sum_bT_b^\dagger T_b=P,\qquad
\left[\sum_bT_bXT_b^\dagger\right]_{ij}=\operatorname{tr}(F_{ji}X).
\tag{12.6}
$$

补上 $|v\rangle\langle b|(I-P)$ 得到完整CPTP解码 $\mathcal D_F$。若 $Q$ 满足 $PQ=Q$、$[Q,F_{ij}]=0$ 及 $\operatorname{tr}(F_{vv}Q)=1$，则

$$
\mathcal D_F(Q\pi(A))=A\quad\forall A\in M_d(\mathbb C).
\tag{12.7}
$$

**证明。** 矩阵单位律给出 $P^2=P$、$P^\dagger=P$ 以及 $PF_{ij}=F_{ij}P=F_{ij}$；有限和展开给出 $\pi(AB)=\pi(A)\pi(B)$ 和 $\pi(A)^\dagger=\pi(A^\dagger)$。对 $T_b$ 求 Gram 和，物理基的完备性给出 $\sum_iF_{iv}F_{vi}=P$。其作用的第 $(i,j)$ 元为

$$
\operatorname{tr}(F_{vi}XF_{jv})=\operatorname{tr}(F_{ji}X),
$$

得到(12.6)。完整CPTP性由支持外复位补全。另一方面，交换性与迹循环律给出

$$
\operatorname{tr}(F_{ij}Q)
=\operatorname{tr}(F_{iv}F_{vj}Q)
=\operatorname{tr}(F_{vj}F_{iv}Q)
=\delta_{ij}\operatorname{tr}(F_{vv}Q).
$$

将 $Q\pi(A)$ 代入(12.6)，逐项用矩阵单位律即得到 $A_{ij}$；支持条件使复位项为零。∎

式(12.7)是任意矩阵上的代数恒等式。要把 $Q\pi(\rho)$ 作为物理密度态，进一步取 $Q\ge0$、$\rho\ge0$、$\operatorname{tr}\rho=1$；交换性保证乘积正性，而(12.6)和归一条件给出迹一。这里没有选择综合征本征向量或支持丛的全局基。它是定理11.4观测代数视角的解码接口。[QREC-OA-PRA]

### 定理 12.6：规定逻辑仪器的有限物理实现

在定理12.5条件下，若逻辑 Kraus 满足 $\sum_aL_a^\dagger L_a=I_d$，则物理 Kraus $\pi(L_a)$ 连同 $I-P$ 的平方和为 $I_n$。对于 $PQ=Q$ 且 $Q$ 与全部矩阵单位交换的输入 $Q\pi(\rho)$，失败分支 $I-P$ 的输出为零，其余分支满足

$$
\pi(L_a)\,Q\pi(\rho)\,\pi(L_a)^\dagger
=Q\pi(L_a\rho L_a^\dagger).
$$

**证明。** 保乘法、伴随和线性给出 $\sum_a\pi(L_a)^\dagger\pi(L_a)=\pi(I_d)=P$。补项贡献 $(I-P)^2=I-P$。第二式由交换性与保乘法成立，失败项由 $(I-P)Q=0$ 消失。∎

### 定理 12.7：全部逻辑矩阵单位的显式运输生成元

令 $F_{ij}(t)$ 为实参数 $t$ 上的可微矩阵族，逐时满足定理12.5的矩阵单位和伴随关系。记 $D_{ij}=\dot F_{ij}$、$\dot P=\sum_iD_{ii}$，定义

$$
Z=\frac1d\sum_{i,j}D_{ij}F_{ji},\qquad K=Z-P\dot P.
\tag{12.8}
$$

则

$$
K^\dagger=-K,\qquad [K,F_{ij}]=D_{ij},\qquad [K,P]=\dot P.
\tag{12.9}
$$

**证明。** 对实际矩阵族求导，乘法和伴随关系给出

$$
D_{ij}F_{kl}+F_{ij}D_{kl}=\delta_{jk}D_{il},\qquad D_{ij}^\dagger=D_{ji}.
$$

对 $F_{ij}F_{ji}$ 求和后微分得 $Z+Z^\dagger=\dot P$；对 $P^2=P$ 微分得 $P\dot P+\dot PP=\dot P$ 和 $P\dot PP=0$。因此 $K+K^\dagger=0$。固定 $k,l$，前述乘法律及其导数给出

$$
ZF_{kl}=\frac1d\sum_jD_{kj}F_{jl},\qquad
F_{kl}Z=\frac1d\sum_jD_{kj}F_{jl}-D_{kl}P.
$$

同时 $[P\dot P,F_{kl}]=-F_{kl}\dot P$。故

$$
[K,F_{kl}]=D_{kl}P+F_{kl}\dot P=D_{kl},
$$

最后一步是 $F_{kl}P=F_{kl}$ 的实际导数。对对角指标求和得到投影式。∎

### 命题 12.8：只固定支持投影不足以运输内部逻辑代数

令 $d=2$，$F_{ij}(t)=U(t)e_{ij}U(t)^\dagger$，其中 $U(t)=e^{tB}$，$B=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$。则 $P(t)=I_2$、$\dot P=0$，但 $D_{11}(0)=[B,e_{11}]\ne0$，所以投影生成元 $[\dot P,P]=0$ 不能满足 $[K,F_{11}]=D_{11}$。定义(12.8)仍满足全部交织导数关系。

**证明。** $B^\dagger=-B$ 保证 $U(t)$ 酉，因此两条对角矩阵单位之和为恒等。直接计算 $[B,e_{11}]=\begin{pmatrix}0&-1\\-1&0\end{pmatrix}$，其非零性给出所述不足。定理12.7适用于这个实际可微族。∎

当逻辑维数 $d=1$ 时，(12.8)退化为 $[\dot P,P]$，接入 Kato 的投影运输背景。[QREC-Kato] 多维逻辑情形要求同时运输内部矩阵单位；本节的代数平均公式有独立证明，不将它归为Kato原文中的一般定理。由生成元继续得到全时间酉传播子，还需解决相应微分方程及其存在、唯一性和积分收敛条件；(12.9)本身没有假设这些分析结论。

### 定理 12.9：任意实际左逆保证计算出的谱恢复候选正确

在定理12.4的保迹条件下，以下三者等价：存在有限 Kraus 左逆；式(12.5)的标量交叉积条件成立；定义12.1计算出的同一个 $\mathcal R_E$ 满足 $\mathcal R_E\mathcal N=\mathrm{id}$。

**证明。** 前两者由定理12.4等价；第三者提供显式有限 Kraus 左逆，反向立即成立。为证明任意左逆都保证该特定候选正确，取式(12.4)中的实际 $A_b$，定义恢复伴随的观测量

$$
Y_X=\sum_bA_b^\dagger X A_b.
$$

定理12.3给出 $A_bE_a=z_{ba}I$，故

$$
Y_XE_a=\sum_bA_b^\dagger X(A_bE_a)
=\sum_bA_b^\dagger(A_bE_a)X=E_aX.
$$

伴随关系 $Y_{X^\dagger}=Y_X^\dagger$ 进一步给出 $E_a^\dagger Y_X=XE_a^\dagger$。于是

$$
QY_X=Y_XQ=\mathcal N(X).
\tag{12.10}
$$

有限 Hermitian 矩阵的函数演算保持其交换子代数，所以 $WY_X=Y_XW$。用定理12.2中实际谱函数的恒等式得到

$$
W\mathcal N(X)W=WQWY_X=PY_X.
$$

原通道输出支持在 $P$，恢复的补空间项为零。因此

$$
\mathcal R_E\mathcal N(X)
=\sum_aE_a^\dagger P Y_XE_a
=\sum_aE_a^\dagger PE_aX
=\left(\sum_aE_a^\dagger E_a\right)X=X.
$$

这证明了预先计算的谱候选正确，而不需要在结论中再选择一个未指定的恢复器。∎

这里 $Y_X$ 是实际恢复的 Heisenberg 伴随；上述证明只使用其在错误像上的交织。它没有断言 $X\mapsto Y_X$ 在整个物理空间上保乘法。谱候选的具体构造和其精确恢复性质仍归于既有恢复理论。[QREC-BK][QREC-NS]

[QREC-MD]: https://doi.org/10.1088/1751-8113/42/24/245303 "M.-D. Choi, N. Johnston and D. W. Kribs, The multiplicative domain in quantum error correction, Journal of Physics A: Mathematical and Theoretical 42, 245303 (2009); arXiv:0811.0947."
[QREC-Kato]: https://doi.org/10.1143/JPSJ.5.435 "T. Kato, On the Adiabatic Theorem of Quantum Mechanics, Journal of the Physical Society of Japan 5(6), 435–439 (1950)."
