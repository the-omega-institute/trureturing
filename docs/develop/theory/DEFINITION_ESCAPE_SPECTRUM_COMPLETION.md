# 定义逃逸谱完备化
## Definition-Escape Spectrum Completion（DESC）

> **状态**：定义、数学定理与证明骨架、显式边界反模型，v1.0，2026-08-25。
> **版本纪律**：工作树只保留这一份当前 v1.0；草稿演进与被撤销文字归 git，不在卷内并置修订剧场。
> **母卷边界**：只引用 DECT v1.0 的 §5.3、§6.1、§6.2、§16.2 与 §17.2；本卷的语义与结算均在本地写全，不引用母卷其他章节或后续版本。
> **主张边界**：T1、T2 与 T5 的集合/实数推理在卷内给出；T3 借用紧致开覆盖定理；T4(a) 借用 Lebesgue 测度，T4(b) 明示假设 BPI。本文不声称已有 Lean 证明、具体解析估计或新颖性证明。

## 0. 共同语义

令 \((X,\mathcal A)\) 为可测对象空间，\(q:X\to Q\) 为现行概念，\(T:X\to Y\) 为目标。正文定理域中的定义语言 \(\Gamma\) 有限或可数，成本与预算满足

\[c:\Gamma\to\mathbb R_{>0},\qquad L\in\mathbb R_{\ge0}.\]

定义目标残差、单定义分离集与语言盲核：

\[
\begin{aligned}
E&:=\mathcal E(q;T)=\{(x,y):q(x)=q(y),\ T(x)\ne T(y)\},\\
U_d&:=\{(x,y)\in E:d(x)\ne d(y)\},\\
B&:=\mathcal B_\Gamma(q;T)=E\cap\bigcap_{d\in\Gamma}\ker d
=E\setminus\bigcup_{d\in\Gamma}U_d.
\end{aligned}
\]

令 \(\mathfrak E\subseteq\mathcal P(E)\) 为集合代数，含 \(\varnothing,E,B\) 与每个 \(U_d\)，因而含以下所有有限并、差集与 \(E_S\)。有限/可数 \(\Gamma\) 时可直接取由 \(E\) 与 \(\{U_d\}\) 生成的 \(\sigma\)-代数；边界反模型使用更大语言时须另行明载 \(B\in\mathfrak E\)。固定有限非负实值 charge

\[\nu:\mathfrak E\to\mathbb R_{\ge0}\hookrightarrow\mathbb R.\]

满足

\[
\nu(\varnothing)=0,
\quad A\cap D=\varnothing\Longrightarrow\nu(A\cup D)=\nu(A)+\nu(D),
\quad A\subseteq D\Longrightarrow\nu(A)\le\nu(D),
\]

并假设

\[0<M_0:=\nu(E)<\infty.\]

对有限族 \(S\Subset\Gamma\)，记

\[E_S:=E\setminus\bigcup_{d\in S}U_d,\qquad C(S):=\sum_{d\in S}c(d),\qquad \mathscr F_L:=\{S\Subset\Gamma:C(S)\le L\}.\]

于是 \(B\subseteq E_S\)，且有限可加性给出

\[\nu(E_S)=\nu(B)+\nu(E_S\setminus B).\]

这里“有限”始终指有限定义族；不把点态无限联合偷换成有限预算。

## T1. 预算包络恒等式

定义未归一化预算包络与逃逸谱

\[M_\Gamma(L):=\inf_{S\in\mathscr F_L}\nu(E_S),\qquad \rho_\Gamma(L):=\frac{M_\Gamma(L)}{M_0}.\]

**定理 T1（下确界包络）**。\(L\mapsto M_\Gamma(L)\) 非增且取值于 \([0,M_0]\)，并且

\[
\boxed{
\inf_{L\ge0}M_\Gamma(L)
=\lim_{L\to\infty}M_\Gamma(L)
=\inf_{S\Subset\Gamma}\nu(E_S)
}
\]

以及

\[
\boxed{
\inf_{L\ge0}\rho_\Gamma(L)
=\lim_{L\to\infty}\rho_\Gamma(L)
=\frac1{M_0}\inf_{S\Subset\Gamma}\nu(E_S).
}
\]

证明：预算增大只会扩大 \(\mathscr F_L\)，故包络非增且有下界；每个有限 \(S\) 都落入预算 \(C(S)\)，而每个预算层只含有限族候选，故两重下确界相等。第二式由 \(M_0>0\) 归一化得到。

**真残差**：无限预算读数是所有有限定义族残差质量的下确界，不是任意预算点。
**结案判据**：核验单调性、上下界与两类候选的共尾关系；没有最优值取到的前件时，不要求给出取到下确界的有限族。

## T2. 盲核地板的真刻画

先不预置连续性。共同语义下，下列三项等价：

\[
\begin{aligned}
\mathrm{(i)}\quad&\lim_{L\to\infty}\rho_\Gamma(L)=\frac{\nu(B)}{M_0};\\
\mathrm{(ii)}\quad&\forall\varepsilon>0\ \exists S\Subset\Gamma:
\nu(E_S\setminus B)<\varepsilon;\\
\mathrm{(iii)}\quad&\exists(F_n)_{n\ge1},\quad
F_n\Subset\Gamma,\quad F_n\subseteq F_{n+1},\quad
\nu(E_{F_n})\downarrow\nu(B).
\end{aligned}
\]

证明：T1 与 \(\nu(E_S)=\nu(B)+\nu(E_S\setminus B)\) 给出 \((i)\Leftrightarrow(ii)\)。由 (ii) 为误差 \(1/n\) 选择有限见证 \(S_n\)，再令 \(F_n=\bigcup_{k\le n}S_k\)，单调性给出 (iii)；\((iii)\Rightarrow(ii)\) 直接取充分大的 \(n\)。这是等价引理，不把其中任一项冒充自动成立的前件。

现在枚举 \(\Gamma=(d_n)_{n\ge1}\)；\(\Gamma\) 有限时允许重复。令

\[
F_n:=\{d_1,\ldots,d_n\},
\qquad A_n:=E_{F_n}.
\]

可数性给出 \(A_n\downarrow B\)，且 \((F_n)\) 对所有有限 \(S\Subset\Gamma\) 共尾。因此

\[
\lim_{L\to\infty}M_\Gamma(L)
=\inf_n\nu(A_n)
=\lim_{n\to\infty}\nu(A_n).
\]

**定理 T2（穷举残差链 iff）**。在共同语义下，

\[
\boxed{
\lim_{L\to\infty}\rho_\Gamma(L)=\frac{\nu(B)}{M_0}
\quad\Longleftrightarrow\quad
\nu(A_n)\downarrow\nu\!\left(\bigcap_nA_n\right)=\nu(B).
}
\]

右式恰是 \(\nu\) 沿这条穷举残差链自上连续。全局自上连续蕴含右式，故是充分条件；它不被冒充为必要前件。等价式不依赖枚举选择，因为每条穷举链都与全体有限族共尾。

**真残差**：盲核是不可再切割的地板；地板以上若不能被有限切割任意逼近，留下的是预算极限缺口。
**结案判据**：分别核验一般三式等价、穷举链与有限族共尾、以及该链上的质量极限；删除可数性或链连续性只说明统一保证可能失效。

## T3. 紧致残差有限完备化

给 \(E\) 残差子空间拓扑。假设 \(E\) 紧致、\(B=\varnothing\)，且每个 \(U_d\) 在 \(E\) 中开。

**定理 T3（紧致有限完备化）**。存在有限 \(S\Subset\Gamma\) 与有限预算 \(L=C(S)\)，使

\[E_S=\varnothing,\qquad \rho_\Gamma(L)=0.\]

证明：\(B=\varnothing\) 使 \(\{U_d:d\in\Gamma\}\) 覆盖 \(E\)；开性使其为开覆盖；紧致性给出有限子覆盖。取该子覆盖的定义族 \(S\)。这里借用成熟的紧致开覆盖定理，不声称解析紧致性或定义连续性已在仓库形式化。

**真残差**：逐点可分不推出统一有限预算；紧致性才把逐点见证压成有限子覆盖。
**结案判据**：给出紧致性、开性与覆盖证书，再核验有限子覆盖及成本和。

## T4. 两个统一保证的边界反模型

冻结 T4 的命题极性：T4 断言下述 (a)、(b) 两个显式构造分别存在并满足列出的 charge 与残差计算。验证构造是在证明 T4；只有推翻这些冻结计算的有效反证才反驳 T4。

### T4(a) 删除可数性：单点切割

取 \(X=[0,1]\times\{0,1\}\)、\(q(t,i)=t\)、\(T(t,i)=i\)，并令

\[
e_t^+:=((t,0),(t,1)),
\qquad e_t^-:=((t,1),(t,0)),
\qquad E=\{e_t^+,e_t^-:t\in[0,1]\}.
\]

对 \(C\subseteq E\)，写 \(C_\pm=\{t:e_t^\pm\in C\}\)，并取

\[
\mathfrak E:=\{C\subseteq E:C_+,C_-\text{ 均 Lebesgue 可测}\},
\qquad
\nu(C):=\tfrac12\lambda(C_+)+\tfrac12\lambda(C_-).
\]

则 \(\nu\) 是 \(\mathfrak E\) 上的有限 charge，\(M_0=1\)。对每个 \(t\in[0,1]\) 定义

\[
d_t(s,i):=
\begin{cases}
i,&s=t,\\
0,&s\ne t.
\end{cases}
\]

于是

\[
U_{d_t}=\{e_t^+,e_t^-\},
\qquad B=E\setminus\bigcup_{t\in[0,1]}U_{d_t}=\varnothing,
\qquad \nu(E_S)=1\quad(S\Subset\Gamma).
\]

令 \(c(d_t)=1\)。该不可数 \(\Gamma\) 明确位于正文有限/可数定理域之外；任一有限定义族只切掉有限多个零测点，故

\[
\rho_\Gamma(L)=1\quad(L<\infty),
\qquad
\lim_{L\to\infty}\rho_\Gamma(L)=1\ne0=\frac{\nu(B)}{M_0}.
\]

### T4(b) 删除链连续性：完整自由超滤 charge

假设布尔素理想定理 BPI，取 \(\mathbb N\) 上自由超滤 \(\mathcal U\)。令 \(X=\mathbb N\times\{0,1\}\)、\(q(n,i)=n\)、\(T(n,i)=i\)，写 \(e_n^\pm\) 为两条有向残差边，并定义

\[
d_n(k,i):=
\begin{cases}
i,&k\le n,\\
0,&k>n.
\end{cases}
\]

取 \(\Gamma=\{d_n:n\ge1\}\)、\(c(d_n)=1\)、\(\mathfrak E=\mathcal P(E)\)。对 \(A\subseteq\mathbb N\)，令

\[
\mu_\mathcal U(A):=
\begin{cases}
1,&A\in\mathcal U,\\
0,&A\notin\mathcal U,
\end{cases}
\]

并对每个 \(C\subseteq E\) 定义

\[
\nu(C):=\tfrac12\mu_\mathcal U(\{k:e_k^+\in C\})
+\tfrac12\mu_\mathcal U(\{k:e_k^-\in C\}).
\]

若 \(C,D\) 不交，则两个符号上的指标集分别不交；超滤素性给出 \(\mu_\mathcal U(A\sqcup D)=\mu_\mathcal U(A)+\mu_\mathcal U(D)\)。因此 \(\nu\) 在整个 \(\mathcal P(E)\) 上有限可加、非负、单调，且 \(\nu(E)=1\)。又有

\[
E_{\{d_1,\ldots,d_n\}}=\{e_k^+,e_k^-:k>n\},
\qquad
\bigcap_{n\ge1}E_{\{d_1,\ldots,d_n\}}=\varnothing.
\]

任一有限 \(S\) 留下某个余有限尾集；余有限集属于自由超滤，故

\[
B=\varnothing,
\qquad \nu(E_S)=1\quad(S\Subset\Gamma),
\qquad \rho_\Gamma(L)=1\quad(L<\infty),
\qquad \nu(\varnothing)=0.
\]

它满足共同 charge 语义，但不沿穷举残差链自上连续，因而不与 T2 冲突。

> **现役接口边界**：`EscapeWeight` 只有 `empty_mass` 与 `mass_nonnegative`；它还缺有限可加律，故不能把“补链连续性”缩写成现役接口的唯一缺口。

**真残差**：T4(a) 表明逐点无盲核不等于有限族能覆盖正质量；T4(b) 表明集合链可降到空而 charge 质量仍恒正。
**结案判据**：分别核验 (a) 的可测截面与有限点零测、(b) 的双符号自由超滤 charge 与尾集计算；两项都支持 T4 本身。

## T5. 母卷三分型及其适用域

采用母卷 §6.1 的不可消除逃逸率

\[\rho_\Gamma^\infty:=\frac{\nu(B)}{M_0}.\]

并忠实保留母卷 §6.2 的三类：

\[
\begin{aligned}
\mathsf{FiniteClosed}
&:\Longleftrightarrow
\exists L\ge0,\ \rho_\Gamma(L)=0;\\
\mathsf{AsymptoticClosed}
&:\Longleftrightarrow
(\forall L\ge0,\ \rho_\Gamma(L)>0)
\ \wedge\ \lim_{L\to\infty}\rho_\Gamma(L)=0;\\
\mathsf{StructurallyIncomplete}
&:\Longleftrightarrow
\rho_\Gamma^\infty>0.
\end{aligned}
\]

**定理 T5（三分穷尽，带链连续前件）**。在共同语义并且

\[
\lim_{L\to\infty}\rho_\Gamma(L)=\rho_\Gamma^\infty
\]

成立时，上述三类两两互斥且穷尽。证明：若 \(\rho_\Gamma^\infty>0\)，单调非负谱不可能在有限预算为零，故只有结构不完备型；若 \(\rho_\Gamma^\infty=0\)，经典排中把“某个有限预算为零”与“每个有限预算严格为正”分开，分别得到有限闭合型与渐近闭合型。

这里选择保留母卷分类而不另造同名严格变体，理由是 `StructurallyIncomplete` 的语义应由盲核 \(B\) 决定。T4(b) 中 \(B=\varnothing\) 而 \(\lim_L\rho_\Gamma(L)=1\)：它故意违反链连续前件，不属于本定理的穷尽域，也不被冒充为母卷的结构不完备。

另记不参与母卷三分型的严格见证谓词

\[
\mathsf{WitnessFiniteClosed}
:\Longleftrightarrow
\exists S\Subset\Gamma,\ \nu(E_S)=0.
\]

它推出 \(\mathsf{FiniteClosed}\)，但一般不等价。分离例：令 \(E\cong\mathbb N_{\ge1}\times\{+,-\}\)，每条符号边质量为 \(2^{-k-1}\)，\(d_n\) 切掉 \(k\le n\)，且 \(c(d_n)=1\)。则

\[
\nu(E_{\{d_n\}})=2^{-n},
\qquad \rho_\Gamma(1)=\inf_n2^{-n}=0,
\]

但任何有限族仍留下正质量尾集。因此 `FiniteClosed` 真而 `WitnessFiniteClosed` 假；只有零下确界预算层取到最优值时，反向蕴含才成立。

**真残差**：盲核不完备与预算极限缺口是两个不同现象；三分穷尽只在二者由链连续性对齐时成立。
**结案判据**：核验链连续前件、\(\rho_\Gamma^\infty\) 与有限预算零值；前件失败时不得输出三分穷尽判词。

## 本地 SpectrumCommitment

本卷独立定义七元记录，不借用母卷的持有链或结算章节：

\[
\boxed{
\operatorname{SpectrumCommitment}=
(\operatorname{atom\_family},\operatorname{scope},\operatorname{baseline},
\operatorname{weight\_spec},\operatorname{comparator},
\operatorname{test\_plan},\operatorname{falsifiable\_prediction}).
}
\]

冻结

\[A=\{a_1,\ldots,a_5\},\qquad a_i=\texttt{DESC-v1.0/T}i.\]

且 \(a_i\) 分别只对应 T1--T5。各字段取值为：

- `scope`：正文定理只收有限/可数 \(\Gamma\)；T4 边界检查可使用明示的更大构造。
- `baseline`：DECT v1.0 的 §5.3、§6.1、§6.2、§16.2、§17.2，不预记任一 \(T_i\) 为真。
- `weight_spec`：共同语义的有限非负实值 charge；T2/T5 的穷尽结论另需穷举残差链连续。
- `test_plan`：核验公式类型与配对、前件闭包、T1/T2 推理、T3 紧致借用、T4 两子项及 T5 适用域。
- `comparator` 与 `falsifiable_prediction`：由下述固定截止纯函数给出。

基线内容地址固定为：在提交 `f2d87fdc0506c31e787eb7b771c240d54c705de9`，母卷文件 SHA-256 为 `ff23c648ecc88dc128b084e6b5bbd3d6e9510f7f634ab5ceca6cc88641f780b7`。本地记录已经写全，且不引用母卷其他章节。

### 证据极性与 T4 父聚合

原子研究态为

\[
Q=\{\mathsf{open},\mathsf{proved},\mathsf{refuted},
\mathsf{statement\mbox{-}revised},\mathsf{invalid}\}.
\]

固定证据截止为

\[
D:=\texttt{2026-09-30T00:00:00Z}.
\]

只消费规范账本中 `received_at` 不晚于 \(D\) 的有限前缀；\(D\) 与证明进展、成功票数、运输批次和事件顺序无关。证据集合单调追加，各原子在 \(D\) 前保持 open，在 \(D\) 由同一纯函数一次迁移到终态：

- `proved`：存在核验通过的 kernel 定理证明冻结命题；T4 子项还允许机器核验通过的本卷显式构造见证。
- `refuted`：存在机器核验通过、确实推翻冻结命题自身的反模型；验证失败、缺证或支持 T4 的边界见证都不是 refuted。
- `statement-revised`：冻结陈述或 scope 在截止前发生语义改写。
- `invalid`：规范证据槽缺失、格式不可判、证书不通过，或同一冻结命题同时出现有效正反证据。T1--T3、T5 与每个 T4 子项均按 `statement-revised` → 上述 `invalid` → `refuted` → `proved` → 缺少决定性证据则 `invalid` 的固定优先序取值，故子项结算也是总函数。

T4 先冻结两个合取子命题 \(C_{4a}\)、\(C_{4b}\)，分别对应 T4(a)、T4(b)，并各自按上式结算。kernel 定理与机器见证只是证据载体不同，都会归一为子项 `proved`。父项按以下总函数聚合：

\[
s_4=
\begin{cases}
\mathsf{statement\mbox{-}revised},&\text{T4 或任一子命题被改写},\\
\mathsf{refuted},&\text{否则，至少一个子命题被有效反驳},\\
\mathsf{proved},&\text{否则，两个子命题均为 proved},\\
\mathsf{invalid},&\text{否则}.
\end{cases}
\]

因此一项由 kernel 定理证明、另一项由机器见证验证的混合正证据聚合为 T4 `proved`；一正一反聚合为 T4 `refuted`，不会永久 open。机器验证两个边界反模型是在支持 T4，不是反驳 T4。

### 固定截止判词

在 \(D\) 对所有五个父原子执行上述 terminalization；缺证本身成为 `invalid`，故截止后没有总体 open 路径。令

\[
N:=\#\{a_i:s_i\in\{\mathsf{proved},\mathsf{refuted}\}\}.
\]

冻结预测为“五单元至少三项由 kernel 定理、机器正见证或机器反模型结案”，其总结算为

\[
\operatorname{Verdict}=
\begin{cases}
\mathsf{success},&N\ge3,\\
\mathsf{failure},&N<3.
\end{cases}
\]

`statement-revised` 与 `invalid` 均不计成功票；未能在截止前形成终态材料也按 `invalid` 处理。截止后的证据不改变本次预测判词，可另立新承诺，不回写本记录。同一截止证据集合无论事件顺序或批次如何都得到同一结果，也不以提前达到三票为截止条件。

## 已合并案号排除账

2026-08-24 已亲跑 `gh pr view`，#2904、#2938、#3039 均为 `MERGED`。排除地址冻结如下：

- **#2904（13 个 Lean 模块）**：共同前缀 `D5/S3/ConceptDynamics/`；`Coding/ProductiveDiagonalEscapeCriterion.*`；`DefinitionEscape/{DefinitionKernelGalois,LatentAdequacyCriterion,MinimalTargetDistillation,MultiTargetBlindResidual,QuestionAlgebraDuality,RelativeSemanticDiagonal}.*`；`Promotion/ResearchPromotionLoop.*`；`RefinementGeometry/{InverseLimitCompletion,RefinementUltrametric}.*`；`ResidualCoverage/{GreedyResidualAllocation,ResidualSeparationAdapter,WeightedResidualCoverage}.*`。
- **#2938**：`D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelObstruction.blind_kernel_obstruction`。
- **#3039**：`D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency.{finite_window_minimal_sufficiency,descent_composes}`。

地址交集可机械判为 \(\varnothing\)。语义差分逐项为：T1 是无限预算实值下确界/极限，不是有限加权覆盖或 Galois 闭包；T2 是 charge 地板、有限逼近与链连续刻画，不是盲核因子化阻断；T3 是拓扑紧致有限子覆盖，不是 finite snapshot exact cover 或有限窗最小充分性；T4 是不可数/Lebesgue 与自由超滤的测度边界构造，排除模块无此反模型；T5 是母卷三分型的精确适用域与“取到/趋近”分离，不是 refinement geometry、promotion receipt 或 descent composition。

## 新颖性边界

检索只是一份可复核的非穷尽收据，不构成新颖性证明。T1--T5 当前状态为“已作卷尾所列检索，不作新颖性声明”；Szpilrajn 型延伸未被任何定理消费，不列为借用项。

# 追加账本

## v1.0 — 2026-08-25

当前唯一版本存入：有限 charge 共同语义、T1 预算包络、T2 真 iff、T3 紧致完备化、T4 两个完整边界 charge、采用母卷盲核定义且受链连续前件约束的 T5、固定截止的本地 `SpectrumCommitment`、已合并案号排除账与非穷尽检索收据。此前草稿字节与修复过程只由 git 保存。

2026-08-24 联网检索：GitHub code 全局精确查 `"Definition-Escape Spectrum Completion"` 与 `"blind residual" "escape spectrum"`，均 0 命中；Crossref `/works` 查 `definition escape spectrum`，前五命中均词面无关；OpenAlex `/works` 查 `blind kernel budget residual measure`、`finitely additive measure continuity from above ultrafilter`、`compactness finite subcover residual set cover`，只命中一般/旁支材料（有限可加概率旁支含 DOI `10.1007/BF00531529`），未命中 T1–T5 的直接同题组合。该非穷尽检索不足以证明新颖性，故本卷状态为“已作上述检索，**不作新颖性声明**”；Szpilrajn 型延伸未被 T1–T5 消费，撤销其借用项。
