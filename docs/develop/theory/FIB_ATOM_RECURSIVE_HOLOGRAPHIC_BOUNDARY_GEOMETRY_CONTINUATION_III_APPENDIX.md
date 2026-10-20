# FIB-ATOM recursive holographic boundary geometry · Continuation III Appendix

**Notation.** This appendix continues the [third continuation](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md). Sections 94–95 are kept here without changing their numbering or mathematical scope; earlier sections and references remain in Continuation III.

## 94. 联合终端响应：代数零点不等于合法来源碰撞

最新 DEV 的[严格实数联合相交卷](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md)把上一节的来源保真义务再推进了一步。对一个固定的已获取历史，必须把“存在两个完整世界在某个终端动作下响应相同”与“两个终端动作分别出现了相同的代数指标”分开。前者要求完整来源、原始读数、严格不等式、非奇异分母以及全部严格源方程和守卫同时成立；后者至多提供候选零点。

**定义 94.1（合法联合碰撞）。** 设 $p\ne24$，且 $C(p,v)$ 是固定历史与固定新读出的完整合法世界纤维；沿用严格实数卷的记号，令 $f_J=f_{MJ}$、$f_M=f_{MM}$ 为两种允许终端动作的响应。定义

$$
\begin{aligned}
D_J&=\{(p,v):\exists W\ne W'\in C(p,v),\ f_J(W)=f_J(W')\},\\
D_M&=\{(p,v):\exists W\ne W'\in C(p,v),\ f_M(W)=f_M(W')\}.
\end{aligned}
\tag{94.1}
$$

真正的联合事件是 $D_J\cap D_M$。一个候选参数只有在同一个合法来源纤维中完成两个分别带有来源不等性的碰撞，才属于这个集合。

**命题 94.2（投影零点的提升义务）。** 若一个参数化坐标中的方程组 $G(z)=0$ 只表达投影后的终端指标相等，则

$$
G(z)=0
\quad\Longrightarrow\quad
\text{候选联合零点},
$$

而不能直接推出 $(p,v)\in D_J\cap D_M$。要得到后者，还必须证明：

$$
\boxed{
\begin{gathered}
z\text{ 对应完整合法世界};\\
\text{两个配对中的世界各自不同};\\
\text{所有原始历史读数与严格源方程成立};\\
\text{没有被投影、奇异分母或重复根伪造的标签}.
\end{gathered}}
\tag{94.2}
$$

**证明。** 式 $G(z)=0$ 只约束其所写出的投影坐标。若参数化域还包含不满足来源方程的代数点、重复标签或奇异极限，则这些点不属于 $C(p,v)$，因而不属于 $D_J$ 或 $D_M$。即使它们都合法，若完整纤维中的终端响应仍分别单射，也不存在定义 94.1 所需的来源不等性碰撞。证毕。

严格实数联合相交卷给出了一个精确的反例：在一个极小有理盒中，六个投影方程有唯一横截共同零点；但完整合法子纤维恰有三个世界，且 $f_J$ 与 $f_M$ 在这三个世界上都单射。因此该共同零点不是 $D_J\cap D_M$ 的成员。这个结果把“维数足够”与“联合响应真正可碰撞”明确分离开来。

**推论 94.3（对三维桥的约束）。** 若一个候选三维状态桥只保留投影坐标，并把 $G(z)=0$ 当作联合来源碰撞的证据，则它可能把不属于同一合法来源纤维的代数标签错误地合并。任何声称三维接口已经保留联合终端任务的桥，至少要提供：

$$
\boxed{
\text{合法来源纤维}
\;+\;
\text{终端动作的联合响应}
\;+\;
\text{来源不等性以及全部严格源方程、守卫与历史读数约束的证明}.
}
\tag{94.3}
$$

这项约束与第 92、93 节的两种障碍正交：第 92 节排除只经 $q$ 的完整来源恢复，第 93 节排除跨层统一双 Lipschitz 的固定三维保真桥；本节说明即使某个代数图看起来已经出现共同相交，也必须先完成来源与联合响应的提升。

**开放边界 94.4。** 严格实数卷的结果把一个共同代数零点排除为合法联合碰撞，并缩小了零漂移分支的外部候选集；它没有完成整个 $D_J\cap D_M$ 的全局分类。因而当前可保留的结论是：

$$
\boxed{
\text{三维接口的联合充分性必须在完整合法来源纤维上核验；}
}
\tag{94.4}
$$

而不是“联合碰撞已被三维坐标完全刻画”。这为后续研究提供了明确检验顺序：先验证来源提升和合法性，再验证终端响应，最后才讨论固定维数的几何实现。

## 94.99 追加锚（本行以下为增补区）

## 95. 谱全息边界：局部边缘不保留联合响应

最新 DEV 的[实际 FIB Choi 理论](AURIC_FIB_ACTUAL_WORD_PURITY_ARITHMETIC.md)
给出了一种与前面两类几何障碍不同的
信息逃逸。这里的局部接口仍然只有三维，但被消去的区别不是来源标签或
归一化距离，而是接口与参考副本之间的联合算子关系。

**定义 95.1（局部边缘与联合谱目标）。** 令 $V\cong\mathbb C^3$ 为
实际 qutrit 接口，令 $\omega_n\in\mathcal D(V\otimes V)$ 是最新 DEV
§87 的归一化 Choi 状态。定义局部边界读出

$$
\lambda(\omega)=\bigl(\operatorname{Tr}_2\omega,
\operatorname{Tr}_1\omega\bigr),
$$

并把联合谱目标取为

$$
\mathfrak J(\omega)=\bigl(N(\omega),\operatorname{SN}(\omega)\bigr),
$$

其中 $N$ 是部分转置负性，$\operatorname{SN}$ 是 Schmidt number。这里
第二个张量因子是参考/输入副本；它不是把三维接口误写成第六维空间。

**定理 95.2（固定局部边缘下的联合响应逃逸）。** 对所有
$n\in\{0,1,2,\ldots\}\cup\{\infty\}$，都有

$$
\lambda(\omega_n)=\left(\frac{I_3}{3},\frac{I_3}{3}\right).
\tag{95.1}
$$

但联合目标满足

$$
\begin{array}{c|c|c}
\text{horizon}&N(\omega_n)&\operatorname{SN}(\omega_n)\\\hline
0&1&3\\
1\le n<\infty&2^{1-n}/3&2\\
\infty&0&1.
\end{array}
\tag{95.2}
$$

因此，例如 $\omega_1$ 与 $\omega_\infty$ 是同一局部边缘读出的逃逸对，
但它们的联合目标分别为 $(1/6,2)$ 与 $(0,1)$。

**证明。** 式 (95.1) 是 DEV §87 对 $\omega_n$ 的两个边缘恒等式。式
(95.2) 是其 Corollary 87.3 与 Theorem 88.1 的精确谱结论。代入
$n=1$ 与 $n=\infty$ 即得同读出、异目标的来源对。证毕。

这个反例把“局部三维已经完整”与“联合关系已经保留”严格分开：即使边界
知道两个局部 qutrit 的完整一阶密度矩阵，仍不能恢复参考相关中的联合谱。
必须增加跨界响应，例如部分转置的负特征值、负性，或者等价地足以恢复
该联合算子的二阶读出。

**推论 95.3（有限 horizon 的谱记忆）。** 对每个有限 $n\ge1$，

$$
N(\omega_n)=\frac{2^{1-n}}3>0,
$$

所以联合关系在每个有限 horizon 仍有非零的谱见证，且其大小按
$2^{-n}$ 衰减；只有在 $n\to\infty$ 的极限才变为零。因而“相关性已经很
小”与“相关性已经消失”不能互换。

另一方面，DEV §89 的 SIC/MUB 相关范数在 $n\ge3$ 不再违反其
Schmidt-number 检验阈值，尽管式 (95.2) 仍给出 $N(\omega_n)>0$。所以
有限观测族的不检测只能说明该族没有看见这个联合见证，不能推出联合
状态可分。这里的检测统计、联合算子目标和物理可实现性仍须分别记账。

**命题 95.4（四层桥接义务）。** 将本续篇的结果按信息层次排列，三维
接口要支持完整任务，至少要分别核验：

$$
\boxed{
\begin{array}{c}
\text{来源层：观察纤维是否合并了目标不同的来源；}\\
\text{度量层：跨尺度桥是否保持统一距离比例；}\\
\text{合法层：投影零点是否提升为同一合法来源纤维中的联合碰撞；}\\
\text{算子层：局部边缘是否保留参考副本的联合谱响应。}
\end{array}}
\tag{95.3}
$$

**证明。** 来源层由 §92 的 $q$-only 逃逸对给出；度量层由定理 93.2
给出；合法层由命题 94.2 的投影零点反例给出；算子层由定理 95.2 给出。
四项的目标映射分别是来源、距离、合法联合事件和联合谱，因此不能用
其中一项替代另一项。证毕。

这使“全息边界”的最低要求更具体：三维可以继续作为局部方向接口，但
边界必须按声明任务保存跨来源、跨尺度、跨历史和跨参考系统的联合响应。
这些附加对象不是自动增加的空间轴；它们是为了使观察商、度量桥、合法
拼接和算子演化同时良定义而必须保留的关系数据。

## 96. 公共局部框架下的正半定振幅边界

§95 记录了一个联合谱目标的逃逸对：所有 horizon 的两个 qutrit 边缘都
是 $I_3/3$，但联合负性和 Schmidt number 仍随 horizon 改变。最新 DEV 的
实际 Choi 理论还给出了更强的结构性检验：即使允许把联合状态写成一组
三维振幅的有限混合，也不能把这种表示沿所有 horizon 保持下去。

**定义 96.1（公共正半定振幅类）。** 对
$\rho\in\mathcal D(\mathbb C^3\otimes\mathbb C^3)$，写

$$
|C\rangle\!\rangle=\sum_{a,b=0}^2C_{ab}|a,b\rangle .
$$

称 $\rho$ 属于 $\mathsf{PPSD}$，如果存在同一对局部酉 $L,R$、有限个
$C_k=C_k^\dagger\succeq0$ 和概率 $p_k$，满足

$$
\begin{gathered}
p_k\ge0,\qquad \sum_kp_k=1,\qquad
\operatorname{Tr}(C_k^2)=1,\\
(L\otimes R)\rho(L\otimes R)^\dagger
 =\sum_kp_k|C_k\rangle\!\rangle\langle\!\langle C_k| .
\end{gathered}
\tag{96.1}
$$

这里的 $L,R$ 对同一 ensemble 的所有项都相同。这个定义描述的是一种
受限的三维算子边界；它不是任意 Choi 分解，也不是把参考 qutrit 当成
第四个空间方向。

对实际 FIB Choi 家族 $\omega_n$，定义结构目标

$$
\chi_{\mathsf{PPSD}}(\omega)=
\mathbf 1_{\{\omega\in\mathsf{PPSD}\}}.
\tag{96.2}
$$

它与 §95 的联合谱目标不同：这里询问的是“能否在一个公共局部框架中
由正半定三维振幅组成有限混合”，而不是直接询问负性大小。

**定理 96.2（horizon 二处的结构逃逸）。** 对有限 horizon 的实际 Choi
状态，有

$$
\chi_{\mathsf{PPSD}}(\omega_n)=1
\quad\Longleftrightarrow\quad n\in\{0,1\}.
\tag{96.3}
$$

特别地，

$$
\lambda(\omega_1)=\lambda(\omega_2)
 =\left(\frac{I_3}{3},\frac{I_3}{3}\right),
\qquad
\chi_{\mathsf{PPSD}}(\omega_1)=1,
\quad
\chi_{\mathsf{PPSD}}(\omega_2)=0.
\tag{96.4}
$$

所以局部边缘读出不能恢复这一结构目标；这给出一个不同于负性和
Schmidt number 的信息逃逸对。

**证明。** DEV §91.2 已给出 $n=0$ 的单项振幅
$I_3/\sqrt3$，以及 $n=1$ 的两项振幅

$$
\operatorname{diag}(1,1,0)/\sqrt2,
\qquad
\operatorname{diag}(0,0,1),
$$

其权重为 $2/3,1/3$，并给出相应的公共局部框架。因此
$\chi_{\mathsf{PPSD}}(\omega_0)=\chi_{\mathsf{PPSD}}(\omega_1)=1$。

为说明排除机制，若 (96.1) 成立，则交换算子 $\mathsf S$ 与参考部分
转置给出

$$
\sigma^\Gamma=Q\mathsf S,
\qquad
Q=\sum_kp_k(C_k\otimes C_k)\succeq0,
\qquad
Q\mathsf S=\mathsf S Q,
\tag{96.5}
$$

其中 $\sigma=(L\otimes R)\rho(L\otimes R)^\dagger$。于是
$\sigma^\Gamma$ 的严格正特征子空间只能落在
$\operatorname{Sym}^2(\mathbb C^3)$ 中。这个性质在局部框架变换下保持：

$$
\bigl((L\otimes R)\rho(L\otimes R)^\dagger\bigr)^\Gamma
 = (L\otimes\overline R)\rho^\Gamma
   (L\otimes\overline R)^\dagger .
\tag{96.6}
$$

而 DEV §91.2 对 $n\ge2$ 的实际状态给出一个严格正的部分转置平面：

$$
|1\rangle\otimes
\operatorname{span}\{|1\rangle,|2\rangle\}
\subseteq H_+(\widetilde\omega_n^\Gamma).
\tag{96.7}
$$

任何形如 $a\otimes B$ 且 $a\ne0$、$\dim B\ge2$ 的平面都不可能包含在
$\operatorname{Sym}^2(\mathbb C^3)$ 中：若
$a\otimes b=b\otimes a$，则 $b$ 必须属于 $a$ 的一维张成空间。
因此 (96.7) 与 (96.5) 矛盾；局部酉只把这个平面送到另一个同维的
乘积平面，不能消除矛盾。故所有 $n\ge2$ 都有
$\chi_{\mathsf{PPSD}}(\omega_n)=0$。与 $n=0,1$ 的显式构造合并，得
(96.3)。将 $n=1,2$ 代入 §95 的边缘恒等式即得 (96.4)。证毕。

这个定理把 horizon 2 标记为一个结构转折点。它不是说三维接口在
horizon 2 失效，而是说以下更强的边界假设失效：

$$
\boxed{
\text{一个公共局部框架}
 +
\text{有限个正半定三维振幅}
 +
\text{对全部 horizon 的同类分解}.
}
$$

仍可保留完整 Choi 矩阵、允许非正半定或非 Hermitian 的 Kraus 振幅，
或直接保留部分转置的谱数据；这些选择保存的是不同的关系。不能从
$\chi_{\mathsf{PPSD}}(\omega_2)=0$ 单独推出某一种替代编码已经存在。

**推论 96.3（局部三维边界的三层判定）。** 对实际 Choi 族，至少要分开
检查以下三件事：

$$
\boxed{
\begin{array}{rcl}
\text{局部边缘充分性}&:&\lambda(\omega_n);\\
\text{联合谱充分性}&:&(N(\omega_n),\operatorname{SN}(\omega_n));\\
\text{结构分解充分性}&:&\chi_{\mathsf{PPSD}}(\omega_n).
\end{array}}
\tag{96.8}
$$

第一项对所有 horizon 都相同；第二项在有限 horizon 仍有衰减的非零
见证；第三项在 $n=2$ 已从 1 变为 0。因而“边缘不变”“联合相关很小”
和“仍存在公共正半定振幅边界”是三个不同命题，不能互相替代。

这对三维稳定窗口的含义是：局部维数可以保持为 3，而可用的边界表示
类别随递归深度发生结构相变。若项目把公共正半定振幅当作边界协议，
它至多覆盖 $n=0,1$；要继续递归，协议必须显式增加允许的算子关系或
历史记忆。新增的不是第四根空间轴，而是跨 horizon 的表示资源。

**开放边界 96.4。** 定理 96.2 只排除公共正半定 Hermitian 振幅这一
具体表示类。它没有给出任意有限维近似表示的最优误差，也没有证明某个
非正半定表示的最小容量；完整 Choi 恢复、连续 horizon 的近似压缩、
以及这些算子边界与原生 FIB 空间运输的对应仍需分别证明。

## 97. 异常来源相交的有限外部基与合法提升

最新 DEV 的[严格实数联合相交支持卷](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md)
把 §94 的“候选零点不等于合法碰撞”推进到一个更细的必要条件。它不把
所有复杂的来源纤维直接压成一个有限坐标集，而是先隔离一个异常世界集合，
再对整个子纤维仍然发生两种终端碰撞的情形给出有限外部基。

**定义 97.1（异常包含与联合基点）。** 设 $(p,v)$ 是实际参数，
$C(p,v)$ 是固定历史、固定读出和全部严格守卫定义出的合法来源子纤维；
$E(p,v)\subseteq C(p,v)$ 是异常世界集合。令 $f_J,f_M$ 是两个允许终端
动作的响应。称 $(p,v)$ 为异常包含的联合基点，如果

$$
\begin{gathered}
C(p,v)\cap E(p,v)\ne\varnothing,\\
\exists W\ne W'\in C(p,v),\ f_J(W)=f_J(W'),\\
\exists Z\ne Z'\in C(p,v),\ f_M(Z)=f_M(Z').
\end{gathered}
\tag{97.1}
$$

两对世界不要求彼此不交，且被选中的碰撞对不必包含那个异常世界。
这个量词顺序很重要：异常世界只负责定位整个子纤维所在的基点，终端碰撞
仍须在同一个完整合法子纤维中独立成立。

**定理 97.2（异常包含联合基点的有限外部约化）。** 沿用严格实数卷的
多项式、异常判定式 $E_0,S_4,Q_{10},Q_{24}$ 以及异常图表的非零因子，
定义

$$
\begin{aligned}
Z_E={}&V_{\mathbb C}(Q_{10},E_0N_J,E_0N_M)\\
&\cup V_{\mathbb C}(S_4,E_0N_J,E_0N_M)\\
&\cup V_{\mathbb C}(Q_{24},e_{24}n_{24,J},e_{24}n_{24,M}).
\end{aligned}
\tag{97.2}
$$

这是一个显式定义的有限、也可能为空的复仿射集合。若一个实参数
$(p,v)$ 满足 $p\ne24$，是异常包含的联合基点，则

$$
\boxed{(p,v)\in Z_E.}
\tag{97.3}
$$

**证明。** 先从 (97.1) 选择一个异常世界，只用于定位基点。若该世界
具有零漂移，严格实数支持卷的异常分类给出 $Q_{10}=0$。若其具有非零
漂移并落在 $F_0=0$ 图表，则 CRT 图表给出 $Q_{24}=0$；剩余的异常情形
满足 $\Lambda=0$，从而给出 $S_4=0$。这三种情形穷尽异常定义。

在 $Q_{10}=0$ 或 $S_4=0$ 的基点，完整来源桥把每个实际世界表示为旧图表
中的忠实坐标；在 $Q_{24}=0$ 的基点，则使用 $e_{24}$ 外的 CRT 图表。
在这些图表上，不同实际世界有不同的 $x$，而每一个终端碰撞都迫使相应
的幂行列式为零。因此 $J$ 对给定子纤维的碰撞给出 $N_J=0$，$M$ 的碰撞
给出 $N_M=0$，分别代入三种图表便得到 (97.2) 的一个分支。三者的并集
给出 (97.3)。严格实数支持卷还证明各图表因子之间没有共同曲线分量，
故每个交集是有限的；没有把复根、重复根或分母为零的点当作合法世界。
证毕。

该定理的结论方向必须保留：

$$
\text{合法异常包含碰撞}
\Longrightarrow
\text{有限外部候选},
$$

而不是反向等价。$Z_E$ 中的点可能只有复代数根，可能没有满足严格实数
守卫的 lift，也可能没有来源不等性的实际世界；即使存在 lift，还须逐项
验证完整历史读数、非奇异分母、终端动作和两个碰撞对。有限性减少的是
候选搜索空间，不是合法来源的恢复成本。

**推论 97.3（三维桥不得把外部基当作状态边界）。** 若一个三维接口只
保存 $(p,v)$ 的投影坐标，那么 (97.3) 最多提供一个必要的外部筛选器。它
不能单独证明：

$$
\begin{array}{c}
Z_E\text{ 中存在真实世界};\\
\text{该世界属于同一历史与读出纤维};\\
\text{两种终端动作分别存在来源不等性的碰撞};\\
\text{或三维接口能够恢复这些 lift 的联合响应}.
\end{array}
$$

因此，本节把 §94 的验证顺序具体化为四步：先在 $Z_E$ 中定位外部候选，
再做严格实数 lift，然后检查完整合法来源纤维，最后才检查三维边界对
联合终端响应的充分性。任何一步失败都只能删除该候选，不能把剩余候选
当成已经发生的物理碰撞。

**开放边界 97.4。** 严格实数支持卷明确保留了未覆盖的 children：避开
异常集合的 regular charts、$b\to0$、$r\to0,1$、非紧端点、剩余奇异
分母和全部原始守卫仍未被全局分类。因此 $Z_E$ 是异常包含扇区的必要
外部基，而不是整个 $D_J\cap D_M$ 的消灭或存在定理。它也不提供
native source-to-space 映射、距离、时钟或三维运输的形式化实现。
